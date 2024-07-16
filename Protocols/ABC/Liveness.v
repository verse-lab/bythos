From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.ABC Require Export Safety.
From Bythos.Properties Require Import Liveness.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module ACLiveness (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f).

Import A V (* VBFT *) BTh BSett.
Import ssrbool. (* anyway *)

Module Export ACS := ACSafety A Sn V (* VBFT *) BTh BSett PPrim TSSPrim.
Import ACN.ACDT.P ACN.ACDT.TSS.
Include Liveness A M BTh BSett P0 PSOp ACP Ns ACAdv ACN.

Module Terminating_Convergence.

(* start *)
Definition all_honest_nodes_submitted v w := forall n, is_byz n = false -> (w @ n).(submitted_value) = Some v.

(* end *)
Definition all_honest_nodes_confirmed v w := forall n, is_byz n = false -> (w @ n).(conf) /\ (w @ n).(submitted_value) = Some v.

Fact all_honest_nodes_submitted_stmap_peq_cong v : stmap_peq_cong (all_honest_nodes_submitted v).
Proof. unfold stmap_peq_cong, all_honest_nodes_submitted. intros w w' Hs. hnf in Hs. now setoid_rewrite Hs. Qed.

Fact all_honest_nodes_confirmed_stmap_peq_cong v : stmap_peq_cong (all_honest_nodes_confirmed v).
Proof. unfold stmap_peq_cong, all_honest_nodes_confirmed. intros w w' Hs. hnf in Hs. now setoid_rewrite Hs. Qed.

Section Proof_of_Terminating_Convergence.

  Variables (v : Value).

  Hypothesis (H_byz_minor : num_byz <= f).

  Let submitted_v w n : Prop := (w @ n).(submitted_value) = Some v.
  Let valid_submitmsg n : Message := let: vv := (* value_bft n *) v in
    (SubmitMsg vv (light_sign vv (lightkey_map n)) (sign vv (key_map n))).

  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : all_honest_nodes_submitted v w).

  Definition pkts_needed_in_round_1 nonbyz_senders pkts :=
    pkts_multi_to_all (N - f) w nonbyz_senders pkts valid_submitmsg submitted_v.

  Let nonbyz_senders := (List.filter (fun n => negb (is_byz n)) valid_nodes).

  Lemma round_1_pkts :
    exists pkts, pkts_needed_in_round_1 nonbyz_senders pkts.
  Proof.
    unfold pkts_needed_in_round_1, nonbyz_senders. saturate.
    exists (List.filter (fun p => 
      match p.(msg) with
      | SubmitMsg _ _ _ =>
        (negb (is_byz p.(src))) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)).
    hnf. split_and?; auto using incl_filter, NoDup_filter, valid_nodes_NoDup.
    - pose proof (filter_nonbyz_lower_bound valid_nodes_NoDup). unfold N. lia.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      now rewrite andb_true_iff, !negb_true_iff in Hcheck.
    - intros n1 Hin1_backup.
      pose proof Hin1_backup as Hnonbyz_n1%is_nonbyz_synonym. pose proof Hnonbyz_n1 as Hv%Hstart. split_and?; auto.
      intros n2 Hnonbyz_n2.
      pick inv_submitted_broadcast as_ Hbc by_ (pose proof (Hl2h _ Hnonbyz_n1) as []). saturate_assumptions!. 
      pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst n1) as []). rewrite Hv in Htmp. destruct Htmp as ((* -> & *)? & ?). 
      rewrite Hcoh in Hbc. destruct Hbc as (b & Hbc). exists b. apply filter_In. 
      simpl. now rewrite andb_true_iff, !negb_true_iff. 
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 nonbyz_senders pkts).

  Definition round_1_end w' :=
    Eval unfold mutual_receiving in mutual_receiving valid_submitmsg w'.

  Fact round_1_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    (* FIXME: can this be automated? *)
    hnf in Hround1. unfold valid_submitmsg in Hround1. 
    pick SubmitMsg as_ HH by_ (destruct_and? Hround1).
    hnf. intros n1 Hnonbyz_n1%is_nonbyz_synonym n2 Hnonbyz_n2.
    saturate_assumptions!. destruct HH as (_ & _ & HH). saturate_assumptions!. 
    destruct HH as (? & HH). now apply (in_map markRcv), Hincl in HH.
  Qed.

  Lemma all_honest_nodes_confirmed_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : all_honest_nodes_confirmed v w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    (* clear H_w_reachable. *) saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n.
    (* need to use persistence here to know buffer = nil *)
    apply persistent_invariants_trace in Htrace0; auto. 
    pick submitted_value_persistent as_ Hvv by_ (pose proof (Htrace0 n) as []). rewrite <- Ew0 in Hvv.
    pose proof (Hstart _ Hnonbyz_n) as Hvn. saturate_assumptions! in_ Hvv.
    split; auto. destruct (conf (w0 @ n)) eqn:Ec; auto.
    (* TODO this step is repeating? *)
    pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst n) as []). rewrite Hvv(*, Hcoh *) in Htmp. destruct Htmp as ((* Ev & *)_ & _). 
    assert (incl nonbyz_senders (w0 @ n).(from_set)) as Hincl.
    { hnf. intros nn Hnonbyz_nn%is_nonbyz_synonym. specialize (Hw0 _ Hnonbyz_nn n Hnonbyz_n).
      (* need to unify (value_bft nn) with v *)
      (* TODO this step is repeating! *)
      pick submitted_value_persistent as_ Hvv' by_ (pose proof (Htrace0 nn) as []). rewrite <- Ew0 in Hvv'.
      pose proof (Hstart _ Hnonbyz_nn) as Hvn'. saturate_assumptions! in_ Hvv'.
      pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst nn) as []). rewrite Hvv'(*, Hcoh *) in Htmp. destruct Htmp as ((* Ev' & *)_ & _). 
      pick inv_submitmsg_receive as_ Htmp by_ (pose proof (Hh2l _ Hw0) as []). 
      unfold valid_submitmsg, inv_submitmsg_receive_ in Htmp. simpl in Htmp. rewrite Hvv(*, Ev' *) in Htmp.
      (* FIXME: maybe use ABCinv below? *)
      apply Htmp; auto using correct_sign_verify_ok, correct_sign_verify_ok_light. }
    unfold nonbyz_senders in Hincl. 
    apply NoDup_incl_length in Hincl; auto using NoDup_filter, valid_nodes_NoDup.
    pose proof (filter_nonbyz_lower_bound valid_nodes_NoDup).
    pick inv_conf_correct as_ Htmp by_ (pose proof (Hst n) as []). unfold N in Htmp. rewrite Ec in Htmp. lia.  
  Qed.

  End Round1.

End Proof_of_Terminating_Convergence.

End Terminating_Convergence.

Module Accountability.

Lemma conflicting_cert_quorum_in_proof rcerts v1 v2 nsigs1 nsigs2
  (Hvneq : v1 <> v2)
  (Hin1 : In (v1, nsigs1) rcerts)
  (Hin2 : In (v2, nsigs2) rcerts) 
  (Hcert_valid1 : certificate_valid v1 nsigs1)
  (Hcert_valid2 : certificate_valid v2 nsigs2) :
  incl (List.filter (fun n => In_dec Address_eqdec n (map fst nsigs1)) (map fst nsigs2)) 
    (genproof rcerts).
Proof.
  hnf. intros nb' (Hin2' & Hin1'%sumbool_is_left)%filter_In.
  pose proof Hin2' as Hin2''.
  eapply valid_cert_sender_in in Hin1', Hin2'; eauto.
  apply genproof_correct. 
  now exists v1, v2, (sign v1 (key_map nb')), (sign v2 (key_map nb')), nsigs1, nsigs2.
Qed.

Definition nonbyz_confirmed n w : Prop := is_byz n = false /\ (localState w n).(conf).

(* start *)
Definition confirmed_different_values n1 n2 w : Prop :=
  Eval unfold nonbyz_confirmed in
  n1 <> n2 /\ nonbyz_confirmed n1 w /\ nonbyz_confirmed n2 w /\ 
  (w @ n1).(submitted_value) <> (w @ n2).(submitted_value).

Definition confirmed_different_values' n1 n2 w : Prop :=
  Eval unfold nonbyz_confirmed in
  n1 <> n2 /\ nonbyz_confirmed n1 w /\ nonbyz_confirmed n2 w /\ 
  match (w @ n1).(submitted_value), (w @ n2).(submitted_value) with
  | Some v1, Some v2 => v1 <> v2
  | _, _ => False
  end.

Fact confirmed_different_values_strengthen n1 n2 w (Hr : reachable w) :
  confirmed_different_values n1 n2 w -> confirmed_different_values' n1 n2 w.
Proof.
  saturate.
  intros (Hnneq & (H_n1_nonbyz & Hconf1) & (H_n2_nonbyz & Hconf2) & Hvneq).
  pick confirmed_then_submitted as_ Hv1 by_ (pose proof (Hst n1) as []).
  pick confirmed_then_submitted as_ Hv2 by_ (pose proof (Hst n2) as []).
  saturate_assumptions. 
  pick inv_submit_mixin as_ Hs1 by_ (pose proof (Hst n1) as []).
  pick inv_submit_mixin as_ Hs2 by_ (pose proof (Hst n2) as []).
  hnf.
  destruct (submitted_value (w @ n1)) as [ v1 | ], (submitted_value (w @ n2)) as [ v2 | ]; try discriminate.
  (* rewrite Hcoh in Hs1, Hs2. *) eqsolve.
Qed.

(* end; not represented as an explicit state *)
Definition accountability w :=
  exists byzs : list Address, 
    NoDup byzs /\
    N - (f + f) <= length byzs /\
    Forall is_byz byzs /\
    (forall n, is_byz n = false -> incl byzs (genproof (w @ n).(received_certs))).

Section Proof_of_Accountability.

  Section Round1.

  Variables (w : World) (n1 n2 : Address).
  Hypothesis (H_w_reachable : reachable w) (Hstart : confirmed_different_values n1 n2 w).

  Local Tactic Notation "prepare" hyp(H) :=
    apply confirmed_different_values_strengthen in H; auto;
    destruct H as (Hnneq & (Hnonbyz_n1 & Hconf1) & (Hnonbyz_n2 & Hconf2) & Hvneq); clear H;
    destruct (w @ n1).(submitted_value) as [ v1 | ] eqn:Hv1, (w @ n2).(submitted_value) as [ v2 | ] eqn:Hv2; try contradiction.

  (* well, using 4 packets instead of 2 is inevitable. *)
  (* TODO self messaging is kind of weird *)
  Definition mutual_lightcerts v1 v2 b1 b2 b3 b4 := Eval cbn in
    let f (bb : bool) src dst b := 
      let: qq := if bb then v1 else v2 in (mkP src dst (LightConfirmMsg 
      (qq, (lightsig_combine (localState w src).(collected_lightsigs)))) b) in
    (f true n1 n1 b1 :: f true n1 n2 b2 :: f false n2 n1 b3 :: f false n2 n2 b4 :: nil). 

  Definition pkts_needed_in_round_1 pkts :=
    incl pkts (sentMsgs w) /\ Forall good_packet pkts /\
    exists v1 v2 b1 b2 b3 b4, 
      (w @ n1).(submitted_value) = Some v1 /\
      (w @ n2).(submitted_value) = Some v2 /\
      pkts = mutual_lightcerts v1 v2 b1 b2 b3 b4. 

  Lemma round_1_pkts : exists pkts, pkts_needed_in_round_1 pkts.
  Proof.
    unfold pkts_needed_in_round_1, mutual_lightcerts. saturate. prepare Hstart.
    pick inv_conf_lightconfmsg as_ Hc1 by_ (pose proof (Hl2h _ Hnonbyz_n1) as []).
    pick inv_conf_lightconfmsg as_ Hc2 by_ (pose proof (Hl2h _ Hnonbyz_n2) as []).
    pose proof (Hc1 _ Hv1 Hconf1 n1) as (b1 & Hin1).
    pose proof (Hc1 _ Hv1 Hconf1 n2) as (b2 & Hin2).
    pose proof (Hc2 _ Hv2 Hconf2 n1) as (b3 & Hin3).
    pose proof (Hc2 _ Hv2 Hconf2 n2) as (b4 & Hin4).
    rewrite Hcoh in Hin1, Hin2, Hin3, Hin4. eexists. split_and?. 
    3: exists v1, v2, b1, b2, b3, b4; split_and?; try reflexivity.
    - hnf. simpl. intuition (subst; auto).
    - repeat constructor; auto.
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 pkts).

  Definition round_1_end w' :=
    exists v1 v2, 
      (w @ n1).(submitted_value) = Some v1 /\
      (w @ n2).(submitted_value) = Some v2 /\
      incl (mutual_lightcerts v1 v2 true true true true) (sentMsgs w').

  Fact round_1_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof. hnf in Hround1 |- *. destruct Hround1 as (? & ? & (? & ? & ? & ? & ? & ? & -> & -> & ->)). eauto. Qed.

  (* at the same time as round 1 ends *)
  Definition round_2_start w' :=
    (* some conditions need to be kept *)
    confirmed_different_values' n1 n2 w' /\
    lightcert_conflict_check (w' @ n1).(received_lightcerts) /\
    lightcert_conflict_check (w' @ n2).(received_lightcerts).

  Lemma round_2_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : round_2_start w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    (* clear H_w_reachable. *) saturate. prepare Hstart.

    hnf in Hw0 |- *. destruct Hw0 as (v1' & v2' & Ev1' & Ev2' & Hw0). rewrite Hv1 in Ev1'. rewrite Hv2 in Ev2'. injection Ev1' as <-. injection Ev2' as <-.
    unfold mutual_lightcerts in Hw0. hnf in Hw0. rewrite <- Forall_forall, !Forall_cons_iff in Hw0. 
    destruct Hw0 as (H11 & H12 & H21 & H22 & _).
    (* know that the combined lightsigs are good *)
    (* TODO this is tedious! *)
    (* FIXME: the proof may go too far. possibly using (w @ n) shoule be enough somewhere *)
    apply persistent_invariants_trace in Htrace0; auto. 
    pick inv_submit_mixin as_ Hs1 by_ (pose proof (Hst n1) as []).
    pick inv_submit_mixin as_ Hs2 by_ (pose proof (Hst n2) as []).
    pick inv_set_size as_ Hsz1 by_ (pose proof (Hst n1) as []).
    pick inv_set_size as_ Hsz2 by_ (pose proof (Hst n2) as []).
    pick inv_from_nodup as_ Hnodup1 by_ (pose proof (Hst n1) as []).
    pick inv_from_nodup as_ Hnodup2 by_ (pose proof (Hst n2) as []).
    pick inv_conf_correct as_ Hc1 by_ (pose proof (Hst n1) as []).
    pick inv_conf_correct as_ Hc2 by_ (pose proof (Hst n2) as []).
    pick submitted_value_persistent as_ Hvv1 by_ (pose proof (Htrace0 n1) as []).
    pick submitted_value_persistent as_ Hvv2 by_ (pose proof (Htrace0 n2) as []).
    pick conf_persistent as_ Hcc1 by_ (pose proof (Htrace0 n1) as []). 
    pick conf_persistent as_ Hcc2 by_ (pose proof (Htrace0 n2) as []). 
    pick conf_collected_lightsigs_persistent as_ Hls1 by_ (pose proof (Htrace0 n1) as []).
    pick conf_collected_lightsigs_persistent as_ Hls2 by_ (pose proof (Htrace0 n2) as []). (* also these two *)
    rewrite <- Ew0 in Hvv1, Hvv2, Hcc1, Hcc2, Hls1, Hls2. 
    specialize (Hvv1 v1). specialize (Hvv2 v2). saturate_assumptions!.
    rewrite Hvv1 in Hs1. rewrite Hcc1 in Hc1. rewrite Hvv2 in Hs2. rewrite Hcc2 in Hc2. rewrite Hls1 in *. rewrite Hls2 in *.
    destruct Hs1 as ((*_ & *) Hs1 & _), Hs2 as ((*_ & *) Hs2 & _), Hsz1 as (Hsz1 & _), Hsz2 as (Hsz2 & _).
    apply light_signatures_valid_for_combine in Hs1, Hs2; auto.
    (* know that the lightcerts will not be rejected *)
    let tac vv nn := assert (combined_verify vv (lightsig_combine (collected_lightsigs (w0 @ nn))))
      by (apply combine_correct; exists (from_set (w0 @ nn)); split_and?; auto; try congruence)
    in tac v1 n1; tac v2 n2.
    let tac HH str := (let name := fresh "Hrcv" str in
      pick inv_lightconfirmmsg_receive as_ name by_ (pose proof (Hh2l _ HH) as []))
    in tac H11 ident:(_11); tac H12 ident:(_12); tac H21 ident:(_21); tac H22 ident:(_22).
    saturate_assumptions!. 
    rewrite !lightcert_conflict_check_correct. unfold confirmed_different_values'. rewrite Hvv1, Hvv2. split_and?; auto. 
    all: exists v1, v2; do 2 eexists; split_and?; try eassumption; auto.
  Qed.

  End Round1.

  Section Round2.

  Variables (w : World) (n1 n2 : Address).
  Hypothesis (H_w_reachable : reachable w) (Hstart : round_2_start n1 n2 w).

  Local Tactic Notation "prepare" hyp(H) :=
    destruct H as ((Hnneq & (Hnonbyz_n1 & Hconf1) & (Hnonbyz_n2 & Hconf2) & Hvneq) & Hcheck1 & Hcheck2); clear H;
    destruct (w @ n1).(submitted_value) as [ v1 | ] eqn:Hv1, (w @ n2).(submitted_value) as [ v2 | ] eqn:Hv2; try contradiction.

  Definition pkts_needed_in_round_2 pkts : Prop :=
    match (w @ n1).(submitted_value), (w @ n2).(submitted_value) with
    | Some v1, Some v2 =>
      pkts_multi_to_all 0 (* size does not matter here *) w (n1 :: n2 :: nil) pkts
      (fun n => (ConfirmMsg (if Address_eqdec n n1 then v1 else v2, zip_from_sigs (w @ n)))) (fun _ _ => True) (* do not need extra predicate *)
    | _, _ => False
    end.

  Lemma round_2_pkts : exists pkts, pkts_needed_in_round_2 pkts.
  Proof.
    unfold pkts_needed_in_round_2. saturate. prepare Hstart.
    exists (List.filter (fun p => 
      match p.(msg) with
      | ConfirmMsg _ =>
        (Address_eqdec p.(src) n1 || Address_eqdec p.(src) n2) && (negb (is_byz p.(dst))) (* TODO maybe too general? *)
      | _ => false
      end) (sentMsgs w)).
    hnf. split_and?; auto using incl_filter, le_0_n.
    - repeat constructor; simpl; eqsolve. 
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      autorewrite with booldec in Hcheck. hnf. intuition (subst; auto).
    - intros n Hor. simpl in Hor.
      apply and_wlog_r. 1: eqsolve. intros Hnonbyz_n. split; auto. intros nn Hnonbyz_nn.
      (* know that n1 and n2 must have sent ConfirmMsg *)
      pick inv_conf_confmsg as_ Hs1 by_ (pose proof (Hl2h _ Hnonbyz_n1) as []).
      pick inv_conf_confmsg as_ Hs2 by_ (pose proof (Hl2h _ Hnonbyz_n2) as []).
      saturate_assumptions!. rewrite Hcoh in Hs1, Hs2.
      destruct Hs1 as (b1 & Hs1), Hs2 as (b2 & Hs2). 
      destruct Hor as [ <- | [ <- | [] ] ]; destruct_eqdec as_ ?; try congruence.
      1: exists b1. 2: exists b2.
      all: autorewrite with booldec; simpl; autorewrite with booldec; intuition.
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround2 : pkts_needed_in_round_2 pkts).

  Definition round_2_end w' :=
    match (w @ n1).(submitted_value), (w @ n2).(submitted_value) with
    | Some v1, Some v2 =>
      forall n, is_byz n = false ->
        In (mkP n1 n (ConfirmMsg (v1, zip_from_sigs (w @ n1))) true) (sentMsgs w') /\
        In (mkP n2 n (ConfirmMsg (v2, zip_from_sigs (w @ n2))) true) (sentMsgs w')
    | _, _ => False
    end.

  Fact round_2_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_2_end w'.
  Proof.
    hnf in Hround2 |- *. prepare Hstart.
    hnf in Hround2. pick ConfirmMsg as_ HH by_ (destruct_and? Hround2).
    intros n Hnonbyz_n. split; apply Hincl.
    1: specialize (HH n1 ltac:(simpl; tauto)).
    2: specialize (HH n2 ltac:(simpl; tauto)).
    all: destruct_and? HH; saturate_assumptions!.
    all: destruct_exists; match goal with H : In _ pkts |- _ => apply (in_map markRcv) in H; simpl in H; destruct_eqdec in_ H0 as_ ?; congruence end.
  Qed.

  Lemma accountability_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_2_end w0) : accountability w0.
  Proof.
    saturate. 
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    (* clear H_w_reachable. *) saturate. hnf in Hw0. prepare Hstart.

    (* TODO repeating *)
    pick inv_submit_mixin as_ Hs1 by_ (pose proof (Hst n1) as []).
    pick inv_submit_mixin as_ Hs2 by_ (pose proof (Hst n2) as []).
    pick inv_set_size as_ Hsz1 by_ (pose proof (Hst n1) as []).
    pick inv_set_size as_ Hsz2 by_ (pose proof (Hst n2) as []).
    pick inv_from_nodup as_ Hnodup1 by_ (pose proof (Hst n1) as []).
    pick inv_from_nodup as_ Hnodup2 by_ (pose proof (Hst n2) as []).
    pick inv_conf_correct as_ Hc1 by_ (pose proof (Hst n1) as []).
    pick inv_conf_correct as_ Hc2 by_ (pose proof (Hst n2) as []).
    rewrite Hv1 in Hs1. rewrite Hconf1 in Hc1. rewrite Hv2 in Hs2. rewrite Hconf2 in Hc2. 
    destruct Hs1 as ((*_ & *)_ & Hs1), Hs2 as ((*_ & *)_ & Hs2), Hsz1 as (_ & Hsz1), Hsz2 as (_ & Hsz2).
    remember (List.filter (fun n' : Address => in_dec Address_eqdec n' (w @ n1).(from_set)) (w @ n2).(from_set)) as l eqn:El.
    hnf. exists l. do 2 (try split_and).
    - subst l. auto using NoDup_filter.
    - subst l. apply quorum_intersection; auto; lia.
    - apply and_wlog_l.
      + intros HH. apply Forall_forall. intros x Hin.
        (* exploit that there exists some non-Byz node *)
        specialize (HH _ Hnonbyz_n1). eapply HH, genproof_soundness_always_holds in Hin; auto.
      + intros n Hnonbyz_n. specialize (Hw0 _ Hnonbyz_n). destruct Hw0 as (Hq1 & Hq2). 
        (* need to show that they will be received *)
        pick inv_confirmmsg_receive as_ Hr1 by_ (pose proof (Hh2l0 _ Hq1) as []).
        pick inv_confirmmsg_receive as_ Hr2 by_ (pose proof (Hh2l0 _ Hq2) as []).
        saturate_assumptions.
        unfold zip_from_sigs in Hr1, Hr2. rewrite combine_length in Hr1, Hr2. rewrite <- Hsz1, -> Hc1 in Hr1. rewrite <- Hsz2, -> Hc2 in Hr2.
        specialize (Hr1 (NoDup_combine_l _ _ Hnodup1) ltac:(lia)).
        specialize (Hr2 (NoDup_combine_l _ _ Hnodup2) ltac:(lia)).
        subst l.
        rewrite <- (combine_map_fst (from_set (w @ n1)) (collected_sigs (w @ n1))) by auto.
        rewrite <- (combine_map_fst (from_set (w @ n2)) (collected_sigs (w @ n2))) by auto.
        eapply conflicting_cert_quorum_in_proof; try hypothesis. 
  Qed.

  End Round2.

End Proof_of_Accountability.

End Accountability.

End ACLiveness.
