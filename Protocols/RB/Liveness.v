From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.RB Require Export Safety.
From Bythos.Properties Require Import Liveness.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module RBLiveness (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBS := RBSafety A R V VBFT BTh BSett.
Include Liveness A M BTh BSett P PSOp RBP Ns RBAdv RBN.

Set Implicit Arguments. (* anyway *)

(* at the beginning *)
Definition some_receives src r v w : Prop := exists n, is_byz n = false /\ In v ((w @ n).(output) (src, r)).

(* Definition nonfaulty_bcast src r w : Prop := is_byz src = false /\ (w @ src).(sent) r. *)

(* at the end *)
Definition all_receives src r v w : Prop := forall n, is_byz n = false -> In v ((w @ n).(output) (src, r)).

Fact all_receives_stmap_peq_cong src r v : stmap_peq_cong (all_receives src r v).
Proof. unfold stmap_peq_cong, all_receives. intros w w' Hs. hnf in Hs. now setoid_rewrite Hs. Qed.

Module Global_Liveness.

Section Proof_of_Global_Liveness.

  Variables (src : Address) (r : Round) (v : Value).

  Section Prelude.

  (* the structure of Round 1 and Round 2 are similar, so some conclusions might be reused *)
  Definition pkts_needed size w nonbyz_senders pkts :=
    pkts_multi_to_all size w nonbyz_senders pkts (fun _ => VoteMsg src r v) (fun w n => (w @ n).(voted) (src, r) = Some v).

  Lemma pkts_needed_by_voted_nodes w size (H_w_reachable : reachable w)
    nonbyz_senders (Hf_nonbyz : forall n, In n nonbyz_senders -> is_byz n = false)
    (Hnodup : List.NoDup nonbyz_senders) (Hsize : size <= length nonbyz_senders)
    (Hallvoted : forall n, In n nonbyz_senders -> (w @ n).(voted) (src, r) = Some v) :
    exists pkts, pkts_needed size w nonbyz_senders pkts.
  Proof.
    saturate. 
    exists (List.filter (fun p => 
      match p.(msg) with
      | VoteMsg _ _ _ =>
        (is_left (in_dec Address_eqdec (P.src p) nonbyz_senders)) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)).
    hnf. split_and?; auto using incl_filter.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      unfold is_left in Hcheck. rewrite andb_true_iff, negb_true_iff, sumbool_is_left in Hcheck.
      hnf. simpl. intuition.
    - intros n1 Hin1_backup. 
      pose proof Hin1_backup as Hnonbyz_n1%Hf_nonbyz. pose proof Hin1_backup as Hv%Hallvoted. split_and?; auto.
      intros n2 Hnonbyz_n2.
      pick votemsg_sent_l2h as_ Hsent1' by_ (pose proof (Hl2h _ Hnonbyz_n1) as []). specialize (Hsent1' _ _ _ Hv n2). rewrite Hcoh in Hsent1'.
      destruct Hsent1'. eexists. apply filter_In. 
      simpl. split; [ eassumption | unfold is_left; now rewrite andb_true_iff, negb_true_iff, sumbool_is_left ].
  Qed.

  End Prelude.

  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : some_receives src r v w).

  Definition pkts_needed_in_round_1 nonbyz_senders pkts : Prop :=
    Eval unfold pkts_needed in pkts_needed (N - (f + f)) w nonbyz_senders pkts.

  (* in the first round, there are (N-2f) non-faulty nodes broadcasting Vote messages *)
  Lemma round_1_pkts :
    exists nonbyz_senders pkts, pkts_needed_in_round_1 nonbyz_senders pkts.
  Proof.
    unfold pkts_needed_in_round_1. saturate.
    destruct Hstart as (n & Hnonbyz_n & Hr).
    (* TODO the following two steps are familiar ... *)
    pick output_vote_size as_ H1 by_ (pose proof (Hst n) as []). specialize (H1 _ _ _ Hr).
    unfold th_vote4output in H1.
    pick msgcnt_nodup as_ Hnodup by_ (pose proof (Hst n) as []). specialize (Hnodup (VoteMsg src r v)). simpl in Hnodup.
    pose proof (filter_nonbyz_lower_bound_f Hnodup) as Hlen.
    match type of Hlen with _ <= length ?ll => exists ll end.
    apply pkts_needed_by_voted_nodes; auto using NoDup_filter; try lia.
    all: intros n1 (Hin1 & Hnonbyz%negb_true_iff)%filter_In; auto.
    (* TODO the following two steps has some overlap with a previous proof *)
    pick msgcnt_recv_l2h as_ Hsent1 by_ (pose proof (Hl2h _ Hnonbyz_n) as []). specialize (Hsent1 _ _ Hin1). rewrite Hcoh in Hsent1.
    pick votemsg_sent_h2l as_ Hv1 by_ (pose proof (Hh2ls _ Hsent1) as []). now saturate_assumptions.
  Qed.

  (* universally quantified *)
  Variable (nonbyz_senders : list Address) (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 nonbyz_senders pkts).

  (* FIXME: this might be rewritten as mutual_receiving *)
  Definition round_1_end w' :=
    forall n1, In n1 nonbyz_senders -> 
      forall n2, is_byz n2 = false ->
        In (mkP n1 n2 (VoteMsg src r v) true) (sentMsgs w').

  Fact round_1_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    hnf in Hround1. pick VoteMsg as_ HH by_ (destruct_and? Hround1).
    hnf. intros n1 Hin1 n2 Hnonbyz_n2. specialize (HH _ Hin1).
    destruct HH as (_ & _ & HH). specialize (HH _ Hnonbyz_n2). destruct HH as (? & HH). now apply (in_map markRcv), Hincl in HH.
  Qed.

  (* at the same time as round 1 ends *)
  Definition round_2_start w' :=
    forall n, is_byz n = false -> (w' @ n).(voted) (src, r) = Some v.

  Lemma round_2_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : round_2_start w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. 
    hnf in Hround1. destruct Hround1 as (Hnodup & Hsize & _ & _ & HH).
    destruct (voted _ _) as [ v' | ] eqn:Ev' in |- *.
    - (* use vote_uniqueness *)
      f_equal. 
      pose proof N_minus_2f_gt_0 as Hf. pose proof (length_gt_0_notnil (l:=nonbyz_senders) ltac:(lia)) as (_ & (nn & Hin)).
      pose proof (HH _ Hin) as (Hnonbyz_nn & Hvnn & _). 
      (* FIXME: make this usage of persistence a tactic? *)
      pose proof (persistent_invariants_trace Htrace0) as Hps. rewrite <- Ew0 in *.
      pick voted_persistent as_ Hp by_ (pose proof (Hps nn) as []). apply Hp in Hvnn.
      eapply (Hvu src r n nn); eassumption.
    - (* prove contradiction using the message size *)
      pick voted_none as_ Hp by_ (pose proof (Hst n) as []). apply Hp with (v:=v) in Ev'.
      assert (incl nonbyz_senders (msgcnt (w0 @ n) (VoteMsg src r v))) as Hincl.
      { hnf. intros nn Hin. specialize (Hw0 _ Hin n Hnonbyz_n).
        pick msgcnt_recv_h2l as_ Hr by_ (pose proof (Hh2lr _ Hw0) as []). saturate_assumptions. now simpl in Hr. }
      apply NoDup_incl_length in Hincl; try assumption. unfold th_vote4vote in Ev'. destruct Ev'. lia.
  Qed.

  End Round1.

  Section Round2.

  Variable (w : World).
  Hypothesis (H_w_reachable : reachable w) (Hstart : round_2_start w).

  Definition pkts_needed_in_round_2 nonbyz_senders pkts : Prop :=
    Eval unfold pkts_needed in pkts_needed (N - f) w nonbyz_senders pkts.

  Let nonbyz_senders := (List.filter (fun n => negb (is_byz n)) valid_nodes).

  (* in the second round, there are (N-f) non-faulty nodes broadcasting Vote messages *)
  Lemma round_2_pkts :
    exists pkts, pkts_needed_in_round_2 nonbyz_senders pkts.
  Proof.
    unfold pkts_needed_in_round_2, nonbyz_senders. saturate.
    apply pkts_needed_by_voted_nodes; auto using NoDup_filter, valid_nodes_NoDup, nonbyz_lower_bound.
    all: intros n1 (_ & Hnonbyz%negb_true_iff)%filter_In; auto.
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround2 : pkts_needed_in_round_2 nonbyz_senders pkts).

  Definition round_2_end w' :=
    Eval unfold mutual_receiving in mutual_receiving (fun _ => VoteMsg src r v) w'.

  Fact round_2_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_2_end w'.
  Proof.
    hnf in Hround2. pick VoteMsg as_ HH by_ (destruct_and? Hround2).
    hnf. intros n1 Hin1 n2 Hnonbyz_n2. 
    specialize (HH n1 ltac:(unfold nonbyz_senders; rewrite filter_In, negb_true_iff; auto using Address_is_finite)).
    destruct HH as (_ & _ & HH). specialize (HH _ Hnonbyz_n2). destruct HH as (? & HH). now apply (in_map markRcv), Hincl in HH.
  Qed.

  Lemma all_receives_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_2_end w0) : all_receives src r v w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. 
    pick vote_size_output as_ Hp by_ (pose proof (Hst n) as []). apply Hp.
    assert (incl nonbyz_senders (msgcnt (w0 @ n) (VoteMsg src r v))) as Hincl.
    { hnf. intros nn (_ & Hnonbyz_nn%negb_true_iff)%filter_In. specialize (Hw0 _ Hnonbyz_nn n Hnonbyz_n).
      pick msgcnt_recv_h2l as_ Hr by_ (pose proof (Hh2lr _ Hw0) as []). saturate_assumptions. now simpl in Hr. }
    unfold nonbyz_senders in Hincl. 
    apply NoDup_incl_length in Hincl; auto using NoDup_filter, valid_nodes_NoDup.
    unfold th_vote4output. pose proof nonbyz_lower_bound. lia.
  Qed.

  End Round2.

End Proof_of_Global_Liveness.

End Global_Liveness.

Module Validity.

Section Proof_of_Validity.

  Variables (src : Address) (r : Round).
  Hypothesis (Hnonbyz_src : is_byz src = false).

  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : (w @ src).(sent) r).

  Definition pkts_needed_in_round_1 pkts : Prop :=
    incl pkts (sentMsgs w) /\
    Forall good_packet pkts /\ (* since pkts is under-specified *)
    (forall n, is_byz n = false ->
      exists used, In (mkP src n (InitialMsg r (value_bft src r)) used) pkts).

  Lemma round_1_pkts : exists pkts, pkts_needed_in_round_1 pkts.
  Proof.
    unfold pkts_needed_in_round_1. saturate.
    exists (List.filter (fun p =>
      (Message_eqdec p.(msg) (InitialMsg r (value_bft src r))) &&
      (Address_eqdec (P.src p) src) && (negb (is_byz p.(dst)))) (sentMsgs w)).
    split_and?; auto using incl_filter.
    - apply Forall_forall. intros [ s d m b ] (Hin & Hcheck)%filter_In. simpl in Hcheck.
      unfold is_left in Hcheck. rewrite ! andb_true_iff, ! negb_true_iff in Hcheck. hnf. destruct_eqdec in_ Hcheck as_ ?; try eqsolve. now simplify_eq.
    - intros n Hnonbyz_n.
      pick initialmsg_sent_l2h as_ H1 by_ (pose proof (Hl2h _ Hnonbyz_src) as []). specialize (H1 _ Hstart n). rewrite Hcoh in H1.
      destruct H1 as (b & H1). exists b. unfold is_left. rewrite filter_In, ! andb_true_iff, negb_true_iff. simpl. now rewrite ! eqdec_refl.
  Qed.

  Variable (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 pkts).

  Definition round_1_end w' :=
    forall n, is_byz n = false -> In (mkP src n (InitialMsg r (value_bft src r)) true) (sentMsgs w').

  Fact round_1_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    destruct Hround1 as (_ & _ & H2). 
    hnf. intros n Hnonbyz_n. specialize (H2 _ Hnonbyz_n).
    destruct H2 as (? & H2). now apply (in_map markRcv), Hincl in H2.
  Qed.

  (* at the same time as round 1 ends *)
  Definition round_2_start w' :=
    forall n, is_byz n = false -> (w' @ n).(echoed) (src, r) = Some (value_bft src r).

  Lemma round_2_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : round_2_start w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. specialize (Hw0 _ Hnonbyz_n).
    pick initialmsg_recv_h2l as_ Hp by_ (pose proof (Hh2lr _ Hw0) as []). saturate_assumptions.
    destruct (echoed _ _) as [ v' | ] eqn:Ev' in |- *; [ | isSome_rewrite; discriminate ].
    (* TODO the following two steps are repeating in the integrity proof *)
    pick initialmsg_recv_l2h as_ H4 by_ (pose proof (Hl2h _ Hnonbyz_n) as []). specialize (H4 _ _ _ Ev'). rewrite Hcoh in H4.
    pick initialmsg_sent_h2l as_ H5 by_ (pose proof (Hh2ls _ H4) as []). saturate_assumptions. now f_equal.
  Qed.

  End Round1.

  Section Round2.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : round_2_start w).

  Definition pkts_needed_in_round_2 nonbyz_senders pkts : Prop :=
    Eval unfold pkts_multi_to_all in pkts_multi_to_all (N - f) w nonbyz_senders pkts (fun _ => EchoMsg src r (value_bft src r))
      (fun w n => (w @ n).(echoed) (src, r) = Some (value_bft src r)).

  Let nonbyz_senders := (List.filter (fun n => negb (is_byz n)) valid_nodes).

  (* in the second round, there are (N-f) non-faulty nodes broadcasting Echo messages *)
  Lemma round_2_pkts :
    exists pkts, pkts_needed_in_round_2 nonbyz_senders pkts.
  Proof.
    unfold pkts_needed_in_round_2, nonbyz_senders. saturate.
    exists (List.filter (fun p => 
      match p.(msg) with
      | EchoMsg _ _ _ => (negb (is_byz (P.src p))) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)).
    hnf. split_and?; auto using incl_filter, NoDup_filter, valid_nodes_NoDup, nonbyz_lower_bound.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      now rewrite andb_true_iff, ! negb_true_iff in Hcheck.
    - intros n1 (_ & Hnonbyz_n1)%filter_In. rewrite negb_true_iff in Hnonbyz_n1.
      hnf in Hstart. specialize (@Hstart _ Hnonbyz_n1). (* TODO why @? *) split_and?; auto.
      intros n2 Hnonbyz_n2.
      pick echomsg_sent_l2h as_ Hsent1 by_ (pose proof (Hl2h _ Hnonbyz_n1) as []). specialize (Hsent1 _ _ _ Hstart n2). rewrite Hcoh in Hsent1.
      destruct Hsent1. eexists. apply filter_In. 
      simpl. split; [ eassumption | now rewrite andb_true_iff, ! negb_true_iff ].
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround2 : pkts_needed_in_round_2 nonbyz_senders pkts).

  Definition round_2_end w' :=
    Eval unfold mutual_receiving in mutual_receiving (fun _ => EchoMsg src r (value_bft src r)) w'.

  (* FIXME: this is repeating *)
  Fact round_2_end_suffcond w' (Hincl : incl (map markRcv pkts) (sentMsgs w')) :
    round_2_end w'.
  Proof.
    hnf in Hround2. pick EchoMsg as_ HH by_ (destruct_and? Hround2).
    hnf. intros n1 Hin1 n2 Hnonbyz_n2. 
    specialize (HH n1 ltac:(unfold nonbyz_senders; rewrite filter_In, negb_true_iff; auto using Address_is_finite)).
    destruct HH as (_ & _ & HH). specialize (HH _ Hnonbyz_n2). destruct HH as (? & HH). now apply (in_map markRcv), Hincl in HH.
  Qed.

  (* at the same time as round 2 ends *)
  Definition round_3_start :=
    Eval unfold Global_Liveness.round_2_start in Global_Liveness.round_2_start src r (value_bft src r).

  Lemma round_3_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_2_end w0) : round_3_start w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. 
    hnf in Hround2. destruct Hround2 as (Hnodup & Hsize & _ & _ & HH).
    destruct (voted _ _) as [ v' | ] eqn:Ev' in |- *.
    - (* use vote_integrity *)
      f_equal.
      pose proof (vote_integrity_always_holds H_w0_reachable) as Htmp. now eapply (Htmp n src) in Ev'; try eassumption.
    - (* prove contradiction using the message size *)
      (* TODO repeating *)
      pick voted_none as_ Hp by_ (pose proof (Hst n) as []). apply Hp with (v:=value_bft src r) in Ev'.
      assert (incl nonbyz_senders (msgcnt (w0 @ n) (EchoMsg src r (value_bft src r)))) as Hincl.
      { hnf. subst nonbyz_senders. intros nn (_ & Hnonbyz_nn%negb_true_iff)%filter_In. specialize (Hw0 nn ltac:(assumption) n ltac:(assumption)).
        pick msgcnt_recv_h2l as_ Hr by_ (pose proof (Hh2lr _ Hw0) as []). saturate_assumptions. now simpl in Hr. }
      apply NoDup_incl_length in Hincl; try assumption. unfold th_echo4vote in Ev'. destruct Ev'. lia.
  Qed.

  End Round2.

End Proof_of_Validity.

End Validity.

End RBLiveness.
