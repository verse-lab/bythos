From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.RB Require Export Safety.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

(* split_and, but accumulating *)
Global Ltac split_and_acc_r H :=
  match goal with
  | |- _ /\ _ => 
    let HH := fresh H in
    apply and_wlog_r; [ | intros HH; split_and_acc_r H ]
  | _ => idtac
  end.

Module RBLiveness (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBS := RBSafety A R V VBFT BTh BSett.

(* at the beginning *)
Definition some_receives src r v w : Prop := exists n, is_byz n = false /\ In v ((w @ n).(output) (src, r)).

(* at the end *)
Definition all_receives src r v w : Prop := forall n, is_byz n = false -> In v ((w @ n).(output) (src, r)).

Section Proof_of_Global_Liveness.

  Variables (src : Address) (r : Round) (v : Value).

  Section Prelude.

  (* the structure of Round 1 and Round 2 are similar, so some conclusions might be reused *)

  Definition pkts_needed size w nonbyz_senders pkts : Prop :=
    Forall (fun n => is_byz n = false) nonbyz_senders /\
    List.NoDup nonbyz_senders /\
    size <= length nonbyz_senders /\
    incl pkts (sentMsgs w) /\
    Forall good_packet pkts /\ (* since pkts is under-specified *)
    (forall n1,
      In n1 nonbyz_senders -> 
      (w @ n1).(voted) (src, r) = Some v /\
      (forall n2, is_byz n2 = false ->
        exists used, In (mkP n1 n2 (ReadyMsg src r v) used) pkts)).
  (*
  Lemma pkts_needed_by_voted_nodes w (H_w_reachable : reachable w)
    (Hnum :  :
    exists nonbyz_senders pkts, pkts_needed_in_round_1 nonbyz_senders pkts.
  Proof.
    saturate.
    destruct Hstart as (n & Hnonbyz_n & Hr).
    (* TODO the following two steps are familiar ... *)
    pick output_coh_fwd as_ H1 by_ (pose proof (Hst n) as []). specialize (H1 _ _ _ Hr).
    unfold th_ready4output in H1.
    pick msgcnt_coh as_ Hnodup by_ (pose proof (Hst n) as []). specialize (Hnodup (ReadyMsg src r v)). simpl in Hnodup.
    pose proof (filter_nonbyz_lower_bound_t0 Hnodup) as Hlen.
    (* match type of H1 with _ <= length ?ll => remember ll as l_orig end. *)
    match type of Hlen with _ <= length ?ll => exists ll,
      (List.filter (fun p => 
      match p.(msg) with
      | ReadyMsg _ _ _ =>
        (is_left (in_dec Address_eqdec (P.src p) ll)) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)) end.
    hnf. split_and?; auto using NoDup_filter, incl_filter; try lia.
    - apply Forall_forall. now intros x (Hin & Hnonbyz%negb_true_iff)%filter_In.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      apply andb_true_iff in Hcheck. destruct Hcheck as (Htmp%in_dec_is_left%filter_In & Htmp0).
      hnf. now rewrite <- ! negb_true_iff.
    - intros n1 Hin1_backup.
      pose proof Hin1_backup as (Hin1 & Hnonbyz_n1%negb_true_iff)%filter_In.
      (* TODO the following two steps has some overlap with a previous proof *)
      pick msgcnt_recv_fwd as_ Hsent1 by_ (pose proof (Hfwd _ Hnonbyz_n) as []). specialize (Hsent1 _ _ Hin1). rewrite Hcoh in Hsent1.
      pick readymsg_sent_bwd as_ Hv1 by_ (pose proof (Hbwds _ Hsent1) as []). saturate_assumptions. split; auto. (* solve a side goal *)
      intros n2 Hnonbyz_n2.
      pick readymsg_sent_fwd as_ Hsent1' by_ (pose proof (Hfwd _ Hnonbyz_n1) as []). specialize (Hsent1' _ _ _ Hv1 n2). rewrite Hcoh in Hsent1'.
      destruct Hsent1'. eexists. apply filter_In. 
      simpl. split; [ eassumption | apply andb_true_iff; split; [ now apply in_dec_is_left | now rewrite Hnonbyz_n2 ] ].
  Qed.
  *)

  End Prelude.

  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : some_receives src r v w).

  Definition pkts_needed_in_round_1 nonbyz_senders pkts : Prop :=
    Forall (fun n => is_byz n = false) nonbyz_senders /\
    List.NoDup nonbyz_senders /\
    N - (t0 + t0) <= length nonbyz_senders /\
    incl pkts (sentMsgs w) /\
    Forall good_packet pkts /\ (* since pkts is under-specified *)
    (forall n1,
      In n1 nonbyz_senders -> 
      (w @ n1).(voted) (src, r) = Some v /\
      (forall n2, is_byz n2 = false ->
        exists used, In (mkP n1 n2 (ReadyMsg src r v) used) pkts)).

  (* in the first round, there are (N-2t0) non-faulty nodes broadcasting Ready messages *)
  Lemma round_1_pkts :
    (* HMM neither sigT nor pure exists works well here *)
    (*
    exists pkts nonbyz_senders, 
    (* { pkts : list Packet & 
      { nonbyz_senders : list Address & *)
        incl pkts (sentMsgs w) /\
        Forall good_packet pkts /\ (* kind of redundant *)
        Forall (fun n => is_byz n = false) nonbyz_senders /\
        List.NoDup nonbyz_senders /\
        N - (t0 + t0) <= length nonbyz_senders /\
        (forall n1 n2,
          In n1 nonbyz_senders -> In n2 nonbyz_senders ->
          exists used, In (mkP n1 n2 (ReadyMsg src r v) used) pkts).
    *)
    (*
    exists nonbyz_senders, 
      Forall (fun n => is_byz n = false) nonbyz_senders /\
      List.NoDup nonbyz_senders /\
      N - (t0 + t0) <= length nonbyz_senders /\
      (exists pkts, 
        incl pkts (sentMsgs w) /\
        Forall good_packet pkts /\ (* since pkts is under-specified *)
        (forall n1 n2,
          In n1 nonbyz_senders -> In n2 nonbyz_senders ->
          exists used, In (mkP n1 n2 (ReadyMsg src r v) used) pkts)).
    *)
    exists nonbyz_senders pkts, pkts_needed_in_round_1 nonbyz_senders pkts.
  Proof.
    saturate.
    destruct Hstart as (n & Hnonbyz_n & Hr).
    (* TODO the following two steps are familiar ... *)
    pick output_coh_fwd as_ H1 by_ (pose proof (Hst n) as []). specialize (H1 _ _ _ Hr).
    unfold th_ready4output in H1.
    pick msgcnt_coh as_ Hnodup by_ (pose proof (Hst n) as []). specialize (Hnodup (ReadyMsg src r v)). simpl in Hnodup.
    pose proof (filter_nonbyz_lower_bound_t0 Hnodup) as Hlen.
    (* match type of H1 with _ <= length ?ll => remember ll as l_orig end. *)
    match type of Hlen with _ <= length ?ll => exists ll,
      (List.filter (fun p => 
      match p.(msg) with
      | ReadyMsg _ _ _ =>
        (is_left (in_dec Address_eqdec (P.src p) ll)) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)) end.
    hnf. split_and?; auto using NoDup_filter, incl_filter; try lia.
    - apply Forall_forall. now intros x (Hin & Hnonbyz%negb_true_iff)%filter_In.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      apply andb_true_iff in Hcheck. destruct Hcheck as (Htmp%in_dec_is_left%filter_In & Htmp0).
      hnf. now rewrite <- ! negb_true_iff.
    - intros n1 Hin1_backup.
      pose proof Hin1_backup as (Hin1 & Hnonbyz_n1%negb_true_iff)%filter_In.
      (* TODO the following two steps has some overlap with a previous proof *)
      pick msgcnt_recv_fwd as_ Hsent1 by_ (pose proof (Hfwd _ Hnonbyz_n) as []). specialize (Hsent1 _ _ Hin1). rewrite Hcoh in Hsent1.
      pick readymsg_sent_bwd as_ Hv1 by_ (pose proof (Hbwds _ Hsent1) as []). saturate_assumptions. split; auto. (* solve a side goal *)
      intros n2 Hnonbyz_n2.
      pick readymsg_sent_fwd as_ Hsent1' by_ (pose proof (Hfwd _ Hnonbyz_n1) as []). specialize (Hsent1' _ _ _ Hv1 n2). rewrite Hcoh in Hsent1'.
      destruct Hsent1'. eexists. apply filter_In. 
      simpl. split; [ eassumption | apply andb_true_iff; split; [ now apply in_dec_is_left | now rewrite Hnonbyz_n2 ] ].
  Qed.

  (* universally quantified *)
  Variable (nonbyz_senders : list Address) (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 nonbyz_senders pkts).

  Definition round_1_end w' :=
    forall n1, In n1 nonbyz_senders -> 
      forall n2, is_byz n2 = false ->
        In (mkP n1 n2 (ReadyMsg src r v) true) (sentMsgs w').

  (* at the same time as round 1 ends *)
  Definition round_2_start w' :=
    forall n, is_byz n = false -> (w' @ n).(voted) (src, r) = Some v.

  Fact round_1_end_suffcond w' (Hincl : incl (map receive_pkt pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    hnf in Hround1. pick ReadyMsg as_ HH by_ (destruct_and? Hround1).
    hnf. intros n1 Hin1 n2 Hnonbyz_n2. specialize (HH _ Hin1).
    destruct HH as (? & HH). specialize (HH _ Hnonbyz_n2). destruct HH as (? & HH). now apply (in_map receive_pkt), Hincl in HH.
  Qed.

  Lemma round_2_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : round_2_start w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. 
    hnf in Hround1. destruct Hround1 as (Hf_nonbyz & Hnodup & Hsize & _ & _ & HH).
    destruct (voted _ _) as [ v' | ] eqn:Ev' in |- *.
    - (* use vote_uniqueness *)
      f_equal. 
      pose proof N_minus_2t0_gt_0 as Ht0. pose proof (length_gt_0_notnil (l:=nonbyz_senders) ltac:(lia)) as (_ & (nn & Hin)).
      pose proof (HH _ Hin) as (Hvnn & _). 
      rewrite Forall_forall in Hf_nonbyz. pose proof (Hf_nonbyz _ Hin) as Hnonbyz_nn.
      (* FIXME: make this usage of persistence a tactic? *)
      pose proof (persistent_invariants_trace Htrace0) as Hps. rewrite <- Ew0 in *.
      pick voted_persistent as_ Hp by_ (pose proof (Hps nn) as []). apply Hp in Hvnn.
      eapply (Hvu src r n nn); eassumption.
    - (* prove contradiction using the message size *)
      pick voted_coh_none as_ Hp by_ (pose proof (Hst n) as []). apply Hp with (v:=v) in Ev'.
      assert (incl nonbyz_senders (msgcnt (w0 @ n) (ReadyMsg src r v))) as Hincl.
      { hnf. intros nn Hin. specialize (Hw0 _ Hin n Hnonbyz_n).
        pick msgcnt_recv_bwd as_ Hr by_ (pose proof (Hbwdr _ Hw0) as []). saturate_assumptions. now simpl in Hr. }
      apply NoDup_incl_length in Hincl; try assumption. unfold th_ready4ready in Ev'. destruct Ev'. lia.
  Qed.

  End Round1.

  Section Round2.

  Variable (w : World).
  Hypothesis (H_w_reachable : reachable w) (Hstart : round_2_start w).


  




End Proof_of_Global_Liveness.


Section Proof_of_Validity1.

End Proof_of_Validity1.

End RBLiveness.

Module RBLiveness (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBS := RBSafety A R V VBFT BTh BSett.
