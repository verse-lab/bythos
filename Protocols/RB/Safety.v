From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.RB Require Export Invariant.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module RBSafety (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBInv := RBInvariant A R V VBFT BTh BSett.

Set Implicit Arguments. (* anyway *)

Definition is_safety (P : World -> Prop) : Prop := forall w, reachable w -> P w.

Section Grounded_Invariants.

(* only grounded invariants shall be used in safety proofs *)

(* HMM we can have typeclasses here so that the proofs can be automated (by resolution), 
    but is that too much? *)
(*
Definition is_grounded_invariant (P : World -> Prop) : Prop :=
  P initWorld /\ is_invariant_step P.
*)
Fact grounded_invariant_is_safety P (H : is_grounded_invariant P) : is_safety P.
Proof. destruct H as (Hinit & H). hnf in H |- *. intros w Hr. induction Hr; firstorder. Qed. 

(* TODO need to control the association ... cumbersome *)
Fact grounded_invariants : is_grounded_invariant
  (fun w => (id_coh w /\
    lift_state_inv node_state_invariants w /\
    lift_node_inv node_psent_l2h_invariants w /\
    lift_pkt_inv node_psent_h2l_invariants_sent w /\
    lift_pkt_inv node_psent_h2l_invariants_recv w) /\
    (lift_node_inv echo_exists_before_vote w) /\
    (first_vote_due_to_echo w /\ vote_uniqueness w)).
Proof.
  hnf. split.
  - unfold initWorld, initState, Init.
    pose proof th_echo4vote_gt_0. pose proof th_vote4vote_gt_0. pose proof th_vote4output_gt_0. (* prepare *)
    split_and?; hnf; simpl; intros; try eqsolve; auto.
    1-2: constructor; hnf; simpl; intros; try solve [ discriminate | contradiction | constructor; auto | lia | auto ].
    + destruct msg0; auto; try constructor.
    + destruct (List.filter _ _) as [ | a l ] eqn:E; auto.
      (* FIXME: facilitate the proofs about filter? *)
      pose proof (or_introl eq_refl : In a (a :: l)) as HH. rewrite <- E, -> filter_In, -> andb_true_iff, -> negb_true_iff in HH. eqsolve.
  - (* HMM proof mode? or just auto? *)
    auto using is_invariant_step_under_closed, is_invariant_step_under_split, 
      is_invariant_step_under_clear, is_invariant_step_under_intro_l, 
      id_coh_is_invariant, state_invariants, l2h_invariants, h2l_invariants, 
      echo_exists_before_vote_is_invariant, first_vote_due_to_echo_is_invariant, vote_uniqueness_is_invariant.
Qed.

End Grounded_Invariants.

(* useful *)
Ltac saturate :=
  let Htmp := fresh "Htmp" in
  let Hcoh := fresh "Hcoh" in
  let Hst := fresh "Hst" in
  let Hl2h := fresh "Hl2h" in
  let Hh2ls := fresh "Hh2ls" in
  let Hh2lr := fresh "Hh2lr" in
  let Heebr := fresh "Heebr" in
  let Hvu := fresh "Hvu" in
  match goal with
    H : reachable ?w |- _ => 
    pose proof (grounded_invariant_is_safety grounded_invariants) as Htmp; specialize (Htmp _ H);
    simpl in Htmp; destruct Htmp as ((Hcoh & Hst & Hl2h & Hh2ls & Hh2lr) & Heebr & (_ (* not useful here *) & Hvu))
  end.

Definition vote_integrity w : Prop :=
  forall dst src r v, 
    is_byz dst = false -> is_byz src = false ->
    (w @ dst).(voted) (src, r) = Some v ->
    (w @ src).(sent) r /\ value_bft src r = v.

Definition output_integrity w : Prop :=
  forall dst src r v, 
    is_byz dst = false -> is_byz src = false ->
    In v ((w @ dst).(output) (src, r)) ->
    (w @ src).(sent) r /\ value_bft src r = v.

Definition output_uniqueness w : Prop :=
  forall dst1 dst2 src r v1 v2, 
    is_byz dst1 = false -> is_byz dst2 = false ->
    (* no matter if src is byz or not *)
    In v1 ((w @ dst1).(output) (src, r)) ->
    In v2 ((w @ dst2).(output) (src, r)) ->
    v1 = v2.

Definition single_output w : Prop :=
  forall dst src r, 
    is_byz dst = false ->
    (* no matter if src is byz or not *)
    length ((w @ dst).(output) (src, r)) <= 1.

Section Main_Proof.

Lemma vote_integrity_is_safety : is_safety vote_integrity.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros dst src r v Hnonbyz_dst Hnonbyz_src H2.
  apply Heebr (* also a step *) in H2; auto. hnf in H2. saturate_assumptions. destruct H2 as (src' & dst' & Hnonbyz_src' & Hin'').
  pick echomsg_sent_h2l as_ H3 by_ (pose proof (Hh2ls _ Hin'') as []). saturate_assumptions.
  pick initialmsg_recv_l2h as_ H4 by_ (pose proof (Hl2h _ Hnonbyz_src') as []). specialize (H4 _ _ _ H3). rewrite Hcoh in H4.
  pick initialmsg_sent_h2l as_ H5 by_ (pose proof (Hh2ls _ H4) as []). now saturate_assumptions.
Qed.

Lemma output_integrity_is_safety : is_safety output_integrity.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros dst src r v Hnonbyz_dst Hnonbyz_src Hin.
  pick output_vote_size as_ H1 by_ (pose proof (Hst dst) as []). specialize (H1 _ _ _ Hin). 
  (* TODO the following two steps have some overlap with a previous proof *)
  unfold th_vote4output in H1. pose proof t0_lt_N_minus_2t0 as Ht0.
  pick msgcnt_nodup as_ Hnodup by_ (pose proof (Hst dst) as []). 
  match type of H1 with _ <= ?ll => assert (t0 < ll) as (n & Hnonbyz_n & Hin')%at_least_one_nonfaulty by lia end.
  2: eapply (Hnodup (VoteMsg _ _ _)).
  pick msgcnt_recv_l2h as_ H2 by_ (pose proof (Hl2h _ Hnonbyz_dst) as []). specialize (H2 _ _ Hin'). rewrite Hcoh in H2.
  pick votemsg_sent_h2l as_ H4 by_ (pose proof (Hh2ls _ H2) as []). saturate_assumptions.
  (* use vote_integrity *)
  apply vote_integrity_is_safety in Hr. apply Hr in H4; auto.
Qed.

Lemma output_uniqueness_is_safety : is_safety output_uniqueness.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros dst1 dst2 src r v1 v2 Hnonbyz_dst1 Hnonbyz_dst2 Hin1 Hin2.
  destruct (Value_eqdec v1 v2) as [ | Hneq ]; auto.
  pick output_vote_size as_ Hle1 by_ (pose proof (Hst dst1) as []). specialize (Hle1 _ _ _ Hin1).
  pick output_vote_size as_ Hle2 by_ (pose proof (Hst dst2) as []). specialize (Hle2 _ _ _ Hin2). 
  (* TODO the following step has some overlap with a previous proof *)
  unfold th_vote4output in Hle1, Hle2.
  pick msgcnt_nodup as_ Hnodup1 by_ (pose proof (Hst dst1) as []). specialize (Hnodup1 (VoteMsg src r v1)).
  pick msgcnt_nodup as_ Hnodup2 by_ (pose proof (Hst dst2) as []). specialize (Hnodup2 (VoteMsg src r v2)).
  simpl in Hnodup1, Hnodup2.
  (* the basic idea is to find a non-faulty node in the quorum intersection that equivocate, and then prove False *)
  pose proof (quorum_intersection Hnodup1 Hnodup2 Hle1 Hle2) as Hq. pose proof t0_lt_N_minus_2t0 as Ht0.
  match type of Hq with _ <= ?ll => assert (t0 < ll) as (n & Hnonbyz_n & (Hin2' & Hin1'%sumbool_is_left)%filter_In)%at_least_one_nonfaulty by lia end.
  2: now apply List.NoDup_filter.
  (* TODO the following step has some overlap with a previous proof *)
  pick msgcnt_recv_l2h as_ Hsent1 by_ (pose proof (Hl2h _ Hnonbyz_dst1) as []). specialize (Hsent1 _ _ Hin1'). 
  pick msgcnt_recv_l2h as_ Hsent2 by_ (pose proof (Hl2h _ Hnonbyz_dst2) as []). specialize (Hsent2 _ _ Hin2').
  rewrite Hcoh in Hsent1, Hsent2.
  pick votemsg_sent_h2l as_ Hv1 by_ (pose proof (Hh2ls _ Hsent1) as []).
  pick votemsg_sent_h2l as_ Hv2 by_ (pose proof (Hh2ls _ Hsent2) as []).
  saturate_assumptions. congruence.
Qed.

Lemma unique_output_is_safety : is_safety single_output.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros dst src r Hnonbyz_dst.
  remember (output _ _) as l eqn:E in |- *.
  destruct l as [ | x [ | y l ] ]; simpl; auto.
  (* by using uniqueness_is_safety and setting dst1 = dst2 = dst *)
  pose proof (output_uniqueness_is_safety Hr src r x y Hnonbyz_dst Hnonbyz_dst
    ltac:(rewrite <- E; simpl; tauto) ltac:(rewrite <- E; simpl; tauto)) as ->.
  pick output_nodup as_ Hnodup by_ (pose proof (Hst dst) as []). specialize (Hnodup src r). 
  rewrite <- E, -> ! NoDup_cons_iff in Hnodup. simpl in Hnodup. tauto.
Qed.

End Main_Proof.

End RBSafety.
