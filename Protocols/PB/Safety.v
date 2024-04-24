From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.PB Require Export Invariant.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module PBSafety (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS).

Import A R V Pf VBFT BTh BSett TSS PBDT.
Import ssrbool. (* anyway *)

Module Export PBInv := PBInvariant A R Sn V Pf VBFT BTh BSett TSS0 TSS PBDT.

Set Implicit Arguments. (* anyway *)

Fact id_coh_always_holds : always_holds id_coh.
Proof. intros w Hw. induction Hw; eauto using id_coh_is_invariant. hnf. intros. reflexivity. Qed.

Fact state_invariants_always_holds : always_holds (lift_state_inv node_state_invariants).
Proof.
  intros w Hw. induction Hw; eauto using state_invariants.
  constructor; hnf; unfold initWorld, initState; simpl; intros; hnf in *; try eqsolve.
  - constructor.
  - pose proof th_output_gt_0. lia.
Qed.

Fact l2h_invariants_always_holds : always_holds (lift_node_inv node_psent_l2h_invariants).
Proof.
  eapply is_invariant_reachable_step_under_closed.
  1: hnf; intros ?????; apply l2h_invariants.
  2: apply id_coh_always_holds.
  hnf. intros. constructor; hnf; try discriminate; try contradiction.
Qed.

Fact h2l_invariants_always_holds : always_holds (lift_pkt_inv node_psent_h2l_invariants_nonbyz).
Proof.
  eapply is_invariant_reachable_step_under_closed.
  1: hnf; intros ?????; apply h2l_invariants.
  2: apply id_coh_always_holds.
  hnf. intros. constructor; hnf; try discriminate; try contradiction.
Qed.

(* useful *)
Ltac saturate :=
  let Hcoh := fresh "Hcoh" in
  let Hst := fresh "Hst" in
  let Hl2h := fresh "Hl2h" in
  let Hh2l := fresh "Hh2l" in
  (* let Hh2lbyz := fresh "Hh2lbyz" in *)
  match goal with
    H : reachable ?w |- _ => 
    pose proof (id_coh_always_holds H) as Hcoh;
    pose proof (state_invariants_always_holds H) as Hst;
    pose proof (l2h_invariants_always_holds H) as Hl2h;
    pose proof (h2l_invariants_always_holds H) as Hh2l
    (* pose proof (proj2 h2l_invariants _ H) as Hh2lbyz *)
  end.

(* TODO how to state uniqueness? or, how to express "producing a string"? *)

Definition node_in_counter w : Prop :=
  forall n src r,
    In src (map fst ((w @ n).(counter) r)) ->
    In (src, light_sign (r, (value_bft n r).1) (lightkey_map src)) ((w @ n).(counter) r).

Definition echoed_backtrack w : Prop :=
  forall src dst r vpf, is_byz src = false -> is_byz dst = false ->
    (w @ dst).(echoed) (src, r) = Some vpf -> vpf = value_bft src r.

Definition counter_backtrack w : Prop :=
  forall src dst r, is_byz src = false -> is_byz dst = false ->
    In src (map fst ((w @ dst).(counter) r)) -> 
    (w @ src).(echoed) (dst, r) = Some (value_bft dst r) /\ ex_validate r (value_bft dst r).1 (value_bft dst r).2.

(* also implies external validity *)
Definition output_ok w : Prop :=
  forall n r cs, is_byz n = false -> (w @ n).(output) r = Some cs ->
    let: v := (value_bft n r).1 in
    ex_validate r v (value_bft n r).2 /\ combined_verify (r, v) cs /\
    (exists l : list Address, 
      List.NoDup l /\ t0 < length l /\ 
      (forall n0, In n0 l -> is_byz n0 = false /\ (w @ n0).(echoed) (n, r) = Some (value_bft n r))).

Lemma node_in_counter_always_holds : always_holds node_in_counter.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros n ? r ((src & lsig) & <- & Hin)%in_map_iff. simpl.
  pick counter_ok as_ H1 by_ (pose proof (Hst n) as []). pose proof Hin as ->%H1%lightkey_correct.
  now rewrite Hcoh in Hin.
Qed.

Lemma echoed_backtrack_always_holds : always_holds echoed_backtrack.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros src dst r (v, pf) Hnonbyz_src Hnonbyz_dst E.
  (* <-- InitMsg recv *)
  pick initmsg_recv_l2h as_ H4 by_ (pose proof (Hl2h _ Hnonbyz_dst) as []). saturate_assumptions!. rewrite Hcoh in H4.
  (* <-- sent *)
  pick initmsg_sent_h2l as_ H5 by_ (pose proof (Hh2l _ H4) as []). saturate_assumptions. now destruct H5 as (_ & ->).
Qed.

Lemma counter_backtrack_always_holds : always_holds counter_backtrack.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros ? dst r Hnonbyz_src Hnonbyz_dst ((src & lsig1) & <- & Hin)%in_map_iff. simpl in Hnonbyz_src.
  (* in counter <-- EchoMsg recv *)
  pick echomsg_recv_l2h as_ H2 by_ (pose proof (Hl2h _ Hnonbyz_dst) as []). apply H2 in Hin. rewrite Hcoh in Hin.
  (* <-- echoed *)
  pick echomsg_sent_h2l as_ H3 by_ (pose proof (Hh2l _ Hin) as []). saturate_assumptions.
  destruct (echoed (w @ src) (dst, r)) as [ (v, pf) | ] eqn:E; try contradiction. subst lsig1. simpl. rewrite E.
  (* <-- validated *)
  pick echoed_ex_valid as_ H6 by_ (pose proof (Hst src) as []). saturate_assumptions!. 
  eapply echoed_backtrack_always_holds in E; auto. now rewrite <- E.
Qed.

Lemma output_ok_always_holds : always_holds output_ok.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros.
  (* basic *)
  pick output_some as_ H1 by_ (pose proof (Hst n) as []). specialize (H1 r). isSome_rewrite. saturate_assumptions.
  pick from_nodup as_ Hnodup by_ (pose proof (Hst n) as []). specialize (Hnodup r).
  split_and?.
  - apply at_least_one_nonfaulty in Hnodup.
    2: rewrite map_length, H1; unfold th_output; pose proof N_minus_2t0_gt_0; lia.
    destruct Hnodup as (n1 & Hnonbyz_n1 & Hin).
    now apply counter_backtrack_always_holds in Hin.
  - apply combine_correct.
    eexists. split; [ apply Hnodup | ]. split; [ rewrite map_length, H1; reflexivity | ].
    pick output_is_delivery_cert as_ H2 by_ (pose proof (Hst n) as []). apply H2 in H0. subst cs. unfold delivery_cert. f_equal.
    pick counter_ok as_ H3 by_ (pose proof (Hst n) as []). fold (counter_ok (w @ n)) in H3. rewrite counter_ok_alt in H3. 
    rewrite H3 at 1. now rewrite map_map, Hcoh.
  - exists (List.filter (fun n => negb (is_byz n)) (map fst (counter (w @ n) r))).
    split; [ auto using NoDup_filter | ].
    split. 1:{ pose proof (filter_nonbyz_lower_bound_t0 Hnodup). rewrite map_length, H1 in H2. unfold th_output in H2. pose proof t0_lt_N_minus_2t0. lia. }
    intros n1 (Hin & Hnonbyz_n1%negb_true_iff)%filter_In. split; auto.
    apply counter_backtrack_always_holds in Hin; auto. tauto.
Qed.

End PBSafety.