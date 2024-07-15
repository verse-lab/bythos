From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.ABC Require Export Invariant.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module ACSafety (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.t0).

Import A V (* VBFT *) BTh BSett.
Import ssrbool. (* anyway *)

Module Export ACInv := ACInvariant A Sn V (* VBFT *) BTh BSett PPrim TSSPrim.
Import ACN.ACDT.P ACN.ACDT.TSS.

Set Implicit Arguments. (* anyway *)

(* useful *)
Ltac saturate :=
  let Hcoh := fresh "Hcoh" in
  let Hst := fresh "Hst" in
  let Hl2h := fresh "Hl2h" in
  let Hh2l := fresh "Hh2l" in
  let Hh2lbyz := fresh "Hh2lbyz" in
  match goal with
    H : reachable ?w |- _ => 
    pose proof (id_coh_always_holds H) as Hcoh;
    pose proof (state_invariants H) as Hst;
    pose proof (l2h_invariants H) as Hl2h;
    pose proof (proj1 h2l_invariants _ H) as Hh2l;
    pose proof (proj2 h2l_invariants _ H) as Hh2lbyz
  end.

Definition genproof_soundness w : Prop :=
  forall n nb, is_byz n = false -> In nb (genproof (w @ n).(received_certs)) ->
    is_byz nb.

(* directly behave as Byz *)
Definition behave_byz_is_byz w :=
  forall n v1 v2 sig1 sig2 lsig1 lsig2 dst1 dst2, 
    v1 <> v2 ->
    In (mkP n dst1 (SubmitMsg v1 lsig1 sig1) true) (sentMsgs w) ->
    In (mkP n dst2 (SubmitMsg v2 lsig2 sig2) true) (sentMsgs w) ->
    is_byz n.

Definition agreement w :=
  forall n1 n2, 
    is_byz n1 = false -> is_byz n2 = false ->
    (w @ n1).(conf) -> (w @ n2).(conf) ->
    match (w @ n1).(submitted_value), (w @ n2).(submitted_value) with
    | Some v1, Some v2 => v1 = v2
    | _, _ => False
    end.

Section Main_Proof.

Local Fact zip_aux_pre {A B : Type} (l1 : list A) : forall (l2 : list B)
  (Hsize : length l1 = length l2)
  a (Hin : In a l1), exists b, In (a, b) (combine l1 l2).
Proof.
  induction l1 as [ | aa l1 IH ]; intros.
  - now simpl in Hin.
  - destruct l2 as [ | bb l2 ]; simpl in Hsize; try lia.
    simpl in Hin |- *.
    destruct Hin as [ <- | Hin ].
    + exists bb.
      now left.
    + injection Hsize as Hsize.
      specialize (IH _ Hsize _ Hin).
      destruct IH as (b & IH).
      eauto.
Qed.

Local Fact zip_aux {A B C : Type} (l1 : list A) : forall (l2 : list B) (l3 : list C)
  (Hsize1 : length l1 = length l2) (Hsize2 : length l1 = length l3)
  a c (Hin : In (a, c) (combine l1 l3)),
  exists b, In (a, b, c) (combine (combine l1 l2) l3).
Proof.
  induction l1 as [ | aa l1 IH ]; intros.
  - now simpl in Hin.
  - destruct l2 as [ | bb l2 ], l3 as [ | cc l3 ]; simpl in Hsize1, Hsize2; try lia.
    simpl in Hin |- *.
    destruct Hin as [ Hin | Hin ].
    + simplify_eq.
      exists bb.
      now left.
    + injection Hsize1 as Hsize1.
      injection Hsize2 as Hsize2.
      specialize (IH _ _ Hsize1 Hsize2 _ _ Hin).
      destruct IH as (b & IH).
      eauto.
Qed.

Lemma genproof_soundness_always_holds : always_holds genproof_soundness.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros n nb Hnonbyz Hcheck.
  (* prove by contradiction *)
  destruct (is_byz nb) eqn:E; auto.
  rewrite (proj2 genproof_correct) in Hcheck.
  destruct Hcheck as (v1 & v2 & sig1 & sig2 & nsigs1 & nsigs2 & Hvneq & Hin1 & Hin2 & Hin_nsigs1 & Hin_nsigs2).
  (* cert in rcerts --> valid Confirm msg *)
  pick inv_rcerts_mixin as_ Hrcerts by_ (pose proof (Hst n) as []).
  pose proof (Hrcerts _ _ Hin1) as (Hnsigs_valid1 & _ & _).
  pose proof (Hrcerts _ _ Hin2) as (Hnsigs_valid2 & _ & _).
  (* knowing signature *)
  pose proof Hin_nsigs1 as Hin_nsigs1_backup.
  pose proof Hin_nsigs2 as Hin_nsigs2_backup.
  eapply valid_cert_valid_sig in Hin_nsigs1, Hin_nsigs2; try eassumption. subst sig1 sig2.
  (* knowing the two nodes who accepted nb *)
  pick inv_rcerts_correct as_ Hrcerts_trace by_ (pose proof (Hl2h _ Hnonbyz) as []). rewrite Hcoh in Hrcerts_trace.
  apply Hrcerts_trace in Hin1, Hin2.
  destruct Hin1 as (src1 & Hin1), Hin2 as (src2 & Hin2).
  (* since we assumed that nb is non-Byz, now get to know its submitted value *)
  assert (forall v nsigs src dst used
    (Hin : In (mkP src dst (ConfirmMsg (v, nsigs)) used) (sentMsgs w)) (* no matter who sends to whom *)
    (Hin_nsigs : In (nb, sign v (key_map nb)) nsigs),
    (w @ nb).(submitted_value) = Some v) as Htraceback.
  { intros v0 nsigs0 src0 dst0 used0 Hin Hin_nsigs.
    destruct (is_byz src0) eqn:Ebyz0.
    - (* since Byz nodes cannot forge signatures ... *)
      pick inv_confirmmsg_correct_byz as_ H2 by_ (pose proof (Hh2lbyz _ Hin) as []).
      unfold cert_correct, sig_seen_in_history in H2. 
      specialize (H2 Ebyz0 _ _ Hin_nsigs E (correct_sign_verify_ok _ _)).
      destruct H2 as (? & ? & ? & H2). 
      pick inv_submitmsg_correct as_ Ht by_ (pose proof (Hh2l _ H2) as []). tauto.
    - pick inv_confirmmsg_correct_nonbyz as_ H2 by_ (pose proof (Hh2l _ Hin) as []).
      simpl in H2. saturate_assumptions. destruct H2 as (_ & _ & Ev0 & Hcert).
      assert (exists lsig, In (nb, lsig, sign v0 (key_map nb))
        (zip_from_lsigs_sigs (w @ src0))) as (lsig & Hin_zip).
      { subst. unfold zip_from_lsigs_sigs, zip_from_sigs in *.
        pick inv_set_size as_ Htmp by_ (pose proof (Hst src0) as []). apply zip_aux; tauto. }
      pick inv_nsigs_correct as_ H3 by_ (pose proof (Hl2h _ Ebyz0) as []).
      eapply H3 in Hin_zip; eauto. 
      (* coming back! *)
      pick inv_submitmsg_correct as_ Ht by_ (pose proof (Hh2l _ Hin_zip) as []). tauto.
  }
  apply Htraceback in Hin1; try assumption.
  apply Htraceback in Hin2; try assumption.
  eqsolve.
Qed.

Lemma behave_byz_is_byz_always_holds : always_holds behave_byz_is_byz.
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros. 
  (* prove by contradiction *)
  destruct (is_byz n) eqn:E; auto.
  pick inv_submitmsg_correct as_ Ht1 by_ (pose proof (Hh2l _ H0) as []).
  pick inv_submitmsg_correct as_ Ht2 by_ (pose proof (Hh2l _ H1) as []).
  eqsolve.
Qed.

(* proof by reducing to absurd, using "if a node behaves like a Byzantine node then it is"
    still, that message is possibly not sent by itself, due to key sharing *)
Lemma agreement_always_holds (H_byz_minor : num_byz < N - (t0 + t0)) : always_holds agreement. 
Proof.
  hnf. intros w Hr. saturate.
  hnf. intros n1 n2 Hnonbyz_n1 Hnonbyz_n2 Hconf_n1 Hconf_n2.
  (* in this proof, the usage of state invariants is frequent, so instantiate them first *)
  pose proof (Hst n1) as Hst_n1. pose proof (Hst n2) as Hst_n2.
  destruct_localState w n1 as_ [ ? conf1 ov1 from1 lsigs1 sigs1 rlcerts1 rcerts1 buffer1 ] eqn_ En1.
  destruct_localState w n2 as_ [ ? conf2 ov2 from2 lsigs2 sigs2 rlcerts2 rcerts2 buffer2 ] eqn_ En2.
  pick confirmed_then_submitted as_ Hv1 by_ (destruct Hst_n1).
  pick confirmed_then_submitted as_ Hv2 by_ (destruct Hst_n2). simpl_state. 
  saturate_assumptions. destruct ov1 as [ v1 | ], ov2 as [ v2 | ]; try discriminate. 
  unfold is_true in Hconf_n1, Hconf_n2. subst conf1 conf2.
  (* prove by contradiction *)
  destruct (Value_eqdec v1 v2) as [ | Hneq ]; auto. exfalso.
  (* get to know the size of quorums *)
  pick inv_submit_mixin as_ Hc1 by_ (destruct Hst_n1).
  pick inv_submit_mixin as_ Hc2 by_ (destruct Hst_n2). simpl_state. 
  unfold zip_from_sigs in Hc1, Hc2. simpl in Hc1, Hc2.
  destruct Hc1 as ((* -> & *) _ & Hcert_valid1), Hc2 as ((* -> & *) _ & Hcert_valid2).
  pick inv_conf_correct as_ Hsz1 by_ (destruct Hst_n1). (* required to show quorum size lower bound *)
  pick inv_conf_correct as_ Hsz2 by_ (destruct Hst_n2). simpl_state.
  pick inv_from_nodup as_ Hnodup1 by_ (destruct Hst_n1). (* required to show quorum size lower bound *)
  pick inv_from_nodup as_ Hnodup2 by_ (destruct Hst_n2). simpl_state.
  remember (List.filter (fun n' : Address => in_dec Address_eqdec n' from1) from2) as l eqn:El.
  (* FIXME: is the following overlapped with conflicting_cert_quorum_in_proof? *)
  assert ((N - (t0 + t0)) <= length l) as Hsize by (subst l; apply quorum_intersection; auto; lia).
  assert (Forall (fun x => is_byz x = true) l) as Hbyz.
  { (* trace back *)
    subst l. apply Forall_forall. intros n (Hin2 & Hin1%sumbool_is_left)%filter_In.
    (* show that n has equivocated (behave byz) *)
    pick inv_set_size as_ Hsz1' by_ (destruct Hst_n1).
    pick inv_set_size as_ Hsz2' by_ (destruct Hst_n2). simpl_state. 
    destruct Hsz1' as (Hsz1lsig & Hsz1sig), Hsz2' as (Hsz2lsig & Hsz2sig).
    (* TODO this is cumbersome! *)
    pose proof (zip_aux_pre _ _ Hsz1sig _ Hin1) as (sig1 & Hin1_nsig).
    pose proof (zip_aux_pre _ _ Hsz2sig _ Hin2) as (sig2 & Hin2_nsig).
    pose proof (zip_aux _ _ _ Hsz1lsig Hsz1sig _ _ Hin1_nsig) as (lsig1 & Hin1_submit).
    pose proof (zip_aux _ _ _ Hsz2lsig Hsz2sig _ _ Hin2_nsig) as (lsig2 & Hin2_submit).
    pick inv_nsigs_correct as_ Hq1 by_ (pose proof (Hl2h _ Hnonbyz_n1) as []).
    pick inv_nsigs_correct as_ Hq2 by_ (pose proof (Hl2h _ Hnonbyz_n2) as []). 
    rewrite En1 in Hq1. rewrite En2 in Hq2. unfold zip_from_lsigs_sigs in *. simpl_state.
    eapply Hq1 in Hin1_submit; try reflexivity. eapply Hq2 in Hin2_submit; try reflexivity.
    eapply behave_byz_is_byz_always_holds; eauto. }
  assert (length l <= num_byz) as Hgoal.
  { rewrite <- (forallb_filter_id is_byz l).
    - apply filter_byz_upper_bound. subst l. now apply NoDup_filter.
    - clear -Hbyz. induction Hbyz; simpl; auto. now rewrite andb_true_iff. }
  (* now simple math *)
  lia.
Qed.

End Main_Proof.

End ACSafety.
