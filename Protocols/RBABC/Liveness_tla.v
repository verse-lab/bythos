From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses. 
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Composition Require Export Liveness_tla.
From Bythos.Protocols.RBABC Require Export Protocol.
From Bythos.Protocols.ABC Require Import Liveness_tla.
From Bythos.Protocols.RB Require Import Liveness_tla.

Module RBACLiveness2 (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f).

Import A R ARP V VBFT BTh BSett.
Import ssrbool. (* anyway *)

(* TODO seems like there are some diamond issue, but skip for now *)
Module RBLiveTLA := RBLiveness2 A R V VBFT BTh BSett.
Module ACLiveTLA := ACLiveness2 A Sn V BTh BSett PPrim TSSPrim.

Import RBLiveTLA.RBLive.RBS.RBInv ACLiveTLA.ACLive.ACS.ACInv.

Module Export CM := EmptyModule <+ CompMessage RBN.M ACN.M.
Module Export SCPT := RBACTrigger A R ARP Sn V VBFT BTh RBN.M PPrim TSSPrim ACN.ACDT ACN.M
  CM RBN.P ACN.P0 RBN.RBP ACN.ACP.

Include CompLiveness2 A RBN.M ACN.M BTh RBN.P ACN.P0 RBN.RBP ACN.ACP SCPT RBN.Ns ACN.Ns
  BSett RBN.RBAdv ACN.ACAdv RBN.PSOp ACN.PSOp RBN ACN.

Definition all_receives_RB src r v w : Prop :=
  RBLiveTLA.RBLive.all_receives src r v (world_proj1 w).

Lemma go1 : forall src r f0 (Hnonbyz_src : is_byz src = false),
  ⌜ init ⌝ ∧ nextf f0 ∧ fairness ∧ disambiguation f0 ⊢
  ⌜ λ w, (w @ src).(st1).(sent) r ⌝ ~~> ⌜ all_receives_RB src r (value_bft src r) ⌝.
Proof.
  intros. hnf. intros e (Hini & Hf & Hfair & Hdg).
  pose proof (exec_norm1_sound_next ltac:(intros; hnf; auto) e f0 Hf) as (Hrel & Hf').
  pose proof (exec_norm1_sound_init e f0 Hini) as Hini'.
  set (e' := exec_norm1 f0 e) in Hrel, Hf', Hini'.
  eapply exec_norm1_sound_fairness in Hfair; eauto.
  pose proof (conj Hini' (conj (RBLiveTLA.nextf_impl_next _ _ Hf') Hfair)) as HH%(RBLiveTLA.validity_in_tla _ r Hnonbyz_src).
  apply RBLiveTLA.leads_to_exec_rel with (e':=exec_proj1 e) in HH; auto.
  - hnf; intros ?? (HHH & ?); now rewrite HHH.
  - apply RBN.Ns.stmap_peq_cong_implies_World_rel_cong, RBLiveTLA.RBLive.all_receives_stmap_peq_cong.
Qed.

Definition all_honest_nodes_submitted_AC v w : Prop :=
  ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_submitted v (world_proj2 w).

Definition all_honest_nodes_confirmed_AC v w : Prop :=
  ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_confirmed v (world_proj2 w).

Lemma go2 : forall f0 v,
  ⌜ init ⌝ ∧ nextf f0 ∧ fairness ∧ disambiguation f0 ⊢
  ⌜ all_honest_nodes_submitted_AC v ⌝ ~~> ⌜ all_honest_nodes_confirmed_AC v ⌝.
Proof.
  intros. hnf. intros e (Hini & Hf & Hfair & Hdg).
  pose proof (exec_norm2_sound_next ACAdv.byz_constraints_World_rel e f0 Hf) as (Hrel & Hf').
  pose proof (exec_norm2_sound_init e f0 Hini) as Hini'.
  set (e' := exec_norm2 f0 e) in Hrel, Hf', Hini'.
  eapply exec_norm2_sound_fairness in Hfair; eauto.
  pose proof (conj Hini' (conj (ACLiveTLA.nextf_impl_next _ _ Hf') Hfair)) as HH%(ACLiveTLA.terminating_convergence_in_tla v num_byz_le_f).
  apply ACLiveTLA.leads_to_exec_rel with (e':=exec_proj2 e) in HH; auto.
  all: apply ACN.Ns.stmap_peq_cong_implies_World_rel_cong; 
    auto using ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_submitted_stmap_peq_cong, 
      ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_confirmed_stmap_peq_cong.
Qed.

Lemma inv1 : forall w, reachable w -> 
  forall n, is_byz n = false ->
    (* this holds for any num_byz *)
    ((ACN.Ns.localState (world_proj2 w) n).(submitted_value) = None <->
      (RBN.Ns.localState (world_proj1 w) n).(output) arp = nil) /\
    (forall v, (ACN.Ns.localState (world_proj2 w) n).(submitted_value) = Some v ->
      In v ((RBN.Ns.localState (world_proj1 w) n).(output) arp)).
Proof.
  intros w Hr n Hnonbyz. induction Hr as [ | q w w' Hstep Hr IH ].
  - now cbn.
  - (* preparation *)
    (* output persistence *)
    pose proof (ssd_proj1_sound Hstep) as (Hstep' & Hrel).
    pose proof (RBLiveTLA.RBLive.RBS.RBInv.persistent_invariants Hstep') as Htmp.
    apply (RBN.lift_state_pair_inv_mirrors_World_rel (w1:=world_proj1 w) ltac:(reflexivity) Hrel) in Htmp.
    pick output_persistent as_ Ho by_ (pose proof (Htmp n) as []). specialize (Ho arp.1 arp.2). rewrite -surjective_pairing in Ho.
    clear Htmp Hstep' Hrel.

    (* brute-force discussion is inevitable? *)
    (* TODO need to reason about how handlers deal with some specific fields ... very cumbersome *)
    inversion_step' Hstep; auto.
    all: unfold world_proj1, stmap_proj1, world_proj2, stmap_proj2 in Ho, IH |- *; simpl in Ho, IH |- *.
    all: unfold upd; destruct_eqdec as_ ->; auto.
    all: rewrite upd_refl in Ho.
    + destruct msg as [ mRB | mAC ].
      * rewrite (surjective_pairing (RBN.RBP.procMsg _ _ _)) in Ef.
        destruct (trigger_procMsg _ _) as [ [ v ] | ] eqn:Etr in Ef.
        --(* prepare for the indirectly ... *)
          (* TODO streamline this? *)
          pose proof (reachable_proj2 Hr ACAdv.byz_constraints_World_rel) as (w_ & Hrel_ & Hr_).
          pose proof Hrel_ as Htmp. apply ACN.next_world_preserves_World_rel with (q:=ACN.Intern n (SubmitIntTrans v)) in Htmp.
          cbn in Htmp. rewrite (proj1 Hrel_) in Htmp. unfold world_proj2, stmap_proj2 in Htmp. simpl in Htmp.
          rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in Htmp. 
          (* another way around *)
          eapply ssd_proj2_sound in Hstep. cbn in Hstep. unfold world_proj2, stmap_proj2 in Hstep. simpl in Hstep.
          rewrite (surjective_pairing (RBN.RBP.procMsg _ _ _)) Etr in Hstep.
          rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in Ef, Hstep. simplify_eq. simpl in Hstep |- *.
          unfold world_proj1, stmap_proj1, world_proj2, stmap_proj2 in Hstep. rewrite !upd_refl /= Etr in Hstep.
          (* TODO why keep rewriting ... *)
          cbn in Hstep. rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in Hstep. simpl in Hstep. 
          (* step for the reachable one *)
          destruct Hstep as (Hstep & Hrel).
          pose proof Hstep as Hstep_. eapply ACN.step_mirrors_World_rel in Hstep; try apply ACAdv.byz_constraints_World_rel. (* FIXME: this is bad! *)
          2: symmetry; apply Hrel_.
          (* 2: rewrite Htmp.  *)
          (* TODO why keep rewriting ... *)
          2: simpl; rewrite -> (proj1 Hrel_), -> (surjective_pairing (ACN.ACP.procInt _ _)).
          2: simpl; unfold stmap_proj2; rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)).
          2: simpl; rewrite Htmp; reflexivity.
          (* discuss *)
          unfold trigger_procMsg in Etr. 
          do 2 (match type of Etr with (match ?qq with _ => _ end = _) => destruct qq eqn:?; try discriminate end). simplify_eq.
          apply proj1, proj2 in IH. saturate_assumptions.
          (* indirectly *)
          rewrite Hrel in Htmp. apply psent_mnt_sound_pre in Hstep; auto. destruct Hstep as (_ & Hstep & _). rewrite (proj1 Hrel_) in Hstep. specialize (Hstep IH).
          (* TODO why keep rewriting ... *)
          simpl in Hstep. rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)), -> (proj1 Hrel_) in Hstep. simpl in Hstep. rewrite -> ACN.Ns.upd_refl in Hstep.
          setoid_rewrite Hstep. simpl. clear. eqsolve.
        --simplify_eq. simpl. split. 
          ++rewrite (proj1 IH). unfold trigger_procMsg in Etr.
            match type of Etr with (match ?qq with _ => _ end = _) => destruct qq eqn:E end.
            **match type of Etr with (match ?qq with _ => _ end = _) => now destruct qq end.
            **split; intros H; try discriminate. specialize (Ho _ (or_introl eq_refl)). simpl in Ho. now rewrite H in Ho.
          ++intros v H. pose proof (proj2 IH v H) as H0. apply Ho in H0. now simpl in H0.
      * rewrite (surjective_pairing (ACN.ACP.procMsg _ _ _)) in Ef. simplify_eq. simpl.
        (* indirectly *)
        eapply ssd_proj2_sound in Hstep. cbn in Hstep. unfold world_proj2, stmap_proj2 in Hstep. simpl in Hstep.
        rewrite (surjective_pairing (ACN.ACP.procMsg _ _ _)) in Hstep. simpl in Hstep.
        destruct Hstep as (Hstep & Hrel). apply inv_buffer_received_only_pre with (nn:=n) in Hstep; auto. simpl in Hstep.
        apply proj2 in Hstep. rewrite ACN.Ns.upd_refl in Hstep. now rewrite Hstep.
    + (* this part of brute force is not difficult *)
      unfold procInt, trigger_procInt in E. rewrite (surjective_pairing (RBN.RBP.procInt _ _)) in E. simplify_eq. simpl.
      unfold RBN.RBP.procInt. destruct (w @ n).(st1) as [ ? sent0 ???? ]. destruct (sent0 t); simpl; auto.
Qed.

Lemma inv1' : forall w, reachable w -> 
  forall n, is_byz n = false ->
    (* this holds for any num_byz *)
    (forall v, In v ((RBN.Ns.localState (world_proj1 w) n).(output) arp) ->
      (ACN.Ns.localState (world_proj2 w) n).(submitted_value) = Some v).
Proof.
  intros w Hr n Hnonbyz v Hin. destruct (submitted_value _) as [ v0 | ] eqn:E.
  - apply inv1 in E; auto.
    (* single output *)
    pose proof (RBLiveTLA.RBLive.RBS.output_uniqueness_always_holds) as Htmp2.
    eapply always_holds_proj1_apply in Htmp2; try apply Hr; auto.
    2: intros; hnf; auto.
    (* TODO move this subgoal somewhere else? *)
    2:{ intros ?? Hre. unfold RBLiveTLA.RBLive.RBS.output_uniqueness. now setoid_rewrite (proj1 Hre). }
    unfold world_proj1, stmap_proj1 in Htmp2. hnf in Htmp2. cbn in Htmp2. 
    specialize (Htmp2 n n arp.1 arp.2 v0 v Hnonbyz Hnonbyz). 
    rewrite -surjective_pairing in Htmp2. saturate_assumptions!. now subst.
  - apply inv1 in E; auto. rewrite E in Hin. contradiction.
Qed.

Lemma connector w (Hr : reachable w) :
  all_receives_RB arp.1 arp.2 (value_bft arp.1 arp.2) w ->
  all_honest_nodes_submitted_AC (value_bft arp.1 arp.2) w.
Proof.
  intros H. hnf in H |- *. intros n Hnonbyz. saturate_assumptions!.
  rewrite <- surjective_pairing in H. apply inv1' in H; auto.
Qed.

Lemma validity_overall f (Hnonbyz : is_byz arp.1 = false) :
  ⌜ init ⌝ ∧ nextf f ∧ fairness ∧ disambiguation f ⊢
  ⌜ λ w, (w @ arp.1).(st1).(sent) arp.2 ⌝ ~~> ⌜ all_honest_nodes_confirmed_AC (value_bft arp.1 arp.2) ⌝.
Proof.
  tla_apply (leads_to_trans _ (⌜ all_honest_nodes_submitted_AC (value_bft arp.1 arp.2) ⌝)); tla_split.
  1: tla_apply (leads_to_trans _ (⌜ all_receives_RB arp.1 arp.2 (value_bft arp.1 arp.2) ⌝)); tla_split.
  all: auto using go1, go2.
  (* TODO make a rule? *)
  intros e (Hini & Hnext & _ & _). unseal. exists 0. simpl. apply connector; auto.
  apply reachable_in_tla. split; auto. now apply nextf_impl_next in Hnext.
Qed. 

End RBACLiveness2.
