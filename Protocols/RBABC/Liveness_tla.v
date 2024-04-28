From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses. 
(* From Coq Require Import ClassicalChoice. *)
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.RBABC Require Export Network.
From ABCProtocol.Protocols.ABC Require Import Liveness_tla.
From ABCProtocol.Protocols.RB Require Import Liveness_tla.

Module RBACLiveness2 (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0).

Import A R ARP V VBFT BTh BSett P TSS0 TSS.
Import ssrbool. (* anyway *)

(* TODO seems like there are some diamond issue, but skip for now *)
Module RBLiveTLA := RBLiveness2 A R V VBFT BTh BSett.
Module ACLiveTLA := ACLiveness2 A Sn V BTh BSett P TSS0 TSS.

Import RBLiveTLA.RBLive.RBS.RBInv ACLiveTLA.ACLive.ACS.ACInv.

Module Export RBACN := RBACNetwork A R ARP Sn V VBFT BTh BSett P TSS0 TSS RBN ACN.

Include LivenessTLA A M BTh BSett Pk PSOp RBACP Ns RBACAdv RBACN.

Definition exec_proj1 (e : exec World) : exec RBN.Ns.World := fun n => world_proj1 (e n).

Definition exec_proj2 (e : exec World) : exec ACN.Ns.World := fun n => world_proj2 (e n).

Definition ssdexec_proj1 (f : exec system_step_descriptor) : exec RBN.system_step_descriptor :=
  fun n => (ssd_proj1 (f n)).

Definition ssdexec_proj2 (f : exec system_step_descriptor) (e : exec World) : exec ACN.system_step_descriptor :=
  fun n => (ssd_proj2 (f n) (world_proj1 (e n)) (world_proj1 (e (S n)))).

Definition exec_norm1 f (e : exec World) : exec RBN.Ns.World :=
  RBN.final_world_n (ssdexec_proj1 f) (world_proj1 (e 0)).

Definition exec_norm2 f (e : exec World) : exec ACN.Ns.World :=
  ACN.final_world_n (ssdexec_proj2 f e) (world_proj2 (e 0)).
(* unique interpretability ... *)
(*
Definition next_proj1 (w1 w1' : RBN.Ns.World) : Prop :=
  forall q w w', system_step q w w' -> RBN.system_step (ssd_proj1 q) w1 w1'.
*)
(*
Fact next_proj1_sound w1 w1' : next_proj1 w1 w1' -> RBLiveTLA.next w1 w1'.
Proof. intros H. hnf in H |- *. 
*)
(* TODO it seems inevitable to use some kind of choice axiom to prove the existence below?
    sounds like reasonable, since we are reasoning about infinity *)
(*
Fact exec_proj1_sound (e : exec World) (H : e ⊨ □ ⟨ next ⟩) :
  ∃ (e' : exec RBN.Ns.World), 
    RBLiveTLA.exec_rel e' (exec_proj1 e) ∧
    (e' ⊨ □ ⟨ RBLiveTLA.next ⟩).
*)
Fact exec_norm1_0 e f : exec_norm1 f e 0 = exec_proj1 e 0.
Proof eq_refl.

Corollary exec_proj1_sound_init e (H : e ⊨ ⌜ init ⌝) : (exec_proj1 e ⊨ ⌜ RBLiveTLA.init ⌝).
Proof. hnf in H |- *. unfold exec_proj1. rewrite H. reflexivity. Qed.

Corollary exec_norm1_sound_init e f (H : e ⊨ ⌜ init ⌝) : (exec_norm1 f e ⊨ ⌜ RBLiveTLA.init ⌝).
Proof. hnf. rewrite exec_norm1_0. now apply exec_proj1_sound_init. Qed.

Fact exec_norm1_sound_next (e : exec World) f (Hf : e ⊨ nextf f) :
  let: e' := exec_norm1 f e in
    RBLiveTLA.exec_rel e' (exec_proj1 e) ∧
    (* (e' ⊨ □ ⟨ RBLiveTLA.next ⟩). *)
    (e' ⊨ RBLiveTLA.nextf (ssdexec_proj1 f)).
Proof.
  (*
  autounfold with tla in H. setoid_rewrite drop_n in H. simpl in H.
  pose proof (choice _ H) as (f & Hf). clear H.   (* !!!!!!!! *)
  *)
  autounfold with tla in Hf. hnf in Hf. apply and_wlog_r.
  - hnf. intros n. unfold exec_proj1, exec_norm1.
    induction n as [ | n IH ]; try reflexivity.
    rewrite RBN.final_world_n_add_1.
    pose proof (ssd_proj1_sound _ _ _ (Hf n)) as (_ & H).
    rewrite -H. now apply RBN.next_world_preserves_World_rel.
  - intros Hrel.
    split_and?; autounfold with tla.
    + intros k. (* exists (ssd_proj1 (f k)). rewrite !drop_n /=. *)
      pose proof (ssd_proj1_sound _ _ _ (Hf k)) as (Ha & Hb).
      unfold exec_norm1 in *. rewrite RBN.final_world_n_add_1. eapply RBN.step_mirrors_World_rel.
      1: symmetry; apply Hrel. 1: apply Ha. 1: intros; auto. (* nice *)
      specialize (Hrel (S k)). rewrite RBN.final_world_n_add_1 in Hrel. rewrite Hb Hrel. reflexivity.
    (* + intros k. hnf. intros q w w' Hstep. rewrite !drop_n /=.
      pose proof (ssd_proj1_sound _ _ _ Hstep) as (Ha & Hb).
      subst e'. rewrite RBN.final_world_n_add_1. eapply RBN.step_mirrors_World_rel. *)
Qed.

Fact exec_norm2_0 e f : exec_norm2 f e 0 = exec_proj2 e 0.
Proof eq_refl.

Corollary exec_proj2_sound_init e (H : e ⊨ ⌜ init ⌝) : (exec_proj2 e ⊨ ⌜ ACLiveTLA.init ⌝).
Proof. hnf in H |- *. unfold exec_proj2. rewrite H. reflexivity. Qed.

Corollary exec_norm2_sound_init e f (H : e ⊨ ⌜ init ⌝) : (exec_norm2 f e ⊨ ⌜ ACLiveTLA.init ⌝).
Proof. hnf. rewrite exec_norm2_0. now apply exec_proj2_sound_init. Qed.

Fact exec_norm2_sound_next (e : exec World) f (Hf : e ⊨ nextf f) :
  let: e' := exec_norm2 f e in
    ACLiveTLA.exec_rel e' (exec_proj2 e) ∧
    (e' ⊨ ACLiveTLA.nextf (ssdexec_proj2 f e)).
Proof.
  autounfold with tla in Hf. hnf in Hf. apply and_wlog_r.
  - hnf. intros n. unfold exec_proj2, exec_norm2.
    induction n as [ | n IH ]; try reflexivity.
    rewrite ACN.final_world_n_add_1.
    pose proof (ssd_proj2_sound _ _ _ (Hf n)) as (_ & H).
    rewrite -H. pose proof (Hf n) as EE%next_world_sound. rewrite -!EE. now apply ACN.next_world_preserves_World_rel.
  - intros Hrel.
    split_and?; autounfold with tla.
    + intros k. (* exists (ssd_proj1 (f k)). rewrite !drop_n /=. *)
      pose proof (ssd_proj2_sound _ _ _ (Hf k)) as (Ha & Hb).
      pose proof (Hf k) as EE%next_world_sound. rewrite -EE in Ha Hb. 
      unfold exec_norm2 in *. rewrite ACN.final_world_n_add_1. eapply ACN.step_mirrors_World_rel.
      1: symmetry; apply Hrel. 1: apply Ha. 1: apply ACAdv.byz_constraints_World_rel.
      specialize (Hrel (S k)). rewrite ACN.final_world_n_add_1 in Hrel. rewrite Hb Hrel. reflexivity. 
Qed.

(* TODO have no way to go ... this might be too strong, but I have no better idea
    on how to avoid ambiguity. *)
(* this may not always hold, but can be achieved at the level of network semantics
    (by requiring all resulting worlds to be normalized) *)
(* NOTE: this is stronger than what is actually needed, which is something like next_proj1 *)
Definition disambiguation f (e : exec World) : Prop :=
  forall q n, system_step q (e n) (e (S n)) → f n = q.

Fact exec_norm1_sound_fairness (e : exec World) f (H : e ⊨ nextf f) (Hdg : disambiguation f e)
  (e' : exec RBN.Ns.World) (Hrel : RBLiveTLA.exec_rel e' (exec_proj1 e))
  (* (H' : e' ⊨ □ ⟨ RBLiveTLA.next ⟩) : *)
  (H' : e' ⊨ RBLiveTLA.nextf (ssdexec_proj1 f)) :
  (e ⊨ fairness) → (e' ⊨ RBLiveTLA.fairness).
Proof.
  (* change view, get k *)
  intros Hfair%fairness_adequate; auto. 2: eapply nextf_impl_next, H. 
  apply RBLiveTLA.fairness_adequate; auto. 1: eapply RBLiveTLA.nextf_impl_next, H'. 
  hnf in Hfair |- *. intros [ src dst msg ? ] (Hs & Hd). simpl in *. intros -> n Hin.
  specialize (Hfair (mkP src dst (inl msg) false) (conj Hs Hd) eq_refl n).
  apply (proj2 (Hrel n)) in Hin. unfold exec_proj1, world_proj1 in Hin. simpl in Hin.
  apply option_map_list_In in Hin. destruct Hin as ([ ? ? [] ? ] & Hin & Hpj); try discriminate.
  cbn in Hpj. revert Hpj. intros [= -> -> -> ->]. specialize (Hfair Hin).
  destruct Hfair as (k & Hstep). 
  (* key point: the correspondence between delivery steps *)
  exists k.
  apply Hdg in Hstep. hnf in H'. specialize (H' (k + n)). 
  unfold ssdexec_proj1 in H'. rewrite Hstep in H'. now cbn in H'.
Qed.

Fact exec_norm2_sound_fairness (e : exec World) f (H : e ⊨ nextf f) (Hdg : disambiguation f e)
  (e' : exec ACN.Ns.World) (Hrel : ACLiveTLA.exec_rel e' (exec_proj2 e))
  (H' : e' ⊨ ACLiveTLA.nextf (ssdexec_proj2 f e)) :
  (e ⊨ fairness) → (e' ⊨ ACLiveTLA.fairness).
Proof.
  (* change view, get k *)
  intros Hfair%fairness_adequate; auto. 2: eapply nextf_impl_next, H. 
  apply ACLiveTLA.fairness_adequate; auto. 1: eapply ACLiveTLA.nextf_impl_next, H'. 
  hnf in Hfair |- *. intros [ src dst msg ? ] (Hs & Hd). simpl in *. intros -> n Hin.
  specialize (Hfair (mkP src dst (inr msg) false) (conj Hs Hd) eq_refl n).
  apply (proj2 (Hrel n)) in Hin. unfold exec_proj2, world_proj2 in Hin. simpl in Hin.
  apply option_map_list_In in Hin. destruct Hin as ([ ? ? [] ? ] & Hin & Hpj); try discriminate.
  cbn in Hpj. revert Hpj. intros [= -> -> -> ->]. specialize (Hfair Hin).
  destruct Hfair as (k & Hstep). 
  (* key point: the correspondence between delivery steps *)
  exists k.
  apply Hdg in Hstep. hnf in H'. specialize (H' (k + n)). 
  unfold ssdexec_proj2 in H'. rewrite Hstep in H'. now cbn in H'.
Qed.

Fact leads_to_inl e P Q (H : exec_proj1 e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) :
  e ⊨ ⌜ λ w, P (world_proj1 w) ⌝ ~~> ⌜ λ w, Q (world_proj1 w) ⌝.
Proof. revert H. unseal. (* ??? *) Qed.

Fact leads_to_inr e P Q (H : exec_proj2 e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) :
  e ⊨ ⌜ λ w, P (world_proj2 w) ⌝ ~~> ⌜ λ w, Q (world_proj2 w) ⌝.
Proof. revert H. unseal. (* ??? *) Qed.

Definition all_receives_RB src r v w : Prop :=
  RBLiveTLA.RBLive.all_receives src r v (world_proj1 w).

Goal forall src r f (Hnonbyz_src : is_byz src = false),
  ⌜ init ⌝ ∧ nextf f ∧ fairness ∧ disambiguation f ⊢
  ⌜ λ w, (w @ src).(stRB).(sent) r ⌝ ~~> ⌜ all_receives_RB src r (value_bft src r) ⌝.
Proof.
  intros. hnf. intros e (Hini & Hf & Hfair & Hdg).
  pose proof (exec_norm1_sound_next e f Hf) as (Hrel & Hf').
  pose proof (exec_norm1_sound_init e f Hini) as Hini'.
  set (e' := exec_norm1 f e) in Hrel, Hf', Hini'.
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

Goal forall f v,
  ⌜ init ⌝ ∧ nextf f ∧ fairness ∧ disambiguation f ⊢
  ⌜ all_honest_nodes_submitted_AC v ⌝ ~~> ⌜ all_honest_nodes_confirmed_AC v ⌝.
Proof.
  intros. hnf. intros e (Hini & Hf & Hfair & Hdg).
  pose proof (exec_norm2_sound_next e f Hf) as (Hrel & Hf').
  pose proof (exec_norm2_sound_init e f Hini) as Hini'.
  set (e' := exec_norm2 f e) in Hrel, Hf', Hini'.
  eapply exec_norm2_sound_fairness in Hfair; eauto.
  pose proof (conj Hini' (conj (ACLiveTLA.nextf_impl_next _ _ Hf') Hfair)) as HH%(ACLiveTLA.terminating_convergence_in_tla v num_byz_le_t0).
  apply ACLiveTLA.leads_to_exec_rel with (e':=exec_proj2 e) in HH; auto.
  all: apply ACN.Ns.stmap_peq_cong_implies_World_rel_cong; 
    auto using ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_submitted_stmap_peq_cong, 
      ACLiveTLA.ACLive.Terminating_Convergence.all_honest_nodes_confirmed_stmap_peq_cong.
Qed.

End RBACLiveness2.
