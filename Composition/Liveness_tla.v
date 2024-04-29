From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses. 
(* From Coq Require Import ClassicalChoice. *)
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Properties Require Export Liveness_tla.
From Bythos.Composition Require Export Network.

Module CompLiveness2 (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh)
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  (Ns1 : NetState A M1 Pk1 BTh Pt1) (Ns2 : NetState A M2 Pk2 BTh Pt2)
  (BSett : ByzSetting A)
  (* TODO is using the Adv of each sub-protocol really good? *)
  (Adv1 : Adversary A M1 BTh BSett Pk1 Pt1 Ns1) (Adv2 : Adversary A M2 BTh BSett Pk2 Pt2 Ns2)
  (* TODO this is bad! *)
  (PSOp1 : PacketSoupOperations Pk1) (PSOp2 : PacketSoupOperations Pk2)
  (N1 : Network.Network A M1 BTh BSett Pk1 PSOp1 Pt1 Ns1 Adv1)
  (N2 : Network.Network A M2 BTh BSett Pk2 PSOp2 Pt2 Ns2 Adv2).

Module Export CN := CompNetwork A M1 M2 BTh Pk1 Pk2 Pt1 Pt2 SCPT Ns1 Ns2 BSett Adv1 Adv2 PSOp1 PSOp2 N1 N2.

Include LivenessTLA A CM BTh BSett CPk CPSOp CPt CNs CAdv CN.

Definition exec_proj1 (e : exec World) : exec Ns1.World := fun n => world_proj1 (e n).

Definition exec_proj2 (e : exec World) : exec Ns2.World := fun n => world_proj2 (e n).

Definition ssdexec_proj1 (f : exec system_step_descriptor) : exec N1.system_step_descriptor :=
  fun n => (ssd_proj1 (f n)).

Definition ssdexec_proj2 (f : exec system_step_descriptor) (e : exec World) : exec N2.system_step_descriptor :=
  fun n => (ssd_proj2 (f n) (world_proj1 (e n)) (world_proj1 (e (S n)))).

Definition exec_norm1 f (e : exec World) : exec Ns1.World :=
  N1.final_world_n (ssdexec_proj1 f) (world_proj1 (e 0)).

Definition exec_norm2 f (e : exec World) : exec Ns2.World :=
  N2.final_world_n (ssdexec_proj2 f e) (world_proj2 (e 0)).

Fact exec_norm1_0 e f : exec_norm1 f e 0 = exec_proj1 e 0.
Proof eq_refl.

Fact exec_norm2_0 e f : exec_norm2 f e 0 = exec_proj2 e 0.
Proof eq_refl.

Fact leads_to_inl e P Q (H : exec_proj1 e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) :
  e ⊨ ⌜ λ w, P (world_proj1 w) ⌝ ~~> ⌜ λ w, Q (world_proj1 w) ⌝.
Proof. revert H. unseal. (* ??? *) Qed.

Fact leads_to_inr e P Q (H : exec_proj2 e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) :
  e ⊨ ⌜ λ w, P (world_proj2 w) ⌝ ~~> ⌜ λ w, Q (world_proj2 w) ⌝.
Proof. revert H. unseal. (* ??? *) Qed.

(* TODO have no way to go ... this might be too strong, but I have no better idea
    on how to avoid ambiguity. *)
(* this may not always hold, but can be achieved at the level of network semantics
    (by requiring all resulting worlds to be normalized) *)
(* NOTE: this is stronger than what is actually needed, which is something like next_proj1 *)
Definition disambiguation f (e : exec World) : Prop :=
  forall q n, system_step q (e n) (e (S n)) → f n = q.

(* FIXME: expedient; later change TLA to module type? *)
Module _LiveTLA1 := LivenessTLA A M1 BTh BSett Pk1 PSOp1 Pt1 Ns1 Adv1 N1.
Module _LiveTLA2 := LivenessTLA A M2 BTh BSett Pk2 PSOp2 Pt2 Ns2 Adv2 N2.

Corollary exec_proj1_sound_init e (H : e ⊨ ⌜ init ⌝) : (exec_proj1 e ⊨ ⌜ _LiveTLA1.init ⌝).
Proof. hnf in H |- *. unfold exec_proj1. rewrite H. reflexivity. Qed.

Corollary exec_norm1_sound_init e f (H : e ⊨ ⌜ init ⌝) : (exec_norm1 f e ⊨ ⌜ _LiveTLA1.init ⌝).
Proof. hnf. rewrite exec_norm1_0. now apply exec_proj1_sound_init. Qed.

Fact exec_norm1_sound_next (Hbyz_rel : forall m, Ns1.World_rel_cong (Adv1.byz_constraints m)) (e : exec World) f (Hf : e ⊨ nextf f) :
  let: e' := exec_norm1 f e in
    _LiveTLA1.exec_rel e' (exec_proj1 e) ∧
    (* (e' ⊨ □ ⟨ _LiveTLA1.next ⟩). *)
    (e' ⊨ _LiveTLA1.nextf (ssdexec_proj1 f)).
Proof.
  (*
  autounfold with tla in H. setoid_rewrite drop_n in H. simpl in H.
  pose proof (choice _ H) as (f & Hf). clear H.   (* !!!!!!!! *)
  *)
  autounfold with tla in Hf. hnf in Hf. apply and_wlog_r.
  - hnf. intros n. unfold exec_proj1, exec_norm1.
    induction n as [ | n IH ]; try reflexivity.
    rewrite N1.final_world_n_add_1.
    pose proof (ssd_proj1_sound (Hf n)) as (_ & H).
    rewrite -H. now apply N1.next_world_preserves_World_rel.
  - intros Hrel.
    split_and?; autounfold with tla.
    + intros k. (* exists (ssd_proj1 (f k)). rewrite !drop_n /=. *)
      pose proof (ssd_proj1_sound (Hf k)) as (Ha & Hb).
      unfold exec_norm1 in *. rewrite N1.final_world_n_add_1. eapply N1.step_mirrors_World_rel.
      1: symmetry; apply Hrel. 1: apply Ha. 1: assumption.
      specialize (Hrel (S k)). rewrite N1.final_world_n_add_1 in Hrel. rewrite Hb Hrel. reflexivity.
    (* + intros k. hnf. intros q w w' Hstep. rewrite !drop_n /=.
      pose proof (ssd_proj1_sound _ _ _ Hstep) as (Ha & Hb).
      subst e'. rewrite N1.final_world_n_add_1. eapply N1.step_mirrors_World_rel. *)
Qed.

Fact exec_norm1_sound_fairness (e : exec World) f (H : e ⊨ nextf f) (Hdg : disambiguation f e)
  (e' : exec Ns1.World) (Hrel : _LiveTLA1.exec_rel e' (exec_proj1 e))
  (* (H' : e' ⊨ □ ⟨ _LiveTLA1.next ⟩) : *)
  (H' : e' ⊨ _LiveTLA1.nextf (ssdexec_proj1 f)) :
  (e ⊨ fairness) → (e' ⊨ _LiveTLA1.fairness).
Proof.
  (* change view, get k *)
  intros Hfair%fairness_adequate; auto. 2: eapply nextf_impl_next, H. 
  apply _LiveTLA1.fairness_adequate; auto. 1: eapply _LiveTLA1.nextf_impl_next, H'. 
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

(* TODO basically repeating the proofs above ... this is too bad *)
Corollary exec_proj2_sound_init e (H : e ⊨ ⌜ init ⌝) : (exec_proj2 e ⊨ ⌜ _LiveTLA2.init ⌝).
Proof. hnf in H |- *. unfold exec_proj2. rewrite H. reflexivity. Qed.

Corollary exec_norm2_sound_init e f (H : e ⊨ ⌜ init ⌝) : (exec_norm2 f e ⊨ ⌜ _LiveTLA2.init ⌝).
Proof. hnf. rewrite exec_norm2_0. now apply exec_proj2_sound_init. Qed.

Fact exec_norm2_sound_next (Hbyz_rel : forall m, Ns2.World_rel_cong (Adv2.byz_constraints m)) (e : exec World) f (Hf : e ⊨ nextf f) :
  let: e' := exec_norm2 f e in
    _LiveTLA2.exec_rel e' (exec_proj2 e) ∧
    (e' ⊨ _LiveTLA2.nextf (ssdexec_proj2 f e)).
Proof.
  autounfold with tla in Hf. hnf in Hf. apply and_wlog_r.
  - hnf. intros n. unfold exec_proj2, exec_norm2.
    induction n as [ | n IH ]; try reflexivity.
    rewrite N2.final_world_n_add_1.
    pose proof (ssd_proj2_sound (Hf n)) as (_ & H).
    rewrite -H. pose proof (Hf n) as EE%next_world_sound. rewrite -!EE. now apply N2.next_world_preserves_World_rel.
  - intros Hrel.
    split_and?; autounfold with tla.
    + intros k. (* exists (ssd_proj1 (f k)). rewrite !drop_n /=. *)
      pose proof (ssd_proj2_sound (Hf k)) as (Ha & Hb).
      pose proof (Hf k) as EE%next_world_sound. rewrite -EE in Ha Hb. 
      unfold exec_norm2 in *. rewrite N2.final_world_n_add_1. eapply N2.step_mirrors_World_rel.
      1: symmetry; apply Hrel. 1: apply Ha. 1: assumption.
      specialize (Hrel (S k)). rewrite N2.final_world_n_add_1 in Hrel. rewrite Hb Hrel. reflexivity. 
Qed.

Fact exec_norm2_sound_fairness (e : exec World) f (H : e ⊨ nextf f) (Hdg : disambiguation f e)
  (e' : exec Ns2.World) (Hrel : _LiveTLA2.exec_rel e' (exec_proj2 e))
  (H' : e' ⊨ _LiveTLA2.nextf (ssdexec_proj2 f e)) :
  (e ⊨ fairness) → (e' ⊨ _LiveTLA2.fairness).
Proof.
  (* change view, get k *)
  intros Hfair%fairness_adequate; auto. 2: eapply nextf_impl_next, H. 
  apply _LiveTLA2.fairness_adequate; auto. 1: eapply _LiveTLA2.nextf_impl_next, H'. 
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

End CompLiveness2.
