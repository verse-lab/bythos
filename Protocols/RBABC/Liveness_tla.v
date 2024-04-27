From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses ClassicalChoice.
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

Module RBLiveTLA := RBLiveness2 A R V VBFT BTh BSett.
Module ACLiveTLA := ACLiveness2 A Sn V BTh BSett P TSS0 TSS.

Import RBLiveTLA.RBLive.RBS.RBInv ACLiveTLA.ACLive.ACS.ACInv.

Module Export RBACN := RBACNetwork A R ARP Sn V VBFT BTh BSett P TSS0 TSS RBN ACN.

Include LivenessTLA A M BTh BSett Pk PSOp RBACP Ns RBACAdv RBACN.

Definition exec_proj1 (e : exec World) : exec RBN.Ns.World := fun n => world_proj1 (e n).

Definition exec_proj2 (e : exec World) : exec ACN.Ns.World := fun n => world_proj2 (e n).
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
Fact exec_proj1_sound (e : exec World) (H : e ⊨ □ ⟨ next ⟩) :
  ∃ (e' : exec RBN.Ns.World), 
    RBLiveTLA.exec_rel e' (exec_proj1 e) ∧
    (e' ⊨ □ ⟨ RBLiveTLA.next ⟩).
    (* (e' ⊨ □ ⟨ next_proj1 ⟩). *)
Proof.
  autounfold with tla in H. setoid_rewrite drop_n in H. simpl in H.
  pose proof (choice _ H) as (f & Hf). clear H.   (* !!!!!!!! *)
  pose (e' := RBN.final_world_n (fun n => (ssd_proj1 (f n))) (world_proj1 (e 0))).
  exists e'. apply and_wlog_r.
  - hnf. intros n. unfold exec_proj1. subst e'.
    induction n as [ | n IH ]; try reflexivity.
    rewrite RBN.final_world_n_add_1.
    pose proof (ssd_proj1_sound _ _ _ (Hf n)) as (_ & H).
    rewrite -H. now apply RBN.next_world_preserves_World_rel.
  - intros Hrel.
    split_and?; autounfold with tla.
    + intros k. exists (ssd_proj1 (f k)). rewrite !drop_n /=. 
      pose proof (ssd_proj1_sound _ _ _ (Hf k)) as (Ha & Hb).
      subst e'. rewrite RBN.final_world_n_add_1. eapply RBN.step_mirrors_World_rel.
      1: symmetry; apply Hrel. 1: apply Ha. 1: intros; auto. (* nice *)
      specialize (Hrel (S k)). rewrite RBN.final_world_n_add_1 in Hrel. rewrite Hb Hrel. reflexivity.
    (* + intros k. hnf. intros q w w' Hstep. rewrite !drop_n /=.
      pose proof (ssd_proj1_sound _ _ _ Hstep) as (Ha & Hb).
      subst e'. rewrite RBN.final_world_n_add_1. eapply RBN.step_mirrors_World_rel. *)
Qed.

Fact exec_proj1_sound_fairness (e : exec World) (H : e ⊨ □ ⟨ next ⟩)
  (e' : exec RBN.Ns.World) (Hrel : RBLiveTLA.exec_rel e' (exec_proj1 e))
  (H' : e' ⊨ □ ⟨ RBLiveTLA.next ⟩) :
  (e ⊨ fairness) → (e' ⊨ RBLiveTLA.fairness).
Proof.
  (* change view *)
  intros Hfair%fairness_adequate; auto. apply RBLiveTLA.fairness_adequate; auto.
  hnf in Hfair |- *. intros [ src dst msg ? ] (Hs & Hd). simpl in *. intros -> n Hin.
  specialize (Hfair (mkP src dst (inl msg) false) (conj Hs Hd) eq_refl n).
  apply (proj2 (Hrel n)) in Hin. unfold exec_proj1, world_proj1 in Hin. simpl in Hin.
  apply option_map_list_In in Hin. destruct Hin as ([ ? ? [] ? ] & Hin & Hpj); try discriminate.
  cbn in Hpj. revert Hpj. intros [= -> -> -> ->]. specialize (Hfair Hin).
  destruct Hfair as (k & Hstep). 
Abort.

End RBACLiveness2.
