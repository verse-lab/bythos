From Coq Require Import List Bool Lia ssrbool ListSet Permutation PeanoNat.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From TLA Require Export logic.

From stdpp Require list.

(* huh? *)
(* this only tells some condition will not be enabled forever, 
    but does not tell which action to take once the condition is broken *)

Definition non_stable_action {Σ : Type} (a : action Σ) := 
  forall s s', a s s' -> ~ (enabled a s').

Lemma weak_fairness_weird {Σ : Type} (a : action Σ)
  (H : non_stable_action a) :
  forall e, weak_fairness a e <-> (□ (! (□ tla_enabled a)))%L e.
Proof.
  intros.
  autounfold with tla in *.
  unfold tla_enabled.
  unseal.
  split; intros HH k; specialize (HH k).
  - intros Hcontra.
    specialize (HH Hcontra).
    destruct HH as (n0 & HH).
    apply H in HH.
    apply HH.
    change (S (n0 + k)) with ((S n0) + k).
    apply Hcontra.
  - intros.
    contradiction.
Qed.

Section TestProof.

Require Import TLA.examples.hello_liveness.

Example ab_weird : non_stable_action spec.ab.
Proof.
  unfold spec.ab.
  hnf.
  intros ????.
  hnf in H0.
  destruct H0.
  intuition congruence.
Qed.
