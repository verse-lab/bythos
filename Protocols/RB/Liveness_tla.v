From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.RB Require Export Liveness.

From ABCProtocol.Properties Require Export Liveness_tla.

Module RBLiveness2 (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBLive := RBLiveness A R V VBFT BTh BSett.
Include Liveness A M BTh BSett P PSOp RBP Ns RBAdv RBN.

Lemma global_liveness_in_tla src r v :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ some_receives src r v ⌝ ~~> ⌜ all_receives src r v ⌝.
Proof.
  tla_apply (leads_to_trans _ (⌜ round_2_start src r v ⌝)).
  tla_split.
  - apply leads_to_by_eventual_delivery.
    intros w H_w_reachable H. pose proof (round_1_pkts H_w_reachable H) as (nonbyz_senders & pkts & Hround1).
    hnf in Hround1. pose proof Hround1 as HH. destruct_and? Hround1.
    exists pkts. split_and?; auto. 
    intros w0 l0 Htrace0 -> Hincl.
    eapply round_2_start_suffcond; eauto.
    eapply round_1_end_suffcond; eauto. 
  - apply leads_to_by_eventual_delivery.
    intros w H_w_reachable H. pose proof (round_2_pkts H_w_reachable H) as (pkts & Hround2).
    hnf in Hround2. pose proof Hround2 as HH. destruct_and? Hround2.
    exists pkts. split_and?; auto. 
    intros w0 l0 Htrace0 -> Hincl.
    eapply all_receives_suffcond; eauto.
    eapply round_2_end_suffcond; eauto.
Qed.

End RBLiveness2.

