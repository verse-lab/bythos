From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.RB Require Export Liveness.

From Bythos.Properties Require Export Liveness_tla.

Module RBLiveness2 (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBLive := RBLiveness A R V VBFT BTh BSett.
Include LivenessTLA A M BTh BSett P RBP Ns RBAdv RBN.

Section A.

Import Global_Liveness.

Lemma global_liveness_pre_in_tla src r v :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ round_2_start src r v ⌝ ~~> ⌜ all_receives src r v ⌝.
Proof.
  delivering round_2_pkts which ends at round_2_end_suffcond is sufficient because all_receives_suffcond.
Qed.

Lemma global_liveness_in_tla src r v :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ some_receives src r v ⌝ ~~> ⌜ all_receives src r v ⌝.
Proof.
  tla_apply (leads_to_trans _ (⌜ round_2_start src r v ⌝)). tla_split.
  2: apply global_liveness_pre_in_tla.
  delivering round_1_pkts which ends at round_1_end_suffcond is sufficient because round_2_start_suffcond.
Qed.

End A.

Section A.

Import Validity.

Lemma validity_in_tla src r (Hnonbyz_src : isByz src = false) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ λ w, (w @ src).(sent) r ⌝ ~~> ⌜ all_receives src r (value_bft src r) ⌝.
Proof.
  tla_apply (leads_to_trans _ (⌜ round_2_start src r ⌝)). tla_split.
  2: tla_apply (leads_to_trans _ (⌜ Global_Liveness.round_2_start src r (value_bft src r) ⌝)); tla_split.
  3: apply global_liveness_pre_in_tla.
  - delivering round_1_pkts which ends at round_1_end_suffcond is sufficient because round_2_start_suffcond.
  - delivering round_2_pkts which ends at round_2_end_suffcond is sufficient because round_3_start_suffcond.
Qed.

End A.

End RBLiveness2.
