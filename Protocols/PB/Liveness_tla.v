From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.PB Require Export Liveness.

From ABCProtocol.Properties Require Export Liveness_tla.

Module PBLiveness2 (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS).

Import A R V Pf VBFT BTh BSett TSS PBDT.
Import ssrbool. (* anyway *)

Module Export PBLive := PBLiveness A R Sn V Pf VBFT BTh BSett TSS0 TSS PBDT.
Include Liveness A M BTh BSett P0 PSOp PBP Ns PBAdv PBN.

Section A.

  Import Termination.

  Variables (src : Address) (r : Round).
  Hypothesis (Hnonbyz_src : is_byz src = false) (Hex : ex_validate r (value_bft src r).1 (value_bft src r).2).

  Lemma termination_1_in_tla :
    ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
    ⌜ λ w, (w @ src).(sent) r ⌝ ~~> ⌜ all_echoes src r ⌝.
  Proof using Hex Hnonbyz_src r src.
    delivering round_1_pkts which ends at round_1_end_suffcond is sufficient because round_2_start_suffcond.
  Qed.

  Lemma termination_2_in_tla :
    ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
    ⌜ all_echoes src r ⌝ ~~> ⌜ λ w, (w @ src).(output) r ⌝.
  Proof using Hex Hnonbyz_src r src.
    delivering round_2_pkts which ends at round_2_end_suffcond is sufficient because src_outputs_suffcond.
  Qed.

  Lemma termination_in_tla :
    ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
    ⌜ λ w, (w @ src).(sent) r ⌝ ~~> ⌜ λ w, (w @ src).(output) r ⌝.
  Proof using Hex Hnonbyz_src r src.
    tla_apply (leads_to_trans _ (⌜ all_echoes src r ⌝)). tla_split.
    - apply termination_1_in_tla.
    - apply termination_2_in_tla.
  Qed.

End A.

End PBLiveness2.
