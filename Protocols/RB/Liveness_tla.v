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

(* empirical, but maybe useful? *)
Local Ltac aux Htmp :=
  match type of Htmp with
  | (exists (_ : list ?t), _) =>
    tryif convert t Packet
    then 
      let pkts := fresh "pkts" in
      let Htmp0 := fresh "Htmp" in
      destruct Htmp as (pkts & Htmp); pose proof Htmp as Htmp0; hnf in Htmp0; destruct_and? Htmp0;
      exists pkts; split_and?; eauto
    else
      let Htmp0 := fresh "Htmp" in
      destruct Htmp as (? & Htmp0); aux Htmp0
  | _ => fail 2
  end.

Tactic Notation "delivering" constr(lemma1) "which" "ends" "at" constr(lemma2)
    "is" "sufficient" "because" constr(lemma3) :=
  let Htmp := fresh "Htmp" in
  apply leads_to_by_eventual_delivery;
  intros; pose proof lemma1 as Htmp; saturate_assumptions!;
  aux Htmp; 
  intros; simplify_eq; eapply lemma3; eauto; try (eapply lemma2; eauto).

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

Import Validity1.

Lemma validity_in_tla src r (Hnonbyz_src : is_byz src = false) :
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
