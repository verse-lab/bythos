From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.ABC Require Export Liveness.

From ABCProtocol.Properties Require Export Liveness_tla.

Module ACLiveness2 (A : NetAddr) (V : Signable) (VBFT : ValueBFT A V) 
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A V) (TSS : ThresholdSignatureScheme A V with Definition thres := BTh.t0).

Import A V VBFT BTh BSett P TSS.
Import ssrbool. (* anyway *)

Module Export ACLive := ACLiveness A V VBFT BTh BSett P TSS.
Include Liveness A M BTh BSett P0 PSOp ACP Ns ACAdv ACN.

(* empirical, but maybe useful? *)
Local Ltac aux Htmp :=
  match type of Htmp with
  (* the packets must be at the outmost level *)
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

Import Terminating_Convergence.

(* HMM put premises into TLA level? *)
Lemma terminating_convergence_in_tla v (H_byz_minor : num_byz ≤ t0) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ all_honest_nodes_submitted v ⌝ ~~> ⌜ all_honest_nodes_confirmed v ⌝.
Proof.
  delivering round_1_pkts which ends at round_1_end_suffcond is sufficient because all_honest_nodes_confirmed_suffcond.
Qed.

End A.

Section A.

Import Accountability.

Lemma accountability_in_tla :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ λ w, ∃ n1 : Address, ∃ n2 : Address, confirmed_different_values n1 n2 w ⌝ ~~> ⌜ accountability ⌝.
Proof.
  (* intro first *)
  let tac n := rewrite <- exist_state_pred; apply leads_to_exist_intro; intros n in tac n1; tac n2.
  tla_apply (leads_to_trans _ (⌜ round_2_start n1 n2 ⌝)). tla_split.
  - delivering round_1_pkts which ends at round_1_end_suffcond is sufficient because round_2_start_suffcond.
  - delivering round_2_pkts which ends at round_2_end_suffcond is sufficient because accountability_suffcond.
Qed.

End A.

End ACLiveness2.
