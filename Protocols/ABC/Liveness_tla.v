From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.ABC Require Export Liveness.

From ABCProtocol.Properties Require Export Liveness_tla.

Module ACLiveness2 (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0).

Import A V (* VBFT *) BTh BSett P TSS.
Import ssrbool. (* anyway *)

Module Export ACLive := ACLiveness A Sn V (* VBFT *) BTh BSett P TSS0 TSS.
Include LivenessTLA A M BTh BSett P0 PSOp ACP Ns ACAdv ACN.

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
  - (* TODO automation broken ... but not quite want to fix now *) 
    apply leads_to_by_eventual_delivery.
    intros. pose proof round_2_pkts as Htmp. saturate_assumptions!.
    destruct Htmp as (pkts & Htmp). hnf in Htmp. exists pkts.
    destruct (w @ n1).(submitted_value) eqn:E1, (w @ n2).(submitted_value) eqn:E2; try contradiction. 
    hnf in Htmp. destruct_and? Htmp.
    split_and?; auto. intros. simplify_eq. eapply accountability_suffcond; eauto; eapply round_2_end_suffcond; hnf; eauto.
    rewrite E1 E2. now hnf.
Qed.

End A.

End ACLiveness2.
