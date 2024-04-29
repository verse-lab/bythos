From Coq Require Import List Bool Lia ListSet Permutation PeanoNat.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.ABC.OldProofs Require Export Invariant.
From Bythos.Properties Require Export Liveness_tla.

Module ACLiveness (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A Sn V) 
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0).

Import A V VBFT BTh BSett P TSS.

Module Export ACInv := ACInvariant A Sn V VBFT BTh BSett P TSS0 TSS.
Include LivenessTLA A M BTh BSett P0 PSOp ACP Ns ACAdv ACN.

(* now, really nice things *)

Lemma terminating_convergence_in_tla v (H_byz_minor : num_byz ≤ t0) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ all_honest_nodes_submitted v ⌝ ~~> ⌜ all_honest_nodes_confirmed ⌝.
Proof.
  apply leads_to_by_eventual_delivery.
  intros.
  pose proof (honest_submit_all_received_suffcond _ _ Hw H) as Hsuffcond.
  destruct (submit_msgs_all_sent w v Hw H) as (pkts & Hincl & Hgood & Htmp).
  simpl in Hsuffcond; clear Htmp.
  exists pkts.
  split_and ?; try assumption.
  intros.
  eapply terminating_convergence; try eassumption; eauto.
Qed.

Lemma eventually_accountability_in_tla :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ λ w, ∃ n1 : Address, ∃ n2 : Address, confirmed_different_values n1 n2 w ⌝ ~~> ⌜ accountability ⌝.
Proof.
  (* intro first *)
  let tac n := rewrite <- exist_state_pred; apply leads_to_exist_intro; intros n in tac n1; tac n2.
  tla_apply (leads_to_trans _ 
    (⌜ λ w, confirmed_different_values' n1 n2 w ∧ mutual_lightcert_conflict_detected n1 n2 w ⌝)).
  tla_split.
  - apply leads_to_by_eventual_delivery.
    intros.
    pose proof (mutual_lightcerts_sent _ _ _ Hw H) as (b1 & b2 & b3 & b4 & Hsuffcond).
    exists (mutual_lightcerts w n1 n2 b1 b2 b3 b4).
    change (map receive_pkt _) with (mutual_lightcerts w n1 n2 true true true true).
    split_and ?; try assumption.
    1: unfold confirmed_different_values, confirmed in H.
    1: unfold mutual_lightcerts; repeat (constructor; try tauto).
    intros.
    (* !! *)
    pose proof (reachable_inv _ Hw) as Hinv.
    split.
    + pose proof (proj2 (is_invariant_step_trace _) (confirmed_different_values'_is_invariant n1 n2) w l0) as HH.
      rewrite <- Ew0 in HH.
      apply HH; try assumption.
      split; try assumption.
      now apply confirmed_different_values_strengthen.
    + eapply eventually_mutual_lightcert_conflict_detected; try eassumption; eauto.
  - apply leads_to_by_eventual_delivery.
    intros.
    pose proof (reachable_inv _ Hw) as Hinv.
    destruct H as (Hfundamental%confirmed_different_values_strengthen & H); try assumption.
    pose proof (fullcerts_all_received_suffcond _ _ _ Hw Hfundamental H) as Hsuffcond.
    destruct (fullcerts_all_sent _ _ _ Hw Hfundamental) as (pkts & Hincl & Hgood & Htmp).
    simpl in Hsuffcond; clear Htmp.
    exists pkts.
    split_and ?; try assumption.
    intros.
    eapply eventually_accountability; try eassumption; eauto.
    apply Hsuffcond; auto.
    rewrite Ew0.
    apply <- (is_invariant_step_trace); auto using inv_step.
Qed.

End ACLiveness.
