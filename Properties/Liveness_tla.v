From Coq Require Import List Bool Lia ssrbool ListSet Permutation PeanoNat.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts Invariant. 

(* avoid warning about coercion *)
From ABCProtocol Require TLAmore. 
Import -(coercions) TLAmore. (* need to separate Require and Import; otherwise Coqdep will complain *)

Module Type ACLiveness 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns) (ACInv : ACInvariant A T AC Ns ACN).

Import A T AC Ns ACN ACInv.

Section Preliminaries.

Definition init w := w = initWorld.

Definition next w w' := ∃ q, system_step q w w'.

Fact is_invariant_in_tla P (H : is_invariant_step P) :
  ⌜ P ⌝ ∧ □ ⟨next⟩ ⊢ □ ⌜ P ⌝.
Proof.
  apply init_invariant; auto.
  intros ?? HH (q & Hstep).
  revert HH Hstep.
  now apply H.
Qed.

Fact reachable_in_tla :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ⊢ □ ⌜ reachable ⌝.
Proof.
  apply init_invariant; autounfold with tla.
  - intros ? ->.
    constructor.
  - intros ??? (q & Hstep).
    econstructor; eauto.
Qed.

(* connecting finite trace with infinite trace *)

Lemma exec_segment e (H : e ⊨ □ ⟨ next ⟩) k o :
  ∃ l, system_trace (e k) l ∧ (e (o + k) = final_world (e k) l).
Proof.
  autounfold with tla in H.
  try unfold next in H.
  induction o as [ | o IH ].
  - now exists nil.
  - destruct IH as (l & Htrace & Ew0).
    specialize (H (o + k)).
    destruct H as (q & Hstep).
    rewrite ! drop_n in Hstep.
    simpl in Hstep.
    exists (l ++ (q, e (S (o + k))) :: nil).
    rewrite system_trace_app -final_world_app final_world_cons -Ew0 /=.
    split; auto.
Qed.

End Preliminaries.

#[export] Hint Unfold init next : tla.

Section Fairness.

Definition good_deliver_action_p p w w' :=
  if consumed p 
  then True 
  else In p (sentMsgs w) → system_step (Deliver p) w w'.

Definition fairness : predicate World :=
  (∀ p : Packet, ⌞ good_packet p ⌟ → weak_fairness (good_deliver_action_p p))%L.

#[local] Hint Unfold good_deliver_action_p fairness : tla.

(* TODO huh? *)

Fact fairness_is_always_enabled p (Hg : good_packet p) :
  ⊢ □ tla_enabled (good_deliver_action_p p).
Proof.
  unseal.
  hnf.
  destruct (consumed p).
  1: exists initWorld; auto.
  destruct Hg as (? & ?).
  eexists.
  intros HH.
  eapply DeliverStep with (p:=p); try assumption; try reflexivity.
  rewrite (surjective_pairing (procMsgWithCheck _ _ _)).
  reflexivity.
Qed.

(* certainly, we would like to check whether this is actually what we want! *)
(* semantically, what we want is ...? *)

Definition reliable_condition (e : exec World) :=
  ∀ p, good_packet p → consumed p = false → ∀ n, In p (sentMsgs (e n)) →
    ∃ k, system_step (Deliver p) (e (k + n)) (e (S (k + n))).

(* a lemma which will be used below, stating that the existence of
    an undelivered message will only be changed by an delivery action
  hope this would work for different network models ... *)
(* TODO how to force this requirement for different systems? *)

Fact consumed_is_changed_by_delivery (e : exec World) (Hrc : e ⊨ □ ⟨ next ⟩) 
  p n (E : consumed p = false) (Hin : In p (e n).(sentMsgs)) 
  k (Hnotin : ¬ In p (e (k + n)).(sentMsgs)) :
  ∃ k' : nat, k' < k ∧ system_step (Deliver p) (e (k' + n)) (e (S (k' + n))).
Proof.
  induction k as [ | k IH ]; intros; simpl in Hnotin.
  1: contradiction.
  destruct (in_dec Packet_eqdec p (sentMsgs (e (k + n)))) as [ Hin' | Hnotin' ].
  2: specialize (IH Hnotin'); destruct IH as (k' & Hlt & Hstep).
  2: exists k'; split; [ lia | assumption ].
  clear IH Hin.
  (* system-dependent proof *)
  specialize (Hrc (k + n)).
  hnf in Hrc.
  destruct Hrc as (q & Hstep).
  rewrite ! drop_n /= in Hstep.
  inversion Hstep as [
    | p0 -> _ Hnonbyz Heq 
    | n0 t -> H_n_nonbyz Heq 
    | n0 dst v ls s -> H_n_byz Heq 
    | n0 dst lc -> H_n_byz Hcc Heq
    | n0 dst c -> H_n_byz Hcc Heq ].
  3: rewrite (surjective_pairing (procInt _ _)) in Heq.
  3-6: rewrite Heq /= ?in_app_iff in Hnotin.
  3-6: now apply Decidable.not_or in Hnotin.
  - congruence.
  - destruct (procMsgWithCheck _ _ _) as (st', ms) in Heq.
    rewrite Heq in Hnotin |- *.
    simpl in Hnotin.
    rewrite in_app_iff in_remove_iff in Hnotin.
    apply Decidable.not_or in Hnotin.
    destruct Hnotin as (Hneq1 & (Hnotin1 & Hnotin2)%Decidable.not_or).
    destruct (Packet_eqdec p p0) as [ <- | Hneq2 ].
    2: intuition.
    exists k.
    split; [ constructor | assumption ].
Qed.

Fact fairness_adequate (e : exec World) (Hrc : e ⊨ ⌜ init ⌝ ∧ □ ⟨ next ⟩) :
  (e ⊨ fairness)%L ↔ reliable_condition e.
Proof.
  unfold reliable_condition.
  autounfold with tla in *.
  split; intros H.
  - intros p Hg E n Hin.
    specialize (H _ Hg n (fairness_is_always_enabled _ Hg _)).
    rewrite E in H.
    destruct H as (k & H).
    rewrite ! drop_drop ! drop_n /= in H.
    destruct (in_dec Packet_eqdec p (sentMsgs (e (k + n)))) as [ Hin' | Hnotin' ].
    1: exists k; intuition.
    apply consumed_is_changed_by_delivery in Hnotin'; auto.
    2: now hnf.
    destruct Hnotin' as (? & ? & ?).
    eauto.
  - intros p Hg k _.
    destruct (consumed p) eqn:E.
    1: now exists 0.
    specialize (H _ Hg E).
    (* have to go classic *)
    destruct (Classical_Prop.classic (∃ n : nat, In p (sentMsgs (e (n + k))))).
    + destruct H0 as (n & Hin).
      specialize (H _ Hin).
      destruct H as (k0 & Hstep).
      rewrite !Nat.add_assoc in Hstep.
      exists (k0 + n).
      now rewrite !drop_drop !drop_n /=.
    + rewrite classical.classical.not_exists in H0.
      exists 0.
      rewrite !drop_drop !drop_n /=.
      specialize (H0 0).
      now intros.
Qed.

Lemma eventual_delivery_single p (Hgood : good_packet p) :
  □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜λ w, In p (sentMsgs w)⌝ ~~> ⌜λ w, In (receive_pkt p) (sentMsgs w)⌝.
Proof.
  unfold next, fairness, good_deliver_action_p.
  evar (bb : predicate World).
  (* manual manipulation *)
  match goal with |- pred_impl (tla_and ?aa _) _ =>
    transitivity (tla_and aa bb) end.
  1: tla_split; [ tla_assumption | ].
  1: rewrite tla_and_comm; subst bb; apply impl_drop_one.
  1: etransitivity; [ apply forall_apply with (x0:=p) | ].
  1: hnf; intros e HH; specialize (HH Hgood); apply HH.
  subst bb.
  apply wf1.
  - intros w w' Hin (q & Hstep).
    (* TODO repeating? *)
    inversion Hstep; subst.
    1,3-6: left; simpl; auto.
    1: destruct (procInt _ _) in *; subst; simpl; rewrite in_app_iff; tauto.
    destruct (procMsgWithCheck _ _ _) in *.
    subst; cbn delta [sentMsgs] beta iota.
    destruct (Packet_eqdec p p0) as [ <- | Hneq ].
    + right.
      simpl; now left.
    + left.
      simpl; rewrite in_app_iff.
      right; left.
      now apply in_in_remove.
  - intros w w' Hin (q & Hstep') Hstep.
    destruct p as [ ? ? ? [] ]; simpl in Hstep.
    + eapply psent_norevert_is_invariant; eauto.
    + specialize (Hstep Hin).
      clear q Hstep'.
      inversion Hstep; try discriminate.
      injection H as <-.
      destruct (procMsgWithCheck _ _ _) in *.
      subst; cbn; now left.
  - intros.
    apply (fairness_is_always_enabled _ Hgood (fun _ => s) 0). (* trick *)
Qed.

Corollary eventual_delivery pkts (Hgood : Forall good_packet pkts) :
  □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜λ w, incl pkts (sentMsgs w)⌝ ~~> 
  ⌜λ w, ∀ p, In p pkts → In (receive_pkt p) (sentMsgs w)⌝. (* need some detour if not to write in this way *)
Proof.
  apply leads_to_combine_batch' with (valid:=good_packet); try assumption.
  - intros; now apply eventual_delivery_single.
  - intros p _.
    apply is_invariant_in_tla, psent_norevert_is_invariant.
Qed.

(* one-hop *)
Lemma leads_to_by_eventual_delivery (P Q : World → Prop)
  (H : ∀ w (Hw : reachable w),
    (* message-driven *)
    P w → ∃ pkts, Forall good_packet pkts ∧ incl pkts (sentMsgs w) ∧
      (∀ w0 l0 (Htrace : system_trace w l0) (Ew0 : w0 = final_world w l0),
        incl (map receive_pkt pkts) (sentMsgs w0) → Q w0)) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢ ⌜ P ⌝ ~~> ⌜ Q ⌝.
Proof.
  tla_pose reachable_in_tla.
  (* can only prove by unfolding? *)
  autounfold with tla; intros.
  destruct H0 as (_ & Hnext & Hfair & Hrc).
  specialize (H (e k) (Hrc _) H1).
  destruct H as (pkts & Hgood & Hincl & H).
  pose proof (eventual_delivery _ Hgood e (conj Hnext Hfair) k Hincl) as (k0 & Htmp).
  exists k0.
  hnf in Htmp.
  rewrite drop_drop drop_n /= in Htmp.
  pose proof (exec_segment e Hnext k k0) as (l & Htrace & Ew0).
  specialize (H _ _ Htrace Ew0).
  apply H.
  intros ? (p & <- & ?)%in_map_iff.
  now apply Htmp.
Qed.

End Fairness.

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
    now apply system_trace_preserve_inv.
Qed.

End ACLiveness.