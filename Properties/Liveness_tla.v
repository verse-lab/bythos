From Coq Require Import List Bool Lia ListSet Permutation PeanoNat RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.

From Bythos.Utils Require Export TLAmore. 
(* used this to suppress warning about coercion, but now anyway *)
(* this would require some time ... *)
(* Export -(coercions) TLAmore. (* need to separate Require and Import; otherwise Coqdep will complain *) *)

Module LivenessTLA (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr) 
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P Pr Ns Adv).

Section Preliminaries.

Definition exec_rel (e e' : exec SystemState) : Prop := ∀ n, SystemState_rel (e n) (e' n).

Definition init w := w = initSystemState.

Definition next w w' := ∃ q, system_step q w w'.

(* "next" hides the underlying sequence of system step tags.
    although they can be recovered using choice-like axioms, we may not do that *)

Definition nextf (f : exec system_step_tag) : predicate SystemState :=
  fun e => ∀ n, system_step (f n) (e n) (e (S n)).

Fact nextf_impl_next f : (nextf f ⊢ □ ⟨next⟩).
Proof. unseal. hnf. eexists. apply H. Qed.

Fact is_invariant_in_tla [P] (H : is_invariant_step P) :
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

Lemma exec_segment [e] (H : e ⊨ □ ⟨ next ⟩) k o :
  ∃ l, system_trace (e k) l ∧ (e (o + k) = final_sysstate (e k) l).
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
    rewrite system_trace_snoc final_sysstate_snoc -Ew0 //=.
Qed.

End Preliminaries.

Global Hint Unfold init next : tla.

Global Instance Equivalence_exec_rel : Equivalence exec_rel.
Proof.
  constructor; hnf; intros; hnf in *; intros; try reflexivity; try now symmetry; try now transitivity (y n).
Qed.

Section Fairness.

(* FIXME: do we really need to make this action into an implication? *)
Definition WFPkt p w w' :=
  if received p 
  then True 
  else In p (packetSoup w) → system_step (Delivery p) w w'.

Definition WFDelivery : predicate SystemState :=
  (∀ p : Packet, ⌞ goodPkt p ⌟ → weak_fairness (WFPkt p))%L.

#[local] Hint Unfold WFPkt WFDelivery : tla.

(* like in IronFleet, always-enabled action would simplify the proof *)

Fact WFPkt_is_always_enabled [p] (Hg : goodPkt p) :
  ⊢ □ tla_enabled (WFPkt p).
Proof.
  unseal.
  hnf.
  destruct (received p); eauto.
  destruct Hg as (? & ?).
  eexists.
  intros HH.
  eapply DeliveryStep with (p:=p); try assumption; try reflexivity.
  rewrite (surjective_pairing (procMsg _ _ _)).
  reflexivity.
Qed.

(*
Fact received_is_changed_by_delivery_pre :
  ∀ p, goodPkt p → received p = false → ∀ w w', In p (packetSoup w) →
    w' = next_sysstate (Delivery p) w → system_step (Delivery p) w w'.
Proof.
  intros. hnf in * |-. subst w'. eapply DeliveryStep; try solve [ reflexivity | assumption | tauto ].
  simpl. rewrite (surjective_pairing (procMsg _ _ _)). reflexivity.
Qed.
*)
Definition eventualDelivery (e : exec SystemState) :=
  ∀ p, goodPkt p → received p = false → ∀ n, In p (packetSoup (e n)) →
    ∃ k, system_step (Delivery p) (e (k + n)) (e (S (k + n))).

(*
Definition eventualDelivery_ (e : exec SystemState) :=
  ∀ p, goodPkt p → received p = false → ∀ n, In p (packetSoup (e n)) →
    ∃ k, e (S (k + n)) = next_sysstate (Delivery p) (e (k + n)).
*)
(* a lemma which will be used below, stating that the existence of
    an undelivered message will only be changed by an delivery action
  hope this would work for different network models ... *)

Fact received_is_changed_by_delivery [e : exec SystemState] (Hrc : e ⊨ □ ⟨ next ⟩) 
  [p n] (E : received p = false) (Hin : In p (e n).(packetSoup)) 
  k (Hnotin : ¬ In p (e (k + n)).(packetSoup)) :
  ∃ k' : nat, k' < k ∧ system_step (Delivery p) (e (k' + n)) (e (S (k' + n))).
Proof.
  induction k as [ | k IH ]; intros; simpl in Hnotin.
  1: contradiction.
  destruct (in_dec Packet_eqdec p (packetSoup (e (k + n)))) as [ Hin' | Hnotin' ].
  2: specialize (IH Hnotin'); destruct IH as (k' & Hlt & Hstep).
  2: exists k'; split; [ lia | assumption ].
  clear IH Hin.
  (* system-independent proof *)
  specialize (Hrc (k + n)).
  hnf in Hrc.
  destruct Hrc as (q & Hstep).
  rewrite ! drop_n /= in Hstep.
  inversion Hstep as [
    | p0 -> _ Hnonbyz Heq 
    | n0 t -> H_n_nonbyz Heq 
    | n0 dst m -> H_n_byz Hc Heq ].
  3: rewrite (surjective_pairing (procInt _ _)) in Heq.
  3-4: rewrite Heq /= ?In_sendout ?In_sendout1 in Hnotin.
  3-4: now apply Decidable.not_or in Hnotin.
  - now rewrite H0 in Hin'.
  - destruct (procMsg _ _ _) as (st', ms) in Heq.
    rewrite Heq in Hnotin |- *.
    simpl in Hnotin.
    rewrite In_sendout In_consume in Hnotin.
    apply Decidable.not_or in Hnotin.
    destruct Hnotin as (Hneq1 & (Hnotin1 & Hnotin2)%Decidable.not_or).
    destruct (Packet_eqdec p p0) as [ <- | Hneq2 ].
    2: intuition.
    exists k.
    split; [ constructor | assumption ].
Qed.

(* what if things go too strong *)
(*
Fact fairness_strictly_stronger [e : exec SystemState] (Hrc : e ⊨ □ ⟨ next ⟩) :
  (e ⊨ (∀ p : Packet, ⌞ goodPkt p ⌟ → weak_fairness (system_step (Delivery p)))%L)%L ↔ eventualDelivery e.
Proof.
  unfold eventualDelivery.
  autounfold with tla in *.
  split; intros H.
  - intros p Hg E n Hin.
    specialize (H _ Hg n).
    destruct (Classical_Prop.classic (∀ k : nat, tla_enabled (system_step (Delivery p)) (drop k (drop n e)))).
    + specialize (H H0).
      destruct H as (k & H).
      rewrite ! drop_drop ! drop_n /= in H.
      eauto.
    + rewrite classical.classical.not_forall /tla_enabled/enabled/state_pred in H0.
      destruct H0 as (k & H0).
      rewrite drop_drop drop_n /= in H0.
      assert (¬ In p (e (k + n)).(packetSoup)) as Htmp.
      { intros Htmp. apply H0. eexists. eapply DeliveryStep; try reflexivity; try auto. 1: hnf in *; tauto. 
        rewrite (surjective_pairing (procMsg _ _ _)). reflexivity. }
      apply received_is_changed_by_delivery in Htmp; auto.
      destruct Htmp as (? & ? & ?).
      eauto.
  - intros p Hg k ?.
    (* boom here, since a received packet is not guaranteed to be delivered again *)
Abort.
*)

Fact WFDelivery_adequate [e : exec SystemState] (Hrc : e ⊨ □ ⟨ next ⟩) :
  (e ⊨ WFDelivery)%L ↔ eventualDelivery e.
Proof.
  unfold eventualDelivery.
  autounfold with tla in *.
  split; intros H.
  - intros p Hg E n Hin.
    specialize (H _ Hg n (WFPkt_is_always_enabled Hg _)).
    rewrite E in H.
    destruct H as (k & H).
    rewrite ! drop_drop ! drop_n /= in H.
    destruct (in_dec Packet_eqdec p (packetSoup (e (k + n)))) as [ Hin' | Hnotin' ].
    1: exists k; intuition.
    apply received_is_changed_by_delivery in Hnotin'; auto.
    destruct Hnotin' as (? & ? & ?).
    eauto.
  - intros p Hg k _.
    destruct (received p) eqn:E.
    1: now exists 0.
    specialize (H _ Hg E).
    (* here, we cannot directly construct the existence, 
      so we have to go classic (i.e., prove by contradiction) *)
    destruct (Classical_Prop.classic (∃ n : nat, In p (packetSoup (e (n + k))))) as [ (n & Hin) | H0 ].
    + specialize (H _ Hin).
      destruct H as (k0 & Hstep).
      rewrite !Nat.add_assoc in Hstep.
      exists (k0 + n).
      now rewrite !drop_drop !drop_n /=.
    + assert (∀ n : nat, ¬ In p (e (n + k)).(packetSoup)) as H0'.
      { intros n Hcontra.
        apply H0; eauto.
      }
      exists 0.
      rewrite !drop_drop !drop_n /=.
      specialize (H0' 0).
      now intros.
Qed.

Lemma eventual_delivery_single [p] (Hgood : goodPkt p) :
  □ ⟨ next ⟩ ∧ WFDelivery ⊢
  ⌜λ w, In p (packetSoup w)⌝ ~~> ⌜λ w, In (markRcv p) (packetSoup w)⌝.
Proof.
  destruct p as [ ? ? ? [] ]; simpl markRcv.
  1: simpl; apply impl_drop_hyp, leads_to_refl.
  (* exploit the equivalence above to achieve simpler proof! *)
  autounfold with tla.
  intros e (Hnext & Hfair) k Hin.
  rewrite drop_n /= in Hin.
  apply WFDelivery_adequate in Hfair; try assumption.
  apply Hfair in Hin; auto.
  destruct Hin as (k0 & (_ & _ & (? & ? & _ & E))%DeliverStep_inv).
  exists (S k0).
  rewrite drop_drop drop_n /= E /= In_sendout In_consume /=.
  tauto.
  (* NOTE: another proof is based on WF1, which is longer *)
  (*
  unfold next, WFDelivery, WFPkt.
  evar (bb : predicate SystemState).
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
    inversion Hstep; subst.
    1,3-4: left; simpl; auto.
    1: destruct (procInt _ _) in *; subst; simpl; rewrite In_sendout; tauto.
    1: rewrite In_sendout1; tauto.
    destruct (procMsg _ _ _) in *.
    subst; simpl.
    rewrite ?In_sendout ?In_consume.
    destruct (Packet_eqdec p p0) as [ <- | Hneq ]; intuition.
  - intros w w' Hin (q & Hstep') Hstep.
    destruct p as [ ? ? ? [] ]; simpl in Hstep.
    + eapply psent_norevert_is_invariant; eauto.
    + specialize (Hstep Hin).
      clear q Hstep'.
      inversion Hstep; try discriminate.
      injection H as <-.
      destruct (procMsg _ _ _) in *.
      subst; simpl.
      rewrite ?In_sendout ?In_consume /=.
      tauto.
  - intros.
    apply (WFPkt_is_always_enabled _ Hgood (fun _ => s) 0). (* trick *)
  *)
Qed.

Corollary eventual_delivery [pkts] (Hgood : Forall goodPkt pkts) :
  □ ⟨ next ⟩ ∧ WFDelivery ⊢
  ⌜λ w, incl pkts (packetSoup w)⌝ ~~> 
  ⌜λ w, ∀ p, In p pkts → In (markRcv p) (packetSoup w)⌝. (* need some detour if not to write in this way *)
Proof.
  apply leads_to_combine_batch' with (valid:=goodPkt); try assumption.
  - intros; now apply eventual_delivery_single.
  - intros p _.
    apply is_invariant_in_tla, psent_norevert_is_invariant.
Qed.

(* one-hop *)
Lemma leads_to_by_eventual_delivery (P Q : SystemState → Prop)
  (H : ∀ w (Hw : reachable w),
    (* message-driven *)
    P w → ∃ pkts, Forall goodPkt pkts ∧ incl pkts (packetSoup w) ∧
      (∀ w0 l0 (Htrace : system_trace w l0) (Ew0 : w0 = final_sysstate w l0),
        incl (map markRcv pkts) (packetSoup w0) → Q w0)) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ WFDelivery ⊢ ⌜ P ⌝ ~~> ⌜ Q ⌝.
Proof.
  tla_pose reachable_in_tla.
  (* can only prove by unfolding? *)
  autounfold with tla; intros.
  destruct H0 as (_ & Hnext & Hfair & Hrc).
  specialize (H (e k) (Hrc _) H1).
  destruct H as (pkts & Hgood & Hincl & H).
  pose proof (eventual_delivery Hgood e (conj Hnext Hfair) k Hincl) as (k0 & Htmp).
  exists k0.
  hnf in Htmp.
  rewrite drop_drop drop_n /= in Htmp.
  pose proof (exec_segment Hnext k k0) as (l & Htrace & Ew0).
  specialize (H _ _ Htrace Ew0).
  apply H.
  intros ? (p & <- & ?)%in_map_iff.
  now apply Htmp.
Qed.

End Fairness.

(* relational *)
Lemma leads_to_exec_rel [e e' : exec SystemState] (H : exec_rel e e')
  (P Q : SystemState → Prop) (HP : SystemState_rel_cong P) (HQ : SystemState_rel_cong Q) :
  (e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) → (e' ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝).
Proof.
  unseal. symmetry in H. pose proof (HP _ _ (H k)) as Htmp. saturate_assumptions!.
  destruct H0 as (k0 & H0). exists k0. eapply HQ. 2: apply H0. symmetry. apply H.
Qed.

(* empirical, but maybe useful? *)
Local Ltac aux Htmp :=
  match type of Htmp with
  | (exists (_ : list ?t), _) =>
    tryif assert_succeeds (pose (eq_refl : eq t Packet))
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

Global Tactic Notation "delivering" constr(lemma1) "which" "ends" "at" constr(lemma2)
    "is" "sufficient" "because" constr(lemma3) :=
  let Htmp := fresh "Htmp" in
  apply leads_to_by_eventual_delivery;
  intros; pose proof lemma1 as Htmp; saturate_assumptions!;
  aux Htmp; 
  intros; simplify_eq; eapply lemma3; eauto; try (eapply lemma2; eauto).

End LivenessTLA.
