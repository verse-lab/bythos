From Coq Require Import List Bool Lia ListSet Permutation PeanoNat RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.

From ABCProtocol.Utils Require Export TLAmore. 
(* used this to suppress warning about coercion, but now anyway *)
(* this would require some time ... *)
(* Export -(coercions) TLAmore. (* need to separate Require and Import; otherwise Coqdep will complain *) *)

Module LivenessTLA (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr) 
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P PSOp Pr Ns Adv).

Section Preliminaries.

Definition exec_rel (e e' : exec World) : Prop := ∀ n, World_rel (e n) (e' n).

Definition init w := w = initWorld.

Definition next w w' := ∃ q, system_step q w w'.

(* use functions to eliminate ambiguity, which refers to the case where
    multiple "q" may satisfy the "∃" above *)

Definition nextf (f : exec system_step_descriptor) : predicate World :=
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
    rewrite system_trace_snoc final_world_snoc -Ew0 //=.
Qed.

End Preliminaries.

Global Hint Unfold init next : tla.

Global Instance Equivalence_exec_rel : Equivalence exec_rel.
Proof.
  constructor; hnf; intros; hnf in *; intros; try reflexivity; try now symmetry; try now transitivity (y n).
Qed.

Section Fairness.

Definition good_deliver_action_p p w w' :=
  if consumed p 
  then True 
  else In p (sentMsgs w) → system_step (Deliver p) w w'.

Definition fairness : predicate World :=
  (∀ p : Packet, ⌞ good_packet p ⌟ → weak_fairness (good_deliver_action_p p))%L.

#[local] Hint Unfold good_deliver_action_p fairness : tla.

(* like in IronFleet, always-enabled action would simplify the proof *)

Fact fairness_is_always_enabled [p] (Hg : good_packet p) :
  ⊢ □ tla_enabled (good_deliver_action_p p).
Proof.
  unseal.
  hnf.
  destruct (consumed p); eauto.
  destruct Hg as (? & ?).
  eexists.
  intros HH.
  eapply DeliverStep with (p:=p); try assumption; try reflexivity.
  rewrite (surjective_pairing (procMsgWithCheck _ _ _)).
  reflexivity.
Qed.

(* certainly, we would like to check whether this is actually what we want! *)
(* semantically, what we want is ...? *)

(*
Fact consumed_is_changed_by_delivery_pre :
  ∀ p, good_packet p → consumed p = false → ∀ w w', In p (sentMsgs w) →
    w' = next_world (Deliver p) w → system_step (Deliver p) w w'.
Proof.
  intros. hnf in * |-. subst w'. eapply DeliverStep; try solve [ reflexivity | assumption | tauto ].
  simpl. rewrite (surjective_pairing (procMsgWithCheck _ _ _)). reflexivity.
Qed.
*)
Definition reliable_condition (e : exec World) :=
  ∀ p, good_packet p → consumed p = false → ∀ n, In p (sentMsgs (e n)) →
    ∃ k, system_step (Deliver p) (e (k + n)) (e (S (k + n))).

(*
Definition reliable_condition_ (e : exec World) :=
  ∀ p, good_packet p → consumed p = false → ∀ n, In p (sentMsgs (e n)) →
    ∃ k, e (S (k + n)) = next_world (Deliver p) (e (k + n)).
*)
(* a lemma which will be used below, stating that the existence of
    an undelivered message will only be changed by an delivery action
  hope this would work for different network models ... *)

Fact consumed_is_changed_by_delivery [e : exec World] (Hrc : e ⊨ □ ⟨ next ⟩) 
  [p n] (E : consumed p = false) (Hin : In p (e n).(sentMsgs)) 
  k (Hnotin : ¬ In p (e (k + n)).(sentMsgs)) :
  ∃ k' : nat, k' < k ∧ system_step (Deliver p) (e (k' + n)) (e (S (k' + n))).
Proof.
  induction k as [ | k IH ]; intros; simpl in Hnotin.
  1: contradiction.
  destruct (in_dec Packet_eqdec p (sentMsgs (e (k + n)))) as [ Hin' | Hnotin' ].
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
  - now rewrite H0 in Hin'. (* TODO congruence no longer works now? *)
  - destruct (procMsgWithCheck _ _ _) as (st', ms) in Heq.
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
(*
Fact reliable_condition_change [e : exec World] (Hrc : e ⊨ □ ⟨ next ⟩) :
  reliable_condition e ↔ reliable_condition_ e.
Proof.
  split; intros H; hnf in H |- *; intros; saturate_assumptions!; destruct H as (k & H).
  - exists k. now apply next_world_sound.
  - 
    assert (¬ In p (e (S (k + n))).(sentMsgs)) as Htmp.
    { rewrite H /= (surjective_pairing (procMsgWithCheck _ _ _)) /= In_sendout In_consume. 
      intuition.
    apply consumed_is_changed_by_delivery in H
    apply consumed_is_changed_by_delivery_pre in H.
*)

(* what if things go too strong *)
(*
Fact fairness_strictly_stronger [e : exec World] (Hrc : e ⊨ □ ⟨ next ⟩) :
  (e ⊨ (∀ p : Packet, ⌞ good_packet p ⌟ → weak_fairness (system_step (Deliver p)))%L)%L ↔ reliable_condition e.
Proof.
  unfold reliable_condition.
  autounfold with tla in *.
  split; intros H.
  - intros p Hg E n Hin.
    specialize (H _ Hg n).
    destruct (Classical_Prop.classic (∀ k : nat, tla_enabled (system_step (Deliver p)) (drop k (drop n e)))).
    + specialize (H H0).
      destruct H as (k & H).
      rewrite ! drop_drop ! drop_n /= in H.
      eauto.
    + rewrite classical.classical.not_forall /tla_enabled/enabled/state_pred in H0.
      destruct H0 as (k & H0).
      rewrite drop_drop drop_n /= in H0.
      assert (¬ In p (e (k + n)).(sentMsgs)) as Htmp.
      { intros Htmp. apply H0. eexists. eapply DeliverStep; try reflexivity; try auto. 1: hnf in *; tauto. 
        rewrite (surjective_pairing (procMsgWithCheck _ _ _)). reflexivity. }
      apply consumed_is_changed_by_delivery in Htmp; auto.
      destruct Htmp as (? & ? & ?).
      eauto.
  - intros p Hg k ?.
    (* boom here, since a received packet is not guaranteed to be delivered again *)
Abort.
*)

Fact fairness_adequate [e : exec World] (Hrc : e ⊨ □ ⟨ next ⟩) :
  (e ⊨ fairness)%L ↔ reliable_condition e.
Proof.
  unfold reliable_condition.
  autounfold with tla in *.
  split; intros H.
  - intros p Hg E n Hin.
    specialize (H _ Hg n (fairness_is_always_enabled Hg _)).
    rewrite E in H.
    destruct H as (k & H).
    rewrite ! drop_drop ! drop_n /= in H.
    destruct (in_dec Packet_eqdec p (sentMsgs (e (k + n)))) as [ Hin' | Hnotin' ].
    1: exists k; intuition.
    apply consumed_is_changed_by_delivery in Hnotin'; auto.
    destruct Hnotin' as (? & ? & ?).
    eauto.
  - intros p Hg k _.
    destruct (consumed p) eqn:E.
    1: now exists 0.
    specialize (H _ Hg E).
    (* here, we cannot directly construct the existence, 
      so we have to go classic (i.e., prove by contradiction) *)
    destruct (Classical_Prop.classic (∃ n : nat, In p (sentMsgs (e (n + k))))) as [ (n & Hin) | H0 ].
    + specialize (H _ Hin).
      destruct H as (k0 & Hstep).
      rewrite !Nat.add_assoc in Hstep.
      exists (k0 + n).
      now rewrite !drop_drop !drop_n /=.
    + assert (∀ n : nat, ¬ In p (e (n + k)).(sentMsgs)) as H0'.
      { intros n Hcontra.
        apply H0; eauto.
      }
      exists 0.
      rewrite !drop_drop !drop_n /=.
      specialize (H0' 0).
      now intros.
Qed.

Lemma eventual_delivery_single [p] (Hgood : good_packet p) :
  □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜λ w, In p (sentMsgs w)⌝ ~~> ⌜λ w, In (receive_pkt p) (sentMsgs w)⌝.
Proof.
  destruct p as [ ? ? ? [] ]; simpl receive_pkt.
  1: simpl; apply impl_drop_hyp, leads_to_refl.
  (* exploit the equivalence above to achieve simpler proof! *)
  autounfold with tla.
  intros e (Hnext & Hfair) k Hin.
  rewrite drop_n /= in Hin.
  apply fairness_adequate in Hfair; try assumption.
  apply Hfair in Hin; auto.
  destruct Hin as (k0 & (_ & _ & (? & ? & _ & E))%DeliverStep_inv).
  exists (S k0).
  rewrite drop_drop drop_n /= E /= In_sendout In_consume /=.
  tauto.
  (*
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
    inversion Hstep; subst.
    1,3-4: left; simpl; auto.
    1: destruct (procInt _ _) in *; subst; simpl; rewrite In_sendout; tauto.
    1: rewrite In_sendout1; tauto.
    destruct (procMsgWithCheck _ _ _) in *.
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
      destruct (procMsgWithCheck _ _ _) in *.
      subst; simpl.
      rewrite ?In_sendout ?In_consume /=.
      tauto.
  - intros.
    apply (fairness_is_always_enabled _ Hgood (fun _ => s) 0). (* trick *)
  *)
Qed.

Corollary eventual_delivery [pkts] (Hgood : Forall good_packet pkts) :
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
Lemma leads_to_exec_rel [e e' : exec World] (H : exec_rel e e')
  (P Q : World → Prop) (HP : World_rel_cong P) (HQ : World_rel_cong Q) :
  (e ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝) → (e' ⊨ ⌜ P ⌝ ~~> ⌜ Q ⌝).
Proof.
  unseal. symmetry in H. pose proof (HP _ _ (H k)) as Htmp. saturate_assumptions!.
  destruct H0 as (k0 & H0). exists k0. eapply HQ. 2: apply H0. symmetry. apply H.
Qed.

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

Global Tactic Notation "delivering" constr(lemma1) "which" "ends" "at" constr(lemma2)
    "is" "sufficient" "because" constr(lemma3) :=
  let Htmp := fresh "Htmp" in
  apply leads_to_by_eventual_delivery;
  intros; pose proof lemma1 as Htmp; saturate_assumptions!;
  aux Htmp; 
  intros; simplify_eq; eapply lemma3; eauto; try (eapply lemma2; eauto).

End LivenessTLA.
