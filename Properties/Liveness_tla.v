From Coq Require Import List Bool Lia ssrbool ListSet Permutation PeanoNat.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts Invariant.

From TLA Require Export logic.

From stdpp Require list.

Module Type ACLiveness 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns) (ACInv : ACInvariant A T AC Ns ACN).

Import A T AC Ns ACN ACInv.

(* Definition good_deliver_action w w' :=
  exists p, is_byz (src p) = false /\ In p (sentMsgs w) /\
    (consumed p = false) /\ (* ? *)
    system_step (Deliver p) w w'. *)
(*
Definition good_deliver_action w w' :=
  forall p, is_byz (src p) = false -> In p (sentMsgs w) ->
    (consumed p = false) -> (* ? *)
    system_step (Deliver p) w w'. 
*)

Definition satisfies {Σ : Type} (p : predicate Σ) (e : exec Σ) := p e.

#[local] Hint Unfold satisfies : tla.

Notation "e ⊨ p" := (satisfies p%L e) (at level 100).

Definition init w := w = initWorld.

Definition next w w' := ∃ q, system_step q w w'.

#[local] Hint Unfold init next : tla.

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
  (*
  autounfold with tla.
  unfold init, next.
  intros e (E & H) n.
  induction n as [ | n IH ].
  - rewrite drop_0 E.
    constructor.
  - specialize (H n).
    destruct H as (q & H).
    rewrite ! drop_n in H.
    simpl in H.
    econstructor; eauto.
  *)
Qed.

(*
Definition deliver_action_p p w w' :=
  system_step (Deliver p) w w'.
*)

(*
Definition good_deliver_action_p p w w' :=
  is_byz (src p) = false /\ In p (sentMsgs w) /\
    (consumed p = false) /\ (* ? *)
    system_step (Deliver p) w w'.
*)

(*
Definition fairness : predicate World :=
  ∀ p : Packet, 
    □ (⌜ λ w : World, is_byz (src p) = false ∧ (consumed p = false) ∧ In p (sentMsgs w) ⌝ →
      weak_fairness (deliver_action_p p)).
*)
(*
(* too strict? *)
Definition good_deliver_action_p p w w' :=
  is_byz (src p) = false /\ In p (sentMsgs w) /\
    (consumed p = false) /\ (* ? *)
    system_step (Deliver p) w w'.
*)

Definition good_deliver_action_p p w w' :=
  is_byz (src p) = false ∧ In p (sentMsgs w) ∧
    (* if p is already received then underspecify this transition *)
    (if consumed p then True else system_step (Deliver p) w w').

Definition fairness : predicate World :=
  ∀ p : Packet, weak_fairness (good_deliver_action_p p).

#[local] Hint Unfold good_deliver_action_p fairness : tla.

Fact psent_persistent_single p :
  ⌜ λ w, In p (sentMsgs w) ⌝ ∧ □ ⟨ next ⟩ ⊢
    □ (⌜ λ w, ∃ p', pkt_le p p' ∧ In p' (sentMsgs w) ⌝).
Proof.
  unfold pkt_le.
  apply init_invariant.
  - intros w Hin.
    exists p.
    split; try tauto.
  - intros w w' (p' & Ep' & Hin) (q & Hstep).
    (* TODO extract this out? even more troublesome than below! *)
    inversion Hstep; subst.
    1,3-6: exists p'; split; try assumption; simpl; auto.
    1: destruct (procInt _ _) in *; subst; simpl; rewrite in_app_iff; tauto.
    destruct (procMsgWithCheck _ _ _) in *.
    subst; cbn delta [sentMsgs] beta iota.
    destruct (Packet_eqdec p p0) as [ <- | Hneq ].
    + exists (receive_pkt p).
      simpl.
      split; try tauto.
    + destruct (if Packet_eqdec (receive_pkt p) p0 then (negb (consumed p)) else false) eqn:E0.
      * destruct (Packet_eqdec (receive_pkt p) p0) as [ <- | ]; try discriminate.
        apply negb_true_iff in E0.
        exists (receive_pkt p).
        split; try tauto.
        simpl.
        left; apply receive_pkt_idem.
      * exists p'.
        split; try assumption.
        simpl; rewrite in_app_iff.
        right; left.
        apply in_in_remove; try assumption.
        destruct Ep' as [ <- | Ep' ]; try congruence.
        subst p'.
        intros <-.
        destruct (Packet_eqdec _ _) in E0; try contradiction.
        apply negb_false_iff, receive_pkt_intact in E0.
        congruence.
Qed.

(* certainly, we would like to check whether this is actually what we want! *)

Definition reliable_condition (e : exec World) :=
  ∀ p, good_packet p → ∀ n, In p (sentMsgs (e n)) →
    ∃ k, In (receive_pkt p) (sentMsgs (e (k + n))).

Fact fairness_adequate (e : exec World) (Hrc : e ⊨ ⌜ init ⌝ ∧ □ ⟨ next ⟩) :
  (e ⊨ fairness)%L ↔ reliable_condition e.
Proof.
  unfold reliable_condition.
  autounfold with tla in *.
  split; intros H. 
  - intros p Hg n Hin.
    (* use persistent condition *)
    unshelve epose proof (psent_persistent_single p (drop n e) (conj Hin _)) as HH.
    1: unseal. (* ! *)
    weak_fairness



    

    destruct (consumed p) eqn:E.
    + exists 0.
      simpl.
      now rewrite (proj1 (receive_pkt_intact p) E).
    + 
    
      specialize (HH p n).
      epose proof (HH ?[Goalq]) as (k & HH').
      [Goalq]:{
        intros k. 
        hnf.
        rewrite drop_drop drop_n.
        simpl.
        
        
        destruct (HH _) as (k & HH).
      removehead HH. 
      




      
  unseal.
  
  
  split.
  - 
(*
Lemma eventual_delivery_single p (Hgood : good_packet p) :
  □ ⟨ next ⟩ ∧ weak_fairness good_deliver_action ⊢
  □ ⟨ next ⟩ ∧ weak_fairness (good_deliver_action_p p).
Proof.

  unseal.
  destruct H. split; auto.
  intros. unfold good_deliver_action, good_deliver_action_p in *.
  specialize (H0 k).
*)

(* TODO can we do these only at the level of proof modes? this is too ... *)
(*
Fact foo1 [Σ : Type] (p1 q1 p2 q2 : predicate Σ)
  (H1 : p1 ⊢ q1) (H2 : p2 ⊢ q2) : ((p1 ∧ p2) ⊢ (q1 ∧ q2)).
Proof. autounfold with tla in *. intuition. Qed.
*)
(*
(* not really useful ... *)
Fact foo2 [Σ : Type] (Γ p1 q1 p2 q2 : predicate Σ)
  (H1 : Γ ⊢ p1 ~~> □ q1) (H2 : Γ ⊢ p2 ~~> □ q2) : 
  Γ ⊢ (p1 ∧ p2) ~~> □ (q1 ∧ q2).
Proof.
  hnf in H1, H2.
  unfold leads_to, always, eventually, tla_implies in H1, H2.
  unseal.
  destruct H0.
  specialize (H1 _ H k H0).
  specialize (H2 _ H k H3).
  destruct H1 as (k1 & H1), H2 as (k2 & H2).
  repeat setoid_rewrite drop_drop in H1.
  repeat setoid_rewrite drop_drop in H2.
  exists (Nat.max k1 k2).
  intros kk.
  split.
  - now replace (kk + Nat.max k1 k2 + k) with ((kk + Nat.max k1 k2 - k1) + k1 + k) by lia.
  - now replace (kk + Nat.max k1 k2 + k) with ((kk + Nat.max k1 k2 - k2) + k2 + k) by lia.
Qed.
*)
Fact foo2 [Σ : Type] (Γ p1 q1 p2 q2 : predicate Σ) (next : action Σ)
  (H1 : □ ⟨ next ⟩ ∧ Γ ⊢ p1 ~~> q1) (H2 : □ ⟨ next ⟩ ∧ Γ ⊢ p2 ~~> q2)
  (* q1 and q2 have to be persistent *)
  (* writing H1' and H2' in this way would align with the form of invariant *)
  (H1' : q1 ∧ □ ⟨ next ⟩ ⊢ □ q1) (H2' : q2 ∧ □ ⟨ next ⟩ ⊢ □ q2) : 
  □ ⟨ next ⟩ ∧ Γ ⊢ (p1 ∧ p2) ~~> (q1 ∧ q2).
Proof.
  autounfold with tla in *.
  intros.
  destruct H0.
  specialize (H1 _ H k H0).
  specialize (H2 _ H k H3).
  destruct H1 as (k1 & H1), H2 as (k2 & H2).
  rewrite ! drop_drop in H1, H2.
  destruct H.
  assert (∀ (k k0 : nat), next (drop k (drop k0 e) 0) (drop k (drop k0 e) 1)) as H' 
    by (intros; now rewrite drop_drop).
  specialize (H1' _ (conj H1 (fun k => H' k _)) (Nat.max k1 k2 - k1)).
  specialize (H2' _ (conj H2 (fun k => H' k _)) (Nat.max k1 k2 - k2)).
  rewrite ! drop_drop in H1', H2'.
  replace (drop _ e) with (drop (Nat.max k1 k2 + k) e) in H1' by (f_equal; lia).
  replace (drop _ e) with (drop (Nat.max k1 k2 + k) e) in H2' by (f_equal; lia).
  repeat setoid_rewrite drop_drop.
  eauto.
Qed.

Fact foo2' [A Σ : Type] (Γ : predicate Σ) (p q : A → predicate Σ) (next : action Σ)
  (* TODO the validity condition is cumbersome! *)
  (valid : A → Prop)
  (H : forall (a : A), valid a → (□ ⟨ next ⟩ ∧ Γ ⊢ (p a) ~~> (q a))%L)
  (H' : forall (a : A), valid a → ((q a) ∧ □ ⟨ next ⟩ ⊢ □ (q a))%L)
  (l : list A) (Hv : Forall valid l) :
    (□ ⟨ next ⟩ ∧ Γ ⊢ (fold_right tla_and tla_true (map p l)) ~~> 
      (fold_right tla_and tla_true (map q l)))%L ∧
    (* the following needs to be proved together *)
    ((fold_right tla_and tla_true (map q l)) ∧ □ ⟨next⟩ ⊢
      (□ fold_right tla_and tla_true (map q l)))%L.
Proof.
  induction Hv as [ | a l Ha Hv (IH1 & IH2) ]; simpl.
  - split.
    + now apply impl_drop_hyp, impl_to_leads_to.
    + unseal.
  - split.
    + apply foo2; auto.
    + specialize (H' a).
      rewrite always_and.
      tla_split.
      * etransitivity.
        2: apply H'; try assumption.
        tla_assumption.
      * etransitivity.
        2: apply IH2.
        tla_assumption.
Qed.

Fact foo2'' [A Σ : Type] (Γ : predicate Σ) (p q : A → Σ → Prop) (next : action Σ)
  (valid : A → Prop)
  (H : forall (a : A), valid a → (□ ⟨ next ⟩ ∧ Γ ⊢ ⌜ p a ⌝ ~~> ⌜ q a ⌝)%L) 
  (H' : forall (a : A), valid a → (⌜ q a ⌝ ∧ □ ⟨ next ⟩ ⊢ □ ⌜ q a ⌝)%L)
  (l : list A) (Hv : Forall valid l) :
    □ ⟨ next ⟩ ∧ Γ ⊢ 
      ⌜ λ w, (∀ a, In a l → p a w) ⌝ ~~> ⌜ λ w, (∀ a, In a l → q a w) ⌝.
Proof.
  etransitivity.
  1: apply (proj1 (foo2' _ _ _ _ valid H H' l Hv)).
  clear Hv.
  eapply leads_to_weaken.
  - unseal.
    rewrite <- Forall_forall in H0.
    induction H0; simpl; auto.
  - unseal.
    revert a H1.
    rewrite <- Forall_forall.
    induction l; simpl in H0; auto.
    constructor; intuition.
Qed.

(* Fact foo2 [Σ : Type] (Γ p1 q1 p2 q2 : predicate Σ) (next : action Σ)
  (H1 : □ ⟨ next ⟩ ∧ Γ ⊢ p1 ~~> q1) (H2 : □ ⟨ next ⟩ ∧ Γ ⊢ p2 ~~> q2)
  (* q1 and q2 have to be persistent *)
  (* writing H1' and H2' in this way would align with the form of invariant *)
  (H1' : q1 ∧ □ ⟨ next ⟩ ⊢ □ q1) (H2' : q2 ∧ □ ⟨ next ⟩ ⊢ □ q2) : 
  □ ⟨ next ⟩ ∧ Γ ⊢ (p1 ∧ p2) ~~> (q1 ∧ q2). *)

(*
Fact foo3 [Σ : Type] (Γ p q r : predicate Σ) (H : Γ ⊢ q ~~> r) :
  Γ ⊢ (□ p ∧ q) ~~> (□ p ∧ r).
Proof.
  hnf in H.
  unfold leads_to, always, eventually, tla_implies in H.
  unseal.
  destruct H1.
  specialize (H _ H0 k H2).
  destruct H as (k1 & H).
  rewrite drop_drop in H.
  exists k1.
  split; auto.
Qed.
*)
(* modus ponens? but with the same hypotheses *)
(*
Fact foo4 [Σ : Type] (Γ p q : predicate Σ)
  (Hp : Γ ⊢ p) (Hpq : Γ ⊢ p → q) : Γ ⊢ q.
Proof. firstorder. Qed.
*)
(* like leads_to_weaken, but with hypotheses *)
(*
Fact foo5 [Σ : Type] (Γ p1 p2 q1 q2 : predicate Σ)
  (H : Γ ⊢ p1 ~~> q1) (Hpre : Γ ⊢ p2 → p1) (Hpost : Γ ⊢ q1 → q2) : 
  Γ ⊢ p2 ~~> q2.
Proof. 
  autounfold with tla in *.
  intros.
  apply Hpre in H1.
*)

(* TODO cannot see better way for now *)
(*
Fact psent_persistent pkts :
  ⌜λ w, incl pkts (sentMsgs w)⌝ ∧ □ ⟨ next ⟩ ⊢
    □ (⌜λ w, ∃ pkts', Forall2 pkt_le pkts pkts' ∧ incl pkts' (sentMsgs w)⌝).
Proof.
  induction pkts as [ | p pkts IH ].
  - apply impl_drop_hyp.
    unseal.
    now exists nil.
  - pose proof (psent_persistent_single p) as H.
    match type of IH with pred_impl ?a _ => 
      match type of H with pred_impl ?b _ => 
        transitivity (a ∧ b)%L end end.
    + tla_simp.
      repeat (tla_split; try tla_assumption).
      all: apply impl_drop_one, state_pred_impl; intros w.
      all: unfold incl; simpl; intuition.
    + etransitivity.
      1: apply foo1; eassumption.
      (* degrade *)
      rewrite <- always_and.
      apply impl_under_always.
      rewrite combine_state_preds.
      apply state_pred_impl.
      intros w ((pkts' & Ha1 & Ha2) & (p' & Hb1 & Hb2)).
      exists (p' :: pkts').
      split.
      * now constructor.
      * hnf in Ha2 |- *; simpl. 
        intros p0 [ <- | Hin ]; intuition.
Qed.
*)
Lemma eventual_delivery_single p (Hgood : good_packet p) :
  □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜λ w, In p (sentMsgs w)⌝ ~~> ⌜λ w, In (receive_pkt p) (sentMsgs w)⌝.
Proof.
  unfold next, fairness, good_deliver_action_p.
  evar (bb : predicate World).
  match goal with |- pred_impl (tla_and ?aa _) _ =>
    transitivity (tla_and aa bb) end.
  1: tla_split; [ tla_assumption | ].
  1: rewrite tla_and_comm; subst bb; apply impl_drop_one, forall_apply with (x0:=p).
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
  - intros w w' Hin (q & Hstep') (_ & H_src_nonbyz & Hstep).
    destruct p as [ ? ? ? [] ].
    + eapply psent_norevert_is_invariant; eauto.
    + simpl in Hstep.
      clear q Hstep'.
      inversion Hstep; try discriminate.
      injection H as <-.
      destruct (procMsgWithCheck _ _ _) in *.
      subst; cbn; now left.
  - intros w Hin.
    hnf in Hgood |- *.
    destruct Hgood as (? & ? & ? & ?).
    eexists.
    split_and ?; try assumption.
    destruct (consumed p) eqn:EE; try exact I.
    eapply DeliverStep; eauto.
    (* ...? *)
    rewrite (surjective_pairing (procMsgWithCheck _ _ _)).
    reflexivity.
Qed.
(*
Lemma leads_to_fork' {Σ A: Type} (h: A → Σ → Prop) (h': A → Prop)
  (f: predicate Σ) (p q: Σ → Prop) :
  (f ⊢ ⌜p⌝ ~~> ⌜λ s, ∃ x, h' x ∧ h x s⌝) →
  (∀ (x: A), h' x → (f ⊢ ⌜h x⌝ ~~> ⌜q⌝)) →
  (f ⊢ ⌜p⌝ ~~> ⌜q⌝).
Proof.
  intros Hph Hhq.
  erewrite <- leads_to_trans; tla_split; [ apply Hph | ].
  apply leads_to_exist_intro.
  intros x. unseal. destruct H0. eapply Hhq; try eassumption.
Qed.
*)
Corollary eventual_delivery pkts (Hgood : Forall good_packet pkts) :
  □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜λ w, incl pkts (sentMsgs w)⌝ ~~> 
  ⌜λ w, ∀ p, In p pkts → In (receive_pkt p) (sentMsgs w)⌝. (* need some detour if not to write in this way *)
Proof.
  apply foo2'' with (valid:=good_packet); try assumption.
  - intros; now apply eventual_delivery_single.
  - intros p _.
    apply is_invariant_in_tla, psent_norevert_is_invariant.
Qed.

  (*

  induction pkts as [ | n IH [ | p pkts ] Elen ] using list_ind_3; try discriminate.
  - simpl.
    apply impl_drop_hyp, leads_to_refl.
  - cbn delta [map] beta iota.
    simpl in Elen.
    injection Elen as <-.
    apply Forall_cons_iff in Hgood.
    destruct Hgood as (Hg & Hgood).
    (* this is nice *)
    apply leads_to_fork' with (h':=fun pkts' => Forall2 pkt_le pkts pkts')
      (h:=fun pkts' w => incl (receive_pkt p :: pkts') (sentMsgs w)).
    + admit.
    + intros pkts' Hf.
      assert (Forall good_packet pkts') as Htmp.
      { eapply list.Forall2_Forall_r; try eassumption.
        revert Hgood.
        apply Forall_impl.
        intros; rewrite <- pkt_le_good_packet; eauto.
      }
      specialize (IH _ (eq_sym (list.Forall2_length _ _ _ Hf)) Htmp).
      

      (* eapply foo4.
      1: apply IH. *)


      etransitivity.
      2: apply leads_to_weaken with 
        (p1:=((□ ⌜ λ w : World, In (receive_pkt p) (sentMsgs w) ⌝) ∧ ⌜ λ w : World, incl pkts' (sentMsgs w) ⌝)%L)
        (q1:=((□ ⌜ λ w : World, In (receive_pkt p) (sentMsgs w) ⌝) ∧ ⌜ λ w : World, incl (map receive_pkt pkts') (sentMsgs w) ⌝)%L).
      * now apply foo3.
      * always state_pred
      leads_to 


    etransitivity.
    2: apply leads_to_trans with (q:=⌜λ w, ∃ pkts', Forall2 pkt_le pkts pkts' ∧ incl (receive_pkt p :: pkts') (sentMsgs w)⌝).
    tla_split.
    + admit.
    + (* ex elim *)
      eapply leads_to_fork.
      rewrite <- exist_state_pred.
      apply leads_to_exist_intro.
      intros pkts'.
      leads_to state_pred tla_and
      
  
    etransitivity.
    1: apply IH.


    leads_to "refl"
  




Lemma eventual_delivery_single p (Hgood : good_packet p) :
  □ ⟨ next ⟩ ∧ weak_fairness good_deliver_action ⊢
  ⌜λ w, In p (sentMsgs w)⌝ ~~> ⌜λ w, In (receive_pkt p) (sentMsgs w)⌝.
Proof.
  unfold next.
  apply wf1.
  - intros w w' Hin (q & Hstep).
    (* TODO extract this out? *)
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
  - intros w w' Hin _ (p' & H_src_nonbyz & Hin' & Hstep).
    hnf in Hdl.
      


    1-5: auto.
    inversion Hstep.


Lemma eventual_delivery pkts (Hgood : Forall good_packet pkts) :
  □ ⟨ next ⟩ ∧ weak_fairness good_deliver_action ⊢
  ⌜λ w, incl pkts (sentMsgs w)⌝ ~~> ⌜λ w, incl (map receive_pkt pkts) (sentMsgs w)⌝.
Proof.
  unfold next.
  apply wf1.
  - 
*)

Lemma bar1 e (H : (□ ⟨ next ⟩)%L e) k o :
  exists l, system_trace (e k) l ∧ (e (o + k) = final_world (e k) l).
Proof.
  autounfold with tla in H.
  unfold next in H.
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

(* one-hop *)
Lemma bar (P Q : World -> Prop)
  (H : forall w (Hw : reachable w),
    (* message-driven *)
    P w → exists pkts, Forall good_packet pkts ∧ incl pkts (sentMsgs w) ∧
      (forall w0 l0 (Htrace : system_trace w l0) (Ew0 : w0 = final_world w l0),
        incl (map receive_pkt pkts) (sentMsgs w0) → Q w0)) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢ ⌜ P ⌝ ~~> ⌜ Q ⌝.
Proof.
  tla_pose reachable_in_tla.
  unseal.
  destruct H0 as (_ & Hnext & Hfair & Hrc).
  specialize (H (e k) (Hrc _) H1).
  destruct H as (pkts & Hgood & Hincl & H).
  pose proof (eventual_delivery _ Hgood e (conj Hnext Hfair) k Hincl) as (k0 & Htmp).
  exists k0.
  hnf in Htmp.
  rewrite drop_drop drop_n /= in Htmp.
  pose proof (bar1 e Hnext k k0) as (l & Htrace & Ew0).
  specialize (H _ _ Htrace Ew0).
  apply H.
  intros ? (p & <- & ?)%in_map_iff.
  now apply Htmp.
Qed.

(* now, really nice things *)

Lemma terminating_convergence_in_tla v (H_byz_minor : num_byz ≤ t0) :
  ⌜ init ⌝ ∧ □ ⟨ next ⟩ ∧ fairness ⊢
  ⌜ all_honest_nodes_submitted v ⌝ ~~> ⌜ all_honest_nodes_confirmed ⌝.
Proof.
  apply bar.
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
  tla_apply (leads_to_trans _ (⌜ mutual_lightcert_conflict_detected n1 n2 ⌝)).
  tla_split.
  - apply bar.
    intros.
    pose proof (mutual_lightcerts_sent _ _ _ Hw H) as (b1 & b2 & b3 & b4 & Hsuffcond).
    exists (mutual_lightcerts w n1 n2 b1 b2 b3 b4).
    change (map receive_pkt _) with (mutual_lightcerts w n1 n2 true true true true).
    split_and ?; try assumption.
    1: unfold confirmed_different_values, confirmed in H.
    1: unfold mutual_lightcerts; repeat (constructor; try tauto).
    intros.
    eapply eventually_mutual_lightcert_conflict_detected; try eassumption; eauto.
  - apply bar.
    intros.
    pose proof (fullcerts_all_received_suffcond _ _ Hw H) as Hsuffcond.
    destruct (fullcerts_all_sent w v Hw H) as (pkts & Hincl & Hgood & Htmp).
    simpl in Hsuffcond; clear Htmp.
    exists pkts.
    split_and ?; try assumption.
    intros.
    eapply terminating_convergence; try eassumption; eauto.


    pose proof (mutual_lightcerts_sent _ _ _ Hw H) as (b1 & b2 & b3 & b4 & Hsuffcond).
    exists (mutual_lightcerts w n1 n2 b1 b2 b3 b4).
    change (map receive_pkt _) with (mutual_lightcerts w n1 n2 true true true true).
    split_and ?; try assumption.
    1: unfold confirmed_different_values, confirmed in H.
    1: unfold mutual_lightcerts; repeat (constructor; try tauto).
    intros.
    eapply eventually_mutual_lightcert_conflict_detected; try eassumption; eauto.





    pose proof (honest_submit_all_received_ _ _ Hw H) as Hsuffcond.
    destruct (submit_msgs_all_sent w v Hw H) as (pkts & Hincl & Hgood & Htmp).
    simpl in Hsuffcond; clear Htmp.
    exists pkts.
    split_and ?; try assumption.
    intros.
    eapply terminating_convergence; try eassumption; eauto.
Qed.

End ACLiveness.
