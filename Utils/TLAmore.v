From TLA Require Export logic.

Section Proof_Env.

  Context [Σ : Type].
  Variable (Γ Γ' : predicate Σ).

  (* combining two leads_to things *)

  Fact leads_to_combine (p1 q1 p2 q2 : predicate Σ)
    (* making Γ persistent would be convenient *)
    (H1 : □ Γ ∧ Γ' ⊢ p1 ~~> q1) (H2 : □ Γ ∧ Γ' ⊢ p2 ~~> q2)
    (* q1 and q2 have to be persistent *)
    (* writing H1' and H2' in this way would align with the form of invariant *)
    (H1' : q1 ∧ □ Γ ⊢ □ q1) (H2' : q2 ∧ □ Γ ⊢ □ q2) : 
    □ Γ ∧ Γ' ⊢ (p1 ∧ p2) ~~> (q1 ∧ q2).
  Proof.
    autounfold with tla in *.
    intros.
    destruct H0.
    specialize (H1 _ H k H0).
    specialize (H2 _ H k H3).
    destruct H1 as (k1 & H1), H2 as (k2 & H2).
    rewrite ! drop_drop in H1, H2.
    destruct H.
    assert (∀ (k k0 : nat), Γ (drop k (drop k0 e))) as H' 
      by (intros; now rewrite drop_drop).
    specialize (H1' _ (conj H1 (fun k => H' k _)) (Nat.max k1 k2 - k1)).
    specialize (H2' _ (conj H2 (fun k => H' k _)) (Nat.max k1 k2 - k2)).
    rewrite ! drop_drop in H1', H2'.
    replace (drop _ e) with (drop (Nat.max k1 k2 + k) e) in H1' by (f_equal; lia).
    replace (drop _ e) with (drop (Nat.max k1 k2 + k) e) in H2' by (f_equal; lia).
    repeat setoid_rewrite drop_drop.
    eauto.
  Qed.

  Context [A : Type].
  Variable (valid : A → Prop) (l : list A).
  Hypothesis (Hvalid : Forall valid l).  

  Fact leads_to_combine_batch (p q : A → predicate Σ)
    (H : ∀ a, valid a → (□ Γ ∧ Γ' ⊢ (p a) ~~> (q a))%L)
    (H' : ∀ a, valid a → ((q a) ∧ □ Γ ⊢ □ (q a))%L) :
    (□ Γ ∧ Γ' ⊢ (fold_right tla_and tla_true (map p l)) ~~> 
      (fold_right tla_and tla_true (map q l)))%L ∧
    (* the following needs to be proved together by induction *)
    ((fold_right tla_and tla_true (map q l)) ∧ □ Γ ⊢
      (□ fold_right tla_and tla_true (map q l)))%L.
  Proof using All.
    induction Hvalid as [ | a l Hv Hvalid' IH ]; simpl.
    - split.
      + now apply impl_drop_hyp, impl_to_leads_to.
      + now autounfold with tla.
    - specialize (IH Hvalid').
      destruct IH as (IH1 & IH2).
      split.
      + apply leads_to_combine; auto.
      + rewrite always_and.
        tla_split.
        * now tla_apply H'.
        * now tla_apply IH2.
  Qed.

  Corollary leads_to_combine_batch' (p q : A → Σ → Prop)
    (H : ∀ a, valid a → (□ Γ ∧ Γ' ⊢ ⌜ p a ⌝ ~~> ⌜ q a ⌝)%L)
    (H' : ∀ a, valid a → (⌜ q a ⌝ ∧ □ Γ ⊢ □ ⌜ q a ⌝)%L) :
    □ Γ ∧ Γ' ⊢ 
      ⌜ λ w, (∀ a, In a l → p a w) ⌝ ~~> ⌜ λ w, (∀ a, In a l → q a w) ⌝.
  Proof using All.
    tla_pose (proj1 (leads_to_combine_batch _ _ H H')).
    clear Hvalid.
    tla_apply leads_to_weaken.
    all: autounfold with tla; intros.
    - rewrite <- Forall_forall in H0.
      induction H0; simpl; auto.
    - revert a H1.
      rewrite <- Forall_forall.
      induction l; simpl in H0; auto.
      constructor; intuition.
  Qed.

End Proof_Env.

(* more notations *)

Definition satisfies {Σ : Type} (p : predicate Σ) (e : exec Σ) := p e.
(* TODO any pure predicate in the formalism of TLA? *)
Definition pure_pred {Σ : Type} (P : Prop) : predicate Σ := ⌜ λ _, P ⌝.

Notation "e ⊨ p" := (satisfies p%L e) (at level 100).
Notation "⌞  P  ⌟" := (pure_pred P%type).

#[export] Hint Unfold pure_pred satisfies : tla.

(* for always enabled action, its weak fairness is equivalent with happening infinitely often *)

Fact always_enabled_weak_fairness {Σ : Type} (a : action Σ) :
  □ tla_enabled a ⊢ ((weak_fairness a) → (□ ◇ ⟨a⟩)) ∧ ((□ ◇ ⟨a⟩) → (weak_fairness a)).
Proof.
  rewrite weak_fairness_alt3.
  tla_split.
  - unseal.
    destruct H0 as [ | H0 ]; auto.
    specialize (H0 0).
    firstorder.
  - apply impl_drop_hyp.
    tla_intro.
    tla_left.
Qed.
