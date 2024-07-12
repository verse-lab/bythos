From Coq Require Import Bool List Permutation RelationClasses.

Lemma partition_filter [A : Type] (f : A -> bool) l :
  partition f l = (filter f l, filter (fun a => negb (f a)) l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    now destruct (f x).
Qed.

Fact NoDup_app : forall [A : Type] (l1 l2 : list A)
  (H1: NoDup l1) (H2: NoDup l2)
  (Hneq: forall x y, In x l1 -> In y l2 -> x <> y),
  NoDup (l1 ++ l2).
Proof.
  intros A l1. 
  induction l1 as [ | x l1 IH ]; intros; simpl; auto.
  inversion_clear H1. 
  simpl in Hneq.
  constructor.
  - intros HH. 
    apply in_app_or in HH.
    destruct HH as [ HH | HH ]; try contradiction.
    now apply (Hneq x x (or_introl (eq_refl x)) HH).
  - apply IH; auto.
Qed.

Fact Forall_filter [A : Type] (f : A -> bool) l (P : A -> Prop) 
  (H : Forall P l) : Forall P (filter f l).
Proof.
  rewrite -> Forall_forall in H |- *.
  setoid_rewrite -> filter_In.
  intros.
  now apply H.
Qed.

Fact NoDup_combine_l [A B : Type] (l1 : list A) (l2 : list B) (H : NoDup l1) :
  NoDup (combine l1 l2).
Proof.
  revert l2.
  induction l1 as [ | a l1 IH ]; intros; simpl.
  1: constructor.
  destruct l2 as [ | b l2 ].
  1: constructor.
  rewrite -> NoDup_cons_iff in H |- *.
  split.
  - intros HH.
    now apply in_combine_l in HH.
  - now apply IH.
Qed.

Lemma length_eq_Forall2_True [A B : Type] (l1 : list A) (l2 : list B) (H : length l1 = length l2) :
  Forall2 (fun _ _ => True) l1 l2.
Proof.
  revert l2 H.
  induction l1 as [ | x l1 IH ]; intros; simpl in H |- *; 
    destruct l2 as [ | y l2 ]; simpl in H |- *; try discriminate; auto.
Qed.

Lemma combine_map_fst [A B : Type] (l1 : list A) (l2 : list B) (H : length l1 = length l2) :
  map fst (combine l1 l2) = l1.
Proof.
  apply length_eq_Forall2_True in H.
  induction H; simpl; congruence.
Qed.

Lemma Permutation_split_combine {A : Type} (f : A -> bool) (l : list A) :
  Permutation l (filter f l ++ filter (fun a => negb (f a)) l).
Proof.
  induction l as [ | a l IH ]; auto.
  simpl.
  destruct (f a) eqn:E; simpl.
  - now apply perm_skip.
  - etransitivity. 
    1: apply perm_skip, IH.
    now apply Permutation_middle.
Qed.

Fact in_remove_iff [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y})
  (l : list A) (x y : A) : In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  split.
  - apply in_remove.
  - intros (H & H0).
    revert H0 H.
    apply in_in_remove.
Qed.

Fact in_cons_iff [A : Type] (l : list A) (x y : A) : In x (y :: l) <-> y = x \/ In x l.
Proof. reflexivity. Qed.

Definition set_add_simple [A : Type] (A_eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) 
  (a : A) (l : list A) : list A :=
  if in_dec A_eqdec a l then l else a :: l.

Fact incl_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a : A) (l : list A) : incl l (set_add_simple eqdec a l).
Proof. hnf. intros. unfold set_add_simple. destruct (in_dec _ _ _); simpl; tauto. Qed.

Fact In_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a a' : A) (l : list A) : In a' (set_add_simple eqdec a l) <-> a = a' \/ In a' l.
Proof. unfold set_add_simple. destruct (in_dec _ _ _); simpl; intuition congruence. Qed.

Fact NoDup_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a : A) (l : list A) : List.NoDup l -> List.NoDup (set_add_simple eqdec a l).
Proof. intros H. unfold set_add_simple. destruct (in_dec _ _ _); simpl; auto. now constructor. Qed.

Definition Ineq [A : Type] (l1 l2 : list A) : Prop := forall x, In x l1 <-> In x l2.

#[export] Instance Equivalence_Ineq {A : Type} : Equivalence (@Ineq A).
Proof. constructor; hnf; unfold Ineq in *; firstorder. Qed.

Fact length_gt_0_notnil [A : Type] [l : list A] (H : 0 < length l) :
  l <> nil /\ exists a, In a l.
Proof. destruct l; [ inversion H | ]. simpl. split; try discriminate; eauto. Qed.

Definition option_map_list [A B : Type] (f : A -> option B) (l : list A) : list B :=
  List.flat_map (fun a => match f a with Some a' => a' :: nil | _ => nil end) l.

Fact option_map_list_In [A B : Type] (f : A -> option B) (l : list A) (b : B) :
  In b (option_map_list f l) <-> exists a : A, In a l /\ f a = Some b.
Proof.
  induction l as [ | a l IH ]; simpl. 1: firstorder. 
  rewrite in_app_iff, IH. destruct (f a) eqn:E; simpl; split; try solve [ firstorder ].
  - intros [ [ -> | ] | (a0 & Hina0 & E0) ]; try eauto. contradiction.
  - intros (a0 & [ <- | Hina0 ] & E0); try eauto. left. left. congruence.
  - intros (a0 & [ <- | Hina0 ] & E0); try eauto. congruence.
Qed.
