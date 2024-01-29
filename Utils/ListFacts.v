From Coq Require Import Bool List Permutation.

Definition NoDup_eqdec [A : Type] (A_eqdec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}) : 
  forall l : list A, {NoDup l} + {~ NoDup l}.
Proof.
  intros l.
  induction l as [ | x l IH ].
  - left. 
    constructor.
  - destruct IH as [ IH | IH ].
    + destruct (In_dec A_eqdec x l) as [ Hin | Hnotin ].
      * right.
        intros Hcontra.
        now inversion Hcontra.
      * left.
        now constructor.
    + right.
      intros Hcontra.
      now inversion Hcontra.
Qed.

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

Lemma filter_compose [A B : Type] (f : A -> B) (g : B -> bool) (l : list A) :
  filter g (map f l) = map f (filter (fun x => g (f x)) l).
Proof.
  induction l as [ | x l IH ].
  - reflexivity.
  - simpl.
    rewrite -> ! IH.
    now destruct (g (f x)).
Qed.

Lemma combine_map_fst [A B : Type] (l1 : list A) (l2 : list B) (H : length l1 = length l2) :
  map fst (combine l1 l2) = l1.
Proof.
  revert l2 H.
  induction l1 as [ | x l1 IH ]; intros; simpl in H |- *; 
    destruct l2 as [ | y l2 ]; simpl in H |- *; try discriminate.
  - reflexivity.
  - f_equal.
    apply IH.
    now injection H.
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

Lemma list_ind_3 : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall n, (forall l, length l = n -> P l) -> forall l, length l = S n -> P l) ->
  forall l : list A, P l.
Proof.
  intros. 
  remember (length l) as n eqn:E. 
  revert l E.
  induction n as [ | n IH ]; intros.
  - destruct l; simpl in E; congruence.
  - destruct l; try (simpl in E; congruence).
    eapply H0.
    2: now rewrite E.
    auto.
Qed.
