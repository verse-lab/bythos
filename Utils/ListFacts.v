From Coq Require Import Bool List Permutation.

(* FIXME: change the file name into the more general "Utils" later! *)

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

Fact in_remove_iff [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y})
  (l : list A) (x y : A) : In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  split.
  - apply in_remove.
  - intros (H & H0).
    revert H0 H.
    apply in_in_remove.
Qed.

Definition prod_eq_dec {A B : Type} (eq_dec_a : forall x y : A, {x = y} + {x <> y})
  (eq_dec_b : forall x y : B, {x = y} + {x <> y}) :
  forall x y : (A * B)%type, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; try apply eq_dec_a; try apply eq_dec_b.
Qed.

Fact eqdec_refl {A B : Type} (eqdec : forall x y : A, {x = y} + {x <> y}) (x : A) (b1 b2 : B) :
  (if eqdec x x then b1 else b2) = b1.
Proof. destruct (eqdec _ _); auto; try contradiction. Qed.

Fact in_cons_iff [A : Type] (l : list A) (x y : A) : In x (y :: l) <-> y = x \/ In x l.
Proof. reflexivity. Qed.

Definition map_update [A B : Type] (A_eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) 
  (a : A) (b : B) (mp : A -> B) : A -> B :=
  fun a' => if A_eqdec a a' then b else mp a'.

(* TODO ABC should have something similar *)

Definition set_add_simple [A : Type] (A_eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) 
  (a : A) (l : list A) : list A :=
  if in_dec A_eqdec a l then l else a :: l.
