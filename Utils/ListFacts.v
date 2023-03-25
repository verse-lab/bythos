From Coq Require Import Bool List.

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
