From Coq Require Import Lia List PeanoNat.
From Bythos.Utils Require Export Misc.

(* self-made finite type *)

(* using "b = true" should also work, but here we want to avoid considering equalities of identity proofs *)
Definition isTrue (b : bool) : Prop := if b then True else False.
Fact isTrue_true_iff b : isTrue b <-> b = true.
Proof. destruct b; unfold isTrue; intuition. Qed.
Fact isTrue_same_eq b (H1 H2 : isTrue b) : H1 = H2.
Proof. destruct b; simpl in *; try contradiction. now destruct H1, H2. Qed.
Fact isTrue_andb b1 b2 : isTrue (b1 && b2) <-> isTrue b1 /\ isTrue b2.
Proof. destruct b1, b2; intuition; try exact I. Qed. 

(* this is essentially a special case of { x | P x }, where P has proof irrelevance
    and only a finite number of elements satisfy P (so this becomes a finite type) *)
(* a very close formalization can be found in mathcomp (the ordinal type), 
    which depends on too many other definitions though *)
Inductive fin_nat (n : nat) : Set := FT (m : nat) (H : isTrue (Nat.ltb m n)).

Section FinNat.

Definition fin_nat_eqdec [n : nat] (m1 m2 : fin_nat n) : {m1 = m2} + {m1 <> m2}.
  destruct m1 as [ m1 H1 ], m2 as [ m2 H2 ].
  destruct (Nat.eq_dec m1 m2) as [ -> | Hneq ].
  - left. f_equal. apply isTrue_same_eq.
  - right. intros [=->]. contradiction.
Defined.
Definition fin_nat_rank [n : nat] (a : fin_nat n) : nat :=
  match a with FT _ m _ => S m end.
Fact fin_nat_cmp n (m1 m2 : fin_nat n) : m1 = m2 <-> fin_nat_rank m1 = fin_nat_rank m2.
Proof. 
  split; intros; try congruence.
  (* seems not very convenient to reason about fin_nat_eqdec *)
  (*
  destruct (fin_nat_eqdec m1 m2) eqn:E; try congruence. unfold fin_nat_eqdec in E. 
  destruct m1 as [ m1 ? ], m2 as [ m2 ? ]. simpl in H. 
  destruct (Nat.eq_dec m1 m2); simpl in E; try discriminate. 
  *)
  (* using the same logic as fin_nat_eqdec *)
  destruct m1 as [ m1 ? ], m2 as [ m2 ? ]. simpl in H. injection H as ->. f_equal. apply isTrue_same_eq.
Qed.

Fact le_left_minus_1 n m : S n <= m -> n <= m. Proof. lia. Qed.
Fact le_left_minus_1' n m : isTrue (Nat.leb (S n) m) -> isTrue (Nat.leb n m). 
Proof. rewrite !isTrue_true_iff, !Nat.leb_le. lia. Qed.
(* the following requires some tweak to ensure proof irrelevance *)
(*
Fixpoint fin_nat_enum_aux (n m : nat) (H : m <= n) : list (fin_nat n).
  destruct m as [ | m' ].
  - exact nil.
  - exact (FT n m' (proj2 (isTrue_true_iff _) (proj2 (Nat.ltb_lt _ _) H)) ::
      fin_nat_enum_aux n m' (le_left_minus_1 _ _ H)).
Defined.
*)
Fixpoint fin_nat_enum_aux (n m : nat) (H : isTrue (Nat.leb m n)) {struct m} : list (fin_nat n).
  destruct m as [ | m' ].
  - exact nil.
  - exact (FT n m' H :: fin_nat_enum_aux n m' (le_left_minus_1' _ _ H)). 
Defined.
Definition fin_nat_enum (n : nat) : list (fin_nat n) :=
  fin_nat_enum_aux n n (proj2 (isTrue_true_iff _) (Nat.leb_refl n)).
Fact fin_nat_enum_aux_incl n m1 m2 (H : m1 <= m2) H1 H2 : incl (fin_nat_enum_aux n m1 H1) (fin_nat_enum_aux n m2 H2).
Proof.
  revert n H1 H2. induction H as [ | m2 H IH ]; intros.
  - rewrite (isTrue_same_eq _ H1 H2). hnf; auto.
  - simpl. hnf. intros ? Hin. unshelve eapply IH in Hin; auto.
    1: now apply le_left_minus_1'.
    simpl. auto.
Qed.
Fact fin_nat_enum_complete n : forall a : fin_nat n, In a (fin_nat_enum n).
Proof.
  intros [ m H ].
  assert (In (FT n m H) (fin_nat_enum_aux n (S m) H)) as H0 by (simpl; auto).
  revert H0. now apply fin_nat_enum_aux_incl, Nat.ltb_lt, isTrue_true_iff.
Qed.
Fact fin_nat_enum_aux_NoDup n m H : NoDup (fin_nat_enum_aux n m H).
Proof.
  match goal with |- ?G => enough (G /\ list_max (map (@fin_nat_rank n) (fin_nat_enum_aux n m H)) = m); try tauto end.
  revert H. induction m as [ | m IH ]; intros; simpl.
  - split; constructor.
  - split.
    + specialize (IH (le_left_minus_1' m n H)). destruct IH as (Ha & Hb). 
      constructor; auto. 
      intros Hin. epose proof (list_max_le _ _) as H0. rewrite Hb in H0. apply proj1 in H0. specialize (H0 (le_n _)).
      rewrite Forall_forall in H0. specialize (H0 _ (in_map _ _ _ Hin)). simpl in H0. lia.
    + rewrite (proj2 (IH _)). destruct m; lia.
Qed.
Corollary fin_nat_enum_NoDup n : NoDup (fin_nat_enum n). 
Proof. apply fin_nat_enum_aux_NoDup. Qed.

End FinNat.

(* again, a special case of { x | P x } *)
(* after extraction, the inductive type parameters will be cleared ... *)
Inductive fin_mem {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) (dom : list A) : Type :=
  FM (a : A) (H : isTrue (ssrbool.is_left (in_dec eqdec a dom))).

Section FinMem.

  Context {A : Type} [eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}] [dom : list A].

  Local Notation fin_mem := (fin_mem eqdec dom).

  Definition fin_mem_eqdec (m1 m2 : fin_mem) : {m1 = m2} + {m1 <> m2}.
    destruct m1 as [ m1 H1 ], m2 as [ m2 H2 ].
    destruct (eqdec m1 m2) as [ -> | Hneq ].
    - left. f_equal. apply isTrue_same_eq.
    - right. intros [=->]. contradiction.
  Defined.

  Definition fin_mem_body (m : fin_mem) := match m with FM _ _ a _ => a end.
  Fact fin_mem_in a l : In a l <-> In (fin_mem_body a) (map fin_mem_body l).
  Proof.
    split; intros H; auto using in_map.
    induction l as [ | a' l IH ]; simpl in *; auto. destruct H; try tauto.
    destruct a as [ a H0 ], a' as [ a' H0' ]. simpl in H. 
    left. revert H0'. rewrite H. (* ! *) intros ?. f_equal. apply isTrue_same_eq.
  Qed.
  (*
  Definition fin_mem_lift_single (a : A.t) : list fin_mem :=
    (if in_dec eqdec a A.elements as s0
        return ((isTrue (ssrbool.is_left s0) -> fin_mem) -> list fin_mem)
      then fun f0 : True -> fin_mem => f0 I :: nil
      else fun _ : False -> fin_mem => nil) (FM a).
    (* pose proof (FM a) as f.
    destruct (in_dec eqdec a A.elements).
    - exact (f I :: nil).
    - exact nil.
  Defined. *)
  Fixpoint fin_mem_lift (l : list A.t) : list fin_mem :=
    match l with
    | nil => nil
    | a :: l' => fin_mem_lift_single a ++ fin_mem_lift l'
    end.
  Fact fin_mem_lift_peel l (H : incl l A.elements) : map fin_mem_body (fin_mem_lift l) = l.
  Proof.
    induction l as [ | a l IH ]; try reflexivity.
    simpl. pose proof (H _ (or_introl eq_refl)) as H0. specialize (IH (fun a H' => H a (or_intror H'))).
    rewrite map_app, IH. change (a :: l) with ((a :: nil) ++ l). f_equal. clear H IH.
    unfold fin_mem_lift_single.
    (* emm *)
  Abort.
  *)
  (* things are slightly more complicated without carrying a proof *)
  Fixpoint fin_mem_lift (l : list A) (H : isTrue (forallb (fun a => ssrbool.is_left (in_dec eqdec a dom)) l)) {struct l} : list fin_mem.
    destruct l as [ | a l' ].
    - exact nil.
    - simpl in H. apply (proj1 (isTrue_andb _ _)) in H. destruct H as (H1 & H2).
      exact (FM _ _ a H1 :: fin_mem_lift _ H2).
  Defined.
  Fact fin_mem_lift_qualified l (H : incl l dom) : isTrue (forallb (fun a => ssrbool.is_left (in_dec eqdec a dom)) l).
  Proof.
    induction l as [ | a l' IH ]; simpl; auto.
    rewrite isTrue_andb. pose proof (H _ (or_introl eq_refl)) as H0. specialize (IH (fun a H' => H a (or_intror H'))).
    split; auto. unfold ssrbool.is_left. rewrite (proj2 (sumbool_is_left _)); hnf; auto.
  Qed.
  Fact fin_mem_lift_peel l H : map fin_mem_body (fin_mem_lift l H) = l.
  Proof.
    induction l as [ | a l' IH ]; simpl; auto.
    destruct (proj1 _ _). (* ... *) simpl. f_equal. now rewrite IH.
  Qed.
  Fact fin_mem_lift_NoDup l H (Hnodup : List.NoDup l) : List.NoDup (fin_mem_lift l H).
  Proof.
    induction l as [ | a l IH ]; simpl; try solve [ constructor ].
    apply NoDup_cons_iff in Hnodup. destruct Hnodup as (Hnotin & Hnodup).
    destruct (proj1 _ _). (* ... *) constructor. 2: apply IH; auto.
    rewrite fin_mem_in. simpl. now rewrite fin_mem_lift_peel.
  Qed.

End FinMem.
