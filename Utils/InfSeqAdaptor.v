From Coq Require Import List Bool Lia ssrbool ListSet Permutation PeanoNat RelationClasses.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From InfSeqExt Require Export infseq exteq map.

(* extensions of Stream library *)

Section Stream_Ext.

(* taking a finite prefix would also be useful *)

Fixpoint Str_firstn [T : Type] (n : nat) (l : Stream T) : list T :=
  match n with
  | O => nil
  | S n' => Streams.hd l :: Str_firstn n' (Streams.tl l)
  end.

Fixpoint Str_prepend_list [T : Type] (l : list T) (s : Stream T) : Stream T :=
  match l with
  | nil => s
  | x :: l' => Cons x (Str_prepend_list l' s)
  end.

Fact Str_firstn_map [A B : Type] (f : A -> B) (n : nat) (l : Stream A) :
  Str_firstn n (map f l) = List.map f (Str_firstn n l).
Proof.
  revert l. induction n; intros; simpl; auto.
  destruct l as (x, l). simpl. now rewrite IHn.
Qed.

Fact Str_prepend_list_map [A B : Type] (f : A -> B) (l : list A) (s : Stream A) :
  Str_prepend_list (List.map f l) (map f s) = map f (Str_prepend_list l s).
Proof. induction l; simpl; auto. now rewrite IHl, map_Cons. Qed.

Fact Str_firstn_prepend [T : Type] (n : nat) (l : Stream T) :
  Str_prepend_list (Str_firstn n l) (Str_nth_tl n l) = l.
Proof.
  revert l. induction n; intros; simpl; auto.
  destruct l as (x, l). simpl. congruence.
Qed.

Corollary Str_firstn_prepend' [T : Type] (n1 n2 : nat) (l : Stream T) :
  Str_prepend_list (Str_firstn n1 (Str_nth_tl n2 l)) (Str_nth_tl (n1 + n2) l) = Str_nth_tl n2 l.
Proof. erewrite <- Str_firstn_prepend. now rewrite Str_nth_tl_plus. Qed.

End Stream_Ext.

(* probably people are more familiar with counting, instead of coinduction? *)

Section Adaptor.

(* seems like stepmap is not necessary for counting; Str_nth_tl is enough? *)
(*
Definition stepmap (T : Type) : Type := nat -> T.

Definition infseq2stepmap [T : Type] (s : infseq T) : stepmap T := 
  fun n => Str_nth n s.
*)
Definition always_n [T : Type] (P : Stream T -> Prop) : Stream T -> Prop :=
  fun l => forall n : nat, P (Str_nth_tl n l).

Definition always_n1 [T : Type] (P : T -> Prop) : Stream T -> Prop :=
  fun l => forall n : nat, P (Str_nth n l).

Fact always_n_always [T : Type] (P : Stream T -> Prop) l :
  always_n P l <-> always P l.
Proof.
  unfold always_n.
  split; intros H.
  - revert l H. cofix IH.
    intros. destruct l as (x, l).
    constructor.
    + specialize (H 0). simpl in H. assumption.
    + apply IH. simpl. intros n. specialize (H (S n)). simpl in H. assumption.
  - intros n. revert l H. induction n; intros.
    + simpl. apply always_now'. assumption.
    + destruct l as (x, l).
      simpl. apply IHn. apply always_tl in H. simpl in H. assumption.
Qed.

Definition eventually_n [T : Type] (P : Stream T -> Prop) : Stream T -> Prop :=
  fun l => exists n : nat, P (Str_nth_tl n l).

Definition eventually_n1 [T : Type] (P : T -> Prop) : Stream T -> Prop :=
  fun l => exists n : nat, P (Str_nth n l).

Fact eventually_n_eventually [T : Type] (P : Stream T -> Prop) l :
  eventually_n P l <-> eventually P l.
Proof.
  unfold eventually_n.
  split; intros H.
  - destruct H as (n & H). 
    revert l H. induction n; intros.
    + simpl in H. now apply E0.
    + destruct l as (x, l). simpl in H.
      apply E_next, IHn. assumption.
  - induction H.
    + now exists 0.
    + destruct IHeventually as (n & ?). now exists (S n).
Qed.

End Adaptor.

Section Temporal_Ext.

Definition leadsto [T : Type] (P Q : Stream T -> Prop) : Stream T -> Prop :=
  always (P ->_ (eventually Q)).

Definition valid [T : Type] (P : Stream T -> Prop) : Prop := forall l, P l.

(* TODO currently, can only do semantic level proof ... *)

Lemma leadsto_trans [T : Type] (P Q R : Stream T -> Prop) :
  valid ((leadsto P Q) ->_ ((leadsto Q R) ->_ (leadsto P R))).
Proof.
  unfold valid, leadsto, impl_tl.
  intros l. rewrite <- ? always_n_always.
  unfold always_n. intros.
  apply H, eventually_n_eventually in H1. destruct H1 as (m & H1).
  rewrite Str_nth_tl_plus in H1. apply H0 in H1.
  rewrite <- eventually_n_eventually in H1 |- *. destruct H1 as (k & H1).
  rewrite Str_nth_tl_plus, Nat.add_assoc in H1.
  exists (k + m). now rewrite Str_nth_tl_plus.
Qed.

End Temporal_Ext.

Notation "P '~~>' Q" := (leadsto P Q) (at level 60, no associativity). 

Notation "'|==' P" := (valid P) (at level 50, no associativity). 