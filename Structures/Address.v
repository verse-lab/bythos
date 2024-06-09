From Coq Require Import Lia List.
From Bythos.Utils Require Export Tactics ListFacts Misc.
From Bythos.Utils Require Fintype.

Module Type NetAddr.

Parameter Address : Set.
Parameter Address_eqdec : forall (a1 a2 : Address), {a1 = a2} + {a1 <> a2}.
Parameter Address_inhabitant : Address.

(* restricting Address to be a finite type should be enough *)
(* the Finite typeclass defined in stdpp could be used, but since the development mostly
    uses the definitions in the Coq standard library (e.g., List.NoDup), so did not do that *)
Parameter valid_nodes : list Address.
Axiom valid_nodes_NoDup : NoDup valid_nodes.
Axiom Address_is_finite : forall a : Address, In a valid_nodes.

Definition N := length valid_nodes.

End NetAddr.

(* a simple example, using the finite type in stdpp *)

Require stdpp.finite stdpp.fin.

Module AddrAsFiniteType <: NetAddr.

Import finite fin.

Definition Address := fin 5.
Definition Address_eqdec := @fin_dec 5.
Definition Address_inhabitant : Address := Fin.F1.

Definition valid_nodes := enum (fin 5).
Lemma valid_nodes_NoDup : List.NoDup valid_nodes.
Proof. apply NoDup_ListNoDup. exact (NoDup_enum (fin 5)). Qed.
Lemma Address_is_finite : forall a : Address, In a valid_nodes.
Proof. setoid_rewrite <- elem_of_list_In. exact elem_of_enum. Qed.

Definition N := length valid_nodes.

End AddrAsFiniteType.

(* another definition, in the subtype-like form *)

Module AddrAsFiniteType2 <: NetAddr.

Export Fintype.

Global Instance fin_nat_decision n : base.EqDecision (fin_nat n) := @fin_nat_eqdec n.
Global Program Instance fin_nat_finite n : finite.Finite (fin_nat n) :=
  {| finite.enum := fin_nat_enum n |}.
Next Obligation. intros n. apply base.NoDup_ListNoDup, fin_nat_enum_NoDup. Qed.
Next Obligation. intros n a. apply base.elem_of_list_In, fin_nat_enum_complete. Qed.

(* after extraction, it will become just natural number pairs *)
Definition Address := prod (fin_nat 5) (fin_nat 5).
Definition Address_eqdec := prod_eq_dec (@fin_nat_eqdec 5) (@fin_nat_eqdec 5).
Definition Address_inhabitant : Address := (FT 5 0 I, FT 5 0 I).

(* implicitly involving the instance of building Finite for products *)
Definition valid_nodes : list Address := finite.enum Address.
Lemma valid_nodes_NoDup : List.NoDup valid_nodes.
Proof. apply base.NoDup_ListNoDup, finite.NoDup_enum. Qed.
Lemma Address_is_finite : forall a : Address, In a valid_nodes.
Proof. intros ?. apply base.elem_of_list_In, finite.elem_of_enum. Qed.

Definition N := length valid_nodes.

End AddrAsFiniteType2.

(* the module above seems not to be the best for extraction work ... 
    it involves some constructions in stdpp (e.g., Finite), which may result in the occurrences of 
    weird things like Obj.magic *)

(* JustAList: serving as a uniform interface to instantiate a NetAddr module with just a list *)
(* here, remove the NoDup constraint since we cannot check it after extraction *)
Module Type JustAList.

Parameter t : Set.
Parameter t_eqdec : forall a b : t, {a = b} + {a <> b}.

(* elements may not be determined until some point, so model it into a function *)
Parameter elements : unit -> list t.
Parameter elements_not_empty : elements tt <> nil.

End JustAList.

Module AddrAsFiniteType3 (A : JustAList) <: NetAddr.

Export Fintype.

Local Notation elts := (List.nodup A.t_eqdec (A.elements tt)).
Local Notation fin_mem := (fin_mem A.t_eqdec elts).

Definition Address := fin_mem.
Definition Address_eqdec := @fin_mem_eqdec _ A.t_eqdec elts.
Definition Address_inhabitant : Address.
  pose proof A.elements_not_empty as H. set (l:=A.elements tt). destruct l as [ | a ? ] eqn:E; try contradiction.
  eapply FM with (a:=a). unfold ssrbool.is_left. rewrite (proj2 (sumbool_is_left _)); hnf; auto. apply nodup_In. subst l. rewrite E. simpl. auto.
Qed.

Definition valid_nodes : list Address := fin_mem_lift elts (fin_mem_lift_qualified _ (incl_refl _)).
Lemma valid_nodes_NoDup : List.NoDup valid_nodes.
Proof. apply fin_mem_lift_NoDup, NoDup_nodup. Qed.
Lemma Address_is_finite : forall a : Address, In a valid_nodes.
Proof. 
  intros [ ? H ]. pose proof H as H0%isTrue_true_iff%sumbool_is_left. 
  apply fin_mem_in. simpl. unfold valid_nodes. now rewrite fin_mem_lift_peel.
Qed.

Definition N := length valid_nodes.

End AddrAsFiniteType3.
