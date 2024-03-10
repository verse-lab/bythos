From Coq Require Import Lia List.
From ABCProtocol.Utils Require Export Tactics.

Module Type NetAddr.

Parameter Address : Set.
Parameter Address_eqdec : forall (a1 a2 : Address), {a1 = a2} + {a1 <> a2}.
Parameter Address_inhabitant : Address.

(* restricting Address to be a finite type should be enough *)
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
Definition Address_inhabitant : Fin.t 5 := Fin.F1.

Definition valid_nodes := enum (fin 5).
Lemma valid_nodes_NoDup : List.NoDup valid_nodes.
Proof. apply NoDup_ListNoDup. exact (NoDup_enum (fin 5)). Qed.
Lemma Address_is_finite : forall a : Address, In a valid_nodes.
Proof. setoid_rewrite <- elem_of_list_In. exact elem_of_enum. Qed.

Definition N := length valid_nodes.

End AddrAsFiniteType.
