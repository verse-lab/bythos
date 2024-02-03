From Coq Require Import Lia List.
From Coq Require ssrbool.
Import (coercions) ssrbool.

Module Type NetAddr.

Parameter Address : Set.
Parameter Address_eqdec : forall (a1 a2 : Address), {a1 = a2} + {a1 <> a2}.

(* restricting Address to be a finite type should be enough *)
Parameter valid_nodes : list Address.
Axiom valid_nodes_NoDup : NoDup valid_nodes.
Axiom Address_is_finite : forall a : Address, In a valid_nodes.

Definition N := length valid_nodes.

Parameter is_byz : Address -> bool.

Definition num_byz := length (List.filter is_byz valid_nodes).

(* t0: the threshold, indicating the maximum number of tolerable Byzantine nodes *)
(* we do not assume the  *)
Parameter t0 : nat.

Axiom t0_lt_N : t0 < N.

(* FIXME: trick? instead of stating that valid_nodes is not empty, exploit the fact that 0 < N *)
Definition Address_inhabitant : Address.
  destruct valid_nodes as [ | n ? ] eqn:E.
  2: exact n.
  assert (N = 0) as EN by (unfold N; now rewrite -> E).
  pose proof t0_lt_N.
  rewrite EN in H.
  now exfalso.
Qed.

(*
Definition valid_node n := In n valid_nodes.
Definition is_valid_node n := In_dec Address_eqdec n valid_nodes.

Axiom byz_is_valid : forall n, is_byz n -> valid_node n.
*)

(* this is not used. *)
(*
Axiom at_least_two_honest : exists n1 n2, 
  n1 <> n2 /\ 
  valid_node n1 /\
  valid_node n2 /\
  is_byz n1 = false /\ is_byz n2 = false.
*)

End NetAddr.

(* a simple example *)
(* FIXME: seems like encountered a Coq bug? *)
(*
Module RealAddr <: NetAddr.

From stdpp Require Import finite fin.

Definition Address := fin 5.
Definition Address_eqdec := @fin_dec 5.
Definition valid_nodes := enum (fin 5).
Lemma valid_nodes_NoDup : NoDup valid_nodes.
Proof NoDup_enum (fin 5).
Lemma Address_is_finite : forall a : Address, In a valid_nodes.
Proof. setoid_rewrite <- elem_of_list_In. exact elem_of_enum. Qed.

Definition is_byz : Address -> bool := fun _ => false.
Definition t0 := 2.

Definition N := length valid_nodes.
Definition num_byz := length (List.filter is_byz valid_nodes).

Fact t0_lt_N : t0 < N.
Proof. unfold N, valid_nodes, t0. fold (card (fin 5)). rewrite fin_card. auto. Qed.

End RealAddr.
*)
