From Coq Require Export Lia List.

Module Type NetAddr.

(* how about simply letting addr be a number within some range? any other things to notice here? *)
(* TODO relate this with Byzantine assumption *)

Definition Address := nat. 
Definition Address_eqdec := PeanoNat.Nat.eq_dec.

Parameter is_byz : Address -> bool.
Parameter valid_nodes : list Address.

Definition N := length valid_nodes.
Parameter t0 : nat.
Definition valid_node n := In n valid_nodes.

Axiom at_least_two_honest : exists n1 n2, 
  n1 <> n2 /\ 
  valid_node n1 /\
  valid_node n2 /\
  is_byz n1 = false /\ is_byz n2 = false.

(* Parameter n : nat. *)
(* Definition Address := 'I_n. *)

End NetAddr.
