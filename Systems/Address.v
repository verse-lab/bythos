From Coq Require Import Lia List ssrbool.

Module Type NetAddr.

(* TODO a better approach is to make Address a finite type; lists are awkward here *)

(* how about simply letting addr be a number within some range? any other things to notice here? *)
(* TODO relate this with Byzantine assumption *)

Parameter Address : Set. 
Parameter Address_eqdec : forall (a1 a2 : Address), {a1 = a2} + {a1 <> a2}.

Parameter is_byz : Address -> bool.
Parameter valid_nodes : list Address.

Definition N := length valid_nodes.
Parameter t0 : nat.

Axiom t0_lt_N : t0 < N.

(* FIXME: trick *)
Definition Address_inhabitant : Address.
  destruct valid_nodes as [ | n ? ] eqn:E.
  2: exact n.
  assert (N = 0) as EN by (unfold N; now rewrite -> E).
  pose proof t0_lt_N.
  lia.
Qed.

(* TODO if we want properties about quorum, we need to quantify t0 here *)

Definition valid_node n := In n valid_nodes.

Axiom byz_is_valid : forall n, is_byz n -> valid_node n.

(* this is not used. *)
Axiom at_least_two_honest : exists n1 n2, 
  n1 <> n2 /\ 
  valid_node n1 /\
  valid_node n2 /\
  is_byz n1 = false /\ is_byz n2 = false.

(* Parameter n : nat. *)
(* Definition Address := 'I_n. *)

End NetAddr.
