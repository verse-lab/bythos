From ABCProtocol Require Import Types Address Protocol.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NetState (A : NetAddr) (T : Types A) (AC : ACProtocol A T).
Import A T AC.

(* using a map library seems to be overkill *)
(* FIXME: make this total or partial? maybe we should only represent the states of non-Byzantine nodes *)

Definition StateMap := Address -> State. 
Definition initState := (fun n => Init n).

Definition upd (n : Address) (st : State) (states : StateMap) : StateMap :=
  fun m => if Address_eqdec n m then st else states m.

End NetState.
