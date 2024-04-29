From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Composition Require Export Types.
From ABCProtocol.Protocols.ABC Require Export Types.
From ABCProtocol.Protocols.RB Require Export Types.

(* TODO it seems that if we allow multiple instances of ABC to run at the same time, 
    then it is possible for adversaries to collect signatures from different instances
    and use them in one particular instance.
  in this case, we need to change the protocol a little bit ...
  (1) we only allow one instance of ABC for some (node, round) pair. 
  (2) the value of ABC to be signed becomes the product of instance id and value. 
*)
(*
Module Export SingleRound <: Round.

Definition Round := unit.
Definition Round_eqdec : forall r1 r2 : Round, {r1 = r2} + {r1 <> r2}.
  intros [][]. left. reflexivity.
Qed.

End SingleRound.
*)
Module Type AddrRoundPair (Export A : NetAddr) (Export R : Round).

Parameter arp : Address * Round.

End AddrRoundPair.
