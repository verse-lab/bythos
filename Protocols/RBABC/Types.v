From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Protocols.ABC Require Export Types.
From Bythos.Protocols.RB Require Export Types.

(* TODO it seems that if we allow multiple instances of ABC to run at the same time, 
    then it is possible for adversaries to collect signatures from different instances
    and use them in one particular instance.
  in this case, we need to change the protocol a little bit ...
  choose either:
  (1) we only allow one instance of ABC for some (node, round) pair. 
  (2) the value of ABC to be signed becomes the product of instance id and value. 
*)

Module Type AddrRoundPair (Export A : NetAddr) (Export R : Round).

Parameter arp : Address * Round.

End AddrRoundPair.
