From Coq Require Import List Bool Lia ListSet Permutation PeanoNat.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.

Module Liveness (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr)
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P Pr Ns Adv).

(* some definitions that might be useful in liveness proofs *)

Definition pkts_multi_to_all size w nonbyz_senders pkts (m : Address -> Message) (P : SystemState -> Address -> Prop) : Prop :=
  List.NoDup nonbyz_senders /\
  size <= length nonbyz_senders /\
  incl pkts (packetSoup w) /\
  Forall goodPkt pkts /\ (* since pkts is under-specified *)
  (forall n1,
    In n1 nonbyz_senders -> 
    isByz n1 = false /\
    P w n1 /\
    (forall n2, isByz n2 = false ->
      exists used, In (mkP n1 n2 (m n1) used) pkts)).

Definition mutual_receiving m w' :=
  forall n1, isByz n1 = false -> 
    forall n2, isByz n2 = false ->
      In (mkP n1 n2 (m n1) true) (packetSoup w').

End Liveness.

