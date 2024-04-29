From Coq Require Import List Bool Lia ListSet Permutation PeanoNat.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.

Module Liveness (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr)
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P PSOp Pr Ns Adv).

Definition pkts_multi_to_all size w nonbyz_senders pkts (m : Address -> Message) (P : World -> Address -> Prop) : Prop :=
  List.NoDup nonbyz_senders /\
  size <= length nonbyz_senders /\
  incl pkts (sentMsgs w) /\
  Forall good_packet pkts /\ (* since pkts is under-specified *)
  (forall n1,
    In n1 nonbyz_senders -> 
    is_byz n1 = false /\
    P w n1 /\
    (forall n2, is_byz n2 = false ->
      exists used, In (mkP n1 n2 (m n1) used) pkts)).

Definition mutual_receiving m w' :=
  forall n1, is_byz n1 = false -> 
    forall n2, is_byz n2 = false ->
      In (mkP n1 n2 (m n1) true) (sentMsgs w').

End Liveness.

