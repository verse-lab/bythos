From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.
From Bythos.Protocols.PB Require Export Protocol.

Module PBAdversary (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (VBFT : ValueBFT A R V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.t0) (* ! *)
  (PBDT : PBDataTypes A R Sn V Pf) (M : PBMessage A R Sn V Pf TSSPrim)
  (P0 : SimplePacket A M) 
  (PBP : PBProtocol A R Sn V Pf VBFT BTh TSSPrim PBDT M P0)
  (Ns : NetState A M P0 BTh PBP) <: Adversary A M BTh BSett P0 PBP Ns.

Import A R V Pf VBFT BTh BSett PBDT M P0 PBP PBP.TSS Ns.

(* TODO need to take care that Round, Value and Proof may contain signatures ... *)

(* well ... *)
Definition byz_constraints (m : Message) (w : World) : Prop := True.

End PBAdversary.

Module PBNetwork (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (VBFT : ValueBFT A R V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.t0) (* ! *)
  (PBDT : PBDataTypes A R Sn V Pf).

Import A R V Pf VBFT BTh BSett PBDT.

Module Export M <: MessageType := PBMessageImpl A R Sn V Pf TSSPrim.
Module Export P0 <: SimplePacket A M := SimplePacketImpl A M.
Module Export PSOp : (* hide implementation *) PacketSoupOperations P0 := PacketSoupOperationsImpl P0.
Module Export PBP <: Protocol A M P0 BTh <: PBProtocol A R Sn V Pf VBFT BTh TSSPrim PBDT M P0 :=
  PBProtocolImpl A R Sn V Pf VBFT BTh TSSPrim PBDT M P0.
Module Export Ns <: NetState A M P0 BTh PBP := NetStateImpl A M P0 BTh PBP.
Module Export PBAdv <: Adversary A M BTh BSett P0 PBP Ns := PBAdversary A R Sn V Pf VBFT BTh BSett TSSPrim PBDT M P0 PBP Ns.

Include NetworkImpl A M BTh BSett P0 PSOp PBP Ns PBAdv.

End PBNetwork.
