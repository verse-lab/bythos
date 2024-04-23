From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.PB Require Export Protocol.

Module PBAdversary (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS) (M : PBMessage A R Sn V Pf TSS)
  (P0 : SimplePacket A M) 
  (PBP : PBProtocol A R Sn V Pf VBFT BTh TSS0 TSS PBDT M P0)
  (Ns : NetState A M P0 BTh PBP) <: Adversary A M BTh BSett P0 PBP Ns.

Import A R V Pf VBFT BTh BSett TSS PBDT M P0 PBP Ns.

(* TODO need to take care that Round, Value and Proof may contain light signatures ... *)
(* not sure what to constrain for now ... skip *)

Definition byz_constraints (m : Message) (w : World) : Prop :=
  match m with
  | EchoMsg _ lsig => True
  | _ => True
  end.

End PBAdversary.

Module PBNetwork (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS).

Import A R V Pf VBFT BTh BSett TSS PBDT.

Module Export M <: MessageType := PBMessageImpl A R Sn V Pf TSS.
Module Export P0 <: SimplePacket A M := SimplePacketImpl A M.
Module Export PSOp : (* hide implementation *) PacketSoupOperations P0 := PacketSoupOperationsImpl P0.
Module Export PBP <: Protocol A M P0 BTh <: PBProtocol A R Sn V Pf VBFT BTh TSS0 TSS PBDT M P0 :=
  PBProtocolImpl A R Sn V Pf VBFT BTh TSS0 TSS PBDT M P0.
Module Export Ns <: NetState A M P0 BTh PBP := NetStateImpl A M P0 BTh PBP.
Module Export PBAdv <: Adversary A M BTh BSett P0 PBP Ns := PBAdversary A R Sn V Pf VBFT BTh BSett TSS0 TSS PBDT M P0 PBP Ns.

Include NetworkImpl A M BTh BSett P0 PSOp PBP Ns PBAdv.

End PBNetwork.
