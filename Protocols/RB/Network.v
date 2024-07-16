From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.
From Bythos.Protocols.RB Require Export Protocol.

Module RBAdversary (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (M : RBMessage A R V)
  (P : SimplePacket A M) 
  (RBP : RBProtocol A R V VBFT BTh M P) 
  (Ns : NetState A M P BTh RBP) <: Adversary A M BTh BSett P RBP Ns.

Import A R V VBFT BTh BSett M P RBP Ns.

Definition byzConstraints (m : Message) (w : SystemState) : Prop :=
  (* no constraint here, since we assume reliable communication channels *)
  True.

End RBAdversary.

Module Type RBNetworkType (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A).

Import A R V VBFT BTh BSett.

(* Module Export BTh <: ClassicByzThreshold A := ClassicByzThresholdImpl A. *)
Module Export M <: MessageType := EmptyModule <+ RBMessage A R V.
Module Export P <: SimplePacket A M := EmptyModule <+ SimplePacket A M.
Module Export RBP <: Protocol A M P BTh <: RBProtocol A R V VBFT BTh M P :=
  EmptyModule <+ RBProtocol A R V VBFT BTh M P.
Module Export Ns <: NetState A M P BTh RBP := EmptyModule <+ NetState A M P BTh RBP.
Module Export RBAdv <: Adversary A M BTh BSett P RBP Ns := RBAdversary A R V VBFT BTh BSett M P RBP Ns.

Include NetworkImpl A M BTh BSett P RBP Ns RBAdv.

End RBNetworkType.
