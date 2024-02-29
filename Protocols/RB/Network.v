From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.RB Require Export Protocol.

Module RBAdversary (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (M : RBMessage A R V)
  (P : SimplePacket A M) 
  (RBP : RBProtocol A R V VBFT BTh M P) 
  (Ns : NetState A M P BTh RBP) <: Adversary A M BTh BSett P RBP Ns.

Import A R V VBFT BTh BSett M P RBP Ns.

Definition byz_constraints (m : Message) (w : World) : Prop :=
  (* no constraint here *)
  True.

End RBAdversary.

Module RBNetwork (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.

(* Module Export BTh <: ClassicByzThreshold A := ClassicByzThresholdImpl A. *)
Module Export M <: MessageType := RBMessageImpl A R V.
Module Export P <: SimplePacket A M := SimplePacketImpl A M.
Module Export PSOp : (* hide implementation *) PacketSoupOperations P := PacketSoupOperationsImpl P.
Module Export RBP <: Protocol A M P BTh <: RBProtocol A R V VBFT BTh M P :=
  RBProtocolImpl A R V VBFT BTh M P.
Module Export Ns <: NetState A M P BTh RBP := NetStateImpl A M P BTh RBP.
Module Export RBAdv <: Adversary A M BTh BSett P RBP Ns := RBAdversary A R V VBFT BTh BSett M P RBP Ns.

Include NetworkImpl A M BTh BSett P PSOp RBP Ns RBAdv.

Record Coh (w : World) : Prop := mkCoh {
  id_coh: forall n, (localState w n).(id) = n;
}.

End RBNetwork.
