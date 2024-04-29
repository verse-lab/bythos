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

Definition byz_constraints (m : Message) (w : World) : Prop :=
  (* no constraint here, since we assume reliable communication channels *)
  True.

End RBAdversary.

Module Type RBNetworkType (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A).

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
(*
Definition lift_node_coh_ (P : State -> Prop) : PacketSoup -> State -> Prop :=
  fun _ st => P st.

Definition lift_node_inv (P : PacketSoup -> State -> Prop) : World -> Prop :=
  fun w => forall n, is_byz n = false ->
    P (sentMsgs w) (localState w n).

Definition lift_node_coh (P : State -> Prop) : World -> Prop :=
  Eval unfold lift_node_inv, lift_node_coh_ in lift_node_inv (lift_node_coh_ P).

Definition lift_psent_inv_ (P : StateMap -> PacketSoup -> PacketSoup -> Prop)
  : StateMap -> PacketSoup -> Prop :=
  fun stmap psent => P stmap psent psent.

Definition lift_psent_inv (P : StateMap -> PacketSoup -> PacketSoup -> Prop)
  : World -> Prop :=
  Eval unfold lift_psent_inv_ in fun w => lift_psent_inv_ P (localState w) (sentMsgs w).

Definition id_coh w : Prop := 
  forall n, is_byz n = false -> (localState w n).(id) = n.
*)
End RBNetworkType.

Module RBNetwork (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A) <: RBNetworkType A R V VBFT BTh BSett.

Include RBNetworkType A R V VBFT BTh BSett.

End RBNetwork.
