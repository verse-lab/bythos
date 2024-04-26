From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.RBABC Require Export Protocol.
From ABCProtocol.Protocols.ABC Require Import Network.
From ABCProtocol.Protocols.RB Require Import Network.

Module RBACAdversary (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (RBM : RBMessage A R V)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (ACM : ACMessage A Sn V P TSS ACDT)
  (M : RBACMessage A R Sn V P TSS ACDT RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh P TSS0 TSS ACDT CC ACM ACPk)
  (Pk : SimplePacket A M)
  (RBACP : RBACProtocol A R ARP Sn V VBFT BTh RBM P TSS0 TSS ACDT CC ACM M RBPk ACPk RBP ACP Pk)
  (RBNs : NetState A RBM RBPk BTh RBP) (ACNs : NetState A ACM ACPk BTh ACP) 
  (Ns : NetState A M Pk BTh RBACP) <: Adversary A M BTh BSett Pk RBACP Ns.

Import A R ARP V VBFT BTh P TSS0 TSS ACDT CC M Pk RBACP Ns.

(* auxiliary operations *)
Definition stmap_inl (stmap : StateMap) : RBNs.StateMap :=
  fun n => (stmap n).(stRB).

Definition stmap_inr (stmap : StateMap) : ACNs.StateMap :=
  fun n => (stmap n).(stAC).

Definition world_inl (w : World) : RBNs.World :=
  RBNs.mkW (stmap_inl (localState w)) (pkts_filter_inl (sentMsgs w)).

Definition world_inr (w : World) : ACNs.World :=
  ACNs.mkW (stmap_inr (localState w)) (pkts_filter_inr (sentMsgs w)).

(* instantiate inside *)
Module ACAdv := ACAdversary A Sn V BTh BSett P TSS0 TSS ACDT CC ACM ACPk ACP ACNs.

Definition byz_constraints (m : Message) (w : World) : Prop :=
  match m with
  | inl mRB => True
  | inr mAC => ACAdv.byz_constraints mAC (ACNs.mkW (ACNs.localState ACNs.initWorld) (* this part does not contribute *)
    (pkts_filter_inr (sentMsgs w)))
  end.

End RBACAdversary.

Module RBACNetwork (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0).

Import A R ARP V VBFT BTh BSett P TSS0 TSS.

Module RBN := RBNetwork A R V VBFT BTh BSett.
Module ACN := ACNetwork A Sn V BTh BSett P TSS0 TSS.

Module Export M <: MessageType := RBACMessageImpl A R Sn V P TSS ACN.ACDT RBN.M ACN.M.
Module Export Pk <: SimplePacket A M := SimplePacketImpl A M.
Module Export PSOp : (* hide implementation *) PacketSoupOperations Pk := PacketSoupOperationsImpl Pk.
Module Export RBACP <: Protocol A M Pk BTh
  <: RBACProtocol A R ARP Sn V VBFT BTh RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk
  := RBACProtocolImpl A R ARP Sn V VBFT BTh RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk.
Module Export Ns <: NetState A M Pk BTh RBACP := NetStateImpl A M Pk BTh RBACP.
Module Export RBACAdv <: Adversary A M BTh BSett Pk RBACP Ns :=
  RBACAdversary A R ARP Sn V VBFT BTh BSett RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk
    RBACP RBN.Ns ACN.Ns Ns.

Include NetworkImpl A M BTh BSett Pk PSOp RBACP Ns RBACAdv.

End RBACNetwork.
