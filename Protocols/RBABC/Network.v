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

(* instantiate inside *)
Module ACAdv := ACAdversary A Sn V BTh BSett P TSS0 TSS ACDT CC ACM ACPk ACP ACNs.

Definition byz_constraints (m : Message) (w : World) : Prop :=
  match m with
  | inl mRB => True
  | inr mAC => ACAdv.byz_constraints mAC (ACNs.mkW (ACNs.localState ACNs.initWorld) (* this part does not contribute *)
    (pkts_filter_proj2 (sentMsgs w)))
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

(* auxiliary operations *)
Definition stmap_proj1 (stmap : StateMap) : RBN.Ns.StateMap :=
  fun n => (stmap n).(stRB).

Definition stmap_proj2 (stmap : StateMap) : ACN.Ns.StateMap :=
  fun n => (stmap n).(stAC).

Definition world_proj1 (w : World) : RBN.Ns.World :=
  RBN.Ns.mkW (stmap_proj1 (localState w)) (pkts_filter_proj1 (sentMsgs w)).

Definition world_proj2 (w : World) : ACN.Ns.World :=
  ACN.Ns.mkW (stmap_proj2 (localState w)) (pkts_filter_proj2 (sentMsgs w)).

Definition ssd_proj1 (q : system_step_descriptor) : RBN.system_step_descriptor :=
  match q with
  | Idle => RBN.Idle
  | Deliver p =>
    match pkt_proj1 p with
    | Some res => RBN.Deliver res
    | _ => RBN.Idle
    end
  | Intern n r => RBN.Intern n r
  | Byz src dst m =>
    match m with
    | inl mRB => RBN.Byz src dst mRB
    | _ => RBN.Idle
    end
  end.

(* depending on the previous protocol *)
Definition ssd_proj2 (q : system_step_descriptor) (w w' : RBN.Ns.World) : ACN.system_step_descriptor :=
  match q with
  | Idle => ACN.Idle
  | Deliver p =>
    match pkt_proj2 p with
    | Some res => ACN.Deliver res
    | _ =>
      (* HMM *)
      let: n := p.(dst) in
      match triggered (RBN.Ns.localState w n) (RBN.Ns.localState w' n) with
      | Some v => ACN.Intern n (ACN.ACP.SubmitIntTrans v)
      | _ => ACN.Idle
      end
    end
  | Intern _ _ => ACN.Idle
  | Byz src dst m =>
    match m with
    | inr mAC => ACN.Byz src dst mAC
    | _ => ACN.Idle
    end
  end.

End RBACNetwork.
