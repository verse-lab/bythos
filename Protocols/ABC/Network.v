From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.
From Bythos.Protocols.ABC Require Export Protocol.

Module ACAdversary (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f)
  (ACDT : SimpleACDataTypes A Sn V PPrim TSSPrim) (M : ACMessage A Sn V PPrim TSSPrim ACDT)
  (P0 : SimplePacket A M) 
  (ACP : ACProtocol A Sn V (* VBFT *) BTh PPrim TSSPrim ACDT M P0) 
  (Ns : NetState A M P0 BTh ACP) <: Adversary A M BTh BSett P0 ACP Ns.

Import A V (* VBFT *) BTh BSett ACDT ACDT.P ACDT.TSS M P0 ACP Ns.

(* yes, how about extracting this to be ...? *)
Definition sig_seen_in_history (src : Address) (v : Value) (s : Signature) (pkts : PacketSoup) :=
  exists dst received ls, In (mkP src dst (SubmitMsg v ls s) received) pkts.

Definition cert_correct (psent : PacketSoup) (c : Certificate) :=
  let: (v, nsigs) := c in
  forall n sig, 
    In (n, sig) nsigs ->
    isByz n = false ->
    verify v sig n -> (* this can be expressed in other way *)
    sig_seen_in_history n v sig psent. 

Definition lightsig_seen_in_history (src : Address) (v : Value) (ls : LightSignature) (pkts : PacketSoup) :=
  exists dst received s, In (mkP src dst (SubmitMsg v ls s) received) pkts.

(* safety assumption about light certificates: 
  if the number of Byzantine nodes is not sufficiently large, (* TODO this is the assumption in the paper; is it necessary to have it? *)
  then the light signature is unforgeable *)
Definition lcert_correct (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  let: (v, cs) := lc in
  combined_verify v cs ->
  forall lsigs,
    cs = lightsig_combine lsigs ->
    forall n lsig,
      In lsig lsigs ->
      isByz n = false ->
      light_verify v lsig n ->
      lightsig_seen_in_history n v lsig psent. 

Definition lcert_correct_threshold (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  (num_byz < N - (thres + thres) -> lcert_correct psent lc).

(* a weaker constraint than that provided by cryptographic primitives *)
(* because such values cannot exist, not only cannot be sent *)
Definition byzConstraints (m : Message) (w : SystemState) : Prop :=
  match m with
  | SubmitMsg v lsig sig => True
  | LightConfirmMsg lc => lcert_correct_threshold (packetSoup w) lc
  | ConfirmMsg c => cert_correct (packetSoup w) c
  end.

Fact byz_constraints_SystemState_rel m : SystemState_rel_cong (byzConstraints m).
Proof.
  intros w w' Hrel Hc.
  destruct m as [ | (v, cs) | (v, nsigs) ]; hnf in Hc |- *; auto; 
    repeat progress (intros; saturate_assumptions!; hnf in Hc |- * ).
  - destruct Hc as (? & ? & ? & Hin). apply (proj2 Hrel) in Hin. eauto.
  - destruct Hc as (? & ? & ? & Hin). apply (proj2 Hrel) in Hin. eauto.
Qed.

End ACAdversary.

Module Type ACNetworkType (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f).

Import A V (* VBFT *) BTh BSett.

Module Export ACDT <: SimpleACDataTypes A Sn V PPrim TSSPrim := EmptyModule <+ SimpleACDataTypes A Sn V PPrim TSSPrim.
Module Export M <: MessageType := EmptyModule <+ ACMessage A Sn V PPrim TSSPrim ACDT.
Module Export P0 <: SimplePacket A M := EmptyModule <+ SimplePacket A M.
Module Export ACP <: Protocol A M P0 BTh <: ACProtocol A Sn V (* VBFT *) BTh PPrim TSSPrim ACDT M P0 :=
  EmptyModule <+ ACProtocol A Sn V (* VBFT *) BTh PPrim TSSPrim ACDT M P0.
Module Export Ns <: NetState A M P0 BTh ACP := EmptyModule <+ NetState A M P0 BTh ACP.
Module Export ACAdv <: Adversary A M BTh BSett P0 ACP Ns := ACAdversary A Sn V (* VBFT *) BTh BSett PPrim TSSPrim ACDT M P0 ACP Ns.

Include NetworkImpl A M BTh BSett P0 ACP Ns ACAdv.

End ACNetworkType.
