From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.ABC Require Export Protocol.

Module ACAdversary (A : NetAddr) (V : Signable) (VBFT : ValueBFT A V) 
  (P : PKI A V) (TSS : ThresholdSignatureScheme A V)
  (ACDT : ACDataTypes A V P TSS) 
  (CC : CertCheckers A V P TSS ACDT) (M : ACMessage A V P TSS ACDT)
  (P0 : SimplePacket A M) 
  (ACP : ACProtocol A V VBFT P TSS ACDT CC M P0) 
  (Ns : NetState A M P0 ACP) <: Adversary A M P0 ACP Ns.

Import A V VBFT P TSS ACDT CC M P0 ACP Ns.

(* yes, how about extracting this to be ...? *)
Definition sig_seen_in_history (src : Address) (v : Value) (s : Signature) (pkts : PacketSoup) :=
  exists dst consumed ls, In (mkP src dst (SubmitMsg v ls s) consumed) pkts.

Definition cert_correct (psent : PacketSoup) (c : Certificate) :=
  let: (v, nsigs) := c in
  forall n sig, 
    In (n, sig) nsigs ->
    is_byz n = false ->
    verify v sig n -> (* this can be expressed in other way *)
    sig_seen_in_history n v sig psent. 

(* TODO the lightsig can actually be obtained from full certificates?
  guess this will not affect the following reasoning 
  (since full certificates are assembled from the sent messages), 
  so ignore it for now *)
Definition lightsig_seen_in_history (src : Address) (v : Value) (ls : LightSignature) (pkts : PacketSoup) :=
  exists dst consumed s, In (mkP src dst (SubmitMsg v ls s) consumed) pkts.

(* safety assumption about light certificates: 
  if the number of Byzantine nodes is not sufficiently large, 
  then the light signature is unforgeable *)
Definition lcert_correct (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  let: (v, cs) := lc in
  combined_verify v cs ->
  forall lsigs,
    cs = lightsig_combine lsigs ->
    forall n lsig,
      In lsig lsigs ->
      is_byz n = false ->
      light_verify v lsig n ->
      lightsig_seen_in_history n v lsig psent. 

Definition lcert_correct_threshold (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  (num_byz < N - (t0 + t0) -> lcert_correct psent lc).

Definition byz_constraints (m : Message) (w : World) : Prop :=
  match m with
  | SubmitMsg v lsig sig => True
  | LightConfirmMsg lc => lcert_correct_threshold (sentMsgs w) lc
  | ConfirmMsg c => cert_correct (sentMsgs w) c
  end.

End ACAdversary.

Module ACNetwork (A : NetAddr) (V : Signable) (VBFT : ValueBFT A V) 
  (P : PKI A V) (TSS : ThresholdSignatureScheme A V).

Import A V VBFT P TSS.

Module Export ACDT <: ACDataTypes A V P TSS := ACDataTypesImpl A V P TSS.
Module Export CC : (* hide implementation *) CertCheckers A V P TSS ACDT := CertCheckersImpl A V P TSS ACDT.
Module Export M <: MessageType := ACMessageImpl A V P TSS ACDT.
Module Export P0 <: SimplePacket A M := SimplePacketImpl A M.
Module Export ACP <: Protocol A M P0 <: ACProtocol A V VBFT P TSS ACDT CC M P0 :=
  ACProtocolImpl A V VBFT P TSS ACDT CC M P0.
Module Export Ns <: NetState A M P0 ACP := NetStateImpl A M P0 ACP.
Module Export ACAdv <: Adversary A M P0 ACP Ns := ACAdversary A V VBFT P TSS ACDT CC M P0 ACP Ns.

Include NetworkImpl A M P0 ACP Ns ACAdv.

(* tries to pack all coherent props into a record *)
Record Coh (w : World) : Prop := mkCoh {
  id_coh: forall n, (localState w n).(id) = n;
  (* unrelated_intact: forall n, ~ valid_node n -> holds n w (fun st => st = Init n); *)
}.

End ACNetwork.
