From Coq Require Import Bool List PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Systems Require Export Protocol.
From ABCProtocol.Protocols.RBABC Require Export Types.
From ABCProtocol.Protocols.ABC Require Import Protocol.
From ABCProtocol.Protocols.RB Require Import Protocol.

From RecordUpdate Require Import RecordUpdate.

Module Type RBACProtocol (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (RBM : RBMessage A R V)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (ACM : ACMessage A Sn V P TSS ACDT)
  (M : RBACMessage A R Sn V P TSS ACDT RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh P TSS0 TSS ACDT CC ACM ACPk)
  (Pk : SimplePacket A M) <: Protocol A M Pk BTh.

Import A R V VBFT BTh P TSS ACDT CC M Pk.

(* TODO this should be generic? *)
Definition pkt_inl (p : RBPk.Packet) : Packet :=
  mkP (RBPk.src p) (RBPk.dst p) (inl (RBPk.msg p)) (RBPk.consumed p).

Definition pkt_inr (ar : Address * Round) (p : ACPk.Packet) : Packet :=
  mkP (ACPk.src p) (ACPk.dst p) (inr (ar, ACPk.msg p)) (ACPk.consumed p).

Definition InternalTransition := RBP.InternalTransition.

Record State_ :=
  Node {
    stRB : RBP.State;
    stAC : Address * Round -> ACP.State;
  }.

#[export] Instance eta : Settable _ := settable! Node <stRB; stAC>.

Definition State := State_.

Definition Init (n : Address) : State := Node (RBP.Init n) (fun _ => ACP.Init n).

Definition procInt (st : State) (tr : InternalTransition) : State * list Packet :=
  let: (st', pkts) := RBP.procInt st.(stRB) tr in (st <| stRB := st' |>, map pkt_inl pkts).

Definition triggered (st st' : RBP.State) (mRB : RBM.Message) : option (Address * Round * Value) :=
  match mRB with
  | RBM.VoteMsg q r _ =>
    match (st.(RBP.output) (q, r)), (st'.(RBP.output) (q, r)) with
    | nil, nil => None
    | _ :: _, _ => None
    | nil, v :: _ => Some (q, r, v)
    end
  | _ => None
  end.

Definition procMsgWithCheck (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match msg with
  | inl mRB =>
    let: (stRB', pktsRB) := RBP.procMsgWithCheck st.(stRB) src mRB in
    let: st' := st <| stRB := stRB' |> in
    let: pkts := map pkt_inl pktsRB in
    match triggered st.(stRB) stRB' mRB with
    | Some (q, r, v) =>
      let: (stAC', pktsAC) := ACP.procInt (st.(stAC) (q, r)) (ACP.SubmitIntTrans v) in
      (st' <| stAC := map_update RBP.AddrRdPair_eqdec (q, r) stAC' st.(stAC) |>, pkts ++ map (pkt_inr (q, r)) pktsAC)
    | None => (st', pkts)
    end
  | inr (ar, mAC) =>
    let: (stAC', pktsAC) := ACP.procMsgWithCheck (st.(stAC) ar) src mAC in
    let: pkts := map (pkt_inr ar) pktsAC in
    (st <| stAC := map_update RBP.AddrRdPair_eqdec ar stAC' st.(stAC) |>, pkts)
  end.

End RBACProtocol.

Module RBACProtocolImpl (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (RBM : RBMessage A R V)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (ACM : ACMessage A Sn V P TSS ACDT)
  (M : RBACMessage A R Sn V P TSS ACDT RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh P TSS0 TSS ACDT CC ACM ACPk)
  (Pk : SimplePacket A M) <: Protocol A M Pk BTh
  <: RBACProtocol A R Sn V VBFT BTh RBM P TSS0 TSS ACDT CC ACM M RBPk ACPk RBP ACP Pk.

Include RBACProtocol A R Sn V VBFT BTh RBM P TSS0 TSS ACDT CC ACM M RBPk ACPk RBP ACP Pk.

End RBACProtocolImpl.
