From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Systems Require Export Protocol.
From ABCProtocol.Composition Require Export Types.

From RecordUpdate Require Import RecordUpdate.

(* Seq: Pt1 --> Pt2, unidirection *)

Module Type SeqCompProtocolTrigger (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh).

Parameter trigger_procMsg : Pt1.State -> Pt1.State -> option Pt2.InternalTransition.
Parameter trigger_procInt : Pt1.State -> Pt1.State -> option Pt2.InternalTransition.

End SeqCompProtocolTrigger.

Module SeqCompProtocol (Export A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh) 
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2) <: Protocol.Protocol A CM CPk BTh.

Import BTh CM CPk SCPT.

Definition InternalTransition := Pt1.InternalTransition.

Record State_ :=
  Node {
    st1 : Pt1.State;
    st2 : Pt2.State;
  }.

Global Instance eta : Settable _ := settable! Node <st1; st2>.

Definition State := State_.

Definition Init := fun n => Node (Pt1.Init n) (Pt2.Init n).

Definition procInt st tr :=
  let: (st1', pkts1) := Pt1.procInt st.(st1) tr in
  let: st' := st <| st1 := st1' |> in
  let: pkts := map pkt_inl pkts1 in
  match trigger_procInt st.(st1) st1' with
  | Some tr2 =>
    let: (st2', pkts2) := Pt2.procInt st.(st2) tr2 in
    (st' <| st2 := st2' |>, pkts ++ map pkt_inr pkts2)
  | None => (st', pkts)
  end.

Definition procMsgWithCheck st src msg :=
  match msg with
  | inl m1 =>
    let: (st1', pkts1) := Pt1.procMsgWithCheck st.(st1) src m1 in
    let: st' := st <| st1 := st1' |> in
    let: pkts := map pkt_inl pkts1 in
    match trigger_procMsg st.(st1) st1' with
    | Some tr2 =>
      let: (st2', pkts2) := Pt2.procInt st.(st2) tr2 in
      (st' <| st2 := st2' |>, pkts ++ map pkt_inr pkts2)
    | None => (st', pkts)
    end
  | inr m2 =>
    let: (st2', pkts2) := Pt2.procMsgWithCheck st.(st2) src m2 in
    let: pkts := map pkt_inr pkts2 in
    (st <| st2 := st2' |>, pkts)
  end.

End SeqCompProtocol.
(*
Module SeqCompProtocolImpl (Export A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh) 
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  <: Protocol.Protocol A CM CPk BTh <: SeqCompProtocol A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT.

Include SeqCompProtocol A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT.

End SeqCompProtocolImpl.
*)