From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Systems Require Export Protocol.
From Bythos.Composition Require Export Types.

From RecordUpdate Require Import RecordUpdate.

(* Seq: Pt1 --> Pt2, unidirection *)
(* since the two protocols will run in the same environment, make their BTh the same *)
Module Type SeqCompProtocolTrigger (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh).

(* trigger: check whether Pt2.procInt should be triggered after Pt1.procInt/Pt1.procMsg, 
    based on the change of the local state for Pt1 *)
Parameter trigger_procMsg : Pt1.State (* old local state *) -> Pt1.State (* new local state *) -> option Pt2.InternalEvent.
Parameter trigger_procInt : Pt1.State -> Pt1.State -> option Pt2.InternalEvent.

End SeqCompProtocolTrigger.

Module Type SeqCompProtocol (Export A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh) 
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2) <: Protocol.Protocol A CM CPk BTh.

Import BTh CM CPk SCPT.

Definition InternalEvent := Pt1.InternalEvent.

Record State_ :=
  Node {
    st1 : Pt1.State;
    st2 : Pt2.State;
  }.

Global Instance eta : Settable _ := settable! Node <st1; st2>.

Definition State := State_.

Definition initState := fun n => Node (Pt1.initState n) (Pt2.initState n).

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

Definition procMsg st src msg :=
  match msg with
  | inl m1 =>
    let: (st1', pkts1) := Pt1.procMsg st.(st1) src m1 in
    let: st' := st <| st1 := st1' |> in
    let: pkts := map pkt_inl pkts1 in
    match trigger_procMsg st.(st1) st1' with
    | Some tr2 =>
      let: (st2', pkts2) := Pt2.procInt st.(st2) tr2 in
      (st' <| st2 := st2' |>, pkts ++ map pkt_inr pkts2)
    | None => (st', pkts)
    end
  | inr m2 =>
    let: (st2', pkts2) := Pt2.procMsg st.(st2) src m2 in
    let: pkts := map pkt_inr pkts2 in
    (st <| st2 := st2' |>, pkts)
  end.

End SeqCompProtocol.
