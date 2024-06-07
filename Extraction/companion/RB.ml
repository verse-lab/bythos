open Protocols.RB
open Common
open Util
open Configuration.Config

(* instantiating the concrete datatype modules *)
(* doing it here might be easier than doing it in Coq? *)

module Peers:JustAList with type t = address = PeersPre

module PL = Playground(Peers)

module A:NetAddr with type coq_Address = Peers.t = PL.A
  (* AddrAsFiniteType3(Peers) *)

module R:Round with type coq_Round = int = RoundPre

module V:Value with type coq_Value = int * int =
  struct
  
  type coq_Value = int * int
  let coq_Value_eqdec (v1 : coq_Value) (v2 : coq_Value) = (v1 = v2)
  let coq_Value_inhabitant = (0, 0)

  end

module VBFT:(sig
    val value_bft : A.coq_Address -> R.coq_Round -> V.coq_Value
  end) =
  struct

  (* simply reporting node ID and which round *)
  let value_bft (a : A.coq_Address) (r : R.coq_Round) =
    let i = list_index a (Peers.elements ()) in
    (i + 1, r)

  end

module RBP = PL.RealRBProtocolImpl(R)(V)(VBFT)

(* TODO unfortunately, the boilerplate code below seems hard to eliminate ... *)
let packet_simplify p =
  let open RBP.RealSimplePacketImpl in
  (p.dst, p.msg)

let procInt_simpler st itr = 
  let (st', pkts) = RBP.procInt st itr in
  (st', List.map packet_simplify pkts)

let procMsg_simpler st src msg = 
  let (st', pkts) = RBP.procMsgWithCheck st src msg in
  (st', List.map packet_simplify pkts)

let get_minimal_protocol a = {
  st = RBP.coq_Init a;
  procInt = procInt_simpler;
  procMsg = procMsg_simpler
} 

type protocol_RB = (RBP.coq_State, RBP.RealRBMessageImpl.coq_Message, 
  RBP.coq_InternalTransition, address) minimal_protocol

let procInt_wrapper =
  let cur_round = ref 0 in
  let aux (pr : protocol_RB) = begin
    let tm = int_of_float (Unix.time ()) in
    if tm mod 10 = !me_port mod 10 
    then begin
      cur_round := !cur_round + 1;
      let (st', pkts) = pr.procInt pr.st !cur_round in
      pr.st <- st';
      Shim.Net.send_all pkts;
      Some (st', pkts)
    end
    else None
  end in aux

let procMsg_wrapper (sender : address) (msg : RBP.RealRBMessageImpl.coq_Message) (pr : protocol_RB) =
  let (st', pkts) = pr.procMsg pr.st sender msg in
  (* FIXME: this subprocedure can be made into a function *)
  pr.st <- st';
  Shim.Net.send_all pkts;
  Some (st', pkts)

type aaaaa = RBP.RealRBMessageImpl.coq_Message
[@@deriving show]
