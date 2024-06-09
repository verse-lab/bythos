open Protocols.RB
open Common
open Util
open Configuration.Config

(* instantiating the concrete datatype modules *)
(* doing it here might be easier than doing it in Coq? *)

(* somehow delay the instantiations of everything below, since cluster will only be ready at runtime *)
module Lazymod (A : sig end) = struct

module Peers:JustAList with type t = address = PeersPre

module PL = Playground(Peers)

module A:NetAddr with type coq_Address = Peers.t = PL.A
  (* AddrAsFiniteType3(Peers) *)

module R:Round with type coq_Round = int = RoundPre

module V:Value with type coq_Value = int =
  struct
  
  type coq_Value = int
  let coq_Value_eqdec (v1 : coq_Value) (v2 : coq_Value) = (v1 = v2)
  let coq_Value_inhabitant = 0

  end

module VBFT:(sig
    val value_bft : A.coq_Address -> R.coq_Round -> V.coq_Value
  end) =
  struct

  (* well, just go random ... *)
  let value_bft (a : A.coq_Address) (r : R.coq_Round) =
    Random.int 998244352

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

(* TODO can we automate the string_of derivations for these types?
    neither ppx_import nor ppx_deriving works, since the types are inside a functor *)

let string_of_round (r : R.coq_Round) = string_of_int r

let string_of_value (v : V.coq_Value) = string_of_int v

let string_of_message m =
  let open RBP.RealRBMessageImpl in
  match m with
  | InitialMsg (r, v) -> String.concat "" ["Init ("; string_of_round r; ", "; string_of_round v; ")"]
  | EchoMsg (orig, r, v) -> String.concat "" ["Echo ("; string_of_address orig; ", "; string_of_round r; ", "; string_of_round v; ")"]
  | VoteMsg (orig, r, v) -> String.concat "" ["Vote ("; string_of_address orig; ", "; string_of_round r; ", "; string_of_round v; ")"]

let update_and_send st' pkts st_ref =
  st_ref := st';
  Printf.printf "sending:"; print_newline ();
  List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts;
  Shim.Net.send_all pkts;
  Some (st', pkts)

(* the code below implements the behavior of the node. 
    for a non-faulty node, the behavior refers to how to actually run procInt and procMsg. 
    for a Byzantine node, the behavior can be arbitrary, as long as the node does not terminate. *)

let procInt_wrapper =
  let cur_round = ref 0 in
  let lst_time = ref (-1) in
  let aux st_ref = begin
    let tm = int_of_float (Unix.time ()) in
    if (tm mod 10 = !me_port mod 10) && (tm <> !lst_time)
    then begin
      lst_time := tm;
      cur_round := !cur_round + 1;
      let (st', pkts) = procInt_simpler !st_ref !cur_round in
      update_and_send st' pkts st_ref
    end
    else None
  end in aux

let procMsg_wrapper sender msg st_ref =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  let (st', pkts) = procMsg_simpler !st_ref sender msg in
  update_and_send st' pkts st_ref

(* the function f is basically procMsg_wrapper_wrapper *)
let run a = function
  | 0 ->
    Random.init !me_port;
    let st = ref (RBP.coq_Init a) in
    let loop f = begin
      while true do
        ignore (procInt_wrapper st);
        ignore (f procMsg_wrapper st)
      done
    end in loop
  | _ ->
    (* dead node *)
    let loop f = begin
      while true do () done
    end in loop

end (* Lazymod end *)
