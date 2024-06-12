(* FIXME: the protocol is compositional, the companion file should also be compositional *)
(* but it does not typecheck if we use RBcompanion/ACcompanion 
      (for example, the string_of_message cannot be built from the individual ones in RBcompanion/ACcompanion). why?
    guess it is because there are two copies of the same inductive type. 
    maybe one way to eliminate that is by defining the inductive type outside the module? *)

open Protocols.Driver
open Common
open Configuration.Config
open Util

module Lazymod (A : sig end) = struct

module PL = Playground(Peers)

module RBcompanion = RB.Lazymod(struct end)

module ACcompanion = RB.Lazymod(struct end)

let value_bft =
  List.filter_map (fun s -> 
    match String.split_on_char '=' s with
    | [l; r] -> Some (l, r)
    | _ -> None) (String.split_on_char ',' !extrainfo)

module ARP =
  struct

  let arp = (List.assoc "leader" value_bft |> address_of_string, List.assoc "round" value_bft |> int_of_string)

  end

module RBACP = PL.RealRBABCProtocolImpl(IntRound)(ARP)(StringSn)(IntValue)(RBcompanion.VBFT)(PPrim)

let packet_simplify p =
  let open RBACP.CPk in
  (p.dst, p.msg)

let procInt_simpler st itr = 
  let (st', pkts) = RBACP.procInt st itr in
  (st', List.map packet_simplify pkts)

let procMsg_simpler st src msg = 
  let (st', pkts) = RBACP.procMsgWithCheck st src msg in
  (st', List.map packet_simplify pkts)

let string_of_message m =
  let open Protocols.Datatypes in (* well ... *)
  match m with
  | Coq_inl ml -> begin
    (* copied from RB.ml *)
    let open RBACP.RBP.RBM in
    match ml with
    | InitialMsg (r, v) -> String.concat "" ["Init ("; RBcompanion.string_of_round r; ", "; RBcompanion.string_of_value v; ")"]
    | EchoMsg (orig, r, v) -> String.concat "" ["Echo ("; string_of_address orig; ", "; RBcompanion.string_of_round r; ", "; RBcompanion.string_of_value v; ")"]
    | VoteMsg (orig, r, v) -> String.concat "" ["Vote ("; string_of_address orig; ", "; RBcompanion.string_of_round r; ", "; RBcompanion.string_of_value v; ")"]
  end
  | Coq_inr mr -> begin
    (* copied from ABC.ml *)
    let open RBACP.ACP.ACM in
    match mr with
    | SubmitMsg (v, _, _) -> String.concat "" ["Submit ("; ACcompanion.string_of_value v; ", "; "[some light sig]"; ", "; "[some full sig]"; ")"]
    | LightConfirmMsg (v, _) -> String.concat "" ["LightCert ("; ACcompanion.string_of_value v; ", "; "[some combined sig]"; ")"]
    | ConfirmMsg (v, nsigs) -> String.concat "" ["Cert ("; ACcompanion.string_of_value v; ", "; 
        "["; String.concat "; " (List.map (fun (n, _) -> string_of_address n) nsigs); "]"; ")"]
  end

(* copied from RB.ml *)
let update_and_send st' pkts st_ref =
  st_ref := st';
  if pkts <> [] then begin
    Printf.printf "sending:"; print_newline ();
    List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts
  end else ();
  Shim.Net.send_all pkts;
  Some (st', pkts)

(* copied from RB.ml *)
let procInt_wrapper =
  let cur_round = ref 0 in
  let lst_time = ref (-1) in
  let aux st_ref = begin
    let tm = int_of_float (Unix.time ()) in
    if (tm mod 10 = !me_port mod 10) && (tm <> !lst_time)
    then begin
      lst_time := tm;
      incr cur_round;
      let (st', pkts) = procInt_simpler !st_ref !cur_round in
      update_and_send st' pkts st_ref
    end
    else None
  end in aux

(* copied from ABC.ml *)
let check_confirmed (old_st : RBACP.ACP.coq_State) (new_st : RBACP.ACP.coq_State) =
  let open RBACP.ACP in
  if (not old_st.conf) && new_st.conf
  then begin
    match new_st.submitted_value with
    | Some v -> Printf.printf "confirmed value %d" v; print_newline ()
    | _ -> failwith "this should not happen"
  end else ()

(* copied from ABC.ml *)
let check_genproof =
  (* genproof might be expensive to compute, so memorize it *)
  let found_proof = ref false in
  let aux st = begin
    if not (!found_proof) then begin
      let open RBACP.ACP in
      let pf = CC.genproof st.received_certs in
      if pf <> []
      then (found_proof := true; Printf.printf "found culprits: %s" (String.concat "; " (List.map string_of_address pf)); print_newline ())
      else ()
    end else ()
  end in aux

let procMsg_wrapper st_ref sender msg =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  let old_st = !st_ref in
  let (st', pkts) = procMsg_simpler old_st sender msg in
  let open RBACP in
  check_confirmed old_st.st2 st'.st2;
  check_genproof st'.st2;
  update_and_send st' pkts st_ref

(* here, to simplify things, only consider one conspirator, though we can add more *)
let conspirator = Option.map address_of_string (List.assoc_opt "conspirator" value_bft)

let byz_nodes, other_nodes = List.partition (fun s -> (s = (!me_ip, !me_port)) || (Some s = conspirator)) PL.A.valid_nodes

let half1, half2 = list_take_drop other_nodes ((List.length other_nodes) / 2)

let targets1, targets2 = half1 @ byz_nodes, half2 @ byz_nodes

let restricted_receivers : (address list) ref = ref []

(* copied from update_and_send *)
(* non-faulty nodes would do nothing on the packets to be sent, so this can only be used by Byzantine nodes *)
let update_and_send_byz st' pkts_pre st_ref =
  st_ref := st';
  let pkts = List.filter (fun (a, _) -> List.mem a !restricted_receivers) pkts_pre in
  if pkts <> [] then begin
    Printf.printf "sending:"; print_newline ();
    List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts
  end else ();
  Shim.Net.send_all pkts;
  Some (st', pkts)

let procInt_wrapper_byz_double_vote =
  let q1 = lazy (Random.int 10) in
  let q2 = lazy (Random.int 10) in
  let v1 = lazy (List.assoc "value1" value_bft |> int_of_string) in
  let v2 = lazy (List.assoc "value2" value_bft |> int_of_string) in
  let sent1 = ref false in
  let sent2 = ref false in
  let aux st_ref = begin
    let tm = int_of_float (Unix.time ()) in
    let cond = 
      (if (not !sent1) && (tm mod 20 = Lazy.force q1) then 1
      else if (not !sent2) && (tm mod 20 = (Lazy.force q1) + (Lazy.force q2)) then -1 else 0) in
    let ov = 
      (if cond = 1 then (sent1 := true; Some v1) 
      else if cond = -1 then (sent2 := true; Some v2) else None) in
    match ov with
    | Some v -> begin
      let open RBACP in
      let fresh_st = coq_Init (!me_ip, !me_port) in
      let votemsg = RBP.RBM.VoteMsg (fst ARP.arp, snd ARP.arp, Lazy.force v) in
      let msgcnt_with_one = Protocols.ListFacts.map_update RBP.RBM.coq_Message_eqdec votemsg [(!me_ip, !me_port)] (fun _ -> []) in
      st_ref := { fresh_st with st1 = { fresh_st.st1 with RBP.msgcnt = msgcnt_with_one } };
      (* just vote, without any preceding process *)
      (* does not matter if the Byzantine node is not the leader *)
      let pkts = List.map (fun a -> (a, Protocols.Datatypes.Coq_inl votemsg)) (if cond = 1 then half1 else half2) in
      restricted_receivers := (if cond = 1 then targets1 else targets2);
      update_and_send_byz !st_ref pkts st_ref
    end
    | None -> None
  end in aux

(* the same as non-faulty one, except for using update_and_send_byz *)
let procMsg_wrapper_byz st_ref sender msg =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  let old_st = !st_ref in
  let (st', pkts) = procMsg_simpler old_st sender msg in
  let open RBACP in
  check_confirmed old_st.st2 st'.st2;
  check_genproof st'.st2;
  update_and_send_byz st' pkts st_ref

(* copied from PB.ml *)
let run_nonbyz a =
  (* non-faulty *)
  Random.init !me_port;
  let st = ref (RBACP.coq_Init a) in
  let loop f = begin
    while true do
      ignore (procInt_wrapper st);
      ignore (f (procMsg_wrapper st))
    done
  end in loop

let run a = function
  | 0 -> run_nonbyz a
  | 1 ->
    (* dead node *)
    let loop _ = begin
      while true do () done
    end in loop
  | _ ->
    (* simpler byzantine, just double vote *)
    let st = ref (RBACP.coq_Init a) in
    let loop f = begin
      while true do
        ignore (procInt_wrapper_byz_double_vote st);
        ignore (f (procMsg_wrapper_byz st))
      done
    end in loop

end (* Lazymod end *)
