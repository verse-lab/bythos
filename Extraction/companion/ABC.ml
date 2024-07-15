open Protocols.Driver
open Common
open Configuration.Config
open Util

module Lazymod (A : sig end) = struct

module PL = Playground(Peers)

module ACP = PL.RealACProtocolImpl(StringSn)(IntValue)(PPrim)(PL.BTh)

let packet_simplify p =
  let open ACP.ACPk in
  (p.dst, p.msg)

let procInt_simpler st itr = 
  let (st', pkts) = ACP.procInt st itr in
  (st', List.map packet_simplify pkts)

let procMsg_simpler st src msg = 
  let (st', pkts) = ACP.procMsgWithCheck st src msg in
  (st', List.map packet_simplify pkts)

let string_of_value v = string_of_int v

let string_of_message m =
  let open ACP.ACM in
  match m with
  | SubmitMsg (v, _, _) -> String.concat "" ["Submit ("; string_of_value v; ", "; "[some light sig]"; ", "; "[some full sig]"; ")"]
  | LightConfirmMsg (v, _) -> String.concat "" ["LightCert ("; string_of_value v; ", "; "[some combined sig]"; ")"]
  | ConfirmMsg (v, nsigs) -> String.concat "" ["Cert ("; string_of_value v; ", "; 
      "["; String.concat "; " (List.map (fun (n, _) -> string_of_address n) nsigs); "]"; ")"]

(* copied from RB.ml *)
let update_and_send st' pkts st_ref =
  st_ref := st';
  if pkts <> [] then begin
    Printf.printf "sending:"; print_newline ();
    List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts
  end else ();
  Shim.Net.send_all pkts;
  Some (st', pkts)

(* hack: manually specify value *)
let value_bft =
  List.filter_map (fun s -> try Some (int_of_string s) with _ -> None) (String.split_on_char '.' !extrainfo)

(* randomly pick a time to send a random value *)
let procInt_wrapper =
  (* seems that if not protected, the let will be optimized at compilation time *)
  let q = lazy (Random.int 20) in
  let v = list_nth_default value_bft 0 749837295 in
  let sent = ref false in
  let aux st_ref = begin
    let tm = int_of_float (Unix.time ()) in
    if (not !sent) && (tm mod 20 = Lazy.force q)
    then begin
      sent := true;
      let (st', pkts) = procInt_simpler !st_ref v in
      update_and_send st' pkts st_ref
    end
    else None
  end in aux

let procInt_wrapper_byz =
  let q1 = lazy (Random.int 10) in
  let q2 = lazy (Random.int 10) in
  let v1 = list_nth_default value_bft 0 749837295 in
  let v2 = list_nth_default value_bft 1 749837296 in
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
      (* byz: forgetting *)
      st_ref := { !st_ref with ACP.submitted_value = None };
      let (st', pkts) = procInt_simpler !st_ref v in
      update_and_send st' pkts st_ref
    end
    | None -> None
  end in aux

let check_confirmed (old_st : ACP.coq_State) (new_st : ACP.coq_State) =
  let open ACP in
  if (not old_st.conf) && new_st.conf
  then begin
    match new_st.submitted_value with
    | Some v -> Printf.printf "confirmed value %d" v; print_newline ()
    | _ -> failwith "this should not happen"
  end else ()

let check_genproof =
  (* genproof might be expensive to compute, so memorize it *)
  let found_proof = ref false in
  let aux st = begin
    if not (!found_proof) then begin
      let open ACP in
      let pf = ACDT.CertCheckersImpl.genproof st.received_certs in
      if pf <> []
      then (found_proof := true; Printf.printf "found culprits: %s" (String.concat "; " (List.map string_of_address pf)); print_newline ())
      else ()
    end else ()
  end in aux

let procMsg_wrapper st_ref sender msg =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  let old_st = !st_ref in
  let (st', pkts) = procMsg_simpler !st_ref sender msg in
  check_confirmed old_st st';
  check_genproof st';
  update_and_send st' pkts st_ref

(* copied from PB.ml *)
let run a = function
  | 0 ->
    (* non-faulty *)
    Random.init !me_port;
    let st = ref (ACP.coq_Init a) in
    let loop f = begin
      while true do
        ignore (procInt_wrapper st);
        ignore (f (procMsg_wrapper st))
      done
    end in loop
  | 1 ->
    (* dead node, but at least needs to check new connections; this is inevitable *)
    let loop _ = begin
      while true do Shim.Net.check_for_new_connections () done
    end in loop
  | _ ->
    (* only submit two values, then keep silence *)
    Random.init !me_port;
    let st = ref (ACP.coq_Init a) in
    let loop _ = begin
      while true do 
        ignore (procInt_wrapper_byz st);
        Shim.Net.check_for_new_connections ()
      done
    end in loop

end (* Lazymod end *)
