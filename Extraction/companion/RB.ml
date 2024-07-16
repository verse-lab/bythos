open Protocols.RB
open Common
open Configuration.Config

(* instantiating the concrete datatype modules *)
(* doing it here might be easier than doing it in Coq? *)

(* somehow delay the instantiations of everything below, since cluster will only be ready at runtime *)
module Lazymod (A : sig end) = struct

module PL = Playground(Peers)

module VBFT =
  struct

  (* well, just go random ... *)
  let value_bft _ _ =
    Random.int 998244352

  end

module RBP = PL.RealRBProtocolImpl(IntRound)(IntValue)(VBFT)

(* unfortunately, the boilerplate code below seems hard to eliminate ... *)
let packet_simplify p =
  let open RBP.RBPk in
  (p.dst, p.msg)

let procInt_simpler st itr = 
  let (st', pkts) = RBP.procInt st itr in
  (st', List.map packet_simplify pkts)

let procMsg_simpler st src msg = 
  let (st', pkts) = RBP.procMsg st src msg in
  (st', List.map packet_simplify pkts)

(* can we automate the string_of derivations for these types?
    neither ppx_import nor ppx_deriving works, since the types are inside a functor *)

let string_of_round r = string_of_int r

let string_of_value v = string_of_int v

let string_of_message m =
  let open RBP.RBM in
  match m with
  | InitialMsg (r, v) -> String.concat "" ["Init ("; string_of_round r; ", "; string_of_value v; ")"]
  | EchoMsg (orig, r, v) -> String.concat "" ["Echo ("; string_of_address orig; ", "; string_of_round r; ", "; string_of_value v; ")"]
  | VoteMsg (orig, r, v) -> String.concat "" ["Vote ("; string_of_address orig; ", "; string_of_round r; ", "; string_of_value v; ")"]

let update_and_send st' pkts st_ref =
  st_ref := st';
  if pkts <> [] then begin
    Printf.printf "sending:"; print_newline ();
    List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts
  end else ();
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
      incr cur_round;
      let (st', pkts) = procInt_simpler !st_ref !cur_round in
      update_and_send st' pkts st_ref
    end
    else None
  end in aux

(* to make things more interesting, do some simple checking:
    ideally, 10s is enough for a round of broadcast *)

let check sender msg (st : RBP.coq_State) =
  let open RBP.RBM in
  match msg with
  | InitialMsg (new_r, _) when new_r > 1 -> begin
    let r = new_r - 1 in
    match st.output (sender, r) with
    | [] -> Printf.printf "no acknowledgement for %s at round %s yet. why?" (string_of_address sender) (string_of_round r)
    | [v] -> Printf.printf "acknowledgement for %s at round %s is %s" (string_of_address sender) (string_of_round r) (string_of_value v)
    | _ :: _ :: _ -> Printf.printf "more than one acknowledgement for %s at round %s. why?" (string_of_address sender) (string_of_round r)
  end; print_newline ()
  | _ -> ()

let procMsg_wrapper st_ref sender msg =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  check sender msg !st_ref;
  let (st', pkts) = procMsg_simpler !st_ref sender msg in
  update_and_send st' pkts st_ref

(* the function f is basically procMsg_wrapper_wrapper *)
let run a = function
  | 0 ->
    (* non-faulty *)
    Random.init !me_port;
    let st = ref (RBP.initState a) in
    let loop f = begin
      while true do
        ignore (procInt_wrapper st);
        ignore (f (procMsg_wrapper st))
      done
    end in loop
  | _ ->
    (* dead node *)
    let loop _ = begin
      while true do () done
    end in loop

end (* Lazymod end *)
