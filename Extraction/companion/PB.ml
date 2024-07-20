open Protocols.PB
open Common
open Configuration.Config

module Lazymod (A : sig end) = struct

module PL = Playground(Peers)

module PL2 = PL.Playground2(StringSn)(PPrim)

(** scenario setting: 
    - multi-rounded 4-iteration PB (protocol composition can be more easily achieved after extraction?)
    - value: randomly generated int
    - ex validator: for the first iteration, check the light signature;
      for the subsequent iteration, check whether it is the combined signature for the value in this round in the previous iteration
**)

module Pf =
  struct

  type coq_Proof =
    | LightSig of PL2.TSSPrim.coq_LightSignature
    | DeliveryCert of PL2.TSSPrim.coq_CombinedSignature option

  let coq_Proof_eqdec (pf1 : coq_Proof) (pf2 : coq_Proof) =
    match pf1, pf2 with
    | LightSig i1, LightSig i2 -> PL2.TSSPrim.coq_LightSignature_eqdec i1 i2
    | DeliveryCert (Some l1), DeliveryCert (Some l2) -> PL2.TSSPrim.coq_CombinedSignature_eqdec l1 l2
    | _, _ -> false

  end

let string_of_round_value ((r, itr), v) : string =
  String.concat " " (List.map string_of_int [r; itr; v])

module VBFT =
  struct

  (* need to be outside, since it will be updated by procMsg *)
  let lst_delivery_cert : (PL2.TSSPrim.coq_CombinedSignature option) ref = ref None

  (* will be used in different places *)
  let cur_round = ref 0
  let cur_iter = ref 0
  let max_iter = 4

  let fst_value_bft = random_function_with_mem ()

  (* this function should be deterministic wrt. r *)
  let value_bft (a : address) =
    let aux ((r, itr) : int * int) =
      let v = fst_value_bft r in
      if itr = 1
      then (v, Pf.LightSig (PL2.TSSPrim.light_sign (string_of_round_value ((r, itr), v)) (PL2.TSSPrim.lightkey_map a)))
      else (v, Pf.DeliveryCert !lst_delivery_cert)
    in aux

  end

module PBDT =
  struct

  let coq_RVSn = string_of_round_value

  (* this is awkward! ex_validate does not accept the sender as an argument *)
  (* anyway, as a hack, we can use a ref to record the sender *)
  let lst_sender : address ref = ref ("", -1)

  let ex_validate ((r, itr) : int * int) (v : int) = function
    | Pf.LightSig lsig -> (itr = 1) && (PL2.TSSPrim.light_verify (coq_RVSn ((r, itr), v)) lsig !lst_sender)
    | Pf.DeliveryCert (Some cs) -> (itr > 1) && (itr <= VBFT.max_iter) && (PL2.TSSPrim.combined_verify (coq_RVSn ((r, itr - 1), v)) cs)
    | _ -> false

  end

module PBP = PL2.RealPBProtocolImpl(IntPairRound)(IntValue)(Pf)(VBFT)(PBDT)

let packet_simplify p =
  let open PBP.PBPk in
  (p.dst, p.msg)

let procInt_simpler st itr = 
  let (st', pkts) = PBP.procInt st itr in
  (st', List.map packet_simplify pkts)

let procMsg_simpler st src msg = 
  let (st', pkts) = PBP.procMsg st src msg in
  (st', List.map packet_simplify pkts)

let string_of_round (r, itr) = "[" ^ string_of_int r ^ ", " ^ string_of_int itr ^ "]"

let string_of_value v = string_of_int v

let string_of_proof = function
  | Pf.LightSig _ -> "[some light sig]"
  | Pf.DeliveryCert _ -> "[some combined sig]"

let string_of_message m =
  let open PBP.PBM in
  match m with
  | InitMsg (rd, v, pf) -> String.concat "" ["Init ("; string_of_round rd; ", "; string_of_value v; ", "; string_of_proof pf; ")"]
  | EchoMsg (rd, lsig) -> String.concat "" ["Echo ("; string_of_round rd; ", [some light sig])"]

(* copied from RB.ml *)
let update_and_send st' pkts st_ref =
  st_ref := st';
  if pkts <> [] then begin
    Printf.printf "sending:"; print_newline ();
    List.iter (fun (dst, msg) -> Printf.printf "  %s to %s" (string_of_message msg) (string_of_address dst); print_newline ()) pkts
  end else ();
  Shim.Net.send_all pkts;
  Some (st', pkts)

let procInt_inner st_ref =
  let (st', pkts) = procInt_simpler !st_ref (!VBFT.cur_round, !VBFT.cur_iter) in
  update_and_send st' pkts st_ref

(* ideally, 30s is enough for a full round of broadcast? *)

let check () =
  Printf.printf "check before spontaneous procInt ... ";
  match !VBFT.lst_delivery_cert with
  | Some dc -> begin
    if !VBFT.cur_iter <> VBFT.max_iter
    then Printf.printf "this should not happen. something is wrong!"
    else begin
      let r = !VBFT.cur_round in
      let rd = (r, !VBFT.cur_iter) in
      let v = VBFT.fst_value_bft r in
      Printf.printf "found existing delivery certificate ... ";
      if not (PL2.TSSPrim.combined_verify (PBDT.coq_RVSn (rd, v)) dc)
      then Printf.printf "the delivery certificate for round %d is broken. why?" r
      else ()
    end
  end
  | None when !VBFT.cur_round = 0 -> ()
  | _ -> Printf.printf "broadcast is not finished yet; stopped at iteration %d. why?" !VBFT.cur_iter

let procInt_wrapper =
  let lst_time = ref (-1) in
  let aux st_ref = begin
    let tm = int_of_float (Unix.time ()) in
    if (tm mod 30 = !me_port mod 30) && (tm <> !lst_time)
    then begin
      lst_time := tm;
      check (); print_newline ();
      incr VBFT.cur_round; VBFT.cur_iter := 1; VBFT.lst_delivery_cert := None;
      procInt_inner st_ref
    end
    else None
  end in aux

let check_if_next_iter msg (old_st : PBP.coq_State) (new_st : PBP.coq_State) =
  let open PBP in
  match msg with
  | PBM.EchoMsg (rd, _) -> begin
    match old_st.output rd, new_st.output rd with
    | None, Some dc -> (VBFT.lst_delivery_cert := Some dc; !VBFT.cur_iter < VBFT.max_iter) (* effectful! *)
    | _, _ -> false
  end
  | _ -> false

let procMsg_wrapper st_ref sender msg =
  Printf.printf "receiving %s from %s" (string_of_message msg) (string_of_address sender); print_newline ();
  (* echo the hacky trick above *)
  PBDT.lst_sender := sender;
  let old_st = !st_ref in
  let (st', pkts) = procMsg_simpler old_st sender msg in
  ignore (update_and_send st' pkts st_ref);
  (* check whether it is the time for the next iteration *)
  if check_if_next_iter msg old_st !st_ref
  then (incr VBFT.cur_iter; ignore (procInt_inner st_ref); VBFT.lst_delivery_cert := None)  (* clean lst_delivery_cert only after procInt *)
  else ();
  None (* dummy; just to typecheck *)

(* copied from RB.ml *)
let run a = function
  | 0 ->
    (* non-faulty *)
    Random.init !me_port;
    let st = ref (PBP.initState a) in
    let loop f = begin
      while true do
        ignore (procInt_wrapper st);
        ignore (f (procMsg_wrapper st))
      done
    end in loop
  | _ ->
    (* dead node, but at least needs to check new connections to do key exchange *)
    let loop _ = begin
      while true do Shim.Net.check_for_new_connections () done
    end in loop

end (* Lazymod end *)
