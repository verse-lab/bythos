open Configuration.Config
open Shim

(* a commonly used JustAList definition *)
(* due to the overlapping issue above, the module type annotation will be put
  for each individual protocol *)

module Peers =
  struct
  
  type t = address
  let t_eqdec ((s1, i1) : t) ((s2, i2) : t) =
    (String.equal s1 s2) && (i1 = i2)

  let elements () = !cluster
    
  end

(* usage example: *)
(* module Peers:JustAList with type t = int * int = PeersPre *)

module IntRound =
  struct
  
  type coq_Round = int
  let coq_Round_eqdec (r1 : coq_Round) (r2 : coq_Round) = (r1 = r2)

  end

module IntPairRound =
  struct
  
  type coq_Round = int * int
  let coq_Round_eqdec ((r1, itr1) : coq_Round) ((r2, itr2) : coq_Round) =
    (r1 = r2) && (itr1 = itr2)

  end

module IntValue =
  struct
  
  type coq_Value = int
  let coq_Value_eqdec (v1 : coq_Value) (v2 : coq_Value) = (v1 = v2)
  let coq_Value_inhabitant = 0
  let coq_VSn = string_of_int

  end

(* DEPRECATED since the logic of protocol execution should be described
    with more precise things (e.g., while-loops) *)
(* a minimal description of a protocol executed on a node *)
(* notably, Byzantine nodes can also use this *)
(*
type ('st, 'msg, 'itr, 'node) minimal_protocol = {
  mutable st : 'st;
  procInt : 'st -> 'itr -> 'st * ('node * 'msg) list;
  procMsg : 'st -> 'node -> 'msg -> 'st * ('node * 'msg) list
}
*)

module StringSn =
  struct

  type t = string

  let eqdec = String.equal

  type 'a signable = 'a -> t

  let make (q : 'a1 signable) : 'a1 -> t = q

  end

let get_pub_key (a : address) =
  match Hashtbl.find_opt Crypto.pub_key_map a with
  | Some k -> k
  | None -> begin
    ignore (Net.get_write_fd a);
    match Hashtbl.find_opt Crypto.pub_key_map a with
    | Some k -> k
    | None -> failwith ("Fail to fetch the public key of node " ^ string_of_address a ^ ". Is the setting correct?")
  end

(* a PKIPrim module *)

module PPrim =
  struct

  type coq_PrivateKey = Crypto.private_key

  type coq_Signature = Crypto.signature

  let coq_Signature_eqdec = Crypto.signature_equal

  (* should be ok as long as the node only uses its own private key *)
  let key_map (_ : address) = Crypto.self_priv_key ()

  let verify (s : string) (rs : Crypto.signature) (a : address) : bool =
    let pub = get_pub_key a in
    let hmsg = Crypto.hash_of_string s in
    let res = Mirage_crypto_pk.Dsa.verify ~key:pub rs hmsg in
    res

  let sign = Crypto.sign_string

  end

let random_function_with_mem () =
  let tb : (int, int) Hashtbl.t = Hashtbl.create 10 in
  let aux a = begin
    match Hashtbl.find_opt tb a with
    | Some v -> v
    | None -> (let v = Random.int 998244352 in Hashtbl.add tb a v; v)
  end in aux
