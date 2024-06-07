(* FIXME: each extracted protocol will have its own copy of shared definitions
    like JustAList. how can we eliminate such overlapping things?
  for now, use some tricks to avoid too much repetitive code *)

open Configuration.Config

(* a commonly used JustAList definition *)
(* due to the overlapping issue above, the module type annotation will be put
  for each individual protocol *)

module PeersPre =
  struct
  
  type t = address
  let t_eqdec ((s1, i1) : t) ((s2, i2) : t) =
    (String.equal s1 s2) && (i1 = i2)

  let elements () = !cluster
    
  end

(* usage example: *)
(* module Peers:JustAList with type t = int * int = PeersPre *)

(* FIXME: the coq_ prefixes are kind of troublesome ... how to deal with them? *)

module RoundPre =
  struct
  
  type coq_Round = int
  let coq_Round_eqdec (r1 : coq_Round) (r2 : coq_Round) = (r1 = r2)

  end

(* a minimal description of a protocol executed on a node *)
(* notably, Byzantine nodes can also use this *)
type ('st, 'msg, 'itr, 'node) minimal_protocol = {
  mutable st : 'st;
  procInt : 'st -> 'itr -> 'st * ('node * 'msg) list;
  procMsg : 'st -> 'node -> 'msg -> 'st * ('node * 'msg) list
}
