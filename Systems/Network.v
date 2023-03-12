From Coq Require Import List.
From Coq Require ssreflect.
From Coq Require Import ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States.

Module Type ACNetwork
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC).
Import A T AC Ns.

Definition PacketSoup := list Packet.

(* not sure to use a dedicated PacketSoup for Prcv or not in Coq ... *)
Record World :=
  mkW {
    localState : StateMap;
    sentMsgs : PacketSoup;
  }.

Definition initWorld := mkW initState nil.

(* Network semantics *)
(* a predicate holds for the state of a given node *)
Definition holds (n : Address) (w : World) (cond : State -> Prop) :=
  cond (localState w n).

(* tries to pack all coherent props into a record *)
Record Coh (w : World) : Prop := mkCoh {
  id_coh: forall n, holds n w (fun st => id st = n);
  unrelated_intact: forall n, ~ valid_node n -> holds n w (fun st => st = Init n);
}.

(* unclear about this, ignore it for now *)
(* Record Qualifier := Q { ts: Timestamp; allowed: Address; }. *)

(* yes, how about extracting this to be ...? *)

Definition seen_in_history (src : Address) (v : Value) (s : Signature) (pkts : PacketSoup) :=
  exists dst consumed, In (mkP src dst (SubmitMsg v s) consumed) pkts.

Definition cert_correct (psent : PacketSoup) (c : Certificate) :=
  let: (v, nsigs) := c in
  forall n sig, 
    In (n, sig) nsigs ->
    is_byz n = false ->
    verify v sig n = true -> (* this can be expressed in other way *)
    seen_in_history n v sig psent. 

Definition consume (p : Packet) (psent : PacketSoup) :=
  (receive_pkt p) :: (List.remove Packet_eqdec p psent).

(* TODO use this or indexed inductive relation?
    and put Coh inside the invariant or here?
*)
Inductive system_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) of
      (* Coh w &  *)
      In p (sentMsgs w) &
      consumed p = false &
      valid_node (dst p) &
      is_byz (dst p) = false &
      let: (st', ms) := procMsg (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               ((consume p (sentMsgs w)) ++ ms)

| Intern (proc : Address) (t : InternalTransition) of
      (* Coh w & *)
      valid_node proc &
      is_byz proc = false &
      let: (st', ms) := (procInt (localState w proc) t) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (sentMsgs w))

(* can possibly generate garbage in the following two trans *)
| ByzSubmit (src dst : Address) (v : Value) (s : Signature) of
      (* Coh w & *)
      is_byz src &
      w' = mkW (localState w)
               ((mkP src dst (SubmitMsg v s) false) :: (sentMsgs w))

| ByzConfirm (src dst : Address) (c : Certificate) of
      (* Coh w & *)
      is_byz src &
      cert_correct (sentMsgs w) c &
      w' = mkW (localState w)
               ((mkP src dst (ConfirmMsg c) false) :: (sentMsgs w))
.

End ACNetwork.
