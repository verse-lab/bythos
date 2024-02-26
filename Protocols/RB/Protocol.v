From Coq Require Import Bool List ListSet PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Systems Require Export Protocol.
From ABCProtocol.Protocols.RB Require Export Types.

From RecordUpdate Require Import RecordUpdate.

Module Type RBProtocol (A : NetAddr) (R : RBTag) (V : Signable)
  (VBFT : ValueBFT A R V) 
  (BTh : ByzThreshold A) (M : RBMessage A R V)
  (P : SimplePacket A M) <: Protocol A M P BTh.

Import A R V VBFT BTh M P.

Inductive InternalTransition_ :=
  | SendAction (r : Round).

Definition InternalTransition := InternalTransition_.

Definition AddrRdPair_eqdec : forall (ar1 ar2 : Address * Round), {ar1 = ar2} + {ar1 <> ar2}
  := prod_eq_dec Address_eqdec Round_eqdec.

Inductive Output : Set := ONone | OSome (v : Value) | OAmbig.

Definition output_merge (o : Output) (v : Value) : Output :=
  match o with
  | ONone => OSome v
  | OSome v' => if Value_eqdec v v' then o else OAmbig
  | OAmbig => OAmbig
  end.

Record State_ :=
  Node {
    id : Address;
    (* for internal transition *)
    (* TODO use some library for the following things? *)
    (* TODO require the maps to be finite? *)
    sent : Round -> bool;
    (* having depth-1 maps should be more convenient, so use pair *)
    echoed : Address * Round -> option Value;
    voted : Address * Round -> option Value; 
    msgcnt : Message -> list Address;
    output : Address * Round -> Output; (* final output *)
  }.

(* try something new *)
#[export] Instance eta : Settable _ := settable! Node <id; sent; echoed; voted; msgcnt; output>.

Definition State := State_.

Definition Init (n : Address) : State :=
  Node n (fun _ => false) (fun _ => None) (fun _ => None) (fun _ => nil) (fun _ => ONone).

Definition procInt (st : State) (tr : InternalTransition) : State * list Packet :=
  let: Node n smap emap vmap cnt omap := st in
  match tr with
  | SendAction r =>
    if smap r 
    then (st, nil) 
    else 
      let: smap' := map_update Round_eqdec r true smap in
      let: st' := st <| sent := smap' |> in
      let: msg := InitialMsg r (value_bft n r) in
      let: pkts := broadcast n msg in
      (st', pkts)
  end.

(* TODO do things still work if we consider short-circuiting?
    it seems like the following heuristic will break when the triggering message is
    Echo, but by short-circuiting the node collects enough Ready messages and thus 
    the subsequent triggering message becomes Ready. *)

Definition procMsg (st : State) (src : Address) (msg : Message) : option (State * list Packet) :=
  let: Node n smap emap vmap cnt omap := st in
  match msg with
  | InitialMsg r v =>
    match emap (src, r) with
    | None =>
      (* not echoed for this (src, v) pair yet *)
      let: emap' := map_update AddrRdPair_eqdec (src, r) (Some v) emap in
      let: st' := st <| echoed := emap' |> in
      let: msg := EchoMsg src r v in
      let: pkts := broadcast n msg in
      Some (st', pkts)
    | Some _ => None
    end
  | _ =>
    (* simply add to message counter *)
    (* explicit in_dec check *)
    (* FIXME: maybe impose size limit to counter like in ABC? currently do not *)
    if in_dec Address_eqdec src (cnt msg)
    then None
    else
      let: cnt' := map_update Message_eqdec msg (src :: cnt msg) cnt in
      let: st' := st <| msgcnt := cnt' |> in
      Some (st', nil)
  end.

(* 
  One way to implement the checking is to iterate over all received messages
  and see if any of them has reached the threshold of trigger, but certainly
  no real implementation will use that approach (since it is too inefficient). 

  A simple heuristic is to only consider whether receiving the current message 
  would trigger some event. 
*)

(* some auxiliary definitions for the monitor *)

Definition th_echo4ready := N - t0.
Definition th_ready4ready := N - (t0 + t0).
Definition th_ready4output := N - t0.

Definition check_ready_condition (st : State) (msg : Message) : bool :=
  let: Node n smap emap vmap cnt omap := st in
  match msg with
  | EchoMsg q r _ =>
    (* should have not sent ready message before *)
    negb (ssrbool.isSome (vmap (q, r))) &&
    (* reach the threshold *)
    (th_echo4ready <=? length (cnt msg))
  | ReadyMsg q r _ =>
    (* should have not sent ready message before *)
    negb (ssrbool.isSome (vmap (q, r))) &&
    (* reach the threshold *)
    (th_ready4ready <=? length (cnt msg))
  | _ => false
  end.

Definition check_output_condition (st : State) (msg : Message) : bool :=
  match msg with
  | ReadyMsg _ _ _ =>
    (* allow setting the output multiple times? seems fine *)
    (* reach the threshold *)
    (th_ready4output <=? length (st.(msgcnt) msg))
  | _ => false
  end.

Definition update_voted_by_msg (st : State) (m : Message) : State * list Packet :=
  match m with
  | EchoMsg q r v | ReadyMsg q r v =>
    let: vmap' := map_update AddrRdPair_eqdec (q, r) (Some v) st.(voted) in
    (st <| voted := vmap' |>, broadcast st.(id) (ReadyMsg q r v))
  | _ => (st, nil) (* illegal *)
  end.

Definition update_output_by_msg (m : Message) output :=
  match m with
  | ReadyMsg q r v =>
    map_update AddrRdPair_eqdec (q, r) (output_merge (output (q, r)) v) output
  | _ => output (* illegal *)
  end.

Definition routine_check (st : State) (msg : Message) : State * list Packet :=
  let: (st', pkts) := 
    if check_ready_condition st msg
    then update_voted_by_msg st msg
    else (st, nil) in
  (* TODO this consequencing is ad-hoc ... maybe having some combinator would be better *)
  let: st'' := 
    if check_output_condition st' msg
    then st' <| output := update_output_by_msg msg st'.(output) |>
    else st' in
  (st'', pkts).

Definition procMsgWithCheck (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match procMsg st src msg with
  | Some (st', pkts) =>
    match msg with
    | InitialMsg _ _ => (st', pkts)
    | _ => let: (st'', pkts') := routine_check st' msg in (st'', pkts ++ pkts')
    end
  | None => (st, nil)
  end.

End RBProtocol.

Module RBProtocolImpl (A : NetAddr) (R : RBTag) (V : Signable)
  (VBFT : ValueBFT A R V) 
  (BTh : ByzThreshold A) (M : RBMessage A R V)
  (P : SimplePacket A M) <: Protocol A M P BTh <: RBProtocol A R V VBFT BTh M P.

Include RBProtocol A R V VBFT BTh M P.

End RBProtocolImpl.
