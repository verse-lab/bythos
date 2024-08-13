From Coq Require Import Bool List ListSet PeanoNat Lia.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Systems Require Export Protocol.
From Bythos.Protocols.RB Require Export Types.

From RecordUpdate Require Import RecordUpdate.

Module Type RBProtocol (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (M : RBMessage A R V)
  (P : SimplePacket A M) <: Protocol A M P BTh.

Import A R V VBFT BTh M P.

Definition InternalEvent := Round.

Definition AddrRdPair_eqdec : forall (ar1 ar2 : Address * Round), {ar1 = ar2} + {ar1 <> ar2}
  := prod_eq_dec Address_eqdec Round_eqdec.

Record State_ :=
  Node {
    id : Address;
    (* for internal transition *)
    sent : Round -> bool;
    (* having depth-1 maps should be more convenient, so use pair *)
    echoed : Address * Round -> option Value;
    voted : Address * Round -> option Value; 
    msgcnt : Message -> list Address;
    (* final output *)
    (* using the list type makes the statement of invariant easier, 
        but we need to prove that the length of this list <= 1 *)
    output : Address * Round -> list Value;
  }.

#[export] Instance eta : Settable _ := settable! Node <id; sent; echoed; voted; msgcnt; output>.

Definition State := State_.

Definition initState (n : Address) : State :=
  Node n (fun _ => false) (fun _ => None) (fun _ => None) (fun _ => nil) (fun _ => nil).

Definition procInt (st : State) (r : InternalEvent) : State * list Packet :=
  let: Node n smap emap vmap cnt omap := st in
  if smap r 
  then (st, nil) 
  else 
    let: smap' := map_update Round_eqdec r true smap in
    let: st' := st <| sent := smap' |> in
    let: msg := InitialMsg r (value_bft n r) in
    let: pkts := broadcast n msg in
    (st', pkts).

Definition procMsgPre (st : State) (src : Address) (msg : Message) : option (State * list Packet) :=
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
    (* make in_dec check explicit here *)
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

Definition th_echo4vote := N - f.
Definition th_vote4vote := f + 1.
Definition th_vote4output := N - f.

Fact th_echo4vote_gt_0 : 0 < th_echo4vote.
Proof. unfold th_echo4vote. pose proof f_lt_N. lia. Qed.

Fact th_vote4vote_gt_0 : 0 < th_vote4vote.
Proof. unfold th_vote4vote. (* pose proof f_lt_N_minus_2f. *) lia. Qed.

Fact th_vote4output_gt_0 : 0 < th_vote4output.
Proof th_echo4vote_gt_0.

Definition check_vote_condition (st : State) (msg : Message) : bool :=
  let: Node n smap emap vmap cnt omap := st in
  match msg with
  | EchoMsg q r _ =>
    (* should have not sent vote message before *)
    negb (ssrbool.isSome (vmap (q, r))) &&
    (* reach the threshold *)
    (th_echo4vote <=? length (cnt msg))
  | VoteMsg q r _ =>
    (* should have not sent vote message before *)
    negb (ssrbool.isSome (vmap (q, r))) &&
    (* reach the threshold *)
    (th_vote4vote <=? length (cnt msg))
  | _ => false
  end.

Definition check_output_condition (st : State) (msg : Message) : bool :=
  match msg with
  | VoteMsg _ _ _ =>
    (* allow setting the output multiple times? seems fine *)
    (* reach the threshold *)
    (th_vote4output <=? length (st.(msgcnt) msg))
  | _ => false
  end.

Definition update_voted_by_msg (st : State) (m : Message) : State * list Packet :=
  match m with
  | EchoMsg q r v | VoteMsg q r v =>
    let: vmap' := map_update AddrRdPair_eqdec (q, r) (Some v) st.(voted) in
    (st <| voted := vmap' |>, broadcast st.(id) (VoteMsg q r v))
  | _ => (st, nil) (* illegal *)
  end.

Definition update_output_by_msg (m : Message) output :=
  match m with
  | VoteMsg q r v =>
    map_update AddrRdPair_eqdec (q, r) (set_add_simple Value_eqdec v (output (q, r))) output
  | _ => output (* illegal *)
  end.

Definition routine_check (st : State) (msg : Message) : State * list Packet :=
  let: (st', pkts) := 
    if check_vote_condition st msg
    then update_voted_by_msg st msg
    else (st, nil) in
  let: st'' := 
    if check_output_condition st' msg
    then st' <| output := update_output_by_msg msg st'.(output) |>
    else st' in
  (st'', pkts).

Definition procMsg (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match procMsgPre st src msg with
  | Some (st', pkts) =>
    match msg with
    | InitialMsg _ _ => (st', pkts)
    | _ => let: (st'', pkts') := routine_check st' msg in (st'', pkts ++ pkts')
    end
  | None => (st, nil)
  end.

End RBProtocol.
