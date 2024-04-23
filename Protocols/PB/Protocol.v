From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Systems Require Export Protocol.
From ABCProtocol.Protocols.PB Require Export Types.

From RecordUpdate Require Import RecordUpdate.

Module Type PBProtocol (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS) (M : PBMessage A R Sn V Pf TSS)
  (P0 : SimplePacket A M) <: Protocol A M P0 BTh.

Import A R V Pf VBFT BTh TSS PBDT M P0.

Inductive InternalTransition_ :=
  | SendAction (r : Round).

Definition InternalTransition := InternalTransition_.

(* TODO repeating from RB *)
Definition AddrRdPair_eqdec : forall (ar1 ar2 : Address * Round), {ar1 = ar2} + {ar1 <> ar2}
  := prod_eq_dec Address_eqdec Round_eqdec.

Record State_ :=
  Node {
    id : Address;
    sent : Round -> bool;
    echoed : Address * Round -> option (Value * Proof);
    counter : Round -> list (Address * LightSignature);
    output : Round -> option CombinedSignature;
  }.

(* try something new *)
#[export] Instance eta : Settable _ := settable! Node <id; sent; echoed; counter; output>.

Definition State := State_.

Definition Init (n : Address) : State :=
  Node n (fun _ => false) (fun _ => None) (fun _ => nil) (fun _ => None).

Definition procInt (st : State) (tr : InternalTransition) : State * list Packet :=
  let: Node n smap emap cnt omap := st in
  match tr with
  | SendAction r =>
    if smap r 
    then (st, nil)
    else 
      let: smap' := map_update Round_eqdec r true smap in
      let: st' := st <| sent := smap' |> in
      let: (v, pf) := value_bft n r in
      let: msg := InitMsg r v pf in
      let: pkts := broadcast n msg in
      (st', pkts)
  end.

Definition procMsg (st : State) (src : Address) (msg : Message) : option (State * list Packet) :=
  let: Node n smap emap cnt omap := st in
  match msg with
  | InitMsg r v pf =>
    (* TODO if r includes some identity information about the sender, should we check the consistency? *)
    match emap (src, r) with
    | None =>
      if ex_validate r v pf
      then
        let: emap' := map_update AddrRdPair_eqdec (src, r) (Some (v, pf)) emap in
        let: st' := st <| echoed := emap' |> in
        let: lsig := light_sign (r, v) (lightkey_map n) in
        let: msg := EchoMsg r lsig in
        Some (st', mkP n src msg false :: nil)   (* single point, no broadcast *)
      else None
    | Some _ => None
    end
  | EchoMsg r lsig =>
    (* early terminating, constraining the size *)
    match omap r with
    | None =>
      if light_verify (r, fst (value_bft n r)) lsig src
      then
        if in_dec Address_eqdec src (map fst (cnt r))
        then None
        else
          (* simply add to counter *)
          let: cnt' := map_update Round_eqdec r ((src, lsig) :: cnt r) cnt in
          let: st' := st <| counter := cnt' |> in
          Some (st', nil)
      else None
    | _ => None
    end
  end.

(* TODO repeating from RB *)
Definition th_output := N - t0.

Fact th_output_gt_0 : 0 < th_output.
Proof. unfold th_output. pose proof N_minus_2t0_gt_0. lia. Qed.

Definition delivery_cert r st := lightsig_combine (map snd (st.(counter) r)).

Definition routine_check (st : State) (r : Round) : State :=
  let: l := st.(counter) r in
  if th_output =? length l  (* only once *)
  then
    let: cs := lightsig_combine (map snd l) in
    st <| output := map_update Round_eqdec r (Some cs) st.(output) |>
  else st.

Definition procMsgWithCheck (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match procMsg st src msg with
  | Some (st', pkts) =>
    match msg with
    | EchoMsg r _ => let: st'' := routine_check st' r in (st'', pkts)
    | _ => (st', pkts)
    end
  | None => (st, nil)
  end.

End PBProtocol.

Module PBProtocolImpl (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS) (M : PBMessage A R Sn V Pf TSS)
  (P0 : SimplePacket A M) <: Protocol A M P0 BTh <: PBProtocol A R Sn V Pf VBFT BTh TSS0 TSS PBDT M P0.

Include PBProtocol A R Sn V Pf VBFT BTh TSS0 TSS PBDT M P0.

End PBProtocolImpl.
