From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Systems Require Export Protocol.
From Bythos.Protocols.PB Require Export Types.

From RecordUpdate Require Import RecordUpdate.

Module Type PBProtocol (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (VBFT : ValueBFT A R V Pf) 
  (BTh : ClassicByzThreshold A)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f) (* ! *)
  (PBDT : PBDataTypes A R Sn V Pf) (M : PBMessage A R Sn V Pf TSSPrim)
  (P0 : SimplePacket A M) <: Protocol A M P0 BTh.

Module Export TSS := ThresholdSignatureScheme A Sn TSSPrim.
Import A R V Pf VBFT BTh PBDT M P0.

Inductive InternalEvent_ :=
  | SendAction (r : Round).

Definition InternalEvent := InternalEvent_.

Definition AddrRdPair_eqdec : forall (ar1 ar2 : Address * Round), {ar1 = ar2} + {ar1 <> ar2}
  := prod_eq_dec Address_eqdec Round_eqdec.

Record State_ :=
  Node {
    id : Address;
    (* sender state *)
    sent : Round -> bool;
    counter : Round -> list (Address * LightSignature);
    output : Round -> option CombinedSignature;
    (* receiver state *)
    echoed : Address * Round -> option (Value * Proof);
  }.

#[export] Instance eta : Settable _ := settable! Node <id; sent; counter; output; echoed>.

Definition State := State_.

Definition initState (n : Address) : State :=
  Node n (fun _ => false) (fun _ => nil) (fun _ => None) (fun _ => None).

Definition procInt (st : State) (tr : InternalEvent) : State * list Packet :=
  let: Node n smap cnt omap emap := st in
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

Definition proposal n r := fst (value_bft n r).

(* NOTE: the procMsg shown in the paper can be regarded as the result of inlining 
    routine_check and procMsgPre inside the procMsg defined here *)

Definition procMsgPre (st : State) (src : Address) (msg : Message) : option (State * list Packet) :=
  let: Node n smap cnt omap emap := st in
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
      if light_verify (r, proposal n r) lsig src
      then
        (* NOTE: there is a discrepancy from the pseudocode: 
          in the pseudocode, the sender is not recorded, but only signature is recorded
          not sure if the latter also works; here also record the senders to make things easier *)
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

Definition th_output := N - f.

Fact th_output_gt_0 : 0 < th_output.
Proof. unfold th_output. pose proof N_minus_2f_gt_0. lia. Qed.

Definition delivery_cert r st := lightsig_combine (map snd (st.(counter) r)).

Definition routine_check (st : State) (r : Round) : State :=
  let: l := st.(counter) r in
  if th_output =? length l  (* only once *)
  then
    let: cs := lightsig_combine (map snd l) in
    st <| output := map_update Round_eqdec r (Some cs) st.(output) |>
  else st.

Definition procMsg (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match procMsgPre st src msg with
  | Some (st', pkts) =>
    match msg with
    | EchoMsg r _ => let: st'' := routine_check st' r in (st'', pkts)
    | _ => (st', pkts)
    end
  | None => (st, nil)
  end.

End PBProtocol.
