From Coq Require Import Bool List PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Systems Require Export Protocol.
From Bythos.Protocols.ABC Require Export Types.

From RecordUpdate Require Import RecordUpdate.

Module Type ACProtocol (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (M : ACMessage A Sn V P TSS ACDT)
  (P0 : SimplePacket A M) <: Protocol A M P0 BTh.

Import A V (* VBFT *) BTh P TSS ACDT CC M P0.

Inductive InternalTransition_ :=
  | SubmitIntTrans (v : Value).

Definition InternalTransition := InternalTransition_.
(* TODO 
    If the light certificate conflict check is modelled as an internal transition, 
    then possibly the "eventual Byzantine detection" cannot be expressed easily. 

    However, in order to trigger the check, the conf must be true (which is due to the delivery
    of the (N-t0)-th submit message) and there must be two conflicting light certificates
    (which is due to the delivery of some LightConfirmMsg).  

    They are not synchronized, so we should append "monitors" to the above
    two delivery actions, if not to make light certificate check internal. 

    This is troublesome for now. I suppose there would be a better way to systematically 
    frame out such monitors in the proof (maybe IVy has done something similar). 

  Wait. This may be done with a new kind of transitions?
*)

(* TODO assume peers are already known? *)

Record State_ :=
  Node {
    id : Address;
    (* peers : peers_t; *)
    conf : bool;
    submitted_value : option Value;
    (* need to contain all addresses otherwise cannot perform operations like set *)
    (* since there are two kinds of signatures now, seems cannot avoid using split/combine *)
    from_set : list Address;
    collected_lightsigs : list LightSignature;
    collected_sigs : list Signature;
    received_lightcerts : list LightCertificate;
    received_certs : list Certificate;
    (* holding all pending submit messages *)
    (* TODO add it here, or in a separate State type? *)
    msg_buffer : list (Address * Message)
  }.

#[export] Instance eta : Settable _ := settable! Node <id; conf; submitted_value; from_set; collected_lightsigs; 
  collected_sigs; received_lightcerts; received_certs; msg_buffer>.

Definition State := State_.
(*
Definition State_eqdec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.
  intros. decide equality.
  - decide equality. apply prod_eq_dec; auto using Message_eqdec, Address_eqdec.
  - decide equality. apply Certificate_eqdec.
  - decide equality. apply LightCertificate_eqdec.
  - decide equality. apply Signature_eqdec.
  - decide equality. apply LightSignature_eqdec.
  - decide equality. apply Address_eqdec.
  - decide equality. apply Value_eqdec.
  - decide equality.
  - apply Address_eqdec.
Qed.
*)
Definition Init (n : Address) : State :=
  Node n false None nil nil nil nil nil nil.

Definition certificate_valid v nsigs : Prop :=
  Forall (fun '(n, sig) => verify v sig n) nsigs.

Definition verify_certificate v nsigs : {certificate_valid v nsigs} + {~ certificate_valid v nsigs}.
  unfold certificate_valid.
  apply Forall_dec. (* there is no existing Forall2_dec *)
  intros (n, sig).
  apply bool_dec.
Qed.

Definition light_signatures_valid v nlsigs : Prop :=
  Forall (fun '(n, lsig) => light_verify v lsig n) nlsigs.

Fact light_signatures_valid_for_combine v ns lsigs
  (Hlen : length ns = length lsigs) (H : light_signatures_valid v (combine ns lsigs)) :
  lsigs = map (fun n => light_sign v (lightkey_map n)) ns.
Proof.
  apply length_eq_Forall2_True in Hlen.
  induction Hlen as [ | n ls ns lsigs _ _ IH ].
  - reflexivity.
  - simpl in H.
    apply Forall_cons_iff in H.
    destruct H as (->%lightkey_correct & H).
    specialize (IH H).
    subst lsigs.
    split; auto.
Qed.

Definition zip_from_lsigs (st : State) := 
  List.combine st.(from_set) st.(collected_lightsigs).

Definition zip_from_sigs (st : State) := 
  List.combine st.(from_set) st.(collected_sigs).

Definition zip_from_lsigs_sigs (st : State) := 
  List.combine (List.combine st.(from_set) st.(collected_lightsigs)) st.(collected_sigs).

(* there is only one such check, so somewhat ad-hoc *)
(* FIXME: possibly make sure this would be triggered only once *)
Definition routine_check (st : State) : list Packet :=
  let: Node n conf ov from lsigs sigs rlcerts rcerts buffer := st in
  match ov with 
  | Some vthis => 
    (* actually confirmation implies submission; but we need to use vthis so anyway *)
    if conf && (lightcert_conflict_check rlcerts)
    then broadcast n (ConfirmMsg (vthis, zip_from_sigs st))
    else nil
  | None => nil
  end
.

Definition procMsg (st : State) (src : Address) (msg : Message) : option (State * list Packet) :=
  let: Node n cf ov from lsigs sigs rlcerts rcerts buffer := st in
  match msg with
  | SubmitMsg v lsig sig =>
    match ov with 
    | Some vthis => 
      if (Value_eqdec v vthis) && (verify v sig src) && (light_verify v lsig src)
      then
        (* before prepending, add a check to avoid adding a duplicate node-signature pair *)
        (* checking In fst or In pair should be the same, due to the correctness of verify *)
        (* prevent enlarging from_set after confirmation; TODO need to align this with paper? seems not ... *)
        (*
        let: cond := cf || (in_dec Address_eqdec src from) in
        let: from' := if cond then from else src :: from in
        let: lsigs' := if cond then lsigs else lsig :: lsigs in
        let: sigs' := if cond then sigs else sig :: sigs in
        let: cf' := cf || ((N - t0) <=? (length from')) in
        let: ps := (if cf'
          then broadcast n (LightConfirmMsg (v, lightsig_combine lsigs'))
          else nil) in
        let: st' := st <| conf := cf' |> <| from_set := from' |>
          <| collected_lightsigs := lsigs' |> <| collected_sigs := sigs' |> in
        Some (st', ps)
        *)
        (* FIXME: the broadcast here can be implemented as a check, though *)
        if cf
        then Some (st, broadcast n (LightConfirmMsg (v, lightsig_combine lsigs)))
        else 
          if in_dec Address_eqdec src from
          then None
          else
            let: cf' := (N - t0 <=? S (length from)) in
            let: ps' := if cf' then broadcast n (LightConfirmMsg (v, lightsig_combine (lsig :: lsigs))) else nil in
            let: st' := st <| conf := cf' |> <| from_set := src :: from |>
              <| collected_lightsigs := lsig :: lsigs |> <| collected_sigs := sig :: sigs |> in
            Some (st', ps')
      else None
    | None => 
      (* add to the buffer and wait *)
      let: st' := st <| msg_buffer := (src, msg) :: buffer |> in
      Some (st', nil)
    end
  | LightConfirmMsg lc =>
    let: (v, cs) := lc in
    if combined_verify v cs
    then 
      let: st' := st <| received_lightcerts := lc :: rlcerts |> in
      Some (st', nil)
    else None
  | ConfirmMsg c => 
    let: (v, nsigs) := c in
    (* check whether this is a valid full certificate or not *)
    (* in the paper this condition is ">= N-t0 distinct senders", 
        which is stronger than this *)
    if (ListDec.NoDup_dec AddrSigPair_eqdec nsigs) && ((N - t0) <=? (length nsigs)) && (verify_certificate v nsigs)
    then
      let: st' := st <| received_certs := c :: rcerts |> in
      Some (st', nil)
    else None
  end.

(* a simple wrapper *)

Definition procMsgWithCheck (st : State) (src : Address) (msg : Message) : State * list Packet :=
  match procMsg st src msg with
  | Some (st', ps) =>
    match msg with
    | SubmitMsg _ _ _ | LightConfirmMsg _ => (st', routine_check st' ++ ps)
    | _ => (st', ps)
    end
  | None => (st, nil) (* if the internal state does not change, then no need to do routine check *)
  end.

Definition procInt (st : State) (tr : InternalTransition) :=
  let: Node n cf ov from lsigs sigs rlcerts rcerts buffer := st in
  match tr with
  | SubmitIntTrans vthis => 
    (* making it happen at most once should make things easier *)
    match ov with
    | None =>
      (* let: vthis := value_bft n in *)
      let: ps := broadcast n 
        (SubmitMsg vthis (light_sign vthis (lightkey_map n)) (sign vthis (key_map n))) in
      let: st_start := st <| submitted_value := Some vthis |> <| msg_buffer := nil |> in
      (* also start to process all messages in the buffer *)
      (* not putting ps into the initial value of fold should be easier? *)
      let: (st', ps') := 
        fold_right
          (fun nmsg stps => let: (res1, res2) := procMsgWithCheck (fst stps) (fst nmsg) (snd nmsg) in
            (res1, res2 ++ snd stps)) (st_start, nil) buffer in
      (st', ps' ++ ps)
    | Some _ => (st, nil)
    end
  end.

End ACProtocol.

Module ACProtocolImpl (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (* (VBFT : ValueBFT A Sn V) *)
  (BTh : ByzThreshold A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (M : ACMessage A Sn V P TSS ACDT)
  (P0 : SimplePacket A M) <: Protocol A M P0 BTh <: ACProtocol A Sn V (* VBFT *) BTh P TSS0 TSS ACDT CC M P0.

Include ACProtocol A Sn V (* VBFT *) BTh P TSS0 TSS ACDT CC M P0.

End ACProtocolImpl.
