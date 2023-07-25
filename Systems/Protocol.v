From Coq Require Import Bool List ssrbool.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address ListFacts.

Module Type ACProtocol (A : NetAddr) (T : Types A).
Import T A.

Inductive Message := 
  | SubmitMsg (v : Value) (ls : LightSignature) (s : Signature)
  | LightConfirmMsg (c : LightCertificate)
  (* for historical reasons, this remains the name as "ConfirmMsg". *)
  | ConfirmMsg (c : Certificate).

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros. decide equality.
  - apply Signature_eqdec.
  - apply LightSignature_eqdec.
  - apply Value_eqdec.
  - apply LightCertificate_eqdec.
  - apply Certificate_eqdec.
Qed.

(* did not define msg type; seemingly it is not used in Toychain *)

(* only submit its own value so remember its node id is sufficient *)

Inductive InternalTransition :=
  | SubmitIntTrans | LightCertCheckIntTrans.
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

Record Packet := mkP {src: Address; dst: Address; msg: Message; consumed: bool}.

Definition receive_pkt p :=
  let: mkP src dst msg _ := p in mkP src dst msg true.

Definition Packet_eqdec : forall (p1 p2 : Packet), {p1 = p2} + {p1 <> p2}.
  intros. decide equality.
  - decide equality.
  - apply Message_eqdec.
  - apply Address_eqdec.
  - apply Address_eqdec.
Qed.

(* TODO assume peers are already known? *)

Record State :=
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
    received_certs : list Certificate
  }.

Definition State_eqdec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.
  intros. decide equality.
  - decide equality. apply Certificate_eqdec.
  - decide equality. apply LightCertificate_eqdec.
  - decide equality. apply Signature_eqdec.
  - decide equality. apply LightSignature_eqdec.
  - decide equality. apply Address_eqdec.
  - decide equality. apply Value_eqdec.
  - decide equality.
  - apply Address_eqdec.
Qed.

Definition Init (n : Address) : State :=
  Node n false None nil nil nil nil nil.

Definition broadcast (src : Address) (m : Message) :=
  (map (fun x => mkP src x m false) valid_nodes).

Fact In_broadcast src m p :
  In p (broadcast src m) <-> exists dst, valid_node dst /\ p = mkP src dst m false.
Proof. unfold broadcast. rewrite -> in_map_iff. firstorder. Qed.

Definition valid_addr_sig_pair v nsig : Prop :=
  let: (n, sig) := nsig in valid_node n /\ verify v sig n.

Definition certificate_valid v nsigs : Prop :=
  Forall (valid_addr_sig_pair v) nsigs.

Definition verify_certificate v nsigs : {certificate_valid v nsigs} + {~ certificate_valid v nsigs}.
  unfold certificate_valid.
  apply Forall_dec. (* there is no existing Forall2_dec *)
  intros (n, sig).
  simpl.
  unfold valid_node.
  destruct (In_dec Address_eqdec n valid_nodes) as [ ? | ? ], (verify v sig n) eqn:?.
  all: intuition.
Qed.

Definition valid_addr_lsig_pair v nlsig : Prop :=
  let: (n, lsig) := nlsig in valid_node n /\ light_verify v lsig n.

Definition light_signatures_valid v nlsigs : Prop :=
  Forall (valid_addr_lsig_pair v) nlsigs.

(*
Definition verify_certificate v nsigs :=
  (* add an additional check that the nodes in nsigs are valid *)
  List.fold_right (fun nsig b => let: (n, sig) := nsig in b && (is_valid_node n) && (verify v sig n))
    true nsigs.

Definition certificate_valid v nsigs :=
  Forall (fun nsig => valid_node (fst nsig) /\ verify v (snd nsig) (fst nsig)) nsigs.

Fact verify_certificateP v nsigs :
  verify_certificate v nsigs <-> certificate_valid v nsigs.
Proof.
  unfold verify_certificate.
  induction nsigs as [ | (n, sig) nsigs IH ].
  - simpl. 
    intuition constructor.
  - simpl.
    unfold certificate_valid, is_valid_node, is_true.
    rewrite -> ! andb_true_iff, Forall_cons_iff, IH.
    now destruct (in_dec Address_eqdec n valid_nodes) as [ Hin | Hnotin ].
Qed.
*)

Definition zip_from_lsigs (st : State) := 
  List.combine st.(from_set) st.(collected_lightsigs).

Definition zip_from_sigs (st : State) := 
  List.combine st.(from_set) st.(collected_sigs).

Definition zip_from_lsigs_sigs (st : State) := 
  List.combine (List.combine st.(from_set) st.(collected_lightsigs)) st.(collected_sigs).

Definition procMsg (st : State) (src : Address) (msg : Message) : State * list Packet :=
  let: Node n conf ov from lsigs sigs rlcerts rcerts := st in
  match msg with
  | SubmitMsg v lsig sig =>
    match ov with 
    | Some vthis => 
      if Value_eqdec v vthis 
      then
        (if verify v sig src
        then 
          (if light_verify v lsig src
          then 
            (* before prepending, add a check to avoid adding a duplicate node-signature pair *)
            (* checking In fst or In pair should be the same, due to the correctness of verify *)
            (* let: in_from := In_dec Address_eqdec src (map fst nsigs) in *)
            let: in_from := In_dec Address_eqdec src from in
            let: from' := if conf || in_from then from else src :: from in
            let: lsigs' := if conf || in_from then lsigs else lsig :: lsigs in
            let: sigs' := if conf || in_from then sigs else sig :: sigs in
            let: conf' := (Nat.leb (N - t0) (length from')) in
            let: ps := (if conf' 
              then broadcast n (LightConfirmMsg (v, lightsig_combine lsigs'))
              else nil) in
            let: st' := Node n conf' ov from' lsigs' sigs' rlcerts rcerts in
            (st', ps)
          else (st, nil))
        else (st, nil))
      else (st, nil)
    | None => (st, nil)
    end
  | LightConfirmMsg lc =>
    let: (v, cs) := lc in
    if combined_verify v cs
    then 
      let: st' := Node n conf ov from lsigs sigs (lc :: rlcerts) rcerts in
      (st', nil)
    else (st, nil)
  | ConfirmMsg c => 
    let: (v, nsigs) := c in
    (* check whether this is a valid full certificate or not *)
    (* in the paper this condition is ">= N-t0 distinct senders", 
        which is stronger than this *)
    if NoDup_eqdec AddrSigPair_eqdec nsigs
    then 
      (if Nat.leb (N - t0) (length nsigs) 
      then
        (if verify_certificate v nsigs
        then 
          let: st' := Node n conf ov from lsigs sigs rlcerts (c :: rcerts) in
          (st', nil)
        else (st, nil))
      else (st, nil))
    else (st, nil)
  end.

Definition procInt (st : State) (tr : InternalTransition) :=
  let: Node n conf ov from lsigs sigs rlcerts rcerts := st in
  match tr with
  | SubmitIntTrans => 
    let: vthis := value_bft n in
    let: ps := broadcast n 
      (SubmitMsg vthis (light_sign vthis (lightkey_map n)) (sign vthis (key_map n))) in
    (Node n conf (Some vthis) from lsigs sigs rlcerts rcerts, ps)
  | LightCertCheckIntTrans =>
    match ov with 
    | Some vthis => 
      if conf
      then 
        (if lightcert_conflict_check rlcerts
        then 
        (* send out full certificates only in this case *)
          let: ps := broadcast n (ConfirmMsg (vthis, zip_from_sigs st)) in
          (st, ps)
        else (st, nil))
      else (st, nil)
    | None => (st, nil)
    end
  end.

End ACProtocol.
