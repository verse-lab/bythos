From Coq Require Import Bool List.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address.

Module Type ACProtocol (A : NetAddr) (T : Types A).
Import T A.

Inductive Message := 
  | SubmitMsg (v : Value) (s : Signature)
  | ConfirmMsg (c : Certificate).

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros. decide equality.
  - apply Signature_eqdec.
  - apply Value_eqdec.
  - apply Certificate_eqdec.
Qed.

(* did not define msg type; seemingly it is not used in Toychain *)

(* only submit its own value so remember its node id is sufficient *)

Inductive InternalTransition :=
  | SubmitIntTrans.

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
    cert : Certificate; 
    received_certs : list Certificate
  }.

Definition State_eqdec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.
  intros. decide equality.
  - decide equality. apply Certificate_eqdec.
  - apply Certificate_eqdec.
  - decide equality.
  - apply Address_eqdec.
Qed.

Definition Init (n : Address) : State :=
  Node n false (value_bft n, nil) nil.

Definition broadcast (src : Address) (m : Message) :=
  (map (fun x => mkP src x m false) valid_nodes).

Definition verify_certificate v nsigs :=
  List.fold_right (fun nsig b => let: (n, sig) := nsig in b && (verify v sig n))
    true nsigs.

Definition certificate_valid v nsigs :=
  Forall (fun nsig => verify v (snd nsig) (fst nsig) = true) nsigs.

Fact In_broadcast src m p :
  In p (broadcast src m) <-> exists dst, valid_node dst /\ p = mkP src dst m false.
Proof. unfold broadcast. rewrite -> in_map_iff. firstorder. Qed.

Fact verify_certificateP v nsigs :
  verify_certificate v nsigs = true <-> certificate_valid v nsigs.
Proof.
  unfold verify_certificate.
  induction nsigs as [ | (n, sig) nsigs IH ].
  - simpl. 
    intuition constructor.
  - simpl.
    rewrite -> andb_true_iff, IH.
    unfold certificate_valid.
    now rewrite -> Forall_cons_iff.
Qed.

Definition procMsg (st : State) (src : Address) (msg : Message) : State * list Packet :=
  let: Node n conf cert rcerts := st in
  match msg with
  | SubmitMsg v sig => 
    let: (vthis, nsigs) := cert in
    if Value_eqdec v vthis 
    then
     (if verify v sig src
      then 
       (let: nsigs' := (if conf then nsigs else ((src, sig) :: nsigs)) in
        let: conf' := (Nat.leb (N - t0) (length nsigs')) in
        let: ps := (if conf' 
          then broadcast n (ConfirmMsg (v, nsigs'))
          else nil) in
        let: st' := Node n conf' (vthis, nsigs') rcerts in
        (st', ps))
      else (st, nil))
    else (st, nil)
  | ConfirmMsg c => 
    let: (v, nsigs) := c in
    if verify_certificate v nsigs
    then 
      let: st' := Node n conf cert (c :: rcerts) in
      (st', nil)
    else (st, nil)
  end.

Definition procInt (st : State) (tr : InternalTransition) :=
  let: Node n conf cert rcerts := st in
  match tr with
  | SubmitIntTrans => 
    let: (vthis, _) := cert in
    let: ps := broadcast n (SubmitMsg vthis (sign vthis (key_map n))) in
    (st, ps)
  end.

End ACProtocol.
