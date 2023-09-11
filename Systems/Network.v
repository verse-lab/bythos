From Coq Require Import List Lia.
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
Definition sig_seen_in_history (src : Address) (v : Value) (s : Signature) (pkts : PacketSoup) :=
  exists dst consumed ls, In (mkP src dst (SubmitMsg v ls s) consumed) pkts.

Definition cert_correct (psent : PacketSoup) (c : Certificate) :=
  let: (v, nsigs) := c in
  forall n sig, 
    In (n, sig) nsigs ->
    is_byz n = false ->
    verify v sig n -> (* this can be expressed in other way *)
    sig_seen_in_history n v sig psent. 

(* TODO the lightsig can actually be obtained from full certificates?
  guess this will not affect the following reasoning 
  (since full certificates are assembled from the sent messages), 
  so ignore it for now *)
Definition lightsig_seen_in_history (src : Address) (v : Value) (ls : LightSignature) (pkts : PacketSoup) :=
  exists dst consumed s, In (mkP src dst (SubmitMsg v ls s) consumed) pkts.

(* safety assumption about light certificates: 
  if the number of Byzantine nodes is not sufficiently large, 
  then the light signature is unforgeable *)
Definition lcert_correct (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  let: (v, cs) := lc in
  combined_verify v cs ->
  forall lsigs,
    cs = lightsig_combine lsigs ->
    forall n lsig,
      In lsig lsigs ->
      is_byz n = false ->
      light_verify v lsig n ->
      lightsig_seen_in_history n v lsig psent. 

Definition lcert_correct_threshold (psent : PacketSoup) (lc : LightCertificate) : Prop :=
  (num_byz < N - (t0 + t0) -> lcert_correct psent lc).

Definition consume (p : Packet) (psent : PacketSoup) :=
  (receive_pkt p) :: (List.remove Packet_eqdec p psent).

Inductive system_step_descriptor : Type :=
  | Idle | Deliver (p : Packet) 
  | Intern (proc : Address) (t : InternalTransition) 
  | ByzSubmit (src dst : Address) (v : Value) (ls : LightSignature) (s : Signature) 
  | ByzLightConfirm (src dst : Address) (lc : LightCertificate) 
  | ByzConfirm (src dst : Address) (c : Certificate)
.

(* TODO use this or indexed inductive relation?
    and put Coh inside the invariant or here?
*)
Inductive system_step (q : system_step_descriptor) (w w' : World) : Prop :=
| IdleStep of q = Idle & w = w'

| DeliverStep (p : Packet) of
      q = Deliver p &
      (* Coh w &  *)
      In p (sentMsgs w) &
      (* try modelling message duplication *)
      (* consumed p = false & *)
      (* require sender to be valid; although can also be managed in procMsg *)
      valid_node (src p) &
      valid_node (dst p) &
      is_byz (dst p) = false &
      let: (st', ms) := procMsgWithCheck (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               ((consume p (sentMsgs w)) ++ ms)

| InternStep (proc : Address) (t : InternalTransition) of
      q = Intern proc t &
      (* Coh w & *)
      valid_node proc &
      is_byz proc = false &
      let: (st', ms) := (procInt (localState w proc) t) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (sentMsgs w))

(* can possibly generate garbage in the following two trans *)
| ByzSubmitStep (src dst : Address) (v : Value) (ls : LightSignature) (s : Signature) of
      q = ByzSubmit src dst v ls s &
      (* Coh w & *)
      is_byz src &
      w' = mkW (localState w)
               ((mkP src dst (SubmitMsg v ls s) false) :: (sentMsgs w))

| ByzLightConfirmStep (src dst : Address) (lc : LightCertificate) of
      q = ByzLightConfirm src dst lc &
      (* Coh w & *)
      is_byz src &
      lcert_correct_threshold (sentMsgs w) lc &
      w' = mkW (localState w)
               ((mkP src dst (LightConfirmMsg lc) false) :: (sentMsgs w))

| ByzConfirmStep (src dst : Address) (c : Certificate) of
      q = ByzConfirm src dst c &
      (* Coh w & *)
      is_byz src &
      cert_correct (sentMsgs w) c &
      w' = mkW (localState w)
               ((mkP src dst (ConfirmMsg c) false) :: (sentMsgs w))
.

Fixpoint system_trace (w : World) (l : list (system_step_descriptor * World)) : Prop :=
  match l with
  | nil => True
  | (q, w') :: l' => system_step q w w' /\ system_trace w' l'
  end.

(* TODO It seems that with this condition, we then do not need the "tracking" components
    in the invariant. Is it really so? *)

(* like uniformly continuous, use a single n? *)
(* try use different n first *)
(* P provides sanity check *)
Definition reliable_condition (P : World -> Prop) :=
  forall p w, P w -> In p (sentMsgs w) ->
    (* only between honest nodes? *)
    valid_node (src p) -> valid_node (dst p) ->
    is_byz (src p) = false -> is_byz (dst p) = false ->
    exists n, forall l, system_trace w l -> n <= length l ->
      (* <= and = should be equivalent; may need to prove, though *)
      In (receive_pkt p) (sentMsgs (snd (last l (Idle, w)))).

Fact reliable_condition_for_pkts P (H : reliable_condition P) :
  forall pkts w, P w -> incl pkts (sentMsgs w) ->
    Forall (fun p => valid_node (src p)) pkts -> 
    Forall (fun p => valid_node (dst p)) pkts -> 
    Forall (fun p => is_byz (src p) = false) pkts -> 
    Forall (fun p => is_byz (dst p) = false) pkts -> 
    exists n, forall l, system_trace w l -> n <= length l ->
      incl (map receive_pkt pkts) (sentMsgs (snd (last l (Idle, w)))).
Proof.
  intros pkts.
  induction pkts as [ | p pkts IH ]; intros w Hp Hincl Ha Hb Hc Hd.
  - simpl.
    now exists 0.
  - rewrite -> Forall_cons_iff in *.
    destruct Ha as (Ha' & Ha), Hb as (Hb' & Hb), Hc as (Hc' & Hc), Hd as (Hd' & Hd).
    hnf in H, Hincl.
    simpl in Hincl.
    specialize (H _ _ Hp (Hincl _ (or_introl eq_refl)) Ha' Hb' Hc' Hd').
    destruct H as (n & H).
    specialize (IH _ Hp (fun x Hin => (Hincl x (or_intror Hin))) Ha Hb Hc Hd).
    destruct IH as (n0 & IH).
    exists (Nat.max n n0).
    intros.
    unfold incl.
    simpl.
    intros p0 [ <- | Hin ].
    + apply H; auto; try lia.
    + apply IH; auto; try lia.
Qed.

End ACNetwork.
