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

(* inversion lemmas *)

Fact DeliverStep_inv p w w' (H : system_step (Deliver p) w w') :
  In p (sentMsgs w) /\ valid_node (src p) /\ valid_node (dst p) /\ is_byz (dst p) = false /\
  exists st' ms, procMsgWithCheck (localState w (dst p)) (src p) (msg p) = (st', ms) /\
    w' = mkW (upd (dst p) st' (localState w)) (consume p (sentMsgs w) ++ ms).
Proof.
  inversion H; try discriminate.
  match goal with HH : Deliver _ = Deliver _ |- _ => injection HH as <- end.
  rewrite (surjective_pairing (procMsgWithCheck _ _ _)) in *.
  do 4 (split; try assumption).
  do 2 eexists.
  split; [ reflexivity | assumption ].
Qed.

(* put the two properties here, since they are only related to the packet soup
  (i.e., irrelevant with concrete network transitions) and the notion of packet 
  (i.e., irrelevant with concrete messages); 
  so the two properties should hold on all modelling based on packet soup and packet 
*)

Corollary consume_norevert p p' psent (Hin : In (receive_pkt p) psent) :
  In (receive_pkt p) (consume p' psent).
Proof.
  destruct (Packet_eqdec (receive_pkt p) p') as [ <- | ]; simpl.
  - destruct p; simpl; tauto.
  - right.
    now apply in_in_remove.
Qed.

Fact system_step_psent_norevert p w w' q : 
  In (receive_pkt p) (sentMsgs w) -> system_step q w w' -> In (receive_pkt p) (sentMsgs w').
Proof.
  intros H Hstep.
  inversion Hstep; subst; auto.
  3-5: simpl; now right.
  1: destruct (procMsgWithCheck _ _ _) in *.
  2: destruct (procInt _ _) in *.
  all: subst w'.
  all: cbn delta -[consume] beta iota.
  all: rewrite ! in_app_iff.
  - left.
    now apply consume_norevert.
  - now right.
Qed.

(* two multistep propositions *)

Fixpoint system_trace (w : World) (l : list (system_step_descriptor * World)) : Prop :=
  match l with
  | nil => True
  | (q, w') :: l' => system_step q w w' /\ system_trace w' l'
  end.

Definition final_world (w : World) (l : list (system_step_descriptor * World)) := (snd (last l (Idle, w))).

Fact system_trace_app w l1 l2 :
  system_trace w (l1 ++ l2) <-> system_trace w l1 /\ system_trace (final_world w l1) l2.
Proof.
  revert w l2.
  induction l1 as [ | (q, w') l1 IH ] using rev_ind; intros.
  - now unfold final_world.
  - unfold final_world.
    rewrite <- app_assoc, ! IH, last_last.
    now simpl.
Qed.

Fact final_world_app w l1 l2 : final_world (final_world w l1) l2 = final_world w (l1 ++ l2).
Proof.
  revert w l1.
  induction l2 as [ | (q, w') l2 IH ] using rev_ind; intros. (* induction is not needed *)
  - rewrite app_nil_r.
    now unfold final_world.
  - unfold final_world.
    now rewrite -> app_assoc, ! last_last.
Qed.

Fact final_world_cons w q w' l : final_world w ((q, w') :: l) = final_world w' l.
Proof.
  change (_ :: l) with (((q, w') :: nil) ++ l).
  rewrite <- final_world_app.
  reflexivity.
Qed.

(*
Fact system_trace_psent_norevert p : forall w (H : In (receive_pkt p) (sentMsgs w)) 
  l (Htrace : system_trace w l), In (receive_pkt p) (sentMsgs (final_world w l)).
Proof.
  intros w H l.
  revert w H.
  induction l as [ | (q, w_) l IH ] using rev_ind; intros; simpl; auto.
  rewrite <- final_world_app.
  unfold final_world.
  simpl.
  rewrite system_trace_app in Htrace.
  simpl in Htrace.
  destruct Htrace as (Htrace & Hstep & _).
  eapply system_step_psent_norevert.
  2: apply Hstep.
  now apply IH.
Qed.
*)
Inductive reachable : World -> Prop :=
  | ReachableInit : reachable initWorld
  | ReachableStep q (w w' : World) (Hstep : system_step q w w')
    (H_w_reachable : reachable w) : reachable w'.

Fact reachable_witness w : reachable w <-> exists l, system_trace initWorld l /\ w = final_world initWorld l.
Proof.
  split.
  - intros H.
    induction H as [ | q w w' Hstep H_w_reachable IH ].
    + now exists nil.
    + destruct IH as (l & H1 & H2).
      exists (l ++ ((q, w') :: nil)).
      unfold final_world.
      rewrite system_trace_app, last_last, <- H2.
      now simpl.
  - intros (l & H & ->).
    induction l as [ | (q, w) l IH ] using rev_ind; unfold final_world; try constructor.
    rewrite last_last.
    simpl.
    rewrite system_trace_app in H.
    simpl in H.
    econstructor.
    2: apply IH.
    1: apply H.
    tauto.
Qed.

Definition good_packet p := 
  valid_node (src p) /\ valid_node (dst p) /\
  is_byz (src p) = false /\ is_byz (dst p) = false.

Fact good_packet_dec p : {good_packet p} + {~ good_packet p}.
Proof.
  unfold good_packet, valid_node.
  destruct (in_dec Address_eqdec (src p) valid_nodes), 
    (in_dec Address_eqdec (dst p) valid_nodes), 
    (is_byz (src p)), (is_byz (dst p)); auto.
  all: now right.
Qed.

Fact pkt_le_good_packet p p' : pkt_le p p' -> good_packet p <-> good_packet p'.
Proof. intros [ -> | -> ]. all: destruct p; intuition. Qed.

(*
(* this should be close enough *)
(* making P decidable should be good; we typically make P be (modulo) a finite subset here *)
(* somewhat, a weird "coinduction" *)
Inductive rel_com (P : Packet -> bool) : World -> list (system_step_descriptor * World) -> Prop :=
  | RC_Done : forall w l, 
    (* all must delivered; though we can make something else, but not do that for now *)
    (forall p, good_packet p -> P p -> In (receive_pkt p) (sentMsgs w)) ->
    system_trace w l -> (* is this truly needed? add it for now *)
    rel_com P w l
  | RC_Go : forall p w l w' l', 
    good_packet p -> P p -> In p (sentMsgs w) ->
    system_trace w l -> 
    system_trace w' l' -> 
    w' = final_world w l ->
    In (receive_pkt p) (sentMsgs w') ->
    rel_com P w' l' ->
    rel_com P w (l ++ l').

Definition rel_com_finset pkts w l := rel_com (fun p => in_dec Packet_eqdec p pkts) w l.

Definition modulo_is_fin [A : Type] (P : A -> Prop) :=
  exists (rep : list A) (B : Type) (f : A -> B), 
    forall a, P a <-> (exists a', P a' /\ In a' rep /\ f a = f a').

(* TODO comm complexity? *)
(*
Definition rel_com_fin P w l := 
  modulo_is_fin (fun p => is_true (P p)) -> rel_com P w l.
*)

Fact rel_com_finset_extendable w l pkts (H : rel_com_finset pkts w l) :
  forall l', system_trace (final_world w l) l' -> rel_com_finset pkts w (l ++ l').
Proof.
  induction H; subst; intros; unfold rel_com_finset in *.
  - apply RC_Done; try assumption.
    now apply system_trace_app.
  - rewrite <- app_assoc.
    rewrite <- final_world_app in *.
    eapply RC_Go; eauto.
    now apply system_trace_app. 
Qed.

(* justifying that this definition is not a bogus *)
Fact rel_com_finset_inhabitant w pkts : exists l, rel_com_finset pkts w l.
Proof.
  induction pkts as [ | p pkts (l & H) ]; intros; unfold rel_com_finset in *.
  - exists nil.
    apply RC_Done.
    2: simpl; auto.
    now apply Forall_forall.
  - pose proof ().
    exists (l ++ ()).

Fact rel_com_extendable w l pkts (H : system_trace w l) :
  exists l', rel_com (fun p => in_dec Packet_eqdec p pkts) w (l ++ l').
Proof.
  *)

(*
Inductive eventually (P : World -> Prop) : World -> list (system_step_descriptor * World) -> nat -> Prop :=
  | EV_O : forall w l, eventually P w l O
  | EV_S : forall w l m n, 
    system_trace w l -> 
    P (final_world w (firstn m l)) ->
    eventually P (final_world w (firstn m l)) (skipn m l) n ->
    eventually P w l (S n).
*)

(* THIS IMPLIES FALSE! *)
(*
Definition eventually w (P : World -> Prop) : Prop :=
  (* <= and = should be equivalent; may need to prove, though *)
  exists n, forall l, system_trace w l -> n <= length l -> P (final_world w l).
*)
(* going more generic *)
(* HMM probably, make this typeclass *)

Definition is_invariant_trace (P : World -> Prop) : Prop :=
  forall w l, P w -> system_trace w l -> P (final_world w l).

Definition is_invariant_step (P : World -> Prop) : Prop :=
  forall q w w', P w -> system_step q w w' -> P w'.

Fact is_invariant_step_trace (P : World -> Prop) :
  is_invariant_trace P <-> is_invariant_step P.
Proof.
  unfold is_invariant_trace, is_invariant_step.
  split.
  - intros H q w w' Hp Hstep.
    specialize (H w ((q, w') :: nil) Hp).
    now apply H.
  - intros H w l Hp Htrace.
    induction l as [ | (q, w') l IH ] using rev_ind; auto.
    unfold final_world.
    rewrite last_last.
    simpl.
    rewrite system_trace_app in Htrace.
    simpl in Htrace.
    destruct Htrace as (Htrace & Hstep & _).
    clear Hp.
    specialize (IH Htrace).
    eapply H; eauto.
Qed.

Corollary psent_norevert_is_invariant p : is_invariant_step (fun w => In (receive_pkt p) (sentMsgs w)).
Proof. hnf. intros ???. apply system_step_psent_norevert. Qed.

Corollary psent_norevert_pkts_is_invariant pkts : is_invariant_step (fun w => incl (map receive_pkt pkts) (sentMsgs w)).
Proof.
  induction pkts as [ | p pkts IH ]; hnf; unfold incl; simpl; intros.
  1: contradiction.
  destruct H1 as [ <- | H1 ].
  - eapply system_step_psent_norevert; eauto.
  - eapply IH; eauto.
    hnf.
    intros; eapply H; eauto.
Qed.

(* somewhat calculus of invariant? *)

(* bad *)
(*
Fact eventually_mp_by_app (P Q : World -> Prop) w (Hp : eventually w P)
  (Hpq : forall l (Htrace : system_trace w l) w' (Efw : w' = final_world w l)
    (H : P w'), eventually w' Q) : eventually w (fun w' => eventually w' Q).
Proof.
  destruct Hp as (n & Hp).
  exists n.
  intros l Htrace Hle.
  specialize (Hp _ Htrace Hle).
  now specialize (Hpq _ Htrace _ eq_refl Hp).
Qed.
*)
Fact is_invariant_implconj (P Q : World -> Prop) (Hisinv : is_invariant_step P) 
  (Hpq : forall w, P w -> Q w) : is_invariant_step (fun w => P w /\ Q w).
Proof.
  hnf in Hisinv |- *.
  intros.
  destruct H.
  split.
  1: eapply Hisinv; eauto.
  eapply Hpq, Hisinv; eauto.
Qed.
(*
Fact eventually_mp_by_invariant (P Q Inv : World -> Prop) (Hisinv : is_invariant_step Inv) :
  (forall w, Inv w -> P w -> Q w) -> forall w, Inv w -> eventually w P -> eventually w Q.
Proof.
  intros.
  hnf in H1 |- *.
  destruct H1 as (n & H1).
  exists n.
  intros.
  specialize (H1 _ H2 H3).
  revert H1.
  apply H.
  apply is_invariant_step_trace in Hisinv.
  now apply Hisinv.
Qed.
*)
Fact true_is_invariant : is_invariant_step (fun _ => True).
Proof. now hnf. Qed.

Fact reachable_is_invariant : is_invariant_step reachable.
Proof. intros ? ? ? ? ?. eapply ReachableStep; eauto. Qed.

(*
Fact eventually_mp_ (P Q : World -> Prop) : (forall w, P w -> Q w) -> forall w, eventually w P -> eventually w Q.
Proof.
  intros.
  hnf in H0 |- *.
  destruct H0 as (n & H0).
  exists n.
  intros.
  specialize (H0 _ H1 H2).
  revert H0.
  apply H.
Qed.

Fact eventually_mp_reachable (P Q : World -> Prop) : 
  (forall w, reachable w -> P w -> Q w) -> forall w, reachable w -> eventually w P -> eventually w Q.
Proof.
  intros.
  hnf in H1 |- *.
  destruct H1 as (n & H1).
  exists n.
  intros.
  specialize (H1 _ H2 H3).
  revert H1.
  apply H.
  rewrite reachable_witness in H0 |- *.
  destruct H0 as (l0 & Ha & ->).
  exists (l0 ++ l).
  rewrite system_trace_app.
  split; try tauto.
  apply final_world_app.
Qed.
*)

(* TODO It seems that with this condition, we then do not need the "tracking" components
    in the invariant. Is it really so? *)

(* like uniformly continuous, use a single n? *)
(* try use different n first *)
(* P provides sanity check *)
(*
Definition reliable_condition (P : World -> Prop) :=
  forall p w, P w -> In p (sentMsgs w) -> good_packet p ->
    (* only between honest nodes? *)
    eventually w (fun w' => In (receive_pkt p) (sentMsgs w')).

(* lists: decided subset *)
Fact reliable_condition_for_pkts P (H : reliable_condition P) :
  forall pkts w, P w -> incl pkts (sentMsgs w) ->
    (* Forall (fun p => valid_node (src p)) pkts -> 
    Forall (fun p => valid_node (dst p)) pkts -> 
    Forall (fun p => is_byz (src p) = false) pkts -> 
    Forall (fun p => is_byz (dst p) = false) pkts ->  *)
    Forall good_packet pkts ->
    eventually w (fun w' => incl (map receive_pkt pkts) (sentMsgs w')).
    (* exists n, forall l, system_trace w l -> n <= length l ->
      incl (map receive_pkt pkts) (sentMsgs (final_world w l)). *)
Proof.
  intros pkts.
  induction pkts as [ | p pkts IH ]; intros w Hp Hincl HH.
  - simpl.
    now exists 0.
  - rewrite -> Forall_cons_iff in *.
    destruct HH as (HH' & HH).
    hnf in H, Hincl.
    simpl in Hincl.
    specialize (H _ _ Hp (Hincl _ (or_introl eq_refl)) HH').
    destruct H as (n & H).
    specialize (IH _ Hp (fun x Hin => (Hincl x (or_intror Hin))) HH).
    destruct IH as (n0 & IH).
    exists (Nat.max n n0).
    intros.
    unfold incl.
    simpl.
    intros p0 [ <- | Hin ].
    + apply H; auto; try lia.
    + apply IH; auto; try lia.
Qed.
*)

(* simple existence condition; avoiding some vacuous cases *)
(* ... but does not justify "fairness => liveness" *)
(* this should be generalizable to any system with the same model *)

Fact list_packets_deliverable pkts w
  (Hgood : Forall good_packet pkts) (Hincl : incl pkts (sentMsgs w)) :
  exists l, system_trace w l /\
    incl (map receive_pkt pkts) (sentMsgs (final_world w l)).
Proof.
  revert w Hincl.
  induction Hgood as [ | p pkts Hg Hgood IH ]; intros.
  - now exists nil.
  - destruct (procMsgWithCheck (localState w (dst p)) (src p) (msg p)) as (st', ms) eqn:E.
    pose (w' := 
      if (in_dec Packet_eqdec p pkts)
      then w else (mkW (upd (dst p) st' (localState w)) ((consume p (sentMsgs w)) ++ ms))).
    assert (incl pkts (sentMsgs w')) as Htmp.
    { subst w'.
      destruct (in_dec Packet_eqdec p pkts) as [ Hin | Hnotin ]; simpl; hnf in Hincl |- *.
      - firstorder.
      - intros p' Hin'.
        simpl; rewrite in_app_iff.
        specialize (Hincl _ (or_intror Hin')).
        right; left.
        apply in_in_remove; congruence.
    }
    specialize (IH _ Htmp).
    destruct IH as (l & Htrace & Hres).
    exists (if (in_dec Packet_eqdec p pkts) then l else ((Deliver p, w') :: l)).
    destruct (in_dec Packet_eqdec p pkts) as [ Hin | Hnotin ]; subst w'.
    + split; try assumption.
      hnf in Hres |- *.
      simpl.
      intros p' [ <- | Hin' ].
      * now apply Hres, in_map.
      * now apply Hres.
    + split.
      * cbn delta [system_trace] iota beta.
        split; try assumption.
        hnf in Hg.
        apply DeliverStep with (p:=p); try reflexivity; try tauto.
        1: apply (Hincl _ (or_introl eq_refl)).
        now rewrite E.
      * rewrite final_world_cons.
        hnf in Hres |- *.
        intros p' [ <- | Hin' ]; auto.
        (* use the invariant *)
        pose proof (psent_norevert_is_invariant p) as HH%is_invariant_step_trace.
        apply HH; try assumption.
        simpl; tauto.
Qed.

End ACNetwork.
