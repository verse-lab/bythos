From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export States.

(* constraints are synthetic ...? *)

Module Type Adversary (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export Pr : Protocol A M P) (Export Ns : NetState A M P Pr).

(* FIXME: do we need to consider the case where a Byzantine node sends out multiple messages
    in one step? currently do not, since that would be equivalent with multiple steps *)
Parameter byz_constraints : Message -> World -> Prop.

End Adversary.

Module Type Network (Export A : NetAddr) (Export M : MessageType) 
  (Export P : SimplePacket A M) (Export Pr : Protocol A M P) (Export Ns : NetState A M P Pr) 
  (Export Adv : Adversary A M P Pr Ns).

Inductive system_step_descriptor : Type :=
  | Idle (* stuttering *)
  | Deliver (p : Packet) 
  | Intern (proc : Address) (t : InternalTransition) 
  | Byz (src dst : Address) (m : Message)
.

(* TODO may have different consumption models? *)
Definition consume (p : Packet) (psent : PacketSoup) :=
  (receive_pkt p) :: (List.remove Packet_eqdec p psent).

(* TODO use this or indexed inductive relation? *)
Inductive system_step (q : system_step_descriptor) (w w' : World) : Prop :=
| IdleStep of q = Idle & w = w'

| DeliverStep (p : Packet) of
      q = Deliver p &
      In p (sentMsgs w) &
      (* try modelling message duplication by not checking whether p has been consumed or not *)
      (* FIXME: parameterizing here shall result in different models *)
      (* FIXME: the order of packets should really do not matter! 
        so the proof related with "In" should not be very specific. 
        any way to formalize that notion? *)
      is_byz (dst p) = false &
      let: (st', ms) := procMsgWithCheck (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               ((consume p (sentMsgs w)) ++ ms)

| InternStep (proc : Address) (t : InternalTransition) of
      q = Intern proc t &
      is_byz proc = false &
      let: (st', ms) := (procInt (localState w proc) t) in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (sentMsgs w))

| ByzStep (src dst : Address) (m : Message) of
      q = Byz src dst m &
      is_byz src &
      byz_constraints m w &
      w' = mkW (localState w)
               (mkP src dst m false :: (sentMsgs w))
.

(* inversion lemmas *)

Fact DeliverStep_inv p w w' (H : system_step (Deliver p) w w') :
  In p (sentMsgs w) /\ is_byz (dst p) = false /\
  exists st' ms, procMsgWithCheck (localState w (dst p)) (src p) (msg p) = (st', ms) /\
    w' = mkW (upd (dst p) st' (localState w)) (consume p (sentMsgs w) ++ ms).
Proof.
  inversion H; try discriminate.
  match goal with HH : Deliver _ = Deliver _ |- _ => injection HH as <- end.
  rewrite (surjective_pairing (procMsgWithCheck _ _ _)) in *.
  do 2 (split; try assumption).
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
  3: simpl; now right.
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
  is_byz (src p) = false /\ is_byz (dst p) = false.

Fact good_packet_dec p : {good_packet p} + {~ good_packet p}.
Proof.
  unfold good_packet.
  destruct (is_byz (src p)), (is_byz (dst p)); auto.
  all: now right.
Qed.

Fact pkt_le_good_packet p p' : pkt_le p p' -> good_packet p <-> good_packet p'.
Proof. intros [ -> | -> ]. all: destruct p; intuition. Qed.

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

Fact true_is_invariant : is_invariant_step (fun _ => True).
Proof. now hnf. Qed.

Fact reachable_is_invariant : is_invariant_step reachable.
Proof. intros ? ? ? ? ?. eapply ReachableStep; eauto. Qed.

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
        apply in_in_remove; try assumption.
        now intros ->.
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

End Network.

Module NetworkImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export P : SimplePacket A M) (Export Pr : Protocol A M P) (Export Ns : NetState A M P Pr) 
  (Export Adv : Adversary A M P Pr Ns) <: Network A M P Pr Ns Adv.

Include Network A M P Pr Ns Adv.

End NetworkImpl.
