From Coq Require Import List Lia RelationClasses Morphisms.
From Bythos.Systems Require Export Protocol.

Module Type NetState (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export BTh : ByzThreshold A) (Export Pr : Protocol A M P BTh).

(* using a map library seems to be overkill, so use some simple definitions instead *)

Definition StateMap := Address -> State. 

Definition upd (n : Address) (st : State) (states : StateMap) : StateMap :=
  Eval unfold map_update in map_update Address_eqdec n st states.

Fact upd_refl n st stmap : upd n st stmap n = st.
Proof. now apply map_update_refl. Qed.

Fact upd_intact n n' stmap : upd n' (stmap n') stmap n = stmap n.
Proof. now apply map_update_intact. Qed.

(* if to parameterize this, then need some module type about finite multiset? *)
(* currently, let's stick to list *)
Definition PacketSoup := list Packet.

(* holistic network state *)
Record SystemState :=
  mkW {
    localState : StateMap;
    packetSoup : PacketSoup;
  }.

Definition initSystemState := mkW initState nil.

(* some handy notation *)
Global Notation "w '@' n" := (localState w n) (at level 50, left associativity).

(* pointwise eq *)
Definition stmap_peq (stmap stmap' : StateMap) : Prop :=
  forall n, stmap n = stmap' n.

Definition SystemState_rel (w w' : SystemState) : Prop := Eval unfold stmap_peq in
  stmap_peq (localState w) (localState w') /\ Ineq (packetSoup w) (packetSoup w').

(* FIXME: there should be some algebraic thing describing such prop. what is it? *)
Definition stmap_peq_cong (P : SystemState -> Prop) : Prop :=
  forall w w', stmap_peq (localState w) (localState w') -> P w -> P w'.

Definition SystemState_rel_cong (P : SystemState -> Prop) : Prop :=
  forall w w', SystemState_rel w w' -> P w -> P w'.

Fact stmap_peq_cong_implies_SystemState_rel_cong P : stmap_peq_cong P -> SystemState_rel_cong P.
Proof. intros H. hnf in H |- *. intros ?? (H0 & _). now specialize (H _ _ H0). Qed.

(* using Global to help it penetrate nested modules *)
Global Instance Equivalence_SystemState_rel : Equivalence SystemState_rel.
Proof.
  constructor; hnf.
  - intros. hnf; split; intros; reflexivity.
  - intros x y (H & H0). hnf. split; intros; rewrite ?H, ?H0; reflexivity.
  - intros x y z (H & H0) (H' & H0'). hnf. split; intros; rewrite ?H, ?H0, ?H', ?H0'; reflexivity.
Qed.

Global Tactic Notation "simpl_sysstate" := simpl localState in *; simpl packetSoup in *.

Global Tactic Notation "rewrite_w_expand" ident(w) "in_" hyp(H) :=
  replace w with (mkW (localState w) (packetSoup w)) in H by (now destruct w).

Global Tactic Notation "destruct_localState" ident(w) ident(n) "as_" simple_intropattern(pat) "eqn_" ident(E) :=
  match goal with 
  | H : ?P |- _ =>
    let Htmp := fresh "Htmp" in
    pose proof (H n) as Htmp;
    destruct (localState w n) as pat eqn:E; 
    simpl in Htmp; 
    match type of Htmp with ?nn = _ => subst nn end
  end.

Global Tactic Notation "destruct_localState" ident(w) ident(n) "as_" simple_intropattern(pat) :=
  let E := fresh "E" in
  (destruct_localState w n as_ pat eqn_ E); clear E.

(* ask: can a faulty node produce something with type A, which meets some requirement P, 
    by just using what is in the system state? *)
(* do not really make sense to give a proof saying that if produ_check holds, then P holds.
    this definition can be just taken as premise in some proofs *)
(* in particular, it can be used to describe the adversary capability in the Dolev-Yao style *)
Class producible (A : Type) (P : A -> Prop) :=
  produ_check : SystemState -> A -> Prop.

End NetState.

(* the two modules are here since they are about packet soup, but that might not be a good reason *)
(* FIXME: maybe the following modularization is superfluous?
    the intention for the modularization is merely for hiding the details of sendout/consume, though. 
    maybe need to move them inside some module, instead of making them top-level *)
Module Type PacketSoupOperations (Export P : PacketType).

(* indicating that our proof does not rely on concrete maintaining methods of packet soup,
    as long as those methods satisfy certain properties *)

Parameter sendout1 : Packet -> list Packet -> list Packet.
Parameter sendout : list Packet -> list Packet -> list Packet.

Axiom In_sendout1 : forall p psent p', In p' (sendout1 p psent) <-> p = p' \/ In p' psent.
Axiom In_sendout : forall pkts psent p, In p (sendout pkts psent) <-> In p pkts \/ In p psent.
Axiom sendout0 : forall psent, sendout nil psent = psent.
(* not sure if this is good for autorewrite? *)

Create HintDb psent.

Global Hint Rewrite -> In_sendout1 In_sendout in_app_iff in_cons_iff : psent.

End PacketSoupOperations.

Module PacketSoupOperationsImpl (Export P : PacketType) : PacketSoupOperations P.

Definition sendout1 : Packet -> list Packet -> list Packet := cons.
Definition sendout : list Packet -> list Packet -> list Packet := @List.app Packet.

Fact In_sendout1 : forall p psent p', In p' (sendout1 p psent) <-> p = p' \/ In p' psent.
Proof. intros. reflexivity. Qed.

Fact In_sendout : forall pkts psent p, In p (sendout pkts psent) <-> In p pkts \/ In p psent.
Proof. intros. unfold sendout. now rewrite in_app_iff. Qed.

Fact sendout0 : forall psent, sendout nil psent = psent.
Proof (fun _ => eq_refl).

End PacketSoupOperationsImpl.

Module PacketSoupOperationsLemmas (Export P : PacketType) (Export PSOp : PacketSoupOperations P).

Fact incl_sendout_l (l1 l2 : list Packet) : incl l1 (sendout l1 l2).
Proof. hnf. intros. rewrite In_sendout. now left. Qed.

Fact incl_sendout_r (l1 l2 : list Packet) : incl l1 (sendout l2 l1).
Proof. hnf. intros. rewrite In_sendout. now right. Qed.

Fact incl_sendout_app_l (l l1 l2 l3 : list Packet) (H : incl l (sendout l1 l3)) :
  incl l (sendout (l1 ++ l2) l3).
Proof. hnf in H |- *. intros a HH. specialize (H _ HH). rewrite In_sendout in H |- *. rewrite in_app_iff. tauto. Qed.

Fact incl_sendout_app_r (l l1 l2 l3 : list Packet) (H : incl l (sendout l2 l3)) :
  incl l (sendout (l1 ++ l2) l3).
Proof. hnf in H |- *. intros a HH. specialize (H _ HH). rewrite In_sendout in H |- *. rewrite in_app_iff. tauto. Qed.

End PacketSoupOperationsLemmas.

Module Type PacketConsumption (Export A : NetAddr) (Export M : MessageType) (Export P : SimplePacket A M).

(* since we distinguish between packets that have been received and packets that have not been received,
    we need some mechanism to mark a packet as received *)

Parameter consume : Packet -> list Packet -> list Packet.

Axiom In_consume : forall p psent p', 
  In p' (consume p psent) <-> markRcv p = p' \/ (In p' psent /\ p <> p' (* p <> p' might be overly restricted? *)).

End PacketConsumption.

Module PacketConsumptionImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export P : SimplePacket A M) : PacketConsumption A M P.

Definition consume (p : Packet) (psent : list Packet) :=
  (markRcv p) :: (List.remove Packet_eqdec p psent).

Fact In_consume : forall p psent p', 
  In p' (consume p psent) <-> markRcv p = p' \/ (In p' psent /\ p <> p').
Proof. intros. simpl. rewrite in_remove_iff. intuition. Qed.

End PacketConsumptionImpl.

Module PacketConsumptionLemmas (Export A : NetAddr) (Export M : MessageType) (Export P : SimplePacket A M)
  (Export PC : PacketConsumption A M P).

Section Main.

  Context [psent : list Packet] [p : Packet] (Hin : In p psent).

  Lemma In_consume_idem (Hused : p.(received) = true) :
    forall p', In p' (consume p psent) <-> In p' psent.
  Proof.
    intros. rewrite In_consume. destruct p as [ src dst msg ? ]. simpl in *. subst. 
    destruct (Packet_eqdec (mkP src dst msg true) p') in |- *; eqsolve.
  Qed.

  (* FIXME: any below can be subsumed by In_consume_iff? potentially, there are too many lemmas here *)
  Lemma In_consume_fwd [p'] (Hin' : In p' psent) :
    In (if Packet_eqdec p' p then markRcv p' else p') (consume p psent).
  Proof.
    destruct (Packet_eqdec p' p) as [ <- | Hneq ]; apply In_consume; intuition.
  Qed.

  Lemma In_consume_fwd_full [src dst msg used] (Hin' : In (mkP src dst msg used) psent) :
    In (mkP src dst msg (if (Packet_eqdec (mkP src dst msg used) p) then true else used)) 
      (consume p psent).
  Proof.
    destruct (Packet_eqdec _ _) as [ <- | Hneq ]; apply In_consume; intuition.
  Qed.

  Corollary In_consume_fwd_full' [src dst msg] (Hin' : In (mkP src dst msg true) psent) :
    In (mkP src dst msg true) (consume p psent).
  Proof.
    apply In_consume_fwd_full in Hin'.
    destruct (Packet_eqdec _ _); auto.
  Qed.

  Lemma In_consume_conv [p'] (Hin' : In p' (consume p psent)) :
    exists p'', pkt_le p'' p' /\ In p'' psent.
  Proof.
    apply In_consume in Hin'.
    destruct Hin' as [ <- | (Hin' & _) ].
    - exists p.
      split; [ hnf; auto | assumption ].
    - exists p'.
      split; [ hnf; auto | assumption ].
  Qed.

  Corollary In_consume_conv_full
    [src dst msg used] (Hin' : In (mkP src dst msg used) (consume p psent)) :
    exists used', In (mkP src dst msg used') psent.
  Proof.
    apply In_consume_conv in Hin'.
    destruct Hin' as ([] & [ E | E ] & Hin'); inversion E; eauto.
  Qed.

End Main.

End PacketConsumptionLemmas.
