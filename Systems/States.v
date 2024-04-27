From Coq Require Import List Lia RelationClasses.
From ABCProtocol.Systems Require Export Protocol.

Module Type NetState (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export BTh : ByzThreshold A) (Export Pr : Protocol A M P BTh).

(* using a map library seems to be overkill *)
(* FIXME: make this total or partial? maybe we should only represent the states of non-Byzantine nodes *)

Definition StateMap := Address -> State. 
Definition initState := (fun n => Init n).

Definition upd (n : Address) (st : State) (states : StateMap) : StateMap :=
  (* fun m => if Address_eqdec n m then st else states m. *)
  Eval unfold map_update in map_update Address_eqdec n st states.

Fact upd_refl n st stmap : upd n st stmap n = st.
Proof. now apply map_update_refl. Qed.

Fact upd_intact n n' stmap : upd n' (stmap n') stmap n = stmap n.
Proof. now apply map_update_intact. Qed.

(* if to parameterize this, then need some module type about finite multiset? *)
(* currently, let's stick to list *)
Definition PacketSoup := list Packet.

(* holistic network state *)
Record World :=
  mkW {
    localState : StateMap;
    sentMsgs : PacketSoup;
  }.

Definition initWorld := mkW initState nil.

(* some handy things *)
Global Notation "w '@' n" := (localState w n) (at level 50, left associativity).

Definition World_rel (w w' : World) : Prop :=
  (forall n, (w @ n) = (w' @ n)) /\ Ineq (sentMsgs w) (sentMsgs w').

#[export] Instance Equivalence_World_rel : Equivalence World_rel.
Proof.
  constructor; hnf.
  - intros. hnf; split; intros; reflexivity.
  - intros x y (H & H0). hnf. split; intros; rewrite ?H, ?H0; reflexivity.
  - intros x y z (H & H0) (H' & H0'). hnf. split; intros; rewrite ?H, ?H0, ?H', ?H0'; reflexivity.
Qed.

Global Tactic Notation "simpl_world" := simpl localState in *; simpl sentMsgs in *.

Global Tactic Notation "rewrite_w_expand" ident(w) "in_" hyp(H) :=
  replace w with (mkW (localState w) (sentMsgs w)) in H by (now destruct w).

(* TODO not good design *)
(* this will be instantiated for each protocol, since we do not have id field here *)
Global Ltac destruct_localState_id_coh_check P w := idtac.

Global Tactic Notation "destruct_localState" ident(w) ident(n) "as_" simple_intropattern(pat) "eqn_" ident(E) :=
  match goal with 
  | H : ?P |- _ =>
    tryif destruct_localState_id_coh_check P w
    then
      let Htmp := fresh "Htmp" in
      pose proof (H n) as Htmp;
      destruct (localState w n) as pat eqn:E; 
      simpl in Htmp; 
      match type of Htmp with ?nn = _ => subst nn end
    else fail 0
  end.

Global Tactic Notation "destruct_localState" ident(w) ident(n) "as_" simple_intropattern(pat) :=
  let E := fresh "E" in
  (destruct_localState w n as_ pat eqn_ E); clear E.

(* ask: can a faulty node produce something with type A, which meets some requirement P, 
    by just using what is in the world? *)
(* do not really make sense to give a proof saying that if produ_check holds, then P holds.
    just for proving *)
(* can be used to describe the adversary capability in the Dolev-Yao style *)
Class producible (A : Type) (P : A -> Prop) :=
  produ_check : World -> A -> Prop.

End NetState.

Module NetStateImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export BTh : ByzThreshold A) (Export Pr : Protocol A M P BTh) 
  <: NetState A M P BTh Pr.

Include (NetState A M P BTh Pr).

End NetStateImpl.

Module Type PacketSoupOperations (Export P : PacketType).

(* indicating that our proof does not rely on concrete maintaining methods of packet soup,
    as long as those methods satisfy certain properties *)

Parameter sendout1 : Packet -> list Packet -> list Packet.
Parameter sendout : list Packet -> list Packet -> list Packet.

Axiom In_sendout1 : forall p psent p', In p' (sendout1 p psent) <-> p = p' \/ In p' psent.
Axiom In_sendout : forall pkts psent p, In p (sendout pkts psent) <-> In p pkts \/ In p psent.
Axiom sendout0 : forall psent, sendout nil psent = psent.
(* not sure if this is good for autorewrite? *)

(* expedient *)
Axiom sendout1_sendout : forall p psent, sendout1 p psent = sendout (p :: nil) psent.

Create HintDb psent.

Global Hint Rewrite -> In_sendout1 In_sendout in_app_iff in_cons_iff : psent.

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

End PacketSoupOperations.

Module PacketSoupOperationsImpl (Export P : PacketType) <: PacketSoupOperations P.

Definition sendout1 : Packet -> list Packet -> list Packet := cons.
Definition sendout : list Packet -> list Packet -> list Packet := @List.app Packet.

Fact In_sendout1 : forall p psent p', In p' (sendout1 p psent) <-> p = p' \/ In p' psent.
Proof. intros. reflexivity. Qed.

Fact In_sendout : forall pkts psent p, In p (sendout pkts psent) <-> In p pkts \/ In p psent.
Proof. intros. unfold sendout. now rewrite in_app_iff. Qed.

Fact sendout0 : forall psent, sendout nil psent = psent.
Proof (fun _ => eq_refl).

(* FIXME: can we eliminate this duplicate? *)
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

Fact sendout1_sendout : forall p psent, sendout1 p psent = sendout (p :: nil) psent.
Proof. intros. reflexivity. Qed.

End PacketSoupOperationsImpl.

Module Type PacketConsumption (Export A : NetAddr) (Export M : MessageType) (Export P : SimplePacket A M).

(* since we distinguish between packets that have been delivered and packets that have not been delivered,
    we need some mechanism to mark a packet as delivered *)

Parameter consume : Packet -> list Packet -> list Packet.

Axiom In_consume : forall p psent p', 
  In p' (consume p psent) <-> receive_pkt p = p' \/ (In p' psent /\ p <> p' (* p <> p' might be overly restricted? *)).

End PacketConsumption.

Module PacketConsumptionImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export P : SimplePacket A M) <: PacketConsumption A M P.

Definition consume (p : Packet) (psent : list Packet) :=
  (receive_pkt p) :: (List.remove Packet_eqdec p psent).

Fact In_consume : forall p psent p', 
  In p' (consume p psent) <-> receive_pkt p = p' \/ (In p' psent /\ p <> p').
Proof. intros. simpl. rewrite in_remove_iff. intuition. Qed.

End PacketConsumptionImpl.

Module PacketConsumptionImpl' (Export A : NetAddr) (Export M : MessageType) (Export P : SimplePacket A M)
  (Export PC : PacketConsumption A M P).

(* TODO only consider the case where the consumed packet is in psent? *)

Section Main.

  Context [psent : list Packet] [p : Packet] (Hin : In p psent).

  Lemma In_consume_idem (Hused : p.(consumed) = true) :
    forall p', In p' (consume p psent) <-> In p' psent.
  Proof.
    intros. rewrite In_consume. destruct p as [ src dst msg ? ]. simpl in *. subst. 
    destruct (Packet_eqdec (mkP src dst msg true) p') in |- *; eqsolve.
  Qed.

  (* FIXME: any below can be subsumed by In_consume_iff? *)
  Lemma In_consume_fwd [p'] (Hin' : In p' psent) :
    In (if Packet_eqdec p' p then receive_pkt p' else p') (consume p psent).
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

End PacketConsumptionImpl'.
