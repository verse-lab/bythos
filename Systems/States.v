From Coq Require Import List Lia.
From ABCProtocol.Systems Require Export Protocol.

Module Type NetState (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export BTh : ByzThreshold A) (Export Pr : Protocol A M P BTh).

(* using a map library seems to be overkill *)
(* FIXME: make this total or partial? maybe we should only represent the states of non-Byzantine nodes *)

Definition StateMap := Address -> State. 
Definition initState := (fun n => Init n).

Definition upd (n : Address) (st : State) (states : StateMap) : StateMap :=
  fun m => if Address_eqdec n m then st else states m.

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

Create HintDb psent.

#[export] Hint Rewrite -> In_sendout1 In_sendout in_app_iff in_cons_iff : psent.

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
