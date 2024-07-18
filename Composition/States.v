From Coq Require Import List Lia RelationClasses.
From Bythos.Systems Require Export States.
From Bythos.Composition Require Export Protocol.

Module Type CompNetState (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh)
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  (Ns1 : NetState A M1 Pk1 BTh Pt1) (Ns2 : NetState A M2 Pk2 BTh Pt2)
  (CPt : SeqCompProtocol A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT) <: NetState A CM CPk BTh CPt.

Import BTh CM CPk SCPT.

Include NetState A CM CPk BTh CPt.

(* auxiliary operations *)
Definition stmap_proj1 (stmap : StateMap) : Ns1.StateMap := fun n => (stmap n).(st1).

Definition stmap_proj2 (stmap : StateMap) : Ns2.StateMap := fun n => (stmap n).(st2).

Definition sysstate_proj1 (w : SystemState) : Ns1.SystemState :=
  Ns1.mkW (stmap_proj1 (localState w)) (pkts_filter_proj1 (packetSoup w)).

Definition sysstate_proj2 (w : SystemState) : Ns2.SystemState :=
  Ns2.mkW (stmap_proj2 (localState w)) (pkts_filter_proj2 (packetSoup w)).

Local Set Implicit Arguments.

(* very trivial lemmas *)

Fact procMsg_proj1 [st src m1] : forall st' pkts,
  procMsg st src (inl m1) = (st', pkts) ->
  let: res := Pt1.procMsg st.(st1) src m1 in
  st'.(st1) = fst res /\ pkts_filter_proj1 pkts = snd res.
Proof.
  intros st' pkts E. simpl in E.
  rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)) in E.
  destruct (trigger_procMsg _ _) in E.
  1: rewrite -> (surjective_pairing (Pt2.procInt _ _)) in E.
  all: revert E; intros [= <- <-].
  all: simpl; now autorewrite with pkts_filter.
Qed.

Fact procInt_proj1 [st tr] : forall st' pkts,
  procInt st tr = (st', pkts) ->
  let: res := Pt1.procInt st.(st1) tr in
  st'.(st1) = fst res /\ pkts_filter_proj1 pkts = snd res.
Proof.
  intros st' pkts E. unfold procInt in E.
  rewrite -> (surjective_pairing (Pt1.procInt _ _)) in E.
  destruct (trigger_procInt _ _) in E.
  1: rewrite -> (surjective_pairing (Pt2.procInt _ _)) in E.
  all: revert E; intros [= <- <-].
  all: simpl; now autorewrite with pkts_filter.
Qed.

Fact procMsg_proj2 [st src m2] : forall st' pkts,
  procMsg st src (inr m2) = (st', pkts) ->
  let: res := Pt2.procMsg st.(st2) src m2 in
  st'.(st2) = fst res /\ pkts_filter_proj2 pkts = snd res.
Proof.
  intros st' pkts E. simpl in E.
  rewrite -> (surjective_pairing (Pt2.procMsg _ _ _)) in E.
  revert E; intros [= <- <-].
  simpl; now autorewrite with pkts_filter.
Qed.

End CompNetState.
