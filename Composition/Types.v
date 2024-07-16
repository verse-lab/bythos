From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Structures Require Export Types.

(* the following should be generally useful when composing two protocols, 
    no matter how they are composed *)

Module Type CompMessage (M1 M2 : MessageType) <: MessageType.

Definition Message := (M1.Message + M2.Message)%type.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros.
  repeat (decide equality; auto using M1.Message_eqdec, M2.Message_eqdec).
Qed.

End CompMessage.

Module Type CompSimplePacket (A : NetAddr) (M1 M2 : MessageType) (CM : CompMessage M1 M2)
  (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2) <: SimplePacket A CM.

Include SimplePacket A CM.

(* auxiliary operations *)

Definition pkt_inl (p : Pk1.Packet) : Packet :=
  mkP (Pk1.src p) (Pk1.dst p) (inl (Pk1.msg p)) (Pk1.received p).

Definition pkt_inr (p : Pk2.Packet) : Packet :=
  mkP (Pk2.src p) (Pk2.dst p) (inr (Pk2.msg p)) (Pk2.received p).

Definition pkt_proj1 (p : Packet) : option Pk1.Packet :=
  match p.(msg) with
  | inl msg' => Some (Pk1.mkP p.(src) p.(dst) msg' p.(received))
  | _ => None
  end.

Definition pkt_proj2 (p : Packet) : option Pk2.Packet :=
  match p.(msg) with
  | inr msg' => Some (Pk2.mkP p.(src) p.(dst) msg' p.(received))
  | _ => None
  end.

Global Arguments pkt_proj1 !_.
Global Arguments pkt_proj2 !_.
Global Arguments pkt_inl !_.
Global Arguments pkt_inr !_.

Fact pkt_proj1_refl p : pkt_proj1 (pkt_inl p) = Some p.
Proof. now destruct p. Qed.

Fact pkt_proj1_refl_must p p' : pkt_proj1 (pkt_inl p) = Some p' -> p = p'.
Proof. destruct p. cbn. now intros [=]. Qed.

Fact pkt_proj2_refl p : pkt_proj2 (pkt_inr p) = Some p.
Proof. now destruct p. Qed.

Fact pkt_proj2_refl_must p p' : pkt_proj2 (pkt_inr p) = Some p' -> p = p'.
Proof. destruct p. cbn. now intros [=]. Qed.

Definition pkts_filter_proj1 : list Packet -> list Pk1.Packet :=
  option_map_list pkt_proj1.

Definition pkts_filter_proj2 : list Packet -> list Pk2.Packet :=
  option_map_list pkt_proj2.

Fact pkts_filter_proj1_all pkts1 : pkts_filter_proj1 (map pkt_inl pkts1) = pkts1.
Proof. induction pkts1 as [ | a ? ? ]; simpl; auto. destruct a. simpl. congruence. Qed.

Fact pkts_filter_proj1_no pkts2 : pkts_filter_proj1 (map pkt_inr pkts2) = nil.
Proof. induction pkts2; simpl; auto. Qed.

Fact pkts_filter_proj2_all pkts2 : pkts_filter_proj2 (map pkt_inr pkts2) = pkts2.
Proof. induction pkts2 as [ | a ? ? ]; simpl; auto. destruct a. simpl. congruence. Qed.

Fact pkts_filter_proj2_no pkts1 : pkts_filter_proj2 (map pkt_inl pkts1) = nil.
Proof. induction pkts1; simpl; auto. Qed.

Fact pkts_filter_proj1_app l1 l2 : pkts_filter_proj1 (l1 ++ l2) = pkts_filter_proj1 l1 ++ pkts_filter_proj1 l2.
Proof. apply flat_map_app. Qed.

Fact pkts_filter_proj2_app l1 l2 : pkts_filter_proj2 (l1 ++ l2) = pkts_filter_proj2 l1 ++ pkts_filter_proj2 l2.
Proof. apply flat_map_app. Qed.

Create HintDb pkts_filter.

Hint Rewrite -> pkts_filter_proj1_all pkts_filter_proj1_no pkts_filter_proj2_all pkts_filter_proj2_no
  pkts_filter_proj1_app pkts_filter_proj2_app app_nil_r : pkts_filter.

End CompSimplePacket.
