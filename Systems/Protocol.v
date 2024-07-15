From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Structures Require Export Types.

Module Type ByzThreshold (Export A : NetAddr).

(* t0: the threshold, indicating the maximum number of tolerable Byzantine nodes *)
(* make this a parameter, since sometimes we do not need a concrete number *)
Parameter t0 : nat.

Axiom t0_lt_N : t0 < N.

End ByzThreshold.

Module Type ClassicByzThreshold (Export A : NetAddr) <: ByzThreshold A.

(* TODO is it possible to make this function work over arbitrary integer parameter?
    do not quite want to introduce another module type ... *)

Definition t0 := (N - 1) / 3.

Fact N_gt_0 : 0 < N.
Proof. 
  unfold N. 
  pose proof (Address_is_finite Address_inhabitant).
  destruct valid_nodes; [ contradiction | simpl; apply Nat.lt_0_succ ].
Qed.

Fact t0_times_3_lt_N : 3 * t0 < N.
Proof.
  unfold t0, lt.
  (* nia does not work here *)
  pose proof N_gt_0.
  destruct N as [ | N ]; [ inversion H | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  apply le_n_S, Nat.Div0.mul_div_le.
Qed.

Fact t0_lt_N_minus_2t0 : t0 < N - (t0 + t0).
Proof. pose proof t0_times_3_lt_N. lia. Qed.

Corollary N_minus_2t0_gt_0 : 0 < N - (t0 + t0).
Proof. pose proof t0_lt_N_minus_2t0. lia. Qed.

Fact t0_lt_N : t0 < N.
Proof. pose proof t0_times_3_lt_N. lia. Qed.

End ClassicByzThreshold.

Module ClassicByzThresholdImpl (Export A : NetAddr) <: ClassicByzThreshold A <: ByzThreshold A.

Include ClassicByzThreshold A.

End ClassicByzThresholdImpl.

Module Type Protocol (Export A : NetAddr) (Export M : MessageType) (Export P : PacketType)
  (Export BTh : ByzThreshold A).

Parameter InternalTransition : Type.

Parameter State : Type.
(* not used for now *)
(* Parameter State_eqdec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}. *)

Parameter Init : Address -> State.

(* TODO later change this name to the more canonical "procMsg" *)
Parameter procMsgWithCheck : State -> Address (* sender *) -> Message -> State * list Packet.
Parameter procInt : State -> InternalTransition -> State * list Packet.

End Protocol.
