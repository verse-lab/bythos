From Coq Require Import Bool List PeanoNat Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Structures Require Export Types.

Module Type ByzThreshold (Export A : NetAddr).

(* f: the threshold, indicating the maximum number of tolerable Byzantine nodes *)
(* make this a parameter, since sometimes we do not need a concrete number *)
Parameter f : nat.

Axiom f_lt_N : f < N.

End ByzThreshold.

Module Type ClassicByzThreshold (Export A : NetAddr) <: ByzThreshold A.

(* FIXME: in the future, change 3 into some integer parameter? *)

Definition f := (N - 1) / 3.

Fact N_gt_0 : 0 < N.
Proof. 
  unfold N. 
  pose proof (Address_is_finite Address_inhabitant).
  destruct valid_nodes; [ contradiction | simpl; apply Nat.lt_0_succ ].
Qed.

Fact f_times_3_lt_N : 3 * f < N.
Proof.
  unfold f, lt.
  (* nia does not work here *)
  pose proof N_gt_0.
  destruct N as [ | N ]; [ inversion H | ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  apply le_n_S, Nat.Div0.mul_div_le.
Qed.

Fact f_lt_N_minus_2f : f < N - (f + f).
Proof. pose proof f_times_3_lt_N. lia. Qed.

Corollary N_minus_2f_gt_0 : 0 < N - (f + f).
Proof. pose proof f_lt_N_minus_2f. lia. Qed.

Fact f_lt_N : f < N.
Proof. pose proof f_times_3_lt_N. lia. Qed.

End ClassicByzThreshold.

Module Type Protocol (Export A : NetAddr) (Export M : MessageType) (Export P : PacketType)
  (Export BTh : ByzThreshold A).

Parameter InternalTransition : Type.
Parameter State : Type.
Parameter initState : Address -> State.
Parameter procMsg : State -> Address (* sender *) -> Message -> State * list Packet.
Parameter procInt : State -> InternalTransition -> State * list Packet.

End Protocol.
