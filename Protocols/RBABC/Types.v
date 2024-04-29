From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Composition Require Export Types.
From ABCProtocol.Protocols.ABC Require Export Types.
From ABCProtocol.Protocols.RB Require Export Types.

(* TODO it seems that if we allow multiple instances of ABC to run at the same time, 
    then it is possible for adversaries to collect signatures from different instances
    and use them in one particular instance.
  in this case, we need to change the protocol a little bit ...
  (1) we only allow one instance of ABC for some (node, round) pair. 
  (2) the value of ABC to be signed becomes the product of instance id and value. 
*)
(*
Module Export SingleRound <: Round.

Definition Round := unit.
Definition Round_eqdec : forall r1 r2 : Round, {r1 = r2} + {r1 <> r2}.
  intros [][]. left. reflexivity.
Qed.

End SingleRound.
*)
Module Type AddrRoundPair (Export A : NetAddr) (Export R : Round).

Parameter arp : Address * Round.

End AddrRoundPair.
(*
Module Type SingleValueBFT (Export A : NetAddr) (Export V : Value) (Export LS : Leadership A V) <: ValueBFT A SingleRound V.

Definition value_bft : Address -> Round -> Value := fun _ _ => inputval.

End SingleValueBFT.

Module SingleValueBFTImpl (Export A : NetAddr) (Export V : Value) (Export LS : Leadership A V) 
  <: ValueBFT A SingleRound V <: SingleValueBFT A V LS.

Include SingleValueBFT A V LS.

End SingleValueBFTImpl.
*)
(*
Module Type RBACMessage (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (P : PKI A Sn) (TSS : ThresholdSignatureScheme A Sn)
  (ACDT : ACDataTypes A Sn V P TSS)
  (* module type ...!!! *)
  (RBM : RBMessage A R V) (ACM : ACMessage A Sn V P TSS ACDT) <: MessageType.

Import A R V P TSS ACDT.

Definition Message := (RBM.Message + ACM.Message)%type.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros.
  repeat (decide equality; auto using RBM.Message_eqdec, ACM.Message_eqdec).
Qed.

End RBACMessage.

Module RBACMessageImpl (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (P : PKI A Sn) (TSS : ThresholdSignatureScheme A Sn)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (RBM : RBMessage A R V) (ACM : ACMessage A Sn V P TSS ACDT) <: MessageType <: RBACMessage A R Sn V P TSS ACDT RBM ACM.

Include RBACMessage A R Sn V P TSS ACDT RBM ACM.

End RBACMessageImpl.
*)