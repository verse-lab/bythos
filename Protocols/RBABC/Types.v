From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Structures Require Export Types.
From ABCProtocol.Protocols.ABC Require Export Types.
From ABCProtocol.Protocols.RB Require Export Types.

Module Type RBACMessage (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (P : PKI A Sn) (TSS : ThresholdSignatureScheme A Sn)
  (ACDT : ACDataTypes A Sn V P TSS)
  (* module type ...!!! *)
  (RBM : RBMessage A R V) (ACM : ACMessage A Sn V P TSS ACDT) <: MessageType.

Import A R V P TSS ACDT.

Definition Message := (RBM.Message + (Address * Round) * ACM.Message)%type.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros.
  repeat (decide equality; auto using RBM.Message_eqdec, ACM.Message_eqdec, Address_eqdec, Round_eqdec).
Qed.

End RBACMessage.

Module RBACMessageImpl (A : NetAddr) (R : Round) (Sn : Signable) (V : SignableValue Sn) (P : PKI A Sn) (TSS : ThresholdSignatureScheme A Sn)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (RBM : RBMessage A R V) (ACM : ACMessage A Sn V P TSS ACDT) <: MessageType <: RBACMessage A R Sn V P TSS ACDT RBM ACM.

Include RBACMessage A R Sn V P TSS ACDT RBM ACM.

End RBACMessageImpl.
