From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Structures Require Export Types.
(*
Module Type Leadership (Export A : NetAddr) (Export V : Signable).

Parameter leader : Address.
Parameter inputval : Value. (* to be broadcast *)

End Leadership.
*)

Module Type Value.

(* here, only requires that value has decidable equality *)
Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.

End Value.

Module Type RBTag.

Parameter Round : Type.
Parameter Round_eqdec : forall r1 r2 : Round, {r1 = r2} + {r1 <> r2}.

End RBTag.

Module Type ValueBFT (Export A : NetAddr) (Export R : RBTag) (Export V : Value).

(* fixing what to broadcast at each round *)

Parameter value_bft : Address -> Round -> Value.

End ValueBFT.

Module Type RBMessage (A : NetAddr) (R : RBTag)
  (V : Value (* not for signing here, though *)) <: MessageType.

Import A R V.

Inductive Message_ := 
  | InitialMsg (r : Round) (v : Value)
  | EchoMsg (orig : Address) (r : Round) (v : Value)
  | VoteMsg (orig : Address) (r : Round) (v : Value)
.

Definition Message := Message_.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros. 
  decide equality; auto using Address_eqdec, Value_eqdec, Round_eqdec.
Qed.

End RBMessage.

Module RBMessageImpl (A : NetAddr) (R : RBTag) (V : Value) <: MessageType <: RBMessage A R V.

Include RBMessage A R V.

End RBMessageImpl.
