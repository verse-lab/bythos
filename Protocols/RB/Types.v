From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Structures Require Export Types.

Module Type ValueBFT (Export A : NetAddr) (Export R : Round) (Export V : Value).

(* fixing what to broadcast at each round *)

Parameter value_bft : Address -> Round -> Value.

End ValueBFT.

Module Type RBMessage (A : NetAddr) (R : Round) (V : Value) <: MessageType.

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
