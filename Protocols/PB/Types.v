From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Structures Require Export Types.

Module Type PBProof.

Parameter Proof : Set.
Parameter Proof_eqdec : forall (v1 v2 : Proof), {v1 = v2} + {v1 <> v2}.

End PBProof.

Module Type ValueBFT (Export A : NetAddr) (Export R : Round) (Export V : Value) (Export Pf : PBProof).

Parameter value_bft : Address -> Round -> Value * Proof.

End ValueBFT.

Module Type PBDataTypes (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof).

Import A R V Pf.

Declare Instance RVSn : Sn.signable (Round * Value). (* FIXME: temporary; also can be done with a typeclass for product composition *)

(* NOTE: for now, assume all nodes possess the same external validator *)
Parameter ex_validate : Round -> Value -> Proof -> bool.  

End PBDataTypes.

Module Type PBMessage (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (TSSPrim : ThresholdSignatureSchemePrim A Sn)
  <: MessageType.

Import A R V Pf TSSPrim.

Inductive Message_ := 
  | InitMsg (r : Round) (v : Value) (pf : Proof)   (* from the broadcast initiator *)
  | EchoMsg (r : Round) (lsig : LightSignature)    (* from the receiver *)
.

Definition Message := Message_.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros. 
  decide equality; auto using Value_eqdec, Proof_eqdec, LightSignature_eqdec, 
    Round_eqdec.
Qed.

End PBMessage.

Module PBMessageImpl (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (TSSPrim : ThresholdSignatureSchemePrim A Sn)
  <: MessageType <: PBMessage A R Sn V Pf TSSPrim.

Include PBMessage A R Sn V Pf TSSPrim.

End PBMessageImpl.
