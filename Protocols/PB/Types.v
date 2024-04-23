From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Structures Require Export Types.

Module Type Value (Sn : Signable).

Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.
(* Declare Instance VSn : Sn.signable Value. *)

End Value.

Module Type PBProof (Sn : Signable).

Parameter Proof : Set.
Parameter Proof_eqdec : forall (v1 v2 : Proof), {v1 = v2} + {v1 <> v2}.
(* Declare Instance ProofSn : Sn.signable Proof. *)

End PBProof.

Module Type PBTag.

Parameter Round : Type.
Parameter Round_eqdec : forall r1 r2 : Round, {r1 = r2} + {r1 <> r2}.

End PBTag.

Module Type ValueBFT (Export A : NetAddr) (Export R : PBTag) (Sn : Signable) (Export V : Value Sn) (Export Pf : PBProof Sn).

Parameter value_bft : Address -> Round -> Value * Proof.

End ValueBFT.

Module Type PBDataTypes (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn).

Import A R V Pf TSS.

(* Declare Instance LSSn : Sn.signable LightSignature. *)
Declare Instance VPfSn : Sn.signable (Round * Value). (* TODO temporary; also can be done with a typeclass for product composition *)

(* external validator *)
(* TODO consider each node may possess a different one? not quite ... *)
Parameter ex_validate : Round -> Value -> Proof -> bool.  

End PBDataTypes.

Module Type PBMessage (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn)
  <: MessageType.

Import A R V Pf TSS.

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

Module PBMessageImpl (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn)
  <: MessageType <: PBMessage A R Sn V Pf TSS.

Include PBMessage A R Sn V Pf TSS.

End PBMessageImpl.
