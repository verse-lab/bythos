From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Structures Require Export Types.

Module Type PBProof (Sn : Signable).

Parameter Proof : Set.
Parameter Proof_eqdec : forall (v1 v2 : Proof), {v1 = v2} + {v1 <> v2}.
(* Declare Instance ProofSn : Sn.signable Proof. *)

End PBProof.

Module Type ValueBFT (Export A : NetAddr) (Export R : Round) (Sn : Signable) (Export V : Value) (Export Pf : PBProof Sn).

Parameter value_bft : Address -> Round -> Value * Proof.

End ValueBFT.

Module Type PBDataTypes (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn).

Import A R V Pf TSS.

(* Declare Instance LSSn : Sn.signable LightSignature. *)
Declare Instance VPfSn : Sn.signable (Round * Value). (* TODO temporary; also can be done with a typeclass for product composition *)

(* it seems that in any cases, there will not be LightSigantures in the Proof? so ignore for now *)
(* Parameter lightsig_from_proof : Proof -> list LightSignature. *)

(* external validator *)
(* TODO consider each node may possess a different one? not quite ... *)
Parameter ex_validate : Round -> Value -> Proof -> bool.  

End PBDataTypes.

Module Type PBMessage (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn)
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

Module PBMessageImpl (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof Sn) (TSS : ThresholdSignatureScheme A Sn)
  <: MessageType <: PBMessage A R Sn V Pf TSS.

Include PBMessage A R Sn V Pf TSS.

End PBMessageImpl.
