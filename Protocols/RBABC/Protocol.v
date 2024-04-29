From Coq Require Import Bool List PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Composition Require Export Protocol.
From Bythos.Protocols.RBABC Require Export Types.
From Bythos.Protocols.ABC Require Import Protocol.
From Bythos.Protocols.RB Require Import Protocol.

Module RBACTrigger (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (RBM : RBMessage A R V)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (ACM : ACMessage A Sn V P TSS ACDT)
  (M : CompMessage RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh P TSS0 TSS ACDT CC ACM ACPk) <: SeqCompProtocolTrigger A RBM ACM BTh RBPk ACPk RBP ACP.

Import ARP.

Definition trigger_procMsg (st st' : RBP.State) :=
  match (st.(RBP.output) arp), (st'.(RBP.output) arp) with
  | nil, nil => None
  | _ :: _, _ => None
  | nil, v :: _ => Some (ACP.SubmitIntTrans v)
  end.

Definition trigger_procInt : RBP.State -> RBP.State -> option ACP.InternalTransition := fun _ _ => None.

End RBACTrigger.
