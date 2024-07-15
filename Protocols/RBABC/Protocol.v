From Coq Require Import Bool List PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Composition Require Export Protocol.
From Bythos.Protocols.RBABC Require Export Types.
From Bythos.Protocols.ABC Require Import Protocol.
From Bythos.Protocols.RB Require Import Protocol.

Module RBACTrigger (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (RBM : RBMessage A R V)
  (PPrim : PKIPrim A Sn)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.t0)
  (ACDT : SimpleACDataTypes A Sn V PPrim TSSPrim) (ACM : ACMessage A Sn V PPrim TSSPrim ACDT)
  (M : CompMessage RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh PPrim TSSPrim ACDT ACM ACPk) <: SeqCompProtocolTrigger A RBM ACM BTh RBPk ACPk RBP ACP.

Import ARP.

Definition trigger_procMsg (st st' : RBP.State) :=
  match (st.(RBP.output) arp), (st'.(RBP.output) arp) with
  | nil, nil => None
  | _ :: _, _ => None
  | nil, v :: _ => Some (ACP.SubmitIntTrans v)
  end.

Definition trigger_procInt : RBP.State -> RBP.State -> option ACP.InternalTransition := fun _ _ => None.

End RBACTrigger.
