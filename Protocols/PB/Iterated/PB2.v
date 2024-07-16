From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.PB Require Export Liveness_tla.

Module Type PBProofB (A : NetAddr) (Sn : Signable) (BTh : ClassicByzThreshold A) (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.f)
  <: PBProof. (* Proof type of B *)

Import TSSPrim.

Definition Proof := CombinedSignature.
Definition Proof_eqdec := CombinedSignature_eqdec.

End PBProofB.

Module PB2 (Ad : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (VBFT : ValueBFT Ad R V Pf) 
  (BTh : ClassicByzThreshold Ad)
  (BSettA : RestrictedByzSetting Ad BTh)
  (BSettB : RestrictedByzSetting Ad BTh)
  (TSSPrim : ThresholdSignatureSchemePrim Ad Sn with Definition thres := Ad.N - BTh.f)
  (PfB : PBProofB Ad Sn BTh TSSPrim) 
  (VBFTB : ValueBFT Ad R V PfB)
  (PBDT : PBDataTypes Ad R Sn V Pf)
  (PBDTB : PBDataTypes Ad R Sn V PfB with Definition RVSn := PBDT.RVSn).

Import Ad R V Pf VBFT BTh BSettA BSettB PBDT.
Import ssrbool. (* anyway *)

Module A := PBLiveness2 Ad R Sn V Pf VBFT BTh BSettA TSSPrim PBDT.
Module B := PBLiveness2 Ad R Sn V PfB VBFTB BTh BSettB TSSPrim PBDTB.
Import A.PBP.TSS. (* importing which does not really matter *)
(* If a delivery-certificate exists for v
  then there can only exist a lock-certificate for v
  and there are at least n−2f
  honest parties that hold this lock-certificate. *)

Section AB.

Variable (wa : A.Ns.World).

Hypothesis (Hwa : A.reachable wa). 
Hypothesis (Hvsame : forall n r, fst (VBFT.value_bft n r) = fst (VBFTB.value_bft n r)).
Hypothesis (Hconnect : forall n r cs, (A.Ns.localState wa n).(A.PBP.output) r = Some cs -> snd (VBFTB.value_bft n r) = cs).

Definition unique_lock_availability (wb : B.Ns.World) : Prop :=
  forall n r csa csb, 
    BSettA.is_byz n = false -> 
    BSettB.is_byz n = false ->
    (B.Ns.localState wb n).(B.PBP.output) r = Some csb ->
    (A.Ns.localState wa n).(A.PBP.output) r = Some csa ->
    let: v := fst (VBFT.value_bft n r) in
    combined_verify (r, v) csa /\
    (exists l : list Address, 
      List.NoDup l /\ f < length l /\ 
      (forall n0, In n0 l -> BSettB.is_byz n0 = false /\ (B.Ns.localState wb n0).(B.PBP.echoed) (n, r) = Some (VBFTB.value_bft n r))).

Lemma unique_lock_availability_always_holds : B.always_holds unique_lock_availability.
Proof using Hconnect Hvsame Hwa wa.
  hnf. intros w Hr. hnf. intros. split_and?.
  - apply A.output_ok_always_holds in Hwa. hnf in Hwa. now saturate_assumptions!. 
  - apply B.output_ok_always_holds in Hr. hnf in Hr. now saturate_assumptions!.
Qed.

End AB.

End PB2.
