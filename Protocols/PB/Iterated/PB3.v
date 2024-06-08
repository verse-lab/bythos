From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.PB.Iterated Require Export PB2.

Module PB3 (Ad : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof Sn) (VBFT : ValueBFT Ad R Sn V Pf) 
  (BTh : ClassicByzThreshold Ad)
  (BSettA : RestrictedByzSetting Ad BTh)
  (BSettB : RestrictedByzSetting Ad BTh)
  (BSettC : RestrictedByzSetting Ad BTh)
  (TSS0 : ThresholdSignatureSchemePrim Ad Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme Ad Sn with Module TSSPrim := TSS0)
  (PfB : PBProofB Ad Sn BTh TSS0 TSS) 
  (VBFTB : ValueBFT Ad R Sn V PfB)
  (VBFTC : ValueBFT Ad R Sn V PfB)
  (PBDT : PBDataTypes Ad R Sn V Pf TSS)
  (PBDTB : PBDataTypes Ad R Sn V PfB TSS with Definition VPfSn := PBDT.VPfSn).

Import Ad R V Pf VBFT BTh BSettA BSettB TSS PBDT.
Import ssrbool. (* anyway *)

Module Export PB2Impl := PB2 Ad R Sn V Pf VBFT BTh BSettA BSettB TSS0 TSS PfB VBFTB PBDT PBDTB.
Module C := PBLiveness2 Ad R Sn V PfB VBFTC BTh BSettC TSS0 TSS PBDTB.

Section ABC.

Variable (wb : B.Ns.World).

Hypothesis (Hwb : B.reachable wb). 
Hypothesis (Hvsame : forall n r, fst (VBFTB.value_bft n r) = fst (VBFTC.value_bft n r)).
Hypothesis (Hconnect : forall n r cs, (B.Ns.localState wb n).(B.PBP.output) r = Some cs -> snd (VBFTC.value_bft n r) = cs).

Definition unique_lock_availability (wc : C.Ns.World) : Prop :=
  forall n r csb csc, 
    BSettB.is_byz n = false -> 
    BSettC.is_byz n = false ->
    (C.Ns.localState wc n).(C.PBP.output) r = Some csc ->
    (B.Ns.localState wb n).(B.PBP.output) r = Some csb ->
    let: v := fst (VBFTB.value_bft n r) in
    combined_verify (r, v) csb /\
    (exists l : list Address, 
      List.NoDup l /\ t0 < length l /\ 
      (forall n0, In n0 l -> BSettC.is_byz n0 = false /\ (C.Ns.localState wc n0).(C.PBP.echoed) (n, r) = Some (VBFTC.value_bft n r))).

Lemma unique_lock_availability_always_holds : C.always_holds unique_lock_availability.
Proof using Hconnect Hvsame Hwb wb.
  hnf. intros w Hr. hnf. intros. split_and?.
  - apply B.output_ok_always_holds in Hwb. hnf in Hwb. now saturate_assumptions!.
  - apply C.output_ok_always_holds in Hr. hnf in Hr. now saturate_assumptions!.
Qed.

Definition unique_key_availability := PB2Impl.unique_lock_availability.

End ABC.

End PB3.
