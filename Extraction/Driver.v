From Coq Require Import List Lia PeanoNat RelationClasses.
From Bythos.Systems Require Export Protocol.

From Coq Require Import Extraction.
Extraction Language OCaml.

(* some customization *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant ssrbool.is_left => "(fun x -> x)".
Extract Inductive list => "list" [ "[]" "( :: )" ].
Extract Inductive prod => "( * )"  [ "(,)" ]. (* removing the spaces in "( * )" would result in some parsing bug in vscoq? *)
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant Nat.leb => "( <= )".
Extract Constant Init.Nat.add => "( + )".
Extract Constant PeanoNat.Nat.add => "( + )".   (* TODO when extraction meets alias? *)
Extract Constant Init.Nat.sub => "( - )".
Extract Constant PeanoNat.Nat.sub => "( - )".
Extract Constant Init.Nat.div => "( / )".
Extract Constant PeanoNat.Nat.div => "( / )".   (* TODO how to eliminate divmod? *)
Extract Constant Nat.eq_dec => "( = )".
Extract Constant Init.Nat.eqb => "( = )".
Extract Constant PeanoNat.Nat.eqb => "( = )".

Extract Constant Datatypes.negb => "not".
Extract Constant Bool.bool_dec => "( = )".

Extract Constant List.length => "List.length".
Extract Constant List.app => "List.append".
Extract Constant List.map => "List.map".
Extract Constant List.forallb => "List.for_all".

Extract Constant Datatypes.fst => "fst".
Extract Constant Datatypes.snd => "snd".

Extraction Inline
  Nat.leb Init.Nat.add PeanoNat.Nat.add Init.Nat.sub PeanoNat.Nat.sub Init.Nat.div PeanoNat.Nat.div
    Nat.eq_dec Init.Nat.eqb PeanoNat.Nat.eqb
  Datatypes.negb Bool.bool_dec
  List.length List.app List.map List.forallb
  Datatypes.fst Datatypes.snd.

Extraction Blacklist String List. (* avoid messing up module names *)
Extraction Blacklist RB PB ABC RBABC. (* allowing individual extraction *)

From Bythos.Protocols.RB Require Protocol.
From Bythos.Protocols.PB Require Protocol.
From Bythos.Protocols.ABC Require Protocol.

From Bythos.Composition Require Import Protocol.
From Bythos.Protocols.RBABC Require Protocol.

(* avoid too much warnings on opaque things and "__" things *)
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".
Set Extraction Output Directory "Extraction/extracted".

(* NOTE: some proofs inside the cryptographic primitive-related modules will be extracted as well, 
    resulting in "__"; ignore them for now *)

(* it seems that we can only do the extraction inside the functor below, 
    if we do not try using other definitions of NetAddr, since A is the first argument of VBFT. 
    if A is the last argument, then we can simply make the type of RB.Types.ValueBFT
    to be "RB.Types.ValueBFT R V". *)
Module Playground (L : JustAList).

Module A := AddrAsFiniteList L.
Module BTh := ClassicByzThresholdImpl A.

Module RealRBProtocolImpl (R : Round) (V : Value) (VBFT : RB.Types.ValueBFT A R V). 

Import RB.Protocol.

Module RBM := RBMessageImpl A R V.
Module RBPk := SimplePacketImpl A RBM.

Include (RBProtocolImpl A R V VBFT BTh RBM RBPk).

End RealRBProtocolImpl.

Extraction "RB.ml" RealRBProtocolImpl.

(* we provide another wrapper over PB to instantiate TSSPrim before defining RealPBProtocolImpl,
    since in the companion file, the instantiation of PBProof may depend on light/combined signatures *)
(* FIXME: the instantiation of VBFT may depend on the full TSS, which will be instantiated only in PBProtocolImpl!
    for now, just use TSSPrim in the companion file *)
Module Playground2 (Sn : Signable) (PPrim : PKIPrim A Sn).

Module TSST <: TSSThres with Definition thres := A.N - BTh.f. Definition thres := A.N - BTh.f. End TSST.
Module TSSPrim := SimpleTSSPrim A Sn PPrim TSST.

Module RealPBProtocolImpl (R : Round) (V : Value) (Pf : PB.Types.PBProof)
  (VBFT : PB.Types.ValueBFT A R V Pf) (PBDT : PB.Types.PBDataTypes A R Sn V Pf).

Import PB.Protocol.

Module PBM := PBMessageImpl A R Sn V Pf TSSPrim.
Module PBPk := SimplePacketImpl A PBM.

Include (PBProtocolImpl A R Sn V Pf VBFT BTh TSSPrim PBDT PBM PBPk).

End RealPBProtocolImpl.

Extraction "PB.ml" RealPBProtocolImpl.

End Playground2.

Module RealACProtocolImpl (Sn : Signable) (V : SignableValue Sn) (PPrim : PKIPrim A Sn) (ACBTh : ByzThreshold A).

Import ABC.Protocol.

Module TSST <: TSSThres with Definition thres := A.N - ACBTh.f. Definition thres := A.N - ACBTh.f. End TSST.
Module TSSPrim := SimpleTSSPrim A Sn PPrim TSST.
Module ACDT := ABC.Types.SimpleACDataTypesImpl A Sn V PPrim TSSPrim.
Module ACM := ACMessageImpl A Sn V PPrim TSSPrim ACDT.
Module ACPk := SimplePacketImpl A ACM.

Include (ABC.Protocol.ACProtocolImpl A Sn V ACBTh PPrim TSSPrim ACDT ACM ACPk).

End RealACProtocolImpl.

Extraction "ABC.ml" RealACProtocolImpl.

Module RealRBABCProtocolImpl (R : Round) (ARP : RBABC.Types.AddrRoundPair A R) 
  (Sn : Signable) (V : SignableValue Sn) (VBFT : RB.Types.ValueBFT A R V) (PPrim : PKIPrim A Sn).

Module RBP := RealRBProtocolImpl R V VBFT.
Module ACP := RealACProtocolImpl Sn V PPrim BTh.
Module CM := Composition.Types.CompMessageImpl RBP.RBM ACP.ACM.
Module CPk := Composition.Types.CompSimplePacketImpl A RBP.RBM ACP.ACM CM RBP.RBPk ACP.ACPk.

Import RBABC.Protocol.

Module SCPT := RBACTrigger A R ARP Sn V VBFT BTh RBP.RBM PPrim ACP.TSSPrim ACP.ACDT ACP.ACM
  CM RBP.RBPk ACP.ACPk RBP ACP.

Include (SeqCompProtocol A RBP.RBM ACP.ACM BTh CM RBP.RBPk ACP.ACPk CPk RBP ACP SCPT).

End RealRBABCProtocolImpl.

Extraction "RBABC.ml" RealRBABCProtocolImpl.

Separate Extraction RealRBABCProtocolImpl. (* test *)

End Playground.
