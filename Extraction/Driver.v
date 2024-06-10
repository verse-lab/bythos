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

From Bythos.Protocols.RB Require Protocol.
From Bythos.Protocols.PB Require Protocol.

(* it seems that we can only do the extraction inside the functor below, 
    if we do not try using other definitions of NetAddr, since A is the first argument of VBFT. 
    if A is the last argument, then we can simply make the type of RB.Types.ValueBFT
    to be "RB.Types.ValueBFT R V". *)
Module Playground (L : JustAList).

Module A := AddrAsFiniteType3 L.

Module RealRBProtocolImpl (R : Round) (V : Value) (VBFT : RB.Types.ValueBFT A R V). 

Import RB.Protocol.

Module BTh := ClassicByzThresholdImpl A.
Module RBM := RBMessageImpl A R V.
Module RBPk := SimplePacketImpl A RBM.

Include (RBProtocolImpl A R V VBFT BTh RBM RBPk).

End RealRBProtocolImpl.

Module RealPBProtocolImpl (R : Round) (Sn : Signable) (V : Value) (Pf : PB.Types.PBProof Sn)
  (VBFT : PB.Types.ValueBFT A R Sn V Pf) (PBDT0 : PB.Types.PBDataTypes A R Sn V Pf)
  (PPrim : PKIPrim A Sn).

Import PB.Protocol.

Module BTh := ClassicByzThresholdImpl A.
Module TSST <: TSSThres with Definition thres := BTh.t0. Definition thres := BTh.t0. End TSST.
Module TSS0 := SimpleTSSPrim A Sn PPrim TSST.
Module TSS := ThresholdSignatureSchemeImpl A Sn TSS0.
Module PBDT := PBDT0 TSS.
Module PBM := PBMessageImpl A R Sn V Pf TSS.
Module PBPk := SimplePacketImpl A PBM.

Include (PBProtocolImpl A R Sn V Pf VBFT BTh TSS0 TSS PBDT PBM PBPk).

End RealPBProtocolImpl.

Cd "Extraction/extracted".
Extraction "RB.ml" RealRBProtocolImpl.
Extraction "PB.ml" RealPBProtocolImpl. (* some proofs will be extracted as well, resulting in "__"; ignore them for now *)
Cd "../..".

End Playground.
