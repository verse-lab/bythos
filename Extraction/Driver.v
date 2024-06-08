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

Extract Constant Datatypes.negb => "not".
Extract Constant Bool.bool_dec => "( = )".

Extract Constant List.length => "List.length".
Extract Constant List.app => "List.append".
Extract Constant List.map => "List.map".

Extract Constant Datatypes.fst => "fst".
Extract Constant Datatypes.snd => "snd".

Extraction Inline
  Nat.leb Init.Nat.add PeanoNat.Nat.add Init.Nat.sub PeanoNat.Nat.sub Init.Nat.div PeanoNat.Nat.div Nat.eq_dec
  Datatypes.negb Bool.bool_dec
  List.length List.app List.map
  Datatypes.fst Datatypes.snd.

From Bythos.Protocols.RB Require Import Protocol.
Pwd.

(* it seems that we can only do the extraction inside the module, if we do not try using other definitions of NetAddr *)
Module Playground (L : JustAList).

Module A := AddrAsFiniteType3 L.

Module RealRBProtocolImpl (R : Round) (V : Value) (VBFT : ValueBFT A R V). 

Module RealClassicByzThresholdImpl := ClassicByzThresholdImpl A.
Module RealRBMessageImpl := RBMessageImpl A R V.
Module RealSimplePacketImpl := SimplePacketImpl A RealRBMessageImpl.

Include (RBProtocolImpl A R V VBFT RealClassicByzThresholdImpl RealRBMessageImpl RealSimplePacketImpl).

End RealRBProtocolImpl.

Cd "Extraction/extracted".
Extraction "RB.ml" RealRBProtocolImpl.
Cd "../..".

End Playground.
