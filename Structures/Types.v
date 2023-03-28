From Coq Require Import List ssrbool.
From ABCProtocol Require Export Address.


Module Type Types (A : NetAddr).

Import A.

(* Some design choices: 
1. receiving key or not?
2. how to relate with history?
3. sending key or not (use address as sending key --> let that node use its own key)

on value: 
1. total or partial function?
2. make it a part of network or here?
*)

Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.

(* FIXME: it seems that value_bft, as well as the value stored in a node's state
    will never change. maybe we only need to store one of them
  or, only use for initialization but do not mention it afterwards?
*)

Parameter value_bft : Address -> Value.

Parameter PrivateKey : Set.
Parameter Signature : Set.
Parameter Signature_eqdec : forall (s1 s2 : Signature), {s1 = s2} + {s1 <> s2}.

Parameter key_map : Address -> PrivateKey.
Parameter verify : Value -> Signature -> Address -> bool.
Parameter sign : Value -> PrivateKey -> Signature.

Axiom key_correct : forall v n s, 
  s = (sign v (key_map n)) <-> verify v s n.

Fact correct_sign_verify_ok v n :
  verify v (sign v (key_map n)) n.
Proof. now rewrite <- key_correct. Qed.

(* temporarily use list; there should be some notation of finite multisets or ...? *)

Definition AddrSigPair_eqdec : forall (nsig1 nsig2 : Address * Signature), {nsig1 = nsig2} + {nsig1 <> nsig2}.
  intros. decide equality.
  - apply Signature_eqdec. 
  - apply Address_eqdec.
Qed. 

Definition Certificate : Type := Value * list (Address * Signature).

Definition Certificate_eqdec : forall (c1 c2 : Certificate), {c1 = c2} + {c1 <> c2}.
  intros. decide equality. 1: do 2 (decide equality).
  - apply Signature_eqdec. 
  - apply Address_eqdec.
  - apply Value_eqdec.
Qed. 

Parameter genproof : list Certificate -> list Address.

Axiom genproof_spec : 
  forall certs n, In n (genproof certs) <-> 
    exists v1 v2 nsigs1 nsigs2,
      v1 <> v2 /\
      In (v1, nsigs1) certs /\
      In (v2, nsigs2) certs /\
      In (n, sign v1 (key_map n)) nsigs1 /\
      In (n, sign v2 (key_map n)) nsigs2.

Axiom genproof_nodup : forall certs, NoDup (genproof certs).

End Types.
