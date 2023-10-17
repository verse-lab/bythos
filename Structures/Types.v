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

(* TODO should this key & signature be of the same type as above? *)
Parameter LightPrivateKey : Set.
Parameter LightSignature : Set.
Parameter LightSignature_eqdec : forall (ls1 ls2 : LightSignature), {ls1 = ls2} + {ls1 <> ls2}.
Parameter CombinedSignature : Set.
Parameter CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.

Parameter key_map : Address -> PrivateKey.
Parameter verify : Value -> Signature -> Address -> bool.
Parameter sign : Value -> PrivateKey -> Signature.

Parameter lightkey_map : Address -> LightPrivateKey.
(* TODO if there is only one public key for this, should the address component be used or not? *)
Parameter light_verify : Value -> LightSignature -> Address -> bool.
Parameter light_sign : Value -> LightPrivateKey -> LightSignature.
(* use dependent type to restrict the number of light signatures *)
(* Parameter lightsig_combine : Vector.t LightSignature (N - t0) -> CombinedSignature. *)
(* TODO using dependent type may incur difficulty in the protocol, so use a total function at first 
  if the number of light certificates is not (N-t0), then simply return some garbage
  (guaranteed by "combine_correct" below) *)
Parameter lightsig_combine : list LightSignature -> CombinedSignature.
Parameter combined_verify : Value -> CombinedSignature -> bool.

Axiom key_correct : forall v n s, 
  s = (sign v (key_map n)) <-> verify v s n.

Axiom lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.

Axiom combine_correct : forall v cs, 
  (exists ns : list Address, 
    NoDup ns /\ incl ns valid_nodes /\ length ns = N - t0 /\
    cs = lightsig_combine (map (fun n => light_sign v (lightkey_map n)) ns)) 
  <-> combined_verify v cs.

Fact correct_sign_verify_ok v n :
  verify v (sign v (key_map n)) n.
Proof. now rewrite <- key_correct. Qed.

Fact correct_sign_verify_ok_light v n :
  light_verify v (light_sign v (lightkey_map n)) n.
Proof. now rewrite <- lightkey_correct. Qed.

(* temporarily use list; there should be some notation of finite multisets or ...? *)

Definition AddrSigPair_eqdec : forall (nsig1 nsig2 : Address * Signature), {nsig1 = nsig2} + {nsig1 <> nsig2}.
  intros. decide equality.
  - apply Signature_eqdec. 
  - apply Address_eqdec.
Qed. 

Definition AddrLightSigPair_eqdec : forall (nsig1 nsig2 : Address * LightSignature), {nsig1 = nsig2} + {nsig1 <> nsig2}.
  intros. decide equality.
  - apply LightSignature_eqdec. 
  - apply Address_eqdec.
Qed. 

Definition Certificate : Type := Value * list (Address * Signature).
Definition LightCertificate : Type := Value * CombinedSignature.

Definition Certificate_eqdec : forall (c1 c2 : Certificate), {c1 = c2} + {c1 <> c2}.
  intros. decide equality. 1: do 2 (decide equality).
  - apply Signature_eqdec. 
  - apply Address_eqdec.
  - apply Value_eqdec.
Qed. 

Definition LightCertificate_eqdec : forall (c1 c2 : LightCertificate), {c1 = c2} + {c1 <> c2}.
  intros. decide equality.
  - apply CombinedSignature_eqdec. 
  - apply Value_eqdec.
Qed. 

Parameter lightcert_conflict_check : list LightCertificate -> bool.
Parameter genproof : list Certificate -> list Address.

Definition lightcert_conflict_check_spec (lcc : list LightCertificate -> bool) : Prop :=
  forall lcerts, lcc lcerts <-> 
    exists v1 v2 cs1 cs2,
      v1 <> v2 /\
      In (v1, cs1) lcerts /\
      In (v2, cs2) lcerts.

Axiom lightcert_conflict_check_correct : lightcert_conflict_check_spec lightcert_conflict_check.

Definition genproof_can_detect (genproof : list Certificate -> list Address) : Prop :=
  forall certs n, In n (genproof certs) <-> 
    exists v1 v2 sig1 sig2 nsigs1 nsigs2,
      v1 <> v2 /\
      In (v1, nsigs1) certs /\
      In (v2, nsigs2) certs /\
      In (n, sig1) nsigs1 /\
      In (n, sig2) nsigs2.

Record genproof_spec (genproof : list Certificate -> list Address) : Prop := {
  _ : genproof_can_detect genproof;
  _ : forall certs, NoDup (genproof certs)
}.

Axiom genproof_correct : genproof_spec genproof.

(* should give concrete checkers which does not depend on knowing
    key_map so that it is not vacuous
  TODO for now simply keep them here
*)

Fixpoint lcc_simple_aux (v : Value) (certs : list LightCertificate) : bool :=
  match certs with 
  | nil => false 
  | (v', _) :: certs' => if Value_eqdec v v' then lcc_simple_aux v certs' else true 
  end.

Fixpoint lcc_simple (certs : list LightCertificate) : bool :=
  match certs with
  | nil => false
  | (v, _) :: certs' => (lcc_simple_aux v certs') || (lcc_simple certs')
  end.

Lemma lcc_simple_aux_can_detect v certs : 
  lcc_simple_aux v certs <-> exists v' cs', v <> v' /\ In (v', cs') certs.
Proof with (first [ intuition congruence; fail | firstorder; fail | idtac ]).
  induction certs as [ | (v', cs') certs IH ]; simpl.
  - split...
  - destruct (Value_eqdec v v') as [ <- | Hvneq ]...
    + rewrite IH.
      firstorder.
      congruence...
    + split...
      intros _.
      eauto.
Qed.

Lemma lcc_simple_correct : lightcert_conflict_check_spec lcc_simple.
Proof with (first [ intuition congruence; fail | firstorder; fail | idtac ]).
  hnf.
  intros.
  induction lcerts as [ | (v, cs) lcerts IH ]; simpl.
  - split...
  - destruct (lcc_simple_aux v lcerts) eqn:E.
    + split...
      intros _.
      apply lcc_simple_aux_can_detect in E.
      destruct E as (v' & cs' & Hvneq & Hin).
      exists v, v', cs, cs'...
    + simpl.
      pose proof (lcc_simple_aux_can_detect v lcerts) as HH.
      unfold is_true in HH.
      rewrite <- Bool.not_true_iff_false, -> HH in E.
      rewrite IH.
      split.
      * intros (v1 & v2 & cs1 & cs2 & Hvneq & Hin1 & Hin2).
        exists v1, v2, cs1, cs2...
      * intros (v1 & v2 & cs1 & cs2 & Hvneq & [ E1 | Hin1 ] & [ E2 | Hin2 ]).
        1: idtac...
        1-2: try inversion E1; try inversion E2; subst.
        1-2: exfalso; apply E; eauto.
        exists v1, v2, cs1, cs2...
Qed.

Definition genproof_simple_aux_aux (c : Certificate) (certs : list Certificate) :=
  (List.flat_map 
    (fun c' => if Value_eqdec (fst c) (fst c') 
                then nil 
                else (filter 
                  (fun n => In_dec Address_eqdec n (map fst (snd c))) 
                  (map fst (snd c')))) certs).

Fixpoint genproof_simple_aux (certs : list Certificate) : list Address :=
  match certs with
  | nil => nil
  | c :: certs' => (genproof_simple_aux_aux c certs') ++ (genproof_simple_aux certs')
  end.

Definition genproof_simple (certs : list Certificate) : list Address :=
  nodup Address_eqdec (genproof_simple_aux certs).

Lemma genproof_simple_aux_aux_can_detect v nsigs certs n : 
  In n (genproof_simple_aux_aux (v, nsigs) certs) <-> 
  exists v' nsigs',
    v <> v' /\
    In (v', nsigs') certs /\
    In n (map fst nsigs) /\
    In n (map fst nsigs').
Proof.
  induction certs as [ | (v_, nsigs_) certs IH ].
  - firstorder.
  - simpl.
    rewrite -> in_app_iff, -> IH.
    clear IH.
    destruct (Value_eqdec v v_) as [ <- | Hvneq ].
    + firstorder.
      congruence.
    + rewrite -> filter_In.
      (* awkward ... *)
      assert (in_dec Address_eqdec n (map fst nsigs) <-> In n (map fst nsigs)) as Hp.
      {
        unfold is_true.
        now destruct (in_dec Address_eqdec n (map fst nsigs)).
      }
      rewrite -> Hp.
      intuition firstorder congruence.
Qed.

Lemma genproof_simple_aux_can_detect certs n : In n (genproof_simple_aux certs) <-> 
  exists v1 v2 nsigs1 nsigs2,
    v1 <> v2 /\
    In (v1, nsigs1) certs /\
    In (v2, nsigs2) certs /\
    In n (map fst nsigs1) /\
    In n (map fst nsigs2).
Proof.
  induction certs as [ | (v, nsigs) certs IH ].
  - firstorder.
  - simpl.
    rewrite -> in_app_iff, -> IH, -> genproof_simple_aux_aux_can_detect.
    clear IH.
    split.
    + intros [ (v' & nsigs' & Hvneq & Hin' & Hin_nsigs & Hin_nsigs') | 
        (v1 & v2 & nsigs1 & nsigs2 & Hvneq & Hin1 & Hin2 & Hin_nsigs1 & Hin_nsigs2) ].
      * exists v, v', nsigs, nsigs'.
        intuition.
      * exists v1, v2, nsigs1, nsigs2.
        intuition.
    + intros (v1 & v2 & nsigs1 & nsigs2 & Hvneq & [ Hin1 | Hin1 ] & [ Hin2 | Hin2 ] & Hin_nsigs1 & Hin_nsigs2).
      all: try congruence.
      1-2: left.
      1: exists v2, nsigs2.
      2: exists v1, nsigs1.
      1-2: intuition congruence.
      right.
      exists v1, v2, nsigs1, nsigs2.
      intuition.
Qed.

Lemma genproof_simple_correct : genproof_spec genproof_simple.
Proof.
  unfold genproof_simple.
  constructor.
  - hnf.
    intros.
    rewrite -> nodup_In, -> genproof_simple_aux_can_detect.
    repeat setoid_rewrite -> in_map_iff.
    split.
    + intros (v1 & v2 & nsigs1 & nsigs2 & ? & ? & ? & ((n', sig1) & Htmp1 & ?) & ((n'', sig2) & Htmp2 & ?)).
      simpl in Htmp1, Htmp2.
      subst n' n''.
      now exists v1, v2, sig1, sig2, nsigs1, nsigs2.
    + intros (v1 & v2 & sig1 & sig2 & nsigs1 & nsigs2 & ? & ? & ? & ? & ?).
      exists v1, v2, nsigs1, nsigs2.
      firstorder.
  - intros. 
    now apply NoDup_nodup.
Qed.

End Types.
