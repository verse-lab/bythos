From Coq Require Import List.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Structures Require Export Types.
(* to compose ABC with other protocols, it is not good to use ValueBFT *)
(*
Module Type ValueBFT (Export A : NetAddr) (Sn : Signable) (Export V : SignableValue Sn).

Parameter value_bft : Address -> Value.

End ValueBFT.
*)

Module Type ACDataTypes.

Parameter Certificate : Type.
Parameter LightCertificate : Type.

Axiom Certificate_eqdec : forall (c1 c2 : Certificate), {c1 = c2} + {c1 <> c2}.
Axiom LightCertificate_eqdec : forall (c1 c2 : LightCertificate), {c1 = c2} + {c1 <> c2}.

End ACDataTypes.

Module Type SimpleACDataTypes (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (PPrim : PKIPrim A Sn) (TSSPrim : ThresholdSignatureSchemePrim A Sn)
  <: ACDataTypes.

Module Import P := PKI A Sn PPrim.
Module Import TSS := ThresholdSignatureScheme A Sn TSSPrim.

Import A V.

Definition AddrSigPair_eqdec : forall (nsig1 nsig2 : Address * Signature), {nsig1 = nsig2} + {nsig1 <> nsig2}
  := prod_eq_dec Address_eqdec Signature_eqdec.

Definition AddrLightSigPair_eqdec : forall (nsig1 nsig2 : Address * LightSignature), {nsig1 = nsig2} + {nsig1 <> nsig2}
  := prod_eq_dec Address_eqdec LightSignature_eqdec.

(* temporarily use list; there should be some notation of finite multisets or ...? *)

Definition Certificate : Type := Value * list (Address * Signature).
Definition LightCertificate : Type := Value * CombinedSignature.

Definition Certificate_eqdec : forall (c1 c2 : Certificate), {c1 = c2} + {c1 <> c2}
  := prod_eq_dec Value_eqdec (list_eq_dec AddrSigPair_eqdec).

Definition LightCertificate_eqdec : forall (c1 c2 : LightCertificate), {c1 = c2} + {c1 <> c2}
  := prod_eq_dec Value_eqdec CombinedSignature_eqdec.

(* put this module type inside this concrete instantiation of ACDataTypes, since the following
    two axioms depend on the concrete definitions of Certificate/LightCertificate *)
Module Type CertCheckers.

Parameter lightcert_conflict_check : list LightCertificate -> bool.
Parameter genproof : list Certificate -> list Address.

Axiom lightcert_conflict_check_correct : 
  forall lcerts, lightcert_conflict_check lcerts <-> 
    exists v1 v2 cs1 cs2,
      v1 <> v2 /\
      In (v1, cs1) lcerts /\
      In (v2, cs2) lcerts.

Axiom genproof_correct : 
  (forall certs, NoDup (genproof certs)) /\
  (forall certs n, In n (genproof certs) <-> 
    exists v1 v2 sig1 sig2 nsigs1 nsigs2,
      v1 <> v2 /\
      In (v1, nsigs1) certs /\
      In (v2, nsigs2) certs /\
      In (n, sig1) nsigs1 /\
      In (n, sig2) nsigs2).

End CertCheckers.

(* a naive instantiation of CertCheckers *)
Module Export CertCheckersImpl : CertCheckers.

(* run in linear time *)
Fixpoint lcc_simple (certs : list LightCertificate) : bool :=
  match certs with
  | nil => false
  | (v, _) :: certs' =>
    match certs' with
    | cs' :: certs'' => if Value_eqdec v (fst cs') then lcc_simple certs' else true
    | nil => false
    end
  end.

Definition lightcert_conflict_check := lcc_simple.

Lemma lightcert_conflict_check_correct : 
  forall lcerts, lightcert_conflict_check lcerts <-> 
    exists v1 v2 cs1 cs2,
      v1 <> v2 /\
      In (v1, cs1) lcerts /\
      In (v2, cs2) lcerts.
Proof with (first [ intuition congruence; fail | firstorder; fail | idtac ]).
  unfold lightcert_conflict_check.
  intros.
  induction lcerts as [ | (v, cs) lcerts IH ]; simpl.
  - split...
  - destruct lcerts as [ | (v', cs') lcerts' ] eqn:E.
    + simpl.
      try firstorder; try congruence.
    + rewrite <- E in IH |- *.
      simpl fst.
      destruct (Value_eqdec _ _) as [ <- | Hvneq ].
      * rewrite IH.
        split.
        --intros (v1 & v2 & cs1 & cs2 & Hvneq & Hin1 & Hin2).
          exists v1, v2, cs1, cs2...
        --subst lcerts.
          intros (v1 & v2 & cs1 & cs2 & Hvneq & [ E1 | Hin1 ] & [ E2 | Hin2 ]).
          1: idtac...
          3: exists v1, v2, cs1, cs2...
          1: inversion E1.
          2: inversion E2.
          1-2: subst.
          ++exists v1, v2, cs', cs2...
          ++exists v1, v2, cs1, cs'...
      * split; auto.
        rewrite E.
        exists v, v', cs, cs'...
Qed.

(* NOTE: genproof can also be done in linear time, but to get all possible culprits,
    we use an O(n^3) algorithm here to extract all culprits detectable in some pair of conflicting certificates *)

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

Definition genproof := genproof_simple.

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
    + unfold ssrbool.is_left.
      rewrite -> filter_In, ! sumbool_is_left.
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

Lemma genproof_correct : 
  (forall certs, NoDup (genproof certs)) /\
  (forall certs n, In n (genproof certs) <-> 
    exists v1 v2 sig1 sig2 nsigs1 nsigs2,
      v1 <> v2 /\
      In (v1, nsigs1) certs /\
      In (v2, nsigs2) certs /\
      In (n, sig1) nsigs1 /\
      In (n, sig2) nsigs2).
Proof.
  unfold genproof, genproof_simple.
  split.
  - intros. 
    now apply NoDup_nodup.
  - intros.
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
Qed.

End CertCheckersImpl.

End SimpleACDataTypes.

Module Type ACMessage (A : NetAddr) (Sn : Signable) (V : SignableValue Sn) (PPrim : PKIPrim A Sn) (TSSPrim : ThresholdSignatureSchemePrim A Sn)
  (ACDT : ACDataTypes) <: MessageType.

Import A V PPrim TSSPrim ACDT.

Inductive Message_ := 
  | SubmitMsg (v : Value) (ls : LightSignature) (s : Signature)
  | LightConfirmMsg (c : LightCertificate)
  (* for historical reasons, this remains the name as "ConfirmMsg". *)
  | ConfirmMsg (c : Certificate).

Definition Message := Message_.

Definition Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.
  intros. 
  decide equality; auto using Signature_eqdec, LightSignature_eqdec, 
    Value_eqdec, LightCertificate_eqdec, Certificate_eqdec.
Qed.

End ACMessage.
