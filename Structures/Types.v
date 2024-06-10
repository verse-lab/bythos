From Coq Require Import List RelationClasses Bool PeanoNat.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From Bythos.Structures Require Export Address.
From Bythos.Utils Require Export ListFacts.
(*
Module Type Signable.

Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.

End Signable.
*)
(* the design above is problematic. 
  intuitively, the signing function should work for anything which can be signed in reality ...
  in other words, if we can transform something into those signable, then that thing should be signable as well. 
  so typeclass should be a more suitable abstraction. *)

Module Type Signable.

Parameter t : Set. (* describing what can be signed in reality *)
Parameter eqdec : forall (v1 v2 : t), {v1 = v2} + {v1 <> v2}.
Class signable (A : Type) :=
  make : A -> t.
  (* { make : A -> t;
    make_inj : forall (a1 a2 : A), make a1 = make a2 -> a1 = a2 }. *)

End Signable.

(* FIXME: change V into Sn to keep naming consistency *)
Module Type PKIPrim (Export A : NetAddr) (V : Signable).

(* would expect that in this setting, an address is more or less a public key *)

Parameter PrivateKey : Set.
Parameter Signature : Set.
Parameter Signature_eqdec : forall (s1 s2 : Signature), {s1 = s2} + {s1 <> s2}.

Parameter key_map : Address -> PrivateKey.
Parameter verify : V.t -> Signature -> Address -> bool.
Parameter sign : V.t -> PrivateKey -> Signature.

(* symbolic security assumption *)

Axiom key_correct : forall v n s, 
  s = (sign v (key_map n)) <-> verify v s n.

Fact correct_sign_verify_ok v n :
  verify v (sign v (key_map n)) n.
Proof. now rewrite <- key_correct. Qed.
(*
Section Extended. 

  Context {A : Type} `{Sn : V.signable A}.

  Corollary key_correct' : forall (v : A) n s, 
    s = (sign (V.make v) (key_map n)) <-> verify (V.make v) s n.
  Proof. intros. now rewrite key_correct. Qed.

  Fact correct_sign_verify_ok v n :
    verify v (sign v (key_map n)) n.
  Proof. now rewrite <- key_correct. Qed.

End Extended. 
*)
End PKIPrim.

Module Type PKI (Export A : NetAddr) (V : Signable).

Declare Module PPrim : PKIPrim A V. (* TODO this introduces axiom when "Include"ing? *)
Export PPrim.

Section Extended. 

  Context {A : Type} `{Sn : V.signable A} (v : A).

  Definition verify (sig : Signature) (addr : Address) := verify (V.make v) sig addr.

  Definition sign (k : PrivateKey) := sign (V.make v) k.

  Corollary key_correct n s :
    s = (sign (key_map n)) <-> verify s n.
  Proof. apply key_correct. Qed.

  Corollary correct_sign_verify_ok n :
    verify (sign (key_map n)) n.
  Proof. now rewrite <- key_correct. Qed.

End Extended.

End PKI.

(* FIXME: eliminate such repetition by moving PPrim out *)
Module PKIImpl (Export A : NetAddr) (V : Signable) (P : PKIPrim A V) : PKI A V with Module PPrim := P.

Module Export PPrim <: PKIPrim A V := P.

Section Extended. 

  Context {A : Type} `{Sn : V.signable A} (v : A).

  Definition verify (sig : Signature) (addr : Address) := verify (V.make v) sig addr.

  Definition sign (k : PrivateKey) := sign (V.make v) k.

  Corollary key_correct n s :
    s = (sign (key_map n)) <-> verify s n.
  Proof. apply key_correct. Qed.

  Corollary correct_sign_verify_ok n :
    verify (sign (key_map n)) n.
  Proof. now rewrite <- key_correct. Qed.

End Extended.

End PKIImpl.

(*
Module PKIImpl (Export A : NetAddr) (V : Signable) <: PKI A V.

Include PKI A V.

End PKIImpl.
*)
(* ...? *)
(*
Module Type Signable'.

Parameter signable : Type -> Type.
Existing Class signable.

End Signable'.

Module Type PKI_Forall (Export A : NetAddr) (Export V : Signable').

Parameter PrivateKey : Set.
Parameter Signature : Set.
Parameter Signature_eqdec : forall (s1 s2 : Signature), {s1 = s2} + {s1 <> s2}.

Parameter key_map : Address -> PrivateKey.
Parameter verify : forall {Value : Type} `{signable Value}, Value -> Signature -> Address -> bool.
Parameter sign : forall {Value : Type} `{signable Value}, Value -> PrivateKey -> Signature.

Section Main.

  Context {Value : Type} `{VSn : signable Value}.

  (* symbolic security assumption *)

  Axiom key_correct : forall v n s, 
    s = (sign v (key_map n)) <-> verify v s n.

  Fact correct_sign_verify_ok v n :
    verify v (sign v (key_map n)) n.
  Proof. now rewrite <- key_correct. Qed.

End Main.

End PKI_Forall.
*)
Module Type ThresholdSignatureSchemePrim (Export A : NetAddr) (V : Signable).

Parameter thres : nat.

Parameter LightPrivateKey : Set.
Parameter LightSignature : Set.
Parameter LightSignature_eqdec : forall (ls1 ls2 : LightSignature), {ls1 = ls2} + {ls1 <> ls2}.
Parameter CombinedSignature : Set.
Parameter CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.

Parameter lightkey_map : Address -> LightPrivateKey.
Parameter light_verify : V.t -> LightSignature -> Address -> bool.
Parameter light_sign : V.t -> LightPrivateKey -> LightSignature.
(* use dependent type to restrict the number of light signatures *)
(* Parameter lightsig_combine : Vector.t LightSignature (N - t0) -> CombinedSignature. *)

Parameter lightsig_combine : list LightSignature -> CombinedSignature.
Parameter combined_verify : V.t -> CombinedSignature -> bool.

(* symbolic security assumption *)

Axiom lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.

Axiom combine_correct : forall v cs, 
  (exists ns : list Address, 
  (* FIXME: in the future, change N - thres into thres *)
    NoDup ns /\ length ns = N - thres /\
    cs = lightsig_combine (map (fun n => light_sign v (lightkey_map n)) ns)) 
  <-> combined_verify v cs.

Fact correct_sign_verify_ok_light v n :
  light_verify v (light_sign v (lightkey_map n)) n.
Proof. now rewrite <- lightkey_correct. Qed.

End ThresholdSignatureSchemePrim. 

Module Type ThresholdSignatureScheme (Export A : NetAddr) (V : Signable).

Declare Module TSSPrim : ThresholdSignatureSchemePrim A V.
Export TSSPrim.

Section Extended. 

  Context {A : Type} `{Sn : V.signable A} (v : A).

  Definition light_verify (lsig : LightSignature) (addr : Address) := light_verify (V.make v) lsig addr.

  Definition light_sign (k : LightPrivateKey) := light_sign (V.make v) k.

  Definition combined_verify (cs : CombinedSignature) := combined_verify (V.make v) cs.

  Corollary lightkey_correct n ls :
    ls = (light_sign (lightkey_map n)) <-> light_verify ls n.
  Proof. apply lightkey_correct. Qed.

  Corollary combine_correct cs :
    (exists ns : list Address, 
      NoDup ns /\ length ns = N - thres /\
      cs = lightsig_combine (map (fun n => light_sign (lightkey_map n)) ns)) 
    <-> combined_verify cs.
  Proof. apply combine_correct. Qed.

  Corollary correct_sign_verify_ok_light n :
    light_verify (light_sign (lightkey_map n)) n.
  Proof. now rewrite <- lightkey_correct. Qed.

End Extended.

End ThresholdSignatureScheme.

(* FIXME: eliminate such repetition by moving TSSPrim out *)
Module ThresholdSignatureSchemeImpl (Export A : NetAddr) (V : Signable) (Export TSS : ThresholdSignatureSchemePrim A V)
  : ThresholdSignatureScheme A V with Module TSSPrim := TSS.

Module Export TSSPrim <: ThresholdSignatureSchemePrim A V := TSS.

Section Extended. 

  Context {A : Type} `{Sn : V.signable A} (v : A).

  Definition light_verify (lsig : LightSignature) (addr : Address) := light_verify (V.make v) lsig addr.

  Definition light_sign (k : LightPrivateKey) := light_sign (V.make v) k.

  Definition combined_verify (cs : CombinedSignature) := combined_verify (V.make v) cs.

  Corollary lightkey_correct n ls :
    ls = (light_sign (lightkey_map n)) <-> light_verify ls n.
  Proof. apply lightkey_correct. Qed.

  Corollary combine_correct cs :
    (exists ns : list Address, 
      NoDup ns /\ length ns = N - thres /\
      cs = lightsig_combine (map (fun n => light_sign (lightkey_map n)) ns)) 
    <-> combined_verify cs.
  Proof. apply combine_correct. Qed.

  Corollary correct_sign_verify_ok_light n :
    light_verify (light_sign (lightkey_map n)) n.
  Proof. now rewrite <- lightkey_correct. Qed.

End Extended.

End ThresholdSignatureSchemeImpl.

(*
Module ThresholdSignatureSchemeImpl (Export A : NetAddr) (V : Signable) <: ThresholdSignatureScheme A V.

Include ThresholdSignatureScheme A V.

End ThresholdSignatureSchemeImpl.
*)

Module Type TSSThres. Parameter thres : nat. End TSSThres.

Module SimpleTSSPrim (Export A : NetAddr) (V : Signable) (Export PPrim : PKIPrim A V) (TSST : TSSThres)
  <: ThresholdSignatureSchemePrim A V with Definition thres := TSST.thres.

(* use PKI to emulate TSS; in this case, the threshold can be arbitrary *)

Definition thres := TSST.thres.

(* key trick: inject the node identity into LightPrivateKey *)
Definition LightPrivateKey := (Address * PrivateKey)%type.
Definition LightSignature := (Address * Signature)%type.
Definition LightSignature_eqdec := prod_eq_dec Address_eqdec Signature_eqdec.

Definition CombinedSignature := list LightSignature. 
Definition CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.
  intros.
  apply list_eq_dec, LightSignature_eqdec.
Defined.

Definition lightkey_map n := (n, key_map n).
Definition light_verify v lsig n := 
  if Address_eqdec n (fst lsig) then verify v (snd lsig) n else false.
Definition light_sign v (pk : LightPrivateKey) := (fst pk, sign v (snd pk)).

(* simply putting id here may introduce Obj.magic *)
Definition lightsig_combine (l : list LightSignature) : CombinedSignature := l.
Definition combined_verify (v : V.t) (cs : CombinedSignature) :=
  (Nat.eq_dec (length cs) (N - thres)) && (NoDup_eqdec Address_eqdec (map fst cs))
    && (forallb (fun '(n, sig) => verify v sig n) cs).

Lemma lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.
Proof.
  intros v n (n', sig). unfold lightkey_map, light_verify, light_sign. simpl. split.
  - intros [= -> ->]. rewrite eqdec_refl. apply correct_sign_verify_ok.
  - intros H. destruct (Address_eqdec n n') as [ <- | ]; try discriminate. f_equal. now apply key_correct.
Qed.

Lemma combine_correct : forall v cs, 
  (exists ns : list Address, 
    NoDup ns /\ length ns = N - thres /\
    cs = lightsig_combine (map (fun n => light_sign v (lightkey_map n)) ns)) 
  <-> combined_verify v cs.
Proof.
  intros v cs. 
  unfold combined_verify, is_true, lightsig_combine, light_sign. simpl. 
  rewrite !andb_true_iff, forallb_forall. autorewrite with booldec. 
  split.
  - intros (ns & Hnodup & Hlen & ->). 
    rewrite !map_length, map_map. simpl. rewrite map_id. autorewrite with booldec. 
    split; [ split | ]; auto.
    intros ? (n & <- & H)%in_map_iff. apply correct_sign_verify_ok.
  - intros ((Hlen & Hnodup) & H). exists (map fst cs).
    rewrite !map_length, map_map. 
    split; [ | split ]; auto.
    clear -H. rewrite <- Forall_forall in H. induction H as [ | (n, sig) cs H0 H IH ]; auto.
    simpl. rewrite <- IH. do 2 f_equal. now apply key_correct.
Qed. 

Fact correct_sign_verify_ok_light v n :
  light_verify v (light_sign v (lightkey_map n)) n.
Proof. now rewrite <- lightkey_correct. Qed.

End SimpleTSSPrim. 

Module Type MessageType.

Parameter Message : Type.
Parameter Message_eqdec : forall (m1 m2 : Message), {m1 = m2} + {m1 <> m2}.

End MessageType.

Module Type PacketType.

Parameter Packet : Type.
Parameter Packet_eqdec : forall (p1 p2 : Packet), {p1 = p2} + {p1 <> p2}.

(* TODO add primitives that packet should support? like send_to and broadcast?
    we need to make sure that a node does not have access to the consumed field of a packet
    since it is only for proving!
  for now, ensure it by manual inspection *)

End PacketType.

Module Type SimplePacket (Export A : NetAddr) (Export M : MessageType) <: PacketType.

Record Packet_ : Type := mkP { src: Address; dst: Address; msg: Message; consumed: bool }.

Definition Packet := Packet_. (* TODO this is bad! required by the module type *)
(* Global Arguments Packet : simpl never. *)

Definition Packet_eqdec : forall (p1 p2 : Packet), {p1 = p2} + {p1 <> p2}.
  intros. 
  decide equality; auto using Bool.bool_dec, Message_eqdec, Address_eqdec.
Qed.

Definition receive_pkt p :=
  let: mkP src dst msg _ := p in mkP src dst msg true.

Definition pkt_le p p' : Prop := p' = p \/ p' = receive_pkt p (* may be redundant, but make things simpler? *).

#[export] Instance Reflexive_pkt_le : Reflexive pkt_le.
Proof. now constructor. Qed.

Fact receive_pkt_intact [p] (H : consumed p) : receive_pkt p = p.
Proof. destruct p; simpl in *; now rewrite H. Qed.

Fact receive_pkt_intact_inv [p] (H : receive_pkt p = p) : consumed p.
Proof. destruct p; simpl in *; congruence. Qed.

Fact receive_pkt_idem p : receive_pkt (receive_pkt p) = receive_pkt p.
Proof. now destruct p. Qed.

Definition broadcast (src : Address) (m : Message) :=
  (map (fun x => mkP src x m false) valid_nodes).

Fact In_broadcast src m p :
  In p (broadcast src m) <-> exists dst, p = mkP src dst m false.
Proof. unfold broadcast. rewrite -> in_map_iff. pose proof Address_is_finite. firstorder; eauto. Qed.

Fact broadcast_all_fresh n m :
  Forall (fun p => p.(consumed) = false) (broadcast n m).
Proof. apply Forall_forall. now intros ? (? & ->)%In_broadcast. Qed.

Global Tactic Notation "simpl_pkt" :=
  simpl dst in *; simpl src in *; simpl msg in *; simpl consumed in *.

End SimplePacket.

Module SimplePacketImpl (Export A : NetAddr) (Export M : MessageType) <: (SimplePacket A M) <: PacketType.

Include SimplePacket A M.

End SimplePacketImpl.

(* some commonly used concepts *)

Module Type Value.

Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.
Parameter Value_inhabitant : Value.     (* should be benign *)

End Value.

Module Type SignableValue (Sn : Signable).

Include Value.
Declare Instance VSn : Sn.signable Value.

End SignableValue.

Module Type Round.

Parameter Round : Type.
Parameter Round_eqdec : forall r1 r2 : Round, {r1 = r2} + {r1 <> r2}.

End Round.
