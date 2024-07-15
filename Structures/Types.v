From Coq Require Import List RelationClasses Bool PeanoNat.
From Coq Require ListDec ssrbool.
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
  (* do not require injection here *)

End Signable.

Module Type PKIPrim (Export A : NetAddr) (Sn : Signable).

Parameter PrivateKey : Set.
Parameter Signature : Set.
Parameter Signature_eqdec : forall (s1 s2 : Signature), {s1 = s2} + {s1 <> s2}.

(* NOTE: actually using a key_map would expose all nodes' private keys to the current node, 
    but letting each node maintain its own key would require enriching the local state, 
    so here we only manually guarantee that key_map will only be applied to the current node's ID *)
(* similar issue for lightkey_map *)
Parameter key_map : Address -> PrivateKey.
Parameter verify : Sn.t -> Signature -> Address -> bool.
Parameter sign : Sn.t -> PrivateKey -> Signature.

(* symbolic security assumption *)

Axiom key_correct : forall v n s, 
  s = (sign v (key_map n)) <-> verify v s n.

Fact correct_sign_verify_ok v n :
  verify v (sign v (key_map n)) n.
Proof. now rewrite <- key_correct. Qed.

End PKIPrim.

Module PKI (Export A : NetAddr) (Sn : Signable) (Export PPrim : PKIPrim A Sn).

Section Extended. 

  Context {A : Type} `{SnA : Sn.signable A} (v : A).

  Definition verify (sig : Signature) (addr : Address) := verify (Sn.make v) sig addr.

  Definition sign (k : PrivateKey) := sign (Sn.make v) k.

  Corollary key_correct n s :
    s = (sign (key_map n)) <-> verify s n.
  Proof. apply key_correct. Qed.

  Corollary correct_sign_verify_ok n :
    verify (sign (key_map n)) n.
  Proof. now rewrite <- key_correct. Qed.

End Extended.

End PKI.

Module Type ThresholdSignatureSchemePrim (Export A : NetAddr) (Sn : Signable).

(* NOTE: by importing A, we implicitly allow thres to be a function over A.N *)
Parameter thres : nat.

Parameter LightPrivateKey : Set.
Parameter LightSignature : Set.
Parameter LightSignature_eqdec : forall (ls1 ls2 : LightSignature), {ls1 = ls2} + {ls1 <> ls2}.
Parameter CombinedSignature : Set.
Parameter CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.

Parameter lightkey_map : Address -> LightPrivateKey.
Parameter light_verify : Sn.t -> LightSignature -> Address -> bool.
Parameter light_sign : Sn.t -> LightPrivateKey -> LightSignature.

(* NOTE: we may use dependent type to restrict the number of light signatures *)
(* Parameter lightsig_combine : Vector.t LightSignature thres -> CombinedSignature. *)
Parameter lightsig_combine : list LightSignature -> CombinedSignature.
Parameter combined_verify : Sn.t -> CombinedSignature -> bool.

(* symbolic security assumption *)

Axiom lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.

Axiom combine_correct : forall v cs, 
  (exists ns : list Address, 
    NoDup ns /\ length ns = thres /\
    cs = lightsig_combine (map (fun n => light_sign v (lightkey_map n)) ns)) 
  <-> combined_verify v cs.

Fact correct_sign_verify_ok_light v n :
  light_verify v (light_sign v (lightkey_map n)) n.
Proof. now rewrite <- lightkey_correct. Qed.

End ThresholdSignatureSchemePrim. 

Module ThresholdSignatureScheme (Export A : NetAddr) (Sn : Signable) (Export TSSPrim : ThresholdSignatureSchemePrim A Sn).

Section Extended. 

  Context {A : Type} `{SnA : Sn.signable A} (v : A).

  Definition light_verify (lsig : LightSignature) (addr : Address) := light_verify (Sn.make v) lsig addr.

  Definition light_sign (k : LightPrivateKey) := light_sign (Sn.make v) k.

  Definition combined_verify (cs : CombinedSignature) := combined_verify (Sn.make v) cs.

  Corollary lightkey_correct n ls :
    ls = (light_sign (lightkey_map n)) <-> light_verify ls n.
  Proof. apply lightkey_correct. Qed.

  Corollary combine_correct cs :
    (exists ns : list Address, 
      NoDup ns /\ length ns = thres /\
      cs = lightsig_combine (map (fun n => light_sign (lightkey_map n)) ns)) 
    <-> combined_verify cs.
  Proof. apply combine_correct. Qed.

  Corollary correct_sign_verify_ok_light n :
    light_verify (light_sign (lightkey_map n)) n.
  Proof. now rewrite <- lightkey_correct. Qed.

End Extended.

End ThresholdSignatureScheme.

Module Type TSSThres. Parameter thres : nat. End TSSThres.

(* use PKI to emulate TSS; in this case, the threshold can be arbitrary *)

Module SimpleTSSPrim (Export A : NetAddr) (Sn : Signable) (Export PPrim : PKIPrim A Sn) (TSST : TSSThres)
  <: ThresholdSignatureSchemePrim A Sn with Definition thres := TSST.thres.

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
Definition combined_verify (v : Sn.t) (cs : CombinedSignature) :=
  (Nat.eq_dec (length cs) thres) && (ListDec.NoDup_dec Address_eqdec (map fst cs))
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
    NoDup ns /\ length ns = thres /\
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

End PacketType.

(* the canonical implementation of the packet type *)

Module Type SimplePacket (Export A : NetAddr) (Export M : MessageType) <: PacketType.

(* NOTE: defining Packet in this way may allow nodes to manipulate the received field.
    while in theory, the received field can only be modified by the network semantics, 
    allowing nodes to modify it might be exploited in some cases.
    for now, just manually inspect that nodes do not touch the received field *)
Record Packet_ : Type := mkP { src: Address; dst: Address; msg: Message; received: bool }.

Definition Packet := Packet_. (* as enforced by the module mechanism, we cannot directly define Packet to be a record *)

Definition Packet_eqdec : forall (p1 p2 : Packet), {p1 = p2} + {p1 <> p2}.
  intros. 
  decide equality; auto using Bool.bool_dec, Message_eqdec, Address_eqdec.
Qed.

Definition markRcv p :=
  let: mkP src dst msg _ := p in mkP src dst msg true.

Definition pkt_le p p' : Prop := p' = p \/ p' = markRcv p (* may be redundant, but make things simpler? *).

#[export] Instance Reflexive_pkt_le : Reflexive pkt_le.
Proof. now constructor. Qed.

Fact receive_pkt_intact [p] (H : received p) : markRcv p = p.
Proof. destruct p; simpl in *; now rewrite H. Qed.

Fact receive_pkt_intact_inv [p] (H : markRcv p = p) : received p.
Proof. destruct p; simpl in *; congruence. Qed.

Fact receive_pkt_idem p : markRcv (markRcv p) = markRcv p.
Proof. now destruct p. Qed.

Definition broadcast (src : Address) (m : Message) :=
  (map (fun x => mkP src x m false) valid_nodes).

Fact In_broadcast src m p :
  In p (broadcast src m) <-> exists dst, p = mkP src dst m false.
Proof. unfold broadcast. rewrite -> in_map_iff. pose proof Address_is_finite. firstorder; eauto. Qed.

Fact broadcast_all_fresh n m :
  Forall (fun p => p.(received) = false) (broadcast n m).
Proof. apply Forall_forall. now intros ? (? & ->)%In_broadcast. Qed.

Global Tactic Notation "simpl_pkt" :=
  simpl dst in *; simpl src in *; simpl msg in *; simpl received in *.

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
