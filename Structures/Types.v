From Coq Require Import List RelationClasses.
From Coq Require ssrbool.
Import (coercions) ssrbool.
From ABCProtocol.Structures Require Export Address.
From ABCProtocol.Utils Require Export ListFacts.

Module Type Signable.

(* ideally, this would be "bytes" ... here model the objects that can be signed *)

Parameter Value : Set.
Parameter Value_eqdec : forall (v1 v2 : Value), {v1 = v2} + {v1 <> v2}.

End Signable.

Module Type PKI (Export A : NetAddr) (Export V : Signable).

(* would expect that in this setting, an address is more or less a public key *)

Parameter PrivateKey : Set.
Parameter Signature : Set.
Parameter Signature_eqdec : forall (s1 s2 : Signature), {s1 = s2} + {s1 <> s2}.

Parameter key_map : Address -> PrivateKey.
Parameter verify : Value -> Signature -> Address -> bool.
Parameter sign : Value -> PrivateKey -> Signature.

(* symbolic security assumption *)

Axiom key_correct : forall v n s, 
  s = (sign v (key_map n)) <-> verify v s n.

Fact correct_sign_verify_ok v n :
  verify v (sign v (key_map n)) n.
Proof. now rewrite <- key_correct. Qed.

End PKI.

Module Type ThresholdSignatureScheme (Export A : NetAddr) (Export V : Signable).

Parameter thres : nat.

Parameter LightPrivateKey : Set.
Parameter LightSignature : Set.
Parameter LightSignature_eqdec : forall (ls1 ls2 : LightSignature), {ls1 = ls2} + {ls1 <> ls2}.
Parameter CombinedSignature : Set.
Parameter CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.

Parameter lightkey_map : Address -> LightPrivateKey.
(* TODO if for threshold signature scheme there will be a separate public key, 
    then we can only view Address as "the abstraction of publicly available information about a node"
    rather than "a public key (in PKI infrastructure)" *)
Parameter light_verify : Value -> LightSignature -> Address -> bool.
Parameter light_sign : Value -> LightPrivateKey -> LightSignature.
(* use dependent type to restrict the number of light signatures *)
(* Parameter lightsig_combine : Vector.t LightSignature (N - t0) -> CombinedSignature. *)
(* TODO using dependent type may incur difficulty in the protocol, so use a total function at first 
  if the number of light certificates is not (N-t0), then simply return some garbage
  (guaranteed by "combine_correct" below) *)
(*
(* it might also be good to know who signed these shared signatures, 
    without which we may be unable to implement the TSS
    by using the original PKI infrastructure; 
  also, theoretically we should be allowed to know the signers? *)
Parameter lightsig_combine : list (Address * LightSignature) -> CombinedSignature.

(* or, we can bake the information of sender into LightSignature *)
(* or, we can make the information of sender optional *)
(* FIXME: read some real-world code of TSS to make decision *)
*)
Parameter lightsig_combine : list LightSignature -> CombinedSignature.
Parameter combined_verify : Value -> CombinedSignature -> bool.

(* symbolic security assumption *)

Axiom lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.

Axiom combine_correct : forall v cs, 
  (exists ns : list Address, 
    NoDup ns /\ length ns = N - thres /\
    cs = lightsig_combine (map (fun n => light_sign v (lightkey_map n)) ns)) 
  <-> combined_verify v cs.

Fact correct_sign_verify_ok_light v n :
  light_verify v (light_sign v (lightkey_map n)) n.
Proof. now rewrite <- lightkey_correct. Qed.

End ThresholdSignatureScheme. 

(*
Module SimpleTSS (A : NetAddr) (V : Signable) (P : PKI A V).

(* use PKI to emulate TSS *)

Import A V P.

(* in this case, need to include the information of senders somewhere, 
    otherwise cannot use the original verify function *)

Definition LightPrivateKey := PrivateKey.
Definition LightSignature := (Address * Signature)%type.
Definition LightSignature_eqdec := prod_eq_dec Address_eqdec Signature_eqdec.

Definition CombinedSignature := list LightSignature. 
Definition CombinedSignature_eqdec : forall (cs1 cs2 : CombinedSignature), {cs1 = cs2} + {cs1 <> cs2}.
  intros.
  apply list_eq_dec, LightSignature_eqdec.
Defined.

Definition lightkey_map := key_map.
Definition light_verify v lsig n := 
  if Address_eqdec n (fst lsig) then verify v (snd lsig) n else false.
Definition light_sign v pk := (* ! *).
(*
(* TODO where to add the guard checking? *)
Definition lightsig_combine : list (Address * LightSignature) -> CombinedSignature := id.
Definition combined_verify (v : Value) (cs : CombinedSignature) :=
  forallb (fun '(n, lsig) => light_verify v lsig n) cs.

Lemma lightkey_correct : forall v n ls, 
  ls = (light_sign v (lightkey_map n)) <-> light_verify v ls n.
Proof key_correct.

Lemma combine_correct : forall v cs, 
  (exists ns : list Address, 
    NoDup ns /\ length ns = N - t0 /\
    cs = lightsig_combine (map (fun n => (n, light_sign v (lightkey_map n))) ns)) 
  <-> combined_verify v cs.
Proof.
*)

End SimpleTSS. 
*)

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
