From Coq Require Import List Bool Lia ssrbool ListSet.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts.

Module ACInvariant 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns).

Import A T AC Ns ACN.

(* this is somewhat "pure" property (not related to psent) *)
Record node_coh (st : State) : Prop := mkNodeCoh {
  inv_set_size: 
    length st.(from_set) = length st.(collected_lightsigs) /\
    length st.(from_set) = length st.(collected_sigs);
  inv_conf_correct:
    if st.(conf)
    then length st.(from_set) = N - t0
    else length st.(from_set) < N - t0;
  inv_from_nodup: NoDup st.(from_set);
  (* "NoDup nsigs" and "N - t0 <= (length nsigs)" should also hold 
    even if the certificate is sent by a Byzantine node *)
  inv_rlcerts: forall v cs, In (v, cs) st.(received_lightcerts) -> 
    combined_verify v cs;
  inv_rcerts_mixin: forall v nsigs, In (v, nsigs) st.(received_certs) -> 
    certificate_valid v nsigs /\
    (NoDup nsigs) /\ 
    N - t0 <= (length nsigs);
  (* mixin of before and after submission *)
  inv_submit_mixin: 
    match st.(submitted_value) with
    | Some v => 
      v = value_bft st.(id) /\
      light_signatures_valid v (zip_from_lsigs st) /\
      certificate_valid v (zip_from_sigs st)
    | None => st.(from_set) = nil
    end;
  inv_buffer_mixin: (st.(submitted_value) -> st.(msg_buffer) = nil) /\
    Forall (fun nmsg => valid_node (fst nmsg) /\
      (match snd nmsg with SubmitMsg _ _ _ => True | _ => False end)) st.(msg_buffer)
}.

Record node_invariant (psent : PacketSoup) (st : State) : Prop := mkNodeInv {
  inv_nsigs_correct: 
    match st.(submitted_value) with
    | Some v => forall n lsig sig, 
      In (n, lsig, sig) (zip_from_lsigs_sigs st) ->
        In (mkP n st.(id) (SubmitMsg v lsig sig) true) psent
    | None => True
    end;
  inv_rlcerts_correct: forall lc,
    In lc st.(received_lightcerts) ->
      exists src, In (mkP src st.(id) (LightConfirmMsg lc) true) psent;
  inv_rcerts_correct: forall c,
    In c st.(received_certs) ->
      exists src, In (mkP src st.(id) (ConfirmMsg c) true) psent;
  (* there must be some packets sent on some condition 
      (or, packets cannot disappear from the packet soup for no reason) *)
  inv_submitted_broadcast: 
    match st.(submitted_value) with
    | Some v => forall n, valid_node n -> 
      exists used, In (mkP st.(id) n 
        (SubmitMsg v (light_sign v (lightkey_map st.(id))) (sign v (key_map st.(id)))) 
        used) psent
    | None => True
    end;
  inv_conf_lightconfmsg: 
    match st.(submitted_value) with
    | Some v => st.(conf) -> forall n, valid_node n -> 
      exists used, In (mkP st.(id) n (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) used) psent
    | None => True
    end;
  (* have to guarantee that the messages in the buffer are already delivered *)
  inv_buffer_received: 
    Forall (fun nmsg => In (mkP (fst nmsg) st.(id) (snd nmsg) true) psent) st.(msg_buffer);
  inv_node_coh: node_coh st
}.

Fact valid_cert_valid_sig v nsigs
  (Hcert_valid : certificate_valid v nsigs) 
  n sig (Hin : In (n, sig) nsigs) : sig = sign v (key_map n).
Proof.
  unfold certificate_valid in Hcert_valid.
  rewrite -> Forall_forall in Hcert_valid.
  now apply Hcert_valid, proj2, key_correct in Hin.
Qed. 

Fact valid_cert_sender_in v nsigs
  (Hcert_valid : certificate_valid v nsigs) 
  n (Hin : In n (map fst nsigs)) : In (n, sign v (key_map n)) nsigs.
Proof.
  apply in_map_iff in Hin.
  destruct Hin as ((n', s) & Heq & ?).
  simpl in Heq.
  subst n'.
  pose proof H as H'.
  eapply valid_cert_valid_sig in H; eauto.
  now subst s.
Qed.

Fact valid_cert_nodup_implies_sender_nodup v nsigs
  (Hcert_valid : certificate_valid v nsigs) 
  (Hcert_nodup : NoDup nsigs) : NoDup (map fst nsigs).
Proof.
  clear -Hcert_nodup Hcert_valid.
  induction nsigs as [ | (n, sig) nsigs IH ].
  - constructor.
  - inversion_clear Hcert_nodup as [ | ? ? Hnotin Hcert_nodup' ].
    apply Forall_cons_iff in Hcert_valid.
    simpl in Hcert_valid.
    destruct Hcert_valid as ((Hnvalid & Hveri) & Hcert_valid).
    rewrite <- key_correct in Hveri.
    subst sig.
    constructor.
    + intros Hin.
      now eapply valid_cert_sender_in in Hin; eauto.
    + apply IH; intuition.
Qed.

(* NoDup (snd (cert st)) is enough to show NoDup senders *)
(*
Fact node_invariant_implies_inv_cert_sender_nodup st psent 
  (Hnodeinv : node_invariant psent st) : NoDup (map fst (snd (cert st))).
Proof.
  destruct Hnodeinv as (Hnodeinv_nsigs, _, _, (_, Hcert_nodup, _, Hcert_valid)).
  destruct (cert st) as (v, nsigs).
  eapply valid_cert_nodup_implies_sender_nodup; eauto.
Qed.
*)
(* make two views of invariants *)

Definition _inv_submitmsg_correct stmap src v lsig sig : Prop := 
  is_byz src = false ->
    verify v sig src /\
    light_verify v lsig src /\
    Some v = (stmap src).(submitted_value).

Definition _inv_lightconfirmmsg_correct stmap psent_history src lc : Prop := 
  if is_byz src
    then lcert_correct_threshold psent_history lc
    else (stmap src).(conf) /\ Some (fst lc) = (stmap src).(submitted_value) /\
      snd lc = lightsig_combine (stmap src).(collected_lightsigs)
.

Definition _inv_confirmmsg_correct stmap psent_history src c : Prop := 
  if is_byz src
    then cert_correct psent_history c
    else (stmap src).(conf) /\ lightcert_conflict_check (stmap src).(received_lightcerts) (* this is new *)
      /\ Some (fst c) = (stmap src).(submitted_value) /\
      snd c = zip_from_sigs (stmap src)
.

Definition _inv_submitmsg_receive (stmap : StateMap) src dst v lsig sig (consumed : bool) : Prop := 
  consumed -> is_byz dst = false ->
  match (stmap dst).(submitted_value) with
  | None => In (src, SubmitMsg v lsig sig) (stmap dst).(msg_buffer)
  | Some ov => 
    (* the length condition may be more natural, but it would be hard to reason about 
      without invariant 1; so replace it with the condition on conf *)
    (* length (stmap dst).(from_set) < N - t0 -> *)
    (stmap dst).(conf) = false ->
    v = ov -> verify v sig src -> light_verify v lsig src ->
      In src (stmap dst).(from_set) (* ths should be enough *)
  end
.

(* by rule, a valid light/full certificate cannot be rejected by an honest node for no reason *)
Definition _inv_lightconfirmmsg_receive (stmap : StateMap) dst v cs (consumed : bool) : Prop := 
  consumed -> is_byz dst = false ->
  combined_verify v cs -> In (v, cs) (received_lightcerts (stmap dst))
.

Definition _inv_confirmmsg_receive (stmap : StateMap) dst v nsigs (consumed : bool) : Prop := 
  consumed -> is_byz dst = false ->
  certificate_valid v nsigs -> NoDup nsigs -> (N - t0 <= (length nsigs)) ->
    In (v, nsigs) (received_certs (stmap dst))
.

Definition _inv_msg_correct_2 stmap p : Prop :=
  let: mkP src dst msg b := p in
  match msg with
  | LightConfirmMsg (v, cs) => _inv_lightconfirmmsg_receive stmap dst v cs b
  | ConfirmMsg (v, nsigs) => _inv_confirmmsg_receive stmap dst v nsigs b
  | SubmitMsg v lsig sig => _inv_submitmsg_receive stmap src dst v lsig sig b
  end.

Global Arguments _inv_submitmsg_receive _ _ _ _ _ _ _/.
Global Arguments _inv_lightconfirmmsg_receive _ _ _ _ _/.
Global Arguments _inv_confirmmsg_receive _ _ _ _ _/.
Global Arguments _inv_msg_correct_2 _ _/.

(* additional invariant which is used to prove the eventual accountability *)

Record invariant_2 (w : World) : Prop := mkInv2 {
  _ : Forall (_inv_msg_correct_2 (localState w)) (sentMsgs w)
}.

Definition _inv_msg_correct stmap psent_history p : Prop :=
  let: mkP src dst msg _ := p in
  match msg with
  | SubmitMsg v lsig sig => _inv_submitmsg_correct stmap src v lsig sig
  | LightConfirmMsg lc => _inv_lightconfirmmsg_correct stmap psent_history src lc
  | ConfirmMsg c => _inv_confirmmsg_correct stmap psent_history src c
  end.

Global Arguments _inv_submitmsg_correct _ _ _ _ _/.
Global Arguments _inv_lightconfirmmsg_correct _ _ _ _/.
Global Arguments _inv_confirmmsg_correct _ _ _ _/.
Global Arguments _inv_msg_correct _ _ _/.

Record _psent_invariant (stmap : StateMap) (psent psent_history : PacketSoup) : Prop := mkPsentInv {
  inv_submitmsg_correct: forall src dst v lsig sig consumed, 
    In (mkP src dst (SubmitMsg v lsig sig) consumed) psent ->
    _inv_submitmsg_correct stmap src v lsig sig;
  inv_lightconfirmmsg_correct: forall src dst lc consumed, 
    In (mkP src dst (LightConfirmMsg lc) consumed) psent ->
    _inv_lightconfirmmsg_correct stmap psent_history src lc;
  inv_confirmmsg_correct: forall src dst c consumed, 
    In (mkP src dst (ConfirmMsg c) consumed) psent ->
    _inv_confirmmsg_correct stmap psent_history src c
}.

Definition psent_invariant stmap psent := _psent_invariant stmap psent psent.

Lemma psent_invariant_viewchange stmap psent psent_history :
  _psent_invariant stmap psent psent_history <->
  (forall p, In p psent -> _inv_msg_correct stmap psent_history p).
Proof.
  split; intros H.
  - intros p Hin.
    destruct p as (src, dst, msg, used).
    simpl.
    destruct msg as [ v ls s | lc | c ].
    all: eapply H; eauto.
  - constructor.
    + intros src dst v lsig sig b Hin_psent H_src_nonbyz.
      specialize (H (mkP src dst (SubmitMsg v lsig sig) b) Hin_psent).
      now apply H.
    + intros src dst lc b Hin_psent.
      specialize (H (mkP src dst (LightConfirmMsg lc) b) Hin_psent).
      now apply H.
    + intros src dst c b Hin_psent.
      specialize (H (mkP src dst (ConfirmMsg c) b) Hin_psent).
      now apply H.
Qed.

(* Global Arguments _psent_invariant _ _ _/.
Global Arguments psent_invariant _ _/. *)

Record invariant (w : World) : Prop := mkInv {
  coh: Coh w;
  node_inv: forall n, is_byz n = false -> 
    holds n w (node_invariant (sentMsgs w));
    (* node_invariant (localState w n) (sentMsgs w); *)
  psent_inv: psent_invariant (localState w) (sentMsgs w)
}.

Section Main_Proof.

(* TODO some of these tactic notations are redundant; consider simplification *)

Tactic Notation "simpl_pkt" :=
  simpl dst in *; simpl src in *; simpl msg in *; simpl consumed in *.

Tactic Notation "simpl_state" :=
  simpl id in *; simpl conf in *; simpl submitted_value in *; simpl from_set in *;
  simpl collected_lightsigs in *; simpl collected_sigs in *; simpl received_lightcerts in *; 
  simpl received_certs in *; simpl msg_buffer in *.

Tactic Notation "destruct_procMsg" "as_" ident(st') ident(ms) "eqn_" ident(E) :=
  match goal with 
  | H : (let: (_, _) := procMsg ?st ?nsrc ?msg in _) |- _ => 
    destruct (procMsg st nsrc msg) as (st', ms) eqn:E
  end.

Tactic Notation "destruct_procInt" "as_" ident(st') ident(ms) "eqn_" ident(E) :=
  match goal with 
  | H : (let: (_, _) := procInt ?st ?t in _) |- _ => 
    destruct (procInt st t) as (st', ms) eqn:E
  end.

(* destruct and unify at the same time *)

Tactic Notation "destruct_localState" ident(w) ident(n) 
  "as_" ident(conf) ident(ov) ident(from) ident(lsigs) ident(sigs) 
  ident(rlcerts) ident(rcerts) ident(buffer) "eqn_" ident(E) :=
  let n' := fresh n in
  let Htmp := fresh "Htmp" in
  match goal with 
  | H : Coh w |- _ =>
    destruct (localState w n) as (n', conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer) eqn:E; 
    assert (n' = n) as Htmp by
      (now rewrite <- (id_coh _ H n), E); 
    subst n'
  end.

Tactic Notation "injection_pair" hyp(H) :=
  match type of H with
  (?a, ?b) = (?c, ?d) => is_var c; is_var d; injection H as <-; try subst c; try subst d
  end.

Tactic Notation "rewrite_w_expand" ident(w) "in_" hyp(H) :=
  replace w with (mkW (localState w) (sentMsgs w)) in H by (now destruct w).

Tactic Notation "eqsolve" := solve [ intuition congruence | intuition discriminate ].

Create HintDb ABCinv.

Tactic Notation "basic_solver" := auto with ABCinv; try eqsolve; try lia.

Local Hint Resolve correct_sign_verify_ok : ABCinv.
Local Hint Resolve correct_sign_verify_ok_light : ABCinv.

Fact incl_appl_simple [A] (l1 l2 : list A) : incl l1 (l1 ++ l2).
Proof. now apply incl_appl. Qed.

Fact incl_appr_simple [A] (l1 l2 : list A) : incl l1 (l2 ++ l1).
Proof. now apply incl_appr. Qed.

Local Hint Resolve incl_appl_simple : ABCinv.
Local Hint Resolve incl_appr_simple : ABCinv.

Inductive psent_mnt : bool -> PacketSoup -> PacketSoup -> Prop :=
  | PsentEq (psent : PacketSoup) : psent_mnt false psent psent
  | PsentEq' (p : Packet) (psent : PacketSoup) 
    (Hin : In p psent) : psent_mnt false psent (consume p psent)
  (* since we do not count, mutual in is enough (rather than permutation) *)
  (* TODO replace PsentEq with this more general version? *)
  | PsentEq'' (psent psent' : PacketSoup) 
    (Hinin : forall p, In p psent <-> In p psent') : psent_mnt false psent psent'
  | PsentLe (psent1 psent2 psent' : PacketSoup) 
    (Hpsenteq : psent_mnt false psent1 psent2)
    (Hsubset : incl psent2 psent') : 
      psent_mnt true psent1 psent'.

Definition node_submit (st : State) v :=
  let: Node n conf _ from lsigs sigs rlcerts rcerts _ := st in
  Node n conf (Some v) from lsigs sigs rlcerts rcerts nil.

Definition node_upd_collect_submit (st : State) conf from lsigs sigs :=
  let: Node n _ ov _ _ _ rlcerts rcerts buffer := st in
  Node n conf ov from lsigs sigs rlcerts rcerts buffer.

Definition node_upd_rlcerts (st : State) rlcerts :=
  let: Node n conf ov from lsigs sigs _ rcerts buffer := st in
  Node n conf ov from lsigs sigs rlcerts rcerts buffer.

Definition node_upd_rcerts (st : State) rcerts :=
  let: Node n conf ov from lsigs sigs rlcerts _ buffer := st in
  Node n conf ov from lsigs sigs rlcerts rcerts buffer.

(* since each time there is only one field being updated, no need to make 
    recursive assumptions *)

Inductive state_mnt : bool -> State -> State -> Prop :=
  | StateEq (st : State) : state_mnt false st st
  | StateSubmitMnt (st : State) v_sub (Hnewsub : st.(submitted_value) = None) : 
    state_mnt true st (node_submit st v_sub)
  (*
  | StateCertMnt (st : State) (bundled_content : list (Address * LightSignature * Signature))
    (Hmnt : match st.(submitted_value) with None => True
      | Some _ => 
        if st.(conf) 
        then bundled_content = zip_from_lsigs_sigs st
        else incl (zip_from_lsigs_sigs st) bundled_content
      end) :
    state_mnt true st
    (* this is too ... *)
    (let: (tmp, sigs) := List.split bundled_content in
    let: (from, lsigs) := List.split tmp in 
    node_upd_collect_submit st 
      (st.(conf) || (Nat.leb (N - t0) (length bundled_content))) 
      from lsigs sigs)
  *)
  | StateCertMnt (st : State) from lsigs sigs
    (Hlen : length from = length lsigs /\ length from = length sigs)
    (Hmnt : match st.(submitted_value) with None => True
      | Some _ => 
        if st.(conf) 
        then from = st.(from_set) /\ lsigs = st.(collected_lightsigs) /\
          sigs = st.(collected_sigs)
        else incl st.(from_set) from /\ incl st.(collected_lightsigs) lsigs /\
          incl st.(collected_sigs) sigs
      end) :
    state_mnt true st
    (* this is too ... *)
    (node_upd_collect_submit st 
      (st.(conf) || (Nat.leb (N - t0) (length from))) 
      from lsigs sigs)
  | StateRLCertsMnt (st : State) rlcerts
    (Hmnt : incl st.(received_lightcerts) rlcerts) : 
    state_mnt true st (node_upd_rlcerts st rlcerts)
  | StateRCertsMnt (st : State) rcerts
    (Hmnt : incl st.(received_certs) rcerts) : 
    state_mnt true st (node_upd_rcerts st rcerts).

Local Hint Constructors state_mnt : ABCinv.
Local Hint Constructors psent_mnt : ABCinv.

Local Hint Constructors NoDup : ABCinv.

Lemma In_consume psent p (Hin : In p psent)
  src dst msg used (Hin' : In (mkP src dst msg used) psent) :
  In (mkP src dst msg (if (Packet_eqdec (mkP src dst msg used) p)
  then true else used)) (consume p psent).
Proof.
  simpl.
  destruct (Packet_eqdec (mkP src dst msg used) p) as [ <- | Hneq ].
  - now left.
  - right.
    now apply in_in_remove.
Qed.

Corollary In_consume' psent p (Hin : In p psent)
  src dst msg (Hin' : In (mkP src dst msg true) psent) :
  In (mkP src dst msg true) (consume p psent).
Proof.
  apply In_consume with (p:=p) in Hin'.
  2: assumption.
  destruct (Packet_eqdec (mkP src dst msg true) p); auto.
Qed.

Corollary In_psent_mnt b psent psent' (Hpmnt : psent_mnt b psent psent') : 
  forall src dst msg used (Hin : In (mkP src dst msg used) psent),
  exists used', (if used then used' = true else True) /\ In (mkP src dst msg used') psent'.
Proof.
  induction Hpmnt; intros.
  - exists used.
    split.
    + now destruct used.
    + assumption. 
  - apply In_consume with (p:=p) in Hin0.
    2: assumption.
    destruct used.
    + exists true.
      match goal with H : context[Packet_eqdec ?p' p] |- _ => destruct (Packet_eqdec p' p); eauto end.
    + eauto. 
  - exists used.
    rewrite <- Hinin.
    split.
    + now destruct used.
    + assumption. 
  - eapply IHHpmnt in Hin.
    firstorder.
Qed.

Corollary In_psent_mnt' b psent psent' (Hpmnt : psent_mnt b psent psent') 
  src dst msg (Hin : In (mkP src dst msg true) psent) :
  In (mkP src dst msg true) psent'.
Proof.
  eapply In_psent_mnt in Hin.
  2: apply Hpmnt.
  now destruct Hin as (? & -> & ?).
Qed.

Lemma In_consume_converse psent p (Hin : In p psent)
  src dst msg used (Hin' : In (mkP src dst msg used) (consume p psent)) :
  exists used', In (mkP src dst msg used') psent.
Proof.
  simpl in Hin'.
  destruct Hin' as [ Hin' | Hin' ].
  - destruct p.
    simpl in Hin'.
    injection Hin' as <-.
    subst.
    eauto.
  - exists used.
    eapply in_remove; eauto.
Qed.

Lemma Coh_psent_irrelevant stmap psent psent' (Hcoh : Coh (mkW stmap psent)) :
  Coh (mkW stmap psent').
Proof. destruct Hcoh. constructor; auto. Qed.

(* actually funext can be used here, but at first try avoiding it *)
Lemma upd_same_pointwise_eq stmap (n m : Address) : 
  stmap m = upd n (stmap n) stmap m.
Proof.
  unfold upd.
  destruct (Address_eqdec n m) as [ <- | Hneq ]; auto.
Qed.

Fact stmap_pointwise_eq_preserve_Coh stmap stmap' psent 
  (Hpeq : forall x, stmap x = stmap' x)
  (Hcoh : Coh (mkW stmap psent)) : Coh (mkW stmap' psent).
Proof.
  destruct Hcoh as (Hcoh1, Hcoh2).
  unfold holds in Hcoh1, Hcoh2.
  simpl in Hcoh1, Hcoh2.
  setoid_rewrite -> Hpeq in Hcoh1.
  setoid_rewrite -> Hpeq in Hcoh2.
  now constructor.
Qed.

Lemma upd_id_intact_preserve_Coh stmap n st' psent 
  (Hnvalid : valid_node n)
  (Hsmnt : (stmap n).(id) = st'.(id))
  (Hcoh : Coh (mkW stmap psent)) :
  Coh (mkW (upd n st' stmap) psent).
Proof.
  constructor.
  - intros n0.
    unfold holds, upd.
    simpl. 
    destruct (Address_eqdec n n0) as [ -> | Hneq ].
    1: rewrite <- Hsmnt.
    all: apply Hcoh.
  - intros n0 Hninvalid.
    unfold holds, upd. 
    simpl.
    destruct (Address_eqdec n n0); try eqsolve.
    now apply Hcoh in Hninvalid.
Qed.

Corollary state_mnt_preserve_Coh ob stmap n st' psent 
  (Hnvalid : valid_node n)
  (Hsmnt : state_mnt ob (stmap n) st')
  (Hcoh : Coh (mkW stmap psent)) :
  Coh (mkW (upd n st' stmap) psent).
Proof.
  apply upd_id_intact_preserve_Coh; try assumption.
  inversion Hsmnt; subst.
  all: destruct (stmap n) eqn:E; try reflexivity.
Qed.

Lemma psent_mnt_preserve_lcert_correct b psent psent'
  (Hpmnt : psent_mnt b psent psent')
  lc (Hcc : lcert_correct psent lc) : lcert_correct psent' lc.
Proof.
  destruct lc as (v, cs).
  revert v cs Hcc. 
  induction Hpmnt; subst; intros.
  - assumption.
  - hnf in Hcc |- *.
    intros Hcv lsigs -> n lsig Hin' H_n_nonbyz Hveri.
    specialize (Hcc Hcv _ eq_refl _ _ Hin' H_n_nonbyz Hveri).
    hnf in Hcc |- *.
    destruct Hcc as (dst & used & sig & Hwitness).
    apply In_consume with (p:=p) in Hwitness; eauto.
  - hnf in Hcc |- *.
    unfold lightsig_seen_in_history in Hcc |- *.
    setoid_rewrite <- Hinin.
    assumption.
  - apply IHHpmnt in Hcc.
    hnf in Hcc |- *.
    intros Hcv lsigs -> n lsig Hin' H_n_nonbyz Hveri.
    specialize (Hcc Hcv _ eq_refl _ _ Hin' H_n_nonbyz Hveri).
    hnf in Hcc |- *.
    destruct Hcc as (dst & used & sig & Hwitness).
    exists dst, used, sig.
    now apply Hsubset.
Qed.

Lemma psent_mnt_preserve_cert_correct b psent psent'
  (Hpmnt : psent_mnt b psent psent')
  c (Hcc : cert_correct psent c) : cert_correct psent' c.
Proof.
  destruct c as (v, nsigs).
  revert v nsigs Hcc. 
  induction Hpmnt; subst; intros.
  - assumption.
  - hnf in Hcc |- *.
    intros n sig Hin' H_n_nonbyz Hveri.
    specialize (Hcc _ _ Hin' H_n_nonbyz Hveri).
    hnf in Hcc |- *.
    destruct Hcc as (dst & used & lsig & Hwitness).
    apply In_consume with (p:=p) in Hwitness; eauto.
  - hnf in Hcc |- *.
    unfold sig_seen_in_history in Hcc |- *.
    setoid_rewrite <- Hinin.
    assumption.
  - apply IHHpmnt in Hcc.
    hnf in Hcc |- *.
    intros n sig Hin' H_n_nonbyz Hveri.
    specialize (Hcc _ _ Hin' H_n_nonbyz Hveri).
    hnf in Hcc |- *.
    destruct Hcc as (dst & used & lsig & Hwitness).
    apply Hsubset in Hwitness.
    now exists dst, used, lsig.
Qed.

Lemma psent_mnt_preserve_node_invariant b psent psent'
  (Hpmnt : psent_mnt b psent psent')
  st (Hnodeinv : node_invariant psent st) : node_invariant psent' st.
Proof.
  destruct st as (n, conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer).
  constructor; simpl_state.
  - destruct ov as [ v | ]; auto.
    intros n0 lsig sig Hin_nsig.
    eapply In_psent_mnt'; eauto.
    now apply Hnodeinv.
  - intros lc Hin_rlcerts.
    destruct Hnodeinv as (_, Hnodeinv, _, _, _, _, _).
    specialize (Hnodeinv lc Hin_rlcerts).
    simpl in Hnodeinv.
    destruct Hnodeinv as (src & H).
    exists src.
    eapply In_psent_mnt'; eauto.
  - intros c Hin_rcerts.
    destruct Hnodeinv as (_, _, Hnodeinv, _, _, _, _).
    specialize (Hnodeinv c Hin_rcerts).
    simpl in Hnodeinv.
    destruct Hnodeinv as (src & H).
    exists src.
    eapply In_psent_mnt'; eauto.
  - destruct ov as [ v | ]; auto.
    destruct Hnodeinv as (_, _, _, Hnodeinv, _, _, _).
    simpl_state.
    simpl in Hnodeinv.
    intros n0 Hn0valid.
    specialize (Hnodeinv _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - destruct ov as [ v | ]; auto.
    destruct Hnodeinv as (_, _, _, _, Hnodeinv, _, _).
    simpl_state.
    intros -> n0 Hn0valid.
    specialize (Hnodeinv eq_refl _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - destruct Hnodeinv as (_, _, _, _, _, Hnodeinv, _).
    rewrite -> Forall_forall in Hnodeinv |- *.
    intros.
    eapply In_psent_mnt', Hnodeinv; eauto.
  - apply Hnodeinv.
Qed.

Fact lightcert_conflict_check_incl rlcerts rlcerts' 
  (Hincl : incl rlcerts rlcerts') 
  (Hcheck : lightcert_conflict_check rlcerts) :
  lightcert_conflict_check rlcerts'.
Proof.
  apply lightcert_conflict_check_correct in Hcheck.
  apply lightcert_conflict_check_correct.
  destruct Hcheck as (v1 & v2 & cs1 & cs2 & Hvneq & Hin1 & Hin2).
  exists v1, v2, cs1, cs2.
  split; [ assumption | ].
  split; now apply Hincl.
Qed.

Lemma state_mnt_preserve_psent_invariant ob stmap n st'
  (Hsmnt : state_mnt ob (stmap n) st')
  stmap' (Hpeq : forall x, stmap' x = (upd n st' stmap) x)
  psent (Hpsentinv : psent_invariant stmap psent) : 
  psent_invariant stmap' psent.
Proof.
  constructor.
  - intros src dst v lsig sig b Hin_psent H_src_nonbyz.
    rewrite -> Hpeq.
    unfold upd.
    destruct (Address_eqdec n src) as [ -> | Hneq ].
    2: eapply Hpsentinv; eauto.
    inversion Hsmnt; subst.
    all: destruct (stmap src) as (?, ?, v0, ?, ?, ?, ?, ?, ?) eqn:E.
    all: simpl.
    1,3-5: replace v0 with (stmap src).(submitted_value); [ eapply Hpsentinv; eauto | now rewrite E ].
    (* this is only for the submit transition *)
    hnf in Hpsentinv.
    rewrite -> psent_invariant_viewchange in Hpsentinv.
    specialize (Hpsentinv _ Hin_psent).
    simpl in Hpsentinv, Hnewsub.
    subst v0.
    rewrite -> E in Hpsentinv.
    simpl in Hpsentinv.
    eqsolve.
  - intros src dst lc b Hin_psent.
    (* TODO exploit some symmetry of light certs and full certs? *)
    simpl.
    rewrite -> Hpeq.
    destruct Hpsentinv as (_, Hpsentinv, _).
    specialize (Hpsentinv src dst lc b Hin_psent).
    simpl in Hpsentinv.
    destruct (is_byz src) eqn:H_src_byz.
    1: assumption.
    unfold upd.
    destruct (Address_eqdec n src) as [ -> | Hneq ].
    2: eapply Hpsentinv; eauto.
    destruct (stmap src) as (?, conf0, v0, ?, ?, ?, ?, ?, ?) eqn:E.
    inversion Hsmnt; subst.
    all: simpl_state; try assumption.
    1: subst v0; eqsolve.
    destruct v0 as [ v0 | ]; try eqsolve.
    destruct conf0; eqsolve.
  - intros src dst c b Hin_psent.
    (* TODO exploit some symmetry of light certs and full certs? *)
    simpl.
    rewrite -> Hpeq.
    destruct Hpsentinv as (_, _, Hpsentinv).
    specialize (Hpsentinv src dst c b Hin_psent).
    simpl in Hpsentinv.
    destruct (is_byz src) eqn:H_src_byz.
    1: assumption.
    unfold upd.
    destruct (Address_eqdec n src) as [ -> | Hneq ].
    2: eapply Hpsentinv; eauto.
    destruct (stmap src) as (?, conf0, v0, ?, ?, ?, rlcerts0, ?, ?) eqn:E.
    inversion Hsmnt; subst.
    all: simpl_state; try assumption.
    all: destruct v0 as [ v0 | ]; try eqsolve.
    all: destruct conf0; try eqsolve.
    + unfold node_upd_collect_submit.
      simpl.
      eqsolve.
    + (* needs a small subset property *)
      pose proof (lightcert_conflict_check_incl _ _ Hmnt).
      intuition.
Qed.

Fact psent_equiv_preserve_psent_invariant stmap psent psent'
  (Hpmnt0 : psent_mnt false psent psent')
  (Hpsentinv : psent_invariant stmap psent) : 
  psent_invariant stmap psent'.
Proof.
  inversion Hpmnt0; subst.
  - assumption.
  - constructor.
    + intros src dst v lsig sig b Hin_psent H_src_nonbyz.
      apply In_consume_converse in Hin_psent.
      2: assumption.
      destruct Hin_psent.
      eapply Hpsentinv; eauto.
    + intros src dst lc b Hin_psent.
      simpl.
      apply In_consume_converse in Hin_psent.
      2: assumption.
      destruct Hin_psent.
      match goal with 
      |- if ?cond then _ else ?g => cut (if cond then lcert_correct_threshold psent lc else g)
      end.
      * destruct (is_byz src).
        2: auto.
        intros HH Hth.
        eapply psent_mnt_preserve_lcert_correct; eauto.
      * eapply Hpsentinv; eauto.
    + intros src dst c b Hin_psent.
      simpl.
      apply In_consume_converse in Hin_psent.
      2: assumption.
      destruct Hin_psent.
      match goal with 
      |- if ?cond then _ else ?g => cut (if cond then cert_correct psent c else g)
      end.
      * destruct (is_byz src).
        2: auto.
        eapply psent_mnt_preserve_cert_correct; eauto.
      * eapply Hpsentinv; eauto.
  - constructor.
    + setoid_rewrite <- Hinin.
      apply Hpsentinv.
    + unfold _inv_lightconfirmmsg_correct, lcert_correct_threshold, lcert_correct, lightsig_seen_in_history.
      setoid_rewrite <- Hinin.
      intros src dst lc b Hin_psent.
      destruct Hpsentinv as (_, Hpsentinv, _).
      specialize (Hpsentinv src dst lc b Hin_psent).
      simpl in Hpsentinv.
      destruct lc as (v, cs), (is_byz src).
      * setoid_rewrite <- Hinin.
        apply Hpsentinv.
      * apply Hpsentinv.
    + unfold _inv_confirmmsg_correct, cert_correct, sig_seen_in_history.
      setoid_rewrite <- Hinin.
      intros src dst c b Hin_psent.
      destruct Hpsentinv as (_, _, Hpsentinv).
      specialize (Hpsentinv src dst c b Hin_psent).
      simpl in Hpsentinv.
      destruct c as (v, nsigs), (is_byz src).
      * setoid_rewrite <- Hinin.
        apply Hpsentinv.
      * apply Hpsentinv.
Qed.

Lemma psent_history_mnt_preserve__inv_msg_correct 
  b psent psent' (Hpmnt : psent_mnt b psent psent') 
  stmap p (Hpsentinv : _inv_msg_correct stmap psent p) :
  _inv_msg_correct stmap psent' p.
Proof.
  simpl in Hpsentinv |- *.
  destruct p as (src, ?, [ | | ], ?).
  1: assumption.
  all: destruct (is_byz src); try assumption.
  - intros Hle. eapply psent_mnt_preserve_lcert_correct; eauto.
  - eapply psent_mnt_preserve_cert_correct; eauto.
Qed.

(* TODO avoiding funext can make things trouble like this (need stmap' as intermediate) ...
    we can always remove pointwise eq hyp as long as we have a base one to transform between them
*)

(* Hstcond, Hpsentcond: sufficient conditions for proving new properties from old state *)

Corollary inv_preserve_10 n stmap st'
  (Hnvalid : valid_node n)
  (Hsmnt : state_mnt true (stmap n) st')
  psent 
  (Hstcond : node_invariant psent st')
  (Hinv : invariant (mkW stmap psent)) : 
  invariant (mkW (upd n st' stmap) psent).
Proof.
  destruct Hinv as (Hcoh, Hnodeinv, Hpsentinv).
  constructor.
  - eapply state_mnt_preserve_Coh; eauto.
  - intros n0 H_n0_nonbyz.
    unfold holds, upd. 
    simpl.
    destruct (Address_eqdec n n0) as [ <- | ].
    1: assumption.
    now apply Hnodeinv.
  - eapply state_mnt_preserve_psent_invariant; eauto.
Qed.

Corollary psent_invariant_by_extend stmap psent psent'
  (Hpsentcond : exists psent_, psent_mnt false psent psent_ /\
    incl psent_ psent' /\
    (forall p, In p psent' -> ~ In p psent_ -> _inv_msg_correct stmap psent p))
  (Hpsentinv : psent_invariant stmap psent) : 
  psent_invariant stmap psent'.
Proof.
  apply psent_invariant_viewchange.
  intros p0 Hin_psent'.
  destruct Hpsentcond as (psent_ & Hpmnt0 & Hsubset & Hpsentcond).
  (* change goal twice: here and after *)
  eapply psent_history_mnt_preserve__inv_msg_correct with (psent:=psent_).
  1:{ 
    eapply PsentLe.
    - apply PsentEq.
    - assumption.
  }
  eapply psent_equiv_preserve_psent_invariant in Hpsentinv.
  2: apply Hpmnt0.
  unfold psent_invariant in Hpsentinv.
  rewrite -> psent_invariant_viewchange in Hpsentinv.
  destruct (In_dec Packet_eqdec p0 psent_) as [ Hin_pent_ | Hin_pent_ ].
  + now apply Hpsentinv.
  + eapply psent_history_mnt_preserve__inv_msg_correct with (psent:=psent).
    1: eauto.
    now apply Hpsentcond.
Qed.

Corollary inv_preserve_01 stmap stmap' psent psent'
  (Hpeq : forall x, stmap x = stmap' x)
  (Hpsentcond : exists psent_, psent_mnt false psent psent_ /\
    incl psent_ psent' /\
    (forall p, In p psent' -> ~ In p psent_ -> _inv_msg_correct stmap psent p))
  (Hinv : invariant (mkW stmap psent)) : 
  invariant (mkW stmap' psent').
Proof.
  constructor.
  - apply Coh_psent_irrelevant with (psent:=psent).
    eapply stmap_pointwise_eq_preserve_Coh.
    + apply Hpeq.
    + apply Hinv.
  - intros n H_n_nonbyz.
    destruct Hpsentcond as (psent_ & Hpmnt0 & Hsubset & _).
    eapply psent_mnt_preserve_node_invariant.
    1: eapply PsentLe; eauto.
    simpl.
    rewrite <- Hpeq.
    now apply Hinv.
  - simpl.
    (* a trick *)
    eapply state_mnt_preserve_psent_invariant with (n:=Address_inhabitant) (stmap:=stmap).
    1: apply StateEq.
    1: intros; now rewrite <- Hpeq, <- upd_same_pointwise_eq.
    eapply psent_invariant_by_extend; eauto.
    now apply Hinv.
Qed. 

Corollary inv_preserve_00 stmap stmap' psent psent'
  (Hpeq : forall x, stmap x = stmap' x)
  (Hpmnt0 : psent_mnt false psent psent')
  (Hinv : invariant (mkW stmap psent)) : 
  invariant (mkW stmap' psent').
Proof.
  eapply inv_preserve_01; eauto.
  exists psent'.
  split.
  1: assumption.
  split.
  1: unfold incl; auto.
  eqsolve.
Qed.

Corollary inv_preserve_stmap_pointwise_eq stmap stmap' psent
  (Hpeq : forall x, stmap x = stmap' x)
  (Hinv : invariant (mkW stmap psent)) : 
  invariant (mkW stmap' psent).
Proof. eapply inv_preserve_00; eauto. apply PsentEq. Qed.

Lemma inv_init : invariant initWorld.
Proof with basic_solver.
  constructor.
  - constructor.
    all: intros; unfold holds; simpl...
  - intros n H_n_nonbyz.
    unfold holds.
    simpl.
    unfold initState.
    constructor; simpl...
    pose proof t0_lt_N.
    constructor; simpl; auto; try lia; try constructor.
  - constructor; simpl...
Qed.

Lemma inv_deliver_step w w' p :
  invariant w -> system_step (Deliver p) w w' -> invariant w'.
Proof with basic_solver.
  intros H Hstep. 
  pose proof (coh _ H) as Hcoh.
  inversion Hstep as [ 
    | p' Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | | | | ]; try discriminate.
  injection Hq as <-.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  destruct_procMsg as_ st' ms eqn_ Epm.
  destruct_localState w dst as_ conf_dst ov_dst from_dst lsigs_dst sigs_dst 
    rlcerts_dst rcerts_dst buffer_dst eqn_ Edst.
  subst w'.
  (* TODO may do case analysis in a smarter way. there is still some repetition *)
  destruct msg as [ v ls s | lc | c ].
  - simpl in Epm.
    (* prepare *)
    pose proof H as Hconf.
    destruct Hconf as (_, Hconf, _).
    specialize (Hconf dst Hnonbyz).
    unfold holds in Hconf.
    rewrite -> Edst in Hconf.
    destruct Hconf as (Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, Hbuffer_recv,
      ((Hsize1 & Hsize2), Hconf, Hfrom_nodup, Hrlcerts, Hrcerts, Hcoll_valid, Hbuffer)).
    simpl in Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, Hbuffer_recv, 
      Hsize1, Hsize2, Hconf, Hfrom_nodup, Hrlcerts, Hrcerts, Hcoll_valid, Hbuffer.
    destruct (match ov_dst with
      | Some v_dst => if Value_eqdec v v_dst 
        then (if verify v s src 
              then (if light_verify v ls src
                    then (if (negb conf_dst) 
                          then (negb (is_left (In_dec Address_eqdec src from_dst))) 
                          else false) 
                    else false)
              else false)
        else false
      | None => false end) eqn:Edecide.
    2: destruct ov_dst as [ v_dst | ].
    + destruct ov_dst as [ v_dst | ] eqn:Eov_dst...
      destruct (Value_eqdec v v_dst) as [ <- | ], 
        (verify v s src) eqn:Everi, 
        (light_verify v ls src) eqn:Elveri, 
        conf_dst eqn:Econf, 
        (In_dec Address_eqdec src from_dst) as [ Ensig_in | Ensig_in ]...
      unfold zip_from_lsigs, zip_from_sigs in Hcoll_valid.
      simpl in Epm, Hcoll_valid.
      destruct Hcoll_valid as (Ev & Hlsigs_valid & Hsigs_valid).
      inversion Hconf as [ Hle | thr Hle Ethr ].
      * (* the only 11 case in the proof *)
        (* now cannot prove by applying 01 then 10 due to interrelation *)
        rewrite <- Hle, -> PeanoNat.Nat.leb_refl in Epm.
        injection_pair Epm.
        (* still can get state mnt, which simplifies some proof *)
        pose proof (StateCertMnt (localState w dst) (src :: from_dst) (ls :: lsigs_dst) (s :: sigs_dst)) as Hsmnt.
        simpl in Hsmnt.
        specialize (Hsmnt (conj (f_equal S Hsize1) (f_equal S Hsize2))). 
        rewrite -> Edst, <- Hle in Hsmnt.
        unfold incl in Hsmnt.
        simpl in Hsmnt.
        rewrite -> PeanoNat.Nat.leb_refl in Hsmnt.
        specialize (Hsmnt (conj (fun _ p => or_intror p) (conj (fun _ p => or_intror p) (fun _ p => or_intror p)))).
        constructor.
        --eapply state_mnt_preserve_Coh; eauto.
          ++rewrite -> Edst.
            now apply Hsmnt.
          ++eapply Coh_psent_irrelevant.
            rewrite_w_expand w in_ H.
            now apply H.
        --intros n H_n_nonbyz.
          unfold holds, upd.
          cbn delta -[consume] iota beta.
          destruct (Address_eqdec dst n) as [ -> | Hnneq ].
          2:{
            eapply psent_mnt_preserve_node_invariant.
            1: eapply PsentLe with (psent1:=(sentMsgs w)) (psent2:=(consume p (sentMsgs w)))...
            now apply H.
          }
          (* only consider the updated node, i.e. itself *)
          (* FIXME: assert this earlier? *)
          pose proof (PsentLe _ _ _ (PsentEq' _ (sentMsgs w) Hpin) 
            (incl_appl_simple _ (broadcast n (LightConfirmMsg (v, lightsig_combine (ls :: lsigs_dst)))))) as Hpmnt1.
          constructor; simpl_state.
          ++cbn delta -[consume] iota beta.
            intros n0 lsig sig Hin.
            rewrite -> in_app_iff.
            left.
            simpl in Hin.
            destruct Hin as [ Hin | Hin ].
            1: inversion Hin; subst; simpl...
            apply In_consume'...
          ++intros lc Hin.
            specialize (Hrlcerts_trace lc Hin).
            destruct Hrlcerts_trace as (src0 & HH).
            exists src0.
            eapply In_psent_mnt'; eauto.
          ++intros c Hin.
            specialize (Hrcerts_trace c Hin).
            destruct Hrcerts_trace as (src0 & HH).
            exists src0.
            eapply In_psent_mnt'; eauto.
          ++simpl.
            intros n0 Hn0valid.
            specialize (Hsubmit_sent n0 Hn0valid).
            destruct Hsubmit_sent as (used0 & HH).
            match goal with |- context[broadcast n ?mm] =>
              eapply In_psent_mnt with (psent':=(consume p (sentMsgs w)) ++ broadcast n mm) in HH end.
            2:{
              eapply PsentLe.
              1: apply PsentEq' with (p:=p)...
              auto with ABCinv.
            }
            simpl in HH.
            destruct HH as (used' & _ & HH).
            eauto.
          ++intros _ n0 Hn0valid.
            exists false.
            rewrite -> in_app_iff.
            right.
            apply In_broadcast.
            eauto.
          ++rewrite -> Forall_forall in Hbuffer_recv |- *.
            intros.
            apply in_app_iff, or_introl, In_consume'...
          ++constructor; simpl...
            unfold zip_from_lsigs, zip_from_sigs.
            simpl.
            intuition constructor; simpl...
        --cbn delta -[consume] iota beta.
          eapply psent_invariant_by_extend with (psent:=consume p (sentMsgs w)).
          1:{
            exists (consume p (sentMsgs w)).
            split...
            split...
            intros p0 Hp0in Hp0notin.
            rewrite -> in_app_iff in Hp0in.
            destruct Hp0in as [ Hp0in | Hp0in ]...
            rewrite -> In_broadcast in Hp0in.
            destruct Hp0in as (n0 & Hn0valid & ->).
            simpl.
            rewrite -> Hnonbyz.
            unfold upd.
            destruct (Address_eqdec dst dst)...
          }
          apply psent_equiv_preserve_psent_invariant with (psent:=(sentMsgs w))...
          eapply state_mnt_preserve_psent_invariant.
          1: rewrite -> Edst; apply Hsmnt.
          1: intros; reflexivity.
          apply H.
      * simpl in Epm.
        assert (~ (thr <= length from_dst)) as Hgt...
        apply PeanoNat.Nat.leb_nle in Hgt.
        rewrite <- Ethr in Epm.
        simpl in Epm. 
        rewrite -> Hgt in Epm.
        injection_pair Epm.
        rewrite -> app_nil_r.
        (* 10 case *)
        eapply inv_preserve_10...
        --(* TODO some repetition here, with regard to above *)
          pose proof (StateCertMnt (localState w dst) (src :: from_dst) (ls :: lsigs_dst) (s :: sigs_dst)) as Hsmnt.
          simpl in Hsmnt.
          specialize (Hsmnt (conj (f_equal S Hsize1) (f_equal S Hsize2))). 
          rewrite -> Edst, <- Ethr in Hsmnt.
          unfold incl in Hsmnt.
          simpl in Hsmnt.
          rewrite -> Hgt in Hsmnt.
          specialize (Hsmnt (conj (fun _ p => or_intror p) (conj (fun _ p => or_intror p) (fun _ p => or_intror p)))).
          rewrite -> Edst.
          apply Hsmnt.
        --destruct H as (_, Hnodeinv, _).
          specialize (Hnodeinv dst Hnonbyz).
          hnf in Hnodeinv.
          rewrite -> Edst in Hnodeinv.
          pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
          (* destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_confsent, Hnodeinv_conf). *)
          constructor; simpl_state...
          ++cbn delta -[consume] iota beta.
            intros n0 lsig sig Hin.
            destruct Hin as [ Hin | Hin ].
            1: inversion Hin; subst; simpl...
            apply In_consume'...
          ++destruct Hnodeinv'.
            assumption.
          ++destruct Hnodeinv'.
            assumption.
          ++destruct Hnodeinv'.
            assumption.
          ++destruct Hnodeinv'.
            assumption.
          ++constructor; simpl...
            unfold zip_from_lsigs, zip_from_sigs.
            simpl.
            intuition constructor; simpl...
        --eapply inv_preserve_00 with (psent:=(sentMsgs w))...
          now rewrite_w_expand w in_ H.
    + (* local state: essentially no change, and psent is regularly changed *)
      assert (st' = (localState w dst)) as ->.
      { 
        rewrite -> Edst.
        (* destruct ov_dst as [ v_dst | ] eqn:Eov_dst... *)
        destruct (Value_eqdec v v_dst), (verify v s src), (light_verify v ls src), 
          conf_dst eqn:E, (In_dec Address_eqdec src from_dst) as [ Ensig_in | Ensig_in ]...
        all: injection_pair Epm...
        all: try rewrite -> Hconf, PeanoNat.Nat.leb_refl...
        rewrite <- PeanoNat.Nat.leb_gt in Hconf.
        rewrite -> Hconf...
      }
      destruct (if Value_eqdec v v_dst 
          then (if verify v s src 
                then (if light_verify v ls src
                      then conf_dst
                      else false)
                else false)
          else false) eqn:Edecide'.
      * destruct (Value_eqdec v v_dst) as [ <- | ], (verify v s src), (light_verify v ls src)...
        subst conf_dst.
        (* send light confirm message *)
        simpl in Epm.
        rewrite <- Edst in Epm.
        inversion Epm.
        subst ms.
        eapply inv_preserve_01.
        1: apply upd_same_pointwise_eq.
        2: rewrite_w_expand w in_ H; apply H.
        exists (consume p (sentMsgs w)).
        split...
        split...
        intros p0 Hin_app Hnotin.
        rewrite -> in_app_iff in Hin_app.
        destruct Hin_app as [ | Hin_ms ]...
        rewrite -> In_broadcast in Hin_ms.
        destruct Hin_ms as (dst' & H_dst'_valid & ->).
        simpl.
        rewrite -> Hnonbyz.
        now rewrite -> Edst.
      * assert (ms = nil) as ->.
        {
          destruct (Value_eqdec v v_dst), (verify v s src), (light_verify v ls src)...
          subst conf_dst.
          destruct (In_dec Address_eqdec src from_dst)...
          rewrite <- PeanoNat.Nat.leb_gt in Hconf.
          simpl in Epm.
          rewrite -> Hconf in Epm...
        }
        rewrite -> app_nil_r.
        eapply inv_preserve_00.
        ++apply upd_same_pointwise_eq.
        ++now apply PsentEq'.
        ++now rewrite_w_expand w in_ H.
    + (* prepend the buffer; belong to none of the monotone cases? *)
      injection_pair Epm.
      rewrite app_nil_r.
      constructor.
      * apply upd_id_intact_preserve_Coh; try assumption.
        --rewrite Edst.
          reflexivity.
        --eapply Coh_psent_irrelevant.
          rewrite_w_expand w in_ H.
          now apply H.
      * intros n H_n_nonbyz.
        unfold holds, upd.
        cbn delta -[consume] iota beta.
        destruct (Address_eqdec dst n) as [ -> | Hnneq ].
        2:{
          eapply psent_mnt_preserve_node_invariant.
          1: eapply PsentLe with (psent1:=(sentMsgs w)) (psent2:=(consume p (sentMsgs w)))...
          now apply H.
        }
        (* only consider the updated node, i.e. itself *)
        pose proof (PsentLe _ _ _ (PsentEq' _ (sentMsgs w) Hpin) 
          (incl_appl_simple _ (broadcast n (LightConfirmMsg (v, lightsig_combine (ls :: lsigs_dst)))))) as Hpmnt1.
        constructor; simpl_state...
        --intros lc Hin.
          specialize (Hrlcerts_trace lc Hin).
          destruct Hrlcerts_trace as (src0 & HH).
          exists src0.
          eapply In_consume'; eauto.
        --intros c Hin.
          specialize (Hrcerts_trace c Hin).
          destruct Hrcerts_trace as (src0 & HH).
          exists src0.
          eapply In_consume'; eauto.
        --rewrite -> Forall_forall in Hbuffer_recv |- *.
          simpl.
          intros ? [ <- | ].
          2: apply In_consume'...
          subst p.
          left.
          reflexivity.
        --constructor; simpl...
          split...
          constructor...
      * eapply psent_equiv_preserve_psent_invariant.
        1: now apply PsentEq'.
        destruct H as (_, _, Hpsentinv).
        constructor; simpl.
        all: intros src0; unfold upd; destruct (Address_eqdec dst src0) as [ <- | ]; [ simpl | apply Hpsentinv ].
        1: destruct Hpsentinv as (Hpsentinv, _, _).
        2: destruct Hpsentinv as (_, Hpsentinv, _).
        3: destruct Hpsentinv as (_, _, Hpsentinv).
        all: specialize (Hpsentinv dst); simpl in Hpsentinv; rewrite Edst in Hpsentinv.
        all: apply Hpsentinv.
  - simpl in Epm.
    destruct lc as (v, cs).
    destruct (combined_verify v cs) eqn:Edecide.
    + injection_pair Epm.
      rewrite -> app_nil_r.
      (* eapply inv_preserve_00 with (psent:=(sentMsgs w))... *)
      eapply inv_preserve_10...
      * match goal with
        |- state_mnt _ _ ?st => replace st with (node_upd_rlcerts (localState w dst) ((v, cs) :: rlcerts_dst))
        end.
        2: simpl; now rewrite -> Edst.
        apply StateRLCertsMnt.
        rewrite -> Edst.
        hnf.
        intuition.
      * destruct H as (_, Hnodeinv, _).
        specialize (Hnodeinv dst Hnonbyz).
        hnf in Hnodeinv.
        rewrite -> Edst in Hnodeinv.
        pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
        (* preserve these ? to make auto work *)
        destruct Hnodeinv as (?, ?, ?, ?, ?, ?, (?, ?, ?, Hrlcerts, ?, ?, ?)).
        constructor; simpl_state.
        --apply Hnodeinv'.
        --simpl.
          destruct Hnodeinv' as (_, Hrlcerts_trace', _, _, _, _, _).
          intros (v0, cs0) [ Hin | Hin ].
          2: now apply Hrlcerts_trace' in Hin.
          injection_pair Hin.
          exists src.
          subst p.
          now left.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --constructor...
          simpl.
          intros v0 cs0 [ Hpeq | ]...
      * eapply inv_preserve_00 with (psent:=(sentMsgs w))...
        now rewrite_w_expand w in_ H.
    + (* essentially no change *)
      injection_pair Epm.
      rewrite -> app_nil_r.
      eapply inv_preserve_00.
      * rewrite <- Edst.
        apply upd_same_pointwise_eq.
      * now apply PsentEq'.
      * now rewrite_w_expand w in_ H.
  - simpl in Epm.
    destruct c as (v, nsigs).
    destruct (if NoDup_eqdec AddrSigPair_eqdec nsigs
      then (if Nat.leb (N - t0) (length nsigs)
            then is_left (verify_certificate v nsigs)
            else false)
      else false) eqn:Edecide.
    + destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
        (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
        (verify_certificate v nsigs) eqn:Everic...
      injection_pair Epm.
      rewrite -> app_nil_r.
      (* eapply inv_preserve_00 with (psent:=(sentMsgs w))... *)
      eapply inv_preserve_10...
      * match goal with
        |- state_mnt _ _ ?st => replace st with (node_upd_rcerts (localState w dst) ((v, nsigs) :: rcerts_dst))
        end.
        2: simpl; now rewrite -> Edst.
        apply StateRCertsMnt.
        rewrite -> Edst.
        hnf.
        intuition.
      * destruct H as (_, Hnodeinv, _).
        specialize (Hnodeinv dst Hnonbyz).
        hnf in Hnodeinv.
        rewrite -> Edst in Hnodeinv.
        pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
        (* preserve these ? to make auto work *)
        destruct Hnodeinv as (?, ?, ?, ?, ?, ?, (?, ?, ?, ?, Hrcerts, ?, ?)).
        constructor; simpl_state.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --simpl.
          destruct Hnodeinv' as (_, _, Hrcerts_trace', _, _, _, _).
          intros (v0, nsigs0) [ Hin | Hin ].
          2: now apply Hrcerts_trace' in Hin.
          injection_pair Hin.
          exists src.
          subst p.
          now left.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --constructor...
          simpl.
          intros v0 nsigs0 [ Hpeq | ]...
          injection_pair Hpeq.
          split; [ | split ]...
          now apply PeanoNat.Nat.leb_le.
      * eapply inv_preserve_00 with (psent:=(sentMsgs w))...
        now rewrite_w_expand w in_ H.
    + assert ((localState w dst, nil) = (st', ms)) as Epm'
        by (destruct (NoDup_eqdec AddrSigPair_eqdec nsigs),
          (Nat.leb (N - t0) (length nsigs)), (verify_certificate v nsigs); eqsolve).
      (* essentially no change *)
      injection_pair Epm'.
      rewrite -> app_nil_r.
      eapply inv_preserve_00.
      * apply upd_same_pointwise_eq.
      * now apply PsentEq'.
      * now rewrite_w_expand w in_ H.
Qed.

Lemma inv_internal_submit_step w w' n :
  invariant w -> system_step (Intern n SubmitIntTrans) w w' -> invariant w'.
Proof with basic_solver.
  intros H Hstep. 
  pose proof (coh _ H) as Hcoh.
  inversion Hstep as [ |
    | n' t Hq Hnvalid H_n_nonbyz Heq 
    | | | ]; try discriminate.
  injection Hq as <-.
  subst t.
  destruct_procInt as_ st' ms eqn_ Epm.
  destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
  subst w'.
  simpl in Epm.
  destruct ov as [ v | ] eqn:Eov.
  - (* simpler *)
    pose proof H as Hv.
    destruct Hv as (_, Hv, _).
    specialize (Hv n H_n_nonbyz).
    unfold holds in Hv.
    rewrite -> En in Hv.
    destruct Hv as (_, _, _, _, _, _, (_, _, _, _, _, Hv, (Hbuffer1 & Hbuffer2))).
    simpl in Hbuffer1.
    specialize (Hbuffer1 eq_refl).
    subst buffer.
    simpl in Epm.
    injection_pair Epm.
    simpl in Hv.
    destruct Hv as (-> & _ & _).
    (* nothing would change *)
    rewrite <- En.
    eapply inv_preserve_01.
    1: apply upd_same_pointwise_eq.
    2: rewrite_w_expand w in_ H; apply H.
    exists (sentMsgs w).
    split...
    split...
    intros p0 Hin_app Hnotin.
    rewrite -> in_app_iff in Hin_app.
    destruct Hin_app as [ Hin_ms | ]...
    rewrite -> In_broadcast in Hin_ms.
    destruct Hin_ms as (dst & H_dst_valid & ->).
    simpl.
    intros _.
    split; [ | split ].
    + now apply key_correct.
    + now apply lightkey_correct.
    + now rewrite -> En.
  - (* this is a different kind of update; may not belong to the monoticity class *)
    (* OK, now added one another case to state monotone ... *)
    (* OK, now it is impossible to do first 01 then 10; need brute force like in deliver submit *)
    subst ov.
    destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in Epm.
    injection_pair Epm.
    rewrite <- app_assoc.
    (* simplify some fields *)
    pose proof H as Hnodeinv.
    destruct Hnodeinv as (_, Hnodeinv, _).
    specialize (Hnodeinv n H_n_nonbyz).
    unfold holds in Hnodeinv.
    rewrite -> En in Hnodeinv.
    destruct Hnodeinv as (Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, _, _, Hbuffer_recv,
      ((Hsize1 & Hsize2), Hconf, _, Hrlcerts, Hrcerts, Hcoll_valid, (_ & Hbuffer))).
    simpl in Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hbuffer_recv, 
      Hsize1, Hsize2, Hconf, Hrlcerts, Hrcerts, Hcoll_valid, Hbuffer.
    subst from.
    destruct sigs, lsigs...
    pose proof t0_lt_N as Htmp.
    simpl in Hconf.
    destruct conf...
    clear Htmp Hsize1 Hsize2.
    (* take one step first *)
    match goal with |- context[broadcast n ?mm] =>
    match type of Efr with context[fold_right _ (?st', nil) _] =>
      assert (invariant (mkW (upd n st' (localState w)) (broadcast n mm ++ sentMsgs w))) as H' end end.
    {
      (* still can get state mnt, which simplifies some proof *)
      pose proof (StateSubmitMnt (localState w n) (value_bft n)) as Hsmnt.
      rewrite En in Hsmnt.
      specialize (Hsmnt eq_refl).
      simpl in Hsmnt.
      constructor.
      - eapply Coh_psent_irrelevant with (psent:=sentMsgs w).
        apply upd_id_intact_preserve_Coh...
        + now rewrite En.
        + now rewrite_w_expand w in_ Hcoh.
      - intros n0 H_n0_nonbyz.
        unfold holds, upd.
        cbn delta -[consume] iota beta.
        destruct (Address_eqdec n n0) as [ <- | Hnneq ].
        2:{
          eapply psent_mnt_preserve_node_invariant.
          1: eapply PsentLe with (psent1:=(sentMsgs w)); [ apply PsentEq | ]...
          now apply H.
        }
        (* only consider the updated node n *)
        constructor; simpl_state; simpl...
        + intros lc Hin.
          specialize (Hrlcerts_trace lc Hin).
          destruct Hrlcerts_trace as (src0 & HH).
          exists src0.
          apply in_app_iff...
        + intros c Hin.
          specialize (Hrcerts_trace c Hin).
          destruct Hrcerts_trace as (src0 & HH).
          exists src0.
          apply in_app_iff...
        + intros n0 Hn0valid.
          exists false.
          rewrite -> in_app_iff.
          left.
          apply In_broadcast.
          eauto.
        + constructor; simpl...
          unfold zip_from_lsigs, zip_from_sigs.
          simpl.
          intuition constructor; simpl...
      - cbn delta -[consume] iota beta.
        eapply psent_invariant_by_extend with (psent:=(sentMsgs w)).
        1:{
          eexists.
          split; [ apply PsentEq | ].
          split...
          intros p0 Hp0in Hp0notin.
          rewrite -> in_app_iff in Hp0in.
          destruct Hp0in as [ Hp0in | Hp0in ]...
          rewrite -> In_broadcast in Hp0in.
          destruct Hp0in as (n0 & Hn0valid & ->).
          simpl.
          unfold upd.
          destruct (Address_eqdec n n)...
        }
        eapply state_mnt_preserve_psent_invariant.
        1: rewrite -> En; apply Hsmnt.
        1: intros; reflexivity.
        apply H.
    }
    (* throw w; only keep some necessary things about buffer *)
    match type of H' with invariant ?ww => remember ww as w' eqn:Ew' end.
    enough (invariant (mkW (upd n st_ (localState w')) (ps_ ++ sentMsgs w'))) as Hgoal.
    {
      subst w'.
      simpl in Hgoal.
      eapply inv_preserve_stmap_pointwise_eq.
      2: apply Hgoal.
      intros n0.
      unfold upd.
      destruct (Address_eqdec n n0)...
    }
    replace (_, nil) with (localState w' n, @nil Packet) in Efr.
    2:{
      subst w'.
      simpl.
      unfold upd.
      destruct (Address_eqdec n n)...
    }
    eapply Forall_impl in Hbuffer_recv.
    2:{
      intros p HH.
      match type of Ew' with context[broadcast n ?mm] => rewrite -> in_app_iff with (l:=broadcast n mm) end.
      right.
      apply HH.
    }
    pose proof (eq_refl (sentMsgs w')) as Htmp.
    rewrite Ew' in Htmp at 1.
    simpl in Htmp.
    rewrite -> Htmp in Hbuffer_recv.
    clear Htmp.
    clear dependent w.
    revert st_ ps_ Efr.
    induction buffer as [ | nmsg buffer IH ]; intros; simpl in Efr.
    + injection_pair Efr.
      simpl.
      eapply inv_preserve_stmap_pointwise_eq.
      * apply upd_same_pointwise_eq.
      * now rewrite_w_expand w' in_ H'.
    + (* processing another buffered message is equivalent with delivering a message *)
      match type of Efr with context[fold_right ?ff ?ini _] =>
        destruct (fold_right ff ini buffer) as (st_', ps_') eqn:Estps end.
      simpl in Efr.
      rewrite -> Forall_cons_iff in Hbuffer, Hbuffer_recv.
      specialize (IH (proj2 Hbuffer) (proj2 Hbuffer_recv) _ _ eq_refl).
      apply proj1 in Hbuffer, Hbuffer_recv.
      destruct nmsg as (src, [ v ls s | lc | c ]).
      all: simpl in Hbuffer; destruct Hbuffer as (H_src_valid & Htmp); try contradiction.
      simpl in Efr, Hbuffer_recv.
      destruct (procMsg st_' src (SubmitMsg v ls s)) as (res1, res2) eqn:Eproc.
      injection_pair Efr.
      rewrite <- app_assoc.
      eapply inv_deliver_step with (p:=mkP src n (SubmitMsg v ls s) true) in IH.
      2:{
        eapply DeliverStep; eauto.
        - simpl.
          apply in_app_iff...
        - simpl.
          unfold upd at 1.
          destruct (Address_eqdec n n); [ | contradiction ].
          rewrite Eproc.
          reflexivity.
      }
      eapply inv_preserve_00.
      3: apply IH.
      1:{
        intros m.
        unfold upd.
        destruct (Address_eqdec n m)...
      }
      (* the most interesting part *)
      apply PsentEq''.
      intros p.
      simpl.
      split.
      * rewrite ! in_app_iff.
        intros [ <- | Hin ].
        1: tauto.
        destruct Hin as [ ([ | ]%in_app_iff & Hneq)%in_remove | ].
        all: tauto.
      * rewrite 1 in_app_iff.
        intros [ Hin | Hin ].
        all: rewrite ! in_app_iff.
        --tauto.
        --destruct (Packet_eqdec (mkP src n (SubmitMsg v ls s) true) p) as [ <- | Hneq1 ].
          1: now left.
          right.
          left.
          apply in_in_remove...
Qed.

Lemma inv_step q w w' :
  invariant w -> system_step q w w' -> invariant w'.
Proof with basic_solver.
  intros H Hstep. 
  pose proof (coh _ H) as Hcoh.
  inversion Hstep as [ 
    | p Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | n t Hq Hnvalid H_n_nonbyz Heq 
    | n dst v ls s Hq H_n_byz Heq 
    | n dst lc Hq H_n_byz Hcc Heq
    | n dst c Hq H_n_byz Hcc Heq ].
  all: subst q.
  - now subst.
  - eapply inv_deliver_step; eauto.
  - destruct t.
    + eapply inv_internal_submit_step; eauto.
    + destruct_procInt as_ st' ms eqn_ Epm.
      destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
      subst w'.
      simpl in Epm.    
      destruct (match ov with
        | Some v => if conf
          then lightcert_conflict_check rlcerts
          else false
        | None => false end) eqn:Edecide'.
      * destruct ov as [ v | ], conf, (lightcert_conflict_check rlcerts) eqn:Everi...
        injection_pair Epm.
        unfold zip_from_sigs.
        simpl.
        rewrite <- En.
        eapply inv_preserve_01.
        1: apply upd_same_pointwise_eq.
        2: rewrite_w_expand w in_ H; apply H.
        exists (sentMsgs w).
        split...
        split...
        intros p0 Hin_app Hnotin.
        rewrite -> in_app_iff in Hin_app.
        destruct Hin_app as [ Hin_ms | ]...
        rewrite -> In_broadcast in Hin_ms.
        destruct Hin_ms as (dst & H_dst_valid & ->).
        simpl.
        rewrite -> H_n_nonbyz, -> En.
        simpl...
      * assert (st' = localState w n /\ ms = nil) as (-> & ->) by (destruct ov, conf, 
          (lightcert_conflict_check rlcerts); simpl in Epm; now injection_pair Epm).
        simpl.
        eapply inv_preserve_stmap_pointwise_eq.
        --apply upd_same_pointwise_eq.
        --now rewrite_w_expand w in_ H.
  - subst w'.
    eapply inv_preserve_01.
    1: reflexivity.
    2: rewrite_w_expand w in_ H; apply H.
    exists (sentMsgs w).
    split...
    split.
    1: unfold incl; firstorder.
    intros p0 Hin_app Hnotin.
    simpl in Hin_app.
    destruct Hin_app as [ <- | ]...
  - subst w'.
    eapply inv_preserve_01.
    1: reflexivity.
    2: rewrite_w_expand w in_ H; apply H.
    exists (sentMsgs w).
    split...
    split.
    1: unfold incl; firstorder.
    intros p0 Hin_app Hnotin.
    simpl in Hin_app.
    destruct Hin_app as [ <- | ]...
    simpl.
    rewrite -> H_n_byz...
  - (* TODO repeating *)
    subst w'.
    eapply inv_preserve_01.
    1: reflexivity.
    2: rewrite_w_expand w in_ H; apply H.
    exists (sentMsgs w).
    split...
    split.
    1: unfold incl; firstorder.
    intros p0 Hin_app Hnotin.
    simpl in Hin_app.
    destruct Hin_app as [ <- | ]...
    simpl.
    rewrite -> H_n_byz...
Qed.

Lemma stmap_pointwise_eq_preserve_inv_2 stmap stmap' psent
  (Hpeq : forall x, stmap x = stmap' x) 
  (Hinv2 : invariant_2 (mkW stmap psent)) : invariant_2 (mkW stmap' psent).
Proof.
  constructor.
  destruct Hinv2 as (Hpsentinv).
  rewrite -> Forall_forall in Hpsentinv |- *.
  simpl in Hpsentinv |- *.
  intros (?, ?, ?, ?) Hin.
  rewrite <- Hpeq.
  now apply Hpsentinv in Hin.
Qed.

Lemma inv_2_by_extend_freshpkt stmap psent psent'
  (Hsubset : forall p, In p psent' -> In p psent \/ consumed p = false)
  (Hinv2 : invariant_2 (mkW stmap psent)) : invariant_2 (mkW stmap psent').
Proof.
  constructor.
  destruct Hinv2 as (Hpsentinv).
  rewrite -> Forall_forall in Hpsentinv |- *.
  simpl in Hpsentinv |- *.
  intros (?, ?, ?, used) Hin.
  apply Hsubset in Hin.
  simpl in Hin.
  destruct Hin as [ Hin | -> ].
  - now apply Hpsentinv in Hin.
  - now destruct msg0 as [ | (?, ?) | (?, ?) ].
Qed.

(* pure facts; should not require any invariant *)

Fact procMsg_sent_packets_are_fresh st src msg :
  forall p (Hin : In p (snd (procMsg st src msg))), consumed p = false.
Proof with basic_solver.
  intros.
  destruct (procMsg st src msg) as (st', ms) eqn:Epm.
  simpl in Hin.
  destruct st as (n, conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer) eqn:Est.
  destruct msg as [ v' ls s | (v, cs) | (v, nsigs) ]; simpl in Epm.
  - (* avoid processing so many subgoals at the same time ... *)
    destruct ov as [ v | ] eqn:Eov.
    2: now injection_pair Epm.
    destruct (Value_eqdec v' v) as [ -> | ].
    2: now injection_pair Epm.
    destruct (verify v s src).
    2: now injection_pair Epm.
    destruct (light_verify v ls src).
    2: now injection_pair Epm.
    destruct conf; simpl in Epm.
    1:{
      injection_pair Epm.
      apply In_broadcast in Hin.
      now destruct Hin as (? & ? & ->).
    }
    destruct (in_dec Address_eqdec src from); simpl in Epm.
    + destruct (Nat.leb (N - t0) (length from)); injection_pair Epm.
      * apply In_broadcast in Hin.
        now destruct Hin as (? & ? & ->).
      * simpl in Hin...
    + destruct (Nat.leb (N - t0) (S (length from))); injection_pair Epm.
      * apply In_broadcast in Hin.
        now destruct Hin as (? & ? & ->).
      * simpl in Hin...
  - destruct (combined_verify v cs).
    all: now injection_pair Epm.
  - destruct (NoDup_eqdec AddrSigPair_eqdec nsigs),
      (Nat.leb (N - t0) (length nsigs)), (verify_certificate v nsigs).
    all: now injection_pair Epm.
Qed.

(* TODO is this necessary or useful? *)
Fact procInt_sent_packets_are_fresh st tr :
  forall p (Hin : In p (snd (procInt st tr))), consumed p = false.
Proof with basic_solver.
  intros.
  destruct (procInt st tr) as (st', ms) eqn:Epm.
  simpl in Hin.
  destruct st as (n, conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer) eqn:Est.
  destruct tr; simpl in Epm.
  - destruct (fold_right _ _ _) as (st'', ps') eqn:Estps in Epm.
    injection_pair Epm.
    rewrite in_app_iff in Hin.
    destruct Hin as [ Hin | Hin ].
    + clear Est.
      revert st'' ps' Estps Hin.
      induction buffer as [ | (src, msg) buffer IH ]; intros; simpl in Estps.
      * now injection_pair Estps.
      * destruct (fold_right _ _ _) as (st_, ps_) eqn:Estps' in Estps.
        specialize (IH st_ ps_ Estps').
        simpl in Estps.
        destruct (procMsg st_ src msg) as (st__, ps__) eqn:Epm'.
        injection_pair Estps.
        rewrite in_app_iff in Hin.
        destruct Hin as [ Hin | Hin ]...
        epose proof (procMsg_sent_packets_are_fresh st_ src msg) as H.
        rewrite Epm' in H.
        simpl in H.
        now apply H.
    + apply In_broadcast in Hin.
      now destruct Hin as (? & ? & ->).
  - destruct ov, conf, (lightcert_conflict_check rlcerts).
    all: injection_pair Epm.
    all: simpl in Hin...
    all: rewrite -> In_broadcast in Hin.
    all: destruct Hin as (? & ? & ->)...
Qed.

Lemma inv_2_init : invariant_2 initWorld.
Proof with basic_solver.
  do 2 constructor.
Qed.

Lemma inv_2_deliver_step w w' p 
  (Hinv2 : invariant_2 w) (Hcoh : Coh w) 
  (Hstep : system_step (Deliver p) w w') : invariant_2 w' /\ Coh w'. (* there is inevitably repetition for Coh proof *)
Proof with basic_solver.
  destruct Hinv2 as (Hpsentinv).
  pose proof Hpsentinv as Hpsentinv'.
  rewrite -> Forall_forall in Hpsentinv'.
  inversion Hstep as [ 
    | p' Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | | | | ]; try discriminate.
  injection Hq as <-.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  pose proof (procMsg_sent_packets_are_fresh (localState w dst) src msg) as Hfresh.
  destruct_procMsg as_ st' ms eqn_ Epm.
  destruct_localState w dst as_ conf_dst ov_dst from_dst lsigs_dst sigs_dst 
    rlcerts_dst rcerts_dst buffer_dst eqn_ Edst.
  subst w'.
  simpl in Hfresh.
  destruct msg as [ v ls s | lc | c ].
  - simpl in Epm.
    (* do some brute force to obtain some pure facts after delivery *)
    (* TODO merge the following two proofs? *)
    assert (received_lightcerts st' = rlcerts_dst /\ received_certs st' = rcerts_dst /\ 
      ov_dst = st'.(submitted_value) /\ (conf_dst -> conf st') /\ id st' = dst) as (Hrlcerts_intact & Hrcerts_intact & Eov & Hconf_impl & Hid_intact).
    {
      destruct ov_dst as [ v_dst | ] eqn:Eov_dst.
      (* TODO possibly optimize this exhaustive case analysis? *)
      1: destruct (Value_eqdec v v_dst), (verify v s src), (light_verify v ls src), 
        conf_dst eqn:E, (In_dec Address_eqdec src from_dst) as [ Ensig_in | Ensig_in ], 
        (Nat.leb (N - t0) (length from_dst)) eqn:Ele.
      all: simpl in Epm.
      all: try rewrite Ele in Epm.
      all: injection_pair Epm...
    }
    split.
    2:{
      apply Coh_psent_irrelevant with (psent:=sentMsgs w).
      apply upd_id_intact_preserve_Coh...
      - now rewrite Edst.
      - rewrite_w_expand w in_ Hcoh.
        assumption.
    }
    (*
    specialize (Hnodeinv dst Hnonbyz).
    unfold holds in Hnodeinv.
    rewrite -> Edst in Hnodeinv.
    destruct Hnodeinv as (_, _, _, _, Hbuffer_recv,
      (_, Hconf, Hfrom_nodup, _, _, _, (Hbuffer1 & Hbuffer2))).
    simpl in Hbuffer_recv,  
      Hconf, Hfrom_nodup, Hbuffer1, Hbuffer2.
    *)
    assert (match ov_dst with
      | Some v_dst => if (if Value_eqdec v v_dst 
          then (if verify v s src 
                then (if light_verify v ls src
                      then (if (negb conf_dst) 
                            then (negb (is_left (In_dec Address_eqdec src from_dst)))
                                (* (if (negb (is_left (In_dec Address_eqdec src from_dst)))
                                  then negb (Nat.leb (N - t0) (S (length from_dst)))
                                  else false)  *)
                            else false) 
                      else false)
                else false)
          else false)
        then st'.(from_set) = src :: from_dst
        else st'.(from_set) = from_dst
      | None => st'.(msg_buffer) = (src, SubmitMsg v ls s) :: buffer_dst
      end) as Hov_res.
    {
      (* TODO is the following partly repeating the proof of procMsg_sent_packets_are_fresh? *)
      destruct ov_dst as [ v_dst | ] eqn:Eov_dst.
      - destruct (Value_eqdec v v_dst) as [ <- | ]. 
        2: now injection_pair Epm.
        destruct (verify v s src).
        2: now injection_pair Epm.
        destruct (light_verify v ls src).
        2: now injection_pair Epm.
        destruct (conf_dst); simpl in Epm |- *.
        1: now injection_pair Epm.
        destruct (in_dec Address_eqdec src from_dst); simpl in Epm |- *.
        all: now injection_pair Epm.
      - now injection_pair Epm.
    }
    (* now discuss; mainly care about the case if the message is submit *)
    apply inv_2_by_extend_freshpkt with (psent:=consume p (sentMsgs w)).
    1: setoid_rewrite -> in_app_iff.
    1: intuition.
    constructor.
    apply Forall_forall.
    simpl.
    intros p0 [ Hin | Hin ].
    + rewrite Ep in Hin.
      simpl in Hin.
      subst p0.
      unfold upd.
      destruct (Address_eqdec dst dst)...
      rewrite <- Eov.
      intros _ _.
      destruct ov_dst as [ v_dst | ].
      * intros Hc <- He Hf.
        destruct (Value_eqdec v v), (verify v s src), (light_verify v ls src)...
        destruct conf_dst; simpl in Epm, Hov_res.
        --(* now get false *)
          injection_pair Epm...
        --destruct (In_dec Address_eqdec src from_dst) as [ Ensig_in | Ensig_in ]; simpl in Hov_res.
          ++now rewrite Hov_res.
          ++rewrite Hov_res.
            simpl...
      * rewrite Hov_res.
        simpl...
    + destruct p0 as (src0, dst0, msg0, b0).
      apply in_remove in Hin.
      destruct Hin as (Hin & _).
      apply Hpsentinv' in Hin.
      simpl in Hin.
      unfold upd.
      destruct (Address_eqdec dst dst0) as [ <- | Hnneq ].
      2: apply Hin.
      rewrite -> Hrcerts_intact, <- Eov, -> Hrlcerts_intact.
      rewrite -> Edst in Hin.
      simpl in Hin |- *.
      destruct msg0 as [ v0 ls0 s0 | (?, ?) | (?, ?) ]...
      intros Ha Hb.
      specialize (Hin Ha Hb).
      destruct ov_dst as [ v_dst | ].
      --intros Hc.
        rewrite Hc in Hconf_impl.
        destruct conf_dst.
        1: specialize (Hconf_impl eq_refl)...
        specialize (Hin eq_refl).
        match type of Hov_res with if ?bb then _ else _ => destruct bb eqn:Edecide; rewrite Hov_res end.
        all: simpl...
      --rewrite Hov_res.
        simpl...
  - (* critical case 1 *)
    simpl in Epm.
    destruct lc as (v, cs).
    assert (ms = nil /\ id st' = dst) as (-> & Hid_intact) by (destruct (combined_verify v cs); injection_pair Epm; eqsolve).
    rewrite -> app_nil_r.
    split.
    2:{
      apply Coh_psent_irrelevant with (psent:=sentMsgs w).
      apply upd_id_intact_preserve_Coh...
      - now rewrite Edst.
      - rewrite_w_expand w in_ Hcoh.
        assumption.
    }
    constructor.
    rewrite -> Forall_forall in Hpsentinv |- *.
    simpl.
    intros p0 [ Hin | Hin ].
    + rewrite Ep in Hin.
      simpl in Hin.
      subst p0.
      unfold upd.
      destruct (Address_eqdec dst dst)...
      destruct (combined_verify v cs) eqn:Everi...
      injection Epm as <-.
      simpl. 
      intuition.
    + destruct p0 as (src0, dst0, msg0, b0).
      apply in_remove in Hin.
      destruct Hin as (Hin & _).
      apply Hpsentinv' in Hin.
      simpl in Hin.
      unfold upd.
      destruct (Address_eqdec dst dst0) as [ <- | Hnneq ].
      2: apply Hin.
      rewrite -> Edst in Hin.
      simpl in Hin.
      destruct msg0 as [ | (v0, cs0) | (?, ?) ]...
      all: destruct (combined_verify v cs) eqn:Everi.
      all: injection Epm as <-...
      simpl.
      intuition.
  - (* critical case 2 *)
    simpl in Epm.
    destruct c as (v, nsigs).
    assert (ms = nil /\ id st' = dst) as (-> & Hid_intact)
      by (destruct (NoDup_eqdec AddrSigPair_eqdec nsigs),
        (Nat.leb (N - t0) (length nsigs)), (verify_certificate v nsigs); injection_pair Epm; eqsolve).
    rewrite -> app_nil_r.
    split.
    2:{
      apply Coh_psent_irrelevant with (psent:=sentMsgs w).
      apply upd_id_intact_preserve_Coh...
      - now rewrite Edst.
      - rewrite_w_expand w in_ Hcoh.
        assumption.
    }
    constructor.
    rewrite -> Forall_forall in Hpsentinv |- *.
    simpl.
    intros p0 [ Hin | Hin ].
    + rewrite Ep in Hin.
      simpl in Hin.
      subst p0.
      unfold upd.
      destruct (Address_eqdec dst dst)...
      destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
        (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
        (verify_certificate v nsigs) eqn:Everic...
      all: injection Epm as <-.
      * simpl. 
        intuition.
      * intros.
        rewrite <- PeanoNat.Nat.leb_le in *.
        eqsolve.
    + destruct p0 as (src0, dst0, msg0, b0).
      apply in_remove in Hin.
      destruct Hin as (Hin & _).
      apply Hpsentinv' in Hin.
      simpl in Hin.
      unfold upd.
      destruct (Address_eqdec dst dst0) as [ <- | Hnneq ].
      2: apply Hin.
      rewrite -> Edst in Hin.
      destruct msg0 as [ | (?, ?) | (v0, nsigs0) ]...
      simpl in Hin |- *.
      all: destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
        (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
        (verify_certificate v nsigs) eqn:Everic.
      all: injection Epm as <-...
      simpl.
      intuition.
Qed.

Lemma inv_2_internal_submit_step w w' n
  (Hinv2 : invariant_2 w) (Hinv : invariant w)
  (Hstep : system_step (Intern n SubmitIntTrans) w w') : invariant_2 w'.
Proof with basic_solver.
  pose proof Hinv as (Hcoh, _, _).
  pose proof Hinv2 as (Hpsentinv').
  rewrite -> Forall_forall in Hpsentinv'.
  inversion Hstep as [ |
    | n' t Hq Hnvalid H_n_nonbyz Heq 
    | | | ]; try discriminate.
  injection Hq as <-.
  subst t.
  pose proof (procInt_sent_packets_are_fresh (localState w n) SubmitIntTrans) as Hfresh.
  destruct_procInt as_ st' ms eqn_ Epm.
  destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
  subst w'.
  simpl in Hfresh, Epm.
  destruct Hinv as (_, Hv, _).
  specialize (Hv n H_n_nonbyz).
  unfold holds in Hv.
  rewrite -> En in Hv.
  destruct Hv as (_, _, _, _, _, Hbuffer_recv, (_, _, _, _, _, Hv, (Hbuffer1 & Hbuffer2))).
  simpl in Hbuffer_recv, Hbuffer1, Hbuffer2, Hv.
  destruct ov as [ v | ] eqn:Eov.
  - apply inv_2_by_extend_freshpkt with (psent:=(sentMsgs w)).
    1:{
      setoid_rewrite in_app_iff.
      intros p [ Hin | ]...
    }
    clear Hfresh.
    specialize (Hbuffer1 eq_refl).
    subst buffer.
    destruct Hv as (-> & _ & _).
    simpl in Epm.
    injection_pair Epm.
    rewrite <- En.
    eapply stmap_pointwise_eq_preserve_inv_2.
    + apply upd_same_pointwise_eq.
    + rewrite_w_expand w in_ Hinv2.
      assumption.
  - subst from ov.
    clear Hbuffer1 Hstep.
    remember (map (fun nmsg => mkP (fst nmsg) n (snd nmsg) true) buffer) as pkts eqn:Epkts.
    destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in Epm.
    injection_pair Epm.
    setoid_rewrite in_app_iff in Hfresh.
    remember (broadcast _ _) as pkts_b eqn:Epkts_b in |- *.
    rewrite <- Epkts_b in *.
    match type of Efr with context[fold_right _ (?ss, nil) _] => remember ss as st' eqn:Est' end.
    remember (mkW (upd n st' (localState w)) (set_diff Packet_eqdec (sentMsgs w) pkts)) as w' eqn:Ew'.
    (* initial step by retracting Hpsentinv' *)
    assert (Coh w') as Hcoh'.
    {
      subst st' w'.
      apply Coh_psent_irrelevant with (psent:=sentMsgs w).
      apply upd_id_intact_preserve_Coh...
      - rewrite En.
        reflexivity.
      - rewrite_w_expand w in_ Hcoh.
        assumption.
    }
    assert (invariant_2 w') as Hpsentinv''.
    {
      subst st' w'.
      constructor.
      rewrite -> Forall_forall.
      cbn delta [sentMsgs localState] beta iota.
      intros (src0, dst0, msg0, b0) Hin%set_diff_iff.
      destruct Hin as (Hin & Hnotin).
      apply Hpsentinv' in Hin.
      simpl in Hin |- *.
      unfold upd.
      destruct (Address_eqdec n dst0) as [ <- | ].
      2: now apply Hin.
      rewrite En in Hin.
      simpl in Hin |- *.
      destruct msg0 as [ v0 lsig0 sig0 | lc0 | c0 ]...
      intros Ha Hb.
      specialize (Hin Ha Hb).
      destruct b0...
      match type of Epkts with _ = map ?ff _ => eapply in_map with (f:=ff) in Hin end.
      simpl in Hin...
    }
    assert (invariant_2 (mkW (upd n st_ (localState w')) (pkts ++ ps_ ++ sentMsgs w')) /\
      Coh (mkW (upd n st_ (localState w')) (pkts ++ ps_ ++ sentMsgs w'))) as (Hgoal & _).
    {
      replace (_, nil) with (localState w' n, @nil Packet) in Efr.
      2:{
        subst w'.
        simpl.
        unfold upd.
        destruct (Address_eqdec n n)...
      }
      clear Ew' En st' Est' Hfresh.
      revert st_ ps_ Efr pkts Epkts.
      induction buffer as [ | nmsg buffer IH ]; intros; simpl in Epkts, Efr.
      - subst pkts.
        injection_pair Efr.
        simpl.
        split.
        + eapply stmap_pointwise_eq_preserve_inv_2.
          * apply upd_same_pointwise_eq.
          * rewrite_w_expand w' in_ Hpsentinv''.
            assumption.
        + apply state_mnt_preserve_Coh with (ob:=false)...
          rewrite_w_expand w' in_ Hcoh'.
          assumption.
      - (* TODO repeating the induction above? *)
        match type of Efr with context[fold_right ?ff ?ini _] =>
          destruct (fold_right ff ini buffer) as (st_', ps_') eqn:Estps end.
        simpl in Efr.
        destruct pkts as [ | p pkts ]...
        injection Epkts as ->.
        match goal with HH : pkts = _ |- _ => rename HH into Epkts end.
        rewrite -> Forall_cons_iff in Hbuffer_recv, Hbuffer2.
        specialize (IH (proj2 Hbuffer_recv) (proj2 Hbuffer2) _ _ eq_refl _ Epkts).
        destruct IH as (IHinv2 & IHcoh).
        apply proj1 in Hbuffer2, Hbuffer_recv.
        destruct nmsg as (src, [ v ls s | lc | c ]).
        all: simpl in Hbuffer2; destruct Hbuffer2 as (H_src_valid & Htmp); try contradiction.
        simpl in Efr, Hbuffer_recv |- *.
        destruct (procMsg st_' src (SubmitMsg v ls s)) as (res1, res2) eqn:Eproc.
        injection_pair Efr.
        (* trick: add one undelivered message *)
        eapply Coh_psent_irrelevant with (psent':=(mkP src n (SubmitMsg v ls s) false) :: pkts ++ ps_' ++ sentMsgs w') in IHcoh.
        eapply inv_2_by_extend_freshpkt with (psent':=(mkP src n (SubmitMsg v ls s) false) :: pkts ++ ps_' ++ sentMsgs w') in IHinv2.
        2: simpl; intros ? [ <- | ]; simpl...
        epose proof (inv_2_deliver_step _ _ (mkP src n (SubmitMsg v ls s) false) IHinv2 IHcoh ?[Goalq]) as (Hinv2_step & Hcoh_step).
        [Goalq]:{
          eapply DeliverStep.
          1: reflexivity.
          2-4: auto.
          1: simpl; auto.
          cbn delta [sentMsgs localState dst AC.src msg] beta iota.
          unfold upd at 1.
          destruct (Address_eqdec n n)...
          rewrite Eproc.
          (* actually consume is useful here *)
          simpl.
          destruct (Packet_eqdec _ _) in |- *.
          2: contradiction.
          reflexivity.
        }
        split.
        + match type of Hinv2_step with invariant_2 (mkW ?ls _) =>
            eapply stmap_pointwise_eq_preserve_inv_2 with (stmap:=ls) end.
          1:{
            intros m.
            unfold upd.
            destruct (Address_eqdec n m)...
          }
          eapply inv_2_by_extend_freshpkt.
          2: apply Hinv2_step.
          simpl.
          intros p [ <- | Hin ]...
          destruct (consumed p) eqn:Eused...
          left.
          right.
          assert (In p ((pkts ++ ps_' ++ sentMsgs w') ++ res2)) as Hin_.
          1: rewrite -> ! in_app_iff in Hin; rewrite -> ! in_app_iff; tauto.
          rewrite 1 in_app_iff in Hin_.
          rewrite 1 in_app_iff.
          destruct Hin_ as [ Hin_ | Hin_ ]...
          left.
          apply in_in_remove...
          destruct p.
          simpl in Eused.
          eqsolve.
        + eapply Coh_psent_irrelevant.
          eapply stmap_pointwise_eq_preserve_Coh.
          2: apply Hcoh_step.
          intros m.
          unfold upd.
          destruct (Address_eqdec n m)...
    }
    subst w'.
    simpl in Hgoal.
    match type of Hgoal with invariant_2 (mkW ?ls _) =>
      eapply stmap_pointwise_eq_preserve_inv_2 with (stmap:=ls) end.
    1:{
      intros m.
      unfold upd.
      destruct (Address_eqdec n m)...
    }
    eapply inv_2_by_extend_freshpkt with (psent:=ps_ ++ sentMsgs w).
    1: intros p; rewrite ! in_app_iff; specialize (Hfresh p)...
    destruct Hgoal as (Hgoal).
    constructor.
    simpl in Hgoal |- *.
    rewrite Forall_forall in Hgoal |- *.
    intros p Hin%in_app_iff.
    specialize (Hgoal p).
    rewrite -> ! in_app_iff, -> set_diff_iff in Hgoal.
    apply Hgoal.
    destruct (in_dec Packet_eqdec p pkts)...
Qed.

Lemma inv_2_step q w w' (Hinv2 : invariant_2 w) (Hinv : invariant w)
  (Hstep : system_step q w w') : invariant_2 w'.
Proof with basic_solver.
  pose proof (coh _ Hinv) as Hcoh.
  pose proof Hinv2 as (Hpsentinv).
  pose proof Hpsentinv as Hpsentinv'.
  rewrite -> Forall_forall in Hpsentinv'.
  inversion Hstep as [ 
    | p Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | n t Hq Hnvalid H_n_nonbyz Heq 
    | n dst v ls s Hq H_n_byz Heq 
    | n dst lc Hq H_n_byz Hcc Heq
    | n dst c Hq H_n_byz Hcc Heq ].
  all: subst q.
  - now subst.
  - eapply inv_2_deliver_step; eauto.
  - pose proof (procInt_sent_packets_are_fresh (localState w n) t) as Hfresh.
    destruct_procInt as_ st' ms eqn_ Epm.
    destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    subst w'.
    simpl in Hfresh.
    destruct t.
    + eapply inv_2_internal_submit_step in Hinv2.
      2: assumption.
      2: apply Hstep.
      assumption.
    + apply inv_2_by_extend_freshpkt with (psent:=(sentMsgs w)).
      1:{
        setoid_rewrite in_app_iff.
        intros p [ Hin | ]...
      }
      simpl in Epm.
      destruct ov, conf, (lightcert_conflict_check rlcerts).
      all: injection_pair Epm.
      all: try rewrite <- En.
      all: eapply stmap_pointwise_eq_preserve_inv_2; 
        [ apply upd_same_pointwise_eq | constructor; simpl ]...
  (* TODO repeating below *)
  - subst w'.
    apply inv_2_by_extend_freshpkt with (psent:=(sentMsgs w)).
    2: now constructor.
    simpl.
    intros p [ <- | ].
    all: intuition.
  - subst w'.
    apply inv_2_by_extend_freshpkt with (psent:=(sentMsgs w)).
    2: now constructor.
    simpl.
    intros p [ <- | ].
    all: intuition.
  - subst w'.
    apply inv_2_by_extend_freshpkt with (psent:=(sentMsgs w)).
    2: now constructor.
    simpl.
    intros p [ <- | ].
    all: intuition.
Qed.

Inductive reachable : list system_step_descriptor -> World -> Prop :=
  | ReachableInit : reachable nil initWorld
  | ReachableStep q (w w' : World) (Hstep : system_step q w w')
    sched (H_w_reachable : reachable sched w) : reachable (q :: sched) w'.

Lemma reachable_inv w sched (H_w_reachable : reachable sched w) :
  invariant w.
Proof.
  induction H_w_reachable as [ | q w w' Hstep sched H_w_reachable IH ].
  - apply inv_init.
  - now apply inv_step in Hstep.
Qed.

Local Fact zip_aux_pre {A B : Type} (l1 : list A) : forall (l2 : list B)
  (Hsize : length l1 = length l2)
  a (Hin : In a l1), exists b, In (a, b) (combine l1 l2).
Proof.
  induction l1 as [ | aa l1 IH ]; intros.
  - now simpl in Hin.
  - destruct l2 as [ | bb l2 ]; simpl in Hsize; try lia.
    simpl in Hin |- *.
    destruct Hin as [ <- | Hin ].
    + exists bb.
      now left.
    + injection Hsize as Hsize.
      specialize (IH _ Hsize _ Hin).
      destruct IH as (b & IH).
      eauto.
Qed.

Local Fact zip_aux {A B C : Type} (l1 : list A) : forall (l2 : list B) (l3 : list C)
  (Hsize1 : length l1 = length l2) (Hsize2 : length l1 = length l3)
  a c (Hin : In (a, c) (combine l1 l3)),
  exists b, In (a, b, c) (combine (combine l1 l2) l3).
Proof.
  induction l1 as [ | aa l1 IH ]; intros.
  - now simpl in Hin.
  - destruct l2 as [ | bb l2 ], l3 as [ | cc l3 ]; simpl in Hsize1, Hsize2; try lia.
    simpl in Hin |- *.
    destruct Hin as [ Hin | Hin ].
    + injection_pair Hin.
      exists bb.
      now left.
    + injection Hsize1 as Hsize1.
      injection Hsize2 as Hsize2.
      specialize (IH _ _ Hsize1 Hsize2 _ _ Hin).
      destruct IH as (b & IH).
      eauto.
Qed.

Lemma inv_sound_weak w (Hinv : invariant w)
  n (H_n_nonbyz : is_byz n = false)
  nb (Hacc : In nb (genproof (received_certs (localState w n)))) :
  (* behave_byz nb (sentMsgs w). *)
  is_byz nb.
Proof.
  (* prove by contradiction *)
  destruct (is_byz nb) eqn:E.
  1: auto.
  destruct genproof_correct as (Hgp, _).
  apply Hgp in Hacc.
  destruct Hacc as (v1 & v2 & sig1 & sig2 & nsigs1 & nsigs2 & Hvneq & Hin1 & Hin2 & Hin_nsigs1 & Hin_nsigs2).
  (* cert in rcerts --> Confirm msg *)
  destruct Hinv as (Hcoh, Hnodeinv, Hpsentinv).
  pose proof (Hnodeinv n H_n_nonbyz) as Hnodeinv_n.
  unfold holds in Hnodeinv_n.
  destruct Hnodeinv_n as (_, _, Hrcerts_trace, _, _, _, ((_ & Hsize2), _, _, _, Hrcerts, _, _)).
  (* sig1, sig2 must be valid *)
  pose proof (Hrcerts _ _ Hin1) as (Hnsigs_valid1 & _ & _).
  pose proof (Hrcerts _ _ Hin2) as (Hnsigs_valid2 & _ & _).
  pose proof Hin_nsigs1 as Hin_nsigs1_backup.
  pose proof Hin_nsigs2 as Hin_nsigs2_backup.
  eapply valid_cert_valid_sig in Hin_nsigs1, Hin_nsigs2; eauto.
  subst sig1 sig2.
  apply Hrcerts_trace in Hin1, Hin2.
  destruct Hin1 as (src1 & Hin1), Hin2 as (src2 & Hin2).
  unfold psent_invariant in Hpsentinv.
  rewrite -> psent_invariant_viewchange in Hpsentinv.
  apply Hpsentinv in Hin1, Hin2.
  (* TODO slightly overlapped with the behave_byz_is_byz proof *)
  assert (forall v nsigs src dst used
    (Hin : _inv_msg_correct (localState w) (sentMsgs w) (mkP src dst (ConfirmMsg (v, nsigs)) used))
    (Hin_nsigs : In (nb, sign v (key_map nb)) nsigs),
    Some v = (localState w nb).(submitted_value)) as Htraceback.
  {
    intros v0 nsigs0 src0 dst0 used0 Hin Hin_nsigs.
    simpl in Hin.
    destruct (is_byz src0) eqn:Ebyz0.
    - specialize (Hin _ _ Hin_nsigs E (correct_sign_verify_ok _ _)).
      unfold sig_seen_in_history in Hin.
      (* overlapping *)
      destruct Hin as (dst & used & ls & Hin).
      apply Hpsentinv in Hin.
      simpl in Hin.
      intuition.
    - destruct Hin as (_ & _ & Ev0 & Hcert).
      (* instantiate another nodeinv *)
      specialize (Hnodeinv src0 Ebyz0).
      unfold holds in Hnodeinv.
      destruct Hnodeinv as (Hcoll_trace, _, _, _, _, _, ((Hsize1' & Hsize2'), _, _, _, _, _, _)).
      rewrite <- Ev0, -> (id_coh _ Hcoh src0) in Hcoll_trace.
      (* TODO here it actually indicates some inconvenience of not saving the complete submit message *)
      assert (exists lsig, In (nb, lsig, sign v0 (key_map nb))
        (zip_from_lsigs_sigs (localState w src0))) as (lsig & Hin_zip).
      { 
        subst.
        unfold zip_from_lsigs_sigs, zip_from_sigs in *.
        apply zip_aux; auto.
      }
      apply Hcoll_trace in Hin_zip.
      (* overlapping *)
      (* coming back! *)
      apply Hpsentinv in Hin_zip.
      simpl in Hin_zip.
      intuition.
  }
  apply Htraceback in Hin1.
  2: assumption.
  apply Htraceback in Hin2.
  2: assumption.
  eqsolve.
Qed.

(* supplementary *)
  
Definition behave_byz n psent :=
  exists v1 v2 sig1 sig2 lsig1 lsig2 dst1 dst2, 
    v1 <> v2 /\
    In (mkP n dst1 (SubmitMsg v1 lsig1 sig1) true) psent /\
    In (mkP n dst2 (SubmitMsg v2 lsig2 sig2) true) psent.

Lemma behave_byz_is_byz n psent stmap
  (Hpsentinv : psent_invariant stmap psent)
  (Hbyz : behave_byz n psent) : is_byz n.
Proof.
  (* prove by contradiction *)
  destruct (is_byz n) eqn:E.
  1: reflexivity.
  destruct Hbyz as (v1 & v2 & lsig1 & lsig2 & sig1 & sig2 & dst1 & dst2 & Hvneq & Hin1 & Hin2).
  hnf in Hpsentinv.
  rewrite -> psent_invariant_viewchange in Hpsentinv.
  apply Hpsentinv in Hin1, Hin2.
  simpl in Hin1, Hin2.
  eqsolve.
Qed.

Lemma conflicting_cert_quorum_size v1 v2 nsigs1 nsigs2 
  (Hcert_valid1 : certificate_valid v1 nsigs1)
  (Hnsigs_nodup1 : NoDup nsigs1)
  (Hsize1 : N - t0 <= (length nsigs1))
  (Hcert_valid2 : certificate_valid v2 nsigs2)
  (Hnsigs_nodup2 : NoDup nsigs2)
  (Hsize2 : N - t0 <= (length nsigs2)) :
  (N - (t0 + t0)) <= length (filter (fun nsig => In_dec Address_eqdec (fst nsig) (map fst nsigs1)) nsigs2). 
Proof.
  (* now show that: at least (2t0-N) distinct nodes are in culprit proof *)
  (* should partition only by the address since signs can be different for different values *)
  destruct (partition (fun nsig => In_dec Address_eqdec (fst nsig) (map fst nsigs1)) nsigs2) as (nsigs12, nsigs2') eqn:Epar.
  epose proof (partition_filter _ nsigs2) as Htmp.
  rewrite -> Epar in Htmp.
  match type of Htmp with (?a, ?b) = (?c, ?d) => 
    assert (a = c) as Ensigs12 by eqsolve; 
    assert (b = d) as Ensigs2' by eqsolve
  end.
  clear Htmp.
  rewrite <- Ensigs12.
  assert (certificate_valid v2 nsigs2') as Hcert_valid2' by (subst nsigs2'; now apply Forall_filter).
  - (* maybe this part has been well formalized in other Coq libraries ... *)
    cut (((length nsigs2) - (length nsigs12)) + (length nsigs1) <= N).
    1: lia.
    pose proof Epar as Elengthpar.
    apply partition_length in Elengthpar.
    replace ((length nsigs2) - (length nsigs12)) with (length nsigs2') by lia.
    unfold N.
    rewrite <- app_length.
    transitivity (length (map fst (nsigs2' ++ nsigs1))).
    1: now rewrite -> map_length.
    apply NoDup_incl_length.
    + rewrite -> map_app.
      apply NoDup_app.
      * subst nsigs2'.
        apply valid_cert_nodup_implies_sender_nodup with (v:=v2).
        --now apply Forall_filter.
        --now apply NoDup_filter.
      * now apply valid_cert_nodup_implies_sender_nodup with (v:=v1).
      * (* show disjoint of nsigs1 and nsigs2' *)
        intros nn ? Hin1' Hin2' <-.
        rewrite -> in_map_iff in Hin1'.
        destruct Hin1' as ((nn', signn) & Htmp & Hin1').
        simpl in Htmp.
        subst nn' nsigs2'.
        apply filter_In in Hin1'.
        simpl in Hin1'.
        now destruct (in_dec Address_eqdec nn (map fst nsigs1)).
    + hnf.
      intros nb' Hin'.
      rewrite -> map_app, in_app_iff in Hin'.
      unfold certificate_valid in Hcert_valid1, Hcert_valid2.
      rewrite -> Forall_forall in Hcert_valid1, Hcert_valid2.
      destruct Hin' as [ Hin' | Hin' ].
      1: subst nsigs2'.
      all: apply in_map_iff in Hin'.
      all: destruct Hin' as ((nb'', sigb') & Htmp & Hin').
      all: simpl in Htmp.
      all: subst nb''.
      * apply filter_In, proj1, Hcert_valid2 in Hin'.
        now simpl in Hin'.
      * apply Hcert_valid1 in Hin'.
        now simpl in Hin'.
Qed.

Section Proof_of_Agreement.

  (*
  Definition has_consensus (stmap : StateMap) :=
    exists v : Value, Forall (fun n => if is_byz n then True 
      else (stmap n).(conf) -> (stmap n).(submitted_value) = Some v) valid_nodes.
  *)

  Definition consensus_broken (stmap : StateMap) :=
    exists n1 n2 v1 v2, 
      n1 <> n2 /\
      valid_node n1 /\
      valid_node n2 /\
      is_byz n1 = false /\
      is_byz n2 = false /\
      v1 <> v2 /\
      (stmap n1).(submitted_value) = Some v1 /\
      (stmap n2).(submitted_value) = Some v2 /\
      (stmap n1).(conf) /\
      (stmap n2).(conf).

  (* proof by reducing to absurd, using "if a node behaves like a Byzantine node then it is"
     still, that message is possibly not sent by itself, due to key sharing *)

  Lemma agreement w (Hinv : invariant w) (H_byz_minor : num_byz < N - (t0 + t0)) :
    consensus_broken (localState w) -> False.
  Proof.
    intros (n1 & n2 & v1 & v2 & Hnneq & Hn1valid & Hn2valid & H_n1_nonbyz & H_n2_nonbyz &
      Hvneq & Hn1v1 & Hn2v2 & Hn1conf & Hn2conf).
    pose proof (coh _ Hinv) as Hcoh.
    destruct_localState w n1 as_ conf1 ov1 from1 lsigs1 sigs1 rlcerts1 rcerts1 buffer1 eqn_ En1.
    destruct_localState w n2 as_ conf2 ov2 from2 lsigs2 sigs2 rlcerts2 rcerts2 buffer2 eqn_ En2.
    simpl_state.
    destruct conf1, conf2; try eqsolve.
    subst ov1 ov2.
    (* get to know the size of sigs *)
    pose proof Hinv as (_, Hnodeinv, _).
    pose proof (Hnodeinv n1 H_n1_nonbyz) as Hnodeinv1.
    pose proof (Hnodeinv n2 H_n2_nonbyz) as Hnodeinv2.
    unfold holds in Hnodeinv1, Hnodeinv2.
    rewrite -> En1 in Hnodeinv1.
    rewrite -> En2 in Hnodeinv2.
    destruct Hnodeinv1 as (Hcoll_trace1, _, _, _, _, _, ((Hsize1 & Hsize1'), Hconf_size1, Hfrom_nodup1, _, _, Hcoll_valid1, _)).
    destruct Hnodeinv2 as (Hcoll_trace2, _, _, _, _, _, ((Hsize2 & Hsize2'), Hconf_size2, Hfrom_nodup2, _, _, Hcoll_valid2, _)).
    simpl_state.
    simpl in Hcoll_trace1, Hcoll_trace2, Hconf_size1, Hconf_size2, Hcoll_valid1, Hcoll_valid2.
    (* get to know the size of quorums *)
    destruct Hcoll_valid1 as (Ev1 & _ & Hcert_valid1), Hcoll_valid2 as (Ev2 & _ & Hcert_valid2).
    unfold zip_from_sigs in Hcert_valid1, Hcert_valid2.
    simpl_state.
    epose proof (conflicting_cert_quorum_size v1 v2 (combine from1 sigs1) (combine from2 sigs2)
      Hcert_valid1 (NoDup_combine_l from1 sigs1 Hfrom_nodup1) ?[Goalq1] 
      Hcert_valid2 (NoDup_combine_l from2 sigs2 Hfrom_nodup2) ?[Goalq2]) as Hsize.
    [Goalq1]: rewrite -> combine_length; lia.
    [Goalq2]: rewrite -> combine_length; lia.
    rewrite <- map_length with (f:=fst), -> combine_map_fst in Hsize.
    2: assumption.
    pose proof (filter_compose fst (fun n' => in_dec Address_eqdec n' from1) (combine from2 sigs2)) as Htmp.
    simpl in Htmp.
    rewrite <- Htmp, -> combine_map_fst in Hsize.
    2: assumption.
    clear Htmp.
    assert (Forall is_byz (filter (fun n' => in_dec Address_eqdec n' from1) from2)) as Hbyz.
    {
      (* trace back *)
      apply Forall_forall.
      intros n (Hin2 & Hin1')%filter_In.
      unfold is_left in Hin1'.
      destruct (in_dec Address_eqdec n from1) as [ Hin1 | ]; try discriminate.
      eapply behave_byz_is_byz.
      1: apply (psent_inv _ Hinv).
      pose proof (zip_aux_pre _ _ Hsize1' _ Hin1) as (sig1 & Hin1_nsig).
      pose proof (zip_aux_pre _ _ Hsize2' _ Hin2) as (sig2 & Hin2_nsig).
      pose proof (zip_aux _ _ _ Hsize1 Hsize1' _ _ Hin1_nsig) as (lsig1 & Hin1_submit).
      pose proof (zip_aux _ _ _ Hsize2 Hsize2' _ _ Hin2_nsig) as (lsig2 & Hin2_submit).
      unfold zip_from_lsigs_sigs in *.
      simpl_state.
      apply Hcoll_trace1 in Hin1_submit.
      apply Hcoll_trace2 in Hin2_submit.
      hnf.
      exists v1, v2, sig1, sig2, lsig1, lsig2, n1, n2.
      intuition.
    }
    assert (length (filter (fun n' => in_dec Address_eqdec n' from1) from2) <= num_byz) as Hgoal.
    {
      unfold num_byz.
      apply NoDup_incl_length.
      - now apply NoDup_filter.
      - intros n Hin.
        eapply Forall_forall with (x:=n) in Hbyz; try assumption.
        pose proof (byz_is_valid _ Hbyz) as Hvalid.
        now apply filter_In.
    }
    (* now simple math *)
    lia.
  Qed.

End Proof_of_Agreement.

Lemma conflicting_cert_quorum_in_proof rcerts v1 v2 nsigs1 nsigs2
  (Hvneq : v1 <> v2)
  (Hin1 : In (v1, nsigs1) rcerts)
  (Hin2 : In (v2, nsigs2) rcerts) 
  (Hcert_valid1 : certificate_valid v1 nsigs1)
  (Hcert_valid2 : certificate_valid v2 nsigs2) :
  incl (filter (fun nsig => In_dec Address_eqdec (fst nsig) (map fst nsigs1)) nsigs2) 
    (map (fun nn => (nn, sign v2 (key_map nn))) (genproof rcerts)).
Proof.
    + hnf.
      intros (nb', sigb') Hin'.
      apply filter_In in Hin'.
      simpl in Hin'.
      destruct Hin' as (Hin2' & Htmp).
      destruct (in_dec Address_eqdec nb' (map fst nsigs1)) as [ Hin1' | ].
      2: eqsolve.
      clear Htmp.
      pose proof Hin2' as Hin2''.
      eapply valid_cert_valid_sig in Hin2'; eauto.
      subst sigb'.
      eapply valid_cert_sender_in in Hin1'; eauto.
      (* now *)
      match goal with |- In ?tp (map ?f _) => change tp with (f nb') end.
      apply in_map.
      destruct genproof_correct as (Hgp, _).
      apply Hgp.
      exists v1, v2, (sign v1 (key_map nb')), (sign v2 (key_map nb')), nsigs1, nsigs2.
      intuition.
Qed.

Lemma reachable_inv_2 w sched (H_w_reachable : reachable sched w) :
  invariant_2 w.
Proof.
  induction H_w_reachable as [ | q w w' Hstep sched H_w_reachable IH ].
  - apply inv_2_init.
  - pose proof (reachable_inv _ _ H_w_reachable) as Hinv.
    now apply inv_2_step in Hstep.
Qed.

(*
Lemma accountability w (Hinv : invariant w) (Hinv2 : invariant_2 w)
  n1 (H_n1_nonbyz : is_byz n1 = false) (Hn1valid : valid_node n1)
  n2 (H_n2_nonbyz : is_byz n2 = false) (Hn2valid : valid_node n2)
  (Hnneq : n1 <> n2)
  (Hconf1 : conf (localState w n1))
  (Hconf2 : conf (localState w n2))
  (Hvneq : fst (cert (localState w n1)) <> fst (cert (localState w n2)))
  (Heventual : Forall (fun p => if (is_byz (src p)) || (is_byz (dst p)) then True else consumed p) (sentMsgs w)) :
  exists byzs : list Address, 
    NoDup byzs /\
    N - (t0 + t0) <= length byzs /\
    Forall is_byz byzs /\
    (forall n, is_byz n = false -> valid_node n -> incl byzs (genproof (received_certs (localState w n)))).
Proof.
  pose proof (coh _ Hinv) as Hcoh.
  destruct_localState w n1 as_ conf1 cert1 rcerts1 eqn_ En1.
  destruct_localState w n2 as_ conf2 cert2 rcerts2 eqn_ En2.
  simpl_state.
  destruct cert1 as (v1, nsigs1), cert2 as (v2, nsigs2).
  simpl in Hvneq.
  (* get size of cert *)
  pose proof Hinv as (_, Hnodeinv, _).
  pose proof (Hnodeinv n1 H_n1_nonbyz) as Hnodeinv1.
  pose proof (Hnodeinv n2 H_n2_nonbyz) as Hnodeinv2.
  unfold holds in Hnodeinv1, Hnodeinv2.
  destruct Hnodeinv1 as (_, _, Hnodeinv_confsent1, (Hsize1, Hnsigs_nodup1, Hrcerts1, Hcert_valid1)), 
    Hnodeinv2 as (_, _, Hnodeinv_confsent2, (Hsize2, Hnsigs_nodup2, Hrcerts2, Hcert_valid2)).
  unfold is_true in Hconf1, Hconf2.
  subst conf1 conf2.
  rewrite -> En1 in Hrcerts1, Hcert_valid1, Hnodeinv_confsent1, Hsize1, Hnsigs_nodup1.
  rewrite -> En2 in Hrcerts2, Hcert_valid2, Hnodeinv_confsent2, Hsize2, Hnsigs_nodup2.
  simpl_state.
  cbn delta [fst snd] beta iota in *.
  specialize (Hnodeinv_confsent1 eq_refl).
  specialize (Hnodeinv_confsent2 eq_refl).
  (* show that the two conflicting full certs have been delivered to, say, n1 *)
  (* TODO although sending a message to a node itself is not a good modelling *)
  destruct Hinv2 as (Hpsentinv2).
  rewrite -> Forall_forall in Heventual, Hpsentinv2.
  assert (N - t0 <= length nsigs1) as Hsizele1 by lia.
  assert (N - t0 <= length nsigs2) as Hsizele2 by lia.
  assert (forall n, is_byz n = false -> valid_node n ->
    In (v1, nsigs1) (received_certs (localState w n))) as H_c1_in_rcerts.
  {
    intros n H_n_nonbyz Hnvalid.
    specialize (Hnodeinv_confsent1 _ Hnvalid) as (used & Hdeliver_from_n1).
    pose proof (Heventual _ Hdeliver_from_n1) as Htmp.
    simpl in Htmp.
    rewrite -> H_n1_nonbyz, -> H_n_nonbyz in Htmp.
    simpl in Htmp.
    unfold is_true in Htmp.
    subst used.
    apply Hpsentinv2 in Hdeliver_from_n1.
    simpl in Hdeliver_from_n1.
    now apply Hdeliver_from_n1.
  }
  assert (forall n, is_byz n = false -> valid_node n ->
    In (v2, nsigs2) (received_certs (localState w n))) as H_c2_in_rcerts.
  {
    intros n H_n_nonbyz Hnvalid.
    specialize (Hnodeinv_confsent2 _ Hnvalid) as (used & Hdeliver_from_n2).
    pose proof (Heventual _ Hdeliver_from_n2) as Htmp.
    simpl in Htmp.
    rewrite -> H_n2_nonbyz, -> H_n_nonbyz in Htmp.
    simpl in Htmp.
    unfold is_true in Htmp.
    subst used.
    apply Hpsentinv2 in Hdeliver_from_n2.
    simpl in Hdeliver_from_n2.
    now apply Hdeliver_from_n2.
  }
  pose proof (H_c1_in_rcerts _ H_n1_nonbyz Hn1valid) as H_c1_in_rcerts_n1.
  pose proof (H_c2_in_rcerts _ H_n1_nonbyz Hn1valid) as H_c2_in_rcerts_n1.
  rewrite -> En1 in H_c1_in_rcerts_n1, H_c2_in_rcerts_n1.
  simpl_state.
  (* now, get the common proof shared by everyone *)
  remember (filter (fun nsig => In_dec Address_eqdec (fst nsig) (map fst nsigs1)) nsigs2) as nsigs12.
  exists (map fst nsigs12).
  assert (forall n, is_byz n = false -> valid_node n ->
    incl (map fst nsigs12) (genproof (received_certs (localState w n)))) as Hcommonproof.
  {
    intros n H_n_nonbyz Hnvalid nb Hinproof.
    subst nsigs12.
    rewrite -> in_map_iff in Hinproof.
    destruct Hinproof as ((nb', sigb') & Htmp & Hinproof).
    simpl in Htmp.
    subst nb'.
    eapply conflicting_cert_quorum_in_proof with (rcerts:=(received_certs (localState w n))) in Hinproof; eauto.
    rewrite -> in_map_iff in Hinproof.
    destruct Hinproof as (nb' & Htmp & Hinproof).
    now injection_pair Htmp.
  }
  intuition.
  - subst nsigs12.
    apply valid_cert_nodup_implies_sender_nodup with (v:=v2).
    + now apply Forall_filter.
    + now apply NoDup_filter.
  - rewrite -> map_length.
    subst nsigs12.
    eapply conflicting_cert_quorum_size; eauto.
  - apply Forall_forall.
    intros nb Hinproof.
    eapply inv_sound_weak with (n:=n1); eauto.
    now apply Hcommonproof.
Qed.
*)

End Main_Proof.

End ACInvariant.
