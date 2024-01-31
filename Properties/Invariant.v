From Coq Require Import List Bool Lia ssrbool ListSet Permutation.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts.

Module Type ACInvariant 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns).

Import A T AC Ns ACN.

(* this is somewhat "pure" property (not related to psent) *)
(* HMM why there is not something like "if confirmed, then submitted"?
    it is a direct result of t0 < N, but is it good doing so? *)
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

(* FIXME: I remember somewhere below uses this. where? *)
Fact confirmed_then_submitted st (H : node_coh st) :
  st.(conf) -> st.(submitted_value).
Proof.
  destruct H as (_, H1, _, _, _, H2, _).
  intros E.
  rewrite E in H1.
  destruct (submitted_value st); auto.
  rewrite H2 in H1.
  pose proof t0_lt_N.
  simpl in H1.
  lia.
Qed.

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
  inv_conf_confmsg: 
    match st.(submitted_value) with
    | Some v => st.(conf) -> lightcert_conflict_check st.(received_lightcerts) ->
      forall n, valid_node n -> 
        exists used, In (mkP st.(id) n (ConfirmMsg (v, zip_from_sigs st)) used) psent
    | None => True
    end;
  (* have to guarantee that the messages in the buffer are already delivered *)
  inv_buffer_received: 
    Forall (fun nmsg => In (mkP (fst nmsg) st.(id) (snd nmsg) true) psent) st.(msg_buffer);
  inv_node_coh: node_coh st
}.

Fact valid_cert_valid_senders v nsigs
  (Hcert_valid : certificate_valid v nsigs) : incl (map fst nsigs) valid_nodes.
Proof.
  hnf in Hcert_valid.
  induction Hcert_valid as [ | (n, sig) nsigs (Hv & _) HH IH ]; hnf; simpl; auto.
  1: intros ? [].
  intros n' [ <- | Hin ]; auto.
Qed.

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
    (* TODO maybe also require valid_node n to make things look better *)
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
  | H : context[let: (_, _) := procMsg ?st ?nsrc ?msg in _] |- _ => 
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
    (* (Hboth_check : lightcert_conflict_check st.(received_lightcerts) -> lightcert_conflict_check rlcerts) : *)
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

Lemma In_consume_iff_by_msgdiff psent p p' (Hdiff : msg p <> msg p') :
  In p psent <-> In p (consume p' psent).
Proof.
  destruct p, p'.
  simpl in Hdiff |- *.
  split.
  - intros H.
    right.
    apply in_in_remove; try eqsolve.
  - intros [ | H ]; try eqsolve.
    now apply in_remove in H.
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
    destruct Hnodeinv as (_, Hnodeinv, _, _, _, _, _, _).
    specialize (Hnodeinv lc Hin_rlcerts).
    simpl in Hnodeinv.
    destruct Hnodeinv as (src & H).
    exists src.
    eapply In_psent_mnt'; eauto.
  - intros c Hin_rcerts.
    destruct Hnodeinv as (_, _, Hnodeinv, _, _, _, _, _).
    specialize (Hnodeinv c Hin_rcerts).
    simpl in Hnodeinv.
    destruct Hnodeinv as (src & H).
    exists src.
    eapply In_psent_mnt'; eauto.
  - destruct ov as [ v | ]; auto.
    destruct Hnodeinv as (_, _, _, Hnodeinv, _, _, _, _).
    simpl_state.
    simpl in Hnodeinv.
    intros n0 Hn0valid.
    specialize (Hnodeinv _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - destruct ov as [ v | ]; auto.
    destruct Hnodeinv as (_, _, _, _, Hnodeinv, _, _, _).
    simpl_state.
    intros -> n0 Hn0valid.
    specialize (Hnodeinv eq_refl _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - destruct ov as [ v | ]; auto.
    destruct Hnodeinv as (_, _, _, _, _, Hnodeinv, _, _).
    simpl_state.
    intros -> Hcheck n0 Hn0valid.
    specialize (Hnodeinv eq_refl Hcheck _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - destruct Hnodeinv as (_, _, _, _, _, _, Hnodeinv, _).
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

(* FIXME: it seems at least we need such pure properties somewhere. is there any systematic way? *)

Fact procMsg_SubmitMsg_mixin st src v lsig sig :
  let: (st', _) := (procMsg st src (SubmitMsg v lsig sig)) in
  st'.(received_lightcerts) = st.(received_lightcerts) /\
  st'.(id) = st.(id) /\
  (st.(conf) -> st'.(conf)) /\
  st'.(submitted_value) = st.(submitted_value).
Proof with (try eqsolve; try (inversion E; subst; simpl in *; eqsolve)).
  destruct (procMsg st src (SubmitMsg v lsig sig)) as (st', ms) eqn:E.
  destruct st as (n, conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer).
  simpl in E |- *.
  destruct ov as [ vthis | ]...
  destruct (Value_eqdec v vthis)...
  destruct (verify v sig src)...
  destruct (light_verify v lsig src)...
  destruct conf...
Qed.

(* generic reestablishment *)

Lemma inv_preserve_routine_check w (H : invariant w)
  n (H_n_nonbyz : is_byz n = false) (Hvalid : valid_node n) :
  invariant (mkW (localState w) (routine_check (localState w n) ++ sentMsgs w)).
Proof with basic_solver.
  pose proof H as (Hcoh, _, _).
  destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
  eapply inv_preserve_01.
  1: reflexivity.
  2: rewrite_w_expand w in_ H; apply H.
  eexists.
  split; [ apply PsentEq | ].
  split...
  intros p Hin_app Hnotin.
  rewrite -> in_app_iff in Hin_app.
  destruct Hin_app as [ Hin | Hin ]...
  clear Hnotin.
  unfold routine_check, zip_from_sigs in Hin.
  simpl_state.
  destruct ov as [ vthis | ], conf, (lightcert_conflict_check rlcerts) eqn:EE; simpl in Hin...
  apply In_broadcast in Hin.
  destruct Hin as (dst0 & HH & ->).
  simpl.
  rewrite H_n_nonbyz, En.
  now simpl_state.
Qed.

(* FIXME: much much ad-hoc; the reason for using this is that we do not have something like "a hole in invariant ..."; 
    but possibly this approach will be used when we have a better reasoning framework?
    e.g., when we can freely bundle/unbundle a set of invariant clauses? *)

Lemma inv_deliver_step_submit_pre w (H : invariant w)
  (* FIXME: add more conditions to make this easier? *)
  p v lsig sig (Emsg : msg p = SubmitMsg v lsig sig)
  w_ (E : let: (st', ms) := procMsg (localState w (dst p)) (src p) (msg p) in
      (* retract trick *)
      w_ = mkW (upd (dst p) (node_upd_rlcerts st' nil) (localState w))
               ((consume p (sentMsgs w)) ++ ms)) (H_ : invariant w_)
  w' (Hstep : system_step (Deliver p) w w') : invariant w'.
Proof with basic_solver.
  inversion Hstep as [ 
    | p' Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq
    | | | | ]; try discriminate.
  injection Hq as <-.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  subst msg.
  unfold procMsgWithCheck in Heq.
  destruct_procMsg as_ st' ms eqn_ Epm.
  (* TODO Coh is tedious! since we do not know that procMsg does not change id, which requires proof *)
  pose proof (coh _ H_) as Hcoh.
  rewrite_w_expand w_ in_ Hcoh.
  eapply upd_id_intact_preserve_Coh with (n:=dst) (st':=st') in Hcoh...
  2:{
    subst w_.
    simpl.
    unfold upd.
    destruct (Address_eqdec dst dst), st'...
  }
  rewrite E in Hcoh at 1.
  simpl localState in Hcoh.
  eapply stmap_pointwise_eq_preserve_Coh with (stmap':=upd dst st' (localState w)) in Hcoh.
  2:{
    intros x.
    unfold upd.
    destruct (Address_eqdec dst x)...
  }
  eapply Coh_psent_irrelevant in Hcoh.
  rewrite <- Heq in Hcoh.
  destruct_localState w' dst as_ conf_dst ov_dst from_dst lsigs_dst sigs_dst 
    rlcerts_dst rcerts_dst buffer_dst eqn_ Es.
  rewrite Heq in Es.
  simpl in Es.
  unfold upd in Es.
  destruct (Address_eqdec dst dst)...
  (* TODO still brute force ... *)
  subst w' w_.
  (* prepare *)
  match goal with |- _ (mkW _ (?la ++ ?lb ++ ?lc)) =>
    assert (forall p0, In p0 (la ++ lb ++ lc) <-> In p0 (la ++ lc) \/ In p0 lb) as Htmp 
    by (intros; rewrite ! in_app_iff; tauto) end.
  constructor...
  - intros n H_n_nonbyz.
    pose proof H as (_, Hnodeinv_ori, _).
    pose proof H_ as (_, Hnodeinv, _).
    specialize (Hnodeinv _ Hnonbyz).
    specialize (Hnodeinv_ori _ Hnonbyz).
    epose proof (procMsg_SubmitMsg_mixin _ _ _ _ _) as Hit.
    rewrite Epm in Hit.
    apply proj1 in Hit.
    unfold holds, upd in Hnodeinv, Hnodeinv_ori |- *.
    cbn delta -[consume] iota beta in Hnodeinv |- *.
    destruct (Address_eqdec dst n) as [ -> | Hnneq ] eqn:Edec.
    2:{
      eapply psent_mnt_preserve_node_invariant.
      1: eapply PsentLe with (psent1:=(sentMsgs w)) (psent2:=(consume p (sentMsgs w)))...
      now apply H.
    }
    rewrite Edec in Hnodeinv.
    rewrite Es at 2.
    rewrite Es in Hnodeinv.
    cbn delta -[consume] iota beta in Hnodeinv.
    destruct Hnodeinv_ori as (_, Hrlcerts_trace, _, _, _, _, _, Hnodecoh_ori).
    destruct Hnodeinv as (Hcoll_trace, _, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, _, Hbuffer_recv, Hnodecoh).
    rewrite <- Hit, -> Es in Hrlcerts_trace.
    simpl_state.
    constructor; simpl_state.
    (* another brute force ... *)
    + destruct ov_dst as [ vthis | ]...
      cbn delta -[consume] iota beta.
      intros n0 lsig0 sig0 Hin.
      specialize (Hcoll_trace _ _ _ Hin).
      rewrite Htmp.
      now left.
    + (* interesting case *)
      intros lc Hin.
      specialize (Hrlcerts_trace lc Hin).
      destruct Hrlcerts_trace as (src0 & HH).
      rewrite (id_coh _ (coh _ H)) in HH.
      exists src0.
      rewrite ! in_app_iff.
      left.
      now apply In_consume'.
    + intros c Hin.
      specialize (Hrcerts_trace c Hin).
      destruct Hrcerts_trace as (src0 & HH).
      exists src0.
      rewrite Htmp.
      now left.
    + destruct ov_dst as [ vthis | ]...
      intros n0 Hn0valid.
      specialize (Hsubmit_sent n0 Hn0valid).
      destruct Hsubmit_sent as (used0 & HH).
      exists used0.
      rewrite Htmp.
      now left.
    + destruct ov_dst as [ vthis | ]...
      intros -> n0 Hn0valid .
      specialize (Hlcert_sent eq_refl n0 Hn0valid).
      destruct Hlcert_sent as (used0 & HH).
      exists used0.
      rewrite Htmp.
      now left.
    + (* interesting case *)
      destruct ov_dst as [ vthis | ]...
      intros -> Hcheck n0 Hn0valid.
      exists false.
      rewrite ! in_app_iff.
      right; left.
      unfold routine_check.
      rewrite Es, Hcheck.
      apply In_broadcast.
      eauto.
    + eapply Forall_impl.
      2: apply Hbuffer_recv.
      cbn beta.
      intros.
      rewrite Htmp.
      now left.
    + constructor; simpl_state; try apply Hnodecoh.
      (* interesting case *)
      intros.
      apply Hnodecoh_ori.
      now rewrite <- Hit, Es.
  - cbn delta -[consume] iota beta.
    apply psent_invariant_by_extend with (psent:=(consume p (sentMsgs w) ++ ms)).
    + eexists.
      split; [ apply PsentEq | ].
      split; [ hnf; intros ?; rewrite Htmp; tauto | ].
      intros p0 [ | Hin ]%Htmp Hnotin...
      unfold routine_check in Hin.
      rewrite Es in Hin.
      destruct ov_dst as [ vthis | ], conf_dst, (lightcert_conflict_check rlcerts_dst) eqn:?.
      all: simpl in Hin...
      apply In_broadcast in Hin.
      destruct Hin as (dst0 & HH & ->).
      simpl.
      rewrite Hnonbyz, Es.
      unfold upd.
      destruct (Address_eqdec dst dst)...
    + eapply state_mnt_preserve_psent_invariant with (n:=dst).
      3: apply H_.
      1: simpl; apply StateRLCertsMnt with (rlcerts:=rlcerts_dst).
      1: subst st'; unfold upd; destruct (Address_eqdec dst dst); simpl; hnf; simpl; intros ?...
      simpl.
      intros n.
      unfold upd.
      destruct (Address_eqdec dst n)...
      destruct (Address_eqdec dst dst)...
      now subst st'.
Qed.

Lemma inv_deliver_step_lightconfirm_pre w (H : invariant w)
  p v cs (Emsg : msg p = LightConfirmMsg (v, cs))
  (Edecide1 : isSome ((localState w (dst p)).(submitted_value)))
  (Edecide2 : (localState w (dst p)).(conf))
  (Edecide3 : combined_verify v cs)
  (Hcheck : lightcert_conflict_check (localState w (dst p)).(received_lightcerts) = false)
  (Hcheck' : lightcert_conflict_check ((v, cs) :: (localState w (dst p)).(received_lightcerts)) = true)
  w_ (E : let: (st', ms) := procMsg (localState w (dst p)) (src p) (msg p) in
      (* retract trick *)
      w_ = mkW (upd (dst p) (node_upd_rlcerts st' (localState w (dst p)).(received_lightcerts)) (localState w))
               ((consume p (sentMsgs w)) ++ ms)) (H_ : invariant w_)
  w' (Hstep : system_step (Deliver p) w w') : invariant w'.
Proof with basic_solver.
  pose proof H as (Hcoh, _, _).
  inversion Hstep as [ 
    | p' Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq
    | | | | ]; try discriminate.
  injection Hq as <-.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  subst msg.
  unfold procMsgWithCheck in Heq.
  destruct_procMsg as_ st' ms eqn_ Epm.
  destruct_localState w dst as_ conf_dst ov_dst from_dst lsigs_dst sigs_dst 
    rlcerts_dst rcerts_dst buffer_dst eqn_ Es.
  simpl in Epm.
  rewrite Edecide3 in Epm.
  injection_pair Epm.
  simpl_state.
  simpl node_upd_rlcerts in *.
  rewrite app_nil_r in *.
  unfold routine_check in Heq.
  destruct ov_dst, conf_dst...
  setoid_rewrite Hcheck' in Heq.
  subst w_ w'.
  constructor.
  - apply upd_id_intact_preserve_Coh...
    + now rewrite Es.
    + eapply Coh_psent_irrelevant.
      rewrite_w_expand w in_ Hcoh.
      apply Hcoh.
  - intros n H_n_nonbyz.
    pose proof H_ as (_, Hnodeinv, _).
    specialize (Hnodeinv _ Hnonbyz).
    unfold holds, upd in Hnodeinv |- *.
    cbn delta -[consume] iota beta in Hnodeinv |- *.
    destruct (Address_eqdec dst n) as [ -> | Hnneq ] eqn:Edec.
    2:{
      eapply psent_mnt_preserve_node_invariant.
      1: eapply PsentLe with (psent1:=(sentMsgs w)) (psent2:=(consume p (sentMsgs w)))...
      now apply H.
    }
    rewrite Edec in Hnodeinv.
    destruct Hnodeinv as (Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, _, Hbuffer_recv, Hnodecoh).
    simpl_state.
    constructor; simpl_state; cbn match in *.
    (* another brute force ... *)
    + intros n0 lsig0 sig0 Hin.
      specialize (Hcoll_trace _ _ _ Hin).
      rewrite in_app_iff...
    + (* interesting case *)
      cbn delta -[consume] iota beta.
      intros lc [ <- | Hin ].
      * subst p.
        simpl.
        eauto.
      * specialize (Hrlcerts_trace _ Hin).
        destruct Hrlcerts_trace as (src0 & HH).
        exists src0.
        rewrite in_app_iff...
    + intros c Hin.
      specialize (Hrcerts_trace c Hin).
      destruct Hrcerts_trace as (src0 & HH).
      exists src0.
      rewrite in_app_iff...
    + intros n0 Hn0valid.
      specialize (Hsubmit_sent n0 Hn0valid).
      destruct Hsubmit_sent as (used0 & HH).
      exists used0.
      rewrite in_app_iff...
    + intros _ n0 Hn0valid .
      specialize (Hlcert_sent eq_refl n0 Hn0valid).
      destruct Hlcert_sent as (used0 & HH).
      exists used0.
      rewrite in_app_iff...
    + (* interesting case *)
      intros _ _ n0 Hn0valid.
      exists false.
      rewrite in_app_iff.
      right.
      apply In_broadcast.
      eauto.
    + eapply Forall_impl.
      2: apply Hbuffer_recv.
      cbn beta.
      intros.
      rewrite in_app_iff...
    + constructor; simpl_state; try apply Hnodecoh.
      (* interesting case *)
      simpl.
      intros ? ? [ HH | Hin ].
      * now injection_pair HH.
      * now apply Hnodecoh.
  - pose proof H_ as (_, _, Hpsentinv).
    cbn delta -[consume] iota beta in Hpsentinv |- *.
    hnf in Hpsentinv |- *.
    rewrite psent_invariant_viewchange in Hpsentinv |- *.
    setoid_rewrite in_app_iff.
    intros p0 [ Hin | (dst0 & HH & ->)%In_broadcast ].
    + specialize (Hpsentinv _ Hin).
      destruct p0 as (src0, dst0, msg0, used0).
      destruct msg0 as [ vv lsig0 sig0 | lc0 | c0 ].
      all: cbn delta -[consume] iota beta in Hpsentinv |- *.
      all: unfold upd in Hpsentinv |- *; destruct (Address_eqdec dst src0) as [ <- | ]...
      all: simpl_state; try rewrite Hnonbyz in *...
      all: destruct (is_byz src0) eqn:?...
      * hnf in Hpsentinv |- *.
        intros Hq.
        specialize (Hpsentinv Hq).
        eapply psent_mnt_preserve_lcert_correct.
        2: apply Hpsentinv.
        apply PsentLe with (psent2:=(consume p (sentMsgs w)))...
      * eapply psent_mnt_preserve_cert_correct.
        2: apply Hpsentinv.
        apply PsentLe with (psent2:=(consume p (sentMsgs w)))...
    + simpl.
      unfold upd.
      destruct (Address_eqdec dst dst)...
      simpl_state.
      rewrite Hnonbyz...
Qed.

Lemma inv_deliver_step_pre w p (H : invariant w)
  (Hpin : In p (sentMsgs w)) (Hsrcvalid : valid_node (src p))
  (Hnvalid : valid_node (dst p)) (Hnonbyz : is_byz (dst p) = false)
  w' (E : let: st := localState w (dst p) in
    let: (st', ms) := procMsg (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) 
        (match msg p with SubmitMsg _ _ _ =>
          (match st'.(submitted_value) with Some _ =>
            if st.(conf) 
            then st'
            else (if st'.(conf)
                  then (if lightcert_conflict_check (st'.(received_lightcerts))
                        then (node_upd_rlcerts st' nil)
                        else st')
                  else st')
          | None => st' end) 
        | LightConfirmMsg (v, cs) => 
          (match st'.(submitted_value) with Some _ =>
            if st'.(conf) 
            then (if combined_verify v cs
                  then (if lightcert_conflict_check (st'.(received_lightcerts))
                        then (if lightcert_conflict_check (st.(received_lightcerts))
                                then st'
                                else (node_upd_rlcerts st' (st.(received_lightcerts))))
                        else st')
                  else st')
            else st'
          | None => st' end)
        | _ => st' end) (localState w))
      ((consume p (sentMsgs w)) ++ ms)) : invariant w'.
Proof with basic_solver.
  (* intros H Hstep.  *)
  pose proof (coh _ H) as Hcoh.
  (* inversion Hstep as [ 
    | p' Hq Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | | | | ]; try discriminate.
  injection Hq as <-. *)
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
    destruct Hconf as (Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, Hcert_sent, Hbuffer_recv,
      ((Hsize1 & Hsize2), Hconf, Hfrom_nodup, Hrlcerts, Hrcerts, Hcoll_valid, Hbuffer)).
    simpl in Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, Hsubmit_sent, Hlcert_sent, Hcert_sent, Hbuffer_recv, 
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
        simpl_state.
        cbn match.
        simpl node_upd_rlcerts.
        match goal with |- context[(Node ?oa ?ob ?oc ?od ?oe ?og _ ?oi ?ok)] =>
          replace (upd dst _ (localState w)) with (upd dst (Node oa ob oc od oe og 
            (if lightcert_conflict_check rlcerts_dst then nil else rlcerts_dst) oi ok) (localState w)) end.
        2: f_equal; now destruct (lightcert_conflict_check rlcerts_dst).
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
        --eapply upd_id_intact_preserve_Coh; eauto.
          ++now rewrite -> Edst.
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
            destruct (lightcert_conflict_check rlcerts_dst); simpl in Hin...
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
          ++(* making dilemma? *)
            cbn match.
            intros _ Hcheck n0 Hn0valid.
            destruct (lightcert_conflict_check rlcerts_dst) eqn:?...
            apply lightcert_conflict_check_correct in Hcheck.
            now destruct Hcheck as (? & ? & ? & ? & ? & ? & ?).
          ++rewrite -> Forall_forall in Hbuffer_recv |- *.
            intros.
            apply in_app_iff, or_introl, In_consume'...
          ++constructor; simpl...
            all: destruct (lightcert_conflict_check rlcerts_dst)...
            all: unfold zip_from_lsigs, zip_from_sigs.
            all: simpl.
            all: intuition constructor; simpl...
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
          (* interesting *)
          rewrite <- Edst in Hsmnt.
          eapply state_mnt_preserve_psent_invariant in Hsmnt.
          2: reflexivity.
          2: apply H.
          (* resort to the original inv, and reach a contradiction *)
          destruct H as (_, _, H).
          hnf in H, Hsmnt |- *.
          rewrite psent_invariant_viewchange in H, Hsmnt |- *.
          intros p0 Hin0.
          specialize (Hsmnt _ Hin0).
          specialize (H _ Hin0).
          destruct p0 as (src0, dst0, msg0, used0), msg0 as [ v0 lsig0 sig0 | (v0, lc0) | (v0, nsigs0) ].
          all: simpl in H, Hsmnt |- *.
          all: unfold upd in H, Hsmnt |- *; destruct (Address_eqdec dst src0) as [ <- | ]...
          simpl_state.
          rewrite Hnonbyz in H, Hsmnt |- *.
          now rewrite Edst in H.
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
      rewrite Edst.
      simpl_state.
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
        rewrite <- Edst in Epm |- *.
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
        replace (upd dst _ (localState w)) with (upd dst (localState w dst) (localState w))
          by (rewrite Edst; destruct conf_dst; reflexivity).
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
      simpl_state.
      simpl node_upd_rlcerts.
      (*
      match goal with |- context[(Node ?oa ?ob ?oc ?od ?oe ?og _ ?oi ?ok)] =>
        replace (upd dst _ (localState w)) with (upd dst (Node oa ob oc od oe og 
          (if (lightcert_conflict_check ((v, cs) :: rlcerts_dst))
            then (if (lightcert_conflict_check rlcerts_dst)
                  then ((v, cs) :: rlcerts_dst)
                  else rlcerts_dst)
            else ((v, cs) :: rlcerts_dst)) oi ok) (localState w)) end.
      (* TODO destruct does not work well here! why? is this a problem related with record? *)
      2: f_equal; destruct (lightcert_conflict_check (_ :: rlcerts_dst)) eqn:?.
      2: destruct (lightcert_conflict_check rlcerts_dst) eqn:?.
      2-4: f_equal; destruct (lightcert_conflict_check _) eqn:?...
      (* eapply inv_preserve_00 with (psent:=(sentMsgs w))... *)
      *)
      destruct (match ov_dst with Some _ => 
        if conf_dst 
        then (if lightcert_conflict_check ((v, cs) :: rlcerts_dst)
              then (if lightcert_conflict_check rlcerts_dst
                    then false
                    else true)
              else false)
        else false
      | _ => false end) eqn:Edecide2.
      * destruct ov_dst, conf_dst, (lightcert_conflict_check ((v, cs) :: rlcerts_dst)) eqn:Hcheck', 
          (lightcert_conflict_check rlcerts_dst) eqn:Hcheck...
        setoid_rewrite -> Hcheck'. (* ! *)
        rewrite <- Edst.
        eapply inv_preserve_00.
        --apply upd_same_pointwise_eq.
        --now apply PsentEq'.
        --now rewrite_w_expand w in_ H.
      * match goal with |- context[(Node ?oa ?ob ?oc ?od ?oe ?og _ ?oi ?ok)] =>
          replace (upd dst _ (localState w)) with (upd dst (Node oa ob oc od oe og 
            ((v, cs) :: rlcerts_dst) oi ok) (localState w)) end.
        2: destruct ov_dst, conf_dst, (lightcert_conflict_check ((v, cs) :: rlcerts_dst)) eqn:Hcheck', 
          (lightcert_conflict_check rlcerts_dst) eqn:Hcheck; 
          try setoid_rewrite Hcheck'; 
          try setoid_rewrite Hcheck...
        eapply inv_preserve_10...
        --match goal with
          |- state_mnt _ _ ?st => replace st with (node_upd_rlcerts (localState w dst) ((v, cs) :: rlcerts_dst))
          end.
          2: simpl; now rewrite -> Edst.
          apply StateRLCertsMnt.
          rewrite -> Edst.
          hnf.
          intuition.
        --destruct H as (_, Hnodeinv, _).
          specialize (Hnodeinv dst Hnonbyz).
          hnf in Hnodeinv.
          rewrite -> Edst in Hnodeinv.
          pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
          (* preserve these ? to make auto work *)
          destruct Hnodeinv as (?, ?, ?, ?, ?, Hlcert_sent, ?, (?, ?, ?, Hrlcerts, ?, ?, ?)).
          constructor; simpl_state.
          ++apply Hnodeinv'.
          ++simpl.
            destruct Hnodeinv' as (_, Hrlcerts_trace', _, _, _, _, _, _).
            intros (v0, cs0) [ Hin | Hin ].
            2: now apply Hrlcerts_trace' in Hin.
            injection_pair Hin.
            exists src.
            subst p.
            now left.
          ++apply Hnodeinv'.
          ++apply Hnodeinv'.
          ++apply Hnodeinv'.
          ++destruct ov_dst as [ vthis | ]...
            intros -> Hcheck' n Hvalid.
            rewrite Hcheck' in Edecide2.
            destruct (lightcert_conflict_check rlcerts_dst) eqn:Hcheck...
            specialize (Hlcert_sent eq_refl eq_refl _ Hvalid).
            destruct Hlcert_sent as (used0 & HH).
            exists used0.
            rewrite <- In_consume_iff_by_msgdiff...
            now subst p.
          ++apply Hnodeinv'.
          ++constructor...
            simpl.
            intros v0 cs0 [ Hpeq | ]...
        --eapply inv_preserve_00 with (psent:=(sentMsgs w))...
          now rewrite_w_expand w in_ H.
    + (* essentially no change *)
      injection_pair Epm.
      simpl_state.
      rewrite <- Edst.
      replace (upd dst _ _) with (upd dst (localState w dst) (localState w)) in |- *.
      2: destruct ov_dst, conf_dst; reflexivity.
      rewrite -> app_nil_r.
      eapply inv_preserve_00.
      * apply upd_same_pointwise_eq.
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
        destruct Hnodeinv as (?, ?, ?, ?, ?, ?, ?, (?, ?, ?, ?, Hrcerts, ?, ?)).
        constructor; simpl_state.
        --apply Hnodeinv'.
        --apply Hnodeinv'.
        --simpl.
          destruct Hnodeinv' as (_, _, Hrcerts_trace', _, _, _, _, _).
          intros (v0, nsigs0) [ Hin | Hin ].
          2: now apply Hrcerts_trace' in Hin.
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

Lemma inv_deliver_step w p (H : invariant w)
  w' (Hstep : system_step (Deliver p) w w') : invariant w'.
Proof with basic_solver.
  pose proof (coh _ H) as Hcoh.
  inversion Hstep as [ 
    | p' Hq Hpin Hsrcvalid Hnvalid Hnonbyz Heq 
    | | | | ]; try discriminate.
  injection Hq as <-.
  pose proof (inv_deliver_step_pre w p H Hpin Hsrcvalid Hnvalid Hnonbyz) as H_.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  unfold procMsgWithCheck in Heq.
  destruct_procMsg as_ st' ms eqn_ Epm.
  destruct_localState w dst as_ conf_dst ov_dst from_dst lsigs_dst sigs_dst 
    rlcerts_dst rcerts_dst buffer_dst eqn_ Edst.
  destruct st' as (n', conf', ov', from', lsigs', sigs', rlcerts', rcerts', buffer') eqn:Est'.
  specialize (H_ _ eq_refl).
  unfold routine_check in Heq.
  destruct msg as [ v ls s | (v, cs) | c ].
  - simpl_state.
    destruct ov' eqn:E1.
    2: now subst w'.
    destruct conf_dst eqn:E2.
    1:{
      (* TODO why this is not easy? *)
      epose proof (procMsg_SubmitMsg_mixin _ _ _ _ _) as Hit.
      rewrite Epm in Hit.
      simpl_state.
      destruct Hit as (-> & -> & Hit & <-).
      specialize (Hit eq_refl).
      hnf in Hit.
      subst conf'.
      subst w'.
      destruct (lightcert_conflict_check rlcerts_dst) eqn:E4.
      2: now simpl.
      (* still need 01 *)
      eapply inv_preserve_01.
      3: apply H_.
      1: reflexivity.
      eexists.
      split; [ apply PsentEq | ].
      split.
      1: hnf; intros ?; rewrite ! in_app_iff; tauto.
      intros p0 Hin_app Hnotin.
      rewrite -> ! in_app_iff in Hin_app.
      rewrite -> ! in_app_iff in Hnotin.
      destruct Hin_app as [ Hin | [ Hin | Hin ] ]...
      apply In_broadcast in Hin.
      destruct Hin as (dst0 & HH & ->).
      simpl.
      rewrite Hnonbyz.
      unfold upd.
      destruct (Address_eqdec dst dst)...
    }
    destruct conf' eqn:E3.
    2: now subst w'.
    destruct (lightcert_conflict_check rlcerts') eqn:E4.
    2: now subst w'.
    simpl node_upd_rlcerts in H_.
    pose proof (inv_deliver_step_submit_pre _ H p v ls s) as H__.
    rewrite Ep in H__.
    simpl_pkt.
    rewrite Edst, Epm in H__.
    specialize (H__ eq_refl _ eq_refl).
    rewrite <- Ep in H__.
    now apply H__.
  - simpl_state.
    destruct ov' eqn:E1.
    2: now subst w'.
    destruct conf' eqn:E2.
    2: now subst w'.
    simpl in Epm.
    destruct (combined_verify v cs) eqn:E3.
    2:{
      injection Epm as <-.
      subst w'.
      (* FIXME: the order is bad; having to repeat here! *)
      destruct (lightcert_conflict_check rlcerts') eqn:E4.
      2: now simpl.
      (* still need 01 *)
      eapply inv_preserve_01.
      3: apply H_.
      1: reflexivity.
      eexists.
      split; [ apply PsentEq | ].
      split.
      1: hnf; intros ?; rewrite ! in_app_iff; tauto.
      intros p0 Hin_app Hnotin.
      rewrite -> ! in_app_iff in Hin_app.
      rewrite -> ! in_app_iff in Hnotin.
      destruct Hin_app as [ Hin | [ Hin | Hin ] ]...
      apply In_broadcast in Hin.
      destruct Hin as (dst0 & HH & ->).
      simpl.
      rewrite Hnonbyz.
      unfold upd.
      destruct (Address_eqdec dst dst)...
    }
    destruct (lightcert_conflict_check rlcerts') eqn:E4.
    2: now subst w'.
    destruct (lightcert_conflict_check rlcerts_dst) eqn:E5.
    + subst w'.
      (* still need 01 *)
      eapply inv_preserve_01.
      3: apply H_.
      1: reflexivity.
      eexists.
      split; [ apply PsentEq | ].
      split.
      1: hnf; intros ?; rewrite ! in_app_iff; tauto.
      intros p0 Hin_app Hnotin.
      rewrite -> ! in_app_iff in Hin_app.
      rewrite -> ! in_app_iff in Hnotin.
      destruct Hin_app as [ Hin | [ Hin | Hin ] ]...
      apply In_broadcast in Hin.
      destruct Hin as (dst0 & HH & ->).
      assert (n' = dst) as -> by congruence.
      simpl.
      rewrite Hnonbyz.
      unfold upd.
      destruct (Address_eqdec dst dst)...
    + simpl node_upd_rlcerts in H_.
      pose proof (inv_deliver_step_lightconfirm_pre _ H p v cs) as H__.
      rewrite Ep in H__.
      simpl_pkt.
      rewrite Edst in H__.
      simpl_state.
      injection Epm as <-.
      subst.
      specialize (H__ eq_refl eq_refl eq_refl E3 E5 E4).
      simpl in H__.
      rewrite E3 in H__.
      specialize (H__ _ eq_refl).
      now apply H__.
  - now subst w'.
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
    destruct Hv as (_, _, _, _, _, _, _, (_, _, _, _, _, Hv, (Hbuffer1 & Hbuffer2))).
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
    destruct Hnodeinv as (Hcoll_trace, Hrlcerts_trace, Hrcerts_trace, _, _, _, Hbuffer_recv,
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
      destruct (procMsgWithCheck st_' src (SubmitMsg v ls s)) as (res1, res2) eqn:Eproc.
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
    eapply inv_internal_submit_step; eauto.
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

Fact procMsgWithCheck_sent_packets_are_fresh st src msg :
  forall p (Hin : In p (snd (procMsgWithCheck st src msg))), consumed p = false.
Proof with basic_solver.
  intros.
  pose proof (procMsg_sent_packets_are_fresh st src msg p) as Htmp.
  unfold procMsgWithCheck, routine_check in Hin.
  destruct (procMsg st src msg) as (st', ms) eqn:Epm.
  destruct st' as (n, conf, ov, from, lsigs, sigs, rlcerts, rcerts, buffer) eqn:Est.
  all: destruct msg; simpl in *...
  all: destruct ov, conf, (lightcert_conflict_check rlcerts)...
  all: rewrite in_app_iff in Hin; destruct Hin as [ Hin | Hin ]...
  all: apply In_broadcast in Hin; now destruct Hin as (? & ? & ->).
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
        destruct (procMsgWithCheck st_ src msg) as (st__, ps__) eqn:Epm'.
        injection_pair Estps.
        rewrite in_app_iff in Hin.
        destruct Hin as [ Hin | Hin ]...
        epose proof (procMsgWithCheck_sent_packets_are_fresh st_ src msg) as H.
        rewrite Epm' in H.
        simpl in H.
        now apply H.
    + apply In_broadcast in Hin.
      now destruct Hin as (? & ? & ->).
Qed.

Lemma inv_2_init : invariant_2 initWorld.
Proof with basic_solver.
  do 2 constructor.
Qed.

Lemma inv_2_deliver_step_pre w p (Hinv2 : invariant_2 w) (Hcoh : Coh w) 
  (Hpin : In p (sentMsgs w)) (Hsrcvalid : valid_node (src p))
  (Hnvalid : valid_node (dst p)) (Hnonbyz : is_byz (dst p) = false)
  w' (E : let: st := localState w (dst p) in
    let: (st', ms) := procMsg (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
      ((consume p (sentMsgs w)) ++ ms)) : invariant_2 w' /\ Coh w'. (* there is inevitably repetition for Coh proof *)
Proof with basic_solver.
  destruct Hinv2 as (Hpsentinv).
  pose proof Hpsentinv as Hpsentinv'.
  rewrite -> Forall_forall in Hpsentinv'.
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

Lemma inv_2_deliver_step w w' p 
  (Hinv2 : invariant_2 w) (Hcoh : Coh w) 
  (Hstep : system_step (Deliver p) w w') : invariant_2 w' /\ Coh w'. (* there is inevitably repetition for Coh proof *)
Proof.
  inversion Hstep as [ 
    | p' Hq Hpin Hsrcvalid Hnvalid Hnonbyz Heq 
    | | | | ]; try discriminate.
  injection Hq as <-.
  pose proof (inv_2_deliver_step_pre w p Hinv2 Hcoh Hpin Hsrcvalid Hnvalid Hnonbyz) as H_.
  destruct p as (src, dst, msg, used) eqn:Ep.
  simpl_pkt.
  rewrite <- Ep in *.
  unfold procMsgWithCheck in Heq.
  destruct_procMsg as_ st' ms eqn_ Epm.
  specialize (H_ _ eq_refl).
  assert (sentMsgs w' = consume p (sentMsgs w) ++ ms \/
    exists m0, sentMsgs w' = consume p (sentMsgs w) ++ (broadcast dst m0 ++ ms)) as Hdecide.
  {
    unfold routine_check in Heq.
    destruct st' as (n', conf', ov', from', lsigs', sigs', rlcerts', rcerts', buffer') eqn:Est'.
    (* TODO trick here *)
    pose proof (id_coh _ (proj2 H_) dst) as Htmp.
    unfold holds, upd in Htmp.
    simpl in Htmp.
    destruct (Address_eqdec dst dst); try eqsolve.
    simpl in Htmp.
    subst n'.
    destruct msg.
    3: subst w'; now left.
    all: destruct ov', conf', (lightcert_conflict_check rlcerts'); try solve [ subst w'; now left ].
    all: subst w'; simpl; right; eauto.
  }
  assert (localState w' = upd dst st' (localState w)) as EE by (destruct msg; simpl in Heq; now subst w').
  replace w' with (mkW (localState w') (sentMsgs w')) in |- * by now destruct w'.
  rewrite EE.
  split.
  - destruct Hdecide as [ -> | (m0 & ->) ].
    1: apply H_.
    eapply inv_2_by_extend_freshpkt.
    2: apply H_.
    intros p0.
    rewrite ! in_app_iff.
    intros [ Hin | [ Hin%In_broadcast | Hin ] ]; auto.
    destruct Hin as (? & ? & ->); auto.
  - eapply Coh_psent_irrelevant, H_.
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
  destruct Hv as (_, _, _, _, _, _, Hbuffer_recv, (_, _, _, _, _, Hv, (Hbuffer1 & Hbuffer2))).
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
        destruct (procMsgWithCheck st_' src (SubmitMsg v ls s)) as (res1, res2) eqn:Eproc.
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

Lemma system_trace_preserve_inv w l (Hinv : invariant w) (H : system_trace w l) :
  invariant (final_world w l).
Proof.
  induction l as [ | (q, w') l IH ] using rev_ind; auto.
  rewrite system_trace_app in H.
  simpl in H.
  unfold final_world.
  rewrite last_last.
  simpl.
  eapply inv_step.
  2: apply H.
  tauto.
Qed.

Lemma reachable_inv w (H_w_reachable : reachable w) :
  invariant w.
Proof.
  induction H_w_reachable as [ | q w w' Hstep H_w_reachable IH ].
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
  destruct Hnodeinv_n as (_, _, Hrcerts_trace, _, _, _, _, ((_ & Hsize2), _, _, _, Hrcerts, _, _)).
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
      destruct Hnodeinv as (Hcoll_trace, _, _, _, _, _, _, ((Hsize1' & Hsize2'), _, _, _, _, _, _)).
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

Lemma quorum_intersection ns1 ns2 
  (Hvalid1 : incl ns1 valid_nodes)
  (Hnsigs_nodup1 : NoDup ns1)
  (Hsize1 : N - t0 <= (length ns1))
  (Hvalid2 : incl ns2 valid_nodes)
  (Hnsigs_nodup2 : NoDup ns2)
  (Hsize2 : N - t0 <= (length ns2)) :
  (N - (t0 + t0)) <= length (filter (fun n => In_dec Address_eqdec n ns1) ns2). 
Proof.
  (* now show that: at least (2t0-N) distinct nodes are in culprit proof *)
  (* should partition only by the address since signs can be different for different values *)
  destruct (partition (fun n => In_dec Address_eqdec n ns1) ns2) as (ns12, ns2') eqn:Epar.
  epose proof (partition_filter _ ns2) as Htmp.
  rewrite -> Epar in Htmp.
  match type of Htmp with (?a, ?b) = (?c, ?d) => 
    assert (a = c) as Ens12 by eqsolve; 
    assert (b = d) as Ens2' by eqsolve
  end.
  clear Htmp.
  rewrite <- Ens12.
  assert (incl ns2' valid_nodes) as Hvalid2'.
  {
    hnf.
    intros a Htmp.
    apply Hvalid2.
    revert a Htmp.
    subst ns2'. 
    apply incl_filter.
  }
  (* maybe this part has been well formalized in other Coq libraries ... *)
    cut (((length ns2) - (length ns12)) + (length ns1) <= N).
    1: lia.
    pose proof Epar as Elengthpar.
    apply partition_length in Elengthpar.
    replace ((length ns2) - (length ns12)) with (length ns2') by lia.
    unfold N.
    rewrite <- app_length.
    apply NoDup_incl_length.
    + subst ns2'.
      apply NoDup_app; auto.
      * now apply NoDup_filter.
      * intros x y (Hin1' & HH)%filter_In Hin2' <-.
        now destruct (in_dec Address_eqdec x ns1).
    + now apply incl_app.
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
    (* get to know the size of froms *)
    pose proof Hinv as (_, Hnodeinv, _).
    pose proof (Hnodeinv n1 H_n1_nonbyz) as Hnodeinv1.
    pose proof (Hnodeinv n2 H_n2_nonbyz) as Hnodeinv2.
    unfold holds in Hnodeinv1, Hnodeinv2.
    rewrite -> En1 in Hnodeinv1.
    rewrite -> En2 in Hnodeinv2.
    destruct Hnodeinv1 as (Hcoll_trace1, _, _, _, _, _, _, ((Hsize1 & Hsize1'), Hconf_size1, Hfrom_nodup1, _, _, Hcoll_valid1, _)).
    destruct Hnodeinv2 as (Hcoll_trace2, _, _, _, _, _, _, ((Hsize2 & Hsize2'), Hconf_size2, Hfrom_nodup2, _, _, Hcoll_valid2, _)).
    simpl_state.
    simpl in Hcoll_trace1, Hcoll_trace2, Hconf_size1, Hconf_size2, Hcoll_valid1, Hcoll_valid2.
    (* get to know the size of quorums *)
    destruct Hcoll_valid1 as (Ev1 & _ & Hcert_valid1), Hcoll_valid2 as (Ev2 & _ & Hcert_valid2).
    unfold zip_from_sigs in Hcert_valid1, Hcert_valid2.
    simpl_state.
    (* FIXME: this is awkward! can we know the validity of from set only in this way? *)
    pose proof (valid_cert_valid_senders _ _ Hcert_valid1) as Hvalid1.
    pose proof (valid_cert_valid_senders _ _ Hcert_valid2) as Hvalid2.
    rewrite combine_map_fst in Hvalid1, Hvalid2; auto.
    assert ((N - (t0 + t0)) <= length (filter (fun n' : Address => in_dec Address_eqdec n' from1) from2)) as Hsize
      by (apply quorum_intersection; auto; try lia).
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
(*
Section Proof_of_Phase_Distinction.

  Hypothesis (H_byz_minor : num_byz < N - (t0 + t0)).

  (* FIXME: this check should be not defined again! now just for convenience *)
  Definition ready_to_broadcast_fullcerts (st : State) : bool :=
    let: Node n conf ov from lsigs sigs rlcerts rcerts buffer := st in
    match ov with 
    | Some vthis => 
      (* actually confirmation implies submission; but we need to use vthis so anyway *)
      if conf
      then lightcert_conflict_check rlcerts
      else false
    | None => false
    end
  .

  Lemma phase_distinct w (Hinv : invariant w) n (Hnvalid : valid_node n) (H_n_nonbyz : is_byz n = false) :
    ready_to_broadcast_fullcerts (localState w n) -> False.
  Proof.
    intros H.
    unfold ready_to_broadcast_fullcerts in H.
    pose proof Hinv as (Hcoh, Hnodeinv, Hpsentinv).
    destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    destruct ov, conf, (lightcert_conflict_check rlcerts) eqn:E; try discriminate.
    apply lightcert_conflict_check_correct in E.
    destruct E as (v1 & v2 & cs1 & cs2 & Hvneq & Hin1 & Hin2).
    pose proof (Hnodeinv _ H_n_nonbyz) as Htmp.
    hnf in Htmp.
    rewrite En in Htmp.
    destruct Htmp as (_, Hrlcerts_trace, _, _, _, _, _, (_, _, _, Hrlcerts, _, _, _)).
    simpl_state.
    (* directly prove that they must come from many *)
    pose proof (Hrlcerts_trace _ Hin1) as (n1 & Hsent1).
    pose proof (Hrlcerts_trace _ Hin2) as (n2 & Hsent2).
    hnf in Hpsentinv.
    rewrite psent_invariant_viewchange in Hpsentinv.
    pose proof (Hpsentinv _ Hsent1) as Hq1.
    pose proof (Hpsentinv _ Hsent2) as Hq2.
    simpl in Hq1, Hq2.
    unfold lcert_correct_threshold, lcert_correct, lightsig_seen_in_history in Hq1, Hq2.
    pose proof (Hrlcerts _ _ Hin1) as Hlcc1.
    pose proof Hlcc1 as (ns1 & Hnoudp1 & Hvalid1 & Hlen1 & E1)%combine_correct.
    pose proof (Hrlcerts _ _ Hin2) as Hlcc2.
    pose proof Hlcc2 as (ns2 & Hnoudp2 & Hvalid2 & Hlen2 & E2)%combine_correct.
    assert ((N - (t0 + t0)) <= length (filter (fun n' : Address => in_dec Address_eqdec n' ns1) ns2)) as Hsize
      by (apply quorum_intersection; auto; try lia).
    

    collected_lightsigs
    (* first know  *)

    combined_verify
    node_invariant
    lcert_correct
    lightsig_seen_in_history




End Proof_of_Phase_Distinction.
*)
Lemma conflicting_cert_quorum_in_proof rcerts v1 v2 nsigs1 nsigs2
  (Hvneq : v1 <> v2)
  (Hin1 : In (v1, nsigs1) rcerts)
  (Hin2 : In (v2, nsigs2) rcerts) 
  (Hcert_valid1 : certificate_valid v1 nsigs1)
  (Hcert_valid2 : certificate_valid v2 nsigs2) :
  incl (filter (fun n => In_dec Address_eqdec n (map fst nsigs1)) (map fst nsigs2)) 
    (genproof rcerts).
Proof.
    + hnf.
      intros nb' (Hin2' & Htmp)%filter_In.
      destruct (in_dec Address_eqdec nb' (map fst nsigs1)) as [ Hin1' | ]; try eqsolve.
      clear Htmp.
      pose proof Hin2' as Hin2''.
      eapply valid_cert_sender_in in Hin1', Hin2'; eauto.
      destruct genproof_correct as (Hgp, _).
      apply Hgp.
      exists v1, v2, (sign v1 (key_map nb')), (sign v2 (key_map nb')), nsigs1, nsigs2.
      intuition.
Qed.

Lemma reachable_inv_2 w (H_w_reachable : reachable w) :
  invariant_2 w.
Proof.
  induction H_w_reachable as [ | q w w' Hstep H_w_reachable IH ].
  - apply inv_2_init.
  - pose proof (reachable_inv _ H_w_reachable) as Hinv.
    now apply inv_2_step in Hstep.
Qed.

(* this is required by terminating convergence ... *)
(* TODO still, cumbersome! *)
(* HMM this belongs to a more general category of "persistent state"? 
    or, a more general invariant ... *)

Definition honest_node_submitted n v w :=
  valid_node n -> is_byz n = false -> (localState w n).(submitted_value) = Some v.

(* FIXME: explain why need an accompanying (invariant w) *)
Fact honest_node_submitted_is_invariant n v : is_invariant_step (fun w => invariant w /\ honest_node_submitted n v w).
Proof.
  hnf.
  intros q w_ w' (Hinv_ & Hst) Hstep.
  split.
  1: eapply inv_step; eauto.
  hnf in Hst |- *.
  intros Hnvalid H_n_nonbyz.
  specialize (Hst Hnvalid H_n_nonbyz).
  pose proof (coh _ Hinv_) as Hcoh.
  inversion Hstep as [ 
    | p Hq Hpin Hvalid Hsrcvalid Hnonbyz Heq 
    | n0 t Hq Hvalid H_n0_nonbyz Heq 
    | n0 dst v0 ls s Hq H_n_byz Heq 
    | n0 dst lc Hq H_n_byz Hcc Heq
    | n0 dst c Hq H_n_byz Hcc Heq ].
  all: subst q.
  1,4-6: now subst w'.
  - destruct p as (src, dst, msg, used) eqn:Ep.
    simpl_pkt.
    rewrite <- Ep in *.
    unfold procMsgWithCheck in Heq.
    destruct_procMsg as_ st' ms eqn_ Epm.
    assert (localState w' = upd dst st' (localState w_)) as -> by (destruct msg; now subst w').
    clear Heq.
    unfold upd.
    destruct (Address_eqdec dst n) as [ -> | ]; auto.
    destruct_localState w_ n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    destruct msg as [ v0 ls s | (v0, cs) | (v0, nsigs) ].
    + epose proof (procMsg_SubmitMsg_mixin _ _ _ _ _) as Hit.
      rewrite Epm in Hit.
      simpl_state.
      eqsolve.
    + simpl in Epm.
      destruct (combined_verify v0 cs).
      all: now injection_pair Epm.
    + simpl in Epm.
      destruct (NoDup_eqdec AddrSigPair_eqdec nsigs), (Nat.leb (N - t0) (length nsigs)), 
        (verify_certificate v0 nsigs).
      all: now injection_pair Epm.
  - destruct t.
    destruct_procInt as_ st' ms eqn_ Epm.
    subst w'.
    unfold upd.
    simpl.
    destruct (Address_eqdec n0 n) as [ -> | ]; auto.
    destruct_localState w_ n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    pose proof Hinv_ as (_, Hnodeinv_, _).
    specialize (Hnodeinv_ _ H_n_nonbyz).
    apply inv_node_coh in Hnodeinv_.
    destruct Hnodeinv_ as (_, _, _, _, _, Ha, (Hb & _)).
    simpl_state.
    subst ov.
    rewrite En in Ha, Hb.
    simpl_state.
    specialize (Hb eq_refl).
    destruct Ha as (Ha & _).
    subst buffer v.
    simpl in Epm.
    now injection_pair Epm.
Qed.

Definition all_honest_nodes_submitted v w := forall n, honest_node_submitted n v w.
(*
Fact all_honest_nodes_submitted_is_invariant v : is_invariant_step (fun w => invariant w /\ all_honest_nodes_submitted v w).
Proof.
  hnf.
  intros q ww ww' (Ha & Hb) Hstep.
  split.
  1: eapply inv_step; eauto.
  intros n.
  eapply honest_node_submitted_is_invariant; eauto.
Qed.
*)
(* fine, another one! *)

Definition honest_node_confirmed n w :=
  valid_node n -> is_byz n = false -> (localState w n).(conf).

Fact honest_node_confirmed_is_invariant n : is_invariant_step (fun w => invariant w /\ honest_node_confirmed n w).
Proof.
  hnf.
  intros q w_ w' (Hinv_ & Hst) Hstep.
  split.
  1: eapply inv_step; eauto.
  hnf in Hst |- *.
  intros Hnvalid H_n_nonbyz.
  specialize (Hst Hnvalid H_n_nonbyz).
  pose proof (coh _ Hinv_) as Hcoh.
  inversion Hstep as [ 
    | p Hq Hpin Hvalid Hsrcvalid Hnonbyz Heq 
    | n0 t Hq Hvalid H_n0_nonbyz Heq 
    | n0 dst v0 ls s Hq H_n_byz Heq 
    | n0 dst lc Hq H_n_byz Hcc Heq
    | n0 dst c Hq H_n_byz Hcc Heq ].
  all: subst q.
  1,4-6: now subst w'.
  - destruct p as (src, dst, msg, used) eqn:Ep.
    simpl_pkt.
    rewrite <- Ep in *.
    unfold procMsgWithCheck in Heq.
    destruct_procMsg as_ st' ms eqn_ Epm.
    assert (localState w' = upd dst st' (localState w_)) as -> by (destruct msg; now subst w').
    clear Heq.
    unfold upd.
    destruct (Address_eqdec dst n) as [ -> | ]; auto.
    destruct_localState w_ n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    destruct msg as [ v0 ls s | (v0, cs) | (v0, nsigs) ].
    + epose proof (procMsg_SubmitMsg_mixin _ _ _ _ _) as Hit.
      rewrite Epm in Hit.
      simpl_state.
      eqsolve.
    + simpl in Epm.
      destruct (combined_verify v0 cs).
      all: now injection_pair Epm.
    + simpl in Epm.
      destruct (NoDup_eqdec AddrSigPair_eqdec nsigs), (Nat.leb (N - t0) (length nsigs)), 
        (verify_certificate v0 nsigs).
      all: now injection_pair Epm.
  - destruct t.
    destruct_procInt as_ st' ms eqn_ Epm.
    subst w'.
    unfold upd.
    simpl.
    destruct (Address_eqdec n0 n) as [ -> | ]; auto.
    pose proof Hinv_ as (_, Hnodeinv_, _).
    specialize (Hnodeinv_ _ H_n_nonbyz).
    apply inv_node_coh in Hnodeinv_.
    pose proof (confirmed_then_submitted (localState w_ n) Hnodeinv_ Hst) as HH.
    destruct_localState w_ n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    simpl_state.
    destruct ov; try discriminate.
    destruct Hnodeinv_ as (_, _, _, _, _, _, (Ha & _)).
    simpl_state.
    specialize (Ha eq_refl).
    subst buffer.
    simpl in Epm.
    now injection_pair Epm.
Qed.

Section Proof_of_Terminating_Convergence.

  (* Hypothesis (Hrc : reliable_condition reachable). *)

  Variables (w : World) (v : Value).

  Hypotheses (H_w_reachable : reachable w) (H1 : all_honest_nodes_submitted v w).

  Lemma submit_msgs_all_sent : 
    { pkts : list Packet & 
      incl pkts (sentMsgs w) /\ 
      (* possibly add condition for all packets containing SubmitMsg? *)
      Forall good_packet pkts /\
      (forall n1 n2, valid_node n1 -> valid_node n2 -> 
        is_byz n1 = false -> is_byz n2 = false ->
        (* FIXME: unify v with value_bft? *)
        exists b, In (mkP n1 n2 (SubmitMsg (value_bft n1) 
          (light_sign (value_bft n1) (lightkey_map n1)) 
          (sign (value_bft n1) (key_map n1))) b) pkts) }.
  Proof.
    exists (filter (fun p => if good_packet_dec p 
      then (match msg p with SubmitMsg _ _ _ => true | _ => false end) else false) 
      (sentMsgs w)).
    split.
    1: apply incl_filter.
    split.
    1: rewrite Forall_forall; setoid_rewrite filter_In.
    1: intros p (? & ?); destruct (good_packet_dec p); eqsolve.
    intros n1 n2 Hn1valid Hn2valid H_n1_nonbyz H_n2_nonbyz.
    pose proof (reachable_inv _ H_w_reachable) as (Hcoh, Hnodeinv, _).
    specialize (Hnodeinv _ H_n1_nonbyz).
    unfold all_honest_nodes_submitted in H1.
    specialize (H1 _ Hn1valid H_n1_nonbyz).
    destruct Hnodeinv as (_, _, _, Hs, _, _, _, (_, _, _, _, _, Hs2, _)).
    rewrite (id_coh _ Hcoh), H1 in Hs, Hs2.
    destruct Hs2 as (-> & _).
    specialize (Hs _ Hn2valid).
    destruct Hs as (b & Hs).
    exists b.
    apply filter_In.
    split; try assumption.
    destruct (good_packet_dec _) as [ | Hn ]; try eqsolve.
    unfold good_packet in Hn.
    eqsolve.
  Qed.

  Definition honest_submit_all_received w' :=
    forall n1 n2, valid_node n1 -> valid_node n2 -> 
      is_byz n1 = false -> is_byz n2 = false -> 
      (* TODO elaborate v ls s? this should be possible due to submit_msgs_all_sent *)
      exists v ls s, In (mkP n1 n2 (SubmitMsg v ls s) true) (sentMsgs w').

  Fact honest_submit_all_received_suffcond w' (H2 : incl (map receive_pkt (projT1 submit_msgs_all_sent)) (sentMsgs w')) :
    honest_submit_all_received w'.
  Proof.
    destruct submit_msgs_all_sent as (pkts & HH).
    simpl in H2.
    destruct HH as (_ & _ & HH).
    hnf in H2 |- *.
    intros n0 n Hn0valid Hnvalid H_n0_nonbyz H_n_nonbyz.
    specialize (HH _ _ Hn0valid Hnvalid H_n0_nonbyz H_n_nonbyz).
    destruct HH as (b & HH%(in_map receive_pkt)).
    simpl in HH.
    apply H2 in HH.
    eauto.
  Qed.

  Variable (w0 : World) (l0 : list (system_step_descriptor * World)).
  Hypothesis (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0)
    (Hw0 : honest_submit_all_received w0).

  Definition all_honest_nodes_confirmed w' :=
    forall n, valid_node n -> is_byz n = false -> (localState w' n).(conf).

  Hypothesis (H_byz_minor : num_byz <= t0).

  Lemma terminating_convergence : all_honest_nodes_confirmed w0.
  Proof.
    assert (is_invariant_step (fun w => reachable w /\ all_honest_nodes_submitted v w)) as Hq.
    {
      hnf.
      unfold all_honest_nodes_submitted.
      intros q ww ww' (Ha & Hb) Hstep.
      split.
      1: eapply ReachableStep; eauto.
      intros n.
      pose proof (honest_node_submitted_is_invariant n v) as Htmp.
      eapply Htmp; eauto.
      split; [ now apply reachable_inv | now apply Hb ].
    }
    apply is_invariant_step_trace in Hq.
    apply Hq in Htrace0; auto.
    clear H_w_reachable H1.
    destruct Htrace0 as (Htmp & H1).
    pose proof (reachable_inv _ Htmp) as Hinv.
    pose proof (reachable_inv_2 _ Htmp) as Hinv2.
    rewrite <- Ew0 in *.
    clear Ew0 Htmp Htrace0 Hq w l0.
    rename w0 into w.
    hnf in H1, Hw0 |- *.
    intros n Hnvalid H_n_nonbyz.
    pose proof Hinv as (Hcoh, Hnodeinv, Hpsentinv).
    destruct_localState w n as_ conf ov from lsigs sigs rlcerts rcerts buffer eqn_ En.
    simpl.
    destruct conf eqn:Econf.
    1: reflexivity.
    (* get to know the size of from *)
    specialize (Hnodeinv n H_n_nonbyz).
    unfold holds in Hnodeinv.
    rewrite -> En in Hnodeinv.
    destruct Hnodeinv as (_, _, _, _, _, _, _, (_, Hconf, Hfrom_nodup, _, _, Hcoll_valid, (Hbuffer & _))).
    simpl_state.
    simpl in Hconf.
    (* get to know the value submitted and buffer = nil *)
    hnf in H1.
    pose proof H1 as H1n.
    specialize (H1n _ Hnvalid H_n_nonbyz).
    rewrite En in H1n.
    simpl in H1n.
    subst ov.
    destruct Hcoll_valid as (Ev & Hcoll_valid).
    specialize (Hbuffer eq_refl).
    subst buffer.
    (* get to know other nodes should be in from *)
    assert (incl (filter (fun n' => negb (is_byz n')) valid_nodes) from) as Hfrom.
    {
      intros n0 (Hn0valid & H_n0_nonbyz%negb_true_iff)%filter_In.
      (* get to know the message *)
      specialize (Hw0 n0 n Hn0valid Hnvalid H_n0_nonbyz H_n_nonbyz).
      destruct Hw0 as (v0 & ls0 & s0 & Hin).
      (* get to know the value and signatures in the message *)
      pose proof H1 as H1n0.
      specialize (H1n0 _ Hn0valid H_n0_nonbyz).
      hnf in Hpsentinv.
      rewrite psent_invariant_viewchange in Hpsentinv.
      specialize (Hpsentinv _ Hin H_n0_nonbyz).
      rewrite <- key_correct, <- lightkey_correct, -> H1n0 in Hpsentinv.
      destruct Hpsentinv as (-> & -> & Ev0).
      injection Ev0 as ->.
      (* get to know the message should be processed *)
      destruct Hinv2 as (Hpsentinv2).
      rewrite Forall_forall in Hpsentinv2.
      specialize (Hpsentinv2 _ Hin eq_refl H_n_nonbyz).
      rewrite En in Hpsentinv2.
      simpl in Hpsentinv2.
      apply Hpsentinv2; auto with ABCinv.
    }
    (* now math *)
    apply NoDup_incl_length in Hfrom.
    2: apply NoDup_filter, valid_nodes_NoDup.
    pose proof (Permutation_split_combine is_byz valid_nodes) as Hperm%Permutation_length.
    rewrite app_length in Hperm.
    unfold num_byz in H_byz_minor.
    pose proof t0_lt_N.
    unfold N in *.
    lia.
  Qed.

End Proof_of_Terminating_Convergence.

Section Proof_of_Accountability.

  (* Hypothesis (Hrc : reliable_condition reachable). *)

  Definition confirmed n w : Prop := is_byz n = false /\ valid_node n /\ (localState w n).(conf).

  Definition confirmed_different_values n1 n2 w : Prop :=
    n1 <> n2 /\ confirmed n1 w /\ confirmed n2 w /\ 
    (localState w n1).(submitted_value) <> (localState w n2).(submitted_value).

  Definition confirmed_different_values' n1 n2 w : Prop :=
    n1 <> n2 /\ confirmed n1 w /\ confirmed n2 w /\ 
    (localState w n1).(submitted_value) = Some (value_bft n1) /\
    (localState w n2).(submitted_value) = Some (value_bft n2) /\
    value_bft n1 <> value_bft n2.

  Local Tactic Notation "get_submitted" hyp(Hinv) "as_" ident(v) ident(EE) :=
    match type of Hinv with node_invariant _ (localState ?w ?n) =>
    match goal with HH : is_true (localState w n).(conf) |- _ =>
      let Hq := fresh "Hq" in
      pose proof (confirmed_then_submitted _ (inv_node_coh _ _ Hinv) HH) as Hq;
      destruct (localState w n).(submitted_value) as [ v | ] eqn:EE; try discriminate;
      clear Hq
    end end.

  Local Tactic Notation "unify_value_bft" hyp(Hinv) :=
    match type of Hinv with node_invariant _ (localState ?w ?n) =>
    match goal with HH1 : (localState w n).(submitted_value) = Some ?v, HH2 : Coh w |- _ =>
      let Hq := fresh "Hq" in
      pose proof (inv_submit_mixin _ (inv_node_coh _ _ Hinv)) as Hq;
      rewrite HH1, (id_coh _ HH2) in Hq;
      destruct Hq as (Hq & _); 
      subst v
    end end.

  Local Tactic Notation "saturate" constr(n1) constr(n2) hyp(Hinv) :=
    (* pose proof (reachable_inv _ H_w_reachable) as Hinv; *)
    pose proof Hinv as (Hcoh, Hnodeinv, _);
    match goal with 
    | H_n1_nonbyz : is_byz n1 = false, H_n2_nonbyz : is_byz n2 = false |- _ =>
    pose proof (Hnodeinv _ H_n1_nonbyz) as Hnodeinv1;
    pose proof (Hnodeinv _ H_n2_nonbyz) as Hnodeinv2;
    unfold holds in Hnodeinv1, Hnodeinv2;
    get_submitted Hnodeinv1 as_ v1 E1;
    get_submitted Hnodeinv2 as_ v2 E2;
    unify_value_bft Hnodeinv1;
    unify_value_bft Hnodeinv2; 
    assert (value_bft n1 <> value_bft n2) as Hvneq' by eqsolve
    end.

  Fact confirmed_different_values_strengthen n1 n2 w (Hinv : invariant w) :
    confirmed_different_values n1 n2 w <-> confirmed_different_values' n1 n2 w.
  Proof.
    split.
    - intros (Hnneq & (H_n1_nonbyz & Hn1valid & Hconf1) & (H_n2_nonbyz & Hn2valid & Hconf2) & Hvneq).
      saturate n1 n2 Hinv.
      now hnf.
    - intros H.
      hnf in H |- *.
      intuition congruence.
  Qed.

  Fact confirmed_different_values'_is_invariant n1 n2 :
    is_invariant_step (fun w => invariant w /\ confirmed_different_values' n1 n2 w).
  Proof.
    hnf.
    intros q w w' (Hinv & (Hnneq & (H_n1_nonbyz & Hn1valid & Hconf1) & 
      (H_n2_nonbyz & Hn2valid & Hconf2) & Hv1 & Hv2 & Hvneq)) Hstep.
    split.
    1: eapply inv_step; eauto.
    hnf.
    split; try assumption.
    split; [ | split ].
    1-2: hnf; do 2 (split; try assumption).
    1-2: eapply honest_node_confirmed_is_invariant; eauto.
    1-2: split; [ assumption | hnf; auto ].
    split; [ | split; try assumption ].
    all: eapply honest_node_submitted_is_invariant; eauto.
    all: split; [ assumption | hnf; auto ].
  Qed.

  Variables (w : World) (n1 n2 : Address).
  Hypothesis (H_w_reachable : reachable w) (Hfundamental : confirmed_different_values n1 n2 w).

  Local Tactic Notation "prepare" hyp(H) :=
    destruct H as (Hnneq & (H_n1_nonbyz & Hn1valid & Hconf1)
      & (H_n2_nonbyz & Hn2valid & Hconf2) & Hvneq); clear H.

  (* well, using 4 packets instead of 2 is inevitable. *)
  Definition mutual_lightcerts b1 b2 b3 b4 := Eval cbn in
    let f src dst b := (mkP src dst (LightConfirmMsg 
      (value_bft src, (lightsig_combine (localState w src).(collected_lightsigs)))) b) in
    (f n1 n1 b1 :: f n1 n2 b2 :: f n2 n1 b3 :: f n2 n2 b4 :: nil). 

  Lemma mutual_lightcerts_sent : exists b1 b2 b3 b4, incl (mutual_lightcerts b1 b2 b3 b4) (sentMsgs w).
  Proof.
    prepare Hfundamental.
    pose proof (reachable_inv _ H_w_reachable) as Hinv.
    saturate n1 n2 Hinv.
    apply inv_conf_lightconfmsg in Hnodeinv1, Hnodeinv2.
    rewrite E1 in Hnodeinv1.
    rewrite E2 in Hnodeinv2.
    pose proof (Hnodeinv1 Hconf1 _ Hn1valid) as (b1 & Hin1).
    pose proof (Hnodeinv1 Hconf1 _ Hn2valid) as (b2 & Hin2).
    pose proof (Hnodeinv2 Hconf2 _ Hn1valid) as (b3 & Hin3).
    pose proof (Hnodeinv2 Hconf2 _ Hn2valid) as (b4 & Hin4).
    rewrite (id_coh _ Hcoh) in Hin1, Hin2, Hin3, Hin4.
    exists b1, b2, b3, b4.
    hnf.
    simpl.
    intros ?.
    eqsolve.
  Qed.

  Definition mutual_lightcert_received w' :=
    incl (mutual_lightcerts true true true true) (sentMsgs w').

  Definition mutual_lightcert_conflict_detected w' :=
    lightcert_conflict_check (localState w' n1).(received_lightcerts) /\
    lightcert_conflict_check (localState w' n2).(received_lightcerts).

  Variable (w0 : World) (l0 : list (system_step_descriptor * World)).
  Hypothesis (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0)
    (Hw0 : mutual_lightcert_received w0).

  Lemma eventually_mutual_lightcert_conflict_detected : mutual_lightcert_conflict_detected w0.
  Proof.
    prepare Hfundamental.
    pose proof reachable_is_invariant as Hq.
    apply is_invariant_step_trace in Hq.
    apply Hq in Htrace0; auto.
    rename Htrace0 into Htmp.
    rewrite <- Ew0 in *.
    clear Ew0 Hq l0.
    pose proof (reachable_inv _ H_w_reachable) as Hinv.
    saturate n1 n2 Hinv.
    pose proof (reachable_inv_2 _ Htmp) as (Hinv2).
    eapply incl_Forall in Hinv2.
    2: apply Hw0.
    unfold mutual_lightcerts in Hinv2.
    rewrite ! Forall_cons_iff in Hinv2.
    simpl in Hinv2.
    (* FIXME: extract this *)
    assert (forall nn vv, valid_node nn -> is_byz nn = false ->
      (localState w nn).(submitted_value) = Some vv ->
      (localState w nn).(conf) ->
      combined_verify vv (lightsig_combine (collected_lightsigs (localState w nn)))) as Hq.
    {
      intros.
      specialize (Hnodeinv nn H0).
      pose proof Hnodeinv as ((Hsize1 & _), Hconf_size, Hfrom_nodup, _, _, Hcoll, _)%inv_node_coh.
      rewrite H1 in Hcoll.
      destruct Hcoll as (_ & Hlcv & _).
      rewrite H2 in Hconf_size.
      apply light_signatures_valid_for_combine in Hlcv; try assumption.
      apply combine_correct.
      exists (localState w nn).(from_set).
      split; try assumption.
      eqsolve.
    }
    pose proof (Hq _ _ Hn1valid H_n1_nonbyz E1 Hconf1) as HH1.
    pose proof (Hq _ _ Hn2valid H_n2_nonbyz E2 Hconf2) as HH2.
    split.
    - apply lightcert_conflict_check_correct.
      do 4 eexists.
      split; [ apply Hvneq' | ].
      split; now apply Hinv2.
    - apply lightcert_conflict_check_correct.
      do 4 eexists.
      split; [ apply Hvneq' | ].
      split; now apply Hinv2.
  Qed.

  (* again, start from w' instead of w ... this should still make sense, 
      although we do not know whether collected_sigs have changed or not *)
  (* from now on, need to forget about w *)

  Hypothesis (H_w0_reachable : reachable w0) (Hfundamental0 : confirmed_different_values n1 n2 w0)
    (Hdetected : mutual_lightcert_conflict_detected w0).

  Collection coll_w0 := n1 n2 w0 H_w0_reachable Hfundamental0 Hdetected.

  Lemma fullcerts_all_sent : 
    { pkts : list Packet &
      incl pkts (sentMsgs w0) /\ 
      Forall good_packet pkts /\
      (forall n, valid_node n -> is_byz n = false ->
        exists b1 b2 nsigs1 nsigs2, 
          (* INTENTIONALLY hide such information *)
          In (mkP n1 n (ConfirmMsg (value_bft n1, nsigs1)) b1) pkts /\
          In (mkP n2 n (ConfirmMsg (value_bft n2, nsigs2)) b2) pkts) }.
  Proof using coll_w0. clear l0 Htrace0 Ew0 Hfundamental H_w_reachable Hw0 w.
    (* pose proof (reachable_inv _ H_w_reachable) as Hinv.
    pose proof Hfundamental as Hf2.
    (* essentially, depending on "confirmed_different_values'_is_invariant" *)
    rewrite (confirmed_different_values_strengthen _ _ _ Hinv) in Hf2.
    pose proof (confirmed_different_values'_is_invariant n1 n2) as Hinv'%is_invariant_step_trace.
    specialize (Hinv' _ _ (conj Hinv Hf2) Htrace0).
    rewrite <- Ew0 in Hinv'. *)
    pose proof (reachable_inv _ H_w0_reachable) as Htmp.
    (* TODO design prepare' *)
    apply confirmed_different_values_strengthen in Hfundamental0; try assumption.
    destruct Hfundamental0 as (Hnneq & (H_n1_nonbyz & Hn1valid & Hconf1) & 
      (H_n2_nonbyz & Hn2valid & Hconf2) & Hv1 & Hv2 & Hvneq).

    exists (filter (fun p => if good_packet_dec p 
      then (match msg p with ConfirmMsg _ => true | _ => false end) else false) 
      (sentMsgs w0)).
    split.
    1: apply incl_filter.
    split.
    1: rewrite Forall_forall; setoid_rewrite filter_In.
    1: intros p (? & ?); destruct (good_packet_dec p); eqsolve.
    intros n Hnvalid H_n_nonbyz.
    pose proof Htmp as (Hcoh_, Hnodeinv_, _).
    pose proof (Hnodeinv_ _ H_n1_nonbyz) as Hnodeinv1_.
    pose proof (Hnodeinv_ _ H_n2_nonbyz) as Hnodeinv2_.
    apply inv_conf_confmsg in Hnodeinv1_, Hnodeinv2_.
    rewrite Hconf1, Hv1, (id_coh _ Hcoh_) in Hnodeinv1_.
    rewrite Hconf2, Hv2, (id_coh _ Hcoh_) in Hnodeinv2_.
    specialize (Hnodeinv1_ eq_refl (proj1 Hdetected) n Hnvalid).
    specialize (Hnodeinv2_ eq_refl (proj2 Hdetected) n Hnvalid).
    destruct Hnodeinv1_ as (b1 & Hin1), Hnodeinv2_ as (b2 & Hin2).
    exists b1, b2, (zip_from_sigs (localState w0 n1)), (zip_from_sigs (localState w0 n2)).
    split.
    all: apply filter_In.
    all: split; try assumption.
    all: destruct (good_packet_dec _) as [ | Hn ]; try eqsolve.
    all: unfold good_packet in Hn.
    all: eqsolve.
  Qed.

  Definition fullcerts_all_received w' :=
    forall n, valid_node n -> is_byz n = false ->
      (* but can elaborate here! *)
      In (mkP n1 n (ConfirmMsg (value_bft n1, zip_from_sigs (localState w' n1))) true) (sentMsgs w') /\
      In (mkP n2 n (ConfirmMsg (value_bft n2, zip_from_sigs (localState w' n2))) true) (sentMsgs w') /\
      (* some additional things ... *)
      (localState w' n1).(conf) /\
      (localState w' n2).(conf) /\
      (localState w' n1).(submitted_value) = Some (value_bft n1) /\
      (localState w' n2).(submitted_value) = Some (value_bft n2).

  Fact fullcerts_all_received_suffcond w' (H2 : incl (map receive_pkt (projT1 fullcerts_all_sent)) (sentMsgs w'))
    (Hinv : invariant w') : fullcerts_all_received w'.
  Proof using coll_w0. clear l0 Htrace0 Ew0 Hfundamental H_w_reachable Hw0 w.
    destruct fullcerts_all_sent as (pkts & HH).
    simpl in H2.
    destruct HH as (Hincl & Hgood & Haa).
    intros n Hnvalid H_n_nonbyz.
    specialize (Haa _ Hnvalid H_n_nonbyz).
    destruct Haa as (? & ? & ? & ? & Hin1%(in_map receive_pkt) & Hin2%(in_map receive_pkt)).
    apply H2 in Hin1, Hin2.
    simpl in Hin1, Hin2.
    destruct Hinv as (Hcoh0, Hnodeinv0, Hpsentinv0).
    hnf in Hpsentinv0.
    rewrite psent_invariant_viewchange in Hpsentinv0.
    pose proof (Hpsentinv0 _ Hin1) as Ht1.
    pose proof (Hpsentinv0 _ Hin2) as Ht2.
    simpl in Ht1, Ht2.
    prepare Hfundamental0.
    rewrite H_n1_nonbyz in Ht1.
    rewrite H_n2_nonbyz in Ht2.
    eqsolve.
  Qed.

  Definition accountability w' :=
    exists byzs : list Address, 
      NoDup byzs /\
      N - (t0 + t0) <= length byzs /\
      Forall is_byz byzs /\
      (forall n, is_byz n = false -> valid_node n -> incl byzs (genproof (localState w' n).(received_certs))).

  Variable (w1 : World) (l1 : list (system_step_descriptor * World)).
  Hypothesis (Htrace1 : system_trace w0 l1) (Ew1 : w1 = final_world w0 l1)
    (Hw1 : fullcerts_all_received w1).

  Collection coll_w0_w1 := w1 l1 Htrace1 Ew1 Hw1.

  Lemma eventually_accountability : accountability w1.
  Proof using coll_w0 coll_w0_w1. clear l0 Htrace0 Ew0 Hfundamental H_w_reachable Hw0 w.
    pose proof reachable_is_invariant as Hq.
    apply is_invariant_step_trace in Hq.
    apply Hq in Htrace1.
    (* 2: subst w0; apply Hq; assumption. *)
    2: assumption.
    rename Htrace1 into Htmp.
    rewrite <- Ew1 in *.
    clear Ew1 Hq l1.
    (* clear dependent w0.
    clear dependent l0. *)
    (* prepare Hfundamental0. *)
    apply confirmed_different_values_strengthen in Hfundamental0.
    2: now apply reachable_inv.
    destruct Hfundamental0 as (Hnneq & (H_n1_nonbyz & Hn1valid & Hconf1) & 
      (H_n2_nonbyz & Hn2valid & Hconf2) & Hv1 & Hv2 & Hvneq); clear Hfundamental0.
    (* pose proof (reachable_inv _ H_w_reachable) as Hinv. *)
    (* saturate n1 n2 Hinv.
    clear Hconf1 Hconf2 H_w_reachable E1 E2 Hinv Hcoh Hnodeinv Hnodeinv1 Hnodeinv2. (* TODO why clear dependent w does not work here? *)
    clear Hvneq. *)
    pose proof (reachable_inv _ Htmp) as Hinv.
    pose proof Hinv as (Hcoh, Hnodeinv, Hpsentinv).
    pose proof (reachable_inv_2 _ Htmp) as (Hpsentinv2).
    clear Htmp.
    hnf in Hw1 |- *.
    destruct_localState w1 n1 as_ conf1 ov1 from1 lsigs1 sigs1 rlcerts1 rcerts1 buffer1 eqn_ En1.
    destruct_localState w1 n2 as_ conf2 ov2 from2 lsigs2 sigs2 rlcerts2 rcerts2 buffer2 eqn_ En2.
    simpl_state.
    (* get basic information; here by trick, instantiate on n1 or n2 to know this information
        can be also obtained by the classic invariant approach, but anyway *)
    pose proof (Hw1 n1 Hn1valid H_n1_nonbyz) as (_ & _ & -> & -> & -> & ->).
    (* get size of cert *)
    pose proof (Hnodeinv n1 H_n1_nonbyz) as Hnodeinv1.
    pose proof (Hnodeinv n2 H_n2_nonbyz) as Hnodeinv2.
    unfold holds in Hnodeinv1, Hnodeinv2.
    rewrite En1 in Hnodeinv1.
    rewrite En2 in Hnodeinv2.
    pose proof Hnodeinv1 as ((_ & Hsize1), Hconf_size1, Hfrom_nodup1, _, _, Hcoll1, _)%inv_node_coh.
    pose proof Hnodeinv2 as ((_ & Hsize2), Hconf_size2, Hfrom_nodup2, _, _, Hcoll2, _)%inv_node_coh.
    simpl_state.
    cbn match in *.
    destruct Hcoll1 as (_ & _ & Hcert_valid1), Hcoll2 as (_ & _ & Hcert_valid2).
    unfold zip_from_sigs in *.
    simpl_state.
    rewrite -> Forall_forall in Hpsentinv2.
    assert (forall n, valid_node n -> is_byz n = false -> 
      In (value_bft n1, combine from1 sigs1) (localState w1 n).(received_certs) /\
      In (value_bft n2, combine from2 sigs2) (localState w1 n).(received_certs)) as H_c1_c2_in_rcerts.
    {
      intros n Hnvalid H_n_nonbyz.
      specialize (Hw1 _ Hnvalid H_n_nonbyz) as (Hin1%Hpsentinv2 & Hin2%Hpsentinv2 & _).
      simpl in Hin1, Hin2.
      split; [ apply Hin1 | apply Hin2 ]; auto; try lia.
      all: try now apply NoDup_combine_l.
      all: rewrite combine_length; lia.
    }
    (* again use the single instantiation trick to get the quorum *)
    pose proof (H_c1_c2_in_rcerts _ Hn1valid H_n1_nonbyz) as (H_c1_in_rcerts_n1 & H_c2_in_rcerts_n1).
    rewrite -> En1 in H_c1_in_rcerts_n1, H_c2_in_rcerts_n1.
    simpl_state.
    remember (filter (fun n => In_dec Address_eqdec n from1) from2) as from12.
    exists from12.
    assert (forall n, valid_node n -> is_byz n = false -> 
      incl from12 (genproof (received_certs (localState w1 n)))) as Hcommonproof.
    {
      intros n Hnvalid H_n_nonbyz nb Hinproof.
      subst from12.
      eapply conflicting_cert_quorum_in_proof; eauto.
      1-2: now apply H_c1_c2_in_rcerts.
      rewrite !combine_map_fst; eqsolve.
    }
    subst from12.
    intuition.
    - now apply NoDup_filter.
    - apply valid_cert_valid_senders in Hcert_valid1, Hcert_valid2.
      rewrite -> ! combine_map_fst in Hcert_valid1, Hcert_valid2; try eqsolve.
      apply quorum_intersection; auto; try lia.
    - apply Forall_forall.
      intros nb Hinproof.
      eapply inv_sound_weak with (n:=n1); eauto.
      now apply Hcommonproof.
  Qed.

End Proof_of_Accountability.

End Main_Proof.

End ACInvariant.
