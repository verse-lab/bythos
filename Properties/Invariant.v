From Coq Require Import List Bool Lia ssrbool.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts.

Module ACInvariant 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns).

Import A T AC Ns ACN.

(* this is somewhat "pure" property (not related to psent) *)
Record node_coh (st : State) : Prop := mkNodeCoh {
  inv_conf_correct:
    if conf st 
    then length (snd (cert st)) = N - t0
    else length (snd (cert st)) < N - t0;
  inv_cert_nodup: NoDup (snd (cert st));
  (* "NoDup nsigs" and "N - t0 <= (length nsigs)" should also hold 
    even if the certificate is sent by a Byzantine node *)
  inv_rcerts_mixin: forall v nsigs, In (v, nsigs) (received_certs st) -> 
    certificate_valid v nsigs /\
    (NoDup nsigs) /\ 
    N - t0 <= (length nsigs);
  (* since there are only full certificates, there is only one certificate_valid *)
  inv_cert_valid: certificate_valid (fst (cert st)) (snd (cert st))
}.

Record node_invariant (psent : PacketSoup) (st : State) : Prop := mkNodeInv {
  inv_nsigs_correct: forall n sig, 
    let: (v, nsigs) := (cert st) in 
    In (n, sig) nsigs ->
      In (mkP n (id st) (SubmitMsg v sig) true) psent;
  inv_rcerts_correct: forall v nsigs,
    In (v, nsigs) (received_certs st) ->
      exists src, In (mkP src (id st) (ConfirmMsg (v, nsigs)) true) psent;
  (* there must be some packets sent on some condition 
      (or, packets cannot disappear from the packet soup for no reason) *)
  inv_conf_confmsg: 
    conf st -> forall n, valid_node n -> exists used, In (mkP (id st) n (ConfirmMsg (cert st)) used) psent;
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

Fact node_invariant_implies_inv_cert_sender_nodup st psent 
  (Hnodeinv : node_invariant psent st) : NoDup (map fst (snd (cert st))).
Proof.
  destruct Hnodeinv as (Hnodeinv_nsigs, _, _, (_, Hcert_nodup, _, Hcert_valid)).
  destruct (cert st) as (v, nsigs).
  eapply valid_cert_nodup_implies_sender_nodup; eauto.
Qed.

(* make two views of invariants *)

Definition _inv_submitmsg_correct stmap src v sig : Prop := 
  is_byz src = false ->
    verify v sig src /\
    v = fst (cert (stmap src)).

Definition _inv_confirmmsg_correct stmap psent_history src c : Prop := 
  if is_byz src
    then cert_correct psent_history c
    else conf (stmap src) /\ c = cert (stmap src)   (* strictly relies on that nsigs will not be updated after its size == N-t0 *)
.

(* by rule, a valid full certificate cannot be rejected by an honest node for no reason *)

Definition _inv_confirmmsg_receive (stmap : StateMap) dst v nsigs (b : bool) : Prop := 
  b -> is_byz dst = false ->
  certificate_valid v nsigs -> NoDup nsigs -> (N - t0 <= (length nsigs)) ->
    In (v, nsigs) (received_certs (stmap dst))
.

Definition _inv_msg_correct_2 stmap p : Prop :=
  let: mkP src dst msg b := p in
  match msg with
  | ConfirmMsg (v, nsigs) => _inv_confirmmsg_receive stmap dst v nsigs b
  | _ => True
  end.

Global Arguments _inv_confirmmsg_receive _ _ _ _ _/.
Global Arguments _inv_msg_correct_2 _ _/.

(* additional invariant which is used to prove the eventual accountability *)

Record invariant_2 (w : World) : Prop := mkInv2 {
  _ : Forall (_inv_msg_correct_2 (localState w)) (sentMsgs w)
}.

Definition _inv_msg_correct stmap psent_history p : Prop :=
  let: mkP src dst msg b := p in
  match msg with
  | SubmitMsg v sig => _inv_submitmsg_correct stmap src v sig
  | ConfirmMsg c => _inv_confirmmsg_correct stmap psent_history src c
  end.

Global Arguments _inv_submitmsg_correct _ _ _ _/.
Global Arguments _inv_confirmmsg_correct _ _ _ _/.
Global Arguments _inv_msg_correct _ _ _/.

Record _psent_invariant (stmap : StateMap) (psent psent_history : PacketSoup) : Prop := mkPsentInv {
  inv_submitmsg_correct: forall src dst v sig b, 
    In (mkP src dst (SubmitMsg v sig) b) psent ->
    _inv_submitmsg_correct stmap src v sig;
  inv_confirmmsg_correct: forall src dst c b, 
    In (mkP src dst (ConfirmMsg c) b) psent ->
    _inv_confirmmsg_correct stmap psent_history src c
}.

Definition psent_invariant stmap psent := _psent_invariant stmap psent psent.

Lemma psent_invariant_change stmap psent psent_history :
  _psent_invariant stmap psent psent_history <->
  (forall p, In p psent -> _inv_msg_correct stmap psent_history p).
Proof.
  split; intros H.
  - intros p Hin.
    destruct p as (src, dst, msg, used).
    simpl.
    destruct msg as [ v s | c ].
    all: eapply H; eauto.
  - constructor.
    + intros src dst v sig b Hin_psent H_src_nonbyz.
      specialize (H (mkP src dst (SubmitMsg v sig) b) Hin_psent).
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
  simpl id in *; simpl conf in *; simpl cert in *; simpl received_certs in *.

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
  "as_" ident(conf) ident(c) ident(rcerts) "eqn_" ident(E) :=
  let n' := fresh n in
  let Htmp := fresh "Htmp" in
  match goal with 
  | H : Coh w |- _ =>
    destruct (localState w n) as (n', conf, c, rcerts) eqn:E; 
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
  | PsentLe (psent1 psent2 psent' : PacketSoup) 
    (Hpsenteq : psent_mnt false psent1 psent2)
    (Hsubset : incl psent2 psent') : 
      psent_mnt true psent1 psent'.

Definition node_upd_nsigs (st : State) conf nsigs :=
  let: Node n _ (v, _) rcerts := st in
  Node n conf (v, nsigs) rcerts.

Definition node_upd_rcerts (st : State) rcerts :=
  let: Node n conf cert _ := st in
  Node n conf cert rcerts.

(* since each time there is only one field being updated, no need to make 
    recursive assumptions *)

Inductive state_mnt : bool -> State -> State -> Prop :=
  | StateEq (st : State) : state_mnt false st st
  | StateCertMnt (st : State) nsigs
    (Hmnt : if conf st then nsigs = snd (cert st)
      else incl (snd (cert st)) nsigs) : 
    state_mnt true st (node_upd_nsigs st 
      ((conf st) || (Nat.leb (N - t0) (length nsigs))) nsigs)
  | StateRCertsMnt (st : State) rcerts
    (Hmnt : incl (received_certs st) rcerts) : 
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

Lemma state_mnt_preserve_Coh ob stmap n st' psent 
  (Hnvalid : valid_node n)
  (Hsmnt : state_mnt ob (stmap n) st')
  (Hcoh : Coh (mkW stmap psent)) :
  Coh (mkW (upd n st' stmap) psent).
Proof. 
  constructor.
  - intros n0.
    unfold holds, upd.
    simpl. 
    destruct (Address_eqdec n n0) as [ -> | Hneq ].
    2: apply Hcoh.
    inversion Hsmnt; subst.
    1: apply Hcoh.
    all: destruct (stmap n0) as (?, ?, (?, ?), ?) eqn:E.
    all: simpl.
    all: transitivity (id (stmap n0)); [ now rewrite E | apply Hcoh ].
  - intros n0 Hninvalid.
    unfold holds, upd. 
    simpl.
    destruct (Address_eqdec n n0); try eqsolve.
    now apply Hcoh in Hninvalid.
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
    destruct Hcc as (dst & used & Hwitness).
    apply In_consume with (p:=p) in Hwitness; eauto.
  - apply IHHpmnt in Hcc.
    hnf in Hcc |- *.
    intros n sig Hin' H_n_nonbyz Hveri.
    specialize (Hcc _ _ Hin' H_n_nonbyz Hveri).
    hnf in Hcc |- *.
    destruct Hcc as (dst & used & Hwitness).
    apply Hsubset in Hwitness.
    now exists dst, used.
Qed.

Lemma psent_mnt_preserve_node_invariant b psent psent'
  (Hpmnt : psent_mnt b psent psent')
  st (Hnodeinv : node_invariant psent st) : node_invariant psent' st.
Proof.
  destruct st as (n, conf, (v, nsigs), rcerts).
  constructor; simpl_state.
  - intros n0 sig Hin_nsig.
    eapply In_psent_mnt'; eauto.
    now apply Hnodeinv.
  - intros v0 nsigs0 Hin_rcerts.
    destruct Hnodeinv as (_, Hnodeinv, _, _).
    specialize (Hnodeinv v0 nsigs0 Hin_rcerts).
    simpl in Hnodeinv.
    destruct Hnodeinv as (src & H).
    exists src.
    eapply In_psent_mnt'; eauto.
  - destruct Hnodeinv as (_, _, Hnodeinv, _).
    simpl_state.
    intros -> n0 Hn0valid.
    specialize (Hnodeinv eq_refl _ Hn0valid).
    destruct Hnodeinv as (used & H).
    eapply In_psent_mnt in H; eauto.
    firstorder.
  - apply Hnodeinv.
Qed.

Lemma state_mnt_preserve_psent_invariant ob stmap n st'
  (Hsmnt : state_mnt ob (stmap n) st')
  stmap' (Hpeq : forall x, stmap' x = (upd n st' stmap) x)
  psent (Hpsentinv : psent_invariant stmap psent) : 
  psent_invariant stmap' psent.
Proof.
  constructor.
  - intros src dst v sig b Hin_psent H_src_nonbyz.
    rewrite -> Hpeq.
    unfold upd.
    destruct (Address_eqdec n src) as [ -> | Hneq ].
    2: eapply Hpsentinv; eauto.
    inversion Hsmnt; subst.
    all: destruct (stmap src) as (?, ?, (v0, ?), ?) eqn:E.
    all: simpl.
    all: replace v0 with (fst (cert (stmap src))); [ eapply Hpsentinv; eauto | now rewrite E ].
  - intros src dst c b Hin_psent.
    simpl.
    rewrite -> Hpeq.
    destruct Hpsentinv as (_, Hpsentinv).
    specialize (Hpsentinv src dst c b Hin_psent).
    simpl in Hpsentinv.
    destruct (is_byz src) eqn:H_src_byz.
    1: assumption.
    unfold upd.
    destruct (Address_eqdec n src) as [ -> | Hneq ].
    2: eapply Hpsentinv; eauto.
    destruct (stmap src) as (?, conf0, (v0, nsigs0), ?) eqn:E.
    inversion Hsmnt; subst.
    all: simpl_state.
    + assumption.
    + destruct conf0.
      * subst nsigs. 
        assumption.
      * eqsolve.
    + assumption.
Qed.

Fact psent_equiv_preserve_psent_invariant stmap psent psent'
  (Hpmnt0 : psent_mnt false psent psent')
  (Hpsentinv : psent_invariant stmap psent) : 
  psent_invariant stmap psent'.
Proof.
  inversion Hpmnt0; subst.
  - assumption.
  - constructor.
    + intros src dst v sig b Hin_psent H_src_nonbyz.
      apply In_consume_converse in Hin_psent.
      2: assumption.
      destruct Hin_psent.
      eapply Hpsentinv; eauto.
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
Qed.

Lemma psent_history_mnt_preserve__inv_msg_correct 
  b psent psent' (Hpmnt : psent_mnt b psent psent') 
  stmap p (Hpsentinv : _inv_msg_correct stmap psent p) :
  _inv_msg_correct stmap psent' p.
Proof.
  simpl in Hpsentinv |- *.
  destruct p as (src, ?, [ | ], ?).
  1: assumption.
  destruct (is_byz src).
  2: assumption.
  eapply psent_mnt_preserve_cert_correct; eauto.
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
  apply psent_invariant_change.
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
  rewrite -> psent_invariant_change in Hpsentinv.
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
  - destruct Hinv as ((Hcoh1, Hcoh2), _, _).
    unfold holds in Hcoh1, Hcoh2.
    simpl in Hcoh1, Hcoh2.
    setoid_rewrite -> Hpeq in Hcoh1.
    setoid_rewrite -> Hpeq in Hcoh2.
    now constructor.
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
    constructor.
    + simpl; lia.
    + constructor. 
    + simpl. 
      intuition.
    + constructor.
  - constructor; simpl...
Qed.

Lemma inv_step w w' :
  invariant w -> system_step w w' -> invariant w'.
Proof with basic_solver.
  intros H Hstep. 
  pose proof (coh _ H) as Hcoh.
  inversion Hstep as [ | p Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | n t Hnvalid H_n_nonbyz Heq 
    | n dst v s H_n_byz Heq 
    | n dst c H_n_byz Hcc Heq ].
  - now subst.
  - destruct p as (src, dst, msg, used) eqn:Ep.
    simpl_pkt.
    rewrite <- Ep in *.
    destruct_procMsg as_ st' ms eqn_ Epm.
    destruct_localState w dst as_ conf_dst cert_dst rcerts_dst eqn_ Edst.
    subst w'.
    (* TODO may do case analysis in a smarter way. there is still some repetition *)
    destruct msg as [ v s | c ].
    + simpl in Epm.
      destruct cert_dst as (v_dst, nsigs_dst).
      (* prepare *)
      pose proof H as Hconf.
      destruct Hconf as (_, Hconf, _).
      specialize (Hconf dst Hnonbyz).
      unfold holds in Hconf.
      destruct Hconf as (_, _, Hconf_sent, (Hconf, Hcert_nodup, Hrcerts, Hcert_valid)).
      rewrite -> Edst in Hconf, Hcert_nodup, Hrcerts, Hcert_valid, Hconf_sent.
      simpl in Hconf, Hcert_nodup, Hrcerts, Hcert_valid, Hconf_sent.
      destruct (if Value_eqdec v v_dst 
        then (if verify v s src 
              then (if (negb conf_dst) 
                    then (negb (is_left (In_dec AddrSigPair_eqdec (src, s) nsigs_dst))) 
                    else false) 
              else false)
        else false) eqn:Edecide.
      * destruct (Value_eqdec v v_dst) as [ <- | ], 
          (verify v s src) eqn:Everi, 
          conf_dst eqn:Econf, 
          (In_dec AddrSigPair_eqdec (src, s) nsigs_dst) as [ Ensig_in | Ensig_in ]...
        inversion Hconf as [ Hle | thr Hle Ethr ].
        --(* the only 11 case in the proof *)
          (* now cannot prove by applying 01 then 10 due to interrelation *)
          simpl in Epm.
          rewrite <- Hle, -> PeanoNat.Nat.leb_refl in Epm.
          injection_pair Epm.
          (* get state mnt *)
          pose proof (StateCertMnt (localState w dst) ((src, s) :: nsigs_dst)) as Hsmnt.
          rewrite -> Edst, <- Hle in Hsmnt.
          unfold incl in Hsmnt.
          simpl in Hsmnt.
          rewrite -> PeanoNat.Nat.leb_refl in Hsmnt.
          specialize (Hsmnt (fun _ p => or_intror p)).
          constructor.
          ++eapply state_mnt_preserve_Coh; eauto.
            **rewrite -> Edst.
              now apply Hsmnt.
            **eapply Coh_psent_irrelevant.
              rewrite_w_expand w in_ H.
              now apply H.
          ++intros n H_n_nonbyz.
            unfold holds, upd.
            cbn delta -[consume] iota beta.
            destruct (Address_eqdec dst n) as [ -> | Hnneq ].
            2:{
              eapply psent_mnt_preserve_node_invariant.
              1: eapply PsentLe with (psent1:=(sentMsgs w)) (psent2:=(consume p (sentMsgs w)))...
              now apply H.
            }
            destruct H as (_, Hnodeinv, _).
            specialize (Hnodeinv n Hnonbyz).
            hnf in Hnodeinv.
            rewrite -> Edst in Hnodeinv.
            destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_confsent, Hnodeinv_coh).
            pose proof (PsentLe _ _ _ (PsentEq' _ (sentMsgs w) Hpin) 
              (incl_appl_simple _ (broadcast n (ConfirmMsg (v, (src, s) :: nsigs_dst))))) as Hpmnt1.
            constructor; simpl_state.
            **intros n0 sig Hin_nsigs.
              rewrite -> in_app_iff.
              left.
              simpl in Hin_nsigs.
              destruct Hin_nsigs as [ Hin_nsigs | Hin_nsigs ].
              2: apply In_consume'...
              injection_pair Hin_nsigs.
              subst p.
              simpl...
            **intros v0 nsigs0 Hin_rcerts.
              specialize (Hnodeinv_rcerts v0 nsigs0 Hin_rcerts).
              simpl in Hnodeinv_rcerts.
              destruct Hnodeinv_rcerts as (src0 & H).
              exists src0.
              eapply In_psent_mnt'; eauto.
            **intros _ n0 Hn0valid.
              exists false.
              rewrite -> in_app_iff.
              right.
              apply In_broadcast.
              eauto.
            **constructor; simpl...
              constructor...
              simpl...
          ++cbn delta -[consume] iota beta.
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
        --simpl in Epm.
          assert (~ (thr <= length nsigs_dst)) as Hgt...
          apply PeanoNat.Nat.leb_nle in Hgt.
          rewrite <- Ethr in Epm.
          simpl in Epm. 
          rewrite -> Hgt in Epm.
          injection_pair Epm.
          rewrite -> app_nil_r.
          (* 10 case *)
          eapply inv_preserve_10...
          ++pose proof (StateCertMnt (localState w dst) ((src, s) :: nsigs_dst)) as Hsmnt.
            rewrite -> Edst, <- Ethr in Hsmnt.
            unfold incl in Hsmnt.
            simpl in Hsmnt.
            rewrite -> Hgt in Hsmnt.
            rewrite -> Edst.
            apply Hsmnt.
            intuition.
          ++destruct H as (_, Hnodeinv, _).
            specialize (Hnodeinv dst Hnonbyz).
            hnf in Hnodeinv.
            rewrite -> Edst in Hnodeinv.
            pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
            destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_confsent, Hnodeinv_conf).
            constructor; simpl_state...
            **simpl. 
              intros n sig [ Hin_nsigs | Hin_nsigs ].
              2: now apply Hnodeinv'.
              injection_pair Hin_nsigs.
              subst p...
            **destruct Hnodeinv' as (_, ?, ?, _).
              assumption.
            **constructor; simpl...
              constructor...
              simpl...
          ++eapply inv_preserve_00 with (psent:=(sentMsgs w))...
            now rewrite_w_expand w in_ H.
      * (* local state: essentially no change, and psent is regularly changed *)
        assert (st' = (localState w dst)) as ->.
        { 
          rewrite -> Edst.
          destruct (Value_eqdec v v_dst), (verify v s src), conf_dst eqn:E, 
            (In_dec AddrSigPair_eqdec (src, s) nsigs_dst) as [ Ensig_in | Ensig_in ]...
          all: injection_pair Epm...
          all: try rewrite -> Hconf, PeanoNat.Nat.leb_refl...
          rewrite <- PeanoNat.Nat.leb_gt in Hconf.
          rewrite -> Hconf...
        }
        destruct (if Value_eqdec v v_dst 
          then (if verify v s src
                then conf_dst 
                else false) 
          else false) eqn:Edecide'.
        --destruct (Value_eqdec v v_dst) as [ <- | ], (verify v s src) eqn:Everi...
          subst conf_dst.
          (* send confirm message (after confirm) *)
          rewrite -> Hconf, PeanoNat.Nat.leb_refl, <- Edst in Epm.
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
        --assert (ms = nil) as ->.
          {
            destruct (Value_eqdec v v_dst), (verify v s src)...
            subst conf_dst.
            destruct (in_dec AddrSigPair_eqdec (src, s) nsigs_dst)...
            rewrite <- PeanoNat.Nat.leb_gt in Hconf.
            rewrite -> Hconf in Epm...
          }
          rewrite -> app_nil_r.
          eapply inv_preserve_00.
          ++apply upd_same_pointwise_eq.
          ++now apply PsentEq'.
          ++now rewrite_w_expand w in_ H.
    + simpl in Epm.
      destruct c as (v, nsigs).
      destruct (if NoDup_eqdec AddrSigPair_eqdec nsigs
        then (if Nat.leb (N - t0) (length nsigs)
              then is_left (verify_certificate v nsigs)
              else false)
        else false) eqn:Edecide.
      * destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
          (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
          (verify_certificate v nsigs) eqn:Everic...
        injection_pair Epm.
        rewrite -> app_nil_r.
        (* eapply inv_preserve_00 with (psent:=(sentMsgs w))... *)
        eapply inv_preserve_10...
        --match goal with
          |- state_mnt _ _ ?st => replace st with (node_upd_rcerts (localState w dst) ((v, nsigs) :: rcerts_dst))
          end.
          2: simpl; now rewrite -> Edst.
          apply StateRCertsMnt.
          rewrite -> Edst.
          hnf.
          intuition.
        --destruct H as (_, Hnodeinv, _).
          specialize (Hnodeinv dst Hnonbyz).
          hnf in Hnodeinv.
          rewrite -> Edst in Hnodeinv.
          pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
          (* preserve these ? to make auto work *)
          destruct Hnodeinv as (?, ?, ?, (?, ?, Hnodeinv_rcerts_mixin, ?)).
          constructor; simpl_state.
          ++apply Hnodeinv'.
          ++simpl.
            destruct Hnodeinv' as (_, Hnodeinv'_rcerts, _, _).
            intros v0 nsigs0 [ Hin_rcerts' | Hin_rcerts' ].
            2: now apply Hnodeinv'_rcerts in Hin_rcerts'.
            injection_pair Hin_rcerts'.
            exists src.
            subst p.
            now left.
          ++apply Hnodeinv'.
          ++constructor...
            simpl.
            intros v0 nsigs0 [ Hpeq | ].
            2: now apply Hnodeinv_rcerts_mixin.
            injection_pair Hpeq.
            split; [ | split ]...
            now apply PeanoNat.Nat.leb_le.
        --eapply inv_preserve_00 with (psent:=(sentMsgs w))...
          now rewrite_w_expand w in_ H.
      * assert ((localState w dst, nil) = (st', ms)) as Epm'
          by (destruct (NoDup_eqdec AddrSigPair_eqdec nsigs),
            (Nat.leb (N - t0) (length nsigs)), (verify_certificate v nsigs); eqsolve).
        (* essentially no change *)
        injection_pair Epm'.
        rewrite -> app_nil_r.
        eapply inv_preserve_00.
        --apply upd_same_pointwise_eq.
        --now apply PsentEq'.
        --now rewrite_w_expand w in_ H.
  - destruct_procInt as_ st' ms eqn_ Epm.
    destruct_localState w n as_ conf cert rcerts eqn_ En.
    subst w'.
    destruct t.
    + simpl in Epm.
      destruct cert as (vthis, nsigs).
      injection_pair Epm.
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
      split.
      * now apply key_correct.
      * now rewrite -> En.
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

Lemma inv_2_by_extend stmap psent psent'
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
  - now destruct msg0 as [ | (?, ?) ].
Qed.

Lemma inv_2_init : invariant_2 initWorld.
Proof with basic_solver.
  do 2 constructor.
Qed.

Lemma inv_2_step w w' (Hinv2 : invariant_2 w)
  (Hcoh : Coh w) (Hstep : system_step w w') : invariant_2 w'.
Proof with basic_solver.
  destruct Hinv2 as (Hpsentinv).
  pose proof Hpsentinv as Hpsentinv'.
  rewrite -> Forall_forall in Hpsentinv'.
  inversion Hstep as [ | p Hpin Hnvalid Hsrcvalid Hnonbyz Heq 
    | n t Hnvalid H_n_nonbyz Heq 
    | n dst v s H_n_byz Heq 
    | n dst c H_n_byz Hcc Heq ].
  - now subst.
  - destruct p as (src, dst, msg, used) eqn:Ep.
    simpl_pkt.
    rewrite <- Ep in *.
    destruct_procMsg as_ st' ms eqn_ Epm.
    destruct_localState w dst as_ conf_dst cert_dst rcerts_dst eqn_ Edst.
    subst w'.
    destruct msg as [ v s | c ].
    + simpl in Epm.
      destruct cert_dst as (v_dst, nsigs_dst).
      (* do some brute force *)
      assert (received_certs st' = rcerts_dst /\ 
        (forall p, In p ms -> consumed p = false)) as (Hrcerts_intact & Hin_ms).
      {
        destruct (Value_eqdec v v_dst) as [ <- | ], 
          (verify v s src) eqn:Everi, 
          conf_dst eqn:Econf, 
          (In_dec AddrSigPair_eqdec (src, s) nsigs_dst) as [ Ensig_in | Ensig_in ], 
          (Nat.leb (N - t0) (length nsigs_dst)) eqn:Ele.
        all: injection_pair Epm.
        all: split; [ reflexivity | ].
        all: simpl.
        all: try (intuition; fail).
        4-5: destruct (Nat.leb (N - t0) (S (length nsigs_dst))) eqn:Ele'.
        all: simpl.
        all: try (intuition; fail).
        all: intros p0 Hinb.
        all: apply In_broadcast in Hinb.
        all: now destruct Hinb as (? & ? & ->).
      }
      (* now discuss *)
      apply inv_2_by_extend with (psent:=consume p (sentMsgs w)).
      1: setoid_rewrite -> in_app_iff.
      1: intuition.
      constructor.
      apply Forall_forall.
      simpl.
      intros (src0, dst0, msg0, b0) [ Hin | Hin ].
      * destruct p.
        simpl in Hin.
        injection Ep as ->.
        injection Hin as ->.
        now subst.
      * apply in_remove in Hin.
        destruct Hin as (Hin & _).
        apply Hpsentinv' in Hin.
        simpl in Hin.
        unfold upd.
        destruct (Address_eqdec dst dst0) as [ <- | Hnneq ].
        2: apply Hin.
        rewrite -> Edst in Hin.
        rewrite -> Hrcerts_intact.
        now simpl in Hin |- *.
    + (* the only critical case *)
      simpl in Epm.
      destruct c as (v, nsigs).
      assert (ms = nil) as ->
        by (destruct (NoDup_eqdec AddrSigPair_eqdec nsigs),
          (Nat.leb (N - t0) (length nsigs)), (verify_certificate v nsigs); eqsolve).
      rewrite -> app_nil_r.
      constructor.
      rewrite -> Forall_forall in Hpsentinv |- *.
      simpl.
      intros (src0, dst0, msg0, b0) [ Hin | Hin ].
      * destruct p.
        simpl in Hin.
        injection Ep as ->.
        injection Hin as ->.
        subst.
        unfold upd.
        destruct (Address_eqdec dst0 dst0) as [ _ | ? ].
        2: eqsolve.
        destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
          (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
          (verify_certificate v nsigs) eqn:Everic...
        all: injection Epm as <-.
        --simpl. 
          intuition.
        --intros.
          rewrite <- PeanoNat.Nat.leb_le in *.
          eqsolve.
      * apply in_remove in Hin.
        destruct Hin as (Hin & _).
        apply Hpsentinv' in Hin.
        simpl in Hin.
        unfold upd.
        destruct (Address_eqdec dst dst0) as [ <- | Hnneq ].
        2: apply Hin.
        rewrite -> Edst in Hin.
        destruct msg0 as [ | (v0, nsigs0) ].
        1: auto.
        simpl in Hin |- *.
        destruct (NoDup_eqdec AddrSigPair_eqdec nsigs) as [ Hnodup | ],
          (Nat.leb (N - t0) (length nsigs)) eqn:Hlnsigs, 
          (verify_certificate v nsigs) eqn:Everic.
        all: injection Epm as <-...
        simpl.
        intuition.
  - destruct_procInt as_ st' ms eqn_ Epm.
    destruct_localState w n as_ conf cert rcerts eqn_ En.
    subst w'.
    destruct t.
    + simpl in Epm.
      destruct cert as (vthis, nsigs).
      injection_pair Epm.
      rewrite <- En.
      eapply stmap_pointwise_eq_preserve_inv_2.
      1: apply upd_same_pointwise_eq.
      apply inv_2_by_extend with (psent:=(sentMsgs w)).
      2: now constructor.
      intros p Hin.
      rewrite -> in_app_iff, In_broadcast in Hin.
      destruct Hin as [ (? & ? & ->) | ].
      all: intuition.
  - subst w'.
    apply inv_2_by_extend with (psent:=(sentMsgs w)).
    2: now constructor.
    simpl.
    intros p [ <- | ].
    all: intuition.
  - subst w'.
    apply inv_2_by_extend with (psent:=(sentMsgs w)).
    2: now constructor.
    simpl.
    intros p [ <- | ].
    all: intuition.
Qed.

Inductive reachable : World -> Prop :=
  | ReachableInit : reachable initWorld
  | ReachableStep (w w' : World) (Hstep : system_step w w')
    (H_w_reachable : reachable w) : reachable w'.

Lemma reachable_inv w (H_w_reachable : reachable w) :
  invariant w.
Proof.
  induction H_w_reachable as [ | w w' Hstep H_w_reachable IH ].
  - apply inv_init.
  - now apply inv_step in Hstep.
Qed.

(* now we can only prove this form of soundness *)

Lemma inv_sound_weak w (Hinv : invariant w)
  n (H_n_nonbyz : is_byz n = false)
  nb (Hacc : In nb (genproof (received_certs (localState w n)))) :
  (* behave_byz nb (sentMsgs w). *)
  is_byz nb.
Proof.
  (* prove by contradiction *)
  destruct (is_byz nb) eqn:E.
  1: auto.
  apply genproof_spec in Hacc.
  destruct Hacc as (v1 & v2 & nsigs1 & nsigs2 & Hvneq & Hin1 & Hin2 & Hin_nsigs1 & Hin_nsigs2).
  (* cert in rcerts --> Confirm msg *)
  destruct Hinv as (Hcoh, Hnodeinv, Hpsentinv).
  pose proof (Hnodeinv n H_n_nonbyz) as Hnodeinv_n.
  unfold holds in Hnodeinv_n.
  destruct Hnodeinv_n as (Hnodeinv_nsigs_n, Hnodeinv_rcerts_n, _, _).
  apply Hnodeinv_rcerts_n in Hin1, Hin2.
  destruct Hin1 as (src1 & Hin1), Hin2 as (src2 & Hin2).
  unfold psent_invariant in Hpsentinv.
  rewrite -> psent_invariant_change in Hpsentinv.
  apply Hpsentinv in Hin1, Hin2.
  assert (forall v nsigs src dst used
    (Hin : _inv_msg_correct (localState w) (sentMsgs w) (mkP src dst (ConfirmMsg (v, nsigs)) used))
    (Hin_nsigs : In (nb, sign v (key_map nb)) nsigs),
    v = fst (cert (localState w nb))) as Htraceback.
  {
    intros v0 nsigs0 src0 dst0 used0 Hin Hin_nsigs.
    simpl in Hin.
    destruct (is_byz src0) eqn:Ebyz0.
    - specialize (Hin _ _ Hin_nsigs E (correct_sign_verify_ok _ _)).
      unfold seen_in_history in Hin.
      destruct Hin as (dst & used & Hin).
      apply Hpsentinv in Hin.
      simpl in Hin.
      intuition.
    - destruct Hin as (_ & Hcert).
      (* instantiate another nodeinv *)
      specialize (Hnodeinv src0 Ebyz0).
      unfold holds in Hnodeinv.
      destruct Hnodeinv as (Hnodeinv_nsigs, _, _, _).
      rewrite <- Hcert in Hnodeinv_nsigs.
      apply Hnodeinv_nsigs in Hin_nsigs.
      (* coming back! *)
      apply Hpsentinv in Hin_nsigs.
      simpl in Hin_nsigs.
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
  exists v1 v2 sig1 sig2 dst1 dst2, 
    v1 <> v2 /\
    In (mkP n dst1 (SubmitMsg v1 sig1) true) psent /\
    In (mkP n dst2 (SubmitMsg v2 sig2) true) psent /\
    verify v1 sig1 n /\ verify v2 sig2 n.

Lemma behave_byz_is_byz n psent stmap
  (Hpsentinv : psent_invariant stmap psent)
  (Hbyz : behave_byz n psent) : is_byz n.
Proof.
  (* prove by contradiction *)
  destruct (is_byz n) eqn:E.
  1: reflexivity.
  destruct Hbyz as (v1 & v2 & sig1 & sig2 & dst1 & dst2 & Hvneq & Hin1 & Hin2 & Hveri1 & Hveri2).
  hnf in Hpsentinv.
  rewrite -> psent_invariant_change in Hpsentinv.
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
      apply genproof_spec.
      exists v1, v2, nsigs1, nsigs2.
      intuition.
Qed.

Lemma reachable_inv_2 w (H_w_reachable : reachable w) :
  invariant_2 w.
Proof.
  induction H_w_reachable as [ | w w' Hstep H_w_reachable IH ].
  - apply inv_2_init.
  - pose proof (reachable_inv _ H_w_reachable) as (Hcoh, _, _).
    now apply inv_2_step in Hstep.
Qed.

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

End Main_Proof.

End ACInvariant.
