From Coq Require Import List Bool Lia ssrbool.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network.

Module ACInvariant 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns).

Import A T AC Ns ACN.

Record node_invariant (psent : PacketSoup) (st : State) : Prop := mkNodeInv {
  inv_nsigs_correct: forall n sig, 
    let: (v, nsigs) := (cert st) in 
    In (n, sig) nsigs ->
      verify v sig n = true /\
      In (mkP n (id st) (SubmitMsg v sig) true) psent;
  inv_rcerts_correct: forall v nsigs,
    In (v, nsigs) (received_certs st) ->
      certificate_valid v nsigs /\
      exists src, In (mkP src (id st) (ConfirmMsg (v, nsigs)) true) psent;
  (* this is somewhat "pure" property (not related to psent) *)
  inv_conf_correct:
    if conf st 
    then length (snd (cert st)) = N - t0
    else length (snd (cert st)) < N - t0
}.

(* make two views of invariants *)

Definition _inv_submitmsg_correct stmap src v sig : Prop := 
  is_byz src = false ->
    verify v sig src = true /\
    v = fst (cert (stmap src)).

Definition _inv_confirmmsg_correct stmap psent_history src c : Prop := 
  if is_byz src
    then cert_correct psent_history c
    else conf (stmap src) = true /\ c = cert (stmap src)   (* strictly relies on that nsigs will not be updated after its size == N-t0 *)
.

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
  | H : invariant w |- _ =>
    destruct (localState w n) as (n', conf, c, rcerts) eqn:E; 
    assert (n' = n) as Htmp by
      (now rewrite <- (id_coh _ (coh _ H) n), E); 
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

Definition list_subset {A} (l1 l2 : list A) :=
  forall p : A, In p l1 -> In p l2.

Fact list_subset_app_r {A} (l1 l2 : list A) : list_subset l1 (l1 ++ l2).
Proof. hnf. intros. apply in_app_iff. now left. Qed.

Fact list_subset_app_l {A} (l1 l2 : list A) : list_subset l1 (l2 ++ l1).
Proof. hnf. intros. apply in_app_iff. now right. Qed.

Local Hint Resolve list_subset_app_l : ABCinv.
Local Hint Resolve list_subset_app_r : ABCinv.

Inductive psent_mnt : bool -> PacketSoup -> PacketSoup -> Prop :=
  | PsentEq (psent : PacketSoup) : psent_mnt false psent psent
  | PsentEq' (p : Packet) (psent : PacketSoup) 
    (Hin : In p psent) : psent_mnt false psent (consume p psent)
  | PsentLe (psent1 psent2 psent' : PacketSoup) 
    (Hpsenteq : psent_mnt false psent1 psent2)
    (Hsubset : list_subset psent2 psent') : 
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
      else list_subset (snd (cert st)) nsigs) : 
    state_mnt true st (node_upd_nsigs st 
      ((conf st) || (Nat.leb (N - t0) (length nsigs))) nsigs)
  | StateRCertsMnt (st : State) rcerts
    (Hmnt : list_subset (received_certs st) rcerts) : 
    state_mnt true st (node_upd_rcerts st rcerts).

Local Hint Constructors state_mnt : ABCinv.
Local Hint Constructors psent_mnt : ABCinv.

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
  revert n conf v nsigs rcerts Hnodeinv. 
  induction Hpmnt; subst; intros.
  - assumption.
  - constructor.
    3: apply Hnodeinv.
    + intros n0 sig Hin_nsig.
      split.
      1: now apply Hnodeinv.
      apply In_consume'.
      1: assumption.
      now apply Hnodeinv.
    + intros v0 nsigs0 Hin_rcerts.
      split.
      1: now apply Hnodeinv.
      destruct Hnodeinv as (_, Hnodeinv, _).
      specialize (Hnodeinv v0 nsigs0 Hin_rcerts).
      simpl in Hnodeinv.
      destruct Hnodeinv as (_ & (src & H)).
      exists src.
      apply In_consume'.
      1: assumption.
      now apply H.
  - apply IHHpmnt in Hnodeinv.
    constructor; simpl.
    3: apply Hnodeinv.
    + intros.
      split.
      * now apply Hnodeinv.
      * now apply Hsubset, Hnodeinv.
    + intros v0 nsigs0 Hin_rcerts.
      split.
      * now apply Hnodeinv.
      * destruct Hnodeinv as (_, Hnodeinv, _).
        specialize (Hnodeinv v0 nsigs0 Hin_rcerts).
        simpl in Hnodeinv.
        destruct Hnodeinv as (_ & (src & H)).
        exists src.
        now apply Hsubset.
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

Corollary inv_preserve_01 stmap stmap' psent psent'
  (Hpeq : forall x, stmap x = stmap' x)
  (Hpsentcond : exists psent_, psent_mnt false psent psent_ /\
    list_subset psent_ psent' /\
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
    destruct Hinv as (_, _, Hpsentinv).
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
  1: unfold list_subset; auto.
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
    lia.
  - constructor; simpl...
Qed.

Lemma inv_step w w' :
  invariant w -> system_step w w' -> invariant w'.
Proof with basic_solver.
  intros H Hstep. 
  inversion Hstep as [ | p Hpin Hpfresh Hnvalid Hnonbyz Heq 
    | n t Hnvalid H_n_nonbyz Heq 
    | n dst v s H_n_byz Heq 
    | n dst c H_n_byz Hcc Heq ].
  - now subst.
  - destruct p as (src, dst, msg, used) eqn:Ep.
    simpl_pkt.
    rewrite <- Ep in *.
    subst used.
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
      destruct Hconf as (_, _, Hconf).
      rewrite -> Edst in Hconf.
      simpl in Hconf.
      destruct (if Value_eqdec v v_dst 
        then (if verify v s src then (negb conf_dst) else false)
        else false) eqn:Edecide.
      * destruct (Value_eqdec v v_dst) as [ <- | ], (verify v s src) eqn:Everi, conf_dst eqn:Econf...
        inversion Hconf as [ Hle | thr Hle Ethr ].
        --(* the only 11 case in the proof; first 01 then 10 *)
          simpl in Epm.
          rewrite <- Hle, -> PeanoNat.Nat.leb_refl in Epm.
          injection_pair Epm.
          eapply inv_preserve_01 with (psent:=consume p (sentMsgs w)).
          1: reflexivity.
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
          eapply inv_preserve_10...
          ++pose proof (StateCertMnt (localState w dst) ((src, s) :: nsigs_dst)) as Hsmnt.
            rewrite -> Edst, <- Hle in Hsmnt.
            unfold list_subset in Hsmnt.
            simpl in Hsmnt.
            rewrite -> PeanoNat.Nat.leb_refl in Hsmnt.
            rewrite -> Edst.
            apply Hsmnt.
            intuition.
          ++(* TODO this part is a repetition. consider remove it *)
            destruct H as (_, Hnodeinv, _).
            specialize (Hnodeinv dst Hnonbyz).
            hnf in Hnodeinv.
            rewrite -> Edst in Hnodeinv.
            pose proof (psent_mnt_preserve_node_invariant _ _ _ (PsentEq' p (sentMsgs w) Hpin) _ Hnodeinv) as Hnodeinv'.
            destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_conf).
            constructor; simpl_state.
            3: simpl; lia.
            **simpl. 
              intros n sig [ Hin_nsigs | Hin_nsigs ].
              2: now apply Hnodeinv'.
              injection_pair Hin_nsigs.
              subst p.
              split...
            **destruct Hnodeinv' as (_, ?, _).
              assumption.
          ++eapply inv_preserve_00 with (psent:=(sentMsgs w))...
            now rewrite_w_expand w in_ H.
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
            unfold list_subset in Hsmnt.
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
            destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_conf).
            constructor; simpl_state.
            3: simpl; lia.
            **simpl. 
              intros n sig [ Hin_nsigs | Hin_nsigs ].
              2: now apply Hnodeinv'.
              injection_pair Hin_nsigs.
              subst p.
              split...
            **destruct Hnodeinv' as (_, ?, _).
              assumption.
          ++eapply inv_preserve_00 with (psent:=(sentMsgs w))...
            now rewrite_w_expand w in_ H.
      * (* local state: essentially no change, and psent is regularly changed *)
        assert (st' = localState w dst) as ->.
        { 
          rewrite -> Edst.
          destruct (Value_eqdec v v_dst), (verify v s src), conf_dst eqn:E...
          injection_pair Epm.
          rewrite -> Hconf.
          f_equal.
          apply PeanoNat.Nat.leb_refl.
        }
        destruct (if Value_eqdec v v_dst then verify v s src else false) eqn:Edecide'.
        --destruct (Value_eqdec v v_dst) as [ <- | ], (verify v s src) eqn:Everi, conf_dst...
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
        --assert (ms = nil) as -> 
            by (destruct (Value_eqdec v v_dst), (verify v s src); eqsolve).
          rewrite -> app_nil_r.
          eapply inv_preserve_00.
          ++apply upd_same_pointwise_eq.
          ++now apply PsentEq'.
          ++now rewrite_w_expand w in_ H.
    + simpl in Epm.
      destruct c as (v, nsigs).
      destruct (verify_certificate v nsigs) eqn:Everic.
      * injection_pair Epm.
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
          destruct Hnodeinv as (Hnodeinv_nsigs, Hnodeinv_rcerts, Hnodeinv_conf).
          constructor; simpl_state.
          3: assumption.
          ++destruct Hnodeinv' as (?, _, _).
            assumption.
          ++simpl.
            destruct Hnodeinv' as (_, Hnodeinv'_rcerts, _).
            intros v0 nsigs0 [ Hin_rcerts' | Hin_rcerts' ].
            2: now apply Hnodeinv'_rcerts in Hin_rcerts'.
            injection_pair Hin_rcerts'.
            split.
            **now apply verify_certificateP.
            **exists src.
              subst p.
              now left.
        --eapply inv_preserve_00 with (psent:=(sentMsgs w))...
          now rewrite_w_expand w in_ H.
      * (* essentially no change *)
        injection_pair Epm.
        rewrite -> app_nil_r, <- Edst.
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
    1: unfold list_subset; firstorder.
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
    1: unfold list_subset; firstorder.
    intros p0 Hin_app Hnotin.
    simpl in Hin_app.
    destruct Hin_app as [ <- | ]...
    simpl.
    rewrite -> H_n_byz...
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
  destruct Hnodeinv_n as (Hnodeinv_nsigs_n, Hnodeinv_rcerts_n, _).
  apply Hnodeinv_rcerts_n in Hin1, Hin2.
  destruct Hin1 as (Hcertvalid1 & (src1 & Hin1)), Hin2 as (Hcertvalid2 & (src2 & Hin2)).
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
      destruct Hnodeinv as (Hnodeinv_nsigs, _, _).
      rewrite <- Hcert in Hnodeinv_nsigs.
      apply Hnodeinv_nsigs in Hin_nsigs.
      destruct Hin_nsigs as (_ & Hin).
      (* coming back! *)
      apply Hpsentinv in Hin.
      simpl in Hin.
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
    verify v1 sig1 n = true /\ verify v2 sig2 n = true.

Lemma behave_byz_is_byz n psent stmap
  (Hpsentinv : psent_invariant stmap psent)
  (Hbyz : behave_byz n psent) : is_byz n = true.
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

End Main_Proof.

End ACInvariant.
