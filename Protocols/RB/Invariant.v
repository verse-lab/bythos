From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.RB Require Export Network.

From RecordUpdate Require Import RecordUpdate.

From stdpp Require Import tactics. (* anyway *)

Module RBInvariant (A : NetAddr) (R : RBTag) (V : Signable) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBN := RBNetwork A R V VBFT BTh BSett.

Section Main_Proof.

Set Implicit Arguments. (* anyway *)

(* boilerplate ... *)
Definition is_InitialMsg (m : Message) :=
  match m with
  | InitialMsg _ _ => true
  | _ => false
  end.

Global Arguments is_InitialMsg !_ /.
(*
(*
Fact is_InitialMsg_false_match {A : Type} m (e1 : Round -> Value -> A) (e2 : Message -> A)
  (H : is_InitialMsg m = false) :
  (match m with
  | InitialMsg r v => e1 r v
  | _ => e2 m
  end) = e2 m.
Proof. destruct m; simpl in H; try discriminate; try reflexivity. Qed.
*)
Fact is_InitialMsg_false_match {A : Type} m (e1 : A) (e2 : A)
  (H : is_InitialMsg m = false) :
  (match m with
  | InitialMsg r v => e1
  | _ => e2
  end) = e2.
Proof. destruct m; simpl in H; try discriminate; try reflexivity. Qed.
*)
Tactic Notation "simpl_pkt" :=
  simpl dst in *; simpl src in *; simpl msg in *; simpl consumed in *.

Tactic Notation "simpl_world" :=
  simpl localState in *; simpl sentMsgs in *.

Tactic Notation "injection_pair" hyp(H) :=
  match type of H with
    (?a, ?b) = (?c, ?d) => is_var c; is_var d; injection H as <-; try subst c; try subst d
  end.

Tactic Notation "inversion_step_" hyp(H) ident(Heq) :=
  (* conventional naming *)
  let n := fresh "n" in
  let p := fresh "p" in
  let t := fresh "t" in
  let m := fresh "m" in
  let dst := fresh "dst" in
  let Hq := fresh "Hq" in
  let Hpin := fresh "Hpin" in
  let Hnonbyz := fresh "Hnonbyz" in
  let Hbyz := fresh "Hbyz" in
  let Hc := fresh "Hc" in
  inversion H as 
    [ Hq <-
    | p Hq Hpin Hnonbyz Heq 
    | n t Hq Hnonbyz Heq 
    | n dst m Hq Hbyz Hc Heq ];
  match type of Hq with
    @eq system_step_descriptor ?q _ => try (is_var q; subst q)
  end.

Tactic Notation "inversion_step" hyp(H) :=
  let Heq := fresh "Heq" in inversion_step_ H Heq.

Tactic Notation "inversion_step'" hyp(H) :=
  let stf := fresh "stf" in (* "f" for final *)
  let msf := fresh "msf" in
  let Ef := fresh "Ef" in
  let E := fresh "E" in
  let Heq := fresh "Heq" in
  inversion_step_ H Heq;
  [
  | (* FIXME: "src", "dst" and "msg" have the same names as functions over messages, 
      so they will have a trailing "0" or something if use "fresh".
      currently, let's get rid of this *)
    (* let src := fresh "src" in
    let dst := fresh "dst" in
    let msg := fresh "msg" in
    let used := fresh "used" in *)
    destruct (procMsgWithCheck _ _ _) as (stf, msf) eqn:Ef in Heq;
    match type of Ef with
    | procMsgWithCheck _ _ (?msgfunc ?p) = _ =>
      destruct p as [ src dst msg used ]; simpl_pkt
    | _ => idtac
    end;
    (* this try seems protocol specific *)
    unfold procMsgWithCheck in Ef;
    (*
    (* no, not in this protocol ... *)
      try (unfold procMsgWithCheck in Ef;
      destruct (procMsg _ _ _) as (st', ms) eqn:E in Ef); *)
    match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  | destruct (procInt _ _) as (st', ms) eqn:E in Heq;
    match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  | match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  ].
(*
Tactic Notation "destruct_localState" ident(w) ident(n) 
  "as_" simple_intropattern(pat) "eqn_" ident(E) :=
  let n' := fresh n in
  let Htmp := fresh "Htmp" in
  match goal with 
  | H : Coh w |- _ =>
    destruct (w @ n) as pat eqn:E; 
    assert (n' = n) as Htmp by
      (now rewrite <- (id_coh _ H n), E); 
    subst n'
  end.
*)

Tactic Notation "simpl_via_is_InitialMsg_false" constr(msg) :=
  repeat match goal with
  | H : context[match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | ReadyMsg _ _ _ => ?ee end] |- _ =>
    replace (match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | ReadyMsg _ _ _ => ee end)
      with ee in H by (destruct msg; try discriminate; reflexivity)
  | |- context[match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | ReadyMsg _ _ _ => ?ee end] =>
    replace (match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | ReadyMsg _ _ _ => ee end)
      with ee by (destruct msg; try discriminate; reflexivity)
  end.

Tactic Notation "eqsolve" := solve [ intuition congruence | intuition discriminate ].

Tactic Notation "hypothesis" :=
  match goal with
    H : ?e |- _ => 
    match type of e with
      Prop => simple apply H
    end
  end.

Tactic Notation "destruct_eqdec" "as_" simple_intropattern(pat) :=
  match goal with
    |- context[if ?eqdec ?a ?b then _ else _] =>
    match type of eqdec with
      forall _ : _, forall _ : _, sumbool (eq _ _) (not (eq _ _)) =>
      destruct (eqdec a b) as [ pat | ] +
      destruct (eqdec a b) as [ | ]
    end
  end.

Create HintDb RBinv.

Tactic Notation "basic_solver" :=
  try reflexivity; auto with RBinv; try tauto; try eqsolve; try lia.

Fact incl_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a : A) (l : list A) : incl l (set_add_simple eqdec a l).
Proof. hnf. intros. unfold set_add_simple. destruct (in_dec _ _ _); simpl; tauto. Qed.

Local Hint Resolve incl_set_add_simple : RBinv.

(*
Tactic Notation "decide_msg" constr(msg) "using_" constr(decider) "eqn_" ident(E) :=
  destruct (decider msg) eqn:E.
*)
Section State_Monotone_Proofs.

(* base state inv *)

Inductive state_mnt : State -> State -> Prop :=
  | MNT_sent : forall (st : State) r,
    st.(sent) r = false ->
    state_mnt st (st <| sent := map_update Round_eqdec r true st.(sent) |>)
  | MNT_echoed : forall (st : State) q r v, 
    st.(echoed) (q, r) = None ->
    state_mnt st (st <| echoed := map_update AddrRdPair_eqdec (q, r) (Some v) st.(echoed) |>)
  | MNT_msgcnt : forall (st : State) q msg,
    (match msg with InitialMsg _ _ => False | _ => True end) ->
    let: cnt := st.(msgcnt) in
    ~ In q (cnt msg) ->
    state_mnt st (st <| msgcnt := map_update Message_eqdec msg (q :: cnt msg) cnt |>)
  | MNT_voted : forall (st : State) q r v,
    st.(voted) (q, r) = None -> (* ignore the other condition *)
    state_mnt st (st <| voted := map_update AddrRdPair_eqdec (q, r) (Some v) st.(voted) |>)
  | MNT_output : forall (st : State) q r vs',
    (* ignore one condition *)
    let: omap := st.(output) in
    incl (omap (q, r)) vs' -> (* over approximation *)
    state_mnt st (st <| output := map_update AddrRdPair_eqdec (q, r) vs' omap |>)
.

(* TODO use a library for transitive closure? *)
Inductive state_mnt_star : bool -> State -> State -> Prop :=
  | MNTs_0 : forall st, state_mnt_star false st st
  | MNTs_S : forall b st st' st'',
    state_mnt st st' ->
    state_mnt_star b st' st'' ->
    state_mnt_star true st st''.

(* the two tactics below are certainly not generic, but enough here *)
(*
Ltac state_mnt_star_ l :=
  match l with
  | ?a :: ?l' => eapply MNTs_S; [ | state_mnt_star_ l' ]; eapply a; auto
  | _ => apply MNTs_0
  end.

Tactic Notation "state_mnt_star" uconstr(l) :=
  match l with
  | _ :: _ => exists true
  | _ => exists false
  end; state_mnt_star_ l.
*)
Tactic Notation "state_mnt_star" constr(kind) tactic(tac) :=
  eapply MNTs_S; [ apply kind | tac ]; simpl; auto.

(* Tactic Notation "state_mnt_star_2" constr(kind1) constr(kind2) :=
  exists true; eapply MNTs_S; [ apply kind1 | eapply MNTs_S; [ apply kind2 | apply MNTs_0 ] ]; auto. *)

Fact state_mnt_is_invariant q w w' (Hstep : system_step q w w') :
  forall n, exists b, state_mnt_star b (w @ n) (w' @ n).
Proof with (try (exists false; constructor)).
  inversion_step' Hstep; clear Hstep; intros...
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef.
    2: injection_pair Ef...
    destruct (w @ dst) as [ dst' sent echoed voted cnt output ].
    unfold procMsg in E.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; try discriminate.
      revert E Ef; intros [= <- <-] [= <- <-]. (* TODO made tactic? *)
      eexists; state_mnt_star MNT_echoed (apply MNTs_0).
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in E; try discriminate.
      revert E; intros [= <- <-].
      unfold routine_check in Ef; simpl in Ef.
      (* fine-grained discussion; avoid repetition as much as possible *)
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; injection_pair Ef; 
        [ destruct (voted (q, r)) eqn:?; try discriminate | ].
      3-4: destruct (Nat.leb _ _) eqn:? in |- *.
      all: eexists.
      all: match goal with 
        | |- context[set output _ _] => state_mnt_star MNT_output idtac
        | _ => idtac 
        end.
      all: first 
        [ state_mnt_star MNT_voted (state_mnt_star MNT_msgcnt (apply MNTs_0))
        | state_mnt_star MNT_msgcnt (apply MNTs_0)
        | idtac ].
      all: apply incl_set_add_simple.
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct t as [ r ].
    destruct (w @ n) as [ dst' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent r) eqn:?; injection_pair E...
    eexists; state_mnt_star MNT_sent (apply MNTs_0).
Qed.

(* use state_mnt as an over-approximation to prove some state-only invariants *)

Definition msgcnt_coh st : Prop :=
  forall msg,
    match msg with
    | InitialMsg _ _ => st.(msgcnt) msg = nil
    | _ => List.NoDup (st.(msgcnt) msg)
    end.

Definition lift_point_to_edge (P : State -> Prop) : State -> State -> Prop :=
  fun st st' => P st -> P st'.

Definition sent_persistent st st' : Prop :=
  forall r, st.(sent) r -> st'.(sent) r.

Definition echoed_persistent st st' : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v -> st'.(echoed) (q, r) = Some v.

Definition msgcnt_persistent st st' : Prop :=
  forall m q, In q (st.(msgcnt) m) -> In q (st'.(msgcnt) m).

Definition voted_persistent st st' : Prop :=
  forall q r v, st.(voted) (q, r) = Some v -> st'.(voted) (q, r) = Some v.

Definition output_persistent st st' : Prop :=
  forall q r v, In v (st.(output) (q, r)) -> In v (st'.(output) (q, r)).

(* TODO how to break/form invariants easily? *)
Record node_state_invariants st st' : Prop := {
  _ : lift_point_to_edge msgcnt_coh st st';
  _ : sent_persistent st st';
  _ : echoed_persistent st st';
  _ : msgcnt_persistent st st';
  _ : voted_persistent st st';
  _ : output_persistent st st';
}.

#[export] Instance Transitive_node_state_invariants : Transitive node_state_invariants.
Proof.
  hnf.
  intros ??? H H0.
  destruct H, H0.
  constructor.
  all: hnf in *; unfold msgcnt_coh in *.
  all: auto.
  all: firstorder.
Qed.

Fact invariants_pre_pre st st' (H : state_mnt st st') :
  node_state_invariants st st'.
Proof.
  constructor.
  all: hnf.
  1: unfold msgcnt_coh. (* ! *)
  all: intros; inversion H; subst; simpl; auto; (* heuristic *) try hypothesis.
  (* another layer of heuristic *)
  all: unfold map_update; destruct_eqdec as_ <-; simpl; auto; try hypothesis; try congruence.
  - destruct msg1; try contradiction.
    all: constructor; try assumption.
    apply (H0 (EchoMsg _ _ _)).
    apply (H0 (ReadyMsg _ _ _)).
Qed.

Fact invariants_pre st st' b (H : state_mnt_star b st st') :
  node_state_invariants st st'.
Proof.
  induction H.
  - constructor; hnf; auto.
  - apply invariants_pre_pre in H.
    etransitivity; eauto.
Qed.

Fact invariants q w w' (Hstep : system_step q w w') :
  forall n, node_state_invariants (w @ n) (w' @ n).
Proof.
  intros n.
  eapply state_mnt_is_invariant with (n:=n) in Hstep.
  destruct Hstep.
  eapply invariants_pre; eauto.
Qed.

End State_Monotone_Proofs.

Definition initialmsg_sent_fwd psent st : Prop :=
  forall r, st.(sent) r -> forall n, exists used, 
    In (mkP st.(id) n (InitialMsg r (value_bft st.(id) r)) used) psent.

Definition initialmsg_sent_bwd p stmap : Prop :=
  match p with
  | mkP src dst (InitialMsg r v) used =>
    is_byz src = false ->
      let: st := stmap src in
      st.(sent) r /\
      value_bft src r = v
  | _ => True
  end.

Definition initialmsg_recv_fwd psent st : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v ->
    In (mkP q st.(id) (InitialMsg r v) true) psent.

Definition initialmsg_recv_bwd p stmap : Prop :=
  match p with
  | mkP src dst (InitialMsg r v) true =>
    is_byz dst = false ->
      let: st := stmap dst in
      exists v', st.(echoed) (src, r) = Some v'
  | _ => True
  end.

Definition echomsg_sent_fwd psent st : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v -> forall n, exists used, 
    In (mkP st.(id) n (EchoMsg q r v) used) psent.

Definition echomsg_sent_bwd p stmap : Prop :=
  match p with
  | mkP src dst (EchoMsg q r v) used =>
    is_byz src = false ->
      let: st := stmap src in
      (* the only possibility of echoing is this *)
      st.(echoed) (q, r) = Some v
  | _ => True
  end.

Definition msgcnt_recv_fwd psent st : Prop :=
  forall m q, In q (st.(msgcnt) m) ->
    In (mkP q st.(id) m true) psent.

Definition msgcnt_recv_bwd p stmap : Prop :=
  match p with
  | mkP src dst m true =>
    match m with
    | EchoMsg _ _ _ | ReadyMsg _ _ _ =>
      is_byz dst = false ->
        let: st := stmap dst in
        In src (st.(msgcnt) m)
    | _ => True
    end
  | _ => True
  end.

Definition getready_coh st : Prop :=
  forall q r v, 
    st.(voted) (q, r) = Some v <->
    (th_echo4ready <= length (st.(msgcnt) (EchoMsg q r v)) \/ 
     th_ready4ready <= length (st.(msgcnt) (ReadyMsg q r v))).

Definition readymsg_sent_fwd psent st : Prop :=
  forall q r v, st.(voted) (q, r) = Some v -> forall n, exists used, 
    In (mkP st.(id) n (ReadyMsg q r v) used) psent.

Definition readymsg_sent_bwd p stmap : Prop :=
  match p with
  | mkP src dst (ReadyMsg q r v) used =>
    is_byz src = false ->
      let: st := stmap src in
      (* the only possibility of voting is this *)
      st.(voted) (q, r) = Some v
  | _ => True
  end.

Definition getoutput_coh st : Prop :=
  forall q r v, 
    In v (st.(output) (q, r)) <->
    th_ready4output <= length (st.(msgcnt) (ReadyMsg q r v)).

(* should be useful ... intensionally inductive? *)
(* serve as a way to tell that "at least some of the ready messages are the consequences of echo messages" *)
(* in paper proof, this invariant might be mentioned as "consider the first non-faulty node who broadcast
    ready messages"; but that would involve the notion of time, which is not convenient to formalize
    and use in the safety proofs *)

Definition echo_is_before_ready p psent : Prop :=
  match p with
  | mkP src dst (ReadyMsg q r v) used =>
    is_byz src = false ->
      exists src' dst', is_byz src' = false /\ 
        In (mkP src' dst' (EchoMsg q r v) true) psent
  | _ => True
  end.

Definition integrity w : Prop :=
  forall p q r v, 
    is_byz p = false -> is_byz q = false ->
    In v ((localState w p).(output) (q, r)) ->
    (localState w q).(sent) r /\ value_bft q r = v.


End Main_Proof.

End RBInvariant.
