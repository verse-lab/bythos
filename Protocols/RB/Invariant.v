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

Tactic Notation "destruct_localState" ident(w) ident(n) 
  "as_" simple_intropattern(pat) "eqn_" ident(E) :=
  match goal with 
  | H : ?P |- _ =>
    change P with (forall pp : nat, id (w @ pp) = pp); (* convertible checked here *)
    let Htmp := fresh "Htmp" in
    pose proof (H n) as Htmp;
    destruct (w @ n) as pat eqn:E; 
    simpl in Htmp; 
    match type of Htmp with ?nn = _ => subst nn end
  end.

Tactic Notation "destruct_localState" ident(w) ident(n) "as_" simple_intropattern(pat) :=
  let E := fresh "E" in
  destruct_localState w n as_ pat eqn_ E; clear E.

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

Tactic Notation "destruct_eqdec_raw" constr(eqdec) constr(a) constr(b) simple_intropattern(pat) :=
  match type of eqdec with
    forall _ : _, forall _ : _, sumbool (eq _ _) (not (eq _ _)) =>
    destruct (eqdec a b) as [ pat | ] +
    destruct (eqdec a b) as [ | ]
  end.

Tactic Notation "destruct_eqdec" "in_" hyp(H) "as_" simple_intropattern(pat) :=
  repeat match type of H with
    context[if ?eqdec ?a ?b then _ else _] => destruct_eqdec_raw eqdec a b pat
  end.

Tactic Notation "destruct_eqdec" "as_" simple_intropattern(pat) :=
  repeat match goal with
    |- context[if ?eqdec ?a ?b then _ else _] => destruct_eqdec_raw eqdec a b pat
  end.

Tactic Notation "destruct_eqdec!" "as_" simple_intropattern(pat) :=
  repeat match goal with 
  | H : context[if ?eqdec ?a ?b then _ else _] |- _ => destruct_eqdec_raw eqdec a b pat
  end; try destruct_eqdec as_ pat.

Tactic Notation "pick" constr(def) "as_" ident(H) :=
  first
  [ match goal with
    | H0 : def _ |- _ => rename H0 into H
    | H0 : def _ _ |- _ => rename H0 into H
    | H0 : def _ _ _ |- _ => rename H0 into H
    end
  | match goal with
    | H0 : context[def] |- _ => rename H0 into H; hnf in H
    end ];
  unfold def in H.

(* TODO need improvement *)
Tactic Notation "pick" constr(def) "as_" ident(H) "by_" tactic2(tac) :=
  let a := fresh "eprop" in
  evar (a : Prop); assert a as H; subst a; [ tac; pick def as_ H; exact H | ].

(* HMM more aggressive (plus backtracking) version? *)
Tactic Notation "saturate_assumptions" :=
  repeat match goal with
    H : ?P -> ?Q |- _ => 
    match type of P with
      Prop => specialize (H ltac:(try apply I; try reflexivity; assumption))
    end
  end.

Create HintDb RBinv.

Tactic Notation "basic_solver" :=
  try reflexivity; auto with RBinv; try tauto; try eqsolve; try lia.

Fact incl_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a : A) (l : list A) : incl l (set_add_simple eqdec a l).
Proof. hnf. intros. unfold set_add_simple. destruct (in_dec _ _ _); simpl; tauto. Qed.

Fact In_set_add_simple {A : Type} (eqdec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
  (a a' : A) (l : list A) : In a' (set_add_simple eqdec a l) <-> a = a' \/ In a' l.
Proof. unfold set_add_simple. destruct (in_dec _ _ _); simpl; eqsolve. Qed.

Local Hint Resolve incl_set_add_simple : RBinv.

Local Hint Resolve incl_sendout_l incl_sendout_r : psent.

Section State_Monotone_Proofs.

(* materialize *)
(* carrying proofs? seems OK, as long as it will never be used in equality proofs *)
Inductive state_mnt_type (st : State) : Type :=
  | Msent : forall r,
    st.(sent) r = false -> state_mnt_type st
  | Mechoed : forall q r (v : Value), 
    st.(echoed) (q, r) = None -> state_mnt_type st
  | Mmsgcnt : forall q msg,
    (match msg with InitialMsg _ _ => False | _ => True end) ->
    let: cnt := st.(msgcnt) in
    ~ In q (cnt msg) -> state_mnt_type st
  | Mvoted : forall q r v,
    st.(voted) (q, r) = None ->
    (* TODO is this useful anymore? *)
    (th_echo4ready <= S (length (st.(msgcnt) (EchoMsg q r v))) \/
     th_ready4ready <= S (length (st.(msgcnt) (ReadyMsg q r v)))) -> state_mnt_type st
  | Moutput : forall q r vs',
    let: omap := st.(output) in
    incl (omap (q, r)) vs' -> (* over approximation; actually it should be set_add *)
    state_mnt_type st
.

Global Arguments Moutput : clear implicits.

(* as a function, directly? *)
Definition state_mnt (st : State) (s : state_mnt_type st) : State :=
  match s with
  | Msent _ r _ =>
    (st <| sent := map_update Round_eqdec r true st.(sent) |>)
  | Mechoed _ q r v _ =>
    (st <| echoed := map_update AddrRdPair_eqdec (q, r) (Some v) st.(echoed) |>)
  | Mmsgcnt _ q msg _ _ =>
    let: cnt := st.(msgcnt) in
    (st <| msgcnt := map_update Message_eqdec msg (q :: cnt msg) cnt |>)
  | Mvoted _ q r v _ _ =>
    (st <| voted := map_update AddrRdPair_eqdec (q, r) (Some v) st.(voted) |>)
  | Moutput _ q r vs' _ =>
    let: omap := st.(output) in
    (st <| output := map_update AddrRdPair_eqdec (q, r) vs' omap |>)
  end.

(* here, psent refers to the updated packet soup. HMM do we need to include the original one? *)
(* "n" is the external address observed from the network point of view, which will be used
    by packet delivery, for instance *)
Definition psent_effect (st : State) (s : state_mnt_type st) (n : Address) (psent : PacketSoup) : Prop :=
  match s with
  | Msent _ r _ =>
    incl (broadcast st.(id) (InitialMsg r (value_bft st.(id) r))) psent
  | Mechoed _ q r v _ =>
    In (mkP q n (InitialMsg r v) true) psent /\
    incl (broadcast st.(id) (EchoMsg q r v)) psent
  | Mmsgcnt _ q msg _ _ =>
    In (mkP q n msg true) psent
  | Mvoted _ q r v _ _ =>
    incl (broadcast st.(id) (ReadyMsg q r v)) psent
  | Moutput _ q r vs' _ => True
  end.

(* hmm, need dependent list in this case *)

Inductive state_mnt_type_list : State -> State -> Type :=
  | MNTnil : forall st, state_mnt_type_list st st
  | MNTcons : forall st (d : state_mnt_type st) st', 
    state_mnt_type_list (state_mnt d) st' ->
    state_mnt_type_list st st'.

(*
(* HMM the backwards one is more intuitive? *)
Inductive state_mnt_type_list : State -> State -> Type :=
  | MNTnil : forall st, state_mnt_type_list st st
  | MNTcons : forall st st' (d : state_mnt_type st'), 
    state_mnt_type_list st st' ->
    state_mnt_type_list st (state_mnt d).
*)
(* from the experience in the backward proofs, it seems beneficial to write this as a recursive function
    instead of an inductive predicate *)

(* an over-approx of the effect over psent? since it can say nothing about psent *)
Fixpoint psent_effect_star (n : Address) (psent : PacketSoup) [st st'] (l : state_mnt_type_list st st') : Prop :=
  match l with
  | MNTnil _ => True
  | MNTcons d l' =>
    psent_effect d n psent /\ psent_effect_star n psent l' (* TODO setting implicit during definition? *)
  end.

Local Ltac state_analyze_select f :=
  match f with
  | sent => uconstr:(Msent)
  | echoed => uconstr:(Mechoed)
  | voted => uconstr:(Mvoted)
  | msgcnt => uconstr:(Mmsgcnt)
  | output => uconstr:(Moutput)
  end.

(* need to add st' as an argument, since the size of state components in the goal will only increase;
    so do recursion on the st' here *)
Ltac state_analyze' st' :=
  match st' with
  | set ?f _ ?st =>
    let ctor := state_analyze_select f in
    unshelve eapply MNTcons; [ eapply ctor; try eassumption | ]; 
      simpl; state_analyze' st
  | _ => try solve [ apply (MNTnil _) ]
  end.

Ltac psent_effect_star_solver :=
  (* mostly heuristics *)
  simpl; autorewrite with psent; simpl; auto using incl_set_add_simple with psent; 
  try solve [ intuition (auto using incl_set_add_simple with psent) ].

Ltac state_analyze :=
  try rewrite sendout0;
  match goal with
  | |- exists (_ : state_mnt_type_list _ ?st'), _ =>
    unshelve eexists; [ state_analyze' st' | ];
    match goal with
    | |- @psent_effect_star _ _ _ _ _ => psent_effect_star_solver
    | _ => basic_solver
    end
  end.

Local Hint Rewrite -> In_consume : psent.

(* for each node (ignoring whether faulty/non-faulty here),
    the change of its local state satisfies some pattern, 
    so does the effect that this change has over the packet soup *)

Fact state_mnt_sound q w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n), 
    psent_effect_star n (sentMsgs w') l.
Proof with (try (now exists (MNTnil _))).
  inversion_step' Hstep; clear Hstep; intros...
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef.
    2: injection_pair Ef...
    destruct (w @ dst) as [ dst' sent echoed voted cnt output ].
    unfold procMsg in E.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; try discriminate. simplify_eq.
      state_analyze.
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in E; try discriminate. simplify_eq.
      unfold routine_check in Ef. simpl in Ef.
      (* fine-grained discussion; avoid repetition as much as possible *)
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; injection_pair Ef; 
        [ apply andb_true_iff in EE; destruct EE as (EE & Eth%Nat.leb_le),
            (voted (q, r)) eqn:?; try discriminate | ].
      3-4: destruct (Nat.leb _ _) eqn:Eth2 in |- *; [ apply Nat.leb_le in Eth2 | ].
      all: state_analyze.
      all: unfold map_update in Eth; rewrite eqdec_refl in Eth; simpl in Eth; auto.
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct t as [ r ].
    destruct (w @ n) as [ dst' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent r) eqn:?; injection_pair E...
    state_analyze.
Qed.

(* use state_mnt as an over-approximation to prove some state-only invariants *)

Definition msgcnt_coh st : Prop :=
  forall msg,
    match msg with
    | InitialMsg _ _ => st.(msgcnt) msg = nil
    | _ => List.NoDup (st.(msgcnt) msg)
    end.

Definition lift_point_to_edge {A : Type} (P : A -> Prop) : A -> A -> Prop :=
  fun st st' => P st -> P st'.

Definition sent_persistent st st' : Prop := Eval unfold lift_point_to_edge in
  forall r, st.(sent) r -> st'.(sent) r.

Definition echoed_persistent st st' : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v -> st'.(echoed) (q, r) = Some v.

Definition msgcnt_persistent st st' : Prop :=
  forall m q, In q (st.(msgcnt) m) -> In q (st'.(msgcnt) m).

Definition voted_persistent st st' : Prop :=
  forall q r v, st.(voted) (q, r) = Some v -> st'.(voted) (q, r) = Some v.

Definition output_persistent st st' : Prop :=
  forall q r v, In v (st.(output) (q, r)) -> In v (st'.(output) (q, r)).

(* let's prove id_coh here ... *)

Definition id_persistent st st' : Prop := st.(id) = st'.(id).

(* TODO how to break/form invariants easily? *)
Record node_state_invariants st st' : Prop := {
  _ : lift_point_to_edge msgcnt_coh st st';
  _ : sent_persistent st st';
  _ : echoed_persistent st st';
  _ : msgcnt_persistent st st';
  _ : voted_persistent st st';
  _ : output_persistent st st';
  _ : id_persistent st st';
}.

#[export] Instance Transitive_node_state_invariants : Transitive node_state_invariants.
Proof.
  hnf. intros ??? H H0. destruct H, H0. constructor.
  all: hnf; intuition.
  - congruence.
Qed.

Fact state_invariants_pre_pre st (d : state_mnt_type st) :
  node_state_invariants st (state_mnt d).
Proof.
  constructor.
  all: hnf; unfold msgcnt_coh.
  (* heuristics: auto; if auto does not work then eauto; hypothesis has what you need *)
  all: intros; destruct d; subst; simpl in *; eauto; try hypothesis.
  (* another layer of heuristic *)
  all: unfold map_update; destruct_eqdec as_ ->; simpl in *; eauto; try hypothesis; try congruence.
  - destruct msg0; try contradiction.
    all: constructor; try assumption.
    apply (H (EchoMsg _ _ _)).
    apply (H (ReadyMsg _ _ _)).
Qed.

Fact state_invariants_pre st st' (l : state_mnt_type_list st st') :
  node_state_invariants st st'.
Proof.
  induction l.
  - constructor; hnf; auto.
  - pose proof (state_invariants_pre_pre d).
    etransitivity; eauto.
Qed.

(* TODO is this wrapper actually useful? *)
Definition lift_state_pair_inv (P : State -> State -> Prop) : World -> World -> Prop :=
  fun w w' => forall n, P (w @ n) (w' @ n).

Fact state_invariants q w w' (Hstep : system_step q w w') :
  lift_state_pair_inv node_state_invariants w w'.
Proof.
  intros n.
  eapply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & _).
  eapply state_invariants_pre; eauto.
Qed.

Definition id_coh w : Prop := forall n, (w @ n).(id) = n.

Fact id_coh_is_invariant : is_invariant_step id_coh.
Proof.
  hnf; intros ??? H Hstep.
  hnf in H |- *; intros n; specialize (H n).
  apply state_invariants in Hstep. hnf in Hstep. specialize (Hstep n).
  destruct Hstep; hnf in *; congruence.
Qed.

(* length is also monotonic, but can be reduced to In + NoDup, so it is not included above *)

(* implication-shaped invariants *)
(* the above are pointed *)

(* the following three must be grouped together! otherwise cannot be proved *)

Definition getready_coh_fwd st : Prop :=
  forall q r v, 
    st.(voted) (q, r) = Some v ->
    (th_echo4ready <= length (st.(msgcnt) (EchoMsg q r v)) \/ 
     th_ready4ready <= length (st.(msgcnt) (ReadyMsg q r v))).

Definition getready_coh_bwd1 st : Prop :=
  forall q r v, 
    (*
    th_echo4ready <= length (st.(msgcnt) (EchoMsg q r v)) ->
    (* exists v', st.(voted) (q, r) = Some v'. *)
    (* use isSome *)
    st.(voted) (q, r).
    *)
    (* or ...? *)
    st.(voted) (q, r) = None ->
    length (st.(msgcnt) (EchoMsg q r v)) < th_echo4ready.

Definition getready_coh_bwd2 st : Prop :=
  forall q r v, 
    (*
    th_ready4ready <= length (st.(msgcnt) (ReadyMsg q r v)) ->
    (* exists v', st.(voted) (q, r) = Some v'. *)
    st.(voted) (q, r).
    *)
    st.(voted) (q, r) = None ->
    length (st.(msgcnt) (ReadyMsg q r v)) < th_ready4ready.

Definition getoutput_coh st : Prop :=
  forall q r v, 
    In v (st.(output) (q, r)) <->
    th_ready4output <= length (st.(msgcnt) (ReadyMsg q r v)).

Record node_state_invariants_2 st st' : Prop := {
  _ : lift_point_to_edge (fun st0 => getready_coh_fwd st0 /\ getready_coh_bwd1 st0 /\
      getready_coh_bwd2 st0) st st';
  _ : lift_point_to_edge getoutput_coh st st';
}.

Tactic Notation "solvetac" tactic(tac) :=
  constructor; hnf; unfold getready_coh_fwd, getready_coh_bwd1, getready_coh_bwd2, getoutput_coh; tac.

#[export] Instance Reflexive_node_state_invariants_2 : Reflexive node_state_invariants_2.
Proof. solvetac auto. Qed.

(* let's try proving the things above directly, to see whether direct style proving is indeed difficult *)
(* the proof skeleton is basically the same *)
Fact invariants_2 q w w' (Hstep : system_step q w w') :
  forall n, node_state_invariants_2 (w @ n) (w' @ n).
Proof.
  intros n.
  inversion_step' Hstep; clear Hstep; intros; try reflexivity.
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]; [ | reflexivity ].
    destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef.
    2: injection_pair Ef; reflexivity.
    destruct (w @ dst) as [ dst' sent echoed voted cnt output ].
    unfold procMsg in E.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; try discriminate.
      revert E Ef; intros [= <- <-] [= <- <-].
      solvetac auto.
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in E; try discriminate.
      revert E; intros [= <- <-].
      unfold routine_check in Ef; simpl in Ef.
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; injection_pair Ef; 
        [ apply andb_true_iff in EE; destruct EE as (EE & Eth%Nat.leb_le),
            (voted (q, r)) eqn:?; try discriminate 
        | apply andb_false_iff in EE; rewrite Nat.leb_gt in EE ].
      3-4: destruct (Nat.leb _ _) eqn:Eth2 in |- *; 
        [ apply Nat.leb_le in Eth2 | apply Nat.leb_nle in Eth2 ].
      all: solvetac
        (match goal with |- (_ /\ _ /\ _) -> _ => intros (Ha & Hb & Hc) | _ => intros H end;
          intros; split_and?; intros;
        simpl in *; unfold map_update in *; destruct_eqdec! as_ ?; simplify_eq;
        simpl in *; try solve [ eauto | tauto | intuition ]).
      all: try rewrite In_set_add_simple in *.
      all: try solve 
        [ rewrite H; split; auto; lia (* for th_ready4output goals without v = v *)
        | rewrite H; eqsolve (* for th_ready4output goals with v = v *)
        | rewrite H in EE; simpl in EE; eqsolve (* for lt goals *)
        | match goal with
          | |- context[?n1 <= S ?n2] => pose proof (fun H => Nat.le_trans n1 _ _ H (le_S _ _ (le_n n2)))
          end; firstorder (* for le or le goals *) ].
  - unfold upd.
    destruct (Address_eqdec _ _) as [ -> | Hneq ]; try reflexivity.
    destruct t as [ r ].
    destruct (w @ n) as [ dst' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent r) eqn:?; injection_pair E; try reflexivity.
    solvetac auto.
Qed.

End State_Monotone_Proofs.

(* TODO naming issue: the "forward"/"backward" invariants should be named as 
    local to global/global to local invariants to avoid confusion with
    the "forward"/"backward" reasoning styles *)

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
      (* exists v', st.(echoed) (src, r) = Some v' *)
      st.(echoed) (src, r)
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
  (* | mkP src dst m true => *)
  | mkP src dst (EchoMsg _ _ _) true
  | mkP src dst (ReadyMsg _ _ _) true =>
    (* match m with
    | EchoMsg _ _ _ | ReadyMsg _ _ _ => *)
      is_byz dst = false ->
        let: st := stmap dst in
        In src (st.(msgcnt) p.(msg))
    (* | _ => True
    end *)
  | _ => True
  end.

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

Section Forward.

Definition lift_node_inv (P : PacketSoup -> State -> Prop) : World -> Prop :=
  fun w => forall n, is_byz n = false -> P (sentMsgs w) (w @ n).
  (* essentially, making a big conjunction over all non-faulty nodes *)

Record node_psent_fwd_invariants psent st : Prop := {
  _ : initialmsg_sent_fwd psent st;
  _ : initialmsg_recv_fwd psent st;
  _ : echomsg_sent_fwd psent st;
  _ : msgcnt_recv_fwd psent st;
  _ : readymsg_sent_fwd psent st;
}.

(* TODO generalize to arbitrary bundle? *)
Tactic Notation "saturate" :=
  match goal with
    Hstep : system_step _ _ _ |- _ =>
    pose proof (state_invariants Hstep) as Hinv; 
    match goal with
      H : context[localState _ ?n] |- _ =>
      is_var n; specialize (Hinv n); destruct Hinv
    end
  end.

(* while you can certainly prove these individually, proving them together can save some time *)
(* this proof would depend on id_coh to unify the internal/external identifiers *)
Fact fwd_invariants : is_invariant_step (fun w => id_coh w /\ lift_node_inv node_psent_fwd_invariants w).
Proof.
  hnf; intros qq ?? (Hcoh & H) Hstep.
  apply and_wlog_r; [ eapply id_coh_is_invariant; eauto | intros Hcoh' ].
  unfold lift_node_inv in *.
  intros n Hnonbyz; specialize (H _ Hnonbyz).
  specialize (Hcoh n); specialize (Hcoh' n). (* unify *)
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & Hpsent).
  (* need to make the invariant clause one-to-one *)
  (* TODO why? can I explain? *)
  constructor.
  all: match goal with |- ?def _ _ => pick def as_ H' by_ (destruct H); clear H; rename H' into H end.
  all: hnf; rewrite Hcoh in *; rewrite Hcoh' in *.
  (* TODO how can this be automated? want something like param_sync *)
  1: intros r; specialize (H r).
  2-3,5: intros q r v; specialize (H q r v).
  5: intros m q; specialize (H m q).
  all: intros.
  all: revert H; induction l as [ st | st d st' l IH ]; intros.
  all: (* all MNTnil (under-specified) cases *)
    try solve 
    [ eapply system_step_psent_norevert_full; eauto
    | eapply system_step_psent_persistent_weak_full; eauto ].
  all: simpl in Hpsent; destruct Hpsent as (Hpsent & HH).
  all: destruct d; simpl in Hpsent, IH, (type of l); saturate_assumptions; try tauto.
  all: unfold map_update in *; destruct_eqdec! as_ ?; simplify_eq (* also simplifies id_coh *); 
    simpl in IH; try tauto.
  all: try solve
    [ exists false; apply Hpsent, In_broadcast; eauto (* for simple *)
    | destruct (Value_eqdec v0 v) as [ -> | ]; (* for those involve value *)
      try solve [ tauto | eqsolve | exists false; apply Hpsent, In_broadcast; eauto ]
      (* we can show that the value echoed/voted this time is the same as the final one, 
          but it's not necessary *)
    | destruct (Address_eqdec q0 q) as [ -> | ]; try solve [ tauto | eqsolve ] ].
Qed.

End Forward.

Section Backward.

(* the state-major view is useful, but we also need a packetsoup-major view *)

Inductive psent_mnt_type_base (psent : PacketSoup) : Type :=
  | Pid : psent_mnt_type_base psent
  | Puse : forall p, In p psent -> psent_mnt_type_base psent
.

(* intended to be in a module type, or something, provided by user *)
Inductive packets_shape_user : Type := PSUbcast (n : Address) (m : Message).

Inductive packets_shape : Type := PSHuser (psu : packets_shape_user) | PSHbyz (p : Packet).

Definition packets_shape_consistent (ps : packets_shape) (pkts : list Packet) : Prop :=
  match ps with
  | PSHuser (PSUbcast n m) => pkts = broadcast n m
  | PSHbyz p => pkts = p :: nil (* TODO too simple? *)
  end.

(* a list *)
Inductive psent_mnt_type : PacketSoup -> Type :=
  | Pbase : forall psent, psent_mnt_type_base psent -> psent_mnt_type psent
  | Pcons : forall pkts ps,
    Forall (fun p => p.(consumed) = false) pkts ->
    packets_shape_consistent ps pkts ->
    forall psent, psent_mnt_type psent -> psent_mnt_type psent
  (* HMM since we are proving, do not consider sendout1 ...? *)
.

Global Arguments Pbase : clear implicits.
Global Arguments Pcons : clear implicits.

Definition psent_mnt_base psent (s : psent_mnt_type_base psent) : PacketSoup :=
  match s with
  | Pid _ => psent
  | Puse _ p _ => consume p psent
  end.

Fixpoint psent_mnt psent (l : psent_mnt_type psent) psent' : Prop :=
  match l with
  | Pbase _ b => psent' = psent_mnt_base b
  | Pcons pkts _ _ _ _ l => exists psent_, psent_mnt l psent_ /\ Ineq psent' (sendout pkts psent_)
  end.

Definition state_effect_bcast (n : Address) (m : Message) (stmap : StateMap) : Prop :=
  match m with
  | InitialMsg r v => value_bft n r = v /\ (stmap n).(sent) r
  | EchoMsg q r v => (stmap n).(echoed) (q, r) = Some v
  | ReadyMsg q r v => (stmap n).(voted) (q, r) = Some v
  end.

Definition state_effect_recv (src n : Address) (m : Message) (stmap : StateMap) : Prop :=
  match m with
  | InitialMsg r _ => (stmap n).(echoed) (src, r)
  | EchoMsg _ _ _ | ReadyMsg _ _ _ => In src ((stmap n).(msgcnt) m)
  end.

(* here, stmap refers to the updated state map *)
(* it seems not quite useful to constrain on the original state map *)
(* writing this as an inductive prop will make inversion difficult;
    for example, inverting "state_effect stmap (Pcons pkts H psent l)" will not give "state_effect stmap l", 
    due to some weird reason ...
  use another way to constrain the shape of pkts, instead *)

(* TODO if this works, consider how to distribute the constraints here and in "psent_mnt_type"
    of course, constraints involving stmap must be here *)
Fixpoint state_effect [psent : PacketSoup] (stmap : StateMap) (l : psent_mnt_type psent) : Prop :=
  match l with
  | Pbase _ b =>
    match b with
    | Pid _ => True (* under-specified *)
    | Puse _ (mkP src n m used) _ => is_byz n = false /\ state_effect_recv src n m stmap
    end
  | Pcons pkts ps _ _ psent' l' =>
    state_effect stmap l' /\ (* putting this here can be convenient *)
    match ps with
    | PSHuser (PSUbcast n m) => is_byz n = false /\ state_effect_bcast n m stmap
    | PSHbyz p => is_byz p.(src) /\ byz_constraints p.(msg) (mkW stmap psent) /\ l' = Pbase _ (Pid _)
    end
  end.

Local Hint Extern 100 (is_true (isSome ?a)) => 
  (match goal with
  | H : ?a = _ |- _ => rewrite H
  end) : RBinv.

Ltac state_effect_solve :=
  match goal with
  | |- @state_effect _ _ _ => simpl; eauto; 
    repeat (first [ rewrite upd_refl; simpl | rewrite map_update_refl; simpl ]);
    auto with RBinv (* use the above heuristic tactic *)
  | _ => idtac
  end.

(* TODO this also seems customizable *)
Ltac psent_analyze' psent' :=
  match psent' with
  | consume ?p ?psent => uconstr:(Pbase psent (Puse psent p ltac:(assumption)))
  | sendout (?pkts1 ++ ?pkts2) ?psent_ =>
    let ss := psent_analyze' constr:(sendout pkts1 psent_) in
    match pkts2 with
    | broadcast ?n ?m => uconstr:(Pcons pkts2 (PSHuser (PSUbcast n m)) (broadcast_all_fresh n m) eq_refl _ ss)
    end
  | sendout ?pkts ?psent_ => 
    let ss := psent_analyze' constr:(psent_) in
    match pkts with
    | broadcast ?n ?m => uconstr:(Pcons pkts (PSHuser (PSUbcast n m)) (broadcast_all_fresh n m) eq_refl _ ss)
    end
  | sendout1 ?p ?psent_ => 
    (* let ss := psent_analyze' constr:(psent_) in *)
    (* early terminate *)
    uconstr:(Pcons (p :: nil) (PSHbyz p) ltac:(now constructor) eq_refl _ (Pbase _ (Pid psent_)))
  | _ => uconstr:(Pbase _ (Pid psent'))
  end.

Ltac psent_mnt_solve :=
  match goal with
  (*
  | |- exists (_ : _), _ = _ /\ _ => 
    eexists; split; (* TODO appending anything after the semicolon here will result in non-termination? *)
    *)
  | |- exists (_ : _), _ = ?psent /\ _ => exists psent; split; 
    (* [ reflexivity | solve [ reflexivity (*| intros ?; autorewrite with psent; tauto ]*) ] ] *)
    (* does not work ... *)
    [ reflexivity | ];
    first [ reflexivity | intros ?; autorewrite with psent; simpl; tauto | idtac ]
    (* why the last tactic may not work? *)
  | |- exists (_ : _), (exists _, _) /\ _ => 
    eexists; split; [ psent_mnt_solve | intros ?; autorewrite with psent ]; try tauto
  | _ => idtac
  end.

Ltac psent_analyze :=
  (* let l := fresh "l" in *)
  try rewrite sendout0;
  match goal with
  | |- exists (_ : ?t), psent_mnt _ ?psent' /\ _ =>
    let l := psent_analyze' psent' in
    unshelve eexists l;
    match goal with
    | |- psent_mnt _ ?psent' /\ _ => 
      split; [ simpl; auto; psent_mnt_solve | state_effect_solve ]
    (* | _ => try apply broadcast_all_fresh *)
    | _ => idtac
    end
    (* evar (l : t); exists l;
    split; [ try rewrite sentout0; psent_analyze' l | ] *)
  end.

Fact psent_mnt_sound q w w' (Hstep : system_step q w w') 
  (Hcoh : id_coh w) (* still needed *) :
  exists l : psent_mnt_type (sentMsgs w),
    psent_mnt l (sentMsgs w') /\ state_effect (localState w') l.
Proof.
  inversion_step' Hstep; clear Hstep; intros.
  - psent_analyze.
  - (* the case analysis is slightly different; the None case needs to be discussed now *)
    destruct_localState w dst as_ [ dst' sent echoed voted cnt output ].
    unfold procMsg in Ef.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; simplify_eq.
      all: psent_analyze.
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in Ef.
      1: simplify_eq; destruct msg; try discriminate; psent_analyze.
      unfold routine_check in Ef; simpl in Ef.
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; injection_pair Ef; 
        [ apply andb_true_iff in EE; destruct EE as (EE & Eth%Nat.leb_le),
            (voted (q, r)) eqn:?; try discriminate | ].
      3-4: destruct (Nat.leb _ _) eqn:Eth2 in |- *; [ apply Nat.leb_le in Eth2 | ].
      all: psent_analyze.
  - destruct t as [ r ].
    destruct_localState w n as_ [ n' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent r) eqn:?; simplify_eq.
    all: psent_analyze.
  - (* TODO the bug happens here ... *)
    psent_analyze. (* ???? *)
    intros ?; autorewrite with psent; simpl; tauto.
Qed.

Definition lift_pkt_inv (P : Packet -> StateMap -> Prop) : PacketSoup -> StateMap -> Prop :=
  fun psent stmap => forall p, In p psent -> P p stmap.

(* this bunch can pass the base case easily, since it does no work for existing packets *)
Record node_psent_bwd_invariants_sent p stmap : Prop := {
  _ : initialmsg_sent_bwd p stmap;
  _ : echomsg_sent_bwd p stmap;
  _ : readymsg_sent_bwd p stmap;
}.

(* this bunch can pass the cons case easily, since it does no work for fresh packets *)
Record node_psent_bwd_invariants_recv p stmap : Prop := {
  _ : initialmsg_recv_bwd p stmap;
  _ : msgcnt_recv_bwd p stmap;
}.

Fact bwd_invariants_id_pre q w w' (Hstep : system_step q w w') p :
  (node_psent_bwd_invariants_sent p (localState w) ->
  forall used, node_psent_bwd_invariants_sent (mkP p.(src) p.(dst) p.(msg) used) (localState w')) /\
  (node_psent_bwd_invariants_recv p (localState w) ->
  node_psent_bwd_invariants_recv p (localState w')).
Proof.
  destruct p as [ src dst msg used ].
  pose proof (state_invariants Hstep) as Hinv. (* use persistent properties to solve *)
  split; intros H.
  1: intros used'; simpl.
  all: constructor.
  all: match goal with |- ?def _ _ => pick def as_ H' by_ (destruct H); clear H; rename H' into H;
    unfold def end.
  all: destruct msg, used; try exact I.
  all: pose proof (Hinv src) as []; pose proof (Hinv dst) as []; intuition.
  (* TODO this is bad. *)
  match goal with 
    H : is_true (isSome (?f ?st ?key)), H0 : context[?st] |- is_true (isSome _) => 
    destruct (f st key) eqn:E in H; try discriminate; apply H0 in E; auto with RBinv
  end.
Qed.

Corollary bwd_invariants_id q w w' (Hstep : system_step q w w') psent :
  (lift_pkt_inv node_psent_bwd_invariants_sent psent (localState w) ->
  lift_pkt_inv node_psent_bwd_invariants_sent psent (localState w')) /\
  (lift_pkt_inv node_psent_bwd_invariants_recv psent (localState w) ->
  lift_pkt_inv node_psent_bwd_invariants_recv psent (localState w')).
Proof.
  split; intros H; hnf in H |- *; intros [ src dst msg used ] Hin; specialize (H _ Hin).
  all: now eapply (bwd_invariants_id_pre Hstep _) in H; eauto.
Qed.

Fact bwd_invariants :
  is_invariant_step (fun w => id_coh w /\ (* needed, since will use psent_mnt_sound *)
    (lift_pkt_inv node_psent_bwd_invariants_sent (sentMsgs w) (localState w)
      /\ lift_pkt_inv node_psent_bwd_invariants_recv (sentMsgs w) (localState w))).
Proof.
  hnf; intros q ?? (Hcoh & H) Hstep.
  apply and_wlog_r; [ eapply id_coh_is_invariant; eauto | intros Hcoh' ].
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply psent_mnt_sound in Hstep; try assumption.
  destruct Hstep as (l & Hpsent & Hse).
  remember (sentMsgs w') as psent' eqn:Htmp; clear Htmp. (* TODO generalize? *)
  revert psent' Hpsent H. 
  induction l as [ psent (* implicitly generalized *) b | pkts ps Hf Hcheck psent l IH ]; intros.
  all: simpl in Hse, Hpsent.
  (* TODO why we do not need to destruct H here (and only need to destruct later)? can I explain? *)
  - destruct b as [ | p' Hin' ]; simpl in Hpsent; subst psent'.
    1: split; now apply (bwd_invariants_id Hstep_ psent).
    split; [ apply proj1 in H | apply proj2 in H ].
    + hnf in H |- *. intros [ src dst msg used ] Hin. 
      apply (In_consume_conv_full Hin') in Hin. destruct Hin as (used' & Hin).
      specialize (H _ Hin).
      eapply (bwd_invariants_id_pre Hstep_ _) in H. simpl in H. exact H.
    + (* check which packet is consumed this time *)
      destruct p' as [ src' dst' msg' used' ].
      hnf in H |- *. intros p Hin%In_consume. simpl in Hin.
      destruct Hin as [ <- | (Hin & _) ].
      2: specialize (H _ Hin).
      1: destruct used'; [ specialize (H _ Hin') | ].
      1,3: eapply (bwd_invariants_id_pre Hstep_ _) in H; simpl in H; exact H.
      (* interesting part *)
      clear H. destruct Hse as (Hnonbyz & Hr).
      destruct msg' as [ r' v' | q' r' v' | q' r' v' ]; simpl in Hr.
      all: constructor; try exact I.
      all: hnf; simpl; auto.
  - destruct Hpsent as (psent_ & Hpmnt & Hineq), Hse as (He & Hse).
    specialize (IH He _ Hpmnt H). clear H.
    split; [ apply proj1 in IH | apply proj2 in IH ].
    all: hnf in IH |- *; intros pp Hin%Hineq; autorewrite with psent in Hin.
    all: destruct Hin as [ Hin | ]; [ | intuition ].
    + destruct ps as [ [ n m ] | pb ]; simpl in Hcheck; subst pkts.
      1: destruct Hse as (Hnonbyz & Hb).
      2: destruct Hse as (Hbyz & Hc & ->); simpl in Hpmnt; subst psent_.
      * (* interesting part *)
        apply In_broadcast in Hin. destruct Hin as (dst & ->).
        constructor.
        all: hnf; destruct m as [ r v | qq r v | qq r v ]; simpl in Hb; intuition.
      * destruct pp as [ ? ? msg ? ], Hin as [ -> | [] ]; try intuition.
        simpl in Hbyz.
        constructor.
        all: hnf; destruct msg as [ r v | qq r v | qq r v ]; intros; eqsolve.
    + rewrite -> Forall_forall in Hf. apply Hf in Hin. destruct pp as [ ? ? mm ? ]. simpl in Hin. subst.
      constructor; destruct mm; apply I.
Qed.

End Backward.

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
