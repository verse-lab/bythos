From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.RB Require Export Network.
From Bythos.Properties Require Import Invariant.

Module RBInvariant (A : NetAddr) (R : Round) (V : Value) (VBFT : ValueBFT A R V)
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh).

Import A R V VBFT BTh BSett.
Import ssrbool. (* anyway *)

Module Export RBN := EmptyModule <+ RBNetworkType A R V VBFT BTh BSett.

Set Implicit Arguments. (* anyway *)

Definition id_coh w : Prop := forall n, (w @ n).(id) = n.

(* persistence *)

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

Definition id_persistent st st' : Prop := st.(id) = st'.(id).

(* state *)

Definition msgcnt_nodup st : Prop :=
  forall msg,
    match msg with
    | InitialMsg _ _ => st.(msgcnt) msg = nil
    | _ => List.NoDup (st.(msgcnt) msg)
    end.

Definition output_nodup st : Prop := forall q r, List.NoDup (st.(output) (q, r)).

(* implication-shaped invariants (therefore async) *)
(* "msgcnt_nodup" is pointed, so proved in another batch *)

(* having one direction invariants would be preferred, since they can be easily applied/specialized *)

(* in the dependency graph, the update of voted happens after the change of msgcnt
    and this dependency is tracked in the basic block, so the "some" invariant can
    be proved by induction on state_mnt_type_list; 
    but for the "none" case, the dependency is reversed *)
(* but now they are proved together, anyway *)
Definition voted_some st : Prop :=
  forall q r v, 
    st.(voted) (q, r) = Some v ->
    (th_echo4vote <= length (st.(msgcnt) (EchoMsg q r v)) \/ 
     th_vote4vote <= length (st.(msgcnt) (VoteMsg q r v))).

Definition voted_none st : Prop :=
  forall q r v,
    st.(voted) (q, r) = None ->
    length (st.(msgcnt) (EchoMsg q r v)) < th_echo4vote /\
    length (st.(msgcnt) (VoteMsg q r v)) < th_vote4vote.

Definition output_vote_size st : Prop :=
  forall q r v, 
    In v (st.(output) (q, r)) ->
    th_vote4output <= length (st.(msgcnt) (VoteMsg q r v)).

Definition vote_size_output st : Prop :=
  forall q r v, 
    th_vote4output <= length (st.(msgcnt) (VoteMsg q r v)) ->
    In v (st.(output) (q, r)).

(* l2h, sent *)

Definition initialmsg_sent_l2h psent st : Prop :=
  forall r, st.(sent) r -> forall n, exists used, 
    In (mkP st.(id) n (InitialMsg r (value_bft st.(id) r)) used) psent.

Definition echomsg_sent_l2h psent st : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v -> forall n, exists used, 
    In (mkP st.(id) n (EchoMsg q r v) used) psent.

Definition votemsg_sent_l2h psent st : Prop :=
  forall q r v, st.(voted) (q, r) = Some v -> forall n, exists used, 
    In (mkP st.(id) n (VoteMsg q r v) used) psent.

(* l2h, recv *)

Definition initialmsg_recv_l2h psent st : Prop :=
  forall q r v, st.(echoed) (q, r) = Some v ->
    In (mkP q st.(id) (InitialMsg r v) true) psent.

Definition msgcnt_recv_l2h psent st : Prop :=
  forall m q, In q (st.(msgcnt) m) ->
    In (mkP q st.(id) m true) psent.

(* h2l, sent *)

Definition sent_h2l_inner (src dst : Address) msg stmap : Prop :=
  let: st := stmap src in
  match msg with
  | InitialMsg r v => st.(sent) r /\ value_bft src r = v
  | EchoMsg q r v => st.(echoed) (q, r) = Some v
  | VoteMsg q r v => st.(voted) (q, r) = Some v
  end.

Definition sent_h2l src dst msg stmap : Prop := Eval unfold sent_h2l_inner in 
  isByz src = false -> sent_h2l_inner src dst msg stmap.

Definition initialmsg_sent_h2l p stmap : Prop := Eval unfold sent_h2l in
  match p with
  | mkP src dst (InitialMsg r v) _ => sent_h2l src dst (InitialMsg r v) stmap
  | _ => True
  end.

Definition echomsg_sent_h2l p stmap : Prop := Eval unfold sent_h2l in
  match p with
  | mkP src dst (EchoMsg q r v) _ => sent_h2l src dst (EchoMsg q r v) stmap
  | _ => True
  end.

Definition votemsg_sent_h2l p stmap : Prop := Eval unfold sent_h2l in
  match p with
  | mkP src dst (VoteMsg q r v) _ => sent_h2l src dst (VoteMsg q r v) stmap
  | _ => True
  end.

(* h2l, recv *)

Definition recv_h2l_inner (src dst : Address) msg stmap : Prop :=
  let: st := stmap dst in
  match msg with
  | InitialMsg r v => st.(echoed) (src, r)
  | _ => In src (st.(msgcnt) msg)
  end.

Definition recv_h2l src dst msg stmap : Prop := Eval unfold recv_h2l_inner in 
  isByz dst = false -> recv_h2l_inner src dst msg stmap.

Definition initialmsg_recv_h2l p stmap : Prop := Eval unfold recv_h2l in
  match p with
  | mkP src dst (InitialMsg r v) true => recv_h2l src dst (InitialMsg r v) stmap
  | _ => True
  end.

Definition msgcnt_recv_h2l p stmap : Prop := Eval unfold recv_h2l in
  match p with
  | mkP src dst (EchoMsg _ _ _ as m | VoteMsg _ _ _ as m) true => recv_h2l src dst m stmap
  | _ => True
  end.

(* automation setup *)

Definition is_InitialMsg (m : Message) :=
  match m with
  | InitialMsg _ _ => true
  | _ => false
  end.

Global Arguments is_InitialMsg !_ /.

(* well, certainly not reusable *)
Tactic Notation "simpl_via_is_InitialMsg_false" constr(msg) :=
  repeat match goal with
  | H : context[match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | VoteMsg _ _ _ => ?ee end] |- _ =>
    replace (match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | VoteMsg _ _ _ => ee end)
      with ee in H by (destruct msg; try discriminate; reflexivity)
  | |- context[match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | VoteMsg _ _ _ => ?ee end] =>
    replace (match msg with InitialMsg _ _ => _ | EchoMsg _ _ _ | VoteMsg _ _ _ => ee end)
      with ee by (destruct msg; try discriminate; reflexivity)
  end.

Create HintDb RBinv.

Tactic Notation "basic_solver" :=
  try reflexivity; auto with RBinv; try tauto; try eqsolve; try lia.

Local Hint Resolve incl_set_add_simple : RBinv.

Local Hint Resolve incl_sendout_l incl_sendout_r : psent.

Local Hint Extern 30 (In _ (set_add_simple _ _ _)) => (rewrite In_set_add_simple; tauto) : psent.

Module Export SMT <: StateMntTemplate A M BTh P RBP Ns.

(* materialize *)
(* carrying proofs? seems OK, as long as it will never be used in equality proofs *)
Inductive state_mnt_type_ (st : State) : Type :=
  | Msent : forall r,
    st.(sent) r = false -> state_mnt_type_ st
  | Mechoed : forall q r (v : Value), 
    st.(echoed) (q, r) = None -> state_mnt_type_ st
  | Mmsgcnt : forall q msg,
    (match msg with InitialMsg _ _ => False | _ => True end) ->
    let: cnt := st.(msgcnt) in
    ~ In q (cnt msg) -> state_mnt_type_ st
  | Mvoted : forall q r v,
    st.(voted) (q, r) = None ->
    (* this seems to readily encode the dependency! *)
    (th_echo4vote <= length (st.(msgcnt) (EchoMsg q r v)) \/
     th_vote4vote <= length (st.(msgcnt) (VoteMsg q r v))) -> state_mnt_type_ st
  | Moutput : forall q r v,
    th_vote4output <= length (st.(msgcnt) (VoteMsg q r v)) ->
    state_mnt_type_ st
.

Global Arguments Moutput : clear implicits.

Definition state_mnt_type := state_mnt_type_.

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
  | Moutput _ q r v _ =>
    let: omap := st.(output) in
    (st <| output := map_update AddrRdPair_eqdec (q, r) (set_add_simple Value_eqdec v (omap (q, r))) omap |>)
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
    incl (broadcast st.(id) (VoteMsg q r v)) psent
  | Moutput _ q r v _ => True
  end.

End SMT.

Module Export SMTool := StateMntToolkit A M BTh P PSOp RBP Ns SMT.

Ltac state_analyze_select f ::=
  match f with
  | sent => uconstr:(Msent)
  | echoed => uconstr:(Mechoed)
  | voted => uconstr:(Mvoted)
  | msgcnt => uconstr:(Mmsgcnt)
  | output => uconstr:(Moutput)
  end.

Ltac psent_effect_star_solver ::=
  (* mostly heuristics *)
  simpl; autorewrite with psent; simpl; auto using incl_set_add_simple with psent; 
  try solve [ intuition (auto using incl_set_add_simple with psent) ].

Ltac post_state_analysis_other_cases_solver ::= try solve [ basic_solver ].

Section State_Monotone_Proofs.

Local Hint Rewrite -> In_consume : psent.

Record node_state_invariants_pre st st' : Prop := {
  _ : lift_point_to_edge voted_some st st';
  _ : lift_point_to_edge voted_none st st';
  _ : lift_point_to_edge output_vote_size st st';
  _ : lift_point_to_edge vote_size_output st st';
}.

(* for each node (ignoring whether faulty/non-faulty here),
    the change of its local state satisfies some pattern, 
    so does the effect that this change has over the packet soup *)

Fact state_mnt_sound q w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n), 
    psent_effect_star n (packetSoup w') l /\ node_state_invariants_pre (w @ n) (w' @ n).
Proof with (try (now exists (MNTnil _))).
  inversion_step' Hstep; clear Hstep; intros...
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct (procMsgPre _ _ _) as [ (st', ms) | ] eqn:E in Ef; simplify_eq...
    destruct (w @ dst) as [ dst' sent echoed voted cnt output ].
    unfold procMsgPre in E.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; try discriminate. simplify_eq.
      state_analyze.
      constructor; hnf; intros HH; hnf in HH |- *; intuition.
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in E; try discriminate. simplify_eq.
      unfold routine_check in Ef. simpl in Ef.
      (* fine-grained discussion; avoid repetition as much as possible *)
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; simplify_eq;
        [ apply andb_true_iff in EE; destruct EE as (EE & Eth%Nat.leb_le),
            (voted (q, r)) eqn:?; try discriminate
        | apply andb_false_iff in EE; rewrite Nat.leb_gt in EE ].
      3-4: destruct (Nat.leb _ _) eqn:Eth2 in |- *; 
        [ apply Nat.leb_le in Eth2 | apply Nat.leb_nle in Eth2 ]. (* TODO make this a automated reflect tactic? *)
      all: state_analyze.
      (* nice time to prove some invariants *)
      all: constructor; hnf; intros HH; hnf in HH |- *; intros; simpl in *;
        try solve [ tauto | intuition | eqsolve ].
      all: unfold map_update in *; destruct_eqdec! as_ ?; simplify_eq; simpl in *; auto with psent.
      all: try solve
        [ pose proof (fun n1 n2 H => Nat.le_trans n1 _ _ H (le_S _ _ (le_n n2))); firstorder
        | progress isSome_rewrite; naive_solver 
        | rewrite In_set_add_simple in *; naive_solver ].
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct (w @ n) as [ dst' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent t) eqn:?; simplify_eq...
    state_analyze.
    constructor; hnf; intros HH; hnf in HH |- *; intuition.
Qed.

Record node_persistent_invariants st st' : Prop := {
  _ : sent_persistent st st';
  _ : echoed_persistent st st';
  _ : msgcnt_persistent st st';
  _ : voted_persistent st st';
  _ : output_persistent st st';
  _ : id_persistent st st';
}.

Local Instance Transitive_node_persistent_invariants : Transitive node_persistent_invariants.
Proof.
  hnf. intros ??? H H0. destruct H, H0. constructor.
  all: hnf; intuition.
  - congruence.
Qed.

Fact persistent_invariants_pre_pre st (d : state_mnt_type st) :
  node_persistent_invariants st (state_mnt d) /\ lift_point_to_edge msgcnt_nodup st (state_mnt d)
    /\ lift_point_to_edge output_nodup st (state_mnt d).
Proof.
  split_and?.
  1: constructor.
  all: match goal with |- lift_point_to_edge ?def _ _ => unfold def | _ => idtac end; hnf.
  (* heuristics: auto; if auto does not work then eauto; hypothesis has what you need *)
  all: intros; destruct d; subst; simpl in *; eauto; try hypothesis.
  (* another layer of heuristic *)
  all: unfold map_update in *; destruct_eqdec! as_ ?; simpl in *; simplify_eq; eauto with psent; try hypothesis.
  - destruct msg0; try contradiction.
    all: constructor; try assumption.
    apply (H (EchoMsg _ _ _)).
    apply (H (VoteMsg _ _ _)).
  - apply NoDup_set_add_simple, H.
Qed.

Fact persistent_invariants_pre st st' (l : state_mnt_type_list st st') :
  node_persistent_invariants st st' /\ lift_point_to_edge msgcnt_nodup st st'
    /\ lift_point_to_edge output_nodup st st'.
Proof.
  induction l.
  - split_and?. 1: constructor. all: hnf; auto.
  - destruct_and? IHl.
    pose proof (persistent_invariants_pre_pre d) as HH. destruct_and? HH.
    split; [ | split_and?; hnf in *; intuition ].
    etransitivity; eauto.
Qed.

(* FIXME: the following two proof scripts may be rewritten as tactics? but not for now *)
Fact persistent_invariants q w w' (Hstep : system_step q w w') :
  lift_state_pair_inv node_persistent_invariants w w'.
Proof.
  intros n.
  eapply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & _).
  eapply persistent_invariants_pre; eauto.
Qed.

Fact persistent_invariants_trace [w l] (Htrace : system_trace w l) :
  lift_state_pair_inv node_persistent_invariants w (final_sysstate w l).
Proof.
  revert w Htrace. induction l as [ | (q, w') l' IH ]; simpl; intros.
  - rewrite final_sysstate_nil. hnf. intros ?. constructor; hnf; auto.
  - rewrite final_sysstate_cons. destruct Htrace as (Hstep%persistent_invariants & Htrace).
    specialize (IH _ Htrace). hnf in IH, Hstep |- *. intros n. specialize (Hstep n). specialize (IH n).
    etransitivity; eauto.
Qed. 

Fact id_coh_is_invariant : is_invariant_step id_coh.
Proof.
  hnf; intros ??? H Hstep.
  hnf in H |- *; intros n; specialize (H n).
  apply persistent_invariants in Hstep. hnf in Hstep. specialize (Hstep n).
  destruct Hstep; hnf in *; congruence.
Qed.

(* length is also monotonic, but can be reduced to In + NoDup, so it is not included above *)
(* FIXME: add them? since they look useful *)

(* reformulate *)
Record node_state_invariants st : Prop := {
  _ : msgcnt_nodup st;
  _ : output_vote_size st;
  _ : vote_size_output st;
  _ : voted_some st;
  _ : voted_none st;
  _ : output_nodup st;
}.

Fact state_invariants : is_invariant_step (lift_state_inv node_state_invariants).
Proof.
  hnf. intros ??? H Hstep.
  hnf in H |- *. intros n. specialize (H n).
  pose proof (state_mnt_sound Hstep n) as (l & _ & Hinv_pre).
  pose proof (persistent_invariants_pre l) as (_ & HH). destruct_and? HH.
  constructor.
  all: match goal with |- ?def _ => pick def as_ H' by_ (destruct H); 
    try (pick def as_ H'' by_ (destruct Hinv_pre)); hnf in * end; now saturate_assumptions.
Qed.

End State_Monotone_Proofs.

Section Forward.

Record node_psent_l2h_invariants psent st : Prop := {
  _ : initialmsg_sent_l2h psent st;
  _ : initialmsg_recv_l2h psent st;
  _ : echomsg_sent_l2h psent st;
  _ : msgcnt_recv_l2h psent st;
  _ : votemsg_sent_l2h psent st;
}.

(* while you can certainly prove these individually, proving them together can save some time *)
(* this proof would depend on id_coh to unify the internal/external identifiers *)
Fact l2h_invariants : is_invariant_step_under id_coh (lift_node_inv node_psent_l2h_invariants).
Proof.
  hnf; intros qq ?? Hcoh Hcoh' H Hstep.
  unfold lift_node_inv in *.
  intros n Hnonbyz; specialize (H _ Hnonbyz).
  specialize (Hcoh n); specialize (Hcoh' n). (* unify *)
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & Hpsent & _).
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

Module Export PMT <: PsentMntTemplate A M BTh BSett P RBP Ns RBAdv RBN.

Inductive packets_shape_ : Type := PSbcast (n : Address) (m : Message).

Definition packets_shape := packets_shape_.

Definition packets_shape_consistent (ps : packets_shape) (pkts : list Packet) : Prop :=
  match ps with
  | PSbcast n m => pkts = broadcast n m
  end.

Definition state_effect_recv := recv_h2l_inner.

Definition state_effect_bcast n m stmap :=
  match m with
  | InitialMsg r v => value_bft n r = v /\ (stmap n).(sent) r
  | EchoMsg q r v => (stmap n).(echoed) (q, r) = Some v
  | VoteMsg q r v => (stmap n).(voted) (q, r) = Some v
  end.

Definition state_effect_send_by_shape (ps : packets_shape) (stmap : StateMap) : Prop :=
  match ps with
  | PSbcast n m => isByz n = false /\ state_effect_bcast n m stmap
  end.

End PMT.

Module Export PMTool := PsentMntToolkit A M BTh BSett P RBP Ns RBAdv RBN PMT.

Ltac pkts_match pkts ::=
  match pkts with
  | broadcast ?n ?m => uconstr:((mkPMT pkts (PSbcast n m) (broadcast_all_fresh n m) eq_refl))
  end.

Ltac state_effect_solve ::=
  match goal with
  | |- @state_effect _ _ _ => simpl; eauto; 
    repeat (first [ rewrite upd_refl; simpl | rewrite map_update_refl; simpl ]);
    try isSome_rewrite; auto
  | _ => idtac
  end.

Section Backward.

Fact psent_mnt_sound_pre q w w' (Hstep : system_step q w w') 
  (Hcoh : id_coh w) (* still needed *) :
  psent_mnt_sound_goal_pre q w w'.
Proof with (try solve [ simplify_eq; psent_analyze ]).
  hnf. inversion_step' Hstep; clear Hstep; intros.
  1,3: exists (Pid _).
  3: exists (Puse _ (mkP src dst msg used) ltac:(hypothesis)). 
  - psent_analyze.
  - destruct_localState w n as_ [ n' sent echoed voted cnt output ].
    simpl in E.
    destruct (sent t) eqn:?; simplify_eq.
    all: psent_analyze.
  - (* the case analysis is slightly different; the None case needs to be discussed now *)
    destruct_localState w dst as_ [ dst' sent echoed voted cnt output ].
    unfold procMsgPre in Ef.
    destruct (is_InitialMsg msg) eqn:Edecide.
    + destruct msg as [ r v | | ]; try discriminate.
      destruct (echoed (src, r)) eqn:EE; simplify_eq.
      all: psent_analyze.
    + simpl_via_is_InitialMsg_false msg.
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in Ef.
      1: simplify_eq; destruct msg; try discriminate; psent_analyze.
      unfold routine_check in Ef; simpl in Ef.
      destruct msg as [ | q r v | q r v ]; simpl in Ef; try discriminate.
      all: destruct (andb _ _) eqn:EE in Ef; simpl in Ef; simplify_eq;
        [ apply andb_true_iff in EE; destruct EE as (EE & Eth%Nat.leb_le),
            (voted (q, r)) eqn:?; try discriminate | ].
      3-4: destruct (Nat.leb _ _) eqn:Eth2 in |- *; [ apply Nat.leb_le in Eth2 | ].
      all: psent_analyze.
  - simpl. intuition.
Qed.

Fact psent_mnt_sound q w w' (Hstep : system_step q w w') 
  (Hcoh : id_coh w) : psent_mnt_sound_goal w w'.
Proof.
  hnf. apply psent_mnt_sound_pre in Hstep; auto.
  destruct q.
  1-3: destruct Hstep as (b & l & ?); now exists (PSKnonbyz b l).
  simpl in Hstep. destruct Hstep as (? & E & ?). rewrite E. eexists (PSKbyz _ _). 
  split_and?; try reflexivity; auto.
Qed.  

(* this bunch can pass the base case easily, since it does no work for existing packets *)
Record node_psent_h2l_invariants_sent p stmap : Prop := {
  _ : initialmsg_sent_h2l p stmap;
  _ : echomsg_sent_h2l p stmap;
  _ : votemsg_sent_h2l p stmap;
}.

(* this bunch can pass the cons case easily, since it does no work for fresh packets *)
Record node_psent_h2l_invariants_recv p stmap : Prop := {
  _ : initialmsg_recv_h2l p stmap;
  _ : msgcnt_recv_h2l p stmap;
}.

Fact h2l_invariants_id_pre q w w' (Hstep : system_step q w w') p :
  (node_psent_h2l_invariants_sent p (localState w) ->
  forall used, node_psent_h2l_invariants_sent (mkP p.(src) p.(dst) p.(msg) used) (localState w')) /\
  (node_psent_h2l_invariants_recv p (localState w) ->
  node_psent_h2l_invariants_recv p (localState w')).
Proof.
  destruct p as [ src dst msg used ].
  pose proof (persistent_invariants Hstep) as Hinv. (* use persistent properties to solve *)
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
    destruct (f st key) eqn:E in H; try discriminate; apply H0 in E
  end.
  now isSome_rewrite.
Qed.

Corollary h2l_invariants_id q w w' (Hstep : system_step q w w') psent :
  (lift_pkt_inv' node_psent_h2l_invariants_sent psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_sent psent (localState w')) /\
  (lift_pkt_inv' node_psent_h2l_invariants_recv psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_recv psent (localState w')).
Proof.
  split; intros H; hnf in H |- *; intros [ src dst msg used ] Hin; specialize (H _ Hin).
  all: now eapply (h2l_invariants_id_pre Hstep _) in H; eauto.
Qed.

(* FIXME: the two bunches can be proved separatedly, so this lemma is weaker than it should be *)
Fact h2l_invariants :
  is_invariant_step_under id_coh (* needed, since will use psent_mnt_sound *)
    (fun w => lift_pkt_inv node_psent_h2l_invariants_sent w
      /\ lift_pkt_inv node_psent_h2l_invariants_recv w).
Proof.
  hnf; intros q ?? Hcoh Hcoh' H Hstep. unfold lift_pkt_inv in H |- *. 
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply psent_mnt_sound in Hstep; try assumption.
  destruct Hstep as ([ b l | [ src dst msg ? ] ] & Hse & Hpsent); simpl in Hse, Hpsent.
  - (* nonbyz step *)
    destruct Hse as (Hb & Hse). 
    remember (packetSoup w') as psent eqn:Htmp; clear Htmp. (* TODO generalize? *)
    revert psent Hpsent H Hse. 
    induction l as [ | a l IH ]; intros.
    all: simpl in Hse, Hpsent.
    (* TODO why we do not need to destruct H here (and only need to destruct later)? can I explain? *)
    + destruct b as [ | p' Hin' ]; simpl in Hb, Hpsent; hnf in Hpsent.
      * split_and?; intros ?; rewrite Hpsent; revert p; try now apply (h2l_invariants_id Hstep_ (packetSoup w)).
      * split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H' by_ (destruct_and? H) end; 
          clear H; rename H' into H; setoid_rewrite Hpsent.
        1: intros [ src dst msg used ] Hin%(In_consume_conv_full Hin'). 
        1: destruct Hin as (used' & Hin); specialize (H _ Hin).
        --eapply (h2l_invariants_id_pre Hstep_) in H. simpl in H. exact H.
        --destruct p' as [ src' dst' msg' used' ].
          hnf in H |- *. intros p Hin%In_consume. simpl in Hin.
          destruct Hin as [ <- | (Hin & _) ].
          2: specialize (H _ Hin).
          1: destruct used'; [ specialize (H _ Hin') | ].
          1,3: eapply (h2l_invariants_id_pre Hstep_ _) in H; simpl in H; exact H.
          (* interesting part *)
          clear H. destruct Hb as (Hnonbyz & Hr).
          destruct msg' as [ r' v' | q' r' v' | q' r' v' ]; simpl in Hr.
          all: constructor; try exact I.
          all: hnf; simpl; auto.
    + destruct a as [ pkts [ n m ] Hf Hcheck ]. simpl in *. subst pkts.
      clear Hb. destruct Hpsent as (psent_ & Hpmnt & Hineq), Hse as (Hse & Hnonbyz & Hb).
      saturate_assumptions!. clear H.
      split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H by_ (destruct_and? IH) end; clear IH.
      all: intros p Hin%Hineq; autorewrite with psent in Hin.
      all: try (destruct Hin as [ (dst & ->)%In_broadcast | ]; [ | solve [ intuition ] ]).
      all: destruct m; simpl in Hb; constructor; hnf; auto; try tauto.
  - (* byz step; easy? *)
    destruct Hse as (Hbyz & -> & Hcb), Hpsent as (Els & Hpsent), H as (HHsent & HHrcv). 
    rewrite Hpsent, Els. clear Els Hpsent.
    split_and?; intros p; rewrite In_sendout1; intros [ <- | Hin ]; auto.
    all: constructor; hnf; destruct msg; simpl; intros; try solve [ auto | congruence | tauto ].
Qed.

End Backward.

(* this is nonsense ... *)
Fact procMsg_fresh st src m :
  Forall (fun p => p.(received) = false) (snd (procMsg st src m)).
Proof.
  unfold procMsg.
  destruct st as [ n sent echoed voted msgcnt output ], m as [ r v | q r v | q r v ]; simpl.
  1: destruct (echoed (src, r)); simpl; auto using broadcast_all_fresh.
  all: destruct (in_dec _ _ _) in |- *; auto.
  all: unfold routine_check; simpl; destruct (andb _ _); simpl; auto using broadcast_all_fresh.
Qed.

Fact procInt_fresh st t :
  Forall (fun p => p.(received) = false) (snd (procInt st t)).
Proof.
  unfold procInt.
  destruct st as [ n sent echoed voted msgcnt output ]; simpl.
  destruct (sent t); simpl; auto using broadcast_all_fresh.
Qed.

(* some invariants should be proved by induction, but also rely on other inductive invariants *)

(* should be useful ... intensionally inductive? *)
(* serve as a way to tell that "at least some of the vote messages are the consequences of echo messages" *)
(* in paper proof, this invariant might be mentioned as "consider the first non-faulty node who broadcast
    vote messages"; but that would involve the notion of time, which is not convenient to formalize
    and use in the safety proofs *)
(*
Definition echo_exists_before_vote p psent : Prop :=
  match p with
  | mkP src dst (VoteMsg q r v) used =>
    isByz src = false ->
      exists src' dst', isByz src' = false /\ 
        In (mkP src' dst' (EchoMsg q r v) true) psent
  | _ => True
  end.
*)
(* considering the following proofs, another form will be more convenient *)
Definition echo_exists_before_vote psent st : Prop :=
  forall q r v, 
    st.(voted) (q, r) = Some v ->
      exists src' dst', isByz src' = false /\ 
        In (mkP src' dst' (EchoMsg q r v) true) psent.

Lemma echo_exists_before_vote_is_invariant :
  is_invariant_step_under (fun w => id_coh w /\
    lift_state_inv node_state_invariants w /\
    lift_node_inv node_psent_l2h_invariants w /\
    lift_pkt_inv node_psent_h2l_invariants_sent w /\
    lift_pkt_inv node_psent_h2l_invariants_recv w)
  (lift_node_inv echo_exists_before_vote).
Proof with saturate_assumptions.
  hnf. intros qq ?? (_ & _ & _ & Hh2ls_back & _) (Hcoh & Hst & Hl2h & Hh2ls & Hh2lr) IH Hstep.
  hnf. intros src Hnonbyz. hnf. intros q r v Hr.
  pick voted_some as_ Hr2 by_ (pose proof (Hst src) as []). saturate_assumptions!.
  unfold th_echo4vote, th_vote4vote in Hr2. pose proof f_lt_N_minus_2f as Hf.
  pick msgcnt_nodup as_ Hnodup by_ (pose proof (Hst src) as []).
  destruct Hr2 as [ Hr2 | Hr2 ].
  (* there must be a non-faulty sender in both cases *)
  all: match type of Hr2 with _ <= ?ll => assert (f < ll) as (n & Hnonbyz' & Hin')%at_least_one_nonfaulty by lia end;
    try solve [ eapply (Hnodup (EchoMsg _ _ _)) | eapply (Hnodup (VoteMsg _ _ _)) ].
  all: pick msgcnt_recv_l2h as_ Hr3 by_ (pose proof (Hl2h _ Hnonbyz) as []); specialize (Hr3 _ _ Hin'); rewrite Hcoh in Hr3.
  - (* easy, base case *)
    eauto.
  - (* inductive case *)
    (* HMM exploiting the network model ... 
      there might be other ways to work around, but this is probably the easiest way for now *)
    eapply system_step_received_inversion_full in Hr3; try eassumption; auto using procMsg_fresh, procInt_fresh.
    destruct Hr3 as (? & Hr3). 
    pick votemsg_sent_h2l as_ Hr4 by_ (pose proof (Hh2ls_back _ Hr3) as [])... apply IH in Hr4; auto.
    destruct Hr4 as (? & ? & ? & Hr4). eapply system_step_psent_norevert_full in Hr4; eauto.
Qed.

Definition first_vote_due_to_echo w : Prop :=
  forall q r v, 
    (* examining all nodes ... luckily Address is set to be finite *)
    let: l := List.filter (fun n => (negb (isByz n)) && 
      (match ((w @ n).(voted) (q, r)) with
       | Some v' => is_left (Value_eqdec v v')
       | _ => false
      end)) valid_nodes in
    match l with
    | nil => True
    | _ => exists n', In n' l /\ th_echo4vote <= length ((w @ n').(msgcnt) (EchoMsg q r v))
    end.

(* TODO the proof is not very nice ... *)
Lemma first_vote_due_to_echo_is_invariant :
  is_invariant_step_under (fun w => id_coh w /\
    lift_state_inv node_state_invariants w /\
    lift_node_inv node_psent_l2h_invariants w /\
    lift_pkt_inv node_psent_h2l_invariants_sent w /\
    lift_pkt_inv node_psent_h2l_invariants_recv w) first_vote_due_to_echo.
Proof.
  intros qq ?? (_ & Hst_back & _ & Hh2ls_back & _) (Hcoh & Hst & Hl2h & _ & Hh2lr) H Hstep q r v. 
  hnf in H. specialize (H q r v).
  match goal with |- context[List.filter ?a ?b] => destruct (List.filter a b) as [ | n' l' ] eqn:E'; try exact I end.
  match type of H with context[List.filter ?a ?b] => destruct (List.filter a b) as [ | n l ] eqn:E in H end.
  - { exists n'. apply and_wlog_r; [ simpl; tauto | rewrite <- E'; intros (_ & Hcheck%andb_true_iff)%filter_In ].
      rewrite negb_true_iff in Hcheck. destruct Hcheck as (Hnonbyz_n' & Hv_).
      clear E'. destruct (voted (w' @ n') (q, r)) as [ v' | ] eqn:E'; [ | discriminate ].
      autorewrite with booldec in Hv_. subst v'.
      pick voted_some as_ Hv' by_ (pose proof (Hst n') as []). apply Hv' in E'.
      destruct E' as [ E' | E' ]; auto.
      (* HMM again, exploiting the network model ... but still cumbersome *)
      (* basically saying that if there is some node in the Vote msgcnt, 
        then by inverting the message, we know that it must have voted 
        in the previous state, which leads to contradiction *)
      (* TODO the following steps are still repeating ... *)
      unfold th_vote4vote in E'. pose proof f_lt_N_minus_2f as Hf.
      pick msgcnt_nodup as_ Hnodup by_ (pose proof (Hst n') as []). 
      match type of E' with _ <= ?ll => assert (f < ll) as (n & Hnonbyz_n & Hin')%at_least_one_nonfaulty by lia end.
      2: eapply (Hnodup (VoteMsg _ _ _)).
      pick msgcnt_recv_l2h as_ Hr3 by_ (pose proof (Hl2h _ Hnonbyz_n') as []). specialize (Hr3 _ _ Hin'). rewrite Hcoh in Hr3.
      eapply system_step_received_inversion_full in Hr3; try eassumption; auto using procMsg_fresh, procInt_fresh.
      destruct Hr3 as (? & Hr3). 
      pick votemsg_sent_h2l as_ Hr4 by_ (pose proof (Hh2ls_back _ Hr3) as []). saturate_assumptions. 
      pose proof (in_nil (a:=n)) as Htmp1. pose proof (Address_is_finite n) as Htmp2.
      rewrite <- E, -> ! filter_In, -> ! andb_true_iff, -> Hr4, -> Hnonbyz_n in Htmp1. autorewrite with booldec in Htmp1. eqsolve. }
  - rewrite <- E in H. clear E n l. rewrite <- E'. clear E' n' l'.
    destruct H as (n & (Hin & Hcheck%andb_true_iff)%filter_In & He). 
    destruct (voted (w @ n) (q, r)) as [ v' | ] eqn:E; [ | eqsolve ]. autorewrite with booldec in Hcheck. destruct Hcheck as (Hnonbyz & <-).
    pick voted_persistent as_ Hv by_ (pose proof (persistent_invariants Hstep n) as []). apply Hv in E.
    exists n. autorewrite with booldec. rewrite E. autorewrite with booldec. split_and?; auto.
    etransitivity; [ apply He | ]. apply NoDup_incl_length.
    + pick msgcnt_nodup as_ Htmp by_ (pose proof (Hst_back n) as []). apply (Htmp (EchoMsg _ _ _)).
    + pick msgcnt_persistent as_ Htmp by_ (pose proof (persistent_invariants Hstep n) as []). hnf. apply (Htmp (EchoMsg _ _ _)).
Qed.

Definition vote_uniqueness w : Prop :=
  forall src r dst1 dst2 v1 v2, 
    isByz dst1 = false -> isByz dst2 = false ->
    (* no matter if src is byz or not *)
    (w @ dst1).(voted) (src, r) = Some v1 ->
    (w @ dst2).(voted) (src, r) = Some v2 ->
    v1 = v2.

Lemma vote_uniqueness_is_invariant :
  is_invariant_step_under (fun w => (id_coh w /\
    lift_state_inv node_state_invariants w /\
    lift_node_inv node_psent_l2h_invariants w /\
    lift_pkt_inv node_psent_h2l_invariants_sent w /\
    lift_pkt_inv node_psent_h2l_invariants_recv w) /\
    first_vote_due_to_echo w) vote_uniqueness.
Proof.
  intros qq ?? ((_ & Hst_back & _ & Hh2ls_back & _) & _) ((Hcoh & Hst & Hl2h & Hh2ls & Hh2lr) & Hfve) H Hstep src r.
  intros dst1 dst2 v1 v2 Hnonbyz_dst1 Hnonbyz_dst2 Hv1 Hv2.
  (* use this, and then quorum intersection *)
  assert (forall v, v = v1 \/ v = v2 -> exists n', isByz n' = false /\ th_echo4vote <= length ((w' @ n').(msgcnt) (EchoMsg src r v))) as He.
  { intros v Hv. specialize (Hfve src r v).
    destruct (List.filter _ valid_nodes) eqn:E in Hfve.
    - (* contradiction *)
      pose proof (in_nil (a:=dst1)) as Htmp1. pose proof (in_nil (a:=dst2)) as Htmp2.
      pose proof (Address_is_finite dst1). pose proof (Address_is_finite dst2). 
      rewrite <- E in Htmp1, Htmp2. autorewrite with booldec in Htmp1, Htmp2.
      rewrite Hv1 in Htmp1. rewrite Hv2 in Htmp2. autorewrite with booldec in Htmp1, Htmp2.
      intuition.
    - rewrite <- E in Hfve. destruct Hfve as (n' & Hfve).
      exists n'. autorewrite with booldec in Hfve. intuition. }
  pose proof (He _ (or_introl eq_refl)) as (n1' & Hnonbyz_n1' & Hsize1).
  pose proof (He _ (or_intror eq_refl)) as (n2' & Hnonbyz_n2' & Hsize2).
  pick msgcnt_nodup as_ Hnodup1 by_ (pose proof (Hst n1') as []). specialize (Hnodup1 (EchoMsg src r v1)). 
  pick msgcnt_nodup as_ Hnodup2 by_ (pose proof (Hst n2') as []). specialize (Hnodup2 (EchoMsg src r v2)).
  simpl in Hnodup1, Hnodup2.
  pose proof (quorum_intersection Hnodup1 Hnodup2 Hsize1 Hsize2) as Hq. pose proof f_lt_N_minus_2f as Hf.
  match type of Hq with _ <= ?ll => assert (f < ll) as (n & Hnonbyz_n & (Hin2' & Hin1'%sumbool_is_left)%filter_In)%at_least_one_nonfaulty by lia end.
  2: now apply List.NoDup_filter.
  (* TODO the following step has some overlap with a previous proof *)
  pick msgcnt_recv_l2h as_ Hsent1 by_ (pose proof (Hl2h _ Hnonbyz_n1') as []). specialize (Hsent1 _ _ Hin1').
  pick msgcnt_recv_l2h as_ Hsent2 by_ (pose proof (Hl2h _ Hnonbyz_n2') as []). specialize (Hsent2 _ _ Hin2').
  rewrite Hcoh in Hsent1, Hsent2.
  pick echomsg_sent_h2l as_ Hvv1 by_ (pose proof (Hh2ls _ Hsent1) as []).
  pick echomsg_sent_h2l as_ Hvv2 by_ (pose proof (Hh2ls _ Hsent2) as []).
  saturate_assumptions. congruence.
Qed.

End RBInvariant.
