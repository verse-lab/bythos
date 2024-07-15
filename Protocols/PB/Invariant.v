From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Protocols.PB Require Export Network.
From Bythos.Properties Require Import Invariant.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module PBInvariant (A : NetAddr) (R : Round) (Sn : Signable) (V : Value) (Pf : PBProof) (VBFT : ValueBFT A R V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (TSSPrim : ThresholdSignatureSchemePrim A Sn with Definition thres := A.N - BTh.t0)
  (PBDT : PBDataTypes A R Sn V Pf).

Import A R V Pf VBFT BTh BSett PBDT.
Import ssrbool. (* anyway *)

Module Export PBN := PBNetwork A R Sn V Pf VBFT BTh BSett TSSPrim PBDT.
Import PBP.TSS.

Set Implicit Arguments. (* anyway *)

Definition id_coh w : Prop := forall n, (w @ n).(id) = n.

(* state *)

Notation NoDup := List.NoDup.

Definition from_nodup st : Prop :=
  forall r, NoDup (map fst (st.(counter) r)).

Definition echoed_ex_valid st : Prop :=
  forall q r v pf, st.(echoed) (q, r) = Some (v, pf) -> ex_validate r v pf.

Definition counter_ok st : Prop :=
  forall r n lsig, In (n, lsig) (st.(counter) r) -> light_verify (r, fst (value_bft st.(id) r)) lsig n.

Fact counter_ok_alt st : counter_ok st <->
  forall r, st.(counter) r = map (fun n => (n, light_sign (r, (value_bft st.(id) r).1) (lightkey_map n))) 
    (map fst (st.(counter) r)).
Proof.
  unfold counter_ok. split; intros.
  - specialize (H r). remember (st.(counter) r) as l eqn:E. clear E.
    induction l as [ | (n, lsig) l IH ]; auto.
    simpl in H |- *. f_equal. 
    + f_equal. apply lightkey_correct, H. auto.
    + apply IH. intros. apply H. auto.
  - rewrite H, in_map_iff in H0. destruct H0 as (? & ? & Hin). simplify_eq.
    apply correct_sign_verify_ok_light.
Qed. 

Definition output_is_delivery_cert st : Prop :=
  forall r cs, st.(output) r = Some cs -> cs = delivery_cert r st.

Definition output_some st : Prop :=
  forall r, st.(output) r -> length (st.(counter) r) = th_output.

Definition output_none st : Prop :=
  forall r, st.(output) r = None -> length (st.(counter) r) < th_output.

(* l2h, sent *)

Definition initmsg_sent_l2h psent st : Prop :=
  forall r, st.(sent) r -> forall n, exists used, 
    In (mkP st.(id) n (InitMsg r (fst (value_bft st.(id) r)) (snd (value_bft st.(id) r))) used) psent.

Definition echomsg_sent_l2h psent st : Prop :=
  forall q r v pf, st.(echoed) (q, r) = Some (v, pf) -> exists used,
    In (mkP st.(id) q (EchoMsg r (light_sign (r, v) (lightkey_map st.(id)))) used) psent.

(* l2h, recv *)

Definition initmsg_recv_l2h psent st : Prop :=
  forall q r v pf, st.(echoed) (q, r) = Some (v, pf) ->
    In (mkP q st.(id) (InitMsg r v pf) true) psent.

Definition echomsg_recv_l2h psent st : Prop :=
  forall n lsig r, In (n, lsig) (st.(counter) r) ->
    In (mkP n st.(id) (EchoMsg r lsig) true) psent.

(* h2l, sent *)

Definition sent_h2l_inner (src dst : Address) msg stmap : Prop :=
  let: st := stmap src in
  match msg with
  | InitMsg r v pf => st.(sent) r /\ value_bft src r = (v, pf)    (* src or st.(id) should not matter *)
  | EchoMsg r lsig =>
    match (st.(echoed) (dst, r)) with
    | None => False
    | Some (v, _) => lsig = light_sign (r, v) (lightkey_map src)
    end
    (* lsig = light_sign (r, fst (value_bft dst r)) (lightkey_map dst) *)
  end.

Definition sent_h2l src dst msg stmap : Prop := Eval unfold sent_h2l_inner in 
  is_byz src = false -> sent_h2l_inner src dst msg stmap.

Definition initmsg_sent_h2l p stmap : Prop := Eval unfold sent_h2l in
  match p with
  (* FIXME: using "as" does not reduce, so have to write "(InitMsg r v pf)" twice?? *)
  | mkP src dst (InitMsg r v pf) _ => sent_h2l src dst (InitMsg r v pf) stmap
  | _ => True
  end.

Definition echomsg_sent_h2l p stmap : Prop := Eval unfold sent_h2l in
  match p with
  | mkP src dst (EchoMsg r lsig) _ => sent_h2l src dst (EchoMsg r lsig) stmap
  | _ => True
  end.

(* h2l, recv *)

Definition recv_h2l_inner (src dst : Address) msg stmap : Prop :=
  let: st := stmap dst in
  match msg with
  | InitMsg r v pf => ex_validate r v pf -> st.(echoed) (src, r) (* HMM not meaningful? *)
  | EchoMsg r lsig =>
    (* FIXME: this is not good, but no very good way? 
        anyway, this branch can be eliminated eventually *)
    In src (map fst (st.(counter) r)) \/ 
    (st.(output) r = None -> light_verify (r, fst (value_bft dst r)) lsig src -> (* dst or st.(id) should not matter *)
    In (src, lsig) (st.(counter) r))
  end.

Definition recv_h2l src dst msg stmap : Prop := Eval unfold recv_h2l_inner in 
  is_byz dst = false -> recv_h2l_inner src dst msg stmap.

Definition initmsg_recv_h2l p stmap : Prop := Eval unfold recv_h2l in
  match p with
  | mkP src dst (InitMsg r v pf) true => recv_h2l src dst (InitMsg r v pf) stmap
  | _ => True
  end.

Definition echomsg_recv_h2l p stmap : Prop := Eval unfold recv_h2l in
  match p with
  | mkP src dst (EchoMsg r lsig) true => recv_h2l src dst (EchoMsg r lsig) stmap
  | _ => True
  end.

(* persistence *)

Definition id_persistent st st' : Prop := st.(id) = st'.(id).

Definition sent_persistent st st' : Prop :=
  forall r, st.(sent) r -> st'.(sent) r.

Definition echoed_persistent st st' : Prop :=
  forall q r v pf, st.(echoed) (q, r) = Some (v, pf) -> st'.(echoed) (q, r) = Some (v, pf).

Definition counter_persistent st st' : Prop :=
  forall r nlsig, In nlsig (st.(counter) r) -> In nlsig (st'.(counter) r).

Definition counter_fixed st st' : Prop :=
  forall r, (* length (st.(counter) r) = th_output *)
    st.(output) r -> st.(counter) r = st'.(counter) r.

Definition output_persistent_pre st st' : Prop :=
  forall r, st.(output) r -> st'.(output) r.

Definition output_persistent st st' : Prop :=
  forall r cs, st.(output) r = Some cs -> st'.(output) r = Some cs.

(* automation setup *)

Create HintDb PBinv.

Tactic Notation "basic_solver" :=
  try reflexivity; auto with PBinv; try tauto; try eqsolve; try lia.

Local Hint Resolve incl_sendout_l incl_sendout_r : psent.

Module Export SMT <: StateMntTemplate A M BTh P0 PSOp PBP Ns.

Inductive state_mnt_type_ (st : State) : Type :=
  | Msent : forall r,
    st.(sent) r = false -> state_mnt_type_ st
  | Mechoed : forall q r (v : Value) (pf : Proof),
    ex_validate r v pf -> 
    st.(echoed) (q, r) = None -> state_mnt_type_ st
  | Mcounter : forall q r lsig, 
    st.(output) r = None -> 
    light_verify (r, fst (value_bft st.(id) r)) lsig q ->
    ~ In q (map fst (st.(counter) r)) -> state_mnt_type_ st
  | Moutput : forall r,
    length (st.(counter) r) = th_output ->
    state_mnt_type_ st
.

Definition state_mnt_type := state_mnt_type_.

Global Arguments Mechoed : clear implicits.
Global Arguments Mcounter : clear implicits.

Definition state_mnt (st : State) (s : state_mnt_type st) : State :=
  match s with
  | Msent _ r _ =>
    (st <| sent := map_update Round_eqdec r true st.(sent) |>)
  | Mechoed _ q r v pf _ _ =>
    (st <| echoed := map_update AddrRdPair_eqdec (q, r) (Some (v, pf)) st.(echoed) |>)
  | Mcounter _ q r lsig _ _ _ =>
    let: cnt := st.(counter) in
    (st <| counter := map_update Round_eqdec r ((q, lsig) :: cnt r) cnt |>)
  | Moutput _ r _ =>
    (st <| output := map_update Round_eqdec r (Some (delivery_cert r st)) st.(output) |>)
  end.

Definition psent_effect (st : State) (s : state_mnt_type st) (n : Address) (psent : PacketSoup) : Prop :=
  match s with
  | Msent _ r _ =>
    incl (broadcast st.(id) (InitMsg r (fst (value_bft st.(id) r)) (snd (value_bft st.(id) r)))) psent
  | Mechoed _ q r v pf _ _ =>
    In (mkP q n (InitMsg r v pf) true) psent /\
    In (mkP st.(id) q (EchoMsg r (light_sign (r, v) (lightkey_map st.(id)))) false) psent
  | Mcounter _ q r lsig _ _ _ =>
    In (mkP q n (EchoMsg r lsig) true) psent
  | Moutput _ r _ => True
  end.

End SMT.

Module Export SMTool := StateMntToolkit A M BTh P0 PSOp PBP Ns SMT.

Ltac state_analyze_select f ::=
  match f with
  | sent => uconstr:(Msent)
  | echoed => uconstr:(Mechoed)
  | counter => uconstr:(Mcounter)
  | output => uconstr:(Moutput)
  end.

Ltac psent_effect_star_solver ::=
  simpl; autorewrite with psent; simpl; auto with psent; try solve [ intuition ].

Ltac post_state_analysis_other_cases_solver ::=
  try solve 
    [ constructor; hnf; intros HH; hnf in HH |- *; intros; simpl in *; basic_solver ].

Section State_Monotone_Proofs.

Local Hint Rewrite -> In_consume : psent.

Record node_state_invariants_pre st st' : Prop := {
  _ : lift_point_to_edge output_some st st';
  _ : lift_point_to_edge output_none st st';
}.

Fact state_mnt_sound q w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n), 
    psent_effect_star n (sentMsgs w') l /\ node_state_invariants_pre (w @ n) (w' @ n).
Proof with (try (now exists (MNTnil _))).
  inversion_step' Hstep; clear Hstep; intros...
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef; simplify_eq...
    destruct (w @ dst) as [ dst' sent echoed cnt output ].
    unfold procMsg in E.
    destruct msg as [ r v pf | r lsig ].
    + destruct (echoed (src, r)) eqn:EE, (ex_validate r v pf) eqn:Eex; try discriminate. simplify_eq.
      state_analyze.
    + destruct (output r) eqn:Eo; try discriminate. 
      destruct (light_verify _ _ _) eqn:Elveri in E; try discriminate. 
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in E; try discriminate. 
      unfold routine_check in Ef. fold (delivery_cert r st') in Ef. 
      destruct (Nat.eqb _ _) eqn:Eeq in Ef; 
        [ apply Nat.eqb_eq in Eeq | apply Nat.eqb_neq in Eeq ]. (* TODO make this a automated reflect tactic? *)
      all: simplify_eq; simpl in *; rewrite ? map_update_refl; rewrite ? sendout0.
      all: state_analyze; try lia.
      all: constructor; hnf; intros HH; hnf in HH |- *; intros; simpl in *.
      (* all map_update type *)
      all: unfold map_update in *; destruct_eqdec! as_ ?; simplify_eq; simpl in *; auto.
      all: try solve
        [ now isSome_rewrite | saturate_assumptions!; lia ].
  - unfold upd.
    destruct (Address_eqdec _ _) as [ <- | Hneq ]...
    destruct t as [ r ].
    destruct (w @ n) as [ dst' sent echoed cnt output ].
    simpl in E.
    destruct (sent r) eqn:?; simplify_eq...
    rewrite (surjective_pairing (value_bft _ _)) in E. simplify_eq.
    state_analyze.
Qed.

(* not very good *)
Record node_persistent_invariants st st' : Prop := {
  _ : sent_persistent st st';
  _ : echoed_persistent st st';
  _ : counter_persistent st st';
  _ : counter_fixed st st';
  _ : output_persistent_pre st st';
  _ : id_persistent st st';
}.

Record node_state_invariants_pre' st st' : Prop := {
  _ : lift_point_to_edge from_nodup st st';
  _ : lift_point_to_edge echoed_ex_valid st st';
  _ : lift_point_to_edge counter_ok st st';
  _ : lift_point_to_edge output_is_delivery_cert st st';
}.

Local Instance Transitive_node_persistent_invariants : Transitive node_persistent_invariants.
Proof.
  hnf. intros ??? H H0. destruct H, H0. constructor.
  all: hnf; intuition.
  - hnf in *. saturate_assumptions!.
    repeat match goal with H : _ = _, H0 : _ = _ |- _ => rewrite H in H0 end.
    saturate_assumptions!. congruence.
  - congruence.
Qed.

Fact persistent_invariants_pre_pre st (d : state_mnt_type st) :
  node_persistent_invariants st (state_mnt d) /\ node_state_invariants_pre' st (state_mnt d).
Proof.
  split_and?; constructor.
  all: match goal with |- lift_point_to_edge ?def _ _ => unfold def | _ => idtac end; hnf.
  all: unfold delivery_cert.
  all: intros; destruct d; subst; simpl in *; eauto; try hypothesis.
  all: unfold map_update in *; destruct_eqdec! as_ ?; simpl in *; simplify_eq; eauto with psent; try hypothesis.
  - now isSome_rewrite. 
  - now constructor.
  - intuition. now simplify_eq.
Qed.

(* TODO the following three: copied from ABC *)
Fact persistent_invariants_pre st st' (l : state_mnt_type_list st st') :
  node_persistent_invariants st st' /\ node_state_invariants_pre' st st'.
Proof.
  induction l.
  - split_and?; constructor. all: hnf; auto.
  - destruct_and? IHl.
    pose proof (persistent_invariants_pre_pre d) as HH. destruct_and? HH.
    split. 1: etransitivity; eauto.
    do 2 (match goal with H : node_state_invariants_pre' _ _ |- _ => destruct H end).
    constructor; hnf in *; auto.
Qed.

Fact persistent_invariants q w w' (Hstep : system_step q w w') :
  lift_state_pair_inv node_persistent_invariants w w'.
Proof.
  intros n.
  eapply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & _).
  eapply persistent_invariants_pre; eauto.
Qed.

Fact persistent_invariants_trace [w l] (Htrace : system_trace w l) :
  lift_state_pair_inv node_persistent_invariants w (final_world w l).
Proof.
  revert w Htrace. induction l as [ | (q, w') l' IH ]; simpl; intros.
  - rewrite final_world_nil. hnf. intros ?. constructor; hnf; auto.
  - rewrite final_world_cons. destruct Htrace as (Hstep%persistent_invariants & Htrace).
    specialize (IH _ Htrace). hnf in IH, Hstep |- *. intros n. specialize (Hstep n). specialize (IH n).
    etransitivity; eauto.
Qed.

(* TODO copied from RB *)
Fact id_coh_is_invariant : is_invariant_step id_coh.
Proof.
  hnf; intros ??? H Hstep.
  hnf in H |- *; intros n; specialize (H n).
  apply persistent_invariants in Hstep. hnf in Hstep. specialize (Hstep n).
  destruct Hstep; hnf in *; congruence.
Qed.

Record node_state_invariants st : Prop := {
  _ : from_nodup st;
  _ : echoed_ex_valid st;
  _ : counter_ok st;
  _ : output_is_delivery_cert st;
  _ : output_some st;
  _ : output_none st;
  (* _ : output_ok st; *)
}.

Fact state_invariants : is_invariant_step (lift_state_inv node_state_invariants).
Proof.
  hnf. intros ??? H Hstep.
  hnf in H |- *. intros n. specialize (H n).
  pose proof (state_mnt_sound Hstep n) as (l & _ & Hinv_pre).
  pose proof (persistent_invariants_pre l) as (_ & HH). destruct_and? HH.
  constructor.
  all: match goal with |- ?def _ => 
    pick def as_ H'' by_ (destruct H); hnf in |- *; 
    try solve [ ((pick def as_ H' by_ (destruct HH)) + (pick def as_ H' by_ (destruct Hinv_pre))); intuition ] 
  end.
Qed.

End State_Monotone_Proofs.

Section Forward.

Record node_psent_l2h_invariants psent st : Prop := {
  _ : initmsg_sent_l2h psent st;
  _ : echomsg_sent_l2h psent st;
  _ : initmsg_recv_l2h psent st;
  _ : echomsg_recv_l2h psent st;
}.

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
  (* TODO why? *)
  1: intros r; specialize (H r).
  2-3: intros q r v pf; specialize (H q r v pf).
  4: intros q lsig r; specialize (H q lsig r).
  (* TODO make routine? *)
  all: intros.
  all: revert H; induction l as [ st | st d st' l IH ]; intros.
  all: (* all MNTnil (under-specified) cases *)
    try solve 
    [ eapply system_step_psent_norevert_full; eauto
    | eapply system_step_psent_persistent_weak_full; eauto ].
  all: simpl in Hpsent; destruct Hpsent as (Hpsent & HH).
  all: destruct d; simpl in Hpsent, IH, (type of l); saturate_assumptions; try tauto.
  all: destruct_and? Hpsent.
  all: unfold map_update in *; destruct_eqdec! as_ ?; simplify_eq (* also simplifies id_coh *); 
    simpl in IH; try tauto.
  all: try solve
    [ exists false; apply Hpsent, In_broadcast; eauto (* for simple *) 
    | destruct (Value_eqdec v0 v) as [ -> | ], (Proof_eqdec pf0 pf) as [ -> | ]; (* for those involve value *)
      try solve [ tauto | apply IH; intros; simplify_eq; auto | eauto ] ].
  destruct (Address_eqdec q0 q) as [ -> | ], (LightSignature_eqdec lsig0 lsig) as [ -> | ];
    try solve [ tauto | apply IH; intros [ | ]; simplify_eq; auto | eauto ].
Qed.

End Forward.

Module Export PMT <: PsentMntTemplate A M BTh BSett P0 PSOp PBP Ns PBAdv PBN.

Inductive packets_shape_ : Type :=
  | PSbcast (n : Address) (m : Message)
  | PSsingle (src dst : Address) (m : Message).

Definition packets_shape := packets_shape_.

Definition packets_shape_consistent (ps : packets_shape) (pkts : list Packet) : Prop :=
  match ps with
  | PSbcast n m => pkts = broadcast n m
  | PSsingle src dst m => pkts = mkP src dst m false :: nil
  end.

Definition state_effect_recv := recv_h2l_inner.

Definition state_effect_bcast n m stmap : Prop := Eval unfold sent_h2l_inner in 
  match m with
  | InitMsg r v pf => sent_h2l_inner n n (InitMsg r v pf) stmap
  | _ => False
  end.

Definition state_effect_single src dst m stmap : Prop := Eval unfold sent_h2l_inner in 
  match m with
  | EchoMsg r lsig => sent_h2l_inner src dst (EchoMsg r lsig) stmap
  | _ => False
  end.

Definition state_effect_send_by_shape (ps : packets_shape) (stmap : StateMap) : Prop :=
  match ps with
  | PSbcast n m => is_byz n = false /\ state_effect_bcast n m stmap
  | PSsingle src dst m => is_byz src = false /\ state_effect_single src dst m stmap
  end.

End PMT.

Module Export PMTool := PsentMntToolkit A M BTh BSett P0 PSOp PBP Ns PBAdv PBN PMT.

Ltac pkts_match pkts ::=
  match pkts with
  | broadcast ?n ?m => uconstr:((mkPMT pkts (PSbcast n m) (broadcast_all_fresh n m) eq_refl))
  end.

Ltac single_pkt_match pkt ::=
  match pkt with
  | mkP ?src ?dst ?m false => uconstr:(mkPMT (pkt :: nil) (PSsingle src dst m) (ltac:(constructor; auto)) eq_refl)
  end.

Ltac state_effect_solve ::=
  simpl; eauto; 
  repeat (first [ rewrite upd_refl; simpl | rewrite map_update_refl; simpl ]);
  try isSome_rewrite; try is_true_rewrite; try solve [ auto | eqsolve ].

Section Backward.

Fact psent_mnt_sound_pre q w w' (Hstep : system_step q w w') 
  (Hcoh : id_coh w) : psent_mnt_sound_goal_pre q w w'.
Proof with (try solve [ simplify_eq; psent_analyze ]).
  hnf. inversion_step' Hstep; clear Hstep; intros.
  1,3: exists (Pid _). 
  3: exists (Puse _ (mkP src dst msg used) ltac:(hypothesis)).
  - psent_analyze.
  - destruct t as [ r ].
    destruct_localState w n as_ [ n' sent echoed cnt output ].
    simpl in E.
    rewrite (surjective_pairing (value_bft _ _)) in E.
    destruct (sent r) eqn:?; simplify_eq.
    all: psent_analyze.
    now rewrite (surjective_pairing (value_bft _ _)).
  - (* the case analysis is slightly different; the None case needs to be discussed now *)
    destruct_localState w dst as_ [ dst' sent echoed cnt output ].
    unfold procMsg in Ef.
    destruct msg as [ r v pf | r lsig ].
    + destruct (echoed (src, r)) eqn:EE, (ex_validate r v pf) eqn:Eex; simplify_eq.
      all: psent_analyze.
    + destruct (output r) eqn:Eo...
      destruct (light_verify _ _ _) eqn:Elveri in Ef...
      destruct (in_dec _ _ _) as [ Hin | Hnotin ] in Ef...
      unfold routine_check in Ef. simpl in Ef. rewrite ? map_update_refl in Ef.
      destruct (Nat.eqb _ _) eqn:Eeq in Ef; 
        [ apply Nat.eqb_eq in Eeq | apply Nat.eqb_neq in Eeq ].
      all: simplify_eq; simpl in *; repeat ((rewrite ! map_update_refl + rewrite ! upd_refl); simpl).
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
Record node_psent_h2l_invariants_sent_nonbyz p stmap : Prop := {
  _ : initmsg_sent_h2l p stmap;
  _ : echomsg_sent_h2l p stmap;
}.

(* this bunch can pass the cons case easily, since it does no work for fresh packets *)
Record node_psent_h2l_invariants_recv p stmap : Prop := {
  _ : initmsg_recv_h2l p stmap;
  _ : echomsg_recv_h2l p stmap;
}.

Fact h2l_invariants_id_pre q w w' (Hstep : system_step q w w') p :
  (node_psent_h2l_invariants_sent_nonbyz p (localState w) ->
  forall used, node_psent_h2l_invariants_sent_nonbyz (mkP p.(src) p.(dst) p.(msg) used) (localState w')) /\
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
  all: destruct msg as [ | ], used; simpl in *; try exact I.
  all: pose proof (Hinv src) as []; pose proof (Hinv dst) as [].
  all: intros; hnf in *; saturate_assumptions; split_and?; destruct_and? H; try hypothesis.
  all: saturate_assumptions!; try tauto.
  (* TODO not very good *)
  1-2: destruct (echoed (w @ src) (dst, r)) as [ (?, ?) | ] eqn:?; try contradiction.
  1-2: saturate_assumptions!; now match_option_rewrite.
  - destruct (echoed (w @ dst) (src, r)) as [ (?, ?) | ] eqn:?; try discriminate.
    saturate_assumptions!. now isSome_rewrite.
  - destruct H as [ H | H ]. 
    + left. rewrite in_map_iff in H |- *. destruct H as ((aa & bb) & <- & H). simpl in *.
      exists (aa, bb). split; auto.
    + right. intros.
      match goal with Ho_ : forall _, is_true (isSome (output _ _)) -> is_true (isSome (output _ _)) |- _ => rename Ho_ into Ho; specialize (Ho r) end.
      destruct (output (w @ dst) r) eqn:?; isSome_rewrite; auto. saturate_assumptions. discriminate.
Qed.

(* TODO copied from RB *)
Corollary h2l_invariants_id q w w' (Hstep : system_step q w w') psent :
  (lift_pkt_inv' node_psent_h2l_invariants_sent_nonbyz psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_sent_nonbyz psent (localState w')) /\
  (lift_pkt_inv' node_psent_h2l_invariants_recv psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_recv psent (localState w')).
Proof.
  split; intros H; hnf in H |- *; intros [ src dst msg used ] Hin; specialize (H _ Hin).
  all: now eapply (h2l_invariants_id_pre Hstep _) in H; eauto.
Qed.

(* TODO copied from ABC *)
Fact h2l_invariants_pre :
  is_invariant_step_under id_coh (* needed, since will use psent_mnt_sound *)
    (fun w => lift_pkt_inv node_psent_h2l_invariants_sent_nonbyz w
      /\ lift_pkt_inv node_psent_h2l_invariants_recv w).
Proof with (repeat (progress (hnf in *; intros))); simplify_eq; (repeat (progress (hnf in *; saturate_assumptions))).
  hnf; intros q ?? Hcoh Hcoh' H Hstep. unfold lift_pkt_inv in H |- *. 
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply psent_mnt_sound in Hstep; try assumption.
  destruct Hstep as ([ b l | [ src dst msg ? ] ] & Hse & Hpsent); simpl in Hse, Hpsent.
  - (* nonbyz step *)
    destruct Hse as (Hb & Hse). 
    remember (sentMsgs w') as psent eqn:Htmp; clear Htmp. (* TODO generalize? *)
    revert psent Hpsent H Hse. 
    induction l as [ | a l IH ]; intros.
    all: simpl in Hse, Hpsent.
    (* TODO why we do not need to destruct H here (and only need to destruct later)? can I explain? *)
    + destruct b as [ | p' Hin' ]; simpl in Hb, Hpsent; hnf in Hpsent.
      * split_and?; intros ?; rewrite Hpsent; revert p; try now apply (h2l_invariants_id Hstep_ (sentMsgs w)).
      * split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H' by_ (destruct_and? H) end; 
          clear H; rename H' into H; setoid_rewrite Hpsent.
        1: intros [ src dst msg used ] Hin%(In_consume_conv_full Hin'). 
        1: destruct Hin as (used' & Hin); specialize (H _ Hin).
        --eapply (h2l_invariants_id_pre Hstep_) in H. simpl in H. exact H.
        --(* check which packet is received this time *)
          destruct p' as [ src' dst' msg' used' ].
          hnf in H |- *. intros p Hin%In_consume. simpl in Hin.
          destruct Hin as [ <- | (Hin & _) ].
          2: specialize (H _ Hin).
          1: destruct used'; [ specialize (H _ Hin') | ].
          1,3: eapply (h2l_invariants_id_pre Hstep_) in H; simpl in H; exact H.
          (* interesting part *)
          clear H. destruct Hb as (Hnonbyz & Hr).
          destruct msg' as [ r' v' pf' | r' lsig' ]; simpl in Hr.
          all: constructor; try exact I.
          all: hnf; simpl; auto.
    + destruct a as [ pkts tmp Hf Hcheck ]. simpl in *.
      clear Hb. destruct Hpsent as (psent_ & Hpmnt & Hineq), Hse as (Hse & Htmp).
      saturate_assumptions!. clear H.
      split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H by_ (destruct_and? IH) end; clear IH.
      all: intros p Hin%Hineq; autorewrite with psent in Hin.
      all: try (destruct Hin as [ Hin_pkts | ]; [ | solve [ intuition ] ]).
      all: destruct tmp as [ n m | src dst m ], Htmp as (Hnonbyz & Hb); simpl in Hcheck; subst pkts; 
        [ apply In_broadcast in Hin_pkts; destruct Hin_pkts as (dst & ->) | simpl in Hin_pkts; destruct Hin_pkts as [ <- | [] ] ].
      all: destruct m; simpl in Hb; constructor; hnf; auto; try tauto.
  - (* byz step; easy? *)
    destruct Hse as (Hbyz & -> & Hcb), Hpsent as (Els & Hpsent), H as (HHsent & HHrcv). 
    rewrite Hpsent, Els. clear Els Hpsent.
    split_and?; intros p; rewrite In_sendout1; intros [ <- | Hin ]; auto.
    all: constructor; hnf; destruct msg as [ | ]; simpl; intros; try solve [ auto | congruence | tauto ].
Qed.

Record node_psent_h2l_invariants_nonbyz p stmap : Prop := {
  _ : initmsg_sent_h2l p stmap;
  _ : echomsg_sent_h2l p stmap;
  _ : initmsg_recv_h2l p stmap;
  _ : echomsg_recv_h2l p stmap;
}.

Fact h2l_invariants :
  is_invariant_step_under id_coh (lift_pkt_inv node_psent_h2l_invariants_nonbyz).
Proof.
  hnf; intros q ?? Hcoh Hcoh' H Hstep. eapply h2l_invariants_pre in Hstep; eauto.
  - hnf in H |- *. intros p Hin. destruct Hstep as (Ha & Hc). 
    specialize (Ha _ Hin). specialize (Hc _ Hin). destruct Ha, Hc. now constructor.
  - split_and?; hnf; intros p Hin; specialize (H _ Hin); destruct H; now constructor.
Qed.

End Backward.

End PBInvariant.
