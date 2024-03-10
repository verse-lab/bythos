From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.ABC Require Export Nw.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module ACInvariant (A : NetAddr) (V : Signable) (VBFT : ValueBFT A V) 
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A V) (TSS : ThresholdSignatureScheme A V with Definition thres := BTh.t0).

Import A V VBFT BTh BSett P TSS.
Import ssrbool. (* anyway *)

Module Export ACN := ACNetwork A V VBFT BTh BSett P TSS.

Definition id_coh w : Prop := forall n, (w @ n).(id) = n.

(* state invariants *)

Notation NoDup := List.NoDup.

Definition inv_set_size st : Prop :=
  length st.(from_set) = length st.(collected_lightsigs) /\
  length st.(from_set) = length st.(collected_sigs).

Definition inv_conf_correct st : Prop :=
  if st.(conf)
  then length st.(from_set) = N - t0
  else length st.(from_set) < N - t0.

Definition inv_from_nodup st : Prop :=
  NoDup st.(from_set).

(* "NoDup nsigs" and "N - t0 <= (length nsigs)" should also hold 
    even if the certificate is sent by a Byzantine node *)

Definition inv_rlcerts st : Prop :=
  forall v cs, In (v, cs) st.(received_lightcerts) -> 
    combined_verify v cs.

Definition inv_rcerts_mixin st : Prop :=
  forall v nsigs, In (v, nsigs) st.(received_certs) -> 
    certificate_valid v nsigs /\
    (NoDup nsigs) /\ 
    N - t0 <= (length nsigs).

Definition inv_submit_mixin st : Prop :=
  match st.(submitted_value) with
  | Some v => 
    v = value_bft st.(id) /\
    light_signatures_valid v (zip_from_lsigs st) /\
    certificate_valid v (zip_from_sigs st)
  | None => st.(from_set) = nil
  end.

Definition inv_submit_none st : Prop :=
  st.(submitted_value) = None -> st.(from_set) = nil.

Fact inv_submit_mixin_break st : inv_submit_mixin st -> inv_submit_none st.
Proof. unfold inv_submit_mixin, inv_submit_none. intros H E. now rewrite E in H. Qed.

Definition buffer_nil_after_submit st : Prop :=
  st.(submitted_value) -> st.(msg_buffer) = nil.

Definition buffer_contains_submitmsg st : Prop :=
  forall nmsg, In nmsg st.(msg_buffer) ->
    match snd nmsg with SubmitMsg _ _ _ => True | _ => False end.

Definition confirmed_then_submitted st : Prop :=
  st.(conf) -> st.(submitted_value).

(* l2h, sent *)

Definition inv_submitted_broadcast psent st : Prop :=
  forall v, st.(submitted_value) = Some v ->
    let: src := st.(id) in
    forall n, exists used, 
      In (mkP src n (SubmitMsg v (light_sign v (lightkey_map src)) (sign v (key_map src))) used) psent.

Definition inv_conf_lightconfmsg psent st : Prop :=
  forall v, st.(submitted_value) = Some v ->
    st.(conf) -> forall n,
    exists used, In (mkP st.(id) n (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) used) psent.

Definition inv_conf_confmsg psent st : Prop :=
  forall v, st.(submitted_value) = Some v ->
    st.(conf) -> lightcert_conflict_check st.(received_lightcerts) -> (* coinciding with control flow *)
    forall n,
      exists used, In (mkP st.(id) n (ConfirmMsg (v, zip_from_sigs st)) used) psent.

(* l2h, recv *)

Definition inv_nsigs_correct psent st : Prop :=
  forall v, st.(submitted_value) = Some v ->
    forall n lsig sig, 
      In (n, lsig, sig) (zip_from_lsigs_sigs st) ->
        In (mkP n st.(id) (SubmitMsg v lsig sig) true) psent.

Definition inv_rlcerts_correct psent st : Prop :=
  forall lc,
    In lc st.(received_lightcerts) ->
      exists src, In (mkP src st.(id) (LightConfirmMsg lc) true) psent.

Definition inv_rcerts_correct psent st : Prop :=
  forall c,
    In c st.(received_certs) ->
      exists src, In (mkP src st.(id) (ConfirmMsg c) true) psent.

Definition inv_buffer_received psent st : Prop :=
  forall nmsg, In nmsg st.(msg_buffer) ->
    In (mkP (fst nmsg) st.(id) (snd nmsg) true) psent.

(* h2l, sent *)

Definition inv_submitmsg_correct p stmap : Prop :=
  match p with
  | mkP src dst (SubmitMsg v lsig sig) used =>
    let: st := stmap src in
    is_byz src = false ->
      verify v sig src /\
      light_verify v lsig src /\
      st.(submitted_value) = Some v (* TODO why put some at LHS? *)
  | _ => True
  end.

(* CHECK conjecture: only Byzantine messages require the history argument?
  only non-Byz messages require the stmap argument? *)
Definition inv_lightconfirmmsg_correct_nonbyz p stmap : Prop :=
  match p with
  | mkP src dst (LightConfirmMsg lc) used =>
    let: st := stmap src in
    is_byz src = false ->
      st.(conf) /\ st.(submitted_value) = Some (fst lc) /\
      snd lc = lightsig_combine st.(collected_lightsigs)
  | _ => True
  end.

Definition inv_lightconfirmmsg_correct_byz p psent_history : Prop :=
  match p with
  | mkP src dst (LightConfirmMsg lc) used =>
    is_byz src -> lcert_correct_threshold psent_history lc
  | _ => True
  end.

Definition inv_confirmmsg_correct_nonbyz p stmap : Prop :=
  match p with
  | mkP src dst (ConfirmMsg c) used =>
    let: st := stmap src in
    is_byz src = false ->
      st.(conf) /\ lightcert_conflict_check st.(received_lightcerts) (* this is new *)
      /\ st.(submitted_value) = Some (fst c) /\
      snd c = zip_from_sigs st
  | _ => True
  end.

Definition inv_confirmmsg_correct_byz p psent_history : Prop :=
  match p with
  | mkP src dst (ConfirmMsg c) used =>
    is_byz src -> cert_correct psent_history c
  | _ => True
  end.

(* h2l, recv *)

(* this is a rather non-trivial invariant since it depends on node state
    and should be proved individually *)
Definition inv_submitmsg_receive_ p st : Prop :=
  match p.(msg) with
  | SubmitMsg v lsig sig =>
    if p.(consumed)
    then
      let: src := p.(src) in
      let: dst := p.(dst) in
      is_byz dst = false ->
      match st.(submitted_value) with
      | None => In (src, SubmitMsg v lsig sig) st.(msg_buffer)
      | Some ov => 
        (* the length condition may be more natural, but it would be hard to reason about 
          without invariant 1; so replace it with the condition on conf *)
        (* length st.(from_set) < N - t0 -> *)
        st.(conf) = false ->
        v = ov -> verify v sig src -> light_verify v lsig src ->
          In src st.(from_set) (* this should be enough; TODO why no need to write zip_from_sigs? *)
      end
    else True
  | _ => True
  end.

Definition inv_submitmsg_receive p stmap : Prop := inv_submitmsg_receive_ p (stmap p.(dst)).

Definition inv_lightconfirmmsg_receive p stmap : Prop :=
  match p with
  | mkP src dst (LightConfirmMsg (v, cs)) true =>
    let: st := stmap dst in
    is_byz dst = false ->
    combined_verify v cs -> In (v, cs) st.(received_lightcerts)
  | _ => True
  end.

Definition inv_confirmmsg_receive p stmap : Prop :=
  match p with
  | mkP src dst (ConfirmMsg (v, nsigs)) true =>
    let: st := stmap dst in
    is_byz dst = false ->
    certificate_valid v nsigs -> NoDup nsigs -> (N - t0 <= (length nsigs)) ->
      In (v, nsigs) st.(received_certs)
  | _ => True
  end.

(* persistence *)

Definition submitted_value_persistent st st' : Prop :=
  forall v, st.(submitted_value) = Some v -> st'.(submitted_value) = Some v.

Definition conf_persistent st st' : Prop := st.(conf) -> st'.(conf).

(* ideally, this would be used together with "buffer_nil_after_submit" *)
Definition msg_buffer_nil_persistent st st' : Prop := 
  st.(submitted_value) -> st.(msg_buffer) = nil -> st'.(msg_buffer) = nil.

Definition msg_buffer_notnil_persistent st st' : Prop := 
  st'.(submitted_value) = None -> 
  forall nmsg, In nmsg st.(msg_buffer) -> In nmsg st'.(msg_buffer).

(* the following will be useful in proving psent_mnt_sound *)
Definition conf_from_set_persistent st st' : Prop := 
  st.(conf) -> st.(from_set) = st'.(from_set).

Definition conf_collected_lightsigs_persistent st st' : Prop := 
  st.(conf) -> st.(collected_lightsigs) = st'.(collected_lightsigs).

Definition conf_collected_sigs_persistent st st' : Prop := 
  st.(conf) -> st.(collected_sigs) = st'.(collected_sigs).

Definition from_set_persistent st st' : Prop :=
  forall n, In n st.(from_set) -> In n st'.(from_set).

Definition received_lightcerts_persistent st st' : Prop := 
  forall lc, In lc st.(received_lightcerts) -> In lc st'.(received_lightcerts).

Definition received_certs_persistent st st' : Prop := 
  forall c, In c st.(received_certs) -> In c st'.(received_certs).

Fact lightcert_conflict_check_persistent st st' (H : received_lightcerts_persistent st st') :
  lightcert_conflict_check st.(received_lightcerts) ->
  lightcert_conflict_check st'.(received_lightcerts).
Proof.
  intros Hb. rewrite lightcert_conflict_check_correct in Hb |- *. 
  destruct Hb as (v1 & v2 & cs1 & cs2 & Hb). destruct_and? Hb.
  exists v1, v2, cs1, cs2. hnf in H. intuition.
Qed.

Definition id_persistent st st' : Prop := st.(id) = st'.(id).

Fact valid_cert_valid_sig v nsigs
  (Hcert_valid : certificate_valid v nsigs) 
  n sig (Hin : In (n, sig) nsigs) : sig = sign v (key_map n).
Proof.
  unfold certificate_valid in Hcert_valid.
  rewrite -> Forall_forall in Hcert_valid.
  now apply Hcert_valid, key_correct in Hin.
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
    destruct Hcert_valid as (Hveri & Hcert_valid).
    rewrite <- key_correct in Hveri.
    subst sig.
    constructor.
    + intros Hin.
      now eapply valid_cert_sender_in in Hin; eauto.
    + apply IH; intuition.
Qed.

Section Main_Proof.

Set Implicit Arguments. (* anyway *)

Tactic Notation "simpl_state" :=
  simpl id in *; simpl conf in *; simpl submitted_value in *; simpl from_set in *;
  simpl collected_lightsigs in *; simpl collected_sigs in *; simpl received_lightcerts in *; 
  simpl received_certs in *; simpl msg_buffer in *.

Create HintDb ABCinv.

Tactic Notation "basic_solver" :=
  try reflexivity; auto with ABCinv; try tauto; try eqsolve; try lia.

Local Hint Resolve correct_sign_verify_ok correct_sign_verify_ok_light : ABCinv.

Local Hint Resolve incl_sendout_l incl_sendout_r incl_sendout_app_l incl_sendout_app_r : ABCinv.

Local Hint Resolve incl_nil_l : datatypes.

Section State_Monotone_Proofs.

Inductive state_mnt_type (st : State) : Type :=
  | Msubmit : st.(submitted_value) = None -> state_mnt_type st
  | Mconf : forall v, st.(submitted_value) = Some v ->
    (* conf may be already true *) state_mnt_type st
  | Mfrom_in : forall src v lsig sig, 
    st.(submitted_value) = Some v ->
    verify v sig src -> light_verify v lsig src ->
    st.(conf) = false -> ~ In src st.(from_set) -> state_mnt_type st
  | Mfrom_buffer : forall (src : Address) (v : Value) (lsig : LightSignature) (sig : Signature), 
    st.(submitted_value) = None -> state_mnt_type st
  | Mlcert : forall (src : Address) v cs,
    combined_verify v cs -> state_mnt_type st
  | Mcert : forall (src : Address) v nsigs,
    NoDup nsigs -> (N - t0) <= length nsigs -> certificate_valid v nsigs -> 
    state_mnt_type st
(*   
  | Mcheck : forall v, (* even the state will not change, it is still required for l2h proof *)
    st.(submitted_value) = Some v ->
    st.(conf) -> lightcert_conflict_check st.(received_lightcerts) ->
    state_mnt_type st
     *)
.

Global Arguments Mconf : clear implicits.
Global Arguments Mfrom_in : clear implicits.
Global Arguments Mlcert : clear implicits. 
Global Arguments Mcert : clear implicits. 
(* Global Arguments Mcheck : clear implicits.  *)

Definition state_mnt (st : State) (s : state_mnt_type st) : State :=
  match s with
  | Msubmit _ _ =>
    (st <| submitted_value := Some (value_bft st.(id)) |>
        <| msg_buffer := nil |>)
  | Mconf _ _ _=>
    (st <| conf := true |>)
  | Mfrom_in _ src _ lsig sig _ _ _ _ _ =>
    (st <| from_set := src :: st.(from_set) |>
        <| collected_lightsigs := lsig :: st.(collected_lightsigs) |> 
        <| collected_sigs := sig :: st.(collected_sigs) |>)
  | Mfrom_buffer _ src v lsig sig _ =>
    (st <| msg_buffer := (src, SubmitMsg v lsig sig) :: st.(msg_buffer) |>)
  | Mlcert _ _ v cs _ =>
    (st <| received_lightcerts := (v, cs) :: st.(received_lightcerts) |>)
  | Mcert _ _ v nsigs _ _ _ =>
    (st <| received_certs := (v, nsigs) :: st.(received_certs) |>)
  (* | Mcheck _ v _ _ _ =>
    st *)
  end.

Definition confirmmsg_bcast st :=
  match st.(submitted_value) with
  | Some v => broadcast st.(id) (ConfirmMsg (v, zip_from_sigs st))
  | None => nil
  end.

(* I guess in theory, there isn't a perfect solution;
    either prove "inv_buffer_received" first (which means you would need another 2-3 proofs, 
    one being induction), or have a ghost variable like this (and potentially complicate
    other proofs). *) 
(* the ghost variable "other_pkts" is really like opening a backdoor ... *)
(* ... which greatly complicates the other proofs. I can no longer tolerate it *)
(*
Definition psent_effect (st : State) (s : state_mnt_type st) (n : Address) (psent : PacketSoup) (other_pkts : list Packet) : Prop :=
  Eval unfold confirmmsg_bcast in
  match s with
  | Msubmit _ _ =>
    let: n := st.(id) in
    let: v := value_bft n in
    let: pkts := broadcast n (SubmitMsg v (light_sign v (lightkey_map n)) (sign v (key_map n))) in
    incl pkts psent
  | Mconf _ v _ =>
    (* let: pkts := broadcast st.(id) (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) in
    incl pkts psent *)
    (* HMM might be a trick *)
    (let: pkts := broadcast st.(id) (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) in
    incl pkts psent) /\
    (lightcert_conflict_check st.(received_lightcerts) ->
    incl (confirmmsg_bcast st) psent)
  | Mfrom_in _ src v lsig sig _ _ _ _ _ =>
    In (mkP src n (SubmitMsg v lsig sig) true) psent
    \/ In (mkP src n (SubmitMsg v lsig sig) true) other_pkts (* ghost state? *)
  | Mfrom_buffer _ src v lsig sig _ =>
    In (mkP src n (SubmitMsg v lsig sig) true) psent
  | Mlcert _ src v cs _ =>
    (In (mkP src n (LightConfirmMsg (v, cs)) true) psent
    \/ In (mkP src n (LightConfirmMsg (v, cs)) true) other_pkts) 
    /\
    (st.(conf) -> lightcert_conflict_check ((v, cs) :: st.(received_lightcerts)) ->
    incl (confirmmsg_bcast st) psent)
  | Mcert _ src v nsigs _ _ _ =>
    In (mkP src n (ConfirmMsg (v, nsigs)) true) psent
    \/ In (mkP src n (ConfirmMsg (v, nsigs)) true) other_pkts
  (* | Mcheck _ v _ _ _ =>
    let: pkts := broadcast st.(id) (ConfirmMsg (v, zip_from_sigs st)) in
    incl pkts psent *)
  end.
*)
Definition psent_effect (st : State) (s : state_mnt_type st) (n : Address) (psent : PacketSoup) : Prop :=
  Eval unfold confirmmsg_bcast in
  match s with
  | Msubmit _ _ =>
    let: n := st.(id) in
    let: v := value_bft n in
    let: pkts := broadcast n (SubmitMsg v (light_sign v (lightkey_map n)) (sign v (key_map n))) in
    incl pkts psent
  | Mconf _ v _ =>
    (* let: pkts := broadcast st.(id) (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) in
    incl pkts psent *)
    (* HMM might be a trick *)
    (let: pkts := broadcast st.(id) (LightConfirmMsg (v, lightsig_combine st.(collected_lightsigs))) in
    incl pkts psent) /\
    (lightcert_conflict_check st.(received_lightcerts) ->
    incl (confirmmsg_bcast st) psent)
  | Mfrom_in _ src v lsig sig _ _ _ _ _ =>
    In (mkP src n (SubmitMsg v lsig sig) true) psent
  | Mfrom_buffer _ src v lsig sig _ =>
    In (mkP src n (SubmitMsg v lsig sig) true) psent
  | Mlcert _ src v cs _ =>
    In (mkP src n (LightConfirmMsg (v, cs)) true) psent
    /\
    (st.(conf) -> lightcert_conflict_check ((v, cs) :: st.(received_lightcerts)) ->
    incl (confirmmsg_bcast st) psent)
  | Mcert _ src v nsigs _ _ _ =>
    In (mkP src n (ConfirmMsg (v, nsigs)) true) psent
  end.

Inductive state_mnt_type_list : State -> State -> Type :=
  | MNTnil : forall st, state_mnt_type_list st st
  | MNTcons : forall st (d : state_mnt_type st) st', 
    state_mnt_type_list (state_mnt d) st' ->
    state_mnt_type_list st st'.

Fixpoint state_mnt_type_list_app [st st' st''] (l1 : state_mnt_type_list st st') (l2 : state_mnt_type_list st' st'') 
  : state_mnt_type_list st st''.
  destruct l1.
  - exact l2.
  - exact (MNTcons d (state_mnt_type_list_app _ _ _ l1 l2)).
Defined.
(*
Fixpoint psent_effect_star (n : Address) (psent : PacketSoup) (other_pkts : list Packet) [st st'] (l : state_mnt_type_list st st') : Prop :=
  match l with
  | MNTnil _ => True
  | MNTcons d l' =>
    psent_effect d n psent other_pkts /\ psent_effect_star n psent other_pkts l' (* TODO setting implicit during definition? *)
  end.
*)
Fixpoint psent_effect_star (n : Address) (psent : PacketSoup) [st st'] (l : state_mnt_type_list st st') : Prop :=
  match l with
  | MNTnil _ => True
  | MNTcons d l' =>
    psent_effect d n psent /\ psent_effect_star n psent l' (* TODO setting implicit during definition? *)
  end.
(*
Lemma psent_effect_star_app n psent others st st' st'' (l1 : state_mnt_type_list st st') (l2 : state_mnt_type_list st' st'') :
  psent_effect_star n psent others (state_mnt_type_list_app l1 l2) <-> 
  psent_effect_star n psent others l1 /\ psent_effect_star n psent others l2.
Proof. revert st'' l2. induction l1; intros; simpl; try tauto. rewrite IHl1. tauto. Qed.

Lemma psent_effect_star_incl n psent psent' others others' st st' (l : state_mnt_type_list st st')
  (H : psent_effect_star n psent others l) (Hincl : incl psent psent') (Hincl' : incl others others') :
  psent_effect_star n psent' others' l.
Proof. induction l; simpl in *; auto. destruct H. split; auto. destruct d; simpl in *; unfold incl in *; intuition. Qed.
*)
Lemma psent_effect_star_app n psent st st' st'' (l1 : state_mnt_type_list st st') (l2 : state_mnt_type_list st' st'') :
  psent_effect_star n psent (state_mnt_type_list_app l1 l2) <-> 
  psent_effect_star n psent l1 /\ psent_effect_star n psent l2.
Proof. revert st'' l2. induction l1; intros; simpl; try tauto. rewrite IHl1. tauto. Qed.

Lemma psent_effect_star_incl n psent psent' st st' (l : state_mnt_type_list st st')
  (H : psent_effect_star n psent l) (Hincl : incl psent psent') :
  psent_effect_star n psent' l.
Proof. induction l; simpl in *; auto. destruct H. split; auto. destruct d; simpl in *; unfold incl in *; intuition. Qed.
(* 
(* false: stopping token *)
Local Ltac state_analyze_select f x :=
  match f with
  | msg_buffer =>
    match x with
    | _ :: _ => uconstr:(Mfrom_buffer)
    | _ => uconstr:(false)
    end
  | collected_sigs => uconstr:(Mfrom_in)
  | received_lightcerts => uconstr:(Mlcert)
  | received_certs => uconstr:(Mcert)
  | _ => uconstr:(false)
  end. 
*)
(* TODO eassumption is not stable ... mostly manual analysis below *)
Ltac analyze_step ctor tac :=
  unshelve eapply MNTcons; [ eapply ctor; tac | ]; simpl.
(*
Ltac state_analyze' st' :=
  match st' with
  | set ?f (fun _ => ?vv) ?st =>
    let ctor := state_analyze_select f vv in
    match ctor with
    | false => idtac
    | _ =>
      state_analyze' st;
      match goal with 
      | |- state_mnt_type_list _ _ =>
        unshelve eapply MNTcons; [ eapply ctor | ]; simpl
      | _ => idtac
      end
    end
  | _ => idtac
  end.
*)
Ltac psent_effect_star_solver :=
  simpl; autorewrite with psent; rewrite ! In_consume; simpl; try solve [ tauto | intuition | basic_solver ].

(* TODO this seems not to work as intended *)
Ltac state_invariants_pre_solver :=
  try solve 
    [ constructor; hnf; intros HH; hnf in HH |- *; intros; simpl in *; basic_solver; try (now isSome_rewrite)
    | intros; try rewrite sendout0; autorewrite with psent; 
      solve [ auto using In_consume_fwd_full' with ABCinv |
        intuition (auto using In_consume_fwd_full' with ABCinv) ] (* for inv_buffer_received *) ].

Ltac local_solver := split_and?; try solve [ intros; eqsolve | psent_effect_star_solver | state_invariants_pre_solver ].
(*
Ltac state_analyze :=
  try rewrite sendout0;
  match goal with
  | |- exists (_ : state_mnt_type_list _ ?st'), _ =>
    unshelve eexists; [ state_analyze' st'; try solve [ apply (MNTnil _) ] | ];
    split_and?;
    match goal with
    | |- @psent_effect_star _ _ _ _ _ => psent_effect_star_solver
    | _ => try solve [ basic_solver ]
    end
  end.
*)
Definition lift_point_to_edge {A : Type} (P : A -> Prop) : A -> A -> Prop :=
  fun st st' => P st -> P st'.

(* here no need to put too many things in *)
Record node_state_invariants_pre st st' : Prop := {
  _ : lift_point_to_edge inv_conf_correct st st';
  (* _ : lift_point_to_edge confirmed_then_submitted st st'; *)
}.
(*
Fact inv_conf_confmsg_incl psent psent' st (H : inv_conf_confmsg psent st)
  (Hincl : incl psent psent') : inv_conf_confmsg psent' st.
Proof. hnf in *. intros. saturate_assumptions!. destruct H. specialize (Hincl _ H). eauto. Qed.
*)
(* the conditions get complicated to accommodate the ghost variable *)
(*
Fact state_mnt_sound_pre_pre p (Hnonbyz : is_byz (dst p) = false) stf msf w w'
  (Ef : procMsgWithCheck (w @ dst p) (src p) (msg p) = (stf, msf))
  psent others (E0 : w' = mkW (upd (dst p) stf (localState w)) (sendout msf psent))
  (*
  (Hothers : match (w @ dst p).(submitted_value) with None => others = nil | _ => True end)
  (Hin : In (receive_pkt p) psent \/ (match p.(msg) with SubmitMsg _ _ _ => In (receive_pkt p) others | _ => False end)) :
  *)
  (Hothers : match (w @ dst p).(submitted_value) with None => others = nil | _ => True end)
  (Hin : In (receive_pkt p) psent \/ In (receive_pkt p) others) :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') others l /\ node_state_invariants_pre (w @ n) (w' @ n).
Proof with (try (now exists (MNTnil _))).
  destruct p as [ src dst msg used ]. simpl_pkt. subst w'. simpl. intros n. unfold procMsgWithCheck in Ef.
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ]...
  destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef; simplify_eq...
  destruct (w @ dst) as [ dst' conf ov from lsigs sigs rlcerts rcerts buffer ].
  destruct msg as [ v ls s | (v, cs) | (v, nsigs) ]; simpl in E.
  1-2: simplify_eq. (* pair inj *)
  1: simpl in Hin.
  - destruct ov as [ vthis | ].
    + destruct (andb _ _) eqn:EE in E; try discriminate. 
      unfold is_left in EE. rewrite ! andb_true_iff, sumbool_is_left in EE. destruct EE as ((-> & Everi) & Elveri).
      destruct conf.
      * simplify_eq. unshelve eexists. 1: analyze_step Mconf ltac:(idtac); try apply MNTnil; try reflexivity. 
        simpl. destruct (lightcert_conflict_check _) in |- *; simpl.
        all: local_solver.
      * destruct (in_dec _ _ _) as [ | Hnotin ] in E; try discriminate. simplify_eq.
        destruct (N - t0 <=? S (length from)) eqn:Eth; 
          [ apply Nat.leb_le in Eth | apply Nat.leb_nle in Eth ].
        all: unshelve eexists; [ analyze_step Mfrom_in ltac:(try eassumption); auto | ]; try apply MNTnil.
        1: analyze_step Mconf ltac:(idtac); auto. 1: apply MNTnil.
        all: simpl. 1: destruct (lightcert_conflict_check _) in |- *; simpl.
        all: local_solver.
    + simplify_eq. simpl. unshelve eexists. 1: analyze_step Mfrom_buffer ltac:(idtac); try apply MNTnil; try reflexivity.
      (* since here is for buffer, need to make sure that others = nil, so we need Hothers *)
      simpl. simpl in Hothers. subst others. simpl in Hin. local_solver.
  - destruct (combined_verify _ _) eqn:EE in E; try discriminate.
    simplify_eq. unshelve eexists. 1: analyze_step Mlcert ltac:(idtac); try apply MNTnil; try reflexivity.
    1: apply src. 1: auto. (* need to manually instantiate src here *)
    simpl. unfold zip_from_sigs. simpl. rewrite app_nil_r.
    destruct ov in |- *; [ destruct (andb _ _) eqn:EE0 in |- *; 
      [ rewrite andb_true_iff in EE0 | rewrite andb_false_iff in EE0 ]; destruct EE0; try is_true_rewrite | ]; simpl.
    all: local_solver.
    (* ... *)
    + (* TODO automation is so weak???? *) now setoid_rewrite H.
    + auto with datatypes.
  - destruct (andb _ _) eqn:EE in E; try discriminate.
    unfold is_left in EE. rewrite ! andb_true_iff, ! sumbool_is_left, Nat.leb_le in EE. destruct_and? EE.
    simplify_eq. unshelve eexists. 1: analyze_step Mcert ltac:(idtac); try apply MNTnil; try reflexivity.
    1: apply src. all: auto. (* need to manually instantiate src here *)
    simpl. local_solver.
Qed.

Fact state_mnt_sound_pre q (Hq_ : forall n t, q <> Intern n t) 
  w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') nil l /\ node_state_invariants_pre (w @ n) (w' @ n).
    (* /\ (id (w @ n) = n (* ! *) -> is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n) -> 
      inv_buffer_received (sentMsgs w') (w' @ n)). *)
Proof with (try (now exists (MNTnil _))).
  unfold inv_buffer_received.
  inversion_step' Hstep; clear Hstep; intros... 
  2: exfalso; eapply Hq_; reflexivity.
  pose proof (@state_mnt_sound_pre_pre (mkP src dst msg used) Hnonbyz stf msf
    w _ Ef (consume (mkP src dst msg used) (sentMsgs w)) nil eq_refl) as H.
  simpl in H. apply H. now destruct (submitted_value _) in |- *. rewrite In_consume. auto.
Qed.

Definition buffer_augment n buf :=
  map (fun nmsg => mkP (fst nmsg) n (snd nmsg) true) buf.

Fact state_mnt_sound q w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') 
      (match q with Intern _ _ => buffer_augment n (w @ n).(msg_buffer) | _ => nil end) l /\ 
    node_state_invariants_pre (w @ n) (w' @ n).
    (* /\ (id (w @ n) = n (* ! *) -> is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n) -> 
      inv_buffer_received (sentMsgs w') (w' @ n)). *)
(* Proof with (try solve [ exists (MNTnil _); simpl; split_and?; local_solver ]). *)
Proof with (try (now exists (MNTnil _))).
  unfold inv_buffer_received.
  destruct q as [ | | n0 t | ]. 1,2,4: eapply state_mnt_sound_pre; try eassumption; auto.
  inversion_step' Hstep; clear Hstep; intros; try discriminate.
  revert Hq. intros [= ->].
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ]...
  destruct t1, (w @ n) as [ n' conf ov from lsigs sigs rlcerts rcerts buffer ].
  simpl in E. simpl.
  destruct ov. 1: simplify_eq...
  destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in E. simplify_eq.
  (* this is great *)
  change (set _ _ (set _ _ _)) with (Node n' conf (Some (value_bft n')) from lsigs sigs rlcerts rcerts nil) in Efr.
  remember (Node _ _ _ _ _ _ _ _ _) as stt eqn:Es in Efr.
  match goal with |- exists (_ : _), (psent_effect_star _ ?pp ?ot _) /\ _ =>
    assert (exists l : state_mnt_type_list stt st', psent_effect_star n pp ot l /\ node_state_invariants_pre stt st') as Hgoal end.
  all: subst stt.
  (* time to do induction *)
  { revert st' ps_ Efr. induction buffer as [ | (src, msg) buffer IH ]; intros; simpl in Efr.
    - simplify_eq...
    - simpl.
      destruct (procMsgWithCheck _ _ _) as (sta, psa) eqn:E0 in Efr.
      destruct (fold_right _ _ _) as (stb, psb) eqn:E1 in Efr. rewrite E1 in E0. simpl in E0, Efr. 
      revert Efr. intros [= <- <-].
      saturate_assumptions!. destruct IH as (l & Ha & HH).
      (* use persistence here *)
      pick submitted_value_persistent as_ Hv by_ (destruct HH). simpl in Hv. specialize (Hv _ eq_refl).
      (* use the previous lemma *)
      pose proof (@state_mnt_sound_pre_pre (mkP src n msg true) Hnonbyz sta psa
        (mkW (upd n stb (localState w)) (sentMsgs w)) _ ltac:(simpl; rewrite upd_refl; assumption)
        (sentMsgs w) (mkP src n msg true :: nil) eq_refl ltac:(simpl; rewrite upd_refl, Hv; auto) ltac:(simpl; auto) n) as Hgoal.
      simpl in Hgoal. rewrite ! upd_refl in Hgoal. destruct Hgoal as (l0 & Ha0 & HH0).
      exists (state_mnt_type_list_app l l0). 
      rewrite psent_effect_star_app. split; [ split; [ eapply psent_effect_star_incl; try apply Ha | eapply psent_effect_star_incl; try apply Ha0 ] | ].
      1-4: hnf; intros ?; autorewrite with psent; simpl; tauto.
      pick submitted_value_persistent as_ Hv0 by_ (destruct HH0). specialize (Hv0 _ Hv).
      destruct HH, HH0. hnf in *. state_invariants_pre_solver. }
  destruct Hgoal as (l & Ha & HH).
  unshelve eexists. 1: analyze_step Msubmit ltac:(idtac); try apply MNTnil; try reflexivity. 1: apply l.
  simpl; local_solver.
  (* TODO still need some cleaning! *)
  destruct HH as [ HH1 HH2 HH3 ]. hnf in *. constructor; auto; try discriminate. 
  hnf; intros; hnf in *; intros. apply HH2; auto. now hnf.
Qed.
*)
Definition lift_node_inv (P : PacketSoup -> State -> Prop) : World -> Prop :=
  fun w => forall n, is_byz n = false -> P (sentMsgs w) (w @ n).

(* FIXME: 

  This poses a problem about proving invariants: sometimes several invariants need 
  to be grouped together to prove, otherwise we need several proofs for each invariant. 
  However, proving the grouped invariants will make the invariants "harder" to use, 
  since we need to satisfy all the invariants at the same time to use only one of them. 

  One way to work around is to use the notion of reachable worlds. By proving the 
  grouped invariant always holds on reachable worlds, one can then "split" the grouped
  invariants. However, this is also not perfect since this requires the world to be 
  actually reachable. When we do not know that condition or that condition has to be 
  proved separately (e.g., by simulation), things will again get complicated. 
  This can happen when there is (mutual recursion) between transitions; see ABC for 
  an example. 

  Another potentially better way is to have finer-grained dependency. For example, if
  invariant B depends on A, while A only depends on itself, then the proof goal can be 
  written as:

  (A -> A') /\ (A /\ B -> B')

  This nevertheless requires some repeating in the proof goal and some intricate 
  manipulation of the proof context (e.g., the hypotheses are different for each subgoal), 
  but should be able to resolve the problem above. 

  Maybe in the future, we can consider develop some way to state that dependency easily 
  and manage the proof context. 
*)
Fact inv_buffer_received_only_pre q (Hq_ : forall n t, q <> Intern n t) 
  w w' (Hstep : system_step q w w') 
  (H : forall n, (w @ n).(id) = n /\ (is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n))
    /\ ((w @ n).(submitted_value) -> (w @ n).(msg_buffer) = nil)) :
  (* we need all four of them for the induction proof *)
  forall n, (w' @ n).(id) = n /\ (is_byz n = false -> inv_buffer_received (sentMsgs w') (w' @ n))
    /\ ((w' @ n).(submitted_value) -> (w' @ n).(msg_buffer) = nil)
    /\ submitted_value_persistent (w @ n) (w' @ n).
Proof with (intros; rewrite ?sendout0; try (rewrite In_sendout; right); eauto using In_consume_fwd_full').
  (* destruct H as (Hcoh & Hrcv).
  unfold id_coh, lift_node_inv.
  enough (forall n, id (w' @ n) = n /\ (is_byz n = false → inv_buffer_received (sentMsgs w') (w' @ n))) as H.
  { split; intros n; specialize (H n); destruct H; saturate_assumptions; auto. }
  intros n. specialize (Hrcv n). *)
  intros n. specialize (H n). destruct H as (Hcoh & Hrcv & Hs).
  unfold inv_buffer_received, submitted_value_persistent in *.
  inversion_step' Hstep; clear Hstep; auto.
  3:{ split_and?; auto. intros. rewrite In_sendout1. right. eapply Hrcv; eauto. }
  2: exfalso; eapply Hq_; reflexivity.
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ].
  2: split_and?; auto...
  destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef; simplify_eq.
  2: split_and?; auto...
  (* get stf first *)
  destruct (w @ dst) as [ dst' conf ov from lsigs sigs rlcerts rcerts buffer ] eqn: Est. simpl_state. subst dst'.
  destruct msg as [ v ls s | (v, cs) | (v, nsigs) ]; simpl in E; simplify_eq. (* pair inj *)
  - destruct ov as [ vthis | ].
    + destruct (andb _ _) eqn:EE, conf in E; try discriminate; simplify_eq; simpl.
      1: split_and?; auto...
      destruct (in_dec _ _ _) as [ | Hnotin ] in E; try discriminate. simplify_eq. simpl.
      split_and?; auto...
    + simplify_eq. simpl. split_and?; auto; try discriminate. 
      intros ?? [ <- | Hin ]; simpl... rewrite In_consume. tauto.
  - destruct (combined_verify _ _) eqn:EE in E; try discriminate.
    simplify_eq. split_and?; auto...
  - destruct (andb _ _) eqn:EE in E; try discriminate.
    simplify_eq. split_and?; auto...
Qed.

Fact inv_buffer_received_only q w w' (Hstep : system_step q w w') 
  (H : forall n, (w @ n).(id) = n /\ (is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n))
    /\ ((w @ n).(submitted_value) -> (w @ n).(msg_buffer) = nil)) :
  forall n, (w' @ n).(id) = n /\ (is_byz n = false -> inv_buffer_received (sentMsgs w') (w' @ n))
    /\ ((w' @ n).(submitted_value) -> (w' @ n).(msg_buffer) = nil)
    /\ submitted_value_persistent (w @ n) (w' @ n).
Proof.
  destruct q as [ | | n t | ]. 
  1,2,4: eapply inv_buffer_received_only_pre; try eassumption; auto.
  unfold inv_buffer_received, submitted_value_persistent in *. intros n0.  
  inversion_step' Hstep; intros; try discriminate.
  revert Hq. intros [= <-]. destruct t1. 
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ].
  2: split_and?; auto; try apply H; intros; rewrite In_sendout; right; now apply H.
  pose proof (proj1 (proj2 (H n)) Hnonbyz) as Hrcv. (* dealing with the in-out id issue, instantiate one for n *)
  pose proof (fun n => proj1 (H n)) as Hcoh. pose proof (proj2 (proj2 (H n))) as Hs.
  destruct_localState w n as_ [ ? conf ov from lsigs sigs rlcerts rcerts buffer ] eqn_ Est. simpl_state.
  simpl in E.
  destruct ov as [ v | ].
  1: simplify_eq; simpl; split_and?; auto; intros; rewrite sendout0; now apply Hrcv.  
  destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in E. simplify_eq.
  change (set _ _ (set _ _ _)) with (Node n conf (Some (value_bft n)) from lsigs sigs rlcerts rcerts nil) in Efr. (* the extensionality is great *)
  (* these are what we need to maintain in the induction proof *)
  enough (id st' = n /\ st'.(msg_buffer) = nil /\ st'.(submitted_value)) as (<- & -> & _).
  1: simpl; split_and?; auto; try discriminate; try contradiction.
  (* time to do induction *)
  clear Hstep Est Hs. revert st' ps_ Efr.
  induction buffer as [ | (src, msg) buffer IH ]; intros; simpl in Efr.
  - now simplify_eq.
  - destruct (procMsgWithCheck _ _ _) as (sta, psa) eqn:E0 in Efr.
    destruct (fold_right _ _ _) as (stb, psb) eqn:E1 in Efr. rewrite E1 in E0. simpl in E0, Efr. 
    revert Efr. intros [= <- <-].
    simpl in Hrcv. specialize (IH (fun a H => Hrcv a (or_intror H))).
    saturate_assumptions! in_ IH. destruct IH as (Hidb & Hsb & Hvv).
    (* use the previous lemma *)
    specialize (Hrcv _ (or_introl eq_refl)). simpl in Hrcv.
    epose proof (DeliverStep (Deliver (mkP src n msg true)) (mkW (upd n stb (localState w)) (sentMsgs w))
      _ _ eq_refl Hrcv Hnonbyz ?[Goalq]).
    [Goalq]: simpl; rewrite upd_refl, E0; reflexivity.
    eapply inv_buffer_received_only_pre with (n:=n) in H0; auto.
    2:{ simpl. intros. unfold upd. destruct (Address_eqdec _ _) as [ <- | Hneq ]; auto.
      split_and?; auto. unfold inv_buffer_received. rewrite Hsb. simpl. contradiction. }
    simpl in H0. rewrite !upd_refl in H0. destruct H0 as (? & _ & Hq1 & Hq2).
    hnf in Hq2. destruct (stb.(submitted_value)) eqn:Ea; try discriminate. specialize (Hq2 _ eq_refl).
    isSome_rewrite; auto.
Qed.

Definition lift_state_inv (P : State -> Prop) : World -> Prop := fun w => forall n, P (w @ n).

Fact inv_buffer_received_only_reformat : always_holds
  (fun w => id_coh w /\ lift_node_inv inv_buffer_received w /\ lift_state_inv buffer_nil_after_submit w).
Proof.
  apply grounded_invariant_always_holds. hnf; split.
  1: split_and?; hnf; intros; hnf in *; intros; try reflexivity; try contradiction.
  intros ??? (H1 & H2 & H3) Hstep. 
  split_and?; intros n; eapply inv_buffer_received_only with (n:=n) in Hstep; try (intros; split_and?; hypothesis).
  all: tauto.
Qed.

Fact id_coh_always_holds : always_holds id_coh.
Proof. always_holds_decompose inv_buffer_received_only_reformat. Qed.

(* HMM just proving always_hold may also be not satisfactory, since this is actually weaker 
    than being an invariant ... this issue may come out in some other proofs that depend
    on these invariants (e.g., proofs using id_coh) *)
Fact inv_buffer_received_always_holds : always_holds (lift_node_inv inv_buffer_received).
Proof. always_holds_decompose inv_buffer_received_only_reformat. Qed.

Fact buffer_nil_after_submit_holds : always_holds (lift_state_inv buffer_nil_after_submit).
Proof. always_holds_decompose inv_buffer_received_only_reformat. Qed.

Fact state_mnt_sound_pre_pre q (Hq_ : forall n t, q <> Intern n t) 
  w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') l /\ node_state_invariants_pre (w @ n) (w' @ n)
    (* this is not persistence! so need to prove here *)
    /\ (w @ n).(submitted_value) = (w' @ n).(submitted_value).
Proof with (try (now exists (MNTnil _))).
  inversion_step' Hstep; clear Hstep; intros... 
  2: exfalso; eapply Hq_; reflexivity.
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ]...
  destruct (procMsg _ _ _) as [ (st', ms) | ] eqn:E in Ef; simplify_eq...
  destruct (w @ dst) as [ dst' conf ov from lsigs sigs rlcerts rcerts buffer ].
  destruct msg as [ v ls s | (v, cs) | (v, nsigs) ]; simpl in E; simplify_eq. (* pair inj *)
  - destruct ov as [ vthis | ].
    + destruct (andb _ _) eqn:EE in E; try discriminate. 
      unfold is_left in EE. rewrite ! andb_true_iff, sumbool_is_left in EE. destruct EE as ((-> & Everi) & Elveri).
      destruct conf.
      * simplify_eq. unshelve eexists. 1: analyze_step Mconf ltac:(idtac); try apply MNTnil; try reflexivity. 
        simpl. destruct (lightcert_conflict_check _) in |- *; simpl.
        all: local_solver.
      * destruct (in_dec _ _ _) as [ | Hnotin ] in E; try discriminate. simplify_eq.
        destruct (N - t0 <=? S (length from)) eqn:Eth; 
          [ apply Nat.leb_le in Eth | apply Nat.leb_nle in Eth ].
        all: unshelve eexists; [ analyze_step Mfrom_in ltac:(try eassumption); auto | ]; try apply MNTnil.
        1: analyze_step Mconf ltac:(idtac); auto. 1: apply MNTnil.
        all: simpl. 1: destruct (lightcert_conflict_check _) in |- *; simpl.
        all: local_solver.
    + simplify_eq. simpl. unshelve eexists. 1: analyze_step Mfrom_buffer ltac:(idtac); try apply MNTnil; try reflexivity.
      (* since here is for buffer, need to make sure that others = nil, so we need Hothers *)
      (* simpl. simpl in Hothers. subst others. simpl in Hin. local_solver. *)
      simpl. local_solver.
  - destruct (combined_verify _ _) eqn:EE in E; try discriminate.
    simplify_eq. unshelve eexists. 1: analyze_step Mlcert ltac:(idtac); try apply MNTnil; try reflexivity.
    1: apply src. 1: auto. (* need to manually instantiate src here *)
    simpl. unfold zip_from_sigs. simpl. rewrite app_nil_r.
    destruct ov in |- *; [ destruct (andb _ _) eqn:EE0 in |- *; 
      [ rewrite andb_true_iff in EE0 | rewrite andb_false_iff in EE0 ]; destruct EE0; try is_true_rewrite | ]; simpl.
    all: local_solver.
    (* ... *)
    + (* TODO automation is so weak???? *) now setoid_rewrite H.
    + auto with datatypes.
  - destruct (andb _ _) eqn:EE in E; try discriminate.
    unfold is_left in EE. rewrite ! andb_true_iff, ! sumbool_is_left, Nat.leb_le in EE. destruct_and? EE.
    simplify_eq. unshelve eexists. 1: analyze_step Mcert ltac:(idtac); try apply MNTnil; try reflexivity.
    1: apply src. all: auto. (* need to manually instantiate src here *)
    simpl. local_solver.
Qed.
(*
Fact state_mnt_sound_pre q (Hq_ : forall n t, q <> Intern n t) 
  w w' (Hstep : system_step q w w') :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') nil l /\ node_state_invariants_pre (w @ n) (w' @ n).
    (* /\ (id (w @ n) = n (* ! *) -> is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n) -> 
      inv_buffer_received (sentMsgs w') (w' @ n)). *)
Proof with (try (now exists (MNTnil _))).
  unfold inv_buffer_received.
  inversion_step' Hstep; clear Hstep; intros... 
  2: exfalso; eapply Hq_; reflexivity.
  pose proof (@state_mnt_sound_pre_pre (mkP src dst msg used) Hnonbyz stf msf
    w _ Ef (consume (mkP src dst msg used) (sentMsgs w)) nil eq_refl) as H.
  simpl in H. apply H. now destruct (submitted_value _) in |- *. rewrite In_consume. auto.
Qed.

Definition buffer_augment n buf :=
  map (fun nmsg => mkP (fst nmsg) n (snd nmsg) true) buf.
*)

(* HMM one inconvenience of having reachable here is that some lemmas become weaker, 
    as they depend on the decomposition here so they have to assume reachable (i.e., persistent_invariants),
    which is though not required to prove them directly *)
Fact state_mnt_sound q w w' (Hstep : system_step q w w') (Hw : reachable w) :
  forall n, exists l : state_mnt_type_list (w @ n) (w' @ n),
    psent_effect_star n (sentMsgs w') l /\ node_state_invariants_pre (w @ n) (w' @ n).
    (* /\ (id (w @ n) = n (* ! *) -> is_byz n = false -> inv_buffer_received (sentMsgs w) (w @ n) -> 
      inv_buffer_received (sentMsgs w') (w' @ n)). *)
(* Proof with (try solve [ exists (MNTnil _); simpl; split_and?; local_solver ]). *)
Proof with (try (now exists (MNTnil _))).
  destruct q as [ | | n t | ]. 
  1,2,4: intros n; eapply state_mnt_sound_pre_pre with (n:=n) in Hstep; try eassumption; auto;
    destruct Hstep as (? & ? & ? & ?); eauto.
  intros n0.
  inversion_step' Hstep; clear Hstep; intros; try discriminate.
  revert Hq. intros [= <-]. destruct t1.
  unfold upd.
  destruct (Address_eqdec _ _) as [ <- | Hneq ]...
  pose proof (id_coh_always_holds Hw) as Hcoh.
  pose proof (inv_buffer_received_always_holds Hw Hnonbyz) as Hrcv. hnf in Hrcv. 
  destruct_localState w n as_ [ ? conf ov from lsigs sigs rlcerts rcerts buffer ] eqn_ Est. simpl_state.
  simpl in E.
  destruct ov. 1: simplify_eq...
  destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in E. simplify_eq.
  change (set _ _ (set _ _ _)) with (Node n conf (Some (value_bft n)) from lsigs sigs rlcerts rcerts nil) in Efr.
  remember (Node _ _ _ _ _ _ _ _ _) as stt eqn:Es in Efr.
  (* time to do induction *)
  match goal with |- exists (_ : _), (psent_effect_star _ ?pp _) /\ _ =>
    assert (exists l : state_mnt_type_list stt st', psent_effect_star n pp l /\ node_state_invariants_pre stt st') as Hgoal end.
  all: subst stt.
  { clear Est. revert st' ps_ Efr. induction buffer as [ | (src, msg) buffer IH ]; intros; simpl in Efr.
    - simplify_eq...
    - simpl.
      destruct (procMsgWithCheck _ _ _) as (sta, psa) eqn:E0 in Efr.
      destruct (fold_right _ _ _) as (stb, psb) eqn:E1 in Efr. rewrite E1 in E0. simpl in E0, Efr. 
      revert Efr. intros [= <- <-].
      simpl in Hrcv. specialize (IH (fun a H => Hrcv a (or_intror H))).
      saturate_assumptions! in_ IH. destruct IH as (l & Ha & HH).
      (* use the previous lemma *)
      specialize (Hrcv _ (or_introl eq_refl)). simpl in Hrcv.
      epose proof (DeliverStep (Deliver (mkP src n msg true)) (mkW (upd n stb (localState w)) (sentMsgs w))
        _ _ eq_refl Hrcv Hnonbyz ?[Goalq]) as H.
      [Goalq]: simpl; rewrite upd_refl, E0; reflexivity.
      eapply state_mnt_sound_pre_pre with (n:=n) in H; auto. 
      simpl_world. rewrite !upd_refl in H. destruct H as (l0 & Ha0 & HH0 & _).
      exists (state_mnt_type_list_app l l0). 
      rewrite psent_effect_star_app. split. 1: split; [ eapply psent_effect_star_incl; try apply Ha | eapply psent_effect_star_incl; try apply Ha0 ].
      1-2: hnf; intros ?; autorewrite with psent; rewrite ?In_consume; simpl; try tauto.
      1: naive_solver. (* interesting case; depend on Hrcv *)
      destruct HH, HH0. hnf in *. state_invariants_pre_solver. }
  destruct Hgoal as (l & Ha & HH).
  unshelve eexists. 1: analyze_step Msubmit ltac:(idtac); try apply MNTnil; try reflexivity. 1: apply l.
  simpl; local_solver.
  (* TODO still need some cleaning! *)
  destruct HH. hnf in *. constructor; auto.
Qed.

Record node_persistent_invariants st st' : Prop := {
  _ : submitted_value_persistent st st';
  _ : conf_persistent st st';
  _ : id_persistent st st';
  _ : msg_buffer_nil_persistent st st';
  _ : conf_from_set_persistent st st';
  _ : conf_collected_lightsigs_persistent st st';
  _ : conf_collected_sigs_persistent st st';
  _ : received_lightcerts_persistent st st';
  _ : received_certs_persistent st st';
  _ : from_set_persistent st st';
  _ : msg_buffer_notnil_persistent st st';
}.

Record node_state_invariants_pre' st st' : Prop := {
  _ : lift_point_to_edge inv_from_nodup st st';
  _ : lift_point_to_edge inv_rlcerts st st';
  _ : lift_point_to_edge inv_rcerts_mixin st st';
  _ : lift_point_to_edge inv_submit_mixin st st';
  _ : lift_point_to_edge buffer_nil_after_submit st st';
  _ : lift_point_to_edge buffer_contains_submitmsg st st';
  _ : lift_point_to_edge confirmed_then_submitted st st';
}.

(* FIXME: the meta things about persistence can be reused? *)
#[export] Instance Transitive_node_persistent_invariants : Transitive node_persistent_invariants.
Proof.
  hnf. intros ??? H H0. destruct H, H0. constructor.
  all: hnf; intuition.
  1: congruence.
  all: hnf in *.
  all: try solve [ is_true_rewrite; saturate_assumptions; congruence; auto ].
  - match goal with H : isSome ?a = true |- _ => destruct a eqn:EE; try discriminate end. 
    saturate_assumptions!. isSome_rewrite. auto.
  - destruct (submitted_value y); isSome_rewrite; try intuition.
    saturate_assumptions!. congruence.
Qed.

Fact persistent_invariants_pre_pre st (d : state_mnt_type st) :
  node_persistent_invariants st (state_mnt d) /\ node_state_invariants_pre' st (state_mnt d).
Proof.
  split_and?; constructor.
  all: match goal with |- lift_point_to_edge ?def _ _ => unfold def | _ => idtac end; hnf.
  all: intros; destruct d; subst; simpl in *; eauto;
    try solve [ hypothesis | congruence | constructor; auto | isSome_rewrite; auto; discriminate | naive_solver ].
  all: try match_option_rewrite; unfold zip_from_lsigs, zip_from_sigs; simpl.
  - rewrite H. simpl. split_and?; hnf; auto with core.
  - destruct_and? H. split_and?; hnf; auto with core.
Qed.

(* FIXME: this is reusable? *)
(* FIXME: this name is misleading ... since it contains two things *)
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

(* TODO is this wrapper actually useful? *)
Definition lift_state_pair_inv (P : State -> State -> Prop) : World -> World -> Prop :=
  fun w w' => forall n, P (w @ n) (w' @ n).

Fact persistent_invariants q w w' (Hstep : system_step q w w') (Hw : reachable w) :
  lift_state_pair_inv node_persistent_invariants w w'.
Proof.
  intros n.
  eapply state_mnt_sound with (n:=n) in Hstep; auto.
  destruct Hstep as (l & _).
  eapply persistent_invariants_pre; eauto.
Qed.

Fact persistent_invariants_trace [w l] (Htrace : system_trace w l) (Hw : reachable w) :
  lift_state_pair_inv node_persistent_invariants w (final_world w l).
Proof.
  revert w Hw Htrace. induction l as [ | (q, w') l' IH ]; simpl; intros.
  - rewrite final_world_nil. hnf. intros ?. constructor; hnf; auto.
  - pose proof (ReachableStep (proj1 Htrace) Hw) as Hw'.
    rewrite final_world_cons. destruct Htrace as (Hstep%persistent_invariants & Htrace); auto.
    saturate_assumptions! in_ IH. hnf in IH, Hstep |- *. intros n. specialize (Hstep n). specialize (IH n).
    etransitivity; eauto.
Qed. 

Record node_state_invariants st : Prop := {
  _ : inv_conf_correct st;

  _ : confirmed_then_submitted st;
  _ : inv_from_nodup st;
  _ : inv_rlcerts st;
  _ : inv_rcerts_mixin st;
  _ : inv_submit_mixin st;
  _ : buffer_nil_after_submit st;
  _ : buffer_contains_submitmsg st;
}.

Fact state_invariants : always_holds (lift_state_inv node_state_invariants).
Proof.
  intros w Hw. induction Hw as [ | q w w' Hstep Hw H ]; auto.
  - (* TODO streamline the proof here? *)
    unfold initWorld, initState, Init.
    hnf. intros n. constructor; simpl; hnf; simpl; try solve [ discriminate | contradiction | constructor; auto | lia | auto ].
    pose proof t0_lt_N. lia.
  - hnf. intros n. specialize (H n).
    pose proof (state_mnt_sound Hstep Hw n) as (l & _ & Hinv_pre).
    pose proof (persistent_invariants_pre l) as (_ & HH). 
    destruct H, Hinv_pre, HH. unfold lift_point_to_edge in *. constructor; auto.
Qed.

End State_Monotone_Proofs.

Section Forward.

Record node_psent_l2h_invariants psent st : Prop := {
  _ : inv_submitted_broadcast psent st;
  _ : inv_conf_lightconfmsg psent st;
  _ : inv_conf_confmsg psent st;
  _ : inv_nsigs_correct psent st; (* requires inv_buffer_received *)
  _ : inv_rlcerts_correct psent st;
  _ : inv_rcerts_correct psent st;
  _ : inv_buffer_received psent st;
}.

(*
Fact l2h_invariants_pre : is_invariant_reachable_step
  (fun w => forall n, is_byz n = false -> 
    inv_buffer_received (sentMsgs w) (w @ n) /\ inv_nsigs_correct (sentMsgs w) (w @ n)).
Proof.
  hnf; intros qq ?? Hw H Hstep. pose proof (ReachableStep Hstep Hw) as Hw'.
  unfold lift_node_inv in *.
  intros n Hnonbyz. saturate_assumptions!. destruct H as (H & H0).
  (* TODO this is cumbersome! *)
  pose proof (id_coh_is_invariant Hw n) as Hcoh.
  pose proof (id_coh_is_invariant Hw' n) as Hcoh'.
  pick inv_submit_mixin as_ Hmx' by_ (pose proof (state_invariants Hw n) as []). rewrite Hcoh in Hmx'.
  assert ((w @ n).(submitted_value) = None -> (w @ n).(from_set) = nil) as Hmx by (now destruct ((w @ n).(submitted_value))). clear Hmx'.
  pick buffer_nil_after_submit as_ Hbn by_ (pose proof (state_invariants Hw n) as []).
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply state_mnt_sound with (n:=n) in Hstep.
  destruct Hstep as (l & Hpsent & _).
  (* generalize a little bit *)
  (* TODO put this before? *)
  assert (exists others, incl others (buffer_augment n (msg_buffer (w @ n))) /\ 
    psent_effect_star n (sentMsgs w') others l) as Hpsent'.
  { eexists. split; [ | apply Hpsent ]. destruct qq; hnf; simpl; tauto. }
  clear Hpsent. destruct Hpsent' as (others & Hincl & Hpsent).
  hnf in H, H0.
  split_and?.
  all: hnf; rewrite Hcoh in *; rewrite Hcoh' in *.
  1: intros (n0, msg0) Hin; specialize (H (n0, msg0)); clear H0 Hbn Hmx.
  (* TODO why if we do not specialize here, things will not go through? *)
  (* TODO revert others? *)
  2: intros v Hv n0 lsig sig; pose proof (fun vv Hvv => H0 vv Hvv n0 lsig sig) as H'; specialize (H (n0, SubmitMsg v lsig sig));
    clear H0; rename H' into H0; revert others Hincl Hpsent.
  (* all: remember (w @ n) as st eqn:Est; remember (w' @ n) as st' eqn:Est'. *)
  all: (* revert Est' Est; *) induction l as [ st | st d st' l IH ]; intros; saturate_assumptions!.
  all: (* all MNTnil (under-specified) cases *)
    try solve [ eapply system_step_psent_norevert_full; eauto ].
  all: simpl in Hpsent; destruct Hpsent as (Hpsent & HH).
  all: destruct d; simpl in Hpsent, IH, (type of l); saturate_assumptions; simplify_eq.
  all: unfold zip_from_lsigs, zip_from_lsigs_sigs, zip_from_sigs in *; simpl in *.
  all: try solve [ tauto | apply IH; auto with datatypes | apply IH with (others:=others); auto with datatypes ].
  (* try unify submitted value *)
  all: pose proof (persistent_invariants_pre l) as ([] & _); 
    pick submitted_value_persistent as_ Hvv; pick conf_persistent as_ Hcc; simpl in Hvv, Hcc;
    try (saturate_assumptions! in_ Hvv); try (saturate_assumptions! in_ Hcc).
  all: try (specialize (Hvv _ eq_refl); rewrite Hvv in * ); simplify_eq.
  - (* use persistence here *)
    pick msg_buffer_nil_persistent as_ Hb by_ (pose proof (persistent_invariants_pre l) as ([] & _)). 
    simpl in Hb. saturate_assumptions. rewrite Hb in Hin. contradiction.
  - destruct (ListFacts.prod_eq_dec Address_eqdec Message_eqdec (n0, msg0) (src0, SubmitMsg v lsig sig)); simplify_eq; auto.
    apply IH; auto with datatypes. intros [ | ]; auto; congruence.
  - apply IH with (others:=nil); try contradiction; auto with datatypes.
    + (* by contradiction *)
      rewrite Hmx. simpl. intros. contradiction.
    + admit.
  - match goal with Hpsent : In (mkP ?srca _ (SubmitMsg _ ?lsiga ?siga) _) _ \/ In _ _ 
      |- In (mkP ?srcb _ (SubmitMsg _ ?lsigb ?sigb) _) _ => 
      destruct (ListFacts.prod_eq_dec (ListFacts.prod_eq_dec Address_eqdec LightSignature_eqdec) Signature_eqdec 
        (srca, lsiga, siga) (srcb, lsigb, sigb)); try simplify_eq end.
    + (* prove that others = nil *)
      destruct Hpsent as [ Hpsent | Hpsent ]; auto.
      isSome_rewrite. saturate_assumptions. rewrite Hbn in Hincl. simpl in Hincl. now apply Hincl in Hpsent.
    + eapply IH; eauto; try congruence. intros ? HH1. intros. rewrite HH1 in *. simplify_eq. 
      eapply H0; try reflexivity. tauto.
  - destruct (ListFacts.prod_eq_dec Address_eqdec Message_eqdec (n0, SubmitMsg v lsig sig) (src0, SubmitMsg v0 lsig0 sig0)); simplify_eq; auto.
    eapply IH with (others:=others); eauto with datatypes. 2: now isSome_rewrite. 
    intros [ | ]; auto; congruence.
Admitted.
*)
Fact l2h_invariants_pre : is_invariant_reachable_step_under
  (fun w => id_coh w /\ lift_state_inv node_state_invariants w /\ lift_node_inv inv_buffer_received w)
  (lift_node_inv node_psent_l2h_invariants).
Proof.
  hnf; intros qq ?? Hw _ (Hcoh & Hst & Hrcv) (Hcoh' & _ & _) H Hstep.
  intros n Hnonbyz. (* saturate later *)
  pose proof (Hcoh n) as Hcoh_. pose proof (Hcoh' n) as Hcoh_'. (* required for bridging n and id later *)
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply state_mnt_sound with (n:=n) in Hstep; auto.
  destruct Hstep as (l & Hpsent & _).
  constructor; auto.
  7: eapply inv_buffer_received_only; eauto. 7: intros n0; split_and?; auto. 7: destruct (Hst n0); hypothesis. (* requires Hw here *)
  all: unfold lift_node_inv in *; saturate_assumptions! in_ Hrcv; saturate_assumptions! in_ H.
  all: match goal with |- ?def _ _ => pick def as_ H' by_ (destruct H); clear H; rename H' into H end.
  all: hnf; rewrite Hcoh_ in *; rewrite Hcoh_' in *.
  (* TODO why if we do not specialize here, things will not go through? *)
  1-4: intros v; specialize (H v).
  2,3: pick confirmed_then_submitted as_ Hcs by_ (pose proof (Hst n) as []). (* eliminate the Msubmit case *)
  4: intros Hv n0 lsig sig; revert Hv; pose proof (fun Hy => H Hy n0 lsig sig) as H'; clear H; rename H' into H.
  4: pick inv_submit_mixin as_ Hmx by_ (pose proof (Hst n) as []); apply inv_submit_mixin_break in Hmx; unfold inv_submit_none in Hmx.
  4: hnf in Hrcv; rewrite Hcoh in Hrcv; specialize (Hrcv (n0, SubmitMsg v lsig sig)).
  5: intros lc; specialize (H lc).
  6: intros c; specialize (H c).
  all: match goal with |- context[zip_from_lsigs_sigs] => idtac | _ => clear Hrcv end. (* Hrcv will only be used in one goal *)
  all: intros.
  all: induction l as [ st | st d st' l IH ]; saturate_assumptions!.
  all: (* all MNTnil (under-specified) cases *)
    try solve 
    [ eapply system_step_psent_norevert_full; eauto
    | destruct H as (tmp & H); exists tmp; eapply system_step_psent_norevert_full; eauto
    | eapply system_step_psent_persistent_weak_full; eauto ].
  all: simpl in Hpsent; destruct Hpsent as (Hpsent & HH).
  all: destruct d; simpl in Hpsent, IH, (type of l); saturate_assumptions; simplify_eq.
  all: match type of Hpsent with _ /\ _ => destruct Hpsent as (Hpsent & Hbb) | _ => idtac end. (* for two kinds of special psent_effects *)
  all: try solve [ tauto | apply IH; auto with datatypes ].
  (* try unify submitted value *)
  all: pose proof (persistent_invariants_pre l) as ([] & _); 
    pick submitted_value_persistent as_ Hvv; pick conf_persistent as_ Hcc; simpl in Hvv, Hcc;
    try (saturate_assumptions! in_ Hvv); try (saturate_assumptions! in_ Hcc).
  all: try (specialize (Hvv _ eq_refl); rewrite Hvv in * ); simplify_eq.
  all: try solve
    [ match goal with HH : context[?a = ?b \/ In _ _] |- _ => (* new Ins *)
      first [ destruct (LightCertificate_eqdec a b) as [ <- | ]
            | destruct (Certificate_eqdec a b) as [ <- | ] ]; try tauto; try eauto end
    | exists false; apply Hpsent, In_broadcast; eauto (* bcast *)
    | try isSome_rewrite; try is_true_rewrite; apply IH; auto; eqsolve (* when just use IH *) ].
  all: unfold zip_from_lsigs, zip_from_lsigs_sigs, zip_from_sigs in *.
  - (* use persistence *)
    pick conf_collected_lightsigs_persistent as_ Hll.
    simpl in Hll. saturate_assumptions. rewrite <- Hll in *. 
    exists false; apply Hpsent, In_broadcast; eauto.
  (* FIXME: read the following two cases *)
  - isSome_rewrite. match_option_rewrite.
    destruct (lightcert_conflict_check _) in Hbb, IH; saturate_assumptions.
    + (* use persistence *)
      pick conf_collected_sigs_persistent as_ Hll1. pick conf_from_set_persistent as_ Hll2.
      simpl in Hll1, Hll2. saturate_assumptions. unfold zip_from_sigs. rewrite <- Hll1, <- Hll2. 
      exists false; apply Hbb, In_broadcast; eauto.
    + apply IH; auto; eqsolve.
  - destruct (conf st) eqn:?; saturate_assumptions. 2: apply IH; auto; eqsolve.
    destruct (lightcert_conflict_check _) in Hbb, IH; saturate_assumptions. 2: apply IH; auto; eqsolve.
    destruct (submitted_value st) as [ v' | ] eqn:?; try discriminate; saturate_assumptions!.
    rewrite Hvv in *. simplify_eq.
    (* TODO repeating *)
    (* use persistence *)
    pick conf_collected_sigs_persistent as_ Hll1. pick conf_from_set_persistent as_ Hll2.
    simpl in Hll1, Hll2. saturate_assumptions. unfold zip_from_sigs. rewrite <- Hll1, <- Hll2. 
    exists false; apply Hbb, In_broadcast; eauto.
  - (* use IH and show that from = nil *)
    unfold inv_buffer_received in IH. simpl in IH. apply IH; auto; try contradiction.
    rewrite Hmx. simpl. contradiction.
  - (* compare & check if can use IH *)
    destruct (ListFacts.prod_eq_dec Address_eqdec Message_eqdec (n0, SubmitMsg v lsig sig) (src0, SubmitMsg v lsig0 sig0)); simplify_eq; auto.
    eapply IH; eauto with datatypes. 2: congruence.
    intros _ [ | ]; auto; congruence.
  - (* compare & check if can use IH *)
    destruct (ListFacts.prod_eq_dec Address_eqdec Message_eqdec (n0, SubmitMsg v lsig sig) (src0, SubmitMsg v0 lsig0 sig0)); simplify_eq; auto.
    apply IH; auto with datatypes. intros [ | ]; auto; congruence.
Qed.

Fact l2h_invariants : always_holds (lift_node_inv node_psent_l2h_invariants).
Proof.
  eapply is_invariant_reachable_step_under_closed.
  1: apply l2h_invariants_pre.
  2: rewrite ! always_holds_and; auto using id_coh_always_holds, state_invariants, inv_buffer_received_always_holds.
  hnf. intros. constructor; hnf; try discriminate; try contradiction.
Qed.

End Forward.

Section Backward.

(* the state-major view is useful, but we also need a packetsoup-major view *)

Inductive psent_mnt_type_base (psent : PacketSoup) : Type :=
  | Pid : psent_mnt_type_base psent
  | Puse : forall p, In p psent -> psent_mnt_type_base psent
.

(* ... this design of mixing user packets and Byzantine packets is not good *)
(*
Inductive packets_shape_user : Type := PSUbcast (n : Address) (m : Message).

Inductive packets_shape : Type := PSHuser (psu : packets_shape_user) | PSHbyz (p : Packet).
*)

(* intended to be in a module type, or something, provided by user *)
Inductive packets_shape : Type := PSbcast (n : Address) (m : Message).

Definition packets_shape_consistent (ps : packets_shape) (pkts : list Packet) : Prop :=
  match ps with
  | PSbcast n m => pkts = broadcast n m
  end.

(* a list *)
(* the base psent will not change, which represents the psent before update *)
(* ... this design is not very good, since the cons part can be just a normal list *)
(*
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
*)

(* want to write it in another way so that the base part can be exposed, 
    which will enable some proofs about psent_mnt_type concatenation *)
(* write the atomic part as a dependent record? *)
(* FIXME: this is a strong over-approximation; actually, the sender (which is unique
    in one transition) should be the argument. but now we do not need that precise
    description so skip *)
Record psent_mnt_type : Type := mkPMT {
  pkts : list Packet;
  ps : packets_shape;
  _ : Forall (fun p => p.(consumed) = false) pkts;
  _ : packets_shape_consistent ps pkts;
}.

Global Arguments mkPMT : clear implicits.

Definition psent_mnt_base psent (s : psent_mnt_type_base psent) : PacketSoup :=
  match s with
  | Pid _ => psent
  | Puse _ p _ => consume p psent
  end.

(* intuitively, psent' gets smaller when l gets smaller *)
Fixpoint psent_mnt psent (b : psent_mnt_type_base psent) (l : list psent_mnt_type) psent' : Prop :=
  match l with
  | nil => 
    (* psent' = psent_mnt_base b *)
    Ineq psent' (psent_mnt_base b)
  | a :: l' => exists psent_, psent_mnt b l' psent_ /\ Ineq psent' (sendout a.(pkts) psent_)
  end.

Fact psent_mnt_idbase_Ineq [psent psent1 psent2] (l : list psent_mnt_type) (H : Ineq psent1 psent2) :
  psent_mnt (Pid psent1) l psent <-> psent_mnt (Pid psent2) l psent.
Proof.
  revert psent. induction l; simpl; intros.
  - now rewrite H.
  - setoid_rewrite IHl. auto.
Qed.

Fact psent_mnt_result_Ineq [psent psent1 psent2] (b : psent_mnt_type_base psent) (l : list psent_mnt_type) (H : Ineq psent1 psent2) :
  psent_mnt b l psent1 <-> psent_mnt b l psent2.
Proof.
  destruct l as [ | a l' ]; simpl.
  - now rewrite H.
  - setoid_rewrite H. auto.
Qed.

Fact psent_mnt_base_change [psent psent'] (b : psent_mnt_type_base psent) (l : list psent_mnt_type) :
  psent_mnt b l psent' <-> psent_mnt (Pid (psent_mnt_base b)) l psent'.
Proof.
  revert psent'. induction l as [ | a l IH ]; simpl; intros.
  - reflexivity.
  - setoid_rewrite IH. reflexivity.
Qed.

Fact psent_mnt_idbase_pop [psent psent'] l a :
  psent_mnt (Pid (sendout a.(pkts) psent)) l psent' <-> psent_mnt (Pid psent) (l ++ a :: nil) psent'.
Proof.
  revert psent'. induction l as [ | a' l IH ]; simpl; intros.
  - split. 
    + intros HH. exists psent. split; try reflexivity; auto.
    + intros (psent_ & Ha & Hb). hnf in Ha, Hb |- *. intros x. specialize (Ha x). specialize (Hb x).
      autorewrite with psent in Ha, Hb |- *. tauto.
  - setoid_rewrite IH. auto.
Qed.

(* here, the list to be appended must start with Pid *)
Fact psent_mnt_append [psent psent' psent''] (b : psent_mnt_type_base psent) (l l' : list psent_mnt_type)
  (H : psent_mnt b l psent') (H' : psent_mnt (Pid psent') l' psent'') : psent_mnt b (l' ++ l) psent''.
Proof.
  revert l psent b psent' psent'' H H'. induction l' as [ | a l' IH ]; simpl; intros.
  - erewrite psent_mnt_result_Ineq by eassumption. assumption.
  - destruct H' as (psent_ & H1 & H2). saturate_assumptions!. eauto.
Qed.

(* TODO the following functions seems to be repeating the bodies of the h2l invariants above. 
  maybe put these above and reuse? *)
Definition state_effect_bcast (n : Address) (m : Message) (stmap : StateMap) : Prop :=
  let: st := (stmap n) in
  match m with
  | SubmitMsg v lsig sig => 
    verify v sig n /\ light_verify v lsig n /\
    st.(submitted_value) = Some v
  | LightConfirmMsg (v, cs) =>
    st.(conf) /\ st.(submitted_value) = Some v /\
    cs = lightsig_combine st.(collected_lightsigs)
  | ConfirmMsg (v, nsigs) => 
    st.(conf) /\ lightcert_conflict_check st.(received_lightcerts) (* this is new *)
    /\ st.(submitted_value) = Some v /\ nsigs = zip_from_sigs st
  end.

Definition state_effect_recv (src : Address) (m : Message) (st : State) : Prop :=
  (* currently only uses single point, so reduces the argument *)
  (* let: st := (stmap n) in *)
  match m with
  | SubmitMsg v lsig sig => 
    match st.(submitted_value) with
    | None => In (src, m) st.(msg_buffer)
    | Some ov => 
      (* the length condition may be more natural, but it would be hard to reason about 
        without invariant 1; so replace it with the condition on conf *)
      (* length st.(from_set) < N - t0 -> *)
      st.(conf) = false ->
      v = ov -> verify v sig src -> light_verify v lsig src ->
        In src st.(from_set) (* ths should be enough *)
    end
  | LightConfirmMsg (v, cs) =>
    combined_verify v cs -> In (v, cs) st.(received_lightcerts)
  | ConfirmMsg (v, nsigs) => 
    certificate_valid v nsigs -> NoDup nsigs -> (N - t0 <= (length nsigs)) ->
    In (v, nsigs) st.(received_certs)
  end.

(* here, stmap refers to the updated state map *)
(* it seems not quite useful to constrain on the original state map *)
(* writing this as an inductive prop will make inversion difficult;
    for example, inverting "state_effect stmap (Pcons pkts H psent l)" will not give "state_effect stmap l", 
    due to some weird reason ...
  use another way to constrain the shape of pkts, instead *)

(* TODO if this works, consider how to distribute the constraints here and in "psent_mnt_type"
    of course, constraints involving stmap must be here *)
Definition state_effect_base [psent] (stmap : StateMap) (b : psent_mnt_type_base psent) : Prop :=
  match b with
  | Pid _ => True (* under-specified *)
  | Puse _ (mkP src n m used) _ => is_byz n = false /\ state_effect_recv src m (stmap n)
  end.

Global Arguments state_effect_base [_] _ !_.

Fixpoint state_effect_send (stmap : StateMap) (l : list psent_mnt_type) : Prop :=
  match l with
  | nil => True
  | a :: l' =>
    state_effect_send stmap l' /\ (* putting this here can be convenient *)
    match a.(ps) with
    | PSbcast n m => is_byz n = false /\ state_effect_bcast n m stmap
    end
  end.

Fact state_effect_send_app stmap l l' : 
  state_effect_send stmap (l ++ l') <-> state_effect_send stmap l /\ state_effect_send stmap l'.
Proof. revert l'. induction l; simpl; intros; try tauto. rewrite IHl. tauto. Qed.

Fact state_effect_bcast_stmap_peq stmap stmap' n msg (Hpeq : forall n, stmap n = stmap' n) : 
  state_effect_bcast n msg stmap <-> state_effect_bcast n msg stmap'.
Proof. destruct msg; simpl. all: rewrite Hpeq; auto. Qed.

Fact state_effect_send_stmap_peq stmap stmap' l (Hpeq : forall n, stmap n = stmap' n) : 
  state_effect_send stmap l <-> state_effect_send stmap' l.
Proof. induction l; simpl; intros; try tauto. rewrite IHl. destruct (ps _). rewrite state_effect_bcast_stmap_peq by eassumption. tauto. Qed.

Inductive psent_sender_kind (psent : list Packet) : Type := 
  | PSKnonbyz (b : psent_mnt_type_base psent) (l : list psent_mnt_type)
  | PSKbyz (p : Packet).

Definition state_effect (stmap : StateMap) [psent] (psk : psent_sender_kind psent) : Prop :=
  match psk with
  | PSKnonbyz b l => state_effect_base stmap b /\ state_effect_send stmap l
  | PSKbyz _ p => is_byz p.(src) /\ p.(consumed) = false /\ byz_constraints p.(msg) (mkW stmap psent) (* FIXME: is byz_constraints only about psent? *)
  end.

Ltac state_effect_solve :=
  simpl; eauto; repeat (first [ rewrite upd_refl; simpl ]); split_and?; 
  try isSome_rewrite; try tauto; try eqsolve; auto.

(* here, do not consider base *)
(* FIXME: unify with the one in RB? *)
Ltac psent_analyze' psent' :=
  match psent' with
  | sendout (?pkts1 ++ ?pkts2) ?psent_ =>
    let ss := psent_analyze' constr:(sendout pkts1 psent_) in
    match pkts2 with
    | broadcast ?n ?m => uconstr:((mkPMT pkts2 (PSbcast n m) (broadcast_all_fresh n m) eq_refl) :: ss)
    end
  | sendout ?pkts ?psent_ => 
    let ss := psent_analyze' constr:(psent_) in
    match pkts with
    | broadcast ?n ?m => uconstr:((mkPMT pkts (PSbcast n m) (broadcast_all_fresh n m) eq_refl) :: ss)
    end
  (*
  | sendout1 ?p ?psent_ => 
    (* early terminate *)
    uconstr:((mkPMT (p :: nil) (PSHbyz p) ltac:(now constructor) eq_refl) :: nil)
  *)
  | _ => uconstr:(@nil psent_mnt_type)
  end.

Ltac psent_mnt_solve :=
  match goal with
  (*
  | |- exists (_ : _), _ = _ /\ _ => 
    eexists; split; (* TODO appending anything after the semicolon here will result in non-termination? *)
    *)
  | |- exists (_ : _), (* _ = ?psent *) (Ineq _ ?psent) /\ _ => exists psent; split; 
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
  try rewrite sendout0;
  match goal with
  | |- exists (_ : ?t), psent_mnt _ _ ?psent' /\ _ =>
    let l := psent_analyze' psent' in
    unshelve eexists l;
    match goal with
    | |- psent_mnt _ _ ?psent' /\ _ => 
      split; [ simpl; auto; try reflexivity; psent_mnt_solve | state_effect_solve ]
    (* | _ => try apply broadcast_all_fresh *)
    | _ => idtac
    end
  end.

Definition lift_pkt_inv' (P : Packet -> StateMap -> Prop) : PacketSoup -> StateMap -> Prop :=
  fun psent stmap => forall p, In p psent -> P p stmap.

Definition lift_pkt_inv (P : Packet -> StateMap -> Prop) : World -> Prop :=
  Eval unfold lift_pkt_inv' in fun w => lift_pkt_inv' P (sentMsgs w) (localState w).

Fact psent_mnt_sound_pre_pre p (Hnonbyz : is_byz (dst p) = false) stf msf w w'
  (Hcoh : id_coh w) (* still needed *)
  (Ef : procMsgWithCheck (w @ dst p) (src p) (msg p) = (stf, msf))
  psent (E0 : w' = mkW (upd (dst p) stf (localState w)) (sendout msf psent)) (Hpin : In p psent) :
  exists l : list psent_mnt_type,
    psent_mnt (Pid psent) l (sentMsgs w') /\ state_effect (localState w') (PSKnonbyz (Puse psent p Hpin) l).
    (* /\ (lift_pkt_inv' inv_submitmsg_receive psent (localState w) ->
      lift_pkt_inv' inv_submitmsg_receive (sendout msf psent) (localState w')). *)
Proof.
  destruct p as [ src dst msg used ]. simpl_pkt. subst w'. simpl. unfold procMsgWithCheck in Ef. 
  destruct_localState w dst as_ [ ? conf ov from lsigs sigs rlcerts rcerts buffer ] eqn_ Est.
  destruct msg as [ v ls s | (v, cs) | (v, nsigs) ]; simpl in Ef; simplify_eq. (* pair inj *)
  + destruct ov as [ vthis | ].
    (* TODO a tactic for sumbool rewriting *)
    * destruct (andb _ _) eqn:EE in Ef; unfold is_left in EE; 
        [ rewrite !andb_true_iff, sumbool_is_left in EE
        | rewrite !andb_false_iff, sumbool_is_right in EE ]; simplify_eq.
      2: psent_analyze.
      destruct EE as ((-> & Everi) & Elveri).
      destruct conf eqn:?.
      --simplify_eq. simpl. 
        destruct (lightcert_conflict_check _) eqn:? in |- *; simpl.
        all: psent_analyze. 
      --destruct (in_dec _ _ _) as [ Hin | Hnotin ] in Ef; simplify_eq.
        1: psent_analyze. 
        simpl.
        destruct (N - t0 <=? S (length from)) eqn:Eth; simpl;
          [ apply Nat.leb_le in Eth | apply Nat.leb_nle in Eth ].
        1: destruct (lightcert_conflict_check _) eqn:? in |- *; simpl.
        all: psent_analyze.
    * simplify_eq. simpl. psent_analyze.
  + destruct (combined_verify _ _) eqn:EE in Ef; simplify_eq.
    2: psent_analyze.
    simpl. rewrite app_nil_r. 
    destruct ov in |- *; [ destruct (andb _ _) eqn:EE0 in |- *; 
      [ rewrite andb_true_iff in EE0 | rewrite andb_false_iff in EE0 ]; destruct EE0; try is_true_rewrite | ]; simpl.
    all: psent_analyze.
  + destruct (andb _ _) eqn:EE in Ef; unfold is_left in EE; 
      [ rewrite !andb_true_iff, !sumbool_is_left, !Nat.leb_le in EE
      | rewrite !andb_false_iff, !sumbool_is_right, !Nat.leb_nle in EE ]; simplify_eq.
    all: psent_analyze.
Qed.
(*
Fact psent_mnt_sound_pre q w w' (Hstep : system_step q w w') (Hq_ : forall n t, q <> Intern n t) 
  (* having reachable instead would complicate the induction proof *)
  (Hcoh : id_coh w) (* still needed *) :
  exists (b : psent_mnt_type_base (sentMsgs w)) (l : list psent_mnt_type),
    psent_mnt b l (sentMsgs w') /\ state_effect (localState w') b l.
Proof.
  inversion_step' Hstep; clear Hstep; intros.
  3: exfalso; eapply Hq_; reflexivity.
  - exists (Pid _). psent_analyze.
  - exists (Puse _ _ Hpin).
    let pkt := constr:(mkP src dst msg used) in
      eapply psent_mnt_sound_pre_pre with (psent:=consume pkt (sentMsgs w)) in Ef; try reflexivity; auto.
    simpl in Ef. destruct Ef as (l & Ha & Hb).
    exists l. rewrite psent_mnt_base_change. simpl. 
    exists ( 
  - (* TODO the bug happens here ... *)
    psent_analyze. (* ???? *)
    intros ?; autorewrite with psent; simpl; tauto.
Qed.
*)
(* required below? *)

Fact procMsgWithCheck_fresh st src m :
  Forall (fun p => p.(consumed) = false) (snd (procMsgWithCheck st src m)).
Proof with (simpl; rewrite ?Forall_app; auto using broadcast_all_fresh).
  unfold procMsgWithCheck, routine_check.
  destruct st as [ n conf ov from lsigs sigs rlcerts rcerts buffer ], m as [ v lsig sig | (v, cs) | (v, nsigs) ]; simpl.
  - destruct ov...
    destruct (andb _ _)... destruct conf.
    + destruct (andb _ _)...
    + destruct (in_dec _ _ _)...
      destruct (andb _ _). all: destruct (Nat.leb _ _)...
  - destruct (combined_verify _ _)...
    destruct ov... destruct (andb _ _)...
  - destruct (andb _ _)...
Qed.

(* specialized to this invariant only *)
(*
Fact inv_submitmsg_receive_fresh_skip psent psent' pkts st
  (Hf : Forall (fun p => p.(consumed) = false) pkts) (Hpsent : forall p, In p psent' <-> In p psent \/ In p pkts) :
  (forall p, In p psent -> inv_submitmsg_receive_ p st) ->
  (forall p, In p psent' -> inv_submitmsg_receive_ p st).
Proof.
  intros H p Hin%Hpsent. destruct Hin as [ Hin | Hin ]; auto.
  eapply Forall_forall in Hin. 2: apply Hf. simpl in Hin. hnf. rewrite Hin. now destruct (msg p).
Qed.
*)
Fact psent_mnt_sound_pre n t w w' (Hstep : system_step (Intern n t) w w') (Hw : reachable w) :
  (lift_pkt_inv' inv_submitmsg_receive (sentMsgs w) (localState w) ->
    lift_pkt_inv' inv_submitmsg_receive (sentMsgs w') (localState w')) /\
  exists l : list psent_mnt_type,
    psent_mnt (Pid (sentMsgs w)) l (sentMsgs w') /\ state_effect (localState w') (PSKnonbyz (Pid (sentMsgs w)) l).
Proof.
  simpl.
  pose proof (id_coh_always_holds Hw) as Hcoh.
  (* destruct q as [ | | n t | ]. 
  1,2,4: eapply psent_mnt_sound_pre; try eassumption; auto. *)
  inversion_step' Hstep; clear Hstep; intros; try discriminate.
  revert Hq. intros [= <-]. destruct t1.
  pose proof (inv_buffer_received_always_holds Hw Hnonbyz) as Hrcv. hnf in Hrcv. 
  destruct_localState w n as_ [ ? conf ov from lsigs sigs rlcerts rcerts buffer ] eqn_ Est. simpl_state.
  simpl in E.
  (* destruct ov. 1: simplify_eq; psent_analyze. *)
  destruct ov. 1: simplify_eq; split; [ | psent_analyze ].
  1:{ rewrite sendout0. intros Hq. hnf in Hq |- *. intros p Hin. specialize (Hq _ Hin). 
    unfold inv_submitmsg_receive in Hq |- *. now rewrite <- Est, -> upd_intact. }
  destruct (fold_right _ _ _) as (st_, ps_) eqn:Efr in E. simplify_eq.
  change (set _ _ (set _ _ _)) with (Node n conf (Some (value_bft n)) from lsigs sigs rlcerts rcerts nil) in Efr.
  (* time to do induction *)
  assert (st'.(id) = n /\ (* required by psent_mnt_sound_pre_pre *)
    st'.(submitted_value) = Some (value_bft n) /\ (* required at the end *)
    Forall (fun '(src, msg) => state_effect_recv src msg st') buffer /\
    Forall (fun p => p.(consumed) = false) ps_ /\ (* required to do fresh skip *)
    exists l : list psent_mnt_type, 
    psent_mnt (Pid (sentMsgs w)) l (sendout ps_ (sentMsgs w)) /\ state_effect_send (upd n st' (localState w)) l) as Hgoal.
  { clear Est. revert st' ps_ Efr. induction buffer as [ | (src, msg) buffer IH ]; intros; simpl in Efr.
    - simplify_eq. split_and?; auto. psent_analyze.
    - destruct (procMsgWithCheck _ _ _) as (sta, psa) eqn:E0 in Efr.
      destruct (fold_right _ _ _) as (stb, psb) eqn:E1 in Efr. rewrite E1 in E0. simpl in E0, Efr. 
      revert Efr. intros [= <- <-].
      simpl in Hrcv. specialize (IH (fun a H => Hrcv a (or_intror H))).
      saturate_assumptions! in_ IH. destruct IH as (Hcohb & Hvb & Hre & Hfresh & l & Ha & HH).
      (* use the previous lemma to obtain persistence ... TODO this is cumbersome, any better way? *)
      specialize (Hrcv _ (or_introl eq_refl)). simpl in Hrcv.
      epose proof (DeliverStep (Deliver (mkP src n msg true)) (mkW (upd n stb (localState w)) (sentMsgs w))
        _ _ eq_refl Hrcv Hnonbyz ?[Goalq]) as H.
      [Goalq]: simpl; rewrite upd_refl, E0; reflexivity.
      eapply state_mnt_sound_pre_pre with (n:=n) in H; auto. simpl in H. destruct H as (ll & _). rewrite !upd_refl in ll.
      pose proof (persistent_invariants_pre ll) as ([] & _).
      split; try congruence.
      apply and_wlog_r. 1: hnf in *; auto. intros Hva.
      (* use previous lemma *)
      epose proof (@psent_mnt_sound_pre_pre (mkP src n msg true) Hnonbyz sta psa
        (mkW (upd n stb (localState w)) nil (* not important *)) _ ?[Goalq] ltac:(simpl; rewrite upd_refl; assumption)
        (sendout psb (sentMsgs w)) eq_refl ltac:(rewrite In_sendout; now right)) as Hgoal.
      [Goalq]:{ hnf. simpl. intros n0. unfold upd. destruct (Address_eqdec _ _); auto; congruence. }
      simpl in Hgoal. destruct Hgoal as (l0 & Ha0 & ((_ & Hre0) & HH0)). rewrite !upd_refl in Hre0.
      (* well, this is inevitable *)
      split.
      1:{ constructor; auto. revert Hre. apply Forall_impl. intros (src0, [ v0 lsig0 sig0 | (v0, cs0) | (v0, nsigs0) ]) Htmp.
        all: simpl in Htmp |- *; intros; try (rewrite Hvb in Htmp; rewrite Hva); intros.
        all: hnf in *; try is_true_rewrite; intuition.
        destruct (ACP.conf stb); saturate_assumptions; try discriminate. intuition. }
      split.
      1:{ apply Forall_app. split; auto. epose proof (procMsgWithCheck_fresh _ _ _) as Htmp. now rewrite E0 in Htmp. }
      (* compose *)
      pose proof (psent_mnt_append _ _ _ Ha Ha0) as Hq.
      exists (l0 ++ l). split.
      + erewrite psent_mnt_result_Ineq. 1: apply Hq.
        hnf. intros. autorewrite with psent. tauto.
      + rewrite state_effect_send_app. split.
        * erewrite state_effect_send_stmap_peq. 1: apply HH0.
          intros. unfold upd. now destruct_eqdec as_ ?.
        * (* TODO this is so bad ... *)
          clear Hq Ha. induction l as [ | a l IH ]; simpl; auto.
          simpl in HH. destruct HH as (HH & Ht). saturate_assumptions. split; auto.
          destruct (ps a) as [ n0 [ ? ? ? | (?, ?) | (?, ?) ] ]; simpl in Ht |- *. 
          all: unfold upd in Ht |- *; destruct_eqdec as_ <-; auto.
          (* time to use various persistence *)
          all: hnf in *; unfold zip_from_sigs in *. 
          all: destruct_and? Ht; split_and?; saturate_assumptions!; auto; try congruence.
          (* well, ... *)
          hnf in *. now apply lightcert_conflict_check_persistent with (st:=stb).
  }
  destruct Hgoal as (_ & Hv & Hre & Hfresh & l & Ha & HH).
  (* use the accumulation of state_effect_recv to prove the invariant! *)
  split.
  1:{ intros Hq. hnf in Hq |- *. intros p Hin. autorewrite with psent in Hin.
    unfold inv_submitmsg_receive in Hq |- *. destruct Hin as [ [ Hin | Hin ] | Hin ].
    - eapply Forall_forall in Hin; try eassumption; simpl in Hin. hnf. rewrite Hin. now destruct (msg p).
    - apply In_broadcast in Hin; destruct Hin as (? & ->); simpl. apply I.
    - specialize (Hq _ Hin). unfold upd. destruct p as [ src dst msg used ]. simpl in Hq |- *.
      destruct (Address_eqdec n dst) as [ <- | ]; auto.
      rewrite Est in Hq. hnf in Hq |- *. simpl in Hq |- *. rewrite Hv.
      destruct msg as [ v0 lsig0 sig0 | | ], used; auto.
      saturate_assumptions. eapply Forall_forall in Hq; try eassumption. simpl in Hq. now rewrite Hv in Hq. }
  match goal with |- context[SubmitMsg ?v ?lsig ?sig] =>
    let m := constr:(SubmitMsg v lsig sig) in
    exists ((mkPMT (broadcast n m) (PSbcast n m) (broadcast_all_fresh n m) eq_refl) :: l) end.
  split_and?; auto; simpl.
  - exists (sendout ps_ (sentMsgs w)). split; auto. 
    hnf. intros ?. autorewrite with psent. tauto.
  - split_and?; auto with ABCinv.
    now rewrite upd_refl.
Qed.

Fact psent_mnt_sound q w w' (Hstep : system_step q w w') (Hw : reachable w) :
  (lift_pkt_inv' inv_submitmsg_receive (sentMsgs w) (localState w) ->
    lift_pkt_inv' inv_submitmsg_receive (sentMsgs w') (localState w')) /\
  exists psk : psent_sender_kind (sentMsgs w),
    state_effect (localState w') psk /\
    match psk with
    | PSKnonbyz b l => psent_mnt b l (sentMsgs w')
    | PSKbyz _ p => localState w' = localState w (* this should be enough *) /\ sentMsgs w' = sendout1 p (sentMsgs w)
    end.
Proof.
  inversion_step' Hstep.
  - split; auto. now exists (PSKnonbyz (Pid _) nil).
  - pose proof (procMsgWithCheck_fresh (w @ dst) src msg) as Hfresh. unfold procMsgWithCheck in Hfresh. rewrite Ef in Hfresh. simpl in Hfresh.
    pose proof (id_coh_always_holds Hw) as Hcoh.
    let pkt := constr:(mkP src dst msg used) in
      unshelve eapply psent_mnt_sound_pre_pre with (p:=receive_pkt pkt) (psent:=consume pkt (sentMsgs w)) in Ef; try reflexivity; auto.
    1: rewrite In_consume; simpl; tauto.
    simpl in Ef. destruct Ef as (l & Ha & ((_ & Hre) & Hb)). rewrite upd_refl in Hre.
    split.
    (* TODO this proof is kind of repeating *)
    + intros Hq. hnf in Hq |- *. intros p Hin. autorewrite with psent in Hin.
      unfold inv_submitmsg_receive in Hq |- *. destruct Hin as [ Hin | Hin ].
      * eapply Forall_forall in Hin; try eassumption; simpl in Hin. hnf. rewrite Hin. now destruct (P0.msg p).
      * apply In_consume in Hin. simpl in Hin. destruct Hin as [ <- | (Hin & _) ].
        --simpl. rewrite upd_refl. hnf. simpl. destruct msg as [ v0 lsig0 sig0 | | ]; auto.
        --specialize (Hq _ Hin). unfold upd. destruct p as [ src0 dst0 msg0 used0 ]. simpl.
          destruct (Address_eqdec _ _) as [ <- | ] in |- *; auto.
          (* here, relies on the fact that receiving does not change the submitted value! *)
          hnf in Hq |- *. simpl in Hq |- *. destruct msg0 as [ | | ], used0; auto.
          saturate_assumptions. intros _.
          eapply state_mnt_sound_pre_pre with (n:=dst) in Hstep; auto.
          simpl in Hstep. rewrite !upd_refl in Hstep. destruct Hstep as (ll & _ & _ & Hvv). rewrite Hvv in Hq.
          (* and also some persistence *)
          pose proof (persistent_invariants_pre ll) as ([] & _). hnf in *.
          destruct (submitted_value stf); intros; try intuition.
          destruct (conf (w @ dst)); saturate_assumptions; auto. now is_true_rewrite.
    + (* this flipping is good *)
      exists (PSKnonbyz (Puse (sentMsgs w) (mkP src dst msg used) Hpin) l). simpl. rewrite upd_refl.
      split_and?; try tauto. now rewrite psent_mnt_base_change.
  - eapply psent_mnt_sound_pre in Hstep; auto.
    simpl in Hstep. destruct Hstep as (? & l & Hstep). destruct_and? Hstep.
    split; auto. exists (PSKnonbyz (Pid (sentMsgs w)) l). now simpl.
  - split.
    + intros Hq. hnf in Hq |- *. intros p Hin. rewrite In_sendout1 in Hin. 
      unfold inv_submitmsg_receive in Hq |- *. destruct Hin as [ <- | Hin ]; auto.
      hnf. simpl. now destruct m.
    + exists (PSKbyz _ (mkP n dst0 m false)).
      simpl. now rewrite_w_expand w in_ Hc.
Qed.

Fact inv_submitmsg_receive_always_holds : always_holds (lift_pkt_inv inv_submitmsg_receive).
Proof.
  intros w Hw. induction Hw as [ | q w w' Hstep Hw H ]; auto.
  - (* TODO streamline the proof here? *)
    unfold initWorld, initState, Init. hnf. simpl. intros. contradiction.
  - eapply psent_mnt_sound in H; eauto.
Qed.

Definition lift_pkt_inv_alt' (P : Packet -> PacketSoup -> Prop) : PacketSoup -> Prop :=
  fun psent => forall p, In p psent -> P p psent.

Definition lift_pkt_inv_alt (P : Packet -> PacketSoup -> Prop) : World -> Prop :=
  Eval unfold lift_pkt_inv_alt' in fun w => lift_pkt_inv_alt' P (sentMsgs w).

(* this bunch can pass the base case easily, since it does no work for existing packets *)
Record node_psent_h2l_invariants_sent_nonbyz p stmap : Prop := {
  _ : inv_submitmsg_correct p stmap;
  _ : inv_lightconfirmmsg_correct_nonbyz p stmap;
  _ : inv_confirmmsg_correct_nonbyz p stmap;
}.

(* this bunch can pass the base case easily, since it does no work for existing packets *)
(* sending only, since we do not model the local state of Byz node *)
Record node_psent_h2l_invariants_byz p history : Prop := {
  _ : inv_lightconfirmmsg_correct_byz p history;
  _ : inv_confirmmsg_correct_byz p history;
}.

(* this is not easy to prove individually, since we need to prove that 
    all packets sent out in Deliver or Intern transitions are from non-Byz nodes, 
    which needs another proof *)
(*
Fact h2l_invariants_byz :
  is_invariant_step (lift_pkt_inv_alt node_psent_h2l_invariants_byz).
Proof with (repeat (progress (hnf in *; intros))); simplify_eq; (repeat (progress (hnf in *; saturate_assumptions!))).
  hnf. intros ??? H Hstep.
  hnf in H |- *. intros [ src0 dst0 msg0 used0 ] Hin.
  inversion_step' Hstep; auto.
  - constructor; hnf.
    all: destruct msg0 as [ | (v0, cs0) | (v0, nsigs0) ]; auto; intros...
*)

(* this bunch can pass the cons case easily, since it does no work for fresh packets *)
(* for nonbyz only *)
Record node_psent_h2l_invariants_recv_pre p stmap : Prop := {
  (* _ : inv_submitmsg_receive p stmap; *)
  _ : inv_lightconfirmmsg_receive p stmap;
  _ : inv_confirmmsg_receive p stmap;
}.

Fact h2l_invariants_id_pre q w w' (Hstep : system_step q w w') (Hw : reachable w) p :
  (node_psent_h2l_invariants_sent_nonbyz p (localState w) ->
  forall used, node_psent_h2l_invariants_sent_nonbyz (mkP p.(src) p.(dst) p.(msg) used) (localState w')) /\
  (node_psent_h2l_invariants_recv_pre p (localState w) ->
  node_psent_h2l_invariants_recv_pre p (localState w')).
Proof.
  destruct p as [ src dst msg used ].
  pose proof (persistent_invariants Hstep Hw) as Hinv. (* use persistent properties to solve *)
  split; intros H.
  1: intros used'; simpl.
  all: constructor.
  all: match goal with |- ?def _ _ => pick def as_ H' by_ (destruct H); clear H; rename H' into H;
    unfold def end.
  all: destruct msg as [ | (?, ?) | (?, ?) ], used; simpl in *; try exact I.
  all: pose proof (Hinv src) as []; pose proof (Hinv dst) as [].
  all: intros; hnf in *; unfold zip_from_sigs in *; saturate_assumptions!; split_and?; destruct_and? H;
    try isSome_rewrite; try is_true_rewrite; saturate_assumptions; saturate_assumptions!.
  all: try solve [ eauto using lightcert_conflict_check_persistent | tauto | congruence | intuition ].
Qed.

Corollary h2l_invariants_id q w w' (Hstep : system_step q w w') (Hw : reachable w) psent :
  (lift_pkt_inv' node_psent_h2l_invariants_sent_nonbyz psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_sent_nonbyz psent (localState w')) /\
  (lift_pkt_inv' node_psent_h2l_invariants_recv_pre psent (localState w) ->
  lift_pkt_inv' node_psent_h2l_invariants_recv_pre psent (localState w')).
Proof.
  split; intros H; hnf in H |- *; intros [ src dst msg used ] Hin; specialize (H _ Hin).
  all: now eapply (h2l_invariants_id_pre Hstep Hw) in H; eauto.
Qed.

Fact h2l_invariants_pre :
  is_invariant_reachable_step_under id_coh (* needed, since will use psent_mnt_sound *)
    (fun w => lift_pkt_inv node_psent_h2l_invariants_sent_nonbyz w
      /\ lift_pkt_inv_alt node_psent_h2l_invariants_byz w
      /\ lift_pkt_inv node_psent_h2l_invariants_recv_pre w).
Proof with (repeat (progress (hnf in *; intros))); simplify_eq; (repeat (progress (hnf in *; saturate_assumptions))).
  hnf; intros q ?? Hw _ Hcoh Hcoh' H Hstep. unfold lift_pkt_inv, lift_pkt_inv_alt in H |- *. 
  (* get the effect *)
  pose proof Hstep as Hstep_.
  apply psent_mnt_sound in Hstep; try assumption.
  destruct Hstep as (_ & [ b l | [ src dst msg ? ] ] & Hse & Hpsent); simpl in Hse, Hpsent.
  - (* nonbyz step *)
    destruct Hse as (Hb & Hse). 
    remember (sentMsgs w') as psent eqn:Htmp; clear Htmp. (* TODO generalize? *)
    revert psent Hpsent H Hse. 
    induction l as [ | a l IH ]; intros.
    all: simpl in Hse, Hpsent.
    (* TODO why we do not need to destruct H here (and only need to destruct later)? can I explain? *)
    + destruct b as [ | p' Hin' ]; simpl in Hb, Hpsent; hnf in Hpsent.
      * split_and?; intros ?; rewrite Hpsent; revert p; try now apply (h2l_invariants_id Hstep_ Hw (sentMsgs w)).
        (* byz *)
        destruct H as (_ & H & _). 
        intros [ src0 dst0 [ | (v0, cs0) | (v0, nsigs0) ] used0 ] Hin; specialize (H _ Hin); destruct H; hnf in *.
        all: constructor; hnf; auto...
        all: setoid_rewrite Hpsent; saturate_assumptions!...
        all: auto.
      * split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H' by_ (destruct_and? H) end; 
          clear H; rename H' into H; setoid_rewrite Hpsent.
        1-2: intros [ src dst msg used ] Hin%(In_consume_conv_full Hin'). 
        1-2: destruct Hin as (used' & Hin); specialize (H _ Hin).
        --eapply (h2l_invariants_id_pre Hstep_ Hw) in H. simpl in H. exact H.
        --(* byz; TODO slightly repeating *)
          destruct msg as [ | (v0, cs0) | (v0, nsigs0) ], H.
          all: constructor; hnf; auto...
          all: setoid_rewrite Hpsent; saturate_assumptions!...
          all: destruct_exists; repeat match goal with HH : _ |- _ => apply (In_consume_fwd_full Hin') in HH end.
          all: eauto.
        --(* check which packet is consumed this time *)
          destruct p' as [ src' dst' msg' used' ].
          hnf in H |- *. intros p Hin%In_consume. simpl in Hin.
          destruct Hin as [ <- | (Hin & _) ].
          2: specialize (H _ Hin).
          1: destruct used'; [ specialize (H _ Hin') | ].
          1,3: eapply (h2l_invariants_id_pre Hstep_ Hw) in H; simpl in H; exact H.
          (* interesting part *)
          clear H. destruct Hb as (Hnonbyz & Hr).
          destruct msg' as [ v' lsig' sig' | (v', cs') | (v', nsigs') ]; simpl in Hr.
          all: constructor; try exact I.
          all: hnf; simpl; auto.
    + destruct a as [ pkts [ n m ] Hf Hcheck ]. simpl in *. subst pkts.
      clear Hb. destruct Hpsent as (psent_ & Hpmnt & Hineq), Hse as (Hse & Hnonbyz & Hb).
      saturate_assumptions!. clear H.
      split_and?; match goal with |- forall (_ : _), _ -> ?def _ _ => pick def as_ H by_ (destruct_and? IH) end; clear IH.
      all: intros p Hin%Hineq; autorewrite with psent in Hin.
      all: try (destruct Hin as [ (dst & ->)%In_broadcast | ]; [ | solve [ intuition ] ]).
      * (* interesting case *)
        constructor.
        all: hnf; destruct m as [ | [] | [] ]; simpl in *; auto.
      * (* byz; TODO slightly repeating *)
        rewrite In_broadcast in Hin.
        destruct Hin as [ (dst & ->) | Hin ]; 
          [ | specialize (H _ Hin); rename m into m0; destruct p as [ src0 dst0 m used0 ], H ]; 
          destruct m as [ | (v0, cs0) | (v0, nsigs0) ].
        all: constructor; hnf; auto; try congruence... (* is_byz conflict *)
        all: setoid_rewrite Hineq; saturate_assumptions!...
        all: setoid_rewrite In_sendout.
        all: destruct_exists; eauto.
      * constructor; destruct m as [ | [] | [] ]; hnf; auto.
  - (* byz step; easy? *)
    destruct Hse as (Hbyz & -> & Hcb), Hpsent as (Els & Hpsent), H as (HHsent & HHbyz & HHrcv). 
    rewrite Hpsent, Els. clear Els Hpsent.
    split_and?; intros p; rewrite In_sendout1; intros [ <- | Hin ]; auto.
    all: constructor; hnf; destruct msg as [ | [] | [] ]; simpl; intros; try solve [ auto | congruence | tauto ].
    (* now only Byz goals left *)
    all: clear HHsent HHrcv.
    all: tryif progress saturate_assumptions! then destruct HHbyz else idtac.
    (* here, do some manual work to avoid simplify_eq gives wierd substition results *)
    all: match goal with 
      | |- (match ?pp with _ => _ end) => destruct pp as [ src0 dst0 [ | [] | [] ] used0 ]; intros; simpl in *; auto; saturate_assumptions
      | _ => idtac end...
    all: saturate_assumptions!...
    all: simpl in *; setoid_rewrite In_sendout1.
    all: destruct_exists; eauto.
Qed.

Record node_psent_h2l_invariants_nonbyz p stmap : Prop := {
  _ : inv_submitmsg_correct p stmap;
  _ : inv_lightconfirmmsg_correct_nonbyz p stmap;
  _ : inv_confirmmsg_correct_nonbyz p stmap;
  _ : inv_submitmsg_receive p stmap;
  _ : inv_lightconfirmmsg_receive p stmap;
  _ : inv_confirmmsg_receive p stmap;
}.

Fact h2l_invariants :
  always_holds (lift_pkt_inv node_psent_h2l_invariants_nonbyz) /\
  always_holds (lift_pkt_inv_alt node_psent_h2l_invariants_byz).
Proof.
  unshelve epose proof (is_invariant_reachable_step_under_closed _ _ h2l_invariants_pre _ id_coh_always_holds) as H. 
  - simpl. split_and?; hnf; intros; contradiction.
  - rewrite !always_holds_and in H. destruct_and? H. split; auto.
    repeat progress (hnf in *; intros; saturate_assumptions!).
    pick node_psent_h2l_invariants_sent_nonbyz as_ HH1. 
    pick node_psent_h2l_invariants_recv_pre as_ HH2.
    destruct HH1, HH2. constructor; auto.
    now apply inv_submitmsg_receive_always_holds.
Qed.

End Backward.

End Main_Proof.

End ACInvariant.