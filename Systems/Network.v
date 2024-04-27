From Coq Require Import List Bool Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export States.

Module Type ByzSetting (Export A : NetAddr).

(* this part is not related (and should never be related) with the protocol implementation, 
    and also should not be instantiated (i.e., work like universally quantified variables) *)
(* FIXME: what if "is_byz" would change wrt. time? *)

Parameter is_byz : Address -> bool.

(* this module is not intended to be instantiated, so let's include things here anyway *)
Definition num_byz := length (List.filter is_byz valid_nodes).

Fact is_byz_synonym n : is_byz n <-> In n (filter is_byz valid_nodes).
Proof. rewrite filter_In. pose proof (Address_is_finite n). intuition. Qed.

Fact is_nonbyz_synonym n : is_byz n = false <-> In n (filter (fun n => negb (is_byz n)) valid_nodes).
Proof. rewrite filter_In, negb_true_iff. pose proof (Address_is_finite n). intuition. Qed.

Fact filter_byz_upper_bound [l : list Address] (Hnodup : List.NoDup l) :
  length (filter is_byz l) <= num_byz.
Proof.
  unfold num_byz.
  apply NoDup_incl_length; auto using NoDup_filter.
  intros ? (Hin & Hbyz)%filter_In.
  apply filter_In; auto using Address_is_finite.
Qed.

Corollary filter_nonbyz_lower_bound [l : list Address] (Hnodup : List.NoDup l) :
  length l - num_byz <= length (filter (fun n => negb (is_byz n)) l).
Proof.
  pose proof (filter_length is_byz l).
  pose proof (filter_byz_upper_bound Hnodup).
  lia.
Qed.

End ByzSetting.

Module Type RestrictedByzSetting (Export A : NetAddr) (Export BTh : ByzThreshold A) <: ByzSetting A.

(* usually, we require the number of Byzantine nodes to be no more than the threshold *)

Include ByzSetting A.

(* TODO a dilemma: 
  (1) put BTh as an module argument, but then BTh cannot be instantiated in Network/Invariant module
    since this ByzSetting will not be instantiated;
  (2) use another local t0 and use "with Definition t0 := " to connect the two t0s, 
    but not sure if that will work well or not 
  currently use (1), since we do not mean to instantiate the proof modules *)

Axiom num_byz_le_t0 : num_byz <= t0.

(* this will not be instantiated, so anyway *)

Lemma at_least_one_nonfaulty [l : list Address] (Hnodup : List.NoDup l)
  (Hlen : t0 < length l) : exists n, is_byz n = false /\ In n l.
Proof.
  pose proof (filter_length is_byz l).
  pose proof (filter_byz_upper_bound Hnodup).
  pose proof num_byz_le_t0.
  destruct (filter (fun _ => _) l) as [ | n l0 ] eqn:E in H.
  1: simpl in H; lia.
  pose proof (or_introl eq_refl : In n (n :: l0)) as HH.
  rewrite <- E in HH.
  apply filter_In in HH.
  exists n.
  now rewrite <- negb_true_iff.
Qed.

Lemma filter_nonbyz_lower_bound_t0 [l : list Address] (Hnodup : List.NoDup l) :
  length l - t0 <= length (filter (fun n => negb (is_byz n)) l).
Proof.
  pose proof (filter_nonbyz_lower_bound Hnodup).
  pose proof num_byz_le_t0.
  lia.
Qed.

Corollary nonbyz_lower_bound :
  N - t0 <= length (filter (fun n => negb (is_byz n)) valid_nodes).
Proof. apply filter_nonbyz_lower_bound_t0, valid_nodes_NoDup. Qed.

End RestrictedByzSetting.

Module Type Adversary (Export A : NetAddr) (Export M : MessageType) 
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : PacketType) (Export Pr : Protocol A M P BTh) 
  (Export Ns : NetState A M P BTh Pr).

(* FIXME: do we need to consider the case where a Byzantine node sends out multiple messages
    in one step? currently do not, since that would be equivalent with multiple steps *)
Parameter byz_constraints : Message -> World -> Prop.

End Adversary.

Module Type Network (Export A : NetAddr) (Export M : MessageType) 
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr) 
  (Export Adv : Adversary A M BTh BSett P Pr Ns).

Module Export PC : (* hide implementation *) PacketConsumption A M P := PacketConsumptionImpl A M P.
Module Export PC' := PacketConsumptionImpl' A M P PC.

Inductive system_step_descriptor : Type :=
  | Idle (* stuttering *)
  | Deliver (p : Packet) 
  | Intern (proc : Address) (t : InternalTransition) 
  | Byz (src dst : Address) (m : Message)
.

Definition next_world (q : system_step_descriptor) (w : World) : World :=
  match q with
  | Idle => w
  | Deliver p => 
    let: (st', ms) := procMsgWithCheck (w @ (dst p)) (src p) (msg p) in
    mkW (upd (dst p) st' (localState w)) (sendout ms (consume p (sentMsgs w)))
  | Intern proc t =>
    let: (st', ms) := (procInt (w @ proc) t) in
    mkW (upd proc st' (localState w)) (sendout ms (sentMsgs w))
  | Byz src dst m =>
    mkW (localState w) (sendout1 (mkP src dst m false) (sentMsgs w))
  end.

(* TODO use this or indexed inductive relation? currently seems no difference *)
Inductive system_step (q : system_step_descriptor) (w w' : World) : Prop :=
| IdleStep of q = Idle & w = w'

| DeliverStep (p : Packet) of
      q = Deliver p &
      In p (sentMsgs w) &
      (* try modelling message duplication by not checking whether p has been consumed or not *)
      (* FIXME: parameterizing here shall result in different models *)
      is_byz (dst p) = false &
      (* cannot reduce inside the inductive definition *)
      (* let: ww := next_world (Deliver p) w in w' = ww *)
      let: (st', ms) := procMsgWithCheck (localState w (dst p)) (src p) (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               (sendout ms (consume p (sentMsgs w)))

| InternStep (proc : Address) (t : InternalTransition) of
      q = Intern proc t &
      is_byz proc = false &
      let: (st', ms) := (procInt (localState w proc) t) in
      w' = mkW (upd proc st' (localState w))
               (sendout ms (sentMsgs w))

| ByzStep (src dst : Address) (m : Message) of
      q = Byz src dst m &
      is_byz src &
      byz_constraints m w &
      w' = mkW (localState w)
               (sendout1 (mkP src dst m false) (sentMsgs w))
.

Fact next_world_sound q w w' (H : system_step q w w') : w' = next_world q w.
Proof. inversion H; subst; simpl; auto. 1: now destruct (procMsgWithCheck _ _ _). 1: now destruct (procInt _ _). Qed.

Local Ltac inversion_step_ H Heq :=
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

Global Tactic Notation "inversion_step" hyp(H) :=
  let Heq := fresh "Heq" in inversion_step_ H Heq.

Global Tactic Notation "inversion_step'" hyp(H) :=
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
    match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  | destruct (procInt _ _) as (st', ms) eqn:E in Heq;
    match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  | match type of Heq with ?w' = _ => try (subst w'; simpl_world) end
  ].

(* inversion lemmas *)

Fact DeliverStep_inv p w w' (H : system_step (Deliver p) w w') :
  In p (sentMsgs w) /\ is_byz (dst p) = false /\
  exists st' ms, procMsgWithCheck (localState w (dst p)) (src p) (msg p) = (st', ms) /\
    w' = mkW (upd (dst p) st' (localState w)) (sendout ms (consume p (sentMsgs w))).
Proof.
  inversion H; try discriminate.
  match goal with HH : Deliver _ = Deliver _ |- _ => injection HH as <- end.
  rewrite (surjective_pairing (procMsgWithCheck _ _ _)) in *.
  do 2 (split; try assumption).
  do 2 eexists.
  split; [ reflexivity | assumption ].
Qed.

Section Network_Model_Generic_Lemmas.

Fact step_preserves_World_rel w1 w2 w1' w2' (H : World_rel w1 w1')
  q (Hstep : system_step q w1 w2) (Hstep' : system_step q w1' w2') :
  World_rel w2 w2'.
Proof.
  inversion_step_ Hstep Ef; inversion_step_ Hstep' Ef'; try discriminate; auto.
  all: destruct H as (Hstmap & Hpsent); hnf in Hpsent.
  - injection Hq as <-. rewrite <- Hstmap in Ef'.
    destruct (procMsgWithCheck _ _ _) in Ef, Ef'. subst.
    hnf. simpl. split; [ intros ?; unfold upd; now destruct_eqdec as_ ? | ].
    hnf. intros ?. autorewrite with psent. now rewrite !In_consume, Hpsent.
  - revert Hq. intros [= <- <-]. rewrite <- Hstmap in Ef'.
    destruct (procInt _ _) in Ef, Ef'. subst.
    hnf. simpl. split; [ intros ?; unfold upd; now destruct_eqdec as_ ? | ].
    hnf. intros ?. autorewrite with psent. now rewrite Hpsent.
  - revert Hq. intros [= <- <- <-].
    subst. hnf; simpl. split; auto. 
    hnf. intros ?. autorewrite with psent. now rewrite Hpsent.
Qed.

(* atomicity of node state change (i.e., at most one node changes its state in one step) *)
(* FIXME: the following n can be known from q! *)
Fact localState_change_atomic [q w w'] (H : system_step q w w') :
  localState w' = localState w \/ exists n st, localState w' = upd n st (localState w).
Proof.
  inversion H; try subst; auto.
  1: rewrite (surjective_pairing (procMsgWithCheck _ _ _)) in *.
  2: rewrite (surjective_pairing (procInt _ _)) in *.
  all: simpl in *; subst; simpl; eauto.
Qed.

Corollary consume_norevert [p psent] (Hin : In (receive_pkt p) psent) p' :
  In (receive_pkt p) (consume p' psent).
Proof.
  apply In_consume.
  destruct (Packet_eqdec (receive_pkt p) p') as [ <- | ]; simpl.
  - left.
    now apply receive_pkt_idem.
  - intuition.
Qed.

Fact system_step_psent_persistent [p w w' q] : 
  In p (sentMsgs w) -> system_step q w w' -> exists p', pkt_le p p' /\ In p' (sentMsgs w').
Proof.
  intros H Hstep.
  inversion Hstep; subst; eauto using Reflexive_pkt_le.
  3: exists p; simpl; rewrite In_sendout1; auto using Reflexive_pkt_le.
  1: destruct (procMsgWithCheck _ _ _) in *.
  2: destruct (procInt _ _) in *.
  all: subst w'; simpl.
  all: setoid_rewrite In_sendout.
  - setoid_rewrite In_consume.
    destruct (Packet_eqdec p p0) as [ <- | ].
    + exists (receive_pkt p); intuition.
      hnf; now right.
    + exists p; intuition.
      reflexivity.
  - exists p; auto using Reflexive_pkt_le.
Qed.

Corollary system_step_psent_persistent_weak_full [src dst msg w w' q] : 
  (exists used, In (mkP src dst msg used) (sentMsgs w)) ->
  system_step q w w' -> 
  (exists used, In (mkP src dst msg used) (sentMsgs w')).
Proof.
  intros (used & H) Hstep.
  eapply system_step_psent_persistent in H; eauto.
  unfold pkt_le in H; simpl in H.
  destruct H as (_ & [ -> | -> ] & ?); eauto.
Qed.

Corollary system_step_psent_norevert [p w w' q] : 
  In (receive_pkt p) (sentMsgs w) -> system_step q w w' -> In (receive_pkt p) (sentMsgs w').
Proof.
  intros H H0.
  eapply system_step_psent_persistent in H; eauto.
  destruct H as (p' & Hle & Hin).
  hnf in Hle; rewrite receive_pkt_idem in Hle.
  now destruct Hle as [ -> | -> ].
Qed.

Corollary system_step_psent_norevert_full [src dst msg w w' q] :
  In (mkP src dst msg true) (sentMsgs w) -> system_step q w w' -> In (mkP src dst msg true) (sentMsgs w').
Proof. rewrite <- receive_pkt_intact with (p:=mkP _ _ _ _) in |- * by auto. apply system_step_psent_norevert. Qed.

(* a received message must be already in the last network state *)
(* HMM more like a trick? *)
Fact system_step_received_inversion_full [src dst msg w w' q]
  (* TODO well, this is not very good ... *)
  (Hfresh1 : forall st src m, Forall (fun p => p.(consumed) = false) (snd (procMsgWithCheck st src m)))
  (Hfresh2 : forall st t, Forall (fun p => p.(consumed) = false) (snd (procInt st t))) : 
  In (mkP src dst msg true) (sentMsgs w') -> system_step q w w' -> 
  exists used, In (mkP src dst msg used) (sentMsgs w).
Proof.
  intros H Hstep.
  inversion Hstep; subst; eauto using Reflexive_pkt_le; simpl in *.
  1: destruct (procMsgWithCheck _ _ _) eqn:E in *.
  2: destruct (procInt _ _) eqn:E in *.
  all: try subst; simpl in H.
  all: autorewrite with psent in H.
  1: match type of E with procMsgWithCheck ?a ?b ?c = _ => 
    specialize (Hfresh1 a b c); rewrite Forall_forall, E in Hfresh1; simpl in Hfresh1 end. 
  2: match type of E with procInt ?a ?b = _ => 
    specialize (Hfresh2 a b); rewrite Forall_forall, E in Hfresh2; simpl in Hfresh2 end. 
  2-3: destruct H as [ H | ]; eauto.
  3: discriminate.
  2: specialize (Hfresh2 _ H); simpl in Hfresh2; discriminate.
  destruct H as [ H | ].
  1: specialize (Hfresh1 _ H); simpl in Hfresh1; discriminate.
  apply In_consume_conv_full in H; try assumption.
Qed.

End Network_Model_Generic_Lemmas.

Section Finite_System_Trace.

(* two multistep propositions *)

Fixpoint system_trace (w : World) (l : list (system_step_descriptor * World)) : Prop :=
  match l with
  | nil => True
  | (q, w') :: l' => system_step q w w' /\ system_trace w' l'
  end.

Definition final_world (w : World) (l : list (system_step_descriptor * World)) := (snd (last l (Idle, w))).

Fact system_trace_app w l1 l2 :
  system_trace w (l1 ++ l2) <-> system_trace w l1 /\ system_trace (final_world w l1) l2.
Proof.
  revert w l2.
  induction l1 as [ | (q, w') l1 IH ] using rev_ind; intros.
  - now unfold final_world.
  - unfold final_world.
    rewrite <- app_assoc, ! IH, last_last.
    now simpl.
Qed.

Corollary system_trace_snoc w l q w' :
  system_trace w (l ++ (q, w') :: nil) <-> system_trace w l /\ system_step q (final_world w l) w'.
Proof. rewrite system_trace_app. simpl. intuition. Qed.

Fact final_world_nil w : final_world w nil = w. Proof eq_refl.

Fact final_world_app w l1 l2 : final_world w (l1 ++ l2) = final_world (final_world w l1) l2.
Proof.
  revert w l1.
  induction l2 as [ | (q, w') l2 IH ] using rev_ind; intros.
  - rewrite app_nil_r.
    now unfold final_world.
  - unfold final_world.
    now rewrite -> app_assoc, ! last_last.
Qed.

Fact final_world_cons w q w' l : final_world w ((q, w') :: l) = final_world w' l.
Proof.
  change (_ :: l) with (((q, w') :: nil) ++ l).
  rewrite final_world_app.
  reflexivity.
Qed.

Fact final_world_snoc w q w' l : final_world w (l ++ (q, w') :: nil) = w'.
Proof. now rewrite final_world_app. Qed. 

End Finite_System_Trace.

Inductive reachable : World -> Prop :=
  | ReachableInit : reachable initWorld
  | ReachableStep q (w w' : World) (Hstep : system_step q w w')
    (H_w_reachable : reachable w) : reachable w'.

Global Arguments ReachableStep [_ _ _] _ _.

Fact reachable_witness w : reachable w <-> exists l, system_trace initWorld l /\ w = final_world initWorld l.
Proof.
  split.
  - intros H.
    induction H as [ | q w w' Hstep H_w_reachable (l & H1 & H2) ].
    + now exists nil.
    + exists (l ++ ((q, w') :: nil)).
      now rewrite system_trace_snoc, final_world_snoc, <- H2.
  - intros (l & H & ->).
    induction l as [ | (q, w) l IH ] using rev_ind; auto using ReachableInit.
    rewrite final_world_snoc.
    rewrite system_trace_snoc in H.
    destruct H.
    econstructor; eauto.
Qed.

(* definition of (non-dependent) invariant *)
(*
Definition is_invariant_trace_dep (P : World -> Prop) (Q : World -> World -> Prop) : Prop :=
  forall w l, P w -> system_trace w l -> Q w (final_world w l).

Definition is_invariant_step_dep (P : World -> Prop) (Q : World -> World -> Prop) : Prop :=
  forall q w w', P w -> system_step q w w' -> Q w w'.
*)
Definition is_invariant_trace (P : World -> Prop) : Prop :=
  forall w l, P w -> system_trace w l -> P (final_world w l).

Definition is_invariant_step (P : World -> Prop) : Prop :=
  forall q w w', P w -> system_step q w w' -> P w'.

Fact is_invariant_step_trace (P : World -> Prop) :
  is_invariant_trace P <-> is_invariant_step P.
Proof.
  unfold is_invariant_trace, is_invariant_step.
  split.
  - intros H q w w' Hp Hstep.
    specialize (H w ((q, w') :: nil) Hp).
    now apply H.
  - intros H w l Hp Htrace.
    induction l as [ | (q, w') l IH ] using rev_ind; auto.
    rewrite final_world_snoc.
    rewrite system_trace_snoc in Htrace.
    destruct Htrace as (Htrace & Hstep).
    clear Hp.
    specialize (IH Htrace).
    eapply H; eauto.
Qed.

Definition is_invariant_reachable_step (P : World -> Prop) : Prop :=
  forall q w w', reachable w -> P w -> system_step q w w' -> P w'.

(* full; with everything *)
Definition is_invariant_reachable_step_under (P Q : World -> Prop) : Prop :=
  forall q w w', reachable w -> reachable w' -> P w -> P w' -> Q w -> system_step q w w' -> Q w'.
(*
Fact is_invariant_implconj (P Q : World -> Prop) (Hisinv : is_invariant_step P) 
  (Hpq : forall w, P w -> Q w) : is_invariant_step (fun w => P w /\ Q w).
Proof.
  hnf in Hisinv |- *.
  intros.
  destruct H.
  split.
  1: eapply Hisinv; eauto.
  eapply Hpq, Hisinv; eauto.
Qed.
*)

(* invariant proof mode? *)
(* or, maybe there is just no need ... we can just consider the invariants that always hold *)

Definition always_holds (P : World -> Prop) : Prop := forall w, reachable w -> P w.

Fact always_holds_and P Q : always_holds (fun w => P w /\ Q w) <-> always_holds P /\ always_holds Q.
Proof. unfold always_holds. firstorder. Qed.

Fact always_holds_impl P Q (H : always_holds P) (H' : forall w, P w -> Q w) : always_holds Q.
Proof. unfold always_holds. firstorder. Qed.

Fact is_invariant_reachable_step_under_closed P Q (Hr : is_invariant_reachable_step_under P Q)
  (Hi : Q initWorld) (H : always_holds P) : always_holds Q.
Proof.
  hnf in H, Hr |- *. intros w Hw. 
  induction Hw; auto. pose proof (ReachableStep Hstep Hw) as Hw'. pose proof (H _ Hw). pose proof (H _ Hw'). firstorder.
Qed.

Global Ltac always_holds_decompose lemma :=
  let H := fresh "H" in pose proof lemma as H; rewrite ! always_holds_and in H; tauto.

Definition is_grounded_invariant (P : World -> Prop) : Prop :=
  P initWorld /\ is_invariant_step P.

(* another way to prove always_holds is by induction on reachable relation *)
Fact grounded_invariant_always_holds P (H : is_grounded_invariant P) : always_holds P.
Proof. destruct H as (Hinit & H). hnf in H |- *. intros w Hr. induction Hr; firstorder. Qed. 

Definition is_invariant_step_under (P Q : World -> Prop) : Prop :=
  forall q w w', P w -> P w' -> Q w -> system_step q w w' -> Q w'.

Fact is_invariant_step_under_clear [P] (Hinv : is_invariant_step P) Q : 
  is_invariant_step_under Q P.
Proof. hnf in *. firstorder. Qed.
(*
Fact is_invariant_step_under_weaken [P]
  (Hinv : is_invariant_step P) Q : is_invariant_step_under (fun w => P w /\ Q w).
Proof. hnf in *. intros ??? (Hp & Hq) Hstep. split; [ firstorder | ]. eapply H; eauto. Qed. 
*)
Fact is_invariant_step_under_intro_l [P Q R] (H : is_invariant_step_under (fun w => P w /\ Q w) R)
  (H0 : is_invariant_step_under P Q) : is_invariant_step_under P (fun w => Q w /\ R w).
Proof. hnf in *. intros ????? (? & ?) ?. saturate_assumptions!. split; [ auto | firstorder ]. Qed.

Fact is_invariant_step_under_split [P Q R] (Hl : is_invariant_step_under P Q)
  (Hr : is_invariant_step_under P R) : is_invariant_step_under P (fun w => Q w /\ R w).
Proof. hnf in *. firstorder. Qed.

Fact is_invariant_step_under_closed [P Q] (H : is_invariant_step_under P Q)
  (Hinv : is_invariant_step P) : is_invariant_step (fun w => P w /\ Q w).
Proof. hnf in *. intros ??? (? & ?) ?. now saturate_assumptions!. Qed.

(* some examples of invariants *)

Fact true_is_invariant : is_invariant_step (fun _ => True).
Proof. now hnf. Qed.

Fact reachable_is_invariant : is_invariant_step reachable.
Proof. intros ? ? ? ? ?. eapply ReachableStep; eauto. Qed.

Fact reachable_by_trace [w l] (H : system_trace w l) (Hr : reachable w) : reachable (final_world w l).
Proof. pose proof (reachable_is_invariant) as HH. rewrite <- is_invariant_step_trace in HH. eapply HH; eauto. Qed.

Corollary psent_norevert_is_invariant p : is_invariant_step (fun w => In (receive_pkt p) (sentMsgs w)).
Proof. hnf. intros ???. apply system_step_psent_norevert. Qed.

Corollary psent_norevert_pkts_is_invariant pkts : is_invariant_step (fun w => incl (map receive_pkt pkts) (sentMsgs w)).
Proof.
  induction pkts as [ | p pkts IH ]; hnf; unfold incl; simpl; intros.
  1: contradiction.
  destruct H1 as [ <- | H1 ].
  - eapply system_step_psent_norevert; eauto.
  - eapply IH; eauto.
    hnf.
    intros; eapply H; eauto.
Qed.

(* good packet and angelic trace *)

Definition good_packet p :=
  is_byz (src p) = false /\ is_byz (dst p) = false.

Fact good_packet_dec p : {good_packet p} + {~ good_packet p}.
Proof.
  unfold good_packet.
  destruct (is_byz (src p)), (is_byz (dst p)); auto.
  all: now right.
Qed.

Fact pkt_le_good_packet [p p'] : pkt_le p p' -> good_packet p <-> good_packet p'.
Proof. intros [ -> | -> ]. all: destruct p; intuition. Qed.

(* simple existence condition; avoiding some vacuous cases *)
(* ... but does not justify "fairness => liveness" *)
(* this should be generalizable to any system with the same model *)

Fact list_packets_deliverable [pkts w]
  (Hgood : Forall good_packet pkts) (Hincl : incl pkts (sentMsgs w)) :
  exists l, system_trace w l /\
    incl (map receive_pkt pkts) (sentMsgs (final_world w l)).
Proof.
  revert w Hincl.
  induction Hgood as [ | p pkts Hg Hgood IH ]; intros.
  - now exists nil.
  - destruct (procMsgWithCheck (localState w (dst p)) (src p) (msg p)) as (st', ms) eqn:E.
    pose (w' := 
      if (in_dec Packet_eqdec p pkts)
      then w else (mkW (upd (dst p) st' (localState w)) (sendout ms (consume p (sentMsgs w))))).
    assert (incl pkts (sentMsgs w')) as Htmp.
    { subst w'.
      destruct (in_dec Packet_eqdec p pkts) as [ Hin | Hnotin ]; simpl; hnf in Hincl |- *.
      - firstorder.
      - intros p' Hin'.
        specialize (Hincl _ (or_intror Hin')).
        simpl; rewrite In_sendout, In_consume.
        right; right.
        split; [ assumption | now intros -> ].
    }
    specialize (IH _ Htmp).
    destruct IH as (l & Htrace & Hres).
    exists (if (in_dec Packet_eqdec p pkts) then l else ((Deliver p, w') :: l)).
    destruct (in_dec Packet_eqdec p pkts) as [ Hin | Hnotin ]; subst w'.
    + split; try assumption.
      hnf in Hres |- *.
      simpl.
      intros p' [ <- | Hin' ].
      * now apply Hres, in_map.
      * now apply Hres.
    + split.
      * cbn delta [system_trace] iota beta.
        split; try assumption.
        hnf in Hg.
        apply DeliverStep with (p:=p); try reflexivity; try tauto.
        1: apply (Hincl _ (or_introl eq_refl)).
        now rewrite E.
      * rewrite final_world_cons.
        hnf in Hres |- *.
        intros p' [ <- | Hin' ]; auto.
        (* use the invariant *)
        pose proof (psent_norevert_is_invariant p) as HH%is_invariant_step_trace.
        apply HH; try assumption.
        simpl; rewrite In_sendout, In_consume; simpl; tauto.
Qed.

(* some other things; not quite related with network semantics, but I do not know anywhere to put *)

(* maybe this lemma has been well formalized in other Coq libraries ... *)
Lemma set_intersection_size [l1 l2 : list Address] (Hnodup1 : NoDup l1) (Hnodup2 : NoDup l2)
  [a] (Hsize1 : a <= length l1) (Hsize2 : a <= length l2) :
  (a + a - N) <= length (filter (fun n => In_dec Address_eqdec n l1) l2).
Proof.
  destruct (partition (fun n => In_dec Address_eqdec n l1) l2) as (l12, l2') eqn:Epar.
  epose proof (partition_filter _ l2) as Htmp.
  rewrite -> Epar, -> pair_equal_spec in Htmp.
  destruct Htmp as (El12 & El2').
  rewrite <- El12.
  cut (((length l2) - (length l12)) + (length l1) <= N).
  1: lia.
  pose proof Epar as Elengthpar.
  apply partition_length in Elengthpar.
  replace ((length l2) - (length l12)) with (length l2') by lia.
  unfold N.
  rewrite <- app_length.
  apply NoDup_incl_length.
  - subst l2'.
    apply NoDup_app; auto.
    + now apply NoDup_filter.
    + intros x y (Hin1' & HH)%filter_In Hin2' <-.
      now destruct (in_dec Address_eqdec x l1).
  - intros ? _.
    now apply Address_is_finite.
Qed.

Corollary quorum_intersection [l1 l2 : list Address] (Hnodup1 : NoDup l1) (Hnodup2 : NoDup l2)
  (Hsize1 : N - t0 <= length l1) (Hsize2 : N - t0 <= length l2) :
  (N - (t0 + t0)) <= length (filter (fun n => In_dec Address_eqdec n l1) l2).
Proof. etransitivity. 2: eapply set_intersection_size; eassumption. lia. Qed.

End Network.

(* kind of useful, so put here *)
Module CommonLiftOperations (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr).

Definition lift_point_to_edge {A : Type} (P : A -> Prop) : A -> A -> Prop :=
  fun st st' => P st -> P st'.

Definition lift_state_pair_inv (P : State -> State -> Prop) : World -> World -> Prop :=
  fun w w' => forall n, P (w @ n) (w' @ n).

Definition lift_state_inv (P : State -> Prop) : World -> Prop := fun w => forall n, P (w @ n).

Definition lift_node_inv (P : PacketSoup -> State -> Prop) : World -> Prop :=
  fun w => forall n, is_byz n = false -> P (sentMsgs w) (w @ n).

Definition lift_pkt_inv' (P : Packet -> StateMap -> Prop) : PacketSoup -> StateMap -> Prop :=
  fun psent stmap => forall p, In p psent -> P p stmap.

Definition lift_pkt_inv (P : Packet -> StateMap -> Prop) : World -> Prop :=
  Eval unfold lift_pkt_inv' in fun w => lift_pkt_inv' P (sentMsgs w) (localState w).

Definition lift_pkt_inv_alt' (P : Packet -> PacketSoup -> Prop) : PacketSoup -> Prop :=
  fun psent => forall p, In p psent -> P p psent.

Definition lift_pkt_inv_alt (P : Packet -> PacketSoup -> Prop) : World -> Prop :=
  Eval unfold lift_pkt_inv_alt' in fun w => lift_pkt_inv_alt' P (sentMsgs w).

End CommonLiftOperations.

Module NetworkImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr) 
  (Export Adv : Adversary A M BTh BSett P Pr Ns) <: Network A M BTh BSett P PSOp Pr Ns Adv.

Include Network A M BTh BSett P PSOp Pr Ns Adv.
Include CommonLiftOperations A M BTh BSett P PSOp Pr Ns. (* since usually NetworkImpl will be called when doing invariant proofs *)

End NetworkImpl.
