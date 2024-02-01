From Coq Require Import List Bool Lia ssrbool ListSet Permutation PeanoNat.
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
From ABCProtocol Require Import Types Address Protocol States Network ListFacts Invariant.
From ABCProtocol Require Import InfSeqAdaptor.

Module Type ACLiveness 
  (A : NetAddr) (T : Types A) (AC : ACProtocol A T) (Ns : NetState A T AC)
  (ACN : ACNetwork A T AC Ns) (ACInv : ACInvariant A T AC Ns ACN).

Import A T AC Ns ACN ACInv.

(* For infinite sequences, there should be better ways to do ... *)
(*
CoInductive system_trace_coind : World -> infseq (system_step_descriptor * World) -> Prop :=
  STCintro : forall w q w' l, 
    system_step q w w' ->
    system_trace_coind w' l ->
    system_trace_coind w (Cons (q, w') l).
*)

CoInductive system_trace_coind : World -> Stream system_step_descriptor -> Stream World -> Prop :=
  STCintro : forall w q w' l1 l2, 
    system_step q w w' ->
    system_trace_coind w' l1 l2 ->
    system_trace_coind w (Cons q l1) (Cons w' l2).

Fact system_trace_coind_inv w l :
  system_trace_coind w l -> 
    system_step (fst (Streams.hd l)) w (snd (Streams.hd l)) /\
    system_trace_coind (snd (Streams.hd l)) (Streams.tl l).
Proof. destruct l. intros H. inversion H. subst. simpl. auto. Qed.

(* TODO is this a general folding property? *)

Lemma system_trace_coind_prefix w l n (H : system_trace_coind w l) :
  system_trace w (Str_firstn n l).
Proof.
  revert w l H. induction n; intros; simpl; auto.
  destruct l as ((q, w'), l). simpl.
  apply system_trace_coind_inv in H. simpl in H. destruct H.
  split; auto.
Qed.

Lemma system_trace_coind_suffix w l n (H : system_trace_coind w l) :
  system_trace_coind (match n with O => w | S n' => snd (Str_nth n' l) end) (Str_nth_tl n l).
Proof.
  revert w l H. induction n; intros; simpl; auto.
  destruct l as ((q, w'), l). simpl. 
  apply system_trace_coind_inv in H. simpl in H. destruct H.
  destruct n; simpl; auto.
  unfold Str_nth. simpl. fold (Str_nth n l). apply IHn in H0.
  destruct l. simpl in *. auto.
Qed.

(* the temporal version of is_invariant_step ... not so convenience? *)

(* Fact is_invariant_step_temporal P (H : is_invariant_step P) w l :
  system_trace_coind w l ->  *)

(* TODO the map over Stream cannot normalize very well ... is it a "bug"?
    also, the proof of map_Cons is very interesting *)

(* TODO we cannot use "exists" for coinductive type? so using infseq World may lose some information ... *)

Definition world_trace w (l : infseq (system_step_descriptor * World)) : infseq World :=
  Cons w (map snd l).

Fact world_trace_is_map_snd w l : world_trace w l = map snd (Cons (Idle, w) l).
Proof. unfold world_trace. rewrite map_Cons. reflexivity. Qed.

(* TODO move this somewhere else *)
(* Definition system_trace' l := match l with nil => True | (q, w) :: l' => system_trace w l' end. *)

(* FIXME: the switching between list of worlds and list of pairs is troublesome! *)

(* TODO is this a good lemma? *)
Fact is_invariant_world_trace_prepend P (H : is_invariant_step P) l w s :
  now P (Str_prepend_list (List.map snd l) (map snd s)) -> 
  system_trace_coind w (Str_prepend_list l s) -> 
  now P (map snd s).
Proof.
  revert w s.
  induction l as [ | (q, w') l IH ]; intros; auto.
  simpl in * |-. apply system_trace_coind_inv in H1. simpl in *. destruct H1. 
  eapply IH; eauto.
  destruct l as [ | (qq, ww') l ]; simpl in *; auto.
  - apply system_trace_coind_inv in H2. destruct H2. apply H in H2; auto.
  - apply system_trace_coind_inv in H2. destruct H2. apply H in H2; auto.
Qed.

Corollary is_invariant_world_trace_prepend' P (H : is_invariant_step P) l w
  (Htrace : system_trace_coind w l) n1 n2 :
  now P (Str_prepend_list (Str_firstn n1 (Str_nth_tl n2 (world_trace w l))) 
    (Str_nth_tl (n1 + n2) (world_trace w l))) -> 
  now P (Str_nth_tl (n1 + n2) (world_trace w l)).
Proof.
  rewrite -> ! world_trace_is_map_snd, -> ! Str_nth_tl_map. intros HH.
  eapply is_invariant_world_trace_prepend; auto.
  2: rewrite Str_firstn_prepend'; apply system_trace_coind_suffix.
  2: constructor; auto. 2: apply IdleStep; eauto. (* idle can be regarded as a trick *)
  now rewrite <- Str_firstn_map.
Qed.

(* traditional weak fairness ...? or just one version? *)

Definition weak_fairness_delivery (l : infseq World) : Prop :=
  forall p : Packet, good_packet p -> 
    continuously (now (fun w => In p (sentMsgs w))) l ->
    eventually (now (fun w => In (receive_pkt p) (sentMsgs w))) l.

Definition weak_fairness_delivery' (l : infseq World) : Prop :=
  forall pkts : list Packet, Forall good_packet pkts -> 
    continuously (now (fun w => incl pkts (sentMsgs w))) l ->
    eventually (now (fun w => incl (List.map receive_pkt pkts) (sentMsgs w))) l.

Fact weak_fairness_deliveryP w l (Htrace : system_trace_coind w l) :
  weak_fairness_delivery (world_trace w l) -> weak_fairness_delivery' (world_trace w l).
Proof.
  unfold weak_fairness_delivery, weak_fairness_delivery'.
  (* split; intros H. *)
  intros H.
  - intros pkts Hf. induction Hf; intros.
    + now apply E0.
    + unfold incl. simpl. specialize (H _ H0).
      pose proof H1 as Hq.
      eapply continuously_monotonic in Hq. 1: apply H in Hq.
      2: intros (?, ?); unfold incl; simpl; firstorder.
      pose proof H1 as Hq2.
      eapply continuously_monotonic in Hq2. 1: apply IHHf in Hq2.
      2: intros (?, ?); unfold incl; simpl; firstorder.
      (* turn to counting semantics *)
      rewrite <- eventually_n_eventually in Hq, Hq2 |- *.
      destruct Hq as (n & Hq), Hq2 as (n2 & Hq2). 
      exists (n + n2).
      rewrite <- Str_firstn_prepend' with (n1:=n2) in Hq.
      rewrite <- Str_firstn_prepend' with (n1:=n) in Hq2.
      apply is_invariant_world_trace_prepend' in Hq, Hq2; auto.
      2-3: try apply psent_norevert_is_invariant; try apply psent_norevert_pkts_is_invariant.
      rewrite Nat.add_comm in Hq.
      remember (Str_nth_tl _ _) as s. destruct s as (xs, s). 
      hnf in Hq, Hq2 |- *. intros. destruct H2 as [ <- | ]; firstorder.
  (* TODO the other direction *)
Qed.
(*
Definition good_world_trace (l : infseq World) : Prop :=
  exists l' : infseq system_step_descriptor, 
    system_trace_coind (hd l) (zipWith pair l' (tl l)).
*)
(* TODO how to implement the NEXT thing in TLA+? *)

Section Temp.

From InfSeqExt Require Import map.

Fact map_EqSt [A B : Type] (f : A -> B) (l : Stream A) :
  EqSt (map f l) (Streams.map f l).
Proof.
  revert l.
  cofix H. intros l. destruct l. rewrite InfSeqAdaptor.map_Cons, map_Cons.
  constructor; simpl; auto.
Qed.
(*
Definition good_world_trace (l : infseq World) : Prop :=
  exists l' : infseq system_step_descriptor, 
    system_trace_coind (hd l) (zip l' (tl l)).

Fact good_world_trace_recover l :
  good_world_trace l -> 
  exists ll, system_trace_coind (hd l) ll /\ EqSt l (world_trace (hd l) ll).
Proof.
  intros (l' & H). exists (zip l' (tl l)). split; auto.
  unfold world_trace. rewrite <- recons at 1. constructor; auto.
  simpl. eapply trans_EqSt. 2: apply map_EqSt. apply sym_EqSt, EqSt_exteq, exteq_snd_zip.
Qed.
*)
End Temp.

(* now, redo the liveness proofs using weak_fairness_delivery *)

Section Proof_of_Terminating_Convergence.

  (* Variables (w : World) (v : Value).
  Hypotheses (H_w_reachable : reachable w) (H1 : all_honest_nodes_submitted v w). *)
  Variables (v : Value).
  Hypothesis (H_byz_minor : num_byz <= t0).

  (* HMM is using initWorld good enough? *)
  (* Variable (l : infseq (system_step_descriptor * World)).
  Hypothesis (Htrace : system_trace_coind initWorld l).
  Hypothesis (Hfairness : weak_fairness_delivery (world_trace initWorld l)). *)

  (* probably we can say terminating_convergence is continuous here, 
      but it seems directly proving continuous is difficult? probably by proving all_honest_nodes_confirmed is an invariant *)
  (* to make things fancier, use the leadsto notation *)
  (* TODO in theory, can make everything seem like nice temporal logic formula ... *)
  Lemma eventually_terminating_convergence :
    |== (now (fun w => w = initWorld) ->_
          good_world_trace ->_
          weak_fairness_delivery' ->_
          ((now (all_honest_nodes_submitted v)) ~~> (now all_honest_nodes_confirmed))).
  Proof.
    unfold valid, impl_tl. intros.
    destruct l. unfold now in H. subst w.
    apply good_world_trace_recover in H0. destruct H0 as (ll & Htrace & Heq).
    simpl in *. 

    destruct H0 as (l' & H0). simpl in H0.
    apply always_n_always. intros n Ha.
    rewrite <- recons in Ha. simpl in Ha.
    pose proof Ha as Ha'. apply submit_msgs_all_sent in Ha'.
    2: admit.



    continuously

    submit_msgs_all_sent


    unfold leadsto. 

    apply weak_fairness_deliveryP in H1.

    hnf. intros l.
    apply weak_fairness_deliveryP in Hfairness; auto.
    apply leadsto_trans with (Q:=now honest_submit_all_received).
    - apply always_n_always. intros n Ha.
      rewrite <- recons in Ha. simpl in Ha.
    apply 
    eapply terminating_convergence in Ha.
    



End Proof_of_Terminating_Convergence.

End ACLiveness.
