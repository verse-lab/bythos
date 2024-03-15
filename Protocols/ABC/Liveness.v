From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.ABC Require Export Safety.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module ACLiveness (A : NetAddr) (V : Signable) (VBFT : ValueBFT A V) 
  (BTh : ByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A V) (TSS : ThresholdSignatureScheme A V with Definition thres := BTh.t0).

Import A V VBFT BTh BSett P TSS.
Import ssrbool. (* anyway *)

Module Export ACS := ACSafety A V VBFT BTh BSett P TSS.

Definition pkts_needed size w nonbyz_senders pkts (m : Address -> Message) (P : World -> Address -> Prop) : Prop :=
  List.NoDup nonbyz_senders /\
  size <= length nonbyz_senders /\
  incl pkts (sentMsgs w) /\
  Forall good_packet pkts /\ (* since pkts is under-specified *)
  (forall n1,
    In n1 nonbyz_senders -> 
    is_byz n1 = false /\
    P w n1 /\
    (forall n2, is_byz n2 = false ->
      exists used, In (mkP n1 n2 (m n1) used) pkts)).

Definition mutual_receiving m w' :=
  forall n1, is_byz n1 = false ->
    forall n2, is_byz n2 = false ->
      In (mkP n1 n2 (m n1) true) (sentMsgs w').

Module Terminating_Convergence.

(* start *)
Definition all_honest_nodes_submitted v w := forall n, is_byz n = false -> (w @ n).(submitted_value) = Some v.

(* end *)
Definition all_honest_nodes_confirmed v w := forall n, is_byz n = false -> (w @ n).(conf) /\ (w @ n).(submitted_value) = Some v.
(*
Fact all_honest_nodes_submitted_is_invariant v :
  is_invariant_reachable_step (all_honest_nodes_submitted v).
Proof.
  hnf. intros ??? Hr H Hstep.
  hnf in H |- *. intros n Hnonbyz. saturate_assumptions!.
  eapply persistent_invariants in Hstep; eauto. 
  pick submitted_value_persistent as_ Htmp by_ (pose proof (Hstep n) as []). now apply Htmp.
Qed.
*)
Section Proof_of_Terminating_Convergence.

  Variables (v : Value).

  Hypothesis (H_byz_minor : num_byz <= t0).

  Let submitted_v w n : Prop := (w @ n).(submitted_value) = Some v.
  Let valid_submitmsg n : Message := let: vv := value_bft n in
    (SubmitMsg vv (light_sign vv (lightkey_map n)) (sign vv (key_map n))).

  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : all_honest_nodes_submitted v w).

  Definition pkts_needed_in_round_1 nonbyz_senders pkts :=
    pkts_needed (N - t0) w nonbyz_senders pkts valid_submitmsg submitted_v.

  Let nonbyz_senders := (List.filter (fun n => negb (is_byz n)) valid_nodes).

  Lemma round_1_pkts :
    exists pkts, pkts_needed_in_round_1 nonbyz_senders pkts.
  Proof.
    unfold pkts_needed_in_round_1, nonbyz_senders. saturate.
    exists (List.filter (fun p => 
      match p.(msg) with
      | SubmitMsg _ _ _ =>
        (negb (is_byz p.(src))) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)).
    hnf. split_and?; auto using incl_filter, NoDup_filter, valid_nodes_NoDup.
    - pose proof (filter_nonbyz_lower_bound valid_nodes_NoDup). unfold N. lia.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; simpl in Hcheck; try discriminate.
      now rewrite andb_true_iff, !negb_true_iff in Hcheck.
    - intros n1 Hin1_backup.
      pose proof Hin1_backup as Hnonbyz_n1%is_nonbyz_synonym. pose proof Hnonbyz_n1 as Hv%Hstart. split_and?; auto.
      intros n2 Hnonbyz_n2.
      pick inv_submitted_broadcast as_ Hbc by_ (pose proof (Hl2h _ Hnonbyz_n1) as []). saturate_assumptions!. 
      pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst n1) as []). rewrite Hv in Htmp. destruct Htmp as (-> & ? & ?). 
      rewrite Hcoh in Hbc. destruct Hbc as (b & Hbc). exists b. apply filter_In. 
      simpl. now rewrite andb_true_iff, !negb_true_iff. 
  Qed.

  (* universally quantified *)
  Variable (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 nonbyz_senders pkts).

  Definition round_1_end w' :=
    Eval unfold mutual_receiving in mutual_receiving valid_submitmsg w'.

  Fact round_1_end_suffcond w' (Hincl : incl (map receive_pkt pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    (* FIXME: can this be automated? *)
    hnf in Hround1. unfold valid_submitmsg in Hround1. 
    pick SubmitMsg as_ HH by_ (destruct_and? Hround1).
    hnf. intros n1 Hnonbyz_n1%is_nonbyz_synonym n2 Hnonbyz_n2.
    saturate_assumptions!. destruct HH as (_ & _ & HH). saturate_assumptions!. 
    destruct HH as (? & HH). now apply (in_map receive_pkt), Hincl in HH.
  Qed.

  Lemma all_honest_nodes_confirmed_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : all_honest_nodes_confirmed v w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    (* clear H_w_reachable. *) saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n.
    (* need to use persistence here to know buffer = nil *)
    apply persistent_invariants_trace in Htrace0; auto. 
    pick submitted_value_persistent as_ Hvv by_ (pose proof (Htrace0 n) as []). rewrite <- Ew0 in Hvv.
    pose proof (Hstart _ Hnonbyz_n) as Hvn. saturate_assumptions! in_ Hvv.
    split; auto. destruct (conf (w0 @ n)) eqn:Ec; auto.
    (* TODO this step is repeating? *)
    pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst n) as []). rewrite Hvv, Hcoh in Htmp. destruct Htmp as (Ev & _ & _). 
    assert (incl nonbyz_senders (w0 @ n).(from_set)) as Hincl.
    { hnf. intros nn Hnonbyz_nn%is_nonbyz_synonym. specialize (Hw0 _ Hnonbyz_nn n Hnonbyz_n).
      (* need to unify (value_bft nn) with v *)
      (* TODO this step is repeating! *)
      pick submitted_value_persistent as_ Hvv' by_ (pose proof (Htrace0 nn) as []). rewrite <- Ew0 in Hvv'.
      pose proof (Hstart _ Hnonbyz_nn) as Hvn'. saturate_assumptions! in_ Hvv'.
      pick inv_submit_mixin as_ Htmp by_ (pose proof (Hst nn) as []). rewrite Hvv', Hcoh in Htmp. destruct Htmp as (Ev' & _ & _). 
      pick inv_submitmsg_receive as_ Htmp by_ (pose proof (Hh2l _ Hw0) as []). 
      unfold valid_submitmsg, inv_submitmsg_receive_ in Htmp. simpl in Htmp. rewrite Hvv, Ev' in Htmp.
      (* FIXME: maybe use ABCinv below? *)
      apply Htmp; auto using correct_sign_verify_ok, correct_sign_verify_ok_light. }
    unfold nonbyz_senders in Hincl. 
    apply NoDup_incl_length in Hincl; auto using NoDup_filter, valid_nodes_NoDup.
    pose proof (filter_nonbyz_lower_bound valid_nodes_NoDup).
    pick inv_conf_correct as_ Htmp by_ (pose proof (Hst n) as []). unfold N in Htmp. rewrite Ec in Htmp. lia.  
  Qed.

  End Round1.

End Proof_of_Terminating_Convergence.

End Terminating_Convergence.

End ACLiveness.
