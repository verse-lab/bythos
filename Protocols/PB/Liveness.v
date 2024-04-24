From Coq Require Import List Bool Lia PeanoNat ListSet Permutation RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Protocols.PB Require Export Safety.

From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import tactics. (* anyway *)

Module PBLiveness (A : NetAddr) (R : PBTag) (Sn : Signable) (V : Value Sn) (Pf : PBProof Sn) (VBFT : ValueBFT A R Sn V Pf) 
  (BTh : ClassicByzThreshold A) (BSett : RestrictedByzSetting A BTh)
  (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (PBDT : PBDataTypes A R Sn V Pf TSS).

Import A R V Pf VBFT BTh BSett TSS PBDT.
Import ssrbool. (* anyway *)

Module Export PBS := PBSafety A R Sn V Pf VBFT BTh BSett TSS0 TSS PBDT.

Set Implicit Arguments. (* anyway *)

Definition all_echoes src r w : Prop := forall n, is_byz n = false -> (w @ n).(echoed) (src, r) = Some (value_bft src r).

(* TODO make this reusable *)
Create HintDb booldec.

Fact is_left_unfold [A B : Prop] (b : {A} + {B}) : is_left b = if b then true else false.
Proof eq_refl.

Hint Rewrite -> is_left_unfold sumbool_is_left sumbool_is_right andb_true_iff negb_true_iff @eqdec_refl : booldec.

Module Termination.

Section Proof_of_Termination.

  Variables (src : Address) (r : Round).
  Hypothesis (Hnonbyz_src : is_byz src = false) (Hex : ex_validate r (value_bft src r).1 (value_bft src r).2).

  (* TODO template based on Proof_of_Validity, Round1 *)
  Section Round1.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : (w @ src).(sent) r).

  Let initmsg_in n used := In (mkP src n (InitMsg r (value_bft src r).1 (value_bft src r).2) used).

  Definition pkts_needed_in_round_1 pkts : Prop := Eval unfold initmsg_in in
    incl pkts (sentMsgs w) /\
    Forall good_packet pkts /\ (* since pkts is under-specified *)
    (forall n, is_byz n = false ->
      exists used, initmsg_in n used pkts).

  Lemma round_1_pkts : exists pkts, pkts_needed_in_round_1 pkts.
  Proof.
    unfold pkts_needed_in_round_1. saturate.
    exists (List.filter (fun p =>
      (Message_eqdec p.(msg) (InitMsg r (value_bft src r).1 (value_bft src r).2)) &&
      (Address_eqdec (P0.src p) src) && (negb (is_byz p.(dst)))) (sentMsgs w)).
    split_and?; auto using incl_filter.
    - apply Forall_forall. intros [ s d m b ] (Hin & Hcheck)%filter_In. simpl in Hcheck. 
      autorewrite with booldec in Hcheck. hnf. simpl. eqsolve.
    - intros n Hnonbyz_n.
      pick initmsg_sent_l2h as_ H1 by_ (pose proof (Hl2h _ Hnonbyz_src) as []). saturate_assumptions!. rewrite Hcoh in H1.
      destruct H1 as (b & H1). exists b. rewrite filter_In. simpl. now autorewrite with booldec.
  Qed.

  Variable (pkts : list Packet).
  Hypotheses (Hround1 : pkts_needed_in_round_1 pkts).

  Definition round_1_end w' := Eval unfold initmsg_in in
    forall n, is_byz n = false -> initmsg_in n true (sentMsgs w').

  Fact round_1_end_suffcond w' (Hincl : incl (map receive_pkt pkts) (sentMsgs w')) :
    round_1_end w'.
  Proof.
    destruct Hround1 as (_ & _ & H2). 
    hnf. intros n Hnonbyz_n. specialize (H2 _ Hnonbyz_n).
    destruct H2 as (? & H2). now apply (in_map receive_pkt), Hincl in H2.
  Qed.

  Lemma round_2_start_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_1_end w0) : all_echoes src r w0.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0 |- *. intros n Hnonbyz_n. specialize (Hw0 _ Hnonbyz_n).
    pick initmsg_recv_h2l as_ Hp by_ (pose proof (Hh2l _ Hw0) as []). saturate_assumptions.
    destruct (echoed (w0 @ n) (src, r)) as [ vpf | ] eqn:E; try discriminate.
    apply echoed_backtrack_always_holds in E; auto. congruence.
  Qed.

  End Round1.

  Section Round2.

  Variable (w : World).
  Hypotheses (H_w_reachable : reachable w) (Hstart : all_echoes src r w).

  Let echomsg_in n used := In (mkP n src (EchoMsg r (light_sign (r, (value_bft src r).1) (lightkey_map n))) used).

  Definition pkts_needed_in_round_2 pkts : Prop := Eval unfold echomsg_in in
    incl pkts (sentMsgs w) /\
    Forall good_packet pkts /\ (* since pkts is under-specified *)
    (forall n, is_byz n = false ->
      exists used, echomsg_in n used pkts).

  Lemma round_2_pkts : exists pkts, pkts_needed_in_round_2 pkts.
  Proof.
    unfold pkts_needed_in_round_2. saturate.
    exists (List.filter (fun p => 
      match p.(msg) with
      | EchoMsg _ _ => (negb (is_byz (P0.src p))) && (negb (is_byz p.(dst)))
      | _ => false
      end) (sentMsgs w)).
    split_and?; auto using incl_filter.
    - apply Forall_forall. intros [ s d [] b ] (Hin & Hcheck)%filter_In; try discriminate. simpl in Hcheck. 
      now autorewrite with booldec in Hcheck.
    - intros n Hnonbyz_n. pose proof (Hstart Hnonbyz_n) as HH. rewrite (surjective_pairing (value_bft _ _)) in HH.
      pick echomsg_sent_l2h as_ H1 by_ (pose proof (Hl2h _ Hnonbyz_n) as []). specialize (H1 _ _ _ _ HH). rewrite Hcoh in H1.
      destruct H1 as (b & H1). exists b. rewrite filter_In. simpl. now autorewrite with booldec.
  Qed.

  Variable (pkts : list Packet).
  Hypotheses (Hround2 : pkts_needed_in_round_2 pkts).

  Definition round_2_end w' := Eval unfold echomsg_in in
    forall n, is_byz n = false -> echomsg_in n true (sentMsgs w').

  Fact round_2_end_suffcond w' (Hincl : incl (map receive_pkt pkts) (sentMsgs w')) :
    round_2_end w'.
  Proof.
    destruct Hround2 as (_ & _ & H2). 
    hnf. intros n Hnonbyz_n. specialize (H2 _ Hnonbyz_n).
    destruct H2 as (? & H2). now apply (in_map receive_pkt), Hincl in H2.
  Qed.

  Lemma src_outputs_suffcond w0 l0 (Htrace0 : system_trace w l0) (Ew0 : w0 = final_world w l0) 
    (Hw0 : round_2_end w0) : (w0 @ src).(output) r.
  Proof.
    pose proof (reachable_by_trace Htrace0 H_w_reachable) as H_w0_reachable. rewrite <- Ew0 in H_w0_reachable.
    clear H_w_reachable. saturate.

    hnf in Hw0. destruct (output _ _) eqn:E; auto.
    pick output_none as_ H1 by_ (pose proof (Hst src) as []). saturate_assumptions! in_ H1.
    (* prove contradiction using the message size *)
    assert (incl (List.filter (fun n => negb (is_byz n)) valid_nodes) (map fst ((w0 @ src).(counter) r))) as Hincl.
    { hnf. intros n1 Hnonbyz_n1%is_nonbyz_synonym. specialize (Hw0 _ Hnonbyz_n1).
      pick echomsg_recv_h2l as_ H2 by_ (pose proof (Hh2l _ Hw0) as []). saturate_assumptions. destruct H2 as [ | H2 ]; auto. 
      specialize (H2 ltac:(assumption) ltac:(now apply lightkey_correct)). now apply (in_map fst) in H2. }
    apply NoDup_incl_length in Hincl; auto using NoDup_filter, valid_nodes_NoDup. 
    unfold th_output in H1. rewrite map_length in Hincl. pose proof nonbyz_lower_bound. lia.
  Qed.

  End Round2.

End Proof_of_Termination.

End Termination.

End PBLiveness.
