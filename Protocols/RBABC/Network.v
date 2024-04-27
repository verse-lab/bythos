From Coq Require Import List Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.RBABC Require Export Protocol.
From ABCProtocol.Protocols.ABC Require Import Network.
From ABCProtocol.Protocols.RB Require Import Network.

(* TODO this is inevitable for the refinement proofs, if we require worlds to be strictly equal *)
From Coq Require Import FunctionalExtensionality.

Module RBACAdversary (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (RBM : RBMessage A R V)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (ACDT : ACDataTypes A Sn V P TSS) 
  (CC : CertCheckers A Sn V P TSS ACDT) (ACM : ACMessage A Sn V P TSS ACDT)
  (M : RBACMessage A R Sn V P TSS ACDT RBM ACM)
  (RBPk : SimplePacket A RBM) (ACPk : SimplePacket A ACM) 
  (RBP : RBProtocol A R V VBFT BTh RBM RBPk)
  (ACP : ACProtocol A Sn V BTh P TSS0 TSS ACDT CC ACM ACPk)
  (Pk : SimplePacket A M)
  (RBACP : RBACProtocol A R ARP Sn V VBFT BTh RBM P TSS0 TSS ACDT CC ACM M RBPk ACPk RBP ACP Pk)
  (RBNs : NetState A RBM RBPk BTh RBP) (ACNs : NetState A ACM ACPk BTh ACP) 
  (Ns : NetState A M Pk BTh RBACP) <: Adversary A M BTh BSett Pk RBACP Ns.

Import A R ARP V VBFT BTh P TSS0 TSS ACDT CC M Pk RBACP Ns.

(* instantiate inside *)
Module ACAdv := ACAdversary A Sn V BTh BSett P TSS0 TSS ACDT CC ACM ACPk ACP ACNs.

Definition byz_constraints (m : Message) (w : World) : Prop :=
  match m with
  | inl mRB => True
  | inr mAC => ACAdv.byz_constraints mAC (ACNs.mkW (ACNs.localState ACNs.initWorld) (* this part does not contribute *)
    (pkts_filter_proj2 (sentMsgs w)))
  end.

End RBACAdversary.

Module RBACNetwork (A : NetAddr) (R : Round) (ARP : AddrRoundPair A R) (Sn : Signable) (V : SignableValue Sn) (VBFT : ValueBFT A R V) 
  (BTh : ClassicByzThreshold A) (BSett : ByzSetting A)
  (P : PKI A Sn) (TSS0 : ThresholdSignatureSchemePrim A Sn with Definition thres := BTh.t0) (* ! *)
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0).

Import A R ARP V VBFT BTh BSett P TSS0 TSS.

Module RBN := RBNetwork A R V VBFT BTh BSett.
Module ACN := ACNetwork A Sn V BTh BSett P TSS0 TSS.

Module Export M <: MessageType := RBACMessageImpl A R Sn V P TSS ACN.ACDT RBN.M ACN.M.
Module Export Pk <: SimplePacket A M := SimplePacketImpl A M.
Module Export PSOp : (* hide implementation *) PacketSoupOperations Pk := PacketSoupOperationsImpl Pk.
Module Export RBACP <: Protocol A M Pk BTh
  <: RBACProtocol A R ARP Sn V VBFT BTh RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk
  := RBACProtocolImpl A R ARP Sn V VBFT BTh RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk.
Module Export Ns <: NetState A M Pk BTh RBACP := NetStateImpl A M Pk BTh RBACP.
Module Export RBACAdv <: Adversary A M BTh BSett Pk RBACP Ns :=
  RBACAdversary A R ARP Sn V VBFT BTh BSett RBN.M P TSS0 TSS ACN.ACDT ACN.CC ACN.M M RBN.P ACN.P0 RBN.RBP ACN.ACP Pk
    RBACP RBN.Ns ACN.Ns Ns.

Include NetworkImpl A M BTh BSett Pk PSOp RBACP Ns RBACAdv.

(* auxiliary operations *)
Definition stmap_proj1 (stmap : StateMap) : RBN.Ns.StateMap :=
  fun n => (stmap n).(stRB).

Definition stmap_proj2 (stmap : StateMap) : ACN.Ns.StateMap :=
  fun n => (stmap n).(stAC).

Definition world_proj1 (w : World) : RBN.Ns.World :=
  RBN.Ns.mkW (stmap_proj1 (localState w)) (pkts_filter_proj1 (sentMsgs w)).

Definition world_proj2 (w : World) : ACN.Ns.World :=
  ACN.Ns.mkW (stmap_proj2 (localState w)) (pkts_filter_proj2 (sentMsgs w)).

Definition ssd_proj1 (q : system_step_descriptor) : RBN.system_step_descriptor :=
  match q with
  | Idle => RBN.Idle
  | Deliver p =>
    match pkt_proj1 p with
    | Some res => RBN.Deliver res
    | _ => RBN.Idle
    end
  | Intern n r => RBN.Intern n r
  | Byz src dst m =>
    match m with
    | inl mRB => RBN.Byz src dst mRB
    | _ => RBN.Idle
    end
  end.

(* depending on the previous protocol *)
Definition ssd_proj2 (q : system_step_descriptor) (w w' : RBN.Ns.World) : ACN.system_step_descriptor :=
  match q with
  | Idle => ACN.Idle
  | Deliver p =>
    match pkt_proj2 p with
    | Some res => ACN.Deliver res
    | _ =>
      (* HMM *)
      let: n := p.(dst) in
      match triggered (RBN.Ns.localState w n) (RBN.Ns.localState w' n) with
      | Some v => ACN.Intern n (ACN.ACP.SubmitIntTrans v)
      | _ => ACN.Idle
      end
    end
  | Intern _ _ => ACN.Idle
  | Byz src dst m =>
    match m with
    | inr mAC => ACN.Byz src dst mAC
    | _ => ACN.Idle
    end
  end.

Fact stmap_proj1_upd stmap n st :
  stmap_proj1 (upd n st stmap) = RBN.Ns.upd n st.(stRB) (stmap_proj1 stmap).
Proof.
  unfold stmap_proj1. apply functional_extensionality. (* !!!!!!!! *) 
  intros ?. unfold upd, RBN.Ns.upd. now destruct_eqdec as_ ?.
Qed.

Fact stmap_proj2_upd stmap n st :
  stmap_proj2 (upd n st stmap) = ACN.Ns.upd n st.(stAC) (stmap_proj2 stmap).
Proof.
  unfold stmap_proj2. apply functional_extensionality. (* !!!!!!!! *) 
  intros ?. unfold upd, ACN.Ns.upd. now destruct_eqdec as_ ?.
Qed.

Fact pkts_filter_proj1_all pktsRB : pkts_filter_proj1 (map pkt_inl pktsRB) = pktsRB.
Proof. induction pktsRB; simpl; auto. destruct a. simpl. congruence. Qed.

Fact pkts_filter_proj1_no pktsAC : pkts_filter_proj1 (map pkt_inr pktsAC) = nil.
Proof. induction pktsAC; simpl; auto. Qed.

Fact pkts_filter_proj2_all pktsAC : pkts_filter_proj2 (map pkt_inr pktsAC) = pktsAC.
Proof. induction pktsAC; simpl; auto. destruct a. simpl. congruence. Qed.

Fact pkts_filter_proj2_no pktsRB : pkts_filter_proj2 (map pkt_inl pktsRB) = nil.
Proof. induction pktsRB; simpl; auto. Qed.

Fact pkts_filter_proj1_app l1 l2 : pkts_filter_proj1 (l1 ++ l2) = pkts_filter_proj1 l1 ++ pkts_filter_proj1 l2.
Proof. apply flat_map_app. Qed. 

Create HintDb pkts_filter.

Hint Rewrite -> pkts_filter_proj1_all pkts_filter_proj1_no pkts_filter_proj2_all pkts_filter_proj2_no
  pkts_filter_proj1_app app_nil_r : pkts_filter.

(* TODO are the proofs below repeating? *)
Fact procMsgWithCheck_proj1 st src mRB : forall st' pkts,
  procMsgWithCheck st src (inl mRB) = (st', pkts) ->
  let: res := RBN.RBP.procMsgWithCheck st.(stRB) src mRB in
  st'.(stRB) = fst res /\ pkts_filter_proj1 pkts = snd res.
Proof.
  intros st' pkts E. simpl in E.
  rewrite -> (surjective_pairing (RBN.RBP.procMsgWithCheck _ _ _)) in E.
  destruct (triggered _ _) in E.
  1: rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in E.
  all: revert E; intros [= <- <-]. (* TODO why simplify_eq does not work here? *)
  all: simpl; now autorewrite with pkts_filter.
Qed.

Fact procMsgWithCheck_proj2 st src mAC : forall st' pkts,
  procMsgWithCheck st src (inr mAC) = (st', pkts) ->
  let: res := ACN.ACP.procMsgWithCheck st.(stAC) src mAC in
  st'.(stAC) = fst res /\ pkts_filter_proj2 pkts = snd res.
Proof.
  intros st' pkts E. simpl in E.
  rewrite -> (surjective_pairing (ACN.ACP.procMsgWithCheck _ _ _)) in E.
  revert E; intros [= <- <-].
  simpl; now autorewrite with pkts_filter.
Qed.

(* the definitions should be sound *)
Fact ssd_proj1_sound q w w' (Hstep : system_step q w w') :
  RBN.system_step (ssd_proj1 q) (world_proj1 w) (world_proj1 w').
Proof.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj1; simpl_world; rewrite ?stmap_proj1_upd. 
  - constructor; eauto.
  - destruct msg as [ mRB | mAC ]; simpl.
    + eapply RBN.DeliverStep; try reflexivity; simpl; auto.
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * unfold stmap_proj1 at 1.
        pose proof (procMsgWithCheck_proj1 _ _ _ _ _ Ef) as (E1 & E2).
        rewrite -> (surjective_pairing (RBN.RBP.procMsgWithCheck _ _ _)), <- E1, <- E2.
        f_equal. admit.
    + eapply RBN.IdleStep; try reflexivity; simpl; auto.
      rewrite -> (surjective_pairing (ACN.ACP.procMsgWithCheck _ _ _)) in Ef.
      revert Ef. intros [= <- <-]. simpl. f_equal.
      * apply functional_extensionality. (* !!!!!!!! *) 
        intros ?. unfold stmap_proj1, RBN.Ns.upd. now destruct_eqdec as_ ->.
      * admit.
  - eapply RBN.InternStep; try reflexivity; simpl; auto.
    unfold stmap_proj1 at 1. unfold procInt in E. 
    rewrite -> (surjective_pairing (RBN.RBP.procInt _ _)) in E |- *.
    revert E. intros [= <- <-]. simpl. f_equal.
    admit.
  - unfold world_proj1. simpl_world.
    destruct m as [ mRB | mAC ]; simpl.
    + eapply RBN.ByzStep; try reflexivity; simpl; auto.
      f_equal. admit.
    + eapply RBN.IdleStep; try reflexivity; simpl; auto.
      f_equal. admit.
Admitted.

Fact ssd_proj2_sound q w w' (Hstep : system_step q w w') :
  ACN.system_step (ssd_proj2 q (world_proj1 w) (world_proj1 w')) (world_proj2 w) (world_proj2 w').
Proof.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj2; simpl_world; rewrite ?stmap_proj2_upd. 
  - constructor; eauto.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1. rewrite upd_refl.
      pose proof (procMsgWithCheck_proj1 _ _ _ _ _ Ef) as (E1 & _).
      rewrite E1. rewrite -> (surjective_pairing (RBN.RBP.procMsgWithCheck _ _ _)) in Ef.
      destruct (triggered _ _) in Ef |- *.
      * eapply ACN.InternStep; try reflexivity; simpl; auto.
        unfold stmap_proj2 at 1. 
        rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in Ef |- *.
        revert Ef. intros [= <- <-]. simpl. f_equal.
        admit.
      * eapply ACN.IdleStep; try reflexivity; simpl; auto.
        revert Ef. intros [= <- <-]. simpl. f_equal.
        --apply functional_extensionality. (* !!!!!!!! *) 
          intros ?. unfold stmap_proj2, ACN.Ns.upd. now destruct_eqdec as_ ->.
        --admit.
    + eapply ACN.DeliverStep; try reflexivity; simpl; auto.
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * unfold stmap_proj2 at 1.
        pose proof (procMsgWithCheck_proj2 _ _ _ _ _ Ef) as (E1 & E2).
        rewrite -> (surjective_pairing (ACN.ACP.procMsgWithCheck _ _ _)), <- E1, <- E2.
        f_equal. admit.
  - eapply ACN.IdleStep; try reflexivity; simpl; auto.
    unfold procInt in E. 
    rewrite -> (surjective_pairing (RBN.RBP.procInt _ _)) in E.
    revert E. intros [= <- <-]. simpl. f_equal.
    + apply functional_extensionality. (* !!!!!!!! *) 
      intros ?. unfold stmap_proj2, ACN.Ns.upd. now destruct_eqdec as_ ->.
    + admit.
  - unfold world_proj2. simpl_world.
    destruct m as [ mRB | mAC ]; simpl.
    + eapply ACN.IdleStep; try reflexivity; simpl; auto.
      f_equal. admit.
    + eapply ACN.ByzStep; try reflexivity; simpl; auto.
      f_equal. admit.
Admitted.

End RBACNetwork.
