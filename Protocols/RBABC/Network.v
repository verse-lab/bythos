From Coq Require Import List Lia RelationClasses.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.
From ABCProtocol.Protocols.RBABC Require Export Protocol.
From ABCProtocol.Protocols.ABC Require Import Network.
From ABCProtocol.Protocols.RB Require Import Network.

(* TODO this is inevitable for the refinement proofs, if we require worlds to be strictly equal *)
(* From Coq Require Import FunctionalExtensionality. *)

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
  (TSS : ThresholdSignatureScheme A Sn with Module TSSPrim := TSS0)
  (RBN : RBNetworkType A R V VBFT BTh BSett)
  (ACN : ACNetworkType A Sn V BTh BSett P TSS0 TSS).

Import A R ARP V VBFT BTh BSett P TSS0 TSS.
(*
Module RBN := RBNetwork A R V VBFT BTh BSett.
Module ACN := ACNetwork A Sn V BTh BSett P TSS0 TSS.
*)
(* Existing Instance RBN.Ns.Equivalence_World_rel.
Existing Instance ACN.Ns.Equivalence_World_rel. *)

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
(*
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
*)
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

Local Hint Rewrite -> RBN.PC.In_consume ACN.PC.In_consume In_consume option_map_list_In : psent.

(* the definitions should be sound *)

Fact ssd_proj1_sound q w w' (Hstep : system_step q w w') :
  exists ww, RBN.system_step (ssd_proj1 q) (world_proj1 w) ww /\
    RBN.Ns.World_rel ww (world_proj1 w').
Proof.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj1; simpl_world.
  - eexists. split; [ constructor; reflexivity | ]. reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + eexists. split; [ eapply RBN.DeliverStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * unfold stmap_proj1 at 1.
        pose proof (procMsgWithCheck_proj1 _ _ _ _ _ Ef) as (E1 & E2).
        rewrite -> (surjective_pairing (RBN.RBP.procMsgWithCheck _ _ _)), <- E1, <- E2.
        reflexivity.
      * hnf; simpl. split; [ intros ?; unfold stmap_proj1, upd, RBN.Ns.upd; now destruct_eqdec as_ -> | ].
        hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
        (* TODO cumbersome ... *)
        split.
        --intros [ (a & Hin & Hpj) | [ <- | ((a & Hin & Hpj) & Hneq) ] ].
          ++exists a. autorewrite with psent. tauto.
          ++exists (mkP src dst (inl mRB) true). autorewrite with psent. tauto.
          ++exists a. autorewrite with psent. 
            destruct a as [ ? ? [] ? ]; cbn in Hpj |- *; try discriminate.
            injection Hpj as <-. eqsolve.
        --intros (a & Hin & Hpj). autorewrite with psent in Hin.
          simpl in Hin. destruct Hin as [ Hin | [ <- | (Hin & Hneq) ] ].
          ++eauto.
          ++cbn in Hpj. injection Hpj as <-. auto.
          ++right. right. split; eauto. intros <-. apply Hneq. 
            destruct a as [ ? ? [] ? ]; cbn in Hpj |- *; try discriminate.
            congruence.
    + eexists. split; [ eapply RBN.IdleStep; try reflexivity; simpl; auto | ].
      rewrite -> (surjective_pairing (ACN.ACP.procMsgWithCheck _ _ _)) in Ef.
      revert Ef. intros [= <- <-]. 
      hnf; simpl. split; [ intros ?; unfold stmap_proj1, upd, RBN.Ns.upd; now destruct_eqdec as_ -> | ].
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros (a & Hin & Hpj). exists a. split; auto. 
        autorewrite with psent. right. right. split; auto. intros <-. discriminate.
      * intros (a & Hin & Hpj). exists a. split; auto.
        autorewrite with psent in Hin. destruct Hin as [ (a' & <- & Hin')%in_map_iff | [ <- | (? & ?) ] ]; auto; try discriminate.
  - eexists. split; [ eapply RBN.InternStep; try reflexivity; simpl; auto | ].
    1: rewrite -> (surjective_pairing (RBN.RBP.procInt _ _)); reflexivity.
    unfold stmap_proj1 at 1. unfold procInt in E.
    rewrite -> (surjective_pairing (RBN.RBP.procInt _ _)) in E.
    revert E. intros [= <- <-].
    hnf; simpl. split; [ intros ?; unfold stmap_proj1, upd, RBN.Ns.upd; now destruct_eqdec as_ -> | ].
    hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
    (* TODO cumbersome ... *)
    split.
    + intros [ Hin | (a & Hin & Hpj) ].
      --exists (pkt_inl p). autorewrite with psent. split; [ left; now apply in_map | apply pkt_proj1_refl ].
      --exists a. autorewrite with psent. auto.
    + intros (a & Hin & Hpj). autorewrite with psent in Hin. destruct Hin as [ (p' & <- & Hin')%in_map_iff | Hin ]; eauto.
      apply pkt_proj1_refl_must in Hpj. subst. tauto.
  - destruct m as [ mRB | mAC ]; simpl.
    + eexists. split; [ eapply RBN.ByzStep; try reflexivity; simpl; auto | ].
      simpl. hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros [ <- | (a & Hin & Hpj) ].
        --eexists. autorewrite with psent. split; [ left; reflexivity | ]. reflexivity.
        --exists a. autorewrite with psent. tauto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. destruct Hin as [ <- | Hin ]; eauto.
        cbn in Hpj. injection Hpj as <-. now left.
    + eexists. split; [ eapply RBN.IdleStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
Qed.

Fact ssd_proj2_sound q w w' (Hstep : system_step q w w') :
  exists ww, ACN.system_step (ssd_proj2 q (world_proj1 w) (world_proj1 w')) (world_proj2 w) ww /\
    ACN.Ns.World_rel ww (world_proj2 w').
Proof.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj2; simpl_world.
  - eexists. split; [ constructor; reflexivity | ]. reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1. rewrite upd_refl.
      pose proof (procMsgWithCheck_proj1 _ _ _ _ _ Ef) as (E1 & _).
      rewrite E1. rewrite -> (surjective_pairing (RBN.RBP.procMsgWithCheck _ _ _)) in Ef.
      destruct (triggered _ _) in Ef |- *.
      * eexists. split; [ eapply ACN.InternStep; try reflexivity; simpl; auto | ].
        all: rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)) in Ef.
        1: unfold stmap_proj2 at 1; rewrite -> (surjective_pairing (ACN.ACP.procInt _ _)); reflexivity.
        revert Ef. intros [= <- <-]. 
        hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, ACN.Ns.upd; now destruct_eqdec as_ -> | ].
        hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
        (* TODO cumbersome ... *)
        split.
        --intros [ Hin | (a & Hin & Hpj) ].
          ++exists (pkt_inr p). autorewrite with psent. split; [ left; right; now apply in_map | apply pkt_proj2_refl ].
          ++exists a. autorewrite with psent. split; auto. right. right. split; auto. intros <-. discriminate.
        --intros (a & Hin & Hpj). autorewrite with psent in Hin. 
          destruct Hin as [ [ Hin | Hin ] | [ <- | (Hin & Hneq) ] ]; eauto.
          all: apply in_map_iff in Hin; destruct Hin as (a' & <- & Hin'); try discriminate.
          apply pkt_proj2_refl_must in Hpj. subst. tauto.
      * eexists. split; [ eapply ACN.IdleStep; try reflexivity; simpl; auto | ].
        revert Ef. intros [= <- <-].
        hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, ACN.Ns.upd; now destruct_eqdec as_ -> | ].
        hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
        (* TODO cumbersome ... *)
        split.
        --intros (a & Hin & Hpj). exists a. autorewrite with psent. split; auto. right. right. split; auto. intros <-. discriminate.
        --intros (a & Hin & Hpj). autorewrite with psent in Hin. 
          destruct Hin as [ (a' & <- & Hin')%in_map_iff | [ <- | (Hin & Hneq) ] ]; eauto.
    + eexists. split; [ eapply ACN.DeliverStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * unfold stmap_proj2 at 1.
        pose proof (procMsgWithCheck_proj2 _ _ _ _ _ Ef) as (E1 & E2).
        rewrite -> (surjective_pairing (ACN.ACP.procMsgWithCheck _ _ _)), <- E1, <- E2.
        reflexivity.
      * hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, ACN.Ns.upd; now destruct_eqdec as_ -> | ].
        hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
        (* TODO cumbersome ... *)
        (* TODO repeating some proof above *)
        split.
        --intros [ (a & Hin & Hpj) | [ <- | ((a & Hin & Hpj) & Hneq) ] ].
          ++exists a. autorewrite with psent. tauto.
          ++exists (mkP src dst (inr mAC) true). autorewrite with psent. tauto.
          ++exists a. autorewrite with psent. 
            destruct a as [ ? ? [] ? ]; cbn in Hpj |- *; try discriminate.
            injection Hpj as <-. eqsolve.
        --intros (a & Hin & Hpj). autorewrite with psent in Hin.
          simpl in Hin. destruct Hin as [ Hin | [ <- | (Hin & Hneq) ] ].
          ++eauto.
          ++cbn in Hpj. injection Hpj as <-. auto.
          ++right. right. split; eauto. intros <-. apply Hneq. 
            destruct a as [ ? ? [] ? ]; cbn in Hpj |- *; try discriminate.
            congruence.
  - eexists. split; [ eapply ACN.IdleStep; try reflexivity; simpl; auto | ].
    unfold procInt in E. 
    rewrite -> (surjective_pairing (RBN.RBP.procInt _ _)) in E.
    revert E. intros [= <- <-].
    hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, ACN.Ns.upd; now destruct_eqdec as_ -> | ].
    hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
    (* TODO cumbersome ... *)
    split.
    + intros (a & Hin & Hpj). exists a. autorewrite with psent. auto.
    + intros (a & Hin & Hpj). autorewrite with psent in Hin. 
      destruct Hin as [ (a' & <- & Hin')%in_map_iff | ? ]; eauto. discriminate.
  - (* TODO repeating the proof above *)
    destruct m as [ mRB | mAC ]; simpl.
    + eexists. split; [ eapply ACN.IdleStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
    + eexists. split; [ eapply ACN.ByzStep; try reflexivity; simpl; auto | ].
      simpl. hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros [ <- | (a & Hin & Hpj) ].
        --eexists. autorewrite with psent. split; [ left; reflexivity | ]. reflexivity.
        --exists a. autorewrite with psent. tauto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. destruct Hin as [ <- | Hin ]; eauto.
        cbn in Hpj. injection Hpj as <-. now left.
Qed.

End RBACNetwork.
