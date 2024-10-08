From Coq Require Import List Bool Lia PeanoNat.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.
From Bythos.Composition Require Export States.

(* FIXME: is using the Adv of each sub-protocol really good? may introduce some problems? *)
Module Type SimpleCompAdv (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh)
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  (CPt : SeqCompProtocol A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT)
  (Ns1 : NetState A M1 Pk1 BTh Pt1) (Ns2 : NetState A M2 Pk2 BTh Pt2)
  (CNs : CompNetState A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT Ns1 Ns2 CPt)
  (BSett : ByzSetting A)
  (Adv1 : Adversary A M1 BTh BSett Pk1 Pt1 Ns1) (Adv2 : Adversary A M2 BTh BSett Pk2 Pt2 Ns2) <: Adversary A CM BTh BSett CPk CPt CNs.

Import CNs.

Definition byzConstraints m w :=
  match m with
  | inl m1 => Adv1.byzConstraints m1 (sysstate_proj1 w)
  | inr m2 => Adv2.byzConstraints m2 (sysstate_proj2 w)
  end.

End SimpleCompAdv.

Module Type CompNetwork (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (CM : CompMessage M1 M2) (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (CPk : CompSimplePacket A M1 M2 CM Pk1 Pk2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh)
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  (CPt : SeqCompProtocol A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT)
  (Ns1 : NetState A M1 Pk1 BTh Pt1) (Ns2 : NetState A M2 Pk2 BTh Pt2)
  (CNs : CompNetState A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT Ns1 Ns2 CPt)
  (BSett : ByzSetting A)
  (Adv1 : Adversary A M1 BTh BSett Pk1 Pt1 Ns1) (Adv2 : Adversary A M2 BTh BSett Pk2 Pt2 Ns2)
  (CAdv : SimpleCompAdv A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT CPt Ns1 Ns2 CNs BSett Adv1 Adv2)
  (N1 : Network.Network A M1 BTh BSett Pk1 Pt1 Ns1 Adv1)
  (N2 : Network.Network A M2 BTh BSett Pk2 Pt2 Ns2 Adv2) <: Network.Network A CM BTh BSett CPk CPt CNs CAdv.

Import BTh SCPT.

Include NetworkImpl A CM BTh BSett CPk CPt CNs CAdv.

Definition tag_proj1 (q : system_step_tag) : N1.system_step_tag :=
  match q with
  | Stuttering => N1.Stuttering
  | Delivery p =>
    match pkt_proj1 p with
    | Some res => N1.Delivery res
    | _ => N1.Stuttering
    end
  | Internal n r => N1.Internal n r
  | Byzantine src dst m =>
    match m with
    | inl m1 => N1.Byzantine src dst m1
    | _ => N1.Stuttering
    end
  end.

(* depending on the previous protocol *)
Definition tag_proj2 (q : system_step_tag) (w w' : Ns1.SystemState) : N2.system_step_tag :=
  match q with
  | Stuttering => N2.Stuttering
  | Delivery p =>
    match pkt_proj2 p with
    | Some res => N2.Delivery res
    | _ =>
      let: n := p.(dst) in
      match trigger_procMsg (Ns1.localState w n) (Ns1.localState w' n) with
      | Some tr2 => N2.Internal n tr2
      | _ => N2.Stuttering
      end
    end
  | Internal n _ =>
    match trigger_procInt (Ns1.localState w n) (Ns1.localState w' n) with
    | Some tr2 => N2.Internal n tr2
    | _ => N2.Stuttering
    end
  | Byzantine src dst m =>
    match m with
    | inr mAC => N2.Byzantine src dst mAC
    | _ => N2.Stuttering
    end
  end.

Local Set Implicit Arguments.

Local Hint Rewrite -> N1.PC.In_consume N2.PC.In_consume In_consume option_map_list_In : psent.

(* the definitions should be sound *)

Fact tag_proj1_sound q w :
  let: ww := N1.next_sysstate (tag_proj1 q) (sysstate_proj1 w) in
  forall w' (Hstep : system_step q w w'),
    N1.system_step (tag_proj1 q) (sysstate_proj1 w) ww /\
    Ns1.SystemState_rel ww (sysstate_proj1 w').
Proof.
  intros w' Hstep.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold sysstate_proj1; simpl_sysstate.
  - split; [ constructor | ]; reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1.
      rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)).
      split; [ eapply N1.DeliveryStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)). reflexivity.
      * pose proof (procMsg_proj1 Ef) as (E1 & E2). rewrite <- E1, <- E2.
        hnf; simpl. split; [ intros ?; unfold upd, Ns1.upd; now destruct_eqdec as_ -> | ].
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
    + split; [ eapply N1.StutteringStep; try reflexivity; simpl; auto | ].
      rewrite -> (surjective_pairing (Pt2.procMsg _ _ _)) in Ef.
      revert Ef. intros [= <- <-]. 
      hnf; simpl. split; [ intros ?; unfold stmap_proj1, upd, Ns1.upd; now destruct_eqdec as_ -> | ].
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros (a & Hin & Hpj). exists a. split; auto. 
        autorewrite with psent. right. right. split; auto. intros <-. discriminate.
      * intros (a & Hin & Hpj). exists a. split; auto.
        autorewrite with psent in Hin. destruct Hin as [ (a' & <- & Hin')%in_map_iff | [ <- | (? & ?) ] ]; auto; try discriminate.
  - unfold stmap_proj1. unfold procInt in E.
    rewrite -> (surjective_pairing (Pt1.procInt _ _)).
    split; [ eapply N1.InternalStep; try reflexivity; simpl; auto | ].
    1: rewrite -> (surjective_pairing (Pt1.procInt _ _)); reflexivity.
    pose proof (procInt_proj1 E) as (E1 & E2). rewrite <- E1, <- E2.
    hnf; simpl. split; [ intros ?; unfold upd, Ns1.upd; now destruct_eqdec as_ -> | ].
    hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
    (* ...? *)
    setoid_rewrite In_sendout. firstorder.
  - destruct m as [ mRB | mAC ]; simpl.
    + split; [ eapply N1.ByzantineStep; try reflexivity; simpl; auto | ].
      simpl. hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros [ <- | (a & Hin & Hpj) ].
        --eexists. autorewrite with psent. split; [ left; reflexivity | ]. reflexivity.
        --exists a. autorewrite with psent. tauto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. destruct Hin as [ <- | Hin ]; eauto.
        cbn in Hpj. injection Hpj as <-. now left.
    + split; [ eapply N1.StutteringStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
Qed.

Corollary reachable_proj1 w (Hr : reachable w) (Hbyz_rel : forall m, Ns1.SystemState_rel_cong (Adv1.byzConstraints m)) :
  exists ww, Ns1.SystemState_rel ww (sysstate_proj1 w) /\ N1.reachable ww.
Proof.
  induction Hr as [ | q w w' Hstep Hr (ww & Hrel & Hr') ].
  - exists Ns1.initSystemState. split; [ | now constructor ]. split; auto; try reflexivity.
  - pose proof (tag_proj1_sound Hstep) as (Ha & Hb).
    symmetry in Hrel. pose proof Hrel as Hrel_. eapply N1.step_mirrors_SystemState_rel in Hrel.
    2: apply Ha. 2: auto. 2: now apply N1.next_sysstate_preserves_SystemState_rel.
    eexists. split. 2: eapply N1.ReachableStep; try apply Hrel. all: auto.
    rewrite <- Hb. now apply N1.next_sysstate_preserves_SystemState_rel. (* HMM ...? *)
Qed.

Corollary always_holds_proj1_apply w (Hr : reachable w) (Hbyz_rel : forall m, Ns1.SystemState_rel_cong (Adv1.byzConstraints m))
  (P : Ns1.SystemState -> Prop) (HP : Ns1.SystemState_rel_cong P) (Hinv : N1.always_holds P) : P (sysstate_proj1 w).
Proof.
  pose proof (reachable_proj1 Hr Hbyz_rel) as (ww & Hrel & Hr'). apply Hinv in Hr'. apply HP in Hrel. tauto.
Qed.

Fact tag_proj2_sound q w :
  let: qq := tag_proj2 q (sysstate_proj1 w) (sysstate_proj1 (next_sysstate q w)) in
  let: ww := N2.next_sysstate qq (sysstate_proj2 w) in
  forall w' (Hstep : system_step q w w'),
    N2.system_step qq (sysstate_proj2 w) ww /\
    Ns2.SystemState_rel ww (sysstate_proj2 w').
Proof.
  intros w' Hstep.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold sysstate_proj2; simpl_sysstate.
  - split; [ constructor | ]; reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1.
      pose proof (procMsg_proj1 Ef) as (E1 & _).
      rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)) in Ef |- *.
      rewrite Ef. simpl. rewrite upd_refl, E1. 
      destruct (trigger_procMsg _ _) in Ef |- *.
      * split; [ eapply N2.InternalStep; try reflexivity; simpl; auto | ].
        all: rewrite -> (surjective_pairing (Pt2.procInt _ _)) in Ef.
        all: simpl; unfold stmap_proj2; rewrite -> (surjective_pairing (Pt2.procInt _ _)); try reflexivity.
        revert Ef. intros [= <- <-]. 
        hnf. simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
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
      * split; [ eapply N2.StutteringStep; try reflexivity; simpl; auto | ].
        revert Ef. intros [= <- <-].
        hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
        hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
        (* TODO cumbersome ... *)
        split.
        --intros (a & Hin & Hpj). exists a. autorewrite with psent. split; auto. right. right. split; auto. intros <-. discriminate.
        --intros (a & Hin & Hpj). autorewrite with psent in Hin. 
          destruct Hin as [ (a' & <- & Hin')%in_map_iff | [ <- | (Hin & Hneq) ] ]; eauto.
    + unfold stmap_proj2.
      rewrite -> (surjective_pairing (Pt2.procMsg _ _ _)).
      split; [ eapply N2.DeliveryStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * rewrite -> (surjective_pairing (Pt2.procMsg _ _ _)). reflexivity.
      * pose proof (procMsg_proj2 Ef) as (E1 & E2). rewrite <- E1, <- E2.
        hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
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
  - unfold stmap_proj1. rewrite E. simpl. rewrite upd_refl.
    pose proof (procInt_proj1 E) as (E1 & E2).
    unfold procInt in E. rewrite -> (surjective_pairing (Pt1.procInt _ _)), <- E1 in E.
    (* TODO are the proofs above overly complicated? *)
    destruct (trigger_procInt _ _) eqn:Etr in E |- *.
    + split; [ eapply N2.InternalStep; try reflexivity; simpl; auto | ].
      1: rewrite -> (surjective_pairing (Pt2.procInt _ _)); reflexivity.
      clear E1 E2 Etr. 
      simpl. unfold stmap_proj2. rewrite -> (surjective_pairing (Pt2.procInt _ _)) in E |- *. 
      revert E. intros [= <- <-].
      hnf. simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      (* TODO repeating some proof above *)
      split.
      * intros [ Hin | (a & Hin & Hpj) ].
        --exists (pkt_inr p). autorewrite with psent. split; [ left; right; now apply in_map | apply pkt_proj2_refl ].
        --exists a. autorewrite with psent. split; auto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. 
        destruct Hin as [ [ Hin | Hin ] | Hin ]; eauto.
        all: apply in_map_iff in Hin; destruct Hin as (a' & <- & Hin'); try discriminate.
        apply pkt_proj2_refl_must in Hpj. subst. tauto.
    + clear E1 E2 Etr. revert E. intros [= <- <-].
      split; [ eapply N2.StutteringStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros (a & Hin & Hpj). exists a. autorewrite with psent. auto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. 
        destruct Hin as [ (a' & <- & Hin')%in_map_iff | ? ]; eauto. discriminate.
  - (* TODO repeating the proof above *)
    destruct m as [ mRB | mAC ]; simpl.
    + split; [ eapply N2.StutteringStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
    + split; [ eapply N2.ByzantineStep; try reflexivity; simpl; auto | ].
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

(* TODO simply repeating the proof above *)
Corollary reachable_proj2 w (Hr : reachable w) (Hbyz_rel : forall m, Ns2.SystemState_rel_cong (Adv2.byzConstraints m)) :
  exists ww, Ns2.SystemState_rel ww (sysstate_proj2 w) /\ N2.reachable ww.
Proof.
  induction Hr as [ | q w w' Hstep Hr (ww & Hrel & Hr') ].
  - exists Ns2.initSystemState. split; [ | now constructor ]. split; auto; try reflexivity.
  - pose proof (tag_proj2_sound Hstep) as (Ha & Hb).
    symmetry in Hrel. pose proof Hrel as Hrel_. eapply N2.step_mirrors_SystemState_rel in Hrel.
    2: apply Ha. 2: auto. 2: now apply N2.next_sysstate_preserves_SystemState_rel.
    eexists. split. 2: eapply N2.ReachableStep; try apply Hrel. all: auto.
    rewrite <- Hb. now apply N2.next_sysstate_preserves_SystemState_rel.
Qed.

Corollary always_holds_proj2_apply w (Hr : reachable w) (Hbyz_rel : forall m, Ns2.SystemState_rel_cong (Adv2.byzConstraints m))
  (P : Ns2.SystemState -> Prop) (HP : Ns2.SystemState_rel_cong P) (Hinv : N2.always_holds P) : P (sysstate_proj2 w).
Proof.
  pose proof (reachable_proj2 Hr Hbyz_rel) as (ww & Hrel & Hr'). apply Hinv in Hr'. apply HP in Hrel. tauto.
Qed.

End CompNetwork.
