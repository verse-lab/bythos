From Coq Require Import List Bool Lia PeanoNat.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From Bythos.Systems Require Export Network.
From Bythos.Composition Require Export States.

(* FIXME: without making it a module type, we cannot compose CompNetwork *)

Module CompNetwork (A : NetAddr) (M1 M2 : MessageType) (BTh : ByzThreshold A)
  (Pk1 : SimplePacket A M1) (Pk2 : SimplePacket A M2)
  (Pt1 : Protocol.Protocol A M1 Pk1 BTh)
  (Pt2 : Protocol.Protocol A M2 Pk2 BTh)
  (SCPT : SeqCompProtocolTrigger A M1 M2 BTh Pk1 Pk2 Pt1 Pt2)
  (Ns1 : NetState A M1 Pk1 BTh Pt1) (Ns2 : NetState A M2 Pk2 BTh Pt2)
  (BSett : ByzSetting A)
  (* TODO is using the Adv of each sub-protocol really good? *)
  (Adv1 : Adversary A M1 BTh BSett Pk1 Pt1 Ns1) (Adv2 : Adversary A M2 BTh BSett Pk2 Pt2 Ns2)
  (* TODO this is bad! *)
  (PSOp1 : PacketSoupOperations Pk1) (PSOp2 : PacketSoupOperations Pk2)
  (N1 : Network.Network A M1 BTh BSett Pk1 PSOp1 Pt1 Ns1 Adv1)
  (N2 : Network.Network A M2 BTh BSett Pk2 PSOp2 Pt2 Ns2 Adv2).

Import BTh SCPT.

Module Export CM := CompMessageImpl M1 M2.

Module Export CPk := CompSimplePacketImpl A M1 M2 CM Pk1 Pk2.

Module Export CNs := CompNetState A M1 M2 BTh CM Pk1 Pk2 CPk Pt1 Pt2 SCPT Ns1 Ns2.

Module Export CAdv <: Adversary A CM BTh BSett CPk CPt CNs.

Definition byz_constraints m w :=
  match m with
  | inl m1 => Adv1.byz_constraints m1 (world_proj1 w)
  | inr m2 => Adv2.byz_constraints m2 (world_proj2 w)
  end.

End CAdv.

Module Export CPSOp : (* hide implementation *) PacketSoupOperations CPk := PacketSoupOperationsImpl CPk.

Include NetworkImpl A CM BTh BSett CPk CPSOp CPt CNs CAdv.

Definition ssd_proj1 (q : system_step_descriptor) : N1.system_step_descriptor :=
  match q with
  | Idle => N1.Idle
  | Deliver p =>
    match pkt_proj1 p with
    | Some res => N1.Deliver res
    | _ => N1.Idle
    end
  | Intern n r => N1.Intern n r
  | Byz src dst m =>
    match m with
    | inl m1 => N1.Byz src dst m1
    | _ => N1.Idle
    end
  end.

(* depending on the previous protocol *)
Definition ssd_proj2 (q : system_step_descriptor) (w w' : Ns1.World) : N2.system_step_descriptor :=
  match q with
  | Idle => N2.Idle
  | Deliver p =>
    match pkt_proj2 p with
    | Some res => N2.Deliver res
    | _ =>
      let: n := p.(dst) in
      match trigger_procMsg (Ns1.localState w n) (Ns1.localState w' n) with
      | Some tr2 => N2.Intern n tr2
      | _ => N2.Idle
      end
    end
  | Intern n _ =>
    match trigger_procInt (Ns1.localState w n) (Ns1.localState w' n) with
    | Some tr2 => N2.Intern n tr2
    | _ => N2.Idle
    end
  | Byz src dst m =>
    match m with
    | inr mAC => N2.Byz src dst mAC
    | _ => N2.Idle
    end
  end.

Local Set Implicit Arguments.

Local Hint Rewrite -> N1.PC.In_consume N2.PC.In_consume In_consume option_map_list_In : psent.

(* the definitions should be sound *)

Fact ssd_proj1_sound q w :
  let: ww := N1.next_world (ssd_proj1 q) (world_proj1 w) in
  forall w' (Hstep : system_step q w w'),
    N1.system_step (ssd_proj1 q) (world_proj1 w) ww /\
    Ns1.World_rel ww (world_proj1 w').
Proof.
  intros w' Hstep.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj1; simpl_world.
  - split; [ constructor | ]; reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1.
      rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)).
      split; [ eapply N1.DeliverStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)). reflexivity.
      * pose proof (procMsgWithCheck_proj1 Ef) as (E1 & E2). rewrite <- E1, <- E2.
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
    + split; [ eapply N1.IdleStep; try reflexivity; simpl; auto | ].
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
    split; [ eapply N1.InternStep; try reflexivity; simpl; auto | ].
    1: rewrite -> (surjective_pairing (Pt1.procInt _ _)); reflexivity.
    pose proof (procInt_proj1 E) as (E1 & E2). rewrite <- E1, <- E2.
    hnf; simpl. split; [ intros ?; unfold upd, Ns1.upd; now destruct_eqdec as_ -> | ].
    hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
    (* ...? *)
    setoid_rewrite In_sendout. firstorder.
  - destruct m as [ mRB | mAC ]; simpl.
    + split; [ eapply N1.ByzStep; try reflexivity; simpl; auto | ].
      simpl. hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros [ <- | (a & Hin & Hpj) ].
        --eexists. autorewrite with psent. split; [ left; reflexivity | ]. reflexivity.
        --exists a. autorewrite with psent. tauto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. destruct Hin as [ <- | Hin ]; eauto.
        cbn in Hpj. injection Hpj as <-. now left.
    + split; [ eapply N1.IdleStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj1. autorewrite with psent.
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
Qed.

Corollary reachable_proj1 w (Hr : reachable w) (Hbyz_rel : forall m, Ns1.World_rel_cong (Adv1.byz_constraints m)) :
  exists ww, Ns1.World_rel ww (world_proj1 w) /\ N1.reachable ww.
Proof.
  induction Hr as [ | q w w' Hstep Hr (ww & Hrel & Hr') ].
  - exists Ns1.initWorld. split; [ | now constructor ]. split; auto; try reflexivity.
  - pose proof (ssd_proj1_sound Hstep) as (Ha & Hb).
    symmetry in Hrel. pose proof Hrel as Hrel_. eapply N1.step_mirrors_World_rel in Hrel.
    2: apply Ha. 2: auto. 2: now apply N1.next_world_preserves_World_rel.
    eexists. split. 2: eapply N1.ReachableStep; try apply Hrel. all: auto.
    rewrite <- Hb. now apply N1.next_world_preserves_World_rel. (* HMM ...? *)
Qed.

Corollary always_holds_proj1_apply w (Hr : reachable w) (Hbyz_rel : forall m, Ns1.World_rel_cong (Adv1.byz_constraints m))
  (P : Ns1.World -> Prop) (HP : Ns1.World_rel_cong P) (Hinv : N1.always_holds P) : P (world_proj1 w).
Proof.
  pose proof (reachable_proj1 Hr Hbyz_rel) as (ww & Hrel & Hr'). apply Hinv in Hr'. apply HP in Hrel. tauto.
Qed.

Fact ssd_proj2_sound q w :
  let: qq := ssd_proj2 q (world_proj1 w) (world_proj1 (next_world q w)) in
  let: ww := N2.next_world qq (world_proj2 w) in
  forall w' (Hstep : system_step q w w'),
    N2.system_step qq (world_proj2 w) ww /\
    Ns2.World_rel ww (world_proj2 w').
Proof.
  intros w' Hstep.
  inversion_step' Hstep; clear Hstep; simpl.
  all: unfold world_proj2; simpl_world.
  - split; [ constructor | ]; reflexivity.
  - destruct msg as [ mRB | mAC ]; simpl.
    + unfold stmap_proj1.
      pose proof (procMsgWithCheck_proj1 Ef) as (E1 & _).
      rewrite -> (surjective_pairing (Pt1.procMsg _ _ _)) in Ef |- *.
      rewrite Ef. simpl. rewrite upd_refl, E1. 
      destruct (trigger_procMsg _ _) in Ef |- *.
      * split; [ eapply N2.InternStep; try reflexivity; simpl; auto | ].
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
      * split; [ eapply N2.IdleStep; try reflexivity; simpl; auto | ].
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
      split; [ eapply N2.DeliverStep; try reflexivity; simpl; auto | ].
      * apply option_map_list_In. eexists. split. apply Hpin. reflexivity.
      * rewrite -> (surjective_pairing (Pt2.procMsg _ _ _)). reflexivity.
      * pose proof (procMsgWithCheck_proj2 Ef) as (E1 & E2). rewrite <- E1, <- E2.
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
    + split; [ eapply N2.InternStep; try reflexivity; simpl; auto | ].
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
      split; [ eapply N2.IdleStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; [ intros ?; unfold stmap_proj2, upd, Ns2.upd; now destruct_eqdec as_ -> | ].
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      split.
      * intros (a & Hin & Hpj). exists a. autorewrite with psent. auto.
      * intros (a & Hin & Hpj). autorewrite with psent in Hin. 
        destruct Hin as [ (a' & <- & Hin')%in_map_iff | ? ]; eauto. discriminate.
  - (* TODO repeating the proof above *)
    destruct m as [ mRB | mAC ]; simpl.
    + split; [ eapply N2.IdleStep; try reflexivity; simpl; auto | ].
      hnf; simpl. split; auto.
      hnf. intros p. unfold pkts_filter_proj2. autorewrite with psent.
      (* TODO cumbersome ... *)
      setoid_rewrite In_sendout1. firstorder. subst. discriminate.
    + split; [ eapply N2.ByzStep; try reflexivity; simpl; auto | ].
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
Corollary reachable_proj2 w (Hr : reachable w) (Hbyz_rel : forall m, Ns2.World_rel_cong (Adv2.byz_constraints m)) :
  exists ww, Ns2.World_rel ww (world_proj2 w) /\ N2.reachable ww.
Proof.
  induction Hr as [ | q w w' Hstep Hr (ww & Hrel & Hr') ].
  - exists Ns2.initWorld. split; [ | now constructor ]. split; auto; try reflexivity.
  - pose proof (ssd_proj2_sound Hstep) as (Ha & Hb).
    symmetry in Hrel. pose proof Hrel as Hrel_. eapply N2.step_mirrors_World_rel in Hrel.
    2: apply Ha. 2: auto. 2: now apply N2.next_world_preserves_World_rel.
    eexists. split. 2: eapply N2.ReachableStep; try apply Hrel. all: auto.
    rewrite <- Hb. now apply N2.next_world_preserves_World_rel.
Qed.

Corollary always_holds_proj2_apply w (Hr : reachable w) (Hbyz_rel : forall m, Ns2.World_rel_cong (Adv2.byz_constraints m))
  (P : Ns2.World -> Prop) (HP : Ns2.World_rel_cong P) (Hinv : N2.always_holds P) : P (world_proj2 w).
Proof.
  pose proof (reachable_proj2 Hr Hbyz_rel) as (ww & Hrel & Hr'). apply Hinv in Hr'. apply HP in Hrel. tauto.
Qed.

End CompNetwork.
