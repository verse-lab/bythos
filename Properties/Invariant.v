From Coq Require Import List Bool Lia.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Systems Require Export Network.

From RecordUpdate Require Export RecordUpdate.
From stdpp Require Export tactics. (* anyway *)

Module Type StateMntTemplate (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A)
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr).

Parameter state_mnt_type : State -> Type.
Parameter state_mnt : forall st : State, state_mnt_type st -> State.
Parameter psent_effect : forall st : State, state_mnt_type st -> Address -> PacketSoup -> Prop.

End StateMntTemplate.

Module StateMntToolkit (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A)
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr)
  (Export SMT : StateMntTemplate A M BTh P PSOp Pr Ns).

Global Arguments state_mnt [_] _.
Global Arguments psent_effect [_] _ _ _.

(* dependent list *)
(* during construction, the state at the beginning gets closer to the one at the end *)
Inductive state_mnt_type_list : State -> State -> Type :=
  | MNTnil : forall st, state_mnt_type_list st st
  | MNTcons : forall [st] (d : state_mnt_type st) [st'], 
    state_mnt_type_list (state_mnt d) st' ->
    state_mnt_type_list st st'.

Fixpoint state_mnt_type_list_app [st st' st''] (l1 : state_mnt_type_list st st') (l2 : state_mnt_type_list st' st'') 
  : state_mnt_type_list st st''.
  destruct l1.
  - exact l2.
  - exact (MNTcons d (state_mnt_type_list_app _ _ _ l1 l2)).
Defined.

(* an over-approx of the effect over psent? since it can say nothing about psent *)
Fixpoint psent_effect_star (n : Address) (psent : PacketSoup) [st st'] (l : state_mnt_type_list st st') : Prop :=
  match l with
  | MNTnil _ => True
  | MNTcons d l' =>
    psent_effect d n psent /\ psent_effect_star n psent l'
  end.

Lemma psent_effect_star_app n psent st st' st'' (l1 : state_mnt_type_list st st') (l2 : state_mnt_type_list st' st'') :
  psent_effect_star n psent (state_mnt_type_list_app l1 l2) <-> 
  psent_effect_star n psent l1 /\ psent_effect_star n psent l2.
Proof. revert st'' l2. induction l1; intros; simpl; try tauto. rewrite IHl1. tauto. Qed.

(* NOTE: the following only works for states defined as Records *)

Ltac state_analyze_select f := idtac "state_analyze_select is user defined.".

(* need to add st' as an argument, since the size of state components in the goal will only increase;
    so do recursion on the st' here *)

Ltac state_analyze' st' :=
  match st' with
  | set ?f _ ?st =>
    let ctor := state_analyze_select f in
    (* this constructs the sequence in the reversed order ... 
      the refl check of record update is so good that this bug is not exposed *)
    (* unshelve eapply MNTcons; [ eapply ctor; try eassumption | ]; 
      simpl; state_analyze' st *)
    state_analyze' st;
    match goal with 
    | |- state_mnt_type_list _ _ =>
      unshelve eapply MNTcons; [ eapply ctor; try eassumption | ]; simpl
    | _ => idtac
    end
  | _ => idtac
  end.

Ltac psent_effect_star_solver := idtac "psent_effect_star_solver is user defined.".

Ltac post_state_analysis_other_cases_solver := idtac "post_state_analysis_other_cases_solver is user defined.".

Ltac state_analyze :=
  try rewrite sendout0;
  match goal with
  | |- exists (_ : state_mnt_type_list _ ?st'), _ =>
    unshelve eexists; [ state_analyze' st'; try solve [ apply (MNTnil _) ] | ];
    split_and?;
    match goal with
    | |- @psent_effect_star _ _ _ _ _ => psent_effect_star_solver
    | _ => post_state_analysis_other_cases_solver
    end
  end.

End StateMntToolkit.

Module Type PsentMntTemplate (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr)
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P PSOp Pr Ns Adv).

Parameter packets_shape : Type.
Parameter packets_shape_consistent : packets_shape -> list Packet -> Prop.

Parameter state_effect_recv : forall (src dst : Address) (m : Message) (stmap : StateMap), Prop.
Parameter state_effect_send_by_shape : packets_shape -> StateMap -> Prop.

End PsentMntTemplate.

Module PsentMntToolkit (Export A : NetAddr) (Export M : MessageType)
  (Export BTh : ByzThreshold A) (Export BSett : ByzSetting A) 
  (Export P : SimplePacket A M) (Export PSOp : PacketSoupOperations P)
  (Export Pr : Protocol A M P BTh) (Export Ns : NetState A M P BTh Pr)
  (Export Adv : Adversary A M BTh BSett P Pr Ns) (Export N : Network A M BTh BSett P PSOp Pr Ns Adv)
  (Export PMT : PsentMntTemplate A M BTh BSett P PSOp Pr Ns Adv N).

(* want to write it in another way so that the base part can be exposed, 
    which will enable some proofs about psent_mnt_type concatenation *)
Inductive psent_mnt_type_base (psent : PacketSoup) : Type :=
  | Pid : psent_mnt_type_base psent
  | Puse : forall p, In p psent -> psent_mnt_type_base psent
.

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

Definition psent_mnt_base [psent] (s : psent_mnt_type_base psent) : PacketSoup :=
  match s with
  | Pid _ => psent
  | Puse _ p _ => consume p psent
  end.

Fixpoint psent_mnt [psent] (b : psent_mnt_type_base psent) (l : list psent_mnt_type) psent' : Prop :=
  match l with
  | nil => Ineq psent' (psent_mnt_base b)
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

Definition state_effect_base [psent] (stmap : StateMap) (b : psent_mnt_type_base psent) : Prop :=
  match b with
  | Pid _ => True (* under-specified *)
  | Puse _ (mkP src n m used) _ => is_byz n = false /\ state_effect_recv src n m stmap
  end.

Global Arguments state_effect_base [_] _ !_.

Fixpoint state_effect_send (stmap : StateMap) (l : list psent_mnt_type) : Prop :=
  match l with
  | nil => True
  | a :: l' =>
    state_effect_send stmap l' /\ (* putting this here can be convenient *)
    state_effect_send_by_shape a.(ps) stmap
  end.

Fact state_effect_send_app stmap l l' : 
  state_effect_send stmap (l ++ l') <-> state_effect_send stmap l /\ state_effect_send stmap l'.
Proof. revert l'. induction l; simpl; intros; try tauto. rewrite IHl. tauto. Qed.

Inductive psent_sender_kind (psent : list Packet) : Type := 
  | PSKnonbyz (b : psent_mnt_type_base psent) (l : list psent_mnt_type)
  | PSKbyz (p : Packet).

Global Arguments PSKnonbyz [_] _ _.

Definition state_effect (stmap : StateMap) [psent] (psk : psent_sender_kind psent) : Prop :=
  match psk with
  | PSKnonbyz b l => state_effect_base stmap b /\ state_effect_send stmap l
  | PSKbyz _ p => is_byz p.(src) /\ p.(consumed) = false /\ byz_constraints p.(msg) (mkW stmap psent) (* FIXME: is byz_constraints only about psent? *)
  end.

Ltac pkts_match pkts := idtac "pkts_match is user defined.".

Ltac single_pkt_match pkt := idtac "single_pkt_match is user defined.".

Ltac psent_analyze' psent' :=
  match psent' with
  | sendout (?pkts1 ++ ?pkts2) ?psent_ =>
    let ss := psent_analyze' constr:(sendout pkts1 psent_) in
    let qq := pkts_match pkts2 in
    uconstr:(qq :: ss)
  | sendout (?pkt :: nil) ?psent_ => 
    let ss := psent_analyze' constr:(psent_) in
    let qq := single_pkt_match pkt in
    uconstr:(qq :: ss)
  | sendout ?pkts ?psent_ => 
    let ss := psent_analyze' constr:(psent_) in
    let qq := pkts_match pkts in
    uconstr:(qq :: ss)
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

Ltac state_effect_solve := idtac "state_effect_solve is user defined.".

Ltac psent_analyze :=
  try rewrite sendout0;
  match goal with
  | |- exists (_ : ?t), psent_mnt _ _ ?psent' /\ _ =>
    let l := psent_analyze' psent' in
    unshelve eexists l;
    match goal with
    | |- psent_mnt _ _ ?psent' /\ _ => 
      split; [ simpl; auto; try reflexivity; psent_mnt_solve | state_effect_solve ]
    | _ => idtac
    end
  end.

Definition psent_mnt_sound_goal_pre q w w' : Prop :=
  match q with
  | Byz src dst m =>
    let: p := mkP src dst m false in
    localState w' = localState w /\ 
    sentMsgs w' = sendout1 p (sentMsgs w) /\
    state_effect (localState w') (PSKbyz (sentMsgs w) p)
  | _ =>
    exists (b : psent_mnt_type_base (sentMsgs w)) (l : list psent_mnt_type), 
      psent_mnt b l (sentMsgs w') /\ state_effect (localState w') (PSKnonbyz b l)
  end.

Definition psent_mnt_sound_goal w w' : Prop :=
  exists psk : psent_sender_kind (sentMsgs w),
    state_effect (localState w') psk /\
    match psk with
    | PSKnonbyz b l => psent_mnt b l (sentMsgs w')
    | PSKbyz _ p => localState w' = localState w (* this should be enough *) /\ sentMsgs w' = sendout1 p (sentMsgs w)
    end.

End PsentMntToolkit.
