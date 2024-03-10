From Coq Require ssrbool.

Global Tactic Notation "eqsolve" := solve [ intuition congruence | intuition discriminate ].

Global Tactic Notation "pick" constr(def) "as_" ident(H) :=
  first
  [ match goal with
    | H0 : def _ |- _ => rename H0 into H
    | H0 : def _ _ |- _ => rename H0 into H
    | H0 : def _ _ _ |- _ => rename H0 into H
    end
  | match goal with
    | H0 : context[def] |- _ => rename H0 into H; hnf in H
    end ];
  tryif (is_const def) then (unfold def in H) else idtac.

(* TODO need improvement *)
Global Tactic Notation "pick" constr(def) "as_" ident(H) "by_" tactic2(tac) :=
  let a := fresh "eprop" in
  evar (a : Prop); assert a as H; subst a; 
    [ tac; (let Htmp := fresh "Htmp" in pick def as_ Htmp; exact Htmp) | ].

Global Tactic Notation "saturate_assumptions" :=
  repeat match goal with
    H : ?P -> ?Q |- _ => 
    match type of P with
      Prop => specialize (H ltac:(try apply I; try reflexivity; assumption))
    end
  end.

Local Ltac sat H :=
  match type of H with
  | forall (_ : ?P), _ =>
    tryif 
      ((first [ specialize (H I) | specialize (H eq_refl) | specialize (H ltac:(assumption)) ]; sat H) +
      (* search with backtracking *)
      (match goal with
      | HH : ?P |- _ => specialize (H HH); sat H
      end)) then idtac else fail 1
  | _ => idtac
  end.

(* just a wrapper with a better name *)
Global Tactic Notation "saturate_assumptions" "!" "in_" hyp(H) := sat H.

Global Tactic Notation "saturate_assumptions" "!" :=
  repeat match goal with
  | H : forall (_ : _), _ |- _ => sat H
  end.

Global Tactic Notation "hypothesis" :=
  match goal with
    H : ?e |- _ => 
    match type of e with
      Prop => solve [ simple apply H ]
    end
  end.

(* FIXME: later, combine the following two together *)
Global Ltac isSome_rewrite :=
  repeat match goal with
  | H : ?a = _, H0 : context[ssrbool.isSome ?a] |- _ => rewrite H in H0; simpl in H0
  | H : ?a = _ |- context[ssrbool.isSome ?a] => rewrite H; simpl
  end.

Global Ltac is_true_rewrite :=
  repeat match goal with
  | H : ?a = true, H0 : context[is_true ?a] |- _ => rewrite H in H0; change (is_true true) with (true = true) in H0
  | H : ?a = false, H0 : context[is_true ?a] |- _ => rewrite H in H0; change (is_true false) with (false = true) in H0
  | H : ?a = true |- context[is_true ?a] => rewrite H; change (is_true true) with (true = true)
  | H : ?a = false |- context[is_true ?a] => rewrite H; change (is_true false) with (false = true)
  end.

Global Ltac match_option_rewrite :=
  repeat match goal with
  | H : ?a = _, H0 : context[match ?a with Some _ => _ | None => _ end] |- _ => rewrite H in H0; simpl in H0
  | H : ?a = _ |- context[match ?a with Some _ => _ | None => _ end] => rewrite H; simpl
  end.

Global Tactic Notation "destruct_eqdec_raw" constr(eqdec) constr(a) constr(b) simple_intropattern(pat) :=
  match type of eqdec with
    forall _ : _, forall _ : _, sumbool (eq _ _) (not (eq _ _)) =>
    destruct (eqdec a b) as [ pat | ] +
    destruct (eqdec a b) as [ | ]
  end.

Global Tactic Notation "destruct_eqdec" "in_" hyp(H) "as_" simple_intropattern(pat) :=
  repeat match type of H with
    context[if ?eqdec ?a ?b then _ else _] => destruct_eqdec_raw eqdec a b pat
  end.

Global Tactic Notation "destruct_eqdec" "as_" simple_intropattern(pat) :=
  repeat match goal with
    |- context[if ?eqdec ?a ?b then _ else _] => destruct_eqdec_raw eqdec a b pat
  end.

Global Tactic Notation "destruct_eqdec" "!" "as_" simple_intropattern(pat) :=
  repeat match goal with 
  | H : context[if ?eqdec ?a ?b then _ else _] |- _ => destruct_eqdec_raw eqdec a b pat
  end; try destruct_eqdec as_ pat.

Global Tactic Notation "destruct_exists" :=
  repeat match goal with
    H : exists (_ : _), _ |- _ =>
    destruct H as (? & ?)
  end.
