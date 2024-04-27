From Coq Require Import Bool List Permutation RelationClasses.
From Coq Require ssrbool.

Definition prod_eq_dec {A B : Type} (eq_dec_a : forall x y : A, {x = y} + {x <> y})
  (eq_dec_b : forall x y : B, {x = y} + {x <> y}) :
  forall x y : (A * B)%type, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; try apply eq_dec_a; try apply eq_dec_b.
Qed.

Fact eqdec_refl {A B : Type} (eqdec : forall x y : A, {x = y} + {x <> y}) (x : A) (b1 b2 : B) :
  (if eqdec x x then b1 else b2) = b1.
Proof. destruct (eqdec _ _); auto; try contradiction. Qed.

Fact sumbool_is_left [A : Prop] (dec : {A} + {~ A}) : 
  (if dec then true else false) = true <-> A.
Proof. destruct dec; intuition discriminate. Qed.

Fact sumbool_is_right [A : Prop] (dec : {A} + {~ A}) : 
  (if dec then true else false) = false <-> ~ A.
Proof. destruct dec; intuition discriminate. Qed.

Create HintDb booldec.

Fact is_left_unfold [A B : Prop] (b : {A} + {B}) : ssrbool.is_left b = if b then true else false.
Proof eq_refl.

Global Hint Rewrite -> is_left_unfold sumbool_is_left sumbool_is_right andb_true_iff andb_false_iff orb_true_iff orb_false_iff negb_true_iff @eqdec_refl filter_In : booldec.
