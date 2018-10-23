Require Import Coq.Bool.Sumbool.

Arguments sumbool_and : default implicits.
Arguments sumbool_or : default implicits.

Section SumBool.

  Lemma sumbool_and_true_l: forall (A B C D : Prop) (E: Type) (a: A) (Y: {C} + {D}) (t f: E),
      (if @sumbool_and _ B _ _ (left a) Y then t else f) =
      (if Y then t else f) .
  Proof.
    intros; case Y; auto.
  Qed.

  Lemma sumbool_and_false_l: forall (A B C D : Prop) (E: Type) (b: B) (Y: {C} + {D}) (t f: E),
      (if @sumbool_and A _ _ _ (right b) Y then t else f) = f.
  Proof.
    intros; case Y; auto.
  Qed.

  Lemma sumbool_and_true_r: forall (A B C D : Prop) (E: Type) (c: C) (X: {A} + {B}) (t f: E),
      (if @sumbool_and _ _ _ D X (left c) then t else f) =
      (if X then t else f).
  Proof.
    intros; case X; auto.
  Qed.

  Lemma sumbool_and_false_r: forall (A B C D: Prop) (E: Type) (d: D) (X: {A} + {B}) (t f: E),
      (if @sumbool_and _ _ C _ X (right d) then t else f) = f.
  Proof.
    intros; case X; auto.
  Qed.

  Lemma sumbool_and_diag: forall (A B : Prop) (E: Type) (X: {A} + {B}) (t f: E),
      (if sumbool_and X X then t else f) = (if X then t else f).
  Proof.
    intros; case X; auto.
  Qed.
End SumBool.

Bind Scope sumbool_scope with sumbool.
Delimit Scope sumbool_scope with sumbool.

Notation "x || y"
  := (sumbool_or x y)  (at level 50, left associativity) : sumbool_scope.
Notation "x && y"
  := (sumbool_and x y) (at level 40, left associativity) : sumbool_scope.
