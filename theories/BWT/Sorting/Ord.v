Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Basics.

(** A type equipped with a total, decidable preorder. *)

Class Ord (A : Type):=
  { le : A -> A -> Prop;
    le_trans : forall x y z, le x y -> le y z -> le x z;
    le_total : forall x y, le x y \/ le y x;
    le_dec : forall x y, {le x y} + {~le x y};
  }.

Notation "x <= y" := (le x y) (at level 70, no associativity) : ord_scope.
Local Open Scope ord_scope.

Lemma le_refl {A} `{Ord A} : forall x, x <= x.
Proof.
  intros. destruct (le_total x x); auto.
Qed.

Lemma le_not {A} `{Ord A} : forall x y, ~(x <= y) -> y <= x.
Proof.
  intros. destruct (le_total x y). contradiction. auto.
Qed.

Definition ge {A} `{Ord A} x y := y <= x.
Definition lt {A} `{Ord A} x y := ~ (y <= x).
Definition gt {A} `{Ord A} x y := ~ (x <= y).

Notation "x >= y" := (ge x y) (at level 70, no associativity) : ord_scope.
Notation "x < y" := (lt x y) (at level 70, no associativity) : ord_scope.
Notation "x > y" := (gt x y) (at level 70, no associativity) : ord_scope.

(** Two elements are equivalent if they compare [le] in both directions. *)

Definition eqv {A} `{Ord A} (x y : A) : Prop := x <= y /\ y <= x.

Notation " x === y " := (eqv x y) (at level 70, no associativity) : ord_scope.
Notation " x =/= y " := (~ eqv x y) (at level 70, no associativity) : ord_scope.

Program Definition eqv_dec {A} `{Ord A} (x y : A) : {x === y} + {x =/= y} :=
  if le_dec x y then
    if le_dec y x then left _
    else right _
  else right _.
Solve All Obligations with unfold eqv; intuition eauto.

Notation " x == y " := (eqv_dec (x :>) (y :>)) (no associativity, at level 70) : ord_scope.

Section Equiv.
  Context {A} `{Ord A}.

  Theorem eqv_refl : forall x, x === x.
  Proof.
    intros.
    unfold eqv. split; apply le_refl.
  Qed.

  Theorem eqv_sym : forall x y, eqv x y -> eqv y x.
  Proof. intros. unfold eqv in *. intuition. Qed.

  Theorem eqv_trans : forall x y z , eqv x y -> eqv y z -> eqv x z.
  Proof. intros. unfold eqv in *. intuition (eapply le_trans; eauto). Qed.

  (* Instance Equivalence_eqv : Equivalence eqv | 0 := *)
  (*   { Equivalence_Reflexive := eqv_refl; *)
  (*     Equivalence_Symmetric := eqv_sym; *)
  (*     Equivalence_Transitive := eqv_trans; *)
  (*   }. *)

  Theorem eqv_def : forall x y,
      x === y <-> x <= y /\ y <= x.
  Proof. reflexivity. Qed.

  (* Instance EqDec_eqv : EqDec A eqv | 0 := eqv_dec. *)

  Theorem eqv_subst : forall x y, x === y -> forall z, x === z <-> y === z.
  Proof.
    intros.
    repeat rewrite eqv_def in *.
    intuition; eauto using le_trans.
  Qed.
End Equiv.

Section Lt.
  Context {A} `{Ord A}.

  Theorem lt_spec : forall x y, x <= y <-> x < y \/ x === y.
  Proof.
    intros.
    destruct (eqv_dec x y); unfold lt, eqv in *; intuition; eauto using le_not.
  Qed.

  Program Definition lt_eq_dec x y : {x < y} + {x === y} + {y < x} :=
    match (le_dec x y, le_dec y x) with
    | (_, right _) => inleft (left _)
    | (right _, _) => inright _
    | (left _, left _) => inleft (right _)
    end.
  Next Obligation. unfold eqv; eauto. Defined.

  Theorem lt_irrefl : forall x, ~ (x < x).
    intros x c.
    apply c. apply le_refl.
  Qed.

  Theorem lt_trans : forall x y z, x < y -> y < z -> x < z.
  Proof.
    intros. unfold lt in *.
    match goal with [ H : ~ _ <= _ |- _ ] => apply le_not in H end.
    intro.
    eauto using le_trans.
  Qed.

  Theorem lt_excl : forall x y, ~ (x < y /\ y < x).
    intros x y [lxy lyx].
    eapply lt_irrefl.
    eapply lt_trans; eauto.
  Qed.

  Theorem lt_not_eq : forall x y, x < y -> x =/= y.
  Proof. unfold lt, eqv in *. intuition. Qed.

  Theorem lt_le : forall x y, x < y -> x <= y.
  Proof. unfold lt. intros. apply le_not. auto. Qed.

End Lt.

Add Parametric Relation {A} `{Ord A} : A eqv
    reflexivity proved by eqv_refl
    symmetry proved by eqv_sym
    transitivity proved by eqv_trans
  as eqv_rel.

Add Parametric Morphism {A} `{Ord A} : le with
  signature eqv ==> eqv ==> iff as le_mor.
Proof.
  intros.
  unfold eqv in *. intuition; eauto using le_trans.
Qed.

Add Parametric Morphism {A} `{Ord A} : lt with
  signature eqv ==> eqv ==> iff as lt_mor.
Proof.
  intros.
  unfold eqv, lt in *. intuition; eauto using le_trans.
Qed.

Section Projection.
  Context {A B : Type} `{Ord B}.

  Variable proj : A -> B.

  Instance Ord_proj : Ord A :=
    { le := fun x y => le (proj x) (proj y);}.
  Proof.
    - intros. eapply le_trans; eauto.
    - intros. eapply le_total.
    - intros. destruct (le_dec (proj x) (proj y)).
      + left. auto.
      + right. auto.
  Defined.
End Projection.
