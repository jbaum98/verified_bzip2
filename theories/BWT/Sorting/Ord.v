Require Import Coq.Bool.Sumbool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.EquivDec.

Class Preord (A : Type) :=
  { le : A -> A -> Prop;
    le_trans : forall x y z, le x y -> le y z -> le x z;
    le_total : forall x y, le x y \/ le y x;
    le_dec : forall x y, {le x y} + {~le x y};
  }.

Lemma le_refl `{Preord} : forall x, le x x.
Proof.
  intros. destruct (le_total x x); auto.
Qed.

Add Parametric Relation (A : Type) `(Preord A) : A le
    reflexivity proved by le_refl
    transitivity proved by le_trans
      as preord_le_rel.

Section Preord.
  Context {A : Type} {O : Preord A}.

  Definition ge x y := le y x.
  Definition lt x y := ~ (le y x).
  Definition gt x y := ~ (le x y).

  Lemma lt_le_rev : forall x y, lt y x -> le y x.
  Proof.
    intros. destruct (le_total x y). contradiction. auto.
  Qed.

  Definition le_decb x y := proj1_sig (bool_of_sumbool (le_dec x y)).
End Preord.

Definition eqv `{Preord} x y := le x y /\ le y x.

Theorem eqv_refl `{Preord} : forall x, eqv x x.
Proof.
  intros. unfold eqv. split; reflexivity.
Qed.

Theorem eqv_sym `{Preord} : forall x y, eqv x y -> eqv y x.
Proof. intros. unfold eqv in *. intuition. Qed.

Theorem eqv_trans `{Preord} : forall x y z , eqv x y -> eqv y z -> eqv x z.
Proof. intros. unfold eqv in *. intuition (eapply le_trans; eauto). Qed.

Add Parametric Relation (A : Type) `(Preord A) : A eqv
    reflexivity proved by eqv_refl
    symmetry proved by eqv_sym
    transitivity proved by eqv_trans
      as eqv_rel.

Add Parametric Morphism `(Preord) : le with
      signature eqv ==> eqv ==> iff as le_mor.
Proof.
  intros.
  unfold eqv in *. intuition; eauto using le_trans.
Qed.

Add Parametric Morphism `(Preord): lt with
      signature eqv ==> eqv ==> iff as lt_mor.
Proof.
  intros.
  unfold eqv, lt in *. intuition; eauto using le_trans.
Qed.

Section Eqv.
  Context {A : Type} {O : Preord A}.

  Program Definition eqv_dec x y : {eqv x y} + {~ eqv x y} :=
    if le_dec x y then
      if le_dec y x then left _
      else right _
    else right _.
  Solve All Obligations with unfold eqv; intuition eauto.

  Definition eqv_decb x y := proj1_sig (bool_of_sumbool (eqv_dec x y)).

  Theorem eqv_def : forall x y,
      eqv x y <-> (le x y /\ le y x).
  Proof. reflexivity. Qed.

  Global Instance Preord_eqv_Equivalence : Equivalence eqv := {}.
  Global Instance Ord_EqDec : EqDec A eqv := eqv_dec.
End Eqv.

Section Lt.
  Context {A : Type} {O : Preord A}.

  Theorem lt_spec : forall x y, le x y <-> lt x y \/ eqv x y.
  Proof.
    intros.
    destruct (eqv_dec x y); unfold lt, eqv in *; intuition; eauto using lt_le_rev.
  Qed.

  Theorem lt_spec2 : forall x y, lt x y <-> le x y /\ ~ eqv x y.
  Proof.
    intros.
    destruct (eqv_dec x y); unfold lt, eqv in *; intuition; eauto using lt_le_rev.
  Qed.

  Program Definition lt_eq_dec x y : {lt x y} + {eqv x y} + {lt y x} :=
    match (le_dec x y, le_dec y x) with
    | (_, right _) => inleft (left _)
    | (right _, _) => inright _
    | (left _, left _) => inleft (right _)
    end.
  Next Obligation. unfold eqv; eauto. Defined.

  Theorem lt_irrefl : forall x, ~ (lt x x).
    intros x c.
    apply c. apply le_refl.
  Qed.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    intros. unfold lt in *.
    match goal with [ H : ~ le _ _ |- _ ] => apply lt_le_rev in H end.
    intro.
    eauto using le_trans.
  Qed.

  Theorem lt_excl : forall x y, ~ (lt x y /\ lt y x).
    intros x y [lxy lyx].
    eapply lt_irrefl.
    eapply lt_trans; eauto.
  Qed.

  Theorem lt_not_eq : forall x y, lt x y -> ~ eqv x y.
  Proof. unfold lt, eqv in *. intuition. Qed.

  Theorem lt_le : forall x y, lt x y -> le x y.
  Proof. unfold lt. intros. apply lt_le_rev. auto. Qed.
End Lt.

Section Ord.
  Class Ord (A : Type) `{Preord A} :=
    { eqv_eq : forall x y, eqv x y -> x = y }.

  Global Instance Ord_EquivDef {A} `{Ord A} : EqDec A eq.
  Proof.
    intros x y.
    destruct (eqv_dec x y).
    - left. apply eqv_eq. auto.
    - right. intro c. apply n. rewrite c. reflexivity.
  Defined.
End Ord.
