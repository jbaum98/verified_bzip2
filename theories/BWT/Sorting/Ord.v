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

Remark le_refl `{Preord} : forall x, le x x.
Proof.
  intros. destruct (le_total x x); auto.
Qed.

Add Parametric Relation (A : Type) `(Preord A) : A le
    reflexivity proved by le_refl
    transitivity proved by le_trans
      as preord_le_rel.

Definition ge `{Preord} x y := le y x.
Definition lt `{Preord} x y := ~ (le y x).
Definition gt `{Preord} x y := ~ (le x y).

Remark ge_refl `{Preord} : forall x, ge x x.
Proof. unfold ge. reflexivity. Qed.

Remark ge_trans `{Preord} : forall x y z,
    ge x y -> ge y z -> ge x z.
Proof. unfold ge. intros. transitivity y; auto. Qed.

Add Parametric Relation (A : Type) `(Preord A) : A ge
    reflexivity proved by ge_refl
    transitivity proved by ge_trans
      as preord_ge_rel.

Remark lt_trans `{Preord} : forall x y z,
    lt x y -> lt y z -> lt x z.
Proof.
  unfold lt; intros.
  destruct (le_total y x); [contradiction|].
  destruct (le_total z y); [contradiction|].
  destruct (le_dec z x); [|auto].
  exfalso. apply H0. transitivity z; auto.
Qed.

Add Parametric Relation (A : Type) `(Preord A) : A lt
    transitivity proved by lt_trans
      as preord_lt_rel.

Remark gt_trans `{Preord} : forall x y z,
    gt x y -> gt y z -> gt x z.
Proof.
  unfold gt; intros.
  destruct (le_total x y); [contradiction|].
  destruct (le_total y z); [contradiction|].
  destruct (le_dec x z); [|auto].
  exfalso. apply H0. transitivity z; auto.
Qed.

Add Parametric Relation (A : Type) `(Preord A) : A gt
    transitivity proved by gt_trans
      as preord_gt_rel.

Section Preord.
  Context {A : Type} {O : Preord A}.
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
  Global Instance Preord_EqDec : EqDec A eqv := eqv_dec.
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

  Lemma neqv_neq `{Ord} : forall x y, x =/= y -> x <> y.
  Proof. intros x y N c; apply N; subst; easy. Qed.

  Global Instance Ord_EquivDef {A} `{Ord A} : EqDec A eq.
  Proof.
    intros x y.
    destruct (eqv_dec x y).
    - left. apply eqv_eq. auto.
    - right. intro c. apply n. rewrite c. reflexivity.
  Defined.

  Definition ord_eq_dec {A} `{Ord A} : forall x y : A, { x = y } + { x <> y }
    := equiv_dec.
End Ord.
