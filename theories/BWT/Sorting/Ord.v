Require Import Coq.Bool.Sumbool.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Setoids.Setoid.

(** A type equipped with a total, decidable preorder. *)

Class Ord (A : Type):=
  { le : A -> A -> Prop;
    le_trans : forall x y z, le x y -> le y z -> le x z;
    le_total : forall x y, le x y \/ le y x;
    le_dec : forall x y, {le x y} + {~le x y};
  }.

Lemma le_refl {A} `{Ord A} : forall x, le x x.
Proof.
  intros. destruct (le_total x x); auto.
Qed.

Lemma le_not {A} `{Ord A} : forall x y, ~(le x y) -> le y x.
Proof.
  intros. destruct (le_total x y). contradiction. auto.
Qed.

Definition le_decb {A} `{Ord A} x y := proj1_sig (bool_of_sumbool (le_dec x y)).

Definition ge {A} `{Ord A} x y := le y x.
Definition lt {A} `{Ord A} x y := ~ (le y x).
Definition gt {A} `{Ord A} x y := ~ (le x y).

(** Two elements are equivalent if they compare [le] in both directions. *)

Definition eqv {A} `{Ord A} (x y : A) : Prop := le x y /\ le y x.

Program Definition eqv_dec {A} `{Ord A} (x y : A) : {eqv x y} + {~ eqv x y} :=
  if le_dec x y then
    if le_dec y x then left _
    else right _
  else right _.
Solve All Obligations with unfold eqv; intuition eauto.

Definition eqv_decb {A} `{Ord A} x y := proj1_sig (bool_of_sumbool (eqv_dec x y)).

Section Equiv.
  Context {A} `{Ord A}.

  Theorem eqv_refl : forall x, eqv x x.
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
      eqv x y <-> (le x y /\ le y x).
  Proof. reflexivity. Qed.

  (* Instance EqDec_eqv : EqDec A eqv | 0 := eqv_dec. *)

  Theorem eqv_subst : forall x y z, eqv x y -> (eqv x z <-> eqv y z).
  Proof.
    intros.
    repeat rewrite eqv_def in *.
    intuition; eauto using le_trans.
  Qed.
End Equiv.

Section Lt.
  Context {A} `{Ord A}.

  Theorem lt_spec : forall x y, le x y <-> lt x y \/ eqv x y.
  Proof.
    intros.
    destruct (eqv_dec x y); unfold lt, eqv in *; intuition; eauto using le_not.
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
    match goal with [ H : ~ le _ _ |- _ ] => apply le_not in H end.
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
