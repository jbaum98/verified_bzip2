Require Export Coq.Program.Combinators.
Require Export Coq.Program.Basics.
Require Import Setoid.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Lemma compose_x_right {A B : Type} (p q : A -> B) :
  impl (p = q) (forall (X : Type) (x : X -> A), p ∘ x = q ∘ x).
Proof. intro. intros. f_equal. auto. Qed.

(** We will use the support for subrelations to inform the tactic that
    pointwise equality and regular equality coincide. Now every
    morphism for one relation will be a morphism for the other. As
    every Coq function is a morphism for Leibniz equality, that'll
    make the pointwise extension available as as an equivalent for
    every argument of functional type. When we rewrite under a lambda
    as argument of [f : (A -> A) -> A], the tactic generates a
    constraint for [f] to be a morphism for pointwise equivalent
    functions, which will reduce to be a morphism for Leibniz-equal
    functions which is in turn trivial. *)

Require Import Setoid Morphisms Program.Syntax.

(** The [respectful RA RB] relation is reflexive when [RA] is included
in equality and
    [RB] includes equality. This will be used to show, e.g that
[Reflexive (pointwise_relation A eq ==> eq)] *)

Generalizable All Variables.

Instance refl_respectful {A B : Set} `(sa : subrelation A RA eq)
`(sb : subrelation B eq RB) : Reflexive (RA ++> RB)%signature.
Proof. intros. intros f x x' Hxx'. apply sb. f_equal. apply (sa _ _
Hxx'). Qed.

(** The same lemma in terms of [subrelation] only that can be applied
recursively. *)

Instance subrel_eq_respect {A B : Set} `(sa : subrelation A RA eq)
`(sb : subrelation B eq RB) :
   subrelation eq (respectful RA RB).
Proof. intros. intros f g Hfg. subst. intros a a' Raa'. apply sb.
f_equal. apply (sa _ _ Raa'). Qed.

(** Using extensionality, we can show that any two pointwise equal
functions are Leibniz-equal: *)

Instance pointwise_eq_ext {A B : Set} `(sb : subrelation B RB (@eq
B)) : subrelation (pointwise_relation A RB) eq.
Proof. intros. intros f g Hfg. apply functional_extensionality. intros x. apply
sb. apply (Hfg x). Qed.

(** Conversely, two equal functions are trivially pointwise-equal.
This instance and [refl_respectful]
    should be in the library. *)

Instance eq_pointwise {A B : Set} `(sb : subrelation B (@eq B) RB) :
subrelation eq (pointwise_relation A RB).
Proof. intros. intros f g Hfg x. apply sb. subst f. reflexivity. Qed.

Create HintDb compose_assoc.
Hint Rewrite compose_assoc : compose_assoc.

Ltac crewrite_main prf k :=
    let HCons := fresh "HCons" in
    let HNil := fresh "HNil" in
    pose proof prf as HCons;
    setoid_rewrite compose_x_right in HCons;
    rewrite_strat any (outermost (hints compose_assoc)) in HCons;

    pose proof prf as HNil;
    rewrite_strat any (outermost (hints compose_assoc)) in HNil;

    rewrite ?compose_assoc;
    k HCons HNil;
    rewrite <- ?compose_assoc;
    clear HCons; clear HNil.

Tactic Notation "cerewrite" "->" uconstr(P) "in" ident(H) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite -> HCons in H || erewrite -> HNil in H); [|b..] ).
Tactic Notation "crewrite" "<-" uconstr(P) "in" ident(H) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite <- HCons in H || erewrite <- HNil in H); [|b..]).
Tactic Notation "crewrite" uconstr(P) "in" ident(H) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite HCons in H || erewrite HNil in H); [|b..]).

Tactic Notation "crewrite" "->" uconstr(P) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite -> HCons || erewrite -> HNil); [|b..]).
Tactic Notation "crewrite" "<-" uconstr(P) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite <- HCons || erewrite <- HNil); [|b..]).
Tactic Notation "crewrite" uconstr(P) "by" tactic(b) :=
  crewrite_main P ltac:(fun HCons HNil => (erewrite HCons || erewrite HNil); [|b..]).

Tactic Notation "crewrite" "->" uconstr(P) "in" ident(H) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite -> HCons in H || erewrite -> HNil in H).
Tactic Notation "crewrite" "<-" uconstr(P) "in" ident(H) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite <- HCons in H || erewrite <- HNil in H).
Tactic Notation "crewrite" uconstr(P) "in" ident(H) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite HCons in H || erewrite HNil in H).

Tactic Notation "crewrite" "->" uconstr(P) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite -> HCons || erewrite -> HNil).
Tactic Notation "crewrite" "<-" uconstr(P) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite <- HCons || erewrite <- HNil).
Tactic Notation "crewrite" uconstr(P) :=
  crewrite_main P ltac:(fun HCons HNil => erewrite HCons || erewrite HNil).

Ltac xrewrite_forward prf b :=
  let H := fresh "H" in
  epose prf as H;
  eapply equal_f in H; unfold compose in H; unfold id in H;
  rewrite H by b; clear H.

Ltac xrewrite_back prf b :=
  let H := fresh "H" in
  epose prf as H;
  eapply equal_f in H; unfold compose in H; unfold id in H;
  rewrite <- H by b; clear H.

Ltac xrewrite_forward_id prf b x' :=
  let H := fresh "H" in
  epose prf as H;
  apply equal_f with (x := x') in H; unfold compose in H; unfold id in H;
  rewrite H by b; clear H.

Ltac xrewrite_back_id prf b x' :=
  let H := fresh "H" in
  epose prf as H;
  apply equal_f with (x := x') in H; unfold compose in H; unfold id in H;
  rewrite <- H by b; clear H.

Tactic Notation "xrewrite" uconstr(P) "by" tactic(b) := xrewrite_forward P b.
Tactic Notation "xrewrite" "->" uconstr(P) "by" tactic(b) := xrewrite_forward P b.
Tactic Notation "xrewrite" "<-" uconstr(P) "by" tactic(b) := xrewrite_back P b.

Tactic Notation "xrewrite" uconstr(P) := xrewrite_forward P idtac.
Tactic Notation "xrewrite" "->" uconstr(P) := xrewrite_forward P idtac.
Tactic Notation "xrewrite" "<-" uconstr(P) := xrewrite_back P idtac.

Tactic Notation "xrewrite" uconstr(P) "with" ident(x) "by" tactic(b)
  := xrewrite_forward_id P b x.
Tactic Notation "xrewrite" "->" uconstr(P) "with" ident(x) "by" tactic(b)
  := xrewrite_forward_id P b x.
Tactic Notation "xrewrite" "<-" uconstr(P) "with" ident(x) "by" tactic(b)
  := xrewrite_back_id P b x.

Tactic Notation "xrewrite" uconstr(P) "with" ident(x)
  := xrewrite_forward_id P idtac x.
Tactic Notation "xrewrite" "->" uconstr(P) "with" ident(x)
  := xrewrite_forward_id P idtac x.
Tactic Notation "xrewrite" "<-" uconstr(P) "with" ident(x)
  := xrewrite_back_id P idtac x.

Ltac compose_pop_right :=
  rewrite <- ?compose_assoc;
  match goal with
  | |- context [ (?f ∘ ?g) ?x] =>
    let a := constr:((f ∘ g) x) in
    let b := constr:(f (g x)) in
    replace a with b by reflexivity
  end.

Ltac compose_pop_left :=
  rewrite ?compose_assoc;
  match goal with
  | |- context [ (?f ∘ ?g) ?x] =>
    let a := constr:((f ∘ g) x) in
    let b := constr:(f (g x)) in
    replace a with b by reflexivity
  end.

Ltac compose_push_left :=
  rewrite ?compose_assoc;
  match goal with
  | |- context [?f ((?g ∘ ?h) ?x)] =>
    let a := constr:(f ((g ∘ h) x)) in
    let b := constr:((f ∘ g ∘ h) x) in
    replace a with b by reflexivity
  end.

Ltac compose_var x :=
  match goal with
  | |- context [?f (?g x)] =>
    let a := constr:(f (g x)) in
    let b := constr:((f ∘ g) x) in
    replace a with b by reflexivity
  end.

Section Test.
  Variable A : Type.
  Variables a b c d : A -> A.
  Variable R : (A -> A) -> Prop.
  Hypothesis H : (forall x : A, x = x) -> a ∘ b ∘ b ∘ b = c.
  Hypothesis H' : c = d.


  Goal c ∘ c ∘ id = a ∘ b ∘ b ∘ b.
  Proof.
    crewrite H by reflexivity.
    crewrite <- H by reflexivity.
    crewrite <- H by reflexivity.
    crewrite <- H by reflexivity.
    crewrite <- H in H' by easy.
  Abort.
End Test.
