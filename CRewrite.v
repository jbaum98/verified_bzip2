Require Import Coq.Program.Combinators.
Require Import Coq.Program.Basics.
Require Import Coq.Classes.Morphisms.

Ltac lhs := match goal with |- ?lhs = _ => constr:(lhs) end.
Ltac rhs := match goal with |- _ = ?rhs => constr:(rhs) end.

Lemma compose_x_right {A B : Type} {p q : A -> B} :
  p = q -> forall (X : Type) (x : X -> A), p ∘ x = q ∘ x.
Proof. intros. f_equal. auto. Qed.

Ltac crewrite prf :=
  let H' := fresh "H'" in
  let t := type of prf in
  pose prf as H'; eapply compose_x_right in H'; rewrite ?compose_assoc in H';
  rewrite <- ?compose_assoc;
  let LHS := lhs in rewrite <- compose_id_right with (f := LHS);
  rewrite ?compose_assoc;
  let LHS := lhs in rewrite <- compose_id_left with (f := LHS);
  repeat (rewrite <- compose_assoc; try rewrite H');
  rewrite <- ?compose_assoc;
  let LHS := lhs in try rewrite compose_id_right;
  rewrite ?compose_assoc;
  let LHS := lhs in try rewrite compose_id_left;
  rewrite <- ?compose_assoc.
