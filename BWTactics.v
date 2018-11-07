Require Export Coq.Program.Combinators.
Require Export Coq.Program.Basics.

Lemma compose_x_right {A B : Type} {p q : A -> B} :
  p = q -> forall (X : Type) (x : X -> A), p ∘ x = q ∘ x.
Proof. intros. f_equal. auto. Qed.

Ltac rhs H :=
  match type of H with
  | _ = ?rhs => constr:(rhs)
  end.

Ltac crewrite_main H' :=
  (* Reverse normalize H' *)
  rewrite ?compose_assoc in H';

  (* Normalize c and compose id on either side *)
  match goal with
  | |- context [?f ∘ ?g] =>
    let c := constr:(f ∘ g) in

    rewrite <- (compose_id_right _ _ c), <- (compose_id_left _ _ c);
    rewrite <- ?compose_assoc;

    (* Repatedly move one function over and try to rewrite by H' *)
    progress (repeat (rewrite H' || rewrite compose_assoc);
              rewrite <- ?compose_assoc);

    (* Remove the ids *)
    rewrite <- ?compose_assoc, ?compose_id_right;
    rewrite ?compose_assoc, ?compose_id_left;
    rewrite <- ?compose_assoc
  end.

Ltac crewrite_forward prf b :=
  let H' := fresh "H'" in
  epose prf as H'; eapply compose_x_right in H';
  [crewrite_main H' | b..]; clear H'.

Ltac crewrite_back prf b :=
  let H' := fresh "H'" in
  epose prf as H'; eapply compose_x_right in H'; eapply eq_sym in H';
  [crewrite_main H' | b..]; clear H'.

Tactic Notation "crewrite" uconstr(P) "by" tactic(b) := crewrite_forward P b.
Tactic Notation "crewrite" "->" uconstr(P) "by" tactic(b) := crewrite_forward P b.
Tactic Notation "crewrite" "<-" uconstr(P) "by" tactic(b) := crewrite_back P b.

Tactic Notation "crewrite" uconstr(P) := crewrite_forward P idtac.
Tactic Notation "crewrite" "->" uconstr(P) := crewrite_forward P idtac.
Tactic Notation "crewrite" "<-" uconstr(P) := crewrite_back P idtac.

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
  Variables a b c : A -> A.
  Variable R : (A -> A) -> Prop.
  Hypothesis H : a ∘ b = c.

  Goal c ∘ c ∘ id = a ∘ b ∘ a ∘ b.
  Proof.
    crewrite H.
    crewrite H.
    crewrite <- H.
    crewrite <- H.
    reflexivity.
  Qed.
End Test.
