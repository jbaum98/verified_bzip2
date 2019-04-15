Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.

Section Rewrites.
  Context {A : Type} `(EqDec A).

  Theorem equiv_dec_spec : forall a b, reflect (a === b) (a ==b b).
  Proof.
    intros.
    unfold equiv_decb.
    destruct (a == b); [left|right]; auto.
  Qed.

  Remark if_equiv_dec_b {B} : forall x y (t e : B),
      (if x == y then t else e) = (if x ==b y then t else e).
  Proof.
    intros.
    unfold equiv_decb.
    destruct (equiv_dec x y); auto.
  Qed.

  Theorem equiv_decb_refl : forall x,
      (x ==b x) = true.
  Proof.
    intros.
    destruct (equiv_dec_spec x x); [auto|].
    exfalso; apply n. reflexivity.
  Qed.
End Rewrites.


Hint Resolve equiv_dec_spec : eqdestruct.

Ltac eqdestruct X :=
  let H := fresh in
  let e := fresh "e" in
  evar (e: Prop);
  assert (H: reflect e X); subst e;
  [eauto with eqdestruct
  | destruct H as [H|H];
    try contradiction;
    try match goal with
    | H1 : ?a === ?b, H2 : ?a =/= ?b |- _ => contradiction
    | H1 : ?a === ?b, H2 : ?b =/= ?a |- _ => symmetry in H2; contradiction
    end
  ].
