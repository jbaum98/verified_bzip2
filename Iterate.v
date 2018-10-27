Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Repeat.

Import ListNotations.

Section Iterate.
  Context {A : Type}.

  Fixpoint iter (f : A -> A) (n : nat) (z : A) : list A :=
    match n with
    | O   => [z]
    | S m => z :: iter f m (f z)
    end.

  Theorem iter_preserves : forall f n z (P: A -> Prop),
      (forall x, P x -> P (f x)) -> P z -> Forall P (iter f n z).
  Proof.
    intros f n z P HPreserve Pz. revert z Pz.
    induction n.
    - constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Theorem iter_nth : forall f n z i d,
      i <= n -> nth i (iter f n z) d = rep f i z.
  Proof.
    intros f n z i. revert f n z.
    induction i; intros.
    - destruct n.
      + reflexivity.
      + reflexivity.
    - destruct n; try omega.
      rewrite rep_z. apply IHi. omega.
  Qed.

  Theorem iter_length : forall f n z,
      length (iter f n z) = S n.
  Proof.
    induction n; intros.
    - simpl. reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.
End Iterate.
