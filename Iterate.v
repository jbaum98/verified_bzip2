Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Repeat.
Require Import Pointfree.

Import ListNotations.

Section Iterate.
  Variable A : Type.

  Fixpoint iter (f : A -> A) (n : nat) (z : A) : list A :=
    match n with
    | O   => []
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

  Theorem iter_nth : forall f n i d,
      i < n -> nth' i d ∘ iter f n = rep f i.
  Proof.
    intros f n i. revert f n.
    induction i; intros.
    - destruct n.
      + omega.
      + reflexivity.
    - extensionality z. unfold compose.
      destruct n; [omega|]. simpl iter; simpl nth'.
      apply lt_S_n in H.
      rewrite <- rep_r.
      crewrite <- (IHi f n d); [|eauto..].
      reflexivity.
  Qed.

  Theorem iter_length : forall f n z,
      length (iter f n z) = n.
  Proof.
    induction n; intros.
    - simpl. reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.
End Iterate.

Arguments iter {_}.
