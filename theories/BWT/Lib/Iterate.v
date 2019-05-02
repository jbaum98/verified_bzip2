Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.Repeat.

Import ListNotations.

Section Iterate.
  Context {A : Type}.

  (* Apply a function f to an initial input z, n times.
     iter f n z = [z; f z; f (f z); ... f^n z]
   *)
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

  Theorem iter_nth : forall f n z i d,
      i < n -> nth i (iter f n z) d = rep f i z.
  Proof.
    intros f n z i. revert f n z.
    induction i; intros.
    - destruct n.
      + omega.
      + reflexivity.
    - destruct n; try omega.
      rewrite <- rep_r. apply IHi. omega.
  Qed.

  Theorem iter_length : forall f n z,
      length (iter f n z) = n.
  Proof.
    induction n; intros.
    - simpl. reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.
End Iterate.
