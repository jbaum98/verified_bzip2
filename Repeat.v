Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.

Require Import BWTactics.

Section Repeat.
  Variable A : Type.
  Open Scope program_scope.

  Definition rep (f : A -> A) : nat -> A -> A :=
    fix rep n :=
      match n with
      | O => id
      | S m => f ∘ rep m
      end.

  Theorem rep_l : forall f n,
      f ∘ rep f n = rep f (S n).
  Proof. reflexivity. Qed.

  Theorem rep_r  : forall f n,
      rep f n ∘ f = rep f (S n).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl rep at 1. crewrite IHn.
      reflexivity.
  Qed.

  Theorem rep_z : forall f n z,
      rep f (S n) z = rep f n (f z).
  Proof.
    intros.
    pose proof rep_r f n.
    eapply equal_f with (x := z) in H.
    auto.
  Qed.

  Theorem rep_split : forall f n m,
      rep f n ∘ rep f m = rep f (n + m).
  Proof.
    intros.
    induction m.
    - simpl.
      rewrite Nat.add_0_r. reflexivity.
    - simpl. crewrite (rep_r f n). simpl; crewrite IHm.
      rewrite rep_l. f_equal. omega.
  Qed.
End Repeat.

Arguments rep {_}.

Section Invertible.
  Variables (A : Type) (f g : A -> A).
  Hypothesis HI: g ∘ f = id.

  Lemma rep_inv1_l : forall n,
      g ∘ rep f (S n) = rep f n.
  Proof.
    intros.
    simpl. crewrite HI.
    easy.
  Qed.

  Lemma rep_inv1_r : forall n,
      rep g (S n) ∘ f = rep g n.
  Proof.
    intros. induction n.
    - simpl. auto.
    - remember (S n) as n'; simpl; subst.
      crewrite IHn. apply rep_l.
  Qed.

  Theorem rep_inv_l : forall n m,
      n >= m -> rep g m ∘ rep f n  = rep f (n - m).
  Proof.
    intros n m. revert n. induction m; intros.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
    - simpl. crewrite (IHm n) by omega.
      destruct (n - m) as [|x] eqn:Hn; try omega.
      rewrite rep_inv1_l by auto.
      replace (n - S m) with x by omega.
      reflexivity.
  Qed.

  Theorem rep_inv_r : forall n m,
      m >= n -> rep g m ∘ rep f n = rep g (m - n).
  Proof.
    intros n m. induction n; intros.
    - simpl. rewrite Nat.sub_0_r.
      reflexivity.
    - crewrite <- rep_r. crewrite IHn by omega.
      destruct (m - n) as [|x] eqn:Hm; try omega.
      rewrite rep_inv1_r by auto.
      replace (m - S n) with x by omega.
      reflexivity.
  Qed.
End Invertible.

Section Preserves.
  Context {A : Type} (P : A -> Prop) (f : A -> A).
  Hypothesis HP : forall x, P x -> P (f x).

  Theorem rep_preserves : forall z n,
      P z -> P (rep f n z).
  Proof.
    intros z n Pz; revert z Pz.
    induction n; auto; intros.
    simpl; unfold compose. auto.
  Qed.
End Preserves.
