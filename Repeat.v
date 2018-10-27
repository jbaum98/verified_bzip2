Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.omega.Omega.

Section Repeat.
  Open Scope program_scope.

  Context {A : Type}.

  Fixpoint rep (f : A -> A) (n : nat) : A -> A :=
    match n with
    | O => id
    | S m => f ∘ rep f m
    end.

  Theorem rep_z : forall f n z,
      rep f (S n) z = rep f n (f z).
  Proof.
    induction n; intros.
    - reflexivity.
    - remember (S n) as n'. simpl. subst.
      unfold compose.
      rewrite IHn. easy.
  Qed.

  Theorem rep_l : forall f n,
      f ∘ rep f n = rep f (S n).
  Proof. reflexivity. Qed.

  Theorem rep_r  : forall f n,
      rep f n ∘ f = rep f (S n).
  Proof.
    intros.
    extensionality z. unfold compose.
    symmetry; apply rep_z.
  Qed.

  Theorem rep_split : forall f n m,
      rep f n ∘ rep f m = rep f (n + m).
  Proof.
    intros.
    induction m.
    - simpl. rewrite compose_id_right.
      rewrite Nat.add_0_r. reflexivity.
    - simpl. rewrite <- compose_assoc, rep_r.
      simpl. rewrite compose_assoc. rewrite IHm.
      rewrite rep_l.
      f_equal. omega.
  Qed.
End Repeat.

Section Invertible.
  Open Scope program_scope.

  Context {A : Type} (f g : A -> A).
  Hypothesis HI: g ∘ f = id.

  Lemma rep_inv1_l : forall n,
      g ∘ rep f (S n) = rep f n.
  Proof.
    intros.
    simpl. rewrite <- compose_assoc, HI.
    apply compose_id_left.
  Qed.

  Lemma rep_inv1_r : forall n,
      rep g (S n) ∘ f = rep g n.
  Proof.
    intros. induction n.
    - simpl. rewrite compose_id_right. auto.
    - remember (S n) as n'; simpl; subst.
      rewrite compose_assoc. rewrite IHn.
      apply rep_l.
  Qed.

  Theorem rep_inv_l : forall n m,
      n >= m -> rep g m ∘ rep f n = rep f (n - m).
  Proof.
    intros n m. revert n. induction m; intros.
    - simpl. rewrite compose_id_left, Nat.sub_0_r.
      reflexivity.
    - simpl. rewrite compose_assoc, IHm by omega.
      destruct (n - m) as [|x] eqn:Hn; try omega.
      rewrite rep_inv1_l by auto.
      replace (n - S m) with x by omega.
      reflexivity.
  Qed.

  Theorem rep_inv_r : forall n m,
      m >= n -> rep g m ∘ rep f n = rep g (m - n).
  Proof.
    intros n m. induction n; intros.
    - simpl. rewrite compose_id_right. rewrite Nat.sub_0_r.
      reflexivity.
    - rewrite <- rep_r, <- compose_assoc, IHn by omega.
      destruct (m - n) as [|x] eqn:Hm; try omega.
      rewrite rep_inv1_r by auto.
      replace (m - S n) with x by omega.
      reflexivity.
  Qed.
End Invertible.

Section Preserves.
  Context {A : Type} (P : A -> Prop) (f : A -> A).
  Hypothesis HP : forall x, P x -> P (f x).

  Theorem repeat_n_preserves : forall z n,
      P z -> P (rep f n z).
  Proof.
    intros z n Pz; revert z Pz.
    induction n; auto; intros.
    simpl; unfold compose. auto.
  Qed.
End Preserves.
