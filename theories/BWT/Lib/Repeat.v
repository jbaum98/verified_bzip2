Require Import Coq.Arith.PeanoNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Section Repeat.
  Context {A : Type}.

  Fixpoint rep (f : A -> A) (n : nat) (z : A) : A :=
    match n with
    | O => z
    | S m => f (rep f m z)
    end.

  Theorem rep_z : forall f n z,
      rep f (S n) z = rep f n (f z).
  Proof.
    induction n; intros.
    - reflexivity.
    - remember (S n) as n'. simpl. subst.
      rewrite IHn. easy.
  Qed.

  Theorem rep_l : forall f n z,
      f (rep f n z) = rep f (S n) z.
  Proof. reflexivity. Qed.

  Theorem rep_r  : forall f n z,
      rep f n (f z) = rep f (S n) z.
  Proof.
    intros. symmetry; apply rep_z.
  Qed.

  Theorem rep_split : forall f n m z,
      rep f n (rep f m z) = rep f (n + m) z.
  Proof.
    intros.
    induction m.
    - simpl.
      rewrite Nat.add_0_r. reflexivity.
    - simpl; rewrite rep_r. simpl; rewrite IHm.
      rewrite rep_l.
      f_equal. omega.
  Qed.
End Repeat.

Section Invertible.
  Context {A : Type} (f g : A -> A).
  Hypothesis HI: forall x, g (f x) = x.

  Lemma rep_inv1_l : forall n z,
      g (rep f (S n) z) = rep f n z.
  Proof.
    intros.
    simpl. rewrite HI.
    easy.
  Qed.

  Lemma rep_inv1_r : forall n z,
      rep g (S n) (f z) = rep g n z.
  Proof.
    intros. induction n.
    - simpl. auto.
    - remember (S n) as n'; simpl; subst.
      rewrite IHn. apply rep_l.
  Qed.

  Theorem rep_inv_l : forall n m z,
      n >= m -> rep g m (rep f n z) = rep f (n - m) z.
  Proof.
    intros n m. revert n. induction m; intros.
    - simpl. rewrite Nat.sub_0_r. reflexivity.
    - simpl. rewrite IHm by omega.
      destruct (n - m) as [|x] eqn:Hn; try omega.
      rewrite rep_inv1_l by auto.
      replace (n - S m) with x by omega.
      reflexivity.
  Qed.

  Theorem rep_inv_r : forall n m z,
      m >= n -> rep g m (rep f n z) = rep g (m - n) z.
  Proof.
    intros n m. induction n; intros.
    - simpl. rewrite Nat.sub_0_r.
      reflexivity.
    - rewrite <- rep_r, IHn by omega.
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
    simpl. auto.
  Qed.
End Preserves.

Section Map.
  Context {A : Type}.

  Variable f : A -> A.

  Lemma rep_map_cons : forall n a l,
      rep (map f) n (a :: l) = rep f n a :: rep (map f) n l.
  Proof.
    induction n; intros a l; [reflexivity|].
    cbn. rewrite IHn. cbn. reflexivity.
  Qed.

  Theorem rep_map : forall n l,
      rep (map f) n l = map (rep f n) l.
  Proof.
    induction l.
    - cbn. apply rep_preserves; [|reflexivity].
      intros; subst; reflexivity.
    - cbn. rewrite <- IHl.
      apply rep_map_cons.
  Qed.
End Map.
