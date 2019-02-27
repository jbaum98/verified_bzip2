Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Import Coq.Lists.List.ListNotations.

Section Props.
  Context {A : Type} {P : A -> Prop} .
  Variables l l' : list A.
  Hypothesis HP : Permutation l l'.

  Theorem Permutation_exists :
    Exists P l -> Exists P l'.
  Proof.
    intros HE.
    apply Exists_exists.
    apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
    eauto using Permutation_in.
  Defined.

  Theorem Permutation_forall :
    Forall P l -> Forall P l'.
  Proof.
    intros.
    apply Forall_forall.
    intros a HA.
    apply Permutation_in with (l' := l) in HA; auto using Permutation_sym.
    revert a HA.
    apply Forall_forall.
    auto.
  Qed.
End Props.

Section Preserve.
  Context {A : Type} (f : list A -> list A).
  Hypothesis HF: forall l, Permutation l (f l).

  Theorem f_perm : forall (x y : list A),
      Permutation x y -> Permutation x (f y).
  Proof.
    assert (LP: forall l, Permutation (f l) l). {
      intro l. apply Permutation_sym. apply HF.
    }
    intros. inversion H; subst; clear H.
    - apply HF.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply perm_skip. apply Permutation_sym. auto.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      repeat constructor.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply Permutation_sym. eapply perm_trans; eauto.
  Qed.

  Theorem f_perm' : forall (x y : list A),
      Permutation x y -> Permutation (f x) (f y).
  Proof.
    intros.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym. apply H.
  Qed.

  Theorem f_nonempty : forall l,
      l <> [] -> f l <> [].
  Proof.
    intros. intro contra.
    specialize (HF l).
    rewrite contra in HF.
    apply Permutation_sym in HF.
    apply Permutation_nil in HF.
    rewrite HF in H. contradiction.
  Qed.
End Preserve.

Lemma Permutation_cons_in {A} : forall (x y : A) xs ys,
    Permutation (x :: xs) (y :: ys) ->
    (x = y \/ In x ys).
Proof.
  intros x y xs ys P.
  eapply Permutation_in in P.
  cbn in P. destruct P as [E | I]; eauto.
  cbn; eauto.
Qed.


(** A property of permutations that is missing from the List library:
  a permutation of a list without duplicates is a list without duplicates. *)

Lemma Permutation_NoDup {A}:
  forall (l l': list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; intros.
  constructor.

  inversion H0; subst. constructor; auto.
  red; intro; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.

  inversion H; subst. inversion H3; subst.
  constructor. simpl. simpl in H2. intuition.
  constructor. simpl in H2. intuition. auto.

  auto.
Qed.
