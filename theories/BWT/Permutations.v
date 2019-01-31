Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.

Section Permutations.
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
End Permutations.

Section PermutationsF.
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
      l <> nil -> f l <> nil.
  Proof.
    intros. intro contra.
    specialize (HF l).
    rewrite contra in HF.
    apply Permutation_sym in HF.
    apply Permutation_nil in HF.
    rewrite HF in H. contradiction.
  Qed.
End PermutationsF.
