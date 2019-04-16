Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.Stable.

Section InsertionSort.
  Context {A : Type} {O : Preord A}.

  Fixpoint insert (x : A) (l : list A) :=
    match l with
    | nil => x :: nil
    | h::t => if le_dec x h then x :: h :: t else h :: insert x t
    end.

  Fixpoint sort (l: list A) : list A :=
    match l with
    | nil => nil
    | h::t => insert h (sort t)
    end.

  Lemma insert_perm: forall x l, Permutation (x::l) (insert x l).
  Proof.
    intros. revert x. induction l as [ | hd tl IH]; intros x.
    - simpl. apply Permutation_refl.
    - simpl. destruct (le_dec x  hd).
      + apply Permutation_refl.
      + rewrite perm_swap. apply Permutation_cons.
        reflexivity.
        apply IH.
  Qed.

  Theorem sort_perm: forall l, Permutation l (sort l).
  Proof.
    induction l as [ | hd tl IH].
    - simpl. apply Permutation_refl.
    - simpl. apply perm_skip with (x := hd) in IH.
      eapply perm_trans.
      + apply IH.
      + apply insert_perm.
  Qed.

  Lemma insert_sorted:
    forall a l, Sorted l -> Sorted (insert a l).
  Proof.
    intros a l Sl; revert a.
    induction Sl as [ | hd tl HIn HS IH]; intros a; [apply Sorted_1|].
    simpl; destruct (le_dec a hd).
    - apply Sorted_cons.
      intros x HIn'; simpl in HIn'.
      destruct HIn'; [subst; auto|].
      eapply le_trans. apply l. apply HIn; auto.
      constructor. apply HIn. apply HS.
    - apply Sorted_cons.
      intros x HIn'.
      apply Permutation_in with (l' := a::tl) in HIn';
        [|auto using insert_perm, Permutation_sym].
      destruct HIn'; [subst; apply lt_le_rev; auto|].
      apply HIn; auto.
      apply IH.
  Qed.

  Theorem sort_sorted: forall l, Sorted (sort l).
  Proof.
    induction l as [ | hd tl IH].
    - simpl. apply Sorted_nil.
    - simpl. apply insert_sorted. apply IH.
  Qed.

  Lemma insert_stable : forall a l, @Stable A eqv _ _ (a :: l) (insert a l).
  Proof.
    induction l as [|b l]; [apply Stable_skip; reflexivity|].
    cbn. destruct (le_dec a b).
    - reflexivity.
    - transitivity (b :: a :: l).
      apply Stable_swap.
      intros []. contradiction.
      apply Stable_skip. easy.
  Qed.

  Theorem sort_stable : forall l, @Stable A eqv _ _ l (sort l).
  Proof.
    induction l; [reflexivity|].
    cbn. transitivity (a :: sort l).
    apply Stable_skip. apply IHl.
    apply insert_stable.
  Qed.
End InsertionSort.
