Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import Coq.Lists.List.ListNotations.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.StablePerm.
Require Import BWT.Lib.Sumbool.
Require Import BWT.Lib.Permutation.

Section InsertionSort.
  Context {A : Type} {O : Preord A}.

  Fixpoint insert (x : A) (l : list A) :=
    match l with
    | [] => [x]
    | h :: t =>
      if le_dec x h then x :: h :: t else h :: insert x t
    end.

  Definition sort : list A -> list A :=
    fold_right insert [].

  Lemma insert_perm: forall x l,
      Permutation (x :: l) (insert x l).
  Proof.
    intros; revert x; induction l as [|h t IH]; intros x;
      [reflexivity|].
    cbn. destruct (le_dec x h); [reflexivity|].
    rewrite perm_swap.
    apply Permutation_cons; [easy|apply IH].
  Qed.

  Theorem sort_perm: forall l, Permutation l (sort l).
  Proof.
    induction l as [|h t IH]; [reflexivity|].
    cbn.
    transitivity (h :: sort t); [apply perm_skip; easy|].
    apply insert_perm.
  Qed.

  Lemma insert_forall_le : forall x l,
      Forall (le x) l -> insert x l = x :: l.
  Proof.
    intros x l HF.
    destruct l as [|h t]; [easy|].
    cbn. rewrite if_true by (eapply Forall_inv; apply HF).
    reflexivity.
  Qed.

  Lemma insert_sorted: forall x l,
      Sorted l -> Sorted (insert x l).
  Proof.
    intros x l Sl; revert x.
    induction Sl as [|a t HF HS IH]; intros x; [apply Sorted_1|].
    cbn; destruct (le_dec x a).
    - revert IH; setoid_rewrite SortedLocal_iff; intros IH.
      apply SortedLocal_cons; [|easy].
      rewrite <- insert_forall_le by easy.
      apply IH.
    - apply Sorted_cons; [|easy].
      apply Permutation_forall with (l := x :: t);
        [apply insert_perm|].
      constructor; [apply lt_le; easy|easy].
  Qed.

  Theorem sort_sorted: forall l, Sorted (sort l).
  Proof.
    induction l as [ | hd tl IH].
    - simpl. apply Sorted_nil.
    - simpl. apply insert_sorted. apply IH.
  Qed.

  Lemma insert_stable : forall a l, @StablePerm A eqv _ _ (a :: l) (insert a l).
  Proof.
    induction l as [|b l]; [apply StablePerm_skip; reflexivity|].
    cbn. destruct (le_dec a b).
    - reflexivity.
    - transitivity (b :: a :: l).
      apply StablePerm_swap.
      intros []. contradiction.
      apply StablePerm_skip. easy.
  Qed.

  Theorem sort_stable : forall l, @StablePerm A eqv _ _ l (sort l).
  Proof.
    induction l; [reflexivity|].
    cbn. transitivity (a :: sort l).
    apply StablePerm_skip. apply IHl.
    apply insert_stable.
  Qed.
End InsertionSort.
