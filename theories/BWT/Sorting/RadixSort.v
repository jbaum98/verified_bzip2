Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.Stable.
Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Lib.Repeat.
Require Import BWT.Sorting.Key.
Require Import BWT.Lib.List.

Section RadixSort.
  Context {A : Type} {O : Ord A}.

  Open Scope program_scope.

  Definition radixsort (l : list (list A)) (n : nat): list (list A)
    := rep (hdsort ∘ map rrot) n l.

  Lemma radixsort_perm_ind : forall n l,
      Permutation (rep (map rrot) n l) (rep (hdsort ∘ map rrot) n l).
  Proof.
    induction n; intro l; [reflexivity|].
    cbn; symmetry.
    apply Permutation_trans with (l' := map rrot (rep (hdsort ∘ map rrot) n l)).
    symmetry. apply sort_perm.
    apply Permutation_map.
    symmetry. apply IHn.
  Qed.

  Theorem radixsort_perm : forall n l,
      Forall (fun x => length x = n) l ->
      Permutation l (radixsort l n).
  Proof.
    intros n l HL.
    unfold radixsort.
    rewrite <- map_id at 1.
    rewrite map_forall_eq with (g := rep rrot n).
    rewrite <- rep_map.
    apply radixsort_perm_ind.
    eapply Forall_impl; [|apply HL].
    cbn; intros a HN.
    rewrite <- HN. symmetry. apply rrot_rep_id.
  Qed.

End RadixSort.
