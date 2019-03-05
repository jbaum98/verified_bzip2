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
Require Import BWT.Columns.
Require Import BWT.Sorting.Lexicographic.

Section RadixSort.
  Context {A : Type} {O : Ord A}.

  Open Scope program_scope.

  Definition radixsort (l : list (list A)) (n : nat): list (list A)
    := rep (hdsort ∘ map rrot) n l.

  Lemma radixsort_perm_ind : forall n l,
      Permutation (rep (map rrot) n l) (radixsort l n).
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

  Local Arguments eqv {_} _.
  Local Arguments le {_} _.
  Local Arguments lt {_} _.
  Local Arguments StablePerm {_} _ {_}.
  Local Arguments tl {_}.

  Theorem hdsort_sorted_S : forall n colmat colmat',
      StablePerm (eqv (keyOrd (firstn 1))) colmat colmat' ->
      PrefixSorted n (map tl colmat) ->
      PrefixSorted 1 colmat' ->
      PrefixSorted (S n) colmat'.
  Proof.
    intros n colmat colmat' HSP.
    induction HSP as [| x colmat colmat' | |]; intros HPSmat HPScolmat'.
    - apply Sorted_nil.
    - apply Sorted_cons.
      intros b HB.
      inversion HPScolmat'; subst; clear HPScolmat'.
      specialize (H1 b HB).
      apply lt_spec in H1.
      destruct H1.
      + rewrite key_le.
        unfold le, Ord_list_lex.
        apply lex_le_cons_lt.





    assert (HSP : @StablePerm _ (@eqv _ (keyOrd (firstn 1))) _ (prepend_col col mat) (hdsort (prepend_col col mat)))
           by apply sort_stable.
    remember (prepend_col col mat) as bigmat.
    remember (hdsort (prepend_col col mat)) as bigmat'.
    revert Heqbigmat Heqbigmat'.
    induction HSP as [|x mattl mat' | x y mattl | mattl mat' mat''].
    - intros. apply Sorted_nil.
    - intros Hbigmat Hbigmat' n HPS.
      unfold hdsort.
      rewrite <- HL'.
      apply Sorted_cons.
      pose proof (@sort_sorted _ (keyOrd (firstn 1)) (x :: l)).
      inversion H. cbn in HL'.
      rewrite <- HL' in H1.
      inversion H1.
      cbn in HL'.
      rewrite <- HL' in H0.
      inversion H0; subst.
      apply H1.

  Theorem radixsort_sorted : forall n l,
      Forall (fun x => length x = n) l ->
      Sorted (radixsort l n).
  Admitted.
End RadixSort.
