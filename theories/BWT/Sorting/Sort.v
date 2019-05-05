Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.StablePerm.

Section Sort.
  Context {A : Type}.

  Implicit Types (f g : list A -> list A).

  Section Preord.
    Context {O : Preord A}.

    Definition Sort f :=
      forall l, Sorted (f l) /\ Permutation (f l) l.

    Definition StableSort f :=
      forall l, Sorted (f l) /\ StablePerm (f l) l.

    Corollary StableSort_Sort : forall f,
        StableSort f -> Sort f.
    Proof.
      intros f HF l; destruct (HF l).
      split; [|apply StablePerm_Perm]; easy.
    Qed.

    Corollary StableSort_unique : forall f g,
        StableSort f -> StableSort g ->
        (forall l, f l = g l).
    Proof.
      intros f g HF HG l.
      apply StablePerm_Sorted_eq; [apply HF|apply HG|].
      transitivity l; [|symmetry]; [apply HF| apply HG].
    Qed.
  End Preord.

  Section Leibniz.
    Context `{O : Ord A}.

    Theorem Sort_StableSort_Ord : forall f,
        Sort f <-> StableSort f.
    Proof.
      split; [|apply StableSort_Sort].
      intros HF.
      split; [apply HF|].
      apply all_perm_stable; [apply eqv_eq|apply HF].
    Qed.

    Theorem Sort_Ord_unique : forall f g,
        Sort f -> Sort g ->
        (forall l, f l = g l).
    Proof.
      setoid_rewrite Sort_StableSort_Ord.
      exact StableSort_unique.
    Qed.
  End Leibniz.
End Sort.
