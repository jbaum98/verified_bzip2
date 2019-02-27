Require Import Coq.Lists.List.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Mergesort.
Require Import BWT.Sorting.Lexicographic.

Section KeyOrd.
  Context {K : Type} `{O: Ord K}.

  Definition keyOrd {A : Type} (key : A -> K) : Ord A.
  Proof.
    apply Build_Ord with (le := fun x y => le (key x) (key y));
      intros; eauto using le_trans, le_total, le_dec.
  Defined.
End KeyOrd.

Section HdSort.
  Context {A : Type} `{O: Ord A}.

  Program Definition hdsort : list (list A) -> list (list A)
    := @mergesort _ (keyOrd (firstn 1)).

End HdSort.
