Supplementary Materials
=======================

This directory contains the Coq sources described in the paper.

To compile the Coq sources for the main theorems, run
```sh
make -j$(nproc)
```
We have tested compilation with Coq 8.8, 8.9, and 8.10.

The main theorems are:

- `unwt_correct` (BWT/BurrowsWheeler.v:200) which proves that `unbwt` satisfies its specification.

   ```coq
   Theorem unbwt_correct : forall xs : list A,
       unbwt (bwn xs) (bwl xs) = xs.
   ```
- `radixsort_correct` (BWT/Sorting/RadixSort.v:168) which proves that `radixsort` satisfies its specification.

  ```coq
  Theorem radixsort_correct : forall n m,
      Forall (fun x => length x = n) m ->
      Sorted (radixsort m n) /\ Permutation (radixsort m n) m.
  ```
- `StablePerm_Sorted_eq` (BWT/Sorting/StablePerm.v:528) which proves that there is only one stable permutation of any list.

  ```coq
  Theorem StablePerm_Sorted_eq : forall l l',
      Sorted l -> Sorted l' -> StablePerm l l' ->
      l = l'.
  ```
