Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.

Section Sorted.
  Context {A : Type} `{O: Ord A}.
  Open Scope ord_scope.

  (** What it means for a list to be sorted in increasing order. *)

  Inductive Sorted: list A -> Prop :=
  | Sorted_nil:
      Sorted nil
  | Sorted_cons: forall hd tl,
      (forall x, In x tl -> hd <= x) ->
      Sorted tl ->
      Sorted (hd :: tl).

  (** Lists of 1 element are sorted. *)

  Remark Sorted_1:
    forall x, Sorted (x :: nil).
  Proof.
    intros. constructor. intros. elim H. constructor.
  Qed.

  (** Lists of 2 ordered elements are sorted. *)

  Remark Sorted_2:
    forall x y, x <= y -> Sorted (x :: y :: nil).
  Proof.
    intros. constructor.
    intros. simpl in H0. destruct H0. subst x0. auto. contradiction.
    apply Sorted_1.
  Qed.
End Sorted.
