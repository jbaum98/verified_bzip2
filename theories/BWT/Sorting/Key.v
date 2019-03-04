Require Import Coq.Lists.List.

Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.

Section KeyOrd.
  Context {A K : Type} `{O: Ord K}.

  Variable key : A -> K.

  Definition keyOrd : Ord A.
  Proof.
    apply Build_Ord with (le := fun x y => le (key x) (key y));
      intros; eauto using le_trans, le_total, le_dec.
  Defined.

  Remark key_le : forall x y,
      @le A keyOrd x y = @le K O (key x) (key y).
  Proof. reflexivity. Qed.

  Remark key_le_dec : forall x y,
      @le_dec A keyOrd x y = @le_dec K O (key x) (key y).
  Proof. reflexivity. Qed.

  Section Inv.
    Variable f : A -> A.
    Hypothesis HF : forall x, key (f x) = key x.

    Lemma key_insert_inv : forall x l,
       @insert A keyOrd (f x) (map f l) = map f (@insert A keyOrd x l).
    Proof.
      induction l; [reflexivity|].
      simpl. rewrite !HF.
      destruct (le_dec (key x) (key a)).
      - reflexivity.
      - simpl; f_equal.
        apply IHl.
    Qed.

    Theorem key_sort_inv : forall l,
        @sort A keyOrd (map f l) = map f (@sort A keyOrd l).
    Proof.
      induction l; [reflexivity|].
      simpl. rewrite <- key_insert_inv, IHl.
      reflexivity.
    Qed.
  End Inv.
End KeyOrd.

Section HdSort.
  Context {A : Type} `{O: Ord A}.

  Definition hdsort : list (list A) -> list (list A)
    := @sort _ (keyOrd (firstn 1)).

End HdSort.

Section Prefix.
  Context {A : Type} `{O: Ord A}.

  Local Arguments Sorted {_} _ _.

  Definition prefixSorted (n : nat) : list (list A) -> Prop
    := Sorted (keyOrd (firstn n)).

  Theorem prefixSorted_zero : forall l,
      prefixSorted 0 l.
  Proof.
    intros l. unfold prefixSorted.
    induction l; [apply Sorted_nil|].
    apply Sorted_cons.
    intros. rewrite key_le.
    apply lex_le_nil. apply IHl.
  Qed.
End Prefix.
