Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.

Section Sorted.
  Context {A : Type} `{O: Ord A}.

  (** What it means for a list to be sorted in increasing order. *)

  Inductive Sorted: list A -> Prop :=
  | Sorted_nil:
      Sorted nil
  | Sorted_cons: forall hd tl,
      (forall x, In x tl -> le hd x) ->
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
    forall x y, le x y -> Sorted (x :: y :: nil).
  Proof.
    intros. constructor.
    intros. simpl in H0. destruct H0. subst x0. auto. contradiction.
    apply Sorted_1.
  Qed.
End Sorted.

Section LocallySorted.
  Context {A : Type} `{O: Ord A}.

  (** An alternative definition of being sorted that's easier to prove. *)
  Inductive LocallySorted : list A -> Prop :=
  | LSorted_nil : LocallySorted nil
  | LSorted_cons1 a : LocallySorted (a :: nil)
  | LSorted_consn a b l :
      LocallySorted (b :: l) -> le a b -> LocallySorted (a :: b :: l).

  Lemma Sorted_LocallySorted_iff : forall l, Sorted l <-> LocallySorted l.
  Proof.
    split.
    - induction l as [|a [|b l]]; intros H; constructor;
        inversion H; subst; clear H; auto using in_eq.
    - induction l as [|a [|b l]]; intros.
      + constructor.
      + constructor; [contradiction|constructor].
      + inversion H; subst; clear H.
        specialize (IHl H2); clear H2.
        constructor; auto.
        intros. eapply le_trans; eauto.
        inversion IHl; subst; clear IHl.
        destruct H; subst; auto using le_refl.
  Qed.
End LocallySorted.
