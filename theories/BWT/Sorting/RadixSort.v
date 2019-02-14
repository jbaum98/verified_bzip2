Require Import Coq.Lists.List.
Import ListNotations.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Mergesort.

Section OrdHead.
  Context {A : Type} `{Ord A}.

  Inductive le_hd : list A -> list A -> Prop :=
  | le_nil : forall ys, le_hd [] ys
  | le_cons : forall x xs y ys, le x y -> le_hd (x :: xs) (y :: ys).

  Instance Ord_head : Ord (list A) := { le := le_hd; }.
  Proof.
    - intros x y z LXY LYZ.
      destruct LXY; [constructor|].
      inversion LYZ; subst; clear LYZ.
      constructor. eapply le_trans; eauto.
    - intros x y.
      destruct x as [|x xtl]; [left; constructor|].
      destruct y as [|y ytl]; [right; constructor|].
      destruct (le_total x y); [left | right]; constructor; auto.
    - intros.
      destruct x as [|x xtl]; [left; constructor|].
      destruct y as [|y ytl].
      + right. intro contra. inversion contra.
      + destruct (le_dec x y).
        * left. constructor. auto.
        * right.
          intro contra. inversion contra.
          contradiction.
  Defined.
End OrdHead.

Let l := [[2; 1; 3];
          [1; 4; 8];
          [3; 1; 2]].

Section InsertionSort.
  Context {A : Type} `{Ord A}.

  Fixpoint insert (i:A) (l: list A) :=
    match l with
    | nil => i::nil
    | h::t => if le_dec i h then i::h::t else h :: insert i t
    end.

  Fixpoint sort (l: list A) : list A :=
    match l with
    | nil => nil
    | h::t => insert h (sort t)
    end.
End InsertionSort.

Eval compute in (mergesort [3; 1; 2]).
