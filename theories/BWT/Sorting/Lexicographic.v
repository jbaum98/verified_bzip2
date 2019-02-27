(** An implementation of equivalence and lexicographic ordering for
    lists, only looking at the first k elements of the list. **)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Mergesort.

Import Coq.Lists.List.ListNotations.

Section LexLe.
  Context {A : Type} `{O: Ord A}.

  Inductive lex_le : list A -> list A -> Prop :=
  | lex_le_nil : forall ys, lex_le [] ys
  | le_cons_lt : forall x y xs ys, lt x y -> lex_le (x :: xs) (y :: ys)
  | le_cons_eq : forall x y xs ys, eqv x y -> lex_le xs ys ->
                              lex_le (x :: xs) (y :: ys).

  Theorem lex_le_trans : forall x y z, lex_le x y -> lex_le y z -> lex_le x z.
  Proof.
    intros x y z LXY. revert z.
    induction LXY as [|x y xs ys HLT|x y xs ys HE HLex IH]; intros z LYZ;
      [constructor|inversion LYZ; subst; clear LYZ..];
      rename y0 into z; rename ys0 into zs.
    - apply le_cons_lt. eapply lt_trans; eauto.
    - apply le_cons_lt. rewrite <- H1. auto.
    - apply le_cons_lt. rewrite HE. auto.
    - apply le_cons_eq.
      eapply eqv_trans; eauto.
      apply IH; auto.
  Defined.

  Theorem lex_le_total : forall x y, lex_le x y \/ lex_le y x.
  Proof.
    induction x as [|x xs]; [left; constructor|].
    intros [|y ys]; [right; constructor|].
    destruct (lt_eq_dec x y) as [[LXY|E]|LYX]; eauto using le_cons_lt.
    edestruct IHxs; eauto using le_cons_eq, eqv_sym.
  Defined.

  Program Fixpoint lex_le_dec xs ys : { lex_le xs ys } + { ~ lex_le xs ys } :=
    match (xs, ys) with
    | (nil, _)      => left  _
    | (_ :: _, nil) => right _
    | (x :: xs, y :: ys) =>
      match lt_eq_dec x y with
      | inleft (left _) => left _  (* < *)
      | inright _       => right _ (* > *)
      | inleft (right _) =>
        match (lex_le_dec xs ys) with
        | left  _ => left _
        | right _ => right _
        end
      end
    end.
  Next Obligation. constructor. Defined.
  Next Obligation. intro c; inversion c. Defined.
  Next Obligation. apply le_cons_lt. auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_excl; split; eauto.
    - eapply lt_not_eq; eauto using eqv_sym.
  Defined.
  Next Obligation. apply le_cons_eq; auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_not_eq; eauto.
    - contradiction.
  Defined.
End LexLe.

Instance Ord_list_lex {A} `{Ord A} : Ord (list A) :=
  { le := lex_le;
    le_trans := lex_le_trans;
    le_total := lex_le_total;
    le_dec := lex_le_dec;
  }.

Section LexSort.
  Context {A : Type} `{Ord A}.

  Definition lexsort : list (list A) -> list (list A)
    := fun l => proj1_sig (@mergesort _ Ord_list_lex l).

  Theorem lexsort_perm : forall l, Permutation l (lexsort l).
  Proof.
    intros.
    unfold lexsort. case (mergesort l). intros l' [S [P St]].
    cbn. apply Permutation_sym. apply P.
  Defined.

  Theorem lexsort_length : forall l,
      length (lexsort l) = length l.
  Proof.
    intros.
    apply Permutation_length.
    apply Permutation_sym. apply lexsort_perm.
  Qed.
End LexSort.
