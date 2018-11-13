(** An implementation of equivalence and lexicographic ordering for
    lists, only looking at the first k elements of the list. **)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Mergesort.
Require Import BWT.Sorting.Sorted.

Import ListNotations.

Section LeK.

  Context {A : Type} `{Ord A}.
  Open Scope ord_scope.

  Inductive le_k : nat -> list A -> list A -> Prop :=
  | le_nil     : forall ys k, le_k k [] ys
  | le_zero    : forall xs ys, le_k 0 xs ys
  | le_cons_lt : forall x y xs ys k, x < y -> le_k k (x :: xs) (y :: ys)
  | le_cons_eq : forall x y xs ys k, x === y -> le_k k xs ys ->
                                le_k (S k) (x :: xs) (y :: ys).

  Notation "x <={ k } y" := (le_k k x y) (at level 70, no associativity) : ord_scope.

  Theorem le_k_trans : forall k x y z, x <={k} y -> y <={k} z -> x <={k} z.
  Proof.
    intros k x y z LXY. revert z.
    induction LXY; intros z LYZ; inversion LYZ; subst; clear LYZ;
      try apply le_nil; try apply le_zero; try discriminate;
        [apply le_cons_lt|apply le_cons_lt|apply le_cons_lt|apply le_cons_eq];
        repeat match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; clear H
        | [ H : _ === _ |- _ ] => try (rewrite H || rewrite <- H); clear H
        end; eauto using lt_trans, eqv_refl.
  Defined.

  Theorem le_k_total : forall k x y, x <={k} y \/ y <={k} x.
  Proof.
    intros k x. revert k.
    induction x as [|x xs]; intros k y; destruct y as [|y ys]; eauto using le_nil.
    destruct (lt_eq_dec x y) as [[LXY|E]|LYX]; eauto using le_cons_lt.
    destruct k; eauto using le_zero.
    edestruct IHxs; eauto using le_cons_eq, eqv_sym.
  Defined.

  Program Fixpoint le_k_dec k xs ys : { xs <={k} ys } + { ~ xs <={k} ys } :=
    match k with
    | O   => left _
    | S k =>
      match (xs, ys) with
      | (nil, _)      => left  _
      | (_ :: _, nil) => right _
      | (x :: xs, y :: ys) =>
        match lt_eq_dec x y with
        | inleft (left _) => left _  (* < *)
        | inright _       => right _ (* > *)
        | inleft (right _) =>
          match (le_k_dec k xs ys) with
          | left  _ => left _
          | right _ => right _
          end
        end
      end
    end.
  Next Obligation. apply le_zero. Defined.
  Next Obligation. apply le_nil.  Defined.
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
End LeK.

Instance Ord_list_k {A} `{Ord A} (k : nat) : Ord (list A) :=
  { le := le_k k;
    le_trans := le_k_trans k;
    le_total := le_k_total k;
    le_dec := le_k_dec k;
  }.

Section Sort.
  Context {A : Type} `{Ord A}.

  Variable k : nat.
  Let Ok := Ord_list_k k.

  Program Definition sort :  list (list A) -> list (list A)
    := @mergesort _ Ok.

  Lemma sort_props : forall l,
      @Sorted _ Ok (sort l) /\
      Permutation (sort l) l /\
      @Stable _ Ok (sort l) l.
  Proof.
    intros.
    unfold sort. case (mergesort l). intros l' [S [P St]].
    cbn. intuition.
  Qed.

  Theorem sort_sorted : forall l,
      @Sorted _ Ok (sort l).
  Proof. apply sort_props. Qed.

  Theorem sort_perm : forall l,
      Permutation (sort l) l.
  Proof. apply sort_props. Qed.

  Theorem sort_stable : forall l,
      @Stable _ Ok (sort l) l.
  Proof. apply sort_props. Qed.

  Theorem sort_length : forall l,
      length (sort l) = length l.
  Proof.
    intros.
    apply Permutation_length.
    apply sort_perm.
  Qed.
End Sort.

Section SortedK.
  Context {A : Type} `{Ord A}.

  Local Arguments Sorted {_} _.
  Local Arguments le {_} _.

  Theorem sorted_zero : forall l,
      Sorted (Ord_list_k 0) l.
  Proof.
    intros.
    apply Sorted_LocallySorted_iff.
    induction l as [|a [|b l]]; constructor; auto.
    apply le_zero.
  Qed.

  Theorem sort_zero : forall l : list (list A),
    sort 0 l = l.
  Proof.
    intros.
    unfold sort. case (mergesort l) as [l' [S [P St]]]; cbn.
    apply @stable_sort_unique with (O := Ord_list_k 0); auto using sorted_zero.
  Qed.

  Theorem le_k_S : forall k x y,
      le_k (S k) x y -> le_k k x y.
  Proof.
    intros k x y HL. remember (S k) as k'. generalize dependent k.
    induction HL; intros; subst.
    - constructor.
    - discriminate.
    - constructor; auto.
    - destruct k0; [apply le_zero|].
      apply le_cons_eq; auto.
  Qed.

  Theorem sorted_S : forall k l,
      Sorted (Ord_list_k (S k)) l -> Sorted (Ord_list_k k) l.
  Proof.
    intros k l HS. remember (S k) as k'. generalize dependent k.
    induction HS; intros; subst; constructor.
    - intros. apply le_k_S. apply H0. apply H1.
    - apply IHHS. auto.
  Qed.

End SortedK.
