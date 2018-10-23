(** An implementation of equivalence and lexicographic ordering for
    lists, only looking at the first k elements of the list. **)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.

Require Import Ord.
Require MergesortClass.

Module Mergesort := MergesortClass.

Section Eq_K.

  Context {A : Type} {R : relation A} `{E : EqDec A R}.

  Inductive eq_k : nat -> list A -> list A -> Prop :=
  | eq_nil  : forall k, eq_k k [] []
  | eq_zero : forall xs ys, eq_k 0 xs ys
  | eq_cons : forall x y xs ys k, x === y -> eq_k k xs ys -> eq_k (S k) (x :: xs) (y :: ys).

  Fixpoint eq_k_dec (k: nat) (xs ys : list A) :
    { eq_k k xs ys } + { ~ eq_k k xs ys }.
  Proof.
    destruct k.
    - left. apply eq_zero.
    - destruct xs as [|x xtl]; destruct ys as [|y ytl].
      + left; apply eq_nil.
      + right. intro contra. inversion contra.
      + right. intro contra. inversion contra.
      + destruct (x == y).
        * destruct (eq_k_dec k xtl ytl).
          { left.  apply eq_cons; auto. }
          { right. intro contra. inversion contra. contradiction. }
        * right. intro contra. inversion contra. contradiction.
  Defined.

  Theorem eq_k_refl (k : nat) : forall (l : list A),
      eq_k k l l.
  Proof.
    intro l; revert k.
    induction l; intro k.
    - apply eq_nil.
    - destruct k.
      + apply eq_zero.
      + apply eq_cons. apply equiv_reflexive.
        apply IHl.
  Defined.

  Theorem eq_k_sym (k : nat) : forall (a b : list A),
      eq_k k a b -> eq_k k b a.
  Proof.
    intros a b H.
    induction H.
    - apply eq_nil.
    - apply eq_zero.
    - apply eq_cons. apply equiv_symmetric; auto.
      auto.
  Defined.

  Fixpoint eq_k_trans (k : nat) : forall (a b c : list A),
      eq_k k a b -> eq_k k b c -> eq_k k a c.
  Proof.
    intros.
    destruct a; destruct b; destruct c;
      auto; try constructor;
        try (destruct k; try apply eq_zero; try inversion H; try inversion H0);
        subst.
    apply eq_cons; auto.
    eapply equiv_transitive; eauto.
    apply eq_k_trans with (b := b); auto.
  Defined.

  Instance Equivalence_list_k (k : nat) : Equivalence (eq_k k) :=
  { Equivalence_Reflexive := eq_k_refl k;
    Equivalence_Symmetric := eq_k_sym k;
    Equivalence_Transitive := eq_k_trans k }.

  Instance EqDec_list_k (k : nat) : EqDec (list A) (eq_k k) :=
    eq_k_dec k.

  Theorem eq_k_firstn : forall k xs ys,
      eq_k k xs ys <-> Forall2 equiv (firstn k xs) (firstn k ys).
  Proof with auto.
    induction k; intros xs ys.
    - split; intros; constructor.
    - destruct xs as [|hd tl]; destruct ys as [|hd' tl'].
      + split; intros; constructor.
      + split; intros; inversion H.
      + split; intros; inversion H.
      + split; intros;
          inversion H; subst; clear H;
            simpl; constructor; try apply IHk; auto.
  Qed.
End Eq_K.

Section Ord_K.

  Context {A : Type} {eqA : relation A} `{E : EqDec A eqA}.
  Context {leA: relation A} `{O: TotalOrderDec A eqA leA}.

  Inductive le_k : nat -> list A -> list A -> Prop :=
  | le_nil     : forall ys k, le_k k [] ys
  | le_zero    : forall xs ys, le_k 0 xs ys
  | le_cons_lt : forall x y xs ys k, leA x y -> ~ eqA x y -> le_k k (x :: xs) (y :: ys)
  | le_cons_eq : forall x y xs ys k, eqA x y -> le_k k xs ys ->
                                le_k (S k) (x :: xs) (y :: ys).

  Fixpoint le_k_dec (k: nat) (xs ys : list A) :
    { le_k k xs ys } + { le_k k ys xs }.
  Proof.
    destruct k.
    - left. apply le_zero.
    - destruct xs as [|x xtl]; destruct ys as [|y ytl];
        simpl; try (left; apply le_nil); try (right; apply le_nil).
      destruct (x == y).
      + destruct (le_k_dec k xtl ytl); try omega.
        * left.  apply le_cons_eq; auto.
        * right. apply le_cons_eq; auto. apply equiv_symmetric in e. auto.
      + destruct (le_dec x y).
        * left.  apply le_cons_lt; auto.
        * right. apply le_cons_lt; auto.
          intro contra. apply c. apply equiv_symmetric. auto.
  Defined.

  Instance LeDec_list_k (k : nat) : LeDec (le_k k) := le_k_dec k.
End Ord_K.

Section Sort.
  Context {A : Type} `{TotalOrderDec A}.

  Variable k : nat.

  Definition sort : list (list A) -> list (list A)
    := @Mergesort.sort _ _ (LeDec_list_k k ).

  Theorem sort_perm : forall l, Permutation l (sort l).
  Proof.
    exact Mergesort.Permuted_sort.
  Defined.
End Sort.
