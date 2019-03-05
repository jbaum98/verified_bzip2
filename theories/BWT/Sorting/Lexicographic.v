(** An implementation of equivalence and lexicographic ordering for
    lists, only looking at the first k elements of the list. **)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.InsertionSort.

Import Coq.Lists.List.ListNotations.

Section LexLe.
  Context {A : Type} `{O: Ord A}.

  Inductive lex_le : list A -> list A -> Prop :=
  | lex_le_nil : forall ys, lex_le [] ys
  | lex_le_cons_lt : forall x y xs ys, lt x y -> lex_le (x :: xs) (y :: ys)
  | lex_le_cons_eq : forall x y xs ys, eqv x y -> lex_le xs ys ->
                              lex_le (x :: xs) (y :: ys).

  Theorem lex_le_trans : forall x y z, lex_le x y -> lex_le y z -> lex_le x z.
  Proof.
    intros x y z LXY. revert z.
    induction LXY as [|x y xs ys HLT|x y xs ys HE HLex IH]; intros z LYZ;
      [constructor|inversion LYZ; subst; clear LYZ..];
      rename y0 into z; rename ys0 into zs.
    - apply lex_le_cons_lt. eapply lt_trans; eauto.
    - apply lex_le_cons_lt. rewrite <- H1. auto.
    - apply lex_le_cons_lt. rewrite HE. auto.
    - apply lex_le_cons_eq.
      eapply eqv_trans; eauto.
      apply IH; auto.
  Defined.

  Theorem lex_le_total : forall x y, lex_le x y \/ lex_le y x.
  Proof.
    induction x as [|x xs]; [left; constructor|].
    intros [|y ys]; [right; constructor|].
    destruct (lt_eq_dec x y) as [[LXY|E]|LYX]; eauto using lex_le_cons_lt.
    edestruct IHxs; eauto using lex_le_cons_eq, eqv_sym.
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
  Next Obligation. apply lex_le_cons_lt. auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_excl; split; eauto.
    - eapply lt_not_eq; eauto using eqv_sym.
  Defined.
  Next Obligation. apply lex_le_cons_eq; auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_not_eq; eauto.
    - contradiction.
  Defined.

  Theorem lex_le_not_nil_r : forall (a : A) x,
      ~ lex_le (a :: x) [].
  Proof. intros. intro c. inversion c. Qed.

  Theorem lex_le_trunc_r : forall x y,
      lex_le x y ->
      lex_le x (firstn (length x) y).
  Proof.
    induction x; intros y HLE; [apply lex_le_nil|].
    inversion HLE; subst.
    - cbn. apply lex_le_cons_lt. auto.
    - cbn. apply lex_le_cons_eq. auto.
      apply IHx. auto.
  Qed.

  Inductive lex_lt : list A -> list A -> Prop :=
  | lex_lt_nil : forall hy ty, lex_lt [] (hy :: ty)
  | lex_lt_cons_lt : forall x y xs ys, lt x y -> lex_lt (x :: xs) (y :: ys)
  | lex_lt_cons_eq : forall x y xs ys, eqv x y -> lex_lt xs ys ->
                              lex_lt (x :: xs) (y :: ys).

  Theorem lex_lt_iff : forall x y,
      lex_lt x y <-> ~ (lex_le y x).
  Proof.
    induction x; intro y.
    - split.
      + intro. inversion H.
        apply lex_le_not_nil_r.
      + intro. destruct y.
        exfalso; apply H; constructor.
        constructor.
    - split.
      + intro. inversion H; subst; clear H.
        * intro c.
          inversion c; subst; clear c.
          apply (lt_excl a y0); split; auto.
          apply (lt_not_eq a y0); auto. symmetry. auto.
        * intro c. inversion c; subst; clear c.
          apply (lt_not_eq y0 a); auto. symmetry; auto.
          apply IHx in H4. contradiction.
      + intro. destruct y. exfalso. apply H. constructor.
        destruct (le_dec a0 a).
        apply lt_spec in l. destruct l.
        exfalso. apply H. apply lex_le_cons_lt. auto.
        apply lex_lt_cons_eq. symmetry. auto.
        apply IHx.
        intro c. apply H. apply lex_le_cons_eq; auto.
        apply lex_lt_cons_lt. auto.
  Qed.
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
    := @sort _ Ord_list_lex.

  Global Arguments lexsort _ : simpl never.

  Theorem lexsort_perm : forall l, Permutation l (lexsort l).
  Proof.
    intros.
    unfold lexsort. apply sort_perm.
  Defined.

  Theorem lexsort_length : forall l,
      length (lexsort l) = length l.
  Proof.
    intros.
    apply Permutation_length.
    apply Permutation_sym. apply lexsort_perm.
  Qed.
End LexSort.

Theorem lex_lt_inv {A : Type} {O : Ord A} : forall hx tx hy ty,
    lt (hx :: tx) (hy :: ty) ->
    (eqv hx hy /\ lt tx ty) \/ lt hx hy.
Proof.
  intros. apply lex_lt_iff in H.
  remember (hx :: tx) as x.
  remember (hy :: ty) as y.
  revert hx tx hy ty Heqx Heqy.
  induction H; [discriminate|intros hx tx hy ty Heqx Heqy; inversion Heqx; inversion Heqy; subst; clear Heqx Heqy..].
  - right; auto.
  - destruct tx. inversion H0; subst; clear H0.
    left. split; auto.
    apply lex_lt_iff. constructor.
    destruct ty. inversion H0.
    destruct (IHlex_lt a tx a0 ty) as [[]|]; auto.
    + left; split; auto.
      apply lex_lt_iff.
      apply lex_lt_iff in H2.
      apply lex_lt_cons_eq; auto.
    + left; split; auto.
      apply lex_lt_iff.
      apply lex_lt_cons_lt.
      auto.
Qed.

Theorem lex_lt_destr {A : Type} {O : Ord A} : forall x y : list A,
    lt x y ->
    exists hx tx hy ty,
      x = hx ++ tx /\
      y = hy ++ ty /\
      lt tx ty /\
      eqv hx hy.
Proof.
  intros x y HLT. apply lex_lt_iff in HLT.
  induction HLT.
  - exists [], [], [], (hy::ty).
    repeat split; [apply lex_lt_iff|..]; constructor.
  - exists [], (x::xs), [], (y::ys).
    repeat split; [apply lex_lt_iff|..]; constructor; auto.
  - destruct IHHLT as [hx [tx [hy [ty [Hx [Hy [Hlt Heqv]]]]]]].
    exists (x::hx), tx, (y::hy), ty.
    rewrite Hx, Hy.
    repeat split; [|apply lex_le_cons_eq..];
      auto using eqv_rel_Symmetric; destruct Heqv; auto.
Qed.

Theorem lex_eqv_iff {A} {O : Ord A} : forall x y,
    Forall2 eqv x y <-> eqv x y.
Proof.
  induction x as [|a x IH]; intros y.
  - split.
   + intro H. inversion H; subst.
     split; constructor.
   + intros [LXY LYX].
     inversion LYX; subst.
     constructor.
  - split.
    + intro H. inversion H; subst; clear H.
      apply IH in H4. destruct H4.
      split; apply lex_le_cons_eq; auto using eqv_rel_Symmetric.
    + intros [LXY LYX].
      inversion LXY; inversion LYX; subst.
      * discriminate.
      * inversion H4; subst.
        exfalso; apply (lt_excl a y0); auto.
      * inversion H5; subst.
        symmetry in H6. apply lt_not_eq in H6. contradiction.
        auto.
      * discriminate.
      * inversion H5; subst.
        symmetry in H1; apply lt_not_eq in H1. contradiction. auto.
      * inversion H6; subst.
        assert (eqv x ys) by (split; auto).
        constructor; auto. apply IH. auto.
Qed.

Theorem lex_eqv_prepend {A} {O : Ord A} : forall hx tx hy ty,
    eqv hx hy -> le tx ty -> le (hx ++ tx) (hy ++ ty).
Proof.
  intros hx tx hy ty HE.
  apply lex_eqv_iff in HE.
  induction HE; intro HL.
  - cbn. auto.
  - cbn. apply lex_le_cons_eq; auto.
    apply IHHE. auto.
Qed.

Theorem lex_eqv_firstn {A} {O : Ord A} : forall x y j,
    eqv x y ->
    eqv (firstn j x) (firstn j y).
Proof.
  intros x y j HE; revert j.
  apply lex_eqv_iff in HE.
  induction HE; intros j.
  - rewrite firstn_nil. split; constructor.
  - apply lex_eqv_iff. destruct j; cbn; [constructor|].
    constructor; auto. apply lex_eqv_iff. auto.
Qed.
