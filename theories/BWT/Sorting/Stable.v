Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Sumbool.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.List.

Section Stable.
  Context {A : Type} `{O : Ord A}.

  (** Stable permutations.  Two lists are in the [Stable] relation if
  equivalent elements appear in the same order in both lists.
  That is, if the first list is of the form [ ... x ... y ... ]
  with [x] and [y] being equivalent, the other list is also of
  the form [ ... x ... y ... ].  *)

  Definition Stable (l l': list A) : Prop :=
    forall x, filter (eqv_decb x) l = filter (eqv_decb x) l'.

  Lemma Stable_refl:
    forall l, Stable l l.
    intros; red; intros; auto.
  Qed.

  Lemma Stable_trans:
    forall l1 l2 l3, Stable l1 l2 -> Stable l2 l3 -> Stable l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (eqv_decb x) l2); auto.
  Qed.

  Lemma Stable_sym : forall l l',
      Stable l l' -> Stable l' l.
  Proof.
    intros l l' H x.
    specialize (H x).
    erewrite eq_sym; eauto.
  Qed.

  Lemma Stable_app:
    forall l l' m m', Stable l l' -> Stable m m' -> Stable (l ++ m) (l' ++ m').
  Proof.
    intros; red; intros. repeat rewrite filter_app. f_equal; auto.
  Qed.

  Lemma Stable_skip:
    forall a l l', Stable l l' -> Stable (a::l) (a::l').
  Proof.
    intros; red; intros. simpl.
    unfold eqv_decb; destruct (eqv_dec x a); simpl. f_equal. apply H. apply H.
  Qed.

  Lemma Stable_swap:
    forall a b l, ~le b a -> Stable (a::b::l) (b::a::l).
  Proof.
    intros; red; intros. simpl.
    unfold eqv_decb.
    case_eq (eqv_dec x a); intro; simpl; auto.
    case_eq (eqv_dec x b); intro; simpl; auto.
    elim H. unfold eqv in *.
    intuition. eauto using le_trans.
  Qed.

  Lemma Stable_cons_app:
    forall a l l1 l2,
      Stable l (l1 ++ l2) ->
      (forall b, In b l1 -> ~eqv a b) ->
      Stable (a :: l) (l1 ++ a :: l2).
  Proof.
    intros; red; intros. rewrite filter_app. simpl.
    generalize (H x). rewrite filter_app.
    unfold eqv_decb; case_eq (eqv_dec x a); intro; simpl; auto.
    rewrite (filter_empty _ l1). simpl. intro. congruence.
    intros. case_eq (eqv_dec x x0); intro; auto.
    elim (H0 x0); auto.
    unfold eqv in e. destruct e.
    unfold eqv in e0. destruct e0.
    split; eapply le_trans; eauto.
  Qed.

  Lemma Stable_cons_app':
    forall a b l l1 l2,
      Stable l (b :: l1 ++ l2) ->
      Sorted (b :: l1) -> lt a b ->
      Stable (a :: l) (b :: l1 ++ a :: l2).
  Proof.
    intros. change (Stable (a :: l) ((b :: l1) ++ a :: l2)).
    apply Stable_cons_app. simpl; auto.
    intros. simpl in H2. destruct H2. subst b0. apply lt_not_eq. auto.
    inversion H0; subst. red; intros [P Q]. elim H1.
    apply le_trans with b0; eauto using lt_le.
  Qed.

  Lemma Stable_decomp:
    forall l l',
      Stable l l' ->
      forall l1 x l2 y l3,
        l = l1 ++ x :: l2 ++ y :: l3 ->
        le x y -> le y x ->
        exists l1', exists l2', exists l3',
              l' = l1' ++ x :: l2' ++ y :: l3'.
  Proof.
    intros.
    generalize (H x). subst l. rewrite filter_app. simpl.
    rewrite filter_app. simpl.
    assert (eqv x x) by apply eqv_refl.
    unfold eqv_decb.
    destruct (eqv_dec x x); [|contradiction].
    assert (eqv x y) by (unfold eqv; eauto).
    destruct (eqv_dec x y); [|contradiction].
    simpl; intro.
    destruct (filter_sublist _ _ _ _ _ (sym_equal H4)) as [m1 [m2 [P [Q R]]]].
    destruct (filter_sublist _ _ _ _ _ R) as [m3 [m4 [S [T U]]]].
    exists m1; exists m3; exists m4. congruence.
  Qed.

  Lemma Stable_nil : forall l,
      Stable nil l -> l = nil.
  Proof.
    induction l.
    - easy.
    - intro S.
      unfold Stable in S; cbn in S.
      specialize (S a).
      unfold eqv_decb in S.
      destruct (eqv_dec a a); [|pose proof (eqv_refl a); contradiction].
      simpl in S; inversion S.
  Qed.

  (** There is only one way to sort a list stably. *)

  Theorem stable_sort_unique : forall l l',
      Sorted l -> Sorted l' ->
      Permutation l l' -> Stable l l' ->
      l = l'.
  Proof.
    induction l as [|hd tl]; intros l' SL SL' P St.
    - apply Permutation_nil in P. subst; auto.
    - destruct l' as [|hd' tl'].
      apply Permutation_sym in P. apply Permutation_nil_cons in P.
      contradiction.
      inversion SL; inversion SL'; subst; clear SL SL'.
      assert (eqv hd hd'). {
        pose proof (Permutation_sym P) as P'.
        destruct (Permutation_cons_in hd hd' tl tl' P);
          destruct (Permutation_cons_in hd' hd tl' tl P');
          subst; try apply eqv_refl.
        assert (le hd hd') by auto.
        assert (le hd' hd) by auto.
        unfold eqv; destruct (le_dec hd hd'); destruct (le_dec hd' hd);
          try contradiction.
        auto.
      }
      pose proof (St hd) as F. cbn in F.
      unfold eqv_decb in F.
      destruct (eqv_dec hd hd); [|pose proof eqv_refl hd; contradiction].
      destruct (eqv_dec hd hd'); [|contradiction].
      simpl in F; inversion F; subst; clear F.
      f_equal.
      apply IHtl; auto.
      apply Permutation_cons_inv in P. auto.
      unfold Stable in *.
      intro x; specialize (St x).
      cbn in St.
      unfold eqv_decb in St.
      destruct (eqv_dec x hd'); auto.
      simpl in St.
      inversion St; auto.
  Qed.
End Stable.
