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

Section Filter.
  Context {A T F} (f : forall y : A, {T y} + {F y}).

  Fixpoint filter l : list A :=
    match l with
    | nil => nil
    | x :: tl => if f x then x :: filter tl else filter tl
    end.

  Theorem filter_In : forall l x,
      In x (filter l) <-> In x l /\ exists PT, f x = left PT.
  Proof.
    induction l; intros.
    - cbn. intuition.
    - cbn. split; intros.
      + destruct (f a) eqn:EF.
        destruct H; subst; intuition; eauto; try apply IHl; auto.
        right. apply IHl; auto.
        split; [right|]; apply IHl; auto.
      + destruct H as [[E | I] [PT HF]]; subst.
        rewrite HF. intuition.
        destruct (f a) eqn:EF; [right|]; apply IHl; eauto.
  Qed.

  Remark filter_app: forall (l l': list A),
      filter (l ++ l') = filter l ++ filter l'.
  Proof.
    induction l; intros; simpl. auto.
    destruct (f a); simpl. f_equal; auto. auto.
  Qed.

  Remark filter_empty: forall l,
      (forall x, In x l -> exists PF, f x = right PF) ->
      filter l = nil.
  Proof.
    induction l; simpl; intros.
    auto.
    destruct (H a) as [PF HF]; [eauto|].
    rewrite HF. apply IHl. auto.
  Qed.

  Remark filter_sublist:
    forall x (l l1' l2': list A),
      filter l = l1' ++ x :: l2' ->
      exists l1, exists l2, l = l1 ++ x :: l2 /\ filter l1 = l1' /\ filter l2 = l2'.
  Proof.
    induction l; intros until l2'; simpl.
    intro. destruct l1'; simpl in H; discriminate.
    case_eq (f a); intros.
    destruct l1'; simpl in H0; injection H0; clear H0; intros.
    subst x. exists (@nil A); exists l. auto.
    subst a0. destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. congruence. auto.
    destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. auto. auto.
  Qed.
End Filter.

Lemma Permutation_cons_in {A} : forall (x y : A) xs ys,
    Permutation (x :: xs) (y :: ys) ->
    (x = y \/ In x ys).
Proof.
  intros x y xs ys P.
  eapply Permutation_in in P.
  cbn in P. destruct P as [E | I]; eauto.
  cbn; eauto.
Qed.



Section Stable.
  Context {A : Type} `{O : Ord A}.
  Open Scope ord_scope.

  (** Stable permutations.  Two lists are in the [Stable] relation if
  equivalent elements appear in the same order in both lists.
  That is, if the first list is of the form [ ... x ... y ... ]
  with [x] and [y] being equivalent, the other list is also of
  the form [ ... x ... y ... ].  *)

  Definition Stable (l l': list A) : Prop :=
    forall x, filter (eqv_dec x) l = filter (eqv_dec x) l'.

  Lemma Stable_refl:
    forall l, Stable l l.
    intros; red; intros; auto.
  Qed.

  Lemma Stable_trans:
    forall l1 l2 l3, Stable l1 l2 -> Stable l2 l3 -> Stable l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (eqv_dec x) l2); auto.
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
    destruct (eqv_dec x a). f_equal; auto. auto.
  Qed.

  Lemma Stable_swap:
    forall a b l, ~le b a -> Stable (a::b::l) (b::a::l).
  Proof.
    intros; red; intros. simpl.
    case_eq (eqv_dec x a); intro; auto.
    case_eq (eqv_dec x b); intro; auto.
    elim H. unfold eqv in *.
    intuition. eauto using le_trans.
  Qed.

  Lemma Stable_cons_app:
    forall a l l1 l2,
      Stable l (l1 ++ l2) ->
      (forall b, In b l1 -> ~(a <= b /\ b <= a)) ->
      Stable (a :: l) (l1 ++ a :: l2).
  Proof.
    intros; red; intros. rewrite filter_app. simpl.
    generalize (H x). rewrite filter_app.
    case_eq (eqv_dec x a); intro; auto.
    rewrite (filter_empty (eqv_dec x) l1). simpl. intro. congruence.
    intros. case_eq (eqv_dec x x0); intro; auto.
    elim (H0 x0); auto.
    unfold eqv in e. destruct e.
    unfold eqv in e0. destruct e0.
    split; eapply le_trans; eauto.
    intros; exists n; auto.
  Qed.

  Lemma Stable_cons_app':
    forall a b l l1 l2,
      Stable l (b :: l1 ++ l2) ->
      Sorted (b :: l1) -> ~(b <= a) ->
      Stable (a :: l) (b :: l1 ++ a :: l2).
  Proof.
    intros. change (Stable (a :: l) ((b :: l1) ++ a :: l2)).
    apply Stable_cons_app. simpl; auto.
    intros. simpl in H2. destruct H2. subst b0. tauto.
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
    destruct (eqv_dec x x); [|contradiction].
    assert (eqv x y) by (unfold eqv; eauto).
    destruct (eqv_dec x y); [|contradiction].
    intro.
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
      destruct (eqv_dec a a); [|pose proof (eqv_refl a); contradiction].
      inversion S.
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
      destruct (eqv_dec hd hd); [|pose proof eqv_refl hd; contradiction].
      destruct (eqv_dec hd hd'); [|contradiction].
      inversion F; subst; clear F.
      f_equal.
      apply IHtl; auto.
      apply Permutation_cons_inv in P. auto.
      unfold Stable in *.
      intro x; specialize (St x).
      cbn in St.
      destruct (eqv_dec x hd'); auto.
      inversion St; auto.
  Qed.
End Stable.

Section LocallySorted.
  Context {A : Type} `{O: Ord A}.
  Open Scope ord_scope.

  (** An alternative definition of being sorted that's easier to prove. *)
  Inductive LocallySorted : list A -> Prop :=
  | LSorted_nil : LocallySorted nil
  | LSorted_cons1 a : LocallySorted (a :: nil)
  | LSorted_consn a b l :
      LocallySorted (b :: l) -> a <= b -> LocallySorted (a :: b :: l).

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
