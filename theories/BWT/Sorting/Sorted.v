Require Import Coq.Logic.FinFun.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.EquivDec.

Require Import BWT.Sorting.Ord.
Require Import BWT.ZipWith.
Require Import BWT.Filter.

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

  Theorem Sorted_uncons : forall hd tl,
      Sorted (hd :: tl) ->
      (forall x : A, In x tl -> le hd x) /\ Sorted tl.
  Proof. intros hd tl H. inversion H. auto. Qed.
End Sorted.

Section SortedFilter.
  Context {A} `{Ord A}.

  Theorem sorted_filter : forall l,
      Sorted l -> (forall {F T} (f : forall y : A, {T y} + {F y}), Sorted (filter f l)).
  Proof.
    intros. induction l; [constructor|].
    simpl. destruct (f a).
    - inversion H0; subst; clear H0.
      constructor.
      + intros x Hx.
        apply H3. apply filter_In in Hx. intuition.
      + apply IHl. auto.
    - apply IHl. apply Sorted_uncons in H0. intuition.
  Qed.
End SortedFilter.

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

  Lemma Stable_uncons:
    forall a l l', Stable (a::l) (a::l') -> Stable l l'.
  Proof.
    intros; red; intros.
    specialize (H x). simpl in H.
    destruct (eqv_dec x a). inversion H; auto. auto.
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

Section Index.
  Context {A : Type} `{O: Ord A}.

  Definition IndexSorted (l : list A) := forall i j d,
      i <= j < length l ->
      le (nth i l d) (nth j l d).

  Theorem IndexSorted_uncons : forall l a, IndexSorted (a :: l) -> IndexSorted l.
  Proof.
    intros l a HS.
    intros i j d HIJ.
    replace (nth i l d) with (nth (S i) (a :: l) d) by reflexivity.
    replace (nth j l d) with (nth (S j) (a :: l) d) by reflexivity.
    apply HS. simpl. omega.
  Qed.

  Theorem Sorted_IndexSorted_iff : forall l, Sorted l <-> IndexSorted l.
  Proof.
    split.
    - induction l as [|a l IH]; intros H;
        intros i j d HIJ; simpl in HIJ.
      + assert (i = 0 /\ j = 0) as HIJ0 by omega .
        destruct HIJ0; subst.
        apply le_refl.
      + destruct i; destruct j; simpl in HIJ; [apply le_refl| |omega|].
        * simpl nth at 1.
          eapply Sorted_uncons. apply H.
          simpl. apply nth_In. omega.
        * simpl. apply IH. eapply Sorted_uncons; eauto. omega.
    - induction l as [|a l IH]; intros H; constructor.
      + intros x HI.
        apply In_nth with (d := a) in HI.
        destruct HI as [i [HI Hx]].
        rewrite <- Hx.
        replace a with (nth 0 (a :: l) a) at 1 by reflexivity.
        replace (nth i l a) with (nth (S i) (a :: l) a) by reflexivity.
        apply H. simpl. omega.
      + apply IH. eapply IndexSorted_uncons. eauto.
  Qed.

  Definition IndexStable (l l': list A) := forall d,
    (let n := length l in
     length l' = n /\
     (exists f : nat -> nat,
         bFun n f /\
         bInjective n f /\
         (forall x : nat, x < n -> nth x l' d = nth (f x) l d) /\
         (forall i j, eqv (nth i l' d) (nth j l' d) -> i <= j < n -> f i <= f j))).

  Lemma perm_zipocc_fun `{EqDec A eq} : forall l l' da dn,
      Permutation l l' ->
      length l = length l' /\
      exists p,
        bFun (length l) p /\
        bInjective (length l) p /\
        (forall x : nat, x < length l ->
                  nth x (zipOcc l') (da, dn) = nth (p x) (zipOcc l) (da, dn)) /\
        (forall x : nat, x < length l -> nth x l' da = nth (p x) l da).
  Proof.
    intros l l' da dn HP.
    assert (HL : length l = length l') by (apply Permutation_length; auto).
    split; auto.
    apply zipOcc_Permutation in HP.
    destruct (proj1 (Permutation_nth _ _ (da, dn)) HP)
        as [HLZ [p [pbound [pinj pcorrect]]]].
    rewrite zipOcc_length in pbound, pinj, pcorrect.
    exists p. repeat split; auto.
    intros x Hx. specialize (pcorrect x Hx).
    rewrite !zipOcc_correct, !combine_nth in pcorrect
      by (symmetry; apply occs_length).
    inversion pcorrect. auto.
  Qed.

  Hint Extern 1 =>
  match goal with
  | |- exists pf, ?f ?x = left pf => apply dec_exists_pf_left
  end : dec_exists.

  Hint Extern 1 =>
  match goal with
  | |- exists pf, ?f ?x = right pf => apply dec_exists_pf_right
  end : dec_exists.

  Lemma IndexStable_nil : forall l, IndexStable nil l -> l = nil.
  Proof.
    intros. destruct l. auto.
    unfold IndexStable in H.
    destruct (H a). simpl in H. discriminate.
  Qed.

  Lemma nth_eq : forall l l' : list A,
      length l = length l' ->
      (forall i d, i < length l -> nth i l d = nth i l' d) <-> l = l'.
  Proof.
    induction l; intros l' L.
    - split; intros.
      + symmetry. apply length_zero_iff_nil. auto.
      + subst. reflexivity.
    - split; intros.
      + destruct l'. simpl in L. omega.
      f_equal.
        * apply (H 0 a). simpl; omega.
        * apply IHl; auto.
          intros i d.
          specialize (H (S i) d).
          simpl in H. intro; apply H; omega.
      + rewrite H. reflexivity.
  Qed.

  Theorem bounded_mono_id : forall (f : nat -> nat) n,
      bFun n f ->
      bInjective n f ->
      (forall x y, x <= y < n -> f x <= f y) ->
      forall x, x < n -> f x = x.
  Proof.
    induction n; intros ffin finj fmono.
    - intros; omega.
    - assert (fsur: bSurjective (S n) f) by (apply bInjective_bSurjective; auto).
      destruct (bSurjective_bBijective ffin fsur) as [g [gfin Hg]].
      destruct (Nat.eq_dec (f n) n) as [Eq|Neq]; [|exfalso].
      + assert (forall x, x < n -> f x <> n). {
          intros x Hx. rewrite <- Eq.
          intro c. apply finj in c; omega.
        }
        intros x Hx. destruct (Nat.eq_dec x n). subst. auto.
        apply IHn.
        * intros a Ha. specialize (H a Ha). specialize (ffin a). omega.
        * intros a b Ha Hb Heq. apply finj; omega.
        * intros. apply fmono. omega.
        * omega.
      + assert (f n < S n) by (apply ffin; omega).
        assert (f n < n) by omega.
        assert (g n < S n) by (apply gfin; omega).
        assert (g n <> n). {
          intro c. apply Neq. rewrite <- c at 1. apply Hg. omega.
        }
        assert (g n < n) by omega.
        assert (g n <= n < S n) by omega.
        specialize (fmono (g n) n H4).
        replace (f (g n)) with n in fmono by (symmetry; apply Hg; omega). omega.
  Qed.

  Theorem perm_inversions_eq : forall (l l' : list A) d,
    (let n := length l in
     length l' = n /\
     (exists f : nat -> nat,
         FinFun.bFun n f /\
         FinFun.bInjective n f /\
         (forall x : nat, x < n -> nth x l' d = nth (f x) l d) /\
         (forall i j, i <= j < n -> f i <= f j))) <-> l = l'.
  Proof.
    unfold FinFun.bFun, FinFun.bInjective.
    split; [|intros; subst; split; auto; exists (fun x => x); intuition auto].
    intros [HL [p [pbounded [pinj [pcorrect pmono]]]]].
    apply nth_eq; auto.
    intros i d' HI.
    rewrite <- !nth_indep with (d := d) (d' := d') by omega.
    rewrite pcorrect by omega.
    rewrite bounded_mono_id with (n := length l); auto.
  Qed.

  Hint Extern 1 =>
  match goal with
  | H: length ?l = length ?l' |- unfilter_ix (eqv_dec ?x) ?l' ?i < length ?l =>
    rewrite H
  end : jake.

  Theorem IndexStable_iff `{EqDec A eq}: forall l l',
      (Stable l l' /\ Permutation l l') <-> IndexStable l l'.
  Proof.
    intros. split.
    - intros [HS HP] d.
      destruct (perm_zipocc_fun l l' d 0)
        as [HL [p [pbounded [pinj [pcorrect_zip pcorrect]]]]]; auto.
      split; [auto using Permutation_length, Permutation_sym|].
      exists p. repeat split; auto.

      intros i j HE HIJ.
      specialize (HS (nth i l' d)).

      eapply @filter_ix_monotonic
        with (i := p i) (j := p j) (l := l) (f := eqv_dec (nth i l' d));
        try rewrite <- pcorrect;
        auto using pbounded, eqv_refl with zarith dec_exists.

      erewrite <- @filter_ix_zipOcc with (l := l') (i := i) (i' := p i);
        auto using eqv_refl with zarith.
      erewrite <- @filter_ix_zipOcc with (l := l') (i := j) (i' := p j);
        auto using eqv_refl with zarith.

      eapply @filter_ix_monotonic
        with (i := i) (j := j) (l := l') (f := eqv_dec (nth i l' d));
        try rewrite <- pcorrect;
        auto using pbounded, eqv_refl with zarith dec_exists.
    - intros HI.
      assert (HP: Permutation l l'). {
        destruct l eqn:Hl;
          [apply IndexStable_nil in HI; subst; constructor|
           rewrite <- Hl in *; clear l0 Hl].
        eapply Permutation_nth.
        simpl. destruct (HI a) as [HL [p [pbounded [pinj pcorrect]]]].
        split; [auto|]. exists p. intuition.
      }
      split; auto.

      intro x.

      assert (HPf: Permutation (filter (eqv_dec x) l) (filter (eqv_dec x) l')) by (apply filter_perm; auto).

      assert (HL: length l = length l')
        by (auto using Permutation_length, Permutation_sym).
      assert (HLf: length (filter (eqv_dec x) l) = length (filter (eqv_dec x) l'))
        by (auto using Permutation_length, Permutation_sym).

      apply perm_inversions_eq with (d := x).
      split; [auto using Permutation_length, Permutation_sym|].
      destruct (HI x) as [_ [f [fbound [finj [fcorrect fmono]]]]].
      exists (fun i => filter_ix (eqv_dec x) l (f (unfilter_ix (eqv_dec x) l' i))).
      intuition.
      + intros i Hi. apply filter_ix_bounded with (d := x). apply fbound.
        rewrite HL. apply unfilter_ix_bounded. rewrite <- HLf. auto.
        apply dec_exists_pf_left.
        rewrite <- fcorrect by (rewrite HL; apply unfilter_ix_bounded; omega).
        rewrite <- unfilter_ix_correct by omega.
        eapply @filter_In with (f := eqv_dec x).
        apply nth_In. unfold not. rewrite <- HLf. omega.
      + intros i j Hi Hj Hfeq.
        eapply filter_ix_inj in Hfeq. apply finj in Hfeq. apply unfilter_ix_inj in Hfeq. auto.
        1-6, 7: auto using fbound, unfilter_ix_bounded with arith zarith jake.
        1,2: apply dec_exists_pf_left;
          rewrite <- fcorrect by (auto using fbound, unfilter_ix_bounded with zarith jake);
          rewrite <- unfilter_ix_correct by (auto using fbound, unfilter_ix_bounded with zarith jake);
        eapply @filter_In with (f := eqv_dec x);
        apply nth_In; unfold not; rewrite <- HLf; omega.
      + rewrite <- filter_ix_correct.
        rewrite <- fcorrect.
        rewrite <- unfilter_ix_correct.
        reflexivity.
        4: apply dec_exists_pf_left; rewrite <- fcorrect, <- unfilter_ix_correct;
          auto; [eapply @filter_In with (f := eqv_dec x);
            apply nth_In; unfold not; rewrite <- HLf; omega|..].
        all: auto using fbound, unfilter_ix_bounded with zarith jake.
      + rewrite <- filter_ix_monotonic.
        apply fmono. rewrite <- !unfilter_ix_correct.
        destruct (proj1 (filter_In (eqv_dec x) l' (nth i (filter (eqv_dec x) l') x))).
        apply nth_In. unfold not; rewrite <- HLf; omega.
        destruct (proj1 (filter_In (eqv_dec x) l' (nth j (filter (eqv_dec x) l') x))).
        apply nth_In. unfold not; rewrite <- HLf; omega.
        destruct H3, H5. 1,2: eauto using eqv_sym, eqv_trans.
        5, 7: apply dec_exists_pf_left; rewrite <- fcorrect, <- unfilter_ix_correct;
          auto; [eapply @filter_In with (f := eqv_dec x);
            apply nth_In; unfold not; rewrite <- HLf; omega|..].
        3: rewrite <- unfilter_ix_monotonic. intuition.
        all: auto using fbound, unfilter_ix_bounded with zarith jake.
  Qed.

  Theorem IndexStable_trans `{EqDec A eq} : forall l1 l2 l3 : list A,
      IndexStable l1 l2 -> IndexStable l2 l3 -> IndexStable l1 l3.
  Proof.
    intros. eapply IndexStable_iff.
    eapply IndexStable_iff in H0.
    eapply IndexStable_iff in H1.
    destruct H0, H1. split.
    eauto using Stable_trans. eauto using Permutation_trans.
  Qed.

  Theorem IndexStable_sym `{EqDec A eq} : forall l1 l2 : list A,
      IndexStable l1 l2 -> IndexStable l2 l1.
  Proof.
    intros. eapply IndexStable_iff.
    eapply IndexStable_iff in H0.
    destruct H0. split.
    eauto using Stable_sym. eauto using Permutation_sym.
  Qed.
End Index.

Section Preserve.
  Context {A B: Type} `{OA : Ord A} `{OB : Ord B}.

  Theorem sorted_preserve : forall (f : A -> B) (l : list A),
      (forall a1 a2 : A, In a1 l -> In a2 l -> le a1 a2 -> le (f a1) (f a2)) ->
      Sorted l -> Sorted (map f l).
  Proof.
    induction l; [constructor|]; intros HF HS.
    cbn. constructor.
    - intros. apply in_map_iff in H.
      destruct H as [xpre [Hxpre Hinxpre]].
      rewrite <- Hxpre. apply HF; cbn; intuition.
      eapply Sorted_uncons; eauto.
    - apply IHl; [|eapply Sorted_uncons]; eauto.
      intros. apply HF; cbn; intuition.
  Qed.

  Theorem stable_preserve `{ED: EqDec B eq} : forall (f : A -> B) (l l' : list A),
      (forall a1 a2 : A, In a1 l -> In a2 l -> eqv (f a1) (f a2) -> eqv a1 a2) ->
      IndexStable l l' -> IndexStable (map f l) (map f l').
  Proof.
    intros f l l' HF HS.
    destruct l eqn:Hl. intro. apply IndexStable_nil in HS.
    subst. eapply IndexStable_iff. cbn. split. apply Stable_refl. constructor.
    rewrite <- Hl in *. clear Hl l0.
    destruct (HS a) as [HL [p [pbound [pinj [pcorrect pmono]]]]].
    split. rewrite !map_length. auto.
    exists p. rewrite !map_length. intuition.
    - rewrite !nth_indep with (d := d) (d' := f a)
        by (rewrite map_length; auto using pbound with zarith).
      rewrite !map_nth.
      f_equal. apply pcorrect. omega.
    - apply pmono.
      rewrite !nth_indep with (d := d) (d' := f a) in H
        by (rewrite map_length; auto using pbound with zarith).
      rewrite !map_nth in H.
      apply HF; rewrite pcorrect by omega; [apply nth_In; apply pbound; omega..|].
      rewrite <- pcorrect by omega. apply H. omega.
  Qed.

  Theorem stable_map_equiv_eq : forall (f : A -> B) (l l' : list A),
      (forall a1 a2 : A, In a1 l -> In a2 l -> eqv (f a1) (f a2) -> f a1 = f a2) ->
      Permutation l l' -> Stable (map f l) (map f l').
  Proof.
    intros f l l' HF HP. induction HP.
    - constructor.
    - cbn. apply Stable_skip. apply IHHP; intuition.
    - cbn. intro fz. cbn.
      destruct (eqv_dec fz (f y)); destruct (eqv_dec fz (f x)); [|reflexivity..].
      assert (eqv (f y) (f x)) by (eauto using eqv_sym, eqv_trans).
      apply HF in H; intuition. rewrite H. reflexivity.
    - eapply Stable_trans. apply IHHP1; eauto using Permutation_sym, Permutation_trans.
      apply IHHP2; intuition.
      apply HF; eauto using Permutation_in, Permutation_sym.
  Qed.
End Preserve.
