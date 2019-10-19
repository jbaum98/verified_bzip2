Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Import Coq.Lists.List.ListNotations.

Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.StablePerm.
Require Import BWT.Lib.List.
Require Import BWT.Lib.TakeWhile.
Require Import BWT.Lib.Permutation.

Section KeyOrd.
  Context {A K : Type} `{O: Preord K}.

  Variable key : A -> K.

  Definition keyOrd : Preord A.
  Proof.
    apply Build_Preord with (le := fun x y => le (key x) (key y));
      intros; eauto using le_trans, le_total, le_dec.
  Defined.

  Local Arguments le {_} _.
  Local Arguments lt {_} _.
  Local Arguments eqv {_} _.
  Local Arguments le_dec {_} _.

  Remark key_le : forall x y,
      le keyOrd x y = le O (key x) (key y).
  Proof. reflexivity. Qed.

  Remark key_lt : forall x y,
      lt keyOrd x y = lt O (key x) (key y).
  Proof. reflexivity. Qed.

  Remark key_eqv : forall x y,
      eqv keyOrd x y = eqv O (key x) (key y).
  Proof. reflexivity. Qed.

  Remark key_le_dec : forall x y,
      le_dec keyOrd x y = le_dec O (key x) (key y).
  Proof. reflexivity. Qed.

  Section Inv.
    Variable f : A -> A.
    Hypothesis HF : forall x, key (f x) = key x.

    Local Arguments insert {_} _.
    Local Arguments sort {_} _.

    Lemma key_insert_inv : forall x l,
       insert keyOrd (f x) (map f l) = map f (insert keyOrd x l).
    Proof.
      induction l; [reflexivity|].
      simpl. rewrite !HF.
      destruct (le_dec _ (key x) (key a)).
      - reflexivity.
      - simpl; f_equal.
        apply IHl.
    Qed.

    Theorem key_sort_inv : forall l,
        sort keyOrd (map f l) = map f (sort keyOrd l).
    Proof.
      induction l; [reflexivity|].
      simpl. rewrite <- key_insert_inv, IHl.
      reflexivity.
    Qed.
  End Inv.

  Local Arguments Sorted {_} _.

  Theorem key_sorted : forall l,
      Sorted keyOrd l <-> Sorted O (map key l).
  Proof.
    induction l; [split; intros; apply Sorted_nil|].
    split; cbn; intros HS; apply Sorted_cons_inv in HS; destruct HS as [HLe HS].
    - cbn. apply Sorted_cons.
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [kx [Hkx HIn]].
      rewrite <- Hkx. rewrite Forall_forall in HLe. apply HLe. auto.
      apply IHl; auto.
    - apply Sorted_cons. rewrite Forall_forall.
      intros. rewrite Forall_forall in HLe. apply HLe. apply in_map. auto.
      apply IHl. auto.
  Qed.
End KeyOrd.

Section Firstn.
  Context {A : Type} {O: Preord A}.

  Local Arguments le {_} _.
  Local Arguments lt {_} _.
  Local Arguments eqv {_} _.
  Local Arguments le_dec {_} _.

  Definition lexle_firstn n := keyOrd(firstn n).

  Theorem key_le_firstn_O : forall x y,
      le (keyOrd (firstn 0)) x y.
  Proof.
    intros. rewrite key_le.
    apply lex_le_nil.
  Qed.

  Theorem key_le_firstn_1 : forall hx hy tx ty,
      le (keyOrd (firstn 1)) (hx :: tx) (hy :: ty) ->
      le _ hx hy.
  Proof.
    intros. rewrite key_le in H. cbn in H.
    inversion H; subst.
    - apply lt_le; auto.
    - unfold eqv in H3; intuition.
  Qed.

  Theorem key_lt_firstn_1 : forall hx hy tx ty,
      lt (keyOrd (firstn 1)) (hx :: tx) (hy :: ty) ->
      lt _ hx hy.
  Proof.
    intros. rewrite key_lt in H; cbn in H.
    intro c.
    apply H.
    apply lt_spec in c.
    destruct c.
    - apply lex_le_cons_lt. auto.
    - apply lex_le_cons_eq. auto. constructor.
  Qed.

  Theorem key_eqv_firstn_1 : forall hx hy tx ty,
      eqv (keyOrd (firstn 1)) (hx :: tx) (hy :: ty) ->
      eqv _ hx hy.
  Proof.
    intros. rewrite key_eqv in H.
    cbn in H. destruct H.
    apply key_le_firstn_1 with (tx := nil) (ty := nil) in H.
    apply key_le_firstn_1 with (tx := nil) (ty := nil) in H0.
    unfold eqv. intuition.
  Qed.

  Theorem key_le_firstn_S : forall j x y,
      le (keyOrd (firstn (S j))) x y ->
      le (keyOrd (firstn j)) x y.
  Proof.
    intros.
    rewrite key_le in *.
    apply lt_spec in H.
    destruct H.
    + apply lex_lt_destr in H.
      destruct H as [hx [tx [hy [ty [a [Hx [Hy [Hlt Heq]]]]]]]].
      remember (length hx) as n.
      assert (Heqn' : n = length hy). {
        apply lex_eqv_iff in Heq.
        subst n. eapply Forall2_length; eauto.
      }
      destruct (Nat.le_gt_cases (S j) n).
      * assert (HT: tx = nil /\ (a :: ty) = nil). {
          apply f_equal with (f := @length A) in Hx; apply f_equal with (f := @length A) in Hy.
          rewrite app_length in *.
          rewrite <- Heqn in Hx. rewrite <- Heqn' in Hy.
          pose proof (firstn_le_length (S j) x).
          pose proof (firstn_le_length (S j) y).
          cbn [length] in Hy.
          split; apply length_zero_iff_nil; omega.
        }
        destruct HT. discriminate.
      * assert (HLE : n <= j) by omega.
        apply Nat.le_exists_sub in HLE.
        destruct HLE as [p [HP _]].
        apply f_equal with (f := firstn j) in Hx; apply f_equal with (f := firstn j) in Hy.
        rewrite firstn_firstn in *.
        replace (Nat.min j (S j)) with j in * by (symmetry; apply Nat.min_l; omega).
        rewrite plus_comm in HP.
        rewrite HP in Hx at 2, Hy at 2; rewrite Heqn in Hx; rewrite Heqn' in Hy.
        rewrite firstn_app_2 in Hx, Hy.
        rewrite Hx, Hy.
        apply lex_eqv_prepend; auto.
        destruct p; [rewrite firstn_O; apply lex_le_nil|].
        apply lex_lt_iff in Hlt.
        inversion Hlt; subst; clear Hlt.
        rewrite firstn_nil; apply lex_le_nil.
        apply lex_le_cons_lt; auto.
        inversion H4.
    + assert (HLJ : forall l : list A, firstn j l = firstn j (firstn (S j) l)). {
        intros l.
        rewrite firstn_firstn.
        replace (Nat.min j (S j)) with j by (symmetry; apply Nat.min_l; omega).
        reflexivity.
      }
      assert (HE: eqv List_Lex_Preord (firstn j x) (firstn j y)). {
        rewrite (HLJ x), (HLJ y).
        apply lex_eqv_firstn.
        auto.
      }
      destruct HE as [HE _].
      auto.
  Qed.

  Theorem key_le_firstn_ge : forall k j x y,
      j <= k ->
      le (keyOrd (firstn k)) x y ->
      le (keyOrd (firstn j)) x y.
  Proof.
    induction k; intros j x y HJK HLeK.
    - assert (j = 0) by omega.
      subst j. apply key_le_firstn_O.
    - apply le_lt_or_eq in HJK.
      destruct HJK.
      apply IHk. omega.
      apply key_le_firstn_S. auto.
      rewrite H. auto.
  Qed.

  Theorem key_firstn_S : forall n x y,
      le (keyOrd (firstn 1)) x y ->
      le (keyOrd (firstn n)) (tl x) (tl y) ->
      le (keyOrd (firstn (S n))) x y.
  Proof.
    induction n; intros x y L1 Ln; [auto|].
    remember (S n) as n'.
    destruct x as [|hx tx]; [apply lex_le_nil|].
    destruct y as [|hy ty]; [apply lex_le_not_nil_r in L1; contradiction|].
    rewrite key_le; cbn.
    apply lt_spec in L1; destruct L1 as [HLt | HEq].
    - apply lex_le_cons_lt.
      apply key_lt_firstn_1 in HLt. auto.
    - apply lex_le_cons_eq.
      apply key_eqv_firstn_1 in HEq. auto.
      cbn [tl] in Ln. apply Ln.
  Qed.

  Theorem key_lt_firstn_S : forall j x y,
      lt (keyOrd (firstn j)) x y ->
      lt (keyOrd (firstn (S j))) x y.
  Proof.
    induction j; intros x y HLT; apply lex_lt_iff in HLT; apply lex_lt_iff.
    - rewrite !firstn_O in HLT.
      inversion HLT.
    - remember (S j) as j'.
      destruct x as [|hx tx]; (destruct y as [|hy ty]; [rewrite firstn_nil in HLT; inversion HLT|]).
      + apply lex_lt_nil.
      + rewrite Heqj', !firstn_cons in HLT.
        inversion HLT; subst x y xs ys; clear HLT.
        * apply lex_lt_cons_lt; auto.
        * rewrite !firstn_cons.
          apply lex_lt_cons_eq; auto.
          subst j'.
          apply lex_lt_iff; apply IHj.
          apply lex_lt_iff; auto.
  Qed.

  Theorem key_lt_firstn_ge : forall k j x y,
      j <= k ->
      lt (keyOrd (firstn j)) x y ->
      lt (keyOrd (firstn k)) x y.
  Proof.
    induction k; intros j x y HJK HLtK.
    - assert (j = 0) by omega.
      subst j. apply lex_lt_iff in HLtK. inversion HLtK.
    - apply le_lt_or_eq in HJK.
      destruct HJK.
      apply key_lt_firstn_S. apply (IHk j); [omega|auto].
      rewrite <- H. auto.
  Qed.

  Local Arguments StablePerm {_} {_} {_} _.
  Local Arguments Preord_EqDec {_} _.

  Theorem PrefixStable_le : forall i j l l',
      i <= j ->
      StablePerm (Preord_EqDec (keyOrd (firstn i))) l l' ->
      StablePerm (Preord_EqDec (keyOrd (firstn j))) l l'.
  Proof.
    intros i j l l' HIJ.
    apply StablePerm_weaken.
    intros; apply key_le_firstn_ge with (k := j); easy.
  Qed.

  Theorem PrefixStable_length : forall n l l',
      Forall (fun x => length x = n) l ->
      StablePerm (Preord_EqDec (keyOrd (firstn n))) l l' ->
      StablePerm (Preord_EqDec (List_Lex_Preord)) l l'.
  Proof.
    intros n l l' Hn.
    apply StablePerm_weaken.
    cbn. intros x y Hx Hy.
    rewrite Forall_forall in Hn.
    assert (length x = n) by (apply Hn; easy).
    assert (length y = n) by (apply Hn; easy).
    rewrite !firstn_all2 by omega.
    easy.
  Qed.

  Theorem PrefixStable_firstn_1 : forall l l',
      StablePerm (Preord_EqDec (keyOrd (firstn 1))) l l' ->
      StablePerm (Preord_EqDec (List_Lex_Preord)) l l'.
  Proof.
    intros l l'.
    apply StablePerm_weaken.
    cbn [le List_Lex_Preord keyOrd].
    intros x y Hx Hy.
    intro HLe.
    destruct x; [apply lex_le_nil|].
    destruct y; [apply lex_le_not_nil_r in HLe; contradiction|].
    cbn.
    inversion HLe; subst; clear HLe.
    - apply lex_le_cons_lt; easy.
    - apply lex_le_cons_eq; [|constructor]; easy.
  Qed.
End Firstn.

Section HdSort.
  Context {A : Type} `{O: Ord A}.

  Definition hdsort : list (list A) -> list (list A)
    := @sort _ (keyOrd (firstn 1)).
End HdSort.

Section Prefix.
  Context {A : Type} `{O: Preord A}.

  Local Arguments Sorted {_} _ _.

  Definition PrefixSorted (n : nat) : list (list A) -> Prop
    := Sorted (keyOrd (firstn n)).

  Theorem PrefixSorted_zero : forall l,
      PrefixSorted 0 l.
  Proof.
    intros l. unfold PrefixSorted.
    induction l; [apply Sorted_nil|].
    apply Sorted_cons; [|easy].
    apply Forall_forall. intros; apply key_le_firstn_O.
  Qed.
End Prefix.

Section Insert.
  Context {A : Type} {P : Preord A}.

  Local Arguments eqv {_} _.
  Local Arguments le {_} _.
  Local Arguments ge {_} _.
  Local Arguments gt {_} _.
  Local Arguments le_dec {_} _.
  Local Arguments lt {_} _.
  Local Arguments tl {_}.
  Local Arguments Sorted {_}.
  Local Arguments SortedLocal {_}.
  Local Arguments StablePerm {_} _ {_} {_}.
  Local Arguments insert {_}.
  Local Arguments sort {_}.

  Let insert1 := insert (keyOrd (firstn 1)).
  Let le_dec1 := le_dec (keyOrd (firstn 1)).
  Let StablePerm1 := StablePerm (@eqv _ (keyOrd (firstn 1))).

  Theorem insert_sorted_S : forall m x j,
      PrefixSorted (S j) (hdsort m) ->
      PrefixSorted j (tl x :: map tl m) ->
      PrefixSorted (S j) (insert1 x (hdsort m)).
  Proof.
    intros m x j HShm HStm.
    destruct (@insert_destr _ (keyOrd (firstn 1)) x (hdsort m))
             as [m1 [m2 [HIm [Hm [Hm1 Hm2]]]]]; [apply sort_sorted|].
    fold insert1 in HIm.
    rewrite HIm.
    rewrite Hm in HShm.
    assert (HSm1 : PrefixSorted (S j) m1) by (apply (Sorted_app m1 m2); easy).
    assert (HSm2 : PrefixSorted (S j) m2) by (apply (Sorted_app m1 m2); easy).
    apply Sorted_app_cons.
    split; [|split]; [easy|..].
    - apply Sorted_cons; [|easy].
      apply Forall_forall.
      intros y Hy.
      apply key_firstn_S; [|apply in_map with (f := tl) in Hy];
        revert Hy; apply Forall_forall; [apply Hm2|].
      apply Forall_app with (l1 := map tl m1).
      rewrite <- map_app, <- Hm.
      apply Permutation_forall with (l := map tl m).
      apply Permutation_map. apply sort_perm.
      apply Sorted_cons_inv. apply HStm.
    - eapply Forall_impl; [|apply Hm1].
      intros y Hy.
      apply lt_le.
      apply @key_lt_firstn_ge with (j := 1); [omega|easy].
  Qed.

  Theorem hdsort_sorted_S : forall (m : list (list A)) j,
    PrefixSorted j (map tl m) ->
    PrefixSorted (S j) (hdsort m).
  Proof.
    induction m; intros j HS; [constructor|].
    cbn [hdsort sort fold_right].
    eapply insert_sorted_S; [|easy].
    apply IHm. eapply Sorted_cons_inv. apply HS.
  Qed.
End Insert.
