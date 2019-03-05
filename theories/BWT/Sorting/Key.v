Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Lib.List.

Section KeyOrd.
  Context {A K : Type} `{O: Ord K}.

  Variable key : A -> K.

  Definition keyOrd : Ord A.
  Proof.
    apply Build_Ord with (le := fun x y => le (key x) (key y));
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
End KeyOrd.

Section Firstn.
  Context {A : Type} {O: Ord A}.

  Local Arguments le {_} _.
  Local Arguments lt {_} _.
  Local Arguments eqv {_} _.
  Local Arguments le_dec {_} _.

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

  Theorem key_le_firstn_gt : forall j x y,
      le (keyOrd (firstn (S j))) x y ->
      le (keyOrd (firstn j)) x y.
  Proof.
    intros.
    rewrite key_le in *.
    apply lt_spec in H.
    destruct H.
    apply lex_lt_destr in H.
    destruct H as [hx [tx [hy [ty [Hx [Hy [Hlt Heq]]]]]]].
    remember (length hx) as n.
    assert (Heqn' : n = length hy). {
      apply lex_eqv_iff in Heq.
      subst n. eapply Forall2_length; eauto.
    }
    destruct (Nat.le_gt_cases (S j) n).
    + assert (HT: tx = nil /\ ty = nil). {
        apply f_equal with (f := @length A) in Hx; apply f_equal with (f := @length A) in Hy.
        rewrite app_length in *.
        rewrite <- Heqn in Hx. rewrite <- Heqn' in Hy.
        pose proof (firstn_le_length (S j) x).
        pose proof (firstn_le_length (S j) y).
        split; apply length_zero_iff_nil; omega.
      }
      destruct HT; subst tx ty.
      rewrite app_nil_r in *.
      apply f_equal with (f := firstn j) in Hx; apply f_equal with (f := firstn j) in Hy.
      rewrite firstn_firstn in *.
      replace (Nat.min j (S j)) with j in * by (symmetry; apply Nat.min_l; omega).
      rewrite Hx, Hy.
      apply lex_eqv_firstn. symmetry. auto.
    +
      pose proof (firstn_le_length (S j) x).
      rewrite firstn_all2 in Hx.



    destruct x as [|a x]; [rewrite firstn_nil; constructor|].
    destruct y as [|b y]; [symmetry in Hy; apply app_eq_nil in Hy; destruct Hy; subst; apply lex_lt_iff in Hlt; inversion Hlt|].
    cbn in Hx; cbn in Hy.
    destruct hx as [|hxhd hxtl].
    replace hy with (@nil A) in * by (apply lex_eqv_iff in Heq; inversion Heq; auto).



    cbn in Hx.
    rewrite key_le.
    destruct (Nat.lt_ge_cases (S j))
    Search "<".
    destruct ()

    pose proof (lex_)
    rewrite key_le in H.
    destruct (Nat.le_gt_cases (length x) (S j)).
    - rewrite firstn_all2 in H by omega.

      r
        ewrite firstn_length_le in H.

  Theorem key_le_firstn_gt : forall k j x y,
      j < k ->
      le (keyOrd (firstn k)) x y ->
      le (keyOrd (firstn j)) x y.
  Proof.
    induction k; intros j x y HJK HLeK.
    - assert (j = 0) by omega.
      subst j. apply key_le_firstn_O.
    - apply le_lt_or_eq in HJK.
      destruct HJK.
      apply IHk. omega.
      admit.
      inversion H; subst.


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
      apply IHn. cbn in Ln. app

End Firstn.

Section HdSort.
  Context {A : Type} `{O: Ord A}.

  Definition hdsort : list (list A) -> list (list A)
    := @sort _ (keyOrd (firstn 1)).

End HdSort.

Section Prefix.
  Context {A : Type} `{O: Ord A}.

  Local Arguments Sorted {_} _ _.

  Definition PrefixSorted (n : nat) : list (list A) -> Prop
    := Sorted (keyOrd (firstn n)).

  Theorem PrefixSorted_zero : forall l,
      PrefixSorted 0 l.
  Proof.
    intros l. unfold PrefixSorted.
    induction l; [apply Sorted_nil|].
    apply Sorted_cons.
    intros. apply key_firstn_O. apply IHl.
  Qed.
End Prefix.
