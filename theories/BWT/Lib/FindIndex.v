Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.PeanoNat.

Import Coq.Lists.List.ListNotations.

Require Import BWT.Lib.Sumbool.

Section FindIndex.
  Context {A : Type} `{EqDec A}.

  Fixpoint findIndex (x : A) (ls : list A) : nat :=
    match ls with
    | [] => 0
    | hd :: tl =>
      match x == hd with
      | left _ => 0
      | right _ => S (findIndex x tl)
      end
    end.

  Theorem findIndex_correct : forall x xs d,
      Exists (equiv x) xs -> nth (findIndex x xs) xs d === x.
  Proof.
    intros x xs d E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + apply IHE.
  Qed.

  Theorem findIndex_bounds : forall x xs,
      Exists (equiv x) xs -> findIndex x xs < length xs.
  Proof.
    intros x xs E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + simpl. apply le_n_S. apply IHE.
  Qed.

  Theorem findIndex_nth : forall i xs d,
      (forall x y, x === y -> x = y) ->
      NoDup xs ->
      i < length xs ->
      findIndex (nth i xs d) xs = i.
  Proof.
    intros i xs d eqv_eq ND HI.
    assert (E : Exists (equiv (nth i xs d)) xs). {
      apply Exists_exists. exists (nth i xs d).
      split; [|easy].
      apply nth_In. easy.
    }
    apply (NoDup_nth xs d);
      [|apply findIndex_bounds|
       |apply eqv_eq; rewrite findIndex_correct]; easy.
  Qed.

  Theorem findIndex_map : forall f xs x,
      (forall x y, x === y -> x = y) ->
      NoDup (map f xs) ->
      Exists (equiv x) xs ->
      findIndex (f x) (map f xs) = findIndex x xs.
  Proof.
    intros f xs x eqv_eq.
    revert x; induction xs; intros x ND E; [easy|].
    cbn.
    destruct (f x == f a).
    - rewrite if_true. easy.
      apply eqv_eq in e.
      cbn in ND. apply NoDup_cons_iff in ND.
      destruct ND as [HNIn ND].
      apply Exists_exists in E.
      destruct E as [x' [HIn HX]].
      apply eqv_eq in HX; subst x'.
      destruct HIn; [subst; easy|].
      apply in_map with (f := f) in H0.
      rewrite e in H0.
      contradiction.
    - destruct (x == a).
      + apply eqv_eq in e.
        rewrite e in c.
        exfalso; apply c; reflexivity.
      + f_equal.
        apply IHxs; [apply NoDup_cons_iff in ND; easy|].
        apply Exists_cons in E.
        destruct E; easy.
  Qed.

  Theorem findIndex_cons : forall xs x y,
      x =/= y ->
      findIndex x (y :: xs) = S (findIndex x xs).
  Proof.
    intros xs x y NE.
    cbn. rewrite if_false by easy.
    easy.
  Qed.
End FindIndex.
