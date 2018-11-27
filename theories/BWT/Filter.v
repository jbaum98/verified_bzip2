Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FinFun.
Require Import Coq.Sorting.Permutation.
Require Import FunInd.

Section Filter.
  Context {A T F} (f : forall y : A, {T y} + {F y}).

  Function filter l : list A :=
    match l with
    | nil => nil
    | x :: tl => if f x then x :: filter tl else filter tl
    end.

  Theorem filter_length : forall l,
      length (filter l) <= length l.
  Proof. intros; functional induction (filter l); cbn; omega. Qed.

  Theorem filter_length_cons : forall l a,
      length (filter (a :: l)) >= length (filter l).
  Proof. intros; simpl; destruct (f a); simpl; omega. Qed.

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

  Ltac sub_sumbool :=
    match goal with
    | H : ?x = left ?pf |- context ctx[if ?x then ?a else ?b] =>
      let Hdestr := fresh "Hdestr" in
      destruct x eqn:Hdestr;
      [|try rewrite Hdestr in *; discriminate]; clear Hdestr H
    | H : ?x = right ?pf |- context ctx[if ?x then ?a else ?b] =>
      let Hdestr := fresh "Hdestr" in
      destruct x eqn:Hdestr;
      [try rewrite Hdestr in *; discriminate|]; clear Hdestr H
    end.

  Remark filter_app: forall (l l': list A),
      filter (l ++ l') = filter l ++ filter l'.
  Proof.
    intros l;
      functional induction (filter l) as [|l a x _ prf HL IH|l a x _ prf HR IH];
      intros; cbn; try sub_sumbool; try rewrite IH; easy.
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

  Theorem filter_Forall : forall l,
      Forall T (filter l).
  Proof.
    induction l.
    - constructor.
    - simpl. destruct (f a).
      constructor; auto.
      auto.
  Qed.

  Fixpoint unfilter_ix (l : list A) : nat -> nat :=
    match l with
    | nil => fun _ => 0
    | a :: l =>
      if f a then
        fun i => match i with
              | O => O
              | S i => S (unfilter_ix l i)
              end
      else fun i => S (unfilter_ix l i)
    end.

  Theorem unfilter_ix_bounded : forall l i,
      i < length (filter l) ->
      unfilter_ix l i < length l.
  Proof.
    induction l; intros.
    - cbn. destruct i; cbn in *; omega.
    - cbn [filter unfilter_ix] in *.
      destruct (f a); destruct i; cbn in *; auto with zarith arith.
  Qed.

  Theorem unfilter_ix_inj : forall l i j,
      i < length (filter l) ->
      j < length (filter l) ->
      unfilter_ix l i = unfilter_ix l j -> i = j.
  Proof.
    induction l; intros.
    - cbn. destruct i; cbn in *; omega.
    - cbn [filter unfilter_ix] in *.
      destruct (f a); destruct i; destruct j; cbn in *; auto with zarith arith.
  Qed.

  Theorem unfilter_ix_correct : forall l i d,
      i < length (filter l) ->
      nth i (filter l) d = nth (unfilter_ix l i) l d.
  Proof.
    induction l; intros.
    - cbn. destruct i; cbn in *; omega.
    - cbn [filter unfilter_ix] in *.
      destruct (f a); destruct i; cbn in *; auto with zarith arith.
  Qed.

  Theorem unfilter_ix_strict : forall l i j,
      i < length (filter l) ->
      j < length (filter l) ->
      (i < j <-> unfilter_ix l i < unfilter_ix l j).
  Proof.
    intros l i j Hi Hj.
    split; revert i j Hi Hj;
      (induction l; intros;
       [cbn; destruct i; cbn in *; omega
       |cbn in *; destruct (f a); destruct i; destruct j; cbn in *;
        auto with arith zarith]).
  Qed.

  Theorem unfilter_ix_monotonic : forall l i j,
      i < length (filter l) ->
      j < length (filter l) ->
      (i <= j <-> unfilter_ix l i <= unfilter_ix l j).
  Proof.
    intros.
    split; intros; destruct (Nat.eq_dec i j);
      [subst;auto| |subst;auto| ];
      [assert (i < j) by omega|
       assert (unfilter_ix l i <> unfilter_ix l j) by
           (intro c; apply unfilter_ix_inj in c; [contradiction|auto..])];
      apply Nat.lt_le_incl;
      apply unfilter_ix_strict with (l := l) (i := i) (j := j); auto with zarith.
  Qed.

  Fixpoint filter_ix (l : list A) : nat -> nat :=
    match l with
    | nil => fun _ => 0
    | a :: l =>
      if f a then
        fun i => match i with
              | O => O
              | S i => S (filter_ix l i)
              end
      else fun i => match i with
                 | O => O
                 | S i => filter_ix l i
                 end
    end.

  Theorem filter_ix_bounded : forall l i d,
      i < length l ->
      (exists PF, f (nth i l d) = left PF) ->
      filter_ix l i < length (filter l).
  Proof.
    induction l; intros i d HL HT.
    - cbn in *; omega.
    - specialize IHl with (d := d).
      cbn in *; destruct (f a) eqn:HFA; destruct i; cbn;
        auto with zarith arith || rewrite HFA in *; destruct HT; discriminate.
  Qed.

  Theorem filter_ix_inj : forall l i j d,
      i < length l -> (exists PF, f (nth i l d) = left PF) ->
      j < length l -> (exists PF, f (nth j l d) = left PF) ->
      filter_ix l i = filter_ix l j -> i = j.
  Proof.
    induction l; intros i j d HLI HTI HLJ HTJ.
    - cbn in *; omega.
    - specialize IHl with (d := d).
      cbn in *; destruct (f a) eqn:HFA; destruct i; destruct j; cbn;
        auto with zarith arith ||
                  rewrite HFA in *; destruct HTI; destruct HTJ; discriminate.
  Qed.

  Theorem filter_ix_correct : forall l i d,
      i < length l ->
      (exists PF, f (nth i l d) = left PF) ->
      nth i l d = nth (filter_ix l i) (filter l) d.
  Proof.
    induction l; intros i d HL HT.
    - cbn in *; omega.
    - cbn in *; destruct (f a) eqn:HFA; destruct i; cbn;
        auto with zarith arith || rewrite HFA in *; destruct HT; discriminate.
  Qed.

  Theorem filter_ix_strict : forall l i j d,
      i < length l -> (exists PF, f (nth i l d) = left PF) ->
      j < length l -> (exists PF, f (nth j l d) = left PF) ->
      (i < j <-> filter_ix l i < filter_ix l j).
  Proof.
    intros l i j d Hi HTi Hj HTj.
    split; revert i j d Hi HTi Hj HTj;
      (induction l; intros;
       [cbn; destruct i; cbn in *; omega
       |specialize IHl with (d := d);
        cbn in *; destruct (f a) eqn:HFA; destruct i; destruct j; cbn in *;
        auto with arith zarith ||
                  rewrite HFA in *; destruct HTi; destruct HTj; discriminate]).
  Qed.

  Theorem filter_ix_monotonic : forall l i j d,
      i < length l -> (exists PF, f (nth i l d) = left PF) ->
      j < length l -> (exists PF, f (nth j l d) = left PF) ->
      (i <= j <-> filter_ix l i <= filter_ix l j).
  Proof.
    intros.
    split; intros;
      pose proof (filter_length l);
      destruct (Nat.eq_dec i j);
      [subst;auto| |subst;auto| ];
      [assert (i < j) by omega|
       assert (filter_ix l i <> filter_ix l j) by
           (intro c; apply filter_ix_inj with (d := d) in c; [contradiction|auto with zarith..])];
      apply Nat.lt_le_incl;
      eapply filter_ix_strict with (l := l) (i := i) (j := j); eauto with zarith.
  Qed.

  Theorem filter_perm : forall l l',
      Permutation l l' -> Permutation (filter l) (filter l').
  Proof.
    intros l l' P. induction P.
    - constructor.
    - cbn. destruct (f x); auto.
    - cbn. destruct (f x); destruct (f y); auto using perm_swap.
    - eauto using Permutation_trans.
  Qed.
End Filter.

Theorem filter_ix_map {A B T F} (f : forall y : A, {T y} + {F y}) (g : B -> A) : forall l i,
    filter_ix (fun x => f (g x)) l i = filter_ix f (map g l) i.
Proof.
  induction l; [reflexivity|].
  cbn; destruct (f (g a)); destruct i; auto.
Qed.

Section FilterInPair.
  Lemma split_cons {A B} : forall a b (l : list (A * B)),
    split ((a, b) :: l) = (a :: fst (split l), b :: snd (split l)).
  Proof. intros. cbn. destruct (split l). reflexivity. Qed.

  Theorem filter_in_pair_l {A B} (E: forall x y : A, {x = y} + {x <> y}) :
    forall l (a : A) (b : B),
      In (a, b) l <-> In b (snd (split (filter (fun x => E a (fst x)) l))).
  Proof.
    induction l as [|[hda hdb] tl]; intros.
    - cbn. intuition.
    - cbn. destruct (E a hda); subst; intros; [rewrite split_cons|];
      cbn; split; intros H; try destruct H;
        try match goal with
              H : (_, _) = (_, _) |- _ =>
              inversion H; subst; clear H
            end; subst; intuition; try contradiction;
          try right; solve [apply IHtl;auto].
  Qed.

  Theorem filter_in_pair_r {A B} (E: forall x y : B, {x = y} + {x <> y}) :
    forall l (a : A) (b : B),
      In (a, b) l <-> In a (fst (split (filter (fun x => E b (snd x)) l))).
  Proof.
    induction l as [|[hda hdb] tl]; intros.
    - cbn. intuition.
    - cbn. destruct (E b hdb); subst; intros; [rewrite split_cons|];
      cbn; split; intros H; try destruct H;
        try match goal with
              H : (_, _) = (_, _) |- _ =>
              inversion H; subst; clear H
            end; subst; intuition; try contradiction;
          try right; solve [apply IHtl;auto].
  Qed.
End FilterInPair.
