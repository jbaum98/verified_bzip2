Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.

Import Coq.Lists.List.ListNotations.

Section StableInd.
  Context {A : Type} `{E: EqDec A}.

  (* StablePerm l l' means that there exists a stable permutation
     from l to l'. That means that the permutation doesn't swap any
     elements considered equivalent by the equivalence relation E. *)

  Inductive StablePerm : list A -> list A -> Prop :=
  | stable_perm_nil : StablePerm nil nil
  | stable_perm_skip : forall (x : A) (l l' : list A),
      StablePerm l l' -> StablePerm (x :: l) (x :: l')
  | stable_perm_swap : forall (x y : A) (l : list A),
      x =/= y -> StablePerm (y :: x :: l) (x :: y :: l)
  | stable_perm_trans : forall l l' l'' : list A,
      StablePerm l l' -> StablePerm l' l'' -> StablePerm l l''.

  Lemma stable_perm_refl : forall l, StablePerm l l.
  Proof. induction l; constructor; auto. Qed.

  Lemma stable_perm_sym : forall l l',
      StablePerm l l' -> StablePerm l' l.
  Proof.
    intros l l' HS.
    induction HS; econstructor; eauto.
    symmetry. auto.
  Qed.
End StableInd.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) StablePerm
    reflexivity proved by stable_perm_refl
    symmetry proved by stable_perm_sym
    transitivity proved by stable_perm_trans
      as stable_perm_rel.

Section StableFilter.
  Context {A : Type} `{E : EqDec A}.

  (* Much of this is part is taken from Xavier Leroy
     https://xavierleroy.org/coq/Mergesort.html
   *)

  (* This is an alternative definition of lists for which there exists
     a stable permutation. *)

  Definition StableFilter (l l': list A) : Prop :=
    forall x, filter (equiv_decb x) l = filter (equiv_decb x) l'.

  Lemma StableFilter_refl:
    forall l, StableFilter l l.
    intros; red; intros; auto.
  Qed.

  Lemma StableFilter_trans:
    forall l1 l2 l3, StableFilter l1 l2 -> StableFilter l2 l3 -> StableFilter l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (equiv_decb x) l2); auto.
  Qed.

  Lemma StableFilter_sym : forall l l',
      StableFilter l l' -> StableFilter l' l.
  Proof.
    intros l l' H x.
    specialize (H x).
    erewrite eq_sym; eauto.
  Qed.

  Remark filter_app: forall (f : A -> bool) l l',
      filter f (l ++ l') = filter f l ++ filter f l'.
  Proof.
    induction l; intros; simpl. auto.
    destruct (f a); simpl. f_equal; auto. auto.
  Qed.

  Lemma StableFilter_app: forall l l' m m',
      StableFilter l l' -> StableFilter m m' -> StableFilter (l ++ m) (l' ++ m').
  Proof.
    intros; red; intros. repeat rewrite filter_app. f_equal; auto.
  Qed.

  Lemma StableFilter_skip: forall a l l',
      StableFilter l l' -> StableFilter (a::l) (a::l').
  Proof.
    intros; red; intros. simpl.
    destruct (x ==b a); simpl. f_equal; auto. auto.
  Qed.

  Lemma StableFilter_swap: forall a b l,
      a =/= b -> StableFilter (a::b::l) (b::a::l).
  Proof.
    intros; red; intros. simpl.
    unfold equiv_decb.
    case_eq (equiv_dec x a); intro; simpl; auto.
    case_eq (equiv_dec x b); intro; simpl; auto.
    elim H. unfold equiv_decb in *.
    eapply equiv_transitive. apply equiv_symmetric; eauto. eauto.
  Qed.

  Lemma StableFilter_nil_iff : forall l,
      StableFilter nil l <-> l = nil.
  Proof.
    split; [|intros H; rewrite H; apply StableFilter_refl].
    induction l; [easy|].
    unfold StableFilter; cbn.
    intro S; specialize (S a).
    unfold equiv_decb at 1 in S.
    destruct (equiv_dec a a); [|exfalso; apply c; reflexivity].
    inversion S.
  Qed.

  Lemma StableFilter_uncons : forall x l l',
      StableFilter (x :: l) (x :: l') -> StableFilter l l'.
  Proof.
    intros x l l' HS y; specialize (HS y); cbn in HS.
    destruct (y ==b x); [injection HS|]; auto.
  Qed.

  Lemma StableFilter_unswap : forall x y l,
      StableFilter (x :: y :: l) (y :: x :: l) -> x =/= y \/ x = y.
  Proof.
    intros x y l HS.
    specialize (HS x).
    assert (filter_cons : forall f (h : A) t,
               filter f (h :: t) = if f h then h :: filter f t else filter f t)
           by reflexivity.
    rewrite filter_cons in HS; unfold equiv_decb at 1 in HS.
    destruct (x == x); [|exfalso; apply c; reflexivity].
    rewrite (filter_cons _ y (x :: l)) in HS; unfold equiv_decb at 2 in HS.
    destruct (x == y); [right; inversion HS|left]; auto.
  Qed.
End StableFilter.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) StableFilter
    reflexivity proved by StableFilter_refl
    symmetry proved by StableFilter_sym
    transitivity proved by StableFilter_trans
      as StableFilter_rel.

(* We want to show that both definitions are equivalent. In fact, we
   can prove that StableFilter l l' -> Permutation l l', but for the
   purposes of this example we'll just include it as a separate
   premise. *)

Theorem perm_stable_stable_perm {A} `{E : EqDec A} : forall l l' : list A,
    Permutation l l' -> StableFilter l l' -> StablePerm l l'.
Proof.
  intros l l' HP; induction HP; intros HS.
  - apply stable_perm_nil.
  - apply stable_perm_skip; apply IHHP.
    eapply StableFilter_uncons; eauto.
  - destruct (StableFilter_unswap _ _ _ HS).
    + apply stable_perm_swap; symmetry; auto.
    + subst. do 2 apply stable_perm_skip. reflexivity.
  - admit.
Admitted.
