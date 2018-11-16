(** An implementation of equivalence and lexicographic ordering for
    lists, only looking at the first k elements of the list. **)

Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Mergesort.
Require Import BWT.Sorting.Sorted.

Import ListNotations.

Section LeK.

  Context {A : Type} `{Ord A}.
  Open Scope ord_scope.

  Inductive le_k : nat -> list A -> list A -> Prop :=
  | le_nil     : forall ys k, le_k k [] ys
  | le_zero    : forall xs ys, le_k 0 xs ys
  | le_cons_lt : forall x y xs ys k, x < y -> le_k k (x :: xs) (y :: ys)
  | le_cons_eq : forall x y xs ys k, x === y -> le_k k xs ys ->
                                le_k (S k) (x :: xs) (y :: ys).

  Notation "x <={ k } y" :=
    (le_k k x y) (at level 70, no associativity, format "x  <={ k }  y") : ord_scope.

  Theorem le_k_trans : forall k x y z, x <={k} y -> y <={k} z -> x <={k} z.
  Proof.
    intros k x y z LXY. revert z.
    induction LXY; intros z LYZ; inversion LYZ; subst; clear LYZ;
      try apply le_nil; try apply le_zero; try discriminate;
        [apply le_cons_lt|apply le_cons_lt|apply le_cons_lt|apply le_cons_eq];
        repeat match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; subst; clear H
        | [ H : _ === _ |- _ ] => try (rewrite H || rewrite <- H); clear H
        end; eauto using lt_trans, eqv_refl.
  Defined.

  Theorem le_k_total : forall k x y, x <={k} y \/ y <={k} x.
  Proof.
    intros k x. revert k.
    induction x as [|x xs]; intros k y; destruct y as [|y ys]; eauto using le_nil.
    destruct (lt_eq_dec x y) as [[LXY|E]|LYX]; eauto using le_cons_lt.
    destruct k; eauto using le_zero.
    edestruct IHxs; eauto using le_cons_eq, eqv_sym.
  Defined.

  Program Fixpoint le_k_dec k xs ys : { xs <={k} ys } + { ~ xs <={k} ys } :=
    match k with
    | O   => left _
    | S k =>
      match (xs, ys) with
      | (nil, _)      => left  _
      | (_ :: _, nil) => right _
      | (x :: xs, y :: ys) =>
        match lt_eq_dec x y with
        | inleft (left _) => left _  (* < *)
        | inright _       => right _ (* > *)
        | inleft (right _) =>
          match (le_k_dec k xs ys) with
          | left  _ => left _
          | right _ => right _
          end
        end
      end
    end.
  Next Obligation. apply le_zero. Defined.
  Next Obligation. apply le_nil.  Defined.
  Next Obligation. intro c; inversion c. Defined.
  Next Obligation. apply le_cons_lt. auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_excl; split; eauto.
    - eapply lt_not_eq; eauto using eqv_sym.
  Defined.
  Next Obligation. apply le_cons_eq; auto. Defined.
  Next Obligation.
    intro c. inversion c; subst; clear c.
    - eapply lt_not_eq; eauto.
    - contradiction.
  Defined.

  Theorem le_k_tl : forall k x y a,
      a :: x <={S k} a :: y -> x <={k} y.
  Proof.
    intros k x y a HS.
    inversion HS; subst; clear HS.
    - exfalso; eapply lt_irrefl; eauto.
    - simpl. auto.
  Qed.
End LeK.

Instance Ord_list_k {A} `{Ord A} (k : nat) : Ord (list A) :=
  { le := le_k k;
    le_trans := le_k_trans k;
    le_total := le_k_total k;
    le_dec := le_k_dec k;
  }.

Theorem le_uncons {A} `{Ord A} : forall k a b x y,
    @le _ (Ord_list_k (S k)) (a :: x) (b :: y) ->
    eqv a b -> @le _ (Ord_list_k k) x y.
Proof.
  intros k a b x y HE.
  inversion HE; subst; clear HE; intros.
  apply lt_not_eq in H2. contradiction.
  auto.
Qed.

Theorem eqv_uncons {A} `{Ord A} : forall k a b x y,
    @eqv _ (Ord_list_k (S k)) (a :: x) (b :: y) ->
    eqv a b /\ @eqv _ (Ord_list_k k) x y.
Proof.
  intros k a b x y HE.
  destruct HE as [LA LB].
  inversion LA; inversion LB; subst; clear LA LB.
  - exfalso. eapply lt_excl. intuition eauto.
  - apply lt_not_eq in H2. apply eqv_sym in H10. contradiction.
  - apply lt_not_eq in H9. apply eqv_sym in H4. contradiction.
  - unfold eqv in *. intuition.
Qed.

Theorem eqv_cons {A} `{Ord A} : forall k a b x y,
    @eqv _ (Ord_list_k  k) x y -> eqv a b ->
    @eqv _ (Ord_list_k (S k)) (a :: x) (b :: y).
Proof.
  intros k a b x y HEtl HEhd.
  split; apply le_cons_eq; auto using eqv_sym;
  destruct HEtl; auto.
Qed.

Add Parametric Morphism {A} `{O : Ord A} {k} : cons with
      signature (@eqv A O) ==>
                 (@le (list A) (@Ord_list_k A O k)) ==>
                 (@le (list A) (@Ord_list_k A O (S k))) as cons_eqv.
Proof. intros. eapply le_cons_eq; auto. Qed.

Theorem Forall2_uncons {A} : forall (P : A -> A -> Prop) a b x y,
    Forall2 P (a :: x) (b :: y) ->
    P a b /\ Forall2 P x y.
Proof.
  intros.
  inversion H; subst; clear H.
  intuition.
Qed.

Theorem eqv_k_correct {A} `{Ord A} : forall k x y,
    length x >= k -> length y >= k ->
    @eqv _ (Ord_list_k k) x y <-> Forall2 eqv (firstn k x) (firstn k y).
Proof.
  induction k; intros.
  - simpl. split; constructor; apply le_zero.
  - destruct x; destruct y.
    + simpl. split; constructor; apply le_nil.
    + simpl in *; omega.
    + simpl in *; omega.
    + split; intros.
      * simpl. constructor.
        eapply eqv_uncons; eauto.
        apply IHk; simpl in *; try omega; auto.
        eapply eqv_uncons; eauto.
      * eapply eqv_cons.
        apply IHk; simpl in *; try omega.
        eapply Forall2_uncons. eauto.
        eapply Forall2_uncons. eauto.
Qed.

Section Sort.
  Context {A : Type} `{Ord A}.

  Variable k : nat.
  Let Ok := Ord_list_k k.

  Program Definition sort :  list (list A) -> list (list A)
    := @mergesort _ Ok.

  Lemma sort_props : forall l,
      @Sorted _ Ok (sort l) /\
      Permutation (sort l) l /\
      @Stable _ Ok (sort l) l.
  Proof.
    intros.
    unfold sort. case (mergesort l). intros l' [S [P St]].
    cbn. intuition.
  Qed.

  Theorem sort_sorted : forall l,
      @Sorted _ Ok (sort l).
  Proof. apply sort_props. Qed.

  Theorem sort_perm : forall l,
      Permutation (sort l) l.
  Proof. apply sort_props. Qed.

  Theorem sort_stable : forall l,
      @Stable _ Ok (sort l) l.
  Proof. apply sort_props. Qed.

  Theorem sort_length : forall l,
      length (sort l) = length l.
  Proof.
    intros.
    apply Permutation_length.
    apply sort_perm.
  Qed.

  Theorem sort_nil : sort [] = [].
  Proof.
    apply Permutation_nil. apply Permutation_sym. apply sort_perm.
  Qed.
End Sort.

Section SortedK.
  Context {A : Type} `{Ord A}.

  Local Arguments Sorted {_} _.
  Local Arguments le {_} _.

  Theorem sorted_zero : forall l,
      Sorted (Ord_list_k 0) l.
  Proof.
    intros.
    apply Sorted_LocallySorted_iff.
    induction l as [|a [|b l]]; constructor; auto.
    apply le_zero.
  Qed.

  Theorem sort_zero : forall l : list (list A),
    sort 0 l = l.
  Proof.
    intros.
    unfold sort. case (mergesort l) as [l' [S [P St]]]; cbn.
    apply @stable_sort_unique with (O := Ord_list_k 0); auto using sorted_zero.
  Qed.

  Theorem le_k_S : forall k x y,
      le_k (S k) x y -> le_k k x y.
  Proof.
    intros k x y HL. remember (S k) as k'. generalize dependent k.
    induction HL; intros; subst.
    - constructor.
    - discriminate.
    - constructor; auto.
    - destruct k0; [apply le_zero|].
      apply le_cons_eq; auto.
  Qed.

  Theorem sorted_S : forall k l,
      Sorted (Ord_list_k (S k)) l -> Sorted (Ord_list_k k) l.
  Proof.
    intros k l HS. remember (S k) as k'. generalize dependent k.
    induction HS; intros; subst; constructor.
    - intros. apply le_k_S. apply H0. apply H1.
    - apply IHHS. auto.
  Qed.

  Theorem sorted_hd : forall k a l,
      Sorted (Ord_list_k k) (a :: l) ->
      forall x, In x l -> le_k k a x.
  Proof.
    intros k a l HS.
    inversion HS; subst; clear HS.
    intros. apply H2. apply H0.
  Qed.

  Lemma eq_hd_in_tl : forall a l x,
      Forall (fun x => exists t, x = a :: t) l ->
      In x (map (@tl A) l) -> In (a :: x) l.
  Proof.
    intro a. induction l; intros x Hhd HI; [contradiction HI|].
    destruct HI.
    - left. rewrite <- H0.
      apply Forall_forall with (x := a0) in Hhd.
      destruct Hhd.
      rewrite H1. reflexivity.
      intuition.
    - right. apply IHl; auto.
      inversion Hhd; auto.
  Qed.
End SortedK.

Theorem Forall_tl {A} : forall (P : A -> Prop) l a,
    Forall P (a :: l) -> Forall P l.
Proof. intros P l a HF. inversion HF; auto. Qed.

Section StartWith.
  Context {A : Type}.

  Lemma sorted_hd_nonempty `{Ord A} : forall k a l x s,
      @Sorted _ (Ord_list_k (S k)) ((a :: l) :: s) ->
      In x s -> x <> [].
  Proof.
    intros k a l x s HS HI.
    assert (n: ~ @le _ (@Ord_list_k _ _ (S k)) (a :: l) []) by (intro c; inversion c).
    intro c; apply n; clear n.
    inversion HS; subst; clear HS.
    apply H2. auto.
  Qed.

  Theorem sort_tl `{Ord A} : forall k mat a d,
      @Sorted _ (Ord_list_k (S k)) mat ->
      Forall (fun x => eqv a (hd d x)) mat ->
      @Sorted _ (Ord_list_k k) (map (@tl _) mat).
  Proof.
    intros k.
    induction mat as [|l mat IH]; intros a d HS Ha; [constructor|].
    simpl. constructor.
    - intros x HI.
      destruct l as [|lhd ltl] eqn:HL; [constructor|].
      simpl.
      inversion Ha. subst x0 l0; clear Ha.
      apply le_uncons with (a0 := lhd) (b := a); auto using eqv_sym.
      destruct (proj1 (in_map_iff _ _ _) HI) as [xfull [Hx HI']].
      destruct xfull as [|xhd xtl]; [exfalso; eapply sorted_hd_nonempty; eauto|].
      simpl in Hx. subst x.
      apply le_trans with (y := xhd :: xtl).
      eapply Sorted_uncons. apply HS. auto.
      apply le_cons_eq; [|apply (@le_refl _ (Ord_list_k k))].
      eapply Forall_forall in H3; eauto.
      simpl in H3. auto using eqv_sym.
    - eapply IH.
      eapply Sorted_uncons. eauto.
      inversion Ha. eauto.
  Qed.
End StartWith.
