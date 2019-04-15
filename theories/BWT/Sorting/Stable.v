Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Wf.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Program.Utils.

Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.Ord.
Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.List.
Require Import BWT.Lib.TakeWhile.
Require Import BWT.Lib.ZipWith.
Require Import BWT.Lib.Sumbool.
Require Import BWT.Lib.EqDec.

Section Stable.
  Context {A : Type} `{E : EqDec A}.

  (** Stable permutations.  Two lists are in the [Stable] relation if
  equivalent elements appear in the same order in both lists.
  That is, if the first list is of the form [ ... x ... y ... ]
  with [x] and [y] being equivalent, the other list is also of
  the form [ ... x ... y ... ].  *)

  Definition Stable (l l': list A) : Prop :=
    forall x, filter (equiv_decb x) l = filter (equiv_decb x) l'.

  Lemma Stable_refl:
    forall l, Stable l l.
    intros; red; intros; auto.
  Qed.

  Lemma Stable_trans:
    forall l1 l2 l3, Stable l1 l2 -> Stable l2 l3 -> Stable l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (equiv_decb x) l2); auto.
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
    destruct (equiv_decb x a); simpl. f_equal; auto. auto.
  Qed.

  Lemma Stable_swap:
    forall a b l, a =/= b -> Stable (a::b::l) (b::a::l).
  Proof.
    intros; red; intros. simpl.
    unfold equiv_decb.
    case_eq (equiv_dec x a); intro; simpl; auto.
    case_eq (equiv_dec x b); intro; simpl; auto.
    elim H. unfold equiv_decb in *.
    eapply equiv_transitive. apply equiv_symmetric; eauto. eauto.
  Qed.

  Lemma Stable_cons_app:
    forall a l l1 l2,
      Stable l (l1 ++ l2) ->
      (forall b, In b l1 -> a =/= b) ->
      Stable (a :: l) (l1 ++ a :: l2).
  Proof.
    intros; red; intros. rewrite filter_app. simpl.
    generalize (H x). rewrite filter_app.
    unfold equiv_decb; case_eq (equiv_dec x a); intro; simpl; auto.
    rewrite (filter_empty _ l1). simpl. intro. congruence.
    intros. case_eq (equiv_dec x x0); intro; auto.
    elim (H0 x0); auto.
    eapply equiv_transitive; [symmetry; apply e|auto].
  Qed.

  Lemma Stable_nil : forall l,
      Stable nil l -> l = nil.
  Proof.
    induction l.
    - easy.
    - intro S.
      unfold Stable in S; cbn in S.
      specialize (S a).
      rewrite equiv_decb_refl in S.
      inversion S.
  Qed.

  Lemma Stable_unskip:
    forall a l l', Stable (a::l) (a::l') -> Stable l l'.
  Proof.
    intros a l l' HS x.
    specialize (HS x). cbn in HS.
    eqdestruct (x ==b a); [inversion HS|]; auto.
  Qed.

  Lemma Stable_1 : forall l x,
      Stable (x::nil) l -> l = x::nil.
  Proof.
    induction l; intros x HS.
    - specialize (HS x). cbn in HS.
      rewrite equiv_decb_refl in HS. inversion HS.
    - eqdestruct (a ==b x).
      + assert (a = x). {
          specialize (HS a); cbn in HS.
          rewrite equiv_decb_refl in HS.
          eqdestruct (a ==b x).
          inversion HS; auto.
        }
        subst. apply Stable_unskip in HS.
        apply Stable_nil in HS.
        subst. reflexivity.
      + specialize (HS a). cbn in HS.
        eqdestruct (a ==b x).
        rewrite equiv_decb_refl in HS.
        inversion HS.
  Qed.
End Stable.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) Stable
    reflexivity proved by Stable_refl
    symmetry proved by Stable_sym
    transitivity proved by Stable_trans
      as Stable_rel.

Section Perm.
  Context {A} `{Eq : EqDec A eq} eqv `{Equiv : EqDec A eqv}.

  Implicit Type l : list A.

  Arguments equiv_dec [_] _ {_} {_}.
  Arguments equiv_decb [_] _ {_} {_}.
  Arguments Stable [_] _ [_] [_].

  Theorem Stable_rem1 : forall l1 l2 a,
      Stable eqv (a :: l1) l2 -> Stable eqv l1 (rem1 a l2).
  Proof.
    induction l1 as [|h1 t1 IH]; intros l2 a HS.
    - cbn in HS. apply Stable_1 in HS. subst.
      cbn. rewrite if_true by reflexivity. reflexivity.
    - intro x.
      cbn. eqdestruct (equiv_decb eqv x h1).
      + rewrite filter_rem1.
        specialize (HS x). cbn in HS.
        eqdestruct (equiv_decb eqv x h1).
        eqdestruct (equiv_decb eqv x a).
        * rewrite <- HS.
          cbn. rewrite if_true by reflexivity.
          reflexivity.
        * rewrite <- HS.
          cbn. rewrite if_false.
          f_equal. rewrite rem1_not_in; [reflexivity|].
          intro c. apply filter_In in c.
          destruct c as [_ c].
          eqdestruct (equiv_decb eqv x a). inversion c.
          intro c. rewrite c in H1. contradiction.
      + specialize (HS x).
        cbn in HS. eqdestruct (equiv_decb eqv x h1).
        eqdestruct (equiv_decb eqv x a).
        * rewrite filter_rem1. rewrite <- HS.
          cbn. rewrite if_true by reflexivity.
          reflexivity.
        * rewrite filter_rem1. rewrite <- HS.
          rewrite rem1_not_in; [reflexivity|].
          intro c. apply filter_In in c.
          destruct c as [_ c].
          eqdestruct (equiv_decb eqv x a). inversion c.
  Qed.

  Theorem stable_count_occ : forall l l',
      Stable eqv l l' ->
      (forall x, count_occ (equiv_dec eq) l x = count_occ (equiv_dec eq) l' x).
  Proof.
    induction l as [|h t IH]; intros l' HS x.
    - apply Stable_nil in HS. subst; reflexivity.
    - cbn. destruct (equiv_dec eq h x).
      + rewrite e in *; clear e.
        rewrite <- filter_true_count_occ with (f := equiv_decb eqv x) (l := l')
          by apply equiv_decb_refl.
        specialize (HS x). rewrite <- HS.
        cbn. rewrite equiv_decb_refl.
        cbn. rewrite if_true by reflexivity.
        rewrite filter_true_count_occ by apply equiv_decb_refl.
        reflexivity.
      + rewrite (count_occ_rem1_neq l' x h) by auto.
        apply IH with (l' := rem1 h l').
        apply Stable_rem1. apply HS.
  Qed.

  Corollary Stable_perm : forall l l', Stable eqv l l' -> Permutation l l'.
  Proof.
    intros. apply count_occ_Permutation.
    apply stable_count_occ. auto.
  Qed.
End Perm.

Section StableInd.
  Context {A : Type} `{EqDec A}.

  Inductive StableInd : list A -> list A -> Prop :=
  | stable_ind_nil : StableInd nil nil
  | stable_ind_skip : forall (x : A) (l l' : list A),
      StableInd l l' -> StableInd (x :: l) (x :: l')
  | stable_ind_swap : forall (x y : A) (l : list A),
      x =/= y -> StableInd (y :: x :: l) (x :: y :: l)
  | stable_ind_trans : forall l l' l'' : list A,
      StableInd l l' -> StableInd l' l'' -> StableInd l l''.

  Lemma stable_ind_refl : forall l, StableInd l l.
  Proof. induction l; constructor; auto. Qed.

  Lemma stable_ind_sym : forall l l',
      StableInd l l' -> StableInd l' l.
  Proof.
    intros l l' HS.
    induction HS; econstructor; eauto.
    symmetry. auto.
  Qed.
End StableInd.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) StableInd
    reflexivity proved by stable_ind_refl
    symmetry proved by stable_ind_sym
    transitivity proved by stable_ind_trans
      as stable_ind_rel.

Section StableIndStable.
  Context {A : Type} eqv `{Equiv : EqDec A eqv}.

  Implicit Types l : list A.

  Theorem stable_perm_stable : forall l l', StableInd l l' -> Stable l l'.
    intros l l' SP.
    induction SP.
    - unfold Stable. intros. reflexivity.
    - apply Stable_skip. auto.
    - apply Stable_swap. symmetry. auto.
    - eapply Stable_trans; eauto.
  Qed.

  Lemma stable_destr : forall h h' l l',
      Stable (h :: l) (h' :: l') ->
      h =/= h' ->
      exists l1 l2, l = l1 ++ h' :: l2 /\ (Forall (fun b => negb (h' ==b b) = true) l1).
  Proof.
    assert (NB : forall y x : A, (fun a : A => (y <>b a) = true) x -> (y ==b x) = false). {
      intros x y HT.
      rewrite <- Bool.negb_involutive at 1.
      unfold nequiv_decb in HT.
      rewrite HT. auto.
    }
    intros h h' l l' HS HNeq.
    specialize (HS h'). cbn in HS.
    eqdestruct (h' ==b h).
    rewrite equiv_decb_refl in HS.
    remember (take_while (nequiv_decb h') l) as l1.
    remember (drop_while (nequiv_decb h') l) as l2.
    assert (HL : l = l1 ++ l2) by (subst; apply take_drop_while_id).
    rewrite HL, filter_app in HS.
    rewrite filter_empty, app_nil_l in HS.
    destruct l2 as [|a l2]; [inversion HS|].
    exists l1, l2.
    split; [|subst l1; apply take_while_all].
    rewrite HL; do 2 f_equal.
    cbn in HS.
    rewrite <- (Bool.negb_involutive (h' ==b a)) in HS.
    replace (negb (h' ==b a)) with (h' <>b a) in HS by reflexivity.
    erewrite (drop_while_hd (nequiv_decb h')) in HS by (symmetry; eauto).
    cbn in HS; inversion HS; auto.
    apply Forall_forall. subst l1.
    eapply Forall_impl; [apply NB|apply take_while_all].
  Qed.

  Context `(Eq : EqDec A eq).

  Arguments equiv_dec [_] _ [_] [_].
  Arguments equiv_decb [_] _ [_] [_].
  Arguments Stable [_] _ [_] [_].
  Arguments StableInd [_] _ [_].

  Remark cons_app_length : forall t h l1 l2 n,
      t = l1 ++ h :: l2 ->
      n = length t ->
      n = length (h :: l1 ++ l2).
  Proof.
    intros t h l1 l2 n HT HL.
    rewrite HT in HL.
    cbn. rewrite app_length in *. cbn in HL.
    omega.
  Qed.

  Remark cons_app_length' : forall t h l1 l2 n,
      t = l1 ++ h :: l2 ->
      S n = length t ->
      n = length (l1 ++ l2).
  Proof.
    intros t h l1 l2 n HT HL.
    rewrite HT in HL.
    rewrite app_length in *. cbn in HL.
    omega.
  Qed.

  Remark Hy : forall h l x y,
      Forall (fun b : A => negb (equiv_decb eqv h b) = true) l ->
      eqv y h ->
      In x l -> (equiv_decb eqv y x) = false.
  Proof.
    intros h l x y HL HEq.
    revert x. apply Forall_forall; eapply Forall_impl; [|apply HL].
    cbn. intros a. rewrite Bool.negb_true_iff.
    intro HA.
    eqdestruct (equiv_decb eqv h a); [discriminate|].
    eqdestruct (equiv_decb eqv y a).
    exfalso. apply H. transitivity y. symmetry. auto. auto.
    auto.
  Qed.

  Theorem perm_stable_stable_perm : forall l l',
      Stable eqv l l' -> StableInd eqv l l'.
  Proof.
    (* We use strong induction on length of lists *)
    intros l l' HS.
    remember (length l) as n.
    assert (Heqn' : n = length l'). {
      rewrite Heqn; apply Permutation_length.
      apply (@Stable_perm A equiv1 Eq eqv equiv0 Equiv).
      apply HS.
    }
    revert l l' Heqn Heqn' HS.

    induction n as [n IH] using (well_founded_induction lt_wf);
      intros l l' HL HL' HS.
    destruct n as [|n].
    - symmetry in HL;  apply length_zero_iff_nil in HL.
      symmetry in HL'; apply length_zero_iff_nil in HL'.
      subst; apply stable_ind_nil.
    - destruct l as [|h t];    [cbn in HL; discriminate|].
      destruct l' as [|h' t']; [cbn in HL'; discriminate|].
      cbn in HL, HL'.
      injection HL; clear HL;  intro HL.
      injection HL'; clear HL'; intro HL'.
      destruct (equiv_dec eqv h h').
      + assert (h = h'). {
          specialize (HS h). cbn in HS.
          rewrite equiv_decb_refl in HS.
          eqdestruct (equiv_decb eqv h h').
          inversion HS; auto.
        }
        subst h. constructor. apply (IH n); auto.
        eapply Stable_unskip. apply HS.
      + assert (HL1L2 : exists l1 l2,
                   t = l1 ++ h' :: l2 /\
                   (Forall (fun b => negb (equiv_decb eqv h' b) = true) l1))
          by (apply stable_destr with (h := h) (l' := t'); auto).
        destruct HL1L2 as [l1 [l2 [HT HL1]]].
        assert (Stable eqv (h' :: (l1 ++ l2)) t). {
          rewrite HT.
          apply Stable_cons_app.
          apply Stable_refl.
          apply Forall_forall.
          eapply Forall_impl; [|apply HL1].
          intro a. unfold equiv_decb. destruct (equiv_dec eqv h' a); intuition.
        }
        transitivity (h :: h' :: (l1 ++ l2)).
        apply stable_ind_skip.
        apply (IH n); [auto..|eapply cons_app_length; eauto|symmetry; auto].
        transitivity (h' :: h :: (l1 ++ l2)).
        apply stable_ind_swap; [symmetry; auto].
        apply stable_ind_skip.
        assert (HL1L2' : exists l1' l2',
                   t' = l1' ++ h :: l2' /\
                   (Forall (fun b => negb (equiv_decb eqv h b) = true) l1'))
          by (apply stable_destr with (h := h') (l' := t); symmetry; auto).
        destruct HL1L2' as [l1' [l2' [HT' HL1']]].
        transitivity (h :: (l1' ++ l2')).
        apply stable_ind_skip.

        destruct n as [|n'];
          [rewrite HT in HL; rewrite app_length in HL; cbn in HL; omega|].
        apply (IH n'); [omega|eapply cons_app_length'; eauto..|].
        intro y; specialize (HS y).
        rewrite !filter_app.
        rewrite HT, HT' in HS.
        cbn in HS; rewrite !filter_app in HS.
        eqdestruct (equiv_decb eqv y h); [|eqdestruct (equiv_decb eqv y h')].
        * eqdestruct (equiv_decb eqv y h').
          symmetry in H0; exfalso; apply c. transitivity y; auto.
          rewrite (filter_empty _ l1') in * by (intros; eapply Hy; eauto).
          cbn [app filter] in HS.
          eqdestruct (equiv_decb eqv y h); eqdestruct (equiv_decb eqv y h').
          injection HS; intro HS'.
          rewrite HS'. reflexivity.
        * rewrite (filter_empty _ l1) in *
            by (intros; eapply Hy with (h := h'); eauto).
          cbn [app filter] in HS.
          eqdestruct (equiv_decb eqv y h); eqdestruct (equiv_decb eqv y h').
          injection HS; intro HS'.
          cbn. rewrite HS'. reflexivity.
        * cbn in HS.
          eqdestruct (equiv_decb eqv y h); eqdestruct (equiv_decb eqv y h').
          auto.
        * rewrite HT'.
          apply (IH n); [|eapply cons_app_length|rewrite <- HT'|]; eauto.
          apply Stable_cons_app. apply Stable_refl.
          apply Forall_forall; eapply Forall_impl; [|apply HL1'].
          intros. cbn in H0.
          eqdestruct (equiv_decb eqv h a); cbn in H0. inversion H0.
          auto.
  Qed.

End StableIndStable.
