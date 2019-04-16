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

Section Permutation.
  Context {A : Type} `{E : EqDec A}.

  Implicit Type l : list A.

  Theorem stable_destr : forall h h' l l',
      Stable (h :: l) (h' :: l') ->
      h =/= h' ->
      exists l1 l2, l = l1 ++ h' :: l2 /\ (Forall (fun x => h' =/= x) l1).
  Proof.
    intros h h' l l' HS HNeq.
    specialize (HS h'). cbn in HS.
    eqdestruct (h' ==b h).
    rewrite equiv_decb_refl in HS.
    remember (take_while (nequiv_decb h') l) as l1.
    remember (drop_while (nequiv_decb h') l) as l2.
    assert (HL : l = l1 ++ l2) by (subst; apply take_drop_while_id).
    rewrite HL, filter_app in HS.
    rewrite filter_empty, app_nil_l in HS
      by (subst l1;
          apply Forall_forall; eapply Forall_impl; [|apply take_while_all];
          cbn; unfold nequiv_decb; setoid_rewrite Bool.negb_true_iff; auto).
    destruct l2 as [|a l2]; [inversion HS|].
    exists l1, l2.
    split.
    - rewrite HL; do 2 f_equal.
      cbn in HS.
      rewrite <- (Bool.negb_involutive (h' ==b a)) in HS.
      replace (negb (h' ==b a)) with (h' <>b a) in HS by reflexivity.
      erewrite (drop_while_hd (nequiv_decb h')) in HS by (symmetry; eauto).
      cbn in HS; inversion HS; auto.
    - subst l1.
      eapply Forall_impl; [|apply take_while_all].
      clear. cbn; intros.
      eqdestruct (h' <>b a); [auto|discriminate].
  Qed.

  Lemma Stable_equiv_hd : forall h h' l l',
      Stable (h :: l) (h' :: l') ->
      h === h' -> h = h'.
  Proof.
    intros h h' l l' HS HEqv.
    specialize (HS h); cbn in HS.
    rewrite equiv_decb_refl in HS.
    eqdestruct (h ==b h').
    inversion HS; auto.
  Qed.

  Lemma Stable_cons_app_to_front : forall l l1 l2 h,
      l = l1 ++ h :: l2 ->
      Forall (fun x => h =/= x) l1 ->
      Stable l (h :: l1 ++ l2).
  Proof.
    intros l l1 l2 h HL HL1.
    subst l; symmetry.
    apply Stable_cons_app; [reflexivity|].
    apply Forall_forall; eapply Forall_impl; [|apply HL1].
    cbn; auto.
  Qed.

  Lemma stable_remove_hds : forall l l' h h' l1 l2 l1' l2',
      h =/= h' ->
      Stable (h :: l) (h' :: l') ->
      l = l1 ++ h' :: l2 ->
      l' = l1' ++ h :: l2' ->
      Forall (fun x => h' =/= x) l1 ->
      Forall (fun x => h =/= x) l1' ->
      Stable (l1 ++ l2) (l1' ++ l2').
  Proof.
    assert (HF : forall l h y,
               y === h ->
               Forall (fun x => h =/= x) l ->
               forall x, In x l -> (y ==b x) = false). {
      intros l h y HEqv HL.
      apply Forall_forall; eapply Forall_impl; [|apply HL].
      cbn; intros x HNeq.
      eqdestruct (y ==b x); [|reflexivity].
      exfalso; apply HNeq.
      symmetry in HEqv.
      transitivity y; auto.
    }

    intros l l' h h' l1 l2 l1' l2' HNeqv HS HL HL' HL1 HL1'.
    intro x; specialize (HS x).
    rewrite HL, HL' in HS.
    cbn in HS; rewrite !filter_app in *.
    eqdestruct (x ==b h); eqdestruct (x ==b h').
    - exfalso. symmetry in H. apply HNeqv.
      transitivity x; auto.
    - rewrite (filter_empty _ l1') in * by (eapply HF; eauto).
      cbn in HS.
      eqdestruct (x ==b h); eqdestruct (x ==b h').
      injection HS; intro HS'.
      rewrite HS'. reflexivity.
    - rewrite (filter_empty _ l1) in * by (eapply HF; eauto).
      cbn in HS.
      eqdestruct (x ==b h); eqdestruct (x ==b h').
      injection HS; intro HS'.
      rewrite HS'. reflexivity.
    - cbn in HS.
      eqdestruct (x ==b h); eqdestruct (x ==b h').
      apply HS.
  Qed.

  Ltac cons_app_lengths :=
    subst; cbn in *; try rewrite !app_length in *; cbn in *; omega.

  Lemma Stable_length : forall l l',
      Stable l l' -> length l = length l'.
  Proof.
    intros l l'. remember (length l) as n eqn:HL; rewrite HL.
    revert l l' HL.
    induction n as [|n IH]; intros l l' HL HS.
    - symmetry in HL; apply length_zero_iff_nil in HL; subst.
      apply Stable_nil in HS. subst. reflexivity.
    - cbn.
      destruct l as [|h t]; [inversion HL|].
      destruct l' as [|h' t'].
      symmetry in HS. apply Stable_nil in HS. inversion HS.
      cbn; f_equal.
      destruct (h == h') as [HEqv|HNeqv].
      + assert (h = h') by (eapply Stable_equiv_hd; eauto).
        subst.
        rewrite (IH t t');
          [reflexivity|cons_app_lengths|].
        eapply Stable_unskip; eauto.
      + destruct (stable_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
        destruct (stable_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
          [symmetry in HS|symmetry in HNeqv|]; auto.
        transitivity (length (h' :: l1 ++ l2)).
        apply IH; [cbn in HL; omega|apply Stable_cons_app_to_front; easy].
        rewrite HT'.
        transitivity (length (h :: l1' ++ l2')); [|cons_app_lengths].
        transitivity (length (h' :: l1' ++ l2')); [|reflexivity].
        apply IH;
          [cons_app_lengths|apply Stable_skip; eapply stable_remove_hds; eauto].
  Qed.

  Lemma Stable_perm_ind : forall n l l',
      n = length l ->
      n = length l' ->
      Stable l l' -> Permutation l l'.
  Proof.
    induction n as [[|n] IH] using (well_founded_induction lt_wf).
    - intros l l' HL HL' HS.
      repeat match goal with
      | H : 0 = length ?l |- _ => symmetry in H; apply length_zero_iff_nil in H
      end.
      subst; apply perm_nil.
    - intros [|h t] [|h' t'] HL HL' HS; cbn in HL, HL'; [discriminate..|].
      destruct (h == h') as [HEqv|HNeqv].
      + assert (h = h') by (eapply Stable_equiv_hd; easy).
        subst; apply perm_skip.
        apply (IH n); [omega..|eapply Stable_unskip; easy].
      + destruct (stable_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
        destruct (stable_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
          [symmetry in HS|symmetry in HNeqv|]; auto.
        rewrite HT, HT'.
        transitivity (h :: h' :: l1 ++ l2);
          [apply perm_skip; symmetry; apply Permutation_middle|].
        etransitivity; [apply perm_swap|apply perm_skip].
        transitivity (h :: l1' ++ l2');
          [apply perm_skip|apply Permutation_middle].
      destruct n as [|n'];
        [rewrite HT in HL; rewrite app_length in HL; cbn in HL; omega|].
        apply (IH n'); [omega|cons_app_lengths..|eapply stable_remove_hds; eauto].
  Qed.

  Corollary Stable_perm : forall l l', Stable l l' -> Permutation l l'.
  Proof.
    intros.
    apply Stable_perm_ind with (n := length l);
      [|apply Stable_length|]; easy.
  Qed.
End Permutation.

Section CountOcc.
  Context {A} `{EqDec A}.

  Variable eq_dec : forall x y : A, { x = y } + { x <> y }.

  Implicit Type l : list A.

  Theorem Stable_rem1 : forall l1 l2 a,
      Stable (a :: l1) l2 -> Stable l1 (rem1 eq_dec a l2).
  Proof.
    induction l1 as [|h1 t1 IH]; intros l2 a HS.
    - cbn in HS. apply Stable_1 in HS. subst.
      cbn. rewrite if_true by reflexivity. reflexivity.
    - intro x.
      cbn. eqdestruct (x ==b h1).
      + rewrite filter_rem1.
        specialize (HS x). cbn in HS.
        eqdestruct (x ==b h1).
        eqdestruct (x ==b a).
        * rewrite <- HS.
          cbn. rewrite if_true by reflexivity.
          reflexivity.
        * rewrite <- HS.
          cbn. rewrite if_false.
          f_equal. rewrite rem1_not_in; [reflexivity|].
          intro c. apply filter_In in c.
          destruct c as [_ c].
          eqdestruct (x ==b a). inversion c.
          intro c. rewrite c in H2. contradiction.
      + specialize (HS x).
        cbn in HS. eqdestruct (x ==b h1).
        eqdestruct (x ==b a).
        * rewrite filter_rem1. rewrite <- HS.
          cbn. rewrite if_true by reflexivity.
          reflexivity.
        * rewrite filter_rem1. rewrite <- HS.
          rewrite rem1_not_in; [reflexivity|].
          intro c. apply filter_In in c.
          destruct c as [_ c].
          eqdestruct (x ==b a). inversion c.
  Qed.

  Theorem stable_count_occ : forall l l',
      Stable l l' ->
      (forall x, count_occ eq_dec l x = count_occ eq_dec l' x).
  Proof.
    induction l as [|h t IH]; intros l' HS x.
    - apply Stable_nil in HS. subst; reflexivity.
    - cbn. destruct (eq_dec h x).
      + rewrite e in *; clear e.
        rewrite <- filter_true_count_occ with (f := equiv_decb x) (l := l')
          by apply equiv_decb_refl.
        specialize (HS x). rewrite <- HS.
        cbn. rewrite equiv_decb_refl.
        cbn. rewrite if_true by reflexivity.
        rewrite filter_true_count_occ by apply equiv_decb_refl.
        reflexivity.
      + rewrite count_occ_rem1_neq with (x0 := h) (l := l') by auto.
        apply IH with (l' := rem1 eq_dec h l').
        apply Stable_rem1. apply HS.
  Qed.
End CountOcc.

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
  Context {A : Type} `{EqDec A}.

  Implicit Types l : list A.

  Theorem stable_perm_stable : forall l l', StableInd l l' -> Stable l l'.
    intros l l' SP.
    induction SP.
    - unfold Stable. intros. reflexivity.
    - apply Stable_skip. auto.
    - apply Stable_swap. symmetry. auto.
    - eapply Stable_trans; eauto.
  Qed.

  Remark stable_length_zero : forall l l',
      0 = length l ->
      0 = length l' ->
      StableInd l l'.
  Proof.
    intros l l' HL HL'.
    symmetry in HL;  apply length_zero_iff_nil in HL.
    symmetry in HL'; apply length_zero_iff_nil in HL'.
    subst; apply stable_ind_nil.
  Qed.

  Ltac cons_app_lengths :=
    subst; cbn in *; try rewrite !app_length in *; cbn in *; omega.

  Lemma stable_ind_iff_ind : forall n l l',
      n = length l -> n = length l' ->
      Stable l l' -> StableInd l l'.
  Proof.
    induction n as [[|n] IH] using (well_founded_induction lt_wf);
      [intros; apply stable_length_zero; auto|].
    intros [|h t] [|h' t'] HL HL' HS; cbn in HL, HL';
      [discriminate..|].
    injection HL; injection HL'; clear HL HL'; intros HL' HL.
    destruct (h == h') as [HEqv | HNeqv].
    - assert (h = h') by (eapply Stable_equiv_hd; eauto).
      subst h. constructor. apply (IH n); auto.
      eapply Stable_unskip. apply HS.
    - destruct (stable_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
      destruct (stable_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
        [symmetry in HS|symmetry in HNeqv|]; auto.
      transitivity (h :: h' :: (l1 ++ l2)); [apply stable_ind_skip|].
      apply (IH n); [..|cons_app_lengths|apply Stable_cons_app_to_front]; eauto.
      transitivity (h' :: h :: (l1 ++ l2)).
      apply stable_ind_swap; [symmetry; auto].
      apply stable_ind_skip.
      transitivity (h :: (l1' ++ l2')).
      apply stable_ind_skip.
      destruct n as [|n']; [cons_app_lengths|].
      apply (IH n'); [cons_app_lengths..|eapply stable_remove_hds]; eauto.
      symmetry.
      apply (IH n); [..|cons_app_lengths|apply Stable_cons_app_to_front]; eauto.
  Qed.

  Corollary stable_ind_iff : forall l l',
      Stable l l' <-> StableInd l l'.
  Proof.
    split.
    - intro HS.
      apply stable_ind_iff_ind with (n := length l); [reflexivity| |auto].
      apply Stable_length; easy.
    - apply stable_perm_stable.
  Qed.
End StableIndStable.

Section Unique.
  Context {A} `{Preord A}.

  Theorem stable_sort_unique : forall l l',
      Sorted l -> Sorted l' -> Stable l l' ->
      l = l'.
  Proof.
    induction l as [|hd tl]; intros l' SL SL' St.
    - apply Stable_nil in St. subst; auto.
    - destruct l' as [|hd' tl'];
      [exfalso; eapply Permutation_nil_cons; symmetry;
        apply (@Stable_perm _ _ _ Ord_EqDec); easy|].
      apply Sorted_cons_inv in SL; destruct SL as [HIn SL].
      apply Sorted_cons_inv in SL'; destruct SL' as [HIn' SL'].
      assert (hd === hd'). {
        apply (@Stable_perm _ _ _ Ord_EqDec) in St; rename St into P.
        pose proof (Permutation_sym P) as P'.
        destruct (Permutation_cons_in hd hd' tl tl' P);  [subst; reflexivity|].
        destruct (Permutation_cons_in hd' hd tl' tl P'); [subst; reflexivity|].
        split; auto.
      }
      pose proof (St hd) as F. cbn in F.
      rewrite equiv_decb_refl in F.
      eqdestruct (hd ==b hd').
      inversion F; subst; clear F.
      f_equal.
      apply IHtl; [..|eapply Stable_unskip]; easy.
  Qed.
End Unique.

Section Leibniz.
  Context {A : Type} `{EqDec A}.

  Hypothesis eqv_eq : forall x y, x === y -> x = y.

  Theorem all_perm_stable : forall l l',
      Permutation l l' -> Stable l l'.
  Proof.
    intros l l' HP; induction HP.
    - reflexivity.
    - apply Stable_skip. easy.
    - destruct (equiv_dec x y).
      + apply eqv_eq in e. subst.
        do 2 apply Stable_skip. reflexivity.
      + apply Stable_swap; easy.
    - transitivity l'; easy.
  Qed.
End Leibniz.
