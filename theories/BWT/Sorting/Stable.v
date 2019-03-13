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
      unfold equiv_decb in S.
      destruct (equiv_dec a a); [|pose proof (equiv_reflexive _ a); contradiction].
      simpl in S; inversion S.
  Qed.

  Theorem stable_perm_nodup : forall l l',
      NoDup l -> NoDup l' -> Stable l l' -> Permutation l l'.
  Proof.
    intros l l' ND ND' HS.
    apply NoDup_Permutation; auto.
    intros x.
    assert (forall s, In x s <-> In x (filter (equiv_decb x) s)).
    intros; split; intros. apply filter_In; split; auto.
    unfold equiv_decb; destruct (x == x); [|exfalso; apply c; reflexivity]; auto.
    apply (proj1 (filter_In (equiv_decb x) x s)); auto.
    rewrite (H l), (H l').
    apply in_eq_iff.
    apply HS.
  Qed.
End Stable.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) Stable
    reflexivity proved by Stable_refl
    symmetry proved by Stable_sym
    transitivity proved by Stable_trans
      as Stable_rel.

Theorem filter_count_occ_in {A} `{E : EqDec A eq} : forall (f : A -> bool) a (l : list A),
    (f a = true) ->
    count_occ E (filter f l) a = count_occ E l a.
Proof.
  induction l as [|h t IH]; intros HF; [reflexivity|].
  cbn. destruct (E h a).
  - rewrite e, HF; cbn. rewrite e.
    destruct (E a a); [|exfalso; apply c; reflexivity].
    f_equal. apply IH. auto.
  - destruct (f h); cbn.
    destruct (E h a); [contradiction|].
    apply IH; auto.
    apply IH; auto.
Qed.

Theorem filter_count_occ_not_in {A} `{E : EqDec A eq} : forall (f : A -> bool) a (l : list A),
    (f a = false) ->
    count_occ E (filter f l) a = 0.
Proof.
  induction l as [|h t IH]; intros HF; [reflexivity|].
  cbn. destruct (f h) eqn:HFh; cbn.
  destruct (E h a).
  - exfalso. rewrite e, HF in HFh. discriminate.
  - rewrite IH; auto.
  - rewrite IH; auto.
Qed.

Theorem filter_zipOcc {A} `{EqDec A eq} : forall f (l : list A),
    zipOcc (filter f l) = filter (fun x => f (fst x)) (zipOcc l).
Proof.
  induction l.
  - reflexivity.
  - cbn. destruct (f a) eqn:Hfa.
    + cbn. rewrite (filter_count_occ_in f a) by eauto.
      f_equal. apply IHl.
    + apply IHl.
Qed.

Theorem stable_count_occ {A} `{E : EqDec A eq}: forall l l' : list A,
    Stable l l' -> (forall x, count_occ E l x = count_occ E l' x).
Proof.
  induction l as [|h t IH]; intros l' HS x.
  - apply Stable_nil in HS. subst; reflexivity.
  - cbn. destruct (E h x).
    + rewrite e in *; clear e.
      rewrite <- filter_count_occ_in with (f := equiv_decb x) (l := l').
      specialize (HS x). rewrite <- HS.
      cbn. unfold equiv_decb at 1. destruct (x == x); [|exfalso; apply c; reflexivity].
      destruct (E x x); [|exfalso; apply c; reflexivity].
      cbn.
      destruct (E x x); [|exfalso; apply c; reflexivity].
      f_equal. rewrite filter_count_occ_in. reflexivity.
      unfold equiv_decb; destruct (x == x); [|exfalso; apply c; reflexivity]; auto.
      unfold equiv_decb; destruct (x == x); [|exfalso; apply c; reflexivity]; auto.
    + specialize (HS x). cbn in HS.
      unfold equiv_decb at 1 in HS.
      destruct (x == h); [symmetry in c; contradiction|].
      rewrite <- filter_count_occ_in with (f := equiv_decb x) (l := l').
      rewrite <- HS.
      rewrite filter_count_occ_in. reflexivity.
      unfold equiv_decb; destruct (x == x); [|exfalso; apply c1; reflexivity]; auto.
      unfold equiv_decb; destruct (x == x); [|exfalso; apply c1; reflexivity]; auto.
Qed.

Theorem Stable_perm {A} {E : EqDec A eq} : forall l l' : list A,
    Stable l l' -> Permutation l l'.
Proof.
  intros. apply count_occ_Permutation.
  apply stable_count_occ. auto.
Qed.

Section StableInd.
  Context {A : Type} `{EqDec A}.

  Inductive StablePerm : list A -> list A -> Prop :=
  | stable_perm_nil : StablePerm nil nil
  | stable_perm_skip : forall (x : A) (l l' : list A), StablePerm l l' -> StablePerm (x :: l) (x :: l')
  | stable_perm_swap : forall (x y : A) (l : list A), x =/= y -> StablePerm (y :: x :: l) (x :: y :: l)
  | stable_perm_trans : forall l l' l'' : list A, StablePerm l l' -> StablePerm l' l'' -> StablePerm l l''.

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

Section StablePermStable.
  Context {A : Type} `{EqDec A}.

  Implicit Types l : list A.

  Theorem stable_perm_stable : forall l l', StablePerm l l' -> Stable l l'.
    intros l l' SP.
    induction SP.
    - unfold Stable. intros. reflexivity.
    - apply Stable_skip. auto.
    - apply Stable_swap. symmetry. auto.
    - eapply Stable_trans; eauto.
  Qed.

  Theorem stable_perm_perm : forall l l', StablePerm l l' -> Permutation l l'.
    intros l l' SP. induction SP; econstructor; eauto.
  Qed.

  Lemma stable_destr : forall h h' l l',
      Stable (h :: l) (h' :: l') ->
      h =/= h' ->
      exists l1 l2, l = l1 ++ h' :: l2 /\ (Forall (fun b => negb (h' ==b b) = true) l1).
  Proof.
    intros h h' l l' HS HNeq.
    specialize (HS h'). cbn in HS.
    unfold equiv_decb at 1 in HS; destruct (h' == h); [exfalso; apply HNeq; symmetry; auto|].
    unfold equiv_decb at 2 in HS; destruct (h' == h'); [|exfalso; apply c0; reflexivity].
    remember (take_while (nequiv_decb h') l) as l1.
    remember (drop_while (nequiv_decb h') l) as l2.
    assert (HL : l = l1 ++ l2) by (subst; apply take_drop_while_id).
    rewrite HL, filter_app in HS.
    rewrite filter_empty, app_nil_l in HS.
    destruct l2 as [|a l2]; [inversion HS|].
    exists l1, l2.
    split; [|subst l1; apply take_while_all].
    rewrite HL; do 2 f_equal.
    cbn in HS. rewrite <- (Bool.negb_involutive (h' ==b a)) in HS.
    replace (negb (h' ==b a)) with (h' <>b a) in HS by reflexivity.
    erewrite (drop_while_hd (nequiv_decb h')) in HS by (symmetry; eauto).
    inversion HS; auto.
    apply Forall_forall. subst l1.
    eapply Forall_impl; [|apply take_while_all].
    intros. cbn in H0.
    rewrite <- Bool.negb_involutive at 1; unfold nequiv_decb in H0. rewrite H0. auto.
  Qed.

  Theorem perm_stable_stable_perm : forall l l',
      Permutation l l' -> Stable l l' -> StablePerm l l'.
  Proof.
    intros l l' HP.
    remember (length l) as n.
    assert (Heqn' : n = length l') by (rewrite Heqn; apply Permutation_length; apply HP).
    revert l l' Heqn Heqn' HP.
    induction n as [n IH] using (well_founded_induction lt_wf); intros l l' HL HL' HP HS.
    destruct n as [|n].
    - symmetry in HL; apply length_zero_iff_nil in HL.
      symmetry in HL'; apply length_zero_iff_nil in HL'.
      subst.
      apply stable_perm_nil.
    - destruct l as [|h t];    [cbn in HL; discriminate|].
      destruct l' as [|h' t']; [cbn in HL'; discriminate|].
      cbn in HL, HL'.
      injection HL; clear HL; intro HL.
      injection HL'; clear HL'; intro HL'.
      destruct (h == h').
      + assert (h = h'). {
          specialize (HS h). simpl in HS.
          unfold equiv_decb in HS.
          destruct (h == h); [|exfalso; apply c; apply equiv_reflexive].
          destruct (h == h'); [clear e|exfalso; apply c; auto].
          inversion HS. auto.
        }
        subst h. constructor. apply (IH n); auto.
        eapply Permutation_cons_inv; eauto.
        intro y. specialize (HS y).
        inversion HS. destruct (y ==b h'); auto.
        inversion H1; auto.
      + assert (exists l1 l2, t = l1 ++ h' :: l2 /\ (Forall (fun b => negb (h' ==b b) = true) l1))
          by (apply stable_destr with (h := h) (l' := t'); auto).
        destruct H0 as [l1 [l2 [HT HL1]]].
        assert (Stable (h' :: (l1 ++ l2)) t). {
          rewrite HT.
          apply Stable_cons_app.
          apply Stable_refl.
          apply Forall_forall.
          eapply Forall_impl; [|apply HL1].
          intro a. unfold equiv_decb. destruct (equiv_dec h' a); intuition.
        }
        apply stable_perm_trans with (l' := h :: h' :: (l1 ++ l2)).
        apply stable_perm_skip.
        apply (IH n); auto.
        symmetry; auto.
        rewrite HT in HL. rewrite app_length in HL. cbn in HL.
        cbn. rewrite app_length. omega.
        rewrite HT. symmetry.
        apply Permutation_cons_app. apply Permutation_refl.
        apply Stable_sym. auto.
        eapply stable_perm_trans with (l' := h' :: h :: (l1 ++ l2)).
        apply stable_perm_swap.
        symmetry. auto.
        apply stable_perm_skip.
        assert (exists l1' l2', t' = l1' ++ h :: l2' /\ (Forall (fun b => negb (h ==b b) = true) l1'))
          by (apply stable_destr with (h := h') (l' := t); symmetry; auto).
        destruct H1 as [l1' [l2' [HT' HL1']]].
        apply stable_perm_trans with (l' := h :: (l1' ++ l2')).
        apply stable_perm_skip.
        destruct n as [|n']; [rewrite HT in HL; rewrite app_length in HL; cbn in HL; omega|].
        apply (IH n'); [omega|admit|admit|..].
        apply Permutation_cons_inv with (a := h).
        apply Permutation_cons_inv with (a := h').
        apply Permutation_trans with (l' := (h :: h' :: l1 ++ l2)); [apply perm_swap|].
        apply Permutation_trans with (l' := (h :: t)); [rewrite HT; apply perm_skip; apply Permutation_cons_app; reflexivity|].
        symmetry.
        apply Permutation_trans with (l' := (h' :: t')); [rewrite HT'; apply perm_skip; apply Permutation_cons_app; reflexivity|].
        symmetry. apply HP.
        intro y; specialize (HS y).
        rewrite !filter_app.
        rewrite HT, HT' in HS.
        cbn in HS; rewrite !filter_app in HS.
        destruct (y ==b h); [|destruct (y ==b h')].
        * destruct (y ==b h'); [admit|].
          replace (equiv_decb y) with (equiv_decb h) in * by admit.
          rewrite (filter_empty _ l1') in *.
          cbn [app filter] in HS.
          destruct (h ==b h); [|admit].
          injection HS; intro HS'.
          rewrite <- HS'.
          cbn.
          destruct (h ==b h'); [admit|].
          reflexivity.
          apply Forall_forall; eapply Forall_impl; [|apply HL1'].
          cbn; intros. destruct (h ==b a); auto.
          apply Forall_forall; eapply Forall_impl; [|apply HL1'].
          cbn; intros. destruct (h ==b a); auto.
        * replace (equiv_decb y) with (equiv_decb h') in * by admit.
          rewrite (filter_empty _ l1) in *.
          cbn [app filter] in HS.
          destruct (h' ==b h'); [|admit].
          injection HS; intro HS'.
          cbn.
          rewrite HS'.
          destruct (h' ==b h); [admit|].
          reflexivity.
          apply Forall_forall; eapply Forall_impl; [|apply HL1].
          cbn; intros. destruct (h' ==b a); auto.
          apply Forall_forall; eapply Forall_impl; [|apply HL1].
          cbn; intros. destruct (h' ==b a); auto.
        * cbn in HS.
          destruct (y ==b h'); [admit|].
          destruct (y ==b h); [admit|].
          auto.
        * rewrite HT'.
          apply (IH n); auto.
          admit. admit.
          apply Permutation_cons_app. reflexivity.
          apply Stable_cons_app. apply Stable_refl.
          apply Forall_forall; eapply Forall_impl; [|apply HL1'].
          cbn; intros. admit.
  Admitted.

End StablePermStable.
