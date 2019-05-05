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

Section StablePerm.
  Context {A : Type} `{E : EqDec A}.

  Definition StablePerm (l l': list A) : Prop :=
    forall x, filter (equiv_decb x) l = filter (equiv_decb x) l'.

  Lemma StablePerm_refl:
    forall l, StablePerm l l.
  Proof. intros; red; reflexivity. Qed.

  Lemma StablePerm_trans:
    forall l1 l2 l3, StablePerm l1 l2 -> StablePerm l2 l3 -> StablePerm l1 l3.
  Proof.
    intros; red; intros. transitivity (filter (equiv_decb x) l2); auto.
  Qed.

  Lemma StablePerm_sym : forall l l',
      StablePerm l l' -> StablePerm l' l.
  Proof.
    intros l l' H x.
    specialize (H x).
    erewrite eq_sym; eauto.
  Qed.

  Lemma StablePerm_app:
    forall l l' m m', StablePerm l l' -> StablePerm m m' -> StablePerm (l ++ m) (l' ++ m').
  Proof.
    intros; red; intros. repeat rewrite filter_app. f_equal; auto.
  Qed.

  Lemma StablePerm_skip:
    forall a l l', StablePerm l l' -> StablePerm (a::l) (a::l').
  Proof.
    intros; red; intros. simpl.
    destruct (equiv_decb x a); simpl. f_equal; auto. auto.
  Qed.

  Lemma StablePerm_swap:
    forall a b l, a =/= b -> StablePerm (a::b::l) (b::a::l).
  Proof.
    intros; red; intros. simpl.
    unfold equiv_decb.
    case_eq (equiv_dec x a); intro; simpl; auto.
    case_eq (equiv_dec x b); intro; simpl; auto.
    elim H. unfold equiv_decb in *.
    eapply equiv_transitive. apply equiv_symmetric; eauto. eauto.
  Qed.

  Lemma StablePerm_cons_app:
    forall a l l1 l2,
      StablePerm l (l1 ++ l2) ->
      (forall b, In b l1 -> a =/= b) ->
      StablePerm (a :: l) (l1 ++ a :: l2).
  Proof.
    intros a l l1 l2 HS HI; red; intros.
    rewrite filter_app.
    destruct (x == a);
      [|cbn; rewrite <- !if_equiv_dec_b, !if_false, <- filter_app by easy; apply HS].
    assert (forall b, In b l1 -> (x ==b b) = false). {
      intros. destruct (equiv_dec_spec _ x b); [|easy].
      specialize (HI b H). exfalso; apply HI.
      transitivity x; symmetry in e; easy.
    }
    specialize (HS x); rewrite filter_app in HS.
    rewrite (filter_empty _ l1) in * by easy.
    cbn; rewrite <- !if_equiv_dec_b, !if_true by easy.
    f_equal.
    apply HS.
  Qed.

  Lemma StablePerm_nil : forall l,
      StablePerm nil l -> l = nil.
  Proof.
    induction l.
    - easy.
    - intro S.
      unfold StablePerm in S; cbn in S.
      specialize (S a).
      rewrite equiv_decb_refl in S.
      inversion S.
  Qed.

  Lemma StablePerm_unskip:
    forall a l l', StablePerm (a::l) (a::l') -> StablePerm l l'.
  Proof.
    intros a l l' HS x.
    specialize (HS x). cbn in HS.
    eqdestruct (x ==b a); [inversion HS|]; auto.
  Qed.

  Lemma StablePerm_1 : forall l x,
      StablePerm (x::nil) l -> l = x::nil.
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
        subst. apply StablePerm_unskip in HS.
        apply StablePerm_nil in HS.
        subst. reflexivity.
      + specialize (HS a). cbn in HS.
        eqdestruct (a ==b x).
        rewrite equiv_decb_refl in HS.
        inversion HS.
  Qed.
End StablePerm.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) StablePerm
    reflexivity proved by StablePerm_refl
    symmetry proved by StablePerm_sym
    transitivity proved by StablePerm_trans
      as StablePerm_rel.

Section Permutation.
  Context {A : Type} `{E : EqDec A}.

  Implicit Type l : list A.

  Theorem StablePerm_destr : forall h h' l l',
      StablePerm (h :: l) (h' :: l') ->
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

  Theorem StablePerm_destr' : forall h l l',
      StablePerm (h :: l) l' ->
      exists l1 l2, l' = l1 ++ h :: l2 /\ (Forall (fun x => h =/= x) l1).
  Proof.
    intros h l l' HS.
    specialize (HS h). cbn in HS.
    rewrite <- if_equiv_dec_b, if_true in HS by reflexivity.
    remember (take_while (nequiv_decb h) l') as l1.
    remember (drop_while (nequiv_decb h) l') as l2.
    assert (HL : l' = l1 ++ l2) by (subst; apply take_drop_while_id).
    rewrite HL, filter_app in HS.
    rewrite @filter_empty with (l := l1), app_nil_l in HS
      by (subst l1; apply Forall_forall; eapply Forall_impl; [|apply take_while_all];
          cbn; setoid_rewrite Bool.negb_true_iff; easy).
    destruct l2 as [|a l2]; [inversion HS|].
    exists l1, l2.
    split.
    - rewrite HL; do 2 f_equal.
      cbn in HS.
      rewrite <- (Bool.negb_involutive (h ==b a)) in HS.
      replace (negb (h ==b a)) with (h <>b a) in HS by reflexivity.
      erewrite (drop_while_hd (nequiv_decb h)) in HS by (symmetry; eauto).
      cbn in HS; inversion HS; auto.
    - subst l1.
      eapply Forall_impl; [|apply take_while_all].
      clear. cbn; intros.
      eqdestruct (h <>b a); [auto|discriminate].
  Qed.

  Lemma StablePerm_equiv_hd : forall h h' l l',
      StablePerm (h :: l) (h' :: l') ->
      h === h' -> h = h'.
  Proof.
    intros h h' l l' HS HEqv.
    specialize (HS h); cbn in HS.
    rewrite equiv_decb_refl in HS.
    eqdestruct (h ==b h').
    inversion HS; auto.
  Qed.

  Lemma StablePerm_cons_app_to_front : forall l l1 l2 h,
      l = l1 ++ h :: l2 ->
      Forall (fun x => h =/= x) l1 ->
      StablePerm l (h :: l1 ++ l2).
  Proof.
    intros l l1 l2 h HL HL1.
    subst l; symmetry.
    apply StablePerm_cons_app; [reflexivity|].
    apply Forall_forall; eapply Forall_impl; [|apply HL1].
    cbn; auto.
  Qed.

  Lemma stable_remove_hds : forall l l' h h' l1 l2 l1' l2',
      h =/= h' ->
      StablePerm (h :: l) (h' :: l') ->
      l = l1 ++ h' :: l2 ->
      l' = l1' ++ h :: l2' ->
      Forall (fun x => h' =/= x) l1 ->
      Forall (fun x => h =/= x) l1' ->
      StablePerm (l1 ++ l2) (l1' ++ l2').
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

  Lemma StablePerm_length : forall l l',
      StablePerm l l' -> length l = length l'.
  Proof.
    intros l l'. remember (length l) as n eqn:HL; rewrite HL.
    revert l l' HL.
    induction n as [|n IH]; intros l l' HL HS.
    - symmetry in HL; apply length_zero_iff_nil in HL; subst.
      apply StablePerm_nil in HS. subst. reflexivity.
    - cbn.
      destruct l as [|h t]; [inversion HL|].
      destruct l' as [|h' t'].
      symmetry in HS. apply StablePerm_nil in HS. inversion HS.
      cbn; f_equal.
      destruct (h == h') as [HEqv|HNeqv].
      + assert (h = h') by (eapply StablePerm_equiv_hd; eauto).
        subst.
        rewrite (IH t t');
          [reflexivity|cons_app_lengths|].
        eapply StablePerm_unskip; eauto.
      + destruct (StablePerm_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
        destruct (StablePerm_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
          [symmetry in HS|symmetry in HNeqv|]; auto.
        transitivity (length (h' :: l1 ++ l2)).
        apply IH; [cbn in HL; omega|apply StablePerm_cons_app_to_front; easy].
        rewrite HT'.
        transitivity (length (h :: l1' ++ l2')); [|cons_app_lengths].
        transitivity (length (h' :: l1' ++ l2')); [|reflexivity].
        apply IH;
          [cons_app_lengths|apply StablePerm_skip; eapply stable_remove_hds; eauto].
  Qed.

  Lemma StablePerm_Perm_ind : forall n l l',
      n = length l ->
      n = length l' ->
      StablePerm l l' -> Permutation l l'.
  Proof.
    induction n as [[|n] IH] using (well_founded_induction lt_wf).
    - intros l l' HL HL' HS.
      repeat match goal with
      | H : 0 = length ?l |- _ => symmetry in H; apply length_zero_iff_nil in H
      end.
      subst; apply perm_nil.
    - intros [|h t] [|h' t'] HL HL' HS; cbn in HL, HL'; [discriminate..|].
      destruct (h == h') as [HEqv|HNeqv].
      + assert (h = h') by (eapply StablePerm_equiv_hd; easy).
        subst; apply perm_skip.
        apply (IH n); [omega..|eapply StablePerm_unskip; easy].
      + destruct (StablePerm_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
        destruct (StablePerm_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
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

  Corollary StablePerm_Perm : forall l l', StablePerm l l' -> Permutation l l'.
  Proof.
    intros.
    apply StablePerm_Perm_ind with (n := length l);
      [|apply StablePerm_length|]; easy.
  Qed.
End Permutation.

Theorem rem_nth_StablePerm {A} `{EqDec A} : forall (l : list A) i d,
    i < length l ->
    (forall k, k < i -> nth i l d =/= nth k l d) ->
    StablePerm l (nth i l d :: rem_nth i l).
Proof.
  intros l i d HI HK.
  destruct i as [|i'] eqn:Heqni;
    [destruct l; easy
    |rewrite <- Heqni in *; assert (0 < i) by omega; clear i' Heqni].
  rewrite rem_nth_split by omega.
  rewrite @firstn_skipn_split with (i := i) (l := l) (d := d) at 1 by omega.
  apply StablePerm_cons_app_to_front; [easy|].
  apply Forall_forall.
  intros x HIn.
  apply In_nth with (d := d) in HIn .
  destruct HIn as [j [HJ HX]].
  rewrite <- HX; clear x HX.
  rewrite firstn_length, Nat.min_l in HJ by omega.
  rewrite firstn_nth by easy.
  apply HK; easy.
Qed.

Section CountOcc.
  Context {A} `{EqDec A}.

  Variable eq_dec : forall x y : A, { x = y } + { x <> y }.

  Implicit Type l : list A.

  Theorem StablePerm_rem1 : forall l1 l2 a,
      StablePerm (a :: l1) l2 -> StablePerm l1 (rem1 eq_dec a l2).
  Proof.
    induction l1 as [|h1 t1 IH]; intros l2 a HS.
    - cbn in HS. apply StablePerm_1 in HS. subst.
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
      StablePerm l l' ->
      (forall x, count_occ eq_dec l x = count_occ eq_dec l' x).
  Proof.
    induction l as [|h t IH]; intros l' HS x.
    - apply StablePerm_nil in HS. subst; reflexivity.
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
        apply StablePerm_rem1. apply HS.
  Qed.
End CountOcc.

Section StablePermInd.
  Context {A : Type} `{EqDec A}.

  Inductive StablePermInd : list A -> list A -> Prop :=
  | StablePermInd_nil : StablePermInd nil nil
  | StablePermInd_skip : forall (x : A) (l l' : list A),
      StablePermInd l l' -> StablePermInd (x :: l) (x :: l')
  | StablePermInd_swap : forall (x y : A) (l : list A),
      x =/= y -> StablePermInd (y :: x :: l) (x :: y :: l)
  | StablePermInd_trans : forall l l' l'' : list A,
      StablePermInd l l' -> StablePermInd l' l'' -> StablePermInd l l''.

  Lemma StablePermInd_refl : forall l, StablePermInd l l.
  Proof. induction l; constructor; auto. Qed.

  Lemma StablePermInd_sym : forall l l',
      StablePermInd l l' -> StablePermInd l' l.
  Proof.
    intros l l' HS.
    induction HS; econstructor; eauto.
    symmetry. auto.
  Qed.
End StablePermInd.

Add Parametric Relation (A : Type) `(E : EqDec A) : (list A) StablePermInd
    reflexivity proved by StablePermInd_refl
    symmetry proved by StablePermInd_sym
    transitivity proved by StablePermInd_trans
      as StablePermInd_rel.

Section StablePermInd_Iff.
  Context {A : Type} `{EqDec A}.

  Implicit Types l : list A.

  Theorem StablePermInd_imp : forall l l', StablePermInd l l' -> StablePerm l l'.
    intros l l' SP.
    induction SP.
    - unfold StablePerm. intros. reflexivity.
    - apply StablePerm_skip. auto.
    - apply StablePerm_swap. symmetry. auto.
    - eapply StablePerm_trans; eauto.
  Qed.

  Remark StablePermInd_length_zero : forall l l',
      0 = length l ->
      0 = length l' ->
      StablePermInd l l'.
  Proof.
    intros l l' HL HL'.
    symmetry in HL;  apply length_zero_iff_nil in HL.
    symmetry in HL'; apply length_zero_iff_nil in HL'.
    subst; apply StablePermInd_nil.
  Qed.

  Ltac cons_app_lengths :=
    subst; cbn in *; try rewrite !app_length in *; cbn in *; omega.

  Lemma StablePermInd_impby_ind : forall n l l',
      n = length l -> n = length l' ->
      StablePerm l l' -> StablePermInd l l'.
  Proof.
    induction n as [[|n] IH] using (well_founded_induction lt_wf);
      [intros; apply StablePermInd_length_zero; auto|].
    intros [|h t] [|h' t'] HL HL' HS; cbn in HL, HL';
      [discriminate..|].
    injection HL; injection HL'; clear HL HL'; intros HL' HL.
    destruct (h == h') as [HEqv | HNeqv].
    - assert (h = h') by (eapply StablePerm_equiv_hd; eauto).
      subst h. constructor. apply (IH n); auto.
      eapply StablePerm_unskip. apply HS.
    - destruct (StablePerm_destr h h' t t') as [l1 [l2 [HT HL1]]]; auto.
      destruct (StablePerm_destr h' h t' t) as [l1' [l2' [HT' HL1']]];
        [symmetry in HS|symmetry in HNeqv|]; auto.
      transitivity (h :: h' :: (l1 ++ l2)); [apply StablePermInd_skip|].
      apply (IH n); [..|cons_app_lengths|apply StablePerm_cons_app_to_front]; eauto.
      transitivity (h' :: h :: (l1 ++ l2)).
      apply StablePermInd_swap; [symmetry; auto].
      apply StablePermInd_skip.
      transitivity (h :: (l1' ++ l2')).
      apply StablePermInd_skip.
      destruct n as [|n']; [cons_app_lengths|].
      apply (IH n'); [cons_app_lengths..|eapply stable_remove_hds]; eauto.
      symmetry.
      apply (IH n); [..|cons_app_lengths|apply StablePerm_cons_app_to_front]; eauto.
  Qed.

  Corollary StablePermInd_iff : forall l l',
      StablePerm l l' <-> StablePermInd l l'.
  Proof.
    split.
    - intro HS.
      apply StablePermInd_impby_ind with (n := length l); [reflexivity| |auto].
      apply StablePerm_length; easy.
    - apply StablePermInd_imp.
  Qed.
End StablePermInd_Iff.

Section Unique.
  Context {A} `{Preord A}.

  Theorem StablePerm_Sorted_eq : forall l l',
      Sorted l -> Sorted l' -> StablePerm l l' ->
      l = l'.
  Proof.
    induction l as [|h t IH]; intros l' SL SL' St;
    [apply StablePerm_nil in St; subst; auto|].
    destruct l' as [|h' t'];
      [exfalso; eapply Permutation_nil_cons; symmetry;
       apply (@StablePerm_Perm _ _ _ Preord_EqDec); easy|].
    apply Sorted_cons_inv in SL; destruct SL as [HIn SL].
    apply Sorted_cons_inv in SL'; destruct SL' as [HIn' SL'].
    assert (h === h'). {
      apply (@StablePerm_Perm _ _ _ Preord_EqDec) in St; rename St into P.
      pose proof (Permutation_sym P) as P'.
      destruct (Permutation_cons_in h h' t t' P);  [subst; reflexivity|].
      destruct (Permutation_cons_in h' h t' t P'); [subst; reflexivity|].
      rewrite Forall_forall in HIn, HIn'.
      split; auto.
    }
    pose proof (St h) as F. cbn in F.
    rewrite <- !if_equiv_dec_b, !if_true in F by easy.
    inversion F; subst; clear F.
    f_equal.
    apply IH; [..|eapply StablePerm_unskip]; easy.
  Qed.
End Unique.

Section Leibniz.
  Context {A : Type} `{EqDec A}.

  Hypothesis eqv_eq : forall x y, x === y -> x = y.

  Theorem all_perm_stable : forall l l',
      Permutation l l' -> StablePerm l l'.
  Proof.
    intros l l' HP; induction HP.
    - reflexivity.
    - apply StablePerm_skip. easy.
    - destruct (equiv_dec x y).
      + apply eqv_eq in e. subst.
        do 2 apply StablePerm_skip. reflexivity.
      + apply StablePerm_swap; easy.
    - transitivity l'; easy.
  Qed.
End Leibniz.

Section Weaken.
  Context {A : Type}.

  Variables (O1 O2: Preord A).

  Local Arguments le {_} _.
  Local Arguments eqv {_} _.
  Local Arguments equiv_decb {_} _ {_} {_}.
  Local Arguments StablePerm {_} {_} {_} _.
  Local Arguments Preord_EqDec {_} _.

  Variables l l' : list A.

  Hypothesis le_weaken : forall x y,
      In x l -> In y l -> le O2 x y -> le O1 x y.

  Theorem StablePerm_weaken :
      StablePerm (Preord_EqDec O1) l l' -> StablePerm (Preord_EqDec O2) l l'.
  Proof.
    setoid_rewrite StablePermInd_iff.
    intros HS.
    induction HS; [easy|..].
    - constructor. apply IHHS.
      intros a b Ha Hb. apply le_weaken; right; easy.
    - constructor.
      unfold complement, Equivalence.equiv in *.
      intro c; apply H; clear H.
      destruct c.
      split; apply le_weaken; intuition.
    - transitivity l'; [apply IHHS1; easy|apply IHHS2].
      apply StablePermInd_iff in HS1; apply StablePerm_Perm in HS1.
      symmetry in HS1.
      intros x y Hx Hy.
      apply le_weaken; (eapply Permutation_in; [apply HS1|]); easy.
  Qed.
End Weaken.
