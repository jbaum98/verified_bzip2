Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import BWT.Rotation.
Require Import BWT.Sorting.Prefix.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Repeat.
Require Import BWT.Rots.
Require Import BWT.Instances.

Import ListNotations.

Open Scope program_scope.

Lemma eq_map {A B : Type} (f g : A -> B) l :
  (forall x, f x = g x) -> map f l = map g l.
Proof.
  intros HExt; induction l; try reflexivity.
  simpl; rewrite HExt, IHl.
  reflexivity.
Qed.

Lemma map_map' {A B C : Type} : forall (f : A -> B) (g : B -> C) l,
    map g (map f l) = map (g ∘ f) l.
Proof.
  intros.
  rewrite map_map. apply eq_map.
  reflexivity.
Qed.

Lemma Forall2_eq {A : Type} : forall x y : list A,
    Forall2 eq x y <-> x = y.
Proof.
  split; intros.
  - induction H.
    + reflexivity.
    + subst. f_equal.
  - subst. induction y; constructor; auto.
Qed.

Lemma Forall2_map {A B : Type} (R : B -> B -> Prop) : forall (f : A -> B) (l l' : list A),
    length l = length l' ->
    Forall2 R (map f l) (map f l') <-> Forall2 (fun x y => R (f x) (f y)) l l'.
Proof.
  induction l; intros.
  - simpl in H.
    replace l' with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
    split; constructor.
  - destruct l' as [|a' l']; [inversion H|].
    simpl; split; intros HImp; inversion HImp; subst; clear HImp; constructor; auto.
    + apply IHl; auto.
    + apply IHl; auto.
Qed.

Lemma Forall2_impl : forall (A B : Type) (P Q : A -> B -> Prop),
    (forall a b, P a b -> Q a b) -> forall l l', Forall2 P l l' -> Forall2 Q l l'.
Proof.
  intros. induction H0; constructor; auto.
Qed.

Lemma map_injective {A B : Type} : forall (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' -> l = l'.
Proof.
  intros f l l' HInj MapEq.
  assert (length l = length l'). {
    rewrite <- map_length with (f := f), MapEq, -> map_length.
    easy.
  }
  assert (Forall2 (fun x y => f x = f y) l l'). {
    apply Forall2_eq in MapEq.
    apply (proj1 (Forall2_map eq f l l' H)) in MapEq.
    apply MapEq.
  }
  apply Forall2_eq.
  eapply Forall2_impl; [| apply H0].
  cbv beta; intros. auto.
Qed.

Lemma map_forall_eq {A B : Type} : forall (l : list A) (f g : A -> B),
    Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
  induction l; intros.
  - reflexivity.
  - inversion H; subst; clear H.
    simpl. f_equal; auto.
Qed.

Section Permutations.
  Context {A : Type} {P : A -> Prop} .
  Variables l l' : list A.
  Hypothesis HP : Permutation l l'.

  Theorem Permutation_exists :
    Exists P l -> Exists P l'.
  Proof.
    intros HE.
    apply Exists_exists.
    apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
    eauto using Permutation_in.
  Defined.

  Theorem Permutation_forall :
    Forall P l -> Forall P l'.
  Proof.
    intros.
    apply Forall_forall.
    intros a HA.
    apply Permutation_in with (l' := l) in HA; auto using Permutation_sym.
    revert a HA.
    apply Forall_forall.
    auto.
  Qed.
End Permutations.

Section PrependColumn.
  Context {A : Type}.

  Definition prepend_col := zipWith (@cons A).

  Lemma prepend_cons : forall ahd bhd atl btl,
      prepend_col (ahd :: atl) (bhd :: btl) = (ahd :: bhd) :: prepend_col atl btl.
  Proof. reflexivity. Qed.

  Theorem prepend_hd_tl : forall l d,
      Forall (fun x => ~ x = []) l ->
      prepend_col (map (hd d) l) (map (@tl A) l) = l.
  Proof.
    induction l; intros.
    - simpl. reflexivity.
    - inversion H; subst; clear H.
      cbn. rewrite IHl by auto. f_equal.
      destruct a; try contradiction.
      reflexivity.
  Qed.

  Theorem prepend_map_tl : forall l c,
      length c >= length l ->
      map (@tl A) (prepend_col c l) = l.
  Proof.
    induction l; intros.
    - unfold prepend_col. rewrite zipWith_nil_r. reflexivity.
    - destruct c; [simpl in H; omega|].
      rewrite prepend_cons. simpl.
      f_equal. apply IHl. simpl in H. omega.
  Qed.
End PrependColumn.

Section AppendCol.
  Context {A : Type}.

  Definition append_col (c : list A) (m : list (list A)) :=
    map lrot (prepend_col c m).

  Theorem map_lrot_prepend : forall c m,
      map lrot (prepend_col c m) = append_col c m.
  Proof.
    reflexivity.
  Qed.

  Theorem map_rrot_append : forall c m,
      map rrot (append_col c m) = prepend_col c m.
  Proof.
    intros.
    apply map_injective with (f := lrot); [apply lrot_injective|].
    rewrite map_map.
    erewrite map_ext; [|apply r_l_rot_inverse].
    rewrite map_id. reflexivity.
  Qed.

  Theorem append_last_init : forall l d,
      Forall (fun x => ~ x = []) l ->
      append_col (map (fun x => last x d) l) (map init l) = l.
  Proof.
    induction l; intros.
    - reflexivity.
    - inversion H; subst; clear H.
      simpl. unfold append_col in *. cbn.
      rewrite IHl; auto.
      f_equal.
      destruct a; try contradiction.
      symmetry. apply init_last_destr.
  Qed.

  Theorem map_lrot_append : forall l d,
      Forall (fun x => ~ x = []) l ->
      map lrot l = append_col (map (hd d) l) (map (@tl A) l).
  Proof.
    intros. unfold append_col.
    rewrite prepend_hd_tl; auto.
  Qed.

  Theorem map_rrot_prepend : forall (l : list (list A)) d,
      Forall (fun x => ~ x = []) l ->
      map rrot l = prepend_col (map (fun x => last x d) l) (map init l).
  Proof.
    intros.
    apply map_injective with (f := lrot); [apply lrot_injective|].
    rewrite map_map.
    erewrite map_ext; [|apply r_l_rot_inverse].
    rewrite map_id.
    pose proof append_last_init as ALI.
    unfold append_col in ALI. symmetry. auto.
  Qed.
End AppendCol.

Section SortRotations.
  Context {A : Type} `{O : Ord A}.
  Hypothesis Heqv : forall x y, eqv x y -> eq x y.

  Local Arguments Sorted {_} _.
  Local Arguments Stable {_} _.
  Local Arguments eqv_dec {_} _.
  Local Arguments eqv {_} _.
  Local Arguments le {_} _.

  Lemma prepend_sorted : forall k mat c,
      length c >= length mat ->
      Sorted (Ord_list_k k) mat ->
      Sorted (Ord_list_k (S k)) (sort 1 (prepend_col c mat)).
  Proof.
    intros k mat c HL HS.
    apply Sorted_IndexSorted_iff; intros i j d HIJ.
    apply Sorted_IndexSorted_iff in HS.
    remember (nth i _ _) as x.
    remember (nth j _ _) as y.
    destruct x as [|xhd xtl]; [constructor|].
    destruct y as [|yhd ytl]; [admit|].

    assert (Stable (Ord_list_k 1)(sort 1 (prepend_col c mat)) (prepend_col c mat) /\
            Permutation (sort 1 (prepend_col c mat)) (prepend_col c mat))
      as HSt by (destruct (sort_props 1 (prepend_col c mat)); intuition).
    apply IndexStable_iff in HSt.

    destruct (eqv_dec O xhd yhd).
    - apply le_cons_eq. auto.

      unfold IndexStable in HSt.
      specialize HSt with (i := i) (j := j) (d := d).
      destruct HSt as [i' [j' [Hi' [Hj' HIJ']]]]; auto.
      rewrite <- Heqy, <- Heqx.
      admit.

      rewrite <- Hi' in Heqx.
      rewrite <- Hj' in Heqy.
      apply f_equal with (f := (@tl _)) in Heqy.
      rewrite <- map_nth in Heqy.
      simpl in Heqy.
      apply f_equal with (f := (@tl _)) in Heqx.
      rewrite <- map_nth in Heqx.
      simpl in Heqx.
      rewrite prepend_map_tl in Heqx; [|auto].
      rewrite prepend_map_tl in Heqy; [|auto].
      rewrite Heqx, Heqy.
      apply HS. rewrite sort_length in HIJ'.
      admit.
    - apply le_cons_lt.
      destruct (proj1 (lt_spec xhd yhd)); [|auto|contradiction]; clear n.

      assert (Sorted (Ord_list_k 1) (sort 1 (prepend_col c mat)))
        as HS1 by apply sort_sorted.
      apply Sorted_IndexSorted_iff in HS1.
      apply f_equal with (f := hd xhd) in Heqx.
      apply f_equal with (f := hd yhd) in Heqy.
      rewrite <- map_nth in Heqy.
      rewrite <- map_nth in Heqx.
      simpl in Heqy; simpl in Heqx.
      rewrite Heqy, Heqx.
      eapply HS1.

      eapply Sorted_uncons.



    remember (sort 1 (prepend_col c mat)) as s.
    assert (Sorted (Ord_list_k 1) s) by (subst; apply sort_sorted).
    assert (Stable (Ord_list_k 1) s (prepend_col c mat)) by (subst; apply sort_stable).
    clear Heqs. generalize dependent c. generalize dependent mat. generalize dependent s.
    induction s as [|shd stl]; [constructor|].
    constructor.
    - admit.
    - destruct c as [|chd ctl]; [admit|].
      destruct mat as [|mathd mattl]; [admit|].
      eapply IHstl. eapply Sorted_uncons. eauto.
      eapply Sorted_uncons. apply H0. simpl in H.
      instantiate (1 := ctl). omega.



    - constructor.
    generalize dependent c. induction H0; intros.
    - unfold prepend_col. rewrite zipWith_nil_r. constructor.
    - destruct c as [|chd ctl]; [simpl in *; omega|].
      rewrite prepend_cons.
      constructor.

    remember (sort 1 _) as s. generalize dependent c. generalize dependent mat.
    induction s as [|a s]; intros mat HS c HL Heqs; constructor.
    - admit.
    - eapply Sorted_uncons. rewrite Heqs.
      eapply IHs. eauto.
    - intros.
      destruct a as [|ah atl]; [apply le_nil|].
      destruct x as [|xh xtl]; [exfalso; eapply sorted_hd_nonempty;
                                [rewrite Heqs; apply sort_sorted|eauto|easy]|].
      destruct (eqv_dec _ ah xh).
      + apply le_cons_eq; auto. clear Heqv.
        assert (In xtl (map (@tl _) s))
          by (replace xtl with (tl (xh :: xtl)) by reflexivity; apply in_map; auto).
        clear H.
        apply @Sorted_uncons with (O := Ord_list_k k) (tl := map (@tl _) s);
          [|auto].
        replace (atl :: map _ _) with (map (@tl _) ((ah :: atl) :: s))
          by reflexivity.
        eapply sort_tl.
        constructor.
        intros. destruct x; [admit|].
        apply @le_cons_eq with (H := O).
        admit.

        assert (Sorted (Ord_list_k k) (map (@tl _)))

        assert (Stable (Ord_list_k 1) ((ah :: atl) :: s) (prepend_col c mat))
          as HSt by (rewrite Heqs; apply sort_stable).
        specialize (HSt (ah :: atl)).
        simpl in HSt.
        destruct (eqv_dec (Ord_list_k 1) (ah :: atl) (ah :: atl));
          [|exfalso; apply n; apply eqv_refl].
        clear e0.

        remember (filter _ _) as f in HSt at 2.
        assert (Sorted (Ord_list_k k) f).
        rewrite Heqf. apply sorted_filter.

        destruct f. simpl in H2. inversion H2.
        simpl in H2. inversion H2; clear H2.
        assert (Sorted (Ord_list_k k) (map (@tl _) (prepend_col c mat))). {
          rewrite prepend_map_tl; auto.
        }
        assert (Forall (fun x => exists t, x = ah :: t) (l :: f)). {
          eapply Forall_impl with (P := eqv (Ord_list_k 1) (ah :: atl)).
          intros. exists (tl a).
          inversion H3.
          apply eqv_k_correct in H3.
          destruct a.
          simpl in H3. inversion H3.
          simpl in H3. inversion H3; subst; clear H3.
          apply filter_Forall with (f0 := eqv_dec (Ord_list_k 1) (ah :: atl))
                              ].
        }
        pose proof

        apply map_injective in H1


      destruct mat.
      unfold prepend_col in Heqs. rewrite zipWith_nil_r in Heqs.
      rewrite sort_nil in Heqs. discriminate.
      destruct c.
      unfold prepend_col in Heqs. rewrite zipWith_nil_l in Heqs.
      rewrite sort_nil in Heqs. discriminate.
      apply IHs with (mat := mat) (c := c).
      inversion H; auto.
      rewrite prepend_cons in Heqs.

      +

    induction c using list_ind2.

    - apply LSorted_nil.
    - destruct mat; [apply LSorted_nil|].
      rewrite prepend_cons.

  Lemma stable_S_k : forall k l,
      Stable (Ord_list_k (S k))
             (map (rep rrot (S k)) l)
             (sort 1 (map rrot (sort k (map (rep rrot k) l)))).
  Proof.
    intros k l.
    induction l.
    - compute. reflexivity.
    - unfold Stable. intros. simpl.
      destruct (eqv_dec (Ord_list_k (S k)) x (rrot (rep rrot k a))).
  Admitted.

  Theorem sort_rrot_k : forall k l,
    sort k (map (rep rrot k) l) = rep (sort 1 ∘ map rrot) k l.
  Proof.
    induction k; intros; [simpl; rewrite map_id; apply sort_zero|].
    simpl. unfold compose.
    rewrite <- IHk; clear IHk.
    replace (fun z => rrot (rep rrot k z)) with (rep (@rrot A) (S k))
      by (extensionality z; symmetry; apply rep_l).
    apply @stable_sort_unique with (O := Ord_list_k (S k)); auto.
    - apply sort_sorted.
    - admit.
    - eapply Permutation_trans. apply sort_perm.
      apply Permutation_sym.
      eapply Permutation_trans. apply sort_perm.
      eapply Permutation_trans. apply Permutation_map. apply sort_perm.
      rewrite map_map. apply Permutation_refl.
    - eapply Stable_trans. apply sort_stable.
      apply stable_S_k.
  Admitted.

  Lemma sort_succ_rrot : forall k (l : list (list A)),
      sort (S k) (map rrot l) = sort 1 (map rrot (sort k l)).
  Proof.
    intros.
    pose proof (sort_rrot_k (S k)) as E6.
    simpl rep at 2 in E6.
    specialize E6 with (l := map (rep lrot k) l).
    rewrite <- sort_rrot_k in E6.
    pose proof rep_inv_r (@lrot A) rrot l_r_rot_inverse as rep_inv.
    do 2 rewrite map_map' in E6.
    rewrite eq_map with (f := rep rrot (S k) ∘ rep lrot k) (g := rrot) in E6
      by (intros; unfold compose;
          rewrite rep_inv, Nat.sub_succ_l, Nat.sub_diag;
          [reflexivity|apply Nat.le_refl|apply Nat.le_succ_diag_r]).
    rewrite eq_map with (f := rep rrot k ∘ rep lrot k) (g := id)in E6
      by (intros; unfold compose; rewrite rep_inv;
          [rewrite Nat.sub_diag; reflexivity|apply Nat.le_refl]).
    (* TODO For some reason hangs at the end *)
    replace (sort 1 (map rrot (sort k l)))
    with ((sort 1 ∘ map rrot) (sort k l)) by reflexivity.
    rewrite map_id in E6.
    apply E6.
  Qed.
End SortRotations.

Section Cols.
  Context {A : Type}.

  Definition cols j := map (@firstn A j).

  Context `{Ord A}.

  Lemma cols_rrot : forall j l d,
      cols (S j) (map rrot l) = prepend_col (map (fun x => last x d) l) (cols j l).
  Admitted.

  Theorem cols_sort1 : forall k j l,
      cols j (sort k l) = cols j (sort (Nat.min j k) l).
  Admitted.

  Theorem cols_sort2 : forall k j l,
      cols j (sort k l) = sort (Nat.min j k) (cols j l).
  Admitted.

  Lemma cols_sort_lt : forall k j l,
      j <= k -> cols j (sort k l) = sort j (cols j l).
  Proof.
    intros.
    replace j with (Nat.min j k) at 2 by (apply Min.min_l; auto).
    apply cols_sort2.
  Qed.

  Theorem cols_sort_perm : forall k j p l,
      (forall l, Permutation l (p l)) -> cols j (sort k (p l)) = cols j (sort k l).
  Admitted.

  Theorem cols_sort_shift : forall k j l,
      1 <= j <= k ->
      cols j (sort k (rots l)) = sort 1 (cols j (map rrot (sort k (rots l)))).
  Proof.
    intros.
    replace 1 with (Nat.min j 1) by (apply Min.min_r; omega).
    rewrite <- cols_sort2, <- sort_succ_rrot, map_rrot_rots, cols_sort2.
    rewrite cols_sort_perm by apply rrot_perm.
    rewrite cols_sort2.
    replace (Nat.min j (S k)) with (Nat.min j k) by (rewrite ?Nat.min_l; omega).
    reflexivity.
  Qed.

  Theorem cols_id : forall n mat,
      Forall (fun x => length x <= n) mat ->
      cols n mat = mat.
  Proof.
    induction n; intros mat HL.
    - unfold cols. unfold firstn.
      rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      simpl; intros.
      assert (length a = 0) by omega.
      symmetry. apply length_zero_iff_nil; auto.
    - unfold cols. rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      cbv beta. intros.
      apply firstn_all2; auto.
  Qed.
End Cols.

Section Lexsort.
  Context {A : Type} `{Ord A}.

  Lemma orig_in_sorted_rots : forall l k,
      l <> [] -> Exists (eq l) (sort k (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
    apply sort_perm.
    apply orig_in_rots. auto.
  Qed.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply sort_perm. apply rots_row_length.
  Qed.
End Lexsort.

Section FindIndex.
  Context {A : Type} `{EqDec A}.

  Fixpoint findIndex (x : A) (ls : list A) : nat :=
    match ls with
    | [] => 0
    | hd :: tl =>
      match x == hd with
      | left _ => 0
      | right Neq => S (findIndex x tl)
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
End FindIndex.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

  Definition bwp (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => List.map (fun x => last x hd) (sort (length l) (rots l))
    end.

  Theorem bwp_nonempty : forall l,
      l <> [] ->
      forall d, bwp l = List.map (fun x => last x d) (sort (length l) (rots l)).
  Proof.
    destruct l; intros.
    - contradiction.
    - apply map_forall_eq.
      apply Forall_forall.
      intros.
      assert (x <> []). {
        apply (Forall_forall (fun x => ~ x = []) (sort (length (a :: l)) (rots (a :: l)))); auto.
        eapply Permutation_forall. apply sort_perm.
        apply rots_nonempty; auto.
      }
      apply last_nonempty; auto.
  Qed.

  Theorem bwp_length : forall l,
      length (bwp l) = length l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite map_length.
      rewrite sort_length.
      rewrite rots_length.
      reflexivity.
  Qed.

  Definition bwn (l : list A) : nat :=
    findIndex l (sort (length l) (rots l)).

  Theorem bwn_correct : forall xs d,
    xs <> [] -> nth (bwn xs) (sort (length xs) (rots xs)) d = xs.
  Proof.
    intros.
    unfold bwn.
    apply findIndex_correct.
    apply orig_in_sorted_rots. auto.
  Qed.
End Transform.

Lemma map_const {A B} : forall (f : A -> B) l c,
    (forall x, f x = c) -> map f l = repeat c (length l).
Proof.
  intros.
  induction l; [reflexivity|].
  simpl. rewrite H. f_equal. auto.
Qed.

Section Recreate.
  Context {A : Type} `{Ord A}.

  Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
    match j with
    | O    => map (const []) l
    | S j' => sort 1 (prepend_col l (recreate j' l))
    end.

  Theorem recreate_inspiration : forall j l,
      j < length l ->
      cols (S j) (sort (length l) (rots l)) =
      sort 1 (prepend_col (bwp l) (cols j (sort (length l) (rots l)))).
  Proof.
    intros. destruct l eqn:HL; [reflexivity|].
    rewrite <- HL in *. assert (l <> []) by (intro c; subst; inversion c).
    rewrite cols_sort_shift by omega.
    rewrite cols_rrot with (d := a).
    rewrite <- bwp_nonempty with (d := a) by auto.
    reflexivity.
  Qed.

  Lemma recreate_correct_gen : forall j l,
      j <= length l ->
      recreate j (bwp l) = cols j (sort (length l) (rots l)).
  Proof.
    induction j; intros.
    - unfold cols. simpl.
      do 2 (erewrite map_const; [|unfold const; reflexivity]).
      rewrite bwp_length, sort_length, rots_length.
      reflexivity.
    - simpl.
      rewrite recreate_inspiration by omega.
      rewrite IHj by omega.
      reflexivity.
  Qed.

  Theorem recreate_correct : forall l,
      recreate (length l) (bwp l) = sort (length l) (rots l).
  Proof.
    intros.
    rewrite recreate_correct_gen by omega.
    rewrite cols_id; auto.
    eapply Forall_impl; [|apply sort_rots_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{O : Ord A} `{E : EqDec A eq}.

  Definition unbwt (t : nat) (l : list A) : list A :=
    nth t (recreate (length l) l) l.

  Theorem unbwt_correct : forall xs : list A,
      unbwt (bwn xs) (bwp xs) = xs.
  Proof.
    intros [|a xs]; [reflexivity|].
    unfold unbwt.
    rewrite bwp_length.
    rewrite recreate_correct.
    apply bwn_correct.
    intro contra; inversion contra.
  Qed.
End Unbwt.
