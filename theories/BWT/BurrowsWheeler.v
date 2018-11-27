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
Require Import BWT.ZipWith.

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
  Context {A : Type} `{O : Ord A} `{E : EqDec A eq}.

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
    destruct y as [|yhd ytl]; [exfalso; eapply Sorted_before_nonempty;
                               [eapply sort_sorted|eauto..]|].

    assert (Stable (Ord_list_k 1) (prepend_col c mat) (sort 1 (prepend_col c mat)) /\
            Permutation (prepend_col c mat) (sort 1 (prepend_col c mat)))
      as HSt by (destruct (sort_props 1 (prepend_col c mat));
                 split; [apply Stable_sym|apply Permutation_sym]; intuition).
    eapply IndexStable_iff in HSt.

    assert (length (prepend_col c mat) = length mat). {
      unfold prepend_col.
      rewrite zipWith_length.
      rewrite Nat.min_r by auto. auto.
    }

    destruct (eqv_dec O xhd yhd).
    - apply le_cons_eq. auto.

      unfold IndexStable in HSt.
      destruct (HSt d) as [HeqL [p [pbound [pinj [pcorrect pmono]]]]].
      pose proof Heqx as Hxtl; pose proof Heqy as Hytl.
      apply f_equal with (f := (@tl _)) in Hytl.
      apply f_equal with (f := (@tl _)) in Hxtl.
      simpl in Hxtl; simpl in Hytl.
      rewrite Hxtl, Hytl.
      rewrite !pcorrect.
      rewrite <- !map_nth with (f := @tl A).
      rewrite prepend_map_tl.
      apply HS.
      split. apply pmono. unfold eqv, le, Ord_list_k.
      rewrite <- Heqx, <- Heqy.
      rewrite !le_k_1. unfold eqv in *; intuition.
      omega. rewrite <- H. apply pbound. omega.
      omega. omega. omega.
    - apply le_cons_lt.
      destruct (proj1 (lt_spec xhd yhd)); [|auto|contradiction]; clear n.
      eapply le_k_1. rewrite Heqy, Heqx.

      assert (Sorted (Ord_list_k 1) (sort 1 (prepend_col c mat)))
        as HS1 by apply sort_sorted.
      apply Sorted_IndexSorted_iff in HS1.
      apply HS1. auto.
  Qed.

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
    - erewrite map_rrot_prepend.
      apply prepend_sorted.
      rewrite !map_length, sort_length, map_length. omega.
      admit. (* Prove mapping init preserves sorted *)
      eapply Permutation_forall.
      apply Permutation_sym. apply sort_perm.
      apply Forall_forall.
      intros x Hin. apply in_map_iff in Hin.
      destruct Hin.
      admit.

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

  Context `{Ord A} `{EqDec A eq}.
  Hypothesis Heq : forall x y, eqv x y -> x = y.

  Local Arguments Sorted {_} _.
  Local Arguments Stable {_} _.
  Local Arguments IndexStable {_} _.
  Local Arguments eqv_dec {_} _.
  Local Arguments eqv {_} _.
  Local Arguments le {_} _.

  Lemma cols_rrot : forall j l d,
      cols (S j) (map rrot l) = prepend_col (map (fun x => last x d) l) (cols j l).
  Admitted.

  Lemma foo : forall j l l',
     eqv (Ord_list_k j) (firstn j l) (firstn j l') <-> (firstn j l) = (firstn j l').
  Proof.
    induction j; intros.
    - cbn. split; intros. reflexivity. apply eqv_zero.
    - split; intros.
  Admitted.

  Theorem cols_sort1 : forall k j l,
      cols j (sort k l) = cols j (sort (Nat.min j k) l).
  Proof.
    intros. destruct (le_gt_dec j k) as [LJK | LKJ]; unfold le, Ord_nat in *.
    - rewrite Nat.min_l by omega.
      apply @stable_sort_unique with (O := Ord_list_k j).
      + apply @sorted_preserve with (OA := Ord_list_k k).
        intros. eapply le_k_firstn_le; eauto.
        apply sort_sorted.
      + apply @sorted_preserve with (OA := Ord_list_k j).
        intros. eapply le_k_firstn_le; [|apply H3]. omega.
        apply sort_sorted.
      + apply Permutation_map. eapply perm_trans. apply sort_perm.
        apply Permutation_sym. apply sort_perm.
      + apply IndexStable_iff.
        assert (ISJ: IndexStable (Ord_list_k j) l (sort j l)). {
          apply IndexStable_iff. split.
          apply Stable_sym. apply sort_stable.
          apply Permutation_sym. apply sort_perm.
        }
        assert (ISK: Stable (Ord_list_k k) (sort k l) l). {
           apply sort_stable.
        }
        assert (ISK': IndexStable (Ord_list_k j) (cols j (sort k l)) (cols j l)). {
          apply IndexStable_iff. split.
          apply stable_map_equiv_eq; [|apply sort_perm].
          intros. apply foo. auto.
          apply Permutation_map. apply sort_perm.
        }

        intros d.
        destruct (ISJ d) as [HLJ [fj [fjbound [fjinj [fjcorrect fjmono]]]]].
        destruct (ISK' d) as [HLK [fk [fkbound [fkinj [fkcorrect fkmono]]]]].
        pose proof (sort_length k l).
        pose proof (sort_length j l).
        split. unfold cols. rewrite !map_length. omega.
        exists (fun x => fk (fj x)). unfold cols. rewrite !map_length.
        repeat split.
        * intros x Hx. rewrite <- map_length with (f := firstn j). unfold cols in *.
          apply fkbound. rewrite <- HLK, map_length. apply fjbound. omega.
        * intros x y Hx Hy Heq'.
          apply fjinj; [rewrite <- HLJ; omega..|].
          apply fkinj;
            [rewrite <- HLK; unfold cols; rewrite map_length; apply fjbound; omega..|].
          auto.
        * intros.
          rewrite <- fkcorrect.
          rewrite !nth_indep with (d := d) (d' := firstn j d).
          unfold cols.
          rewrite !map_nth. f_equal.
          rewrite <- fjcorrect. reflexivity.
          1-4: unfold cols; rewrite ?map_length, ?HLJ; try omega; try apply fkbound;
            rewrite ?sort_length; apply fjbound; omega.
        * intros. apply fkmono. unfold cols.
          rewrite !nth_indep with (d := d) (d' := firstn j d).
          rewrite !map_nth. rewrite <- !fjcorrect.
          rewrite <- !map_nth with (f := firstn j).
          rewrite <- !nth_indep with (d := d) (d' := firstn j d).
          apply H3.
          1-7: unfold cols; rewrite ?map_length, ?HLJ; try split; try omega; try apply fkbound;
            rewrite ?sort_length; try apply fjbound; try omega.

          apply fjmono. admit.
          admit.
    - admit.
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
    apply Permutation_sym. apply sort_perm.
    apply orig_in_rots. auto.
  Qed.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply Permutation_sym. apply sort_perm. apply rots_row_length.
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
        eapply Permutation_forall. apply Permutation_sym. apply sort_perm.
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
  Context {A : Type} `{Ord A} `{EqDec A eq}.

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

Print Assumptions unbwt_correct.
