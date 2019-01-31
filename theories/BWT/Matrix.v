Require Import BWT.Sorting.Ord.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import BWT.Sorting.Prefix.
Require Import BWT.Rotation.
Require Import BWT.Repeat.
Require Import BWT.Lib.
Require Import BWT.Rots.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.

Import ListNotations.

Open Scope program_scope.

Section SortRotations.
  Context {A : Type} `{O : Ord A}.

  Theorem foo : forall k l,
sort (S k) (map rrot l) = (sort 1 ∘ map rrot) (sort k l) ->
      @sort A O (S k) (map rrot l) = @sort A O 1 (map rrot (sort k l)).
  Proof. unfold compose in *. easy. Qed.

  Lemma sort_succ_k : forall k l,
      sort (S k) l = sort 1 (map rrot (sort k (map lrot l))).
  Proof.
  Admitted.

  Theorem sort_rrot_k : forall k l,
    sort k (map (rep rrot k) l)= rep (sort 1 ∘ map rrot) k l.
  Proof.
  Admitted.

  Lemma sort_succ_rrot : forall k (l : list (list A)),
      @sort A O (S k) (map rrot l) = @sort A O 1 (map rrot (sort k l)).
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

Fixpoint zipWith {A B C} (f : A -> B -> C) (a : list A) (b : list B) : list C :=
  match (a, b) with
  | (ahd :: atl, bhd :: btl) => f ahd bhd :: zipWith f atl btl
  | _ => []
  end.

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

  Lemma cols_rrot : forall j l d,
      cols (S j) (map rrot l) = prepend_col (map (fun x => last x d) l) (cols j l).
  Admitted.
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
