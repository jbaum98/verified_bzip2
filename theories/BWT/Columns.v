Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.List.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Rotation.Rots.
Require Import BWT.Sorting.Key.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Ord.

Import Coq.Lists.List.ListNotations.

Section Cols.
  Context {A : Type} `{Ord A}.

  Definition cols j := map (@firstn A j).

  Theorem lexsort_rots_hdsort : forall l,
      hdsort (map rrot (lexsort (rots l))) = lexsort (rots l).
  Admitted.

  Theorem cols_S_hdsort : forall j l,
      cols (S j) (hdsort l) = hdsort (cols (S j) l).
  Admitted.

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
