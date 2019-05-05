Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.List.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Rotation.Rots.
Require Import BWT.Sorting.Key.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Ord.
Require Import BWT.Lib.Repeat.
Require Import BWT.Lib.ZipWith.

Import Coq.Lists.List.ListNotations.

Section Cols.
  Context {A : Type} `{Ord A}.

  Definition cols (j : nat) : list (list A) -> list (list A)
    := map (firstn j).

  Theorem cols_hdsort_comm : forall j l,
      cols (S j) (hdsort l) = hdsort (cols (S j) l).
  Proof.
    intros j l.
    unfold cols, hdsort; symmetry.
    apply key_sort_inv.
    intros []; reflexivity.
  Qed.

  Theorem cols_id : forall j m,
      Forall (fun x => length x <= j) m ->
      cols j m = m.
  Proof.
    intros j m HL.
    unfold cols; rewrite <- map_id.
    apply map_forall_eq.
    eapply Forall_impl; [|apply HL].
    cbn; intros r Hr.
    apply firstn_all2; easy.
  Qed.
End Cols.

Section PrependColumn.
  Context {A : Type}.

  Definition prepend_col : list A -> list (list A) -> list (list A)
    := zipWith cons.

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

  Lemma firstn_rrot : forall j (l : list A) d,
      j < length l ->
      firstn (S j) (rrot l) = last l d :: firstn j l.
  Proof.
    intros j [|h l] d H; cbn in H; [omega|].
    cbn [rrot firstn].
    rewrite last_nonempty with (d' := d) by (intro c; inversion c).
    f_equal.
    apply firstn_init; auto.
  Qed.

  Lemma cols_map_rrot : forall j l d,
      Forall (fun x => j < length x) l ->
      cols (S j) (map rrot l) = prepend_col (map (fun x => last x d) l) (cols j l).
  Proof.
    intros j l; revert j; induction l as [|h t]; intros j d HJ.
    unfold prepend_col; reflexivity.
    cbn [map cols]; rewrite prepend_cons.
    f_equal.
    apply firstn_rrot; inversion HJ; auto.
    apply IHt; inversion HJ; auto.
  Qed.

  Theorem map_tl_prepend : forall l c,
      length c >= length l ->
      map (@tl A) (prepend_col c l) = l.
  Proof.
    induction l; intros c HL.
    - unfold prepend_col. rewrite zipWith_nil_r. reflexivity.
    - destruct c as [|hc tc]. cbn in HL. omega.
      rewrite prepend_cons.
      cbn [map tl]. f_equal. apply IHl.
      cbn in HL. omega.
  Qed.
End PrependColumn.

Section AppendCol.
  Context {A : Type}.

  Implicit Types (c : list A) (m : list (list A)).

  Definition append_col c m := map lrot (prepend_col c m).

  Theorem map_lrot_prepend : forall c m,
      map lrot (prepend_col c m) = append_col c m.
  Proof. reflexivity. Qed.

  Theorem map_rrot_append : forall c m,
      map rrot (append_col c m) = prepend_col c m.
  Proof.
    intros.
    apply map_injective with (f := lrot); [apply lrot_injective|].
    rewrite map_map.
    erewrite map_ext; [|apply r_l_rot_inverse].
    rewrite map_id. reflexivity.
  Qed.

  Theorem append_last_init : forall m d,
      Forall (fun r => ~ r = []) m ->
      append_col (map (fun r => last r d) m) (map init m) = m.
  Proof.
    induction m as [|r m IH]; intros.
    - reflexivity.
    - inversion H; subst; clear H.
      cbn [append_col prepend_col zipWith map].
      fold (append_col (map (fun r : list A => last r d) m) (map init m)).
      rewrite IH; auto.
      f_equal.
      destruct r; try contradiction.
      symmetry. apply init_last_destr.
  Qed.

  Theorem map_lrot_append : forall m d,
      Forall (fun r => ~ r = []) m ->
      map lrot m = append_col (map (hd d) m) (map (@tl A) m).
  Proof.
    intros. unfold append_col.
    rewrite prepend_hd_tl; auto.
  Qed.

  Theorem map_rrot_prepend : forall m d,
      Forall (fun r => ~ r = []) m ->
      map rrot m = prepend_col (map (fun r => last r d) m) (map init m).
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
