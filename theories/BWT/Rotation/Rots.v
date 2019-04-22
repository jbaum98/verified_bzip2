Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.Iterate.
Require Import BWT.Lib.Repeat.
Require Import BWT.Lib.List.
Require Import BWT.Rotation.Rotation.

Import ListNotations.

Section Rots.
  Context {A : Type}.

  Definition rots (l : list A) : list (list A) :=
    iter lrot (length l) l.

  Lemma rots_destr : forall (l : list A),
      l <> [] -> exists r, rots l = l :: r.
  Proof.
    intros.
    unfold rots.
    destruct l as [| a [| b tl]] eqn:HD; simpl; try contradiction; clear H.
    - eexists. f_equal.
    - eexists. f_equal.
  Defined.

  Lemma rots_length : forall l,
      length (rots l) = length l.
  Proof.
    intros. unfold rots. apply iter_length.
  Qed.

  Lemma rots_row_length : forall l,
      Forall (fun x => length x = length l) (rots l).
  Proof.
    intros. apply iter_preserves; auto.
    intros. eapply eq_trans. symmetry. apply lrot_length. auto.
  Qed.

  Theorem map_rrot_rots : forall l,
      map rrot (rots l) = rrot (rots l).
  Proof.
    intros; apply nth_eq; [rewrite -> map_length, rrot_length; reflexivity|].
    intros i d HI.
    rewrite -> nth_indep with (d' := rrot d), map_nth by auto.
    unfold rots in HI; rewrite -> map_length, iter_length in HI.
    unfold rots; rewrite iter_nth by omega.
    rewrite nth_rrot, iter_length by (rewrite iter_length; omega).
    destruct i; simpl Nat.add; simpl Repeat.rep; simpl id.
    - rewrite Nat.mod_small, iter_nth, Nat.sub_1_r by omega.
      symmetry; apply lrot_rep_pred.
    - remember (length l) as L.
      replace (S (i + L) - 1) with (i + 1 * L) by omega.
      rewrite Nat.mod_add, Nat.mod_small, iter_nth, rep_l by omega.
      apply rep_inv1_l. apply l_r_rot_inverse.
  Qed.

  Lemma orig_in_rots : forall l,
      l <> [] -> Exists (eq l) (rots l).
  Proof.
    intros. simpl.
    destruct (rots_destr l) as [x HCons]; auto.
    rewrite HCons.
    apply Exists_cons_hd. apply eq_refl.
  Qed.

  Theorem rots_nonempty : forall l,
      Forall (fun x => ~ (x = [])) (rots l).
  Proof.
    destruct l eqn:HL.
    - constructor.
    - rewrite <- HL.
      assert (l <> []) by (intro c; subst; inversion c). clear HL.
      eapply Forall_impl with (P := fun x => length x = length l).
      intros x Hlen.
      assert (HlenL: length l <> 0)
        by (rewrite length_zero_iff_nil; intro c; contradiction).
      rewrite <- Hlen in HlenL.
      rewrite <- length_zero_iff_nil; auto.
      unfold rots. apply iter_preserves.
      intros x Hx. rewrite <- Hx. symmetry; apply lrot_length.
      auto.
  Qed.
End Rots.
