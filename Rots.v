Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.omega.Omega.

Require Import Iterate.
Require Import Rotation.
Require Import Repeat.

Import ListNotations.

Section Rots.
  Context {A : Type}.

  Definition rots (l : list A) : list (list A) :=
    iter lrot (Nat.pred (length l)) l.

  Lemma rots_destr : forall (l : list A),
      exists r, rots l = l :: r.
  Proof.
    intros.
    unfold rots.
    destruct l as [| a [| b tl]]; simpl.
    - exists nil. auto.
    - eexists. f_equal.
    - eexists. f_equal.
  Defined.

  Lemma rots_len : forall l,
      Forall (fun x => length x = length l) (rots l).
  Proof.
    intros. apply iter_preserves; auto.
    intros. eapply eq_trans. symmetry. apply lrot_length. auto.
  Qed.

  Theorem map_rrot_rots : forall l,
      map rrot (rots l) = rrot (rots l).
  Proof.
    intros; unfold rots.
    apply nth_eq. rewrite -> map_length, rrot_length; reflexivity.
    intros.
    rewrite -> nth_indep with (d' := rrot d), map_nth by auto.
    rewrite -> map_length, iter_length in H.
    rewrite iter_nth by omega.
    rewrite nth_rrot by (rewrite iter_length; omega).
    rewrite iter_length.
    destruct i; simpl Nat.add; simpl Repeat.rep; simpl id.
    - rewrite Nat.mod_small by omega.
      rewrite iter_nth by omega.
      simpl; rewrite Nat.sub_0_r.
      symmetry; apply lrot_rep_pred.
    - remember (Nat.pred (length l)) as L.
      replace (S (i + S _) - 1) with (i + 1 * S L) by omega.
      rewrite Nat.mod_add, Nat.mod_small by omega.
      rewrite iter_nth by omega.
      rewrite rep_l.
      apply rep_inv1_l. apply l_r_rot_inverse.
  Qed.

  Lemma orig_in_rots `{EqDec (list A)}: forall l,
      Exists (equiv l) (rots l).
  Proof.
    intros. simpl.
    destruct (rots_destr l).
    rewrite H0.
    apply Exists_cons_hd. apply equiv_reflexive.
  Defined.
End Rots.
