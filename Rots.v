Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.omega.Omega.

Require Import Iterate.
Require Import Rotation.
Require Import Repeat.
Require Import Pointfree.

Import ListNotations.

Section Rots.
  Variable A : Type.

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
  Proof. intros. unfold rots. apply iter_length. Qed.

  Lemma rots_length' : @length (list A)∘ rots = @length A.
  Proof. intros. extensionality l. apply rots_length. Qed.

  Lemma rots_row_length : forall l,
      Forall (fun x => length x = length l) (rots l).
  Proof.
    intros. apply iter_preserves; auto.
    intros. eapply eq_trans. symmetry. apply lrot_length. auto.
  Qed.

  Theorem map_rrot_rots : map rrot ∘ rots = rrot ∘ rots.
  Proof.
    assert (pointfree: forall D B C (f g : D -> B) h (x : C),
               f (h x) = g (h x) -> (f ∘ h) x = (g ∘ h) x)
      by (intros; unfold compose; auto).

    extensionality l. unfold compose, rots.
    apply nth_eq'. rewrite map_length, rrot_length; reflexivity.

    remember (length l) as n. rewrite ?map_length, ?iter_length.
    intros i d H.

    replace (nth' i d _) with (nth' i (rrot d) (map rrot (iter lrot n l)))
      by (unfold nth'; apply nth_indep; rewrite map_length, iter_length; omega).

    change ((nth' i (rrot d) ∘ map rrot ∘ iter lrot n) l =
            (nth' i d ∘ rrot ∘ iter lrot n) l).

    crewrite map_nth'.
    crewrite iter_nth by omega.
    erewrite pointfree with (f := (nth' i d ∘ rrot));
      [|eapply nth_rrot]; [|rewrite iter_length..]; [|reflexivity|omega].

    destruct i; simpl Nat.add; simpl rep; simpl id.
    - rewrite Nat.mod_small by omega.
      rewrite iter_nth by omega.
      simpl. rewrite Nat.sub_1_r.
      symmetry. unfold compose, id. rewrite Heqn; apply lrot_rep_pred.
    - replace (S (i + n) - 1) with (i + 1 * n) by omega.
      rewrite Nat.mod_add, Nat.mod_small by omega.
      rewrite iter_nth by omega.
      rewrite rep_l.
      crewrite (rep_inv1_l _ _ _ (l_r_rot_inverse A)). reflexivity.
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

Arguments rots {_}.
