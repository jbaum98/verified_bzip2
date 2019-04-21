Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.Repeat.
Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.List.

Import ListNotations.

Section Rot.
  Open Scope program_scope.

  Context {A : Type}.

  (* Rotate a list to the right by moving the last element to the front. *)
  Definition rrot (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => last l hd :: init l
    end.

  (* Rotate a list to the left by moving the first element to the end. *)
  Definition lrot (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => tl ++ [hd]
    end.

  Lemma rrot_app : forall (l: list A) y,
      rrot (l ++ [y]) = y :: l.
  Proof.
    intros.
    pose proof (app_cons_not_nil l [] y) as contra.
    unfold rrot.
    destruct (l ++ [y]) eqn:H.
    - contradiction.
    - rewrite <- H; clear contra H.
      rewrite last_app, init_app.
      simpl. rewrite app_nil_r.
      reflexivity.
  Qed.

  Lemma lrot_app : forall (x y: list A) a,
      lrot (a :: x ++ y) = x ++ y ++ [a].
  Proof.
    intros.
    unfold lrot.
    simpl.
    symmetry.
    apply app_assoc.
  Qed.

  Theorem rrot_rev : forall l,
    rrot (rev l) = rev (lrot l).
  Proof.
    destruct l.
    - reflexivity.
    - simpl.
      rewrite rrot_app.
      unfold lrot. simpl.
      rewrite rev_app_distr.
      reflexivity.
  Qed.

  Theorem lrot_rev : forall l,
      lrot (rev l) = rev (rrot l).
  Proof.
    intros.
    rewrite <- rev_involutive at 1.
    rewrite <- rrot_rev, -> rev_involutive.
    reflexivity.
  Qed.

  Theorem l_r_rot_inverse : forall (l: list A),
      rrot (lrot l) = l.
  Proof.
    destruct l.
    - reflexivity.
    - simpl. apply rrot_app.
  Qed.

  Theorem r_l_rot_inverse : forall (l: list A),
      lrot (rrot l) = l.
  Proof.
    intro l.
    rewrite <- rev_involutive at 1.
    rewrite <- rrot_rev.
    replace (rev (rrot l)) with (lrot (rev l)) by apply lrot_rev.
    rewrite l_r_rot_inverse.
    apply rev_involutive.
  Qed.

  Theorem lrot_perm : forall (l : list A),
      Permutation l (lrot l).
  Proof.
    destruct l as [|hd tl].
    - apply perm_nil.
    - simpl.
      rewrite <- rev_involutive.
      rewrite rev_unit.
      apply Permutation_sym.
      eapply perm_trans.
      apply Permutation_sym. apply Permutation_rev.
      apply perm_skip.
      eapply perm_trans.
      apply Permutation_sym. apply Permutation_rev.
      apply Permutation_refl.
  Qed.

  Theorem lrot_perm' : forall (x y : list A),
      Permutation x y -> Permutation x (lrot y).
  Proof.
    exact (f_perm lrot lrot_perm).
  Qed.

  Theorem lrot_perm'' : forall (x y : list A),
      Permutation x y -> Permutation (lrot x) (lrot y).
  Proof.
    exact (f_perm' lrot lrot_perm).
  Qed.

  Theorem rrot_perm : forall (l : list A),
      Permutation l (rrot l).
  Proof.
    intros.
    rewrite <- rev_involutive.
    rewrite <- lrot_rev.
    apply Permutation_sym. eapply perm_trans.
    apply Permutation_sym. apply Permutation_rev.
    eapply perm_trans. apply lrot_perm''.
    apply Permutation_sym. apply Permutation_rev.
    apply Permutation_sym. apply lrot_perm.
  Qed.

  Theorem rrot_perm' : forall (x y : list A),
      Permutation x y -> Permutation x (rrot y).
  Proof.
    exact (f_perm rrot rrot_perm).
  Qed.

  Theorem rrot_perm'' : forall (x y : list A),
      Permutation x y -> Permutation (rrot x) (rrot y).
  Proof.
    exact (f_perm' rrot rrot_perm).
  Qed.

  Theorem lrot_length : forall l,
        length l = length (lrot l).
  Proof.
    intros.
    apply Permutation_length.
    apply lrot_perm.
  Qed.

  Theorem rrot_length : forall l,
        length l = length (rrot l).
  Proof.
    intros.
    apply Permutation_length.
    apply rrot_perm.
  Qed.

  Theorem lrot_nonempty : forall l,
      l <> [] -> lrot l <> [].
  Proof.
    exact (f_nonempty lrot lrot_perm).
  Qed.

  Theorem rrot_nonempty : forall l,
      l <> [] -> rrot l <> [].
  Proof.
    exact (f_nonempty rrot rrot_perm).
  Qed.
End Rot.

Section Nth.
  Context {A : Type}.

  Lemma nth_lrot : forall (l : list A) i d,
      i < length l -> nth i (lrot l) d = nth ((i + 1) mod (length l)) l d.
  Proof.
    destruct l as [|x xs]; intros.
    - simpl lrot.
      rewrite nth_overflow; try rewrite nth_overflow; auto.
      simpl; omega.
    - destruct (Nat.eq_dec i (Nat.pred (length (x :: xs)))).
      + subst; clear H.
        replace (length (x :: xs)) with (length (lrot (x :: xs))) at 1
          by (symmetry; apply lrot_length).
        rewrite nth_last.
        simpl length; simpl Nat.pred; rewrite Nat.add_1_r.
        rewrite Nat.mod_same; try omega.
        rewrite nth_first.
        simpl. apply last_app.
      + simpl in H, n. assert (i < length xs) by omega; clear H n.
        rewrite Nat.mod_small by (simpl; omega).
        rewrite Nat.add_1_r. simpl nth.
        apply app_nth1; auto.
  Qed.

  Lemma hd_last_rev : forall (l : list A) d,
      hd d l = last (rev l) d.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl hd; simpl rev.
      rewrite last_app. reflexivity.
  Qed.

  Lemma hd_rev_last : forall (l : list A) d,
      hd d (rev l) = last l d.
  Proof.
    intros.
    rewrite <- rev_involutive with (l := l) at 2.
    rewrite hd_last_rev.
    reflexivity.
  Qed.

  Lemma last_lrot : forall (l : list A) d,
      last (lrot l) d = hd d l.
  Proof.
    destruct l; intros.
    - reflexivity.
    - simpl. apply last_app.
  Qed.

  Lemma hd_rrot : forall (l : list A) d,
      hd d (rrot l) = last l d.
  Proof.
    intros.
    rewrite hd_last_rev.
    rewrite <- lrot_rev.
    rewrite last_lrot.
    rewrite <- hd_rev_last.
    reflexivity.
  Qed.

  Lemma nth_rrot : forall (l : list A) i d,
      i < length l -> nth i (rrot l) d = nth ((i + length l - 1) mod (length l)) l d.
  Proof.
    destruct l as [|x xs]; intros.
    - simpl lrot.
      rewrite nth_overflow; try rewrite nth_overflow; auto.
      simpl; omega.
    - destruct i.
      + simpl lrot. rewrite nth_first.
        rewrite Nat.add_0_l.
        rewrite Nat.mod_small by omega.
        rewrite Nat.sub_1_r.
        rewrite nth_last.
        rewrite hd_rrot.
        reflexivity.
      + rewrite Nat.sub_1_r. simpl pred. simpl length.
        replace (S (length (xs))) with (1 * S (length xs)) at 1 by omega.
        rewrite Nat.mod_add; try omega.
        simpl in H.
        rewrite Nat.mod_small by omega.
        unfold rrot.
        replace (nth (S _) _ _) with (nth i (init (x :: xs)) d) by reflexivity.
        rewrite init_last_destr with (d0 := d) at 2.
        rewrite app_nth1 by (rewrite init_len; simpl; omega).
        reflexivity.
  Qed.
End Nth.

Section Repeats.
  Context {A : Type}.

  Definition lastn (k : nat) (l : list A) : list A :=
    rev (firstn k (rev l)).

  Theorem lastn_all : forall l : list A,
      lastn (length l) l = l.
  Proof.
    intros.
    unfold lastn.
    rewrite <- rev_length.
    rewrite firstn_all.
    apply rev_involutive.
  Qed.

  Theorem lastn_1_app : forall a l,
      lastn 1 (l ++ [a]) = [a].
  Proof.
    induction l.
    - reflexivity.
    - simpl. unfold lastn.
      simpl rev at 2.
      rewrite rev_unit. simpl firstn. reflexivity.
  Qed.

  Theorem lastn_app : forall a l k,
      lastn k l ++ [a] = lastn (S k) (l ++ [a]).
  Proof.
    induction k.
    - simpl. symmetry. apply lastn_1_app.
    - simpl.
      unfold lastn.
      rewrite rev_unit.
      remember (S k) as k'. simpl firstn at 2. subst.
      remember (firstn _ _) as F.
      simpl. reflexivity.
  Qed.

  Lemma firstn_lt : forall k (l l': list A),
      k <= length l -> firstn k l = firstn k (l ++ l').
  Proof.
    intros.
    rewrite firstn_app.
    replace (k - length l) with 0 by omega.
    simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma lastn_lt : forall k (l l': list A),
      k <= length l -> lastn k l = lastn k (l' ++ l).
  Proof.
    intros.
    unfold lastn. f_equal.
    rewrite rev_app_distr.
    apply firstn_lt.
    rewrite rev_length; auto.
  Qed.

  Lemma repeat_lrot_k : forall k (l : list A),
      k <= length l -> rep lrot k l = lastn (length l - k) l ++ firstn k l.
  Proof.
    induction k; intros.
    - simpl. rewrite app_nil_r. rewrite Nat.sub_0_r.
      symmetry. apply lastn_all.
    - destruct l as [|a tl] eqn:HL.
      + apply rep_preserves.
        intros; subst; auto.
        reflexivity.
      + rewrite <- HL at 1 2 3.
        simpl firstn.
        replace (cons a) with (app [a]) by reflexivity.
        replace (lastn (length l - S k) l) with (lastn (length l - S k) tl)
          by (simpl in H; subst; replace (a :: tl) with ([a] ++ tl) by auto;
              apply lastn_lt; rewrite app_length; simpl; omega).
        rewrite app_assoc.
        rewrite lastn_app.
        rewrite <- HL in H.
        replace (S (length l - S k)) with (length l - k) by omega.
        replace (firstn k tl) with (firstn k (lrot l))
          by (subst; symmetry; apply firstn_lt; simpl in H; omega).
        replace (tl ++ [a]) with (lrot l) by (subst; reflexivity).
        replace (length l) with (length (lrot l)) by (symmetry; apply lrot_length).
        rewrite rep_z.
        apply IHk; try (rewrite <- lrot_length; omega).
  Qed.

  Theorem lrot_rep_id : forall (l : list A),
      rep lrot (length l) l = l.
  Proof.
    intros.
    rewrite repeat_lrot_k; auto.
    rewrite firstn_all. rewrite Nat.sub_diag.
    reflexivity.
  Qed.

  Theorem rrot_rep_id : forall (l : list A),
      rep rrot (length l) l = l.
  Proof.
    intros.
    rewrite <- lrot_rep_id at 1.
    replace (length (rep rrot (length l) l)) with (length l)
      by (eapply rep_preserves; [|reflexivity];
          intros x LenEq; rewrite LenEq; apply rrot_length).
    rewrite rep_inv_l; [|apply r_l_rot_inverse|omega].
    rewrite Nat.sub_diag. reflexivity.
  Qed.

  Theorem lrot_rep_pred : forall (l : list A),
      rep lrot (Nat.pred (length l)) l = rrot l.
  Proof.
    intros.
    rewrite <- rep_inv1_l with (g := rrot) by apply l_r_rot_inverse.
    f_equal.
    destruct (length l) eqn:HL.
    - replace l with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
      reflexivity.
    - simpl Nat.pred. rewrite <- HL; clear HL.
      apply lrot_rep_id.
  Qed.

  Theorem rrot_rep_pred : forall (l : list A),
      rep rrot (Nat.pred (length l)) l = lrot l.
  Proof.
    intros.
    rewrite <- rep_inv1_l with (g := lrot) by apply r_l_rot_inverse.
    f_equal.
    destruct (length l) eqn:HL.
    - replace l with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
      reflexivity.
    - simpl Nat.pred. rewrite <- HL; clear HL.
      apply rrot_rep_id.
  Qed.
End Repeats.

Section Injective.
  Context {A : Type}.

  Theorem lrot_injective : forall l l' : list A,
      lrot l = lrot l' -> l = l'.
  Proof.
    intros.
    apply f_equal with (f := rrot) in H.
    do 2 rewrite l_r_rot_inverse in H.
    auto.
  Qed.

  Theorem rrot_injective : forall l l' : list A,
      rrot l = rrot l' -> l = l'.
  Proof.
    intros.
    apply f_equal with (f := lrot) in H.
    do 2 rewrite r_l_rot_inverse in H.
    auto.
  Qed.
End Injective.
