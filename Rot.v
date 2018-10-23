Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.

Import ListNotations.

Section HeadTailInitLast.
  Context {A : Type}.

  (* Drop the last element of a list. *)
  Fixpoint init l : list A :=
    match l with
    | [] | [_] => []
    | hd :: tl => hd :: init tl
    end.

  Lemma last2 : forall (l : list A) (a b d : A),
      last (a :: b :: l) d = last (b :: l) d.
  Proof.
    reflexivity.
  Qed.

  Lemma init2 : forall (l : list A) (a b : A),
      init (a :: b :: l) = a :: init (b :: l).
  Proof.
    reflexivity.
  Qed.

  (* An induction scheme that considers the singleton list as a
     separate case and steps by two elements at a time. *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      P [] ->
      (forall a, P [a]) ->
      (forall a b l, P (b :: l) -> P (a :: b :: l)) ->
      forall l : list A, P l.
  Proof.
    intros P HBase HOne HInd.
    refine (
        fix F l : P l :=
          match l as l' return l = l' -> P l' with
          | []  => fun _ => HBase
          | [x] => fun _ => HOne x
          | a :: tl => fun HL => _
          end eq_refl
      ).
    destruct l. rewrite <- HL. exact HBase.
    inversion HL. apply HInd. rewrite <- H1. apply F.
  Qed.

  Lemma last_app : forall (l: list A) (x d: A),
      last (l ++ [x]) d = x.
  Proof.
    induction l as [| x | a b tl IH] using list_ind2;
      intros; try reflexivity.
    do 2 rewrite <- app_comm_cons.
    rewrite last2.
    apply IH.
  Qed.

  Lemma init_app : forall (x y: list A) a,
      init (x ++ a :: y) = x ++ init (a :: y).
  Proof.
    induction x as [| x | a b tl IH] using list_ind2;
      intros; try reflexivity.
    do 2 rewrite <- app_comm_cons.
    rewrite init2.
    rewrite <- app_comm_cons at 1.
    f_equal.
    apply IH.
  Qed.

  Lemma l_app_nil_inv : forall (a b : A) (l : list A),
      l ++ [b] = [a] -> l = [] /\ a = b.
  Proof.
    destruct l as [|hd tl].
    - split; auto. rewrite app_nil_l in H.
      inversion H; auto.
    - intros contra. inversion contra.
      symmetry in H1. apply app_cons_not_nil in H1. contradiction.
  Qed.

  Lemma last_nonempty : forall (l: list A) w x y z,
      l <> [] -> last (x :: l) w = last (z :: l) y.
  Proof.
    induction l as [| a | a b tl IH] using list_ind2;
      intros; try contradiction; clear H.
    - reflexivity.
    - rewrite last2.
      rewrite last2 with (a := z) at 1.
      apply IH.
      intro contra; inversion contra.
  Qed.

  Lemma hd_tl_destr : forall (x : A) xs d,
      x :: xs = (hd d (x :: xs)) :: (tl (x :: xs)).
  Proof.
    reflexivity.
  Qed.

  Lemma init_last_destr : forall xs x d,
      x :: xs = init (x :: xs) ++ [last (x :: xs) d].
  Proof.
    induction xs; intros.
    - reflexivity.
    - rewrite init2. rewrite <- app_comm_cons.
      f_equal. rewrite last2.
      apply IHxs.
  Qed.

  Lemma tl_len : forall l : list A,
      length (tl l) = Nat.pred (length l).
  Proof.
    induction l; reflexivity.
  Qed.

  Lemma init_len : forall l : list A,
      length (init l) = Nat.pred (length l).
  Proof.
    induction l using list_ind2; intros; try reflexivity.
    rewrite init2.
    replace (length (a :: _)) with (S (length (init (b :: l)))) by reflexivity.
    rewrite IHl. reflexivity.
  Qed.
End HeadTailInitLast.

Section Permutations.
  Context {A : Type} (f : list A -> list A).
  Hypothesis HF: forall l, Permutation l (f l).

  Theorem f_perm : forall (x y : list A),
      Permutation x y -> Permutation x (f y).
  Proof.
    assert (LP: forall l, Permutation (f l) l). {
      intro l. apply Permutation_sym. apply HF.
    }
    intros. inversion H; subst; clear H.
    - apply HF.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply perm_skip. apply Permutation_sym. auto.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      repeat constructor.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply Permutation_sym. eapply perm_trans; eauto.
  Qed.

  Theorem f_perm' : forall (x y : list A),
      Permutation x y -> Permutation (f x) (f y).
  Proof.
    intros.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym. apply H.
  Qed.

  Theorem f_nonempty : forall l,
      l <> [] -> f l <> [].
  Proof.
    intros. intro contra.
    specialize (HF l).
    rewrite contra in HF.
    apply Permutation_sym in HF.
    apply Permutation_nil in HF.
    rewrite HF in H. contradiction.
  Qed.
End Permutations.

Section Rot.
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

  Theorem rrot_reverse : forall (l: list A),
      rrot (rev l) = rev (lrot l).
  Proof.
    destruct l.
    - reflexivity.
    - simpl. rewrite rrot_app.
      unfold lrot. simpl.
      rewrite rev_app_distr.
      reflexivity.
  Qed.

  Theorem lrot_reverse : forall (l: list A),
      lrot (rev l) = rev (rrot l).
  Proof.
    intros.
    rewrite <- rev_involutive at 1.
    rewrite <- rrot_reverse.
    rewrite -> rev_involutive.
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
    rewrite <- rrot_reverse.
    replace (rev (rrot l)) with (lrot (rev l)) by apply lrot_reverse.
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
    rewrite <- lrot_reverse.
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

  Lemma nth_eq : forall l l' : list A,
      length l = length l' ->
      (forall i d, i < length l -> nth i l d = nth i l' d) <-> l = l'.
  Proof.
    induction l; intros l' L.
    - split; intros.
      + symmetry. apply length_zero_iff_nil. auto.
      + subst. reflexivity.
    - split; intros.
      + destruct l'. simpl in L. omega.
      f_equal.
        * apply (H 0 a). simpl; omega.
        * apply IHl; auto.
          intros i d.
          specialize (H (S i) d).
          simpl in H. intro; apply H; omega.
      + rewrite H. reflexivity.
  Qed.

  Lemma nth_first : forall (l : list A) d,
      nth 0 l d = hd d l.
  Proof.
    destruct l; reflexivity.
  Qed.

  Lemma nth_last : forall (l : list A) d,
      nth (Nat.pred (length l)) l d = last l d.
  Proof.
    induction l using list_ind2; intros; try reflexivity.
    replace (last (a :: b :: l)) with (last (b :: l)) by reflexivity.
    replace (length (a :: b :: l)) with (S (length (b :: l))) by reflexivity.
    unfold Nat.pred.
    replace (nth _ _ _)
    with (nth (Nat.pred (length (b ::l))) (b :: l) d) by reflexivity.
    apply IHl.
  Qed.

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
    rewrite <- lrot_reverse.
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
