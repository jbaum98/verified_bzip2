Require Import List.
Import ListNotations.

Require Import VST.floyd.sublist.

Section Rot.

  Open Scope program_scope.

  Variable A : Type.

  Fixpoint init l : list A :=
    match l with
    | [] | [_] => []
    | hd :: tl => hd :: init tl
    end.

  Definition rrot `{Inhabitant A} (l: list A) : list A :=
    match l with
    | [] => []
    | _ => last l default :: init l
    end.

  Definition lrot (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => tl ++ [hd]
    end.

  Lemma last_app : forall (l: list A) (x d: A),
      last (l ++ [x]) d = x.
  Proof.
    induction l.
    - reflexivity.
    - intros. simpl.
      remember (l ++ [x]) as v. destruct v.
      + exfalso. revert Heqv. apply app_cons_not_nil.
      + rewrite Heqv. apply IHl.
  Qed.

  Lemma init_app : forall (x y: list A) a,
      init (x ++ a :: y) = x ++ init (a :: y).
  Proof.
    induction x.
    - reflexivity.
    - intros.
      rewrite <- app_comm_cons.
      remember (x ++ a0 :: y) as l.
      destruct l.
      + exfalso. revert Heql. apply app_cons_not_nil.
      + replace (init (a :: a1 :: l)) with (a :: init (a1 :: l)) by reflexivity.
        rewrite <- app_comm_cons.
        f_equal.
        rewrite Heql; clear Heql.
        apply IHx.
  Qed.

  Lemma rrot_app `{Inhabitant A}: forall (l: list A) a,
      rrot (l ++ [a]) = a :: l.
  Proof.
    intros.
    destruct (l ++ [a]) eqn:contra.
    - exfalso. symmetry in contra. revert contra. apply app_cons_not_nil.
    - unfold rrot.
      rewrite <- contra. clear contra.
      rewrite last_app.
      rewrite init_app.
      simpl.
      rewrite app_nil_r.
      reflexivity.
  Qed.

  Lemma last_nonempty : forall (l: list A) w x y z,
      l <> [] -> last (x :: l) w = last (z :: l) y.
  Proof.
    induction l.
    - contradiction.
    - intros. destruct l.
      + reflexivity.
      + replace (last (x :: a :: a0 :: l) w) with (last (a :: a0 :: l) w) by reflexivity.
        replace (last (z :: a :: a0 :: l) y) with (last (a :: a0 :: l) y) by reflexivity.
      apply IHl.
      intro contra. inversion contra.
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

  Theorem rrot_reverse `{Inhabitant A} : forall (l: list A),
      rrot (rev l) = rev (lrot l).
  Proof.
    destruct l.
    - reflexivity.
    - simpl. rewrite rrot_app.
      unfold lrot. simpl.
      rewrite rev_app_distr.
      reflexivity.
  Qed.

  Theorem lrot_reverse `{Inhabitant A} : forall (l: list A),
      lrot (rev l) = rev (rrot l).
  Proof.
    intros.
    rewrite <- rev_involutive at 1.
    rewrite <- rrot_reverse.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Theorem l_r_rot_inverse `{Inhabitant A}: forall (l: list A),
      rrot (lrot l) = l.
  Proof.
    destruct l.
    - reflexivity.
    - simpl. apply rrot_app.
  Qed.

  Theorem r_l_rot_inverse `{Inhabitant A}: forall (l: list A),
      lrot (rrot l) = l.
  Proof.
    intro l.
    rewrite <- rev_involutive at 1.
    rewrite <- rrot_reverse.
    replace (rev (rrot l)) with (lrot (rev l)) by apply lrot_reverse.
    rewrite l_r_rot_inverse.
    apply rev_involutive.
  Qed.
End Rot.

Arguments lrot [_] _.
Arguments rrot [_] [_] _.
