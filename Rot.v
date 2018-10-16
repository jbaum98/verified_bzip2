Require Import List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

Section Rot.

  Open Scope program_scope.

  Context {A : Type}.

  Fixpoint init l : list A :=
    match l with
    | [] | [_] => []
    | hd :: tl => hd :: init tl
    end.

  Definition rrot (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => last l hd :: init l
    end.

  Definition lrot (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => tl ++ [hd]
    end.

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

  Theorem f_perm (f : list A -> list A) (HF: forall l, Permutation l (f l)) :
    forall (x y : list A), Permutation x y -> Permutation x (f y).
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

  Theorem f_perm' (f : list A -> list A) (HF: forall l, Permutation l (f l)) :
    forall (x y : list A), Permutation x y -> Permutation (f x) (f y).
  Proof.
    intros.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym. apply H.
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

  Theorem f_nonempty (f : list A -> list A) (HF: forall l, Permutation l (f l)):
    forall l, l <> [] -> f l <> [].
  Proof.
    intros. intro contra.
    specialize (HF l).
    rewrite contra in HF.
    apply Permutation_sym in HF.
    apply Permutation_nil in HF.
    rewrite HF in H. contradiction.
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
