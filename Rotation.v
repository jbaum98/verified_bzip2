Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.

Require Import Repeat.
Require Import BWTactics.

Import ListNotations.

Local Definition last {A} d l := @List.last A l d.
Arguments last /.

(* Automatically use A as type argument to rev *)
Local Definition rev {A} := @rev A.
Arguments rev /.

Local Theorem rev_involutive {A} :
  rev ∘ rev = @id (list A).
Proof. extensionality l. apply List.rev_involutive. Qed.

Local Definition nth {A} i d l := @List.nth A i l d.

Section HeadTailInitLast.
  Context {A : Type}.

  (* Drop the last element of a list. *)
  Fixpoint init l : list A :=
    match l with
    | [] | [_] => []
    | hd :: tl => hd :: init tl
    end.

  Lemma last2 : forall (l : list A) (a b d : A),
      last d (a :: b :: l) = last d (b :: l).
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
      last d (l ++ [x]) = x.
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

  Lemma last_nonempty : forall (l: list A) d d',
      l <> [] -> last d l = last d' l.
  Proof.
    induction l as [| a | a b tl IH] using list_ind2;
      intros; try contradiction; clear H.
    - reflexivity.
    - do 2 rewrite last2.
      apply IH.
      intro contra; inversion contra.
  Qed.

  Lemma hd_tl_destr : forall (x : A) xs d,
      x :: xs = (hd d (x :: xs)) :: (tl (x :: xs)).
  Proof.
    reflexivity.
  Qed.

  Lemma init_last_destr : forall xs x d,
      x :: xs = init (x :: xs) ++ [last d (x :: xs)].
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
    | hd :: tl => last hd l :: init l
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

  Theorem rrot_rev :
    rrot ∘ rev = rev ∘ lrot.
  Proof.
    extensionality l.
    destruct l.
    - reflexivity.
    - unfold compose. cbn.
      rewrite rrot_app.
      unfold lrot. simpl.
      rewrite rev_app_distr.
      reflexivity.
  Qed.

  Theorem lrot_rev :
      lrot ∘ rev = rev ∘ rrot.
  Proof.
    intros.
    crewrite <- rev_involutive.
    crewrite <- rrot_rev.
    crewrite -> rev_involutive.
    reflexivity.
  Qed.

  Theorem l_r_rot_inverse : rrot ∘ lrot = id.
  Proof.
    extensionality l.
    destruct l.
    - reflexivity.
    - simpl. apply rrot_app.
  Qed.

  Theorem r_l_rot_inverse : lrot ∘ rrot = id.
  Proof.
    extensionality l.
    crewrite <- rev_involutive.
    crewrite <- rrot_rev.
    remember (rev ∘ rrot) as f.
    crewrite <- lrot_rev. subst.
    crewrite l_r_rot_inverse.
    crewrite compose_id_left.
    unfold compose. xrewrite rev_involutive. easy.
  Qed.

  Theorem lrot_perm : forall (l : list A),
      Permutation l (lrot l).
  Proof.
    destruct l as [|hd tl].
    - apply perm_nil.
    - simpl.
      rewrite <- List.rev_involutive.
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
    replace rrot with (id ∘ rrot) by apply compose_id_left.
    crewrite <- rev_involutive.
    crewrite <- lrot_rev.
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
      (forall i d, i < length l -> nth i d l = nth i d l') <-> l = l'.
  Proof.
    induction l; intros l' L.
    - split; intros.
      + symmetry. apply length_zero_iff_nil. auto.
      + subst. reflexivity.
    - split; intros.
      + destruct l'. simpl in L. omega.
      f_equal.
        * apply (H 0 a). cbn. omega.
        * apply IHl; auto.
          intros i.
          intros.
          eapply (H (S i)). cbn. omega.
      + rewrite H. reflexivity.
  Qed.

  Lemma nth_first : forall d : A,
      nth 0 d = hd d.
  Proof.
    intros. extensionality l. destruct l; reflexivity.
  Qed.

  Lemma nth_last : forall (l : list A) d,
      nth (Nat.pred (length l)) d l = last d l.
  Proof.
    induction l using list_ind2; intros; try reflexivity.
    replace (last d (a :: b :: l)) with (last d (b :: l)) by reflexivity.
    replace (length (a :: b :: l)) with (S (length (b :: l))) by reflexivity.
    unfold Nat.pred.
    replace (nth _ _ _)
    with (nth (Nat.pred (length (b ::l))) d (b :: l)) by reflexivity.
    apply IHl.
  Qed.

  Lemma nth_lrot : forall (l : list A) i n d,
      n = length l -> i < n ->
      (nth i d ∘ lrot) l = nth ((i + 1) mod n) d l.
  Proof.
    destruct l as [|x xs]; intros i n d Hn H.
    - simpl lrot.
      unfold nth.
      rewrite ?nth_overflow by (simpl; omega). destruct i; easy.
    - destruct (Nat.eq_dec i (Nat.pred (length (x :: xs)))).
      + subst i; clear H; rewrite <- Hn.

        unfold compose at 1; rewrite Hn at 1;
        replace (length (x :: xs)) with (length (lrot (x :: xs))) at 1
          by (symmetry; apply lrot_length);
        rewrite nth_last.

        simpl length; simpl Nat.pred; rewrite Nat.add_1_r.
        simpl in Hn. rewrite Nat.succ_pred_pos, Nat.mod_same by omega.
        rewrite nth_first. apply last_app.

      + cbn in Hn, n0. assert (i < length xs) by omega; clear H n0.
        rewrite Nat.mod_small by (simpl; omega).
        rewrite Nat.add_1_r. simpl nth.
        apply app_nth1; auto.
  Qed.

  Lemma hd_last_rev : forall d : A,
      hd d = last d ∘ rev.
  Proof.
    intros.
    extensionality l; induction l.
    - reflexivity.
    - unfold compose, hd, rev. simpl List.rev.
      rewrite last_app. reflexivity.
  Qed.

  Lemma hd_rev_last : forall d : A,
      hd d ∘ rev = last d.
  Proof.
    intros.
    crewrite hd_last_rev.
    crewrite rev_involutive.
    reflexivity.
  Qed.

  Lemma last_lrot : forall d : A,
      last d ∘ lrot = hd d.
  Proof.
    intros; extensionality l.
    destruct l; intros.
    - reflexivity.
    - unfold compose, lrot. apply last_app.
  Qed.

  Lemma hd_rrot : forall d : A,
      hd d ∘ rrot = last d.
  Proof.
    intros.
    crewrite hd_last_rev.
    crewrite <- lrot_rev.
    crewrite last_lrot.
    crewrite hd_rev_last.
    reflexivity.
  Qed.

  Lemma nth_cons : forall (l : list A) x i d,
      nth (S i) d (x :: l) = nth i d l.
  Proof. reflexivity. Qed.

  Lemma nth_rrot : forall (l : list A) i n d,
      n = length l -> i < length l ->
      (nth i d ∘ rrot) l = nth ((i + n - 1) mod n) d l.
  Proof.
    destruct l as [|x xs]; intros.
    - unfold compose; simpl rrot; simpl nth at 1.
      unfold nth; rewrite !nth_overflow by (simpl; omega).
      destruct i; easy.
    - destruct i.
      + simpl rrot. crewrite nth_first.
        rewrite Nat.add_0_l, Nat.mod_small, Nat.sub_1_r by omega.
        rewrite H, nth_last.
        rewrite hd_rrot.
        reflexivity.
      + rewrite Nat.sub_1_r; simpl pred; simpl length.
        rewrite <- (Nat.mul_1_l n) at 1; rewrite Nat.mod_add by omega.
        simpl in H, H0; rewrite Nat.mod_small by omega.
        unfold compose, rrot.
        rewrite nth_cons.
        rewrite init_last_destr with (d0 := x) at 2.
        unfold nth at 2; rewrite app_nth1 by (rewrite init_len; simpl; omega).
        reflexivity.
  Qed.
End Nth.

Section Repeats.
  Context {A : Type}.

  Definition lastn (k : nat) : list A -> list A :=
    rev ∘ firstn k ∘ rev.

  Theorem lastn_all : forall l : list A,
      lastn (length l) l = l.
  Proof.
    intros.
    unfold lastn.
    rewrite <- rev_length.
    unfold compose. rewrite firstn_all.
    xrewrite rev_involutive.
    easy.
  Qed.

  Theorem lastn_1_app : forall a l,
      lastn 1 (l ++ [a]) = [a].
  Proof.
    induction l.
    - reflexivity.
    - simpl. unfold lastn, compose.
      simpl rev at 2.
      rewrite rev_unit. simpl firstn. reflexivity.
  Qed.

  Theorem lastn_app : forall a l k,
      lastn k l ++ [a] = lastn (S k) (l ++ [a]).
  Proof.
    induction k.
    - simpl. symmetry. apply lastn_1_app.
    - simpl.
      unfold lastn, compose.
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
    unfold lastn, compose. f_equal.
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
    compose_var l.
    crewrite (rep_inv_l); [|apply r_l_rot_inverse|omega].
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
      unfold compose. rewrite lrot_rep_id.
      easy.
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
      unfold compose. rewrite rrot_rep_id.
      easy.
  Qed.
End Repeats.

Section Injective.
  Context {A : Type}.

  Theorem lrot_injective : forall l l' : list A,
      lrot l = lrot l' -> l = l'.
  Proof.
    intros.
    xrewrite <- l_r_rot_inverse with l.
    xrewrite <- l_r_rot_inverse with l'.
    f_equal. auto.
  Qed.

  Theorem rrot_injective : forall l l' : list A,
      rrot l = rrot l' -> l = l'.
  Proof.
    intros.
    xrewrite <- r_l_rot_inverse with l.
    xrewrite <- r_l_rot_inverse with l'.
    f_equal. auto.
  Qed.
End Injective.
