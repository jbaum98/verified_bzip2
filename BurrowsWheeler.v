Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.

Require Import Rot.
Require Import Prefix.
Require Import Ord.

Import ListNotations.

Theorem Permutation_exists {A : Type} {P : A -> Prop} : forall l l',
    Permutation l l' -> Exists P l -> Exists P l'.
Proof.
  intros l l' HP HE.
  apply Exists_exists.
  apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
  eauto using Permutation_in.
Defined.

Theorem Permutation_forall {A : Type} {P : A -> Prop}: forall x y,
    Permutation x y -> Forall P x -> Forall P y.
Proof.
  intros.
  apply Forall_forall.
  intros a HA.
  apply Permutation_in with (l' := x) in HA; auto using Permutation_sym.
  revert a HA.
  apply Forall_forall.
  auto.
Qed.

Section Repeat.
  Fixpoint repeat_n {A : Type} (f : A -> A) (z : A) (n : nat) : A :=
    match n with
    | O => z
    | S m => repeat_n f (f z) m
    end.

  Theorem repeat_inv {A : Type} (f g : A -> A) (HI: forall x, g (f x) = x) : forall n x,
      g (repeat_n f x (S n)) = repeat_n f x n.
  Proof.
    induction n; intros.
    - simpl. auto.
    - remember (S n) as n'. simpl. subst.
      apply IHn.
  Qed.

  Theorem repeat_n_preserves {A : Type} : forall f z n (P: A -> Prop),
      (forall x, P x -> P (f x)) -> P z -> P (repeat_n f z n).
  Proof.
    intros f z n P Preserve Pz. revert z Pz.
    induction n.
    - auto.
    - simpl. auto.
  Qed.

  Lemma repeat_lrot_len {A : Type} : forall (l : list A) n,
      length (repeat_n lrot l n) = length l.
  Proof.
    intros.
    apply repeat_n_preserves; auto.
    intros. rewrite <- H.
    symmetry. apply lrot_length.
  Qed.

  Definition lastn {A : Type} (k : nat) (l : list A) : list A :=
    rev (firstn k (rev l)).

  Theorem lastn_all {A : Type} : forall l : list A,
      lastn (length l) l = l.
  Proof.
    intros.
    unfold lastn.
    rewrite <- rev_length.
    rewrite firstn_all.
    apply rev_involutive.
  Qed.

  Theorem lastn_1_app {A : Type} : forall (a : A) l,
      lastn 1 (l ++ [a]) = [a].
  Proof.
    induction l.
    - reflexivity.
    - simpl. unfold lastn.
      simpl rev at 2.
      rewrite rev_unit. simpl firstn. reflexivity.
  Qed.

  Theorem lastn_app {A : Type} : forall (a : A) l k,
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

  Lemma firstn_lt {A : Type} : forall k (l l': list A),
      k <= length l -> firstn k l = firstn k (l ++ l').
  Proof.
    intros.
    rewrite firstn_app.
    replace (k - length l) with 0 by omega.
    simpl. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma lastn_lt {A : Type} : forall k (l l': list A),
      k <= length l -> lastn k l = lastn k (l' ++ l).
  Proof.
    intros.
    unfold lastn.
    f_equal.
    rewrite rev_app_distr.
    apply firstn_lt.
    rewrite rev_length; auto.
  Qed.

  Lemma repeat_lrot_k {A : Type} : forall k (l : list A),
      k <= length l -> repeat_n lrot l k = lastn (length l - k) l ++ firstn k l.
  Proof.
    induction k; intros.
    - simpl. rewrite app_nil_r. rewrite Nat.sub_0_r.
      symmetry. apply lastn_all.
    - simpl repeat_n.
      destruct l as [|a tl] eqn:HL.
      + simpl.
        apply repeat_n_preserves.
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
        apply IHk; try (rewrite <- lrot_length; omega).
  Qed.

  Theorem lrot_l_id {A : Type} : forall (l : list A),
      repeat_n lrot l (length l) = l.
  Proof.
    intros.
    rewrite repeat_lrot_k; auto.
    rewrite firstn_all. rewrite Nat.sub_diag.
    reflexivity.
  Qed.

  Theorem lrot_pred_l_rrot {A : Type} : forall (l : list A),
      repeat_n lrot l (Nat.pred (length l)) = rrot l.
  Proof.
    intros.
    rewrite <- repeat_inv with (g := rrot) by apply l_r_rot_inverse.
    f_equal.
    destruct (length l) eqn:HL.
    - replace l with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
      reflexivity.
    - simpl Nat.pred. rewrite <- HL; clear HL.
      apply lrot_l_id.
  Qed.
End Repeat.

Section Iterate.
  Context {A : Type}.

  Fixpoint iterate_n (f : A -> A) (z : A) (n : nat) : list A :=
    match n with
    | O   => [z]
    | S m => z :: iterate_n f (f z) m
    end.

  Theorem iterate_n_preserves : forall f n z (P: A -> Prop),
      (forall x, P x -> P (f x)) -> P z -> Forall P (iterate_n f z n).
  Proof.
    intros f n z P HPreserve Pz. revert z Pz.
    induction n.
    - constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Theorem iterate_n_nth : forall f n z i d,
      i <= n -> nth i (iterate_n f z n) d = repeat_n f z i.
  Proof.
    intros f n z i. revert f n z.
    induction i; intros.
    - destruct n.
      + reflexivity.
      + reflexivity.
    - destruct n; try omega.
      simpl. apply IHi. omega.
  Qed.

  Theorem iterate_n_len : forall f n z,
      length (iterate_n f z n) = S n.
  Proof.
    induction n; intros.
    - simpl. reflexivity.
    - simpl. f_equal. apply IHn.
  Qed.
End Iterate.

Section Rots.
  Context {A : Type}.

  Definition rots (l : list A) : list (list A) :=
    iterate_n lrot l (Nat.pred (length l)).

  Lemma rots_destr : forall (l : list A),
      exists r, rots l = l :: r.
  Proof.
    intros.
    unfold rots.
    destruct l as [| a [| b tl]].
    - simpl. exists nil. auto.
    - simpl. eexists. f_equal.
    - simpl. eexists. f_equal.
  Defined.

  Lemma orig_in_rots `{EqDec (list A)}: forall l,
      Exists (equiv l) (rots l).
  Proof.
    intros. simpl.
    destruct (rots_destr l).
    rewrite H0.
    apply Exists_cons_hd. apply equiv_reflexive.
  Defined.

  Lemma rots_len : forall l,
      Forall (fun x => length x = length l) (rots l).
  Proof.
    intros. apply iterate_n_preserves; auto.
    intros. eapply eq_trans. symmetry. apply lrot_length. auto.
  Qed.

  Theorem rrot_rots : forall l,
      map rrot (rots l) = rrot (rots l).
  Proof.
    intros l.
    unfold rots.
    apply nth_eq. { rewrite map_length, rrot_length; reflexivity. }
    intros.
    rewrite nth_indep with (d' := rrot d), map_nth by auto.
    rewrite map_length, iterate_n_len in H.
    rewrite iterate_n_nth by omega.
    rewrite nth_rrot by (rewrite iterate_n_len; omega).
    rewrite iterate_n_nth.
    rewrite iterate_n_len.
    destruct i.
    - unfold Nat.add. clear H.
      rewrite Nat.mod_small by omega. simpl. rewrite Nat.sub_0_r.
      symmetry; apply lrot_pred_l_rrot.
    - replace ((S i + S _) - 1) with (i + 1 * S (Nat.pred (length l))) by omega.
      rewrite Nat.mod_add by omega.
      rewrite Nat.mod_small by omega.
      apply repeat_inv. apply l_r_rot_inverse.
    - rewrite iterate_n_len.
      destruct i.
      + simpl Nat.add.
        eapply Nat.le_trans.
        apply Nat.mod_le; try omega.
        omega.
      + replace (S i + S _ - 1) with (i + 1 * S (Nat.pred (length l))) by omega.
        rewrite Nat.mod_add by omega.
        rewrite Nat.mod_small by omega.
        omega.
  Qed.
End Rots.

Section Lexsort.
  Context {A : Type} `{TotalOrderDec A}.

  Definition lexsort (ls : list (list A)) : list (list A) :=
    match ls with
    | [] => []
    | hd :: tl => sort (length hd) ls
    end.

  Remark lexsort_rots : forall l,
      lexsort (rots l) = sort (length l) (rots l).
  Proof.
    intros. unfold lexsort.
    destruct (rots_destr l). rewrite -> H0. reflexivity.
  Qed.

  Lemma orig_in_sorted_rots : forall l k,
      Exists (@equiv _ _ (Equivalence_list_k k) l) (sort k (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
    apply sort_perm.
    apply (@orig_in_rots _ _ _ (EqDec_list_k k) l).
  Defined.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply sort_perm. apply rots_len.
  Qed.
End Lexsort.

Section FindIndex.
  Context {A : Type} `{EqDec A}.

  Fixpoint findIndex (x : A) (ls : list A) : nat :=
    match ls with
    | [] => 0
    | hd :: tl =>
      match x == hd with
      | left _ => 0
      | right Neq => S (findIndex x tl)
      end
    end.

  Theorem findIndex_correct : forall x xs d,
      Exists (equiv x) xs -> nth (findIndex x xs) xs d === x.
  Proof.
    intros x xs d E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + apply IHE.
  Qed.

  Theorem findIndex_bounds : forall x xs,
      Exists (equiv x) xs -> findIndex x xs < length xs.
  Proof.
    intros x xs E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + simpl. apply le_n_S. apply IHE.
  Qed.
End FindIndex.

Section Transform.
  Context {A : Type} `{O: TotalOrderDec A}.

  Definition bwp (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => List.map (fun x => last x hd) (lexsort (rots l))
    end.

  Definition bwn (l : list A) : nat :=
    @findIndex _ _ _ (EqDec_list_k (length l)) l (lexsort (rots l)).

  Theorem bwn_correct : forall xs d,
      Forall2 equiv (nth (bwn xs) (lexsort (rots xs)) d) xs.
  Proof.
    intros.
    unfold bwn.
    rewrite <- firstn_all.
    rewrite <- firstn_all at 1.
    replace (length (nth _ _ _)) with (length xs).
    - apply eq_k_firstn.
      apply findIndex_correct.
      rewrite lexsort_rots.
      apply orig_in_sorted_rots.
    - assert (L: forall x, In x (lexsort (rots xs)) -> (fun x => length x = length xs) x). {
        apply Forall_forall.
        rewrite lexsort_rots.
        apply sort_rots_len.
      }
      symmetry; apply L.
      apply nth_In. apply findIndex_bounds.
      rewrite lexsort_rots. apply orig_in_sorted_rots.
  Qed.
End Transform.

Lemma Forall2_eq {A : Type} : forall x y : list A,
    Forall2 eq x y <-> x = y.
Proof.
  split; intros.
  - induction H.
    + reflexivity.
    + subst. f_equal.
  - subst. induction y; constructor; auto.
Qed.

Section Transform_Eq.
  Context {A: Type} `{TotalOrderDec A eq} .

  Theorem bwn_correct' : forall xs d,
    nth (bwn xs) (lexsort (rots xs)) d = xs.
  Proof.
    intros.
    apply Forall2_eq.
    apply bwn_correct.
  Qed.
End Transform_Eq.
