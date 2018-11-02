Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Rotation.
Require Import Prefix.
Require Import Ord.
Require Import Repeat.
Require Import Rots.

Import ListNotations.

Open Scope program_scope.

Lemma eq_map {A B : Type} (f g : A -> B) l :
  (forall x, f x = g x) -> map f l = map g l.
Proof.
  intros HExt; induction l; try reflexivity.
  simpl; rewrite HExt, IHl.
  reflexivity.
Qed.

Lemma map_map' {A B C : Type} : forall (f : A -> B) (g : B -> C) l,
    map g (map f l) = map (g ∘ f) l.
Proof.
  intros.
  rewrite map_map. apply eq_map.
  reflexivity.
Qed.

Lemma Forall2_eq {A : Type} : forall x y : list A,
    Forall2 eq x y <-> x = y.
Proof.
  split; intros.
  - induction H.
    + reflexivity.
    + subst. f_equal.
  - subst. induction y; constructor; auto.
Qed.

Lemma Forall2_map {A B : Type} (R : B -> B -> Prop) : forall (f : A -> B) (l l' : list A),
    length l = length l' ->
    Forall2 R (map f l) (map f l') <-> Forall2 (fun x y => R (f x) (f y)) l l'.
Proof.
  induction l; intros.
  - simpl in H.
    replace l' with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
    split; constructor.
  - destruct l' as [|a' l']; [inversion H|].
    simpl; split; intros HImp; inversion HImp; subst; clear HImp; constructor; auto.
    + apply IHl; auto.
    + apply IHl; auto.
Qed.

Lemma Forall2_impl : forall (A B : Type) (P Q : A -> B -> Prop),
    (forall a b, P a b -> Q a b) -> forall l l', Forall2 P l l' -> Forall2 Q l l'.
Proof.
  intros. induction H0; constructor; auto.
Qed.

Lemma map_injective {A B : Type} : forall (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' -> l = l'.
Proof.
  intros f l l' HInj MapEq.
  assert (length l = length l'). {
    rewrite <- map_length with (f := f), MapEq, -> map_length.
    easy.
  }
  assert (Forall2 (fun x y => f x = f y) l l'). {
    apply Forall2_eq in MapEq.
    apply (proj1 (Forall2_map eq f l l' H)) in MapEq.
    apply MapEq.
  }
  apply Forall2_eq.
  eapply Forall2_impl; [| apply H0].
  cbv beta; intros. auto.
Qed.

Lemma map_forall_eq {A B : Type} : forall (l : list A) (f g : A -> B),
    Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
  induction l; intros.
  - reflexivity.
  - inversion H; subst; clear H.
    simpl. f_equal; auto.
Qed.

Section Permutations.
  Context {A : Type} {P : A -> Prop} .
  Variables l l' : list A.
  Hypothesis HP : Permutation l l'.

  Theorem Permutation_exists :
    Exists P l -> Exists P l'.
  Proof.
    intros HE.
    apply Exists_exists.
    apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
    eauto using Permutation_in.
  Defined.

  Theorem Permutation_forall :
    Forall P l -> Forall P l'.
  Proof.
    intros.
    apply Forall_forall.
    intros a HA.
    apply Permutation_in with (l' := l) in HA; auto using Permutation_sym.
    revert a HA.
    apply Forall_forall.
    auto.
  Qed.
End Permutations.

Section SortRotations.
  Context {A : Type} `{TotalOrderDec A}.

  Theorem sort_rrot_k : forall k l,
    sort k (map (rep rrot k) l)= rep (sort 1 ∘ map rrot) k l.
  Proof.
  Admitted.

  Lemma sort_succ_rrot : forall k l,
      sort (S k) (map rrot l) = sort 1 (map rrot (sort k l)).
  Proof.
    intros.
    pose proof (sort_rrot_k (S k)) as E6.
    simpl rep at 2 in E6.
    specialize E6 with (l := map (rep lrot k) l).
    rewrite <- sort_rrot_k in E6.
    pose proof rep_inv_r (@lrot A) rrot l_r_rot_inverse as rep_inv.
    do 2 rewrite map_map' in E6.
    rewrite eq_map with (f := rep rrot (S k) ∘ rep lrot k) (g := rrot) in E6
      by (intros; unfold compose; rewrite rep_inv by omega;
          rewrite Nat.sub_succ_l, Nat.sub_diag; [reflexivity|omega]).
    rewrite eq_map with (f := rep rrot k ∘ rep lrot k) (g := id)in E6
      by (intros; unfold compose; rewrite rep_inv by omega;
          rewrite Nat.sub_diag; reflexivity).
    rewrite map_id in E6.
    unfold compose in E6.
    apply E6.
  Qed.
End SortRotations.

Section Cols.
  Context {A : Type}.

  Definition cols j := map (@firstn A j).

  Context `{TotalOrderDec A}.

  Theorem cols_sort1 : forall k j l,
      cols j (sort k l) = cols j (sort (Nat.min j k) l).
  Admitted.

  Theorem cols_sort2 : forall k j l,
      cols j (sort k l) = sort (Nat.min j k) (cols j l).
  Admitted.

  Lemma cols_sort_lt : forall k j l,
      j <= k -> cols j (sort k l) = sort j (cols j l).
  Proof.
    intros.
    replace j with (Nat.min j k) at 2 by (apply Min.min_l; auto).
    apply cols_sort2.
  Qed.

  Theorem cols_sort_perm : forall k j p l,
      (forall l, Permutation l (p l)) -> cols j (sort k (p l)) = cols j (sort k l).
  Admitted.

  Theorem cols_sort_shift : forall k j l,
      1 <= j <= k ->
      cols j (sort k (rots l)) = sort 1 (cols j (map rrot (sort k (rots l)))).
  Proof.
    intros.
    replace 1 with (Nat.min j 1) by (apply Min.min_r; omega).
    rewrite <- cols_sort2, <- sort_succ_rrot, map_rrot_rots, cols_sort2.
    rewrite cols_sort_perm by apply rrot_perm.
    rewrite cols_sort2.
    replace (Nat.min j (S k)) with (Nat.min j k) by (rewrite ?Nat.min_l; omega).
    reflexivity.
  Qed.

  Theorem cols_id : forall n mat,
      Forall (fun x => length x <= n) mat ->
      cols n mat = mat.
  Proof.
    induction n; intros mat HL.
    - unfold cols. unfold firstn.
      rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      simpl; intros.
      assert (length a = 0) by omega.
      symmetry. apply length_zero_iff_nil; auto.
    - unfold cols. rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      cbv beta. intros.
      apply firstn_all2; auto.
  Qed.
End Cols.

Section Lexsort.
  Context {A : Type} `{TotalOrderDec A}.

  Lemma orig_in_sorted_rots : forall l k,
      l <> [] -> Exists (@equiv _ _ (Equivalence_list_k k) l) (sort k (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
    apply sort_perm.
    apply (@orig_in_rots _ _ _ (EqDec_list_k k) l); auto.
  Defined.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply sort_perm. apply rots_row_length.
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
    | hd :: tl => List.map (fun x => last x hd) (sort (length l) (rots l))
    end.

  Theorem bwp_nonempty : forall l,
      l <> [] ->
      forall d, bwp l = List.map (fun x => last x d) (sort (length l) (rots l)).
  Proof.
    destruct l; intros.
    - contradiction.
    - apply map_forall_eq.
      apply Forall_forall.
      intros.
      assert (x <> []). {
        apply (Forall_forall (fun x => ~ x = []) (sort (length (a :: l)) (rots (a :: l)))); auto.
        eapply Permutation_forall. apply sort_perm.
        apply rots_nonempty; auto.
      }
      apply last_nonempty; auto.
  Qed.

  Theorem bwp_length : forall l,
      length (bwp l) = length l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. rewrite map_length.
      rewrite sort_length.
      rewrite rots_length.
      reflexivity.
  Qed.

  Definition bwn (l : list A) : nat :=
    @findIndex _ _ _ (EqDec_list_k (length l)) l (sort (length l) (rots l)).

  Theorem bwn_correct : forall xs d,
      xs <> [] -> Forall2 equiv (nth (bwn xs) (sort (length xs) (rots xs)) d) xs.
  Proof.
    intros.
    unfold bwn.
    rewrite <- firstn_all.
    rewrite <- firstn_all at 1.
    replace (length (nth _ _ _)) with (length xs).
    - apply eq_k_firstn.
      apply findIndex_correct.
      apply orig_in_sorted_rots; auto.
    - assert (L: forall x, In x (sort (length xs) (rots xs)) -> (fun x => length x = length xs) x). {
        apply Forall_forall.
        apply sort_rots_len.
      }
      symmetry; apply L.
      apply nth_In. apply findIndex_bounds.
      apply orig_in_sorted_rots; auto.
  Qed.
End Transform.

Section Transform_Eq.
  Context {A: Type} `{TotalOrderDec A eq} .

  Theorem bwn_correct' : forall xs d,
    xs <> [] -> nth (bwn xs) (sort (length xs) (rots xs)) d = xs.
  Proof.
    intros.
    apply Forall2_eq.
    apply bwn_correct.
    auto.
  Qed.
End Transform_Eq.

Section PrependColumn.
  Context {A : Type}.

  Fixpoint prepend_col (col : list A) (mat : list (list A)) :=
    match (col, mat) with
    | (hd :: tl, row :: rows) => (hd :: row) :: prepend_col tl rows
    | _ => mat
    end.

  Lemma cols_rrot : forall j l d,
      cols (S j) (map rrot l) = prepend_col (map (fun x => last x d) l) (cols j l).
  Admitted.

  Theorem recreate_inspiration `{TotalOrderDec A} : forall j l,
      j < length l ->
      cols (S j) (sort (length l) (rots l)) =
      sort 1 (prepend_col (bwp l) (cols j (sort (length l) (rots l)))).
  Proof.
    intros. destruct l eqn:HL; [reflexivity|].
    rewrite <- HL in *. assert (l <> []) by (intro c; subst; inversion c).
    rewrite cols_sort_shift by omega.
    rewrite cols_rrot with (d := a).
    rewrite <- bwp_nonempty with (d := a) by auto.
    reflexivity.
  Qed.
End PrependColumn.

Lemma map_const {A B} : forall (f : A -> B) l c,
    (forall x, f x = c) -> map f l = repeat c (length l).
Proof.
  intros.
  induction l; [reflexivity|].
  simpl. rewrite H. f_equal. auto.
Qed.

Section Recreate.
  Context {A : Type} `{TotalOrderDec A eq}.

  Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
    match j with
    | O    => map (const []) l
    | S j' => sort 1 (prepend_col l (recreate j' l))
    end.

  Lemma recreate_correct_gen : forall j l,
      j <= length l ->
      recreate j (bwp l) = cols j (sort (length l) (rots l)).
  Proof.
    induction j; intros.
    - unfold cols. simpl.
      do 2 (erewrite map_const; [|unfold const; reflexivity]).
      rewrite bwp_length, sort_length, rots_length.
      reflexivity.
    - simpl.
      rewrite recreate_inspiration by omega.
      rewrite IHj by omega.
      reflexivity.
  Qed.

  Theorem recreate_correct : forall l,
      recreate (length l) (bwp l) = sort (length l) (rots l).
  Proof.
    intros.
    rewrite recreate_correct_gen by omega.
    rewrite cols_id; auto.
    eapply Forall_impl; [|apply sort_rots_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{TotalOrderDec A eq}.

  Definition unbwt (t : nat) (l : list A) : list A :=
    nth t (recreate (length l) l) l.

  Theorem unbwt_correct : forall xs,
      unbwt (bwn xs) (bwp xs) = xs.
  Proof.
    intros [|a xs]; [reflexivity|].
    unfold unbwt.
    rewrite bwp_length.
    rewrite recreate_correct.
    apply bwn_correct'.
    intro contra; inversion contra.
  Qed.
End Unbwt.
