Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

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
End Cols.

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
