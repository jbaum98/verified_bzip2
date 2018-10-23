Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Recdef.
Require Import Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import ConstructiveEpsilon.
Require Import Coq.Sorting.Permutation.

Require Import Rot.
Require Import Prefix.
Require Import Ord.

Section BW.

Open Scope program_scope.

Fixpoint iterate_n {A : Type} (f : A -> A) (n : nat) (x : A) : list A :=
  match n with
  | O   => [x]
  | S m => x :: iterate_n f m (f x)
  end.

Definition rots {A : Type} (l : list A) : list (list A) :=
  iterate_n lrot (Nat.pred (length l)) l.

Definition lexsort {A : Type} `{TotalOrderDec A} (ls : list (list A)) : list (list A) :=
  match ls with
  | [] => []
  | hd :: tl => sort (length hd) ls
  end.

Theorem iterate_n_preserves {A: Type}: forall f n (z: A) (P: A -> Prop),
    P z -> (forall x, P x -> P (f x)) -> P z -> Forall P (iterate_n f n z).
Proof.
  intros f n z P Hz HPreserve Pz. revert z Hz Pz.
  induction n.
  - constructor; auto.
  - simpl. constructor; auto.
Qed.

Definition bwp {A: Type} `{TotalOrderDec A} (l: list A) : list A :=
  match l with
  | [] => []
  | hd :: tl => (List.map (fun x => last x hd) ∘ lexsort ∘ rots) l
  end.

Lemma Exists_not_hd {A : Type} {P : A -> Prop} : forall hd tl,
    ~ P hd -> Exists P (hd :: tl) -> Exists P tl.
Proof.
  intros hd tl Nhd E.
  inversion E; subst; clear E.
  - contradiction.
  - auto.
Qed.

Fixpoint findIndex {A : Type} `{EqDec A} (x : A) (ls : list A) : nat :=
  match ls with
  | [] => 0
  | hd :: tl =>
    match equiv_dec x hd with
    | left _ => 0
    | right Neq => S (findIndex x tl)
    end
  end.

Theorem findIndex_correct {A : Type} `{EqDec A} : forall x xs d,
    Exists (equiv x) xs -> nth (findIndex x xs) xs d === x.
Proof.
  intros x xs d E.
  unfold findIndex.
  induction E.
  - destruct (x == x0).
    + simpl. apply equiv_symmetric. auto.
    + contradiction.
  - destruct (x == x0).
    + simpl.  apply equiv_symmetric. auto.
    + apply IHE.
Qed.

Theorem findIndex_bounds {A : Type} `{EqDec A} : forall x xs,
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

Theorem Exists_ix {A : Type } {P : A -> Prop} {l : list A} {d}:
  Exists P l -> (exists i : nat, i < length l /\ P (nth i l d)).
Proof.
  intros E.
  apply Exists_exists in E.
  destruct E as [x [HI HP]].
  apply In_nth with (d := d) in HI.
  destruct HI as [i [HI HN]].
  exists i. replace (nth i l d) with x. split; auto.
Qed.

Theorem Exists_ix' {A : Type } {P : A -> Prop} {l : list A} d:
  (forall n, {P n} + {~ P n}) -> Exists P l -> { i : nat | i < length l /\ P (nth i l d) }.
Proof.
  intros Pdec E.
  assert (forall i, {i < length l /\ P (nth i l d)} + { ~ (i < length l /\ P (nth i l d))}). {
  intros. destruct (Pdec (nth i l d)); destruct (lt_dec i (length l)).
    - left; auto.
    - right; intuition.
    - right; intuition.
    - right; intuition.
  }
  pose proof (constructive_indefinite_ground_description_nat _ H (Exists_ix E)).
  apply H0.
Defined.

Lemma rots_destr {A : Type} : forall (l : list A),
    exists r, rots l = l :: r.
Proof.
  intros.
  unfold rots.
  destruct l as [| a [| b tl]].
  - simpl. exists nil. auto.
  - simpl. eexists. f_equal.
  - simpl. eexists. f_equal.
Defined.

Theorem orig_in_rots {A : Type} `{EqDec (list A)}: forall l,
    Exists (equiv l) (rots l).
Proof.
  intros. simpl.
  destruct (rots_destr l).
  rewrite H0.
  apply Exists_cons_hd. apply equiv_reflexive.
Defined.

Theorem Permutation_exists {A : Type} {P : A -> Prop} : forall l l',
    Permutation l l' -> Exists P l -> Exists P l'.
Proof.
  intros l l' HP HE.
  apply Exists_exists.
  apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
  eauto using Permutation_in.
Defined.

Lemma orig_in_sorted_rots {A : Type} `{TotalOrderDec A} : forall (l : list A) k,
    Exists (@equiv _ _ (Equivalence_list_k k) l) (sort k (rots l)).
Proof.
  intros.
  apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
  apply sort_perm.
  apply (@orig_in_rots _ _ _ (EqDec_list_k k) l).
Defined.

Definition bwn {A : Type} `{TotalOrderDec A} (l : list A) : nat :=
  @findIndex _ _ _ (EqDec_list_k (length l)) l (lexsort (rots l)).

Lemma rots_len {A: Type} : forall (l : list A),
    Forall (fun x => length x = length l) (rots l).
Proof.
  intros. apply iterate_n_preserves; auto.
  intros. eapply eq_trans. symmetry. apply lrot_length. auto.
Qed.

Theorem perm_forall {A : Type} {P : A -> Prop}: forall x y,
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

Lemma sort_rots_len {A: Type} `{TotalOrderDec A}: forall k (l : list A),
    Forall (fun x => length x = length l) (sort k (rots l)).
Proof.
  intros.
  eapply perm_forall.
  apply sort_perm. apply rots_len.
Qed.

Theorem bwn_def {A : Type} `{TotalOrderDec A} : forall xs d,
    Forall2 equiv (nth (bwn xs) (lexsort (rots xs)) d) xs.
Proof.
  intros.
  unfold bwn.
  eapply eq_k_len.
  - pose proof Forall_forall.
    specialize H0 with (A := list A) (P := fun x => length x = length xs).
    specialize (H0 (lexsort (rots xs))).
    apply H0. unfold lexsort.
    destruct (rots_destr xs). rewrite H1. rewrite <- H1.
    apply sort_rots_len.
    apply nth_In.
    apply findIndex_bounds.
    unfold lexsort.
    destruct (rots_destr xs). rewrite H1. rewrite <- H1.
    apply orig_in_sorted_rots.
  - reflexivity.
  - apply findIndex_correct.
    unfold lexsort.
    destruct (rots_destr xs).
    rewrite H0. rewrite <- H0.
    apply orig_in_sorted_rots.
Qed.
End BW.

Definition f {A: Type} `{TotalOrderDec A} (l: list A) := (lexsort (rots l), bwp l, bwn l).

Compute (f [1; 2; 3]).
Compute (f [3; 1; 2]).
Compute (f [2; 1; 2]).
