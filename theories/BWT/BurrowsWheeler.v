Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import BWT.Columns.
Require Import BWT.Instances.
Require Import BWT.Lib.FindIndex.
Require Import BWT.Lib.List.
Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.Repeat.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Rotation.Rots.
Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.Key.
Require Import BWT.Sorting.RadixSort.
Require Import BWT.Sorting.StablePerm.
Require Import BWT.Sorting.Sort.

Import Coq.Lists.List.ListNotations.

Section Transform.
  Context {A : Type} `{O: Ord A}.

  Definition bwl (l : list A) : list A :=
    match l with
    | [] => []
    | hd :: _ => List.map (fun x => last x hd) (lexsort (rots l))
    end.

  Lemma bwl_nonempty : forall l d,
      l <> [] ->
      bwl l = List.map (fun x => last x d) (lexsort (rots l)).
  Proof.
    destruct l; intros.
    - contradiction.
    - apply map_forall_eq.
      apply Forall_forall.
      intros x HIn.
      assert (x <> []). {
        apply (Forall_forall (fun x => ~ x = []) (lexsort (rots (a :: l)))); auto.
        eapply Permutation_forall. apply lexsort_perm.
        apply rots_nonempty; auto.
      }
      apply last_nonempty; auto.
  Qed.

  Lemma bwl_length : forall l,
      length (bwl l) = length l.
  Proof.
    induction l.
    - reflexivity.
    - cbn [bwl]. rewrite map_length.
      rewrite lexsort_length.
      rewrite rots_length.
      reflexivity.
  Qed.

  Lemma sort_rots_all_len : forall l,
      Forall (fun x => length x = length l) (lexsort (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply lexsort_perm. apply rots_row_length.
  Qed.

  Definition bwn (l : list A) : nat :=
    findIndex l (lexsort (rots l)).

  Lemma orig_in_sorted_rots : forall l,
      l <> [] -> Exists (eq l) (lexsort (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := lexsort (rots l)).
    apply lexsort_perm.
    apply orig_in_rots. auto.
  Qed.

  Theorem bwn_correct : forall xs d,
    xs <> [] -> nth (bwn xs) (lexsort (rots xs)) d = xs.
  Proof.
    intros.
    unfold bwn.
    apply eqv_eq.
    apply findIndex_correct.
    eapply Exists_impl; [apply orig_in_sorted_rots; auto|].
    intros; subst; reflexivity.
  Qed.
End Transform.

Section Radixsort.
  Context {A : Type} `{O : Ord A}.

  Theorem lexsort_rots_radixsort : forall l n,
      Forall (fun x => length x = n) l ->
      radixsort l n = lexsort l.
  Proof.
    intros l n HL.
    apply StablePerm_Sorted_eq;
      [apply radixsort_sorted; easy|apply lexsort_sorted|].
    apply all_perm_stable; [apply eqv_eq|].
    transitivity l;
      [symmetry; apply radixsort_perm; easy|apply lexsort_perm].
  Qed.

  Lemma hdsort_rrot_length : forall l,
      Forall (fun x : list A => length x = length l) (hdsort (rrot (rots l))).
  Proof.
    intros.
    eapply Permutation_forall.
    transitivity (rrot (rots l));
      [apply rrot_perm|apply InsertionSort.sort_perm].
    apply rots_row_length.
  Qed.

  Theorem lexsort_rots_hdsort : forall l,
      hdsort (map rrot (lexsort (rots l))) = lexsort (rots l).
  Proof.
    intros.
    rewrite <- (lexsort_rots_radixsort (rots l) (length l))
      by apply rots_row_length.
    unfold radixsort at 1.
    match goal with
    | |- hdsort (map rrot ?x) = ?R =>
      replace (hdsort (map rrot x)) with ((hdsort ∘ map rrot) x) by reflexivity
    end.
    rewrite rep_l, <- rep_r.
    match goal with
    | |- rep (hdsort ∘ map rrot) ?n ?l = ?R =>
      replace (rep (hdsort ∘ map rrot) n l) with (radixsort l n) by reflexivity
    end.
    unfold compose.
    rewrite map_rrot_rots.
    apply StablePerm_Sorted_eq;
      [apply radixsort_sorted..|]; [apply hdsort_rrot_length|apply rots_row_length|].
    apply all_perm_stable; [apply eqv_eq|].
    transitivity (rots l).
    + transitivity (hdsort (rrot (rots l))).
      symmetry. apply radixsort_perm; apply hdsort_rrot_length.
      transitivity (rrot (rots l)).
      symmetry; apply InsertionSort.sort_perm.
      symmetry; apply rrot_perm.
    + apply radixsort_perm; apply rots_row_length.
  Qed.
End Radixsort.

Section Recreate.
  Context {A : Type} `{Ord A}.

  Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
    match j with
    | O    => map (const []) l
    | S j' => hdsort (prepend_col l (recreate j' l))
    end.

  Theorem recreate_correct_inv : forall j l,
      j <= length l ->
      recreate j (bwl l) = cols j (lexsort (rots l)).
  Proof.
    induction j as [|j IH]; intros l HJ.
    - unfold cols; simpl.
      do 2 (erewrite map_const; [|unfold const; reflexivity]).
      rewrite bwl_length, lexsort_length, rots_length.
      reflexivity.
    - rewrite <- lexsort_rots_hdsort.
      rewrite cols_hdsort_comm.
      destruct (length_nonempty_destr l j) as [HNE d]; [auto|].
      rewrite cols_map_rrot with (d0 := d).
      rewrite <- IH by omega.
      rewrite <- bwl_nonempty with (d0:=d) by auto.
      reflexivity.
      eapply Forall_impl; [|apply sort_rots_all_len].
      cbn; intros; omega.
  Qed.

  Corollary recreate_correct : forall l,
      recreate (length l) (bwl l) = lexsort (rots l).
  Proof.
    intros.
    rewrite recreate_correct_inv by omega.
    rewrite cols_id; auto.
    eapply Forall_impl; [|apply sort_rots_all_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{O : Ord A}.

  Definition unbwt (i : nat) (l : list A) : list A :=
    nth i (recreate (length l) l) l.

  Theorem unbwt_correct : forall xs : list A,
      unbwt (bwn xs) (bwl xs) = xs.
  Proof.
    intros [|a xs]; [reflexivity|].
    unfold unbwt.
    rewrite bwl_length.
    rewrite recreate_correct.
    apply bwn_correct.
    intro contra; inversion contra.
  Qed.
End Unbwt.

Print Assumptions unbwt_correct.
