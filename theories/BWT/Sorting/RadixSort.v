Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.Stable.
Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Lib.Repeat.
Require Import BWT.Sorting.Key.
Require Import BWT.Lib.List.
Require Import BWT.Columns.
Require Import BWT.Sorting.Lexicographic.

Section RadixSort.
  Context {A : Type} {O : Preord A}.

  Open Scope program_scope.

  Definition radixsort (l : list (list A)) (n : nat): list (list A)
    := rep (hdsort ∘ map rrot) n l.

  Remark radixsort_S : forall l j,
      radixsort l (S j) = hdsort (map rrot (radixsort l j)).
  Proof. reflexivity. Qed.

  Lemma radixsort_perm_ind : forall n l,
      Permutation (rep (map rrot) n l) (radixsort l n).
  Proof.
    induction n; intro l; [reflexivity|].
    cbn; symmetry.
    apply Permutation_trans with (l' := map rrot (rep (hdsort ∘ map rrot) n l)).
    symmetry. apply sort_perm.
    apply Permutation_map.
    symmetry. apply IHn.
  Qed.

  Theorem radixsort_perm : forall n l,
      Forall (fun x => length x = n) l ->
      Permutation l (radixsort l n).
  Proof.
    intros n l HL.
    unfold radixsort.
    rewrite <- map_id at 1.
    rewrite map_forall_eq with (g := rep rrot n).
    rewrite <- rep_map.
    apply radixsort_perm_ind.
    eapply Forall_impl; [|apply HL].
    cbn; intros a HN.
    rewrite <- HN. symmetry. apply rrot_rep_id.
  Qed.

  Lemma radixsort_nil : forall n, radixsort nil n = nil.
  Proof.
    intros. unfold radixsort.
    apply rep_preserves; [|auto].
    intros x HIn. unfold compose.
    subst.
    reflexivity.
  Qed.

  Theorem radixsort_length : forall n j l,
      Forall (fun x => length x = n) l ->
      Forall (fun x => length x = n) (radixsort l j).
  Proof.
    intros n j l HL.
    unfold radixsort.
    apply rep_preserves; [|auto].
    clear HL l.
    intros l HL.
    apply Forall_forall.
    intros x HIn. unfold compose in HIn.
    apply Permutation_in with (l' := map rrot l) in HIn; [|symmetry; apply sort_perm].
    apply in_map_iff in HIn.
    destruct HIn as [prex [Hprex HIn]].
    rewrite <- Hprex, <- rrot_length.
    apply Forall_forall with (x := prex) in HL.
    apply HL. apply HIn.
  Qed.

  Theorem radixsort_sorted_ind `{@Ord A O} : forall n j l,
      j <= n ->
      Forall (fun x => length x = n) l ->
      PrefixSorted j (radixsort l j).
  Proof.
    induction j; intros l HJ HF; [apply PrefixSorted_zero|].
    rewrite radixsort_S.
    destruct l eqn:HL; [rewrite radixsort_nil; apply Sorted_nil|].
    assert (exists d : A, True). {
      destruct l0.
      inversion HF; subst. cbn in HJ. omega.
      exists a. auto.
    }
    rewrite <- HL in *; clear HL l0 l1.
    destruct H0 as [d _].
    rewrite map_rrot_prepend with (d0 := d).
    apply sort_sorted_S.
    rewrite map_tl_prepend.
    apply key_sorted. rewrite map_map.
    rewrite map_forall_eq with (g := firstn j).
    apply key_sorted.
    apply IHj; [omega|auto].
    apply Forall_forall. intros x Hin.
    apply firstn_init.
    apply radixsort_length with (j := j) in HF.
    apply Forall_forall with (x := x) in HF.
    rewrite HF. omega. auto.
    rewrite !map_length. omega.
    apply radixsort_length with (j := j) in HF.
    eapply Forall_impl; [|apply HF].
    intros a HLa.
    cbn in HLa.
    intro c. rewrite c in HLa. cbn in HLa.
    omega.
  Qed.

  Theorem radixsort_sorted `{@Ord A O} : forall n l,
      Forall (fun x => length x = n) l ->
      Sorted (radixsort l n).
  Proof.
    intros n l HL.
    replace (radixsort l n) with (map (firstn n) (radixsort l n)).
    apply key_sorted. apply radixsort_sorted_ind with (n := n).
    omega. auto.
    rewrite <- map_id. apply map_forall_eq.
    apply radixsort_length with (j := n) in HL.
    eapply Forall_impl; [|apply HL].
    intros. rewrite <- H0. apply firstn_all.
  Qed.
End RadixSort.
