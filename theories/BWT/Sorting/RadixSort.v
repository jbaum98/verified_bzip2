Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.

Require Import BWT.Sorting.Ord.
Require Import BWT.Sorting.Sorted.
Require Import BWT.Sorting.StablePerm.
Require Import BWT.Sorting.InsertionSort.
Require Import BWT.Rotation.Rotation.
Require Import BWT.Lib.Repeat.
Require Import BWT.Lib.Permutation.
Require Import BWT.Sorting.Key.
Require Import BWT.Lib.List.
Require Import BWT.Columns.
Require Import BWT.Sorting.Lexicographic.
Require Import BWT.Sorting.PermFun.

Section RadixSort.
  Context {A : Type} {O : Preord A}.

  Open Scope program_scope.

  Implicit Type m : list (list A).
  Implicit Type n : nat.

  Definition radixsort m (n : nat) : list (list A)
    := rep (hdsort ∘ map rrot) n m.

  Remark radixsort_S : forall l j,
      radixsort l (S j) = hdsort (map rrot (radixsort l j)).
  Proof. reflexivity. Qed.

  Lemma radixsort_perm_inv : forall j m,
      Permutation (rep (map rrot) j m) (rep (hdsort ∘ map rrot) j m).
  Proof.
    induction j as [|j IH]; intro m; [reflexivity|].
    cbn; symmetry.
    transitivity (map rrot (rep (hdsort ∘ map rrot) j m)).
    symmetry. apply sort_perm.
    apply Permutation_map.
    symmetry. apply IH.
  Qed.

  Theorem radixsort_perm : forall n m,
      Forall (fun r => length r = n) m ->
      Permutation m (radixsort m n).
  Proof.
    intros n m HL.
    unfold radixsort.
    rewrite <- map_id at 1.
    rewrite map_forall_eq with (g := rep rrot n).
    rewrite <- rep_map.
    apply radixsort_perm_inv.
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

  Lemma StablePerm_map_rrot : forall m m' : list (list A),
      StablePerm m m' -> StablePerm (map rrot m) (map rrot m').
  Proof.
    intros m m' HS.
    apply StablePermInd_iff in HS.
    induction HS.
    - reflexivity.
    - cbn. apply StablePerm_skip. apply IHHS.
    - cbn. apply StablePerm_swap.
      intro c; apply H.
      symmetry.
      apply lex_eqv_iff in c.
      apply lex_eqv_iff.
      rewrite <- @r_l_rot_inverse with (l := x).
      rewrite <- @r_l_rot_inverse with (l := y).
      apply Forall2_lrot. easy.
    - transitivity (map rrot l'); easy.
  Qed.

  Lemma radixsort_stable_inv : forall j m,
      StablePerm (rep (map rrot) j m) (rep (hdsort ∘ map rrot) j m).
  Proof.
    induction j; intros l; [reflexivity|].
    cbn; symmetry.
    transitivity (map rrot (rep (hdsort ∘ map rrot) j l)).
    apply PrefixStable_firstn_1.
    symmetry. apply sort_stable.
    apply StablePerm_map_rrot. symmetry. apply IHj.
  Qed.

  Theorem radixsort_stable : forall n l,
      Forall (fun x => length x = n) l ->
      StablePerm l (radixsort l n).
  Proof.
    intros n l HL.
    etransitivity; [|apply radixsort_stable_inv].
    rewrite rep_map.
    replace (map (rep rrot n) l) with (map (fun x => x) l); [rewrite map_id; easy|].
    apply map_forall_eq.
    eapply Forall_impl; [|apply HL].
    intros. rewrite <- H. symmetry; apply rrot_rep_id.
  Qed.

  Lemma radixsort_sorted_inv : forall n j m,
      j <= n ->
      Forall (fun r => length r = n) m ->
      PrefixSorted j (radixsort m j).
  Proof.
    induction j; intros m HJ HL; [apply PrefixSorted_zero|].
    destruct m as [|r m]; [rewrite radixsort_nil; apply Sorted_nil|].
    destruct r as [|d t] eqn:Ht;
      [apply Forall_inv in HL; cbn in HL; omega|rewrite <- Ht in *; clear t Ht].
    rewrite radixsort_S.
    apply hdsort_sorted_S.
    rewrite map_rrot_prepend with (d0 := d)
      by (eapply Forall_impl; [|apply radixsort_length with (j := j) (n := n); easy];
          cbn; intros; intro c; subst; cbn in HJ; omega).
    rewrite map_tl_prepend by (rewrite !map_length; omega).
    apply key_sorted. rewrite map_map.
    rewrite map_forall_eq with (g := firstn j)
      by (apply radixsort_length with (j := j) in HL;
          eapply Forall_impl; [|apply HL]; cbn; intros; apply firstn_init; omega).
    apply key_sorted; fold (PrefixSorted j (radixsort (r :: m) j)).
    apply IHj; [omega|auto].
  Qed.

  Theorem radixsort_sorted : forall n m,
      Forall (fun x => length x = n) m ->
      Sorted (radixsort m n).
  Proof.
    intros n m HL.
    rewrite <- map_id.
    rewrite map_forall_eq with (g := firstn n)
      by (apply radixsort_length with (j := n) in HL;
          eapply Forall_impl; [|apply HL];
          cbn; intros; subst; symmetry; apply firstn_all).
    apply key_sorted; fold (PrefixSorted n (radixsort m n)).
    apply radixsort_sorted_inv with (n := n); [omega|easy].
  Qed.

  Theorem radixsort_correct : forall n m,
      Forall (fun x => length x = n) m ->
      Sorted (radixsort m n) /\ Permutation (radixsort m n) m.
  Proof.
    split; [apply radixsort_sorted|symmetry; apply radixsort_perm]; easy.
  Qed.
End RadixSort.
