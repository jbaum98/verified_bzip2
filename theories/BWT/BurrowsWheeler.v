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

Import Coq.Lists.List.ListNotations.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

  Definition bwp (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: _ => List.map (fun x => last x hd) (lexsort (rots l))
    end.

  Lemma bwp_nonempty : forall l d,
      l <> [] ->
      bwp l = List.map (fun x => last x d) (lexsort (rots l)).
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

  Lemma bwp_length : forall l,
      length (bwp l) = length l.
  Proof.
    induction l.
    - reflexivity.
    - cbn [bwp]. rewrite map_length.
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

Section Recreate.
  Context {A : Type} `{Ord A}.

  Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
    match j with
    | O    => map (const []) l
    | S j' => hdsort (prepend_col l (recreate j' l))
    end.

  Theorem recreate_correct_ind : forall j l,
      j <= length l ->
      recreate j (bwp l) = cols j (lexsort (rots l)).
  Proof.
    induction j as [|j IH]; intros l HJ.
    - unfold cols; simpl.
      do 2 (erewrite map_const; [|unfold const; reflexivity]).
      rewrite bwp_length, lexsort_length, rots_length.
      reflexivity.
    - rewrite <- lexsort_rots_hdsort.
      rewrite cols_S_hdsort.
      destruct (length_nonempty_destr l j) as [HNE d]; [auto|].
      rewrite cols_rrot with (d0 := d).
      rewrite <- IH by omega.
      rewrite <- bwp_nonempty with (d0:=d) by auto.
      reflexivity.
      eapply Forall_impl; [|apply sort_rots_all_len].
      cbn; intros; omega.
  Qed.

  Corollary recreate_correct : forall l,
      recreate (length l) (bwp l) = lexsort (rots l).
  Proof.
    intros.
    rewrite recreate_correct_ind by omega.
    rewrite cols_id; auto.
    eapply Forall_impl; [|apply sort_rots_all_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{O : Ord A} `{E : EqDec A eq}.

  Definition unbwt (i : nat) (l : list A) : list A :=
    nth i (recreate (length l) l) l.

  Theorem unbwt_correct : forall xs : list A,
      unbwt (bwn xs) (bwp xs) = xs.
  Proof.
    intros [|a xs]; [reflexivity|].
    unfold unbwt.
    rewrite bwp_length.
    rewrite recreate_correct.
    apply bwn_correct.
    intro contra; inversion contra.
  Qed.
End Unbwt.

Print Assumptions unbwt_correct.
