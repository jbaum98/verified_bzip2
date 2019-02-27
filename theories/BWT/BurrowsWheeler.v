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
Require Import BWT.Sorting.Prefix.

Import Coq.Lists.List.ListNotations.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

  Definition bwp (l: list A) : list A :=
    match l with
    | [] => []
    | hd :: tl => List.map (fun x => last x hd) (sort (length l) (rots l))
    end.

  Lemma bwp_nonempty : forall l d,
      l <> [] ->
      bwp l = List.map (fun x => last x d) (sort (length l) (rots l)).
  Proof.
    destruct l; intros.
    - contradiction.
    - apply map_forall_eq.
      apply Forall_forall.
      intros x HIn.
      assert (x <> []). {
        apply (Forall_forall (fun x => ~ x = []) (sort (length (a :: l)) (rots (a :: l)))); auto.
        eapply Permutation_forall. apply sort_perm.
        apply rots_nonempty; auto.
      }
      apply last_nonempty; auto.
  Qed.

  Lemma bwp_length : forall l,
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
    findIndex l (sort (length l) (rots l)).

  Lemma orig_in_sorted_rots : forall l k,
      l <> [] -> Exists (eq l) (sort k (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
    apply sort_perm.
    apply orig_in_rots. auto.
  Qed.

  Theorem bwn_correct : forall xs d,
    xs <> [] -> nth (bwn xs) (sort (length xs) (rots xs)) d = xs.
  Proof.
    intros.
    unfold bwn.
    apply findIndex_correct.
    apply orig_in_sorted_rots. auto.
  Qed.
End Transform.

Section Recreate.
  Context {A : Type} `{Ord A}.

  Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
    match j with
    | O    => map (const []) l
    | S j' => sort 1 (prepend_col l (recreate j' l))
    end.

  Theorem recreate_correct_ind : forall j l,
      j <= length l ->
      recreate j (bwp l) = cols j (sort (length l) (rots l)).
  Proof.
    induction j as [|j IH]; intros l HJ.
    - unfold cols; simpl.
      do 2 (erewrite map_const; [|unfold const; reflexivity]).
      rewrite bwp_length, sort_length, rots_length.
      reflexivity.
    - rewrite <- sort_rots_hdsort.
      rewrite cols_S_hdsort.
      destruct (length_nonempty_destr l j) as [HNE d]; [auto|].
      rewrite cols_rrot with (d0 := d).
      rewrite <- IH by omega.
      rewrite <- bwp_nonempty with (d0:=d) by auto.
      reflexivity.
  Qed.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply sort_perm. apply rots_row_length.
  Qed.

  Corollary recreate_correct : forall l,
      recreate (length l) (bwp l) = sort (length l) (rots l).
  Proof.
    intros.
    rewrite recreate_correct_ind by omega.
    rewrite cols_id; auto.
    eapply Forall_impl; [|apply sort_rots_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{O : Ord A} `{E : EqDec A eq}.

  Definition unbwt (t : nat) (l : list A) : list A :=
    nth t (recreate (length l) l) l.

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
