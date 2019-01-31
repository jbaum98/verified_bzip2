Require Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import BWT.Rotation.
Require Import BWT.Sorting.Prefix.
Require Import BWT.Sorting.Ord.
Require Import BWT.Repeat.
Require Import BWT.Rots.
Require Import BWT.Instances.
Require Import BWT.Lib.
Require Import BWT.Permutations.
Require Import BWT.FindIx.
Require Import BWT.Matrix.
Require Import BWT.NonEmptyList.

Import ListNotations.

Open Scope program_scope.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

  Definition bwp (l: list A) : list A :=
    map last (sort (rots l)).

    match l with
    | [] => []
    | hd :: tl => List.map (fun x => last x hd) (sort (length l) (rots l))
    end.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

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
    findIx l (sort (length l) (rots l)).

  Theorem bwn_correct : forall xs d,
    xs <> [] -> nth (bwn xs) (sort (length xs) (rots xs)) d = xs.
  Proof.
    intros.
    unfold bwn.
    apply findIx_correct.
    apply orig_in_sorted_rots. auto.
  Qed.
End Transform.

Section ReverseTransform.
  Section Recreate.
    Context {A : Type} `{Ord A}.

    Fixpoint recreate (j : nat) (l : list A) : list (list A) :=
      match j with
      | O    => map (const []) l
      | S j' => sort 1 (prepend_col l (recreate j' l))
      end.

    Theorem recreate_inspiration : forall j l,
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

    Lemma recreate_correct_gen : forall j l,
        j <= length l ->
        recreate j (bwp l) = cols j (sort (length l) (rots l)).
    Proof.
      induction j; intros.
      - unfold cols.
        erewrite map_const with (g := const []) (ys := bwp l);
          [| |rewrite bwp_length, sort_length, rots_length]; [|reflexivity..].
        reflexivity.
      - assert (rrot_hdsort_id : forall xs,
                   sort (length xs) (rots xs) =
                   sort 1 (map rrot (sort (length xs) (rots xs)))) by admit.
        rewrite rrot_hdsort_id.
        assert (cols_hdsort_comm : forall j xs,
                   cols (S j) (sort 1 xs) =
                   sort 1 (cols (S j) xs)) by admit.
        rewrite cols_hdsort_comm.
        rewrite cols_rrot.
        assert (cols_succ_rrot : forall j xs d,
                   cols (S j) (map rrot xs) =
                   prepend_col (map (fun l => last l d) xs) (cols j xs)).
        simpl.
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
End ReverseTransform.
