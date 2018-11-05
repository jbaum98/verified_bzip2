(** * Merge sort over lists *)

Require Import Sorted.

Require Import Coq.Lists.List.
Require Coq.Program.Wf.
Require Coq.Program.Tactics.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.

Require Import Ord.

Section Sort.

(** A type equipped with a total, decidable preorder. *)
  Context {A} `{O : Ord A}.
  Open Scope ord_scope.

(** Merging two sorted lists. *)

Fixpoint merge (l1: list A) : list A -> list A :=
  match l1 with
  | nil => (fun l2 => l2)
  | h1 :: t1 =>
      let fix merge_aux (l2: list A) : list A :=
        match l2 with
        | nil => l1
        | h2 :: t2 =>
           if le_dec h1 h2
           then h1 :: merge t1 l2
           else h2 :: merge_aux t2
        end
      in merge_aux
  end.

Lemma merge_spec:
  forall l1, Sorted l1 ->
  forall l2, Sorted l2 ->
  Sorted (merge l1 l2) /\ Permutation (merge l1 l2) (l1 ++ l2) /\ Stable (merge l1 l2) (l1 ++ l2).
Proof.
  induction 1.
  intros; simpl. split. auto. split. apply Permutation_refl. apply Stable_refl.
  induction 1; intros; simpl.
  rewrite <- app_nil_end.
  split. constructor; auto. split. apply Permutation_refl. apply Stable_refl.
  destruct (le_dec hd hd0).
(* le hd hd0 *)
  destruct (IHSorted (hd0 :: tl0)) as [P [Q R]]. constructor; auto.
  split.
  constructor. intros.
  assert (In x (tl ++ hd0 :: tl0)). eapply Permutation_in; eauto.
  destruct (in_app_or _ _ _ H4). auto.
  simpl in H5; destruct H5. congruence. apply le_trans with hd0; auto.
  auto.
  split.
  apply perm_skip; auto.
  apply Stable_skip; auto.
(* ~le hd hd0 *)
  destruct IHSorted0 as [P [Q R]].
  split.
  change (Sorted (hd0 :: merge (hd :: tl) tl0)).
  constructor. intros.
  assert (In x ((hd :: tl) ++ tl0)). eapply Permutation_in; eauto.
  simpl in H4; destruct H4. subst x. apply le_not; auto.
  destruct (in_app_or _ _ _ H4). apply le_trans with hd; auto. apply le_not; auto. auto.
  auto.
  split.
  change (Permutation (hd0 :: merge (hd :: tl) tl0) ((hd :: tl) ++ hd0 :: tl0)).
  apply Permutation_cons_app. auto.
  change (Stable (hd0 :: merge (hd :: tl) tl0) ((hd :: tl) ++ hd0 :: tl0)).
  rewrite <- app_comm_cons.
  apply Stable_cons_app'. auto. constructor; auto. auto.
Qed.

(** Flattening a list of lists. *)

Fixpoint flatten (ll: list (list A)): list A :=
  match ll with
  | nil => nil
  | hd :: tl => hd ++ flatten tl
  end.

(** Merging adjacent pairs of lists in a list of sorted lists. *)

Program Fixpoint merge_pairs
    (ll: list (list A))
    (SORTED: forall l, In l ll -> Sorted l)
    {struct ll}:
    { ll' : list(list A) |
      (forall l, In l ll' -> Sorted l)
      /\ Permutation (flatten ll') (flatten ll)
      /\ Stable (flatten ll') (flatten ll)
      /\ (length ll' <= length ll)%nat
      /\ (length ll >= 2 -> length ll' < length ll)%nat } :=
  match ll with
  | l1 :: l2 :: tl => merge l1 l2 :: merge_pairs tl _
  | _ => ll
  end.
Next Obligation.
  apply SORTED. simpl. auto.
Defined.
Next Obligation.
  assert (Sorted l1). apply SORTED. simpl; auto.
  assert (Sorted l2). apply SORTED. simpl; auto.
  destruct (merge_spec l1 H l2 H0). destruct H2.
  split. intros. destruct H4. congruence. auto.
  split. rewrite <- app_ass. apply Permutation_app; auto.
  split. rewrite <- app_ass. apply Stable_app; auto.
  split. simpl. omega.
  intros. simpl. omega.
Defined.
Next Obligation.
  split. auto. split. apply Permutation_refl. split. apply Stable_refl.
  split. omega.
  intro.
  destruct ll; simpl in H0. elimtype False; omega.
  destruct ll; simpl in H0. elimtype False; omega.
  elim (H l l0 ll). auto.
Defined.

(** Iterating [merge_pairs] until all sorted lists have been merged in one. *)

Program Fixpoint merge_iter (ll: list (list A))
                            (SRT: forall l, In l ll -> Sorted l)
                            {measure (length ll)} :
                 { l : list A
                   | Sorted l /\ Permutation l (flatten ll) /\ Stable l (flatten ll) } :=
  match ll with
  | nil => nil
  | l :: nil => l
  | _ => merge_iter (merge_pairs ll _) _
  end.
Next Obligation.
  split. constructor. split. apply perm_nil. apply Stable_refl.
Defined.
Next Obligation.
  split. simpl in SRT. auto.
  rewrite <- app_nil_end. split. apply Permutation_refl. apply Stable_refl.
Defined.
Next Obligation.
  cbn in H0.
  destruct (merge_pairs ll SRT)
    as [mll [P [Q [R [S T]]]]].
  auto.
Defined.
Next Obligation.
  cbn.
  destruct (merge_pairs ll SRT)
    as [mll [P [Q [R [S T]]]]].
  apply T.
  destruct ll as [| a ll]; try destruct ll as [|b ll];
    [contradiction|elim (n a); auto|].
  simpl; omega.
Defined.
Local Obligation Tactic := intros; subst; cbn.
Next Obligation.
  case ((merge_iter
          (proj1_sig
             (merge_pairs ll
                (fun (l : list A) (H0 : In l ll) =>
                 merge_iter_func_obligation_3 ll SRT ll H eq_refl l H0)))
          (fun (l : list A)
             (H0 : In l
                     (proj1_sig
                        (merge_pairs ll
                           (fun (l0 : list A) (H0 : In l0 ll) =>
                            merge_iter_func_obligation_3 ll SRT ll H eq_refl l0 H0))))
           => merge_iter_func_obligation_4 ll SRT ll H eq_refl l H0)
          (merge_iter_func_obligation_5 ll SRT merge_iter ll H eq_refl))).
  intro res.
  case ((merge_pairs ll
                (fun (l : list A) (H0 : In l ll) =>
                 merge_iter_func_obligation_3 ll SRT ll H eq_refl l H0))).
  simpl. intros mll [P [Q [R [V S]]]] [T [U W]].
  split. auto.
  split. apply Permutation_trans with (flatten mll). auto. auto.
  apply Stable_trans with (flatten mll). auto. auto.
Defined.
Local Obligation Tactic := Tactics.program_simpl.
Next Obligation.
  split; intros. congruence. congruence.
Defined.

(** Cutting a list into a list of sorted lists. *)

Program Fixpoint presort (l: list A) :
  { l': list (list A) |
    (forall x, In x l' -> Sorted x) /\ Permutation (flatten l') l /\ Stable (flatten l') l} :=
  match l with
  | nil => nil
  | x :: nil => (x :: nil) :: nil
  | x :: y :: tl =>
    (if le_dec x y then x :: y :: nil else y :: x :: nil)
      :: presort tl
  end.
Next Obligation.
  split. tauto. split. constructor. apply Stable_refl.
Qed.
Next Obligation.
  split. intros. destruct H. subst x0. constructor. intros. elim H. constructor.
  contradiction.
  split. apply Permutation_refl. apply Stable_refl.
Qed.
Next Obligation.
  split.
  intros. destruct H. subst x1.
  destruct (le_dec x y); apply Sorted_2; auto.
  apply le_not; auto. auto.
  destruct (le_dec x y); simpl.
  split.
  apply perm_skip. apply perm_skip. auto.
  apply Stable_skip. apply Stable_skip. auto.
  split.
  eapply perm_trans. apply perm_swap.  apply perm_skip. apply perm_skip. auto.
  eapply Stable_trans. apply Stable_swap. auto.  apply Stable_skip. apply Stable_skip. auto.
Defined.

(** The sorting function. *)

Program Definition mergesort (l: list A):
  { l' : list A | Sorted l' /\ Permutation l' l /\ Stable l' l } :=
  merge_iter (presort l) _.
Next Obligation.
  destruct (presort l) as [l' [P Q]]. simpl in H. auto.
Qed.
Next Obligation.
  case ((merge_iter (proj1_sig (presort l))
          (fun (l0 : list A) (H : In l0 (proj1_sig (presort l))) =>
           mergesort_obligation_1 l l0 H))).
  intros res. simpl.
  case (presort l). simpl.
  intros l' [P [Q R]] [S [T U]].
  split. auto. split. eapply Permutation_trans; eauto. eapply Stable_trans; eauto.
Qed.

(** A property of permutations that is missing from the List library:
  a permutation of a list without duplicates is a list without duplicates. *)

Lemma Permutation_NoDup:
  forall (l l': list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; intros.
  constructor.

  inversion H0; subst. constructor; auto.
  red; intro; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.

  inversion H; subst. inversion H3; subst.
  constructor. simpl. simpl in H2. intuition.
  constructor. simpl in H2. intuition. auto.

  auto.
Qed.

End Sort.
