Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Import Coq.Lists.List.ListNotations.

Require Import BWT.Lib.Permutation.

Definition perm (n : nat) (p : list nat) : Prop :=
  Permutation p (seq 0 n).

Theorem perm_0 : forall p,
    perm 0 p -> p = [].
Proof.
  intros p HP.
  unfold perm in HP; symmetry in HP.
  apply Permutation_nil; easy.
Qed.

Theorem perm_range : forall p i n,
    perm n p -> In i p -> i < n.
Proof.
  intros p i n HP; revert i.
  apply Forall_forall.
  eapply Permutation_forall; [symmetry; apply HP|].
  apply Forall_forall. apply in_seq.
Qed.

Section Apply.
  Context {A : Type}.

  Implicit Types (p : list nat) (l : list A).

  Definition apply p l : list A
    := match l with
       | [] => []
       | d::_ => map (fun i => nth i l d) p
       end.

  Theorem apply_def : forall p l d ,
      perm (length l) p ->
      apply p l = map (fun i => nth i l d) p.
  Proof.
    intros p [|h t] d HP.
    - apply perm_0 in HP; subst; easy.
    - cbn [apply]. apply map_ext_in.
      intros; apply nth_indep.
      apply (perm_range p); easy.
  Qed.

  Theorem map_seq_id : forall l d,
      map (fun x : nat => nth x l d) (seq 0 (length l)) = l.
  Proof.
    induction l; intros d; [easy|].
    cbn [length seq map]; f_equal.
    rewrite <- seq_shift, map_map.
    apply IHl.
  Qed.

  Theorem apply_id : forall l,
      apply (seq 0 (length l)) l = l.
  Proof.
    destruct l; [easy|].
    apply map_seq_id with (d := a).
  Qed.
End Apply.

Section Compose.
  Implicit Types (p : list nat).

  Definition compose p2 p1 := apply p2 p1.

  Theorem compose_apply {A} : forall n (l : list A) p1 p2,
      length l = n ->
      perm n p1 -> perm n p2 ->
      apply (compose p2 p1) l = apply p2 (apply p1 l).
  Proof.
    induction n; intros l p1 p2 HL HP1 HP2.
    - apply length_zero_iff_nil in HL.
      apply perm_0 in HP1.
      apply perm_0 in HP2.
      subst; easy.
    - destruct l as [|h t]; [discriminate|].
      destruct p1 as [|h1 t1];
        [unfold perm in HP1; apply Permutation_length in HP1; discriminate|].
      destruct p2 as [|h2 t2];
        [unfold perm in HP2; apply Permutation_length in HP2; discriminate|].
      unfold compose.
      cbn [apply map apply map].
      f_equal.
      + cbn.
    cbn [apply map].
    destruct l as [|h t] eqn:HL; [easy|rewrite <- HL in *; clear HL t].
    rewrite !apply_def with (d := h), apply_def with (d := 0).

    rewrite map_map.

    rewrite <- map_seq_id with (d := h). map_map.
    intros. rewrite <- @apply_id with (l := l).
    unfold compose.
    induction l; intros p1 p2; [easy|].

  Theorem perm_ex_Permutation {A} : forall l l' : list A,
      Permutation l l' -> (exists p, perm (length l) p /\ apply p l = l').
  Proof.
    intros l l' HP.
    induction HP.
    - exists []. split; cbn; unfold perm; auto.
    - destruct IHHP as [p [Hp HA]].
      exists (0 :: map S p). cbn [length apply]; split.
      + unfold perm; cbn.
        apply perm_skip.
        rewrite <- seq_shift.
        apply Permutation_map. apply Hp.
      + cbn [map]. f_equal.
        rewrite apply_def with (d := x) in HA by easy.
        rewrite map_map. cbn. easy.
    - exists (1 :: 0 :: map (fun x => S (S x)) (seq 0 (length l))).
      split.
      + unfold perm. cbn [length seq].
        rewrite <- map_map, !seq_shift.
        apply perm_swap.
      + cbn [apply map]; do 2 f_equal.
        rewrite map_map. cbn [nth].
        apply apply_id.
    - destruct IHHP1 as [p1 [Hp1 HA1]].
      destruct IHHP2 as [p2 [Hp2 HA2]].
      exists (apply p1 p2).

End Apply.

Section Stable.
  Context {A} `{EqDec A}.

  Definition stable_perm (p : list nat) (l : list A) :=
    perm (length l) p /\
