Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Lib.List.
Import Coq.Lists.List.ListNotations.

Section Props.
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
End Props.

Section Preserve.
  Context {A : Type} (f : list A -> list A).
  Hypothesis HF: forall l, Permutation l (f l).

  Theorem f_perm : forall (x y : list A),
      Permutation x y -> Permutation x (f y).
  Proof.
    assert (LP: forall l, Permutation (f l) l). {
      intro l. apply Permutation_sym. apply HF.
    }
    intros. inversion H; subst; clear H.
    - apply HF.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply perm_skip. apply Permutation_sym. auto.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      repeat constructor.
    - apply Permutation_sym. eapply perm_trans. apply LP.
      apply Permutation_sym. eapply perm_trans; eauto.
  Qed.

  Theorem f_perm' : forall (x y : list A),
      Permutation x y -> Permutation (f x) (f y).
  Proof.
    intros.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym.
    eapply perm_trans. apply Permutation_sym. apply f_perm; auto.
    apply Permutation_sym. apply H.
  Qed.

  Theorem f_nonempty : forall l,
      l <> [] -> f l <> [].
  Proof.
    intros. intro contra.
    specialize (HF l).
    rewrite contra in HF.
    apply Permutation_sym in HF.
    apply Permutation_nil in HF.
    rewrite HF in H. contradiction.
  Qed.
End Preserve.

Lemma Permutation_cons_in {A} : forall (x y : A) xs ys,
    Permutation (x :: xs) (y :: ys) ->
    (x = y \/ In x ys).
Proof.
  intros x y xs ys P.
  eapply Permutation_in in P.
  cbn in P. destruct P as [E | I]; eauto.
  cbn; eauto.
Qed.


(** A property of permutations that is missing from the List library:
  a permutation of a list without duplicates is a list without duplicates. *)

Lemma Permutation_NoDup {A}:
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

Theorem Permutation_1 {A} : forall (a : A) y,
    Permutation [a] y -> y = [a].
Proof.
  intros a y HP.
  remember [a] as x. revert a Heqx.
  induction HP.
  - reflexivity.
  - intros a H. inversion H; subst; clear H.
    apply Permutation_nil in HP. subst l'.
    reflexivity.
  - intros a H. inversion H.
  - intros.
    specialize (IHHP1 a Heqx).
    specialize (IHHP2 a (eq_trans IHHP1 Heqx )).
    subst; auto.
Qed.

Theorem Permutation_zip_eq {A B} : forall l1 l2 : list (A * B),
    Permutation l1 l2 ->
    NoDup (map fst l1) ->
    map fst l1 = map fst l2 ->
    map snd l1 = map snd l2.
Proof.
  induction l1 as [|[xl xr] l1 IH]; intros [|[yl yr] l2];
    intros P ND H1;
    [..|symmetry in P|];
    [reflexivity|apply Permutation_nil_cons in P; contradiction..|].
  cbn in *.
  inversion H1; subst; clear H1.
  destruct (Permutation_in (yl, xr) P) as [HE | HP]; [left; easy|..].
  - inversion HE; subst; clear HE.
    f_equal.
    apply IH.
    eapply Permutation_cons_inv; apply P.
    eapply NoDup_cons_iff; apply ND.
    easy.
  - exfalso.
    apply NoDup_cons_iff with (a := yl) (l := map fst l1); [easy|].
    rewrite H2.
    apply in_map_iff. exists (yl, xr). easy.
Qed.

Theorem Permutation_combine_eq {A B} : forall (x : list A) (y1 y2 : list B),
    Permutation (combine x y1) (combine x y2) ->
    length x = length y1 -> length x = length y2 ->
    NoDup x ->
    y1 = y2.
Proof.
  intros x y1 y2 HP HL1 HL2 ND.
  pose proof (combine_split x y1 HL1) as S1.
  pose proof (combine_split x y2 HL2) as S2.
  rewrite map_split in S1, S2.
  inversion S1 as [[X1 Y1]]; rewrite X1 in *; clear S1.
  inversion S2 as [[X2 Y2]]; rewrite Y2, X2 in *; rewrite <- Y2; clear S2.
  apply Permutation_zip_eq; rewrite ?X1, ?X2; easy.
Qed.
