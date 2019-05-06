Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.omega.Omega.

Require Import BWT.Sorting.Ord.
Require Import BWT.Lib.List.

Section Sorted.
  Context {A : Type} `{O: Preord A}.

  Inductive Sorted: list A -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_cons : forall a l,
      Forall (le a) l ->
      Sorted l -> Sorted (a :: l).

  Remark Sorted_1:
    forall x, Sorted (x :: nil).
  Proof. intros; constructor; constructor. Qed.

  Remark Sorted_2:
    forall x y, le x y -> Sorted (x :: y :: nil).
  Proof. intros; (repeat constructor || easy). Qed.

  Lemma Sorted_cons_inv {x l} :
      Sorted (x :: l) -> (Forall (le x) l) /\ Sorted l.
  Proof. intro HS. inversion HS; split; auto. Qed.

  Lemma Sorted_const : forall l,
      (exists x, Forall (eq x) l) ->
      Sorted l.
  Proof.
    intros l [x HF].
    induction HF; [apply Sorted_nil|].
    apply Sorted_cons; [|easy].
    eapply Forall_impl; [|apply HF].
    intros; subst; reflexivity.
  Qed.

  Theorem Sorted_rem1 {eq_dec : forall x y, {x=y}+{x<>y}} : forall l x,
      Sorted l -> Sorted (rem1 eq_dec x l).
  Proof.
    intros l x HS; revert x.
    induction HS; intros x; [constructor|].
    cbn.
    destruct (eq_dec x a); [auto|].
    apply Sorted_cons; [|easy].
    apply Forall_forall.
    intros y HIny.
    apply in_rem1_in in HIny; revert HIny.
    apply Forall_forall; easy.
  Qed.
End Sorted.

Section SortedLocal.
  Context {A : Type} `{O: Preord A}.

  (** An alternative definition of being sorted that's easier to prove. *)
  Inductive SortedLocal : list A -> Prop :=
  | SortedLocal_nil : SortedLocal nil
  | SortedLocal_1 : forall a, SortedLocal (a :: nil)
  | SortedLocal_cons : forall a b l,
      SortedLocal (b :: l) -> le a b -> SortedLocal (a :: b :: l).

  Lemma SortedLocal_iff : forall l, Sorted l <-> SortedLocal l.
  Proof.
    split.
    - induction l as [|a [|b l]]; intros H; [constructor..|].
      apply Sorted_cons_inv in H; destruct H.
      constructor; [apply IHl; easy|].
      eapply Forall_inv; apply H.
    - induction l as [|a [|b l]]; intros HS;
        [apply Sorted_nil|apply Sorted_1|].
      inversion HS; subst; clear HS.
      specialize (IHl H1); clear H1.
      constructor; auto.
      constructor; [easy|].
      apply Sorted_cons_inv in IHl.
      eapply Forall_impl; [|apply IHl].
      intros; transitivity b; easy.
  Qed.

  Theorem Sorted_app_cons : forall a l1 l2,
      Sorted (l1 ++ a :: l2) <->
      Sorted l1 /\ Sorted (a :: l2) /\ Forall (ge a) l1.
  Proof.
    intros a l1 l2.
    split.
    - intros HS.
      remember (l1 ++ a :: l2) as l.
      revert a l1 l2 Heql.
      induction HS; intros x l1 l2 HL;
        [apply app_cons_not_nil in HL; contradiction|].
      destruct l1;
        [inversion HL; subst; clear HL; split; auto using Sorted_nil, Sorted_cons|].
      inversion HL; subst a0; clear HL; rename H2 into HL.
      destruct (IHHS x l1 l2) as [HS1 [HS2 HF]]; [inversion HL; auto|].
      repeat split.
      + apply Sorted_cons; [|easy].
        apply @Forall_app with (l1 := l1) (l2 := x :: l2).
        rewrite <- HL. easy.
      + apply HS2.
      + constructor; [|easy].
        apply Forall_forall with (l := l) (P := le a); [easy|].
        rewrite HL; apply in_or_app. right. left. auto.
    - induction l1 as [|h t]; intros [HS1 [HS2 HF]]; [apply HS2|].
      cbn; apply Sorted_cons;
        [|apply IHt; inversion HS1; inversion HS2; inversion HF; easy].
      apply Forall_app.
      split; [apply Sorted_cons_inv in HS1; easy|].
      assert (le h a)
        by (apply Forall_forall with (l := h :: t) (P := ge a); [|left]; easy).
      apply Sorted_cons_inv in HS2.
      constructor; [easy|].
      apply Forall_impl with (P := le a); [|apply HS2].
      intros; transitivity a; easy.
  Qed.

  Theorem Sorted_app : forall l1 l2,
      Sorted (l1 ++ l2) -> Sorted l1 /\ Sorted l2.
  Proof.
    intros l1 l2 HS.
    destruct l2. rewrite app_nil_r in HS.
    split; [easy|apply Sorted_nil].
    split; apply (Sorted_app_cons a l1 l2); easy.
  Qed.
End SortedLocal.

Section SortedIx.
  Context {A : Type} `{O: Preord A}.

  Definition SortedIx (l: list A) :=
    forall i j d, i <= j < length l -> le (nth i l d) (nth j l d).

  Lemma SortedIx_cons_inv : forall a b l,
      SortedIx (a :: b :: l) -> le a b /\ SortedIx (b :: l).
  Proof.
    intros a b l HS.
    split.
    - replace a with (nth 0 (a :: b :: l) a) by easy.
      replace b with (nth 1 (a :: b :: l) a) by easy.
      apply HS. cbn; omega.
    - intros i j d HIJ.
      replace (nth i (b :: l) d) with (nth (S i) (a :: b :: l) d) by easy.
      replace (nth j (b :: l) d) with (nth (S j) (a :: b :: l) d) by easy.
      apply HS.
      cbn in *; omega.
  Qed.

  Theorem SortedIx_iff : forall l,
      Sorted l <-> SortedIx l.
  Proof.
    split; induction l as [|h t IH]; [easy| |constructor|].
    - intros HS i j d HIJ.
      apply Sorted_cons_inv in HS; destruct HS as [Hh HS].
      destruct i as [|i]; destruct j as [|j]; [| |omega|].
      + cbn. reflexivity.
      + cbn. apply Forall_nth; [easy|cbn in HIJ; omega].
      + cbn. apply IH; [easy|cbn in HIJ; omega].
    - intros HSix.
      apply SortedLocal_iff; rewrite SortedLocal_iff in IH.
      destruct t as [|b t]; constructor.
      + apply IH. apply (SortedIx_cons_inv h b t). easy.
      + apply (SortedIx_cons_inv h b t). easy.
  Qed.
End SortedIx.
