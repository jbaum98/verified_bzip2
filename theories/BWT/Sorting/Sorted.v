Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.

Require Import BWT.Sorting.Ord.
Require Import BWT.Lib.List.

Section Sorted.
  Context {A : Type} `{O: Preord A}.

  Inductive Sorted: list A -> Prop :=
  | Sorted_nil:
      Sorted nil
  | Sorted_cons: forall hd tl,
      (forall x, In x tl -> le hd x) ->
      Sorted tl ->
      Sorted (hd :: tl).

  Remark Sorted_1:
    forall x, Sorted (x :: nil).
  Proof.
    intros. constructor. intros. elim H. constructor.
  Qed.

  (** Lists of 2 ordered elements are sorted. *)

  Remark Sorted_2:
    forall x y, le x y -> Sorted (x :: y :: nil).
  Proof.
    intros. constructor.
    intros. simpl in H0. destruct H0. subst x0. auto. contradiction.
    apply Sorted_1.
  Qed.

  Lemma Sorted_cons_inv {x l} :
      Sorted (x :: l) -> (forall y, In y l -> le x y) /\ Sorted l.
  Proof. intro HS. inversion HS; split; auto. Qed.

  Lemma Sorted_const : forall l,
      (exists x, Forall (eq x) l) ->
      Sorted l.
  Proof.
    intros l [x HF].
    induction HF; [apply Sorted_nil|].
    apply Sorted_cons.
    intros a HIn.
    apply (proj1 (Forall_forall (eq x) l)) with (x0 := a) in HF; auto.
    subst. reflexivity. auto.
  Qed.
End Sorted.

Theorem Sorted_rem1 {A} {P : Preord A} {E : EqDec A eq} : forall l x,
    Sorted l -> Sorted (rem1 x l).
Proof.
  intros l x HS; revert x.
  induction HS; intros x; [constructor|].
  cbn.
  destruct (equiv_dec x hd); [auto|].
  apply Sorted_cons; intros.
  apply H. apply in_rem1_in in H0. auto.
  apply IHHS.
Qed.

Section LocallySorted.
  Context {A : Type} `{O: Preord A}.

  (** An alternative definition of being sorted that's easier to prove. *)
  Inductive LocallySorted : list A -> Prop :=
  | LSorted_nil : LocallySorted nil
  | LSorted_cons1 a : LocallySorted (a :: nil)
  | LSorted_consn a b l :
      LocallySorted (b :: l) -> le a b -> LocallySorted (a :: b :: l).

  Lemma Sorted_LocallySorted_iff : forall l, Sorted l <-> LocallySorted l.
  Proof.
    split.
    - induction l as [|a [|b l]]; intros H; constructor;
        inversion H; subst; clear H; auto using in_eq.
    - induction l as [|a [|b l]]; intros.
      + constructor.
      + constructor; [contradiction|constructor].
      + inversion H; subst; clear H.
        specialize (IHl H2); clear H2.
        constructor; auto.
        intros. eapply le_trans; eauto.
        inversion IHl; subst; clear IHl.
        destruct H; subst; auto using le_refl.
  Qed.

  Theorem Sorted_app : forall a l1 l2,
      Sorted (l1 ++ a :: l2) <->
      Sorted l1 /\ Sorted (a :: l2) /\ Forall (fun x => le x a) l1.
  Proof.
    intros a l1 l2.
    split.
    - intros HS.
      remember (l1 ++ a :: l2) as l.
      revert a l1 l2 Heql.
      induction HS; intros a l1 l2 HL.
      apply app_cons_not_nil in HL; contradiction.
      destruct l1. inversion HL; subst; clear HL.
      split; auto using Sorted_nil, Sorted_cons.
      destruct (IHHS a l1 l2) as [HS1 [HS2 HF]]; [inversion HL; auto|].
      repeat split.
      + apply Sorted_cons.
        inversion HL; subst; clear HL.
        intros x HIn.
        apply H. apply in_or_app.
        left. auto.
        apply HS1.
      + apply HS2.
      + constructor.
        inversion HL; subst; clear HL.
        apply H. apply in_or_app. right. left. auto.
        auto.
    - induction l1 as [|h t]; intros [HS1 [HS2 HF]]; [apply HS2|].
      cbn; apply Sorted_cons.
      intros x HIn.
      apply in_app_or in HIn.
      destruct HIn.
      + apply Sorted_cons_inv in HS1; destruct HS1 as [HLe _].
        apply HLe. auto.
      + inversion HF; subst; clear HF.
        destruct H; [subst; auto|].
        apply Sorted_cons_inv in HS2; destruct HS2 as [HLe _].
        transitivity a; [auto|].
        apply HLe. auto.
      + apply IHt. repeat split.
        * apply Sorted_cons_inv in HS1; destruct HS1; auto.
        * auto.
        * inversion HF; auto.
  Qed.
End LocallySorted.
