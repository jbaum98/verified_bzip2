Require Import Coq.Lists.List.
Import ListNotations.

Section TakeWhile.
  Context {A : Type}.

  Fixpoint take_while (f : A -> bool) (l : list A) : list A :=
    match l with
    | [] => []
    | h :: t => if f h then h :: take_while f t else []
    end.

  Fixpoint drop_while (f : A -> bool) (l : list A) : list A :=
    match l with
    | [] => []
    | h :: t => if f h then drop_while f t else l
    end.

  Theorem take_while_all : forall f l,
      Forall (fun x => f x = true) (take_while f l).
  Proof.
    induction l; [constructor|].
    simpl. destruct (f a) eqn:HF.
    - constructor. auto. apply IHl.
    - constructor.
  Qed.

  Theorem drop_while_hd : forall f l l' a,
      drop_while f l = a :: l' ->
      f a = false.
  Proof.
    induction l as [|h l IH]; intros l' a HL.
    - cbn in HL. discriminate.
    - cbn in HL. destruct (f h) eqn:FH.
      + eapply IH; eauto.
      + inversion HL; subst; auto.
  Qed.

  Theorem take_drop_while_id : forall f l,
      l = take_while f l ++ drop_while f l.
  Proof.
    induction l; [reflexivity|].
    simpl; destruct (f a) eqn:HF.
    - cbn. f_equal. apply IHl.
    - reflexivity.
  Qed.
End TakeWhile.
