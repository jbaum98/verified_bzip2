Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Section FindIx.
  Context {A : Type} `{EqDec A}.

  Fixpoint findIx (x : A) (ls : list A) : nat :=
    match ls with
    | [] => 0
    | hd :: tl =>
      match x == hd with
      | left _ => 0
      | right Neq => S (findIx x tl)
      end
    end.

  Theorem findIx_correct : forall x xs d,
      Exists (equiv x) xs -> nth (findIx x xs) xs d === x.
  Proof.
    intros x xs d E.
    unfold findIx.
    induction E.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + apply IHE.
  Qed.

  Theorem findIx_bounds : forall x xs,
      Exists (equiv x) xs -> findIx x xs < length xs.
  Proof.
    intros x xs E.
    unfold findIx.
    induction E.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + simpl. apply le_n_S. apply IHE.
  Qed.
End FindIx.
