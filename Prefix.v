Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Structures.Orders.
Require Import Ord.
Require Mergesort.

Section EqK.

  Context {A : Type} {R : relation A} `{E : EqDec A R}.

  Inductive eq_k : nat -> list A -> list A -> Prop :=
  | eq_nil  : forall k, eq_k k [] []
  | eq_zero : forall xs ys, eq_k 0 xs ys
  | eq_cons : forall x y xs ys k, x === y -> eq_k k xs ys -> eq_k (S k) (x :: xs) (y :: ys).

  Fixpoint eq_k_dec (k: nat) (xs ys : list A) :
    { eq_k k xs ys } + { ~ eq_k k xs ys }.
  Proof.
    destruct k.
    - left. apply eq_zero.
    - destruct xs as [|x xtl]; destruct ys as [|y ytl].
      + left; apply eq_nil.
      + right. intro contra. inversion contra.
      + right. intro contra. inversion contra.
      + destruct (x == y).
        * destruct (eq_k_dec k xtl ytl).
          { left.  apply eq_cons; auto. }
          { right. intro contra. inversion contra. contradiction. }
        * right. intro contra. inversion contra. contradiction.
  Defined.

  Theorem eq_k_refl (k : nat) : forall (l : list A),
      eq_k k l l.
  Proof.
    intro l; revert k.
    induction l; intro k.
    - apply eq_nil.
    - destruct k.
      + apply eq_zero.
      + apply eq_cons. apply equiv_reflexive.
        apply IHl.
  Qed.

  Theorem eq_k_sym (k : nat) : forall (a b : list A),
      eq_k k a b -> eq_k k b a.
  Proof.
    intros a b H.
    induction H.
    - apply eq_nil.
    - apply eq_zero.
    - apply eq_cons. apply equiv_symmetric; auto.
      auto.
  Qed.

  Fixpoint eq_k_trans (k : nat) : forall (a b c : list A),
      eq_k k a b -> eq_k k b c -> eq_k k a c.
  Proof.
    intros.
    destruct a; destruct b; destruct c;
      auto; try constructor;
        try (destruct k; try apply eq_zero; try inversion H; try inversion H0);
        subst.
    apply eq_cons; auto.
    eapply equiv_transitive; eauto.
    apply eq_k_trans with (b := b); auto.
  Qed.

  Instance Equivalence_list_k (k : nat) : Equivalence (eq_k k) :=
  { Equivalence_Reflexive := eq_k_refl k;
    Equivalence_Symmetric := eq_k_sym k;
    Equivalence_Transitive := eq_k_trans k }.

  Instance EqDec_list_k (k : nat) : EqDec (list A) (eq_k k) :=
    eq_k_dec k.

  Theorem eq_k_firstn : forall k xs ys,
      eq_k k xs ys <-> Forall2 eq (firstn k xs) (firstn k ys).
  Admitted.
End EqK.

Section Ord_K.

  Context {A : Type} {eqA : relation A} `{E : EqDec A eqA}.
  Context {leA: relation A} `{O: TotalOrderDec A eqA leA}.

  Inductive le_k : nat -> list A -> list A -> Prop :=
  | le_nil     : forall ys k, le_k k [] ys
  | le_zero    : forall xs ys, le_k 0 xs ys
  | le_cons_lt : forall x y xs ys k, leA x y -> ~ eqA x y -> le_k k (x :: xs) (y :: ys)
  | le_cons_eq : forall x y xs ys k, eqA x y -> le_k k xs ys ->
                                le_k (S k) (x :: xs) (y :: ys).

  Fixpoint le_k_dec (k: nat) (xs ys : list A) :
    { le_k k xs ys } + { le_k k ys xs }.
  Proof.
    destruct k.
    - left. apply le_zero.
    - destruct xs as [|x xtl]; destruct ys as [|y ytl];
        simpl; try (left; apply le_nil); try (right; apply le_nil).
      destruct (x == y).
      + destruct (le_k_dec k xtl ytl); try omega.
        * left.  apply le_cons_eq; auto.
        * right. apply le_cons_eq; auto. apply equiv_symmetric in e. auto.
      + destruct (le_dec x y).
        * left.  apply le_cons_lt; auto.
        * right. apply le_cons_lt; auto.
          intro contra. apply c. apply equiv_symmetric. auto.
  Defined.

  Instance LeDec_list_k (k : nat) : LeDec (le_k k) := le_k_dec k.
End Ord_K.

Definition sort {A : Type} `{TotalOrderDec A} (k : nat) :
  list (list A) -> list (list A)
  := @Mergesort.sort _ _ (LeDec_list_k k ).

Compute sort 4 [[1; 2; 3]; [1; 0; 2]].


(*   Theorem le_k_antisymm (k : nat) : forall a b : list A, *)
(*       le_k k a b -> le_k k b a -> eq_k k a b. *)
(*   Proof. *)
(*     intros a b LAB LBA. *)
(*     induction LAB; subst. *)
(*     - inversion LBA; subst; clear LBA. *)
(*       constructor. apply eq_zero. *)
(*     - apply eq_zero. *)
(*     - inversion LBA; subst; clear LBA. *)
(*       + apply eq_zero. *)
(*       + eapply lt_contra; eauto. *)
(*       + eapply lt_eq_contra; eauto using eq_sym. *)
(*     - inversion LBA; subst; clear LBA. *)
(*       + eapply lt_eq_contra; eauto using eq_sym. *)
(*       + apply eq_cons; auto. *)
(*   Qed. *)

(*   Theorem le_k_trans (k : nat) : forall a b c : list A, *)
(*       le_k k a b -> le_k k b c -> le_k k a c. *)
(*   Proof. *)
(*     intros a b c LAB LBC. *)
(*     induction LAB; try constructor. *)
(*     - inversion LBC; subst; clear LBC; try constructor. *)
(*       + *)

(*   Instance Ord_list_k (k: nat) : Ord (list A) (Eq_list_k k) := *)
(*     { *)
(*       le := le_k k; *)
(*       le_dec := le_k_dec k; *)
(*       le_antisymm := le_k_antisymm k; *)
(*       le_trans := le_k_trans k; *)
(*     }. *)
(* End Ord_K. *)

(* Compute le_k_dec 2 [1; 2; 3] [1; 0; 2]. *)
