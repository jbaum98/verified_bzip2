Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Program.
Require Import Coq.Program.Tactics.
Require Import Coq.Sorting.Permutation.

Inductive Index {A : Type} (P : A -> Prop) : list A -> Type :=
| Index_zero : forall (x : A) (l : list A), P x -> Index P (x :: l)
| Index_succ : forall (x : A) (l : list A), Index P l -> Index P (x :: l).

Program Fixpoint index_to_sig {A: Type} {P : A -> Prop} {l}
         (ix : Index P l) : { i : nat | i < length l & forall d, P (nth i l d)}
  := match ix with
     | Index_zero _ x tl Px => exist2 _ _ 0 _ _
     | Index_succ _ x tl ix' =>
       let (i, lProof', pProof') := index_to_sig ix' in
         exist2 _ _ (S i) _ _
     end.
Next Obligation.
  apply Nat.lt_0_succ.
Defined.
Next Obligation.
  apply lt_n_S. apply lProof'.
Defined.

Program Fixpoint index_from_sig {A: Type} {P : A -> Prop} {l}
        (s : { i : nat | i < length l & forall d, P (nth i l d)})
        {measure match s with exist2 _ _ i _ _ => i end }
  : Index P l
  :=
    match s with
    | exist2 _ _ i lProof pProof =>
      match l with
      | [] => _
      | hd :: tl =>
        match i with
        | O    => Index_zero _ hd tl (pProof hd)
        | S i' => Index_succ _ hd tl (index_from_sig (exist2 _ _ i' _ _))
        end
      end
    end.
Next Obligation.
  apply Nat.nlt_0_r in lProof. contradiction.
Defined.
Local Obligation Tactic := intros; simpl; subst.
Next Obligation.
  apply lt_S_n. apply lProof.
Defined.
Next Obligation.
  apply Nat.lt_succ_diag_r.
Defined.

Theorem Permutation_ix {A : Type} {P : A -> Prop}: forall (l l' : list A) (x : A),
 Permutation l l' -> Index P l -> Index P l'.
Proof.
  intros l l' x Hperm; nduction Hperm; simpl; tauto.
Qed.
