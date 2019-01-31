Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.
Require Import BWT.NonEmptyList.

Require Import BWT.Repeat.

Import ListNotations.

Section Rot.
  Open Scope program_scope.

  Context {A : Type}.

  (* Rotate a list to the right by moving the last element to the front. *)
  Definition rrot (l: list A) : list A :=
    ne_cons (last l) (init l).

  (* Rotate a list to the left by moving the first element to the end. *)
  Definition lrot (l: list A) : list A :=
    ne_snoc (head l) (tail l).

  Theorem l_r_rot_inverse : forall (l: list A),
      rrot (lrot l) = l.
  Proof.
    intro. unfold rrot, lrot.
    rewrite last_ne_snoc, init_ne_snoc.
    apply head_tail_id.
  Qed.

  Theorem r_l_rot_inverse : forall (l: list A),
      lrot (rrot l) = l.
  Proof.
    intro. unfold rrot, lrot.
    rewrite head_ne_cons, tail_ne_cons.
    apply last_init_id.
  Qed.
End Rot.
