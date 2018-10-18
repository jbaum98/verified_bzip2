Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Recdef.
Require Import Omega.

Require Import Rot.
Require Import Prefix.
Require Import Ord.

Section BW.

Open Scope program_scope.

Fixpoint iterate_n {A: Type} (f: A -> A) (n: nat) (x: A) : list A :=
  match n with
  | O   => []
  | S m => x :: iterate_n f m (f x)
  end.

Definition rots {A: Type} : list A -> list (list A) :=
  fun l => iterate_n lrot (length l) l.

Definition lexsort {A: Type} `{TotalOrderDec A} : list (list A) -> list (list A) :=
  fun ls =>
    match ls with
    | [] => []
    | hd :: tl => sort (length hd) ls
    end.

Theorem iterate_n_preserves {A: Type}: forall f n (z: A) (P: A -> Prop),
    (forall x, P x -> P (f x)) -> P z -> Forall P (iterate_n f n z).
Proof.
  intros f n z P HPreserve Pz. revert z Pz.
  induction n.
  - constructor.
  - simpl. constructor; auto.
Qed.

Definition bwp {A: Type} `{TotalOrderDec A} (l: list A) : list A :=
  match l with
  | [] => []
  | hd :: tl => (List.map (fun x => last x hd) ∘ lexsort ∘ rots) l
  end.

End BW.

Compute bwp [1; 2; 3].
