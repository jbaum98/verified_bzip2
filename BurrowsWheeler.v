Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Recdef.
Require Import Omega.

Require Import Rot.

Fixpoint iterate_n {A: Type} (f: A -> A) (n: nat) (x: A) : list A :=
  match n with
  | O    => []
  | S m => x :: iterate_n f m (f x)
  end.

Definition rots {A: Type} : list A -> list (list A) :=
  fun l => iterate_n (@lrot A) (length l) l.

Definition lexsort {A: Type} : list (list A) -> list (list A).
Admitted.

Theorem lrot_nonempty {A: Type}: forall (l: list A),
    l <> [] -> lrot l <> [].
Proof.
  destruct l.
  - contradiction.
  - intro. simpl.
    intro contra.
    symmetry in contra.
    apply app_cons_not_nil in contra.
    apply contra.
Qed.

Theorem iterate_n_preserves {A: Type}: forall f n (z: A) (P: A -> Prop),
    (forall x, P x -> P (f x)) -> P z -> Forall P (iterate_n f n z).
Proof.
  intros f n z P HPreserve Pz. revert z Pz.
  induction n.
  - constructor.
  - simpl. constructor; auto.
Qed.

Theorem rots_nonempty {A: Type}: forall l,
    l <> [] -> Forall (fun x => x <> @nil A) (rots l).
Proof.
  induction l.
  - contradiction.
  - intro.
    unfold rots.
    apply iterate_n_preserves. apply lrot_nonempty. auto.
Qed.

Theorem lexsort_nonempty {A: Type}: forall l,
    Forall (fun x => x <> @nil A) l -> Forall (fun x => x <> @nil A) (lexsort l).
Admitted.


Definition bwp {A: Type} : list A -> list A :=
  fun l => match l as l0 return l = l0 -> list A with
        | [] => const []
        | _ => fun EL =>
                let NE := list_disc EL in
                let p := lexsort_nonempty (rots l) (rots_nonempty l NE) in
                safe_lasts (lexsort (rots l)) p
        end eq_refl.
