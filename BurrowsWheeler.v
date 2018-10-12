Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Recdef.
Require Import Omega.

Open Scope program_scope.


Definition list_disc_empty_nonempty
           {A T: Type} {tl: list A} {hd: A}
           (H: [] = hd :: tl) : T :=
  match H in _ = l return
        match l with
        | [] => unit
        | _  => T
        end
  with
  | eq_refl => tt
  end.

Definition list_disc_nonempty_empty
           {A T: Type} {tl: list A} {hd: A}
           (H: hd :: tl = []) : T :=
  match H in _ = l return
        match l with
        | [] => T
        | _  => unit
        end
  with
  | eq_refl => tt
  end.

Definition list_disc {A: Type} {T: Set} {l tl: list A} {hd: A} :
  l = hd :: tl -> l = [] -> T
  := match l return l = hd :: tl -> l = [] -> T with
     | [] => list_disc_empty_nonempty
     | _  => const list_disc_nonempty_empty
     end.

Fixpoint safe_last {A: Type} (l: list A) (NE: l <> []) : A :=
  match l with
  | [] => False_rect A ∘ NE
  | hd :: tl =>
    fun _ => match tl as tl' return tl = tl' -> A with
          | [] => const hd
          | tlhd :: tltl => safe_last tl ∘ list_disc
          end eq_refl
  end eq_refl.

Definition Forall_uncons {A: Type} {P: A -> Prop} {l x xs} :
  l = x :: xs -> Forall P l -> P x /\ Forall P xs :=
  fun L H =>
    match H in Forall _ ne return (x :: xs = ne -> P x /\ Forall P xs)
    with
    | Forall_nil _ => list_disc_nonempty_empty
    | Forall_cons y p f =>
      fun E => conj
              (eq_ind_r _ p (f_equal (hd x)  E))
              (eq_ind_r _ f (f_equal (@tl A) E))
    end (eq_sym L).

Fixpoint safe_lasts {A: Type} (l: list (list A))
         (NE: Forall (fun x => x <> @nil A) l) : list A :=
  match l as l0 return l = l0 -> list A with
  | [] => const []
  | hd :: tl =>
    fun E =>
      match Forall_uncons E NE with
      | conj Phd Ptl  =>
        safe_last hd Phd :: safe_lasts tl Ptl
      end
  end eq_refl.

Definition lrot {A: Type} (l: list A) : list A :=
  match l with
  | [] => []
  | hd :: tl => tl ++ [hd]
  end.

Fixpoint init {A: Type} (l: list A) : list A :=
  match l with
  | [] | [_] => []
  | hd :: tl => hd :: init tl
  end.

Definition rrot {A: Type}: list A -> list A :=
  let go := fix go l soFar :=
    match l with
    | [] => []
    | [x] => x :: soFar
    | hd :: tl => go tl (soFar ++ [hd])
    end in
  flip go [].

Theorem app_not_nil {A: Type}: forall l (a: A),
    l ++ [a] <> [].
Proof.
  intros l a contra.
  symmetry in contra.
  apply app_cons_not_nil in contra.
  apply contra.
Qed.

Lemma rrot_app {A: Type}: forall (l: list A) a,
    rrot (l ++ [a]) = a :: l.
Proof.
  induction l.
  - reflexivity.
  - intros b.
    simpl. unfold rrot. unfold flip.
    remember (l ++ [b]) as y.
    destruct y.
    + exfalso. apply (app_not_nil Heq
    +

Theorem rot_reverse {A: Type}: forall (l: list A),
    rrot (rev l) = rev (lrot l).
Proof.
  induction l.
  - reflexivity.
  - simpl.

    rewrite rev_unit.
    replace [a] with (rev [a]) by reflexivity.
    rewrite <- rev_app_distr.
    unfold app.
    rewrite <- rev_append_rev.
    simpl.

Theorem l_r_rot_inverse {A: Type}: forall (l: list A),
rrot (lrot l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- rev_involutive with (l := l ++ [a]).
    rewrite rev_unit.
    unfold rrot at 1.
    rewrite <- rev_app_distr.

Fixpoint iterate_n {A: Type} (f: A -> A) (n: nat) (x: A) : list A :=
  match n with
  | O    => []
  | S m => x :: iterate_n f m (f x)
  end.

Definition rots {A: Type} : list A -> list (list A) :=
  fun l => iterate_n lrot (length l) l.

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
