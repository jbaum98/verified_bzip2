Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import Omega.
Require Import Coq.Bool.Bool.

Require Import VST.fcf.EqDec.

Open Scope eq_scope.
Open Scope bool_scope.

Section RunLength.

  Generalizable Variable A.
  Context `{EqDec A}.

  Definition run_length_cons (maxRun : nat) (x: A) (l: list (A * nat)) :=
    match l with
    | nil => [(x,1)]
    | (y,count)::tl => if (x ?= y) && (ltb count maxRun)
                      then (x, count+1)::tl
                      else (x,1) :: (y, count) :: tl
    end.

  Definition run_length_encode maxRun :=
    List.fold_right (run_length_cons maxRun) [].

  Definition run_length_cons_inverse (x: (A * nat)) (l: list A) :=
    match x with
    | (el, count) => List.repeat el count ++ l
    end.

  Definition run_length_decode (l : list (A * nat)) :=
    List.fold_right run_length_cons_inverse [] l.

  Definition run_bounded maxRun (l: list (A * nat)) :=
    Forall (fun x => x <= maxRun) (map snd l).

  Theorem run_length_cons_bounded : forall maxRun x l,
      maxRun > 0 ->
      run_bounded maxRun l -> run_bounded maxRun (run_length_cons maxRun x l).
  Proof.
    intros. destruct l.
    - (* empty list *)
      unfold run_bounded. simpl.
      econstructor. omega. econstructor.
    - (* nonempty list *)
      destruct p. simpl.
      destruct (EqDec_dec H x a).
      + (* x equal to head of list *)
        destruct (eqb_leibniz x a) as [_ L].
        specialize (L e). rewrite L. simpl.
        destruct (Nat.ltb_spec n maxRun).
        * (* n < maxRun *)
          unfold run_bounded in *. simpl.
          econstructor. omega.
          inversion H1. auto.
        * (* n >= maxRun *)
          unfold run_bounded in *. simpl.
          repeat (econstructor; try omega; auto).
      + (* x is new *)
        destruct (eqb_false_iff H x a) as [_ L].
        specialize (L n0). rewrite L. simpl.
        repeat (econstructor; try omega; auto).
  Qed.

End RunLength.

Compute run_length_encode 2 [1; 1; 1; 2; 2; 3; 2; 1].
Compute run_length_decode (run_length_encode 2 [1; 1; 1; 2; 2; 3; 2; 1]).
