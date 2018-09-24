Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.

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

End RunLength.

Compute run_length_encode [1; 1; 1; 2; 2; 3; 2; 1].
Compute run_length_decode (run_length_encode [1; 1; 1; 2; 2; 3; 2; 1]).
