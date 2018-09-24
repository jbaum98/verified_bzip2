Require Import List.
Import ListNotations.

Definition run_length {A: Type} (eq: A -> A -> bool) :=
  let f := fun next newList =>
             match newList with
             | nil => [(next,1)]
             | (x,count)::tl => if eq x next then (x, count+1)::tl else (next,1) :: (x, count) :: tl
             end
  in List.fold_right f [].

Check run_length.
