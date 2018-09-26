Require Import List.
Import ListNotations.
Require Import Coq.Init.Nat.
Require Import Omega.
Require Import Coq.Bool.Bool.
Require Import Recdef.

Require Import VST.fcf.EqDec.

Section RunLength.

  Open Scope bool_scope.
  Open Scope nat_scope.
  Open Scope eq_scope.

  Generalizable Variable A.
  Context `{ED : EqDec A}.

  (* maxRun is the maximum length of a run. Useful if we want to
       later encode the run-length encoded list in some fixed-size
       binary representation, so we have a limit on the largest
       representable number. *)
  Variable maxRun : nat.
  Hypothesis HMaxRunPos : maxRun > 0.

  (* Add one element to a run-length encoded list l. *)
  Definition run_length_cons (x: A) (l: list (A * nat)) :=
    match l with
    | nil => [(x,1)]
    | (y,count)::tl =>
      if (x ?= y) && (count <? maxRun)
      then (x, Nat.succ count) :: tl
      else (x,1) :: (y, count) :: tl
    end.

  (* Run length encode an entire list. *)
  Definition run_length_encode :=
    List.fold_right run_length_cons [].

  Lemma run_length_cons_cases : forall x l
                                  (P: A -> list (A * nat) -> list (A * nat) -> Prop),
      P x [] [(x, 1)] ->
      (forall hd count tl, x = hd -> count < maxRun ->
                      P x ((hd,count)::tl) ((hd, Nat.succ count)::tl)) ->
      (forall hd count tl, x = hd -> count >= maxRun ->
                      P x ((hd,count)::tl) ((x,1)::(hd,count)::tl)) ->
      (forall hd count tl, x <> hd -> P x ((hd,count)::tl) ((x,1)::(hd,count)::tl)) ->
      P x l (run_length_cons x l).
  Proof.
    intros x l P HBase HEq HOver HNew.
    induction l as [| p tl].
    - apply HBase.
    - destruct p as [hd count].
      destruct (EqDec_dec _ x hd) as [Eq | Neq].
      + simpl. rewrite (proj2 (eqb_leibniz _ _) Eq).
        destruct (le_lt_dec maxRun count) as [ Ge | Lt ].
        * assert (Ge': count >= maxRun) by omega.
          rewrite (proj2 (Nat.ltb_ge _ _) Ge'). simpl.
          apply HOver; auto.
        * rewrite (proj2 (Nat.ltb_lt _ _) Lt). simpl.
          subst x. apply HEq; auto.
      + simpl. rewrite (proj2 (eqb_false_iff _ _ _) Neq).
        rewrite andb_false_l.
        apply HNew; auto.
  Qed.

  Definition run_bounded (l: list (A * nat)) :=
    Forall (fun x => x <= maxRun) (map snd l).

  Lemma run_length_cons_bounded : forall x l,
      run_bounded l -> run_bounded (run_length_cons x l).
  Proof.
    intros x l.
    apply run_length_cons_cases;
      try (intros hd count tl HEq HLT HInd);
      simpl; try (inversion HInd; subst); econstructor; auto; simpl; try omega.
  Qed.

  Theorem run_length_bounded : forall l,
      run_bounded (run_length_encode l).
  Proof.
    induction l.
    - econstructor.
    - unfold run_length_encode. simpl.
      apply run_length_cons_bounded; auto.
  Qed.

  (* We define a measure that will decrease on each recursive call to
     run_length_decode, so that we can prove that it terminates. To
     that end, we measure the cons cell itself as 1 so that the
     measure decreases when we remove a cons cell with a 0 run.*)
  Fixpoint run_length_measure (l : list (A * nat)) :=
    match l with
    | [] => 0
    | (_,count)::tl =>
      if count ?= 0
      then 1 + run_length_measure tl
      else 1 + count + run_length_measure tl
    end.

  Function run_length_decode (l : list (A * nat)) { measure run_length_measure l } :=
    match l with
    | [] => []
    | (x,count)::tl =>
      if 0 <? count
      then x :: run_length_decode ((x, Nat.pred count) :: tl)
      else run_length_decode tl
    end.
  Proof.
    - intros l p tl x count HP HL HLT. simpl.
      destruct (Nat.eq_dec 1 count) as [Eq | NEq].
      + subst. simpl. omega.
      + apply Nat.ltb_lt in HLT.
        assert (HLT': 0 < Nat.pred count) by omega.
        rewrite (proj2 (Nat.leb_gt _ _) HLT').
        rewrite (proj2 (Nat.leb_gt _ _) HLT). simpl.
        omega.
    - intros l p tl x count HP HL HLT. simpl.
      rewrite Nat.ltb_antisym in HLT.
      rewrite (proj1 (negb_false_iff _) HLT).
      simpl. omega.
  Defined.

  Lemma run_length_cons_invert : forall x l,
      run_length_decode (run_length_cons x l) = x :: run_length_decode l.
  Proof.
    intros x l.
    apply run_length_cons_cases;
      intros; simpl;
        do 2 (try (rewrite run_length_decode_equation);
              simpl; subst; try reflexivity).
  Qed.

  Theorem run_length_invert : forall l,
    run_length_decode (run_length_encode l) = l.
  Proof.
    induction l as [| hd tl].
    - rewrite run_length_decode_equation. reflexivity.
    - simpl. rewrite run_length_cons_invert.
      f_equal. apply IHtl.
  Qed.

End RunLength.
