Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.funind.Recdef.
Require Import Coq.Classes.EquivDec.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.

Require Import NatEncode.
Require Import SumboolIf.
Require Import Instances.

Import ListNotations.

Section RunLength.

  Open Scope nat_scope.

  Context `{A: Set}.

  Section Encode.
    Context `{ED : EqDec A eq}.

    (* modulus is the an upper bound on the length of a run. Useful if
       we want to later encode the run-length encoded list in some
       fixed-size binary representation, so we have a limit on the
       largest representable number. *)
    Variable modulus : nat.
    Hypothesis HModulusPos : modulus > 1.

    (* Add one element to a run-length encoded list l. *)
    Definition run_length_cons (x: A) (l: list (A * nat)) :=
      match l with
      | nil => [(x,1)]
      | (y,count)::tl =>
        if ((x == y) && (lt_dec (Nat.succ count) modulus))%sumbool
        then (x, Nat.succ count) :: tl
        else (x,1) :: (y, count) :: tl
      end.

    (* Run length encode an entire list. *)
    Definition run_length_encode : list A -> list (A * nat) :=
      List.fold_right run_length_cons [].

    (* A useful lemma to break down proofs about run_length_cons into 4 cases:
     - l = []
     - x = hd and count+1 < modulus
     - x = hd and count+1 >= modulus
     - x <> hd
     *)
    Lemma run_length_cons_cases :
      (* P is a relation between the inputs of run_length_cons and its output *)
      forall x l (P: A -> list (A * nat) -> list (A * nat) -> Prop),
        (* l = 0 *)
        P x [] [(x, 1)] ->
        (* x = hd and count < modulus *)
        (forall hd count tl,
            x = hd -> Nat.succ count < modulus ->
            P x ((hd,count)::tl) ((hd, Nat.succ count)::tl)) ->
        (* x = hd and count >= modulus *)
        (forall hd count tl,
            x = hd -> Nat.succ count >= modulus ->
            P x ((hd,count)::tl) ((x,1)::(hd,count)::tl)) ->
        (* x <> hd *)
        (forall hd count tl,
            x <> hd ->
            P x ((hd,count)::tl) ((x,1)::(hd,count)::tl)) ->
        P x l (run_length_cons x l).
    Proof with auto.
      intros x l P HBase HEq HOver HNew.
      induction l as [| p tl].
      - apply HBase.
      - destruct p as [hd count]. simpl.
        destruct (x == hd); unfold equiv in *; subst.
        + destruct (lt_dec (Nat.succ count) modulus).
          * apply HEq...
          * apply HOver... omega.
        + rewrite sumbool_and_false_l. apply HNew...
    Qed.

    (* run_bounded asserts that every run in l is less than or equal to
     modulus *)
    Definition run_bounded (l: list (A * nat)) :=
      Forall (fun x => x < modulus) (map snd l).

    (* run_length_cons preserves run_bounded *)
    Lemma run_length_cons_bounded : forall x l,
        run_bounded l -> run_bounded (run_length_cons x l).
    Proof.
      intros x l.
      apply run_length_cons_cases;
        try (intros hd count tl HEq HLT HInd);
        simpl; try (inversion HInd; subst); econstructor; auto; simpl; try omega.
    Qed.

    (* run_length_encode preserves run_bounded *)
    Theorem run_length_bounded : forall l,
        run_bounded (run_length_encode l).
    Proof.
      induction l.
      - econstructor.
      - unfold run_length_encode. simpl.
        apply run_length_cons_bounded; auto.
    Qed.
  End Encode.

  Section Decode.
    Open Scope sumbool.

    (* We define a measure that will decrease on each recursive call to
     run_length_decode, so that we can prove that it terminates. To
     that end, we measure the cons cell itself as 1 so that the
     measure decreases when we remove a cons cell with a 0 run.*)
    Fixpoint run_length_measure (l : list (A * nat)) :=
      match l with
      | [] => 0
      | (_,count)::tl =>
        if count == 0
        then 1 + run_length_measure tl
        else 1 + count + run_length_measure tl
      end.

    (* decode a run-length encoded list *)
    Function run_length_decode (l : list (A * nat)) { measure run_length_measure l } :=
      match l with
      | [] => []
      | (x,count)::tl =>
        if lt_dec 0 count
        then x :: run_length_decode ((x, Nat.pred count) :: tl)
        else run_length_decode tl
      end.
    Proof.
      - intros l p tl x count HP HL HLT _. simpl.
        destruct (count == 1) as [Eq | NEq]; unfold equiv in *.
        + subst. simpl. omega.
        + destruct (Nat.pred count == 0); destruct (count == 0);
            unfold equiv in *; try omega.
      - intros l p tl x count HP HL HLT _. simpl.
        destruct (count == 0); unfold equiv in *; try omega.
    Defined.
  End Decode.

  (* run_length_decode-ing the result of a run_length_cons is the same
     as regular cons followed by run_length_decode *)
  Lemma run_length_cons_invert `{EqDec A eq}: forall modulus x l,
      modulus > 1 ->
      run_length_decode (run_length_cons modulus x l) = x :: run_length_decode l.
  Proof.
    intros modulus x l HMaxRunPos.
    apply run_length_cons_cases;
      intros; simpl;
        do 2 (try (rewrite run_length_decode_equation);
              simpl; subst; auto; try reflexivity).
  Qed.

  (* run_length_decode undoes run_length_encode *)
  Theorem run_length_invert `{EqDec A eq}: forall modulus l,
      modulus > 1 ->
      run_length_decode (run_length_encode modulus l) = l.
  Proof.
    intros modulus l HMaxRunPos; revert l.
    induction l as [| hd tl].
    - rewrite run_length_decode_equation. reflexivity.
    - simpl. rewrite run_length_cons_invert; auto.
      f_equal. apply IHtl.
  Qed.

End RunLength.

Section Run_Encoding.

  Open Scope nat_scope.

  Generalizable Variable A.
  Context `{NE : NatEncode A}.

  Definition encode_runs : list (A * nat) -> list A :=
    let flatten_run p : list A :=
        match p with (x, count) => [x; encode count] end
    in flat_map flatten_run.

  Fixpoint decode_runs (l: list A) : list (A * nat) :=
    match l with
    | x::count::tl => (x, decode count) :: decode_runs tl
    | _ => []
    end.

  Theorem encode_runs_inverse : forall l,
      Forall (fun x => x < modulus) (map snd l) ->
      decode_runs (encode_runs l) = l.
  Proof.
    induction l.
    - intros; reflexivity.
    - intros HBounded.
      inversion HBounded; subst; clear HBounded.
      destruct a as [x count]. simpl.
      rewrite IHl; auto. do 2 f_equal.
      apply nat_encode_inverse.
      simpl in H1; auto.
  Qed.

End Run_Encoding.

Section Bytes.

  Local Definition modulus := Z.to_nat Byte.modulus.

  Open Scope Z_scope.
  Lemma two_p_gt_ONE : forall x,
      0 < x -> two_p x > 1.
  Proof.
    intros.
    replace 1 with (two_p 0) by reflexivity.
    apply Z.lt_gt.
    apply two_p_monotone_strict.
    omega.
  Qed.

  Lemma modulus_gt_one : 1 < Byte.modulus.
    rewrite Byte.modulus_power.
    apply Z.gt_lt. apply two_p_gt_ONE.
    generalize Byte.wordsize_pos; omega.
  Qed.

  Open Scope nat_scope.

  Theorem HMaxRunPos : modulus > 1.
  Proof.
    unfold modulus.
    pose proof modulus_gt_one.
    apply (Z2Nat.inj_lt 1 _); try omega.
  Qed.

  Definition run_length_encode_bytes (l: list byte) : list byte :=
    encode_runs (run_length_encode modulus l).

  Definition run_length_decode_bytes (l: list byte) : list byte :=
    run_length_decode (decode_runs l).

  Theorem run_length_bytes_invert : forall l,
      run_length_decode_bytes (run_length_encode_bytes l) = l.
  Proof.
    intros.
    pose proof HMaxRunPos.
    unfold run_length_encode_bytes, run_length_decode_bytes.
    rewrite encode_runs_inverse.
    rewrite run_length_invert; auto.
    apply run_length_bounded; auto.
  Qed.
End Bytes.
