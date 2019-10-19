Require Import Coq.ZArith.ZArith.
Require Import Ascii.
Require Export Coq.Classes.EquivDec.
Require Import Coq.Logic.Eqdep_dec.

Require Export BWT.Sorting.Ord.

Instance EqDec_Z : EqDec Z eq := BinInt.Z.eq_dec.

Instance EqDec_ascii : EqDec ascii eq := ascii_dec.

Instance Preord_nat : Preord nat :=
  { le := Nat.le;
    le_trans := Nat.le_trans;
    le_total := Nat.le_ge_cases;
    le_dec := Compare_dec.le_dec;
  }.

Instance Ord_nat : Ord nat.
Proof.
  apply Build_Ord; intros x y [].
  apply Nat.le_antisymm; easy.
Qed.

Instance Preord_Z : Preord Z :=
  { le := Z.le;
    le_trans := Z.le_trans;
    le_total := Z.le_ge_cases;
    le_dec := Z_le_dec;
  }.

Instance Ord_Z : Ord Z.
Proof.
  apply Build_Ord; intros x y [].
  apply Z.le_antisymm; easy.
Qed.

Theorem int_Preord {A : Type}
        {unsigned : A -> Z} {repr : Z -> A}
        (repr_unsigned : forall x, repr (unsigned x) = x) :
  Preord A.
Proof.
  apply Build_Preord with (le := (fun x y : A => le (unsigned x) (unsigned y)));
    intros; eauto using le_trans, le_total, le_dec.
Defined.

Section ProofIrreleventZLt.
  Implicit Type c : comparison.

  Theorem comparison_eq_dec : forall c1 c2, { c1 = c2 } + { c1 <> c2 }.
  Proof.
    intros [] [];
    match goal with
    | |- { ?x = ?x } + { ?x <> ?x } => left; reflexivity
    | |- { ?x = ?y } + { ?x <> ?y } => right; intro c; inversion c
    end.
  Defined.

  Theorem comparison_eq_unicity : forall c1 c2 (H1 H2 : c1 = c2), H1 = H2.
  Proof. exact (UIP_dec comparison_eq_dec). Defined.

  Theorem Z_lt_eq_dec : forall m n (H1 H2 : Z.lt m n), { H1 = H2 } + { H1 <> H2 }.
  Proof. intros; left; apply comparison_eq_unicity. Defined.

  Theorem Z_lt_unicity : forall m n (H1 H2 : Z.lt m n) (E1 E2 : H1 = H2), E1 = E2.
  Proof. intros m n. exact (UIP_dec (Z_lt_eq_dec m n)). Defined.
End ProofIrreleventZLt.

Instance Ascii_Preord : Preord ascii.
Proof.
  apply Build_Preord with (le := (fun x y => le (nat_of_ascii x) (nat_of_ascii y))).
  - intros x y z; exact (le_trans (nat_of_ascii x) (nat_of_ascii y) (nat_of_ascii z)).
  - intros; exact (le_total (nat_of_ascii x) (nat_of_ascii y)).
  - intros; exact (le_dec (nat_of_ascii x) (nat_of_ascii y)).
Defined.

Theorem N_of_digits_inj : forall x y,
    length x = length y ->
    N_of_digits x = N_of_digits y ->
    x = y.
Proof.
  induction x; intros y HL E.
  cbn in HL. symmetry in HL. apply List.length_zero_iff_nil in HL. subst. easy.
  destruct y; [inversion HL|].
  cbn in E.
  remember (N_of_digits x) as nx.
  remember (N_of_digits y) as ny.
  destruct a; destruct b; destruct nx; destruct ny;
    try (cbn in E; inversion E); subst; f_equal; apply IHx; auto.
Qed.

Theorem nat_of_ascii_inj : forall x y,
    nat_of_ascii x = nat_of_ascii y ->
    x = y.
Proof.
  intros [] [] E.
  apply Nnat.N2Nat.inj in E.
  unfold N_of_ascii in E.
  apply N_of_digits_inj in E; [|reflexivity].
  inversion E; easy.
Qed.

Instance Ascii_Ord : Ord ascii.
Proof.
  apply Build_Ord; intros x y [].
  unfold le, Ascii_Preord in *.
  apply nat_of_ascii_inj.
  apply eqv_eq. split; easy.
Qed.
