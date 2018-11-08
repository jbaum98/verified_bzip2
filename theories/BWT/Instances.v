Require compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Require Export Coq.Classes.EquivDec.

Require Export BWT.Sorting.Ord.

Instance Byte_EqDec   : EqDec Integers.Byte.int   eq := Integers.Byte.eq_dec.
Instance Int_EqDec    : EqDec Integers.Int.int    eq := Integers.Int.eq_dec.
Instance Int64_EqDec  : EqDec Integers.Int64.int  eq := Integers.Int64.eq_dec.
Instance Ptrofs_EqDec : EqDec Integers.Ptrofs.int eq := Integers.Ptrofs.eq_dec.

Instance EqDec_Z : EqDec Z eq := BinInt.Z.eq_dec.

Instance Ord_nat : Ord nat :=
  { le := Nat.le;
    le_trans := Nat.le_trans;
    le_total := Nat.le_ge_cases;
    le_dec := Compare_dec.le_dec;
  }.

Instance Ord_Z : Ord Z :=
  { le := Z.le;
    le_trans := Z.le_trans;
    le_total := Z.le_ge_cases;
    le_dec := Z_le_dec;
  }.

Theorem int_Ord {A : Type}
        {unsigned : A -> Z} {repr : Z -> A}
        (repr_unsigned : forall x, repr (unsigned x) = x) :
  Ord A.
Proof.
  apply Build_Ord with (le := (fun x y : A => le (unsigned x) (unsigned y)));
    intros; eauto using le_trans, le_total, le_dec.
Defined.

Instance Byte_Ord : Ord Integers.Byte.int :=
  int_Ord Integers.Byte.repr_unsigned.
Instance Int_Ord : Ord Integers.Int.int :=
  int_Ord Integers.Int.repr_unsigned.
Instance Int64_Ord : Ord Integers.Int64.int :=
  int_Ord Integers.Int64.repr_unsigned.
Instance Ptrofs_Ord : Ord Integers.Ptrofs.int :=
  int_Ord Integers.Ptrofs.repr_unsigned.
