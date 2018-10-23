Require compcert.lib.Integers.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.EquivDec.

Instance Byte_EqDec   : EqDec Integers.Byte.int   eq := Integers.Byte.eq_dec.
Instance Int_EqDec    : EqDec Integers.Int.int    eq := Integers.Int.eq_dec.
Instance Int64_EqDec  : EqDec Integers.Int64.int  eq := Integers.Int64.eq_dec.
Instance Ptrofs_EqDec : EqDec Integers.Ptrofs.int eq := Integers.Ptrofs.eq_dec.

Instance EqDec_Z : EqDec Z eq := BinInt.Z.eq_dec.
