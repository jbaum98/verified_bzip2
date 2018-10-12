Require compcert.lib.Integers.
Require compcert.lib.Coqlib.
Require Import VST.msl.eq_dec.

Instance Byte_EqDec   : EqDec Integers.Byte.int   := Integers.Byte.eq_dec.
Instance Int_EqDec    : EqDec Integers.Int.int    := Integers.Int.eq_dec.
Instance Int64_EqDec  : EqDec Integers.Int64.int  := Integers.Int64.eq_dec.
Instance Ptrofs_EqDec : EqDec Integers.Ptrofs.int := Integers.Ptrofs.eq_dec.

Instance Z_EqDec : EqDec Z := zeq.
