Require Import fcf.EqDec.
Require compcert.lib.Integers.
Require Import Coqlib.

Instance Byte_EqDec   : EqDec Integers.Byte.int   := dec_EqDec Integers.Byte.eq_dec.
Instance Int_EqDec    : EqDec Integers.Int.int    := dec_EqDec Integers.Int.eq_dec.
Instance Int64_EqDec  : EqDec Integers.Int64.int  := dec_EqDec Integers.Int64.eq_dec.
Instance Ptrofs_EqDec : EqDec Integers.Ptrofs.int := dec_EqDec Integers.Ptrofs.eq_dec.
Instance Z_EqDec : EqDec Z := dec_EqDec zeq.
