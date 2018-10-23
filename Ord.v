Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require compcert.lib.Integers.

Require Import Instances.

(* A class for decidable ordering *)
Class LeDec (A : Type) (leA : relation A) :=
   le_dec : forall x y, { leA x y } + { leA y x}.

(* A class for decidable total order *)
Class TotalOrderDec (A : Type) eqA `{E : EqDec A eqA} leA :=
  { TotalOrder_Reflexive  :> Reflexive leA;
    TotalOrder_Transitive :> Transitive leA;
    TotalOrder_Antisymmetric :> Antisymmetric A eqA leA;
    TotalOrder_dec :> LeDec A leA
  }.

Definition lt {A: Type} `{TotalOrderDec A} :=
  fun x y => leA x y /\ ~ eqA x y.

Instance LeDec_nat : LeDec nat Nat.le := Compare_dec.le_ge_dec.

Instance TotalOrderDec_nat : TotalOrderDec nat eq Nat.le :=
  { TotalOrder_Reflexive := Nat.le_refl;
    TotalOrder_Transitive := PeanoNat.Nat.le_trans;
    TotalOrder_Antisymmetric := Nat.le_antisymm;
  }.

Instance LeDec_Z : LeDec Z Z.le.
Proof.
  unfold LeDec.
  intros.
  destruct (Z_le_dec x y).
  - left; omega.
  - right; omega.
Defined.

Instance TotalOrderDec_Z : TotalOrderDec Z eq Z.le :=
  { TotalOrder_Reflexive := Z.le_refl; }.

Theorem int_EqDec {A : Type} `{EqDec A eq}
        {unsigned : A -> Z} {repr : Z -> A}
        (repr_unsigned : forall x, repr (unsigned x) = x) :
  TotalOrderDec A eq (fun x y : A => Z.le (unsigned x) (unsigned y)).
Proof.
  apply Build_TotalOrderDec.
  - intro x. apply TotalOrder_Reflexive.
  - intros x y z. apply TotalOrder_Transitive.
  - intros x y Lxy Lyx.
    rewrite <- repr_unsigned at 1.
    rewrite <- repr_unsigned.
    f_equal.
    apply TotalOrder_Antisymmetric; auto.
  - intros x y. apply TotalOrder_dec.
Defined.

Instance Byte_EqDec : TotalOrderDec Integers.Byte.int _ _ :=
  int_EqDec Integers.Byte.repr_unsigned.
Instance Int_EqDec : TotalOrderDec Integers.Int.int _ _ :=
  int_EqDec Integers.Int.repr_unsigned.
Instance Int64_EqDec : TotalOrderDec Integers.Int64.int _ _ :=
  int_EqDec Integers.Int64.repr_unsigned.
Instance Ptrofs_EqDec : TotalOrderDec Integers.Ptrofs.int _ _ :=
  int_EqDec Integers.Ptrofs.repr_unsigned.
