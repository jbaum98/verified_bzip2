Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.DecidableClass.

Class LeDec {A : Type} (leA : relation A) :=
   le_dec : forall x y, { leA x y } + { leA y x}.

Class TotalOrderDec {A: Type} eqA `{E: EqDec A eqA} leA :=
  { TotalOrder_Reflexive  :> Reflexive leA;
    TotalOrder_Transitive :> Transitive leA;
    TotalOrder_Antisymmetric :> Antisymmetric A eqA leA;
    TotalOrder_dec :> LeDec leA
  }.

Instance LeDec_nat : LeDec Nat.le := Compare_dec.le_ge_dec.

Instance TotalOrderDec_nat : TotalOrderDec eq Nat.le :=
  { TotalOrder_Reflexive := Nat.le_refl;
    TotalOrder_Transitive := PeanoNat.Nat.le_trans;
    TotalOrder_Antisymmetric := Nat.le_antisymm;
  }.

Instance Equiv_Z : Equivalence (@eq Z) :=
  { Equivalence_Reflexive := @eq_refl Z; }.

Instance EqDec_Z : EqDec Z (@eq Z) := Z.eq_dec.

Instance LeDec_Z : LeDec Z.le.
Proof.
  unfold LeDec.
  intros.
  destruct (Z_le_dec x y).
  - left; omega.
  - right; omega.
Defined.

Instance TotalOrderDec_Z : TotalOrderDec eq Z.le :=
  { TotalOrder_Reflexive := Z.le_refl; }.
