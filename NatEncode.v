Require compcert.lib.Integers.
Require Import Coqlib.

Open Scope nat_scope.
Class NatEncode (A : Set) := {
  modulus : nat;
  encode : nat -> A;
  decode : A -> nat;
  nat_encode_inverse : forall x, x < modulus -> decode (encode x) = x
}.
Close Scope nat_scope.

Theorem int_nat_encode : forall {I: Set} {modulus: Z} {repr: Z -> I} {unsigned: I -> Z},
    modulus > 0 ->
    (forall x, unsigned (repr x) = x mod modulus) ->
    NatEncode I.
Proof.
  intros I modulus repr unsigned modulus_pos unsigned_repr_eq.
  eapply (Build_NatEncode I
            (Z.to_nat modulus)
            (fun x => repr (Z.of_nat x))
            (fun x => Z.to_nat (unsigned x))).
  intros.
  rewrite unsigned_repr_eq.
  rewrite <- Nat2Z.id in H at 1.
  rewrite <- Z2Nat.inj_lt in H; try omega.
  rewrite Z.mod_small; try omega.
  apply Nat2Z.id.
Defined.

Instance Byte_NatEncode : NatEncode Integers.Byte.int
  := int_nat_encode Integers.Byte.modulus_pos Integers.Byte.unsigned_repr_eq.
Instance Int_NatEncode : NatEncode Integers.Int.int
  := int_nat_encode Integers.Int.modulus_pos Integers.Int.unsigned_repr_eq.
Instance Int64_NatEncode : NatEncode Integers.Int64.int
  := int_nat_encode Integers.Int64.modulus_pos Integers.Int64.unsigned_repr_eq.
Instance Ptrofs_NatEncode : NatEncode Integers.Ptrofs.int
  := int_nat_encode Integers.Ptrofs.modulus_pos Integers.Ptrofs.unsigned_repr_eq.
