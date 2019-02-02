Require Import mathcomp.fingroup.perm.
Require Import mathcomp.fingroup.morphism.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.path.
Require Import mathcomp.ssreflect.div.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.fingraph.
Require Import mathcomp.ssreflect.tuple.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.bigop.
Require Import mathcomp.ssreflect.prime.
Require Import mathcomp.ssreflect.finset.
Require Import mathcomp.ssreflect.binomial.
Require Import mathcomp.ssreflect.generic_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Stable.
  Variable (T : Type) (e : rel T).

  Definition stable {n} (s t : n.-tuple T) :=
    exists p : 'S_n, [forall i : 'I_n, forall (j : 'I_n | i < j),
                      e (tnth s i) (tnth s j) ==> (p i < p j)].
End Stable.

Section Sort.
  Variable sort : forall T : eqType, rel T -> seq T -> seq T.

  Hypothesis perm_sort
    : forall (T : eqType) (leT : rel T) (s : seq T), perm_eql (sort leT s) s.

  Lemma size_sort : forall (T : eqType) (leT : rel T) (s : seq T),
      size (sort leT s) = size s.
  Proof. by move=> T leT s; apply /perm_eq_size /perm_eqlE /perm_sort. Qed.

  Variables n : nat.
  Variables (T : eqType) (leT : rel T) (s : n.-tuple T).

  Definition perm_ixs : seq 'I_n :=
     sort [rel i j | leT (tnth s i) (tnth s j)] (ord_enum n).

  Lemma size_perm_ixs : size perm_ixs == n.
  Proof. by rewrite size_sort -(size_map val) val_ord_enum size_iota. Qed.

  Theorem perm_ixs_inj : injective (tnth (Tuple size_perm_ixs)).
  Proof.
    apply/injectiveP; rewrite /injectiveb /dinjectiveb map_tnth_enum.
    have Hperm_eq : perm_eq perm_ixs (ord_enum n).
    - by apply /perm_eqlE /perm_sort.
    by rewrite (perm_eq_uniq Hperm_eq) ord_enum_uniq.
  Qed.
End Sort.


Definition perm_of {T : eqType} sort perm_sort (leT : rel T) (s : seq T) :=
  perm (@perm_ixs_inj sort perm_sort _ T leT (in_tuple s)).

Check perm_of.



End Stable.
