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

Section Permuter.
  Variable T : eqType.

  Definition permuter := forall {n} (s : n.-tuple T), 'S_n.

  Section FromFun.
    Variable f : seq T -> seq T.
    Implicit Type s : seq T.

    Hypothesis perm_f : forall s, perm_eql (f s) s.

    Program Fixpoint perm_ixs s : seq nat :=
      match s with
      | [::] => [::]
      | [:: x & t] =>
        let: RotToSpec k _ _ := rot_to (_ : x \in s) in
        rotr k (0 :: map succn (perm_ixs t))
      end.
    Next Obligation. by rewrite /in_mem /= eq_refl. Defined.

    Lemma perm_ixsE : forall x s,
        perm_ixs (x s) =

    Theorem perm_ixs_iota : forall s,
        perm_eq (perm_ixs s) (iota 0 (size s)).
    Proof.
      elim => [|x s IHs]; first done.
      rewrite .

  Program Definition

  (* Program Definition to_permuter (f : seq T -> seq T) (perm_f : forall s, perm_eql (f s) s) *)
  (*   : permuter := *)
  (*   fun n s => *)
  (*     match n with *)
  (*     | 0 => 1 *)
  (*     | S n => *)


Section Stable.
  Variable (T : eqType) (e : rel T).

  Definition stable_perm {n} (p : {perm 'I_n}) (s : n.-tuple T) : bool :=
    [forall i : 'I_n, forall j : 'I_n,
          (i < j) && (e (tnth s i) (tnth s j)) ==> (p i < p j)].

  Definition stable (f : permuter) : Prop := forall {n} (s : n.-tuple T),
      stable_perm (f n s) s.
End Stable.

Section StableSort.
  Implicit Types T : eqType.
  Variable n : nat.
  Variable sort : forall T, rel T -> n.-tuple T -> n.-tuple T.

  Hypothesis perm_sort : forall T (leT : rel T) (s : n.-tuple T),
      perm_eql (sort leT s) s.

  Lemma size_sort : forall T (leT : rel T) (s : n.-tuple T),
      size (sort leT s) = size s.
  Proof. by move=> T leT s; rewrite !size_tuple. Qed.

  Section SortPerm.
    Variables (T : eqType) (leT : rel T) (s : n.-tuple T).

    Definition perm_ixs : seq 'I_n :=
      sort [rel i j | leT (tnth s i) (tnth s j)] (ord_tuple n).

    Lemma size_perm_ixs : size perm_ixs == n.
    Proof. by rewrite size_sort size_tuple. Qed.

    Theorem perm_ixs_inj : injective (tnth (Tuple size_perm_ixs)).
    Proof.
      apply/injectiveP; rewrite /injectiveb /dinjectiveb map_tnth_enum.
      have Hperm_eq : perm_eq perm_ixs (ord_tuple n).
      - by apply /perm_eqlE /perm_sort.
          by rewrite (perm_eq_uniq Hperm_eq) val_ord_tuple enum_uniq.
    Qed.

    Definition perm_of_sort : 'S_n := perm perm_ixs_inj.
  End SortPerm.

  Definition stable_sort_tuple {T} leT (s : n.-tuple T) :=
      stable_perm leT (perm_of_sort leT s) s.
End StableSort.

Definition stable_sort {T : eqType} (sort : forall T, rel T -> n.-tuple)
