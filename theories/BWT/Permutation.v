Require Import mathcomp.fingroup.perm.
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

Section HilbertSaxiom.

  Variables A B C : Prop.

  Lemma HilbertS : (A -> B -> C) -> (A -> B) ->
                   A -> C.
  Proof.
    move=> hAiBiC hAiB hA.
    move: hAiBiC.
    apply.
    - by []. by apply: hAiB.
  Qed.

  Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

  Lemma HilbertS2 : C.
  Proof.
    apply: hAiBiC; first by apply: hA.
    exact: hAiB.
  Qed.

  Lemma HilbertS3 : C.
  Proof. by apply : hAiBiC; last exact : hAiB. Qed.
End HilbertSaxiom.

Print bool.

Section Symmetric_Conjunction_Disjunction.

  Lemma andb_sym : forall A B : bool, A && B -> B && A.
  Proof.
    case.
    - by case.
    by [].
  Qed.

  Lemma and_sym : forall A B : Prop,
      A /\ B -> B /\ A.
  Proof.
    move=> A B.
    case.
    done.
  Qed.

  Lemma or_sym : forall A B : Prop,
      A \/ B -> B \/ A.
  Proof.
    move=> A B [hA | hB].
    - by apply: or_intror.
    - by apply: or_introl.
  Qed.

  Lemma or_sym2 : forall A B : bool,
      A \/ B -> B \/ A.
  Proof.
    by move=> [] [] AorB; apply/orP; move/orP: AorB.
  Qed.
End Symmetric_Conjunction_Disjunction.

Section R_sym_trans.
  Variables (D : Type) (R : D -> D -> Prop).

  Hypothesis R_sym : forall x y, R x y -> R y x.

  Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

  Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
  Proof.
    move=> x [y Rxy].
    by apply: R_trans (R_sym Rxy).
  Qed.
End R_sym_trans.

Section Smullyan_drinker.

  Variables (D : Type) (P : D -> Prop).

  Hypothesis (d : D) (EM : forall A, A \/ ~A).

  Lemma drinker : exists x, P x -> forall y, P y.
  Proof.
    case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy].
    - by exists y.
    - exists d => _ y.
      case: (EM (P y)) => // notPy.
      case nonotPy. by exists y.
  Qed.
End Smullyan_drinker.

Section Equality.

  Variable f : nat -> nat.

  Hypothesis f00 : f 0 = 0.

  Lemma fkk : forall k, k = 0 -> f k = k.
    by move=> k ->.
  Qed.

  Variables (D : eqType) (x y : D).

  Lemma eq_prop_bool : x = y -> x == y.
  Proof. by move/eqP. Qed.
End Equality.

Section Using_Definition.

  Variable U : Type.

  Definition set := U -> Prop.

  Definition subset (A B : set) :=
    forall x, A x -> B x.

  Definition transitive (T : Type) (R : T -> T -> Prop) :=
    forall x y z, R x y -> R y z -> R x z.

  Lemma subset_trans : transitive subset.
  Proof.
    move=> x y z subxy subyz t.
    by move /subxy /subyz.
  Qed.

End Using_Definition.

Section EDiv.
  Definition edivn_rec d :=
    fix loop (m q : nat) {struct m} :=
      if m - d is m'.+1
      then loop m' q.+1
      else (q, m).

  Definition edivn m d :=
    if d > 0
    then edivn_rec d.-1 m 0
    else (0, m).

  CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
    EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) :
      edivn_spec m d (q, r).

  Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
  Proof.
    rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
    elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
    rewrite subn_if_gt; case: ltnP => [// | le_dm].
    rewrite -{1}(subnK le_dm) -addSn addSnnS [_ + d.+1]addnC addnA -mulSnr; apply: IHn.
    apply: leq_trans le_mn; exact : leq_subr.
  Qed.

  Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
  Proof.
    move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
    case: edivnP lt_rd => q' r'; rewrite d_pos /=.
    wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
    rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
    by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
  Qed.
End EDiv.

Locate "^~".

Search _ perm_eq.

Section Relates.
  Variable T : eqType.
  Variable n : nat.

  Implicit Type p : 'S_n.

  Definition perm_relates p :=
    [rel x y : n.-tuple T | [forall i, tnth x i == tnth y (p i)]].
End Relates.

Let n := 3.

Program Definition zero : 'I_n := Ordinal (_ : 0 < n).
Program Definition one  : 'I_n := Ordinal (_ : 1 < n).
Program Definition two  : 'I_n := Ordinal (_ : 2 < n).

Definition p := tperm zero one.

Goal p zero == one.
Proof. by case: tpermP. Qed.

Goal p one == zero.
Proof. by case: tpermP. Qed.

Goal p two == two.
Proof. by case: tpermP. Qed.

Eval compute in ((tperm zero one) zero).
(*
     = perm (can_inj (tperm_proof (Ordinal is_true_true) (Ordinal is_true_true)))
         (Ordinal is_true_true)
     : ordinal_finType n
 *)


Check @forallP (ordinal_finType 3) _.


Goal perm_relates _ p x y.
Proof. apply/forallP => i.
       case: tpermP.
         move => H. by rewrite H.
         move => H. by rewrite H.
         move => HZ HO.
         suff thm: i = two.
           by rewrite {}thm.
Admitted.
