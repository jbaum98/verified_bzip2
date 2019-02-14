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

Search _ perm_eq.
Eval compute in perm_eq [:: 1; 3; 2] [:: 1; 2; 3].

Inductive Permutation {A} : seq A -> seq A -> Type :=
| perm_nil: Permutation [::] [::]
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Theorem perm_eq_nil {T : eqType} : forall ys : seq T,
    perm_eq [::] ys -> ys = [::].
Proof.
  elim; first by move=>_.
  move=>a l IH; rewrite /perm_eq; move/allP.
  rewrite /=; move/(_ a); rewrite eq_refl /=.
  rewrite /in_mem /=.
  have : 0 == 1 + _ = false. by move=>n. move ->.
  rewrite eq_refl Bool.orb_true_l.
  by move=>contra; exfalso; apply/notF; apply contra.
Qed.

Theorem Permutation_perm_eqlP {T : eqType}: forall xs ys : seq T,
    perm_eq xs ys -> Permutation xs ys.
Proof.
  elim; first by move=>ys; move/perm_eq_nil ->; constructor.
  move=>a l IH ys; rewrite /perm_eq; move/allP.
Admitted.

Inductive In {T : Type} (x : T) : seq T -> Type :=
| in_hd : forall t, In x [:: x & t]
| in_cons : forall y l, In x l -> In x (y :: l).

Definition ix_in {T : Type} (x : T)  : forall l : seq T, In x l -> nat :=
  fix f l HI :=
    match HI with
    | in_hd _ => 1
    | in_cons _ t HI' => (f t HI').+1
    end.
Hint Constructors In.

Section InPair.
  Variables A B : eqType.
  Implicit Types (a : A) (b : B).

  Theorem in_pair_fst : forall a b l,
      ((a, b) \in l) = (b \in [seq p.2 | p <- l & p.1 == a]).
  Proof.
    move=> a b; elim; first done.
    case=> [a' b'] l IH.
    rewrite seq.in_cons /=.
    have : (a, b) == (a' , b') = ((a == a') && (b == b')) by done.
    move ->; rewrite (eq_sym a) /=.
    case (a' == a).
    - by rewrite map_cons /= seq.in_cons IH.
    - by rewrite -IH.
  Qed.
End InPair.

Section Comp.
  Variable T : eqType.
  Implicit Types xs ys : seq T.

  Fixpoint calc_perm xs ys : seq nat :=
    match xs with
    | [::] => [::]
    | [:: h & t] => find (eq_op h) ys :: calc_perm t ys
    end.

  Theorem calc_perm_size : forall xs ys,
      size (calc_perm xs ys) = size xs.
  Proof.
    elim; first done.
    by move=>h t IH ys; rewrite /= IH.
  Qed.

  Fixpoint tag_reps xs : seq (T * nat) :=
    match xs with
    | [::] => [::]
    | [:: h & t] => (h, count_mem h t) :: tag_reps t
    end.

  Lemma iota_rev : forall n i,
      iota i (n.+1) = rcons (iota i n) (i+n).
  Proof.
    elim=>n; first by rewrite -plusE -plus_n_O.
    move=> IH i.
    remember (n.+1) as n'. rewrite [iota i _]/=.
    rewrite {}IH; subst n'.
    by rewrite [iota i _]/= rcons_cons addSnnS.
  Qed.

  Theorem tag_reps_filter_snd : forall x xs,
      [seq p.2 | p <- tag_reps xs & p.1 == x] = rev (iota 0 (count_mem x xs)).
  Proof.
    move=> x; elim; first done.
    move=> h t IH.
    rewrite [count_mem _ _]/= [LHS]/=.
    case E : (h == x); last by apply IH.
    move/eqP in E; subst h.
    by rewrite map_cons iota_rev rev_rcons IH.
  Qed.

  Lemma iota_ubound : forall n i,
      all [ pred x | x < (i + n) ] (iota i n).
  Proof.
    elim=>[|n IH] i; first done.
    rewrite /= leqnn -addSnnS ltn_addr /=; last by rewrite ltnSn.
    rewrite addSnnS /=.
    rewrite /=; apply/andP; split.
    elim=>[|n IH] i; first by done.
    apply/negPf; rewrite /=.

  Theorem tag_reps_uniq : forall xs,
      uniq (tag_reps xs).
  Proof.
    elim; first done.
    move=> x t IH; rewrite /=.
    rewrite {}IH Bool.andb_true_r.
    apply/negPf.
    rewrite in_pair_fst tag_reps_filter_snd.
End Comp.

Eval compute in calc_perm [:: 2; 1; 3] [:: 3; 1; 2].

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
