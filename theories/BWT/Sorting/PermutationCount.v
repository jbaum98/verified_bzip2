Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.omega.Omega.

Require Import BWT.Lib.List.
Require Import BWT.Lib.Sumbool.

Section PermutationCount.
  Context {A : Type} `(ED : EqDec A eq).

  Implicit Type l : list A.

  Definition PermutationCount l l' : Prop :=
    forall x, count_occ equiv_dec l x = count_occ equiv_dec l' x.

  Theorem PermutationCount_iff : forall l l',
      Permutation l l' <-> PermutationCount l l'.
  Proof.
    unfold PermutationCount.
    intros l l'. split.
    - intros P; induction P.
      + reflexivity.
      + intros y; destruct (x == y);
          [rewrite !count_occ_cons_eq|rewrite !count_occ_cons_neq];
          [f_equal|..]; easy.
      + intros z.
        destruct (y == z); destruct (x == z);
          repeat match goal with
          | H : ?a === ?b |- _ => rewrite (count_occ_cons_eq equiv_dec _ H)
          | H : ?a =/= ?b |- _ => rewrite (count_occ_cons_neq equiv_dec _ H)
          end; easy.
      + intros. eapply eq_trans; [apply IHP1|apply IHP2].
    - revert l'. induction l; intros l' HCO.
      + replace l' with (@nil A); [constructor|].
        symmetry. eapply count_occ_inv_nil.
        cbn in HCO. symmetry in HCO. apply HCO.
      + assert (In a l'). {
          eapply (count_occ_In equiv_dec).
          specialize (HCO a).
          cbn in HCO.
          rewrite if_true in HCO by reflexivity.
          rewrite <- HCO. omega.
        }
        edestruct (in_split a l') as [L [R HLR]]; auto.
        eapply Permutation_trans; [|rewrite HLR; apply Permutation_middle].
        constructor. apply IHl.
        intros. destruct (a == x).
        * apply Nat.succ_inj.
          rewrite <- count_occ_remove_eq.
          rewrite <- count_occ_cons_eq with (x := a); [|auto].
          rewrite <- e, <- HLR. apply HCO.
        * rewrite <- @count_occ_remove_neq with (a := a); auto.
          rewrite <- HLR.
          rewrite <- HCO, count_occ_cons_neq; auto.
  Qed.
End PermutationCount.
