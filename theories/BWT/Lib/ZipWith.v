Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Section ZipWith.
  Context {A B C : Type}.

  Variable f : A -> B -> C.

  Fixpoint zipWith (a : list A) (b : list B) : list C :=
    match (a, b) with
    | (ahd :: atl, bhd :: btl) => f ahd bhd :: zipWith atl btl
    | _ => []
    end.

  Theorem zipWith_nil_l : forall b,
      zipWith [] b = [].
  Proof. reflexivity. Qed.

  Theorem zipWith_nil_r : forall a,
      zipWith a [] = [].
  Proof. destruct a; reflexivity. Qed.

  Theorem zipWith_length : forall a b,
      length (zipWith a b) = Nat.min (length a) (length b).
  Proof.
    induction a; intros; [reflexivity|].
    destruct b; [reflexivity|].
    cbn. f_equal. auto.
  Qed.

  Lemma zipWith_length_eq : forall a b,
      length a = length b ->
      length (zipWith a b) = length a /\ length (zipWith a b) = length b.
  Proof. intros. rewrite !zipWith_length, !H, !Nat.min_id. intuition. Qed.
End ZipWith.

Lemma zipWith_combine {A B} : forall (a : list A) (b : list B),
    zipWith pair a b = combine a b.
Proof. reflexivity. Qed.


Section Pairs.
  Context {A B : Type}.

  Lemma not_in_pair : forall (l : list (A * B)) a b,
       ~ In a (fst (split l)) \/ ~ In b (snd (split l)) -> ~ In (a, b) l.
  Proof.
    intros l a b.
    remember (a, b) as p;
    replace a with (fst p) by (subst; easy); replace b with (snd p) by (subst; easy).
    intros []; intro c; [apply in_split_l in c|apply in_split_r in c]; contradiction.
  Qed.

  Theorem NoDup_pair : forall l : list (A * B),
      NoDup (fst (split l)) \/ NoDup (snd (split l)) -> NoDup l.
  Proof.
    induction l; cbn; [intuition constructor|].
    destruct a; cbn. destruct (split l) eqn:HS. cbn.
    intros []; inversion H; subst; clear H;
      (constructor; [apply not_in_pair; rewrite HS; auto|apply IHl; intuition]).
  Qed.

  Lemma map_split : forall l : list (A * B),
      split l = (map fst l, map snd l).
  Proof.
    induction l as [|[a b] l]; [reflexivity|]; cbn; destruct (split l).
    inversion IHl; subst. easy.
  Qed.
End Pairs.

Section ZipIx.
  Context {A : Type}.

  Fixpoint zipIx (i : nat) (l : list A) : list (A * nat) :=
    match l with
    | [] => []
    | a :: l => (a, i) :: zipIx (S i) l
    end.

  Theorem zipIx_correct : forall l i, zipIx i l = combine l (seq i (length l)).
  Proof.
    induction l; intros; [reflexivity|].
    cbn. f_equal. apply IHl.
  Qed.

  Theorem zipIx_NoDup : forall l i, NoDup (zipIx i l).
  Proof.
    intros.
    rewrite zipIx_correct.
    apply NoDup_pair. right.
    rewrite combine_split; [|rewrite seq_length; easy].
    cbn. apply seq_NoDup.
  Qed.

  Theorem zipIx_length : forall l i, length (zipIx i l) = length l.
  Proof.
    intros. rewrite zipIx_correct.
    rewrite <- zipWith_combine.
    apply zipWith_length_eq.
    symmetry; apply seq_length.
  Qed.
End ZipIx.

Section ZipOcc.
  Context {A : Type} `{E: EqDec A eq}.

  Fixpoint zipOcc (l : list A) : list (A * nat) :=
    match l with
    | [] => []
    | a :: l => (a, count_occ E l a) :: zipOcc l
    end.

  Fixpoint occs (l : list A) :=
    match l with
    | [] => []
    | a :: l => count_occ E l a :: occs l
    end.

  Remark occs_nil_iff : forall l,
      occs l = [] <-> l = [].
  Proof.
    split; [|intros; subst; easy].
    induction l; [reflexivity|].
    simpl. intro c; inversion c.
  Qed.

  Remark zipOcc_nil_iff : forall l,
      zipOcc l = [] <-> l = [].
  Proof.
    split; [|intros; subst; easy].
    induction l; [reflexivity|].
    simpl. intro c; inversion c.
  Qed.

  Theorem zipOcc_correct : forall l,
      zipOcc l = combine l (occs l).
  Proof.
    induction l; intros; [reflexivity|].
    cbn. f_equal. apply IHl.
  Qed.

  Theorem occs_length : forall l,
      length (occs l) = length l.
  Proof. induction l; cbn; auto. Qed.

  Theorem zipOcc_length : forall l,
      length (zipOcc l) = length l.
  Proof.
    intros.
    rewrite zipOcc_correct, <- zipWith_combine.
    apply zipWith_length_eq.
    auto using occs_length.
  Qed.

  Lemma count_occ_remove_eq : forall a L R,
      count_occ E (L ++ a :: R) a = S (count_occ E (L ++ R) a).
  Proof.
    induction L; intros.
    - cbn. destruct (E a a); [reflexivity|pose proof eq_refl a; contradiction].
    - cbn. destruct (E a0 a); rewrite IHL; reflexivity.
  Qed.

  Lemma count_occ_remove_neq : forall a L R x,
      a <> x ->
      count_occ E (L ++ a :: R) x = count_occ E (L ++ R) x.
  Proof.
    induction L; intros.
    - cbn. destruct (E a x); [contradiction|easy].
    - cbn. destruct (E a0 x); rewrite IHL; auto.
  Qed.

  Theorem count_occ_Permutation : forall l l',
      Permutation l l' <-> forall x, count_occ E l x = count_occ E l' x.
  Proof.
    intros l l'. split.
    - intros P; induction P.
      + reflexivity.
      + intros y.
        destruct (E x y);
          [rewrite !count_occ_cons_eq|rewrite !count_occ_cons_neq]; auto.
      + intros z.
        destruct (E y z); destruct (E x z);
          repeat match goal with
                 | H : ?a === ?b |- _ => rewrite (count_occ_cons_eq E _ H)
                 | H : ?a =/= ?b |- _ => rewrite (count_occ_cons_neq E _ H)
                 end; easy.
      + intros. eapply eq_trans; eauto.
    - revert l'. induction l; intros l' HCO.
      + replace l' with (@nil A). constructor.
        symmetry. eapply count_occ_inv_nil.
        cbn in HCO. symmetry in HCO. apply HCO.
      + assert (In a l'). {
          eapply count_occ_In.
          specialize (HCO a).
          cbn in HCO.
          destruct (E a a); [|pose proof (eq_refl a); contradiction].
          rewrite <- HCO. omega.
        }
        edestruct (in_split a l') as [L [R HLR]]; auto.
        eapply Permutation_trans; [|rewrite HLR; apply Permutation_middle].
        constructor. apply IHl.
        intros. destruct (E a x).
        * apply Nat.succ_inj.
          rewrite <- count_occ_remove_eq.
          rewrite <- count_occ_cons_eq with (x := a); [|auto].
          rewrite <- e, <- HLR. apply HCO.
        * rewrite <- count_occ_remove_neq with (a := a); auto.
          rewrite <- HLR.
          rewrite <- HCO, count_occ_cons_neq; auto.
  Qed.

  Theorem zipOcc_inj : forall l l',
      zipOcc l = zipOcc l' -> l = l'.
  Proof.
    induction l as [|h t IH]; intros [|h' t'] HEZ.
    - reflexivity.
    - inversion HEZ.
    - inversion HEZ.
    - cbn in HEZ. inversion HEZ; subst.
      f_equal. apply IH. auto.
  Qed.

  Lemma combine_nil_iff {B} : forall (l : list A) (r : list B),
      length l = length r ->
      combine l r = nil -> l = [] /\ r = [].
  Proof.
    intros [] [] HL Hnil.
    - auto.
    - inversion HL.
    - inversion HL.
    - inversion Hnil.
  Qed.

  Lemma combine_inj {B} : forall (xl yl : list A) (xr yr : list B),
      length xl = length xr ->
      length yl = length yr ->
      combine xl xr = combine yl yr ->
      xl = yl /\ xr = yr.
  Proof.
    induction xl as [|hxl txl IH]; intros [|hyl tyl] [|hxr txr] [|hyr tyr] HLX HLY HEq;
      try (cbn in *; omega); try discriminate.
    - auto.
    - cbn in *. inversion HEq; subst; clear HEq.
      split; f_equal; apply (IH tyl txr tyr); auto.
  Qed.

  Theorem combine_Permutation {B} : forall (xl yl : list A) (xr yr : list B),
      length xl = length xr -> length yl = length yr ->
      Permutation (combine xl xr) (combine yl yr) -> Permutation xl yl /\ Permutation xr yr.
  Proof.
    intros xl yl xr yr HXL HYL HP.
    remember (combine xl xr) as x; remember (combine yl yr) as y.
    revert xl yl xr yr HXL HYL Heqx Heqy.
    induction HP as [| zh zt zt' HP IH |x y z |x z y]; intros xl yl xr yr HXL HYL Heqx Heqy.
    - symmetry in Heqx, Heqy.
      apply combine_nil_iff in Heqx; [|auto]; apply combine_nil_iff in Heqy; [|auto].
      destruct Heqx; destruct Heqy; subst; split; apply perm_nil.
    - destruct xl as [|hxl txl]; [inversion Heqx|].
      destruct xr as [|hxr txr]; [inversion Heqx|].
      destruct yl as [|hyl tyl]; [inversion Heqy|].
      destruct yr as [|hyr tyr]; [inversion Heqy|].
      cbn [combine] in Heqx, Heqy.
      destruct zh; inversion Heqx; inversion Heqy; subst.
      cbn in HXL, HYL.
      split; constructor; apply (IH txl tyl txr tyr); auto.
    - destruct xl as [|axl [|bxl txl]]; destruct xr as [|axr [|bxr txr]]; [inversion Heqx..|].
      destruct yl as [|ayl [|byl tyl]]; destruct yr as [|ayr [|byr tyr]]; [inversion Heqy..|].
      cbn in Heqx, Heqy, HXL, HYL.
      destruct x; destruct y; inversion Heqx; inversion Heqy; subst.
      apply combine_inj in H9; [|omega..]; destruct H9.
      subst; split; apply perm_swap.
    - assert (Heqz : exists zl zr, z = combine zl zr /\ length zl = length zr). {
        exists (fst (split z)), (snd (split z)).
        pose proof (split_combine z).
        split.
        destruct (split z) as [zl zr]; auto.
        transitivity (length z); [apply split_length_l|symmetry; apply split_length_r].
      }
      destruct Heqz as [zl [zr [Heqz HZL]]].
      split; [transitivity zl | transitivity zr];
      [apply (IHHP1 xl zl xr zr)|apply (IHHP2 zl yl zr yr)|
       apply (IHHP1 xl zl xr zr)|apply (IHHP2 zl yl zr yr)]; auto.
  Qed.

  Theorem zipOcc_Permutation : forall l l',
      Permutation l l' <-> Permutation (zipOcc l) (zipOcc l').
  Proof.
    split.
    - intros P. induction P.
      + constructor.
      + cbn.
        replace (count_occ E l' x) with (count_occ E l x)
          by (apply count_occ_Permutation; auto).
        constructor. auto.
      + cbn. destruct (E y x); destruct (E x y); try intuition.
        * unfold equiv in *; subst. constructor. constructor. apply Permutation_refl.
        * apply perm_swap.
      + eauto using Permutation_trans.
    - rewrite !zipOcc_correct.
      apply (combine_Permutation l l' (occs l) (occs l')); rewrite occs_length; auto.
  Qed.

  Theorem zipOcc_fst_nth : forall l i d dn,
      fst (nth i (zipOcc l) (d, dn)) = nth i l d.
  Proof.
    intros.
    rewrite zipOcc_correct.
    destruct (lt_dec i (length l)).
    - rewrite combine_nth by (rewrite occs_length; intuition).
      reflexivity.
    - rewrite !nth_overflow
        by (try rewrite combine_length, occs_length, Nat.min_id; omega).
      reflexivity.
  Qed.
End ZipOcc.
