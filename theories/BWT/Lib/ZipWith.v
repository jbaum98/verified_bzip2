Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Require Import BWT.Lib.Sumbool.
Require Import BWT.Lib.List.
Require Import BWT.Sorting.PermutationCount.

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
  Context {A : Type}.
  Variable eq_dec : forall x y : A, { x = y } + { x <> y }.

  Fixpoint zipOcc (l : list A) : list (A * nat) :=
    match l with
    | [] => []
    | a :: l => (a, count_occ eq_dec l a) :: zipOcc l
    end.

  Fixpoint occs (l : list A) :=
    match l with
    | [] => []
    | a :: l => count_occ eq_dec l a :: occs l
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

  Theorem filter_zipOcc : forall f l,
      zipOcc (filter f l) =
      filter (fun x => f (fst x)) (zipOcc l).
  Proof.
    induction l as [|a l IH]; [reflexivity|]; cbn.
    destruct (f a) eqn:Hfa.
    - cbn. rewrite (filter_true_count_occ eq_dec f a) by eauto.
      f_equal. apply IH.
    - apply IH.
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
        replace (count_occ eq_dec l' x) with (count_occ eq_dec l x)
          by (apply PermutationCount_iff; auto).
        constructor. auto.
      + cbn. destruct (eq_dec y x); destruct (eq_dec x y); try intuition.
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
