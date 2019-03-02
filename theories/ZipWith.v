Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Require Import Filter.

Section ZipWith.
  Context {A B C : Type} (f : A -> B -> C).

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

  Theorem zipOcc_Permutation : forall l l',
      Permutation l l' -> Permutation (zipOcc l) (zipOcc l').
  Proof.
    intros l l' P. induction P.
    - constructor.
    - cbn.
      replace (count_occ E l' x) with (count_occ E l x)
        by (apply count_occ_Permutation; auto).
      constructor. auto.
    - cbn. destruct (E y x); destruct (E x y); try intuition.
      + unfold equiv in *; subst. constructor. constructor. apply Permutation_refl.
      + apply perm_swap.
    - eauto using Permutation_trans.
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

  Section Filter.
    Context {T F} (f : forall y : A, {T y} + {F y}).

    Theorem filter_count_occ_in : forall l a,
        (exists p, f a = left p) ->
        count_occ E (filter f l) a = count_occ E l a.
    Proof.
      induction l as [|hd tl]; intros; [reflexivity|].
      cbn. destruct (f hd) eqn:Hfhd; cbn; destruct (E hd a); auto.
      unfold equiv in *; subst. destruct H. rewrite H in Hfhd. discriminate.
    Qed.

    Theorem filter_count_occ_not_in : forall l a,
        (exists p, f a = right p) ->
        count_occ E (filter f l) a = 0.
    Proof.
      induction l as [|hd tl]; intros; [reflexivity|].
      cbn. destruct (f hd) eqn:Hfhd; cbn; destruct (E hd a); auto.
      unfold equiv in *; subst. destruct H. rewrite H in Hfhd. discriminate.
    Qed.

    Theorem filter_zipOcc  : forall l,
        zipOcc (filter f l) = filter (fun x => f (fst x)) (zipOcc l).
    Proof.
      induction l.
      - reflexivity.
      - cbn. destruct (f a) eqn:Hfa.
        + cbn. rewrite filter_count_occ_in by eauto.
          f_equal. apply IHl.
        + apply IHl.
    Qed.
  End Filter.

  Theorem filter_eq_repeat : forall x l,
      filter (E x) l = repeat x (count_occ E l x).
  Proof.
    induction l; [reflexivity|].
    cbn. destruct (E x a); destruct (E a x); unfold equiv in *; subst;
           try contradiction.
    - cbn. rewrite IHl. reflexivity.
    - apply IHl.
  Qed.

  Theorem count_occ_repeat_eq : forall x n,
      count_occ E (repeat x n) x = n.
  Proof.
    induction n; [reflexivity|].
    cbn. destruct (E x x); [|pose proof equiv_reflexive _ x; contradiction].
    rewrite IHn. reflexivity.
  Qed.

  Theorem count_occ_repeat_neq : forall x y n,
      x <> y ->
      count_occ E (repeat x n) y = 0.
  Proof.
    intros x y n Hneq.
    induction n; [reflexivity|].
    cbn. destruct (E x y); try contradiction.
    apply IHn.
  Qed.

  Lemma rev_seq_n : forall n i,
      rev (seq i (S n)) = (n + i) :: rev (seq i n).
  Proof.
    induction n; intros.
    - reflexivity.
    - remember (S n) as n'.
      cbn [seq rev]; subst.
      rewrite IHn; cbn [app].
      f_equal. omega.
  Qed.

  Theorem occs_repeat_eq : forall x n,
      occs (repeat x n) = rev (seq 0 n).
  Proof.
    induction n; [reflexivity|].
    cbn [repeat occs]. rewrite IHn.
    rewrite count_occ_repeat_eq.
    rewrite rev_seq_n. rewrite <- plus_n_O. easy.
  Qed.

  Theorem zipOcc_filter_eq : forall x l,
      snd (split (filter (fun y => E x (fst y)) (zipOcc l))) =
      rev (seq 0 (count_occ E l x)).
  Proof.
    intros.
    rewrite <- filter_zipOcc with (f := E x).
    rewrite zipOcc_correct, combine_split. cbn.
    rewrite filter_eq_repeat.
    rewrite occs_repeat_eq. easy.
    rewrite occs_length. reflexivity.
  Qed.

  Lemma len_not_in_seq : forall n i,
      ~ In (i + n) (seq i n).
  Proof.
    induction n; intros; cbn; [auto|].
    intros H; destruct H as [H | H]; [omega|].
    rewrite <- Nat.add_succ_comm in H.
    eapply IHn. eauto.
  Qed.

  Theorem zipOcc_NoDup : forall l,
      NoDup (zipOcc l).
  Proof.
    induction l.
    - constructor.
    - cbn. constructor; [|auto].
      destruct (in_dec E a l).
      + rewrite (filter_in_pair_l E).
        setoid_rewrite zipOcc_filter_eq.
        rewrite <- in_rev.
        rewrite <- plus_O_n with (n := count_occ E l a) at 1.
        apply len_not_in_seq.
      + apply not_in_pair. left.
        rewrite zipOcc_correct, combine_split
          by (symmetry; apply occs_length); auto.
  Qed.

  Section FilterIx.
    Context {P} (f : forall y : A, {P y} + {~ P y}).

    Lemma dec_exists_pf_left : forall x,
        P x <-> exists PF, f x = left PF.
    Proof.
      intros. destruct (f x) eqn:Hfx.
      - split; intros; [exists p|]; easy.
      - split; intros; [contradiction|].
        destruct H. discriminate.
    Qed.
    Hint Resolve -> dec_exists_pf_left.

    Lemma dec_exists_pf_right : forall x,
        ~ P x <-> exists PF, f x = right PF.
    Proof.
      intros. destruct (f x) eqn:Hfx.
      - split; intros; [contradiction|].
        destruct H. discriminate.
      - split; intros; [exists n|]; easy.
    Qed.
    Hint Resolve -> dec_exists_pf_right.

    Theorem filter_ix_zipOcc : forall l l',
        filter f l = filter f l' ->
        forall i i' da dn,
        i < length l -> i' < length l' ->
        nth i (zipOcc l) (da, dn) = nth i' (zipOcc l') (da, dn) ->
        P (nth i l da) ->
        filter_ix f l i =
        filter_ix f l' i'.
    Proof.
      intros l l' Hf i i' da dn HL HL' Heq HP.
      replace l with (fst (split (zipOcc l)));
        replace l' with (fst (split (zipOcc l')));
        [|rewrite zipOcc_correct, combine_split by (symmetry; apply occs_length);
           easy..].
      rewrite !map_split. cbn. rewrite <- !filter_ix_map.

      eapply NoDup_nth with (d := (da, dn)).
      apply @zipOcc_NoDup with (l := filter f l).
      - rewrite filter_zipOcc. apply @filter_ix_bounded with (d := (da, dn)).
        + rewrite zipOcc_length. auto with zarith.
        + apply dec_exists_pf_left. rewrite zipOcc_fst_nth. auto.
      - rewrite Hf.
        rewrite filter_zipOcc. apply @filter_ix_bounded with (d := (da, dn)).
        + rewrite zipOcc_length. omega.
        + apply dec_exists_pf_left. rewrite zipOcc_fst_nth.
          rewrite !zipOcc_correct, !combine_nth in Heq
            by (symmetry; apply occs_length). inversion Heq; subst. auto.
      - rewrite Hf at 2. rewrite !filter_zipOcc.
        rewrite <- !filter_ix_correct; [apply Heq|..];
          rewrite ?zipOcc_length, <- ?Heq; try omega;
            apply dec_exists_pf_left; rewrite zipOcc_fst_nth; auto.
    Qed.
  End FilterIx.
End ZipOcc.
