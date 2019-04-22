Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.omega.Omega.
Require Import Coq.Init.Nat.
Import Coq.Lists.List.ListNotations.

Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.Sumbool.
Require Import BWT.Lib.List.
Require Import BWT.Lib.FindIndex.
Require Import BWT.Sorting.Stable.

Definition perm (n : nat) (p : list nat) : Prop :=
  Permutation p (seq 0 n).

Theorem perm_0 : forall p,
    perm 0 p -> p = [].
Proof.
  intros p HP.
  unfold perm in HP; symmetry in HP.
  apply Permutation_nil; easy.
Qed.

Theorem perm_S_nil : forall n,
    ~ perm (S n) [].
Proof.
  intros n c.
  eapply Permutation_nil_cons.
  apply c.
Qed.

Theorem perm_range : forall p i n,
    perm n p -> In i p -> i < n.
Proof.
  intros p i n HP; revert i.
  apply Forall_forall.
  eapply Permutation_forall; [symmetry; apply HP|].
  apply Forall_forall. apply in_seq.
Qed.

Theorem perm_length : forall p n,
    perm n p -> length p = n.
Proof.
  intros.
  apply Permutation_length in H.
  rewrite seq_length in H.
  easy.
Qed.

Section Apply.
  Context {A : Type}.

  Implicit Types (p : list nat) (l : list A).

  Definition apply p l : list A
    := match l with
       | [] => []
       | d::_ => map (fun i => nth i l d) p
       end.

  Theorem apply_def : forall p l d ,
      perm (length l) p ->
      apply p l = map (fun i => nth i l d) p.
  Proof.
    intros p [|h t] d HP.
    - apply perm_0 in HP; subst; easy.
    - cbn [apply]. apply map_ext_in.
      intros; apply nth_indep.
      apply (perm_range p); easy.
  Qed.

  Theorem map_seq_id : forall l d,
      map (fun x : nat => nth x l d) (seq 0 (length l)) = l.
  Proof.
    induction l; intros d; [easy|].
    cbn [length seq map]; f_equal.
    rewrite <- seq_shift, map_map.
    apply IHl.
  Qed.

  Theorem apply_id : forall l,
      apply (seq 0 (length l)) l = l.
  Proof.
    destruct l; [easy|].
    apply map_seq_id with (d := a).
  Qed.

  Definition rem_perm i := map (fun j => if lt_dec i j then pred j else j).

  Theorem rem_perm_0 : forall p n, perm n (0 :: p) -> rem_perm 0 p = map pred p.
  Proof.
    induction p; intros n HP; [easy|].
    unfold rem_perm. apply map_ext_in.
    intros x HIn.
    assert (1 <= x). {
      unfold perm in HP.
      destruct n;
        [symmetry in HP; apply Permutation_nil in HP; inversion HP|cbn in HP].
      apply (in_seq n 1 x).
      eapply Permutation_in; [eapply Permutation_cons_inv; apply HP|easy].
    }
    destruct (lt_dec 0 x); omega.
  Qed.

  Theorem rem_perm_NoDup : forall p i,
      NoDup p -> ~ In i p -> NoDup (rem_perm i p).
  Proof.
    intros p i ND.
    induction ND; intros NIn; [constructor|].
    cbn. destruct (lt_dec i x) as [HLt | HGe].
    - rewrite not_in_cons in NIn.
      destruct NIn as [HNeq Nin].
      apply NoDup_cons; [|apply IHND; apply Nin].
      unfold rem_perm. rewrite in_map_iff.
      destruct x; [omega|cbn in *].
      intros [y [Hy HIn]].
      destruct (lt_dec i y).
      + destruct y; [omega|cbn in *].
        subst. contradiction.
      + subst.
        assert (i = x) by omega; subst.
        contradiction.
    - rewrite not_in_cons in NIn.
      destruct NIn as [HNeq Nin].
      apply NoDup_cons; [|apply IHND; apply Nin].
      unfold rem_perm. rewrite in_map_iff.
      intros [y [Hy HIn]].
      destruct (lt_dec i y).
      + destruct y; [omega|cbn in *].
        subst. omega.
      + subst. contradiction.
  Qed.

  Lemma seq_split : forall i j s,
      seq s (i + j) = seq s i ++ seq (s + i) j.
  Proof.
    induction i as [|i IH]; intros j s;
      [cbn; rewrite Nat.add_0_r; reflexivity|].
    cbn; f_equal.
    rewrite IH; f_equal.
    rewrite <- plus_Snm_nSm.
    reflexivity.
  Qed.

  Lemma seq_last_perm : forall p n,
      Permutation (n :: p) (seq 0 (S n)) ->
      Permutation p (seq 0 n).
  Proof.
    intros p n HP.
    replace (S n) with (n + 1) in HP by omega.
    rewrite seq_split with (i := n) (j := 1) in HP.
    cbn in HP.
    rewrite Permutation_app_comm in HP.
    eapply Permutation_cons_inv. apply HP.
  Qed.

  Theorem rem_perm_Perm : forall p i n,
      perm (S n) (i :: p) ->
      perm n (rem_perm i p).
  Proof.
    unfold perm in *.
    intros p i n P.
    apply NoDup_Permutation; [|apply seq_NoDup|].
    - symmetry in P; apply Permutation_NoDup in P; [|apply seq_NoDup].
      apply NoDup_cons_iff in P.
      apply rem_perm_NoDup; easy.
    - intro x; split; intros HIn.
      + apply in_seq; split; [omega|cbn].
        unfold rem_perm in HIn.
        apply in_map_iff in HIn.
        destruct HIn as [y [Hy HIn]].
        assert (y < S n)
          by (apply perm_range with (p := i :: p); [apply P|right; easy]).
        assert (i < S n)
          by (apply perm_range with (p := i :: p); [apply P|left; easy]).
        assert (y <> i). {
          intro c; subst. clear -HIn P.
          symmetry in P; apply Permutation_NoDup in P; [|apply seq_NoDup].
          apply NoDup_cons_iff in P.
          destruct P; contradiction.
        }
        destruct (Nat.eq_dec y n); [subst; rewrite if_true; omega|].
        destruct (lt_dec i y); omega.
      + unfold rem_perm; rewrite in_map_iff.
        destruct (Nat.eq_dec i n). {
          subst. apply seq_last_perm in P.
          exists x. rewrite if_false by (apply in_seq in HIn; omega).
          split; [easy|].
          eapply Permutation_in; [symmetry; apply P|easy..].
        }
        destruct (le_lt_dec i x).
        * exists (S x).
          rewrite if_true by omega.
          split; [easy|].
          eapply or_ind with (A := i = S x); [omega|intro H; exact H|].
          eapply Permutation_in with (l' := i :: p);
            [symmetry; apply P|].
          apply in_seq in HIn.
          apply in_seq. omega.
        * exists x.
          rewrite if_false by omega.
          split; [easy|].
          assert (x < n) by (apply in_seq in HIn; easy).
          eapply or_ind with (A := i = x); [omega|intro R; exact R|].
          eapply Permutation_in with (l' := i :: p);
            [symmetry; apply P|].
          apply in_seq in HIn.
          apply in_seq. omega.
  Qed.

  Fixpoint rem_nth i l :=
    match l with
    | [] => []
    | h :: t =>
      match i with
      | 0 => t
      | S i' => h :: rem_nth i' t
      end
    end.

  Remark rem_nth_nil : forall i,
      rem_nth i [] = [].
  Proof. intros []; easy. Qed.

  Remark rem_nth_zero : forall a l,
      rem_nth 0 (a :: l) = l.
  Proof. easy. Qed.

  Theorem rem_nth_length : forall l i,
      i < length l ->
      length (rem_nth i l) = pred (length l).
  Proof.
    induction l; intros i HI; [cbn in HI; omega|].
    cbn in *. destruct i; [easy|].
    cbn. rewrite IHl by omega.
    destruct l; [omega|easy].
  Qed.

  Theorem nth_lt_rem_nth : forall i j l d,
      j < i ->
      nth j (rem_nth i l) d = nth j l d.
  Proof.
    induction i as [|i IH]; intros j l d HIJ; [omega|].
    destruct l; [cbn [rem_nth]; easy|].
    cbn [rem_nth].
    destruct j; cbn [nth]; [easy|].
    apply IH; omega.
  Qed.

  Theorem nth_ge_rem_nth : forall i j l d,
      j >= i ->
      nth j (rem_nth i l) d = nth (S j) l d.
  Proof.
    induction i as [|i IH]; intros j l d HIJ.
    - destruct l; cbn [rem_nth tl];
        [rewrite !nth_overflow by (cbn; omega); easy|].
      easy.
    - destruct l; cbn [rem_nth tl];
        [rewrite !nth_overflow by (cbn; omega); easy|].
      destruct j; [omega|].
      cbn [nth]. apply IH. omega.
  Qed.

  Theorem rem_hd_perm : forall l i p d,
      perm (length l) (i::p) ->
      apply (i::p) l = nth i l d :: apply (rem_perm i p) (rem_nth i l).
  Proof.
    intros.
    assert (length l > 0). {
      unfold perm in H. apply Permutation_length in H.
      cbn in H. destruct l; cbn in *; omega.
    }
    assert (~ In i p). {
      unfold perm in H; symmetry in H.
      apply Permutation_NoDup in H; [|apply seq_NoDup].
      apply NoDup_cons_iff in H.
      easy.
    }
    rewrite apply_def with (d := d) by easy.
    cbn [map]. f_equal.
    rewrite apply_def with (d := d)
      by (apply rem_perm_Perm;
          rewrite rem_nth_length
            by (apply perm_range with (p := i :: p); [easy|left; easy]);
          rewrite <- S_pred_pos by omega;
          easy).
    unfold rem_perm; rewrite map_map.
    apply map_ext_in.
    intros a HIn.
    assert (i <> a) by (intro c; subst; contradiction).
    destruct (lt_dec i a).
    - rewrite nth_ge_rem_nth by omega.
      destruct a; easy.
    - rewrite nth_lt_rem_nth by omega; easy.
  Qed.

  Theorem rem_nth_Perm : forall l i d,
      i < length l ->
      Permutation l (nth i l d :: rem_nth i l).
  Proof.
    induction l; intros i d HI; [cbn in*; omega|].
    destruct i; [reflexivity|].
    cbn. etransitivity; [|apply perm_swap].
    apply perm_skip. apply IHl. cbn in *; omega.
  Qed.

  Lemma firstn_skipn_nth : forall (l : list A) i d,
      i < length l ->
      firstn 1 (skipn i l) = [nth i l d].
  Proof.
    induction l; intros i d HL; [cbn in HL; omega|].
    destruct i; [easy|].
    cbn [skipn nth]. apply IHl. cbn in HL; omega.
  Qed.

  Lemma firstn_skipn_split : forall l i d,
      0 < i < length l ->
      l = firstn i l ++ nth i l d :: skipn (S i) l.
  Proof.
    intros l i d HL.
    destruct i; [omega|].
    rewrite <- firstn_skipn with (l := l) (n := S (S i)) at 1.
    replace (S (S i)) with (S i + 1) at 1 by omega.
    rewrite <- firstn_skipn with (l := l) (n := S i) at 1.
    rewrite firstn_app, firstn_length, Nat.min_l by omega.
    replace (S i + 1 - S i) with 1 by omega.
    rewrite firstn_firstn, Nat.min_r by omega.
    rewrite firstn_skipn_nth with (d := d) by omega.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Theorem rem_nth_app_1 : forall l1 l2 i,
      i >= length l1 ->
      rem_nth i (l1 ++ l2) = l1 ++ rem_nth (i - length l1) l2.
  Proof.
    induction l1; intros l2 i HI; [rewrite <- minus_n_O; easy|].
    cbn in HI. destruct i; [omega|].
    cbn. f_equal.
    apply IHl1. omega.
  Qed.

  Theorem rem_nth_app_2 : forall l1 l2 i,
      i < length l1 ->
      rem_nth i (l1 ++ l2) = rem_nth i l1 ++ l2.
  Proof.
    induction l1; intros l2 i HI; [rewrite app_nil_l; easy|].
    cbn in HI. destruct i; [easy|].
    cbn. f_equal.
    apply IHl1. omega.
  Qed.

  Theorem rem_nth_split : forall l i,
      i < length l ->
      rem_nth i l = firstn i l ++ skipn (S i) l.
  Proof.
    intros l i HI.
    destruct i; [destruct l; easy|].
    destruct l as [|d t] eqn:HL; [easy|rewrite <- HL in *; clear t HL].
    rewrite firstn_skipn_split with (i := S i) (d := d) (l := l) at 1 by omega.
    rewrite rem_nth_app_1 by (rewrite firstn_length, Nat.min_l; omega).
    f_equal. rewrite firstn_length, Nat.min_l by omega.
    replace (S i - S i) with 0 by omega.
    easy.
  Qed.

  Theorem perm_Perm : forall p l,
      perm (length l) p ->
      Permutation (apply p l) l.
  Proof.
    unfold perm. intros p l.
    remember (length l) as n.
    revert p l Heqn.
    induction n as [|n IH]; intros p l HN HP.
    - symmetry in HN; apply length_zero_iff_nil in HN; subst.
      apply perm_0 in HP; subst.
      reflexivity.
    - destruct l as [|a l]; [inversion HN|].
      destruct p as [|i p]; [apply Permutation_nil_cons in HP; contradiction|].
    rewrite rem_hd_perm with (d := a) by (rewrite <- HN; easy).
    assert (i < length (a :: l))
      by (apply perm_range with (p := i :: p); [rewrite <- HN|left]; easy).
    etransitivity;
      [apply perm_skip|symmetry; apply rem_nth_Perm; easy].
    apply IH; [|apply rem_perm_Perm; easy].
    rewrite rem_nth_length by easy. cbn in *; omega.
  Qed.

  Theorem apply_length : forall p l,
      perm (length l) p ->
      length (apply p l) = length l.
  Proof.
    intros.
    destruct l as [|d t] eqn:HL; [easy|rewrite <- HL in *; clear HL t].
    rewrite apply_def with (d := d) by easy.
    apply Permutation_length in H.
    rewrite seq_length in H.
    unfold apply; rewrite map_length.
    easy.
  Qed.
End Apply.

Section Compose.
  Implicit Types (p : list nat).

  Definition compose p2 p1 := apply p2 p1.

  Remark compose_length : forall n p1 p2,
      perm n p1 -> perm n p2 -> length (compose p1 p2) = n.
  Proof.
    intros n p1 p2 HP1 HP2.
    apply perm_length in HP2; subst.
    apply apply_length. easy.
  Qed.

  Remark compose_Perm : forall n p1 p2,
      perm n p1 -> perm n p2 -> perm n (compose p1 p2).
  Proof.
    intros n p1 p2 HP1 HP2.
    unfold perm.
    transitivity p2; [|apply HP2].
    apply perm_Perm; [apply perm_length in HP2; subst; easy].
  Qed.

  Theorem compose_id_l : forall p n,
      perm n p ->
      compose (seq 0 n) p = p.
  Proof.
    intros p n HP.
    apply perm_length in HP. subst.
    apply apply_id.
  Qed.

  Theorem compose_id_r : forall p n,
      perm n p ->
      compose p (seq 0 n) = p.
  Proof.
    intros p n HP.
    destruct p as [|i p];
    [destruct n; [easy|apply perm_S_nil in HP; contradiction]|].
    rewrite apply_def with (d := 0) by (rewrite seq_length; easy).
    cbn [map].
    f_equal; [apply seq_nth; eapply perm_range; [apply HP|left; easy]|].
    rewrite <- map_id.
    apply map_ext_in.
    intros a HIn.
    rewrite seq_nth by (eapply perm_range; [apply HP|right; easy]).
    reflexivity.
  Qed.

  Theorem rem_nth_combine {A B} : forall (l : list A) (r : list B) i,
      rem_nth i (combine l r) = combine (rem_nth i l) (rem_nth i r).
  Proof.
    induction l as [|xl l IH]; intros r i.
    - rewrite rem_nth_nil. cbn. apply rem_nth_nil.
    - destruct r as [|xr r];
        [rewrite rem_nth_nil; destruct i; destruct l; easy|].
      destruct i; [easy|].
      cbn; f_equal.
      apply IH.
  Qed.

  Theorem apply_combine {A B} : forall n p (l : list A) (r : list B),
      perm n p -> length l = n -> length r = n ->
      apply p (combine l r) = combine (apply p l) (apply p r).
  Proof.
    induction n; intros p l r HP HL HR.
    - apply perm_0 in HP.
      apply length_zero_iff_nil in HL.
      apply length_zero_iff_nil in HR.
      subst. reflexivity.
    - destruct p as [|i p]; [apply perm_S_nil in HP; contradiction|].
      destruct l as [|xl l]; [inversion HL|].
      destruct r as [|xr r]; [inversion HR|].
      rewrite rem_hd_perm with (d := (xl, xr))
        by (rewrite combine_length, HL, HR, Nat.min_id; easy).
      rewrite rem_hd_perm with (d := xl) by (rewrite HL; easy).
      rewrite rem_hd_perm with (d := xr) by (rewrite HR; easy).
      cbn [combine]; rewrite <- combine_nth by (rewrite HL, HR; easy).
      f_equal.
      rewrite <- IHn;
        [|apply rem_perm_Perm; easy|rewrite rem_nth_length; rewrite ?HL, ?HR..];
        [|easy| |easy|];
        [|apply perm_range with (p := i :: p); [|left]; easy..].
      rewrite <- rem_nth_combine; cbn [combine].
      reflexivity.
  Qed.

  Theorem compose_apply {A} : forall p1 p2 (l : list A),
      perm (length l) p1 -> perm (length l) p2 ->
      apply (compose p2 p1) l = apply p2 (apply p1 l).
  Proof.
    intros p1 p2 l HP1 HP2.
    destruct l as [|d t] eqn:HL; [easy|rewrite <- HL in *; clear t HL].
    remember (seq 0 (length l)) as I.
    remember (@combine nat A I l) as Z.
    assert (L: length Z = length l). {
      rewrite HeqZ, combine_length, HeqI, seq_length, Nat.min_id.
      easy.
    }
    assert (L1 : length p1 = length l) by (apply perm_length; easy).
    assert (L2 : length p2 = length l) by (apply perm_length; easy).
    assert (P1 : Permutation (apply p2 (apply p1 Z)) Z). {
      rewrite perm_Perm; [|rewrite apply_length; rewrite L; easy].
      rewrite perm_Perm; [reflexivity|rewrite L; easy].
    }
    assert (P2 : Permutation (apply (compose p2 p1) Z) Z). {
      rewrite perm_Perm; [reflexivity|].
      rewrite L.
      unfold perm, compose.
      transitivity p1; [apply perm_Perm|apply HP1].
      rewrite @perm_length with (n := length l); easy.
    }
    symmetry in P2; pose proof (Permutation_trans P1 P2) as P; clear P1 P2.
    rewrite HeqZ in P.
    rewrite !apply_combine with (n := length l) in P;
      repeat match goal with
      | |- context [length (apply ?p ?l)] => rewrite apply_length
      | |- context [length I] => rewrite HeqI; rewrite seq_length
      | |- perm ?n (compose ?p2 ?p1) => apply compose_Perm
      end;
      try easy.
    rewrite HeqI, !compose_id_r in P;
      [|apply compose_Perm|]; [|easy..].
    symmetry.
    apply (Permutation_combine_eq _ _ _ P);
      [rewrite !apply_length..
      |apply @Permutation_NoDup with (l := I);
       rewrite HeqI; [| apply seq_NoDup]];
      [..|symmetry; fold (perm (length l) (apply p2 p1)); fold (compose p2 p1)];
      try match goal with
      | |- context [length (apply ?p ?l)] => rewrite apply_length
      | |- perm ?n (compose ?p2 ?p1) => apply compose_Perm
      end; rewrite ?L1; try easy.
  Qed.
End Compose.

Section Permutation.
  Context {A : Type}.

  Implicit Type l : list A.

  Theorem perm_ex_Permutation : forall l l',
      Permutation l l' -> (exists p, perm (length l) p /\ apply p l = l').
  Proof.
    intros l l' HP.
    induction HP.
    - exists []. split; cbn; unfold perm; auto.
    - destruct IHHP as [p [Hp HA]].
      exists (0 :: map S p). cbn [length apply]; split.
      + unfold perm; cbn.
        apply perm_skip.
        rewrite <- seq_shift.
        apply Permutation_map. apply Hp.
      + cbn [map]. f_equal.
        rewrite apply_def with (d := x) in HA by easy.
        rewrite map_map. cbn. easy.
    - exists (1 :: 0 :: map (fun x => S (S x)) (seq 0 (length l))).
      split.
      + unfold perm. cbn [length seq].
        rewrite <- map_map, !seq_shift.
        apply perm_swap.
      + cbn [apply map]; do 2 f_equal.
        rewrite map_map. cbn [nth].
        rewrite <- apply_def by (unfold perm; reflexivity).
        apply apply_id.
    - destruct IHHP1 as [p1 [Hp1 HA1]].
      destruct IHHP2 as [p2 [Hp2 HA2]].
      assert (perm (length l) p2). {
        rewrite <- HA1 in Hp2.
        rewrite apply_length in Hp2 by easy.
        easy.
      }
      exists (compose p2 p1).
      split; [apply compose_Perm; easy|].
      rewrite compose_apply by easy.
      rewrite HA1, HA2.
      easy.
  Qed.

  Theorem perm_ex_Permutation_iff : forall l l',
      Permutation l l' <-> (exists p, perm (length l) p /\ apply p l = l').
  Proof.
    split.
    - apply perm_ex_Permutation.
    - intros [p [Hp HA]].
      subst.
      symmetry. apply perm_Perm.
      easy.
  Qed.
End Permutation.

Section Image.
  Context {A : Type}.

  Implicit Types (p : list nat) (l : list A).

  Definition image p i := findIndex i p.
  Definition preimage p i := nth i p 0.

  Lemma perm_i_exists : forall p n i,
      perm n p -> i < n ->
      Exists (equiv i) p.
  Proof.
    intros p n i HP HI.
    eapply Permutation_exists; [symmetry; apply HP|].
    apply Exists_exists.
    exists i. split; [|easy].
    apply in_seq; omega.
  Qed.

  Theorem preimage_image : forall p i n,
      perm n p -> i < n ->
      preimage p (image p i) = i.
  Proof.
    intros p i l HP HI.
    unfold image, preimage.
    rewrite findIndex_correct by (eapply perm_i_exists; [apply HP|omega]).
    reflexivity.
  Qed.

  Theorem image_preimage : forall p i n,
      perm n p -> i < n ->
      image p (preimage p i) = i.
  Proof.
    intros p i l HP HI.
    unfold image, preimage.
    rewrite findIndex_nth;
      [..
      |eapply Permutation_NoDup; [symmetry; apply HP|apply seq_NoDup]
      |erewrite perm_length by apply HP
      ]; easy.
  Qed.

  Theorem image_inj : forall p i j n,
      perm n p -> i < n -> j < n ->
      image p i = image p j -> i = j.
  Proof.
    intros p i j n HP HI HJ HE.
    unfold image in HE.
    apply f_equal with (f := fun x => nth x p 0) in HE.
    rewrite !findIndex_correct in HE by (eapply perm_i_exists; [apply HP|easy]).
    easy.
  Qed.

  Theorem preimage_inj : forall p i j n,
      perm n p -> i < n -> j < n ->
      preimage p i = preimage p j -> i = j.
  Proof.
    intros p i j n HP HI HJ HE.
    apply (NoDup_nth p 0); [|erewrite perm_length by apply HP..|]; [|easy..].
    eapply Permutation_NoDup; [symmetry; apply HP|].
    apply seq_NoDup.
  Qed.

  Theorem image_bound : forall p i n,
      perm n p -> i < n -> image p i < n.
  Proof.
    intros p i n HP HI.
    unfold image.
    rewrite <- perm_length with (p := p) by easy.
    apply findIndex_bounds.
    eapply perm_i_exists; [apply HP|easy].
  Qed.

  Theorem preimage_bound : forall p i n,
      perm n p -> i < n -> preimage p i < n.
  Proof.
    intros p i n HP HI.
    unfold preimage.
    apply perm_range with (p := p); [easy|].
    apply nth_In.
    rewrite perm_length with (n := n) by easy.
    easy.
  Qed.

  Theorem nth_image_apply : forall p i l d,
      perm (length l) p -> i < length l ->
      nth (image p i) (apply p l) d = nth i l d.
  Proof.
    intros p i l d HP HI.
    rewrite @apply_def with (d := d) by easy.
    unfold image.
    assert (E : Exists (equiv i) p)
      by (eapply perm_i_exists; [apply HP|easy]).
    assert (In (findIndex i p) p). {
      eapply Permutation_in; [symmetry; apply HP|].
      apply in_seq.
      pose proof (findIndex_bounds i p E).
      erewrite perm_length in H by apply HP.
      omega.
    }
    rewrite nth_indep with (d := d) (d' := nth 0 l d)
      by (apply perm_range with (p := p);
          [erewrite map_length, perm_length|]; [apply HP..|easy]).
    rewrite map_nth with (f := (fun i0 : nat => nth i0 l d)).
    rewrite findIndex_correct by easy.
    reflexivity.
  Qed.

  Theorem nth_preimage_apply : forall p i l d,
      perm (length l) p -> i < length l ->
      nth (preimage p i) l d = nth i (apply p l) d.
  Proof.
    intros p i l d HP HI.
    rewrite <- image_preimage with (i := i) (p := p) (n := length l) at 2 by easy.
    rewrite nth_image_apply; [..|apply preimage_bound]; [|easy..].
    reflexivity.
  Qed.
End Image.

Section Stable.
  Context {A} `{EqDec A}.

  Definition stable_perm (l : list A) (p : list nat) :=
    perm (length l) p /\ forall i j d,
      i < j < length l ->
      nth i l d === nth j l d ->
      image p i < image p j.

  Definition stable_perm_preimage (l : list A) (p : list nat) :=
    perm (length l) p /\ forall i j d,
      i < j < length l ->
      nth i (apply p l) d === nth j (apply p l) d ->
      preimage p i < preimage p j.

  Theorem stable_perm_image_preimage : forall l p,
      stable_perm l p <-> stable_perm_preimage l p.
  Proof.
    intros; split; (intros [HP HS]; split; [easy|]); intros i j d HIJ HE.
    - rewrite <- image_preimage with (i := i) (p := p) (n := length l) in HE
        by (omega || easy).
      rewrite <- image_preimage with (i := j) (p := p) (n := length l) in HE
        by (omega || easy).
      rewrite !nth_image_apply in HE by (try apply preimage_bound; omega || easy).
      apply Nat.nle_gt. intro c.
      destruct (le_lt_or_eq _ _ c) as [HLt|HEq];
        [|apply preimage_inj with (n := length l) in HEq; [omega|easy..|omega]].
      assert (c2 : ~ j < i) by omega. apply c2; clear c2.
      rewrite <- image_preimage with (i := i) (n := length l) (p := p)
        by (omega || easy).
      rewrite <- image_preimage with (i := j) (n := length l) (p := p)
        by (omega || easy).
      apply HS with (d := d).
      split; [omega|].
      apply preimage_bound; [easy|omega].
      easy.
    - rewrite <- preimage_image with (i := i) (p := p) (n := length l) in HE
        by (omega || easy).
      rewrite <- preimage_image with (i := j) (p := p) (n := length l) in HE
        by (omega || easy).
      rewrite !nth_preimage_apply in HE by (try apply image_bound; omega || easy).
      apply Nat.nle_gt. intro c.
      destruct (le_lt_or_eq _ _ c) as [HLt|HEq];
        [|apply image_inj with (n := length l) in HEq; [omega|easy..|omega]].
      assert (c2 : ~ j < i) by omega. apply c2; clear c2.
      rewrite <- preimage_image with (i := i) (n := length l) (p := p)
        by (omega || easy).
      rewrite <- preimage_image with (i := j) (n := length l) (p := p)
        by (omega || easy).
      apply HS with (d := d).
      split; [omega|].
      apply image_bound; [easy|omega].
      easy.
  Qed.

  Theorem stable_perm_nil : stable_perm [] [].
  Proof.
    split; [apply perm_nil|].
    intros i j d HIJ HE.
    cbn in HIJ. omega.
  Qed.

  Theorem stable_perm_compose : forall p1 p2 l,
      stable_perm l p1 -> stable_perm (apply p1 l) p2 ->
      stable_perm l (compose p2 p1).
  Proof.
    setoid_rewrite stable_perm_image_preimage.
    intros p1 p2 l [HP1 HS1] [HP2 HS2].
    rewrite apply_length in HP2 by easy.
    split; [apply compose_Perm; easy|].
    intros i j d HIJ HE.
    rewrite @apply_def with (d := 0)
      by (apply perm_length in HP1; rewrite HP1; easy).
    unfold preimage.
    rewrite nth_indep with (n := i) (d' := nth 0 p1 0)
      by (rewrite map_length; apply perm_length in HP2; omega).
    rewrite nth_indep with (n := j) (d' := nth 0 p1 0)
      by (rewrite map_length; apply perm_length in HP2; omega).
    rewrite !map_nth with (f := fun x => nth x p1 0).
    apply HS1 with (d := d).
    split; [|apply perm_range with (p := p2);
             [easy|apply nth_In; apply perm_length in HP2; omega]].
    apply HS2 with (d := d);
      [rewrite apply_length; [omega|easy]|].
    rewrite <- compose_apply by easy. easy.
    rewrite compose_apply in HE by easy.
    rewrite @apply_def with (d := d) in HE
      by (rewrite apply_length; easy).
    rewrite nth_indep with (n := i) (d := d) (d' := nth j (apply p1 l) d) in HE
      by (rewrite map_length; apply perm_length in HP2; omega).
    rewrite !map_nth with (f := (fun i => nth i (apply p1 l) d)) in HE.
    rewrite nth_indep with (n := j) (d := d) (d' := nth j (apply p1 l) d) in HE
      by (rewrite map_length; apply perm_length in HP2; omega).
    rewrite !map_nth with (f := (fun i => nth i (apply p1 l) d)) in HE.
    rewrite !nth_indep with (d := 0) (d' := j)
      by (apply perm_length in HP2; omega).
    apply HE.
  Qed.

  Theorem stable_perm_ex_Stable : forall l l',
      Stable l l' -> (exists p, stable_perm l p /\ apply p l = l').
  Proof.
    setoid_rewrite stable_perm_image_preimage.
    intros l l' HS.
    apply stable_ind_iff in HS.
    induction HS.
    - exists []. split; [apply stable_perm_image_preimage; apply stable_perm_nil|easy].
    - destruct IHHS as [p [HSP HA]].
      exists (0 :: map S p).
      destruct HSP as [HP HSP].
      split; [split|].
      + unfold perm. cbn. apply perm_skip.
        rewrite <- seq_shift.
        apply Permutation_map.
        easy.
      + intros i j d HIJ HE.
        pose proof (perm_length _ _ HP); cbn in HIJ.
        unfold preimage.
        rewrite !nth_indep with (d := 0) (d' := 1)
          by (cbn; rewrite map_length; omega).
        destruct i; destruct j; [omega| |omega|].
        * cbn [nth]. rewrite map_nth. omega.
        * cbn. rewrite !map_nth.
          apply lt_n_S.
          apply HSP with (d := d); [omega|].
          cbn [apply map] in HE.
          rewrite map_map in HE.
          cbn in HE.
          rewrite @apply_def with (d := x); easy.
      + cbn [apply map]; rewrite nth_first; cbn [hd].
        f_equal. rewrite <- HA.
        rewrite apply_def with (d := x) by easy.
        rewrite map_map. apply map_ext.
        easy.
    - exists (1 :: 0 :: map (fun x => S (S x)) (seq 0 (length l))).
      split; [split|].
      + unfold perm. cbn [length seq].
        rewrite <- map_map, !seq_shift.
        apply perm_swap.
      + intros i j d HIJ HE.
        destruct i; destruct j;
          [omega|destruct j|omega|
           destruct i; destruct j; [omega| |omega|]];
          [exfalso; cbn in HE; contradiction
          |cbn in *;
           rewrite nth_indep with (d' := 2)
             by (rewrite map_length, seq_length; omega);
           rewrite map_nth with (d := 0);
           omega..
          |].
        cbn.
        rewrite !nth_indep with (d := 0) (d' := S (S 0))
          by (rewrite map_length, seq_length; cbn in *; omega).
        rewrite !map_nth with (d := 0).
        do 2 apply lt_n_S.
        rewrite !seq_nth by (cbn in *; omega).
        omega.
      + cbn [apply map]; rewrite nth_first; cbn [hd].
        do 2 f_equal. rewrite <- map_seq_id with (d := y).
        rewrite map_map. apply map_ext.
        easy.
    - destruct IHHS1 as [p1 [HSP1 HA1]].
      destruct IHHS2 as [p2 [HSP2 HA2]].
      exists (compose p2 p1).
      rewrite <- stable_perm_image_preimage in *.
      split; [apply stable_perm_compose;
              [|rewrite <- HA1 in HSP2]; easy|].
      rewrite compose_apply, HA1, HA2
        by (destruct HSP1 as [HP1 _]; destruct HSP2 as [HP2 _];
            rewrite <- HA1, apply_length in HP2 by easy; easy).
      reflexivity.
  Qed.

  Theorem firstn_nth : forall n (l : list A) i d,
      i < n ->
      nth i (firstn n l) d = nth i l d.
  Proof.
    induction n as [|n IH]; intros l i d HI; [omega|].
    destruct l; [destruct i; easy|].
    destruct i; [easy|].
    cbn [firstn nth]. apply IH; omega.
  Qed.

  Theorem rem_nth_Stable : forall (l : list A) i d,
      i < length l ->
      (forall k, k < i -> nth i l d =/= nth k l d) ->
      Stable l (nth i l d :: rem_nth i l).
  Proof.
    intros l i d HI HK.
    destruct i as [|i'] eqn:Heqni;
      [destruct l; easy
      |rewrite <- Heqni in *; assert (0 < i) by omega; clear i' Heqni].
    rewrite rem_nth_split by omega.
    rewrite @firstn_skipn_split with (i := i) (l := l) (d := d) at 1 by omega.
    apply Stable_cons_app_to_front; [easy|].
    apply Forall_forall.
    intros x HIn.
    apply In_nth with (d := d) in HIn .
    destruct HIn as [j [HJ HX]].
    rewrite <- HX; clear x HX.
    rewrite firstn_length, Nat.min_l in HJ by omega.
    rewrite firstn_nth by easy.
    apply HK; easy.
  Qed.

  Theorem image_lt_rem_perm : forall p j i n,
      perm (S n) (i :: p) ->
      j < i -> image (rem_perm i p) j = pred (image (i :: p) j).
  Proof.
    intros p j i n HP HIJ.
    unfold image, rem_perm.
    cbn. rewrite if_false by (intro c; unfold equiv in c; omega).
    cbn.
    match goal with
    | |- context [findIndex ?j (map ?f ?l)] =>
      rewrite <- (findIndex_map f p)
    end; [|easy|fold (rem_perm i p)|].
    rewrite if_false by omega.
    easy.
    eapply Permutation_NoDup;
      [symmetry; apply rem_perm_Perm; apply HP|apply seq_NoDup].
    apply Exists_exists.
    exists j; split; [|easy].
    apply in_cons_neq with (y := i); [omega|].
    eapply Permutation_in; [symmetry; apply HP|].
    apply in_seq.
    split; [omega|].
    transitivity i; [omega|].
    eapply perm_range; [apply HP|left]; easy.
  Qed.

  Theorem image_ge_rem_perm : forall p j i n,
      perm (S n) (i :: p) ->
      i <= j < n -> image (rem_perm i p) j = pred (image (i :: p) (S j)).
  Proof.
    intros p j i n HP HIJ.
    unfold image, rem_perm.
    cbn [findIndex]. rewrite if_false by (intro c; unfold equiv in c; omega).
    cbn.
    match goal with
    | |- context [findIndex ?j (map ?f ?l)] =>
      rewrite <- (findIndex_map f p)
    end; [|easy|fold (rem_perm i p)|].
    rewrite if_true by omega.
    easy.
    eapply Permutation_NoDup;
      [symmetry; apply rem_perm_Perm; apply HP|apply seq_NoDup].
    apply Exists_exists.
    exists (S j); split; [|easy].
    apply in_cons_neq with (y := i); [omega|].
    eapply Permutation_in; [symmetry; apply HP|].
    apply in_seq.  omega.
  Qed.

  Theorem image_lt_rem_perm'' : forall p j i n,
      perm n (i :: p) ->
      j < i -> image (rem_perm i p) j = image p j.
  Proof.
    induction p; intros j i n HP HIJ.
    - assert (n = 1) by (apply perm_length in HP; easy); subst.
      assert (i = 0) by (apply perm_range with (i := i) in HP; [omega|left; easy]).
      omega.
    - unfold rem_perm, image.
      match goal with
      | |- context [findIndex ?j (map ?f ?l)] =>
        rewrite <- (findIndex_map f (a :: p))
      end.
      rewrite if_false by omega.
      reflexivity.
      easy.
      fold (rem_perm i (a :: p)).
      destruct n; [apply perm_length in HP; cbn in HP; discriminate|].
      eapply Permutation_NoDup;
        [symmetry; apply rem_perm_Perm; apply HP|apply seq_NoDup].
      assert (i < n) by (eapply perm_range; [apply HP|left; easy]).
      assert (In j (i :: a :: p)). {
        eapply Permutation_in; [symmetry; apply HP|].
        apply in_seq. omega.
      }
      apply Exists_exists.
      exists j. split; [|easy].
      cbn in H1; cbn. intuition.
  Qed.

  Theorem rem_perm_Stable : forall p i l,
      i < length l ->
      stable_perm l (i :: p) ->
      stable_perm (rem_nth i l) (rem_perm i p).
  Proof.
    intros p k l HI [HP HS].
    split; [apply rem_perm_Perm; rewrite rem_nth_length; destruct l; easy|].
    intros i j d HIJ HE.
    assert (IK : image (k :: p) k = 0) by (cbn; rewrite if_true; easy).
    remember (length l) as n.
    destruct n; [apply perm_length in HP; omega|].
    rewrite rem_nth_length in HIJ by omega.
    destruct (le_lt_dec k i); [|destruct (le_lt_dec k j)].
    - assert (k <= j) by omega.
      rewrite !image_ge_rem_perm with (n := n) by (omega || easy).
      apply (Nat.pred_lt_mono (image (k :: p) (S i))).
      rewrite <- IK.
      intro c.
      apply image_inj with (n := S n) in c; (omega || easy).
      apply HS with (d := d); [omega|].
      rewrite !nth_ge_rem_nth in HE by omega.
      easy.
    - rewrite image_ge_rem_perm with (j := j) (n := n) by (omega || easy).
      rewrite image_lt_rem_perm with (j := i) (n := n) by (omega || easy).
      apply (Nat.pred_lt_mono (image (k :: p) i)).
      rewrite <- IK.
      intro c.
      apply image_inj with (n := S n) in c; (omega || easy).
      apply HS with (d := d); [omega|].
      rewrite @nth_ge_rem_nth with (j := j) in HE by omega.
      rewrite @nth_lt_rem_nth with (j := i) in HE by omega.
      easy.
    - rewrite !image_lt_rem_perm with (n := n) by easy.
      apply (Nat.pred_lt_mono (image (k :: p) i)).
      rewrite <- IK.
      intro c.
      apply image_inj with (n := S n) in c; (omega || easy).
      apply HS with (d := d); [omega|].
      rewrite !nth_lt_rem_nth in HE by omega.
      easy.
  Qed.

  Theorem stable_perm_StablePerm : forall p l,
      stable_perm l p -> Stable (apply p l) l.
  Proof.
    setoid_rewrite stable_perm_image_preimage.
    intros p l.
    remember (length l) as n.
    revert p l Heqn.
    induction n as [|n IH]; intros p l HL [HP HS].
    - symmetry in HL; apply length_zero_iff_nil in HL; subst.
      apply perm_0 in HP; subst.
      reflexivity.
    - destruct l as [|a l]; [inversion HL|].
      destruct p as [|i p]; [apply perm_S_nil in HP; contradiction|].
      rewrite rem_hd_perm with (d := a) by easy.
      assert (forall k, k < i -> nth i (a :: l) a =/= nth k (a::l) a). {
        intros k HK.
        assert (k < length (a :: l)). {
          transitivity i; [easy|].
          apply perm_range with (p := i :: p); [|left]; easy.
        }
        specialize (HS 0 (image (i::p) k) a).
        rewrite nth_image_apply in HS by easy.
        cbn [apply map] in HS; rewrite !nth_first in HS; cbn [hd] in HS.
        rewrite preimage_image with (n := length (a :: l)) in HS by easy.
        assert (L: 0 < image (i :: p) k < length (a :: l)). {
          destruct (Nat.eq_dec (image (i :: p) k) 0).
          - subst. unfold image in e.
            apply f_equal with (f := fun x => nth x (i :: p) 0) in e.
            rewrite findIndex_correct in e. cbn in e.
            omega.
            apply perm_i_exists with (n := length (a :: l)); [easy|].
            transitivity i; [easy|].
            apply perm_range with (p := i :: p); [|left]; easy.
          - split; [omega|].
            unfold image.
            erewrite <- perm_length by apply HP.
            apply findIndex_bounds.
            apply perm_i_exists with (n := length (a :: l)); [easy|].
            transitivity i; [easy|].
            apply perm_range with (p := i :: p); [|left]; easy.
        }
        intro c.
        specialize (HS L c).
        cbn in HS.
        omega.
      }
      transitivity (nth i (a :: l) a :: rem_nth i (a :: l)).
      apply Stable_skip.
      apply IH.
      rewrite rem_nth_length;
        [cbn in *; omega|eapply perm_range; [apply HP|left; easy]].
      apply stable_perm_image_preimage.
      apply rem_perm_Stable;
        [eapply perm_range; [apply HP|left; easy]
        |apply stable_perm_image_preimage; easy].
      symmetry. apply rem_nth_Stable;
                  [eapply perm_range; [apply HP|left; easy]|easy].
  Qed.

  Theorem stable_perm_ex_StablePerm_iff : forall l l',
       Stable l l' <-> exists p, stable_perm l p /\ apply p l = l'.
  Proof.
    split.
    - apply stable_perm_ex_Stable.
    - intros [p []].
      subst l'.
      symmetry; apply stable_perm_StablePerm.
      easy.
  Qed.
End Stable.
