Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.omega.Omega.
Require Import Coq.Init.Nat.
Import Coq.Lists.List.ListNotations.

Require Import BWT.Lib.Permutation.
Require Import BWT.Lib.Sumbool.
Require Import BWT.Lib.List.

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
