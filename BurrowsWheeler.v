Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Rotation.
Require Import Prefix.
Require Import Ord.
Require Import Repeat.
Require Import Rots.
Require Import Instances.
Require Import Pointfree.
Require Import Lib.

Import ListNotations.

Open Scope program_scope.

Section SortRotations.
  Context {A : Type} `{O : Ord A}.

  Lemma sort_succ_k : forall k,
      sort (S k) = sort 1 ∘ map rrot ∘ sort k ∘ map lrot.
  Proof.
  Admitted.

  Theorem sort_rrot_k : forall k,
    sort k ∘ map (rep rrot k) = rep (sort 1 ∘ map rrot) k.
  Proof.
  Admitted.

  Lemma sort_succ_rrot : forall k,
      sort (S k) ∘ map rrot = sort 1 ∘ map rrot ∘ sort k.
  Proof.
    intros.
    pose proof rep_inv_r (@lrot A) rrot l_r_rot_inverse as rep_inv.

    replace rrot with (rep (@rrot A) 1) at 1 by reflexivity.
    replace 1 with (S k - k) at 1 by omega.
    rewrite <- rep_inv by omega.
    rewrite <- map_map', <- ?compose_assoc.

    rewrite <- compose_id_right.
    replace (@id (list (list A))) with (map (rep (@rrot A) 0))
      by (extensionality l; apply map_id).
    replace 0 with (k - k) at 2 by omega.
    rewrite <- rep_inv by omega.
    rewrite <- map_map', <- ?compose_assoc.

    f_equal.
    symmetry; crewrite sort_rrot_k; symmetry.
    apply sort_rrot_k.
  Qed.
End SortRotations.

Section Cols.
  Context {A : Type}.

  Definition cols j := map (@firstn A j).

  Context `{Ord A}.

  Theorem cols_sort1 : forall k j,
      cols j ∘ sort k = cols j ∘ sort (Nat.min j k).
  Admitted.

  Theorem cols_sort2 : forall k j,
      cols j ∘ sort k = sort (Nat.min j k) ∘ cols j.
  Admitted.

  Lemma cols_sort_lt : forall k j,
      j <= k -> cols j ∘ sort k = sort j ∘ cols j.
  Proof.
    intros.
    replace j with (Nat.min j k) at 2 by (apply Min.min_l; auto).
    apply cols_sort2.
  Qed.

  Theorem cols_sort_perm : forall k j p,
      (forall l, Permutation l (p l)) -> cols j ∘ sort k ∘ p  = cols j ∘ sort k.
  Admitted.

  Theorem cols_sort_shift : forall k j,
      1 <= j <= k ->
      cols j ∘ sort k ∘ rots = sort 1 ∘ cols j ∘ map rrot ∘ sort k ∘ rots.
  Proof.
    intros.
    replace 1 with (Nat.min j 1) by (apply Min.min_r; omega).
    crewrite <- cols_sort2.
    crewrite <- sort_succ_rrot.
    crewrite map_rrot_rots.
    crewrite cols_sort2.
    crewrite cols_sort_perm by apply rrot_perm.
    crewrite cols_sort2.
    replace (Nat.min j (S k)) with (Nat.min j k) by (rewrite ?Nat.min_l; omega).
    reflexivity.
  Qed.

  Theorem cols_id : forall n mat,
      Forall (fun x => length x <= n) mat -> cols n mat = mat.
  Proof.
    induction n; intros mat HL.
    - unfold cols. unfold firstn.
      rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      simpl; intros.
      assert (length a = 0) by omega.
      symmetry. apply length_zero_iff_nil; auto.
    - unfold cols. rewrite <- map_id.
      apply map_forall_eq.
      eapply Forall_impl; [|apply HL].
      cbv beta. intros.
      apply firstn_all2; auto.
  Qed.
End Cols.

Definition zipWith {A B C} (f : A -> B -> C) : (list A * list B) -> list C :=
  let zipWith' :=
      fix zipWith' a b :=
      match (a, b) with
      | (a :: atl, b :: btl) => f a b :: zipWith' atl btl
      | _ => []
      end
  in fun p => let (a, b) := p in zipWith' a b.

Section Fork.
  Definition fork {A B C} (p : (A -> B) * (A -> C)) : A -> (B * C)
    := fun a => let (f, g) := p in (f a, g a).

  Theorem fork_compose {A B C D} : forall (h : A -> B) (f : B -> C) (g : B -> D),
      fork (f, g) ∘ h = fork (f ∘ h, g ∘ h).
  Proof. intros. extensionality x. reflexivity. Qed.

  Theorem fork_map_zip {A B C D} :
    forall (f : A -> B) (g : A -> C) (h : B -> C -> D) a (l : list A),
      (zipWith h ∘ fork (map f, map g)) (a :: l)
      =
      h (f a) (g a) :: ((zipWith h ∘ fork (map f, map g)) l).
  Proof. intros. reflexivity. Qed.
End Fork.

Section PrependColumn.
  Context {A : Type}.

  Definition prepend_col : list A * list (list A) -> list (list A) :=
     zipWith cons.

  Lemma prepend_cons : forall a b atl btl,
      prepend_col (a :: atl, b :: btl) = (a :: b) :: prepend_col (atl, btl).
  Proof. reflexivity. Qed.

  Theorem prepend_hd_tl : forall l d,
      Forall (fun x => ~ x = []) l ->
      (prepend_col ∘ fork (map (hd d), map (@tl A))) l = l.
  Proof.
    induction l; intros.
    - simpl. reflexivity.
    - inversion H; subst; clear H.
      unfold prepend_col. rewrite fork_map_zip.
      destruct a as [|ahd atl] eqn:HA; [contradiction|];
      rewrite <- hd_tl_destr; rewrite <- HA in *; clear HA ahd atl.
      f_equal. apply IHl. auto.
  Qed.

  Lemma cols_rrot : forall j d,
      cols (S j) ∘ map rrot = prepend_col ∘ fork (map (last' d), cols j).
  Admitted.
End PrependColumn.

Section AppendCol.
  Context {A : Type}.

  Definition append_col : (list A * list (list A)) -> list (list A)
    := map lrot ∘ prepend_col.

  Theorem map_lrot_prepend : map lrot ∘ prepend_col = append_col.
  Proof. reflexivity. Qed.

  Theorem map_rrot_append : map rrot ∘ append_col = prepend_col.
  Proof.
    intros.
    apply inj_compose_left with (f := map lrot);
      [intros; eapply map_injective; [apply lrot_injective|easy]|].
    crewrite map_map'. rewrite r_l_rot_inverse.
    crewrite map_id'.
    apply map_lrot_prepend.
  Qed.

  Theorem append_last_init : forall l d,
      Forall (fun x => ~ x = []) l ->
      (append_col ∘ fork (map (last' d), map init)) l = l.
  Proof.
    intros. unfold append_col.
    rewrite <- hd_rrot, <-  tl_rrot.
    rewrite <- ?map_map'.
    rewrite <- fork_compose.
    compose_pop_right; compose_pop_left.
    rewrite prepend_hd_tl.
    rewrite map_map, <- map_id.
    eapply map_ext; intros; xrewrite r_l_rot_inverse; easy.

    apply Forall_forall. intros x HI; apply in_map_iff in HI.
    destruct HI as [x' [HR HI]].
    subst. apply rrot_nonempty.
    eapply Forall_forall with (P := fun y => ~ y = []); eauto.
  Qed.

  Theorem map_rrot_prepend : forall (l : list (list A)) d,
      Forall (fun x => ~ x = []) l ->
      map rrot l = (prepend_col ∘ fork (map (last' d), map init)) l.
  Proof.
    intros.
    apply map_injective with (f := lrot); [apply lrot_injective|].
    rewrite map_map.
    erewrite map_ext; [|intros; xrewrite r_l_rot_inverse; easy].
    rewrite map_id.
    compose_push_left.
    crewrite map_lrot_prepend.
    symmetry. apply append_last_init. auto.
  Qed.

  Theorem map_lrot_append : forall l d,
      Forall (fun x => ~ x = []) l ->
      map lrot l = (append_col ∘ fork (map (hd d), map tl')) l.
  Proof.
    intros. unfold append_col.
    compose_pop_left.
    rewrite prepend_hd_tl; auto.
  Qed.
End AppendCol.

Section Lexsort.
  Context {A : Type} `{Ord A}.

  Lemma orig_in_sorted_rots : forall l k,
      l <> [] -> Exists (eq l) (sort k (rots l)).
  Proof.
    intros.
    apply Permutation_exists with (l0 := rots l) (l' := sort k (rots l)).
    apply sort_perm.
    apply orig_in_rots. auto.
  Qed.

  Lemma sort_rots_len : forall k l,
      Forall (fun x => length x = length l) (sort k (rots l)).
  Proof.
    intros.
    eapply Permutation_forall.
    apply sort_perm. apply rots_row_length.
  Qed.
End Lexsort.

Section FindIndex.
  Context {A : Type} `{EqDec A}.

  Fixpoint findIndex (x : A) (ls : list A) : nat :=
    match ls with
    | [] => 0
    | hd :: tl =>
      match x == hd with
      | left _ => 0
      | right Neq => S (findIndex x tl)
      end
    end.

  Theorem findIndex_correct : forall x xs d,
      Exists (equiv x) xs -> nth (findIndex x xs) xs d === x.
  Proof.
    intros x xs d E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply equiv_symmetric. auto.
      + apply IHE.
  Qed.

  Theorem findIndex_bounds : forall x xs,
      Exists (equiv x) xs -> findIndex x xs < length xs.
  Proof.
    intros x xs E.
    unfold findIndex.
    induction E.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + contradiction.
    - destruct (x == x0).
      + simpl. apply Nat.lt_0_succ.
      + simpl. apply le_n_S. apply IHE.
  Qed.
End FindIndex.

Section Transform.
  Context {A : Type} `{O: Ord A} `{E : EqDec A eq}.

  Definition lexsort l : list (list A) := sort (length l) l.

  Definition bwp (l: list A) : list A :=
    match l with
    | [] => const []
    | hd :: tl => map (last' hd) ∘ lexsort ∘ rots
    end l.

  Theorem bwp_nonempty : forall l,
      l <> [] ->
      forall d, bwp l = (map (last' d) ∘ lexsort ∘ rots) l.
  Proof.
    destruct l eqn:HL; intros.
    - contradiction.
    - unfold bwp, compose.
      rewrite <- HL in *; clear HL l0.
      apply map_forall_eq; apply Forall_forall.
      intros x HI.
      apply last_nonempty.
      eapply Forall_forall with (P := fun x => ~ x = []); [|eauto].
      eapply Permutation_forall. apply sort_perm.
      apply rots_nonempty; auto.
  Qed.

  Theorem bwp_length : forall l,
      length (bwp l) = length l.
  Proof.
    induction l.
    - reflexivity.
    - simpl. unfold bwp, lexsort, compose.
      rewrite map_length, sort_length, rots_length.
      reflexivity.
  Qed.

  Theorem bwp_length' : @length A ∘ bwp = @length A.
  Proof.
    extensionality l. unfold compose. apply bwp_length.
  Qed.

  Definition bwn (l : list A) : nat :=
    findIndex l (lexsort (rots l)).

  Theorem bwn_correct : forall xs d,
    xs <> [] -> nth (bwn xs) (lexsort (rots xs)) d = xs.
  Proof.
    intros.
    unfold bwn.
    apply findIndex_correct.
    apply orig_in_sorted_rots. auto.
  Qed.
End Transform.

Lemma map_const {A B} : forall (f : A -> B) c,
    (forall x, f x = c) -> map f = repeat c ∘ @length A.
Proof.
  intros. extensionality l. unfold compose.
  induction l; [reflexivity|].
  simpl. rewrite H. f_equal. auto.
Qed.

Section Recreate.
  Context {A : Type} `{Ord A}.

  Fixpoint recreate (j : nat) : list A -> list (list A) :=
    match j with
    | O    => map (const [])
    | S j' => sort 1 ∘ prepend_col ∘ fork (id, recreate j')
    end.

  Theorem recreate_inspiration : forall j k d,
      j < k ->
      cols (S j) ∘ sort k ∘ rots =
      sort 1 ∘ prepend_col ∘
           fork (map (last' d) ∘ sort k ∘ rots, cols j ∘ sort k ∘ rots).
  Proof.
    intros.
    crewrite cols_sort_shift.
    crewrite cols_rrot.
    crewrite fork_compose.
    remember (map _ ∘ _) as f; crewrite fork_compose.
    subst f. reflexivity.
    omega.
  Qed.

  Lemma recreate_correct_gen : forall j l,
      j <= length l ->
      (recreate j ∘ bwp) l = (cols j ∘ lexsort ∘ rots) l.
  Proof.
    induction j; intros.
    - unfold cols. simpl.
      do 2 (crewrite map_const; [|unfold const; reflexivity]).
      crewrite bwp_length'.
      crewrite sort_length''.
      crewrite rots_length'.
      reflexivity.
    - simpl.
      replace ((cols (S j) ∘ lexsort ∘ rots) l)
      with ((cols (S j) ∘ sort (length l) ∘ rots) l)
        by (unfold compose, lexsort; rewrite rots_length; easy).
      destruct l eqn:HL; [simpl in *; omega|].
      rewrite <- HL in *.
      crewrite (recreate_inspiration j (length l) a) by omega.
      crewrite fork_compose.
      unfold compose, fork; do 4 f_equal.
      + erewrite bwp_nonempty. unfold compose, lexsort.
        rewrite rots_length. reflexivity. intro c. rewrite c in *. discriminate.
      + unfold compose in IHj. rewrite IHj. unfold lexsort. rewrite rots_length.
        reflexivity.
        omega.
  Qed.

  Theorem recreate_correct : forall l,
      recreate (length l) (bwp l) = lexsort (rots l).
  Proof.
    intros.
    pose proof (recreate_correct_gen (length l) l) as R.
    unfold compose in R. rewrite R by omega.
    rewrite cols_id; [unfold lexsort; rewrite rots_length; reflexivity|].
    eapply Forall_impl; [|apply sort_rots_len].
    cbv beta; intros; omega.
  Qed.
End Recreate.

Section Unbwt.
  Context {A : Type} `{O : Ord A} `{E : EqDec A eq}.

  Definition unbwt (t : nat) (l : list A) : list A :=
    nth t (recreate (length l) l) l.

  Theorem unbwt_correct : forall xs : list A,
      unbwt (bwn xs) (bwp xs) = xs.
  Proof.
    intros xs; destruct xs as [|a tl] eqn:Hxs; [reflexivity|].
    rewrite <- Hxs in *.
    unfold unbwt.
    rewrite bwp_length.
    rewrite recreate_correct.
    apply bwn_correct.
    intro contra; rewrite contra in *; discriminate.
  Qed.
End Unbwt.
