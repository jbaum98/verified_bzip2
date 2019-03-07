Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Sorting.Permutation.

Require Import BWT.Lib.Permutation.

Import Coq.Lists.List.ListNotations.

Section HeadTailInitLast.
  Context {A : Type}.

  (* Drop the last element of a list. *)
  Fixpoint init l : list A :=
    match l with
    | [] | [_] => []
    | hd :: tl => hd :: init tl
    end.

  Lemma last2 : forall (l : list A) (a b d : A),
      last (a :: b :: l) d = last (b :: l) d.
  Proof.
    reflexivity.
  Qed.

  Lemma init2 : forall (l : list A) (a b : A),
      init (a :: b :: l) = a :: init (b :: l).
  Proof.
    reflexivity.
  Qed.

  (* An induction scheme that considers the singleton list as a
     separate case and steps by two elements at a time. *)
  Theorem list_ind2 : forall (P : list A -> Prop),
      P [] ->
      (forall a, P [a]) ->
      (forall a b l, P (b :: l) -> P (a :: b :: l)) ->
      forall l : list A, P l.
  Proof.
    intros P HBase HOne HInd.
    refine (
        fix F l : P l :=
          match l as l' return l = l' -> P l' with
          | []  => fun _ => HBase
          | [x] => fun _ => HOne x
          | a :: tl => fun HL => _
          end eq_refl
      ).
    destruct l. rewrite <- HL. exact HBase.
    inversion HL. apply HInd. rewrite <- H1. apply F.
  Qed.

  Lemma last_app : forall (l: list A) (x d: A),
      last (l ++ [x]) d = x.
  Proof.
    induction l as [| x | a b tl IH] using list_ind2;
      intros; try reflexivity.
    do 2 rewrite <- app_comm_cons.
    rewrite last2.
    apply IH.
  Qed.

  Lemma init_app : forall (x y: list A) a,
      init (x ++ a :: y) = x ++ init (a :: y).
  Proof.
    induction x as [| x | a b tl IH] using list_ind2;
      intros; try reflexivity.
    do 2 rewrite <- app_comm_cons.
    rewrite init2.
    rewrite <- app_comm_cons at 1.
    f_equal.
    apply IH.
  Qed.

  Lemma l_app_nil_inv : forall (a b : A) (l : list A),
      l ++ [b] = [a] -> l = [] /\ a = b.
  Proof.
    destruct l as [|hd tl].
    - split; auto. rewrite app_nil_l in H.
      inversion H; auto.
    - intros contra. inversion contra.
      symmetry in H1. apply app_cons_not_nil in H1. contradiction.
  Qed.

  Lemma last_nonempty : forall (l: list A) d d',
      l <> [] -> last l d = last l d'.
  Proof.
    induction l as [| a | a b tl IH] using list_ind2;
      intros; try contradiction; clear H.
    - reflexivity.
    - do 2 rewrite last2.
      apply IH.
      intro contra; inversion contra.
  Qed.

  Lemma hd_tl_destr : forall (x : A) xs d,
      x :: xs = (hd d (x :: xs)) :: (tl (x :: xs)).
  Proof.
    reflexivity.
  Qed.

  Lemma init_last_destr : forall xs x d,
      x :: xs = init (x :: xs) ++ [last (x :: xs) d].
  Proof.
    induction xs; intros.
    - reflexivity.
    - rewrite init2. rewrite <- app_comm_cons.
      f_equal. rewrite last2.
      apply IHxs.
  Qed.

  Lemma tl_len : forall l : list A,
      length (tl l) = Nat.pred (length l).
  Proof.
    induction l; reflexivity.
  Qed.

  Lemma init_len : forall l : list A,
      length (init l) = Nat.pred (length l).
  Proof.
    induction l using list_ind2; intros; try reflexivity.
    rewrite init2.
    replace (length (a :: _)) with (S (length (init (b :: l)))) by reflexivity.
    rewrite IHl. reflexivity.
  Qed.

  Lemma firstn_init : forall j l,
      j < length l ->
      firstn j (init l) = firstn j l.
  Proof.
    intros j l; revert j; induction l; intros j; [reflexivity|].
    cbn [length]; intros HJ.
    destruct j; [reflexivity|].
    assert (j < length l) by omega; clear HJ.
    destruct l as [|b l]; [cbn in H; omega|].
    rewrite init2. cbn [firstn]. f_equal. apply IHl. auto.
  Qed.
End HeadTailInitLast.

Section Forall2.
  Lemma Forall2_eq {A : Type} : forall x y : list A,
      Forall2 eq x y <-> x = y.
  Proof.
    split; intros.
    - induction H.
      + reflexivity.
      + subst. f_equal.
    - subst. induction y; constructor; auto.
  Qed.

  Theorem Forall2_length {A : Type} : forall (R : A -> A -> Prop) (l l' : list A),
      Forall2 R l l' ->
      length l = length l'.
  Proof.
    intros R l l' HF.
    induction HF; cbn; auto.
  Qed.

  Lemma Forall2_map {A B : Type} (R : B -> B -> Prop) : forall (f : A -> B) (l l' : list A),
      Forall2 R (map f l) (map f l') <-> Forall2 (fun x y => R (f x) (f y)) l l'.
  Proof.
    induction l; intros.
    - split; intros H; replace l' with (@nil A); [constructor| |constructor|].
      + cbn in H. inversion H. symmetry in H0. apply map_eq_nil in H0. auto.
      + inversion H. auto.
    - destruct l' as [|a' l']; [split; cbn; intros H; inversion H|].
      simpl; split; intros HImp; inversion HImp; subst; clear HImp; constructor; auto; apply IHl; auto.
  Qed.

  Lemma Forall2_impl : forall (A B : Type) (P Q : A -> B -> Prop),
      (forall a b, P a b -> Q a b) -> forall l l', Forall2 P l l' -> Forall2 Q l l'.
  Proof.
    intros. induction H0; constructor; auto.
  Qed.
End Forall2.

Section Map.
  Open Scope program_scope.

  Lemma eq_map {A B : Type} (f g : A -> B) l :
    (forall x, f x = g x) -> map f l = map g l.
  Proof.
    intros HExt; induction l; try reflexivity.
    simpl; rewrite HExt, IHl.
    reflexivity.
  Qed.

  Lemma map_map' {A B C : Type} : forall (f : A -> B) (g : B -> C) l,
      map g (map f l) = map (g ∘ f) l.
  Proof.
    intros.
    rewrite map_map. apply eq_map.
    reflexivity.
  Qed.

  Lemma map_injective {A B : Type} : forall (f : A -> B) l l',
      (forall x y, f x = f y -> x = y) ->
      map f l = map f l' -> l = l'.
  Proof.
    intros f l l' HInj MapEq.
    assert (length l = length l'). {
      rewrite <- map_length with (f := f), MapEq, -> map_length.
      easy.
    }
    assert (Forall2 (fun x y => f x = f y) l l'). {
      apply Forall2_eq in MapEq.
      apply (proj1 (Forall2_map eq f l l')) in MapEq.
      apply MapEq.
    }
    apply Forall2_eq.
    eapply Forall2_impl; [| apply H0].
    cbv beta; intros. auto.
  Qed.

  Lemma map_forall_eq {A B : Type} : forall (l : list A) (f g : A -> B),
      Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof.
    induction l; intros.
    - reflexivity.
    - inversion H; subst; clear H.
      simpl. f_equal; auto.
  Qed.

  Lemma map_const {A B} : forall (f : A -> B) l c,
      (forall x, f x = c) -> map f l = repeat c (length l).
  Proof.
    intros.
    induction l; [reflexivity|].
    simpl. rewrite H. f_equal. auto.
  Qed.
End Map.

Section Filter.
  Context {A : Type}.

  Implicit Types (l : list A) (f : A -> bool).

  Remark filter_app: forall f l l',
      filter f (l ++ l') = filter f l ++ filter f l'.
  Proof.
    induction l; intros; simpl. auto.
    destruct (f a); simpl. f_equal; auto. auto.
  Qed.

  Remark filter_empty: forall f l,
      (forall x, In x l -> f x = false) ->
      filter f l = nil.
  Proof.
    induction l; simpl; intros.
    auto.
    rewrite (H a (or_introl eq_refl)).
    apply IHl. auto.
  Qed.

  Remark filter_sublist: forall f x l l1' l2',
      filter f l = l1' ++ x :: l2' ->
      exists l1, exists l2, l = l1 ++ x :: l2 /\ filter f l1 = l1' /\ filter f l2 = l2'.
  Proof.
    induction l; intros until l2'; simpl.
    intro. destruct l1'; simpl in H; discriminate.
    case_eq (f a); intros.
    destruct l1'; simpl in H0; injection H0; clear H0; intros.
    subst x. exists (@nil A); exists l. auto.
    subst a0. destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. congruence. auto.
    destruct (IHl _ _ H0) as [l1 [l2 [P [Q R]]]]. subst l.
    exists (a :: l1); exists l2.
    split. auto. split. simpl. rewrite H. auto. auto.
  Qed.
End Filter.

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

Lemma length_nonempty_destr {A} : forall (xs : list A) l,
    S l <= length xs ->
    (xs <> []) * A.
Proof.
  intros [|h t] l.
  - simpl; omega.
  - simpl; intro HL; split.
    + intro c; inversion c.
    + exact h.
Qed.

Section Rem1.
  Context {A : Type} `{EqDec A eq}.

  Fixpoint rem1 (x : A) (l : list A) : list A
    := match l with
       | [] => []
       | h :: t => if x == h then t else h :: rem1 x t
       end.

  Theorem rem1_in_split : forall x a,
      In a x ->
      exists l1 l2, x = l1 ++ a :: l2 /\ rem1 a x = l1 ++ l2.
  Proof.
    induction x as [|hx tx]; intros a HIn; [inversion HIn|].
    cbn [rem1].
    destruct (equiv_dec a hx).
    + subst.
      exists [], tx. split; cbn; auto.
      rewrite e. auto.
    + destruct (IHtx a) as [l1 [l2 [Htx Hrem]]].
      destruct HIn; [rewrite H0 in c; exfalso; apply c; reflexivity|auto].
      exists (hx :: l1), l2.
      split; [rewrite Htx; reflexivity|].
      cbn. f_equal. auto.
  Qed.

  Theorem Permutation_rem1 : forall x a y,
      Permutation (a :: x) y -> Permutation x (rem1 a y).
  Proof.
    intros x a y HP.
    destruct (rem1_in_split y a) as [l1 [l2 [Hy Hyrem]]].
    eapply Permutation_in; [apply HP|left; auto].
    rewrite Hyrem.
    apply Permutation_cons_inv with (a := a).
    transitivity y; [auto|].
    rewrite Hy. symmetry. apply Permutation_cons_app.
    reflexivity.
  Qed.

  Theorem in_rem1_in : forall a b x,
      In a (rem1 b x) -> In a x.
  Proof.
    intros a b x. revert a b.
    induction x as [|h t]; intros a b HIn; [inversion HIn|].
    cbn in *. destruct (equiv_dec b h).
    - right; auto.
    - destruct HIn.
      + left; auto.
      + right; eapply IHt. apply H0.
  Qed.

  Theorem in_in_rem1_neq : forall a b x,
       In a x -> In a (rem1 b x) \/ a = b.
  Proof.
    intros a b x.
    destruct (equiv_dec a b); [auto|].
    induction x as [|h t]; intros HIn; [inversion HIn|left].
    cbn. destruct (equiv_dec b h).
    - destruct HIn; [|auto].
      exfalso. apply c. symmetry. transitivity h; auto.
    - destruct HIn; [left; auto|].
      destruct IHt; [|right|exfalso; apply c]; auto.
  Qed.

  Theorem rem1_map : forall f l x,
      map f (rem1 x l) = rem1 (f x) (map f l).
  Admitted.
End Rem1.
