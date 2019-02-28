Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.

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

  Lemma Forall2_map {A B : Type} (R : B -> B -> Prop) : forall (f : A -> B) (l l' : list A),
      length l = length l' ->
      Forall2 R (map f l) (map f l') <-> Forall2 (fun x y => R (f x) (f y)) l l'.
  Proof.
    induction l; intros.
    - simpl in H.
      replace l' with (@nil A) by (symmetry; apply length_zero_iff_nil; auto).
      split; constructor.
    - destruct l' as [|a' l']; [inversion H|].
      simpl; split; intros HImp; inversion HImp; subst; clear HImp; constructor; auto.
      + apply IHl; auto.
      + apply IHl; auto.
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
      apply (proj1 (Forall2_map eq f l l' H)) in MapEq.
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

Fixpoint zipWith {A B C} (f : A -> B -> C) (a : list A) (b : list B) : list C :=
  match (a, b) with
  | (ahd :: atl, bhd :: btl) => f ahd bhd :: zipWith f atl btl
  | _ => []
  end.

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
