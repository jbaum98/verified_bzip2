Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.

Open Scope program_scope.

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

  Lemma map_const_repeat {A B} : forall (f : A -> B) l c,
      (forall x, f x = c) -> map f l = repeat c (length l).
  Proof.
    intros.
    induction l; [reflexivity|].
    simpl. rewrite H. f_equal. auto.
  Qed.

  Lemma const_const {A} : forall c x y : A,
      const c x = const c y.
  Proof. reflexivity. Qed.

  Lemma map_const {A B C} : forall (f : A -> C) (g : B -> C),
      (forall x y, f x = g y) ->
      forall xs ys,
        length xs = length ys ->
        map f xs = map g ys.
  Proof.
    intros f g Hconst xs ys HL.
    destruct (length xs) eqn:Hn.
    - replace xs with (@nil A); replace ys with (@nil B);
        [reflexivity|symmetry; apply length_zero_iff_nil; omega..].
    - destruct xs as [|a xtl] eqn:Hxs; [cbn in Hn; omega|].
      destruct ys as [|b ytl] eqn:Hys; [cbn in Hn, HL; omega|].
      rewrite <- Hxs, <- Hys, <- Hn in *; clear Hn Hxs Hys xtl ytl.
      rewrite map_const_repeat with (c := f a)
        by (rewrite Hconst with (y := b); easy).
      rewrite map_const_repeat with (c := g b)
        by (rewrite <- Hconst with (x := a); easy).
      f_equal; auto.
  Qed.
End Map.
