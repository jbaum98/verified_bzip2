Require Import Coq.Lists.List.

Require Export BWTactics.
Require Import Lib.

Section TlLast.
  Definition tl' {A} l := @tl A l.
  Arguments tl' /.

  Definition last' {A} d l := @last A l d.
  Arguments last' /.
End TlLast.

Section Rev.
  (* Automatically use A as type argument to rev *)
  Definition rev' {A} := @rev A.
  Arguments rev' /.

  Theorem rev_involutive' {A} :
    rev' ∘ rev' = @id (list A).
  Proof. extensionality l. apply rev_involutive. Qed.

  Theorem rev_injective' {A} : forall x x' : list A,
      rev' x = rev' x' -> x = x'.
  Proof.
    intros.
    rewrite <- rev_involutive.
    replace (rev x') with (rev' x') by reflexivity.
    rewrite <- H.
    rewrite rev_involutive.
    reflexivity.
  Qed.

 Theorem rev_surjective {A} :
   forall y : list A, exists x, rev' x = y.
 Proof.
   intros.
   exists (rev' y).
   unfold rev'. apply rev_involutive.
 Qed.
End Rev.

Section Nth.
  Context {A : Type}.

  Definition nth' i d l := @nth A i l d.

  Theorem nth_indep' : forall l n d d',
       n < length l -> nth' n d l = nth' n d' l.
  Proof. unfold nth'. exact (@nth_indep A). Qed.

  Theorem map_nth' : forall f i d,
      nth' i (f d) ∘ map f = f ∘ nth' i d.
  Proof.
    intros. extensionality l. unfold nth'.
    apply map_nth.
  Qed.
End Nth.

Section Map.
  Lemma eq_map {A B : Type} (f g : A -> B) l :
    (f = g) -> map f l = map g l.
  Proof.
    intros HE; induction l; try reflexivity.
    eapply equal_f in HE.
    simpl; rewrite HE, IHl.
    reflexivity.
  Qed.

  Lemma map_map' {A B C : Type} : forall (f : A -> B) (g : B -> C),
    map g ∘ map f = map (g ∘ f).
  Proof.
    intros. extensionality l. unfold compose.
    rewrite map_map. apply eq_map.
    reflexivity.
  Qed.

  Lemma map_id' {A} : map id = @id (list A).
  Proof. extensionality l. rewrite map_id. reflexivity. Qed.

  Lemma map_injective {A B : Type} : forall (f : A -> B) ,
      (forall x y, f x = f y -> x = y) ->
      forall x y, map f x = map f y -> x = y.
  Proof.
    intros f HInj x y MapEq.
    assert (length x = length y). {
      rewrite <- map_length with (f := f), MapEq, -> map_length.
      easy.
    }
    assert (Forall2 (fun x y => f x = f y) x y). {
      apply Forall2_eq in MapEq.
      apply (proj1 (Forall2_map eq f x y H)) in MapEq.
      apply MapEq.
    }
    apply Forall2_eq.
    eapply Forall2_impl; [| apply H0].
    cbv beta; intros. auto.
  Qed.
End Map.

Section InjectiveSurjective.
  Theorem inj_compose_left {A B C}: forall f : B -> C,
    (forall x x', f x = f x' -> x = x') ->
    forall g h : A -> B, f ∘ g = f ∘ h -> g = h.
  Proof.
    intros f HInj g h E.
    extensionality x.
    apply HInj.
    revert x. apply equal_f.
    apply E.
  Qed.

  Theorem sur_compose_right {A B C}: forall f : A -> B,
      (forall y, exists x, f x = y) ->
      forall g h : B -> C, g ∘ f = h ∘ f -> g = h.
  Proof.
    intros f HInj g h E.
    extensionality y.
    destruct HInj with (y := y) as [x Hx].
    rewrite <- Hx.
    eapply equal_f in E. unfold compose in E.
    apply E.
  Qed.
End InjectiveSurjective.
