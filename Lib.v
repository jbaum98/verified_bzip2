Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

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
  Lemma map_forall_eq {A B : Type} : forall (l : list A) (f g : A -> B),
    Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof.
    induction l; intros.
    - reflexivity.
    - inversion H; subst; clear H.
      simpl. f_equal; auto.
  Qed.
End Map.

Section Permutation.
  Context {A : Type} {P : A -> Prop} .
  Variables l l' : list A.
  Hypothesis HP : Permutation l l'.

  Theorem Permutation_exists :
    Exists P l -> Exists P l'.
  Proof.
    intros HE.
    apply Exists_exists.
    apply Exists_exists in HE; destruct HE as [x [HIn HPx]].
    eauto using Permutation_in.
  Defined.

  Theorem Permutation_forall :
    Forall P l -> Forall P l'.
  Proof.
    intros.
    apply Forall_forall.
    intros a HA.
    apply Permutation_in with (l' := l) in HA; auto using Permutation_sym.
    revert a HA.
    apply Forall_forall.
    auto.
  Qed.
End Permutation.
