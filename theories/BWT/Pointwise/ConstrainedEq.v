Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BWT.Pointwise.ComposeList.

Fixpoint constr_eq {A B} (constrs : list (A -> Prop)) (f g : [A --> B]) (x : A): Prop :=
  match constrs with
  | nil => capply f x = capply g x
  | cons constr constrs => constr x -> constr_eq constrs f g x
  end.

Definition constr_ext_eq {A B} constrs (f g : [A --> B]) : Prop
  := forall x, constr_eq constrs f g x.

Notation "f ≡ g 'given' c" := (constr_ext_eq c f g) (at level 100).

Goal ((fun x => x) :∘: id{nat} ≡ (fun x => 2 * x) :∘: id{nat} given [fun x => x = 0]).
Proof.
  unfold constr_ext_eq, constr_eq.
  intros x Hx. simpl constr_eq. autorewrite with core. rewrite !Hx.
  reflexivity.
Qed.
