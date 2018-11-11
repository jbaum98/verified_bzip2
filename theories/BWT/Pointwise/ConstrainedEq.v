Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Basics.
Import ListNotations.

Require Import BWT.Pointwise.FList.

Definition preconditions (premises: list Prop) (conc : Prop) : Prop
  := fold_right Basics.impl conc premises.

Definition constr_eq {A B} (constrs : list (A -> Prop)) (f g : [A --> B]) : Prop
  := forall x, preconditions (map (Basics.flip Basics.apply x) constrs) (fapply f x = fapply g x).

Notation "f ≡ g" := (constr_eq [] f g) (at level 100) : flist_scope.
Notation "f ≡ g 'given' c" := (constr_eq c f g) (at level 100) : flist_scope.

Ltac destr_constr_eq
  := cbv [constr_eq preconditions Basics.impl Basics.flip Basics.apply]; cbn;
     autorewrite with flist; cbn.

Goal ([fun x => x] ≡ [fun x => 2 * x] given [fun x => x = 0]).
Proof.
  destr_constr_eq.
  intros x Hx. rewrite Hx. reflexivity.
Qed.
