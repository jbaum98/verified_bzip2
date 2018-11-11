Require Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.

Reserved Notation "[ A --> B ]" (format "[ A  -->  B ]") .

Inductive flist : Type -> Type -> Type :=
| fnil : forall A, [A --> A]
| fcons : forall A B C, (B -> C) -> [A --> B] -> [A --> C]
where "[ A --> B ]" := (flist A B) : type_scope.

Infix ":∘:" := (fcons _ _ _) (at level 60, right associativity) : flist_scope.

Delimit Scope flist_scope with flist.
Bind Scope flist_scope with flist.

Arguments fnil {A}%type.
Arguments fcons {A}%type {B}%type {C}%type f (fl)%flist.

Open Scope flist_scope.

Notation "[ ]" := fnil : flist_scope.
Notation "id{ A }" := (@fnil A) (format "id{ A }") : flist_scope.
Notation "[ f ]" := (f :∘: id{_}) : flist_scope.
Notation "[ a ∘ b ∘ .. ∘ c ]" :=
  (a :∘: b :∘: .. (c :∘: id{_}) ..) : flist_scope.

Local Notation " g `∘` f " := (Basics.compose g f)
  (at level 40, left associativity).

Local Open Scope flist_scope.

Program Fixpoint fapply {A B} (f : [A --> B]) : A -> B :=
  match f in [A' --> B'] return (A = A' -> B = B' -> A' -> B') with
  | [] => _
  | h :∘: tl => fun _ => _ (fapply tl)
  end _ _.

Arguments fapply : simpl never.

Theorem fapply_nil {A} : fapply id{A} = id.
Proof. reflexivity. Qed.
Hint Rewrite @fapply_nil : flist.

Theorem fapply_cons {A B C} : forall (g : B -> C) (f : [A --> B]),
    fapply (g :∘: f) = g `∘` fapply f.
Proof. reflexivity. Qed.
Hint Rewrite @fapply_cons : flist.

Program Fixpoint fapp {A B C} (f : [B --> C]) (g : [A --> B]) : [A --> C] :=
  match f in [B' --> C'] return (B = B' -> C = C' -> [A --> C]) with
  | [] => _
  | h :∘: tl =>
    fun _ _ => _ (h :∘: (@fapp A _ _ tl _))
  end _ _.

Arguments fapp : simpl never.

Infix "+∘+" := fapp (at level 60, right associativity) : flist_scope.

Theorem fapp_nil_l {A B} : forall g : [A --> B], id{B} +∘+ g = g.
Proof. reflexivity. Qed.
Hint Rewrite @fapp_nil_l : flist.

Theorem fapp_cons {A B C D} : forall (h : C -> D) (f : [B --> C]) (g : [A --> B]),
    (h :∘: f) +∘+ g = h :∘: (f +∘+ g).
Proof. reflexivity. Qed.
Hint Rewrite @fapp_cons : flist.

Theorem fapp_nil_r {A B} : forall g : [A --> B], g +∘+ id{A} = g.
Proof.
  induction g.
  - reflexivity.
  - rewrite fapp_cons. rewrite IHg. reflexivity.
Qed.
Hint Rewrite @fapp_nil_r : flist.

Theorem fapply_app {A B C} : forall (f : [B --> C]) (g : [A --> B]),
    fapply (f +∘+ g) = fapply f `∘` fapply g.
Proof.
  induction f; intros.
  - autorewrite with flist. easy.
  - autorewrite with flist. rewrite IHf. reflexivity.
Qed.

Hint Rewrite compose_id_left : flist.
Hint Rewrite compose_id_right : flist.
