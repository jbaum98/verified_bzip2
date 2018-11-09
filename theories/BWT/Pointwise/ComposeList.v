Require Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Combinators.

Reserved Notation "❲ A --> B ❳" (format "❲ A  -->  B ❳") .

Inductive compose_list : Type -> Type -> Type :=
| compose_list_nil : forall A, ❲A --> A❳
| compose_list_cons : forall A B C, (B -> C) -> ❲A --> B❳ -> ❲A --> C❳
where "❲ A --> B ❳" := (compose_list A B) : type_scope.

Arguments compose_list_nil {_}.
Arguments compose_list_cons {_} {_} {_}.

Infix ":∘:" := compose_list_cons (at level 60, right associativity) : compose_scope.

Notation "id{ A }" := (@compose_list_nil A) (format "id{ A }") : compose_scope.
Notation "❲ ❳" := compose_list_nil  : compose_scope.
Notation "❲ x ❳" := (compose_list_cons x compose_list_nil) : compose_scope.
Notation "❲ x ∘ y ∘ .. ∘ z ❳" :=
  (compose_list_cons
     x (compose_list_cons
          y .. (compose_list_cons z compose_list_nil) ..))
    (format "❲ x  ∘  y  ∘  ..  ∘  z ❳")
  : compose_scope.

Open Scope compose_scope.
Open Scope program_scope.

Program Fixpoint capply {A B} (f : ❲A --> B❳) : A -> B :=
  match f in ❲A' --> B'❳ return (A = A' -> B = B' -> A' -> B') with
  | id{_} => _
  | h :∘: tl => fun _ => _ (capply tl)
  end _ _.

Arguments capply {_} {_} _ _ : simpl never.

Theorem capply_nil {A} : capply id{A} = id.
Proof. reflexivity. Qed.
Hint Rewrite @capply_nil.

Theorem capply_cons {A B C} : forall (g : B -> C) (f : ❲A --> B❳),
    capply (g :∘: f) = Basics.compose g (capply f).
Proof. reflexivity. Qed.
Hint Rewrite @capply_cons.

Program Fixpoint capp {A B C} (f : ❲B --> C❳) (g : ❲A --> B❳) : ❲A --> C❳ :=
  match f in ❲B' --> C'❳ return (B = B' -> C = C' -> ❲A --> C❳) with
  | id{_} => _
  | h :∘: tl =>
    fun _ _ => _ (h :∘: (@capp A _ _ tl _))
  end _ _.

Arguments capp {_} {_} {_} _ _ : simpl never.

Infix "+∘+" := capp (at level 60, right associativity) : compose_scope.

Theorem capp_nil {A B} : forall g : ❲A --> B❳, id{B} +∘+ g = g.
Proof. reflexivity. Qed.
Hint Rewrite @capp_nil.

Theorem capp_cons {A B C D} : forall (h : C -> D) (f : ❲B --> C❳) (g : ❲A --> B❳),
    (h :∘: f) +∘+ g = h :∘: (f +∘+ g).
Proof. reflexivity. Qed.
Hint Rewrite @capp_cons.

Theorem capply_app {A B C} : forall (f : ❲B --> C❳) (g : ❲A --> B❳),
    capply (f +∘+ g) = Basics.compose (capply f) (capply g).
Proof.
  induction f; intros.
  - autorewrite with core. easy.
  - autorewrite with core. rewrite IHf. reflexivity.
Qed.
