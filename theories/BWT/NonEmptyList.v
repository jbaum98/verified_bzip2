Require Import Coq.omega.Omega.
Require Coq.Lists.List.
Require Import Coq.Program.Wf.

Import List.ListNotations.
Bind Scope list_scope with List.list.

Inductive list (A : Type) : Type :=
| wrap : A -> list A
| cons : A -> list A -> list A.

Arguments wrap {_}.
Arguments cons {_}.

Infix "::" := cons (at level 60, right associativity) : ne_list_scope.
Delimit Scope ne_list_scope with ne_list.
Bind Scope ne_list_scope with list.

Fixpoint ne_cons {A} (x : A) (xs : List.list A) : list A :=
  match xs with
  | []%list => wrap x
  | (hd :: tl)%list => x :: ne_cons hd tl
  end.

Module ListNotations.
  Notation "[ x ]" := (wrap x) : ne_list_scope.
  Notation "[ x ; y ]" := (cons x (wrap y)) : ne_list_scope.
  Notation "[ w ; x ; y ; .. ; z ]" := (ne_cons w (List.cons x (List.cons y .. (List.cons z List.nil) .. ))) : ne_list_scope.
End ListNotations.

Import ListNotations.
Open Scope ne_list_scope.

Fixpoint snoc {A} (x : A) (xs : list A) : list A :=
  match xs with
  | [y] => y :: [x]
  | hd :: tl => hd :: snoc x tl
  end.

Fixpoint ne_snoc {A} (x : A) (xs : List.list A) : list A :=
  match xs with
  | []%list => wrap x
  | (hd :: tl)%list => hd :: ne_snoc x tl
  end.

Program Fixpoint embed {A} (xs : list A) : { xs : List.list A | xs <> List.nil } :=
  match xs with
  | [x] => [x]%list
  | hd :: tl => (hd :: embed tl)%list
  end.

Program Fixpoint extract {A} (xs: { xs : List.list A | xs <> List.nil })
        {measure (length xs)}
  : list A
  :=
  match xs with
  | []%list => _
  | [x]%list => [x]
  | (hd :: tl)%list => hd :: extract tl
  end.
Next Obligation.
  specialize (H hd).
  intro contra. rewrite contra in H.
  contradiction H. easy.
Defined.

Theorem ne_cons_correct {A} : forall xs (x : A),
    embed (ne_cons x xs) = (x :: xs)%list.
Proof. induction xs; simpl; [|rewrite IHxs]; reflexivity. Qed.

Theorem ne_snoc_correct {A} : forall xs (x : A),
    embed (ne_snoc x xs) = (xs ++ [x])%list.
Proof. induction xs; intros; simpl; [|rewrite <- IHxs]; reflexivity. Qed.

Definition head {A} (xs : list A) : A :=
  match xs with
  | [x] => x
  | x :: _ => x
  end.

Definition tail {A} (xs : list A) : List.list A :=
  match xs with
  | [_] => List.nil
  | _ :: tl => embed tl
  end.

Fixpoint last {A} (xs : list A) : A :=
  match xs with
  | [x] => x
  | _ :: tl => last tl
  end.

Fixpoint init {A} (xs : list A) : List.list A :=
  match xs with
  | [_] => List.nil
  | hd :: tl => hd :: init tl
  end.

Theorem head_cons {A} : forall (hd : A) tl,
    head (hd :: tl) = hd.
Proof. reflexivity. Qed.

Theorem tail_cons {A} : forall (hd : A) tl,
    tail (hd :: tl) = embed tl.
Proof. reflexivity. Qed.

Theorem head_tail_id {A} : forall xs : list A,
    ne_cons (head xs) (tail xs) = xs.
Proof.
  induction xs; [reflexivity|].
  cbn. rewrite <- IHxs.
  rewrite ne_cons_correct. reflexivity.
Qed.

Theorem head_ne_cons {A} : forall (hd : A) tl,
    head (ne_cons hd tl) = hd.
Proof. destruct tl; reflexivity. Qed.

Theorem tail_ne_cons {A} : forall (hd : A) tl,
    tail (ne_cons hd tl) = tl.
Proof. destruct tl; [reflexivity|apply ne_cons_correct]. Qed.

Theorem last_snoc {A} : forall (lt : A) it,
    last (snoc lt it) = lt.
Proof. induction it; auto. Qed.

Theorem init_snoc {A} : forall (lt : A) it,
    init (snoc lt it) = embed it.
Proof. induction it; cbn; [|rewrite IHit]; easy. Qed.

Theorem last_ne_snoc {A} : forall (lt : A) it,
    last (ne_snoc lt it) = lt.
Proof. induction it; cbn; [|rewrite IHit]; easy. Qed.

Theorem init_ne_snoc {A} : forall (lt : A) it,
    init (ne_snoc lt it) = it.
Proof. induction it; cbn; [|rewrite IHit]; easy. Qed.

Theorem last_init_id {A} : forall xs : list A,
    ne_snoc (last xs) (init xs) = xs.
Proof.
  induction xs; [reflexivity|].
  cbn. rewrite IHxs. reflexivity.
Qed.

Fixpoint length {A} (xs : list A) : nat :=
  match xs with
  | [_] => 1
  | _ :: tl => S (length tl)
  end.

Theorem length_gt_zero {A} : forall xs : list A,
    length xs > 0.
Proof. induction xs; cbn; omega. Qed.

Theorem length_correct {A} : forall xs : list A,
    length xs = List.length (embed xs).
Proof. induction xs; cbn; auto. Qed.

Fixpoint map {A B} (f : A -> B) (xs : list A) : list B :=
  match xs with
  | [x] => [f x]
  | hd :: tl => f hd :: map f tl
  end.

Theorem map_correct {A B} : forall (f : A -> B) xs,
    embed (map f xs) = List.map f (embed xs).
Proof. induction xs; cbn; [|rewrite IHxs]; easy. Qed.
