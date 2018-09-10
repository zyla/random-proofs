Require List.
Import List.ListNotations.
Local Open Scope list_scope.
Require Import Program.

Definition Shape := list (list Type).

Inductive fin : nat -> Type :=
  | FZ : forall {n}, fin (S n)
  | FS : forall {n}, fin n -> fin (S n).

Fixpoint nat_to_fin (m : nat) (n : nat) : option (fin m) :=
  match m, n with
  | S m', 0 => Some FZ
  | S m', S n' => option_map FS (nat_to_fin m' n')
  | _, _ => None
  end.

Fixpoint weaken {m} (n : fin m) : fin (S m) :=
  match n with
  | FZ => FZ
  | FS n' => FS (weaken n')
  end.

Inductive hlist : list Type -> Type :=
  | HNil : hlist nil
  | HCons : forall {x xs}, x -> hlist xs -> hlist (x :: xs).

Inductive At {A} : nat -> A -> list A -> Prop :=
  | Here : forall {x xs}, At 0 x (x :: xs)
  | There : forall {x y xs n}, At n x xs -> At (S n) x (y :: xs).

Fixpoint index {A} (i : nat) (l : list A) {struct l} : option A :=
  match l with
  | [] => None
  | x :: xs =>
    match i with
    | 0 => Some x
    | S i' => index i' xs
    end
  end.

Fixpoint indexT (i : nat) (l : list Type) {struct l} : Type :=
  match l with
  | [] => False
  | x :: xs =>
    match i with
    | 0 => x
    | S i' => indexT i' xs
    end
  end.

Inductive union (xs : list Type) : Type :=
  u_intro : forall (i : nat) {x : Type}, indexT i xs -> union xs.

Definition Rep (s : Shape) := union (List.map hlist s).

Class Generic (a : Type) := {
  shape : Shape;
  construct : Rep shape -> a;
  destruct : a -> Rep shape;
  construct_destruct : forall (x : a), construct (destruct x) = x;
  destruct_construct : forall (x : Rep shape), destruct (construct x) = x
}.
Instance Generic_unit : Generic unit := {
  shape := [[]];
  construct _ := tt;
  destruct _ := u_intro [hlist []] 0 HNil
}.
exact (hlist []).
intro x. destruct x. auto.
intro x. destruct x.
destruct i; simpl in i0.
dependent destruction i0. simpl. reflexivity.
simpl in e. inversion e. subst x. pattern e.
dependent destruction e.
dependent destruction x0. reflexivity.
simpl in e. inversion e.
Defined.

Instance Generic_sum {A B} {_ : Generic A} {_ : Generic B} : Generic (A + B) := {
  shape := [[A]; [B]];
  destruct x :=
    match x with
    | inl a => u_intro _ 0 _ (HCons a HNil)
    | inr b => u_intro _ 1 _ (HCons b HNil)
    end
}.
- intro. destruct X.
  destruct i.
  * simpl in e. inversion e. subst x.
    dependent destruction x0. constructor. assumption.
  * simpl in e. inversion e.
    destruct i; try (inversion e).
    subst x. dependent destruction x0.
    right. assumption.
- reflexivity.
- reflexivity.
- intros x.
  case x; intro; reflexivity.
-intro x.
 dependent inversion x; simpl. 
Admitted.