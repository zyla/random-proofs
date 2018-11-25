(* Identifiers *)

Inductive Ident := MkIdent : nat -> Ident.

Scheme Equality for Ident.

Definition X : Ident := MkIdent 0.
Definition Y : Ident := MkIdent 1.

(* Expressions *)

Inductive Expr :=
  | Const : nat -> Expr
  | Var : Ident -> Expr
  | Add : Expr -> Expr -> Expr.

Scheme Equality for Expr.

(*

(17 + (X + 6)) + Y

    +
   / \
  +   Y
 / \
17  +
   / \
  X   6

*)


Eval simpl in

  Add
    (Add
      (Const 17)
      (Add
        (Var X)
        (Const 6))
    )
    (Var Y).


























(* Environment is a mapping from identifiers to values.
   We ignore partiality for now (environment returns arbitrary
    value for undefined variables)

   X := 3
   Y := 17

   X := 3
 *)

Definition Env := Ident -> nat.

Definition empty_env : Env := fun _ => 0.
























(* Denotational semantics of expressions *)

Fixpoint eval (env : Env) (expr : Expr) : nat :=
  match expr with
  | Const x => x
  | Var v => env v

  | Add x y => eval env x + eval env y
  end.


Example eval_ex1 : eval empty_env (Add (Const 2) (Const 3)) = 5
  := eq_refl.

Example eval_ex2 : eval
  (fun x => if Ident_beq x X then 7 else 0) (* X := 7 *)
  (Add (Const 1) (Var X)) = 8
  := eq_refl.



























(* Property 1. forall e, there are no subexpressions
  of the form (0 + x) in remove_left_zero e. *)

(* Property 2. forall env e, eval env (remove_left_zero e) = eval env e *)







Check nat_ind.
Check Expr_ind.


(* A simple optimization pass: (0 + e) -> e *)

Fixpoint remove_left_zero (expr : Expr) : Expr :=
  match expr with
  | Add (Const 0) e => remove_left_zero e
  | Add x y => Add (remove_left_zero x) (remove_left_zero y)

  | Const _ => expr
  | Var _ => expr
  end.


Example remove_left_zero_ex1 :
  remove_left_zero (Add (Var Y) (Add (Const 0) (Var X))) (* Y + (0 + X) *)
   = Add (Var Y) (Var X)
   := eq_refl.


Example remove_left_zero_ex2 :
  remove_left_zero (Add (Var Y) (Add (Var X) (Const 0))) (* Y + (X + 0) *)
   = Add (Var Y) (Add (Var X) (Const 0))
   := eq_refl.

(* Correctness theorem: preservation of denotational semantics *)

Definition PreservesSemantics (f : Expr -> Expr) :=
  forall env expr, eval env (f expr) = eval env expr.


Theorem remove_left_zero_correct : PreservesSemantics remove_left_zero.
Proof.
  unfold PreservesSemantics. intros.
  
  induction expr.
  - unfold remove_left_zero. reflexivity.
  - unfold remove_left_zero. reflexivity.
  - simpl.
    destruct expr1 eqn:Hexpr1.
    * destruct n.
      
      simpl. apply IHexpr2.
      
      simpl in IHexpr1.
      simpl. rewrite IHexpr2. reflexivity.
      
    * simpl. rewrite IHexpr2. reflexivity.
    * simpl. auto. (* simpl in *. rewrite IHexpr1. rewrite IHexpr2. reflexivity. *)
Qed.

Print remove_left_zero_correct.


Check eq_ind_r.

(*
\x ->
  case y of
    Just z -> ...
    Nothing -> ...

case y of
  Just z -> \x -> ...
  Nothing -> \x -> ...
  
       : forall (A : Type) (x y : A),
       y = x ->
       (P : A -> Prop),
       P x -> P y
*)












Theorem remove_left_zero_correct_2 : PreservesSemantics remove_left_zero.
Proof.
  unfold PreservesSemantics.
  intros.

  induction expr.
  - (* Const *) auto.
  - (* Var *) auto.
  - (* The interesting case - Add *)
    destruct expr1; simpl; try rewrite IHexpr1; try rewrite IHexpr2; auto.
    * (* We're left with (Add (Const n) expr2)) *)
      destruct n; simpl; auto.
Qed.







(* Property 1. forall e, there are no subexpressions
  of the form (0 + x) in remove_left_zero e. *)

Fixpoint has_subexpr (p : Expr -> bool) (expr : Expr) : bool :=
  p expr ||
  match expr with
  | Const _ => false
  | Var _ => false
  | Add x y => has_subexpr p x || has_subexpr p y
  end.

Definition is_zero_plus expr :=
  match expr with
  | Add (Const 0) _ => true
  | _ => false
  end.

Theorem remove_left_zero_removes_zeros : forall e,
  has_subexpr is_zero_plus (remove_left_zero e) = false.
Proof.
  intros.
  induction e; auto.

  (* Add e1 e2 *)
  simpl.
  destruct e1; auto.
  - destruct n; auto.
Admitted.




(* Utilities *)

Fixpoint bottom_up (f : Expr -> Expr) (e : Expr) : Expr :=
  f (match e with
     | Const n => e
     | Var v => e
     | Add e1 e2 => Add (bottom_up f e1) (bottom_up f e2)
     end).

Theorem bottom_up_preserves_semantics : forall f,
  PreservesSemantics f ->
  PreservesSemantics (bottom_up f).
Proof.
  unfold PreservesSemantics. intros.
  induction expr; try apply H; auto.
  simpl. rewrite H. simpl. auto.
Qed.

Definition remove_left_zero_2 := bottom_up
  (fun x =>
    match x with
    | Add (Const 0) e => e
    | _ => x
    end).

Theorem remove_left_zero_2_correct : PreservesSemantics remove_left_zero_2.
Proof.
  apply bottom_up_preserves_semantics.
  unfold PreservesSemantics. intros.
  destruct expr; auto.
  destruct expr1; auto.
  destruct n; auto.
Qed.

Theorem remove_left_zero_idempotent : forall e,
  remove_left_zero (remove_left_zero e) = remove_left_zero e.
Proof.
  intros.
  induction e; auto.
  induction e1.
  - destruct n; auto. simpl. rewrite IHe2. auto.
  - simpl. rewrite IHe2. auto.
  - (* stuck *)
Admitted.

Inductive ExprF a :=
  | ConstF : nat -> ExprF a
  | VarF : Ident -> ExprF a
  | AddF : a -> a -> ExprF a.

Arguments ConstF [_].
Arguments VarF [_].
Arguments AddF [_].

Definition Expr2 := forall r, (ExprF r -> r) -> r.

Definition myexpr : Expr2 :=
  fun _ f =>
    f (AddF (f (ConstF 0)) (f (VarF X))).

Print myexpr.


Require Import Setoid.




Definition Idempotent {A} (f : A -> A) := forall x, f (f x) = f x.

Definition Nonexpansive f :=
  (forall n, exists n', f (Const n) = Const n') /\
  (forall v, exists v', f (Var v) = Var v').

Theorem bottom_up_idempotent : forall f, Idempotent f -> Nonexpansive f -> Idempotent (bottom_up f).
Proof.
  unfold Idempotent.
  intros.
  destruct H0.
  induction x.
  - simpl. destruct (H0 n). rewrite H2 at 1. simpl.
    rewrite <- H2.
    apply H.
  - simpl. destruct (H1 i). rewrite H2. simpl. rewrite <- H2. auto.
  - simpl.
    destruct (f (Add (bottom_up f x1) (bottom_up f x2))) eqn:Hsomeshit.
    * admit.
    * admit.
    * simpl. rewrite <- Hsomeshit. f_equal. f_equal.
Admitted.

Require Import FunInd.

Functional Scheme remove_left_zero_ind := Induction for remove_left_zero Sort Prop.

Theorem remove_left_zero_correct_3 : PreservesSemantics remove_left_zero.
Proof.
  unfold PreservesSemantics. intros.
  functional induction remove_left_zero expr; intros; subst; simpl; auto.
Qed.

