Require Import MSets.
Require Import List.
Import ListNotations.
Local Open Scope list_scope.

Module MaximalCliques (E : DecidableType) (S : MSetInterface.WSetsOn(E)).

Definition fst {A B} (a : A * B) := let (x, _) := a in x.
Definition snd {A B} (a : A * B) := let (_, x) := a in x.

Fixpoint BronKerbosch1_func (depth : nat) (N : S.elt -> S.t) (R P X : S.t): list S.t :=
  match depth with
  | 0 => []
  | S depth' =>
    if S.is_empty P && S.is_empty X then
      [R]
    else
      snd
      (S.fold
        (fun v (a : S.t * S.t * list S.t) =>
           ( S.remove v (fst (fst a))
           , S.add v (snd (fst a))
           , BronKerbosch1_func depth' N (S.add v R) (S.inter P (N v)) (S.inter X (N v)) ++ snd a
           )
        )
        P
        (P, X, []))
  end.

Definition BronKerbosch1 N V := BronKerbosch1_func (S.cardinal V) N S.empty V S.empty.

Definition IsClique (N : S.elt -> S.t) (X : S.t) : Prop :=
  forall x y, S.In x X -> S.In y X ->
  S.In y (N x).

Definition IsMaximalClique N V X : Prop :=
  IsClique N X /\ (forall v, S.In v V -> ~S.In v X -> ~IsClique N (S.add v X)).

Lemma Forall_app : forall {A} (P : A -> Prop) xs ys, Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Admitted.

Lemma fold_left_spec :
  forall A B (P : B -> Type) (f : B -> A -> B) xs,
  (forall x acc, P acc -> P (f acc x)) ->
  forall acc,
  P acc ->
  P (fold_left f xs acc).
Proof.
  intros A B P f xs HP1.
  induction xs.
  - auto.
  - intros acc Hacc.
    apply IHxs. apply HP1.
    apply Hacc.
Qed.

Lemma fold_spec_better :
  forall {A} (P : A -> Type) f initial set,
  (forall x acc, P acc -> P (f x acc)) ->
  P initial ->
  P (S.fold f set initial).
Proof.
  intros.
  rewrite S.fold_spec.
  unfold flip.
  apply fold_left_spec; auto.
Qed.

Lemma IsClique_add :
  forall N R x,
  IsClique N R -> IsClique N (S.add x R).
Proof.
  unfold IsClique in *.
  intros.
  (* This probably needs some more assumptions. *)
Admitted.

Theorem BK_IsClique : forall n N R P X,
  IsClique N R ->
  Forall (IsClique N) (BronKerbosch1_func n N R P X).
Proof.
  intros n N.
  induction n; simpl; auto.
  intros R P X H_IsCliqueR.
  destruct (S.is_empty P && S.is_empty X).

  (* Forall (IsClique N) [R] *)
  auto.

  apply fold_spec_better.
  
  (* step *)
  - intros. unfold snd.
    apply Forall_app.
    * apply IHn.
      apply IsClique_add.
      auto.
    * apply H.
  (* initial *)
  - constructor.
Qed.

End MaximalCliques.

Module OrdNat : DecidableType.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition eq_equiv : Equivalence eq := _.
  Definition eq_dec : forall (x y : nat), {x = y} + {x <> y}.
  decide equality. Defined.
End OrdNat.

Module NatSet := MSetWeakList.Make OrdNat.
Module MC := MaximalCliques OrdNat NatSet.