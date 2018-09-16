Require Import MSets.
Require Import List.
Import ListNotations.
Local Open Scope list_scope.

Module MaximalCliques (E : DecidableType) (S : MSetInterface.WSetsOn(E)).

Fixpoint BronKerbosch1_func (depth : nat) (N : S.elt -> S.t) (R P X : S.t): list S.t :=
  match depth with
  | 0 => []
  | S depth' =>
    if S.is_empty P && S.is_empty X then
      [R]
    else
      (fix loop P X xs :=
        match xs with
        | [] => []
        | v :: xs' =>
           BronKerbosch1_func depth' N (S.add v R) (S.inter P (N v)) (S.inter X (N v)) ++
           loop (S.remove v P) (S.add v X) xs'
        end) P X (S.elements P)
   end.

Definition BronKerbosch1 N V := BronKerbosch1_func (S.cardinal V) N S.empty V S.empty.

Definition IsClique (N : S.elt -> S.t) (X : S.t) : Prop :=
  forall x y, S.In x X -> S.In y X ->
  S.In y (N x).

Definition IsMaximalClique N V X : Prop :=
  IsClique N X /\ (forall v, S.In v V -> ~S.In v X -> ~IsClique N (S.add v X)).

Lemma Forall_app : forall {A} (P : A -> Prop) xs ys, Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
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

  set (xs := S.elements P).
  generalize dependent P.
  generalize dependent X.
  induction xs; auto.
  apply Forall_app.
  - apply IHn. admit.
  - SearchAbout S.In.
Admitted.

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