Require Import List.

Inductive parens := Parens : list parens -> parens.

Inductive p_list (A : Type) (P : A -> Prop) :=
  | Nil : p_list A P
  | Cons : forall (x : A), P x -> p_list A P -> p_list A P.

Inductive char := Open : char | Close : char.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | x :: xs => x ++ concat xs
  end%list.

Fixpoint encode (p : parens) : list char :=

  match p with
  | Parens ps => Open :: concat (map encode ps) ++ (Close :: nil)
  end%list.

Eval simpl in encode (Parens (Parens nil :: Parens nil :: nil))%list.

Inductive all {A} (P : A -> Prop) : list A -> Prop :=
  | all_nil : all P nil
  | all_cons : forall (x : A) (xs : list A), P x -> all P xs -> all P (x :: xs).

Parameter Hole : Type. Parameter hole : Hole.

Fixpoint parens_ind_2 (P : parens -> Prop)
  (Hparens : forall l, all P l -> P (Parens l))
  p : P p :=

  let fix mk_all l : all P l :=
        match l with
        | nil => all_nil P
        | x :: xs => all_cons P x xs (parens_ind_2 P Hparens x) (mk_all xs)
        end%list

  in

  match p with
  | Parens ps => Hparens ps (mk_all ps)
  end.

(*******************************************************)


Fixpoint count_open (l : list char) : nat :=
  match l with
  | nil => 0
  | Open :: xs => S (count_open xs)
  | Close :: xs => count_open xs
  end%list.


Fixpoint count_close (l : list char) : nat :=
  match l with
  | nil => 0
  | Open :: xs => count_close xs
  | Close :: xs => S (count_close xs)
  end%list.

Lemma count_open_append

Theorem encode_count_eq : forall p, count_open (encode p) = count_close (encode p).
Proof.
  intros.
  apply parens_ind_2 with (p:=p).
  intros.
  induction H.
  - reflexivity.
  - simpl.