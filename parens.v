Require Import List PeanoNat ZArith.

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

Scheme Equality for char.

Definition eq_char := char_eq_dec.

Definition count_char_1 c x := if eq_char x c then 1 else 0.

Fixpoint count_char (c : char) (l : list char) : nat :=
  match l with
  | nil => 0
  | x :: xs => count_char_1 c x + count_char c xs
  end%list.

Definition count_close := count_char Close.
Definition count_open := count_char Open.

Lemma count_char_append : forall c xs ys, count_char c (xs ++ ys) = count_char c xs + count_char c ys.
Proof.
  intros c xs ys.
  induction xs.
  - auto.
  - simpl. rewrite IHxs. omega.
Qed.

Lemma encode_count_all : forall P xs,
  all (fun p : parens => P (encode p)) xs ->
  P nil ->
  (forall xs ys, P xs -> P ys -> P (xs ++ ys)) ->
  P (concat (map encode xs)).
Proof.
  intros P xs Hall Hnil Happend.
  induction Hall.
  - auto.
  - apply Happend; auto.
Qed.

Definition Balanced xs := count_char Open xs = count_char Close xs.

Lemma balanced_append : forall xs ys, Balanced xs -> Balanced ys -> Balanced (xs ++ ys).
Proof.
  unfold Balanced.
  intros.
  repeat rewrite count_char_append.
  auto.
Qed.

Theorem encode_count_eq : forall p, Balanced (encode p).
Proof.
  unfold Balanced.
  intros.
  apply parens_ind_2 with (p:=p).
  intros.
  destruct H.
  - auto.
  - simpl.
    repeat rewrite count_char_append.
    rewrite H. simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.add_1_r.
    f_equal.
    f_equal.
    apply encode_count_all. apply H0. reflexivity. apply balanced_append.
Qed.

Require Extraction.
Recursive Extraction encode.