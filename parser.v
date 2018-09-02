(*
To illustrate some of the problems arising when parsing JSON, we're gonna write a parser for a simpler data type:

value ::= tt | "[" value "," value "," ... "," value "]"

*)

Module Mutual.

Inductive value :=
  | Unit : value
  | Array : values -> value

with values :=
  | nil : values
  | cons : value -> values -> values.

Scheme value_mut_ind := Induction for value Sort Prop
with values_mut_ind := Induction for values Sort Prop.

Require Import String.

Fixpoint encode_value (v : value) : string :=
  match v with
  | Unit => "tt"
  | Array values => "[" ++ encode_values values ++ "]"
  end

with encode_values (vs : values) : string :=
  match vs with
  | nil => ""
  | cons x nil => encode_value x
  | cons x xs => encode_value x ++ "," ++ encode_values xs
  end.

Definition test_encode : encode_value (Array (cons Unit (cons (Array nil) nil))) = "[tt,[]]"%string := eq_refl.

Section Parser.

Notation "x :: xs" := (String x xs) (at level 60, right associativity).

Inductive stack :=
  | Top : stack
  | InArray : values -> stack -> stack.

Fixpoint reverse_acc (acc v : values) : values :=
  match v with
  | nil => acc
  | cons x xs => reverse_acc (cons x acc) xs
  end.

Definition reverse (v : values) : values := reverse_acc nil v.

Fixpoint parse_value (s : string) (st : stack) : option value :=
  match st, s with
  | _, ""%string => None
  | _, "t" :: "t" :: rest => parse_end Unit rest st
  | _, "[" :: rest => parse_value rest (InArray nil st)
  | InArray nil next, "]" :: rest => parse_end (Array nil) rest next
  | _, _ => None
  end
with parse_end obj s st :=
  match st, s with
  | Top, ""%string => Some obj
  | InArray values next, "," :: rest => parse_value rest (InArray (cons obj values) next)
  | InArray values next, "]" :: rest => parse_end (Array (reverse (cons obj values))) rest next
  | _, _ => None
  end.


Definition test_parse : parse_value "[tt,[]]"%string Top = Some (Array (cons Unit (cons (Array nil) nil))) := eq_refl.

Check value_mut_ind.

Lemma append_assoc : forall (a b c : string), ( (a ++ b) ++ c = a ++ (b ++ c) )%string.
Admitted.

Lemma encode_parse_roundtrip_1 : forall v st rest,
  parse_value (encode_value v ++ rest) st = parse_end v rest st.
Proof.
  intro v.
  eapply value_mut_ind with
   (P:=fun v => forall st rest, parse_value (encode_value v ++ rest) st = parse_end v rest st)
   (P0:=fun v => forall st rest, parse_value (encode_values v ++ "]" :: rest) (InArray nil st) = parse_end (Array v) rest st).
  - destruct st.
    + reflexivity.
    + destruct v0; reflexivity.
  - intros vs IHvs.
    simpl in *.
    intros.
    rewrite append_assoc.
    destruct st.
    apply IHvs.
    destruct v0; apply IHvs.
  - destruct st.
    simpl. reflexivity.
    destruct v0; reflexivity.
  - intros.
    destruct st.
    + destruct v1.
      * simpl.
        rewrite H.
        reflexivity.
      * simpl.
        rewrite append_assoc.
        rewrite H.
        rewrite append_assoc.
        destruct v2.
        