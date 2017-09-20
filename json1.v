Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import List.

Open Scope string_scope.

Inductive json : Set :=
  | Bool : bool -> json
  (* TODO: numbers *)
  | Null : json
(*  | J_String : string -> json *)
  | Array : list json -> json
(*  | Object : list (string * json) -> json *)
  .

Fixpoint intercalate (sep : string) (xs : list string) : string :=
  match xs with
  | nil => ""
  | x :: nil => x
  | x :: xs => x ++ sep ++ intercalate sep xs
  end%string.

Definition escape_string str := ("""" ++ str ++ """").

Fixpoint encode (v : json) : string :=
  match v with
  | Bool true => "true"
  | Bool false => "false"
  | Null => "null"
(*  | J_String str => escape_string str *)
  | Array items => "[" ++ intercalate "," (map encode items) ++ "]"
(*  | Object kvs => "{" ++ intercalate ","
        ((fix encode_kvs (kvs : list (string * json)) :=
            match kvs with
            | nil => nil
            | (k, v) :: kvs => (escape_string k ++ ":" ++ encode v) :: encode_kvs kvs
            end) kvs) ++ "}" *)
  end.

Parameter hole : Type.

Section Parser.

  Notation "[]" := EmptyString.
  Notation "x :: xs" := (String x xs) (at level 60, right associativity).

  Definition is_space (c : ascii) : bool :=
    match c with
    | " " => true
    | "009" => true
    | "010" => true
    | _ => false
    end%char.

  Inductive Stack :=
    | S_Top : Stack
    | S_Array : list json -> Stack -> Stack.

  Fixpoint parse_json (s : string) (stack : Stack) : option json :=
    let fix parse_end_no_ws obj stack str {struct str} :=
          match stack, str with
          | S_Array objs next, "," :: rest =>
              parse_json rest (S_Array (obj :: objs) next)
          | S_Array objs next, "]" :: rest =>
              parse_end_no_ws (Array (rev (obj :: objs))) next rest
          | S_Top, "" => Some obj
          | _, _ => None
          end
    in
    let fix parse_end obj str :=
          match str with
          | [] => parse_end_no_ws obj stack str
          | c :: rest =>
              if is_space c
                then parse_end obj rest
                else parse_end_no_ws obj stack (c :: rest)
          end
    in
    match s with
    | [] => None
    | c :: rest =>
        if is_space c then parse_json rest stack else 
        match s with
        | "t" :: "r" :: "u" :: "e" :: rest => parse_end (Bool true) rest
        | "t" :: rest => parse_end (Bool true) rest
        | "f" :: "a" :: "l" :: "s" :: "e" :: rest => parse_end (Bool false) rest
        | "n" :: "u" :: "l" :: "l" :: rest => parse_end Null rest
        | "[" :: rest => parse_json rest (S_Array nil stack)
        | _ => None
        end
    end.

  Fixpoint parse_json_no_ws (s : string) (stack : Stack) : option json :=
    let fix parse_end obj stack str {struct str} :=
          match stack, str with
          | S_Array objs next, "," :: rest =>
              parse_json_no_ws rest (S_Array (obj :: objs) next)
          | S_Array objs next, "]" :: rest =>
              parse_end (Array (rev (obj :: objs))) next rest
          | S_Top, "" => Some obj
          | _, _ => None
          end
    in
    match stack, s with
    | _, "t" :: "r" :: "u" :: "e" :: rest =>
        parse_end (Bool true) stack rest
    | _, "f" :: "a" :: "l" :: "s" :: "e" :: rest =>
        parse_end (Bool false) stack rest
    | _, "n" :: "u" :: "l" :: "l" :: rest =>
        parse_end Null stack rest
    | _, "[" :: rest =>
        parse_json_no_ws rest (S_Array nil stack)
    | S_Array objs next, "]" :: rest =>
        parse_end (Array (rev objs)) next rest
    | _, _ => None
    end.

  Eval simpl in (option_map encode (parse_json_no_ws "[true,[],[false],[false,true]]" S_Top)).

  Eval simpl in (parse_json " [ true , false , [ true ]]" S_Top).

End Parser.

Inductive All {A} (P : A -> Prop) : list A -> Prop :=
  | All_nil : All P nil
  | All_cons : forall x xs, P x -> All P xs -> All P (x :: xs).

Fixpoint json_ind_2 (P : json -> Prop) x
    (Hbool : forall b, P (Bool b))
    (Hnull : P Null)
    (Harray : forall l, All P l -> P (Array l))
    : P x :=

  match x as x return P x with
  | Bool b => Hbool b
  | Null => Hnull
  | Array l => Harray l
      ((fix list_proof l : All P l := 
        match l as l return All P l with
        | nil => All_nil P
        | x :: xs => All_cons P x xs (json_ind_2 P x Hbool Hnull Harray) (list_proof xs)
        end
      ) l)
  end.


Theorem json_roundtrip : forall v, parse_json_no_ws (encode v) S_Top = Some v.
Proof.
  intro v.
  apply json_ind_2 with (x:=v).
  - intro b.
    destruct b; reflexivity.
  - reflexivity.
  - intros l Hall.
    induction Hall.
    + reflexivity.
    + unfold encode. fold @encode.
      destruct xs.
      * simpl.
        unfold parse_json_no_ws. fold @parse_json_no_ws.
        admit.
      * assert (intercalate "," (map encode (x :: j :: xs)) = encode x ++ "," ++ intercalate "," (map encode (j :: xs))) as H1.
        reflexivity.
        rewrite H1.
      unfold parse_json_no_ws.

(*
Inductive Rep : json -> string -> Prop :=
  | R_True : Rep (Bool true) "true"
  | R_False : Rep (Bool false) "false"
  | R_Null : Rep Null "null"
  | R_Array : forall items str,
      RepItems items str -> Rep (Array items) ("[" ++ str ++ "]")

with RepItems : list json -> string -> Prop :=
  | RI_Empty : RepItems [] ""
  | RI_One : forall item str, Rep item str -> RepItems item str
  | RI_Many : forall item items str strs, Rep item str, Rep
*)
