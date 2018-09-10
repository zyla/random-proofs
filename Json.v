Require Import List String.
Import ListNotations.

Inductive value :=
  | Number : nat -> value
  | String : string -> value
  | Array : list value -> value
  | Object : list (string * value) -> value
  | Null : value
  | Undefined : value
  .

Class Serializable A := {
  to_json : A -> value;
  from_json : value -> option A;
  roundtrip : forall (x : A), from_json (to_json x) = Some x
}.

Notation S := Serializable.

Instance Serializable_unit : S unit := {
  to_json _ := Object [];
  from_json _ := Some tt;
}.
intro x. case x. exact eq_refl.
Defined.

Instance Serializable_prod {A B} {_ : S A} {_ : S B} : S (A * B) := {
  to_json p := let (x, y) := p in Array [ to_json x; to_json y ];
  from_json v :=
    match v with
    | Array [ x; y ] =>
      match from_json x, from_json y with
      | Some x1, Some y1 => Some (x1, y1)
      | _, _ => None
      end
    | _ => None
    end
}.
(* roundtrip *)
intro p.
destruct p.
rewrite roundtrip.
rewrite roundtrip.
reflexivity.
Defined.

Instance S_nat : S nat := {
  to_json := Number;
  from_json v :=
    match v with
    | Number x => Some x
    | _ => None
    end
}.
intro. auto.
Defined.

Eval compute in to_json (1, tt, 5, 6).

Record foo := mk_foo { bar : nat; baz : nat }.

Definition foo1 : foo := {| bar := 1; baz := 1 |}.

Record Heap := {
  m : Set -> Set; (* monad for heap operations *)
  ref : Set -> Set;
  read_ref : forall {a}, ref a -> m a
  ...
}
Axiom unsafePerformIO : forall {a}, (forall {h : Heap}, { x : m h a | ... }) -> a.


Module Type Heap_Sig.
  Parameter m : Set -> Set.
  Parameter ref : Set -> Set.
  Parameter read_ref : forall {a}, ref a -> m a.
  (* ... *)
End Heap_Sig.

Module App(Heap : Heap_Sig).
  Inductive dynamic := ... (Heap.ref ...)
End App.

Module PureHeap.