Require Import List String.
Import ListNotations.
Require Import Coq.Numbers.DecimalString.
Local Open Scope string_scope.


Record Field := {
  field_name : option string;
  field_type : Set
}.

Record Constructor := {
  con_name : string;
  fields : list Field
}.

Record Shape := {
  type_name : string;
  constructors : list Constructor
}.

Inductive empty : Set :=.

Fixpoint Product (ts : list Set) : Set :=
  match ts with
  | [] => unit
  | x :: xs => x * Product xs
  end.

Fixpoint Sum (ts : list Set) : Set :=
  match ts with
  | [] => empty
  | x :: xs => sum x (Sum xs)
  end.

Definition SOP tts := Sum (map Product tts).
Definition to_sop (s : list Constructor) := map (fun x => map field_type (fields x)) s.

Definition Rep_F xs := Product (map field_type xs).
Definition Rep_C xs := Sum (map (fun x => Rep_F (fields x)) xs).
Definition Rep (s : Shape) : Set := Rep_C s.(constructors).

Example rep_test1 :
  Rep (Build_Shape "test"
    [ Build_Constructor "C1" []
    ; Build_Constructor "C2" [Build_Field (Some "F1") nat]
    ; Build_Constructor "C3" [Build_Field None nat; Build_Field None bool]]) =
  (unit +
   (nat * unit +
    (nat * (bool * unit) +
     empty)))%type
  := eq_refl.

Class Show (A : Set) := {
  show : A -> string
}.

Class Generic (A : Set) := {
  shape : Shape;
  to : A -> Rep shape
}.

Instance Generic_empty : Generic empty := {
  shape := Build_Shape "empty" [];
  to := empty_rec _
}.

Instance Generic_unit : Generic unit := {
  shape := Build_Shape "unit" [Build_Constructor "tt" []];
  to := fun _ => inl tt
}.

Arguments shape A [_].

Instance Show_empty : Show empty := { show := empty_rec _ }.
Instance Show_unit : Show unit := { show := fun _ => "tt" }.

Class Both P Q := { both1 : P; both2: Q }.
Instance Both_PQ {P Q} {p : P} {q : Q} : Both P Q := {
  both1 := p; both2 := q
}.

Class Always := {}.
Instance Always_instance : Always := {}.

Fixpoint All {A} (P : A -> Set) (xs : list A) : Set :=
  match xs with
  | [] => Always
  | x :: xs' => Both (P x) (All P xs')
  end.

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).
Notation "f ... g" := (compose f g) (at level 90).

Fixpoint shows_fields (ts : list Field) :
    forall {_ : All (fun x => Show (field_type x)) ts},
    Product (map field_type ts) -> list (option string * string) :=
  match ts with
  | [] => fun _ _ => []
  | Build_Field name _ :: ts => fun allshow v =>
    let (x, xs) := v in
    let (show_t, show_ts) := allshow in
    (name, show x) :: @shows_fields ts show_ts xs
  end.

Fixpoint elim_fields
    (P : Field -> Set)
    R
    (f : forall field, P field -> field_type field -> R)
    (ts : list Field) :
    All P ts -> Rep_F ts -> list R :=
  match ts with
  | [] => fun _ _ => []
  | field :: ts => fun all_p v =>
    let (x, xs) := v in
    let (P_t, P_ts) := all_p in
    f field P_t x :: @elim_fields P R f ts P_ts xs
  end.

Definition shows_fields2 :=
  elim_fields
    (fun x => Show (field_type x))
    (option string * string)
    (fun field Show_x x => (field_name field, @show _ Show_x x)).

Definition RepC_nil_elim {A} : Rep_C [] -> A.
compute. apply empty_rect. Defined.

Fixpoint elim_sum
    (P : Constructor -> Set)
    R
    (f : forall c, P c -> Rep_F (fields c) -> R)
    (ts : list Constructor) :
    All P ts -> Rep_C ts -> R :=
  match ts with
  | [] => fun _ => RepC_nil_elim
  | con :: ts => fun all_p v =>
    let (P_t, P_ts) := all_p in
    match v with
    | inl x => f con P_t x
    | inr xs => @elim_sum P R f ts P_ts xs
    end
  end.

Fixpoint intercalate (sep : string) (l : list string) : string :=
  match l with
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ intercalate sep xs
  end.

Definition All_C P := All (fun c => All (fun x => P (field_type x)) c.(fields)).

Fixpoint genericShow (cs : list Constructor)
  {allShow : All_C Show cs}
  (x : Rep_C cs) : string :=
  elim_sum _ _
    (fun c Pc flds =>
      c.(con_name) ++ " (" ++
      intercalate ", "
       (map (@snd (option string) string)
         (shows_fields2
          c.(fields) Pc flds)) ++ ")")
    cs allShow x.

Notation solve_constraint := (ltac:(compute; typeclasses eauto)) (only parsing).

Definition test_shape :=
  Build_Shape "test"
    [ Build_Constructor "C1" []
    ; Build_Constructor "C2" [Build_Field (Some "F1") nat]
    ; Build_Constructor "C3" [Build_Field None nat; Build_Field None bool]].

Instance Show_bool : Show bool := {
  show x :=
    match x with
    | true => "true"
    | false => "false"
    end
}.

Definition string_of_nat x := NilZero.string_of_int (Nat.to_int x).

Instance Show_nat : Show nat := {
  show := string_of_nat
}.

Example test_genericShow :
  @genericShow test_shape.(constructors) solve_constraint
    (inr (inr (inl (179, (true, tt)))))
    = "C3 (179, true)"
    := eq_refl.
