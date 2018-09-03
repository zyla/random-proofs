Require Import List.

Inductive emptiness := NonEmpty : emptiness | MaybeEmpty : emptiness.

Inductive char : Set := mk_char : nat -> char.
Definition string := list char.

Definition parser_guts (a : Set) := string -> list (a * nat).

Definition non_empty {a} (p : parser_guts a) : Prop :=
  p nil = nil.

Definition satisfies_emptiness e {a} (p : parser_guts a) :=
  match e with
  | MaybeEmpty => True
  | NonEmpty => non_empty p
  end.

Definition parser (e : emptiness) (a : Set) : Set :=
  { p : parser_guts a | satisfies_emptiness e p }.

SearchAbout sig.

Definition returnP {a : Set} (x : a) : parser MaybeEmpty a.
refine (exist _ (fun _ => cons (x, 0) nil) _).
simpl; auto.
Defined.

Definition append_emptiness e1 e2 :=
  match e1, e2 with
  | MaybeEmpty, MaybeEmpty => MaybeEmpty
  | _, _ => NonEmpty
  end.

Definition bind_list {a b} (xs : list a) (k : a -> list b) : list b := concat (map k xs).

Definition bindP_guts {a b : Set} (p : parser_guts a) (k : a -> parser_guts b) : parser_guts b :=
  fun input =>
    bind_list (p input) (fun result =>
      let (x, n) := result in
      k x (skipn n input)).

Theorem bind_nonempty_nonempty : forall {a b} (p : parser_guts a) (k : a -> parser_guts b),
  non_empty p ->
  non_empty (bindP_guts p k).
Proof.
  unfold non_empty in *. intros a b p k Hp.
  unfold bindP_guts. rewrite Hp.
  unfold bind_list. unfold map. reflexivity.
Qed.

Lemma skipn_nil_nil : forall {A} n, skipn n (@nil A) = (@nil A).
Proof.
  intros.
  destruct n; auto.
Qed.

Lemma bind_nil_nil : forall {a b} (l : list a) (k : a -> list b), (forall x, k x = nil) -> bind_list l k = nil.
Proof.
  intros.
  unfold bind_list.
  induction l.
  - auto.
  - simpl. rewrite H. simpl. assumption.
Qed.

Theorem bind_nonempty_nonempty_2 : forall {a b} (p : parser_guts a) (k : a -> parser_guts b),
  (forall x, non_empty (k x)) ->
  non_empty (bindP_guts p k).
Proof.
  unfold non_empty in *. intros a b p k Hk.
  unfold bindP_guts.
  destruct (p nil).
  - auto.
  - apply bind_nil_nil.
    intros. destruct x. rewrite skipn_nil_nil. apply Hk.
Qed.

Definition bindP {a b : Set} {e1 e2} (p : parser e1 a) (k : a -> parser e2 b) : parser (append_emptiness e1 e2) b.
destruct p as [p_guts Hp].
exists (bindP_guts p_guts (fun x => proj1_sig (k x))).

unfold append_emptiness in *. unfold satisfies_emptiness in *.
destruct e1; destruct e2; try auto.

- apply bind_nonempty_nonempty. assumption.
- apply bind_nonempty_nonempty. assumption.
- apply bind_nonempty_nonempty_2.
  intros.
  destruct (k x). simpl.
  apply s.
Qed.

Definition type_of {a} (x : a) := a.

Definition satisfy (p : char -> bool) : parser NonEmpty char.
exists (fun input =>
  match input with
  | nil => nil
  | x :: xs =>
     if p x
       then (x, 1) :: nil
       else nil
  end).

reflexivity.
Defined.

Definition non_empty_str : Set := char * string.

Scheme Equality for char.

Definition mapP {a b : Set} {e} (f : a -> b) (p : parser e a) : parser e b.
destruct p as [p_guts Hp].
exists (fun input => map (fun result => match result with (x, n) => (f x, n) end) (p_guts input)).
unfold satisfies_emptiness in *.
destruct e; auto.
unfold non_empty in *.
rewrite Hp.
reflexivity.
Defined.

Fixpoint stringP' c s : parser NonEmpty unit :=
  match s with
  | c' :: s'' =>
    bindP
      (satisfy (char_beq c))
      (fun _ => stringP' c' s'')
  | nil =>
    mapP (fun _ => tt) (satisfy (char_beq c))
  end.

Definition stringP (s : non_empty_str) : parser NonEmpty unit :=
  let (c, s') := s in stringP' c s'.

Definition alt_emptiness e1 e2 :=
  match e1, e2 with
  | NonEmpty, NonEmpty => NonEmpty
  | _, _ => MaybeEmpty
  end.

Definition fail {a} : parser NonEmpty a.
exists (fun _ => nil). reflexivity.
Defined.

Definition altP {e1 e2 a} (p1 : parser e1 a) (p2 : parser e2 a) : parser (alt_emptiness e1 e2) a.
Admitted.

Fixpoint manyP {a} (p : parser NonEmpty a) : parser MaybeEmpty (list a) :=
 altP
   (bindP p (fun x =>
     bindP (manyP p) (fun xs =>
     returnP (cons x xs))))
   (returnP nil).