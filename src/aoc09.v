Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Export NArith List Number Decimal.

From stdpp Require Import gmap sorting.

Import ListNotations.

Record DIGITS := { unDIGITS : list N }.

Fixpoint decimal_to_digits (d : Decimal.uint) : list N :=
  match d with
  | D0 d => 0 :: decimal_to_digits d
  | D1 d => 1 :: decimal_to_digits d
  | D2 d => 2 :: decimal_to_digits d
  | D3 d => 3 :: decimal_to_digits d
  | D4 d => 4 :: decimal_to_digits d
  | D5 d => 5 :: decimal_to_digits d
  | D6 d => 6 :: decimal_to_digits d
  | D7 d => 7 :: decimal_to_digits d
  | D8 d => 8 :: decimal_to_digits d
  | D9 d => 9 :: decimal_to_digits d
  | Nil => []
  end%N.

Definition decimal_to_DIGITS (d : Number.uint) :=
  match d with
  | UIntDecimal d => Some {| unDIGITS := decimal_to_digits d |}
  | _ => None
  end.

Definition dummy_from_DIGITS : DIGITS -> option Number.uint := fun _ => None.

Declare Scope DIGITS_scope.
Delimit Scope DIGITS_scope with DIGITS.

Number Notation DIGITS decimal_to_DIGITS dummy_from_DIGITS : DIGITS_scope.

Definition Input : Type := list (list N).

Notation "'input' x .. y" := (map unDIGITS (cons x%DIGITS .. (cons y%DIGITS nil) ..))
  (at level 200, x at level 0, only parsing).

Definition example : Input := input
2199943210
3987894921
9856789892
8767896789
9899965678
.

#[local] Open Scope bool_scope.
#[local] Open Scope N_scope.

(* Add sentinel values *)
Definition pad (xs : Input) : Input :=
  let sentinel_row :=
    match xs with
    | [] => []
    | x :: _ => 10 :: 10 :: map (fun _ => 10) x
    end in
  sentinel_row :: map (fun x => 10 :: x ++ [10])%N xs ++ [sentinel_row].

Fixpoint find_local_min_row (r1 r2 r3 : list N) : list N :=
  match r1, r2, r3 with
  | _11 :: (x12 :: _13 :: _) as r1,
    x21 :: (x22 :: x23 :: _) as r2,
    _31 :: (x32 :: _33 :: _) as r3 =>
    if (x22 <? x12) && (x22 <? x21) && (x22 <? x23) && (x22 <? x32) then
      x22 :: find_local_min_row r1 r2 r3
    else
      find_local_min_row r1 r2 r3
  | _, _, _ => []
  end.

Fixpoint find_local_min (xs : Input) : list N :=
  match xs with
  | r1 :: (r2 :: r3 :: _) as xs =>
    find_local_min_row r1 r2 r3 ++ find_local_min xs
  | _ => []
  end.

Definition sum_N : list N -> N := fold_right N.add 0.

Definition solve (xs : Input) : N :=
  let ys := find_local_min (pad xs) in
  sum_N (map N.succ ys).

(* Compute solve example. *)

Module St.

Section St.

Context (S : Type).

Record m (A : Type) : Type := Mk { run : S -> S * A }.

Definition pure {A} (a : A) : m A := Mk (fun s => (s, a)).

Definition bind {A B} (u : m A) (k : A -> m B) : m B :=
  Mk (fun s =>
    let sa := run u s in
    run (k (snd sa)) (fst sa)).

Fixpoint concat_for {A B} (cat : B -> B -> B) (dog : B) (xs : list A) (f : A -> m B) : m B :=
  match xs with
  | nil => pure dog
  | x :: xs =>
    bind (f x) (fun y =>
    bind (concat_for cat dog xs f) (fun ys =>
    pure (cat y ys)))
  end.

Fixpoint for_ {A} (xs : list A) (f : A -> m unit) : m unit :=
  match xs with
  | nil => pure tt
  | x :: xs => bind (f x) (fun _ => for_ xs f)
  end.

End St.
End St.

Notation "'let!' a ':=' u 'in' v" := (St.bind u (fun a => v)) (at level 200, a binder).

Section CC.

Context (V : Type) `{EqDecision V, Countable V}.

Record graph : Type :=
  { nodes : list V
  ; neighbors : V -> list V
  }.

Record CC_state : Type :=
  { visited : gset V
  ; cur_component : list V
  }.

Definition set_visited (f : gset V -> gset V) (s : CC_state) : CC_state :=
  {| visited := f (visited s) ; cur_component := cur_component s |}.

Definition check_visited (v : V) : St.m CC_state bool :=
  St.Mk (fun s => (s, bool_decide (elem_of v (visited s)))).

Definition visit (v : V) : St.m CC_state unit :=
  St.Mk (fun s =>
    ( {| visited := union (singleton v) (visited s)
      ;  cur_component := v :: cur_component s |}
    , tt)).

Definition reset_cur_component : St.m CC_state unit :=
  St.Mk (fun s =>
    ( {| visited := visited s ; cur_component := nil |}
    , tt)).

Definition get_cur_component : St.m CC_state (list V) :=
  St.Mk (fun s => (s, cur_component s)).

Fixpoint create_component (g : graph) (fuel : nat) (v : V) : St.m CC_state unit :=
  let! bvisited := check_visited v in
  if bvisited then
    St.pure tt
  else match fuel with | O => St.pure tt | S fuel =>
    let! _ := visit v in
    St.for_ (neighbors g v) (create_component g fuel)
  end.

Fixpoint _connected_components (g : graph) (fuel : nat) (vs : list V) (cc : list (list V))
  : St.m CC_state (list (list V)) :=
  match vs with
  | nil => St.pure cc
  | v :: vs =>
    let! _ := reset_cur_component in
    let! _ := create_component g fuel v in
    let! c := get_cur_component in
    let cc :=
      match c with
      | nil => (* Already visited *) cc
      | _ :: _ => c :: cc
      end in
    _connected_components g fuel vs cc
  end.

Definition connected_components (g : graph) : list (list V) :=
  snd (St.run
    (_connected_components g (length (nodes g)) (nodes g) nil)
    {| visited := empty ; cur_component := nil |}).

End CC.

Definition foldi {A B} (f : N -> A -> B -> B) (xs : list A) (b0 : B) : B :=
  let fix _foldi (n : N) (xs : list A) :=
    match xs with
    | x :: xs => f n x (_foldi (N.succ n) xs)
    | nil => b0
    end in _foldi 0 xs.

Definition map_of_grid (xs : list (list N)) : gmap (N * N) N :=
  foldi (fun i =>
    foldi (fun j h => insert (i, j) h))
    xs empty.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end.

Definition not_mountain (m : gmap (N * N) N) (ij : N * N) : bool :=
  match lookup ij m with
  | None => false
  | Some h => h <? 9
  end.

Definition fourneighbors (m : gmap (N * N) N) '((i,j) : N * N) : list (N * N) :=
  filter (not_mountain m) [(i+1,j);(i-1,j);(i,j+1);(i,j-1)].

(* Assumes padding on the sides *)
Definition graph_of_map (m : gmap (N * N) N) : graph (N * N) :=
  {| nodes := filter (not_mountain m) (elements (dom (gset (N * N)) m))
  ;  neighbors := fourneighbors m
  |}.

Definition graph_of_grid (m : list (list N)) : graph (N * N) :=
  graph_of_map (map_of_grid (pad m)).

(* Compute connected_components (graph_of_grid example). *)

Definition solve2 (m : Input) : N :=
  let ccs := connected_components (graph_of_grid m) in
  let sizes := merge_sort N.ge (map (fun cc => N.of_nat (length cc)) ccs) in
  match sizes with
  | a :: b :: c :: _ => a * b * c
  | _ => 0
  end.

(* Compute solve2 example. *)

Definition solve12 (xs : Input) : N * N := (solve xs, solve2 xs).
