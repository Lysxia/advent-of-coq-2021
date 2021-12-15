From Coq Require Export NArith List Number Decimal.
From Coq Require Import ZArith.

From stdpp Require Import gmap sorting.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.

#[global] Open Scope N_scope.

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
  end.

Record DIGITS := { unDIGITS : list N }.

Definition decimal_to_DIGITS (d : Number.uint) :=
  match d with
  | UIntDecimal d => Some {| unDIGITS := decimal_to_digits d |}
  | _ => None
  end.

Definition dummy_from_DIGITS : DIGITS -> option Number.uint := fun _ => None.

Declare Scope DIGITS_scope.
Delimit Scope DIGITS_scope with DIGITS.

Number Notation DIGITS decimal_to_DIGITS dummy_from_DIGITS : DIGITS_scope.

Definition foldi {A B} (f : N -> A -> B -> B) (xs : list A) (b0 : B) : B :=
  let fix _foldi (n : N) (xs : list A) :=
    match xs with
    | x :: xs => f n x (_foldi (N.succ n) xs)
    | nil => b0
    end in _foldi 0 xs.

(* N is awkward because of saturating subtraction, we use Z so going negative
   is a natural way to detect going "out of bounds". *)
Definition point : Type := Z * Z.

Definition map_of_grid (xs : list (list N)) : gmap point N :=
  foldi (fun j =>
    foldi (fun i h => insert (Z.of_N i, Z.of_N j) h))
    xs empty.

Record Input : Type := MkInput
  { input_grid : gmap point N
  ; input_dim : N * N
  }.

Definition input_of_grid (xs : list (list N)) : Input :=
  {| input_grid := map_of_grid xs
  ;  input_dim := match xs with
                  | [] => (0, 0)
                  | row ::_ => (N.of_nat (length row), N.of_nat (length xs))
                  end |}.

Notation "'input' x .. y" := (input_of_grid (map unDIGITS (cons x%DIGITS .. (cons y%DIGITS nil) ..)))
  (at level 200, x at level 0, only parsing).

Definition example : Input := input
1163751742
1381373672
2136511328
3694931569
7463417111
1319128137
1359912421
3125421639
1293138521
2311944581
.

(* Priority queue with a heap à la Lampropoulos (Ode on a random urn) *)
Module Q.

Inductive t (K : Type) (leK : K -> K -> Prop) (V : Type) : Type :=
| Node : K -> V -> t leK V -> t leK V -> t leK V
  (* invariant: the right tree is bigger than the left tree *)
| Leaf : t leK V
.

Section Q.

Context {K : Type} {leK : K -> K -> Prop} {V : Type} `{!RelDecision leK}.

Definition empty : t leK V := Leaf.

Fixpoint push (k : K) (v : V) (q : t leK V) : t leK V :=
  match q with
  | Leaf => Node k v Leaf Leaf
  | Node k' v' l r =>
    if decide_rel leK k k' then Node k v r (push k' v' l) else Node k' v' r (push k v l)
  end.

Fixpoint unsnoc (q : t leK V) : option (K * V * t leK V) :=
  match q with
  | Leaf => None
  | Node k v l r =>
    match unsnoc r with
    | None => Some (k, v, Leaf)
    | Some (k', v', r') => Some (k', v', Node k v r' l)
    end
  end.

(* Remove the root of [q] and push [(k, v)]. This looks awkward but seems necessary
   to make the function structurally recursive. *)
Fixpoint sift (k : K) (v : V) (q : t leK V) : t leK V :=
  match q with
  | Leaf => Node k v Leaf Leaf
  | Node _ _ l r =>
    match l, r with
    | Leaf, Node k' v' _ _ =>
      if decide_rel leK k k' then Node k v l r else Node k' v' Leaf (Node k v Leaf Leaf)
    | _, Leaf => Node k v l r (* If r = Leaf then l = Leaf *)
    | Node kl vl _ _, Node kr vr _ _ =>
      if decide_rel leK kl kr then
        if decide_rel leK k kl then
          Node k v l r
        else
          Node kl vl (sift k v l) r
      else
        if decide_rel leK k kr then
          Node k v l r
        else
          Node kr vr l (sift k v r)
    end
  end.

Definition pop (q : t leK V) : option (K * V * t leK V) :=
  match q with
  | Leaf => None
  | Node k v l r =>
    let q :=
      match unsnoc r with
      | None => Leaf
      | Some (k', v', r') => sift k' v' (Node k v r' l)
      end in
    Some (k, v, q)
  end.

Fixpoint pops (n : nat) (q : t leK V) : list (K * V) :=
  match n with
  | O => []
  | S n =>
    match pop q with
    | None => []
    | Some (k, v, q) => (k, v) :: pops n q
    end
  end.

End Q.
End Q.

(* Compute Q.pops 5 (Q.push (leK := N.le) 3 tt (Q.push 2 tt (Q.push 7 tt (Q.push 4 tt Q.empty)))). *)

Definition isSome {A} (x : option A) :=
  match x with
  | Some _ => true
  | None => false
  end.

(* [gset] insertion (as [fun x s => union (singleton x) s]) is slow,
   so we redefine our own sets from maps which have fast [insert]. *)
Notation set X := (gmap X unit).
Notation insert_set x s := (insert x tt s).
Notation elem_set x s := (isSome (lookup x s)).

Section Dijkstra.

Context (V : Type) `{EqDecision V, Countable V}.

Record graph : Type :=
  { max_edges : nat  (* upper bound on the number of edges, as fuel *)
  ; neighbors : V -> list (N * V)
  }.

Definition no_fuel : N. Proof. exact 0. Qed.

Fixpoint _dijkstra (g : graph) (goal : V) (q : Q.t N.le V) (visited : set V) (fuel : nat) : N :=
  match fuel with O => no_fuel | S fuel =>
  match Q.pop q with None => 0 | Some (d, v, q) =>
  if decide (v = goal) then d (* REACHED GOAL *) else
  if elem_set v visited then _dijkstra g goal q visited fuel (* SKIP *) else
  let visited := insert_set v visited in
  let q := fold_left (fun q '(dd, v) => Q.push (d + dd) v q) (neighbors g v) q in
  _dijkstra g goal q visited fuel
  end
  end.

Definition dijkstra (g : graph) (goal start : V) : N :=
  _dijkstra g goal (Q.push 0 start Q.empty) empty (S (max_edges g)).

End Dijkstra.

Definition grid_neighbors '((i,j) : point) : list point :=
  [(i+1,j); (i-1,j); (i,j+1); (i,j-1)]%Z.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end%list.

Definition neigh (m : gmap point N) (ij : point) : list (N * point) :=
  map_filter (fun ij =>
    match lookup ij m with
    | None => None
    | Some d => Some (d, ij)
    end) (grid_neighbors ij).

Definition graph_of_input (i : Input) : graph point :=
  {| max_edges := let '(x, y) := input_dim i in N.to_nat (4 * x * y)
  ;  neighbors := neigh (input_grid i)
  |}.

Definition solve (i : Input) : N :=
  let g := graph_of_input i in
  let start := (0, 0)%Z in
  let '(x, y) := input_dim i in
  let goal := (Z.of_N (x - 1), Z.of_N (y - 1)) in 
  dijkstra g goal start.

(* Compute solve example. *)

Module Part2.
Section Part2.

Context (ii : Input).

Definition REPEAT := 5.

Definition goal :=
  let '(x, y) := input_dim ii in
  (Z.of_N (REPEAT * x - 1), Z.of_N (REPEAT * y - 1)).

Definition decompose_point '((i, j) : point) : N * point :=
  let '(x, y) := input_dim ii in
  ( ((Z.to_N i `div` x) + (Z.to_N j `div` y))%N
  , (i `mod` Z.of_N x, j `mod` Z.of_N y)%Z).

Definition out_of_bounds '((i, j) : point) : bool :=
  let '(x, y) := input_dim ii in
  (i <? 0)%Z || (j <? 0)%Z || (Z.of_N (REPEAT * x) <=? i)%Z || (Z.of_N (REPEAT * y) <=? j)%Z.

Definition neigh (m : gmap point N) (ij : point) : list (N * point) :=
  map_filter (fun ij =>
    if out_of_bounds ij then None else
    let '(s, ij') := decompose_point ij in
    let wrap x := ((x - 1) `mod` 9) + 1 in
    match lookup ij' m with
    | None => None
    | Some d => Some (wrap (d + s), ij)
    end) (grid_neighbors ij).

Definition graph_of_input : graph point :=
  {| max_edges := let '(x, y) := input_dim ii in N.to_nat (100 * x * y)  (* 4 * REPEAT * REPEAT *)
  ;  neighbors := neigh (input_grid ii)
  |}.

Definition solve : N :=
  let g := graph_of_input in
  let start := (0, 0)%Z in
  dijkstra g goal start.

End Part2.
End Part2.

Definition solve2 := Part2.solve.

(*
Section Test.

Let g := Part2.graph_of_input example.

Compute neighbors g (11,0)%Z.

End Test.
*)

(* Compute solve2 example. *)

Definition solve12 i := (solve i, solve2 i).
