From Coq Require Export Ascii String NArith.
From stdpp Require Import gmap.

#[global] Open Scope N_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(* Parsing *)

Declare Custom Entry edge.

Notation "'input' e1 .. en" := (cons e1 .. (cons en nil) ..)
  (at level 200, e1 custom edge, en custom edge).

Notation "x '-' y" := (x%string, y%string)
  (in custom edge at level 1, x constr at level 0, y constr at level 0).

Definition Input : Type := list (string * string).

Definition example : Input := input
"start"-"A"
"start"-"b"
"A"-"c"
"A"-"b"
"b"-"d"
"A"-"end"
"b"-"end"
.

(* Graphs *)

Section G.

Context (V : Type) `{EqDecision V, Countable V}.

Definition graph : Type := gmap V (list V).

Definition add_edge (x y : V) (g : graph) : graph :=
  let alt ys := Some match ys with None => [y] | Some ys => (y :: ys) end in
  partial_alter alt x g.

Definition get_edges (x : V) (g : graph) : list V :=
  match lookup x g with
  | None => []
  | Some ys => ys
  end.

Definition adj_list (xs : list (V * V)) : graph :=
  fold_left (fun g '(x, y) => add_edge x y (add_edge y x g)) xs empty.

End G.

Arguments graph : clear implicits.
Arguments graph V {_ _}.

(* Recursion and memoization *)

Definition endo (X : Type) : Type := (X -> X).

Class Monad M : Type :=
  { ret : forall {A}, A -> M A
  ; bind : forall {A B}, M A -> (A -> M B) -> M B
  }.

Declare Scope monad_scope.
#[global] Open Scope monad_scope.

Notation "'let*' x ':=' u 'in' v" := (bind u (fun x => v)) (at level 200) : monad_scope.

Fixpoint traverse {M} `{Monad M} {A B} (f : A -> M B) (xs : list A) : M (list B) :=
  match xs with
  | [] => ret []
  | x :: xs =>
    let* y := f x in
    let* ys := traverse f xs in
    ret (y :: ys)
  end.

Record identity (A : Type) : Type := Mk_identity { run_identity : A }.

Instance Monad_identity : Monad identity :=
  {| ret _ x := Mk_identity x
  ;  bind _ _ u k := k (run_identity u) 
  |}.

Fixpoint naive_fix (fuel : nat) {A R} (r0 : R) (gf : endo (A -> identity R)) : A -> R :=
  fun x =>
    run_identity (gf (fun x => Mk_identity match fuel with
        | O => r0
        | S fuel => naive_fix fuel r0 gf x
        end) x).

Record state (S A : Type) : Type := Mk_state { run_state : S -> S * A }.

Instance Monad_state {S} : Monad (state S) :=
  {| ret _ x := Mk_state (fun s => (s, x))
  ;  bind _ _ u k := Mk_state (fun s =>
       let '(s, x) := run_state u s in
       run_state (k x) s) |}.

Definition memom (A R : Type) `{EqDecision A, Countable A} : Type -> Type := state (gmap A R).

Fixpoint _memo_fix (fuel : nat) {A R} `{EqDecision A, Countable A}
  (r0 : R) (gf : endo (A -> state (gmap A R) R)) : A -> state (gmap A R) R :=
  fun x => Mk_state (fun s =>
    match lookup x s with
    | Some y => (s, y)
    | None =>
      let __memo_fix x := match fuel with O => ret r0 | S fuel => _memo_fix fuel r0 gf x end in
      let '(s, y) := run_state (gf __memo_fix x) s in
      (insert x y s, y)
    end).

Definition memo_fix (fuel : nat) {A R} `{EqDecision A, Countable A}
  (r0 : R) (gf : endo (A -> state (gmap A R) R)) : A -> R :=
  fun x => snd (run_state (_memo_fix fuel r0 gf x) empty).

(* DFS *)

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

Notation v := string (only parsing).

Definition is_big (x : v) : bool :=
  match x with
  | ""%string => false
  | String c _ => ((N_of_ascii "A" <=? N_of_ascii c) && (N_of_ascii c <=? N_of_ascii "Z"))
  end.

Definition visit (x : v) (visited : set v) : option (set v) :=
  if is_big x then Some visited
  else if elem_set x visited then None
  else Some (insert_set x visited).

Definition start_from (x : v) : set v * v :=
  (insert_set x empty, x).

Definition sum_N (xs : list N) : N :=
  fold_left N.add xs 0.

Definition _count_paths {M} `{Monad M} {VISITED} (_visit : v -> VISITED -> option VISITED)
  (g : graph v) : endo (VISITED * v -> M N) := fun __count_paths '(visited, x) =>
  if String.eqb x "end" then ret 1 else
  let search x := match _visit x visited with
    | None => ret 0
    | Some visited => __count_paths (visited, x)
    end in
  let* ns := traverse search (get_edges x g) in
  ret (sum_N ns).

(* The maximum length can be up to twice the number of nodes, because we can revisit big nodes.
   An implicit assumption is that there are no adjacent big nodes, so a long path must consist
   of an alternation of big and small nodes, and each small node is visited once, hence the bound. *)
Definition count_paths (g : graph v) : N :=
  memo_fix (2 * size g) 0 (_count_paths visit g) (start_from "start").

Definition solve (xs : Input) : N :=
  count_paths (adj_list xs).

(* Compute solve example. *)

Definition visit2 (x : v) '((may_revisit, visited) : bool * set v) : option (bool * set v) :=
  if is_big x then Some (may_revisit, visited)
  else if elem_set x visited then
    if negb (String.eqb x "start") && may_revisit then Some (false, visited) else None
  else Some (may_revisit, insert_set x visited).

Definition start_from2 (x : v) : ((bool * set v) * v) :=
  ((true, insert_set x empty), x).

Definition count_paths2 (g : graph v) : N :=
  memo_fix (2 * S (size g)) 0 (_count_paths visit2 g) (start_from2 "start").

Definition solve2 (xs : Input) : N :=
  count_paths2 (adj_list xs).

(* Compute solve2 example. *)

Definition solve12 xs := (solve xs, solve2 xs).
