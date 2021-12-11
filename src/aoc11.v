From Coq Require Export NArith List Number Decimal.
From Coq Require Import ZArith.

From stdpp Require Import gmap sorting.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.

#[local] Open Scope N_scope.

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

Definition point : Type := Z * Z.

(* N is awkward because of saturating subtraction, we use Z so going negative
   is a natural way to detect going "out of bounds". *)
Definition map_of_grid (xs : list (list N)) : gmap point N :=
  foldi (fun i =>
    foldi (fun j h => insert (Z.of_N i, Z.of_N j) h))
    xs empty.

Definition Input : Type := gmap point N.

Notation "'input' x .. y" := (map_of_grid (map unDIGITS (cons x%DIGITS .. (cons y%DIGITS nil) ..)))
  (at level 200, x at level 0, only parsing).

Definition example : Input := input
5483143223
2745854711
5264556173
6141336146
6357385478
4167524645
2176841721
6882881134
4846848554
5283751526
.

(* Phase 1 *)
Definition incr_all (g : gmap point N) : gmap point N :=
  fmap N.succ g.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end.

(* Phase 2.a: Find the first ones to reach 10 *)
Definition first_flash (g : gmap point N) : list point :=
  let flashy '(ij, energy) := if energy <=? 9 then None else Some ij in
  map_filter flashy (map_to_list g).

(* Phase 2.b: Propagage the energy *)

(* We only process each flashing point once, when it increases from 9 to 10. *)
Definition radiate '(ij : point) (g : gmap point N) (todo : list point)
  : gmap point N * list point :=
  match lookup ij g with
  | None => (g, todo)
  | Some energy =>
      (insert ij (N.succ energy) g, if energy =? 9 then ij :: todo else todo)
  end.

Definition neighbors '((i,j) : point) : list point :=
  [(i+1,j+1); (i+1,j); (i+1,j-1); (i,j+1); (i,j-1); (i-1,j+1); (i-1,j); (i-1,j-1)]%Z.

Definition flash (ij : point) (g : gmap point N) (todo : list point)
  : gmap point N * list point :=
  fold_left (fun '(g, todo) ij => radiate ij g todo) (neighbors ij) (g, todo).

Fixpoint _propagate (fuel : nat) (g : gmap point N) (ndone : N) (todo : list point)
  : gmap point N * N :=
  match todo, fuel with
  | [], _ => (g, ndone)
  | _, O => (empty, 0)  (* Should not happen *)
  | ij :: todo, S fuel =>
      let '(g, todo) := flash ij g todo in
      _propagate fuel g (N.succ ndone) todo
  end.

(* Phase 2 *)
Definition propagate (g : gmap point N) : gmap point N * N :=
  _propagate (size g) g 0 (first_flash g).

(* Phase 3 *)
Definition exhaust (g : gmap point N) : gmap point N :=
  fmap (fun energy => if energy <=? 9 then energy else 0)%N g.

Definition step (g : gmap point N) : gmap point N * N :=
  let g := incr_all g in
  let '(g, n) := propagate g in
  let g := exhaust g in
  (g, n).

Fixpoint _steps (n : nat) (g : gmap point N) (nflashes : N) : gmap point N * N :=
  match n with
  | O => (g, nflashes)
  | S n =>
    let '(g, more) := step g in
    _steps n g (nflashes + more)
  end.

Definition steps (n : nat) (g : gmap point N) : N := snd (_steps n g 0).

Definition solve := steps 100.

(* Compute solve example. *)

Definition steps2 (fuel : N) (g : gmap point N) : N :=
  let sz := N.of_nat (size g) in
  N.iter fuel
    (fun self '(g, n) =>
      let n := N.succ n in
      let '(g, flashes) := step g in
      if flashes =? sz then n else self (g, n))
    (fun _ => 0%N (* should not happen with enough fuel *))
    (g, 0).

Definition solve2 := steps2 1000.

(* Compute solve2 example. *)

Definition solve12 g := (solve g, solve2 g).

(* Spec (no proofs) *)

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

Definition radiate' '(ij : point) (g : gmap point N) : gmap point N :=
  match lookup ij g with
  | None => g
  | Some energy => insert ij (N.succ energy) g
  end.

Definition flash' (ij : point) (g : gmap point N) : gmap point N :=
  fold_left (fun g ij => radiate' ij g) (neighbors ij) g.

Record state : Type := MkState
  { energies : gmap point N  (* current levels *)
  ; flashed : set point      (* points that already flashed *)
  }.

Definition lookup0 (ij : point) (m : gmap point N) : N :=
  match lookup ij m with
  | Some n => n
  | None => 0
  end.

Definition one_flash : state -> state -> Prop := fun s s' =>
  exists ij, 9 <? lookup0 ij (energies s) /\ ~ elem_of ij (dom (gset _) (flashed s)) /\
    s' = {| energies := flash' ij (energies s) ; flashed := insert_set ij (flashed s) |}.

Lemma strongly_confluent_one_flash_prop (s s1 s2 : state)
  : one_flash s s1 -> one_flash s s2 ->
    s1 = s2 \/ exists s3, one_flash s1 s3 /\ one_flash s2 s3.
Proof.
Abort.

Inductive star {A} (r : A -> A -> Prop) : A -> A -> Prop :=
| star_zero x : star r x x
| star_succ x y z : r x y -> star r y z -> star r x z
.

Definition all_flash : state -> state -> Prop := fun s s' =>
  star one_flash s s' /\ forall s'', ~ one_flash s' s''.

Theorem step_correct g
  : exists s', all_flash (MkState g empty) s'
      /\ step g = (energies s', N.of_nat (size (flashed s'))).
Proof.
Abort.
