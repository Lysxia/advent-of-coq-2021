From Coq Require Export ZArith NArith List String Ascii.
From stdpp Require Import gmap.
Import ListNotations.

Set Implicit Arguments.

(* dirty preprocessing will insert an empty string *)
Notation "'input' tbl _r0 r1 .. rn" := (tbl%string, cons r1%string .. (cons rn%string nil) ..)
  (at level 200, tbl at level 0, _r0 at level 0, r1 at level 0, rn at level 0, only parsing).

Definition example := input
"..#.#..#####.#.#.#.###.##.....###.##.#..###.####..#####..#....#..#..##..##
#..######.###...####..#..#####..##..#.#####...##.#.#..#.##..#.#......#.###
.######.###.####...#.##.##..#..#..#####.....#.#....###..#.##......#.....#.
.#..#..##..#...##.######.####.####.#.#...#.......#..#.#.#...####.##.#.....
.#..#...##.#.##..#...##.#.##..###.#......#.#.......#.#.#.####.###.##...#..
...####.#..#..#.##.#....##..#.####....##...##..#...#......#.#.......#.....
..##..####..#...#.#.#...##..#.#..###..#####........#..####......#..#"
""
"#..#."
"#...."
"##..#"
"..#.."
"..###"
.

Inductive cellstate := On | Off.

Definition foldli {A B} (f : N -> A -> B -> B) (b : B) (xs : list A) : B :=
  fold_right (fun x go i b => go (N.succ i) (f i x b)) (fun _ b => b) xs 0%N b.

Definition _mk_table (s : string) : gmap N unit :=
  foldli (fun i c => if (c =? "#")%char then insert i tt else fun m => m) empty
    (filter (fun c => (c =? "#") || (c =? "."))%bool%char (list_ascii_of_string s)).

Definition mk_table (s : string) : N -> cellstate :=
  let t := _mk_table s in
  fun i => match lookup i t with
    | None => Off
    | Some _ => On
    end.

Definition point : Type := Z * Z.

Definition mk_grid : list string -> list (list cellstate) :=
  map (fun row => map (fun c => if (c =? "#")%char then On else Off) (list_ascii_of_string row)).

Definition shifts0 {A} (x0 : A) : list (list A -> list A) :=
  [fun x => x; fun x => x0 :: x; fun x => x0 :: x0 :: x].

Definition shifts {A} (x0 : A) : list (list (list A) -> list (list A)) := Eval cbn in
  List.rev' (map (fun '(f, g) x => f (g x))
    (list_prod
      (shifts0 [])
      ((fun x => x) :: List.tl (map (@map _ _) (shifts0 x0))))).

Definition snocbit (i : N) (b : cellstate) :=
  match b with
  | On => N.succ_double i
  | Off => N.double i
  end.

Fixpoint zip_with_extend {A B C} (f : A -> B -> C) (x0 : A) (y0 : B)
    (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zip_with_extend f x0 y0 xs ys
  | [], _ => map (f x0) ys
  | _, [] => map (fun x => f x y0) xs
  end.

Definition nine (def : cellstate) (g : list (list cellstate)) : list (list N) :=
  let zz def' := zip_with_extend (zip_with_extend snocbit def' def) [] [] in
  snd (fold_left (fun '(def', g') z => (snocbit def' def, zz def' g' (z g))) (shifts def) (0%N, [])).

Definition step (f : N -> cellstate) '((def, g) : cellstate * list (list cellstate))
  : cellstate * list (list cellstate) :=
  let newdef :=
    match def with
    | Off => f 0%N
    | On => f 511%N
    end in
  (newdef, map (map f) (nine def g)).

Definition sum_with {A} (f : A -> N) (xs : list A) : N :=
  fold_left (fun i x => i + f x)%N xs 0%N.

Definition count '((def, g) : cellstate * list (list cellstate)) : N :=
  match def with
  | On => 9999999999%N (* Boo *)
  | Off => sum_with (sum_with (fun c => match c with On => 1 | Off => 0 end)%N) g
  end.

Definition enhance (n : N) (f : N -> cellstate)
  : cellstate * list (list cellstate) -> cellstate * list (list cellstate) :=
  N.iter n (step f).

Definition solve '(t, g) :=
  let t := mk_table t in
  let g := (Off, mk_grid g) in
  count (enhance 2 t g).

(* Compute solve example. *)
(*
Compute
  let '(t, g) := example in
  let t := mk_table t in
  let g := (Off, mk_grid g) in
  step t (step t g).
*)

Definition solve2 '(t, g) :=
  let t := mk_table t in
  let g := (Off, mk_grid g) in
  count (enhance 50 t g).

(* Compute solve2 example. *)

Definition solve12 '(t, g) :=
  let t := mk_table t in
  let g := (Off, mk_grid g) in
  (count (enhance 2 t g), count (enhance 50 t g)).
