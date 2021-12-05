From Coq Require Export List NArith.
From stdpp Require Import base gmap.

#[global] Open Scope N_scope.

Declare Custom Entry line.

Notation "'input' l1  ..  ln" := (cons l1 .. (cons ln nil) ..) (at level 200, l1 custom line, only parsing).

Notation "x1 ',' y1 '->' x2 ',' y2" := ((x1, y1), (x2, y2))
  (in custom line at level 1, x1 constr at level 0, y1 constr at level 0, x2 constr at level 0, y2 constr at level 0).

Notation Point := (N * N)%type.

Notation Line := (Point * Point)%type.

Definition Input : Type := list Line.

Definition example : Input := input
0,9 -> 5,9
8,0 -> 0,8
9,4 -> 3,4
2,2 -> 2,1
7,0 -> 7,4
6,4 -> 2,0
0,9 -> 2,9
3,4 -> 1,4
0,0 -> 8,8
5,5 -> 8,2
.

Definition is_hline '(((_, y1), (_, y2)) : Line) : bool :=
  y1 =? y2.

Definition is_vline '(((x1, _), (x2, _)) : Line) : bool :=
  x1 =? x2.

Definition is_hvline (l : Line) : bool :=
  is_hline l || is_vline l.

Definition iter_line {A} (l : Line) (f : Point -> A -> A) (x : A) : A :=
  let '((x1, y1), (x2, y2)) := l in
  if y1 =? y2 then
    let '(x1, x2) := if x1 <=? x2 then (x1, x2) else (x2, x1) in
    N.recursion x (fun i => f (x1+i, y1)) (x2 - x1 + 1)
  else if x1 =? x2 then
    let '(y1, y2) := if y1 <=? y2 then (y1, y2) else (y2, y1) in
    N.recursion x (fun i => f (x1, y1+i)) (y2 - y1 + 1)
  else if x1 <? x2 then
    let add := if y1 <=? y2 then N.add else N.sub in
    N.recursion x (fun i => f (x1+i, add y1 i)) (x2 - x1 + 1)
  else
    let add := if y2 <=? y1 then N.add else N.sub in
    N.recursion x (fun i => f (x2+i, add y2 i)) (x1 - x2 + 1).

Definition add_line (l : Line) : gmap Point positive -> gmap Point positive :=
  let incr o := Some match o with None => 1%positive | Some n => Pos.succ n end in
  iter_line l (partial_alter incr).

Definition cover (l : list Line) : gmap Point positive :=
  fold_left (fun m l => add_line l m) l empty.

Definition overlapping (x : Point * positive) : Prop :=
  (1 < snd x)%positive.

Definition solve (ls : list Line) : nat :=
  size $ filter overlapping $ cover $ filter is_hvline ls.

(* Compute solve example. *)

Definition sizeN {A} (xs : list A) : N :=
  let fix s n xs :=
    match xs with
    | [] => n
    | _ :: xs => s (N.succ n) xs
    end in
  s 0 xs.

Definition solve2 (ls : list Line) : _ :=
  length $ map_to_list $ filter overlapping $ cover ls.

(* Compute solve2 example. *)

Definition solve12 (ls : list Line) : _ :=
  (solve ls, solve2 ls).
