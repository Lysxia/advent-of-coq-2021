From Coq Require Export ZArith Ascii String.
From Coq Require Import List.
From stdpp Require Import gmap.

#[global] Open Scope string_scope.

Declare Custom Entry paper.
Declare Custom Entry paperf.

Notation "'input' d1 .. dn f1 .. fn" := (cons d1 .. (cons dn nil) .., cons f1 .. (cons fn nil) ..)
  (at level 200, d1 custom paper, f1 custom paperf, only parsing).

Notation "x , y" := (x%Z,y%Z)
  (in custom paper at level 1, x constr at level 0, y constr at level 0).

Notation "'fold' 'along' c '=' x" := (c x%Z)
  (in custom paperf at level 1, c constr at level 0, x constr at level 0).

Inductive axis :=
| x (_ : Z)
| y (_ : Z)
.

Definition point : Type := Z * Z.

Definition Input : Type := (list point * list axis).

Definition example := input
6,10
0,14
9,10
0,3
10,4
4,11
6,0
6,12
4,1
0,13
10,12
3,4
3,0
8,4
1,10
2,14
8,10
9,0

fold along y=7
fold along x=5
.

#[local] Open Scope Z_scope.

Definition fold1_along_x (n : Z) '((i, j) : point) : point :=
  (if n <=? i then 2 * n - i else i, j).

Definition fold1_along_y (n : Z) '((i, j) : point) : point :=
  (i, if n <=? j then 2 * n - j else j).

Definition fold1_along (n : axis) : point -> point :=
  match n with
  | x n => fold1_along_x n
  | y n => fold1_along_y n
  end.

Definition fold_along (n : axis) : list point -> list point :=
  map (fold1_along n).

(* stdpp's is quadratic *)
Definition list_to_set {A} `{Countable A} (xs : list A) : gset A :=
  dom (M := gmap A unit) (gset A) (fold_right (fun x m => insert x tt m) empty xs).

Definition solve '((dots, folds) : Input) : N :=
  match folds with
  | nil => 0%N
  | f :: _ => N.of_nat (size (C := gset _) (list_to_set (fold_along f dots)))
  end.

(* Compute solve example. *)

Definition fold_all '((dots, folds) : Input) : list point :=
  fold_left (fun dots f => fold_along f dots) folds dots.

Definition matrix_of (imin imax jmin jmax : Z) {A} (f : Z * Z -> A) : list (list A) :=
  N.recursion (fun x => x) (fun dj k nil_ =>
    let j := jmin + Z.of_N dj in
    k (cons (N.recursion (fun x => x) (fun di k nil_ =>
      let i := imin + Z.of_N di in
      k (cons (f (i, j)) nil_)) (Z.to_N (imax - imin + 1)) nil)
      nil_)
  ) (Z.to_N (jmax - jmin + 1)) nil.

Infix "::" := String : string_scope.

Definition display_matrix (xs : list (list ascii)) : string :=
  fold_right (fun row s =>
    "010" :: fold_right (fun c s => c :: s) s row) ""%string xs.

Definition display (dots : list point) : string :=
  let dots := list_to_set dots in
  let imax := fold_left (fun i '(i', _) => Z.max i i') (elements dots) 0 in
  let jmax := fold_left (fun j '(_, j') => Z.max j j') (elements dots) 0 in
  display_matrix (matrix_of 0 imax 0 jmax (fun ij =>
    if decide (elem_of ij dots) then "#"%char else "."%char)).

Definition solve2 (xs : Input) : string :=
  display (fold_all xs).

(* Compute solve2 example. *)

Definition solve12 (xs : Input) := (solve xs, solve2 xs).
