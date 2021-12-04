From Coq Require Export NArith List.
Import ListNotations.

#[global] Open Scope N.

Declare Custom Entry bingo.
Declare Custom Entry bingo1.

Record Input := { rand : list N ; boards : list (list (list N)) }.

Notation "'input' rand1 ',' .. ',' randn board1 .. boardn" :=
  {| rand := cons rand1 .. (cons randn nil) ..
  ;  boards := cons board1 .. (cons boardn nil) ..
  |}
  (at level 200, randn at level 0, board1 custom bingo, only parsing).

Notation "a b c d e" := [a; b; c; d; e]
  (in custom bingo at level 1, a custom bingo1, b custom bingo1, c custom bingo1, d custom bingo1, e custom bingo1).

Notation "a b c d e" := [a; b; c; d; e]
  (in custom bingo1 at level 1, a constr at level 0, b constr at level 0, c constr at level 0, d constr at level 0, e constr at level 0).

Definition example : Input := input
7,4,9,5,11,17,23,2,0,14,21,24,10,16,13,6,15,25,12,22,18,20,8,19,3,26,1

22 13 17 11  0
 8  2 23  4 24
21  9 14 16  7
 6 10  3 18  5
 1 12 20 15 19

 3 15  0  2 22
 9 18 13 17  5
19  8  7 25 23
20 11 10 24  4
14 21 16 12  6

14 21 17 24  4
10 16 15  9 19
18  8 23 26 20
22 11 13  6  5
 2  0 12  3  7 
.

Definition Board := list (list (option N)).

Definition mkBoard : list (list N) -> Board := map (map Some).

Definition call (n : N) : Board -> Board :=
  map (map (fun x => match x with Some m => if N.eqb m n then None else x | None => x end)).

Fixpoint zip_with {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  | _, _ => nil
  end.

Fixpoint transpose {A} (xs : list (list A)) : list (list A) :=
  match xs with
  | x :: [] => map (fun y => cons y nil) x
  | x :: xs => zip_with cons x (transpose xs)
  | [] => []
  end.

Definition isNone {A} (x : option A) : bool :=
  match x with
  | None => true
  | Some _ => false
  end.

Definition cleared : list (option N) -> bool :=
  forallb isNone.

Definition winning (b : Board) : bool :=
  existsb cleared b || existsb cleared (transpose b).

Fixpoint fold_with {A B} (f : B -> B -> B) (y : B) (g : A -> B) (xs : list A) : B :=
  match xs with
  | [] => y
  | x :: xs => f (g x) (fold_with f y g xs)
  end.

Definition sum_with {A} : (A -> N) -> list A -> N := fold_with N.add 0%N.

Definition score : Board -> N :=
  sum_with (sum_with (fun x => match x with None => 0 | Some x => x end)).

Fixpoint bingo (rs : list N) (bs : list Board) : N * Board :=
  match rs with
  | [] => (0, [])  (* must not happen *)
  | r :: rs =>
    let bs := map (call r) bs in
    match find winning bs with
    | None => bingo rs bs
    | Some b => (r, b)
    end
  end.

Definition solve (xs : Input) : N :=
  let '(r, b) := bingo (rand xs) (map mkBoard (boards xs)) in
  r * score b.

(* Compute solve example. *)

Fixpoint unbingo (rs : list N) (bs : list Board) : N * Board :=
  match rs with
  | [] => (0, [])  (* must not happen *)
  | r :: rs =>
    let bs0 := map (call r) bs in
    let bs := filter (fun b => negb (winning b)) bs0 in
    match bs with
    | [] =>
      match bs0 with
      | b :: _ => (r, b)
      | _ => (0, [])  (* must not happen *)
      end
    | _ => unbingo rs bs
    end
  end.

Definition solve2 (xs : Input) : N :=
  let '(r, b) := unbingo (rand xs) (map mkBoard (boards xs)) in
  r * score b.

(* Compute solve2 example. *)

Definition solve12 (xs : Input) : N * N :=
  (solve xs, solve2 xs).
