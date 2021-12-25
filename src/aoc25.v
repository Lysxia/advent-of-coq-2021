From Coq Require Export String Ascii NArith List.
From stdpp Require Import list strings.

Notation "'input' r0 .. rn" := (cons r0%string .. (cons rn%string nil) ..)
  (at level 200, r0 at level 0, rn at level 0, only parsing).

Definition example := input
"v...>>.vv>"
".vv>>.vv.."
">>.>v>...v"
">>v>>.>.v."
"v>v.vv.v.."
">.>>..v..."
".vv..>.>v."
"v.v..>>v.v"
"....v..v.>"
.

Inductive cell := Right | Down | Empty.
Definition parse (xs : list string) : list (list cell) :=
  map (fun row =>
    map (fun c =>
      if (c =? "v")%char then Down else if (c =? ">")%char then Right else Empty)
      (list_ascii_of_string row))
    xs.

Fixpoint init {A} (xs : list A) : list A :=
  match xs with
  | _ :: nil => nil
  | x :: xs => x :: init xs
  | nil => nil
  end.

(* [xs] is a row extended with the last cell at the beginning and the first cell at the end. *)
Fixpoint _move_right (xs : list cell) : list cell :=
  match xs with
  | Right :: Empty :: xs => Empty :: Right :: _move_right xs
  | x :: xs => x :: _move_right xs
  | nil => nil
  end.

Definition move_right : list (list cell) -> list (list cell) :=
  map (fun row => init (List.tl (_move_right (List.last row Empty :: row ++ List.hd Empty row :: nil)))).

Fixpoint zip_with {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  | _, _ => nil
  end.

Fixpoint transpose {A} (xs : list (list A)) : list (list A) :=
  match xs with
  | x :: nil => map (fun y => cons y nil) x
  | x :: xs => zip_with cons x (transpose xs)
  | nil => nil
  end.

Definition swap (c : cell) : cell :=
  match c with
  | Down => Right
  | Right => Down
  | Empty => Empty
  end.

Definition transpose' (xs : list (list cell)) : list (list cell) :=
  transpose (map (map swap) xs).

Definition move_down (xs : list (list cell)) : list (list cell) :=
  transpose' (move_right (transpose' xs)).

#[global] Instance EqDecision_cell : EqDecision cell. 
Proof. solve_decision. Defined.

Fixpoint steps (fuel : nat) (xs : list (list cell)) : list (list cell) :=
  match fuel with
  | O => xs
  | S fuel =>
    let xs' := move_down (move_right xs) in
    steps fuel xs'
  end.

Definition show_map (xs : list (list cell)) : string :=
  let cell2ascii x :=
    match x with
    | Down => "v"
    | Right => ">"
    | Empty => "."
    end%char in
  let nl := String "010" "" in
  nl ++ String.concat nl (map (fun row => string_of_list_ascii (map cell2ascii row)) xs).

Fixpoint steps_to_stop (fuel : nat) (xs : list (list cell)) : N :=
  match fuel with
  | O => 0
  | S fuel =>
    let xs' := move_down (move_right xs) in
    if bool_decide (xs = xs') then 1 else N.succ (steps_to_stop fuel xs')
  end.

Definition solve (xs : list string) : N := steps_to_stop 999 (parse xs).

(* Compute solve example. *)
