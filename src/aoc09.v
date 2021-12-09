From Coq Require Export NArith List Number Decimal.

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
