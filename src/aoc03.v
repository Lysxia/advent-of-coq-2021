From Coq Require Export ZArith NArith List Number Decimal.

Import ListNotations.

Record bits := Mk_bits { unbits : list bool }.

(* Reinterpret a decimal with only digits 0 and 1 in binary. *)
Fixpoint bindec_to_bits_ (d : Decimal.uint) : list bool :=
  match d with
  | D0 d => false :: bindec_to_bits_ d
  | D1 d => true :: bindec_to_bits_ d
  | Nil | _ => []
  end.

Definition bindec_to_bits (d : Decimal.uint) : bits := Mk_bits (bindec_to_bits_ d).

Definition dummy_bits_to (b : bits) : option Decimal.uint := None.

Declare Scope bits_scope.
Number Notation bits bindec_to_bits dummy_bits_to : bits_scope.

Notation "'input' x .. y" := (cons (unbits x) .. (cons (unbits y) nil) ..) (at level 200, x at level 0).

#[global] Open Scope bits_scope.

Definition example : list _ := input
00100
11110
10110
10111
10101
01111
00111
11100
10000
11001
00010
01010
.

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

Definition sum_bool_Z (xs : list bool) : Z :=
  fold_left (fun i (b : bool) => i + if b then 1 else -1)%Z xs 0%Z.

Fixpoint bits_to_N_ (acc : N) (xs : list bool) : N :=
  match xs with
  | [] => acc
  | x :: xs => bits_to_N_ (if x then acc * 2 + 1 else acc * 2) xs
  end.

Definition bits_to_N := bits_to_N_ 0.

Record PartOne := { gamma : list bool ; epsilon : list bool }.

Definition part_one (xs : list (list bool)) : PartOne :=
  let tmp := map (fun x => if (sum_bool_Z x <? 0)%Z then false else true) (transpose xs) in
  {| gamma := tmp ; epsilon := map negb tmp |}.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end.

Definition solve (xs : list (list bool)) : N :=
  let ans := part_one xs in
  bits_to_N (gamma ans) * bits_to_N (epsilon ans).

(* Compute solve example. *)

Definition head {A} (xs : list A) : option A :=
  match xs with
  | x :: _ => Some x
  | [] => None
  end.

Fixpoint brrr (n : nat) (switch : bool) (xs : list (list bool * list bool)) : list bool :=
  match n with
  | O => []
  | S n =>
    let bit := xorb switch (0 <=? sum_bool_Z (map_filter (fun '(x, _) => head x) xs))%Z in
    match map_filter (fun '(x, y) =>
      match x with
      | c :: x => if Bool.eqb bit c then Some (x, y) else None
      | _ => None
      end) xs
    with
    | [(_, x)] => x
    | xs => brrr n switch xs
    end
  end.

Definition brr switch xs := brrr (length xs) switch (map (fun x => (x, x)) xs).

Definition solve2 (xs : list (list bool)) : N :=
  let ogr := brr false xs in
  let csr := brr true xs in
  bits_to_N ogr * bits_to_N csr.

(* Compute solve2 example. *)
