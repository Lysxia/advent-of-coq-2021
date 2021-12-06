From Coq Require Export List NArith.
Import ListNotations.

#[global] Open Scope N_scope.

Notation "'input' x ',' .. ',' y" := (cons x .. (cons y nil) ..) (at level 200).

Definition example : list N := input
3,4,3,1,2
.

Fixpoint zip_with {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | x :: xs, y :: ys => f x y :: zip_with f xs ys
  | _, _ => nil
  end.

Definition one_vector (x : N) : list N :=
  repeat 0 (N.to_nat x) ++ 1 :: repeat 0 (8 - N.to_nat x).

Fixpoint input_to_vector (xs : list N) : list N :=
  match xs with
  | [] => [0; 0; 0; 0; 0; 0; 0; 0; 0]
  | x :: xs => zip_with N.add (one_vector x) (input_to_vector xs)
  end.

Fixpoint add_at (n : nat) (c : N) (xs : list N) : list N :=
  match n, xs with
  | _, [] => [] (* should not happen *)
  | O, x :: xs => x+c :: xs
  | S n, x :: xs => x :: add_at n c xs
  end.

Definition step (v : list N) : list N :=
  match v with
  | [] => [] (* should not happen *)
  | x0 :: v => add_at 6 x0 v ++ [x0]
  end.

Fixpoint steps (n : nat) (v : list N) : list N :=
  match n with
  | O => v
  | S n => steps n (step v)
  end.

Definition sum (xs : list N) := fold_left N.add xs 0.

Definition solve (xs : list N) : N :=
  sum (steps 80 (input_to_vector xs)).

(* Compute solve example. *)

Definition solve2 (xs : list N) : N :=
  sum (steps 256 (input_to_vector xs)).

Definition solve12 (xs : list N) : N * N :=
  (solve xs, solve2 xs).
