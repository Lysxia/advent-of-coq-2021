From Coq Require Export List NArith.
From Coq Require Import Lia.

Import ListNotations.

#[global] Open Scope N_scope.

Notation "'input' x .. y" := (cons x .. (cons y nil) ..) (at level 200, x at level 0, only parsing).

Definition example : list N := input
199
200
208
210
200
207
240
269
260
263
.

(* Part 1 *)

(* Count the number of consecutive increasing pairs *)
Fixpoint count_increases_ (xs : list N) (acc : N) : N :=
  match xs with
  | [] | _ :: [] => acc
  | x :: (y :: _) as xs =>
    count_increases_ xs (if x <? y then 1 + acc else acc)
  end.

Definition count_increases (xs : list N) : N := count_increases_ xs 0.

Definition solve : list N -> N := count_increases.

(* Compute solve example.  (* 7 *) *)

(* Seems as simple as could be. *)

(* Part 2 *)

(* Count the number of consecutive increasing sums in a sliding window of length 3 *)
Fixpoint count_increases2_ (xs : list N) (acc : N) : N :=
  match xs with
  | x :: (_ :: _ :: y :: _) as xs =>
    count_increases2_ xs (if x <? y then 1 + acc else acc)
  | _ => acc
  end.

Definition count_increases2 (xs : list N) : N := count_increases2_ xs 0.

Definition solve2 : list N -> N := count_increases2.

(* Compute solve2 example. (* 5 *) *)

Definition solve12 (i : list N) : N * N := (solve i, solve2 i).

(* This solution avoids computing the sums. We can prove that it's equivalent to a more literal
   solution that does the sums. *)

Fixpoint sum3 (xs : list N) : list N :=
  match xs with
  | x :: (y :: z :: _) as xs => (x + y + z) :: sum3 xs
  | _ => []
  end.

Theorem count_increases2_correct xs : count_increases (sum3 xs) = count_increases2 xs.
Proof.
  unfold count_increases, count_increases2. generalize 0.
  induction xs as [ | x xs IH]; cbn [sum3]; intros n; [ reflexivity | ].
  destruct xs as [ | y [ | z [ | t xs_ ] ] ]; [ reflexivity .. | ].
  change
    ( count_increases_ (sum3 (y :: z :: t :: xs_)) (if x + y + z <? y + z + t then 1 + n else n)
    = count_increases2_ (y :: z :: t :: xs_) (if x <? t then 1 + n else n)).
  destruct (N.ltb_spec x t);
  destruct (N.ltb_spec (x + y + z) (y + z + t)); [ apply IH | lia | lia | apply IH ].
Qed.
