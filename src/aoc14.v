From Coq Require Export NArith Ascii String.
From stdpp Require Import gmap.

Declare Custom Entry arr.

Notation "'input' i j1 .. jn" := (i%string, cons j1 .. (cons jn nil) ..)
  (at level 200, i at level 0, j1 custom arr, jn custom arr).

Notation "p -> q" := (p%string, q%char)
  (in custom arr at level 1, p constr at level 0, q constr at level 0).

Definition Input : Type := string * list (string * ascii).

Definition example : Input := input
"NNCB"

"CH" -> "B"
"HH" -> "N"
"CB" -> "H"
"NH" -> "C"
"HB" -> "C"
"HC" -> "B"
"HN" -> "C"
"NN" -> "C"
"BH" -> "H"
"NC" -> "B"
"NB" -> "B"
"BN" -> "B"
"BB" -> "N"
"BC" -> "B"
"CC" -> "N"
"CN" -> "C"
.

Infix "::" := String : string_scope.

#[global] Open Scope N_scope.

Definition pairmap (xs : list (string * ascii)) : gmap (ascii * ascii) ascii :=
  fold_left (fun m '(x, y) =>
    match x with
    | (x1 :: x2 :: "")%string => insert (x1,x2) y m
    | _ => m
    end) xs empty.

Fixpoint _occs (z : list ascii) : gmap (ascii * ascii) N :=
  match z with
  | nil | _ :: nil => empty
  | c1 :: (c2 :: _) as z =>
    let incr o := match o with
      | None => Some 1%N
      | Some n => Some (N.succ n)
      end in
    partial_alter incr (c1, c2) (_occs z)
  end.

Definition occ (s : string) : (list ascii * gmap (ascii * ascii) N) :=
  let z := list_ascii_of_string s in
  let ends := match z with
              | c1 :: c2 :: z' => c1 :: List.last z' c2 :: nil
              | c1 :: nil => c1 :: nil
              | nil => nil
              end in
  (ends, _occs z).

Definition Pairs : Type := gmap (ascii * ascii) N.

Definition incrmap {A} `{Countable A} (a : A) (n : N) : gmap A N -> gmap A N :=
  partial_alter (fun i => Some
    match i with
    | Some i => i + n
    | None => n
    end) a.

Definition step_pairs (trans : gmap (ascii * ascii) ascii) (pairs : Pairs) : Pairs :=
  let go m '((a, b), n) :=
        match lookup (a, b) trans with
        | None => incrmap (a, b) n m
        | Some c => incrmap (a, c) n (incrmap (c, b) n m)
        end in
  fold_left go (map_to_list pairs) empty.

Definition steps_pairs (n : N) (trans : gmap (ascii * ascii) ascii) : Pairs -> Pairs :=
  N.iter n (step_pairs trans).

Definition count (extra : list ascii) (pairs : Pairs) : gmap ascii N :=
  let extra' := fold_left (fun m c => incrmap c 1 m) extra empty in
  let pairs' := 
    fold_left (fun m '((a, b), n) => incrmap a n (incrmap b n m)) (map_to_list pairs) extra' in
  fmap N.div2 pairs'.

Fixpoint max_by {A} (leb : A -> A -> bool) (a : A) (xs : list A) : A :=
  match xs with
  | nil => a
  | x :: xs => max_by leb (if leb a x then x else a) xs
  end.

Definition min_by {A} (leb : A -> A -> bool) := max_by (fun x y => leb y x).

Definition min_max (z : gmap ascii N) : N * N :=
  let z := map snd (map_to_list z) in
  match z with
  | n0 :: z => (min_by N.leb n0 z, max_by N.leb n0 z)
  | nil => (0, 0)
  end.

Definition run (n : N) '((ini, trans) : Input) :=
  let trans := pairmap trans in
  let '(extra, pairs) := occ ini in
  let pairs := steps_pairs n trans pairs in
  (extra, pairs).

Definition _solve (n : N) (x : Input) : N :=
  let '(extra, pairs) := run n x in
  let cc := count extra pairs in
  let '(mini, maxi) := min_max cc in
  maxi - mini.

Definition solve := _solve 10.
Definition solve2 := _solve 40.
Definition solve12 x := (solve x, solve2 x).

(* Compute solve example. *)
