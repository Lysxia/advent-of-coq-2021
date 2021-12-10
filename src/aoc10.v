From Coq Require Export Ascii String NArith.
From Coq Require Import List Arith.

Import ListNotations.

Set Implicit Arguments.

#[global] Open Scope string_scope.

Infix "::" := String.String.

Fixpoint _rev_string (r s : string) : string :=
  match s with
  | "" => r
  | c :: s => _rev_string (c :: r) s
  end.

Definition rev_string : string -> string := _rev_string "".

Definition is_empty (w : string) : bool :=
  match w with
  | "" => true
  | _ => false
  end.

Fixpoint _split_on (c0 : ascii) (w s : string) : list string :=
  match s with
  | "" => if is_empty w then [] else [rev_string w]
  | c :: s =>
    if Ascii.eqb c0 c then
      if is_empty w then _split_on c0 w s else rev_string w :: _split_on c0 "" s
    else
      _split_on c0 (c :: w) s
  end.

(* Drops empty words! *)
Definition split_on (c0 : ascii) : string -> list string := _split_on c0 "".

Definition words : string -> list string := split_on " ".
Definition lines : string -> list string := split_on "010".

Definition input : string -> list string := lines.

Definition example := input
"[({(<(())[]>[[{[]{<()<>>
[(()[<>])]({[<{<<[]>>(
{([(<{}[<>[]}>{[]{[(<()>
(((({<>}<{<{<>}{[]{[]{}
[[<[([]))<([[{}[[()]]]
[{[{({}]{}}([{[{{{}}([]
{<[[]]>}<{[{[{[]{()[[[]
[<(<(<(<{}))><([]([]()
<{([([[(<>()){}]>(<<{{
<{([{{}}[<[[[<>{}]]]>[]]".

Inductive Result : Type :=
| Illegal (c : ascii)
| Valid (z : list ascii)
.

Fixpoint _check (z : list ascii) (s : string) : Result :=
  match s with
  | "" => Valid z
  | c :: s =>
    let pop (c' : ascii) :=
      match z with
      | (cz :: z)%list => if (c' =? cz)%char then _check z s else Illegal c
      | _ => Illegal c
      end in
    if ((c =? "(") || (c =? "[") || (c =? "{") || (c =? "<"))%char%bool then
      _check (c :: z) s
    else if (c =? ")")%char then pop "("%char
    else if (c =? "]")%char then pop "["%char
    else if (c =? "}")%char then pop "{"%char
    else if (c =? ">")%char then pop "<"%char
    else Illegal  c
  end.

Definition check := _check [].

Definition sum_with {A} (f : A -> N) : list A -> N :=
  fold_right (fun x => N.add (f x)) 0%N.

Definition score (r : Result) : N :=
  match r with
  | Valid _ => 0
  | Illegal c =>
    if c =? ")" then 3
    else if c =? "]" then 57
    else if c =? "}" then 1197
    else if c =? ">" then 25137
    else 0 (* Should not happen *)
  end%char%N.

Definition solve : list string -> N :=
  sum_with (fun l => score (check l)).

(* Compute solve example. *)

Definition score2 (z : list ascii) : N :=
  fold_left (fun a c =>
    5 * a
    + if c =? "(" then 1
      else if c =? "[" then 2
      else if c =? "{" then 3
      else if c =? "<" then 4
      else 0)%char%N z 0%N.

Fixpoint minimum1 (x : N) (xs : list N) : N :=
  match xs with
  | [] => x
  | y :: xs => minimum1 (if (x <=? y)%N then x else y) xs 
  end%list.

Definition minimum (xs : list N) : option N :=
  match xs with
  | [] => None
  | x :: xs => Some (minimum1 x xs)
  end%list.

Fixpoint _split (x : N) (l r xs : list N) : list N * list N :=
  match xs with
  | [] => (l, r)
  | y :: xs =>
    if (y <=? x)%N then _split x (y :: l) r xs else _split x l (y :: r) xs
  end%list.

Definition split (x : N) (xs : list N) := _split x [] [] xs.

Fixpoint kth (fuel : list N) (k : nat) (xs : list N) : option N :=
  match fuel with
  | [] => None
  | _ :: fuel =>
    match xs with
    | [] => None
    | x :: xs =>
      let '(l, r) := split x xs in
      let nl := length l in
      match Nat.compare k nl with
      | Eq => Some x
      | Lt => kth fuel k l
      | Gt => kth fuel (k - nl - 1) r
      end
    end
  end%list.

Definition median (xs : list N) : option N :=
  kth xs (Nat.div2 (length xs)) xs.

Definition dummydefault (x : option N) : N :=
  match x with
  | Some x => x
  | None => 0
  end.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end%list.

Definition unValid (r : Result) : option (list ascii) :=
  match r with
  | Illegal _ => None
  | Valid z => Some z
  end.

Definition solve2 (xs : list string) : N :=
  dummydefault (median (map score2 (map_filter (fun l => unValid (check l)) xs))).

(* Compute solve2 example. *)

(* [solve12] factors the common logic of [check] in [solve] and [solve2]. *)
Definition solve12 (xs : list string) : N * N :=
  let xs := map check xs in
  (sum_with score xs, dummydefault (median (map score2 (map_filter unValid xs)))).

(**)

Lemma sum_with_map {A B} (f : A -> B) (g : B -> N) xs
  : sum_with g (map f xs) = sum_with (fun x => g (f x)) xs.
Proof.
  unfold sum_with; generalize 0%N.
  induction xs; intros; cbn; congruence.
Qed.

Lemma map_filter_map {A B C} (f : A -> B) (g : B -> option C) xs
  : map_filter g (map f xs) = map_filter (fun x => g (f x)) xs.
Proof.
  induction xs as [ | x xs IH ]; cbn; [ | destruct (g (f x))]; cbn; congruence.
Qed.

Lemma solve12Correct xs : solve12 xs = (solve xs, solve2 xs).
Proof.
  unfold solve12; cbn. rewrite sum_with_map, map_filter_map. reflexivity.
Qed.
