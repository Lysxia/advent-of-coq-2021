From Coq Require Export String Ascii List NArith Arith.
From Coq Require Import Permutation.

Set Implicit Arguments.

Import ListNotations.

#[global] Open Scope string_scope.
#[global] Open Scope N_scope.

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

Definition raw_signal : Type := string.
Definition signal : Type := list bool. (* length 7 *)

Fixpoint char_of (c : ascii) (w : string) : bool :=
  match w with
  | "" => false
  | cw :: w => Ascii.eqb c cw || char_of c w
  end.

Definition word_to_signal (w : raw_signal) : signal :=
  map (fun c => char_of c w) ["a"; "b"; "c"; "d"; "e"; "f"; "g"]%char.

Definition Line : Type := (list raw_signal * list raw_signal).

Definition input (s : string) : list Line :=
  let input_line l :=
    match words l with
    | [s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; vbar; t0; t1; t2; t3] =>
        if String.eqb "|" vbar then
          ([s0; s1; s2; s3; s4; s5; s6; s7; s8; s9], [t0; t1; t2; t3])
        else ([],[])
    | _ => ([],[])
    end in
  map input_line (lines s).

Definition example := Eval cbv in input
  "be cfbegad cbdgef fgaecd cgeb fdcge agebfd fecdb fabcd edb | fdgacbe cefdb cefbgd gcbe
edbfga begcd cbg gc gcadebf fbgde acbgfd abcde gfcbed gfec | fcgedb cgb dgebacf gc
fgaebd cg bdaec gdafb agbcfd gdcbef bgcad gfac gcb cdgabef | cg cg fdcagb cbg
fbegcd cbd adcefb dageb afcb bc aefdc ecdab fgdeca fcdbega | efabcd cedba gadfec cb
aecbfdg fbg gf bafeg dbefa fcge gcbea fcaegb dgceab fcbdga | gecf egdcabf bgf bfgea
fgeab ca afcebg bdacfeg cfaedg gcfdb baec bfadeg bafgc acf | gebdcfa ecba ca fadegcb
dbcfg fgd bdegcaf fgec aegbdf ecdfab fbedc dacgb gdcebf gf | cefg dcbef fcge gbcadfe
bdfegc cbegaf gecbf dfcage bdacg ed bedf ced adcbefg gebcd | ed bcgafe cdgba cbgef
egadfb cdbfeg cegd fecab cgb gbdefca cg fgcdab egfdb bfceg | gbdfcae bgc cg cgb
gcafb gcf dcaebfg ecagb gf abcdeg gaef cafbge fdbac fegbdc | fgae cfgab fg bagce".

Definition sum_with {A} (f : A -> N) : list A -> N :=
  fold_right (fun x => N.add (f x)) 0.

Definition count_1478 : list Line -> N :=
  sum_with (fun '(_, y) =>
    sum_with (fun s =>
      if ((String.length s =? 2) || (String.length s =? 3) ||
          (String.length s =? 4) || (String.length s =? 7))%nat%bool
      then 1 else 0) y).

Definition solve := count_1478.

(* Compute solve example. *)


(*
 aaaa
b    c
b    c
 dddd 
e    f
e    f
 gggg 

Number of digits where segment is active:
a 8
b 6
c 8
d 7
e 4
f 9
g 7

c occurs in the digit 1, and a doesn't
d occurs in the digit 4, and g doesn't
*)

Definition count (c : ascii) (xs : list raw_signal) : N :=
  sum_with (fun s => if char_of c s then 1 else 0) xs.

Definition occurs_in_1 (c : ascii) (xs : list raw_signal) : bool :=
  existsb (fun s => (String.length s =? 2)%nat && char_of c s)%bool xs.

Definition occurs_in_4 (c : ascii) (xs : list raw_signal) : bool :=
  existsb (fun s => (String.length s =? 4)%nat && char_of c s)%bool xs.

Definition decode (xs : list raw_signal) : list (ascii * ascii) :=
  map (fun c =>
    (c, let n := count c xs in
        if n =? 4 then "e"
        else if n =? 6 then "b"
        else if n =? 9 then "f"
        else if n =? 7 then
          if occurs_in_4 c xs then "d" else "g"
        else if n =? 8 then
          if occurs_in_1 c xs then "c" else "a"
        else "?")%N%char) ["a"; "b"; "c"; "d"; "e"; "f"; "g"]%char.

Definition lookup_char {A} (def : A) (c : ascii) (xs : list (ascii * A)) : A :=
  match List.find (fun w => c =? fst w)%char xs with
  | Some y => snd y
  | None => def
  end.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | "" => ""
  | c :: s => f c :: map_string f s
  end.

Definition decipher (d : list (ascii * ascii)) (xs : raw_signal) : raw_signal :=
  map_string (fun c => lookup_char "?"%char c d) xs.

Notation t := true (only parsing).
Notation f := false (only parsing).

Definition raw_signal_to_digit (s : raw_signal) : N :=
  match word_to_signal s with
  | [t;t;t;f;t;t;t] => 0
  | [f;f;t;f;f;t;f] => 1
  | [t;f;t;t;t;f;t] => 2
  | [t;f;t;t;f;t;t] => 3
  | [f;t;t;t;f;t;f] => 4
  | [t;t;f;t;f;t;t] => 5
  | [t;t;f;t;t;t;t] => 6
  | [t;f;t;f;f;t;f] => 7
  | [t;t;t;t;t;t;t] => 8
  | [t;t;t;t;f;t;t] => 9
  | _ => 10000000 (* Blow up if wrong *)
  end.

Fixpoint _from_decimal (d : N) (s : list N) : N :=
  match s with
  | [] => d
  | c :: s => _from_decimal (d * 10 + c) s
  end%list.

Definition from_decimal : list N -> N := _from_decimal 0.

Definition outsig_to_num (s : list raw_signal) : N :=
  from_decimal (map raw_signal_to_digit s).

Definition decipher_line '((x,y) : Line) : N :=
  let d := decode x in
  let y := map (decipher d) y in
  outsig_to_num y.

Definition example1 := input "acedgfb cdfbe gcdfa fbcad dab cefabd cdfgeb eafb cagedb ab | cdfeb fcadb cdfeb cdbaf".

(* Compute map decipher_line example1. *)

Definition solve2 : list Line -> N :=
  sum_with decipher_line.

(* Compute solve2 example. *)

Definition solve12 (xs : list Line) : N * N :=
  (solve xs, solve2 xs).

(* Spec, no proofs *)

Definition digits : list raw_signal :=
  ["cf"; "acdeg"; "acdfg"; "bcdf"; "abdfg"; "abdefg"; "acf"; "abcdefg"; "abcdfg"]%string.

(* The seven segments *)
Definition segs : list ascii := ["a"; "b"; "c"; "d"; "e"; "f"; "g"]%char.

Definition mapping {A B} (xs : list A) (ys : list B) (x : A) (y : B) :=
  List.In (x, y) (List.combine xs ys).

Fixpoint Forall2_string (F : ascii -> ascii -> Prop) (s1 s2 : string) : Prop :=
  match s1, s2 with
  | "", "" => True
  | c1 :: s1, c2 :: s2 => F c1 c2 /\ Forall2_string F s1 s2
  | _, _ => False
  end.

Definition Permutation_string (s1 s2 : string) : Prop :=
  Permutation (list_ascii_of_string s1) (list_ascii_of_string s2).

Definition index {A} (xs : list A) (n : nat) (x : A) : Prop :=
  (n < length xs)%nat /\ nth n xs x = x.

(* A well-formed input line [l] is related to the "canonical" representation of segments
   [segs] and [digits] as follows. *)
Record LineSpec (l : Line) : Type :=
  { (* (1) The display segments are scrambled *)
    ssegs : list ascii  (* scrambled display lines *)
  ; ssegs_P : Permutation segs ssegs

    (* (2) We apply the segment scrambling to the digits *)
  ; sdigits : list raw_signal
  ; sdigits_P : Forall2 (Forall2_string (mapping segs ssegs)) digits sdigits

    (* (3) The digits are shuffled *)
  ; ssdigits : list raw_signal
  ; ssdigits_P : Permutation sdigits ssdigits

    (* (4) The order of segments in each digit is shuffled,
       this yields the first half of our input. *)
  ; sssdigits : list raw_signal := fst l
  ; sssdigits_P : Forall2 Permutation_string ssdigits sssdigits

    (* (5) The second half of the input is 4 digits *)
  ; outs : list nat
  ; outs_length : length outs = 4%nat

    (* (6) The digits are mapped to their 7-segment display
       (this implies the elements of [outs] are actually digits) *)
  ; douts : list raw_signal
  ; douts_X : Forall2 (index digits) outs douts

    (* (7) Apply the segment scrambling (like (2)) *)
  ; sdouts : list raw_signal
  ; sdouts_P : Forall2 (Forall2_string (mapping segs ssegs)) douts sdouts

    (* (8) The segments are shuffled, that's the second half of the input. *)
  ; ssdouts : list raw_signal := snd l
  ; ssdouts_P : Forall2 Permutation_string sdouts ssdouts
  }.

(* [decipher_line] reconstructs the 4 digits in [outs]. *)
Theorem decipher_correct (l : Line) (ls : LineSpec l)
  : decipher_line l = from_decimal (map N.of_nat (outs ls)).
Proof.
  (* Good luck *)
Abort.
