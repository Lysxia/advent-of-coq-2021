From Coq Require Export Ascii String NArith.
From Coq Require Import List.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

#[global] Open Scope N_scope.

Notation b0 := false.
Notation b1 := true.

Infix "::" := String : string_scope.

Definition bits := list bool.

Definition hex_N_to_bits (n : N) : bits :=
  [ N.odd (n / 8) ; N.odd (n / 4) ; N.odd (n / 2) ; N.odd n ].

Definition hex_to_bits (c : ascii) : bits := hex_N_to_bits (
  if c =? "0" then  0 else
  if c =? "1" then  1 else
  if c =? "2" then  2 else
  if c =? "3" then  3 else
  if c =? "4" then  4 else
  if c =? "5" then  5 else
  if c =? "6" then  6 else
  if c =? "7" then  7 else
  if c =? "8" then  8 else
  if c =? "9" then  9 else
  if c =? "A" then 10 else
  if c =? "B" then 11 else
  if c =? "C" then 12 else
  if c =? "D" then 13 else
  if c =? "E" then 14 else
  if c =? "F" then 15 else 0)%char.

Fixpoint to_bits (s : string) : bits :=
  match s with
  | "" => []
  | c :: s => (hex_to_bits c ++ to_bits s)%list
  end%string.

Notation input s := (to_bits s%string) (only parsing).

Definition example := input "8A004A801A8002F478".
Definition example2 := input "620080001611562C8802118E34".
Definition example3 := input "C0015000016115A2E0802F182340".
Definition example4 := input "A0016C880162017C3686B18A3D4780".

Definition parser (A : Type) : Type :=
  forall R, (A -> bits -> N -> option R) -> bits -> N -> option R.

Definition run_parser {A} (p : parser A) (bs : bits) : option A :=
  p A (fun x _ _ => Some x) bs 0.

Definition onebit : parser bool := fun R k bs pos =>
  match bs with
  | [] => None
  | b :: bs => k b bs (N.succ pos)
  end.

Definition ret {A} (x : A) : parser A := fun R k bs => k x bs.

Definition bind {A B} (u : parser A) (c : A -> parser B) : parser B := fun R k =>
  u _ (fun x => c x _ k).

Notation "'let*' x ':=' u 'in' c" := (bind u (fun x => c)) (at level 200, x binder).

Definition fixed (n : N) : parser N :=
  N.iter n (fun c acc =>
    let* b := onebit in
    c (N.double acc + N.b2n b)) ret 0.

Definition get_pos : parser N := fun R k bs p => k p bs p.

Inductive packet :=
| Packet (ver : N) (typ : N) (pay : payload)
with payload :=
| Literal (_ : N)
| Operator (_ : list packet)
.

Definition repeat {A} (n : N) (p : parser A) : parser (list A) :=
  N.iter n (fun ps =>
    let* x := p in
    let* xs := ps in
    ret (x :: xs)) (ret []).

Definition fail {A} : parser A := fun R _ _ _ => None.

Definition while_bounded {A} (n : N) (p : parser (option A)) : parser (list A) :=
  N.iter (N.succ n) (fun ps =>
    let* ox := p in
    match ox with
    | None => ret []
    | Some x => let* xs := ps in ret (x :: xs)
    end) fail.

Fixpoint iter_list {A B} (n : list A) (f : B -> B) (x : B) : B :=
  match n with
  | [] => x
  | _ :: n => f (iter_list n f x)
  end.

Definition fix_consuming {A B} (f : (A -> parser B) -> (A -> parser B)) (x : A) : parser B :=
  fun _ k bs p =>
    iter_list bs f (fun _ => fail) x _ k bs p.

Definition fix_consuming' {A} (f : parser A -> parser A) : parser A :=
  fix_consuming (fun z _ => f (z tt)) tt.

Section Lit.

Context (__literal : N -> parser N).

Definition _literal (acc : N) : parser N :=
  let* b := onebit in
  let* h := fixed 4 in
  match b with
  | b0 => ret (acc * 16 + h)
  | b1 => __literal (acc * 16 + h)
  end.

End Lit.

Definition get_literal : parser N := fix_consuming _literal 0.

Section Packets.

Context (__packet : parser packet).

Definition _packet : parser packet :=
  let* ver := fixed 3 in
  let* typ := fixed 3 in
  if typ =? 4 then
    let* n := get_literal in
    ret (Packet ver typ (Literal n))
  else
    let* b := onebit in
    let* packs := match b with
      | b0 =>
        let* len := fixed 15 in
        let* pos := get_pos in
        while_bounded len
          (let* pos' := get_pos in
           match N.compare pos' (pos + len) with
           | Eq => ret None
           | Lt => let* x := __packet in ret (Some x)
           | Gt => fail
           end)
      | b1 =>
        let* len := fixed 11 in
        repeat len __packet
      end in
    ret (Packet ver typ (Operator packs)).

End Packets.

Definition get_packet : parser packet  := fix_consuming' _packet.

(* Compute (run_parser get_packet example). *)

Fixpoint sum_versions (p : packet) : N :=
  match p with
  | Packet v _ pl => v + sum_versions_payload pl
  end
with sum_versions_payload (pl : payload) : N :=
  match pl with
  | Literal _ => 0
  | Operator ps => fold_left (fun acc p => acc + sum_versions p) ps 0
  end.

Definition solve (bs : bits) : option N :=
  option_map sum_versions (run_parser get_packet bs).

(*
Compute solve example.
Compute solve example2.
Compute solve example3.
Compute solve example4.
*)

Module Import Ops.

Definition sum (xs : list N) :=
  fold_left N.add xs 0.

Definition product (xs : list N) :=
  fold_left N.mul xs 1.

Definition minimum (xs : list N) :=
  match xs with
  | [] => 0
  | x :: xs => fold_left N.min xs x
  end.

Definition maximum (xs : list N) :=
  match xs with
  | [] => 0
  | x :: xs => fold_left N.max xs x
  end.

Definition gt (xs : list N) :=
  match xs with
  | [x; y] => if y <? x then 1 else 0
  | _ => 0
  end.

Definition lt (xs : list N) :=
  match xs with
  | [x; y] => if x <? y then 1 else 0
  | _ => 0
  end.

Definition eq (xs : list N) :=
  match xs with
  | [x; y] => if x =? y then 1 else 0
  | _ => 0
  end.

End Ops.

Fixpoint eval (p : packet) : N :=
  match p with
  | Packet _ _ (Literal n) => n
  | Packet _ t (Operator ps) =>
    let args := map eval ps in
    let op :=
      if t =? 0 then sum
      else if t =? 1 then product 
      else if t =? 2 then minimum
      else if t =? 3 then maximum
      else if t =? 5 then gt
      else if t =? 6 then lt
      else (* t = 7 *) eq
    in op args
  end.

Definition solve2 (bs : bits) : option N :=
  option_map eval (run_parser get_packet bs).

Definition solve12 (bs : bits) : option (N * N) :=
  option_map (fun x => (sum_versions x, eval x)) (run_parser get_packet bs).

Definition example5 := input "C200B40A82".
Definition example6 := input "880086C3E88112".
Definition example7 := input "CE00C43D881120".

(*
Compute solve2 example5.
Compute solve2 example6.
Compute solve2 example7.
*)
