From Coq Require Export ZArith.
From stdpp Require Import gmap.

Set Implicit Arguments.

#[global] Open Scope Z_scope.

Declare Custom Entry alu.

Module Syntax.

Inductive op := Add | Mul | Div | Mod | Eql | Inp.  (* Inp ignores register 2 *)
Inductive reg := x | y | z | w | imm (_ : Z).
Coercion imm : Z >-> reg.
Record instr := Mk_instr
  { iop : op
  ; ir1 : reg
  ; ir2 : reg
  }.

Notation "'input' a1 .. an" := (cons a1 .. (cons an nil) ..)
  (at level 200, a1 custom alu, an custom alu).

Notation "'add' r1 r2" := (Mk_instr Add r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'mul' r1 r2" := (Mk_instr Mul r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'div' r1 r2" := (Mk_instr Add r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'mod' r1 r2" := (Mk_instr Mod r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'eql' r1 r2" := (Mk_instr Eql r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'inp' r" := (Mk_instr Inp r x)
  (in custom alu at level 1, r constr at level 0).

Notation "`` x" := x
  (at level 10, x custom alu, only parsing).

Definition example := input
inp w
mul x 0
add x z
mod x 26
div z 1
add x 11
eql x w
eql x 0
mul y 0
add y 25
mul y x
add y 1
mul z y
mul y 0
add y w
add y -8
mul y x
add z y
.

Definition ocons {A} (x : A) (xs : option (list A)) : option (list A) :=
  option_map (cons x) xs.

Fixpoint recognize (xs : list instr) : option (list (Z * Z * Z)) :=
  match xs with
  |    `` inp w
    :: `` mul x 0
    :: `` add x z
    :: `` mod x 26
    :: `` div z (imm A)
    :: `` add x (imm B)
    :: `` eql x w
    :: `` eql x 0
    :: `` mul y 0
    :: `` add y 25
    :: `` mul y x
    :: `` add y 1
    :: `` mul z y
    :: `` mul y 0
    :: `` add y w
    :: `` add y (imm C)
    :: `` mul y x
    :: `` add z y
    :: xs => option_map (cons (A,B,C)) (recognize xs)
  | nil => Some nil
  | _ => None
  end.

End Syntax.

Definition step '((div_z, add_x, add_y) : Z * Z * Z) (rw : Z) (rz : Z) : Z :=
  let rx := (rz mod 26) + add_x in
  let rz := rz / div_z in
  if rw =? rx then rz else rz * 26 + rw + add_y.

(* Recursion and memoization *)

Definition endo (X : Type) : Type := (X -> X).

Class Monad M : Type :=
  { ret : forall {A}, A -> M A
  ; bind : forall {A B}, M A -> (A -> M B) -> M B
  }.

Declare Scope monad_scope.
#[global] Open Scope monad_scope.

Notation "'let*' x ':=' u 'in' v" := (bind u (fun x => v)) (at level 200) : monad_scope.

Fixpoint traverse {M} `{Monad M} {A B} (f : A -> M B) (xs : list A) : M (list B) :=
  match xs with
  | [] => ret []
  | x :: xs =>
    let* y := f x in
    let* ys := traverse f xs in
    ret (y :: ys)
  end.

Record identity (A : Type) : Type := Mk_identity { run_identity : A }.

Instance Monad_identity : Monad identity :=
  {| ret _ x := Mk_identity x
  ;  bind _ _ u k := k (run_identity u) 
  |}.

Fixpoint naive_fix (fuel : nat) {A R} (r0 : R) (gf : endo (A -> identity R)) : A -> R :=
  fun x =>
    run_identity (gf (fun x => Mk_identity match fuel with
        | O => r0
        | S fuel => naive_fix fuel r0 gf x
        end) x).

Record state (S A : Type) : Type := Mk_state { run_state : S -> S * A }.

Instance Monad_state {S} : Monad (state S) :=
  {| ret _ x := Mk_state (fun s => (s, x))
  ;  bind _ _ u k := Mk_state (fun s =>
       let '(s, x) := run_state u s in
       run_state (k x) s) |}.

Definition memom (A R : Type) `{Countable A} : Type -> Type := state (gmap A R).

Fixpoint _memo_fix (fuel : nat) {A B R} `{Countable A}
  (r0 : R) (gf : endo (A -> B -> state (gmap A R) R)) : A -> B -> state (gmap A R) R :=
  fun x b => Mk_state (fun s =>
    match lookup x s with
    | Some y => (s, y)
    | None =>
      let __memo_fix x b := match fuel with O => ret r0 | S fuel => _memo_fix fuel r0 gf x b end in
      let '(s, y) := run_state (gf __memo_fix x b) s in
      (insert x y s, y)
    end).

Definition memo_fix (fuel : nat) {A B R} `{Countable A}
  (r0 : R) (gf : endo (A -> B -> state (gmap A R) R)) : A -> B -> R :=
  fun x b => snd (run_state (_memo_fix fuel r0 gf x b) empty).

Fixpoint find' {A B} (xs : list A) (f : A -> option B) : option B :=
  match xs with
  | nil => None
  | x :: xs =>
    match f x with
    | None => find' xs f
    | Some y => Some y
    end
  end.

Fixpoint findM {M} `{Monad M} {A B} (xs : list A) (f : A -> M (option B)) : M (option B) :=
  match xs with
  | nil => ret None
  | x :: xs =>
    let* o := f x in
    match o with
    | None => findM xs f
    | Some y => ret (Some y)
    end
  end.

Notation "'let?' x ':=' xs 'in' f" := (find' xs (fun x => f))
  (at level 200, x pattern).

Notation "'let?*' x ':=' xs 'in' f" := (findM xs (fun x => f))
  (at level 200, x pattern).

Definition _search {M} `{Monad M} (digits : list Z)
  : endo (Z * N -> list (Z -> Z -> Z) -> M (option (list Z))) := fun _search '(rz, n) ts =>
  match ts with
  | nil => if rz =? 0 then ret (Some nil) else ret None
  | t :: ts =>
    let?* d := digits in
    let rz := t d rz in
    let* r := _search (rz, N.succ n) ts in
    ret (option_map (cons d) r)
  end.

Definition decimal (xs : list Z) : Z :=
  fold_left (fun acc d => acc * 10 + d) xs 0.

Definition search (digits : list Z) (ts : list (Z -> Z -> Z)) : option Z :=
  let r := memo_fix (length ts) None (_search digits) (0,0%N) ts in
  option_map decimal r.

Export Syntax.

Definition solve (i : list instr) : option Z :=
  match recognize i with
  | None => None
  | Some ts => search (9::8::7::6::5::4::3::2::1::nil) (map step ts)
  end.

(*
Compute
  let step x d z :=
    if (z =? 0) && (d =? x) then 0 else 1 in
  search (1::0::nil) (map step (1::0::1::1::1::1::1::1::1::1::1::1::1::1::1::1::1::1::nil)).
*)
(* Compute solve example. *)
