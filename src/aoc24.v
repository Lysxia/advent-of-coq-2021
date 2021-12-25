From Coq Require Export ZArith.
From stdpp Require Import gmap lexico.

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
  (at level 200, a1 custom alu, an custom alu, only parsing).

Notation "'add' r1 r2" := (Mk_instr Add r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'mul' r1 r2" := (Mk_instr Mul r1%Z r2%Z)
  (in custom alu at level 1, r1 constr at level 0, r2 constr at level 0).
Notation "'div' r1 r2" := (Mk_instr Div r1%Z r2%Z)
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

Definition step '((div_z, add_x, add_y) : Z * Z * Z) (rw : Z) (rz : Z) : option Z :=
  if (rz <? 0) || (div_z =? 0) then None else Some
  ( let rx := (rz mod 26) + add_x in
    let rz := Z.quot rz div_z in
    if rx =? rw then rz else rz * 26 + rw + add_y).

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

(* [log_lt n b k = true] if [k / b^n = 0] *)
Fixpoint log_lt (n : nat) (b k : Z) : bool :=
  (k =? 0) ||
  match n with
  | O => false
  | S n => log_lt n b (k / b)
  end.

Definition _search {M} `{Monad M} (digits : list Z)
  : endo (Z * N -> list (Z -> Z -> option Z) -> M (option (list Z))) := fun _search '(rz, n) ts =>
  match ts with
  | nil => if rz =? 0 then ret (Some nil) else ret None
  | t :: ts =>
    let?* d := digits in
    match t d rz with
    | None => ret None
    | Some rz =>
      if log_lt (13 - N.to_nat n) 26 rz then
        let* r := _search (rz, N.succ n) ts in
        ret (option_map (cons d) r)
      else
        ret None
    end
  end.

Definition decimal (xs : list Z) : Z :=
  fold_left (fun acc d => acc * 10 + d) xs 0.

Definition search (digits : list Z) (ts : list (Z -> Z -> option Z)) : option Z :=
  let r := memo_fix (length ts) None (_search digits) (0,0%N) ts in
  option_map decimal r.

Export Syntax.

Definition solve (i : list instr) : option Z :=
  match recognize i with
  | None => None
  | Some ts => search (9::8::7::6::5::4::3::2::1::nil) (map step ts)
  end.

Definition solve2 (i : list instr) : option Z :=
  match recognize i with
  | None => None
  | Some ts => search (1::2::3::4::5::6::7::8::9::nil) (map step ts)
  end.

Definition solve12 i := (solve i, solve2 i).

(* Compute solve example. *)

Fixpoint compile (xs : list (Z * Z * Z)) : list instr :=
  match xs with
  | nil => nil
  | (A,B,C) :: xs =>
       `` inp w
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
    :: compile xs
  end.

Ltac destructall :=
  repeat lazymatch goal with
  | [ |- context [match ?u with _ => _ end]] => destruct u; try discriminate
  end.

Lemma compile_recognize xs ys : Some ys = recognize xs -> xs = compile ys.
Proof.
  revert xs ys; fix SELF 1; intros [ | x xs] ys; cbn [recognize]; destructall.
  { injection 1; intros ->; reflexivity. }
  specialize (SELF xs).
  destruct (recognize xs) as [ zs | ]; [ | discriminate].
  specialize (SELF zs eq_refl).
  cbn [option_map]; injection 1; intros ->.
  cbn.
  rewrite SELF. reflexivity.
Qed.

Lemma recognize_compile xs : Some xs = recognize (compile xs).
Proof.
  induction xs as [ | x xs IH ]; [ reflexivity | destruct x as [[A B] C] ]; cbn.
  rewrite <- IH; reflexivity.
Qed.

Set Primitive Projections.
Record regs := Mk_regs
  { get_w : Z
  ; get_x : Z
  ; get_y : Z
  ; get_z : Z
  }.

Definition get_reg (r : reg) : regs -> Z :=
  match r with
  | imm v => fun _ => v
  | w => get_w
  | x => get_x
  | y => get_y
  | z => get_z
  end.

Definition set_reg (r : reg) (v : Z) (rr : regs) : option regs :=
  let '(Mk_regs rw rx ry rz) := rr in
  match r with
  | imm _ => None
  | w => Some (Mk_regs v rx ry rz)
  | x => Some (Mk_regs rw v ry rz)
  | y => Some (Mk_regs rw rx v rz)
  | z => Some (Mk_regs rw rx ry v)
  end.

Arguments set_reg r /.

Definition alu_div (x y : Z) : option Z :=
  if y =? 0 then None else Some (Z.quot x y).

Definition alu_mod (x y : Z) : option Z :=
  if (x <? 0) || (y <=? 0) then None else Some (Z.modulo x y).

Definition alu_eql (x y : Z) : Z :=
  if x =? y then 1 else 0.

Definition alu (t : instr) (is : list Z) (rr : regs) : option (list Z * regs) :=
  let no_input := option_map (fun x => (is, x)) in
  let evalop (o : Z -> Z -> option Z) :=
    let r1 := ir1 t in let r2 := ir2 t in
    mbind (fun v => set_reg r1 v rr) (o (get_reg r1 rr) (get_reg r2 rr)) in
  let tevalop (o : Z -> Z -> Z) := evalop (fun x y => Some (o x y)) in
  match iop t with
  | Add => no_input (tevalop Z.add)
  | Mul => no_input (tevalop Z.mul)
  | Div => no_input (evalop alu_div)
  | Mod => no_input (evalop alu_mod)
  | Eql => no_input (tevalop alu_eql)
  | Inp =>
    match is with
    | nil => None
    | v :: is => option_map (fun x => (is, x)) (set_reg (ir1 t) v rr)
    end
  end.

Fixpoint alus (ts : list instr) (is : list Z) (rr : regs) : option Z :=
  match ts with
  | nil => Some (get_z rr)
  | t :: ts =>
    match alu t is rr with
    | None => None
    | Some (is, rr) => alus ts is rr
    end
  end.

Fixpoint steps (ts : list (Z * Z * Z)) (is : list Z) (rz : Z) : option Z :=
  match ts, is with
  | nil, _ => Some rz
  | t :: ts, i :: is =>
    match step t i rz with
    | None => None
    | Some rz => steps ts is rz
    end
  | _ :: _, nil => None
  end.

Lemma alus_unfold t ts is rr
  : alus (t :: ts) is rr
  = match alu t is rr with
    | None => None
    | Some (is, rr) => alus ts is rr
    end.
Proof. reflexivity. Qed.

Lemma steps_correct ts is rr : steps ts is (get_z rr) = alus (compile ts) is rr.
Proof.
  revert is rr; induction ts as [| t ts IH]; cbn; [ reflexivity | intros is rr ].
  destruct is as [| i is], t as [[A B] C]; [ reflexivity | ].
  do 4 (rewrite alus_unfold; cbn - [alus]).
  rewrite Z.mul_0_r, Z.add_0_l.
  unfold alu_mod. destruct (get_z _ <? 0); [ reflexivity | ].
  cbn - [alus].
  do 1 (rewrite alus_unfold; cbn - [alus]).
  unfold alu_div. destruct (A =? 0); [ reflexivity | ]. cbn - [alus].
  do 13 (rewrite alus_unfold; cbn - [alus]).
  rewrite !Z.mul_0_r, !Z.add_0_l.
  unfold alu_eql. destruct (_ =? _); cbn.
  { rewrite !Z.mul_0_r, Z.add_0_l, Z.add_0_r, Z.mul_1_r. apply (IH _ (Mk_regs _ _ _ _)). }
  { rewrite !Z.mul_1_r, Z.add_assoc. apply (IH _ (Mk_regs _ _ _ _)). }
Qed.

Fixpoint evals (ts : list (Z -> Z -> option Z)) (ws : list Z) (rz : Z) : option Z :=
  match ts, ws with
  | t :: ts, rw :: ws =>
    match t rw rz with
    | Some rz => evals ts ws rz
    | None => None
    end
  | _ :: _, nil => None
  | nil, _ => Some rz
  end.

Lemma evals_steps ts ws rz : evals (map step ts) ws rz = steps ts ws rz.
Proof.
  revert ws rz; induction ts as [|t ts IH]; intros; cbn; [ reflexivity | ].
  destruct ws as [|rw ws]; [ reflexivity | ].
  destruct step; auto.
Qed.

Definition smallest {A} (r : relation A) (f : A -> Prop) (x : A) : Prop :=
  f x /\ (forall y, f y -> r x y).

Definition smallest_lexico {A} `{Lexico A} := smallest (lexico (A := A)).
Definition greatest_lexico {A} `{Lexico A} := smallest (fun x y : A => lexico y x).

Definition is_digit (x : Z) : Prop := elem_of x (1::2::3::4::5::6::7::8::9::nil).

Theorem solve_correct i ans : solve i = Some ans <->
  exists i0 res,
    i = compile i0 /\
    ans = decimal res /\ Forall is_digit res /\
    greatest_lexico (fun res' => steps i0 res' 0 = Some 0) res.
Proof.
Abort.

Theorem solve2_correct i ans : solve i = Some ans <->
  exists i0 res,
    i = compile i0 /\
    ans = decimal res /\ Forall is_digit res /\
    smallest_lexico (fun res' => steps i0 res' 0 = Some 0) res.
Proof.
Abort.
