From Coq Require Export NArith List.

From stdpp Require Import gmap.

Set Implicit Arguments.

#[global] Open Scope N_scope.

Notation "'input' 'Player' '1' 'starting' 'position' ':' n1 'Player' '2' 'starting' 'position' ':' n2" := (n1%N, n2%N)
  (at level 200, n1 at level 0, only parsing).

Definition example := input
Player 1 starting position: 4
Player 2 starting position: 8
.

Record board := MkBoard
  { p1 : N
  ; p2 : N
  ; s1 : N
  ; s2 : N
  }.

Definition mk_board '((p1,p2) : N * N) : board :=
  {| p1 := p1 ; p2 := p2 ; s1 := 0 ; s2 := 0 |}.

#[global] Instance EqDecision_board : EqDecision board.
Proof.
  intros x y; hnf; decide equality; apply (decide _).
Defined.

#[global] Instance Countable_board : Countable board.
Proof.
  apply (inj_countable (A := N * N * N * N) (fun b => (p1 b, p2 b, s1 b, s2 b))
           (fun '(p1,p2,s1,s2) => Some (MkBoard p1 p2 s1 s2))).
  intros []; reflexivity.
Defined.

Definition advance (b : board) (n : N) : board :=
  let p1' := (p1 b + n - 1) mod 10 + 1 in
  {| p1 := p2 b
  ;  p2 := p1'
  ;  s1 := s2 b
  ;  s2 := s1 b + p1'
  |}.

Record board1 := MkBoard1
  { b1 : board
  ; rolls : N
  ; d : N
  }.

Definition step1 (b : board1) : board1 :=
  {| b1 := advance (b1 b) (3 * rolls b + 1)
  ;  rolls := 3 + rolls b
  ;  d := (d b + 3) mod 10
  |}.

Definition play1 i : board1 :=
  N.iter 2000 (fun go b => if 1000 <=? s2 (b1 b) then b else go (step1 b))
    (fun b => b (* should not happen *))
    {| b1 := mk_board i ; rolls := 0 ; d := 1 |}.

Definition solve i : N :=
  let b := play1 i in
  s1 (b1 b) * rolls b.

(* Compute let '(p1,p2):= example in play p1 p2. *)
(* Compute solve example. *)

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

Fixpoint _memo_fix (fuel : nat) {A R} `{Countable A}
  (r0 : R) (gf : endo (A -> state (gmap A R) R)) : A -> state (gmap A R) R :=
  fun x => Mk_state (fun s =>
    match lookup x s with
    | Some y => (s, y)
    | None =>
      let __memo_fix x := match fuel with O => ret r0 | S fuel => _memo_fix fuel r0 gf x end in
      let '(s, y) := run_state (gf __memo_fix x) s in
      (insert x y s, y)
    end).

Definition memo_fix (fuel : nat) {A R} `{Countable A}
  (r0 : R) (gf : endo (A -> state (gmap A R) R)) : A -> R :=
  fun x => snd (run_state (_memo_fix fuel r0 gf x) empty).

Fixpoint addwave (xs ys : list N) :=
  match xs, ys with
  | x :: xs, y :: ys => x + y :: addwave xs ys
  | nil, ys => ys
  | xs, nil => xs
  end.

Definition microwave (xs : list N) : list N :=
  addwave (addwave xs (0 :: xs)) (0 :: 0 :: xs).

Definition threedice : list (N * N) := Eval cbv in
  combine (3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil) (microwave (microwave (microwave (1 :: nil)))).

Definition sum_worlds (xs : list (N * N)) : N * N :=
  fold_left (fun '(x,y) '(x',y') => (x+x', y+y')) xs (0,0).

(* Starting from board [b], numbers of worlds in which each player wins *)
Definition __play2 {M} `{Monad M} : endo (board -> M (N * N)%type) := fun __play2 b =>
  if 21 <=? s2 b then ret (0, 1) else
    (* Weight and flip *)
    let wflip w '(v1, v2) := (v2 * w, v1 * w) in
    let* rs := traverse (fun '(d, w) => let* r := __play2 (advance b d) in ret (wflip w r))
                 threedice in
    ret (sum_worlds rs).

Definition _play2 : board -> N * N := memo_fix 42 (0, 0) __play2.
Definition play2 i := _play2 (mk_board i).

Definition solve2 i : N :=
  let '(v1, v2) := play2 i in
  if v1 <? v2 then v2 else v1.

(* Compute solve2 example. *)

Definition solve12 i := (solve i, solve2 i).
