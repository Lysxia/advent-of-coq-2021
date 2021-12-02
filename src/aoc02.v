From Coq Require Export ZArith List.
Import ListNotations.

#[global] Open Scope Z_scope.

Inductive cmd :=
| forward
| up
| down
.

Declare Custom Entry aoc02.

Notation "'input' x .. y" := (cons x .. (cons y nil) ..) (at level 200, x custom aoc02, y custom aoc02, only parsing).
Notation "x y" := (x, y) (in custom aoc02 at level 0, x constr at level 0, y constr at level 0).

Definition example := input
forward 5
down 5
forward 8
up 3
down 8
forward 2
.

(* Part One *)

Definition position : Type := Z * Z.

Definition eval1 (c : cmd) (n : Z) '((hpos, zpos) : position) : position :=
  match c with
  | forward => (hpos + n, zpos)
  | up   => (hpos, zpos - n)
  | down => (hpos, zpos + n)
  end.

Fixpoint eval (xs : list (cmd * Z)) (current : position) : position :=
  match xs with
  | [] => current
  | (c, n) :: xs => eval xs (eval1 c n current)
  end.

Definition solve (xs : list (cmd * Z)) : Z :=
  let '(hpos, zpos) := eval xs (0, 0) in
  hpos * zpos.

(* Compute solve example. *)

(* Part Two *)

Definition position_2 : Type := Z * Z * Z.

Definition eval1_2 (c : cmd) (n : Z) '((hpos, zpos, aim) : position_2) : position_2 :=
  match c with
  | forward => (hpos + n, zpos + n * aim, aim)
  | up => (hpos, zpos, aim - n)
  | down => (hpos, zpos, aim + n)
  end.

Fixpoint eval_2 (xs : list (cmd * Z)) (current : position_2) : position_2 :=
  match xs with
  | [] => current
  | (c, n) :: xs => eval_2 xs (eval1_2 c n current)
  end.

Definition solve2 (xs : list (cmd * Z)) : Z :=
  let '(hpos, zpos, _aim) := eval_2 xs (0, 0, 0) in
  hpos * zpos.

(* Compute solve2 example. *)

(* The second part generalizes the first: the [aim] in Part Two plays the role of
   depth ([zpos]) in Part One. *) 

(* We could prove this directly, but just to be fancy, let's make it explicit
   that it relies on a _simulation argument_:
   the single-step functions [eval1] and [eval1_2] preserve a relation [R] between [position]
   and [position_2], so the iterated-step functions [eval] and [eval_2] also preserve [R]. *)

Lemma eval_sim : forall (R : position -> position_2 -> Prop),
  (forall c n p p2, R p p2 -> R (eval1 c n p) (eval1_2 c n p2)) ->
  forall xs p p2,
  R p p2 -> R (eval xs p) (eval_2 xs p2).
Proof.
  intros R SIM; induction xs as [ | [c n] xs IH ]; cbn.
  - trivial.
  - intros * H; apply IH, SIM, H.
Qed.

Lemma eval1_fact : forall c n hpos zpos aim,
  eval1 c n (hpos, aim) = let '(hpos', _, aim') := eval1_2 c n (hpos, zpos, aim) in (hpos', aim').
Proof.
  destruct c; reflexivity.
Qed.

Theorem eval_fact : forall xs hpos zpos aim,
  eval xs (hpos, aim) = let '(hpos', _, aim') := eval_2 xs (hpos, zpos, aim) in (hpos', aim').
Proof.
  intros xs hpos zpos aim; apply eval_sim.
  - intros c n _ [[? ?] ?] ->. apply eval1_fact.
  - reflexivity.
Qed.
