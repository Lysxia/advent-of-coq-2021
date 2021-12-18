From Coq Require Import List.
From Coq Require Export ZArith.

#[global] Open Scope Z_scope.
#[local] Open Scope bool_scope.

Declare Custom Entry nn.

Notation "'input' 'target' 'area' ':' 'x' '=' xmin '..' xmax ',' 'y' '=' ymin '..' ymax" :=
  ((xmin, xmax), (ymin, ymax))
  (at level 200, xmin custom nn, xmax custom nn, ymin custom nn, ymax custom nn, only parsing).

Notation "- n" := (Zneg n%positive) (in custom nn at level 1, n bigint, only parsing).
Notation "n" := n%Z (in custom nn at level 0, n bigint, only parsing).

Definition example := input
target area: x=20..30, y=-10..-5
.

Definition point : Type := Z * Z.

(* Assume vx >= 0 *)
Definition step '(((x, y), (vx, vy)) : point * point) : point * point :=
  let vx' := if vx =? 0 then vx else vx - 1 in
  let vy' := vy - 1 in
  ((x + vx, y + vy), (vx', vy')).

Definition req_fuel (vy : Z) (ymin : Z) : N :=
  Z.to_N (2 + ((Z.sqrt (4 * vy ^ 2 - 4 * vy - 8 * ymin + 1) + 2 * vy) / 2)).

Definition steps_for (fuel : N) (v : point) : list point :=
  N.iter fuel (fun go y => fst y :: go (step y)) (fun x => fst x :: nil) ((0,0), v).

Definition get_vy '((_, vy) : point) := vy.
Definition get_ymin '((_, (ymin, _)) : point * point) := ymin.

Definition on_target '(((xmin,xmax), (ymin,ymax)) : point * point) '((x, y) : point) : bool :=
  (xmin <=? x) && (x <=? xmax) && (ymin <=? y) && (y <=? ymax).

Definition trajectory (tgt : point * point) (v : point) : list point :=
  let fuel := req_fuel (get_vy v) (get_ymin tgt) in
  steps_for fuel v.

Definition hit (tgt : point * point) (traj : list point):=
  existsb (on_target tgt) traj.

Definition Zseq (zmin zmax : Z) : list Z :=
  Z.iter (zmax - zmin) (fun go i => i :: go (i + 1)) (fun i => i :: nil) zmin.

Definition range '(((xmin,xmax), (ymin,ymax)) : point * point) : list point :=
  list_prod (Zseq 0 xmax) (Zseq ymin (-ymin)).

Definition max_of {A} (f : A -> Z) (xs : list A) : Z :=
  fold_left (fun y x => Z.max y (f x)) xs (-42).

Definition solve (tgt : point * point) : Z :=
  max_of (max_of snd) (filter (hit tgt) (map (trajectory tgt) (range tgt))).

(*
Compute (trajectory example (6,9)).
Compute solve example.
*)

Definition solve2 (tgt : point * point) : nat :=
  length (filter (hit tgt) (map (trajectory tgt) (range tgt))).

Definition solve12 tgt :=
  let trajs := filter (hit tgt) (map (trajectory tgt) (range tgt)) in
  (max_of (max_of snd) trajs, length trajs).
