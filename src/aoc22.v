From Coq Require Export ZArith NArith.
From Coq Require Import List.

#[global] Open Scope Z_scope.

Declare Custom Entry cc.

Notation "'input' c1 .. cn" := (cons c1 .. (cons cn nil) ..)
  (at level 200, c1 custom cc at level 1, cn custom cc at level 1, only parsing).

Inductive s := on | off.

Notation "zz 'x=' xmin '..' xmax ',' 'y' '=' ymin '..' ymax ',' 'z' '=' zmin '..' zmax" :=
  (zz, (xmin, xmax), (ymin, ymax), (zmin, zmax))
  (in custom cc at level 0, zz constr at level 0, only parsing).

Notation "'-' x" := (Zneg x%positive) (in custom cc at level 0, x bigint, only parsing).
Notation "x" := (x%Z) (in custom cc at level 0, x bigint, only parsing).

Definition example := input
on x=10..12,y=10..12,z=10..12
on x=11..13,y=11..13,z=11..13
off x=9..11,y=9..11,z=9..11
on x=10..10,y=10..10,z=10..10
.

Definition cube : Type := (s * (Z * Z) * (Z * Z) * (Z * Z)).

Definition switch (i : s) : s := match i with on => off | off => on end.

Definition intersect (c1 c2 : cube) : list cube :=
  let '(i1, (xmin1, xmax1), (ymin1, ymax1), (zmin1, zmax1)) := c1 in
  let '(i2, (xmin2, xmax2), (ymin2, ymax2), (zmin2, zmax2)) := c2 in
  let xmin := Z.max xmin1 xmin2 in
  let xmax := Z.min xmax1 xmax2 in
  let ymin := Z.max ymin1 ymin2 in
  let ymax := Z.min ymax1 ymax2 in
  let zmin := Z.max zmin1 zmin2 in
  let zmax := Z.min zmax1 zmax2 in
  if ((xmax <? xmin) || (ymax <? ymin) || (zmax <? zmin))%bool then
    c1 :: nil
  else
    (switch i1, (xmin,xmax), (ymin,ymax), (zmin,zmax)) :: c1 :: nil.

Definition add_cube (cs : list cube) (c2 : cube) : list cube :=
  let cs := concat (map (fun c1 => intersect c1 c2) cs) in
  let '(i2, _, _, _) := c2 in
  match i2 with
  | on => c2 :: cs
  | off => cs
  end.

Definition vol_cube (c : cube) : Z :=
  let '(i, (xmin,xmax), (ymin,ymax), (zmin,zmax)) := c in
  let v := (1 + xmax - xmin) * (1 + ymax - ymin) * (1 + zmax - zmin) in
  match i with
  | on => v
  | off => - v
  end.

Definition count_on (cs : list cube) : Z :=
  fold_right (fun c n => vol_cube c + n) 0 cs.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end%list.

Definition remove50 (cs : list cube) : list cube :=
  map_filter (fun '((_, (xmin,xmax), (ymin,ymax), (zmin,zmax)) as c) =>
    if ((50 <? xmin) || (xmax <? -50) || (50 <? ymin) || (ymax <? -50) || (50 <? zmin) || (zmax <? -50))%bool then None else Some c) cs.

Definition solve (cs : list cube) : Z :=
  let cs := remove50 cs in
  let cs := fold_left add_cube cs nil in
  count_on cs.

(* Compute solve example. *)

Definition solve2 (cs : list cube) : Z :=
  let cs := fold_left add_cube cs nil in
  count_on cs.

Definition solve12 (xs : list cube) : Z * Z := (solve xs, solve2 xs).
