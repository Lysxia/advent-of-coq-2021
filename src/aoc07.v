From Coq Require Export NArith List.
From Coq Require Import Arith Sorting Orders OrdersEx Lia Program.
Import ListNotations.

#[global] Open Scope N_scope.

Notation "'input' x ',' .. ',' y" := (cons x .. (cons y nil) ..)
  (at level 200, x constr at level 0).

Definition example := input
16,1,2,0,4,2,7,1,2,14
.

Module NTotalOrder := OTF_to_TTLB N_as_OT. 
Module SortN := Sort NTotalOrder.

Definition median (xs : list N) : N :=
  match skipn (length xs / 2)%nat xs with
  | [] => 0
  | x :: _ => x
  end.

Definition sum_N : list N -> N := fold_right N.add 0%N.

Definition dist (x y : N) : N := if x <=? y then y - x else x - y.

Definition solve (xs : list N) : N :=
  let xs := SortN.sort xs in
  sum_N (map (dist (median xs)) xs).

(* Compute solve example. *)

Definition dist2 (x y : N) : N :=
  let d := dist x y in
  d * (d + 1) / 2.

Definition fuel2 (y : N) (xs : list N) : N :=
  sum_N (map (dist2 y) xs).

#[local] Obligation Tactic := try (apply measure_wf, N.lt_wf_0).

Module Doesn'tCompute.
(* Find the minimum of a convex function f on [l,r] *)
#[program]
Fixpoint searchMin (f : N -> N) (l r : N) (fl fr : N) {measure (r - l) (N.lt)} : N * N :=
  let xl := (2 * l + r) / 3 in
  let xr := (l + 2 * r) / 3 in
  let fxl := f xl in
  let fxr := f xr in
  match l + 3 <=? r with
  | true =>
    if fl <=? fxl then searchMin f l xl fl fxl
    else if fxl <=? fxr then searchMin f l xr fl fxr
    else if fxr <=? fr then searchMin f xl r fxl fr
    else searchMin f xr r fxr fr
  | false =>
    if fl <=? fxl then (l, fl)
    else if fxl <=? fxr then (xl, fxl)
    else if fxr <=? fr then (xr, fxr)
    else (r, fr)
  end.

Add Search Blacklist "N_as".

Next Obligation.
  intros f l r fl fr searchMin xl xr fxl fxr Z H. subst Z. symmetry in H. apply N.leb_le in H.
  enough (xl + 2 <= r) by lia.
  subst xl.
  rewrite <- (N.div_add _ 2 3) by lia.
  rewrite <- (N.div_mul r 3) at 2 by lia.
  apply N.div_le_mono; lia.
Qed.

Next Obligation.
  intros f l r fl fr searchMin xl xr fxl fxr Z H. subst Z. symmetry in H. apply N.leb_le in H.
  enough (xr + 1 <= r) by lia.
  subst xr.
  rewrite <- (N.div_add _ 1 3) by lia.
  rewrite <- (N.div_mul r 3) at 2 by lia.
  apply N.div_le_mono; lia.
Qed.

Next Obligation.
  intros f l r fl fr searchMin xl xr fxl fxr Z H. subst Z. symmetry in H. apply N.leb_le in H.
  enough (l + 1 <= xl) by lia.
  rewrite <- (N.div_mul _ 3) at 1 by lia.
  apply N.div_le_mono; lia.
Qed.

Next Obligation.
  intros f l r fl fr searchMin xl xr fxl fxr Z H. subst Z. symmetry in H. apply N.leb_le in H.
  enough (l + 2 <= xr) by lia.
  rewrite <- (N.div_mul _ 3) at 1 by lia.
  apply N.div_le_mono; lia.
Qed.

End Doesn'tCompute.

Fixpoint searchMin (n : nat) (f : N -> N) (l r : N) (fl fr : N) : N * N :=
  match n with O => (0, 0) | S n =>
  let xl := (2 * l + r) / 3 in
  let xr := (l + 2 * r) / 3 in
  let fxl := f xl in
  let fxr := f xr in
  match l + 3 <? r with
  | true =>
    if fl <=? fxl then searchMin n f l xl fl fxl
    else if fxl <=? fxr then searchMin n f l xr fl fxr
    else if fxr <=? fr then searchMin n f xl r fxl fr
    else searchMin n f xr r fxr fr
  | false =>
    if fl <=? fxl then (l, fl)
    else if fxl <=? fxr then (xl, fxl)
    else if fxr <=? fr then (xr, fxr)
    else (r, fr)
  end
  end.

Fixpoint maximum (xs : list N) : N :=
  match xs with
  | [] => 0
  | [x] => x
  | x :: xs => N.max x (maximum xs)
  end.

Definition solve2 (xs : list N) : N :=
  let f n := fuel2 n xs in
  let f0 := f 0 in
  let n := maximum xs in
  let fn := f n in
  snd (searchMin (N.to_nat n) f 0 n f0 fn).

(* Compute solve2 example. *)

Definition solve12 (xs : list N) : N * N := (solve xs, solve2 xs).
