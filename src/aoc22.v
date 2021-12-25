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

Definition cancel_cube (c1 c2 : cube) : list cube :=
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
    let c' := (switch i1, (xmin,xmax), (ymin,ymax), (zmin,zmax)) in
    match i1 with
    | on => c' :: c1 :: nil
    | off => c1 :: c' :: nil
    end.

Notation _cancel_cubes cs c := (concat (map (fun c1 => cancel_cube c1 c) cs)).
Definition cancel_cubes (cs : list cube) (c : cube) : list cube := _cancel_cubes cs c.

Definition add_cube (cs : list cube) (c2 : cube) : list cube :=
  let cs := cancel_cubes cs c2 in
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

(**)

From stdpp Require Import gmap.

Definition point : Type := Z * Z * Z.

#[global] Open Scope Z_scope.

Definition union_for {A} `{Countable A} (zmin zmax : Z) (k : Z -> gset A) : gset A :=
  Z.iter (1 + zmax - zmin) (fun go dz m => go (Z.succ dz) (union (k (zmin + dz)) m))
    (fun _ m => m) 0 empty.

Lemma Z_iter_ind {A} (f : A -> A) (x : A) (P : Z -> A -> Prop)
    (H0 : P 0 x) (HS : forall n y, 0 <= n -> P n y -> P (Z.succ n) (f y))
  : forall n, 0 <= n -> P n (Z.iter n f x).
Proof.
  intros n; induction n; intros Hn.
  - apply H0.
  - induction p using Pos.peano_ind.
    + unfold Z.iter, Pos.iter. apply (HS 0); [ reflexivity | apply H0 ].
    + unfold Z.iter. rewrite Pos.iter_succ. rewrite Pos2Z.inj_succ.
      apply HS; [ | apply IHp ]; apply Pos2Z.is_nonneg.
  - lia.
Qed.

Lemma Z_iter_neg {A} (f : A -> A) (x : A) n : n <= 0 -> Z.iter n f x = x.
Proof.
  destruct n; try reflexivity. lia.
Qed.

Lemma _union_for_spec {A} `{Countable A} (zmin zmax n : Z) (k : Z -> gset A) (x : A)
  : 0 <= n <= 1 + zmax - zmin -> forall m,
    (elem_of x m <-> exists z, elem_of x (k z) /\ zmin <= z <= zmax - n) ->
    elem_of x (Z.iter n (fun go dz m => go (Z.succ dz) (union (k (zmin + dz)) m)) (fun _ m => m) (1 + zmax - zmin - n) m)
      <-> exists z, elem_of x (k z) /\ zmin <= z <= zmax.
Proof.
  intros [Hn Hn']; revert Hn'; apply Z_iter_ind; [ | | apply Hn ]; clear Hn.
  - intros Hn m Hm. rewrite Hm. rewrite Z.sub_0_r. reflexivity.
  - clear n; intros n Hn0 f IH Hn m Hm.
    replace (Z.succ (1 + zmax - zmin - Z.succ n)) with (1 + zmax - zmin - n) by lia.
    apply IH; [ lia | ]. rewrite elem_of_union. rewrite Hm.
    replace (zmin + (1 + zmax - zmin - Z.succ n)) with (zmax - n) by lia.
    assert (HH : (elem_of x (k (zmax - n))) <-> exists z, elem_of x (k z) /\ z = zmax - n).
    { split; [ exists (zmax - n); auto | intros [_ [? ->]]; auto ]. }
    rewrite HH. clear HH.
    assert (HH : forall A (P Q : A -> Prop), (ex P \/ ex Q) <-> ex (fun z => P z \/ Q z)).
    { clear. firstorder. }
    rewrite HH. clear HH.
    apply Morphisms_Prop.ex_iff_morphism.
    intros z.
    assert (HH : forall P Q R, P /\ Q \/ P /\ R <-> P /\ (Q \/ R)).
    { clear; tauto. }
    rewrite HH. clear HH.
    apply Morphisms_Prop.and_iff_morphism.
    { reflexivity. }
    lia.
Qed.

Lemma union_for_spec {A} `{Countable A} (zmin zmax : Z) (k : Z -> gset A) (x : A)
  : elem_of x (union_for zmin zmax k) <-> exists z, elem_of x (k z) /\ zmin <= z <= zmax.
Proof.
  unfold union_for. destruct (decide (zmin <= zmax)).
  - evar (zz : Z). replace 0 with zz.
    + apply _union_for_spec. lia.
      rewrite elem_of_empty.
      split; [ intros [] | intros [z []] ]. lia.
    + lia.
  - rewrite Z_iter_neg by lia. rewrite elem_of_empty.
    split; [ intros [] | intros [z []] ]. lia.
Qed.

Definition cube_to_set (c : cube) : gset point :=
  let '(_, (xmin,xmax), (ymin,ymax), (zmin,zmax)) := c in
  union_for xmin xmax (fun x =>
  union_for ymin ymax (fun y =>
  union_for zmin zmax (fun z => singleton (x,y,z)))).

Lemma _cube_to_set_spec
  : forall '((_, (xmin, xmax), (ymin,ymax), (zmin,zmax)) as c : cube) '((x,y,z) : point),
    elem_of (x,y,z) (cube_to_set c)
    <-> ((xmin <= x <= xmax) /\ (ymin <= y <= ymax) /\ (zmin <= z <= zmax)).
Proof.
  intros [[[i [xmin xmax]] [ymin ymax]] [zmin zmax]] [[x y] z]; cbn.
  do 3 setoid_rewrite union_for_spec. split.
  - intros [x' [[y' [[z' [single Ez]] Ey]] Ex]].
    apply elem_of_singleton in single.
    inversion_clear single.
    auto.
  - intros [Ex [Ey Ez]].
    exists x; split;
      [ exists y; split; [exists z; split; [apply elem_of_singleton; easy | ] | ] | ]; auto.
Qed.

Lemma cube_to_set_spec {p x y z c i xmin xmax ymin ymax zmin zmax}
  : p = (x,y,z) ->
    c = (i,(xmin,xmax),(ymin,ymax),(zmin,zmax)) ->
    elem_of p (cube_to_set c) <->
    ((xmin <= x <= xmax) /\ (ymin <= y <= ymax) /\ (zmin <= z <= zmax)).
Proof.
  intros -> ->. apply (_cube_to_set_spec (_,(_,_),(_,_),(_,_)) (_,_,_)).
Qed.

Lemma size_union_uniform (zmin zmax zz : Z) (k : Z -> gset point)
  : (forall z z', z <> z' -> k z ## k z') ->
    (forall z, Z.of_nat (size (k z)) = zz) ->
    Z.of_nat (size (union_for zmin zmax k)) = (1 + zmax - zmin) * zz.
Proof.
Admitted.

Lemma size_cube_to_set i xmin xmax ymin ymax zmin zmax
  : Z.of_nat (size (cube_to_set (i, (xmin, xmax), (ymin, ymax), (zmin, zmax))))
  = (1 + xmax - xmin) * (1 + ymax - ymin) * (1 + zmax - zmin).
Proof.
  rewrite <- Z.mul_assoc. cbn.
  apply size_union_uniform; intros.
  { admit. }
  apply size_union_uniform; intros.
  { admit. }
  rewrite size_union_uniform with (zz := 1); [ lia | | ].
  { admit. }
  intros; rewrite size_singleton. reflexivity.
Admitted.

Definition add_cube' (xs : gset point) (c : cube) : gset point :=
  let '(i,_,_,_) := c in
  match i with
  | on => union xs (cube_to_set c)
  | off => difference xs (cube_to_set c)
  end.

Lemma vol_cube_on (c : cube)
  : fst (fst (fst c)) = on -> vol_cube c = Z.of_nat (size (cube_to_set c)).
Proof.
  destruct c as [[[? []] []] []]; cbn [vol_cube fst]; rewrite size_cube_to_set; intros ->; reflexivity.
Qed.

Lemma vol_cube_off (c : cube)
  : fst (fst (fst c)) = off -> vol_cube c = - Z.of_nat (size (cube_to_set c)).
Proof.
  destruct c as [[[? []] []] []]; cbn [vol_cube fst]; rewrite size_cube_to_set; intros ->; reflexivity.
Qed.

Fixpoint inclexcl (cs : list cube) : gset point :=
  match cs with
  | (i,_,_,_) as c :: cs =>
    match i with
    | on => union (inclexcl cs) (cube_to_set c)
    | off => difference (inclexcl cs) (cube_to_set c)
    end
  | nil => empty
  end.

Fixpoint nested_cubes (cs : list cube) : Prop :=
  match cs with
  | c :: cs =>
    (let '(i,_,_,_) := c in
    match i with
    | on => disjoint (inclexcl cs) (cube_to_set c)
    | off => subseteq (cube_to_set c) (inclexcl cs)
    end) /\ nested_cubes cs
  | nil => True
  end.

(*
Lemma count_on_cancel_cubes (cs : list cube) (c : cube)
  : count_on (cancel_cubes cs c) = Z.of_nat (size (difference (inclexcl cs) c)).
*)

Lemma disjoint_cube_to_set c1 c2
  : (let '(_, (xmin1,xmax1), (ymin1,ymax1), (zmin1,zmax1)) := c1 in
     let '(_, (xmin2,xmax2), (ymin2,ymax2), (zmin2,zmax2)) := c2 in
     (Z.min xmax1 xmax2 < Z.max xmin1 xmin2) \/ (Z.min ymax1 ymax2 < Z.max ymin1 ymin2) \/ (Z.min zmax1 zmax2 < Z.max zmin1 zmin2))%Z ->
    cube_to_set c1 ## cube_to_set c2.
Proof.
  destruct c1 as [[[i1 [xmin1 xmax1]] [ymin1 ymax1]] [zmin1 zmax1]];
  destruct c2 as [[[i2 [xmin2 xmax2]] [ymin2 ymax2]] [zmin2 zmax2]]; cbn delta.
  intros H. apply elem_of_disjoint.
  intros [[? ?] ?] H1 H2.
  rewrite (cube_to_set_spec eq_refl eq_refl) in H1.
  rewrite (cube_to_set_spec eq_refl eq_refl) in H2.
  lia.
Qed.

Lemma intercube {i1 xmin1 xmax1 ymin1 ymax1 zmin1 zmax1
    i2 xmin2 xmax2 ymin2 ymax2 zmin2 zmax2
    c' i'}
  : (c' = ( i'
          , (Z.max xmin1 xmin2,Z.min xmax1 xmax2)
          , (Z.max ymin1 ymin2,Z.min ymax1 ymax2)
          , (Z.max zmin1 zmin2,Z.min zmax1 zmax2))) ->
    cube_to_set c' = intersection (cube_to_set (i1,(xmin1,xmax1),(ymin1,ymax1),(zmin1,zmax1)))
                                  (cube_to_set (i2,(xmin2,xmax2),(ymin2,ymax2),(zmin2,zmax2))).
Proof.
  intros ->.
  apply set_eq. intros [[]]. rewrite elem_of_intersection.
  do 3 rewrite (cube_to_set_spec eq_refl eq_refl).
  split; lia.
Qed.

Lemma cancel_cube_spec cs cs' c1 c
  : nested_cubes (c1 :: cs) ->
    inclexcl cs' = difference (inclexcl cs) (cube_to_set c) ->
    inclexcl (cancel_cube c1 c ++ cs') = difference (inclexcl (c1 :: cs)) (cube_to_set c).
Proof.
  cbn.
  destruct c as [[[i [xmin2 xmax2]] [ymin2 ymax2]] [zmin2 zmax2]]; cbn [cancel_cube].
  destruct c1 as [[[[] [xmin1 xmax1]] [ymin1 ymax1]] [zmin1 zmax1]]; cbn [cancel_cube switch].
  - symmetry; rewrite difference_union_distr_l_L.
    destruct (_ : bool) eqn:Eb; cbn [inclexcl app]; intros; rewrite H0.
    + rewrite (difference_disjoint_L
        (cube_to_set (on, (xmin1, xmax1), (ymin1, ymax1), (zmin1, zmax1)))
        (cube_to_set (i, (xmin2, xmax2), (ymin2, ymax2), (zmin2, zmax2)))); [ reflexivity | ].
      apply disjoint_cube_to_set. lia.
    + symmetry; rewrite difference_union_distr_l_L.
      rewrite difference_difference_L.
      erewrite (intercube eq_refl).
      assert (EE : forall X Y : gset point, union X (intersection Y X) = X).
      { intros; rewrite union_comm_L. apply subseteq_union_L. apply intersection_subseteq_r. }
      rewrite EE. clear EE.
      assert (EE : forall X Y : gset point, difference X (intersection X Y) = difference X Y).
      { clear. intros. apply set_eq. intros x.
        do 2 rewrite elem_of_difference. rewrite not_elem_of_intersection.
        tauto. }
      rewrite EE; clear EE.
      reflexivity.
  - symmetry; rewrite difference_difference_L.
    destruct (_ : bool) eqn:Eb; cbn [inclexcl app]; rewrite H0.
    + rewrite difference_difference_L. f_equal. apply union_comm_L.
    + symmetry. rewrite difference_union_distr_l_L.
      rewrite difference_difference_L.
      assert (HH := subseteq_empty_difference_L (A := point) (C := gset point)).
      rewrite (HH (cube_to_set _) (cube_to_set _)).
      2:{ erewrite (intercube (i2 := off) eq_refl). apply intersection_subseteq_l. }
      rewrite union_empty_r_L.
      f_equal. apply union_comm_L.
Qed.

Lemma difference_cancel_cubes (cs : list cube) (c : cube)
  : nested_cubes cs ->
    inclexcl (cancel_cubes cs c) = difference (inclexcl cs) (cube_to_set c).
Proof.
  induction cs as [ | c1 cs IH ]; intros H.
  - cbn. rewrite subseteq_empty_difference_L; [ reflexivity |].
    apply empty_subseteq.
  - cbn [cancel_cubes concat map]. apply cancel_cube_spec; auto.
    apply IH, H.
Qed.

Lemma nested_cancel_cubes (cs : list cube) (c : cube)
  : nested_cubes cs ->
    nested_cubes (cancel_cubes cs c).
Proof.
  induction cs as [ | c1 cs IH ]; cbn; [ auto | ]; intros [].
  destruct c as [[[i [xmin2 xmax2]] [ymin2 ymax2]] [zmin2 zmax2]]; cbn [cancel_cube].
  destruct c1 as [[[[] [xmin1 xmax1]] [ymin1 ymax1]] [zmin1 zmax1]]; cbn [cancel_cube switch].
  - destruct (_ : bool); cbn [nested_cubes app inclexcl];
      change (_cancel_cubes cs ?i) with (cancel_cubes cs i);
      rewrite difference_cancel_cubes by auto.
    + split; auto. apply disjoint_difference_l2. auto.
    + split.
      * apply union_subseteq_r'. erewrite (intercube (i2 := off) eq_refl).
        apply intersection_subseteq_l.
      * split; auto. apply disjoint_difference_l2. auto.
  - destruct (_ : bool) eqn:Eb; cbn [nested_cubes app inclexcl];
      change (_cancel_cubes cs ?i) with (cancel_cubes cs i);
      rewrite difference_cancel_cubes by auto.
    + split; auto. apply subseteq_difference_r; auto.
      apply disjoint_cube_to_set; lia.
    + split.
      * apply elem_of_subseteq. intros p.
        rewrite elem_of_union, elem_of_difference.
        erewrite (intercube eq_refl).
        rewrite elem_of_intersection.
        intros HH.
        eassert (u := decide (elem_of p (cube_to_set _))).
        destruct u as [u | u].
        { right; split; [ apply HH | exact u ]. }
        { left; split; [ apply elem_of_subseteq in H; auto | exact u ]. }
      * split; auto.
        rewrite (intercube (i1 := off) (i2 := off) eq_refl).
        apply disjoint_difference_l1. apply intersection_subseteq_r.
Qed.

Lemma add_cube_nested (cs : list cube) (c : cube)
  : nested_cubes cs ->
    nested_cubes (add_cube cs c).
Proof.
  intros Hcs. destruct c as [[[i ?] ?] ?]; cbn [add_cube add_cube']. destruct i.
  - cbn [count_on foldr].
    constructor; [ | apply nested_cancel_cubes; auto ].
    rewrite difference_cancel_cubes by auto.
    apply disjoint_difference_l1. reflexivity.
  - apply nested_cancel_cubes; auto.
Qed.

Lemma add_cube_spec (cs : list cube) (xs : gset point := inclexcl cs) (c : cube)
  : nested_cubes cs ->
    inclexcl (add_cube cs c) = add_cube' (inclexcl cs) c.
Proof.
  intros Hcs. destruct c as [[[i ?] ?] ?]; cbn [add_cube add_cube']. destruct i.
  - cbn [inclexcl]. rewrite difference_cancel_cubes; auto.
    apply difference_union_L.
  - apply difference_cancel_cubes; auto.
Qed.

Lemma _fold_add_cube_spec (cs ks : list cube) (xs : gset point := inclexcl ks)
  : nested_cubes ks ->
    inclexcl (fold_left add_cube cs ks) = fold_left add_cube' cs xs.
Proof.
  revert ks xs; induction cs; intros ks xs Hcs; cbn.
  - reflexivity.
  - intros; rewrite IHcs.
    + f_equal; apply add_cube_spec; auto.
    + apply add_cube_nested; auto.
Qed.

Lemma fold_add_cube_spec (cs : list cube)
  : inclexcl (fold_left add_cube cs nil) = fold_left add_cube' cs empty.
Proof.
  apply _fold_add_cube_spec. constructor.
Qed.

Lemma _fold_add_cube_nested (cs : list cube)
  : forall ks, nested_cubes ks -> nested_cubes (fold_left add_cube cs ks).
Proof.
  induction cs; cbn; auto using add_cube_nested.
Qed.

Lemma fold_add_cube_nested (cs : list cube)
  : nested_cubes (fold_left add_cube cs nil).
Proof.
  apply _fold_add_cube_nested. constructor.
Qed.

Lemma size_inclexcl (cs : list cube)
  : nested_cubes cs -> count_on cs = Z.of_nat (size (inclexcl cs)).
Proof.
  induction cs as [ | c cs IH]; cbn.
  - reflexivity.
  - destruct c as [[[i ?] ?] ?]. destruct i; intros [].
    + rewrite size_union by auto.
      rewrite Nat2Z.inj_add, <- IH by auto.
      rewrite vol_cube_on by reflexivity.
      apply Z.add_comm.
    + rewrite size_difference by auto.
      rewrite Nat2Z.inj_sub, <- IH; [ | auto | apply subseteq_size; auto ].
      rewrite vol_cube_off by reflexivity.
      apply Z.add_opp_l.
Qed.

Theorem vol_add_spec (cs : list cube)
  : count_on (fold_left add_cube cs nil) = Z.of_nat (size (fold_left add_cube' cs empty)).
Proof.
  rewrite <- fold_add_cube_spec. apply size_inclexcl. apply fold_add_cube_nested.
Qed.
