From Coq Require Export NArith List.
From Coq Require Import Arith Sorting Orders OrdersEx Lia.
Import ListNotations.

Add Search Blacklist "N_as".

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

(* |x-y| *)
Definition dist (x y : N) : N := if x <=? y then y - x else x - y.

Definition solve (xs : list N) : N :=
  let xs := SortN.sort xs in
  sum_N (map (dist (median xs)) xs).

(* Compute solve example. *)

Definition dist2 (x y : N) : N :=
  let d := dist x y in
  d * (d + 1) / 2.

(* Cost to move everyone starting at positions [xs] to the same position [y]. *)
Definition fuel2 (xs : list N) (y : N) : N :=
  sum_N (map (dist2 y) xs).

Fixpoint searchMin (n : nat) (f : N -> N) (low width : N) : N * N :=
  match n with O => (0, 0) | S n =>
  let il := width / 2 in
  let xl := low + il in
  let xr := low + il + 1 in
  let fl := f xl in
  let fr := f xr in
  match 1 <? width with
  | true =>
    if fl <=? fr then searchMin n f low il
    else searchMin n f xr (width - il - 1)
  | false =>
    if (0 =? width)%N || (fl <=? fr)%N then (xl, fl) else (xr, fr)
  end
  end.

Fixpoint maximum (xs : list N) : N :=
  match xs with
  | [] => 0
  | [x] => x
  | x :: xs => N.max x (maximum xs)
  end.

Definition solve2 (xs : list N) : N :=
  let f n := fuel2 xs n in
  let m := maximum xs in
  snd (searchMin (S (N.to_nat m)) f 0 m).

(* Compute solve2 example. *)

Definition solve12 (xs : list N) : N * N := (solve xs, solve2 xs).

Definition Convex (f : N -> N) : Prop :=
  forall i j k, (j+k) * f (i+j) <= k * f i + j * f (i+j+k).

Definition LocallyConvex (f : N -> N) : Prop :=
  forall i, 2 * f (i+1) <= f i + f (i+2).

Definition Predecreasing (f : N -> N) : Prop :=
  forall i j, i < j -> f j <= f i -> forall k, k <= i -> f i <= f k.

Definition Postincreasing (f : N -> N) : Prop :=
  forall i j, i < j -> f i <= f j -> forall k, j <= k -> f j <= f k.

Definition VShaped (f : N -> N) : Prop := Predecreasing f /\ Postincreasing f.

Lemma cancel_add_sub : forall a b c, c <= b -> (a + c) + (b - c) = a + b.
Proof.
  intros; rewrite N.add_sub_assoc; lia.
Qed.

Ltac forward H :=
  match type of H with
  | (?Y -> _) => let Z := fresh in assert (Z : Y); [ | specialize (H Z) ]
  end.

Lemma searchMin_sound n f
  : forall low width, width < N.of_nat n ->
    let x := searchMin n f low width in
    low <= fst x <= low + width
      /\ snd x = f (fst x).
Proof.
  induction n; cbn [searchMin]; intros; [ lia | ].
  rewrite Nat2N.inj_succ in H.
  destruct (N.ltb_spec 1 width).
  - assert (HH : width / 2 < width).
    { apply N.div_lt_upper_bound; lia. }
    destruct (_ <=? _).
    { eapply Morphisms_Prop.and_impl_morphism; [ | exact (fun X => X) | apply IHn; lia ].
      intros ?; lia. }
    { eapply Morphisms_Prop.and_impl_morphism; [ | exact (fun X => X) | apply IHn ].
      { eapply Morphisms_Prop.and_impl_morphism.
        { red; apply N.le_trans. remember (width / 2). lia. }
        { refine (fun X => N.le_trans _ _ _ X _). lia. } }
      eapply N.le_lt_trans.
      { apply N.sub_le_mono_r. apply N.le_sub_l. }
      lia. }
  - destruct (N.eqb_spec 0 width).
    { subst width; cbn. rewrite N.add_0_r. split; [ split | ]; reflexivity. }
    destruct (_ <=? _) eqn:E; cbn; split; try reflexivity.
    all: apply N.le_1_r in H0; destruct H0 as [-> | ->]; cbn; lia.
Qed.

Lemma searchMin_correct n f (Hf : VShaped f)
  : forall low width,
    width < N.of_nat n ->
    forall i, i <= width -> snd (searchMin n f low width) <= f (low+i).
Proof.
  induction n; [ (* contradiction *) lia | ]. intros; cbn [searchMin].
  rewrite Nat2N.inj_succ in H.
  destruct (N.ltb_spec 1 width).
  - assert (HH : width / 2 < width).
    { apply N.div_lt_upper_bound; lia. }
    assert (coIH : width / 2 < N.of_nat n) by lia.
    destruct (N.leb_spec (f (low + width / 2)) (f (low + width / 2 + 1))).
    + specialize (IHn low (width / 2) coIH).
      destruct (N.leb_spec i (width / 2)).
      { apply IHn; assumption. }
      { etransitivity; [ apply IHn; reflexivity | ].
        rewrite H2.
        eapply (proj2 Hf); [ | apply H2 | ]; lia. }
    + specialize (IHn (low + width / 2 + 1) (width - width / 2 - 1)).
      forward IHn.
      { eapply N.le_lt_trans.
        { apply N.sub_le_mono_r. apply N.le_sub_l. }
        lia. }
      destruct (N.ltb_spec i (width / 2 + 1)).
      { etransitivity; [ apply (IHn 0); lia | ].
        rewrite N.add_0_r.
        apply N.lt_le_incl in H2. rewrite H2.
        eapply (proj1 Hf); [ | apply H2 | ]; lia. }
      { replace i with (width / 2 + 1 + (i - (width / 2 + 1))) by lia.
        rewrite 2 N.add_assoc. apply IHn. lia. }
  - destruct (N.eqb_spec 0 width); cbn.
    { subst width; cbn. apply N.le_0_r in H0. subst. reflexivity. }
    destruct (N.leb_spec (f (low + width / 2)) (f (low + width / 2 + 1))) as [e | e]; cbn.
    all: apply N.le_1_r in H1; destruct H1 as [-> | ->]; cbn; try contradiction.
    all: apply N.le_1_r in H0; destruct H0 as [-> | ->]; cbn.
    all: cbn in e; try rewrite N.add_0_r in *; try reflexivity; lia.
Qed.

Lemma Convex_additive f g : Convex f -> Convex g -> Convex (fun i => f i + g i).
Proof.
  unfold Convex; intros Hf Hg i j k. specialize (Hf i j k). specialize (Hg i j k). lia.
Qed.

Lemma Convex_constant i : Convex (fun _ => i).
Proof.
  unfold Convex; lia.
Qed.

Lemma Convex_summative {A} (f : A -> N -> N)
  : (forall z, Convex (f z)) -> forall xs, Convex (fun i => sum_N (map (fun x => f x i) xs)).
Proof.
  intros Hf; induction xs; cbn.
  - apply Convex_constant.
  - apply Convex_additive; auto.
Qed.

Lemma div_mul : forall n m, n mod m = 0 -> n / m * m = n.
Proof.
  intros. rewrite (N.div_mod' n m) at 2. rewrite H, N.add_0_r. lia.
Qed.

Lemma conseq_even : forall n, (n * (n+1)) mod 2 = 0.
Proof.
  intros n. assert (H := N.mod_bound_pos n 2). destruct H as [_ H]; [lia ..| ].
  apply N.lt_le_pred in H.
  apply N.le_1_r in H.
  rewrite <- N.mul_mod_idemp_l by lia.
  destruct H as [ H | H ]; rewrite H.
  - reflexivity.
  - rewrite N.mul_1_l. rewrite <- N.add_mod_idemp_l by lia. rewrite H. reflexivity.
Qed.

Lemma minus_minus m n p : n <= m -> p <= n -> m - n + p = m - (n - p).
Proof.
  lia.
Qed.

Lemma LocallyConvex_dist2_2 : forall z, LocallyConvex (fun i => dist2 i z).
Proof.
  unfold Convex, dist2, dist. intros z i.
  repeat lazymatch goal with
    | [ |- context [ ?x <=? ?y ] ] => destruct (N.leb_spec x y); cbn - [N.add N.sub N.mul]
    end.
  all: try lia.
  all: apply (N.mul_le_mono_pos_r _ _ 2); [ lia | ].
  all: rewrite (N.mul_add_distr_r _ _ 2).
  all: rewrite <- !(N.mul_assoc _ _ 2).
  all: rewrite !div_mul by apply conseq_even.
  all: try lia.
  - rewrite minus_minus, N.add_sub by lia.
    replace (z - (i+1)) with ((z-i)-1) by lia.
    replace (z - (i+2) + 1) with ((z-i)-1) by lia.
    replace (z - (i+2)) with ((z-i)-2) by lia.
    rewrite ?(N.mul_add_distr_l (z-i)), ?(N.mul_add_distr_r (z-i)), ?(N.mul_sub_distr_l (z-i)), ?(N.mul_sub_distr_r (z-i)).
    remember ((z-i) * (z-i)) as ZZ.
    lia.
  - replace z with (i+1) by lia. lia.
  - replace z with i by lia. lia.
Qed.

Instance Proper_mul_le : Proper (N.le ==> N.le ==> N.le) N.mul.
Proof.
  unfold Proper, respectful. auto using N.mul_le_mono.
Qed.

Instance Proper_add_le : Proper (N.le ==> N.le ==> N.le) N.add.
Proof.
  unfold Proper, respectful. auto using N.add_le_mono.
Qed.

Lemma add_twice n : n + n = 2 * n.
Proof.
  lia.
Qed.

Lemma Convex_LocallyConvex f : LocallyConvex f -> Convex f.
Proof.
  unfold LocallyConvex, Convex. intros Hf.
  intros i j k; revert i j; induction k as [ | k IH ] using N.peano_ind; intros i j.
  - rewrite N.mul_0_l, !N.add_0_r. lia.
  - rewrite !N.add_succ_r, N.mul_succ_l.
    etransitivity; [ rewrite <- N.add_le_mono_r; apply IH | ].
    enough (j * f (i + j + k) + f (i + j) <= f i + j * f (N.succ (i + j + k))) by lia.
    clear IH.
    revert i j; induction k as [ | k IH ] using N.peano_ind; intros i j.
    + rewrite N.add_0_r, <- N.mul_succ_l.
      induction j as [ | j IH] using N.peano_ind.
      * rewrite N.add_0_r, !N.mul_0_l. lia.
      * rewrite (N.add_le_mono_r _ _ (N.succ j * f (i + N.succ j))).
        rewrite N.mul_succ_l. rewrite N.add_shuffle0, add_twice, N.mul_shuffle3, N.add_succ_r, <- (N.add_1_r (i + j)).
        rewrite (Hf (i+j)).
        rewrite N.mul_add_distr_l, IH. rewrite <- N.add_1_r.
        replace (N.succ (i + j + 1)) with (i + j + 2) by lia. lia.
    + rewrite (N.add_le_mono_r _ _ (j * f (i + j + N.succ k))).
      rewrite N.add_shuffle0, add_twice, N.mul_shuffle3.
      replace (i + j + N.succ k) with (i + j + k + 1) by lia.
      rewrite Hf.
      replace (N.succ (i + j + k + 1)) with (i + j + k + 2) by lia.
      rewrite !N.mul_add_distr_l.
      rewrite N.add_shuffle0.
      rewrite IH.
      replace (N.succ (i + j + k)) with (i + j + k + 1) by lia.
      lia.
Qed.

Lemma Postincreasing_Convex f : Convex f -> Postincreasing f.
Proof.
  unfold Convex, Postincreasing; intros Hf i j Eij Fij k Ejk. revert Fij.
  replace k with (j + (k - j)) in * by lia; generalize (k-j).
  replace j with (i + (N.pred (j - i) + 1)) in * by lia; generalize (N.pred (j-i)).
  clear j k Eij Ejk. intros j k. intros Fj.
  specialize (Hf i (j + 1) k).
  rewrite N.mul_add_distr_r in Hf.
  rewrite Fj in Hf.
  rewrite (N.add_comm (_ * _)) in Hf.
  rewrite <- N.add_le_mono_l in Hf.
  rewrite <- N.mul_le_mono_pos_l in Hf by lia.
  lia.
Qed.

Lemma Predecreasing_Convex f : Convex f -> Predecreasing f.
Proof.
  unfold Convex, Predecreasing; intros Hf i j Eij Fij k Ejk. revert Fij.
  replace j with (i + (N.pred (j - i) + 1)) in * by lia; generalize (N.pred (j-i)).
  replace i with (k + (i - k)) in * by lia; generalize (i-k).
  clear i j Eij Ejk. intros i j. intros Fj.
  specialize (Hf k i (j+1)).
  rewrite N.mul_add_distr_r in Hf.
  rewrite Fj in Hf.
  rewrite (N.add_comm (_ * _)) in Hf.
  rewrite <- N.add_le_mono_r in Hf.
  rewrite <- N.mul_le_mono_pos_l in Hf by lia.
  lia.
Qed.

Lemma VShaped_Convex f : Convex f -> VShaped f.
Proof.
  constructor.
  - apply Predecreasing_Convex; auto.
  - apply Postincreasing_Convex; auto.
Qed.

Lemma Convex_fuel2 : forall z, Convex (fuel2 z).
Proof.
  intros z; apply Convex_summative.
  intros z'; apply Convex_LocallyConvex, LocallyConvex_dist2_2.
Qed.

Theorem solve2_correct xs
  : exists i, solve2 xs = fuel2 xs i /\ forall j, j <= maximum xs -> fuel2 xs i <= fuel2 xs j.
Proof.
  unfold solve2.
  exists (fst (searchMin (S (N.to_nat (maximum xs))) (fuel2 xs) 0 (maximum xs))).
  assert (Hmax : forall i, i < N.of_nat (S (N.to_nat i))) by lia.
  refine ((fun I J => conj I (J I)) _ _).
  - apply (searchMin_sound _ _ _ _ (Hmax _)).
  - intros E j Hj. rewrite <- E. apply searchMin_correct with (low := 0).
    + apply VShaped_Convex, Convex_fuel2.
    + apply Hmax.
    + apply Hj.
Qed.
