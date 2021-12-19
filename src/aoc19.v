From Coq Require Export ZArith List.
Import ListNotations.

From stdpp Require Import gmap sorting lexico.

Set Implicit Arguments.

#[local] Open Scope Z_scope.
Declare Custom Entry scanner.

Definition point : Type := (Z * Z * Z).
Definition scanner : Type := list point.

Notation "'input' s1 .. sn" :=
  (cons (A := Z * scanner) s1 .. (cons (A := Z * scanner) sn nil) ..)
  (at level 200, s1 custom scanner, sn custom scanner, only parsing).

Notation "'---' 'scanner' x '---' p1 .. pn" :=
  (x%Z, cons (A := point) p1 .. (cons (A := point) pn nil) ..)
  (in custom scanner at level 3, x constr at level 0, p1 at level 2, only parsing).

Notation "x , y , z" := (x,y,z)
  (in custom scanner at level 2, y at level 0, z at level 0, only parsing).

Notation "- n" := (Zneg n%positive) (in custom scanner at level 0, n bigint, only parsing).
Notation "n" := n%Z (in custom scanner at level 0, n bigint, only parsing).

Definition example : list (Z * scanner) := input
--- scanner 0 ---
404,-588,-901
528,-643,409
-838,591,734
390,-675,-793
-537,-823,-458
-485,-357,347
-345,-311,381
-661,-816,-575
-876,649,763
-618,-824,-621
553,345,-567
474,580,667
-447,-329,318
-584,868,-557
544,-627,-890
564,392,-477
455,729,728
-892,524,684
-689,845,-530
423,-701,434
7,-33,-71
630,319,-379
443,580,662
-789,900,-551
459,-707,401

--- scanner 1 ---
686,422,578
605,423,415
515,917,-361
-336,658,858
95,138,22
-476,619,847
-340,-569,-846
567,-361,727
-460,603,-452
669,-402,600
729,430,532
-500,-761,534
-322,571,750
-466,-666,-811
-429,-592,574
-355,545,-477
703,-491,-529
-328,-685,520
413,935,-424
-391,539,-444
586,-435,557
-364,-763,-893
807,-499,-711
755,-354,-619
553,889,-390

--- scanner 2 ---
649,640,665
682,-795,504
-784,533,-524
-644,584,-595
-588,-843,648
-30,6,44
-674,560,763
500,723,-460
609,671,-379
-555,-800,653
-675,-892,-343
697,-426,-610
578,704,681
493,664,-388
-671,-858,530
-667,343,800
571,-461,-707
-138,-166,112
-889,563,-600
646,-828,498
640,759,510
-630,509,768
-681,-892,-333
673,-379,-804
-742,-814,-386
577,-820,562

--- scanner 3 ---
-589,542,597
605,-692,669
-500,565,-823
-660,373,557
-458,-679,-417
-488,449,543
-626,468,-788
338,-750,-386
528,-832,-391
562,-778,733
-938,-730,414
543,643,-506
-524,371,-870
407,773,750
-104,29,83
378,-903,-323
-778,-728,485
426,699,580
-438,-605,-362
-469,-447,-387
509,732,623
647,635,-688
-868,-804,481
614,-800,639
595,780,-596

--- scanner 4 ---
727,592,562
-293,-554,779
441,611,-461
-714,465,-776
-743,427,-804
-660,-479,-426
832,-632,460
927,-485,-438
408,393,-506
466,436,-512
110,16,151
-258,-428,682
-393,719,612
-211,-452,876
808,-476,-593
-575,615,604
-485,667,467
-680,325,-822
-627,-443,-432
872,-547,-609
833,512,582
807,604,487
839,-516,451
891,-625,532
-652,-548,-490
30,-46,-14
.

Definition z_rotations : list (point -> point) :=
  [ fun '(x,y,z) => (x,y,z)
  ; fun '(x,y,z) => (y,-x,z)
  ; fun '(x,y,z) => (-x,-y,z)
  ; fun '(x,y,z) => (-y,x,z)
  ].

Definition z_inversions : list (point -> point) :=
  [ fun '(x,y,z) => (x,y,z)
  ; fun '(x,y,z) => (x,-y,-z)
  ].

Definition z_corotations : list (point -> point) :=
  [ fun '(x,y,z) => (x,y,z)
  ; fun '(x,y,z) => (z,x,y)
  ; fun '(x,y,z) => (y,z,x)
  ].

Definition orientations : list (point -> point) := Eval cbn in
  map (fun '(f, (g, h)) '(x,y,z) => f (g (h (x,y,z))))
    (list_prod z_corotations (list_prod z_inversions z_rotations)).

Definition to_x '((x,_,_) : point) : Z := x.
Definition to_y '((_,y,_) : point) : Z := y.
Definition to_z '((_,_,z) : point) : Z := z.

Definition in_range_on (f : point -> Z) (p q : point) : bool :=
  Z.abs (f p - f q) <=? 1000.

Definition in_range (p q : point) :=
  in_range_on to_x p q &&
  in_range_on to_y p q &&
  in_range_on to_z p q.

(* Both scanners must be sorted *)
Definition scanner_match (xpos ypos : point) (x y : scanner) : bool :=
  let x := filter (in_range ypos) x in
  let y := filter (in_range xpos) y in
  (12 <=? length x)%nat && bool_decide (x = y).

Definition memoS := gmap (Z * Z) unit.

Record m (a : Type) : Type := MkM { unM : memoS -> memoS * a }.

Definition bindM {A B} (u : m A) (k : A -> m B) : m B :=
  MkM (fun s => let '(s, x) := unM u s in unM (k x) s).

Definition retM {A} (x : A) : m A :=
  MkM (fun s => (s, x)).

Notation "'let*' x ':=' u 'in' k" := (bindM u (fun x => k))
  (at level 200, x pattern).

Fixpoint find' {A B} (xs : list A) (f : A -> option B) : option B :=
  match xs with
  | nil => None
  | x :: xs =>
    match f x with
    | None => find' xs f
    | Some y => Some y
    end
  end.

Fixpoint findM {A B} (xs : list A) (f : A -> m (option B)) : m (option B) :=
  match xs with
  | nil => retM None
  | x :: xs =>
    let* o := f x in
    match o with
    | None => findM xs f
    | Some y => retM (Some y)
    end
  end.

Notation "'let?' x ':=' xs 'in' f" := (find' xs (fun x => f))
  (at level 200, x pattern).

Notation "'let?*' x ':=' xs 'in' f" := (findM xs (fun x => f))
  (at level 200, x pattern).

Definition on_point (f : Z -> Z -> Z) '((x,y,z) : point) '((x',y',z') : point) : point :=
  (f x x', f y y', f z z').

Declare Scope point_scope.
Delimit Scope point_scope with point.

Notation "x - y" := (on_point Z.sub x y) : point_scope.
Notation "x + y" := (on_point Z.add x y) : point_scope.

Definition sort_scanner : scanner -> scanner := merge_sort lexico.

Definition count {A} `{EqDecision A, Countable A} (xs : list A) : gmap A positive :=
  fold_left (fun m x => partial_alter (fun on =>
    match on with
    | None => Some 1%positive
    | Some n => Some (Pos.succ n)
    end) x m) xs empty.

Definition try_match (xpos : point) (x y : scanner) : option (point * scanner) :=
  let? o := orientations in
  let y := map o y in
  let xy := count (map (fun '(a,b) => a - b)%point (list_prod x y)) in
  match map_to_list (filter (fun '(_, n) => 12 <=? n)%positive xy) with
  | (d, _) :: _ => Some (d, map (fun ey => ey + d)%point y)
  | [] => None
  end.

Definition try_matchM (xid yid : Z) (xpos : point) (x y : scanner) : m (option (point * scanner)) :=
  MkM (fun s =>
    let k := (xid, yid) in
    match lookup k s with
    | None => (insert k tt s, try_match xpos x y)
    | Some _ => (s, None)
    end).

(*
Time Eval vm_compute in match map snd example with
  | a :: b :: c :: d :: _ => try_match (0,0,0) a b
  | _ => None
  end.
Time Eval vm_compute in match map snd example with
  | a :: b :: c :: d :: _ => try_match (sort_scanner a) c
  | _ => None
  end.
Time Eval vm_compute in match map snd example with
  | a :: b :: c :: d :: e :: _ => try_match (sort_scanner b) e
  | _ => None
  end.
*)

Fixpoint pick {A} (xs : list A) : list (A * list A) :=
  match xs with
  | nil => nil
  | x :: xs => (x, xs) :: map (fun '(y,ys) => (y,x::ys)) (pick xs)
  end.

Lemma Forall_map {A B} (f : A -> B) (P : B -> Prop) xs
  : Forall (fun x => P (f x)) xs -> Forall P (map f xs).
Proof.
  induction 1; cbn; constructor; auto.
Qed.

Lemma pick_correct {A} (xs : list A)
  : List.Forall (fun '(y,ys) => exists ys1 ys2, ys = ys1 ++ ys2 /\ xs = ys1 ++ y :: ys2) (pick xs).
Proof.
  induction xs; cbn; constructor.
  - exists [], xs; split; reflexivity.
  - apply Forall_map. apply (Forall_impl _ _ _ IHxs). clear.
    intros [x ys] (ys1 & ys2 & [HH1 HH2]).
    exists (a :: ys1), ys2. split; cbn; congruence.
Qed.

Definition next_scanner (xs : list (Z * point * scanner)) (ys : list (Z * scanner))
  : m (option (list (Z * point * scanner) * list (Z * scanner))) :=
  let?* ((yid, y), ys) := pick ys in
  let?* (xid, xpos, x) := xs in
  let* o := try_matchM xid yid xpos x y in
  match o with
  | None => retM None
  | Some (ypos, y) => retM (Some ((yid, ypos, y) :: xs, ys))
  end.

(* fuel = length ys *)
Fixpoint _full_scan (fuel : nat) (xs : list (Z * point * scanner)) (ys : list (Z * scanner))
  : m (list (Z * point * scanner)) :=
  match fuel with
  | O => retM xs
  | S fuel =>
    let* o := next_scanner xs ys in
    match o with
    | None => retM nil (* something went wrong *)
    | Some (xs, ys) => _full_scan fuel xs ys
    end
  end.

Definition full_scan (xs : list (Z * scanner)) : list (Z * point * scanner) :=
  match xs with
  | (xid, x) :: xs =>
    snd (unM (_full_scan (length xs) [(xid, (0,0,0), x)] xs) empty)
  | [] => []
  end.

(*
Time Compute full_scan example.
*)
(*
Definition fs_example : list scanner :=
  [[(-739, -1745, 668); (-706, -3180, -659); 
    (-697, -3072, -689); (-687, -1600, 576); (-654, -3158, -753);
    (-635, -1737, 486); (-620, -3212, 371); (-601, -1648, -643);
    (-518, -1681, -600); (-499, -1607, -770); 
    (-470, -3283, 303); (-430, -3130, 366); (12, -2351, -103);
    (346, -2985, 342); (366, -3059, 397); (377, -2827, 367);
    (396, -1931, -563); (408, -1815, 803); (432, -2009, 850);
    (497, -1838, -617); (534, -1912, 768); (568, -2007, -577);
    (686, -3108, -505); (776, -3184, -501); (846, -3110, -434)];
   [(-739, -1745, 668); (-706, -3180, -659); (-697, -3072, -689);
    (-687, -1600, 576); (-654, -3158, -753); (-635, -1737, 486);
    (-620, -3212, 371); (-601, -1648, -643); (-518, -1681, -600);
    (-499, -1607, -770); (-470, -3283, 303); (-430, -3130, 366);
    (12, -2351, -103); (346, -2985, 342); (366, -3059, 397);
    (377, -2827, 367); (396, -1931, -563); (408, -1815, 803);
    (432, -2009, 850); (497, -1838, -617); (534, -1912, 768);
    (568, -2007, -577); (686, -3108, -505); (776, -3184, -501);
    (846, -3110, -434)];
   [(-739, -1745, 668); (-706, -3180, -659); (-697, -3072, -689);
    (-687, -1600, 576); (-654, -3158, -753); (-635, -1737, 486);
    (-620, -3212, 371); (-601, -1648, -643); (-518, -1681, -600);
    (-499, -1607, -770); (-470, -3283, 303); (-430, -3130, 366);
    (12, -2351, -103); (346, -2985, 342); (366, -3059, 397);
    (377, -2827, 367); (396, -1931, -563); (408, -1815, 803);
    (432, -2009, 850); (497, -1838, -617); (534, -1912, 768);
    (568, -2007, -577); (686, -3108, -505); (776, -3184, -501);
    (846, -3110, -434)];
   [(-739, -1745, 668); (-687, -1600, 576); (-661, -816, -575);
    (-635, -1737, 486); (-618, -824, -621); (-601, -1648, -643);
    (-537, -823, -458); (-518, -1681, -600); (-499, -1607, -770);
    (-485, -357, 347); (-447, -329, 318); (-345, -311, 381);
    (-27, -1108, -65); (390, -675, -793); (396, -1931, -563);
    (404, -588, -901); (408, -1815, 803); (423, -701, 434);
    (432, -2009, 850); (459, -707, 401); (497, -1838, -617);
    (528, -643, 409); (534, -1912, 768); (544, -627, -890);
    (568, -2007, -577)];
   [(-892, 524, 684); (-876, 649, 763); (-838, 591, 734);
    (-789, 900, -551); (-689, 845, -530); (-661, -816, -575);
    (-618, -824, -621); (-584, 868, -557); (-537, -823, -458);
    (-485, -357, 347); (-447, -329, 318); (-345, -311, 381);
    (7, -33, -71); (390, -675, -793); (404, -588, -901); 
    (423, -701, 434); (443, 580, 662); (455, 729, 728); 
    (459, -707, 401); (474, 580, 667); (528, -643, 409);
    (544, -627, -890); (553, 345, -567); (564, 392, -477);
    (630, 319, -379)]].
*)

Fixpoint union (xs ys : list point) : list point :=
  match xs with
  | (x :: xs) as xxs =>
    let fix union__ yys :=
      match yys with
      | y :: ys =>
        if decide (x = y) then x :: union xs ys else
        if decide (lexico x y) then x :: union xs yys else y :: union__ ys
      | [] => xxs
      end
    in union__ ys
  | _ => ys
  end.

Definition merge_beacons (xs : list (Z * point * scanner)) : scanner :=
  fold_left (fun xs ys => union xs (sort_scanner (snd ys))) xs [].

Definition _solve xs' := length (merge_beacons xs').

Definition solve (xs : list (Z * scanner)) : nat :=
  _solve (full_scan xs).

(* Time Compute solve example. *)

Fixpoint pick2 {A} (xs : list A) : list (A * A) :=
  match xs with
  | x :: xs => map (fun y => (x, y)) xs ++ pick2 xs
  | [] => []
  end.

Definition dist (p q : point) :=
  let '(x,y,z) := (p - q)%point in
  Z.abs x + Z.abs y + Z.abs z.

Definition maximumZ (xs : list Z) : Z :=
  fold_left Z.max xs 0%Z.

Definition diameter (xs : list point) : Z :=
  maximumZ (map (fun '(p,q) => dist p q) (pick2 xs)).

Definition _solve2 (xs' : list (Z * point * scanner)) : Z :=
  diameter (map (fun '(_,p,_) => p) xs').

Definition solve2 (xs : list (Z * scanner)) : Z :=
  let xs' := full_scan xs in
  _solve2 xs'.

(* Time Compute solve2 example. *)

Definition solve12 (xs : list (Z * scanner)) : nat * Z :=
  let xs' := full_scan xs in
  (_solve xs', _solve2 xs').
