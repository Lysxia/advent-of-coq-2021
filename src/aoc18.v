From Coq Require Export NArith List.

#[local] Open Scope N_scope.

Inductive t :=
| Lf (_ : N)
| Nd (_ _ : t)
.

Declare Custom Entry bin.

Notation "'input' x .. y" := (cons x .. (cons y nil) ..) (at level 200, x custom bin, y custom bin).

Notation "'[' x ',' y ']'" := (Nd x y) (in custom bin at level 1).
Notation "n" := (Lf n) (in custom bin at level 0, n bigint).

Definition example : list t := input
[1,2]
[[1,2],3]
[9,[8,7]]
[[1,9],[8,5]]
[[[[1,2],[3,4]],[[5,6],[7,8]]],9]
[[[9,[3,8]],[[0,9],6]],[[[3,7],[4,9]],3]]
[[[[1,3],[5,3]],[[1,3],[8,7]]],[[[4,9],[6,9]],[[8,2],[7,3]]]]
.

Definition unLf (x : t) : N :=
  match x with
  | Lf n => n
  | _ => 0
  end.

Fixpoint add_left (x : t) (n : N) : t :=
  match x with
  | Lf m => Lf (n + m)
  | Nd l r => Nd (add_left l n) r
  end.

Fixpoint add_right (x : t) (n : N) : t :=
  match x with
  | Lf m => Lf (n + m)
  | Nd l r => Nd l (add_right r n)
  end.

Fixpoint explode (depth : N) (x : t) : option (N * t * N) :=
  match x with
  | Lf _ => None
  | Nd l r =>
    if depth =? 4 then Some (unLf l, Lf 0, unLf r)
    else match explode (N.succ depth) l with
      | None =>
        match explode (N.succ depth) r with
        | None => None
        | Some (rl, r', rr) => Some (0, Nd (add_right l rl) r', rr)
        end
      | Some (ll, l', lr) => Some (ll, Nd l' (add_left r lr), 0)
      end
  end.

Fixpoint split (x : t) : option t :=
  match x with
  | Lf n => if n <=? 9 then None else Some (Nd (Lf (n / 2)) (Lf ((n+1) / 2)))
  | Nd l r =>
    match split l with
    | None =>
      match split r with
      | None => None
      | Some r => Some (Nd l r)
      end
    | Some l => Some (Nd l r)
    end
  end.

Definition reduce1 (x : t) : option t :=
  match explode 0 x with
  | None => split x
  | Some (_, x, _) => Some x
  end.

Definition reduce (fuel : N) : t -> t :=
  N.iter fuel (fun _reduce x =>
    match reduce1 x with
    | None => x
    | Some x => _reduce x
    end) (fun x => x).

Fixpoint magnitude (x : t) : N :=
  match x with
  | Lf n => n
  | Nd l r => 3 * magnitude l + 2 * magnitude r
  end.

Definition solve (i : list t) : N :=
  match i with
  | nil => 0
  | cons x xs => magnitude (fold_left (fun x y => reduce 1000 (Nd x y)) xs x)
  end.

Definition example2 := input
[[[0,[5,8]],[[1,7],[9,6]]],[[4,[1,2]],[[1,4],2]]]
[[[5,[2,8]],4],[5,[[9,9],0]]]
[6,[[[6,2],[5,6]],[[7,6],[4,7]]]]
[[[6,[0,7]],[0,9]],[4,[9,[9,0]]]]
[[[7,[6,4]],[3,[1,3]]],[[[5,5],1],9]]
[[6,[[7,3],[3,2]]],[[[3,8],[5,7]],4]]
[[[[5,4],[7,7]],8],[[8,3],8]]
[[9,3],[[9,9],[6,[4,9]]]]
[[2,[[7,7],7]],[[5,8],[[9,3],[0,2]]]]
[[[[5,2],5],[8,[3,7]]],[[5,[7,5]],[4,4]]]
.

(* Compute solve example. *)
(* Compute solve example2. *)

Fixpoint pick {A} (xs : list A) : list (A * list A) :=
  match xs with
  | nil => nil
  | x :: xs => (x, xs) :: map (fun '(y,ys) => (y,x::xs)) (pick xs)
  end.

Definition pick2 {A} (xs : list A) : list (A * A) :=
  concat (map (fun '(x, xs) => map (fun '(y, ys) => (x, y)) (pick xs)) (pick xs)).

Definition maximum (xs : list N) : N := fold_left N.max xs 0.

Definition solve2 (xs : list t) : N :=
  maximum (map (fun '(x, y) => magnitude (reduce 1000 (Nd x y))) (pick2 xs)).

(* Compute solve2 example2. *)

Definition solve12 xs := (solve xs, solve2 xs).
