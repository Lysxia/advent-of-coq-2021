From Coq Require Export List NArith.

From stdpp Require Import gmap.

Set Implicit Arguments.
Set Contextual Implicit.

#[global] Open Scope N_scope.

Declare Custom Entry cc.

Inductive t := A | B | C | D.

Inductive cell : Type :=
| Hall (_ : option t)
| Room (label : t) (_ : option t) (_ : option t)
.

Notation hall_ := (Hall None).
Notation hall x := (Hall (Some x)).
Definition room_ x a b := Room x (Some a) (Some b).

Definition conf : Type := list cell. (* configuration *)

Definition mkconf (a b c d e f g h : t) : conf :=
  hall_ ::
  hall_ ::
  room_ A a e ::
  hall_ ::
  room_ B b f ::
  hall_ ::
  room_ C c g ::
  hall_ ::
  room_ D d h ::
  hall_ ::
  hall_ :: nil.

Notation "'input' ############# # # ### a # b # c # d ### # e # f # g # h # #########" := (mkconf a b c d e f g h)
  (at level 200, only parsing).

Definition example := input
#############
#           #
###B#C#B#D###
  #A#D#C#A#
  #########
.

Definition cost (x : t) : N :=
  match x with
  | A => 1
  | B => 10
  | C => 100
  | D => 1000
  end.

Definition eqb_t (x y : t) : bool :=
  match x, y with
  | A, A | B, B | C, C | D, D => true
  | _, _ => false
  end.

Definition skipNone {A B} (o : option A) (f : A -> list B) : list B :=
  match o with
  | None => nil
  | Some x => f x
  end.

Definition skipSome {A B} (o : option A) (f : list B) : list B :=
  match o with
  | None => f
  | Some _ => nil
  end.

Fixpoint walk_left {B} (pre suf : list cell) (k : N -> list cell -> cell -> list cell -> list B) : list B :=
  match pre with
  | nil => nil
  | Hall (Some _) :: _ => nil
  | x :: pre => k 1 pre x suf ++ walk_left pre (x :: suf) (fun i => k (N.succ i))
  end.

Fixpoint walk_right {B} (pre suf : list cell) (k : N -> list cell -> cell -> list cell -> list B) : list B :=
  match suf with
  | nil => nil
  | Hall (Some _) :: _ => nil
  | x :: suf => k 1 pre x suf ++ walk_right (x :: pre) suf (fun i => k (N.succ i))
  end.

Definition walk {B} (pre suf : list cell) (mid : cell) (k : N -> list cell -> cell -> list cell -> list B) : list B :=
  walk_left pre (mid :: suf) k ++ walk_right (mid :: pre) suf k.

Definition __pick1_Room (n : N) (c : cell) (pre suf : list cell) (x : t) : list (N * conf) :=
  walk pre suf c (fun m pre c2 suf =>
    match c2 with
    | Hall _ (* must be None *) => (cost x * (n + m), rev_append pre (Hall (Some x) :: suf)) :: nil
    | Room l y z => if eqb_t x l then
        let conf1 := (cost x * (n + m + 1), rev_append pre (Room l (Some x) z :: suf)) in
        let conf2 := (cost x * (n + m + 2), rev_append pre (Room l None (Some x) :: suf)) in
        skipSome y (conf1 :: skipSome z (conf2 :: nil))
      else nil
    end).

Definition __pick1 pre suf c : list (N * conf) :=
  match c with
  | Hall None => nil
  | Hall (Some x) => walk pre suf (Hall None) (fun n pre c2 suf =>
    match c2 with
    | Hall _ => nil
    | Room l y z => if eqb_t x l then
        let conf1 := (cost x * (n+1), rev_append pre (Room l (Some x) z :: suf)) in
        let conf2 := (cost x * (n+2), rev_append pre (Room l None (Some x) :: suf)) in
        skipSome y (conf1 :: skipSome z (conf2 :: nil))
      else nil
    end)
  | Room l x y =>
    match x with
    | None => skipNone y (fun y => if eqb_t l y then nil else __pick1_Room 2 (Room l x None) pre suf y)
    | Some x => __pick1_Room 1 (Room l None y) pre suf x
    end
  end.

Fixpoint _pick1 (pre suf : list cell) : list (N * conf) :=
  match suf with
  | nil => nil
  | x :: suf => __pick1 pre suf x ++ _pick1 (x :: pre) suf
  end.

Definition neighbors_conf (c : conf) : list (N * conf) := _pick1 nil c.

(* Compute neighbors_conf example.  *)

#[global] Instance EqDecision_t : EqDecision t.
Proof. solve_decision. Defined.

#[global] Instance Countable_t : Countable t.
Proof.
  refine {|
    encode := fun x => match x with A => 1 | B => 2 | C => 4 | D => 5 end ;
    decode := fun x => match x with 1 => Some A | 2 => Some B | 4 => Some C | 5 => Some D | _ => None end |}%positive.
  intros []; reflexivity.
Defined.

#[global] Instance EqDecision_cell : EqDecision cell.
Proof. solve_decision. Defined.

#[global] Instance Countable_cell : Countable cell.
Proof.
  apply (inj_countable (A := option t + (t * option t * option t))%type
          (fun c => match c with
            | Hall x => inl x
            | Room x y z => inr (x,y,z)
            end)
          (fun c => Some match c with
            | inl x => Hall x
            | inr (x,y,z) => Room x y z
            end)).
  intros []; reflexivity.
Defined.

(* Priority queue with a heap à la Lampropoulos (Ode on a random urn) *)
Module Q.

Inductive t (K : Type) (leK : K -> K -> Prop) (V : Type) : Type :=
| Node : K -> V -> t leK V -> t leK V -> t leK V
  (* invariant: the right tree is bigger than the left tree *)
| Leaf : t leK V
.

Section Q.

Context {K : Type} {leK : K -> K -> Prop} {V : Type} `{!RelDecision leK}.

Definition empty : t leK V := Leaf.

Fixpoint push (k : K) (v : V) (q : t leK V) : t leK V :=
  match q with
  | Leaf => Node k v Leaf Leaf
  | Node k' v' l r =>
    if decide_rel leK k k' then Node k v r (push k' v' l) else Node k' v' r (push k v l)
  end.

Fixpoint unsnoc (q : t leK V) : option (K * V * t leK V) :=
  match q with
  | Leaf => None
  | Node k v l r =>
    match unsnoc r with
    | None => Some (k, v, Leaf)
    | Some (k', v', r') => Some (k', v', Node k v r' l)
    end
  end.

(* Remove the root of [q] and push [(k, v)]. This looks awkward but seems necessary
   to make the function structurally recursive. *)
Fixpoint sift (k : K) (v : V) (q : t leK V) : t leK V :=
  match q with
  | Leaf => Node k v Leaf Leaf
  | Node _ _ l r =>
    match l, r with
    | Leaf, Node k' v' _ _ =>
      if decide_rel leK k k' then Node k v l r else Node k' v' Leaf (Node k v Leaf Leaf)
    | _, Leaf => Node k v l r (* If r = Leaf then l = Leaf *)
    | Node kl vl _ _, Node kr vr _ _ =>
      if decide_rel leK kl kr then
        if decide_rel leK k kl then
          Node k v l r
        else
          Node kl vl (sift k v l) r
      else
        if decide_rel leK k kr then
          Node k v l r
        else
          Node kr vr l (sift k v r)
    end
  end.

Definition pop (q : t leK V) : option (K * V * t leK V) :=
  match q with
  | Leaf => None
  | Node k v l r =>
    let q :=
      match unsnoc r with
      | None => Leaf
      | Some (k', v', r') => sift k' v' (Node k v r' l)
      end in
    Some (k, v, q)
  end.

Fixpoint pops (n : nat) (q : t leK V) : list (K * V) :=
  match n with
  | O => []
  | S n =>
    match pop q with
    | None => []
    | Some (k, v, q) => (k, v) :: pops n q
    end
  end.

End Q.
End Q.

(* Compute Q.pops 5 (Q.push (leK := N.le) 3 tt (Q.push 2 tt (Q.push 7 tt (Q.push 4 tt Q.empty)))). *)

Definition isSome {A} (x : option A) :=
  match x with
  | Some _ => true
  | None => false
  end.

(* [gset] insertion (as [fun x s => union (singleton x) s]) is slow,
   so we redefine our own sets from maps which have fast [insert]. *)
Notation set X := (gmap X unit).
Notation insert_set x s := (insert x tt s).
Notation elem_set x s := (isSome (lookup x s)).

Section Dijkstra. (* This is really A* now *)

Context (V : Type) `{Countable V}.

Record graph : Type :=
  { max_edges : N  (* upper bound on the number of edges, as fuel *)
  ; neighbors : V -> list (N * V)
  ; heuristic : V -> N  (* Lower bound on the remaining distance *)
  }.

Definition no_fuel : N. Proof. exact 0. Qed.
Definition not_found : N. Proof. exact 0. Qed.

Definition _dijkstra (g : graph) (goal : V) (__dijkstra : _)
    (q : Q.t N.le (N * V)) (visited : set V) : N :=
  match Q.pop q with None => not_found | Some (_, (d, v), q) =>
  if decide (v = goal) then d (* REACHED GOAL *) else
  if elem_set v visited then __dijkstra q visited (* SKIP *) else
  let visited := insert_set v visited in
  let push q '(dd, v) := if elem_set v visited then q else Q.push (d + dd + heuristic g v) (d + dd, v) q in
  let q := fold_left push (neighbors g v) q in
  __dijkstra q visited
  end.

Definition lazy_iter {A B} (n : N) (f : (A -> B) -> (A -> B)) (x : A -> B) (a : A) : B :=
  match n with
  | N0 => x a
  | Npos p =>
    let fix iterpos p (x : A -> B) a : B :=
      match p with
      | xH => f x a
      | (p~1)%positive => f (iterpos p (iterpos p x)) a
      | (p~0)%positive => iterpos p (iterpos p x) a
      end in
    iterpos p x a
  end.

Lemma lazy_iter_correct {A B} (n : N) (f : (A -> B) -> (A -> B)) x
  : lazy_iter n f x = N.iter n f x.
Proof.
  destruct n as [ | p]; unfold lazy_iter; cbn.
  - reflexivity.
  - revert x; induction p; cbn; intros.
    + f_equal. rewrite IHp. f_equal. apply IHp.
    + rewrite 2 IHp. reflexivity.
    + reflexivity.
Qed.

Definition dijkstra (g : graph) (goal start : V) : N :=
  lazy_iter (N.succ (max_edges g)) (_dijkstra g goal) (fun _ _ => no_fuel)
    (Q.push 0 (* don't need the heuristic for the first point *) (0, start) Q.empty)
    empty.

End Dijkstra.

(* n! / (n-k)! *)
Definition ffact (n k : N) : N :=
  N.iter k (fun _ff n => n * _ff (N.pred n)) (fun _ => 1) n.

Definition heur (l : conf) : N :=
  fold_right (fun x h => h +
    match x with
    | Hall (Some x) => cost x * 2
    | Hall None => 0
    | Room l u v =>
      let cc o :=
        match o with
        | None => 0
        | Some x => if eqb_t x l then 0 else cost x
        end in
      4 * cc u + 5 * cc v
    end) 0 l.

Definition graph_conf : graph conf :=
  {| max_edges := 64 * ffact 15 8
  ;  neighbors := neighbors_conf
  ;  heuristic := heur
  |}.

Definition goal := mkconf A B C D A B C D.

Definition solve : conf -> N := dijkstra graph_conf goal.

(*
Definition testconf : conf :=
  Hall (Some A) ::
  Hall (Some A) ::
  Room A None None ::
  hall_ ::
  room_ B B B ::
  hall_ ::
  room_ C C D ::
  hall_ ::
  Room D None (Some C) ::
  Hall None ::
  Hall (Some D) :: nil.
Time Compute solve testconf.
(* Compute map (fun '(_, x) => neighbors_conf x) (neighbors_conf testconf). *)
*)

(*
(* Compute neighbors_conf example. *)
Definition example1 : conf :=
  [hall_; hall_; Room A (Some B) (Some A); hall B;
   Room B (Some C) (Some D); hall_; Room C None (Some C); hall_;
   Room D (Some D) (Some A); hall_; hall_].
(* Compute neighbors_conf example1. *)
Definition example2 : conf :=
  [hall_; hall_; Room A (Some B) (Some A); hall B; 
   Room B None (Some D); hall_; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some A); hall_; hall_].
(* Compute neighbors_conf example2. *)
Definition example3 : conf :=
  [hall_; hall_; Room A (Some B) (Some A); hall B; 
   Room B None None; hall D; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some A); hall_; hall_].
(* Compute neighbors_conf example3. *)
Definition example4 : conf :=
  [hall_; hall_; Room A (Some B) (Some A); hall_; 
   Room B None (Some B); hall D; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some A); hall_; hall_].
(* Compute neighbors_conf example4. *)
Definition example5 : conf :=
  [hall_; hall_; Room A None (Some A); hall_; 
   Room B (Some B) (Some B); hall D; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some A); hall_; hall_].
(* Compute neighbors_conf example5. *)
Definition example6 : conf :=
  [hall_; hall_; Room A None (Some A); hall_; 
   Room B (Some B) (Some B); hall D; Room C (Some C) (Some C); 
   hall D; Room D None (Some A); hall_; hall_].
(* Compute neighbors_conf example6. *)
Definition example7 : conf :=
  [hall_; hall_; Room A None (Some A); hall_; 
   Room B (Some B) (Some B); hall D; Room C (Some C) (Some C); 
   hall D; Room D None None; hall A; hall_].
(* Compute neighbors_conf example7. *)
Definition example8 : conf :=
  [hall_; hall_; Room A None (Some A); hall_; 
   Room B (Some B) (Some B); hall D; Room C (Some C) (Some C); hall_;
   Room D None (Some D); hall A; hall_].
(* Compute neighbors_conf example8. *)
Definition example9 : conf :=
  [hall_; hall_; Room A None (Some A); hall_; 
   Room B (Some B) (Some B); hall_; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some D); hall A; hall_].
(* Compute neighbors_conf example9. *)
Definition example10 : conf :=
  [hall_; hall_; Room A (Some A) (Some A); hall_;
   Room B (Some B) (Some B); hall_; Room C (Some C) (Some C); hall_;
   Room D (Some D) (Some D); hall_; hall_].
*)

(* Time Compute solve example. *)
