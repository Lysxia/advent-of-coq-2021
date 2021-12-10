From Coq Require Export Ascii String NArith.
From Coq Require Import List Arith.

Import ListNotations.

Set Implicit Arguments.

#[global] Open Scope string_scope.

Infix "::" := String.String.

Fixpoint _rev_string (r s : string) : string :=
  match s with
  | "" => r
  | c :: s => _rev_string (c :: r) s
  end.

Definition rev_string : string -> string := _rev_string "".

Definition is_empty (w : string) : bool :=
  match w with
  | "" => true
  | _ => false
  end.

Fixpoint _split_on (c0 : ascii) (w s : string) : list string :=
  match s with
  | "" => if is_empty w then [] else [rev_string w]
  | c :: s =>
    if Ascii.eqb c0 c then
      if is_empty w then _split_on c0 w s else rev_string w :: _split_on c0 "" s
    else
      _split_on c0 (c :: w) s
  end.

(* Drops empty words! *)
Definition split_on (c0 : ascii) : string -> list string := _split_on c0 "".

Definition words : string -> list string := split_on " ".
Definition lines : string -> list string := split_on "010".

Definition input : string -> list string := lines.

Definition example := input
"[({(<(())[]>[[{[]{<()<>>
[(()[<>])]({[<{<<[]>>(
{([(<{}[<>[]}>{[]{[(<()>
(((({<>}<{<{<>}{[]{[]{}
[[<[([]))<([[{}[[()]]]
[{[{({}]{}}([{[{{{}}([]
{<[[]]>}<{[{[{[]{()[[[]
[<(<(<(<{}))><([]([]()
<{([([[(<>()){}]>(<<{{
<{([{{}}[<[[[<>{}]]]>[]]".

Inductive Result : Type :=
| Illegal (c : ascii)
| Valid (z : list ascii)
.

Definition bra_cket (bra : ascii) : ascii :=
  (if bra =? "(" then ")"
   else if bra =? "[" then "]"
   else if bra =? "{" then "}"
   else if bra =? "<" then ">"
   else "?")%char.

Definition cket_bra (cket : ascii) : ascii :=
  (if cket =? ")" then "("
   else if cket =? "]" then "["
   else if cket =? "}" then "{"
   else if cket =? ">" then "<"
  else "?")%char.

Fixpoint _check (z : list ascii) (s : string) : Result :=
  match s with
  | "" => Valid z
  | c :: s =>
    if ((c =? "(") || (c =? "[") || (c =? "{") || (c =? "<"))%char%bool then
      _check (c :: z) s
    else
      match z with
      | (cz :: z)%list => if (cket_bra c =? cz)%char then _check z s else Illegal c
      | _ => Illegal c
      end
  end.

Definition check := _check [].

Definition sum_with {A} (f : A -> N) : list A -> N :=
  fold_right (fun x => N.add (f x)) 0%N.

Definition score (r : Result) : N :=
  match r with
  | Valid _ => 0
  | Illegal c =>
    if c =? ")" then 3
    else if c =? "]" then 57
    else if c =? "}" then 1197
    else if c =? ">" then 25137
    else 0 (* Should not happen *)
  end%char%N.

Definition solve : list string -> N :=
  sum_with (fun l => score (check l)).

(* Compute solve example. *)

Definition score2 (z : list ascii) : N :=
  fold_left (fun a c =>
    5 * a
    + if c =? "(" then 1
      else if c =? "[" then 2
      else if c =? "{" then 3
      else if c =? "<" then 4
      else 0)%char%N z 0%N.

Fixpoint minimum1 (x : N) (xs : list N) : N :=
  match xs with
  | [] => x
  | y :: xs => minimum1 (if (x <=? y)%N then x else y) xs 
  end%list.

Definition minimum (xs : list N) : option N :=
  match xs with
  | [] => None
  | x :: xs => Some (minimum1 x xs)
  end%list.

Fixpoint _split (x : N) (l r xs : list N) : list N * list N :=
  match xs with
  | [] => (l, r)
  | y :: xs =>
    if (y <=? x)%N then _split x (y :: l) r xs else _split x l (y :: r) xs
  end%list.

Definition split (x : N) (xs : list N) := _split x [] [] xs.

Fixpoint kth (fuel : list N) (k : nat) (xs : list N) : option N :=
  match fuel with
  | [] => None
  | _ :: fuel =>
    match xs with
    | [] => None
    | x :: xs =>
      let '(l, r) := split x xs in
      let nl := length l in
      match Nat.compare k nl with
      | Eq => Some x
      | Lt => kth fuel k l
      | Gt => kth fuel (k - nl - 1) r
      end
    end
  end%list.

Definition median (xs : list N) : option N :=
  kth xs (Nat.div2 (length xs)) xs.

Definition dummydefault (x : option N) : N :=
  match x with
  | Some x => x
  | None => 0
  end.

Fixpoint map_filter {A B} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: xs =>
    match f x with
    | None => map_filter f xs
    | Some y => y :: map_filter f xs
    end
  end%list.

Definition unValid (r : Result) : option (list ascii) :=
  match r with
  | Illegal _ => None
  | Valid z => Some z
  end.

Definition solve2 (xs : list string) : N :=
  dummydefault (median (map score2 (map_filter (fun l => unValid (check l)) xs))).

(* Compute solve2 example. *)

(* [solve12] factors the common logic of [check] in [solve] and [solve2]. *)
Definition solve12 (xs : list string) : N * N :=
  let xs := map check xs in
  (sum_with score xs, dummydefault (median (map score2 (map_filter unValid xs)))).

(**)

Lemma sum_with_map {A B} (f : A -> B) (g : B -> N) xs
  : sum_with g (map f xs) = sum_with (fun x => g (f x)) xs.
Proof.
  unfold sum_with; generalize 0%N.
  induction xs; intros; cbn; congruence.
Qed.

Lemma map_filter_map {A B C} (f : A -> B) (g : B -> option C) xs
  : map_filter g (map f xs) = map_filter (fun x => g (f x)) xs.
Proof.
  induction xs as [ | x xs IH ]; cbn; [ | destruct (g (f x))]; cbn; congruence.
Qed.

Lemma solve12Correct xs : solve12 xs = (solve xs, solve2 xs).
Proof.
  unfold solve12; cbn. rewrite sum_with_map, map_filter_map. reflexivity.
Qed.

(**)

(* Correctness of [check] *)

(*
Soundness and completeness.

Soundness: If [check s] returns [Valid z], then the input [s] can be completed
into a well-bracketed string, using the stack [z], [s ++ destack z].

Theorem check_sound s z : check s = Valid z -> wellbracketed (s ++ destack z).

Completeness: If [check s] returns [Illegal c], then [c] is the earliest character of [s]
such that the prefix before [c] is still completeable to a well-bracketed string, but not any
completion after [c] (including [s] itself).

Theorem check_complete s c
  : check s = Illegal c ->
    exists t u, s = t ++ c :: u
      /\ (exists v, wellbracketed (t ++ v))
      /\ forall u', ~wellbracketed (t ++ c :: u').
*)

Lemma append_assoc (s t u : string) : (s ++ t) ++ u = s ++ (t ++ u).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma append_empty_r (s : string) : (s ++ "") = s.
Proof.
  induction s; cbn; congruence.
Qed.

Lemma append_cons_r (s : string) (c : ascii) (t : string) : (s ++ c :: "") ++ t = (s ++ c :: t).
Proof.
  induction s; cbn; congruence.
Qed.

Create HintDb wb.

Inductive brackets : ascii -> ascii -> Prop :=
| brackets_Par : brackets "(" ")"
| brackets_Squ : brackets "[" "]"
| brackets_Bra : brackets "{" "}"
| brackets_Ang : brackets "<" ">"
.
#[global] Hint Constructors brackets : wb.

Inductive wellbracketed : string -> Prop :=
| wellbracketed_empty : wellbracketed ""
| wellbracketed_step bra cket s t
  : brackets bra cket -> wellbracketed s -> wellbracketed t -> wellbracketed (bra :: s ++ cket :: t)
.
#[global] Hint Constructors wellbracketed : wb.

Lemma wellbracketed_app s t : wellbracketed s -> wellbracketed t -> wellbracketed (s ++ t).
Proof.
  revert t; induction 1; intros; cbn; auto.
  rewrite append_assoc; constructor; auto.
Qed.
#[export] Hint Resolve wellbracketed_app : wb.

Ltac spliteq :=
  lazymatch goal with
  | [ |- context [ (?lhs =? ?rhs)%char ] ] => destruct (Ascii.eqb_spec lhs rhs)
  end.

Lemma _check_adequate s : wellbracketed s -> forall t z, _check z (s ++ t) = _check z t.
Proof.
  induction 1.
  - reflexivity.
  - cbn [_check]; intros; cbn; destruct H; cbn.
    all: rewrite append_assoc; cbn.
    all: rewrite IHwellbracketed1; cbn.
    all: apply IHwellbracketed2.
Qed.

Theorem check_adequate s : wellbracketed s -> check s = Valid [].
Proof.
  rewrite <- (append_empty_r s) at 2.
  exact (fun H => _check_adequate H _ _).
Qed.

Inductive unstack : list ascii -> string -> Prop :=
| unstack_nil s : wellbracketed s -> unstack [] s
| unstack_cons bra cket z t s
  : brackets bra cket -> unstack z t -> wellbracketed s -> unstack (bra :: z) (t ++ bra :: s)
.
#[export] Hint Constructors unstack : wb.

Lemma extend_unstack z t s : unstack z t -> wellbracketed s -> unstack z (t ++ s).
Proof.
  intros [].
  - constructor. apply wellbracketed_app; auto.
  - rewrite append_assoc. cbn; econstructor; eauto. apply wellbracketed_app; auto.
Qed.

Lemma cket_bra_cket bra cket
  : cket_bra cket = bra -> bra <> "?"%char -> bra_cket bra = cket.
Proof.
  unfold cket_bra; repeat (spliteq; cbn); intros; subst; reflexivity + contradiction.
Qed.

Lemma _check_sound z z' t s : unstack z t -> _check z s = Valid z' -> unstack z' (t ++ s).
Proof.
  revert z t.
  induction s; intros z t Hz.
  - rewrite append_empty_r; cbn; congruence.
  - cbn [_check]; repeat (spliteq; cbn [orb]); subst.
    1,2,3,4: rewrite <- append_cons_r; apply IHs.
    1,2,3,4: econstructor; eauto with wb.
    all: destruct Hz; try discriminate.
    all: destruct H; cbn; spliteq; cbn; try discriminate.
    all: apply cket_bra_cket in e; [ subst | discriminate ].
    all: rewrite <- append_cons_r; apply IHs.
    all: rewrite append_assoc; cbn.
    all: apply extend_unstack; eauto with wb.
Qed.

Fixpoint destack (z : list ascii) : string :=
  match z with
  | nil => ""
  | (c :: z)%list => bra_cket c :: destack z
  end.

Definition destack_unstack z t : unstack z t -> forall s, wellbracketed s -> wellbracketed (t ++ s ++ destack z).
Proof.
  induction 1; cbn; intros.
  - rewrite append_empty_r; apply wellbracketed_app; auto.
  - rewrite append_assoc; destruct H; cbn.
    all: rewrite <- (append_assoc s), <- (append_cons_r (s ++ _)); change (?c :: ?s ++ ?t) with ((c :: s) ++ t).
    all: apply IHunstack.
    all: eauto with wb.
Qed.

Theorem check_sound s z : check s = Valid z -> wellbracketed (s ++ destack z).
Proof.
  intros H; eapply destack_unstack with (s := "").
  - eapply _check_sound with (t := ""); eauto with wb.
  - eauto with wb.
Qed.

Lemma check_prefix s t z : check (s ++ t) = Valid z -> exists z', check s = Valid z'.
Proof.
  unfold check; generalize (@nil ascii).
  induction s; cbn [check _check String.append]; [ eauto | ].
  repeat (spliteq; cbn [orb]); subst; try auto.
  intros []; [ discriminate | ].
  spliteq; [ | discriminate].
  apply IHs.
Qed.

Lemma ex_f {A B} (f : A -> B) (P : B -> Prop) : ex (fun x => P (f x)) -> ex P.
Proof.
  intros [x H]; exists (f x); exact H.
Qed.

Lemma _check_legit z s c
  : _check z s = Illegal c ->
    exists t u, s = t ++ c :: u /\ _check z (t ++ c :: "") = Illegal c /\ exists z', _check z t = Valid z'.
Proof.
  revert z; induction s as [ | cs s IH ]; cbn; [ discriminate | ].
  intros z Hz.
  lazymatch goal with
  | [ |- ex ?P ] =>
    let P' := match eval pattern c in P with
      | (?P' _) => P'
      end in
    enough (HH : (exists t, P (cs :: t)) \/ (c = cs /\ P' cs ""))
      by (destruct HH as [[t HH] | [-> HH]]; [exists (cs :: t) | exists ""]; exact HH)
  end.
  cbn. revert Hz.
  repeat (spliteq; cbn [orb]).
  1,2,3,4: left; specialize (IH _ Hz); destruct IH as (t & u & ? & ?); exists t, u; split; congruence.
  destruct z.
  - injection 1; intros <-; right; eauto 6.
  - spliteq; [ | injection 1; intros <-; right; eauto 6 ].
    left; specialize (IH _ Hz).
    destruct IH as (t & u & ? & ?). exists t, u; split; congruence.
Qed.

Lemma check_legit s c
  : check s = Illegal c ->
    exists t u, s = t ++ c :: u /\ check (t ++ c :: "") = Illegal c /\ exists z', check t = Valid z'.
Proof.
  apply _check_legit.
Qed.

Theorem check_complete s c
  : check s = Illegal c ->
    exists t u, s = t ++ c :: u
      /\ (exists v, wellbracketed (t ++ v))
      /\ forall u', ~wellbracketed (t ++ c :: u').
Proof.
  intros H; destruct (check_legit _ H) as (t & u & Hs & Ht & z' & Hz').
  exists t, u; split; [exact Hs | split ].
  - eexists; revert Hz'; apply check_sound.
  - intros u' H'.
    apply check_adequate in H'.
    rewrite <- append_cons_r in H'.
    apply check_prefix in H'.
    destruct H' as [? H']; congruence.
Qed.
