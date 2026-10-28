(** * Rule syntax and range restriction

    Rules relate predicates over encoded constants, with explicit positive and negative literals.
    For example, [Rule (Atom p [TVar 0]) [LPos (Atom q [TVar 0])]] copies facts from q to p.
    Builds on: CollectionsEncoding and Stdlib lists. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding.
Import List.ListNotations.

(** A tuple contains the encoded constants of a ground fact. *)
Definition tuple : Type := list positive.

(** Terms distinguish variables from encoded constants. *)
Inductive term : Type :=
  | TVar (v : nat)
  | TConst (c : positive).

(** An atom applies a predicate to its argument terms. *)
Record atom (P : Type) : Type := Atom {
  pred : P;
  args : list term
}.

Arguments Atom {P}.
Arguments pred {P}.
Arguments args {P}.

(** A literal records whether an atom must be present or absent. *)
Inductive literal (P : Type) : Type :=
  | LPos (a : atom P)
  | LNeg (a : atom P).

Arguments LPos {P}.
Arguments LNeg {P}.

(** A rule derives its head whenever all body literals hold. *)
Record rule (P : Type) : Type := Rule {
  head : atom P;
  body : list (literal P)
}.

Arguments Rule {P}.
Arguments head {P}.
Arguments body {P}.

(** A program supplies predicate keys, arities and rules. *)
Record program (P : Type) : Type := Program {
  penc : encoding P;
  arity : P -> nat;
  rules : list (rule P)
}.

Arguments Program {P}.
Arguments penc {P}.
Arguments arity {P}.
Arguments rules {P}.

(** Ground atoms pair their predicate with a tuple of constants. *)
Definition ground_atom (P : Type) : Type := (P * tuple)%type.

(** Instantiation replaces variables according to a total valuation. *)
Definition inst (sigma : nat -> positive) (t : term) : positive :=
  match t with
  | TVar v => sigma v
  | TConst c => c
  end.

(** Grounding instantiates every argument of an atom. *)
Definition ground {P} (sigma : nat -> positive) (a : atom P) : ground_atom P :=
  (pred a, map (inst sigma) (args a)).

(** Both literal polarities expose the same underlying atom. *)
Definition lit_atom {P} (l : literal P) : atom P :=
  match l with
  | LPos a => a
  | LNeg a => a
  end.

(** Variable occurrence preserves argument order and repetitions. *)
Definition atom_vars {P} (a : atom P) : list nat :=
  flat_map (fun t => match t with TVar v => [v] | TConst _ => [] end) (args a).

(** Every head or negative variable must also occur in a positive body atom. *)
Definition safe_rule {P} (r : rule P) : Prop :=
  forall v, (In v (atom_vars (head r)) \/
    exists a, In (LNeg a) (body r) /\ In v (atom_vars a)) ->
  exists a, In (LPos a) (body r) /\ In v (atom_vars a).

(** Programs are range restricted and all rule atoms and facts respect predicate arities. *)
Definition program_wf {P} (prog : program P) (facts : list (ground_atom P)) : Prop :=
  (forall r, In r (rules prog) -> safe_rule r /\
    length (args (head r)) = arity prog (pred (head r)) /\
    forall l, In l (body r) -> length (args (lit_atom l)) = arity prog (pred (lit_atom l))) /\
  forall f, In f facts -> length (snd f) = arity prog (fst f).
