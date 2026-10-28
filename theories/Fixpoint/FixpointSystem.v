(** * Constraint systems and their solutions

    Systems attach query trees to target unknowns, with optional static summaries.
    For example, a constant query constrains its target even without reading anything.
    Builds on: FixpointQuery, CollectionsMap and OrderMonotone. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery.

Module System.

(** A finite constraint list supplies targets and right-hand sides. *)
Record t (X C A : Type) : Type := Make {
  constraints : list C;
  target : C -> X;
  rhs : C -> Query.t X A
}.

Arguments Make {X C A}.
Arguments constraints {X C A}.
Arguments target {X C A}.
Arguments rhs {X C A}.

(** Static summaries cover every possible dynamic read and side target. *)
Record static {X C A} (S : t X C A) : Type := Static {
  deps : C -> list X;
  side_targets : C -> list X;
  reads_within : forall c s, incl (Query.reads (rhs S c) s) (deps c);
  sides_within : forall c s, incl (map fst (Query.sides (rhs S c) s)) (side_targets c)
}.

Arguments Static {X C A S}.
Arguments deps {X C A S}.
Arguments side_targets {X C A S}.
Arguments reads_within {X C A S}.
Arguments sides_within {X C A S}.

End System.
Import System.

Abbreviation deps := System.deps.
Abbreviation side_targets := System.side_targets.

(** A post-solution bounds every return and every side contribution. *)
Definition post_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
    forall x a, In (x, a) (Query.sides (System.rhs S c) s) -> leb L a (s x) = true.

(** Finite assignments store only explicitly supplied values. *)
Definition assignment (X A : Type) : Type := Map.t X A.

(** Absent unknowns have the lattice's bottom value. *)
Definition lookup {X A} (EX : encoding X) (L : lattice A) (m : assignment X A) (x : X) : A :=
  match Map.get EX x m with
  | Some a => a
  | None => bot L
  end.

(** Monotonicity bounds results and matches every contribution by a larger contribution. *)
Definition monotone_query {X A} (L : lattice A) (q : Query.t X A) : Prop :=
  monotone_on_assignments L L (Query.eval q) /\
  forall s1 s2, fun_leb L s1 s2 -> forall x a, In (x, a) (Query.sides q s1) ->
    exists b, In (x, b) (Query.sides q s2) /\ leb L a b = true.

(** Every listed constraint in a monotone system has a monotone query. *)
Definition monotone_system {X C A} (L : lattice A) (S : System.t X C A) : Prop :=
  forall c, In c (System.constraints S) -> monotone_query L (System.rhs S c).

(** The greatest value satisfies every constraint, including side contributions. *)
Theorem top_post_solution {X C A} (L : lattice A) (S : System.t X C A) (T : top L) :
  post_solution L S (fun _ => top_value T).
Proof.
  intros c Hc; split.
  - apply top_greatest.
  - intros x a Ha; apply top_greatest.
Qed.
