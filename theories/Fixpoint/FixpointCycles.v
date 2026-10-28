(** * Static flows and cycle cuts

    Read dependencies flow to both the target and declared side targets.
    For example, a query reading x and contributing to y introduces a flow from x to y.
    Builds on: FixpointSystem and Stdlib transitive closure. *)

From Stdlib Require Import List Relations.Relation_Operators.
From Gaulois.Fixpoint Require Import FixpointSystem.

(** A read flows into every possible output of the same listed constraint. *)
Definition flows {X C A} {S : System.t X C A} (SS : System.static S) (y x : X) : Prop :=
  exists c, In c (System.constraints S) /\ In y (deps SS c) /\
    (x = System.target S c \/ In x (side_targets SS c)).

(** Removing flows into the selected points leaves no nonempty cycle. *)
Definition cuts_every_cycle {X C A} {S : System.t X C A}
  (SS : System.static S) (W : X -> bool) : Prop :=
  forall x, ~ clos_trans X (fun y z => flows SS y z /\ W z = false) x x.
