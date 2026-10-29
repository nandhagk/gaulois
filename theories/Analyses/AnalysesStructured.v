(** * Variable interfaces for structured clients

    Structured analyses use explicit descriptions of atom and guard variables.
    For example, a copy atom reads its source and defines its destination.
    Builds on: ViewsSkeleton and ViewsStructured. *)

From Stdlib Require Import List.
From Gaulois.Views Require Import ViewsSkeleton ViewsStructured.
Import List.ListNotations.

(** A client lists the variables read, written and observed by its primitive actions. *)
Record skel_vars (A G X : Type) : Type := SkelVars {
  atom_uses : A -> list X;
  atom_defs : A -> list X;
  atom_trap_uses : A -> list X;
  guard_uses : G -> list X
}.

Arguments atom_uses {A G X}.
Arguments atom_defs {A G X}.
Arguments atom_trap_uses {A G X}.
Arguments guard_uses {A G X}.

(** Primitive transitions respect their declared variables and guard observations. *)
Record skel_vars_laws {A G St O X Cv} (C : skeleton_client A G St O)
    (sv : skel_vars A G X) (look : St -> X -> Cv) : Prop := {
  atom_frame : forall a st l st' x, atom_step C a st l st' -> ~ In x (atom_defs sv a) ->
    look st' x = look st x;
  atom_agrees : forall a st1 l st1' st2, atom_step C a st1 l st1' ->
    (forall x, In x (atom_uses sv a) -> look st1 x = look st2 x) ->
    exists st2', atom_step C a st2 l st2' /\
      forall x, In x (atom_defs sv a) -> look st1' x = look st2' x;
  guard_agrees : forall g st1 st2,
    (forall x, In x (guard_uses sv g) -> look st1 x = look st2 x) ->
    guard_bool C g st1 = guard_bool C g st2 /\ guard_index C g st1 = guard_index C g st2;
  trap_agrees : forall a st1 st2,
    (forall x, In x (atom_trap_uses sv a) -> look st1 x = look st2 x) ->
    (atom_trap C a st1 <-> atom_trap C a st2) /\ (atom_stop C a st1 <-> atom_stop C a st2);
  jump_keeps : forall p n st st' x, jump_effect C p n st st' -> look st' x = look st x
}.

(** An action inventory contains both its inputs and its outputs. *)
Definition act_vars {A G X} (sv : skel_vars A G X) (act : action A G) : list X :=
  match act with
  | AAtom a => atom_uses sv a ++ atom_defs sv a
  | AGuard g _ => guard_uses sv g
  | AIndexIs g _ => guard_uses sv g
  | AIndexAtLeast g _ => guard_uses sv g
  | AJump _ _ => []
  end.
