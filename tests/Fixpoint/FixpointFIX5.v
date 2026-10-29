(** * Nested WTO computation examples

    Small three-level systems expose component stabilization, side outputs and fuel boundaries.
    For example, joining reaches the middle value where widening at a head reaches the top.
    Builds on: FixpointNested, FixpointCheck and OrderLattice. *)

From Stdlib Require Import List Bool Arith PeanoNat PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphWto.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointWorklist FixpointTotal FixpointSchedule FixpointNested.
Import List.ListNotations.

Inductive nested_test_value : Type :=
  | TestBottom
  | TestMiddle
  | TestTop.

Definition nested_test_rank (a : nested_test_value) : nat :=
  match a with
  | TestBottom => 0
  | TestMiddle => 1
  | TestTop => 2
  end.

Definition nested_test_join (a b : nested_test_value) : nested_test_value :=
  if Nat.leb (nested_test_rank a) (nested_test_rank b) then b else a.

Definition nested_test_lattice : lattice nested_test_value :=
  {| leb := fun a b => Nat.leb (nested_test_rank a) (nested_test_rank b);
     bot := TestBottom;
     join := nested_test_join;
     widen := fun _ _ => TestTop;
     narrow := fun a _ => a |}.

Definition nested_test_laws : lattice_laws nested_test_lattice.
Proof.
  constructor; intros; repeat match goal with x : nested_test_value |- _ => destruct x end;
    cbn in *; congruence.
Qed.

Definition nested_test_top : top nested_test_lattice.
Proof.
  refine (Top _ _ TestTop _); intros []; reflexivity.
Defined.

Definition nested_test_height : height nested_test_lattice.
Proof.
  refine (Height _ _ nested_test_rank 2 _ _).
  - intros []; cbn; lia.
  - intros [] []; cbn; intros H; try discriminate; lia.
Defined.

Definition nested_test_wrank : widening_rank nested_test_lattice.
Proof.
  refine (WideningRank _ _ (fun a => 2 - nested_test_rank a) _ _);
    intros [] []; cbn; intros H; try discriminate; lia.
Defined.

Definition nested_test_empty : System.t nat nat nested_test_value :=
  System.Make [] (fun c => c) (fun _ => Query.Ret TestBottom).

Definition nested_test_empty_static : System.static nested_test_empty.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _); intros c s x Hin; exact Hin.
Defined.

Example empty_nested_run_finishes_with_one_unit_under_both_strategies :
  nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_empty
    nested_test_empty_static 1 = Some Map.empty /\
  nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_empty
    nested_test_empty_static 1 = Some Map.empty.
Proof.
  vm_compute; auto.
Qed.

Definition nested_test_cycle : System.t nat nat nested_test_value :=
  System.Make [0; 1; 2] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 2 Query.Ret
      else Query.Ask 0 (fun a => Query.Ask 2
        (fun b => Query.Ret (nested_test_join TestMiddle (nested_test_join a b))))).

Definition nested_test_cycle_static : System.static nested_test_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2] else [0; 2])
    (fun _ => []) _ _); intros c s x Hin; unfold nested_test_cycle in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Defined.

Definition nested_test_observe (result : option (assignment nat nested_test_value)) :=
  option_map (fun m => map (lookup nat_encoding nested_test_lattice m) [0; 1; 2]) result.

Example nested_cycle_has_an_actual_inner_component :
  NestedPlan.root (nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static) =
    NestedComponent 1 (NestedVisit 0 (NestedComponent 2 NestedEnd NestedEnd)) NestedEnd /\
  index_get nat_encoding
    (NestedPlan.members (nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static))
    2 =
    [2; 1].
Proof.
  vm_compute; auto.
Qed.

Example nested_cycle_completes_with_distinct_joining_and_widening_results :
  nested_test_observe (nested_run nat_encoding nat_encoding nested_test_lattice Joining
    nested_test_cycle nested_test_cycle_static 200) = Some [TestMiddle; TestMiddle; TestMiddle] /\
  nested_test_observe (nested_run nat_encoding nat_encoding nested_test_lattice Widening
    nested_test_cycle nested_test_cycle_static 200) = Some [TestTop; TestTop; TestTop].
Proof.
  vm_compute; auto.
Qed.

(** A bounded test observer records the constraints, without changing the production machine. *)
Fixpoint nested_test_trace (n : nat) (plan : NestedPlan.t nat nat) (st : strategy)
    (S : System.t nat nat nested_test_value) (state : NestedState.t nat nat nested_test_value) :
    list nat :=
  match n with
  | 0 => []
  | S smaller =>
    match nested_step nat_encoding nested_test_lattice plan st S state with
    | None => []
    | Some next =>
      let trace := nested_test_trace smaller plan st S next in
      match NestedState.ready state with
      | [] => trace
      | c :: _ => c :: trace
      end
    end
  end.

Example inner_component_stabilizes_before_its_outer_head_is_revisited :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  nested_test_trace 12 plan Joining nested_test_cycle (nested_start plan) = [1; 0; 2; 2] /\
  nested_test_trace 12 plan Widening nested_test_cycle (nested_start plan) = [1; 0; 2; 2].
Proof.
  vm_compute; auto.
Qed.

Example changing_an_inner_member_marks_all_containing_components :
  let plan := nested_prepare nat_encoding nested_test_cycle nested_test_cycle_static in
  let state := nested_update nat_encoding nested_test_lattice plan Joining (2, TestMiddle)
    (nested_start plan) in
  (FinSet.mem nat_encoding 1 (NestedState.dirty state),
    FinSet.mem nat_encoding 2 (NestedState.dirty state), NestedState.changed state) =
    (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example exhausted_nested_fuel_returns_no_assignment :
  nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_cycle
    nested_test_cycle_static 1 = None /\
  nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_cycle
    nested_test_cycle_static 1 = None.
Proof.
  vm_compute; auto.
Qed.

Definition nested_test_side : System.t nat nat nested_test_value :=
  System.Make [0; 1] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Side 1 TestMiddle (Query.Ret TestBottom)
      else Query.Ask 1 Query.Ret).

Definition nested_test_side_static : System.static nested_test_side.
Proof.
  refine (System.Static (fun c => if Nat.eqb c 0 then [] else [1])
    (fun c => if Nat.eqb c 0 then [1] else []) _ _); intros c s x Hin;
    unfold nested_test_side in *; cbn in *; destruct (Nat.eqb c 0); exact Hin.
Defined.

Example side_contribution_targets_an_earlier_component :
  NestedPlan.root (nested_prepare nat_encoding nested_test_side nested_test_side_static) =
    NestedComponent 1 NestedEnd (NestedVisit 0 NestedEnd).
Proof.
  vm_compute; reflexivity.
Qed.

Example a_side_change_dirties_an_already_visited_component :
  let plan := nested_prepare nat_encoding nested_test_side nested_test_side_static in
  match nested_loop (nested_step nat_encoding nested_test_lattice plan Joining nested_test_side)
    6 (nested_start plan) with
  | inl state => (NestedState.changed state,
    FinSet.mem nat_encoding 1 (NestedState.dirty state))
  | inr _ => (false, false)
  end = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example a_side_change_requires_a_complete_second_outer_pass :
  let plan := nested_prepare nat_encoding nested_test_side nested_test_side_static in
  nested_test_trace 14 plan Joining nested_test_side (nested_start plan) = [1; 0; 1; 0] /\
  nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_side
    nested_test_side_static 13 = None /\
  nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_side
    nested_test_side_static 13 = None /\
  option_map (fun m => check_post nested_test_lattice nested_test_side
    (lookup nat_encoding nested_test_lattice m))
    (nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_side
      nested_test_side_static 14) = Some true /\
  option_map (fun m => check_post nested_test_lattice nested_test_side
    (lookup nat_encoding nested_test_lattice m))
    (nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_side
      nested_test_side_static 14) = Some true.
Proof.
  vm_compute; auto.
Qed.

Example target_buckets_preserve_constraint_order_and_duplicates :
  index_get nat_encoding (nested_targets nat_encoding
    (System.Make [2; 0; 2; 1] (fun _ => 0) (fun _ => Query.Ret TestBottom))) 0 = [2; 0; 2; 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example outer_stabilization_keeps_the_side_contribution_under_both_strategies :
  option_map (fun m => lookup nat_encoding nested_test_lattice m 1)
    (nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_side
      nested_test_side_static 100) = Some TestMiddle /\
  option_map (fun m => lookup nat_encoding nested_test_lattice m 1)
    (nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_side
      nested_test_side_static 100) = Some TestTop.
Proof.
  vm_compute; auto.
Qed.

Example completed_nested_runs_pass_the_independent_full_checker :
  option_map (fun m => check_post nested_test_lattice nested_test_cycle
    (lookup nat_encoding nested_test_lattice m))
    (nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_cycle
      nested_test_cycle_static 200) = Some true /\
  option_map (fun m => check_post nested_test_lattice nested_test_side
    (lookup nat_encoding nested_test_lattice m))
    (nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_side
      nested_test_side_static 100) = Some true.
Proof.
  vm_compute; auto.
Qed.

Example exhausted_nested_solver_uses_the_everywhere_top_fallback :
  map (proj1_sig (nested_solve_fuel nat_encoding nat_encoding nested_test_lattice nested_test_laws
    nested_test_top Joining nested_test_cycle nested_test_cycle_static 1)) [0; 1; 2; 99] =
    [TestTop; TestTop; TestTop; TestTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example joining_nested_cycle_has_a_computed_completion_witness :
  exists fuel m, nested_run nat_encoding nat_encoding nested_test_lattice Joining nested_test_cycle
    nested_test_cycle_static fuel = Some m.
Proof.
  exists 200%positive, (Map.set nat_encoding 0 TestMiddle
    (Map.set nat_encoding 1 TestMiddle (Map.set nat_encoding 2 TestMiddle Map.empty))).
  vm_compute; reflexivity.
Qed.

Example widening_nested_cycle_has_a_computed_completion_witness :
  exists fuel m, nested_run nat_encoding nat_encoding nested_test_lattice Widening nested_test_cycle
    nested_test_cycle_static fuel = Some m.
Proof.
  exists 200%positive, (Map.set nat_encoding 0 TestTop
    (Map.set nat_encoding 1 TestTop (Map.set nat_encoding 2 TestTop Map.empty))).
  vm_compute; reflexivity.
Qed.
