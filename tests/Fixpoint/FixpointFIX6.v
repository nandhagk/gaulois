(** * Observation-oriented SCC computation examples

    Nested cycles exercise immutable predecessor inputs and component-boundary expiration.
    For example, a predecessor is retained through a successor cycle and removed before later SCCs.
    Builds on: FixpointObserve, FixpointCheck, FixpointNested and OrderLattice. *)

From Stdlib Require Import List Bool Arith PeanoNat PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointWorklist FixpointSchedule FixpointNested FixpointObserve.
Import List.ListNotations.

Inductive observation_test_value : Type :=
  | ObservationBottom
  | ObservationMiddle
  | ObservationTop.

Definition observation_test_rank (value : observation_test_value) : nat :=
  match value with
  | ObservationBottom => 0
  | ObservationMiddle => 1
  | ObservationTop => 2
  end.

Definition observation_test_join (left right : observation_test_value) : observation_test_value :=
  if Nat.leb (observation_test_rank left) (observation_test_rank right) then right else left.

Definition observation_test_lattice : lattice observation_test_value :=
  Lattice _ (fun left right => Nat.leb (observation_test_rank left) (observation_test_rank right))
    ObservationBottom observation_test_join (fun _ _ => ObservationTop) (fun left _ => left).

Definition observation_test_laws : lattice_laws observation_test_lattice.
Proof.
  constructor; intros;
    repeat match goal with value : observation_test_value |- _ => destruct value end;
    cbn in *; congruence.
Qed.

Definition observation_test_system : System.t nat nat observation_test_value :=
  System.Make [0; 1; 2; 3; 4; 5; 6] (fun c => c)
    (fun c =>
      match c with
      | 0 => Query.Ret ObservationMiddle
      | 1 => Query.Ask 2 Query.Ret
      | 2 => Query.Ask 3 Query.Ret
      | 3 => Query.Ask 1 (fun left => Query.Ask 3 (fun right => Query.Ask 0
          (fun predecessor => Query.Ret
            (observation_test_join predecessor (observation_test_join left right)))))
      | 4 => Query.Ask 1 Query.Ret
      | 5 => Query.Ask 4 Query.Ret
      | _ => Query.Ret ObservationBottom
      end).

Definition observation_test_static : System.static observation_test_system.
Proof.
  refine (System.Static
    (fun c => match c with 1 => [2] | 2 => [3] | 3 => [1; 3; 0] | 4 => [1] | 5 => [4] | _ => [] end)
    (fun _ => []) _ _); intros [|[|[|[|[|[|c]]]]]] s x Hin; exact Hin.
Defined.

Definition observation_test_index :=
  index_system nat_encoding observation_test_system observation_test_static.

Definition observation_test_roots := [3; 5; 6; 5].

Definition observation_test_plan :=
  observation_canonical nat_encoding observation_test_system observation_test_static
    observation_test_index.

Definition observation_test_result (st : strategy) (fuel : positive) :=
  observation_run nat_encoding observation_test_lattice st observation_test_system
    observation_test_static observation_test_index observation_test_roots
    observation_test_plan fuel.

Definition observation_test_schedule :=
  observation_compile nat_encoding observation_test_system observation_test_static 0
    observation_test_roots observation_test_plan.

Example observation_component_order_and_nested_local_schedule_are_fixed :
  observation_components observation_test_plan = [[6]; [0]; [1; 2; 3]; [4]; [5]] /\
  map (fun component => NestedPlan.root (ObservationComponent.code component))
    observation_test_schedule =
    [NestedVisit 6 NestedEnd; NestedVisit 0 NestedEnd;
     NestedComponent 1 (NestedComponent 3 NestedEnd (NestedVisit 2 NestedEnd)) NestedEnd;
     NestedVisit 4 NestedEnd; NestedVisit 5 NestedEnd] /\
  map ObservationComponent.expire observation_test_schedule = [[6]; []; [3; 0; 2]; [1]; [5; 4]].
Proof.
  vm_compute; auto.
Qed.

Example observation_preparation_accepts_the_canonical_plan :
  observation_prepare nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots = Some observation_test_plan /\
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots observation_test_plan = true.
Proof.
  vm_compute; auto.
Qed.

Definition observation_test_reordered_lifetimes :=
  ObservationPlan (observation_components observation_test_plan)
    (Map.set nat_encoding 1 [0; 3; 2] (observation_expire observation_test_plan)).

Example observation_reordered_lifetimes_are_accepted_and_preserve_results :
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots observation_test_reordered_lifetimes = true /\
  observation_run nat_encoding observation_test_lattice Joining observation_test_system
    observation_test_static observation_test_index observation_test_roots
    observation_test_reordered_lifetimes 64 = observation_test_result Joining 64 /\
  observation_reference nat_encoding observation_test_lattice Widening observation_test_system
    observation_test_static observation_test_index observation_test_roots
    observation_test_reordered_lifetimes 64 = observation_test_result Widening 64.
Proof.
  vm_compute; auto.
Qed.

Example observation_empty_lifetime_bindings_and_duplicate_evictions_are_semantic :
  let p := ObservationPlan (observation_components observation_test_plan)
    (Map.set nat_encoding 0 []
      (Map.set nat_encoding 1 [0; 3; 2; 0] (observation_expire observation_test_plan))) in
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots p = true /\
  observation_run nat_encoding observation_test_lattice Joining observation_test_system
    observation_test_static observation_test_index observation_test_roots p 64 =
    observation_test_result Joining 64.
Proof.
  vm_compute; auto.
Qed.

Definition observation_test_alternative_plan :=
  let order := [[0]; [6]; [3; 1; 2]; [4]; [5]] in
  ObservationPlan order (observation_expirations nat_encoding observation_test_system
    observation_test_static observation_test_index order).

Example observation_valid_component_and_member_reorderings_are_accepted :
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots observation_test_alternative_plan = true /\
  option_map (fun values => map (fun x => Map.get nat_encoding x values) [3; 5; 6])
    (observation_run nat_encoding observation_test_lattice Joining observation_test_system
      observation_test_static observation_test_index observation_test_roots
      observation_test_alternative_plan 400) =
    Some [Some ObservationMiddle; Some ObservationMiddle; Some ObservationBottom].
Proof.
  vm_compute; auto.
Qed.

Example observation_invalid_topological_order_and_split_scc_are_rejected :
  let backwards := [[6]; [1; 2; 3]; [0]; [4]; [5]] in
  let split_cycle := [[6]; [0]; [1]; [2; 3]; [4]; [5]] in
  let plan_for := fun order => ObservationPlan order
    (observation_expirations nat_encoding observation_test_system observation_test_static
      observation_test_index order) in
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots (plan_for backwards) = false /\
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots (plan_for split_cycle) = false.
Proof.
  vm_compute; auto.
Qed.

Example observation_nested_cycle_stabilizes_with_its_predecessor_input :
  option_map (fun values => map (fun x => Map.get nat_encoding x values) [3; 5; 6])
    (observation_test_result Joining 400) =
    Some [Some ObservationMiddle; Some ObservationMiddle; Some ObservationBottom] /\
  option_map (fun values => map (fun x => Map.get nat_encoding x values) [3; 5; 6])
    (observation_test_result Widening 400) =
    Some [Some ObservationTop; Some ObservationTop; Some ObservationBottom].
Proof.
  vm_compute; auto.
Qed.

Example observation_duplicates_coalesce_and_bottom_is_explicitly_stored :
  option_map (fun values => (Map.size values, Map.get nat_encoding 6 values,
    Map.get nat_encoding 0 values, Map.get nat_encoding 4 values))
    (observation_test_result Joining 400) = (Some (3, Some ObservationBottom, None, None)).
Proof.
  vm_compute; reflexivity.
Qed.

Example observation_fuel_exhaustion_agrees_with_the_reference :
  observation_test_result Joining 1 = None /\ observation_test_result Widening 1 = None /\
  observation_reference nat_encoding observation_test_lattice Joining observation_test_system
    observation_test_static observation_test_index observation_test_roots observation_test_plan 1 =
    None.
Proof.
  vm_compute; auto.
Qed.

Example observation_exact_completion_boundary_uses_the_same_fuel :
  observation_test_result Joining 63 = None /\ observation_test_result Widening 63 = None /\
  option_map Map.size (observation_test_result Joining 64) = Some 3 /\
  option_map Map.size (observation_test_result Widening 64) = Some 3 /\
  option_map Map.size
    (observation_reference nat_encoding observation_test_lattice Joining observation_test_system
      observation_test_static observation_test_index observation_test_roots
      observation_test_plan 64)
    = Some 3 /\
  observation_reference nat_encoding observation_test_lattice Joining observation_test_system
    observation_test_static observation_test_index observation_test_roots observation_test_plan 63 =
    None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** This finite test observer records working memory only when a component finishes. *)
Fixpoint observation_test_boundaries (ticks : nat)
    (state : ObservationState.t nat nat observation_test_value +
      (assignment nat observation_test_value * assignment nat observation_test_value)) :
    list (list nat * nat * option observation_test_value * option observation_test_value) :=
  match ticks, state with
  | 0, _ => []
  | _, inr _ => []
  | S remaining, inl current =>
    let after := observation_tick nat_encoding observation_test_lattice Joining
      (observation_system observation_test_system 0) true state in
    let tail := observation_test_boundaries remaining after in
    match nested_step nat_encoding observation_test_lattice
      (ObservationComponent.code (ObservationState.active current)) Joining
      (observation_system observation_test_system 0) (ObservationState.local current) with
    | Some _ => tail
    | None =>
      let '(values, output) :=
        match after with
        | inl next =>
          (NestedState.current (ObservationState.local next), ObservationState.observed next)
        | inr result => result
        end in
      (ObservationComponent.members (ObservationState.active current), Map.size values,
        Map.get nat_encoding 0 values, Map.get nat_encoding 3 output) :: tail
    end
  end.

Example observation_predecessor_expires_after_the_cycle_before_later_components :
  observation_test_boundaries 400
    (observation_begin observation_test_schedule Map.empty Map.empty) =
    [([6], 0, None, None); ([0], 1, Some ObservationMiddle, None);
     ([1; 2; 3], 1, None, Some ObservationMiddle);
     ([4], 1, None, Some ObservationMiddle); ([5], 0, None, Some ObservationMiddle)].
Proof.
  vm_compute; reflexivity.
Qed.

(** The bounded observer samples the predecessor before each repeated evaluation of constraint 3. *)
Fixpoint observation_test_predecessor_reads (ticks : nat)
    (state : ObservationState.t nat nat observation_test_value +
      (assignment nat observation_test_value * assignment nat observation_test_value)) :
    list (option observation_test_value) :=
  match ticks, state with
  | 0, _ => []
  | _, inr _ => []
  | S remaining, inl current =>
    let after := observation_tick nat_encoding observation_test_lattice Joining
      (observation_system observation_test_system 0) true state in
    let tail := observation_test_predecessor_reads remaining after in
    match NestedState.ready (ObservationState.local current) with
    | 3 :: _ =>
      Map.get nat_encoding 0 (NestedState.current (ObservationState.local current)) :: tail
    | _ => tail
    end
  end.

Example observation_predecessor_is_retained_through_repeated_cycle_reads :
  let samples := observation_test_predecessor_reads 64
    (observation_begin observation_test_schedule Map.empty Map.empty) in
  Nat.leb 2 (length samples) = true /\
  forallb (fun sample => match sample with Some ObservationMiddle => true | _ => false end)
    samples = true.
Proof.
  vm_compute; auto.
Qed.

Example observation_full_reference_passes_the_independent_checker :
  option_map (fun values => check_post observation_test_lattice observation_test_system
    (lookup nat_encoding observation_test_lattice values))
    (observation_full_reference nat_encoding observation_test_lattice Widening
      observation_test_system observation_test_static observation_test_index observation_test_roots
      observation_test_plan 400)
    = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example observation_outside_the_universe_is_rejected :
  observation_prepare nat_encoding observation_test_system observation_test_static
    observation_test_index [99] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example observation_early_expiration_and_missing_components_are_rejected :
  let wrong_lifetime := ObservationPlan (observation_components observation_test_plan)
    (Map.set nat_encoding 0 [0] (observation_expire observation_test_plan)) in
  let missing_component := ObservationPlan [] (observation_expire observation_test_plan) in
  observation_plan_check nat_encoding observation_test_system observation_test_static
    observation_test_index observation_test_roots wrong_lifetime = false /\
  observation_test_result Joining 400 =
    observation_reference nat_encoding observation_test_lattice Joining observation_test_system
      observation_test_static observation_test_index observation_test_roots
      observation_test_plan 400 /\
  observation_run nat_encoding observation_test_lattice Joining observation_test_system
    observation_test_static observation_test_index observation_test_roots
    missing_component 400 = None.
Proof.
  vm_compute; auto.
Qed.

Definition observation_test_side_system : System.t nat nat observation_test_value :=
  System.Make [0] (fun _ => 0) (fun _ => Query.Ret ObservationBottom).

Definition observation_test_side_static : System.static observation_test_side_system.
Proof.
  refine (System.Static (fun _ => []) (fun _ => [1]) _ _); intros c s x Hin; contradiction.
Defined.

Example observation_declared_side_targets_are_rejected_even_without_actual_contributions :
  let ix := index_system nat_encoding observation_test_side_system observation_test_side_static in
  let p := observation_canonical nat_encoding observation_test_side_system
    observation_test_side_static ix in
  observation_prepare nat_encoding observation_test_side_system observation_test_side_static
    ix [0] = None /\
  observation_plan_check nat_encoding observation_test_side_system observation_test_side_static
    ix [0] p = false /\
  observation_run nat_encoding observation_test_lattice Joining observation_test_side_system
    observation_test_side_static ix [0] p 400 = None.
Proof.
  vm_compute; auto.
Qed.

Definition observation_test_read_only : System.t nat nat observation_test_value :=
  System.Make [0] (fun _ => 0) (fun _ => Query.Ask 1 Query.Ret).

Definition observation_test_read_only_static : System.static observation_test_read_only.
Proof.
  refine (System.Static (fun _ => [1]) (fun _ => []) _ _); intros c s x Hin; exact Hin.
Defined.

Example observation_unknowns_without_target_constraints_retain_bottom :
  let ix := index_system nat_encoding observation_test_read_only
    observation_test_read_only_static in
  let p := observation_canonical nat_encoding observation_test_read_only
    observation_test_read_only_static ix in
  observation_components p = [[1]; [0]] /\
  option_map (fun values => (Map.size values, Map.get nat_encoding 1 values,
    Map.get nat_encoding 0 values))
    (observation_run nat_encoding observation_test_lattice Joining observation_test_read_only
      observation_test_read_only_static ix [1; 0; 1] p 30) =
    Some (2, Some ObservationBottom, Some ObservationBottom).
Proof.
  vm_compute; auto.
Qed.

Definition observation_test_empty : System.t nat nat observation_test_value :=
  System.Make [] (fun c => c) (fun _ => Query.Ret ObservationBottom).

Definition observation_test_empty_static : System.static observation_test_empty.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _); intros c s x Hin; exact Hin.
Defined.

Example observation_empty_system_and_empty_observations_finish_at_one_unit :
  let ix := index_system nat_encoding observation_test_empty observation_test_empty_static in
  let p := ObservationPlan [] Map.empty in
  observation_prepare nat_encoding observation_test_empty observation_test_empty_static ix [] =
    Some p /\
  observation_run nat_encoding observation_test_lattice Joining observation_test_empty
    observation_test_empty_static ix [] p 1 = Some Map.empty /\
  observation_full_reference nat_encoding observation_test_lattice Widening observation_test_empty
    observation_test_empty_static ix [] p 1 = Some Map.empty /\
  option_map Map.size (observation_run nat_encoding observation_test_lattice Joining
    observation_test_system observation_test_static observation_test_index []
    observation_test_plan 64)
    = Some 0.
Proof.
  vm_compute; auto.
Qed.

Example observation_internal_occurrences_preserve_constraint_order_and_duplicates :
  let system := System.Make [2; 0; 2; 1] (fun _ => 0) (fun _ => Query.Ret ObservationBottom) in
  let numbered := observation_system system 0 in
  map (observation_label 0 (observation_number 0 (System.constraints system)))
    (index_get nat_encoding (nested_targets nat_encoding numbered) 0) = [2; 0; 2; 1].
Proof.
  vm_compute; reflexivity.
Qed.
