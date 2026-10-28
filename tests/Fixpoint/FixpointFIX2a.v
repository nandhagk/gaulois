(** * Indexed worklist examples

    Computation distinguishes pending runs, completed cyclic runs and the top fallback.
    For example, a side contribution invalidates an already evaluated reader and queues it again.
    Builds on: FixpointWorklist, FixpointCheck and OrderBasic. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointWorklist.
Import List.ListNotations.

Definition worklist_schedule : scheduler nat := Scheduler (fun _ => 1%positive) (fun _ => false).

Definition worklist_empty : System.t nat nat bool :=
  System.Make [] (fun c => c) (fun _ => Query.Ret true).

Example empty_queue_finishes :
  run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining worklist_empty
    Recorded 1 = Some Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

(* The low-priority-number reader runs before its producer. The producer contributes to 0
   and the cycle propagates through 1; the repeated side target is processed in trace order. *)
Definition worklist_cycle : System.t nat nat bool :=
  System.Make [0; 1; 2] (fun c => if Nat.eqb c 0 then 1 else 0)
    (fun c => if Nat.eqb c 0 then Query.Ask 0 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 1 Query.Ret
      else Query.Side 0 true (Query.Side 0 false (Query.Ret false))).

Definition worklist_static : System.static worklist_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [0] else if Nat.eqb c 1 then [1] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then [] else [0]) _ _).
  - intros c s x Hin; unfold worklist_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
  - intros c s x Hin; unfold worklist_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; intuition.
Defined.

Definition cycle_observation (m : assignment nat bool) : list bool :=
  map (lookup nat_encoding bool_lattice m) [0; 1; 99].

Example exhausted_fuel_is_pending :
  run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining worklist_cycle
    Recorded 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cyclic_recorded_run_finishes :
  option_map cycle_observation
    (run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining worklist_cycle
      Recorded 8) = Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example cyclic_declared_run_finishes :
  option_map cycle_observation
    (run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining worklist_cycle
      (Declared worklist_static (index_system nat_encoding worklist_cycle worklist_static)) 8) =
    Some [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example completed_run_checker_accepts :
  option_map (fun m => check_post bool_lattice worklist_cycle (lookup nat_encoding bool_lattice m))
    (run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining worklist_cycle
      Recorded 8) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example side_update_queues_observed_reader :
  option_map (fun e =>
    (cycle_observation (Engine.current e), PQueue.priority nat_encoding 0 (Engine.queue e)))
    (match engine_step nat_encoding nat_encoding bool_lattice worklist_schedule Joining
      worklist_cycle Recorded (initial_state nat_encoding worklist_schedule worklist_cycle) with
     | None => None
     | Some e =>
       match engine_step nat_encoding nat_encoding bool_lattice worklist_schedule Joining
         worklist_cycle Recorded e with
       | None => None
       | Some e' => engine_step nat_encoding nat_encoding bool_lattice worklist_schedule Joining
           worklist_cycle Recorded e'
       end
     end) = Some ([true; false; false], Some 1%positive).
Proof.
  vm_compute; reflexivity.
Qed.

Definition self_reading_system : System.t nat nat bool :=
  System.Make [0] (fun c => c)
    (fun _ => Query.Ask 0 (fun _ => Query.Side 0 true (Query.Ret false))).

Example reads_recorded_before_self_update :
  option_map (fun e => (PQueue.priority nat_encoding 0 (Engine.queue e),
    FinSet.elements (recorded_at nat_encoding (Engine.recorded e) 0)))
    (engine_step nat_encoding nat_encoding bool_lattice worklist_schedule Joining
      self_reading_system Recorded
      (initial_state nat_encoding worklist_schedule self_reading_system))
    = Some (Some 1%positive, [0]).
Proof.
  vm_compute; reflexivity.
Qed.

Example completion_requires_final_probe :
  run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining
    self_reading_system Recorded 2 = None /\
  option_map (fun m => lookup nat_encoding bool_lattice m 0)
    (run_worklist nat_encoding nat_encoding bool_lattice worklist_schedule Joining
      self_reading_system Recorded 3) = Some true.
Proof.
  vm_compute; auto.
Qed.

Example top_fallback_on_exhaustion :
  map (proj1_sig (solve_fuel nat_encoding nat_encoding bool_lattice bool_laws bool_top
    worklist_schedule Joining worklist_cycle 1)) [0; 1; 99] = [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example completed_solver_keeps_computed_assignment :
  map (proj1_sig (solve_fuel nat_encoding nat_encoding bool_lattice bool_laws bool_top
    worklist_schedule Joining worklist_cycle 8)) [0; 1; 99] = [true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition distinct_widening : lattice bool :=
  Lattice bool (fun a b => negb a || b) false orb (fun _ _ => true) andb.

Definition constant_false : System.t nat nat bool :=
  System.Make [0] (fun c => c) (fun _ => Query.Ret false).

Definition pair_widening : lattice (bool * bool) :=
  Lattice (bool * bool)
    (fun a b => (negb (fst a) || fst b) && (negb (snd a) || snd b)) (false, false)
    (fun a b => (fst a || fst b, snd a || snd b)) (fun _ _ => (true, true))
    (fun a b => (fst a && fst b, snd a && snd b)).

Definition pair_system : System.t nat nat (bool * bool) :=
  System.Make [0] (fun c => c) (fun _ => Query.Ret (true, false)).

Example effective_widening_uses_selected_sites :
  option_map (fun m => lookup nat_encoding pair_widening m 0)
    (run_worklist nat_encoding nat_encoding pair_widening worklist_schedule Widening
      pair_system Recorded 2) = Some (true, false) /\
  option_map (fun m => lookup nat_encoding pair_widening m 0)
    (run_worklist nat_encoding nat_encoding pair_widening
      (Scheduler (fun _ => 1%positive) (fun _ => true)) Widening pair_system Recorded 2)
      = Some (true, true) /\
  option_map (fun m => lookup nat_encoding pair_widening m 0)
    (run_worklist nat_encoding nat_encoding pair_widening
      (Scheduler (fun _ => 1%positive) (fun _ => true)) Joining pair_system Recorded 2)
      = Some (true, false).
Proof.
  vm_compute; auto.
Qed.

Definition duplicate_reads : System.t nat nat bool :=
  System.Make [0] (fun c => c)
    (fun _ => Query.Ask 1 (fun _ => Query.Ask 1 (fun _ => Query.Ret false))).

Example repeated_reads_are_deduplicated :
  option_map (fun e => FinSet.elements (recorded_at nat_encoding (Engine.recorded e) 1))
    (engine_step nat_encoding nat_encoding bool_lattice worklist_schedule Joining
      duplicate_reads Recorded (initial_state nat_encoding worklist_schedule duplicate_reads))
    = Some [0].
Proof.
  vm_compute; reflexivity.
Qed.

Example priorities_come_from_targets :
  option_map (fun e => PQueue.priority nat_encoding 1 (Engine.queue e))
    (engine_step nat_encoding nat_encoding bool_lattice
      (Scheduler (fun x => if Nat.eqb x 0 then 1%positive else 2%positive) (fun _ => false))
      Joining worklist_cycle Recorded
      (initial_state nat_encoding
        (Scheduler (fun x => if Nat.eqb x 0 then 1%positive else 2%positive) (fun _ => false))
        worklist_cycle)) = Some None.
Proof.
  vm_compute; reflexivity.
Qed.

Example below_update_is_skipped_at_widening_point :
  option_map cycle_observation
    (run_worklist nat_encoding nat_encoding distinct_widening
      (Scheduler (fun _ => 1%positive) (fun _ => true)) Widening constant_false Recorded 2)
    = Some [false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example widening_point_is_selected :
  update_value distinct_widening worklist_schedule Joining 0 false false = false /\
  update_value distinct_widening worklist_schedule Widening 0 false false = false /\
  update_value distinct_widening (Scheduler (fun _ => 1%positive) (fun _ => true))
    Widening 0 false false = true.
Proof.
  vm_compute; auto.
Qed.
