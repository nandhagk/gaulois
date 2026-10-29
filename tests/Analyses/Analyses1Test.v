(** * Dense dataflow examples

    Small graphs exercise may-facts, must-facts and accepted code motion across a diamond.
    For example, inserting expression 7 on the empty arm makes deletion at the join valid.
    Builds on: AnalysesLiveness, AnalysesAvailable and FixpointTotal. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck FixpointWorklist
  FixpointTotal
  FixpointSchedule FixpointIndex.
From Gaulois.Domains Require Import DomainsEquality.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable.
Import List.ListNotations.

Local Definition computed_map {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys) : assignment X A :=
  match run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256 with
  | Some m => m
  | None => Map.empty
  end.

Local Lemma total_computation {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys)
    (HT : terminates L ss sch Joining) :
  (match run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256 with
   | Some _ => true
   | None => false
   end) = true ->
  proj1_sig (solve_total EX EC L HL sch Joining sys ss HT) =
    lookup EX L (computed_map EX EC L sch sys ss).
Proof.
  unfold computed_map.
  destruct (run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256)
    as [m|] eqn:Hrun; [intro Hsuccess|discriminate].
  destruct (solve_total_run EX EC L sys sch Joining HL ss HT) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m' [Hrun' Heq]].
  pose proof (total_completed_runs_unique EX EC L sch Joining sys _ fuel 256 m' m Hrun' Hrun)
    as Hsame.
  now rewrite Hsame in Heq.
Qed.

Definition empty_graph : Graph.t nat nat := Graph.Make [] [] (fun _ => []) id id.

Definition empty_vars : var_view nat unit nat nat nat unit :=
  VarView (GraphView empty_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun _ => []) (fun _ => []) (fun _ => []) (fun _ _ => tt).

Example empty_liveness :
  fmem nat_encoding 0 (proj1_sig (solve_liveness nat_encoding nat_encoding nat_encoding empty_vars)
    0) = false.
Proof.
  unfold solve_liveness; rewrite total_computation;
    [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

Definition diamond : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2; 3; 4; 5; 6]
    (fun n => match n with
              | 0 => [0; 1]
              | 1 => [2]
              | 2 => [3]
              | 3 => [4]
              | 5 => [5]
              | _ => []
              end)
    (fun e => match e with 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | _ => 5 end)
    (fun e => match e with 0 => 1 | 1 => 2 | 2 | 3 => 3 | 4 => 4 | _ => 6 end).

Definition diamond_view : graph_view nat unit nat nat :=
  GraphView diamond id (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition diamond_vars : var_view nat unit nat nat nat unit :=
  VarView diamond_view
    (fun e => match e with 0 | 4 => [0] | 5 => [9] | _ => [] end)
    (fun e => match e with 0 | 1 | 2 => [0] | 5 => [9] | _ => [] end)
    (fun n => match n with 4 => [0] | 6 => [8] | _ => [] end) (fun _ _ => tt).

Definition live : nat -> live_set nat_encoding diamond_vars :=
  proj1_sig (solve_liveness nat_encoding nat_encoding nat_encoding diamond_vars).

Local Lemma live_computation n : live n =
  lookup nat_encoding (live_lattice nat_encoding diamond_vars)
    (computed_map nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
      (live_lattice nat_encoding diamond_vars)
      (rpo_scheduler nat_encoding _ (liveness_static nat_encoding diamond_vars))
      (liveness_system nat_encoding diamond_vars) (liveness_static nat_encoding diamond_vars)) n.
Proof.
  unfold live, solve_liveness; rewrite total_computation; [reflexivity|vm_compute; reflexivity].
Qed.

Example same_edge_use_before_def : fmem nat_encoding 0 (live 0) = true.
Proof.
  rewrite live_computation; vm_compute; reflexivity.
Qed.

Example live_kill : fmem nat_encoding 0 (live 1) = false.
Proof.
  rewrite live_computation; vm_compute; reflexivity.
Qed.

Example unreachable_use_is_live : fmem nat_encoding 9 (live 5) = true.
Proof.
  rewrite live_computation; vm_compute; reflexivity.
Qed.

Example unreachable_exit_propagates : fmem nat_encoding 8 (live 5) = true.
Proof.
  rewrite live_computation; vm_compute; reflexivity.
Qed.

Definition reaching : nat -> reach_set nat_encoding nat_encoding diamond_vars :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (reach_lattice nat_encoding nat_encoding diamond_vars) (finite_powerset_laws _ _)
    (rpo_scheduler nat_encoding (reaching_system nat_encoding nat_encoding diamond_vars)
      (forward_static _ _ _)) Joining
    (reaching_system nat_encoding nat_encoding diamond_vars) (forward_static _ _ _)
    (inhabits (base_height (finite_powerset_height _ _
      (FinSet.elements_nodup _ _ (FinSet.wf_fold_add _ _ _ (Map.wf_empty _))))))).

Local Definition reaching_run : nat -> reach_set nat_encoding nat_encoding diamond_vars :=
  lookup nat_encoding (reach_lattice nat_encoding nat_encoding diamond_vars)
    (computed_map nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
      (reach_lattice nat_encoding nat_encoding diamond_vars)
      (rpo_scheduler nat_encoding (reaching_system nat_encoding nat_encoding diamond_vars)
        (forward_static _ _ _))
      (reaching_system nat_encoding nat_encoding diamond_vars) (forward_static _ _ _)).

Local Lemma reaching_computation : reaching = reaching_run.
Proof.
  unfold reaching, reaching_run.
  apply total_computation; vm_compute; reflexivity.
Qed.

Example reaching_killed_definition :
  fmem (pair_encoding nat_encoding nat_encoding) (0, 0) (reaching 3) = false /\
  fmem (pair_encoding nat_encoding nat_encoding) (0, 2) (reaching 3) = true /\
  fmem (pair_encoding nat_encoding nat_encoding) (0, 1) (reaching 3) = true.
Proof.
  rewrite reaching_computation; vm_compute; auto.
Qed.

Definition raw_reaching_graph : Graph.t nat nat :=
  Graph.Make [7; 7] [0; 0] (fun _ => [0; 1; 0]) (fun _ => 99) (fun _ => 88).

Definition raw_reaching_vars : var_view nat unit nat nat nat unit :=
  VarView (GraphView raw_reaching_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun _ => [])
    (fun e => match e with 0 | 9 => [0; 0] | 1 => [0; 1; 1] | _ => [] end)
    (fun _ => []) (fun _ _ => tt).

Definition raw_reaching_fact : reach_set nat_encoding nat_encoding raw_reaching_vars :=
  top_value (finite_powerset_top _ _).

Definition raw_reaching_system := reaching_system nat_encoding nat_encoding raw_reaching_vars.

Definition raw_reaching_result e : reach_set nat_encoding nat_encoding raw_reaching_vars :=
  Query.eval (System.rhs raw_reaching_system (Flow e)) (fun _ => raw_reaching_fact).

(** Unlisted writes kill old pairs but their fresh pairs remain outside the universe. *)
Example reaching_unlisted_kill :
  fmem (pair_encoding nat_encoding nat_encoding) (0, 0) (raw_reaching_result 9) = false /\
  fmem (pair_encoding nat_encoding nat_encoding) (0, 1) (raw_reaching_result 9) = false /\
  fmem (pair_encoding nat_encoding nat_encoding) (1, 1) (raw_reaching_result 9) = true /\
  fmem (pair_encoding nat_encoding nat_encoding) (0, 9) (raw_reaching_result 9) = false.
Proof.
  vm_compute; auto.
Qed.

(** An unlisted edge with no definitions retains the complete input fact. *)
Example reaching_unlisted_empty :
  proj1_sig (raw_reaching_result 8) = proj1_sig raw_reaching_fact.
Proof.
  vm_compute; reflexivity.
Qed.

(** Raw views preserve complete transfers and ordered observations for every queried row. *)
Example reaching_raw_observations :
  map (fun e => Query.run (System.rhs raw_reaching_system (Flow e))
      (fun _ => raw_reaching_fact)) [0; 1; 9; 8] =
    map (fun e => (reaching_transfer nat_encoding nat_encoding raw_reaching_vars e
      raw_reaching_fact, [99], ([] : list (nat * reach_set nat_encoding nat_encoding
        raw_reaching_vars)))) [0; 1; 9; 8] /\
  System.target raw_reaching_system (Flow 9) = 88 /\
  Query.run (System.rhs raw_reaching_system (Seed 12)) (fun _ => raw_reaching_fact) =
    (bot (reach_lattice nat_encoding nat_encoding raw_reaching_vars), [], []).
Proof.
  vm_compute; auto.
Qed.

Definition zero_left : live_set nat_encoding diamond_vars :=
  finite_clamp nat_encoding (var_universe nat_encoding diamond_vars)
    (FinSet.of_list nat_encoding [0; 8]).

Definition zero_right : live_set nat_encoding diamond_vars :=
  finite_clamp nat_encoding (var_universe nat_encoding diamond_vars)
    (FinSet.of_list nat_encoding [8; 9]).

Example must_join_intersects :
  fmem nat_encoding 0 (join (zero_lattice nat_encoding diamond_vars) zero_left zero_right)
    = false /\
  fmem nat_encoding 8 (join (zero_lattice nat_encoding diamond_vars) zero_left zero_right) = true /\
  fmem nat_encoding 9 (join (zero_lattice nat_encoding diamond_vars) zero_left zero_right) = false.
Proof.
  vm_compute; auto.
Qed.

Definition diamond_copies : copy_view nat unit nat nat nat unit :=
  CopyView diamond_vars (fun e => match e with 0 => [(0, 1)] | _ => [] end).

Definition copied_partition : partition nat_encoding :=
  equality_transfer nat_encoding diamond_copies 0 (top_value (partition_top nat_encoding)).

Example equality_generates_copy :
  fst (partition_test nat_encoding 0 1 copied_partition) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example equality_forgets_write :
  fst (partition_test nat_encoding 0 1
    (equality_transfer nat_encoding diamond_copies 2 copied_partition)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition expressions : genkill_view nat unit nat nat nat unit :=
  GenKillView diamond_view (fun e => match e with 0 | 4 => [7] | _ => [] end)
    (fun _ _ => false) (fun _ _ => Some tt).

Definition motion : lcm_result nat nat nat :=
  LcmResult (fun e => match e with 1 => [7] | _ => [] end)
    (fun n => match n with 3 => [7] | _ => [] end).

Definition extended_expressions : genkill_view nat unit nat nat nat unit :=
  GenKillView diamond_view (fun e => gen expressions e ++ insert motion e)
    (kill expressions) (uval expressions).

Definition avail : nat -> avail_set nat_encoding expressions :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (avail_lattice nat_encoding expressions) (finite_must_laws _ _)
    (rpo_scheduler nat_encoding (available_system nat_encoding expressions)
      (forward_static _ _ _)) Joining
    (available_system nat_encoding expressions) (forward_static _ _ _)
    (inhabits (base_height (finite_must_height _ _
      (FinSet.elements_nodup _ _ (FinSet.wf_fold_add _ _ _ (Map.wf_empty _))))))).

Definition busy : nat -> avail_set nat_encoding expressions :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (avail_lattice nat_encoding expressions) (finite_must_laws _ _)
    (rpo_scheduler nat_encoding (busy_system nat_encoding expressions)
      (backward_static _ _ _)) Joining
    (busy_system nat_encoding expressions) (backward_static _ _ _)
    (inhabits (base_height (finite_must_height _ _
      (FinSet.elements_nodup _ _ (FinSet.wf_fold_add _ _ _ (Map.wf_empty _))))))).

Definition avail2 : nat -> avail_set nat_encoding extended_expressions :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (avail_lattice nat_encoding extended_expressions) (finite_must_laws _ _)
    (rpo_scheduler nat_encoding (available_system nat_encoding extended_expressions)
      (forward_static _ _ _)) Joining
    (available_system nat_encoding extended_expressions) (forward_static _ _ _)
    (inhabits (base_height (finite_must_height _ _
      (FinSet.elements_nodup _ _ (FinSet.wf_fold_add _ _ _ (Map.wf_empty _))))))).

Local Definition available_run (gk : genkill_view nat unit nat nat nat unit) :
    nat -> avail_set nat_encoding gk :=
  lookup nat_encoding (avail_lattice nat_encoding gk)
    (computed_map nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
      (avail_lattice nat_encoding gk)
      (rpo_scheduler nat_encoding (available_system nat_encoding gk) (forward_static _ _ _))
      (available_system nat_encoding gk) (forward_static _ _ _)).

Local Definition busy_run : nat -> avail_set nat_encoding expressions :=
  lookup nat_encoding (avail_lattice nat_encoding expressions)
    (computed_map nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
      (avail_lattice nat_encoding expressions)
      (rpo_scheduler nat_encoding (busy_system nat_encoding expressions) (backward_static _ _ _))
      (busy_system nat_encoding expressions) (backward_static _ _ _)).

Local Lemma avail_computation : avail = available_run expressions.
Proof.
  apply total_computation; vm_compute; reflexivity.
Qed.

Local Lemma busy_computation : busy = busy_run.
Proof.
  apply total_computation; vm_compute; reflexivity.
Qed.

Local Lemma avail2_computation : avail2 = available_run extended_expressions.
Proof.
  apply total_computation; vm_compute; reflexivity.
Qed.

Example available_join_requires_both_arms : fmem nat_encoding 7 (avail 3) = false.
Proof.
  rewrite avail_computation; vm_compute; reflexivity.
Qed.

Example insertion_completes_availability : fmem nat_encoding 7 (avail2 3) = true.
Proof.
  rewrite avail2_computation; vm_compute; reflexivity.
Qed.

Example diamond_lcm_accepts : lcm_check nat_encoding expressions avail busy avail2 motion = true.
Proof.
  rewrite avail_computation, busy_computation, avail2_computation; vm_compute; reflexivity.
Qed.

Definition premature_deletion : lcm_result nat nat nat :=
  LcmResult (insert motion) (fun n => match n with 0 => [7] | _ => [] end).

Example lcm_rejects_unavailable_deletion :
  lcm_check nat_encoding expressions avail busy avail2 premature_deletion = false.
Proof.
  rewrite avail_computation, busy_computation, avail2_computation; vm_compute; reflexivity.
Qed.

Definition redundant_insertion : lcm_result nat nat nat :=
  LcmResult (fun e => match e with 2 => [7] | _ => [] end) (delete motion).

Example lcm_rejects_already_available_insertion :
  lcm_check nat_encoding expressions avail busy avail2 redundant_insertion = false.
Proof.
  rewrite avail_computation, busy_computation, avail2_computation; vm_compute; reflexivity.
Qed.
