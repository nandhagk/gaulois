(** * Call-index observations and the malformed-view boundary

    These examples check exact duplicate order and prepared argument-position facts.
    For example, a repeated target contributes its actual argument twice to a decimal fold.
    Builds on: AnalysesCallScc, AnalysesCalls, ViewsSummary and OrderBasic. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderMonotone.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointIndex
  FixpointTotal FixpointLeast.
From Gaulois.Views Require Import ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesCalls AnalysesCallScc.
Import List.ListNotations.

Definition ana8a_sites (f : nat) : list nat :=
  match f with
  | 0 => [10; 11; 10]
  | 1 => [12]
  | 2 => [13]
  | _ => []
  end.

Definition ana8a_caller (p : nat) : nat :=
  match p with
  | 12 => 1
  | 13 => 2
  | _ => 0
  end.

Definition ana8a_targets (p : nat) : list nat :=
  match p with
  | 10 => [1; 1; 0]
  | 11 => [1]
  | 12 => [0; 1]
  | 13 => [3]
  | _ => [9; 0; 9]
  end.

Definition ana8a_view : calls_view unit nat nat :=
  CallsView [0; 1; 2; 3] [0] ana8a_sites ana8a_caller (fun _ => 0) (fun _ => []).

Definition ana8a_index : call_index nat nat :=
  prepare_calls nat_encoding nat_encoding ana8a_view ana8a_targets.

Example ana8a_duplicate_targets : indexed_targets ana8a_index 10 = [1; 1; 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_unknown_fallback : indexed_targets ana8a_index 99 = [9; 0; 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_multiple_callers :
  indexed_callers ana8a_index 1 = [10; 10; 11; 10; 10; 12].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_duplicate_sites : indexed_callers ana8a_index 0 = [10; 10; 12].
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana8a_arguments : args_view unit nat nat nat unit :=
  ArgsView (fun p => match p with
    | 10 => [2; 3]
    | 11 => [5]
    | 12 => [7; 11]
    | _ => []
    end) (fun _ => []) (fun _ _ => None).

Definition ana8a_order_sensitive : lattice N :=
  {| bot := 0%N;
     leb := N.leb;
     join := fun a b => (10 * a + b)%N;
     widen := N.max;
     narrow := fun a _ => a |}.

Definition ana8a_facts : nat -> nat -> N :=
  arg_facts_indexed nat_encoding ana8a_arguments
    (callers_index nat_encoding ana8a_view ana8a_targets)
    ana8a_order_sensitive N.of_nat.

Example ana8a_exact_argument_order : ana8a_facts 1 0 = 225227%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_missing_positions : ana8a_facts 1 1 = 33341%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_outside_position : ana8a_facts 1 2 = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_absent_caller : ana8a_facts 99 0 = 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana8a_components :=
  call_scc_scheduler nat_encoding (call_graph ana8a_view ana8a_targets).

Example ana8a_mutual_component :
  Pos.eqb (priority ana8a_components 0) (priority ana8a_components 1) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_disconnected_callee_first :
  Pos.ltb (priority ana8a_components 3) (priority ana8a_components 2) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Finite observations do not determine the global raw-graph premise *)

Definition ana8a_empty_view : calls_view unit nat unit :=
  CallsView [0] [0] (fun _ => []) (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_hidden_view : calls_view unit nat unit :=
  CallsView [0] [0] (fun f => if Nat.eqb f 1 then [tt] else [])
    (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_hidden_resolve (_ : unit) : list nat := [0].

Definition ana8a_observed (cv : calls_view unit nat unit) :=
  (functions cv, roots cv, map (sites_of cv) (functions cv),
    map (fun f => map (fun p => (caller_of cv p, ana8a_hidden_resolve p)) (sites_of cv f))
      (functions cv)).

Example ana8a_same_listed_observations :
  ana8a_observed ana8a_empty_view = ana8a_observed ana8a_hidden_view.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_same_prepared_calls :
  prepare_calls nat_encoding unit_encoding ana8a_empty_view ana8a_hidden_resolve =
    prepare_calls nat_encoding unit_encoding ana8a_hidden_view ana8a_hidden_resolve.
Proof.
  reflexivity.
Qed.

Example ana8a_same_component_graph :
  call_scc_graph nat_encoding (call_graph ana8a_empty_view ana8a_hidden_resolve) =
    call_scc_graph nat_encoding (call_graph ana8a_hidden_view ana8a_hidden_resolve).
Proof.
  reflexivity.
Qed.

Example ana8a_empty_graph_wf : graph_wf (call_graph ana8a_empty_view ana8a_hidden_resolve).
Proof.
  constructor.
  - repeat constructor; cbn; tauto.
  - intros f Hf; exact Hf.
  - intros f e Hedge; contradiction.
  - intros f e Hf Hedge; contradiction.
Qed.

Example ana8a_hidden_edge_observation :
  map (Graph.source (call_graph ana8a_hidden_view ana8a_hidden_resolve))
    (Graph.out (call_graph ana8a_hidden_view ana8a_hidden_resolve) 1) = [0].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_hidden_graph_not_wf :
  ~ graph_wf (call_graph ana8a_hidden_view ana8a_hidden_resolve).
Proof.
  intro Hwf.
  pose proof (out_source Hwf 1 (CallEdge tt 0) (or_introl eq_refl)) as Hsource.
  discriminate Hsource.
Qed.

Definition ana8a_seed : summary_spec nat unit bool :=
  SummarySpec bool_lattice (fun _ => true) (fun _ _ a => a).

Example ana8a_same_retained_equations :
  summary_system ana8a_empty_view ana8a_hidden_resolve ana8a_seed =
    summary_system ana8a_hidden_view ana8a_hidden_resolve ana8a_seed.
Proof.
  reflexivity.
Qed.

Example ana8a_same_zero_context_equations :
  callstring_system 0 ana8a_empty_view ana8a_hidden_resolve ana8a_seed =
    callstring_system 0 ana8a_hidden_view ana8a_hidden_resolve ana8a_seed.
Proof.
  reflexivity.
Qed.

Example ana8a_root_seed_observation :
  Query.eval
    (System.rhs (callstring_system 0 ana8a_empty_view ana8a_hidden_resolve ana8a_seed)
      (SLocal 0, [])) (fun _ => false) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_root_postsolution_nonbottom sigma :
  post_solution bool_lattice
    (callstring_system 0 ana8a_empty_view ana8a_hidden_resolve ana8a_seed) sigma ->
  sigma (0, []) = true.
Proof.
  intro Hpost.
  pose proof (proj1 (Hpost (SLocal 0, []) (or_introl eq_refl))) as Hroot.
  change (sigma (0, []) = true) in Hroot; exact Hroot.
Qed.

(** * Exact finite-check boundaries *)

Definition ana8a_duplicate_view : calls_view unit nat unit :=
  CallsView [0; 0] [0] (fun _ => []) (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_root_missing_view : calls_view unit nat unit :=
  CallsView [0] [1] (fun _ => []) (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_wrong_source_view : calls_view unit nat unit :=
  CallsView [0] [0] (fun f => if Nat.eqb f 0 then [tt] else [])
    (fun _ => 1) (fun _ => 0) (fun _ => []).

Definition ana8a_missing_target_view : calls_view unit nat unit :=
  CallsView [0] [0] (fun f => if Nat.eqb f 0 then [tt] else [])
    (fun _ => 0) (fun _ => 0) (fun _ => []).

Example ana8a_duplicate_functions_rejected :
  call_listed_check nat_encoding (call_graph ana8a_duplicate_view ana8a_hidden_resolve) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_unlisted_root_rejected :
  call_listed_check nat_encoding (call_graph ana8a_root_missing_view ana8a_hidden_resolve) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_inconsistent_source_rejected :
  call_listed_check nat_encoding (call_graph ana8a_wrong_source_view ana8a_hidden_resolve) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_unlisted_target_rejected :
  call_listed_check nat_encoding (call_graph ana8a_missing_target_view (fun _ => [1])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_empty_targets_accept_wrong_caller :
  call_listed_check nat_encoding (call_graph ana8a_wrong_source_view (fun _ => [])) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_hidden_pair_both_accepted :
  (call_listed_check nat_encoding (call_graph ana8a_empty_view ana8a_hidden_resolve),
   call_listed_check nat_encoding (call_graph ana8a_hidden_view ana8a_hidden_resolve)) =
    (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example ana8a_parallel_lists_accepted :
  call_listed_check nat_encoding (call_graph ana8a_view ana8a_targets) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Probes of the actual public engines *)

Definition ana8a_bool_height : inhabited (height bool_lattice) :=
  inhabits (base_height bool_height).

Definition ana8a_bool_spec (local_fact : nat -> bool) : summary_spec nat nat bool :=
  SummarySpec bool_lattice local_fact (fun _ _ a => a).

Definition ana8a_summary_probe {P} (EP : encoding P) (cv : calls_view unit nat P)
    resolve (sp : summary_spec nat P bool) (fuel : positive) : Map.t nat bool :=
  let targets := indexed_targets (prepare_calls nat_encoding EP cv resolve) in
  let sys := summary_system cv targets sp in
  let stat := summary_static cv targets sp in
  match run_worklist nat_encoding (summary_constraint_encoding nat_encoding EP) bool_lattice
    (call_scc_scheduler nat_encoding (call_graph cv targets)) Joining sys
    (Declared stat (index_system nat_encoding sys stat)) fuel with
  | Some m => m
  | None => Map.empty
  end.

Definition ana8a_recursive_spec := ana8a_bool_spec (fun f => Nat.eqb f 1).
Definition ana8a_recursive_map :=
  ana8a_summary_probe nat_encoding ana8a_view ana8a_targets ana8a_recursive_spec 64.

Example ana8a_mutual_with_base_and_disconnected :
  map (solve_scc_summaries nat_encoding nat_encoding ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height) [0; 1; 2; 3] = [true; true; false; false].
Proof.
  assert (Hagree : forall f, solve_scc_summaries nat_encoding nat_encoding ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height f = lookup nat_encoding bool_lattice
      ana8a_recursive_map f).
  { apply call_summary_probe with (fuel := 64%positive).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity. }
  cbn [map]; rewrite !Hagree; vm_compute; reflexivity.
Qed.

Definition ana8a_self_view : calls_view unit nat nat :=
  CallsView [0; 1] [0] (fun f => if Nat.eqb f 0 then [0] else [])
    (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_self_spec := ana8a_bool_spec (fun f => Nat.eqb f 0).
Definition ana8a_self_map :=
  ana8a_summary_probe nat_encoding ana8a_self_view (fun _ => [0]) ana8a_self_spec 16.

Example ana8a_self_recursion_has_base :
  solve_scc_summaries nat_encoding nat_encoding ana8a_self_view (fun _ => [0])
    ana8a_self_spec bool_laws ana8a_bool_height 0 = true.
Proof.
  transitivity (lookup nat_encoding bool_lattice ana8a_self_map 0).
  - apply call_summary_probe with (fuel := 16%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Definition ana8a_disconnected_spec := ana8a_bool_spec (fun f => Nat.eqb f 3).
Definition ana8a_disconnected_map :=
  ana8a_summary_probe nat_encoding ana8a_view ana8a_targets ana8a_disconnected_spec 64.

Example ana8a_callee_component_stabilizes_first :
  map (solve_scc_summaries nat_encoding nat_encoding ana8a_view ana8a_targets
    ana8a_disconnected_spec bool_laws ana8a_bool_height) [0; 1; 2; 3] = [false; false; true; true].
Proof.
  assert (Hagree : forall f, solve_scc_summaries nat_encoding nat_encoding ana8a_view ana8a_targets
    ana8a_disconnected_spec bool_laws ana8a_bool_height f = lookup nat_encoding bool_lattice
      ana8a_disconnected_map f).
  { apply call_summary_probe with (fuel := 64%positive); vm_compute; reflexivity. }
  cbn [map]; rewrite !Hagree; vm_compute; reflexivity.
Qed.

Definition ana8a_fallback_map : Map.t nat bool :=
  Map.set nat_encoding 0 true Map.empty.

Example ana8a_rejected_summary_retains_original_nonbottom_seed :
  solve_scc_summaries nat_encoding unit_encoding ana8a_duplicate_view ana8a_hidden_resolve
    ana8a_seed bool_laws ana8a_bool_height 0 = true.
Proof.
  rewrite call_summary_rejected by (vm_compute; reflexivity).
  destruct (solve_total_run nat_encoding (summary_constraint_encoding nat_encoding unit_encoding)
    bool_lattice (summary_system ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed)
    (Scheduler (fun _ => 1%positive) (fun _ => false)) Joining bool_laws
    (summary_static ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed) ana8a_bool_height)
    as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m [Hrun Hagree]].
  assert (Hprobe : run_worklist nat_encoding
    (summary_constraint_encoding nat_encoding unit_encoding) bool_lattice
    (Scheduler (fun _ => 1%positive) (fun _ => false)) Joining
    (summary_system ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed)
    (Declared (summary_static ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed)
      (index_system nat_encoding
        (summary_system ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed)
        (summary_static ana8a_duplicate_view ana8a_hidden_resolve ana8a_seed))) 8 =
      Some ana8a_fallback_map).
  { vm_compute; reflexivity. }
  pose proof (total_completed_runs_unique _ _ _ _ _ _ _ _ _ _ _ Hrun Hprobe) as Hsame.
  rewrite Hsame in Hagree; exact (f_equal (fun s : nat -> bool => s 0) Hagree).
Qed.

Example ana8a_rejected_contexts_bottom k x :
  solve_reachable_callstrings nat_encoding unit_encoding k ana8a_duplicate_view ana8a_hidden_resolve
    ana8a_seed bool_laws ana8a_bool_height x = false.
Proof.
  apply call_context_rejected; vm_compute; reflexivity.
Qed.

Definition ana8a_context_probe_map {P} (EP : encoding P) k (cv : calls_view unit nat P)
    resolve (sp : summary_spec nat P bool) (fuel : positive) : Map.t (nat * list P) bool :=
  let targets := indexed_targets (prepare_calls nat_encoding EP cv resolve) in
  let EX := call_context_encoding nat_encoding EP in
  let EC := pair_encoding (summary_constraint_encoding nat_encoding EP) (list_encoding EP) in
  let graph := call_reachable_graph nat_encoding EP k cv targets in
  let region := call_context_region nat_encoding EP k cv targets in
  let sys := callstring_system k cv targets sp in
  let stat := callstring_static k cv targets sp in
  let sub := call_restrict EX region sys in
  let substat := call_restrict_static EX region sys stat in
  match run_worklist EX EC bool_lattice (call_scc_scheduler EX graph) Joining sub
    (Declared substat (index_system EX sub substat)) fuel with
  | Some m => m
  | None => Map.empty
  end.

Definition ana8a_zero_map := ana8a_context_probe_map nat_encoding 0 ana8a_view ana8a_targets
  ana8a_recursive_spec 64.

Example ana8a_zero_bound_reachable_engine :
  solve_reachable_callstrings nat_encoding nat_encoding 0 ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height (0, []) = true.
Proof.
  transitivity (lookup (call_context_encoding nat_encoding nat_encoding)
    bool_lattice ana8a_zero_map (0, [])).
  - apply call_context_probe with (fuel := 64%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Example ana8a_zero_bound_disconnect_excluded :
  solve_reachable_callstrings nat_encoding nat_encoding 0 ana8a_view ana8a_targets
    ana8a_disconnected_spec bool_laws ana8a_bool_height (3, []) = false.
Proof.
  unfold solve_reachable_callstrings.
  change (call_context_solve nat_encoding nat_encoding 0 ana8a_view
    (indexed_targets (prepare_calls nat_encoding nat_encoding ana8a_view ana8a_targets))
    ana8a_disconnected_spec bool_laws ana8a_bool_height (3, []) = false).
  apply call_context_solve_outside; vm_compute; reflexivity.
Qed.

Definition ana8a_one_map := ana8a_context_probe_map nat_encoding 1 ana8a_view ana8a_targets
  ana8a_recursive_spec 128.

Example ana8a_distinct_caller_contexts :
  (solve_reachable_callstrings nat_encoding nat_encoding 1 ana8a_view ana8a_targets
     ana8a_recursive_spec bool_laws ana8a_bool_height (1, [10]),
   solve_reachable_callstrings nat_encoding nat_encoding 1 ana8a_view ana8a_targets
     ana8a_recursive_spec bool_laws ana8a_bool_height (1, [11])) = (true, true).
Proof.
  assert (Hten : solve_reachable_callstrings nat_encoding nat_encoding 1 ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height (1, [10]) =
      lookup (call_context_encoding nat_encoding nat_encoding) bool_lattice
        ana8a_one_map (1, [10])).
  { apply call_context_probe with (fuel := 128%positive); vm_compute; reflexivity. }
  assert (Heleven : solve_reachable_callstrings nat_encoding nat_encoding 1 ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height (1, [11]) =
      lookup (call_context_encoding nat_encoding nat_encoding) bool_lattice
        ana8a_one_map (1, [11])).
  { apply call_context_probe with (fuel := 128%positive); vm_compute; reflexivity. }
  rewrite Hten, Heleven; vm_compute; reflexivity.
Qed.

Example ana8a_long_context_bottom :
  solve_reachable_callstrings nat_encoding nat_encoding 1 ana8a_view ana8a_targets
    ana8a_recursive_spec bool_laws ana8a_bool_height (1, [10; 11]) = false.
Proof.
  unfold solve_reachable_callstrings.
  change (call_context_solve nat_encoding nat_encoding 1 ana8a_view
    (indexed_targets (prepare_calls nat_encoding nat_encoding ana8a_view ana8a_targets))
    ana8a_recursive_spec bool_laws ana8a_bool_height (1, [10; 11]) = false).
  apply call_context_solve_outside; vm_compute; reflexivity.
Qed.

Example ana8a_context_bound_retains_latest : push_ctx 2 11 [10; 12] = [11; 10].
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana8a_unknown_targets : nat -> list nat :=
  resolver (fun _ => None) (fun _ => @None unit) (fun _ : unit => false)
    (fun _ => None) [0; 1].

Definition ana8a_unknown_map := ana8a_summary_probe nat_encoding ana8a_self_view
  ana8a_unknown_targets (ana8a_bool_spec (fun f => Nat.eqb f 1)) 32.

Example ana8a_unknown_resolver_normal_engine :
  solve_scc_summaries nat_encoding nat_encoding ana8a_self_view ana8a_unknown_targets
    (ana8a_bool_spec (fun f => Nat.eqb f 1)) bool_laws ana8a_bool_height 0 = true.
Proof.
  transitivity (lookup nat_encoding bool_lattice ana8a_unknown_map 0).
  - apply call_summary_probe with (fuel := 32%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Definition ana8a_hidden_map := ana8a_summary_probe unit_encoding ana8a_hidden_view
  ana8a_hidden_resolve ana8a_seed 8.

Example ana8a_hidden_offlist_accepted_engine_nonbottom :
  solve_scc_summaries nat_encoding unit_encoding ana8a_hidden_view ana8a_hidden_resolve
    ana8a_seed bool_laws ana8a_bool_height 0 = true.
Proof.
  transitivity (lookup nat_encoding bool_lattice ana8a_hidden_map 0).
  - apply call_summary_probe with (fuel := 8%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

(** * Weak joins and the separate least-solution gate *)

Inductive ana8a_level : Type :=
  | Ana8aLow
  | Ana8aMiddle
  | Ana8aHigh.

Definition ana8a_level_rank (a : ana8a_level) : nat :=
  match a with
  | Ana8aLow => 0
  | Ana8aMiddle => 1
  | Ana8aHigh => 2
  end.

Definition ana8a_weak_lattice : lattice ana8a_level :=
  {| bot := Ana8aLow;
     leb := fun a b => Nat.leb (ana8a_level_rank a) (ana8a_level_rank b);
     join := fun _ _ => Ana8aHigh;
     widen := fun _ _ => Ana8aHigh;
     narrow := fun a _ => a |}.

Definition ana8a_weak_laws : lattice_laws ana8a_weak_lattice.
Proof.
  constructor; intros; repeat match goal with
  | a : ana8a_level |- _ => destruct a
  end; cbn in *; congruence.
Qed.

Definition ana8a_weak_height : inhabited (height ana8a_weak_lattice).
Proof.
  constructor; refine (@Height ana8a_level ana8a_weak_lattice ana8a_level_rank 2 _ _).
  - intros []; cbn; lia.
  - intros [] [] Hstrict; cbn in *; discriminate || lia.
Qed.

Definition ana8a_weak_seed : summary_spec nat unit ana8a_level :=
  SummarySpec ana8a_weak_lattice (fun _ => Ana8aMiddle) (fun _ _ a => a).

Example ana8a_weak_postsolution :
  post_solution ana8a_weak_lattice (summary_system ana8a_empty_view ana8a_hidden_resolve
    ana8a_weak_seed) (solve_scc_summaries nat_encoding unit_encoding ana8a_empty_view
      ana8a_hidden_resolve ana8a_weak_seed ana8a_weak_laws ana8a_weak_height).
Proof.
  apply solve_scc_summaries_post; exact ana8a_empty_graph_wf.
Qed.

Example ana8a_weak_join_can_overshoot :
  solve_scc_summaries nat_encoding unit_encoding ana8a_empty_view ana8a_hidden_resolve
    ana8a_weak_seed ana8a_weak_laws ana8a_weak_height 0 = Ana8aHigh.
Proof.
  transitivity (lookup nat_encoding ana8a_weak_lattice
    (Map.set nat_encoding 0 Ana8aHigh Map.empty) 0).
  - apply call_summary_probe with (fuel := 8%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Example ana8a_weak_result_is_not_least :
  ~ least_solution ana8a_weak_lattice (summary_system ana8a_empty_view ana8a_hidden_resolve
    ana8a_weak_seed) (solve_scc_summaries nat_encoding unit_encoding ana8a_empty_view
      ana8a_hidden_resolve ana8a_weak_seed ana8a_weak_laws ana8a_weak_height).
Proof.
  intros [Hpost Hleast].
  assert (Hcandidate : post_solution ana8a_weak_lattice
    (summary_system ana8a_empty_view ana8a_hidden_resolve ana8a_weak_seed)
    (fun _ => Ana8aMiddle)).
  { intros [f|p g] Hrow; split; try reflexivity; intros x a Hbad; contradiction. }
  specialize (Hleast _ Hcandidate 0).
  rewrite ana8a_weak_join_can_overshoot in Hleast; discriminate Hleast.
Qed.

Example ana8a_bool_least_under_separate_laws :
  least_solution bool_lattice (summary_system ana8a_empty_view ana8a_hidden_resolve ana8a_seed)
    (solve_scc_summaries nat_encoding unit_encoding ana8a_empty_view ana8a_hidden_resolve
      ana8a_seed bool_laws ana8a_bool_height).
Proof.
  apply solve_scc_summaries_least; [exact ana8a_empty_graph_wf|exact bool_lub|].
  intros [f|p g] Hrow; split.
  - intros s t Hst; apply (leb_refl bool_laws).
  - intros s t Hst x a Hbad; contradiction.
  - intros s t Hst; apply Hst.
  - intros s t Hst x a Hbad; contradiction.
Qed.

Definition ana8a_chain_view : calls_view unit nat nat :=
  CallsView [0; 1] [0] (fun f => if Nat.eqb f 0 then [0] else [])
    (fun _ => 0) (fun _ => 0) (fun _ => []).

Definition ana8a_chain_targets :=
  indexed_targets (prepare_calls nat_encoding nat_encoding ana8a_chain_view (fun _ => [1])).
Definition ana8a_chain_system :=
  summary_system ana8a_chain_view ana8a_chain_targets ana8a_recursive_spec.
Definition ana8a_chain_static :=
  summary_static ana8a_chain_view ana8a_chain_targets ana8a_recursive_spec.
Definition ana8a_chain_schedule :=
  call_scc_scheduler nat_encoding (call_graph ana8a_chain_view ana8a_chain_targets).
Definition ana8a_chain_encoding := summary_constraint_encoding nat_encoding nat_encoding.
Definition ana8a_chain_step := engine_step nat_encoding ana8a_chain_encoding bool_lattice
  ana8a_chain_schedule Joining ana8a_chain_system
  (Declared ana8a_chain_static (index_system nat_encoding ana8a_chain_system ana8a_chain_static)).
Definition ana8a_chain_first := initial_state ana8a_chain_encoding ana8a_chain_schedule
  ana8a_chain_system.

Definition ana8a_chain_next_target (e : Engine.t nat (summary_constraint nat nat) bool) :=
  match PQueue.pop ana8a_chain_encoding (Engine.queue e) with
  | Some (_, c, _) => Some (System.target ana8a_chain_system c)
  | None => None
  end.

Example ana8a_actual_queue_enters_callee_before_caller :
  (ana8a_chain_next_target ana8a_chain_first,
   match ana8a_chain_step ana8a_chain_first with
   | Some e => ana8a_chain_next_target e
   | None => None
   end) = (Some 1, Some 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana8a_hidden_zero_map := ana8a_context_probe_map unit_encoding 0 ana8a_hidden_view
  ana8a_hidden_resolve ana8a_seed 8.

Example ana8a_hidden_pair_reachable_engines_nonbottom :
  (solve_reachable_callstrings nat_encoding unit_encoding 0 ana8a_empty_view ana8a_hidden_resolve
     ana8a_seed bool_laws ana8a_bool_height (0, []),
   solve_reachable_callstrings nat_encoding unit_encoding 0 ana8a_hidden_view ana8a_hidden_resolve
     ana8a_seed bool_laws ana8a_bool_height (0, [])) = (true, true).
Proof.
  assert (Hvalid : solve_reachable_callstrings nat_encoding unit_encoding 0 ana8a_empty_view
    ana8a_hidden_resolve ana8a_seed bool_laws ana8a_bool_height (0, []) =
      lookup (call_context_encoding nat_encoding unit_encoding) bool_lattice
        ana8a_hidden_zero_map (0, [])).
  { apply call_context_probe with (fuel := 8%positive); vm_compute; reflexivity. }
  assert (Hhidden : solve_reachable_callstrings nat_encoding unit_encoding 0 ana8a_hidden_view
    ana8a_hidden_resolve ana8a_seed bool_laws ana8a_bool_height (0, []) =
      lookup (call_context_encoding nat_encoding unit_encoding) bool_lattice
        ana8a_hidden_zero_map (0, [])).
  { apply call_context_probe with (fuel := 8%positive); vm_compute; reflexivity. }
  rewrite Hvalid, Hhidden; vm_compute; reflexivity.
Qed.

Example ana8a_empty_target_wrong_source_uses_selected_engine :
  solve_scc_summaries nat_encoding unit_encoding ana8a_wrong_source_view (fun _ => [])
    ana8a_seed bool_laws ana8a_bool_height 0 = true.
Proof.
  transitivity (lookup nat_encoding bool_lattice (Map.set nat_encoding 0 true Map.empty) 0).
  - apply call_summary_probe with (fuel := 8%positive); vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.
