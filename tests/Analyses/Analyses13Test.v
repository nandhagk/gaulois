(** * Sparse liveness computations

    These cases materialize complete sparse results on strict and general point models.
    For example, an unreachable exit use propagates backwards inside its unreachable component.
    Builds on: AnalysesSsaLiveSets, Analyses11Test, Analyses12Test and ViewsVIEW8. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesModel RulesSolve RulesJoin
  RulesDelta.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesSsaLiveQuery
  AnalysesSsaLiveSets.
From Gaulois.Tests.Views Require Import ViewsVIEW8.
From Gaulois.Tests.Analyses Require Import Analyses11Test Analyses12Test.
Import List.ListNotations.

(** * Uses precede kills, including duplicate operands *)

Definition sparse_same_edge :=
  sparse_live_materialize bool_encoding unit_encoding nat_encoding same_edge_uses.

Example sparse_same_edge_use_before_def :
  map (fun n => sparse_live_at bool_encoding nat_encoding sparse_same_edge n 0) [false; true] =
    [true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition sparse_duplicate_uses : point_uses bool unit nat :=
  PointUses (live_graph same_edge_uses) (fun _ => [0; 0; 0]) (fun _ => [0; 0]) (fun _ => []).

Example sparse_duplicate_operands_agree :
  sparse_live_materialize bool_encoding unit_encoding nat_encoding sparse_duplicate_uses =
    sparse_same_edge.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_empty_and_absent :
  sparse_live_materialize bool_encoding unit_encoding nat_encoding
    (PointUses (live_graph same_edge_uses) (fun _ => []) (fun _ => [99]) (fun _ => [])) =
    Map.empty /\
  sparse_live_at nat_encoding nat_encoding Map.empty 99 99 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Parallel phi edges, loop phi and unreachable points *)

Definition sparse_fixture := sparse_live_materialize fixture_point_encoding
  live_fixture_edge_encoding live_fixture_value_encoding fixture_uses.
Definition sparse_fixture_query :=
  sparse_live_at fixture_point_encoding live_fixture_value_encoding sparse_fixture.
Definition sparse_fixture_names := [InputLeft; InputRight; PhiValue; NextValue; UndefinedDead].

Example sparse_all_fixture_rows :
  map (fun n => map (sparse_fixture_query n) sparse_fixture_names) (Graph.nodes fixture_graph) =
    [[false; false; false; false; false];
     [true; true; false; false; false];
     [true; true; false; false; false];
     [false; false; false; false; false];
     [false; false; true; false; false];
     [false; false; true; true; false];
     [false; false; false; false; true];
     [false; false; false; false; true]].
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_parallel_phi_is_edge_specific :
  let changed := sparse_live_materialize fixture_point_encoding live_fixture_edge_encoding
    live_fixture_value_encoding (point_model live_changed_points) in
  edge_use fixture_uses LeftPhi = [InputLeft] /\
  edge_use fixture_uses RightPhi = [InputRight] /\
  sparse_fixture_query EntryAfter InputRight = true /\
  sparse_live_at fixture_point_encoding live_fixture_value_encoding changed
    EntryAfter InputRight = false.
Proof.
  vm_compute; repeat split.
Qed.

Example sparse_loop_phi_stops_at_parameter_definition :
  map (sparse_fixture_query LoopBefore) [PhiValue; NextValue] = [false; false] /\
  map (sparse_fixture_query LoopAfter) [PhiValue; NextValue] = [true; true].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example sparse_unreachable_component_is_live :
  sparse_fixture_query DeadBefore UndefinedDead = true /\
  sparse_fixture_query DeadAfter UndefinedDead = true /\
  FinSet.mem fixture_point_encoding DeadBefore
    (visited (query_dfs live_fixture_graph)) = false.
Proof.
  vm_compute; repeat split.
Qed.

Example sparse_fixture_fast_query_agreement n x : reachable fixture_graph n ->
  sparse_fixture_query n x = live_fixture_query n x.
Proof.
  apply (sparse_live_query_agrees fixture_point_encoding live_fixture_edge_encoding
    live_fixture_value_encoding fixture_ssa fixture_ssa_laws fixture_reachable_ssa fixture_ready).
Qed.

Example sparse_reachable_fixture_query_bits :
  map (fun n => map (sparse_fixture_query n) sparse_fixture_names)
    [EntryBefore; EntryBody; EntryAfter; LoopBefore; LoopBody; LoopAfter] =
  map (fun n => map (live_fixture_query n) sparse_fixture_names)
    [EntryBefore; EntryBody; EntryAfter; LoopBefore; LoopBody; LoopAfter].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Self-loops and irreducible components *)

Definition sparse_self_uses : point_uses bool bool nat :=
  PointUses live_self_graph (fun e => if e then [0] else [])
    (fun e => if e then [] else [0]) (fun _ => []).

Example sparse_self_loop :
  let m := sparse_live_materialize bool_encoding bool_encoding nat_encoding sparse_self_uses in
  sparse_live_at bool_encoding nat_encoding m true 0 = true /\
  sparse_live_at bool_encoding nat_encoding m false 0 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition sparse_irreducible := sparse_live_materialize nat_encoding nat_encoding nat_encoding
  live_irreducible_uses.
Definition sparse_irreducible_query := sparse_live_at nat_encoding nat_encoding sparse_irreducible.

Example sparse_irreducible_all_rows :
  map (fun n => map (sparse_irreducible_query n) [0; 1; 99])
    (Graph.nodes live_irreducible_graph) =
    [[false; false; false]; [true; false; false]; [true; false; false];
     [true; false; false]; [true; false; false]; [true; false; false]].
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_irreducible_fast_query_agreement n x :
  In n (Graph.nodes live_irreducible_graph) ->
  sparse_irreducible_query n x = live_irreducible_query n x.
Proof.
  intro Hnode; apply (sparse_live_query_agrees nat_encoding nat_encoding nat_encoding
    live_irreducible_ssa irreducible_point_laws irreducible_reachable_ssa irreducible_ready).
  apply irreducible_all_reachable; exact Hnode.
Qed.

Example sparse_non_strict_same_edge_use :
  let m := sparse_live_materialize nat_encoding nat_encoding nat_encoding
    (point_model live_bad_points) in
  sparse_live_at nat_encoding nat_encoding m 0 0 = true /\
  sparse_irreducible_query 0 0 = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Trap, stop and return exit operands *)

(* Nodes 1 and 2 are respectively trap and resource-stop exits; 3 is an unreachable return. *)
Definition sparse_exit_graph : Graph.t nat bool :=
  Graph.Make [0] [0; 1; 2; 3]
    (fun n => match n with 0 => [false; true] | _ => [] end) (fun _ => 0)
    (fun e => if e then 2 else 1).

Definition sparse_exit_uses : point_uses nat bool nat :=
  PointUses sparse_exit_graph (fun _ => []) (fun _ => [])
    (fun n => match n with 1 => [10; 10] | 2 => [11] | 3 => [12] | _ => [] end).

Definition sparse_exit_vars : var_view nat unit nat bool nat unit :=
  VarView (GraphView sparse_exit_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (edge_use sparse_exit_uses) (edge_def sparse_exit_uses) (exit_use sparse_exit_uses)
    (fun _ _ => tt).

Example sparse_exit_graph_ready : ready nat_encoding sparse_exit_graph
    (prepare nat_encoding sparse_exit_graph).
Proof.
  apply prepare_ready.
  - constructor.
    + repeat constructor; cbn; intuition congruence.
    + intros n [<-|[]]; cbn; auto.
    + intros [|n] e Hin; cbn in Hin; [reflexivity|contradiction].
    + intros [|n] [] _ Hin; cbn in *; intuition congruence.
  - intros [|n]; cbn; repeat constructor; cbn; intuition congruence.
Qed.

Definition sparse_exits := sparse_live_materialize nat_encoding bool_encoding nat_encoding
  sparse_exit_uses.

Example sparse_exit_and_unused_bits :
  map (fun n => map (sparse_live_at nat_encoding nat_encoding sparse_exits n) [10; 11; 12; 99])
    [0; 1; 2; 3; 99] =
    [[true; true; false; false]; [true; false; false; false];
     [false; true; false; false]; [false; false; true; false]; [false; false; false; false]].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Full computations of the actual least Rules solution *)

Local Definition sparse_rule_rows {S O N E V C} (EN : encoding N) (EV : encoding V)
    (vv : var_view S O N E V C) ns xs db :=
  map (fun n => map (fun x => fmem EV x (live_of_db EN EV vv db n)) xs) ns.

Local Lemma sparse_rule_rows_agree {S O N E V C} (EN : encoding N) (EV : encoding V)
    (vv : var_view S O N E V C) ns xs db db' :
  (forall p ts, db_holds liveness_program db p ts = db_holds liveness_program db' p ts) ->
  sparse_rule_rows EN EV vv ns xs db = sparse_rule_rows EN EV vv ns xs db'.
Proof.
  intros Hdb; unfold sparse_rule_rows; apply map_ext; intro n; apply map_ext; intro x.
  unfold live_of_db.
  assert (Hfilter : filter (fun y => db_holds liveness_program db PLive (args2 EN EV n y))
      (var_universe EV vv) =
    filter (fun y => db_holds liveness_program db' PLive (args2 EN EV n y))
      (var_universe EV vv)) by (apply filter_ext; intro y; apply Hdb).
  rewrite Hfilter; reflexivity.
Qed.

Local Lemma sparse_rules_computation {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) ns xs answer :
  option_map (sparse_rule_rows EN EV vv ns xs)
    (delta_bounded_program IndexedNested liveness_program (extract_live_facts EN EE EV vv) 32) =
      Some answer ->
  option_map (sparse_rule_rows EN EV vv ns xs)
    (solve_program liveness_program (extract_live_facts EN EE EV vv)) = Some answer.
Proof.
  apply Analyses11Test.rules_computation.
  - split; [exact (proj1 AnalysesRules.analysis_programs_rules_wf)|
      apply AnalysesRules.live_facts_arity].
  - exists AnalysesRules.analysis_strata; exact (proj1 AnalysesRules.analysis_programs_stratified).
  - apply sparse_rule_rows_agree.
Qed.

Example sparse_loop_and_unreachable_match_computed_rules :
  option_map (sparse_rule_rows fixture_point_encoding live_fixture_value_encoding
    live_fixture_vars (Graph.nodes fixture_graph) sparse_fixture_names)
    (solve_program liveness_program (extract_live_facts fixture_point_encoding
      live_fixture_edge_encoding live_fixture_value_encoding live_fixture_vars)) =
  Some (map (fun n => map (sparse_fixture_query n) sparse_fixture_names)
    (Graph.nodes fixture_graph)).
Proof.
  apply sparse_rules_computation; vm_compute; reflexivity.
Qed.

Example sparse_irreducible_matches_computed_rules :
  option_map (sparse_rule_rows nat_encoding nat_encoding live_irreducible_vars
    (Graph.nodes live_irreducible_graph) [0; 1; 99])
    (solve_program liveness_program (extract_live_facts nat_encoding nat_encoding nat_encoding
      live_irreducible_vars)) =
  Some (map (fun n => map (sparse_irreducible_query n) [0; 1; 99])
    (Graph.nodes live_irreducible_graph)).
Proof.
  apply sparse_rules_computation; vm_compute; reflexivity.
Qed.

Example sparse_exits_match_computed_rules :
  option_map (sparse_rule_rows nat_encoding nat_encoding sparse_exit_vars [0; 1; 2; 3] [10; 11; 12])
    (solve_program liveness_program (extract_live_facts nat_encoding bool_encoding nat_encoding
      sparse_exit_vars)) =
  Some (map (fun n => map (sparse_live_at nat_encoding nat_encoding sparse_exits n) [10; 11; 12])
    [0; 1; 2; 3]).
Proof.
  apply sparse_rules_computation; vm_compute; reflexivity.
Qed.

Example sparse_actual_rules_least_dense_comparison db :
  solve_program liveness_program (extract_live_facts nat_encoding bool_encoding nat_encoding
    sparse_exit_vars) = Some db ->
  forall n x, In n (Graph.nodes sparse_exit_graph) ->
    sparse_live_at nat_encoding nat_encoding sparse_exits n x =
      fmem nat_encoding x (live_of_db nat_encoding nat_encoding sparse_exit_vars db n).
Proof.
  intro Hsolve; apply (sparse_live_materialize_dense nat_encoding bool_encoding nat_encoding
    sparse_exit_vars (live_of_db nat_encoding nat_encoding sparse_exit_vars db)
    sparse_exit_graph_ready).
  exact (rules_liveness_least nat_encoding bool_encoding nat_encoding sparse_exit_vars db
    (proj1 sparse_exit_graph_ready) Hsolve).
Qed.
