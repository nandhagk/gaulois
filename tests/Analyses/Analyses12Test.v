(** * R/T liveness query examples

    These cases compute reusable graph and value indexes, including irreducible control flow.
    For example, replacing one parallel phi operand changes its value index while R/T is reused.
    Builds on: AnalysesSsaLiveQuery and the checked VIEW-8 instruction-point fixture. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphDominators GraphReducible.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Rules Require Import RulesSyntax RulesModel RulesSolve.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesSsaLiveQuery.
From Gaulois.Tests.Views Require Import ViewsVIEW8.
Import List.ListNotations.

(** * Branching parallel phi operands and a loop-carried definition *)

Definition live_fixture_edge_encoding : encoding fixture_edge.
Proof.
  refine (Encoding fixture_edge (fun e => match e with
    | EntryParameters => 1%positive
    | EntryInstruction => 2%positive
    | LeftPhi => 3%positive
    | RightPhi => 4%positive
    | LoopParameters => 5%positive
    | LoopInstruction => 6%positive
    | BackPhi => 7%positive
    | DeadParameters => 8%positive
    end) _).
  intros [] [] Hcode; cbn in Hcode; congruence.
Defined.

Definition live_fixture_value_encoding : encoding fixture_value.
Proof.
  refine (Encoding fixture_value (fun x => match x with
    | InputLeft => 1%positive
    | InputRight => 2%positive
    | PhiValue => 3%positive
    | NextValue => 4%positive
    | UndefinedDead => 5%positive
    end) _).
  intros [] [] Hcode; cbn in Hcode; congruence.
Defined.

Definition live_fixture_graph := prepare_ssa_query_graph fixture_point_encoding
  live_fixture_edge_encoding fixture_graph.
Definition live_fixture_values := prepare_ssa_query_values fixture_point_encoding
  live_fixture_value_encoding fixture_ssa.
Definition live_fixture_query := ssa_live_query fixture_point_encoding live_fixture_value_encoding
  live_fixture_graph live_fixture_values.
Definition live_fixture_vars :
    var_view fixture_point unit fixture_point fixture_edge fixture_value unit :=
  VarView (GraphView fixture_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (edge_use fixture_uses) (edge_def fixture_uses) (exit_use fixture_uses) (fun _ _ => tt).

Example branch_parallel_phi_queries :
  map (live_fixture_query EntryAfter) [InputLeft; InputRight; PhiValue; NextValue] =
    [true; true; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_carried_queries :
  map (live_fixture_query LoopAfter) [InputLeft; InputRight; PhiValue; NextValue] =
    [false; false; true; true] /\
  map (live_fixture_query LoopBefore) [PhiValue; NextValue] = [false; false].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example prepared_value_uses_and_definitions :
  FinSet.elements (live_index_get live_fixture_value_encoding InputRight
    (query_uses live_fixture_values)) = [EntryAfter] /\
  Map.get live_fixture_value_encoding PhiValue (query_def live_fixture_values) = Some LoopBefore /\
  Map.get live_fixture_value_encoding UndefinedDead (query_def live_fixture_values) = None.
Proof.
  vm_compute; repeat split.
Qed.

Definition live_changed_points :
    ssa_points fixture_block fixture_block_edge fixture_point fixture_edge fixture_value :=
  SsaPoints (PointUses fixture_graph
    (fun e => match e with RightPhi => [InputLeft] | _ => edge_use fixture_uses e end)
    (edge_def fixture_uses) (exit_use fixture_uses))
    (block_graph fixture_ssa) (points_in_block fixture_ssa) (instruction_edges fixture_ssa)
    (parameter_edge fixture_ssa) (block_of_point fixture_ssa) (block_edge_of fixture_ssa)
    (block_params fixture_ssa)
    (fun e => match e with RightIncoming => [InputLeft] | _ => block_edge_args fixture_ssa e end)
    (point_definition fixture_ssa).

Example graph_index_reused_after_operand_change :
  prepare_ssa_query_graph fixture_point_encoding live_fixture_edge_encoding
    (live_graph (point_model live_changed_points)) = live_fixture_graph /\
  ssa_live_query fixture_point_encoding live_fixture_value_encoding live_fixture_graph
    (prepare_ssa_query_values fixture_point_encoding live_fixture_value_encoding
      live_changed_points)
    EntryAfter InputRight = false /\ live_fixture_query EntryAfter InputRight = true.
Proof.
  split; [reflexivity|vm_compute; split; reflexivity].
Qed.

Example loop_rules_least_comparison : exists db,
  solve_program liveness_program (extract_live_facts fixture_point_encoding
    live_fixture_edge_encoding live_fixture_value_encoding live_fixture_vars) = Some db /\
  map (fun x => fmem live_fixture_value_encoding x
    (live_of_db fixture_point_encoding live_fixture_value_encoding live_fixture_vars db LoopAfter))
    [InputLeft; InputRight; PhiValue; NextValue] = [false; false; true; true].
Proof.
  destruct (rules_liveness_solves fixture_point_encoding live_fixture_edge_encoding
    live_fixture_value_encoding live_fixture_vars fixture_point_graph_wf) as [db Hsolve].
  exists db; split; [exact Hsolve|].
  assert (Hreach : reachable fixture_graph LoopAfter).
  { apply (proj1 (reachable_dfs fixture_point_encoding fixture_graph fixture_prepared LoopAfter
      fixture_ready)); vm_compute; reflexivity. }
  assert (Hsame : forall x, fmem live_fixture_value_encoding x
    (live_of_db fixture_point_encoding live_fixture_value_encoding live_fixture_vars db LoopAfter) =
      live_fixture_query LoopAfter x).
  { intro x; symmetry; apply (ssa_live_query_rules fixture_point_encoding live_fixture_edge_encoding
      live_fixture_value_encoding fixture_ssa live_fixture_vars db);
      try reflexivity; try assumption; try exact fixture_ssa_laws;
      try exact fixture_reachable_ssa; exact fixture_ready. }
  rewrite (map_ext _ _ Hsame); vm_compute; reflexivity.
Qed.

Example general_fallback_preserves_unreachable_use :
  general_live_query fixture_point_encoding live_fixture_edge_encoding live_fixture_value_encoding
    live_fixture_vars DeadBefore UndefinedDead = true.
Proof.
  apply general_live_query_exact; [exact fixture_point_graph_wf|cbn; tauto|].
  exact unreachable_use_is_syntactically_live.
Qed.

(** * A reachable irreducible SCC, with a separate unused definition *)

Definition live_irreducible_graph : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2; 3; 4; 5]
    (fun n => match n with 0 => [0] | 1 => [1; 2] | 2 => [3] | 3 => [4]
      | 4 => [5] | 5 => [6; 7] | _ => [] end)
    (fun e => match e with 0 => 0 | 1 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | _ => 5 end)
    (fun e => match e with 0 => 1 | 1 | 6 => 2 | 2 | 4 | 7 => 4 | 3 => 3 | _ => 5 end).

Definition live_irreducible_uses : point_uses nat nat nat :=
  PointUses live_irreducible_graph
    (fun e => match e with 4 | 7 => [0] | _ => [] end)
    (fun e => match e with 0 => [0; 1] | _ => [] end)
    (fun n => match n with 5 => [0] | _ => [] end).

Definition live_irreducible_blocks : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2]
    (fun n => match n with 0 => [1; 2] | 1 => [4] | 2 => [6; 7] | _ => [] end)
    (fun e => match e with 1 | 2 => 0 | 4 => 1 | _ => 2 end)
    (fun e => match e with 1 | 6 => 1 | _ => 2 end).

Definition live_irreducible_ssa : ssa_points nat nat nat nat nat :=
  SsaPoints live_irreducible_uses live_irreducible_blocks
    (fun b => match b with 0 => [0; 1] | 1 => [2; 3] | _ => [4; 5] end)
    (fun b => match b with 0 => [0] | 1 => [3] | _ => [5] end)
    (fun b => match b with 0 => 0 | 1 => 3 | _ => 5 end)
    (fun n => match n with 0 | 1 => 0 | 2 | 3 => 1 | _ => 2 end)
    (fun e => match e with 0 | 3 | 5 => None | _ => Some e end)
    (fun b => match b with 0 => [0; 1] | _ => [] end) (fun _ => [])
    (fun x => match x with 0 | 1 => Some 0 | _ => None end).

(** Bounded case splits discharge this fixture's finite graph and point inventories. *)
Local Ltac live_small n := destruct n as [|[|[|[|[|[|n]]]]]]; cbn in *.

Local Ltac live_edge e := destruct e as [|[|[|[|[|[|[|[|e]]]]]]]]; cbn in *.

Example irreducible_graph_wf : graph_wf live_irreducible_graph.
Proof.
  constructor.
  - repeat constructor; cbn; intuition lia.
  - intros n [<-|[]]; now left.
  - intros n e He; live_small n; live_edge e; intuition congruence.
  - intros n e Hn He; live_small n; live_edge e; intuition congruence.
Qed.

Example irreducible_out_nodup : forall n, NoDup (Graph.out live_irreducible_graph n).
Proof.
  intro n; live_small n; repeat constructor; cbn; intuition lia.
Qed.

Example irreducible_ready : ready nat_encoding live_irreducible_graph
    (prepare nat_encoding live_irreducible_graph).
Proof.
  apply prepare_ready; [exact irreducible_graph_wf|exact irreducible_out_nodup].
Qed.

Example irreducible_point_laws : ssa_point_laws live_irreducible_ssa.
Proof.
  constructor.
  - exact irreducible_graph_wf.
  - exact irreducible_out_nodup.
  - constructor.
    + repeat constructor; cbn; intuition lia.
    + intros n [<-|[]]; now left.
    + intros n e He; live_small n; live_edge e; intuition congruence.
    + intros n e Hn He; live_small n; live_edge e; intuition congruence.
  - intro n; live_small n; repeat constructor; cbn; intuition lia.
  - intro n; split; intro Hn.
    + live_small n; try solve [intuition lia];
        [exists 0|exists 0|exists 1|exists 1|exists 2|exists 2]; cbn; auto.
    + destruct Hn as [b [Hb Hn]]; live_small b; live_small n; intuition congruence.
  - intro b; live_small b; repeat constructor; cbn; intuition lia.
  - intros b n Hb Hn; live_small b; live_small n; intuition congruence.
  - intros b _; live_small b; discriminate.
  - intros b Hb; live_small b; try solve [intuition lia].
    all: eapply point_chain_step; [now left|reflexivity|apply point_chain_one].
  - intros b e Hb He; live_small b; live_edge e; intuition congruence.
  - intros n e Hn He Hinternal; live_small n; live_edge e; intuition congruence.
  - intros b _; live_small b; reflexivity.
  - intros b x Hb; live_small b; reflexivity.
  - intros n e Hn He; live_small n; live_edge e; intuition congruence.
  - intros be Hbe; unfold edges_of, live_irreducible_blocks in Hbe; cbn in Hbe.
    repeat destruct Hbe as [<-|Hbe]; try contradiction; reflexivity.
  - intros n e be Hn He Hbe x Harg; cbn in Harg; contradiction.
  - intros be Hbe; unfold edges_of, live_irreducible_blocks in Hbe; cbn in Hbe.
    repeat destruct Hbe as [<-|Hbe]; try contradiction.
    + exists 1, 1; cbn; tauto.
    + exists 1, 2; cbn; tauto.
    + exists 3, 4; cbn; tauto.
    + exists 5, 6; cbn; tauto.
    + exists 5, 7; cbn; tauto.
  - intros e1 e2 be _ _ Hfirst Hsecond.
    live_edge e1; live_edge e2; cbn in Hfirst, Hsecond; congruence.
Qed.

Example irreducible_reachable_ssa : reachable_point_ssa live_irreducible_ssa.
Proof.
  constructor.
  - exists 0; reflexivity.
  - intros n x Hreach Huse.
    assert (Hshape : n <> 0 /\ x = 0).
    { destruct Huse as [Hexit|[e [He Huse]]].
      - live_small n; cbn in Hexit; intuition congruence.
      - live_small n; live_edge e; cbn in He, Huse; intuition congruence. }
    destruct Hshape as [Hne ->]; exists 0; split; [reflexivity|split].
    + apply reachable_entry; now left.
    + split.
      * intros root es [Hroot|[]] _; left; exact Hroot.
      * intro Heq; apply Hne; symmetry; exact Heq.
  - intros n e x _ He Hdef.
    destruct e as [|e]; cbn in Hdef; [|contradiction].
    assert (Hn : n = 0) by (live_small n; intuition congruence).
    subst n; destruct Hdef as [<-|[<-|[]]]; reflexivity.
  - intros x d e Hhome _ He.
    destruct x as [|[|x]]; cbn in Hhome; try discriminate;
      inversion Hhome; subst d; cbn in He; destruct He as [<-|[]]; cbn; tauto.
Qed.

Definition live_irreducible_index := prepare_ssa_query_graph nat_encoding nat_encoding
  live_irreducible_graph.
Definition live_irreducible_values := prepare_ssa_query_values nat_encoding nat_encoding
  live_irreducible_ssa.
Definition live_irreducible_query := ssa_live_query nat_encoding nat_encoding
  live_irreducible_index live_irreducible_values.
Definition live_irreducible_vars : var_view nat unit nat nat nat unit :=
  VarView (GraphView live_irreducible_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (edge_use live_irreducible_uses) (edge_def live_irreducible_uses)
    (exit_use live_irreducible_uses) (fun _ _ => tt).

Example reachable_irreducibility :
  map (fun n => FinSet.mem nat_encoding n (visited (query_dfs live_irreducible_index)))
    [0; 1; 2; 3; 4; 5] = [true; true; true; true; true; true] /\
  reducible_b (prepare nat_encoding live_irreducible_graph)
    (query_dom live_irreducible_index) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example irreducible_is_not_reducible : ~ reducible live_irreducible_graph.
Proof.
  intro Hreducible.
  pose proof (proj2 (reducible_b_correct nat_encoding live_irreducible_graph
    (prepare nat_encoding live_irreducible_graph) irreducible_ready
    (dominator_exact_true nat_encoding live_irreducible_graph _ irreducible_ready)) Hreducible)
    as Htest.
  vm_compute in Htest; discriminate.
Qed.

Example irreducible_query_bits :
  map (fun n => map (live_irreducible_query n) [0; 1]) [0; 1; 2; 3; 4; 5] =
    [[false; false]; [true; false]; [true; false]; [true; false]; [true; false]; [true; false]].
Proof.
  vm_compute; reflexivity.
Qed.

Example unused_definition_has_no_value_row :
  point_definition live_irreducible_ssa 1 = Some 0 /\
  Map.get nat_encoding 1 (query_def live_irreducible_values) = None /\
  FinSet.elements (live_index_get nat_encoding 1 (query_uses live_irreducible_values)) = [].
Proof.
  vm_compute; repeat split.
Qed.

Example irreducible_graph_rows :
  FinSet.elements (live_index_get nat_encoding 5 (query_reduced live_irreducible_index)) = [5] /\
  map (fun n => FinSet.mem nat_encoding n
    (live_index_get nat_encoding 5 (query_back_closure live_irreducible_index)))
    [0; 1; 2; 3; 4; 5] = [false; false; true; false; true; true].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example irreducible_all_reachable n :
  In n (Graph.nodes live_irreducible_graph) -> reachable live_irreducible_graph n.
Proof.
  intro Hn; apply (proj1 (reachable_dfs nat_encoding live_irreducible_graph
    (prepare nat_encoding live_irreducible_graph) n irreducible_ready)).
  cbn in Hn; repeat destruct Hn as [<-|Hn]; try contradiction; vm_compute; reflexivity.
Qed.

Example irreducible_rules_least_comparison : exists db,
  solve_program liveness_program (extract_live_facts nat_encoding nat_encoding nat_encoding
    live_irreducible_vars) = Some db /\
  map (fun n => map (fun x => fmem nat_encoding x
      (live_of_db nat_encoding nat_encoding live_irreducible_vars db n)) [0; 1])
    (Graph.nodes live_irreducible_graph) =
    [[false; false]; [true; false]; [true; false]; [true; false]; [true; false]; [true; false]].
Proof.
  destruct (rules_liveness_solves nat_encoding nat_encoding nat_encoding live_irreducible_vars
    irreducible_graph_wf) as [db Hsolve]; exists db; split; [exact Hsolve|].
  transitivity (map (fun n => map (live_irreducible_query n) [0; 1])
    (Graph.nodes live_irreducible_graph)); [|exact irreducible_query_bits].
  apply map_ext_in; intros n Hn; apply map_ext; intro x; symmetry.
  apply (ssa_live_query_rules nat_encoding nat_encoding nat_encoding live_irreducible_ssa
    live_irreducible_vars db); try reflexivity; try assumption;
    try exact irreducible_point_laws; try exact irreducible_reachable_ssa;
    try exact irreducible_ready; apply irreducible_all_reachable; exact Hn.
Qed.

(** * Self-loops, edge identity and the strictness boundary *)

Definition live_self_graph : Graph.t bool bool :=
  Graph.Make [false] [false; true]
    (fun n => if n then [true] else [false]) (fun e => e) (fun _ => true).

Example self_loop_reduced_and_t :
  let idx := prepare_ssa_query_graph bool_encoding bool_encoding live_self_graph in
  FinSet.elements (live_index_get bool_encoding true (query_reduced idx)) = [true] /\
  FinSet.elements (live_index_get bool_encoding true (query_back_closure idx)) = [true] /\
  ancestor_b bool_encoding (query_dfs idx) true true = true.
Proof.
  vm_compute; repeat split.
Qed.

Example self_loop_live_query :
  let idx := prepare_ssa_query_graph bool_encoding bool_encoding live_self_graph in
  let values := SsaQueryValues (Map.set bool_encoding false false Map.empty)
    (Map.set bool_encoding false (FinSet.add bool_encoding true FinSet.empty) Map.empty) in
  ssa_live_query bool_encoding bool_encoding idx values true false = true /\
  ssa_live_query bool_encoding bool_encoding idx values false false = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition live_bad_points : ssa_points nat nat nat nat nat :=
  SsaPoints (PointUses live_irreducible_graph
    (fun e => match e with 0 => [0] | _ => edge_use live_irreducible_uses e end)
    (edge_def live_irreducible_uses) (exit_use live_irreducible_uses))
    live_irreducible_blocks (points_in_block live_irreducible_ssa)
    (instruction_edges live_irreducible_ssa) (parameter_edge live_irreducible_ssa)
    (block_of_point live_irreducible_ssa) (block_edge_of live_irreducible_ssa)
    (block_params live_irreducible_ssa) (block_edge_args live_irreducible_ssa)
    (point_definition live_irreducible_ssa).

Example same_edge_use_definition_rejects_strict_ssa : ~ reachable_point_ssa live_bad_points.
Proof.
  intro Hssa.
  destruct (point_ssa_uses_defined Hssa 0 0 ltac:(constructor; now left)
    ltac:(right; exists 0; cbn; auto)) as [d [Hhome [_ [_ Hne]]]].
  cbn in Hhome; inversion Hhome; subst d; apply Hne; reflexivity.
Qed.

Example same_edge_use_is_retained_by_general_fallback :
  let vv : var_view bool unit bool unit nat unit :=
    VarView (GraphView (live_graph same_edge_uses) id
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (edge_use same_edge_uses) (edge_def same_edge_uses) (exit_use same_edge_uses)
    (fun _ _ => tt) in
  general_live_query bool_encoding unit_encoding nat_encoding vv false 0 = true.
Proof.
  cbn zeta; apply general_live_query_exact.
  - constructor.
    + constructor; [cbn; intros [Hfalse|[]]; discriminate|].
      constructor; [cbn; tauto|constructor].
    + intros n [<-|[]]; now left.
    + intros [] [] He; cbn in *; intuition congruence.
    + intros [] [] _ He; cbn in *; intuition congruence.
  - cbn; auto.
  - exact same_edge_use_is_live.
Qed.
