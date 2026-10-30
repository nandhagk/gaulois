(** * SSA analysis compatibility checks

    These checks compare each compatibility alias with its source declaration.
    For example, the numbering fixture retains its definition through both paths.
    Builds on: ExamplesSsaAnalyses and the routed SSA analysis clients. *)

From Stdlib Require Import ZArith.
From Gaulois.Examples.Ssa Require Import ExamplesSsaTyping ExamplesSsaAnalyses.

(** The old qualified paths compute the same fixture values as their sources. *)
Example compatibility_computations :
  ExamplesSsaAnalyses.gvn_first = 2 /\
  ExamplesSsaAnalyses.count_up_inv 0 = 5%Z /\
  ExamplesSsaAnalyses.chain_reads 0 = nil.
Proof.
  vm_compute; auto.
Qed.

(** The qualified theorem applies to the qualified fixture. *)
Example compatibility_theorem_application :
  wf_program (fun _ _ => None) ExamplesSsaAnalyses.count_up.
Proof.
  exact ExamplesSsaAnalyses.count_up_wf.
Qed.

Example label_encoding_alias :
  @ExamplesSsaAnalyses.label_encoding = @ExamplesSsaAnalysisBase.label_encoding.
Proof.
  reflexivity.
Qed.

Example ssa_bop_code_alias :
  @ExamplesSsaAnalyses.ssa_bop_code = @ExamplesSsaAnalysisBase.ssa_bop_code.
Proof.
  reflexivity.
Qed.

Example ssa_cval_code_alias :
  @ExamplesSsaAnalyses.ssa_cval_code = @ExamplesSsaAnalysisBase.ssa_cval_code.
Proof.
  reflexivity.
Qed.

Example ssa_cval_encoding_alias :
  @ExamplesSsaAnalyses.ssa_cval_encoding = @ExamplesSsaAnalysisBase.ssa_cval_encoding.
Proof.
  reflexivity.
Qed.

Example ssa_sop_code_alias :
  @ExamplesSsaAnalyses.ssa_sop_code = @ExamplesSsaAnalysisBase.ssa_sop_code.
Proof.
  reflexivity.
Qed.

Example sop_encoding_alias :
  @ExamplesSsaAnalyses.sop_encoding = @ExamplesSsaAnalysisBase.sop_encoding.
Proof.
  reflexivity.
Qed.

Example const_numeric_alias :
  @ExamplesSsaAnalyses.const_numeric = @ExamplesSsaAnalysisBase.const_numeric.
Proof.
  reflexivity.
Qed.

Example const_conc_alias :
  @ExamplesSsaAnalyses.const_conc = @ExamplesSsaAnalysisBase.const_conc.
Proof.
  reflexivity.
Qed.

Example liveness_at_alias :
  @ExamplesSsaAnalyses.liveness_at = @ExamplesSsaAnalysisBase.liveness_at.
Proof.
  reflexivity.
Qed.

Example ssa_dead_value_removable_alias :
  @ExamplesSsaAnalyses.ssa_dead_value_removable = @ExamplesSsaAnalysisBase.ssa_dead_value_removable.
Proof.
  reflexivity.
Qed.

Example factorial_ssa_alias :
  @ExamplesSsaAnalyses.factorial_ssa = @ExamplesSsaAnalysisBase.factorial_ssa.
Proof.
  reflexivity.
Qed.

Example z_value_alias :
  @ExamplesSsaAnalyses.z_value = @ExamplesSsaAnalysisBase.z_value.
Proof.
  reflexivity.
Qed.

Example p_value_alias :
  @ExamplesSsaAnalyses.p_value = @ExamplesSsaAnalysisBase.p_value.
Proof.
  reflexivity.
Qed.

Example loop_header_point_alias :
  @ExamplesSsaAnalyses.loop_header_point = @ExamplesSsaAnalysisBase.loop_header_point.
Proof.
  reflexivity.
Qed.

Example ok_i32_alias :
  @ExamplesSsaAnalyses.ok_i32 = @ExamplesSsaAnalysisBase.ok_i32.
Proof.
  reflexivity.
Qed.

Example mul_one_term_alias :
  @ExamplesSsaAnalyses.mul_one_term = @ExamplesSsaAnalysisBase.mul_one_term.
Proof.
  reflexivity.
Qed.

Example mul_one_rules_alias :
  @ExamplesSsaAnalyses.mul_one_rules = @ExamplesSsaAnalysisBase.mul_one_rules.
Proof.
  reflexivity.
Qed.

Example unit_cost_alias :
  @ExamplesSsaAnalyses.unit_cost = @ExamplesSsaAnalysisBase.unit_cost.
Proof.
  reflexivity.
Qed.

Example mul_one_rules_sound_alias :
  @ExamplesSsaAnalyses.mul_one_rules_sound = @ExamplesSsaAnalysisBase.mul_one_rules_sound.
Proof.
  reflexivity.
Qed.

Example ssa_sccp_sound_alias :
  @ExamplesSsaAnalyses.ssa_sccp_sound = @ExamplesSsaAnalysisBase.ssa_sccp_sound.
Proof.
  reflexivity.
Qed.

Example ssa_guard_chain_sound_alias :
  @ExamplesSsaAnalyses.ssa_guard_chain_sound = @ExamplesSsaAnalysisBase.ssa_guard_chain_sound.
Proof.
  reflexivity.
Qed.

Example ssa_andersen_sound_alias :
  @ExamplesSsaAnalyses.ssa_andersen_sound = @ExamplesSsaAnalysisBase.ssa_andersen_sound.
Proof.
  reflexivity.
Qed.

Example ssa_steensgaard_sound_alias :
  @ExamplesSsaAnalyses.ssa_steensgaard_sound = @ExamplesSsaAnalysisBase.ssa_steensgaard_sound.
Proof.
  reflexivity.
Qed.

Example ssa_escape_sound_alias :
  @ExamplesSsaAnalyses.ssa_escape_sound = @ExamplesSsaAnalysisBase.ssa_escape_sound.
Proof.
  reflexivity.
Qed.

Example gvn_pure_alias :
  @ExamplesSsaAnalyses.gvn_pure = @ExamplesSsaNumbering.gvn_pure.
Proof.
  reflexivity.
Qed.

Example gvn_prog_alias :
  @ExamplesSsaAnalyses.gvn_prog = @ExamplesSsaNumbering.gvn_prog.
Proof.
  reflexivity.
Qed.

Example gvn_first_alias :
  @ExamplesSsaAnalyses.gvn_first = @ExamplesSsaNumbering.gvn_first.
Proof.
  reflexivity.
Qed.

Example gvn_second_alias :
  @ExamplesSsaAnalyses.gvn_second = @ExamplesSsaNumbering.gvn_second.
Proof.
  reflexivity.
Qed.

Example gvn_problem_alias :
  @ExamplesSsaAnalyses.gvn_problem = @ExamplesSsaNumbering.gvn_problem.
Proof.
  reflexivity.
Qed.

Example gvn_binding_state_alias :
  @ExamplesSsaAnalyses.gvn_binding_state = @ExamplesSsaNumbering.gvn_binding_state.
Proof.
  reflexivity.
Qed.

Example gvn_binding_observation_alias :
  @ExamplesSsaAnalyses.gvn_binding_observation = @ExamplesSsaNumbering.gvn_binding_observation.
Proof.
  reflexivity.
Qed.

Example gvn_binding_observation_laws_alias :
  @ExamplesSsaAnalyses.gvn_binding_observation_laws =
  @ExamplesSsaNumbering.gvn_binding_observation_laws.
Proof.
  reflexivity.
Qed.

Example gvn_binding_witness_alias :
  @ExamplesSsaAnalyses.gvn_binding_witness = @ExamplesSsaNumbering.gvn_binding_witness.
Proof.
  reflexivity.
Qed.

Example gvn_binding_home_dominates_alias :
  @ExamplesSsaAnalyses.gvn_binding_home_dominates =
  @ExamplesSsaNumbering.gvn_binding_home_dominates.
Proof.
  reflexivity.
Qed.

Example gvn_binding_equal_alias :
  @ExamplesSsaAnalyses.gvn_binding_equal = @ExamplesSsaNumbering.gvn_binding_equal.
Proof.
  reflexivity.
Qed.

Example gvn_use_prog_alias :
  @ExamplesSsaAnalyses.gvn_use_prog = @ExamplesSsaNumbering.gvn_use_prog.
Proof.
  reflexivity.
Qed.

Example gvn_use_problem_alias :
  @ExamplesSsaAnalyses.gvn_use_problem = @ExamplesSsaNumbering.gvn_use_problem.
Proof.
  reflexivity.
Qed.

Example gvn_use_state_alias :
  @ExamplesSsaAnalyses.gvn_use_state = @ExamplesSsaNumbering.gvn_use_state.
Proof.
  reflexivity.
Qed.

Example gvn_use_observation_alias :
  @ExamplesSsaAnalyses.gvn_use_observation = @ExamplesSsaNumbering.gvn_use_observation.
Proof.
  reflexivity.
Qed.

Example gvn_use_observation_laws_alias :
  @ExamplesSsaAnalyses.gvn_use_observation_laws = @ExamplesSsaNumbering.gvn_use_observation_laws.
Proof.
  reflexivity.
Qed.

Example gvn_use_witness_alias :
  @ExamplesSsaAnalyses.gvn_use_witness = @ExamplesSsaNumbering.gvn_use_witness.
Proof.
  reflexivity.
Qed.

Example gvn_use_equal_alias :
  @ExamplesSsaAnalyses.gvn_use_equal = @ExamplesSsaNumbering.gvn_use_equal.
Proof.
  reflexivity.
Qed.

Example gvn_phi_prog_alias :
  @ExamplesSsaAnalyses.gvn_phi_prog = @ExamplesSsaNumbering.gvn_phi_prog.
Proof.
  reflexivity.
Qed.

Example gvn_phi_problem_alias :
  @ExamplesSsaAnalyses.gvn_phi_problem = @ExamplesSsaNumbering.gvn_phi_problem.
Proof.
  reflexivity.
Qed.

Example gvn_phi_left_alias :
  @ExamplesSsaAnalyses.gvn_phi_left = @ExamplesSsaNumbering.gvn_phi_left.
Proof.
  reflexivity.
Qed.

Example gvn_phi_right_alias :
  @ExamplesSsaAnalyses.gvn_phi_right = @ExamplesSsaNumbering.gvn_phi_right.
Proof.
  reflexivity.
Qed.

Example gvn_phi_observation_alias :
  @ExamplesSsaAnalyses.gvn_phi_observation = @ExamplesSsaNumbering.gvn_phi_observation.
Proof.
  reflexivity.
Qed.

Example gvn_phi_observation_laws_alias :
  @ExamplesSsaAnalyses.gvn_phi_observation_laws = @ExamplesSsaNumbering.gvn_phi_observation_laws.
Proof.
  reflexivity.
Qed.

Example gvn_phi_checked_alias :
  @ExamplesSsaAnalyses.gvn_phi_checked = @ExamplesSsaNumbering.gvn_phi_checked.
Proof.
  reflexivity.
Qed.

Example gvn_phi_witness_alias :
  @ExamplesSsaAnalyses.gvn_phi_witness = @ExamplesSsaNumbering.gvn_phi_witness.
Proof.
  reflexivity.
Qed.

Example gvn_phi_equal_alias :
  @ExamplesSsaAnalyses.gvn_phi_equal = @ExamplesSsaNumbering.gvn_phi_equal.
Proof.
  reflexivity.
Qed.

Example gvn_loop_prog_alias :
  @ExamplesSsaAnalyses.gvn_loop_prog = @ExamplesSsaNumbering.gvn_loop_prog.
Proof.
  reflexivity.
Qed.

Example gvn_loop_problem_alias :
  @ExamplesSsaAnalyses.gvn_loop_problem = @ExamplesSsaNumbering.gvn_loop_problem.
Proof.
  reflexivity.
Qed.

Example gvn_loop_info_alias :
  @ExamplesSsaAnalyses.gvn_loop_info = @ExamplesSsaNumbering.gvn_loop_info.
Proof.
  reflexivity.
Qed.

Example gvn_loop_value_alias :
  @ExamplesSsaAnalyses.gvn_loop_value = @ExamplesSsaNumbering.gvn_loop_value.
Proof.
  reflexivity.
Qed.

Example gvn_loop_laws_alias :
  @ExamplesSsaAnalyses.gvn_loop_laws = @ExamplesSsaNumbering.gvn_loop_laws.
Proof.
  reflexivity.
Qed.

Example gvn_loop_wf_alias :
  @ExamplesSsaAnalyses.gvn_loop_wf = @ExamplesSsaNumbering.gvn_loop_wf.
Proof.
  reflexivity.
Qed.

Example gvn_loop_invariant_alias :
  @ExamplesSsaAnalyses.gvn_loop_invariant = @ExamplesSsaNumbering.gvn_loop_invariant.
Proof.
  reflexivity.
Qed.

Example gvn_loop_stability_alias :
  @ExamplesSsaAnalyses.gvn_loop_stability = @ExamplesSsaNumbering.gvn_loop_stability.
Proof.
  reflexivity.
Qed.

Example gvn_loop_run_alias :
  @ExamplesSsaAnalyses.gvn_loop_run = @ExamplesSsaNumbering.gvn_loop_run.
Proof.
  reflexivity.
Qed.

Example gvn_loop_recomputed_alias :
  @ExamplesSsaAnalyses.gvn_loop_recomputed = @ExamplesSsaNumbering.gvn_loop_recomputed.
Proof.
  reflexivity.
Qed.

Example gvn_loop_sound_alias :
  @ExamplesSsaAnalyses.gvn_loop_sound = @ExamplesSsaNumbering.gvn_loop_sound.
Proof.
  reflexivity.
Qed.

Example count_up_alias :
  @ExamplesSsaAnalyses.count_up = @ExamplesSsaScev.count_up.
Proof.
  reflexivity.
Qed.

Example count_up_n_alias :
  @ExamplesSsaAnalyses.count_up_n = @ExamplesSsaScev.count_up_n.
Proof.
  reflexivity.
Qed.

Example count_up_chrec_alias :
  @ExamplesSsaAnalyses.count_up_chrec = @ExamplesSsaScev.count_up_chrec.
Proof.
  reflexivity.
Qed.

Example count_up_inv_alias :
  @ExamplesSsaAnalyses.count_up_inv = @ExamplesSsaScev.count_up_inv.
Proof.
  reflexivity.
Qed.

Example count_up_inventory_alias :
  @ExamplesSsaAnalyses.count_up_inventory = @ExamplesSsaScev.count_up_inventory.
Proof.
  reflexivity.
Qed.

Example count_up_ops_alias :
  @ExamplesSsaAnalyses.count_up_ops = @ExamplesSsaScev.count_up_ops.
Proof.
  reflexivity.
Qed.

Example count_up_loop_alias :
  @ExamplesSsaAnalyses.count_up_loop = @ExamplesSsaScev.count_up_loop.
Proof.
  reflexivity.
Qed.

Example count_up_wf_alias :
  @ExamplesSsaAnalyses.count_up_wf = @ExamplesSsaScev.count_up_wf.
Proof.
  reflexivity.
Qed.

Example count_up_ops_laws_alias :
  @ExamplesSsaAnalyses.count_up_ops_laws = @ExamplesSsaScev.count_up_ops_laws.
Proof.
  reflexivity.
Qed.

Example count_up_ssa_laws_alias :
  @ExamplesSsaAnalyses.count_up_ssa_laws = @ExamplesSsaScev.count_up_ssa_laws.
Proof.
  reflexivity.
Qed.

Example count_up_strict_laws_alias :
  @ExamplesSsaAnalyses.count_up_strict_laws = @ExamplesSsaScev.count_up_strict_laws.
Proof.
  reflexivity.
Qed.

Example count_up_start_alias :
  @ExamplesSsaAnalyses.count_up_start = @ExamplesSsaScev.count_up_start.
Proof.
  reflexivity.
Qed.

Example count_up_header_zero_alias :
  @ExamplesSsaAnalyses.count_up_header_zero = @ExamplesSsaScev.count_up_header_zero.
Proof.
  reflexivity.
Qed.

Example count_up_header_one_alias :
  @ExamplesSsaAnalyses.count_up_header_one = @ExamplesSsaScev.count_up_header_one.
Proof.
  reflexivity.
Qed.

Example count_up_zero_exit_alias :
  @ExamplesSsaAnalyses.count_up_zero_exit = @ExamplesSsaScev.count_up_zero_exit.
Proof.
  reflexivity.
Qed.

Example count_up_start_initial_alias :
  @ExamplesSsaAnalyses.count_up_start_initial = @ExamplesSsaScev.count_up_start_initial.
Proof.
  reflexivity.
Qed.

Example count_up_entry_run_alias :
  @ExamplesSsaAnalyses.count_up_entry_run = @ExamplesSsaScev.count_up_entry_run.
Proof.
  reflexivity.
Qed.

Example count_up_positive_run_alias :
  @ExamplesSsaAnalyses.count_up_positive_run = @ExamplesSsaScev.count_up_positive_run.
Proof.
  reflexivity.
Qed.

Example count_up_zero_run_alias :
  @ExamplesSsaAnalyses.count_up_zero_run = @ExamplesSsaScev.count_up_zero_run.
Proof.
  reflexivity.
Qed.

Example count_up_plan_alias :
  @ExamplesSsaAnalyses.count_up_plan = @ExamplesSsaScev.count_up_plan.
Proof.
  reflexivity.
Qed.

Example count_up_plan_checked_alias :
  @ExamplesSsaAnalyses.count_up_plan_checked = @ExamplesSsaScev.count_up_plan_checked.
Proof.
  reflexivity.
Qed.

Example count_up_plan_compiled_alias :
  @ExamplesSsaAnalyses.count_up_plan_compiled = @ExamplesSsaScev.count_up_plan_compiled.
Proof.
  reflexivity.
Qed.

Example count_up_recognise_alias :
  @ExamplesSsaAnalyses.count_up_recognise = @ExamplesSsaScev.count_up_recognise.
Proof.
  reflexivity.
Qed.

Example count_up_loop_laws_alias :
  @ExamplesSsaAnalyses.count_up_loop_laws = @ExamplesSsaScev.count_up_loop_laws.
Proof.
  reflexivity.
Qed.

Example count_up_recurrence_alias :
  @ExamplesSsaAnalyses.count_up_recurrence = @ExamplesSsaScev.count_up_recurrence.
Proof.
  reflexivity.
Qed.

Example count_up_trip_bound_alias :
  @ExamplesSsaAnalyses.count_up_trip_bound = @ExamplesSsaScev.count_up_trip_bound.
Proof.
  reflexivity.
Qed.

Example calls_ssa_resolver_listed_alias :
  @ExamplesSsaAnalyses.calls_ssa_resolver_listed = @ExamplesSsaCalls.calls_ssa_resolver_listed.
Proof.
  reflexivity.
Qed.

Example calls_ssa_graph_wf_alias :
  @ExamplesSsaAnalyses.calls_ssa_graph_wf = @ExamplesSsaCalls.calls_ssa_graph_wf.
Proof.
  reflexivity.
Qed.

Example ssa_summary_sound_alias :
  @ExamplesSsaAnalyses.ssa_summary_sound = @ExamplesSsaCalls.ssa_summary_sound.
Proof.
  reflexivity.
Qed.

Example ssa_recursion_sound_alias :
  @ExamplesSsaAnalyses.ssa_recursion_sound = @ExamplesSsaCalls.ssa_recursion_sound.
Proof.
  reflexivity.
Qed.

Example ssa_unreachable_sound_alias :
  @ExamplesSsaAnalyses.ssa_unreachable_sound = @ExamplesSsaCalls.ssa_unreachable_sound.
Proof.
  reflexivity.
Qed.

Example ssa_stack_demand_sound_alias :
  @ExamplesSsaAnalyses.ssa_stack_demand_sound = @ExamplesSsaCalls.ssa_stack_demand_sound.
Proof.
  reflexivity.
Qed.

Example ssa_callee_leaf_sound_alias :
  @ExamplesSsaAnalyses.ssa_callee_leaf_sound = @ExamplesSsaCalls.ssa_callee_leaf_sound.
Proof.
  reflexivity.
Qed.

Example ssa_immutable_sound_alias :
  @ExamplesSsaAnalyses.ssa_immutable_sound = @ExamplesSsaMemoryBase.ssa_immutable_sound.
Proof.
  reflexivity.
Qed.

Example chain_graph_alias :
  @ExamplesSsaAnalyses.chain_graph = @ExamplesSsaMemoryLegacy.chain_graph.
Proof.
  reflexivity.
Qed.

Example chain_writes_alias :
  @ExamplesSsaAnalyses.chain_writes = @ExamplesSsaMemoryLegacy.chain_writes.
Proof.
  reflexivity.
Qed.

Example chain_writes_clobber_alias :
  @ExamplesSsaAnalyses.chain_writes_clobber = @ExamplesSsaMemoryLegacy.chain_writes_clobber.
Proof.
  reflexivity.
Qed.

Example chain_reads_alias :
  @ExamplesSsaAnalyses.chain_reads = @ExamplesSsaMemoryLegacy.chain_reads.
Proof.
  reflexivity.
Qed.

Example chain_ssa_alias :
  @ExamplesSsaAnalyses.chain_ssa = @ExamplesSsaMemoryLegacy.chain_ssa.
Proof.
  reflexivity.
Qed.
