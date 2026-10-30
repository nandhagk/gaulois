(** * SSA analysis compatibility facade

    This module preserves the qualified paths of the SSA analysis clients.
    For example, factorial and the numbering fixtures remain available through this facade.
    Builds on: ExamplesSsaAnalysisBase and the SSA analysis client modules. *)

From Gaulois.Examples.Ssa Require Export
  ExamplesSsaAnalysisBase ExamplesSsaNumbering ExamplesSsaScev ExamplesSsaCalls
  ExamplesSsaMemoryBase ExamplesSsaMemoryLegacy.

(** Compatibility alias for label_encoding. *)
Definition label_encoding := @ExamplesSsaAnalysisBase.label_encoding.

(** Compatibility alias for ssa_bop_code. *)
Definition ssa_bop_code := @ExamplesSsaAnalysisBase.ssa_bop_code.

(** Compatibility alias for ssa_cval_code. *)
Definition ssa_cval_code := @ExamplesSsaAnalysisBase.ssa_cval_code.

(** Compatibility alias for ssa_cval_encoding. *)
Definition ssa_cval_encoding := @ExamplesSsaAnalysisBase.ssa_cval_encoding.

(** Compatibility alias for ssa_sop_code. *)
Definition ssa_sop_code := @ExamplesSsaAnalysisBase.ssa_sop_code.

(** Compatibility alias for sop_encoding. *)
Definition sop_encoding := @ExamplesSsaAnalysisBase.sop_encoding.

(** Compatibility alias for const_numeric. *)
Definition const_numeric := @ExamplesSsaAnalysisBase.const_numeric.

(** Compatibility alias for const_conc. *)
Definition const_conc := @ExamplesSsaAnalysisBase.const_conc.

(** Compatibility alias for liveness_at. *)
Definition liveness_at := Eval unfold ExamplesSsaAnalysisBase.liveness_at in
  @ExamplesSsaAnalysisBase.liveness_at.

(** Compatibility alias for ssa_dead_value_removable. *)
Definition ssa_dead_value_removable := @ExamplesSsaAnalysisBase.ssa_dead_value_removable.

(** Compatibility alias for factorial_ssa. *)
Definition factorial_ssa := @ExamplesSsaAnalysisBase.factorial_ssa.

(** Compatibility alias for z_value. *)
Definition z_value := @ExamplesSsaAnalysisBase.z_value.

(** Compatibility alias for p_value. *)
Definition p_value := @ExamplesSsaAnalysisBase.p_value.

(** Compatibility alias for loop_header_point. *)
Definition loop_header_point := @ExamplesSsaAnalysisBase.loop_header_point.

(** Compatibility alias for ok_i32. *)
Definition ok_i32 := @ExamplesSsaAnalysisBase.ok_i32.

(** Compatibility alias for mul_one_term. *)
Definition mul_one_term := @ExamplesSsaAnalysisBase.mul_one_term.

(** Compatibility alias for mul_one_rules. *)
Definition mul_one_rules := @ExamplesSsaAnalysisBase.mul_one_rules.

(** Compatibility alias for unit_cost. *)
Definition unit_cost := @ExamplesSsaAnalysisBase.unit_cost.

(** Compatibility alias for mul_one_rules_sound. *)
Definition mul_one_rules_sound := @ExamplesSsaAnalysisBase.mul_one_rules_sound.

(** Compatibility alias for ssa_sccp_sound. *)
Definition ssa_sccp_sound := @ExamplesSsaAnalysisBase.ssa_sccp_sound.

(** Compatibility alias for ssa_guard_chain_sound. *)
Definition ssa_guard_chain_sound := @ExamplesSsaAnalysisBase.ssa_guard_chain_sound.

(** Compatibility alias for ssa_andersen_sound. *)
Definition ssa_andersen_sound := @ExamplesSsaAnalysisBase.ssa_andersen_sound.

(** Compatibility alias for ssa_steensgaard_sound. *)
Definition ssa_steensgaard_sound := @ExamplesSsaAnalysisBase.ssa_steensgaard_sound.

(** Compatibility alias for ssa_escape_sound. *)
Definition ssa_escape_sound := @ExamplesSsaAnalysisBase.ssa_escape_sound.

(** Compatibility alias for gvn_pure. *)
Definition gvn_pure := @ExamplesSsaNumbering.gvn_pure.

(** Compatibility alias for gvn_prog. *)
Definition gvn_prog := @ExamplesSsaNumbering.gvn_prog.

(** Compatibility alias for gvn_first. *)
Definition gvn_first := @ExamplesSsaNumbering.gvn_first.

(** Compatibility alias for gvn_second. *)
Definition gvn_second := @ExamplesSsaNumbering.gvn_second.

(** Compatibility alias for gvn_problem. *)
Definition gvn_problem := @ExamplesSsaNumbering.gvn_problem.

(** Compatibility alias for gvn_binding_state. *)
Definition gvn_binding_state := @ExamplesSsaNumbering.gvn_binding_state.

(** Compatibility alias for gvn_binding_observation. *)
Definition gvn_binding_observation := @ExamplesSsaNumbering.gvn_binding_observation.

(** Compatibility alias for gvn_binding_observation_laws. *)
Definition gvn_binding_observation_laws := @ExamplesSsaNumbering.gvn_binding_observation_laws.

(** Compatibility alias for gvn_binding_witness. *)
Definition gvn_binding_witness := @ExamplesSsaNumbering.gvn_binding_witness.

(** Compatibility alias for gvn_binding_home_dominates. *)
Definition gvn_binding_home_dominates := @ExamplesSsaNumbering.gvn_binding_home_dominates.

(** Compatibility alias for gvn_binding_equal. *)
Definition gvn_binding_equal := @ExamplesSsaNumbering.gvn_binding_equal.

(** Compatibility alias for gvn_use_prog. *)
Definition gvn_use_prog := @ExamplesSsaNumbering.gvn_use_prog.

(** Compatibility alias for gvn_use_problem. *)
Definition gvn_use_problem := @ExamplesSsaNumbering.gvn_use_problem.

(** Compatibility alias for gvn_use_state. *)
Definition gvn_use_state := @ExamplesSsaNumbering.gvn_use_state.

(** Compatibility alias for gvn_use_observation. *)
Definition gvn_use_observation := @ExamplesSsaNumbering.gvn_use_observation.

(** Compatibility alias for gvn_use_observation_laws. *)
Definition gvn_use_observation_laws := @ExamplesSsaNumbering.gvn_use_observation_laws.

(** Compatibility alias for gvn_use_witness. *)
Definition gvn_use_witness := @ExamplesSsaNumbering.gvn_use_witness.

(** Compatibility alias for gvn_use_equal. *)
Definition gvn_use_equal := @ExamplesSsaNumbering.gvn_use_equal.

(** Compatibility alias for gvn_phi_prog. *)
Definition gvn_phi_prog := @ExamplesSsaNumbering.gvn_phi_prog.

(** Compatibility alias for gvn_phi_problem. *)
Definition gvn_phi_problem := @ExamplesSsaNumbering.gvn_phi_problem.

(** Compatibility alias for gvn_phi_left. *)
Definition gvn_phi_left := @ExamplesSsaNumbering.gvn_phi_left.

(** Compatibility alias for gvn_phi_right. *)
Definition gvn_phi_right := @ExamplesSsaNumbering.gvn_phi_right.

(** Compatibility alias for gvn_phi_observation. *)
Definition gvn_phi_observation := @ExamplesSsaNumbering.gvn_phi_observation.

(** Compatibility alias for gvn_phi_observation_laws. *)
Definition gvn_phi_observation_laws := @ExamplesSsaNumbering.gvn_phi_observation_laws.

(** Compatibility alias for gvn_phi_checked. *)
Definition gvn_phi_checked := @ExamplesSsaNumbering.gvn_phi_checked.

(** Compatibility alias for gvn_phi_witness. *)
Definition gvn_phi_witness := @ExamplesSsaNumbering.gvn_phi_witness.

(** Compatibility alias for gvn_phi_equal. *)
Definition gvn_phi_equal := @ExamplesSsaNumbering.gvn_phi_equal.

(** Compatibility alias for gvn_loop_prog. *)
Definition gvn_loop_prog := @ExamplesSsaNumbering.gvn_loop_prog.

(** Compatibility alias for gvn_loop_problem. *)
Definition gvn_loop_problem := @ExamplesSsaNumbering.gvn_loop_problem.

(** Compatibility alias for gvn_loop_info. *)
Definition gvn_loop_info := @ExamplesSsaNumbering.gvn_loop_info.

(** Compatibility alias for gvn_loop_value. *)
Definition gvn_loop_value := @ExamplesSsaNumbering.gvn_loop_value.

(** Compatibility alias for gvn_loop_laws. *)
Definition gvn_loop_laws := @ExamplesSsaNumbering.gvn_loop_laws.

(** Compatibility alias for gvn_loop_wf. *)
Definition gvn_loop_wf := @ExamplesSsaNumbering.gvn_loop_wf.

(** Compatibility alias for gvn_loop_invariant. *)
Definition gvn_loop_invariant := @ExamplesSsaNumbering.gvn_loop_invariant.

(** Compatibility alias for gvn_loop_stability. *)
Definition gvn_loop_stability := @ExamplesSsaNumbering.gvn_loop_stability.

(** Compatibility alias for gvn_loop_run. *)
Definition gvn_loop_run := @ExamplesSsaNumbering.gvn_loop_run.

(** Compatibility alias for gvn_loop_recomputed. *)
Definition gvn_loop_recomputed := @ExamplesSsaNumbering.gvn_loop_recomputed.

(** Compatibility alias for gvn_loop_sound. *)
Definition gvn_loop_sound := @ExamplesSsaNumbering.gvn_loop_sound.

(** Compatibility alias for count_up. *)
Definition count_up := @ExamplesSsaScev.count_up.

(** Compatibility alias for count_up_n. *)
Definition count_up_n := @ExamplesSsaScev.count_up_n.

(** Compatibility alias for count_up_chrec. *)
Definition count_up_chrec := @ExamplesSsaScev.count_up_chrec.

(** Compatibility alias for count_up_inv. *)
Definition count_up_inv := @ExamplesSsaScev.count_up_inv.

(** Compatibility alias for count_up_inventory. *)
Definition count_up_inventory := @ExamplesSsaScev.count_up_inventory.

(** Compatibility alias for count_up_ops. *)
Definition count_up_ops := @ExamplesSsaScev.count_up_ops.

(** Compatibility alias for count_up_loop. *)
Definition count_up_loop := @ExamplesSsaScev.count_up_loop.

(** Compatibility alias for count_up_wf. *)
Definition count_up_wf := @ExamplesSsaScev.count_up_wf.

(** Compatibility alias for count_up_ops_laws. *)
Definition count_up_ops_laws := @ExamplesSsaScev.count_up_ops_laws.

(** Compatibility alias for count_up_ssa_laws. *)
Definition count_up_ssa_laws := @ExamplesSsaScev.count_up_ssa_laws.

(** Compatibility alias for count_up_strict_laws. *)
Definition count_up_strict_laws := @ExamplesSsaScev.count_up_strict_laws.

(** Compatibility alias for count_up_start. *)
Definition count_up_start := @ExamplesSsaScev.count_up_start.
Arguments count_up_start n%_Z_scope.

(** Compatibility alias for count_up_header_zero. *)
Definition count_up_header_zero := @ExamplesSsaScev.count_up_header_zero.
Arguments count_up_header_zero n%_Z_scope.

(** Compatibility alias for count_up_header_one. *)
Definition count_up_header_one := @ExamplesSsaScev.count_up_header_one.
Arguments count_up_header_one n%_Z_scope.

(** Compatibility alias for count_up_zero_exit. *)
Definition count_up_zero_exit := @ExamplesSsaScev.count_up_zero_exit.

(** Compatibility alias for count_up_start_initial. *)
Definition count_up_start_initial := @ExamplesSsaScev.count_up_start_initial.
Arguments count_up_start_initial n%_Z_scope _.

(** Compatibility alias for count_up_entry_run. *)
Definition count_up_entry_run := @ExamplesSsaScev.count_up_entry_run.
Arguments count_up_entry_run n%_Z_scope.

(** Compatibility alias for count_up_positive_run. *)
Definition count_up_positive_run := @ExamplesSsaScev.count_up_positive_run.
Arguments count_up_positive_run n%_Z_scope _.

(** Compatibility alias for count_up_zero_run. *)
Definition count_up_zero_run := @ExamplesSsaScev.count_up_zero_run.

(** Compatibility alias for count_up_plan. *)
Definition count_up_plan := @ExamplesSsaScev.count_up_plan.

(** Compatibility alias for count_up_plan_checked. *)
Definition count_up_plan_checked := @ExamplesSsaScev.count_up_plan_checked.

(** Compatibility alias for count_up_plan_compiled. *)
Definition count_up_plan_compiled := @ExamplesSsaScev.count_up_plan_compiled.

(** Compatibility alias for count_up_recognise. *)
Definition count_up_recognise := @ExamplesSsaScev.count_up_recognise.

(** Compatibility alias for count_up_loop_laws. *)
Definition count_up_loop_laws := @ExamplesSsaScev.count_up_loop_laws.

(** Compatibility alias for count_up_recurrence. *)
Definition count_up_recurrence := @ExamplesSsaScev.count_up_recurrence.

(** Compatibility alias for count_up_trip_bound. *)
Definition count_up_trip_bound := @ExamplesSsaScev.count_up_trip_bound.
Arguments count_up_trip_bound s0 es%_list_scope s t%_N_scope _ _ _ _ _ _.

(** Compatibility alias for calls_ssa_resolver_listed. *)
Definition calls_ssa_resolver_listed := @ExamplesSsaCalls.calls_ssa_resolver_listed.

(** Compatibility alias for calls_ssa_graph_wf. *)
Definition calls_ssa_graph_wf := @ExamplesSsaCalls.calls_ssa_graph_wf.

(** Compatibility alias for ssa_summary_sound. *)
Definition ssa_summary_sound := @ExamplesSsaCalls.ssa_summary_sound.

(** Compatibility alias for ssa_recursion_sound. *)
Definition ssa_recursion_sound := @ExamplesSsaCalls.ssa_recursion_sound.

(** Compatibility alias for ssa_unreachable_sound. *)
Definition ssa_unreachable_sound := @ExamplesSsaCalls.ssa_unreachable_sound.

(** Compatibility alias for ssa_stack_demand_sound. *)
Definition ssa_stack_demand_sound := @ExamplesSsaCalls.ssa_stack_demand_sound.

(** Compatibility alias for ssa_callee_leaf_sound. *)
Definition ssa_callee_leaf_sound := @ExamplesSsaCalls.ssa_callee_leaf_sound.

(** Compatibility alias for ssa_immutable_sound. *)
Definition ssa_immutable_sound := @ExamplesSsaMemoryBase.ssa_immutable_sound.
Arguments ssa_immutable_sound ext%_function_scope P lim ty o%_Z_scope _ _%_function_scope
  s tr%_list_scope t l%_nat_scope _ _ _.

(** Compatibility alias for chain_graph. *)
Definition chain_graph := @ExamplesSsaMemoryLegacy.chain_graph.

(** Compatibility alias for chain_writes. *)
Definition chain_writes := @ExamplesSsaMemoryLegacy.chain_writes.

(** Compatibility alias for chain_writes_clobber. *)
Definition chain_writes_clobber := @ExamplesSsaMemoryLegacy.chain_writes_clobber.

(** Compatibility alias for chain_reads. *)
Definition chain_reads := @ExamplesSsaMemoryLegacy.chain_reads.

(** Compatibility alias for chain_ssa. *)
Definition chain_ssa := @ExamplesSsaMemoryLegacy.chain_ssa.
