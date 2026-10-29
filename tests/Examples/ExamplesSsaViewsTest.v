(** * SSA graph and analysis regression cases

    Computed examples exercise actual total-engine results and typed activation traps.
    For example, the same division point traps for divisor zero and runs for divisor one.
    Builds on: ExamplesSsaAnalyses, ExamplesSsaViews and FixpointTotal. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderBasic OrderPointwise.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointSchedule FixpointIndex
  FixpointWorklist FixpointTotal FixpointCheck.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand AnalysesValues.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaActivation ExamplesSsaBridge
  ExamplesSsaViews ExamplesSsaAnalyses.
Import List.ListNotations.
Local Open Scope nat_scope.

Local Definition ssa_test_needed {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) : finite_map EX (dvars dv) bool :=
  match demand_worklist_run EX dv 256%positive with
  | Some result => lookup unit_encoding (demand_lattice EX bool_demand dv) result tt
  | None => bot (demand_lattice EX bool_demand dv)
  end.

Local Lemma ssa_test_needed_agrees {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :
  demand_worklist_run EX dv 256%positive <> None ->
  needed_values EX dv = ssa_test_needed EX dv.
Proof.
  intro Hfinished; unfold ssa_test_needed.
  destruct (demand_worklist_run EX dv 256%positive) as [result|] eqn:Hrun;
    [eapply needed_values_from_run; exact Hrun|contradiction].
Qed.

Local Definition ssa_test_map {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys) : assignment X A :=
  match run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256 with
  | Some result => result
  | None => Map.empty
  end.

Local Lemma ssa_test_total_agrees {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys)
    (HT : terminates L ss sch Joining) :
  run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256 <> None ->
  proj1_sig (solve_total EX EC L HL sch Joining sys ss HT) =
    lookup EX L (ssa_test_map EX EC L sch sys ss).
Proof.
  intro Hfinished; unfold ssa_test_map.
  destruct (run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 256)
    as [result|] eqn:Hrun; [|contradiction].
  destruct (solve_total_run EX EC L sys sch Joining HL ss HT) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [result' [Hrun' Hagrees]].
  pose proof (total_completed_runs_unique EX EC L sch Joining sys _ fuel 256
    result' result Hrun' Hrun) as Heq.
  rewrite <- Heq; exact Hagrees.
Qed.

(** The actual SSA checker accepts the factorial fixture. *)
Example factorial_wf : wf_check factorial_ssa = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example factorial_counter_instruction :
  uses (ssa_var_view no_ext factorial_ssa 0) (SsaEdge 1 1 2) = [5; 7] /\
  Graph.out (ssa_point_graph factorial_ssa 0) (1, 2) = [SsaEdge 1 1 2].
Proof.
  vm_compute; auto.
Qed.

(** The auxiliary counter is live at the loop's first instruction. *)
Example factorial_z_live :
  fmem var_encoding z_value (liveness_at factorial_ssa loop_header_point) = true.
Proof.
  unfold liveness_at, solve_liveness.
  rewrite ssa_test_total_agrees by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

(** The actual total neededness producer leaves the auxiliary counter undemanded. *)
Example factorial_z_dead :
  dead_value var_encoding (ssa_demand_view no_ext factorial_ssa 0) z_value = true.
Proof.
  unfold dead_value; rewrite ssa_test_needed_agrees by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

(** The factorial accumulator is demanded by the output and return. *)
Example factorial_p_needed :
  dead_value var_encoding (ssa_demand_view no_ext factorial_ssa 0) p_value = false.
Proof.
  unfold dead_value; rewrite ssa_test_needed_agrees by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Definition ssa_division_program : program :=
  Program [(0, FDef 0 [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2))] TyI32)] 0 [].

Definition ssa_division_env (divisor : Z) : vid -> option cval :=
  env_set (env_set (fun _ => None) 0 (VInt W32 1)) 1 (VInt W32 divisor).

Definition ssa_division_start (divisor : Z) : astate :=
  AState 0 0 (ssa_division_env divisor).

Local Lemma ssa_division_initial divisor : (0 <= divisor < 2 ^ 32)%Z ->
  initial (activation no_ext ssa_division_program 0) (ssa_division_start divisor).
Proof.
  intro Hvalid.
  exists (FDef 0 [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2))] TyI32),
    (SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2)),
    [VInt W32 1; VInt W32 divisor], (ssa_division_env divisor).
  repeat split; try reflexivity.
  constructor; [change (0 <= 1 < 4294967296)%Z; lia|].
  constructor; [exact Hvalid|constructor].
Qed.

Example ssa_division_checked : wf_check ssa_division_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ssa_division_reachable_inputs :
  reachable_state (activation no_ext ssa_division_program 0) (ssa_division_start 0) /\
  reachable_state (activation no_ext ssa_division_program 0) (ssa_division_start 1) /\
  point (ssa_point_view no_ext ssa_division_program 0) (ssa_division_start 0) =
    point (ssa_point_view no_ext ssa_division_program 0) (ssa_division_start 1).
Proof.
  split.
  - exists (ssa_division_start 0), []; split; [|constructor].
    apply ssa_division_initial; change (0 <= 0 < 4294967296)%Z; lia.
  - split; [|reflexivity].
    exists (ssa_division_start 1), []; split; [|constructor].
    apply ssa_division_initial; change (0 <= 1 < 4294967296)%Z; lia.
Qed.

Example ssa_division_zero_traps :
  trapped (activation_endings no_ext ssa_division_program 0) (ssa_division_start 0).
Proof.
  exists 2, (OBin W32 BDivU), [0; 1], [VInt W32 1; VInt W32 0].
  split; [|split; reflexivity].
  exists (FDef 0 [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2))] TyI32),
    (SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2)).
  repeat split; reflexivity.
Qed.

Example ssa_division_unit_runs :
  step (activation no_ext ssa_division_program 0) (ssa_division_start 1) []
    (AState 0 1 (env_set (ssa_division_env 1) 2 (VInt W32 1))).
Proof.
  eapply AOp with (o := OBin W32 BDivU) (args := [0; 1])
    (cs := [VInt W32 1; VInt W32 1]); try reflexivity.
  exists (FDef 0 [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2))] TyI32),
    (SBlock [(0, TyI32); (1, TyI32)] [IOp 2 (OBin W32 BDivU) [0; 1]] (TRet 2)).
  repeat split; reflexivity.
Qed.

Example ssa_division_exit_operands :
  dexit (ssa_demand_view no_ext ssa_division_program 0) (0, 0) = [(0, true); (1, true)].
Proof.
  vm_compute; reflexivity.
Qed.

Example ssa_zero_divisor_needed :
  dead_value var_encoding (ssa_demand_view no_ext ssa_division_program 0) 1 = false.
Proof.
  unfold dead_value; rewrite ssa_test_needed_agrees by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Example ssa_factorial_guarded_edge :
  edge_guard (ssa_block_view no_ext factorial_ssa 0) (SsaEdge 1 1 0) =
    [Condition 11 GTrue] /\
  uses (ssa_var_view no_ext factorial_ssa 0) (SsaEdge 1 1 6) = [11; 6; 9; 8].
Proof.
  vm_compute; auto.
Qed.

Definition ssa_parallel_program : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32); (2, TyI32)] []
      (TBr 0 1 [1; 2] 1 [2; 1]));
     (1, SBlock [(3, TyI32); (4, TyI32)] [IOp 5 (OBin W32 BAdd) [3; 4]] (TRet 5));
     (2, SBlock [(6, TyPtr); (7, TyI32)]
       [IStore M4 6 7; IFree 6; ILoad 8 TyI32 M4 6] (TRet 8))] TyI32)] 0 [].

Definition ssa_call_program : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
     (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32);
    (1, FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)] 0 [].

Example ssa_parallel_and_call_checked :
  wf_check ssa_parallel_program = true /\ wf_check ssa_call_program = true.
Proof.
  vm_compute; auto.
Qed.

Example ssa_empty_block_and_parallel_edges :
  Graph.out (ssa_point_graph ssa_parallel_program 0) (0, 0) =
    [SsaEdge 0 1 0; SsaEdge 0 1 1] /\
  edge_args (ssa_block_view no_ext ssa_parallel_program 0) (SsaEdge 0 1 0) = [1; 2] /\
  edge_args (ssa_block_view no_ext ssa_parallel_program 0) (SsaEdge 0 1 1) = [2; 1].
Proof.
  vm_compute; auto.
Qed.

Example ssa_entry_value_defined_before_use :
  point_definition (ssa_refined_points ssa_parallel_program 0) (SsaSourceValue 0) =
    Some (SsaBeforeParams 0) /\
  edge_def (point_model (ssa_refined_points ssa_parallel_program 0)) (SsaBindParams 0) =
    [SsaSourceValue 0; SsaSourceValue 1; SsaSourceValue 2] /\
  edge_use (point_model (ssa_refined_points ssa_parallel_program 0)) (SsaBindParams 0) = [].
Proof.
  vm_compute; auto.
Qed.

Example ssa_pending_and_source_carriers_differ :
  uses (ssa_refined_semantic_var_view no_ext ssa_parallel_program 0) (SsaBindParams 1) =
    [SsaPendingVar 0; SsaPendingVar 1] /\
  defs (ssa_refined_semantic_var_view no_ext ssa_parallel_program 0) (SsaTransfer 0 1 1) =
    [SsaPendingVar 0; SsaPendingVar 1] /\
  edge_def (point_model (ssa_refined_points ssa_parallel_program 0)) (SsaTransfer 0 1 1) = [] /\
  edge_use (point_model (ssa_refined_points ssa_parallel_program 0)) (SsaTransfer 0 1 1) =
    [SsaSourceValue 0; SsaSourceValue 2; SsaSourceValue 1].
Proof.
  vm_compute; auto.
Qed.

Example ssa_call_arguments_are_distinct :
  edge_args (ssa_block_view no_ext ssa_call_program 0) (SsaEdge 0 1 0) = [] /\
  block_edge_args (ssa_refined_points ssa_call_program 0) (SsaEdge 0 1 0) =
    [SsaCallResult 0] /\
  edge_def (point_model (ssa_refined_points ssa_call_program 0)) (SsaMakeCallResult 0) =
    [SsaCallResult 0] /\
  uses (ssa_refined_semantic_var_view no_ext ssa_call_program 0) (SsaTransfer 0 1 0) =
    [SsaCallVar 0].
Proof.
  vm_compute; auto.
Qed.

Example ssa_unreachable_exit_operands_retained :
  dexit (ssa_demand_view no_ext ssa_parallel_program 0) (2, 0) = [(6, true); (7, true)] /\
  dexit (ssa_demand_view no_ext ssa_parallel_program 0) (2, 1) = [(6, true)] /\
  dexit (ssa_demand_view no_ext ssa_parallel_program 0) (2, 2) = [(6, true)].
Proof.
  vm_compute; auto.
Qed.

Example ssa_nonreturn_endpoint_stays_dead :
  ssa_refine_point ssa_parallel_program 0 (0, 1) = SsaDeadPoint 0 /\
  Graph.out (ssa_refined_graph ssa_parallel_program 0) (SsaDeadPoint 0) = [] /\
  exit_use (point_model (ssa_refined_points ssa_parallel_program 0)) (SsaDeadPoint 0) = [].
Proof.
  vm_compute; auto.
Qed.

Example ssa_integer_bridge_boundaries :
  to_word ssa_bridge (VInt W32 (-1)%Z) = None /\
  to_word ssa_bridge (VInt W32 4294967296) = None /\
  op_eval no_ext (OBin W32 BShl) [VInt W32 1; VInt W32 32] = Some (VInt W32 1) /\
  op_eval no_ext (OBin W64 BEq) [VInt W64 7; VInt W64 7] = Some (VInt W32 1).
Proof.
  vm_compute; auto.
Qed.

Example ssa_unit_divisor_does_not_trap :
  ~ trapped (activation_endings no_ext ssa_division_program 0) (ssa_division_start 1).
Proof.
  intros [x [o [args [cs [[fd [b [Hf [Hb Hnth]]]] [Hread Heval]]]]]].
  vm_compute in Hf; injection Hf as <-.
  vm_compute in Hb; injection Hb as <-.
  vm_compute in Hnth; injection Hnth as <- <- <-.
  vm_compute in Hread; injection Hread as <-.
  vm_compute in Heval; discriminate.
Qed.

Example ssa_parallel_reads_precede_parameter_writes :
  let env := ssa_division_env 2 in
  match read_args env [1; 0] with
  | Some cs => match bind_params env [(0, TyI32); (1, TyI32)] cs with
      | Some env' => (env' 0, env' 1)
      | None => (None, None)
      end
  | None => (None, None)
  end = (Some (VInt W32 2), Some (VInt W32 1)).
Proof.
  vm_compute; reflexivity.
Qed.

Example ssa_call_result_crosses_pending_slots :
  let r := SsaRefinedState (SsaCallReady 0) (fun _ => None)
    (fun _ => Some (VInt W32 42)) (fun _ => Some (VInt W32 99)) in
  match ssa_administrative_next ssa_call_program 0 r with
  | Some before => match ssa_administrative_next ssa_call_program 0 before with
      | Some after => (srs_point after, srs_env after 1,
          srs_call_results after 0, srs_pending after 0, srs_pending after 9)
      | None => (SsaDeadPoint 0, None, None, None, None)
      end
  | None => (SsaDeadPoint 0, None, None, None, None)
  end = (SsaExecPoint 1 0, Some (VInt W32 42), Some (VInt W32 42),
    Some (VInt W32 42), Some (VInt W32 99)).
Proof.
  vm_compute; reflexivity.
Qed.

Local Lemma ssa_test_well_formed P :
  ext_sigs P = [] -> wf_check P = true -> wf_program no_ext P.
Proof.
  intros Hextensions Hchecked; apply wf_check_sound;
    [apply ext_respects_nil; exact Hextensions|exact Hchecked].
Qed.

(** The complete block laws instantiate on the checker-accepted looping factorial program. *)
Example ssa_factorial_block_laws :
  ssa_view_laws (activation no_ext factorial_ssa 0) (ssa_block_view no_ext factorial_ssa 0).
Proof.
  apply ssa_block_view_laws.
  - apply ssa_test_well_formed; [reflexivity|exact factorial_wf].
  - cbn; left; reflexivity.
Qed.

(** The stable liveness bridge retains a trap operand in an unreachable source block. *)
Example ssa_unreachable_refined_liveness :
  syntactic_live (var_point_uses (ssa_var_view no_ext ssa_parallel_program 0)) 6 (2, 0) /\
  syntactic_live (point_model (ssa_refined_points ssa_parallel_program 0))
    (SsaSourceValue 6) (SsaExecPoint 2 0).
Proof.
  assert (Hraw : syntactic_live (var_point_uses (ssa_var_view no_ext ssa_parallel_program 0))
    6 (2, 0)).
  { apply live_exit; vm_compute; left; reflexivity. }
  split; [exact Hraw|].
  apply (proj1 (ssa_refined_liveness no_ext ssa_parallel_program 0
    (ssa_test_well_formed ssa_parallel_program eq_refl (proj1 ssa_parallel_and_call_checked))
    (or_introl eq_refl) (2, 0) 6 ltac:(vm_compute; tauto))).
  exact Hraw.
Qed.

Local Lemma ssa_call_source_killed :
  ~ syntactic_live (var_point_uses (ssa_var_view no_ext ssa_call_program 0)) 1 (0, 0).
Proof.
  intro Hlive; inversion Hlive as [n Hexit|n e Hout Huse|n e Hout Hkill Hnext]; subst.
  - vm_compute in Hexit; contradiction.
  - vm_compute in Hout; destruct Hout as [Heq|Hfalse]; [subst e|contradiction].
    vm_compute in Huse; destruct Huse as [Hfalse|Hfalse]; [discriminate|contradiction].
  - vm_compute in Hout; destruct Hout as [Heq|Hfalse]; [subst e|contradiction].
    apply Hkill; vm_compute; left; reflexivity.
Qed.

(** Fresh call temporaries do not bypass the source continuation parameter's kill. *)
Example ssa_call_refined_source_killed :
  ~ syntactic_live (point_model (ssa_refined_points ssa_call_program 0))
    (SsaSourceValue 1) (SsaExecPoint 0 0).
Proof.
  intro Hlive; apply ssa_call_source_killed.
  apply (proj2 (ssa_refined_liveness no_ext ssa_call_program 0
    (ssa_test_well_formed ssa_call_program eq_refl (proj2 ssa_parallel_and_call_checked))
    (or_introl eq_refl) (0, 0) 1 ltac:(vm_compute; tauto))).
  exact Hlive.
Qed.

Definition ssa_duplicate_program : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [IOp 1 (OBin W32 BAdd) [0; 0]] (TJump 1 [1; 1]));
     (1, SBlock [(2, TyI32); (3, TyI32)] [] (TRet 2))] TyI32)] 0 [].

(** The checker accepts repeated operands and repeated incoming values. *)
Example ssa_duplicate_operands_checked : wf_check ssa_duplicate_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Entry binding precedes the first instruction, retaining both copies of its operand. *)
Example ssa_first_instruction_entry_use :
  Graph.entries (ssa_refined_graph ssa_duplicate_program 0) = [SsaBeforeParams 0] /\
  point_definition (ssa_refined_points ssa_duplicate_program 0) (SsaSourceValue 0) =
    Some (SsaBeforeParams 0) /\
  edge_def (point_model (ssa_refined_points ssa_duplicate_program 0)) (SsaBindParams 0) =
    [SsaSourceValue 0] /\
  Graph.target (ssa_refined_graph ssa_duplicate_program 0) (SsaBindParams 0) =
    SsaExecPoint 0 0 /\
  uses (ssa_var_view no_ext ssa_duplicate_program 0) (SsaEdge 0 0 0) = [0; 0] /\
  edge_use (point_model (ssa_refined_points ssa_duplicate_program 0)) (SsaInstruction 0 0) =
    [SsaSourceValue 0; SsaSourceValue 0].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate selected values remain distinct operand occurrences before common binding. *)
Example ssa_duplicate_transfer_operands :
  edge_args (ssa_block_view no_ext ssa_duplicate_program 0) (SsaEdge 0 1 0) = [1; 1] /\
  block_edge_args (ssa_refined_points ssa_duplicate_program 0) (SsaEdge 0 1 0) =
    [SsaSourceValue 1; SsaSourceValue 1] /\
  uses (ssa_refined_semantic_var_view no_ext ssa_duplicate_program 0) (SsaTransfer 0 1 0) =
    [SsaSourceVar 1; SsaSourceVar 1] /\
  defs (ssa_refined_semantic_var_view no_ext ssa_duplicate_program 0) (SsaTransfer 0 1 0) =
    [SsaPendingVar 0; SsaPendingVar 1].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition ssa_switch_program : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32); (1, TyI32); (2, TyI32)]
      [IOp 3 (OConst (VInt W32 7)) []; IOp 4 (OBin W32 BAdd) [3; 3]]
      (TSwitch 0 [(2%Z, 1, [1; 1]); (4294967297%Z, 1, [2; 1]); ((-1)%Z, 1, [1; 2])]
        1 [2; 2]));
     (1, SBlock [(5, TyI32); (6, TyI32)] [] (TRet 5))] TyI32)] 0 [].

(** Multiple case occurrences with wrapped keys and repeated operands pass the source checker. *)
Example ssa_switch_checked : wf_check ssa_switch_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Case guards use their own wrapped keys; the default excludes every key in source order. *)
Example ssa_switch_case_and_default_guards :
  map (edge_guard (ssa_block_view no_ext ssa_switch_program 0))
    [SsaEdge 0 1 0; SsaEdge 0 1 1; SsaEdge 0 1 2; SsaEdge 0 1 3] =
    [[Condition 0 (GConst (VInt W32 2))];
     [Condition 0 (GConst (VInt W32 1))];
     [Condition 0 (GConst (VInt W32 4294967295))];
     [Condition 0 (GNotConst (VInt W32 2)); Condition 0 (GNotConst (VInt W32 1));
      Condition 0 (GNotConst (VInt W32 4294967295))]].
Proof.
  vm_compute; reflexivity.
Qed.

(** Cached body lengths and target metadata preserve raw/refined slots and operand copies. *)
Example ssa_switch_point_rows :
  Graph.out (ssa_point_graph ssa_switch_program 0) (0, 2) =
    [SsaEdge 0 1 2; SsaEdge 0 1 3; SsaEdge 0 1 4; SsaEdge 0 1 5] /\
  uses (ssa_var_view no_ext ssa_switch_program 0) (SsaEdge 0 1 5) = [0; 2; 2] /\
  Graph.source (ssa_refined_graph ssa_switch_program 0) (SsaTransfer 0 1 3) =
    SsaExecPoint 0 2 /\
  edge_use (point_model (ssa_refined_points ssa_switch_program 0)) (SsaTransfer 0 1 3) =
    [SsaSourceValue 0; SsaSourceValue 2; SsaSourceValue 2] /\
  defs (ssa_refined_semantic_var_view no_ext ssa_switch_program 0) (SsaTransfer 0 1 3) =
    [SsaPendingVar 0; SsaPendingVar 1].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
