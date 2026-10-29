(** * Sparse numeric and path regressions

    The examples exercise numeric truth at different widths and actual sparse propagation.
    For example, the true branch of 32-bit one plus one preserves both concrete operands.
    Builds on: AnalysesValues, AnalysesPaths and the SSA constant-domain client. *)

From Stdlib Require Import List ZArith Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderFlat OrderLift OrderDisjunction.
From Gaulois.Bits Require Import BitsWord BitsOp BitsExpr.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointCheck FixpointWorklist.
From Gaulois.Views Require Import ViewsGraph ViewsSsa ViewsDominated.
From Gaulois.Analyses Require Import AnalysesValues AnalysesPaths.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaSemantics ExamplesSsaBridge
  ExamplesSsaAnalyses.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition numeric_test_domain := sparse_of_numeric const_numeric const_conc ssa_bridge TAny.

Definition numeric_test_const (z : Z) : tagged (flat Z) := TVal 32%positive (FVal z).

Example constant_arithmetic :
  op_abs numeric_test_domain (OBin W32 BAdd) [numeric_test_const 1; numeric_test_const 1] =
    numeric_test_const 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example true_32_bit_one_plus_one_keeps_arguments :
  assume_args numeric_test_domain (OBin W32 BAdd) true
    [numeric_test_const 1; numeric_test_const 1] = [numeric_test_const 1; numeric_test_const 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example true_32_bit_one_plus_one_contains_concrete_arguments :
  Forall2 (gamma (fact_conc numeric_test_domain))
    (assume_args numeric_test_domain (OBin W32 BAdd) true
      [numeric_test_const 1; numeric_test_const 1]) [VInt W32 1; VInt W32 1].
Proof.
  vm_compute. repeat constructor; discriminate.
Qed.

Definition expression_test_bridge : op_bridge Bits.expr cval :=
  OpBridge (fun e => Some e) (to_word ssa_bridge).

Definition expression_test_domain :=
  sparse_of_numeric const_numeric const_conc expression_test_bridge TAny.

Example false_zero_keeps_argument :
  assume_args expression_test_domain (Bits.Var 0) false [numeric_test_const 0] =
    [numeric_test_const 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example true_nonzero_keeps_argument :
  assume_args expression_test_domain (Bits.Var 0) true [numeric_test_const 7] =
    [numeric_test_const 7].
Proof.
  vm_compute; reflexivity.
Qed.

Example false_zero_contains_concrete_argument :
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.Var 0) false [numeric_test_const 0]) [VInt W32 0].
Proof.
  vm_compute. repeat constructor; discriminate.
Qed.

Example true_nonzero_contains_concrete_argument :
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.Var 0) true [numeric_test_const 7]) [VInt W32 7].
Proof.
  vm_compute. repeat constructor; discriminate.
Qed.

Example unknown_width_variable_true :
  assume_args expression_test_domain (Bits.Var 0) true [TAny] = [TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_width_variable_false :
  assume_args expression_test_domain (Bits.Var 0) false [TAny] = [TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_width_both_branches_contain_valid_arguments :
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.Var 0) true [TAny]) [VInt W64 19] /\
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.Var 0) false [TAny]) [VInt W32 0].
Proof.
  vm_compute. split; constructor; [exact I|constructor|exact I|constructor].
Qed.

Example root_comparison_preserves_inputs :
  assume_args expression_test_domain (Bits.App bvult [Bits.Var 0; Bits.Var 1]) true
    [numeric_test_const 1; numeric_test_const 2] = [numeric_test_const 1; numeric_test_const 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example root_comparison_contains_concrete_arguments :
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.App bvult [Bits.Var 0; Bits.Var 1]) true
      [numeric_test_const 1; numeric_test_const 2]) [VInt W32 1; VInt W32 2].
Proof.
  vm_compute. repeat constructor; discriminate.
Qed.

Example root_truncation_tests_result_truth :
  assume_args expression_test_domain (Bits.App (bvtrunc 1%positive) [Bits.Var 0]) false
    [numeric_test_const 2] = [numeric_test_const 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example root_truncation_contains_concrete_argument :
  Forall2 (gamma (fact_conc expression_test_domain))
    (assume_args expression_test_domain (Bits.App (bvtrunc 1%positive) [Bits.Var 0]) false
      [numeric_test_const 2]) [VInt W32 2].
Proof.
  vm_compute. repeat constructor; discriminate.
Qed.

Example malformed_expression_has_bottom_forward_result :
  op_abs expression_test_domain (Bits.App bvadd [Bits.Var 0]) [numeric_test_const 1] = TBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_expression_refinement_preserves_input_arity :
  length (assume_args expression_test_domain (Bits.App bvadd [Bits.Var 0]) true
    [numeric_test_const 1; numeric_test_const 2]) = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_expression_refines_only_its_present_operand :
  assume_args expression_test_domain (Bits.App bvadd [Bits.Var 0]) true
    [numeric_test_const 1; numeric_test_const 2] = [TBot; numeric_test_const 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example unmapped_expression_retains_facts_in_order :
  assume_args numeric_test_domain (OConst (VInt W32 19)) true
    [numeric_test_const 7; TAny; numeric_test_const 0] =
    [numeric_test_const 7; TAny; numeric_test_const 0].
Proof.
  vm_compute; reflexivity.
Qed.

Definition numeric_test_graph : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2]
    (fun n => match n with 0 => [0; 1] | 1 => [2] | _ => [] end)
    (fun e => match e with 2 => 1 | _ => 0 end)
    (fun e => match e with 0 => 1 | _ => 2 end).

Definition numeric_test_view : ssa_view nat unit nat nat nat sop cval :=
  {| base := GraphView numeric_test_graph (fun n => n)
       (fun _ _ _ _ => False) (fun _ _ _ => False);
     def x := match x with 0 => Param 0 0 | 1 => Op (OBin W32 BAdd) [0; 0] | _ => Arbitrary end;
     home := fun _ => 0;
     params n := match n with 0 => [0] | _ => [] end;
     edge_args := fun _ => [];
     edge_guard e := match e with
       | 0 => [Condition 1 (GConst (VInt W32 2))]
       | 1 => [Condition 1 (GConst (VInt W32 0))]
       | _ => []
       end;
     val := fun _ _ => None;
     ViewsSsa.op_eval := op_eval (fun _ _ => None);
     truth := ssa_truth |}.

Definition numeric_test_problem := numeric_problem const_numeric const_conc ssa_bridge TAny
  numeric_test_view [0; 1] (fun _ => numeric_test_const 1).

Definition numeric_test_lattice := lift_bot_lattice (fact_lat numeric_test_domain).

Definition numeric_test_scheduler : scheduler (sparse_unknown nat nat nat) :=
  Scheduler (fun _ => 1%positive) (fun _ => false).

Definition numeric_test_run :=
  run_worklist (sparse_unknown_encoding nat_encoding nat_encoding nat_encoding)
    (sparse_constraint_encoding nat_encoding nat_encoding nat_encoding) numeric_test_lattice
    numeric_test_scheduler Joining (sparse_system nat_encoding nat_encoding numeric_test_problem)
    (Declared (sparse_static nat_encoding nat_encoding numeric_test_problem)
      (index_system (sparse_unknown_encoding nat_encoding nat_encoding nat_encoding)
        (sparse_system nat_encoding nat_encoding numeric_test_problem)
        (sparse_static nat_encoding nat_encoding numeric_test_problem))) 256%positive.

Definition numeric_test_solution :=
  lookup (sparse_unknown_encoding nat_encoding nat_encoding nat_encoding) numeric_test_lattice
    (match numeric_test_run with Some m => m | None => Map.empty end).

Example sparse_numeric_run_finishes :
  match numeric_test_run with Some _ => true | None => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_checker_accepts :
  check_post numeric_test_lattice (sparse_system nat_encoding nat_encoding numeric_test_problem)
    numeric_test_solution = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_constant_propagation :
  numeric_test_solution (UVal 1) = Some (numeric_test_const 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_infeasible_edge : numeric_test_solution (UEdge 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example sparse_numeric_feasible_edge : numeric_test_solution (UEdge 0) = Some TAny.
Proof.
  vm_compute; reflexivity.
Qed.

Example bounded_path_merge :
  join (fact_lat (path_domain 1 numeric_test_domain))
    [numeric_test_const 1] [numeric_test_const 2] = [TVal 32%positive FTop].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_arithmetic_preserves_alternatives :
  op_abs (path_domain 2 numeric_test_domain) (OBin W32 BAdd)
    [[numeric_test_const 1; numeric_test_const 2]; [numeric_test_const 1]] =
    [numeric_test_const 2; numeric_test_const 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_guard_filters_every_alternative :
  assume_value (path_domain 2 numeric_test_domain) (GConst (VInt W32 2))
    [numeric_test_const 1; numeric_test_const 2] = [TBot; numeric_test_const 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example path_backward_refines_joined_arguments :
  assume_args (path_domain 2 expression_test_domain) (Bits.Var 0) false
    [[numeric_test_const 7]] = [[TBot]].
Proof.
  vm_compute; reflexivity.
Qed.

Example dominated_guard_chain :
  guard_chain numeric_test_view nat_encoding 1 = [Condition 1 (GConst (VInt W32 2))].
Proof.
  vm_compute; reflexivity.
Qed.

Example dominated_guard_refines_the_use :
  refined_fact nat_encoding (make_dom_context nat_encoding numeric_test_graph)
    numeric_test_problem (fun _ => Some TAny) 1 1 = Some (numeric_test_const 2).
Proof.
  vm_compute; reflexivity.
Qed.
