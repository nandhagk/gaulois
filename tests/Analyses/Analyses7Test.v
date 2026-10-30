(** * Scalar recurrence arithmetic examples

    These examples distinguish exact wrapped trip counts from separate no-wrap evidence.
    For example, the width-two sequence zero, two, zero, two never fails the test below three.
    Builds on: AnalysesScev and BitsWord. *)

From Stdlib Require Import List Bool Arith ZArith NArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsGraph ViewsSsa.
From Gaulois.Analyses Require Import AnalysesScev.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition scev_test_env (_ : nat) : Z := 0%Z.

Definition scev_test_affine (base step : Z) : chrec nat :=
  CRec (CInv (IConst base)) (CInv (IConst step)).

Example scev_constant_value :
  eval_chrec scev_test_env (CInv (IConst 7)) 12 = 7%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_affine_five :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 1) (IConst 5) = Some 5%N /\
  nowrap_check 32%positive Unsigned scev_test_env
    (scev_test_affine 0 1) (IConst 5) 5%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_zero_trip :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 1) (IConst 0) = Some 0%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_constant_word_never_fails :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 0 0) (IConst 5) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_wrapped_cycle_has_no_failure :
  trip_count scev_test_env 2%positive Unsigned CmpLt
    (scev_test_affine 0 2) (IConst 3) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_wrapped_first_failure :
  trip_count scev_test_env 2%positive Unsigned CmpNe
    (scev_test_affine 3 1) (IConst 0) = Some 1%N /\
  nowrap_check 2%positive Unsigned scev_test_env
    (scev_test_affine 3 1) (IConst 0) 1%N = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_unsigned_boundary :
  trip_count scev_test_env 32%positive Unsigned CmpLt
    (scev_test_affine 4294967294 1) (IConst 4294967295) = Some 1%N /\
  nowrap_check 32%positive Unsigned scev_test_env
    (scev_test_affine 4294967294 1) (IConst 4294967295) 1%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_inclusive_first_failure :
  trip_count scev_test_env 8%positive Unsigned CmpLe
    (scev_test_affine 0 1) (IConst 5) = Some 6%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_descending :
  trip_count scev_test_env 8%positive Signed CmpNe
    (scev_test_affine 2 (-1)) (IConst (-3)) = Some 5%N /\
  nowrap_check 8%positive Signed scev_test_env
    (scev_test_affine 2 (-1)) (IConst (-3)) 5%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_minimum_wrap_rejected :
  trip_count scev_test_env 3%positive Signed CmpLt
    (scev_test_affine (-4) (-1)) (IConst (-3)) = Some 1%N /\
  nowrap_check 3%positive Signed scev_test_env
    (scev_test_affine (-4) (-1)) (IConst (-3)) 1%N = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_arbitrary_base_at_zero :
  trip_count scev_test_env 8%positive Unsigned CmpLt
    (CRec (CGeo (CInv (IConst 7)) (CInv (IConst 3))) (CInv (IConst 2)))
    (IConst 11) = Some 2%N /\
  nowrap_check 8%positive Unsigned scev_test_env
    (CRec (CGeo (CInv (IConst 7)) (CInv (IConst 3))) (CInv (IConst 2)))
    (IConst 11) 2%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_word_literal_and_coefficient :
  signed_iexpr 8%positive Signed (IWordConst 255 : iexpr nat) = IConst (-1) /\
  signed_iexpr 1%positive Signed (IConst 2 : iexpr nat) = IConst 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_affine_product_normal_form :
  chrec_mul (scev_test_affine 2 3) (scev_test_affine 5 7) =
    CRec (CInv (IMul (IConst 2) (IConst 5)))
      (CRec (CInv (IAdd (IAdd (IMul (IConst 2) (IConst 7))
          (IMul (IConst 5) (IConst 3))) (IMul (IConst 3) (IConst 7))))
        (CInv (IMul (IConst 2) (IMul (IConst 3) (IConst 7))))).
Proof.
  reflexivity.
Qed.

Example scev_geometric_product :
  eval_chrec scev_test_env
    (chrec_mul (CGeo (CInv (IConst 2)) (CInv (IConst 3)))
      (CGeo (CInv (IConst 5)) (CInv (IConst 2)))) 3 = 2160%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_fallback_nodes :
  let a := CGeo (CInv (IConst 2)) (CInv (IConst 3)) in
  let b := scev_test_affine 1 2 in
  chrec_add a b = CSum a b /\ chrec_mul a b = CProduct a b /\
    eval_chrec scev_test_env (CSum a b) 2 = 23%Z /\
    eval_chrec scev_test_env (CProduct a b) 2 = 90%Z.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_test_nested_plan : scev_plan nat :=
  ScevPlan
    [ScevBinding 0 10 20 SAddUpdate (Some (SOutside 11)) true;
     ScevBinding 1 12 21 SAddUpdate (Some (SPhi 0)) true] 1.

Example scev_compiler_ranked_nested_phi :
  scev_compile_plan nat_encoding scev_test_nested_plan =
    Some (CRec (CInv (IVar 12)) (CRec (CInv (IVar 10)) (CInv (IVar 11)))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_geometric :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SMulUpdate (Some (SOutside 11)) false] 0) =
    Some (CGeo (CInv (IVar 10)) (CInv (IVar 11))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_doubling_coefficient :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SDoubleUpdate None true] 0) =
    Some (CGeo (CInv (IVar 10)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_shared_expression :
  let e := SAdd 30 (SOutside 11) (SOutside 12) in
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 0 10 20 SAddUpdate (Some (SMul 31 e e)) true] 0) =
    Some (CRec (CInv (IVar 10))
      (CInv (IMul (IAdd (IVar 11) (IVar 12)) (IAdd (IVar 11) (IVar 12))))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_missing_prior_phi :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 1 12 21 SAddUpdate (Some (SPhi 0)) true] 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_compiler_missing_other :
  scev_compile_plan nat_encoding
    (ScevPlan [ScevBinding 1 12 21 SAddUpdate None true] 1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_shape_graph : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2] (fun _ => []) (fun _ => 0) (fun _ => 1).

Definition scev_shape_defs (x : nat) : definition nat nat nat :=
  match x with
  | 3 => Param 1 0
  | 6 => Param 1 1
  | 5 => Op 0 [3; 2]
  | 7 => Op 0 [6; 3]
  | 8 => Op 2 []
  | _ => Arbitrary
  end.

Definition scev_shape_loop (defs : nat -> definition nat nat nat)
    (entry_args : list nat) : loop_view unit unit nat nat nat nat Z :=
  LoopView
    (SsaView (GraphView scev_shape_graph (fun _ => 0) (fun _ _ _ _ => False)
      (fun _ _ _ => False)) defs
      (fun x => if Nat.eqb x 3 || Nat.eqb x 6 then 1 else
        if Nat.eqb x 5 || Nat.eqb x 7 || Nat.eqb x 8 then 2 else 0)
      (fun _ => [3; 6]) (fun e => if Nat.eqb e 0 then entry_args else [5; 7])
      (fun _ => []) (fun _ _ => None) (fun _ _ => None) (fun _ => false))
    1 (fun n => Nat.eqb n 1 || Nat.eqb n 2) 0 1 None.

Definition scev_shape_ops : scev_ops nat Z :=
  ScevOps 8%positive (wrap 8%positive) (Nat.eqb 0) (Nat.eqb 1)
    (fun o => if Nat.eqb o 2 then Some 255%Z else None).

Definition scev_shape_inventory := [0; 1; 2; 3; 5; 6; 7; 8].

Definition scev_shape_nested_plan : scev_plan nat :=
  ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true;
    ScevBinding 6 1 7 SAddUpdate (Some (SPhi 3)) true] 6.

Example scev_checker_ranked_nested_phi :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_nested_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_geometric :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 1 [3; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops (ScevPlan [ScevBinding 3 0 5 SMulUpdate (Some (SOutside 2)) true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_direct_self_add :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops (ScevPlan [ScevBinding 3 0 5 SDoubleUpdate None true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_tagged_word_literal :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1])
    scev_shape_ops
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SConst 8 255)) true] 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_nonlinear_direct_feedback_rejected :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else
      if Nat.eqb x 8 then Op 1 [3; 3] else scev_shape_defs x) [0; 1]) scev_shape_ops
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SMul 8 (SPhi 3) (SPhi 3))) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_mutual_feedback_rejected :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 6] else scev_shape_defs x) [0; 1])
    scev_shape_ops
    (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SPhi 6)) true;
      ScevBinding 6 1 7 SAddUpdate (Some (SPhi 3)) true] 6) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_missing_inventory_operand :
  scev_plan_check nat_encoding nat_encoding [0; 1; 3; 5; 6; 7; 8]
    (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops scev_shape_nested_plan = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_missing_phi_argument :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop scev_shape_defs []) scev_shape_ops scev_shape_nested_plan = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_duplicate_phi_rejected :
  let b := ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true in
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops (ScevPlan [b; b] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_malformed_operation_operands :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3] else scev_shape_defs x) [0; 1])
    scev_shape_ops (ScevPlan [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_nested_phis :
  recognise nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops 6 =
    Some (CRec (CInv (IVar 1)) (CRec (CInv (IVar 0)) (CInv (IVar 2)))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_geometric :
  recognise nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 1 [3; 2] else scev_shape_defs x) [0; 1])
    scev_shape_ops 3 = Some (CGeo (CInv (IVar 0)) (CInv (IVar 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_direct_doubling :
  recognise nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 3] else scev_shape_defs x) [0; 1])
    scev_shape_ops 3 = Some (CGeo (CInv (IVar 0)) (CInv (IConst 2))).
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_mutual_feedback_rejected :
  recognise nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 6] else scev_shape_defs x) [0; 1])
    scev_shape_ops 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_nonlinear_self_feedback_rejected :
  recognise nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else
      if Nat.eqb x 8 then Op 1 [3; 3] else scev_shape_defs x) [0; 1]) scev_shape_ops 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_missing_inventory_rejected :
  recognise nat_encoding nat_encoding [0; 1; 3; 5; 6; 7; 8]
    (scev_shape_loop scev_shape_defs [0; 1]) scev_shape_ops 3 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_descending_env (x : nat) : Z :=
  if Nat.eqb x 2 then 255%Z else if Nat.eqb x 0 then 2%Z else 0%Z.

Example scev_recognise_signed_descending_variable :
  let lv := scev_shape_loop scev_shape_defs [0; 1] in
  match recognise nat_encoding nat_encoding scev_shape_inventory lv scev_shape_ops 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_descending_literal :
  let lv := scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1] in
  match recognise nat_encoding nat_encoding scev_shape_inventory lv scev_shape_ops 3 with
  | Some c =>
    c = CRec (CInv (IVar 0)) (CInv (IWordConst 255)) /\
    trip_count (fun y => view_z 8%positive Signed (scev_descending_env y)) 8%positive Signed CmpNe
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253)) =
        Some 5%N
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_signed_descending_variable_nowrap :
  let lv := scev_shape_loop scev_shape_defs [0; 1] in
  match recognise nat_encoding nat_encoding scev_shape_inventory lv scev_shape_ops 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_signed_descending_literal_nowrap :
  let lv := scev_shape_loop
    (fun x => if Nat.eqb x 5 then Op 0 [3; 8] else scev_shape_defs x) [0; 1] in
  match recognise nat_encoding nat_encoding scev_shape_inventory lv scev_shape_ops 3 with
  | Some c => nowrap_check 8%positive Signed
      (fun y => view_z 8%positive Signed (scev_descending_env y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 253))
      5%N = true
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_checker_unrelated_binding_rejected :
  scev_plan_check nat_encoding nat_encoding scev_shape_inventory
    (scev_shape_loop (fun x => if Nat.eqb x 7 then Op 0 [6; 2] else scev_shape_defs x)
      [0; 1]) scev_shape_ops
    (ScevPlan [ScevBinding 6 1 7 SAddUpdate (Some (SOutside 2)) true;
      ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true] 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example scev_recognise_signed_minimum_wrap_rejected :
  let lv := scev_shape_loop scev_shape_defs [0; 1] in
  let inv := fun x => if Nat.eqb x 0 then 128%Z else
    if Nat.eqb x 2 then 255%Z else 0%Z in
  match recognise nat_encoding nat_encoding scev_shape_inventory lv scev_shape_ops 3 with
  | Some c =>
    trip_count (fun y => view_z 8%positive Signed (inv y)) 8%positive Signed CmpLt
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129)) =
        Some 1%N /\
    nowrap_check 8%positive Signed (fun y => view_z 8%positive Signed (inv y))
      (signed_chrec 8%positive Signed c) (signed_iexpr 8%positive Signed (IWordConst 129))
      1%N = false
  | None => False
  end.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example scev_checker_nested_independent_conditions :
  scev_plan_valid scev_shape_inventory (scev_shape_loop scev_shape_defs [0; 1])
    scev_shape_ops scev_shape_nested_plan.
Proof.
  apply scev_plan_check_sound with (EN := nat_encoding) (EV := nat_encoding).
  exact scev_checker_ranked_nested_phi.
Qed.

(** * Integrated dependency sharing and context invalidation *)

Definition scev_shared_defs (x : nat) : definition nat nat nat :=
  match x with
  | 3 => Param 1 0
  | 6 => Param 1 1
  | 13 => Param 1 2
  | 5 => Op 0 [3; 2]
  | 7 => Op 0 [6; 11]
  | 14 => Op 0 [13; 12]
  | 8 => Op 0 [3; 2]
  | 9 => Op 0 [8; 8]
  | 10 => Op 0 [9; 9]
  | 11 => Op 0 [10; 10]
  | 12 => Op 0 [6; 11]
  | _ => Arbitrary
  end.

Definition scev_shared_home (x : nat) : nat :=
  match x with
  | 3 | 6 | 13 => 1
  | 5 | 7 | 8 | 9 | 10 | 11 | 12 | 14 => 2
  | _ => 0
  end.

Definition scev_shared_loop : loop_view unit unit nat nat nat nat Z :=
  LoopView
    (SsaView (GraphView scev_shape_graph (fun _ => 0) (fun _ _ _ _ => False)
      (fun _ _ _ => False)) scev_shared_defs scev_shared_home
      (fun _ => [3; 6; 13]) (fun e => if Nat.eqb e 0 then [0; 1; 0] else [5; 7; 14])
      (fun _ => []) (fun _ _ => None) (fun _ _ => None) (fun _ => false))
    1 (fun n => Nat.eqb n 1 || Nat.eqb n 2) 0 1 None.

Definition scev_shared_inventory := [0; 1; 2; 3; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14].

Definition scev_shared_e8 : scev_expr nat := SAdd 8 (SPhi 3) (SOutside 2).
Definition scev_shared_e9 : scev_expr nat := SAdd 9 scev_shared_e8 scev_shared_e8.
Definition scev_shared_e10 : scev_expr nat := SAdd 10 scev_shared_e9 scev_shared_e9.
Definition scev_shared_e11 : scev_expr nat := SAdd 11 scev_shared_e10 scev_shared_e10.

Definition scev_shared_plan : scev_plan nat :=
  ScevPlan
    [ScevBinding 3 0 5 SAddUpdate (Some (SOutside 2)) true;
     ScevBinding 6 1 7 SAddUpdate (Some scev_shared_e11) true;
     ScevBinding 13 0 14 SAddUpdate (Some (SAdd 12 (SPhi 6) scev_shared_e11)) true] 13.

Definition scev_shared_execution : option (scev_recognition_execution nat_encoding) :=
  recognise_plan_execution nat_encoding nat_encoding scev_shared_inventory
    scev_shared_loop scev_shape_ops 13.

Example scev_integrated_dag_preparation_reuses :
  match scev_shared_execution with
  | Some execution =>
    sre_preparation_nodes execution = [13; 12; 6; 11; 10; 9; 8; 3; 2] /\
    sre_preparation_hits execution = [11; 10; 9; 8; 2] /\
    sre_plan execution = scev_shared_plan
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_integrated_dag_checker_and_compiler_reuse :
  match scev_shared_execution with
  | Some execution =>
    length (scc_hits (sre_checker_cache execution)) = 5 /\
    length (scc_misses (sre_checker_cache execution)) = 8 /\
    length (scc_hits (sre_compiler_cache execution)) = 5 /\
    length (scc_misses (sre_compiler_cache execution)) = 8 /\
    hd 1%positive (scc_hits (sre_checker_cache execution)) =
      scev_expr_code nat_encoding scev_shared_e11 /\
    hd 1%positive (scc_hits (sre_compiler_cache execution)) =
      scev_expr_code nat_encoding scev_shared_e11
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_integrated_shared_plan_checked :
  scev_plan_check nat_encoding nat_encoding scev_shared_inventory scev_shared_loop
    scev_shape_ops scev_shared_plan = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition scev_shared_index :=
  scev_prepare_index nat_encoding scev_shared_inventory scev_shared_loop scev_shared_plan.

Example scev_checker_rank_change_invalidates_then_reuses :
  let e := scev_prepare_expr nat_encoding (SPhi 3) in
  let '(r0, m0) := scev_check_shared_expr nat_encoding (lbody scev_shared_loop)
    scev_shared_index scev_shape_ops 0 e scev_cache_empty in
  let '(r1, m1) := scev_check_shared_expr nat_encoding (lbody scev_shared_loop)
    scev_shared_index scev_shape_ops 1 e m0 in
  let '(r2, m2) := scev_check_shared_expr nat_encoding (lbody scev_shared_loop)
    scev_shared_index scev_shape_ops 2 e m1 in
  fst r0 = false /\ fst r1 = true /\ fst r2 = true /\
    length (scc_misses m2) = 2 /\ length (scc_hits m2) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition scev_shared_lookup (z : Z) (extra : bool) (x : nat) : option (chrec nat) :=
  if Nat.eqb x 3 then Some (CInv (IConst z)) else
    if extra && Nat.eqb x 6 then Some (CInv (IConst 9)) else None.

Example scev_compiler_environment_change_invalidates_then_reuses :
  let e := scev_prepare_expr nat_encoding (SPhi 3) in
  match scev_compile_shared_expr nat_encoding (scev_shared_lookup 0 false) e
    scev_cache_empty with
  | Some (_, m0) =>
    match scev_compile_shared_expr nat_encoding (scev_shared_lookup 1 false) e m0 with
    | Some (_, m1) =>
      match scev_compile_shared_expr nat_encoding (scev_shared_lookup 1 true) e m1 with
      | Some (c, m2) =>
        c = CInv (IConst 1) /\ length (scc_misses m2) = 2 /\ length (scc_hits m2) = 1
      | None => False
      end
    | None => False
    end
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_checker_same_root_malformed_tree_is_distinct :
  let good := scev_prepare_expr nat_encoding scev_shared_e8 in
  let bad := scev_prepare_expr nat_encoding (SAdd 8 (SOutside 2) (SOutside 2)) in
  let '(r0, m0) := scev_check_shared_expr nat_encoding (lbody scev_shared_loop)
    scev_shared_index scev_shape_ops 1 good scev_cache_empty in
  let '(r1, m1) := scev_check_shared_expr nat_encoding (lbody scev_shared_loop)
    scev_shared_index scev_shape_ops 1 bad m0 in
  fst r0 = true /\ fst r1 = false /\ length (scc_misses m1) = 4 /\
    length (scc_hits m1) = 0.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example scev_compiler_same_root_different_tree_is_distinct :
  let first := scev_prepare_expr nat_encoding (SAdd 8 (SOutside 2) (SOutside 2)) in
  let second := scev_prepare_expr nat_encoding (SAdd 8 (SOutside 2) (SConst 9 7)) in
  match scev_compile_shared_expr nat_encoding (fun _ => None) first scev_cache_empty with
  | Some (_, m0) =>
    match scev_compile_shared_expr nat_encoding (fun _ => None) second m0 with
    | Some (c, m1) =>
      c = CInv (IAdd (IVar 2) (IWordConst 7)) /\ length (scc_misses m1) = 4 /\
        length (scc_hits m1) = 2
    | None => False
    end
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
