(** * Floating-point boundaries and demanded parameters

    Computed examples distinguish float patterns and the demanded-parameter transfer.
    For example, a full demand on a target parameter must reach its source jump argument.
    Builds on: FloatSsa, Flocq Bits and the SSA checker. *)

From Stdlib Require Import Bool List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderPointwise.
From Gaulois.Views Require Import ViewsSemantics ViewsSsa.
From Gaulois.Analyses Require Import AnalysesDemand.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaTypingProofs ExamplesSsaSemantics ExamplesSsaActivation ExamplesSsaViews.
From Gaulois.Float Require Import FloatInterval FloatOps FloatNan FloatSsa.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition test_nan32 : @nan_model 24 128 := @default_nan_model 24 128 ltac:(lia).
Definition test_nan64 : @nan_model 53 1024 := @default_nan_model 53 1024 ltac:(lia).
Local Abbreviation test_float_ext := (float_ext test_nan32 test_nan64).

(* Evaluate observations during elaboration so the test claims themselves contain only concrete
   SSA data. Imported Flocq proof fields are not assumptions of the finite observed results. *)
Definition observed_signed_zeros32 : list (option cval) := Eval vm_compute in
  [test_float_ext 6 [VF32 1065353216; VF32 0];
   test_float_ext 6 [VF32 1065353216; VF32 2147483648];
   test_float_ext 8 [VF32 0; VF32 2147483648]].

Example float_signed_zeros32 : observed_signed_zeros32 =
  [Some (VF32 2139095040); Some (VF32 4286578688); Some (VInt W32 0)].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition observed_smallest_patterns : list (option cval) := Eval vm_compute in
  [test_float_ext 0 [VF32 1; VF32 0]; test_float_ext 1 [VF64 1; VF64 0];
   test_float_ext 8 [VF32 0; VF32 1]; test_float_ext 9 [VF64 0; VF64 1]].

Example float_smallest_patterns : observed_smallest_patterns =
  [Some (VF32 1); Some (VF64 1); Some (VInt W32 1); Some (VInt W32 1)].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition observed_invalid_divisions : list (option cval) := Eval vm_compute in
  [test_float_ext 6 [VF32 2139095040; VF32 2139095040];
   test_float_ext 7 [VF64 0; VF64 0]].

Example float_invalid_divisions : observed_invalid_divisions =
  [Some (VF32 2143289344); Some (VF64 9221120237041090560)].
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition observed_extension_shapes : list (option cval) := Eval vm_compute in
  [test_float_ext 0 [VF32 0; VF32 0]; test_float_ext 1 [VF64 0; VF64 0];
   test_float_ext 0 [VF64 0; VF64 0]; test_float_ext 0 [VF32 (-1); VF32 0];
   test_float_ext 1 [VF64 (2 ^ 64); VF64 0]; test_float_ext 10 [VF32 0; VF32 0]].

Example float_extension_shapes : observed_extension_shapes =
  [Some (VF32 0); Some (VF64 0); None; None; None; None].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example float_tag_roundtrips :
  float_ext_decode (float_ext_tag F32 (FArith FDiv)) = Some (F32, FArith FDiv) /\
  float_ext_decode (float_ext_tag F64 FLt) = Some (F64, FLt).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example float_backward_demands :
  nan_back (FArith FAdd) NotDemanded = (NotDemanded, NotDemanded) /\
  nan_back (FArith FMul) (Demanded false true) = (Demanded true true, Demanded true true) /\
  nan_back FLt (Demanded true true) = (Demanded false false, Demanded false false).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition parameter_entry : ssa_block := SBlock [(0, TyF32)] [] (TJump 1 [0]).
Definition parameter_target : ssa_block := SBlock [(1, TyF32)] [] (TRet 1).
Definition parameter_function : fdef :=
  FDef 0 [(0, parameter_entry); (1, parameter_target)] TyF32.
Definition parameter_program : program := Program [(0, parameter_function)] 0 float_ext_sigs.
Definition parameter_edge : ssa_edge := SsaEdge 0 1 0.

Example float_parameter_checked : wf_check parameter_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_parameter_backward : list (vid * nan_demand) * list (vid * nan_demand) :=
  Eval vm_compute in
  (dback (ssa_nan_demand_view test_float_ext parameter_program 0) parameter_edge 1
    (Demanded false true),
   dback (ssa_nan_demand_view test_float_ext parameter_program 0) parameter_edge 1 NotDemanded).

Example float_parameter_backward :
  observed_parameter_backward = ([(0, Demanded false true)], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example float_forward_pair_occurrences :
  nan_forward_pairs (Demanded true false) [(3, true); (1, false); (3, true)] =
    [(3, Demanded true false); (1, Demanded true false); (3, Demanded true false)].
Proof.
  vm_compute; reflexivity.
Qed.

Definition parameter_universe : list vid := Eval vm_compute in
  dvars (ssa_nan_demand_view test_float_ext parameter_program 0).

Definition parameter_demand : finite_map nat_encoding parameter_universe nan_demand.
Proof.
  refine (exist _ (Map.set nat_encoding 1 (Demanded false false) Map.empty) _).
  split; [apply Map.wf_set, Map.wf_empty|].
  intros x Hpresent; destruct (Nat.eq_dec x 1) as [->|Hdifferent].
  - vm_compute; auto.
  - rewrite Map.get_set_other, Map.get_empty in Hpresent by exact Hdifferent; contradiction.
Defined.

Definition parameter_start (bits : Z) : astate :=
  AState 0 0 (env_set (fun _ => None) 0 (VF32 bits)).

Definition parameter_finish (bits : Z) : astate :=
  activation_enter 1 (env_set (aenv (parameter_start bits)) 1 (VF32 bits)).

Example float_parameter_initial (bits : Z) :
  initial (activation (fun _ _ => None) parameter_program 0) (parameter_start bits).
Proof.
  exists parameter_function, parameter_entry, [VF32 bits], (aenv (parameter_start bits)).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [constructor; constructor|].
  split; reflexivity.
Qed.

Example float_parameter_step (bits : Z) :
  step (activation (fun _ _ => None) parameter_program 0)
    (parameter_start bits) [] (parameter_finish bits).
Proof.
  eapply AJump with (args := [0]) (cs := [VF32 bits]).
  - exists parameter_function, parameter_entry; vm_compute; repeat split; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
Qed.

Definition observed_parameter_demands : list nan_demand := Eval vm_compute in
  map (fun x => dget nat_encoding nan_lattice
    (demand_transfer nat_encoding nan_domain_ssa
      (ssa_nan_demand_view test_float_ext parameter_program 0) parameter_edge parameter_demand) x)
    [0; 1; 2].

Example float_parameter_input_demand :
  observed_parameter_demands = [Demanded false false; NotDemanded; NotDemanded].
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_optional_nan_agreement : Prop := Eval vm_compute in
  nan_option_agree NotDemanded None (Some (VF32 (-1))) /\
  ~ nan_option_agree (Demanded false false) None (Some (VF32 0)) /\
  nan_option_agree (Demanded false false) (Some (VF32 2143289345))
    (Some (VF32 2143289346)) /\
  ~ nan_option_agree (Demanded false true) (Some (VF32 2143289345))
    (Some (VF32 2143289346)) /\
  nan_option_agree (Demanded true true) (Some (VF32 (2 ^ 32))) (Some (VF32 (2 ^ 32))) /\
  ~ nan_option_agree (Demanded true true) (Some (VF32 (2 ^ 32)))
    (Some (VF32 (2 ^ 32 + 1))) /\
  nan_option_agree (Demanded false false) (aenv (parameter_finish 2143289345) 1)
    (aenv (parameter_finish 2143289346) 1).

Example float_optional_nan_agreement : observed_optional_nan_agreement.
Proof.
  vm_compute; intuition congruence.
Qed.

Definition unreachable_operation : ssa_block :=
  SBlock [(2, TyF32); (3, TyF32)] [IOp 4 (OExt 0) [3; 3]] (TRet 4).

Definition unreachable_arbitrary : ssa_block :=
  SBlock [(5, TyI64); (6, TyPtr); (9, TyF32)]
    [IAlloc 7 5; ILoad 8 TyI32 M4 6] (TRet 9).

Definition unreachable_function : fdef := FDef 0
  [(0, parameter_entry); (1, parameter_target); (2, unreachable_operation);
   (3, unreachable_arbitrary)] TyF32.

Definition unreachable_program : program :=
  Program [(0, unreachable_function)] 0 float_ext_sigs.

Example float_unreachable_program_checked : wf_check unreachable_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_unreachable_operation :
    list (vid * nan_demand) * list (vid * nan_demand) * list (vid * nan_demand) :=
  Eval vm_compute in
  (dnec (ssa_nan_demand_view test_float_ext unreachable_program 0) (SsaEdge 2 2 0),
   dback (ssa_nan_demand_view test_float_ext unreachable_program 0) (SsaEdge 2 2 0) 4
     (Demanded false false),
   dexit (ssa_nan_demand_view test_float_ext unreachable_program 0) (2, 0)).

Example float_unreachable_ordered_duplicate_demands : observed_unreachable_operation =
  ([(3, Demanded true true); (3, Demanded true true);
    (3, Demanded false false); (3, Demanded false false)],
   [(3, Demanded false false); (3, Demanded false false)],
   [(3, Demanded true true); (3, Demanded true true)]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_unreachable_coverage : bool := Eval vm_compute in
  forallb (fun x => existsb (Nat.eqb x)
    (dvars (ssa_nan_demand_view test_float_ext unreachable_program 0))) (seq 0 10).

Example float_all_raw_variables_covered : observed_unreachable_coverage = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_arbitrary_backward : list (vid * nan_demand) * list (vid * nan_demand) :=
  Eval vm_compute in
  (dback (ssa_nan_demand_view test_float_ext unreachable_program 0) (SsaEdge 3 3 0) 7
     (Demanded true true),
   dback (ssa_nan_demand_view test_float_ext unreachable_program 0) (SsaEdge 3 3 1) 8
     (Demanded false true)).

Example float_arbitrary_backward : observed_arbitrary_backward = ([], []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Constructor fixtures keep the test roots independent of the decoder's inherited axioms. *)
Definition bound32 (negative : bool) (mantissa : positive) (exponent : Z)
    (Hbounded : SpecFloat.bounded 24 128 mantissa exponent = true) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_finite 24 128 negative mantissa exponent Hbounded) eq_refl.

Definition bound64 (negative : bool) (mantissa : positive) (exponent : Z)
    (Hbounded : SpecFloat.bounded 53 1024 mantissa exponent = true) : @fl_nn 53 1024 :=
  exist _ (@Binary.B754_finite 53 1024 negative mantissa exponent Hbounded) eq_refl.

Definition zero32 (negative : bool) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_zero 24 128 negative) eq_refl.

Definition inf32 (negative : bool) : @fl_nn 24 128 :=
  exist _ (@Binary.B754_infinity 24 128 negative) eq_refl.

Definition one32 : @fl_nn 24 128 := bound32 false 8388608 (-23) eq_refl.
Definition two32 : @fl_nn 24 128 := bound32 false 8388608 (-22) eq_refl.
Definition half32 : @fl_nn 24 128 := bound32 false 8388608 (-24) eq_refl.
Definition minus_one32 : @fl_nn 24 128 := bound32 true 8388608 (-23) eq_refl.
Definition minus_two32 : @fl_nn 24 128 := bound32 true 8388608 (-22) eq_refl.
Definition tiny32 : @fl_nn 24 128 := bound32 false 1 (-149) eq_refl.
Definition normal32 : @fl_nn 24 128 := bound32 false 8388608 (-149) eq_refl.
Definition maximum32 : @fl_nn 24 128 := bound32 false 16777215 104 eq_refl.
Definition halfway32 : @fl_nn 24 128 := bound32 false 8388608 (-47) eq_refl.

Definition one64 : @fl_nn 53 1024 := bound64 false 4503599627370496 (-52) eq_refl.
Definition two64 : @fl_nn 53 1024 := bound64 false 4503599627370496 (-51) eq_refl.
Definition half64 : @fl_nn 53 1024 := bound64 false 4503599627370496 (-53) eq_refl.
Definition tiny64 : @fl_nn 53 1024 := bound64 false 1 (-1074) eq_refl.
Definition normal64 : @fl_nn 53 1024 := bound64 false 4503599627370496 (-1074) eq_refl.
Definition maximum64 : @fl_nn 53 1024 := bound64 false 9007199254740991 971 eq_refl.

Definition numeric32 (lo hi : @fl_nn 24 128) : @fl_interval 24 128 :=
  FlInterval lo hi false false false true.

Definition numeric64 (lo hi : @fl_nn 53 1024) : @fl_interval 53 1024 :=
  FlInterval lo hi false false false true.

Definition point32 (x : @fl_nn 24 128) : @fl_interval 24 128 := numeric32 x x.
Definition point64 (x : @fl_nn 53 1024) : @fl_interval 53 1024 := numeric64 x x.

Definition zero_only32 (negative : bool) : @fl_interval 24 128 :=
  FlInterval (inf32 false) (inf32 true) false negative (negb negative) false.

Definition interval_view32 (x : @fl_interval 24 128) :
    (Z * Z * bool * bool * bool * bool)%type :=
  (Bits.bits_of_b32 (proj1_sig (flo x)), Bits.bits_of_b32 (proj1_sig (fhi x)), may_nan x,
   may_neg_zero x, may_pos_zero x, may_subnormal x).

Definition interval_view64 (x : @fl_interval 53 1024) :
    (Z * Z * bool * bool * bool * bool)%type :=
  (Bits.bits_of_b64 (proj1_sig (flo x)), Bits.bits_of_b64 (proj1_sig (fhi x)), may_nan x,
   may_neg_zero x, may_pos_zero x, may_subnormal x).

Definition observed_arithmetic32 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_bin FAdd (numeric32 one32 two32) (point32 one32);
     fl_bin FSub (numeric32 one32 two32) (point32 one32);
     fl_bin FMul (numeric32 one32 two32) (numeric32 minus_two32 minus_one32);
     fl_bin FDiv (numeric32 one32 two32) (numeric32 one32 two32)].

Example float_directed_arithmetic32 : observed_arithmetic32 =
  [(1073741824, 1077936128, false, false, false, false);
   (2147483648, 1065353216, false, true, true, true);
   (3229614080, 3212836864, false, false, false, false);
   (1056964608, 1073741824, false, false, false, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_rounding32 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_bin FAdd (point32 one32) (point32 halfway32);
     fl_bin FMul (point32 tiny32) (point32 half32);
     fl_bin FMul (point32 (bound32 true 1 (-149) eq_refl)) (point32 half32);
     fl_bin FAdd (point32 tiny32) (point32 tiny32);
     fl_bin FSub (point32 normal32) (point32 tiny32);
     fl_bin FAdd (point32 normal32) (point32 tiny32);
     fl_bin FMul (point32 maximum32) (point32 two32);
     fl_bin FDiv (point32 maximum32) (point32 tiny32)].

Example float_directed_rounding32 : observed_rounding32 =
  [(1065353216, 1065353217, false, false, false, false);
   (0, 1, false, true, true, true);
   (2147483649, 2147483648, false, true, true, true);
   (2, 2, false, false, false, true);
   (8388607, 8388607, false, false, false, true);
   (8388609, 8388609, false, false, false, false);
   (2139095039, 2139095040, false, false, false, false);
   (2139095039, 2139095040, false, false, false, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_arithmetic64 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view64
    [fl_bin FAdd (numeric64 one64 two64) (point64 one64);
     fl_bin FDiv (numeric64 one64 two64) (numeric64 one64 two64);
     fl_bin FMul (point64 tiny64) (point64 half64);
     fl_bin FSub (point64 normal64) (point64 tiny64);
     fl_bin FMul (point64 maximum64) (point64 two64)].

Example float_directed_arithmetic64 : observed_arithmetic64 =
  [(4611686018427387904, 4613937818241073152, false, false, false, false);
   (4602678819172646912, 4611686018427387904, false, false, false, false);
   (0, 1, false, true, true, true);
   (4503599627370495, 4503599627370495, false, false, false, true);
   (9218868437227405311, 9218868437227405312, false, false, false, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_exceptional32 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_bin FDiv (point32 (inf32 false)) (point32 (inf32 false));
     fl_bin FAdd (point32 (inf32 false)) (point32 (inf32 true));
     fl_bin FSub (point32 (inf32 false)) (point32 (inf32 false));
     fl_bin FMul (zero_only32 false) (point32 (inf32 false));
     fl_bin FDiv (point32 one32) (zero_only32 false);
     fl_bin FDiv (point32 one32) (zero_only32 true);
     fl_bin FDiv (point32 minus_one32) (zero_only32 false);
     fl_bin FDiv (point32 one32) (point32 (inf32 false));
     fl_bin FDiv (point32 minus_one32) (point32 (inf32 false));
     fl_bin FDiv (zero_only32 false) (zero_only32 true);
     fl_bin FDiv (numeric32 one32 two32) (numeric32 minus_one32 one32);
     fl_bin FAdd fl_bottom (point32 one32);
     fl_bin FAdd (FlInterval (inf32 false) (inf32 true) true false false false)
       (point32 one32);
     fl_bin FAdd (zero_only32 false) (point32 one32);
     fl_bin FMul (point32 (inf32 true)) (point32 minus_one32)].

Example float_exceptional_arithmetic32 : observed_exceptional32 =
  [(2139095040, 4286578688, true, false, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (2139095040, 2139095040, false, false, false, false);
   (4286578688, 4286578688, false, false, false, false);
   (4286578688, 4286578688, false, false, false, false);
   (2139095040, 4286578688, false, false, true, false);
   (2139095040, 4286578688, false, true, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (4286578688, 2139095040, false, true, true, true);
   (2139095040, 4286578688, false, false, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (1065353216, 1065353216, false, false, false, false);
   (2139095040, 2139095040, false, false, false, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition signed_range32 : @fl_interval 24 128 :=
  FlInterval minus_two32 one32 true true false true.

Definition observed_unary_refinement32 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_neg signed_range32; fl_abs signed_range32;
     fl_abs (numeric32 minus_two32 minus_one32);
     fst (fl_assume_lt signed_range32
       (FlInterval one32 one32 true false false false));
     snd (fl_assume_lt signed_range32
       (FlInterval one32 one32 true false false false))].

Example float_unary_refinement32 : observed_unary_refinement32 =
  [(3212836864, 1073741824, true, false, true, true);
   (0, 1073741824, true, false, true, true);
   (1065353216, 1073741824, false, false, false, true);
   (3221225472, 1065353216, false, true, false, true);
   (1065353216, 1065353216, false, false, false, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition float_any_view32 (a : fl_any) : option (Z * Z * bool * bool * bool * bool) :=
  match a with FlA32 interval => Some (interval_view32 interval) | _ => None end.

Definition observed_numeric_ssa : list (option (Z * Z * bool * bool * bool * bool)) :=
  Eval vm_compute in map float_any_view32
    [op_abs float_ssa_domain (OExt 0) [FlA32 (numeric32 one32 two32); FlA32 (point32 one32)];
     op_abs float_ssa_domain (OExt 1) [FlA32 (point32 one32); FlA32 (point32 one32)];
     op_abs float_ssa_domain (OExt 10) [FlA32 (point32 one32); FlA32 (point32 one32)];
     op_abs float_ssa_domain (OExt 8) [FlA32 (point32 one32); FlA32 (point32 two32)]] ++
    map float_any_view32 (assume_args float_ssa_domain (OExt 8) true
      [FlA32 signed_range32; FlA32 (point32 one32)]) ++
    map float_any_view32 (assume_args float_ssa_domain (OExt 8) false
      [FlA32 signed_range32; FlA32 (point32 one32)]).

Example float_numeric_ssa_transfers : observed_numeric_ssa =
  [Some (1073741824, 1077936128, false, false, false, false); None; None; None;
   Some (3221225472, 1065353216, false, true, false, true);
   Some (1065353216, 1065353216, false, false, false, true);
   Some (3221225472, 1065353216, true, true, false, true);
   Some (1065353216, 1065353216, false, false, false, true)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition multi_parameter_entry : ssa_block :=
  SBlock [(0, TyF32); (2, TyF32)] [] (TJump 1 [0; 2; 0]).

Definition multi_parameter_target : ssa_block :=
  SBlock [(1, TyF32); (3, TyF32); (4, TyF32)] [] (TRet 1).

Definition multi_parameter_program : program :=
  Program [(0, FDef 0 [(0, multi_parameter_entry); (1, multi_parameter_target)] TyF32)]
    0 float_ext_sigs.

Example float_multi_parameter_checked : wf_check multi_parameter_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_multi_parameter_inputs :
    list (vid * bool) * list (vid * nan_demand) * list (vid * nan_demand) :=
  Eval vm_compute in
  (flat_map (fun x => dback (ssa_demand_view test_float_ext multi_parameter_program 0)
      (SsaEdge 0 1 0) x true) [1; 3; 4],
   flat_map (fun x => dback (ssa_nan_demand_view test_float_ext multi_parameter_program 0)
      (SsaEdge 0 1 0) x (Demanded true false)) [1; 3; 4],
   dback (ssa_nan_demand_view test_float_ext multi_parameter_program 0) (SsaEdge 0 1 1) 1
      (Demanded true false)).

Example float_raw_selected_parameter_order_and_duplicates : observed_multi_parameter_inputs =
  ([(0, true); (2, true); (0, true)],
   [(0, Demanded true false); (2, Demanded true false); (0, Demanded true false)], []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_memory_exits : list (list (vid * nan_demand)) := Eval vm_compute in
  map (dexit (ssa_nan_demand_view test_float_ext unreachable_program 0)) [(3, 0); (3, 1); (3, 2)].

Example float_raw_memory_exits_remain_full : observed_memory_exits =
  [[]; [(6, Demanded true true)]; []].
Proof.
  vm_compute; reflexivity.
Qed.

Definition call_entry : ssa_block :=
  SBlock [(0, TyFun); (1, TyF32)] [] (TCall (CIndirect 0 [TyF32] TyF32) [1] 1).

Definition call_target : ssa_block := SBlock [(2, TyF32)] [] (TRet 2).

Definition call_program : program :=
  Program [(0, FDef 0 [(0, call_entry); (1, call_target)] TyF32)] 0 float_ext_sigs.

Example float_call_program_checked : wf_check call_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_call_demands :
    bool * list (vid * nan_demand) * list (vid * nan_demand) := Eval vm_compute in
  (match def (ssa_block_view test_float_ext call_program 0) 2 with
   | Arbitrary => true | _ => false end,
   dback (ssa_nan_demand_view test_float_ext call_program 0) (SsaEdge 0 1 0) 2
      (Demanded true true),
   dnec (ssa_nan_demand_view test_float_ext call_program 0) (SsaEdge 0 1 0)).

Example float_call_result_arbitrary_and_inputs_full : observed_call_demands =
  (true, [], [(0, Demanded true true); (1, Demanded true true)]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_extra64 : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view64
    [fl_bin FDiv (point64 maximum64) (point64 tiny64);
     fl_bin FDiv
       (point64 (exist _ (@Binary.B754_infinity 53 1024 false) eq_refl))
       (point64 (exist _ (@Binary.B754_infinity 53 1024 false) eq_refl));
     fl_neg (numeric64 one64 two64);
     fl_abs (numeric64 (bound64 true 4503599627370496 (-51) eq_refl)
       (bound64 true 4503599627370496 (-52) eq_refl))].

Example float_extra_boundaries64 : observed_extra64 =
  [(9218868437227405311, 9218868437227405312, false, false, false, false);
   (9218868437227405312, 18442240474082181120, true, false, false, false);
   (13835058055282163712, 13830554455654793216, false, false, false, true);
   (4607182418800017408, 4611686018427387904, false, false, false, true)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_zero_only_results : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_bin FAdd (zero_only32 false) (zero_only32 true);
     fl_bin FSub (zero_only32 false) (zero_only32 false);
     fl_bin FMul (zero_only32 false) (point32 minus_one32);
     fl_bin FDiv (zero_only32 false) (point32 one32)].

Example float_zero_only_results_exclude_subnormals : observed_zero_only_results =
  [(0, 0, false, true, true, false);
   (2147483648, 0, false, true, true, false);
   (2147483648, 2147483648, false, true, true, false);
   (0, 0, false, true, true, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.

Definition observed_abs_empty_bounds : list (Z * Z * bool * bool * bool * bool) :=
  Eval vm_compute in map interval_view32
    [fl_abs fl_bottom;
     fl_abs (FlInterval (inf32 false) (inf32 true) true false false false);
     fl_abs (zero_only32 true); fl_abs (zero_only32 false)].

Example float_abs_preserves_empty_numeric_bounds : observed_abs_empty_bounds =
  [(2139095040, 4286578688, false, false, false, false);
   (2139095040, 4286578688, true, false, false, false);
   (2139095040, 4286578688, false, false, true, false);
   (2139095040, 4286578688, false, false, true, false)]%Z.
Proof.
  vm_compute; reflexivity.
Qed.
