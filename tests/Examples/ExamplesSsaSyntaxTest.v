(** * Computed SSA syntax, typing and semantics tests

    These examples exercise accepted and rejected programs and concrete operator, memory
    and frame observations. For example, storing four bytes and loading them preserves an I32.
    Builds on: the four ExamplesSsa theories. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Examples.Ssa Require Import
  ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics ExamplesSsaTypingProofs.
Import List.ListNotations.
Local Open Scope nat_scope.

Example nontrivial_program_accepted : wf_check memory_calls = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nontrivial_program_well_formed : wf_program no_ext memory_calls.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact nontrivial_program_accepted].
Qed.

Example wrong_width_rejected : wf_check bad_operand = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example use_before_definition_rejected : wf_check late_definition = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_parameters_accepted : wf_check parallel_loop = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example parallel_parameter_swap :
  match bind_params
    (env_set (env_set (fun _ => None) 0 (VInt W32 3%Z)) 1 (VInt W32 7%Z))
    [(0, TyI32); (1, TyI32)] [VInt W32 7%Z; VInt W32 3%Z] with
  | Some env => (env 0, env 1)
  | None => (None, None)
  end = (Some (VInt W32 7%Z), Some (VInt W32 3%Z)).
Proof.
  vm_compute; reflexivity.
Qed.

Example wrapped_switch_uses_first_match :
  switch_target 0%Z [(4294967296%Z, 1, [2]); (0%Z, 3, [4])] 5 [6] = (1, [2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example integer_constants_wrap :
  op_eval no_ext (OConst (VInt W32 (-1)%Z)) [] = Some (VInt W32 4294967295%Z) /\
  op_eval no_ext (OConst (VInt W64 18446744073709551616%Z)) [] = Some (VInt W64 0%Z).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example word_boundaries :
  op_eval no_ext (OBin W32 BAdd) [VInt W32 4294967295%Z; VInt W32 1%Z] =
    Some (VInt W32 0%Z) /\
  op_eval no_ext OZext [VInt W32 4294967295%Z] = Some (VInt W64 4294967295%Z) /\
  op_eval no_ext OTrunc [VInt W64 18446744073709551615%Z] =
    Some (VInt W32 4294967295%Z).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example invalid_integer_inputs_trap :
  op_eval no_ext (OBin W32 BAdd) [VInt W32 (-1)%Z; VInt W32 0%Z] = None /\
  op_eval no_ext (OBin W32 BAdd) [VInt W32 0%Z; VInt W32 4294967296%Z] = None /\
  op_eval no_ext OZext [VInt W32 4294967296%Z] = None /\
  op_eval no_ext OTrunc [VInt W64 (-1)%Z] = None /\
  op_eval no_ext (OBin W64 BDivU) [VInt W64 1%Z; VInt W64 0%Z] = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example shifts_comparisons_and_pointer_offset :
  op_eval no_ext (OBin W64 BShl) [VInt W64 3%Z; VInt W64 64%Z] = Some (VInt W64 3%Z) /\
  op_eval no_ext (OBin W32 BLtS) [VInt W32 4294967295%Z; VInt W32 0%Z] =
    Some (VInt W32 1%Z) /\
  op_eval no_ext OPtrAdd [VPtr 0 3%Z; VInt W64 18446744073709551615%Z] =
    Some (VPtr 0 2%Z).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example little_endian_memory :
  match memory_store M4 zero_block 1%Z (VInt W32 305419896%Z) with
  | Some mb =>
    (mbytes mb 1%Z, mbytes mb 4%Z, memory_load TyI32 M4 mb 1%Z,
      memory_load TyI64 M8 mb 1%Z)
  | None => (MInt 0%Z, MInt 0%Z, None, None)
  end = (MInt 120%Z, MInt 18%Z, Some (VInt W32 305419896%Z), None).
Proof.
  vm_compute; reflexivity.
Qed.

Example pointer_fragments_round_trip :
  match memory_store M8 zero_block 0%Z (VPtr 17 3%Z) with
  | Some mb => (memory_load TyPtr M8 mb 0%Z, memory_load TyI64 M8 mb 0%Z)
  | None => (None, None)
  end = (Some (VPtr 17 3%Z), None).
Proof.
  vm_compute; reflexivity.
Qed.

Example freed_memory_retains_site :
  let freed := MBlock (msz zero_block) (mbytes zero_block) false (msite zero_block) in
  (memory_load TyI32 M1 freed 0%Z, msite freed) = (None, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example indirect_call_signature_checked :
  let env := env_set (fun _ => None) 4 (VFun 1) in
  callee_def memory_calls env (CIndirect 4 [TyI32] TyI32) =
    Some (1, arithmetic_callee, SBlock [(6, TyI32)]
      [IOp 7 (OConst (VInt W32 1%Z)) []; IOp 8 (OBin W32 BAdd) [6; 7]]
      (TBr 8 1 [8] 2 [6])) /\
  callee_def memory_calls env (CIndirect 4 [TyI64] TyI32) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example allocation_step :
  step_s no_ext memory_calls (Limits 8 8) allocation_start []
    (State [advance (SFrame 0 0 0 allocation_env 0)
      (env_set allocation_env 2 (VPtr 0 0%Z))]
      (memory_set (fun _ => None) 0 zero_block) 1).
Proof.
  apply SAlloc with (n := 0) (z := 8%Z).
  - exists memory_caller, (SBlock [(0, TyI64); (1, TyI32)]
      [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
        IOp 4 (OConst (VFun 1)) []]
      (TCall (CIndirect 4 [TyI32] TyI32) [3] 1)); vm_compute; repeat split; reflexivity.
  - vm_compute; reflexivity.
  - cbn; lia.
Qed.

Example allocation_resource_stop :
  stopped (ssa_endings no_ext memory_calls (Limits 8 0)) allocation_start.
Proof.
  exists (SFrame 0 0 0 allocation_env 0), []; split; [reflexivity|right].
  exists 2, 0, 8%Z; split.
  - exists memory_caller, (SBlock [(0, TyI64); (1, TyI32)]
      [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
        IOp 4 (OConst (VFun 1)) []]
      (TCall (CIndirect 4 [TyI32] TyI32) [3] 1)); vm_compute; repeat split; reflexivity.
  - split; [vm_compute; reflexivity|constructor].
Qed.

Example declared_extension_accepted : wf_check extension_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example undeclared_extension_rejected :
  wf_check (Program (funcs extension_program) 0 []) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example extension_host_agreement : ext_respects no_ext extension_program.
Proof.
  intros tag ps r cs v Hin Htypes Hvalid Heval; discriminate.
Qed.

Example allocation_size_is_a_word :
  valid_cval (VInt W64 18446744073709551615%Z) /\
  ~ valid_cval (VInt W64 18446744073709551616%Z).
Proof.
  cbn [valid_cval]; lia.
Qed.

Example allocation_start_reachable :
  reachable_state (ssa_semantics no_ext memory_calls (Limits 8 8)) allocation_start.
Proof.
  exists allocation_start, []; split; [|constructor].
  exists memory_caller, (SBlock [(0, TyI64); (1, TyI32)]
    [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
      IOp 4 (OConst (VFun 1)) []]
    (TCall (CIndirect 4 [TyI32] TyI32) [3] 1)),
    [VInt W64 8%Z; VInt W32 5%Z], allocation_env.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  - constructor; [cbn [valid_cval]; lia|].
    constructor; [cbn [valid_cval]; lia|constructor].
  - split; reflexivity.
Qed.

Example reachable_allocation_extent :
  exists z, allocation_env 0 = Some (VInt W64 z) /\ (0 <= z < 2 ^ 64)%Z.
Proof.
  eapply (allocation_size_in_range no_ext memory_calls (Limits 8 8) allocation_start
    (SFrame 0 0 0 allocation_env 0) memory_caller
    (SBlock [(0, TyI64); (1, TyI32)]
      [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
        IOp 4 (OConst (VFun 1)) []]
      (TCall (CIndirect 4 [TyI32] TyI32) [3] 1)) 2 0).
  - exact nontrivial_program_well_formed.
  - exact allocation_start_reachable.
  - left; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
Qed.

Example direct_call_program_accepted : wf_check return_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example direct_call_pushes_frame :
  step_s no_ext return_program (Limits 8 8) calling_state [] called_state.
Proof.
  apply SCall with (c := CDirect 1) (args := [0]) (cs := [VInt W32 42%Z])
    (fd := FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)
    (b := SBlock [(2, TyI32)] [] (TRet 2)).
  - exists (FDef 0
      [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
       (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
      (SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
      vm_compute; repeat split; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example return_binds_only_continuation_parameter :
  step_s no_ext return_program (Limits 8 8) called_state [] returned_state.
Proof.
  apply SReturn with (x := 2) (v := VInt W32 42%Z).
  - exists (FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
      (SBlock [(2, TyI32)] [] (TRet 2)); vm_compute; repeat split; reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
Qed.

Example main_return_emits_result :
  step_s no_ext return_program (Limits 8 8) returned_state [EvRet (VInt W32 42%Z)]
    (State [SFrame 0 1 1 (env_set caller_env 1 (VInt W32 42%Z)) 1] (fun _ => None) 0).
Proof.
  apply SReturnMain with (x := 1).
  - exists (FDef 0
      [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
       (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
      (SBlock [(1, TyI32)] [] (TRet 1)); vm_compute; repeat split; reflexivity.
  - reflexivity.
Qed.

Example declared_extension_evaluates :
  op_eval identity_ext (OExt 7) [VInt W32 9%Z] = Some (VInt W32 9%Z).
Proof.
  reflexivity.
Qed.

Example identity_extension_respects_signature : ext_respects identity_ext extension_program.
Proof.
  intros tag ps r cs v Hin Htypes Hvalid Heval.
  cbn [extension_program ext_sigs] in Hin; destruct Hin as [Heq|Hin]; [|contradiction].
  injection Heq as <- <- <-.
  destruct (typed_single_i32 cs Htypes) as [z ->].
  injection Heval as <-; split; [reflexivity|].
  inversion Hvalid as [|? ? Hz Hnil]; exact Hz.
Qed.

Example arithmetic_and_bitwise_results :
  map (fun o => op_eval no_ext (OBin W32 o) [VInt W32 6%Z; VInt W32 3%Z])
    [BSub; BMul; BDivU; BAnd; BOr; BXor; BShrU; BEq; BLtU] =
    map (fun z => Some (VInt W32 z)) [3%Z; 18%Z; 2%Z; 2%Z; 7%Z; 5%Z; 0%Z; 0%Z; 0%Z].
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_pointer_overwrite_traps :
  match memory_store M8 zero_block 0%Z (VPtr 17 0%Z) with
  | Some mb =>
    match memory_store M1 mb 3%Z (VInt W32 1%Z) with
    | Some mb' => memory_load TyPtr M8 mb' 0%Z
    | None => None
    end
  | None => None
  end = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example invalid_memory_ranges_trap :
  memory_load TyI32 M1 zero_block (-1)%Z = None /\
  memory_load TyI64 M8 zero_block 1%Z = None /\
  memory_store M2 zero_block 7%Z (VInt W32 1%Z) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example switch_program_accepted : wf_check switch_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example non_dominating_definition_rejected : wf_check non_dominating_definition = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example prepared_function_lookup_keeps_first_binding :
  let first := FDef 0 [(0, SBlock [(0, TyI32)] [] (TRet 0))] TyI32 in
  let second := FDef 0 [(0, SBlock [(1, TyI64)] [] (TRet 1))] TyI64 in
  let duplicated := Program [(0, first); (0, second)] 0 [] in
  let prepared := Map.map (prepare_function (op_sig duplicated))
    (first_index (funcs duplicated)) in
  option_map prepared_def (Map.get nat_encoding 0 prepared) = Some first /\
  prepared_entry_sig prepared 0 = Some ([TyI32], TyI32) /\
  wf_check duplicated = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example prepared_block_lookup_keeps_first_binding :
  let first := SBlock [(0, TyI32)] [] (TRet 0) in
  let second := SBlock [(1, TyI64)] [] (TRet 1) in
  let fd := FDef 0 [(0, first); (0, second)] TyI32 in
  let duplicated := Program [(0, fd)] 0 [] in
  let prepared := prepare_function (op_sig duplicated) fd in
  Map.get nat_encoding 0 (prepared_block_index prepared) = Some first /\
  prepared_signature prepared = Some ([TyI32], TyI32) /\
  wf_check duplicated = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example prepared_extensions_keep_first_signature :
  let duplicated := Program (funcs extension_program) 0
    [(7, ([TyI32], TyI32)); (7, ([TyI64], TyI64))] in
  op_sig duplicated (OExt 7) = Some ([TyI32], TyI32) /\
  wf_check duplicated = true.
Proof.
  vm_compute; split; reflexivity.
Qed.
