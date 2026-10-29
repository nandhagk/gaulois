(** * Full SSA effects and call regressions

    The fixtures exercise exact resolver choices and reachable full-machine memory traps.
    For example, freeing a freshly allocated block makes the following load trap.
    Builds on: ExamplesSsaEffects and ExamplesSsaSyntaxTest. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaViews ExamplesSsaEffects.
From Gaulois.Tests.Examples Require Import ExamplesSsaSyntaxTest.
Import List.ListNotations.
Local Open Scope nat_scope.

Example effects_fixture_accepted : wf_check ssa_effects_fixture = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example effects_fixture_well_formed : wf_program no_ext ssa_effects_fixture.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact effects_fixture_accepted].
Qed.

Example direct_target_exact : ssa_resolver return_program (0, 0) = [1].
Proof.
  vm_compute; reflexivity.
Qed.

Example indirect_targets_compatible_only : ssa_resolver memory_calls (0, 0) = [1].
Proof.
  vm_compute; reflexivity.
Qed.

Example indirect_compatible_target :
  option_map (fun target => fst (fst target))
    (callee_def memory_calls (env_set (fun _ => None) 4 (VFun 1))
      (CIndirect 4 [TyI32] TyI32)) = Some 1 /\
  callee_def memory_calls (env_set (fun _ => None) 4 (VFun 0))
    (CIndirect 4 [TyI32] TyI32) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example resolver_preserves_multiple_target_order :
  let identity x := FDef 0 [(0, SBlock [(x, TyI32)] [] (TRet x))] TyI32 in
  let P := Program (funcs memory_calls ++ [(7, identity 20); (3, identity 21)]) 0 [] in
  wf_check P = true /\ ssa_resolver P (0, 0) = [1; 7; 3].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example functions_sites_and_stack :
  functions (ssa_calls no_ext return_program) = [0; 1] /\
  roots (ssa_calls no_ext return_program) = [0] /\
  sites_of (ssa_calls no_ext return_program) 0 = [(0, 0)] /\
  sites_of (ssa_calls no_ext return_program) 1 = [] /\
  here (ssa_calls no_ext return_program) called_state = 1 /\
  frames (ssa_calls no_ext return_program) called_state = [(0, (0, 0))] /\
  active (ssa_calls no_ext return_program) called_state = [1; 0].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example direct_call_and_return_observations :
  step_s no_ext return_program (Limits 8 8) calling_state [] called_state /\
  step_s no_ext return_program (Limits 8 8) called_state [] returned_state /\
  frames (ssa_calls no_ext return_program) returned_state = [].
Proof.
  split; [exact direct_call_pushes_frame|].
  split; [exact return_binds_only_continuation_parameter|reflexivity].
Qed.

Example indirect_call_pushes_compatible_frame :
  let env := env_set (env_set (fun _ => None) 3 (VInt W32 5%Z)) 4 (VFun 1) in
  step_s no_ext memory_calls (Limits 8 8)
    (State [SFrame 0 0 5 env 0] (fun _ => None) 0) []
    (State [SFrame 1 0 0 (env_set (fun _ => None) 6 (VInt W32 5%Z)) 0;
      SFrame 0 0 5 env 1] (fun _ => None) 0).
Proof.
  cbn zeta; apply SCall with (c := CIndirect 4 [TyI32] TyI32) (args := [3])
    (cs := [VInt W32 5%Z]) (fd := arithmetic_callee)
    (b := SBlock [(6, TyI32)]
      [IOp 7 (OConst (VInt W32 1%Z)) []; IOp 8 (OBin W32 BAdd) [6; 7]]
      (TBr 8 1 [8] 2 [6])).
  - exists memory_caller, (SBlock [(0, TyI64); (1, TyI32)]
      [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
       IOp 4 (OConst (VFun 1)) []] (TCall (CIndirect 4 [TyI32] TyI32) [3] 1)).
    repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example representative_effect_flags :
  (reads ssa_effects (AnInstr (IAlloc 1 0)),
   allocates ssa_effects (AnInstr (IAlloc 1 0)),
   may_stop ssa_effects (AnInstr (IAlloc 1 0)),
   may_trap ssa_effects (AnInstr (ILoad 2 TyI32 M1 1)),
   observes ssa_effects (AnInstr (IOutput 2)),
   calls ssa_effects (ATerm (TCall (CDirect 1) [0] 1)),
   may_diverge ssa_effects (ATerm (TCall (CDirect 1) [0] 1)),
   observes ssa_effects (ATerm (TRet 2))) =
  (true, true, true, true, true, true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example pure_and_nonwriting_effect_flags :
  (reads ssa_effects (AnInstr (IOutput 2)),
   writes ssa_effects (AnInstr (IAlloc 1 0)),
   writes ssa_effects (AnInstr (ILoad 2 TyI32 M1 1)),
   may_trap ssa_effects (AnInstr (IOp 2 (OBin W32 BAdd) [0; 1])),
   may_trap ssa_effects (AnInstr (IOp 2 (OBin W32 BDivU) [0; 1])),
   may_trap ssa_effects (AnInstr (IOp 2 (OExt 7) [0])),
   may_stop ssa_effects (ATerm (TRet 2)),
   calls ssa_effects (ATerm (TJump 1 [0])),
   observes ssa_effects (ATerm (TCall (CDirect 1) [0] 1))) =
  (false, false, false, false, true, true, false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example instruction_lookup_boundaries :
  instr_at (ssa_effects_view no_ext ssa_effects_fixture (Limits 8 8))
    ssa_effects_initial_state = Some (AnInstr (IAlloc 1 0)) /\
  instr_at (ssa_effects_view no_ext ssa_effects_fixture (Limits 8 8))
    ssa_effects_trap_state = Some (AnInstr (ILoad 2 TyI32 M1 1)) /\
  ssa_current ssa_effects_fixture
    (State [SFrame 0 0 3 ssa_effects_allocated_env 0] (fun _ => None) 0) =
    Some (ATerm (TRet 2)) /\
  ssa_current ssa_effects_fixture
    (State [SFrame 0 0 4 ssa_effects_allocated_env 0] (fun _ => None) 0) = None /\
  ssa_current ssa_effects_fixture (State [] (fun _ => None) 0) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example effects_fixture_initial :
  initial (ssa_semantics no_ext ssa_effects_fixture (Limits 8 8)) ssa_effects_initial_state.
Proof.
  exists (FDef 0 [(0, SBlock [(0, TyI64)]
    [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2))] TyI32),
    (SBlock [(0, TyI64)] [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2)),
    [VInt W64 8%Z], ssa_effects_initial_env.
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor].
Qed.

Example effects_fixture_allocates :
  step_s no_ext ssa_effects_fixture (Limits 8 8)
    ssa_effects_initial_state [] ssa_effects_allocated_state.
Proof.
  apply SAlloc with (n := 0) (z := 8%Z).
  - exists (FDef 0 [(0, SBlock [(0, TyI64)]
      [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2))] TyI32),
      (SBlock [(0, TyI64)] [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2)).
    repeat split; reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example effects_fixture_frees :
  step_s no_ext ssa_effects_fixture (Limits 8 8)
    ssa_effects_allocated_state [] ssa_effects_trap_state.
Proof.
  change (step_s no_ext ssa_effects_fixture (Limits 8 8) ssa_effects_allocated_state []
    (State [advance (SFrame 0 0 1 ssa_effects_allocated_env 0) ssa_effects_allocated_env]
      (memory_set
        (memory_set (fun _ => None) 0 (MBlock 8 (fun _ => MInt 0%Z) true 1)) 0
        (MBlock 8 (fun _ => MInt 0%Z) false 1)) 1)).
  apply SFree with (p := 1) (mb := MBlock 8 (fun _ => MInt 0%Z) true 1).
  - exists (FDef 0 [(0, SBlock [(0, TyI64)]
      [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2))] TyI32),
      (SBlock [(0, TyI64)] [IAlloc 1 0; IFree 1; ILoad 2 TyI32 M1 1] (TRet 2)).
    repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example trapping_load_reachable :
  reachable_state (ssa_semantics no_ext ssa_effects_fixture (Limits 8 8))
    ssa_effects_trap_state.
Proof.
  exists ssa_effects_initial_state, []; split; [exact effects_fixture_initial|].
  eapply exec_step with (l := []) (tr := []); [exact effects_fixture_allocates|].
  eapply exec_step with (l := []) (tr := []); [exact effects_fixture_frees|constructor].
Qed.

Example dead_block_load_traps :
  memory_load TyI32 M1 (MBlock 8 (fun _ => MInt 0%Z) false 1) 0%Z = None /\
  mem ssa_effects_trap_state 0 = Some (MBlock 8 (fun _ => MInt 0%Z) false 1) /\
  depth (ssa_effects_view no_ext ssa_effects_fixture (Limits 8 8))
    ssa_effects_trap_state = 1 /\
  next_block ssa_effects_trap_state = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example dead_block_load_is_a_full_machine_trap :
  trapped (ssa_endings no_ext ssa_effects_fixture (Limits 8 8)) ssa_effects_trap_state.
Proof.
  split.
  - intros [tr [t Hstep]].
    unfold ssa_effects_trap_state in Hstep; inversion Hstep; subst;
      match goal with
      | Hat : at_instr _ _ _ |- _ =>
        pose proof (ssa_current_instr _ _ [] (mem ssa_effects_trap_state) 1 _ Hat)
          as Haction
      | Hat : at_term _ _ _ |- _ =>
        pose proof (ssa_current_term _ _ [] (mem ssa_effects_trap_state) 1 _ Hat)
          as Haction
      end;
      vm_compute in Haction;
      try discriminate Haction.
    inversion Haction; subst.
    match goal with
    | Hpointer : fenv _ 1 = Some (VPtr _ _) |- _ =>
      vm_compute in Hpointer; injection Hpointer as <- <-
    end.
    match goal with
    | Hmemory : _ 0 = Some _ |- _ =>
      vm_compute in Hmemory; injection Hmemory as <-
    end.
    match goal with
    | Hload : memory_load _ _ _ _ = Some _ |- _ =>
      discriminate Hload
    end.
  - split.
    + intros [fr [fd [b [Hstack [Hf [Hb Hpast]]]]]].
      change ([SFrame 0 0 2 ssa_effects_allocated_env 0] = [fr]) in Hstack.
      injection Hstack as <-.
      vm_compute in Hf; injection Hf as <-.
      vm_compute in Hb; injection Hb as <-; cbn in Hpast; lia.
    + intro Hstop.
      pose proof (ssa_stop_flag ssa_effects_fixture (Limits 8 8) ssa_effects_trap_state
        (AnInstr (ILoad 2 TyI32 M1 1)) eq_refl Hstop) as Hflag.
      discriminate Hflag.
Qed.

Example full_effect_and_call_laws_apply :
  effects_laws (ssa_semantics no_ext ssa_effects_fixture (Limits 8 8))
    (ssa_endings no_ext ssa_effects_fixture (Limits 8 8)) ssa_effects
    (ssa_effects_view no_ext ssa_effects_fixture (Limits 8 8)) /\
  calls_view_laws (ssa_semantics no_ext return_program (Limits 8 8))
    (ssa_calls no_ext return_program) (ssa_resolver return_program).
Proof.
  split.
  - apply ssa_effects_laws; exact effects_fixture_well_formed.
  - apply ssa_calls_laws, wf_check_sound.
    + apply ext_respects_nil; reflexivity.
    + exact direct_call_program_accepted.
Qed.
