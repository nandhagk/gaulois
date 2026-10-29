(** * Full SSA graph and memory fixtures

    These examples check concrete framed executions and the observations exposed by both views.
    For example, an allocated zero block is stored, loaded and freed while its site remains 2.
    Builds on: ExamplesSsaMemory, ExamplesSsaSemantics and ExamplesSsaTypingProofs. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemory.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaMemory.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition test_limits : limits := Limits 8 8.

Definition test_memory_block : ssa_block :=
  SBlock [(0, TyI64); (1, TyI32)]
    [IAlloc 2 0; IStore M4 2 1; ILoad 3 TyI32 M4 2; IFree 2;
      IOp 4 (OConst (VFun 1)) []]
    (TCall (CIndirect 4 [TyI32] TyI32) [3] 1).

Definition test_pointer_env : vid -> option cval := env_set allocation_env 2 (VPtr 0 0%Z).

Definition test_stored_block : mblock :=
  match memory_store M4 zero_block 0%Z (VInt W32 5%Z) with
  | Some b => b
  | None => zero_block
  end.

Definition test_loaded_env : vid -> option cval := env_set test_pointer_env 3 (VInt W32 5%Z).

Definition test_allocated : state :=
  State [SFrame 0 0 1 test_pointer_env 0] (memory_set (fun _ => None) 0 zero_block) 1.

Definition test_stored : state :=
  State [SFrame 0 0 2 test_pointer_env 0] (memory_set (mem test_allocated) 0 test_stored_block) 1.

Definition test_loaded : state :=
  State [SFrame 0 0 3 test_loaded_env 0] (mem test_stored) 1.

Definition test_freed : state :=
  State [SFrame 0 0 4 test_loaded_env 0]
    (memory_set (mem test_loaded) 0
      (MBlock (msz test_stored_block) (mbytes test_stored_block) false 2)) 1.

Example memory_fixture_accepted : wf_check memory_calls = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example memory_fixture_wf : wf_program no_ext memory_calls.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact memory_fixture_accepted].
Qed.

Example memory_initial_reachable :
  reachable_state (ssa_semantics no_ext memory_calls test_limits) allocation_start.
Proof.
  exists allocation_start, []; split; [|constructor].
  exists memory_caller, test_memory_block, [VInt W64 8%Z; VInt W32 5%Z], allocation_env.
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split.
  - constructor; [cbn [valid_cval]; lia|].
    constructor; [cbn [valid_cval]; lia|constructor].
  - split; reflexivity.
Qed.

Example memory_allocate_step :
  step_s no_ext memory_calls test_limits allocation_start [] test_allocated.
Proof.
  apply SAlloc with (n := 0) (z := 8%Z).
  - exists memory_caller, test_memory_block; vm_compute; repeat split; reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example memory_store_step :
  step_s no_ext memory_calls test_limits test_allocated [] test_stored.
Proof.
  eapply SStore with (p := 2) (x := 1) (b := 0) (off := 0%Z) (mb := zero_block)
    (v := VInt W32 5%Z).
  - exists memory_caller, test_memory_block; vm_compute; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example memory_load_step :
  step_s no_ext memory_calls test_limits test_stored [] test_loaded.
Proof.
  eapply SLoad with (t := TyI32) (sz := M4) (p := 2) (b := 0) (off := 0%Z)
    (mb := test_stored_block).
  - exists memory_caller, test_memory_block; vm_compute; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
Qed.

Example memory_free_step :
  step_s no_ext memory_calls test_limits test_loaded [] test_freed.
Proof.
  apply SFree with (p := 2) (b := 0) (mb := test_stored_block).
  - exists memory_caller, test_memory_block; vm_compute; repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example memory_run :
  exec (ssa_semantics no_ext memory_calls test_limits) allocation_start [] test_freed.
Proof.
  eapply exec_step with (l := []) (tr := []); [exact memory_allocate_step|].
  eapply exec_step with (l := []) (tr := []); [exact memory_store_step|].
  eapply exec_step with (l := []) (tr := []); [exact memory_load_step|].
  eapply exec_step with (l := []) (tr := []); [exact memory_free_step|constructor].
Qed.

Example memory_view_operations :
  map (mem_instr (ssa_mem_view no_ext memory_calls test_limits))
    [allocation_start; test_allocated; test_stored; test_loaded; test_freed] =
  [Some (MemAlloc 2 0); Some (MemStore 2 0%Z 4 1); Some (MemLoad 2 0%Z 4);
   Some (MemFree 2); None].
Proof.
  vm_compute; reflexivity.
Qed.

Example allocation_zero_bytes :
  match mem test_allocated 0 with
  | Some b => (msz b, mlive b, msite b, mbytes b 0%Z, mbytes b 7%Z)
  | None => (0, false, 0, MInt 1%Z, MInt 1%Z)
  end = (8, true, 2, MInt 0%Z, MInt 0%Z).
Proof.
  vm_compute; reflexivity.
Qed.

Example stored_bytes_and_loaded_value :
  (mbytes test_stored_block 0%Z, mbytes test_stored_block 1%Z,
    mbytes test_stored_block 4%Z, test_loaded_env 3) =
  (MInt 5%Z, MInt 0%Z, MInt 0%Z, Some (VInt W32 5%Z)).
Proof.
  vm_compute; reflexivity.
Qed.

Example historical_site_and_dead_bytes :
  (loc_site (ssa_mem_view no_ext memory_calls test_limits) test_freed 0,
   loc_of (ssa_mem_view no_ext memory_calls test_limits) test_freed (VPtr 0 0%Z),
   match mem test_freed 0 with
   | Some b => memory_load TyI32 M1 b 0%Z
   | None => None
   end) = (Some 2, Some 0, None).
Proof.
  vm_compute; reflexivity.
Qed.

Example absent_and_nonpointer_locations :
  (loc_of (ssa_mem_view no_ext memory_calls test_limits) test_freed (VPtr 1 0%Z),
   loc_of (ssa_mem_view no_ext memory_calls test_limits) test_freed (VInt W64 0%Z),
   loc_offset (ssa_mem_view no_ext memory_calls test_limits) test_freed (VPtr 0 (-3)%Z)) =
  (None, None, (-3)%Z).
Proof.
  vm_compute; reflexivity.
Qed.

Example allocation_full_edge :
  taken (ssa_full_view no_ext memory_calls test_limits) allocation_start [] test_allocated
    (FullEdge (0, 0, 0) (0, 0, 1) 0).
Proof.
  split.
  - vm_compute; tauto.
  - split; [reflexivity|left; exists (IAlloc 2 0); split; [|reflexivity]].
    exists memory_caller, test_memory_block; vm_compute; repeat split; reflexivity.
Qed.

Example full_graph_and_memory_laws :
  graph_view_laws (ssa_semantics no_ext memory_calls test_limits)
    (ssa_full_view no_ext memory_calls test_limits) /\
  mem_view_laws (ssa_semantics no_ext memory_calls test_limits)
    (ssa_mem_view no_ext memory_calls test_limits).
Proof.
  split; [apply ssa_full_view_laws|apply ssa_mem_laws]; exact memory_fixture_wf.
Qed.

Example site_stability_on_actual_run :
  loc_site (ssa_mem_view no_ext memory_calls test_limits) test_freed 0 = Some 2.
Proof.
  assert (Hallocated : reachable_state (ssa_semantics no_ext memory_calls test_limits)
    test_allocated).
  { eapply reachable_state_step; [exact memory_initial_reachable|exact memory_allocate_step]. }
  eapply (loc_site_preserved (ssa_semantics no_ext memory_calls test_limits)
    (ssa_mem_view no_ext memory_calls test_limits)).
  - apply ssa_mem_laws; exact memory_fixture_wf.
  - exact Hallocated.
  - eapply exec_step with (l := []) (tr := []); [exact memory_store_step|].
    eapply exec_step with (l := []) (tr := []); [exact memory_load_step|].
    eapply exec_step with (l := []) (tr := []); [exact memory_free_step|constructor].
  - reflexivity.
Qed.

Example direct_call_full_graph :
  Graph.out (cfg (ssa_full_view no_ext return_program test_limits)) (0, 0, 0) =
    [FullEdge (0, 0, 0) (1, 0, 0) 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example return_to_caller_full_graph :
  In (FullEdge (1, 0, 0) (0, 1, 0) 0)
    (Graph.out (cfg (ssa_full_view no_ext return_program test_limits)) (1, 0, 0)).
Proof.
  vm_compute; tauto.
Qed.

Example main_return_endpoint :
  In (FullEdge (0, 1, 0) (0, 1, 1) 0)
    (Graph.out (cfg (ssa_full_view no_ext return_program test_limits)) (0, 1, 0)).
Proof.
  vm_compute; tauto.
Qed.

Example direct_call_step_and_edge :
  step_s no_ext return_program test_limits calling_state [] called_state /\
  taken (ssa_full_view no_ext return_program test_limits) calling_state [] called_state
    (FullEdge (0, 0, 0) (1, 0, 0) 0).
Proof.
  split.
  - apply SCall with (c := CDirect 1) (args := [0]) (cs := [VInt W32 42%Z])
      (fd := FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)
      (b := SBlock [(2, TyI32)] [] (TRet 2)).
    + exists (FDef 0
        [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
         (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
        (SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
        vm_compute; repeat split; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn; lia.
  - split; [vm_compute; tauto|]; split; [reflexivity|].
    right; exists (TCall (CDirect 1) [0] 1); split; [|reflexivity].
    exists (FDef 0
      [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
       (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
      (SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
      vm_compute; repeat split; reflexivity.
Qed.

Example return_step_and_edge :
  step_s no_ext return_program test_limits called_state [] returned_state /\
  taken (ssa_full_view no_ext return_program test_limits) called_state [] returned_state
    (FullEdge (1, 0, 0) (0, 1, 0) 0).
Proof.
  split.
  - apply SReturn with (x := 2) (v := VInt W32 42%Z).
    + exists (FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
        (SBlock [(2, TyI32)] [] (TRet 2)); vm_compute; repeat split; reflexivity.
    + reflexivity.
    + reflexivity.
  - split; [vm_compute; tauto|]; split; [reflexivity|].
    right; exists (TRet 2); split; [|reflexivity].
    exists (FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
      (SBlock [(2, TyI32)] [] (TRet 2)); vm_compute; repeat split; reflexivity.
Qed.

Example main_return_event_and_edge :
  let final := State [SFrame 0 1 1 (env_set caller_env 1 (VInt W32 42%Z)) 1]
    (fun _ => None) 0 in
  step_s no_ext return_program test_limits returned_state [EvRet (VInt W32 42%Z)] final /\
  taken (ssa_full_view no_ext return_program test_limits) returned_state
    [EvRet (VInt W32 42%Z)] final (FullEdge (0, 1, 0) (0, 1, 1) 0).
Proof.
  split.
  - apply SReturnMain with (x := 1).
    + exists (FDef 0
        [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
         (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
        (SBlock [(1, TyI32)] [] (TRet 1)); vm_compute; repeat split; reflexivity.
    + reflexivity.
  - split; [vm_compute; tauto|]; split; [reflexivity|].
    right; exists (TRet 1); split; [|reflexivity].
    exists (FDef 0
      [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
       (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
      (SBlock [(1, TyI32)] [] (TRet 1)); vm_compute; repeat split; reflexivity.
Qed.

Definition parallel_memory_graph_program : program :=
  Program [(0, FDef 0
    [(0, SBlock [(0, TyI32)] [] (TBr 0 1 [0] 1 [0]));
     (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32)] 0 [].

Example parallel_graph_fixture_accepted : wf_check parallel_memory_graph_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example parallel_slots_remain_distinct :
  Graph.out (cfg (ssa_full_view no_ext parallel_memory_graph_program test_limits)) (0, 0, 0) =
  [FullEdge (0, 0, 0) (0, 1, 0) 0; FullEdge (0, 0, 0) (0, 1, 0) 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example switch_slots_include_default :
  Graph.out (cfg (ssa_full_view no_ext switch_program test_limits)) (0, 0, 0) =
  [FullEdge (0, 0, 0) (0, 1, 0) 0; FullEdge (0, 0, 0) (0, 2, 0) 1;
   FullEdge (0, 0, 0) (0, 2, 0) 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example indirect_calls_cross_function_boundaries :
  In (FullEdge (0, 0, 5) (1, 0, 0) 0)
    (Graph.out (cfg (ssa_full_view no_ext memory_calls test_limits)) (0, 0, 5)).
Proof.
  vm_compute; tauto.
Qed.

Example no_stationary_steps :
  ~ stays (ssa_full_view no_ext memory_calls test_limits) test_loaded [] test_freed.
Proof.
  exact (fun Hfalse => Hfalse).
Qed.

Example memory_lookup_keeps_first_function :
  let first := FDef 0 [(0, SBlock [] [IAlloc 0 1] (TRet 0))] TyPtr in
  let second := FDef 1 [(1, SBlock [] [IFree 2] (TRet 2))] TyI32 in
  let duplicated := Program [(0, first); (0, second)] 0 [] in
  let view := ssa_mem_view no_ext duplicated test_limits in
  map (fun l => mem_instr view
    (State [SFrame 0 l 0 (fun _ => None) 0] (fun _ => None) 0)) [0; 1] =
    [Some (MemAlloc 0 1); None].
Proof.
  vm_compute; reflexivity.
Qed.

Example memory_lookup_keeps_first_block :
  let first := SBlock [] [IAlloc 0 1] (TRet 0) in
  let second := SBlock [] [IFree 2] (TRet 2) in
  let duplicated := Program [(0, FDef 0 [(0, first); (0, second)] TyPtr)] 0 [] in
  mem_instr (ssa_mem_view no_ext duplicated test_limits)
    (State [SFrame 0 0 0 (fun _ => None) 0] (fun _ => None) 0) = Some (MemAlloc 0 1).
Proof.
  vm_compute; reflexivity.
Qed.
