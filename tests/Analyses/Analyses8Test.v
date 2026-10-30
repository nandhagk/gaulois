(** * Call analysis computations and contract diagnostics

    Small call graphs exercise target fallback, bounded contexts and real recursive frames.
    For example, two pushes produce the active chain [0; 1; 0].
    Builds on: AnalysesCalls and ExamplesSsaCalls. *)

From Stdlib Require Import List Bool Arith Lia ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDag.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesCalls.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaEffects ExamplesSsaCalls.
Import List.ListNotations.
Local Open Scope nat_scope.

Example calls_direct_precedence :
  resolver (fun _ : nat => Some 2) (fun _ => Some 3) (fun _ => false)
    (fun _ => Some [4; 5]) [0; 1; 2] 10 = [2].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_indirect_fact :
  resolver (fun _ : nat => None) (fun _ => Some 3) (fun _ => false)
    (fun _ => Some [4; 5]) [0; 1; 2] 10 = [4; 5].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_unresolved_indirect :
  resolver (fun _ : nat => None) (fun _ => Some 3) (fun _ => false)
    (fun _ => @None (list nat)) [0; 1; 2] 10 = [0; 1; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_missing_value_fallback :
  resolver (fun _ : nat => None) (fun _ => @None nat) (fun _ => false)
    (fun _ => Some [4; 5]) [0; 1; 2] 10 = [0; 1; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_bounded_context : push_ctx 2 13 [12; 11; 10] = [13; 12].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_zero_context : push_ctx 0 13 [12; 11] = [].
Proof.
  vm_compute; reflexivity.
Qed.

Inductive calls_stage : Type :=
  | Outer
  | Inner
  | Repeated.

Definition calls_test_semantics : semantics calls_stage unit :=
  Semantics (fun s => s = Outer) (fun s l s' =>
    match s, s' with
    | Outer, Inner => l = []
    | Inner, Repeated => l = []
    | _, _ => False
    end).

Definition calls_test_view : calls_view calls_stage nat nat :=
  CallsView [0; 1] [0]
    (fun f => match f with 0 => [10] | 1 => [11] | _ => [] end)
    (fun p => if Nat.eqb p 10 then 0 else 1)
    (fun s => match s with Inner => 1 | _ => 0 end)
    (fun s => match s with
      | Outer => []
      | Inner => [(0, 10)]
      | Repeated => [(1, 11); (0, 10)]
      end).

Definition calls_test_resolve (p : nat) : list nat :=
  if Nat.eqb p 10 then [1] else [0].

Lemma calls_test_laws : calls_view_laws calls_test_semantics calls_test_view calls_test_resolve.
Proof.
  constructor.
  - intros [|[|f]] p Hsite; cbn in Hsite; try contradiction;
      destruct Hsite as [<-|Hfalse]; [reflexivity|contradiction|reflexivity|contradiction].
  - intros s Hinitial; cbn in Hinitial; subst s; split; [left; reflexivity|reflexivity].
  - intros s _ f Hin; destruct s; cbn in Hin |- *; intuition congruence.
  - intros s l s' _ Hstep; destruct s, s'; cbn in Hstep; try contradiction.
    + right; left; exists 10; cbn; intuition.
    + right; left; exists 11; cbn; intuition.
Qed.

Lemma calls_test_reachable : reachable_state calls_test_semantics Repeated.
Proof.
  exists Outer, []; split; [reflexivity|].
  change (exec calls_test_semantics Outer ([] ++ []) Repeated).
  eapply exec_step with (s' := Inner); [reflexivity|].
  change (exec calls_test_semantics Inner ([] ++ []) Repeated).
  eapply exec_step with (s' := Repeated); [reflexivity|constructor].
Qed.

Example calls_actual_recursive_chain : active calls_test_view Repeated = [0; 1; 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_recursive_cycle :
  exists f, In f (active calls_test_view Repeated) /\
    recursive (call_graph calls_test_view calls_test_resolve) f.
Proof.
  apply (recursive_sound nat_encoding calls_test_semantics calls_test_view
    calls_test_resolve Repeated calls_test_laws calls_test_reachable).
  intro Hnd; inversion Hnd as [|x xs Hnot Htail]; apply Hnot; cbn; right; left; reflexivity.
Qed.

Example calls_leaf : callee_leaf calls_test_view 2 = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_recursive_contexts :
  ctx_of calls_test_view 1 Repeated 0 = [11] /\
  ctx_of calls_test_view 1 Repeated 1 = [10] /\
  ctx_of calls_test_view 1 Repeated 2 = [].
Proof.
  vm_compute; auto.
Qed.

Example calls_caller_buckets :
  callers_of nat_encoding (callers_index nat_encoding calls_test_view calls_test_resolve) 0 = [11]
  /\ callers_of nat_encoding
    (callers_index nat_encoding calls_test_view calls_test_resolve) 1 = [10]
  /\ callers_of nat_encoding (callers_index nat_encoding calls_test_view calls_test_resolve) 2 = [].
Proof.
  vm_compute; auto.
Qed.

Definition calls_test_args : args_view calls_stage nat nat nat nat :=
  ArgsView (fun p => [p; 100]) (fun f => [f]) (fun _ x => Some x).

Example calls_argument_join :
  arg_fact nat_encoding calls_test_args
    (callers_index nat_encoding calls_test_view calls_test_resolve) bool_lattice
    (fun x => Nat.eqb x 10) 1 0 = true /\
  arg_fact nat_encoding calls_test_args
    (callers_index nat_encoding calls_test_view calls_test_resolve) bool_lattice
    (fun x => Nat.eqb x 10) 0 0 = false.
Proof.
  vm_compute; auto.
Qed.

(** The current call laws permit conservative targets outside the finite function inventory. *)
Definition calls_open_view : calls_view unit nat nat :=
  CallsView [0] [0] (fun f => [f]) (fun p => p) (fun _ => 0) (fun _ => []).

Definition calls_open_semantics : semantics unit unit :=
  Semantics (fun _ => True) (fun _ _ _ => False).

Lemma calls_open_laws :
  calls_view_laws calls_open_semantics calls_open_view (fun _ => [1]).
Proof.
  constructor.
  - intros f p [Heq|Hfalse]; [symmetry; exact Heq|contradiction].
  - intros s _; split; [left; reflexivity|reflexivity].
  - intros s _ f [Heq|Hfalse]; [left; exact Heq|contradiction].
  - intros s l s' _ Hfalse; exact (False_rect _ Hfalse).
Qed.

Example calls_open_graph_not_well_formed :
  ~ graph_wf (call_graph calls_open_view (fun _ => [1])).
Proof.
  intro Hwf.
  pose proof (out_target_in Hwf 0 (CallEdge 0 1) ltac:(left; reflexivity)
    ltac:(left; reflexivity)) as Hlisted.
  cbn in Hlisted; destruct Hlisted as [Hbad|Hfalse]; [discriminate|contradiction].
Qed.

Example calls_open_graph_reachable_cycle :
  reachable (call_graph calls_open_view (fun _ => [1])) 1 /\
  path (call_graph calls_open_view (fun _ => [1])) 1 [CallEdge 1 1] 1.
Proof.
  split.
  - apply (reachable_step (g := call_graph calls_open_view (fun _ => [1])) (CallEdge 0 1)).
    + apply reachable_entry; left; reflexivity.
    + left; reflexivity.
  - apply (path_cons (g := call_graph calls_open_view (fun _ => [1])) (CallEdge 1 1) [] 1).
    + left; reflexivity.
    + constructor.
Qed.

Example calls_open_preparation_misses_cycle :
  exists r, max_paths (prepare nat_encoding (call_graph calls_open_view (fun _ => [1])))
    (fun _ => 1%Z) = Some r.
Proof.
  vm_compute; eexists; reflexivity.
Qed.

(** A weighted diamond has duplicate targets, parallel sites, and a separate zero-weight cycle. *)
Definition calls_weighted_view : calls_view unit nat nat :=
  CallsView [0; 1; 2; 3; 4] [0]
    (fun f => match f with 0 => [0; 1] | 1 => [2] | 2 => [3] | 4 => [4] | _ => [] end)
    (fun p => match p with 0 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 4 end)
    (fun _ => 0) (fun _ => []).

Definition calls_weighted_resolve (p : nat) : list nat :=
  match p with
  | 0 | 1 => [1; 1; 2]
  | 2 | 3 => [3]
  | 4 => [4]
  | _ => []
  end.

Definition calls_weighted_graph := call_graph calls_weighted_view calls_weighted_resolve.

Definition calls_test_weights : frame_weights nat :=
  FrameWeights (fun f => match f with 0 => 2 | 1 => 3 | 2 => 9 | 3 => 5 | _ => 0 end).

Example calls_weighted_graph_wf : graph_wf calls_weighted_graph.
Proof.
  apply call_graph_wf.
  - repeat constructor; cbn; intuition congruence.
  - intros f [<-|[]]; left; reflexivity.
  - intros [|[|[|[|[|f]]]]] p Hin; cbn in Hin; intuition subst; cbn; tauto.
  - intros [|[|[|[|[|p]]]]] g Hin; cbn in Hin; intuition subst; cbn; tauto.
Qed.

Example calls_duplicate_parallel_targets_deduplicated :
  length (Graph.out (calls_finite_graph nat_encoding calls_weighted_graph 0) 0) = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_weighted_branching_maximum :
  stack_demand nat_encoding calls_weighted_view calls_weighted_graph calls_test_weights 0 = Some 16.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_query_rerooted :
  stack_demand nat_encoding calls_weighted_view calls_weighted_graph calls_test_weights 1 = Some 8.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_zero_weight_reachable_cycle :
  stack_demand nat_encoding calls_weighted_view calls_weighted_graph calls_test_weights 4 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_zero_weight_unrelated_cycle :
  stack_demand nat_encoding calls_weighted_view calls_weighted_graph
    (FrameWeights (fun _ => 0)) 0 = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_empty_path_includes_start :
  stack_demand nat_encoding calls_weighted_view calls_weighted_graph calls_test_weights 3 = Some 5.
Proof.
  vm_compute; reflexivity.
Qed.

Example calls_raw_maximum_attained :
  path calls_weighted_graph 0 [CallEdge 0 2; CallEdge 3 3] 3 /\
  weight calls_test_weights 0 + calls_path_weight calls_weighted_graph calls_test_weights
    [CallEdge 0 2; CallEdge 3 3] = 16.
Proof.
  split.
  - apply (path_cons (g := calls_weighted_graph) (CallEdge 0 2) [CallEdge 3 3] 3).
    + cbn; auto.
    + apply (path_cons (g := calls_weighted_graph) (CallEdge 3 3) [] 3);
        [left; reflexivity|constructor].
  - vm_compute; reflexivity.
Qed.

Example calls_exact_bound_on_all_raw_paths :
  forall es v, path calls_weighted_graph 0 es v ->
    weight calls_test_weights 0 +
      calls_path_weight calls_weighted_graph calls_test_weights es <= 16.
Proof.
  exact (proj1 (proj2 (stack_demand_exact nat_encoding calls_weighted_view calls_weighted_graph
    calls_test_weights 0 calls_weighted_graph_wf (or_introl eq_refl))
    16 calls_weighted_branching_maximum)).
Qed.

Example calls_actual_recursive_demand :
  stack_demand nat_encoding calls_test_view (call_graph calls_test_view calls_test_resolve)
    calls_test_weights 0 = None /\
  stack_above nat_encoding calls_test_view calls_test_weights 0 Repeated = 2 /\
  stack_above nat_encoding calls_test_view calls_test_weights 1 Repeated = 5 /\
  stack_above nat_encoding calls_test_view calls_test_weights 2 Repeated = 7.
Proof.
  vm_compute; auto.
Qed.

Definition calls_pure_effects : effects_view calls_stage unit nat :=
  EffectsView (fun _ => None) (fun _ => 0) (fun _ _ => True) (fun _ => 0).

Lemma calls_purity_laws :
  summary_laws calls_test_semantics calls_test_view (purity_spec calls_test_view (fun _ => false))
    (purity_cover calls_pure_effects).
Proof.
  constructor.
  - intros a b s l s' Hle Hcover Hfalse; subst b; destruct a;
      [discriminate|apply Hcover; reflexivity].
  - intros s l s' _ Hstep _; split; [|reflexivity].
    destruct s, s'; cbn in Hstep; contradiction || exact Hstep.
  - intros p g a s l s' _ _ Hcover; exact Hcover.
Qed.

Example calls_purity_nontrivial_post_solution :
  post_solution bool_lattice
    (summary_system calls_test_view calls_test_resolve
      (purity_spec calls_test_view (fun _ => false))) (fun _ => false).
Proof.
  intros [f|p g] _; split; [reflexivity|intros x a Hin; contradiction|
    reflexivity|intros x a Hin; contradiction].
Qed.

Example calls_purity_actual_callee_step :
  forall l, step calls_test_semantics Inner l Repeated ->
    l = [] /\ heap calls_pure_effects Repeated = heap calls_pure_effects Inner.
Proof.
  intros l Hstep.
  eapply (purity_sound calls_test_semantics calls_test_view calls_test_resolve calls_pure_effects
    (fun _ => false) (fun _ => false) calls_test_laws calls_purity_laws
    calls_purity_nontrivial_post_solution Inner l Repeated 0).
  - exists Outer, []; split; [reflexivity|].
    change (exec calls_test_semantics Outer ([] ++ []) Inner).
    eapply exec_step with (s' := Inner); [reflexivity|constructor].
  - exact Hstep.
  - right; left; reflexivity.
  - reflexivity.
Qed.

Example calls_contextual_post_solution :
  post_solution bool_lattice
    (callstring_system 2 calls_test_view calls_test_resolve
      (purity_spec calls_test_view (fun _ => false))) (fun _ => false).
Proof.
  intros [[f|p g] c] _; split; [reflexivity|intros x a Hin; contradiction|
    reflexivity|intros x a Hin; contradiction].
Qed.

Example calls_contextual_actual_callee_step :
  forall l, step calls_test_semantics Inner l Repeated ->
    step_covers (purity_cover calls_pure_effects)
      ((fun _ => false) (0, ctx_of calls_test_view 2 Inner 1)) Inner l Repeated.
Proof.
  intros l Hstep.
  eapply (callstring_sound calls_test_semantics 2 calls_test_view calls_test_resolve
    (purity_spec calls_test_view (fun _ => false)) (purity_cover calls_pure_effects)
    (fun _ => false) calls_test_laws calls_purity_laws calls_contextual_post_solution
    Inner l Repeated 1 0).
  - exists Outer, []; split; [reflexivity|].
    change (exec calls_test_semantics Outer ([] ++ []) Inner).
    eapply exec_step with (s' := Inner); [reflexivity|constructor].
  - exact Hstep.
  - reflexivity.
Qed.

Example calls_ssa_direct_wf : wf_program no_ext return_program.
Proof.
  apply wf_check_sound.
  - apply ext_respects_nil; reflexivity.
  - vm_compute; reflexivity.
Qed.

Example calls_ssa_direct_initial :
  initial (ssa_semantics no_ext return_program (Limits 8 8)) calling_state.
Proof.
  exists (FDef 0 [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
    (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
    (SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1)), [VInt W32 42%Z], caller_env.
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor].
Qed.

Example calls_ssa_direct_push :
  step (ssa_semantics no_ext return_program (Limits 8 8)) calling_state [] called_state.
Proof.
  unfold calling_state, called_state.
  apply SCall with (c := CDirect 1) (args := [0]) (cs := [VInt W32 42%Z])
    (fd := FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32)
    (b := SBlock [(2, TyI32)] [] (TRet 2)).
  - exists (FDef 0 [(0, SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1));
      (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32),
      (SBlock [(0, TyI32)] [] (TCall (CDirect 1) [0] 1)); repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example calls_ssa_direct_reachable :
  reachable_state (ssa_semantics no_ext return_program (Limits 8 8)) called_state.
Proof.
  exists calling_state, []; split; [exact calls_ssa_direct_initial|].
  change (exec (ssa_semantics no_ext return_program (Limits 8 8))
    calling_state ([] ++ []) called_state).
  eapply exec_step with (s' := called_state); [exact calls_ssa_direct_push|constructor].
Qed.

Example calls_ssa_direct_demand :
  ssa_resolver return_program (0, 0) = [1] /\
  stack_demand nat_encoding (ssa_calls no_ext return_program)
    (call_graph (ssa_calls no_ext return_program) (ssa_resolver return_program))
    calls_test_weights 0 = Some 5 /\
  stack_above nat_encoding (ssa_calls no_ext return_program) calls_test_weights 0 called_state = 5.
Proof.
  vm_compute; auto.
Qed.

Example calls_ssa_direct_stack_bound :
  stack_above nat_encoding (ssa_calls no_ext return_program) calls_test_weights 0 called_state <= 5.
Proof.
  apply (ssa_stack_demand_sound no_ext return_program (Limits 8 8) calls_test_weights 0 5).
  - exact calls_ssa_direct_wf.
  - exact (proj1 (proj2 calls_ssa_direct_demand)).
  - exact calls_ssa_direct_reachable.
  - right; left; reflexivity.
Qed.

Example calls_ssa_leaf_returns :
  step (ssa_semantics no_ext return_program (Limits 8 8)) called_state [] returned_state.
Proof.
  unfold called_state, returned_state.
  apply SReturn with (x := 2) (v := VInt W32 42%Z).
  - exists (FDef 0 [(0, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
      (SBlock [(2, TyI32)] [] (TRet 2)); repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example calls_ssa_actual_leaf_shape :
  frames (ssa_calls no_ext return_program) returned_state =
    frames (ssa_calls no_ext return_program) called_state \/
  exists g p, frames (ssa_calls no_ext return_program) called_state =
    (g, p) :: frames (ssa_calls no_ext return_program) returned_state.
Proof.
  exact (ssa_callee_leaf_sound no_ext return_program (Limits 8 8) 1 calls_ssa_direct_wf
    eq_refl called_state [] returned_state calls_ssa_direct_reachable eq_refl
    calls_ssa_leaf_returns).
Qed.

Example calls_ssa_unreachable_excluded :
  ~ In 99 (active (ssa_calls no_ext return_program) called_state).
Proof.
  apply (ssa_unreachable_sound no_ext return_program (Limits 8 8) 99 calls_ssa_direct_wf).
  - intro Hreach.
    pose proof (reachable_in_nodes _ _
      (calls_ssa_graph_wf no_ext return_program (Limits 8 8) calls_ssa_direct_wf) Hreach) as Hin.
    cbn in Hin; intuition congruence.
  - exact calls_ssa_direct_reachable.
Qed.

(** Main receives a function pointer and an integer; its only compatible target is a leaf. *)
Definition calls_ssa_indirect_program : program := Program
  [(0, FDef 0
    [(0, SBlock [(0, TyFun); (1, TyI32)] [] (TCall (CIndirect 0 [TyI32] TyI32) [1] 1));
     (1, SBlock [(2, TyI32)] [] (TRet 2))] TyI32);
   (1, FDef 0 [(0, SBlock [(3, TyI32)] [] (TRet 3))] TyI32)] 0 [].

Definition calls_ssa_indirect_env : vid -> option cval :=
  env_set (env_set (fun _ => None) 0 (VFun 1)) 1 (VInt W32 7%Z).

Definition calls_ssa_indirect_start : state :=
  State [SFrame 0 0 0 calls_ssa_indirect_env 0] (fun _ => None) 0.

Definition calls_ssa_indirect_called : state :=
  State [SFrame 1 0 0 (env_set (fun _ => None) 3 (VInt W32 7%Z)) 0;
    SFrame 0 0 0 calls_ssa_indirect_env 1] (fun _ => None) 0.

Example calls_ssa_indirect_wf : wf_program no_ext calls_ssa_indirect_program.
Proof.
  apply wf_check_sound.
  - apply ext_respects_nil; reflexivity.
  - vm_compute; reflexivity.
Qed.

Example calls_ssa_indirect_initial :
  initial (ssa_semantics no_ext calls_ssa_indirect_program (Limits 8 8)) calls_ssa_indirect_start.
Proof.
  exists (FDef 0
    [(0, SBlock [(0, TyFun); (1, TyI32)] [] (TCall (CIndirect 0 [TyI32] TyI32) [1] 1));
     (1, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
    (SBlock [(0, TyFun); (1, TyI32)] [] (TCall (CIndirect 0 [TyI32] TyI32) [1] 1)),
    [VFun 1; VInt W32 7%Z], calls_ssa_indirect_env.
  repeat split; try reflexivity.
  constructor; [exact I|constructor; [cbn [valid_cval]; lia|constructor]].
Qed.

Example calls_ssa_indirect_push :
  step (ssa_semantics no_ext calls_ssa_indirect_program (Limits 8 8))
    calls_ssa_indirect_start [] calls_ssa_indirect_called.
Proof.
  unfold calls_ssa_indirect_start, calls_ssa_indirect_called.
  apply SCall with (c := CIndirect 0 [TyI32] TyI32) (args := [1]) (cs := [VInt W32 7%Z])
    (fd := FDef 0 [(0, SBlock [(3, TyI32)] [] (TRet 3))] TyI32)
    (b := SBlock [(3, TyI32)] [] (TRet 3)).
  - exists (FDef 0
      [(0, SBlock [(0, TyFun); (1, TyI32)] [] (TCall (CIndirect 0 [TyI32] TyI32) [1] 1));
       (1, SBlock [(2, TyI32)] [] (TRet 2))] TyI32),
      (SBlock [(0, TyFun); (1, TyI32)] [] (TCall (CIndirect 0 [TyI32] TyI32) [1] 1));
      repeat split; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn; lia.
Qed.

Example calls_ssa_indirect_reachable :
  reachable_state (ssa_semantics no_ext calls_ssa_indirect_program (Limits 8 8))
    calls_ssa_indirect_called.
Proof.
  exists calls_ssa_indirect_start, []; split; [exact calls_ssa_indirect_initial|].
  change (exec (ssa_semantics no_ext calls_ssa_indirect_program (Limits 8 8))
    calls_ssa_indirect_start ([] ++ []) calls_ssa_indirect_called).
  eapply exec_step with (s' := calls_ssa_indirect_called);
    [exact calls_ssa_indirect_push|constructor].
Qed.

Example calls_ssa_indirect_demand :
  ssa_resolver calls_ssa_indirect_program (0, 0) = [1] /\
  stack_demand nat_encoding (ssa_calls no_ext calls_ssa_indirect_program)
    (call_graph (ssa_calls no_ext calls_ssa_indirect_program)
      (ssa_resolver calls_ssa_indirect_program)) calls_test_weights 0 = Some 5 /\
  stack_above nat_encoding (ssa_calls no_ext calls_ssa_indirect_program)
    calls_test_weights 0 calls_ssa_indirect_called = 5.
Proof.
  vm_compute; auto.
Qed.

Example calls_ssa_indirect_stack_bound :
  stack_above nat_encoding (ssa_calls no_ext calls_ssa_indirect_program)
    calls_test_weights 0 calls_ssa_indirect_called <= 5.
Proof.
  apply (ssa_stack_demand_sound no_ext calls_ssa_indirect_program (Limits 8 8)
    calls_test_weights 0 5).
  - exact calls_ssa_indirect_wf.
  - exact (proj1 (proj2 calls_ssa_indirect_demand)).
  - exact calls_ssa_indirect_reachable.
  - right; left; reflexivity.
Qed.
