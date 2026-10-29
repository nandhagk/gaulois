(** * Strict SSA and activation-history regression cases

    These examples instantiate complete laws on checked source programs and retain frame events.
    For example, a caller's output remains in its history while two nested callees emit outputs.
    Builds on: ExamplesSsaStrict, ExamplesSsaAnalyses and ExamplesSsaViewsTest. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Graph Require Import GraphCore GraphDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints ViewsDominated.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaActivation
  ExamplesSsaViews ExamplesSsaAnalyses ExamplesSsaStrict.
From Gaulois.Tests.Examples Require Import ExamplesSsaViewsTest.
Import List.ListNotations.
Local Open Scope nat_scope.

Local Lemma strict_checked P : ext_sigs P = [] -> wf_check P = true -> wf_program no_ext P.
Proof.
  intros Hextensions Hchecked; apply wf_check_sound;
    [apply ext_respects_nil; exact Hextensions|exact Hchecked].
Qed.

(** Complete raw and refined laws hold for a loop with carried phi parameters. *)
Example strict_factorial_laws :
  strict_ssa_laws (activation no_ext factorial_ssa 0) (ssa_block_view no_ext factorial_ssa 0) /\
  reachable_point_ssa (ssa_refined_points factorial_ssa 0).
Proof.
  assert (Hwf : wf_program no_ext factorial_ssa) by
    (apply strict_checked; [reflexivity|exact factorial_wf]).
  split; [apply ssa_strict_laws|apply (ssa_refined_reachable_strict no_ext)];
    [exact Hwf|left; reflexivity|exact Hwf|left; reflexivity].
Qed.

(** The full laws also allow incoming edges to entry and simultaneous swapping there. *)
Example strict_entry_self_loop_laws :
  wf_check parallel_loop = true /\
  strict_ssa_laws (activation no_ext parallel_loop 0) (ssa_block_view no_ext parallel_loop 0) /\
  reachable_point_ssa (ssa_refined_points parallel_loop 0) /\
  Graph.out (ssa_refined_graph parallel_loop 0) (SsaExecPoint 0 0) = [SsaTransfer 0 0 0].
Proof.
  assert (Hchecked : wf_check parallel_loop = true) by (vm_compute; reflexivity).
  split; [exact Hchecked|].
  assert (Hwf : wf_program no_ext parallel_loop) by
    (apply strict_checked; [reflexivity|exact Hchecked]).
  split; [apply ssa_strict_laws; [exact Hwf|left; reflexivity]|].
  split; [apply (ssa_refined_reachable_strict no_ext); [exact Hwf|left; reflexivity]|].
  vm_compute; reflexivity.
Qed.

(** An empty-body source block and an unreachable memory component retain complete strict laws. *)
Example strict_parallel_unreachable_laws :
  strict_ssa_laws (activation no_ext ssa_parallel_program 0)
    (ssa_block_view no_ext ssa_parallel_program 0) /\
  reachable_point_ssa (ssa_refined_points ssa_parallel_program 0).
Proof.
  assert (Hwf : wf_program no_ext ssa_parallel_program) by
    (apply strict_checked; [reflexivity|exact (proj1 ssa_parallel_and_call_checked)]).
  split; [apply ssa_strict_laws|apply (ssa_refined_reachable_strict no_ext)];
    [exact Hwf|left; reflexivity|exact Hwf|left; reflexivity].
Qed.

(** Every reachable first-instruction use is strictly dominated by the entry parameter edge. *)
Example strict_first_instruction_use :
  reachable_point_ssa (ssa_refined_points ssa_duplicate_program 0) /\
  strictly_dominates (ssa_refined_graph ssa_duplicate_program 0)
    (SsaBeforeParams 0) (SsaExecPoint 0 0).
Proof.
  pose proof (ssa_refined_reachable_strict no_ext ssa_duplicate_program 0
    (strict_checked ssa_duplicate_program eq_refl ssa_duplicate_operands_checked)
    (or_introl eq_refl)) as Hlaws.
  split; [exact Hlaws|].
  assert (Hreach : reachable (ssa_refined_graph ssa_duplicate_program 0) (SsaExecPoint 0 0)).
  { apply (reachable_step (g := ssa_refined_graph ssa_duplicate_program 0) (SsaBindParams 0)).
    - apply reachable_entry; vm_compute; left; reflexivity.
    - vm_compute; left; reflexivity. }
  destruct (point_ssa_uses_defined Hlaws (SsaExecPoint 0 0) (SsaSourceValue 0) Hreach)
    as [d [Hdefinition [Hdefined Hdominates]]].
  - right; exists (SsaInstruction 0 0); split; vm_compute; tauto.
  - vm_compute in Hdefinition; injection Hdefinition as <-; exact Hdominates.
Qed.

(** Loop-carried parameters precede first uses, and incoming reads remain on projected edges. *)
Example strict_loop_phi_layout :
  point_definition (ssa_refined_points factorial_ssa 0) (SsaSourceValue 3) =
    Some (SsaBeforeParams 1) /\
  edge_use (point_model (ssa_refined_points factorial_ssa 0)) (SsaInstruction 1 0) =
    [SsaSourceValue 3; SsaSourceValue 4] /\
  edge_use (point_model (ssa_refined_points factorial_ssa 0)) (SsaTransfer 1 1 0) =
    [SsaSourceValue 11; SsaSourceValue 6; SsaSourceValue 9; SsaSourceValue 8] /\
  edge_def (point_model (ssa_refined_points factorial_ssa 0)) (SsaTransfer 1 1 0) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The complete strict model selects the call-result definition before its projected use. *)
Example strict_call_result_use :
  reachable_point_ssa (ssa_refined_points ssa_call_program 0) /\
  strictly_dominates (ssa_refined_graph ssa_call_program 0)
    (SsaExecPoint 0 0) (SsaCallReady 0).
Proof.
  pose proof (ssa_refined_reachable_strict no_ext ssa_call_program 0
    (strict_checked ssa_call_program eq_refl (proj2 ssa_parallel_and_call_checked))
    (or_introl eq_refl)) as Hlaws.
  split; [exact Hlaws|].
  assert (Hreach : reachable (ssa_refined_graph ssa_call_program 0) (SsaCallReady 0)).
  { apply (reachable_step (g := ssa_refined_graph ssa_call_program 0) (SsaMakeCallResult 0)).
    - apply (reachable_step (g := ssa_refined_graph ssa_call_program 0) (SsaBindParams 0)).
      + apply reachable_entry; vm_compute; left; reflexivity.
      + vm_compute; left; reflexivity.
    - vm_compute; left; reflexivity. }
  destruct (point_ssa_uses_defined Hlaws (SsaCallReady 0) (SsaCallResult 0) Hreach)
    as [d [Hdefinition [Hdefined Hdominates]]].
  - right; exists (SsaTransfer 0 1 0); split; vm_compute; tauto.
  - vm_compute in Hdefinition; injection Hdefinition as <-; exact Hdominates.
Qed.

(** The common parameter edge kills its source values on every outgoing occurrence. *)
Example strict_common_parameter_kill :
  let s := ssa_refined_points ssa_parallel_program 0 in
  forall e, In e (Graph.out (live_graph (point_model s)) (SsaBeforeParams 1)) ->
    In (SsaSourceValue 3) (edge_def (point_model s) e).
Proof.
  cbn zeta; intros e Hout; vm_compute in Hout.
  destruct Hout as [<-|Hfalse]; [vm_compute; left; reflexivity|contradiction].
Qed.

(** Empty stacks and out-of-range frame positions have no activation. *)
Example strict_empty_frames :
  frame_activation parallel_loop (State [] (fun _ => None) 0) 0 = None /\
  subtrace ([] : list event) [EvOut (VInt W32 7)].
Proof.
  split; [reflexivity|apply sub_nil].
Qed.

(** * Nested calls with observable local steps *)

Definition strict_nested_main : fdef := FDef 0
  [(0, SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1));
   (1, SBlock [(1, TyI32)] [] (TRet 1))] TyI32.

Definition strict_nested_middle : fdef := FDef 0
  [(0, SBlock [(2, TyI32)] [IOutput 2] (TCall (CDirect 2) [2] 1));
   (1, SBlock [(3, TyI32)] [] (TRet 3))] TyI32.

Definition strict_nested_leaf : fdef := FDef 0
  [(0, SBlock [(4, TyI32)] [IOutput 4] (TRet 4))] TyI32.

Definition strict_nested : program := Program
  [(0, strict_nested_main); (1, strict_nested_middle); (2, strict_nested_leaf)] 0 [].

Definition strict_value : cval := VInt W32 7.
Definition strict_env (x : vid) : vid -> option cval := env_set (fun _ => None) x strict_value.
Definition strict_memory : nat -> option mblock := fun _ => None.
Definition strict_limits : limits := Limits 4 0.

Definition strict_start : state := State [SFrame 0 0 0 (strict_env 0) 0] strict_memory 0.
Definition strict_main_out : state := State [SFrame 0 0 1 (strict_env 0) 0] strict_memory 0.
Definition strict_middle_start : state := State
  [SFrame 1 0 0 (strict_env 2) 0; SFrame 0 0 1 (strict_env 0) 1] strict_memory 0.
Definition strict_middle_out : state := State
  [SFrame 1 0 1 (strict_env 2) 0; SFrame 0 0 1 (strict_env 0) 1] strict_memory 0.
Definition strict_leaf_start : state := State
  [SFrame 2 0 0 (strict_env 4) 0; SFrame 1 0 1 (strict_env 2) 1;
   SFrame 0 0 1 (strict_env 0) 1] strict_memory 0.
Definition strict_leaf_out : state := State
  [SFrame 2 0 1 (strict_env 4) 0; SFrame 1 0 1 (strict_env 2) 1;
   SFrame 0 0 1 (strict_env 0) 1] strict_memory 0.
Definition strict_middle_returned : state := State
  [SFrame 1 1 0 (env_set (strict_env 2) 3 strict_value) 1;
   SFrame 0 0 1 (strict_env 0) 1] strict_memory 0.
Definition strict_main_returned : state := State
  [SFrame 0 1 0 (env_set (strict_env 0) 1 strict_value) 1] strict_memory 0.

(** The nested program passes the actual source checker and has complete strict laws. *)
Example strict_nested_checked :
  wf_check strict_nested = true /\
  strict_ssa_laws (activation no_ext strict_nested 0) (ssa_block_view no_ext strict_nested 0) /\
  reachable_point_ssa (ssa_refined_points strict_nested 0).
Proof.
  assert (Hchecked : wf_check strict_nested = true) by (vm_compute; reflexivity).
  split; [exact Hchecked|].
  assert (Hwf : wf_program no_ext strict_nested) by
    (apply strict_checked; [reflexivity|exact Hchecked]).
  split; [apply ssa_strict_laws|apply (ssa_refined_reachable_strict no_ext)];
    [exact Hwf|left; reflexivity|exact Hwf|left; reflexivity].
Qed.

(** Three live frames are extracted innermost first, with each caller still at its call. *)
Example strict_nested_frame_extraction :
  map (frame_activation strict_nested strict_leaf_out) [0; 1; 2; 3] =
    [Some (AState 0 1 (strict_env 4), 2);
     Some (AState 0 1 (strict_env 2), 1);
     Some (AState 0 1 (strict_env 0), 0); None].
Proof.
  reflexivity.
Qed.

Local Lemma strict_start_initial :
  initial (ssa_semantics no_ext strict_nested strict_limits) strict_start.
Proof.
  exists strict_nested_main,
    (SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1)),
    [strict_value], (strict_env 0); repeat split; try reflexivity.
  constructor; [change (0 <= 7 < 4294967296)%Z; lia|constructor].
Qed.

Local Lemma strict_nested_steps :
  step_s no_ext strict_nested strict_limits strict_start [EvOut strict_value] strict_main_out /\
  step_s no_ext strict_nested strict_limits strict_main_out [] strict_middle_start /\
  step_s no_ext strict_nested strict_limits strict_middle_start [EvOut strict_value]
    strict_middle_out /\
  step_s no_ext strict_nested strict_limits strict_middle_out [] strict_leaf_start /\
  step_s no_ext strict_nested strict_limits strict_leaf_start [EvOut strict_value]
    strict_leaf_out /\
  step_s no_ext strict_nested strict_limits strict_leaf_out [] strict_middle_returned /\
  step_s no_ext strict_nested strict_limits strict_middle_returned [] strict_main_returned.
Proof.
  repeat split.
  - eapply SOutput; [exists strict_nested_main,
      (SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1));
      repeat split; reflexivity|reflexivity].
  - eapply SCall with (c := CDirect 1) (args := [0]) (cs := [strict_value])
      (fd := strict_nested_middle)
      (b := SBlock [(2, TyI32)] [IOutput 2] (TCall (CDirect 2) [2] 1));
      try reflexivity; [|cbn; lia].
    exists strict_nested_main,
      (SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1)); repeat split; reflexivity.
  - eapply SOutput; [exists strict_nested_middle,
      (SBlock [(2, TyI32)] [IOutput 2] (TCall (CDirect 2) [2] 1));
      repeat split; reflexivity|reflexivity].
  - eapply SCall with (c := CDirect 2) (args := [2]) (cs := [strict_value])
      (fd := strict_nested_leaf) (b := SBlock [(4, TyI32)] [IOutput 4] (TRet 4));
      try reflexivity; [|cbn; lia].
    exists strict_nested_middle,
      (SBlock [(2, TyI32)] [IOutput 2] (TCall (CDirect 2) [2] 1)); repeat split; reflexivity.
  - eapply SOutput; [exists strict_nested_leaf,
      (SBlock [(4, TyI32)] [IOutput 4] (TRet 4)); repeat split; reflexivity|reflexivity].
  - eapply SReturn with (x := 4); try reflexivity.
    exists strict_nested_leaf, (SBlock [(4, TyI32)] [IOutput 4] (TRet 4));
      repeat split; reflexivity.
  - eapply SReturn with (x := 3); try reflexivity.
    exists strict_nested_middle, (SBlock [(3, TyI32)] [] (TRet 3)); repeat split; reflexivity.
Qed.

(** The actual full run emits the caller, middle and leaf outputs in that order. *)
Example strict_nested_full_run :
  exec (ssa_semantics no_ext strict_nested strict_limits) strict_start
    [EvOut strict_value; EvOut strict_value; EvOut strict_value] strict_main_returned.
Proof.
  destruct strict_nested_steps as [Hmain [Hcall [Hmiddle [Hcall' [Hleaf [Hreturn Hreturn']]]]]].
  eapply exec_step with (l := [EvOut strict_value]); [exact Hmain|].
  eapply exec_step with (l := []); [exact Hcall|].
  eapply exec_step with (l := [EvOut strict_value]); [exact Hmiddle|].
  eapply exec_step with (l := []); [exact Hcall'|].
  eapply exec_step with (l := [EvOut strict_value]); [exact Hleaf|].
  eapply exec_step with (l := []); [exact Hreturn|].
  eapply exec_step with (l := []); [exact Hreturn'|constructor].
Qed.

(** Lifting the resumed outer frame supplies a history inside the actual full trace. *)
Example strict_nested_lifted_history :
  exists a0 trf, initial (activation no_ext strict_nested 0) a0 /\
    exec (activation no_ext strict_nested 0) a0 trf
      (AState 1 0 (env_set (strict_env 0) 1 strict_value)) /\
    subtrace trf [EvOut strict_value; EvOut strict_value; EvOut strict_value].
Proof.
  eapply (activation_lifting no_ext strict_nested strict_limits strict_start strict_main_returned
    _ 0 (strict_checked strict_nested eq_refl (proj1 strict_nested_checked)) strict_start_initial
    strict_nested_full_run); reflexivity.
Qed.

(** The caller's matching activation can keep exactly its own one output before returning. *)
Example strict_outer_nonempty_history :
  exec (activation no_ext strict_nested 0) (AState 0 0 (strict_env 0))
    [EvOut strict_value] (AState 1 0 (env_set (strict_env 0) 1 strict_value)).
Proof.
  eapply exec_step with (l := [EvOut strict_value]) (s' := AState 0 1 (strict_env 0)).
  - eapply AOutput with (x := 0); [|reflexivity].
    exists strict_nested_main,
      (SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1)); repeat split; reflexivity.
  - eapply exec_step with (l := []); [|constructor].
    eapply ACall with (c := CDirect 1) (args := [0]) (ps := [TyI32]) (r := TyI32)
      (cs := [strict_value]) (v := strict_value); try reflexivity.
    + exists strict_nested_main,
        (SBlock [(0, TyI32)] [IOutput 0] (TCall (CDirect 1) [0] 1)); repeat split; reflexivity.
    + change (0 <= 7 < 4294967296)%Z; lia.
Qed.

(** Each of the three live nested frames has a lifted activation history. *)
Example strict_live_nested_histories :
  forall i a f, frame_activation strict_nested strict_leaf_out i = Some (a, f) ->
    exists a0 trf, initial (activation no_ext strict_nested f) a0 /\
      exec (activation no_ext strict_nested f) a0 trf a /\
      subtrace trf [EvOut strict_value; EvOut strict_value; EvOut strict_value].
Proof.
  intros i a f Hframe.
  assert (Hrun : exec (ssa_semantics no_ext strict_nested strict_limits) strict_start
    [EvOut strict_value; EvOut strict_value; EvOut strict_value] strict_leaf_out).
  { destruct strict_nested_steps as [Hmain [Hcall [Hmiddle [Hcall' [Hleaf Hreturns]]]]].
    eapply exec_step with (l := [EvOut strict_value]); [exact Hmain|].
    eapply exec_step with (l := []); [exact Hcall|].
    eapply exec_step with (l := [EvOut strict_value]); [exact Hmiddle|].
    eapply exec_step with (l := []); [exact Hcall'|].
    eapply exec_step with (l := [EvOut strict_value]); [exact Hleaf|constructor]. }
  exact (activation_lifting no_ext strict_nested strict_limits strict_start strict_leaf_out
    _ i (strict_checked strict_nested eq_refl (proj1 strict_nested_checked))
    strict_start_initial Hrun a f Hframe).
Qed.

(** The explicit caller history keeps its output and skips the two callee outputs. *)
Example strict_nested_subtrace :
  subtrace [EvOut strict_value]
    [EvOut strict_value; EvOut strict_value; EvOut strict_value] /\
  subtrace [EvOut strict_value; EvRet strict_value]
    [EvOut strict_value; EvOut strict_value; EvOut strict_value; EvRet strict_value].
Proof.
  split.
  - apply sub_keep; apply sub_nil.
  - apply sub_keep; apply sub_skip; apply sub_skip; apply sub_keep; apply sub_nil.
Qed.
