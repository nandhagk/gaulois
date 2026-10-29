(** * While analysis and erasure computations

    These examples execute the dense engines and check the actual While view boundaries.
    For example, the factorial counter is live but unneeded, and its assignment is erased.
    Builds on: While analyses, region summaries and the total worklist engine. *)

From Stdlib Require Import List Bool Arith ZArith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderPointwise OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointTotal FixpointIndex
  FixpointSchedule.
From Gaulois.Views Require Import ViewsSemantics ViewsSkeleton ViewsStructured ViewsRegion
  ViewsEffects.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesDemand.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics
  ExamplesWhileSkeleton ExamplesWhileViews ExamplesWhileAnalyses.
Import List.ListNotations.

Local Open Scope nat_scope.

(** A successful bounded engine run exposes the exact result of the total engine. *)
Local Lemma while_total_computation {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys)
    (HT : terminates L ss sch Joining) :
  (match run_worklist EX EC L sch Joining sys
    (Declared ss (index_system EX sys ss)) 4096%positive with
   | Some _ => true
   | None => false
   end) = true ->
  proj1_sig (solve_total EX EC L HL sch Joining sys ss HT) =
    lookup EX L (match run_worklist EX EC L sch Joining sys
      (Declared ss (index_system EX sys ss)) 4096%positive with
      | Some result => result
      | None => Map.empty
      end).
Proof.
  destruct (run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss))
    4096%positive) as [result|] eqn:Hrun; [intro Hsuccess|discriminate].
  destruct (solve_total_run EX EC L sys sch Joining HL ss HT) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [total [Htotal Heq]].
  assert (total = result) as ->.
  { eapply total_completed_runs_unique; [exact Htotal|exact Hrun]. }
  exact Heq.
Qed.

(** The engine reports the counter live at the actual factorial loop-body entry. *)
Example while_z_live :
  fmem var_encoding z_var (while_live_at factorial_while loop_head) = true.
Proof.
  unfold while_live_at, solve_liveness.
  rewrite while_total_computation; vm_compute; reflexivity.
Qed.

(** The closed neededness engine excludes the counter's self-dependent value. *)
Example while_z_dead : while_dead_var factorial_while z_var = true.
Proof.
  unfold while_dead_var, dead_value, needed_values, demand_solver.
  rewrite while_total_computation; vm_compute; reflexivity.
Qed.

(** Actual demand-driven erasure produces exactly the fixture with the counter update skipped. *)
Example while_dce_factorial :
  while_dce factorial_while word_stores (while_needed factorial_while) = factorial_while_dce.
Proof.
  unfold while_needed, needed_values, demand_solver.
  rewrite while_total_computation; vm_compute; reflexivity.
Qed.

(** The actual While diamond accepts a nonempty insertion and deletion using all three engines. *)
Example while_lcm_accepts :
  lcm_check expr_encoding (while_genkill_view lcm_prog word_stores)
    (lcm_avail lcm_prog) (lcm_busy lcm_prog)
    (lcm_avail2 lcm_prog lcm_result_ex) lcm_result_ex = true.
Proof.
  unfold lcm_avail, lcm_busy, lcm_avail2, while_solve_available.
  rewrite !while_total_computation; vm_compute; reflexivity.
Qed.

(** The accepted motion fixture really inserts on the empty arm and deletes at the join. *)
Example while_lcm_nontrivial :
  insert lcm_result_ex (SkelEdge (PEntry [DFirst; DSecond]) 0) =
    [EBin Add (EVar 3) (EVar 4)] /\
  delete lcm_result_ex (PEntry [DSecond]) = [EBin Add (EVar 3) (EVar 4)].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A no-op program has no live variables and an empty closed demand. *)
Example while_empty_analyses :
  fmem var_encoding 0 (while_live_at SSkip (PEntry [])) = false /\
  while_dead_var SSkip 0 = true /\ while_dce SSkip word_stores (while_needed SSkip) = SSkip.
Proof.
  split.
  - unfold while_live_at, solve_liveness.
    rewrite while_total_computation; vm_compute; reflexivity.
  - split.
    + unfold while_dead_var, dead_value, needed_values, demand_solver.
      rewrite while_total_computation; vm_compute; reflexivity.
    + reflexivity.
Qed.

(** Block completion distinguishes escaping depth zero from depth one. *)
Example while_region_block_exits :
  summarise (while_region_alg SSkip) (Skeleton.Block (Skeleton.Jump 0)) = (true, []) /\
  summarise (while_region_alg SSkip) (Skeleton.Block (Skeleton.Jump 1)) = (false, [0]).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A table retains its default before ordered duplicate entries, including after lowering. *)
Example while_region_table_inventory :
  summarise (while_region_alg SSkip) (Skeleton.JumpTable (EConst 0%Z) [2; 0; 2; 1] 1) =
    (false, [1; 2; 0; 2; 1]) /\
  summarise (while_region_alg SSkip)
    (Skeleton.Block (Skeleton.Loop (Skeleton.JumpTable (EConst 0%Z) [2; 0; 2; 1] 3))) =
    (true, [1; 0; 0]).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Translated break and continue subtrees keep their distinct loop and block summaries. *)
Example while_region_translated_jumps :
  summarise (while_region_alg (SLoop (SBreak 0)))
    (Skeleton.Loop (to_skeleton (SBreak 0))) = (false, [0]) /\
  summarise (while_region_alg (SLoop (SContinue 0)))
    (Skeleton.Loop (to_skeleton (SContinue 0))) = (false, []) /\
  summarise (while_region_alg SSkip) (to_skeleton (SLoop (SBreak 0))) = (true, []) /\
  summarise (while_region_alg SSkip) (to_skeleton (SLoop (SContinue 0))) = (false, []).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Nested translated loops validate both jump kinds and retain ordered outer escapes. *)
Example while_nested_structured :
  loops_ok 0 (SLoop (SLoop (SSeq (SContinue 1) (SBreak 1)))) = true /\
  labels_ok 0 (to_skeleton (SLoop (SLoop (SSeq (SContinue 1) (SBreak 1))))) = true /\
  summarise (while_region_alg SSkip)
    (to_skeleton (SLoop (SSeq (SContinue 1) (SBreak 1)))) = (false, [0; 1]).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Whole-state equality relates an actual initial skip state to itself and matches its ANop. *)
Example while_skip_effects_positive :
  let st : store := fun _ => 0%Z in
  initial (skeleton_semantics (to_skeleton SSkip) (while_client (fun _ => True)))
    (Go [] [] st) /\
  heap_agree (while_effects_view SSkip) (Go [] [] st) (Go [] [] st) /\
  instr_at (while_effects_view SSkip) (Go [] [] st) = Some ANop /\
  step (skeleton_semantics (to_skeleton SSkip) (while_client (fun _ => True)))
    (Go [] [] st) [] (Ret [] [] st).
Proof.
  split; [exists (fun _ => 0%Z); split; [reflexivity|exact I]|].
  split; [reflexivity|split; [reflexivity|]].
  eapply step_atom; [reflexivity|split; reflexivity].
Qed.

(** Separate erasure agreement permits different dead values in actual While states. *)
Example while_erasure_dead_values :
  let d := while_needed SSkip in
  er_agree var_encoding (while_erasure SSkip word_stores d) d
    (Go [] [] (fun _ => 0%Z)) (Go [] [] (fun _ => 1%Z)) /\ (0 <> 1)%Z.
Proof.
  split; [|discriminate].
  change (forall x, dget var_encoding bool_lattice (while_needed SSkip) x = true -> (0 = 1)%Z).
  intros x Hneed; unfold dget, pointwise_lookup in Hneed.
  rewrite finite_map_out in Hneed; [discriminate|].
  change (~ In x []); tauto.
Qed.

(** The actual reachable finished skip state is not heap-related to its initial Go state. *)
Example while_skip_effects_finished_negative :
  let st : store := fun _ => 0%Z in
  reachable_state (skeleton_semantics (to_skeleton SSkip) (while_client (fun _ => True)))
    (Ret [] [] st) /\
  ~ heap_agree (while_effects_view SSkip) (Go [] [] st) (Ret [] [] st).
Proof.
  split.
  - exists (Go [] [] (fun _ => 0%Z)), []; split.
    + exists (fun _ => 0%Z); split; [reflexivity|exact I].
    + apply exec_one; eapply step_atom; [reflexivity|split; reflexivity].
  - discriminate.
Qed.
