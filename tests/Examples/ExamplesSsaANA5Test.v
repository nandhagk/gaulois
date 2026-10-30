(** * Concrete value-numbering client regressions

    These examples exercise source bindings, dominated uses, cyclic phi histories and loops.
    For example, the cyclic phi client reaches its use after both an entry and a back edge.
    Builds on: ExamplesSsaNumbering and AnalysesNumbering. *)

From Stdlib Require Import List Arith ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa.
From Gaulois.Analyses Require Import AnalysesNumbering.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaActivation ExamplesSsaViews
  ExamplesSsaAnalyses ExamplesSsaNumbering.
Import List.ListNotations.
Local Open Scope nat_scope.

(** Scoped numbering merges the original two-block additions and passes its checker. *)
Example gvn_merges :
  dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_second =
    dominator_numbering label_encoding var_encoding sop_encoding gvn_problem gvn_first /\
  numbering_check label_encoding var_encoding sop_encoding gvn_problem
    (dominator_numbering label_encoding var_encoding sop_encoding gvn_problem) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gvn_actual_binding : exists c d,
  val (nsv gvn_problem) gvn_binding_state gvn_second = Some c /\
  val (nsv gvn_problem) gvn_binding_state gvn_first = Some d /\ c = d.
Proof.
  exact gvn_binding_equal.
Qed.

Example gvn_actual_dominated_use : exists c,
  val (nsv gvn_use_problem) gvn_use_state gvn_first = Some c /\
  val (nsv gvn_use_problem) gvn_use_state gvn_second = Some c.
Proof.
  exact gvn_use_equal.
Qed.

Example gvn_phi_nontrivial_class : gvn_phi_left <> gvn_phi_right /\
  optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_left =
    optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem gvn_phi_right /\
  numbering_check label_encoding var_encoding sop_encoding gvn_phi_problem
    (optimistic_numbering label_encoding var_encoding sop_encoding gvn_phi_problem) = true.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Example gvn_phi_entry_and_back_contexts :
  observation_previous gvn_phi_observation 2 1 = Some (SsaEdge 1 1 0, 1) /\
  observation_previous gvn_phi_observation 1 1 = Some (SsaEdge 0 1 0, 0) /\
  observation_rank gvn_phi_observation 1 gvn_phi_left <
    observation_rank gvn_phi_observation 2 gvn_phi_left.
Proof.
  vm_compute; repeat split; reflexivity || apply Nat.lt_succ_diag_r.
Qed.

Example gvn_phi_unrolled_use :
  reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation 2) /\
  exists c, val (nsv gvn_phi_problem) (observation_state gvn_phi_observation 2)
    gvn_phi_left = Some c /\
    val (nsv gvn_phi_problem) (observation_state gvn_phi_observation 2) gvn_phi_right = Some c.
Proof.
  assert (Hr : reachable_state (activation (fun _ _ => None) gvn_phi_prog 0)
    (observation_state gvn_phi_observation 2)).
  { destruct (observed_param gvn_phi_observation_laws 2 gvn_phi_left 1 0 (VInt W32 0%Z))
      as [e [h [z [l [t [tr [Hprevious [He [Htarget [Hz [Hready [Hrank
        [Hval [Hreachable [Hstep [Htaken Hrun]]]]]]]]]]]]]]]];
      [cbn; tauto|reflexivity|cbn; intuition discriminate|reflexivity|].
    eapply reachable_state_exec; [|exact Hrun].
    eapply reachable_state_step; eassumption. }
  split; [exact Hr|].
  exists (VInt W32 0%Z); split; reflexivity.
Qed.

Example gvn_loop_inside_value :
  body gvn_loop_info (home (nsv gvn_loop_problem) gvn_loop_value) = true /\
  invariant_in gvn_loop_problem gvn_loop_info gvn_loop_value = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gvn_loop_real_execution : exists s tr t,
  reachable_state (activation (fun _ _ => None) gvn_loop_prog 0) s /\
  exec_in (activation (fun _ _ => None) gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) s tr t /\ s <> t.
Proof.
  exact gvn_loop_run.
Qed.

Example gvn_loop_direct_stability :
  loop_operands_stable (activation (fun _ _ => None) gvn_loop_prog 0)
    gvn_loop_problem gvn_loop_info gvn_loop_value.
Proof.
  exact gvn_loop_stability.
Qed.
