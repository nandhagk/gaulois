(** * Finite congruence and ranked-observation boundaries

    Positive and negative source fixtures distinguish symbolic congruence from unavailable values.
    For example, a back edge leaves an old addition defined but not ready in its new context.
    Builds on: AnalysesNumbering, ExamplesSsaNumbering and ViewsDominated. *)

From Stdlib Require Import List Bool Arith Lia ZArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsDominated.
From Gaulois.Analyses Require Import AnalysesNumbering.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaBridge ExamplesSsaActivation ExamplesSsaViews
  ExamplesSsaStrict ExamplesSsaAnalyses ExamplesSsaNumbering.
Import List.ListNotations.
Local Open Scope nat_scope.

Definition ana5_no_ext : nat -> list cval -> option cval := fun _ _ => None.
Definition ana5_zero := VInt W32 0%Z.
Definition ana5_one := VInt W32 1%Z.
Definition ana5_two := VInt W32 2%Z.

Definition ana5_merge_second (x : vid) := if Nat.eqb x 3 then 2 else x.

Example ana5_valid_proposal :
  numbering_check label_encoding var_encoding sop_encoding gvn_problem ana5_merge_second = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana5_unequal_proposal_rejected :
  numbering_check label_encoding var_encoding sop_encoding gvn_problem (fun _ => 0) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana5_entry_parameters_independent :
  let s := AState 0 0 (env_set (env_set (fun _ => None) 0 ana5_zero) 1 ana5_one) in
  val (nsv gvn_problem) s 0 = Some ana5_zero /\
  val (nsv gvn_problem) s 1 = Some ana5_one /\
  val (nsv gvn_problem) s 0 <> val (nsv gvn_problem) s 1 /\
  dominator_numbering label_encoding var_encoding sop_encoding gvn_problem 0 <>
    dominator_numbering label_encoding var_encoding sop_encoding gvn_problem 1.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Example ana5_unequal_entry_values_are_initial :
  initial (activation ana5_no_ext gvn_prog 0)
    (AState 0 0 (env_set (env_set (fun _ => None) 0 ana5_zero) 1 ana5_one)).
Proof.
  unfold activation, activation_initial; cbn [initial].
  eexists; eexists; exists [ana5_zero; ana5_one],
    (env_set (env_set (fun _ => None) 0 ana5_zero) 1 ana5_one).
  repeat split; try reflexivity; repeat constructor; cbn [ana5_zero ana5_one valid_cval]; lia.
Qed.

Definition ana5_entry_backedge_prog := Program [(0, FDef 0
  [(0, SBlock [(0, TyI32); (1, TyI32)] [] (TJump 0 [0; 0]))] TyI32)] 0 [].
Definition ana5_entry_backedge_problem := NumberingProblem
  (ssa_block_view ana5_no_ext ana5_entry_backedge_prog 0) gvn_pure
  (values_of ana5_entry_backedge_prog 0).

Example ana5_entry_backedge_does_not_identify_initial_parameters :
  wf_check ana5_entry_backedge_prog = true /\
  numbering_check label_encoding var_encoding sop_encoding ana5_entry_backedge_problem
    (fun _ => 0) = false /\
  optimistic_numbering label_encoding var_encoding sop_encoding ana5_entry_backedge_problem 0 <>
    optimistic_numbering label_encoding var_encoding sop_encoding ana5_entry_backedge_problem 1.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Definition ana5_arbitrary_prog := Program [(0, FDef 0
  [(0, SBlock [(0, TyPtr)] [ILoad 1 TyI32 M4 0; ILoad 2 TyI32 M4 0] (TRet 2))]
  TyI32)] 0 [].
Definition ana5_arbitrary_problem := NumberingProblem
  (ssa_block_view ana5_no_ext ana5_arbitrary_prog 0) gvn_pure
  (values_of ana5_arbitrary_prog 0).

Example ana5_arbitrary_singletons :
  wf_check ana5_arbitrary_prog = true /\
  def (nsv ana5_arbitrary_problem) 1 = Arbitrary /\
  def (nsv ana5_arbitrary_problem) 2 = Arbitrary /\
  numbering_check label_encoding var_encoding sop_encoding ana5_arbitrary_problem
    (fun x => if Nat.eqb x 2 then 1 else x) = false /\
  optimistic_numbering label_encoding var_encoding sop_encoding ana5_arbitrary_problem 1 <>
    optimistic_numbering label_encoding var_encoding sop_encoding ana5_arbitrary_problem 2 /\
  numbering_check label_encoding var_encoding sop_encoding ana5_arbitrary_problem (fun x => x)
    = true.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Example ana5_arbitrary_loads_can_differ : exists s,
  reachable_state (activation ana5_no_ext ana5_arbitrary_prog 0) s /\
  val (nsv ana5_arbitrary_problem) s 1 = Some ana5_one /\
  val (nsv ana5_arbitrary_problem) s 2 = Some ana5_two.
Proof.
  pose (a := AState 0 0 (env_set (fun _ => None) 0 (VPtr 0 0%Z))).
  pose (b := activation_advance a (env_set (aenv a) 1 ana5_one)).
  pose (c := activation_advance b (env_set (aenv b) 2 ana5_two)).
  exists c; split; [|split; reflexivity].
  exists a, []; split.
  - unfold activation, activation_initial; cbn [initial].
    eexists; eexists; exists [VPtr 0 0%Z], (aenv a); repeat split; try reflexivity.
    repeat constructor.
  - eapply exec_step with (l := []) (s' := b).
    + apply (ALoad ana5_no_ext ana5_arbitrary_prog 0 a 1 TyI32 M4 0 ana5_one).
      * unfold at_instr; eexists; eexists; repeat split; reflexivity.
      * reflexivity.
      * cbn [ana5_one valid_cval]; lia.
    + eapply exec_step with (l := []) (s' := c); [|constructor].
      apply (ALoad ana5_no_ext ana5_arbitrary_prog 0 b 2 TyI32 M4 0 ana5_two).
      * unfold at_instr; eexists; eexists; repeat split; reflexivity.
      * reflexivity.
      * cbn [ana5_two valid_cval]; lia.
Qed.

Definition ana5_incomplete_problem := NumberingProblem (nsv gvn_problem) gvn_pure [2; 3].

Example ana5_missing_operands_prevent_merging :
  numbering_check label_encoding var_encoding sop_encoding ana5_incomplete_problem
    ana5_merge_second = false /\
  dominator_numbering label_encoding var_encoding sop_encoding ana5_incomplete_problem 2 <>
    dominator_numbering label_encoding var_encoding sop_encoding ana5_incomplete_problem 3 /\
  optimistic_numbering label_encoding var_encoding sop_encoding ana5_incomplete_problem 2 <>
    optimistic_numbering label_encoding var_encoding sop_encoding ana5_incomplete_problem 3.
Proof.
  vm_compute; repeat split; discriminate.
Qed.

Example ana5_unknown_ids_remain_themselves :
  dominator_numbering label_encoding var_encoding sop_encoding gvn_problem 99 = 99 /\
  optimistic_numbering label_encoding var_encoding sop_encoding gvn_problem 99 = 99 /\
  numbering_check label_encoding var_encoding sop_encoding gvn_problem
    (fun x => if Nat.eqb x 99 then 0 else x) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition ana5_same_home_prog := Program [(0, FDef 0
  [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BAdd) [0; 1]; IOp 3 (OBin W32 BAdd) [0; 1]] (TRet 3))] TyI32)] 0 [].
Definition ana5_same_home_problem := NumberingProblem
  (ssa_block_view ana5_no_ext ana5_same_home_prog 0) gvn_pure
  (values_of ana5_same_home_prog 0).
Definition ana5_same_home_start :=
  AState 0 0 (env_set (env_set (fun _ => None) 0 ana5_zero) 1 ana5_one).
Definition ana5_same_home_middle := activation_advance ana5_same_home_start
  (env_set (aenv ana5_same_home_start) 2 ana5_one).
Definition ana5_same_home_end := activation_advance ana5_same_home_middle
  (env_set (aenv ana5_same_home_middle) 3 ana5_one).
Definition ana5_same_home_observation : numbering_observation unit astate label ssa_edge vid :=
  NumberingObservation (fun _ => ana5_same_home_end) (fun _ x => In x [0; 1; 2; 3])
    (fun _ x => if Nat.ltb x 2 then 0 else 1) (fun _ _ => None).

Example ana5_same_home_operand_readiness :
  wf_check ana5_same_home_prog = true /\
  home (nsv ana5_same_home_problem) 2 = home (nsv ana5_same_home_problem) 3 /\
  aenv ana5_same_home_middle 2 = Some ana5_one /\ aenv ana5_same_home_middle 3 = None /\
  dominator_numbering label_encoding var_encoding sop_encoding ana5_same_home_problem 2 =
    dominator_numbering label_encoding var_encoding sop_encoding ana5_same_home_problem 3.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example ana5_same_home_middle_is_reachable :
  reachable_state (activation ana5_no_ext ana5_same_home_prog 0) ana5_same_home_middle.
Proof.
  exists ana5_same_home_start, []; split.
  - unfold activation, activation_initial; cbn [initial].
    eexists; eexists; exists [ana5_zero; ana5_one], (aenv ana5_same_home_start).
    repeat split; try reflexivity; repeat constructor; cbn [ana5_zero ana5_one valid_cval]; lia.
  - eapply exec_step with (l := []) (s' := ana5_same_home_middle); [|constructor].
    apply (AOp ana5_no_ext ana5_same_home_prog 0 ana5_same_home_start 2 (OBin W32 BAdd)
      [0; 1] [ana5_zero; ana5_one] ana5_one); try reflexivity.
    unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Example ana5_same_home_observation_laws :
  numbering_observation_laws (activation ana5_no_ext ana5_same_home_prog 0)
    ana5_same_home_problem ana5_same_home_observation.
Proof.
  constructor.
  - intros [] x o args c Hready Hdef Hp Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      change (Some ana5_one = Some c) in Hval; injection Hval as <-.
    all: exists [ana5_zero; ana5_one]; split; [|reflexivity].
    all: constructor; [repeat split; cbn; tauto || lia || reflexivity|];
      constructor; [repeat split; cbn; tauto || lia || reflexivity|constructor].
  - intros [] x b i c Hready Hdef Hentry Hval.
    change (In x [0; 1; 2; 3]) in Hready.
    destruct Hready as [<-|[<-|[<-|[<-|Hnone]]]]; try contradiction;
      vm_compute in Hdef; try discriminate; injection Hdef as <- <-;
      exfalso; apply Hentry; left; reflexivity.
Qed.

Example ana5_same_home_ready_values_agree :
  forall c d, val (nsv ana5_same_home_problem) ana5_same_home_end 2 = Some c ->
  val (nsv ana5_same_home_problem) ana5_same_home_end 3 = Some d -> c = d.
Proof.
  intros c d Hc Hd.
  eapply (numbering_observations_equal (activation ana5_no_ext ana5_same_home_prog 0)
    label_encoding var_encoding sop_encoding ana5_same_home_problem ana5_same_home_observation
    (dominator_numbering label_encoding var_encoding sop_encoding ana5_same_home_problem)
    ana5_same_home_observation_laws (dominator_numbering_checked _ _ _ _) tt 2 3 c d);
    try exact Hc; try exact Hd; vm_compute; intuition discriminate.
Qed.

Definition ana5_trap_prog := Program [(0, FDef 0
  [(0, SBlock [(0, TyI32); (1, TyI32)]
    [IOp 2 (OBin W32 BDivU) [0; 1]; IOp 3 (OBin W32 BDivU) [0; 1]] (TRet 3))] TyI32)] 0 [].
Definition ana5_trap_problem := NumberingProblem (ssa_block_view ana5_no_ext ana5_trap_prog 0)
  gvn_pure (values_of ana5_trap_prog 0).

Example ana5_congruent_pure_operations_can_trap :
  wf_check ana5_trap_prog = true /\ gvn_pure (OBin W32 BDivU) = true /\
  op_eval ana5_no_ext (OBin W32 BDivU) [ana5_one; ana5_zero] = None /\
  optimistic_numbering label_encoding var_encoding sop_encoding ana5_trap_problem 2 =
    optimistic_numbering label_encoding var_encoding sop_encoding ana5_trap_problem 3 /\
  numbering_check label_encoding var_encoding sop_encoding ana5_trap_problem
    (optimistic_numbering label_encoding var_encoding sop_encoding ana5_trap_problem) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example ana5_actual_trapping_activation :
  activation_trapped ana5_no_ext ana5_trap_prog 0
    (AState 0 0 (env_set (env_set (fun _ => None) 0 ana5_one) 1 ana5_zero)).
Proof.
  exists 2, (OBin W32 BDivU), [0; 1], [ana5_one; ana5_zero]; split.
  - unfold at_instr; eexists; eexists; repeat split; reflexivity.
  - split; reflexivity.
Qed.

Example ana5_stable_operation_repeats : exists a b c d tr o args,
  reachable_state (activation ana5_no_ext gvn_loop_prog 0) a /\
  def (nsv gvn_loop_problem) gvn_loop_value = Op o args /\
  step (activation ana5_no_ext gvn_loop_prog 0) a [] b /\
  exec_in (activation ana5_no_ext gvn_loop_prog 0)
    (fun u => body gvn_loop_info (point (base (nsv gvn_loop_problem)) u) = true) b tr c /\
  step (activation ana5_no_ext gvn_loop_prog 0) c [] d /\
  val (nsv gvn_loop_problem) a gvn_loop_value <>
    val (nsv gvn_loop_problem) b gvn_loop_value /\
  val (nsv gvn_loop_problem) c gvn_loop_value = val (nsv gvn_loop_problem) d gvn_loop_value.
Proof.
  destruct gvn_loop_recomputed as (a & b & c & d & tr & o & args & Hr & Hdef & Hat & Hstep &
    Hchange & Hrun & Hat' & Hstep' & Ha & Hd & Heq).
  exists a, b, c, d, tr, o, args; repeat split; assumption.
Qed.

(** A new loop parameter makes the preceding iteration's second result stale. *)
Definition ana5_stale_prog := Program [(0, FDef 0
  [(0, SBlock [(0, TyI32)] [IOp 1 (OConst ana5_one) []] (TJump 1 [0]));
   (1, SBlock [(3, TyI32)]
     [IOp 4 (OBin W32 BAdd) [3; 1]; IOp 5 (OBin W32 BAdd) [3; 1]] (TJump 1 [4]))]
  TyI32)] 0 [].
Definition ana5_stale_problem := NumberingProblem
  (ssa_block_view ana5_no_ext ana5_stale_prog 0) gvn_pure (values_of ana5_stale_prog 0).
Definition ana5_stale_initial := AState 0 0 (env_set (fun _ => None) 0 ana5_zero).
Definition ana5_stale_entry_source := activation_advance ana5_stale_initial
  (env_set (aenv ana5_stale_initial) 1 ana5_one).
Definition ana5_stale_header := activation_enter 1
  (env_set (aenv ana5_stale_entry_source) 3 ana5_zero).
Definition ana5_stale_first := activation_advance ana5_stale_header
  (env_set (aenv ana5_stale_header) 4 ana5_one).
Definition ana5_stale_back_source := activation_advance ana5_stale_first
  (env_set (aenv ana5_stale_first) 5 ana5_one).
Definition ana5_stale_back_target := activation_enter 1
  (env_set (aenv ana5_stale_back_source) 3 ana5_one).
Definition ana5_stale_state := activation_advance ana5_stale_back_target
  (env_set (aenv ana5_stale_back_target) 4 ana5_two).

Example ana5_stale_backedge_reachable :
  wf_check ana5_stale_prog = true /\
  reachable_state (activation ana5_no_ext ana5_stale_prog 0) ana5_stale_state.
Proof.
  split; [vm_compute; reflexivity|].
  exists ana5_stale_initial, []; split.
  - unfold activation, activation_initial; cbn [initial].
    eexists; eexists; exists [ana5_zero], (aenv ana5_stale_initial).
    repeat split; try reflexivity; repeat constructor; cbn [ana5_zero valid_cval]; lia.
  - eapply exec_step with (l := []) (s' := ana5_stale_entry_source).
    + apply (AOp ana5_no_ext ana5_stale_prog 0 ana5_stale_initial 1 (OConst ana5_one)
        [] [] ana5_one); try reflexivity.
      unfold at_instr; eexists; eexists; repeat split; reflexivity.
    + eapply exec_step with (l := []) (s' := ana5_stale_header).
      * apply (AJump ana5_no_ext ana5_stale_prog 0 ana5_stale_entry_source 1 [0]
          [ana5_zero] (aenv ana5_stale_header)); try reflexivity.
        unfold at_term; eexists; eexists; repeat split; reflexivity.
      * eapply exec_step with (l := []) (s' := ana5_stale_first).
        -- apply (AOp ana5_no_ext ana5_stale_prog 0 ana5_stale_header 4 (OBin W32 BAdd)
             [3; 1] [ana5_zero; ana5_one] ana5_one); try reflexivity.
           unfold at_instr; eexists; eexists; repeat split; reflexivity.
        -- eapply exec_step with (l := []) (s' := ana5_stale_back_source).
           ++ apply (AOp ana5_no_ext ana5_stale_prog 0 ana5_stale_first 5 (OBin W32 BAdd)
                [3; 1] [ana5_zero; ana5_one] ana5_one); try reflexivity.
              unfold at_instr; eexists; eexists; repeat split; reflexivity.
           ++ eapply exec_step with (l := []) (s' := ana5_stale_back_target).
              ** apply (AJump ana5_no_ext ana5_stale_prog 0 ana5_stale_back_source 1 [4]
                   [ana5_one] (aenv ana5_stale_back_target)); try reflexivity.
                 unfold at_term; eexists; eexists; repeat split; reflexivity.
              ** eapply exec_step with (l := []) (s' := ana5_stale_state); [|constructor].
                 apply (AOp ana5_no_ext ana5_stale_prog 0 ana5_stale_back_target 4
                   (OBin W32 BAdd) [3; 1] [ana5_one; ana5_one] ana5_two); try reflexivity.
                 unfold at_instr; eexists; eexists; repeat split; reflexivity.
Qed.

Example ana5_stale_equal_classes_have_unequal_current_bindings :
  optimistic_numbering label_encoding var_encoding sop_encoding ana5_stale_problem 4 =
    optimistic_numbering label_encoding var_encoding sop_encoding ana5_stale_problem 5 /\
  numbering_check label_encoding var_encoding sop_encoding ana5_stale_problem
    (optimistic_numbering label_encoding var_encoding sop_encoding ana5_stale_problem) = true /\
  val (nsv ana5_stale_problem) ana5_stale_state 4 = Some ana5_two /\
  val (nsv ana5_stale_problem) ana5_stale_state 5 = Some ana5_one /\
  val (nsv ana5_stale_problem) ana5_stale_state 4 <>
    val (nsv ana5_stale_problem) ana5_stale_state 5.
Proof.
  vm_compute; repeat split; discriminate || reflexivity.
Qed.

Definition ana5_stale_observation : numbering_observation unit astate label ssa_edge vid :=
  NumberingObservation (fun _ => ana5_stale_state) (fun _ x => In x [0; 1; 3; 4; 5])
    (fun _ x => if Nat.eqb x 4 || Nat.eqb x 5 then 2 else if Nat.eqb x 3 then 1 else 0)
    (fun _ _ => None).

Example ana5_stale_binding_cannot_be_observed_ready :
  ~ numbering_observation_laws (activation ana5_no_ext ana5_stale_prog 0)
    ana5_stale_problem ana5_stale_observation.
Proof.
  intro Hlaws.
  destruct (observed_op Hlaws tt 5 (OBin W32 BAdd) [3; 1] ana5_one)
    as [cs [Hcs Heval]]; [cbn; tauto|reflexivity|reflexivity|reflexivity|].
  inversion Hcs as [|a c args tail [Hready [Hrank Hc]] Htail]; subst.
  inversion Htail as [|b d args' tail' [Hready' [Hrank' Hd]] Hnil]; subst.
  inversion Hnil; subst.
  change (Some ana5_one = Some c) in Hc; injection Hc as <-.
  change (Some ana5_one = Some d) in Hd; injection Hd as <-.
  discriminate Heval.
Qed.

(** A transition to None satisfies the older origin laws but violates the new pure-binding law. *)
Definition ana5_toggle_graph : Graph.t unit unit :=
  Graph.Make [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt).
Definition ana5_toggle_semantics : semantics bool unit :=
  Semantics (fun s => s = false) (fun s tr t => tr = [] /\ t = negb s).
Definition ana5_toggle_view : ssa_view bool unit unit unit unit unit unit :=
  SsaView (GraphView ana5_toggle_graph (fun _ : bool => tt) (fun _ _ _ _ => False)
    (fun _ _ _ => True)) (fun _ => Op tt []) (fun _ => tt) (fun _ => [])
    (fun _ => []) (fun _ => []) (fun s _ => if s then Some tt else None)
    (fun _ _ => Some tt) (fun _ => false).
Definition ana5_toggle_problem := NumberingProblem ana5_toggle_view (fun _ => true) [tt].
Definition ana5_toggle_loop := LoopInfo tt (fun _ => true).

Example ana5_transition_none_has_old_ssa_laws :
  ssa_view_laws ana5_toggle_semantics ana5_toggle_view /\
  strict_ssa_laws ana5_toggle_semantics ana5_toggle_view.
Proof.
  split.
  - constructor.
    + constructor.
      * constructor.
        -- repeat constructor; cbn; tauto.
        -- intros [] Hin; cbn; tauto.
        -- intros [] [] Hin; contradiction.
        -- intros [] [] Hnode Hin; contradiction.
      * intros s Hstart; cbn; tauto.
      * intros s tr t Hr Hstep; left; exact I.
      * intros s tr t e Hr Hstep Htaken; contradiction.
      * intros s tr t Hr Hstep Hstay; reflexivity.
    + intros x b i Hdef; discriminate.
    + intros s tr t e Hr Hstep Htaken; contradiction.
    + intros s tr t e Hr Hstep Htaken; contradiction.
    + intros s tr t [] [] Hr Hstep Hpost.
      right; left; exists tt, [], []; repeat split; constructor || reflexivity.
  - constructor.
    + intros s tr t x Hr Hstep Hstay Hchanged; reflexivity.
    + intros s tr t e x Hr Hstep Htaken; contradiction.
    + intros s tr t x Hr Hstep Hstay Haway; exfalso; apply Haway; reflexivity.
    + intros s tr t e x Hr Hstep Htaken; contradiction.
    + intros e cd He; contradiction.
    + intros x o args y Hdef Hy; inversion Hdef; subst; contradiction.
Qed.

Example ana5_transition_none_is_excluded_by_pure_binding :
  invariant_in ana5_toggle_problem ana5_toggle_loop tt = true /\
  loop_operands_stable ana5_toggle_semantics ana5_toggle_problem ana5_toggle_loop tt /\
  ~ numbering_loop_laws ana5_toggle_semantics ana5_toggle_problem.
Proof.
  split; [reflexivity|split].
  - intros o args y s tr t Hinside Hdef Hp Hy Hr Hrun.
    injection Hdef as <- <-; contradiction.
  - intro Hlaws.
    assert (Hr : reachable_state ana5_toggle_semantics true).
    { exists false, []; split; [reflexivity|].
      exact (exec_step (m := ana5_toggle_semantics) false [] true [] true
        (conj eq_refl eq_refl) (exec_refl true)). }
    assert (Hchanged : val ana5_toggle_view false tt <> val ana5_toggle_view true tt)
      by discriminate.
    destruct (loop_op_binding Hlaws true [] false tt tt [] Hr (conj eq_refl eq_refl)
      eq_refl eq_refl Hchanged) as [cs [c [_ [_ Hval]]]]; discriminate.
Qed.

Example ana5_transition_none_boundary :
  step ana5_toggle_semantics true [] false /\
  val ana5_toggle_view true tt = Some tt /\ val ana5_toggle_view false tt = None.
Proof.
  repeat split; reflexivity.
Qed.

Definition ana5_operation_cycle_view : ssa_view bool unit unit unit unit unit unit :=
  SsaView (base ana5_toggle_view) (fun _ => Op tt [tt]) (fun _ => tt) (fun _ => [])
    (fun _ => []) (fun _ => []) (val ana5_toggle_view) (fun _ _ => Some tt) (fun _ => false).

Example ana5_recursive_operation_cycle_is_not_invariant :
  invariant_in (NumberingProblem ana5_operation_cycle_view (fun _ => true) [tt])
    ana5_toggle_loop tt = false.
Proof.
  vm_compute; reflexivity.
Qed.
