(** * Checked rewrite execution examples

    These examples distinguish accepted rewrites from invalid attempts and scheduler stops.
    For example, rewriting operator zero to operator one allocates a new represented term.
    Builds on: RewriteRun and the directly proved graph operations. *)

From Stdlib Require Import List Bool NArith PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteRun.
Import List.ListNotations.

Definition run_signature : rw_signature nat bool nat :=
  {| rw_var_sort := fun v => Some (Nat.eqb v 10);
     rw_operator_shape := fun _ sorts result =>
       negb result && match sorts with [false] => true | _ => false end |}.

Definition run_rule : rw_rule nat bool nat unit :=
  {| rw_holes := [tt];
     rw_hole_sort := fun _ => Some false;
     rw_lhs := RWPApp false 0 [RWHole false tt];
     rw_rhs := RWPApp false 1 [RWHole false tt];
     rw_condition := fun sub =>
       match sub tt with
       | Some (RWVar _ v) => Nat.eqb v 0
       | _ => false
       end |}.

Definition run_admissible (sem : rw_semantics nat bool nat nat) : Prop :=
  forall value, rw_eval_op sem 0 [value] = rw_eval_op sem 1 [value].

Example run_rule_well_formed : rw_rule_wf run_signature run_rule.
Proof.
  split.
  - constructor; [intro Hin; inversion Hin|constructor].
  - split.
    + intros []; split; intro Hdomain; [exists false; reflexivity|now left].
    + split.
      * apply rwp_typed_app; [constructor; [constructor; reflexivity|constructor]|reflexivity].
      * split.
        -- apply rwp_typed_app; [constructor; [constructor; reflexivity|constructor]|reflexivity].
        -- reflexivity.
Qed.

Example run_rule_semantically_sound : rw_rule_sound run_signature run_admissible run_rule.
Proof.
  intros sub lhs rhs Hsub Hguard Hlhs Hrhs.
  cbn [run_rule rw_lhs rw_rhs rw_instantiate] in Hlhs, Hrhs.
  destruct (sub tt) as [t|] eqn:Hterm; [|discriminate].
  injection Hlhs as <-; injection Hrhs as <-; intros sem Hsem.
  rewrite !rw_denote_app, !rw_denote_args_cons.
  destruct (rw_denote sem t) as [value|]; cbn [rw_denote_args]; [apply Hsem|reflexivity].
Qed.

Definition run_semantics : rw_semantics nat bool nat nat :=
  {| rw_var_value := fun v => Some v;
     rw_eval_op := fun _ values => match values with [value] => Some value | _ => None end |}.

Example run_admissible_inhabited : run_admissible run_semantics.
Proof.
  intro value; reflexivity.
Qed.

Definition run_source : rw_term nat bool nat := RWApp false 0 [RWVar false 0].

Definition run_target : rw_term nat bool nat := RWApp false 1 [RWVar false 0].

Definition run_initial := rw_add nat_encoding bool_encoding nat_encoding rw_empty run_source.

Definition run_graph := fst run_initial.

Definition run_root := snd run_initial.

Definition run_attempt (index : nat) (t : rw_term nat bool nat) : rw_attempt nat bool nat unit :=
  RwAttempt index run_root (Map.set unit_encoding tt t Map.empty).

Definition run_good_attempt := run_attempt 0 (RWVar false 0).

Definition run_apply :=
  rw_apply nat_encoding bool_encoding nat_encoding unit_encoding run_signature [run_rule].

Definition run_result :=
  match run_apply run_graph run_good_attempt with
  | Some accepted => accepted
  | None => run_graph
  end.

Example run_initial_invariants :
  rw_graph_wf run_signature run_graph /\
  rw_graph_sound run_signature run_admissible [run_rule] run_graph /\
  rw_productive run_graph /\ rw_represents run_graph run_root run_source.
Proof.
  pose proof (rw_add_correct nat_encoding bool_encoding nat_encoding run_signature
    run_admissible [run_rule] rw_empty run_source (rw_empty_wf run_signature)
    (rw_empty_sound run_signature run_admissible [run_rule]) rw_empty_productive) as Hadded.
  assert (Htyped : rw_typed run_signature run_source).
  { apply rw_typed_app; [constructor; [constructor; reflexivity|constructor]|reflexivity]. }
  specialize (Hadded Htyped).
  change (rw_graph_wf run_signature run_graph /\
    rw_graph_sound run_signature run_admissible [run_rule] run_graph /\
    rw_productive run_graph /\ rw_extends rw_empty run_graph /\
    rw_represents run_graph run_root run_source) in Hadded.
  destruct Hadded as [Hwf [Hsound [Hproductive [Hext Hrepr]]]]; auto.
Qed.

Example accepted_nontrivial_rewrite :
  run_apply run_graph run_good_attempt = Some run_result /\
  rw_rep_test nat_encoding bool_encoding nat_encoding run_result run_root run_source = true /\
  rw_rep_test nat_encoding bool_encoding nat_encoding run_result run_root run_target = true /\
  length (rw_nodes_in run_graph) = 2 /\ length (rw_nodes_in run_result) = 3.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example accepted_rewrite_invariants :
  rw_graph_wf run_signature run_result /\
  rw_graph_sound run_signature run_admissible [run_rule] run_result /\
  rw_productive run_result /\ rw_clean run_result /\ rw_extends run_graph run_result.
Proof.
  destruct run_initial_invariants as [Hwf [Hsound [Hproductive Hrepr]]].
  apply (rw_apply_correct nat_encoding bool_encoding nat_encoding unit_encoding
    run_signature run_admissible [run_rule] run_graph run_result run_good_attempt).
  - constructor; [exact run_rule_well_formed|constructor].
  - constructor; [exact run_rule_semantically_sound|constructor].
  - exact Hwf.
  - exact Hsound.
  - exact Hproductive.
  - exact (proj1 accepted_nontrivial_rewrite).
Qed.

Definition run_false_source : rw_term nat bool nat := RWApp false 0 [RWVar false 1].

Definition run_false_graph :=
  fst (rw_add nat_encoding bool_encoding nat_encoding rw_empty run_false_source).

Example false_guard_rejected :
  rw_rep_test nat_encoding bool_encoding nat_encoding run_false_graph run_root run_false_source =
    true /\ run_apply run_false_graph (run_attempt 0 (RWVar false 1)) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example missing_substitution_rejected :
  rw_check_sub nat_encoding bool_encoding nat_encoding unit_encoding run_signature run_rule
    (fun _ => None) = false /\
  run_apply run_graph (RwAttempt 0 run_root Map.empty) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example wrong_sort_substitution_rejected :
  rw_check_sub nat_encoding bool_encoding nat_encoding unit_encoding run_signature run_rule
    (fun _ => Some (RWVar true 10)) = false /\
  run_apply run_graph (run_attempt 0 (RWVar true 10)) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example recursively_mistyped_substitution_rejected :
  rw_check_sub nat_encoding bool_encoding nat_encoding unit_encoding run_signature run_rule
    (fun _ => Some (RWApp false 0 [RWVar false 10])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition run_extra_hole_rule : rw_rule nat bool nat bool :=
  {| rw_holes := [false; true];
     rw_hole_sort := fun _ => Some false;
     rw_lhs := RWHole false false;
     rw_rhs := RWHole false false;
     rw_condition := fun _ => true |}.

Example unused_declared_hole_still_required :
  rw_check_sub nat_encoding bool_encoding nat_encoding bool_encoding run_signature
    run_extra_hole_rule (fun h => if h then None else Some (RWVar false 0)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_rule_rejected : run_apply run_graph (run_attempt 1 (RWVar false 0)) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example absent_source_rejected : run_apply rw_empty run_good_attempt = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition run_schedule :=
  rw_run nat_encoding bool_encoding nat_encoding unit_encoding run_signature [run_rule].

Definition run_once : rw_strategy nat bool nat unit :=
  fun g => if rw_rep_test nat_encoding bool_encoding nat_encoding g run_root run_target
    then None else Some run_good_attempt.

Example strategy_stops_after_accepted_rewrite :
  rw_run_graph (run_schedule run_once 2 run_graph) = run_result /\
  rw_run_stop (run_schedule run_once 2 run_graph) = RWStopped.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example bounded_run_invariants :
  let g := rw_run_graph (run_schedule run_once 2 run_graph) in
  rw_graph_wf run_signature g /\
  rw_graph_sound run_signature run_admissible [run_rule] g /\
  rw_productive g /\ rw_extends run_graph g.
Proof.
  destruct run_initial_invariants as [Hwf [Hsound [Hproductive Hrepr]]].
  apply (rw_run_correct nat_encoding bool_encoding nat_encoding unit_encoding
    run_signature run_admissible [run_rule] run_once 2 run_graph).
  - constructor; [exact run_rule_well_formed|constructor].
  - constructor; [exact run_rule_semantically_sound|constructor].
  - exact Hwf.
  - exact Hsound.
  - exact Hproductive.
Qed.

Example stopped_does_not_mean_saturated :
  run_schedule (fun _ => None) 1 run_graph = RwRunResult run_graph RWStopped /\
  rw_rep_test nat_encoding bool_encoding nat_encoding run_graph run_root run_target = false /\
  run_apply run_graph run_good_attempt = Some run_result.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example zero_fuel_exhausted :
  run_schedule (fun _ => None) 0 run_graph = RwRunResult run_graph RWFuelExhausted.
Proof.
  reflexivity.
Qed.

Example exhausted_after_one_accepted_attempt :
  run_schedule run_once 1 run_graph = RwRunResult run_result RWFuelExhausted.
Proof.
  vm_compute; reflexivity.
Qed.

Example stopped_strategy_with_large_binary_fuel :
  run_schedule (fun _ => None) 1000000000000000000000000 run_graph =
    RwRunResult run_graph RWStopped.
Proof.
  vm_compute; reflexivity.
Qed.

Example failed_attempt_consumes_fuel_and_preserves_graph :
  run_schedule (fun _ => Some (run_attempt 0 (RWVar false 1))) 3 run_false_graph =
    RwRunResult run_false_graph RWFuelExhausted.
Proof.
  vm_compute; reflexivity.
Qed.

(** This malformed graph reaches union rejection after tentatively interning the right-hand side. *)
Definition run_bad_sort_graph : rw_graph nat bool nat :=
  RwGraph [2; 3]%positive [2; 3]%positive
    (Map.of_list positive_encoding [(2, 2); (3, 3)]%positive)
    (Map.of_list positive_encoding [(2%positive, false); (3%positive, true)])
    (Map.of_list positive_encoding
      [(2%positive, (2%positive, RWNVar false 0));
       (3%positive, (3%positive, RWNApp false 0 [2]%positive))]).

Example failed_union_discards_tentative_nodes :
  rw_rep_test nat_encoding bool_encoding nat_encoding run_bad_sort_graph run_root run_source =
    true /\
  run_apply run_bad_sort_graph run_good_attempt = None /\
  (let '(added, target) :=
     rw_add nat_encoding bool_encoding nat_encoding run_bad_sort_graph run_target in
   length (rw_nodes_in added) = 3 /\ rw_union bool_encoding added run_root target = None) /\
  run_schedule (fun _ => Some run_good_attempt) 1 run_bad_sort_graph =
    RwRunResult run_bad_sort_graph RWFuelExhausted.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
