(** * Effects, resolver graphs and frame summaries

    These examples compute empty and recursive graphs, summary rows and checker results.
    For example, a quiet caller's summary becomes observable when it can call an emitting callee.
    Builds on: ViewsEffects, ViewsCalls, ViewsSummary and FixpointCheck. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls ViewsSummary.
Import List.ListNotations.

(** * Empty and recursive call graphs *)

Definition empty_calls : calls_view unit unit unit :=
  CallsView [] [] (fun _ => []) (fun _ => tt) (fun _ => tt) (fun _ => []).

Definition empty_summary : summary_spec unit unit bool :=
  SummarySpec bool_lattice (fun _ => false) (fun _ _ a => a).

Example empty_graph_and_summary :
  Graph.nodes (call_graph empty_calls (fun _ => [])) = [] /\
  Graph.entries (call_graph empty_calls (fun _ => [])) = [] /\
  Graph.out (call_graph empty_calls (fun _ => [])) tt = [] /\
  System.constraints (summary_system empty_calls (fun _ => []) empty_summary) = [] /\
  check_post bool_lattice (summary_system empty_calls (fun _ => []) empty_summary)
    (fun _ => false) = true.
Proof.
  vm_compute; auto.
Qed.

Definition call_state := (bool * list (bool * bool))%type.

Definition recursive_calls : calls_view call_state bool bool :=
  CallsView [true; false] [true] (fun f => [f]) (fun p => p) fst snd.

Definition targets (p : bool) : list bool := if p then [false; true] else [false].

Example recursive_resolver_edges :
  Graph.out (call_graph recursive_calls targets) true =
    [CallEdge true false; CallEdge true true] /\
  Graph.out (call_graph recursive_calls targets) false = [CallEdge false false] /\
  Graph.source (call_graph recursive_calls targets) (CallEdge true false) = true /\
  Graph.target (call_graph recursive_calls targets) (CallEdge true false) = false /\
  active recursive_calls (false, [(true, true); (true, true)]) = [false; true; true].
Proof.
  vm_compute; auto.
Qed.

Example recursive_call_graph_wf : graph_wf (call_graph recursive_calls targets).
Proof.
  apply call_graph_wf; cbn.
  - constructor; [intros [Hbad|[]]; discriminate|].
    constructor; [intros []|constructor].
  - intros f [<-|[]]; left; reflexivity.
  - intros f p [<-|[]]; split; [reflexivity|destruct f; cbn; auto].
  - intros [] [] Hin; cbn in *; auto.
Qed.

(** * A concrete push, local-step and return semantics *)

Inductive call_step : call_state -> list nat -> call_state -> Prop :=
  | step_local : forall f stack,
      call_step (f, stack) (if f then [] else [7]) (f, stack)
  | step_push : forall f stack g, In g (targets f) ->
      call_step (f, stack) [] (g, (f, f) :: stack)
  | step_pop : forall g f p stack,
      call_step (g, (f, p) :: stack) [] (f, stack).

Definition call_semantics : semantics call_state nat :=
  Semantics (fun s => s = (true, [])) call_step.

Example recursive_calls_laws : calls_view_laws call_semantics recursive_calls targets.
Proof.
  constructor.
  - intros f p [<-|[]]; reflexivity.
  - intros s ->; cbn; auto.
  - intros s Hreachable [] Hin; cbn; auto.
  - intros s l s' Hreachable Hstep; destruct Hstep as
      [f stack|f stack g Htarget|g f p stack].
    + left; split; reflexivity.
    + right; left; exists f; cbn; auto.
    + right; right; exists f, p; split; reflexivity.
Qed.

Definition observable_summary : summary_spec bool bool bool :=
  SummarySpec bool_lattice negb (fun _ _ a => a).

Definition observable_cover : step_cover call_state nat bool :=
  StepCover (fun a _ l _ => l = [] \/ a = true).

Example observable_summary_laws :
  summary_laws call_semantics recursive_calls observable_summary observable_cover.
Proof.
  constructor.
  - intros [] [] s l s' Hle Hcover; cbn in *; try discriminate; auto.
  - intros s l s' Hreachable Hstep; destruct Hstep as
      [f stack|f stack g Htarget|g f p stack]; cbn.
    + destruct f; cbn; auto.
    + left; reflexivity.
    + left; reflexivity.
  - intros p g a s l s' Hreachable Hframe Hcover; exact Hcover.
Qed.

Example local_and_call_rows :
  System.constraints (summary_system recursive_calls targets observable_summary) =
    [SLocal true; SLocal false; SCall true false; SCall true true; SCall false false] /\
  Query.run (System.rhs (summary_system recursive_calls targets observable_summary)
    (SLocal true)) (fun _ => true) = (false, [], []) /\
  Query.run (System.rhs (summary_system recursive_calls targets observable_summary)
    (SCall true false)) negb = (true, [false], []) /\
  deps (summary_static recursive_calls targets observable_summary) (SLocal false) = [] /\
  deps (summary_static recursive_calls targets observable_summary) (SCall true false) = [false] /\
  side_targets (summary_static recursive_calls targets observable_summary) (SCall true false) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example summary_codes :
  encode (summary_constraint_encoding bool_encoding bool_encoding) (SLocal false) =
    encode (sum_encoding bool_encoding (pair_encoding bool_encoding bool_encoding)) (inl false) /\
  encode (summary_constraint_encoding bool_encoding bool_encoding) (SCall true false) =
    encode (sum_encoding bool_encoding (pair_encoding bool_encoding bool_encoding))
      (inr (true, false)).
Proof.
  vm_compute; auto.
Qed.

Example summary_checker_accepts_and_rejects :
  check_post bool_lattice (summary_system recursive_calls targets observable_summary)
    (fun _ => true) = true /\
  check_post bool_lattice (summary_system recursive_calls targets observable_summary) negb = false.
Proof.
  vm_compute; auto.
Qed.

Example recursive_stack_reachable :
  reachable_state call_semantics (false, [(true, true); (true, true)]).
Proof.
  exists (true, []), []; split; [reflexivity|].
  eapply exec_step with (l := []) (tr := []) (s' := (true, [(true, true)])).
  - apply step_push; cbn; auto.
  - eapply exec_step with (l := []) (tr := [])
      (s' := (false, [(true, true); (true, true)])).
    + apply step_push; cbn; auto.
    + constructor.
Qed.

Example suspended_caller_covers_callee_event :
  step_covers observable_cover true (false, [(true, true); (true, true)]) [7]
    (false, [(true, true); (true, true)]).
Proof.
  apply (summary_sound call_semantics recursive_calls targets observable_summary observable_cover
    (fun _ => true) recursive_calls_laws observable_summary_laws) with (f := true).
  - apply check_post_iff; vm_compute; reflexivity.
  - exact recursive_stack_reachable.
  - apply step_local.
  - cbn; auto.
Qed.

Example active_callee_reachable_in_graph : reachable (call_graph recursive_calls targets) false.
Proof.
  apply (active_reachable_in_call_graph call_semantics recursive_calls targets recursive_calls_laws
    (false, [(true, true); (true, true)]) recursive_stack_reachable false).
  left; reflexivity.
Qed.

(** * Non-observing finite execution *)

Definition quiet_semantics : semantics nat nat :=
  Semantics (fun s => s = 2) (fun s l t => s = Datatypes.S t /\ l = []).

Definition quiet_endings : endings nat :=
  Endings (fun s => s = 0) (fun _ => False) (fun _ => False).

Definition quiet_effects : effects unit :=
  Effects (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false).

Definition quiet_view : effects_view nat unit unit :=
  EffectsView (fun _ => Some tt) (fun _ => tt) eq (fun _ => 0).

Example quiet_effects_laws : effects_laws quiet_semantics quiet_endings quiet_effects quiet_view.
Proof.
  constructor.
  - intros s l s' i Hreachable Hinstr [_ Htrace] Hflag; exact Htrace.
  - intros s i Hreachable Hinstr Htrap; exfalso; exact Htrap.
  - intros s i Hreachable Hinstr Hstop; exfalso; exact Hstop.
  - intros s l s' i Hreachable Hinstr Hstep Hwrite Halloc Hfree; reflexivity.
  - intros s l s' t i Hreachable Hinstr Hstep Hread Heq; cbn in Heq; subst t.
    exists s'; split; [exact Hstep|reflexivity].
  - intros s t i Hs Ht His Hit Hread Heq; split; intro Hbad; exact Hbad.
  - intros s t i Hs Ht His Hit Hread Heq; split; intro Hbad; exact Hbad.
  - intros s l s' i Hreachable Hinstr Hstep Hcall; reflexivity.
  - intros s l s' i Hreachable Hinstr Hstep Hcall; discriminate Hcall.
Qed.

Example quiet_two_step_run : exec_in quiet_semantics (fun _ => True) 2 [] 0.
Proof.
  eapply exec_in_step with (l := []) (tr := []) (s' := 1).
  - exact I.
  - split; reflexivity.
  - eapply exec_in_step with (l := []) (tr := []) (s' := 0).
    + exact I.
    + split; reflexivity.
    + constructor; exact I.
Qed.

Example quiet_run_has_empty_trace : forall tr,
  exec_in quiet_semantics (fun _ => True) 2 tr 0 -> tr = [].
Proof.
  intros tr Hrun; eapply silent_exec_in; [exact quiet_effects_laws| |exact Hrun|].
  - exists 2, []; split; [reflexivity|constructor].
  - intros t HP Hrunning; exists tt; split; reflexivity.
Qed.

Example quiet_flags_and_heap :
  observes quiet_effects tt = false /\ calls quiet_effects tt = false /\
  heap quiet_view 2 = heap quiet_view 0 /\ depth quiet_view 2 = depth quiet_view 0.
Proof.
  vm_compute; auto.
Qed.
