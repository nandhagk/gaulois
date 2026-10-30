(** * Whole-program SSA call analysis clients

    These wrappers connect generic call summaries to the actual SSA frame machine.
    For example, call-graph unreachability excludes a function from every active SSA stack.
    Builds on: ExamplesSsaAnalysisBase, ExamplesSsaEffects and AnalysesCalls. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesCalls.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaEffects ExamplesSsaAnalysisBase.
Import List.ListNotations.

Lemma calls_ssa_resolver_listed ext P : wf_program ext P ->
  forall p target, In target (ssa_resolver P p) -> In target (map fst (funcs P)).
Proof.
  intros Hwf [f l] target Hin; unfold ssa_resolver in Hin; cbn [fst snd] in Hin.
  rewrite Map.get_map in Hin.
  change (Map.get nat_encoding f (first_index (funcs P))) with (find_func P f) in Hin.
  destruct (find_func P f) as [fd|] eqn:Hfunction; cbn [option_map] in Hin;
    [|contradiction].
  rewrite Map.get_map in Hin.
  change (Map.get nat_encoding l (first_index (blocks fd))) with (find_block fd l) in Hin.
  destruct (find_block fd l) as [b|] eqn:Hblock; cbn [option_map] in Hin;
    [|contradiction].
  destruct (bterm b) as [next args|x yes ya no na|x cases default args|callee args cont|x]
    eqn:Hterm; try contradiction.
  destruct callee as [g|x ps result].
  - destruct Hin as [<-|[]].
    pose proof (proj1 (proj2 (proj2
      (wf_block ext P f fd l b Hwf Hfunction Hblock)))) as Htyped.
    rewrite Hterm in Htyped.
    cbn [term_typed callee_sig callee_sig_with] in Htyped.
    unfold entry_sig in Htyped; rewrite Map.get_map in Htyped.
    change (Map.get nat_encoding g (first_index (funcs P))) with (find_func P g) in Htyped.
    destruct (find_func P g) as [callee_fd|] eqn:Hcallee; [|contradiction].
    apply in_map_iff; exists (g, callee_fd); split; [reflexivity|].
    apply first_index_sound; exact Hcallee.
  - rewrite ssa_signature_groups_agrees in Hin.
    apply in_map_iff in Hin; destruct Hin as [[g callee_fd] [Heq Hfiltered]].
    cbn in Heq; subst target; apply filter_In in Hfiltered.
    apply in_map_iff; exists (g, callee_fd); split; [reflexivity|exact (proj1 Hfiltered)].
Qed.

Lemma calls_ssa_graph_wf ext P (lim : limits) : wf_program ext P ->
  graph_wf (call_graph (ssa_calls ext P) (ssa_resolver P)).
Proof.
  intro Hwf; constructor.
  - exact (proj1 (proj2 Hwf)).
  - intros f [<-|[]]; cbn [call_graph ssa_calls].
    destruct (proj1 Hwf) as [fd Hmain].
    apply in_map_iff; exists (main P, fd); split; [reflexivity|].
    apply first_index_sound; exact Hmain.
  - intros f [p g] Hin; cbn [call_graph] in Hin |- *.
    apply in_flat_map in Hin; destruct Hin as [q [Hq Hin]].
    apply in_map_iff in Hin; destruct Hin as [target [Heq Htarget]].
    inversion Heq; subst q target; cbn.
    exact (sites_caller (ssa_calls_laws ext P lim Hwf) f p Hq).
  - intros f [p g] Hf Hin; cbn [call_graph] in Hin |- *.
    apply in_flat_map in Hin; destruct Hin as [q [Hq Hin]].
    apply in_map_iff in Hin; destruct Hin as [target [Heq Htarget]].
    inversion Heq; subst q target; cbn.
    exact (calls_ssa_resolver_listed ext P Hwf p g Htarget).
Qed.

(** A false SSA purity summary guarantees silence and an unchanged concrete heap. *)
Theorem ssa_summary_sound (ext : nat -> list cval -> option cval) (P : program) (lim : limits)
    (impure_local : func -> bool) (sigma : func -> bool) :
  wf_program ext P ->
  summary_laws (ssa_semantics ext P lim) (ssa_calls ext P)
    (purity_spec (ssa_calls ext P) impure_local) (purity_cover (ssa_effects_view ext P lim)) ->
  post_solution bool_lattice
    (summary_system (ssa_calls ext P) (ssa_resolver P)
      (purity_spec (ssa_calls ext P) impure_local)) sigma ->
  forall s l s' g, reachable_state (ssa_semantics ext P lim) s ->
    step (ssa_semantics ext P lim) s l s' -> In g (active (ssa_calls ext P) s) ->
    sigma g = false ->
    l = nil /\ heap (ssa_effects_view ext P lim) s' = heap (ssa_effects_view ext P lim) s.
Proof.
  intros Hwf Hsummary Hpost.
  apply (purity_sound (ssa_semantics ext P lim) (ssa_calls ext P) (ssa_resolver P)
    (ssa_effects_view ext P lim) impure_local sigma); [apply ssa_calls_laws; exact Hwf| |];
    assumption.
Qed.

Section SsaAnalysisWrappers.
Context (ext : nat -> list cval -> option cval) (P : program) (lim : limits).
Local Abbreviation m := (ssa_semantics ext P lim).
Local Abbreviation cv := (ssa_calls ext P).
Local Abbreviation resolve := (ssa_resolver P).

(** Repeated SSA activations imply a real cycle in the resolved call graph. *)
Theorem ssa_recursion_sound (s : state) :
  wf_program ext P -> reachable_state m s -> ~ NoDup (active cv s) ->
  exists f, In f (active cv s) /\ recursive (call_graph cv resolve) f.
Proof.
  intro Hwf; apply (recursive_sound nat_encoding m cv resolve s).
  apply ssa_calls_laws; exact Hwf.
Qed.

(** A function unreachable from main cannot occur in any reachable SSA stack. *)
Theorem ssa_unreachable_sound (f : func) :
  wf_program ext P -> ~ reachable (call_graph cv resolve) f ->
  forall s, reachable_state m s -> ~ In f (active cv s).
Proof.
  intro Hwf; apply (unreachable_never_runs m cv resolve f).
  apply ssa_calls_laws; exact Hwf.
Qed.

(** Finite SSA stack demand bounds every actual active prefix for an arbitrary query function. *)
Theorem ssa_stack_demand_sound (fw : frame_weights func) (f : func) (d : nat) :
  wf_program ext P -> stack_demand nat_encoding cv (call_graph cv resolve) fw f = Some d ->
  forall s, reachable_state m s -> In f (active cv s) ->
    stack_above nat_encoding cv fw f s <= d.
Proof.
  intro Hwf; apply (stack_demand_sound nat_encoding m cv resolve fw f d).
  - apply ssa_calls_laws; exact Hwf.
  - apply (calls_ssa_graph_wf ext P lim); exact Hwf.
Qed.

(** An SSA leaf step preserves the suspended stack or returns to its caller. *)
Theorem ssa_callee_leaf_sound (f : func) :
  wf_program ext P -> callee_leaf cv f = true ->
  forall s l s', reachable_state m s -> here cv s = f -> step m s l s' ->
    frames cv s' = frames cv s \/ exists g p, frames cv s = (g, p) :: frames cv s'.
Proof.
  intro Hwf; apply (callee_leaf_sound m cv resolve f).
  apply ssa_calls_laws; exact Hwf.
Qed.

End SsaAnalysisWrappers.
