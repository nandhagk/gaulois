(** * Executable SSA PRE realization and boundary checks

    The client proves complete local laws and behavior while retaining both historical diagnostics.
    For example, delayed target choice admits complete macros but no stuttering match.
    Builds on: Analyses16Test, AnalysesSsaPre and AnalysesSsaPreSemantics. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesAvailable AnalysesSsaPreGraph AnalysesSsaPre
  AnalysesSsaPreSemantics AnalysesSsaLiveQuery.
From Gaulois.Tests.Analyses Require Import Analyses16Test.
Import List.ListNotations.

Definition pre_frame_state := (pre_test_block * pre_test_stage)%type.

(** The six-step prefix stops immediately before the left branch's second evaluation. *)
Inductive pre_frame_step : pre_frame_state -> list unit -> pre_frame_state -> Prop :=
  | pre_frame_bind_entry : pre_frame_step (PreEntry, PreBefore) [] (PreEntry, PreBody)
  | pre_frame_compute_entry : pre_frame_step (PreEntry, PreBody) [] (PreEntry, PreBetween)
  | pre_frame_again_entry : pre_frame_step (PreEntry, PreBetween) [] (PreEntry, PreAfter)
  | pre_frame_enter_left : pre_frame_step (PreEntry, PreAfter) [] (PreLeft, PreBefore)
  | pre_frame_bind_left : pre_frame_step (PreLeft, PreBefore) [] (PreLeft, PreBody)
  | pre_frame_compute_left : pre_frame_step (PreLeft, PreBody) [] (PreLeft, PreBetween).

Definition pre_frame_semantics : semantics pre_frame_state unit :=
  Semantics (fun s => s = (PreEntry, PreBefore)) pre_frame_step.

Definition pre_frame_endings : endings pre_frame_state :=
  Endings (fun _ => False) (fun _ => False) (fun _ => False).

Definition pre_frame_graph : graph_view pre_frame_state unit pre_frame_state pre_test_edge :=
  GraphView pre_test_points (fun s => s)
    (fun s _ s' e => Graph.source pre_test_points e = s /\
      In e (Graph.out pre_test_points s) /\ Graph.target pre_test_points e = s')
    (fun _ _ _ => False).

(** All bindings change from zero to one at the last transition, despite its empty defs list. *)
Definition pre_frame_value (s : pre_frame_state) : nat :=
  match s with
  | (PreLeft, PreBetween) => 1
  | _ => 0
  end.

Definition pre_frame_eval (s : pre_frame_state) (_ : pre_test_value) : option nat :=
  Some (S (pre_frame_value s)).

Definition pre_frame_ssa_view : ssa_view pre_frame_state unit pre_test_block
    pre_test_block_edge pre_test_value unit nat :=
  SsaView (GraphView pre_test_blocks fst (fun _ _ _ _ => False) (fun _ _ _ => False))
    (def pre_test_view) (home pre_test_view) (params pre_test_view) (edge_args pre_test_view)
    (edge_guard pre_test_view) (fun s _ => Some (pre_frame_value s))
    (op_eval pre_test_view) (truth pre_test_view).

(** The original full-law syntax is unchanged while the runtime valuation is state dependent. *)
Definition pre_frame_expression : pre_expr_ssa pre_frame_state unit pre_test_block
    pre_test_block_edge pre_frame_state pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_ssa pre_frame_ssa_view
    (PreExpressionView
      (GenKillView pre_frame_graph (gen (pre_genkill (pre_expression pre_test_expression)))
        (kill (pre_genkill (pre_expression pre_test_expression))) pre_frame_eval)
      (fun _ => true) pre_test_occurrence)
    [PreX; PreY; PreZ] [PreX; PreY; PreZ] (fun _ => 1%positive) (fun x => [x])
    (fun x env => option_map S (env x)) (fun be x => Some (pre_test_translate be x))
    (fun _ => false) (fun _ => true).

(** Every adopted expression-SSA premise permits this varying runtime valuation. *)
Example pre_frame_expression_laws :
  pre_expr_ssa_laws pre_test_value_encoding pre_frame_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - exact (pre_expr_reachable_blocks _ _ pre_test_expression_laws).
  - exact (pre_expr_reachable_points _ _ pre_test_expression_laws).
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - exact (pre_expr_entry_no_incoming _ _ pre_test_expression_laws).
  - exact (pre_expr_params_nodup _ _ pre_test_expression_laws).
  - exact (pre_expr_value_nodup _ _ pre_test_expression_laws).
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; destruct u; cbn; tauto|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u (or_introl eq_refl)); reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    destruct e as [b|b|b|be], u; try destruct b;
      cbn in Hkill |- *; intuition congruence.
  - exact (pre_expr_def_home _ _ pre_test_expression_laws).
  - exact (pre_expr_cross_no_defs _ _ pre_test_expression_laws).
  - exact (pre_expr_real_internal _ _ pre_test_expression_laws).
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
Qed.

(** This legal sequential reload selects the first left computation. *)
Definition pre_frame_plan : pre_plan pre_test_edge pre_test_value :=
  PrePlan Map.empty
    (Map.set pre_test_edge_encoding (PreAgain PreLeft)
      (FinSet.of_list pre_test_value_encoding [PreX]) Map.empty)
    (Map.set pre_test_edge_encoding (PreAgain PreLeft)
      (PreComputed (PreCompute PreLeft) PreX) Map.empty) Map.empty.

(** The only cache write stores the kept computation's prescribed pre-state value. *)
Definition pre_frame_cached (s : pre_frame_state)
    (version : pre_version pre_test_edge pre_test_value) : option nat :=
  match s, version with
  | (PreLeft, PreBetween), PreComputed (PreCompute PreLeft) PreX => Some 1
  | _, _ => None
  end.

Definition pre_frame_realizer : pre_realizer pre_frame_state unit pre_frame_state pre_test_edge
    pre_frame_state pre_test_edge pre_test_value nat :=
  PreRealizer pre_frame_semantics pre_frame_endings pre_frame_graph
    (fun _ => pre_frame_semantics) (fun _ => pre_frame_endings) (fun _ => pre_frame_graph)
    (fun _ n => PrePoint n) (fun _ e => Some e) pre_frame_eval pre_frame_cached eq
    (fun _ _ => 0).

Local Lemma pre_frame_inserted : forall e u,
  pre_inserted pre_test_edge_encoding pre_test_value_encoding pre_frame_plan e u = false.
Proof.
  intros e u; unfold pre_inserted, live_index_get; cbn [pre_frame_plan pre_insertions].
  rewrite Map.get_empty; apply FinSet.mem_empty.
Qed.

(** The source's stopping point is explicitly covered, including its stuck ending. *)
Example pre_frame_exit_covered : pre_exit_covered pre_frame_expression pre_frame_realizer.
Proof.
  intros s k Hreachable Hending; reflexivity.
Qed.

Local Lemma pre_frame_deleted : forall e u,
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_frame_plan e u = true <->
  e = PreAgain PreLeft /\ u = PreX.
Proof.
  intros e u; destruct e as [b|b|b|be], u; try destruct b; try destruct be;
    vm_compute; intuition congruence.
Qed.

(** The reload is legal because its defining target is exactly the reload's source. *)
Example pre_frame_plan_legal :
  pre_placement_legal pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_frame_expression) pre_frame_plan.
Proof.
  split.
  - intros e u He Hinsert; rewrite pre_frame_inserted in Hinsert; discriminate.
  - intros e u He Hdelete; apply pre_frame_deleted in Hdelete; destruct Hdelete as [-> ->].
    split; [reflexivity|]; split; [reflexivity|].
    exists (PreComputed (PreCompute PreLeft) PreX), (PreLeft, PreBetween).
    split; [reflexivity|]; split; [reflexivity|apply dominates_refl].
Qed.

(** A reachable source edge changes the expression despite its syntactic non-killing flag. *)
Example pre_frame_nonkill_changes_value :
  pre_frame_step (PreLeft, PreBody) [] (PreLeft, PreBetween) /\
  kill (pre_genkill (pre_expression pre_frame_expression)) (PreCompute PreLeft) PreX = false /\
  pre_frame_eval (PreLeft, PreBody) PreX <> pre_frame_eval (PreLeft, PreBetween) PreX.
Proof.
  split; [constructor|]; split; [reflexivity|discriminate].
Qed.

Local Lemma pre_frame_edges : forall s l s', pre_frame_step s l s' ->
  exists e, taken pre_frame_graph s l s' e.
Proof.
  intros s l s' Hstep; destruct Hstep.
  - exists (PreBind PreEntry); cbn; tauto.
  - exists (PreCompute PreEntry); cbn; tauto.
  - exists (PreAgain PreEntry); cbn; tauto.
  - exists (PreCross PreToLeft); cbn; tauto.
  - exists (PreBind PreLeft); cbn; tauto.
  - exists (PreCompute PreLeft); cbn; tauto.
Qed.

Local Lemma pre_frame_graph_laws : graph_view_laws pre_frame_semantics pre_frame_graph.
Proof.
  constructor.
  - exact pre_test_points_wf.
  - intros s Hinitial; change (s = (PreEntry, PreBefore)) in Hinitial; subst s; cbn; tauto.
  - intros s l s' Hreach Hstep; right; apply pre_frame_edges; exact Hstep.
  - intros s l s' e Hreach Hstep [Hsource [Hout Htarget]]; split; assumption.
  - intros s l s' Hreach Hstep Hstays; contradiction.
Qed.

Local Lemma pre_frame_no_admin : forall p e t, ~ pre_admin pre_frame_realizer p e t.
Proof.
  intros p e t [k Horigin]; discriminate.
Qed.

Local Lemma pre_frame_finish_same : forall p e s t,
  pre_finish pre_frame_realizer p e s t -> s = t.
Proof.
  intros p e s t Hfinish; destruct Hfinish.
  - reflexivity.
  - exfalso; eapply pre_frame_no_admin; eassumption.
Qed.

Local Lemma pre_frame_macro : forall p e s l s',
  pre_macro_step pre_frame_realizer p e s l s' <->
  pre_frame_step s l s' /\ taken pre_frame_graph s l s' e.
Proof.
  intros p e s l s'; split.
  - intros [Hboundary [t1 [te [Hstep [Htaken [Hproject Hfinish]]]]]].
    apply pre_frame_finish_same in Hfinish; subst t1.
    cbn in Hproject; inversion Hproject; subst te; split; assumption.
  - intros [Hstep Htaken]; destruct Htaken as [Hsource [Hout Htarget]].
    split.
    + change (PrePoint s = @PrePoint pre_frame_state pre_test_edge
        (Graph.source pre_test_points e)); rewrite Hsource; reflexivity.
    + exists s', e; split; [exact Hstep|]; split.
      * split; [exact Hsource|]; split; assumption.
      * split; [reflexivity|]; apply pre_finish_boundary.
        change (PrePoint s' = @PrePoint pre_frame_state pre_test_edge
          (Graph.target pre_test_points e)); rewrite Htarget; reflexivity.
Qed.

Local Lemma pre_frame_match : forall p s t e,
  pre_core_agree pre_frame_realizer s t ->
  (forall l s', pre_frame_step s l s' -> taken pre_frame_graph s l s' e ->
    exists t', pre_macro_step pre_frame_realizer p e t l t' /\ s' = t') /\
  (forall l t', pre_macro_step pre_frame_realizer p e t l t' ->
    exists s', pre_frame_step s l s' /\ taken pre_frame_graph s l s' e /\ s' = t').
Proof.
  intros p s t e Heq; change (s = t) in Heq; subst t; split.
  - intros l s' Hstep Htaken; exists s'; split; [apply pre_frame_macro; tauto|reflexivity].
  - intros l t' Hmacro; apply pre_frame_macro in Hmacro; exists t'; tauto.
Qed.

Local Lemma pre_frame_taken_unique : forall s l s' e,
  pre_frame_step s l s' -> taken pre_frame_graph s l s' e ->
  match s with
  | (PreEntry, PreBefore) => e = PreBind PreEntry
  | (PreEntry, PreBody) => e = PreCompute PreEntry
  | (PreEntry, PreBetween) => e = PreAgain PreEntry
  | (PreEntry, PreAfter) => e = PreCross PreToLeft
  | (PreLeft, PreBefore) => e = PreBind PreLeft
  | (PreLeft, PreBody) => e = PreCompute PreLeft
  | _ => False
  end.
Proof.
  intros s l s' e Hstep [Hsource [Hout Htarget]]; destruct Hstep; cbn in Hout |- *;
    intuition subst; try reflexivity; discriminate.
Qed.

Local Lemma pre_frame_phi_update : forall incoming parameter
    (old : pre_version pre_test_edge pre_test_value -> option nat) version,
  pre_phi_update pre_test_edge_encoding pre_test_value_encoding pre_frame_plan
    incoming parameter old version = old version.
Proof.
  intros incoming parameter old version; destruct version; cbn [pre_phi_update pre_frame_plan];
    try reflexivity.
  destruct (Pos.eqb (encode pre_test_edge_encoding parameter_edge)
    (encode pre_test_edge_encoding parameter)); [|reflexivity].
  change (match Map.get (pair_encoding
      (pair_encoding pre_test_edge_encoding pre_test_edge_encoding) pre_test_value_encoding)
      ((parameter_edge, incoming), u) Map.empty with
    | Some selected => old selected
    | None => old (PreMerged parameter_edge u)
    end = old (PreMerged parameter_edge u)).
  rewrite Map.get_empty; reflexivity.
Qed.

Local Lemma pre_frame_cached_frame : forall s e l s' version,
  pre_frame_step s l s' -> taken pre_frame_graph s l s' e ->
  pre_version_written pre_test_edge_encoding e version = false ->
  pre_frame_cached s' version = pre_frame_cached s version.
Proof.
  intros s e l s' version Hstep Htaken Hwritten.
  pose proof (pre_frame_taken_unique _ _ _ _ Hstep Htaken) as Hedge.
  destruct Hstep; cbn in Hedge; subst e; destruct version as [u|d u|d u|d u];
    try reflexivity.
  all: destruct d as [b|b|b|be]; try destruct b; try destruct be;
    destruct u; cbn in Hwritten |- *; try reflexivity; discriminate.
Qed.

Local Lemma pre_frame_cached_compute : forall s e l s' u,
  pre_frame_step s l s' -> taken pre_frame_graph s l s' e ->
  pre_test_occurrence e = Some u ->
  pre_frame_cached s' (PreComputed e u) = pre_frame_eval s u.
Proof.
  intros s e l s' u Hstep Htaken Hcomputed.
  pose proof (pre_frame_taken_unique _ _ _ _ Hstep Htaken) as Hedge.
  destruct Hstep; cbn in Hedge; subst e; cbn in Hcomputed; try discriminate.
  inversion Hcomputed; subst u; reflexivity.
Qed.

Local Lemma pre_frame_phi_cache : forall be incoming s0 l0 s1 l1 s2 version,
  Map.get pre_test_block_edge_encoding be
    (pre_point_edge_index pre_test_block_edge_encoding pre_test_ssa) = Some incoming ->
  pre_frame_step s0 l0 s1 -> taken pre_frame_graph s0 l0 s1 incoming ->
  pre_frame_step s1 l1 s2 -> pre_frame_cached s2 version = pre_frame_cached s1 version.
Proof.
  intros be incoming s0 l0 s1 l1 s2 version Hindex Hstep Htaken Hparameter.
  pose proof (pre_frame_taken_unique _ _ _ _ Hstep Htaken) as Hedge.
  destruct Hstep; cbn in Hedge; subst incoming; destruct be; cbn in Hindex;
    try discriminate.
  inversion Hparameter; reflexivity.
Qed.

(** C48's new source generation field is an independent obligation for this old fixture. *)
Definition pre_frame_source_gen_value : Prop :=
  forall s l s' e u, reachable_state pre_frame_semantics s -> pre_frame_step s l s' ->
    taken pre_frame_graph s l s' e ->
    In u (gen (pre_genkill (pre_expression pre_frame_expression)) e) ->
    pre_frame_eval s' u = pre_frame_eval s u.

(** C48's non-kill field rules out the old fixture's mutation on its last step. *)
Definition pre_frame_source_kill_frame : Prop :=
  forall s l s' e u, reachable_state pre_frame_semantics s -> pre_frame_step s l s' ->
    taken pre_frame_graph s l s' e ->
    kill (pre_genkill (pre_expression pre_frame_expression)) e u = false ->
    pre_frame_eval s' u = pre_frame_eval s u.

(** All historical fields still hold, separately from the two newly required source frames. *)
Example pre_frame_local_laws_if_frames :
  pre_frame_source_gen_value -> pre_frame_source_kill_frame ->
  pre_local_laws pre_test_block_edge_encoding pre_test_point_encoding pre_test_edge_encoding
    pre_test_value_encoding pre_test_value_encoding pre_frame_expression
    (pre_expression pre_frame_expression) (pre_initial_available pre_frame_expression)
    pre_frame_realizer pre_frame_plan.
Proof.
  intros Hgen_value Hkill_frame.
  constructor.
  - split; [reflexivity|]; split; [reflexivity|].
    split; [exact pre_frame_graph_laws|]; split; [exact pre_frame_graph_laws|].
    split; [intros s l s' Hfalse; exact Hfalse|].
    split; [intros s l s' Hfalse; exact Hfalse|].
    intros s l s' Hreach Hstep; destruct (pre_frame_edges _ _ _ Hstep) as [e Htaken].
    exists e; split; [exact Htaken|]; cbn; exists e; split; [reflexivity|].
    destruct Htaken as [Hsource [Hout Htarget]]; split; [exact Hout|].
    left; change (PrePoint s' = @PrePoint pre_frame_state pre_test_edge
      (Graph.target pre_test_points e)); rewrite Htarget; reflexivity.
  - split; [reflexivity|]; split.
    + intros s t u Heq; change (s = t) in Heq; subst t; reflexivity.
    + split.
      * intros s u Hreach Hpure; exists (S (pre_frame_value s)); reflexivity.
      * intros e u Hcomputed; change (pre_test_occurrence e = Some u) in Hcomputed.
        change (In u (match pre_test_occurrence e with Some x => [x] | None => [] end)).
        rewrite Hcomputed; left; reflexivity.
  - exact Hgen_value.
  - exact Hkill_frame.
  - intros s t e Hs Ht Hpoint Hboundary Hagree Hdeleted; apply pre_frame_match; exact Hagree.
  - intros s t e u l s' t' Hs Ht Hagree Hinsert.
    rewrite pre_frame_inserted in Hinsert; discriminate.
  - intros s t e u version Hs Ht Hpoint Hboundary Hagree Hdeleted Hreload Hcache.
    apply pre_frame_match; exact Hagree.
  - intros s t e l s' t' version Hs Ht Hpoint Hboundary Hstep Htaken Hmacro Hwritten.
    apply pre_frame_macro in Hmacro; destruct Hmacro as [Htstep Httaken].
    eapply pre_frame_cached_frame; eassumption.
  - intros s t e u l s' t' Hs Ht Hcomputed Hdeleted Hstep Htaken Hmacro.
    apply pre_frame_macro in Hmacro; destruct Hmacro as [Htstep Httaken].
    assert (s = t) as ->.
    { destruct Htaken as [Hsource _], Httaken as [Htsource _]; congruence. }
    eapply pre_frame_cached_compute; eassumption.
  - intros s t u Hs Ht Hagree Hinitial; discriminate.
  - intros s0 t0 s1 t1 s2 t2 be incoming l0 l version Hs Ht Hindex
      Hstep Htaken Hmacro Hparameter Hparameter_taken Hparameter_macro.
    apply pre_frame_macro in Hmacro; destruct Hmacro as [Htstep Httaken].
    apply pre_frame_macro in Hparameter_macro;
      destruct Hparameter_macro as [Htparameter Httparameter].
    rewrite pre_frame_phi_update; eapply pre_frame_phi_cache; eassumption.
  - intros t e Hreach Hadmin; exfalso; eapply pre_frame_no_admin; exact Hadmin.
  - intros s t n k Hs Ht Hpoint Hboundary Hagree.
    change (s = t) in Hagree; subst t; reflexivity.
Qed.

(** The sole reachable block transfer and its parameter step obey actual phi substitution. *)
Example pre_frame_phi_source_laws :
  pre_phi_source_laws pre_test_block_edge_encoding pre_test_value_encoding
    pre_frame_expression pre_frame_realizer.
Proof.
  intros be e s0 l0 s1 l1 s2 Hreachable Hindex Hstep Htaken Hparameter Hparameter_taken x.
  pose proof (pre_frame_taken_unique _ _ _ _ Hstep Htaken) as Hedge.
  destruct Hstep; cbn in Hedge; subst e; destruct be; cbn in Hindex; try discriminate.
  inversion Hparameter; subst s2 l1; reflexivity.
Qed.

Local Lemma pre_frame_pair_step : forall s s' l,
  pre_paired_run pre_frame_realizer pre_frame_plan (PreEntry, PreBefore)
    (PreEntry, PreBefore) s s -> pre_frame_step s l s' ->
  pre_paired_run pre_frame_realizer pre_frame_plan (PreEntry, PreBefore)
    (PreEntry, PreBefore) s' s'.
Proof.
  intros s s' l Hpaired Hstep; destruct (pre_frame_edges _ _ _ Hstep) as [e Htaken].
  eapply pre_paired_step with (e := e) (l := l).
  - exact Hpaired.
  - exact Hstep.
  - exact Htaken.
  - apply pre_frame_macro; split; assumption.
  - reflexivity.
Qed.

(** The bad reload boundary is reached by a complete pair of six ordinary original edges. *)
Example pre_frame_paired_run :
  pre_paired_run pre_frame_realizer pre_frame_plan (PreEntry, PreBefore)
    (PreEntry, PreBefore) (PreLeft, PreBetween) (PreLeft, PreBetween).
Proof.
  eapply pre_frame_pair_step with (s := (PreLeft, PreBody)); [|constructor].
  eapply pre_frame_pair_step with (s := (PreLeft, PreBefore)); [|constructor].
  eapply pre_frame_pair_step with (s := (PreEntry, PreAfter)); [|constructor].
  eapply pre_frame_pair_step with (s := (PreEntry, PreBetween)); [|constructor].
  eapply pre_frame_pair_step with (s := (PreEntry, PreBody)); [|constructor].
  eapply pre_frame_pair_step with (s := (PreEntry, PreBefore)); [|constructor].
  apply pre_paired_initial; reflexivity.
Qed.

(** The initial pair satisfies the complete requested cache relation. *)
Example pre_frame_initial_cache :
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_frame_expression) pre_frame_realizer pre_frame_plan
    (PreEntry, PreBefore) (PreEntry, PreBefore) (PreEntry, PreBefore).
Proof.
  split; [reflexivity|]; intros e u version Hsource Hdeleted Hreload.
  apply pre_frame_deleted in Hdeleted; destruct Hdeleted as [-> ->]; discriminate.
Qed.

(** The historical mutation leaves the demanded cache relation false at the reload boundary. *)
Example pre_frame_cache_invariant_fails :
  ~ pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
      (pre_expression pre_frame_expression) pre_frame_realizer pre_frame_plan
      (PreLeft, PreBetween) (PreLeft, PreBetween) (PreLeft, PreBetween).
Proof.
  intros [Hcore Hcache].
  specialize (Hcache (PreAgain PreLeft) PreX (PreComputed (PreCompute PreLeft) PreX)
    eq_refl eq_refl eq_refl).
  discriminate.
Qed.

(** The actual FRG classifies both left evaluations as the same fresh reaching version. *)
Example pre_frame_actual_frg_reuse :
  let f := build_frg pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_frame_expression in
  Map.get pre_test_edge_encoding (PreCompute PreLeft) (frg_occurrence_index f) =
    Some (FrFresh (PreCompute PreLeft) PreX) /\
  Map.get pre_test_edge_encoding (PreAgain PreLeft) (frg_occurrence_index f) =
    Some (FrFresh (PreCompute PreLeft) PreX).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The semantic countermodel still supplies every premise of the actual FRG producer theorem. *)
Example pre_frame_actual_frg_wf :
  frg_wf pre_test_block_encoding pre_test_block_edge_encoding pre_test_point_encoding
    pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding pre_frame_expression
    (build_frg pre_test_block_encoding pre_test_block_edge_encoding pre_test_point_encoding
      pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding pre_frame_expression).
Proof.
  apply build_frg_wf.
  - exact pre_frame_expression_laws.
  - exact pre_test_blocks_ready.
  - exact pre_test_points_ready.
Qed.

Local Lemma pre_frame_reachable_compute :
  reachable_state pre_frame_semantics (PreLeft, PreBody).
Proof.
  exists (PreEntry, PreBefore), []; split; [reflexivity|].
  eapply exec_step with (l := []) (tr := []) (s' := (PreEntry, PreBody)); [constructor|].
  eapply exec_step with (l := []) (tr := []) (s' := (PreEntry, PreBetween)); [constructor|].
  eapply exec_step with (l := []) (tr := []) (s' := (PreEntry, PreAfter)); [constructor|].
  eapply exec_step with (l := []) (tr := []) (s' := (PreLeft, PreBefore)); [constructor|].
  eapply exec_step with (l := []) (tr := []) (s' := (PreLeft, PreBody));
    [constructor|apply exec_refl].
Qed.

(** The omitted source gen/kill semantic premise rules out exactly this countermodel. *)
Example pre_frame_genkill_laws_fail :
  ~ genkill_laws pre_frame_semantics pre_frame_endings
      (pre_genkill (pre_expression pre_frame_expression)).
Proof.
  intro Hlaws.
  pose proof (kill_frame Hlaws (PreLeft, PreBody) [] (PreLeft, PreBetween)
    (PreCompute PreLeft) PreX pre_frame_reachable_compute pre_frame_compute_left
    (conj eq_refl (conj (or_introl eq_refl) eq_refl)) eq_refl) as Hvalue.
  discriminate.
Qed.

(** The current C48 local record rejects the historical source mutation through kill-frame. *)
Example pre_frame_current_local_laws_fail :
  ~ pre_local_laws pre_test_block_edge_encoding pre_test_point_encoding pre_test_edge_encoding
      pre_test_value_encoding pre_test_value_encoding pre_frame_expression
      (pre_expression pre_frame_expression) (pre_initial_available pre_frame_expression)
      pre_frame_realizer pre_frame_plan.
Proof.
  intro Hlaws.
  pose proof (pre_local_kill_frame _ _ _ _ _ _ _ _ _ _ Hlaws
    (PreLeft, PreBody) [] (PreLeft, PreBetween) (PreCompute PreLeft) PreX
    pre_frame_reachable_compute pre_frame_compute_left
    (conj eq_refl (conj (or_introl eq_refl) eq_refl)) eq_refl) as Hvalue.
  discriminate.
Qed.

(** * A choice delayed until target administration

    The source chooses an ending on its visible edge. The target emits the same event,
    then chooses its ending silently. Complete macros agree, while early commitment to
    either source successor cannot follow every target administrative choice. *)

Inductive pre_choice_state : Type :=
  | ChoiceSourceStart
  | ChoiceSourceFinal
  | ChoiceSourceTrap
  | ChoiceTargetStart
  | ChoiceTargetAdmin
  | ChoiceTargetFinal
  | ChoiceTargetTrap.

(** The source's single original edge can either finish or trap after the same event. *)
Inductive pre_choice_source_step : pre_choice_state -> list unit -> pre_choice_state -> Prop :=
  | choice_source_final :
      pre_choice_source_step ChoiceSourceStart [tt] ChoiceSourceFinal
  | choice_source_trap :
      pre_choice_source_step ChoiceSourceStart [tt] ChoiceSourceTrap.

(** The target delays this choice until its silent administrative edge. *)
Inductive pre_choice_target_step : pre_choice_state -> list unit -> pre_choice_state -> Prop :=
  | choice_target_begin :
      pre_choice_target_step ChoiceTargetStart [tt] ChoiceTargetAdmin
  | choice_target_final :
      pre_choice_target_step ChoiceTargetAdmin [] ChoiceTargetFinal
  | choice_target_trap :
      pre_choice_target_step ChoiceTargetAdmin [] ChoiceTargetTrap.

Definition pre_choice_source : semantics pre_choice_state unit :=
  Semantics (fun s => s = ChoiceSourceStart) pre_choice_source_step.

Definition pre_choice_target : semantics pre_choice_state unit :=
  Semantics (fun t => t = ChoiceTargetStart) pre_choice_target_step.

Definition pre_choice_source_end : endings pre_choice_state :=
  Endings (fun s => s = ChoiceSourceFinal) (fun s => s = ChoiceSourceTrap) (fun _ => False).

Definition pre_choice_target_end : endings pre_choice_state :=
  Endings (fun t => t = ChoiceTargetFinal) (fun t => t = ChoiceTargetTrap) (fun _ => False).

Definition pre_choice_source_point (s : pre_choice_state) : pre_frame_state :=
  match s with
  | ChoiceSourceFinal | ChoiceSourceTrap => (PreEntry, PreBody)
  | _ => (PreEntry, PreBefore)
  end.

Definition pre_choice_source_graph :
    graph_view pre_choice_state unit pre_frame_state pre_test_edge :=
  GraphView pre_test_points pre_choice_source_point
    (fun s _ s' e => e = PreBind PreEntry /\
      pre_choice_source_point s = (PreEntry, PreBefore) /\
      pre_choice_source_point s' = (PreEntry, PreBody))
    (fun _ _ _ => False).

Inductive pre_choice_point : Type :=
  | ChoiceBefore
  | ChoiceDuring
  | ChoiceAfter.

Inductive pre_choice_edge : Type :=
  | ChoiceBegin
  | ChoiceFinishFinal
  | ChoiceFinishTrap.

Definition pre_choice_target_cfg : Graph.t pre_choice_point pre_choice_edge :=
  Graph.Make [ChoiceBefore] [ChoiceBefore; ChoiceDuring; ChoiceAfter]
    (fun n => match n with
      | ChoiceBefore => [ChoiceBegin]
      | ChoiceDuring => [ChoiceFinishFinal; ChoiceFinishTrap]
      | ChoiceAfter => []
      end)
    (fun e => match e with
      | ChoiceBegin => ChoiceBefore
      | _ => ChoiceDuring
      end)
    (fun e => match e with
      | ChoiceBegin => ChoiceDuring
      | _ => ChoiceAfter
      end).

Definition pre_choice_target_point (t : pre_choice_state) : pre_choice_point :=
  match t with
  | ChoiceTargetAdmin => ChoiceDuring
  | ChoiceTargetFinal | ChoiceTargetTrap => ChoiceAfter
  | _ => ChoiceBefore
  end.

Definition pre_choice_target_graph :
    graph_view pre_choice_state unit pre_choice_point pre_choice_edge :=
  GraphView pre_choice_target_cfg pre_choice_target_point
    (fun s _ t e => Graph.source pre_choice_target_cfg e = pre_choice_target_point s /\
      In e (Graph.out pre_choice_target_cfg (pre_choice_target_point s)) /\
      Graph.target pre_choice_target_cfg e = pre_choice_target_point t)
    (fun _ _ _ => False).

(** Boundaries preserve the chosen ending, while the in-progress state makes no choice yet. *)
Definition pre_choice_core (s t : pre_choice_state) : Prop :=
  (s = ChoiceSourceStart /\ t = ChoiceTargetStart) \/
  (s = ChoiceSourceFinal /\ t = ChoiceTargetFinal) \/
  (s = ChoiceSourceTrap /\ t = ChoiceTargetTrap).

Definition pre_choice_origin (n : pre_choice_point) : pre_origin pre_frame_state pre_test_edge :=
  match n with
  | ChoiceBefore => PrePoint (PreEntry, PreBefore)
  | ChoiceDuring => PreOnEdge (PreBind PreEntry) 1
  | ChoiceAfter => PrePoint (PreEntry, PreBody)
  end.

Definition pre_choice_project (e : pre_choice_edge) : option pre_test_edge :=
  match e with
  | ChoiceBegin => Some (PreBind PreEntry)
  | _ => None
  end.

(** Every cache and expression is the constant one, so this fixture satisfies C48 for all plans. *)
Definition pre_choice_realizer : pre_realizer pre_choice_state unit pre_frame_state
    pre_test_edge pre_choice_point pre_choice_edge pre_test_value nat :=
  PreRealizer pre_choice_source pre_choice_source_end pre_choice_source_graph
    (fun _ => pre_choice_target) (fun _ => pre_choice_target_end)
    (fun _ => pre_choice_target_graph) (fun _ => pre_choice_origin)
    (fun _ => pre_choice_project) (fun _ _ => Some 1) (fun _ _ => Some 1)
    pre_choice_core (fun _ t => match t with ChoiceTargetAdmin => 1 | _ => 0 end).

Definition pre_choice_ssa_view : ssa_view pre_choice_state unit pre_test_block
    pre_test_block_edge pre_test_value unit nat :=
  SsaView (GraphView pre_test_blocks (fun _ => PreEntry)
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (def pre_test_view) (home pre_test_view) (params pre_test_view) (edge_args pre_test_view)
    (edge_guard pre_test_view) (fun _ _ => Some 0) (op_eval pre_test_view) (truth pre_test_view).

Definition pre_choice_expression : pre_expr_ssa pre_choice_state unit pre_test_block
    pre_test_block_edge pre_frame_state pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_ssa pre_choice_ssa_view
    (PreExpressionView
      (GenKillView pre_choice_source_graph
        (gen (pre_genkill (pre_expression pre_test_expression)))
        (kill (pre_genkill (pre_expression pre_test_expression))) (fun _ _ => Some 1))
      (fun _ => true) pre_test_occurrence)
    [PreX; PreY; PreZ] [PreX; PreY; PreZ] (fun _ => 1%positive) (fun x => [x])
    (fun x env => option_map S (env x)) (fun be x => Some (pre_test_translate be x))
    (fun _ => false) (fun _ => true).

(** The delayed-choice fixture retains the entire strict, reachable expression-SSA contract. *)
Example pre_choice_expression_laws :
  pre_expr_ssa_laws pre_test_value_encoding pre_choice_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - exact (pre_expr_reachable_blocks _ _ pre_test_expression_laws).
  - exact (pre_expr_reachable_points _ _ pre_test_expression_laws).
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - exact (pre_expr_entry_no_incoming _ _ pre_test_expression_laws).
  - exact (pre_expr_params_nodup _ _ pre_test_expression_laws).
  - exact (pre_expr_value_nodup _ _ pre_test_expression_laws).
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; destruct u; cbn; tauto|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u (or_introl eq_refl)); reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    destruct e as [b|b|b|be], u; try destruct b;
      cbn in Hkill |- *; intuition congruence.
  - exact (pre_expr_def_home _ _ pre_test_expression_laws).
  - exact (pre_expr_cross_no_defs _ _ pre_test_expression_laws).
  - exact (pre_expr_real_internal _ _ pre_test_expression_laws).
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
Qed.

Local Lemma pre_choice_source_graph_laws :
  graph_view_laws pre_choice_source pre_choice_source_graph.
Proof.
  constructor.
  - exact pre_test_points_wf.
  - intros s Hinitial; change (s = ChoiceSourceStart) in Hinitial; subst s; cbn; tauto.
  - intros s l s' Hreachable Hstep; right; exists (PreBind PreEntry).
    destruct Hstep; repeat split; reflexivity.
  - intros s l s' e Hreachable Hstep [-> [Hsource Htarget]].
    change (In (PreBind PreEntry) (Graph.out pre_test_points (pre_choice_source_point s)) /\
      (PreEntry, PreBody) = pre_choice_source_point s').
    rewrite Hsource, Htarget; cbn; tauto.
  - intros s l s' Hreachable Hstep Hfalse; contradiction.
Qed.

Local Lemma pre_choice_target_cfg_wf : graph_wf pre_choice_target_cfg.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros [] Hentry; cbn in *; tauto.
  - intros [] [] Hedge; cbn in *; intuition congruence.
  - intros [] [] Hnode Hedge; cbn in *; intuition congruence.
Qed.

Local Lemma pre_choice_target_edges : forall s l t, pre_choice_target_step s l t ->
  exists e, taken pre_choice_target_graph s l t e.
Proof.
  intros s l t Hstep; destruct Hstep.
  - exists ChoiceBegin; cbn; tauto.
  - exists ChoiceFinishFinal; cbn; tauto.
  - exists ChoiceFinishTrap; cbn; tauto.
Qed.

Local Lemma pre_choice_target_graph_laws :
  graph_view_laws pre_choice_target pre_choice_target_graph.
Proof.
  constructor.
  - exact pre_choice_target_cfg_wf.
  - intros t Hinitial; change (t = ChoiceTargetStart) in Hinitial; subst t; cbn; tauto.
  - intros s l t Hreachable Hstep; right; apply pre_choice_target_edges; exact Hstep.
  - intros s l t e Hreachable Hstep [Hsource [Hout Htarget]]; tauto.
  - intros s l t Hreachable Hstep Hfalse; contradiction.
Qed.

Local Lemma pre_choice_macro : forall p e t l t',
  pre_macro_step pre_choice_realizer p e t l t' <->
  t = ChoiceTargetStart /\ e = PreBind PreEntry /\ l = [tt] /\
    (t' = ChoiceTargetFinal \/ t' = ChoiceTargetTrap).
Proof.
  intros p e t l t'; split.
  - intros [Hboundary [t1 [te [Hstep [Htaken [Hproject Hfinish]]]]]].
    destruct Hstep; cbn in Hboundary; try discriminate.
    destruct te; cbn in Hproject; try discriminate.
    inversion Hproject; subst e.
    apply pre_finish_endpoint in Hfinish.
    destruct t'; cbn in Hfinish; try discriminate; tauto.
  - intros [-> [-> [-> Hend]]]; destruct Hend as [-> | ->]; split;
      [reflexivity| |reflexivity|].
    + exists ChoiceTargetAdmin, ChoiceBegin; split; [constructor|].
      split; [cbn; tauto|]; split; [reflexivity|].
      eapply pre_finish_admin with (t1 := ChoiceTargetFinal) (te := ChoiceFinishFinal).
      * exists 1; reflexivity.
      * constructor.
      * cbn; tauto.
      * reflexivity.
      * apply pre_finish_boundary; reflexivity.
    + exists ChoiceTargetAdmin, ChoiceBegin; split; [constructor|].
      split; [cbn; tauto|]; split; [reflexivity|].
      eapply pre_finish_admin with (t1 := ChoiceTargetTrap) (te := ChoiceFinishTrap).
      * exists 1; reflexivity.
      * constructor.
      * cbn; tauto.
      * reflexivity.
      * apply pre_finish_boundary; reflexivity.
Qed.

Local Lemma pre_choice_match : forall p s t e, pre_choice_core s t ->
  (forall l s', pre_choice_source_step s l s' ->
    taken pre_choice_source_graph s l s' e ->
    exists t', pre_macro_step pre_choice_realizer p e t l t' /\ pre_choice_core s' t') /\
  (forall l t', pre_macro_step pre_choice_realizer p e t l t' ->
    exists s', pre_choice_source_step s l s' /\
      taken pre_choice_source_graph s l s' e /\ pre_choice_core s' t').
Proof.
  intros p s t e Hcore; destruct Hcore as [[-> ->]|[[-> ->]|[-> ->]]]; split.
  - intros l s' Hstep [-> Hpoints]; destruct Hstep.
    + exists ChoiceTargetFinal; split; [apply pre_choice_macro; tauto|].
      right; left; tauto.
    + exists ChoiceTargetTrap; split; [apply pre_choice_macro; tauto|].
      right; right; tauto.
  - intros l t' Hmacro; apply pre_choice_macro in Hmacro.
    destruct Hmacro as [_ [-> [-> [-> | ->]]]].
    + exists ChoiceSourceFinal; split; [constructor|].
      split; [repeat split; reflexivity|right; left; tauto].
    + exists ChoiceSourceTrap; split; [constructor|].
      split; [repeat split; reflexivity|right; right; tauto].
  - intros l s' Hstep; inversion Hstep.
  - intros l t' Hmacro; apply pre_choice_macro in Hmacro; intuition discriminate.
  - intros l s' Hstep; inversion Hstep.
  - intros l t' Hmacro; apply pre_choice_macro in Hmacro; intuition discriminate.
Qed.

Local Lemma pre_choice_phi_update : forall p incoming parameter version,
  pre_phi_update pre_test_edge_encoding pre_test_value_encoding p incoming parameter
    (fun _ => Some 1) version = Some 1.
Proof.
  intros p incoming parameter [u|e u|e u|e u]; cbn [pre_phi_update]; try reflexivity.
  destruct (Pos.eqb (encode pre_test_edge_encoding e) (encode pre_test_edge_encoding parameter));
    [|reflexivity].
  destruct (Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((e, incoming), u) (pre_phi_versions p)); reflexivity.
Qed.

Local Lemma pre_choice_endings : forall s t k, pre_choice_core s t ->
  (ends_as pre_choice_source pre_choice_source_end k s <->
    ends_as pre_choice_target pre_choice_target_end k t).
Proof.
  assert (running pre_choice_source ChoiceSourceStart) as Hsource.
  { exists [tt], ChoiceSourceFinal; constructor. }
  assert (running pre_choice_target ChoiceTargetStart) as Htarget.
  { exists [tt], ChoiceTargetAdmin; constructor. }
  intros s t k Hcore; destruct Hcore as [[-> ->]|[[-> ->]|[-> ->]]]; destruct k;
    cbn [ends_as pre_choice_source_end pre_choice_target_end final trapped stopped];
    try (split; intro Hfalse; discriminate); try tauto.
  - unfold stuck; tauto.
  - unfold stuck; cbn; tauto.
  - unfold stuck; cbn; tauto.
Qed.

Local Lemma pre_choice_projection : forall p t l t',
  reachable_state pre_choice_target t -> pre_choice_target_step t l t' ->
  exists te, taken pre_choice_target_graph t l t' te /\
    match pre_choice_origin (pre_choice_target_point t) with
    | PrePoint n => exists e, pre_choice_project te = Some e /\
        In e (Graph.out pre_test_points n) /\
        (pre_boundary pre_choice_realizer p (Graph.target pre_test_points e) t' \/
         pre_admin pre_choice_realizer p e t')
    | PreOnEdge e _ => pre_choice_project te = None /\
        (pre_admin pre_choice_realizer p e t' \/
         pre_boundary pre_choice_realizer p (Graph.target pre_test_points e) t')
    end.
Proof.
  intros p t l t' Hreachable Hstep; destruct Hstep.
  - exists ChoiceBegin; split; [cbn; tauto|].
    cbn; exists (PreBind PreEntry); split; [reflexivity|].
    split; [cbn; tauto|right; exists 1; reflexivity].
  - exists ChoiceFinishFinal; split; [cbn; tauto|].
    cbn; split; [reflexivity|right; reflexivity].
  - exists ChoiceFinishTrap; split; [cbn; tauto|].
    cbn; split; [reflexivity|right; reflexivity].
Qed.

(** Both administrative choices finish silently and decrease the same concrete measure. *)
Local Lemma pre_choice_progress : forall p t e,
  reachable_state pre_choice_target t -> pre_admin pre_choice_realizer p e t ->
  ~ final pre_choice_target_end t /\ ~ trapped pre_choice_target_end t /\
  ~ stopped pre_choice_target_end t /\ ~ stuck pre_choice_target pre_choice_target_end t /\
  running pre_choice_target t /\ forall l t', pre_choice_target_step t l t' -> l = [] /\
    (pre_boundary pre_choice_realizer p (Graph.target pre_test_points e) t' \/
     (pre_admin pre_choice_realizer p e t' /\
       pre_measure pre_choice_realizer p t' < pre_measure pre_choice_realizer p t)).
Proof.
  intros p t e Hreachable [k Horigin]; destruct t; cbn in Horigin; try discriminate.
  inversion Horigin; subst e k.
  split; [discriminate|]; split; [discriminate|]; split; [tauto|].
  split.
  - intros [Hnot_running _]; apply Hnot_running; exists [], ChoiceTargetFinal; constructor.
  - split; [exists [], ChoiceTargetFinal; constructor|].
    intros l t' Hstep; inversion Hstep; subst; split; [reflexivity| |reflexivity|];
      left; reflexivity.
Qed.

(** All current local laws, including both C48 source frames, hold for every possible plan. *)
Example pre_choice_local_laws : forall p,
  pre_local_laws pre_test_block_edge_encoding pre_test_point_encoding pre_test_edge_encoding
    pre_test_value_encoding pre_test_value_encoding pre_choice_expression
    (pre_expression pre_choice_expression) (pre_initial_available pre_choice_expression)
    pre_choice_realizer p.
Proof.
  intro p; constructor.
  - split; [reflexivity|]; split; [reflexivity|].
    split; [exact pre_choice_source_graph_laws|].
    split; [exact pre_choice_target_graph_laws|].
    split; [intros s l s' Hfalse; exact Hfalse|].
    split; [intros t l t' Hfalse; exact Hfalse|].
    exact (pre_choice_projection p).
  - split; [reflexivity|]; split; [reflexivity|]; split.
    + intros s u Hreachable Hpure; exists 1; reflexivity.
    + intros e u Hcomputed; change (pre_test_occurrence e = Some u) in Hcomputed.
      change (In u (match pre_test_occurrence e with Some x => [x] | None => [] end)).
      rewrite Hcomputed; left; reflexivity.
  - intros s l s' e u Hreachable Hstep Htaken Hgen; reflexivity.
  - intros s l s' e u Hreachable Hstep Htaken Hkill; reflexivity.
  - intros s t e Hs Ht Hpoint Hboundary Hcore Hdeleted.
    apply pre_choice_match; exact Hcore.
  - intros s t e u l s' t' Hs Ht Hcore Hinsert Hstep Htaken Hmacro; reflexivity.
  - intros s t e u version Hs Ht Hpoint Hboundary Hcore Hdeleted Hreload Hcache.
    apply pre_choice_match; exact Hcore.
  - intros s t e l s' t' version Hs Ht Hpoint Hboundary Hstep Htaken Hmacro Hwritten.
    reflexivity.
  - intros s t e u l s' t' Hs Ht Hcomputed Hdeleted Hstep Htaken Hmacro; reflexivity.
  - intros s t u Hs Ht Hcore Havailable; reflexivity.
  - intros s0 t0 s1 t1 s2 t2 be incoming l0 l version Hs Ht Hindex
      Hstep Htaken Hmacro Hparameter Hparameter_taken Hparameter_macro.
    symmetry; apply pre_choice_phi_update.
  - exact (pre_choice_progress p).
  - intros s t n k Hs Ht Hpoint Hboundary Hcore; apply pre_choice_endings; exact Hcore.
Qed.

(** Every source ending is explicitly covered, including hypothetical stuck and stop endings. *)
Example pre_choice_exit_covered : pre_exit_covered pre_choice_expression pre_choice_realizer.
Proof.
  intros s k Hreachable Hending; reflexivity.
Qed.

(** No source run traverses a block edge and a parameter edge in this one-edge fixture. *)
Example pre_choice_phi_source_laws :
  pre_phi_source_laws pre_test_block_edge_encoding pre_test_value_encoding
    pre_choice_expression pre_choice_realizer.
Proof.
  intros be e s0 l0 s1 l1 s2 Hreachable Hindex Hstep Htaken Hparameter Hparameter_taken x.
  destruct Hstep; inversion Hparameter.
Qed.

(** Each arbitrary plan has the required initial boundary and full cache agreement. *)
Example pre_choice_initial_cache : forall p,
  pre_boundary pre_choice_realizer p (PreEntry, PreBefore) ChoiceTargetStart /\
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_choice_expression) pre_choice_realizer p (PreEntry, PreBefore)
    ChoiceSourceStart ChoiceTargetStart.
Proof.
  intro p; split; [reflexivity|]; split; [left; tauto|].
  intros e u version Hsource Hdelete Hreload; reflexivity.
Qed.

(** The fixture supplies every semantic-theorem premise independently of the plan producer. *)
Example pre_choice_all_premises : forall p,
  pre_expr_ssa_laws pre_test_value_encoding pre_choice_expression /\
  ready pre_test_block_encoding (block_graph (pre_ssa_points pre_choice_expression))
    (prepare pre_test_block_encoding (block_graph (pre_ssa_points pre_choice_expression))) /\
  ready pre_test_point_encoding (live_graph (point_model (pre_ssa_points pre_choice_expression)))
    (prepare pre_test_point_encoding
      (live_graph (point_model (pre_ssa_points pre_choice_expression)))) /\
  pre_exit_covered pre_choice_expression pre_choice_realizer /\
  pre_phi_source_laws pre_test_block_edge_encoding pre_test_value_encoding
    pre_choice_expression pre_choice_realizer /\
  pre_local_laws pre_test_block_edge_encoding pre_test_point_encoding pre_test_edge_encoding
    pre_test_value_encoding pre_test_value_encoding pre_choice_expression
    (pre_expression pre_choice_expression) (pre_initial_available pre_choice_expression)
    pre_choice_realizer p /\
  initial (pre_source pre_choice_realizer) ChoiceSourceStart /\
  initial (pre_target pre_choice_realizer p) ChoiceTargetStart /\
  pre_boundary pre_choice_realizer p
    (point (pre_source_graph pre_choice_realizer) ChoiceSourceStart) ChoiceTargetStart /\
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_choice_expression) pre_choice_realizer p
    (point (pre_source_graph pre_choice_realizer) ChoiceSourceStart)
    ChoiceSourceStart ChoiceTargetStart.
Proof.
  intro p; split; [exact pre_choice_expression_laws|].
  split; [exact pre_test_blocks_ready|]; split; [exact pre_test_points_ready|].
  split; [exact pre_choice_exit_covered|]; split; [exact pre_choice_phi_source_laws|].
  split; [exact (pre_choice_local_laws p)|].
  split; [reflexivity|]; split; [reflexivity|].
  exact (pre_choice_initial_cache p).
Qed.

Local Lemma pre_choice_source_final_run : forall tr s,
  exec pre_choice_source ChoiceSourceFinal tr s -> tr = [] /\ s = ChoiceSourceFinal.
Proof.
  intros tr s Hrun; inversion Hrun as [|s0 l s1 suffix s2 Hstep Htail]; subst.
  - tauto.
  - inversion Hstep.
Qed.

Local Lemma pre_choice_target_trap_run : forall tr t,
  exec pre_choice_target ChoiceTargetTrap tr t -> tr = [] /\ t = ChoiceTargetTrap.
Proof.
  intros tr t Hrun; inversion Hrun as [|t0 l t1 suffix t2 Hstep Htail]; subst.
  - tauto.
  - inversion Hstep.
Qed.

Local Lemma pre_choice_target_start_silent : forall t,
  exec pre_choice_target ChoiceTargetStart [] t -> t = ChoiceTargetStart.
Proof.
  intros t Hrun; inversion Hrun as [|t0 l t1 suffix t2 Hstep Htail]; subst.
  - reflexivity.
  - inversion Hstep; subst; discriminate.
Qed.

(** No choice of relation or decreasing measures gives the required two-way stuttering match. *)
Example pre_choice_no_stuttering : forall R mu1 mu2,
  stuttering pre_choice_source pre_choice_source_end pre_choice_target pre_choice_target_end
    R mu1 mu2 -> ~ R ChoiceSourceStart ChoiceTargetStart.
Proof.
  intros R mu1 mu2 Hstutter Hinitial.
  pose proof (st_forth Hstutter _ _ _ _ Hinitial choice_source_final) as Hforth.
  destruct Hforth as [[Hsilent _]|[t1 [t' [Hsilent [Hstep Hrelated]]]]]; [discriminate|].
  apply pre_choice_target_start_silent in Hsilent; subst t1.
  inversion Hstep; subst t'.
  pose proof (st_back Hstutter _ _ _ _ Hrelated choice_target_trap) as Hback.
  destruct Hback as [[Hsilent [Hend Hmeasure]]|[s1 [s' [Hrun [Hnext Hend]]]]].
  - destruct (st_ends_forth Hstutter _ _ EndFinal Hend eq_refl) as [t [Hrun Hfinal]].
    apply pre_choice_target_trap_run in Hrun; destruct Hrun as [_ ->].
    discriminate.
  - apply pre_choice_source_final_run in Hrun; destruct Hrun as [_ ->].
    inversion Hnext.
Qed.

(** The actual macro semantics has one transition for each complete original-edge realization. *)
Definition pre_choice_macros (p : pre_plan pre_test_edge pre_test_value) :
    semantics pre_choice_state unit :=
  Semantics (initial pre_choice_target)
    (fun t l t' => exists e, pre_macro_step pre_choice_realizer p e t l t').

Local Lemma pre_choice_macro_final_run : forall p tr t,
  exec (pre_choice_macros p) ChoiceTargetFinal tr t ->
  tr = [] /\ t = ChoiceTargetFinal.
Proof.
  intros p tr t Hrun; inversion Hrun as [|t0 l t1 suffix t2 Hstep Htail]; subst.
  - tauto.
  - destruct Hstep as [e Hmacro]; apply pre_choice_macro in Hmacro; intuition discriminate.
Qed.

(** The required macro-to-actual-target stuttering correspondence is impossible as well. *)
Example pre_choice_macros_no_stuttering : forall p R mu1 mu2,
  stuttering (pre_choice_macros p) pre_choice_target_end pre_choice_target
    pre_choice_target_end R mu1 mu2 -> ~ R ChoiceTargetStart ChoiceTargetStart.
Proof.
  intros p R mu1 mu2 Hstutter Hinitial.
  assert (step (pre_choice_macros p) ChoiceTargetStart [tt] ChoiceTargetFinal) as Hmacro.
  { exists (PreBind PreEntry); apply pre_choice_macro; tauto. }
  pose proof (st_forth Hstutter _ _ _ _ Hinitial Hmacro) as Hforth.
  destruct Hforth as [[Hsilent _]|[t1 [t' [Hsilent [Hstep Hrelated]]]]]; [discriminate|].
  apply pre_choice_target_start_silent in Hsilent; subst t1.
  inversion Hstep; subst t'.
  pose proof (st_back Hstutter _ _ _ _ Hrelated choice_target_trap) as Hback.
  destruct Hback as [[Hsilent [Hend Hmeasure]]|[s1 [s' [Hrun [Hnext Hend]]]]].
  - destruct (st_ends_forth Hstutter _ _ EndFinal Hend eq_refl) as [t [Hrun Hfinal]].
    apply pre_choice_target_trap_run in Hrun; destruct Hrun as [_ ->].
    discriminate.
  - apply pre_choice_macro_final_run in Hrun; destruct Hrun as [_ ->].
    destruct Hnext as [e Hnext]; apply pre_choice_macro in Hnext; intuition discriminate.
Qed.

Local Lemma pre_choice_source_start_run : forall tr s,
  exec pre_choice_source ChoiceSourceStart tr s ->
  (tr = [] /\ s = ChoiceSourceStart) \/
  (tr = [tt] /\ (s = ChoiceSourceFinal \/ s = ChoiceSourceTrap)).
Proof.
  intros tr s Hrun; inversion Hrun as [|s0 l s1 suffix s2 Hstep Htail]; subst.
  - left; tauto.
  - destruct Hstep; inversion Htail as [|q0 l1 q1 suffix1 q2 Hnext Hrest]; subst;
      try (inversion Hnext); right; tauto.
Qed.

Local Lemma pre_choice_target_terminal_run : forall t tr t',
  (t = ChoiceTargetFinal \/ t = ChoiceTargetTrap) ->
  exec pre_choice_target t tr t' -> tr = [] /\ t' = t.
Proof.
  intros t tr t' Hterminal Hrun; inversion Hrun as [|s0 l s1 suffix s2 Hstep Htail]; subst.
  - tauto.
  - destruct Hterminal as [-> | ->]; inversion Hstep.
Qed.

Local Lemma pre_choice_target_admin_run : forall tr t,
  exec pre_choice_target ChoiceTargetAdmin tr t ->
  tr = [] /\ (t = ChoiceTargetAdmin \/ t = ChoiceTargetFinal \/ t = ChoiceTargetTrap).
Proof.
  intros tr t Hrun; inversion Hrun as [|s0 l s1 suffix s2 Hstep Htail]; subst.
  - tauto.
  - inversion Hstep; subst s1 l.
    + destruct (pre_choice_target_terminal_run _ _ _ (or_introl eq_refl) Htail) as [-> ->].
      cbn; tauto.
    + destruct (pre_choice_target_terminal_run _ _ _ (or_intror eq_refl) Htail) as [-> ->].
      cbn; tauto.
Qed.

Local Lemma pre_choice_target_start_run : forall tr t,
  exec pre_choice_target ChoiceTargetStart tr t ->
  (tr = [] /\ t = ChoiceTargetStart) \/
  (tr = [tt] /\
    (t = ChoiceTargetAdmin \/ t = ChoiceTargetFinal \/ t = ChoiceTargetTrap)).
Proof.
  intros tr t Hrun; inversion Hrun as [|s0 l s1 suffix s2 Hstep Htail]; subst.
  - left; tauto.
  - inversion Hstep; subst s1 l.
    apply pre_choice_target_admin_run in Htail; destruct Htail as [-> Hend].
    right; cbn; tauto.
Qed.

Local Lemma pre_choice_source_no_divergence : forall s, ~ diverges pre_choice_source s.
Proof.
  intros s Hdiverge; inversion Hdiverge as [s0 l s1 Hstep Htail]; subst.
  destruct Hstep; inversion Htail as [s0 l s1 Hnext Hrest]; inversion Hnext.
Qed.

Local Lemma pre_choice_target_no_divergence : forall t, ~ diverges pre_choice_target t.
Proof.
  assert (forall t, t = ChoiceTargetFinal \/ t = ChoiceTargetTrap ->
    ~ diverges pre_choice_target t) as Hterminal.
  { intros t [-> | ->] Hdiverge; inversion Hdiverge as [s0 l s1 Hstep Htail];
      inversion Hstep. }
  assert (~ diverges pre_choice_target ChoiceTargetAdmin) as Hadmin.
  { intro Hdiverge; inversion Hdiverge as [s0 l s1 Hstep Htail].
    inversion Hstep; subst s1.
    - exact (Hterminal _ (or_introl eq_refl) Htail).
    - exact (Hterminal _ (or_intror eq_refl) Htail). }
  intros t Hdiverge; inversion Hdiverge as [s0 l s1 Hstep Htail]; subst.
  destruct Hstep.
  - exact (Hadmin Htail).
  - exact (Hterminal _ (or_introl eq_refl) Htail).
  - exact (Hterminal _ (or_intror eq_refl) Htail).
Qed.

Local Lemma pre_choice_target_reach_final :
  exec pre_choice_target ChoiceTargetStart [tt] ChoiceTargetFinal.
Proof.
  eapply exec_step with (l := [tt]) (tr := []) (s' := ChoiceTargetAdmin).
  - constructor.
  - apply exec_one; constructor.
Qed.

Local Lemma pre_choice_target_reach_trap :
  exec pre_choice_target ChoiceTargetStart [tt] ChoiceTargetTrap.
Proof.
  eapply exec_step with (l := [tt]) (tr := []) (s' := ChoiceTargetAdmin).
  - constructor.
  - apply exec_one; constructor.
Qed.

Local Lemma pre_choice_source_start_no_end : forall k,
  ~ ends_as pre_choice_source pre_choice_source_end k ChoiceSourceStart.
Proof.
  intros []; cbn [ends_as pre_choice_source_end]; try (intro Hfalse; discriminate); try tauto.
  intros [Hnot_running _]; apply Hnot_running; exists [tt], ChoiceSourceFinal; constructor.
Qed.

Local Lemma pre_choice_target_start_no_end : forall k,
  ~ ends_as pre_choice_target pre_choice_target_end k ChoiceTargetStart.
Proof.
  intros []; cbn [ends_as pre_choice_target_end]; try (intro Hfalse; discriminate); try tauto.
  intros [Hnot_running _]; apply Hnot_running; exists [tt], ChoiceTargetAdmin; constructor.
Qed.

Local Lemma pre_choice_target_admin_no_end : forall k,
  ~ ends_as pre_choice_target pre_choice_target_end k ChoiceTargetAdmin.
Proof.
  intros []; cbn [ends_as pre_choice_target_end]; try (intro Hfalse; discriminate); try tauto.
  intros [Hnot_running _]; apply Hnot_running; exists [], ChoiceTargetFinal; constructor.
Qed.

(** The obstruction concerns stuttering coupling: all observable behavior sets still agree. *)
Example pre_choice_same_behaviour :
  same_behaviour pre_choice_source pre_choice_source_end ChoiceSourceStart
    pre_choice_target pre_choice_target_end ChoiceTargetStart.
Proof.
  constructor.
  - intros k tr; split.
    + intros [s [Hrun Hending]]; apply pre_choice_source_start_run in Hrun.
      destruct Hrun as [[-> ->]|[-> [-> | ->]]].
      * exfalso; exact (pre_choice_source_start_no_end k Hending).
      * exists ChoiceTargetFinal; split; [exact pre_choice_target_reach_final|].
        apply (proj1 (pre_choice_endings _ _ _ (or_intror (or_introl (conj eq_refl eq_refl))))).
        exact Hending.
      * exists ChoiceTargetTrap; split; [exact pre_choice_target_reach_trap|].
        apply (proj1 (pre_choice_endings _ _ _ (or_intror (or_intror (conj eq_refl eq_refl))))).
        exact Hending.
    + intros [t [Hrun Hending]]; apply pre_choice_target_start_run in Hrun.
      destruct Hrun as [[-> ->]|[-> [-> | [-> | ->]]]].
      * exfalso; exact (pre_choice_target_start_no_end k Hending).
      * exfalso; exact (pre_choice_target_admin_no_end k Hending).
      * exists ChoiceSourceFinal; split; [apply exec_one; constructor|].
        apply (proj2 (pre_choice_endings _ _ _ (or_intror (or_introl (conj eq_refl eq_refl))))).
        exact Hending.
      * exists ChoiceSourceTrap; split; [apply exec_one; constructor|].
        apply (proj2 (pre_choice_endings _ _ _ (or_intror (or_intror (conj eq_refl eq_refl))))).
        exact Hending.
  - intro tr; split.
    + intros [s Hrun]; apply pre_choice_source_start_run in Hrun.
      destruct Hrun as [[-> _]|[-> _]].
      * exists ChoiceTargetStart; apply exec_refl.
      * exists ChoiceTargetAdmin; apply exec_one; constructor.
    + intros [t Hrun]; apply pre_choice_target_start_run in Hrun.
      destruct Hrun as [[-> _]|[-> _]].
      * exists ChoiceSourceStart; apply exec_refl.
      * exists ChoiceSourceFinal; apply exec_one; constructor.
  - intro tr; split; intros [s [Hrun Hdiverge]]; exfalso.
    + exact (pre_choice_source_no_divergence s Hdiverge).
    + exact (pre_choice_target_no_divergence s Hdiverge).
Qed.

(** The general C51 path theorem handles the delayed choice that refutes stuttering. *)
Example pre_choice_complete_path_behaviour : forall p,
  same_behaviour (pre_macro_semantics pre_choice_realizer p) pre_choice_target_end
    ChoiceTargetStart pre_choice_target pre_choice_target_end ChoiceTargetStart.
Proof.
  intro p; eapply (pre_target_macro_behaviour pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_choice_expression (pre_expression pre_choice_expression)
    (pre_initial_available pre_choice_expression) pre_choice_realizer p
    (pre_choice_local_laws p) ChoiceTargetStart (PreEntry, PreBefore)).
  - exists ChoiceTargetStart, []; split; [reflexivity|apply exec_refl].
  - reflexivity.
Qed.

(** * Placement on a diamond with one missing incoming computation *)

Definition pre_diamond_occurrence (e : pre_test_edge) : option pre_test_value :=
  match e with
  | PreCompute PreRight | PreAgain PreRight => None
  | _ => pre_test_occurrence e
  end.

Definition pre_diamond_expression : pre_expr_ssa unit unit pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_ssa pre_test_view
    (PreExpressionView (GenKillView pre_test_point_view
      (fun e => match pre_diamond_occurrence e with Some u => [u] | None => [] end)
      (kill (pre_genkill (pre_expression pre_test_expression))) (fun _ _ => Some 1))
      (fun _ => true) pre_diamond_occurrence)
    [PreX; PreY; PreZ] [PreX; PreY; PreZ] (fun _ => 1%positive) (fun x => [x])
    (fun x env => option_map S (env x)) (fun be x => Some (pre_test_translate be x))
    (fun _ => false) (fun _ => false).

Local Lemma pre_diamond_occurrence_original : forall e u,
  pre_diamond_occurrence e = Some u -> pre_test_occurrence e = Some u.
Proof.
  intros [b|b|b|be] u Hcomputed; try destruct b; cbn in Hcomputed |- *;
    try discriminate; exact Hcomputed.
Qed.

(** Removing the right branch's occurrences retains the full C47 expression-SSA domain. *)
Example pre_diamond_expression_laws :
  pre_expr_ssa_laws pre_test_value_encoding pre_diamond_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - exact (pre_expr_reachable_blocks _ _ pre_test_expression_laws).
  - exact (pre_expr_reachable_points _ _ pre_test_expression_laws).
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - exact (pre_expr_entry_no_incoming _ _ pre_test_expression_laws).
  - exact (pre_expr_params_nodup _ _ pre_test_expression_laws).
  - exact (pre_expr_value_nodup _ _ pre_test_expression_laws).
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; destruct u; cbn; tauto|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u (or_introl eq_refl)); reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    destruct e as [b|b|b|be], u; try destruct b;
      cbn in Hkill |- *; intuition congruence.
  - exact (pre_expr_def_home _ _ pre_test_expression_laws).
  - exact (pre_expr_cross_no_defs _ _ pre_test_expression_laws).
  - intros e u Hcomputed; apply (pre_expr_real_internal _ _ pre_test_expression_laws e u).
    apply pre_diamond_occurrence_original; exact Hcomputed.
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
Qed.

Definition pre_diamond_frg := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
  pre_test_value_encoding pre_diamond_expression.

Definition pre_diamond_facts := solve_ssapre pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
  pre_test_value_encoding pre_diamond_expression pre_diamond_frg.

Definition pre_diamond_plan := ssa_pre_place pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
  pre_test_value_encoding pre_diamond_expression.

(** The join expression is down-safe and can be made available, and its later flag is reset. *)
Example pre_diamond_reset_flags :
  live_bool_get (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreJoin,PreZ)
    (ssapre_downsafe pre_diamond_facts) = true /\
  live_bool_get (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreJoin,PreZ)
    (ssapre_can_available pre_diamond_facts) = true /\
  live_bool_get (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreJoin,PreZ)
    (ssapre_later pre_diamond_facts) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The actual producer inserts the right predecessor's translated expression. *)
Example pre_diamond_insertion :
  pre_inserted pre_test_edge_encoding pre_test_value_encoding pre_diamond_plan
    (PreCross PreRightJoin) PreY = true /\
  pre_inserted pre_test_edge_encoding pre_test_value_encoding pre_diamond_plan
    (PreCross PreLeftJoin) PreX = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Both later recomputations select the expression phi rather than a predecessor's expression. *)
Example pre_diamond_deletions :
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_diamond_plan
    (PreCompute PreJoin) PreZ = true /\
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_diamond_plan
    (PreAgain PreJoin) PreZ = true /\
  Map.get pre_test_edge_encoding (PreCompute PreJoin) (pre_reload_versions pre_diamond_plan) =
    Some (PreMerged (PreBind PreJoin) PreZ).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The C47 parameter expression selects distinct translated versions on the actual two edges. *)
Example pre_diamond_phi_selection :
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((PreBind PreJoin,PreCross PreLeftJoin),PreZ)
    (pre_phi_versions pre_diamond_plan) = Some (PreComputed (PreCompute PreLeft) PreX) /\
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((PreBind PreJoin,PreCross PreRightJoin),PreZ)
    (pre_phi_versions pre_diamond_plan) = Some (PreInserted (PreCross PreRightJoin) PreY).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The direct reset theorem applies to this complete-law producer input. *)
Example pre_diamond_resets_exact :
  let f := pre_diamond_frg in
  forall b u, FinSet.mem (pair_encoding pre_test_block_encoding pre_test_value_encoding)
    (b,u) (frg_phi_index f) = true ->
    (live_bool_get (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      (b,u) (ssapre_downsafe pre_diamond_facts) = true <->
      ~ ssapre_down_unsafe pre_test_block_encoding pre_test_value_encoding
        pre_test_block_edge_encoding f (b,u)).
Proof.
  cbn zeta; intros b u Hphi.
  exact (proj1 (solve_ssapre_exact pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_diamond_expression pre_diamond_expression_laws
    pre_test_blocks_ready pre_test_points_ready b u Hphi)).
Qed.

(** Placement legality is instantiated for the actual insertion, join and deletion producer. *)
Example pre_diamond_plan_legal :
  pre_placement_legal pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_diamond_expression) pre_diamond_plan.
Proof.
  apply ssa_pre_place_legal.
  - exact pre_diamond_expression_laws.
  - exact pre_test_blocks_ready.
  - exact pre_test_points_ready.
Qed.

(** The generic phi-version theorem covers both distinct incoming translations of the diamond. *)
Example pre_diamond_phi_versions_correct : forall be version,
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((PreBind PreJoin,PreCross be),PreZ)
    (pre_phi_versions pre_diamond_plan) = Some version ->
  Graph.target pre_test_blocks be = PreJoin ->
  exists translated, pre_phi_translate pre_diamond_expression be PreZ = Some translated /\
    pre_version_expr version = translated /\
    (version = PreInserted (PreCross be) translated \/ exists n,
      pre_version_point (pre_expression pre_diamond_expression) version = Some n /\
      dominates pre_test_points n (Graph.source pre_test_points (PreCross be))).
Proof.
  intros be version Hget Htarget.
  eapply (ssa_pre_phi_versions_correct pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_diamond_expression pre_diamond_expression_laws
    pre_test_blocks_ready pre_test_points_ready PreJoin PreZ be (PreCross be) version).
  - destruct be; try reflexivity; cbn in Htarget; discriminate.
  - exact Htarget.
  - exact Hget.
Qed.

Definition pre_loop_pre_plan := ssa_pre_place pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding unit_encoding unit_encoding
  (pre_flow_expression pre_loop_blocks pre_loop_occurs).

(** A loop reload selects the finite merged version, including the original backedge identity. *)
Example pre_loop_pre_selection :
  Map.get pre_test_edge_encoding (PreCompute PreLeft) (pre_reload_versions pre_loop_pre_plan) =
    Some (PreMerged (PreBind PreLeft) tt) /\
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    unit_encoding)
    ((PreBind PreLeft,PreCross PreToRight),tt) (pre_phi_versions pre_loop_pre_plan) =
    Some (PreMerged (PreBind PreLeft) tt) /\
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    unit_encoding)
    ((PreBind PreLeft,PreCross PreToLeft),tt) (pre_phi_versions pre_loop_pre_plan) =
    Some (PreComputed (PreCompute PreEntry) tt).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The supported loop has the same generic legality guarantee as the acyclic diamond. *)
Example pre_loop_pre_legal :
  pre_placement_legal pre_test_point_encoding pre_test_edge_encoding unit_encoding
    (pre_expression (pre_flow_expression pre_loop_blocks pre_loop_occurs)) pre_loop_pre_plan.
Proof.
  apply ssa_pre_place_legal.
  - exact pre_loop_expression_laws.
  - exact pre_loop_blocks_ready.
  - exact pre_loop_points_ready.
Qed.

Definition pre_parallel_pre_plan := ssa_pre_place pre_test_block_encoding
  pre_test_block_edge_encoding pre_test_point_encoding pre_test_edge_encoding
  pre_test_value_encoding pre_test_value_encoding (pre_parallel_expression true).

(** Parallel incoming edges retain distinct X/Y versions after placement and resolution. *)
Example pre_parallel_pre_selection :
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((PreBind PreJoin,PreCross PreLeftJoin),PreZ)
    (pre_phi_versions pre_parallel_pre_plan) = Some (PreComputed (PreCompute PreRight) PreX) /\
  Map.get (pair_encoding (pair_encoding pre_test_edge_encoding pre_test_edge_encoding)
    pre_test_value_encoding) ((PreBind PreJoin,PreCross PreRightJoin),PreZ)
    (pre_phi_versions pre_parallel_pre_plan) = Some (PreComputed (PreAgain PreRight) PreY).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The C19 no-incoming-entry premise still rejects an entry loop in this backend. *)
Example pre_pre_entry_loop_rejected :
  ~ pre_expr_ssa_laws unit_encoding
    (pre_flow_expression pre_entry_self_loop (fun _ => false)).
Proof.
  exact pre_entry_self_loop_rejected.
Qed.

Definition pre_trap_expression : pre_expr_ssa unit unit pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_ssa pre_test_view
    (PreExpressionView (GenKillView pre_test_point_view
      (fun e => match pre_diamond_occurrence e with Some u => [u] | None => [] end)
      (kill (pre_genkill (pre_expression pre_test_expression))) (fun _ _ => None))
      (fun _ => false) pre_diamond_occurrence)
    [PreX; PreY; PreZ] [PreX; PreY; PreZ] (fun _ => 1%positive) (fun x => [x])
    (fun _ _ => None) (fun be x => Some (pre_test_translate be x))
    (fun _ => false) (fun _ => false).

(** A trapping expression satisfies the full syntax laws with speculation classified false. *)
Example pre_trap_expression_laws : pre_expr_ssa_laws pre_test_value_encoding pre_trap_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - exact (pre_expr_reachable_blocks _ _ pre_test_expression_laws).
  - exact (pre_expr_reachable_points _ _ pre_test_expression_laws).
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - exact (pre_expr_entry_no_incoming _ _ pre_test_expression_laws).
  - exact (pre_expr_params_nodup _ _ pre_test_expression_laws).
  - exact (pre_expr_value_nodup _ _ pre_test_expression_laws).
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; destruct u; cbn; tauto|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    destruct e as [b|b|b|be], u; try destruct b;
      cbn in Hkill |- *; intuition congruence.
  - exact (pre_expr_def_home _ _ pre_test_expression_laws).
  - exact (pre_expr_cross_no_defs _ _ pre_test_expression_laws).
  - intros e u Hcomputed; apply (pre_expr_real_internal _ _ pre_test_expression_laws e u).
    apply pre_diamond_occurrence_original; exact Hcomputed.
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
  - intros be u v Hpure Htranslate; discriminate.
  - intros be u v env Hbe Hu Htranslate; reflexivity.
Qed.

(** Trapping evaluation returns no value, and the actual producer emits no motion for it. *)
Example pre_trap_no_motion :
  uval (pre_genkill (pre_expression pre_trap_expression)) tt PreZ = None /\
  ssa_pre_place pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_trap_expression =
      PrePlan Map.empty Map.empty Map.empty Map.empty.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * An executable client with distinct branch values *)

(** Source-visible fields and the target's private cache share a concrete state carrier. *)
Record pre_client_state : Type := PreClientState {
  client_pc : pre_frame_state;
  client_incoming : pre_test_block_edge;
  client_z : nat;
  client_result : option nat;
  client_cache : Map.t (pre_version pre_test_edge pre_test_value) nat;
  client_ending : ending;
  client_admin : option pre_test_edge
}.

Definition pre_client_version_encoding :=
  pre_version_encoding pre_test_edge_encoding pre_test_value_encoding.

Definition pre_client_read (s : pre_client_state) (u : pre_test_value) : nat :=
  match u with
  | PreX => 6
  | PreY => 8
  | PreZ => client_z s
  end.

Definition pre_client_eval (s : pre_client_state) (u : pre_test_value) : option nat :=
  Some (S (pre_client_read s u)).

Definition pre_client_cached (s : pre_client_state)
    (version : pre_version pre_test_edge pre_test_value) : option nat :=
  Map.get pre_client_version_encoding version (client_cache s).

Definition pre_client_initial (kind : ending) : pre_client_state :=
  PreClientState (PreEntry,PreBefore) PreExit 0 None Map.empty kind None.

(** Core agreement retains operands, result observations, incoming identity and all ending tags. *)
Definition pre_client_core (s t : pre_client_state) : Prop :=
  client_admin s = None /\ client_admin t = None /\ client_pc s = client_pc t /\
  client_incoming s = client_incoming t /\ client_z s = client_z t /\
  client_result s = client_result t /\ client_ending s = client_ending t.

Definition pre_client_set_option (version : pre_version pre_test_edge pre_test_value)
    (value : option nat) (cache : Map.t (pre_version pre_test_edge pre_test_value) nat) :=
  match value with
  | Some c => Map.set pre_client_version_encoding version c cache
  | None => Map.remove pre_client_version_encoding version cache
  end.

(** All phi reads use the old cache, including when several result slots are updated. *)
Definition pre_client_phi (p : pre_plan pre_test_edge pre_test_value)
    (incoming parameter : pre_test_edge)
    (cache : Map.t (pre_version pre_test_edge pre_test_value) nat) :=
  fold_left (fun updated u => pre_client_set_option (PreMerged parameter u)
    (pre_phi_update pre_test_edge_encoding pre_test_value_encoding p incoming parameter
      (fun version => Map.get pre_client_version_encoding version cache) (PreMerged parameter u))
    updated) [PreX;PreY;PreZ] cache.

Definition pre_client_source_value (e : pre_test_edge) (s : pre_client_state) : option nat :=
  match pre_diamond_occurrence e with
  | Some u => pre_client_eval s u
  | None => client_result s
  end.

(** A replacement reads its selected slot and performs no expression evaluation. *)
Definition pre_client_target_value (p : pre_plan pre_test_edge pre_test_value)
    (e : pre_test_edge) (s : pre_client_state) : option nat :=
  match pre_diamond_occurrence e with
  | Some u =>
    if pre_deleted pre_test_edge_encoding pre_test_value_encoding p e u then
      Some (match Map.get pre_test_edge_encoding e (pre_reload_versions p) with
        | Some version => match pre_client_cached s version with Some c => c | None => 0 end
        | None => 0
        end)
    else pre_client_eval s u
  | None => client_result s
  end.

Definition pre_client_advance (e : pre_test_edge) (s : pre_client_state) (result : option nat)
    (cache : Map.t (pre_version pre_test_edge pre_test_value) nat) (admin : option pre_test_edge) :=
  PreClientState (Graph.target pre_test_points e)
    (match e with PreCross be => be | _ => client_incoming s end)
    (match e with
     | PreBind PreJoin => match client_incoming s with
       | PreLeftJoin => pre_client_read s PreX
       | PreRightJoin => pre_client_read s PreY
       | _ => client_z s
       end
     | _ => client_z s
     end)
    result cache (client_ending s) admin.

Definition pre_client_source_exec (e : pre_test_edge) (s : pre_client_state) : pre_client_state :=
  pre_client_advance e s (pre_client_source_value e s) (client_cache s) None.

Definition pre_client_target_cache (p : pre_plan pre_test_edge pre_test_value)
    (e : pre_test_edge) (s : pre_client_state) :=
  let cache := match e with
    | PreBind _ => pre_client_phi p (PreCross (client_incoming s)) e (client_cache s)
    | _ => client_cache s
    end in
  match pre_diamond_occurrence e with
  | Some u =>
    if pre_deleted pre_test_edge_encoding pre_test_value_encoding p e u then cache
    else Map.set pre_client_version_encoding (PreComputed e u) (S (pre_client_read s u)) cache
  | None => cache
  end.

Definition pre_client_target_exec (p : pre_plan pre_test_edge pre_test_value)
    (e : pre_test_edge) (s : pre_client_state) : pre_client_state :=
  pre_client_advance e s (pre_client_target_value p e s) (pre_client_target_cache p e s) (Some e).

Definition pre_client_insert_cache (p : pre_plan pre_test_edge pre_test_value)
    (e : pre_test_edge) (s : pre_client_state) :=
  fold_left (fun cache u => Map.set pre_client_version_encoding (PreInserted e u)
    (S (pre_client_read s u)) cache)
    (FinSet.elements (live_index_get pre_test_edge_encoding e (pre_insertions p))) (client_cache s).

Definition pre_client_finish_exec (p : pre_plan pre_test_edge pre_test_value)
    (e : pre_test_edge) (s : pre_client_state) : pre_client_state :=
  PreClientState (Graph.target pre_test_points e) (client_incoming s) (client_z s) (client_result s)
    (pre_client_insert_cache p e s) (client_ending s) None.

(** The last operation emits the returned value, after either computation or cache reload. *)
Definition pre_client_trace (e : pre_test_edge) (s : pre_client_state) : list nat :=
  match e with
  | PreAgain PreJoin => match client_result s with Some c => [c] | None => [] end
  | _ => []
  end.

Inductive pre_client_source_step : pre_client_state -> list nat -> pre_client_state -> Prop :=
  | pre_client_source_edge : forall s e, client_admin s = None ->
      In e (Graph.out pre_test_points (client_pc s)) ->
      pre_client_source_step s (pre_client_trace e (pre_client_source_exec e s))
        (pre_client_source_exec e s).

Inductive pre_client_target_step (p : pre_plan pre_test_edge pre_test_value) :
    pre_client_state -> list nat -> pre_client_state -> Prop :=
  | pre_client_target_begin : forall s e, client_admin s = None ->
      In e (Graph.out pre_test_points (client_pc s)) ->
      pre_client_target_step p s (pre_client_trace e (pre_client_target_exec p e s))
        (pre_client_target_exec p e s)
  | pre_client_target_finish : forall s e, client_admin s = Some e ->
      pre_client_target_step p s [] (pre_client_finish_exec p e s).

Definition pre_client_source : semantics pre_client_state nat :=
  Semantics (fun s => exists kind, s = pre_client_initial kind) pre_client_source_step.

Definition pre_client_target (p : pre_plan pre_test_edge pre_test_value) :
    semantics pre_client_state nat :=
  Semantics (fun s => exists kind, s = pre_client_initial kind) (pre_client_target_step p).

Definition pre_client_endings : endings pre_client_state :=
  Endings
    (fun s => client_admin s = None /\ client_pc s = (PreJoin,PreAfter) /\
      client_ending s = EndFinal)
    (fun s => client_admin s = None /\ client_pc s = (PreJoin,PreAfter) /\
      client_ending s = EndTrap)
    (fun s => client_admin s = None /\ client_pc s = (PreJoin,PreAfter) /\
      client_ending s = EndStop).

Definition pre_client_source_graph :
    graph_view pre_client_state nat pre_frame_state pre_test_edge :=
  GraphView pre_test_points client_pc
    (fun s _ t e => In e (Graph.out pre_test_points (client_pc s)) /\
      Graph.target pre_test_points e = client_pc t) (fun _ _ _ => False).

Inductive pre_client_target_point : Type :=
  | ClientBoundary (n : pre_frame_state)
  | ClientAdmin (e : pre_test_edge).

Inductive pre_client_target_edge : Type :=
  | ClientBegin (e : pre_test_edge)
  | ClientFinish (e : pre_test_edge).

Definition pre_client_all_edges : list pre_test_edge :=
  map PreBind [PreEntry;PreLeft;PreRight;PreJoin] ++
  map PreCompute [PreEntry;PreLeft;PreRight;PreJoin] ++
  map PreAgain [PreEntry;PreLeft;PreRight;PreJoin] ++
  map PreCross [PreToLeft;PreToRight;PreLeftJoin;PreRightJoin;PreExit].

Definition pre_client_target_cfg : Graph.t pre_client_target_point pre_client_target_edge :=
  Graph.Make [ClientBoundary (PreEntry,PreBefore)]
    (map ClientBoundary (Graph.nodes pre_test_points) ++ map ClientAdmin pre_client_all_edges)
    (fun n => match n with
      | ClientBoundary n => map ClientBegin (Graph.out pre_test_points n)
      | ClientAdmin e => [ClientFinish e]
      end)
    (fun e => match e with
      | ClientBegin e => ClientBoundary (Graph.source pre_test_points e)
      | ClientFinish e => ClientAdmin e
      end)
    (fun e => match e with
      | ClientBegin e => ClientAdmin e
      | ClientFinish e => ClientBoundary (Graph.target pre_test_points e)
      end).

Definition pre_client_target_point_of (s : pre_client_state) : pre_client_target_point :=
  match client_admin s with
  | None => ClientBoundary (client_pc s)
  | Some e => ClientAdmin e
  end.

Definition pre_client_target_graph :
    graph_view pre_client_state nat pre_client_target_point pre_client_target_edge :=
  GraphView pre_client_target_cfg pre_client_target_point_of
    (fun s _ t e => In e (Graph.out pre_client_target_cfg (pre_client_target_point_of s)) /\
      Graph.target pre_client_target_cfg e = pre_client_target_point_of t)
    (fun _ _ _ => False).

Definition pre_client_origin (n : pre_client_target_point) :
    pre_origin pre_frame_state pre_test_edge :=
  match n with
  | ClientBoundary n => PrePoint n
  | ClientAdmin e => PreOnEdge e 1
  end.

Definition pre_client_project (e : pre_client_target_edge) : option pre_test_edge :=
  match e with
  | ClientBegin e => Some e
  | ClientFinish _ => None
  end.

Definition pre_client_realizer : pre_realizer pre_client_state nat pre_frame_state pre_test_edge
    pre_client_target_point pre_client_target_edge pre_test_value nat :=
  PreRealizer pre_client_source pre_client_endings pre_client_source_graph pre_client_target
    (fun _ => pre_client_endings) (fun _ => pre_client_target_graph)
    (fun _ => pre_client_origin) (fun _ => pre_client_project) pre_client_eval pre_client_cached
    pre_client_core (fun _ s => match client_admin s with None => 0 | Some _ => 1 end).

Local Lemma pre_client_set_option_get : forall version value cache query,
  Map.get pre_client_version_encoding query (pre_client_set_option version value cache) =
    if dfs_eq_dec pre_client_version_encoding query version then value
    else Map.get pre_client_version_encoding query cache.
Proof.
  intros version [c|] cache query; unfold pre_client_set_option;
    destruct (dfs_eq_dec pre_client_version_encoding query version) as [->|Hne].
  - apply Map.get_set_same.
  - apply Map.get_set_other; exact Hne.
  - apply Map.get_remove_same.
  - apply Map.get_remove_other; exact Hne.
Qed.

(** The concrete simultaneous cache update realizes the complete public phi operation. *)
Local Lemma pre_client_phi_get : forall p incoming parameter cache version,
  Map.get pre_client_version_encoding version (pre_client_phi p incoming parameter cache) =
    pre_phi_update pre_test_edge_encoding pre_test_value_encoding p incoming parameter
      (fun selected => Map.get pre_client_version_encoding selected cache) version.
Proof.
  intros p incoming parameter cache version; cbv [pre_client_phi fold_left].
  rewrite !pre_client_set_option_get.
  destruct (dfs_eq_dec pre_client_version_encoding version (PreMerged parameter PreZ))
    as [->|Hnot_z]; [reflexivity|].
  destruct (dfs_eq_dec pre_client_version_encoding version (PreMerged parameter PreY))
    as [->|Hnot_y]; [reflexivity|].
  destruct (dfs_eq_dec pre_client_version_encoding version (PreMerged parameter PreX))
    as [->|Hnot_x]; [reflexivity|].
  destruct version as [u|e u|e u|e u]; cbn [pre_phi_update]; try reflexivity.
  destruct (Pos.eqb (encode pre_test_edge_encoding e) (encode pre_test_edge_encoding parameter))
    eqn:Hparameter; [|reflexivity].
  apply Pos.eqb_eq, (encode_injective pre_test_edge_encoding) in Hparameter; subst e.
  destruct u; exfalso; [apply Hnot_x|apply Hnot_y|apply Hnot_z]; reflexivity.
Qed.

Local Lemma pre_client_phi_frame : forall p incoming parameter cache version,
  pre_version_written pre_test_edge_encoding parameter version = false ->
  Map.get pre_client_version_encoding version (pre_client_phi p incoming parameter cache) =
    Map.get pre_client_version_encoding version cache.
Proof.
  intros p incoming parameter cache [u|e u|e u|e u] Hwritten;
    rewrite pre_client_phi_get; try reflexivity.
  change (Pos.eqb (encode pre_test_edge_encoding parameter)
    (encode pre_test_edge_encoding e) = false) in Hwritten.
  unfold pre_phi_update; rewrite Pos.eqb_sym, Hwritten; reflexivity.
Qed.

Local Lemma pre_client_insert_fold_frame : forall e version expressions
    (cache : Map.t (pre_version pre_test_edge pre_test_value) nat),
  pre_version_written pre_test_edge_encoding e version = false ->
  forall (value : pre_test_value -> nat), Map.get pre_client_version_encoding version
    (fold_left (fun updated u => Map.set pre_client_version_encoding (PreInserted e u)
      (value u) updated) expressions cache) = Map.get pre_client_version_encoding version cache.
Proof.
  intros e version expressions; induction expressions as [|u expressions IH];
    intros cache Hwritten value; [reflexivity|].
  change (Map.get pre_client_version_encoding version
    (fold_left (fun updated u' => Map.set pre_client_version_encoding (PreInserted e u')
      (value u') updated) expressions
      (Map.set pre_client_version_encoding (PreInserted e u) (value u) cache)) =
    Map.get pre_client_version_encoding version cache).
  rewrite IH by exact Hwritten; apply Map.get_set_other.
  intro Heq; subst version; cbn [pre_version_written] in Hwritten.
  rewrite Pos.eqb_refl in Hwritten; discriminate.
Qed.

Local Lemma pre_client_source_graph_laws :
  graph_view_laws pre_client_source pre_client_source_graph.
Proof.
  constructor.
  - exact pre_test_points_wf.
  - intros s [kind ->]; cbn; tauto.
  - intros s l t Hreachable Hstep; destruct Hstep as [s e Hadmin Hout].
    right; exists e; split; [exact Hout|reflexivity].
  - intros s l t e Hreachable Hstep [Hout Htarget]; split; assumption.
  - intros s l t Hreachable Hstep Hfalse; contradiction.
Qed.

Local Lemma pre_client_all_edges_complete : forall e, In e pre_client_all_edges.
Proof.
  intros [b|b|b|be]; try destruct b; try destruct be; cbn; tauto.
Qed.

Local Lemma pre_client_all_edges_nodup : NoDup pre_client_all_edges.
Proof.
  cbn; repeat constructor; cbn; intuition discriminate.
Qed.

Local Lemma pre_client_target_in : forall e,
  In (Graph.target pre_test_points e) (Graph.nodes pre_test_points).
Proof.
  intros [b|b|b|be]; try destruct b; try destruct be; cbn; tauto.
Qed.

Local Lemma pre_client_target_cfg_wf : graph_wf pre_client_target_cfg.
Proof.
  constructor.
  - apply nodup_app_disjoint.
    + apply nodup_map_injective.
      * intros n n' Heq; congruence.
      * exact (nodes_nodup pre_test_points_wf).
    + apply nodup_map_injective; [intros e e' Heq; congruence|exact pre_client_all_edges_nodup].
    + intros n Hin Hother; apply in_map_iff in Hin, Hother.
      destruct Hin as [point [Heq Hin]], Hother as [edge [Hother Hin']]; congruence.
  - intros n [Heq|Hfalse]; [subst n|contradiction]; apply in_or_app; left.
    apply in_map; cbn; tauto.
  - intros [n|edge] te Hin.
    + apply in_map_iff in Hin; destruct Hin as [e [Heq Hout]]; subst te.
      change (ClientBoundary (Graph.source pre_test_points e) = ClientBoundary n).
      f_equal; exact (out_source pre_test_points_wf n e Hout).
    + destruct Hin as [Heq|Hfalse]; [subst te; reflexivity|contradiction].
  - intros [n|edge] te Hnode Hin.
    + apply in_map_iff in Hin; destruct Hin as [e [Heq Hout]]; subst te.
      change (In (ClientAdmin e) (map ClientBoundary (Graph.nodes pre_test_points) ++
        map ClientAdmin pre_client_all_edges)).
      apply in_or_app; right; apply in_map; apply pre_client_all_edges_complete.
    + destruct Hin as [Heq|Hfalse]; [subst te|contradiction].
      change (In (ClientBoundary (Graph.target pre_test_points edge))
        (map ClientBoundary (Graph.nodes pre_test_points) ++ map ClientAdmin pre_client_all_edges)).
      apply in_or_app; left.
      apply in_map; apply pre_client_target_in.
Qed.

Local Lemma pre_client_target_graph_laws : forall p,
  graph_view_laws (pre_client_target p) pre_client_target_graph.
Proof.
  intro p; constructor.
  - exact pre_client_target_cfg_wf.
  - intros s [kind ->]; cbn; tauto.
  - intros s l t Hreachable Hstep; destruct Hstep as [s e Hadmin Hout|s e Hadmin].
    + right; exists (ClientBegin e); split.
      * unfold pre_client_target_point_of; rewrite Hadmin; apply in_map; exact Hout.
      * reflexivity.
    + right; exists (ClientFinish e); split.
      * unfold pre_client_target_point_of; rewrite Hadmin; left; reflexivity.
      * reflexivity.
  - intros s l t e Hreachable Hstep [Hout Htarget]; split; assumption.
  - intros s l t Hreachable Hstep Hfalse; contradiction.
Qed.

Local Lemma pre_client_out_target_unique : forall n e e',
  In e (Graph.out pre_test_points n) -> In e' (Graph.out pre_test_points n) ->
  Graph.target pre_test_points e = Graph.target pre_test_points e' -> e = e'.
Proof.
  intros [b stage] e e' Hout Hout' Htarget; destruct b, stage; cbn in Hout, Hout';
    intuition subst; cbn in Htarget; congruence.
Qed.

Local Lemma pre_client_taken_source : forall s e edge,
  client_admin s = None -> In e (Graph.out pre_test_points (client_pc s)) ->
  taken pre_client_source_graph s (pre_client_trace e (pre_client_source_exec e s))
    (pre_client_source_exec e s) edge -> edge = e.
Proof.
  intros s e edge Hadmin Hout [Hout' Htarget].
  eapply pre_client_out_target_unique; [exact Hout'|exact Hout|exact Htarget].
Qed.

Local Lemma pre_client_source_endpoint : forall s l s' e,
  pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
  s' = pre_client_source_exec e s.
Proof.
  intros s l s' e Hstep Htaken; destruct Hstep as [s d Hadmin Hout].
  pose proof (pre_client_taken_source s d e Hadmin Hout Htaken) as ->; reflexivity.
Qed.

Definition pre_client_ssa_view : ssa_view pre_client_state nat pre_test_block pre_test_block_edge
    pre_test_value unit nat :=
  SsaView (GraphView pre_test_blocks (fun s => fst (client_pc s))
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (def pre_test_view) (home pre_test_view) (params pre_test_view) (edge_args pre_test_view)
    (edge_guard pre_test_view) (fun s u => Some (pre_client_read s u))
    (op_eval pre_test_view) (truth pre_test_view).

Definition pre_client_expression : pre_expr_ssa pre_client_state nat pre_test_block
    pre_test_block_edge pre_frame_state pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_ssa pre_client_ssa_view
    (PreExpressionView (GenKillView pre_client_source_graph
      (fun e => match pre_diamond_occurrence e with Some u => [u] | None => [] end)
      (kill (pre_genkill (pre_expression pre_test_expression))) pre_client_eval)
      (fun _ => true) pre_diamond_occurrence)
    [PreX;PreY;PreZ] [PreX;PreY;PreZ] (fun _ => 1%positive) (fun u => [u])
    (fun u env => option_map S (env u)) (fun be u => Some (pre_test_translate be u))
    (fun _ => false) (fun n => match n with (PreJoin,PreAfter) => true | _ => false end).

(** The concrete varying-value client supplies every adopted expression and graph premise. *)
Example pre_client_expression_laws :
  pre_expr_ssa_laws pre_test_value_encoding pre_client_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - exact (pre_expr_reachable_blocks _ _ pre_test_expression_laws).
  - exact (pre_expr_reachable_points _ _ pre_test_expression_laws).
  - exists PreEntry, (PreEntry,PreBefore); repeat split; reflexivity.
  - exact (pre_expr_entry_no_incoming _ _ pre_test_expression_laws).
  - exact (pre_expr_params_nodup _ _ pre_test_expression_laws).
  - exact (pre_expr_value_nodup _ _ pre_test_expression_laws).
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; destruct u; cbn; tauto|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u (or_introl eq_refl)); reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    destruct e as [b|b|b|be], u; try destruct b;
      cbn in Hkill |- *; intuition congruence.
  - exact (pre_expr_def_home _ _ pre_test_expression_laws).
  - exact (pre_expr_cross_no_defs _ _ pre_test_expression_laws).
  - intros e u Hcomputed; apply (pre_expr_real_internal _ _ pre_test_expression_laws e u).
    apply pre_diamond_occurrence_original; exact Hcomputed.
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; destruct be, u; cbn in Htranslate;
      inversion Htranslate; subst v; reflexivity.
Qed.

Definition pre_client_plan := ssa_pre_place pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
  pre_test_value_encoding pre_client_expression.

(** Runtime valuations do not alter the actual insertion, join and deletion decisions. *)
Example pre_client_plan_agrees : pre_client_plan = pre_diamond_plan.
Proof.
  vm_compute; reflexivity.
Qed.

Local Lemma pre_client_inserted : forall e u,
  pre_inserted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = true <->
    e = PreCross PreRightJoin /\ u = PreY.
Proof.
  intros [b|b|b|be] u; try destruct b; try destruct be; destruct u;
    vm_compute; intuition congruence.
Qed.

Local Lemma pre_client_deleted : forall e u,
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = true <->
    (e = PreAgain PreLeft /\ u = PreX) \/
    ((e = PreCompute PreJoin \/ e = PreAgain PreJoin) /\ u = PreZ).
Proof.
  intros [b|b|b|be] u; try destruct b; try destruct be; destruct u;
    vm_compute; intuition congruence.
Qed.

Local Lemma pre_client_kept_computation : forall e u,
  pre_diamond_occurrence e = Some u ->
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = false ->
  e = PreCompute PreLeft /\ u = PreX.
Proof.
  intros [b|b|b|be] u Hcomputed Hkept; try destruct b; try destruct be; destruct u;
    vm_compute in Hcomputed, Hkept; intuition congruence.
Qed.

Local Lemma pre_client_boundary : forall p n s,
  pre_boundary pre_client_realizer p n s <-> client_admin s = None /\ client_pc s = n.
Proof.
  intros p n s; change (pre_client_origin (pre_client_target_point_of s) = PrePoint n <->
    client_admin s = None /\ client_pc s = n).
  unfold pre_client_target_point_of; destruct (client_admin s) eqn:Hadmin;
    cbn [pre_client_origin]; intuition congruence.
Qed.

Local Lemma pre_client_admin_point : forall p e s,
  pre_admin pre_client_realizer p e s <-> client_admin s = Some e.
Proof.
  intros p e s; unfold pre_admin.
  change ((exists k, pre_client_origin (pre_client_target_point_of s) = PreOnEdge e k) <->
    client_admin s = Some e).
  unfold pre_client_target_point_of; destruct (client_admin s) as [d|] eqn:Hadmin;
    cbn [pre_client_origin]; split.
  - intros [k Heq]; inversion Heq; reflexivity.
  - intro Heq; injection Heq as ->; exists 1; reflexivity.
  - intros [k Hfalse]; discriminate.
  - intro Hfalse; discriminate.
Qed.

Local Lemma pre_client_finish_boundary : forall p e s t n,
  pre_boundary pre_client_realizer p n s -> pre_finish pre_client_realizer p e s t -> t = s.
Proof.
  intros p e s t n Hboundary Hfinish; destruct Hfinish as [s Htarget|
    s q t te Hadmin Hstep Htaken Hproject Hfinish].
  - reflexivity.
  - apply pre_client_boundary in Hboundary; destruct Hboundary as [Hnone Hpoint].
    apply pre_client_admin_point in Hadmin; congruence.
Qed.

Local Lemma pre_client_finish_admin : forall p e s t,
  client_admin s = Some e -> pre_finish pre_client_realizer p e s t ->
  t = pre_client_finish_exec p e s.
Proof.
  intros p e s t Hadmin Hfinish; destruct Hfinish as [s Hboundary|
    s q t te Hadmin' Hstep Htaken Hproject Htail].
  - apply pre_client_boundary in Hboundary; destruct Hboundary as [Hnone Hpoint]; congruence.
  - destruct Hstep as [s d Hnone Hout|s d Hsome]; [congruence|].
    assert (d = e) by congruence; subst d.
    eapply pre_client_finish_boundary; [|exact Htail].
    apply pre_client_boundary; split; reflexivity.
Qed.

Local Lemma pre_client_finish_actual : forall p e s,
  pre_finish pre_client_realizer p e (pre_client_target_exec p e s)
    (pre_client_finish_exec p e (pre_client_target_exec p e s)).
Proof.
  intros p e s; eapply pre_finish_admin with (te := ClientFinish e)
    (t1 := pre_client_finish_exec p e (pre_client_target_exec p e s)).
  - apply pre_client_admin_point; reflexivity.
  - apply pre_client_target_finish; reflexivity.
  - split; [left; reflexivity|reflexivity].
  - reflexivity.
  - apply pre_finish_boundary, pre_client_boundary; split; reflexivity.
Qed.

(** A complete client macro includes its actual primitive and exactly one administrative step. *)
Local Lemma pre_client_macro : forall p e s l t,
  pre_macro_step pre_client_realizer p e s l t <->
    client_admin s = None /\ In e (Graph.out pre_test_points (client_pc s)) /\
    l = pre_client_trace e (pre_client_target_exec p e s) /\
    t = pre_client_finish_exec p e (pre_client_target_exec p e s).
Proof.
  intros p e s l t; split.
  - intros [Hboundary [q [te [Hstep [Htaken [Hproject Hfinish]]]]]].
    apply pre_client_boundary in Hboundary; destruct Hboundary as [Hnone Hsource].
    destruct Hstep as [s d Hadmin Hout|s d Hadmin]; [|congruence].
    destruct te as [edge|edge]; [|discriminate].
    change (Some edge = Some e) in Hproject; injection Hproject as ->.
    destruct Htaken as [Hout' Htarget].
    change (ClientAdmin e = ClientAdmin d) in Htarget; injection Htarget as ->.
    split; [exact Hnone|]; split; [exact Hout|]; split; [reflexivity|].
    eapply pre_client_finish_admin; [reflexivity|exact Hfinish].
  - intros [Hnone [Hout [-> ->]]]; split.
    + apply pre_client_boundary; split; [exact Hnone|].
      symmetry; apply (out_source pre_test_points_wf); exact Hout.
    + exists (pre_client_target_exec p e s), (ClientBegin e); split.
      * apply pre_client_target_begin; assumption.
      * split.
        -- split.
           ++ unfold pre_client_target_point_of; rewrite Hnone; apply in_map; exact Hout.
           ++ reflexivity.
        -- split; [reflexivity|apply pre_client_finish_actual].
Qed.

Local Lemma pre_client_core_eval : forall s t u,
  pre_client_core s t -> pre_client_eval s u = pre_client_eval t u.
Proof.
  intros s t u [_ [_ [_ [_ [Hz Hrest]]]]]; destruct u; try reflexivity.
  unfold pre_client_eval, pre_client_read; rewrite Hz; reflexivity.
Qed.

Local Lemma pre_client_core_advance :
  forall p e s t source_value target_value source_cache target_cache,
  pre_client_core s t -> source_value = target_value ->
  pre_client_core (pre_client_advance e s source_value source_cache None)
    (pre_client_finish_exec p e (pre_client_advance e t target_value target_cache (Some e))).
Proof.
  intros p e s t source_value target_value source_cache target_cache
    [Hs [Ht [Hpoint [Hincoming [Hz [Hresult Hkind]]]]]] Hvalue.
  unfold pre_client_core, pre_client_finish_exec, pre_client_advance;
    cbn [client_admin client_pc client_incoming client_z client_result client_ending].
  rewrite Hincoming, Hz, Hkind, Hvalue; repeat split; reflexivity.
Qed.

Local Lemma pre_client_trace_values : forall p e s t,
  pre_client_source_value e s = pre_client_target_value p e t ->
  pre_client_trace e (pre_client_source_exec e s) =
    pre_client_trace e (pre_client_target_exec p e t).
Proof.
  intros p [b|b|b|be] s t Hvalue; try destruct b;
    cbn [pre_client_trace]; try reflexivity.
  change (match pre_client_source_value (PreAgain PreJoin) s with
    | Some c => [c]
    | None => []
    end = match pre_client_target_value p (PreAgain PreJoin) t with
    | Some c => [c]
    | None => []
    end).
  rewrite Hvalue; reflexivity.
Qed.

Local Lemma pre_client_kept_values : forall p e s t,
  pre_client_core s t ->
  (forall u, pre_deleted pre_test_edge_encoding pre_test_value_encoding p e u = false) ->
  pre_client_source_value e s = pre_client_target_value p e t.
Proof.
  intros p e s t Hcore Hkept; unfold pre_client_source_value, pre_client_target_value.
  destruct (pre_diamond_occurrence e) as [u|] eqn:Hcomputed.
  - rewrite Hkept; apply pre_client_core_eval; exact Hcore.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hcore)))))).
Qed.

Local Lemma pre_client_replaced_values : forall p e u version s t,
  pre_diamond_occurrence e = Some u ->
  pre_deleted pre_test_edge_encoding pre_test_value_encoding p e u = true ->
  Map.get pre_test_edge_encoding e (pre_reload_versions p) = Some version ->
  pre_client_cached t version = pre_client_eval s u ->
  pre_client_source_value e s = pre_client_target_value p e t.
Proof.
  intros p e u version s t Hcomputed Hdeleted Hreload Hcache.
  unfold pre_client_source_value, pre_client_target_value.
  rewrite Hcomputed, Hdeleted, Hreload, Hcache; reflexivity.
Qed.

Local Lemma pre_client_primitive_match : forall p s t e,
  pre_client_core s t -> pre_client_source_value e s = pre_client_target_value p e t ->
  (forall l s', pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
    exists t', pre_macro_step pre_client_realizer p e t l t' /\ pre_client_core s' t') /\
  (forall l t', pre_macro_step pre_client_realizer p e t l t' ->
    exists s', pre_client_source_step s l s' /\ taken pre_client_source_graph s l s' e /\
      pre_client_core s' t').
Proof.
  intros p s t e Hcore Hvalue; pose proof Hcore as [Hsource_admin [Htarget_admin [Hpoint Hrest]]].
  pose proof (pre_client_trace_values p e s t Hvalue) as Htrace; split.
  - intros l s' Hstep Htaken; destruct Hstep as [s d Hadmin Hout].
    pose proof (pre_client_taken_source s d e Hadmin Hout Htaken) as ->.
    exists (pre_client_finish_exec p d (pre_client_target_exec p d t)); split.
    + apply pre_client_macro; split; [exact Htarget_admin|].
      split; [rewrite <- Hpoint; exact Hout|]; split; [exact Htrace|reflexivity].
    + apply pre_client_core_advance; assumption.
  - intros l t' Hmacro; apply pre_client_macro in Hmacro.
    destruct Hmacro as [Ht [Hout [-> ->]]]; exists (pre_client_source_exec e s); split.
    + rewrite <- Htrace; apply pre_client_source_edge; [exact Hsource_admin|].
      rewrite Hpoint; exact Hout.
    + split.
      * split; [rewrite Hpoint; exact Hout|reflexivity].
      * apply pre_client_core_advance; assumption.
Qed.

(** The executable source preserves every generated expression across its actual edge. *)
Local Lemma pre_client_gen_value : forall s l s' e u,
  pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
  In u (gen (pre_genkill (pre_expression pre_client_expression)) e) ->
  pre_client_eval s' u = pre_client_eval s u.
Proof.
  intros s l s' e u Hstep Htaken Hgen; destruct Hstep as [s d Hadmin Hout].
  pose proof (pre_client_taken_source s d e Hadmin Hout Htaken) as ->.
  destruct d as [b|b|b|be]; try destruct b;
    cbn [pre_client_expression pre_expression pre_genkill gen pre_diamond_occurrence] in Hgen;
    try contradiction; destruct Hgen as [Heq|Hfalse]; try contradiction;
    subst u; reflexivity.
Qed.

(** The parameter step changes only its killed join expression; all other reads are framed. *)
Local Lemma pre_client_kill_frame : forall s l s' e u,
  pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
  kill (pre_genkill (pre_expression pre_client_expression)) e u = false ->
  pre_client_eval s' u = pre_client_eval s u.
Proof.
  intros s l s' e u Hstep Htaken Hkill; destruct Hstep as [s d Hadmin Hout].
  pose proof (pre_client_taken_source s d e Hadmin Hout Htaken) as ->.
  destruct d as [b|b|b|be]; try destruct b; destruct u; try reflexivity;
    discriminate Hkill.
Qed.

Local Lemma pre_client_projection : forall p t l t',
  pre_client_target_step p t l t' ->
  exists te, taken pre_client_target_graph t l t' te /\
    match pre_client_origin (pre_client_target_point_of t) with
    | PrePoint n => exists e, pre_client_project te = Some e /\
        In e (Graph.out pre_test_points n) /\
        (pre_boundary pre_client_realizer p (Graph.target pre_test_points e) t' \/
         pre_admin pre_client_realizer p e t')
    | PreOnEdge e _ => pre_client_project te = None /\
        (pre_admin pre_client_realizer p e t' \/
         pre_boundary pre_client_realizer p (Graph.target pre_test_points e) t')
    end.
Proof.
  intros p t l t' Hstep; destruct Hstep as [t e Hadmin Hout|t e Hadmin].
  - exists (ClientBegin e); split.
    + split.
      * unfold pre_client_target_point_of; rewrite Hadmin; apply in_map; exact Hout.
      * reflexivity.
    + unfold pre_client_target_point_of; rewrite Hadmin; cbn [pre_client_origin].
      exists e; split; [reflexivity|]; split; [exact Hout|].
      right; apply pre_client_admin_point; reflexivity.
  - exists (ClientFinish e); split.
    + split; [unfold pre_client_target_point_of; rewrite Hadmin; left; reflexivity|reflexivity].
    + unfold pre_client_target_point_of; rewrite Hadmin; cbn [pre_client_origin].
      split; [reflexivity|]; right; apply pre_client_boundary; split; reflexivity.
Qed.

Local Lemma pre_client_cache_frame : forall p e t l t' version,
  pre_macro_step pre_client_realizer p e t l t' ->
  pre_version_written pre_test_edge_encoding e version = false ->
  pre_client_cached t' version = pre_client_cached t version.
Proof.
  intros p e t l t' version Hmacro Hwritten; apply pre_client_macro in Hmacro.
  destruct Hmacro as [Hadmin [Hout [-> ->]]].
  unfold pre_client_cached, pre_client_finish_exec, pre_client_insert_cache;
    cbn [client_cache].
  rewrite pre_client_insert_fold_frame by exact Hwritten.
  unfold pre_client_target_exec; cbn [pre_client_advance client_cache].
  unfold pre_client_target_cache.
  destruct (pre_diamond_occurrence e) as [u|] eqn:Hcomputed.
  - destruct (pre_deleted pre_test_edge_encoding pre_test_value_encoding p e u).
    + destruct e as [b|b|b|be]; try reflexivity.
      apply pre_client_phi_frame; exact Hwritten.
    + rewrite Map.get_set_other.
      * destruct e as [b|b|b|be]; try reflexivity.
        apply pre_client_phi_frame; exact Hwritten.
      * intro Heq; subst version; cbn [pre_version_written] in Hwritten.
        rewrite Pos.eqb_refl in Hwritten; discriminate.
  - destruct e as [b|b|b|be]; try reflexivity.
    apply pre_client_phi_frame; exact Hwritten.
Qed.

Local Lemma pre_client_insert_row : forall e,
  FinSet.elements (live_index_get pre_test_edge_encoding e (pre_insertions pre_client_plan)) =
    match e with PreCross PreRightJoin => [PreY] | _ => [] end.
Proof.
  intros [b|b|b|be]; try destruct b; try destruct be; vm_compute; reflexivity.
Qed.

Local Lemma pre_client_insert_cache_agrees : forall e s,
  pre_client_insert_cache pre_client_plan e s =
    match e with
    | PreCross PreRightJoin => Map.set pre_client_version_encoding
        (PreInserted (PreCross PreRightJoin) PreY) 9 (client_cache s)
    | _ => client_cache s
    end.
Proof.
  intros e s; unfold pre_client_insert_cache; rewrite pre_client_insert_row.
  destruct e as [b|b|b|be]; try destruct be; reflexivity.
Qed.

(** The only newly inserted computation uses the right predecessor's translated operand. *)
Local Lemma pre_client_insert : forall s t e u l s' t',
  pre_inserted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = true ->
  pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
  pre_macro_step pre_client_realizer pre_client_plan e t l t' ->
  pre_client_cached t' (PreInserted e u) = pre_client_eval s' u.
Proof.
  intros s t e u l s' t' Hinsert Hstep Htaken Hmacro.
  apply pre_client_inserted in Hinsert; destruct Hinsert as [-> ->].
  apply pre_client_macro in Hmacro; destruct Hmacro as [Hadmin [Hout [Htrace ->]]].
  unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
  rewrite pre_client_insert_cache_agrees, Map.get_set_same; reflexivity.
Qed.

(** A kept left-branch operation stores its computed value, before any later reload. *)
Local Lemma pre_client_compute : forall s t e u l s' t',
  pre_diamond_occurrence e = Some u ->
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = false ->
  pre_client_source_step s l s' -> taken pre_client_source_graph s l s' e ->
  pre_macro_step pre_client_realizer pre_client_plan e t l t' ->
  pre_client_cached t' (PreComputed e u) = pre_client_eval s u.
Proof.
  intros s t e u l s' t' Hcomputed Hkept Hstep Htaken Hmacro.
  destruct (pre_client_kept_computation e u Hcomputed Hkept) as [-> ->].
  apply pre_client_macro in Hmacro; destruct Hmacro as [Hadmin [Hout [Htrace ->]]].
  unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
  rewrite pre_client_insert_cache_agrees.
  change (Map.get pre_client_version_encoding (PreComputed (PreCompute PreLeft) PreX)
    (Map.set pre_client_version_encoding (PreComputed (PreCompute PreLeft) PreX) 7
      (client_cache t)) = Some 7).
  apply Map.get_set_same.
Qed.

Local Lemma pre_client_cross_record : forall p be t l t',
  pre_macro_step pre_client_realizer p (PreCross be) t l t' -> client_incoming t' = be.
Proof.
  intros p be t l t' Hmacro; apply pre_client_macro in Hmacro.
  destruct Hmacro as [Hadmin [Hout [Htrace ->]]]; reflexivity.
Qed.

Local Lemma pre_client_phi_macro : forall b be t l t' version,
  client_incoming t = be ->
  pre_macro_step pre_client_realizer pre_client_plan (PreBind b) t l t' ->
  pre_client_cached t' version =
    pre_phi_update pre_test_edge_encoding pre_test_value_encoding pre_client_plan
      (PreCross be) (PreBind b) (pre_client_cached t) version.
Proof.
  intros b be t l t' version Hincoming Hmacro; apply pre_client_macro in Hmacro.
  destruct Hmacro as [Hadmin [Hout [Htrace ->]]].
  unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
  rewrite pre_client_insert_cache_agrees.
  change (Map.get pre_client_version_encoding version
    (pre_client_phi pre_client_plan (PreCross (client_incoming t)) (PreBind b) (client_cache t)) =
      pre_phi_update pre_test_edge_encoding pre_test_value_encoding pre_client_plan
        (PreCross be) (PreBind b)
        (fun selected => Map.get pre_client_version_encoding selected (client_cache t)) version).
  rewrite Hincoming; apply pre_client_phi_get.
Qed.

(** Actual incoming edge identity is retained through the simultaneous join update. *)
Local Lemma pre_client_phi_select : forall t0 t1 t2 be incoming l0 l version,
  Map.get pre_test_block_edge_encoding be
    (pre_point_edge_index pre_test_block_edge_encoding pre_test_ssa) = Some incoming ->
  pre_macro_step pre_client_realizer pre_client_plan incoming t0 l0 t1 ->
  pre_macro_step pre_client_realizer pre_client_plan
    (PreBind (Graph.target pre_test_blocks be)) t1 l t2 ->
  pre_client_cached t2 version =
    pre_phi_update pre_test_edge_encoding pre_test_value_encoding pre_client_plan incoming
      (PreBind (Graph.target pre_test_blocks be)) (pre_client_cached t1) version.
Proof.
  intros t0 t1 t2 be incoming l0 l version Hindex Hcross Hparameter.
  assert (incoming = PreCross be) as ->.
  { destruct be; vm_compute in Hindex; congruence. }
  eapply pre_client_phi_macro; [eapply pre_client_cross_record; exact Hcross|exact Hparameter].
Qed.

Local Lemma pre_client_progress : forall p t e,
  pre_admin pre_client_realizer p e t ->
  ~ final pre_client_endings t /\ ~ trapped pre_client_endings t /\
  ~ stopped pre_client_endings t /\
  ~ stuck (pre_client_target p) pre_client_endings t /\ running (pre_client_target p) t /\
  forall l t', pre_client_target_step p t l t' -> l = [] /\
    pre_boundary pre_client_realizer p (Graph.target pre_test_points e) t'.
Proof.
  intros p t e Hadmin; apply pre_client_admin_point in Hadmin.
  assert (running (pre_client_target p) t) as Hrunning.
  { exists [], (pre_client_finish_exec p e t); apply pre_client_target_finish; exact Hadmin. }
  split; [intros [Hnone Hrest]; congruence|].
  split; [intros [Hnone Hrest]; congruence|].
  split; [intros [Hnone Hrest]; congruence|].
  split; [intros [Hnot_running Hrest]; contradiction|].
  split; [exact Hrunning|].
  intros l t' Hstep; destruct Hstep as [t d Hnone Hout|t d Hsome]; [congruence|].
  assert (d = e) as -> by congruence; split; [reflexivity|].
  apply pre_client_boundary; split; reflexivity.
Qed.

Local Lemma pre_client_running : forall p s t,
  pre_client_core s t -> (running pre_client_source s <-> running (pre_client_target p) t).
Proof.
  intros p s t [Hs [Ht [Hpoint Hrest]]]; split.
  - intros [l [s' Hstep]]; destruct Hstep as [s e Hadmin Hout].
    exists (pre_client_trace e (pre_client_target_exec p e t)), (pre_client_target_exec p e t).
    apply pre_client_target_begin; [exact Ht|rewrite <- Hpoint; exact Hout].
  - intros [l [t' Hstep]]; destruct Hstep as [t e Hadmin Hout|t e Hadmin]; [|congruence].
    exists (pre_client_trace e (pre_client_source_exec e s)), (pre_client_source_exec e s).
    apply pre_client_source_edge; [exact Hs|rewrite Hpoint; exact Hout].
Qed.

(** Core equality preserves declared endings and stuck, including the absence of a transition. *)
Local Lemma pre_client_endings_agree : forall p s t k,
  pre_client_core s t ->
  (ends_as pre_client_source pre_client_endings k s <->
    ends_as (pre_client_target p) pre_client_endings k t).
Proof.
  intros p s t k Hcore; pose proof (pre_client_running p s t Hcore) as Hrunning.
  destruct Hcore as [Hs [Ht [Hpoint [Hincoming [Hz [Hresult Hkind]]]]]].
  destruct k; cbn [ends_as]; try unfold stuck;
    cbn [pre_client_endings final trapped stopped];
    rewrite ?Hrunning, ?Hs, ?Ht, ?Hpoint, ?Hkind; tauto.
Qed.

Local Lemma pre_client_source_admin : forall s,
  reachable_state pre_client_source s -> client_admin s = None.
Proof.
  assert (forall s0 tr s, exec pre_client_source s0 tr s ->
    client_admin s0 = None -> client_admin s = None) as Hframe.
  { intros s0 tr s Hrun; induction Hrun as [s|s l t tr u Hstep Hrun IH]; intro Hnone.
    - exact Hnone.
    - apply IH; destruct Hstep; reflexivity. }
  intros s [s0 [tr [[kind ->] Hrun]]]; eapply Hframe; [exact Hrun|reflexivity].
Qed.

Local Lemma pre_client_out_nonexit : forall n,
  n <> (PreJoin,PreAfter) -> exists e, In e (Graph.out pre_test_points n).
Proof.
  intros [b stage] Hnot_exit; destruct b, stage; cbn in Hnot_exit |- *;
    try (eexists; left; reflexivity); exfalso; apply Hnot_exit; reflexivity.
Qed.

(** The resource, trap, normal and stuck endings all occur at the actual source exit. *)
Example pre_client_exit_covered : pre_exit_covered pre_client_expression pre_client_realizer.
Proof.
  intros s k Hreachable Hending.
  assert (client_pc s = (PreJoin,PreAfter)) as Hexit.
  { destruct k; cbn [ends_as pre_client_realizer pre_source pre_source_end
      pre_client_endings final trapped stopped] in Hending.
    - exact (proj1 (proj2 Hending)).
    - exact (proj1 (proj2 Hending)).
    - exact (proj1 (proj2 Hending)).
    - destruct (dfs_eq_dec pre_test_point_encoding (client_pc s) (PreJoin,PreAfter))
        as [Heq|Hne]; [exact Heq|].
      destruct (pre_client_out_nonexit (client_pc s) Hne) as [e Hout].
      exfalso; apply (proj1 Hending).
      exists (pre_client_trace e (pre_client_source_exec e s)), (pre_client_source_exec e s).
      apply pre_client_source_edge; [apply pre_client_source_admin; exact Hreachable|exact Hout]. }
  change (match client_pc s with (PreJoin,PreAfter) => true | _ => false end = true).
  rewrite Hexit; reflexivity.
Qed.

(** Each executable parameter edge implements the actual incoming edge's source substitution. *)
Example pre_client_phi_source : pre_phi_source_laws pre_test_block_edge_encoding
  pre_test_value_encoding pre_client_expression pre_client_realizer.
Proof.
  intros be e s0 l0 s1 l1 s2 Hreachable Hindex Hstep Htaken Hparameter Hparameter_taken x.
  assert (e = PreCross be) as He.
  { destruct be; vm_compute in Hindex; congruence. }
  subst e.
  pose proof (pre_client_source_endpoint s0 l0 s1 (PreCross be) Hstep Htaken) as Hfirst.
  pose proof (pre_client_source_endpoint s1 l1 s2 (PreBind (Graph.target pre_test_blocks be))
    Hparameter Hparameter_taken) as Hsecond.
  subst s2 s1; destruct be, x; reflexivity.
Qed.

Local Lemma pre_client_deleted_computation : forall e u,
  pre_deleted pre_test_edge_encoding pre_test_value_encoding pre_client_plan e u = true ->
  pre_diamond_occurrence e = Some u.
Proof.
  intros e u Hdeleted; apply pre_client_deleted in Hdeleted.
  destruct Hdeleted as [[He Hu]|[He Hu]]; subst u.
  - subst e; reflexivity.
  - destruct He as [He|He]; subst e; reflexivity.
Qed.

(** This actual insertion/join/deletion client discharges every current local realization law. *)
Example pre_client_local_laws : pre_local_laws pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
  pre_client_expression (pre_expression pre_client_expression)
  (pre_initial_available pre_client_expression) pre_client_realizer pre_client_plan.
Proof.
  constructor.
  - split; [reflexivity|]; split; [reflexivity|].
    split; [exact pre_client_source_graph_laws|].
    split; [apply pre_client_target_graph_laws|].
    split; [intros s l s' Hfalse; exact Hfalse|].
    split; [intros t l t' Hfalse; exact Hfalse|].
    intros t l t' Hreachable Hstep; eapply pre_client_projection; exact Hstep.
  - split; [intros s u; reflexivity|].
    split; [exact pre_client_core_eval|].
    split; [intros s u Hreachable Hpure; exists (S (pre_client_read s u)); reflexivity|].
    intros e u Hcomputed; change (pre_diamond_occurrence e = Some u) in Hcomputed.
    change (In u (match pre_diamond_occurrence e with
      Some x => [x] | None => [] end)); rewrite Hcomputed; left; reflexivity.
  - intros s l s' e u Hreachable Hstep Htaken Hgen.
    eapply pre_client_gen_value; eassumption.
  - intros s l s' e u Hreachable Hstep Htaken Hkill.
    eapply pre_client_kill_frame; eassumption.
  - intros s t e Hsource Htarget Hpoint Hboundary Hcore Hkept.
    apply pre_client_primitive_match; [exact Hcore|].
    apply pre_client_kept_values; assumption.
  - intros s t e u l s' t' Hsource Htarget Hcore Hinsert Hstep Htaken Hmacro.
    eapply pre_client_insert; eassumption.
  - intros s t e u version Hsource Htarget Hpoint Hboundary Hcore Hdeleted Hreload Hcache.
    apply pre_client_primitive_match; [exact Hcore|].
    eapply pre_client_replaced_values; try eassumption.
    apply pre_client_deleted_computation; exact Hdeleted.
  - intros s t e l s' t' version Hsource Htarget Hpoint Hboundary Hstep Htaken Hmacro Hwritten.
    eapply pre_client_cache_frame; eassumption.
  - intros s t e u l s' t' Hsource Htarget Hcomputed Hkept Hstep Htaken Hmacro.
    eapply pre_client_compute; eassumption.
  - intros s t u Hsource Htarget Hcore Hinitial; discriminate.
  - intros s0 t0 s1 t1 s2 t2 be incoming l0 l version Hsource Htarget Hindex
      Hcross Hcross_taken Hcross_macro Hparameter Hparameter_taken Hparameter_macro.
    eapply pre_client_phi_select; eassumption.
  - intros t e Hreachable Hadmin.
    destruct (pre_client_progress pre_client_plan t e Hadmin) as
      [Hfinal [Htrap [Hstop [Hstuck [Hrunning Hstep]]]]].
    split; [exact Hfinal|]; split; [exact Htrap|]; split; [exact Hstop|].
    split; [exact Hstuck|]; split; [exact Hrunning|].
    intros l t' Htarget; destruct (Hstep l t' Htarget) as [Htrace Hboundary].
    split; [exact Htrace|left; exact Hboundary].
  - intros s t n k Hsource Htarget Hpoint Hboundary Hcore.
    apply pre_client_endings_agree; exact Hcore.
Qed.

(** The actual source and target executions retain the right/left branch choice. *)
Definition pre_client_edges (right : bool) : list pre_test_edge :=
  let branch := if right then PreRight else PreLeft in
  [PreBind PreEntry; PreCompute PreEntry; PreAgain PreEntry;
   PreCross (if right then PreToRight else PreToLeft);
   PreBind branch; PreCompute branch; PreAgain branch;
   PreCross (if right then PreRightJoin else PreLeftJoin);
   PreBind PreJoin; PreCompute PreJoin; PreAgain PreJoin].

Fixpoint pre_client_source_walk (s : pre_client_state) (edges : list pre_test_edge) :
    list nat * pre_client_state :=
  match edges with
  | [] => ([],s)
  | e :: rest =>
    let s' := pre_client_source_exec e s in
    let '(tr,t) := pre_client_source_walk s' rest in (pre_client_trace e s' ++ tr,t)
  end.

Fixpoint pre_client_target_walk (s : pre_client_state) (edges : list pre_test_edge) :
    list nat * pre_client_state :=
  match edges with
  | [] => ([],s)
  | e :: rest =>
    let primitive := pre_client_target_exec pre_client_plan e s in
    let t := pre_client_finish_exec pre_client_plan e primitive in
    let '(tr,t') := pre_client_target_walk t rest in (pre_client_trace e primitive ++ tr,t')
  end.

Fixpoint pre_client_walk_enabled (advance : pre_test_edge -> pre_client_state -> pre_client_state)
    (s : pre_client_state) (edges : list pre_test_edge) : Prop :=
  match edges with
  | [] => True
  | e :: rest => client_admin s = None /\ In e (Graph.out pre_test_points (client_pc s)) /\
      pre_client_walk_enabled advance (advance e s) rest
  end.

Local Lemma pre_client_source_walk_sound : forall edges s tr t,
  pre_client_walk_enabled pre_client_source_exec s edges ->
  pre_client_source_walk s edges = (tr,t) -> exec pre_client_source s tr t.
Proof.
  intro edges; induction edges as [|e edges IH]; intros s tr t Henabled Hwalk.
  - inversion Hwalk; apply exec_refl.
  - destruct Henabled as [Hadmin [Hout Henabled]]; cbn [pre_client_source_walk] in Hwalk.
    destruct (pre_client_source_walk (pre_client_source_exec e s) edges)
      as [tail_trace final] eqn:Htail; inversion Hwalk; subst tr t.
    eapply exec_step; [apply pre_client_source_edge; eassumption|].
    eapply IH; eassumption.
Qed.

Local Lemma pre_client_target_walk_sound : forall edges s tr t,
  pre_client_walk_enabled (fun e s => pre_client_finish_exec pre_client_plan e
    (pre_client_target_exec pre_client_plan e s)) s edges ->
  pre_client_target_walk s edges = (tr,t) -> exec (pre_client_target pre_client_plan) s tr t.
Proof.
  intro edges; induction edges as [|e edges IH]; intros s tr t Henabled Hwalk.
  - inversion Hwalk; apply exec_refl.
  - destruct Henabled as [Hadmin [Hout Henabled]]; cbn [pre_client_target_walk] in Hwalk.
    destruct (pre_client_target_walk (pre_client_finish_exec pre_client_plan e
      (pre_client_target_exec pre_client_plan e s)) edges) as [tail_trace final] eqn:Htail.
    inversion Hwalk; subst tr t; eapply exec_app.
    + apply (pre_macro_exec pre_client_realizer pre_client_plan e).
      apply pre_client_macro; repeat split; assumption || reflexivity.
    + eapply IH; eassumption.
Qed.

(** Both computed runs emit distinct branch values and choose that value at the actual join. *)
Example pre_client_execution_values : forall right kind,
  let source_run := pre_client_source_walk (pre_client_initial kind) (pre_client_edges right) in
  let target_run := pre_client_target_walk (pre_client_initial kind) (pre_client_edges right) in
  let expected := if right then 9 else 7 in
  fst source_run = [expected] /\ fst target_run = [expected] /\
  client_result (snd source_run) = Some expected /\
  client_result (snd target_run) = Some expected /\
  pre_client_cached (snd target_run) (PreMerged (PreBind PreJoin) PreZ) = Some expected.
Proof.
  intros [] kind; vm_compute; repeat split; reflexivity.
Qed.

(** The executable observations are actual semantic runs, including every administrative finish. *)
Example pre_client_execution_paths : forall right kind,
  let source_run := pre_client_source_walk (pre_client_initial kind) (pre_client_edges right) in
  let target_run := pre_client_target_walk (pre_client_initial kind) (pre_client_edges right) in
  exec pre_client_source (pre_client_initial kind) (fst source_run) (snd source_run) /\
  exec (pre_client_target pre_client_plan) (pre_client_initial kind)
    (fst target_run) (snd target_run).
Proof.
  intros right kind; cbn zeta; split.
  - apply (pre_client_source_walk_sound (pre_client_edges right) (pre_client_initial kind)).
    + destruct right; cbn; repeat split; intuition congruence.
    + destruct (pre_client_source_walk _ _); reflexivity.
  - apply (pre_client_target_walk_sound (pre_client_edges right) (pre_client_initial kind)).
    + destruct right; cbn; repeat split; intuition congruence.
    + destruct (pre_client_target_walk _ _); reflexivity.
Qed.

(** Trap and resource-stop tags survive the actual inserted, selected and deleted operations. *)
Example pre_client_execution_endings : forall right kind,
  ends_as pre_client_source pre_client_endings kind
    (snd (pre_client_source_walk (pre_client_initial kind) (pre_client_edges right))) /\
  ends_as (pre_client_target pre_client_plan) pre_client_endings kind
    (snd (pre_client_target_walk (pre_client_initial kind) (pre_client_edges right))).
Proof.
  intros right kind; destruct kind; try (destruct right; split; repeat split; reflexivity).
  destruct right; split; unfold ends_as, stuck; repeat split;
    try (intros [Hfalse Hrest]; discriminate);
    intros [tr [t Hstep]]; inversion Hstep; cbn in *; intuition discriminate.
Qed.

(** The boundary invariant distinguishes predecessor caches before simultaneous phi selection. *)
Definition pre_client_cache_state (s : pre_client_state) : Prop :=
  match client_pc s with
  | (PreLeft,PreBetween) | (PreLeft,PreAfter) =>
    pre_client_cached s (PreComputed (PreCompute PreLeft) PreX) = Some 7
  | (PreJoin,PreBefore) =>
    (client_incoming s = PreLeftJoin /\
      pre_client_cached s (PreComputed (PreCompute PreLeft) PreX) = Some 7) \/
    (client_incoming s = PreRightJoin /\
      pre_client_cached s (PreInserted (PreCross PreRightJoin) PreY) = Some 9)
  | (PreJoin,PreBody) | (PreJoin,PreBetween) | (PreJoin,PreAfter) =>
    pre_client_cached s (PreMerged (PreBind PreJoin) PreZ) = Some (S (client_z s))
  | _ => True
  end.

Local Lemma pre_client_join_update : forall t,
  pre_client_cached (pre_client_finish_exec pre_client_plan (PreBind PreJoin)
    (pre_client_target_exec pre_client_plan (PreBind PreJoin) t))
    (PreMerged (PreBind PreJoin) PreZ) =
    match client_incoming t with
    | PreLeftJoin => pre_client_cached t (PreComputed (PreCompute PreLeft) PreX)
    | PreRightJoin => pre_client_cached t (PreInserted (PreCross PreRightJoin) PreY)
    | _ => pre_client_cached t (PreMerged (PreBind PreJoin) PreZ)
    end.
Proof.
  intro t; unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
  rewrite pre_client_insert_cache_agrees.
  change (Map.get pre_client_version_encoding (PreMerged (PreBind PreJoin) PreZ)
    (pre_client_phi pre_client_plan (PreCross (client_incoming t)) (PreBind PreJoin)
      (client_cache t)) = match client_incoming t with
    | PreLeftJoin => Map.get pre_client_version_encoding
        (PreComputed (PreCompute PreLeft) PreX) (client_cache t)
    | PreRightJoin => Map.get pre_client_version_encoding
        (PreInserted (PreCross PreRightJoin) PreY) (client_cache t)
    | _ => Map.get pre_client_version_encoding (PreMerged (PreBind PreJoin) PreZ) (client_cache t)
    end).
  rewrite pre_client_phi_get; destruct (client_incoming t); reflexivity.
Qed.

(** Every actual complete client macro preserves the boundary cache invariant. *)
Local Lemma pre_client_cache_state_macro : forall t e l t',
  pre_client_cache_state t -> pre_macro_step pre_client_realizer pre_client_plan e t l t' ->
  pre_client_cache_state t'.
Proof.
  intros t e l t' Hcache Hmacro; pose proof Hmacro as Hmacro_original.
  apply pre_client_macro in Hmacro; destruct Hmacro as [Hadmin [Hout [Htrace ->]]].
  assert (client_pc t = Graph.source pre_test_points e) as Hsource.
  { symmetry; exact (out_source pre_test_points_wf _ e Hout). }
  unfold pre_client_cache_state in Hcache; rewrite Hsource in Hcache.
  destruct e as [b|b|b|be]; try destruct b; try destruct be;
    cbn [pre_client_cache_state pre_client_finish_exec pre_client_target_exec
      pre_client_advance client_pc]; try exact I.
  - change (pre_client_cached (pre_client_finish_exec pre_client_plan (PreBind PreJoin)
      (pre_client_target_exec pre_client_plan (PreBind PreJoin) t))
      (PreMerged (PreBind PreJoin) PreZ) =
        Some (S (match client_incoming t with
        | PreLeftJoin => 6
        | PreRightJoin => 8
        | _ => client_z t
        end))).
    rewrite pre_client_join_update; destruct Hcache as [[Hedge Hvalue]|[Hedge Hvalue]];
      rewrite Hedge; exact Hvalue.
  - unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
    rewrite pre_client_insert_cache_agrees.
    change (Map.get pre_client_version_encoding (PreComputed (PreCompute PreLeft) PreX)
      (Map.set pre_client_version_encoding (PreComputed (PreCompute PreLeft) PreX) 7
        (client_cache t)) = Some 7); apply Map.get_set_same.
  - etransitivity; [exact (pre_client_cache_frame pre_client_plan (PreCompute PreJoin) t l _
      (PreMerged (PreBind PreJoin) PreZ)
      Hmacro_original eq_refl)|exact Hcache].
  - etransitivity; [exact (pre_client_cache_frame pre_client_plan (PreAgain PreLeft) t l _
      (PreComputed (PreCompute PreLeft) PreX)
      Hmacro_original eq_refl)|exact Hcache].
  - etransitivity; [exact (pre_client_cache_frame pre_client_plan (PreAgain PreJoin) t l _
      (PreMerged (PreBind PreJoin) PreZ)
      Hmacro_original eq_refl)|exact Hcache].
  - left; split; [reflexivity|].
    etransitivity; [exact (pre_client_cache_frame pre_client_plan (PreCross PreLeftJoin) t l _
      (PreComputed (PreCompute PreLeft) PreX)
      Hmacro_original eq_refl)|exact Hcache].
  - right; split; [reflexivity|].
    unfold pre_client_cached, pre_client_finish_exec; cbn [client_cache].
    rewrite pre_client_insert_cache_agrees, Map.get_set_same; reflexivity.
Qed.

Local Lemma pre_client_paired_cache_state : forall s0 t0 s t,
  pre_paired_run pre_client_realizer pre_client_plan s0 t0 s t -> pre_client_cache_state t.
Proof.
  intros s0 t0 s t Hpaired; induction Hpaired as [Hsource Htarget Hboundary Hcore|
    s t e l s' t' Hpaired IH Hstep Htaken Hmacro Hcore].
  - destruct Htarget as [kind ->]; exact I.
  - eapply pre_client_cache_state_macro; eassumption.
Qed.

Local Lemma pre_client_cache_from_state : forall s t,
  pre_client_core s t -> pre_client_cache_state t ->
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_client_expression) pre_client_realizer pre_client_plan (client_pc s) s t.
Proof.
  intros s t Hcore Hcache; split; [exact Hcore|].
  pose proof Hcore as [Hs [Ht [Hpoint [Hincoming [Hz Hrest]]]]].
  intros e u version Hsource Hdeleted Hreload.
  change (Graph.source pre_test_points e = client_pc s) in Hsource.
  unfold pre_client_cache_state in Hcache; rewrite <- Hpoint, <- Hsource in Hcache.
  apply pre_client_deleted in Hdeleted; destruct Hdeleted as [[He Hu]|[He Hu]]; subst u.
  - subst e.
    change (Some (PreComputed (PreCompute PreLeft) PreX) = Some version) in Hreload.
    injection Hreload as <-; exact Hcache.
  - destruct He as [He|He]; subst e;
      change (Some (PreMerged (PreBind PreJoin) PreZ) = Some version) in Hreload;
      injection Hreload as <-;
      change (pre_client_cached t (PreMerged (PreBind PreJoin) PreZ) = Some (S (client_z s)));
      rewrite Hz; exact Hcache.
Qed.

(** The executable client cache agrees at every boundary of the very same paired run. *)
Example pre_client_paired_cache : forall s0 t0 s t,
  pre_paired_run pre_client_realizer pre_client_plan s0 t0 s t ->
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_client_expression) pre_client_realizer pre_client_plan (client_pc s) s t.
Proof.
  intros s0 t0 s t Hpaired; apply pre_client_cache_from_state.
  - destruct Hpaired; assumption.
  - eapply pre_client_paired_cache_state; exact Hpaired.
Qed.

(** The complete-path proof applies to the actual executable producer client and all ending tags. *)
Example pre_client_complete_path_behaviour : forall kind,
  same_behaviour pre_client_source pre_client_endings (pre_client_initial kind)
    (pre_client_target pre_client_plan) pre_client_endings (pre_client_initial kind).
Proof.
  intro kind; eapply (pre_cache_paths_behaviour pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    pre_client_expression (pre_expression pre_client_expression)
    (pre_initial_available pre_client_expression) pre_client_realizer pre_client_plan
    pre_client_local_laws (pre_client_initial kind) (pre_client_initial kind)).
  - exact (ssa_pre_deletions_defined pre_test_block_encoding pre_test_block_edge_encoding
      pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
      pre_client_expression pre_client_expression_laws pre_test_blocks_ready pre_test_points_ready).
  - intros s t Hpaired; eapply pre_client_paired_cache; exact Hpaired.
  - exists kind; reflexivity.
  - exists kind; reflexivity.
  - apply pre_client_boundary; split; reflexivity.
  - repeat split; reflexivity.
Qed.

(** The fixed general cache theorem applies to every paired history of the executable client. *)
Example pre_client_generic_cache : forall kind s t,
  pre_paired_run pre_client_realizer pre_client_plan
    (pre_client_initial kind) (pre_client_initial kind) s t ->
  pre_cache_agree pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding
    (pre_expression pre_client_expression) pre_client_realizer pre_client_plan
    (point (pre_source_graph pre_client_realizer) s) s t.
Proof.
  intros kind s t Hpaired.
  exact (ssa_pre_cache_invariant pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    pre_client_expression pre_client_realizer (pre_client_initial kind) (pre_client_initial kind)
    pre_client_expression_laws pre_test_blocks_ready pre_test_points_ready pre_client_exit_covered
    pre_client_phi_source pre_client_local_laws s t Hpaired).
Qed.

(** The exact generic theorem proves the insertion, join and deletion client's behavior. *)
Example pre_client_generic_semantics : forall kind,
  same_behaviour pre_client_source pre_client_endings (pre_client_initial kind)
    (pre_client_target pre_client_plan) pre_client_endings (pre_client_initial kind).
Proof.
  intro kind; apply (ssa_pre_semantics pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    pre_client_expression pre_client_realizer (pre_client_initial kind) (pre_client_initial kind)
    pre_client_expression_laws pre_test_blocks_ready pre_test_points_ready pre_client_exit_covered
    pre_client_phi_source pre_client_local_laws).
  - exists kind; reflexivity.
  - exists kind; reflexivity.
  - apply pre_client_boundary; split; reflexivity.
  - apply pre_client_cache_from_state; [repeat split; reflexivity|exact I].
Qed.
