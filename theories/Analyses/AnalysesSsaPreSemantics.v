(** * Local realization of SSA PRE plans

    A realizer maps target boundaries and administrative points to original graph edges.
    For example, a split incoming edge can finish silently before a parameter selection.
    Builds on: AnalysesSsaPre, ViewsSemantics, ViewsGraph and ViewsSsaPoints. *)

From Stdlib Require Import List PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphIdf GraphLoops.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesAvailable AnalysesSsaPreGraph AnalysesSsaPre.
Import List.ListNotations.

(** Target points project either to a source boundary or to one source edge in progress. *)
Inductive pre_origin (N E : Type) : Type :=
  | PrePoint (n : N)
  | PreOnEdge (e : E) (remaining : nat).
Arguments PrePoint {N E}.
Arguments PreOnEdge {N E}.

(** A client supplies concrete source and target semantics and their cache observations. *)
Record pre_realizer (S O N E NT ET U C : Type) : Type := PreRealizer {
  pre_source : semantics S O;
  pre_source_end : endings S;
  pre_source_graph : graph_view S O N E;
  pre_target : pre_plan E U -> semantics S O;
  pre_target_end : pre_plan E U -> endings S;
  pre_target_graph : pre_plan E U -> graph_view S O NT ET;
  pre_origin_of : pre_plan E U -> NT -> pre_origin N E;
  pre_project_edge : pre_plan E U -> ET -> option E;
  pre_eval : S -> U -> option C;
  pre_cached : S -> pre_version E U -> option C;
  pre_core_agree : S -> S -> Prop;
  pre_measure : pre_plan E U -> S -> nat
}.
Arguments PreRealizer {S O N E NT ET U C}.
Arguments pre_source {S O N E NT ET U C}.
Arguments pre_source_end {S O N E NT ET U C}.
Arguments pre_source_graph {S O N E NT ET U C}.
Arguments pre_target {S O N E NT ET U C}.
Arguments pre_target_end {S O N E NT ET U C}.
Arguments pre_target_graph {S O N E NT ET U C}.
Arguments pre_origin_of {S O N E NT ET U C}.
Arguments pre_project_edge {S O N E NT ET U C}.
Arguments pre_eval {S O N E NT ET U C}.
Arguments pre_cached {S O N E NT ET U C}.
Arguments pre_core_agree {S O N E NT ET U C}.
Arguments pre_measure {S O N E NT ET U C}.

(** Cache agreement requires the selected version of every outgoing reload to hold its value. *)
Definition pre_cache_agree {S O N E NT ET U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (v : pre_expression_view S O N E U C)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) (n : N) (s t : S) : Prop :=
  pre_core_agree r s t /\
  forall e u version, Graph.source (cfg (gkview (pre_genkill v))) e = n ->
    pre_deleted EE EU p e u = true -> Map.get EE e (pre_reload_versions p) = Some version ->
    pre_cached r t version = pre_eval r s u.

(** A target boundary projects to exactly the given source point. *)
Definition pre_boundary {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (n : N) (t : S) : Prop :=
  pre_origin_of r p (point (pre_target_graph r p) t) = PrePoint n.

(** Source endings must occur at points classified as exits by the expression view. *)
Definition pre_exit_covered {S O B BE N E NT ET V K U C}
    (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C) : Prop :=
  forall s k, reachable_state (pre_source r) s ->
    ends_as (pre_source r) (pre_source_end r) k s ->
    pre_exit_point a (point (pre_source_graph r) s) = true.

(** The source parameter step performs the actual incoming edge's simultaneous substitution. *)
Definition pre_phi_source_laws {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) : Prop :=
  forall be e s0 l0 s1 l1 s2,
    reachable_state (pre_source r) s0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some e ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 e ->
    step (pre_source r) s1 l1 s2 ->
    taken (pre_source_graph r) s1 l1 s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    forall x, val (pre_ssa_view a) s2 x = pre_phi_env EV a be (val (pre_ssa_view a) s0) x.

(** An administrative state is projected onto the edge currently being realized. *)
Definition pre_admin {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t : S) : Prop :=
  exists k, pre_origin_of r p (point (pre_target_graph r p) t) = PreOnEdge e k.

(** A finish contains only silent administrative steps before its first edge-target boundary. *)
Inductive pre_finish {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) : S -> S -> Prop :=
  | pre_finish_boundary : forall t,
      pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t -> pre_finish r p e t t
  | pre_finish_admin : forall t t1 t2 te, pre_admin r p e t ->
      step (pre_target r p) t [] t1 -> taken (pre_target_graph r p) t [] t1 te ->
      pre_project_edge r p te = None -> pre_finish r p e t1 t2 -> pre_finish r p e t t2.

(** Every administrative finish reaches the boundary of the same original edge. *)
Lemma pre_finish_endpoint {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t t' : S) :
  pre_finish r p e t t' ->
  pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t'.
Proof.
  intro Hfinish; induction Hfinish as [t Hboundary|t t1 t2 te Hadmin Hstep Htaken
    Hproject Hfinish IH].
  - exact Hboundary.
  - exact IH.
Qed.

(** A finish is an actual silent target run with its original endpoint. *)
Lemma pre_finish_exec {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t t' : S) :
  pre_finish r p e t t' -> exec (pre_target r p) t [] t'.
Proof.
  intro Hfinish; induction Hfinish as [t Hboundary|t t1 t2 te Hadmin Hstep Htaken
    Hproject Hfinish IH].
  - apply exec_refl.
  - exact (exec_step t [] t1 [] t2 Hstep IH).
Qed.

(** A macro executes one projected original edge followed by its administrative finish. *)
Definition pre_macro_step {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t : S) (l : list O) (t' : S) : Prop :=
  pre_boundary r p (Graph.source (cfg (pre_source_graph r)) e) t /\
  exists t1 te, step (pre_target r p) t l t1 /\
    taken (pre_target_graph r p) t l t1 te /\ pre_project_edge r p te = Some e /\
    pre_finish r p e t1 t'.

(** Paired runs couple source edges with target macros and successor core agreement. *)
Inductive pre_paired_run {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (s0 t0 : S) : S -> S -> Prop :=
  | pre_paired_initial : initial (pre_source r) s0 -> initial (pre_target r p) t0 ->
      pre_boundary r p (point (pre_source_graph r) s0) t0 -> pre_core_agree r s0 t0 ->
      pre_paired_run r p s0 t0 s0 t0
  | pre_paired_step : forall s t e l s' t', pre_paired_run r p s0 t0 s t ->
      step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      pre_macro_step r p e t l t' -> pre_core_agree r s' t' ->
      pre_paired_run r p s0 t0 s' t'.

(** Local laws constrain graph steps, cache writes, parameter selection, progress and endings. *)
Record pre_local_laws {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (v : pre_expression_view S O N E U C) (initial_available : U -> bool)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) : Prop := {
  pre_local_graph :
    v = pre_expression a /\ pre_source_graph r = gkview (pre_genkill v) /\
    graph_view_laws (pre_source r) (pre_source_graph r) /\
    graph_view_laws (pre_target r p) (pre_target_graph r p) /\
    (forall s l s', ~ stays (pre_source_graph r) s l s') /\
    (forall t l t', ~ stays (pre_target_graph r p) t l t') /\
    (forall t l t', reachable_state (pre_target r p) t -> step (pre_target r p) t l t' ->
      exists te, taken (pre_target_graph r p) t l t' te /\
      match pre_origin_of r p (point (pre_target_graph r p) t) with
      | PrePoint n => exists e, pre_project_edge r p te = Some e /\
          In e (Graph.out (cfg (pre_source_graph r)) n) /\
          (pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t' \/
           pre_admin r p e t')
      | PreOnEdge e _ => pre_project_edge r p te = None /\
          (pre_admin r p e t' \/
           pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t')
      end);
  pre_local_operands :
    (forall s u, pre_eval r s u = uval (pre_genkill v) s u) /\
    (forall s t u, pre_core_agree r s t -> pre_eval r s u = pre_eval r t u) /\
    (forall s u, reachable_state (pre_source r) s -> pre_total_pure v u = true ->
      exists c, pre_eval r s u = Some c) /\
    (forall e u, pre_recomputed v e = Some u -> In u (gen (pre_genkill v) e));
  pre_local_gen_value : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e -> In u (gen (pre_genkill v) e) ->
    uval (pre_genkill v) s' u = uval (pre_genkill v) s u;
  pre_local_kill_frame : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e -> kill (pre_genkill v) e u = false ->
    uval (pre_genkill v) s' u = uval (pre_genkill v) s u;
  pre_local_kept : forall s t e,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t -> pre_core_agree r s t ->
    (forall u, pre_deleted EE EU p e u = false) ->
    (forall l s', step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      exists t', pre_macro_step r p e t l t' /\ pre_core_agree r s' t') /\
    (forall l t', pre_macro_step r p e t l t' ->
      exists s', step (pre_source r) s l s' /\ taken (pre_source_graph r) s l s' e /\
        pre_core_agree r s' t');
  pre_local_insert : forall s t e u l s' t',
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    pre_core_agree r s t -> pre_inserted EE EU p e u = true ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_cached r t' (PreInserted e u) = pre_eval r s' u;
  pre_local_replace : forall s t e u version,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t -> pre_core_agree r s t ->
    pre_deleted EE EU p e u = true -> Map.get EE e (pre_reload_versions p) = Some version ->
    pre_cached r t version = pre_eval r s u ->
    (forall l s', step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      exists t', pre_macro_step r p e t l t' /\ pre_core_agree r s' t') /\
    (forall l t', pre_macro_step r p e t l t' ->
      exists s', step (pre_source r) s l s' /\ taken (pre_source_graph r) s l s' e /\
        pre_core_agree r s' t');
  pre_local_cache_frame : forall s t e l s' t' version,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_version_written EE e version = false ->
    pre_cached r t' version = pre_cached r t version;
  pre_local_compute : forall s t e u l s' t',
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    pre_recomputed v e = Some u -> pre_deleted EE EU p e u = false ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_cached r t' (PreComputed e u) = pre_eval r s u;
  pre_local_initial : forall s t u,
    initial (pre_source r) s -> initial (pre_target r p) t -> pre_core_agree r s t ->
    initial_available u = true -> pre_cached r t (PreInitial u) = pre_eval r s u;
  pre_local_phi_select : forall s0 t0 s1 t1 s2 t2 be incoming l0 l version,
    reachable_state (pre_source r) s0 -> reachable_state (pre_target r p) t0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 incoming ->
    pre_macro_step r p incoming t0 l0 t1 ->
    step (pre_source r) s1 l s2 ->
    taken (pre_source_graph r) s1 l s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_macro_step r p
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be))
      t1 l t2 ->
    pre_cached r t2 version =
      pre_phi_update EE EU p incoming
        (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be))
        (pre_cached r t1) version;
  pre_local_progress : forall t e, reachable_state (pre_target r p) t -> pre_admin r p e t ->
    ~ final (pre_target_end r p) t /\ ~ trapped (pre_target_end r p) t /\
    ~ stopped (pre_target_end r p) t /\ ~ stuck (pre_target r p) (pre_target_end r p) t /\
    running (pre_target r p) t /\
    forall l t', step (pre_target r p) t l t' -> l = [] /\
      (pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t' \/
       (pre_admin r p e t' /\ pre_measure r p t' < pre_measure r p t));
  pre_local_endings : forall s t n k,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = n -> pre_boundary r p n t -> pre_core_agree r s t ->
    (ends_as (pre_source r) (pre_source_end r) k s <->
      ends_as (pre_target r p) (pre_target_end r p) k t)
}.

(** * Complete paths and administrative prefixes *)

(** Macro semantics retains each complete target path and its particular endpoint. *)
Definition pre_macro_semantics {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) : semantics S O :=
  Semantics (initial (pre_target r p))
    (fun t l t' => exists e, pre_macro_step r p e t l t').

(** A partial finish records only actual administrative choices, before the next boundary. *)
Inductive pre_finish_prefix {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) (e : E) : S -> S -> Prop :=
  | pre_prefix_refl : forall t, pre_admin r p e t -> pre_finish_prefix r p e t t
  | pre_prefix_step : forall t t1 t2 te, pre_admin r p e t ->
      step (pre_target r p) t [] t1 -> taken (pre_target_graph r p) t [] t1 te ->
      pre_project_edge r p te = None -> pre_finish_prefix r p e t1 t2 ->
      pre_finish_prefix r p e t t2.

(** A partial finish can be completed without changing any earlier administrative choice. *)
Lemma pre_finish_prefix_complete {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t q u :
  pre_finish_prefix r p e t q -> pre_finish r p e q u -> pre_finish r p e t u.
Proof.
  intros Hprefix; induction Hprefix as [t Hadmin|t t1 t2 te Hadmin Hstep Htaken Hproject
    Hprefix IH]; intro Hfinish.
  - exact Hfinish.
  - eapply pre_finish_admin; eauto.
Qed.

(** Every incomplete finish still ends inside the same projected edge. *)
Lemma pre_finish_prefix_endpoint {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t q :
  pre_finish_prefix r p e t q -> pre_admin r p e q.
Proof.
  intro Hprefix; induction Hprefix as [t Hadmin|t t1 t2 te Hadmin Hstep Htaken Hproject
    Hprefix IH]; assumption.
Qed.

(** Partial finishes are actual silent paths with their exact endpoint. *)
Lemma pre_finish_prefix_exec {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t q :
  pre_finish_prefix r p e t q -> exec (pre_target r p) t [] q.
Proof.
  intro Hprefix; induction Hprefix as [t Hadmin|t t1 t2 te Hadmin Hstep Htaken Hproject
    Hprefix IH].
  - apply exec_refl.
  - exact (exec_step t [] t1 [] t2 Hstep IH).
Qed.

(** Appending a silent administrative prefix retains all choices of both prefixes. *)
Lemma pre_finish_prefix_app {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t q u :
  pre_finish_prefix r p e t q -> pre_finish_prefix r p e q u ->
  pre_finish_prefix r p e t u.
Proof.
  intro Hprefix; induction Hprefix as [t Hadmin|t t1 t2 te Hadmin Hstep Htaken Hproject
    Hprefix IH]; intro Htail.
  - exact Htail.
  - eapply pre_prefix_step; eauto.
Qed.

(** Every complete macro is a nonempty actual path with precisely the macro trace. *)
Lemma pre_macro_exec {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t l t' :
  pre_macro_step r p e t l t' -> exec (pre_target r p) t l t'.
Proof.
  intros [Hboundary [q [te [Hstep [Htaken [Hproject Hfinish]]]]]].
  rewrite <- (app_nil_r l); eapply exec_step; [exact Hstep|].
  eapply pre_finish_exec; exact Hfinish.
Qed.

(** Macro paths expand to actual paths without changing their trace or endpoint. *)
Lemma pre_macros_exec {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) t tr t' :
  exec (pre_macro_semantics r p) t tr t' -> exec (pre_target r p) t tr t'.
Proof.
  intro Hrun; induction Hrun as [t|t l q tr u [e Hmacro] Hrun IH].
  - apply exec_refl.
  - eapply exec_app; [eapply pre_macro_exec; exact Hmacro|exact IH].
Qed.

(** A complete macro ends at a boundary on precisely its own original edge. *)
Lemma pre_macro_endpoint {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) e t l t' :
  pre_macro_step r p e t l t' ->
  pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t'.
Proof.
  intros [Hboundary [q [te [Hstep [Htaken [Hproject Hfinish]]]]]].
  eapply pre_finish_endpoint; exact Hfinish.
Qed.

(** A macro path that starts at a boundary ends at a boundary, including the empty path. *)
Lemma pre_macros_boundary {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) t tr t' :
  exec (pre_macro_semantics r p) t tr t' ->
  (exists n, pre_boundary r p n t) -> exists n, pre_boundary r p n t'.
Proof.
  intro Hrun; induction Hrun as [t|t l q tr u [e Hmacro] Hrun IH]; intro Hboundary.
  - exact Hboundary.
  - apply IH; exists (Graph.target (cfg (pre_source_graph r)) e).
    eapply pre_macro_endpoint; exact Hmacro.
Qed.

(** Infinite macro paths expand constructively because each macro contains an actual first step. *)
Lemma pre_macros_diverges {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) t :
  diverges (pre_macro_semantics r p) t -> diverges (pre_target r p) t.
Proof.
  intro Hdiverge.
  apply (diverges_from_progress (pre_target r p)
    (fun q => exists tr u, exec (pre_target r p) q tr u /\
      diverges (pre_macro_semantics r p) u)).
  - intros q [tr [u [Hrun Hdiv]]]; destruct Hrun as [q|q l q' tr u Hstep Htail].
    + destruct Hdiv as [q l u [e [Hboundary [q' [te [Hstep [Htaken [Hproject Hfinish]]]]]]]
        Hdiv].
      exists l, q'; split; [exact Hstep|]; exists [], u; split.
      * eapply pre_finish_exec; exact Hfinish.
      * exact Hdiv.
    + exists l, q'; split; [exact Hstep|]; exists tr, u; split; assumption.
  - exists [], t; split; [apply exec_refl|exact Hdiverge].
Qed.

(** A grouped target path ends at a complete boundary or retains its actual unfinished macro. *)
Inductive pre_grouped_path {S O N E NT ET U C}
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) (t0 : S) : list O -> S -> Prop :=
  | pre_grouped_boundary : forall tr t n,
      exec (pre_macro_semantics r p) t0 tr t -> pre_boundary r p n t ->
      pre_grouped_path r p t0 tr t
  | pre_grouped_pending : forall tr l t q u e te,
      exec (pre_macro_semantics r p) t0 tr t ->
      pre_boundary r p (Graph.source (cfg (pre_source_graph r)) e) t ->
      step (pre_target r p) t l q -> taken (pre_target_graph r p) t l q te ->
      pre_project_edge r p te = Some e -> pre_finish_prefix r p e q u ->
      pre_grouped_path r p t0 (tr ++ l) u.

Section TargetPaths.
  Context {S O B BE N E NT ET V K U C : Type}.
  Variables (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U).
  Variables (a : pre_expr_ssa S O B BE N E V K C U)
    (v : pre_expression_view S O N E U C) (ia : U -> bool)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U).
  Hypothesis Hlaws : pre_local_laws EBE EN EE EV EU a v ia r p.

  Local Lemma pre_target_projection : forall t l t',
    reachable_state (pre_target r p) t -> step (pre_target r p) t l t' ->
    exists te, taken (pre_target_graph r p) t l t' te /\
      match pre_origin_of r p (point (pre_target_graph r p) t) with
      | PrePoint n => exists e, pre_project_edge r p te = Some e /\
          In e (Graph.out (cfg (pre_source_graph r)) n) /\
          (pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t' \/
           pre_admin r p e t')
      | PreOnEdge e _ => pre_project_edge r p te = None /\
          (pre_admin r p e t' \/
           pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t')
      end.
  Proof.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws))))))).
  Qed.

  (** Each reachable administrative state has a finite completion on its own projected edge. *)
  Lemma pre_admin_completes : forall t e,
    reachable_state (pre_target r p) t -> pre_admin r p e t ->
    exists t', pre_finish r p e t t'.
  Proof.
    intro t; remember (pre_measure r p t) as bound eqn:Hmeasure.
    revert t Hmeasure; induction bound as [bound IH] using lt_wf_ind.
    intros q Hmeasure e Hreachable Hadmin.
    destruct (pre_local_progress _ _ _ _ _ _ _ _ _ _ Hlaws q e Hreachable Hadmin)
      as [Hfinal [Htrap [Hstop [Hstuck [[l [q' Hstep]] Hprogress]]]]].
    destruct (Hprogress l q' Hstep) as [-> Hnext].
    destruct (pre_target_projection q [] q' Hreachable Hstep) as [te [Htaken Hproject]].
    destruct Hadmin as [k Horigin]; rewrite Horigin in Hproject.
    destruct Hproject as [Hproject Hshape].
    destruct Hnext as [Hboundary|[Hadmin Hdecrease]].
    - exists q'; eapply pre_finish_admin with (te := te) (t1 := q').
      + exists k; exact Horigin.
      + exact Hstep.
      + exact Htaken.
      + exact Hproject.
      + apply pre_finish_boundary; exact Hboundary.
    - destruct (IH (pre_measure r p q') ltac:(lia) q' eq_refl e
        (reachable_state_step (pre_target r p) q [] q' Hreachable Hstep) Hadmin)
        as [u Hfinish].
      exists u; eapply pre_finish_admin; eauto; exists k; exact Horigin.
  Qed.

  (** Every reachable administrative ending is excluded for each of the four ending tags. *)
  Lemma pre_admin_no_ending : forall t e k,
    reachable_state (pre_target r p) t -> pre_admin r p e t ->
    ~ ends_as (pre_target r p) (pre_target_end r p) k t.
  Proof.
    intros t e k Hreachable Hadmin.
    destruct (pre_local_progress _ _ _ _ _ _ _ _ _ _ Hlaws t e Hreachable Hadmin)
      as [Hfinal [Htrap [Hstop [Hstuck Hrest]]]].
    destruct k; assumption.
  Qed.

  Local Lemma pre_source_graph_wf : graph_wf (cfg (pre_source_graph r)).
  Proof.
    exact (cfg_wf (proj1 (proj2 (proj2
      (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws))))).
  Qed.

  (** Every actual boundary step completes a macro retaining that particular first transition. *)
  Lemma pre_boundary_step_macro : forall t n l q,
    reachable_state (pre_target r p) t -> pre_boundary r p n t ->
    step (pre_target r p) t l q -> exists e u,
      pre_macro_step r p e t l u /\ pre_finish r p e q u.
  Proof.
    intros t n l q Hreachable Hboundary Hstep.
    destruct (pre_target_projection t l q Hreachable Hstep) as [te [Htaken Hproject]].
    unfold pre_boundary in Hboundary; rewrite Hboundary in Hproject.
    destruct Hproject as [e [Hproject [Hout Hnext]]].
    assert (exists u, pre_finish r p e q u) as [u Hfinish].
    { destruct Hnext as [Hboundary'|Hadmin].
      - exists q; apply pre_finish_boundary; exact Hboundary'.
      - eapply pre_admin_completes; [eapply reachable_state_step; eassumption|exact Hadmin]. }
    exists e, u; split; [|exact Hfinish]; split.
    - unfold pre_boundary; rewrite Hboundary, (out_source pre_source_graph_wf n e Hout).
      reflexivity.
    - exists q, te; repeat split; assumption.
  Qed.

  (** Boundary running is unchanged by replacing complete target paths with macro steps. *)
  Lemma pre_boundary_running : forall t n,
    reachable_state (pre_target r p) t -> pre_boundary r p n t ->
    (running (pre_macro_semantics r p) t <-> running (pre_target r p) t).
  Proof.
    intros t n Hreachable Hboundary; split.
    - intros [l [u [e [Hsource [q [te [Hstep Hrest]]]]]]]; exists l, q; exact Hstep.
    - intros [l [q Hstep]].
      destruct (pre_boundary_step_macro t n l q Hreachable Hboundary Hstep)
        as [e [u [Hmacro Hfinish]]].
      exists l, u, e; exact Hmacro.
  Qed.

  (** Macro and actual semantics have identical ending tags at reachable boundaries. *)
  Lemma pre_boundary_endings : forall t n k,
    reachable_state (pre_target r p) t -> pre_boundary r p n t ->
    (ends_as (pre_macro_semantics r p) (pre_target_end r p) k t <->
      ends_as (pre_target r p) (pre_target_end r p) k t).
  Proof.
    intros t n k Hreachable Hboundary; destruct k; try reflexivity.
    unfold ends_as, stuck; rewrite (pre_boundary_running t n Hreachable Hboundary).
    reflexivity.
  Qed.

  (** A diverging actual administrative path reaches a boundary along that same infinite path. *)
  Lemma pre_admin_diverges_completes : forall t e,
    reachable_state (pre_target r p) t -> pre_admin r p e t ->
    diverges (pre_target r p) t -> exists t',
      pre_finish r p e t t' /\ reachable_state (pre_target r p) t' /\
      diverges (pre_target r p) t'.
  Proof.
    intro t; remember (pre_measure r p t) as bound eqn:Hmeasure.
    revert t Hmeasure; induction bound as [bound IH] using lt_wf_ind.
    intros q Hmeasure e Hreachable Hadmin Hdiverge.
    destruct Hdiverge as [q l q' Hstep Hdiv].
    destruct (pre_local_progress _ _ _ _ _ _ _ _ _ _ Hlaws q e Hreachable Hadmin)
      as [_ [_ [_ [_ [_ Hprogress]]]]].
    destruct (Hprogress l q' Hstep) as [-> Hnext].
    destruct (pre_target_projection q [] q' Hreachable Hstep) as [te [Htaken Hproject]].
    destruct Hadmin as [k Horigin]; rewrite Horigin in Hproject.
    destruct Hproject as [Hproject Hshape].
    assert (reachable_state (pre_target r p) q') as Hreachable'.
    { eapply reachable_state_step; eassumption. }
    destruct Hnext as [Hboundary|[Hadmin Hdecrease]].
    - exists q'; split; [|split; assumption].
      eapply pre_finish_admin with (te := te) (t1 := q').
      + exists k; exact Horigin.
      + exact Hstep.
      + exact Htaken.
      + exact Hproject.
      + apply pre_finish_boundary; exact Hboundary.
    - destruct (IH (pre_measure r p q') ltac:(lia) q' eq_refl e Hreachable' Hadmin Hdiv)
        as [u [Hfinish [Hreachable_u Hdiv_u]]].
      exists u; split; [|split; assumption].
      eapply pre_finish_admin; eauto; exists k; exact Horigin.
  Qed.

  Local Lemma pre_boundary_diverges_step : forall t n,
    reachable_state (pre_target r p) t -> pre_boundary r p n t ->
    diverges (pre_target r p) t -> exists l u,
      step (pre_macro_semantics r p) t l u /\ reachable_state (pre_target r p) u /\
      diverges (pre_target r p) u /\ exists n', pre_boundary r p n' u.
  Proof.
    intros t n Hreachable Hboundary Hdiverge.
    destruct Hdiverge as [t l q Hstep Hdiv].
    destruct (pre_target_projection t l q Hreachable Hstep) as [te [Htaken Hproject]].
    unfold pre_boundary in Hboundary; rewrite Hboundary in Hproject.
    destruct Hproject as [e [Hproject [Hout Hnext]]].
    assert (reachable_state (pre_target r p) q) as Hreachable_q.
    { eapply reachable_state_step; eassumption. }
    assert (exists u, pre_finish r p e q u /\ reachable_state (pre_target r p) u /\
      diverges (pre_target r p) u) as [u [Hfinish [Hreachable_u Hdiv_u]]].
    { destruct Hnext as [Hboundary_q|Hadmin].
      - exists q; split; [apply pre_finish_boundary; exact Hboundary_q|split; assumption].
      - eapply pre_admin_diverges_completes; eassumption. }
    exists l, u; split.
    - exists e; split.
      + unfold pre_boundary; rewrite Hboundary, (out_source pre_source_graph_wf n e Hout).
        reflexivity.
      + exists q, te; repeat split; assumption.
    - split; [exact Hreachable_u|]; split; [exact Hdiv_u|].
      exists (Graph.target (cfg (pre_source_graph r)) e).
      eapply pre_finish_endpoint; exact Hfinish.
  Qed.

  (** Decreasing administration turns every actual infinite path into complete macro steps. *)
  Lemma pre_target_diverges_macros : forall t n,
    reachable_state (pre_target r p) t -> pre_boundary r p n t ->
    diverges (pre_target r p) t -> diverges (pre_macro_semantics r p) t.
  Proof.
    intros t n Hreachable Hboundary Hdiv.
    apply (diverges_from_progress (pre_macro_semantics r p)
      (fun q => reachable_state (pre_target r p) q /\ diverges (pre_target r p) q /\
        exists n', pre_boundary r p n' q)).
    - intros q [Hreachable_q [Hdiv_q [n' Hboundary_q]]].
      destruct (pre_boundary_diverges_step q n' Hreachable_q Hboundary_q Hdiv_q)
        as [l [u [Hstep [Hreachable_u [Hdiv_u Hboundary_u]]]]].
      exists l, u; split; [exact Hstep|]; split; [exact Hreachable_u|].
      split; assumption.
    - split; [exact Hreachable|]; split; [exact Hdiv|eauto].
  Qed.

  Local Lemma pre_boundary_step_grouped : forall t0 tr t n l q,
    exec (pre_macro_semantics r p) t0 tr t -> pre_boundary r p n t ->
    reachable_state (pre_target r p) t -> step (pre_target r p) t l q ->
    pre_grouped_path r p t0 (tr ++ l) q.
  Proof.
    intros t0 tr t n l q Hrun Hboundary Hreachable Hstep.
    destruct (pre_target_projection t l q Hreachable Hstep) as [te [Htaken Hproject]].
    unfold pre_boundary in Hboundary; rewrite Hboundary in Hproject.
    destruct Hproject as [e [Hproject [Hout Hnext]]].
    assert (pre_boundary r p (Graph.source (cfg (pre_source_graph r)) e) t) as Hsource.
    { unfold pre_boundary; rewrite Hboundary, (out_source pre_source_graph_wf n e Hout).
      reflexivity. }
    destruct Hnext as [Hboundary'|Hadmin].
    - eapply pre_grouped_boundary; [|exact Hboundary'].
      eapply exec_app; [exact Hrun|]; apply exec_one; exists e.
      split; [exact Hsource|]; exists q, te; repeat split; try assumption.
      apply pre_finish_boundary; exact Hboundary'.
    - eapply pre_grouped_pending; try eassumption.
      apply pre_prefix_refl; exact Hadmin.
  Qed.

  Local Lemma pre_pending_step_grouped : forall t0 tr l t q u e te next_l u',
    exec (pre_macro_semantics r p) t0 tr t ->
    pre_boundary r p (Graph.source (cfg (pre_source_graph r)) e) t ->
    step (pre_target r p) t l q -> taken (pre_target_graph r p) t l q te ->
    pre_project_edge r p te = Some e -> pre_finish_prefix r p e q u ->
    reachable_state (pre_target r p) u -> step (pre_target r p) u next_l u' ->
    pre_grouped_path r p t0 ((tr ++ l) ++ next_l) u'.
  Proof.
    intros t0 tr l t q u e te next_l u' Hrun Hboundary Hstart Htaken Hproject
      Hprefix Hreachable Hstep.
    pose proof (pre_finish_prefix_endpoint r p e q u Hprefix) as Hadmin.
    destruct (pre_local_progress _ _ _ _ _ _ _ _ _ _ Hlaws u e Hreachable Hadmin)
      as [_ [_ [_ [_ [_ Hprogress]]]]].
    destruct (Hprogress next_l u' Hstep) as [-> Hnext]; rewrite app_nil_r.
    destruct (pre_target_projection u [] u' Hreachable Hstep) as [te' [Htaken' Hproject']].
    destruct Hadmin as [k Horigin]; rewrite Horigin in Hproject'.
    destruct Hproject' as [Hproject' Hshape].
    destruct Hnext as [Hboundary'|[Hadmin' Hdecrease]].
    - eapply pre_grouped_boundary; [|exact Hboundary'].
      eapply exec_app; [exact Hrun|]; apply exec_one; exists e; split; [exact Hboundary|].
      exists q, te; split; [exact Hstart|]; split; [exact Htaken|].
      split; [exact Hproject|]; eapply pre_finish_prefix_complete; [exact Hprefix|].
      eapply pre_finish_admin with (te := te') (t1 := u').
      + exists k; exact Horigin.
      + exact Hstep.
      + exact Htaken'.
      + exact Hproject'.
      + apply pre_finish_boundary; exact Hboundary'.
    - eapply pre_grouped_pending; try eassumption.
      eapply pre_finish_prefix_app; [exact Hprefix|].
      eapply pre_prefix_step with (te := te') (t1 := u').
      + exists k; exact Horigin.
      + exact Hstep.
      + exact Htaken'.
      + exact Hproject'.
      + apply pre_prefix_refl; exact Hadmin'.
  Qed.

  (** Extending a grouped prefix follows this actual successor, including delayed choices. *)
  Lemma pre_grouped_step : forall t0 tr t l t',
    pre_grouped_path r p t0 tr t -> reachable_state (pre_target r p) t ->
    step (pre_target r p) t l t' -> pre_grouped_path r p t0 (tr ++ l) t'.
  Proof.
    intros t0 tr t l t' Hgroup Hreachable Hstep.
    destruct Hgroup as [tr t n Hrun Hboundary|
      tr first t q u e te Hrun Hboundary Hstart Htaken Hproject Hprefix].
    - eapply pre_boundary_step_grouped; eassumption.
    - eapply pre_pending_step_grouped; eassumption.
  Qed.

  Local Lemma pre_grouped_exec : forall t tr t',
    exec (pre_target r p) t tr t' -> reachable_state (pre_target r p) t ->
    forall t0 prefix, pre_grouped_path r p t0 prefix t ->
      pre_grouped_path r p t0 (prefix ++ tr) t'.
  Proof.
    intros t tr t' Hrun; induction Hrun as [t|t l q tr u Hstep Hrun IH];
      intros Hreachable t0 prefix Hgroup.
    - rewrite app_nil_r; exact Hgroup.
    - rewrite app_assoc; apply IH.
      + eapply reachable_state_step; eassumption.
      + eapply pre_grouped_step; eassumption.
  Qed.

  (** Every actual finite target path has a grouping that preserves all completed endpoints. *)
  Lemma pre_target_path_grouped : forall t0 tr t n,
    reachable_state (pre_target r p) t0 -> pre_boundary r p n t0 ->
    exec (pre_target r p) t0 tr t -> pre_grouped_path r p t0 tr t.
  Proof.
    intros t0 tr t n Hreachable Hboundary Hrun.
    change (pre_grouped_path r p t0 ([] ++ tr) t).
    eapply pre_grouped_exec; try eassumption.
    eapply pre_grouped_boundary; [apply exec_refl|exact Hboundary].
  Qed.

  (** An unfinished finite prefix extends silently to a complete macro on its actual history. *)
  Lemma pre_grouped_completes : forall t0 tr t,
    pre_grouped_path r p t0 tr t -> reachable_state (pre_target r p) t ->
    exists t', exec (pre_target r p) t [] t' /\
      exec (pre_macro_semantics r p) t0 tr t' /\ exists n, pre_boundary r p n t'.
  Proof.
    intros t0 tr t Hgroup Hreachable.
    destruct Hgroup as [tr t n Hrun Hboundary|
      tr first t q u e te Hrun Hboundary Hstart Htaken Hproject Hprefix].
    - exists t; split; [apply exec_refl|]; split; [exact Hrun|eauto].
    - destruct (pre_admin_completes u e Hreachable
        (pre_finish_prefix_endpoint r p e q u Hprefix)) as [u' Hfinish].
      exists u'; split; [eapply pre_finish_exec; exact Hfinish|]; split.
      + eapply exec_app; [exact Hrun|]; apply exec_one; exists e; split; [exact Hboundary|].
        exists q, te; split; [exact Hstart|]; split; [exact Htaken|].
        split; [exact Hproject|]; eapply pre_finish_prefix_complete; eassumption.
      + exists (Graph.target (cfg (pre_source_graph r)) e).
        eapply pre_finish_endpoint; exact Hfinish.
  Qed.

  Local Lemma pre_grouped_finish : forall t0 tr t k,
    pre_grouped_path r p t0 tr t -> reachable_state (pre_target r p) t ->
    ends_as (pre_target r p) (pre_target_end r p) k t ->
    exec (pre_macro_semantics r p) t0 tr t /\
      ends_as (pre_macro_semantics r p) (pre_target_end r p) k t.
  Proof.
    intros t0 tr t k Hgroup Hreachable Hending.
    destruct Hgroup as [tr t n Hrun Hboundary|
      tr first t q u e te Hrun Hboundary Hstart Htaken Hproject Hprefix].
    - split; [exact Hrun|].
      apply (proj2 (pre_boundary_endings t n k Hreachable Hboundary)); exact Hending.
    - exfalso; eapply pre_admin_no_ending; [exact Hreachable| |exact Hending].
      eapply pre_finish_prefix_endpoint; exact Hprefix.
  Qed.

  Local Lemma pre_grouped_diverges : forall t0 tr t,
    pre_grouped_path r p t0 tr t -> reachable_state (pre_target r p) t ->
    diverges (pre_target r p) t -> diverges_after (pre_macro_semantics r p) t0 tr.
  Proof.
    intros t0 tr t Hgroup Hreachable Hdiv.
    destruct Hgroup as [tr t n Hrun Hboundary|
      tr first t q u e te Hrun Hboundary Hstart Htaken Hproject Hprefix].
    - exists t; split; [exact Hrun|]; eapply pre_target_diverges_macros; eassumption.
    - destruct (pre_admin_diverges_completes u e Hreachable
        (pre_finish_prefix_endpoint r p e q u Hprefix) Hdiv)
        as [u' [Hfinish [Hreachable_u Hdiv_u]]].
      exists u'; split.
      + eapply exec_app; [exact Hrun|]; apply exec_one; exists e; split; [exact Hboundary|].
        exists q, te; split; [exact Hstart|]; split; [exact Htaken|].
        split; [exact Hproject|]; eapply pre_finish_prefix_complete; eassumption.
      + eapply pre_target_diverges_macros; [exact Hreachable_u| |exact Hdiv_u].
        eapply pre_finish_endpoint; exact Hfinish.
  Qed.

  (** Complete-path grouping preserves all four endings, exact prefixes and both divergences. *)
  Lemma pre_target_macro_behaviour : forall t0 n,
    reachable_state (pre_target r p) t0 -> pre_boundary r p n t0 ->
    same_behaviour (pre_macro_semantics r p) (pre_target_end r p) t0
      (pre_target r p) (pre_target_end r p) t0.
  Proof.
    intros t0 n Hreachable Hboundary; constructor.
    - intros k tr; split; intros [t [Hrun Hending]].
      + exists t; split; [eapply pre_macros_exec; exact Hrun|].
        destruct (pre_macros_boundary r p t0 tr t Hrun (ex_intro _ n Hboundary))
          as [n' Hboundary_t].
        apply (proj1 (pre_boundary_endings t n' k
          (reachable_state_exec (pre_target r p) t0 tr t Hreachable
            (pre_macros_exec r p t0 tr t Hrun)) Hboundary_t)); exact Hending.
      + exists t; eapply pre_grouped_finish.
        * eapply pre_target_path_grouped; eassumption.
        * eapply reachable_state_exec; eassumption.
        * exact Hending.
    - intro tr; split; intros [t Hrun].
      + exists t; eapply pre_macros_exec; exact Hrun.
      + destruct (pre_grouped_completes t0 tr t
          (pre_target_path_grouped t0 tr t n Hreachable Hboundary Hrun)
          (reachable_state_exec (pre_target r p) t0 tr t Hreachable Hrun))
          as [u [Hsilent [Hmacros Hend]]].
        exists u; exact Hmacros.
    - intro tr; split; intros [t [Hrun Hdiv]].
      + exists t; split; [eapply pre_macros_exec; exact Hrun|].
        apply pre_macros_diverges; exact Hdiv.
      + eapply pre_grouped_diverges.
        * eapply pre_target_path_grouped; eassumption.
        * eapply reachable_state_exec; eassumption.
        * exact Hdiv.
  Qed.

  (** Paired histories retain reachability, the exact source boundary and core agreement. *)
  Lemma pre_paired_facts : forall s0 t0 s t,
    pre_paired_run r p s0 t0 s t ->
    reachable_state (pre_source r) s /\ reachable_state (pre_target r p) t /\
    pre_boundary r p (point (pre_source_graph r) s) t /\ pre_core_agree r s t.
  Proof.
    intros s0 t0 s t Hpaired.
    induction Hpaired as [Hsource Htarget Hboundary Hcore|
      s t e l s' t' Hpaired [Hreachable_s [Hreachable_t [Hboundary Hcore]]]
      Hstep Htaken Hmacro Hcore'].
    - split; [exists s0, []; split; [exact Hsource|apply exec_refl]|].
      split; [exists t0, []; split; [exact Htarget|apply exec_refl]|].
      split; assumption.
    - split; [eapply reachable_state_step; eassumption|].
      split.
      { eapply reachable_state_exec; [exact Hreachable_t|eapply pre_macro_exec; exact Hmacro]. }
      split; [|exact Hcore'].
      pose proof (proj2 (taken_edge (proj1 (proj2 (proj2
        (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws)))) s l s' e
        Hreachable_s Hstep Htaken)) as Htarget.
      rewrite <- Htarget; eapply pre_macro_endpoint; exact Hmacro.
  Qed.

  Variables (s0 t0 : S).
  Hypothesis Hdeletions : forall e u, pre_deleted EE EU p e u = true ->
    pre_recomputed v e = Some u /\
      exists version, Map.get EE e (pre_reload_versions p) = Some version.
  Hypothesis Hcache : forall s t, pre_paired_run r p s0 t0 s t ->
    pre_cache_agree EN EE EU v r p (point (pre_source_graph r) s) s t.

  Local Lemma pre_deletion_case : forall e,
    (forall u, pre_deleted EE EU p e u = false) \/
    exists u version, pre_deleted EE EU p e u = true /\
      Map.get EE e (pre_reload_versions p) = Some version.
  Proof.
    intro e; destruct (pre_recomputed v e) as [u|] eqn:Hcomputed.
    - destruct (pre_deleted EE EU p e u) eqn:Hdeleted.
      + right; destruct (Hdeletions e u Hdeleted) as [_ [version Hreload]].
        exists u, version; split; assumption.
      + left; intro u'; destruct (pre_deleted EE EU p e u') eqn:Hdeleted'; [|reflexivity].
        destruct (Hdeletions e u' Hdeleted') as [Hcomputed' _].
        rewrite Hcomputed in Hcomputed'; injection Hcomputed' as ->; congruence.
    - left; intro u; destruct (pre_deleted EE EU p e u) eqn:Hdeleted; [|reflexivity].
      destruct (Hdeletions e u Hdeleted) as [Hcomputed' _]; congruence.
  Qed.

  Local Lemma pre_paired_edge_match : forall s t e,
    pre_paired_run r p s0 t0 s t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    (forall l s', step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      exists t', pre_macro_step r p e t l t' /\ pre_core_agree r s' t') /\
    (forall l t', pre_macro_step r p e t l t' ->
      exists s', step (pre_source r) s l s' /\ taken (pre_source_graph r) s l s' e /\
        pre_core_agree r s' t').
  Proof.
    intros s t e Hpaired Hpoint.
    destruct (pre_paired_facts s0 t0 s t Hpaired)
      as [Hreachable_s [Hreachable_t [Hboundary Hcore]]].
    destruct (pre_deletion_case e) as [Hkept|[u [version [Hdeleted Hreload]]]].
    - eapply pre_local_kept; eassumption.
    - eapply pre_local_replace; try eassumption.
      destruct (Hcache s t Hpaired) as [_ Hvalues].
      apply (Hvalues e u version); try assumption.
      destruct (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws) as [_ [Hgraph _]].
      rewrite <- Hgraph; symmetry; exact Hpoint.
  Qed.

  Local Lemma pre_paired_bisimulation :
    bisimulation (pre_source r) (pre_source_end r) (pre_macro_semantics r p)
      (pre_target_end r p) (pre_paired_run r p s0 t0).
  Proof.
    constructor.
    - intros s t k Hpaired.
      destruct (pre_paired_facts s0 t0 s t Hpaired)
        as [Hreachable_s [Hreachable_t [Hboundary Hcore]]].
      rewrite (pre_boundary_endings t (point (pre_source_graph r) s) k
        Hreachable_t Hboundary).
      eapply pre_local_endings; eauto.
    - intros s t l s' Hpaired Hstep.
      destruct (pre_paired_facts s0 t0 s t Hpaired)
        as [Hreachable_s [Hreachable_t [Hboundary Hcore]]].
      destruct (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws)
        as [_ [_ [Hgraph [_ [Hno_stays Hrest]]]]].
      destruct (edge_covers Hgraph s l s' Hreachable_s Hstep) as [Hstays|[e Htaken]].
      + exfalso; exact (Hno_stays s l s' Hstays).
      + assert (point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e)
          as Hpoint.
        { symmetry; apply (out_source (cfg_wf Hgraph)).
          exact (proj1 (taken_edge Hgraph s l s' e Hreachable_s Hstep Htaken)). }
        destruct (proj1 (pre_paired_edge_match s t e Hpaired Hpoint) l s' Hstep Htaken)
          as [t' [Hmacro Hcore']].
        exists t'; split; [exists e; exact Hmacro|].
        eapply pre_paired_step; eassumption.
    - intros s t l t' Hpaired [e Hmacro].
      destruct (pre_paired_facts s0 t0 s t Hpaired)
        as [Hreachable_s [Hreachable_t [Hboundary Hcore]]].
      assert (point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e)
        as Hpoint.
      { destruct Hmacro as [Hsource Hrest]; unfold pre_boundary in Hsource, Hboundary.
        rewrite Hboundary in Hsource; injection Hsource as Heq; exact Heq. }
      destruct (proj2 (pre_paired_edge_match s t e Hpaired Hpoint) l t' Hmacro)
        as [s' [Hstep [Htaken Hcore']]].
      exists s'; split; [exact Hstep|]; eapply pre_paired_step; eassumption.
  Qed.

  (** A cache invariant on paired histories suffices for the complete actual-path behavior proof. *)
  Lemma pre_cache_paths_behaviour :
    initial (pre_source r) s0 -> initial (pre_target r p) t0 ->
    pre_boundary r p (point (pre_source_graph r) s0) t0 -> pre_core_agree r s0 t0 ->
    same_behaviour (pre_source r) (pre_source_end r) s0
      (pre_target r p) (pre_target_end r p) t0.
  Proof.
    intros Hsource Htarget Hboundary Hcore.
    eapply same_behaviour_trans.
    - eapply bisimilar_same_behaviour; [exact pre_paired_bisimulation|].
      apply pre_paired_initial; assumption.
    - eapply pre_target_macro_behaviour; [|exact Hboundary].
      exists t0, []; split; [exact Htarget|apply exec_refl].
  Qed.
End TargetPaths.

(** * Source value regions *)

(** A region contains no syntactic kill after its last visit to the defining point. *)
Definition pre_cache_region {N E U} (g : Graph.t N E) (kill : E -> U -> bool)
    (q n : N) (u : U) : Prop :=
  dominates g q n /\ forall es, path g q es n ->
    Forall (fun e => Graph.target g e <> q) es -> Forall (fun e => kill e u = false) es.

Local Lemma pre_region_path_avoids {N E} (EN : encoding N) (g : Graph.t N E) q p n es :
  ready EN g (prepare EN g) -> reachable g n -> dominates g q p -> dominates g p n ->
  path g p es n -> Forall (fun e => Graph.target g e <> p) es ->
  Forall (fun e => Graph.target g e <> q) es.
Proof.
  intros Hready Hreachable Hqp Hpn Hpath Hclear.
  apply Forall_forall; intros e Hin Htarget.
  destruct (loop_path_split g p es n e Hpath Hin) as [first [last [Hfirst [Hlast Hsplit]]]].
  assert (Forall (fun a => Graph.target g a <> p) last) as Hlast_clear.
  { rewrite <- Hsplit in Hclear; apply Forall_app in Hclear; exact (proj2 Hclear). }
  rewrite Htarget in Hlast.
  pose proof (AnalysesSsaPreGraph.pre_dominance_suffix g p q last n Hpn Hlast Hlast_clear)
    as Hpq.
  assert (reachable g p) as Hp by (eapply dom_dominator_reachable; eassumption).
  assert (reachable g q) as Hq by (eapply dom_dominator_reachable; eassumption).
  assert (p = q) as Heq.
  { eapply idf_dominance_antisym; eassumption. }
  apply (proj1 (Forall_forall _ _) Hclear e Hin); congruence.
Qed.

(** A dominating cached definition inherits every non-killing region of its expression class. *)
Lemma pre_cache_region_weaken {N E U} (EN : encoding N) (g : Graph.t N E)
    (kill : E -> U -> bool) q p n u :
  ready EN g (prepare EN g) -> reachable g n ->
  dominates g q p -> dominates g p n -> pre_cache_region g kill q n u ->
  pre_cache_region g kill p n u.
Proof.
  intros Hready Hreachable Hqp Hpn [Hqn Hstable]; split; [exact Hpn|].
  intros es Hpath Hclear.
  pose proof (pre_region_path_avoids EN g q p n es Hready Hreachable Hqp Hpn Hpath Hclear)
    as Hclear_q.
  assert (reachable g p) as Hp by (eapply dom_dominator_reachable; eassumption).
  destruct (AnalysesSsaPreGraph.pre_dominating_path EN g q p Hp Hqp)
    as [prefix [Hprefix Hprefix_clear]].
  pose proof (Hstable (prefix ++ es) (idf_path_app g q prefix p es n Hprefix Hpath)) as Hkills.
  assert (Forall (fun e => Graph.target g e <> q) (prefix ++ es)) as Hfree.
  { apply Forall_app; split; assumption. }
  apply Hkills in Hfree; apply Forall_app in Hfree; exact (proj2 Hfree).
Qed.

Local Lemma pre_cache_region_last {N E U} (g : Graph.t N E) (kill : E -> U -> bool)
    q e u es :
  In e (Graph.out g (Graph.source g e)) -> Graph.target g e <> q ->
  pre_cache_region g kill q (Graph.target g e) u ->
  path g q es (Graph.source g e) -> Forall (fun a => Graph.target g a <> q) es ->
  Forall (fun a => kill a u = false) es /\ kill e u = false.
Proof.
  intros Hedge Htarget [Hdom Hstable] Hpath Hclear.
  assert (path g q (es ++ [e]) (Graph.target g e)) as Hextended.
  { eapply path_snoc; [exact Hpath|reflexivity|exact Hedge]. }
  assert (Forall (fun a => Graph.target g a <> q) (es ++ [e])) as Hfree.
  { apply Forall_app; split; [exact Hclear|constructor; [exact Htarget|constructor]]. }
  pose proof (Hstable _ Hextended Hfree) as Hkills; apply Forall_app in Hkills.
  split; [exact (proj1 Hkills)|].
  destruct Hkills as [Hprefix Hlast]; inversion Hlast; assumption.
Qed.

(** Stepping away from the defining point exposes the same region before a non-killing edge. *)
Lemma pre_cache_region_back {N E U} (EN : encoding N) (g : Graph.t N E)
    (kill : E -> U -> bool) q e u :
  reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
  Graph.target g e <> q -> pre_cache_region g kill q (Graph.target g e) u ->
  pre_cache_region g kill q (Graph.source g e) u /\ kill e u = false.
Proof.
  intros Hreachable Hedge Htarget Hregion.
  assert (q <> Graph.target g e) as Hdifferent by congruence.
  pose proof (AnalysesSsaPreGraph.pre_strict_target_dominates_source g e q Hedge
    (conj (proj1 Hregion) Hdifferent)) as Hdom.
  split.
  - split; [exact Hdom|]; intros es Hpath Hclear.
    exact (proj1 (pre_cache_region_last g kill q e u es Hedge Htarget Hregion Hpath Hclear)).
  - destruct (AnalysesSsaPreGraph.pre_dominating_path EN g q (Graph.source g e)
      Hreachable Hdom) as [es [Hpath Hclear]].
    exact (proj2 (pre_cache_region_last g kill q e u es Hedge Htarget Hregion Hpath Hclear)).
Qed.

(** A reusable FRG version supplies the source non-kill region used by its resolved cache slot. *)
Lemma pre_frg_cache_region {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n d q :
  frg_reusable a f u n d -> frg_version_point a d = Some q ->
  pre_cache_region (live_graph (point_model (pre_ssa_points a)))
    (kill (pre_genkill (pre_expression a))) q n u.
Proof.
  intros [[Hmember [Hexpr [q' [Hpoint [Hdom Hnearest]]]]] [q'' [Hpoint' Hstable]]] Hq.
  rewrite Hq in Hpoint, Hpoint'; injection Hpoint as ->; injection Hpoint' as ->.
  split; assumption.
Qed.

(** * Source frames on the actual paired history *)

Section SourceFrames.
  Context {S O B BE N E NT ET V K U C : Type}.
  Variables (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U).
  Variables (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U).
  Hypothesis Ha : pre_expr_ssa_laws EV a.
  Hypothesis Hlaws : pre_local_laws EBE EN EE EV EU a (pre_expression a)
    (pre_initial_available a) r p.

  (** A non-killing actual source edge preserves the realizer's expression value. *)
  Lemma pre_source_eval_frame : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e ->
    kill (pre_genkill (pre_expression a)) e u = false -> pre_eval r s' u = pre_eval r s u.
  Proof.
    intros s l s' e u Hreachable Hstep Htaken Hkill.
    destruct (pre_local_operands _ _ _ _ _ _ _ _ _ _ Hlaws) as [Heval Hrest].
    rewrite !Heval; eapply pre_local_kill_frame; eassumption.
  Qed.

  (** Generation-value agreement relates the stored pre-edge value to the actual successor. *)
  Lemma pre_source_eval_generated : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e ->
    In u (gen (pre_genkill (pre_expression a)) e) -> pre_eval r s' u = pre_eval r s u.
  Proof.
    intros s l s' e u Hreachable Hstep Htaken Hgen.
    destruct (pre_local_operands _ _ _ _ _ _ _ _ _ _ Hlaws) as [Heval Hrest].
    rewrite !Heval; eapply pre_local_gen_value; eassumption.
  Qed.

  (** A source-frame region and a cache frame preserve the same slot across the given macro. *)
  Lemma pre_region_cache_step : forall s t e l s' t' version q,
    ready EN (live_graph (point_model (pre_ssa_points a)))
      (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' ->
    pre_version_point (pre_expression a) version = Some q ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q ->
    pre_cache_region (live_graph (point_model (pre_ssa_points a)))
      (kill (pre_genkill (pre_expression a))) q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) (pre_version_expr version) ->
    pre_cached r t version = pre_eval r s (pre_version_expr version) ->
    pre_cached r t' version = pre_eval r s' (pre_version_expr version).
  Proof.
    intros s t e l s' t' version q Hready Hsource Htarget Hpoint Hboundary
      Hstep Htaken Hmacro Hversion Hnot_q Hregion Hcache.
    pose proof (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws) as
      [Hview [Hgraph [Hsource_graph Hrest]]].
    assert (cfg (pre_source_graph r) = live_graph (point_model (pre_ssa_points a))) as Hcfg.
    { rewrite Hgraph; symmetry; exact (pre_expr_point_graph EV a Ha). }
    assert (pre_version_written EE e version = false) as Hwritten.
    { apply (pre_version_unwritten_target EE (pre_expression a) e version q Hversion).
      rewrite <- (pre_expr_point_graph EV a Ha); exact Hnot_q. }
    pose proof (view_point_reachable (pre_source r) (pre_source_graph r) s
      Hsource_graph Hsource) as Hreachable.
    rewrite Hpoint, Hcfg in Hreachable.
    pose proof (proj1 (taken_edge Hsource_graph s l s' e Hsource Hstep Htaken)) as Hedge.
    rewrite Hpoint, Hcfg in Hedge.
    destruct (pre_cache_region_back EN _ _ q e (pre_version_expr version)
      Hreachable Hedge Hnot_q Hregion) as [Hbefore Hkill].
    assert (pre_cached r t' version = pre_cached r t version) as Hframe.
    { eapply pre_local_cache_frame; eassumption. }
    rewrite Hframe, Hcache; symmetry; eapply pre_source_eval_frame; eassumption.
  Qed.

  (** A kept computation's stored pre-edge value agrees with its actual source successor. *)
  Lemma pre_computed_cache_step : forall s t e u l s' t',
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    pre_recomputed (pre_expression a) e = Some u -> pre_deleted EE EU p e u = false ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_cached r t' (PreComputed e u) = pre_eval r s' u.
  Proof.
    intros s t e u l s' t' Hsource Htarget Hcomputed Hkept Hstep Htaken Hmacro.
    assert (pre_cached r t' (PreComputed e u) = pre_eval r s u) as Hcompute.
    { eapply pre_local_compute; eassumption. }
    rewrite Hcompute; symmetry; eapply pre_source_eval_generated; try eassumption.
    destruct (pre_local_operands _ _ _ _ _ _ _ _ _ _ Hlaws) as [_ [_ [_ Hgen]]].
    apply Hgen; exact Hcomputed.
  Qed.

  (** A cross-block edge has no expression kill because it defines no SSA operands. *)
  Lemma pre_cross_expression_frame : forall be incoming u,
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    pre_expr_in_family a u -> kill (pre_genkill (pre_expression a)) incoming u = false.
  Proof.
    intros be incoming u Hindex Hfamily.
    destruct (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) be incoming) Hindex) as [Hedge Hbe].
    destruct (kill (pre_genkill (pre_expression a)) incoming u) eqn:Hkill; [|reflexivity].
    destruct (pre_expr_kill_operand EV a Ha incoming u Hedge Hfamily Hkill)
      as [x [Hoperand Hdefined]].
    rewrite (pre_expr_cross_no_defs EV a Ha incoming be Hedge Hbe) in Hdefined; contradiction.
  Qed.

  (** The actual two source steps identify the same incoming environment used by the phi read. *)
  Lemma pre_source_phi_value : forall be incoming s0 l0 s1 l1 s2 u translated,
    pre_phi_source_laws EBE EV a r ->
    reachable_state (pre_source r) s0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 incoming ->
    step (pre_source r) s1 l1 s2 ->
    taken (pre_source_graph r) s1 l1 s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_expr_in_family a u -> pre_phi_translate a be u = Some translated ->
    pre_eval r s2 u = pre_eval r s0 translated.
  Proof.
    intros be incoming s0 l0 s1 l1 s2 u translated Hphi Hsource Hindex Hcross Htaken
      Hparameter Hparameter_taken Hfamily Htranslate.
    destruct (pre_local_operands _ _ _ _ _ _ _ _ _ _ Hlaws) as [Heval Hrest].
    rewrite !Heval, (pre_expr_runtime EV a Ha s2 u),
      (pre_expr_runtime EV a Ha s0 translated).
    etransitivity.
    - apply (pre_expr_operand_support EV a Ha u).
      intros x Hoperand; eapply Hphi; eassumption.
    - apply (pre_expr_translation_eval EV a Ha be u translated).
      + exact (proj2 (AnalysesSsaPre.pre_point_index_block_listed EBE
          (pre_ssa_points a) be incoming (pre_expr_points EV a Ha) Hindex)).
      + exact Hfamily.
      + exact Htranslate.
  Qed.

  (** An inserted incoming expression retains its pre-cross source value on this very macro. *)
  Lemma pre_phi_inserted_value : forall be incoming s t l s' t' translated,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    pre_core_agree r s t -> pre_expr_in_family a translated ->
    pre_inserted EE EU p incoming translated = true ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' incoming ->
    pre_macro_step r p incoming t l t' ->
    pre_cached r t' (PreInserted incoming translated) = pre_eval r s translated.
  Proof.
    intros be incoming s t l s' t' translated Hsource Htarget Hindex Hcore Hfamily Hinsert
      Hstep Htaken Hmacro.
    assert (pre_cached r t' (PreInserted incoming translated) = pre_eval r s' translated)
      as Hwritten.
    { eapply pre_local_insert; eassumption. }
    rewrite Hwritten; eapply pre_source_eval_frame; try eassumption.
    eapply pre_cross_expression_frame; eassumption.
  Qed.

  (** A simultaneous phi read uses the selected slot of the actual incoming macro's endpoint. *)
  Lemma pre_phi_cache_step : forall be incoming s0 t0 l0 s1 t1 l1 s2 t2 u translated selected,
    pre_phi_source_laws EBE EV a r ->
    reachable_state (pre_source r) s0 -> reachable_state (pre_target r p) t0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 incoming ->
    pre_macro_step r p incoming t0 l0 t1 ->
    step (pre_source r) s1 l1 s2 ->
    taken (pre_source_graph r) s1 l1 s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_macro_step r p
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be))
      t1 l1 t2 ->
    pre_expr_in_family a u -> pre_phi_translate a be u = Some translated ->
    Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be),
        incoming),u) (pre_phi_versions p) = Some selected ->
    pre_cached r t1 selected = pre_eval r s0 translated ->
    pre_cached r t2 (PreMerged
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) u) =
      pre_eval r s2 u.
  Proof.
    intros be incoming s0 t0 l0 s1 t1 l1 s2 t2 u translated selected Hphi Hsource Htarget
      Hindex Hcross Hcross_taken Hcross_macro Hparameter Hparameter_taken Hparameter_macro
      Hfamily Htranslate Hselected Hcache.
    pose proof (pre_local_phi_select _ _ _ _ _ _ _ _ _ _ Hlaws s0 t0 s1 t1 s2 t2 be
      incoming l0 l1 (PreMerged
        (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) u)
      Hsource Htarget Hindex Hcross Hcross_taken Hcross_macro Hparameter Hparameter_taken
      Hparameter_macro) as Hupdate.
    unfold pre_phi_update in Hupdate; rewrite Pos.eqb_refl, Hselected in Hupdate.
    rewrite Hupdate, Hcache; symmetry; eapply pre_source_phi_value; eassumption.
  Qed.

  (** A paired nonentry parameter source retains its actual immediately preceding incoming macro. *)
  Lemma pre_paired_parameter_history : forall s0 t0 s t b,
    pre_paired_run r p s0 t0 s t -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
    point (pre_source_graph r) s = Graph.source (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b) ->
    exists before_s before_t incoming be l,
      pre_paired_run r p s0 t0 before_s before_t /\
      step (pre_source r) before_s l s /\ taken (pre_source_graph r) before_s l s incoming /\
      pre_macro_step r p incoming before_t l t /\
      Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming /\
      Graph.target (block_graph (pre_ssa_points a)) be = b.
  Proof.
    intros s0 t0 s t b Hpaired Hb Hnonentry Hpoint.
    destruct (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws) as
      [Hview [Hgraph [Hsource_graph Hrest]]].
    assert (cfg (pre_source_graph r) = live_graph (point_model (pre_ssa_points a))) as Hcfg.
    { rewrite Hgraph; symmetry; exact (pre_expr_point_graph EV a Ha). }
    destruct Hpaired as [Hsource Htarget Hboundary Hcore|
      before_s before_t incoming l s t Hpaired Hstep Htaken Hmacro Hcore].
    - exfalso; apply (pre_parameter_source_nonentry EV a b Ha Hb Hnonentry).
      pose proof (entry_points Hsource_graph s0 Hsource) as Hentry.
      rewrite Hcfg, Hpoint in Hentry; exact Hentry.
    - destruct (pre_paired_facts EBE EN EE EV EU a (pre_expression a)
        (pre_initial_available a) r p Hlaws s0 t0 before_s before_t Hpaired)
        as [Hreachable Hfacts].
      destruct (taken_edge Hsource_graph before_s l s incoming Hreachable Hstep Htaken)
        as [Hout Htarget].
      assert (In incoming (edges_of (cfg (pre_source_graph r)))) as Hedge.
      { apply in_flat_map; exists (point (pre_source_graph r) before_s); split; [|exact Hout].
        apply (reachable_in_nodes _ _ (cfg_wf Hsource_graph)).
        eapply view_point_reachable; eassumption. }
      rewrite Hcfg in Hedge, Htarget; rewrite Hpoint in Htarget.
      destruct (pre_parameter_predecessor EBE (pre_ssa_points a) b incoming
        (pre_expr_points EV a Ha) Hb Hedge Htarget) as [be [Hindex Hblock]].
      exists before_s, before_t, incoming, be, l.
      split; [exact Hpaired|]; split; [exact Hstep|]; split; [exact Htaken|].
      split; [exact Hmacro|]; split; assumption.
  Qed.

  (** Resolving an FRG class transfers its non-kill region to that slot's actual definition. *)
  Lemma pre_scope_reuse_region : forall (EB : encoding B) f scope d u n version,
    ready EN (live_graph (point_model (pre_ssa_points a)))
      (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
    reachable (live_graph (point_model (pre_ssa_points a))) n ->
    pre_finalize_scope_origin EB EE EU a scope -> frg_reusable a f u n d ->
    AnalysesSsaPre.pre_finalize_available EB EN EE EU a
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      scope d u n = Some version ->
    exists q, pre_version_point (pre_expression a) version = Some q /\
      pre_cache_region (live_graph (point_model (pre_ssa_points a)))
        (kill (pre_genkill (pre_expression a))) q n u.
  Proof.
    intros EB f scope d u n version Hready Hreachable Hscope Hreusable Havailable.
    pose proof (pre_finalize_available_lookup EB EN EE EU a _ scope d u n version Havailable)
      as Hslot.
    destruct (Hscope d version Hslot) as [Hexpr [class_point [q [Hclass [Hpoint Horigin]]]]].
    unfold AnalysesSsaPre.pre_finalize_available in Havailable; rewrite Hslot, Hpoint in Havailable.
    destruct (Pos.eqb (encode EU (pre_version_expr version)) (encode EU u)); [|discriminate].
    destruct (dominates_b EN
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) q n)
      eqn:Hquery; [|discriminate].
    assert (dominates (live_graph (point_model (pre_ssa_points a))) q n) as Hdom.
    { exact (proj1 (proj2 (proj2 (dominator_tree_sound EN _ _ Hready))) q n Hquery). }
    exists q; split; [exact Hpoint|].
    eapply pre_cache_region_weaken; [exact Hready|exact Hreachable|exact Horigin|exact Hdom|].
    eapply pre_frg_cache_region; eassumption.
  Qed.
End SourceFrames.

(** Every produced reload has a non-killing region from its actual resolved definition. *)
Theorem ssa_pre_reload_regions {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in forall e u version,
    pre_deleted EE EU p e u = true -> Map.get EE e (pre_reload_versions p) = Some version ->
    exists q, pre_version_point (pre_expression a) version = Some q /\
      pre_cache_region (live_graph (point_model (pre_ssa_points a)))
        (kill (pre_genkill (pre_expression a))) q
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) u.
Proof.
  intros Ha Hb Hn; cbn zeta; intros e u version Hdeleted Hreload.
  pose (f := build_frg EB EBE EN EE EV EU a).
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  destruct (ssa_pre_reload_origins EB EBE EN EE EV EU a Ha Hb Hn e version Hreload)
    as [d [Hclass [Hexpr [class_point [q [Hclass_point [Hversion_point Horigin]]]]]]].
  change (Map.get EE e (frg_occurrence_index f) = Some d) in Hclass.
  destruct (ssa_pre_output_supported EB EBE EN EE EV EU a Ha Hb Hn)
    as [Hlisted Hremaining].
  pose proof (Hlisted e version Hreload) as Hedge.
  destruct (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e u Hdeleted)
    as [Hcomputed Hreload_exists].
  pose proof (ssa_pre_place_legal EB EBE EN EE EV EU a Ha Hb Hn) as Hlegal.
  unfold pre_placement_legal in Hlegal; rewrite <- (pre_expr_point_graph EV a Ha) in Hlegal.
  destruct (proj2 Hlegal e u Hedge Hdeleted) as [_ [Hpure [selected [point
    [Hselected [Hpoint Hdom]]]]]].
  rewrite Hreload in Hselected; injection Hselected as <-.
  rewrite Hversion_point in Hpoint; injection Hpoint as <-.
  destruct (AnalysesSsaPreGraph.pre_listed_edge_out _ e (proj1 Hn) Hedge)
    as [Hsource_node Hout].
  pose proof (pre_expr_reachable_points EV a Ha _ Hsource_node) as Hreachable_source.
  assert (frg_reusable a f u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d) as Hreusable.
  { destruct (frg_occurrence_exact _ _ _ _ _ _ _ _ Hfrg e u Hedge Hcomputed Hpure)
      as [selected [Hselected [Hmember [Hselected_expr Hcases]]]].
    rewrite Hclass in Hselected; injection Hselected as <-.
    destruct Hcases as [Hfresh|Hreuse]; [|exact Hreuse].
    subst d; cbn [frg_version_point] in Hclass_point; injection Hclass_point as <-.
    assert (dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as Hback.
    { eapply dominates_trans; eassumption. }
    pose proof (AnalysesSsaPreGraph.pre_internal_immediate EV a e Ha Hedge
      (proj1 (pre_expr_real_internal EV a Ha e u Hcomputed))) as [[Hforward Hdifferent] Hminimal].
    exfalso; apply Hdifferent.
    eapply idf_dominance_antisym; [exact Hn|exact Hreachable_source| |exact Hforward|exact Hback].
    apply (reachable_step e); assumption. }
  exists q; split; [exact Hversion_point|].
  eapply pre_cache_region_weaken; [exact Hn|exact Hreachable_source|exact Horigin|exact Hdom|].
  eapply pre_frg_cache_region; eassumption.
Qed.

(** A regular selected phi input has a non-kill region at that actual incoming edge's source. *)
Theorem ssa_pre_phi_regions {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in forall b u be incoming version,
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,incoming),u) (pre_phi_versions p) = Some version ->
    pre_finalize_regular version ->
    exists translated q, pre_phi_translate a be u = Some translated /\
      pre_version_expr version = translated /\
      pre_version_point (pre_expression a) version = Some q /\
      pre_cache_region (live_graph (point_model (pre_ssa_points a)))
        (kill (pre_genkill (pre_expression a))) q
        (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming) translated.
Proof.
  intros Ha Hb Hn; cbn zeta; intros b u be incoming version Hindex Htarget Hget Hregular.
  pose (f := build_frg EB EBE EN EE EV EU a).
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  destruct (ssa_pre_phi_origins EB EBE EN EE EV EU a Ha Hb Hn
    (parameter_edge (pre_ssa_points a) b) incoming u version Hget Hregular)
    as [block [edge [op [Hparameter [Hindex' [Htarget' [Hbinding
      [Hexpr_origin [class_point [q [Hclass_point [Hversion_point Horigin]]]]]]]]]]]].
  assert (edge = be) as ->.
  { pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) edge incoming) Hindex')) as Hproject.
    pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) be incoming) Hindex)) as Hproject'; congruence. }
  assert (block = b) as -> by congruence.
  change (Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
    (frg_phi_operands f) = Some op) in Hbinding.
  destruct (ssa_pre_phi_versions_correct EB EBE EN EE EV EU a Ha Hb Hn b u be incoming version
    Hindex Htarget Hget) as [translated [Htranslate [Hexpr Hdefinition]]].
  destruct Hdefinition as [Hinserted|[point [Hpoint Hdom]]].
  { subst version; contradiction. }
  rewrite Hversion_point in Hpoint; injection Hpoint as <-.
  assert (frg_operand_version op <> FrUnavailable translated) as Havailable.
  { intro Heq; rewrite Heq in Hclass_point; discriminate. }
  pose proof (proj2 (frg_operand_selection _ _ _ _ _ _ _ _ Hfrg b u be op incoming translated
    Hbinding Hindex Htranslate) Havailable) as Hreusable.
  destruct (AnalysesSsaPre.pre_point_index_block_listed EBE (pre_ssa_points a) be incoming
    (pre_expr_points EV a Ha) Hindex) as [Hedge Hbe].
  destruct (AnalysesSsaPreGraph.pre_listed_edge_out _ incoming (proj1 Hn) Hedge)
    as [Hsource Hout].
  exists translated, q; split; [exact Htranslate|]; split; [exact Hexpr|].
  split; [exact Hversion_point|].
  eapply pre_cache_region_weaken; [exact Hn| |exact Horigin|exact Hdom|].
  - apply (pre_expr_reachable_points EV a Ha); exact Hsource.
  - eapply pre_frg_cache_region; eassumption.
Qed.

(** * Cache induction on the paired history *)

(** Every retained definition holds its source value throughout its non-killing region. *)
Definition pre_regular_cache {S O B BE N E NT ET V K U C}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C)
    f facts p s t : Prop :=
  forall version q, pre_finalize_kept_version EB EE EU a f facts p version ->
    pre_version_point (pre_expression a) version = Some q ->
    pre_cache_region (live_graph (point_model (pre_ssa_points a)))
      (kill (pre_genkill (pre_expression a))) q (point (pre_source_graph r) s)
      (pre_version_expr version) ->
    pre_cached r t version = pre_eval r s (pre_version_expr version).

(** A parameter source retains its preceding cross macro and the pre-cross values it reads. *)
Definition pre_pending_phi_cache {S O B BE N E NT ET V K U C}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C)
    (f : factored_redundancy_graph B BE E U) facts p s0 t0 s t : Prop :=
  forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
    point (pre_source_graph r) s = Graph.source (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b) ->
    exists before_s before_t incoming be l,
      pre_paired_run r p s0 t0 before_s before_t /\
      step (pre_source r) before_s l s /\ taken (pre_source_graph r) before_s l s incoming /\
      pre_macro_step r p incoming before_t l t /\
      Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming /\
      Graph.target (block_graph (pre_ssa_points a)) be = b /\
      forall u, FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
        AnalysesSsaPre.pre_finalize_will EB EU facts (b,u) = true ->
        exists translated selected, pre_phi_translate a be u = Some translated /\
          Map.get (pair_encoding (pair_encoding EE EE) EU)
            ((parameter_edge (pre_ssa_points a) b,incoming),u) (pre_phi_versions p) =
              Some selected /\
          pre_cached r t selected = pre_eval r before_s translated.

Section PlacementCache.
  Context {S O B BE N E NT ET V K U C : Type}.
  Variables (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U).
  Variables (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C).
  Let f := build_frg EB EBE EN EE EV EU a.
  Let facts := solve_ssapre EB EBE EN EE EV EU a f.
  Let p := ssa_pre_place EB EBE EN EE EV EU a.
  Hypothesis Ha : pre_expr_ssa_laws EV a.
  Hypothesis Hb : ready EB (block_graph (pre_ssa_points a))
    (prepare EB (block_graph (pre_ssa_points a))).
  Hypothesis Hn : ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))).
  Hypothesis Hphi : pre_phi_source_laws EBE EV a r.
  Hypothesis Hlaws : pre_local_laws EBE EN EE EV EU a (pre_expression a)
    (pre_initial_available a) r p.

  Local Lemma pre_placement_frg : frg_wf EB EBE EN EE EV EU a f.
  Proof.
    apply build_frg_wf; assumption.
  Qed.

  Local Lemma pre_placement_cfg : cfg (pre_source_graph r) =
      live_graph (point_model (pre_ssa_points a)).
  Proof.
    destruct (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws) as [Hview [Hgraph Hrest]].
    rewrite Hgraph; symmetry; exact (pre_expr_point_graph EV a Ha).
  Qed.

  Local Lemma pre_placement_phi_site b u :
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
      ~ In b (Graph.entries (block_graph (pre_ssa_points a))).
  Proof.
    intro Hmember.
    destruct (proj1 (frg_phi_exact _ _ _ _ _ _ _ _ pre_placement_frg b u) Hmember)
      as [Hfamily [Hpure Hneeded]].
    eapply pre_phi_needed_nonentry; eassumption.
  Qed.

  Local Lemma pre_placement_computed_kept e u :
    pre_finalize_kept_version EB EE EU a f facts p (PreComputed e u) ->
    pre_deleted EE EU p e u = false.
  Proof.
    intros [Hedge [Hcomputed Hnone]].
    destruct (pre_deleted EE EU p e u) eqn:Hdeleted; [|reflexivity].
    destruct (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e u Hdeleted)
      as [Hreal [version Hget]].
    change (Map.get EE e (pre_reload_versions p) = Some version) in Hget.
    rewrite Hnone in Hget; discriminate.
  Qed.

  Local Lemma pre_placement_inserted parameter incoming u e translated :
    Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),u)
      (pre_phi_versions p) = Some (PreInserted e translated) ->
    pre_inserted EE EU p e translated = true.
  Proof.
    intro Hget; destruct (AnalysesSsaPre.pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn)
      as [scope Hraw].
    apply (proj2 (AnalysesSsaPre.pre_finalize_materialized_insertion EE EU _ _ e translated
      (pre_finalize_phi_wf _ _ _ _ _ _ Hraw))).
    exists parameter, incoming, u; exact Hget.
  Qed.

  Local Lemma pre_placement_cross_unwritten be incoming version :
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    pre_finalize_kept_version EB EE EU a f facts p version ->
    pre_version_written EE incoming version = false.
  Proof.
    intros Hindex Hkept.
    destruct (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) be incoming) Hindex) as [Hedge Hproject].
    destruct version as [u|e u|e u|e u]; cbn [pre_version_written]; [reflexivity| |contradiction|].
    - destruct Hkept as [Hlisted [Hcomputed Hnone]].
      apply Pos.eqb_neq; intro Heq; apply (encode_injective EE) in Heq; subst e.
      pose proof (proj1 (pre_expr_real_internal EV a Ha incoming u Hcomputed)) as Hinternal;
        congruence.
    - destruct Hkept as [b [-> [Hmember Hwill]]].
      destruct (pre_placement_phi_site b u Hmember) as [Hb' Hnonentry].
      destruct (AnalysesSsaPreGraph.pre_parameter_edge_listed (pre_ssa_points a) b
        (pre_expr_points EV a Ha) Hb') as [Hparameter Hinternal].
      apply Pos.eqb_neq; intro Heq; apply (encode_injective EE) in Heq.
      rewrite <- Heq in Hinternal; congruence.
  Qed.

  Local Lemma pre_placement_taken s l s' e :
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e ->
    point (pre_source_graph r) s =
      Graph.source (live_graph (point_model (pre_ssa_points a))) e /\
    point (pre_source_graph r) s' =
      Graph.target (live_graph (point_model (pre_ssa_points a))) e /\
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))).
  Proof.
    intros Hreachable Hstep Htaken.
    pose proof (proj1 (proj2 (proj2 (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws)))) as Hgraph.
    destruct (taken_edge Hgraph s l s' e Hreachable Hstep Htaken) as [Hout Htarget].
    assert (In (point (pre_source_graph r) s) (Graph.nodes (cfg (pre_source_graph r)))) as Hnode.
    { eapply reachable_in_nodes; [exact (cfg_wf Hgraph)|].
      eapply view_point_reachable; eassumption. }
    split.
    - rewrite <- pre_placement_cfg; symmetry; exact (out_source (cfg_wf Hgraph) _ _ Hout).
    - split; [rewrite <- pre_placement_cfg; symmetry; exact Htarget|].
      rewrite <- pre_placement_cfg; apply in_flat_map; eexists; split; eassumption.
  Qed.

  Local Lemma pre_placement_regular_initial s t :
    initial (pre_source r) s -> initial (pre_target r p) t -> pre_core_agree r s t ->
    pre_regular_cache EB EE EU a r f facts p s t.
  Proof.
    intros Hsource Htarget Hcore version q Hkept Hpoint Hregion.
    pose proof (proj1 (proj2 (proj2 (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws)))) as Hgraph.
    pose proof (entry_points Hgraph s Hsource) as Hentry; rewrite pre_placement_cfg in Hentry.
    pose proof (pre_dominates_entry _ q _ Hentry (proj1 Hregion)) as Heq; subst q.
    destruct version as [u|e u|e u|e u].
    - eapply pre_local_initial; eassumption.
    - destruct Hkept as [Hedge [Hcomputed Hnone]].
      cbn [pre_version_point] in Hpoint; rewrite <- (pre_expr_point_graph EV a Ha) in Hpoint.
      injection Hpoint as Hpoint; exfalso.
      exact (pre_point_entry_no_incoming EV a e _ Ha Hedge Hentry Hpoint).
    - contradiction.
    - destruct Hkept as [b [-> [Hmember Hwill]]].
      destruct (pre_placement_phi_site b u Hmember) as [Hb' Hnonentry].
      pose proof (proj1 (AnalysesSsaPreGraph.pre_parameter_edge_listed (pre_ssa_points a) b
        (pre_expr_points EV a Ha) Hb')) as Hedge.
      cbn [pre_version_point] in Hpoint; rewrite <- (pre_expr_point_graph EV a Ha) in Hpoint.
      injection Hpoint as Hpoint; exfalso.
      exact (pre_point_entry_no_incoming EV a _ _ Ha Hedge Hentry Hpoint).
  Qed.

  Local Lemma pre_placement_pending_initial s0 t0 :
    initial (pre_source r) s0 -> pre_pending_phi_cache EB EBE EE EU a r f facts p s0 t0 s0 t0.
  Proof.
    intros Hsource b Hb' Hnonentry Hpoint; exfalso.
    apply (pre_parameter_source_nonentry EV a b Ha Hb' Hnonentry).
    pose proof (proj1 (proj2 (proj2 (pre_local_graph _ _ _ _ _ _ _ _ _ _ Hlaws)))) as Hgraph.
    pose proof (entry_points Hgraph s0 Hsource) as Hentry.
    rewrite pre_placement_cfg, Hpoint in Hentry; exact Hentry.
  Qed.

  Local Lemma pre_placement_phi_choice b u be incoming version :
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,incoming),u) (pre_phi_versions p) = Some version ->
    exists translated, pre_phi_translate a be u = Some translated /\
      pre_version_expr version = translated /\
      (version = PreInserted incoming translated \/ pre_finalize_regular version).
  Proof.
    intros Hindex Hget.
    destruct (AnalysesSsaPre.pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn)
      as [scope Hraw].
    destruct (pre_finalize_phis_safe _ _ _ _ _ _ Hraw
      (parameter_edge (pre_ssa_points a) b) incoming u version Hget)
      as [block [edge [translated [Hindex' [Htarget [Hparameter
        [Htranslate [Hexpr Horigin]]]]]]]].
    pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) be incoming) Hindex)) as Hproject.
    pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
      (pre_expr_points EV a Ha) edge incoming) Hindex')) as Hproject'.
    assert (edge = be) as -> by congruence.
    exists translated; split; [exact Htranslate|]; split; [exact Hexpr|].
    destruct Horigin as [[Hinsert Hrest]|[Hregular Hdefinition]];
      [left; exact Hinsert|right; exact Hregular].
  Qed.

  Local Lemma pre_placement_pending_step s0 t0 s t e l s' t' :
    pre_paired_run r p s0 t0 s t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_regular_cache EB EE EU a r f facts p s t ->
    pre_pending_phi_cache EB EBE EE EU a r f facts p s0 t0 s' t'.
  Proof.
    intros Hpaired Hstep Htaken Hmacro Hcache b Hb' Hnonentry Hpoint.
    destruct (pre_paired_facts EBE EN EE EV EU a (pre_expression a) (pre_initial_available a)
      r p Hlaws s0 t0 s t Hpaired) as [Hsource [Htarget [Hboundary Hcore]]].
    destruct (pre_placement_taken s l s' e Hsource Hstep Htaken)
      as [Hbefore [Hafter Hedge]].
    destruct (pre_parameter_predecessor EBE (pre_ssa_points a) b e
      (pre_expr_points EV a Ha) Hb' Hedge (eq_trans (eq_sym Hafter) Hpoint))
      as [be [Hindex Hblock]].
    exists s, t, e, be, l; split; [exact Hpaired|]; split; [exact Hstep|].
    split; [exact Htaken|]; split; [exact Hmacro|]; split; [exact Hindex|].
    split; [exact Hblock|]; intros u Hmember Hwill.
    destruct (AnalysesSsaPre.pre_point_index_block_listed EBE (pre_ssa_points a) be e
      (pre_expr_points EV a Ha) Hindex) as [Hlisted Hbe].
    destruct (ssa_pre_phi_inputs_complete EB EBE EN EE EV EU a Ha Hb Hn b u be e Hmember
      Hwill Hbe Hblock Hindex) as [selected Hselected].
    change (Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,e),u) (pre_phi_versions p) = Some selected)
      in Hselected.
    destruct (pre_placement_phi_choice b u be e selected Hindex Hselected)
      as [translated [Htranslate [Hexpr Hchoice]]].
    exists translated, selected; split; [exact Htranslate|]; split; [exact Hselected|].
    destruct Hchoice as [->|Hregular].
    - apply (pre_phi_inserted_value EBE EN EE EV EU a r p Ha Hlaws be e s t l s' t'
        translated); try assumption.
      + destruct (proj1 (frg_phi_exact _ _ _ _ _ _ _ _ pre_placement_frg b u) Hmember)
          as [Hfamily Hrest].
        eapply pre_family_translate; eassumption.
      + eapply pre_placement_inserted; exact Hselected.
    - pose proof (proj2 (ssa_pre_selected_versions_kept EB EBE EN EE EV EU a Ha Hb Hn)
        ((parameter_edge (pre_ssa_points a) b,e),u) selected Hselected Hregular) as Hkept.
      destruct (ssa_pre_phi_regions EB EBE EN EE EV EU a Ha Hb Hn b u be e selected
        Hindex Hblock Hselected Hregular)
        as [actual [q [Htranslate' [Hexpr' [Hdefinition Hregion]]]]].
      assert (actual = translated) as -> by congruence.
      assert (pre_cached r t selected = pre_eval r s translated) as Hsaved.
      { rewrite <- Hexpr; apply (Hcache selected q); [exact Hkept|exact Hdefinition|].
        rewrite Hexpr, Hbefore; exact Hregion. }
      assert (pre_cached r t' selected = pre_cached r t selected) as Hframe.
      { eapply pre_local_cache_frame; try eassumption.
        - rewrite pre_placement_cfg; exact Hbefore.
        - eapply pre_placement_cross_unwritten; eassumption. }
      rewrite Hframe; exact Hsaved.
  Qed.

  Local Lemma pre_placement_merged_step s0 t0 s t l s' t' b u :
    pre_paired_run r p s0 t0 s t ->
    step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' (parameter_edge (pre_ssa_points a) b) ->
    pre_macro_step r p (parameter_edge (pre_ssa_points a) b) t l t' ->
    pre_pending_phi_cache EB EBE EE EU a r f facts p s0 t0 s t ->
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    AnalysesSsaPre.pre_finalize_will EB EU facts (b,u) = true ->
    pre_cached r t' (PreMerged (parameter_edge (pre_ssa_points a) b) u) = pre_eval r s' u.
  Proof.
    intros Hpaired Hstep Htaken Hmacro Hpending Hmember Hwill.
    destruct (pre_paired_facts EBE EN EE EV EU a (pre_expression a) (pre_initial_available a)
      r p Hlaws s0 t0 s t Hpaired) as [Hsource [Htarget [Hboundary Hcore]]].
    destruct (pre_placement_taken s l s' _ Hsource Hstep Htaken) as [Hbefore Hrest].
    destruct (pre_placement_phi_site b u Hmember) as [Hb' Hnonentry].
    destruct (Hpending b Hb' Hnonentry Hbefore) as [before_s [before_t [incoming [be [cross_l
      [Hprefix [Hcross [Hcross_taken [Hcross_macro [Hindex [Hblock Hvalues]]]]]]]]]]].
    destruct (Hvalues u Hmember Hwill)
      as [translated [selected [Htranslate [Hselected Hcache]]]].
    destruct (pre_paired_facts EBE EN EE EV EU a (pre_expression a) (pre_initial_available a)
      r p Hlaws s0 t0 before_s before_t Hprefix) as [Hsource_before [Htarget_before Hfacts]].
    rewrite <- Hblock.
    eapply (pre_phi_cache_step EBE EN EE EV EU a r p Ha Hlaws be incoming before_s before_t
      cross_l s t l s' t' u translated selected); try rewrite Hblock; try eassumption.
    exact (proj1 (proj1 (frg_phi_exact _ _ _ _ _ _ _ _ pre_placement_frg b u) Hmember)).
  Qed.

  Local Lemma pre_placement_initial_point u q :
    pre_version_point (pre_expression a) (PreInitial u) = Some q ->
    In q (Graph.entries (live_graph (point_model (pre_ssa_points a)))).
  Proof.
    intro Hpoint; destruct (pre_expr_entry_position EV a Ha)
      as [entry [first [Hblock [Hentries Hfirst]]]].
    cbn [pre_version_point] in Hpoint.
    rewrite <- (pre_expr_point_graph EV a Ha), Hentries in Hpoint.
    injection Hpoint as <-; rewrite Hentries; left; reflexivity.
  Qed.

  Local Lemma pre_placement_regular_step s0 t0 s t e l s' t' :
    pre_paired_run r p s0 t0 s t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_regular_cache EB EE EU a r f facts p s t ->
    pre_pending_phi_cache EB EBE EE EU a r f facts p s0 t0 s t ->
    pre_regular_cache EB EE EU a r f facts p s' t'.
  Proof.
    intros Hpaired Hstep Htaken Hmacro Hcache Hpending version q Hkept Hdefinition Hregion.
    destruct (pre_paired_facts EBE EN EE EV EU a (pre_expression a) (pre_initial_available a)
      r p Hlaws s0 t0 s t Hpaired) as [Hsource [Htarget [Hboundary Hcore]]].
    destruct (pre_placement_taken s l s' e Hsource Hstep Htaken)
      as [Hbefore [Hafter Hedge]].
    rewrite Hafter in Hregion.
    destruct (dfs_eq_dec EN (Graph.target (live_graph (point_model (pre_ssa_points a))) e) q)
      as [Hwriting|Hother].
    - destruct version as [u|writer u|writer u|writer u].
      + exfalso; exact (pre_point_entry_no_incoming EV a e q Ha Hedge
          (pre_placement_initial_point u q Hdefinition) Hwriting).
      + destruct Hkept as [Hlisted [Hcomputed Hnone]].
        cbn [pre_version_point] in Hdefinition.
        rewrite <- (pre_expr_point_graph EV a Ha) in Hdefinition.
        injection Hdefinition as Hwriter.
        assert (e = writer) as ->.
        { eapply AnalysesSsaPreGraph.pre_internal_incoming_unique.
          - exact (pre_expr_points EV a Ha).
          - exact Hlisted.
          - exact (proj1 (pre_expr_real_internal EV a Ha writer u Hcomputed)).
          - exact Hedge.
          - rewrite Hwriting, Hwriter; reflexivity. }
        eapply (pre_computed_cache_step EBE EN EE EV EU a r p Hlaws);
          try eassumption.
        apply pre_placement_computed_kept; repeat split; assumption.
      + contradiction.
      + destruct Hkept as [b [-> [Hmember Hwill]]].
        destruct (pre_placement_phi_site b u Hmember) as [Hb' Hnonentry].
        destruct (AnalysesSsaPreGraph.pre_parameter_edge_listed (pre_ssa_points a) b
          (pre_expr_points EV a Ha) Hb') as [Hlisted Hinternal].
        cbn [pre_version_point] in Hdefinition.
        rewrite <- (pre_expr_point_graph EV a Ha) in Hdefinition.
        injection Hdefinition as Hwriter.
        assert (e = parameter_edge (pre_ssa_points a) b) as ->.
        { eapply AnalysesSsaPreGraph.pre_internal_incoming_unique; try eassumption.
          - exact (pre_expr_points EV a Ha).
          - rewrite Hwriting, Hwriter; reflexivity. }
        eapply pre_placement_merged_step; eassumption.
    - destruct (AnalysesSsaPreGraph.pre_listed_edge_out _ e (proj1 Hn) Hedge)
        as [Hnode Hout].
      pose proof (pre_expr_reachable_points EV a Ha _ Hnode) as Hreachable.
      destruct (pre_cache_region_back EN _ _ q e (pre_version_expr version) Hreachable Hout
        Hother Hregion) as [Hprior Hkill].
      assert (pre_cached r t version = pre_eval r s (pre_version_expr version)) as Hsaved.
      { apply (Hcache version q); try assumption; rewrite Hbefore; exact Hprior. }
      eapply (pre_region_cache_step EBE EN EE EV EU a r p Ha Hlaws); try eassumption.
      rewrite pre_placement_cfg; exact Hbefore.
  Qed.

  (** The cache and pending incoming-edge facts advance together on this same paired history. *)
  Lemma pre_placement_paired_cache s0 t0 s t :
    pre_paired_run r p s0 t0 s t ->
    pre_regular_cache EB EE EU a r f facts p s t /\
      pre_pending_phi_cache EB EBE EE EU a r f facts p s0 t0 s t.
  Proof.
    intro Hpaired; induction Hpaired as [Hsource Htarget Hboundary Hcore|
      s t e l s' t' Hpaired [Hcache Hpending] Hstep Htaken Hmacro Hcore'].
    - split; [apply pre_placement_regular_initial; assumption|
        apply pre_placement_pending_initial; exact Hsource].
    - split; [eapply pre_placement_regular_step; eassumption|
        eapply pre_placement_pending_step; eassumption].
  Qed.
End PlacementCache.

(** The actual executable placement maintains reload cache agreement on every paired history. *)
Theorem ssa_pre_cache_invariant {S O B BE N E NT ET V K U C}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (s0 t0 : S) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  pre_exit_covered a r -> pre_phi_source_laws EBE EV a r ->
  pre_local_laws EBE EN EE EV EU a (pre_expression a) (pre_initial_available a) r p ->
  forall s t, pre_paired_run r p s0 t0 s t ->
    pre_cache_agree EN EE EU (pre_expression a) r p (point (pre_source_graph r) s) s t.
Proof.
  intros Ha Hb Hn; cbn zeta; intros Hexit Hphi Hlaws s t Hpaired.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (facts := solve_ssapre EB EBE EN EE EV EU a f).
  pose (p := ssa_pre_place EB EBE EN EE EV EU a).
  destruct (pre_placement_paired_cache EB EBE EN EE EV EU a r Ha Hb Hn Hphi Hlaws
    s0 t0 s t Hpaired) as [Hcache Hpending].
  split.
  - exact (proj2 (proj2 (proj2 (pre_paired_facts EBE EN EE EV EU a (pre_expression a)
      (pre_initial_available a) r p Hlaws s0 t0 s t Hpaired)))).
  - intros e u version Hsource Hdeleted Hget.
    destruct (ssa_pre_reload_regions EB EBE EN EE EV EU a Ha Hb Hn e u version Hdeleted Hget)
      as [q [Hpoint Hregion]].
    pose proof (proj1 (ssa_pre_selected_versions_kept EB EBE EN EE EV EU a Ha Hb Hn)
      e version Hget) as Hkept.
    destruct (ssa_pre_reload_origins EB EBE EN EE EV EU a Ha Hb Hn e version Hget)
      as [d [Hclass [Hexpr Horigin]]].
    pose proof (build_frg_wf EB EBE EN EE EV EU a Ha Hb Hn) as Hfrg.
    pose proof (proj1 (proj2 (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)))
      as Hcomputed_class.
    pose proof (proj1 (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e u Hdeleted))
      as Hcomputed.
    assert (pre_version_expr version = u) as Hvalue by congruence.
    rewrite <- (pre_expr_point_graph EV a Ha) in Hsource.
    rewrite <- Hvalue; apply (Hcache version q); [exact Hkept|exact Hpoint|].
    rewrite Hvalue, <- Hsource; exact Hregion.
Qed.

(** Complete actual target paths and source paths have exactly the same observations and endings. *)
Theorem ssa_pre_semantics {S O B BE N E NT ET V K U C} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (s0 t0 : S) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let v := pre_expression a in
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  pre_exit_covered a r -> pre_phi_source_laws EBE EV a r ->
  pre_local_laws EBE EN EE EV EU a v (pre_initial_available a) r p ->
  initial (pre_source r) s0 -> initial (pre_target r p) t0 ->
  pre_boundary r p (point (pre_source_graph r) s0) t0 ->
  pre_cache_agree EN EE EU v r p (point (pre_source_graph r) s0) s0 t0 ->
  same_behaviour (pre_source r) (pre_source_end r) s0
    (pre_target r p) (pre_target_end r p) t0.
Proof.
  intros Ha Hb Hn; cbn zeta; intros Hexit Hphi Hlaws Hsource Htarget Hboundary Hcache.
  eapply (pre_cache_paths_behaviour EBE EN EE EV EU a (pre_expression a)
    (pre_initial_available a) r (ssa_pre_place EB EBE EN EE EV EU a) Hlaws s0 t0).
  - exact (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn).
  - exact (ssa_pre_cache_invariant EB EBE EN EE EV EU a r s0 t0 Ha Hb Hn Hexit Hphi Hlaws).
  - exact Hsource.
  - exact Htarget.
  - exact Hboundary.
  - exact (proj1 Hcache).
Qed.
