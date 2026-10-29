(** * Expression-specific sparse evaluation graphs

    Indexed splicing contracts eventless paths and retains a point in each closed cycle.
    For example, two eventless edges through a degree-one point become one summarized arc.
    Builds on: AnalysesAvailable, GraphPrepare, FixpointTotal and OrderDual. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone OrderBasic OrderDual OrderPowerset.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointWorklist
  FixpointTotal FixpointSchedule.
From Gaulois.Views Require Import ViewsGraph.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable.
Import List.ListNotations.

(** An expression event either generates or invalidates that expression. *)
Definition seg_event {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (u : U) (e : E) : bool := mentions EU u (gen gk e) || kill gk e u.

(** Generation takes precedence over invalidation on the same edge. *)
Definition seg_bit_transfer {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (b : bool) : bool :=
  mentions EU u (gen gk e) || (b && negb (kill gk e u)).

(** Boolean must-facts start at true and combine by conjunction. *)
Definition seg_must_lattice : lattice bool := dual_lattice bool_lattice bool_top andb.

(** A sparse graph retains paths, interior positions and both cached transfer directions. *)
Record seg_index (N E : Type) : Type := SegIndex {
  seg_graph : Graph.t N E;
  seg_paths : Map.t E (list E);
  seg_interiors : Map.t N (E * nat);
  seg_forward_summary : Map.t E (bool * bool);
  seg_backward_summary : Map.t E (bool * bool)
}.

Arguments SegIndex {N E}.
Arguments seg_graph {N E}.
Arguments seg_paths {N E}.
Arguments seg_interiors {N E}.
Arguments seg_forward_summary {N E}.
Arguments seg_backward_summary {N E}.

(** Missing arcs have no represented original edges. *)
Definition seg_path {N E} (EE : encoding E) (idx : seg_index N E) (a : E) : list E :=
  match Map.get EE a (seg_paths idx) with
  | Some es => es
  | None => []
  end.

(** Interior points are all edge targets except the segment's final endpoint. *)
Definition seg_internal_nodes {N E} (g : Graph.t N E) (es : list E) : list N :=
  map (Graph.target g) (removelast es).

(** The index partitions all original edges and locates precisely the contracted points. *)
Record seg_index_laws {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (is_event : E -> bool) (idx : seg_index N E) : Prop := {
  seg_wf : ready EN (seg_graph idx) (prepare EN (seg_graph idx));
  seg_entries : Graph.entries (seg_graph idx) = Graph.entries g;
  seg_nodes_original : incl (Graph.nodes (seg_graph idx)) (Graph.nodes g);
  seg_boundaries : forall n, In n (Graph.nodes g) ->
    (In n (Graph.entries g) \/ Graph.out g n = []) -> In n (Graph.nodes (seg_graph idx));
  seg_junctions : forall n, In n (Graph.nodes g) ->
    (length (Graph.out g n) <> 1 \/ length (pred_edges (prepare EN g) n) <> 1) ->
    In n (Graph.nodes (seg_graph idx));
  seg_event_endpoints : forall e, In e (edges_of g) -> is_event e = true ->
    In (Graph.source g e) (Graph.nodes (seg_graph idx)) /\
    In (Graph.target g e) (Graph.nodes (seg_graph idx));
  seg_path_valid : forall a, In a (edges_of (seg_graph idx)) ->
    exists es, seg_path EE idx a = a :: es /\
      path g (Graph.source (seg_graph idx) a) (a :: es) (Graph.target (seg_graph idx) a);
  seg_path_nodup : forall a, In a (edges_of (seg_graph idx)) -> NoDup (seg_path EE idx a);
  seg_internal_nodup : forall a, In a (edges_of (seg_graph idx)) ->
    NoDup (seg_internal_nodes g (seg_path EE idx a));
  seg_internal_lookup : forall a k n, In a (edges_of (seg_graph idx)) ->
    nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n ->
    Map.get EN n (seg_interiors idx) = Some (a,k);
  seg_edge_partition : forall e, In e (edges_of g) ->
    exists! a, In a (edges_of (seg_graph idx)) /\ In e (seg_path EE idx a);
  seg_no_event_inside : forall a, In a (edges_of (seg_graph idx)) ->
    (exists e, In e (seg_path EE idx a) /\ is_event e = true) ->
    seg_path EE idx a = [a];
  seg_interior_unique : forall n, In n (Graph.nodes g) ->
    ~ In n (Graph.nodes (seg_graph idx)) ->
    exists a k, Map.get EN n (seg_interiors idx) = Some (a,k) /\
      In a (edges_of (seg_graph idx)) /\
      nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n;
  seg_interior_only : forall n a k, Map.get EN n (seg_interiors idx) = Some (a,k) ->
    In a (edges_of (seg_graph idx)) /\
    nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n /\
    ~ In n (Graph.nodes (seg_graph idx));
  seg_interior_degree : forall n, In n (Graph.nodes g) ->
    ~ In n (Graph.nodes (seg_graph idx)) ->
    length (Graph.out g n) = 1 /\ length (pred_edges (prepare EN g) n) = 1
}.

(** * Boolean summaries *)

(** The dual Boolean operations satisfy the weak lattice laws. *)
Theorem seg_must_laws : lattice_laws seg_must_lattice.
Proof.
  constructor; intros; repeat match goal with
  | b : bool |- _ => destruct b
  end; cbn in *; congruence.
Qed.

(** Conjunction is the least upper bound in the must order. *)
Theorem seg_must_lub : lub_laws seg_must_lattice.
Proof.
  constructor; intros [] [] []; cbn; congruence.
Qed.

(** Each individual expression transfer distributes over intersection. *)
Theorem seg_bit_distributive {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (a b : bool) :
  seg_bit_transfer EU gk u e (a && b) =
    (seg_bit_transfer EU gk u e a && seg_bit_transfer EU gk u e b).
Proof.
  unfold seg_bit_transfer; destruct (mentions EU u (gen gk e)), (kill gk e u), a, b;
    reflexivity.
Qed.

Local Definition seg_apply (s : bool * bool) (b : bool) : bool :=
  if b then snd s else fst s.

Local Definition seg_compose (first second : bool * bool) : bool * bool :=
  (seg_apply second (fst first), seg_apply second (snd first)).

Local Lemma seg_compose_apply first second b :
  seg_apply (seg_compose first second) b = seg_apply second (seg_apply first b).
Proof.
  destruct b; reflexivity.
Qed.

Local Lemma seg_bit_identity {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u e b :
  seg_event EU gk u e = false -> seg_bit_transfer EU gk u e b = b.
Proof.
  unfold seg_event, seg_bit_transfer.
  destruct (mentions EU u (gen gk e)), (kill gk e u), b; cbn; congruence.
Qed.

Local Lemma seg_bit_monotone {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u e :
  monotone_fun seg_must_lattice seg_must_lattice (seg_bit_transfer EU gk u e).
Proof.
  unfold monotone_fun, seg_bit_transfer.
  destruct (mentions EU u (gen gk e)), (kill gk e u); intros [] []; cbn; congruence.
Qed.

Local Definition seg_height : height seg_must_lattice.
Proof.
  refine (@Height bool seg_must_lattice (fun b => if b then 0 else 1) 1 _ _).
  - abstract (intros []; cbn; lia).
  - abstract (intros [] []; cbn; intro Hstrict; try discriminate; lia).
Defined.

(** * Indexed path splicing *)

(* A rope makes each splice constant work; final paths are flattened once. *)
Inductive seg_rope (E : Type) : Type :=
  | SegLeaf (e : E)
  | SegAppend (left right : seg_rope E).

Arguments SegLeaf {E}.
Arguments SegAppend {E}.

Local Fixpoint seg_rope_onto {E} (r : seg_rope E) (tail : list E) : list E :=
  match r with
  | SegLeaf e => e :: tail
  | SegAppend first second => seg_rope_onto first (seg_rope_onto second tail)
  end.

Local Definition seg_rope_edges {E} (r : seg_rope E) : list E := seg_rope_onto r [].

Local Lemma seg_rope_onto_app {E} (r : seg_rope E) tail :
  seg_rope_onto r tail = seg_rope_edges r ++ tail.
Proof.
  revert tail; induction r as [e|first IHfirst second IHsecond]; intro tail;
    cbn [seg_rope_onto].
  - reflexivity.
  - change (seg_rope_onto first (seg_rope_onto second tail) =
      seg_rope_onto first (seg_rope_onto second []) ++ tail).
    rewrite !IHfirst, IHsecond; apply app_assoc.
Qed.

Local Lemma seg_rope_append {E} (left right : seg_rope E) :
  seg_rope_edges (SegAppend left right) = seg_rope_edges left ++ seg_rope_edges right.
Proof.
  unfold seg_rope_edges at 1; cbn [seg_rope_onto]; apply seg_rope_onto_app.
Qed.

(** A live arc stores its endpoint, path rope and two constant-size truth tables. *)
Record seg_arc (N E : Type) : Type := SegArc {
  seg_tip : N;
  seg_rope_value : seg_rope E;
  seg_fw : bool * bool;
  seg_bw : bool * bool
}.

Arguments SegArc {N E}.
Arguments seg_tip {N E}.
Arguments seg_rope_value {N E}.
Arguments seg_fw {N E}.
Arguments seg_bw {N E}.

(** Construction tracks surviving points, current incoming arcs and live arc payloads. *)
Record seg_work (N E : Type) : Type := SegWork {
  seg_alive : FinSet.t N;
  seg_incoming : Map.t N E;
  seg_arcs : Map.t E (seg_arc N E)
}.

Arguments SegWork {N E}.
Arguments seg_alive {N E}.
Arguments seg_incoming {N E}.
Arguments seg_arcs {N E}.

Local Definition seg_join_arc {N E} (left right : seg_arc N E) : seg_arc N E :=
  SegArc (seg_tip right) (SegAppend (seg_rope_value left) (seg_rope_value right))
    (seg_compose (seg_fw left) (seg_fw right))
    (seg_compose (seg_bw right) (seg_bw left)).

Local Definition seg_event_points {N E} (EN : encoding N) (g : Graph.t N E)
    (event : E -> bool) (es : list E) : FinSet.t N :=
  fold_right (fun e points => if event e then
    FinSet.add EN (Graph.source g e) (FinSet.add EN (Graph.target g e) points)
    else points) FinSet.empty es.

(* Only originally degree-one, nonboundary, nonevent points are candidates. *)
Local Definition seg_candidates {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) (points entries : FinSet.t N) : Map.t N E :=
  fold_right (fun n candidates =>
    if FinSet.mem EN n points || FinSet.mem EN n entries then candidates else
    match succ_edges p n, pred_edges p n with
    | [e], [_] => Map.set EN n e candidates
    | _, _ => candidates
    end) Map.empty (Graph.nodes g).

Local Definition seg_initial {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (transfer : E -> bool -> bool) (es : list E) : seg_work N E :=
  SegWork (FinSet.of_list EN (Graph.nodes g))
    (fold_right (fun e incoming => Map.set EN (Graph.target g e) e incoming) Map.empty es)
    (fold_right (fun e arcs => Map.set EE e
      (SegArc (Graph.target g e) (SegLeaf e) (transfer e false, transfer e true)
        (transfer e false, transfer e true)) arcs) Map.empty es).

Local Definition seg_merge {N E} (EN : encoding N) (EE : encoding E)
    (n : N) (a b : E) (first second : seg_arc N E) (work : seg_work N E) : seg_work N E :=
  SegWork (FinSet.remove EN n (seg_alive work))
    (Map.set EN (seg_tip second) a (seg_incoming work))
    (Map.set EE a (seg_join_arc first second) (Map.remove EE b (seg_arcs work))).

Local Definition seg_splice {N E} (EN : encoding N) (EE : encoding E)
    (candidates : Map.t N E) (n : N) (work : seg_work N E) : seg_work N E :=
  if FinSet.mem EN n (seg_alive work) then
    match Map.get EN n candidates, Map.get EN n (seg_incoming work) with
    | Some b, Some a =>
      if Pos.eqb (encode EE a) (encode EE b) then work else
      match Map.get EE a (seg_arcs work), Map.get EE b (seg_arcs work) with
      | Some first, Some second =>
        seg_merge EN EE n a b first second work
      | _, _ => work
      end
    | _, _ => work
    end
  else work.

Local Fixpoint seg_position_bindings {N E} (a : E) (ns : list N) (k : nat) :
    list (N * (E * nat)) :=
  match ns with
  | n :: rest => (n,(a,k)) :: seg_position_bindings a rest (S k)
  | [] => []
  end.

Local Definition seg_finish {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) (work : seg_work N E) : seg_index N E :=
  let paths := Map.map (fun arc => seg_rope_edges (seg_rope_value arc)) (seg_arcs work) in
  SegIndex
    (Graph.Make (Graph.entries g)
      (filter (fun n => FinSet.mem EN n (seg_alive work)) (Graph.nodes g))
      (fun n => if FinSet.mem EN n (seg_alive work) then succ_edges p n else [])
      (Graph.source g)
      (fun a => match Map.get EE a (seg_arcs work) with
                | Some arc => seg_tip arc
                | None => Graph.target g a
                end))
    paths
    (Map.of_list EN (flat_map (fun arc => seg_position_bindings (fst arc)
      (seg_internal_nodes g (snd arc)) 0) (Map.elements paths)))
    (Map.map seg_fw (seg_arcs work)) (Map.map seg_bw (seg_arcs work)).

(** Splicing every eligible point contracts maximal paths and leaves one point per closed cycle. *)
Definition build_expression_seg {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : seg_index N E :=
  let g := cfg (gkview gk) in
  let p := prepare EN g in
  let es := edges_of g in
  let points := seg_event_points EN g (seg_event EU gk u) es in
  let candidates := seg_candidates EN g p points (FinSet.of_list EN (Graph.entries g)) in
  let work := fold_left (fun work n => seg_splice EN EE candidates n work) (Graph.nodes g)
    (seg_initial EN EE g (seg_bit_transfer EU gk u) es) in
  seg_finish EN EE g p work.

(** A cached truth table applies a segment without visiting its path. *)
Definition seg_summary_apply {E} (EE : encoding E) (a : E) (b : bool)
    (summaries : Map.t E (bool * bool)) : bool :=
  match Map.get EE a summaries with
  | Some (f, t) => if b then t else f
  | None => b
  end.

(** Forward iterations read only the cached forward summary. *)
Definition seg_forward_transfer {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E)
    (a : E) (b : bool) : bool :=
  seg_summary_apply EE a b (seg_forward_summary idx).

(** Backward iterations read only the cached backward summary. *)
Definition seg_backward_transfer {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E)
    (a : E) (b : bool) : bool :=
  seg_summary_apply EE a b (seg_backward_summary idx).

(** Availability starts empty at every original entry. *)
Definition seg_available_system {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) :
    System.t N (dense_constraint N E) bool :=
  forward_system (seg_graph idx) (fun _ => false) (seg_forward_transfer EE EU gk u idx).

(** Busy expressions start empty at sinks and unconstrained at every other cut point. *)
Definition seg_busy_system {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) :
    System.t N (dense_constraint N E) bool :=
  backward_system (seg_graph idx)
    (fun n => match Graph.out (seg_graph idx) n with [] => false | _ => true end)
    (seg_backward_transfer EE EU gk u idx).

(** Reconstruction walks the stored prefix only when an interior point is requested. *)
Definition seg_reconstruct_available {N E} (EN : encoding N) (EE : encoding E)
    (idx : seg_index N E) (transfer : E -> bool -> bool) (cut : N -> bool) : N -> bool :=
  let cuts := FinSet.of_list EN (Graph.nodes (seg_graph idx)) in
  fun n => if FinSet.mem EN n cuts then cut n else
    match Map.get EN n (seg_interiors idx) with
    | Some (a,k) => fold_left (fun b e => transfer e b)
      (firstn (S k) (seg_path EE idx a)) (cut (Graph.source (seg_graph idx) a))
    | None => false
    end.

(** Backward reconstruction walks the suffix following the requested interior point. *)
Definition seg_reconstruct_busy {N E} (EN : encoding N) (EE : encoding E)
    (idx : seg_index N E) (transfer : E -> bool -> bool) (cut : N -> bool) : N -> bool :=
  let cuts := FinSet.of_list EN (Graph.nodes (seg_graph idx)) in
  fun n => if FinSet.mem EN n cuts then cut n else
    match Map.get EN n (seg_interiors idx) with
    | Some (a,k) => fold_right transfer (cut (Graph.target (seg_graph idx) a))
      (skipn (S k) (seg_path EE idx a))
    | None => false
    end.

Local Definition seg_available_cut {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) : N -> bool :=
    let sys := seg_available_system EE EU gk u idx in
    let ss := forward_static _ _ _ in
    proj1_sig (solve_total EN (dense_constraint_encoding EN EE)
      seg_must_lattice seg_must_laws (rpo_scheduler EN sys ss) Joining sys ss
      (inhabits seg_height)).

Local Definition seg_busy_cut {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) : N -> bool :=
    let sys := seg_busy_system EE EU gk u idx in
    let ss := backward_static _ _ _ in
    proj1_sig (solve_total EN (dense_constraint_encoding EN EE)
      seg_must_lattice seg_must_laws (rpo_scheduler EN sys ss) Joining sys ss
      (inhabits seg_height)).

(** Solve the forward Boolean must system and reconstruct the requested original point. *)
Definition seg_available {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : N -> bool :=
  if FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk)) then
    let idx := build_expression_seg EN EE EU gk u in
    seg_reconstruct_available EN EE idx (seg_bit_transfer EU gk u)
      (seg_available_cut EN EE EU gk u idx)
  else fun _ => false.

(** Solve the backward Boolean must system, retaining true in unconstrained closed cycles. *)
Definition seg_busy {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : N -> bool :=
  if FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk)) then
    let idx := build_expression_seg EN EE EU gk u in
    seg_reconstruct_busy EN EE idx (seg_bit_transfer EU gk u) (seg_busy_cut EN EE EU gk u idx)
  else fun _ => false.

(** * Cached composition invariants *)

Local Definition seg_arc_summary {N E} (transfer : E -> bool -> bool)
    (arc : seg_arc N E) : Prop := forall b,
  seg_apply (seg_fw arc) b = fold_left (fun b e => transfer e b)
    (seg_rope_edges (seg_rope_value arc)) b /\
  seg_apply (seg_bw arc) b = fold_right transfer b (seg_rope_edges (seg_rope_value arc)).

Local Lemma seg_leaf_summary {N E} (transfer : E -> bool -> bool) e (tip : N) :
  seg_arc_summary transfer
    (SegArc tip (SegLeaf e) (transfer e false, transfer e true)
      (transfer e false, transfer e true)).
Proof.
  intros []; split; reflexivity.
Qed.

Local Lemma seg_join_summary {N E} (transfer : E -> bool -> bool)
    (first second : seg_arc N E) :
  seg_arc_summary transfer first -> seg_arc_summary transfer second ->
  seg_arc_summary transfer (seg_join_arc first second).
Proof.
  intros Hfirst Hsecond b; unfold seg_join_arc; cbn [seg_rope_value seg_fw seg_bw].
  rewrite seg_rope_append, fold_left_app, fold_right_app, !seg_compose_apply; split.
  - rewrite (proj1 (Hfirst b)); apply (proj1 (Hsecond _)).
  - rewrite (proj2 (Hsecond b)); apply (proj2 (Hfirst _)).
Qed.

Local Definition seg_summary_invariant {N E} (EE : encoding E)
    (transfer : E -> bool -> bool) (work : seg_work N E) : Prop :=
  forall a arc, Map.get EE a (seg_arcs work) = Some arc -> seg_arc_summary transfer arc.

Local Lemma seg_initial_summaries {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) transfer es :
  seg_summary_invariant EE transfer (seg_initial EN EE g transfer es).
Proof.
  unfold seg_summary_invariant, seg_initial; cbn [seg_arcs].
  induction es as [|e es IH]; intros a arc Hget; cbn in Hget.
  - rewrite Map.get_empty in Hget; discriminate.
  - destruct (Pos.eq_dec (encode EE a) (encode EE e)) as [Heq|Hne].
    + apply (encode_injective EE) in Heq; subst a.
      rewrite Map.get_set_same in Hget; inversion Hget; apply seg_leaf_summary.
    + rewrite Map.get_set_other in Hget.
      * exact (IH a arc Hget).
      * intro Heq; subst a; contradiction.
Qed.

Local Lemma seg_splice_summaries {N E} (EN : encoding N) (EE : encoding E)
    candidates n (work : seg_work N E) transfer :
  seg_summary_invariant EE transfer work ->
  seg_summary_invariant EE transfer (seg_splice EN EE candidates n work).
Proof.
  intro Hsummary; unfold seg_splice.
  destruct (FinSet.mem EN n (seg_alive work)); [|exact Hsummary].
  destruct (Map.get EN n candidates) as [b|], (Map.get EN n (seg_incoming work)) as [a|];
    try exact Hsummary.
  destruct (Pos.eqb (encode EE a) (encode EE b)); [exact Hsummary|].
  destruct (Map.get EE a (seg_arcs work)) as [first|] eqn:Hfirst;
    destruct (Map.get EE b (seg_arcs work)) as [second|] eqn:Hsecond; try exact Hsummary.
  intros c arc Hget; cbn [seg_merge seg_arcs] in Hget.
  destruct (Pos.eq_dec (encode EE c) (encode EE a)) as [Heq|Hne].
  - apply (encode_injective EE) in Heq; subst c.
    rewrite Map.get_set_same in Hget; inversion Hget; subst arc.
    apply seg_join_summary; [exact (Hsummary _ _ Hfirst)|exact (Hsummary _ _ Hsecond)].
  - rewrite Map.get_set_other in Hget by (intro Heq; subst c; contradiction).
    destruct (Pos.eq_dec (encode EE c) (encode EE b)) as [Heq|Hother].
    + apply (encode_injective EE) in Heq; subst c.
      rewrite Map.get_remove_same in Hget; discriminate.
    + rewrite Map.get_remove_other in Hget by (intro Heq; subst c; contradiction).
      exact (Hsummary _ _ Hget).
Qed.

Local Lemma seg_fold_summaries {N E} (EN : encoding N) (EE : encoding E)
    candidates ns (work : seg_work N E) transfer :
  seg_summary_invariant EE transfer work ->
  seg_summary_invariant EE transfer
    (fold_left (fun work n => seg_splice EN EE candidates n work) ns work).
Proof.
  revert work; induction ns as [|n ns IH]; intros work Hsummary; cbn; [exact Hsummary|].
  apply IH, seg_splice_summaries; exact Hsummary.
Qed.

Local Lemma seg_finish_summary {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) (work : seg_work N E) transfer :
  seg_summary_invariant EE transfer work -> forall a b,
  seg_summary_apply EE a b (seg_forward_summary (seg_finish EN EE g p work)) =
    fold_left (fun b e => transfer e b) (seg_path EE (seg_finish EN EE g p work) a) b /\
  seg_summary_apply EE a b (seg_backward_summary (seg_finish EN EE g p work)) =
    fold_right transfer b (seg_path EE (seg_finish EN EE g p work) a).
Proof.
  intros Hsummary a b; unfold seg_summary_apply, seg_path, seg_finish.
  cbn [seg_forward_summary seg_backward_summary seg_paths]; rewrite !Map.get_map.
  destruct (Map.get EE a (seg_arcs work)) as [arc|] eqn:Harc; cbn.
  - specialize (Hsummary _ _ Harc b); unfold seg_apply in Hsummary.
    destruct (seg_fw arc), (seg_bw arc); exact Hsummary.
  - split; reflexivity.
Qed.

(** Both cached directions equal the corresponding fold of every represented segment. *)
Theorem build_expression_seg_summaries {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  forall a b, In a (edges_of (seg_graph (build_expression_seg EN EE EU gk u))) ->
    seg_forward_transfer EE EU gk u (build_expression_seg EN EE EU gk u) a b =
      fold_left (fun acc e => seg_bit_transfer EU gk u e acc)
        (seg_path EE (build_expression_seg EN EE EU gk u) a) b /\
    seg_backward_transfer EE EU gk u (build_expression_seg EN EE EU gk u) a b =
      fold_right (fun e acc => seg_bit_transfer EU gk u e acc) b
        (seg_path EE (build_expression_seg EN EE EU gk u) a).
Proof.
  intros _ a b _; unfold seg_forward_transfer, seg_backward_transfer, build_expression_seg.
  apply seg_finish_summary, seg_fold_summaries, seg_initial_summaries.
Qed.

(** * Structural splice invariants *)

Local Definition seg_eq_dec {K} (EK : encoding K) (x y : K) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode EK x) (encode EK y)) as [Heq|Hne].
  - left; apply (encode_injective EK); exact Heq.
  - right; intro Heq; subst y; contradiction.
Defined.

Local Lemma seg_mentions_spec {K} (EK : encoding K) x xs :
  mentions EK x xs = true <-> In x xs.
Proof.
  unfold mentions; rewrite existsb_exists; split.
  - intros [y [Hy Heq]]; apply Pos.eqb_eq, (encode_injective EK) in Heq; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply Pos.eqb_refl].
Qed.

Local Lemma seg_event_points_spec {N E} (EN : encoding N) (g : Graph.t N E) event es n :
  FinSet.mem EN n (seg_event_points EN g event es) = true <->
  exists e, In e es /\ event e = true /\ (n = Graph.source g e \/ n = Graph.target g e).
Proof.
  unfold seg_event_points; induction es as [|e es IH]; cbn [fold_right].
  - rewrite FinSet.mem_empty; split; [discriminate|intros [d [Hd _]]; contradiction].
  - destruct (event e) eqn:Hevent.
    + rewrite !FinSet.mem_add, IH; split.
      * intros [Hsource|[Htarget|[d [Hd [He Hpoint]]]]].
        -- exists e; split; [now left|]; split; [exact Hevent|now left].
        -- exists e; split; [now left|]; split; [exact Hevent|now right].
        -- exists d; split; [now right|auto].
      * intros [d [[<-|Hd] [He [Hsource|Htarget]]]].
        -- now left.
        -- right; now left.
        -- right; right; exists d; auto.
        -- right; right; exists d; auto.
    + rewrite IH; split.
      * intros [d [Hd Hrest]]; exists d; split; [now right|exact Hrest].
      * intros [d [[<-|Hd] [He Hpoint]]].
        -- congruence.
        -- exists d; auto.
Qed.

Local Lemma seg_candidates_sound {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) points entries n b :
  Map.get EN n (seg_candidates EN g p points entries) = Some b ->
  In n (Graph.nodes g) /\ succ_edges p n = [b] /\
  (exists d, pred_edges p n = [d]) /\
  FinSet.mem EN n points = false /\ FinSet.mem EN n entries = false.
Proof.
  unfold seg_candidates; generalize (Graph.nodes g) as ns; intro ns.
  induction ns as [|v ns IH]; cbn; intro Hget.
  - rewrite Map.get_empty in Hget; discriminate.
  - destruct (FinSet.mem EN v points || FinSet.mem EN v entries) eqn:Hpin.
    + destruct (IH Hget) as [Hin Hrest]; split; [now right|exact Hrest].
    + destruct (succ_edges p v) as [|e [|e' es]] eqn:Hout;
        destruct (pred_edges p v) as [|d [|d' ds]] eqn:Hpred;
        try (destruct (IH Hget) as [Hin Hrest]; split; [now right|exact Hrest]).
      destruct (seg_eq_dec EN n v) as [->|Hne].
      * rewrite Map.get_set_same in Hget; inversion Hget; subst b.
        apply orb_false_iff in Hpin; destruct Hpin as [Hp He].
        split; [now left|]; split; [exact Hout|]; split; [now exists d|auto].
      * rewrite Map.get_set_other in Hget by exact Hne.
        destruct (IH Hget) as [Hin Hrest]; split; [now right|exact Hrest].
Qed.

Local Lemma seg_table_get {K V} (EK : encoding K) (value : K -> V) ks k :
  Map.get EK k (fold_right (fun key table => Map.set EK key (value key) table)
    Map.empty ks) = if mentions EK k ks then Some (value k) else None.
Proof.
  induction ks as [|key ks IH]; cbn [fold_right mentions existsb].
  - apply Map.get_empty.
  - destruct (Pos.eqb (encode EK k) (encode EK key)) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EK) in Heq; subst key.
      rewrite Map.get_set_same; reflexivity.
    + rewrite Map.get_set_other; [exact IH|].
      intro H; subst key; rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Local Lemma seg_path_targets {N E} (g : Graph.t N E) v es w :
  path g v es w -> es <> [] ->
  map (Graph.target g) es = seg_internal_nodes g es ++ [w].
Proof.
  intro Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intro Hnonempty.
  - contradiction.
  - destruct es as [|d es].
    + inversion Hpath; reflexivity.
    + cbn [seg_internal_nodes removelast map].
      change (Graph.target g e :: map (Graph.target g) (d :: es) =
        Graph.target g e :: (seg_internal_nodes g (d :: es) ++ [w])).
      f_equal; apply IH; discriminate.
Qed.

Local Lemma seg_internal_app {N E} (g : Graph.t N E) v es w fs :
  path g v es w -> es <> [] -> fs <> [] ->
  seg_internal_nodes g (es ++ fs) =
    seg_internal_nodes g es ++ w :: seg_internal_nodes g fs.
Proof.
  intros Hpath Hes Hfs; unfold seg_internal_nodes at 1.
  rewrite removelast_app by exact Hfs.
  rewrite map_app, (seg_path_targets g v es w Hpath Hes), <- app_assoc; reflexivity.
Qed.

Local Lemma seg_path_edge_nodes {N E} (g : Graph.t N E) v es w :
  graph_wf g -> In v (Graph.nodes g) -> path g v es w ->
  In w (Graph.nodes g) /\ incl es (edges_of g).
Proof.
  intros Hwf Hv Hpath; induction Hpath as [v|e es w Hedge Hpath IH].
  - split; [exact Hv|intros d Hd; contradiction].
  - assert (Ht : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
    destruct (IH Ht) as [Hw Hedges]; split; [exact Hw|].
    intros d [<-|Hd]; [exact (edges_of_in g (Graph.source g e) e Hv Hedge)|exact (Hedges d Hd)].
Qed.

Local Definition seg_live {N E} (EN : encoding N) (work : seg_work N E) (n : N) : Prop :=
  FinSet.mem EN n (seg_alive work) = true.

Local Definition seg_trace {N E} (arc : seg_arc N E) : list E :=
  seg_rope_edges (seg_rope_value arc).

Local Lemma seg_join_trace {N E} (first second : seg_arc N E) :
  seg_trace (seg_join_arc first second) = seg_trace first ++ seg_trace second.
Proof.
  apply seg_rope_append.
Qed.

(* Every active arc starts with its original identity. The domain law keeps outgoing
   lists unchanged at surviving points, and the incoming law supplies direct splice lookup. *)
Record seg_work_laws {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (candidates : Map.t N E) (work : seg_work N E) : Prop := {
  seg_work_wf : Map.wf EE (seg_arcs work);
  seg_work_support : forall n, seg_live EN work n -> In n (Graph.nodes g);
  seg_work_pinned : forall n, In n (Graph.nodes g) -> Map.get EN n candidates = None ->
    seg_live EN work n;
  seg_work_domain : forall a,
    (exists arc, Map.get EE a (seg_arcs work) = Some arc) <->
    In a (edges_of g) /\ seg_live EN work (Graph.source g a);
  seg_work_path : forall a arc, Map.get EE a (seg_arcs work) = Some arc ->
    (exists es, seg_trace arc = a :: es) /\
    path g (Graph.source g a) (seg_trace arc) (seg_tip arc) /\
    seg_live EN work (seg_tip arc) /\ NoDup (seg_trace arc) /\
    (forall n, In n (seg_internal_nodes g (seg_trace arc)) -> ~ seg_live EN work n);
  seg_work_partition : forall e, In e (edges_of g) ->
    exists! a, exists arc, Map.get EE a (seg_arcs work) = Some arc /\ In e (seg_trace arc);
  seg_work_coverage : forall n, In n (Graph.nodes g) -> ~ seg_live EN work n ->
    exists a arc, Map.get EE a (seg_arcs work) = Some arc /\
      In n (seg_internal_nodes g (seg_trace arc));
  seg_work_incoming : forall n b, seg_live EN work n -> Map.get EN n candidates = Some b ->
    exists a arc, Map.get EN n (seg_incoming work) = Some a /\
      Map.get EE a (seg_arcs work) = Some arc /\ seg_tip arc = n /\
      forall c other, Map.get EE c (seg_arcs work) = Some other -> seg_tip other = n -> c = a
}.

Arguments seg_work_wf {N E EN EE g candidates work} _.
Arguments seg_work_support {N E EN EE g candidates work} _ n _.
Arguments seg_work_pinned {N E EN EE g candidates work} _ n _ _.
Arguments seg_work_domain {N E EN EE g candidates work} _ a.
Arguments seg_work_path {N E EN EE g candidates work} _ a arc _.
Arguments seg_work_partition {N E EN EE g candidates work} _ e _.
Arguments seg_work_coverage {N E EN EE g candidates work} _ n _ _.
Arguments seg_work_incoming {N E EN EE g candidates work} _ n b _ _.

Local Lemma seg_initial_incoming {N E} (EN : encoding N) (g : Graph.t N E) es n d :
  In d es -> Graph.target g d = n ->
  (forall e, In e es -> Graph.target g e = n -> e = d) ->
  Map.get EN n (fold_right (fun e incoming => Map.set EN (Graph.target g e) e incoming)
    Map.empty es) = Some d.
Proof.
  induction es as [|e es IH]; intros Hd Htarget Hunique; [contradiction|].
  cbn [fold_right]; destruct (seg_eq_dec EN n (Graph.target g e)) as [Heq|Hne].
  - rewrite <- Heq, Map.get_set_same; f_equal; apply Hunique; [now left|now symmetry].
  - rewrite Map.get_set_other by exact Hne; apply IH; [|exact Htarget|].
    + destruct Hd as [<-|Hd]; [congruence|exact Hd].
    + intros a Ha; apply Hunique; now right.
Qed.

Local Lemma seg_edge_source_in {N E} (g : Graph.t N E) e :
  graph_wf g -> In e (edges_of g) -> In (Graph.source g e) (Graph.nodes g).
Proof.
  intros Hwf He; apply in_flat_map in He; destruct He as [n [Hn He]].
  now rewrite (out_source Hwf n e He).
Qed.

Local Lemma seg_initial_laws {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) points entries transfer :
  ready EN g p ->
  seg_work_laws EN EE g (seg_candidates EN g p points entries)
    (seg_initial EN EE g transfer (edges_of g)).
Proof.
  intros Hready; destruct Hready as [Hwf [Hedges Hprepared]].
  assert (Hget : forall a,
    Map.get EE a (seg_arcs (seg_initial EN EE g transfer (edges_of g))) =
    if mentions EE a (edges_of g) then
      Some (SegArc (Graph.target g a) (SegLeaf a) (transfer a false, transfer a true)
        (transfer a false, transfer a true)) else None).
  { intro a; exact (seg_table_get EE (fun e => SegArc (Graph.target g e) (SegLeaf e)
      (transfer e false, transfer e true) (transfer e false, transfer e true)) (edges_of g) a). }
  assert (Hlive : forall n, seg_live EN (seg_initial EN EE g transfer (edges_of g)) n <->
    In n (Graph.nodes g)).
  { intro n; apply FinSet.of_list_spec. }
  constructor.
  - clear Hget Hlive; unfold seg_initial; cbn [seg_arcs].
    induction (edges_of g) as [|e es IH]; cbn.
    + apply Map.wf_empty.
    + apply Map.wf_set; exact IH.
  - intros n Hn; now apply Hlive.
  - intros n Hn _; now apply Hlive.
  - intro a; rewrite Hget; destruct (mentions EE a (edges_of g)) eqn:Ha.
    + apply seg_mentions_spec in Ha; split.
      * intros _; split; [exact Ha|apply Hlive; eapply seg_edge_source_in; eassumption].
      * intros _; eexists; reflexivity.
    + split.
      * intros [arc Harc]; discriminate.
      * intros [Hin _]; pose proof (proj2 (seg_mentions_spec EE a _) Hin) as Htrue; congruence.
  - intros a arc Harc; rewrite Hget in Harc.
    destruct (mentions EE a (edges_of g)) eqn:Ha; [|discriminate].
    apply seg_mentions_spec in Ha; inversion Harc; subst arc.
    split; [exists []; reflexivity|]; split.
    + constructor; [apply edges_of_source; assumption|constructor].
    + split.
      * apply Hlive; eapply out_target_in;
          [exact Hwf|eapply seg_edge_source_in; eassumption|apply edges_of_source; assumption].
      * split; [constructor; [intro H; contradiction|constructor]|].
        intros n Hn; contradiction.
  - intros e He; exists e; split.
    + exists (SegArc (Graph.target g e) (SegLeaf e) (transfer e false, transfer e true)
        (transfer e false, transfer e true)); split.
      * rewrite Hget, (proj2 (seg_mentions_spec EE e _) He); reflexivity.
      * now left.
    + intros a [arc [Harc Hin]]; rewrite Hget in Harc.
      destruct (mentions EE a (edges_of g)); [|discriminate].
      inversion Harc; subst arc; destruct Hin as [Heq|Hnone]; [now symmetry|contradiction].
  - intros n Hn Hdead; exfalso; apply Hdead, Hlive; exact Hn.
  - intros n b Hn Hcandidate.
    destruct (seg_candidates_sound EN g p points entries n b Hcandidate)
      as [Hnode [Hout [[d Hpred] Hrest]]].
    assert (Hd : In d (edges_of g) /\ Graph.target g d = n).
    { assert (Hmember : In d (pred_edges p n)) by (rewrite Hpred; now left).
      apply (pred_agrees Hprepared n d Hnode) in Hmember.
      destruct Hmember as [v [Hv [Hedge Htarget]]]; split; [eapply edges_of_in; eassumption|].
      exact Htarget. }
    assert (Hunique : forall e, In e (edges_of g) -> Graph.target g e = n -> e = d).
    { intros e He Htarget; assert (Hin : In e (pred_edges p n)).
      { apply (pred_agrees Hprepared n e Hnode); apply in_flat_map in He.
        destruct He as [v [Hv He]]; exists v; auto. }
      rewrite Hpred in Hin; destruct Hin as [Heq|Hnone]; [now symmetry|contradiction]. }
    exists d, (SegArc (Graph.target g d) (SegLeaf d) (transfer d false, transfer d true)
      (transfer d false, transfer d true)); split.
    + apply seg_initial_incoming; [exact (proj1 Hd)|exact (proj2 Hd)|exact Hunique].
    + split.
      * rewrite Hget; rewrite (proj2 (seg_mentions_spec EE d _) (proj1 Hd)); reflexivity.
      * split; [exact (proj2 Hd)|].
        intros c other Hother Htarget; rewrite Hget in Hother.
        destruct (mentions EE c (edges_of g)) eqn:Hc; [|discriminate].
        inversion Hother; subst other; apply Hunique;
          [exact (proj1 (seg_mentions_spec EE c _) Hc)|exact Htarget].
Qed.

Local Lemma seg_work_trace_in {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work a arc :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  Map.get EE a (seg_arcs work) = Some arc -> incl (seg_trace arc) (edges_of g).
Proof.
  intros Hwf Hwork Harc.
  destruct (proj1 (seg_work_domain Hwork a) (ex_intro _ arc Harc)) as [_ Hsource].
  exact (proj2 (seg_path_edge_nodes g _ _ _ Hwf
    (seg_work_support Hwork _ Hsource) (proj1 (proj2 (seg_work_path Hwork a arc Harc))))).
Qed.

Local Lemma seg_work_disjoint {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work a first b second :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  Map.get EE a (seg_arcs work) = Some first ->
  Map.get EE b (seg_arcs work) = Some second -> a <> b ->
  forall e, In e (seg_trace first) -> ~ In e (seg_trace second).
Proof.
  intros Hwf Hwork Hfirst Hsecond Hne e Hleft Hright.
  destruct (seg_work_partition Hwork e
    (seg_work_trace_in EN EE g candidates work a first Hwf Hwork Hfirst e Hleft))
    as [owner [Howner Hunique]].
  apply Hne; transitivity owner.
  - symmetry; apply Hunique; exists first; auto.
  - apply Hunique; exists second; auto.
Qed.

Local Lemma seg_merge_live {N E} (EN : encoding N) (EE : encoding E)
    n a b (first second : seg_arc N E) work v :
  seg_live EN (seg_merge EN EE n a b first second work) v <->
  v <> n /\ seg_live EN work v.
Proof.
  apply FinSet.mem_remove.
Qed.

Local Lemma seg_merge_lookup {N E} (EN : encoding N) (EE : encoding E)
    n a b (first second : seg_arc N E) work c :
  Map.get EE c (seg_arcs (seg_merge EN EE n a b first second work)) =
    if seg_eq_dec EE c a then Some (seg_join_arc first second) else
    if seg_eq_dec EE c b then None else Map.get EE c (seg_arcs work).
Proof.
  cbn [seg_merge seg_arcs]; destruct (seg_eq_dec EE c a) as [->|Hca].
  - apply Map.get_set_same.
  - rewrite Map.get_set_other by exact Hca; destruct (seg_eq_dec EE c b) as [->|Hcb].
    + apply Map.get_remove_same.
    + apply Map.get_remove_other; exact Hcb.
Qed.

Local Lemma seg_merge_incoming {N E} (EN : encoding N) (EE : encoding E)
    n a b (first second : seg_arc N E) work v :
  Map.get EN v (seg_incoming (seg_merge EN EE n a b first second work)) =
    if seg_eq_dec EN v (seg_tip second) then Some a else Map.get EN v (seg_incoming work).
Proof.
  cbn [seg_merge seg_incoming]; destruct (seg_eq_dec EN v (seg_tip second)) as [->|Hne].
  - apply Map.get_set_same.
  - apply Map.get_set_other; exact Hne.
Qed.

Local Lemma seg_merge_path {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work n a b first second :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  Graph.out g n = [b] -> seg_live EN work n ->
  Map.get EE a (seg_arcs work) = Some first -> seg_tip first = n ->
  Map.get EE b (seg_arcs work) = Some second -> a <> b ->
  (forall c other, Map.get EE c (seg_arcs work) = Some other ->
    seg_tip other = n -> c = a) ->
  Graph.source g b = n /\ Graph.source g a <> n /\ seg_tip second <> n /\
  (exists es, seg_trace (seg_join_arc first second) = a :: es) /\
  path g (Graph.source g a) (seg_trace (seg_join_arc first second)) (seg_tip second) /\
  NoDup (seg_trace (seg_join_arc first second)) /\
  seg_internal_nodes g (seg_trace (seg_join_arc first second)) =
    seg_internal_nodes g (seg_trace first) ++ n :: seg_internal_nodes g (seg_trace second).
Proof.
  intros Hwf Hwork Hout Hlive Hfirst Htip Hsecond Hne Hincoming.
  assert (Hb : Graph.source g b = n) by (apply (out_source Hwf n b); rewrite Hout; now left).
  assert (Ha : Graph.source g a <> n).
  { intro Hsource; assert (Hin : In a (Graph.out g n)).
    { rewrite <- Hsource; apply edges_of_source; [exact Hwf|].
      exact (proj1 (proj1 (seg_work_domain Hwork a) (ex_intro _ first Hfirst))). }
    rewrite Hout in Hin; destruct Hin as [Heq|Hnone]; [apply Hne; now symmetry|contradiction]. }
  assert (Ht : seg_tip second <> n) by (intro H; apply Hne; symmetry; eapply Hincoming; eauto).
  destruct (seg_work_path Hwork a first Hfirst)
    as [[es Htrace] [Hpath [Hend [Hnodup Hinside]]]].
  destruct (seg_work_path Hwork b second Hsecond)
    as [[fs Htrace'] [Hpath' [Hend' [Hnodup' Hinside']]]].
  assert (Hjoined : seg_trace (seg_join_arc first second) = seg_trace first ++ seg_trace second)
    by (apply seg_rope_append).
  split; [exact Hb|]; split; [exact Ha|]; split; [exact Ht|]; split.
  - exists (es ++ seg_trace second); rewrite Hjoined, Htrace; reflexivity.
  - split.
    + rewrite Hjoined; eapply graph_path_app; [exact Hpath|now rewrite Htip, <- Hb].
    + split.
      * rewrite Hjoined; apply nodup_app_disjoint; [exact Hnodup|exact Hnodup'|].
        exact (seg_work_disjoint EN EE g candidates work a first b second
          Hwf Hwork Hfirst Hsecond Hne).
      * rewrite Hjoined; apply (seg_internal_app g (Graph.source g a)
          (seg_trace first) n (seg_trace second));
          [now rewrite <- Htip|congruence|congruence].
Qed.

Section SegMergeLaws.
Context {N E : Type} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
  (candidates : Map.t N E) (work : seg_work N E) (n : N) (a b : E)
  (first second : seg_arc N E).
Hypotheses (Hwf : graph_wf g) (Hwork : seg_work_laws EN EE g candidates work)
  (Hcandidate : Map.get EN n candidates = Some b) (Hout : Graph.out g n = [b])
  (Hlive : seg_live EN work n) (Hfirst : Map.get EE a (seg_arcs work) = Some first)
  (Htip : seg_tip first = n) (Hsecond : Map.get EE b (seg_arcs work) = Some second)
  (Hne : a <> b)
  (Hincoming : forall c other, Map.get EE c (seg_arcs work) = Some other ->
    seg_tip other = n -> c = a).
Let next := seg_merge EN EE n a b first second work.

Local Lemma seg_merge_shape :
  Graph.source g b = n /\ Graph.source g a <> n /\ seg_tip second <> n /\
  (exists es, seg_trace (seg_join_arc first second) = a :: es) /\
  path g (Graph.source g a) (seg_trace (seg_join_arc first second)) (seg_tip second) /\
  NoDup (seg_trace (seg_join_arc first second)) /\
  seg_internal_nodes g (seg_trace (seg_join_arc first second)) =
    seg_internal_nodes g (seg_trace first) ++ n :: seg_internal_nodes g (seg_trace second).
Proof.
  apply (seg_merge_path EN EE g candidates work n a b first second); assumption.
Qed.

Local Lemma seg_merge_new : Map.get EE a (seg_arcs next) = Some (seg_join_arc first second).
Proof.
  unfold next; rewrite seg_merge_lookup; destruct (seg_eq_dec EE a a); congruence.
Qed.

Local Lemma seg_merge_old c arc :
  c <> a -> c <> b -> Map.get EE c (seg_arcs work) = Some arc ->
  Map.get EE c (seg_arcs next) = Some arc.
Proof.
  intros Hca Hcb Hget; unfold next; rewrite seg_merge_lookup.
  destruct (seg_eq_dec EE c a), (seg_eq_dec EE c b); congruence.
Qed.

Local Lemma seg_merge_cases c arc : Map.get EE c (seg_arcs next) = Some arc ->
  (c = a /\ arc = seg_join_arc first second) \/
  (c <> a /\ c <> b /\ Map.get EE c (seg_arcs work) = Some arc).
Proof.
  unfold next; rewrite seg_merge_lookup.
  destruct (seg_eq_dec EE c a) as [Heq|Hca]; intro Hget.
  - inversion Hget; auto.
  - destruct (seg_eq_dec EE c b); [discriminate|auto].
Qed.

Local Lemma seg_merge_only_out c : In c (edges_of g) -> Graph.source g c = n -> c = b.
Proof.
  intros Hc Hsource; pose proof (edges_of_source g c Hwf Hc) as Hedge.
  rewrite Hsource, Hout in Hedge; destruct Hedge as [Heq|Hnone]; [now symmetry|contradiction].
Qed.

Local Lemma seg_merge_domain : forall c,
  (exists arc, Map.get EE c (seg_arcs next) = Some arc) <->
  In c (edges_of g) /\ seg_live EN next (Graph.source g c).
Proof.
  destruct seg_merge_shape as [Hb [Ha Hrest]]; intro c; split.
  - intros [arc Harc]; apply seg_merge_cases in Harc.
    destruct Harc as [[-> ->]|[Hca [Hcb Hget]]].
    + destruct (proj1 (seg_work_domain Hwork a) (ex_intro _ first Hfirst)) as [Hedge Hsource].
      split; [exact Hedge|apply seg_merge_live; auto].
    + destruct (proj1 (seg_work_domain Hwork c) (ex_intro _ arc Hget)) as [Hedge Hsource].
      split; [exact Hedge|apply seg_merge_live; split; [|exact Hsource]].
      intro Heq; apply Hcb, seg_merge_only_out; assumption.
  - intros [Hedge Hsource]; apply seg_merge_live in Hsource; destruct Hsource as [Hcn Hsource].
    destruct (seg_eq_dec EE c a) as [->|Hca].
    + exists (seg_join_arc first second); exact seg_merge_new.
    + destruct (proj2 (seg_work_domain Hwork c) (conj Hedge Hsource)) as [arc Harc].
      exists arc; apply seg_merge_old; [exact Hca| |exact Harc].
      intro Heq; subst c; contradiction.
Qed.

Local Lemma seg_merge_paths : forall c arc, Map.get EE c (seg_arcs next) = Some arc ->
  (exists es, seg_trace arc = c :: es) /\
  path g (Graph.source g c) (seg_trace arc) (seg_tip arc) /\
  seg_live EN next (seg_tip arc) /\ NoDup (seg_trace arc) /\
  (forall v, In v (seg_internal_nodes g (seg_trace arc)) -> ~ seg_live EN next v).
Proof.
  destruct seg_merge_shape as [Hb [Ha [Ht [Hhead [Hpath [Hnodup Hinside]]]]]].
  intros c arc Harc; apply seg_merge_cases in Harc.
  destruct Harc as [[-> ->]|[Hca [Hcb Hget]]].
  - split; [exact Hhead|]; split; [exact Hpath|]; split.
    + apply seg_merge_live; split; [exact Ht|].
      exact (proj1 (proj2 (proj2 (seg_work_path Hwork b second Hsecond)))).
    + split; [exact Hnodup|].
      intros v Hin Hnow; apply seg_merge_live in Hnow; destruct Hnow as [Hvn Hold].
      rewrite Hinside, in_app_iff in Hin; destruct Hin as [Hin|[Heq|Hin]].
      * exact ((proj2 (proj2 (proj2 (proj2 (seg_work_path Hwork a first Hfirst))))) v Hin Hold).
      * apply Hvn; now symmetry.
      * exact ((proj2 (proj2 (proj2 (proj2 (seg_work_path Hwork b second Hsecond))))) v Hin Hold).
  - destruct (seg_work_path Hwork c arc Hget)
      as [Hhead' [Hpath' [Htip' [Hnodup' Hinside']]]].
    split; [exact Hhead'|]; split; [exact Hpath'|]; split.
    + apply seg_merge_live; split; [|exact Htip'].
      intro Heq; apply Hca; eapply Hincoming; eassumption.
    + split; [exact Hnodup'|].
      intros v Hin Hnow; apply (Hinside' v Hin); exact (proj2 (proj1
        (seg_merge_live EN EE n a b first second work v) Hnow)).
Qed.

Local Lemma seg_merge_partition : forall e, In e (edges_of g) ->
  exists! c, exists arc, Map.get EE c (seg_arcs next) = Some arc /\ In e (seg_trace arc).
Proof.
  intros e He; destruct (seg_work_partition Hwork e He) as [c [[arc [Harc Hin]] Hunique]].
  destruct (seg_eq_dec EE c b) as [->|Hcb].
  - exists a; split.
    + exists (seg_join_arc first second); split; [exact seg_merge_new|].
      rewrite seg_join_trace; apply in_or_app; right.
      rewrite Hsecond in Harc; inversion Harc; exact Hin.
    + intros d [other [Hother Hmember]]; apply seg_merge_cases in Hother.
      destruct Hother as [[-> _]|[Hda [Hdb Hold]]]; [reflexivity|].
      exfalso; apply Hdb; symmetry; apply Hunique; exists other; auto.
  - exists c; split.
    + destruct (seg_eq_dec EE c a) as [->|Hca].
      * exists (seg_join_arc first second); split; [exact seg_merge_new|].
        rewrite seg_join_trace; apply in_or_app; left.
        rewrite Hfirst in Harc; inversion Harc; exact Hin.
      * exists arc; split; [apply seg_merge_old; assumption|exact Hin].
    + intros d [other [Hother Hmember]]; apply seg_merge_cases in Hother.
      destruct Hother as [[-> ->]|[Hda [Hdb Hold]]].
      * rewrite seg_join_trace, in_app_iff in Hmember; destruct Hmember as [Hmember|Hmember].
        -- apply Hunique; exists first; auto.
        -- exfalso; apply Hcb, Hunique; exists second; auto.
      * apply Hunique; exists other; auto.
Qed.

Local Lemma seg_merge_coverage : forall v, In v (Graph.nodes g) -> ~ seg_live EN next v ->
  exists c arc, Map.get EE c (seg_arcs next) = Some arc /\
    In v (seg_internal_nodes g (seg_trace arc)).
Proof.
  destruct seg_merge_shape as [Hb [Ha [Ht [Hhead [Hpath [Hnodup Hinside]]]]]].
  intros v Hv Hdead; destruct (seg_eq_dec EN v n) as [->|Hvn].
  - exists a, (seg_join_arc first second); split; [exact seg_merge_new|].
    rewrite Hinside; apply in_or_app; right; now left.
  - assert (Hold : ~ seg_live EN work v).
    { intro H; apply Hdead, seg_merge_live; auto. }
    destruct (seg_work_coverage Hwork v Hv Hold) as [c [arc [Harc Hin]]].
    destruct (seg_eq_dec EE c a) as [->|Hca].
    + rewrite Hfirst in Harc; inversion Harc; subst arc.
      exists a, (seg_join_arc first second); split; [exact seg_merge_new|].
      rewrite Hinside; apply in_or_app; now left.
    + destruct (seg_eq_dec EE c b) as [->|Hcb].
      * rewrite Hsecond in Harc; inversion Harc; subst arc.
        exists a, (seg_join_arc first second); split; [exact seg_merge_new|].
        rewrite Hinside; apply in_or_app; right; now right.
      * exists c, arc; split; [apply seg_merge_old; assumption|exact Hin].
Qed.

Local Lemma seg_merge_incoming_law : forall v e,
  seg_live EN next v -> Map.get EN v candidates = Some e ->
  exists c arc, Map.get EN v (seg_incoming next) = Some c /\
    Map.get EE c (seg_arcs next) = Some arc /\ seg_tip arc = v /\
    forall d other, Map.get EE d (seg_arcs next) = Some other -> seg_tip other = v -> d = c.
Proof.
  intros v e Hnow Hchoice; apply seg_merge_live in Hnow; destruct Hnow as [Hvn Hold].
  destruct (seg_work_incoming Hwork v e Hold Hchoice)
    as [owner [arc [Hindex [Harc [Hend Hunique]]]]].
  destruct (seg_eq_dec EN v (seg_tip second)) as [Heq|Hvt].
  - exists a, (seg_join_arc first second); split.
    + unfold next; rewrite seg_merge_incoming;
        destruct (seg_eq_dec EN v (seg_tip second)); congruence.
    + split; [exact seg_merge_new|]; split; [now symmetry|].
      intros d other Hother Htip'; apply seg_merge_cases in Hother.
      destruct Hother as [[-> _]|[Hda [Hdb Hget]]]; [reflexivity|].
      assert (Hbowner : b = owner) by (eapply Hunique; [exact Hsecond|now symmetry]).
      assert (Hdowner : d = owner) by (eapply Hunique; eassumption).
      exfalso; apply Hdb; congruence.
  - assert (Hca : owner <> a).
    { intro Heq; subst owner; rewrite Hfirst in Harc; inversion Harc; subst arc; congruence. }
    assert (Hcb : owner <> b).
    { intro Heq; subst owner; rewrite Hsecond in Harc; inversion Harc; subst arc; congruence. }
    exists owner, arc; split.
    + unfold next; rewrite seg_merge_incoming;
        destruct (seg_eq_dec EN v (seg_tip second)); congruence.
    + split; [apply seg_merge_old; assumption|]; split; [exact Hend|].
      intros d other Hother Htip'; apply seg_merge_cases in Hother.
      destruct Hother as [[-> ->]|[Hda [Hdb Hget]]]; [exfalso; apply Hvt; now symmetry|].
      eapply Hunique; eassumption.
Qed.

Local Lemma seg_merge_laws : seg_work_laws EN EE g candidates next.
Proof.
  constructor.
  - cbn [next seg_merge seg_arcs]; apply Map.wf_set, Map.wf_remove, (seg_work_wf Hwork).
  - intros v Hv; apply seg_merge_live in Hv; apply (seg_work_support Hwork v); exact (proj2 Hv).
  - intros v Hv Hpin; apply seg_merge_live; split.
    + intro Heq; subst v; congruence.
    + exact (seg_work_pinned Hwork v Hv Hpin).
  - exact seg_merge_domain.
  - exact seg_merge_paths.
  - exact seg_merge_partition.
  - exact seg_merge_coverage.
  - exact seg_merge_incoming_law.
Qed.

End SegMergeLaws.

Local Lemma seg_splice_laws {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates n work :
  graph_wf g ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  seg_work_laws EN EE g candidates work ->
  seg_work_laws EN EE g candidates (seg_splice EN EE candidates n work).
Proof.
  intros Hwf Hout Hwork; unfold seg_splice.
  destruct (FinSet.mem EN n (seg_alive work)) eqn:Hlive; [|exact Hwork].
  destruct (Map.get EN n candidates) as [b|] eqn:Hcandidate;
    destruct (Map.get EN n (seg_incoming work)) as [a|] eqn:Hindex; try exact Hwork.
  destruct (Pos.eqb (encode EE a) (encode EE b)) eqn:Heq; [exact Hwork|].
  destruct (Map.get EE a (seg_arcs work)) as [first|] eqn:Hfirst;
    destruct (Map.get EE b (seg_arcs work)) as [second|] eqn:Hsecond; try exact Hwork.
  destruct (seg_work_incoming Hwork n b Hlive Hcandidate)
    as [owner [arc [Hin [Harc [Htip Hunique]]]]].
  rewrite Hindex in Hin; inversion Hin; subst owner.
  rewrite Hfirst in Harc; inversion Harc; subst arc.
  apply (seg_merge_laws EN EE g candidates work n a b first second);
    try assumption; [apply Hout; exact Hcandidate|].
  intro H; subst b; rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Local Lemma seg_fold_laws {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates ns work :
  graph_wf g ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  seg_work_laws EN EE g candidates work ->
  seg_work_laws EN EE g candidates
    (fold_left (fun work n => seg_splice EN EE candidates n work) ns work).
Proof.
  intros Hwf Hout; revert work; induction ns as [|n ns IH]; intros work Hwork; cbn.
  - exact Hwork.
  - apply IH, seg_splice_laws; assumption.
Qed.

Local Lemma seg_built_work_laws {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) points entries transfer :
  ready EN g (prepare EN g) ->
  let candidates := seg_candidates EN g (prepare EN g) points entries in
  seg_work_laws EN EE g candidates
    (fold_left (fun work n => seg_splice EN EE candidates n work) (Graph.nodes g)
      (seg_initial EN EE g transfer (edges_of g))).
Proof.
  intros Hready; cbn zeta; apply seg_fold_laws.
  - exact (proj1 Hready).
  - intros n b Hget; destruct (seg_candidates_sound EN g (prepare EN g) points entries n b Hget)
      as [Hn [Hout Hrest]].
    rewrite (succ_agrees (proj2 (proj2 Hready)) n Hn) in Hout; exact Hout.
  - apply seg_initial_laws; exact Hready.
Qed.

(** * Exact interior indexing *)

Local Lemma seg_internal_sources {N E} (g : Graph.t N E) v es w :
  path g v es w -> seg_internal_nodes g es =
    match es with [] => [] | _ :: rest => map (Graph.source g) rest end.
Proof.
  intro Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; [reflexivity|].
  destruct es as [|d es]; [reflexivity|].
  inversion Hpath; subst; cbn [seg_internal_nodes removelast map] in *.
  f_equal; [congruence|exact IH].
Qed.

Local Lemma seg_nodup_map_on {A B} (f : A -> B) xs :
  NoDup xs -> (forall x y, In x xs -> In y xs -> f x = f y -> x = y) -> NoDup (map f xs).
Proof.
  intro Hnodup; induction Hnodup as [|x xs Hnot Hnodup IH]; intro Hinjective; cbn.
  - constructor.
  - constructor.
    + intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]].
      assert (Hyx : y = x) by (apply Hinjective; [now right|now left|exact Heq]).
      subst y; exact (Hnot Hy).
    + apply IH; intros u v Hu Hv Heq; apply Hinjective; [now right|now right|exact Heq].
Qed.

Local Lemma seg_nodup_nth {A} (xs : list A) k l x :
  NoDup xs -> nth_error xs k = Some x -> nth_error xs l = Some x -> k = l.
Proof.
  intro Hnodup; revert k l; induction Hnodup as [|y ys Hnot Hnodup IH]; intros [|k] [|l]; cbn;
    intros Hk Hl; try discriminate; [reflexivity| | |].
  - inversion Hk; subst y; exfalso; apply Hnot; eapply nth_error_In; exact Hl.
  - inversion Hl; subst y; exfalso; apply Hnot; eapply nth_error_In; exact Hk.
  - f_equal; eapply IH; eassumption.
Qed.

Local Lemma seg_work_nonlive_out {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work n :
  seg_work_laws EN EE g candidates work ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  In n (Graph.nodes g) -> ~ seg_live EN work n -> exists b, Graph.out g n = [b].
Proof.
  intros Hwork Hshape Hnode Hdead; destruct (Map.get EN n candidates) as [b|] eqn:Hcandidate.
  - exists b; apply Hshape; exact Hcandidate.
  - exfalso; apply Hdead; exact (seg_work_pinned Hwork n Hnode Hcandidate).
Qed.

Local Lemma seg_work_internal_nodup {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work a arc :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  Map.get EE a (seg_arcs work) = Some arc -> NoDup (seg_internal_nodes g (seg_trace arc)).
Proof.
  intros Hwf Hwork Hshape Harc.
  destruct (seg_work_path Hwork a arc Harc)
    as [[es Hhead] [Hpath [Htip [Hnodup Hinside]]]].
  rewrite (seg_internal_sources g _ _ _ Hpath), Hhead; cbn.
  rewrite Hhead in Hnodup; inversion Hnodup as [|e rest Hnot Htail]; subst.
  apply seg_nodup_map_on; [exact Htail|].
  intros x y Hx Hy Heq.
  assert (Horigx : In x (edges_of g)).
  { apply (seg_work_trace_in EN EE g candidates work a arc Hwf Hwork Harc).
    rewrite Hhead; now right. }
  assert (Horigy : In y (edges_of g)).
  { apply (seg_work_trace_in EN EE g candidates work a arc Hwf Hwork Harc).
    rewrite Hhead; now right. }
  assert (Hdead : ~ seg_live EN work (Graph.source g x)).
  { apply Hinside; rewrite (seg_internal_sources g _ _ _ Hpath), Hhead; cbn.
    apply in_map; exact Hx. }
  destruct (seg_work_nonlive_out EN EE g candidates work (Graph.source g x) Hwork Hshape
    (seg_edge_source_in g x Hwf Horigx) Hdead) as [b Hout].
  pose proof (edges_of_source g x Hwf Horigx) as Hinx.
  pose proof (edges_of_source g y Hwf Horigy) as Hiny.
  rewrite Hout in Hinx; rewrite <- Heq, Hout in Hiny.
  destruct Hinx as [<-|Hnone]; [|contradiction].
  destruct Hiny as [Hequal|Hnone]; [exact Hequal|contradiction].
Qed.

Local Lemma seg_work_interior_next {N E} (g : Graph.t N E) a es tip k n :
  path g (Graph.source g a) (a :: es) tip ->
  nth_error (seg_internal_nodes g (a :: es)) k = Some n ->
  exists e, nth_error es k = Some e /\ Graph.source g e = n.
Proof.
  intros Hpath Hnth; rewrite (seg_internal_sources g _ _ _ Hpath), nth_error_map in Hnth.
  destruct (nth_error es k) as [e|] eqn:He; cbn in Hnth; [|discriminate].
  inversion Hnth; exists e; auto.
Qed.

Local Lemma seg_work_interior_unique {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) candidates work a arc b other k l n :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  Map.get EE a (seg_arcs work) = Some arc -> Map.get EE b (seg_arcs work) = Some other ->
  nth_error (seg_internal_nodes g (seg_trace arc)) k = Some n ->
  nth_error (seg_internal_nodes g (seg_trace other)) l = Some n -> a = b /\ k = l.
Proof.
  intros Hwf Hwork Hshape Harc Hother Hk Hl.
  destruct (seg_work_path Hwork a arc Harc) as [[es Hhead] [Hpath [Htip [Hnd Hinside]]]].
  destruct (seg_work_path Hwork b other Hother) as [[fs Hhead'] [Hpath' Hrest]].
  rewrite Hhead in Hpath, Hk; rewrite Hhead' in Hpath', Hl.
  destruct (seg_work_interior_next g a es (seg_tip arc) k n Hpath Hk) as [e [He Hsource]].
  destruct (seg_work_interior_next g b fs (seg_tip other) l n Hpath' Hl) as [d [Hd Hsource']].
  assert (Hein : In e (seg_trace arc)) by (rewrite Hhead; right; eapply nth_error_In; exact He).
  assert (Hdin : In d (seg_trace other)) by (rewrite Hhead'; right; eapply nth_error_In; exact Hd).
  assert (Heorig : In e (edges_of g)) by
    (apply (seg_work_trace_in EN EE g candidates work a arc Hwf Hwork Harc); exact Hein).
  assert (Hdorig : In d (edges_of g)) by
    (apply (seg_work_trace_in EN EE g candidates work b other Hwf Hwork Hother); exact Hdin).
  assert (Hnode : In n (Graph.nodes g)) by (rewrite <- Hsource; eapply seg_edge_source_in; eauto).
  assert (Hdead : ~ seg_live EN work n).
  { apply Hinside; rewrite Hhead; eapply nth_error_In; exact Hk. }
  destruct (seg_work_nonlive_out EN EE g candidates work n Hwork Hshape Hnode Hdead)
    as [out Hedge].
  pose proof (edges_of_source g e Hwf Heorig) as Houte.
  pose proof (edges_of_source g d Hwf Hdorig) as Houtd.
  rewrite Hsource, Hedge in Houte; rewrite Hsource', Hedge in Houtd.
  assert (Hed : e = d) by (destruct Houte as [<-|Hnone], Houtd as [<-|Hnone'];
    try contradiction; reflexivity).
  assert (Hab : a = b).
  { destruct (seg_eq_dec EE a b) as [Hequal|Hne]; [exact Hequal|].
    exfalso; apply (seg_work_disjoint EN EE g candidates work a arc b other
      Hwf Hwork Harc Hother Hne e Hein); now rewrite Hed. }
  split; [exact Hab|]; subst b; rewrite Harc in Hother; inversion Hother; subst other.
  eapply seg_nodup_nth.
  - apply (seg_work_internal_nodup EN EE g candidates work a arc); assumption.
  - rewrite Hhead; exact Hk.
  - rewrite Hhead'; exact Hl.
Qed.

Local Lemma seg_position_bindings_offset {N E} (a b : E) (ns : list N) start n k :
  In (n,(b,k)) (seg_position_bindings a ns start) <->
  a = b /\ exists i, nth_error ns i = Some n /\ k = start + i.
Proof.
  revert start; induction ns as [|v ns IH]; intro start; cbn [seg_position_bindings In].
  - split; [contradiction|intros [_ [[|i] [Hnth _]]]; discriminate].
  - rewrite IH; split.
    + intros [Heq|[Hab [i [Hnth Hk]]]].
      * inversion Heq; subst; split; [reflexivity|exists 0; cbn; auto].
      * split; [exact Hab|exists (S i); cbn; split; [exact Hnth|lia]].
    + intros [Hab [[|i] [Hnth Hk]]].
      * cbn in Hnth; inversion Hnth; subst v; left; subst b.
        replace k with start by lia; reflexivity.
      * right; split; [exact Hab|exists i; split; [exact Hnth|lia]].
Qed.

Local Lemma seg_position_bindings_spec {N E} (a b : E) (ns : list N) n k :
  In (n,(b,k)) (seg_position_bindings a ns 0) <-> a = b /\ nth_error ns k = Some n.
Proof.
  rewrite seg_position_bindings_offset; split.
  - intros [Hab [i [Hnth Hk]]]; cbn in Hk; subst k; auto.
  - intros [Hab Hnth]; split; [exact Hab|exists k; auto].
Qed.

Local Lemma seg_bindings_only {K V} (EK : encoding K) (bindings : list (K * V)) k v :
  Map.get EK k (Map.of_list EK bindings) = Some v -> In (k,v) bindings.
Proof.
  rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode EK (fst kv)) (encode EK k)) (rev bindings))
    as [[other value]|] eqn:Hfind; cbn; intro Heq; [|discriminate].
  inversion Heq; subst value; apply find_some in Hfind; destruct Hfind as [Hin Hcode].
  cbn in Hcode; apply Pos.eqb_eq, (encode_injective EK) in Hcode; subst other.
  apply in_rev; exact Hin.
Qed.

Local Lemma seg_find_present {A} (test : A -> bool) xs x :
  In x xs -> test x = true -> find test xs <> None.
Proof.
  induction xs as [|y xs IH]; cbn; intros Hin Htest; [contradiction|].
  destruct (test y) eqn:Hy; [discriminate|].
  destruct Hin as [<-|Hin]; [congruence|exact (IH Hin Htest)].
Qed.

Local Lemma seg_bindings_get {K V} (EK : encoding K) (bindings : list (K * V)) k v :
  (forall k v w, In (k,v) bindings -> In (k,w) bindings -> v = w) ->
  In (k,v) bindings -> Map.get EK k (Map.of_list EK bindings) = Some v.
Proof.
  intros Hcoherent Hin; rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode EK (fst kv)) (encode EK k)) (rev bindings))
    as [[other value]|] eqn:Hfind; cbn.
  - apply find_some in Hfind; destruct Hfind as [Hmember Hcode].
    cbn in Hcode; apply Pos.eqb_eq, (encode_injective EK) in Hcode; subst other.
    f_equal; apply (Hcoherent k value v); [apply in_rev; exact Hmember|exact Hin].
  - exfalso; apply (seg_find_present
      (fun kv => Pos.eqb (encode EK (fst kv)) (encode EK k))
      (rev bindings) (k,v) (proj1 (in_rev _ _) Hin) (Pos.eqb_refl _)); exact Hfind.
Qed.

Local Definition seg_all_positions {N E} (g : Graph.t N E) (paths : Map.t E (list E)) :
    list (N * (E * nat)) :=
  flat_map (fun arc => seg_position_bindings (fst arc)
    (seg_internal_nodes g (snd arc)) 0) (Map.elements paths).

Local Lemma seg_all_positions_spec {N E} (EE : encoding E) (g : Graph.t N E)
    paths n a k : Map.wf EE paths ->
  (In (n,(a,k)) (seg_all_positions g paths) <->
  exists es, Map.get EE a paths = Some es /\ nth_error (seg_internal_nodes g es) k = Some n).
Proof.
  intro Hwf; unfold seg_all_positions; rewrite in_flat_map; split.
  - intros [[b es] [Hbinding Hposition]]; cbn in Hposition.
    apply seg_position_bindings_spec in Hposition; destruct Hposition as [-> Hnth].
    exists es; split; [apply (Map.elements_sound EE); assumption|exact Hnth].
  - intros [es [Hget Hnth]]; exists (a,es); split.
    + apply (Map.elements_complete EE); assumption.
    + apply seg_position_bindings_spec; auto.
Qed.

Local Lemma seg_finish_positions_raw {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) work n a k :
  Map.wf EE (seg_arcs work) ->
  (In (n,(a,k)) (seg_all_positions g (seg_paths (seg_finish EN EE g p work))) <->
  exists arc, Map.get EE a (seg_arcs work) = Some arc /\
    nth_error (seg_internal_nodes g (seg_trace arc)) k = Some n).
Proof.
  intro Hwf; rewrite (seg_all_positions_spec EE g).
  - cbn [seg_finish seg_paths]; rewrite Map.get_map; split.
    + intros [es [Hget Hnth]]; destruct (Map.get EE a (seg_arcs work)) as [arc|];
        cbn in Hget; [|discriminate].
      inversion Hget; subst es; exists arc; auto.
    + intros [arc [Hget Hnth]]; rewrite Hget; cbn; eexists; split; [reflexivity|exact Hnth].
  - apply Map.wf_map; exact Hwf.
Qed.

Local Lemma seg_finish_positions {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) candidates work :
  graph_wf g -> seg_work_laws EN EE g candidates work ->
  (forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]) ->
  forall n a k,
  Map.get EN n (seg_interiors (seg_finish EN EE g p work)) = Some (a,k) <->
  exists arc, Map.get EE a (seg_arcs work) = Some arc /\
    nth_error (seg_internal_nodes g (seg_trace arc)) k = Some n.
Proof.
  intros Hwf Hwork Hshape n a k.
  change (Map.get EN n (Map.of_list EN
    (seg_all_positions g (seg_paths (seg_finish EN EE g p work)))) = Some (a,k) <->
    exists arc, Map.get EE a (seg_arcs work) = Some arc /\
      nth_error (seg_internal_nodes g (seg_trace arc)) k = Some n).
  split.
  - intro Hget; apply seg_bindings_only in Hget.
    apply (proj1 (seg_finish_positions_raw EN EE g p work n a k (seg_work_wf Hwork))); exact Hget.
  - intro Hposition; apply seg_bindings_get.
    + intros v [b l] [c m] Hb Hc.
      apply (seg_finish_positions_raw EN EE g p work _ _ _ (seg_work_wf Hwork)) in Hb, Hc.
      destruct Hb as [first [Hfirst Hnth]], Hc as [second [Hsecond Hnth']].
      destruct (seg_work_interior_unique EN EE g candidates work b first c second l m v
        Hwf Hwork Hshape Hfirst Hsecond Hnth Hnth') as [-> ->]; reflexivity.
    + apply (proj2 (seg_finish_positions_raw EN EE g p work n a k (seg_work_wf Hwork))).
      exact Hposition.
Qed.

Local Lemma seg_finish_nodes {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) candidates work n :
  seg_work_laws EN EE g candidates work ->
  (In n (Graph.nodes (seg_graph (seg_finish EN EE g p work))) <-> seg_live EN work n).
Proof.
  intro Hwork; cbn [seg_finish seg_graph Graph.nodes]; rewrite filter_In; split.
  - intros [_ Hlive]; exact Hlive.
  - intro Hlive; split; [exact (seg_work_support Hwork n Hlive)|exact Hlive].
Qed.

Local Lemma seg_finish_out_agrees {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) candidates work n :
  ready EN g p -> seg_work_laws EN EE g candidates work ->
  In n (Graph.nodes (seg_graph (seg_finish EN EE g p work))) ->
  Graph.out (seg_graph (seg_finish EN EE g p work)) n = Graph.out g n.
Proof.
  intros Hready Hwork Hn; apply (seg_finish_nodes EN EE g p candidates work n Hwork) in Hn.
  cbn [seg_finish seg_graph Graph.out]; unfold seg_live in Hn; rewrite Hn.
  apply (succ_agrees (proj2 (proj2 Hready)) n (seg_work_support Hwork n Hn)).
Qed.

Local Lemma seg_finish_edges {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) candidates work a :
  ready EN g p -> seg_work_laws EN EE g candidates work ->
  (In a (edges_of (seg_graph (seg_finish EN EE g p work))) <->
    exists arc, Map.get EE a (seg_arcs work) = Some arc).
Proof.
  intros [Hwf [Hnodup Hprepared]] Hwork; split.
  - intro Hin; apply in_flat_map in Hin; destruct Hin as [n [Hnode Hedge]].
    apply (seg_finish_nodes EN EE g p candidates work n Hwork) in Hnode.
    cbn [seg_finish seg_graph Graph.out] in Hedge; unfold seg_live in Hnode; rewrite Hnode in Hedge.
    rewrite (succ_agrees Hprepared n (seg_work_support Hwork n Hnode)) in Hedge.
    apply (proj2 (seg_work_domain Hwork a)); split.
    + apply (edges_of_in g n a (seg_work_support Hwork n Hnode) Hedge).
    + rewrite (out_source Hwf n a Hedge); exact Hnode.
  - intros [arc Harc]; destruct (proj1 (seg_work_domain Hwork a) (ex_intro _ arc Harc))
      as [Hedge Hsource].
    apply in_flat_map; exists (Graph.source g a); split.
    + apply (seg_finish_nodes EN EE g p candidates work _ Hwork); exact Hsource.
    + cbn [seg_finish seg_graph Graph.out]; unfold seg_live in Hsource; rewrite Hsource.
      rewrite (succ_agrees Hprepared _ (seg_work_support Hwork _ Hsource)).
      apply edges_of_source; assumption.
Qed.

Local Lemma seg_finish_path {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) work a arc :
  Map.get EE a (seg_arcs work) = Some arc ->
  seg_path EE (seg_finish EN EE g p work) a = seg_trace arc /\
  Graph.target (seg_graph (seg_finish EN EE g p work)) a = seg_tip arc.
Proof.
  intro Harc; unfold seg_path; cbn [seg_finish seg_paths seg_graph Graph.target].
  rewrite Map.get_map, Harc; split; reflexivity.
Qed.

Local Lemma seg_finish_ready {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (p : prepared EN g) candidates work :
  ready EN g p -> seg_work_laws EN EE g candidates work ->
  (forall n, In n (Graph.entries g) -> Map.get EN n candidates = None) ->
  ready EN (seg_graph (seg_finish EN EE g p work))
    (prepare EN (seg_graph (seg_finish EN EE g p work))).
Proof.
  intros Hready Hwork Hentries; destruct Hready as [Hwf [Hnodup Hprepared]]; apply prepare_ready.
  - constructor.
    + cbn [seg_finish seg_graph Graph.nodes]; apply NoDup_filter, (nodes_nodup Hwf).
    + intros n Hn; apply (seg_finish_nodes EN EE g p candidates work n Hwork).
      apply (seg_work_pinned Hwork n); [apply (entries_in Hwf n Hn)|apply Hentries; exact Hn].
    + intros n a Ha; cbn [seg_finish seg_graph Graph.out Graph.source] in *.
      destruct (FinSet.mem EN n (seg_alive work)) eqn:Hlive; [|contradiction].
      rewrite (succ_agrees Hprepared n (seg_work_support Hwork n Hlive)) in Ha.
      exact (out_source Hwf n a Ha).
    + intros n a Hn Ha.
      assert (Hedge : In a (edges_of (seg_graph (seg_finish EN EE g p work))))
        by (eapply edges_of_in; [exact Hn|exact Ha]).
      apply (seg_finish_edges EN EE g p candidates work a
        (conj Hwf (conj Hnodup Hprepared)) Hwork) in Hedge.
      destruct Hedge as [arc Harc]; rewrite (proj2 (seg_finish_path EN EE g p work a arc Harc)).
      apply (seg_finish_nodes EN EE g p candidates work _ Hwork).
      exact (proj1 (proj2 (proj2 (seg_work_path Hwork a arc Harc)))).
  - intro n; cbn [seg_finish seg_graph Graph.out].
    destruct (FinSet.mem EN n (seg_alive work)) eqn:Hlive; [|constructor].
    rewrite (succ_agrees Hprepared n (seg_work_support Hwork n Hlive)); apply Hnodup.
Qed.

Local Lemma seg_candidates_pinned {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) event n :
  ready EN g p -> In n (Graph.nodes g) ->
  (In n (Graph.entries g) \/ length (Graph.out g n) <> 1 \/ length (pred_edges p n) <> 1 \/
    FinSet.mem EN n (seg_event_points EN g event (edges_of g)) = true) ->
  Map.get EN n (seg_candidates EN g p (seg_event_points EN g event (edges_of g))
    (FinSet.of_list EN (Graph.entries g))) = None.
Proof.
  intros Hready Hnode Hpin; destruct (Map.get EN n (seg_candidates EN g p
    (seg_event_points EN g event (edges_of g)) (FinSet.of_list EN (Graph.entries g))))
    as [b|] eqn:Hget; [|reflexivity].
  destruct (seg_candidates_sound EN g p _ _ n b Hget)
    as [_ [Hout [[d Hpred] [Hevent Hentry]]]].
  rewrite (succ_agrees (proj2 (proj2 Hready)) n Hnode) in Hout.
  destruct Hpin as [Hin|[Hout'|[Hpred'|Hevent']]].
  - pose proof (proj2 (FinSet.of_list_spec EN n _) Hin); congruence.
  - rewrite Hout in Hout'; contradiction.
  - rewrite Hpred in Hpred'; contradiction.
  - congruence.
Qed.

Local Lemma seg_path_event_singleton {N E} (g : Graph.t N E) event a es tip
    (alive : N -> Prop) :
  path g (Graph.source g a) (a :: es) tip ->
  (forall n, In n (seg_internal_nodes g (a :: es)) -> ~ alive n) ->
  (forall e, In e (a :: es) -> event e = true ->
    alive (Graph.source g e) /\ alive (Graph.target g e)) ->
  (exists e, In e (a :: es) /\ event e = true) -> a :: es = [a].
Proof.
  intros Hpath Hinside Hevent [e [Hin He]]; destruct es as [|d es]; [reflexivity|].
  exfalso; destruct Hin as [<-|Hin].
  - apply (Hinside (Graph.target g a)); [now left|exact (proj2 (Hevent a (or_introl eq_refl) He))].
  - apply (Hinside (Graph.source g e)).
    + rewrite (seg_internal_sources g _ _ _ Hpath); apply in_map; exact Hin.
    + exact (proj1 (Hevent e (or_intror Hin) He)).
Qed.

Local Lemma seg_finish_correct {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) event work :
  ready EN g (prepare EN g) ->
  let candidates := seg_candidates EN g (prepare EN g)
    (seg_event_points EN g event (edges_of g)) (FinSet.of_list EN (Graph.entries g)) in
  seg_work_laws EN EE g candidates work ->
  seg_index_laws EN EE g event (seg_finish EN EE g (prepare EN g) work).
Proof.
  intros Hready candidates Hwork; pose proof (proj1 Hready) as Hwf.
  set (p := prepare EN g); fold p in Hready.
  assert (Hshape : forall n b, Map.get EN n candidates = Some b -> Graph.out g n = [b]).
  { intros n b Hget; destruct (seg_candidates_sound EN g p _ _ n b Hget)
      as [Hn [Hout Hrest]].
    rewrite (succ_agrees (proj2 (proj2 Hready)) n Hn) in Hout; exact Hout. }
  assert (Hpin : forall n, In n (Graph.nodes g) ->
    (In n (Graph.entries g) \/ length (Graph.out g n) <> 1 \/ length (pred_edges p n) <> 1 \/
      FinSet.mem EN n (seg_event_points EN g event (edges_of g)) = true) ->
    seg_live EN work n).
  { intros n Hn Hreason; apply (seg_work_pinned Hwork n Hn).
    apply (seg_candidates_pinned EN g p event n Hready Hn Hreason). }
  assert (Hevents : forall e, In e (edges_of g) -> event e = true ->
    seg_live EN work (Graph.source g e) /\ seg_live EN work (Graph.target g e)).
  { intros e He Hevent; split.
    - apply Hpin; [eapply seg_edge_source_in; eassumption|].
      right; right; right; apply seg_event_points_spec; exists e; auto.
    - apply Hpin.
      + apply (out_target_in Hwf (Graph.source g e) e
          (seg_edge_source_in g e Hwf He) (edges_of_source g e Hwf He)).
      + right; right; right; apply seg_event_points_spec; exists e; auto. }
  constructor.
  - apply (seg_finish_ready EN EE g p candidates work Hready Hwork).
    intros n Hn; apply (seg_candidates_pinned EN g p event n Hready
      (entries_in Hwf n Hn)); now left.
  - reflexivity.
  - intros n Hn; apply (seg_finish_nodes EN EE g p candidates work n Hwork) in Hn.
    exact (seg_work_support Hwork n Hn).
  - intros n Hn Hboundary; apply (seg_finish_nodes EN EE g p candidates work n Hwork), Hpin;
      [exact Hn|].
    destruct Hboundary as [Hentry|Hout]; [now left|right; left; rewrite Hout; discriminate].
  - intros n Hn [Hout|Hpred]; apply (seg_finish_nodes EN EE g p candidates work n Hwork), Hpin;
      [exact Hn|now right; left|exact Hn|now right; right; left].
  - intros e He Hevent; destruct (Hevents e He Hevent) as [Hsource Htarget]; split;
      apply (seg_finish_nodes EN EE g p candidates work _ Hwork); assumption.
  - intros a Ha; apply (seg_finish_edges EN EE g p candidates work a Hready Hwork) in Ha.
    destruct Ha as [arc Harc]; destruct (seg_work_path Hwork a arc Harc)
      as [[es Hhead] [Hpath Hrest]].
    exists es; rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)), Hhead; split;
      [reflexivity|].
    rewrite (proj2 (seg_finish_path EN EE g p work a arc Harc)); now rewrite <- Hhead.
  - intros a Ha; apply (seg_finish_edges EN EE g p candidates work a Hready Hwork) in Ha.
    destruct Ha as [arc Harc]; rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)).
    exact (proj1 (proj2 (proj2 (proj2 (seg_work_path Hwork a arc Harc))))).
  - intros a Ha; apply (seg_finish_edges EN EE g p candidates work a Hready Hwork) in Ha.
    destruct Ha as [arc Harc]; rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)).
    apply (seg_work_internal_nodup EN EE g candidates work a arc); assumption.
  - intros a k n Ha Hnth; apply (seg_finish_edges EN EE g p candidates work a Hready Hwork) in Ha.
    destruct Ha as [arc Harc]; rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)) in Hnth.
    apply (proj2 (seg_finish_positions EN EE g p candidates work Hwf Hwork Hshape n a k)).
    exists arc; auto.
  - intros e He; destruct (seg_work_partition Hwork e He) as [a [[arc [Harc Hin]] Hunique]].
    exists a; split.
    + split.
      * apply (seg_finish_edges EN EE g p candidates work a Hready Hwork); now exists arc.
      * rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)); exact Hin.
    + intros b [Hb Hmember].
      apply (seg_finish_edges EN EE g p candidates work b Hready Hwork) in Hb.
      destruct Hb as [other Hother]; rewrite (proj1 (seg_finish_path EN EE g p work b other Hother))
        in Hmember.
      apply Hunique; exists other; auto.
  - intros a Ha Hsome; apply (seg_finish_edges EN EE g p candidates work a Hready Hwork) in Ha.
    destruct Ha as [arc Harc]; rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)) in *.
    destruct (seg_work_path Hwork a arc Harc)
      as [[es Hhead] [Hpath [Htip [Hnd Hinside]]]].
    rewrite Hhead in *; apply (seg_path_event_singleton g event a es (seg_tip arc)
      (seg_live EN work) Hpath Hinside); [|exact Hsome].
    intros e Hin Hevent; apply Hevents; [|exact Hevent].
    apply (seg_work_trace_in EN EE g candidates work a arc Hwf Hwork Harc); now rewrite Hhead.
  - intros n Hn Hnot.
    assert (Hdead : ~ seg_live EN work n).
    { intro H; apply Hnot, (seg_finish_nodes EN EE g p candidates work n Hwork); exact H. }
    destruct (seg_work_coverage Hwork n Hn Hdead) as [a [arc [Harc Hin]]].
    apply In_nth_error in Hin; destruct Hin as [k Hnth]; exists a, k; split.
    + apply (proj2 (seg_finish_positions EN EE g p candidates work Hwf Hwork Hshape n a k));
        now exists arc.
    + split.
      * apply (seg_finish_edges EN EE g p candidates work a Hready Hwork); now exists arc.
      * rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)); exact Hnth.
  - intros n a k Hget.
    apply (proj1 (seg_finish_positions EN EE g p candidates work Hwf Hwork Hshape n a k)) in Hget.
    destruct Hget as [arc [Harc Hnth]]; split.
    + apply (seg_finish_edges EN EE g p candidates work a Hready Hwork); now exists arc.
    + split; [rewrite (proj1 (seg_finish_path EN EE g p work a arc Harc)); exact Hnth|].
      intro Hlive; apply (seg_finish_nodes EN EE g p candidates work n Hwork) in Hlive.
      apply (proj2 (proj2 (proj2 (proj2 (seg_work_path Hwork a arc Harc)))) n);
        [eapply nth_error_In; exact Hnth|exact Hlive].
  - intros n Hn Hnot; destruct (Map.get EN n candidates) as [b|] eqn:Hget.
    + destruct (seg_candidates_sound EN g p _ _ n b Hget) as [_ [Hout [[d Hpred] Hrest]]].
      rewrite (succ_agrees (proj2 (proj2 Hready)) n Hn) in Hout.
      unfold p in Hpred; rewrite Hout, Hpred; auto.
    + exfalso; apply Hnot, (seg_finish_nodes EN EE g p candidates work n Hwork).
      exact (seg_work_pinned Hwork n Hn Hget).
Qed.

(** Construction partitions all edges and indexes every contracted original point exactly. *)
Theorem build_expression_seg_correct {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  seg_index_laws EN EE (cfg (gkview gk)) (seg_event EU gk u)
    (build_expression_seg EN EE EU gk u).
Proof.
  intro Hready; unfold build_expression_seg; apply seg_finish_correct; [exact Hready|].
  apply seg_built_work_laws; exact Hready.
Qed.

Local Lemma seg_built_out_agrees {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) u n :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  In n (Graph.nodes (seg_graph (build_expression_seg EN EE EU gk u))) ->
  Graph.out (seg_graph (build_expression_seg EN EE EU gk u)) n = Graph.out (cfg (gkview gk)) n.
Proof.
  intros Hready Hn; unfold build_expression_seg in *; eapply seg_finish_out_agrees;
    [exact Hready|apply seg_built_work_laws; exact Hready|exact Hn].
Qed.

(** * Boolean projection and finite must-facts *)

Local Lemma seg_bool_equal (a b : bool) : (a = true <-> b = true) -> a = b.
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Local Lemma seg_bool_le (a b : bool) :
  leb seg_must_lattice a b = true <-> (b = true -> a = true).
Proof.
  destruct a, b; cbn; intuition congruence.
Qed.

Local Lemma seg_clamp_spec {U} (EU : encoding U) universe set u :
  fmem EU u (finite_clamp EU universe set) = true <->
  In u universe /\ FinSet.mem EU u set = true.
Proof.
  change (FinSet.mem EU u (FinSet.of_list EU
    (filter (fun u => FinSet.mem EU u set) universe)) = true <->
    In u universe /\ FinSet.mem EU u set = true).
  rewrite FinSet.of_list_spec, filter_In; reflexivity.
Qed.

Local Lemma seg_transfer_member {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u e a :
  In u (expr_universe EU gk) ->
  fmem EU u (avail_transfer EU gk e a) = seg_bit_transfer EU gk u e (fmem EU u a).
Proof.
  intro Hu; apply seg_bool_equal; unfold avail_transfer, seg_bit_transfer.
  rewrite seg_clamp_spec, FinSet.mem_union, !FinSet.of_list_spec, filter_In,
    (FinSet.elements_spec EU u _ (proj1 (proj2_sig a))), orb_true_iff, andb_true_iff,
    negb_true_iff, seg_mentions_spec.
  unfold fmem; tauto.
Qed.

Local Lemma seg_dense_transfer_monotone {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) e :
  monotone_fun (avail_lattice EU gk) (avail_lattice EU gk) (avail_transfer EU gk e).
Proof.
  intros a b Hle; apply FinSet.subset_spec;
    [exact (proj1 (proj2_sig (avail_transfer EU gk e b)))|].
  intros u Hmember; assert (Hu : In u (expr_universe EU gk)) by
    (exact (proj2 (proj2_sig (avail_transfer EU gk e b)) u Hmember)).
  change (fmem EU u (avail_transfer EU gk e a) = true).
  change (fmem EU u (avail_transfer EU gk e b) = true) in Hmember.
  rewrite (seg_transfer_member EU gk u e a Hu), (seg_transfer_member EU gk u e b Hu) in *.
  apply (proj1 (seg_bool_le _ _) (seg_bit_monotone EU gk u e _ _
    (proj2 (seg_bool_le _ _) (set_member_subset EU _ _ Hle u)))); exact Hmember.
Qed.

Local Definition seg_lift_bit {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (b : bool) : avail_set EU gk :=
  finite_clamp EU (expr_universe EU gk) (if b then FinSet.of_list EU [u] else FinSet.empty).

Local Lemma seg_lift_member {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u b v :
  fmem EU v (seg_lift_bit EU gk u b) = true <->
  In v (expr_universe EU gk) /\ v = u /\ b = true.
Proof.
  unfold seg_lift_bit; rewrite seg_clamp_spec; destruct b.
  - rewrite FinSet.of_list_spec; cbn; intuition congruence.
  - rewrite FinSet.mem_empty; intuition congruence.
Qed.

Local Lemma seg_lift_self {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u b :
  In u (expr_universe EU gk) -> fmem EU u (seg_lift_bit EU gk u b) = b.
Proof.
  intro Hu; apply seg_bool_equal; rewrite seg_lift_member; tauto.
Qed.

Local Definition seg_dense_available {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u : System.t N (dense_constraint N E) bool :=
  forward_system (cfg (gkview gk)) (fun _ => false) (seg_bit_transfer EU gk u).

Local Definition seg_dense_busy {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u : System.t N (dense_constraint N E) bool :=
  backward_system (cfg (gkview gk))
    (fun n => match Graph.out (cfg (gkview gk)) n with [] => false | _ => true end)
    (seg_bit_transfer EU gk u).

Local Lemma seg_available_project {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u sigma :
  In u (expr_universe EU gk) ->
  post_solution (avail_lattice EU gk) (available_system EU gk) sigma ->
  post_solution seg_must_lattice (seg_dense_available EU gk u) (fun n => fmem EU u (sigma n)).
Proof.
  intros Hu Hpost; apply forward_post_solution_iff.
  destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow]; split.
  - intros n Hn; apply seg_bool_le; intro Hmember.
    pose proof (set_member_subset EU _ _ (Hseed n Hn) u Hmember) as Hempty.
    apply seg_clamp_spec in Hempty; rewrite FinSet.mem_empty in Hempty; tauto.
  - intros e He; apply seg_bool_le; intro Hmember.
    rewrite <- seg_transfer_member by exact Hu.
    exact (set_member_subset EU _ _ (Hflow e He) u Hmember).
Qed.

Local Lemma seg_busy_project {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u sigma :
  In u (expr_universe EU gk) ->
  post_solution (avail_lattice EU gk) (busy_system EU gk) sigma ->
  post_solution seg_must_lattice (seg_dense_busy EU gk u) (fun n => fmem EU u (sigma n)).
Proof.
  intros Hu Hpost; apply backward_post_solution_iff.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow]; split.
  - intros n Hn; apply seg_bool_le.
    specialize (Hseed n Hn); destruct (Graph.out (cfg (gkview gk)) n) as [|e es]; [|reflexivity].
    intro Hmember; pose proof (set_member_subset EU _ _ Hseed u Hmember) as Hempty.
    apply seg_clamp_spec in Hempty; rewrite FinSet.mem_empty in Hempty; tauto.
  - intros e He; apply seg_bool_le; intro Hmember.
    rewrite <- seg_transfer_member by exact Hu.
    exact (set_member_subset EU _ _ (Hflow e He) u Hmember).
Qed.

Local Lemma seg_available_lift {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u rho :
  post_solution seg_must_lattice (seg_dense_available EU gk u) rho ->
  post_solution (avail_lattice EU gk) (available_system EU gk)
    (fun n => seg_lift_bit EU gk u (rho n)).
Proof.
  intro Hpost; destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply forward_post_solution_iff; split.
  - intros n Hn; apply FinSet.subset_spec;
      [exact (proj1 (proj2_sig (seg_lift_bit EU gk u (rho n))))|].
    intros v Hmember; apply seg_lift_member in Hmember; destruct Hmember as [Hv [-> Hbit]].
    pose proof (proj1 (seg_bool_le _ _) (Hseed n Hn) Hbit) as Hfalse; discriminate.
  - intros e He; apply FinSet.subset_spec;
      [exact (proj1 (proj2_sig
        (seg_lift_bit EU gk u (rho (Graph.target (cfg (gkview gk)) e)))))|].
    intros v Hmember; apply seg_lift_member in Hmember; destruct Hmember as [Hv [-> Hbit]].
    change (fmem EU u (avail_transfer EU gk e
      (seg_lift_bit EU gk u (rho (Graph.source (cfg (gkview gk)) e)))) = true).
    rewrite (seg_transfer_member EU gk u e _ Hv), (seg_lift_self EU gk u _ Hv).
    apply (proj1 (seg_bool_le _ _) (Hflow e He)); exact Hbit.
Qed.

Local Lemma seg_busy_lift {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u rho :
  post_solution seg_must_lattice (seg_dense_busy EU gk u) rho ->
  post_solution (avail_lattice EU gk) (busy_system EU gk)
    (fun n => seg_lift_bit EU gk u (rho n)).
Proof.
  intro Hpost; destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply backward_post_solution_iff; split.
  - intros n Hn; destruct (Graph.out (cfg (gkview gk)) n) as [|e es] eqn:Hout.
    + apply FinSet.subset_spec; [exact (proj1 (proj2_sig (seg_lift_bit EU gk u (rho n))))|].
      intros v Hmember; apply seg_lift_member in Hmember; destruct Hmember as [Hv [-> Hbit]].
      pose proof (proj1 (seg_bool_le _ _) (Hseed n Hn) Hbit) as Hfalse.
      cbn in Hfalse; rewrite Hout in Hfalse; discriminate.
    + apply bot_least, finite_must_laws.
  - intros e He; apply FinSet.subset_spec;
      [exact (proj1 (proj2_sig
        (seg_lift_bit EU gk u (rho (Graph.source (cfg (gkview gk)) e)))))|].
    intros v Hmember; apply seg_lift_member in Hmember; destruct Hmember as [Hv [-> Hbit]].
    change (fmem EU u (avail_transfer EU gk e
      (seg_lift_bit EU gk u (rho (Graph.target (cfg (gkview gk)) e)))) = true).
    rewrite (seg_transfer_member EU gk u e _ Hv), (seg_lift_self EU gk u _ Hv).
    apply (proj1 (seg_bool_le _ _) (Hflow e He)); exact Hbit.
Qed.

(** * Reconstruction on contracted paths *)

Local Lemma seg_forward_identity {E} (transfer : E -> bool -> bool) es b :
  (forall e, In e es -> forall b, transfer e b = b) ->
  fold_left (fun b e => transfer e b) es b = b.
Proof.
  revert b; induction es as [|e es IH]; intros b Hidentity; cbn; [reflexivity|].
  rewrite (Hidentity e (or_introl eq_refl) b); apply IH.
  intros d Hd b'; exact (Hidentity d (or_intror Hd) b').
Qed.

Local Lemma seg_backward_identity {E} (transfer : E -> bool -> bool) es b :
  (forall e, In e es -> forall b, transfer e b = b) -> fold_right transfer b es = b.
Proof.
  induction es as [|e es IH]; intro Hidentity; cbn; [reflexivity|].
  rewrite (Hidentity e (or_introl eq_refl) (fold_right transfer b es)); apply IH.
  intros d Hd b'; exact (Hidentity d (or_intror Hd) b').
Qed.

Local Lemma seg_firstn_in {A} k (xs : list A) x : In x (firstn k xs) -> In x xs.
Proof.
  revert xs; induction k as [|k IH]; intros [|y ys]; cbn; intro Hin; try contradiction.
  destruct Hin as [<-|Hin]; [now left|right; apply IH; exact Hin].
Qed.

Local Lemma seg_skipn_in {A} k (xs : list A) x : In x (skipn k xs) -> In x xs.
Proof.
  intro Hin; rewrite <- (firstn_skipn k xs); apply in_or_app; now right.
Qed.

Local Lemma seg_reconstruct_cut {N E} (EN : encoding N) (EE : encoding E)
    (idx : seg_index N E) transfer cut n :
  In n (Graph.nodes (seg_graph idx)) ->
  seg_reconstruct_available EN EE idx transfer cut n = cut n /\
  seg_reconstruct_busy EN EE idx transfer cut n = cut n.
Proof.
  intro Hn; unfold seg_reconstruct_available, seg_reconstruct_busy.
  rewrite (proj2 (FinSet.of_list_spec EN n _) Hn); split; reflexivity.
Qed.

Local Lemma seg_reconstruct_interior {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) event idx transfer cut a k n :
  seg_index_laws EN EE g event idx ->
  (forall e, event e = false -> forall b, transfer e b = b) ->
  In a (edges_of (seg_graph idx)) ->
  nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n ->
  seg_reconstruct_available EN EE idx transfer cut n = cut (Graph.source (seg_graph idx) a) /\
  seg_reconstruct_busy EN EE idx transfer cut n = cut (Graph.target (seg_graph idx) a).
Proof.
  intros Hidx Hidentity Ha Hnth.
  pose proof (seg_internal_lookup _ _ _ _ _ Hidx a k n Ha Hnth) as Hget.
  destruct (seg_interior_only _ _ _ _ _ Hidx n a k Hget) as [_ [_ Hnot]].
  assert (Habsent : FinSet.mem EN n (FinSet.of_list EN (Graph.nodes (seg_graph idx))) = false).
  { destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.nodes (seg_graph idx)))) eqn:Hmem;
      [exfalso; apply Hnot, (proj1 (FinSet.of_list_spec EN n _) Hmem)|reflexivity]. }
  assert (Hedges : forall e, In e (seg_path EE idx a) -> forall b, transfer e b = b).
  { intros e He b; apply Hidentity; destruct (event e) eqn:Hevent; [|reflexivity].
    pose proof (seg_no_event_inside _ _ _ _ _ Hidx a Ha (ex_intro _ e (conj He Hevent))) as Hsingle.
    rewrite Hsingle in Hnth; destruct k; discriminate. }
  unfold seg_reconstruct_available, seg_reconstruct_busy; rewrite Habsent, Hget; split.
  - apply seg_forward_identity; intros e He; apply Hedges; eapply seg_firstn_in; exact He.
  - apply seg_backward_identity; intros e He; apply Hedges; eapply seg_skipn_in; exact He.
Qed.

Local Lemma seg_path_sources {N E} (g : Graph.t N E) start es tip e :
  path g start es tip -> In e es ->
  Graph.source g e = start \/ In (Graph.source g e) (seg_internal_nodes g es).
Proof.
  intros Hpath Hin; destruct Hpath as [v|a rest tip Hedge Htail]; [contradiction|].
  destruct Hin as [<-|Hin]; [now left|right].
  rewrite (seg_internal_sources g _ _ _ (path_cons a rest tip Hedge Htail)).
  apply in_map; exact Hin.
Qed.

Local Lemma seg_path_targets_in {N E} (g : Graph.t N E) start es tip e :
  path g start es tip -> In e es ->
  Graph.target g e = tip \/ In (Graph.target g e) (seg_internal_nodes g es).
Proof.
  intros Hpath Hin; assert (Hnonempty : es <> []) by (intro Heq; rewrite Heq in Hin; contradiction).
  assert (Hmember : In (Graph.target g e) (map (Graph.target g) es)) by (apply in_map; exact Hin).
  rewrite (seg_path_targets g start es tip Hpath Hnonempty), in_app_iff in Hmember.
  destruct Hmember as [Hinside|[Heq|Hnone]]; [now right|left; now symmetry|contradiction].
Qed.

Local Lemma seg_cut_endpoints {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) event idx a :
  seg_index_laws EN EE g event idx -> In a (edges_of (seg_graph idx)) ->
  In (Graph.source (seg_graph idx) a) (Graph.nodes (seg_graph idx)) /\
  In (Graph.target (seg_graph idx) a) (Graph.nodes (seg_graph idx)).
Proof.
  intros Hidx Ha; pose proof (proj1 (seg_wf _ _ _ _ _ Hidx)) as Hwf; split.
  - eapply seg_edge_source_in; eassumption.
  - eapply out_target_in;
      [exact Hwf|eapply seg_edge_source_in; eassumption|apply edges_of_source; assumption].
Qed.

Local Lemma seg_forward_monotone {E} (transfer : E -> bool -> bool) es :
  (forall e, In e es -> monotone_fun seg_must_lattice seg_must_lattice (transfer e)) ->
  monotone_fun seg_must_lattice seg_must_lattice
    (fun b => fold_left (fun b e => transfer e b) es b).
Proof.
  induction es as [|e es IH]; intros Hmono x y Hxy; cbn; [exact Hxy|].
  apply IH.
  - intros d Hd; apply Hmono; now right.
  - apply Hmono; [now left|exact Hxy].
Qed.

Local Lemma seg_backward_monotone {E} (transfer : E -> bool -> bool) es :
  (forall e, In e es -> monotone_fun seg_must_lattice seg_must_lattice (transfer e)) ->
  monotone_fun seg_must_lattice seg_must_lattice (fun b => fold_right transfer b es).
Proof.
  induction es as [|e es IH]; intros Hmono x y Hxy; cbn; [exact Hxy|].
  apply Hmono; [now left|apply IH; [|exact Hxy]].
  intros d Hd; apply Hmono; now right.
Qed.

Local Lemma seg_forward_path_bound {N E} (g : Graph.t N E) transfer sigma start es tip :
  graph_wf g -> In start (Graph.nodes g) -> path g start es tip ->
  (forall e, In e (edges_of g) ->
    monotone_fun seg_must_lattice seg_must_lattice (transfer e)) ->
  (forall e, In e (edges_of g) ->
    leb seg_must_lattice (transfer e (sigma (Graph.source g e)))
      (sigma (Graph.target g e)) = true) ->
  leb seg_must_lattice (fold_left (fun b e => transfer e b) es (sigma start)) (sigma tip) = true.
Proof.
  intros Hwf Hstart Hpath Hmono Hflow; induction Hpath as [v|e es tip Hedge Hpath IH].
  - apply (leb_refl seg_must_laws).
  - cbn; assert (He : In e (edges_of g)) by (eapply edges_of_in; eassumption).
    assert (Htarget : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
    eapply (leb_trans seg_must_laws).
    + apply seg_forward_monotone; [|apply Hflow; exact He].
      intros d Hd; apply Hmono; apply (proj2 (seg_path_edge_nodes g _ _ _ Hwf Htarget Hpath));
        exact Hd.
    + apply IH; exact Htarget.
Qed.

Local Lemma seg_backward_path_bound {N E} (g : Graph.t N E) transfer sigma start es tip :
  graph_wf g -> In start (Graph.nodes g) -> path g start es tip ->
  (forall e, In e (edges_of g) ->
    monotone_fun seg_must_lattice seg_must_lattice (transfer e)) ->
  (forall e, In e (edges_of g) ->
    leb seg_must_lattice (transfer e (sigma (Graph.target g e)))
      (sigma (Graph.source g e)) = true) ->
  leb seg_must_lattice (fold_right transfer (sigma tip) es) (sigma start) = true.
Proof.
  intros Hwf Hstart Hpath Hmono Hflow; induction Hpath as [v|e es tip Hedge Hpath IH].
  - apply (leb_refl seg_must_laws).
  - cbn; assert (He : In e (edges_of g)) by (eapply edges_of_in; eassumption).
    assert (Htarget : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
    eapply (leb_trans seg_must_laws); [apply Hmono; [exact He|apply IH; exact Htarget]|].
    apply Hflow; exact He.
Qed.

Local Lemma seg_path_split {N E} (g : Graph.t N E) start es tip k n :
  path g start es tip -> nth_error (seg_internal_nodes g es) k = Some n ->
  path g start (firstn (S k) es) n /\ path g n (skipn (S k) es) tip.
Proof.
  intro Hpath; revert k; induction Hpath as [v|e es tip Hedge Hpath IH]; intros k Hnth.
  - destruct k; discriminate.
  - destruct es as [|d es]; [destruct k; discriminate|].
    destruct k as [|k]; cbn [seg_internal_nodes removelast map nth_error] in Hnth.
    + inversion Hnth; subst n; split; [constructor; [exact Hedge|constructor]|exact Hpath].
    + destruct (IH k Hnth) as [Hprefix Hsuffix]; split;
        [constructor; [exact Hedge|exact Hprefix]|exact Hsuffix].
Qed.

Section SegEquivalence.
Context {S O N E U C : Type} (EN : encoding N) (EE : encoding E) (EU : encoding U)
  (gk : genkill_view S O N E U C) (u : U).
Hypothesis Hready : ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))).
Let g := cfg (gkview gk).
Let idx := build_expression_seg EN EE EU gk u.
Let transfer := seg_bit_transfer EU gk u.

Local Lemma seg_equivalence_index : seg_index_laws EN EE g (seg_event EU gk u) idx.
Proof.
  apply build_expression_seg_correct; exact Hready.
Qed.

Local Lemma seg_equivalence_summaries a b : In a (edges_of (seg_graph idx)) ->
  seg_forward_transfer EE EU gk u idx a b =
    fold_left (fun acc e => transfer e acc) (seg_path EE idx a) b /\
  seg_backward_transfer EE EU gk u idx a b = fold_right transfer b (seg_path EE idx a).
Proof.
  apply build_expression_seg_summaries; exact Hready.
Qed.

Local Lemma seg_equivalence_out n : In n (Graph.nodes (seg_graph idx)) ->
  Graph.out (seg_graph idx) n = Graph.out g n.
Proof.
  apply seg_built_out_agrees; exact Hready.
Qed.

Local Lemma seg_restrict_available sigma :
  post_solution seg_must_lattice (seg_dense_available EU gk u) sigma ->
  post_solution seg_must_lattice (seg_available_system EE EU gk u idx) sigma.
Proof.
  intro Hpost; destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply forward_post_solution_iff; split.
  - intros n Hn; rewrite (seg_entries _ _ _ _ _ seg_equivalence_index) in Hn.
    exact (Hseed n Hn).
  - intros a Ha; rewrite (proj1 (seg_equivalence_summaries a
      (sigma (Graph.source (seg_graph idx) a)) Ha)).
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite Hes; apply (seg_forward_path_bound g transfer sigma _ _ _ (proj1 Hready)).
    + apply (seg_nodes_original _ _ _ _ _ seg_equivalence_index).
      exact (proj1 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)).
    + exact Hpath.
    + intros e He; apply seg_bit_monotone.
    + exact Hflow.
Qed.

Local Lemma seg_restrict_busy sigma :
  post_solution seg_must_lattice (seg_dense_busy EU gk u) sigma ->
  post_solution seg_must_lattice (seg_busy_system EE EU gk u idx) sigma.
Proof.
  intro Hpost; destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply backward_post_solution_iff; split.
  - intros n Hn; specialize (Hseed n (seg_nodes_original _ _ _ _ _ seg_equivalence_index n Hn)).
    rewrite (seg_equivalence_out n Hn); exact Hseed.
  - intros a Ha; rewrite (proj2 (seg_equivalence_summaries a
      (sigma (Graph.target (seg_graph idx) a)) Ha)).
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite Hes; apply (seg_backward_path_bound g transfer sigma _ _ _ (proj1 Hready)).
    + apply (seg_nodes_original _ _ _ _ _ seg_equivalence_index).
      exact (proj1 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)).
    + exact Hpath.
    + intros e He; apply seg_bit_monotone.
    + exact Hflow.
Qed.

Local Lemma seg_arc_identity a : In a (edges_of (seg_graph idx)) ->
  seg_path EE idx a <> [a] ->
  forall e, In e (seg_path EE idx a) -> forall b, transfer e b = b.
Proof.
  intros Ha Hlong e He b; apply seg_bit_identity.
  destruct (seg_event EU gk u e) eqn:Hevent; [|reflexivity].
  exfalso; apply Hlong, (seg_no_event_inside _ _ _ _ _ seg_equivalence_index a Ha).
  exists e; auto.
Qed.

Local Lemma seg_reconstruct_on_arc cut a e : In a (edges_of (seg_graph idx)) ->
  In e (seg_path EE idx a) ->
  seg_reconstruct_available EN EE idx transfer cut (Graph.source g e) =
    cut (Graph.source (seg_graph idx) a) /\
  seg_reconstruct_busy EN EE idx transfer cut (Graph.target g e) =
    cut (Graph.target (seg_graph idx) a) /\
  (Graph.target g e = Graph.target (seg_graph idx) a \/
    seg_reconstruct_available EN EE idx transfer cut (Graph.target g e) =
      cut (Graph.source (seg_graph idx) a)) /\
  (Graph.source g e = Graph.source (seg_graph idx) a \/
    seg_reconstruct_busy EN EE idx transfer cut (Graph.source g e) =
      cut (Graph.target (seg_graph idx) a)).
Proof.
  intros Ha He; destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha)
    as [es [Hes Hpath]]; rewrite <- Hes in Hpath.
  destruct (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha) as [Hsource Htarget].
  assert (Hinterior : forall n, In n (seg_internal_nodes g (seg_path EE idx a)) ->
    seg_reconstruct_available EN EE idx transfer cut n = cut (Graph.source (seg_graph idx) a) /\
    seg_reconstruct_busy EN EE idx transfer cut n = cut (Graph.target (seg_graph idx) a)).
  { intros n Hin; apply In_nth_error in Hin; destruct Hin as [k Hnth].
    apply (seg_reconstruct_interior EN EE g _ idx transfer cut a k n seg_equivalence_index);
      [intros d Hd b; apply seg_bit_identity; exact Hd|exact Ha|exact Hnth]. }
  pose proof (seg_path_sources g _ _ _ e Hpath He) as Hsources.
  pose proof (seg_path_targets_in g _ _ _ e Hpath He) as Htargets.
  split.
  - destruct Hsources as [Heq|Hin].
    + rewrite Heq; exact (proj1 (seg_reconstruct_cut EN EE idx transfer cut _ Hsource)).
    + exact (proj1 (Hinterior _ Hin)).
  - split.
    + destruct Htargets as [Heq|Hin].
      * rewrite Heq; exact (proj2 (seg_reconstruct_cut EN EE idx transfer cut _ Htarget)).
      * exact (proj2 (Hinterior _ Hin)).
    + split.
      * destruct Htargets as [Heq|Hin]; [now left|right; exact (proj1 (Hinterior _ Hin))].
      * destruct Hsources as [Heq|Hin]; [now left|right; exact (proj2 (Hinterior _ Hin))].
Qed.

Local Lemma seg_singleton_endpoints start a tip : path g start [a] tip ->
  Graph.source g a = start /\ Graph.target g a = tip.
Proof.
  intro Hpath; inversion Hpath as [|e es w Hedge Htail]; subst.
  inversion Htail; split; congruence.
Qed.

Local Lemma seg_reconstructed_available_post cut :
  post_solution seg_must_lattice (seg_available_system EE EU gk u idx) cut ->
  post_solution seg_must_lattice (seg_dense_available EU gk u)
    (seg_reconstruct_available EN EE idx transfer cut).
Proof.
  intro Hpost; destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply forward_post_solution_iff; fold g transfer; split.
  - intros n Hn; assert (Hcut : In n (Graph.nodes (seg_graph idx))).
    { apply (entries_in (proj1 (seg_wf _ _ _ _ _ seg_equivalence_index)) n).
      rewrite (seg_entries _ _ _ _ _ seg_equivalence_index); exact Hn. }
    rewrite (proj1 (seg_reconstruct_cut EN EE idx transfer cut n Hcut)); apply Hseed.
    rewrite (seg_entries _ _ _ _ _ seg_equivalence_index); exact Hn.
  - intros e He; destruct (seg_edge_partition _ _ _ _ _ seg_equivalence_index e He)
      as [a [[Ha Hmember] Hunique]].
    destruct (seg_reconstruct_on_arc cut a e Ha Hmember) as [Hsource [_ [Htarget Hrest]]].
    pose proof (Hflow a Ha) as Hbound.
    rewrite (proj1 (seg_equivalence_summaries a
      (cut (Graph.source (seg_graph idx) a)) Ha)) in Hbound.
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite Hsource; destruct es as [|d es].
    + rewrite Hes in Hmember; destruct Hmember as [<-|Hnone]; [|contradiction].
      destruct (seg_singleton_endpoints _ a _ Hpath) as [Hs Ht].
      rewrite Ht, (proj1 (seg_reconstruct_cut EN EE idx transfer cut _
        (proj2 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)))).
      rewrite Hes in Hbound; exact Hbound.
    + assert (Hlong : seg_path EE idx a <> [a]) by (rewrite Hes; discriminate).
      rewrite (seg_arc_identity a Ha Hlong e Hmember).
      rewrite (seg_forward_identity transfer _ _ (seg_arc_identity a Ha Hlong)) in Hbound.
      destruct Htarget as [Ht|Ht].
      * rewrite Ht, (proj1 (seg_reconstruct_cut EN EE idx transfer cut _
          (proj2 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)))); exact Hbound.
      * rewrite Ht; apply (leb_refl seg_must_laws).
Qed.

Local Lemma seg_reconstructed_busy_post cut :
  post_solution seg_must_lattice (seg_busy_system EE EU gk u idx) cut ->
  post_solution seg_must_lattice (seg_dense_busy EU gk u)
    (seg_reconstruct_busy EN EE idx transfer cut).
Proof.
  intro Hpost; destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost)
    as [Hseed Hflow]; apply backward_post_solution_iff; fold g transfer; split.
  - intros n Hn; destruct (Graph.out g n) as [|e es] eqn:Hout;
      [|apply (bot_least seg_must_laws)].
    assert (Hcut : In n (Graph.nodes (seg_graph idx))).
    { apply (seg_boundaries _ _ _ _ _ seg_equivalence_index n Hn); now right. }
    rewrite (proj2 (seg_reconstruct_cut EN EE idx transfer cut n Hcut)).
    pose proof (Hseed n Hcut) as Hbound; rewrite (seg_equivalence_out n Hcut) in Hbound.
    fold g in Hbound; rewrite Hout in Hbound; exact Hbound.
  - intros e He; destruct (seg_edge_partition _ _ _ _ _ seg_equivalence_index e He)
      as [a [[Ha Hmember] Hunique]].
    destruct (seg_reconstruct_on_arc cut a e Ha Hmember) as [_ [Htarget [_ Hsource]]].
    pose proof (Hflow a Ha) as Hbound.
    rewrite (proj2 (seg_equivalence_summaries a
      (cut (Graph.target (seg_graph idx) a)) Ha)) in Hbound.
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite Htarget; destruct es as [|d es].
    + rewrite Hes in Hmember; destruct Hmember as [<-|Hnone]; [|contradiction].
      destruct (seg_singleton_endpoints _ a _ Hpath) as [Hs Ht].
      rewrite Hs, (proj2 (seg_reconstruct_cut EN EE idx transfer cut _
        (proj1 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)))).
      rewrite Hes in Hbound; exact Hbound.
    + assert (Hlong : seg_path EE idx a <> [a]) by (rewrite Hes; discriminate).
      rewrite (seg_arc_identity a Ha Hlong e Hmember).
      rewrite (seg_backward_identity transfer _ _ (seg_arc_identity a Ha Hlong)) in Hbound.
      destruct Hsource as [Hs|Hs].
      * rewrite Hs, (proj2 (seg_reconstruct_cut EN EE idx transfer cut _
          (proj1 (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha)))); exact Hbound.
      * rewrite Hs; apply (leb_refl seg_must_laws).
Qed.

Local Lemma seg_available_compare sigma cut :
  post_solution seg_must_lattice (seg_dense_available EU gk u) sigma ->
  (forall n, In n (Graph.nodes (seg_graph idx)) -> leb seg_must_lattice (cut n) (sigma n) = true) ->
  forall n, In n (Graph.nodes g) ->
  leb seg_must_lattice (seg_reconstruct_available EN EE idx transfer cut n) (sigma n) = true.
Proof.
  intros Hpost Hcut n Hn; destruct (in_dec (seg_eq_dec EN) n (Graph.nodes (seg_graph idx)))
    as [Hlisted|Hnot].
  - rewrite (proj1 (seg_reconstruct_cut EN EE idx transfer cut n Hlisted)).
    apply Hcut; exact Hlisted.
  - destruct (seg_interior_unique _ _ _ _ _ seg_equivalence_index n Hn Hnot)
      as [a [k [Hindex [Ha Hnth]]]].
    rewrite (proj1 (seg_reconstruct_interior EN EE g _ idx transfer cut a k n
      seg_equivalence_index (fun e He b => seg_bit_identity EU gk u e b He) Ha Hnth)).
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite <- Hes in Hpath; destruct (seg_path_split g _ _ _ k n Hpath Hnth) as [Hprefix Hsuffix].
    destruct (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha) as [Hsource Htarget].
    destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
    pose proof (seg_forward_path_bound g transfer sigma _ _ _ (proj1 Hready)
      (seg_nodes_original _ _ _ _ _ seg_equivalence_index _ Hsource) Hprefix
      (fun e He => seg_bit_monotone EU gk u e) Hflow) as Hbound.
    assert (Hlong : seg_path EE idx a <> [a]).
    { intro Hsingle; rewrite Hsingle in Hnth; destruct k; discriminate. }
    rewrite (seg_forward_identity transfer _ _ (fun e He =>
      seg_arc_identity a Ha Hlong e (seg_firstn_in (Nat.succ k) _ e He))) in Hbound.
    eapply (leb_trans seg_must_laws); [apply Hcut; exact Hsource|exact Hbound].
Qed.

Local Lemma seg_busy_compare sigma cut :
  post_solution seg_must_lattice (seg_dense_busy EU gk u) sigma ->
  (forall n, In n (Graph.nodes (seg_graph idx)) -> leb seg_must_lattice (cut n) (sigma n) = true) ->
  forall n, In n (Graph.nodes g) ->
  leb seg_must_lattice (seg_reconstruct_busy EN EE idx transfer cut n) (sigma n) = true.
Proof.
  intros Hpost Hcut n Hn; destruct (in_dec (seg_eq_dec EN) n (Graph.nodes (seg_graph idx)))
    as [Hlisted|Hnot].
  - rewrite (proj2 (seg_reconstruct_cut EN EE idx transfer cut n Hlisted)).
    apply Hcut; exact Hlisted.
  - destruct (seg_interior_unique _ _ _ _ _ seg_equivalence_index n Hn Hnot)
      as [a [k [Hindex [Ha Hnth]]]].
    rewrite (proj2 (seg_reconstruct_interior EN EE g _ idx transfer cut a k n
      seg_equivalence_index (fun e He b => seg_bit_identity EU gk u e b He) Ha Hnth)).
    destruct (seg_path_valid _ _ _ _ _ seg_equivalence_index a Ha) as [es [Hes Hpath]].
    rewrite <- Hes in Hpath; destruct (seg_path_split g _ _ _ k n Hpath Hnth) as [Hprefix Hsuffix].
    destruct (seg_cut_endpoints EN EE g _ idx a seg_equivalence_index Ha) as [Hsource Htarget].
    destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
    pose proof (seg_backward_path_bound g transfer sigma _ _ _ (proj1 Hready) Hn Hsuffix
      (fun e He => seg_bit_monotone EU gk u e) Hflow) as Hbound.
    assert (Hlong : seg_path EE idx a <> [a]).
    { intro Hsingle; rewrite Hsingle in Hnth; destruct k; discriminate. }
    rewrite (seg_backward_identity transfer _ _ (fun e He =>
      seg_arc_identity a Ha Hlong e (seg_skipn_in (Nat.succ k) _ e He))) in Hbound.
    eapply (leb_trans seg_must_laws); [apply Hcut; exact Htarget|exact Hbound].
Qed.

End SegEquivalence.

Local Lemma seg_flow_row {N E} (seeds : list N) (es : list E) e :
  In (Flow e) (map Seed seeds ++ map Flow es) -> In e es.
Proof.
  intro Hrow; apply in_app_or in Hrow; destruct Hrow as [Hseed|Hflow].
  - apply in_map_iff in Hseed; destruct Hseed as [n [Heq Hin]]; discriminate.
  - apply in_map_iff in Hflow; destruct Hflow as [d [Heq Hin]]; inversion Heq; subst d; exact Hin.
Qed.

Local Lemma seg_forward_system_monotone {N E A} (L : lattice A) (HL : lattice_laws L)
    (g : Graph.t N E) init transfer :
  (forall e, In e (edges_of g) -> monotone_fun L L (transfer e)) ->
  monotone_system L (forward_system g init transfer).
Proof.
  intros Hmono [n|e] Hrow; split.
  - intros sigma tau Hle; apply (leb_refl HL).
  - intros sigma tau Hle x b Hside; contradiction.
  - assert (He : In e (edges_of g)).
    { eapply seg_flow_row; exact Hrow. }
    intros sigma tau Hle; apply Hmono; [exact He|apply Hle].
  - intros sigma tau Hle x b Hside; contradiction.
Qed.

Local Lemma seg_backward_system_monotone {N E A} (L : lattice A) (HL : lattice_laws L)
    (g : Graph.t N E) init transfer :
  (forall e, In e (edges_of g) -> monotone_fun L L (transfer e)) ->
  monotone_system L (backward_system g init transfer).
Proof.
  intros Hmono [n|e] Hrow; split.
  - intros sigma tau Hle; apply (leb_refl HL).
  - intros sigma tau Hle x b Hside; contradiction.
  - assert (He : In e (edges_of g)).
    { eapply seg_flow_row; exact Hrow. }
    intros sigma tau Hle; apply Hmono; [exact He|apply Hle].
  - intros sigma tau Hle x b Hside; contradiction.
Qed.

Local Lemma seg_available_cut_least {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) u :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  let idx := build_expression_seg EN EE EU gk u in
  least_solution seg_must_lattice (seg_available_system EE EU gk u idx)
    (seg_available_cut EN EE EU gk u idx).
Proof.
  intros Hready idx; unfold seg_available_cut; apply solve_total_least; [exact seg_must_lub|].
  apply (seg_forward_system_monotone seg_must_lattice seg_must_laws);
    intros a Ha x y Hxy; unfold idx in *.
  rewrite (proj1 (build_expression_seg_summaries EN EE EU gk u Hready a x Ha)),
    (proj1 (build_expression_seg_summaries EN EE EU gk u Hready a y Ha)).
  apply seg_forward_monotone; [intros e He; apply seg_bit_monotone|exact Hxy].
Qed.

Local Lemma seg_busy_cut_least {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) u :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  let idx := build_expression_seg EN EE EU gk u in
  least_solution seg_must_lattice (seg_busy_system EE EU gk u idx)
    (seg_busy_cut EN EE EU gk u idx).
Proof.
  intros Hready idx; unfold seg_busy_cut; apply solve_total_least; [exact seg_must_lub|].
  apply (seg_backward_system_monotone seg_must_lattice seg_must_laws);
    intros a Ha x y Hxy; unfold idx in *.
  rewrite (proj2 (build_expression_seg_summaries EN EE EU gk u Hready a x Ha)),
    (proj2 (build_expression_seg_summaries EN EE EU gk u Hready a y Ha)).
  apply seg_backward_monotone; [intros e He; apply seg_bit_monotone|exact Hxy].
Qed.

Local Lemma seg_absent_member {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) u (fact : avail_set EU gk) :
  ~ In u (expr_universe EU gk) -> fmem EU u fact = false.
Proof.
  intro Hnot; destruct (fmem EU u fact) eqn:Hmem; [|reflexivity].
  exfalso; apply Hnot; exact (proj2 (proj2_sig fact) u Hmem).
Qed.

(** Reconstructed sparse availability equals every least dense fact at every original point. *)
Theorem seg_available_exact {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  least_solution (avail_lattice EU gk) (available_system EU gk) sigma ->
  forall n u, In n (Graph.nodes (cfg (gkview gk))) ->
    seg_available EN EE EU gk u n = fmem EU u (sigma n).
Proof.
  intros Hready Hleast n u Hn; unfold seg_available.
  destruct (FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk))) eqn:Hmember.
  - pose proof (proj1 (FinSet.of_list_spec EU u _) Hmember) as Hu.
    set (idx := build_expression_seg EN EE EU gk u).
    set (cut := seg_available_cut EN EE EU gk u idx).
    change (seg_reconstruct_available EN EE idx (seg_bit_transfer EU gk u) cut n =
      fmem EU u (sigma n)).
    pose proof (seg_available_cut_least EN EE EU gk u Hready) as Hcut.
    fold idx in Hcut; fold cut in Hcut.
    pose proof (seg_available_project EU gk u sigma Hu (proj1 Hleast)) as Hproject.
    pose proof (seg_restrict_available EN EE EU gk u Hready _ Hproject) as Hrestrict.
    pose proof (proj2 Hcut _ Hrestrict) as Hcutbelow.
    pose proof (seg_available_compare EN EE EU gk u Hready _ cut Hproject
      (fun m _ => Hcutbelow m) n Hn) as Hcompare.
    pose proof (seg_available_lift EU gk u _
      (seg_reconstructed_available_post EN EE EU gk u Hready cut (proj1 Hcut))) as Hlift.
    pose proof (proj2 Hleast _ Hlift n) as Hdensebelow.
    apply seg_bool_equal; split.
    + intro Hr; apply (set_member_subset EU _ _ Hdensebelow u).
      change (fmem EU u (seg_lift_bit EU gk u
        (seg_reconstruct_available EN EE idx (seg_bit_transfer EU gk u) cut n)) = true).
      rewrite seg_lift_self by exact Hu; exact Hr.
    + exact (proj1 (seg_bool_le _ _) Hcompare).
  - symmetry; apply seg_absent_member; intro Hu.
    pose proof (proj2 (FinSet.of_list_spec EU u _) Hu); congruence.
Qed.

(** Reconstructed sparse anticipation equals every least dense fact, including closed SCCs. *)
Theorem seg_busy_exact {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  least_solution (avail_lattice EU gk) (busy_system EU gk) sigma ->
  forall n u, In n (Graph.nodes (cfg (gkview gk))) ->
    seg_busy EN EE EU gk u n = fmem EU u (sigma n).
Proof.
  intros Hready Hleast n u Hn; unfold seg_busy.
  destruct (FinSet.mem EU u (FinSet.of_list EU (expr_universe EU gk))) eqn:Hmember.
  - pose proof (proj1 (FinSet.of_list_spec EU u _) Hmember) as Hu.
    set (idx := build_expression_seg EN EE EU gk u).
    set (cut := seg_busy_cut EN EE EU gk u idx).
    change (seg_reconstruct_busy EN EE idx (seg_bit_transfer EU gk u) cut n =
      fmem EU u (sigma n)).
    pose proof (seg_busy_cut_least EN EE EU gk u Hready) as Hcut.
    fold idx in Hcut; fold cut in Hcut.
    pose proof (seg_busy_project EU gk u sigma Hu (proj1 Hleast)) as Hproject.
    pose proof (seg_restrict_busy EN EE EU gk u Hready _ Hproject) as Hrestrict.
    pose proof (proj2 Hcut _ Hrestrict) as Hcutbelow.
    pose proof (seg_busy_compare EN EE EU gk u Hready _ cut Hproject
      (fun m _ => Hcutbelow m) n Hn) as Hcompare.
    pose proof (seg_busy_lift EU gk u _
      (seg_reconstructed_busy_post EN EE EU gk u Hready cut (proj1 Hcut))) as Hlift.
    pose proof (proj2 Hleast _ Hlift n) as Hdensebelow.
    apply seg_bool_equal; split.
    + intro Hr; apply (set_member_subset EU _ _ Hdensebelow u).
      change (fmem EU u (seg_lift_bit EU gk u
        (seg_reconstruct_busy EN EE idx (seg_bit_transfer EU gk u) cut n)) = true).
      rewrite seg_lift_self by exact Hu; exact Hr.
    + exact (proj1 (seg_bool_le _ _) Hcompare).
  - symmetry; apply seg_absent_member; intro Hu.
    pose proof (proj2 (FinSet.of_list_spec EU u _) Hu); congruence.
Qed.
