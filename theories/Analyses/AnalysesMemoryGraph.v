(** * Whole-memory versions and dynamic provenance

    Local graph laws connect structural versions to actual ordered edge histories.
    For example, a read/write consumes its incoming version before defining its own version.
    Builds on: GraphCore, ViewsGraph, ViewsSemantics and ViewsMemoryEffects. *)

From Stdlib Require Import List Arith Lia.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
Import List.ListNotations.

(** Definitions retain both the edge identity and its ordered effect position. *)
Inductive memory_version (N E : Type) : Type :=
  | MemoryLive
  | MemoryPhi (node : N)
  | MemoryDef (edge : E) (index : nat).

Arguments MemoryLive {N E}.
Arguments MemoryPhi {N E}.
Arguments MemoryDef {N E}.

(** A finite inventory accompanies node inputs, occurrence inputs and exact-edge operands. *)
Record memory_graph (N E : Type) : Type := MemoryGraph {
  memory_phis : list N;
  memory_versions : list (memory_version N E);
  memory_in : N -> memory_version N E;
  memory_before : E -> nat -> option (memory_version N E);
  memory_out : E -> memory_version N E;
  memory_operand : N -> option E -> option (memory_version N E)
}.

Arguments MemoryGraph {N E}.
Arguments memory_phis {N E}.
Arguments memory_versions {N E}.
Arguments memory_in {N E}.
Arguments memory_before {N E}.
Arguments memory_out {N E}.
Arguments memory_operand {N E}.

(** An occurrence is an in-range effect of a listed edge with reachable source. *)
Definition memory_occurrence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (e : E) (i : nat) (a : memory_effect T) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
  nth_error (effects e) i = Some a.

(** Phi membership is represented by the finite node inventory. *)
Definition memory_phi_at {N E} (mg : memory_graph N E) (n : N) : Prop :=
  In n (memory_phis mg).

(** Live-on-entry exists even for an empty graph; other versions need reachable witnesses. *)
Definition memory_valid_version {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (v : memory_version N E) : Prop :=
  match v with
  | MemoryLive => True
  | MemoryPhi n => reachable g n /\ memory_phi_at mg n
  | MemoryDef e i => exists a, memory_occurrence g effects e i a /\ effect_is_def a = true
  end.

(** An effect defines its output after consuming its input. *)
Definition memory_after {N E T} (e : E) (i : nat) (a : memory_effect T)
    (v : memory_version N E) : memory_version N E :=
  if effect_is_def a then MemoryDef e i else v.

(** Each occurrence lookup records the version immediately before that ordered effect. *)
Inductive memory_edge_flow {N E T} (mg : memory_graph N E) (e : E) :
    nat -> list (memory_effect T) -> memory_version N E -> memory_version N E -> Prop :=
  | memory_edge_nil : forall i v, memory_edge_flow mg e i [] v v
  | memory_edge_cons : forall i a rest v w,
      memory_before mg e i = Some v ->
      memory_edge_flow mg e (S i) rest (memory_after e i a v) w ->
      memory_edge_flow mg e i (a :: rest) v w.

(** Arrival either selects the actual incoming phi operand or preserves the incoming version. *)
Definition memory_arrival {N E} (mg : memory_graph N E) (n : N) (key : option E)
    (v : memory_version N E) : Prop :=
  (memory_phi_at mg n /\ memory_operand mg n key = Some v /\ memory_in mg n = MemoryPhi n) \/
  (~ memory_phi_at mg n /\ memory_in mg n = v).

(** Well-formedness imposes only local flow, inventory and incoming-edge obligations. *)
Record memory_graph_wf {N E T} (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) : Prop := {
  memory_cfg_wf : graph_wf g;
  memory_phis_nodup : NoDup (memory_phis mg);
  memory_phi_reachable : forall n, memory_phi_at mg n -> reachable g n;
  memory_versions_nodup : NoDup (memory_versions mg);
  memory_versions_exact : forall v, In v (memory_versions mg) <->
    memory_valid_version g effects mg v;
  memory_entries_arrive : forall n, In n (Graph.entries g) ->
    memory_arrival mg n None MemoryLive;
  memory_edges_flow : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) ->
    memory_edge_flow mg e 0 (effects e) (memory_in mg (Graph.source g e)) (memory_out mg e);
  memory_edges_arrive : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) ->
    memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e);
  memory_in_valid : forall n, reachable g n ->
    memory_valid_version g effects mg (memory_in mg n);
  memory_out_valid : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) -> memory_valid_version g effects mg (memory_out mg e);
  memory_before_domain : forall e i,
    (exists v, memory_before mg e i = Some v) <->
    exists a, memory_occurrence g effects e i a;
  memory_operand_domain : forall n k,
    (exists v, memory_operand mg n k = Some v) <->
    memory_phi_at mg n /\
    match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end
}.

Arguments memory_cfg_wf {N E T g effects mg}.
Arguments memory_phis_nodup {N E T g effects mg}.
Arguments memory_phi_reachable {N E T g effects mg}.
Arguments memory_versions_nodup {N E T g effects mg}.
Arguments memory_versions_exact {N E T g effects mg}.
Arguments memory_entries_arrive {N E T g effects mg}.
Arguments memory_edges_flow {N E T g effects mg}.
Arguments memory_edges_arrive {N E T g effects mg}.
Arguments memory_in_valid {N E T g effects mg}.
Arguments memory_out_valid {N E T g effects mg}.
Arguments memory_before_domain {N E T g effects mg}.
Arguments memory_operand_domain {N E T g effects mg}.

(** Path flow retains the operand selected by every actual edge of a path. *)
Inductive memory_path_flow {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    N -> list E -> N -> Prop :=
  | memory_path_nil : forall n, memory_path_flow g effects mg n [] n
  | memory_path_cons : forall e es n,
      In e (Graph.out g (Graph.source g e)) ->
      memory_edge_flow mg e 0 (effects e) (memory_in mg (Graph.source g e)) (memory_out mg e) ->
      memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e) ->
      memory_path_flow g effects mg (Graph.target g e) es n ->
      memory_path_flow g effects mg (Graph.source g e) (e :: es) n.

(** Scanning a finite edge prefix retains its last definition and otherwise the supplied origin. *)
Fixpoint memory_last_defs {N E T} (e : E) (i : nat) (effects : list (memory_effect T))
    (origin : memory_version N E) : memory_version N E :=
  match effects with
  | [] => origin
  | a :: rest => memory_last_defs e (S i) rest (memory_after e i a origin)
  end.

(** The dynamic origin follows all visits in their actual order, starting at live-on-entry. *)
Definition memory_last_path {N E T} (effects : E -> list (memory_effect T)) (es : list E) :
    memory_version N E :=
  fold_left (fun origin e => memory_last_defs e 0 (effects e) origin) es MemoryLive.

(** Edge provenance advances static versions and dynamic origins through the same effects. *)
Inductive memory_edge_provenance {N E T} (mg : memory_graph N E) (e : E) :
    nat -> list (memory_effect T) -> memory_version N E -> memory_version N E ->
    memory_version N E -> memory_version N E -> Prop :=
  | memory_edge_provenance_nil : forall i input origin,
      memory_edge_provenance mg e i [] input origin input origin
  | memory_edge_provenance_cons : forall i a rest input origin output last,
      memory_before mg e i = Some input ->
      memory_edge_provenance mg e (S i) rest (memory_after e i a input)
        (memory_after e i a origin) output last ->
      memory_edge_provenance mg e i (a :: rest) input origin output last.

(** Provenance keeps the full path, including revisits and the selected incoming phi operand. *)
Inductive memory_provenance {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (root : N) :
    list E -> N -> memory_version N E -> memory_version N E -> Prop :=
  | memory_provenance_entry : In root (Graph.entries g) ->
      memory_arrival mg root None MemoryLive ->
      memory_provenance g effects mg root [] root (memory_in mg root) MemoryLive
  | memory_provenance_edge : forall es e origin last,
      memory_provenance g effects mg root es (Graph.source g e)
        (memory_in mg (Graph.source g e)) origin ->
      In e (Graph.out g (Graph.source g e)) ->
      memory_edge_provenance mg e 0 (effects e) (memory_in mg (Graph.source g e)) origin
        (memory_out mg e) last ->
      memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e) ->
      memory_provenance g effects mg root (es ++ [e]) (Graph.target g e)
        (memory_in mg (Graph.target g e)) last.

(** An occurrence couples its lookup and static prefix with the exact dynamic last definition. *)
Definition memory_occurrence_history {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (es : list E) (e : E) (i : nat)
    (input origin : memory_version N E) : Prop :=
  memory_before mg e i = Some input /\
  memory_edge_provenance mg e 0 (firstn i (effects e)) (memory_in mg (Graph.source g e))
    (memory_last_path effects es) input origin /\
  origin = memory_last_defs e 0 (firstn i (effects e)) (memory_last_path effects es).

Lemma memory_reachable_path_flow {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (Hwf : memory_graph_wf g effects mg) u es n :
  path g u es n -> reachable g u -> memory_path_flow g effects mg u es n.
Proof.
  intro Hpath; induction Hpath as [n|e es n Hedge Hpath IH]; intro Hreachable.
  - constructor.
  - constructor.
    + exact Hedge.
    + apply (memory_edges_flow Hwf); assumption.
    + apply (memory_edges_arrive Hwf); assumption.
    + apply IH; eapply reachable_step; eassumption.
Qed.

(** Local graph laws cover every entry-rooted path without a producer-specific path premise. *)
Theorem memory_path_correspondence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival mg root None MemoryLive /\ memory_path_flow g effects mg root es n.
Proof.
  intros Hwf root es n Hentry Hpath; split.
  - apply (memory_entries_arrive Hwf); exact Hentry.
  - eapply memory_reachable_path_flow; [exact Hwf|exact Hpath|].
    constructor; exact Hentry.
Qed.

Lemma memory_edge_flow_input_valid {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) e start
    (xs : list (memory_effect T)) input output :
  memory_edge_flow mg e start xs input output ->
  memory_valid_version g effects mg input ->
  (forall j a, nth_error xs j = Some a -> effect_is_def a = true ->
    memory_valid_version g effects mg (MemoryDef e (start + j))) ->
  forall j a, nth_error xs j = Some a -> exists v,
    memory_before mg e (start + j) = Some v /\ memory_valid_version g effects mg v.
Proof.
  intro Hflow; induction Hflow as [start input|start a xs input output Hbefore Hflow IH];
    intros Hvalid Hdefs j observed Hnth.
  - destruct j; discriminate.
  - destruct j as [|j].
    + cbn in Hnth; inversion Hnth; subst observed.
      rewrite Nat.add_0_r; exists input; split; assumption.
    + replace (start + S j) with (S start + j) by lia.
      refine (IH _ _ j observed Hnth).
      * unfold memory_after; destruct (effect_is_def a) eqn:Hdef; [|exact Hvalid].
        replace start with (start + 0) by lia; eapply Hdefs; [reflexivity|exact Hdef].
      * intros k next Hnext Hdef.
        replace (S start + k) with (start + S k) by lia.
        eapply Hdefs; [exact Hnext|exact Hdef].
Qed.

(** Every occurrence has a valid incoming version, and defining occurrences are inventoried. *)
Theorem memory_occurrence_input_valid {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall e i a, memory_occurrence g effects e i a -> exists v,
    memory_before mg e i = Some v /\ memory_valid_version g effects mg v /\
    (effect_is_def a = true -> In (MemoryDef e i) (memory_versions mg)).
Proof.
  intros Hwf e i a [Hedge [Hreachable Hnth]].
  assert (Hdefs : forall j observed, nth_error (effects e) j = Some observed ->
    effect_is_def observed = true ->
    memory_valid_version g effects mg (MemoryDef e (0 + j))).
  { intros j observed Hfound Hdef; exists observed; split; [|exact Hdef].
    split; [exact Hedge|split; assumption]. }
  destruct (memory_edge_flow_input_valid g effects mg e 0 (effects e)
    (memory_in mg (Graph.source g e)) (memory_out mg e)
    (memory_edges_flow Hwf e Hedge Hreachable) (memory_in_valid Hwf _ Hreachable)
    Hdefs i a Hnth)
    as [v [Hbefore Hvalid]].
  exists v; split; [exact Hbefore|split; [exact Hvalid|]].
  intro Hdef; apply (memory_versions_exact Hwf); exists a; split; [|exact Hdef].
  split; [exact Hedge|split; assumption].
Qed.

Lemma memory_edge_flow_provenance {N E T} (mg : memory_graph N E) e start
    (xs : list (memory_effect T)) input output :
  memory_edge_flow mg e start xs input output -> forall origin,
    memory_edge_provenance mg e start xs input origin output
      (memory_last_defs e start xs origin).
Proof.
  intro Hflow; induction Hflow as [start input|start a xs input output Hbefore Hflow IH];
    intro origin.
  - constructor.
  - cbn [memory_last_defs]; constructor; [exact Hbefore|apply IH].
Qed.

Lemma memory_provenance_reachable {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) root es n input origin :
  memory_provenance g effects mg root es n input origin -> reachable g n.
Proof.
  intro Hprovenance; induction Hprovenance as
    [Hentry Harrival|es e origin last Hprefix IH Hedge Hflow Harrival].
  - constructor; exact Hentry.
  - eapply reachable_step; eassumption.
Qed.

Lemma memory_path_provenance {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (Hwf : memory_graph_wf g effects mg) u es n :
  path g u es n -> forall root prefix origin,
  memory_provenance g effects mg root prefix u (memory_in mg u) origin ->
  memory_provenance g effects mg root (prefix ++ es) n (memory_in mg n)
    (fold_left (fun current e => memory_last_defs e 0 (effects e) current) es origin).
Proof.
  intro Hpath; induction Hpath as [n|e es n Hedge Hpath IH];
    intros root prefix origin Hprefix.
  - cbn; rewrite app_nil_r; exact Hprefix.
  - pose proof (memory_provenance_reachable g effects mg root prefix _ _ _ Hprefix)
      as Hreachable.
    pose proof (memory_edge_flow_provenance mg e 0 (effects e) _ _
      (memory_edges_flow Hwf e Hedge Hreachable) origin) as Hflow.
    assert (Hnext : memory_provenance g effects mg root (prefix ++ [e]) (Graph.target g e)
      (memory_in mg (Graph.target g e)) (memory_last_defs e 0 (effects e) origin)).
    { eapply memory_provenance_edge.
      - exact Hprefix.
      - exact Hedge.
      - exact Hflow.
      - apply (memory_edges_arrive Hwf); assumption. }
    specialize (IH root (prefix ++ [e]) _ Hnext).
    rewrite <- app_assoc in IH; cbn in IH; exact IH.
Qed.

Lemma memory_edge_flow_prefix {N E T} (mg : memory_graph N E) e start
    (xs : list (memory_effect T)) input output :
  memory_edge_flow mg e start xs input output -> forall j a origin,
    nth_error xs j = Some a -> exists before,
    memory_before mg e (start + j) = Some before /\
    memory_edge_provenance mg e start (firstn j xs) input origin before
      (memory_last_defs e start (firstn j xs) origin).
Proof.
  intro Hflow; induction Hflow as [start input|start a xs input output Hbefore Hflow IH];
    intros j observed origin Hnth.
  - destruct j; discriminate.
  - destruct j as [|j].
    + rewrite Nat.add_0_r; exists input; split; [exact Hbefore|constructor].
    + destruct (IH j observed (memory_after e start a origin) Hnth)
        as [before [Hlookup Hprefix]].
      exists before; split.
      * replace (start + S j) with (S start + j) by lia; exact Hlookup.
      * cbn [firstn memory_last_defs]; constructor; assumption.
Qed.

(** The same actual path and edge prefix determine the last dynamic definition before each use. *)
Theorem memory_definition_before_occurrence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin,
    memory_provenance g effects mg root es (Graph.source g e)
      (memory_in mg (Graph.source g e)) (memory_last_path effects es) /\
    memory_occurrence_history g effects mg es e i input origin.
Proof.
  intros Hwf root es e i a Hentry Hpath [Hedge [Hreachable Hnth]].
  assert (Hentry_provenance : memory_provenance g effects mg root [] root
    (memory_in mg root) MemoryLive).
  { constructor; [exact Hentry|apply (memory_entries_arrive Hwf); exact Hentry]. }
  pose proof (memory_path_provenance g effects mg Hwf _ _ _ Hpath root [] MemoryLive
    Hentry_provenance) as Hprovenance.
  destruct (memory_edge_flow_prefix mg e 0 (effects e) _ _
    (memory_edges_flow Hwf e Hedge Hreachable) i a (memory_last_path effects es) Hnth)
    as [input [Hbefore Hprefix]].
  exists input, (memory_last_defs e 0 (firstn i (effects e)) (memory_last_path effects es)).
  split; [exact Hprovenance|].
  split; [exact Hbefore|split; [exact Hprefix|reflexivity]].
Qed.

(** An initial semantic execution follows the memory flow of its exact graph-edge history. *)
Theorem memory_execution_correspondence {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) (mg : memory_graph N E) :
  memory_effect_laws m v ->
  memory_graph_wf (cfg (effect_graph v)) (edge_effects v) mg ->
  forall s es t, initial m s -> run_edges m (effect_graph v) s es t ->
    memory_arrival mg (point (effect_graph v) s) None MemoryLive /\
    memory_path_flow (cfg (effect_graph v)) (edge_effects v) mg
      (point (effect_graph v) s) es (point (effect_graph v) t).
Proof.
  intros Hlaws Hwf s es t Hinitial Hrun.
  apply (memory_path_correspondence _ _ _ Hwf).
  - apply (entry_points (effect_view_laws Hlaws)); exact Hinitial.
  - eapply run_edges_path; [apply (effect_view_laws Hlaws)| |exact Hrun].
    exists s, []; split; [exact Hinitial|constructor].
Qed.
