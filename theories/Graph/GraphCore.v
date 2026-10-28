(** * Graphs and paths

    Finite node lists describe edge-labelled graphs and their paths.
    For example, a path with no edges connects a node to itself.
    Builds on: Collections encodings and finite sets. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
Import List.ListNotations.

(** * Graph representation *)

Module Graph.

(** A graph supplies entries, nodes and labelled outgoing edges. *)
Record t (V E : Type) : Type := Make {
  entries : list V;
  nodes : list V;
  out : V -> list E;
  source : E -> V;
  target : E -> V
}.
Arguments Make {V E}.
Arguments entries {V E}.
Arguments nodes {V E}.
Arguments out {V E}.
Arguments source {V E}.
Arguments target {V E}.

End Graph.

(** Reachable nodes are entries or targets of edges from reachable nodes. *)
Inductive reachable {V E} (g : Graph.t V E) : V -> Prop :=
  | reachable_entry : forall v, In v (Graph.entries g) -> reachable g v
  | reachable_step : forall e, reachable g (Graph.source g e) ->
      In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.target g e).
Arguments reachable_entry {V E g} v _.
Arguments reachable_step {V E g} e _ _.

(** Well-formed graphs have distinct nodes and closed, correctly sourced edges. *)
Record graph_wf {V E} (g : Graph.t V E) : Prop := {
  nodes_nodup : NoDup (Graph.nodes g);
  entries_in : forall v, In v (Graph.entries g) -> In v (Graph.nodes g);
  out_source : forall v e, In e (Graph.out g v) -> Graph.source g e = v;
  out_target_in : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    In (Graph.target g e) (Graph.nodes g)
}.
Arguments Build_graph_wf {V E g} _ _ _ _.
Arguments nodes_nodup {V E g} _.
Arguments entries_in {V E g} _ v _.
Arguments out_source {V E g} _ v e _.
Arguments out_target_in {V E g} _ v e _ _.

(** A path is a sequence of edges joined at their endpoints. *)
Inductive path {V E} (g : Graph.t V E) : V -> list E -> V -> Prop :=
  | path_nil : forall v, path g v [] v
  | path_cons : forall e es w, In e (Graph.out g (Graph.source g e)) ->
      path g (Graph.target g e) es w -> path g (Graph.source g e) (e :: es) w.
Arguments path_nil {V E g} v.
Arguments path_cons {V E g} e es w _ _.

(** Reachability between two nodes means that some path connects them. *)
Definition reaches {V E} (g : Graph.t V E) (u v : V) : Prop := exists es, path g u es v.

(** Mutual reachability requires paths in both directions. *)
Definition mutual {V E} (g : Graph.t V E) (u v : V) : Prop :=
  reaches g u v /\ reaches g v u.

(** An acyclic graph has no nonempty path from a listed node to itself. *)
Definition acyclic {V E} (g : Graph.t V E) : Prop :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es = [].

(** One element occurs strictly before another in a list. *)
Definition before {A} (l : list A) (u v : A) : Prop :=
  exists l1 l2 l3, l = l1 ++ u :: l2 ++ v :: l3.

(** Replace the entries without changing the graph's edges. *)
Definition set_entries {V E} (g : Graph.t V E) (roots : list V) : Graph.t V E :=
  {| Graph.entries := roots; Graph.nodes := Graph.nodes g; Graph.out := Graph.out g;
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.

(** Remove listed blocked nodes and edges entering them. *)
Definition without {V E} (EV : encoding V) (blocked : FinSet.t V) (g : Graph.t V E)
    : Graph.t V E :=
  {| Graph.entries := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.entries g);
     Graph.nodes := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => negb (FinSet.mem EV (Graph.target g e) blocked))
       (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.

(** Keep selected nodes and edges entering them, with no entries. *)
Definition induced {V E} (EV : encoding V) (keep : FinSet.t V) (g : Graph.t V E)
    : Graph.t V E :=
  {| Graph.entries := []; Graph.nodes := filter (fun v => FinSet.mem EV v keep) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => FinSet.mem EV (Graph.target g e) keep) (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.

(** Count outgoing edges over the node list. *)
Definition edge_count {V E} (g : Graph.t V E) : nat :=
  fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).

(** * Reachability laws *)

Lemma path_snoc {V E} (g : Graph.t V E) u es v e :
  path g u es v -> v = Graph.source g e -> In e (Graph.out g v) ->
  path g u (es ++ [e]) (Graph.target g e).
Proof.
  intros Hpath; induction Hpath as [v|a es w Hedge Hpath IH]; intros Heq Hin.
  - subst v; simpl; constructor; [exact Hin|constructor].
  - simpl; constructor; [exact Hedge|]. apply IH; assumption.
Qed.

(** Reachability holds exactly for endpoints of paths from entries. *)
Theorem reachable_iff_path {V E} (g : Graph.t V E) (v : V) :
  reachable g v <-> exists s es, In s (Graph.entries g) /\ path g s es v.
Proof.
  split.
  - intro Hreach; induction Hreach as [v Hin|e Hreach IH Hedge].
    + exists v, []; split; [exact Hin|constructor].
    + destruct IH as [s [es [Hin Hpath]]]. exists s, (es ++ [e]); split; [exact Hin|].
      eapply path_snoc; eauto.
  - intros [s [es [Hin Hpath]]].
    assert (Hstart : reachable g s) by (constructor; exact Hin).
    clear Hin; induction Hpath as [v|e es w Hedge Hpath IH]; [exact Hstart|].
    apply IH. eapply reachable_step; eauto.
Qed.

(** A reachable node belongs to the node list of a well-formed graph. *)
Theorem reachable_in_nodes {V E} (g : Graph.t V E) (v : V) :
  graph_wf g -> reachable g v -> In v (Graph.nodes g).
Proof.
  intros Hwf Hreach; induction Hreach as [v Hin|e Hreach IH Hedge].
  - eapply entries_in; eauto.
  - eapply out_target_in; eauto.
Qed.
