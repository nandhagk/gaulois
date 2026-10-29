(** * Edgewise control dependence

    Each reversed edge contributes a stopped post-dominator-parent walk.
    For example, the two distinct branch edges of a diamond control their respective arms.
    Builds on: GraphFrontier and GraphPostDominators. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphPostDominators GraphFrontier.
Import List.ListNotations.

(** An edge controls nodes that post-dominate its target but not strictly its source. *)
Definition control_dependent {V E} (g : Graph.t V E) (exits : list V) (n : V) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ post_dominates g exits n (Graph.target g e) /\
  ~ (post_dominates g exits n (Graph.source g e) /\ n <> Graph.source g e).

(** Node control dependence existentially hides the identity of the controlling edge. *)
Definition cdep {V E} (g : Graph.t V E) (exits : list V) (b n : V) : Prop :=
  exists e, Graph.source g e = b /\ control_dependent g exits n e.

(** Every graph node has a finite path to one of the explicit exits. *)
Definition exits_reachable {V E} (g : Graph.t V E) (exits : list V) : Prop :=
  forall v, In v (Graph.nodes g) -> exists es x, path g v es x /\ In x exits.

Lemma control_reverse_reachable {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits v : ready EV g p -> exits_reachable g exits ->
  In v (Graph.nodes g) -> reachable (reverse_graph p exits) v.
Proof.
  intros Hready Hexit Hv; destruct (Hexit v Hv) as [es [x [Hpath Hx]]].
  apply reachable_iff_path; exists x, (rev es); split; [exact Hx|].
  apply path_reverse_forward; assumption.
Qed.

Lemma control_reverse_edge {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits e : ready EV g p -> incl exits (Graph.nodes g) ->
  exits_reachable g exits ->
  In (Graph.source g e) (Graph.nodes g) ->
  (In e (frontier_edges (prepared_reverse p exits)) <->
   In e (Graph.out g (Graph.source g e))).
Proof.
  intros Hready Hexits Hexit Hsource.
  unfold frontier_edges.
  split.
  - intro Hin; apply filter_In in Hin; destruct Hin as [Hin _].
    apply in_flat_map in Hin; destruct Hin as [v [Hv Hin]].
    change (In e (succ_edges p v)) in Hin.
    rewrite (succ_agrees (proj2 (proj2 Hready)) v Hv) in Hin.
    pose proof (out_source (proj1 Hready) v e Hin) as Heq; subst v; exact Hin.
  - intro Hedge.
    assert (Htarget : In (Graph.target g e) (Graph.nodes g)).
    { eapply out_target_in; [exact (proj1 Hready)|exact Hsource|exact Hedge]. }
    apply filter_In; split.
    + apply in_flat_map; exists (Graph.source g e); split; [exact Hsource|].
      change (In e (succ_edges p (Graph.source g e))).
      rewrite (succ_agrees (proj2 (proj2 Hready)) _ Hsource); exact Hedge.
    + change (FinSet.mem EV (Graph.target g e)
        (visited (dfs (prepared_reverse p exits) FinSet.empty exits)) = true).
      apply (proj2 (reachable_dfs EV (reverse_graph p exits) (prepared_reverse p exits)
        (Graph.target g e) (reverse_graph_ready EV g p exits Hready Hexits))).
      apply control_reverse_reachable; assumption.
Qed.

(** Preserve each controlling edge identity alongside every visited dependent node. *)
Definition control_events {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (exits : list V) (pt : dom_tree V) : list (V * E) :=
  let rp := prepared_reverse p exits in
  flat_map (fun e => map (fun n => (n, e))
    (frontier_runner rp pt (Graph.target g e) (Map.get EV (Graph.source g e) (idom pt))))
    (frontier_edges rp).

Definition control_at {V E} (EV : encoding V) (m : Map.t V (list E)) (n : V) (e : E) : Prop :=
  exists l, Map.get EV n m = Some l /\ In e l.

Definition control_add {V E} (EV : encoding V) (m : Map.t V (list E))
    (event : V * E) : Map.t V (list E) :=
  let '(n, e) := event in
  Map.set EV n (e :: match Map.get EV n m with Some l => l | None => [] end) m.

Lemma control_add_spec {V E} (EV : encoding V) (m : Map.t V (list E)) x a n e :
  control_at EV (control_add EV m (x, a)) n e <->
  (n = x /\ e = a) \/ control_at EV m n e.
Proof.
  unfold control_at, control_add; destruct (dfs_eq_dec EV n x) as [Heq|Hne].
  - subst x; rewrite Map.get_set_same.
    destruct (Map.get EV n m) as [old|] eqn:Hget.
    + split.
      * intros [l [Heq Hin]]; inversion Heq; subst l; destruct Hin as [Hsame|Hin].
        -- left; auto.
        -- right; exists old; auto.
      * intros [[_ Hsame]|[l [Heq Hin]]].
        -- subst e; exists (a :: old); split; [reflexivity|left; reflexivity].
        -- inversion Heq; subst l; exists (a :: old); split; [reflexivity|right; exact Hin].
    + split.
      * intros [l [Heq Hin]]; inversion Heq; subst l; destruct Hin as [Hsame|Hfalse].
        -- left; auto.
        -- contradiction.
      * intros [[_ Hsame]|[l [Hfalse _]]]; [subst e|discriminate].
        exists [a]; split; [reflexivity|left; reflexivity].
  - rewrite Map.get_set_other by exact Hne.
    split; [intro H; right; exact H|intros [[Heq _]|H]; [contradiction|exact H]].
Qed.

Lemma control_fold_spec {V E} (EV : encoding V) (events : list (V * E)) m n e :
  control_at EV (fold_left (control_add EV) events m) n e <->
  In (n, e) events \/ control_at EV m n e.
Proof.
  revert m; induction events as [|[x a] rest IH]; intro m; cbn [fold_left].
  - cbn [In]; tauto.
  - rewrite IH, control_add_spec; cbn [In].
    split.
    + intros [Hin|[[Heq Heq']|Hmem]]; [left; right; exact Hin|left; left; congruence|auto].
    + intros [[Heq|Hin]|Hmem].
      * inversion Heq; subst; right; left; auto.
      * left; exact Hin.
      * right; right; exact Hmem.
Qed.

(** Index reverse-frontier edge visits by the dependent node. *)
Definition control_deps {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (exits : list V) (pt : dom_tree V) : Map.t V (list E) :=
  fold_left (control_add EV) (control_events p exits pt) Map.empty.

Lemma control_runner_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits e n : ready EV g p -> incl exits (Graph.nodes g) ->
  exits_reachable g exits -> dominator_exact (prepared_reverse p exits) = true ->
  In (Graph.source g e) (Graph.nodes g) -> In e (Graph.out g (Graph.source g e)) ->
  (In n (frontier_runner (prepared_reverse p exits) (post_dominator_tree p exits)
    (Graph.target g e) (Map.get EV (Graph.source g e) (idom (post_dominator_tree p exits)))) <->
   post_dominates g exits n (Graph.target g e) /\
   ~ (post_dominates g exits n (Graph.source g e) /\ n <> Graph.source g e)).
Proof.
  intros Hready Hexits Hexit Hcheck Hsource Hedge.
  assert (Htarget : In (Graph.target g e) (Graph.nodes g)).
  { eapply out_target_in; [exact (proj1 Hready)|exact Hsource|exact Hedge]. }
  assert (Hredge : In e (Graph.out (reverse_graph p exits)
    (Graph.source (reverse_graph p exits) e))).
  { cbn [reverse_graph]; apply (pred_agrees (proj2 (proj2 Hready)) _ e Htarget).
    exists (Graph.source g e); auto. }
  pose proof (frontier_runner_edge_exact EV (reverse_graph p exits)
    (prepared_reverse p exits) e n (reverse_graph_ready EV g p exits Hready Hexits)
    Hcheck Hredge (control_reverse_reachable EV g p exits (Graph.target g e)
      Hready Hexit Htarget)) as Hrunner.
  change (In n (frontier_runner (prepared_reverse p exits) (post_dominator_tree p exits)
    (Graph.target g e) (Map.get EV (Graph.source g e) (idom (post_dominator_tree p exits)))) <->
    dominates (reverse_graph p exits) n (Graph.target g e) /\
    ~ strictly_dominates (reverse_graph p exits) n (Graph.source g e)) in Hrunner.
  rewrite Hrunner; unfold strictly_dominates.
  rewrite <- (post_dominates_iff_reverse EV g p n (Graph.target g e) exits
    Hready Hexits Htarget).
  rewrite <- (post_dominates_iff_reverse EV g p n (Graph.source g e) exits
    Hready Hexits Hsource); reflexivity.
Qed.

Lemma control_events_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits e n : ready EV g p -> incl exits (Graph.nodes g) ->
  exits_reachable g exits -> dominator_exact (prepared_reverse p exits) = true ->
  In (Graph.source g e) (Graph.nodes g) ->
  (In (n, e) (control_events p exits (post_dominator_tree p exits)) <->
   control_dependent g exits n e).
Proof.
  intros Hready Hexits Hexit Hcheck Hsource; unfold control_events, control_dependent.
  rewrite in_flat_map; split.
  - intros [a [Ha Hin]]; apply in_map_iff in Hin; destruct Hin as [d [Heq Hin]].
    inversion Heq; subst a d.
    apply (control_reverse_edge EV g p exits e Hready Hexits Hexit Hsource) in Ha.
    split; [exact Ha|].
    apply (control_runner_exact EV g p exits e n Hready Hexits Hexit Hcheck Hsource Ha);
      exact Hin.
  - intros [Hedge Hdom]; exists e; split.
    + apply (control_reverse_edge EV g p exits e Hready Hexits Hexit Hsource); exact Hedge.
    + apply in_map_iff; exists n; split; [reflexivity|].
      apply (control_runner_exact EV g p exits e n Hready Hexits Hexit Hcheck Hsource Hedge);
        exact Hdom.
Qed.

(** Control dependence is the post-dominance frontier, edge by edge, for an exact tree. *)
Theorem control_deps_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (n : V) (e : E) (exits : list V) :
  ready EV g p -> incl exits (Graph.nodes g) -> exits_reachable g exits ->
  dominator_exact (prepared_reverse p exits) = true -> In n (Graph.nodes g) ->
  In (Graph.source g e) (Graph.nodes g) ->
  ((exists l, Map.get EV n (control_deps p exits (post_dominator_tree p exits)) = Some l /\
    In e l) <-> control_dependent g exits n e).
Proof.
  intros Hready Hexits Hexit Hcheck Hn Hsource.
  change (control_at EV (control_deps p exits (post_dominator_tree p exits)) n e <->
    control_dependent g exits n e).
  unfold control_deps; rewrite control_fold_spec.
  rewrite (control_events_exact EV g p exits e n Hready Hexits Hexit Hcheck Hsource).
  unfold control_at; rewrite Map.get_empty; split; [intros [H|[l [Hfalse _]]]|];
    try discriminate; auto.
Qed.
