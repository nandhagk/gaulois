(** * Natural loops by a stopped reverse search

    A natural loop contains its header and the nodes that reach its tail without the header.
    For example, for a back edge 3 to 2, the reverse search starts at 3 and stops at 2.
    Builds on: GraphCore, GraphPrepare, GraphDfs and GraphDominance. *)

From Stdlib Require Import List Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance.
Import List.ListNotations.

(** The header is included explicitly; all other members can reach the tail avoiding the header. *)
Definition natural_loop {V E} (EV : encoding V) (g : Graph.t V E) (e : E) (n : V) : Prop :=
  n = Graph.target g e \/
  exists es, path (without EV (FinSet.add EV (Graph.target g e) FinSet.empty) g)
    n es (Graph.source g e).

(** Reuse the prepared predecessor index for one search stopped at the header. *)
Definition natural_loop_nodes {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (e : E) : FinSet.t V :=
  let header := Graph.target g e in
  let tail := Graph.source g e in
  FinSet.add EV header (visited (dfs (prepared_reverse p [tail])
    (FinSet.add EV header FinSet.empty) [tail])).

Section NaturalLoops.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).

Lemma natural_loop_sources_free (q : Graph.t V E) blocked u es v :
  path q u es v -> FinSet.mem EV u blocked = false ->
  (forall e, In e es -> FinSet.mem EV (Graph.target q e) blocked = false) ->
  forall e, In e es -> FinSet.mem EV (Graph.source q e) blocked = false.
Proof.
  intro Hpath; induction Hpath as [v|a es v Hedge Hpath IH]; intros Hu Htargets e Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; exact Hu.
    + apply IH; [apply Htargets; left; reflexivity| |exact Hin].
      intros b Hb; apply Htargets; right; exact Hb.
Qed.

Lemma natural_loop_endpoint_free (q : Graph.t V E) blocked u es v :
  path (without EV blocked q) u es v -> FinSet.mem EV u blocked = false ->
  FinSet.mem EV v blocked = false.
Proof.
  intros Hpath Hu; apply path_without in Hpath; destruct Hpath as [Hpath Htargets].
  destruct (path_endpoint q u es v Hpath) as [Heq|[e [Hin Heq]]].
  - subst v; exact Hu.
  - rewrite <- Heq; apply Htargets; exact Hin.
Qed.

Lemma natural_loop_reverse_avoiding blocked u es v :
  ready EV g p -> In u (Graph.nodes g) -> In v (Graph.nodes g) ->
  FinSet.mem EV u blocked = false -> FinSet.mem EV v blocked = false ->
  (path (without EV blocked g) u es v <->
   path (without EV blocked (reverse_graph p [v])) v (rev es) u).
Proof.
  intros Hready Hu Hv Hufree Hvfree; rewrite !path_without; split.
  - intros [Hpath Htargets]; split.
    + apply (proj1 (reverse_path EV g p u v es [v] Hready Hu Hv)); exact Hpath.
    + intros e Hin; cbn [Graph.target].
      apply (natural_loop_sources_free g blocked u es v Hpath Hufree Htargets e).
      apply (proj2 (in_rev es e)); exact Hin.
  - intros [Hpath Htargets]; split.
    + apply (proj2 (reverse_path EV g p u v es [v] Hready Hu Hv)); exact Hpath.
    + intros e Hin.
      apply (natural_loop_sources_free (reverse_graph p [v]) blocked v (rev es) u
        Hpath Hvfree Htargets e).
      apply (proj1 (in_rev es e)); exact Hin.
Qed.

Lemma natural_loop_search e x : ready EV g p ->
  In (Graph.source g e) (Graph.nodes g) -> In x (Graph.nodes g) ->
  x <> Graph.target g e ->
  (FinSet.mem EV x (visited (dfs (prepared_reverse p [Graph.source g e])
      (FinSet.add EV (Graph.target g e) FinSet.empty) [Graph.source g e])) = true <->
   exists es, path (without EV (FinSet.add EV (Graph.target g e) FinSet.empty) g)
     x es (Graph.source g e)).
Proof.
  intros Hready Htail Hx Hnotheader.
  set (blocked := FinSet.add EV (Graph.target g e) FinSet.empty).
  assert (Hroots : incl [Graph.source g e] (Graph.nodes g)).
  { intros v [Heq|Hin]; [subst v; exact Htail|contradiction]. }
  pose proof (reverse_graph_ready EV g p [Graph.source g e] Hready Hroots) as Hreverse.
  destruct (dfs_exact EV (reverse_graph p [Graph.source g e])
    (prepared_reverse p [Graph.source g e]) x [Graph.source g e] blocked Hreverse Hroots)
    as [Hexact _].
  rewrite Hexact.
  change (reachable (without EV blocked (reverse_graph p [Graph.source g e])) x <->
    exists es, path (without EV blocked g) x es (Graph.source g e)).
  assert (Hxfree : FinSet.mem EV x blocked = false).
  { apply singleton_absent; exact Hnotheader. }
  split.
  - intro Hreach; apply reachable_without in Hreach.
    destruct Hreach as [s [es [Hentry [Hpath [Hsfree Htargets]]]]].
    cbn [Graph.entries] in Hentry; destruct Hentry as [Heq|Hin]; [subst s|contradiction].
    exists (rev es).
    apply (proj2 (natural_loop_reverse_avoiding blocked x (rev es) (Graph.source g e)
      Hready Hx Htail Hxfree Hsfree)).
    rewrite rev_involutive; apply path_without; auto.
  - intros [es Hpath].
    pose proof (natural_loop_endpoint_free g blocked x es (Graph.source g e) Hpath Hxfree)
      as Htailfree.
    apply reachable_iff_path; exists (Graph.source g e), (rev es); split.
    + apply filter_In; split; [left; reflexivity|].
      apply negb_true_iff; exact Htailfree.
    + apply (proj1 (natural_loop_reverse_avoiding blocked x es (Graph.source g e)
        Hready Hx Htail Hxfree Htailfree)); exact Hpath.
Qed.

(** On graph nodes the stopped reverse search computes precisely the natural-loop predicate. *)
Theorem natural_loop_nodes_exact x e : ready EV g p ->
  In (Graph.source g e) (Graph.nodes g) -> In x (Graph.nodes g) ->
  (FinSet.mem EV x (natural_loop_nodes p e) = true <-> natural_loop EV g e x).
Proof.
  intros Hready Htail Hx; unfold natural_loop_nodes, natural_loop; rewrite FinSet.mem_add.
  destruct (dfs_eq_dec EV x (Graph.target g e)) as [Heq|Hne].
  - split; intros _; left; exact Heq.
  - rewrite (natural_loop_search e x Hready Htail Hx Hne); reflexivity.
Qed.

End NaturalLoops.
