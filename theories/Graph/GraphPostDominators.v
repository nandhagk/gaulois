(** * Post-dominance via graph reversal

    Exit paths become entry paths in the prepared reverse graph.
    For example, a node on every path to either exit post-dominates their source.
    Builds on: GraphPrepare and GraphDominators. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphDominators.
Import List.ListNotations.

(** Every path from the node to an exit visits the post-dominator. *)
Definition post_dominates {V E} (g : Graph.t V E) (exits : list V) (d n : V) : Prop :=
  forall es x, path g n es x -> In x exits ->
    d = n \/ exists e, In e es /\ Graph.target g e = d.

(** Construct the dominator tree rooted at the exits in the reverse graph. *)
Definition post_dominator_tree {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (exits : list V) : dom_tree V :=
  dominator_tree (prepared_reverse p exits).

Lemma post_path_vertices {V E} (g : Graph.t V E) s es n d :
  path g s es n ->
  (d = s \/ exists e, In e es /\ Graph.target g e = d) <->
  (d = n \/ exists e, In e es /\ Graph.source g e = d).
Proof.
  intro Hpath; induction Hpath as [v|e es w Hedge Hpath IH].
  - simpl; split; intros [Heq|[a [Hin _]]]; try contradiction; auto.
  - simpl in *; split.
    + intros [Heq|[a [[Heq|Hin] Ha]]].
      * right; exists e; split; [left; reflexivity|symmetry; exact Heq].
      * subst a; destruct (proj1 IH (or_introl (eq_sym Ha))) as [Hend|[b [Hb Hsrc]]].
        -- left; exact Hend.
        -- right; exists b; auto.
      * destruct (proj1 IH (or_intror (ex_intro _ a (conj Hin Ha))))
          as [Hend|[b [Hb Hsrc]]].
        -- left; exact Hend.
        -- right; exists b; auto.
    + intros [Hend|[a [[Heq|Hin] Ha]]].
      * destruct (proj2 IH (or_introl Hend)) as [Htarget|[b [Hb Htarget]]].
        -- right; exists e; split; [left; reflexivity|symmetry; exact Htarget].
        -- right; exists b; auto.
      * subst a; left; symmetry; exact Ha.
      * destruct (proj2 IH (or_intror (ex_intro _ a (conj Hin Ha))))
          as [Htarget|[b [Hb Htarget]]].
        -- right; exists e; split; [left; reflexivity|symmetry; exact Htarget].
        -- right; exists b; auto.
Qed.

(** Post-dominance agrees with dominance on the reversed graph. *)
Theorem post_dominates_iff_reverse {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (d n : V) (exits : list V) :
  ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  (post_dominates g exits d n <-> dominates (reverse_graph p exits) d n).
Proof.
  intros Hready Hexits Hn; split.
  - intros Hpost x es Hexit Hpath.
    change (In x exits) in Hexit.
    pose proof (path_reverse_backward EV g p exits x es n Hready (Hexits x Hexit) Hpath)
      as Hforward.
    specialize (Hpost (rev es) x Hforward Hexit).
    apply (proj1 (post_path_vertices g n (rev es) x d Hforward)) in Hpost.
    destruct Hpost as [Heq|[e [Hin Heq]]]; [left; exact Heq|].
    right; exists e; split; [apply in_rev; exact Hin|exact Heq].
  - intros Hdom es x Hpath Hexit.
    pose proof (path_reverse_forward EV g p exits n es x Hready Hn Hpath) as Hreverse.
    specialize (Hdom x (rev es) Hexit Hreverse).
    destruct Hdom as [Heq|[e [Hin Heq]]].
    + apply (proj2 (post_path_vertices g n es x d Hpath)); left; exact Heq.
    + apply (proj2 (post_path_vertices g n es x d Hpath)); right.
      exists e; split; [apply in_rev; exact Hin|exact Heq].
Qed.

(** Every positive tree query is a semantic post-dominance fact. *)
Theorem post_dominator_tree_sound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (d n : V) (exits : list V) :
  ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominates_b EV (post_dominator_tree p exits) d n = true -> post_dominates g exits d n.
Proof.
  intros Hready Hexits Hn Hquery.
  apply (proj2 (post_dominates_iff_reverse EV g p d n exits Hready Hexits Hn)).
  eapply (proj1 (proj2 (proj2 (dominator_tree_sound EV (reverse_graph p exits)
    (prepared_reverse p exits) (reverse_graph_ready EV g p exits Hready Hexits))))); exact Hquery.
Qed.

(** A checked reverse tree answers exactly on nodes that can reach an exit. *)
Theorem post_dominator_tree_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (d n : V) (exits : list V) :
  ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominator_exact (prepared_reverse p exits) = true ->
  (exists es x, path g n es x /\ In x exits) ->
  (dominates_b EV (post_dominator_tree p exits) d n = true <-> post_dominates g exits d n).
Proof.
  intros Hready Hexits Hn Hcheck [es [x [Hpath Hexit]]].
  assert (Hreach : reachable (reverse_graph p exits) n).
  { apply reachable_iff_path; exists x, (rev es); split; [exact Hexit|].
    apply path_reverse_forward; assumption. }
  rewrite (proj1 (dominator_tree_exact EV (reverse_graph p exits)
    (prepared_reverse p exits) (reverse_graph_ready EV g p exits Hready Hexits) Hcheck) d n Hreach).
  symmetry; apply post_dominates_iff_reverse; assumption.
Qed.
