(** * Frontier placement and ordered memory renaming

    A tagged split graph preserves original edge identities and supplies a fresh live root.
    For example, two parallel edges become two different synthetic nodes.
    Builds on: AnalysesMemoryGraph, GraphIdf and CollectionsEncoding. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphLengauerTarjan GraphDominators GraphEdgeDominance GraphFrontier GraphIdf.
From Gaulois.Views Require Import ViewsGraph ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph.
Import List.ListNotations.

(** * Tagged split graph *)

(** The live root, original blocks and individual edge identities have disjoint tags. *)
Inductive memory_dom_node (N E : Type) : Type :=
  | MemoryRoot
  | MemoryBlock (n : N)
  | MemoryEdge (e : E).

Arguments MemoryRoot {N E}.
Arguments MemoryBlock {N E}.
Arguments MemoryEdge {N E}.

(** Virtual entry edges and the two halves of a real edge retain distinct identities. *)
Inductive memory_dom_edge (N E : Type) : Type :=
  | MemoryStart (n : N)
  | MemoryBegin (e : E)
  | MemoryEnd (e : E).

Arguments MemoryStart {N E}.
Arguments MemoryBegin {N E}.
Arguments MemoryEnd {N E}.

(** Node encodings reserve a root code and distinguish both client key spaces. *)
Definition memory_dom_node_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (memory_dom_node N E).
Proof.
  refine (Encoding _ (fun v => match v with
    | MemoryRoot => xH
    | MemoryBlock n => xO (encode EN n)
    | MemoryEdge e => xI (encode EE e)
    end) _).
  intros [|n|e] [|n'|e'] Heq; cbn in Heq; try discriminate; try reflexivity;
    injection Heq as Heq; f_equal; eapply encode_injective; exact Heq.
Defined.

(** Edge encodings distinguish entry, beginning and ending tags. *)
Definition memory_dom_edge_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (memory_dom_edge N E).
Proof.
  refine (Encoding _ (fun a => match a with
    | MemoryStart n => xO (encode EN n)
    | MemoryBegin e => xI (xO (encode EE e))
    | MemoryEnd e => xI (xI (encode EE e))
    end) _).
  intros [n|e|e] [n'|e'|e'] Heq; cbn in Heq; try discriminate;
    injection Heq as Heq; f_equal; eapply encode_injective; exact Heq.
Defined.

(** Deduplication retains the first occurrence of each injectively encoded identity. *)
Definition memory_distinct {A} (EA : encoding A) (xs : list A) : list A :=
  virtual_entries_from EA FinSet.empty xs.

Lemma memory_distinct_in {A} (EA : encoding A) xs x :
  In x (memory_distinct EA xs) <-> In x xs.
Proof.
  unfold memory_distinct; rewrite virtual_entries_from_in, FinSet.mem_empty; tauto.
Qed.

Lemma memory_distinct_nodup {A} (EA : encoding A) xs : NoDup (memory_distinct EA xs).
Proof.
  apply virtual_entries_from_nodup.
Qed.

(** Every block's deduplicated outgoing list is materialized once in a trie index. *)
Definition memory_block_index {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : Map.t N (list E) :=
  fold_right (fun n m => Map.set EN n (memory_distinct EE (Graph.out g n)) m)
    Map.empty (Graph.nodes g).

Lemma memory_index_list {A B} (EA : encoding A) (f : A -> list B) xs x :
  index_edges EA (fold_right (fun y m => Map.set EA y (f y) m) Map.empty xs) x =
    if existsb (fun y => Pos.eqb (encode EA x) (encode EA y)) xs then f x else [].
Proof.
  induction xs as [|y rest IH]; cbn [fold_right existsb].
  - unfold index_edges; rewrite Map.get_empty; reflexivity.
  - destruct (Pos.eq_dec (encode EA x) (encode EA y)) as [Heq|Hne].
    + apply (encode_injective EA) in Heq; subst y.
      unfold index_edges; rewrite Map.get_set_same, Pos.eqb_refl; reflexivity.
    + unfold index_edges in *; rewrite Map.get_set_other by (intro Heq; subst y; congruence).
      assert (Hfalse : Pos.eqb (encode EA x) (encode EA y) = false)
        by (apply Pos.eqb_neq; exact Hne).
      rewrite Hfalse; exact IH.
Qed.

Lemma memory_block_index_at {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) n :
  In n (Graph.nodes g) ->
  index_edges EN (memory_block_index EN EE g) n = memory_distinct EE (Graph.out g n).
Proof.
  intro Hn; unfold memory_block_index; rewrite memory_index_list.
  assert (Hexists : existsb (fun y => Pos.eqb (encode EN n) (encode EN y))
      (Graph.nodes g) = true).
  { apply existsb_exists; exists n; split; [exact Hn|apply Pos.eqb_refl]. }
  rewrite Hexists; reflexivity.
Qed.

Lemma memory_block_index_domain {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) n :
  ~ In n (Graph.nodes g) -> index_edges EN (memory_block_index EN EE g) n = [].
Proof.
  intro Hn; unfold memory_block_index; rewrite memory_index_list.
  destruct (existsb (fun y => Pos.eqb (encode EN n) (encode EN y)) (Graph.nodes g))
    eqn:Hexists; [|reflexivity].
  apply existsb_exists in Hexists; destruct Hexists as [y [Hy Heq]].
  apply Pos.eqb_eq, (encode_injective EN) in Heq; subst y; contradiction.
Qed.

(** The root and every real edge are expanded using prepared identity-preserving lists. *)
Definition memory_dom_graph {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : Graph.t (memory_dom_node N E) (memory_dom_edge N E) :=
  let entries := memory_distinct EN (Graph.entries g) in
  let edges := memory_distinct EE (edges_of g) in
  let edge_set := FinSet.of_list EE edges in
  let blocks := memory_block_index EN EE g in
  {| Graph.entries := [MemoryRoot];
     Graph.nodes := MemoryRoot :: map MemoryBlock (Graph.nodes g) ++ map MemoryEdge edges;
     Graph.out := fun v => match v with
       | MemoryRoot => map MemoryStart entries
       | MemoryBlock n => map MemoryBegin (index_edges EN blocks n)
       | MemoryEdge e => if FinSet.mem EE e edge_set then [MemoryEnd e] else []
       end;
     Graph.source := fun a => match a with
       | MemoryStart _ => MemoryRoot
       | MemoryBegin e => MemoryBlock (Graph.source g e)
       | MemoryEnd e => MemoryEdge e
       end;
     Graph.target := fun a => match a with
       | MemoryStart n => MemoryBlock n
       | MemoryBegin e => MemoryEdge e
       | MemoryEnd e => MemoryBlock (Graph.target g e)
       end |}.

Lemma memory_dom_block_node {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) n :
  In (MemoryBlock n) (Graph.nodes (memory_dom_graph EN EE g)) <-> In n (Graph.nodes g).
Proof.
  change ((@MemoryRoot N E = MemoryBlock n \/ In (MemoryBlock n)
    (map MemoryBlock (Graph.nodes g) ++ map MemoryEdge (memory_distinct EE (edges_of g))))
    <-> In n (Graph.nodes g)).
  rewrite in_app_iff, !in_map_iff.
  split.
  - intros [Hroot|[[m [Heq Hm]]|[e [Heq _]]]]; try discriminate.
    inversion Heq; subst m; exact Hm.
  - intro Hn; right; left; exists n; auto.
Qed.

Lemma memory_dom_edge_node {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) e :
  In (MemoryEdge e) (Graph.nodes (memory_dom_graph EN EE g)) <-> In e (edges_of g).
Proof.
  change ((@MemoryRoot N E = MemoryEdge e \/ In (MemoryEdge e)
    (map MemoryBlock (Graph.nodes g) ++ map MemoryEdge (memory_distinct EE (edges_of g))))
    <-> In e (edges_of g)).
  rewrite in_app_iff, !in_map_iff.
  split.
  - intros [Hroot|[[n [Heq _]]|[a [Heq Ha]]]]; try discriminate.
    inversion Heq; subst a; now apply memory_distinct_in in Ha.
  - intro He; right; right; exists e; split; [reflexivity|].
    apply memory_distinct_in; exact He.
Qed.

Lemma memory_dom_block_out {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) n : In n (Graph.nodes g) ->
  Graph.out (memory_dom_graph EN EE g) (MemoryBlock n) =
    map MemoryBegin (memory_distinct EE (Graph.out g n)).
Proof.
  intro Hn; change (map (@MemoryBegin N E) (index_edges EN (memory_block_index EN EE g) n) =
    map MemoryBegin (memory_distinct EE (Graph.out g n))).
  rewrite memory_block_index_at by exact Hn; reflexivity.
Qed.

Lemma memory_dom_edge_out {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) e : In e (edges_of g) ->
  Graph.out (memory_dom_graph EN EE g) (MemoryEdge e) = [MemoryEnd e].
Proof.
  intro He; unfold memory_dom_graph; cbn [Graph.out].
  assert (Hmem : FinSet.mem EE e (FinSet.of_list EE (memory_distinct EE (edges_of g))) = true).
  { apply FinSet.of_list_spec, memory_distinct_in; exact He. }
  rewrite Hmem; reflexivity.
Qed.

Lemma memory_dom_outside {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) v :
  ~ In v (Graph.nodes (memory_dom_graph EN EE g)) ->
  Graph.out (memory_dom_graph EN EE g) v = [].
Proof.
  destruct v as [|n|e]; intro Hnot.
  - exfalso; apply Hnot; left; reflexivity.
  - unfold memory_dom_graph; cbn [Graph.out].
    rewrite memory_block_index_domain; [reflexivity|].
    intro Hn; apply Hnot, memory_dom_block_node; exact Hn.
  - unfold memory_dom_graph; cbn [Graph.out].
    destruct (FinSet.mem EE e (FinSet.of_list EE (memory_distinct EE (edges_of g))))
      eqn:Hmem; [|reflexivity].
    exfalso; apply Hnot, memory_dom_edge_node.
    apply FinSet.of_list_spec, memory_distinct_in in Hmem; exact Hmem.
Qed.

Lemma memory_dom_begin_in {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) n e : graph_wf g ->
  (In (MemoryBegin e) (Graph.out (memory_dom_graph EN EE g) (MemoryBlock n)) <->
    In n (Graph.nodes g) /\ In e (Graph.out g n)).
Proof.
  intro Hwf.
  destruct (existsb (fun m => Pos.eqb (encode EN n) (encode EN m)) (Graph.nodes g))
    eqn:Hlisted.
  - apply existsb_exists in Hlisted; destruct Hlisted as [m [Hm Heq]].
    apply Pos.eqb_eq, (encode_injective EN) in Heq; subst m.
    rewrite memory_dom_block_out by exact Hm; rewrite in_map_iff; split.
    + intros [a [Heq Ha]]; inversion Heq; subst a; split; [exact Hm|].
      now apply memory_distinct_in in Ha.
    + intros [_ He]; exists e; split; [reflexivity|apply memory_distinct_in; exact He].
  - assert (Hnot : ~ In n (Graph.nodes g)).
    { intro Hn; assert (Hexists : existsb
        (fun m => Pos.eqb (encode EN n) (encode EN m)) (Graph.nodes g) = true).
      { apply existsb_exists; exists n; split; [exact Hn|apply Pos.eqb_refl]. }
      congruence. }
    unfold memory_dom_graph; cbn [Graph.out].
    rewrite memory_block_index_domain by exact Hnot; cbn; tauto.
Qed.

(** Expansion is well formed and every expanded adjacency list has unique edge identities. *)
Theorem memory_dom_graph_wf {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> graph_wf (memory_dom_graph EN EE g) /\
    (forall v, NoDup (Graph.out (memory_dom_graph EN EE g) v)).
Proof.
  intro Hwf; split.
  - constructor.
    + cbn [memory_dom_graph]; constructor.
      * rewrite in_app_iff, !in_map_iff; intros [[n [Heq _]]|[e [Heq _]]]; discriminate.
      * apply nodup_app_disjoint.
        -- apply nodup_map_injective; [intros n m Heq; now inversion Heq|exact (nodes_nodup Hwf)].
        -- apply nodup_map_injective; [intros e a Heq; now inversion Heq|].
           apply memory_distinct_nodup.
        -- intros v Hblock Hedge; apply in_map_iff in Hblock; apply in_map_iff in Hedge.
           destruct Hblock as [n [Heq _]], Hedge as [e [Heq' _]]; congruence.
    + intros v [Heq|Hfalse]; [subst v; left; reflexivity|contradiction].
    + intros [|n|e] a Ha.
      * cbn [memory_dom_graph Graph.out] in Ha; apply in_map_iff in Ha.
        destruct Ha as [n [Heq _]]; subst a; reflexivity.
      * cbn [memory_dom_graph Graph.out] in Ha; apply in_map_iff in Ha.
        destruct Ha as [e [Heq He]]; subst a; cbn [memory_dom_graph Graph.source].
        unfold memory_block_index in He; rewrite memory_index_list in He.
        destruct (existsb _ _) eqn:Hlisted; [|contradiction].
        apply memory_distinct_in in He; f_equal; exact (out_source Hwf n e He).
      * cbn [memory_dom_graph Graph.out] in Ha.
        destruct (FinSet.mem _ _ _); [|contradiction].
        destruct Ha as [Heq|Hfalse]; [subst a; reflexivity|contradiction].
    + intros [|n|e] a Hnode Ha.
      * cbn [memory_dom_graph Graph.out] in Ha; apply in_map_iff in Ha.
        destruct Ha as [n [Heq Hentry]]; subst a; apply memory_dom_block_node.
        apply memory_distinct_in in Hentry; exact (entries_in Hwf n Hentry).
      * apply memory_dom_block_node in Hnode; rewrite memory_dom_block_out in Ha by exact Hnode.
        apply in_map_iff in Ha; destruct Ha as [e [Heq He]]; subst a.
        apply memory_distinct_in in He.
        apply memory_dom_edge_node; exact (edges_of_in g n e Hnode He).
      * apply memory_dom_edge_node in Hnode; rewrite memory_dom_edge_out in Ha by exact Hnode.
        destruct Ha as [Heq|Hfalse]; [subst a|contradiction].
        apply memory_dom_block_node; apply in_flat_map in Hnode.
        destruct Hnode as [n [Hn He]]; exact (out_target_in Hwf n e Hn He).
  - intros [|n|e].
    + cbn [memory_dom_graph Graph.out]; apply nodup_map_injective;
        [intros n m Heq; now inversion Heq|apply memory_distinct_nodup].
    + cbn [memory_dom_graph Graph.out]; apply nodup_map_injective;
        [intros e a Heq; now inversion Heq|].
      unfold memory_block_index; rewrite memory_index_list.
      destruct (existsb _ _); [apply memory_distinct_nodup|constructor].
    + cbn [memory_dom_graph Graph.out]; destruct (FinSet.mem _ _ _); constructor;
        [intro Hfalse; exact Hfalse|constructor].
Qed.

(** Deduplication supplies exactly the preparation premises of dominance and direct IDF. *)
Lemma memory_dom_ready {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> ready (memory_dom_node_encoding EN EE) (memory_dom_graph EN EE g)
    (prepare (memory_dom_node_encoding EN EE) (memory_dom_graph EN EE g)).
Proof.
  intro Hwf; destruct (memory_dom_graph_wf EN EE g Hwf) as [Hgraph Hout].
  apply prepare_ready; assumption.
Qed.

(** * Original and expanded reachability *)

Lemma memory_dom_lift_reachable {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : graph_wf g -> forall n, reachable g n ->
  reachable (memory_dom_graph EN EE g) (MemoryBlock n).
Proof.
  intros Hwf n Hreach; induction Hreach as [n Hentry|e Hsource IH Hedge].
  - change (reachable (memory_dom_graph EN EE g)
      (Graph.target (memory_dom_graph EN EE g) (MemoryStart n))).
    apply reachable_step.
    + apply reachable_entry; left; reflexivity.
    + cbn [memory_dom_graph Graph.out]; apply in_map, memory_distinct_in; exact Hentry.
  - assert (Hnode : In (Graph.source g e) (Graph.nodes g)).
    { exact (reachable_in_nodes g _ Hwf Hsource). }
    assert (Hlisted : In e (edges_of g)) by (eapply edges_of_in; eassumption).
    change (reachable (memory_dom_graph EN EE g)
      (Graph.target (memory_dom_graph EN EE g) (MemoryEnd e))).
    apply reachable_step.
    + change (reachable (memory_dom_graph EN EE g)
        (Graph.target (memory_dom_graph EN EE g) (MemoryBegin e))).
      apply reachable_step; [exact IH|].
      apply memory_dom_begin_in; [exact Hwf|split; assumption].
    + change (In (MemoryEnd e) (Graph.out (memory_dom_graph EN EE g) (MemoryEdge e))).
      rewrite memory_dom_edge_out by exact Hlisted; left; reflexivity.
Qed.

Lemma memory_dom_lower_reachable {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : graph_wf g -> forall v,
  reachable (memory_dom_graph EN EE g) v ->
  match v with
  | MemoryRoot => True
  | MemoryBlock n => reachable g n
  | MemoryEdge e => reachable g (Graph.source g e) /\ In e (Graph.out g (Graph.source g e))
  end.
Proof.
  intros Hwf v Hreach; induction Hreach as [v Hentry|a Hsource IH Hedge].
  - destruct Hentry as [Heq|Hfalse]; [subst v; exact I|contradiction].
  - destruct a as [n|e|e]; cbn [memory_dom_graph Graph.source Graph.target] in IH |- *.
    + cbn [memory_dom_graph Graph.out Graph.source] in Hedge; apply in_map_iff in Hedge.
      destruct Hedge as [m [Heq Hm]]; inversion Heq; subst m.
      apply memory_distinct_in in Hm; exact (reachable_entry n Hm).
    + apply memory_dom_begin_in in Hedge; [|exact Hwf].
      split; [exact IH|exact (proj2 Hedge)].
    + destruct IH as [Hreach He]; exact (reachable_step e Hreach He).
Qed.

(** Expansion preserves exactly the reachable original blocks, including entry backedges. *)
Theorem memory_dom_reachable {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> forall n,
    (reachable (memory_dom_graph EN EE g) (MemoryBlock n) <-> reachable g n).
Proof.
  intros Hwf n; split.
  - exact (memory_dom_lower_reachable EN EE g Hwf (MemoryBlock n)).
  - apply memory_dom_lift_reachable; exact Hwf.
Qed.

(** Each original edge expands to its beginning and ending, preserving path order. *)
Fixpoint memory_dom_path {N E} (es : list E) : list (memory_dom_edge N E) :=
  match es with
  | [] => []
  | e :: rest => MemoryBegin e :: MemoryEnd e :: memory_dom_path rest
  end.

Lemma memory_dom_path_injective {N E} (xs ys : list E) :
  @memory_dom_path N E xs = memory_dom_path ys -> xs = ys.
Proof.
  revert ys; induction xs as [|x rest IH]; intros [|y tail] Heq; try discriminate.
  - reflexivity.
  - cbn [memory_dom_path] in Heq.
    assert (Hxy : x = y) by congruence; subst y; f_equal; apply IH; congruence.
Qed.

Lemma memory_dom_path_lift {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) s es n : graph_wf g -> path g s es n -> In s (Graph.nodes g) ->
  path (memory_dom_graph EN EE g) (MemoryBlock s) (memory_dom_path es) (MemoryBlock n).
Proof.
  intros Hwf Hpath; induction Hpath as [n|e es n Hedge Hpath IH]; intro Hsource.
  - constructor.
  - cbn [memory_dom_path].
    apply (@path_cons _ _ (memory_dom_graph EN EE g) (MemoryBegin e)).
    + apply memory_dom_begin_in; [exact Hwf|split; assumption].
    + apply (@path_cons _ _ (memory_dom_graph EN EE g) (MemoryEnd e)).
      * change (In (MemoryEnd e) (Graph.out (memory_dom_graph EN EE g) (MemoryEdge e))).
        rewrite memory_dom_edge_out; [left; reflexivity|].
        exact (edges_of_in g (Graph.source g e) e Hsource Hedge).
      * apply IH; exact (out_target_in Hwf (Graph.source g e) e Hsource Hedge).
Qed.

Lemma memory_dom_paths_lower {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : graph_wf g -> forall ds,
  (forall s n, path (memory_dom_graph EN EE g) (MemoryBlock s) ds (MemoryBlock n) ->
    exists es, ds = memory_dom_path es /\ path g s es n) /\
  (forall e n, path (memory_dom_graph EN EE g) (MemoryEdge e) ds (MemoryBlock n) ->
    exists es, ds = MemoryEnd e :: memory_dom_path es /\ path g (Graph.target g e) es n).
Proof.
  intros Hwf ds; induction ds as [|a rest [IHblock IHedge]]; split.
  - intros s n Hpath; apply dominance_path_nil_inv in Hpath; inversion Hpath; subst n.
    exists []; split; [reflexivity|constructor].
  - intros e n Hpath; apply dominance_path_nil_inv in Hpath; discriminate.
  - intros s n Hpath; apply dominance_path_cons_inv in Hpath.
    destruct Hpath as [Hsource [Hedge Htail]].
    destruct a as [m|e|e]; cbn [memory_dom_graph Graph.source] in Hsource; try discriminate.
    inversion Hsource; subst s.
    destruct (IHedge e n Htail) as [es [Hrest Hpath]].
    exists (e :: es); split; [cbn [memory_dom_path]; now rewrite Hrest|].
    apply path_cons; [|exact Hpath].
    apply memory_dom_begin_in in Hedge; [exact (proj2 Hedge)|exact Hwf].
  - intros e n Hpath; apply dominance_path_cons_inv in Hpath.
    destruct Hpath as [Hsource [_ Htail]].
    destruct a as [m|a|a]; cbn [memory_dom_graph Graph.source] in Hsource; try discriminate.
    inversion Hsource; subst a.
    destruct (IHblock (Graph.target g e) n Htail) as [es [Hrest Hpath]].
    exists es; split; [now rewrite Hrest|exact Hpath].
Qed.

(** Split paths between listed original blocks are exactly the ordered expanded CFG paths. *)
Lemma memory_dom_path_agrees {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) s es n : graph_wf g -> In s (Graph.nodes g) ->
  (path (memory_dom_graph EN EE g) (MemoryBlock s) (memory_dom_path es) (MemoryBlock n) <->
    path g s es n).
Proof.
  intros Hwf Hs; split.
  - intro Hpath; destruct (proj1 (memory_dom_paths_lower EN EE g Hwf (memory_dom_path es))
      s n Hpath) as [original [Heq Horiginal]].
    apply memory_dom_path_injective in Heq; subst original; exact Horiginal.
  - intro Hpath; apply memory_dom_path_lift; assumption.
Qed.

(** An expanded edge node is reachable exactly when its listed source is reachable. *)
Lemma memory_dom_edge_reachable {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) e : graph_wf g ->
  (reachable (memory_dom_graph EN EE g) (MemoryEdge e) <->
    reachable g (Graph.source g e) /\ In e (Graph.out g (Graph.source g e))).
Proof.
  intro Hwf; split.
  - exact (memory_dom_lower_reachable EN EE g Hwf (MemoryEdge e)).
  - intros [Hsource Hedge].
    change (reachable (memory_dom_graph EN EE g)
      (Graph.target (memory_dom_graph EN EE g) (MemoryBegin e))).
    apply reachable_step.
    + apply memory_dom_lift_reachable; assumption.
    + apply memory_dom_begin_in; [exact Hwf|split; [|exact Hedge]].
      exact (reachable_in_nodes g _ Hwf Hsource).
Qed.

(** Recover the prepared edge list from the tagged node inventory without deduplicating again. *)
Fixpoint memory_dom_edge_tags {N E} (nodes : list (memory_dom_node N E)) : list E :=
  match nodes with
  | [] => []
  | MemoryEdge e :: rest => e :: memory_dom_edge_tags rest
  | _ :: rest => memory_dom_edge_tags rest
  end.

Lemma memory_dom_edge_tags_app {N E} (xs ys : list (memory_dom_node N E)) :
  memory_dom_edge_tags (xs ++ ys) = memory_dom_edge_tags xs ++ memory_dom_edge_tags ys.
Proof.
  induction xs as [|[|n|e] rest IH]; cbn [memory_dom_edge_tags app]; now rewrite ?IH.
Qed.

Lemma memory_dom_edge_tags_exact {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : memory_dom_edge_tags (Graph.nodes (memory_dom_graph EN EE g)) =
    memory_distinct EE (edges_of g).
Proof.
  change (memory_dom_edge_tags
    (map (@MemoryBlock N E) (Graph.nodes g) ++ map MemoryEdge (memory_distinct EE (edges_of g)))
    = memory_distinct EE (edges_of g)).
  rewrite memory_dom_edge_tags_app.
  assert (Hblocks : forall ns, memory_dom_edge_tags (map (@MemoryBlock N E) ns) = []).
  { intro ns; induction ns; cbn [map memory_dom_edge_tags]; assumption || reflexivity. }
  assert (Hedges : forall es, memory_dom_edge_tags (map (@MemoryEdge N E) es) = es).
  { intro es; induction es; cbn [map memory_dom_edge_tags]; now rewrite ?IHes. }
  rewrite Hblocks, Hedges; reflexivity.
Qed.

(** The already computed live set filters defining edges in original first-occurrence order. *)
Definition memory_dom_defs_from {N E T} (edges : list E)
    (effects : E -> list (memory_effect T)) (live : FinSet.t (memory_dom_node N E))
    (ED : encoding (memory_dom_node N E)) : list (memory_dom_node N E) :=
  MemoryRoot :: map MemoryEdge (filter (fun e => FinSet.mem ED (MemoryEdge e) live &&
    existsb effect_is_def (effects e)) edges).

(** The live root and every reachable defining edge seed the unpruned frontier query. *)
Definition memory_dom_defs {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) : list (memory_dom_node N E) :=
  let sg := memory_dom_graph EN EE g in
  let ED := memory_dom_node_encoding EN EE in
  let sp := prepare ED sg in
  memory_dom_defs_from (memory_dom_edge_tags (Graph.nodes sg)) effects
    (visited (dfs sp FinSet.empty (Graph.entries sg))) ED.

Lemma memory_dom_defs_exact {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) d : graph_wf g ->
  (In d (memory_dom_defs EN EE g effects) <-> d = MemoryRoot \/
    exists e a, d = MemoryEdge e /\ reachable g (Graph.source g e) /\
      In e (Graph.out g (Graph.source g e)) /\ In a (effects e) /\ effect_is_def a = true).
Proof.
  intro Hwf; unfold memory_dom_defs; rewrite memory_dom_edge_tags_exact.
  unfold memory_dom_defs_from; cbn [In].
  rewrite in_map_iff; split.
  - intros [Heq|[e [Heq Hin]]]; [left; symmetry; exact Heq|].
    apply filter_In in Hin; destruct Hin as [_ Htest].
    apply Bool.andb_true_iff in Htest; destruct Htest as [Hlive Hdef].
    apply (reachable_dfs _ _ _ _ (memory_dom_ready EN EE g Hwf)) in Hlive.
    apply memory_dom_edge_reachable in Hlive; [|exact Hwf].
    destruct Hlive as [Hsource Hedge]; apply existsb_exists in Hdef.
    destruct Hdef as [a [Ha Hdef]]; right; exists e, a; repeat split; try assumption.
    symmetry; exact Heq.
  - intros [Heq|[e [a [Heq [Hsource [Hedge [Ha Hdef]]]]]]]; [left; symmetry; exact Heq|].
    right; exists e; split; [symmetry; exact Heq|].
    apply filter_In; split.
    + apply memory_distinct_in; eapply edges_of_in; [|exact Hedge].
      exact (reachable_in_nodes g _ Hwf Hsource).
    + apply Bool.andb_true_iff; split.
      * apply (reachable_dfs _ _ _ _ (memory_dom_ready EN EE g Hwf)).
        apply memory_dom_edge_reachable; [exact Hwf|split; assumption].
      * apply existsb_exists; exists a; split; assumption.
Qed.

(** A root-to-edge-node path first traverses the original source block. *)
Lemma memory_dom_edge_dominated {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) e :
  dominates (memory_dom_graph EN EE g) (MemoryBlock (Graph.source g e)) (MemoryEdge e).
Proof.
  intros s es Hentry Hpath.
  destruct Hentry as [Heq|Hfalse]; [subst s|contradiction].
  assert (Hnonempty : es <> []).
  { intro Heq; subst es; apply dominance_path_nil_inv in Hpath; discriminate. }
  destruct (semi_path_last _ _ _ _ Hpath Hnonempty)
    as [pre [a [Hsplit [Hpre [Hedge Htarget]]]]].
  destruct a as [n|a|a]; cbn [memory_dom_graph Graph.target] in Htarget; try discriminate.
  inversion Htarget; subst a.
  destruct (path_endpoint _ _ _ _ Hpre) as [Hroot|[a [Ha Htarget']]].
  - change (@MemoryBlock N E (Graph.source g e) = MemoryRoot) in Hroot; discriminate.
  - right; exists a; split.
    + rewrite Hsplit; apply in_or_app; left; exact Ha.
    + exact Htarget'.
Qed.

(** Synthetic edge nodes and the live root never belong to a dominance frontier. *)
Lemma memory_dom_frontier_block {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) d v : graph_wf g ->
  in_df (memory_dom_graph EN EE g) d v -> exists n, v = MemoryBlock n.
Proof.
  intros Hwf [a [Hedge [Htarget [Hsource [Hdom Hnot]]]]].
  destruct a as [n|e|e]; cbn [memory_dom_graph Graph.target] in Htarget; subst v.
  - exists n; reflexivity.
  - exfalso; apply Hnot; split.
    + eapply dominates_trans; [exact Hdom|apply memory_dom_edge_dominated].
    + intro Heq; subst d.
      pose proof (memory_dom_edge_dominated EN EE g e) as Hback.
      assert (Htarget : reachable (memory_dom_graph EN EE g) (MemoryEdge e))
        by (exact (reachable_step (MemoryBegin e) Hsource Hedge)).
      pose proof (idf_dominance_antisym _ _ _ (memory_dom_ready EN EE g Hwf)
        (MemoryEdge e) (MemoryBlock (Graph.source g e)) Htarget Hsource Hdom Hback) as Hbad.
      discriminate.
  - exists (Graph.target g e); reflexivity.
Qed.

(** Every iterated-frontier placement is a reachable original block. *)
Lemma memory_dom_idf_block {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) v : graph_wf g ->
  in_idf (memory_dom_graph EN EE g) (memory_dom_defs EN EE g effects) v ->
  exists n, v = MemoryBlock n /\ reachable g n.
Proof.
  intros Hwf Hphi; destruct Hphi as [d v Hfrom Hdf].
  destruct (memory_dom_frontier_block EN EE g d v Hwf Hdf) as [n Heq]; subst v.
  exists n; split; [reflexivity|].
  apply (memory_dom_reachable EN EE g Hwf).
  destruct Hdf as [e [Hedge [Htarget [Hsource _]]]]; rewrite <- Htarget.
  exact (reachable_step e Hsource Hedge).
Qed.

(** * Ordered occurrence records *)

(** The last defining occurrence is independent of the incoming version. *)
Fixpoint memory_edge_definition {N E T} (e : E) (i : nat)
    (effects : list (memory_effect T)) : option (memory_version N E) :=
  match effects with
  | [] => None
  | a :: rest =>
    match memory_edge_definition e (S i) rest with
    | Some d => Some d
    | None => if effect_is_def a then Some (MemoryDef e i) else None
    end
  end.

(** Each node record retains its inherited version, outgoing version and occurrence index. *)
Record memory_rename_record (N E : Type) : Type := MemoryRenameRecord {
  memory_record_input : memory_version N E;
  memory_record_output : memory_version N E;
  memory_record_before : Map.t nat (memory_version N E)
}.

Arguments MemoryRenameRecord {N E}.
Arguments memory_record_input {N E}.
Arguments memory_record_output {N E}.
Arguments memory_record_before {N E}.

(** The left-to-right effect pass records an input before replacing it by a definition. *)
Fixpoint memory_rename_effects {N E T} (e : E) (i : nat)
    (effects : list (memory_effect T)) (input : memory_version N E) :
    Map.t nat (memory_version N E) * memory_version N E :=
  match effects with
  | [] => (Map.empty, input)
  | a :: rest =>
    let '(before, output) := memory_rename_effects e (S i) rest (memory_after e i a input) in
    (Map.set nat_encoding i input before, output)
  end.

Lemma memory_rename_effects_output {N E T} (e : E) i
    (effects : list (memory_effect T)) (input : memory_version N E) :
  snd (memory_rename_effects e i effects input) = memory_last_defs e i effects input /\
  memory_last_defs e i effects input =
    match memory_edge_definition e i effects with Some d => d | None => input end.
Proof.
  revert i input; induction effects as [|a rest IH]; intros i input; [split; reflexivity|].
  cbn [memory_rename_effects memory_last_defs memory_edge_definition].
  specialize (IH (S i) (memory_after e i a input)).
  destruct (memory_rename_effects e (S i) rest (memory_after e i a input)) as [before output].
  cbn [snd] in IH |- *; destruct IH as [Houtput Hlast]; split; [exact Houtput|].
  rewrite Hlast; destruct (memory_edge_definition e (S i) rest) as [d|]; [reflexivity|].
  unfold memory_after; destruct (effect_is_def a); reflexivity.
Qed.

Lemma memory_rename_effects_get {N E T} (e : E) i
    (effects : list (memory_effect T)) (input : memory_version N E) j :
  Map.get nat_encoding j (fst (memory_rename_effects e i effects input)) =
    if Nat.leb i j then
      match nth_error effects (j - i) with
      | Some _ => Some (memory_last_defs e i (firstn (j - i) effects) input)
      | None => None
      end
    else None.
Proof.
  revert i input j; induction effects as [|a rest IH]; intros i input j.
  - cbn [memory_rename_effects fst]; rewrite Map.get_empty.
    destruct (Nat.leb i j); [destruct (j - i)|]; reflexivity.
  - cbn [memory_rename_effects].
    destruct (memory_rename_effects e (S i) rest (memory_after e i a input))
      as [before output] eqn:Hrest; cbn [fst].
    destruct (Nat.eq_dec j i) as [Heq|Hne].
    + subst j; rewrite Map.get_set_same, Nat.leb_refl, Nat.sub_diag; reflexivity.
    + rewrite Map.get_set_other by exact Hne.
      specialize (IH (S i) (memory_after e i a input) j); rewrite Hrest in IH; cbn [fst] in IH.
      rewrite IH; destruct (Nat.leb i j) eqn:Hle.
      * apply Nat.leb_le in Hle; assert (Hlt : i < j) by lia.
        assert (Hnext : Nat.leb (S i) j = true) by (apply Nat.leb_le; lia).
        assert (Hsub : j - i = S (j - S i)) by lia.
        rewrite Hnext, Hsub; reflexivity.
      * apply Nat.leb_gt in Hle.
        assert (Hnext : Nat.leb (S i) j = false) by (apply Nat.leb_gt; lia).
        rewrite Hnext; reflexivity.
Qed.

(** The effect record has exactly the original occurrence domain. *)
Lemma memory_rename_effects_domain {N E T} (e : E)
    (effects : list (memory_effect T)) (input : memory_version N E) i :
  (exists v, Map.get nat_encoding i (fst (memory_rename_effects e 0 effects input)) = Some v)
    <-> exists a, nth_error effects i = Some a.
Proof.
  rewrite memory_rename_effects_get, Nat.sub_0_r; cbn [Nat.leb].
  destruct (nth_error effects i) as [a|].
  - split; [intros _; exists a; reflexivity|].
    intros _; eexists; reflexivity.
  - split; intros [x Hfalse]; discriminate.
Qed.

(** Every lookup in an ordered effect pass agrees with its inductive flow relation. *)
Lemma memory_rename_effects_flow {N E T} (mg : memory_graph N E) (e : E)
    (effects : list (memory_effect T)) (input : memory_version N E) :
  (forall j, memory_before mg e j =
    Map.get nat_encoding j (fst (memory_rename_effects e 0 effects input))) ->
  memory_edge_flow mg e 0 effects input (memory_last_defs e 0 effects input).
Proof.
  intro Hget.
  assert (Hflow : forall (rest : list (memory_effect T)) i (current : memory_version N E),
    (forall j, i <= j -> memory_before mg e j =
      Map.get nat_encoding j (fst (memory_rename_effects e i rest current))) ->
    memory_edge_flow mg e i rest current (memory_last_defs e i rest current)).
  { intro rest; induction rest as [|a rest IH]; intros i current Hlocal.
    - constructor.
    - cbn [memory_last_defs]; constructor.
      + rewrite Hlocal by lia; rewrite memory_rename_effects_get.
        rewrite Nat.leb_refl, Nat.sub_diag; reflexivity.
      + apply IH; intros j Hj; rewrite Hlocal by lia.
        cbn [memory_rename_effects].
        destruct (memory_rename_effects e (S i) rest (memory_after e i a current))
          as [before output]; cbn [fst].
        rewrite Map.get_set_other by lia; reflexivity. }
  apply Hflow; intros j _; apply Hget.
Qed.

(** A node's assignment is the phi or final definition established while visiting that node. *)
Definition memory_node_assignment {N E T} (EN : encoding N) (phis : FinSet.t N)
    (effects : E -> list (memory_effect T)) (v : memory_dom_node N E) :
    option (memory_version N E) :=
  match v with
  | MemoryRoot => Some MemoryLive
  | MemoryBlock n => if FinSet.mem EN n phis then Some (MemoryPhi n) else None
  | MemoryEdge e => memory_edge_definition e 0 (effects e)
  end.

(** A dominator-stack visit processes the actual ordered effects at each edge node. *)
Definition memory_rename_visit {N E T} (EN : encoding N) (phis : FinSet.t N)
    (effects : E -> list (memory_effect T)) (v : memory_dom_node N E)
    (input : memory_version N E) : memory_rename_record N E :=
  match v with
  | MemoryRoot => MemoryRenameRecord input MemoryLive Map.empty
  | MemoryBlock n => MemoryRenameRecord input
      (if FinSet.mem EN n phis then MemoryPhi n else input) Map.empty
  | MemoryEdge e =>
    let '(before, output) := memory_rename_effects e 0 (effects e) input in
    MemoryRenameRecord input output before
  end.

Lemma memory_rename_visit_input {N E T} (EN : encoding N) phis
    (effects : E -> list (memory_effect T)) v input :
  memory_record_input (memory_rename_visit EN phis effects v input) = input.
Proof.
  destruct v as [|n|e]; cbn [memory_rename_visit memory_record_input]; try reflexivity.
  destruct (memory_rename_effects e 0 (effects e) input); reflexivity.
Qed.

Lemma memory_rename_visit_output {N E T} (EN : encoding N) phis
    (effects : E -> list (memory_effect T)) v input :
  memory_record_output (memory_rename_visit EN phis effects v input) =
    match memory_node_assignment EN phis effects v with
    | Some d => d
    | None => input
    end.
Proof.
  destruct v as [|n|e]; cbn [memory_rename_visit memory_node_assignment memory_record_output].
  - reflexivity.
  - destruct (FinSet.mem EN n phis); reflexivity.
  - pose proof (memory_rename_effects_output e 0 (effects e) input) as [Houtput Hlast].
    destruct (memory_rename_effects e 0 (effects e) input); cbn [snd] in Houtput.
    cbn [memory_record_output]; now rewrite Houtput, Hlast.
Qed.

(** * Explicit dominator stack *)

(** Pending frames save the inherited version, so sibling subtrees restore their scope. *)
Record memory_stack_state (V W R : Type) : Type := MemoryStackState {
  memory_stack_tasks : list (V * W);
  memory_stack_seen : FinSet.t V;
  memory_stack_records : Map.t V R
}.

Arguments MemoryStackState {V W R}.
Arguments memory_stack_tasks {V W R}.
Arguments memory_stack_seen {V W R}.
Arguments memory_stack_records {V W R}.

(** Initial frames all carry the live version and no node has yet been visited. *)
Definition memory_stack_start {V W R} (roots : list V) (live : W) : memory_stack_state V W R :=
  MemoryStackState (map (fun root => (root, live)) roots) FinSet.empty Map.empty.

(** A fresh frame is visited once; its children inherit its outgoing version. *)
Definition memory_stack_step {V W R} (EV : encoding V) (children : Map.t V (list V))
    (visit : V -> W -> R) (output : R -> W) (st : memory_stack_state V W R) :=
  match memory_stack_tasks st with
  | [] => st
  | (v, input) :: rest =>
    if FinSet.mem EV v (memory_stack_seen st) then
      MemoryStackState rest (memory_stack_seen st) (memory_stack_records st)
    else
      let record := visit v input in
      MemoryStackState
        (map (fun child => (child, output record)) (index_edges EV children v) ++ rest)
        (FinSet.add EV v (memory_stack_seen st))
        (Map.set EV v record (memory_stack_records st))
  end.

(** Binary blocks stop immediately after the saved-frame stack becomes empty. *)
Fixpoint memory_stack_run {V W R} (step : memory_stack_state V W R -> memory_stack_state V W R)
    (k : positive) (st : memory_stack_state V W R) : memory_stack_state V W R :=
  match memory_stack_tasks st with
  | [] => st
  | _ =>
    match k with
    | xH => step st
    | xO half => memory_stack_run step half (memory_stack_run step half st)
    | xI half => step (memory_stack_run step half (memory_stack_run step half st))
    end
  end.

(** Each unvisited parent binding pays for the child frame that it can still introduce. *)
Fixpoint memory_stack_credit {V} (EV : encoding V) (parents : list (V * V))
    (seen : FinSet.t V) : nat :=
  match parents with
  | [] => 0
  | (_, parent) :: rest =>
    if FinSet.mem EV parent seen then memory_stack_credit EV rest seen
    else S (memory_stack_credit EV rest seen)
  end.

Definition memory_stack_measure {V W R} (EV : encoding V) parents
    (st : memory_stack_state V W R) : nat :=
  length (memory_stack_tasks st) + memory_stack_credit EV parents (memory_stack_seen st).

Lemma memory_children_cons {V} (EV : encoding V) child parent parents v :
  index_edges EV (dom_children EV ((child, parent) :: parents)) v =
    if dfs_eq_dec EV v parent then child :: index_edges EV (dom_children EV parents) v
    else index_edges EV (dom_children EV parents) v.
Proof.
  cbn [dom_children]; unfold index_edges at 1.
  destruct (dfs_eq_dec EV v parent) as [Heq|Hne].
  - subst v; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma memory_stack_credit_spent {V} (EV : encoding V) parents seen v :
  FinSet.mem EV v seen = false ->
  memory_stack_credit EV parents (FinSet.add EV v seen) +
    length (index_edges EV (dom_children EV parents) v) = memory_stack_credit EV parents seen.
Proof.
  intro Hfresh; induction parents as [|[child parent] rest IH].
  - unfold index_edges; cbn [dom_children memory_stack_credit]; rewrite Map.get_empty; reflexivity.
  - rewrite memory_children_cons; cbn [memory_stack_credit]; rewrite dfs_mem_add.
    destruct (dfs_eq_dec EV v parent) as [Heq|Hne].
    + subst parent; destruct (dfs_eq_dec EV v v); [|congruence].
      rewrite Hfresh; cbn [length]; lia.
    + destruct (dfs_eq_dec EV parent v); [congruence|].
      destruct (FinSet.mem EV parent seen); cbn [length]; lia.
Qed.

Lemma memory_stack_credit_empty {V} (EV : encoding V) parents :
  memory_stack_credit EV parents FinSet.empty = length parents.
Proof.
  induction parents as [|[child parent] rest IH]; cbn [memory_stack_credit length];
    [reflexivity|rewrite FinSet.mem_empty, IH; reflexivity].
Qed.

Lemma memory_stack_step_decreases {V W R} (EV : encoding V) parents
    (visit : V -> W -> R) output st : memory_stack_tasks st <> [] ->
  memory_stack_measure EV parents
    (memory_stack_step EV (dom_children EV parents) visit output st) <
    memory_stack_measure EV parents st.
Proof.
  destruct st as [[|[v input] rest] seen records]; [contradiction|]; intro Hpending.
  unfold memory_stack_measure, memory_stack_step.
  cbn [memory_stack_tasks memory_stack_seen memory_stack_records].
  destruct (FinSet.mem EV v seen) eqn:Hseen; cbn [memory_stack_tasks memory_stack_seen length].
  - lia.
  - rewrite length_app, length_map.
    pose proof (memory_stack_credit_spent EV parents seen v Hseen); lia.
Qed.

Lemma memory_stack_run_agrees {V W R} step :
  (forall st : memory_stack_state V W R, memory_stack_tasks st = [] -> step st = st) ->
  forall k st, memory_stack_run step k st = Pos.iter step st k.
Proof.
  intro Hempty.
  assert (Hfixed : forall st k, memory_stack_tasks st = [] -> Pos.iter step st k = st).
  { intros st k Htasks; induction k using Pos.peano_ind.
    - apply Hempty; exact Htasks.
    - rewrite Pos.iter_succ, IHk; apply Hempty; exact Htasks. }
  intro k; induction k as [k IH|k IH|]; intros [[|task rest] seen records].
  - symmetry; apply Hfixed; reflexivity.
  - cbn [memory_stack_run memory_stack_tasks]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO k)).
  - symmetry; apply Hfixed; reflexivity.
  - cbn [memory_stack_run memory_stack_tasks].
    rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - symmetry; apply Hfixed; reflexivity.
  - reflexivity.
Qed.

Lemma memory_stack_iter_bound {V W R} (EV : encoding V) parents step :
  (forall st : memory_stack_state V W R, memory_stack_tasks st = [] -> step st = st) ->
  (forall st, memory_stack_tasks st <> [] ->
    memory_stack_measure EV parents (step st) < memory_stack_measure EV parents st) ->
  forall k st, memory_stack_tasks (Pos.iter step st k) = [] \/
    memory_stack_measure EV parents (Pos.iter step st k) + Pos.to_nat k <=
      memory_stack_measure EV parents st.
Proof.
  intros Hempty Hstep k; induction k using Pos.peano_ind; intro st.
  - cbn [Pos.iter]; destruct (memory_stack_tasks st) as [|task rest] eqn:Htasks.
    + left; rewrite Hempty by exact Htasks; exact Htasks.
    + right; pose proof (Hstep st ltac:(rewrite Htasks; discriminate)).
      cbn [Pos.to_nat]; lia.
  - rewrite Pos.iter_succ; destruct (IHk st) as [Hdone|Hbound].
    + left; rewrite Hempty by exact Hdone; exact Hdone.
    + destruct (memory_stack_tasks (Pos.iter step st k)) as [|task rest] eqn:Htasks.
      * left; rewrite Hempty by exact Htasks; exact Htasks.
      * right; pose proof (Hstep (Pos.iter step st k)
          ltac:(rewrite Htasks; discriminate)).
        rewrite Pos2Nat.inj_succ; lia.
Qed.

(** A nearest assignment is below every other assignment dominating the same node. *)
Definition memory_nearest {V E W} (g : Graph.t V E) (assign : V -> option W) n w : Prop :=
  exists d, assign d = Some w /\ dominates g d n /\
    forall d' w', assign d' = Some w' -> dominates g d' n -> dominates g d' d.

Section StackProof.
Context {V E W R : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.
Variable (assign : V -> option W) (live : W) (visit : V -> W -> R) (output : R -> W).
Hypothesis Hvisit : forall n w, output (visit n w) =
  match assign n with Some d => d | None => w end.
Hypothesis Hroot : forall n, reachable g n ->
  Map.get EV n (idom (dominator_tree p)) = None -> assign n = Some live.

Local Abbreviation parents := (idom (dominator_tree p)).
Local Abbreviation bindings := (Map.elements parents).
Local Abbreviation children := (dom_children EV bindings).

(** A saved frame carries the nearest assignment of its parent, or live at a root. *)
Definition memory_stack_inherited n w : Prop :=
  match Map.get EV n parents with
  | Some parent => memory_nearest g assign parent w
  | None => w = live
  end.

Lemma memory_nearest_visit n w : reachable g n -> memory_stack_inherited n w ->
  memory_nearest g assign n (output (visit n w)).
Proof.
  intros Hn Hinherited; rewrite Hvisit.
  destruct (assign n) as [d|] eqn:Hassign.
  - exists n; split; [exact Hassign|split; [apply dominates_refl|]].
    intros d' w' _ Hdom; exact Hdom.
  - unfold memory_stack_inherited in Hinherited.
    destruct (Map.get EV n parents) as [parent|] eqn:Hparent.
    + destruct Hinherited as [d [Hd [Hdom Hnearest]]].
      destruct (dominator_tree_with_exact EV g p Hready SimpleLT) as [_ [Hexact _]].
      pose proof (proj1 (Hexact parent n Hn) Hparent) as [[Hpn Hpne] Himmediate].
      exists d; split; [exact Hd|split].
      * eapply dominates_trans; eassumption.
      * intros d' w' Hd' Hdn; apply Hnearest with w'; [exact Hd'|].
        apply Himmediate; split; [exact Hdn|].
        intro Heq; subst d'; congruence.
    + pose proof (Hroot n Hn Hparent); congruence.
Qed.

Lemma memory_nearest_unique n x y : reachable g n -> memory_nearest g assign n x ->
  memory_nearest g assign n y -> x = y.
Proof.
  intros Hn [a [Ha [Han Hnearest_a]]] [b [Hb [Hbn Hnearest_b]]].
  assert (Hab : dominates g a b) by (eapply Hnearest_b; eassumption).
  assert (Hba : dominates g b a) by (eapply Hnearest_a; eassumption).
  assert (Ha_reach : reachable g a) by (eapply dom_dominator_reachable; eassumption).
  assert (Hb_reach : reachable g b) by (eapply dom_dominator_reachable; eassumption).
  pose proof (idf_dominance_antisym EV g p Hready a b Ha_reach Hb_reach Hab Hba) as Heq.
  subst b; congruence.
Qed.

(** Records reflect actual visits; pending scopes and missing-node coverage survive each step. *)
Record memory_stack_invariant (st : memory_stack_state V W R) : Prop := {
  memory_stack_domain : forall n, FinSet.mem EV n (memory_stack_seen st) = true <->
    exists record, Map.get EV n (memory_stack_records st) = Some record;
  memory_stack_recorded : forall n record,
    Map.get EV n (memory_stack_records st) = Some record -> reachable g n /\
      exists input, record = visit n input /\ memory_stack_inherited n input;
  memory_stack_pending : forall n input, In (n, input) (memory_stack_tasks st) ->
    reachable g n /\ memory_stack_inherited n input;
  memory_stack_coverage : forall n, reachable g n ->
    FinSet.mem EV n (memory_stack_seen st) = false ->
    In n (map fst (memory_stack_tasks st)) \/
      exists parent, Map.get EV n parents = Some parent /\
        FinSet.mem EV parent (memory_stack_seen st) = false
}.

Lemma memory_stack_children n child :
  In child (index_edges EV children n) <-> Map.get EV child parents = Some n.
Proof.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap _].
  rewrite dom_children_in; split.
  - apply Map.elements_sound; exact Hmap.
  - apply Map.elements_complete; exact Hmap.
Qed.

(** Visiting a parent transfers missing-node coverage to its newly pushed child frames. *)
Lemma memory_stack_push_coverage n (input : W) (rest : list (V * W)) seen (outgoing : W) :
  (forall v, reachable g v -> FinSet.mem EV v seen = false ->
    In v (map fst ((n, input) :: rest)) \/
      exists parent, Map.get EV v parents = Some parent /\ FinSet.mem EV parent seen = false) ->
  forall v, reachable g v -> FinSet.mem EV v (FinSet.add EV n seen) = false ->
    In v (map fst
      (map (fun child => (child, outgoing)) (index_edges EV children n) ++ rest)) \/
      exists parent, Map.get EV v parents = Some parent /\
        FinSet.mem EV parent (FinSet.add EV n seen) = false.
Proof.
  intros Hcoverage v Hv Hfresh.
  assert (Hvn : v <> n).
  { intro Heq; subst v; assert (Hmem : FinSet.mem EV n (FinSet.add EV n seen) = true)
      by (apply FinSet.mem_add; left; reflexivity); congruence. }
  assert (Hold : FinSet.mem EV v seen = false).
  { apply Bool.not_true_iff_false; intro Hmem.
    assert (Hnew : FinSet.mem EV v (FinSet.add EV n seen) = true)
      by (apply FinSet.mem_add; right; exact Hmem); congruence. }
  destruct (Hcoverage v Hv Hold) as [[Heq|Hin]|[parent [Hparent Hparent_fresh]]].
  - cbn [fst] in Heq; subst v; contradiction.
  - left; rewrite map_app; apply in_or_app; right; exact Hin.
  - destruct (dfs_eq_dec EV parent n) as [Heq|Hne].
    + subst parent; left; rewrite map_app; apply in_or_app; left.
      apply in_map_iff; exists (v, outgoing); split; [reflexivity|].
      apply in_map_iff; exists v; split; [reflexivity|].
      apply memory_stack_children; exact Hparent.
    + right; exists parent; split; [exact Hparent|].
      apply Bool.not_true_iff_false; rewrite FinSet.mem_add; intros [Heq|Hmem];
        [contradiction|congruence].
Qed.

Lemma memory_stack_invariant_step st : memory_stack_invariant st ->
  memory_stack_invariant (memory_stack_step EV children visit output st).
Proof.
  intros Hinv; destruct st as [[|[n input] rest] seen records]; [exact Hinv|].
  destruct Hinv as [Hdomain Hrecorded Hpending Hcoverage].
  cbn [memory_stack_tasks memory_stack_seen memory_stack_records] in *.
  unfold memory_stack_step; cbn [memory_stack_tasks memory_stack_seen memory_stack_records].
  destruct (FinSet.mem EV n seen) eqn:Hseen.
  - constructor; cbn [memory_stack_tasks memory_stack_seen memory_stack_records].
    + exact Hdomain.
    + exact Hrecorded.
    + intros v w Hin; apply Hpending; right; exact Hin.
    + intros v Hv Hfresh; destruct (Hcoverage v Hv Hfresh) as [[Heq|Hin]|Hparent].
      * cbn [fst] in Heq; subst v; congruence.
      * left; exact Hin.
      * right; exact Hparent.
  - destruct (Hpending n input (or_introl eq_refl)) as [Hn Hinput].
    pose proof (memory_nearest_visit n input Hn Hinput) as Hnearest.
    constructor; cbn [memory_stack_tasks memory_stack_seen memory_stack_records].
    + intro v; rewrite FinSet.mem_add; split.
      * intros [Heq|Hmem].
        -- subst v; eexists; apply Map.get_set_same.
        -- apply Hdomain in Hmem; destruct Hmem as [record Hget].
           destruct (dfs_eq_dec EV v n) as [Heq|Hne].
           ++ subst v; eexists; apply Map.get_set_same.
           ++ exists record; rewrite Map.get_set_other by exact Hne; exact Hget.
      * intros [record Hget]; destruct (dfs_eq_dec EV v n) as [Heq|Hne]; [left; exact Heq|].
        right; apply Hdomain; exists record; rewrite Map.get_set_other in Hget by exact Hne.
        exact Hget.
    + intros v record Hget; destruct (dfs_eq_dec EV v n) as [Heq|Hne].
      * subst v; rewrite Map.get_set_same in Hget; inversion Hget; subst record.
        split; [exact Hn|exists input; split; [reflexivity|exact Hinput]].
      * rewrite Map.get_set_other in Hget by exact Hne; exact (Hrecorded v record Hget).
    + intros v w Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin; destruct Hin as [child [Heq Hchild]].
        inversion Heq; subst child w; apply memory_stack_children in Hchild.
        destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hparent_domain _] _]].
        split; [exact (proj1 (Hparent_domain v n Hchild))|].
        unfold memory_stack_inherited; rewrite Hchild; exact Hnearest.
      * apply Hpending; right; exact Hin.
    + apply (memory_stack_push_coverage n input rest seen (output (visit n input))).
      exact Hcoverage.
Qed.

Lemma memory_stack_invariant_start roots :
  (forall n, In n roots <-> reachable g n /\ Map.get EV n parents = None) ->
  memory_stack_invariant (memory_stack_start roots live).
Proof.
  intro Hroots; constructor; cbn [memory_stack_start memory_stack_seen memory_stack_records
    memory_stack_tasks].
  - intro n; rewrite FinSet.mem_empty, Map.get_empty; split;
      [discriminate|intros [record Hfalse]; discriminate].
  - intros n record Hfalse; rewrite Map.get_empty in Hfalse; discriminate.
  - intros n input Hin; apply in_map_iff in Hin; destruct Hin as [root [Heq Hin]].
    inversion Heq; subst root input; apply Hroots in Hin; destruct Hin as [Hn Hparent].
    split; [exact Hn|unfold memory_stack_inherited; rewrite Hparent; reflexivity].
  - intros n Hn _; destruct (Map.get EV n parents) as [parent|] eqn:Hparent.
    + right; exists parent; split; [reflexivity|apply FinSet.mem_empty].
    + left; apply in_map_iff; exists (n, live); split; [reflexivity|].
      apply in_map_iff; exists n; split; [reflexivity|apply Hroots; split; assumption].
Qed.

Lemma memory_stack_invariant_iter st k : memory_stack_invariant st ->
  memory_stack_invariant (Pos.iter (memory_stack_step EV children visit output) st k).
Proof.
  intro Hinv; induction k using Pos.peano_ind.
  - apply memory_stack_invariant_step; exact Hinv.
  - rewrite Pos.iter_succ; apply memory_stack_invariant_step; exact IHk.
Qed.

(** An empty stack has materialized every reachable node, with its actual inherited scope. *)
Lemma memory_stack_complete st : memory_stack_invariant st -> memory_stack_tasks st = [] ->
  forall n, reachable g n -> exists record input,
    Map.get EV n (memory_stack_records st) = Some record /\ record = visit n input /\
      memory_stack_inherited n input /\ memory_nearest g assign n (output record).
Proof.
  intros Hinv Hdone.
  destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hparent_domain Hforest] _]].
  assert (Hseen : forall n, reachable g n -> FinSet.mem EV n (memory_stack_seen st) = true).
  { refine (well_founded_ind Hforest
      (fun n => reachable g n -> FinSet.mem EV n (memory_stack_seen st) = true) _).
    intros n IH Hn.
    destruct (FinSet.mem EV n (memory_stack_seen st)) eqn:Hmem; [reflexivity|].
    destruct (memory_stack_coverage _ Hinv n Hn Hmem) as [Hin|[parent [Hparent Hfresh]]].
    - rewrite Hdone in Hin; contradiction.
    - pose proof (IH parent Hparent (proj2 (Hparent_domain n parent Hparent))); congruence. }
  intros n Hn; pose proof (Hseen n Hn) as Hmem.
  apply (memory_stack_domain _ Hinv) in Hmem; destruct Hmem as [record Hget].
  destruct (memory_stack_recorded _ Hinv n record Hget) as [_ [input [Heq Hinput]]].
  exists record, input; split; [exact Hget|split; [exact Heq|split; [exact Hinput|]]].
  rewrite Heq; apply memory_nearest_visit; assumption.
Qed.

(** The number of initial roots and parent bindings bounds all explicit-stack transitions. *)
Lemma memory_stack_run_complete roots :
  (forall n, In n roots <-> reachable g n /\ Map.get EV n parents = None) ->
  let initial : memory_stack_state V W R := memory_stack_start roots live in
  let step := memory_stack_step EV children visit output in
  let final := memory_stack_run step (Pos.of_succ_nat (length roots + length bindings)) initial in
  memory_stack_tasks final = [] /\ memory_stack_invariant final.
Proof.
  intro Hroots; cbn zeta.
  assert (Hempty : forall st : memory_stack_state V W R,
      memory_stack_tasks st = [] -> memory_stack_step EV children visit output st = st).
  { intros st Htasks; unfold memory_stack_step; rewrite Htasks; reflexivity. }
  rewrite memory_stack_run_agrees by exact Hempty.
  split.
  - destruct (memory_stack_iter_bound EV bindings _ Hempty
      (memory_stack_step_decreases EV bindings visit output)
      (Pos.of_succ_nat (length roots + length bindings))
      (memory_stack_start roots live)) as [Hdone|Hbound]; [exact Hdone|].
    unfold memory_stack_measure, memory_stack_start in Hbound.
    cbn [memory_stack_tasks memory_stack_seen] in Hbound.
    rewrite length_map, memory_stack_credit_empty, SuccNat2Pos.id_succ in Hbound; lia.
  - apply memory_stack_invariant_iter, memory_stack_invariant_start; exact Hroots.
Qed.

End StackProof.

(** If a target has no assignment or phi, all incoming renamed versions coincide. *)
Lemma memory_nearest_no_phi {V E W} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (assign : V -> option W) defs e x y :
  ready EV g p ->
  (forall d w, reachable g d -> assign d = Some w -> In d defs \/ in_idf g defs d) ->
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) ->
  assign (Graph.target g e) = None -> ~ in_idf g defs (Graph.target g e) ->
  memory_nearest g assign (Graph.source g e) x ->
  memory_nearest g assign (Graph.target g e) y -> x = y.
Proof.
  intros Hready Hseed Hedge Hsource Hnone Hnot
    [a [Ha [Has Hnearest_a]]] [b [Hb [Hbt Hnearest_b]]].
  assert (Hat : strictly_dominates g a (Graph.target g e)).
  { destruct (dfs_eq_dec EV a (Graph.target g e)) as [Heq|Hne].
    - subst a; congruence.
    - split; [|exact Hne].
      destruct (dominates_b EV (dominator_tree p) a (Graph.target g e)) eqn:Hdom.
      + apply (proj1 (proj1 (dominator_tree_with_exact EV g p Hready SimpleLT)
          a (Graph.target g e) (reachable_step e Hsource Hedge))); exact Hdom.
      + exfalso; apply Hnot; apply (idf_step a (Graph.target g e)).
        * apply (Hseed a x); [eapply dom_dominator_reachable; eassumption|exact Ha].
        * exists e; split; [exact Hedge|split; [reflexivity|split; [exact Hsource|]]].
          split; [exact Has|]; intros [Hstrict _].
          apply (proj2 (proj1 (dominator_tree_with_exact EV g p Hready SimpleLT)
            a (Graph.target g e) (reachable_step e Hsource Hedge))) in Hstrict.
          change (dominates_b EV (dominator_tree p) a (Graph.target g e) = true) in Hstrict.
          congruence. }
  assert (Hbs : dominates g b (Graph.source g e)).
  { apply (idf_strict_predecessor g b e Hedge).
    split; [exact Hbt|intro Heq; subst b; congruence]. }
  assert (Hab : dominates g a b) by (eapply Hnearest_b; [exact Ha|exact (proj1 Hat)]).
  assert (Hba : dominates g b a) by (eapply Hnearest_a; [exact Hb|exact Hbs]).
  assert (Har : reachable g a) by (eapply dom_dominator_reachable; eassumption).
  assert (Hbr : reachable g b) by (eapply dom_dominator_reachable; eassumption).
  pose proof (idf_dominance_antisym EV g p Hready a b Har Hbr Hab Hba) as Heq.
  subst b; congruence.
Qed.

(** * Construction inventories *)

Lemma memory_edge_definition_witness {N E T} (e : E) i
    (effects : list (memory_effect T)) (d : memory_version N E) :
  memory_edge_definition e i effects = Some d -> exists j a,
    d = MemoryDef e (i + j) /\ nth_error effects j = Some a /\ effect_is_def a = true.
Proof.
  revert i; induction effects as [|a rest IH]; intros i Hdef; [discriminate|].
  cbn [memory_edge_definition] in Hdef.
  destruct (memory_edge_definition e (S i) rest) as [last|] eqn:Hrest.
  - inversion Hdef; subst last; destruct (IH (S i) Hrest) as [j [b [Heq [Hb Hdefb]]]].
    exists (S j), b; split; [rewrite Heq; f_equal; lia|split; assumption].
  - destruct (effect_is_def a) eqn:Ha; [|discriminate].
    inversion Hdef; subst d; exists 0, a; rewrite Nat.add_0_r; auto.
Qed.

(** Definition inventories retain every defining position, including earlier writes on an edge. *)
Fixpoint memory_edge_versions {N E T} (e : E) (i : nat)
    (effects : list (memory_effect T)) : list (memory_version N E) :=
  match effects with
  | [] => []
  | a :: rest =>
    if effect_is_def a then MemoryDef e i :: memory_edge_versions e (S i) rest
    else memory_edge_versions e (S i) rest
  end.

Lemma memory_edge_versions_exact {N E T} (e : E) i
    (effects : list (memory_effect T)) (d : memory_version N E) :
  In d (memory_edge_versions e i effects) <-> exists j a,
    d = MemoryDef e (i + j) /\ nth_error effects j = Some a /\ effect_is_def a = true.
Proof.
  revert i; induction effects as [|a rest IH]; intro i; cbn [memory_edge_versions].
  - split; [contradiction|intros [j [b [_ [Hfalse _]]]]; destruct j; discriminate].
  - destruct (effect_is_def a) eqn:Ha.
    + cbn [In]; rewrite IH; split.
      * intros [Heq|[j [b [Heq [Hb Hdefb]]]]].
        -- exists 0, a; rewrite Nat.add_0_r; auto.
        -- exists (S j), b; split; [rewrite Heq; f_equal; lia|auto].
      * intros [[|j] [b [Heq [Hb Hdefb]]]].
        -- cbn [nth_error] in Hb; inversion Hb; subst b; left.
           rewrite Nat.add_0_r in Heq; symmetry; exact Heq.
        -- right; exists j, b; split; [rewrite Heq; f_equal; lia|auto].
    + rewrite IH; split.
      * intros [j [b [Heq [Hb Hdefb]]]]; exists (S j), b.
        split; [rewrite Heq; f_equal; lia|auto].
      * intros [[|j] [b [Heq [Hb Hdefb]]]].
        -- cbn [nth_error] in Hb; inversion Hb; subst b; congruence.
        -- exists j, b; split; [rewrite Heq; f_equal; lia|auto].
Qed.

(** Stable structural version identifiers have injective codes independent of allocation sites. *)
Definition memory_frontier_version_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (memory_version N E).
Proof.
  let ED := constr:(pair_encoding EE nat_encoding) in
  refine (Encoding _ (fun d => match d with
    | MemoryLive => xH
    | MemoryPhi n => xO (encode EN n)
    | MemoryDef e i => xI (encode ED (e, i))
    end) _).
  intros [|n|e i] [|n'|e' i'] Heq; cbn in Heq; try discriminate; try reflexivity.
  - injection Heq as Heq; f_equal; apply (encode_injective EN); exact Heq.
  - injection Heq as Heq.
    change (encode (pair_encoding EE nat_encoding) (e, i) =
      encode (pair_encoding EE nat_encoding) (e', i')) in Heq.
    apply (encode_injective (pair_encoding EE nat_encoding)) in Heq.
    inversion Heq; reflexivity.
Defined.

(** Materialization builds a function-valued result index once from its finite key list. *)
Definition memory_result_index {K A} (EK : encoding K) (value : K -> A) (keys : list K) :
    Map.t K A := fold_right (fun k m => Map.set EK k (value k) m) Map.empty keys.

Lemma memory_result_index_get {K A} (EK : encoding K) (value : K -> A) keys k :
  Map.get EK k (memory_result_index EK value keys) =
    if existsb (fun key => Pos.eqb (encode EK k) (encode EK key)) keys
    then Some (value k) else None.
Proof.
  unfold memory_result_index; induction keys as [|key rest IH]; cbn [fold_right existsb].
  - apply Map.get_empty.
  - destruct (dfs_eq_dec EK k key) as [Heq|Hne].
    + subst key; rewrite Map.get_set_same, Pos.eqb_refl; reflexivity.
    + rewrite Map.get_set_other by exact Hne.
      assert (Hcode : Pos.eqb (encode EK k) (encode EK key) = false).
      { apply Pos.eqb_neq; intro Heq; apply Hne, (encode_injective EK); exact Heq. }
      rewrite Hcode; exact IH.
Qed.

Lemma memory_result_index_domain {K A} (EK : encoding K) (value : K -> A) keys k :
  (exists a, Map.get EK k (memory_result_index EK value keys) = Some a) <-> In k keys.
Proof.
  rewrite memory_result_index_get.
  destruct (existsb (fun key => Pos.eqb (encode EK k) (encode EK key)) keys) eqn:Hmem.
  - apply existsb_exists in Hmem; destruct Hmem as [key [Hin Heq]].
    apply Pos.eqb_eq, (encode_injective EK) in Heq; subst key.
    split; [intros _; exact Hin|intros _; eexists; reflexivity].
  - split; [intros [a Hfalse]; discriminate|intro Hin].
    assert (Htrue : existsb (fun key => Pos.eqb (encode EK k) (encode EK key)) keys = true).
    { apply existsb_exists; exists k; split; [exact Hin|apply Pos.eqb_refl]. }
    congruence.
Qed.

Lemma memory_result_index_at {K A} (EK : encoding K) (value : K -> A) keys k :
  In k keys -> Map.get EK k (memory_result_index EK value keys) = Some (value k).
Proof.
  intro Hin; rewrite memory_result_index_get.
  assert (Htrue : existsb (fun key => Pos.eqb (encode EK k) (encode EK key)) keys = true).
  { apply existsb_exists; exists k; split; [exact Hin|apply Pos.eqb_refl]. }
  rewrite Htrue; reflexivity.
Qed.

(** The synthetic root dominates every split node and is the forest's only root. *)
Lemma memory_dom_root_exact {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> forall v,
  (In v [MemoryRoot] <-> reachable (memory_dom_graph EN EE g) v /\
    Map.get (memory_dom_node_encoding EN EE) v
      (idom (dominator_tree (prepare (memory_dom_node_encoding EN EE)
        (memory_dom_graph EN EE g)))) = None).
Proof.
  intros Hwf v.
  pose proof (memory_dom_ready EN EE g Hwf) as Hready.
  destruct (dominator_tree_with_exact _ _ _ Hready SimpleLT) as [_ [_ Hroots]].
  assert (Hroot : reachable (memory_dom_graph EN EE g) MemoryRoot).
  { apply reachable_entry; left; reflexivity. }
  assert (Hdominates : forall n, dominates (memory_dom_graph EN EE g) MemoryRoot n).
  { intros n s es [Heq|Hfalse] _; [left; exact Heq|contradiction]. }
  split.
  - intros [Heq|Hfalse]; [subst v|contradiction]; split; [exact Hroot|].
    apply (proj2 (Hroots MemoryRoot Hroot)); intros d [Hd Hne].
    destruct (Hd MemoryRoot [] (or_introl eq_refl) (path_nil MemoryRoot))
      as [Heq|[e [Hfalse _]]]; [contradiction|contradiction].
  - intros [Hv Hnone].
    destruct (dfs_eq_dec (memory_dom_node_encoding EN EE) v MemoryRoot) as [Heq|Hne].
    + left; symmetry; exact Heq.
    + exfalso; apply (proj1 (Hroots v Hv) Hnone MemoryRoot).
      split; [apply Hdominates|congruence].
Qed.

(** A reachable synthetic edge's immediate dominator is its original source block. *)
Lemma memory_dom_edge_parent {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) e : graph_wf g ->
  reachable (memory_dom_graph EN EE g) (MemoryEdge e) ->
  Map.get (memory_dom_node_encoding EN EE) (MemoryEdge e)
    (idom (dominator_tree (prepare (memory_dom_node_encoding EN EE)
      (memory_dom_graph EN EE g)))) = Some (MemoryBlock (Graph.source g e)).
Proof.
  intros Hwf He; pose proof (memory_dom_ready EN EE g Hwf) as Hready.
  destruct (dominator_tree_with_exact _ _ _ Hready SimpleLT) as [_ [Hparents _]].
  apply (proj2 (Hparents _ _ He)); split.
  - split; [apply memory_dom_edge_dominated|discriminate].
  - intros d Hd; apply (idf_strict_predecessor (memory_dom_graph EN EE g) d (MemoryBegin e)).
    + apply memory_dom_edge_reachable in He; [|exact Hwf].
      destruct He as [Hsource Hedge]; apply memory_dom_begin_in; [exact Hwf|split; [|exact Hedge]].
      exact (reachable_in_nodes g _ Hwf Hsource).
    + exact Hd.
Qed.

(** * Shared preparation and result materialization *)

(** This record carries the finite products of one frontier query and one stack traversal. *)
Record memory_frontier_state (N E : Type) : Type := MemoryFrontierState {
  memory_frontier_phis : list N;
  memory_frontier_phi_set : FinSet.t N;
  memory_frontier_edges : list E;
  memory_frontier_records : Map.t (memory_dom_node N E) (memory_rename_record N E)
}.

Arguments MemoryFrontierState {N E}.
Arguments memory_frontier_phis {N E}.
Arguments memory_frontier_phi_set {N E}.
Arguments memory_frontier_edges {N E}.
Arguments memory_frontier_records {N E}.

(** One prepared split graph feeds the live search, exact LT tree, direct IDF and stack. *)
Definition memory_frontier_prepare {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) : memory_frontier_state N E :=
  let sg := memory_dom_graph EN EE g in
  let ED := memory_dom_node_encoding EN EE in
  let sp := prepare ED sg in
  let live := visited (dfs sp FinSet.empty (Graph.entries sg)) in
  let all_edges := memory_dom_edge_tags (Graph.nodes sg) in
  let edges := filter (fun e => FinSet.mem ED (MemoryEdge e) live) all_edges in
  let defs := memory_dom_defs_from all_edges effects live ED in
  let tree := dominator_tree_with sp SimpleLT in
  let placements := direct_idf sp tree defs in
  let phis := filter (fun n => FinSet.mem ED (MemoryBlock n) placements) (Graph.nodes g) in
  let phi_set := FinSet.of_list EN phis in
  let bindings := Map.elements (idom tree) in
  let children := dom_children ED bindings in
  let step := memory_stack_step ED children (memory_rename_visit EN phi_set effects)
    memory_record_output in
  let initial := memory_stack_start [MemoryRoot] MemoryLive in
  let final := memory_stack_run step (Pos.of_succ_nat (1 + length bindings)) initial in
  MemoryFrontierState phis phi_set edges (memory_stack_records final).

(** Missing nodes have an empty occurrence index and the harmless total live default. *)
Definition memory_frontier_record {N E} (ED : encoding (memory_dom_node N E))
    (records : Map.t (memory_dom_node N E) (memory_rename_record N E)) node :
    memory_rename_record N E :=
  match Map.get ED node records with
  | Some record => record
  | None => MemoryRenameRecord MemoryLive MemoryLive Map.empty
  end.

(** Operand keys retain each exact incoming identity, including virtual entry operands. *)
Definition memory_frontier_operand_keys {N E} (EN : encoding N) (g : Graph.t N E)
    (phis : FinSet.t N) (edges : list E) : list (N * option E) :=
  map (fun n => (n, None)) (filter (fun n => FinSet.mem EN n phis) (Graph.entries g)) ++
  map (fun e => (Graph.target g e, Some e))
    (filter (fun e => FinSet.mem EN (Graph.target g e) phis) edges).

(** Result fields read prepared tries; all finite inventories and operands are built once. *)
Definition memory_frontier_materialize {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (state : memory_frontier_state N E) :
    memory_graph N E :=
  let ED := memory_dom_node_encoding EN EE in
  let phis := memory_frontier_phis state in
  let edges := memory_frontier_edges state in
  let records := memory_frontier_records state in
  let record := memory_frontier_record ED records in
  let output := fun e => memory_record_output (record (MemoryEdge e)) in
  let phi_set := memory_frontier_phi_set state in
  let versions := memory_distinct (memory_frontier_version_encoding EN EE)
    (MemoryLive :: map MemoryPhi phis ++
      flat_map (fun e => memory_edge_versions e 0 (effects e)) edges) in
  let keys := memory_frontier_operand_keys EN g phi_set edges in
  let operands := memory_result_index (pair_encoding EN (option_encoding EE))
    (fun key => match snd key with None => MemoryLive | Some e => output e end) keys in
  MemoryGraph phis versions
    (fun n => memory_record_output (record (MemoryBlock n)))
    (fun e i => Map.get nat_encoding i (memory_record_before (record (MemoryEdge e))))
    output (fun n k => Map.get (pair_encoding EN (option_encoding EE)) (n, k) operands).

(** The proof-free computation is shared by the dependent public builder and its observations. *)
Definition memory_frontier_data {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) : memory_graph N E :=
  memory_frontier_materialize EN EE g effects (memory_frontier_prepare EN EE g effects).

Section FrontierProof.
Context {N E T : Type} (EN : encoding N) (EE : encoding E) (g : Graph.t N E).
Variable effects : E -> list (memory_effect T).
Hypothesis Hwf : graph_wf g.

Local Abbreviation ED := (memory_dom_node_encoding EN EE).
Local Abbreviation sg := (memory_dom_graph EN EE g).
Local Abbreviation sp := (prepare ED sg).
Local Abbreviation tree := (dominator_tree sp).
Local Abbreviation live := (visited (dfs sp FinSet.empty (Graph.entries sg))).
Local Abbreviation defs := (memory_dom_defs EN EE g effects).
Local Abbreviation placements := (direct_idf sp tree defs).
Local Abbreviation phis :=
  (filter (fun n => FinSet.mem ED (MemoryBlock n) placements) (Graph.nodes g)).
Local Abbreviation phi_set := (FinSet.of_list EN phis).
Local Abbreviation edges :=
  (filter (fun e => FinSet.mem ED (MemoryEdge e) live) (memory_dom_edge_tags (Graph.nodes sg))).
Local Abbreviation assign := (memory_node_assignment EN phi_set effects).
Local Abbreviation visit := (memory_rename_visit EN phi_set effects).
Local Abbreviation bindings := (Map.elements (idom tree)).
Local Abbreviation children := (dom_children ED bindings).
Local Abbreviation initial :=
  (@memory_stack_start (memory_dom_node N E) (memory_version N E)
    (memory_rename_record N E) [MemoryRoot] MemoryLive).
Local Abbreviation step := (memory_stack_step ED children visit memory_record_output).
Local Abbreviation final :=
  (memory_stack_run step (Pos.of_succ_nat (1 + length bindings)) initial).
Local Abbreviation records := (memory_stack_records final).
Local Abbreviation record_at := (memory_frontier_record ED records).
Local Abbreviation mg := (memory_frontier_data EN EE g effects).

Lemma memory_frontier_ready : ready ED sg sp.
Proof.
  apply memory_dom_ready; exact Hwf.
Qed.

Lemma memory_frontier_phi_in n : In n phis <-> in_idf sg defs (MemoryBlock n).
Proof.
  change (In n (filter (fun n => FinSet.mem ED (MemoryBlock n) placements) (Graph.nodes g))
    <-> in_idf sg defs (MemoryBlock n)).
  rewrite filter_In.
  rewrite (direct_idf_exact ED sg sp defs (MemoryBlock n) memory_frontier_ready).
  split; [tauto|intro Hphi; split; [|exact Hphi]].
  destruct (memory_dom_idf_block EN EE g effects (MemoryBlock n) Hwf Hphi)
    as [m [Heq Hm]]; inversion Heq; subst m.
  exact (reachable_in_nodes g n Hwf Hm).
Qed.

Lemma memory_frontier_phi_reaches n : In n phis -> reachable g n.
Proof.
  intro Hphi; apply memory_frontier_phi_in in Hphi.
  destruct (memory_dom_idf_block EN EE g effects (MemoryBlock n) Hwf Hphi)
    as [m [Heq Hm]]; inversion Heq; subst m; exact Hm.
Qed.

Lemma memory_frontier_edges_in e : In e edges <->
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e).
Proof.
  change (In e (filter (fun e => FinSet.mem ED (MemoryEdge e) live)
    (memory_dom_edge_tags (Graph.nodes sg))) <->
    In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e)).
  rewrite filter_In, memory_dom_edge_tags_exact, memory_distinct_in.
  rewrite (reachable_dfs ED sg sp (MemoryEdge e) memory_frontier_ready).
  rewrite (memory_dom_edge_reachable EN EE g e Hwf); split; [tauto|].
  intros [Hedge Hsource]; split; [|tauto].
  eapply edges_of_in; [exact (reachable_in_nodes g _ Hwf Hsource)|exact Hedge].
Qed.

Lemma memory_frontier_root_assignment v : reachable sg v ->
  Map.get ED v (idom tree) = None -> assign v = Some MemoryLive.
Proof.
  intros Hv Hparent.
  destruct (proj2 (memory_dom_root_exact EN EE g Hwf v) (conj Hv Hparent))
    as [Heq|Hfalse]; [subst v; reflexivity|contradiction].
Qed.

Lemma memory_frontier_final : memory_stack_tasks final = [] /\
  memory_stack_invariant ED sg sp assign MemoryLive visit final.
Proof.
  apply (memory_stack_run_complete ED sg sp memory_frontier_ready assign MemoryLive
    visit memory_record_output (memory_rename_visit_output EN phi_set effects)
    memory_frontier_root_assignment [MemoryRoot]).
  apply memory_dom_root_exact; exact Hwf.
Qed.

Lemma memory_frontier_recorded v : reachable sg v -> exists input,
  Map.get ED v records = Some (visit v input) /\
    memory_stack_inherited ED sg sp assign MemoryLive v input /\
    memory_nearest sg assign v (memory_record_output (visit v input)).
Proof.
  intro Hv; destruct memory_frontier_final as [Hdone Hinv].
  destruct (memory_stack_complete ED sg sp memory_frontier_ready assign MemoryLive
    visit memory_record_output (memory_rename_visit_output EN phi_set effects)
    memory_frontier_root_assignment final Hinv Hdone v Hv)
    as [record [input [Hget [Heq [Hinput Hnearest]]]]].
  exists input; subst record; auto.
Qed.

Lemma memory_frontier_record_at v : reachable sg v -> exists input,
  record_at v = visit v input /\ memory_stack_inherited ED sg sp assign MemoryLive v input /\
    memory_nearest sg assign v (memory_record_output (record_at v)).
Proof.
  intro Hv; destruct (memory_frontier_recorded v Hv) as [input [Hget [Hinput Hnearest]]].
  exists input; unfold memory_frontier_record; rewrite Hget; auto.
Qed.

Lemma memory_frontier_record_domain v record : Map.get ED v records = Some record -> reachable sg v.
Proof.
  intro Hget; destruct (proj2 memory_frontier_final) as [_ Hrecorded _ _].
  exact (proj1 (Hrecorded v record Hget)).
Qed.

Lemma memory_frontier_prepare_eq : memory_frontier_prepare EN EE g effects =
  MemoryFrontierState phis phi_set edges records.
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_phis_data n : memory_phi_at mg n <-> In n phis.
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_in_data n :
  memory_in mg n = memory_record_output (record_at (MemoryBlock n)).
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_out_data e :
  memory_out mg e = memory_record_output (record_at (MemoryEdge e)).
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_before_data e i : memory_before mg e i =
  Map.get nat_encoding i (memory_record_before (record_at (MemoryEdge e))).
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_assignment_seed d w : reachable sg d -> assign d = Some w ->
  In d defs \/ in_idf sg defs d.
Proof.
  destruct d as [|n|e]; intro Hreach; cbn [memory_node_assignment].
  - intros _; left; apply memory_dom_defs_exact; [exact Hwf|left; reflexivity].
  - destruct (FinSet.mem EN n phi_set) eqn:Hphi; [|discriminate].
    intros _; right; apply memory_frontier_phi_in.
    now apply FinSet.of_list_spec in Hphi.
  - intro Hdef; destruct (memory_edge_definition_witness e 0 (effects e) w Hdef)
      as [j [a [_ [Ha Hdefa]]]].
    left; apply memory_dom_defs_exact; [exact Hwf|right].
    apply memory_dom_edge_reachable in Hreach; [|exact Hwf].
    exists e, a; split; [reflexivity|split; [exact (proj1 Hreach)|]].
    split; [exact (proj2 Hreach)|split; [eapply nth_error_In; exact Ha|exact Hdefa]].
Qed.

Lemma memory_frontier_assignment_valid d w : reachable sg d -> assign d = Some w ->
  memory_valid_version g effects mg w.
Proof.
  destruct d as [|n|e]; intro Hreach; cbn [memory_node_assignment].
  - intro Heq; inversion Heq; exact I.
  - destruct (FinSet.mem EN n phi_set) eqn:Hphi; [|discriminate].
    intro Heq; inversion Heq; subst w; split.
    + apply (memory_dom_reachable EN EE g Hwf); exact Hreach.
    + apply memory_frontier_phis_data; now apply FinSet.of_list_spec in Hphi.
  - intro Hdef; destruct (memory_edge_definition_witness e 0 (effects e) w Hdef)
      as [j [a [Heq [Ha Hdefa]]]]; cbn [Nat.add] in Heq; subst w.
    apply memory_dom_edge_reachable in Hreach; [|exact Hwf].
    exists a; split; [split; [exact (proj2 Hreach)|split; [exact (proj1 Hreach)|exact Ha]]|].
    exact Hdefa.
Qed.

Lemma memory_frontier_nearest v : reachable sg v ->
  memory_nearest sg assign v (memory_record_output (record_at v)).
Proof.
  intro Hv; destruct (memory_frontier_record_at v Hv) as [input [_ [_ Hnearest]]].
  exact Hnearest.
Qed.

Lemma memory_frontier_output_valid v : reachable sg v ->
  memory_valid_version g effects mg (memory_record_output (record_at v)).
Proof.
  intro Hv; destruct (memory_frontier_nearest v Hv) as [d [Hd [Hdom _]]].
  apply (memory_frontier_assignment_valid d).
  - eapply dom_dominator_reachable; eassumption.
  - exact Hd.
Qed.

(** The inherited scope of an edge node is exactly its original source block's output. *)
Lemma memory_frontier_edge_record e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) ->
  record_at (MemoryEdge e) = visit (MemoryEdge e) (memory_in mg (Graph.source g e)).
Proof.
  intros Hedge Hsource.
  assert (He : reachable sg (MemoryEdge e)).
  { apply memory_dom_edge_reachable; [exact Hwf|split; assumption]. }
  destruct (memory_frontier_record_at (MemoryEdge e) He) as [input [Hrecord [Hinput _]]].
  assert (Hinput_eq : input = memory_in mg (Graph.source g e)).
  { unfold memory_stack_inherited in Hinput.
    rewrite (memory_dom_edge_parent EN EE g e Hwf He) in Hinput.
    rewrite memory_frontier_in_data.
    apply (memory_nearest_unique ED sg sp memory_frontier_ready assign
      (MemoryBlock (Graph.source g e))).
    - apply memory_dom_lift_reachable; assumption.
    - exact Hinput.
    - apply memory_frontier_nearest, memory_dom_lift_reachable; assumption. }
  rewrite Hinput_eq in Hrecord; exact Hrecord.
Qed.

Lemma memory_frontier_edge_before e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> forall i, memory_before mg e i =
    Map.get nat_encoding i (fst (memory_rename_effects e 0 (effects e)
      (memory_in mg (Graph.source g e)))).
Proof.
  intros Hedge Hsource i; rewrite memory_frontier_before_data.
  rewrite (memory_frontier_edge_record e Hedge Hsource); unfold memory_rename_visit.
  destruct (memory_rename_effects e 0 (effects e) (memory_in mg (Graph.source g e)));
    reflexivity.
Qed.

Lemma memory_frontier_edge_output e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> memory_out mg e =
    memory_last_defs e 0 (effects e) (memory_in mg (Graph.source g e)).
Proof.
  intros Hedge Hsource; rewrite memory_frontier_out_data.
  rewrite (memory_frontier_edge_record e Hedge Hsource); unfold memory_rename_visit.
  pose proof (proj1 (memory_rename_effects_output e 0 (effects e)
    (memory_in mg (Graph.source g e)))) as Houtput.
  destruct (memory_rename_effects e 0 (effects e) (memory_in mg (Graph.source g e)));
    exact Houtput.
Qed.

(** Every reachable original edge consumes its recorded inputs in the prescribed order. *)
Lemma memory_frontier_edge_flow e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) ->
  memory_edge_flow mg e 0 (effects e) (memory_in mg (Graph.source g e)) (memory_out mg e).
Proof.
  intros Hedge Hsource; rewrite memory_frontier_edge_output by assumption.
  apply memory_rename_effects_flow, memory_frontier_edge_before; assumption.
Qed.

(** Absence from the IDF forces the same renamed version along every incoming split edge. *)
Lemma memory_frontier_no_phi a n : In a (Graph.out sg (Graph.source sg a)) ->
  reachable sg (Graph.source sg a) -> Graph.target sg a = MemoryBlock n ->
  ~ In n phis -> memory_record_output (record_at (Graph.source sg a)) = memory_in mg n.
Proof.
  intros Hedge Hsource Htarget Hnot; rewrite memory_frontier_in_data.
  apply (memory_nearest_no_phi ED sg sp assign defs a).
  - exact memory_frontier_ready.
  - exact memory_frontier_assignment_seed.
  - exact Hedge.
  - exact Hsource.
  - rewrite Htarget; cbn [memory_node_assignment].
    destruct (FinSet.mem EN n phi_set) eqn:Hphi; [|reflexivity].
    exfalso; apply Hnot; now apply FinSet.of_list_spec in Hphi.
  - rewrite Htarget; intro Hphi; apply Hnot, memory_frontier_phi_in; exact Hphi.
  - apply memory_frontier_nearest; exact Hsource.
  - rewrite Htarget; apply memory_frontier_nearest.
    rewrite <- Htarget; exact (reachable_step a Hsource Hedge).
Qed.

Lemma memory_frontier_root_output : memory_record_output (record_at MemoryRoot) = MemoryLive.
Proof.
  assert (Hroot : reachable sg MemoryRoot) by (apply reachable_entry; left; reflexivity).
  destruct (memory_frontier_record_at MemoryRoot Hroot) as [input [Hrecord _]].
  rewrite Hrecord; reflexivity.
Qed.

Lemma memory_frontier_operand_key n k :
  In (n, k) (memory_frontier_operand_keys EN g phi_set edges) <-> In n phis /\
    match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end.
Proof.
  unfold memory_frontier_operand_keys; rewrite in_app_iff, !in_map_iff.
  destruct k as [e|]; split.
  - intros [[m [Hbad _]]|[a [Heq Hin]]]; [discriminate|].
    inversion Heq; subst a n; apply filter_In in Hin; destruct Hin as [Hedge Hphi].
    apply FinSet.of_list_spec in Hphi; apply memory_frontier_edges_in in Hedge; tauto.
  - intros [Hphi [Hedge [Hsource Htarget]]]; right; exists e; split.
    + now rewrite Htarget.
    + apply filter_In; split; [apply memory_frontier_edges_in; split; assumption|].
      rewrite Htarget; apply FinSet.of_list_spec; exact Hphi.
  - intros [[m [Heq Hin]]|[e [Hbad _]]]; [|discriminate].
    inversion Heq; subst m; apply filter_In in Hin; destruct Hin as [Hentry Hphi].
    apply FinSet.of_list_spec in Hphi; split; assumption.
  - intros [Hphi Hentry]; left; exists n; split; [reflexivity|].
    apply filter_In; split; [exact Hentry|apply FinSet.of_list_spec; exact Hphi].
Qed.

Lemma memory_frontier_operand_domain n k :
  (exists v, memory_operand mg n k = Some v) <-> memory_phi_at mg n /\
    match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end.
Proof.
  change ((exists v, Map.get (pair_encoding EN (option_encoding EE)) (n, k)
    (memory_result_index (pair_encoding EN (option_encoding EE))
      (fun key => match snd key with
        | None => MemoryLive
        | Some e => memory_record_output (record_at (MemoryEdge e))
        end) (memory_frontier_operand_keys EN g phi_set edges)) = Some v) <->
    memory_phi_at mg n /\ match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end).
  rewrite memory_result_index_domain, memory_frontier_operand_key, memory_frontier_phis_data.
  reflexivity.
Qed.

Lemma memory_frontier_operand_at n k : In n phis ->
  (match k with
   | None => In n (Graph.entries g)
   | Some e => In e (Graph.out g (Graph.source g e)) /\
       reachable g (Graph.source g e) /\ Graph.target g e = n
   end) -> memory_operand mg n k = Some
    (match k with None => MemoryLive | Some e => memory_out mg e end).
Proof.
  intros Hphi Hkey.
  apply memory_result_index_at, memory_frontier_operand_key; split; assumption.
Qed.

Lemma memory_frontier_entry_arrival n : In n (Graph.entries g) ->
  memory_arrival mg n None MemoryLive.
Proof.
  intro Hentry; destruct (FinSet.mem EN n phi_set) eqn:Hphi.
  - apply FinSet.of_list_spec in Hphi; left; split; [apply memory_frontier_phis_data; exact Hphi|].
    split; [apply memory_frontier_operand_at; assumption|].
    rewrite memory_frontier_in_data.
    destruct (memory_frontier_record_at (MemoryBlock n)
      (memory_dom_lift_reachable EN EE g Hwf n (reachable_entry n Hentry)))
      as [input [Hrecord _]].
    rewrite Hrecord; cbn [memory_rename_visit memory_record_output].
    assert (Hmem : FinSet.mem EN n phi_set = true) by (apply FinSet.of_list_spec; exact Hphi).
    now rewrite Hmem.
  - assert (Hnot : ~ In n phis).
    { intro Hin; pose proof (proj2 (FinSet.of_list_spec EN n phis) Hin); congruence. }
    right; split; [rewrite memory_frontier_phis_data; exact Hnot|].
    symmetry; rewrite <- memory_frontier_root_output.
    apply (memory_frontier_no_phi (MemoryStart n) n).
    + cbn [memory_dom_graph Graph.source Graph.out]; apply in_map, memory_distinct_in; exact Hentry.
    + apply reachable_entry; left; reflexivity.
    + reflexivity.
    + exact Hnot.
Qed.

Lemma memory_frontier_edge_arrival e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e).
Proof.
  intros Hedge Hsource; destruct (FinSet.mem EN (Graph.target g e) phi_set) eqn:Hphi.
  - apply FinSet.of_list_spec in Hphi; left; split; [apply memory_frontier_phis_data; exact Hphi|].
    split; [apply memory_frontier_operand_at; [exact Hphi|repeat split; assumption]|].
    rewrite memory_frontier_in_data.
    destruct (memory_frontier_record_at (MemoryBlock (Graph.target g e))
      (memory_dom_lift_reachable EN EE g Hwf _ (reachable_step e Hsource Hedge)))
      as [input [Hrecord _]].
    rewrite Hrecord; cbn [memory_rename_visit memory_record_output].
    assert (Hmem : FinSet.mem EN (Graph.target g e) phi_set = true)
      by (apply FinSet.of_list_spec; exact Hphi).
    now rewrite Hmem.
  - assert (Hnot : ~ In (Graph.target g e) phis).
    { intro Hin; pose proof (proj2 (FinSet.of_list_spec EN (Graph.target g e) phis) Hin).
      congruence. }
    right; split; [rewrite memory_frontier_phis_data; exact Hnot|].
    symmetry; rewrite memory_frontier_out_data.
    apply (memory_frontier_no_phi (MemoryEnd e) (Graph.target g e)).
    + change (In (MemoryEnd e) (Graph.out sg (MemoryEdge e))).
      rewrite memory_dom_edge_out; [left; reflexivity|].
      eapply edges_of_in; [exact (reachable_in_nodes g _ Hwf Hsource)|exact Hedge].
    + apply memory_dom_edge_reachable; [exact Hwf|split; assumption].
    + reflexivity.
    + exact Hnot.
Qed.

Lemma memory_frontier_versions_data : memory_versions mg =
  memory_distinct (memory_frontier_version_encoding EN EE)
    (MemoryLive :: map MemoryPhi phis ++
      flat_map (fun e => memory_edge_versions e 0 (effects e)) edges).
Proof.
  reflexivity.
Qed.

Lemma memory_frontier_versions_exact : forall v, In v (memory_versions mg) <->
  memory_valid_version g effects mg v.
Proof.
  intro v; rewrite memory_frontier_versions_data, memory_distinct_in.
  change (MemoryLive = v \/ In v (map MemoryPhi phis ++
    flat_map (fun e => memory_edge_versions e 0 (effects e)) edges) <->
    memory_valid_version g effects mg v).
  rewrite in_app_iff; split.
  - intros [Heq|[Hphi|Hdef]].
    + subst v; exact I.
    + apply in_map_iff in Hphi; destruct Hphi as [n [Heq Hn]]; subst v.
      split.
      * apply memory_frontier_phi_reaches; exact Hn.
      * apply memory_frontier_phis_data; exact Hn.
    + apply in_flat_map in Hdef; destruct Hdef as [e [Hedge Hdef]].
      apply memory_edge_versions_exact in Hdef; destruct Hdef as [j [a [Heq [Ha Hdefa]]]].
      cbn [Nat.add] in Heq; subst v; apply memory_frontier_edges_in in Hedge.
      exists a; split; [split; [exact (proj1 Hedge)|split; [exact (proj2 Hedge)|exact Ha]]|].
      exact Hdefa.
  - destruct v as [|n|e i].
    + intros _; left; reflexivity.
    + intros [_ Hphi]; right; left; apply in_map, memory_frontier_phis_data; exact Hphi.
    + intros [a [[Hedge [Hsource Hnth]] Hdef]]; right; right.
      apply in_flat_map; exists e; split; [apply memory_frontier_edges_in; split; assumption|].
      apply memory_edge_versions_exact; exists i, a; split; [reflexivity|split; assumption].
Qed.

(** Inputs exist exactly at the ordered occurrences of reachable listed edges. *)
Lemma memory_frontier_occurrence_domain e i :
  (exists v, memory_before mg e i = Some v) <-> exists a, memory_occurrence g effects e i a.
Proof.
  destruct (Map.get ED (MemoryEdge e) records) as [record|] eqn:Hrecord.
  - pose proof (memory_frontier_record_domain (MemoryEdge e) record Hrecord) as Hreach.
    apply memory_dom_edge_reachable in Hreach; [|exact Hwf].
    destruct Hreach as [Hsource Hedge].
    rewrite (memory_frontier_edge_before e Hedge Hsource).
    rewrite memory_rename_effects_domain; split.
    + intros [a Ha]; exists a; split; [exact Hedge|split; assumption].
    + intros [a [_ [_ Ha]]]; exists a; exact Ha.
  - assert (Hbefore : memory_before mg e i = None).
    { rewrite memory_frontier_before_data; unfold memory_frontier_record; rewrite Hrecord.
      apply Map.get_empty. }
    rewrite Hbefore; split; [intros [v Hfalse]; discriminate|].
    intros [a [Hedge [Hsource _]]].
    assert (He : reachable sg (MemoryEdge e)).
    { apply memory_dom_edge_reachable; [exact Hwf|split; assumption]. }
    destruct (memory_frontier_recorded (MemoryEdge e) He) as [input [Hget _]]; congruence.
Qed.

(** The frontier and stack constructor satisfies every local graph law directly. *)
Theorem memory_frontier_data_wf : memory_graph_wf g effects mg.
Proof.
  constructor.
  - exact Hwf.
  - change (NoDup phis); apply NoDup_filter; exact (nodes_nodup Hwf).
  - intros n Hphi; apply memory_frontier_phi_reaches, memory_frontier_phis_data; exact Hphi.
  - rewrite memory_frontier_versions_data; apply memory_distinct_nodup.
  - exact memory_frontier_versions_exact.
  - exact memory_frontier_entry_arrival.
  - exact memory_frontier_edge_flow.
  - exact memory_frontier_edge_arrival.
  - intros n Hn; rewrite memory_frontier_in_data.
    apply memory_frontier_output_valid, memory_dom_lift_reachable; assumption.
  - intros e Hedge Hsource; rewrite memory_frontier_out_data.
    apply memory_frontier_output_valid, memory_dom_edge_reachable; [exact Hwf|split; assumption].
  - exact memory_frontier_occurrence_domain.
  - exact memory_frontier_operand_domain.
Qed.

End FrontierProof.

(** Every well-formed CFG receives a directly proved whole-memory version graph. *)
Definition memory_frontier_build {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
    { mg : memory_graph N E | memory_graph_wf g effects mg } :=
  exist _ (memory_frontier_data EN EE g effects) (memory_frontier_data_wf EN EE g effects Hwf).

(** Original block phis are exactly the unpruned iterated frontier of live and real definitions. *)
Theorem memory_frontier_phi_exact {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall n, memory_phi_at (proj1_sig (memory_frontier_build EN EE g effects Hwf)) n <->
    in_idf (memory_dom_graph EN EE g) (memory_dom_defs EN EE g effects) (MemoryBlock n).
Proof.
  intro n; apply memory_frontier_phi_in; exact Hwf.
Qed.

(** Every original entry path selects the actual edge operands of the same constructed graph. *)
Theorem memory_frontier_path {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival (proj1_sig (memory_frontier_build EN EE g effects Hwf)) root None MemoryLive /\
    memory_path_flow g effects (proj1_sig (memory_frontier_build EN EE g effects Hwf)) root es n.
Proof.
  apply memory_path_correspondence; exact (proj2_sig (memory_frontier_build EN EE g effects Hwf)).
Qed.

(** The same constructed graph retains the last dynamic definition on every occurrence history. *)
Theorem memory_frontier_definition_before_occurrence {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin,
    memory_provenance g effects (proj1_sig (memory_frontier_build EN EE g effects Hwf))
      root es (Graph.source g e)
      (memory_in (proj1_sig (memory_frontier_build EN EE g effects Hwf)) (Graph.source g e))
      (memory_last_path effects es) /\
    memory_occurrence_history g effects (proj1_sig (memory_frontier_build EN EE g effects Hwf))
      es e i input origin.
Proof.
  apply memory_definition_before_occurrence.
  exact (proj2_sig (memory_frontier_build EN EE g effects Hwf)).
Qed.
