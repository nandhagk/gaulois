# Gaulois.Graph

Graph provides edge-labelled graphs with entry nodes, and the standard algorithms over them, each
with an exactness theorem: depth-first search and reverse postorder, dominators and
post-dominators, strongly connected components, loop forests, Bourdoncle's weak topological order,
dominance frontiers, control dependence and register colouring. Nothing assumes node ids: a node
type supplies an `encoding`. For example, with entries `[1]` and edges `1→2`, `2→3`, `3→2`, the
search visits `[1; 2; 3]`, `3→2` is a retreating edge, `2` dominates `3`, and the loop forest has
one loop with header `2` and nodes `{2, 3}`. Every producer is total. Dominator backends and the
weak topological order have direct correctness proofs. Independent checkers remain available for
external candidates; colouring also retains its checked fallback.

Conventions of this document. The graph record is `Graph.t V E` in module `Graph`, with the
projections `Graph.entries`, `Graph.nodes`, `Graph.out`, `Graph.source` and `Graph.target`, always
written qualified (a constraint system also has a `target`). `reachable`, `graph_wf` and every other
definition are top-level names. Sets are `FinSet.t`; `FinSet.mem EV v s` takes the encoding first,
as in Collections. Statements sit in `Section`s whose `Context` and `Variables` declare what they
mention; a theorem is generalised over exactly the ones it uses, in declaration order. Stdlib
imports (`List`, `Bool`, `ZArith`, `Permutation`, `Relations.Relation_Operators`) are implicit,
`ListNotations` is open. Every `Inductive` and `Record` takes its parameters implicitly in
constructors and projections (`Arguments` declarations are omitted).

## Files

Prerequisites: GRA-1a needs COL-1c; GRA-1b needs GRA-1a; GRA-2a needs GRA-1b;
GRA-2c needs GRA-2a; GRA-2d and GRA-2e need GRA-2c; GRA-2f needs GRA-2d and GRA-2e;
GRA-2b needs GRA-2f; GRA-7 needs GRA-5 and GRA-2f;
GRA-3a needs GRA-1b; GRA-3b needs GRA-3a; GRA-4a needs GRA-2f and GRA-1b; GRA-4b needs GRA-3a and
GRA-4a; GRA-4c needs GRA-3a; GRA-5 needs GRA-2b; GRA-6a needs GRA-1a; GRA-6b needs GRA-6a.

| File | Contents | Card |
|---|---|---|
| `GraphCore.v` | module `Graph`, `reachable`, `graph_wf` (anchors); `path`, `reaches`, `mutual`, `before`, `acyclic`, `set_entries`, `without`, `induced`, `edge_count` | GRA-1a |
| `GraphPrepare.v` | `prepared` (with `fuel`), `prepare`, `prepared_laws`, `ready`, `reverse_graph`, `prepared_reverse` | GRA-1a |
| `GraphDfs.v` | `dfs`, `dfs_result`, `rpo`, `retreating`, tree ancestry, interval ancestry test | GRA-1b |
| `GraphCertificate.v` | `check_path`, `tree_path` | GRA-1b |
| `GraphDominance.v` | semantic dominance, `idom_ancestor`, `forest_on`, virtual-root reduction | GRA-2a |
| `GraphSemiDominators.v` | shared DFS numbering, semidominators and link/eval proofs | GRA-2c |
| `GraphLengauerTarjan.v` | `simple_lt_idom`, `simple_lt_idom_exact` | GRA-2d |
| `GraphSemiNca.v` | `semi_nca_idom`, `semi_nca_idom_exact` | GRA-2e |
| `GraphDominators.v` | `dom_tree`, `chk_idom`, boundary checker, selector and exact trees | GRA-2f |
| `GraphEdgeDominance.v` | `edge_dominates`, `edge_dom_index`, `dominating_edges` | GRA-2b |
| `GraphPostDominators.v` | `post_dominates`, `post_dominator_tree` | GRA-2b |
| `GraphScc.v` | iterative Tarjan: `scc_within`, `scc`, `condensation`, `topological_order` | GRA-3a |
| `GraphDag.v` | `topological_sort`, `max_paths` | GRA-3b |
| `GraphChain.v` | `resolve`, `resolve_all` (forwarding chains) | GRA-3b |
| `GraphReducible.v` | `back_edge`, `reducible`, `reducible_b` | GRA-4a |
| `GraphNaturalLoops.v` | `natural_loop`, `natural_loop_nodes` | GRA-4a |
| `GraphLoops.v` | `loop_forest`, `loop_forest_of` | GRA-4b |
| `GraphWto.v` | `wto`, `wto_of`, `check_wto`, `wto_all_heads`, `wto_total` | GRA-4c |
| `GraphFrontier.v` | `dominance_chain`, `dominance_frontier`, `iterated_frontier` | GRA-5 |
| `GraphIdf.v` | `in_pruned_idf`, `direct_idf`, `direct_pruned_idf` | GRA-7 |
| `GraphControlDependence.v` | `control_deps`, `cdep` | GRA-5 |
| `GraphInterference.v` | `interference`, `add_point` (an observer step) | GRA-6a |
| `GraphColour.v` | `greedy_colour`, `check_colouring`, `all_spilled` | GRA-6a |
| `GraphBriggs.v` | `briggs_colour`, `colour_checked`, `degenerate` | GRA-6b |

## Definitions

### GRA-1a: core, preparation, reverse graph, fuel

`reachable` and `graph_wf` are the anchors, with the projections written qualified:

```coq
Module Graph.
Record t (V E : Type) : Type := Make {
  entries : list V;
  nodes : list V;
  out : V -> list E;
  source : E -> V;
  target : E -> V
}.
End Graph.
Inductive reachable {V E} (g : Graph.t V E) : V -> Prop :=
  | reachable_entry : forall v, In v (Graph.entries g) -> reachable g v
  | reachable_step : forall e, reachable g (Graph.source g e) ->
      In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.target g e).
Record graph_wf {V E} (g : Graph.t V E) : Prop := {
  nodes_nodup : NoDup (Graph.nodes g);
  entries_in : forall v, In v (Graph.entries g) -> In v (Graph.nodes g);
  out_source : forall v e, In e (Graph.out g v) -> Graph.source g e = v;
  out_target_in : forall v e, In v (Graph.nodes g) -> In e (Graph.out g v) ->
    In (Graph.target g e) (Graph.nodes g)
}.
```

Additions to `GraphCore.v`:

```coq
Inductive path {V E} (g : Graph.t V E) : V -> list E -> V -> Prop :=
  | path_nil : forall v, path g v [] v
  | path_cons : forall e es w, In e (Graph.out g (Graph.source g e)) ->
      path g (Graph.target g e) es w -> path g (Graph.source g e) (e :: es) w.
Definition reaches {V E} (g : Graph.t V E) (u v : V) : Prop := exists es, path g u es v.
Definition mutual {V E} (g : Graph.t V E) (u v : V) : Prop := reaches g u v /\ reaches g v u.
Definition acyclic {V E} (g : Graph.t V E) : Prop :=
  forall v es, In v (Graph.nodes g) -> path g v es v -> es = [].
Definition before {A} (l : list A) (u v : A) : Prop := exists l1 l2 l3, l = l1 ++ u :: l2 ++ v :: l3.
Definition set_entries {V E} (g : Graph.t V E) (roots : list V) : Graph.t V E :=
  {| Graph.entries := roots; Graph.nodes := Graph.nodes g; Graph.out := Graph.out g;
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* delete the blocked nodes, and the edges into them *)
Definition without {V E} (EV : encoding V) (blocked : FinSet.t V) (g : Graph.t V E) : Graph.t V E :=
  {| Graph.entries := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.entries g);
     Graph.nodes := filter (fun v => negb (FinSet.mem EV v blocked)) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => negb (FinSet.mem EV (Graph.target g e) blocked)) (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* keep only the nodes of `keep`, and the edges between them; no entries *)
Definition induced {V E} (EV : encoding V) (keep : FinSet.t V) (g : Graph.t V E) : Graph.t V E :=
  {| Graph.entries := []; Graph.nodes := filter (fun v => FinSet.mem EV v keep) (Graph.nodes g);
     Graph.out := fun v => filter (fun e => FinSet.mem EV (Graph.target g e) keep) (Graph.out g v);
     Graph.source := Graph.source g; Graph.target := Graph.target g |}.
(* the number of edges listed in the out lists of the nodes *)
Definition edge_count {V E} (g : Graph.t V E) : nat :=
  fold_right (fun v n => length (Graph.out g v) + n) 0 (Graph.nodes g).
```

`prepare` runs once per graph. The index maps are built from `Graph.out g` over `Graph.nodes g`, so
every later algorithm reads adjacency and predecessors by map lookup. The record also carries the
fuel of every explicit-stack walk: one run visits each node at most once, and each step takes an
edge, pushes a new node or pops one, so `2 * length (Graph.nodes g) + edge_count g + 2` steps
suffice.

```coq
Record prepared {V E} (EV : encoding V) (g : Graph.t V E) : Type := Prepared {
  out_index : Map.t V (list E);          (* Graph.out g v, stored per node *)
  in_index : Map.t V (list E);           (* the edges whose target is v, in order of Graph.nodes g *)
  fuel : positive                        (* 2 * |nodes| + edge_count g + 2, in binary *)
}.
Definition prepare {V E} (EV : encoding V) (g : Graph.t V E) : prepared EV g.
Definition succ_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (v : V) : list E.
Definition pred_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (v : V) : list E.
(* both are the stored list, or [] when v has no entry *)
Record prepared_laws {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop := {
  succ_agrees : forall v, In v (Graph.nodes g) -> succ_edges p v = Graph.out g v;
  succ_domain : forall v, ~ In v (Graph.nodes g) -> succ_edges p v = [];
  pred_agrees : forall v e, In v (Graph.nodes g) ->
    (In e (pred_edges p v) <->
     exists u, In u (Graph.nodes g) /\ In e (Graph.out g u) /\ Graph.target g e = v);
  pred_domain : forall v, ~ In v (Graph.nodes g) -> pred_edges p v = [];
  pred_nodup : forall v, NoDup (pred_edges p v);
  fuel_value : Pos.to_nat (fuel p) = 2 * length (Graph.nodes g) + edge_count g + 2
}.
(* the standing premise of every algorithm below: the graph is well formed, no out list repeats an
   edge, and p is its index *)
Definition ready {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop :=
  graph_wf g /\ (forall v, NoDup (Graph.out g v)) /\ prepared_laws EV g p.
(* the reverse graph: entries become the exits, edges keep their identity and swap direction *)
Definition reverse_graph {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : Graph.t V E :=
  {| Graph.entries := exits; Graph.nodes := Graph.nodes g; Graph.out := pred_edges p;
     Graph.source := Graph.target g; Graph.target := Graph.source g |}.
Definition prepared_reverse {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : prepared EV (reverse_graph p exits) :=
  {| out_index := in_index p; in_index := out_index p; fuel := fuel p |}.
```

### GRA-1b: depth-first search, certificates

`dfs` is depth-first search from `roots` in the given order, never entering a node of `blocked`
(use `FinSet.empty` for the plain search). It loops over the roots; a root that is blocked or
already visited is skipped, and every other root starts one explicit-stack run, with
`(node, remaining successor edges)` frames and fuel `fuel p`.

```coq
Record dfs_result (V E : Type) : Type := DfsResult {
  preorder : list V;
  postorder : list V;
  tree_edge : Map.t V E;                 (* the edge by which v was first reached; absent for a root *)
  pre_num : Map.t V positive;            (* 1-based position in preorder *)
  post_num : Map.t V positive;           (* 1-based position in postorder *)
  visited : FinSet.t V
}.
Definition dfs {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (blocked : FinSet.t V) (roots : list V) : dfs_result V E.
Definition rpo {V E} (r : dfs_result V E) : list V := rev (postorder r).
Definition tree_parent {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (u v : V) : Prop :=
  exists e, Map.get EV v (tree_edge r) = Some e /\ Graph.source g e = u.
(* u is v or a DFS-tree ancestor of v *)
Definition dfs_ancestor {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) : V -> V -> Prop :=
  clos_refl_trans V (tree_parent EV g r).
(* constant-time ancestry by DFS intervals *)
Definition ancestor_b {V E} (EV : encoding V) (r : dfs_result V E) (u v : V) : bool :=
  match Map.get EV u (pre_num r), Map.get EV v (pre_num r),
        Map.get EV u (post_num r), Map.get EV v (post_num r) with
  | Some a, Some b, Some c, Some d => Pos.leb a b && Pos.leb d c
  | _, _, _, _ => false
  end.
(* an edge is retreating when it goes from a node to itself or to one of its tree ancestors *)
Definition retreating {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (e : E) : Prop :=
  dfs_ancestor EV g r (Graph.target g e) (Graph.source g e).
```

```coq
(* GraphCertificate.v *)
(* a certificate that `es` is a path from s to v: each edge leaves the current node and is one of
   its successor edges; eqE decides equality of edges *)
Definition check_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (eqE : E -> E -> bool) (s : V) (es : list E) (v : V) : bool.
(* the tree path from a root to v, read off tree_edge in time linear in its length *)
Definition tree_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : dfs_result V E) (v : V) : option (V * list E).
```

### GRA-2a, GRA-2c–2f: the dominator tree

`dominates` is semantic: every path from an entry to `n` passes through `d` (as its first node, or
as the target of one of its edges). With several entries a node can have no strict dominator.

```coq
Definition dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n ->
    d = s \/ exists e, In e es /\ Graph.target g e = d.
Definition strictly_dominates {V E} (g : Graph.t V E) (d n : V) : Prop := dominates g d n /\ d <> n.
Definition immediately_dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  strictly_dominates g d n /\ forall x, strictly_dominates g x n -> dominates g x d.
```

The dominator tree is a forest: the roots are the reachable nodes with no strict dominator, and
`idom` omits them.

`GraphDominance.v` also supplies a fresh virtual root. The type `V + unit` keeps the root
distinct from every client vertex; `E + V` keeps synthetic entry edges distinct from client
edges. `virtual_entries` removes duplicate entries in first-occurrence order, using `EV`.

```coq
Definition virtual_entries {V E} (EV : encoding V) (g : Graph.t V E) : list V.
Definition virtual_graph {V E} (EV : encoding V) (g : Graph.t V E) : Graph.t (V + unit) (E + V) :=
  {| Graph.entries := [inr tt];
     Graph.nodes := map (@inl V unit) (Graph.nodes g) ++ [inr tt];
     Graph.out := fun v => match v with
       | inl x => map (@inl E V) (Graph.out g x)
       | inr _ => map (@inr E V) (virtual_entries EV g)
       end;
     Graph.source := fun e => match e with
       | inl x => inl (Graph.source g x)
       | inr _ => inr tt
       end;
     Graph.target := fun e => match e with
       | inl x => inl (Graph.target g x)
       | inr x => inl x
       end |}.
Definition virtual_encoding {V} (EV : encoding V) : encoding (V + unit) :=
  sum_encoding EV unit_encoding.
Definition virtual_prepared {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : prepared (virtual_encoding EV) (virtual_graph EV g) :=
  prepare (virtual_encoding EV) (virtual_graph EV g).
```

GRA-2c builds the shared semidominator map on that graph. A semidominator path has at least one
edge; every internal vertex has a DFS preorder number strictly greater than the target's. The
first and last vertices are excluded from that internal-vertex test. The semidominator is the
candidate with least preorder number. The root and unreachable vertices have no map entry.

```coq
Definition semidom_path {V E} (EV : encoding V) (g : Graph.t V E)
  (r : dfs_result V E) (u n : V) : Prop :=
  exists es k h, es <> [] /\ path g u es n /\ Map.get EV n (pre_num r) = Some k /\
    Map.get EV u (pre_num r) = Some h /\
    forall pre e post, es = pre ++ e :: post -> post <> [] ->
      exists j, Map.get EV (Graph.target g e) (pre_num r) = Some j /\ Pos.lt k j.
Definition semidominator {V E} (EV : encoding V) (g : Graph.t V E)
  (r : dfs_result V E) (u n : V) : Prop :=
  semidom_path EV g r u n /\
  exists k, Map.get EV u (pre_num r) = Some k /\
    forall v, semidom_path EV g r v n ->
      exists j, Map.get EV v (pre_num r) = Some j /\ Pos.le k j.
Definition virtual_dfs {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : dfs_result (V + unit) (E + V) :=
  dfs (virtual_prepared p) FinSet.empty [inr tt].
Definition semidominators {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t (V + unit) (V + unit).
```

Compute semidominators in reverse DFS order using predecessor indexes and shared link/eval;
both direct backends consume this same result. For each compressed link, the implementation
maintains the minimum semidominator-rank label on the corresponding segment of the original
uncompressed linked forest. `eval` returns a minimum on the queried linked path; compression
preserves that fact for all subsequent queries. Prove the segment invariant, minimum query,
rank-decreasing termination, semidominator path characterization and virtual-root path reduction
before either backend proof. These proof helpers and the link/eval state are internal.

```coq
Record dom_tree (V : Type) : Type := DomTree {
  idom : Map.t V V;                      (* parent in the forest; absent for a root *)
  tin : Map.t V positive;                (* DFS interval of the node in the forest *)
  tout : Map.t V positive
}.
Definition idom_ancestor {V} (EV : encoding V) (m : Map.t V V) : V -> V -> Prop :=
  clos_refl_trans V (fun u v => Map.get EV v m = Some u).      (* u is v or an ancestor of v *)
(* m is a forest on the reachable nodes: keys and parents are reachable and no parent chain is infinite *)
Definition forest_on {V E} (EV : encoding V) (g : Graph.t V E) (m : Map.t V V) : Prop :=
  (forall v u, Map.get EV v m = Some u -> reachable g v /\ reachable g u) /\
  well_founded (fun u v => Map.get EV v m = Some u).
Inductive dom_algorithm : Type := SimpleLT | SemiNCA.
Definition simple_lt_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V.
Definition semi_nca_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V.
Definition chk_idom {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) : Map.t V V := simple_lt_idom p.
(* The compatibility name is directly proved, not an unchecked CHK candidate. *)
(* Both use one DFS on a fresh tagged virtual root, shared semidominators and link/eval.
   Erase virtual-root parent bindings. LT settles buckets and corrects provisional parents;
   Semi-NCA finds the nearest common ancestor of each semidominator and DFS parent. *)
Definition dom_tree_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (m : Map.t V V) : dom_tree V.
(* idom is m; tin and tout come from one DFS of the forest m, from the reachable nodes that have no
   parent, over children lists built from m *)
Definition check_idom {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (m : Map.t V V) : bool.
(* first: every key and value of m is reachable, and the numbering of m visits every key, so m is a
   forest; then, for every reachable d, runs dfs p {d} (Graph.entries g) and requires, for every
   reachable n: n is missed by that search  iff  dominates_b (dom_tree_of p m) d n *)
Definition dominates_b {V} (EV : encoding V) (t : dom_tree V) (d n : V) : bool :=
  match Map.get EV d (tin t), Map.get EV n (tin t), Map.get EV d (tout t), Map.get EV n (tout t) with
  | Some a, Some b, Some c, Some e => Pos.leb a b && Pos.leb e c
  | _, _, _, _ => false
  end.
(* the fallback: no parents, except that when every entry is one node s each other reachable node
   has parent s (a sole entry dominates everything reachable) *)
Definition flat_idom {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : Map.t V V :=
  match Graph.entries g with
  | s :: rest =>
      if forallb (fun x => Pos.eqb (encode EV x) (encode EV s)) rest
      then fold_left (fun m n => if Pos.eqb (encode EV n) (encode EV s) then m else Map.set EV n s m)
             (preorder (dfs p FinSet.empty (Graph.entries g))) Map.empty
      else Map.empty
  | [] => Map.empty
  end.
Definition flat_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : dom_tree V :=
  dom_tree_of p (flat_idom p).
(* did the independent checker accept the directly constructed default map? *)
Definition dominator_exact {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : bool :=
  check_idom p (chk_idom p).
(* Explicit boundary query. Direct constructors do not call this expensive checker. *)
Definition dominator_tree_with {V E} {EV : encoding V} {g : Graph.t V E}
  (p : prepared EV g) (algorithm : dom_algorithm) : dom_tree V :=
  dom_tree_of p (match algorithm with SimpleLT => simple_lt_idom p | SemiNCA => semi_nca_idom p end).
Definition dominator_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : dom_tree V :=
  dominator_tree_with p SimpleLT.
```

### GRA-2b: edge dominance and post-dominators

```coq
(* GraphEdgeDominance.v: every entry path to n contains the edge e *)
Definition edge_dominates {V E} (g : Graph.t V E) (e : E) (n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n -> In e es.
```

Edge dominance rides on the tree. `edge_dom_index` maps a node `v` to the edge that dominates `v`:
among the edges of `pred_edges p v` whose source is reachable and for which `dominates_b t v
(source e)` is false, the only one, provided `v` is not an entry and there is exactly one. One pass
over `Graph.nodes g` builds it. `dominating_edges` walks the `idom` chain of `n` once.

```coq
Definition edge_dom_index {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) : Map.t V E.
Definition dominating_edges {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (ix : Map.t V E) (n : V) : list E.
(* the index entries of n and of every ancestor of n in t *)

(* GraphPostDominators.v: every path from n to an exit passes through d *)
Definition post_dominates {V E} (g : Graph.t V E) (exits : list V) (d n : V) : Prop :=
  forall es x, path g n es x -> In x exits -> d = n \/ exists e, In e es /\ Graph.target g e = d.
(* post-dominators: the total dominator tree of the reverse graph, from an explicit list of exits *)
Definition post_dominator_tree {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (exits : list V) : dom_tree V :=
  dominator_tree (prepared_reverse p exits).
```

### GRA-3a: components and condensation

```coq
Definition topological_order {V E} (g : Graph.t V E) (l : list V) : Prop :=
  NoDup l /\ (forall v, In v l <-> In v (Graph.nodes g)) /\
  forall e, In (Graph.source g e) (Graph.nodes g) -> In e (Graph.out g (Graph.source g e)) ->
    before l (Graph.source g e) (Graph.target g e).

Record scc_result (V : Type) : Type := SccResult {
  components : list (list V);            (* in Tarjan's emission order: after every component it reaches *)
  component_ids : list positive;         (* IDs in the same emission order *)
  component_at : Trie.t (list V);       (* component indexed by its ID *)
  comp_of : Map.t V positive             (* component ID of each node *)
}.
Definition scc_within {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (region : list V) : scc_result V.
(* iterative Tarjan over the nodes of region in list order, ignoring every edge whose target is
   outside region (a set built once from region). A call costs O(|region| + the edges of its nodes);
   no filtered copy of the graph is built. On emission, a positive counter starts at 1 and advances
   once per component; the component, its ID, and its trie binding are recorded together *)
Definition scc {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : scc_result V :=
  scc_within p (Graph.nodes g).
```

The machine behind `scc_within`; its invariant is the spine of the exactness proof.

```coq
Record tarjan_frame (V E : Type) : Type := TarjanFrame {
  frame_node : V;
  frame_edges : list E                   (* the successor edges of frame_node not yet taken *)
}.
Record tarjan_state (V E : Type) : Type := TarjanState {
  frames : list (tarjan_frame V E);      (* the open nodes: the depth-first path from the current root, innermost first *)
  disc : Map.t V positive;               (* discovery number of every visited node, from a positive clock *)
  low : Map.t V positive;                (* lowlink of every visited node not yet in a component *)
  pending : list V;                      (* visited nodes not yet in a component, newest first *)
  clock : positive;                      (* the next discovery number *)
  emitted : scc_result V                 (* the components emitted so far *)
}.
(* Invariant, for the induced graph G of region, at every step:
   I1  every emitted component is a strong component of G, and every edge of G that leaves it enters
       a component emitted earlier;
   I2  pending is exactly the visited nodes outside the emitted components, newest first, with disc
       strictly decreasing; frames lists the open nodes, a subsequence of pending, each open node
       the tree parent of the open node before it;
   I3  for every pending w: low w <= disc w, and low w = disc x for a pending x in the strong
       component of w (x = w when nothing older was found);
   I4  when the frame of v closes: low v = disc v exactly when no pending node older than v lies in
       the strong component of v, and then the pending nodes down to v are that whole component,
       emitted as one; otherwise low v is folded into the low of the node below it on frames. *)
```

```coq
Definition condensation {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : scc_result V) : Graph.t positive E.
(* nodes = rev (component_ids r); entries = the distinct components of the entries of g;
   out c = the edges of g that leave a member of c for another component (edges keep their
   identity and labels), kept in a trie built in one pass; source e, target e = the components of
   the ends of e *)
```

### GRA-3b: topological sort, maximum-weight paths, forwarding chains

```coq
Definition topological_sort {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) :
  option (list V).      (* rpo of dfs p FinSet.empty (Graph.nodes g); None if some edge retreats *)
Definition path_weight {E} (w : E -> Z) (es : list E) : Z := fold_right (fun e acc => (w e + acc)%Z) 0%Z es.
Record dag_paths (V E : Type) : Type := DagPaths {
  best : Map.t V Z;                      (* maximum weight of an entry path to v; present iff reachable *)
  via : Map.t V E                        (* last edge of one such path; absent when the empty path wins *)
}.
Definition max_paths {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (w : E -> Z) :
  option (dag_paths V E).
(* one pass in the rpo of the reachable part, rpo (dfs p FinSet.empty (Graph.entries g)); None iff
   an edge out of a reachable node retreats, that is, iff a reachable cycle exists *)
Definition max_path_to {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (r : dag_paths V E) (v : V) : option (V * list E).      (* follows via back to an entry *)

(* a forwarding step: v satisfies fwd and has exactly one outgoing edge *)
Definition forward_step {V E} (g : Graph.t V E) (fwd : V -> bool) (v : V) : option E :=
  if fwd v then match Graph.out g v with [e] => Some e | _ => None end else None.
Inductive chain {V E} (g : Graph.t V E) (fwd : V -> bool) : V -> list E -> V -> Prop :=
  | chain_stop : forall v, forward_step g fwd v = None -> chain g fwd v [] v
  | chain_move : forall v e es w, forward_step g fwd v = Some e ->
      chain g fwd (Graph.target g e) es w -> chain g fwd v (e :: es) w.
Inductive resolution (V : Type) : Type := Landing (w : V) | Cyclic.
Definition resolve {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (fwd : V -> bool)
  (v : V) : resolution V.                 (* follows forward_step; a visited set is the cycle guard *)
Definition resolve_all {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (fwd : V -> bool) : Map.t V (resolution V).      (* every node of g; each chain walked once *)
```

### GRA-4a: reducibility and natural loops

```coq
Definition back_edge {V E} (g : Graph.t V E) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
  dominates g (Graph.target g e) (Graph.source g e).
(* Hecht-Ullman: every cycle through a reachable node contains a back edge *)
Definition reducible {V E} (g : Graph.t V E) : Prop :=
  forall v es, reachable g v -> es <> [] -> path g v es v -> exists e, In e es /\ back_edge g e.
Definition reducible_b {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (t : dom_tree V) : bool.
(* every retreating edge of dfs p FinSet.empty (Graph.entries g) out of a visited node has a target
   that dominates_b its source, by one interval test per edge *)

(* the natural loop of a back edge: its target, and what reaches its source without the target *)
Definition natural_loop {V E} (EV : encoding V) (g : Graph.t V E) (e : E) (n : V) : Prop :=
  n = Graph.target g e \/
  exists es, path (without EV (FinSet.add EV (Graph.target g e) FinSet.empty) g) n es (Graph.source g e).
Definition natural_loop_nodes {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (e : E) :
  FinSet.t V.
(* the target of e together with one reverse search from the source of e that never enters the
   target *)
```

### GRA-4b: the loop nesting forest

```coq
Record loop_forest (V : Type) : Type := LoopForest {
  loop_headers : list V;                 (* every header, once; an outer loop before the loops inside it *)
  loop_nodes : Map.t V (FinSet.t V);     (* header -> every node of its loop, nested loops included *)
  loop_parent : Map.t V V;               (* header -> header of the next enclosing loop; absent at top *)
  loop_of : Map.t V V                    (* node -> header of its innermost loop; absent outside loops *)
}.
Definition loop_forest_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : loop_forest V.
(* Steensgaard/Ramalingam recursion on node lists: the loops of a region are the non-trivial
   components of scc_within p region (a component is trivial when it is one node with no self loop);
   the header of one is its first node in rpo (dfs p FinSet.empty (Graph.entries g)); its children
   are the loops of its node list without the header. The top region is the preorder of that search.
   Each call costs O(|region| + the edges of its nodes). Irreducible loops are covered. *)
Definition in_loop {V} (EV : encoding V) (f : loop_forest V) (h x : V) : Prop :=
  exists s, Map.get EV h (loop_nodes f) = Some s /\ FinSet.mem EV x s = true.
(* the set a loop lives in: its parent's loop without the parent's header, or, at top level, the
   nodes reachable from the entries *)
Definition outer_nodes {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (f : loop_forest V) (h : V) : FinSet.t V :=
  match Map.get EV h (loop_parent f) with
  | Some h' => match Map.get EV h' (loop_nodes f) with
               | Some s => FinSet.remove EV h' s | None => FinSet.empty end
  | None => visited (dfs p FinSet.empty (Graph.entries g))
  end.
Definition strong_component {V E} (g : Graph.t V E) (S : V -> Prop) : Prop :=
  (exists v, S v) /\ (forall u v, S u -> S v -> mutual g u v) /\ (forall u v, S u -> mutual g u v -> S v).
```

### GRA-4c: the weak topological order

A weak topological order is a flat token list: `a (b c (d) e) f` is `WVertex a`, `WOpen b`,
`WVertex c`, `WOpen d`, `WClose`, `WVertex e`, `WClose`, `WVertex f`.

```coq
Inductive wto_token (V : Type) : Type :=
  | WVertex (v : V)
  | WOpen (h : V)                        (* a component begins; h is its head and first vertex *)
  | WClose.                              (* the innermost open component ends *)
Definition wto (V : Type) : Type := list (wto_token V).
Fixpoint balanced_from {V} (d : nat) (w : wto V) : bool :=
  match w with
  | [] => Nat.eqb d 0
  | WVertex _ :: w' => balanced_from d w'
  | WOpen _ :: w' => balanced_from (S d) w'
  | WClose :: w' => match d with O => false | S d' => balanced_from d' w' end
  end.
(* each vertex in textual order with the stack of heads of the components containing it,
   innermost first; a head's own stack starts with itself *)
Fixpoint annotate {V} (stack : list V) (w : wto V) : list (V * list V) :=
  match w with
  | [] => []
  | WVertex v :: w' => (v, stack) :: annotate stack w'
  | WOpen h :: w' => (h, h :: stack) :: annotate (h :: stack) w'
  | WClose :: w' => annotate (tl stack) w'
  end.
Definition wto_order {V} (w : wto V) : list V := map fst (annotate [] w).
(* Bourdoncle's definition over the reachable nodes: every edge goes forward, or its target is
   the head of a component that contains its source *)
Definition wto_valid {V E} (g : Graph.t V E) (w : wto V) : Prop :=
  balanced_from 0 w = true /\ NoDup (wto_order w) /\
  (forall v, In v (wto_order w) <-> reachable g v) /\
  forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before (wto_order w) (Graph.source g e) (Graph.target g e) \/
    exists st, In (Graph.source g e, st) (annotate [] w) /\ In (Graph.target g e) st.
Definition check_wto {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) (w : wto V) : bool.
(* One token pass assigns positive positions and stores (pos, end) for every vertex. For a head,
   end is the position of its matching WClose; for a vertex, end is its own position. A separate
   set records heads. For each edge u -> v, accept when pos u < pos v, or when v is a head and
   pos v <= pos u <= end v. The checker also verifies balance, uniqueness and exact reachability.
   Each edge uses map and set lookups, without scanning a head stack. *)
Definition wto_of {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : wto V.
(* Bourdoncle's recursion on node lists, from the reachable nodes in rpo: the components of
   scc_within p region in reverse emission order (a topological order of the condensation); a
   non-trivial component with header h, the first of its nodes in rpo, becomes WOpen h, the order
   of its node list without h, then WClose; a singleton with a self-loop also opens a component.
   An acyclic singleton becomes WVertex. The producer is proved valid directly. *)
(* the fallback in which every node is a head, nested: the vertices of order become heads in turn *)
Definition wto_all_heads {V} (order : list V) : wto V :=
  map (fun h => WOpen h) order ++ repeat (WClose : wto_token V) (length order).
(* total: the directly proved order; the checker and fallback remain boundary utilities *)
Definition wto_total {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g) : wto V :=
  wto_of p.
```

### GRA-5: frontiers and control dependence

```coq
Definition in_df {V E} (g : Graph.t V E) (d n : V) : Prop :=
  exists e, In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = n /\
    reachable g (Graph.source g e) /\
    dominates g d (Graph.source g e) /\ ~ strictly_dominates g d n.
Inductive in_idf {V E} (g : Graph.t V E) (defs : list V) : V -> Prop :=
  | idf_step : forall d n, (In d defs \/ in_idf g defs d) -> in_df g d n -> in_idf g defs n.
Definition dominance_frontier {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) : Map.t V (FinSet.t V).
(* Cooper-Harvey-Kennedy runner walk, with no two-predecessor shortcut: for each node b and each
   reachable predecessor of b, walk up the tree from that predecessor to idom b exclusive, or to the
   root inclusive when b has no idom, adding b to the frontier of every node on the walk; the walk is
   charged to the frontier it fills. Specified for an exact tree only *)
Definition iterated_frontier {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (df : Map.t V (FinSet.t V)) (defs : list V) : FinSet.t V.      (* worklist over df with a seen set *)

(* GraphIdf.v: direct single-query IDF, without materializing all frontiers. *)
Inductive in_pruned_idf {V E} (g : Graph.t V E) (defs : list V) (live : V -> bool) : V -> Prop :=
  | pruned_idf_step : forall d n, (In d defs \/ in_pruned_idf g defs live d) ->
      in_df g d n -> live n = true -> in_pruned_idf g defs live n.
Definition direct_idf {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (defs : list V) : FinSet.t V.
Definition direct_pruned_idf {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (t : dom_tree V) (defs : list V) (live : V -> bool) : FinSet.t V.
(* A dominator-tree priority worklist visits DJ edges and processes each discovered node once.
   The pruned variant enqueues and emits only live nodes. Build indexes once; charge priority
   operations, visited edges, encoding, and output separately. *)

(* GraphControlDependence.v: edge e = (b -> s) makes n control dependent on b when n
   post-dominates s and does not strictly post-dominate b *)
Definition control_dependent {V E} (g : Graph.t V E) (exits : list V) (n : V) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ post_dominates g exits n (Graph.target g e) /\
  ~ (post_dominates g exits n (Graph.source g e) /\ n <> Graph.source g e).
Definition cdep {V E} (g : Graph.t V E) (exits : list V) (b n : V) : Prop :=
  exists e, Graph.source g e = b /\ control_dependent g exits n e.
(* every node of g reaches an exit; a client adds exits for infinite loops *)
Definition exits_reachable {V E} (g : Graph.t V E) (exits : list V) : Prop :=
  forall v, In v (Graph.nodes g) -> exists es x, path g v es x /\ In x exits.
Definition control_deps {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
  (exits : list V) (pt : dom_tree V) : Map.t V (list E).
(* n -> the edges n is control dependent on: the frontier of n in the reverse graph, edge by edge *)
```

### GRA-6a: interference and greedy colouring

```coq
Record interference (V : Type) : Type := Interference {
  vertices : FinSet.t V;
  adjacent : Map.t V (FinSet.t V)        (* symmetric; no self loops *)
}.
Definition empty_interference {V} : interference V.
Definition neighbours {V} (EV : encoding V) (ig : interference V) (v : V) : FinSet.t V :=
  match Map.get EV v (adjacent ig) with Some s => s | None => FinSet.empty end.
Definition interferes {V} (EV : encoding V) (ig : interference V) (u v : V) : Prop :=
  FinSet.mem EV v (neighbours EV ig u) = true.
Record interference_wf {V} (EV : encoding V) (ig : interference V) : Prop := {
  interferes_sym : forall u v, interferes EV ig u v -> interferes EV ig v u;
  interferes_irrefl : forall v, ~ interferes EV ig v v;
  interferes_vertex : forall u v, interferes EV ig u v -> FinSet.mem EV u (vertices ig) = true;
  vertices_wf : FinSet.wf EV (vertices ig);
  adjacent_wf : Map.wf EV (adjacent ig);
  neighbours_wf : forall v, FinSet.wf EV (neighbours EV ig v)
}.
(* an observer step for Fixpoint's replay: at a point that writes `defs`, with `src` the source
   when the point is a move, and `live` the set live after it, add (d, x) for every d in defs and
   x in FinSet.elements live with x <> d and Some x <> src; every defined and live vertex becomes a vertex *)
Definition add_point {V} (EV : encoding V) (defs : list V) (src : option V) (live : FinSet.t V)
  (ig : interference V) : interference V.

Record colour_result (V : Type) : Type := ColourResult {
  colours : Map.t V nat;                 (* colour numbers 0 .. k-1 *)
  spilled : list V
}.
Record proper_colouring {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
    (res : colour_result V) : Prop := {
  colour_below_k : forall v c, Map.get EV v (colours res) = Some c -> c < k;
  vertex_decided : forall v, FinSet.mem EV v (vertices ig) = true ->
    (exists c, Map.get EV v (colours res) = Some c) \/ In v (spilled res);
  spilled_uncoloured : forall v, In v (spilled res) -> Map.get EV v (colours res) = None;
  adjacent_differ : forall u v cu cv, interferes EV ig u v ->
    Map.get EV u (colours res) = Some cu -> Map.get EV v (colours res) = Some cv -> cu <> cv;
  precoloured_kept : forall v c, Map.get EV v pre = Some c -> Map.get EV v (colours res) = Some c
}.
Definition check_colouring {V} (EV : encoding V) (ig : interference V) (k : nat)
  (pre : Map.t V nat) (res : colour_result V) : bool.      (* one pass over vertices and neighbours *)
(* the precoloured vertices use colours below k, and no two adjacent ones share a colour *)
Definition precolour_ok {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat) : Prop :=
  (forall v c, Map.get EV v pre = Some c -> c < k) /\
  forall u v cu cv, interferes EV ig u v -> Map.get EV u pre = Some cu -> Map.get EV v pre = Some cv -> cu <> cv.
Definition greedy_colour {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) (order : list V) : colour_result V.
(* in `order`: the preferred colour of a move partner if free, else the lowest free colour, else spill *)
(* keeps the precoloured vertices (colours := pre) and spills every other vertex of ig *)
Definition all_spilled {V} (EV : encoding V) (ig : interference V) (pre : Map.t V nat) : colour_result V :=
  {| colours := pre;
     spilled := filter (fun v => negb (Map.mem EV v pre)) (FinSet.elements (vertices ig)) |}.
```

### GRA-6b: Chaitin-Briggs colouring

```coq
Definition briggs_colour {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) : colour_result V.
(* Chaitin-Briggs: simplify vertices of degree < k, push a spill candidate optimistically when none
   remains, then select in reverse order with the move bias; a failed select is an actual spill *)
Definition colour_checked {V} (EV : encoding V) (ig : interference V) (k : nat) (pre : Map.t V nat)
  (moves : list (V * V)) : colour_result V :=
  let r := briggs_colour EV ig k pre moves in
  if check_colouring EV ig k pre r then r else all_spilled EV ig pre.
(* the elimination-order form of "k-colourable by simplification" *)
Definition degenerate {V} (EV : encoding V) (ig : interference V) (k : nat) : Prop :=
  exists order, NoDup order /\ (forall v, FinSet.mem EV v (vertices ig) = true <-> In v order) /\
    forall l1 v l2, order = l1 ++ v :: l2 ->
      length (filter (fun u => FinSet.mem EV u (neighbours EV ig v)) l2) < k.
```

## Theorems

`ready EV g p` is the standing premise: the graph is well formed, no out list repeats an edge, and
`p` is its prepared form with its laws. In a statement, `R` stands for `dfs p blocked roots` where a
`Local Notation` says so. Theorems about `dominator_tree`, `wto_total` and `colour_checked` are
total: soundness holds without a premise, exactness under `dominator_exact p = true`.

### GRA-1a

```coq
Section Gra1a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v : V) (es : list E) (exits : list V).

(** Reachability is the existence of an entry path, and a reachable node of a well-formed graph is one of its nodes. *)
Theorem reachable_iff_path : reachable g v <-> exists s es, In s (Graph.entries g) /\ path g s es v.
Theorem reachable_in_nodes : graph_wf g -> reachable g v -> In v (Graph.nodes g).
(* Proof idea: induction on reachable and on the path from the entry; entries_in and out_target_in. Card: GRA-1a. *)

(** The prepared indexes agree with the graph, and no predecessor list repeats an edge. *)
Theorem prepare_ready : graph_wf g -> (forall x, NoDup (Graph.out g x)) -> ready EV g (prepare EV g).
(* Proof idea: a fold of Map.set over Graph.nodes g builds both indexes. The graph's unique nodes,
   out_source and the NoDup out lists give pred_nodup; fuel_value follows by arithmetic.
   Card: GRA-1a. *)
Theorem pred_edges_nodup : ready EV g p -> NoDup (pred_edges p v).
(* Proof idea: project pred_nodup from prepared_laws. Card: GRA-1a. *)

(** Reversal keeps the standing premise and reverses paths. *)
Theorem reverse_graph_ready :
  ready EV g p -> incl exits (Graph.nodes g) -> ready EV (reverse_graph p exits) (prepared_reverse p exits).
(* Proof idea: pred_agrees and out_source give each graph law; pred_nodup gives NoDup reverse out
   lists. The original NoDup out lists and succ_agrees give reverse pred_nodup at graph nodes;
   succ_domain gives it outside them. The edge lists on both sides have no repeats and contain the
   same edges, so their total lengths agree and fuel_value carries over. The swapped indexes agree
   by symmetry. Card: GRA-1a. *)
Theorem reverse_path :
  ready EV g p -> In u (Graph.nodes g) -> In v (Graph.nodes g) ->
  (path g u es v <-> path (reverse_graph p exits) v (rev es) u).
(* Proof idea: induction on es, with pred_agrees for each edge. Card: GRA-1a. *)
End Gra1a.
```

### GRA-1b

```coq
Section Gra1b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v s : V) (es : list E) (roots : list V) (blocked : FinSet.t V) (eqE : E -> E -> bool).
Local Notation R := (dfs p blocked roots).

(** The search visits exactly what the roots reach without entering a blocked node, each once, within `fuel p`. *)
Theorem dfs_exact : ready EV g p -> incl roots (Graph.nodes g) ->
  (FinSet.mem EV v (visited R) = true <->
   reachable (without EV blocked (set_entries g roots)) v) /\
  NoDup (preorder R) /\ Permutation (preorder R) (postorder R) /\
  (In v (preorder R) <-> FinSet.mem EV v (visited R) = true).
(* Proof idea: the stack invariant: finished nodes have all successors visited or blocked, visited nodes were reached by a path; a run that visits k new nodes takes at most 2k + (edges of those nodes) + 1 steps, within fuel p, so the fuel never runs out. Card: GRA-1b. *)
(** The plain search from the entries visits exactly the reachable nodes. *)
Theorem reachable_dfs : ready EV g p ->
  (FinSet.mem EV v (visited (dfs p FinSet.empty (Graph.entries g))) = true <-> reachable g v).
(* Proof idea: dfs_exact with nothing blocked; filtering by the empty set leaves every list unchanged, so reachability is that of g. Card: GRA-1b. *)

(** Every visited node is a root or has a tree edge from a visited parent that precedes it. *)
Theorem dfs_tree : ready EV g p -> incl roots (Graph.nodes g) -> FinSet.mem EV v (visited R) = true ->
  (In v roots /\ Map.get EV v (tree_edge R) = None) \/
  (exists e, Map.get EV v (tree_edge R) = Some e /\ In e (Graph.out g (Graph.source g e)) /\
     Graph.target g e = v /\ FinSet.mem EV (Graph.source g e) (visited R) = true /\
     before (preorder R) (Graph.source g e) v).
(* Proof idea: tree_edge is set exactly when a node is first reached through an edge. Card: GRA-1b. *)

(** In reverse postorder a parent precedes its child and a root precedes its whole tree. *)
Theorem rpo_order : ready EV g p -> incl roots (Graph.nodes g) ->
  (forall e, Map.get EV v (tree_edge R) = Some e -> before (rpo R) (Graph.source g e) v) /\
  (forall w, In v roots -> Map.get EV v (tree_edge R) = None -> FinSet.mem EV v (visited R) = true ->
     dfs_ancestor EV g R v w -> w = v \/ before (rpo R) v w).
(* Proof idea: a node finishes after its tree descendants, so it comes first in the reverse. Card: GRA-1b. *)
(** With one entry, reverse postorder starts at it. *)
Theorem rpo_single_entry : ready EV g p -> Graph.entries g = [s] ->
  exists rest, rpo (dfs p FinSet.empty (Graph.entries g)) = s :: rest.
(* Proof idea: s is the only root, and rpo_order puts it before its tree. Card: GRA-1b. *)
(** From the entries, every reachable node that is not an entry has a DFS parent earlier in reverse postorder. *)
Theorem rpo_parent_of_non_entry : ready EV g p -> reachable g v -> ~ In v (Graph.entries g) ->
  exists e, Map.get EV v (tree_edge (dfs p FinSet.empty (Graph.entries g))) = Some e /\
    before (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.source g e) v.
(* Proof idea: reachable_dfs makes v visited; only entries are roots, so dfs_tree gives a tree edge, and rpo_order orders it. Card: GRA-1b. *)

(** Every edge out of a visited node goes forward in reverse postorder or retreats to an ancestor. *)
Theorem rpo_edge_classes : ready EV g p -> incl roots (Graph.nodes g) -> forall e,
  FinSet.mem EV (Graph.source g e) (visited (dfs p FinSet.empty roots)) = true ->
  In e (Graph.out g (Graph.source g e)) ->
  before (rpo (dfs p FinSet.empty roots)) (Graph.source g e) (Graph.target g e) \/
  retreating EV g (dfs p FinSet.empty roots) e.
(* Proof idea: by finish times: tree, forward and cross edges finish their target first; an edge to an open node is retreating. Card: GRA-1b. *)
(** Every cycle through a visited node contains a retreating edge. *)
Theorem cycle_has_retreating_edge : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true -> es <> [] -> path g v es v ->
  exists e, In e es /\ retreating EV g (dfs p FinSet.empty roots) e.
(* Proof idea: if every edge went forward, positions in rpo would increase strictly around the cycle. Card: GRA-1b. *)
(** The interval test decides ancestry in constant time. *)
Theorem ancestor_b_agrees : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV u (visited R) = true -> FinSet.mem EV v (visited R) = true ->
  (ancestor_b EV R u v = true <-> dfs_ancestor EV g R u v).
(* Proof idea: tree intervals nest, and pre_num and post_num are positions in the two orders. Card: GRA-1b. *)

(** A certificate checks exactly when it is a path, and a tree path is a path from a root. *)
Theorem check_path_correct : ready EV g p -> (forall a b, eqE a b = true <-> a = b) -> In s (Graph.nodes g) ->
  (check_path p eqE s es v = true <-> path g s es v).
(* Proof idea: induction on es; the membership test is succ_agrees. Card: GRA-1b. *)
Theorem tree_path_valid : ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited R) = true ->
  exists s es, tree_path p R v = Some (s, es) /\ In s roots /\ path g s es v.
(* Proof idea: follow tree_edge to a root; each edge is a successor edge by dfs_tree. Card: GRA-1b. *)
End Gra1b.
```

### GRA-2a

```coq
Section Gra2a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (d n s : V) (m : Map.t V V).

(** Dominance is reflexive and transitive. *)
Theorem dominates_refl : dominates g n n.
Theorem dominates_trans : forall a b c, dominates g a b -> dominates g b c -> dominates g a c.
(* Proof idea: refl: an entry path ends at n, as its start or as an edge target. Trans: a path to c passes b; its prefix to b is an entry path to b, so it passes a. Card: GRA-2a. *)

(** Dominance is unreachability once the dominator is deleted; this is what the checker runs. *)
Theorem dominates_iff_unreachable_without :
  dominates g d n <-> ~ reachable (without EV (FinSet.add EV d FinSet.empty) g) n.
(* Proof idea: a path of g from an entry that avoids d, as start and as every target, is a path of the filtered graph and conversely. Card: GRA-2a. *)

Theorem virtual_entries_exact : NoDup (virtual_entries EV g) /\
  (forall v, In v (virtual_entries EV g) <-> In v (Graph.entries g)).
(* Proof idea: a set-indexed first-occurrence traversal preserves membership and order.
   Card: GRA-2a. *)
Theorem virtual_graph_ready : ready EV g p ->
  ready (virtual_encoding EV) (virtual_graph EV g) (virtual_prepared p).
(* Proof idea: tagged constructors are disjoint and injective; virtual_entries_exact gives
   unique synthetic edges and graph closure; apply prepare_ready. Card: GRA-2a. *)
Theorem virtual_path_iff : ready EV g p -> forall s es n,
  (path (virtual_graph EV g) (inr tt) (inr s :: map (@inl E V) es) (inl n) <->
   In s (Graph.entries g) /\ path g s es n).
(* Proof idea: invert the first synthetic edge, then induct on the original edge list.
   Card: GRA-2a. *)
Theorem virtual_dominates_iff : ready EV g p -> forall d n,
  (dominates g d n <-> dominates (virtual_graph EV g) (inl d) (inl n)).
(* Proof idea: every root-to-real-node path begins with one synthetic entry edge and otherwise
   contains only original edges; translate both directions using virtual_path_iff. Card: GRA-2a. *)

Theorem semidominators_wf : ready EV g p ->
  Map.wf (virtual_encoding EV) (semidominators p).
Theorem semidominators_exact : ready EV g p -> forall u n,
  (Map.get (virtual_encoding EV) n (semidominators p) = Some u <->
   reachable (virtual_graph EV g) n /\ n <> inr tt /\
   semidominator (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) u n).
(* Proof idea: DFS numbering and the semidominator path characterization reduce every candidate
   to a predecessor and a linked-tree minimum. Prove the compression segment invariant and
   reverse-order induction, including root and unreachable omissions. Card: GRA-2c. *)

Theorem simple_lt_idom_exact : ready EV g p ->
  Map.wf EV (simple_lt_idom p) /\ forest_on EV g (simple_lt_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (simple_lt_idom p) d n)).
(* Proof idea: semidominator path characterization, link/eval minimum-label invariant, bucket
   settlement and final parent correction; translate paths through the fresh virtual root.
   Card: GRA-2d. *)
Theorem semi_nca_idom_exact : ready EV g p ->
  Map.wf EV (semi_nca_idom p) /\ forest_on EV g (semi_nca_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (semi_nca_idom p) d n)).
(* Proof idea: shared semidominator and link/eval invariants and the nearest-common-ancestor
   theorem; the parent walk decreases DFS rank. Card: GRA-2e. *)
Theorem dominator_tree_with_exact : ready EV g p -> forall algorithm,
  (forall d n, reachable g n ->
    (dominates_b EV (dominator_tree_with p algorithm) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = Some d <->
     immediately_dominates g d n)) /\
  (forall n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = None <->
     forall d, ~ strictly_dominates g d n)).
(* Proof idea: apply the selected backend's exactness and forest numbering; strict dominators
   form a chain. Card: GRA-2f. *)
Theorem dominator_exact_true : ready EV g p -> dominator_exact p = true.
(* Proof idea: simple_lt_idom_exact and check_idom_complete. Card: GRA-2f. *)

(** The producer's map is well formed. *)
Theorem chk_idom_wf : ready EV g p -> Map.wf EV (chk_idom p).
(* Proof idea: simple_lt_idom_exact. Card: GRA-2f. *)

(** The checker decides exactness: an accepted map is a forest whose ancestry is dominance on every reachable node, and every such map is accepted. *)
Theorem check_idom_sound : ready EV g p -> Map.wf EV m -> check_idom p m = true ->
  forest_on EV g m /\ forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n).
(* Proof idea: the numbering check gives the forest; dominates_iff_unreachable_without and dfs_exact for each blocked search give the iff for reachable d; an unreachable d dominates no reachable node and is no ancestor of one. Card: GRA-2f. *)
Theorem check_idom_complete : ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n)) -> check_idom p m = true.
(* Proof idea: each test of the checker is an instance of the hypothesis, by the same two theorems read backwards; well-foundedness makes the numbering reach every key. Card: GRA-2f. *)

(** The numbering of a forest is the interval encoding of its ancestry on the reachable nodes. *)
Theorem dom_tree_of_agrees : ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall n, (exists a, Map.get EV n (tin (dom_tree_of p m)) = Some a) <-> reachable g n) /\
  (forall d n, reachable g n -> (dominates_b EV (dom_tree_of p m) d n = true <-> idom_ancestor EV m d n)).
(* Proof idea: the DFS of the forest visits every node below a root; intervals of a DFS nest exactly along ancestry (ancestor_b_agrees on the forest). Card: GRA-2f. *)

(** The fallback is a forest: no parents, or the sole entry as the parent of every other reachable node. *)
Theorem flat_idom_shape : ready EV g p ->
  Map.wf EV (flat_idom p) /\ forest_on EV g (flat_idom p) /\
  ((Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s) ->
     forall n, Map.get EV n (flat_idom p) = Some s <-> (reachable g n /\ n <> s)) /\
  ((forall s', ~ (Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s')) ->
     forall n, Map.get EV n (flat_idom p) = None).
(* Proof idea: unfold the fold over the preorder (reachable_dfs): each key is a reachable non-entry with the entry as its parent, which is a root. Card: GRA-2f. *)

(** The total tree is always sound: it covers the reachable nodes, its ancestry and its interval test imply dominance, and each parent strictly dominates its child. *)
Theorem dominator_tree_sound : ready EV g p ->
  (forall n, (exists a, Map.get EV n (tin (dominator_tree p)) = Some a) <-> reachable g n) /\
  (forall d n, idom_ancestor EV (idom (dominator_tree p)) d n -> dominates g d n) /\
  (forall d n, dominates_b EV (dominator_tree p) d n = true -> dominates g d n) /\
  (forall n d, Map.get EV n (idom (dominator_tree p)) = Some d -> strictly_dominates g d n).
(* Proof idea: simple_lt_idom_exact, dom_tree_of_agrees and dominance reflexivity. Card: GRA-2f. *)

(** When the checker accepted the map, the tree is exact: interval dominance is dominance, the parent of a node is its immediate dominator, and the roots have no strict dominator. *)
Theorem dominator_tree_exact : ready EV g p -> dominator_exact p = true ->
  (forall d n, reachable g n -> (dominates_b EV (dominator_tree p) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
     (Map.get EV n (idom (dominator_tree p)) = Some d <-> immediately_dominates g d n)) /\
  (forall n, reachable g n ->
     (Map.get EV n (idom (dominator_tree p)) = None <-> forall d, ~ strictly_dominates g d n)).
(* Proof idea: dominator_tree_with_exact for SimpleLT. Card: GRA-2f. *)
End Gra2a.
```

### GRA-2b

```coq
Section Gra2b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (d n : V) (e : E) (exits : list V).

(** With an exact tree, an edge dominates n exactly when it is the dominating edge of a node that dominates n. *)
Theorem edge_dominates_iff : ready EV g p -> dominator_exact p = true -> reachable g n ->
  (edge_dominates g e n <->
   exists v, Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e /\
             dominates_b EV (dominator_tree p) v n = true).
(* Proof idea: e dominates n iff e dominates its target v and v dominates n (take the last occurrence of e on an entry path to n); e dominates v iff v is not an entry and e is the sole in-edge of v from a reachable source that v does not dominate (a shortest entry path to v ends in such an edge). pred_edges_nodup makes the count exact. Card: GRA-2b. *)
(** `dominating_edges` returns only edges that dominate n, with no premise that the checker accepted the tree. *)
Theorem dominating_edges_sound : ready EV g p ->
  In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) ->
  edge_dominates g e n.
(* Proof idea: an imprecise tree can only count too many in-edges as not dominated by v, which drops the index entry and never invents one; each ancestor of n dominates n by dominator_tree_sound, and dominates_trans composes. Card: GRA-2b. *)
(** With an exact tree, `dominating_edges` lists exactly the edges that dominate n. *)
Theorem dominating_edges_exact : ready EV g p -> dominator_exact p = true -> reachable g n ->
  (In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) <->
   edge_dominates g e n).
(* Proof idea: the dominators of n are its idom chain, then edge_dominates_iff. Card: GRA-2b. *)
(** A self-loop never dominates its own node: the first arrival does not use it. *)
Theorem self_loop_not_edge_dominating :
  reachable g n -> Graph.source g e = n -> Graph.target g e = n -> ~ edge_dominates g e n.
(* Proof idea: a shortest entry path to n contains no edge out of n. Card: GRA-2b. *)

(** Post-dominance is dominance in the reverse graph, and the post-dominator tree answers it soundly always and exactly when its checker accepted. *)
Theorem post_dominates_iff_reverse : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  (post_dominates g exits d n <-> dominates (reverse_graph p exits) d n).
(* Proof idea: reverse_path, with the exits as the entries; the nodes visited are the same set read in the other direction. Card: GRA-2b. *)
Theorem post_dominator_tree_sound : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominates_b EV (post_dominator_tree p exits) d n = true -> post_dominates g exits d n.
(* Proof idea: reverse_graph_ready, dominator_tree_sound on the reverse graph, then the previous theorem. Card: GRA-2b. *)
Theorem post_dominator_tree_exact : ready EV g p -> incl exits (Graph.nodes g) -> In n (Graph.nodes g) ->
  dominator_exact (prepared_reverse p exits) = true -> (exists es x, path g n es x /\ In x exits) ->
  (dominates_b EV (post_dominator_tree p exits) d n = true <-> post_dominates g exits d n).
(* Proof idea: reverse_graph_ready, dominator_tree_exact on the reverse graph (n is reachable there by reverse_path), then the previous theorem. Card: GRA-2b. *)
End Gra2b.
```

### GRA-3a

```coq
Section Gra3a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (u v : V) (e : E) (region : list V).
Local Abbreviation R := (scc p).

(** The components partition the region, and two nodes share one exactly when each reaches the other inside it. *)
Theorem scc_within_exact : ready EV g p -> incl region (Graph.nodes g) ->
  NoDup (concat (components (scc_within p region))) /\
  (forall x, In x (concat (components (scc_within p region))) <-> In x region) /\
  (forall c, In c (components (scc_within p region)) -> c <> []) /\
  length (component_ids (scc_within p region)) = length (components (scc_within p region)) /\
  (forall i c, Trie.get i (component_at (scc_within p region)) = Some c <->
     In (i, c) (combine (component_ids (scc_within p region))
                        (components (scc_within p region)))) /\
  NoDup (component_ids (scc_within p region)) /\
  (forall x i, Map.get EV x (comp_of (scc_within p region)) = Some i <->
     exists c, Trie.get i (component_at (scc_within p region)) = Some c /\ In x c) /\
  (In u region -> In v region ->
     ((exists i, Map.get EV u (comp_of (scc_within p region)) = Some i /\
                 Map.get EV v (comp_of (scc_within p region)) = Some i) <->
      mutual (induced EV (FinSet.of_list EV region) g) u v)).
(* Proof idea: the invariant I1 to I4 of the machine, with the fuel bound 2|region| + edges + 1 of fuel p; a node is popped with its root's component iff it reaches and is reached from the root inside the region. Card: GRA-3a. *)
(** Components are emitted after every component they reach. *)
Theorem scc_reverse_topological : ready EV g p -> incl region (Graph.nodes g) ->
  In e (Graph.out g (Graph.source g e)) -> In (Graph.source g e) region -> In (Graph.target g e) region ->
  exists i j, Map.get EV (Graph.source g e) (comp_of (scc_within p region)) = Some i /\
    Map.get EV (Graph.target g e) (comp_of (scc_within p region)) = Some j /\ (j <= i)%positive.
(* Proof idea: I1: an edge leaving an emitted component enters an earlier one, and an edge inside a component has equal indices. Card: GRA-3a. *)
(** On the whole graph the components are the mutual-reachability classes of g. *)
Theorem scc_exact : ready EV g p ->
  NoDup (concat (components R)) /\ (forall x, In x (concat (components R)) <-> In x (Graph.nodes g)) /\
  (In u (Graph.nodes g) -> In v (Graph.nodes g) ->
     ((exists i, Map.get EV u (comp_of R) = Some i /\ Map.get EV v (comp_of R) = Some i) <-> mutual g u v)).
(* Proof idea: scc_within_exact with region = nodes g; the induced graph keeps every edge of g, since out_target_in puts every target in nodes g. Card: GRA-3a. *)
(** The condensation is a well-formed DAG with the stated edges, entries and a topological order. *)
Theorem condensation_correct : ready EV g p ->
  graph_wf (condensation p R) /\ (forall c, NoDup (Graph.out (condensation p R) c)) /\
  acyclic (condensation p R) /\
  topological_order (condensation p R) (rev (component_ids R)) /\
  (forall c e', In e' (Graph.out (condensation p R) c) <->
     exists x j, In x (Graph.nodes g) /\ In e' (Graph.out g x) /\ Map.get EV x (comp_of R) = Some c /\
       Map.get EV (Graph.target g e') (comp_of R) = Some j /\ j <> c) /\
  (forall c, In c (Graph.entries (condensation p R)) <->
     exists s, In s (Graph.entries g) /\ Map.get EV s (comp_of R) = Some c) /\
  NoDup (Graph.entries (condensation p R)) /\
  (forall e', In (Graph.source g e') (Graph.nodes g) -> In (Graph.target g e') (Graph.nodes g) ->
     exists i j, Map.get EV (Graph.source g e') (comp_of R) = Some i /\
       Map.get EV (Graph.target g e') (comp_of R) = Some j /\
       Graph.source (condensation p R) e' = i /\ Graph.target (condensation p R) e' = j).
(* Proof idea: a cycle of components would merge them by scc_exact; the order is scc_reverse_topological; the out lists are sublists of out lists of g, kept whole. Card: GRA-3a. *)
End Gra3a.
```

### GRA-3b

```coq
Section Gra3b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (v : V) (w : E -> Z) (fwd : V -> bool).

(** A topological sort exists exactly when the graph is acyclic. *)
Theorem topological_sort_correct : ready EV g p ->
  (forall l, topological_sort p = Some l -> topological_order g l) /\
  (topological_sort p = None <-> ~ acyclic g).
(* Proof idea: rpo of a search from every node; an edge goes forward unless it retreats, and a retreating edge closes a cycle with the tree path. Card: GRA-3b. *)

(** On a graph whose reachable part is acyclic, `max_paths` is exact and attained; it fails only on a reachable cycle. *)
Theorem max_paths_exact : ready EV g p ->
  (forall v es, reachable g v -> es <> [] -> ~ path g v es v) ->
  exists r, max_paths p w = Some r /\ forall v,
    (reachable g v <-> exists b, Map.get EV v (best r) = Some b) /\
    forall b, Map.get EV v (best r) = Some b ->
      (exists s es, max_path_to p r v = Some (s, es) /\ In s (Graph.entries g) /\ path g s es v /\
         path_weight w es = b) /\
      (forall s es, In s (Graph.entries g) -> path g s es v -> (path_weight w es <= b)%Z).
(* Proof idea: dynamic programming in the rpo of the reachable part, where every edge goes forward (rpo_edge_classes with no retreating edge); via records an arg-max edge. Card: GRA-3b. *)
Theorem max_paths_cycle : ready EV g p -> max_paths p w = None ->
  exists v es, reachable g v /\ es <> [] /\ path g v es v.
(* Proof idea: None arises only from a retreating edge out of a reachable node, which closes a cycle with the tree path. Card: GRA-3b. *)

(** `resolve` lands where the forwarding chain ends, is Cyclic exactly when it never ends, and `resolve_all` agrees with it. *)
Theorem resolve_correct : ready EV g p -> In v (Graph.nodes g) ->
  (forall x, resolve p fwd v = Landing x <-> exists es, chain g fwd v es x) /\
  (resolve p fwd v = Cyclic <-> forall es x, ~ chain g fwd v es x) /\
  Map.get EV v (resolve_all p fwd) = Some (resolve p fwd v).
(* Proof idea: forward_step is a function, so a chain is unique; a repeated node proves a cycle, and the walk visits at most |nodes| nodes, within fuel p. Card: GRA-3b. *)
End Gra3b.
```

### GRA-4a

```coq
Section Gra4a.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (x : V) (e : E).

(** Back edges retreat in every search, and every retreating edge is a back edge exactly when the graph is reducible. *)
Theorem back_edge_retreating : ready EV g p -> back_edge g e ->
  retreating EV g (dfs p FinSet.empty (Graph.entries g)) e.
(* Proof idea: the target dominates the source, so it lies on the tree path to the source (tree_path_valid). Card: GRA-4a. *)
Theorem reducible_iff_retreating_back : ready EV g p ->
  (reducible g <-> forall e, In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) ->
     retreating EV g (dfs p FinSet.empty (Graph.entries g)) e -> back_edge g e).
(* Proof idea: right to left: cycle_has_retreating_edge puts a retreating edge on every cycle, and it is a back edge. Left to right: the tree path from the target to the source and the edge form a cycle; a tree edge is never a back edge, since the entry path of tree edges to its source does not contain its target, so the retreating edge must be the back edge. Card: GRA-4a. *)
(** The interval check is sound always and decides reducibility under an exact tree. *)
Theorem reducible_b_sound : ready EV g p -> reducible_b p (dominator_tree p) = true -> reducible g.
(* Proof idea: dominates_b is sound (dominator_tree_sound), so every retreating edge is a back edge; reducible_iff_retreating_back. Card: GRA-4a. *)
Theorem reducible_b_correct : ready EV g p -> dominator_exact p = true ->
  (reducible_b p (dominator_tree p) = true <-> reducible g).
(* Proof idea: reducible_iff_retreating_back, with dominates_b equal to dominates on reachable nodes by dominator_tree_exact. Card: GRA-4a. *)

(** One reverse search computes a natural loop. *)
Theorem natural_loop_nodes_exact : ready EV g p -> In (Graph.source g e) (Graph.nodes g) ->
  In x (Graph.nodes g) ->
  (FinSet.mem EV x (natural_loop_nodes p e) = true <-> natural_loop EV g e x).
(* Proof idea: dfs_exact on prepared_reverse with the target blocked, and reverse_path; the target is added by hand. Card: GRA-4a. *)
End Gra4a.
```

### GRA-4b

```coq
Section Gra4b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Local Notation F := (loop_forest_of p).

(** The loop forest nests strictly, lists each header once with an outer loop first, and `loop_of` names the innermost loop. *)
Theorem loop_forest_nested : ready EV g p ->
  (forall h, In h (loop_headers F) <-> exists s, Map.get EV h (loop_nodes F) = Some s) /\
  NoDup (loop_headers F) /\
  (forall h, In h (loop_headers F) -> In h (Graph.nodes g) /\ in_loop EV F h h) /\
  (forall h h', Map.get EV h (loop_parent F) = Some h' ->
     before (loop_headers F) h' h /\
     (forall y, in_loop EV F h y -> in_loop EV F h' y) /\ ~ in_loop EV F h h') /\
  (forall y h, Map.get EV y (loop_of F) = Some h ->
     in_loop EV F h y /\ forall h', in_loop EV F h' y -> in_loop EV F h' h) /\
  (forall y, Map.get EV y (loop_of F) = None -> forall h, ~ in_loop EV F h y).
(* Proof idea: induction on the recursion depth of loop_forest_of; each level removes one header, and the headers of a level are emitted after the header whose loop contains them. Card: GRA-4b. *)
(** Each loop is a non-trivial strongly connected component of the set it lives in, headed by its first node in rpo. *)
Theorem loop_forest_exact : ready EV g p -> forall h, In h (loop_headers F) ->
  strong_component (induced EV (outer_nodes p F h) g) (in_loop EV F h) /\
  (exists es, es <> [] /\ path (induced EV (outer_nodes p F h) g) h es h) /\
  (forall y, in_loop EV F h y -> y = h \/ before (rpo (dfs p FinSet.empty (Graph.entries g))) h y).
(* Proof idea: each level computes scc_within of its list (scc_within_exact); the header is the rpo-first member by construction. Card: GRA-4b. *)
(** Every cycle through a reachable node lies in the loop of one of its own nodes, irreducible graphs included. *)
Theorem loop_forest_covers : ready EV g p -> forall v es, reachable g v -> es <> [] -> path g v es v ->
  exists h, In h (loop_headers F) /\ (h = v \/ In h (map (Graph.target g) es)) /\
    forall y, (y = v \/ In y (map (Graph.target g) es)) -> in_loop EV F h y.
(* Proof idea: take the outermost level whose set contains the cycle; either its header is on the cycle, or the cycle survives the header's removal and the recursion applies. Card: GRA-4b. *)
End Gra4b.
```

### GRA-4c

```coq
Section Gra4c.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (w : wto V) (order : list V).

(** The WTO check decides Bourdoncle's definition, and in a valid order every cycle lies in a component whose head is on the cycle. *)
Theorem check_wto_correct : ready EV g p -> (check_wto p w = true <-> wto_valid g w).
(* Proof idea: the token pass records each head's matching close; its interval contains exactly the
   positions whose annotation includes that head. Card: GRA-4c. *)
Theorem wto_valid_cycles : wto_valid g w -> forall v es, reachable g v -> es <> [] -> path g v es v ->
  exists h, (h = v \/ In h (map (Graph.target g) es)) /\
    forall y st, (y = v \/ In y (map (Graph.target g) es)) -> In (y, st) (annotate [] w) -> In h st.
(* Proof idea: the textually first node m of the cycle has its incoming cycle edge going backward, so m is the head of a component containing that edge's source; well-nesting then forces the component to contain the whole cycle. Card: GRA-4c. *)

(** The all-heads order is valid for every listing of the reachable nodes, so the fallback is valid. *)
Theorem wto_all_heads_valid : ready EV g p -> NoDup order -> (forall v, In v order <-> reachable g v) ->
  wto_valid g (wto_all_heads order).
(* Proof idea: annotate gives the i-th node the stack of the heads up to itself, so an edge goes forward in the list or has its target among the heads before and including its source. Card: GRA-4c. *)
(** The recursive SCC producer itself produces a valid order. *)
Theorem wto_of_valid : ready EV g p -> wto_valid g (wto_of p).
(* Proof idea: induct on the strictly decreasing region; SCC emission orders cross-component
   edges forward, and removing the selected head encloses each remaining backward edge.
   Card: GRA-4c. *)
(** The total order is always valid. *)
Theorem wto_total_valid : ready EV g p -> wto_valid g (wto_total p).
(* Proof idea: wto_of_valid. Card: GRA-4c. *)
End Gra4c.
```

### GRA-5

```coq
Section Gra5.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (n : V) (e : E) (defs exits : list V).

(** The runner chain contains exactly the dominance-frontier witnesses for one incoming edge. *)
Theorem dominance_chain : ready EV g p -> dominator_exact p = true ->
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) -> forall d,
  (dominates g d (Graph.source g e) /\ ~ strictly_dominates g d (Graph.target g e) <->
   dominates_b EV (dominator_tree p) d (Graph.source g e) = true /\
   (forall q, Map.get EV (Graph.target g e) (idom (dominator_tree p)) = Some q ->
      dominates_b EV (dominator_tree p) d q = false)).
(* Proof idea: the immediate dominator of the target dominates each reachable predecessor; its
   ancestors are exactly the strict dominators of the target. Apply dominator_tree_exact to the
   predecessor and parent. With no parent the runner reaches the root. Card: GRA-5. *)

(** With an exact tree, the computed frontiers are the dominance frontiers, and the iterated frontier is the least closed set. *)
Theorem dominance_frontier_exact : ready EV g p -> dominator_exact p = true -> forall d n,
  ((exists s, Map.get EV d (dominance_frontier p (dominator_tree p)) = Some s /\
              FinSet.mem EV n s = true) <-> in_df g d n).
(* Proof idea: dominance_chain identifies each runner walk with its frontier witnesses.
   Card: GRA-5. *)
Theorem iterated_frontier_exact : ready EV g p -> dominator_exact p = true ->
  (FinSet.mem EV n (iterated_frontier p (dominance_frontier p (dominator_tree p)) defs) = true <->
   in_idf g defs n).
(* Proof idea: worklist invariant: the seen set is closed under df and every member is derived by idf_step. Card: GRA-5. *)

(** Control dependence is the post-dominance frontier, edge by edge, for an exact post-dominator tree. *)
Theorem control_deps_exact : ready EV g p -> incl exits (Graph.nodes g) -> exits_reachable g exits ->
  dominator_exact (prepared_reverse p exits) = true -> In n (Graph.nodes g) ->
  In (Graph.source g e) (Graph.nodes g) ->
  ((exists l, Map.get EV n (control_deps p exits (post_dominator_tree p exits)) = Some l /\ In e l) <->
   control_dependent g exits n e).
(* Proof idea: dominance_chain on the reverse graph identifies the runner for each edge, and
   post_dominates_iff_reverse translates its witnesses to control dependence. Card: GRA-5. *)
End Gra5.
```

### GRA-7: direct iterated-frontier queries

```coq
Section Gra7.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (defs : list V) (live : V -> bool) (n : V).
Theorem direct_idf_exact : ready EV g p ->
  (FinSet.mem EV n (direct_idf p (dominator_tree p) defs) = true <-> in_idf g defs n).
Theorem direct_pruned_idf_exact : ready EV g p ->
  (FinSet.mem EV n (direct_pruned_idf p (dominator_tree p) defs live) = true <->
   in_pruned_idf g defs live n).
(* Proof idea: the DJ traversal discovers exactly the frontier of each processed definition;
   induction over worklist steps and derivations proves soundness and least-closure completeness.
   The pruning proof includes the live predicate on each derivation step. Card: GRA-7. *)
End Gra7.
```

### GRA-6a

```coq
Section Gra6a.
Context {V : Type} (EV : encoding V).
Variables (ig : interference V) (k : nat) (pre : Map.t V nat) (moves : list (V * V))
  (order : list V) (defs : list V) (src : option V) (live : FinSet.t V).

(** The observer step adds exactly the interferences of one point, makes every defined and live node a vertex, and keeps the graph symmetric and loop-free. *)
Theorem add_point_exact : FinSet.wf EV live -> forall u v,
  interferes EV (add_point EV defs src live ig) u v <->
  (interferes EV ig u v \/
   (In u defs /\ FinSet.mem EV v live = true /\ v <> u /\ Some v <> src) \/
   (In v defs /\ FinSet.mem EV u live = true /\ u <> v /\ Some u <> src)).
(* Proof idea: add_point is a fold of FinSet.add into both adjacency sets, over defs and FinSet.elements live; FinSet.elements_spec turns elements into membership. Card: GRA-6a. *)
Theorem add_point_vertices : FinSet.wf EV live -> forall v,
  FinSet.mem EV v (vertices (add_point EV defs src live ig)) = true <->
  (FinSet.mem EV v (vertices ig) = true \/ In v defs \/ FinSet.mem EV v live = true).
(* Proof idea: vertices only grow, by the defined nodes and the elements of live (FinSet.elements_spec). Card: GRA-6a. *)
Theorem add_point_wf : interference_wf EV ig -> FinSet.wf EV live ->
  interference_wf EV (add_point EV defs src live ig).
(* Proof idea: each added pair is added in both directions and skips equal ends; Map.wf_set and FinSet.wf_ops keep the stored sets well formed. Card: GRA-6a. *)

(** The checker decides properness. *)
Theorem check_colouring_correct : forall res, interference_wf EV ig -> Map.wf EV pre -> Map.wf EV (colours res) ->
  (check_colouring EV ig k pre res = true <-> proper_colouring EV ig k pre res).
(* Proof idea: unfold; each clause is one pass over the vertices and their neighbour sets, and Map.elements_spec on the well-formed maps. Card: GRA-6a. *)
(** Greedy colouring is proper for every order and move bias, and spills nothing when every degree is below k. *)
Theorem greedy_colour_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  proper_colouring EV ig k pre (greedy_colour EV ig k pre moves order).
(* Proof idea: invariant: the coloured part is proper; a vertex takes a colour absent from its coloured neighbours. Card: GRA-6a. *)
Theorem greedy_no_spill : interference_wf EV ig -> (forall v, (FinSet.size (neighbours EV ig v) < k)%nat) ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  spilled (greedy_colour EV ig k Map.empty moves order) = [].
(* Proof idea: neighbours_wf makes FinSet.size the number of neighbours (FinSet.size_elements); fewer than k forbidden colours leave one free. Card: GRA-6a. *)
End Gra6a.
```

### GRA-6b

```coq
Section Gra6b.
Context {V : Type} (EV : encoding V).
Variables (ig : interference V) (k : nat) (pre : Map.t V nat) (moves : list (V * V)).

(** Chaitin-Briggs colouring is proper, and the checked wrapper is proper even if the producer is wrong. *)
Theorem briggs_colour_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  proper_colouring EV ig k pre (briggs_colour EV ig k pre moves).
(* Proof idea: select pops every pushed vertex once with the greedy step; simplify only removes vertices. Card: GRA-6b. *)
Theorem colour_checked_proper : interference_wf EV ig -> Map.wf EV pre -> precolour_ok EV ig k pre ->
  proper_colouring EV ig k pre (colour_checked EV ig k pre moves).
(* Proof idea: check_colouring_correct on the accepted branch (the producer's colour map is built from pre by Map.set, so it is well formed); the all-spilled branch is proper by precolour_ok. Card: GRA-6b. *)
(** Nothing spills when the graph simplifies completely; this is stated without precolouring. *)
Theorem briggs_no_spill : interference_wf EV ig -> degenerate EV ig k ->
  spilled (briggs_colour EV ig k Map.empty moves) = [].
(* Proof idea: a degenerate graph always has a vertex of degree < k to simplify, and at select time fewer than k of its neighbours are coloured. Card: GRA-6b. *)
End Gra6b.
```

## Algorithms and references

- **Depth-first search**, iterative with an explicit stack: Tarjan, "Depth-first search and linear
  graph algorithms", SIAM J. Comput. 1972. Reverse postorder and the edge classes are the standard
  forest classification. With several entries the roots form a forest, so an entry reached from an
  earlier one lies in that tree; `rpo_single_entry` is the single-entry statement, and dominance
  uses a virtual root above the roots.
- **Dominators:** Lengauer and Tarjan (1979) simple LT and Georgiadis (2005) Semi-NCA share
  DFS, semidominators and link/eval; each backend is directly proved exact. A fresh tagged virtual
  root handles multiple entries. `check_idom` remains an independent boundary checker.
- **Edge dominance:** an edge dominates a node `v` exactly when it is the only in-edge of `v` from
  a reachable node that `v` does not dominate; then it dominates what `v` dominates.
- **Strongly connected components:** Tarjan 1972, with an explicit stack and lowlinks, stated as the
  invariant I1 to I4; `scc_within` runs on a node list so that loop forests and weak orders recurse
  without filtering the whole graph. **DAG paths** by dynamic programming in the rpo of the
  reachable part; **forwarding chains** by memoised walking.
- **Loops:** Steensgaard, "Sequentializing program dependence graphs for irreducible programs"
  (1993) and Ramalingam, "On loops, dominators, and dominance frontiers" (TOPLAS 2002) for the
  recursive decomposition; Havlak (TOPLAS 1997) for irreducible loops. **Reducibility:** Hecht and
  Ullman (1972). **WTO:** Bourdoncle, "Efficient chaotic iteration strategies with widenings"
  (1993); the checker is his definition, so a wrong producer cannot cause an unsound schedule, and
  the all-heads order is the always-valid fallback.
- **Frontiers and control dependence:** Cytron, Ferrante, Rosen, Wegman and Zadeck (TOPLAS 1991)
  and the runner walk of Cooper, Harvey and Kennedy; Ferrante, Ottenstein and Warren (TOPLAS 1987).
  Both are specified for an exact tree only.
- **Colouring:** Chaitin et al. (1981); Briggs, Cooper and Torczon (TOPLAS 1994) for optimistic
  colouring; George and Appel (1996) for the move bias. Spill choice is a heuristic and not
  specified; properness and the no-spill guarantees are.

## Performance notes

- `prepare` is one pass over `Graph.nodes g` and their edges, with map costs of O(P) per
  operation; every later algorithm reads adjacency and predecessors by lookup in that index.
  Each adjacency list is traversed as required by the algorithm; do not repeatedly scan the full
  graph or unrelated lists. The `before`, `In` and `incl` forms appear in statements only.
  Prove a binary fuel bound for each traversal, including initialization and skipped roots.
- Each prepared index has an agreement lemma: `out_index` with `succ_agrees`, `in_index` with
  `pred_agrees`, `fuel` with `fuel_value`, `pre_num` and `post_num` with `ancestor_b_agrees`,
  `tin` and `tout` with `dom_tree_of_agrees`, `edge_dom_index` with `edge_dominates_iff`,
  `comp_of` with `scc_within_exact`.
- `dfs`, `rpo`, `scc`, `condensation`, `topological_sort`, `max_paths` and `resolve_all` take
  O(V + E) graph operations plus map, key, weight and output costs. Frontier and control-dependence
  runner walks cost O(V + E + visits), with up to O(VE) visits including repeated parallel edges.
- `check_idom` is O(V * (V + E)) graph operations:
  one blocked search per reachable node, over the same prepared index. `dominates_b` and
  `ancestor_b` queries are O(1) interval tests plus map lookups.
- `loop_forest_of` and `wto_of` are O((V + E) * d) for loop depth `d`, since each level is one
  `scc_within` call on a list; `natural_loop_nodes` is proportional to the loop and its incoming
  edges, because the search starts at one node and stops at the header. Materialized loop-node sets
  can themselves contain Theta(Vd) memberships. Map operations cost O(P), where P is the encoded
  key length, not necessarily O(log V); also count binary arithmetic, allocations and output.
- Colouring keeps a degree-bucket map (`Map.t nat (FinSet.t V)`) for simplify and forbidden colours
  as a set per vertex; finding a free colour is O(k).

## Open questions

1. **Edge equality.** `check_path` takes `eqE : E -> E -> bool` instead of an `encoding E`, so
   graphs with opaque edge types need no encoding; membership is a scan of one successor list,
   which is bounded by the out-degree of one node.
2. **Direct producers.** The selected dominator backend and `wto_of` are directly proved; boundary
   checkers remain useful for externally supplied candidates and differential examples.

## Cross-document contracts

Fixpoint uses `Graph.t`, `Graph.out`, `Graph.target`, `prepare`, `ready` and `wto_total`.
The dependency graph has duplicate-free outgoing edges. Views uses the total dominator tree
and its sound edge index; its soundness theorem requires duplicate-free outgoing edges.
Analyses uses `cdep`, `exits_reachable` and `max_paths` on the prepared reachable graph.
