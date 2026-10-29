(** * Refinement at dominated uses

    Strict SSA frames transport guards and operand equations to dominated reads.
    For example, a constant guard refines a value throughout the edge's dominated region.
    Builds on: ViewsSsa, ViewsRefine and GraphEdgeDominance. *)

From Stdlib Require Import List Arith Lia Wf_nat PArith Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderConcrete OrderLift.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphLengauerTarjan GraphDominators GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsRefine.
Import List.ListNotations.

(** Strict SSA restricts redefinition and positively preserves bindings away from their homes. *)
Record strict_ssa_laws {S O N E V K C} (m : semantics S O)
    (sv : ssa_view S O N E V K C) : Prop := {
  redefine_in_stay : forall s l s' x, reachable_state m s -> step m s l s' ->
    stays (base sv) s l s' -> val sv s' x <> val sv s x -> point (base sv) s = home sv x;
  redefine_on_edge : forall s l s' e x, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> val sv s' x <> val sv s x -> home sv x = point (base sv) s';
  frame_in_stay : forall s l s' x, reachable_state m s -> step m s l s' ->
    stays (base sv) s l s' -> point (base sv) s <> home sv x -> val sv s' x = val sv s x;
  frame_on_edge : forall s l s' e x, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> home sv x <> point (base sv) s' -> val sv s' x = val sv s x;
  guard_home : forall e cd, In e (edges_of (cfg (base sv))) -> In cd (edge_guard sv e) ->
    dominates (cfg (base sv)) (home sv (subject cd)) (Graph.source (cfg (base sv)) e);
  op_args_dominate : forall x o args y, def sv x = Op o args -> In y args ->
    dominates (cfg (base sv)) (home sv y) (home sv x)
}.

Arguments redefine_in_stay {S O N E V K C m sv} _ s l s' x _ _ _ _.
Arguments redefine_on_edge {S O N E V K C m sv} _ s l s' e x _ _ _ _.
Arguments frame_in_stay {S O N E V K C m sv} _ s l s' x _ _ _ _.
Arguments frame_on_edge {S O N E V K C m sv} _ s l s' e x _ _ _ _.
Arguments guard_home {S O N E V K C m sv} _ e cd _ _.
Arguments op_args_dominate {S O N E V K C m sv} _ x o args y _ _.

(** * Constructive finite-path reasoning *)

(* Only listed nodes are compared; there is no equality decision on the carrier. *)
Lemma listed_nodes_eq {A} (xs : list A) : NoDup xs ->
  forall x y, In x xs -> In y xs -> x = y \/ x <> y.
Proof.
  intro Hdistinct; induction Hdistinct as [|a xs Hfresh Hdistinct IH];
    intros x y Hx Hy; [contradiction|].
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy].
  - left; congruence.
  - right; intro Heq; subst; contradiction.
  - right; intro Heq; subst; contradiction.
  - apply IH; assumption.
Qed.

(** * Edge-occurrence projection *)

(* Distinct occurrences may carry equal client edges. Projecting occurrences keeps
   their order and multiplicity, so every traversal performs the same node work. *)
Module EdgeProjection.

(** Projection keeps nodes and the ordered occurrences of all outgoing edges. *)
Record graph_laws {N E F} (g : Graph.t N E) (h : Graph.t N F) (f : E -> F) : Prop := {
  entries_agree : Graph.entries h = Graph.entries g;
  nodes_agree : Graph.nodes h = Graph.nodes g;
  out_agree : forall n, Graph.out h n = map f (Graph.out g n);
  source_agree : forall e, Graph.source h (f e) = Graph.source g e;
  target_agree : forall e, Graph.target h (f e) = Graph.target g e
}.

Lemma map_set {N E F} (EN : encoding N) (f : E -> F) n e m :
  Map.map f (Map.set EN n e m) = Map.set EN n (f e) (Map.map f m).
Proof.
  apply Trie.extensionality; intro p; unfold Map.map, Map.set.
  rewrite Trie.get_map.
  destruct (Pos.eq_dec p (encode EN n)) as [Heq|Hneq].
  - subst p; rewrite !Trie.get_set_same; reflexivity.
  - rewrite !Trie.get_set_other by congruence; rewrite Trie.get_map; reflexivity.
Qed.

Lemma map_empty {N E F} (f : E -> F) : Map.map f (@Map.empty N E) = Map.empty.
Proof.
  reflexivity.
Qed.

Lemma map_filter {E F} (f : E -> F) (p : F -> bool) xs :
  map f (filter (fun e => p (f e)) xs) = filter p (map f xs).
Proof.
  induction xs as [|e xs IH]; [reflexivity|].
  cbn; destruct (p (f e)); cbn; rewrite IH; reflexivity.
Qed.

Lemma prepare_succ_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f -> forall n,
  succ_edges (prepare EN h) n = map f (succ_edges (prepare EN g) n).
Proof.
  intros Hgraph n; unfold succ_edges; cbn [prepare out_index].
  rewrite !prepare_succ, (nodes_agree _ _ _ Hgraph), (out_agree _ _ _ Hgraph n).
  destruct (existsb _ _); reflexivity.
Qed.

Lemma flat_edges_agree {N E F} (g : Graph.t N E) (h : Graph.t N F) f :
  graph_laws g h f -> forall ns,
  flat_map (Graph.out h) ns = map f (flat_map (Graph.out g) ns).
Proof.
  intros Hgraph ns; induction ns as [|n ns IH]; [reflexivity|].
  cbn; rewrite (out_agree _ _ _ Hgraph), IH, map_app; reflexivity.
Qed.

Lemma prepare_pred_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f -> forall n,
  pred_edges (prepare EN h) n = map f (pred_edges (prepare EN g) n).
Proof.
  intros Hgraph n; rewrite !prepare_pred, (nodes_agree _ _ _ Hgraph).
  rewrite (flat_edges_agree g h f Hgraph).
  rewrite <- map_filter.
  f_equal; apply filter_ext; intro e; rewrite (target_agree _ _ _ Hgraph); reflexivity.
Qed.

Lemma edge_count_agree {N E F} (g : Graph.t N E) (h : Graph.t N F) f :
  graph_laws g h f -> edge_count h = edge_count g.
Proof.
  intro Hgraph; unfold edge_count; rewrite (nodes_agree _ _ _ Hgraph).
  induction (Graph.nodes g) as [|n ns IH]; cbn; [reflexivity|].
  rewrite (out_agree _ _ _ Hgraph), length_map, IH; reflexivity.
Qed.

Lemma prepare_fuel_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f ->
  fuel (prepare EN h) = fuel (prepare EN g).
Proof.
  intro Hgraph; cbn [prepare fuel].
  rewrite (nodes_agree _ _ _ Hgraph), (edge_count_agree g h f Hgraph); reflexivity.
Qed.

Definition state {N E F} (f : E -> F) (st : DfsState.t N E) : DfsState.t N F :=
  DfsState.Make (DfsState.pre st) (DfsState.post st) (Map.map f (DfsState.parent st))
    (DfsState.pre_index st) (DfsState.post_index st) (DfsState.seen st)
    (DfsState.pre_clock st) (DfsState.post_clock st).

Definition stack {N E F} (f : E -> F) (xs : dfs_stack N E) : dfs_stack N F :=
  map (fun ve => (fst ve, map f (snd ve))) xs.

Definition work {N E F} (f : E -> F) (w : dfs_stack N E * DfsState.t N E) :=
  (stack f (fst w), state f (snd w)).

Definition result {N E F} (f : E -> F) (r : dfs_result N E) : dfs_result N F :=
  DfsResult (preorder r) (postorder r) (Map.map f (tree_edge r))
    (pre_num r) (post_num r) (visited r).

Lemma discover_agree {N E F} (EN : encoding N) (f : E -> F) n via st :
  state f (dfs_discover EN n via st) =
  dfs_discover EN n (option_map f via) (state f st).
Proof.
  destruct via; unfold state, dfs_discover; cbn; [rewrite map_set|]; reflexivity.
Qed.

Lemma step_agree {N E F} (EN : encoding N) (g : Graph.t N E) (h : Graph.t N F)
    (p : prepared EN g) (q : prepared EN h) f blocked w :
  (forall e, Graph.target h (f e) = Graph.target g e) ->
  (forall n, succ_edges q n = map f (succ_edges p n)) ->
  work f (dfs_step p blocked w) = dfs_step q blocked (work f w).
Proof.
  intros Htarget Hsucc; destruct w as [xs st]; destruct xs as [|[n es] xs].
  - reflexivity.
  - destruct es as [|e es].
    + reflexivity.
    + cbn [dfs_step work stack fst snd map state DfsState.seen]; rewrite Htarget.
      destruct (FinSet.mem EN (Graph.target g e) blocked ||
        FinSet.mem EN (Graph.target g e) (DfsState.seen st)); [reflexivity|].
      rewrite Hsucc; unfold work, stack, state, dfs_discover; cbn.
      rewrite map_set; reflexivity.
Qed.

Lemma run_agree {N E F} (EN : encoding N) (g : Graph.t N E) (h : Graph.t N F)
    (p : prepared EN g) (q : prepared EN h) f blocked k w :
  (forall e, Graph.target h (f e) = Graph.target g e) ->
  (forall n, succ_edges q n = map f (succ_edges p n)) ->
  work f (dfs_run p blocked k w) = dfs_run q blocked k (work f w).
Proof.
  intros Htarget Hsucc; rewrite !dfs_run_agrees.
  induction k using Pos.peano_ind.
  - apply step_agree; assumption.
  - rewrite !Pos.iter_succ, (step_agree EN g h p q f blocked _ Htarget Hsucc).
    rewrite IHk; reflexivity.
Qed.

Lemma root_agree {N E F} (EN : encoding N) (g : Graph.t N E) (h : Graph.t N F)
    (p : prepared EN g) (q : prepared EN h) f blocked st n :
  (forall e, Graph.target h (f e) = Graph.target g e) ->
  (forall v, succ_edges q v = map f (succ_edges p v)) -> fuel q = fuel p ->
  state f (dfs_root p blocked st n) = dfs_root q blocked (state f st) n.
Proof.
  intros Htarget Hsucc Hfuel; unfold dfs_root; cbn [state DfsState.seen].
  destruct (FinSet.mem EN n blocked || FinSet.mem EN n (DfsState.seen st)); [reflexivity|].
  rewrite Hfuel.
  pose proof (run_agree EN g h p q f blocked (fuel p)
    ([(n, succ_edges p n)], dfs_discover EN n None st) Htarget Hsucc) as Hrun.
  apply (f_equal snd) in Hrun; unfold work, stack in Hrun; cbn [fst snd map] in Hrun.
  rewrite discover_agree, <- Hsucc in Hrun; exact Hrun.
Qed.

Lemma dfs_agree {N E F} (EN : encoding N) (g : Graph.t N E) (h : Graph.t N F)
    (p : prepared EN g) (q : prepared EN h) f blocked roots :
  (forall e, Graph.target h (f e) = Graph.target g e) ->
  (forall n, succ_edges q n = map f (succ_edges p n)) -> fuel q = fuel p ->
  result f (dfs p blocked roots) = dfs q blocked roots.
Proof.
  intros Htarget Hsucc Hfuel; unfold dfs.
  assert (Hfold : forall ns st,
    state f (fold_left (dfs_root p blocked) ns st) =
    fold_left (dfs_root q blocked) ns (state f st)).
  { intro ns; induction ns as [|n ns IH]; intro st; cbn [fold_left]; [reflexivity|].
    rewrite IH, (root_agree EN g h p q f blocked st n Htarget Hsucc Hfuel); reflexivity. }
  pose proof (Hfold roots dfs_initial) as Hagree.
  change (state f dfs_initial) with (@dfs_initial N F) in Hagree.
  rewrite <- Hagree; reflexivity.
Qed.

Lemma prepared_dfs_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f blocked roots : graph_laws g h f ->
  result f (dfs (prepare EN g) blocked roots) = dfs (prepare EN h) blocked roots.
Proof.
  intro Hgraph; apply dfs_agree.
  - apply (target_agree _ _ _ Hgraph).
  - apply prepare_succ_agree; exact Hgraph.
  - apply prepare_fuel_agree with (f := f); exact Hgraph.
Qed.

Lemma predecessor_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f r semis acc e :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  semi_predecessor EN h (result f r) semis acc (f e) =
  semi_predecessor EN g r semis acc e.
Proof.
  intro Hsource; unfold semi_predecessor; destruct acc; rewrite Hsource; reflexivity.
Qed.

Lemma settle_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) (p : prepared EN g) (q : prepared EN h) f r st n :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  (forall v, pred_edges q v = map f (pred_edges p v)) ->
  semi_settle q (result f r) st n = semi_settle p r st n.
Proof.
  intros Hsource Hpred; unfold semi_settle; cbn [result tree_edge].
  rewrite Map.get_map; destruct (Map.get EN n (tree_edge r)) as [e|]; [|reflexivity].
  cbn [option_map]; rewrite Hsource, Hpred.
  assert (Hfold : forall es acc,
    fold_left (semi_predecessor EN h (result f r) (SemiState.result st)) (map f es) acc =
    fold_left (semi_predecessor EN g r (SemiState.result st)) es acc).
  { intro es; induction es as [|a es IH]; intro acc; cbn [map fold_left]; [reflexivity|].
    rewrite (predecessor_agree EN g h f r (SemiState.result st) acc a Hsource); apply IH. }
  rewrite Hfold; reflexivity.
Qed.

Lemma semis_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) (p : prepared EN g) (q : prepared EN h) f r :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  (forall v, pred_edges q v = map f (pred_edges p v)) ->
  semi_compute q (result f r) = semi_compute p r.
Proof.
  intros Hsource Hpred; unfold semi_compute; cbn [result preorder].
  assert (Hfold : forall ns st,
    fold_left (semi_settle q (result f r)) ns st = fold_left (semi_settle p r) ns st).
  { intro ns; induction ns as [|n ns IH]; intro st; cbn [fold_left]; [reflexivity|].
    rewrite (settle_agree EN g h p q f r st n Hsource Hpred); apply IH. }
  apply Hfold.
Qed.

Lemma reverse_step_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f r semis buckets st n :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  lt_reverse_step EN h (result f r) semis buckets st n =
  lt_reverse_step EN g r semis buckets st n.
Proof.
  intro Hsource; unfold lt_reverse_step; cbn [result tree_edge].
  rewrite Map.get_map; destruct (Map.get EN n (tree_edge r)) as [e|]; [|reflexivity].
  cbn [option_map]; rewrite Hsource; reflexivity.
Qed.

Lemma lt_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f r semis :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  lt_compute EN h (result f r) semis = lt_compute EN g r semis.
Proof.
  intro Hsource; unfold lt_compute, lt_provisional; cbn [result preorder].
  assert (Hfold : forall ns st buckets,
    fold_left (lt_reverse_step EN h (result f r) semis buckets) ns st =
    fold_left (lt_reverse_step EN g r semis buckets) ns st).
  { intro ns; induction ns as [|n ns IH]; intros st buckets; cbn [fold_left]; [reflexivity|].
    rewrite (reverse_step_agree EN g h f r semis buckets st n Hsource); apply IH. }
  rewrite Hfold; reflexivity.
Qed.

Definition virtual_edge {N E F} (f : E -> F) (e : E + N) : F + N :=
  match e with
  | inl a => inl (f a)
  | inr n => inr n
  end.

Lemma virtual_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f ->
  graph_laws (virtual_graph EN g) (virtual_graph EN h) (virtual_edge f).
Proof.
  intro Hgraph; constructor.
  - reflexivity.
  - cbn; rewrite (nodes_agree _ _ _ Hgraph); reflexivity.
  - intros [n|[]]; cbn.
    + rewrite (out_agree _ _ _ Hgraph), !map_map; apply map_ext; intro a; reflexivity.
    + unfold virtual_entries; rewrite (entries_agree _ _ _ Hgraph), map_map.
      apply map_ext; intro n; reflexivity.
  - intros [e|n]; cbn; [rewrite (source_agree _ _ _ Hgraph)|]; reflexivity.
  - intros [e|n]; cbn; [rewrite (target_agree _ _ _ Hgraph)|]; reflexivity.
Qed.

Lemma parents_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f ->
  simple_lt_idom (prepare EN h) = simple_lt_idom (prepare EN g).
Proof.
  intro Hgraph.
  pose proof (virtual_agree EN g h f Hgraph) as Hvirtual.
  pose proof (prepared_dfs_agree (virtual_encoding EN) _ _ (virtual_edge f)
    FinSet.empty [inr tt] Hvirtual) as Hdfs.
  unfold simple_lt_idom, virtual_prepared; rewrite <- Hdfs.
  rewrite (semis_agree (virtual_encoding EN) _ _ _ _ (virtual_edge f) _
    (source_agree _ _ _ Hvirtual) (prepare_pred_agree _ _ _ _ Hvirtual)).
  rewrite (lt_agree (virtual_encoding EN) _ _ (virtual_edge f) _ _
    (source_agree _ _ _ Hvirtual)); reflexivity.
Qed.

Lemma tree_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f : graph_laws g h f ->
  dominator_tree (prepare EN h) = dominator_tree (prepare EN g).
Proof.
  intro Hgraph; unfold dominator_tree, dominator_tree_with.
  rewrite (parents_agree EN g h f Hgraph).
  assert (Hforest : forall m, dom_forest (prepare EN h) m = dom_forest (prepare EN g) m).
  { intro m; unfold dom_forest; rewrite (entries_agree _ _ _ Hgraph).
    rewrite <- (prepared_dfs_agree EN g h f FinSet.empty (Graph.entries g) Hgraph).
    reflexivity. }
  unfold dom_tree_of, dom_search; rewrite Hforest; reflexivity.
Qed.

Lemma candidates_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) (p : prepared EN g) (q : prepared EN h) f t live n :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  (forall v, pred_edges q v = map f (pred_edges p v)) ->
  edge_dom_candidates q t live n = map f (edge_dom_candidates p t live n).
Proof.
  intros Hsource Hpred; unfold edge_dom_candidates; rewrite Hpred, <- map_filter.
  f_equal; apply filter_ext; intro e; rewrite Hsource; reflexivity.
Qed.

Lemma choice_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) (p : prepared EN g) (q : prepared EN h) f t entries live n :
  (forall a, Graph.source h (f a) = Graph.source g a) ->
  (forall v, pred_edges q v = map f (pred_edges p v)) ->
  edge_dom_choice q t entries live n = option_map f (edge_dom_choice p t entries live n).
Proof.
  intros Hsource Hpred; unfold edge_dom_choice.
  destruct (FinSet.mem EN n entries); [reflexivity|].
  rewrite (candidates_agree EN g h p q f t live n Hsource Hpred).
  destruct (edge_dom_candidates p t live n) as [|e [|a es]]; reflexivity.
Qed.

Lemma index_agree {N E F} (EN : encoding N) (g : Graph.t N E)
    (h : Graph.t N F) f t : graph_laws g h f ->
  edge_dom_index (prepare EN h) t = Map.map f (edge_dom_index (prepare EN g) t).
Proof.
  intro Hgraph; unfold edge_dom_index.
  rewrite (entries_agree _ _ _ Hgraph), (nodes_agree _ _ _ Hgraph).
  rewrite <- (prepared_dfs_agree EN g h f FinSet.empty (Graph.entries g) Hgraph).
  cbn [result visited].
  set (entries := FinSet.of_list EN (Graph.entries g)).
  set (live := visited (dfs (prepare EN g) FinSet.empty (Graph.entries g))).
  assert (Hfold : forall ns ix,
    fold_left (fun m n => match edge_dom_choice (prepare EN h) t entries live n with
      | Some e => Map.set EN n e m
      | None => m
      end) ns (Map.map f ix) =
    Map.map f (fold_left (fun m n => match edge_dom_choice (prepare EN g) t entries live n with
      | Some e => Map.set EN n e m
      | None => m
      end) ns ix)).
  { intro ns; induction ns as [|n ns IH]; intro ix; cbn [fold_left]; [reflexivity|].
    rewrite (choice_agree EN g h _ _ f t entries live n
      (source_agree _ _ _ Hgraph) (prepare_pred_agree EN g h f Hgraph)).
    destruct (edge_dom_choice (prepare EN g) t entries live n); cbn [option_map].
    - rewrite <- map_set; apply IH.
    - apply IH. }
  apply (Hfold _ Map.empty).
Qed.

Definition edge_work {N E F} (f : E -> F) (w : option N * list E) :=
  (fst w, map f (snd w)).

Lemma edge_step_agree {N E F} (EN : encoding N) (f : E -> F) t ix w :
  edge_work f (edge_dom_step EN t ix w) =
  edge_dom_step EN t (Map.map f ix) (edge_work f w).
Proof.
  destruct w as [[n|] es]; unfold edge_work, edge_dom_step; cbn.
  - rewrite Map.get_map; destruct (Map.get EN n ix); reflexivity.
  - reflexivity.
Qed.

Lemma edges_agree {N E F} (EN : encoding N) (g : Graph.t N E) (h : Graph.t N F)
    (p : prepared EN g) (q : prepared EN h) (f : E -> F) t ix n : fuel q = fuel p ->
  dominating_edges q t (Map.map f ix) n = map f (dominating_edges p t ix n).
Proof.
  intro Hfuel; unfold dominating_edges; rewrite Hfuel, !edge_dom_run_agrees.
  assert (Hiter : forall k w,
    edge_work f (Pos.iter (edge_dom_step EN t ix) w k) =
    Pos.iter (edge_dom_step EN t (Map.map f ix)) (edge_work f w) k).
  { intro k; induction k using Pos.peano_ind; intro w.
    - apply edge_step_agree.
    - rewrite !Pos.iter_succ, edge_step_agree, IHk; reflexivity. }
  pose proof (f_equal snd (Hiter (fuel p) (Some n, []))) as Hagree.
  symmetry; exact Hagree.
Qed.

Lemma path_lift {N E F} (g : Graph.t N E) (h : Graph.t N F) f s es t :
  graph_laws g h f -> path h s es t ->
  exists lifted, path g s lifted t /\ map f lifted = es.
Proof.
  intros Hgraph Hpath; induction Hpath as [n|a es t Hedge Hpath IH].
  - exists []; split; [constructor|reflexivity].
  - destruct IH as [lifted [Hlifted Hmap]].
    rewrite (out_agree _ _ _ Hgraph) in Hedge.
    apply in_map_iff in Hedge; destruct Hedge as [e [Heq Hin]]; subst a.
    exists (e :: lifted); split.
    + rewrite (source_agree _ _ _ Hgraph) in Hin |- *.
      constructor; [exact Hin|].
      rewrite <- (target_agree _ _ _ Hgraph); exact Hlifted.
    + cbn; rewrite Hmap; reflexivity.
Qed.

Lemma edge_dominance_project {N E F} (g : Graph.t N E) (h : Graph.t N F) f e n :
  graph_laws g h f -> edge_dominates g e n -> edge_dominates h (f e) n.
Proof.
  intros Hgraph Hdom s es Hentry Hpath.
  destruct (path_lift g h f s es n Hgraph Hpath) as [lifted [Hlifted Hmap]].
  rewrite <- Hmap; apply in_map; apply Hdom with s.
  - rewrite <- (entries_agree _ _ _ Hgraph); exact Hentry.
  - exact Hlifted.
Qed.

End EdgeProjection.
Import EdgeProjection.

(** * Runs and unchanged bindings *)

Lemma exec_in_start {S O} (m : semantics S O) (P : S -> Prop) s tr t :
  exec_in m P s tr t -> P s.
Proof.
  intro Hrun; destruct Hrun; assumption.
Qed.

Lemma dominated_edge_source_reachable {N E} (g : Graph.t N E) e n :
  reachable g n -> edge_dominates g e n -> reachable g (Graph.source g e).
Proof.
  intros Hreach Hdom; apply reachable_iff_path in Hreach.
  destruct Hreach as [s [es [Hentry Hpath]]].
  destruct (edge_path_prefix g s es n e Hpath (Hdom s es Hentry Hpath))
    as [pre [Hpre _]].
  apply reachable_iff_path; exists s, pre; auto.
Qed.

(* Repeatedly shorten an entry prefix if it already contains e. This proves the
   suffix claim without deciding membership or equality of edges. *)
Lemma dominated_suffix_contains {N E} (g : Graph.t N E) e d n fs :
  reachable g (Graph.source g e) -> dominates g d (Graph.source g e) ->
  edge_dominates g e n -> path g d fs n -> In e fs.
Proof.
  intros Hreach Hhome Hdom Hsuffix.
  apply reachable_iff_path in Hreach; destruct Hreach as [s [es [Hentry Hpath]]].
  remember (length es) as k eqn:Hlength; revert es Hpath Hlength.
  induction k using lt_wf_ind; intros es Hpath Hlength.
  destruct (Hhome s es Hentry Hpath) as [Hstart|[a [Hin Htarget]]].
  - subst d.
    exact (Hdom s fs Hentry Hsuffix).
  - destruct (path_prefix_target g s es (Graph.source g e) a Hpath Hin)
      as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre.
    pose proof (Hdom s (pre ++ fs) Hentry (graph_path_app g _ _ _ _ _ Hpre Hsuffix)) as Hinfull.
    apply in_app_or in Hinfull; destruct Hinfull as [Hinpre|Hinfs]; [|exact Hinfs].
    assert (Hines : In e es) by (apply Hsub; exact Hinpre).
    destruct (edge_path_prefix g s es (Graph.source g e) e Hpath Hines)
      as [short [Hshort Hsmaller]].
    eapply (H (length short)); [lia|exact Hshort|reflexivity].
Qed.

Lemma edge_source_not_dominated {N E} (g : Graph.t N E) e :
  reachable g (Graph.source g e) -> ~ edge_dominates g e (Graph.source g e).
Proof.
  intros Hreach Hdom.
  pose proof (dominated_suffix_contains g e (Graph.source g e) (Graph.source g e) []
    Hreach (dominates_refl g _) Hdom (path_nil _)) as Hfalse.
  contradiction.
Qed.

Lemma exec_in_edge_free {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    e s tr t : graph_view_laws m gv -> reachable_state m s ->
  exec_in m (fun u => point gv u <> Graph.source (cfg gv) e) s tr t ->
  exists es, path (cfg gv) (point gv s) es (point gv t) /\ ~ In e es.
Proof.
  intros Hview Hreach Hrun; revert Hreach.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intro Hreach.
  - exists []; split; [constructor|intro Hin; contradiction].
  - destruct (IH (reachable_state_step m s l s' Hreach Hstep)) as [es [Hpath Hfree]].
    destruct (edge_covers Hview s l s' Hreach Hstep) as [Hstay|[a Htaken]].
    + exists es; split; [|exact Hfree].
      rewrite <- (stays_point Hview s l s' Hreach Hstep Hstay); exact Hpath.
    + destruct (view_taken_edge m gv s l s' a Hview Hreach Hstep Htaken)
        as [_ [Hsource Htarget]].
      exists (a :: es); split.
      * rewrite <- Hsource; constructor.
        -- rewrite Hsource; exact (proj1 (taken_edge Hview s l s' a Hreach Hstep Htaken)).
        -- rewrite Htarget; exact Hpath.
      * intros [Heq|Hin]; [subst a; apply Haway; symmetry; exact Hsource|exact (Hfree Hin)].
Qed.

Lemma exec_last_point {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    d s tr t : graph_view_laws m gv -> In d (Graph.nodes (cfg gv)) ->
  reachable_state m s -> exec m s tr t ->
  exec_in m (fun u => point gv u <> d) s tr t \/ point gv t = d \/
  exists u l v tail, reachable_state m u /\ point gv u = d /\ step m u l v /\
    exec_in m (fun w => point gv w <> d) v tail t.
Proof.
  intros Hview Hd Hreach Hrun; revert Hreach.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hreach.
  - destruct (listed_nodes_eq _ (nodes_nodup (cfg_wf Hview)) (point gv s) d
      (view_point_in_nodes m gv s Hview Hreach) Hd) as [Heq|Hneq].
    + right; left; exact Heq.
    + left; constructor; exact Hneq.
  - destruct (IH (reachable_state_step m s l s' Hreach Hstep)) as [Haway|Hlast].
    + destruct (listed_nodes_eq _ (nodes_nodup (cfg_wf Hview)) (point gv s) d
        (view_point_in_nodes m gv s Hview Hreach) Hd) as [Heq|Hneq].
      * right; right; exists s, l, s', tr; repeat split; assumption.
      * left; econstructor; eassumption.
    + right; exact Hlast.
Qed.

Lemma exec_in_away_home {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    e d s tr t : graph_view_laws m gv ->
  reachable (cfg gv) (Graph.source (cfg gv) e) ->
  dominates (cfg gv) d (Graph.source (cfg gv) e) ->
  edge_dominates (cfg gv) e (point gv t) -> reachable_state m s ->
  exec_in m (fun u => point gv u <> Graph.source (cfg gv) e) s tr t ->
  exec_in m (fun u => point gv u <> d) s tr t.
Proof.
  intros Hview Hsource Hhome Hdom Hreach Hrun; revert Hreach Hdom.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intros Hreach Hdom.
  - constructor; intro Heq.
    pose proof (dominated_suffix_contains (cfg gv) e d (point gv s) [] Hsource Hhome Hdom)
      as Hcontains.
    rewrite Heq in Hcontains; specialize (Hcontains (path_nil d)); contradiction.
  - assert (Hcurrent : point gv s <> d).
    { intro Heq.
      destruct (exec_in_edge_free m gv e s (l ++ tr) t Hview Hreach
        (exec_in_step s l s' tr t Haway Hstep Hrun)) as [es [Hpath Hfree]].
      rewrite Heq in Hpath.
      apply Hfree; eapply dominated_suffix_contains; eassumption. }
    econstructor; [exact Hcurrent|exact Hstep|].
    apply IH; [eapply reachable_state_step; eassumption|exact Hdom].
Qed.

(* A last visit of the source suffices: the edge taken at its departure must be e.
   The remaining states avoid that source, so no later step can take e. *)
Lemma last_dominating_edge {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    s e : graph_view_laws m gv -> reachable_state m s ->
  edge_dominates (cfg gv) e (point gv s) ->
  exists u l v tail, reachable_state m u /\ step m u l v /\ taken gv u l v e /\
    exec_in m (fun w => point gv w <> Graph.source (cfg gv) e) v tail s.
Proof.
  intros Hview Hreach Hdom.
  assert (Hsource : reachable (cfg gv) (Graph.source (cfg gv) e)).
  { eapply dominated_edge_source_reachable; [eapply view_point_reachable; eassumption|exact Hdom]. }
  destruct Hreach as [s0 [tr [Hinitial Hrun]]].
  assert (Hstart : reachable_state m s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  destruct (exec_last_point m gv (Graph.source (cfg gv) e) s0 tr s Hview
    (reachable_in_nodes _ _ (cfg_wf Hview) Hsource) Hstart Hrun)
    as [Haway|[Hend|[u [l [v [tail [Hu [Hpoint [Hstep Htail]]]]]]]]].
  - destruct (exec_in_edge_free m gv e s0 tr s Hview Hstart Haway) as [es [Hpath Hfree]].
    exfalso; apply Hfree; apply Hdom with (point gv s0).
    + apply (entry_points Hview); exact Hinitial.
    + exact Hpath.
  - exfalso; apply (edge_source_not_dominated (cfg gv) e Hsource).
    rewrite <- Hend; exact Hdom.
  - assert (Hv : reachable_state m v) by (eapply reachable_state_step; eassumption).
    pose proof (exec_in_start m _ v tail s Htail) as Hvaway.
    destruct (edge_covers Hview u l v Hu Hstep) as [Hstay|[a Htaken]].
    + exfalso; apply Hvaway; rewrite (stays_point Hview u l v Hu Hstep Hstay); exact Hpoint.
    + destruct (view_taken_edge m gv u l v a Hview Hu Hstep Htaken)
        as [_ [Hasource Hatarget]].
      destruct (exec_in_edge_free m gv e v tail s Hview Hv Htail) as [es [Hpath Hfree]].
      assert (Hfull : path (cfg gv) (Graph.source (cfg gv) e) (a :: es) (point gv s)).
      { rewrite <- Hpoint, <- Hasource; constructor.
        - rewrite Hasource; exact (proj1 (taken_edge Hview u l v a Hu Hstep Htaken)).
        - rewrite Hatarget; exact Hpath. }
      destruct (dominated_suffix_contains (cfg gv) e (Graph.source (cfg gv) e)
        (point gv s) (a :: es) Hsource (dominates_refl _ _) Hdom Hfull) as [Heq|Hin].
      * subst a; exists u, l, v, tail; repeat split; assumption.
      * exfalso; exact (Hfree Hin).
Qed.

Lemma exec_frame_away {S O N E V K C} (m : semantics S O)
    (sv : ssa_view S O N E V K C) x s tr t :
  ssa_view_laws m sv -> strict_ssa_laws m sv -> reachable_state m s ->
  exec_in m (fun u => point (base sv) u <> home sv x) s tr t -> val sv t x = val sv s x.
Proof.
  intros Hview Hstrict Hreach Hrun; revert Hreach.
  induction Hrun as [s Haway|s l s' tr t Haway Hstep Hrun IH]; intro Hreach.
  - reflexivity.
  - rewrite (IH (reachable_state_step m s l s' Hreach Hstep)).
    destruct (edge_covers (base_laws Hview) s l s' Hreach Hstep) as [Hstay|[a Htaken]].
    + eapply frame_in_stay; eassumption.
    + eapply frame_on_edge; try eassumption.
      pose proof (exec_in_start m _ s' tr t Hrun) as Htarget; congruence.
Qed.

Lemma dominated_value_preserved {S O N E V K C} (m : semantics S O)
    (sv : ssa_view S O N E V K C) e x u l v tail s :
  ssa_view_laws m sv -> strict_ssa_laws m sv -> reachable_state m u ->
  step m u l v -> taken (base sv) u l v e ->
  exec_in m (fun w => point (base sv) w <> Graph.source (cfg (base sv)) e) v tail s ->
  edge_dominates (cfg (base sv)) e (point (base sv) s) ->
  dominates (cfg (base sv)) (home sv x) (Graph.source (cfg (base sv)) e) ->
  val sv s x = val sv u x.
Proof.
  intros Hview Hstrict Hu Hstep Htaken Htail Hdom Hhome.
  assert (Hv : reachable_state m v) by (eapply reachable_state_step; eassumption).
  destruct (view_taken_edge m (base sv) u l v e (base_laws Hview) Hu Hstep Htaken)
    as [_ [Hsource _]].
  assert (Hreachable : reachable (cfg (base sv)) (Graph.source (cfg (base sv)) e)).
  { rewrite Hsource; eapply view_point_reachable; [exact (base_laws Hview)|exact Hu]. }
  pose proof (exec_in_away_home m (base sv) e (home sv x) v tail s
    (base_laws Hview) Hreachable Hhome Hdom Hv Htail) as Haway.
  rewrite (exec_frame_away m sv x v tail s Hview Hstrict Hv Haway).
  eapply frame_on_edge; try eassumption.
  pose proof (exec_in_start m _ v tail s Haway); congruence.
Qed.

Lemma operand_values_preserved {S O N E V K C} (sv : ssa_view S O N E V K C)
    s t args cs : Forall2 (fun y d => val sv s y = Some d) args cs ->
  (forall y, In y args -> val sv t y = val sv s y) ->
  Forall2 (fun y d => val sv t y = Some d) args cs.
Proof.
  intro Hargs; induction Hargs as [|y d args cs Hvalue Hargs IH]; intro Hpreserve.
  - constructor.
  - constructor.
    + rewrite Hpreserve; [exact Hvalue|left; reflexivity].
    + apply IH; intros z Hin; apply Hpreserve; right; exact Hin.
Qed.

(** A dominating edge's guards and operation equations hold at every reachable dominated read. *)
Theorem dominated_guard_holds {S O N E V K C} (m : semantics S O)
    (sv : ssa_view S O N E V K C) :
  ssa_view_laws m sv -> strict_ssa_laws m sv ->
  forall s e, reachable_state m s ->
    edge_dominates (cfg (base sv)) e (point (base sv) s) ->
    Forall (cond_holds sv s) (edge_guard sv e) /\ guard_ops_consistent sv s e.
Proof.
  intros Hview Hstrict s e Hreach Hdom.
  destruct (last_dominating_edge m (base sv) s e (base_laws Hview) Hreach Hdom)
    as [u [l [v [tail [Hu [Hstep [Htaken Htail]]]]]]].
  pose proof (proj1 (view_taken_edge m (base sv) u l v e
    (base_laws Hview) Hu Hstep Htaken)) as Hedge.
  assert (Hpreserve : forall x,
    dominates (cfg (base sv)) (home sv x) (Graph.source (cfg (base sv)) e) ->
    val sv s x = val sv u x).
  { intros x Hhome; eapply dominated_value_preserved; eassumption. }
  split.
  - apply Forall_forall; intros cd Hcd.
    pose proof (guards_ok Hview u l v e Hu Hstep Htaken) as Hguards.
    apply Forall_forall with (x := cd) in Hguards; [|exact Hcd].
    unfold cond_holds in *; rewrite (Hpreserve (subject cd)
      (guard_home Hstrict e cd Hedge Hcd)); exact Hguards.
  - intros cd o args Hcd Hdef.
    destruct (guard_op_defined Hview u l v e Hu Hstep Htaken cd o args Hcd Hdef)
      as [cs [c [Hargs [Hvalue Heval]]]].
    exists cs, c; split.
    + eapply operand_values_preserved; [exact Hargs|].
      intros y Hin; apply Hpreserve.
      eapply dominates_trans; [eapply op_args_dominate; [exact Hstrict|exact Hdef|]|].
      * exact Hin.
      * apply (guard_home Hstrict e cd Hedge Hcd).
    + split.
      * rewrite (Hpreserve (subject cd) (guard_home Hstrict e cd Hedge Hcd)); exact Hvalue.
      * exact Heval.
Qed.

(** * Sound queries with repeated client edges *)

Fixpoint edge_occurrences {E} (es : list E) (i : nat) : list (E * nat) :=
  match es with
  | [] => []
  | e :: rest => (e, i) :: edge_occurrences rest (S i)
  end.

Lemma edge_occurrences_project {E} (es : list E) :
  forall i, map fst (edge_occurrences es i) = es.
Proof.
  induction es as [|e es IH]; intro i; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma edge_occurrences_positions {E} (es : list E) :
  forall i, map snd (edge_occurrences es i) = seq i (length es).
Proof.
  induction es as [|e es IH]; intro i; cbn; [reflexivity|rewrite IH; reflexivity].
Qed.

Lemma edge_occurrences_nodup {E} (es : list E) i : NoDup (edge_occurrences es i).
Proof.
  apply (NoDup_map_inv snd); rewrite edge_occurrences_positions; apply seq_NoDup.
Qed.

Definition occurrence_graph {N E} (g : Graph.t N E) : Graph.t N (E * nat) :=
  {| Graph.entries := Graph.entries g;
     Graph.nodes := Graph.nodes g;
     Graph.out := fun n => edge_occurrences (Graph.out g n) 0;
     Graph.source := fun ei => Graph.source g (fst ei);
     Graph.target := fun ei => Graph.target g (fst ei) |}.

Lemma occurrence_projection {N E} (g : Graph.t N E) :
  graph_laws (occurrence_graph g) g fst.
Proof.
  constructor; try reflexivity.
  intro n; symmetry; apply edge_occurrences_project.
Qed.

Lemma occurrence_graph_wf {N E} (g : Graph.t N E) :
  graph_wf g -> graph_wf (occurrence_graph g).
Proof.
  intro Hwf; constructor; cbn.
  - apply (nodes_nodup Hwf).
  - apply (entries_in Hwf).
  - intros n ei Hin; apply (out_source Hwf n (fst ei)).
    rewrite <- (edge_occurrences_project (Graph.out g n) 0); apply in_map; exact Hin.
  - intros n ei Hn Hin; apply (out_target_in Hwf n (fst ei) Hn).
    rewrite <- (edge_occurrences_project (Graph.out g n) 0); apply in_map; exact Hin.
Qed.

Lemma dominating_edges_graph_wf {N E} (EN : encoding N) (g : Graph.t N E) b e :
  graph_wf g ->
  In e (dominating_edges (prepare EN g) (dominator_tree (prepare EN g))
    (edge_dom_index (prepare EN g) (dominator_tree (prepare EN g))) b) ->
  edge_dominates g e b.
Proof.
  intros Hwf Hin.
  pose proof (occurrence_projection g) as Hprojection.
  assert (Hready : ready EN (occurrence_graph g) (prepare EN (occurrence_graph g))).
  { apply prepare_ready; [apply occurrence_graph_wf; exact Hwf|].
    intro n; apply edge_occurrences_nodup. }
  rewrite (tree_agree EN (occurrence_graph g) g fst Hprojection) in Hin.
  rewrite (index_agree EN (occurrence_graph g) g fst _ Hprojection) in Hin.
  rewrite (edges_agree EN (occurrence_graph g) g _ _ fst _ _ b
    (prepare_fuel_agree EN (occurrence_graph g) g fst Hprojection)) in Hin.
  apply in_map_iff in Hin; destruct Hin as [ei [Heq Hin]].
  rewrite <- Heq; apply (edge_dominance_project (occurrence_graph g) g fst ei b Hprojection).
  eapply dominating_edges_sound; eassumption.
Qed.

(** * Prepared dominance contexts and refinement *)

(** A context stores a graph, its prepared indexes, its tree and its edge-dominance index. *)
Record dom_context (N E : Type) : Type := DomContext {
  dc_graph : Graph.t N E;
  dc_encoding : encoding N;
  dc_prepared : prepared dc_encoding dc_graph;
  dc_tree : dom_tree N;
  dc_index : Map.t N E
}.

Arguments DomContext {N E}.
Arguments dc_graph {N E}.
Arguments dc_encoding {N E}.
Arguments dc_prepared {N E}.
Arguments dc_tree {N E}.
Arguments dc_index {N E}.

(** Build the graph indexes and dominance data once for subsequent reads. *)
Definition make_dom_context {N E} (EN : encoding N) (g : Graph.t N E) : dom_context N E :=
  let p := prepare EN g in
  let t := dominator_tree p in
  DomContext g EN p t (edge_dom_index p t).

(** Collect the indexed dominating edges in one walk of the dominator chain. *)
Definition dominating_edges_in {N E} (ctx : dom_context N E) (b : N) : list E :=
  dominating_edges (dc_prepared ctx) (dc_tree ctx) (dc_index ctx) b.

(** Refine the value's own fact by the guards of every dominating edge at the read. *)
Definition refined_fact {S O N E V K C A} (EV : encoding V) (ctx : dom_context N E)
    (pr : sparse_problem S O N E V K C A) (s : sparse_unknown N E V -> lift_bot A)
    (b : N) (z : V) : lift_bot A :=
  fold_left (fun a e => refine_fact EV pr s e z a) (dominating_edges_in ctx b) (s (UVal z)).

(** The dominating-edge query is sound for a well-formed graph with distinct outgoing edges. *)
Theorem dominating_edges_in_sound {N E} (EN : encoding N) (g : Graph.t N E) (b : N) (e : E) :
  graph_wf g -> (forall v, NoDup (Graph.out g v)) ->
  In e (dominating_edges_in (make_dom_context EN g) b) -> edge_dominates g e b.
Proof.
  intros Hwf _ Hin; apply (dominating_edges_graph_wf EN g b e Hwf); exact Hin.
Qed.

Lemma refine_dominating_edges_sound {S O N E V K C A} (m : semantics S O)
    (EV : encoding V) (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) s z c :
  ssa_view_laws m (view pr) -> strict_ssa_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  reachable_state m s ->
  (forall x d, val (view pr) s x = Some d ->
    gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  val (view pr) s z = Some c ->
  forall es a, Forall (fun e => edge_dominates (cfg (base (view pr))) e
    (point (base (view pr)) s)) es ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) a c ->
  gamma (lift_bot_gamma (fact_conc (domain pr)))
    (fold_left (fun a e => refine_fact EV pr sigma e z a) es a) c.
Proof.
  intros Hview Hstrict Hdomain Hreach Hfacts Hvalue es; induction es as [|e es IH];
    intros a Hedges Hfact; [exact Hfact|].
  inversion Hedges as [|? ? Hdom Hrest]; subst.
  cbn [fold_left]; apply IH; [exact Hrest|].
  destruct (dominated_guard_holds m (view pr) Hview Hstrict s e Hreach Hdom)
    as [Hguards Hops].
  eapply refine_fact_sound; eassumption.
Qed.

(** On-demand refinement retains the current value, even when outgoing lists contain duplicates. *)
Theorem refined_fact_sound {S O N E V K C A} (m : semantics S O) (EN : encoding N)
    (EV : encoding V) (ctx : dom_context N E) (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) :
  ctx = make_dom_context EN (cfg (base (view pr))) ->
  ssa_view_laws m (view pr) -> strict_ssa_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  forall s z c, reachable_state m s ->
    (forall x d, val (view pr) s x = Some d ->
      gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
    val (view pr) s z = Some c ->
    gamma (lift_bot_gamma (fact_conc (domain pr)))
      (refined_fact EV ctx pr sigma (point (base (view pr)) s) z) c.
Proof.
  intros Hctx Hview Hstrict Hdomain s z c Hreach Hfacts Hvalue; subst ctx.
  unfold refined_fact; eapply refine_dominating_edges_sound; try eassumption.
  - apply Forall_forall; intros e Hin.
    apply (dominating_edges_graph_wf EN (cfg (base (view pr))) _ e
      (cfg_wf (base_laws Hview))); exact Hin.
  - apply Hfacts; exact Hvalue.
Qed.
