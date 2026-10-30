(** * Legacy all-walk memory certificates

    External candidates are checked against every node on every relevant successor walk.
    For example, a cycle that revisits the proposed definition must check that definition again.
    Builds on: AnalysesMemoryWalk, GraphDfs, GraphPrepare and AnalysesMemoryBase. *)

From Stdlib Require Import List Bool ZArith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphIdf.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier
  AnalysesMemoryWalk AnalysesMemoryBase.
Import List.ListNotations.

(** A legacy definition is local to one function or denotes that function's entry memory. *)
Inductive mem_node (F N : Type) : Type :=
  | MDef (f : F) (n : N)
  | MLive (f : F).

Arguments MDef {F N}.
Arguments MLive {F N}.

(** Missing load candidates impose no legacy certificate obligation. *)
Record memory_ssa (F N : Type) : Type := MemorySSA {
  def_of_load : N -> option (mem_node F N)
}.

Arguments MemorySSA {F N}.
Arguments def_of_load {F N}.

(** Every visited node is included, starting before the first edge and ending at the load. *)
Definition legacy_nodes {N E} (g : Graph.t N E) (start : N) (es : list E) : list N :=
  start :: map (Graph.target g) es.

(** Disjoint footprint lists have no common byte of the same historical allocation site. *)
Definition legacy_disjoint {T} (writes reads : list (footprint T)) : Prop :=
  forall t o, covered writes t o 1 -> covered reads t o 1 -> False.

(** The exact half-open overlap test treats empty and reversed intervals as empty. *)
Definition legacy_disjoint_b {T} (ET : encoding T) (writes reads : list (footprint T)) : bool :=
  negb (existsb (fun f => existsb (fun h =>
    Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site h)) &&
    Z.ltb (fp_lo f) (fp_hi f) && Z.ltb (fp_lo h) (fp_hi h) &&
    Z.ltb (fp_lo f) (fp_hi h) && Z.ltb (fp_lo h) (fp_hi f)) reads) writes).

Lemma legacy_covered_byte {T} (fs : list (footprint T)) t o :
  covered fs t o 1 <-> exists f, In f fs /\ fp_site f = t /\ (fp_lo f <= o < fp_hi f)%Z.
Proof.
  split.
  - intro Hcovered; apply Hcovered; cbn; lia.
  - intros [f [Hin [Hsite Hbounds]]] k Hk; exists f; split; [exact Hin|split; [exact Hsite|]].
    cbn in Hk; assert (k = o) by lia; subst k; exact Hbounds.
Qed.

Lemma legacy_overlap_correct {T} (ET : encoding T) (f h : footprint T) :
  Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site h)) &&
    Z.ltb (fp_lo f) (fp_hi f) && Z.ltb (fp_lo h) (fp_hi h) &&
    Z.ltb (fp_lo f) (fp_hi h) && Z.ltb (fp_lo h) (fp_hi f) = true <->
  exists t o, fp_site f = t /\ fp_site h = t /\
    (fp_lo f <= o < fp_hi f)%Z /\ (fp_lo h <= o < fp_hi h)%Z.
Proof.
  repeat rewrite andb_true_iff; rewrite Pos.eqb_eq; repeat rewrite Z.ltb_lt; split.
  - intros [[[[Hsite Hf] Hh] Hfh] Hhf].
    apply (encode_injective ET) in Hsite.
    exists (fp_site f), (Z.max (fp_lo f) (fp_lo h)); repeat split; try congruence;
      pose proof (Z.le_max_l (fp_lo f) (fp_lo h));
      pose proof (Z.le_max_r (fp_lo f) (fp_lo h));
      destruct (Z.max_spec (fp_lo f) (fp_lo h)) as [[_ Heq]|[_ Heq]]; rewrite Heq; lia.
  - intros [t [o [Hf [Hh [Hfb Hhb]]]]]; subst t.
    repeat split; try lia; rewrite Hh; reflexivity.
Qed.

(** Exact Boolean disjointness reflects absence of a shared byte, even for malformed ranges. *)
Theorem legacy_disjoint_b_correct {T} (ET : encoding T) (writes reads : list (footprint T)) :
  legacy_disjoint_b ET writes reads = true <-> legacy_disjoint writes reads.
Proof.
  unfold legacy_disjoint_b; rewrite negb_true_iff; split.
  - intros Hnone t o Hwrite Hread.
    apply legacy_covered_byte in Hwrite as [f [Hf [Hft Hfb]]].
    apply legacy_covered_byte in Hread as [h [Hh [Hht Hhb]]].
    assert (Hsome : existsb (fun f => existsb (fun h =>
      Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site h)) &&
      Z.ltb (fp_lo f) (fp_hi f) && Z.ltb (fp_lo h) (fp_hi h) &&
      Z.ltb (fp_lo f) (fp_hi h) && Z.ltb (fp_lo h) (fp_hi f)) reads) writes = true).
    { apply existsb_exists; exists f; split; [exact Hf|].
      apply existsb_exists; exists h; split; [exact Hh|].
      apply legacy_overlap_correct; exists t, o; auto. }
    congruence.
  - intro Hdisjoint; destruct (existsb _ writes) eqn:Hsome; [|reflexivity].
    apply existsb_exists in Hsome as [f [Hf Hsome]].
    apply existsb_exists in Hsome as [h [Hh Hoverlap]].
    apply legacy_overlap_correct in Hoverlap as [t [o [Hft [Hht [Hfb Hhb]]]]].
    exfalso; apply (Hdisjoint t o); apply legacy_covered_byte; eexists; eauto.
Qed.

(** Candidates cover all successor walks, including the load and any revisited definition. *)
Definition legacy_pair_clear {F N E T} (f : F) (g : Graph.t N E)
    (writes reads : N -> list (footprint T)) (load : N) (d : mem_node F N) : Prop :=
  reachable g load /\
  match d with
  | MDef f' n => f' = f /\ reachable g n /\
      forall e es, In e (Graph.out g n) -> path g (Graph.target g e) es load ->
        forall k, In k (legacy_nodes g (Graph.target g e) es) ->
          legacy_disjoint (writes k) (reads load)
  | MLive f' => f' = f /\ forall entry es, In entry (Graph.entries g) ->
      path g entry es load -> forall k, In k (legacy_nodes g entry es) ->
        legacy_disjoint (writes k) (reads load)
  end.

(** * Node-adjacency normalization

    Node-local writes depend only on visited nodes. Distinct parallel edges therefore have the
    same reachability contribution, and the quotient keeps every possible successor node.
    The original edge identities remain in the all-walk specification. *)

Definition legacy_cfg_rows {N E} (EN : encoding N) (g : Graph.t N E) : Map.t N (list (N * N)) :=
  memory_result_index EN (fun n => map (fun target => (n, target))
    (memory_distinct EN (map (Graph.target g) (Graph.out g n)))) (Graph.nodes g).

Definition legacy_cfg {N E} (EN : encoding N) (g : Graph.t N E) : Graph.t N (N * N) :=
  {| Graph.entries := Graph.entries g;
     Graph.nodes := Graph.nodes g;
     Graph.out := index_edges EN (legacy_cfg_rows EN g);
     Graph.source := fst;
     Graph.target := snd |}.

Lemma legacy_cfg_row {N E} (EN : encoding N) (g : Graph.t N E) n :
  In n (Graph.nodes g) -> Graph.out (legacy_cfg EN g) n =
    map (fun target => (n, target)) (memory_distinct EN (map (Graph.target g) (Graph.out g n))).
Proof.
  intro Hin; unfold legacy_cfg; cbn [Graph.out]; unfold index_edges, legacy_cfg_rows.
  rewrite memory_result_index_at by exact Hin; reflexivity.
Qed.

Lemma legacy_cfg_row_outside {N E} (EN : encoding N) (g : Graph.t N E) n :
  ~ In n (Graph.nodes g) -> Graph.out (legacy_cfg EN g) n = [].
Proof.
  intro Houtside; unfold legacy_cfg; cbn [Graph.out]; unfold index_edges, legacy_cfg_rows.
  destruct (Map.get EN n (memory_result_index EN _ (Graph.nodes g))) as [row|] eqn:Hget;
    [|reflexivity].
  assert (Hsome : exists row, Map.get EN n (legacy_cfg_rows EN g) = Some row).
  { exists row; exact Hget. }
  unfold legacy_cfg_rows in Hsome; apply memory_result_index_domain in Hsome; contradiction.
Qed.

Lemma legacy_cfg_edge {N E} (EN : encoding N) (g : Graph.t N E) n edge :
  In edge (Graph.out (legacy_cfg EN g) n) <->
    In n (Graph.nodes g) /\ fst edge = n /\
    exists e, In e (Graph.out g n) /\ Graph.target g e = snd edge.
Proof.
  destruct (in_dec (dfs_eq_dec EN) n (Graph.nodes g)) as [Hin|Houtside].
  - rewrite legacy_cfg_row by exact Hin; rewrite in_map_iff; split.
    + intros [target [Heq Htarget]]; subst edge; cbn.
      apply memory_distinct_in in Htarget; apply in_map_iff in Htarget as [e [Heq Hedge]].
      split; [exact Hin|split; [reflexivity|exists e; auto]].
    + intros [_ [Hsource [e [Hedge Htarget]]]].
      exists (snd edge); split.
      * destruct edge as [source target]; cbn in *; subst source; reflexivity.
      * apply memory_distinct_in; apply in_map_iff; exists e; auto.
  - rewrite legacy_cfg_row_outside by exact Houtside; cbn; tauto.
Qed.

Lemma legacy_cfg_ready {N E} (EN : encoding N) (g : Graph.t N E) :
  graph_wf g -> ready EN (legacy_cfg EN g) (prepare EN (legacy_cfg EN g)).
Proof.
  intro Hwf; apply prepare_ready.
  - constructor.
    + exact (nodes_nodup Hwf).
    + exact (entries_in Hwf).
    + intros n edge Hedge; apply legacy_cfg_edge in Hedge; exact (proj1 (proj2 Hedge)).
    + intros n edge Hn Hedge; apply legacy_cfg_edge in Hedge.
      destruct Hedge as [_ [_ [e [Hedge Htarget]]]].
      change (In (snd edge) (Graph.nodes g)); rewrite <- Htarget.
      eapply out_target_in; eassumption.
  - intro n; destruct (in_dec (dfs_eq_dec EN) n (Graph.nodes g)) as [Hin|Houtside].
    + rewrite legacy_cfg_row by exact Hin.
      pose proof (memory_distinct_nodup EN (map (Graph.target g) (Graph.out g n))) as Hnodup.
      induction Hnodup as [|target targets Hnot Hnodup IH]; cbn; constructor; [|exact IH].
      intro Hpair; apply in_map_iff in Hpair as [other [Heq Hinother]].
      inversion Heq; subst other; contradiction.
    + rewrite legacy_cfg_row_outside by exact Houtside; constructor.
Qed.

Lemma legacy_path_lift {N E} (EN : encoding N) (g : Graph.t N E) u es v :
  graph_wf g -> path g u es v -> In u (Graph.nodes g) ->
  exists edges, path (legacy_cfg EN g) u edges v.
Proof.
  intros Hwf Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Hlisted.
  - exists []; constructor.
  - assert (Htarget : In (Graph.target g e) (Graph.nodes g)).
    { eapply out_target_in; eassumption. }
    destruct (IH Htarget) as [edges Hedges].
    exists ((Graph.source g e, Graph.target g e) :: edges).
    refine (@path_cons N (N * N) (legacy_cfg EN g)
      (Graph.source g e, Graph.target g e) edges v _ Hedges).
    apply legacy_cfg_edge; cbn; split; [exact Hlisted|split; [reflexivity|exists e; auto]].
Qed.

Lemma legacy_path_lower {N E} (EN : encoding N) (g : Graph.t N E) u es v :
  graph_wf g -> path (legacy_cfg EN g) u es v -> exists edges, path g u edges v.
Proof.
  intros Hwf Hpath; induction Hpath as [v|edge es v Hedge Hpath IH].
  - exists []; constructor.
  - apply legacy_cfg_edge in Hedge; destruct Hedge as [_ [_ [e [Hedge Htarget]]]].
    change (In e (Graph.out g (fst edge))) in Hedge.
    destruct IH as [edges Hedges].
    change (path g (snd edge) edges v) in Hedges; rewrite <- Htarget in Hedges.
    pose proof (out_source Hwf (fst edge) e Hedge) as Hsource.
    exists (e :: edges); change (path g (fst edge) (e :: edges) v); rewrite <- Hsource.
    constructor; [rewrite Hsource; exact Hedge|exact Hedges].
Qed.

Lemma legacy_cfg_reaches {N E} (EN : encoding N) (g : Graph.t N E) u v :
  graph_wf g -> In u (Graph.nodes g) ->
  (reaches (legacy_cfg EN g) u v <-> reaches g u v).
Proof.
  intros Hwf Hlisted; split; intros [es Hpath].
  - eapply legacy_path_lower; eassumption.
  - eapply legacy_path_lift; eassumption.
Qed.

Lemma legacy_cfg_reachable {N E} (EN : encoding N) (g : Graph.t N E) v :
  graph_wf g -> (reachable (legacy_cfg EN g) v <-> reachable g v).
Proof.
  intro Hwf; repeat rewrite reachable_iff_path; split; intros [root [es [Hentry Hpath]]].
  - destruct (legacy_path_lower EN g root es v Hwf Hpath) as [edges Hedges].
    exists root, edges; auto.
  - destruct (legacy_path_lift EN g root es v Hwf Hpath (entries_in Hwf root Hentry))
      as [edges Hedges].
    exists root, edges; auto.
Qed.

Lemma legacy_path_nodes_split {N E} (g : Graph.t N E) start es load k :
  path g start es load -> In k (legacy_nodes g start es) ->
  exists first rest, path g start first k /\ path g k rest load.
Proof.
  intro Hpath; induction Hpath as [load|e es load Hedge Hpath IH]; cbn [legacy_nodes map In].
  - intros [->|Hfalse]; [exists [], []; split; constructor|contradiction].
  - intros [Hhead|Hin].
    + subst k; exists [], (e :: es); split.
      * apply path_nil.
      * exact (path_cons e es load Hedge Hpath).
    + destruct (IH Hin) as [first [rest [Hfirst Hrest]]].
      exists (e :: first), rest; split; [constructor; assumption|exact Hrest].
Qed.

Lemma legacy_path_end_node {N E} (g : Graph.t N E) start es load :
  path g start es load -> In load (legacy_nodes g start es).
Proof.
  intro Hpath; induction Hpath as [load|e es load Hedge Hpath IH];
    cbn [legacy_nodes map In] in *; [left; reflexivity|right; exact IH].
Qed.

Lemma legacy_nodes_prefix {N E} (g : Graph.t N E) start first rest k :
  In k (legacy_nodes g start first) -> In k (legacy_nodes g start (first ++ rest)).
Proof.
  unfold legacy_nodes; rewrite map_app; intros [->|Hin]; [left; reflexivity|].
  right; apply in_or_app; left; exact Hin.
Qed.

Lemma legacy_path_nodes_listed {N E} (g : Graph.t N E) start es load :
  graph_wf g -> In start (Graph.nodes g) -> path g start es load ->
  forall k, In k (legacy_nodes g start es) -> In k (Graph.nodes g).
Proof.
  intros Hwf Hlisted Hpath; revert Hlisted.
  induction Hpath as [load|e es load Hedge Hpath IH]; intros Hlisted k Hin;
    cbn [legacy_nodes map In] in Hin.
  - destruct Hin as [->|Hfalse]; [exact Hlisted|contradiction].
  - destruct Hin as [Hhead|Hin]; [subst k; exact Hlisted|].
    apply IH; [eapply out_target_in; eassumption|exact Hin].
Qed.

(** * Forward/reverse slices *)

Definition legacy_reached {N E} {EN : encoding N} {g : Graph.t N E}
    (p : prepared EN g) (roots : list N) : FinSet.t N := visited (dfs p FinSet.empty roots).

Lemma legacy_reached_correct {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) roots v :
  ready EN g p -> incl roots (Graph.nodes g) ->
  (FinSet.mem EN v (legacy_reached p roots) = true <->
    exists root, In root roots /\ reaches g root v).
Proof.
  intros Hready Hroots; unfold legacy_reached.
  rewrite (proj1 (dfs_exact EN g p v roots FinSet.empty Hready Hroots)), dfs_empty_reachable.
  rewrite reachable_iff_path; split.
  - intros [root [es [Hroot Hpath]]]; exists root; split; [exact Hroot|exists es].
    apply (idf_path_entries_back g roots); exact Hpath.
  - intros [root [Hroot [es Hpath]]]; exists root, es; split; [exact Hroot|].
    apply idf_path_entries; exact Hpath.
Qed.

Definition legacy_slice {N E T} (EN : encoding N) (ET : encoding T) (g : Graph.t N E)
    (p : prepared EN g) (writes : N -> list (footprint T)) (read : list (footprint T))
    (roots : list N) (load : N) : bool :=
  let forward := legacy_reached p roots in
  let backward := legacy_reached (prepared_reverse p [load]) [load] in
  forallb (fun k => if FinSet.mem EN k forward && FinSet.mem EN k backward
    then legacy_disjoint_b ET (writes k) read else true) (Graph.nodes g).

Lemma legacy_slice_correct {N E T} (EN : encoding N) (ET : encoding T) (g : Graph.t N E)
    (p : prepared EN g) writes read roots load :
  ready EN g p -> incl roots (Graph.nodes g) -> In load (Graph.nodes g) ->
  (legacy_slice EN ET g p writes read roots load = true <->
    forall root es, In root roots -> path g root es load ->
      forall k, In k (legacy_nodes g root es) -> legacy_disjoint (writes k) read).
Proof.
  intros Hready Hroots Hload.
  assert (Hback : forall k, In k (Graph.nodes g) ->
    (FinSet.mem EN k (legacy_reached (prepared_reverse p [load]) [load]) = true <->
      reaches g k load)).
  { intros k Hk; rewrite (legacy_reached_correct EN (reverse_graph p [load])
      (prepared_reverse p [load]) [load] k).
    - split.
      + intros [root [[Heq|Hfalse] [es Hpath]]]; [subst root|contradiction].
        exists (rev es); apply (proj2 (reverse_path EN g p k load (rev es) [load]
          Hready Hk Hload)); rewrite rev_involutive; exact Hpath.
      + intros [es Hpath]; exists load; split; [left; reflexivity|exists (rev es)].
        apply (proj1 (reverse_path EN g p k load es [load] Hready Hk Hload)); exact Hpath.
    - apply reverse_graph_ready; [exact Hready|].
      intros n [->|Hfalse]; [exact Hload|contradiction].
    - intros n [->|Hfalse]; [exact Hload|contradiction]. }
  unfold legacy_slice; rewrite forallb_forall; split.
  - intros Hcheck root es Hroot Hpath k Hk.
    assert (Hlisted : In k (Graph.nodes g)).
    { eapply legacy_path_nodes_listed; [exact (proj1 Hready)|apply Hroots; exact Hroot|
        exact Hpath|exact Hk]. }
    destruct (legacy_path_nodes_split g root es load k Hpath Hk)
      as [first [rest [Hfirst Hrest]]].
    specialize (Hcheck k Hlisted).
    assert (Hforward : FinSet.mem EN k (legacy_reached p roots) = true).
    { apply (legacy_reached_correct EN g p roots k Hready Hroots).
      exists root; split; [exact Hroot|exists first; exact Hfirst]. }
    assert (Hbackward : FinSet.mem EN k (legacy_reached (prepared_reverse p [load]) [load]) = true).
    { apply (Hback k Hlisted); exists rest; exact Hrest. }
    rewrite Hforward, Hbackward in Hcheck.
    apply (proj1 (legacy_disjoint_b_correct ET (writes k) read)); exact Hcheck.
  - intros Hclear k Hk.
    destruct (FinSet.mem EN k (legacy_reached p roots)) eqn:Hforward;
      destruct (FinSet.mem EN k (legacy_reached (prepared_reverse p [load]) [load]))
      eqn:Hbackward; cbn; try reflexivity.
    apply (legacy_reached_correct EN g p roots k Hready Hroots) in Hforward.
    apply (Hback k Hk) in Hbackward.
    destruct Hforward as [root [Hroot [first Hfirst]]], Hbackward as [rest Hrest].
    apply legacy_disjoint_b_correct; apply (Hclear root (first ++ rest) Hroot).
    + eapply idf_path_app; eassumption.
    + apply legacy_nodes_prefix; eapply legacy_path_end_node; exact Hfirst.
Qed.

Lemma legacy_clear_reaches {N E T} (g : Graph.t N E) roots load
    (writes : N -> list (footprint T)) read :
  (forall root es, In root roots -> path g root es load ->
    forall k, In k (legacy_nodes g root es) -> legacy_disjoint (writes k) read) <->
  (forall k, (exists root, In root roots /\ reaches g root k) -> reaches g k load ->
    legacy_disjoint (writes k) read).
Proof.
  split.
  - intros Hclear k [root [Hroot [first Hfirst]]] [rest Hrest].
    apply (Hclear root (first ++ rest) Hroot).
    + eapply idf_path_app; eassumption.
    + apply legacy_nodes_prefix; eapply legacy_path_end_node; exact Hfirst.
  - intros Hclear root es Hroot Hpath k Hk.
    destruct (legacy_path_nodes_split g root es load k Hpath Hk)
      as [first [rest [Hfirst Hrest]]].
    apply Hclear.
    + exists root; split; [exact Hroot|exists first; exact Hfirst].
    + exists rest; exact Hrest.
Qed.

Lemma legacy_reaches_listed {N E} (g : Graph.t N E) u v :
  graph_wf g -> In u (Graph.nodes g) -> reaches g u v -> In v (Graph.nodes g).
Proof.
  intros Hwf Hu [es Hpath]; eapply legacy_path_nodes_listed;
    [exact Hwf|exact Hu|exact Hpath|eapply legacy_path_end_node; exact Hpath].
Qed.

Lemma legacy_slice_original {N E T} (EN : encoding N) (ET : encoding T) (g : Graph.t N E)
    writes read roots load :
  graph_wf g -> incl roots (Graph.nodes g) -> In load (Graph.nodes g) ->
  (legacy_slice EN ET (legacy_cfg EN g) (prepare EN (legacy_cfg EN g)) writes read roots load =
    true <-> forall root es, In root roots -> path g root es load ->
      forall k, In k (legacy_nodes g root es) -> legacy_disjoint (writes k) read).
Proof.
  intros Hwf Hroots Hload.
  rewrite (legacy_slice_correct EN ET _ _ writes read roots load
    (legacy_cfg_ready EN g Hwf) Hroots Hload).
  rewrite (legacy_clear_reaches (legacy_cfg EN g)), (legacy_clear_reaches g); split.
  - intros Hclear k [root [Hroot Hfirst]] Hrest.
    assert (Hk : In k (Graph.nodes g)).
    { eapply legacy_reaches_listed; [exact Hwf|apply Hroots; exact Hroot|exact Hfirst]. }
    apply Hclear.
    + exists root; split; [exact Hroot|].
      apply (legacy_cfg_reaches EN g root k Hwf (Hroots root Hroot)); exact Hfirst.
    + apply (legacy_cfg_reaches EN g k load Hwf Hk); exact Hrest.
  - intros Hclear k [root [Hroot Hfirst]] Hrest.
    assert (Hk : In k (Graph.nodes g)).
    { exact (legacy_reaches_listed (legacy_cfg EN g) root k
        (proj1 (legacy_cfg_ready EN g Hwf)) (Hroots root Hroot) Hfirst). }
    apply Hclear.
    + exists root; split; [exact Hroot|].
      apply (legacy_cfg_reaches EN g root k Hwf (Hroots root Hroot)); exact Hfirst.
    + apply (legacy_cfg_reaches EN g k load Hwf Hk); exact Hrest.
Qed.

Definition legacy_successors {N E} (EN : encoding N) (g : Graph.t N E)
    (p : prepared EN g) n : list N := map (Graph.target g) (succ_edges p n).

Lemma legacy_successors_correct {N E} (EN : encoding N) (g : Graph.t N E)
    n root : graph_wf g -> In n (Graph.nodes g) ->
  (In root (legacy_successors EN (legacy_cfg EN g) (prepare EN (legacy_cfg EN g)) n) <->
    exists e, In e (Graph.out g n) /\ Graph.target g e = root).
Proof.
  intros Hwf Hlisted; unfold legacy_successors.
  rewrite (succ_agrees (proj2 (proj2 (legacy_cfg_ready EN g Hwf))) n Hlisted).
  rewrite in_map_iff; split.
  - intros [edge [Htarget Hedge]]; apply legacy_cfg_edge in Hedge.
    change (snd edge = root) in Htarget.
    destruct Hedge as [_ [_ [e [Hedge Heq]]]]; exists e; split; [exact Hedge|congruence].
  - intros [e [Hedge Htarget]]; exists (n, root); split; [reflexivity|].
    apply legacy_cfg_edge; cbn; split; [exact Hlisted|split; [reflexivity|exists e; auto]].
Qed.

Lemma legacy_successors_listed {N E} (EN : encoding N) (g : Graph.t N E) n :
  graph_wf g -> In n (Graph.nodes g) ->
  incl (legacy_successors EN (legacy_cfg EN g) (prepare EN (legacy_cfg EN g)) n) (Graph.nodes g).
Proof.
  intros Hwf Hlisted root Hin.
  apply (legacy_successors_correct EN g n root Hwf Hlisted) in Hin as [e [Hedge <-]].
  eapply out_target_in; eassumption.
Qed.

Definition legacy_pair_check {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T)
    (f : F) (g : Graph.t N E) (p : prepared EN g)
    (reached : FinSet.t N) (writes reads : N -> list (footprint T))
    (load : N) (d : mem_node F N) : bool :=
  FinSet.mem EN load reached &&
  match d with
  | MDef owner n => Pos.eqb (encode EF owner) (encode EF f) && FinSet.mem EN n reached &&
      legacy_slice EN ET g p writes (reads load)
        (legacy_successors EN g p n) load
  | MLive owner => Pos.eqb (encode EF owner) (encode EF f) &&
      legacy_slice EN ET g p writes (reads load) (Graph.entries g) load
  end.

Lemma legacy_pair_check_correct {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T)
    f (g : Graph.t N E) writes reads load d :
  graph_wf g -> In load (Graph.nodes g) ->
  (legacy_pair_check EN EF ET f (legacy_cfg EN g) (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g)) writes reads load d = true
    <-> legacy_pair_clear f g writes reads load d).
Proof.
  intros Hwf Hload.
  assert (Hreach : forall n, FinSet.mem EN n
      (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g)) = true <-> reachable g n).
  { intro n; unfold legacy_reached.
    rewrite (reachable_dfs EN _ _ n (legacy_cfg_ready EN g Hwf)); apply legacy_cfg_reachable;
      exact Hwf. }
  unfold legacy_pair_check, legacy_pair_clear; rewrite andb_true_iff, Hreach.
  destruct d as [owner n|owner]; repeat rewrite andb_true_iff; rewrite Pos.eqb_eq.
  - rewrite Hreach; split.
    + intros [Hreachable [[Howner Hn] Hslice]]; apply (encode_injective EF) in Howner.
      split; [exact Hreachable|split; [exact Howner|split; [exact Hn|]]].
      pose proof ((proj1 (legacy_slice_original EN ET g writes (reads load) _ load Hwf
        (legacy_successors_listed EN g n Hwf (reachable_in_nodes g n Hwf Hn)) Hload)) Hslice)
        as Hslice_clear.
      intros e es Hedge Hpath k Hk.
      apply (Hslice_clear (Graph.target g e) es); [|exact Hpath|exact Hk].
      apply (legacy_successors_correct EN g n _ Hwf (reachable_in_nodes g n Hwf Hn)).
      exists e; auto.
    + intros [Hreachable [Howner [Hn Hclear]]]; split; [exact Hreachable|split].
      * split; [rewrite Howner; reflexivity|exact Hn].
      * apply (proj2 (legacy_slice_original EN ET g writes (reads load) _ load Hwf
          (legacy_successors_listed EN g n Hwf (reachable_in_nodes g n Hwf Hn)) Hload)).
        intros root es Hroot Hpath k Hk.
        apply (legacy_successors_correct EN g n root Hwf (reachable_in_nodes g n Hwf Hn))
          in Hroot as [e [Hedge Htarget]].
        rewrite <- Htarget in Hpath, Hk; eapply Hclear; eassumption.
  - rewrite (legacy_slice_original EN ET g writes (reads load) (Graph.entries g) load Hwf
      (entries_in Hwf) Hload).
    split.
    + intros [Hreachable [Howner Hclear]]; apply (encode_injective EF) in Howner; auto.
    + intros [Hreachable [Howner Hclear]]; split; [exact Hreachable|split; [|exact Hclear]].
      rewrite Howner; reflexivity.
Qed.

(** The optional checker validates every finite-node candidate using its own all-walk decision. *)
Definition no_clobber_check {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F)
    (g : Graph.t N E) (writes reads : N -> list (footprint T)) (ms : memory_ssa F N) : bool :=
  let c := legacy_cfg EN g in
  let p := prepare EN c in
  let reached := legacy_reached p (Graph.entries c) in
  forallb (fun n => match def_of_load ms n with
    | None => true
    | Some d => legacy_pair_check EN EF ET f c p reached writes reads n d
    end) (Graph.nodes g).

(** Acceptance is equivalent to the strong all-walk property for every listed candidate. *)
Theorem no_clobber_check_correct {F N E T} (EN : encoding N) (EF : encoding F)
    (ET : encoding T) (f : F) (g : Graph.t N E) (writes reads : N -> list (footprint T))
    (ms : memory_ssa F N) :
  graph_wf g ->
  (no_clobber_check EN EF ET f g writes reads ms = true <->
    forall n d, In n (Graph.nodes g) -> def_of_load ms n = Some d ->
      legacy_pair_clear f g writes reads n d).
Proof.
  intro Hwf; unfold no_clobber_check; rewrite forallb_forall; split.
  - intros Hcheck n d Hn Hcandidate; specialize (Hcheck n Hn); rewrite Hcandidate in Hcheck.
    apply (legacy_pair_check_correct EN EF ET f g writes reads n d Hwf Hn); exact Hcheck.
  - intros Hclear n Hn; destruct (def_of_load ms n) as [d|] eqn:Hcandidate; [|reflexivity].
    apply (legacy_pair_check_correct EN EF ET f g writes reads n d Hwf Hn).
    eapply Hclear; eassumption.
Qed.

(** * Conditional projection *)

Definition legacy_clobber_proposal {F N E} (f : F) (g : Graph.t N E)
    (result : memory_clobber_result N E) : option (mem_node F N) :=
  match clobber_roots result with
  | [MemoryLive] => Some (MLive f)
  | [MemoryDef e _] => Some (MDef f (Graph.source g e))
  | _ => None
  end.

Definition legacy_occurrence_proposal {F N E T} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) f (g : Graph.t N E) effects (mg : memory_graph N E)
    (listed_edges : FinSet.t E) (reached : FinSet.t N)
    (effect_table : Map.t E (Map.t nat (memory_effect T)))
    (reads : N -> list (footprint T)) (load_occurrence : N -> option (E * nat))
    (fuel : positive) (n : N) : option (mem_node F N) :=
  match load_occurrence n with
  | Some (e, i) =>
    if Pos.eqb (encode EN (Graph.source g e)) (encode EN n) &&
      FinSet.mem EN (Graph.source g e) reached && FinSet.mem EE e listed_edges then
      match memory_walk_effect_get EE effect_table e i, memory_before mg e i with
      | Some a, Some input =>
        if memory_effect_has_read a then
          legacy_clobber_proposal f g
            (memory_clobbers EN EE ET g effects mg (MemoryRegions (reads n)) input fuel)
        else None
      | _, _ => None
      end
    else None
  | None => None
  end.

Definition legacy_retain {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T)
    f (g : Graph.t N E) (p : prepared EN g) reached writes reads n
    (proposal : option (mem_node F N)) : option (mem_node F N) :=
  match proposal with
  | Some d => if legacy_pair_check EN EF ET f g p reached writes reads n d then Some d else None
  | None => None
  end.

Lemma legacy_retain_correct {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T)
    f (g : Graph.t N E) writes reads n proposal (d : mem_node F N) :
  graph_wf g -> In n (Graph.nodes g) ->
  legacy_retain EN EF ET f (legacy_cfg EN g) (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    writes reads n proposal = Some d -> legacy_pair_clear f g writes reads n d.
Proof.
  intros Hwf Hn Hcandidate; unfold legacy_retain in Hcandidate.
  destruct proposal as [proposed|]; [|discriminate].
  destruct (legacy_pair_check EN EF ET f (legacy_cfg EN g) (prepare EN (legacy_cfg EN g))
    (legacy_reached (prepare EN (legacy_cfg EN g)) (Graph.entries g))
    writes reads n proposed) eqn:Hclear; [|discriminate].
  inversion Hcandidate; subst proposed.
  apply (legacy_pair_check_correct EN EF ET f g writes reads n d Hwf Hn); exact Hclear.
Qed.

(** Singleton walker proposals survive only after the stronger independent per-load decision. *)
Definition project_memory_legacy {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (f : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (writes reads : N -> list (footprint T))
    (mg : memory_graph N E) (load_occurrence : N -> option (E * nat)) (fuel : positive) :
    memory_ssa F N :=
  let c := legacy_cfg EN g in
  let p := prepare EN c in
  let reached := legacy_reached p (Graph.entries c) in
  let listed_edges := FinSet.of_list EE (edges_of g) in
  let effect_table := memory_walk_effect_table EE g effects in
  MemorySSA (fun n => legacy_retain EN EF ET f c p reached writes reads n
    (legacy_occurrence_proposal EN EE ET f g effects mg listed_edges reached effect_table
      reads load_occurrence fuel n)).

(** Every retained projection pair satisfies the legacy checker's full all-walk condition. *)
Theorem project_memory_legacy_correct {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (f : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (writes reads : N -> list (footprint T))
    (mg : memory_graph N E) (load_occurrence : N -> option (E * nat)) (fuel : positive) :
  memory_graph_wf g effects mg ->
  no_clobber_check EN EF ET f g writes reads
    (project_memory_legacy EN EE EF ET f g effects writes reads mg load_occurrence fuel) = true.
Proof.
  intro Hwf; apply no_clobber_check_correct; [exact (memory_cfg_wf Hwf)|].
  intros n d Hn Hcandidate.
  eapply (legacy_retain_correct EN EF ET f g writes reads n _ d (memory_cfg_wf Hwf) Hn).
  exact Hcandidate.
Qed.

(** * Byte preservation at historical identities *)

Lemma legacy_run_reachable {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    s es t : reachable_state m s -> run_edges m gv s es t -> reachable_state m t.
Proof.
  intros Hreach Hrun; revert Hreach.
  induction Hrun as [s|s tr s' e es t Hstep Htaken Hrun IH|
    s tr s' es t Hstep Hstays Hrun IH]; intro Hreach; [exact Hreach| |];
    apply IH; eapply reachable_state_step; eassumption.
Qed.

Lemma legacy_run_bytes {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L)
    (laws : bytes_laws m bv) (read : list (footprint T)) s es t :
  reachable_state m s -> run_edges m (bgv bv) s es t ->
  (forall k, In k (legacy_nodes (cfg (bgv bv)) (point (bgv bv) s) es) ->
    legacy_disjoint (writes_at bv k) read) ->
  forall l ty o, covered read ty o 1 -> bsite bv s l = Some ty ->
    byte bv t l o = byte bv s l o.
Proof.
  intros Hreach Hrun; revert Hreach.
  induction Hrun as [s|s tr s' e es t Hstep Htaken Hrun IH|
    s tr s' es t Hstep Hstays Hrun IH]; intros Hreach Hclear l ty o Hread Hsite.
  - reflexivity.
  - pose proof (taken_edge (by_view laws) s tr s' e Hreach Hstep Htaken) as [_ Htarget].
    assert (Hclear_rest : forall k,
      In k (legacy_nodes (cfg (bgv bv)) (point (bgv bv) s') es) ->
      legacy_disjoint (writes_at bv k) read).
    { intros k Hk; apply Hclear; right; cbn [map]; rewrite Htarget; exact Hk. }
    pose proof (byte_site_stable laws s tr s' l ty Hreach Hstep Hsite) as Hsite'.
    rewrite (IH (reachable_state_step m s tr s' Hreach Hstep) Hclear_rest l ty o Hread Hsite').
    eapply (bytes_unwritten_step m bv laws); [exact Hreach|exact Hstep|exact Hsite|].
    intro Hwrite; apply (Hclear (point (bgv bv) s) (or_introl eq_refl) ty o Hwrite Hread).
  - exfalso; exact (by_no_stays laws s tr s' Hstays).
Qed.

(** Accepted candidates preserve exact byte observations of each same historical allocation. *)
Theorem no_clobber_unchanged {S O N E T F L} (m : semantics S O) (bv : bytes_view S O N E T L)
    (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F) (ms : memory_ssa F N)
    (reads : N -> list (footprint T)) :
  bytes_laws m bv ->
  no_clobber_check EN EF ET f (cfg (bgv bv)) (writes_at bv) reads ms = true ->
  (forall s s1 t e1 es' n, reachable_state m s -> run_edges m (bgv bv) s (e1 :: nil) s1 ->
     run_edges m (bgv bv) s1 es' t -> point (bgv bv) t = n ->
     def_of_load ms n = Some (MDef f (Graph.source (cfg (bgv bv)) e1)) ->
     forall l ty o, covered (reads n) ty o 1 -> bsite bv s1 l = Some ty ->
       byte bv t l o = byte bv s1 l o) /\
  (forall s es t n, reachable_state m s -> In (point (bgv bv) s) (Graph.entries (cfg (bgv bv))) ->
     run_edges m (bgv bv) s es t -> point (bgv bv) t = n -> def_of_load ms n = Some (MLive f) ->
     forall l ty o, covered (reads n) ty o 1 -> bsite bv s l = Some ty ->
       byte bv t l o = byte bv s l o).
Proof.
  intros laws Hcheck.
  pose proof (cfg_wf (by_view laws)) as Hwf.
  pose proof ((proj1 (no_clobber_check_correct EN EF ET f (cfg (bgv bv))
    (writes_at bv) reads ms Hwf)) Hcheck) as Haccepted.
  split.
  - intros s s1 t e1 es n Hreach Hdefinition Hrun Hpoint Hcandidate l ty o Hread Hsite.
    pose proof (legacy_run_reachable m (bgv bv) s [e1] s1 Hreach Hdefinition) as Hreach1.
    pose proof (run_edges_path m (bgv bv) s1 t es (by_view laws) Hreach1 Hrun) as Hpath.
    pose proof (run_edges_path m (bgv bv) s s1 [e1] (by_view laws) Hreach Hdefinition)
      as Hdefinition_path.
    assert (Hedge : In e1 (Graph.out (cfg (bgv bv)) (Graph.source (cfg (bgv bv)) e1))).
    { inversion Hdefinition_path; assumption. }
    assert (Htarget : Graph.target (cfg (bgv bv)) e1 = point (bgv bv) s1).
    { inversion Hdefinition_path as [|edge rest final Hlisted Htail]; subst.
      inversion Htail; reflexivity. }
    assert (Hload : In n (Graph.nodes (cfg (bgv bv)))).
    { rewrite <- Hpoint; apply (view_point_in_nodes m (bgv bv) t (by_view laws)).
      eapply legacy_run_reachable; eassumption. }
    destruct (Haccepted n _ Hload Hcandidate) as [_ [_ [_ Hclear]]].
    eapply legacy_run_bytes; [exact laws|exact Hreach1|exact Hrun| |exact Hread|exact Hsite].
    intros k Hk; apply (Hclear e1 es Hedge); rewrite ?Htarget, <- ?Hpoint; assumption.
  - intros s es t n Hreach Hentry Hrun Hpoint Hcandidate l ty o Hread Hsite.
    pose proof (run_edges_path m (bgv bv) s t es (by_view laws) Hreach Hrun) as Hpath.
    assert (Hload : In n (Graph.nodes (cfg (bgv bv)))).
    { rewrite <- Hpoint; eapply legacy_reaches_listed;
        [exact Hwf|apply (entries_in Hwf); exact Hentry|exists es; exact Hpath]. }
    destruct (Haccepted n _ Hload Hcandidate) as [_ [_ Hclear]].
    eapply legacy_run_bytes; [exact laws|exact Hreach|exact Hrun| |exact Hread|exact Hsite].
    intros k Hk; apply (Hclear (point (bgv bv) s) es Hentry); rewrite <- ?Hpoint; assumption.
Qed.
