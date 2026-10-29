(** * Aggressive dead-code marking

    A reverse control-dependence worklist retains effects and possibly diverging loops.
    For example, keeping either arm of a diamond also keeps its controlling branch.
    Builds on: GraphControlDependence, GraphDfs and AnalysesDemand. *)

From Stdlib Require Import List Bool.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphPostDominators GraphControlDependence GraphIdf.
From Gaulois.Analyses Require Import AnalysesDemand.
Import List.ListNotations.

(** The client identifies finite graph nodes whose effects or divergence must be retained. *)
Record adce_input (N E : Type) : Type := AdceInput {
  agraph : Graph.t N E;
  aexits : list N;
  effectful_node : N -> bool;
  may_not_terminate : N -> bool
}.

Arguments agraph {N E}.
Arguments aexits {N E}.
Arguments effectful_node {N E}.
Arguments may_not_terminate {N E}.

(** Materialize the reverse control-dependence buckets once, discarding unlisted controllers. *)
Definition adce_control_index {N E} (EN : encoding N) (ai : adce_input N E) :
    Map.t N (FinSet.t N) :=
  let g := agraph ai in
  let p := prepare EN g in
  let nodes := FinSet.of_list EN (Graph.nodes g) in
  Map.map (fun edges => FinSet.inter EN nodes
    (FinSet.of_list EN (map (Graph.source g) edges)))
    (control_deps p (aexits ai) (post_dominator_tree p (aexits ai))).

Definition adce_controllers {N E} (EN : encoding N) (ai : adce_input N E) (n : N) : FinSet.t N :=
  match Map.get EN n (adce_control_index EN ai) with
  | Some controllers => controllers
  | None => FinSet.empty
  end.

Lemma adce_controllers_wf {N E} (EN : encoding N) (ai : adce_input N E) n :
  FinSet.wf EN (adce_controllers EN ai n).
Proof.
  unfold adce_controllers, adce_control_index; rewrite Map.get_map.
  destruct (Map.get EN n (control_deps (prepare EN (agraph ai)) (aexits ai)
    (post_dominator_tree (prepare EN (agraph ai)) (aexits ai)))); cbn.
  - apply FinSet.wf_inter; apply demand_universe_wf.
  - apply Map.wf_empty.
Qed.

Lemma adce_controllers_support {N E} (EN : encoding N) (ai : adce_input N E) n b :
  FinSet.mem EN b (adce_controllers EN ai n) = true -> In b (Graph.nodes (agraph ai)).
Proof.
  unfold adce_controllers, adce_control_index; rewrite Map.get_map.
  destruct (Map.get EN n (control_deps (prepare EN (agraph ai)) (aexits ai)
    (post_dominator_tree (prepare EN (agraph ai)) (aexits ai)))) as [edges|]; cbn.
  - rewrite FinSet.mem_inter; intros [Hnode _].
    apply FinSet.of_list_spec in Hnode; exact Hnode.
  - rewrite FinSet.mem_empty; discriminate.
Qed.

(** Prepared control buckets agree exactly with semantic control dependence on listed nodes. *)
Lemma adce_controllers_exact {N E} (EN : encoding N) (ai : adce_input N E) n b :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  In n (Graph.nodes (agraph ai)) ->
  (FinSet.mem EN b (adce_controllers EN ai n) = true <->
   In b (Graph.nodes (agraph ai)) /\ cdep (agraph ai) (aexits ai) b n).
Proof.
  intros Hready Hexits Hexit Hn.
  pose proof (dominator_exact_true EN _ _ (reverse_graph_ready EN _ _ _ Hready Hexits)) as Hcheck.
  split.
  - intro Hmem; pose proof (adce_controllers_support EN ai n b Hmem) as Hb.
    unfold adce_controllers, adce_control_index in Hmem; rewrite Map.get_map in Hmem.
    destruct (Map.get EN n (control_deps (prepare EN (agraph ai)) (aexits ai)
      (post_dominator_tree (prepare EN (agraph ai)) (aexits ai)))) as [edges|] eqn:Hget;
      cbn in Hmem; [|rewrite FinSet.mem_empty in Hmem; discriminate].
    apply FinSet.mem_inter in Hmem.
    destruct Hmem as [_ Hedges]; apply FinSet.of_list_spec in Hedges.
    apply in_map_iff in Hedges; destruct Hedges as [e [Hsource He]].
    split; [exact Hb|exists e; split; [exact Hsource|]].
    apply (proj1 (control_deps_exact EN _ _ n e (aexits ai)
      Hready Hexits Hexit Hcheck Hn ltac:(rewrite Hsource; exact Hb))).
    exists edges; auto.
  - intros [Hb [e [Hsource Hdep]]].
    destruct (proj2 (control_deps_exact EN _ _ n e (aexits ai)
      Hready Hexits Hexit Hcheck Hn ltac:(rewrite Hsource; exact Hb)) Hdep)
      as [edges [Hget He]].
    unfold adce_controllers, adce_control_index; rewrite Map.get_map, Hget; cbn.
    apply FinSet.mem_inter; split; apply FinSet.of_list_spec.
    + exact Hb.
    + apply in_map_iff; exists e; auto.
Qed.

(** Worklist edges run from a demanded node to its listed controllers. *)
Definition adce_dependency_graph {N E} (EN : encoding N) (ai : adce_input N E) :
    Graph.t N (N * N) :=
  let nodes := FinSet.of_list EN (Graph.nodes (agraph ai)) in
  let index := adce_control_index EN ai in
  {| Graph.nodes := Graph.nodes (agraph ai);
     Graph.entries := filter (fun n => effectful_node ai n || may_not_terminate ai n)
       (Graph.nodes (agraph ai));
     Graph.out := fun n => if FinSet.mem EN n nodes then
       map (fun b => (n, b)) (FinSet.elements
         (match Map.get EN n index with
          | Some s => s
          | None => FinSet.empty
          end)) else [];
     Graph.source := fst;
     Graph.target := snd |}.

Lemma adce_dependency_edge {N E} (EN : encoding N) (ai : adce_input N E) n e :
  In e (Graph.out (adce_dependency_graph EN ai) n) <->
  fst e = n /\ In n (Graph.nodes (agraph ai)) /\
    FinSet.mem EN (snd e) (adce_controllers EN ai n) = true.
Proof.
  change (In e (if FinSet.mem EN n (FinSet.of_list EN (Graph.nodes (agraph ai))) then
    map (fun b => (n, b)) (FinSet.elements (adce_controllers EN ai n)) else []) <->
    fst e = n /\ In n (Graph.nodes (agraph ai)) /\
      FinSet.mem EN (snd e) (adce_controllers EN ai n) = true).
  destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.nodes (agraph ai)))) eqn:Hn.
  - apply FinSet.of_list_spec in Hn; rewrite in_map_iff; split.
    + intros [b [Heq Hb]]; subst e; cbn; split; [reflexivity|]; split; [exact Hn|].
      apply FinSet.elements_spec; [apply adce_controllers_wf|exact Hb].
    + intros [Heq [_ Hmem]]; destruct e as [u b]; cbn in Heq, Hmem; subst u.
      exists b; split; [reflexivity|].
      apply (proj2 (FinSet.elements_spec EN b _ (adce_controllers_wf EN ai n))); exact Hmem.
  - split; [contradiction|intros [_ [Hin _]]].
    pose proof (proj2 (FinSet.of_list_spec EN n (Graph.nodes (agraph ai))) Hin); congruence.
Qed.

Lemma adce_dependency_ready {N E} (EN : encoding N) (ai : adce_input N E) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  ready EN (adce_dependency_graph EN ai) (prepare EN (adce_dependency_graph EN ai)).
Proof.
  intro Hready; apply prepare_ready.
  - constructor.
    + exact (nodes_nodup (proj1 Hready)).
    + intros n Hin; apply filter_In in Hin; exact (proj1 Hin).
    + intros n e He; apply adce_dependency_edge in He; exact (proj1 He).
    + intros n e Hn He; apply adce_dependency_edge in He.
      exact (adce_controllers_support EN ai n (snd e) (proj2 (proj2 He))).
  - intro n; change (NoDup (if FinSet.mem EN n
      (FinSet.of_list EN (Graph.nodes (agraph ai))) then
      map (fun b => (n, b)) (FinSet.elements (adce_controllers EN ai n)) else [])).
    destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.nodes (agraph ai))));
      [|constructor].
    pose proof (FinSet.elements_nodup EN _ (adce_controllers_wf EN ai n)) as Hnd.
    induction Hnd as [|b rest Hfresh Hnd IH]; cbn; constructor; [|exact IH].
    intro Hin; apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]].
    injection Heq as Heq; subst x; contradiction.
Qed.

(** DFS is a seen-set worklist: each discovered effect or controller is processed once. *)
Definition adce_marked {N E} (EN : encoding N) (ai : adce_input N E) : FinSet.t N :=
  let g := adce_dependency_graph EN ai in
  visited (dfs (prepare EN g) FinSet.empty (Graph.entries g)).

Lemma adce_marked_reachable {N E} (EN : encoding N) (ai : adce_input N E) n :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  (FinSet.mem EN n (adce_marked EN ai) = true <-> reachable (adce_dependency_graph EN ai) n).
Proof.
  intro Hready; apply reachable_dfs, adce_dependency_ready; exact Hready.
Qed.

Lemma adce_seed_marked {N E} (EN : encoding N) (ai : adce_input N E) n :
  ready EN (agraph ai) (prepare EN (agraph ai)) -> In n (Graph.nodes (agraph ai)) ->
  effectful_node ai n || may_not_terminate ai n = true ->
  FinSet.mem EN n (adce_marked EN ai) = true.
Proof.
  intros Hready Hn Hseed; apply adce_marked_reachable; [exact Hready|].
  apply reachable_entry; apply filter_In; auto.
Qed.

(** Marking has finite node support and retains effects, controllers and possible divergence. *)
Theorem adce_closed {N E} (EN : encoding N) (ai : adce_input N E) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall n, FinSet.mem EN n (adce_marked EN ai) = true -> In n (Graph.nodes (agraph ai))) /\
  (forall n, In n (Graph.nodes (agraph ai)) -> effectful_node ai n = true ->
     FinSet.mem EN n (adce_marked EN ai) = true) /\
  (forall b n, In b (Graph.nodes (agraph ai)) -> In n (Graph.nodes (agraph ai)) ->
     FinSet.mem EN n (adce_marked EN ai) = true -> cdep (agraph ai) (aexits ai) b n ->
     FinSet.mem EN b (adce_marked EN ai) = true) /\
  (forall n, In n (Graph.nodes (agraph ai)) -> may_not_terminate ai n = true ->
     FinSet.mem EN n (adce_marked EN ai) = true).
Proof.
  intros Hready Hexits Hexit; split.
  - intros n Hmem; apply (reachable_in_nodes (adce_dependency_graph EN ai));
      [exact (proj1 (adce_dependency_ready EN ai Hready))|].
    apply adce_marked_reachable; assumption.
  - split.
    + intros n Hn Hseed; apply adce_seed_marked; try assumption; rewrite Hseed; reflexivity.
    + split.
      * intros b n Hb Hn Hmem Hdep; apply adce_marked_reachable; [exact Hready|].
        apply (@reachable_step _ _ (adce_dependency_graph EN ai) (n, b)).
        -- apply adce_marked_reachable; assumption.
        -- apply adce_dependency_edge; cbn; split; [reflexivity|]; split; [exact Hn|].
           apply adce_controllers_exact; [exact Hready|exact Hexits|exact Hexit|exact Hn|auto].
      * intros n Hn Hseed; apply adce_seed_marked; try assumption; rewrite Hseed, orb_true_r;
          reflexivity.
Qed.

(** Every set satisfying the listed-node marking rules contains all computed marks. *)
Theorem adce_least {N E} (EN : encoding N) (ai : adce_input N E) (M : FinSet.t N) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall n, In n (Graph.nodes (agraph ai)) -> effectful_node ai n = true ->
     FinSet.mem EN n M = true) ->
  (forall b n, In b (Graph.nodes (agraph ai)) -> In n (Graph.nodes (agraph ai)) ->
     FinSet.mem EN n M = true -> cdep (agraph ai) (aexits ai) b n -> FinSet.mem EN b M = true) ->
  (forall n, In n (Graph.nodes (agraph ai)) -> may_not_terminate ai n = true ->
     FinSet.mem EN n M = true) ->
  forall n, FinSet.mem EN n (adce_marked EN ai) = true -> FinSet.mem EN n M = true.
Proof.
  intros Hready Hexits Hexit Heffect Hcontrol Hdiverge n Hmem.
  apply adce_marked_reachable in Hmem; [|exact Hready].
  induction Hmem as [n Hin|[n b] Hreach IH Hedge].
  - apply filter_In in Hin; destruct Hin as [Hn Hseed]; apply orb_true_iff in Hseed.
    destruct Hseed as [Hseed|Hseed]; [apply Heffect|apply Hdiverge]; assumption.
  - apply adce_dependency_edge in Hedge; cbn in Hedge; destruct Hedge as [_ [Hn Hb]].
    apply adce_controllers_exact in Hb; try assumption.
    destruct Hb as [Hb Hdep]; exact (Hcontrol b n Hb Hn IH Hdep).
Qed.

(** A skip walk reaches a marked node without crossing any different marked node. *)
Definition skips_to {N E} (g : Graph.t N E) (marked : N -> bool) (n m : N) : Prop :=
  marked m = true /\ exists es, path g n es m /\
    forall e, In e es -> Graph.target g e = m \/ marked (Graph.target g e) = false.

(** * Unique first marked successors *)

Section SkipProof.
Context {N E : Type} (EN : encoding N) (ai : adce_input N E).
Hypotheses
  (Hready : ready EN (agraph ai) (prepare EN (agraph ai)))
  (Hexits : incl (aexits ai) (Graph.nodes (agraph ai)))
  (Hexit : exits_reachable (agraph ai) (aexits ai)).

Local Abbreviation marked := (fun n => FinSet.mem EN n (adce_marked EN ai)).
Local Abbreviation g := (agraph ai).

Lemma adce_postdom_predecessor e m : In (Graph.source g e) (Graph.nodes g) ->
  In e (Graph.out g (Graph.source g e)) -> marked (Graph.source g e) = false ->
  marked m = true -> post_dominates g (aexits ai) m (Graph.target g e) ->
  post_dominates g (aexits ai) m (Graph.source g e).
Proof.
  intros Hsource Hedge Hunmarked Hmarked Hpost.
  pose proof (adce_closed EN ai Hready Hexits Hexit) as [Hsupport [_ [Hcontrol _]]].
  pose proof (dominator_exact_true EN _ _ (reverse_graph_ready EN _ _ _ Hready Hexits)) as Hcheck.
  pose proof (post_dominator_tree_exact EN g (prepare EN g) m (Graph.source g e)
    (aexits ai) Hready Hexits Hsource Hcheck (Hexit _ Hsource)) as Hexact.
  destruct (dominates_b EN (post_dominator_tree (prepare EN g) (aexits ai))
    m (Graph.source g e)) eqn:Hquery.
  - apply Hexact; reflexivity.
  - exfalso; assert (Hdep : cdep g (aexits ai) (Graph.source g e) m).
    { exists e; split; [reflexivity|]; split; [exact Hedge|]; split; [exact Hpost|].
      intros [Hdom _]; apply Hexact in Hdom; congruence. }
    pose proof (Hcontrol _ m Hsource (Hsupport m Hmarked) Hmarked Hdep); congruence.
Qed.

Lemma adce_skip_postdom n m es : In n (Graph.nodes g) -> marked n = false -> marked m = true ->
  path g n es m ->
  (forall e, In e es -> Graph.target g e = m \/ marked (Graph.target g e) = false) ->
  post_dominates g (aexits ai) m n.
Proof.
  intros Hn Hfalse Hmarked Hpath; revert Hn Hfalse.
  induction Hpath as [n|e rest m Hedge Hpath IH]; intros Hn Hfalse Hwalk.
  - intros es x Hp Hx; left; reflexivity.
  - apply adce_postdom_predecessor with (e := e); try assumption.
    destruct (Hwalk e (or_introl eq_refl)) as [Heq|Hunmarked].
    + rewrite Heq; intros es x Hp Hx; left; reflexivity.
    + apply IH.
      * exact Hmarked.
      * exact (out_target_in (proj1 Hready) _ e Hn Hedge).
      * exact Hunmarked.
      * intros a Ha; apply Hwalk; right; exact Ha.
Qed.

Lemma adce_postdom_skip_endpoint n first other : marked n = false -> marked first = true ->
  first <> other -> post_dominates g (aexits ai) first n ->
  skips_to g marked n other -> post_dominates g (aexits ai) first other.
Proof.
  intros Hn Hfirst Hne Hpost [_ [prefix [Hprefix Hwalk]]] suffix x Hsuffix Hx.
  destruct (Hpost (prefix ++ suffix) x (idf_path_app g n prefix other suffix x Hprefix Hsuffix) Hx)
    as [Heq|[e [Hin Htarget]]].
  - subst first; congruence.
  - apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + destruct (Hwalk e Hin) as [Heq|Hunmarked].
      * exfalso; apply Hne; congruence.
      * rewrite Htarget in Hunmarked; congruence.
    + right; exists e; auto.
Qed.

Lemma adce_postdom_antisym a b : In a (Graph.nodes g) -> In b (Graph.nodes g) ->
  post_dominates g (aexits ai) a b -> post_dominates g (aexits ai) b a -> a = b.
Proof.
  intros Ha Hb Hab Hba.
  pose proof (reverse_graph_ready EN g (prepare EN g) (aexits ai) Hready Hexits) as Hreverse.
  apply (idf_dominance_antisym EN _ (prepared_reverse (prepare EN g) (aexits ai)) Hreverse).
  - apply control_reverse_reachable; assumption.
  - apply control_reverse_reachable; assumption.
  - apply post_dominates_iff_reverse; assumption.
  - apply post_dominates_iff_reverse; assumption.
Qed.
End SkipProof.

(** All first marked successors of a listed unmarked starting node are equal. *)
Theorem adce_skip_unique {N E} (EN : encoding N) (ai : adce_input N E) (n m1 m2 : N) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall x, In x (aexits ai) -> FinSet.mem EN x (adce_marked EN ai) = true) ->
  In n (Graph.nodes (agraph ai)) -> FinSet.mem EN n (adce_marked EN ai) = false ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m1 ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m2 -> m1 = m2.
Proof.
  intros Hready Hexits Hexit Hmarked_exits Hn Hfalse Hfirst Hsecond.
  destruct (dfs_eq_dec EN m1 m2) as [Heq|Hne]; [exact Heq|].
  pose proof (proj1 (adce_closed EN ai Hready Hexits Hexit)) as Hsupport.
  assert (Hpost1 : post_dominates (agraph ai) (aexits ai) m1 n).
  { destruct Hfirst as [Hm [es [Hpath Hwalk]]].
    exact (adce_skip_postdom EN ai Hready Hexits Hexit n m1 es Hn Hfalse Hm Hpath Hwalk). }
  assert (Hpost2 : post_dominates (agraph ai) (aexits ai) m2 n).
  { destruct Hsecond as [Hm [es [Hpath Hwalk]]].
    exact (adce_skip_postdom EN ai Hready Hexits Hexit n m2 es Hn Hfalse Hm Hpath Hwalk). }
  apply (adce_postdom_antisym EN ai Hready Hexits Hexit).
  - apply Hsupport; exact (proj1 Hfirst).
  - apply Hsupport; exact (proj1 Hsecond).
  - exact (adce_postdom_skip_endpoint EN ai n m1 m2 Hfalse (proj1 Hfirst) Hne Hpost1 Hsecond).
  - exact (adce_postdom_skip_endpoint EN ai n m2 m1 Hfalse (proj1 Hsecond)
      (fun Heq => Hne (eq_sym Heq)) Hpost2 Hfirst).
Qed.
