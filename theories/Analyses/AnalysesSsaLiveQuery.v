(** * Reusable SSA liveness queries

    Graph preparation separates reduced reachability and back-edge closure from value uses.
    For example, changing the operand on one parallel phi edge only rebuilds the value index.
    Builds on: GraphDfs, GraphDominators, GraphReducible, ViewsSsaPoints and AnalysesRules. *)

From Stdlib Require Import List Bool PArith Lia Permutation Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphDominators GraphReducible.
From Gaulois.Fixpoint Require Import FixpointLeast.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Rules Require Import RulesSyntax RulesModel RulesSolve.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesRules.
Import List.ListNotations.

(** A reduced path traverses no edge that retreats in the selected DFS forest. *)
Definition reduced_path {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) (u v : N) : Prop :=
  exists es, path g u es v /\ Forall (fun e => ~ retreating EN g r e) es.

(** One interesting back-edge target is outside the source's reduced reachable set. *)
Definition rt_step {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) (u v : N) : Prop :=
  ~ reduced_path EN g r u v /\
  exists a e, reduced_path EN g r u a /\ In e (Graph.out g a) /\
    Graph.target g e = v /\ retreating EN g r e.

(** T includes the query point and the finite closure of interesting back-edge targets. *)
Definition rt_reaches {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) : N -> N -> Prop :=
  clos_refl_trans N (rt_step EN g r).

(** The graph index has no value-dependent component. *)
Record ssa_query_graph (N E : Type) : Type := SsaQueryGraph {
  query_cfg : Graph.t N E;
  query_dfs : dfs_result N E;
  query_dom : dom_tree N;
  query_reduced : Map.t N (FinSet.t N);
  query_back_closure : Map.t N (FinSet.t N)
}.
Arguments SsaQueryGraph {N E}.
Arguments query_cfg {N E}.
Arguments query_dfs {N E}.
Arguments query_dom {N E}.
Arguments query_reduced {N E}.
Arguments query_back_closure {N E}.

(** Definitions and reachable use points are prepared independently of the R/T index. *)
Record ssa_query_values (N V : Type) : Type := SsaQueryValues {
  query_def : Map.t V N;
  query_uses : Map.t V (FinSet.t N)
}.
Arguments SsaQueryValues {N V}.
Arguments query_def {N V}.
Arguments query_uses {N V}.

(** Missing rows represent the empty set. *)
Definition live_index_get {K V} (EK : encoding K) (k : K)
    (m : Map.t K (FinSet.t V)) : FinSet.t V :=
  match Map.get EK k m with
  | Some s => s
  | None => FinSet.empty
  end.

(** * Graph preparation *)

Local Definition live_r_row {N E} (EN : encoding N) (target : E -> N)
    (out : N -> list E) (back : E -> bool) (n : N) (m : Map.t N (FinSet.t N)) :=
  Map.set EN n
    (fold_right (fun e a =>
       if back e then a else FinSet.union EN (live_index_get EN (target e) m) a)
      (FinSet.add EN n FinSet.empty) (out n)) m.

Local Definition live_r_build {N E} (EN : encoding N) (target : E -> N)
    (out : N -> list E) (back : E -> bool) (order : list N) :=
  fold_right (live_r_row EN target out back) Map.empty order.

Local Definition live_t_edges {N E} (EN : encoding N) (g : Graph.t N E)
    (out : N -> list E) (back : E -> bool) (rm : Map.t N (FinSet.t N)) (n : N) :=
  let reduced := live_index_get EN n rm in
  FinSet.of_list EN
    (flat_map (fun a => map (Graph.target g)
      (filter (fun e => back e && negb (FinSet.mem EN (Graph.target g e) reduced))
        (out a))) (FinSet.elements reduced)).

Local Definition live_tabulate {K V} (EK : encoding K) (f : K -> V) (ns : list K) :=
  fold_right (fun n m => Map.set EK n (f n) m) Map.empty ns.

Local Definition live_t_graph {N E} (EN : encoding N) (g : Graph.t N E)
    (out : N -> list E) (back : E -> bool) (rm : Map.t N (FinSet.t N)) (ns : list N) :=
  let rows := live_tabulate EN (fun n =>
    map (fun v => (n, v)) (FinSet.elements (live_t_edges EN g out back rm n))) ns in
  {| Graph.entries := [];
     Graph.nodes := ns;
     Graph.out := fun n => match Map.get EN n rows with Some es => es | None => [] end;
     Graph.source := @fst N N;
     Graph.target := @snd N N |}.

(** DFS and dominance are computed once; R uses reverse topological propagation, then T uses
    indexed finite DFS closures. Each T search reuses the same prepared adjacency. *)
Definition prepare_ssa_query_graph {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : ssa_query_graph N E :=
  let p := prepare EN g in
  let r := dfs p FinSet.empty (Graph.entries g) in
  let back := fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e) in
  let rm := live_r_build EN (Graph.target g) (succ_edges p) back (rpo r) in
  let tg := live_t_graph EN g (succ_edges p) back rm (preorder r) in
  let tp := prepare EN tg in
  SsaQueryGraph g r (dominator_tree p) rm
    (live_tabulate EN (fun n => FinSet.of_list EN (preorder (dfs tp FinSet.empty [n])))
      (preorder r)).

Local Definition live_value_add {N V} (EN : encoding N) (EV : encoding V)
    (n : N) (x : V) (m : Map.t V (FinSet.t N)) :=
  Map.set EV x (FinSet.add EN n (live_index_get EV x m)) m.

Local Definition live_point_vars {N E V} (p : point_uses N E V) n :=
  exit_use p n ++ flat_map (edge_use p) (Graph.out (live_graph p) n).

Local Definition live_value_uses {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) ns :=
  fold_right (fun n m => fold_right (live_value_add EN EV n) m (live_point_vars p n))
    Map.empty ns.

Local Definition live_value_defs {N V A} (EV : encoding V) (home : V -> option N)
    (bindings : list (V * A)) :=
  fold_right (fun binding m =>
    match home (fst binding) with
    | Some d => Map.set EV (fst binding) d m
    | None => m
    end) Map.empty bindings.

(** Reachable points are visited once; each outgoing occurrence contributes its own operands.
    Static definitions are copied only for indexed values, without scanning all values per query. *)
Definition prepare_ssa_query_values {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) : ssa_query_values N V :=
  let p := point_model s in
  let ns := preorder (dfs (prepare EN (live_graph p)) FinSet.empty
    (Graph.entries (live_graph p))) in
  let us := live_value_uses EN EV p ns in
  let ds := live_value_defs EV (point_definition s) (Map.elements us) in
  SsaQueryValues ds us.

(** The online query scans T(n) and the indexed uses, using trie membership and dominance. *)
Definition ssa_live_query {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : bool :=
  match Map.get EV x (query_def values) with
  | None => false
  | Some d =>
    let us := FinSet.elements (live_index_get EV x (query_uses values)) in
    existsb (fun t =>
      negb (Pos.eqb (encode EN d) (encode EN t)) && dominates_b EN (query_dom idx) d t &&
      (let reduced := live_index_get EN t (query_reduced idx) in
       existsb (fun u => FinSet.mem EN u reduced) us))
      (FinSet.elements (live_index_get EN n (query_back_closure idx)))
  end.

(** Graph preparation retains the selected public graph, DFS and directly proved dominator tree. *)
Theorem ssa_query_graph_structure {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) :
  ready EN g (prepare EN g) ->
  query_cfg (prepare_ssa_query_graph EN EE g) = g /\
  query_dfs (prepare_ssa_query_graph EN EE g) =
    dfs (prepare EN g) FinSet.empty (Graph.entries g) /\
  query_dom (prepare_ssa_query_graph EN EE g) = dominator_tree (prepare EN g).
Proof.
  intros _; repeat split; reflexivity.
Qed.

(** * Reduced-DAG propagation *)

Local Lemma live_index_set {K V} (EK : encoding K) k j s (m : Map.t K (FinSet.t V)) :
  live_index_get EK k (Map.set EK j s m) =
    if dfs_eq_dec EK k j then s else live_index_get EK k m.
Proof.
  unfold live_index_get; destruct (dfs_eq_dec EK k j) as [Heq|Hne].
  - subst j; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma live_r_edges {N E} (EN : encoding N) (target : E -> N)
    (back : E -> bool) es n (m : Map.t N (FinSet.t N)) u :
  FinSet.mem EN u (fold_right (fun e a => if back e then a else
    FinSet.union EN (live_index_get EN (target e) m) a)
    (FinSet.add EN n FinSet.empty) es) = true <->
  u = n \/ exists e, In e es /\ back e = false /\
    FinSet.mem EN u (live_index_get EN (target e) m) = true.
Proof.
  induction es as [|e es IH]; cbn [fold_right].
  - rewrite FinSet.mem_add, FinSet.mem_empty; split.
    + intros [Heq|Hfalse]; [left; exact Heq|discriminate].
    + intros [Heq|[e [Hfalse _]]]; [left; exact Heq|contradiction].
  - destruct (back e) eqn:Hback.
    + rewrite IH; split.
      * intros [H|[a [Ha Hrest]]]; [left; exact H|].
        right; exists a; split; [right; exact Ha|exact Hrest].
      * intros [H|[a [[Ha|Ha] [Hb Hrest]]]]; [left; exact H|subst a; congruence|].
        right; exists a; auto.
    + rewrite FinSet.mem_union, IH; split.
      * intros [H|[H|[a [Ha Hrest]]]].
        -- right; exists e; split; [left; reflexivity|split; assumption].
        -- left; exact H.
        -- right; exists a; split; [right; exact Ha|exact Hrest].
      * intros [H|[a [[Ha|Ha] [Hb Hrest]]]].
        -- right; left; exact H.
        -- subst a; left; exact Hrest.
        -- right; right; exists a; auto.
Qed.

Local Lemma live_r_exact {N E} (EN : encoding N) (g : Graph.t N E)
    (out : N -> list E) (back : E -> bool) order :
  graph_wf g -> NoDup order ->
  (forall n, In n order -> out n = Graph.out g n) ->
  (forall n e, In n order -> In e (out n) -> back e = false ->
    before order n (Graph.target g e)) ->
  forall n u, In n order ->
  (FinSet.mem EN u (live_index_get EN n
    (live_r_build EN (Graph.target g) out back order)) = true <->
   exists es, path g n es u /\ Forall (fun e => back e = false) es).
Proof.
  intros Hwf Hnd; induction Hnd as [|a ns Hfresh Hnd IH]; intros Hout Horder n u Hn.
  - contradiction.
  - assert (Htail : forall n e, In n ns -> In e (out n) -> back e = false ->
      before ns n (Graph.target g e)).
    { intros v e Hv He Hb; pose proof (Horder v e (or_intror Hv) He Hb) as Hbefore.
      apply dfs_before_cons in Hbefore; destruct Hbefore as [[Heq _]|Hbefore].
      - subst v; contradiction.
      - exact Hbefore. }
    assert (Hchild : forall e, In e (out a) -> back e = false ->
      In (Graph.target g e) ns).
    { intros e He Hb; pose proof (Horder a e (or_introl eq_refl) He Hb) as Hbefore.
      apply dfs_before_cons in Hbefore; destruct Hbefore as [[_ Hin]|Hbefore].
      - exact Hin.
      - destruct Hbefore as [pre [mid [post Heq]]].
        exfalso; apply Hfresh; rewrite Heq; apply in_or_app; right; left; reflexivity. }
    change (live_r_build EN (Graph.target g) out back (a :: ns)) with
      (live_r_row EN (Graph.target g) out back a
        (live_r_build EN (Graph.target g) out back ns)).
    unfold live_r_row; rewrite live_index_set.
    destruct (dfs_eq_dec EN n a) as [Heq|Hne].
    + subst n; rewrite live_r_edges; split.
      * intros [Heq|[e [He [Hb Hu]]]].
        -- subst u; exists []; split; constructor.
        -- apply (IH (fun v Hv => Hout v (or_intror Hv)) Htail
             (Graph.target g e) u (Hchild e He Hb)) in Hu.
           destruct Hu as [es [Hpath Hbacks]].
           exists (e :: es); split.
           ++ pose proof (out_source Hwf a e ltac:(rewrite <- Hout; [exact He|left; reflexivity]))
                as Hsource.
              rewrite <- Hsource; constructor; [rewrite Hsource, <- Hout; auto|exact Hpath].
           ++ constructor; assumption.
      * intros [es [Hpath Hbacks]]; inversion Hpath as [|e tail v He Hpath']; subst.
        -- left; reflexivity.
        -- inversion Hbacks as [|edge rest Hb Hrest]; subst.
           right; exists e; split.
           ++ rewrite Hout by (left; reflexivity); exact He.
           ++ split; [exact Hb|].
              apply (IH (fun v Hv => Hout v (or_intror Hv)) Htail
                (Graph.target g e) u).
              ** apply Hchild; [rewrite Hout by (left; reflexivity); exact He|exact Hb].
              ** exists tail; auto.
    + apply IH; [intros v Hv; apply Hout; right; exact Hv|exact Htail|].
      destruct Hn as [Heq|Hin]; [symmetry in Heq; contradiction|exact Hin].
Qed.

Local Lemma live_tabulate_get {K V} (EK : encoding K) (f : K -> V) ns k :
  Map.get EK k (live_tabulate EK f ns) =
    if in_dec (dfs_eq_dec EK) k ns then Some (f k) else None.
Proof.
  induction ns as [|a ns IH].
  - apply Map.get_empty.
  - change (live_tabulate EK f (a :: ns)) with
      (Map.set EK a (f a) (live_tabulate EK f ns)).
    destruct (dfs_eq_dec EK k a) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same; destruct (in_dec (dfs_eq_dec EK) k (k :: ns));
        [reflexivity|exfalso; apply n; left; reflexivity].
    + rewrite Map.get_set_other by exact Hne; rewrite IH.
      destruct (in_dec (dfs_eq_dec EK) k ns) as [Hin|Hnot];
        destruct (in_dec (dfs_eq_dec EK) k (a :: ns)) as [Hin'|Hnot']; try reflexivity.
      * exfalso; apply Hnot'; right; exact Hin.
      * exfalso; destruct Hin' as [Heq|Hin]; [apply Hne; symmetry; exact Heq|contradiction].
Qed.

Local Lemma live_r_wf {N E} (EN : encoding N) (target : E -> N)
    (out : N -> list E) (back : E -> bool) order :
  forall n, FinSet.wf EN
    (live_index_get EN n (live_r_build EN target out back order)).
Proof.
  induction order as [|a ns IH]; intro n.
  - unfold live_r_build, live_index_get; cbn [fold_right].
    rewrite Map.get_empty; apply Map.wf_empty.
  - change (live_r_build EN target out back (a :: ns)) with
      (live_r_row EN target out back a (live_r_build EN target out back ns)).
    unfold live_r_row; rewrite live_index_set; destruct (dfs_eq_dec EN n a) as [Heq|Hne].
    + induction (out a) as [|e es IHe].
      * apply Map.wf_set; apply Map.wf_empty.
      * cbn [fold_right]; destruct (back e); [exact IHe|].
        apply FinSet.wf_union; [apply IH|exact IHe].
    + apply IH.
Qed.

Local Lemma live_set_path {N E} (g : Graph.t N E) roots n es u :
  path (set_entries g roots) n es u <-> path g n es u.
Proof.
  split.
  - intro Hpath; induction Hpath as [v|e es v He Hpath IH].
    + apply path_nil.
    + exact (@path_cons N E g e es v He IH).
  - intro Hpath; induction Hpath as [v|e es v He Hpath IH].
    + apply path_nil.
    + exact (@path_cons N E (set_entries g roots) e es v He IH).
Qed.

Section GraphAgreement.
Context {N E : Type} (EN : encoding N) (g : Graph.t N E).
Local Abbreviation p := (prepare EN g).
Local Abbreviation r := (dfs p FinSet.empty (Graph.entries g)).
Local Abbreviation back := (fun e => ancestor_b EN r (Graph.target g e) (Graph.source g e)).
Local Abbreviation rm := (live_r_build EN (Graph.target g) (succ_edges p) back (rpo r)).
Hypothesis Hready : ready EN g p.

Local Lemma live_pre_reachable n : In n (preorder r) <-> reachable g n.
Proof.
  destruct (dfs_exact EN g p n (Graph.entries g) FinSet.empty Hready
    (entries_in (proj1 Hready))) as [_ [_ [_ Hin]]].
  rewrite Hin; apply reachable_dfs; exact Hready.
Qed.

Local Lemma live_rpo_reachable n : In n (rpo r) <-> reachable g n.
Proof.
  unfold rpo; rewrite <- in_rev.
  destruct (dfs_exact EN g p n (Graph.entries g) FinSet.empty Hready
    (entries_in (proj1 Hready))) as [_ [_ [Hperm _]]].
  rewrite <- live_pre_reachable; split.
  - intro Hin; eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
  - intro Hin; eapply Permutation_in; [exact Hperm|exact Hin].
Qed.

Local Lemma live_back_agrees e : reachable g (Graph.source g e) ->
  In e (Graph.out g (Graph.source g e)) ->
  (back e = true <-> retreating EN g r e).
Proof.
  intros Hsource He; apply ancestor_b_agrees; try exact Hready.
  - exact (entries_in (proj1 Hready)).
  - apply reachable_dfs; [exact Hready|eapply reachable_step; eassumption].
  - apply reachable_dfs; assumption.
Qed.

Local Lemma live_boolean_path n es u : path g n es u -> reachable g n ->
  (Forall (fun e => back e = false) es <-> Forall (fun e => ~ retreating EN g r e) es).
Proof.
  intro Hpath; induction Hpath as [n|e es u He Hpath IH]; intro Hn.
  - split; intro H; constructor.
  - rewrite !Forall_cons_iff, (IH (reachable_step e Hn He)).
    rewrite <- (live_back_agrees e Hn He), Bool.not_true_iff_false; reflexivity.
Qed.

Local Lemma live_reduced_agrees n u : reachable g n ->
  (FinSet.mem EN u (live_index_get EN n rm) = true <-> reduced_path EN g r n u).
Proof.
  intro Hn; unfold reduced_path.
  rewrite (live_r_exact EN g (succ_edges p) back (rpo r) (proj1 Hready)).
  - split; intros [es [Hpath Hbacks]]; exists es; split; [exact Hpath| |exact Hpath|].
    + apply (live_boolean_path n es u Hpath Hn); exact Hbacks.
    + apply (live_boolean_path n es u Hpath Hn); exact Hbacks.
  - apply dfs_rpo_nodup; [exact Hready|exact (entries_in (proj1 Hready))].
  - intros a Ha; apply succ_agrees; [exact (proj2 (proj2 Hready))|].
    apply reachable_in_nodes; [exact (proj1 Hready)|apply live_rpo_reachable; exact Ha].
  - intros a e Ha He Hb.
    assert (Hreach : reachable g a) by (apply live_rpo_reachable; exact Ha).
    rewrite (succ_agrees (proj2 (proj2 Hready)) a
      (reachable_in_nodes g a (proj1 Hready) Hreach)) in He.
    pose proof (out_source (proj1 Hready) a e He) as Hsource; subst a.
    destruct (rpo_edge_classes EN g p (Graph.entries g) Hready
      (entries_in (proj1 Hready)) e
      (proj2 (reachable_dfs EN g p (Graph.source g e) Hready) Hreach) He) as [Horder|Hback].
    + exact Horder.
    + apply (live_back_agrees e Hreach He) in Hback; congruence.
  - apply live_rpo_reachable; exact Hn.
Qed.

Local Lemma live_path_reachable n es u : path g n es u -> reachable g n -> reachable g u.
Proof.
  intro Hpath; induction Hpath as [n|e es u He Hpath IH]; intro Hn.
  - exact Hn.
  - apply IH; eapply reachable_step; eassumption.
Qed.

Local Lemma live_rt_step_reachable n u : reachable g n -> rt_step EN g r n u -> reachable g u.
Proof.
  intros Hn [_ [a [e [[es [Hpath _]] [He [Hu _]]]]]].
  rewrite <- Hu; apply (reachable_step e).
  - rewrite (out_source (proj1 Hready) a e He).
    eapply live_path_reachable; eassumption.
  - rewrite (out_source (proj1 Hready) a e He); exact He.
Qed.

Local Lemma live_t_edges_agrees n u : reachable g n ->
  (FinSet.mem EN u (live_t_edges EN g (succ_edges p) back rm n) = true <->
    rt_step EN g r n u).
Proof.
  intro Hn; unfold live_t_edges; rewrite FinSet.of_list_spec, in_flat_map; split.
  - intros [a [Ha Hu]]; apply in_map_iff in Hu.
    destruct Hu as [e [Hu He]]; apply filter_In in He; destruct He as [He Hb].
    apply andb_true_iff in Hb; destruct Hb as [Hb Hfree]; apply negb_true_iff in Hfree.
    apply (FinSet.elements_spec EN) in Ha; [|apply live_r_wf].
    apply live_reduced_agrees in Ha; [|exact Hn].
    destruct Ha as [es [Hpath Hbacks]].
    assert (Ha : reachable g a) by (eapply live_path_reachable; eassumption).
    rewrite (succ_agrees (proj2 (proj2 Hready)) a
      (reachable_in_nodes g a (proj1 Hready) Ha)) in He.
    split.
    + intro Hreduced; apply live_reduced_agrees in Hreduced; [|exact Hn].
      rewrite Hu in Hfree; congruence.
    + exists a, e; split; [exists es; auto|split; [exact He|split; [exact Hu|]]].
      apply live_back_agrees.
      * rewrite (out_source (proj1 Hready) a e He); exact Ha.
      * rewrite (out_source (proj1 Hready) a e He); exact He.
      * exact Hb.
  - intros [Hnot [a [e [Ha [He [Hu Hb]]]]]]; exists a; split.
    + apply (FinSet.elements_spec EN); [apply live_r_wf|].
      apply live_reduced_agrees; assumption.
    + apply in_map_iff; exists e; split; [exact Hu|apply filter_In; split].
      * rewrite (succ_agrees (proj2 (proj2 Hready))); [exact He|].
        apply reachable_in_nodes; [exact (proj1 Hready)|].
        destruct Ha as [es [Hpath _]]; eapply live_path_reachable; eassumption.
      * apply andb_true_iff; split.
        -- apply live_back_agrees; [|rewrite (out_source (proj1 Hready) a e He); exact He|].
           ++ rewrite (out_source (proj1 Hready) a e He).
              destruct Ha as [es [Hpath _]]; eapply live_path_reachable; eassumption.
           ++ exact Hb.
        -- apply negb_true_iff; rewrite Hu; apply Bool.not_true_iff_false.
           intro Hmem; apply Hnot; apply live_reduced_agrees; assumption.
Qed.

Local Abbreviation tg := (live_t_graph EN g (succ_edges p) back rm (preorder r)).

Local Lemma live_t_out n : Graph.out tg n =
  if in_dec (dfs_eq_dec EN) n (preorder r) then
    map (fun v => (n, v)) (FinSet.elements (live_t_edges EN g (succ_edges p) back rm n))
  else [].
Proof.
  unfold live_t_graph; cbn [Graph.out]; rewrite live_tabulate_get.
  destruct (in_dec (dfs_eq_dec EN) n (preorder r)); reflexivity.
Qed.

Local Lemma live_t_out_source n edge : In edge (Graph.out tg n) -> fst edge = n.
Proof.
  rewrite live_t_out; destruct (in_dec (dfs_eq_dec EN) n (preorder r)) as [Hin|Hnot].
  - intro Hedge; apply in_map_iff in Hedge; destruct Hedge as [v [<- _]]; reflexivity.
  - contradiction.
Qed.

Local Lemma live_t_out_agrees n u : reachable g n ->
  (In (n, u) (Graph.out tg n) <-> rt_step EN g r n u).
Proof.
  intro Hn; rewrite live_t_out.
  destruct (in_dec (dfs_eq_dec EN) n (preorder r)) as [Hin|Hnot].
  - rewrite in_map_iff; split.
    + intros [v [Heq Hv]]; inversion Heq; subst v.
      apply live_t_edges_agrees; [exact Hn|].
      apply (FinSet.elements_spec EN); [apply FinSet.wf_fold_add; apply Map.wf_empty|exact Hv].
    + intro Hstep; exists u; split; [reflexivity|].
      apply (FinSet.elements_spec EN); [apply FinSet.wf_fold_add; apply Map.wf_empty|].
      apply live_t_edges_agrees; assumption.
  - exfalso; apply Hnot; apply live_pre_reachable; exact Hn.
Qed.

Local Lemma live_t_ready : ready EN tg (prepare EN tg).
Proof.
  apply prepare_ready.
  - constructor.
    + change (NoDup (preorder r)); destruct (preorder r) as [|n ns] eqn:Hpre.
      * constructor.
      * destruct (dfs_exact EN g p n (Graph.entries g) FinSet.empty Hready
          (entries_in (proj1 Hready))) as [_ [Hnd _]].
        rewrite Hpre in Hnd; exact Hnd.
    + intros n Hin; contradiction.
    + intros n edge He; apply live_t_out_source; exact He.
    + intros n [a u] Hn He; cbn [Graph.target].
      pose proof (live_t_out_source n (a, u) He) as Ha; cbn in Ha; subst a.
      apply live_pre_reachable; eapply live_rt_step_reachable.
      * apply live_pre_reachable; exact Hn.
      * apply live_t_out_agrees; [apply live_pre_reachable; exact Hn|exact He].
  - intro n; rewrite live_t_out; destruct (in_dec (dfs_eq_dec EN) n (preorder r)).
    + apply nodup_map_injective.
      * intros u v Heq; inversion Heq; reflexivity.
      * apply (FinSet.elements_nodup EN); apply FinSet.wf_fold_add; apply Map.wf_empty.
    + constructor.
Qed.

Local Lemma live_t_path n es u : path tg n es u -> reachable g n ->
  rt_reaches EN g r n u /\ reachable g u.
Proof.
  intro Hpath; induction Hpath as [n|[a b] es u He Hpath IH]; intro Hn.
  - split; [constructor 2|exact Hn].
  - cbn [Graph.source Graph.target] in *.
    pose proof (proj1 (live_t_out_agrees a b Hn) He) as Hstep.
    destruct (IH (live_rt_step_reachable a b Hn Hstep)) as [Hclosure Hu].
    split; [|exact Hu].
    eapply Relation_Operators.rt_trans; [constructor 1; exact Hstep|exact Hclosure].
Qed.

Local Lemma live_t_path_complete n u : rt_reaches EN g r n u -> reachable g n ->
  exists es, path tg n es u.
Proof.
  intro Hclosure; induction Hclosure as [n u Hstep|n|n v u Hnv IHnv Hvu IHvu]; intro Hn.
  - exists [(n, u)]; apply (@path_cons N (N * N) tg (n, u) [] u).
    + apply live_t_out_agrees; assumption.
    + constructor.
  - exists []; constructor.
  - destruct (IHnv Hn) as [es Hpath].
    destruct (live_t_path n es v Hpath Hn) as [_ Hv].
    destruct (IHvu Hv) as [fs Htail]; exists (es ++ fs).
    eapply reducible_path_app; eassumption.
Qed.

Local Lemma live_t_closure_agrees n u : reachable g n ->
  (FinSet.mem EN u (visited (dfs (prepare EN tg) FinSet.empty [n])) = true <->
    rt_reaches EN g r n u).
Proof.
  intro Hn.
  destruct (dfs_exact EN tg (prepare EN tg) u [n] FinSet.empty live_t_ready
    ltac:(intros a [<-|Hfalse]; [apply live_pre_reachable; exact Hn|contradiction]))
    as [Hex _].
  rewrite Hex, dfs_empty_reachable, reachable_iff_path; split.
  - intros [a [es [[Ha|Hfalse] Hpath]]]; [subst a|contradiction].
    apply live_set_path in Hpath; exact (proj1 (live_t_path n es u Hpath Hn)).
  - intro Hclosure; destruct (live_t_path_complete n u Hclosure Hn) as [es Hpath].
    exists n, es; split; [left; reflexivity|].
    apply live_set_path; exact Hpath.
Qed.

Local Lemma live_t_pre_agrees n u : reachable g n ->
  (FinSet.mem EN u (FinSet.of_list EN (preorder (dfs (prepare EN tg) FinSet.empty [n]))) =
    true <-> rt_reaches EN g r n u).
Proof.
  intro Hn; rewrite FinSet.of_list_spec.
  destruct (dfs_exact EN tg (prepare EN tg) u [n] FinSet.empty live_t_ready
    ltac:(intros a [<-|Hfalse]; [apply live_pre_reachable; exact Hn|contradiction]))
    as [_ [_ [_ Hin]]].
  rewrite Hin; apply live_t_closure_agrees; exact Hn.
Qed.

End GraphAgreement.

(** R and T are exactly reduced reachability and the specified back-target closure. *)
Theorem ssa_query_graph_agrees {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) :
  ready EN g (prepare EN g) ->
  (exists entry, Graph.entries g = [entry]) ->
  forall n u, reachable g n -> reachable g u ->
    (FinSet.mem EN u (live_index_get EN n
      (query_reduced (prepare_ssa_query_graph EN EE g))) = true <->
      reduced_path EN g (query_dfs (prepare_ssa_query_graph EN EE g)) n u) /\
    (FinSet.mem EN u (live_index_get EN n
      (query_back_closure (prepare_ssa_query_graph EN EE g))) = true <->
      rt_reaches EN g (query_dfs (prepare_ssa_query_graph EN EE g)) n u).
Proof.
  intros Hready _ n u Hn _; split.
  - apply live_reduced_agrees; assumption.
  - unfold prepare_ssa_query_graph; cbn [query_back_closure query_dfs].
    unfold live_index_get; rewrite live_tabulate_get.
    destruct (in_dec (dfs_eq_dec EN) n
      (preorder (dfs (prepare EN g) FinSet.empty (Graph.entries g)))) as [Hin|Hnot].
    + apply live_t_pre_agrees; assumption.
    + exfalso; apply Hnot; apply live_pre_reachable; assumption.
Qed.

(** * Separate value indexes *)

Local Lemma live_value_add_mem {N V} (EN : encoding N) (EV : encoding V)
    n x k y m :
  FinSet.mem EN k (live_index_get EV y (live_value_add EN EV n x m)) = true <->
    (y = x /\ k = n) \/ FinSet.mem EN k (live_index_get EV y m) = true.
Proof.
  unfold live_value_add; rewrite live_index_set.
  destruct (dfs_eq_dec EV y x) as [Heq|Hne].
  - subst y; rewrite FinSet.mem_add; tauto.
  - tauto.
Qed.

Local Lemma live_value_row_mem {N V} (EN : encoding N) (EV : encoding V)
    n xs m k y :
  FinSet.mem EN k (live_index_get EV y
    (fold_right (live_value_add EN EV n) m xs)) = true <->
    (k = n /\ In y xs) \/ FinSet.mem EN k (live_index_get EV y m) = true.
Proof.
  induction xs as [|x xs IH]; cbn [fold_right In].
  - tauto.
  - rewrite live_value_add_mem, IH; intuition congruence.
Qed.

Local Lemma live_value_uses_mem {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) ns n x :
  FinSet.mem EN n (live_index_get EV x (live_value_uses EN EV p ns)) = true <->
    In n ns /\ point_use_at p n x.
Proof.
  induction ns as [|a ns IH].
  - unfold live_value_uses, live_index_get; cbn [fold_right].
    rewrite Map.get_empty, FinSet.mem_empty; cbn [In]; split; [discriminate|tauto].
  - change (live_value_uses EN EV p (a :: ns)) with
      (fold_right (live_value_add EN EV a) (live_value_uses EN EV p ns) (live_point_vars p a)).
    rewrite live_value_row_mem, IH.
    assert (Hvars : In x (live_point_vars p a) <-> point_use_at p a x).
    { unfold live_point_vars, point_use_at; rewrite in_app_iff, in_flat_map; reflexivity. }
    rewrite Hvars; cbn [In]; intuition congruence.
Qed.

Local Lemma live_value_uses_wf {N E V} (EN : encoding N) (EV : encoding V)
    (p : point_uses N E V) ns :
  Map.wf EV (live_value_uses EN EV p ns) /\
  forall x, FinSet.wf EN (live_index_get EV x (live_value_uses EN EV p ns)).
Proof.
  assert (Hrow : forall n xs m, Map.wf EV m ->
    (forall x, FinSet.wf EN (live_index_get EV x m)) ->
    Map.wf EV (fold_right (live_value_add EN EV n) m xs) /\
    forall x, FinSet.wf EN (live_index_get EV x
      (fold_right (live_value_add EN EV n) m xs))).
  { intros n xs; induction xs as [|a xs IH]; intros m Hm Hsets; cbn [fold_right].
    - auto.
    - destruct (IH m Hm Hsets) as [Hmap Hss]; split.
      + apply Map.wf_set; exact Hmap.
      + intro x; unfold live_value_add; rewrite live_index_set.
        destruct (dfs_eq_dec EV x a) as [Heq|Hne]; [apply Map.wf_set|]; apply Hss. }
  induction ns as [|a ns [IHmap IHsets]].
  - split; [apply Map.wf_empty|].
    intro x; unfold live_value_uses, live_index_get; cbn [fold_right].
    rewrite Map.get_empty; apply Map.wf_empty.
  - apply Hrow; assumption.
Qed.

Local Lemma live_value_defs_get {N V A} (EV : encoding V) (home : V -> option N)
    (bindings : list (V * A)) x d :
  Map.get EV x (live_value_defs EV home bindings) = Some d <->
    In x (map fst bindings) /\ home x = Some d.
Proof.
  induction bindings as [|[y a] rest IH].
  - unfold live_value_defs; cbn [fold_right map]; rewrite Map.get_empty; split;
      [discriminate|intros [Hfalse _]; contradiction].
  - change (live_value_defs EV home ((y, a) :: rest)) with
      (match home y with
       | Some v => Map.set EV y v (live_value_defs EV home rest)
       | None => live_value_defs EV home rest
       end).
    cbn [map fst In]; destruct (home y) as [v|] eqn:Hy.
    + destruct (dfs_eq_dec EV x y) as [Heq|Hne].
      * subst y; rewrite Map.get_set_same, Hy; split.
        -- intro Heq; split; [left; reflexivity|exact Heq].
        -- intros [_ Heq]; exact Heq.
      * rewrite Map.get_set_other by exact Hne; rewrite IH; intuition congruence.
    + rewrite IH; split.
      * intros [Hin Hhome]; auto.
      * intros [[Heq|Hin] Hhome]; [subst y; congruence|auto].
Qed.

Local Lemma live_value_definition {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) (Hlaws : ssa_point_laws s)
    (Hssa : reachable_point_ssa s) n x :
  reachable (live_graph (point_model s)) n -> point_use_at (point_model s) n x ->
  Map.get EV x (query_def (prepare_ssa_query_values EN EV s)) = point_definition s x.
Proof.
  intros Hn Huse.
  destruct (point_ssa_uses_defined Hssa n x Hn Huse) as [d [Hhome _]].
  rewrite Hhome; apply live_value_defs_get; split; [|exact Hhome].
  pose proof (prepare_ready EN (live_graph (point_model s))
    (points_graph_wf Hlaws) (points_out_nodup Hlaws)) as Hready.
  set (ns := preorder (dfs (prepare EN (live_graph (point_model s))) FinSet.empty
    (Graph.entries (live_graph (point_model s))))) in *.
  assert (Hmem : FinSet.mem EN n (live_index_get EV x
    (live_value_uses EN EV (point_model s) ns)) = true).
  { apply live_value_uses_mem; split; [apply live_pre_reachable; assumption|exact Huse]. }
  unfold live_index_get in Hmem.
  destruct (Map.get EV x (live_value_uses EN EV (point_model s) ns)) as [us|] eqn:Hget.
  - apply in_map_iff; exists (x, us); split; [reflexivity|].
    apply (Map.elements_complete EV).
    + exact (proj1 (live_value_uses_wf EN EV (point_model s) ns)).
    + exact Hget.
  - rewrite FinSet.mem_empty in Hmem; discriminate.
Qed.

(** Value preparation records exactly reachable uses and their selected static definitions. *)
Theorem ssa_query_values_agree {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  forall n x, reachable (live_graph (point_model s)) n ->
    (FinSet.mem EN n (live_index_get EV x
      (query_uses (prepare_ssa_query_values EN EV s))) = true <->
      point_use_at (point_model s) n x) /\
    (point_use_at (point_model s) n x ->
      Map.get EV x (query_def (prepare_ssa_query_values EN EV s)) = point_definition s x).
Proof.
  intros Hlaws Hssa n x Hn; split.
  - change (FinSet.mem EN n (live_index_get EV x
      (live_value_uses EN EV (point_model s) (preorder
        (dfs (prepare EN (live_graph (point_model s))) FinSet.empty
          (Graph.entries (live_graph (point_model s))))))) = true <->
      point_use_at (point_model s) n x).
    rewrite live_value_uses_mem; split; [tauto|intro Huse; split; [|exact Huse]].
    apply live_pre_reachable; [apply prepare_ready; [apply points_graph_wf|apply points_out_nodup];
      exact Hlaws|exact Hn].
  - apply live_value_definition; assumption.
Qed.

(** * Dominated paths and R/T *)

Local Definition live_avoiding {N E} (g : Graph.t N E) (d n u : N) : Prop :=
  exists es, path g n es u /\ n <> d /\
    Forall (fun e => Graph.target g e <> d) es.

Local Lemma live_avoiding_app {N E} (g : Graph.t N E) d n t u :
  live_avoiding g d n t -> live_avoiding g d t u -> live_avoiding g d n u.
Proof.
  intros [es [Hpath [Hn Htargets]]] [fs [Htail [_ Htailtargets]]].
  exists (es ++ fs); split; [eapply reducible_path_app; eassumption|].
  split; [exact Hn|apply Forall_app; auto].
Qed.

Local Lemma live_avoiding_dom {N E} (g : Graph.t N E) d n u :
  live_avoiding g d n u -> dominates g d u -> dominates g d n.
Proof.
  intros [es [Hpath [Hn Htargets]]] Hdom root pre Hroot Hpre.
  destruct (Hdom root (pre ++ es) Hroot (reducible_path_app g root pre n es u Hpre Hpath))
    as [Heq|[e [Hin Heq]]].
  - left; exact Heq.
  - apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + right; exists e; auto.
    + exfalso; apply Forall_forall with (x := e) in Htargets; [contradiction|exact Hin].
Qed.

Local Lemma live_reduced_app {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) n t u :
  reduced_path EN g r n t -> reduced_path EN g r t u -> reduced_path EN g r n u.
Proof.
  intros [es [Hpath Hbacks]] [fs [Htail Htailbacks]]; exists (es ++ fs); split.
  - eapply reducible_path_app; eassumption.
  - apply Forall_app; auto.
Qed.

Section DominatedPaths.
Context {N E : Type} (EN : encoding N) (g : Graph.t N E).
Local Abbreviation p := (prepare EN g).
Local Abbreviation r := (dfs p FinSet.empty (Graph.entries g)).
Hypothesis Hready : ready EN g p.

Local Lemma live_tree_reduced d u : reachable g u -> dominates g d u -> reduced_path EN g r d u.
Proof.
  intros Hu Hdom.
  pose proof (reducible_dominates_ancestor EN g p d u Hready Hu Hdom) as Hanc.
  destruct (reducible_ancestor_path EN g p d u Hready Hanc) as [es [Hpath Htree]].
  exists es; split; [exact Hpath|apply Forall_forall; intros e He Hback].
  destruct (reducible_parent EN g p (Graph.target g e) e Hready (Htree e He))
    as [_ [_ [a [b [Ha [Hb Hlt]]]]]].
  destruct (reducible_ancestor_rank EN g p (Graph.target g e) (Graph.source g e)
    Hready Hback b Hb) as [c [Hc Hle]].
  rewrite Ha in Hc; inversion Hc; subst c.
  apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; lia.
Qed.

Local Lemma live_reduced_cycle n : reachable g n ->
  forall es, path g n es n -> Forall (fun e => ~ retreating EN g r e) es -> es = [].
Proof.
  intros Hn es Hpath Hbacks; destruct es as [|e es]; [reflexivity|].
  exfalso; destruct (cycle_has_retreating_edge EN g p n (e :: es) (Graph.entries g)
    Hready (entries_in (proj1 Hready))
    (proj2 (reachable_dfs EN g p n Hready) Hn) ltac:(discriminate) Hpath)
    as [a [Ha Hback]].
  rewrite Forall_forall in Hbacks; exact (Hbacks a Ha Hback).
Qed.

Local Lemma live_reduced_no_return d n : reachable g n -> strictly_dominates g d n ->
  ~ reduced_path EN g r n d.
Proof.
  intros Hn [Hdom Hne] [es [Hpath Hbacks]].
  destruct (live_tree_reduced d n Hn Hdom) as [fs [Htail Htailbacks]].
  assert (Hcycle : path g n (es ++ fs) n) by (eapply reducible_path_app; eassumption).
  assert (Hfree : Forall (fun e => ~ retreating EN g r e) (es ++ fs)).
  { apply Forall_app; auto. }
  pose proof (live_reduced_cycle n Hn (es ++ fs) Hcycle Hfree) as Hnil.
  apply app_eq_nil in Hnil; destruct Hnil as [Hnil _]; subst es.
  inversion Hpath; subst; apply Hne; reflexivity.
Qed.

Local Lemma live_reduced_prefix n es u a : path g n es u ->
  Forall (fun e => ~ retreating EN g r e) es -> In a es ->
  reduced_path EN g r n (Graph.target g a).
Proof.
  intros Hpath Hbacks Ha.
  destruct (path_prefix_target g n es u a Hpath Ha) as [pre [Hpre Hsub]].
  exists pre; split; [exact Hpre|].
  apply Forall_forall; intros e He; apply Forall_forall with (x := e) in Hbacks;
    [exact Hbacks|apply Hsub; exact He].
Qed.

Local Lemma live_reduced_avoiding d n u : reachable g n -> strictly_dominates g d n ->
  reduced_path EN g r n u -> live_avoiding g d n u.
Proof.
  intros Hn Hstrict [es [Hpath Hbacks]]; exists es; split; [exact Hpath|].
  split; [intro Heq; apply (proj2 Hstrict); symmetry; exact Heq|].
  apply Forall_forall; intros e He Heq.
  apply (live_reduced_no_return d n Hn Hstrict).
  rewrite <- Heq; eapply live_reduced_prefix; eassumption.
Qed.

Local Lemma live_rt_step_avoiding d n u : reachable g n -> strictly_dominates g d u ->
  rt_step EN g r n u -> live_avoiding g d n u /\ strictly_dominates g d n.
Proof.
  intros Hn [Hdom Hne] [Hnot [a [e [[es [Hpath Hbacks]] [He [Hu Hback]]]]]].
  assert (HuReach : reachable g u).
  { eapply live_rt_step_reachable; [exact Hready|exact Hn|].
    split; [exact Hnot|exists a, e; split; [exists es; auto|auto]]. }
  pose proof (live_tree_reduced d u HuReach Hdom) as Hdu.
  assert (Hnfree : n <> d).
  { intro Heq; subst n; apply Hnot; exact Hdu. }
  assert (Htargets : Forall (fun edge => Graph.target g edge <> d) es).
  { apply Forall_forall; intros edge Hin Heq; apply Hnot.
    eapply live_reduced_app with (t := d).
    - rewrite <- Heq; eapply live_reduced_prefix; eassumption.
    - exact Hdu. }
  assert (Havoid : live_avoiding g d n u).
  { exists (es ++ [e]); split.
    - rewrite <- Hu; eapply path_snoc; [exact Hpath| |exact He].
      symmetry; exact (out_source (proj1 Hready) a e He).
    - split; [exact Hnfree|apply Forall_app; split; [exact Htargets|]].
      constructor; [rewrite Hu; intro Heq; apply Hne; symmetry; exact Heq|constructor]. }
  split; [exact Havoid|split].
  - eapply live_avoiding_dom; eassumption.
  - intro Heq; apply Hnfree; symmetry; exact Heq.
Qed.

Local Lemma live_rt_reachable n u : rt_reaches EN g r n u -> reachable g n -> reachable g u.
Proof.
  intro Hclosure; induction Hclosure; intro Hn.
  - eapply live_rt_step_reachable; eassumption.
  - exact Hn.
  - apply IHHclosure2; apply IHHclosure1; exact Hn.
Qed.

Local Lemma live_rt_avoiding d n u : rt_reaches EN g r n u -> reachable g n ->
  strictly_dominates g d u -> live_avoiding g d n u /\ strictly_dominates g d n.
Proof.
  intro Hclosure; induction Hclosure as [n u Hstep|n|n t u Hnt IHnt Htu IHtu];
    intros Hn Hstrict.
  - apply live_rt_step_avoiding; assumption.
  - split; [exists []; split; [constructor|split; [|constructor]]|exact Hstrict].
    intro Heq; apply (proj2 Hstrict); symmetry; exact Heq.
  - destruct (IHtu (live_rt_reachable n t Hnt Hn) Hstrict) as [Htail Ht].
    destruct (IHnt Hn Ht) as [Hprefix Hstart]; split; [|exact Hstart].
    eapply live_avoiding_app; eassumption.
Qed.

Local Lemma live_strict_decompose n es u : path g n es u ->
  forall d start t, reachable g start -> rt_reaches EN g r start t ->
  reduced_path EN g r t n -> strictly_dominates g d t ->
  Forall (fun e => strictly_dominates g d (Graph.target g e)) es ->
  exists v, rt_reaches EN g r start v /\ strictly_dominates g d v /\ reduced_path EN g r v u.
Proof.
  intro Hpath; induction Hpath as [n|e es u He Hpath IH];
    intros d start t Hstart Hst Htn Hstrict Htargets.
  - exists t; auto.
  - inversion Htargets as [|edge rest Hnext Hrest]; subst.
    assert (Ht : reachable g t) by (eapply live_rt_reachable; eassumption).
    assert (Hn : reachable g (Graph.source g e)).
    { destruct Htn as [pre [Hpre _]]; eapply live_path_reachable; eassumption. }
    destruct (ancestor_b EN r (Graph.target g e) (Graph.source g e)) eqn:Hback.
    + destruct (FinSet.mem EN (Graph.target g e) (live_index_get EN t
        (live_r_build EN (Graph.target g) (succ_edges p)
          (fun edge => ancestor_b EN r (Graph.target g edge) (Graph.source g edge)) (rpo r))))
        eqn:Hreduced.
      * apply (live_reduced_agrees EN g Hready t (Graph.target g e) Ht) in Hreduced.
        eapply IH; eassumption.
      * eapply IH with (t := Graph.target g e).
        -- exact Hstart.
        -- eapply Relation_Operators.rt_trans; [exact Hst|constructor 1].
           split.
           ++ intro Hreduced'; apply (live_reduced_agrees EN g Hready t (Graph.target g e) Ht)
                in Hreduced'; congruence.
           ++ exists (Graph.source g e), e; split; [exact Htn|split; [exact He|split]].
              ** reflexivity.
              ** apply (live_back_agrees EN g Hready e Hn He); exact Hback.
        -- exists []; split; constructor.
        -- exact Hnext.
        -- exact Hrest.
    + eapply IH; [exact Hstart|exact Hst| |exact Hstrict|exact Hrest].
      eapply live_reduced_app; [exact Htn|exists [e]; split].
      * constructor; [exact He|constructor].
      * constructor; [|constructor]; intro Hretreat.
        apply (live_back_agrees EN g Hready e Hn He) in Hretreat; congruence.
Qed.

End DominatedPaths.

(** * Strict SSA liveness paths *)

Section SsaPaths.
Context {B BE N E V : Type} (s : ssa_points B BE N E V).
Local Abbreviation g := (live_graph (point_model s)).
Hypothesis Hlaws : ssa_point_laws s.
Hypothesis Hssa : reachable_point_ssa s.

Local Lemma live_home_use d n x : point_definition s x = Some d -> reachable g n ->
  point_use_at (point_model s) n x -> strictly_dominates g d n.
Proof.
  intros Hhome Hn Huse.
  destruct (point_ssa_uses_defined Hssa n x Hn Huse) as [a [Ha [_ Hstrict]]].
  rewrite Hhome in Ha; inversion Ha; subst a; exact Hstrict.
Qed.

Local Lemma live_syntactic_strict x n : syntactic_live (point_model s) x n ->
  forall d, point_definition s x = Some d -> reachable g n -> strictly_dominates g d n.
Proof.
  intro Hlive; induction Hlive as [n Hexit|n e He Huse|n e He Hkill Hlive IH];
    intros d Hhome Hn.
  - eapply live_home_use; [exact Hhome|exact Hn|left; exact Hexit].
  - eapply live_home_use; [exact Hhome|exact Hn|right; exists e; auto].
  - pose proof (out_source (points_graph_wf Hlaws) n e He) as Hsource.
    assert (Htarget : reachable g (Graph.target g e)).
    { apply (reachable_step e); [rewrite Hsource; exact Hn|rewrite Hsource; exact He]. }
    destruct (IH d Hhome Htarget) as [Hdom Hne].
    assert (Hnfree : n <> d).
    { intro Heq; apply Hkill; apply (point_ssa_home_kills Hssa x d e Hhome).
      - rewrite <- Heq; exact Hn.
      - rewrite <- Heq; exact He. }
    split.
    + eapply live_avoiding_dom; [|exact Hdom].
      exists [e]; split.
      * rewrite <- Hsource; constructor; [rewrite Hsource; exact He|constructor].
      * split; [exact Hnfree|constructor; [intro Heq; apply Hne; symmetry; exact Heq|constructor]].
    + intro Heq; apply Hnfree; symmetry; exact Heq.
Qed.

Local Lemma live_syntactic_path x n : syntactic_live (point_model s) x n ->
  forall d, point_definition s x = Some d -> reachable g n ->
  exists u es, path g n es u /\
    Forall (fun e => strictly_dominates g d (Graph.target g e)) es /\
    point_use_at (point_model s) u x.
Proof.
  intro Hlive; induction Hlive as [n Hexit|n e He Huse|n e He Hkill Hlive IH];
    intros d Hhome Hn.
  - exists n, []; split; [constructor|split; [constructor|left; exact Hexit]].
  - exists n, []; split; [constructor|split; [constructor|right; exists e; auto]].
  - pose proof (out_source (points_graph_wf Hlaws) n e He) as Hsource.
    assert (Htarget : reachable g (Graph.target g e)).
    { apply (reachable_step e); [rewrite Hsource; exact Hn|rewrite Hsource; exact He]. }
    destruct (IH d Hhome Htarget) as [u [es [Hpath [Htargets Huse]]]].
    exists u, (e :: es); split.
    + rewrite <- Hsource; constructor; [rewrite Hsource; exact He|exact Hpath].
    + split; [constructor; [eapply live_syntactic_strict; eassumption|exact Htargets]|exact Huse].
Qed.

Local Lemma live_avoiding_syntactic d x n u : point_definition s x = Some d ->
  reachable g n -> live_avoiding g d n u -> point_use_at (point_model s) u x ->
  syntactic_live (point_model s) x n.
Proof.
  intros Hhome Hn [es [Hpath [Hfree Htargets]]] Huse.
  revert Hn Hfree Htargets; induction Hpath as [n|e es u He Hpath IH];
    intros Hn Hfree Htargets.
  - destruct Huse as [Hexit|[e [He Huse]]].
    + apply live_exit; exact Hexit.
    + eapply live_edge_use; eassumption.
  - inversion Htargets as [|edge rest Htarget Hrest]; subst.
    eapply live_edge_next; [exact He| |].
    2: apply IH; [exact Huse|eapply reachable_step; eassumption|exact Htarget|exact Hrest].
    intro Hdef; pose proof (point_ssa_defs_at_home Hssa (Graph.source g e) e x Hn He Hdef)
      as Hselected.
    rewrite Hhome in Hselected; inversion Hselected; subst; apply Hfree; reflexivity.
Qed.

Local Lemma live_syntactic_home x n : syntactic_live (point_model s) x n ->
  reachable g n -> exists d, point_definition s x = Some d.
Proof.
  intro Hlive; induction Hlive as [a Hexit|a e He Huse|a e He Hkill Hlive IH]; intro Hn.
  - destruct (point_ssa_uses_defined Hssa a x Hn (or_introl Hexit)) as [d [Hd _]]; eauto.
  - destruct (point_ssa_uses_defined Hssa a x Hn ltac:(right; exists e; auto))
      as [d [Hd _]]; eauto.
  - apply IH; apply (reachable_step e).
    + rewrite (out_source (points_graph_wf Hlaws) a e He); exact Hn.
    + rewrite (out_source (points_graph_wf Hlaws) a e He); exact He.
Qed.

End SsaPaths.

(** * Exact online queries *)

Local Lemma live_codes_different {N} (EN : encoding N) d t :
  negb (Pos.eqb (encode EN d) (encode EN t)) = true <-> d <> t.
Proof.
  rewrite negb_true_iff, Pos.eqb_neq; split.
  - intros Hne Heq; subst t; contradiction.
  - intros Hne Heq; apply Hne; apply (encode_injective EN); exact Heq.
Qed.

Local Lemma live_query_data {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) values n x :
  ssa_live_query EN EV idx values n x = true <->
  exists d t u, Map.get EV x (query_def values) = Some d /\
    In t (FinSet.elements (live_index_get EN n (query_back_closure idx))) /\ d <> t /\
    dominates_b EN (query_dom idx) d t = true /\
    In u (FinSet.elements (live_index_get EV x (query_uses values))) /\
    FinSet.mem EN u (live_index_get EN t (query_reduced idx)) = true.
Proof.
  unfold ssa_live_query; destruct (Map.get EV x (query_def values)) as [d|] eqn:Hdef.
  - rewrite existsb_exists; split.
    + intros [t [Ht Htest]]; apply andb_true_iff in Htest; destruct Htest as [Hhead Huses].
      apply andb_true_iff in Hhead; destruct Hhead as [Hne Hdom].
      apply live_codes_different in Hne; apply existsb_exists in Huses.
      destruct Huses as [u [Hu Hmem]]; exists d, t, u.
      repeat split; assumption || reflexivity.
    + intros [a [t [u [Ha [Ht [Hne [Hdom [Hu Hmem]]]]]]]].
      inversion Ha; subst a; exists t; split; [exact Ht|].
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply live_codes_different|]|].
      * exact Hne.
      * exact Hdom.
      * apply existsb_exists; exists u; auto.
  - split; [discriminate|intros [d [t [u [Hfalse _]]]]; discriminate].
Qed.

Local Lemma live_back_row_wf {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) n :
  FinSet.wf EN (live_index_get EN n (query_back_closure (prepare_ssa_query_graph EN EE g))).
Proof.
  unfold prepare_ssa_query_graph; cbn [query_back_closure].
  unfold live_index_get; rewrite live_tabulate_get.
  destruct (in_dec (dfs_eq_dec EN) n
    (preorder (dfs (prepare EN g) FinSet.empty (Graph.entries g)))).
  - apply FinSet.wf_fold_add; apply Map.wf_empty.
  - apply Map.wf_empty.
Qed.

Section QueryExactness.
Context {B BE N E V : Type} (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (s : ssa_points B BE N E V).
Local Abbreviation g := (live_graph (point_model s)).
Local Abbreviation r := (dfs (prepare EN g) FinSet.empty (Graph.entries g)).
Local Abbreviation idx := (prepare_ssa_query_graph EN EE g).
Local Abbreviation values := (prepare_ssa_query_values EN EV s).
Hypothesis Hlaws : ssa_point_laws s.
Hypothesis Hssa : reachable_point_ssa s.
Hypothesis Hready : ready EN g (prepare EN g).

Local Lemma live_uses_index n x :
  FinSet.mem EN n (live_index_get EV x (query_uses values)) = true <->
    reachable g n /\ point_use_at (point_model s) n x.
Proof.
  change (FinSet.mem EN n (live_index_get EV x (live_value_uses EN EV (point_model s)
    (preorder r))) = true <-> reachable g n /\ point_use_at (point_model s) n x).
  rewrite live_value_uses_mem, (live_pre_reachable EN g Hready n); reflexivity.
Qed.

Local Lemma live_query_math n x : reachable g n ->
  (ssa_live_query EN EV idx values n x = true <->
    exists d t u, point_definition s x = Some d /\ point_use_at (point_model s) u x /\
      rt_reaches EN g r n t /\ strictly_dominates g d t /\ reduced_path EN g r t u).
Proof.
  intro Hn; rewrite live_query_data; split.
  - intros [d [t [u [Hdef [Ht [Hne [Hdom [Hu Hreduced]]]]]]]].
    apply (FinSet.elements_spec EN) in Ht; [|apply live_back_row_wf].
    unfold prepare_ssa_query_graph in Ht; cbn [query_back_closure] in Ht.
    unfold live_index_get in Ht; rewrite live_tabulate_get in Ht.
    destruct (in_dec (dfs_eq_dec EN) n (preorder r)) as [Hin|Hnot];
      [|rewrite FinSet.mem_empty in Ht; discriminate].
    apply (live_t_pre_agrees EN g Hready n t Hn) in Ht.
    pose proof (live_rt_reachable EN g Hready n t Ht Hn) as HtReach.
    apply (FinSet.elements_spec EN) in Hu.
    2: exact (proj2 (live_value_uses_wf EN EV (point_model s) (preorder r)) x).
    apply live_uses_index in Hu; destruct Hu as [HuReach Huse].
    pose proof (live_value_definition EN EV s Hlaws Hssa u x HuReach Huse) as Hselected.
    rewrite Hdef in Hselected.
    exists d, t, u; split; [symmetry; exact Hselected|split; [exact Huse|split; [exact Ht|split]]].
    + split; [|exact Hne].
      apply (proj1 (proj1 (dominator_tree_with_exact EN g (prepare EN g) Hready SimpleLT)
        d t HtReach)); exact Hdom.
    + apply (live_reduced_agrees EN g Hready t u HtReach); exact Hreduced.
  - intros [d [t [u [Hhome [Huse [Ht [Hstrict Hreduced]]]]]]].
    pose proof (live_rt_reachable EN g Hready n t Ht Hn) as HtReach.
    assert (HuReach : reachable g u).
    { destruct Hreduced as [es [Hpath _]]; eapply live_path_reachable; eassumption. }
    exists d, t, u; split.
    + rewrite (live_value_definition EN EV s Hlaws Hssa u x HuReach Huse); exact Hhome.
    + split.
      * apply (FinSet.elements_spec EN); [apply live_back_row_wf|].
        unfold prepare_ssa_query_graph; cbn [query_back_closure].
        unfold live_index_get; rewrite live_tabulate_get.
        destruct (in_dec (dfs_eq_dec EN) n (preorder r)) as [Hin|Hnot].
        -- apply (live_t_pre_agrees EN g Hready n t Hn); exact Ht.
        -- exfalso; apply Hnot; apply live_pre_reachable; assumption.
      * split; [exact (proj2 Hstrict)|split].
        -- apply (proj2 (proj1 (dominator_tree_with_exact EN g (prepare EN g) Hready SimpleLT)
             d t HtReach)); exact (proj1 Hstrict).
        -- split.
           ++ apply (FinSet.elements_spec EN).
              ** exact (proj2 (live_value_uses_wf EN EV (point_model s) (preorder r)) x).
              ** apply live_uses_index; auto.
           ++ apply (live_reduced_agrees EN g Hready t u HtReach); exact Hreduced.
Qed.

End QueryExactness.

(** The prepared R/T query equals finite syntactic point liveness on reachable strict SSA. *)
Theorem ssa_live_query_exact {B BE N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  forall n x, reachable (live_graph (point_model s)) n ->
    (ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = true <-> syntactic_live (point_model s) x n).
Proof.
  intros Hlaws Hssa Hready n x Hn; rewrite (live_query_math EN EE EV s Hlaws Hssa Hready n x Hn).
  split.
  - intros [d [t [u [Hhome [Huse [Ht [Hstrict Hreduced]]]]]]].
    pose proof (live_rt_reachable EN _ Hready n t Ht Hn) as HtReach.
    destruct (live_rt_avoiding EN _ Hready d n t Ht Hn Hstrict) as [Hprefix _].
    pose proof (live_reduced_avoiding EN _ Hready d t u HtReach Hstrict Hreduced) as Htail.
    apply (live_avoiding_syntactic s Hssa d x n u Hhome Hn);
      [eapply live_avoiding_app; eassumption|exact Huse].
  - intro Hlive.
    pose proof (live_syntactic_path s Hlaws Hssa x n Hlive) as Hpath.
    destruct (live_syntactic_home s Hlaws Hssa x n Hlive Hn) as [d Hhome].
    destruct (Hpath d Hhome Hn) as [u [es [Hpath' [Htargets Huse]]]].
    pose proof (live_syntactic_strict s Hlaws Hssa x n Hlive d Hhome Hn) as Hstrict.
    destruct (live_strict_decompose EN _ Hready n es u Hpath' d n n Hn
      ltac:(constructor 2) ltac:(exists []; split; constructor) Hstrict Htargets)
      as [t [Ht [Htd Htu]]].
    exists d, t, u; auto.
Qed.

(** The fast query agrees with every least dense liveness solution on reachable strict SSA. *)
Theorem ssa_live_query_dense {B BE S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) (vv : var_view S O N E V C)
    (sigma : N -> live_set EV vv) :
  point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  least_solution (live_lattice EV vv) (liveness_system EV vv) sigma ->
  forall n x, reachable (live_graph (point_model s)) n ->
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = fmem EV x (sigma n).
Proof.
  intros Hmodel Hlaws Hssa Hready Hleast n x Hn; apply eq_true_iff_eq.
  rewrite (ssa_live_query_exact EN EE EV s Hlaws Hssa Hready n x Hn), Hmodel.
  symmetry; apply syntactic_live_least; [|exact Hleast|].
  - change (graph_wf (live_graph (var_point_uses vv))); rewrite <- Hmodel.
    exact (points_graph_wf Hlaws).
  - apply reachable_in_nodes.
    + change (graph_wf (live_graph (var_point_uses vv))); rewrite <- Hmodel.
      exact (points_graph_wf Hlaws).
    + change (reachable (live_graph (var_point_uses vv)) n); rewrite <- Hmodel; exact Hn.
Qed.

(** Successful Rules solving gives the same least liveness facts as the prepared R/T query. *)
Theorem ssa_live_query_rules {B BE S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) (vv : var_view S O N E V C)
    (db : database pred) :
  point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  solve_program liveness_program (extract_live_facts EN EE EV vv) = Some db ->
  forall n x, reachable (live_graph (point_model s)) n ->
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = fmem EV x (live_of_db EN EV vv db n).
Proof.
  intros Hmodel Hlaws Hssa Hready Hsolve.
  apply ssa_live_query_dense; try assumption.
  apply rules_liveness_least with (EE := EE); [|exact Hsolve].
  change (graph_wf (live_graph (var_point_uses vv))); rewrite <- Hmodel.
  exact (points_graph_wf Hlaws).
Qed.

(** * General fallback *)

(** The separate general producer prepares an ordinary Rules solution and remains available
    for listed unreachable points and non-strict views; it is never called by the fast query. *)
Definition general_live_query {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) : N -> V -> bool :=
  match solve_program liveness_program (extract_live_facts EN EE EV vv) with
  | Some db =>
    let answers := live_tabulate EN (fun n => proj1_sig (live_of_db EN EV vv db n))
      (Graph.nodes (cfg (gview vv))) in
    fun n x => FinSet.mem EV x (live_index_get EN n answers)
  | None => fun _ _ => false
  end.

(** The general fallback answers syntactic liveness throughout the finite graph, including
    unreachable components and same-edge use before definition, without an SSA premise. *)
Theorem general_live_query_exact {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) :
  graph_wf (cfg (gview vv)) -> forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    (general_live_query EN EE EV vv n x = true <-> syntactic_live (var_point_uses vv) x n).
Proof.
  intros Hwf n x Hn; unfold general_live_query.
  destruct (rules_liveness_solves EN EE EV vv Hwf) as [db Hsolve].
  rewrite Hsolve; unfold live_index_get; rewrite live_tabulate_get.
  destruct (in_dec (dfs_eq_dec EN) n (Graph.nodes (cfg (gview vv)))) as [Hin|Hnot];
    [|contradiction].
  apply syntactic_live_rules with (EE := EE); assumption.
Qed.
