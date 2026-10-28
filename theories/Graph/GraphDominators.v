(** * Exact dominator forests and independent boundary validation

    Both verified dominator backends share a forest numbering and interval interface.
    For example, a diamond's join is a child of its entry, not of either branch.
    Builds on: GraphDfs, GraphDominance, GraphLengauerTarjan and GraphSemiNca. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphLengauerTarjan GraphSemiNca.
Import List.ListNotations.

(** A parent forest carries discovery and finishing indexes for ancestry queries. *)
Record dom_tree (V : Type) : Type := DomTree {
  idom : Map.t V V;
  tin : Map.t V positive;
  tout : Map.t V positive
}.
Arguments DomTree {V}.
Arguments idom {V}.
Arguments tin {V}.
Arguments tout {V}.

(** Select either directly verified dominator backend. *)
Inductive dom_algorithm : Type :=
  | SimpleLT
  | SemiNCA.

(** The compatibility producer is the verified simple LT backend. *)
Definition chk_idom {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : Map.t V V := simple_lt_idom p.

(** Group children by parent once, before traversing the forest. *)
Fixpoint dom_children {V} (EV : encoding V) (bindings : list (V * V))
    : Map.t V (list V) :=
  match bindings with
  | [] => Map.empty
  | (v, u) :: rest =>
    let children := dom_children EV rest in
    Map.set EV u (v :: index_edges EV children u) children
  end.

(** The forest graph uses each child itself as its unique incoming edge identity. *)
Definition dom_forest {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (m : Map.t V V) : Graph.t V V :=
  let live := preorder (dfs p FinSet.empty (Graph.entries g)) in
  let children := dom_children EV (Map.elements m) in
  {| Graph.entries := filter (fun v => negb (Map.mem EV v m)) live;
     Graph.nodes := live;
     Graph.out := index_edges EV children;
     Graph.source := fun v => match Map.get EV v m with
       | Some u => u
       | None => v
       end;
     Graph.target := fun v => v |}.

(** A single traversal numbers the parent graph from its parentless reachable vertices. *)
Definition dom_search {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (m : Map.t V V) : dfs_result V V :=
  let f := dom_forest p m in
  dfs (prepare EV f) FinSet.empty (Graph.entries f).

(** Preserve the supplied parents and number their forest once. *)
Definition dom_tree_of {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (m : Map.t V V) : dom_tree V :=
  let r := dom_search p m in
  DomTree m (pre_num r) (post_num r).

(** Nested discovery and finishing intervals decide dominance in an exact tree. *)
Definition dominates_b {V} (EV : encoding V) (t : dom_tree V) (d n : V) : bool :=
  match Map.get EV d (tin t), Map.get EV n (tin t),
        Map.get EV d (tout t), Map.get EV n (tout t) with
  | Some a, Some b, Some c, Some e => Pos.leb a b && Pos.leb e c
  | _, _, _, _ => false
  end.

(** Independently validate parent domains, cycle freedom and blocked-search dominance. *)
Definition check_idom {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (m : Map.t V V) : bool :=
  let live := dfs p FinSet.empty (Graph.entries g) in
  let r := dom_search p m in
  let t := DomTree m (pre_num r) (post_num r) in
  forallb (fun binding =>
    FinSet.mem EV (fst binding) (visited live) &&
    FinSet.mem EV (snd binding) (visited live) &&
    FinSet.mem EV (fst binding) (visited r)) (Map.elements m) &&
  forallb (fun d =>
    let blocked := dfs p (FinSet.add EV d FinSet.empty) (Graph.entries g) in
    forallb (fun n => Bool.eqb (negb (FinSet.mem EV n (visited blocked)))
      (dominates_b EV t d n)) (preorder live)) (preorder live).

(** A sole entry parents every other reachable node in the conservative fallback. *)
Definition flat_idom {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : Map.t V V :=
  match Graph.entries g with
  | s :: rest =>
    if forallb (fun x => Pos.eqb (encode EV x) (encode EV s)) rest
    then fold_left (fun m n =>
      if Pos.eqb (encode EV n) (encode EV s) then m else Map.set EV n s m)
      (preorder (dfs p FinSet.empty (Graph.entries g))) Map.empty
    else Map.empty
  | [] => Map.empty
  end.

(** Number the explicit conservative fallback. *)
Definition flat_tree {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : dom_tree V := dom_tree_of p (flat_idom p).

(** Explicitly query the independent checker on the default backend's output. *)
Definition dominator_exact {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : bool := check_idom p (chk_idom p).

(** Construct an exact tree directly from the selected proved backend. *)
Definition dominator_tree_with {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (algorithm : dom_algorithm) : dom_tree V :=
  dom_tree_of p (match algorithm with
  | SimpleLT => simple_lt_idom p
  | SemiNCA => semi_nca_idom p
  end).

(** The default exact tree uses simple LT without invoking boundary validation. *)
Definition dominator_tree {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : dom_tree V := dominator_tree_with p SimpleLT.

(** * Child indexes and reachable domains *)

Lemma dom_children_in {V} (EV : encoding V) bindings u v :
  In v (index_edges EV (dom_children EV bindings) u) <-> In (v, u) bindings.
Proof.
  induction bindings as [|[w a] rest IH]; cbn [dom_children].
  - unfold index_edges; rewrite Map.get_empty; reflexivity.
  - destruct (dfs_eq_dec EV u a) as [Heq|Hne].
    + subst a; unfold index_edges at 1; rewrite Map.get_set_same.
      change (w = v \/ In v (index_edges EV (dom_children EV rest) u) <->
        (w, u) = (v, u) \/ In (v, u) rest).
      rewrite IH; intuition congruence.
    + unfold index_edges at 1; rewrite Map.get_set_other by exact Hne.
      change (In v (index_edges EV (dom_children EV rest) u) <->
        (w, a) = (v, u) \/ In (v, u) rest).
      rewrite IH; intuition congruence.
Qed.

Lemma dom_children_nodup {V} (EV : encoding V) bindings :
  NoDup (map fst bindings) ->
  forall u, NoDup (index_edges EV (dom_children EV bindings) u).
Proof.
  induction bindings as [|[v a] rest IH]; intros Hnodup u.
  - unfold index_edges; cbn [dom_children]; rewrite Map.get_empty; constructor.
  - inversion Hnodup as [|? ? Hfresh Hrest]; subst.
    cbn [dom_children]; unfold index_edges at 1.
    destruct (dfs_eq_dec EV u a) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same; constructor.
      * intro Hin; apply dom_children_in in Hin; apply Hfresh.
        exact (in_map fst rest (v, u) Hin).
      * apply IH; exact Hrest.
    + rewrite Map.get_set_other by exact Hne; apply IH; exact Hrest.
Qed.

Section ForestNumbering.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variable m : Map.t V V.
Hypothesis Hready : ready EV g p.
Hypothesis Hmap : Map.wf EV m.
Hypothesis Hdomain : forall v u, Map.get EV v m = Some u -> reachable g v /\ reachable g u.

Local Abbreviation F := (dom_forest p m).
Local Abbreviation R := (dom_search p m).

Lemma dom_live n : In n (Graph.nodes F) <-> reachable g n.
Proof.
  destruct Hready as [Hgraph _].
  destruct (dfs_exact EV g p n (Graph.entries g) FinSet.empty Hready (entries_in Hgraph))
    as [_ [_ [_ Hpre]]].
  change (In n (preorder (dfs p FinSet.empty (Graph.entries g))) <-> reachable g n).
  rewrite Hpre; apply reachable_dfs; exact Hready.
Qed.

Lemma dom_edge u v : In v (Graph.out F u) <-> Map.get EV v m = Some u.
Proof.
  change (In v (index_edges EV (dom_children EV (Map.elements m)) u) <->
    Map.get EV v m = Some u).
  rewrite dom_children_in; split.
  - apply Map.elements_sound; exact Hmap.
  - apply Map.elements_complete; exact Hmap.
Qed.

Lemma dom_roots v : In v (Graph.entries F) <-> reachable g v /\ Map.get EV v m = None.
Proof.
  change (In v (filter (fun v => negb (Map.mem EV v m)) (Graph.nodes F)) <->
    reachable g v /\ Map.get EV v m = None).
  rewrite filter_In, dom_live, Bool.negb_true_iff.
  unfold Map.mem; destruct (Map.get EV v m); intuition discriminate.
Qed.

Lemma dom_forest_ready : ready EV F (prepare EV F).
Proof.
  apply prepare_ready.
  - constructor.
    + pose proof (dfs_final_spec EV g p FinSet.empty (Graph.entries g)
        Hready (entries_in (proj1 Hready))) as [Hinv _].
      change (NoDup (preorder (dfs p FinSet.empty (Graph.entries g)))).
      unfold dfs; cbn [preorder]; apply NoDup_rev.
      exact (dfs_pre_nodup _ _ _ _ _ _ Hinv).
    + intros v Hv; apply dom_live; apply dom_roots in Hv; tauto.
    + intros u v Hedge; apply dom_edge in Hedge.
      change ((match Map.get EV v m with Some a => a | None => v end) = u).
      rewrite Hedge; reflexivity.
    + intros u v Hu Hedge; apply dom_live; apply dom_edge in Hedge.
      exact (proj1 (Hdomain v u Hedge)).
  - intro u; exact (dom_children_nodup EV (Map.elements m)
      (Map.elements_nodup EV m Hmap) u).
Qed.

Lemma dom_number_domain v :
  (exists a, Map.get EV v (pre_num R) = Some a) <->
  FinSet.mem EV v (visited R) = true.
Proof.
  pose proof (dom_forest_ready) as Hforest.
  destruct (dfs_final_spec EV F (prepare EV F) FinSet.empty (Graph.entries F)
    Hforest (entries_in (proj1 Hforest))) as [Hinv [Hlabels _]].
  unfold dom_search, dfs; cbn [pre_num visited].
  rewrite (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)).
  symmetry; exact (dfs_seen_pre _ _ _ _ _ _ Hinv v).
Qed.

Lemma dom_search_parent u v : tree_parent EV F R u v -> Map.get EV v m = Some u.
Proof.
  intros [e [He Hsource]].
  pose proof (dom_forest_ready) as Hforest.
  destruct (dfs_final_spec EV F (prepare EV F) FinSet.empty (Graph.entries F)
    Hforest (entries_in (proj1 Hforest))) as [_ [Hlabels _]].
  change (Map.get EV v (DfsState.parent
    (fold_left (dfs_root (prepare EV F) FinSet.empty) (Graph.entries F) dfs_initial))
    = Some e) in He.
  destruct (dfs_parent_labels _ _ _ _ Hlabels v e He) as [_ [_ [Hedge [Htarget _]]]].
  change (e = v) in Htarget; subst e.
  apply dom_edge in Hedge; rewrite Hsource in Hedge; exact Hedge.
Qed.

Lemma dom_search_parent_complete v u :
  FinSet.mem EV v (visited R) = true -> Map.get EV v m = Some u ->
  tree_parent EV F R u v.
Proof.
  intros Hv Hget; pose proof dom_forest_ready as Hforest.
  destruct (dfs_tree EV F (prepare EV F) v (Graph.entries F) FinSet.empty
    Hforest (entries_in (proj1 Hforest)) Hv) as [[Hroot _]|[e [He [Hedge [Ht _]]]]].
  - apply dom_roots in Hroot; destruct Hroot as [_ Hnone]; congruence.
  - change (e = v) in Ht; subst e.
    exists v; split; [exact He|].
    change ((match Map.get EV v m with Some a => a | None => v end) = u).
    rewrite Hget; reflexivity.
Qed.

Lemma dom_search_parent_rank v u :
  FinSet.mem EV v (visited R) = true -> Map.get EV v m = Some u ->
  exists a b, Map.get EV u (pre_num R) = Some a /\
    Map.get EV v (pre_num R) = Some b /\ Pos.lt a b.
Proof.
  intros Hv Hget.
  destruct (dom_search_parent_complete v u Hv Hget) as [e [He Hsource]].
  pose proof dom_forest_ready as Hforest.
  destruct (dfs_final_spec EV F (prepare EV F) FinSet.empty (Graph.entries F)
    Hforest (entries_in (proj1 Hforest))) as [_ [Hlabels _]].
  change (Map.get EV v (DfsState.parent
    (fold_left (dfs_root (prepare EV F) FinSet.empty) (Graph.entries F) dfs_initial))
    = Some e) in He.
  destruct (dfs_parent_labels _ _ _ _ Hlabels v e He) as [_ [_ [_ [_ Hrank]]]].
  rewrite Hsource in Hrank; exact Hrank.
Qed.

Lemma dom_coverage_forest :
  (forall v u, Map.get EV v m = Some u -> FinSet.mem EV v (visited R) = true) ->
  forest_on EV g m.
Proof.
  intro Hcoverage; split; [exact Hdomain|].
  apply (well_founded_lt_compat V (fun v =>
    match Map.get EV v (pre_num R) with
    | Some a => Pos.to_nat a
    | None => 0
    end)).
  intros u v Hget.
  destruct (dom_search_parent_rank v u (Hcoverage v u Hget) Hget)
    as [a [b [Ha [Hb Hlt]]]].
  rewrite Ha, Hb; apply Pos2Nat.inj_lt; exact Hlt.
Qed.

Lemma dom_forest_reachable : well_founded (fun u v => Map.get EV v m = Some u) ->
  forall v, reachable g v -> reachable F v.
Proof.
  intros Hwell v; induction (Hwell v) as [v Hacc IH]; intro Hv.
  destruct (Map.get EV v m) as [u|] eqn:Hget.
  - change (reachable F (Graph.target F v)).
    apply reachable_step.
    + change (reachable F (match Map.get EV v m with Some a => a | None => v end)).
      rewrite Hget; apply IH; [reflexivity|exact (proj2 (Hdomain v u Hget))].
    + apply dom_edge.
      change (Map.get EV v m = Some
        (match Map.get EV v m with Some a => a | None => v end)).
      rewrite Hget; reflexivity.
  - apply reachable_entry; apply dom_roots; split; assumption.
Qed.

Lemma dom_forest_coverage : well_founded (fun u v => Map.get EV v m = Some u) ->
  forall v, FinSet.mem EV v (visited R) = true <-> reachable g v.
Proof.
  intros Hwell v; rewrite (reachable_dfs EV F (prepare EV F) v dom_forest_ready).
  split.
  - intro Hv; apply dom_live; apply (reachable_in_nodes F v (proj1 dom_forest_ready) Hv).
  - apply dom_forest_reachable; exact Hwell.
Qed.

Lemma dom_ancestor_reachable d n : reachable g n -> idom_ancestor EV m d n -> reachable g d.
Proof.
  intros Hn Hanc; induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv].
  - exact (proj2 (Hdomain v u Hget)).
  - exact Hn.
  - apply IHuw; apply IHwv; exact Hn.
Qed.

Lemma dom_search_ancestry :
  (forall v u, Map.get EV v m = Some u -> FinSet.mem EV v (visited R) = true) ->
  forall d n, dfs_ancestor EV F R d n <-> idom_ancestor EV m d n.
Proof.
  intros Hcoverage d n; split; intro Hanc;
    induction Hanc as [u v Hparent|v|u w v Huw IHuw Hwv IHwv].
  - apply rt_step; apply dom_search_parent; exact Hparent.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
  - apply rt_step; apply dom_search_parent_complete with (u := u).
    + apply (Hcoverage v u); exact Hparent.
    + exact Hparent.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma dom_numbering_agrees : forest_on EV g m ->
  (forall n, (exists a, Map.get EV n (tin (dom_tree_of p m)) = Some a) <-> reachable g n) /\
  (forall d n, reachable g n ->
    (dominates_b EV (dom_tree_of p m) d n = true <-> idom_ancestor EV m d n)).
Proof.
  intros [_ Hwell].
  pose proof (dom_forest_coverage Hwell) as Hcoverage.
  split.
  - intro n; change ((exists a, Map.get EV n (pre_num R) = Some a) <-> reachable g n).
    rewrite dom_number_domain; apply Hcoverage.
  - intros d n Hn.
    destruct (FinSet.mem EV d (visited R)) eqn:Hd.
    + change (ancestor_b EV R d n = true <-> idom_ancestor EV m d n).
      rewrite (ancestor_b_agrees EV F (prepare EV F) d n (Graph.entries F) FinSet.empty
        dom_forest_ready (entries_in (proj1 dom_forest_ready)) Hd
        (proj2 (Hcoverage n) Hn)).
      apply dom_search_ancestry; intros v u Hget.
      apply Hcoverage; exact (proj1 (Hdomain v u Hget)).
    + assert (Hnone : Map.get EV d (pre_num R) = None).
      { destruct (Map.get EV d (pre_num R)) as [a|] eqn:Hget; [|reflexivity].
        exfalso; assert (Hmem : FinSet.mem EV d (visited R) = true).
        { apply dom_number_domain; exists a; exact Hget. }
        congruence. }
      split.
      * unfold dominates_b, dom_tree_of; cbn [tin]; rewrite Hnone; discriminate.
      * intro Hanc; pose proof (dom_ancestor_reachable d n Hn Hanc) as Hreach.
        apply Hcoverage in Hreach; congruence.
Qed.

End ForestNumbering.

(** A well-founded reachable parent forest is numbered exactly by ancestry intervals. *)
Theorem dom_tree_of_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (m : Map.t V V) :
  ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall n, (exists a, Map.get EV n (tin (dom_tree_of p m)) = Some a) <-> reachable g n) /\
  (forall d n, reachable g n ->
    (dominates_b EV (dom_tree_of p m) d n = true <-> idom_ancestor EV m d n)).
Proof.
  intros Hready Hmap Hforest.
  apply dom_numbering_agrees; try assumption; exact (proj1 Hforest).
Qed.

(** * Independent blocked-search validation *)

Lemma dom_blocked_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) d n : ready EV g p ->
  (negb (FinSet.mem EV n
    (visited (dfs p (FinSet.add EV d FinSet.empty) (Graph.entries g)))) = true <->
   dominates g d n).
Proof.
  intro Hready.
  destruct (dfs_exact EV g p n (Graph.entries g) (FinSet.add EV d FinSet.empty)
    Hready (entries_in (proj1 Hready))) as [Hexact _].
  replace (set_entries g (Graph.entries g)) with g in Hexact by (destruct g; reflexivity).
  rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, Hexact.
  symmetry; apply dominates_iff_unreachable_without.
Qed.

Lemma dom_dominator_reachable {V E} (g : Graph.t V E) d n :
  reachable g n -> dominates g d n -> reachable g d.
Proof.
  intros Hn Hdom; apply reachable_iff_path in Hn.
  destruct Hn as [s [es [Hs Hpath]]].
  destruct (Hdom s es Hs Hpath) as [Heq|[e [He Htarget]]].
  - subst d; apply reachable_entry; exact Hs.
  - destruct (path_prefix_target g s es n e Hpath He) as [pre [Hpre _]].
    rewrite <- Htarget; apply reachable_iff_path; exists s, pre; split; assumption.
Qed.

Lemma check_idom_bindings {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) m : Map.wf EV m -> check_idom p m = true ->
  forall v u, Map.get EV v m = Some u ->
  (FinSet.mem EV v (visited (dfs p FinSet.empty (Graph.entries g))) = true /\
   FinSet.mem EV u (visited (dfs p FinSet.empty (Graph.entries g))) = true) /\
  FinSet.mem EV v (visited (dom_search p m)) = true.
Proof.
  intros Hmap Hcheck v u Hget.
  unfold check_idom in Hcheck; apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [Hbindings _].
  apply forallb_forall with (x := (v, u)) in Hbindings.
  - cbn in Hbindings; repeat rewrite Bool.andb_true_iff in Hbindings; exact Hbindings.
  - apply (Map.elements_complete EV); assumption.
Qed.

Lemma check_idom_pairs {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) m : ready EV g p -> check_idom p m = true ->
  forall d n, reachable g d -> reachable g n ->
  (dominates_b EV (dom_tree_of p m) d n = true <-> dominates g d n).
Proof.
  intros Hready Hcheck d n Hd Hn.
  unfold check_idom in Hcheck; apply Bool.andb_true_iff in Hcheck.
  destruct Hcheck as [_ Hpairs].
  apply forallb_forall with (x := d) in Hpairs.
  - apply forallb_forall with (x := n) in Hpairs.
    + apply Bool.eqb_prop in Hpairs.
      change (negb (FinSet.mem EV n
        (visited (dfs p (FinSet.add EV d FinSet.empty) (Graph.entries g)))) =
        dominates_b EV (dom_tree_of p m) d n) in Hpairs.
      rewrite <- Hpairs; apply dom_blocked_exact; exact Hready.
    + apply (dom_live EV g p m Hready); exact Hn.
  - apply (dom_live EV g p m Hready); exact Hd.
Qed.

(** Accepted external parents form a forest and recognize exactly semantic dominance. *)
Theorem check_idom_sound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (m : Map.t V V) :
  ready EV g p -> Map.wf EV m -> check_idom p m = true ->
  forest_on EV g m /\ forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV m d n).
Proof.
  intros Hready Hmap Hcheck.
  pose proof (check_idom_bindings EV g p m Hmap Hcheck) as Hbindings.
  assert (Hdomain : forall v u, Map.get EV v m = Some u -> reachable g v /\ reachable g u).
  { intros v u Hget; destruct (Hbindings v u Hget) as [[Hv Hu] _].
    split; apply (reachable_dfs EV g p); assumption. }
  assert (Hforest : forest_on EV g m).
  { apply (dom_coverage_forest EV g p m Hready Hmap Hdomain).
    intros v u Hget; exact (proj2 (Hbindings v u Hget)). }
  split; [exact Hforest|].
  intros d n Hn; split; intro Hdom.
  - apply (proj1 (proj2 (dom_tree_of_agrees EV g p m Hready Hmap Hforest) d n Hn)).
    apply (proj2 (check_idom_pairs EV g p m Hready Hcheck d n
      (dom_dominator_reachable g d n Hn Hdom) Hn)); exact Hdom.
  - apply (proj1 (check_idom_pairs EV g p m Hready Hcheck d n
      (dom_ancestor_reachable EV g m Hdomain d n Hn Hdom) Hn)).
    apply (proj2 (proj2 (dom_tree_of_agrees EV g p m Hready Hmap Hforest) d n Hn)).
    exact Hdom.
Qed.

(** Every exact reachable parent forest passes the independent boundary checker. *)
Theorem check_idom_complete {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (m : Map.t V V) :
  ready EV g p -> Map.wf EV m -> forest_on EV g m ->
  (forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n)) ->
  check_idom p m = true.
Proof.
  intros Hready Hmap Hforest Hexact.
  pose proof (dom_forest_coverage EV g p m Hready Hmap (proj1 Hforest)
    (proj2 Hforest)) as Hcoverage.
  pose proof (proj2 (dom_tree_of_agrees EV g p m Hready Hmap Hforest)) as Hinterval.
  unfold check_idom; apply Bool.andb_true_iff; split.
  - apply forallb_forall; intros [v u] Hin; cbn [fst snd].
    pose proof (Map.elements_sound EV v u m Hmap Hin) as Hget.
    destruct (proj1 Hforest v u Hget) as [Hv Hu].
    repeat rewrite Bool.andb_true_iff; split.
    + split; apply (reachable_dfs EV g p); assumption.
    + apply Hcoverage; exact Hv.
  - apply forallb_forall; intros d Hd; apply forallb_forall; intros n Hn.
    apply (dom_live EV g p m Hready) in Hd, Hn.
    apply Bool.eqb_true_iff; apply eq_true_iff_eq.
    change (negb (FinSet.mem EV n
      (visited (dfs p (FinSet.add EV d FinSet.empty) (Graph.entries g)))) = true <->
      dominates_b EV (dom_tree_of p m) d n = true).
    rewrite (dom_blocked_exact EV g p d n Hready), (Hinterval d n Hn).
    apply Hexact; exact Hn.
Qed.

(** The compatibility producer's map is well formed. *)
Theorem chk_idom_wf {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> Map.wf EV (chk_idom p).
Proof.
  intro Hready; exact (proj1 (simple_lt_idom_exact EV g p Hready)).
Qed.

(** Independent validation always accepts the directly proved default backend. *)
Theorem dominator_exact_true {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> dominator_exact p = true.
Proof.
  intro Hready; destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  apply (check_idom_complete EV g p (chk_idom p)); assumption.
Qed.

(** * Immediate parents of exact forests *)

Lemma dom_ancestor_last {V} (EV : encoding V) (m : Map.t V V) d n :
  idom_ancestor EV m d n ->
  d = n \/ exists u, Map.get EV n m = Some u /\ idom_ancestor EV m d u.
Proof.
  intro Hanc; induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv].
  - right; exists u; split; [exact Hget|apply rt_refl].
  - left; reflexivity.
  - destruct IHwv as [Heq|[a [Hget Hanc]]].
    + subst v; exact IHuw.
    + right; exists a; split; [exact Hget|]. eapply rt_trans; eassumption.
Qed.

(** The preorder rank is used only to prove that parent ancestry is antisymmetric. *)
Definition dom_rank {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (m : Map.t V V) (v : V) : nat :=
  match Map.get EV v (pre_num (dom_search p m)) with
  | Some a => Pos.to_nat a
  | None => 0
  end.

Section ExactParents.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variable m : Map.t V V.
Hypothesis Hready : ready EV g p.
Hypothesis Hmap : Map.wf EV m.
Hypothesis Hforest : forest_on EV g m.
Hypothesis Hexact : forall d n, reachable g n ->
  (dominates g d n <-> idom_ancestor EV m d n).

Lemma dom_parent_rank u v : Map.get EV v m = Some u ->
  dom_rank p m u < dom_rank p m v.
Proof.
  intro Hget.
  pose proof (proj1 Hforest) as Hdomain.
  assert (Hv : FinSet.mem EV v (visited (dom_search p m)) = true).
  { apply (dom_forest_coverage EV g p m Hready Hmap Hdomain (proj2 Hforest)).
    exact (proj1 (Hdomain v u Hget)). }
  destruct (dom_search_parent_rank EV g p m Hready Hmap Hdomain v u Hv Hget)
    as [a [b [Ha [Hb Hlt]]]].
  unfold dom_rank; rewrite Ha, Hb; apply Pos2Nat.inj_lt; exact Hlt.
Qed.

Lemma dom_ancestor_rank d n : idom_ancestor EV m d n ->
  d = n \/ dom_rank p m d < dom_rank p m n.
Proof.
  intro Hanc; induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv].
  - right; apply dom_parent_rank; exact Hget.
  - left; reflexivity.
  - destruct IHuw as [Heq|Hlt], IHwv as [Heq'|Hlt'];
      subst; try (left; reflexivity); right; lia.
Qed.

Lemma dom_ancestor_antisym d n :
  idom_ancestor EV m d n -> idom_ancestor EV m n d -> d = n.
Proof.
  intros Hdn Hnd; apply dom_ancestor_rank in Hdn, Hnd.
  destruct Hdn as [Heq|Hdn]; [exact Heq|].
  destruct Hnd as [Heq|Hnd]; [symmetry; exact Heq|lia].
Qed.

Lemma dom_parent_strict n d : Map.get EV n m = Some d -> strictly_dominates g d n.
Proof.
  intro Hget; split.
  - apply (Hexact d n (proj1 (proj1 Hforest n d Hget))); apply rt_step; exact Hget.
  - intro Heq; subst d; pose proof (dom_parent_rank n n Hget); lia.
Qed.

Lemma dom_parent_immediate d n : reachable g n ->
  (Map.get EV n m = Some d <-> immediately_dominates g d n).
Proof.
  intro Hn; split.
  - intro Hget; split; [apply dom_parent_strict; exact Hget|].
    intros x [Hx Hne]; apply (Hexact x d (proj2 (proj1 Hforest n d Hget))).
    apply (Hexact x n Hn) in Hx.
    destruct (dom_ancestor_last EV m x n Hx) as [Heq|[u [Hu Hanc]]].
    + contradiction.
    + assert (u = d) by congruence; subst u; exact Hanc.
  - intros [[Hd Hne] Hnearest]; apply (Hexact d n Hn) in Hd.
    destruct (dom_ancestor_last EV m d n Hd) as [Heq|[u [Hu Hanc]]].
    + contradiction.
    + assert (Hdreach : reachable g d).
      { eapply dom_ancestor_reachable; [exact (proj1 Hforest)|exact Hn|exact Hd]. }
      assert (Hud : idom_ancestor EV m u d).
      { apply (Hexact u d Hdreach); apply Hnearest; apply dom_parent_strict; exact Hu. }
      pose proof (dom_ancestor_antisym d u Hanc Hud) as Heq; subst u; exact Hu.
Qed.

Lemma dom_parentless_exact n : reachable g n ->
  (Map.get EV n m = None <-> forall d, ~ strictly_dominates g d n).
Proof.
  intro Hn; split.
  - intros Hnone d [Hd Hne]; apply (Hexact d n Hn) in Hd.
    destruct (dom_ancestor_last EV m d n Hd) as [Heq|[u [Hu _]]]; congruence.
  - intro Hroot; destruct (Map.get EV n m) as [d|] eqn:Hget; [|reflexivity].
    exfalso; apply (Hroot d); apply dom_parent_strict; exact Hget.
Qed.

End ExactParents.

(** * Direct selectors and their agreement *)

(** Each backend yields exact interval dominance, immediate parents and parentless roots. *)
Theorem dominator_tree_with_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> forall algorithm,
  (forall d n, reachable g n ->
    (dominates_b EV (dominator_tree_with p algorithm) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = Some d <->
     immediately_dominates g d n)) /\
  (forall n, reachable g n ->
    (Map.get EV n (idom (dominator_tree_with p algorithm)) = None <->
     forall d, ~ strictly_dominates g d n)).
Proof.
  intros Hready algorithm.
  assert (Hbackend : forall m, Map.wf EV m -> forest_on EV g m ->
    (forall d n, reachable g n -> (dominates g d n <-> idom_ancestor EV m d n)) ->
    (forall d n, reachable g n ->
      (dominates_b EV (dom_tree_of p m) d n = true <-> dominates g d n)) /\
    (forall d n, reachable g n ->
      (Map.get EV n m = Some d <-> immediately_dominates g d n)) /\
    (forall n, reachable g n ->
      (Map.get EV n m = None <-> forall d, ~ strictly_dominates g d n))).
  { intros m Hmap Hforest Hexact; split.
    - intros d n Hn; rewrite (proj2 (dom_tree_of_agrees EV g p m Hready Hmap Hforest)
        d n Hn); symmetry; apply Hexact; exact Hn.
    - split.
      + apply (dom_parent_immediate EV g p m); assumption.
      + apply (dom_parentless_exact EV g p m); assumption. }
  destruct algorithm; unfold dominator_tree_with; cbn [idom].
  - destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
    apply Hbackend; assumption.
  - destruct (semi_nca_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
    apply Hbackend; assumption.
Qed.

(** The compatibility exactness theorem follows directly from the default backend. *)
Theorem dominator_tree_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> dominator_exact p = true ->
  (forall d n, reachable g n ->
    (dominates_b EV (dominator_tree p) d n = true <-> dominates g d n)) /\
  (forall d n, reachable g n ->
    (Map.get EV n (idom (dominator_tree p)) = Some d <-> immediately_dominates g d n)) /\
  (forall n, reachable g n ->
    (Map.get EV n (idom (dominator_tree p)) = None <-> forall d, ~ strictly_dominates g d n)).
Proof.
  intros Hready _; apply dominator_tree_with_exact; exact Hready.
Qed.

Lemma dom_interval_numbered {V} (EV : encoding V) (t : dom_tree V) d n :
  dominates_b EV t d n = true -> exists b, Map.get EV n (tin t) = Some b.
Proof.
  unfold dominates_b.
  destruct (Map.get EV d (tin t)), (Map.get EV n (tin t)) as [b|],
    (Map.get EV d (tout t)), (Map.get EV n (tout t));
    try discriminate; intros _; exists b; reflexivity.
Qed.

(** The default tree covers the reachable nodes and all its parent and interval claims are sound. *)
Theorem dominator_tree_sound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p ->
  (forall n, (exists a, Map.get EV n (tin (dominator_tree p)) = Some a) <-> reachable g n) /\
  (forall d n, idom_ancestor EV (idom (dominator_tree p)) d n -> dominates g d n) /\
  (forall d n, dominates_b EV (dominator_tree p) d n = true -> dominates g d n) /\
  (forall n d, Map.get EV n (idom (dominator_tree p)) = Some d -> strictly_dominates g d n).
Proof.
  intro Hready; destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  pose proof (proj1 (dom_tree_of_agrees EV g p (simple_lt_idom p) Hready Hmap Hforest))
    as Hnumbers.
  change (forall n, (exists a, Map.get EV n (tin (dominator_tree p)) = Some a) <->
    reachable g n) in Hnumbers.
  split; [exact Hnumbers|].
  assert (Hparents : forall n d, Map.get EV n (idom (dominator_tree p)) = Some d ->
    strictly_dominates g d n).
  { apply (dom_parent_strict EV g p (simple_lt_idom p)); assumption. }
  split.
  - intros d n Hanc; induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv].
    + exact (proj1 (Hparents v u Hget)).
    + apply dominates_refl.
    + eapply dominates_trans; eassumption.
  - split; [|exact Hparents].
    intros d n Hinterval.
    apply (proj1 (proj1 (dominator_tree_with_exact EV g p Hready SimpleLT) d n
      (proj1 (Hnumbers n) (dom_interval_numbered EV (dominator_tree p) d n Hinterval)))).
    exact Hinterval.
Qed.

Lemma dom_backend_maps_agree {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> simple_lt_idom p = semi_nca_idom p.
Proof.
  intro Hready.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hlt [Hltforest Hltexact]].
  destruct (semi_nca_idom_exact EV g p Hready) as [Hnca [Hncaforest Hncaexact]].
  pose proof (proj1 (proj2 (dominator_tree_with_exact EV g p Hready SimpleLT))) as Hleft.
  pose proof (proj1 (proj2 (dominator_tree_with_exact EV g p Hready SemiNCA))) as Hright.
  change (forall d n, reachable g n ->
    (Map.get EV n (simple_lt_idom p) = Some d <-> immediately_dominates g d n)) in Hleft.
  change (forall d n, reachable g n ->
    (Map.get EV n (semi_nca_idom p) = Some d <-> immediately_dominates g d n)) in Hright.
  apply (Map.extensionality EV); [exact Hlt|exact Hnca|].
  intro n; destruct (Map.get EV n (simple_lt_idom p)) as [d|] eqn:Hget.
  - symmetry; apply Hright.
    + exact (proj1 (proj1 Hltforest n d Hget)).
    + apply Hleft; [exact (proj1 (proj1 Hltforest n d Hget))|exact Hget].
  - destruct (Map.get EV n (semi_nca_idom p)) as [d|] eqn:Hother; [|reflexivity].
    exfalso; assert (Hreach : reachable g n) by exact (proj1 (proj1 Hncaforest n d Hother)).
    assert (Hsome : Map.get EV n (simple_lt_idom p) = Some d).
    { apply (Hleft d n Hreach); apply (Hright d n Hreach); exact Hother. }
    congruence.
Qed.

(** Both selectable backends produce the same complete numbered dominator tree. *)
Theorem dominator_tree_with_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> forall first second,
  dominator_tree_with p first = dominator_tree_with p second.
Proof.
  intros Hready first second; destruct first, second; try reflexivity;
    unfold dominator_tree_with; rewrite (dom_backend_maps_agree EV g p Hready); reflexivity.
Qed.

(** * Conservative flat fallback *)

Lemma dom_flat_fold_wf {V} (EV : encoding V) s xs : forall m,
  Map.wf EV m -> Map.wf EV (fold_left (fun m n =>
    if Pos.eqb (encode EV n) (encode EV s) then m else Map.set EV n s m) xs m).
Proof.
  induction xs as [|v xs IH]; intros m Hmap; cbn; [exact Hmap|].
  apply IH; destruct (Pos.eqb (encode EV v) (encode EV s));
    [exact Hmap|apply Map.wf_set; exact Hmap].
Qed.

Lemma dom_flat_fold_lookup {V} (EV : encoding V) s xs : forall m n,
  Map.get EV n (fold_left (fun m v =>
    if Pos.eqb (encode EV v) (encode EV s) then m else Map.set EV v s m) xs m) =
  if dfs_eq_dec EV n s then Map.get EV n m
  else if in_dec (dfs_eq_dec EV) n xs then Some s else Map.get EV n m.
Proof.
  induction xs as [|v xs IH]; intros m n.
  - cbn [fold_left]; destruct (dfs_eq_dec EV n s), (in_dec (dfs_eq_dec EV) n []);
      try contradiction; reflexivity.
  - cbn [fold_left]; rewrite IH.
    destruct (dfs_eq_dec EV v s) as [Hvs|Hvs].
    + subst v; rewrite Pos.eqb_refl.
      destruct (dfs_eq_dec EV n s) as [Hns|Hns]; [reflexivity|].
      destruct (in_dec (dfs_eq_dec EV) n xs), (in_dec (dfs_eq_dec EV) n (s :: xs));
        try reflexivity; cbn in *; intuition congruence.
    + assert (Hcode : Pos.eqb (encode EV v) (encode EV s) = false).
      { apply Pos.eqb_neq; intro Heq; apply Hvs; apply (encode_injective EV); exact Heq. }
      rewrite Hcode.
      destruct (dfs_eq_dec EV n s) as [Hns|Hns].
      * subst n; rewrite Map.get_set_other by congruence; reflexivity.
      * destruct (dfs_eq_dec EV n v) as [Hnv|Hnv].
        -- subst n; rewrite Map.get_set_same.
           destruct (in_dec (dfs_eq_dec EV) v (v :: xs)) as [Hin|Hnot].
           ++ destruct (in_dec (dfs_eq_dec EV) v xs); reflexivity.
           ++ exfalso; apply Hnot; left; reflexivity.
        -- rewrite Map.get_set_other by exact Hnv.
           destruct (in_dec (dfs_eq_dec EV) n xs),
             (in_dec (dfs_eq_dec EV) n (v :: xs));
             try reflexivity; cbn in *; intuition congruence.
Qed.

Lemma dom_same_entries {V} (EV : encoding V) s rest :
  forallb (fun x => Pos.eqb (encode EV x) (encode EV s)) rest = true <->
  forall x, In x (s :: rest) -> x = s.
Proof.
  rewrite forallb_forall; split.
  - intros Hall x [Heq|Hin]; [symmetry; exact Heq|].
    apply (encode_injective EV); apply Pos.eqb_eq; apply Hall; exact Hin.
  - intros Hall x Hin; apply Pos.eqb_eq; rewrite (Hall x (or_intror Hin)); reflexivity.
Qed.

Lemma dom_flat_single {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) s : ready EV g p ->
  (Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s) ->
  Map.wf EV (flat_idom p) /\
  (forall n d, Map.get EV n (flat_idom p) = Some d <-> reachable g n /\ n <> s /\ d = s).
Proof.
  intros Hready [Hnonempty Hall].
  unfold flat_idom; destruct (Graph.entries g) as [|a rest] eqn:Hentries; [contradiction|].
  assert (Ha : a = s) by (apply Hall; left; reflexivity); subst a.
  rewrite (proj2 (dom_same_entries EV s rest) Hall); split.
  - apply dom_flat_fold_wf; apply Map.wf_empty.
  - intros n d; rewrite dom_flat_fold_lookup, Map.get_empty.
    destruct (dfs_eq_dec EV n s) as [Heq|Hne].
    + subst n; split; [discriminate|intros [_ [Hfalse _]]; contradiction].
    + destruct (in_dec (dfs_eq_dec EV) n
        (preorder (dfs p FinSet.empty (s :: rest)))) as [Hin|Hnot].
      * split.
        -- intro Heq; injection Heq as Heq; subst d; split.
           ++ apply (dom_live EV g p Map.empty Hready).
              change (In n (preorder (dfs p FinSet.empty (Graph.entries g)))).
              rewrite Hentries; exact Hin.
           ++ split; [exact Hne|reflexivity].
        -- intros [_ [_ Heq]]; subst d; reflexivity.
      * split; [discriminate|intros [Hreach _]; exfalso; apply Hnot].
        rewrite <- Hentries; apply (dom_live EV g p Map.empty Hready); exact Hreach.
Qed.

Lemma dom_flat_cases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  flat_idom p = Map.empty \/
  exists s, Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s.
Proof.
  unfold flat_idom; destruct (Graph.entries g) as [|s rest] eqn:Hentries; [left; reflexivity|].
  destruct (forallb (fun x => Pos.eqb (encode EV x) (encode EV s)) rest) eqn:Hsame.
  - right; exists s; split; [discriminate|].
    exact (proj1 (dom_same_entries EV s rest) Hsame).
  - left; reflexivity.
Qed.

(** The explicit fallback is a forest with exactly the advertised sole-entry star shape. *)
Theorem flat_idom_shape {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (s : V) : ready EV g p ->
  Map.wf EV (flat_idom p) /\ forest_on EV g (flat_idom p) /\
  ((Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s) ->
    forall n, Map.get EV n (flat_idom p) = Some s <-> (reachable g n /\ n <> s)) /\
  ((forall s', ~ (Graph.entries g <> [] /\ forall x, In x (Graph.entries g) -> x = s')) ->
    forall n, Map.get EV n (flat_idom p) = None).
Proof.
  intro Hready; split.
  - destruct (dom_flat_cases EV g p) as [Hempty|[a Hsingle]].
    + rewrite Hempty; apply Map.wf_empty.
    + exact (proj1 (dom_flat_single EV g p a Hready Hsingle)).
  - split.
    + destruct (dom_flat_cases EV g p) as [Hempty|[a Hsingle]].
      * rewrite Hempty; split.
        -- intros v u Hget; rewrite Map.get_empty in Hget; discriminate.
        -- intro v; constructor; intros u Hget; rewrite Map.get_empty in Hget; discriminate.
      * pose proof (proj2 (dom_flat_single EV g p a Hready Hsingle)) as Hlookup; split.
        -- intros v u Hget; apply Hlookup in Hget; destruct Hget as [Hv [_ Heq]].
           subst u; split; [exact Hv|apply reachable_entry].
           destruct (Graph.entries g) as [|entry rest] eqn:Hentries.
           ++ destruct Hsingle as [Hnonempty _]; contradiction.
           ++ destruct Hsingle as [_ Hall].
              rewrite <- (Hall entry (or_introl eq_refl)); left; reflexivity.
        -- intro v; constructor; intros u Hget; apply Hlookup in Hget.
           destruct Hget as [_ [_ Heq]]; subst u; constructor; intros w Hget.
           apply Hlookup in Hget; destruct Hget as [_ [Hne _]]; contradiction.
    + split.
      * intro Hsingle; intro n; rewrite (proj2 (dom_flat_single EV g p s Hready Hsingle)).
        tauto.
      * intros Hnone n; destruct (dom_flat_cases EV g p) as [Hempty|[a Hsingle]].
        -- rewrite Hempty; apply Map.get_empty.
        -- exfalso; apply (Hnone a); exact Hsingle.
Qed.
