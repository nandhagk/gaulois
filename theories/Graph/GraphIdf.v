(** * Direct iterated dominance frontiers

    A priority worklist walks the dominator forest and examines outgoing join edges directly.
    For example, a definition on one arm of a diamond emits its join, without building a
    frontier map for the other vertices.
    Builds on: GraphFrontier, GraphDominators, GraphDfs and CollectionsHeap. *)

From Stdlib Require Import List Bool PArith NArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphLengauerTarjan GraphDominators GraphEdgeDominance GraphFrontier.
Import List.ListNotations.

(** Live pruning is part of every closure step, including every subsequent propagation step. *)
Inductive in_pruned_idf {V E} (g : Graph.t V E) (defs : list V) (live : V -> bool)
    : V -> Prop :=
  | pruned_idf_step : forall d n, (In d defs \/ in_pruned_idf g defs live d) ->
      in_df g d n -> live n = true -> in_pruned_idf g defs live n.

Arguments pruned_idf_step {V E g defs live} d n _ _ _.

Lemma pruned_idf_induction {V E} (g : Graph.t V E) defs live (P : V -> Prop) :
  (forall d n, In d defs -> in_df g d n -> live n = true -> P n) ->
  (forall d n, in_pruned_idf g defs live d -> P d -> in_df g d n ->
    live n = true -> P n) ->
  forall n, in_pruned_idf g defs live n -> P n.
Proof.
  intros Hseed Hstep.
  fix IH 2; intros n Hderiv; destruct Hderiv as [d n Hfrom Hdf Hlive].
  destruct Hfrom as [Hdef|Hprev].
  - exact (Hseed d n Hdef Hdf Hlive).
  - exact (Hstep d n Hprev (IH d Hprev) Hdf Hlive).
Qed.

Lemma pruned_idf_all {V E} (g : Graph.t V E) defs n :
  in_pruned_idf g defs (fun _ => true) n <-> in_idf g defs n.
Proof.
  split.
  - apply pruned_idf_induction.
    + intros d x Hdef Hdf _; apply (idf_step d x); [left; exact Hdef|exact Hdf].
    + intros d x _ IH Hdf _; apply (idf_step d x); [right; exact IH|exact Hdf].
  - apply in_idf_induction.
    + intros d x Hdef Hdf; apply (pruned_idf_step d x); auto.
    + intros d x _ IH Hdf; apply (pruned_idf_step d x); auto.
Qed.

(** * Dominator-forest facts *)

Lemma idf_path_app {V E} (g : Graph.t V E) u es w fs v :
  path g u es w -> path g w fs v -> path g u (es ++ fs) v.
Proof.
  intros Hfirst Hlast; induction Hfirst as [u|e es w Hedge Hpath IH].
  - exact Hlast.
  - cbn [app]; apply path_cons; [exact Hedge|apply IH; exact Hlast].
Qed.

Lemma idf_path_nodes {V E} (g : Graph.t V E) u es v : graph_wf g ->
  path g u es v -> In u (Graph.nodes g) -> In v (Graph.nodes g).
Proof.
  intros Hwf Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Hu.
  - exact Hu.
  - apply IH; eapply out_target_in; eassumption.
Qed.

Section ForestFacts.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.

Local Abbreviation T := (dominator_tree p).
Local Abbreviation M := (simple_lt_idom p).
Local Abbreviation F := (dom_forest p (idom T)).

Lemma idf_tree_ready : ready EV F (prepare EV F).
Proof.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest _]].
  apply dom_forest_ready; [exact Hready|exact Hmap|exact (proj1 Hforest)].
Qed.

Lemma idf_tree_node v : In v (Graph.nodes F) <-> reachable g v.
Proof.
  apply dom_live; exact Hready.
Qed.

Lemma idf_tree_edge u v : In v (Graph.out F u) <-> Map.get EV v (idom T) = Some u.
Proof.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap _].
  apply dom_edge; exact Hmap.
Qed.

Lemma idf_tree_path u es v : path F u es v -> idom_ancestor EV (idom T) u v.
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH].
  - apply rt_refl.
  - eapply rt_trans; [apply rt_step|exact IH].
    apply idf_tree_edge; exact Hedge.
Qed.

Lemma idf_tree_reaches u v : idom_ancestor EV (idom T) u v -> reaches F u v.
Proof.
  intro Hanc; induction Hanc as [u v Hget|v|u w v Huw IHuw Hwv IHwv].
  - exists [v].
    assert (Hedge : In v (Graph.out F u)) by (apply idf_tree_edge; exact Hget).
    pose proof (out_source (proj1 idf_tree_ready) u v Hedge) as Hsource.
    change (Graph.source F v = u) in Hsource.
    rewrite <- Hsource; apply path_cons; [rewrite Hsource; exact Hedge|constructor].
  - exists []; constructor.
  - destruct IHuw as [es Hfirst], IHwv as [fs Hlast].
    exists (es ++ fs); eapply idf_path_app; eassumption.
Qed.

Lemma idf_dominance_anc u v : reachable g v ->
  (dominates g u v <-> idom_ancestor EV (idom T) u v).
Proof.
  destruct (simple_lt_idom_exact EV g p Hready) as [_ [_ Hexact]].
  apply Hexact.
Qed.

Lemma idf_ancestor_comparable a b v : idom_ancestor EV (idom T) a v ->
  idom_ancestor EV (idom T) b v ->
  idom_ancestor EV (idom T) a b \/ idom_ancestor EV (idom T) b a.
Proof.
  intros Ha Hb.
  revert a b Ha Hb.
  induction (proj2 (proj1 (proj2 (simple_lt_idom_exact EV g p Hready))) v)
    as [v Hacc IH]; intros a b Ha Hb.
  destruct (dom_ancestor_last EV (idom T) a v Ha) as [Heq|[u [Hparent Hau]]].
  - subst a; right; exact Hb.
  - destruct (dom_ancestor_last EV (idom T) b v Hb) as [Heq|[w [Hparent' Hbw]]].
    + subst b; left; exact Ha.
    + assert (Heq : w = u) by congruence; subst w.
      exact (IH u Hparent a b Hau Hbw).
Qed.

Lemma idf_dominance_comparable a b v : reachable g v -> dominates g a v ->
  dominates g b v -> dominates g a b \/ dominates g b a.
Proof.
  intros Hv Ha Hb.
  destruct (idf_ancestor_comparable a b v (proj1 (idf_dominance_anc a v Hv) Ha)
    (proj1 (idf_dominance_anc b v Hv) Hb)) as [Hab|Hba].
  - left; exact (proj1 (proj2 (dominator_tree_sound EV g p Hready)) a b Hab).
  - right; exact (proj1 (proj2 (dominator_tree_sound EV g p Hready)) b a Hba).
Qed.

Lemma idf_dominance_antisym a b : reachable g a -> reachable g b ->
  dominates g a b -> dominates g b a -> a = b.
Proof.
  intros Ha Hb Hab Hba.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  apply (dom_ancestor_antisym EV g p M Hready Hmap Hforest a b).
  - apply Hexact; assumption.
  - apply Hexact; assumption.
Qed.

Lemma idf_strict_predecessor a e : In e (Graph.out g (Graph.source g e)) ->
  strictly_dominates g a (Graph.target g e) -> dominates g a (Graph.source g e).
Proof.
  intros Hedge [Hdom Hne] s es Hentry Hpath.
  specialize (Hdom s (es ++ [e]) Hentry).
  assert (Hextend : path g s (es ++ [e]) (Graph.target g e)).
  { apply (path_snoc g s es (Graph.source g e) e Hpath eq_refl Hedge). }
  destruct (Hdom Hextend) as [Heq|[x [Hin Htarget]]]; [left; exact Heq|].
  apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
  - right; exists x; auto.
  - subst x; exfalso; apply Hne; symmetry; exact Htarget.
  - contradiction.
Qed.

(** Frontier steps cannot enter the strict subtree of a previously processed definition. *)
Lemma idf_frontier_backwards a d n : in_df g d n -> strictly_dominates g a n ->
  strictly_dominates g a d.
Proof.
  intros [e [Hedge [Htarget [Hsource [Hd Hnot]]]]] Ha; subst n.
  pose proof (idf_strict_predecessor a e Hedge Ha) as Hax.
  assert (Hdr : reachable g d).
  { exact (dom_dominator_reachable g d (Graph.source g e) Hsource Hd). }
  assert (Har : reachable g a).
  { eapply dom_dominator_reachable; [exact Hsource|exact Hax]. }
  destruct (idf_dominance_comparable a d (Graph.source g e) Hsource Hax Hd)
    as [Had|Hda].
  - split; [exact Had|intro Heq; subst a; contradiction].
  - destruct (dfs_eq_dec EV d (Graph.target g e)) as [Heq|Hne].
    + subst d; exact Ha.
    + exfalso; apply Hnot; split; [|exact Hne].
      eapply dominates_trans; [exact Hda|exact (proj1 Ha)].
Qed.

(** A nested root's frontier covers every outer-root witness whose source is in its subtree. *)
Lemma idf_frontier_nested r d e :
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) ->
  dominates g r d -> dominates g d (Graph.source g e) ->
  ~ strictly_dominates g r (Graph.target g e) -> in_df g d (Graph.target g e).
Proof.
  intros Hedge Hsource Hrd Hdx Hnot.
  exists e; split; [exact Hedge|]; split; [reflexivity|].
  split; [exact Hsource|]; split; [exact Hdx|].
  intro Hstrict.
  assert (Hrn : dominates g r (Graph.target g e)).
  { eapply dominates_trans; [exact Hrd|exact (proj1 Hstrict)]. }
  apply Hnot; split; [exact Hrn|].
  intro Heq; subst r.
  assert (Hnr : reachable g (Graph.target g e)) by (eapply reachable_step; eassumption).
  assert (Hdr : reachable g d).
  { exact (dom_dominator_reachable g d (Graph.source g e) Hsource Hdx). }
  apply (proj2 Hstrict); symmetry.
  exact (idf_dominance_antisym (Graph.target g e) d Hnr Hdr Hrd (proj1 Hstrict)).
Qed.

End ForestFacts.

(** Changing only entries preserves every edge-labelled path. *)
Lemma idf_path_entries {V E} (g : Graph.t V E) roots u es v :
  path g u es v -> path (set_entries g roots) u es v.
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH].
  - constructor.
  - exact (@path_cons V E (set_entries g roots) e es v Hedge IH).
Qed.

(** A changed root list does not introduce any new path edges. *)
Lemma idf_path_entries_back {V E} (g : Graph.t V E) roots u es v :
  path (set_entries g roots) u es v -> path g u es v.
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH].
  - constructor.
  - exact (@path_cons V E g e es v Hedge IH).
Qed.

(** A successor-closed blocked set cannot obstruct a path whose endpoint is outside it. *)
Lemma idf_path_free {V E} (EV : encoding V) (g : Graph.t V E) blocked u es v :
  (forall e, In e (Graph.out g (Graph.source g e)) ->
    FinSet.mem EV (Graph.source g e) blocked = true ->
    FinSet.mem EV (Graph.target g e) blocked = true) ->
  path g u es v -> FinSet.mem EV v blocked = false ->
  FinSet.mem EV u blocked = false /\
  forall e, In e es -> FinSet.mem EV (Graph.target g e) blocked = false.
Proof.
  intros Hclosed Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Hfree.
  - split; [exact Hfree|intros e Hfalse; contradiction].
  - destruct (IH Hfree) as [Htarget Hrest]; split.
    + apply Bool.not_true_iff_false; intro Hsource.
      pose proof (Hclosed e Hedge Hsource); congruence.
    + intros x [Heq|Hin]; [subst x; exact Htarget|apply Hrest; exact Hin].
Qed.

Section SubtreeWalk.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.
Local Abbreviation T := (dominator_tree p).
Local Abbreviation F := (dom_forest p (idom T)).

(** Previously scanned subtrees remain closed under dominator-tree child edges. *)
Definition idf_scanned_closed (scanned : FinSet.t V) : Prop :=
  forall u v, FinSet.mem EV u scanned = true ->
    idom_ancestor EV (idom T) u v -> FinSet.mem EV v scanned = true.

Lemma idf_subtree_fresh scanned r v : idf_scanned_closed scanned -> reachable g r ->
  (In v (preorder (dfs (prepare EV F) scanned [r])) <->
   dominates g r v /\ reachable g v /\ FinSet.mem EV v scanned = false).
Proof.
  intros Hclosed Hr.
  assert (Hroots : incl [r] (Graph.nodes F)).
  { intros x [Heq|Hfalse]; [subst x; apply (idf_tree_node EV g p Hready); exact Hr|
      contradiction]. }
  pose proof (dfs_exact EV F (prepare EV F) v [r] scanned
    (idf_tree_ready EV g p Hready) Hroots) as [Hreach [_ [_ Hpre]]].
  rewrite Hpre, Hreach, reachable_without.
  split.
  - intros [s [es [[Heq|Hfalse] [Hpath [Hfree Htargets]]]]]; [subst s|contradiction].
    pose proof (idf_path_entries_back F [r] r es v Hpath) as Hpath'.
    assert (Hv : reachable g v).
    { apply (idf_tree_node EV g p Hready).
      apply (idf_path_nodes F r es v (proj1 (idf_tree_ready EV g p Hready)) Hpath').
      apply (idf_tree_node EV g p Hready); exact Hr. }
    split.
    + apply (proj2 (idf_dominance_anc EV g p Hready r v Hv)).
      apply (idf_tree_path EV g p Hready r es v); exact Hpath'.
    + split; [exact Hv|].
      destruct (path_endpoint _ _ _ _ Hpath) as [Heq|[e [Hin Heq]]].
      * subst v; exact Hfree.
      * subst v; apply Htargets; exact Hin.
  - intros [Hdom [Hv Hfree]].
    destruct (idf_tree_reaches EV g p Hready r v
      (proj1 (idf_dominance_anc EV g p Hready r v Hv) Hdom)) as [es Hpath].
    assert (Hedgeclosed : forall e, In e (Graph.out F (Graph.source F e)) ->
      FinSet.mem EV (Graph.source F e) scanned = true ->
      FinSet.mem EV (Graph.target F e) scanned = true).
    { intros e Hedge Hsource; apply (Hclosed (Graph.source F e) e Hsource).
      apply rt_step; apply (idf_tree_edge EV g p Hready); exact Hedge. }
    destruct (idf_path_free EV F scanned r es v Hedgeclosed Hpath Hfree)
      as [Hrfree Htargets].
    exists r, es; split; [left; reflexivity|]; split.
    + apply idf_path_entries; exact Hpath.
    + split; assumption.
Qed.

End SubtreeWalk.

(** * Priority worklist and direct edge discovery *)

(** Read a cached level, with level one reserved for roots and absent parents. *)
Definition idf_level {V} (EV : encoding V) (levels : Map.t V positive) (v : V) : positive :=
  match Map.get EV v levels with
  | Some level => level
  | None => xH
  end.

(** A parent-before-child pass assigns each child its parent's successor level. *)
Definition idf_level_step {V} (EV : encoding V) (parents : Map.t V V)
    (levels : Map.t V positive) (v : V) : Map.t V positive :=
  Map.set EV v
    (match Map.get EV v parents with
     | Some parent => Pos.succ (idf_level EV levels parent)
     | None => xH
     end) levels.

(** Number levels once using the cached forest graph and its prepared child index. *)
Definition idf_levels {V} (EV : encoding V) (parents : Map.t V V)
    (forest : Graph.t V V) (tree_index : prepared EV forest) : Map.t V positive :=
  fold_left (idf_level_step EV parents)
    (rpo (dfs tree_index FinSet.empty (Graph.entries forest))) Map.empty.

Lemma idf_level_pass_preserves {V} (EV : encoding V) parents order levels v : ~ In v order ->
  Map.get EV v (fold_left (idf_level_step EV parents) order levels) = Map.get EV v levels.
Proof.
  revert levels; induction order as [|x order IH]; intros levels Hnot; [reflexivity|].
  cbn [fold_left]; rewrite IH by (intro Hin; apply Hnot; right; exact Hin).
  unfold idf_level_step; apply Map.get_set_other; intro Heq; subst v; apply Hnot; left; reflexivity.
Qed.

Lemma idf_level_pass_domain {V} (EV : encoding V) parents order levels v :
  (exists level, Map.get EV v (fold_left (idf_level_step EV parents) order levels) = Some level)
    <-> In v order \/ exists level, Map.get EV v levels = Some level.
Proof.
  revert levels; induction order as [|x order IH]; intro levels; cbn [fold_left In].
  - tauto.
  - rewrite IH; unfold idf_level_step.
    destruct (dfs_eq_dec EV v x) as [Heq|Hne].
    + subst x; rewrite Map.get_set_same; split; [intro H; left; left; reflexivity|].
      intro H; right; eexists; reflexivity.
    + rewrite Map.get_set_other by exact Hne; intuition congruence.
Qed.

(** Every parent in the input order is strictly before its child. *)
Definition idf_level_order {V} (EV : encoding V) (parents : Map.t V V) (order : list V)
    : Prop :=
  forall prefix v rest, order = prefix ++ v :: rest ->
    forall u, Map.get EV v parents = Some u -> ~ In u (v :: rest).

Lemma idf_level_pass_equations {V} (EV : encoding V) parents order levels :
  NoDup order -> idf_level_order EV parents order ->
  forall v, In v order ->
  Map.get EV v (fold_left (idf_level_step EV parents) order levels) =
    Some (match Map.get EV v parents with
    | Some u => Pos.succ
        (idf_level EV (fold_left (idf_level_step EV parents) order levels) u)
    | None => xH
    end).
Proof.
  revert levels; induction order as [|x order IH]; intros levels Hnd Horder v Hin;
    [contradiction|].
  inversion Hnd as [|? ? Hfresh Htail]; subst.
  destruct Hin as [Heq|Hin].
  - subst v; cbn [fold_left].
    rewrite idf_level_pass_preserves by exact Hfresh; unfold idf_level_step at 1.
    rewrite Map.get_set_same; destruct (Map.get EV x parents) as [u|] eqn:Hparent;
      [|reflexivity].
    assert (Hu : ~ In u (x :: order)) by (exact (Horder [] x order eq_refl u Hparent)).
    unfold idf_level; change
      (Some (Pos.succ (match Map.get EV u levels with Some k => k | None => xH end)) =
       Some (Pos.succ (match Map.get EV u
         (fold_left (idf_level_step EV parents) (x :: order) levels) with
         | Some k => k
         | None => xH
         end))).
    rewrite idf_level_pass_preserves by exact Hu; reflexivity.
  - cbn [fold_left]; apply IH; try assumption.
    intros prefix v' rest Heq u Hparent.
    apply (Horder (x :: prefix) v' rest); [cbn; rewrite Heq; reflexivity|exact Hparent].
Qed.

Lemma idf_level_pass_bound {V} (EV : encoding V) parents order levels bound :
  1 <= bound ->
  (forall v level, Map.get EV v levels = Some level -> Pos.to_nat level <= bound) ->
  forall v level, Map.get EV v (fold_left (idf_level_step EV parents) order levels) = Some level ->
    Pos.to_nat level <= length order + bound.
Proof.
  revert levels bound; induction order as [|x order IH]; intros levels bound Hpositive Hbound
    v level Hget; cbn [fold_left length] in *.
  - exact (Hbound v level Hget).
  - specialize (IH (idf_level_step EV parents levels x) (S bound) ltac:(lia)).
    assert (Hstep : forall u k, Map.get EV u (idf_level_step EV parents levels x) = Some k ->
      Pos.to_nat k <= S bound).
    { intros u k Hlookup; unfold idf_level_step in Hlookup.
      destruct (dfs_eq_dec EV u x) as [Heq|Hne].
      - subst u; rewrite Map.get_set_same in Hlookup; inversion Hlookup; subst k.
        destruct (Map.get EV x parents) as [parent|]; [|cbn; lia].
        rewrite Pos2Nat.inj_succ; unfold idf_level.
        destruct (Map.get EV parent levels) as [parentlevel|] eqn:Hparent;
          [specialize (Hbound parent parentlevel Hparent); lia|cbn; lia].
      - rewrite Map.get_set_other in Hlookup by exact Hne.
        specialize (Hbound u k Hlookup); lia. }
    specialize (IH Hstep v level Hget); lia.
Qed.

Lemma idf_before_prefix {V} (prefix : list V) v rest u : NoDup (prefix ++ v :: rest) ->
  before (prefix ++ v :: rest) u v -> In u prefix.
Proof.
  induction prefix as [|x prefix IH]; cbn; intros Hnd Hbefore.
  - exfalso; exact (dfs_before_head_false v rest u Hnd Hbefore).
  - apply dfs_before_cons in Hbefore; destruct Hbefore as [[Heq _]|Hbefore].
    + left; symmetry; exact Heq.
    + right; apply IH; [inversion Hnd; assumption|exact Hbefore].
Qed.

Lemma idf_nodup_disjoint {V} (prefix rest : list V) : NoDup (prefix ++ rest) ->
  forall u, In u prefix -> ~ In u rest.
Proof.
  induction prefix as [|x prefix IH]; intros Hnd u Hin Hrest; [contradiction|].
  inversion Hnd as [|? ? Hfresh Htail]; subst; destruct Hin as [Heq|Hin].
  - subst u; apply Hfresh; apply in_or_app; right; exact Hrest.
  - exact (IH Htail u Hin Hrest).
Qed.

Section LevelFacts.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.
Local Abbreviation T := (dominator_tree p).
Local Abbreviation F := (dom_forest p (idom T)).
Local Abbreviation R := (dom_search p (idom T)).
Local Abbreviation D := (idf_levels EV (idom T) F (prepare EV F)).

Lemma idf_level_nodes v : In v (rpo R) <-> reachable g v.
Proof.
  unfold rpo; rewrite <- in_rev.
  pose proof (dfs_exact EV F (prepare EV F) v (Graph.entries F) FinSet.empty
    (idf_tree_ready EV g p Hready) (entries_in (proj1 (idf_tree_ready EV g p Hready))))
    as [_ [_ [Hperm Hpre]]].
  assert (Hsame : In v (postorder R) <-> In v (preorder R)).
  { split.
    - apply (Permutation.Permutation_in v (Permutation.Permutation_sym Hperm)).
    - apply (Permutation.Permutation_in v Hperm). }
  rewrite Hsame.
  rewrite Hpre; destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest _]].
  apply (dom_forest_coverage EV g p (idom T) Hready Hmap (proj1 Hforest) (proj2 Hforest)).
Qed.

Lemma idf_level_numbers v : (exists level, Map.get EV v D = Some level) <-> reachable g v.
Proof.
  unfold idf_levels; rewrite idf_level_pass_domain, Map.get_empty.
  change (In v (rpo R) \/ (exists level : positive, None = Some level) <-> reachable g v).
  rewrite idf_level_nodes; split; [intros [H|[k Hfalse]]; [exact H|discriminate]|auto].
Qed.

Lemma idf_levels_order : idf_level_order EV (idom T) (rpo R).
Proof.
  intros prefix v rest Horder u Hparent Hin.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest _]].
  assert (Hv : FinSet.mem EV v (visited R) = true).
  { apply (dom_forest_coverage EV g p (idom T) Hready Hmap (proj1 Hforest) (proj2 Hforest)).
    apply idf_level_nodes; rewrite Horder; apply in_or_app; right; left; reflexivity. }
  destruct (dom_search_parent_complete EV g p (idom T) Hready Hmap (proj1 Hforest)
    v u Hv Hparent) as [e [Hedge Hsource]].
  pose proof (proj1 (rpo_order EV F (prepare EV F) v (Graph.entries F) FinSet.empty
    (idf_tree_ready EV g p Hready) (entries_in (proj1 (idf_tree_ready EV g p Hready))))
    e Hedge) as Hbefore.
  change (before (rpo R) (Graph.source F e) v) in Hbefore.
  rewrite Hsource, Horder in Hbefore.
  pose proof (dfs_rpo_nodup EV F (prepare EV F) (Graph.entries F)
    (idf_tree_ready EV g p Hready) (entries_in (proj1 (idf_tree_ready EV g p Hready)))) as Hnd.
  change (NoDup (rpo R)) in Hnd; rewrite Horder in Hnd.
  pose proof (idf_before_prefix prefix v rest u Hnd Hbefore) as Hprefix.
  exact (idf_nodup_disjoint prefix (v :: rest) Hnd u Hprefix Hin).
Qed.

(** Cached levels increase by exactly one on every dominator-tree edge. *)
Lemma idf_levels_parent v u : Map.get EV v (idom T) = Some u ->
  idf_level EV D v = Pos.succ (idf_level EV D u).
Proof.
  intro Hparent.
  destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hdomain _] _]].
  assert (Hv : In v (rpo R)) by (apply idf_level_nodes; exact (proj1 (Hdomain v u Hparent))).
  pose proof (idf_level_pass_equations EV (idom T) (rpo R) Map.empty
    (dfs_rpo_nodup EV F (prepare EV F) (Graph.entries F) (idf_tree_ready EV g p Hready)
      (entries_in (proj1 (idf_tree_ready EV g p Hready)))) idf_levels_order v Hv) as Hlevel.
  change (Map.get EV v D = Some (match Map.get EV v (idom T) with
    | Some parent => Pos.succ (idf_level EV D parent)
    | None => xH
    end)) in Hlevel.
  rewrite Hparent in Hlevel; unfold idf_level at 1; rewrite Hlevel; reflexivity.
Qed.

(** Parentless reachable vertices receive level one. *)
Lemma idf_levels_root v : reachable g v -> Map.get EV v (idom T) = None ->
  Map.get EV v D = Some xH.
Proof.
  intros Hv Hparent.
  pose proof (idf_level_pass_equations EV (idom T) (rpo R) Map.empty
    (dfs_rpo_nodup EV F (prepare EV F) (Graph.entries F) (idf_tree_ready EV g p Hready)
      (entries_in (proj1 (idf_tree_ready EV g p Hready)))) idf_levels_order v
      (proj2 (idf_level_nodes v) Hv)) as Hlevel.
  rewrite Hparent in Hlevel; exact Hlevel.
Qed.

Lemma idf_levels_ancestor a b : idom_ancestor EV (idom T) a b ->
  a = b \/ Pos.lt (idf_level EV D a) (idf_level EV D b).
Proof.
  intro Hanc; induction Hanc as [a b Hparent|v|a w b Haw IHaw Hwb IHwb].
  - right; rewrite (idf_levels_parent b a Hparent); apply Pos.lt_succ_diag_r.
  - left; reflexivity.
  - destruct IHaw as [Heq|Hlt], IHwb as [Heq'|Hlt']; subst;
      try (left; reflexivity); right; lia.
Qed.

Lemma idf_levels_bound v level : Map.get EV v D = Some level ->
  Pos.to_nat level <= S (length (Graph.nodes g)).
Proof.
  intro Hget.
  pose proof (idf_level_pass_bound EV (idom T) (rpo R) Map.empty 1 ltac:(lia)
    ltac:(intros x k Hfalse; rewrite Map.get_empty in Hfalse; discriminate) v level Hget)
    as Hbound.
  assert (Hlength : length (rpo R) <= length (Graph.nodes g)).
  { apply NoDup_incl_length.
    - apply (dfs_rpo_nodup EV F (prepare EV F) (Graph.entries F)
        (idf_tree_ready EV g p Hready) (entries_in (proj1 (idf_tree_ready EV g p Hready)))).
    - intros x Hin; apply (reachable_in_nodes g x (proj1 Hready)).
      apply idf_level_nodes; exact Hin. }
  lia.
Qed.

End LevelFacts.

(** Deeper dominator-tree levels receive smaller queue priorities. *)
Definition idf_priority {V} (EV : encoding V) (ceiling : positive) (levels : Map.t V positive)
    (v : V) : positive :=
  match Map.get EV v levels with
  | Some rank => Pos.sub ceiling rank
  | None => ceiling
  end.

Module IdfState.

(** The scanned set is shared by all roots, while emitted and processed vertices are distinct. *)
Record t (V : Type) : Type := Make {
  pending : PQueue.t V;
  emitted : FinSet.t V;
  scanned : FinSet.t V;
  processed : FinSet.t V;
  trace : list V;
  edge_visits : N;
  output_count : N
}.

Arguments Make {V}.
Arguments pending {V}.
Arguments emitted {V}.
Arguments scanned {V}.
Arguments processed {V}.
Arguments trace {V}.
Arguments edge_visits {V}.
Arguments output_count {V}.

End IdfState.
Import IdfState.

(** A root with no dominator-forest number is unreachable and contributes no frontier. *)
Definition idf_seed {V} (EV : encoding V) ceiling (levels : Map.t V positive)
    (q : PQueue.t V) (v : V) : PQueue.t V :=
  match Map.get EV v levels with
  | Some _ => PQueue.push EV (idf_priority EV ceiling levels v) v q
  | None => q
  end.

(** Definitions enter the queue but are emitted only if a frontier step rediscovers them. *)
Definition idf_initial {V} (EV : encoding V) ceiling (levels : Map.t V positive)
    (defs : list V) : IdfState.t V :=
  Make (fold_left (idf_seed EV ceiling levels) defs PQueue.empty)
    FinSet.empty FinSet.empty FinSet.empty [] 0%N 0%N.

(** An emitted vertex enters the queue once unless it has already been processed. *)
Definition idf_emit {V} (EV : encoding V) ceiling (levels : Map.t V positive)
    (st : IdfState.t V) (v : V) : IdfState.t V :=
  Make (if FinSet.mem EV v (processed st) then pending st
        else PQueue.push EV (idf_priority EV ceiling levels v) v (pending st))
    (FinSet.add EV v (emitted st)) (scanned st) (processed st) (trace st)
    (edge_visits st)
    (if FinSet.mem EV v (emitted st) then output_count st else N.succ (output_count st)).

(** A join edge contributes exactly when its target is outside the root's strict subtree. *)
Definition idf_join {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    (live : V -> bool) (root : V) (e : E) : bool :=
  negb (frontier_blocked EV t (Map.get EV (Graph.target g e) (idom t)) root) &&
    live (Graph.target g e).

(** Collecting one adjacency list counts every edge independently of emitted targets. *)
Definition idf_collect_edge {V E} (EV : encoding V) (g : Graph.t V E) (t : dom_tree V)
    live root (acc : list V * N) (e : E) : list V * N :=
  (if idf_join EV g t live root e then Graph.target g e :: fst acc else fst acc,
    N.succ (snd acc)).

(** The prepared graph supplies each newly scanned source's adjacency list. *)
Definition idf_collect_node {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) t live root (acc : list V * N) (v : V) : list V * N :=
  fold_left (idf_collect_edge EV g t live root) (succ_edges p v) acc.

(** A root scans fresh vertices using the shared forest graph and index, then emits its joins. *)
Definition idf_work_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (forest : Graph.t V V)
    (tree_index : prepared EV forest) (levels : Map.t V positive) live
    (st : IdfState.t V) : IdfState.t V :=
  match PQueue.pop EV (pending st) with
  | None => st
  | Some (_, root, rest) =>
    let fresh := preorder (dfs tree_index (scanned st) [root]) in
    let collected := fold_left (idf_collect_node p t live root) fresh ([], 0%N) in
    let scanned' := fold_left (fun s v => FinSet.add EV v s) fresh (scanned st) in
    let started := Make rest (emitted st) scanned' (FinSet.add EV root (processed st))
      (root :: trace st) (N.add (edge_visits st) (snd collected)) (output_count st) in
    fold_left (idf_emit EV (fuel p) levels) (fst collected) started
  end.

(** Binary iteration stops immediately once the priority worklist is empty. *)
Fixpoint idf_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) t (forest : Graph.t V V) (tree_index : prepared EV forest)
    levels live (k : positive) (st : IdfState.t V)
    : IdfState.t V :=
  if PQueue.is_empty (pending st) then st
  else
    match k with
    | xH => idf_work_step p t forest tree_index levels live st
    | xO half => idf_run p t forest tree_index levels live half
        (idf_run p t forest tree_index levels live half st)
    | xI half => idf_work_step p t forest tree_index levels live
        (idf_run p t forest tree_index levels live half
          (idf_run p t forest tree_index levels live half st))
    end.

(** The direct query builds the child index once and shares its visited set across all roots. *)
Definition direct_pruned_idf {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) (live : V -> bool) : FinSet.t V :=
  let forest := dom_forest p (idom t) in
  let tree_index := prepare EV forest in
  let levels := idf_levels EV (idom t) forest tree_index in
  emitted (idf_run p t forest tree_index levels live (Pos.of_succ_nat (length (Graph.nodes g)))
    (idf_initial EV (fuel p) levels defs)).

(** Without live pruning the same DJ traversal computes the ordinary least frontier closure. *)
Definition direct_idf {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (defs : list V) : FinSet.t V :=
  direct_pruned_idf p t defs (fun _ => true).

(** * Discovery and accounting *)

Lemma idf_collect_edges_spec {V E} (EV : encoding V) (g : Graph.t V E) t live root
    edges acc n :
  In n (fst (fold_left (idf_collect_edge EV g t live root) edges acc)) <->
  In n (fst acc) \/ exists e, In e edges /\ Graph.target g e = n /\
    idf_join EV g t live root e = true.
Proof.
  revert acc; induction edges as [|e edges IH]; intro acc; cbn [fold_left].
  - split; [intro H; left; exact H|intros [H|[e [Hfalse _]]]; [exact H|contradiction]].
  - rewrite IH; unfold idf_collect_edge; cbn [fst].
    destruct (idf_join EV g t live root e) eqn:Hjoin; cbn [In];
      split; intros H.
    + destruct H as [[Heq|Hin]|[a [Hin Hrest]]].
      * right; exists e; auto.
      * left; exact Hin.
      * right; exists a; auto.
    + destruct H as [Hin|[a [[Heq|Hin] [Htarget Ha]]]].
      * left; right; exact Hin.
      * subst a; left; left; exact Htarget.
      * right; exists a; auto.
    + destruct H as [Hin|[a [Hin Hrest]]]; [left; exact Hin|right; exists a; auto].
    + destruct H as [Hin|[a [[Heq|Hin] [Htarget Ha]]]].
      * left; exact Hin.
      * subst a; congruence.
      * right; exists a; auto.
Qed.

Lemma idf_collect_edges_count {V E} (EV : encoding V) (g : Graph.t V E) t live root
    edges acc :
  snd (fold_left (idf_collect_edge EV g t live root) edges acc) =
    (N.of_nat (length edges) + snd acc)%N.
Proof.
  revert acc; induction edges as [|e edges IH]; intro acc; cbn [fold_left length].
  - reflexivity.
  - rewrite IH; cbn [idf_collect_edge snd]; rewrite Nat2N.inj_succ; lia.
Qed.

Lemma idf_collect_nodes_spec {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) t live root nodes acc n :
  In n (fst (fold_left (idf_collect_node p t live root) nodes acc)) <->
  In n (fst acc) \/ exists u e, In u nodes /\ In e (succ_edges p u) /\
    Graph.target g e = n /\ idf_join EV g t live root e = true.
Proof.
  revert acc; induction nodes as [|u nodes IH]; intro acc; cbn [fold_left].
  - split; [intro H; left; exact H|intros [H|[u [e [Hfalse _]]]];
      [exact H|contradiction]].
  - rewrite IH; unfold idf_collect_node; rewrite idf_collect_edges_spec; cbn [In].
    split.
    + intros [[Hin|[e Hrest]]|[v [e [Hin Hrest]]]]; [left; exact Hin| |].
      * right; exists u, e; auto.
      * right; exists v, e; auto.
    + intros [Hin|[v [e [[Heq|Hin] Hrest]]]].
      * left; left; exact Hin.
      * subst v; left; right; exists e; exact Hrest.
      * right; exists v, e; auto.
Qed.

(** The edge counter counts adjacency entries, including parallel edges and dead targets. *)
Lemma idf_collect_nodes_count {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) t live root nodes acc :
  snd (fold_left (idf_collect_node p t live root) nodes acc) =
    (fold_right (fun v count => N.of_nat (length (succ_edges p v)) + count)%N 0%N nodes +
      snd acc)%N.
Proof.
  revert acc; induction nodes as [|v nodes IH]; intro acc; cbn [fold_left fold_right].
  - reflexivity.
  - rewrite IH; unfold idf_collect_node; rewrite idf_collect_edges_count; lia.
Qed.

(** Every priority insertion requested by discovery is charged to a visited outgoing edge. *)
Lemma idf_collect_edges_output_bound {V E} (EV : encoding V) (g : Graph.t V E) t live root
    edges acc :
  (N.of_nat (length (fst (fold_left (idf_collect_edge EV g t live root) edges acc))) +
      snd acc <= N.of_nat (length (fst acc)) +
      snd (fold_left (idf_collect_edge EV g t live root) edges acc))%N.
Proof.
  revert acc; induction edges as [|e edges IH]; intro acc; cbn [fold_left]; [lia|].
  specialize (IH (idf_collect_edge EV g t live root acc e)).
  cbn [idf_collect_edge fst snd] in IH.
  destruct (idf_join EV g t live root e); cbn [length] in IH;
    try rewrite Nat2N.inj_succ in IH; lia.
Qed.

Lemma idf_collect_nodes_output_bound {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) t live root nodes acc :
  (N.of_nat (length (fst (fold_left (idf_collect_node p t live root) nodes acc))) +
      snd acc <= N.of_nat (length (fst acc)) +
      snd (fold_left (idf_collect_node p t live root) nodes acc))%N.
Proof.
  revert acc; induction nodes as [|v nodes IH]; intro acc; cbn [fold_left]; [lia|].
  specialize (IH (idf_collect_node p t live root acc v)).
  pose proof (idf_collect_edges_output_bound EV g t live root (succ_edges p v) acc) as Hedges.
  change (N.of_nat (length (fst (idf_collect_node p t live root acc v))) + snd acc <=
    N.of_nat (length (fst acc)) + snd (idf_collect_node p t live root acc v))%N in Hedges.
  lia.
Qed.

Section Discovery.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.
Local Abbreviation T := (dominator_tree p).

Lemma idf_join_exact root e live : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> dominates g root (Graph.source g e) ->
  (idf_join EV g T live root e = true <->
   ~ strictly_dominates g root (Graph.target g e) /\ live (Graph.target g e) = true).
Proof.
  intros Hedge Hsource Hdom.
  pose proof (dominance_chain EV g p e Hready (dominator_exact_true EV g p Hready)
    Hedge Hsource root) as Hchain.
  pose proof (proj2 (proj1 (dominator_tree_exact EV g p Hready
    (dominator_exact_true EV g p Hready)) root (Graph.source g e) Hsource) Hdom)
    as Hquery.
  unfold idf_join; rewrite Bool.andb_true_iff, Bool.negb_true_iff, frontier_blocked_false.
  tauto.
Qed.

(** Fresh subtree sources discover precisely their eligible outgoing frontier witnesses. *)
Lemma idf_discovery root live fresh n :
  (forall v, In v fresh -> dominates g root v /\ reachable g v) ->
  (In n (fst (fold_left (idf_collect_node p T live root) fresh ([], 0%N))) <->
   exists e, In (Graph.source g e) fresh /\ In e (Graph.out g (Graph.source g e)) /\
     Graph.target g e = n /\ ~ strictly_dominates g root n /\ live n = true).
Proof.
  intro Hfresh; rewrite idf_collect_nodes_spec; cbn [fst In].
  split.
  - intros [Hfalse|[v [e [Hv [Hedge [Htarget Hjoin]]]]]]; [contradiction|].
    destruct (Hfresh v Hv) as [Hdom Hreach].
    rewrite (succ_agrees (proj2 (proj2 Hready)) v
      (reachable_in_nodes g v (proj1 Hready) Hreach)) in Hedge.
    pose proof (out_source (proj1 Hready) v e Hedge) as Hsource; subst v.
    apply idf_join_exact in Hjoin; try assumption.
    exists e; rewrite Htarget in Hjoin; tauto.
  - intros [e [Hsource [Hedge [Htarget [Hnot Hlive]]]]].
    right; exists (Graph.source g e), e; repeat split; try assumption.
    + rewrite (succ_agrees (proj2 (proj2 Hready)) _
        (reachable_in_nodes g _ (proj1 Hready) (proj2 (Hfresh _ Hsource)))); exact Hedge.
    + apply idf_join_exact; try assumption; [exact (proj2 (Hfresh _ Hsource))|
        exact (proj1 (Hfresh _ Hsource))|].
      rewrite Htarget; split; assumption.
Qed.

Lemma idf_discovery_sound root live fresh n :
  (forall v, In v fresh -> dominates g root v /\ reachable g v) ->
  In n (fst (fold_left (idf_collect_node p T live root) fresh ([], 0%N))) ->
  in_df g root n /\ live n = true.
Proof.
  intros Hfresh Hin; apply (idf_discovery root live fresh n Hfresh) in Hin.
  destruct Hin as [e [Hsource [Hedge [Htarget [Hnot Hlive]]]]]; split; [|exact Hlive].
  exists e; split; [exact Hedge|]; split; [exact Htarget|].
  destruct (Hfresh _ Hsource) as [Hdom Hreach]; auto.
Qed.

End Discovery.

(** * Queue membership and emission *)

(** Waiting means that the priority queue has a live binding for the vertex. *)
Definition idf_waiting {V} (EV : encoding V) (q : PQueue.t V) (v : V) : Prop :=
  exists rank, PQueue.priority EV v q = Some rank.

(** A queue uses the one fixed priority obtained from the dominator-forest numbering. *)
Definition idf_ranked {V} (EV : encoding V) ceiling (levels : Map.t V positive) (q : PQueue.t V)
    : Prop :=
  forall v rank, PQueue.priority EV v q = Some rank ->
    rank = idf_priority EV ceiling levels v.

Lemma idf_waiting_empty {V} (EV : encoding V) v : ~ idf_waiting EV (@PQueue.empty V) v.
Proof.
  intros [rank Hget]; rewrite PQueue.priority_empty in Hget; discriminate.
Qed.

Lemma idf_waiting_push {V} (EV : encoding V) q rank x v : PQueue.wf EV q ->
  (idf_waiting EV (PQueue.push EV rank x q) v <-> v = x \/ idf_waiting EV q v).
Proof.
  intro Hwf; destruct (dfs_eq_dec EV v x) as [Heq|Hne].
  - subst x; unfold idf_waiting; rewrite PQueue.priority_push_same by exact Hwf.
    split; [intro H; left; reflexivity|intro H; eexists; reflexivity].
  - unfold idf_waiting; rewrite PQueue.priority_push_other by assumption; tauto.
Qed.

Lemma idf_ranked_push {V} (EV : encoding V) ceiling t q v :
  PQueue.wf EV q -> idf_ranked EV ceiling t q ->
  idf_ranked EV ceiling t (PQueue.push EV (idf_priority EV ceiling t v) v q).
Proof.
  intros Hwf Hrank x rank Hget; destruct (dfs_eq_dec EV x v) as [Heq|Hne].
  - subst x; rewrite PQueue.priority_push_same in Hget by exact Hwf.
    destruct (PQueue.priority EV v q) as [old|] eqn:Hold.
    + rewrite (Hrank v old Hold), Pos.min_id in Hget; inversion Hget; reflexivity.
    + inversion Hget; reflexivity.
  - rewrite PQueue.priority_push_other in Hget by assumption; apply Hrank; exact Hget.
Qed.

Lemma idf_waiting_pop {V} (EV : encoding V) q rank root rest : PQueue.wf EV q ->
  PQueue.pop EV q = Some (rank, root, rest) ->
  idf_waiting EV q root /\
  (forall v, idf_waiting EV rest v <-> idf_waiting EV q v /\ v <> root).
Proof.
  intros Hwf Hpop.
  destruct (PQueue.pop_min EV q rest rank root Hwf Hpop) as [Hroot _].
  destruct (PQueue.pop_rest EV q rest rank root Hwf Hpop) as [Hnone [Hother _]].
  split; [exists rank; exact Hroot|].
  intro v; destruct (dfs_eq_dec EV v root) as [Heq|Hne].
  - subst v; unfold idf_waiting; rewrite Hnone; split.
    + intros [r Hfalse]; discriminate.
    + intros [_ Hfalse]; contradiction.
  - unfold idf_waiting; rewrite Hother by exact Hne; tauto.
Qed.

Lemma idf_ranked_pop {V} (EV : encoding V) ceiling t q rank root rest :
  PQueue.wf EV q -> idf_ranked EV ceiling t q ->
  PQueue.pop EV q = Some (rank, root, rest) -> idf_ranked EV ceiling t rest.
Proof.
  intros Hwf Hrank Hpop v value Hget.
  destruct (PQueue.pop_rest EV q rest rank root Hwf Hpop) as [Hnone [Hother _]].
  destruct (dfs_eq_dec EV v root) as [Heq|Hne].
  - subst v; rewrite Hnone in Hget; discriminate.
  - rewrite Hother in Hget by exact Hne; apply Hrank; exact Hget.
Qed.

Lemma idf_emit_waiting {V} (EV : encoding V) ceiling t st x v :
  PQueue.wf EV (pending st) ->
  (idf_waiting EV (pending (idf_emit EV ceiling t st x)) v <->
   idf_waiting EV (pending st) v \/ v = x /\ FinSet.mem EV x (processed st) = false).
Proof.
  intro Hwf; cbn [idf_emit pending].
  destruct (FinSet.mem EV x (processed st)) eqn:Hdone.
  - split; [intro H; left; exact H|intros [H|[_ Hfalse]]; [exact H|discriminate]].
  - rewrite idf_waiting_push by exact Hwf; tauto.
Qed.

Lemma idf_emit_many_frames {V} (EV : encoding V) ceiling t xs st :
  scanned (fold_left (idf_emit EV ceiling t) xs st) = scanned st /\
  processed (fold_left (idf_emit EV ceiling t) xs st) = processed st /\
  trace (fold_left (idf_emit EV ceiling t) xs st) = trace st /\
  edge_visits (fold_left (idf_emit EV ceiling t) xs st) = edge_visits st.
Proof.
  revert st; induction xs as [|x xs IH]; intro st; cbn [fold_left]; [auto|].
  exact (IH (idf_emit EV ceiling t st x)).
Qed.

Lemma idf_emit_many_wf {V} (EV : encoding V) ceiling t xs st :
  PQueue.wf EV (pending st) -> FinSet.wf EV (emitted st) ->
  PQueue.wf EV (pending (fold_left (idf_emit EV ceiling t) xs st)) /\
  FinSet.wf EV (emitted (fold_left (idf_emit EV ceiling t) xs st)).
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hq Ho; [auto|].
  cbn [fold_left]; apply IH; cbn [idf_emit pending emitted].
  - destruct (FinSet.mem EV x (processed st)); [exact Hq|apply PQueue.wf_push; exact Hq].
  - apply Map.wf_set; exact Ho.
Qed.

Lemma idf_emit_many_ranked {V} (EV : encoding V) ceiling t xs st :
  PQueue.wf EV (pending st) -> idf_ranked EV ceiling t (pending st) ->
  idf_ranked EV ceiling t (pending (fold_left (idf_emit EV ceiling t) xs st)).
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hq Hr; [exact Hr|].
  cbn [fold_left]; apply IH; cbn [idf_emit pending].
  - destruct (FinSet.mem EV x (processed st)); [exact Hq|apply PQueue.wf_push; exact Hq].
  - destruct (FinSet.mem EV x (processed st)); [exact Hr|apply idf_ranked_push; assumption].
Qed.

Lemma idf_emit_many_output {V} (EV : encoding V) ceiling t xs st v :
  FinSet.mem EV v (emitted (fold_left (idf_emit EV ceiling t) xs st)) = true <->
  FinSet.mem EV v (emitted st) = true \/ In v xs.
Proof.
  revert st; induction xs as [|x xs IH]; intro st; cbn [fold_left In].
  - tauto.
  - rewrite IH; cbn [idf_emit emitted]; rewrite FinSet.mem_add; intuition congruence.
Qed.

Lemma idf_emit_many_waiting {V} (EV : encoding V) ceiling t xs st v :
  PQueue.wf EV (pending st) ->
  (idf_waiting EV (pending (fold_left (idf_emit EV ceiling t) xs st)) v <->
   idf_waiting EV (pending st) v \/ In v xs /\ FinSet.mem EV v (processed st) = false).
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hwf; cbn [fold_left In].
  - tauto.
  - rewrite IH.
    + rewrite idf_emit_waiting by exact Hwf; cbn [idf_emit processed]; intuition congruence.
    + cbn [idf_emit pending]; destruct (FinSet.mem EV x (processed st));
        [exact Hwf|apply PQueue.wf_push; exact Hwf].
Qed.

(** Emission counts each distinct output once and leaves edge accounting independent. *)
Lemma idf_emit_count {V} (EV : encoding V) ceiling t st v :
  output_count st = N.of_nat (FinSet.size (emitted st)) ->
  output_count (idf_emit EV ceiling t st v) =
    N.of_nat (FinSet.size (emitted (idf_emit EV ceiling t st v))).
Proof.
  intro Hcount; cbn [idf_emit output_count emitted].
  unfold FinSet.size, FinSet.add; rewrite PQueue.map_size_set.
  unfold FinSet.mem, Map.mem.
  destruct (Map.get EV v (emitted st)); [exact Hcount|].
  rewrite Nat2N.inj_succ; f_equal; exact Hcount.
Qed.

Lemma idf_emit_many_count {V} (EV : encoding V) ceiling t xs st :
  output_count st = N.of_nat (FinSet.size (emitted st)) ->
  output_count (fold_left (idf_emit EV ceiling t) xs st) =
    N.of_nat (FinSet.size (emitted (fold_left (idf_emit EV ceiling t) xs st))).
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hcount; [exact Hcount|].
  cbn [fold_left]; apply IH; apply idf_emit_count; exact Hcount.
Qed.

Lemma idf_seed_many_wf {V} (EV : encoding V) ceiling t defs q : PQueue.wf EV q ->
  PQueue.wf EV (fold_left (idf_seed EV ceiling t) defs q).
Proof.
  revert q; induction defs as [|v defs IH]; intros q Hwf; [exact Hwf|].
  cbn [fold_left]; apply IH; unfold idf_seed.
  destruct (Map.get EV v t); [apply PQueue.wf_push; exact Hwf|exact Hwf].
Qed.

Lemma idf_seed_many_ranked {V} (EV : encoding V) ceiling t defs q :
  PQueue.wf EV q -> idf_ranked EV ceiling t q ->
  idf_ranked EV ceiling t (fold_left (idf_seed EV ceiling t) defs q).
Proof.
  revert q; induction defs as [|v defs IH]; intros q Hwf Hr; [exact Hr|].
  cbn [fold_left]; apply IH; unfold idf_seed; destruct (Map.get EV v t).
  - apply PQueue.wf_push; exact Hwf.
  - exact Hwf.
  - apply idf_ranked_push; assumption.
  - exact Hr.
Qed.

Lemma idf_seed_many_waiting {V} (EV : encoding V) ceiling t defs q v :
  PQueue.wf EV q ->
  (idf_waiting EV (fold_left (idf_seed EV ceiling t) defs q) v <->
   idf_waiting EV q v \/ In v defs /\ exists rank, Map.get EV v t = Some rank).
Proof.
  revert q; induction defs as [|x defs IH]; intros q Hwf; cbn [fold_left In].
  - tauto.
  - rewrite IH by (unfold idf_seed; destruct (Map.get EV x t);
      [apply PQueue.wf_push; exact Hwf|exact Hwf]).
    unfold idf_seed; destruct (Map.get EV x t) as [rank|] eqn:Hnumber.
    + rewrite idf_waiting_push by exact Hwf.
      split.
      * intros [[Heq|Hq]|[Hin Hnum]].
        -- subst x; right; split; [left; reflexivity|exists rank; exact Hnumber].
        -- left; exact Hq.
        -- right; split; [right; exact Hin|exact Hnum].
      * intros [Hq|[[Heq|Hin] Hnum]].
        -- left; right; exact Hq.
        -- subst x; left; left; reflexivity.
        -- right; split; assumption.
    + split.
      * intros [Hq|[Hin Hnum]]; [left; exact Hq|].
        right; split; [right; exact Hin|exact Hnum].
      * intros [Hq|[[Heq|Hin] [a Hnum]]].
        -- left; exact Hq.
        -- subst x; congruence.
        -- right; split; [exact Hin|exists a; exact Hnum].
Qed.

Section PriorityFacts.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Hypothesis Hready : ready EV g p.
Local Abbreviation T := (dominator_tree p).
Local Abbreviation F := (dom_forest p (idom T)).
Local Abbreviation D := (idf_levels EV (idom T) F (prepare EV F)).

Lemma idf_priority_strict a b : reachable g b -> strictly_dominates g a b ->
  Pos.lt (idf_priority EV (fuel p) D b) (idf_priority EV (fuel p) D a).
Proof.
  intros Hb [Hab Hne].
  assert (Ha : reachable g a) by (exact (dom_dominator_reachable g a b Hb Hab)).
  destruct (proj2 (idf_level_numbers EV g p Hready a) Ha) as [ra Hra],
    (proj2 (idf_level_numbers EV g p Hready b) Hb) as [rb Hrb].
  pose proof (idf_levels_ancestor EV g p Hready a b
    (proj1 (idf_dominance_anc EV g p Hready a b Hb) Hab)) as Hlevels.
  destruct Hlevels as [Heq|Hlevels]; [contradiction|].
  unfold idf_level in Hlevels; rewrite Hra, Hrb in Hlevels.
  unfold idf_priority; rewrite Hra, Hrb; apply Pos.sub_lt_mono_l; [exact Hlevels|].
  apply Pos2Nat.inj_lt.
  pose proof (idf_levels_bound EV g p Hready b rb Hrb).
  rewrite (fuel_value (proj2 (proj2 Hready))); lia.
Qed.

(** Popping the deepest pending level leaves no pending strict descendant of that root. *)
Lemma idf_pop_no_descendant q rank root rest : PQueue.wf EV q ->
  idf_ranked EV (fuel p) D q -> (forall v, idf_waiting EV q v -> reachable g v) ->
  PQueue.pop EV q = Some (rank, root, rest) ->
  forall v, idf_waiting EV rest v -> ~ strictly_dominates g root v.
Proof.
  intros Hwf Hrank Hdomain Hpop v Hwait Hstrict.
  destruct (idf_waiting_pop EV q rank root rest Hwf Hpop) as [_ Hrest].
  pose proof (proj1 (Hrest v) Hwait) as [Hwaiting Hne].
  destruct Hwaiting as [rv Hrv].
  destruct (PQueue.pop_min EV q rest rank root Hwf Hpop) as [Hroot Hmin].
  specialize (Hmin v rv Hrv); unfold PQueue.before in Hmin.
  rewrite (Hrank root rank Hroot), (Hrank v rv Hrv) in Hmin.
  pose proof (idf_priority_strict root v (Hdomain v ltac:(exists rv; exact Hrv)) Hstrict).
  destruct Hmin as [Hlt|[Heq _]]; lia.
Qed.

End PriorityFacts.

(** * Worklist invariants *)

Section Invariants.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (defs : list V) (live : V -> bool).
Hypothesis Hready : ready EV g p.
Local Abbreviation T := (dominator_tree p).
Local Abbreviation F := (dom_forest p (idom T)).
Local Abbreviation D := (idf_levels EV (idom T) F (prepare EV F)).

(** Sound outputs, completed frontier obligations and pending seeds characterize partial runs. *)
Record idf_invariant (st : IdfState.t V) : Prop := {
  idf_queue_wf : PQueue.wf EV (pending st);
  idf_output_wf : FinSet.wf EV (emitted st);
  idf_scanned_wf : FinSet.wf EV (scanned st);
  idf_processed_wf : FinSet.wf EV (processed st);
  idf_queue_ranked : idf_ranked EV (fuel p) D (pending st);
  idf_queue_domain : forall v, idf_waiting EV (pending st) v -> reachable g v;
  idf_processed_domain : forall v, FinSet.mem EV v (processed st) = true -> reachable g v;
  idf_trace_agrees : forall v, In v (trace st) <-> FinSet.mem EV v (processed st) = true;
  idf_trace_nodup : NoDup (trace st);
  idf_queue_fresh : forall v, idf_waiting EV (pending st) v ->
    FinSet.mem EV v (processed st) = false;
  idf_root_origin : forall v, FinSet.mem EV v (processed st) = true \/
    idf_waiting EV (pending st) v -> In v defs \/ in_pruned_idf g defs live v;
  idf_seed_available : forall v, reachable g v ->
    In v defs \/ FinSet.mem EV v (emitted st) = true ->
    FinSet.mem EV v (processed st) = true \/ idf_waiting EV (pending st) v;
  idf_output_sound : forall v, FinSet.mem EV v (emitted st) = true ->
    in_pruned_idf g defs live v;
  idf_processed_closed : forall d n, FinSet.mem EV d (processed st) = true ->
    in_df g d n -> live n = true -> FinSet.mem EV n (emitted st) = true;
  idf_scanned_agrees : forall v, FinSet.mem EV v (scanned st) = true <->
    reachable g v /\ exists d, FinSet.mem EV d (processed st) = true /\ dominates g d v;
  idf_pending_outside : forall d v, FinSet.mem EV d (processed st) = true ->
    idf_waiting EV (pending st) v -> ~ strictly_dominates g d v;
  idf_output_count_agrees : output_count st = N.of_nat (FinSet.size (emitted st))
}.

Lemma idf_frontier_reachable d n : in_df g d n -> reachable g n.
Proof.
  intros [e [Hedge [Htarget [Hreach _]]]]; subst n; eapply reachable_step; eassumption.
Qed.

Lemma idf_pruned_reachable n : in_pruned_idf g defs live n -> reachable g n.
Proof.
  intros [d x Hfrom Hdf Hlive]; apply (idf_frontier_reachable d x); exact Hdf.
Qed.

Lemma idf_invariant_scanned_closed st : idf_invariant st ->
  idf_scanned_closed EV g p (scanned st).
Proof.
  intros Hinv u v Hu Hanc.
  apply (idf_scanned_agrees st Hinv) in Hu; destruct Hu as [Hureach [d [Hd Hdu]]].
  apply (idf_scanned_agrees st Hinv); split.
  - destruct (dom_ancestor_last EV (idom T) u v Hanc) as [Heq|[q [Hget _]]].
    + subst v; exact Hureach.
    + destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hdomain _] _]].
      exact (proj1 (Hdomain v q Hget)).
  - exists d; split; [exact Hd|].
    eapply dominates_trans; [exact Hdu|].
    exact (proj1 (proj2 (dominator_tree_sound EV g p Hready)) u v Hanc).
Qed.

(** An already scanned witness lies in a completed subtree nested below the current root. *)
Lemma idf_previous_subtree st root v : idf_invariant st ->
  idf_waiting EV (pending st) root -> dominates g root v ->
  FinSet.mem EV v (scanned st) = true ->
  exists d, FinSet.mem EV d (processed st) = true /\ dominates g root d /\ dominates g d v.
Proof.
  intros Hinv Hroot Hrv Hseen.
  apply (idf_scanned_agrees st Hinv) in Hseen; destruct Hseen as [Hv [d [Hd Hdv]]].
  exists d; split; [exact Hd|]; split; [|exact Hdv].
  destruct (idf_dominance_comparable EV g p Hready root d v Hv Hrv Hdv) as [Hrd|Hdr].
  - exact Hrd.
  - destruct (dfs_eq_dec EV d root) as [Heq|Hne].
    + subst d; apply dominates_refl.
    + exfalso; apply (idf_pending_outside st Hinv d root Hd Hroot); split; assumption.
Qed.

(** A root's frontier is either newly discovered or was discharged by a completed nested root. *)
Lemma idf_root_coverage st root fresh candidates : idf_invariant st ->
  idf_waiting EV (pending st) root ->
  fresh = preorder (dfs (prepare EV F) (scanned st) [root]) ->
  candidates = fst (fold_left (idf_collect_node p T live root) fresh ([], 0%N)) ->
  forall n, in_df g root n -> live n = true ->
    FinSet.mem EV n (emitted st) = true \/ In n candidates.
Proof.
  intros Hinv Hroot Hfresh Hcandidates n Hdf Hlive.
  destruct Hdf as [e [Hedge [Htarget [Hsource [Hdom Hnot]]]]].
  destruct (FinSet.mem EV (Graph.source g e) (scanned st)) eqn:Hscanned.
  - destruct (idf_previous_subtree st root (Graph.source g e) Hinv Hroot Hdom Hscanned)
      as [d [Hd [Hrd Hdx]]].
    left; apply (idf_processed_closed st Hinv d n Hd); [|exact Hlive].
    rewrite <- Htarget; apply (idf_frontier_nested EV g p Hready root d e);
      try assumption; rewrite Htarget; exact Hnot.
  - right; rewrite Hcandidates.
    assert (Hfreshspec : forall v, In v fresh <->
      dominates g root v /\ reachable g v /\ FinSet.mem EV v (scanned st) = false).
    { intro v; rewrite Hfresh; apply idf_subtree_fresh;
        [exact Hready|apply idf_invariant_scanned_closed; exact Hinv|
          apply (idf_queue_domain st Hinv); exact Hroot]. }
    apply (idf_discovery EV g p Hready root live fresh n).
    + intros v Hv; apply Hfreshspec in Hv; tauto.
    + exists e; split; [apply Hfreshspec; auto|]; auto.
Qed.

(** Extending the scanned set records exactly the union of the completed subtrees. *)
Lemma idf_scan_coverage st root fresh v : idf_invariant st ->
  idf_waiting EV (pending st) root ->
  fresh = preorder (dfs (prepare EV F) (scanned st) [root]) ->
  (FinSet.mem EV v (fold_left (fun s x => FinSet.add EV x s) fresh (scanned st)) = true <->
   reachable g v /\ exists d, FinSet.mem EV d (FinSet.add EV root (processed st)) = true /\
     dominates g d v).
Proof.
  intros Hinv Hroot Hfresh; rewrite FinSet.mem_fold_add.
  assert (Hfreshspec : In v fresh <->
    dominates g root v /\ reachable g v /\ FinSet.mem EV v (scanned st) = false).
  { rewrite Hfresh; apply idf_subtree_fresh;
      [exact Hready|apply idf_invariant_scanned_closed; exact Hinv|
        apply (idf_queue_domain st Hinv); exact Hroot]. }
  split.
  - intros [Hin|Hseen].
    + apply Hfreshspec in Hin; destruct Hin as [Hdom [Hv _]].
      split; [exact Hv|exists root; split; [apply FinSet.mem_add; left; reflexivity|exact Hdom]].
    + apply (idf_scanned_agrees st Hinv) in Hseen; destruct Hseen as [Hv [d [Hd Hdom]]].
      split; [exact Hv|exists d; split; [apply FinSet.mem_add; right; exact Hd|exact Hdom]].
  - intros [Hv [d [Hd Hdom]]]; apply FinSet.mem_add in Hd; destruct Hd as [Heq|Hd].
    + subst d; destruct (FinSet.mem EV v (scanned st)) eqn:Hseen; [right; reflexivity|].
      left; apply Hfreshspec; auto.
    + right; apply (idf_scanned_agrees st Hinv); split; [exact Hv|exists d; auto].
Qed.

Lemma idf_initial_invariant : idf_invariant (idf_initial EV (fuel p) D defs).
Proof.
  set (q := fold_left (idf_seed EV (fuel p) D) defs PQueue.empty).
  assert (Hq : PQueue.wf EV q) by (apply idf_seed_many_wf; apply PQueue.wf_empty).
  assert (Hwaiting : forall v, idf_waiting EV q v <-> In v defs /\ reachable g v).
  { intro v; unfold q; rewrite idf_seed_many_waiting by (apply PQueue.wf_empty).
    rewrite (idf_level_numbers EV g p Hready v).
    split; [intros [Hfalse|H]; [exfalso; apply (idf_waiting_empty EV v); exact Hfalse|exact H]|
      intro H; right; exact H]. }
  constructor; cbn [idf_initial pending emitted scanned processed trace output_count].
  - exact Hq.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply idf_seed_many_ranked; [apply PQueue.wf_empty|].
    intros v rank Hfalse; rewrite PQueue.priority_empty in Hfalse; discriminate.
  - intros v Hv; apply Hwaiting in Hv; exact (proj2 Hv).
  - intros v Hfalse; rewrite FinSet.mem_empty in Hfalse; discriminate.
  - intro v; rewrite FinSet.mem_empty; cbn [In]; split; [contradiction|discriminate].
  - constructor.
  - intros v Hv; apply FinSet.mem_empty.
  - intros v [Hfalse|Hv].
    + rewrite FinSet.mem_empty in Hfalse; discriminate.
    + left; apply Hwaiting in Hv; exact (proj1 Hv).
  - intros v Hv [Hdef|Hfalse].
    + right; apply Hwaiting; split; assumption.
    + rewrite FinSet.mem_empty in Hfalse; discriminate.
  - intros v Hfalse; rewrite FinSet.mem_empty in Hfalse; discriminate.
  - intros d n Hfalse; rewrite FinSet.mem_empty in Hfalse; discriminate.
  - intro v; rewrite FinSet.mem_empty; split; [discriminate|].
    intros [_ [d [Hfalse _]]]; rewrite FinSet.mem_empty in Hfalse; discriminate.
  - intros d v Hfalse; rewrite FinSet.mem_empty in Hfalse; discriminate.
  - reflexivity.
Qed.

(** A batch transition exposes its queue, set and traversal observations to the semantic proof. *)
Record idf_batch (st : IdfState.t V) root rest fresh candidates (next : IdfState.t V)
    : Prop := {
  idf_batch_pop : PQueue.pop EV (pending st) = Some (idf_priority EV (fuel p) D root, root, rest);
  idf_batch_fresh : fresh = preorder (dfs (prepare EV F) (scanned st) [root]);
  idf_batch_candidates : candidates =
    fst (fold_left (idf_collect_node p T live root) fresh ([], 0%N));
  idf_batch_queue_wf : PQueue.wf EV (pending next);
  idf_batch_output_wf : FinSet.wf EV (emitted next);
  idf_batch_scanned_wf : FinSet.wf EV (scanned next);
  idf_batch_processed_wf : FinSet.wf EV (processed next);
  idf_batch_ranked : idf_ranked EV (fuel p) D (pending next);
  idf_batch_scanned : scanned next =
    fold_left (fun s v => FinSet.add EV v s) fresh (scanned st);
  idf_batch_processed : processed next = FinSet.add EV root (processed st);
  idf_batch_trace : trace next = root :: trace st;
  idf_batch_output : forall v, FinSet.mem EV v (emitted next) = true <->
    FinSet.mem EV v (emitted st) = true \/ In v candidates;
  idf_batch_waiting : forall v, idf_waiting EV (pending next) v <->
    idf_waiting EV rest v \/ In v candidates /\ FinSet.mem EV v (processed next) = false;
  idf_batch_count : output_count next = N.of_nat (FinSet.size (emitted next))
}.

Lemma idf_step_batch st rank root rest : idf_invariant st ->
  PQueue.pop EV (pending st) = Some (rank, root, rest) ->
  let fresh := preorder (dfs (prepare EV F) (scanned st) [root]) in
  let candidates := fst (fold_left (idf_collect_node p T live root) fresh ([], 0%N)) in
  idf_batch st root rest fresh candidates (idf_work_step p T F (prepare EV F) D live st).
Proof.
  intros Hinv Hpop; cbn zeta.
  assert (Hrank : rank = idf_priority EV (fuel p) D root).
  { apply (idf_queue_ranked st Hinv root rank).
    exact (proj1 (PQueue.pop_min EV (pending st) rest rank root
      (idf_queue_wf st Hinv) Hpop)). }
  subst rank.
  unfold idf_work_step; rewrite Hpop.
  set (fresh := preorder (dfs (prepare EV F) (scanned st) [root])).
  set (collected := fold_left (idf_collect_node p T live root) fresh ([], 0%N)).
  set (base := Make rest (emitted st)
    (fold_left (fun s v => FinSet.add EV v s) fresh (scanned st))
    (FinSet.add EV root (processed st)) (root :: trace st)
    (N.add (edge_visits st) (snd collected)) (output_count st)).
  assert (Hrest : PQueue.wf EV rest) by
    (eapply PQueue.wf_pop; [exact (idf_queue_wf st Hinv)|exact Hpop]).
  destruct (idf_emit_many_wf EV (fuel p) D (fst collected) base Hrest
    (idf_output_wf st Hinv)) as [Hqueue Houtput].
  destruct (idf_emit_many_frames EV (fuel p) D (fst collected) base)
    as [Hscanned [Hprocessed [Htrace Hedges]]].
  constructor.
  - exact Hpop.
  - reflexivity.
  - reflexivity.
  - exact Hqueue.
  - exact Houtput.
  - rewrite Hscanned; apply FinSet.wf_fold_add; exact (idf_scanned_wf st Hinv).
  - rewrite Hprocessed; apply Map.wf_set; exact (idf_processed_wf st Hinv).
  - apply idf_emit_many_ranked; [exact Hrest|].
    apply (idf_ranked_pop EV (fuel p) D (pending st)
      (idf_priority EV (fuel p) D root) root rest); try exact Hpop;
      [exact (idf_queue_wf st Hinv)|exact (idf_queue_ranked st Hinv)].
  - exact Hscanned.
  - exact Hprocessed.
  - exact Htrace.
  - intro v; exact (idf_emit_many_output EV (fuel p) D (fst collected) base v).
  - intro v; rewrite (idf_emit_many_waiting EV (fuel p) D (fst collected) base v Hrest).
    rewrite Hprocessed; reflexivity.
  - apply idf_emit_many_count; exact (idf_output_count_agrees st Hinv).
Qed.

Lemma idf_batch_discovery st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall n, In n candidates -> in_df g root n /\ live n = true.
Proof.
  intros Hinv Hbatch n Hin.
  pose proof (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
    root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))) as Hroot.
  rewrite (idf_batch_candidates _ _ _ _ _ _ Hbatch) in Hin.
  apply (idf_discovery_sound EV g p Hready root live fresh n); [|exact Hin].
  intros v Hv; rewrite (idf_batch_fresh _ _ _ _ _ _ Hbatch) in Hv.
  apply (idf_subtree_fresh EV g p Hready (scanned st) root v
    (idf_invariant_scanned_closed st Hinv) (idf_queue_domain st Hinv root Hroot)) in Hv.
  tauto.
Qed.

Lemma idf_batch_sound st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall n, FinSet.mem EV n (emitted next) = true -> in_pruned_idf g defs live n.
Proof.
  intros Hinv Hbatch n Hout; apply (idf_batch_output _ _ _ _ _ _ Hbatch) in Hout.
  destruct Hout as [Hout|Hin]; [exact (idf_output_sound st Hinv n Hout)|].
  destruct (idf_batch_discovery st root rest fresh candidates next Hinv Hbatch n Hin)
    as [Hdf Hlive].
  apply (pruned_idf_step root n); [|exact Hdf|exact Hlive].
  apply (idf_root_origin st Hinv root); right.
  exact (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
    root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))).
Qed.

Lemma idf_batch_closed st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall d n, FinSet.mem EV d (processed next) = true -> in_df g d n -> live n = true ->
    FinSet.mem EV n (emitted next) = true.
Proof.
  intros Hinv Hbatch d n Hd Hdf Hlive.
  rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch) in Hd; apply FinSet.mem_add in Hd.
  apply (idf_batch_output _ _ _ _ _ _ Hbatch).
  destruct Hd as [Heq|Hd].
  - subst d; apply (idf_root_coverage st root fresh candidates Hinv).
    + exact (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
        root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))).
    + exact (idf_batch_fresh _ _ _ _ _ _ Hbatch).
    + exact (idf_batch_candidates _ _ _ _ _ _ Hbatch).
    + exact Hdf.
    + exact Hlive.
  - left; exact (idf_processed_closed st Hinv d n Hd Hdf Hlive).
Qed.

Lemma idf_batch_outside st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall d v, FinSet.mem EV d (processed next) = true ->
    idf_waiting EV (pending next) v -> ~ strictly_dominates g d v.
Proof.
  intros Hinv Hbatch d v Hd Hwait Hstrict.
  pose proof (idf_batch_pop _ _ _ _ _ _ Hbatch) as Hpop.
  destruct (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
    root rest (idf_queue_wf st Hinv) Hpop) as [Hroot Hrest].
  rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch) in Hd; apply FinSet.mem_add in Hd.
  apply (idf_batch_waiting _ _ _ _ _ _ Hbatch) in Hwait.
  destruct Hd as [Heq|Hd], Hwait as [Hwait|[Hin Hfree]].
  - subst d; apply (idf_pop_no_descendant EV g p Hready (pending st)
      (idf_priority EV (fuel p) D root) root rest (idf_queue_wf st Hinv)
      (idf_queue_ranked st Hinv) (idf_queue_domain st Hinv) Hpop v Hwait Hstrict).
  - subst d; destruct (idf_batch_discovery st root rest fresh candidates next Hinv Hbatch v Hin)
      as [[e [Hedge [Htarget [Hsource [Hdom Hnot]]]]] Hlive].
    exact (Hnot Hstrict).
  - exact (idf_pending_outside st Hinv d v Hd (proj1 (proj1 (Hrest v) Hwait)) Hstrict).
  - destruct (idf_batch_discovery st root rest fresh candidates next Hinv Hbatch v Hin)
      as [Hdf Hlive].
    apply (idf_pending_outside st Hinv d root Hd Hroot).
    exact (idf_frontier_backwards EV g p Hready d root v Hdf Hstrict).
Qed.

Lemma idf_batch_available_old st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall v, FinSet.mem EV v (processed st) = true \/ idf_waiting EV (pending st) v ->
    FinSet.mem EV v (processed next) = true \/ idf_waiting EV (pending next) v.
Proof.
  intros Hinv Hbatch v [Hdone|Hwait].
  - left; rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch); apply FinSet.mem_add;
      right; exact Hdone.
  - destruct (dfs_eq_dec EV v root) as [Heq|Hne].
    + subst v; left; rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch).
      apply FinSet.mem_add; left; reflexivity.
    + right; apply (idf_batch_waiting _ _ _ _ _ _ Hbatch); left.
      apply (proj2 (proj2 (idf_waiting_pop EV (pending st)
        (idf_priority EV (fuel p) D root) root rest (idf_queue_wf st Hinv)
        (idf_batch_pop _ _ _ _ _ _ Hbatch)) v)); split; assumption.
Qed.

Lemma idf_batch_available st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall v, reachable g v -> In v defs \/ FinSet.mem EV v (emitted next) = true ->
    FinSet.mem EV v (processed next) = true \/ idf_waiting EV (pending next) v.
Proof.
  intros Hinv Hbatch v Hv [Hdef|Hout].
  - apply (idf_batch_available_old st root rest fresh candidates next Hinv Hbatch).
    apply (idf_seed_available st Hinv v Hv); left; exact Hdef.
  - apply (idf_batch_output _ _ _ _ _ _ Hbatch) in Hout; destruct Hout as [Hout|Hin].
    + apply (idf_batch_available_old st root rest fresh candidates next Hinv Hbatch).
      apply (idf_seed_available st Hinv v Hv); right; exact Hout.
    + destruct (FinSet.mem EV v (processed next)) eqn:Hdone; [left; reflexivity|].
      right; apply (idf_batch_waiting _ _ _ _ _ _ Hbatch); right; split; assumption.
Qed.

Lemma idf_batch_domains st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  (forall v, idf_waiting EV (pending next) v -> reachable g v) /\
  (forall v, FinSet.mem EV v (processed next) = true -> reachable g v).
Proof.
  intros Hinv Hbatch.
  destruct (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
    root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch)) as [Hroot Hrest].
  split.
  - intros v Hwait; apply (idf_batch_waiting _ _ _ _ _ _ Hbatch) in Hwait.
    destruct Hwait as [Hwait|[Hin _]].
    + apply (idf_queue_domain st Hinv); exact (proj1 (proj1 (Hrest v) Hwait)).
    + apply idf_pruned_reachable; apply (idf_batch_sound st root rest fresh candidates next
        Hinv Hbatch v); apply (idf_batch_output _ _ _ _ _ _ Hbatch); right; exact Hin.
  - intros v Hd; rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch) in Hd.
    apply FinSet.mem_add in Hd; destruct Hd as [Heq|Hd].
    + subst v; exact (idf_queue_domain st Hinv root Hroot).
    + exact (idf_processed_domain st Hinv v Hd).
Qed.

Lemma idf_batch_trace_valid st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  (forall v, In v (trace next) <-> FinSet.mem EV v (processed next) = true) /\
  NoDup (trace next).
Proof.
  intros Hinv Hbatch; split.
  - intro v; rewrite (idf_batch_trace _ _ _ _ _ _ Hbatch),
      (idf_batch_processed _ _ _ _ _ _ Hbatch), FinSet.mem_add.
    cbn [In]; rewrite (idf_trace_agrees st Hinv v); intuition congruence.
  - rewrite (idf_batch_trace _ _ _ _ _ _ Hbatch); constructor.
    + intro Hin; apply (idf_trace_agrees st Hinv) in Hin.
      pose proof (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
        root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))) as Hroot.
      pose proof (idf_queue_fresh st Hinv root Hroot); congruence.
    + exact (idf_trace_nodup st Hinv).
Qed.

Lemma idf_batch_pending_fresh st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall v, idf_waiting EV (pending next) v -> FinSet.mem EV v (processed next) = false.
Proof.
  intros Hinv Hbatch v Hwait; apply (idf_batch_waiting _ _ _ _ _ _ Hbatch) in Hwait.
  destruct Hwait as [Hwait|[_ Hfree]]; [|exact Hfree].
  destruct (proj1 (proj2 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
    root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch)) v) Hwait)
    as [Hold Hne].
  rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch).
  apply Bool.not_true_iff_false; intro Hdone; apply FinSet.mem_add in Hdone.
  destruct Hdone as [Heq|Hdone]; [contradiction|].
  pose proof (idf_queue_fresh st Hinv v Hold); congruence.
Qed.

Lemma idf_batch_origin_valid st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next ->
  forall v, FinSet.mem EV v (processed next) = true \/ idf_waiting EV (pending next) v ->
    In v defs \/ in_pruned_idf g defs live v.
Proof.
  intros Hinv Hbatch v [Hd|Hwait].
  - rewrite (idf_batch_processed _ _ _ _ _ _ Hbatch) in Hd; apply FinSet.mem_add in Hd.
    apply (idf_root_origin st Hinv v).
    destruct Hd as [Heq|Hd]; [subst v; right|left; exact Hd].
    exact (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
      root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))).
  - apply (idf_batch_waiting _ _ _ _ _ _ Hbatch) in Hwait.
    destruct Hwait as [Hwait|[Hin _]].
    + apply (idf_root_origin st Hinv v); right.
      exact (proj1 (proj1 (proj2 (idf_waiting_pop EV (pending st)
        (idf_priority EV (fuel p) D root) root rest (idf_queue_wf st Hinv)
        (idf_batch_pop _ _ _ _ _ _ Hbatch)) v) Hwait)).
    + right; apply (idf_batch_sound st root rest fresh candidates next Hinv Hbatch v).
      apply (idf_batch_output _ _ _ _ _ _ Hbatch); right; exact Hin.
Qed.

Lemma idf_batch_invariant st root rest fresh candidates next : idf_invariant st ->
  idf_batch st root rest fresh candidates next -> idf_invariant next.
Proof.
  intros Hinv Hbatch.
  destruct (idf_batch_domains st root rest fresh candidates next Hinv Hbatch)
    as [Hqueuedomain Hprocesseddomain].
  destruct (idf_batch_trace_valid st root rest fresh candidates next Hinv Hbatch)
    as [Htrace Hnodup].
  constructor.
  - exact (idf_batch_queue_wf _ _ _ _ _ _ Hbatch).
  - exact (idf_batch_output_wf _ _ _ _ _ _ Hbatch).
  - exact (idf_batch_scanned_wf _ _ _ _ _ _ Hbatch).
  - exact (idf_batch_processed_wf _ _ _ _ _ _ Hbatch).
  - exact (idf_batch_ranked _ _ _ _ _ _ Hbatch).
  - exact Hqueuedomain.
  - exact Hprocesseddomain.
  - exact Htrace.
  - exact Hnodup.
  - exact (idf_batch_pending_fresh st root rest fresh candidates next Hinv Hbatch).
  - exact (idf_batch_origin_valid st root rest fresh candidates next Hinv Hbatch).
  - exact (idf_batch_available st root rest fresh candidates next Hinv Hbatch).
  - exact (idf_batch_sound st root rest fresh candidates next Hinv Hbatch).
  - exact (idf_batch_closed st root rest fresh candidates next Hinv Hbatch).
  - intro v; rewrite (idf_batch_scanned _ _ _ _ _ _ Hbatch),
      (idf_batch_processed _ _ _ _ _ _ Hbatch).
    apply (idf_scan_coverage st root fresh v Hinv).
    + exact (proj1 (idf_waiting_pop EV (pending st) (idf_priority EV (fuel p) D root)
        root rest (idf_queue_wf st Hinv) (idf_batch_pop _ _ _ _ _ _ Hbatch))).
    + exact (idf_batch_fresh _ _ _ _ _ _ Hbatch).
  - exact (idf_batch_outside st root rest fresh candidates next Hinv Hbatch).
  - exact (idf_batch_count _ _ _ _ _ _ Hbatch).
Qed.

(** Every priority step preserves soundness, completed obligations and exact subtree coverage. *)
Lemma idf_step_invariant st : idf_invariant st ->
  idf_invariant (idf_work_step p T F (prepare EV F) D live st).
Proof.
  intro Hinv; destruct (PQueue.pop EV (pending st)) as [[[rank root] rest]|] eqn:Hpop.
  - eapply idf_batch_invariant; [exact Hinv|].
    exact (idf_step_batch st rank root rest Hinv Hpop).
  - unfold idf_work_step; rewrite Hpop; exact Hinv.
Qed.

(** Roots are processed once, including roots that occur repeatedly in the definition list. *)
Lemma idf_step_once st rank root rest : idf_invariant st ->
  PQueue.pop EV (pending st) = Some (rank, root, rest) ->
  ~ In root (trace st) /\ trace (idf_work_step p T F (prepare EV F) D live st) = root :: trace st.
Proof.
  intros Hinv Hpop; split.
  - intro Hin; apply (idf_trace_agrees st Hinv) in Hin.
    pose proof (proj1 (idf_waiting_pop EV (pending st) rank root rest
      (idf_queue_wf st Hinv) Hpop)) as Hroot.
    pose proof (idf_queue_fresh st Hinv root Hroot); congruence.
  - exact (idf_batch_trace _ _ _ _ _ _ (idf_step_batch st rank root rest Hinv Hpop)).
Qed.

Lemma idf_step_scanned_monotone st v : idf_invariant st ->
  FinSet.mem EV v (scanned st) = true ->
  FinSet.mem EV v (scanned (idf_work_step p T F (prepare EV F) D live st)) = true.
Proof.
  intros Hinv Hseen; destruct (PQueue.pop EV (pending st)) as [[[rank root] rest]|] eqn:Hpop.
  - rewrite (idf_batch_scanned _ _ _ _ _ _ (idf_step_batch st rank root rest Hinv Hpop)).
    apply FinSet.mem_fold_add; right; exact Hseen.
  - unfold idf_work_step; rewrite Hpop; exact Hseen.
Qed.

(** Each subtree scan visits distinct fresh vertices, disjoint from every earlier scan. *)
Lemma idf_scan_once st root : idf_invariant st -> idf_waiting EV (pending st) root ->
  let fresh := preorder (dfs (prepare EV F) (scanned st) [root]) in
  NoDup fresh /\ forall v, In v fresh -> FinSet.mem EV v (scanned st) = false.
Proof.
  intros Hinv Hroot; cbn zeta; split.
  - assert (Hroots : incl [root] (Graph.nodes F)).
    { intros v [Heq|Hfalse]; [subst v|contradiction].
      apply (idf_tree_node EV g p Hready); exact (idf_queue_domain st Hinv root Hroot). }
    exact (proj1 (proj2 (dfs_exact EV F (prepare EV F) root [root] (scanned st)
      (idf_tree_ready EV g p Hready) Hroots))).
  - intros v Hv.
    apply (idf_subtree_fresh EV g p Hready (scanned st) root v
      (idf_invariant_scanned_closed st Hinv) (idf_queue_domain st Hinv root Hroot)) in Hv.
    tauto.
Qed.

(** Edge visits count each newly scanned adjacency entry; duplicate outputs do not affect it. *)
Lemma idf_step_edge_count st rank root rest : idf_invariant st ->
  PQueue.pop EV (pending st) = Some (rank, root, rest) ->
  edge_visits (idf_work_step p T F (prepare EV F) D live st) =
    (edge_visits st + fold_right
      (fun v count => N.of_nat (length (succ_edges p v)) + count)%N 0%N
      (preorder (dfs (prepare EV F) (scanned st) [root])))%N.
Proof.
  intros Hinv Hpop; unfold idf_work_step; rewrite Hpop.
  rewrite (proj2 (proj2 (proj2 (idf_emit_many_frames EV (fuel p) D _ _)))).
  cbn [edge_visits]; rewrite idf_collect_nodes_count; cbn [snd]; lia.
Qed.

Lemma idf_trace_bound st : idf_invariant st -> length (trace st) <= length (Graph.nodes g).
Proof.
  intro Hinv; apply NoDup_incl_length; [exact (idf_trace_nodup st Hinv)|].
  intros v Hv; apply (reachable_in_nodes g v (proj1 Hready)).
  apply (idf_processed_domain st Hinv); apply (idf_trace_agrees st Hinv); exact Hv.
Qed.

Lemma idf_iter_invariant st k : idf_invariant st ->
  idf_invariant (Pos.iter (idf_work_step p T F (prepare EV F) D live) st k).
Proof.
  intro Hinv; induction k using Pos.peano_ind.
  - apply idf_step_invariant; exact Hinv.
  - rewrite Pos.iter_succ; apply idf_step_invariant; exact IHk.
Qed.

Lemma idf_step_empty st : idf_invariant st -> PQueue.is_empty (pending st) = true ->
  idf_work_step p T F (prepare EV F) D live st = st.
Proof.
  intros Hinv Hempty; unfold idf_work_step.
  rewrite (proj2 (PQueue.pop_none EV (pending st) (idf_queue_wf st Hinv)) Hempty).
  reflexivity.
Qed.

Lemma idf_iter_empty st k : idf_invariant st -> PQueue.is_empty (pending st) = true ->
  Pos.iter (idf_work_step p T F (prepare EV F) D live) st k = st.
Proof.
  intros Hinv Hempty; induction k using Pos.peano_ind.
  - apply idf_step_empty; assumption.
  - rewrite Pos.iter_succ, IHk; apply idf_step_empty; assumption.
Qed.

Lemma idf_run_invariant k st : idf_invariant st ->
  idf_invariant (idf_run p T F (prepare EV F) D live k st).
Proof.
  revert st; induction k as [k IH|k IH|]; intros st Hinv; cbn [idf_run];
    destruct (PQueue.is_empty (pending st)); try exact Hinv.
  - apply idf_step_invariant; apply IH; apply IH; exact Hinv.
  - apply IH; apply IH; exact Hinv.
  - apply idf_step_invariant; exact Hinv.
Qed.

Lemma idf_run_agrees k st : idf_invariant st ->
  idf_run p T F (prepare EV F) D live k st =
    Pos.iter (idf_work_step p T F (prepare EV F) D live) st k.
Proof.
  revert st; induction k as [k IH|k IH|]; intros st Hinv; cbn [idf_run];
    destruct (PQueue.is_empty (pending st)) eqn:Hempty.
  - symmetry; apply idf_iter_empty; assumption.
  - rewrite (IH st Hinv), (IH _ (idf_iter_invariant st k Hinv)).
    rewrite <- Pos.iter_add, Pos.add_diag; symmetry; apply (Pos.iter_succ (xO k)).
  - symmetry; apply idf_iter_empty; assumption.
  - rewrite (IH st Hinv), (IH _ (idf_iter_invariant st k Hinv)).
    rewrite <- Pos.iter_add, Pos.add_diag; reflexivity.
  - symmetry; apply idf_iter_empty; assumption.
  - reflexivity.
Qed.

(** Each nonempty queue step consumes a previously unprocessed finite-graph vertex. *)
Lemma idf_iter_progress st k : idf_invariant st ->
  let result := Pos.iter (idf_work_step p T F (prepare EV F) D live) st k in
  PQueue.is_empty (pending result) = true \/
    length (trace st) + Pos.to_nat k <= length (trace result).
Proof.
  intro Hinv; induction k using Pos.peano_ind.
  - cbn [Pos.iter Pos.to_nat].
    destruct (PQueue.pop EV (pending st)) as [[[rank root] rest]|] eqn:Hpop.
    + right; rewrite (proj2 (idf_step_once st rank root rest Hinv Hpop)); cbn; lia.
    + left; unfold idf_work_step; rewrite Hpop.
      apply (proj1 (PQueue.pop_none EV (pending st) (idf_queue_wf st Hinv))); exact Hpop.
  - cbn zeta in *; rewrite Pos.iter_succ.
    set (middle := Pos.iter (idf_work_step p T F (prepare EV F) D live) st k) in *.
    assert (Hmiddle : idf_invariant middle) by (apply idf_iter_invariant; exact Hinv).
    destruct (PQueue.pop EV (pending middle)) as [[[rank root] rest]|] eqn:Hpop.
    + destruct IHk as [Hempty|Hbound].
      * pose proof (proj2 (PQueue.pop_none EV (pending middle)
          (idf_queue_wf middle Hmiddle)) Hempty); congruence.
      * right; rewrite (proj2 (idf_step_once middle rank root rest Hmiddle Hpop)).
        cbn [length]; rewrite Pos2Nat.inj_succ; lia.
    + left; unfold idf_work_step; rewrite Hpop.
      apply (proj1 (PQueue.pop_none EV (pending middle) (idf_queue_wf middle Hmiddle)));
        exact Hpop.
Qed.

Lemma idf_iter_finished st : idf_invariant st ->
  PQueue.is_empty (pending (Pos.iter (idf_work_step p T F (prepare EV F) D live) st
    (Pos.of_succ_nat (length (Graph.nodes g))))) = true.
Proof.
  intro Hinv.
  destruct (idf_iter_progress st (Pos.of_succ_nat (length (Graph.nodes g))) Hinv)
    as [Hempty|Hbound]; [exact Hempty|].
  pose proof (idf_trace_bound _ (idf_iter_invariant st
    (Pos.of_succ_nat (length (Graph.nodes g))) Hinv)) as Hlength.
  rewrite SuccNat2Pos.id_succ in Hbound; lia.
Qed.

Lemma idf_finished_processed st d : idf_invariant st ->
  PQueue.is_empty (pending st) = true -> reachable g d ->
  In d defs \/ FinSet.mem EV d (emitted st) = true ->
  FinSet.mem EV d (processed st) = true.
Proof.
  intros Hinv Hempty Hd Hseed.
  destruct (idf_seed_available st Hinv d Hd Hseed) as [Hdone|[rank Hwait]];
    [exact Hdone|].
  pose proof (proj1 (PQueue.is_empty_spec EV (pending st) (idf_queue_wf st Hinv)) Hempty d).
  congruence.
Qed.

(** An empty queue discharges every derivation step and establishes least-closure completeness. *)
Lemma idf_finished_exact st : idf_invariant st -> PQueue.is_empty (pending st) = true ->
  forall n, FinSet.mem EV n (emitted st) = true <-> in_pruned_idf g defs live n.
Proof.
  intros Hinv Hempty n; split; [exact (idf_output_sound st Hinv n)|].
  apply (pruned_idf_induction g defs live
    (fun v => FinSet.mem EV v (emitted st) = true)).
  - intros d x Hdef Hdf Hlive; apply (idf_processed_closed st Hinv d x); try assumption.
    apply idf_finished_processed; try assumption.
    + destruct Hdf as [e [Hedge [Htarget [Hsource [Hdom _]]]]].
      exact (dom_dominator_reachable g d (Graph.source g e) Hsource Hdom).
    + left; exact Hdef.
  - intros d x Hderiv IH Hdf Hlive; apply (idf_processed_closed st Hinv d x); try assumption.
    apply idf_finished_processed; try assumption.
    + apply idf_pruned_reachable; exact Hderiv.
    + right; exact IH.
Qed.

End Invariants.

(** Emitted nodes are exactly those derived with a live target at every frontier step. *)
Theorem direct_pruned_idf_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (defs : list V) (live : V -> bool) (n : V) : ready EV g p ->
  (FinSet.mem EV n (direct_pruned_idf p (dominator_tree p) defs live) = true <->
   in_pruned_idf g defs live n).
Proof.
  intro Hready; unfold direct_pruned_idf.
  set (initial := idf_initial EV (fuel p)
    (idf_levels EV (idom (dominator_tree p)) (dom_forest p (idom (dominator_tree p)))
      (prepare EV (dom_forest p (idom (dominator_tree p))))) defs).
  pose proof (idf_initial_invariant EV g p defs live Hready) as Hinitial.
  rewrite (idf_run_agrees EV g p defs live Hready _ initial Hinitial).
  apply (idf_finished_exact EV g p defs live).
  - exact (idf_iter_invariant EV g p defs live Hready initial _ Hinitial).
  - exact (idf_iter_finished EV g p defs live Hready initial Hinitial).
Qed.

(** The unpruned direct query is exactly the ordinary least iterated dominance frontier. *)
Theorem direct_idf_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (defs : list V) (n : V) : ready EV g p ->
  (FinSet.mem EV n (direct_idf p (dominator_tree p) defs) = true <-> in_idf g defs n).
Proof.
  intro Hready; unfold direct_idf.
  rewrite (direct_pruned_idf_exact EV g p defs (fun _ => true) n Hready).
  apply pruned_idf_all.
Qed.
