(** * Dominance frontiers and their closure

    Incoming edges contribute their stopped dominator-parent walks to the frontier map.
    For example, both arms of a diamond have its join in their dominance frontier.
    Builds on: GraphDominators, GraphEdgeDominance and GraphDfs. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphLengauerTarjan GraphDominators GraphEdgeDominance.
Import List.ListNotations.

(** A frontier has an incoming edge dominated at its source but not strictly at its target. *)
Definition in_df {V E} (g : Graph.t V E) (d n : V) : Prop :=
  exists e, In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = n /\
    reachable g (Graph.source g e) /\
    dominates g d (Graph.source g e) /\ ~ strictly_dominates g d n.

Scheme All for or.

(** Iterating frontiers starts with definitions and emits only frontier successors. *)
Inductive in_idf {V E} (g : Graph.t V E) (defs : list V) : V -> Prop :=
  | idf_step : forall d n, (In d defs \/ in_idf g defs d) ->
      in_df g d n -> in_idf g defs n.

Arguments idf_step {V E g defs} d n _ _.

Lemma frontier_parent_strict {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) n q d : ready EV g p -> dominator_exact p = true ->
  reachable g n -> Map.get EV n (idom (dominator_tree p)) = Some q ->
  (strictly_dominates g d n <-> dominates g d q).
Proof.
  intros Hready Hcheck Hn Hparent.
  destruct (dominator_tree_exact EV g p Hready Hcheck) as [_ [Hparents _]].
  pose proof (proj1 (Hparents q n Hn) Hparent) as [[Hqn Hqne] Hnearest].
  split; [apply Hnearest|].
  intro Hdq; split; [eapply dominates_trans; eassumption|].
  intro Heq; subst d.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  assert (Hq : reachable g q) by (eapply dom_dominator_reachable; eassumption).
  assert (Hnq : idom_ancestor EV (simple_lt_idom p) n q).
  { apply (Hexact n q Hq); exact Hdq. }
  assert (Hqn' : idom_ancestor EV (simple_lt_idom p) q n).
  { apply (Hexact q n Hn); exact Hqn. }
  apply Hqne; symmetry.
  exact (dom_ancestor_antisym EV g p (simple_lt_idom p) Hready Hmap Hforest n q Hnq Hqn').
Qed.

(** The runner chain contains exactly the dominance-frontier witnesses for one incoming edge. *)
Theorem dominance_chain {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (e : E) : ready EV g p -> dominator_exact p = true ->
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) -> forall d,
  (dominates g d (Graph.source g e) /\ ~ strictly_dominates g d (Graph.target g e) <->
   dominates_b EV (dominator_tree p) d (Graph.source g e) = true /\
   (forall q, Map.get EV (Graph.target g e) (idom (dominator_tree p)) = Some q ->
      dominates_b EV (dominator_tree p) d q = false)).
Proof.
  intros Hready Hcheck Hedge Hsource d.
  pose proof (reachable_step e Hsource Hedge) as Htarget.
  destruct (dominator_tree_exact EV g p Hready Hcheck) as [Hquery [_ Hroots]].
  rewrite <- (Hquery d (Graph.source g e) Hsource).
  destruct (Map.get EV (Graph.target g e) (idom (dominator_tree p))) as [q|] eqn:Hparent.
  - pose proof (frontier_parent_strict EV g p (Graph.target g e) q d
      Hready Hcheck Htarget Hparent) as Hstrict.
    assert (Hq : reachable g q).
    { destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hdomain _] _]].
      exact (proj2 (Hdomain (Graph.target g e) q Hparent)). }
    rewrite <- (Hquery d q Hq) in Hstrict.
    split.
    + intros [Hdom Hnot]; split; [exact Hdom|].
      intros a Heq; inversion Heq; subst a.
      apply Bool.not_true_iff_false; intro Htrue; apply Hnot; apply Hstrict; exact Htrue.
    + intros [Hdom Hnot]; split; [exact Hdom|].
      intro Hstrictdom; apply Hstrict in Hstrictdom.
      specialize (Hnot q eq_refl); congruence.
  - split.
    + intros [Hdom _]; split; [exact Hdom|intros q Hfalse; discriminate].
    + intros [Hdom _]; split; [exact Hdom|].
      apply (proj1 (Hroots (Graph.target g e) Htarget) Hparent).
Qed.

(** A stop excludes its ancestors; on an incoming-edge walk the first such node is the stop. *)
Definition frontier_blocked {V} (EV : encoding V) (t : dom_tree V)
    (stop : option V) (v : V) : bool :=
  match stop with
  | Some q => dominates_b EV t v q
  | None => false
  end.

(** One runner visit records a node and advances to its parent, or stops at the boundary. *)
Definition frontier_runner_step {V} (EV : encoding V) (t : dom_tree V)
    (stop : option V) (state : option V * list V) : option V * list V :=
  match state with
  | (None, seen) => (None, seen)
  | (Some v, seen) =>
    if frontier_blocked EV t stop v then (None, seen)
    else (Map.get EV v (idom t), v :: seen)
  end.

(** Binary blocks stop immediately after the runner finishes. *)
Fixpoint frontier_runner_run {V} (EV : encoding V) (t : dom_tree V)
    (stop : option V) (k : positive) (state : option V * list V) : option V * list V :=
  match fst state with
  | None => state
  | Some _ =>
    match k with
    | xH => frontier_runner_step EV t stop state
    | xO half => frontier_runner_run EV t stop half
        (frontier_runner_run EV t stop half state)
    | xI half => frontier_runner_step EV t stop
        (frontier_runner_run EV t stop half (frontier_runner_run EV t stop half state))
    end
  end.

(** Collect a stopped parent chain within the prepared binary traversal bound. *)
Definition frontier_runner {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (start : V) (stop : option V) : list V :=
  snd (frontier_runner_run EV t stop (fuel p) (Some start, [])).

Lemma frontier_runner_iter_done {V} (EV : encoding V) (t : dom_tree V) stop seen k :
  Pos.iter (frontier_runner_step EV t stop) (None, seen) k = (None, seen).
Proof.
  induction k using Pos.peano_ind; [reflexivity|rewrite Pos.iter_succ, IHk; reflexivity].
Qed.

Lemma frontier_runner_run_agrees {V} (EV : encoding V) (t : dom_tree V) stop k state :
  frontier_runner_run EV t stop k state = Pos.iter (frontier_runner_step EV t stop) state k.
Proof.
  revert state; induction k as [k IH|k IH|]; intros [[v|] seen].
  - cbn [frontier_runner_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO k)).
  - symmetry; apply frontier_runner_iter_done.
  - cbn [frontier_runner_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - symmetry; apply frontier_runner_iter_done.
  - reflexivity.
  - reflexivity.
Qed.

(** Current and emitted nodes stay on the start's parent chain; emitted nodes are unblocked. *)
Definition frontier_runner_sound {V} (EV : encoding V) (t : dom_tree V) stop start
    (state : option V * list V) : Prop :=
  (forall v, fst state = Some v -> idom_ancestor EV (idom t) v start) /\
  (forall d, In d (snd state) ->
    idom_ancestor EV (idom t) d start /\ frontier_blocked EV t stop d = false).

Lemma frontier_runner_sound_step {V} (EV : encoding V) (t : dom_tree V) stop start state :
  frontier_runner_sound EV t stop start state ->
  frontier_runner_sound EV t stop start (frontier_runner_step EV t stop state).
Proof.
  destruct state as [[v|] seen]; intros [Hcurrent Hseen];
    unfold frontier_runner_sound, frontier_runner_step in *; cbn in *; [|auto].
  destruct (frontier_blocked EV t stop v) eqn:Hblocked; cbn.
  - split; [intros u Hfalse; discriminate|exact Hseen].
  - split.
    + intros u Hparent; eapply rt_trans; [apply rt_step; exact Hparent|].
      apply Hcurrent; reflexivity.
    + intros d [Heq|Hin].
      * subst d; split; [apply Hcurrent; reflexivity|exact Hblocked].
      * apply Hseen; exact Hin.
Qed.

Lemma frontier_runner_sound_iter {V} (EV : encoding V) (t : dom_tree V) stop start state k :
  frontier_runner_sound EV t stop start state ->
  frontier_runner_sound EV t stop start (Pos.iter (frontier_runner_step EV t stop) state k).
Proof.
  intro Hstate; induction k using Pos.peano_ind.
  - apply frontier_runner_sound_step; exact Hstate.
  - rewrite Pos.iter_succ; apply frontier_runner_sound_step; exact IHk.
Qed.

(** Every desired ancestor is already emitted or remains above the current runner. *)
Definition frontier_runner_coverage {V} (EV : encoding V) (t : dom_tree V) stop start
    (state : option V * list V) : Prop :=
  forall d, idom_ancestor EV (idom t) d start -> frontier_blocked EV t stop d = false ->
    In d (snd state) \/ exists v, fst state = Some v /\ idom_ancestor EV (idom t) d v.

Lemma frontier_runner_coverage_step {V} (EV : encoding V) (t : dom_tree V) stop start state :
  (forall d v, idom_ancestor EV (idom t) d v -> frontier_blocked EV t stop v = true ->
    frontier_blocked EV t stop d = true) ->
  frontier_runner_coverage EV t stop start state ->
  frontier_runner_coverage EV t stop start (frontier_runner_step EV t stop state).
Proof.
  intros Hup Hcoverage; destruct state as [[v|] seen];
    unfold frontier_runner_coverage, frontier_runner_step in *; cbn in *; [|exact Hcoverage].
  intros d Hanc Hfree; destruct (Hcoverage d Hanc Hfree) as [Hin|[u [Heq Hu]]].
  - destruct (frontier_blocked EV t stop v); cbn; auto.
  - inversion Heq; subst u.
    destruct (frontier_blocked EV t stop v) eqn:Hblocked; cbn.
    + pose proof (Hup d v Hu Hblocked); congruence.
    + destruct (dom_ancestor_last EV (idom t) d v Hu) as [Hsame|[q [Hparent Hq]]].
      * subst d; left; left; reflexivity.
      * right; exists q; split; assumption.
Qed.

Lemma frontier_runner_coverage_iter {V} (EV : encoding V) (t : dom_tree V) stop start state k :
  (forall d v, idom_ancestor EV (idom t) d v -> frontier_blocked EV t stop v = true ->
    frontier_blocked EV t stop d = true) ->
  frontier_runner_coverage EV t stop start state ->
  frontier_runner_coverage EV t stop start
    (Pos.iter (frontier_runner_step EV t stop) state k).
Proof.
  intros Hup Hstate; induction k using Pos.peano_ind.
  - apply frontier_runner_coverage_step; assumption.
  - rewrite Pos.iter_succ; apply frontier_runner_coverage_step; assumption.
Qed.

(** A proof-only parent rank decreases at every active step and vanishes after stopping. *)
Definition frontier_runner_measure {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (state : option V * list V) : nat :=
  match fst state with
  | Some v => S (dom_rank p (simple_lt_idom p) v)
  | None => 0
  end.

Lemma frontier_runner_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) stop v seen : ready EV g p ->
  frontier_runner_measure p (frontier_runner_step EV (dominator_tree p) stop (Some v, seen)) <
  frontier_runner_measure p (Some v, seen).
Proof.
  intro Hready; unfold frontier_runner_step.
  destruct (frontier_blocked EV (dominator_tree p) stop v).
  - cbn [frontier_runner_measure fst]; lia.
  - destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest _]].
    unfold frontier_runner_measure; cbn [fst].
    change (match Map.get EV v (simple_lt_idom p) with
      | Some u => S (dom_rank p (simple_lt_idom p) u)
      | None => 0
      end < S (dom_rank p (simple_lt_idom p) v)).
    destruct (Map.get EV v (simple_lt_idom p)) as [u|] eqn:Hparent; [|lia].
    pose proof (dom_parent_rank EV g p (simple_lt_idom p) Hready Hmap Hforest u v Hparent).
    lia.
Qed.

Lemma frontier_runner_iter_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) stop state k : ready EV g p ->
  let result := Pos.iter (frontier_runner_step EV (dominator_tree p) stop) state k in
  fst result = None \/
    frontier_runner_measure p result + Pos.to_nat k <= frontier_runner_measure p state.
Proof.
  intro Hready; induction k using Pos.peano_ind.
  - destruct state as [[v|] seen]; [|left; reflexivity].
    right; cbn [Pos.iter].
    pose proof (frontier_runner_decreases EV g p stop v seen Hready); cbn in *; lia.
  - rewrite Pos.iter_succ.
    destruct (Pos.iter (frontier_runner_step EV (dominator_tree p) stop) state k)
      as [[v|] seen] eqn:Hrun.
    + destruct IHk as [Hnone|Hbound]; [discriminate|].
      right; pose proof (frontier_runner_decreases EV g p stop v seen Hready).
      rewrite Pos2Nat.inj_succ; cbn in *; lia.
    + left; reflexivity.
Qed.

Lemma frontier_runner_finished {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) stop start : ready EV g p ->
  fst (Pos.iter (frontier_runner_step EV (dominator_tree p) stop)
    (Some start, []) (fuel p)) = None.
Proof.
  intro Hready.
  destruct (frontier_runner_iter_bound EV g p stop (Some start, []) (fuel p) Hready)
    as [Hdone|Hbound]; [exact Hdone|].
  pose proof (edge_dom_rank_bound EV g p start Hready).
  rewrite (fuel_value (proj2 (proj2 Hready))) in Hbound.
  cbn [frontier_runner_measure fst] in Hbound; lia.
Qed.

Lemma frontier_blocked_up {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) stop : ready EV g p -> dominator_exact p = true ->
  (forall q, stop = Some q -> reachable g q) ->
  forall d v, idom_ancestor EV (idom (dominator_tree p)) d v ->
    frontier_blocked EV (dominator_tree p) stop v = true ->
    frontier_blocked EV (dominator_tree p) stop d = true.
Proof.
  intros Hready Hcheck Hstop d v Hanc; destruct stop as [q|]; [|discriminate].
  cbn [frontier_blocked]; intro Hblocked.
  pose proof (proj1 (dominator_tree_exact EV g p Hready Hcheck) d q (Hstop q eq_refl))
    as Hquery.
  apply (proj2 Hquery).
  eapply dominates_trans.
  - apply (proj1 (proj2 (dominator_tree_sound EV g p Hready))); exact Hanc.
  - apply (proj1 (proj1 (dominator_tree_exact EV g p Hready Hcheck) v q
      (Hstop q eq_refl))); exact Hblocked.
Qed.

(** A finished runner returns exactly the unblocked ancestors of its start. *)
Lemma frontier_runner_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) start stop d : ready EV g p -> dominator_exact p = true ->
  reachable g start -> (forall q, stop = Some q -> reachable g q) ->
  (In d (frontier_runner p (dominator_tree p) start stop) <->
   dominates g d start /\ frontier_blocked EV (dominator_tree p) stop d = false).
Proof.
  intros Hready Hcheck Hstart Hstop.
  destruct (simple_lt_idom_exact EV g p Hready) as [_ [_ Hexact]].
  assert (Hanc : dominates g d start <->
    idom_ancestor EV (idom (dominator_tree p)) d start) by (apply Hexact; exact Hstart).
  unfold frontier_runner; rewrite frontier_runner_run_agrees.
  split.
  - intro Hin.
    assert (Hinitial : frontier_runner_sound EV (dominator_tree p)
      stop start (Some start, [])).
    { split; cbn;
        [intros v Heq; inversion Heq; apply rt_refl|intros a Hfalse; contradiction]. }
    destruct (proj2 (frontier_runner_sound_iter EV (dominator_tree p)
      stop start (Some start, []) (fuel p) Hinitial) d Hin) as [Ha Hb].
    split; [apply Hanc; exact Ha|exact Hb].
  - intros [Hdom Hfree].
    assert (Hinitial : frontier_runner_coverage EV (dominator_tree p)
      stop start (Some start, [])).
    { intros a Ha _; right; exists start; split; [reflexivity|exact Ha]. }
    destruct (frontier_runner_coverage_iter EV (dominator_tree p) stop start
      (Some start, []) (fuel p) (frontier_blocked_up EV g p stop Hready Hcheck Hstop)
      Hinitial d (proj1 Hanc Hdom) Hfree) as [Hin|[v [Hcurrent _]]]; [exact Hin|].
    rewrite (frontier_runner_finished EV g p stop start Hready) in Hcurrent; discriminate.
Qed.

Lemma frontier_blocked_false {V} (EV : encoding V) (t : dom_tree V) stop d :
  frontier_blocked EV t stop d = false <->
  forall q, stop = Some q -> dominates_b EV t d q = false.
Proof.
  destruct stop as [q|]; cbn [frontier_blocked].
  - split; [intros H a Heq; inversion Heq; subst a; exact H|intro H; apply H; reflexivity].
  - split; [intros _ q Hfalse; discriminate|intros _; reflexivity].
Qed.

(** Every reachable incoming edge contributes one stopped parent walk. *)
Definition frontier_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list E :=
  let live := visited (dfs p FinSet.empty (Graph.entries g)) in
  filter (fun e => FinSet.mem EV (Graph.source g e) live)
    (flat_map (pred_edges p) (Graph.nodes g)).

Lemma frontier_edges_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) e : ready EV g p ->
  (In e (frontier_edges p) <->
   In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e)).
Proof.
  intro Hready; unfold frontier_edges; rewrite filter_In, reachable_dfs by exact Hready.
  split.
  - intros [Hin Hreach]; apply in_flat_map in Hin; destruct Hin as [b [Hb Hin]].
    apply (pred_agrees (proj2 (proj2 Hready)) b e Hb) in Hin.
    destruct Hin as [u [_ [Hedge _]]].
    pose proof (out_source (proj1 Hready) u e Hedge) as Hsource; subst u; auto.
  - intros [Hedge Hreach]; split; [|exact Hreach].
    apply in_flat_map; exists (Graph.target g e); split.
    + apply (reachable_in_nodes g _ (proj1 Hready)); exact (reachable_step e Hreach Hedge).
    + apply (pred_agrees (proj2 (proj2 Hready)) _ e).
      * apply (reachable_in_nodes g _ (proj1 Hready)); exact (reachable_step e Hreach Hedge).
      * exists (Graph.source g e); repeat split; try assumption.
        apply (reachable_in_nodes g _ (proj1 Hready)); exact Hreach.
Qed.

Lemma frontier_runner_edge_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) e d : ready EV g p -> dominator_exact p = true ->
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) ->
  (In d (frontier_runner p (dominator_tree p) (Graph.source g e)
    (Map.get EV (Graph.target g e) (idom (dominator_tree p)))) <->
   dominates g d (Graph.source g e) /\ ~ strictly_dominates g d (Graph.target g e)).
Proof.
  intros Hready Hcheck Hedge Hsource.
  rewrite frontier_runner_exact; try assumption.
  - rewrite frontier_blocked_false.
    rewrite (dominance_chain EV g p e Hready Hcheck Hedge Hsource d).
    rewrite (proj1 (dominator_tree_exact EV g p Hready Hcheck) d
      (Graph.source g e) Hsource); reflexivity.
  - intros q Hparent; destruct (simple_lt_idom_exact EV g p Hready) as [_ [[Hdomain _] _]].
    exact (proj2 (Hdomain (Graph.target g e) q Hparent)).
Qed.

(** Events pair a visited dominator with the target contributed to its frontier. *)
Definition frontier_events {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : list (V * V) :=
  flat_map (fun e => map (fun d => (d, Graph.target g e))
    (frontier_runner p t (Graph.source g e) (Map.get EV (Graph.target g e) (idom t))))
    (frontier_edges p).

Lemma frontier_events_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) d n : ready EV g p -> dominator_exact p = true ->
  (In (d, n) (frontier_events p (dominator_tree p)) <-> in_df g d n).
Proof.
  intros Hready Hcheck; unfold frontier_events, in_df; rewrite in_flat_map.
  split.
  - intros [e [Hedge Hin]].
    apply (frontier_edges_spec EV g p e Hready) in Hedge; destruct Hedge as [Hedge Hreach].
    apply in_map_iff in Hin; destruct Hin as [a [Heq Hin]]; inversion Heq; subst a n.
    apply (frontier_runner_edge_exact EV g p e d Hready Hcheck Hedge Hreach) in Hin.
    exists e; tauto.
  - intros [e [Hedge [Htarget [Hreach Hdom]]]]; exists e; split.
    + apply (frontier_edges_spec EV g p e Hready); auto.
    + apply in_map_iff; exists d; split; [congruence|].
      apply (frontier_runner_edge_exact EV g p e d Hready Hcheck Hedge Hreach);
        rewrite Htarget; exact Hdom.
Qed.

(** A frontier membership is a successful map lookup followed by set membership. *)
Definition frontier_at {V} (EV : encoding V) (m : Map.t V (FinSet.t V)) (d n : V) : Prop :=
  exists s, Map.get EV d m = Some s /\ FinSet.mem EV n s = true.

Definition frontier_add {V} (EV : encoding V) (m : Map.t V (FinSet.t V))
    (event : V * V) : Map.t V (FinSet.t V) :=
  let '(d, n) := event in
  let old := match Map.get EV d m with Some s => s | None => FinSet.empty end in
  Map.set EV d (FinSet.add EV n old) m.

Lemma frontier_add_spec {V} (EV : encoding V) m x b d n :
  frontier_at EV (frontier_add EV m (x, b)) d n <->
  (d = x /\ n = b) \/ frontier_at EV m d n.
Proof.
  unfold frontier_at, frontier_add; destruct (dfs_eq_dec EV d x) as [Heq|Hne].
  - subst x; rewrite Map.get_set_same.
    destruct (Map.get EV d m) as [old|] eqn:Hget.
    + split.
      * intros [s [Heq Hmem]]; inversion Heq; subst s; apply FinSet.mem_add in Hmem.
        destruct Hmem as [Hsame|Hmem]; [left; auto|right; exists old; auto].
      * intros [[_ Heq]|[s [Heq Hmem]]]; subst; exists (FinSet.add EV b old); split;
          try reflexivity; apply FinSet.mem_add.
        -- left; reflexivity.
        -- inversion Heq; subst s; right; exact Hmem.
    + split.
      * intros [s [Heq Hmem]]; inversion Heq; subst s.
        apply FinSet.mem_add in Hmem; rewrite FinSet.mem_empty in Hmem.
        destruct Hmem as [Hsame|Hfalse]; [left; auto|discriminate].
      * intros [[_ Heq]|[s [Hfalse _]]]; [subst n|discriminate].
        exists (FinSet.add EV b FinSet.empty); split; [reflexivity|].
        apply FinSet.mem_add; left; reflexivity.
  - rewrite Map.get_set_other by exact Hne.
    split; [intro H; right; exact H|intros [[Heq _]|H]; [contradiction|exact H]].
Qed.

Lemma frontier_fold_spec {V} (EV : encoding V) events m d n :
  frontier_at EV (fold_left (frontier_add EV) events m) d n <->
  In (d, n) events \/ frontier_at EV m d n.
Proof.
  revert m; induction events as [|[x b] rest IH]; intro m; cbn [fold_left].
  - cbn [In]; tauto.
  - rewrite IH, frontier_add_spec; cbn [In].
    split.
    + intros [Hin|[[Heq Heq']|Hmem]]; [left; right; exact Hin|left; left; congruence|auto].
    + intros [[Heq|Hin]|Hmem].
      * inversion Heq; subst; right; left; auto.
      * left; exact Hin.
      * right; right; exact Hmem.
Qed.

(** Materialize the Cooper-Harvey-Kennedy runner events in the frontier map. *)
Definition dominance_frontier {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : Map.t V (FinSet.t V) :=
  fold_left (frontier_add EV) (frontier_events p t) Map.empty.

(** With an exact tree, the computed frontiers are the dominance frontiers. *)
Theorem dominance_frontier_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> dominator_exact p = true -> forall d n,
  ((exists s, Map.get EV d (dominance_frontier p (dominator_tree p)) = Some s /\
              FinSet.mem EV n s = true) <-> in_df g d n).
Proof.
  intros Hready Hcheck d n; change (frontier_at EV
    (dominance_frontier p (dominator_tree p)) d n <-> in_df g d n).
  unfold dominance_frontier; rewrite frontier_fold_spec.
  rewrite (frontier_events_exact EV g p d n Hready Hcheck).
  unfold frontier_at; rewrite Map.get_empty; split; [intros [H|[s [Hfalse _]]]|];
    try discriminate; auto.
Qed.

(** Every stored frontier can be enumerated with the finite-set membership laws. *)
Definition frontier_values_wf {V} (EV : encoding V) (m : Map.t V (FinSet.t V)) : Prop :=
  forall d s, Map.get EV d m = Some s -> FinSet.wf EV s.

Lemma frontier_add_wf {V} (EV : encoding V) m event : frontier_values_wf EV m ->
  frontier_values_wf EV (frontier_add EV m event).
Proof.
  intros Hwf d s Hget; destruct event as [x n]; unfold frontier_add in Hget.
  destruct (dfs_eq_dec EV d x) as [Heq|Hne].
  - subst x; rewrite Map.get_set_same in Hget; inversion Hget; subst s.
    apply Map.wf_set; destruct (Map.get EV d m) as [old|] eqn:Hold.
    + apply (Hwf d old Hold).
    + apply Map.wf_empty.
  - rewrite Map.get_set_other in Hget by exact Hne; exact (Hwf d s Hget).
Qed.

Lemma frontier_fold_wf {V} (EV : encoding V) events m : frontier_values_wf EV m ->
  frontier_values_wf EV (fold_left (frontier_add EV) events m).
Proof.
  revert m; induction events as [|event rest IH]; intros m Hwf; [exact Hwf|].
  cbn [fold_left]; apply IH; apply frontier_add_wf; exact Hwf.
Qed.

Lemma dominance_frontier_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) t : frontier_values_wf EV (dominance_frontier p t).
Proof.
  unfold dominance_frontier; apply frontier_fold_wf.
  intros d s Hfalse; rewrite Map.get_empty in Hfalse; discriminate.
Qed.

(** Read each stored frontier once when its node is processed. *)
Definition frontier_successors {V} (EV : encoding V) (df : Map.t V (FinSet.t V))
    (d : V) : list V :=
  match Map.get EV d df with
  | Some s => FinSet.elements s
  | None => []
  end.

Lemma frontier_successors_spec {V} (EV : encoding V) df d n :
  frontier_values_wf EV df ->
  (In n (frontier_successors EV df d) <-> frontier_at EV df d n).
Proof.
  intro Hwf; unfold frontier_successors, frontier_at.
  destruct (Map.get EV d df) as [s|] eqn:Hget.
  - rewrite (FinSet.elements_spec EV n s (Hwf d s Hget)).
    split; [intro H; exists s; auto|intros [old [Heq H]]; inversion Heq; subst; exact H].
  - split; [contradiction|intros [s [Hfalse _]]; discriminate].
Qed.

Lemma frontier_successors_nodup {V} (EV : encoding V) df d :
  frontier_values_wf EV df -> NoDup (frontier_successors EV df d).
Proof.
  intro Hwf; unfold frontier_successors; destruct (Map.get EV d df) as [s|] eqn:Hget.
  - apply (FinSet.elements_nodup EV s (Hwf d s Hget)).
  - constructor.
Qed.

Lemma in_df_nodes {V E} (g : Graph.t V E) d n : graph_wf g -> in_df g d n ->
  In d (Graph.nodes g) /\ In n (Graph.nodes g).
Proof.
  intros Hwf [e [Hedge [Htarget [Hreach [Hdom _]]]]]; subst n; split.
  - apply (reachable_in_nodes g d Hwf); eapply dom_dominator_reachable; eassumption.
  - apply (reachable_in_nodes g _ Hwf); exact (reachable_step e Hreach Hedge).
Qed.

(** The worklist graph starts with the frontiers of definitions, so definitions need not emit. *)
Definition frontier_graph {V E} (EV : encoding V) (g : Graph.t V E)
    (df : Map.t V (FinSet.t V)) (defs : list V) : Graph.t V (V * V) :=
  {| Graph.entries := flat_map (frontier_successors EV df) defs;
     Graph.nodes := Graph.nodes g;
     Graph.out := fun d => map (fun n => (d, n)) (frontier_successors EV df d);
     Graph.source := fst;
     Graph.target := snd |}.

(** A prepared DFS worklist emits the least frontier closure, with one seen set. *)
Definition iterated_frontier {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (df : Map.t V (FinSet.t V)) (defs : list V) : FinSet.t V :=
  let fg := frontier_graph EV g df defs in
  visited (dfs (prepare EV fg) FinSet.empty (Graph.entries fg)).

Lemma frontier_graph_edge {V E} (EV : encoding V) (g : Graph.t V E) df defs d n :
  frontier_values_wf EV df ->
  (In (d, n) (Graph.out (frontier_graph EV g df defs) d) <-> frontier_at EV df d n).
Proof.
  intro Hwf; change (In (d, n) (map (fun x => (d, x)) (frontier_successors EV df d)) <->
    frontier_at EV df d n).
  rewrite in_map_iff.
  rewrite <- (frontier_successors_spec EV df d n Hwf).
  split.
  - intros [x [Heq Hin]]; inversion Heq; subst x; exact Hin.
  - intro Hin; exists n; auto.
Qed.

Lemma frontier_graph_ready {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) defs : ready EV g p -> dominator_exact p = true ->
  let fg := frontier_graph EV g (dominance_frontier p (dominator_tree p)) defs in
  ready EV fg (prepare EV fg).
Proof.
  intros Hready Hcheck; cbn zeta; apply prepare_ready.
  - constructor; cbn [frontier_graph].
    + apply (nodes_nodup (proj1 Hready)).
    + intros n Hin; apply in_flat_map in Hin; destruct Hin as [d [_ Hin]].
      apply (frontier_successors_spec EV _ d n (dominance_frontier_wf EV g p _)) in Hin.
      apply (dominance_frontier_exact EV g p Hready Hcheck) in Hin.
      exact (proj2 (in_df_nodes g d n (proj1 Hready) Hin)).
    + intros d [x n] Hin; apply in_map_iff in Hin; destruct Hin as [a [Heq _]].
      cbn in *; inversion Heq; reflexivity.
    + intros d [x n] _ Hin; apply in_map_iff in Hin; destruct Hin as [a [Heq Hin]].
      inversion Heq; subst x a; cbn.
      apply (frontier_successors_spec EV _ d n (dominance_frontier_wf EV g p _)) in Hin.
      apply (dominance_frontier_exact EV g p Hready Hcheck) in Hin.
      exact (proj2 (in_df_nodes g d n (proj1 Hready) Hin)).
  - intro d; cbn [frontier_graph].
    apply nodup_map_injective.
    + intros x y Heq; inversion Heq; reflexivity.
    + apply frontier_successors_nodup; apply dominance_frontier_wf.
Qed.

Lemma in_idf_induction {V E} (g : Graph.t V E) defs (P : V -> Prop) :
  (forall d n, In d defs -> in_df g d n -> P n) ->
  (forall d n, in_idf g defs d -> P d -> in_df g d n -> P n) ->
  forall n, in_idf g defs n -> P n.
Proof.
  intros Hseed Hstep.
  fix IH 2; intros n Hderiv; destruct Hderiv as [d n Hfrom Hdf].
  destruct Hfrom as [Hdef|Hprev].
  - exact (Hseed d n Hdef Hdf).
  - exact (Hstep d n Hprev (IH d Hprev) Hdf).
Qed.

Lemma frontier_graph_reachable {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) defs n : ready EV g p -> dominator_exact p = true ->
  (reachable (frontier_graph EV g (dominance_frontier p (dominator_tree p)) defs) n <->
   in_idf g defs n).
Proof.
  intros Hready Hcheck.
  set (df := dominance_frontier p (dominator_tree p)).
  assert (Hdf : forall d n, In n (frontier_successors EV df d) <-> in_df g d n).
  { intros d x; rewrite frontier_successors_spec by (apply dominance_frontier_wf).
    apply dominance_frontier_exact; assumption. }
  split.
  - intro Hreach; induction Hreach as [n Hin|[d n] Hreach IH Hedge].
    + cbn [frontier_graph] in Hin; apply in_flat_map in Hin; destruct Hin as [d [Hdef Hin]].
      apply (idf_step d n); [left; exact Hdef|apply Hdf; exact Hin].
    + cbn [frontier_graph] in *; apply in_map_iff in Hedge.
      destruct Hedge as [x [Heq Hin]]; inversion Heq; subst x.
      apply (idf_step d n); [right; exact IH|apply Hdf; exact Hin].
  - apply in_idf_induction.
    + intros d x Hdef Hfrontier; apply reachable_entry; cbn [frontier_graph].
      apply in_flat_map; exists d; split; [exact Hdef|apply Hdf; exact Hfrontier].
    + intros d x _ Hreach Hfrontier.
      apply (@reachable_step V (V * V) (frontier_graph EV g df defs) (d, x)).
      * exact Hreach.
      * apply frontier_graph_edge; [apply dominance_frontier_wf|].
        apply (dominance_frontier_exact EV g p Hready Hcheck); exact Hfrontier.
Qed.

(** The iterated frontier is exactly the least frontier closure of the definitions. *)
Theorem iterated_frontier_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (n : V) (defs : list V) :
  ready EV g p -> dominator_exact p = true ->
  (FinSet.mem EV n (iterated_frontier p (dominance_frontier p (dominator_tree p)) defs) = true <->
   in_idf g defs n).
Proof.
  intros Hready Hcheck; unfold iterated_frontier.
  rewrite reachable_dfs by (apply frontier_graph_ready; assumption).
  apply frontier_graph_reachable; assumption.
Qed.
