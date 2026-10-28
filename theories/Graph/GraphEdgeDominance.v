(** * Edge dominance

    An indexed incoming edge can dominate a node and its dominator descendants.
    For example, the sole incoming edge of a non-entry node dominates that node.
    Builds on: GraphPrepare and GraphDominators. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators GraphLengauerTarjan GraphDominators.
Import List.ListNotations.

(** An edge dominates a node when every entry path to the node traverses it. *)
Definition edge_dominates {V E} (g : Graph.t V E) (e : E) (n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n -> In e es.

(** Select the incoming edges eligible to dominate a node. *)
Definition edge_dom_candidates {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (live : FinSet.t V) (v : V) : list E :=
  filter (fun e => FinSet.mem EV (Graph.source g e) live &&
    negb (dominates_b EV t v (Graph.source g e))) (pred_edges p v).

(** A node has an indexed edge exactly when its candidate list is a singleton. *)
Definition edge_dom_choice {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (entries live : FinSet.t V) (v : V) : option E :=
  if FinSet.mem EV v entries then None else
  match edge_dom_candidates p t live v with
  | [e] => Some e
  | _ => None
  end.

(** Index each non-entry node with its unique reachable incoming non-back edge. *)
Definition edge_dom_index {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : Map.t V E :=
  let entries := FinSet.of_list EV (Graph.entries g) in
  let live := visited (dfs p FinSet.empty (Graph.entries g)) in
  fold_left (fun ix v =>
    match edge_dom_choice p t entries live v with
    | Some e => Map.set EV v e ix
    | None => ix
    end) (Graph.nodes g) Map.empty.

(** Advance once up the parent chain, collecting the current node's indexed edge. *)
Definition edge_dom_step {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    (state : option V * list E) : option V * list E :=
  match state with
  | (None, edges) => (None, edges)
  | (Some v, edges) =>
    (Map.get EV v (idom t),
      match Map.get EV v ix with Some e => e :: edges | None => edges end)
  end.

(** Binary fuel blocks stop as soon as the parent walk reaches a root. *)
Fixpoint edge_dom_run {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    (k : positive) (state : option V * list E) : option V * list E :=
  match fst state with
  | None => state
  | Some _ =>
    match k with
    | xH => edge_dom_step EV t ix state
    | xO half => edge_dom_run EV t ix half (edge_dom_run EV t ix half state)
    | xI half => edge_dom_step EV t ix
        (edge_dom_run EV t ix half (edge_dom_run EV t ix half state))
    end
  end.

Lemma edge_dom_iter_done {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    edges k : Pos.iter (edge_dom_step EV t ix) (None, edges) k = (None, edges).
Proof.
  induction k using Pos.peano_ind; [reflexivity|rewrite Pos.iter_succ, IHk; reflexivity].
Qed.

Lemma edge_dom_run_agrees {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    k state : edge_dom_run EV t ix k state = Pos.iter (edge_dom_step EV t ix) state k.
Proof.
  revert state; induction k as [k IH|k IH|]; intros [[v|] edges].
  - cbn [edge_dom_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO k)).
  - symmetry; apply edge_dom_iter_done.
  - cbn [edge_dom_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - symmetry; apply edge_dom_iter_done.
  - reflexivity.
  - reflexivity.
Qed.

(** Collect index entries along the node's parent chain using prepared binary fuel. *)
Definition dominating_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) (ix : Map.t V E) (n : V) : list E :=
  snd (edge_dom_run EV t ix (fuel p) (Some n, [])).

Lemma edge_index_fold_absent {V E} (EV : encoding V) (choose : V -> option E)
    vs v ix : ~ In v vs ->
  Map.get EV v (fold_left (fun m x =>
    match choose x with Some e => Map.set EV x e m | None => m end) vs ix) =
  Map.get EV v ix.
Proof.
  revert ix; induction vs as [|x xs IH]; intros ix Habsent; [reflexivity|].
  cbn [fold_left]; rewrite IH by (intro Hin; apply Habsent; right; exact Hin).
  destruct (choose x); [apply Map.get_set_other|reflexivity].
  intro Heq; subst x; apply Habsent; left; reflexivity.
Qed.

Lemma edge_index_fold_present {V E} (EV : encoding V) (choose : V -> option E)
    vs v ix : NoDup vs -> In v vs ->
  Map.get EV v (fold_left (fun m x =>
    match choose x with Some e => Map.set EV x e m | None => m end) vs ix) =
  match choose v with Some e => Some e | None => Map.get EV v ix end.
Proof.
  revert ix; induction vs as [|x xs IH]; intros ix Hnodup Hin; [contradiction|].
  inversion Hnodup as [|? ? Hfresh Hrest]; subst.
  cbn [fold_left] in *; destruct Hin as [Heq|Hin].
  - subst x; rewrite edge_index_fold_absent by exact Hfresh.
    destruct (choose v); [apply Map.get_set_same|reflexivity].
  - rewrite IH by assumption.
    destruct (dfs_eq_dec EV v x) as [Heq|Hne]; [subst x; contradiction|].
    destruct (choose v); [reflexivity|].
    destruct (choose x); [apply Map.get_set_other; exact Hne|reflexivity].
Qed.

Lemma edge_dom_index_lookup {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (t : dom_tree V) v : graph_wf g ->
  Map.get EV v (edge_dom_index p t) =
  if in_dec (dfs_eq_dec EV) v (Graph.nodes g) then
    edge_dom_choice p t (FinSet.of_list EV (Graph.entries g))
      (visited (dfs p FinSet.empty (Graph.entries g))) v
  else None.
Proof.
  intro Hwf; unfold edge_dom_index.
  destruct (in_dec (dfs_eq_dec EV) v (Graph.nodes g)) as [Hin|Habsent].
  - rewrite edge_index_fold_present by (try exact Hin; apply nodes_nodup; exact Hwf).
    destruct (edge_dom_choice p t (FinSet.of_list EV (Graph.entries g))
      (visited (dfs p FinSet.empty (Graph.entries g))) v);
      [reflexivity|apply Map.get_empty].
  - rewrite edge_index_fold_absent by exact Habsent; apply Map.get_empty.
Qed.

Lemma edge_dom_candidates_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v e : ready EV g p -> In v (Graph.nodes g) ->
  (In e (edge_dom_candidates p (dominator_tree p)
    (visited (dfs p FinSet.empty (Graph.entries g))) v) <->
   In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
   reachable g (Graph.source g e) /\ ~ dominates g v (Graph.source g e)).
Proof.
  intros Hready Hv; unfold edge_dom_candidates; rewrite filter_In, Bool.andb_true_iff.
  rewrite (reachable_dfs EV g p (Graph.source g e) Hready), Bool.negb_true_iff.
  rewrite (pred_agrees (proj2 (proj2 Hready)) v e Hv).
  split.
  - intros [[u [Hu [Hedge Htarget]]] [Hreach Hnot]].
    assert (Hsource : Graph.source g e = u).
    { eapply out_source; [exact (proj1 Hready)|exact Hedge]. }
    subst u; repeat split; try assumption.
    intro Hdom; apply (proj2 (proj1 (dominator_tree_with_exact EV g p Hready SimpleLT)
      v (Graph.source g e) Hreach)) in Hdom.
    change (dominates_b EV (dominator_tree p) v (Graph.source g e) = true) in Hdom.
    rewrite Hnot in Hdom; discriminate.
  - intros [Hedge [Htarget [Hreach Hnot]]]; split.
    + exists (Graph.source g e); repeat split; try assumption.
      apply (reachable_in_nodes g _ (proj1 Hready)); exact Hreach.
    + split; [exact Hreach|].
      destruct (dominates_b EV (dominator_tree p) v (Graph.source g e)) eqn:Hbool;
        [|reflexivity].
      exfalso; apply Hnot; eapply (proj1 (proj2 (proj2
        (dominator_tree_sound EV g p Hready)))); exact Hbool.
Qed.

Lemma edge_first_arrival_aux {V E} (EV : encoding V) (g : Graph.t V E)
    v s pre u es : path g s pre u -> In s (Graph.entries g) -> v <> s ->
  (forall a, In a pre -> Graph.target g a <> v) -> v <> u -> path g u es v ->
  exists e, In e es /\ In e (Graph.out g (Graph.source g e)) /\
    Graph.target g e = v /\ reachable g (Graph.source g e) /\
    ~ dominates g v (Graph.source g e).
Proof.
  intros Hpre Hentry Hstart Hfree Hcurrent Hpath.
  remember v as dest eqn:Hdest in Hpath.
  revert s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  induction Hpath as [u|e es w Hedge Hpath IH];
    intros s pre Hpre Hentry Hstart Hfree Hcurrent Hdest.
  - congruence.
  - destruct (dfs_eq_dec EV (Graph.target g e) v) as [Htarget|Htarget].
    + exists e; split; [left; reflexivity|]; split; [exact Hedge|]; split; [exact Htarget|].
      split.
      * apply reachable_iff_path; exists s, pre; auto.
      * intros Hdom; destruct (Hdom s pre Hentry Hpre) as [Heq|[a [Hin Ha]]].
        -- contradiction.
        -- exact (Hfree a Hin Ha).
    + destruct (IH s (pre ++ [e]) (path_snoc g s pre (Graph.source g e) e Hpre
        eq_refl Hedge) Hentry Hstart) as [a [Hin Hrest]].
      * intros a Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hin]].
        -- apply Hfree; exact Hin.
        -- subst a; exact Htarget.
        -- contradiction.
      * congruence.
      * exact Hdest.
      * exists a; split; [right; exact Hin|exact Hrest].
Qed.

Lemma edge_first_arrival {V E} (EV : encoding V) (g : Graph.t V E)
    v s es : ~ In v (Graph.entries g) -> In s (Graph.entries g) -> path g s es v ->
  exists e, In e es /\ In e (Graph.out g (Graph.source g e)) /\
    Graph.target g e = v /\ reachable g (Graph.source g e) /\
    ~ dominates g v (Graph.source g e).
Proof.
  intros Hnot Hentry Hpath.
  apply (edge_first_arrival_aux EV g v s [] s es); try assumption.
  - constructor.
  - intro Heq; subst; contradiction.
  - intros a Hin; contradiction.
  - intro Heq; subst; contradiction.
Qed.

Lemma edge_index_singleton {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v e : ready EV g p ->
  Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e ->
  In v (Graph.nodes g) /\ ~ In v (Graph.entries g) /\
  edge_dom_candidates p (dominator_tree p)
    (visited (dfs p FinSet.empty (Graph.entries g))) v = [e].
Proof.
  intros Hready Hget; rewrite (edge_dom_index_lookup EV g p (dominator_tree p) v
    (proj1 Hready)) in Hget.
  destruct (in_dec (dfs_eq_dec EV) v (Graph.nodes g)) as [Hv|Hv]; [|discriminate].
  unfold edge_dom_choice in Hget.
  destruct (FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))) eqn:Hentry;
    [discriminate|].
  assert (Hnot : ~ In v (Graph.entries g)).
  { intro Hin; apply (proj2 (FinSet.of_list_spec EV v (Graph.entries g))) in Hin; congruence. }
  destruct (edge_dom_candidates p (dominator_tree p)
    (visited (dfs p FinSet.empty (Graph.entries g))) v) as [|a [|b rest]];
    try discriminate.
  inversion Hget; subst a; auto.
Qed.

Lemma edge_index_dominates {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v e : ready EV g p ->
  Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e -> edge_dominates g e v.
Proof.
  intros Hready Hget s es Hentry Hpath.
  destruct (edge_index_singleton EV g p v e Hready Hget) as [Hv [Hnot Hsingle]].
  destruct (edge_first_arrival EV g v s es Hnot Hentry Hpath) as [a [Hin Hcandidate]].
  assert (Hmem : In a (edge_dom_candidates p (dominator_tree p)
    (visited (dfs p FinSet.empty (Graph.entries g))) v)).
  { apply (edge_dom_candidates_spec EV g p v a Hready Hv); exact Hcandidate. }
  rewrite Hsingle in Hmem; destruct Hmem as [Heq|Hfalse]; [subst a; exact Hin|contradiction].
Qed.

Lemma edge_nondominated_path {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v u : ready EV g p -> ~ dominates g v u ->
  exists s es, In s (Graph.entries g) /\ path g s es u /\ v <> s /\
    forall a, In a es -> Graph.target g a <> v.
Proof.
  intros Hready Hnot.
  assert (Hmem : FinSet.mem EV u
    (visited (dfs p (FinSet.add EV v FinSet.empty) (Graph.entries g))) = true).
  { destruct (FinSet.mem EV u
      (visited (dfs p (FinSet.add EV v FinSet.empty) (Graph.entries g)))) eqn:Hmem;
      [reflexivity|].
    exfalso; apply Hnot; apply (proj1 (dom_blocked_exact EV g p v u Hready)).
    rewrite Hmem; reflexivity. }
  apply (proj1 (proj1 (dfs_exact EV g p u (Graph.entries g)
    (FinSet.add EV v FinSet.empty) Hready (entries_in (proj1 Hready))))) in Hmem.
  replace (set_entries g (Graph.entries g)) with g in Hmem by (destruct g; reflexivity).
  apply reachable_without in Hmem.
  destruct Hmem as [s [es [Hentry [Hpath [Hstart Hfree]]]]].
  exists s, es; repeat split; try assumption.
  - apply singleton_absent in Hstart; congruence.
  - intros a Hin; exact (proj1 (singleton_absent EV v (Graph.target g a)) (Hfree a Hin)).
Qed.

Lemma edge_candidate_unique {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v e a : ready EV g p -> edge_dominates g e v ->
  Graph.target g e = v -> In a (Graph.out g (Graph.source g a)) ->
  Graph.target g a = v -> ~ dominates g v (Graph.source g a) -> a = e.
Proof.
  intros Hready Hdom Het Hedge Hat Hnot.
  destruct (edge_nondominated_path EV g p v (Graph.source g a) Hready Hnot)
    as [s [es [Hentry [Hpath [_ Hfree]]]]].
  pose proof (path_snoc g s es (Graph.source g a) a Hpath eq_refl Hedge) as Hfull.
  rewrite Hat in Hfull; specialize (Hdom s (es ++ [a]) Hentry Hfull).
  apply in_app_or in Hdom; destruct Hdom as [Hin|[Heq|Hfalse]].
  - exfalso; exact (Hfree e Hin Het).
  - exact Heq.
  - contradiction.
Qed.

Lemma edge_index_complete {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v e : ready EV g p -> reachable g v ->
  Graph.target g e = v -> edge_dominates g e v ->
  Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e.
Proof.
  intros Hready Hreach Htarget Hdom.
  assert (Hv : In v (Graph.nodes g)) by
    (apply (reachable_in_nodes g v (proj1 Hready)); exact Hreach).
  assert (Hnot : ~ In v (Graph.entries g)).
  { intro Hentry; specialize (Hdom v [] Hentry (path_nil v)); contradiction. }
  apply reachable_iff_path in Hreach; destruct Hreach as [s [es [Hentry Hpath]]].
  destruct (edge_first_arrival EV g v s es Hnot Hentry Hpath) as [a [_ Ha]].
  assert (Ha_eq : a = e).
  { destruct Ha as [Hedge [Hat [_ Hnotdom]]].
    eapply edge_candidate_unique; eauto. }
  subst a.
  set (candidates := edge_dom_candidates p (dominator_tree p)
    (visited (dfs p FinSet.empty (Graph.entries g))) v).
  assert (Hin : In e candidates).
  { unfold candidates; apply (edge_dom_candidates_spec EV g p v e Hready Hv); exact Ha. }
  assert (Huniq : forall a, In a candidates -> a = e).
  { intros a Hina; unfold candidates in Hina.
    apply (edge_dom_candidates_spec EV g p v a Hready Hv) in Hina.
    destruct Hina as [Hedge [Hat [_ Hnotdom]]].
    eapply edge_candidate_unique; eauto. }
  assert (Hnodup : NoDup candidates).
  { unfold candidates, edge_dom_candidates; apply NoDup_filter.
    apply (pred_nodup (proj2 (proj2 Hready))). }
  assert (Hsingle : candidates = [e]).
  { destruct candidates as [|a rest]; [contradiction|].
    assert (Hahead : a = e) by (apply Huniq; left; reflexivity); subst a.
    inversion Hnodup as [|? ? Hfresh _]; subst.
    destruct rest as [|b rest]; [reflexivity|].
    exfalso; apply Hfresh; assert (b = e) by (apply Huniq; right; left; reflexivity).
    subst b; left; reflexivity. }
  rewrite (edge_dom_index_lookup EV g p (dominator_tree p) v (proj1 Hready)).
  destruct (in_dec (dfs_eq_dec EV) v (Graph.nodes g)); [|contradiction].
  unfold edge_dom_choice.
  destruct (FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))) eqn:Hentrymem.
  - apply FinSet.of_list_spec in Hentrymem; contradiction.
  - change (match candidates with [a] => Some a | _ => None end = Some e).
    rewrite Hsingle; reflexivity.
Qed.

Lemma edge_last_visit {V E} (EV : encoding V) (g : Graph.t V E) d s es n :
  path g s es n -> (d = s \/ exists a, In a es /\ Graph.target g a = d) ->
  exists pre post, path g s pre d /\ path g d post n /\
    forall a, In a post -> Graph.target g a <> d.
Proof.
  intro Hpath; induction Hpath as [u|e es w Hedge Hpath IH]; intro Hvisit.
  - destruct Hvisit as [Heq|[a [Hin _]]]; [subst d|contradiction].
    exists [], []; repeat split; try constructor; intros a Hin; contradiction.
  - destruct (path_occurrence_dec EV g d (Graph.target g e) es) as [Htail|[Hstart Hfree]].
    + destruct (IH Htail) as [pre [post [Hpre [Hpost Havoid]]]].
      exists (e :: pre), post; split; [constructor; assumption|auto].
    + assert (Hsource : d = Graph.source g e).
      { destruct Hvisit as [Heq|[a [[Heq|Hin] Ha]]]; [exact Heq| |].
        - subst a; congruence.
        - exfalso; exact (Hfree a Hin Ha). }
      subst d; exists [], (e :: es); split; [constructor|]; split.
      * constructor; assumption.
      * intros a [Heq|Hin]; [subst a; congruence|apply Hfree; exact Hin].
Qed.

Lemma edge_dom_target {V E} (EV : encoding V) (g : Graph.t V E)
    e n : reachable g n -> edge_dominates g e n ->
  dominates g (Graph.target g e) n /\ edge_dominates g e (Graph.target g e).
Proof.
  intros Hreach Hdom; split.
  - intros s es Hentry Hpath; right; exists e; split; [apply Hdom with s; assumption|reflexivity].
  - apply reachable_iff_path in Hreach; destruct Hreach as [s [es [Hentry Hpath]]].
    assert (Hvisit : Graph.target g e = s \/
      exists a, In a es /\ Graph.target g a = Graph.target g e).
    { right; exists e; split; [apply Hdom with s; assumption|reflexivity]. }
    destruct (edge_last_visit EV g (Graph.target g e) s es n Hpath Hvisit)
      as [pre [post [_ [Hpost Havoid]]]].
    intros x path_x Hx Hpath_x.
    assert (Hfull : path g x (path_x ++ post) n).
    { eapply semi_path_app; eassumption. }
    specialize (Hdom x (path_x ++ post) Hx Hfull); apply in_app_or in Hdom.
    destruct Hdom as [Hin|Hin]; [exact Hin|].
    exfalso; exact (Havoid e Hin eq_refl).
Qed.

Lemma edge_dom_trans {V E} (g : Graph.t V E) e v n :
  edge_dominates g e v -> dominates g v n -> edge_dominates g e n.
Proof.
  intros Hedge Hdom s es Hentry Hpath.
  destruct (Hdom s es Hentry Hpath) as [Heq|[a [Hin Htarget]]].
  - subst v; specialize (Hedge s [] Hentry (path_nil s)); contradiction.
  - destruct (path_prefix_target g s es n a Hpath Hin) as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre; apply Hsub; apply Hedge with s; assumption.
Qed.

(** An edge dominates a reachable node exactly when an indexed edge dominates an ancestor. *)
Theorem edge_dominates_iff {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (n : V) (e : E) :
  ready EV g p -> dominator_exact p = true -> reachable g n ->
  (edge_dominates g e n <->
   exists v, Map.get EV v (edge_dom_index p (dominator_tree p)) = Some e /\
     dominates_b EV (dominator_tree p) v n = true).
Proof.
  intros Hready Hcheck Hreach; split.
  - intro Hedge; destruct (edge_dom_target EV g e n Hreach Hedge) as [Hdom Htarget].
    exists (Graph.target g e); split.
    + apply edge_index_complete; try assumption; [|reflexivity].
      eapply dom_dominator_reachable; eassumption.
    + apply (proj2 (proj1 (dominator_tree_exact EV g p Hready Hcheck)
        (Graph.target g e) n Hreach)); exact Hdom.
  - intros [v [Hindex Hbool]].
    eapply edge_dom_trans; [apply (edge_index_dominates EV g p v e Hready Hindex)|].
    eapply (proj1 (proj2 (proj2 (dominator_tree_sound EV g p Hready)))); exact Hbool.
Qed.

Definition edge_walk_sound {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n (state : option V * list E) : Prop :=
  (forall v, fst state = Some v -> idom_ancestor EV (idom t) v n) /\
  (forall e, In e (snd state) -> exists v, Map.get EV v ix = Some e /\
    idom_ancestor EV (idom t) v n).

Lemma edge_walk_sound_step {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n state : edge_walk_sound EV t ix n state ->
  edge_walk_sound EV t ix n (edge_dom_step EV t ix state).
Proof.
  destruct state as [[v|] edges]; intros [Hcurrent Hedges];
    unfold edge_dom_step, edge_walk_sound in *; cbn in *; [|auto].
  split.
  - intros u Hparent; eapply rt_trans; [apply rt_step; exact Hparent|].
    apply Hcurrent; reflexivity.
  - destruct (Map.get EV v ix) as [a|] eqn:Hget; cbn.
    + intros e [Heq|Hin]; [subst e; exists v; split; [exact Hget|apply Hcurrent; reflexivity]
        |apply Hedges; exact Hin].
    + exact Hedges.
Qed.

Lemma edge_walk_sound_iter {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n state k : edge_walk_sound EV t ix n state ->
  edge_walk_sound EV t ix n (Pos.iter (edge_dom_step EV t ix) state k).
Proof.
  intro Hstate; induction k using Pos.peano_ind.
  - apply edge_walk_sound_step; exact Hstate.
  - rewrite Pos.iter_succ; apply edge_walk_sound_step; exact IHk.
Qed.

(** Every edge returned by the parent-chain query dominates its node. *)
Theorem dominating_edges_sound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (n : V) (e : E) : ready EV g p ->
  In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) ->
  edge_dominates g e n.
Proof.
  intros Hready Hin; unfold dominating_edges in Hin; rewrite edge_dom_run_agrees in Hin.
  pose proof (edge_walk_sound_iter EV (dominator_tree p)
    (edge_dom_index p (dominator_tree p)) n (Some n, []) (fuel p)) as Hsound.
  assert (Hinitial : edge_walk_sound EV (dominator_tree p)
    (edge_dom_index p (dominator_tree p)) n (Some n, [])).
  { split; cbn; [intros v Heq; inversion Heq; apply rt_refl|intros a Hfalse; contradiction]. }
  destruct (proj2 (Hsound Hinitial) e Hin) as [v [Hindex Hanc]].
  eapply edge_dom_trans; [apply (edge_index_dominates EV g p v e Hready Hindex)|].
  apply (proj1 (proj2 (dominator_tree_sound EV g p Hready))); exact Hanc.
Qed.

Definition edge_walk_coverage {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n (state : option V * list E) : Prop :=
  forall v e, idom_ancestor EV (idom t) v n -> Map.get EV v ix = Some e ->
    In e (snd state) \/ exists u, fst state = Some u /\ idom_ancestor EV (idom t) v u.

Lemma edge_walk_coverage_step {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n state : edge_walk_coverage EV t ix n state ->
  edge_walk_coverage EV t ix n (edge_dom_step EV t ix state).
Proof.
  destruct state as [[u|] edges]; intros Hcoverage;
    unfold edge_walk_coverage, edge_dom_step in *; cbn in *; [|exact Hcoverage].
  intros v e Hanc Hget; destruct (Hcoverage v e Hanc Hget) as [Hin|[w [Heq Hw]]].
  - left; destruct (Map.get EV u ix); cbn; auto.
  - inversion Heq; subst w.
    destruct (dom_ancestor_last EV (idom t) v u Hw) as [Hsame|[parent [Hparent Hancparent]]].
    + subst v; rewrite Hget; left; cbn; auto.
    + right; exists parent; split; assumption.
Qed.

Lemma edge_walk_coverage_iter {V E} (EV : encoding V) (t : dom_tree V) (ix : Map.t V E)
    n state k : edge_walk_coverage EV t ix n state ->
  edge_walk_coverage EV t ix n (Pos.iter (edge_dom_step EV t ix) state k).
Proof.
  intro Hstate; induction k using Pos.peano_ind.
  - apply edge_walk_coverage_step; exact Hstate.
  - rewrite Pos.iter_succ; apply edge_walk_coverage_step; exact IHk.
Qed.

Lemma edge_dom_rank_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v : ready EV g p ->
  dom_rank p (simple_lt_idom p) v <= length (Graph.nodes g).
Proof.
  intro Hready.
  destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  set (m := simple_lt_idom p).
  set (f := dom_forest p m).
  assert (Hf : ready EV f (prepare EV f)).
  { apply (dom_forest_ready EV g p m Hready Hmap (proj1 Hforest)). }
  destruct (dfs_final_spec EV f (prepare EV f) FinSet.empty (Graph.entries f)
    Hf (entries_in (proj1 Hf))) as [Hinv [Hlabels _]].
  unfold dom_rank, dom_search; fold f.
  destruct (Map.get EV v (pre_num (dfs (prepare EV f) FinSet.empty (Graph.entries f))))
    as [k|] eqn:Hget; [|lia].
  unfold dfs in Hget; cbn [pre_num] in Hget.
  pose proof (dfs_numbering_bound EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v k Hget)
    as Hbound.
  apply Pos2Nat.inj_lt in Hbound.
  rewrite (dfs_numbering_size EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)) in Hbound.
  assert (Hincl : incl (DfsState.pre
    (fold_left (dfs_root (prepare EV f) FinSet.empty) (Graph.entries f) dfs_initial))
    (Graph.nodes g)).
  { intros x Hin; apply (reachable_in_nodes g x (proj1 Hready)).
    apply (dom_live EV g p m Hready).
    apply (dfs_pre_nodes _ _ _ _ _ _ Hinv); exact Hin. }
  pose proof (NoDup_incl_length (dfs_pre_nodup _ _ _ _ _ _ Hinv) Hincl); lia.
Qed.

Definition edge_walk_measure {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (state : option V * list E) : nat :=
  match fst state with
  | Some v => S (dom_rank p (simple_lt_idom p) v)
  | None => 0
  end.

Lemma edge_walk_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) ix v edges : ready EV g p ->
  edge_walk_measure p (edge_dom_step EV (dominator_tree p) ix (Some v, edges)) <
  edge_walk_measure p (Some v, edges).
Proof.
  intro Hready; destruct (simple_lt_idom_exact EV g p Hready) as [Hmap [Hforest Hexact]].
  unfold edge_dom_step, edge_walk_measure; cbn [fst].
  change (match Map.get EV v (simple_lt_idom p) with
    | Some u => S (dom_rank p (simple_lt_idom p) u)
    | None => 0
    end < S (dom_rank p (simple_lt_idom p) v)).
  destruct (Map.get EV v (simple_lt_idom p)) as [u|] eqn:Hparent; [|lia].
  pose proof (dom_parent_rank EV g p (simple_lt_idom p) Hready Hmap Hforest u v Hparent).
  lia.
Qed.

Lemma edge_walk_iter_bound {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) ix state k : ready EV g p ->
  let result := Pos.iter (edge_dom_step EV (dominator_tree p) ix) state k in
  fst result = None \/ edge_walk_measure p result + Pos.to_nat k <= edge_walk_measure p state.
Proof.
  intro Hready; induction k using Pos.peano_ind.
  - destruct state as [[v|] edges]; [|left; reflexivity].
    right; cbn [Pos.iter].
    pose proof (edge_walk_decreases EV g p ix v edges Hready); cbn in *; lia.
  - rewrite Pos.iter_succ.
    destruct (Pos.iter (edge_dom_step EV (dominator_tree p) ix) state k)
      as [[v|] edges] eqn:Hrun.
    + destruct IHk as [Hnone|Hbound]; [discriminate|].
      right; pose proof (edge_walk_decreases EV g p ix v edges Hready) as Hdec.
      rewrite Pos2Nat.inj_succ; cbn in *; lia.
    + left; reflexivity.
Qed.

Lemma edge_walk_finished {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (ix : Map.t V E) n : ready EV g p ->
  fst (Pos.iter (edge_dom_step EV (dominator_tree p) ix) (Some n, []) (fuel p)) = None.
Proof.
  intro Hready.
  destruct (edge_walk_iter_bound EV g p ix (Some n, []) (fuel p) Hready) as [Hdone|Hbound];
    [exact Hdone|].
  pose proof (edge_dom_rank_bound EV g p n Hready) as Hrank.
  rewrite (fuel_value (proj2 (proj2 Hready))) in Hbound.
  cbn [edge_walk_measure fst] in Hbound; lia.
Qed.

(** On reachable nodes, the parent-chain query returns exactly the dominating edges. *)
Theorem dominating_edges_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (n : V) (e : E) :
  ready EV g p -> dominator_exact p = true -> reachable g n ->
  (In e (dominating_edges p (dominator_tree p) (edge_dom_index p (dominator_tree p)) n) <->
   edge_dominates g e n).
Proof.
  intros Hready Hcheck Hreach; split.
  - apply dominating_edges_sound; exact Hready.
  - intro Hedge.
    destruct (proj1 (edge_dominates_iff EV g p n e Hready Hcheck Hreach) Hedge)
      as [v [Hindex Hbool]].
    assert (Hdom : dominates g v n).
    { eapply (proj1 (proj2 (proj2 (dominator_tree_sound EV g p Hready)))); exact Hbool. }
    destruct (simple_lt_idom_exact EV g p Hready) as [_ [_ Hexact]].
    assert (Hanc : idom_ancestor EV (idom (dominator_tree p)) v n).
    { change (idom_ancestor EV (simple_lt_idom p) v n).
      apply (Hexact v n Hreach); exact Hdom. }
    assert (Hinitial : edge_walk_coverage EV (dominator_tree p)
      (edge_dom_index p (dominator_tree p)) n (Some n, [])).
    { intros d a Hd Ha; right; exists n; split; [reflexivity|exact Hd]. }
    pose proof (edge_walk_coverage_iter EV (dominator_tree p)
      (edge_dom_index p (dominator_tree p)) n (Some n, []) (fuel p) Hinitial v e Hanc Hindex)
      as Hcoverage.
    unfold dominating_edges; rewrite edge_dom_run_agrees.
    destruct Hcoverage as [Hin|[u [Hcurrent _]]]; [exact Hin|].
    rewrite (edge_walk_finished EV g p (edge_dom_index p (dominator_tree p)) n Hready)
      in Hcurrent; discriminate.
Qed.

Lemma edge_path_prefix {V E} (g : Graph.t V E) s es n e :
  path g s es n -> In e es ->
  exists pre, path g s pre (Graph.source g e) /\ (length pre < length es)%nat.
Proof.
  intro Hpath; induction Hpath as [v|a es w Hedge Hpath IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; exists []; split; [constructor|simpl; lia].
    + destruct (IH Hin) as [pre [Hpre Hlength]].
      exists (a :: pre); split; [constructor; assumption|simpl; lia].
Qed.

(** A self-loop cannot dominate the first arrival at its node. *)
Theorem self_loop_not_edge_dominating {V E} (g : Graph.t V E) (n : V) (e : E) :
  reachable g n -> Graph.source g e = n -> Graph.target g e = n ->
  ~ edge_dominates g e n.
Proof.
  intros Hreach Hsource _ Hdom.
  apply reachable_iff_path in Hreach; destruct Hreach as [s [es [Hs Hpath]]].
  remember (length es) as k eqn:Hlength; revert es Hpath Hlength.
  induction k using lt_wf_ind; intros es Hpath Hlength.
  destruct (edge_path_prefix g s es n e Hpath (Hdom s es Hs Hpath))
    as [pre [Hpre Hshort]].
  rewrite Hsource in Hpre.
  eapply (H (length pre)); [lia|exact Hpre|reflexivity].
Qed.
