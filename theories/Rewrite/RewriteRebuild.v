(** * Direct congruence rebuilding

    A finite worklist revisits congruence obligations only for parents of merged classes.
    For example, merging two children queues applications that still mention either old alias.
    Builds on: RewriteEgraph and RewriteIndex. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex.
Import List.ListNotations.

(** * Congruent productions *)

Lemma rw_node_productive {K Sort V} (sig : rw_signature K Sort V) g node :
  rw_layout sig g -> rw_productive g -> rw_node_valid sig g node ->
  exists t, rw_node_represents g node t.
Proof.
  intros Hwf Hproductive Hvalid; destruct node as [s v|s op ids].
  - exists (RWVar s v); constructor.
  - pose proof (rw_node_valid_children sig g s op ids Hwf Hvalid) as Hdomains.
    assert (Hterms : exists ts, Forall2 (rw_represents g) ids ts).
    { clear Hvalid; induction Hdomains as [|id ids [root Hroot] Hrest [ts Hts]].
      - exists []; constructor.
      - destruct (Hproductive id root Hroot) as [t Ht]; exists (t :: ts); constructor; assumption. }
    destruct Hterms as [ts Hts]; exists (RWApp s op ts); constructor; exact Hts.
Qed.

Lemma rw_node_at_valid {K Sort V} (sig : rw_signature K Sort V) g n owner node :
  rw_layout sig g -> rw_node_at g n = Some (owner, node) -> rw_node_valid sig g node.
Proof.
  intros Hwf Hnode; destruct node as [s v|s op ids].
  - exact (rw_layout_var sig g Hwf n owner s v Hnode).
  - exact (rw_layout_app sig g Hwf n owner s op ids Hnode).
Qed.

Lemma rw_node_at_find {K Sort V} (sig : rw_signature K Sort V) g n owner node :
  rw_layout sig g -> rw_node_at g n = Some (owner, node) ->
  exists root, rw_find g owner = Some root.
Proof.
  intros Hwf Hnode; apply (proj1 (rw_layout_domain sig g Hwf owner)).
  exists (rw_node_sort node); exact (rw_layout_owner sig g Hwf n owner node Hnode).
Qed.

Lemma rw_common_term_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    g a b t :
  rw_graph_sound sig admissible rules g -> rw_represents g a t -> rw_represents g b t ->
  rw_joinable sig admissible rules g a b.
Proof.
  intros Hsound Ha Hb; split; [eauto|]; split; [eauto|].
  intros u v Hu Hv; eapply rw_eq_trans; [exact (Hsound a u t Hu Ha)|].
  exact (Hsound b t v Hb Hv).
Qed.

Lemma rw_congruent_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    g n m a b node other :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
  rw_canonical_node g node = rw_canonical_node g other ->
  rw_joinable sig admissible rules g a b.
Proof.
  intros Hwf Hsound Hproductive Hnode Hother Heq; pose proof (rw_wf_layout sig g Hwf) as Hl.
  destruct (rw_node_productive sig g node Hl Hproductive (rw_node_at_valid sig g n a node Hl Hnode))
    as [t Ht].
  assert (Hu : rw_node_represents g other t).
  { apply (proj1 (rw_canonical_node_represents sig g other t Hl)); rewrite <- Heq.
    apply (proj2 (rw_canonical_node_represents sig g node t Hl)); exact Ht. }
  destruct (rw_node_at_find sig g n a node Hl Hnode) as [ra Ha].
  destruct (rw_node_at_find sig g m b other Hl Hother) as [rb Hb].
  apply (rw_common_term_joinable sig admissible rules g a b t Hsound).
  - destruct Ht as [s v|s op ids ts Hargs].
    + exact (rw_repr_var g a n a ra s v Hnode Ha Ha).
    + exact (rw_repr_app g a n a ra s op ids ts Hnode Ha Ha Hargs).
  - destruct Hu as [s v|s op ids ts Hargs].
    + exact (rw_repr_var g b m b rb s v Hother Hb Hb).
    + exact (rw_repr_app g b m b rb s op ids ts Hother Hb Hb Hargs).
Qed.

Lemma rw_canonical_node_sort {K Sort V} (g : rw_graph K Sort V) node :
  rw_node_sort (rw_canonical_node g node) = rw_node_sort node.
Proof.
  destruct node; reflexivity.
Qed.

Lemma rw_congruent_union {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V)
    g n m a b node other ra rb :
  rw_graph_wf sig g -> rw_node_at g n = Some (a, node) ->
  rw_node_at g m = Some (b, other) -> rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_canonical_node g node = rw_canonical_node g other ->
  rw_union ES g a b = Some (rw_merge g ra rb).
Proof.
  intros Hwf Hnode Hother Ha Hb Heq; pose proof (rw_wf_layout sig g Hwf) as Hl.
  pose proof (rw_layout_owner sig g Hl n a node Hnode) as Hsa.
  pose proof (rw_layout_owner sig g Hl m b other Hother) as Hsb.
  assert (Hs : rw_node_sort node = rw_node_sort other).
  { rewrite <- (rw_canonical_node_sort g node), <- (rw_canonical_node_sort g other); congruence. }
  unfold rw_union; rewrite Ha, Hb, Hsa, Hsb, Hs.
  destruct (Pos.eq_dec (encode ES (rw_node_sort other)) (encode ES (rw_node_sort other)));
    congruence.
Qed.

(** * Prepared congruence partners *)

Definition rw_pair := (rw_id * rw_id)%type.

Definition rw_pair_dec (x y : rw_pair) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Pos.eq_dec.
Defined.

Definition rw_variable_keys {K Sort V} (EN : encoding (rw_node K Sort V))
    (node : rw_node K Sort V) : list rw_id :=
  match node with
  | RWNVar s v => [encode EN (RWNVar s v)]
  | RWNApp _ _ _ => []
  end.

(** Partner preparation uses operator buckets for applications and exact keys for variables. *)
Definition rw_partners {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) (ix : rw_index K) vars n : list rw_id :=
  match rw_node_at base n with
  | Some (_, RWNVar s v) => rw_lookup_list positive_encoding (encode EN (RWNVar s v)) vars
  | Some (_, RWNApp _ op _) => rw_lookup_list EK op (rw_index_ops ix)
  | None => []
  end.

Definition rw_pairs_for {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) ix vars n : list rw_pair :=
  map (fun m => (n, m)) (rw_partners EK EN base ix vars n).

Definition rw_pair_universe {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (base : rw_graph K Sort V) ix vars : list rw_pair :=
  flat_map (rw_pairs_for EK EN base ix vars) (rw_nodes_in base).

Lemma rw_pairs_complete {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base ix vars (g : rw_graph K Sort V) n m a b node other :
  rw_graph_wf sig base -> rw_index_agrees EK base ix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_node_at base n = Some (a, node) -> rw_node_at base m = Some (b, other) ->
  rw_canonical_node g node = rw_canonical_node g other ->
  In (n, m) (rw_pairs_for EK EN base ix vars n).
Proof.
  intros Hwf Hix [Hvarwf Hvars] Hnode Hother Heq; unfold rw_pairs_for.
  apply in_map; unfold rw_partners; rewrite Hnode.
  destruct node as [s v|s op ids], other as [s' v'|s' op' ids']; cbn in Heq;
    try discriminate.
  - injection Heq as <- <-; apply Hvars; exists b, (RWNVar s v); cbn; auto.
  - injection Heq as Hsort Hop Hids; subst op'.
    destruct Hix as [_ [_ [_ [_ [_ [_ [Hops Hrest]]]]]]]; apply Hops; eauto 6.
Qed.

Lemma rw_pairs_in_universe {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base ix vars n a node pair :
  rw_graph_wf sig base -> rw_node_at base n = Some (a, node) ->
  In pair (rw_pairs_for EK EN base ix vars n) ->
  In pair (rw_pair_universe EK EN base ix vars).
Proof.
  intros Hwf Hnode Hin; unfold rw_pair_universe; apply in_flat_map; exists n; split.
  - apply (proj2 (rw_layout_enumerates sig base (rw_wf_layout sig base Hwf) n)); eauto.
  - exact Hin.
Qed.

(** Either orientation keeps a congruence obligation pending. *)
Definition rw_pending (pending : list rw_pair) n m : Prop :=
  In (n, m) pending \/ In (m, n) pending.

(** Every obligation outside the worklist is already closed under the current partition. *)
Definition rw_processed {K Sort V} (g : rw_graph K Sort V) pending : Prop :=
  forall n m a b node other,
    rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
    ~ rw_pending pending n m -> rw_canonical_node g node = rw_canonical_node g other ->
    rw_find g a = rw_find g b.

Lemma rw_processed_initial {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base ix vars :
  rw_graph_wf sig base -> rw_index_agrees EK base ix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_processed base (nodup rw_pair_dec (rw_pair_universe EK EN base ix vars)).
Proof.
  intros Hwf Hix Hvars n m a b node other Hnode Hother Hnot Heq; exfalso; apply Hnot; left.
  apply nodup_In; apply (rw_pairs_in_universe EK EN sig base ix vars n a node (n, m)
    Hwf Hnode); exact (rw_pairs_complete EK EN sig base ix vars base n m a b node other
      Hwf Hix Hvars Hnode Hother Heq).
Qed.

Lemma rw_processed_drop {K Sort V} (g : rw_graph K Sort V) n m rest a b node other :
  rw_processed g ((n, m) :: rest) ->
  rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
  (rw_canonical_node g node = rw_canonical_node g other -> rw_find g a = rw_find g b) ->
  rw_processed g rest.
Proof.
  intros Hprocessed Hnode Hother Hpair x y ox oy nx ny Hx Hy Hnot Heq.
  destruct (rw_pair_dec (x, y) (n, m)) as [Hxy|Hxy].
  - injection Hxy as -> ->; assert (nx = node /\ ox = a) by (split; congruence).
    assert (ny = other /\ oy = b) by (split; congruence); intuition subst;
      apply Hpair; exact Heq.
  - destruct (rw_pair_dec (y, x) (n, m)) as [Hyx|Hyx].
    + injection Hyx as -> ->; assert (nx = other /\ ox = b) by (split; congruence).
      assert (ny = node /\ oy = a) by (split; congruence); intuition subst; symmetry; apply Hpair;
        symmetry; exact Heq.
    + apply (Hprocessed x y ox oy nx ny Hx Hy); [|exact Heq].
      unfold rw_pending in *; cbn; intuition congruence.
Qed.

(** * Affected-parent coverage *)

Lemma rw_parent_allocated {K Sort V} (EK : encoding K) (g : rw_graph K Sort V) ix c n :
  rw_index_agrees EK g ix -> In n (rw_parent_nodes g ix c) ->
  exists owner node, rw_node_at g n = Some (owner, node).
Proof.
  intros Hix Hin; apply (rw_parent_nodes_agree EK g ix c n Hix) in Hin.
  destruct Hin as [root [owner [s [op [ids [child [Hc [Hchild [Hnode Hin]]]]]]]]].
  exists owner, (RWNApp s op ids); exact Hnode.
Qed.

Lemma rw_canonical_id_unaffected {K Sort V} (g : rw_graph K Sort V) ra rb child :
  rw_find g child <> Some rb ->
  rw_canonical_id (rw_merge g ra rb) child = rw_canonical_id g child.
Proof.
  intro Hne; unfold rw_canonical_id; rewrite rw_merge_find.
  destruct (rw_find g child) as [root|] eqn:Hfind; cbn; [|reflexivity].
  rewrite rw_collapse_other; [reflexivity|congruence].
Qed.

Lemma rw_canonical_node_not_parent {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    ix b ra rb n owner node :
  rw_index_agrees EK g ix -> rw_find g b = Some rb ->
  rw_node_at g n = Some (owner, node) -> ~ In n (rw_parent_nodes g ix b) ->
  rw_canonical_node (rw_merge g ra rb) node = rw_canonical_node g node.
Proof.
  intros Hix Hb Hnode Hnot; destruct node as [s v|s op ids]; [reflexivity|].
  cbn [rw_canonical_node]; f_equal; apply map_ext_in; intros child Hin.
  apply rw_canonical_id_unaffected; intro Hchild; apply Hnot.
  apply (rw_parent_nodes_agree EK g ix b n Hix).
  exists rb, owner, s, op, ids, child; repeat split; assumption.
Qed.

Definition rw_enqueue {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    base baseix vars (g : rw_graph K Sort V) ix a b rest : list rw_pair :=
  nodup rw_pair_dec (flat_map (rw_pairs_for EK EN base baseix vars)
    (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b) ++ rest).

Lemma rw_enqueue_rest {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    base baseix vars (g : rw_graph K Sort V) ix a b rest n m :
  rw_pending rest n m -> rw_pending (rw_enqueue EK EN base baseix vars g ix a b rest) n m.
Proof.
  unfold rw_pending, rw_enqueue; intro Hin; destruct Hin as [Hin|Hin];
    [left|right]; apply nodup_In; apply in_or_app; auto.
Qed.

Lemma rw_enqueue_covers {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base baseix vars (g h : rw_graph K Sort V)
    ix a b rest n m owner other node node' :
  rw_graph_wf sig base -> rw_index_agrees EK base baseix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_node_at base n = Some (owner, node) -> rw_node_at base m = Some (other, node') ->
  rw_canonical_node h node = rw_canonical_node h node' ->
  In n (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b) ->
  rw_pending (rw_enqueue EK EN base baseix vars g ix a b rest) n m.
Proof.
  intros Hwf Hix Hvars Hnode Hother Heq Hin; left; unfold rw_enqueue; apply nodup_In.
  apply in_or_app; left; apply in_flat_map; exists n; split; [exact Hin|].
  exact (rw_pairs_complete EK EN sig base baseix vars h n m owner other node node'
    Hwf Hix Hvars Hnode Hother Heq).
Qed.

Lemma rw_processed_merge {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base baseix vars g ix n m rest a b node other ra rb :
  rw_graph_wf sig base -> rw_index_agrees EK base baseix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  (forall id, rw_node_at g id = rw_node_at base id) -> rw_index_agrees EK g ix ->
  rw_processed g ((n, m) :: rest) ->
  rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
  rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_processed (rw_merge g ra rb) (rw_enqueue EK EN base baseix vars g ix a b rest).
Proof.
  intros Hbase Hbaseix Hvars Hnodes Hix Hprocessed Hnode Hother Ha Hb.
  intros x y ox oy nx ny Hx Hy Hnot Heq.
  change (rw_node_at g x = Some (ox, nx)) in Hx.
  change (rw_node_at g y = Some (oy, ny)) in Hy.
  assert (Hnx : ~ In x (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b)).
  { intro Hin; apply Hnot.
    exact (rw_enqueue_covers EK EN sig base baseix vars g (rw_merge g ra rb)
      ix a b rest x y ox oy nx ny Hbase Hbaseix Hvars
      (eq_trans (eq_sym (Hnodes x)) Hx) (eq_trans (eq_sym (Hnodes y)) Hy) Heq Hin). }
  assert (Hny : ~ In y (rw_parent_nodes g ix a ++ rw_parent_nodes g ix b)).
  { intro Hin; apply Hnot; unfold rw_pending.
    pose proof (rw_enqueue_covers EK EN sig base baseix vars g (rw_merge g ra rb)
      ix a b rest y x oy ox ny nx Hbase Hbaseix Hvars
      (eq_trans (eq_sym (Hnodes y)) Hy) (eq_trans (eq_sym (Hnodes x)) Hx) (eq_sym Heq) Hin)
      as Hpending; destruct Hpending; auto. }
  assert (Hstablex : rw_canonical_node (rw_merge g ra rb) nx = rw_canonical_node g nx).
  { apply (rw_canonical_node_not_parent EK g ix b ra rb x ox nx Hix Hb Hx).
    intro Hin; apply Hnx; apply in_or_app; auto. }
  assert (Hstabley : rw_canonical_node (rw_merge g ra rb) ny = rw_canonical_node g ny).
  { apply (rw_canonical_node_not_parent EK g ix b ra rb y oy ny Hix Hb Hy).
    intro Hin; apply Hny; apply in_or_app; auto. }
  rewrite Hstablex, Hstabley in Heq.
  assert (Hrest : ~ rw_pending rest x y).
  { intro Hin; apply Hnot; exact (rw_enqueue_rest EK EN base baseix vars g ix a b rest x y Hin). }
  assert (Hmerged : rw_find (rw_merge g ra rb) a = rw_find (rw_merge g ra rb) b).
  { rewrite !rw_merge_find, Ha, Hb; cbn; rewrite rw_collapse_fixed, rw_collapse_same; reflexivity. }
  destruct (rw_pair_dec (x, y) (n, m)) as [Hxy|Hxy].
  - injection Hxy as -> ->; assert (ox = a) by congruence; assert (oy = b) by congruence.
    subst ox oy; exact Hmerged.
  - destruct (rw_pair_dec (y, x) (n, m)) as [Hyx|Hyx].
    + injection Hyx as -> ->; assert (ox = b) by congruence; assert (oy = a) by congruence.
      subst ox oy; symmetry; exact Hmerged.
    + rewrite !rw_merge_find; f_equal; apply (Hprocessed x y ox oy nx ny Hx Hy); [|exact Heq].
      unfold rw_pending in *; cbn; intuition congruence.
Qed.

(** * Finite worklist transition *)

Record rw_rebuild_state (K Sort V : Type) : Type := RwRebuildState {
  rw_state_graph : rw_graph K Sort V;
  rw_state_index : rw_index K;
  rw_state_pending : list rw_pair
}.

Arguments RwRebuildState {K Sort V}.
Arguments rw_state_graph {K Sort V}.
Arguments rw_state_index {K Sort V}.
Arguments rw_state_pending {K Sort V}.

(** The worklist invariant retains exact indexes and all discharged congruence obligations. *)
Record rw_rebuild_invariant {K Sort V H C} (EK : encoding K)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) base universe (st : rw_rebuild_state K Sort V) :
    Prop := {
  rw_state_wf : rw_graph_wf sig (rw_state_graph st);
  rw_state_sound : rw_graph_sound sig admissible rules (rw_state_graph st);
  rw_state_productive : rw_productive (rw_state_graph st);
  rw_state_agrees : rw_index_agrees EK (rw_state_graph st) (rw_state_index st);
  rw_state_nodes : forall n, rw_node_at (rw_state_graph st) n = rw_node_at base n;
  rw_state_nodup : NoDup (rw_state_pending st);
  rw_state_subset : incl (rw_state_pending st) universe;
  rw_state_processed : rw_processed (rw_state_graph st) (rw_state_pending st);
  rw_state_extends : rw_extends base (rw_state_graph st)
}.

Definition rw_rebuild_step {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EN : encoding (rw_node K Sort V)) base baseix vars (st : rw_rebuild_state K Sort V) :
    rw_rebuild_state K Sort V :=
  let g := rw_state_graph st in
  let ix := rw_state_index st in
  match rw_state_pending st with
  | [] => st
  | (n, m) :: rest =>
    let dropped := RwRebuildState g ix rest in
    match rw_node_at g n, rw_node_at g m with
    | Some (a, node), Some (b, other) =>
      match rw_find g a, rw_find g b with
      | Some ra, Some rb =>
        if Pos.eq_dec (encode EN (rw_canonical_node g node))
          (encode EN (rw_canonical_node g other)) then
          if Pos.eq_dec ra rb then dropped else
          match rw_union ES g a b with
          | Some g' => RwRebuildState g' (rw_index_after_union g g' ix a b)
            (rw_enqueue EK EN base baseix vars g ix a b rest)
          | None => dropped
          end
        else dropped
      | _, _ => dropped
      end
    | _, _ => dropped
    end
  end.

Lemma rw_pairs_allocated {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base ix vars n m :
  rw_graph_wf sig base -> rw_index_agrees EK base ix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  In (n, m) (rw_pair_universe EK EN base ix vars) ->
  (exists owner node, rw_node_at base n = Some (owner, node)) /\
  (exists owner node, rw_node_at base m = Some (owner, node)).
Proof.
  intros Hwf Hix [Hvarwf Hvars] Hin; unfold rw_pair_universe in Hin; apply in_flat_map in Hin.
  destruct Hin as [id [Hid Hin]]; unfold rw_pairs_for in Hin; apply in_map_iff in Hin.
  destruct Hin as [other [Heq Hin]]; injection Heq as -> ->.
  destruct (proj1 (rw_layout_enumerates sig base (rw_wf_layout sig base Hwf) n) Hid)
    as [owner [node Hnode]]; split; [eauto|].
  unfold rw_partners in Hin; rewrite Hnode in Hin; destruct node as [s v|s op ids].
  - apply Hvars in Hin; destruct Hin as [c [other [Hother Hkey]]]; eauto.
  - destruct Hix as [_ [_ [_ [_ [_ [_ [Hops Hrest]]]]]]]; apply Hops in Hin.
    destruct Hin as [c [s' [ids' Hother]]]; exists c, (RWNApp s' op ids'); exact Hother.
Qed.

Lemma rw_rebuild_drop_invariant {K Sort V H C} (EK : encoding K)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) base universe g ix n m rest a b node other :
  rw_rebuild_invariant EK sig admissible rules base universe
    (RwRebuildState g ix ((n, m) :: rest)) ->
  rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
  (rw_canonical_node g node = rw_canonical_node g other -> rw_find g a = rw_find g b) ->
  rw_rebuild_invariant EK sig admissible rules base universe (RwRebuildState g ix rest).
Proof.
  intros [Hwf Hsound Hproductive Hix Hnodes Hnd Hsub Hprocessed Hext] Hnode Hother Hpair.
  constructor; try assumption.
  - inversion Hnd; assumption.
  - intros pair Hin; apply Hsub; cbn; auto.
  - exact (rw_processed_drop g n m rest a b node other Hprocessed Hnode Hother Hpair).
Qed.

Lemma rw_enqueue_subset {K Sort V} (EK : encoding K) (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) base baseix vars g ix a b rest :
  rw_graph_wf sig base -> rw_index_agrees EK g ix ->
  (forall n, rw_node_at g n = rw_node_at base n) ->
  incl rest (rw_pair_universe EK EN base baseix vars) ->
  incl (rw_enqueue EK EN base baseix vars g ix a b rest)
    (rw_pair_universe EK EN base baseix vars).
Proof.
  intros Hbase Hix Hnodes Hrest pair Hin; unfold rw_enqueue in Hin; apply nodup_In in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin|Hin]; [|exact (Hrest pair Hin)].
  apply in_flat_map in Hin; destruct Hin as [parent [Hparent Hin]].
  apply in_app_iff in Hparent; destruct Hparent as [Hparent|Hparent];
    [destruct (rw_parent_allocated EK g ix a parent Hix Hparent) as [owner [node Hnode]]|
     destruct (rw_parent_allocated EK g ix b parent Hix Hparent) as [owner [node Hnode]]];
    apply (rw_pairs_in_universe EK EN sig base baseix vars parent owner node pair Hbase);
    [rewrite <- Hnodes; exact Hnode|exact Hin|rewrite <- Hnodes; exact Hnode|exact Hin].
Qed.

Lemma rw_merge_root_decrease {K Sort V} (sig : rw_signature K Sort V) g ra rb :
  rw_graph_wf sig g -> rw_find g ra = Some ra -> rw_find g rb = Some rb -> ra <> rb ->
  length (rw_roots (rw_merge g ra rb)) < length (rw_roots g).
Proof.
  intros Hwf Hra Hrb Hne; pose proof (rw_wf_layout sig g Hwf) as Hl.
  pose proof (proj1 (rw_layout_find sig g Hl ra ra Hra)) as Hina.
  pose proof (proj1 (rw_layout_find sig g Hl rb rb Hrb)) as Hinb.
  set (kept := filter (fun r => negb (Pos.eqb r ra || Pos.eqb r rb)) (rw_roots g)).
  assert (Hkeep : forall r, In r kept -> In r (rw_roots g) /\ r <> ra /\ r <> rb).
  { intro r; unfold kept; rewrite filter_In, Bool.negb_true_iff, Bool.orb_false_iff,
      !Pos.eqb_neq; tauto. }
  assert (Hnd : NoDup (ra :: rb :: kept)).
  { constructor.
    - intros [Heq|Hin]; [congruence|destruct (Hkeep ra Hin); tauto].
    - constructor.
      + intro Hin; destruct (Hkeep rb Hin); tauto.
      + apply NoDup_filter; exact (rw_layout_roots sig g Hl). }
  assert (Hincl : incl (ra :: rb :: kept) (rw_roots g)).
  { intros r [->|[->|Hin]]; [exact Hina|exact Hinb|exact (proj1 (Hkeep r Hin))]. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlength.
  change (S (length kept) < length (rw_roots g)).
  change (S (S (length kept)) <= length (rw_roots g)) in Hlength; lia.
Qed.

Definition rw_rebuild_measure {K Sort V} (universe : list rw_pair)
    (st : rw_rebuild_state K Sort V) : nat :=
  length (rw_roots (rw_state_graph st)) * S (length universe) + length (rw_state_pending st).

Lemma rw_rebuild_merge_invariant {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EN : encoding (rw_node K Sort V)) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    base baseix vars g ix n m rest a b node other ra rb :
  rw_graph_wf sig base -> rw_index_agrees EK base baseix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars)
    (RwRebuildState g ix ((n, m) :: rest)) ->
  rw_node_at g n = Some (a, node) -> rw_node_at g m = Some (b, other) ->
  rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_canonical_node g node = rw_canonical_node g other ->
  rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars)
    (RwRebuildState (rw_merge g ra rb)
      (rw_index_after_union g (rw_merge g ra rb) ix a b)
      (rw_enqueue EK EN base baseix vars g ix a b rest)).
Proof.
  intros Hbase Hbaseix Hvars Hinv Hnode Hother Ha Hb Heq.
  destruct Hinv as [Hwf Hsound Hproductive Hix Hnodes Hnd Hsub Hprocessed Hext].
  pose proof (rw_congruent_union ES sig g n m a b node other ra rb Hwf Hnode Hother Ha Hb Heq)
    as Hunion.
  pose proof (rw_congruent_joinable sig admissible rules g n m a b node other
    Hwf Hsound Hproductive Hnode Hother Heq) as Hjoin.
  destruct (rw_union_correct ES sig admissible rules g _ a b
    Hwf Hsound Hproductive Hjoin Hunion) as [Hwf' [Hsound' [Hproductive' [Hext' Hmerged]]]].
  constructor; try assumption.
  - exact (rw_index_after_union_agrees EK ES sig g _ ix a b Hwf Hix Hunion).
  - apply NoDup_nodup.
  - apply (rw_enqueue_subset EK EN sig base baseix vars g ix a b rest Hbase Hix Hnodes).
    intros pair Hin; apply Hsub; cbn; auto.
  - exact (rw_processed_merge EK EN sig base baseix vars g ix n m rest a b node other ra rb
      Hbase Hbaseix Hvars Hnodes Hix Hprocessed Hnode Hother Ha Hb).
  - eapply rw_extends_trans; eassumption.
Qed.

Lemma rw_rebuild_step_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EN : encoding (rw_node K Sort V)) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    base baseix vars st :
  rw_graph_wf sig base -> rw_index_agrees EK base baseix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars) st ->
  let next := rw_rebuild_step EK ES EN base baseix vars st in
  rw_rebuild_invariant EK sig admissible rules base
    (rw_pair_universe EK EN base baseix vars) next /\
  (rw_state_pending st <> [] ->
    rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) next <
      rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st).
Proof.
  intros Hbase Hbaseix Hvars Hinv; destruct st as [g ix [|[n m] rest]].
  - split; [exact Hinv|contradiction].
  - pose proof Hinv as [Hwf Hsound Hproductive Hix Hnodes Hnd Hsub Hprocessed Hext].
    cbn [rw_state_graph rw_state_index rw_state_pending] in Hnodes.
    destruct (rw_pairs_allocated EK EN sig base baseix vars n m Hbase Hbaseix Hvars
      (Hsub (n, m) (or_introl eq_refl))) as [[a [node Hnode]] [b [other Hother]]].
    rewrite <- Hnodes in Hnode, Hother.
    pose proof (rw_wf_layout sig g Hwf) as Hl.
    destruct (rw_node_at_find sig g n a node Hl Hnode) as [ra Ha].
    destruct (rw_node_at_find sig g m b other Hl Hother) as [rb Hb].
    cbn [rw_rebuild_step rw_state_graph rw_state_index rw_state_pending].
    rewrite Hnode, Hother, Ha, Hb.
    destruct (Pos.eq_dec (encode EN (rw_canonical_node g node))
      (encode EN (rw_canonical_node g other))) as [Heq|Hne].
    + apply (encode_injective EN) in Heq; destruct (Pos.eq_dec ra rb) as [Hsame|Hdiff].
      * split.
        -- apply (rw_rebuild_drop_invariant EK sig admissible rules base _ g ix n m rest
             a b node other Hinv Hnode Hother); intro Hcan; congruence.
        -- unfold rw_rebuild_measure; cbn; lia.
      * pose proof (rw_congruent_union ES sig g n m a b node other ra rb
          Hwf Hnode Hother Ha Hb Heq) as Hunion; rewrite Hunion.
        pose proof (rw_rebuild_merge_invariant EK ES EN sig admissible rules base baseix vars
          g ix n m rest a b node other ra rb Hbase Hbaseix Hvars Hinv Hnode Hother Ha Hb Heq)
          as Hnext; split; [exact Hnext|].
        intros Hnonempty.
        pose proof (rw_state_nodup EK sig admissible rules base _ _ Hnext) as Hnd'.
        pose proof (rw_state_subset EK sig admissible rules base _ _ Hnext) as Hsub'.
        pose proof (NoDup_incl_length Hnd' Hsub') as Hlength.
        pose proof (proj1 (proj2 (rw_layout_find sig g Hl a ra Ha))) as Hra.
        pose proof (proj1 (proj2 (rw_layout_find sig g Hl b rb Hb))) as Hrb.
        pose proof (rw_merge_root_decrease sig g ra rb Hwf Hra Hrb Hdiff) as Hdecrease.
        unfold rw_rebuild_measure; cbn [rw_state_graph rw_state_pending] in *; cbn [length].
        nia.
    + split.
      * apply (rw_rebuild_drop_invariant EK sig admissible rules base _ g ix n m rest
          a b node other Hinv Hnode Hother); intro Hcan; exfalso; apply Hne; congruence.
      * unfold rw_rebuild_measure; cbn; lia.
Qed.

(** * Binary bounded iteration *)

(** The binary iterator stops immediately when its worklist is empty. *)
Fixpoint rw_repeat {A} (done : A -> bool) (step : A -> A) (fuel : positive) (st : A) : A :=
  if done st then st else
  match fuel with
  | xH => step st
  | xO p => rw_repeat done step p (rw_repeat done step p st)
  | xI p => rw_repeat done step p (rw_repeat done step p (step st))
  end.

Lemma rw_repeat_done {A} (done : A -> bool) step fuel (st : A) :
  done st = true -> rw_repeat done step fuel st = st.
Proof.
  intro Hdone; destruct fuel; cbn [rw_repeat]; now rewrite Hdone.
Qed.

Lemma rw_repeat_credit {A} (done : A -> bool) step (I : A -> Prop) measure :
  (forall st, I st -> I (step st) /\ (done st = false -> measure (step st) < measure st)) ->
  (forall st, done st = true -> step st = st) ->
  forall fuel st, I st ->
  I (rw_repeat done step fuel st) /\
  (done (rw_repeat done step fuel st) = false ->
    measure (rw_repeat done step fuel st) + Pos.to_nat fuel <= measure st).
Proof.
  intros Hstep Hdone fuel; induction fuel as [p IHp|p IHp|]; intros st HI;
    cbn [rw_repeat]; destruct (done st) eqn:Hstop.
  - split; [exact HI|congruence].
  - destruct (Hstep st HI) as [HI1 Hdecrease].
    destruct (IHp (step st) HI1) as [HI2 Hcredit2].
    destruct (IHp (rw_repeat done step p (step st)) HI2) as [HI3 Hcredit3].
    split; [exact HI3|]; intro Hout.
    assert (Hstop2 : done (rw_repeat done step p (step st)) = false).
    { destruct (done (rw_repeat done step p (step st))) eqn:Hdone2; [|reflexivity].
      rewrite (rw_repeat_done done step p _ Hdone2) in Hout; congruence. }
    assert (Hstop1 : done (step st) = false).
    { destruct (done (step st)) eqn:Hdone1; [|reflexivity].
      rewrite (rw_repeat_done done step p _ Hdone1) in Hstop2; congruence. }
    specialize (Hcredit2 Hstop2); specialize (Hcredit3 Hout); specialize (Hdecrease Hstop).
    rewrite Pos2Nat.inj_xI; lia.
  - split; [exact HI|congruence].
  - destruct (IHp st HI) as [HI1 Hcredit1].
    destruct (IHp (rw_repeat done step p st) HI1) as [HI2 Hcredit2].
    split; [exact HI2|]; intro Hout.
    assert (Hstop1 : done (rw_repeat done step p st) = false).
    { destruct (done (rw_repeat done step p st)) eqn:Hdone1; [|reflexivity].
      rewrite (rw_repeat_done done step p _ Hdone1) in Hout; congruence. }
    specialize (Hcredit1 Hstop1); specialize (Hcredit2 Hout); rewrite Pos2Nat.inj_xO; lia.
  - split; [exact HI|congruence].
  - destruct (Hstep st HI) as [HI1 Hdecrease]; split; [exact HI1|].
    intro Hout; specialize (Hdecrease Hstop); cbn; lia.
Qed.

Definition rw_rebuild_done {K Sort V} (st : rw_rebuild_state K Sort V) : bool :=
  match rw_state_pending st with
  | [] => true
  | _ :: _ => false
  end.

Lemma rw_rebuild_run_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EN : encoding (rw_node K Sort V)) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    base baseix vars st :
  rw_graph_wf sig base -> rw_index_agrees EK base baseix ->
  rw_table_incidence positive_encoding base (rw_variable_keys EN) vars ->
  rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars) st ->
  let result := rw_repeat rw_rebuild_done (rw_rebuild_step EK ES EN base baseix vars)
    (Pos.of_succ_nat (rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st)) st in
  rw_rebuild_invariant EK sig admissible rules base
    (rw_pair_universe EK EN base baseix vars) result /\
  rw_state_pending result = [].
Proof.
  intros Hbase Hbaseix Hvars Hinv.
  pose proof (rw_repeat_credit rw_rebuild_done (rw_rebuild_step EK ES EN base baseix vars)
    (rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars))
    (rw_rebuild_measure (rw_pair_universe EK EN base baseix vars))) as Hcredit.
  assert (Hstep : forall st',
      rw_rebuild_invariant EK sig admissible rules base
        (rw_pair_universe EK EN base baseix vars) st' ->
      rw_rebuild_invariant EK sig admissible rules base (rw_pair_universe EK EN base baseix vars)
        (rw_rebuild_step EK ES EN base baseix vars st') /\
      (rw_rebuild_done st' = false ->
        rw_rebuild_measure (rw_pair_universe EK EN base baseix vars)
          (rw_rebuild_step EK ES EN base baseix vars st') <
        rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st')).
  { intros st' HI; destruct (rw_rebuild_step_correct EK ES EN sig admissible rules base baseix vars
      st' Hbase Hbaseix Hvars HI) as [HI' Hdecrease]; split; [exact HI'|].
    intro Hfalse; apply Hdecrease; intro Hempty; unfold rw_rebuild_done in Hfalse;
      rewrite Hempty in Hfalse; discriminate. }
  assert (Hdone : forall st', rw_rebuild_done st' = true ->
      rw_rebuild_step EK ES EN base baseix vars st' = st').
  { intros [g ix [|pair rest]] Hempty; [reflexivity|discriminate]. }
  destruct (Hcredit Hstep Hdone
    (Pos.of_succ_nat (rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st)) st Hinv)
    as [HIout Hbound]; split; [exact HIout|].
  destruct (rw_state_pending (rw_repeat rw_rebuild_done (rw_rebuild_step EK ES EN base baseix vars)
    (Pos.of_succ_nat (rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st)) st))
    as [|pair rest] eqn:Hpending; [reflexivity|].
  assert (Hfalse : rw_rebuild_done (rw_repeat rw_rebuild_done
      (rw_rebuild_step EK ES EN base baseix vars)
      (Pos.of_succ_nat (rw_rebuild_measure (rw_pair_universe EK EN base baseix vars) st)) st) =
      false).
  { unfold rw_rebuild_done at 1; rewrite Hpending; reflexivity. }
  specialize (Hbound Hfalse); rewrite SuccNat2Pos.id_succ in Hbound; lia.
Qed.

(** * Finite-term cleanliness *)

Lemma rw_canonical_ids_equal {K Sort V} (g : rw_graph K Sort V) a b :
  rw_find g a = rw_find g b -> (exists root, rw_find g a = Some root) ->
  rw_canonical_id g a = rw_canonical_id g b.
Proof.
  intros Heq [root Ha]; unfold rw_canonical_id; rewrite <- Heq, Ha; reflexivity.
Qed.

Lemma rw_canonical_children_equal {K Sort V} (g : rw_graph K Sort V) ids ts :
  Forall2 (fun id t => forall other, rw_represents g other t ->
    rw_find g id = rw_find g other) ids ts ->
  Forall2 (rw_represents g) ids ts ->
  forall others, Forall2 (rw_represents g) others ts ->
    map (rw_canonical_id g) ids = map (rw_canonical_id g) others.
Proof.
  intro Hargs; induction Hargs as [|id t ids ts IHt Hrest IHrest]; intros Hrepr others Hothers;
    inversion Hothers as [|other t' others' ts' Hother Htail]; subst.
  - reflexivity.
  - inversion Hrepr as [|id' t' ids' ts' Ht Hts]; subst; cbn; f_equal.
    + apply rw_canonical_ids_equal; [exact (IHt other Hother)|].
      exact (rw_represents_find g id t Ht).
    + exact (IHrest Hts _ Htail).
Qed.

Lemma rw_processed_clean {K Sort V} (g : rw_graph K Sort V) :
  rw_processed g [] -> rw_clean g.
Proof.
  intro Hprocessed; unfold rw_clean.
  assert (Hclean : forall a t, rw_represents g a t ->
      forall b, rw_represents g b t -> rw_find g a = rw_find g b).
  { apply (rw_represents_ind_all g (fun a t =>
        forall b, rw_represents g b t -> rw_find g a = rw_find g b)).
    - intros a n owner root s v Hnode Ho Ha b Hb.
      inversion Hb as [b' m other r s' v' Hother Hotherfind Hbfind|]; subst.
      pose proof (Hprocessed n m owner other (RWNVar s v) (RWNVar s v)
        Hnode Hother) as Hclosed.
      assert (Howners : rw_find g owner = rw_find g other).
      { apply Hclosed; [unfold rw_pending; cbn; tauto|reflexivity]. }
      congruence.
    - intros a n owner root s op ids ts Hnode Ho Ha Hargs IHargs b Hb.
      inversion Hb as [|b' m other r s' op' others ts' Hother Hotherfind Hbfind Hothers]; subst.
      assert (Hcan : rw_canonical_node g (RWNApp s op ids) =
          rw_canonical_node g (RWNApp s op others)).
      { cbn [rw_canonical_node]; f_equal.
        exact (rw_canonical_children_equal g ids ts IHargs Hargs others Hothers). }
      pose proof (Hprocessed n m owner other (RWNApp s op ids) (RWNApp s op others)
        Hnode Hother) as Hclosed.
      assert (Howners : rw_find g owner = rw_find g other).
      { apply Hclosed; [unfold rw_pending; cbn; tauto|exact Hcan]. }
      congruence. }
  intros a b t Ha Hb; exact (Hclean a t Ha b Hb).
Qed.

(** * Canonical production replacement *)

Definition rw_replace {K Sort V} (g : rw_graph K Sort V) n owner node : rw_graph K Sort V :=
  RwGraph (rw_roots g) (rw_nodes_in g) (rw_class_roots g) (rw_sorts g)
    (Map.set positive_encoding n (owner, node) (rw_nodes g)).

Lemma rw_replace_node_at {K Sort V} (g : rw_graph K Sort V) n owner node m :
  rw_node_at (rw_replace g n owner node) m =
    if Pos.eq_dec m n then Some (owner, node) else rw_node_at g m.
Proof.
  change (Map.get positive_encoding m (Map.set positive_encoding n (owner, node) (rw_nodes g)) =
    if Pos.eq_dec m n then Some (owner, node) else rw_node_at g m).
  destruct (Pos.eq_dec m n) as [->|Hne]; [apply Map.get_set_same|].
  apply Map.get_set_other; exact Hne.
Qed.

Lemma rw_canonical_sort {K Sort V} (sig : rw_signature K Sort V) g c :
  rw_layout sig g -> rw_class_sort g (rw_canonical_id g c) = rw_class_sort g c.
Proof.
  intro Hwf; unfold rw_canonical_id; destruct (rw_find g c) as [root|] eqn:Hfind;
    [|reflexivity].
  destruct (rw_layout_find sig g Hwf c root Hfind) as [_ [_ [s [Hc Hr]]]]; congruence.
Qed.

Lemma rw_canonical_node_valid {K Sort V} (sig : rw_signature K Sort V) g node :
  rw_layout sig g -> rw_node_valid sig g node -> rw_node_valid sig g (rw_canonical_node g node).
Proof.
  intros Hwf Hvalid; destruct node as [s v|s op ids]; [exact Hvalid|].
  destruct Hvalid as [sorts [Hsorts Hshape]]; exists sorts; split; [|exact Hshape].
  clear Hshape; induction Hsorts as [|id ty ids tys Hsort Hrest IHrest]; cbn; constructor.
  - rewrite (rw_canonical_sort sig g id Hwf); exact Hsort.
  - exact IHrest.
Qed.

Lemma rw_replace_layout {K Sort V} (sig : rw_signature K Sort V) g n owner old node :
  rw_layout sig g -> rw_node_at g n = Some (owner, old) ->
  rw_node_sort node = rw_node_sort old -> rw_node_valid sig g node ->
  rw_layout sig (rw_replace g n owner node).
Proof.
  intros Hwf Hnode Hsort Hvalid; constructor.
  - exact (rw_layout_roots sig g Hwf).
  - exact (rw_layout_nodes sig g Hwf).
  - exact (rw_layout_classes sig g Hwf).
  - exact (rw_layout_sorts sig g Hwf).
  - apply Map.wf_set; exact (rw_layout_productions sig g Hwf).
  - exact (rw_layout_find sig g Hwf).
  - exact (rw_layout_root sig g Hwf).
  - exact (rw_layout_domain sig g Hwf).
  - intro m; rewrite rw_replace_node_at; destruct (Pos.eq_dec m n) as [->|Hne].
    + split; intro Hin; [eauto|].
      apply (proj2 (rw_layout_enumerates sig g Hwf n)); eauto.
    + exact (rw_layout_enumerates sig g Hwf m).
  - intros m c other Hother; rewrite rw_replace_node_at in Hother.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + injection Hother as <- <-; change (rw_class_sort g owner = Some (rw_node_sort node)).
      rewrite Hsort; exact (rw_layout_owner sig g Hwf n owner old Hnode).
    + exact (rw_layout_owner sig g Hwf m c other Hother).
  - intros m c s v Hother; rewrite rw_replace_node_at in Hother.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + injection Hother as Howner Hother; subst c node; exact Hvalid.
    + exact (rw_layout_var sig g Hwf m c s v Hother).
  - intros m c s op ids Hother; rewrite rw_replace_node_at in Hother.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + injection Hother as Howner Hother; subst c node; exact Hvalid.
    + exact (rw_layout_app sig g Hwf m c s op ids Hother).
Qed.

Lemma rw_node_at_represents {K Sort V} (g : rw_graph K Sort V) c n owner root node t :
  rw_node_at g n = Some (owner, node) -> rw_find g owner = Some root ->
  rw_find g c = Some root -> rw_node_represents g node t -> rw_represents g c t.
Proof.
  intros Hnode Ho Hc Hrepr; destruct Hrepr as [s v|s op ids ts Hargs].
  - exact (rw_repr_var g c n owner root s v Hnode Ho Hc).
  - exact (rw_repr_app g c n owner root s op ids ts Hnode Ho Hc Hargs).
Qed.

Lemma rw_productions_extend {K Sort V} (g h : rw_graph K Sort V) :
  (forall c, rw_find h c = rw_find g c) ->
  (forall n owner node, rw_node_at g n = Some (owner, node) ->
    exists node', rw_node_at h n = Some (owner, node') /\
      forall t, rw_node_represents h node t -> rw_node_represents h node' t) ->
  rw_extends g h.
Proof.
  intros Hfind Hnodes; unfold rw_extends; apply (rw_represents_ind_all g (rw_represents h)).
  - intros c n owner root s v Hnode Ho Hc.
    destruct (Hnodes n owner (RWNVar s v) Hnode) as [node' [Hnode' Hlocal]].
    apply (rw_node_at_represents h c n owner root node' (RWVar s v) Hnode');
      [rewrite Hfind; exact Ho|rewrite Hfind; exact Hc|apply Hlocal; constructor].
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    destruct (Hnodes n owner (RWNApp s op ids) Hnode) as [node' [Hnode' Hlocal]].
    apply (rw_node_at_represents h c n owner root node' (RWApp s op ts) Hnode');
      [rewrite Hfind; exact Ho|rewrite Hfind; exact Hc|apply Hlocal; constructor; exact IHargs].
Qed.

Lemma rw_replace_canonical_correct {K Sort V} (sig : rw_signature K Sort V) g n owner node :
  rw_graph_wf sig g -> rw_node_at g n = Some (owner, node) ->
  let h := rw_replace g n owner (rw_canonical_node g node) in
  rw_graph_wf sig h /\ rw_extends g h /\ rw_extends h g.
Proof.
  intros Hwf Hnode; pose proof (rw_wf_layout sig g Hwf) as Hl.
  set (h := rw_replace g n owner (rw_canonical_node g node)).
  assert (Hlh : rw_layout sig h).
  { apply (rw_replace_layout sig g n owner node (rw_canonical_node g node) Hl Hnode).
    - apply rw_canonical_node_sort.
    - apply rw_canonical_node_valid; [exact Hl|].
      exact (rw_node_at_valid sig g n owner node Hl Hnode). }
  split; [apply rw_layout_wf; exact Hlh|]; split; apply rw_productions_extend.
  - intro c; reflexivity.
  - intros m c other Hother; unfold h; rewrite rw_replace_node_at.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + assert (Hsame : c = owner /\ other = node) by (split; congruence).
      destruct Hsame as [-> ->].
      exists (rw_canonical_node g node); split; [reflexivity|].
      intros t Ht; apply (proj2 (rw_canonical_node_represents sig h node t Hlh)); exact Ht.
    + exists other; split; [exact Hother|intros t Ht; exact Ht].
  - intro c; reflexivity.
  - intros m c other Hother; unfold h in Hother; rewrite rw_replace_node_at in Hother.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + injection Hother as Howner Hother; subst c other; exists node; split; [exact Hnode|].
      intros t Ht; exact (proj1 (rw_canonical_node_represents sig g node t Hl) Ht).
    + exists other; split; [exact Hother|intros t Ht; exact Ht].
Qed.

(** Canonicalizing one production updates every incidence table through the local update API. *)
Definition rw_canonicalize_one {K Sort V} (EK : encoding K) n
    (g : rw_graph K Sort V) ix : rw_graph K Sort V * rw_index K :=
  match rw_node_at g n with
  | Some (owner, node) =>
    let h := rw_replace g n owner (rw_canonical_node g node) in
    (h, rw_index_after_node_change EK g h ix n)
  | None => (g, ix)
  end.

Lemma rw_canonicalize_one_correct {K Sort V H C} (EK : encoding K)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) n g ix :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_clean g -> rw_index_agrees EK g ix ->
  let '(h, ix') := rw_canonicalize_one EK n g ix in
  rw_graph_wf sig h /\ rw_graph_sound sig admissible rules h /\ rw_productive h /\
  rw_clean h /\ rw_index_agrees EK h ix' /\ rw_extends g h.
Proof.
  intros Hwf Hsound Hproductive Hclean Hix; unfold rw_canonicalize_one.
  destruct (rw_node_at g n) as [[owner node]|] eqn:Hnode.
  - destruct (rw_replace_canonical_correct sig g n owner node Hwf Hnode)
      as [Hwf' [Hext Hback]].
    split; [exact Hwf'|]; split.
    + intros c t u Ht Hu; apply (Hsound c t u); apply Hback; assumption.
    + split.
      * intros c root Hfind; change (rw_find g c = Some root) in Hfind.
        destruct (Hproductive c root Hfind) as [t Ht]; exists t; apply Hext; exact Ht.
      * split.
        -- intros a b t Ha Hb; change (rw_find g a = rw_find g b).
           apply (Hclean a b t); apply Hback; assumption.
        -- split; [|exact Hext].
           apply (rw_index_after_node_change_agrees EK sig g _ ix n Hwf Hwf' Hix).
           ++ intro c; reflexivity.
           ++ intros m Hne; rewrite rw_replace_node_at; destruct (Pos.eq_dec m n); congruence.
  - exact (conj Hwf (conj Hsound (conj Hproductive (conj Hclean (conj Hix (rw_extends_refl g)))))).
Qed.

Fixpoint rw_canonicalize_all {K Sort V} (EK : encoding K) ids
    (g : rw_graph K Sort V) ix : rw_graph K Sort V * rw_index K :=
  match ids with
  | [] => (g, ix)
  | n :: ids =>
    let '(h, ix') := rw_canonicalize_one EK n g ix in rw_canonicalize_all EK ids h ix'
  end.

Lemma rw_canonicalize_all_correct {K Sort V H C} (EK : encoding K)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) ids :
  forall g ix, rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_clean g -> rw_index_agrees EK g ix ->
  let '(h, ix') := rw_canonicalize_all EK ids g ix in
  rw_graph_wf sig h /\ rw_graph_sound sig admissible rules h /\ rw_productive h /\
  rw_clean h /\ rw_index_agrees EK h ix' /\ rw_extends g h.
Proof.
  induction ids as [|n ids IHids]; intros g ix Hwf Hsound Hproductive Hclean Hix.
  - exact (conj Hwf (conj Hsound (conj Hproductive (conj Hclean (conj Hix (rw_extends_refl g)))))).
  - pose proof (rw_canonicalize_one_correct EK sig admissible rules n g ix
      Hwf Hsound Hproductive Hclean Hix) as Hone.
    cbn [rw_canonicalize_all]; destruct (rw_canonicalize_one EK n g ix) as [h ix'].
    destruct Hone as [Hwf' [Hsound' [Hproductive' [Hclean' [Hix' Hext]]]]].
    specialize (IHids h ix' Hwf' Hsound' Hproductive' Hclean' Hix').
    destruct (rw_canonicalize_all EK ids h ix') as [j ix''].
    destruct IHids as [Hwf'' [Hsound'' [Hproductive'' [Hclean'' [Hix'' Hext']]]]].
    split; [exact Hwf''|]; split; [exact Hsound''|]; split; [exact Hproductive''|].
    split; [exact Hclean''|]; split; [exact Hix''|]; eapply rw_extends_trans; eassumption.
Qed.

(** Rebuilding discharges indexed congruence obligations, then canonicalizes every child list. *)
Definition rw_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_graph K Sort V :=
  let EN := rw_node_encoding EK ES EV in
  let ix := rw_build_index EK g in
  let vars := rw_build_table positive_encoding g (rw_variable_keys EN) in
  let universe := rw_pair_universe EK EN g ix vars in
  let initial := RwRebuildState g ix (nodup rw_pair_dec universe) in
  let final := rw_repeat rw_rebuild_done (rw_rebuild_step EK ES EN g ix vars)
    (Pos.of_succ_nat (rw_rebuild_measure universe initial)) initial in
  fst (rw_canonicalize_all EK (rw_nodes_in (rw_state_graph final))
    (rw_state_graph final) (rw_state_index final)).

(** Productive sound graphs rebuild to clean sound extensions with the same finite witnesses. *)
Theorem rw_rebuild_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_graph_wf sig (rw_rebuild EK ES EV g) /\
  rw_graph_sound sig admissible rules (rw_rebuild EK ES EV g) /\
  rw_productive (rw_rebuild EK ES EV g) /\
  rw_clean (rw_rebuild EK ES EV g) /\ rw_extends g (rw_rebuild EK ES EV g).
Proof.
  intros Hwf Hsound Hproductive; unfold rw_rebuild.
  set (EN := rw_node_encoding EK ES EV).
  set (ix := rw_build_index EK g).
  set (vars := rw_build_table positive_encoding g (rw_variable_keys EN)).
  set (universe := rw_pair_universe EK EN g ix vars).
  set (initial := RwRebuildState g ix (nodup rw_pair_dec universe)).
  assert (Hix : rw_index_agrees EK g ix) by (apply (rw_build_index_agrees EK sig); exact Hwf).
  assert (Hvars : rw_table_incidence positive_encoding g (rw_variable_keys EN) vars).
  { apply (rw_build_table_correct positive_encoding sig); exact Hwf. }
  assert (Hinitial : rw_rebuild_invariant EK sig admissible rules g universe initial).
  { constructor; try assumption.
    - intro n; reflexivity.
    - apply NoDup_nodup.
    - intros pair Hin; apply nodup_In in Hin; exact Hin.
    - exact (rw_processed_initial EK EN sig g ix vars Hwf Hix Hvars).
    - apply rw_extends_refl. }
  destruct (rw_rebuild_run_correct EK ES EN sig admissible rules g ix vars initial
    Hwf Hix Hvars Hinitial) as [Hfinal Hpending].
  set (final := rw_repeat rw_rebuild_done (rw_rebuild_step EK ES EN g ix vars)
    (Pos.of_succ_nat (rw_rebuild_measure universe initial)) initial) in *.
  destruct Hfinal as [Hwf' Hsound' Hproductive' Hix' Hnodes Hnd Hsub Hprocessed Hext].
  rewrite Hpending in Hprocessed; pose proof (rw_processed_clean _ Hprocessed) as Hclean.
  pose proof (rw_canonicalize_all_correct EK sig admissible rules
    (rw_nodes_in (rw_state_graph final)) (rw_state_graph final) (rw_state_index final)
    Hwf' Hsound' Hproductive' Hclean Hix') as Hcanonical.
  destruct (rw_canonicalize_all EK (rw_nodes_in (rw_state_graph final))
    (rw_state_graph final) (rw_state_index final)) as [h ix'']; cbn [fst].
  destruct Hcanonical as [Hwf'' [Hsound'' [Hproductive'' [Hclean'' [Hix'' Hext']]]]].
  split; [exact Hwf''|]; split; [exact Hsound''|]; split; [exact Hproductive''|].
  split; [exact Hclean''|]; eapply rw_extends_trans; eassumption.
Qed.
