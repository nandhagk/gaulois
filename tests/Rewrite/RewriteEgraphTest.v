(** * E-graph interning and rebuild examples

    These examples exercise finite interning, sort rejection and alias-aware index maintenance.
    For example, a stale child alias still queues its parent after a second class merge.
    Builds on: RewriteEgraph, RewriteIndex and RewriteRebuild. *)

From Stdlib Require Import List Bool PArith PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild.
Import List.ListNotations.

Bind Scope positive_scope with rw_id.

Definition egraph_signature : rw_signature nat bool nat :=
  RwSignature _ _ _ (fun v => Some (Nat.leb 10 v))
    (fun _ sorts result => negb result && forallb negb sorts).

Definition egraph_add := rw_add nat_encoding bool_encoding nat_encoding.

Definition egraph_rebuild := rw_rebuild nat_encoding bool_encoding nat_encoding.

Definition egraph_term : rw_term nat bool nat := RWApp false 0 [RWVar false 0].

Definition egraph_interned := egraph_add rw_empty egraph_term.

Example same_node_interning :
  egraph_add (fst egraph_interned) egraph_term = egraph_interned.
Proof.
  vm_compute; reflexivity.
Qed.

Example cross_sort_union_rejected :
  let '(g, a) := egraph_add rw_empty (RWVar false 0) in
  let '(h, b) := egraph_add g (RWVar true 10) in
  rw_union bool_encoding h a b = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example unallocated_union_rejected : rw_union bool_encoding (fst egraph_interned) 1 2 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition egraph_congruence : bool :=
  let '(g0, a) := egraph_add rw_empty (RWVar false 0) in
  let '(g1, b) := egraph_add g0 (RWVar false 1) in
  let '(g2, pa) := egraph_add g1 (RWApp false 0 [RWVar false 0]) in
  let '(g3, pb) := egraph_add g2 (RWApp false 0 [RWVar false 1]) in
  match rw_union bool_encoding g3 a b with
  | Some merged =>
    let h := egraph_rebuild merged in
    match rw_find h pa, rw_find h pb with
    | Some ra, Some rb => Pos.eqb ra rb
    | _, _ => false
    end
  | None => false
  end.

Example congruence_after_child_union : egraph_congruence = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition egraph_alias_graph : rw_graph nat bool nat :=
  RwGraph [1; 2; 3; 4; 5]%positive [1; 2; 3; 10; 11]%positive
    (Map.of_list positive_encoding [(1, 1); (2, 2); (3, 3); (4, 4); (5, 5)]%positive)
    (Map.of_list positive_encoding
      [(1, false); (2, false); (3, false); (4, false); (5, false)]%positive)
    (Map.of_list positive_encoding
      [(1%positive, (1%positive, RWNVar false 0)); (2%positive, (2%positive, RWNVar false 1));
      (3%positive, (3%positive, RWNVar false 2));
      (10%positive, (4%positive, RWNApp false 0 [2]%positive));
      (11%positive, (5%positive, RWNApp false 0 [3]%positive))]).

Definition egraph_alias_union := rw_merge egraph_alias_graph 1 2.

Definition egraph_alias_index := rw_index_after_union egraph_alias_graph egraph_alias_union
  (rw_build_index nat_encoding egraph_alias_graph) 1 2.

Example stale_parent_remains_indexed :
  rw_node_at egraph_alias_union 10 = Some (4%positive, RWNApp false 0 [2]%positive) /\
  rw_parent_nodes egraph_alias_union egraph_alias_index 1 = [10]%positive.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition egraph_old_alias_union := rw_merge egraph_alias_union 1 3.

Definition egraph_old_alias_index := rw_index_after_union egraph_alias_union egraph_old_alias_union
  egraph_alias_index 1 3.

Example affected_parent_through_old_root_alias :
  existsb (Pos.eqb 10) (rw_parent_nodes egraph_old_alias_union egraph_old_alias_index 3) = true /\
  rw_find (egraph_rebuild egraph_old_alias_union) 4 =
    rw_find (egraph_rebuild egraph_old_alias_union) 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition egraph_repeated_graph : rw_graph nat bool nat :=
  RwGraph [1; 3]%positive [10]%positive
    (Map.of_list positive_encoding [(1, 1); (2, 1); (3, 3)]%positive)
    (Map.of_list positive_encoding [(1, false); (2, false); (3, false)]%positive)
    (Map.of_list positive_encoding
      [(10%positive, (3%positive, RWNApp false 0 [1; 1; 2]%positive))]).

Definition egraph_repeated_changed := rw_replace egraph_repeated_graph 10 3
  (RWNApp false 1 [1; 1; 1]%positive).

Definition egraph_repeated_index := rw_index_after_node_change nat_encoding egraph_repeated_graph
  egraph_repeated_changed (rw_build_index nat_encoding egraph_repeated_graph) 10.

Example repeated_children_and_root_aliases_deduplicate :
  rw_lookup_list positive_encoding 2%positive (rw_index_parents egraph_repeated_index) = [] /\
  rw_lookup_list positive_encoding 1%positive (rw_index_parents egraph_repeated_index) =
    [10]%positive /\
  rw_lookup_list positive_encoding 1%positive (rw_index_root_parents egraph_repeated_index) =
    [10]%positive /\
  rw_lookup_list nat_encoding 0 (rw_index_ops egraph_repeated_index) = [] /\
  rw_lookup_list nat_encoding 1 (rw_index_ops egraph_repeated_index) = [10]%positive.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition egraph_cycle :=
  let '(g, a) := egraph_add rw_empty (RWVar false 0) in
  let '(h, b) := egraph_add g egraph_term in
  match rw_union bool_encoding h a b with
  | Some merged => egraph_rebuild merged
  | None => h
  end.

(** Costs do not occur in graph structure; this cycle also admits the all-zero cost function. *)
Example zero_cost_cycle_has_finite_witness :
  rw_node_at egraph_cycle 3 = Some (3%positive, RWNApp false 0 [2]%positive) /\
  rw_find egraph_cycle 2 = rw_find egraph_cycle 3 /\
  rw_represents egraph_cycle 2 (RWVar false 0) /\ rw_represents egraph_cycle 2 egraph_term.
Proof.
  assert (Hvar : rw_represents egraph_cycle 2 (RWVar false 0)).
  { apply (rw_repr_var _ 2 2 2 2 false 0); vm_compute; reflexivity. }
  split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|]; split; [exact Hvar|].
  apply (rw_repr_app _ 2 3 3 2 false 0 [2]%positive [RWVar false 0]);
    try (vm_compute; reflexivity).
  constructor; [exact Hvar|constructor].
Qed.

(** * A nonproductive-cycle counterexample *)

Definition egraph_nonproductive : rw_graph nat bool nat :=
  RwGraph [1; 2]%positive [1; 2; 3]%positive
    (Map.set positive_encoding 2%positive 2%positive
      (Map.set positive_encoding 1%positive 1%positive Map.empty))
    (Map.set positive_encoding 2%positive false
      (Map.set positive_encoding 1%positive false Map.empty))
    (Map.set positive_encoding 3%positive (2%positive, RWNVar false 0)
      (Map.set positive_encoding 2%positive (2%positive, RWNApp false 0 [1]%positive)
        (Map.set positive_encoding 1%positive
          (1%positive, RWNApp false 0 [1]%positive) Map.empty))).

Lemma egraph_nonproductive_nodes n owner node :
  rw_node_at egraph_nonproductive n = Some (owner, node) ->
  (owner = 1%positive /\ node = RWNApp false 0 [1]%positive) \/
  (owner = 2%positive /\ node = RWNApp false 0 [1]%positive) \/
  (owner = 2%positive /\ node = RWNVar false 0).
Proof.
  intro Hnode.
  change (Map.get positive_encoding n
    (Map.set positive_encoding 3%positive (2%positive, RWNVar false 0)
      (Map.set positive_encoding 2%positive (2%positive, RWNApp false 0 [1]%positive)
        (Map.set positive_encoding 1%positive
          (1%positive, RWNApp false 0 [1]%positive) Map.empty))) =
      Some (owner, node)) in Hnode.
  destruct (Pos.eq_dec n 3) as [->|Hthree].
  - rewrite Map.get_set_same in Hnode; injection Hnode as <- <-; auto.
  - rewrite Map.get_set_other in Hnode by exact Hthree.
    destruct (Pos.eq_dec n 2) as [->|Htwo].
    + rewrite Map.get_set_same in Hnode; injection Hnode as <- <-; auto.
    + rewrite Map.get_set_other in Hnode by exact Htwo.
      destruct (Pos.eq_dec n 1) as [->|Hone].
      * rewrite Map.get_set_same in Hnode; injection Hnode as <- <-; auto.
      * rewrite Map.get_set_other in Hnode by exact Hone; rewrite Map.get_empty in Hnode;
          discriminate.
Qed.

Lemma egraph_nonproductive_find c :
  rw_find egraph_nonproductive c = Some 2%positive -> c = 2%positive.
Proof.
  intro Hfind.
  change (Map.get positive_encoding c
    (Map.set positive_encoding 2%positive 2%positive
      (Map.set positive_encoding 1%positive 1%positive Map.empty)) = Some 2%positive) in Hfind.
  destruct (Pos.eq_dec c 2) as [->|Htwo]; [reflexivity|].
  rewrite Map.get_set_other in Hfind by exact Htwo.
  destruct (Pos.eq_dec c 1) as [->|Hone]; [rewrite Map.get_set_same in Hfind; discriminate|].
  rewrite Map.get_set_other in Hfind by exact Hone; rewrite Map.get_empty in Hfind; discriminate.
Qed.

Lemma egraph_nonproductive_terms c t :
  rw_represents egraph_nonproductive c t -> c = 2%positive /\ t = RWVar false 0.
Proof.
  apply (rw_represents_ind_all egraph_nonproductive
    (fun c t => c = 2%positive /\ t = RWVar false 0)).
  - intros id n owner root s v Hnode Ho Hc.
    apply egraph_nonproductive_nodes in Hnode; destruct Hnode as [[Howner Hnode]|
      [[Howner Hnode]|[Howner Hnode]]]; try discriminate.
    injection Hnode as <- <-; subst owner; vm_compute in Ho; injection Ho as <-.
    split; [apply egraph_nonproductive_find; exact Hc|reflexivity].
  - intros id n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    apply egraph_nonproductive_nodes in Hnode; destruct Hnode as [[Howner Hnode]|
      [[Howner Hnode]|[Howner Hnode]]]; try discriminate;
      injection Hnode as Hsort Hop Hids; subst s op ids;
      inversion IHargs as [|id' t' ids' ts' [Hbad Hterm] Htail]; discriminate.
Qed.

Example nonproductive_cycle_rejects_productivity : ~ rw_productive egraph_nonproductive.
Proof.
  intro Hproductive; destruct (Hproductive 1%positive 1%positive eq_refl) as [t Ht].
  destruct (egraph_nonproductive_terms 1 t Ht) as [Hbad Hterm]; discriminate.
Qed.

Lemma egraph_nonproductive_find_other c : c <> 1%positive -> c <> 2%positive ->
  rw_find egraph_nonproductive c = None.
Proof.
  intros Hone Htwo; change (Map.get positive_encoding c
    (Map.set positive_encoding 2%positive 2%positive
      (Map.set positive_encoding 1%positive 1%positive Map.empty)) = None).
  rewrite !Map.get_set_other by assumption; apply Map.get_empty.
Qed.

Lemma egraph_nonproductive_sort_other c : c <> 1%positive -> c <> 2%positive ->
  rw_class_sort egraph_nonproductive c = None.
Proof.
  intros Hone Htwo; change (Map.get positive_encoding c
    (Map.set positive_encoding 2%positive false
      (Map.set positive_encoding 1%positive false Map.empty)) = None).
  rewrite !Map.get_set_other by assumption; apply Map.get_empty.
Qed.

Lemma egraph_nonproductive_node_other n :
  n <> 1%positive -> n <> 2%positive -> n <> 3%positive ->
  rw_node_at egraph_nonproductive n = None.
Proof.
  intros Hone Htwo Hthree; change (Map.get positive_encoding n
    (Map.set positive_encoding 3%positive (2%positive, RWNVar false 0)
      (Map.set positive_encoding 2%positive (2%positive, RWNApp false 0 [1]%positive)
        (Map.set positive_encoding 1%positive
          (1%positive, RWNApp false 0 [1]%positive) Map.empty))) = None).
  rewrite !Map.get_set_other by assumption; apply Map.get_empty.
Qed.

Example nonproductive_cycle_is_well_formed : rw_graph_wf egraph_signature egraph_nonproductive.
Proof.
  apply rw_layout_wf; constructor.
  - repeat constructor; cbn; intuition discriminate.
  - repeat constructor; cbn; intuition discriminate.
  - apply Map.wf_set; apply Map.wf_set; apply Map.wf_empty.
  - apply Map.wf_set; apply Map.wf_set; apply Map.wf_empty.
  - apply Map.wf_set; apply Map.wf_set; apply Map.wf_set; apply Map.wf_empty.
  - intros c root Hfind; destruct (Pos.eq_dec c 1) as [->|Hone].
    + vm_compute in Hfind; injection Hfind as Hroot; subst root.
      split; [cbn; auto|]; split; [reflexivity|exists false; split; reflexivity].
    + destruct (Pos.eq_dec c 2) as [->|Htwo].
      * vm_compute in Hfind; injection Hfind as Hroot; subst root.
        split; [cbn; auto|]; split; [reflexivity|exists false; split; reflexivity].
      * rewrite (egraph_nonproductive_find_other c Hone Htwo) in Hfind; discriminate.
  - intros root [Heq|[Heq|Hfalse]]; [subst root; reflexivity|subst root; reflexivity|contradiction].
  - intro c; destruct (Pos.eq_dec c 1) as [->|Hone].
    + split; intros Hexists; eexists; reflexivity.
    + destruct (Pos.eq_dec c 2) as [->|Htwo].
      * split; intros Hexists; eexists; reflexivity.
      * rewrite (egraph_nonproductive_find_other c Hone Htwo),
          (egraph_nonproductive_sort_other c Hone Htwo).
        split; intros [x Hx]; discriminate.
  - intro n; destruct (Pos.eq_dec n 1) as [->|Hone].
    + split; intro Hin; [eexists; eexists; reflexivity|cbn; auto].
    + destruct (Pos.eq_dec n 2) as [->|Htwo].
      * split; intro Hin; [eexists; eexists; reflexivity|cbn; auto].
      * destruct (Pos.eq_dec n 3) as [->|Hthree].
        -- split; intro Hin; [eexists; eexists; reflexivity|cbn; auto].
        -- rewrite (egraph_nonproductive_node_other n Hone Htwo Hthree).
           split; [cbn; intuition congruence|intros [owner [node Hnode]]; discriminate].
  - intros n c node Hnode; apply egraph_nonproductive_nodes in Hnode.
    destruct Hnode as [[-> ->]|[[-> ->]|[-> ->]]]; reflexivity.
  - intros n c s v Hnode; apply egraph_nonproductive_nodes in Hnode.
    destruct Hnode as [[Howner Hnode]|[[Howner Hnode]|[Howner Hnode]]]; try discriminate.
    injection Hnode as Hsort Hvar; subst s v; reflexivity.
  - intros n c s op ids Hnode; apply egraph_nonproductive_nodes in Hnode.
    destruct Hnode as [[Howner Hnode]|[[Howner Hnode]|[Howner Hnode]]]; try discriminate;
      injection Hnode as Hsort Hop Hids; subst s op ids; exists [false]; split;
      [constructor; [reflexivity|constructor]|reflexivity|
       constructor; [reflexivity|constructor]|reflexivity].
Qed.

Example nonproductive_cycle_initially_sound :
  rw_graph_sound egraph_signature (fun _ : rw_semantics nat bool nat nat => True)
    ([] : list (rw_rule nat bool nat unit)) egraph_nonproductive.
Proof.
  intros c t u Ht Hu; destruct (egraph_nonproductive_terms c t Ht) as [_ ->].
  destruct (egraph_nonproductive_terms c u Hu) as [_ ->]; apply rw_eq_refl.
Qed.

Definition egraph_counterexample_semantics : rw_semantics nat bool nat nat :=
  RwSemantics _ _ _ _ (fun v => Some v)
    (fun _ args => match args with [v] => Some (S v) | _ => None end).

Example nonproductive_cycle_rebuild_is_not_sound :
  ~ rw_graph_sound egraph_signature (fun _ : rw_semantics nat bool nat nat => True)
    ([] : list (rw_rule nat bool nat unit)) (egraph_rebuild egraph_nonproductive).
Proof.
  intro Hsound.
  assert (Hvar : rw_represents (egraph_rebuild egraph_nonproductive) 1 (RWVar false 0)).
  { apply (rw_repr_var _ 1 3 2 1 false 0); vm_compute; reflexivity. }
  assert (Happ : rw_represents (egraph_rebuild egraph_nonproductive) 1
      (RWApp false 0 [RWVar false 0])).
  { apply (rw_repr_app _ 1 1 1 1 false 0 [1]%positive [RWVar false 0]);
      try (vm_compute; reflexivity).
    constructor; [exact Hvar|constructor]. }
  pose proof (rw_equal_sound egraph_signature (fun _ : rw_semantics nat bool nat nat => True)
    ([] : list (rw_rule nat bool nat unit)) (Forall_nil _) _ _ (Hsound 1%positive _ _ Hvar Happ)
    egraph_counterexample_semantics I) as Hbad.
  vm_compute in Hbad; discriminate.
Qed.
