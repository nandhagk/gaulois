(** * Direct static local solving

    A finite indexed contributor graph selects a closed region before total iteration.
    For example, a side contribution into a root also selects its producer and that producer's
    declared reads and outputs.
    Builds on: GraphDfs, FixpointLocal and FixpointTotal. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointPartial
  FixpointWorklist FixpointTotal FixpointLocal.
Import List.ListNotations.

Module DirectClosure.

(** The finite support includes every indexed constraint, even in an untrusted raw index. *)
Definition indexed {X C} (EC : encoding C) (ix : sys_index X C) : list C :=
  distinct_unknowns EC (flat_map snd (Map.elements (contributors ix))).

(** Reaching a constraint requires its nominal output, side outputs and reads. *)
Definition outputs {X C A} (S : System.t X C A) (SS : System.static S) (c : C) : list X :=
  System.target S c :: side_targets SS c ++ deps SS c.

Definition adjacent {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (v : X + C) : list (X + C) :=
  distinct_unknowns (sum_encoding EX EC)
    (match v with
    | inl x => map (@inr X C) (contributors_of EX ix x)
    | inr c => map (@inl X C) (outputs S SS c)
    end).

(** The finite support bounds the search; the DFS itself reads only indexed adjacency. *)
Definition support {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) : list (X + C) :=
  let cs := indexed EC ix in
  distinct_unknowns (sum_encoding EX EC)
    (map (@inl X C) roots ++ map (@inr X C) cs ++
      flat_map (fun c => map (@inl X C) (outputs S SS c)) cs).

Definition graph {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  : Graph.t (X + C) ((X + C) * (X + C)) :=
  Graph.Make (map (@inl X C) roots) (support EX EC S SS ix roots)
    (fun v => map (pair v) (adjacent EX EC S SS ix v)) fst snd.

Lemma indexed_complete {X C} (EX : encoding X) (EC : encoding C) (ix : sys_index X C) x c :
  In c (contributors_of EX ix x) -> In c (indexed EC ix).
Proof.
  unfold contributors_of, index_get, Map.get, Map.code_get.
  destruct (Trie.get (encode EX x) (contributors ix)) as [[stored cs]|] eqn:Hget;
    cbn; intro Hin; [|contradiction].
  unfold indexed; apply distinct_unknowns_spec, in_flat_map.
  exists (stored, cs); split; [|exact Hin].
  unfold Map.elements; apply in_map_iff; exists (encode EX x, (stored, cs)).
  split; [reflexivity|apply Trie.elements_complete; exact Hget].
Qed.

Lemma support_constraint {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) roots c :
  In (inr c) (support EX EC S SS ix roots) <-> In c (indexed EC ix).
Proof.
  unfold support; rewrite distinct_unknowns_spec, !in_app_iff; split.
  - intros [Hroot|[Hc|Houtput]].
    + apply in_map_iff in Hroot; destruct Hroot as [x [Heq _]]; discriminate.
    + apply in_map_iff in Hc; destruct Hc as [d [Heq Hd]]; injection Heq as Heq.
      subst d; exact Hd.
    + apply in_flat_map in Houtput; destruct Houtput as [d [_ Houtput]].
      apply in_map_iff in Houtput; destruct Houtput as [x [Heq _]]; discriminate.
  - intro Hin; right; left; apply in_map; exact Hin.
Qed.

Lemma support_output {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) roots c x :
  In c (indexed EC ix) -> In x (outputs S SS c) ->
  In (inl x) (support EX EC S SS ix roots).
Proof.
  intros Hc Hx; unfold support; apply distinct_unknowns_spec.
  apply in_or_app; right; apply in_or_app; right.
  apply in_flat_map; exists c; split; [exact Hc|apply in_map; exact Hx].
Qed.

Lemma graph_well_formed {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots :
  graph_wf (graph EX EC S SS ix roots).
Proof.
  constructor; cbn [graph Graph.nodes Graph.entries Graph.out Graph.source Graph.target].
  - apply distinct_unknowns_nodup.
  - intros v Hin; unfold support; apply distinct_unknowns_spec, in_or_app; left; exact Hin.
  - intros v e Hin; apply in_map_iff in Hin; destruct Hin as [w [Heq _]]; subst e; reflexivity.
  - intros v e Hv He; apply in_map_iff in He; destruct He as [w [Heq Hw]]; subst e; cbn.
    unfold adjacent in Hw; apply distinct_unknowns_spec in Hw; destruct v as [x|c].
    + apply in_map_iff in Hw; destruct Hw as [c [Heq Hc]]; subst w.
      apply support_constraint; eapply indexed_complete; exact Hc.
    + apply in_map_iff in Hw; destruct Hw as [x [Heq Hx]]; subst w.
      apply support_constraint in Hv; eapply support_output; eauto.
Qed.

Lemma graph_edges_unique {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots v :
  NoDup (Graph.out (graph EX EC S SS ix roots) v).
Proof.
  cbn [graph Graph.out].
  pose proof (distinct_unknowns_nodup (sum_encoding EX EC)
    (match v with
    | inl x => map (@inr X C) (contributors_of EX ix x)
    | inr c => map (@inl X C) (outputs S SS c)
    end)) as Hnodup.
  change (NoDup (map (pair v) (adjacent EX EC S SS ix v))).
  fold (adjacent EX EC S SS ix v) in Hnodup.
  induction Hnodup as [|w ws Hfresh Hnodup IH]; cbn; constructor; [|exact IH].
  intro Hin; apply in_map_iff in Hin; destruct Hin as [u [Heq Hu]].
  inversion Heq; subst u; exact (Hfresh Hu).
Qed.

Definition search {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) :=
  let g := graph EX EC S SS ix roots in
  dfs (prepare (sum_encoding EX EC) g) FinSet.empty (Graph.entries g).

Definition unknown_projection {X C} (vs : list (X + C)) : list X :=
  flat_map (fun v =>
    match v with
    | inl x => [x]
    | inr _ => []
    end) vs.

Lemma unknown_projection_spec {X C} (vs : list (X + C)) x :
  In x (unknown_projection vs) <-> In (inl x) vs.
Proof.
  unfold unknown_projection; rewrite in_flat_map; split.
  - intros [[y|c] [Hin Hx]]; cbn in Hx; [|contradiction].
    destruct Hx as [Heq|Hfalse]; [subst y; exact Hin|contradiction].
  - intro Hin; exists (inl x); split; [exact Hin|left; reflexivity].
Qed.

Lemma search_spec {X C A} (EX : encoding X) (EC : encoding C) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) roots v :
  In v (preorder (search EX EC S SS ix roots)) <->
  reachable (graph EX EC S SS ix roots) v.
Proof.
  set (g := graph EX EC S SS ix roots).
  assert (Hready : ready (sum_encoding EX EC) g (prepare (sum_encoding EX EC) g)).
  { apply prepare_ready; [apply graph_well_formed|apply graph_edges_unique]. }
  destruct (dfs_exact (sum_encoding EX EC) g (prepare (sum_encoding EX EC) g) v
    (Graph.entries g) FinSet.empty Hready (entries_in (proj1 Hready)))
    as [_ [_ [_ Hpre]]].
  unfold search; fold g; rewrite Hpre; apply reachable_dfs; exact Hready.
Qed.

Lemma adjacent_unknown {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) x v :
  In v (adjacent EX EC S SS ix (inl x)) <->
  exists c, v = inr c /\ In c (contributors_of EX ix x).
Proof.
  unfold adjacent; rewrite distinct_unknowns_spec, in_map_iff.
  split; intros [c [Heq Hin]]; exists c; (split; [symmetry; exact Heq|exact Hin]).
Qed.

Lemma adjacent_constraint {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) c v :
  In v (adjacent EX EC S SS ix (inr c)) <->
  exists x, v = inl x /\ In x (outputs S SS c).
Proof.
  unfold adjacent; rewrite distinct_unknowns_spec, in_map_iff.
  split; intros [x [Heq Hin]]; exists x; (split; [symmetry; exact Heq|exact Hin]).
Qed.

Lemma reachable_edge {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots v w :
  reachable (graph EX EC S SS ix roots) v -> In w (adjacent EX EC S SS ix v) ->
  reachable (graph EX EC S SS ix roots) w.
Proof.
  intros Hv Hw; apply (@reachable_step _ _ (graph EX EC S SS ix roots) (v, w));
    [exact Hv|apply in_map; exact Hw].
Qed.

Lemma reachable_contributor {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots x c :
  reachable (graph EX EC S SS ix roots) (inl x) -> In c (contributors_of EX ix x) ->
  reachable (graph EX EC S SS ix roots) (inr c).
Proof.
  intros Hx Hc; eapply reachable_edge; [exact Hx|].
  apply adjacent_unknown; exists c; auto.
Qed.

Lemma reachable_output {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots c x :
  reachable (graph EX EC S SS ix roots) (inr c) -> In x (outputs S SS c) ->
  reachable (graph EX EC S SS ix roots) (inl x).
Proof.
  intros Hc Hx; eapply reachable_edge; [exact Hc|].
  apply adjacent_constraint; exists x; auto.
Qed.

Lemma reachable_least {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots (E : FinSet.t X) :
  (forall x, In x roots -> FinSet.mem EX x E = true) ->
  (forall x c, FinSet.mem EX x E = true -> In c (contributors_of EX ix x) ->
    forall y, In y (outputs S SS c) -> FinSet.mem EX y E = true) ->
  forall v, reachable (graph EX EC S SS ix roots) v ->
  match v with
  | inl x => FinSet.mem EX x E = true
  | inr c => forall y, In y (outputs S SS c) -> FinSet.mem EX y E = true
  end.
Proof.
  intros Hroots Hclosed v Hreach; induction Hreach as [v Hin|[v w] Hreach IH Hedge].
  - apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]]; subst v; apply Hroots; exact Hx.
  - cbn [graph Graph.source Graph.target Graph.out fst snd] in *.
    apply in_map_iff in Hedge; destruct Hedge as [u [Heq Hu]]; injection Heq as Heq.
    subst u; destruct v as [x|c].
    + apply adjacent_unknown in Hu; destruct Hu as [c [Heq Hc]]; subst w.
      exact (Hclosed x c IH Hc).
    + apply adjacent_constraint in Hu; destruct Hu as [x [Heq Hx]]; subst w.
      exact (IH x Hx).
Qed.

Lemma reachable_constraint_origin {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots c :
  reachable (graph EX EC S SS ix roots) (inr c) ->
  exists x, reachable (graph EX EC S SS ix roots) (inl x) /\
    In c (contributors_of EX ix x).
Proof.
  intro Hreach; remember (inr c) as v eqn:Hvertex.
  destruct Hreach as [v Hin|[v w] Hsource Hedge].
  - subst v; apply in_map_iff in Hin; destruct Hin as [x [Heq _]]; discriminate.
  - cbn [graph Graph.source Graph.target Graph.out fst snd] in *; subst w.
    apply in_map_iff in Hedge; destruct Hedge as [u [Heq Hu]]; injection Heq as Heq; subst u.
    destruct v as [x|d].
    + apply adjacent_unknown in Hu; destruct Hu as [d [Heq Hd]]; injection Heq as Heq.
      subst d; exists x; split; assumption.
    + apply adjacent_constraint in Hu; destruct Hu as [x [Heq _]]; discriminate.
Qed.

End DirectClosure.
Import DirectClosure.

(** The closure consists of the unknown vertices discovered by the indexed bipartite search. *)
Definition local_direct_closure {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) : FinSet.t X :=
  FinSet.of_list EX (unknown_projection (preorder (search EX EC S SS ix roots))).

Lemma local_direct_closure_spec {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots x :
  FinSet.mem EX x (local_direct_closure EX EC S SS ix roots) = true <->
  reachable (graph EX EC S SS ix roots) (inl x).
Proof.
  unfold local_direct_closure; rewrite FinSet.of_list_spec, unknown_projection_spec.
  apply search_spec.
Qed.

(** The internally constructed closure is well formed for every supplied index. *)
Theorem local_direct_closure_wf {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  FinSet.wf EX (local_direct_closure EX EC S SS ix roots).
Proof.
  apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

(** Every requested root is explored, including roots absent from the system. *)
Theorem local_direct_closure_roots {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  forall x, In x roots -> FinSet.mem EX x (local_direct_closure EX EC S SS ix roots) = true.
Proof.
  intros x Hx; apply local_direct_closure_spec, reachable_entry, in_map; exact Hx.
Qed.

(** Every region containing the roots and closed under contributor edges contains the closure. *)
Theorem local_direct_closure_least {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (E : FinSet.t X) :
  FinSet.wf EX E -> (forall x, In x roots -> FinSet.mem EX x E = true) ->
  (forall x c, FinSet.mem EX x E = true -> In c (contributors_of EX ix x) ->
    FinSet.mem EX (System.target S c) E = true /\
    (forall y, In y (side_targets SS c) -> FinSet.mem EX y E = true) /\
    (forall y, In y (deps SS c) -> FinSet.mem EX y E = true)) ->
  FinSet.subset EX (local_direct_closure EX EC S SS ix roots) E = true.
Proof.
  intros Hwf Hroots Hclosed; apply FinSet.subset_spec; [apply local_direct_closure_wf|].
  intros x Hx; apply local_direct_closure_spec in Hx.
  apply (reachable_least EX EC S SS ix roots E Hroots) with (v := inl x); [|exact Hx].
  intros y c Hy Hc z Hz; destruct (Hclosed y c Hy Hc) as [Ht [Hs Hd]].
  unfold outputs in Hz; cbn in Hz; destruct Hz as [Heq|Hz].
  - subst z; exact Ht.
  - apply in_app_iff in Hz as [Hz|Hz]; [apply Hs|apply Hd]; exact Hz.
Qed.

Lemma local_direct_contributor_outputs {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots x c :
  FinSet.mem EX x (local_direct_closure EX EC S SS ix roots) = true ->
  In c (contributors_of EX ix x) ->
  forall y, In y (outputs S SS c) ->
    FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true.
Proof.
  intros Hx Hc y Hy; apply local_direct_closure_spec.
  eapply reachable_output; [|exact Hy].
  eapply reachable_contributor; [apply local_direct_closure_spec; exact Hx|exact Hc].
Qed.

(** Every touched constraint has all of its outputs and declared reads inside the closure. *)
Theorem local_direct_closure_complete {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  sys_index_laws EX S SS ix ->
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
     exists y, In y (side_targets SS c) /\
       FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true) ->
    FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true /\
    (forall y, In y (side_targets SS c) ->
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true) /\
    (forall y, In y (deps SS c) ->
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true).
Proof.
  intros Hindex c Hc Htouch.
  assert (Hindexed : exists x, FinSet.mem EX x
    (local_direct_closure EX EC S SS ix roots) = true /\ In c (contributors_of EX ix x)).
  { destruct Htouch as [Ht|[x [Hs Hx]]].
    - exists (System.target S c); split; [exact Ht|].
      apply (contributors_agree Hindex); auto.
    - exists x; split; [exact Hx|]; apply (contributors_agree Hindex); auto. }
  destruct Hindexed as [x [Hx Hcx]].
  pose proof (local_direct_contributor_outputs EX EC S SS ix roots x c Hx Hcx) as Hout.
  split; [apply Hout; left; reflexivity|]; split; intros y Hy; apply Hout; right.
  - apply in_or_app; left; exact Hy.
  - apply in_or_app; right; exact Hy.
Qed.

(** Restriction keeps touched constraints in their original list order, including duplicates. *)
Definition local_direct_restrict {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (E : FinSet.t X) : System.t X C A :=
  System.Make (filter (fun c => FinSet.mem EX (System.target S c) E ||
    existsb (fun y => FinSet.mem EX y E) (side_targets SS c)) (System.constraints S))
    (System.target S) (System.rhs S).

(** The local system keeps precisely the constraints activated by its finite closure. *)
Definition local_direct_system {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  : System.t X C A :=
  local_direct_restrict EX S SS (local_direct_closure EX EC S SS ix roots).

(** The restricted system uses the original declarations and their original proofs. *)
Definition local_direct_static {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  System.static (local_direct_system EX EC S SS ix roots) :=
  @System.Static X C A (local_direct_system EX EC S SS ix roots)
    (deps SS) (side_targets SS) (System.reads_within SS) (System.sides_within SS).

(** Restriction preserves exactly the original constraints touching the closure. *)
Theorem local_direct_system_constraints {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) (c : C) :
  sys_index_laws EX S SS ix ->
  (In c (System.constraints (local_direct_system EX EC S SS ix roots)) <->
   In c (System.constraints S) /\
   (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
    exists y, In y (side_targets SS c) /\
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true)).
Proof.
  intro Hindex; unfold local_direct_system, local_direct_restrict; cbn [System.constraints].
  rewrite filter_In, orb_true_iff, existsb_exists; reflexivity.
Qed.

(** With an agreeing index, the retained constraints are exactly the discovered vertices. *)
Lemma local_direct_system_reached {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots c :
  sys_index_laws EX S SS ix ->
  (In c (System.constraints (local_direct_system EX EC S SS ix roots)) <->
    In (inr c) (preorder (search EX EC S SS ix roots))).
Proof.
  intro Hindex; rewrite local_direct_system_constraints by exact Hindex.
  rewrite search_spec; split.
  - intros [Hc [Htarget|[x [Hside Hx]]]].
    + eapply reachable_contributor; [apply local_direct_closure_spec; exact Htarget|].
      apply (contributors_agree Hindex); auto.
    + eapply reachable_contributor; [apply local_direct_closure_spec; exact Hx|].
      apply (contributors_agree Hindex); auto.
  - intro Hreach; apply reachable_constraint_origin in Hreach as [x [Hx Hc]].
    apply (contributors_agree Hindex) in Hc as [Hc [Htarget|Hside]]; split; [exact Hc| |exact Hc|].
    + left; rewrite Htarget; apply local_direct_closure_spec; exact Hx.
    + right; exists x; split; [exact Hside|apply local_direct_closure_spec; exact Hx].
Qed.

(** Projection explicitly stores every requested member, including bottom-valued members. *)
Definition local_direct_project {X A} (EX : encoding X) (xs : list X) (s : X -> A)
  : assignment X A :=
  fold_right (fun x m => Map.set EX x (s x) m) Map.empty xs.

Lemma local_direct_project_agrees {X A} (EX : encoding X) (L : lattice A)
  (xs : list X) (s : X -> A) x :
  In x xs -> lookup EX L (local_direct_project EX xs s) x = s x.
Proof.
  induction xs as [|y xs IH]; cbn [local_direct_project fold_right]; intro Hin;
    [contradiction|].
  unfold lookup at 1; destruct (dfs_eq_dec EX x y) as [Heq|Hne].
  - subst y; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; fold (lookup EX L (local_direct_project EX xs s) x).
    apply IH; destruct Hin as [Heq|Hin]; [congruence|exact Hin].
Qed.

Lemma local_direct_project_absent {X A} (EX : encoding X) (xs : list X) (s : X -> A) x :
  ~ In x xs -> Map.get EX x (local_direct_project EX xs s) = None.
Proof.
  induction xs as [|y xs IH]; cbn [local_direct_project fold_right]; intro Hnot.
  - apply Map.get_empty.
  - rewrite Map.get_set_other; [apply IH; intro Hin; apply Hnot; right; exact Hin|].
    intro Heq; apply Hnot; left; symmetry; exact Heq.
Qed.

(** Solve the restricted system directly and retain the finite closure's values. *)
Definition local_direct {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) : local_result X A :=
  let E := local_direct_closure EX EC S SS ix roots in
  let restricted := local_direct_restrict EX S SS E in
  let declarations : System.static restricted :=
    @System.Static X C A restricted
      (deps SS) (side_targets SS) (System.reads_within SS) (System.sides_within SS) in
  let s := proj1_sig (solve_total EX EC L HL sch st restricted declarations HT) in
  LocalResult E (local_direct_project EX (FinSet.elements E) s).

(** Direct local solving always covers its requested roots. *)
Theorem local_direct_roots {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  forall x, In x roots ->
    FinSet.mem EX x (explored (local_direct EX EC L HL sch st S SS ix roots HT)) = true.
Proof.
  apply local_direct_closure_roots.
Qed.

(** Activated queries observe the same reads, result and contributions after finite projection. *)
Lemma local_direct_query_projection {X C A} (EX : encoding X) (EC : encoding C)
  (L : lattice A) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) roots
  (s : X -> A) c :
  sys_index_laws EX S SS ix -> In c (System.constraints S) ->
  (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
    exists y, In y (side_targets SS c) /\
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true) ->
  let t := lookup EX L (local_direct_project EX
    (FinSet.elements (local_direct_closure EX EC S SS ix roots)) s) in
  Query.eval (System.rhs S c) s = Query.eval (System.rhs S c) t /\
  Query.reads (System.rhs S c) s = Query.reads (System.rhs S c) t /\
  Query.sides (System.rhs S c) s = Query.sides (System.rhs S c) t.
Proof.
  intros Hindex Hc Htouch t; apply query_determined; intros x Hread; symmetry.
  apply local_direct_project_agrees, (FinSet.elements_spec EX);
    [apply local_direct_closure_wf|].
  destruct (local_direct_closure_complete EX EC S SS ix roots Hindex c Hc Htouch)
    as [_ [_ Hdeps]].
  apply Hdeps; eapply System.reads_within; exact Hread.
Qed.

(** The restricted post-solution transfers directly to a closed partial solution of the original. *)
Theorem local_direct_closed {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  sys_index_laws EX S SS ix ->
  let r := local_direct EX EC L HL sch st S SS ix roots HT in
  closed_partial EX L S SS (explored r) (lookup EX L (values r)).
Proof.
  intro Hindex.
  set (E := local_direct_closure EX EC S SS ix roots).
  set (result := solve_total EX EC L HL sch st (local_direct_system EX EC S SS ix roots)
    (local_direct_static EX EC S SS ix roots) HT).
  set (s := proj1_sig result).
  set (t := lookup EX L (local_direct_project EX (FinSet.elements E) s)).
  change (closed_partial EX L S SS E t).
  assert (Hagrees : forall x, FinSet.mem EX x E = true -> t x = s x).
  { intros x Hx; apply local_direct_project_agrees, (FinSet.elements_spec EX);
      [apply local_direct_closure_wf|exact Hx]. }
  intros c Hc Htouch.
  destruct (local_direct_closure_complete EX EC S SS ix roots Hindex c Hc Htouch)
    as [Htarget [Hsides Hdeps]].
  destruct (local_direct_query_projection EX EC L S SS ix roots s c Hindex Hc Htouch)
    as [Heval [_ Hside]].
  change (Query.eval (System.rhs S c) s = Query.eval (System.rhs S c) t) in Heval.
  change (Query.sides (System.rhs S c) s = Query.sides (System.rhs S c) t) in Hside.
  assert (Hselected : In c (System.constraints (local_direct_system EX EC S SS ix roots))).
  { apply local_direct_system_constraints; [exact Hindex|split; assumption]. }
  destruct (proj2_sig result c Hselected) as [Hvalue Hcontributions].
  change (leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true) in Hvalue.
  change (forall y a, In (y, a) (Query.sides (System.rhs S c) s) -> leb L a (s y) = true)
    in Hcontributions.
  split.
  - intros y Hy; apply Hdeps; eapply System.reads_within; exact Hy.
  - split.
    + intro Hinside; rewrite (Hagrees _ Hinside), <- Heval; exact Hvalue.
    + intros y a Hy Hinside; rewrite (Hagrees _ Hinside).
      apply Hcontributions; rewrite Hside; exact Hy.
Qed.
