(** * Sparse finite memory sources

    A joining constraint system propagates terminal sources through prepared backward edges.
    For example, a cyclic phi with one incoming store retains that store as a source.
    Builds on: AnalysesMemoryWalk, AnalysesMemorySealed, OrderPowerset and FixpointTotal. *)

From Stdlib Require Import List Bool PArith Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderMonotone.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointWorklist
  FixpointTotal FixpointSchedule.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemorySealed
  AnalysesMemoryWalk AnalysesLiveness.
Import List.ListNotations.

(** Version codes preserve the structural namespaces used by both constructors. *)
Definition memory_version_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (memory_version N E) := memory_frontier_version_encoding EN EE.

(** Facts contain only versions in the supplied finite inventory. *)
Definition memory_flow_facts {N E} (EN : encoding N) (EE : encoding E)
    (mg : memory_graph N E) : Type :=
  finite_set (memory_version_encoding EN EE) (memory_versions mg).

(** Inclusion orders source facts and union joins them. *)
Definition memory_flow_lattice {N E} (EN : encoding N) (EE : encoding E)
    (mg : memory_graph N E) : lattice (memory_flow_facts EN EE mg) :=
  finite_powerset_lattice (memory_version_encoding EN EE) (memory_versions mg).

(** A source is the endpoint of a finite backward walk ending at a terminal. *)
Inductive memory_flow_reaches {N E T} (ET : encoding T) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> memory_version N E -> Prop :=
  | memory_flow_terminal : forall v, memory_walk_terminal ET effects mg q v ->
      memory_flow_reaches ET effects mg q v v
  | memory_flow_step : forall v w source, memory_walk_next ET effects mg q v w ->
      memory_flow_reaches ET effects mg q w source -> memory_flow_reaches ET effects mg q v source.

(** * Prepared sources and queries *)

(** Singleton construction shares the prepared universe and never scans it in an RHS. *)
Definition memory_flow_singleton {K} (EK : encoding K) (U : list K)
    (universe : finite_set EK U) (k : K) : finite_set EK U.
Proof.
  refine (exist _ (FinSet.inter EK (FinSet.of_list EK [k]) (proj1_sig universe)) _).
  abstract (split;
    [apply FinSet.wf_inter; [apply FinSet.wf_fold_add; apply Map.wf_empty|
      exact (proj1 (proj2_sig universe))]|
      intros source Hmem; apply FinSet.mem_inter in Hmem;
      exact (proj2 (proj2_sig universe) source (proj2 Hmem))]).
Defined.

Lemma memory_flow_singleton_mem {K} (EK : encoding K) U universe k source :
  fmem EK source (memory_flow_singleton EK U universe k) = true <->
    source = k /\ fmem EK source universe = true.
Proof.
  unfold fmem, memory_flow_singleton; cbn [proj1_sig].
  rewrite FinSet.mem_inter, FinSet.of_list_spec; cbn; intuition congruence.
Qed.

(** Each successor list is deduplicated once after occurrence and operand preparation. *)
Definition memory_flow_successors {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) : memory_version N E -> list (memory_version N E) :=
  let EV := memory_version_encoding EN EE in
  let next := memory_walk_successors EN EE ET g effects mg q in
  let rows := memory_result_index EV (fun v => memory_distinct EV (next v))
    (memory_distinct EV (memory_versions mg)) in
  index_edges EV rows.

Lemma memory_flow_successors_correct {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q v w :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (In w (memory_flow_successors EN EE ET g effects mg q v) <->
    memory_walk_next ET effects mg q v w).
Proof.
  intros Hwf Hvalid; unfold memory_flow_successors, index_edges.
  rewrite memory_result_index_at by
    (apply memory_distinct_in, (memory_versions_exact Hwf); exact Hvalid).
  rewrite memory_distinct_in; apply memory_walk_successors_correct; assumption.
Qed.

Lemma memory_flow_successors_terminal {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q v :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (memory_flow_successors EN EE ET g effects mg q v = [] <->
    memory_walk_terminal ET effects mg q v).
Proof.
  intros Hwf Hvalid; split.
  - intros Hnil w Hstep.
    apply (memory_flow_successors_correct EN EE ET g effects mg q v w Hwf Hvalid) in Hstep.
    rewrite Hnil in Hstep; contradiction.
  - intros Hterminal; destruct (memory_flow_successors EN EE ET g effects mg q v)
      as [|w ws] eqn:Hnext; [reflexivity|].
    exfalso; apply (Hterminal w).
    apply (memory_flow_successors_correct EN EE ET g effects mg q v w Hwf Hvalid).
    rewrite Hnext; left; reflexivity.
Qed.

(** A union query asks its finite dependency list once and has no side contributions. *)
Definition memory_flow_union_query {X A} (L : lattice A) (xs : list X) : Query.t X A :=
  ask_all xs (fun values => Query.Ret (fold_right (join L) (bot L) values)).

Lemma memory_flow_union_observations {X A} (L : lattice A) (xs : list X) s :
  Query.reads (memory_flow_union_query L xs) s = xs /\
  Query.eval (memory_flow_union_query L xs) s = fold_right (join L) (bot L) (map s xs) /\
  Query.sides (memory_flow_union_query L xs) s = [].
Proof.
  unfold memory_flow_union_query.
  destruct (ask_all_spec s xs (fun values => Query.Ret
    (fold_right (join L) (bot L) values))) as [Hr [Hv Hs]].
  cbn in Hr, Hv, Hs; rewrite app_nil_r in Hr; auto.
Qed.

(** The same prepared next list fixes both the RHS and its exact read dependencies. *)
Definition memory_flow_rhs {X A} (L : lattice A) (next : X -> list X) (seed : X -> A)
    (v : X) : Query.t X A :=
  match next v with
  | [] => Query.Ret (seed v)
  | xs => memory_flow_union_query L xs
  end.

Lemma memory_flow_rhs_reads {X A} (L : lattice A) next seed (v : X) s :
  Query.reads (memory_flow_rhs L next seed v) s = next v.
Proof.
  unfold memory_flow_rhs; destruct (next v); [reflexivity|].
  apply (proj1 (memory_flow_union_observations L _ s)).
Qed.

Lemma memory_flow_rhs_sides {X A} (L : lattice A) next seed (v : X) s :
  Query.sides (memory_flow_rhs L next seed v) s = [].
Proof.
  unfold memory_flow_rhs; destruct (next v); [reflexivity|].
  apply (proj2 (proj2 (memory_flow_union_observations L _ s))).
Qed.

(** The prepared full universe is shared by all terminal singleton seeds. *)
Definition memory_flow_seed {N E} (EN : encoding N) (EE : encoding E)
    (mg : memory_graph N E) : memory_version N E -> memory_flow_facts EN EE mg :=
  let EV := memory_version_encoding EN EE in
  let all := top_value (finite_powerset_top EV (memory_versions mg)) in
  let seeds := memory_result_index EV (memory_flow_singleton EV (memory_versions mg) all)
    (memory_distinct EV (memory_versions mg)) in
  fun v => match Map.get EV v seeds with
  | Some fact => fact
  | None => bot (memory_flow_lattice EN EE mg)
  end.

Lemma memory_flow_seed_mem {N E} EN EE (mg : memory_graph N E) v source :
  In v (memory_versions mg) ->
  (fmem (memory_version_encoding EN EE) source (memory_flow_seed EN EE mg v) = true <->
    source = v).
Proof.
  intro Hin; unfold memory_flow_seed.
  rewrite memory_result_index_at by (apply memory_distinct_in; exact Hin).
  rewrite memory_flow_singleton_mem; split; [tauto|intro Heq; split; [exact Heq|]].
  subst source; apply FinSet.of_list_spec; exact Hin.
Qed.

(** One constraint per distinct supplied version propagates sources from its backward operands. *)
Definition memory_flow_system {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) :
    System.t (memory_version N E) (memory_version N E) (memory_flow_facts EN EE mg) :=
  let next := memory_flow_successors EN EE ET g effects mg q in
  let seed := memory_flow_seed EN EE mg in
  System.Make (memory_distinct (memory_version_encoding EN EE) (memory_versions mg))
    (fun v => v) (memory_flow_rhs (memory_flow_lattice EN EE mg) next seed).

(** A static wrapper reuses the same prepared successor and seed functions as its system. *)
Definition memory_flow_static_for {X A} (L : lattice A) (keys : list X)
    (next : X -> list X) (seed : X -> A) :
    System.static (System.Make keys (fun v => v) (memory_flow_rhs L next seed)).
Proof.
  refine (System.Static next (fun _ => []) _ _).
  - intros v s; cbn [System.rhs]; rewrite memory_flow_rhs_reads; apply incl_refl.
  - intros v s; cbn [System.rhs]; rewrite memory_flow_rhs_sides; apply incl_refl.
Defined.

(** Static reads are exact, and this source system never contributes side values. *)
Definition memory_flow_static {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) : System.static (memory_flow_system EN EE ET g effects mg q) :=
  memory_flow_static_for (memory_flow_lattice EN EE mg)
    (memory_distinct (memory_version_encoding EN EE) (memory_versions mg))
    (memory_flow_successors EN EE ET g effects mg q) (memory_flow_seed EN EE mg).

(** Every prepared successor appears once, including on malformed finite inventories. *)
Lemma memory_flow_successors_nodup {N E T} EN EE (ET : encoding T) (g : Graph.t N E)
    effects mg q v :
  NoDup (memory_flow_successors EN EE ET g effects mg q v).
Proof.
  unfold memory_flow_successors, index_edges; rewrite memory_result_index_get.
  destruct (existsb _ _); [apply memory_distinct_nodup|constructor].
Qed.

(** The declared read lists equal actual reads, have no duplicates, and have no side targets. *)
Theorem memory_flow_dependencies_exact {N E T} EN EE (ET : encoding T) (g : Graph.t N E)
    effects mg q :
  NoDup (System.constraints (memory_flow_system EN EE ET g effects mg q)) /\
  forall v s,
    Query.reads (System.rhs (memory_flow_system EN EE ET g effects mg q) v) s =
      deps (memory_flow_static EN EE ET g effects mg q) v /\
    Query.sides (System.rhs (memory_flow_system EN EE ET g effects mg q) v) s = [] /\
    NoDup (deps (memory_flow_static EN EE ET g effects mg q) v).
Proof.
  split; [apply memory_distinct_nodup|intros v s].
  split; [apply memory_flow_rhs_reads|split; [apply memory_flow_rhs_sides|]].
  apply memory_flow_successors_nodup.
Qed.

(** * Finite-set membership and monotonicity *)

Lemma memory_flow_le {K} (EK : encoding K) U (a b : finite_set EK U) :
  leb (finite_powerset_lattice EK U) a b = true <->
    forall source, fmem EK source a = true -> fmem EK source b = true.
Proof.
  apply FinSet.subset_spec; exact (proj1 (proj2_sig a)).
Qed.

Lemma memory_flow_join_mem {K} (EK : encoding K) U (a b : finite_set EK U) source :
  fmem EK source (join (finite_powerset_lattice EK U) a b) = true <->
  fmem EK source a = true \/ fmem EK source b = true.
Proof.
  apply FinSet.mem_union.
Qed.

Lemma memory_flow_fold_mem {K} (EK : encoding K) U values source :
  fmem EK source (fold_right (join (finite_powerset_lattice EK U))
    (bot (finite_powerset_lattice EK U)) values) = true <->
  exists value, In value values /\ fmem EK source value = true.
Proof.
  induction values as [|value values IH]; cbn [fold_right].
  - change (FinSet.mem EK source FinSet.empty = true <->
      exists value : finite_set EK U, In value [] /\ fmem EK source value = true).
    rewrite FinSet.mem_empty; split; [discriminate|intros [? [[] _]]].
  - rewrite memory_flow_join_mem, IH; split.
    + intros [Hmem|[a [Hin Hmem]]]; [exists value|exists a]; cbn; auto.
    + intros [a [[Heq|Hin] Hmem]]; [subst a; now left|right; eauto].
Qed.

Lemma memory_flow_union_mem {X K} (EK : encoding K) U xs
    (s : X -> finite_set EK U) source :
  fmem EK source (Query.eval (memory_flow_union_query (finite_powerset_lattice EK U) xs) s)
    = true <-> exists v, In v xs /\ fmem EK source (s v) = true.
Proof.
  rewrite (proj1 (proj2 (memory_flow_union_observations _ xs s))), memory_flow_fold_mem.
  split.
  - intros [value [Hin Hmem]]; apply in_map_iff in Hin as [v [<- Hin]]; eauto.
  - intros [v [Hin Hmem]]; exists (s v); split; [apply in_map; exact Hin|exact Hmem].
Qed.

(** The RHS is monotone because singleton seeds are constant and all other operations are unions. *)
Theorem memory_flow_monotone {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q :
  monotone_system (memory_flow_lattice EN EE mg) (memory_flow_system EN EE ET g effects mg q).
Proof.
  intros v Hin; split.
  - intros s t Hle; cbn [memory_flow_system System.rhs]; unfold memory_flow_rhs.
    destruct (memory_flow_successors EN EE ET g effects mg q v) as [|w ws] eqn:Hnext.
    + apply (leb_refl (finite_powerset_laws _ _)).
    + apply memory_flow_le; intros source Hmem; apply memory_flow_union_mem in Hmem.
      destruct Hmem as [u [Hu Hmem]]; apply memory_flow_union_mem.
      exists u; split; [exact Hu|].
      exact (proj1 (memory_flow_le _ _ (s u) (t u)) (Hle u) source Hmem).
  - intros s t Hle x a Hside; cbn [memory_flow_system System.rhs] in Hside.
    rewrite memory_flow_rhs_sides in Hside; contradiction.
Qed.

(** Finite source cardinality supplies joining termination, including cyclic phi dependencies. *)
Definition memory_flow_termination {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q (Hwf : memory_graph_wf g effects mg) :
  terminates (memory_flow_lattice EN EE mg) (memory_flow_static EN EE ET g effects mg q)
    (rpo_scheduler (memory_version_encoding EN EE) (memory_flow_system EN EE ET g effects mg q)
      (memory_flow_static EN EE ET g effects mg q)) Joining :=
  inhabits (base_height (finite_powerset_height (memory_version_encoding EN EE)
    (memory_versions mg) (memory_versions_nodup Hwf))).

(** The public result is the actual function returned by the existing total joining engine. *)
Definition memory_flow_solve {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
    { s : memory_version N E -> memory_flow_facts EN EE mg |
      post_solution (memory_flow_lattice EN EE mg)
        (memory_flow_system EN EE ET g effects mg q) s } :=
  let EV := memory_version_encoding EN EE in
  let L := memory_flow_lattice EN EE mg in
  let keys := memory_distinct EV (memory_versions mg) in
  let next := memory_flow_successors EN EE ET g effects mg q in
  let seed := memory_flow_seed EN EE mg in
  let sys := System.Make keys (fun v => v) (memory_flow_rhs L next seed) in
  let ss := memory_flow_static_for L keys next seed in
  let sch := rpo_scheduler EV sys ss in
  solve_total EV EV L (finite_powerset_laws _ _) sch Joining sys ss
    (memory_flow_termination EN EE ET g effects mg q Hwf).

(** Monotonicity, least upper bounds and finite height make the joining solution least. *)
Theorem memory_flow_least {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  least_solution (memory_flow_lattice EN EE mg) (memory_flow_system EN EE ET g effects mg q)
    (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf)).
Proof.
  apply solve_total_least; [apply finite_powerset_lub|apply memory_flow_monotone].
Qed.

(** * Source interpretation and finite walks *)

Section MemoryFlowCorrect.
Context {N E T : Type} (EN : encoding N) (EE : encoding E) (ET : encoding T)
  (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
  (q : memory_scope T) (Hwf : memory_graph_wf g effects mg).

Local Abbreviation EV := (memory_version_encoding EN EE).
Local Abbreviation L := (memory_flow_lattice EN EE mg).
Local Abbreviation S := (memory_flow_system EN EE ET g effects mg q).
Local Abbreviation next := (memory_flow_successors EN EE ET g effects mg q).

(** Membership in an RHS is exactly a terminal seed or membership from one backward successor. *)
Lemma memory_flow_rhs_mem v source s :
  memory_valid_version g effects mg v ->
  (fmem EV source (Query.eval (System.rhs S v) s) = true <->
    (memory_walk_terminal ET effects mg q v /\ source = v) \/
    exists w, memory_walk_next ET effects mg q v w /\ fmem EV source (s w) = true).
Proof.
  intro Hvalid; cbn [memory_flow_system System.rhs]; unfold memory_flow_rhs.
  destruct (next v) as [|w ws] eqn:Hnext.
  - cbn [Query.eval]; rewrite memory_flow_seed_mem by
      (apply (memory_versions_exact Hwf); exact Hvalid).
    assert (Hterminal : memory_walk_terminal ET effects mg q v).
    { apply (memory_flow_successors_terminal EN EE ET g effects mg q v Hwf Hvalid); exact Hnext. }
    split; [intro Heq; left; auto|].
    intros [[_ Heq]|[u [Hstep Hmem]]]; [exact Heq|exfalso; apply (Hterminal u); exact Hstep].
  - rewrite memory_flow_union_mem; split.
    + intros [u [Hin Hmem]]; right; exists u; split; [|exact Hmem].
      apply (memory_flow_successors_correct EN EE ET g effects mg q v u Hwf Hvalid).
      rewrite Hnext; exact Hin.
    + intros [[Hterminal Heq]|[u [Hstep Hmem]]].
      * exfalso; apply (Hterminal w).
        apply (memory_flow_successors_correct EN EE ET g effects mg q v w Hwf Hvalid).
        rewrite Hnext; left; reflexivity.
      * exists u; split; [|exact Hmem].
        apply (memory_flow_successors_correct EN EE ET g effects mg q v u Hwf Hvalid) in Hstep.
        rewrite Hnext in Hstep; exact Hstep.
Qed.

(** The finite-walk interpretation is a post-solution whenever represented by facts. *)
Lemma memory_flow_interpretation_post s :
  (forall v source, memory_valid_version g effects mg v ->
    (fmem EV source (s v) = true <-> memory_flow_reaches ET effects mg q v source)) ->
  post_solution L S s.
Proof.
  intros Hmeaning v Hin; apply memory_distinct_in, (memory_versions_exact Hwf) in Hin.
  split.
  - apply memory_flow_le; intros source Hmem.
    apply (Hmeaning v source Hin); apply memory_flow_rhs_mem in Hmem; [|exact Hin].
    destruct Hmem as [[Hterminal ->]|[w [Hstep Hsource]]].
    + constructor; exact Hterminal.
    + eapply memory_flow_step; [exact Hstep|].
      apply (Hmeaning w source); [eapply memory_walk_next_valid; eassumption|exact Hsource].
  - intros x a Hside; cbn [memory_flow_system System.rhs] in Hside.
    rewrite memory_flow_rhs_sides in Hside; contradiction.
Qed.

(** Every post-solution includes all finite terminal walks from a valid starting version. *)
Lemma memory_flow_post_covers s :
  post_solution L S s -> forall v source,
  memory_flow_reaches ET effects mg q v source -> memory_valid_version g effects mg v ->
  fmem EV source (s v) = true.
Proof.
  intros Hpost v source Hreach; induction Hreach as [v Hterminal|
    v w source Hstep Hreach IH]; intro Hvalid.
  - assert (Hin : In v (System.constraints S)).
    { apply memory_distinct_in, (memory_versions_exact Hwf); exact Hvalid. }
    apply (proj1 (memory_flow_le EV _ _ _) (proj1 (Hpost v Hin)) v).
    apply memory_flow_rhs_mem; [exact Hvalid|left; auto].
  - assert (Hin : In v (System.constraints S)).
    { apply memory_distinct_in, (memory_versions_exact Hwf); exact Hvalid. }
    apply (proj1 (memory_flow_le EV _ _ _) (proj1 (Hpost v Hin)) source).
    apply memory_flow_rhs_mem; [exact Hvalid|right; exists w; split; [exact Hstep|]].
    apply IH; eapply memory_walk_next_valid; eassumption.
Qed.

(** A fact is semantically justified when each member has a finite terminal walk. *)
Definition memory_flow_justified (s : memory_version N E -> memory_flow_facts EN EE mg) : Prop :=
  forall v source, fmem EV source (s v) = true -> memory_flow_reaches ET effects mg q v source.

Lemma memory_flow_rhs_justified s v source :
  memory_flow_justified s -> memory_valid_version g effects mg v ->
  fmem EV source (Query.eval (System.rhs S v) s) = true ->
  memory_flow_reaches ET effects mg q v source.
Proof.
  intros Hsafe Hvalid Hmem; apply memory_flow_rhs_mem in Hmem; [|exact Hvalid].
  destruct Hmem as [[Hterminal ->]|[w [Hstep Hmem]]].
  - constructor; exact Hterminal.
  - eapply memory_flow_step; [exact Hstep|apply Hsafe; exact Hmem].
Qed.

(** One actual joining update preserves the independent finite-walk interpretation. *)
Lemma memory_flow_raise_justified s t :
  memory_flow_justified s -> raise EV L S s t -> memory_flow_justified t.
Proof.
  intros Hsafe [v [Hin Hupdate]] x source Hmem.
  assert (Hvalid : memory_valid_version g effects mg v).
  { apply memory_distinct_in, (memory_versions_exact Hwf) in Hin; exact Hin. }
  rewrite Hupdate in Hmem; unfold apply_updates, run_updates in Hmem.
  rewrite run_spec in Hmem; cbn [memory_flow_system System.rhs] in Hmem.
  rewrite memory_flow_rhs_sides in Hmem.
  cbn [fold_left fst snd] in Hmem; unfold join_update in Hmem.
  destruct (Pos.eqb (encode EV (System.target S v)) (encode EV x)) eqn:Heq;
    [|apply Hsafe; exact Hmem].
  apply Pos.eqb_eq, (encode_injective EV) in Heq.
  change (v = x) in Heq; subst x.
  destruct (leb L (Query.eval (memory_flow_rhs L next (memory_flow_seed EN EE mg) v) s)
    (s v)) eqn:Hbelow;
    [apply Hsafe; exact Hmem|].
  apply FinSet.mem_union in Hmem as [Hold|Hnew].
  - apply Hsafe; exact Hold.
  - eapply memory_flow_rhs_justified; eassumption.
Qed.

(** Runs from bottom contain only semantically justified terminal sources. *)
Lemma memory_flow_reached_justified s :
  reached EV L S s -> memory_flow_justified s.
Proof.
  intros [s0 [Hbottom Hsteps]].
  assert (Hpreserve : forall a b, clos_refl_trans _ (raise EV L S) a b ->
    memory_flow_justified a -> memory_flow_justified b).
  { intros a b Hrun; induction Hrun as [a b Hraise|a|a b c Hab IHab Hbc IHbc]; intro Hsafe.
    - eapply memory_flow_raise_justified; eassumption.
    - exact Hsafe.
    - apply IHbc, IHab; exact Hsafe. }
  apply (Hpreserve s0 s Hsteps); intros v source Hmem.
  rewrite Hbottom in Hmem; change (FinSet.mem EV source FinSet.empty = true) in Hmem.
  rewrite FinSet.mem_empty in Hmem; discriminate.
Qed.

End MemoryFlowCorrect.

(** The total joining solution contains exactly the finite terminal sources of valid versions. *)
Theorem memory_flow_exact {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  forall start source, memory_valid_version g effects mg start ->
  (fmem (memory_version_encoding EN EE) source
    (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf) start) = true <->
    memory_flow_reaches ET effects mg q start source).
Proof.
  intros start source Hvalid; split.
  - apply (memory_flow_reached_justified EN EE ET g effects mg q Hwf).
    apply solve_total_reached.
  - intro Hreach; eapply memory_flow_post_covers; [exact Hwf| |exact Hreach|exact Hvalid].
    exact (proj2_sig (memory_flow_solve EN EE ET g effects mg q Hwf)).
Qed.

Lemma memory_flow_trace_reaches {N E T} (ET : encoding T) effects (mg : memory_graph N E)
    q v trace source :
  memory_walk_trace ET effects mg q v trace -> memory_trace_last trace = Some source ->
  memory_walk_terminal ET effects mg q source -> memory_flow_reaches ET effects mg q v source.
Proof.
  intro Htrace; induction Htrace as [v|v w trace Hstep Htrace IH]; intros Hlast Hterminal.
  - cbn in Hlast; inversion Hlast; subst source; constructor; exact Hterminal.
  - eapply memory_flow_step; [exact Hstep|apply IH; [|exact Hterminal]].
    destruct Htrace; exact Hlast.
Qed.

(** Every finite source derivation has a concrete finite walk with that same terminal endpoint. *)
Lemma memory_flow_reaches_trace {N E T} (ET : encoding T) effects (mg : memory_graph N E)
    q v source :
  memory_flow_reaches ET effects mg q v source -> exists trace,
    memory_walk_trace ET effects mg q v trace /\ memory_trace_last trace = Some source /\
    memory_walk_terminal ET effects mg q source.
Proof.
  intro Hreach; induction Hreach as [v Hterminal|v w source Hstep Hreach IH].
  - exists [v]; split; [constructor|split; [reflexivity|exact Hterminal]].
  - destruct IH as [trace [Htrace [Hlast Hterminal]]]; exists (v :: trace); split.
    + econstructor; eassumption.
    + split; [destruct Htrace; exact Hlast|exact Hterminal].
Qed.

(** The actual ordered execution history contributes its last dynamic may-clobber. *)
Theorem memory_flow_execution {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input,
    memory_before mg e i = Some input /\
    fmem (memory_version_encoding EN EE)
      (memory_last_clobbers ET q e 0 (firstn i (effects e))
        (memory_path_last_clobber ET q effects es))
      (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf) input) = true.
Proof.
  intros root es e i a Hentry Hpath Hocc.
  destruct (memory_definition_before_occurrence g effects mg Hwf root es e i a Hentry Hpath Hocc)
    as [input [origin [Hprovenance [Hbefore [Hflow Horigin]]]]].
  destruct (memory_walk_provenance_history ET g effects mg q root es _ _ _ Hprovenance)
    as [prefix [Hprefix [Hprefix_last Hprefix_terminal]]].
  destruct (memory_walk_edge_history ET effects mg q e 0 (firstn i (effects e)) _ _ _ _ Hflow
    ltac:(intros j observed Hnth; eapply memory_walk_prefix_position; exact Hnth)
    prefix _ Hprefix Hprefix_last Hprefix_terminal) as [trace [Htrace [Hlast Hterminal]]].
  destruct (memory_occurrence_input_valid g effects mg Hwf e i a Hocc)
    as [incoming [Hincoming [Hvalid _]]].
  rewrite Hbefore in Hincoming; inversion Hincoming; subst incoming.
  exists input; split; [exact Hbefore|].
  apply memory_flow_exact; [exact Hvalid|].
  eapply memory_flow_trace_reaches; eassumption.
Qed.

(** Both proved constructors include the same source selected by the same actual history. *)
Theorem memory_builders_flow_agree {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g)
    (q : memory_scope T) :
  let frontier := memory_frontier_build EN EE g effects Hwf in
  let sealed := memory_sealed_build EN EE g effects Hwf in
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists vf vs,
    memory_before (proj1_sig frontier) e i = Some vf /\
    memory_before (proj1_sig sealed) e i = Some vs /\
    let source := memory_last_clobbers ET q e 0 (firstn i (effects e))
      (memory_path_last_clobber ET q effects es) in
    fmem (memory_version_encoding EN EE) source
      (proj1_sig (memory_flow_solve EN EE ET g effects (proj1_sig frontier) q
        (proj2_sig frontier)) vf) = true /\
    fmem (memory_version_encoding EN EE) source
      (proj1_sig (memory_flow_solve EN EE ET g effects (proj1_sig sealed) q
        (proj2_sig sealed)) vs) = true.
Proof.
  cbn zeta; intros root es e i a Hentry Hpath Hocc.
  destruct (memory_flow_execution EN EE ET g effects _ q
    (proj2_sig (memory_frontier_build EN EE g effects Hwf)) root es e i a Hentry Hpath Hocc)
    as [vf [Hfrontier Hfrontier_source]].
  destruct (memory_flow_execution EN EE ET g effects _ q
    (proj2_sig (memory_sealed_build EN EE g effects Hwf)) root es e i a Hentry Hpath Hocc)
    as [vs [Hsealed Hsealed_source]].
  exists vf, vs; split; [exact Hfrontier|split; [exact Hsealed|split; assumption]].
Qed.
