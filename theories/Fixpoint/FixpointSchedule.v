(** * Static priority schedules

    Static read and output summaries form a finite dependency graph for three schedulers.
    For example, a two-node dependency cycle requires a widening point in each schedule.
    Builds on: FixpointIndex, FixpointWorklist, FixpointCut and Graph algorithms. *)

From Stdlib Require Import List Bool PArith NArith Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphDag
  GraphWto GraphLoops.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointCycles
  FixpointWorklist FixpointCut.
Import List.ListNotations.

(** Every listed constraint contributes its target, reads and declared side targets. *)
Definition unknowns {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : list X :=
  distinct_unknowns EX (flat_map (fun c =>
    System.target S c :: deps SS c ++ side_targets SS c) (System.constraints S)).

(** Build the system index once and use reader buckets to construct distinct outgoing edges. *)
Definition dependency_graph {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : Graph.t X (X * X) :=
  let vertices := unknowns EX S SS in
  let ix := index_system EX S SS in
  {| Graph.entries := vertices;
     Graph.nodes := vertices;
     Graph.out := fun y => map (fun x => (y, x)) (distinct_unknowns EX
       (flat_map (fun c => System.target S c :: side_targets SS c) (readers_of EX ix y)));
     Graph.source := fst;
     Graph.target := snd |}.

(** Static unknown enumeration is duplicate-free and covers exactly the occurrences. *)
Theorem unknowns_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  NoDup (unknowns EX S SS) /\ forall x, In x (unknowns EX S SS) <->
  exists c, In c (System.constraints S) /\
    (x = System.target S c \/ In x (deps SS c) \/ In x (side_targets SS c)).
Proof.
  split; [apply distinct_unknowns_nodup|].
  intro x; unfold unknowns; rewrite distinct_unknowns_spec, in_flat_map.
  split; intros [c [Hc Hx]]; exists c; split; [exact Hc| |exact Hc|].
  - cbn in Hx; rewrite in_app_iff in Hx; intuition congruence.
  - cbn; rewrite in_app_iff; intuition congruence.
Qed.

Lemma dependency_out_spec {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (y : X) (e : X * X) :
  In e (Graph.out (dependency_graph EX S SS) y) <->
  fst e = y /\ flows SS y (snd e).
Proof.
  destruct e as [u x]; unfold dependency_graph; cbn [Graph.out fst snd].
  rewrite in_map_iff.
  split.
  - intros [z [Heq Hz]]; inversion Heq; subst u z; split; [reflexivity|].
    apply distinct_unknowns_spec in Hz; apply in_flat_map in Hz.
    destruct Hz as [c [Hc Hx]].
    apply (readers_agree (index_system_laws EX S SS)) in Hc.
    exists c; cbn in Hx; intuition congruence.
  - intros [Heq [c [Hc [Hy Hx]]]]; cbn in Heq; subst u.
    exists x; split; [reflexivity|]; apply distinct_unknowns_spec, in_flat_map.
    exists c; split.
    + apply (readers_agree (index_system_laws EX S SS)); auto.
    + cbn; intuition congruence.
Qed.

Lemma flows_unknowns {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (y x : X) :
  flows SS y x -> In y (unknowns EX S SS) /\ In x (unknowns EX S SS).
Proof.
  intros [c [Hc [Hy Hx]]]; split; apply (proj2 (unknowns_spec EX S SS));
    exists c; intuition.
Qed.

Lemma schedule_pairs_nodup {X} (y : X) (xs : list X) :
  NoDup xs -> NoDup (map (fun x => (y, x)) xs).
Proof.
  intro Hnd; induction Hnd as [|x xs Hfresh Hnd IH]; cbn; constructor; [|exact IH].
  intro Hin; apply in_map_iff in Hin; destruct Hin as [z [Heq Hz]].
  inversion Heq; subst z; contradiction.
Qed.

(** The dependency graph is well formed, has distinct outgoing edges, and represents flows. *)
Theorem dependency_graph_flows {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) :
  graph_wf (dependency_graph EX S SS) /\
  (forall v, NoDup (Graph.out (dependency_graph EX S SS) v)) /\
  forall y x, flows SS y x <-> exists e,
    In e (Graph.out (dependency_graph EX S SS) y) /\
    Graph.target (dependency_graph EX S SS) e = x.
Proof.
  split.
  - constructor.
    + exact (proj1 (unknowns_spec EX S SS)).
    + intros v Hv; exact Hv.
    + intros v e He; apply dependency_out_spec in He; exact (proj1 He).
    + intros v e _ He; apply dependency_out_spec in He.
      exact (proj2 (flows_unknowns EX S SS _ _ (proj2 He))).
  - split.
    + intro v; cbn [dependency_graph]; apply schedule_pairs_nodup.
      apply distinct_unknowns_nodup.
    + intros y x; split.
      * intro Hflow; exists (y, x); split; [apply dependency_out_spec; auto|reflexivity].
      * intros [e [He Htarget]]; apply dependency_out_spec in He.
        cbn in Htarget; now rewrite <- Htarget.
Qed.

(** Graph preparation establishes every prerequisite of the graph algorithms. *)
Theorem dependency_graph_ready {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : ready EX (dependency_graph EX S SS)
      (prepare EX (dependency_graph EX S SS)).
Proof.
  apply prepare_ready; apply dependency_graph_flows.
Qed.

(** Build positions once; absent keys receive the first priority. *)
Fixpoint schedule_positions {X} (EX : encoding X) (xs : list X) (next : positive) :
    Map.t X positive :=
  match xs with
  | [] => Map.empty
  | x :: rest => Map.set EX x next (schedule_positions EX rest (Pos.succ next))
  end.

Definition schedule_priority {X} (EX : encoding X) (positions : Map.t X positive)
    (x : X) : positive :=
  match Map.get EX x positions with
  | Some p => p
  | None => 1%positive
  end.

(** Collect the targets of edges that retreat to DFS ancestors. *)
Definition schedule_retreats {X E} (EX : encoding X) (g : Graph.t X E)
    (r : dfs_result X E) : FinSet.t X :=
  FinSet.of_list EX (flat_map (fun y => map (Graph.target g)
    (filter (fun e => ancestor_b EX r (Graph.target g e) (Graph.source g e))
      (Graph.out g y))) (Graph.nodes g)).

(** RPO priorities widen at the targets of retreating DFS edges. *)
Definition rpo_scheduler {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : scheduler X :=
  let g := dependency_graph EX S SS in
  let p := prepare EX g in
  let r := dfs p FinSet.empty (Graph.entries g) in
  let positions := schedule_positions EX (rpo r) 1 in
  let heads := schedule_retreats EX g r in
  {| priority := schedule_priority EX positions;
     widening_point := fun x => FinSet.mem EX x heads |}.

(** Opening tokens are precisely the component heads of a weak topological order. *)
Fixpoint schedule_heads {X} (w : wto X) : list X :=
  match w with
  | [] => []
  | WOpen h :: rest => h :: schedule_heads rest
  | _ :: rest => schedule_heads rest
  end.

(** WTO textual priorities widen at its component heads. *)
Definition wto_scheduler {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : scheduler X :=
  let g := dependency_graph EX S SS in
  let p := prepare EX g in
  let w := wto_total p in
  let positions := schedule_positions EX (wto_order w) 1 in
  let heads := FinSet.of_list EX (schedule_heads w) in
  {| priority := schedule_priority EX positions;
     widening_point := fun x => FinSet.mem EX x heads |}.

(** Number components in topological order, without searching their member lists later. *)
Fixpoint schedule_components {X} (EX : encoding X) (cs : list (list X)) (next : N) :
    Map.t X N :=
  match cs with
  | [] => Map.empty
  | members :: rest => fold_left (fun m x => Map.set EX x next m) members
      (schedule_components EX rest (N.succ next))
  end.

(** SCC priorities put predecessors first and use RPO within each component. *)
Definition scc_scheduler {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) : scheduler X :=
  let g := dependency_graph EX S SS in
  let p := prepare EX g in
  let r := dfs p FinSet.empty (Graph.entries g) in
  let positions := schedule_positions EX (rpo r) 1 in
  let cs := scc_within p (Graph.nodes g) in
  let component_positions := schedule_components EX (rev (components cs)) 0%N in
  let n := N.of_nat (length (Graph.nodes g)) in
  let heads := FinSet.of_list EX (loop_headers (loop_forest_of p)) in
  {| priority := fun x =>
       let comp := match Map.get EX x component_positions with
         | Some k => k
         | None => 0%N
         end in
       N.succ_pos (comp * n + (Npos (schedule_priority EX positions x) - 1))%N;
     widening_point := fun x => FinSet.mem EX x heads |}.

(** Sort the graph remaining after deleting edges into cuts and removing cut vertices. *)
Definition plan_of {X C A} (EX : encoding X) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (cuts : FinSet.t X) : option (list X) :=
  let g := without EX cuts (dependency_graph EX S SS) in
  topological_sort (prepare EX g).

(** * Transporting cycles *)

Section ScheduleCycles.
Context {X C A : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).
Local Abbreviation g := (dependency_graph EX S SS).
Local Abbreviation p := (prepare EX g).

Lemma schedule_flow_path (W : X -> bool) (u v : X) :
  clos_trans X (fun y z => flows SS y z /\ W z = false) u v ->
  In u (unknowns EX S SS) /\ W v = false /\
  exists es, es <> [] /\ path g u es v /\
    forall e, In e es -> W (Graph.target g e) = false.
Proof.
  intro Hflow; induction Hflow as [u v [Hflow Hv]|u v z Huv IHuv Hvz IHvz].
  - split; [exact (proj1 (flows_unknowns EX S SS u v Hflow))|].
    split; [exact Hv|]; exists [(u, v)]; split; [discriminate|]; split.
    + apply (@path_cons X (X * X) g (u, v) [] v);
        [apply dependency_out_spec; auto|constructor].
    + intros e [Heq|Hfalse]; [now subst e|contradiction].
  - destruct IHuv as [Hu [_ [es [Hes [Hpathes Htargets]]]]].
    destruct IHvz as [_ [Hz [fs [Hfs [Hpathfs Htargetsf]]]]].
    split; [exact Hu|]; split; [exact Hz|]; exists (es ++ fs); split.
    + intro Hnil; apply app_eq_nil in Hnil; tauto.
    + split; [eapply tarjan_path_append; eassumption|].
      intros e Hin; apply in_app_iff in Hin; destruct Hin; auto.
Qed.

Lemma schedule_cycle_free (W : X -> bool) (v : X) (es : list (X * X)) :
  W v = false -> (forall e, In e es -> W (Graph.target g e) = false) ->
  forall h, h = v \/ In h (map (Graph.target g) es) -> W h = false.
Proof.
  intros Hv Htargets h [Heq|Hin]; [now subst h|].
  apply in_map_iff in Hin; destruct Hin as [e [Heq He]]; subst h; auto.
Qed.

Lemma schedule_retreat_member (r : dfs_result X (X * X)) (e : X * X) :
  In (Graph.source g e) (Graph.nodes g) -> In e (Graph.out g (Graph.source g e)) ->
  ancestor_b EX r (Graph.target g e) (Graph.source g e) = true ->
  FinSet.mem EX (Graph.target g e) (schedule_retreats EX g r) = true.
Proof.
  intros Hsource Hedge Hback; apply FinSet.of_list_spec, in_flat_map.
  exists (Graph.source g e); split; [exact Hsource|]; apply in_map, filter_In; auto.
Qed.

(** RPO retreating targets intersect every nonempty flow cycle. *)
Theorem rpo_scheduler_cuts :
  cuts_every_cycle SS (widening_point (rpo_scheduler EX S SS)).
Proof.
  intros v Hcycle.
  destruct (schedule_flow_path _ _ _ Hcycle) as [Hv [Hfree [es [Hnonempty [Hpath Htargets]]]]].
  pose proof (dependency_graph_ready EX S SS) as Hready.
  assert (Hroots : incl (Graph.entries g) (Graph.nodes g)) by (intros x Hx; exact Hx).
  assert (Hvisited : forall x, In x (Graph.nodes g) ->
    FinSet.mem EX x (visited (dfs p FinSet.empty (Graph.entries g))) = true).
  { intros x Hx; apply dag_root_visited; assumption. }
  destruct (cycle_has_retreating_edge EX g p v es (Graph.entries g)
    Hready Hroots (Hvisited v Hv) Hnonempty Hpath) as [e [He Hback]].
  destruct (wto_path_edges g v es v Hpath (@reachable_entry X (X * X) g v Hv) e He)
    as [_ [Hreach Hedge]].
  assert (Hsource : In (Graph.source g e) (Graph.nodes g)).
  { eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hreach]. }
  assert (Htarget : In (Graph.target g e) (Graph.nodes g)).
  { eapply out_target_in; [exact (proj1 Hready)|exact Hsource|exact Hedge]. }
  apply (proj2 (ancestor_b_agrees EX g p _ _ _ FinSet.empty Hready Hroots
    (Hvisited _ Htarget) (Hvisited _ Hsource))) in Hback.
  pose proof (schedule_retreat_member _ e Hsource Hedge Hback) as Hmem.
  specialize (Htargets e He); change (FinSet.mem EX (Graph.target g e)
    (schedule_retreats EX g (dfs p FinSet.empty (Graph.entries g))) = false) in Htargets.
  congruence.
Qed.

Lemma schedule_annotate_heads (w : wto X) (stack : list X) (x h : X) (st : list X) :
  In (x, st) (annotate stack w) -> In h st -> In h stack \/ In h (schedule_heads w).
Proof.
  revert stack; induction w as [|[v|v|] rest IH]; intros stack Hrow Hh; cbn in *.
  - contradiction.
  - destruct Hrow as [Heq|Hrow].
    + inversion Heq; subst st; now left.
    + exact (IH stack Hrow Hh).
  - destruct Hrow as [Heq|Hrow].
    + inversion Heq; subst st; cbn in Hh; intuition.
    + destruct (IH (v :: stack) Hrow Hh) as [[Heq|Hin]|Hin]; intuition.
  - destruct (IH (tl stack) Hrow Hh) as [Hin|Hin]; [left|now right].
    destruct stack; [exact Hin|now right].
Qed.

(** WTO component heads intersect every nonempty flow cycle. *)
Theorem wto_scheduler_cuts :
  cuts_every_cycle SS (widening_point (wto_scheduler EX S SS)).
Proof.
  intros v Hcycle.
  destruct (schedule_flow_path _ _ _ Hcycle) as [Hv [Hfree [es [Hnonempty [Hpath Htargets]]]]].
  pose proof (wto_total_valid EX g p (dependency_graph_ready EX S SS)) as Hvalid.
  destruct (wto_valid_cycles g (wto_total p) Hvalid v es (@reachable_entry X (X * X) g v Hv)
    Hnonempty Hpath) as [h [Hh Hcontains]].
  assert (Hrow : exists st, In (v, st) (annotate [] (wto_total p))).
  { pose proof (proj2 (proj1 (proj2 (proj2 Hvalid)) v)
      (@reachable_entry X (X * X) g v Hv)) as Hin.
    unfold wto_order in Hin; apply in_map_iff in Hin.
    destruct Hin as [[x st] [Heq Hrow]]; cbn in Heq; subst x; now exists st. }
  destruct Hrow as [st Hrow].
  specialize (Hcontains v st (or_introl eq_refl) Hrow).
  destruct (schedule_annotate_heads _ [] v h st Hrow Hcontains) as [Hfalse|Hhead];
    [contradiction|].
  assert (Hmem : FinSet.mem EX h (FinSet.of_list EX (schedule_heads (wto_total p))) = true).
  { apply FinSet.of_list_spec; exact Hhead. }
  pose proof (schedule_cycle_free _ v es Hfree Htargets h Hh) as Hnot.
  change (FinSet.mem EX h (FinSet.of_list EX (schedule_heads (wto_total p))) = false)
    in Hnot; congruence.
Qed.

(** Loop forest headers used by the SCC scheduler intersect every nonempty flow cycle. *)
Theorem scc_scheduler_cuts :
  cuts_every_cycle SS (widening_point (scc_scheduler EX S SS)).
Proof.
  intros v Hcycle.
  destruct (schedule_flow_path _ _ _ Hcycle) as [Hv [Hfree [es [Hnonempty [Hpath Htargets]]]]].
  destruct (loop_forest_covers EX g p (dependency_graph_ready EX S SS) v es
    (@reachable_entry X (X * X) g v Hv) Hnonempty Hpath) as [h [Hhead [Hh _]]].
  assert (Hmem : FinSet.mem EX h (FinSet.of_list EX (loop_headers (loop_forest_of p))) = true).
  { apply FinSet.of_list_spec; exact Hhead. }
  pose proof (schedule_cycle_free _ v es Hfree Htargets h Hh) as Hnot.
  change (FinSet.mem EX h (FinSet.of_list EX (loop_headers (loop_forest_of p))) = false)
    in Hnot; congruence.
Qed.

End ScheduleCycles.

(** * Non-cut plans *)

Section SchedulePlans.
Context {X C A : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).
Local Abbreviation g := (dependency_graph EX S SS).

Lemma schedule_without_ready (cuts : FinSet.t X) :
  ready EX (without EX cuts g) (prepare EX (without EX cuts g)).
Proof.
  destruct (dependency_graph_flows EX S SS) as [Hwf [Hdistinct _]].
  apply prepare_ready.
  - constructor; cbn [without].
    + apply NoDup_filter; exact (nodes_nodup Hwf).
    + intros v Hv; exact Hv.
    + intros v e He; apply filter_In in He; exact (out_source Hwf v e (proj1 He)).
    + intros v e Hv He; apply filter_In in Hv, He; apply filter_In; split.
      * exact (out_target_in Hwf v e (proj1 Hv) (proj1 He)).
      * exact (proj2 He).
  - intro v; apply NoDup_filter; apply Hdistinct.
Qed.

Lemma schedule_without_path (cuts : FinSet.t X) (u : X) (es : list (X * X)) (v : X) :
  path (without EX cuts g) u es v ->
  (es = [] /\ u = v) \/
  clos_trans X (fun y z => flows SS y z /\ FinSet.mem EX z cuts = false) u v.
Proof.
  intro Hpath; induction Hpath as [v|e es v He Hpath IH].
  - now left.
  - right; apply filter_In in He; destruct He as [He Hfree].
    apply negb_true_iff in Hfree; apply dependency_out_spec in He.
    assert (Hstep : flows SS (Graph.source g e) (Graph.target g e) /\
      FinSet.mem EX (Graph.target g e) cuts = false) by (split; [exact (proj2 He)|exact Hfree]).
    destruct IH as [[_ Heq]|Htail].
    + cbn [without Graph.target] in Heq; subst v; apply t_step; exact Hstep.
    + eapply t_trans; [apply t_step; exact Hstep|exact Htail].
Qed.

Lemma schedule_without_acyclic (cuts : FinSet.t X) :
  cuts_every_cycle SS (fun x => FinSet.mem EX x cuts) -> acyclic (without EX cuts g).
Proof.
  intros Hcuts v es _ Hpath.
  destruct (schedule_without_path cuts v es v Hpath) as [[Hnil _]|Hcycle];
    [exact Hnil|exfalso; exact (Hcuts v Hcycle)].
Qed.

Lemma schedule_before_prefix (l1 : list X) (x : X) (l2 : list X) (y : X) :
  NoDup (l1 ++ x :: l2) -> before (l1 ++ x :: l2) y x -> In y l1.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros Hnd Hbefore.
  - inversion Hnd as [|x' rest Hfresh Htail]; subst x' rest.
    apply dfs_before_cons in Hbefore; destruct Hbefore as [[_ Hin]|Hbefore].
    + contradiction.
    + destruct Hbefore as [first [middle [last Heq]]].
      apply Hfresh; rewrite Heq; apply in_or_app; right; cbn; right.
      apply in_or_app; right; now left.
  - inversion Hnd as [|a' rest Hfresh Htail]; subst a' rest.
    apply dfs_before_cons in Hbefore; destruct Hbefore as [[Heq _]|Hbefore].
    + now left.
    + right; apply IH; assumption.
Qed.

Lemma schedule_topological_plan (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) :
  sys_index_laws EX S SS ix -> topological_order (without EX cuts g) plan ->
  plan_valid EX S SS ix cuts plan.
Proof.
  intros Hix [Hnd [Hmembers Hedges]]; split; [exact Hnd|]; split.
  - intros x Hx; apply Hmembers, filter_In in Hx; apply negb_true_iff; exact (proj2 Hx).
  - split.
    + intros c Hc x Hx; destruct (FinSet.mem EX x cuts) eqn:Hcut; [now left|right].
      apply Hmembers, filter_In; split; [|now apply negb_true_iff].
      apply (proj2 (unknowns_spec EX S SS)); exists c; intuition.
    + intros l1 x l2 Hplan c Hc y Hy.
      destruct (FinSet.mem EX y cuts) eqn:Hycut; [now left|right; left].
      assert (Hflow : flows SS y x).
      { apply (contributors_agree Hix) in Hc; destruct Hc as [Hc Hx].
        exists c; intuition congruence. }
      assert (Hxplan : In x plan) by (rewrite Hplan; apply in_or_app; right; now left).
      pose proof (proj1 (Hmembers x) Hxplan) as Hxnode.
      apply filter_In in Hxnode.
      assert (Hynode : In y (Graph.nodes (without EX cuts g))).
      { apply filter_In; split; [exact (proj1 (flows_unknowns EX S SS y x Hflow))|].
        now apply negb_true_iff. }
      assert (Hout : In (y, x) (Graph.out (without EX cuts g) y)).
      { apply filter_In; split; [apply dependency_out_spec; auto|exact (proj2 Hxnode)]. }
      pose proof (Hedges (y, x) Hynode Hout) as Hbefore.
      apply schedule_before_prefix with x l2; rewrite <- Hplan; assumption.
Qed.

(** A plan exists exactly for cycle cuts, and every returned order satisfies the cut contract. *)
Theorem plan_of_valid (ix : sys_index X C) (cuts : FinSet.t X) :
  sys_index_laws EX S SS ix ->
  (cuts_every_cycle SS (fun x => FinSet.mem EX x cuts) <->
    exists plan, plan_of EX S SS ix cuts = Some plan) /\
  forall plan, plan_of EX S SS ix cuts = Some plan -> plan_valid EX S SS ix cuts plan.
Proof.
  intro Hix.
  destruct (topological_sort_correct EX (without EX cuts g)
    (prepare EX (without EX cuts g)) (schedule_without_ready cuts)) as [Hsort Hnone].
  assert (Hvalid : forall plan, plan_of EX S SS ix cuts = Some plan ->
    plan_valid EX S SS ix cuts plan).
  { intros plan Hplan; apply schedule_topological_plan; [exact Hix|apply Hsort; exact Hplan]. }
  split; [split|exact Hvalid].
  - intro Hcuts; unfold plan_of.
    destruct (topological_sort (prepare EX (without EX cuts g))) as [plan|] eqn:Hplan.
    + exists plan; reflexivity.
    + exfalso; apply (proj1 Hnone eq_refl), schedule_without_acyclic; exact Hcuts.
  - intros [plan Hplan]; apply (plan_valid_cuts EX S SS ix cuts plan Hix), Hvalid; exact Hplan.
Qed.

End SchedulePlans.
