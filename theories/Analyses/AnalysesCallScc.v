(** * Indexed call summaries and reachable contexts

    Prepared call indexes retain resolver order while a callee-first indexed worklist solves
    summary equations and dependency-closed reachable context equations.
    For example, two occurrences of one callee remain two caller contributions in argument facts.
    Builds on: AnalysesCalls, GraphScc, GraphDfs, FixpointIndex and FixpointTotal. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal FixpointLeast.
From Gaulois.Views Require Import ViewsSemantics ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesCalls.
Import List.ListNotations.

(** * Resolver and caller preparation *)

(** Target lookups preserve lists; caller lookups retain every listed site occurrence. *)
Record call_index (F P : Type) : Type := CallIndex {
  indexed_targets : P -> list F;
  indexed_callers : F -> list P
}.

Arguments CallIndex {F P}.
Arguments indexed_targets {F P}.
Arguments indexed_callers {F P}.

(** Listed sites are cached once, with the original resolver as the missing-site fallback. *)
Definition prepare_calls {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) : call_index F P :=
  let targets := fold_right (fun p ix => Map.set EP p (resolve p) ix)
    Map.empty (distinct_unknowns EP (flat_map (sites_of cv) (functions cv))) in
  let target := fun p => match Map.get EP p targets with
    | Some fs => fs
    | None => resolve p
    end in
  let callers := callers_index EF cv target in
  CallIndex target (callers_of EF callers).

(** A cache filled with resolver lists agrees even for sites outside its finite domain. *)
Lemma call_targets_lookup {P F} (EP : encoding P) (resolve : P -> list F) ps p :
  match Map.get EP p (fold_right (fun q ix => Map.set EP q (resolve q) ix) Map.empty ps) with
  | Some fs => fs
  | None => resolve p
  end = resolve p.
Proof.
  induction ps as [|q ps IH]; cbn [fold_right].
  - rewrite Map.get_empty; reflexivity.
  - destruct (calls_eq_dec EP p q) as [->|Hne].
    + rewrite Map.get_set_same; reflexivity.
    + rewrite Map.get_set_other by exact Hne; exact IH.
Qed.

(** * Finite listed-graph validation *)

(** Collect a membership index and reject exactly repeated encoded keys in the same pass. *)
Fixpoint call_inventory {X} (EX : encoding X) (xs : list X) : FinSet.t X * bool :=
  match xs with
  | [] => (FinSet.empty, true)
  | x :: rest =>
    let '(seen, unique) := call_inventory EX rest in
    (FinSet.add EX x seen, negb (FinSet.mem EX x seen) && unique)
  end.

(** The inventory contains precisely the input keys and records their uniqueness. *)
Lemma call_inventory_agrees {X} (EX : encoding X) xs :
  (forall x, FinSet.mem EX x (fst (call_inventory EX xs)) = true <-> In x xs) /\
  (snd (call_inventory EX xs) = true <-> NoDup xs).
Proof.
  induction xs as [|x xs [Hmembers Hunique]].
  - cbn [call_inventory]; split.
    + intro x; change (FinSet.mem EX x FinSet.empty = true <-> False).
      rewrite FinSet.mem_empty; intuition discriminate.
    + split; [intros _; constructor|reflexivity].
  - cbn [call_inventory] in *.
    destruct (call_inventory EX xs) as [seen unique] eqn:Hinventory; cbn in *.
    split.
    + intro y; rewrite FinSet.mem_add, Hmembers; cbn; intuition congruence.
    + rewrite andb_true_iff, negb_true_iff, Hunique.
      split.
      * intros [Hfresh Hnodup]; constructor; [|exact Hnodup].
        intro Hin; apply Hmembers in Hin; congruence.
      * intro Hnodup; inversion Hnodup as [|? ? Hfresh Htail]; subst.
        split; [|exact Htail].
        destruct (FinSet.mem EX x seen) eqn:Hmem; [|reflexivity].
        exfalso; apply Hfresh, Hmembers; exact Hmem.
Qed.

(** Listed validation observes no outgoing edge of an unlisted node. *)
Definition call_listed_wf {X E} (g : Graph.t X E) : Prop :=
  NoDup (Graph.nodes g) /\ incl (Graph.entries g) (Graph.nodes g) /\
  forall x e, In x (Graph.nodes g) -> In e (Graph.out g x) ->
    Graph.source g e = x /\ In (Graph.target g e) (Graph.nodes g).

(** Check only generated listed edges, so a site with no targets imposes no source test. *)
Definition call_listed_check {X E} (EX : encoding X) (g : Graph.t X E) : bool :=
  let '(listed, unique) := call_inventory EX (Graph.nodes g) in
  unique && forallb (fun x => FinSet.mem EX x listed) (Graph.entries g) &&
    forallb (fun x => forallb (fun e =>
      Pos.eqb (encode EX (Graph.source g e)) (encode EX x) &&
      FinSet.mem EX (Graph.target g e) listed) (Graph.out g x)) (Graph.nodes g).

(** Acceptance is exactly the finite listed property, rather than global raw well-formedness. *)
Lemma call_listed_check_exact {X E} (EX : encoding X) (g : Graph.t X E) :
  call_listed_check EX g = true <-> call_listed_wf g.
Proof.
  pose proof (call_inventory_agrees EX (Graph.nodes g)) as [Hmembers Hunique].
  unfold call_listed_check, call_listed_wf.
  destruct (call_inventory EX (Graph.nodes g)) as [listed unique]; cbn in *.
  rewrite !andb_true_iff, Hunique, !forallb_forall.
  split.
  - intros [[Hnodup Hroots] Hedges]; split; [exact Hnodup|]; split.
    + intros x Hx; apply Hmembers, Hroots; exact Hx.
    + intros x e Hx He; specialize (Hedges x Hx).
      apply forallb_forall with (x := e) in Hedges; [|exact He].
      apply andb_true_iff in Hedges; destruct Hedges as [Hsource Htarget].
      split; [apply (encode_injective EX), Pos.eqb_eq; exact Hsource|].
      apply Hmembers; exact Htarget.
  - intros [Hnodup [Hroots Hedges]]; split; [split; [exact Hnodup|]|].
    + intros x Hx; apply Hmembers, Hroots; exact Hx.
    + intros x Hx; apply forallb_forall; intros e He.
      destruct (Hedges x e Hx He) as [Hsource Htarget].
      apply andb_true_iff; split.
      * rewrite Hsource; apply Pos.eqb_refl.
      * apply Hmembers; exact Htarget.
Qed.

(** Full raw graph well-formedness always passes the finite listed check. *)
Lemma call_listed_check_complete {X E} (EX : encoding X) (g : Graph.t X E) :
  graph_wf g -> call_listed_check EX g = true.
Proof.
  intro Hwf; apply call_listed_check_exact; split; [exact (nodes_nodup Hwf)|]; split.
  - exact (entries_in Hwf).
  - intros x e Hx He; split.
    + exact (out_source Hwf x e He).
    + exact (out_target_in Hwf x e Hx He).
Qed.

(** * Distinct adjacency for component preparation *)

(** Only the component graph merges parallel targets; summary rows retain their original lists. *)
Definition call_scc_graph {X E} (EX : encoding X) (g : Graph.t X E) : Graph.t X (X * X) :=
  {| Graph.entries := Graph.entries g;
     Graph.nodes := Graph.nodes g;
     Graph.out := index_edges EX (calls_target_index EX g);
     Graph.source := fst;
     Graph.target := snd |}.

(** A distinct adjacency edge represents exactly one or more raw edges to its target. *)
Lemma call_scc_edge {X E} (EX : encoding X) (g : Graph.t X E) x y :
  In (x, y) (Graph.out (call_scc_graph EX g) x) <->
  In x (Graph.nodes g) /\ exists e, In e (Graph.out g x) /\ Graph.target g e = y.
Proof.
  apply (calls_finite_edge EX g x x y).
Qed.

(** Every normalized edge is stored under its own source. *)
Lemma call_scc_source {X E} (EX : encoding X) (g : Graph.t X E) x e :
  In e (Graph.out (call_scc_graph EX g) x) -> fst e = x.
Proof.
  apply (calls_finite_source EX g x x e).
Qed.

(** Normalization supplies all graph and uniqueness premises required by Tarjan. *)
Lemma call_scc_ready {X E} (EX : encoding X) (g : Graph.t X E) :
  graph_wf g -> ready EX (call_scc_graph EX g) (prepare EX (call_scc_graph EX g)).
Proof.
  intro Hwf; apply prepare_ready.
  - constructor.
    + exact (nodes_nodup Hwf).
    + exact (entries_in Hwf).
    + apply call_scc_source.
    + intros x [u v] Hx Hedge; cbn.
      pose proof (call_scc_source EX g x (u, v) Hedge) as Hsource; cbn in Hsource; subst u.
      apply call_scc_edge in Hedge; destruct Hedge as [_ [e [Hedge <-]]].
      eapply out_target_in; eassumption.
  - intro x.
    change (NoDup (Graph.out (calls_finite_graph EX g x) x)).
    rewrite calls_finite_out; destruct (existsb _ _); [|constructor].
    pose proof (FinSet.elements_nodup EX
      (FinSet.of_list EX (map (Graph.target g) (Graph.out g x)))
      (FinSet.wf_fold_add EX _ _ (Map.wf_empty EX))) as Hnodup.
    induction Hnodup as [|v vs Hfresh Hnodup IH]; cbn; [constructor|].
    constructor; [|exact IH].
    rewrite in_map_iff; intros [w [Heq Hin]]; inversion Heq; subst w; contradiction.
Qed.

(** Every listed raw path has a normalized path with the same endpoints. *)
Lemma call_scc_path_forward {X E} (EX : encoding X) (g : Graph.t X E) x es y :
  graph_wf g -> In x (Graph.nodes g) -> path g x es y ->
  exists edges, path (call_scc_graph EX g) x edges y.
Proof.
  intros Hwf Hx Hpath; revert Hx.
  induction Hpath as [x|e es y Hedge Hpath IH]; intro Hx.
  - exists []; constructor.
  - destruct (IH (out_target_in Hwf _ _ Hx Hedge)) as [edges Hedges].
    exists ((Graph.source g e, Graph.target g e) :: edges).
    apply (path_cons (g := call_scc_graph EX g)
      (Graph.source g e, Graph.target g e) edges y).
    + apply call_scc_edge; split; [exact Hx|exists e; auto].
    + exact Hedges.
Qed.

(** Each normalized path can be expanded into raw edges with the same endpoints. *)
Lemma call_scc_path_backward {X E} (EX : encoding X) (g : Graph.t X E) x edges y :
  graph_wf g -> path (call_scc_graph EX g) x edges y -> exists es, path g x es y.
Proof.
  intros Hwf Hpath; induction Hpath as [x|[u v] edges y Hedge Hpath [es Hes]].
  - exists []; constructor.
  - cbn in *; apply call_scc_edge in Hedge.
    destruct Hedge as [Hu [e [Hedge Htarget]]].
    pose proof (out_source Hwf u e Hedge) as Hsource.
    exists (e :: es); rewrite <- Hsource; apply path_cons.
    + rewrite Hsource; exact Hedge.
    + rewrite Htarget; exact Hes.
Qed.

(** Removing duplicate targets preserves mutual reachability between all listed functions. *)
Lemma call_scc_mutual {X E} (EX : encoding X) (g : Graph.t X E) x y :
  graph_wf g -> In x (Graph.nodes g) -> In y (Graph.nodes g) ->
  (mutual (call_scc_graph EX g) x y <-> mutual g x y).
Proof.
  intros Hwf Hx Hy; split; intros [[es Hxy] [fs Hyx]]; split.
  - eapply call_scc_path_backward; eassumption.
  - eapply call_scc_path_backward; eassumption.
  - eapply call_scc_path_forward; eassumption.
  - eapply call_scc_path_forward; eassumption.
Qed.

(** The component ID is the queue priority, with callees emitted before their callers. *)
Definition call_scc_scheduler {X E} (EX : encoding X) (g : Graph.t X E) : scheduler X :=
  let graph := call_scc_graph EX g in
  let result := scc (prepare EX graph) in
  Scheduler (scc_owner EX result) (fun _ => false).

(** Every normalized call edge points to an equal or earlier queue priority. *)
Lemma call_scc_priority {X E} (EX : encoding X) (g : Graph.t X E) x e :
  graph_wf g -> In x (Graph.nodes g) -> In e (Graph.out g x) ->
  (priority (call_scc_scheduler EX g) (Graph.target g e) <=
    priority (call_scc_scheduler EX g) x)%positive.
Proof.
  intros Hwf Hx Hedge.
  pose proof (out_target_in Hwf x e Hx Hedge) as Htarget.
  set (graph := call_scc_graph EX g).
  set (prepared := prepare EX graph).
  assert (Hready : ready EX graph prepared) by (apply call_scc_ready; exact Hwf).
  assert (Hedge' : In (x, Graph.target g e) (Graph.out graph x)).
  { apply call_scc_edge; split; [exact Hx|exists e; auto]. }
  destruct (scc_reverse_topological EX graph prepared (x, Graph.target g e)
    (Graph.nodes graph) Hready (incl_refl _) Hedge' Hx Htarget)
    as [i [j [Hi [Hj Hle]]]].
  change (Map.get EX x (comp_of (scc prepared)) = Some i) in Hi.
  change (Map.get EX (Graph.target g e) (comp_of (scc prepared)) = Some j) in Hj.
  change ((scc_owner EX (scc prepared) (Graph.target g e) <=
    scc_owner EX (scc prepared) x)%positive).
  unfold scc_owner; rewrite Hi, Hj; exact Hle.
Qed.

(** Cached targets agree exactly, including order, duplicates and unlisted-site results. *)
Theorem prepare_calls_targets {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) :
  forall p, indexed_targets (prepare_calls EF EP cv resolve) p = resolve p.
Proof.
  intro p; apply call_targets_lookup.
Qed.

(** Caller membership is exactly listed-site membership and resolver membership. *)
Theorem prepare_calls_callers {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) :
  forall f p, In p (indexed_callers (prepare_calls EF EP cv resolve) f) <->
    (exists g, In g (functions cv) /\ In p (sites_of cv g)) /\ In f (resolve p).
Proof.
  intros f p; unfold prepare_calls; cbn [indexed_callers].
  rewrite callers_index_agrees, call_targets_lookup; reflexivity.
Qed.

(** The prepared caller map stores each binding at its encoded function key. *)
Theorem callers_index_wf {S F P} (EF : encoding F) (cv : calls_view S F P)
    (resolve : P -> list F) : Map.wf EF (callers_index EF cv resolve).
Proof.
  unfold callers_index; induction (flat_map (sites_of cv) (functions cv)) as [|p ps IH].
  - apply Map.wf_empty.
  - cbn [fold_right]; induction (resolve p) as [|f fs IHfs].
    + exact IH.
    + cbn [fold_right]; apply Map.wf_set; exact IHfs.
Qed.

(** * Argument-position preparation *)

(** Traverse each actual list once, joining the corresponding stored position in caller order. *)
Fixpoint call_arguments_add {V A} (L : lattice A) (fact : V -> A) (xs : list V)
    (position : nat) (acc : Map.t nat A) : Map.t nat A :=
  match xs with
  | [] => acc
  | x :: rest => call_arguments_add L fact rest (Datatypes.S position)
      (Map.set nat_encoding position
        (join L (lookup nat_encoding L acc position) (fact x)) acc)
  end.

(** Adding a suffix of actuals leaves earlier argument positions untouched. *)
Lemma call_arguments_before {V A} (L : lattice A) (fact : V -> A) xs position acc i :
  i < position ->
  lookup nat_encoding L (call_arguments_add L fact xs position acc) i =
    lookup nat_encoding L acc i.
Proof.
  revert position acc; induction xs as [|x xs IH]; intros position acc Hbefore.
  - reflexivity.
  - cbn [call_arguments_add]; rewrite IH by lia.
    apply lookup_set_other; lia.
Qed.

(** A present actual joins once at its position, while a missing actual preserves the old fact. *)
Lemma call_arguments_position {V A} (L : lattice A) (fact : V -> A) xs position acc n :
  lookup nat_encoding L (call_arguments_add L fact xs position acc) (position + n) =
    match nth_error xs n with
    | Some x => join L (lookup nat_encoding L acc (position + n)) (fact x)
    | None => lookup nat_encoding L acc (position + n)
    end.
Proof.
  revert position acc n; induction xs as [|x xs IH]; intros position acc [|n].
  - reflexivity.
  - reflexivity.
  - cbn [call_arguments_add nth_error]; rewrite Nat.add_0_r.
    rewrite call_arguments_before by lia; apply lookup_set_same.
  - cbn [call_arguments_add nth_error].
    replace (position + Datatypes.S n) with (Datatypes.S position + n) by lia.
    rewrite IH; destruct (nth_error xs n); rewrite lookup_set_other by lia; reflexivity.
Qed.

(** A caller bucket is folded left so no lattice algebra is needed for exact agreement. *)
Definition call_arguments_bucket {S F P V C A} (av : args_view S F P V C)
    (L : lattice A) (fact : V -> A) (ps : list P) : Map.t nat A :=
  fold_left (fun acc p => call_arguments_add L fact (actuals av p) 0 acc) ps Map.empty.

(** Position lookup commutes exactly with the left fold over caller occurrences. *)
Lemma call_arguments_fold {S F P V C A} (av : args_view S F P V C)
    (L : lattice A) (fact : V -> A) ps acc i :
  lookup nat_encoding L
    (fold_left (fun acc p => call_arguments_add L fact (actuals av p) 0 acc) ps acc) i =
  fold_left (fun a p => match nth_error (actuals av p) i with
    | Some x => join L a (fact x)
    | None => a
    end) ps (lookup nat_encoding L acc i).
Proof.
  revert acc; induction ps as [|p ps IH]; intro acc; cbn [fold_left].
  - reflexivity.
  - rewrite IH.
    pose proof (call_arguments_position L fact (actuals av p) 0 acc i) as Hposition.
    cbn [Nat.add] in Hposition; rewrite Hposition; reflexivity.
Qed.

(** Folding present actuals in caller order equals the retained flattened argument fold. *)
Lemma call_arguments_flat {S F P V C A} (av : args_view S F P V C)
    (L : lattice A) (fact : V -> A) ps a i :
  fold_left (fun a p => match nth_error (actuals av p) i with
    | Some x => join L a (fact x)
    | None => a
    end) ps a =
  fold_left (join L) (flat_map (fun p => match nth_error (actuals av p) i with
    | Some x => [fact x]
    | None => []
    end) ps) a.
Proof.
  revert a; induction ps as [|p ps IH]; intro a; cbn [fold_left flat_map].
  - reflexivity.
  - destruct (nth_error (actuals av p) i); cbn [app fold_left]; apply IH.
Qed.

(** Prepare all function-position facts once, then answer with two encoded lookups. *)
Definition arg_facts_indexed {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) : F -> nat -> A :=
  let facts := Map.map (call_arguments_bucket av L fact) ix in
  fun f i => match Map.get EF f facts with
    | Some positions => lookup nat_encoding L positions i
    | None => bot L
    end.

(** Indexed argument facts preserve the original fold exactly, including duplicate calls. *)
Theorem arg_facts_indexed_agrees {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) :
  Map.wf EF ix ->
  forall f i, arg_facts_indexed EF av ix L fact f i = arg_fact EF av ix L fact f i.
Proof.
  intros Hwf f i; unfold arg_facts_indexed; rewrite Map.get_map.
  unfold arg_fact, callers_of; destruct (Map.get EF f ix) as [ps|]; cbn [option_map].
  - unfold call_arguments_bucket; rewrite call_arguments_fold, call_arguments_flat.
    unfold lookup; rewrite Map.get_empty; reflexivity.
  - reflexivity.
Qed.

(** * Indexed joining execution *)

Section CallJoining.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (Hheight : inhabited (height L))
  (sys : System.t X C A) (stat : System.static sys) (sch : scheduler X).
Local Abbreviation ix := (index_system EX sys stat).
Local Abbreviation dep := (Declared stat ix).

(** The executable result carries a finite trace ending at its first empty queue. *)
Definition call_finished (prepared : sys_index X C) (start : Engine.t X C A) : Type :=
  {last : Engine.t X C A | exists n,
    engine_steps EX EC L sch Joining sys (Declared stat prepared) n start last /\
      engine_step EX EC L sch Joining sys (Declared stat prepared) last = None}.

(** Follow the selected indexed transition; accessibility supplies no executable fuel. *)
Definition call_join_body (prepared : sys_index X C) (start : Engine.t X C A)
    (next : forall last, engine_rel EX EC L sch Joining sys (Declared stat prepared) last start ->
      call_finished prepared last) : call_finished prepared start.
Proof.
  destruct (engine_step EX EC L sch Joining sys (Declared stat prepared) start)
    as [next_state|] eqn:Hstep.
  - pose (result := next next_state Hstep).
    refine (exist _ (proj1_sig result) _).
    destruct (proj2_sig result) as [n [Hrun Hempty]].
    exists (Datatypes.S n); split; [|exact Hempty].
    exact (engine_steps_cons EX EC L sch Joining sys (Declared stat prepared)
      n start next_state _ Hstep Hrun).
  - refine (exist _ start _); exists 0; split; [constructor|exact Hstep].
Defined.

(** The recursive executor retains the supplied index and its agreement evidence throughout. *)
Definition call_join_execute (prepared : sys_index X C)
    (Hprepared : sys_index_laws EX sys stat prepared) :
    call_finished prepared (initial_state EC sch sys) :=
  Fix_F (call_finished prepared) (call_join_body prepared)
    (proj1 (engine_acc EX EC L sys sch Joining stat prepared HL Hheight Hprepared)).

(** Build the dependency index once before entering the selected recursive executor. *)
Definition call_join_run : call_finished ix (initial_state EC sch sys) :=
  let prepared := index_system EX sys stat in
  call_join_execute prepared (index_system_laws EX sys stat).

(** Read the reached assignment from the final state of the indexed run. *)
Definition call_join_solution : X -> A :=
  lookup EX L (Engine.current (proj1_sig call_join_run)).

(** Empty-queue stability establishes every original constraint, even with weak joins. *)
Lemma call_join_post : post_solution L sys call_join_solution.
Proof.
  destruct (proj2_sig call_join_run) as [n [Hrun Hempty]].
  apply (engine_finished_sound EX EC L sys sch Joining dep _ HL
    (index_system_laws EX sys stat)); [|exact Hempty].
  exact (engine_steps_reachable EX EC L sch Joining sys dep n _ Hrun).
Qed.

(** Every selected update is a raise in the original constraint-run semantics. *)
Lemma call_join_reached : reached EX L sys call_join_solution.
Proof.
  destruct (proj2_sig call_join_run) as [n [Hrun Hempty]].
  destruct Hheight as [Hfinite].
  exact (proj2 (total_join_steps_reached EX EC L HL sch sys stat ix
    (index_system_laws EX sys stat) Hfinite n _ Hrun)).
Qed.

(** Leastness uses the separate least-upper-bound and monotonicity laws. *)
Lemma call_join_least : lub_laws L -> monotone_system L sys ->
  least_solution L sys call_join_solution.
Proof.
  intros Hlub Hmono; apply (reached_least EX L sys _ HL Hlub Hmono).
  - exact call_join_reached.
  - exact call_join_post.
Qed.

(** A completed binary run observes the exact same final assignment as accessibility execution. *)
Lemma call_join_agrees fuel m :
  run_worklist EX EC L sch Joining sys dep fuel = Some m ->
  forall x, call_join_solution x = lookup EX L m x.
Proof.
  intro Hfuel; destruct (proj2_sig call_join_run) as [n [Hrun Hempty]].
  assert (Hcompleted : run_worklist EX EC L sch Joining sys dep (Pos.of_succ_nat n) =
    Some (Engine.current (proj1_sig call_join_run))).
  { apply run_worklist_spec; exists n, (proj1_sig call_join_run); split.
    - rewrite SuccNat2Pos.id_succ; lia.
    - split; [exact Hrun|split; [exact Hempty|reflexivity]]. }
  pose proof (total_completed_runs_unique EX EC L sch Joining sys dep _ _ _ _
    Hcompleted Hfuel) as Heq.
  intro x; unfold call_join_solution; rewrite Heq; reflexivity.
Qed.

End CallJoining.

(** * Actual component phases of the priority worklist *)

Section CallQueueOrder.
Context {X C A : Type} (EC : encoding C) (sys : System.t X C A) (sch : scheduler X).

(** Every pending row is keyed by the component of the unknown it updates. *)
Definition call_queue_ranked (q : PQueue.t C) : Prop :=
  forall c p, PQueue.priority EC c q = Some p -> p = priority sch (System.target sys c).

(** A phase bound excludes all pending rows in earlier components. *)
Definition call_queue_above (phase : positive) (q : PQueue.t C) : Prop :=
  forall c p, PQueue.priority EC c q = Some p -> (phase <= p)%positive.

(** Adding indexed readers preserves their exact component keys. *)
Lemma call_enqueue_ranked cs q : PQueue.wf EC q -> call_queue_ranked q ->
  call_queue_ranked (enqueue EC sch sys cs q).
Proof.
  revert q; induction cs as [|c cs IH]; intros q Hwf Hrank; [exact Hrank|].
  cbn [enqueue]; apply IH; [apply PQueue.wf_push; exact Hwf|].
  intros d p Hget; destruct (calls_eq_dec EC d c) as [->|Hne].
  - rewrite PQueue.priority_push_same in Hget by exact Hwf.
    destruct (PQueue.priority EC c q) as [old|] eqn:Hold.
    + rewrite (Hrank c old Hold), Pos.min_id in Hget; inversion Hget; reflexivity.
    + inversion Hget; reflexivity.
  - rewrite PQueue.priority_push_other in Hget by assumption; apply Hrank; exact Hget.
Qed.

(** Reader insertion cannot reopen a component below the current phase. *)
Lemma call_enqueue_above phase cs q :
  PQueue.wf EC q -> call_queue_above phase q ->
  (forall c, In c cs -> (phase <= priority sch (System.target sys c))%positive) ->
  call_queue_above phase (enqueue EC sch sys cs q).
Proof.
  revert q; induction cs as [|c cs IH]; intros q Hwf Habove Hcs; [exact Habove|].
  cbn [enqueue]; apply IH.
  - apply PQueue.wf_push; exact Hwf.
  - intros d p Hget; destruct (calls_eq_dec EC d c) as [->|Hne].
    + rewrite PQueue.priority_push_same in Hget by exact Hwf.
      pose proof (Hcs c (or_introl eq_refl)) as Hc.
      destruct (PQueue.priority EC c q) as [old|] eqn:Hold; inversion Hget; subst p.
      * pose proof (Habove c old Hold); apply Pos.min_glb; assumption.
      * exact Hc.
    + rewrite PQueue.priority_push_other in Hget by assumption; apply (Habove d p Hget).
  - intros d Hd; apply Hcs; now right.
Qed.

(** Pop keeps the keys of all remaining rows unchanged. *)
Lemma call_pop_ranked q q' p c :
  PQueue.wf EC q -> call_queue_ranked q -> PQueue.pop EC q = Some (p, c, q') ->
  p = priority sch (System.target sys c) /\ call_queue_ranked q'.
Proof.
  intros Hwf Hrank Hpop.
  destruct (PQueue.pop_min EC q q' p c Hwf Hpop) as [Hget Hmin].
  destruct (PQueue.pop_rest EC q q' p c Hwf Hpop) as [Hnone [Hother Hsize]].
  split; [exact (Hrank c p Hget)|].
  intros d r Hr; destruct (calls_eq_dec EC d c) as [->|Hne].
  - rewrite Hnone in Hr; discriminate.
  - rewrite Hother in Hr by exact Hne; apply Hrank; exact Hr.
Qed.

(** The actual popped priority bounds every row remaining after the pop. *)
Lemma call_pop_above q q' p c :
  PQueue.wf EC q -> PQueue.pop EC q = Some (p, c, q') -> call_queue_above p q'.
Proof.
  intros Hwf Hpop d r Hr.
  destruct (PQueue.pop_min EC q q' p c Hwf Hpop) as [Hget Hmin].
  destruct (PQueue.pop_rest EC q q' p c Hwf Hpop) as [Hnone [Hother Hsize]].
  assert (Hdc : d <> c) by (intro Heq; subst d; rewrite Hnone in Hr; discriminate).
  rewrite Hother in Hr by exact Hdc.
  specialize (Hmin d r Hr); unfold PQueue.before in Hmin; lia.
Qed.

End CallQueueOrder.

Section CallPhases.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (Hheight : inhabited (height L))
  (sys : System.t X C A) (stat : System.static sys)
  (sch : scheduler X).
Local Abbreviation ix := (index_system EX sys stat).
Local Abbreviation dep := (Declared stat ix).
Local Abbreviation step := (engine_step EX EC L sch Joining sys dep).
Hypothesis Hsides : forall c s, Query.sides (System.rhs sys c) s = [].
Hypothesis Horder : forall c x, In c (System.constraints sys) -> In x (deps stat c) ->
  (priority sch x <= priority sch (System.target sys c))%positive.

(** Every successful step stays within its component or advances to a later component. *)
Lemma call_step_phase e e' :
  total_state_valid EX EC sys stat e -> call_queue_ranked EC sys sch (Engine.queue e) ->
  step e = Some e' -> exists p c q,
    PQueue.pop EC (Engine.queue e) = Some (p, c, q) /\
    p = priority sch (System.target sys c) /\
    call_queue_ranked EC sys sch (Engine.queue e') /\
    call_queue_above EC p (Engine.queue e').
Proof.
  intros [Hwf [Hr Hpending]] Hrank Hstep; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|] eqn:Hpop; [|discriminate].
  destruct (call_pop_ranked EC sys sch _ _ _ _ Hwf Hrank Hpop) as [Hp Hrankq].
  pose proof (call_pop_above EC _ _ _ _ Hwf Hpop) as Habove.
  pose proof (PQueue.wf_pop EC _ _ _ _ Hwf Hpop) as Hqwf.
  rewrite run_spec, Hsides in Hstep; cbn [engine_updates fold_left] in Hstep.
  unfold engine_update in Hstep; cbn in Hstep.
  destruct (leb L (Query.eval (System.rhs sys c) (lookup EX L (Engine.current e)))
    (lookup EX L (Engine.current e) (System.target sys c))) eqn:Hbelow.
  - inversion Hstep; subst e'; exists p, c, q; split; [reflexivity|].
    split; [exact Hp|]; split; assumption.
  - inversion Hstep; subst e'; exists p, c, q; split; [reflexivity|].
    split; [exact Hp|]; split.
    + apply call_enqueue_ranked; assumption.
    + apply call_enqueue_above; [exact Hqwf|exact Habove|].
      intros d Hd; apply (readers_agree (index_system_laws EX sys stat)) in Hd.
      rewrite Hp; apply (Horder d _ (proj1 Hd) (proj2 Hd)).
Qed.

(** The initialized priority worklist has exact component keys. *)
Lemma call_initial_ranked : call_queue_ranked EC sys sch (Engine.queue (initial_state EC sch sys)).
Proof.
  apply call_enqueue_ranked; [apply PQueue.wf_empty|].
  intros c p Hget; rewrite PQueue.priority_empty in Hget; discriminate.
Qed.

(** All states on an actual run retain the component keys used by the queue-order proof. *)
Lemma call_steps_ranked n e :
  engine_steps EX EC L sch Joining sys dep n (initial_state EC sch sys) e ->
  total_state_valid EX EC sys stat e /\ call_queue_ranked EC sys sch (Engine.queue e).
Proof.
  intro Hrun; remember (initial_state EC sch sys) as start eqn:Hstart in Hrun.
  revert Hstart; induction Hrun as [e|n a b c Hrun IH Hstep]; intro Hstart.
  - subst e; split; [apply total_initial_valid|exact call_initial_ranked].
  - destruct (IH Hstart) as [Hvalid Hrank]; split.
    + destruct Hheight as [Hfinite].
      exact (total_join_step_valid EX EC L HL sch sys stat ix
        (index_system_laws EX sys stat) Hfinite b c Hvalid Hstep).
    + destruct (call_step_phase b c Hvalid Hrank Hstep)
        as (p & row & q & Hpop & Hp & Hrank' & Habove).
      exact Hrank'.
Qed.

(** Before a later phase runs, every earlier component is already quiescent. *)
Lemma call_phase_quiescent n e phase :
  engine_steps EX EC L sch Joining sys dep n (initial_state EC sch sys) e ->
  call_queue_above EC phase (Engine.queue e) ->
  forall c, In c (System.constraints sys) ->
    (priority sch (System.target sys c) < phase)%positive ->
    constraint_satisfied L sys c (lookup EX L (Engine.current e)).
Proof.
  intros Hrun Habove c Hc Hbefore.
  destruct (call_steps_ranked n e Hrun) as [Hvalid Hrank].
  destruct (engine_reachable_invariant EX EC L sch Joining sys dep HL
    (index_system_laws EX sys stat) e
    (engine_steps_reachable EX EC L sch Joining sys dep n e Hrun)) as [_ [_ Hstable]].
  assert (Hnone : PQueue.priority EC c (Engine.queue e) = None).
  { destruct (PQueue.priority EC c (Engine.queue e)) as [p|] eqn:Hget; [|reflexivity].
    pose proof (Hrank c p Hget); pose proof (Habove c p Hget); exfalso; lia. }
  exact (proj1 (Hstable c Hc Hnone)).
Qed.

(** A pending row either is the row popped now or stays pending after the indexed update. *)
Lemma call_pending_step e e' c :
  total_state_valid EX EC sys stat e -> step e = Some e' ->
  PQueue.priority EC c (Engine.queue e) <> None ->
  (exists p q, PQueue.pop EC (Engine.queue e) = Some (p, c, q)) \/
    PQueue.priority EC c (Engine.queue e') <> None.
Proof.
  intros [Hwf Hrest] Hstep Hpending; unfold engine_step in Hstep.
  destruct (PQueue.pop EC (Engine.queue e)) as [[[p d] q]|] eqn:Hpop; [|discriminate].
  destruct (calls_eq_dec EC c d) as [->|Hne].
  - left; exists p, q; reflexivity.
  - right; destruct (PQueue.pop_rest EC _ _ _ _ Hwf Hpop) as [_ [Hother _]].
    assert (Hpendingq : PQueue.priority EC c q <> None) by (rewrite Hother; assumption).
    rewrite run_spec, Hsides in Hstep; cbn [engine_updates fold_left] in Hstep.
    unfold engine_update in Hstep; cbn in Hstep.
    destruct (leb L (Query.eval (System.rhs sys d) (lookup EX L (Engine.current e)))
      (lookup EX L (Engine.current e) (System.target sys d))) eqn:Hbelow;
      inversion Hstep; subst e'; [exact Hpendingq|].
    apply enqueue_member; [exact (PQueue.wf_pop EC _ _ _ _ Hwf Hpop)|now right].
Qed.

(** Processing records an actual pop on a prefix of the selected transition trace. *)
Definition call_processed (c : C) : Prop :=
  exists n e e' p q,
    engine_steps EX EC L sch Joining sys dep n (initial_state EC sch sys) e /\
    PQueue.pop EC (Engine.queue e) = Some (p, c, q) /\ step e = Some e'.

(** A successful pop always produces a transition, regardless of the row's outputs. *)
Lemma call_step_empty e : step e = None -> PQueue.pop EC (Engine.queue e) = None.
Proof.
  unfold engine_step; destruct (PQueue.pop EC (Engine.queue e)) as [[[p c] q]|];
    [|reflexivity].
  destruct (Query.run (System.rhs sys c) (lookup EX L (Engine.current e))) as [[v rs] ss].
  destruct (engine_updates EX EC L sch Joining sys dep (Engine.recorded e)
    ((System.target sys c, v) :: ss) (Engine.current e, q)); discriminate.
Qed.

(** Every pending item, including a requeued one, is eventually popped before termination. *)
Lemma call_pending_eventually e c : Acc (engine_rel EX EC L sch Joining sys dep) e ->
  total_state_valid EX EC sys stat e -> PQueue.priority EC c (Engine.queue e) <> None ->
  exists n before after p q, engine_steps EX EC L sch Joining sys dep n e before /\
    PQueue.pop EC (Engine.queue before) = Some (p, c, q) /\ step before = Some after.
Proof.
  intro Hacc; induction Hacc as [e Hacc IH]; intros Hvalid Hpending.
  destruct (step e) as [e'|] eqn:Hstep.
  - destruct (call_pending_step e e' c Hvalid Hstep Hpending) as [[p [q Hpop]]|Hnext].
    + exists 0, e, e', p, q; split; [constructor|auto].
    + destruct Hheight as [Hfinite].
      pose proof (total_join_step_valid EX EC L HL sch sys stat ix
        (index_system_laws EX sys stat) Hfinite e e' Hvalid Hstep) as Hvalid'.
      destruct (IH e' Hstep Hvalid' Hnext) as (n & before & after & p & q & Hrun & Hpop & Hend).
      exists (Datatypes.S n), before, after, p, q; split; [|auto].
      exact (engine_steps_cons EX EC L sch Joining sys dep n e e' before Hstep Hrun).
  - exfalso; destruct Hvalid as [Hwf Hrest].
    pose proof (call_step_empty e Hstep) as Hnone.
    apply (PQueue.pop_none EC _ Hwf) in Hnone.
    apply Hpending; exact (proj1 (PQueue.is_empty_spec EC _ Hwf) Hnone c).
Qed.

(** Finite-height accessibility proves fairness of the initialized indexed worklist. *)
Lemma call_join_fair c : In c (System.constraints sys) -> call_processed c.
Proof.
  intro Hc; apply call_pending_eventually.
  - exact (proj1 (engine_acc EX EC L sys sch Joining stat ix HL Hheight
      (index_system_laws EX sys stat))).
  - apply total_initial_valid.
  - apply enqueue_member; [apply PQueue.wf_empty|now left].
Qed.

(** At every actual prefix, a requeued row has a future pop on the same deterministic engine. *)
Lemma call_join_fair_suffix n e c :
  engine_steps EX EC L sch Joining sys dep n (initial_state EC sch sys) e ->
  PQueue.priority EC c (Engine.queue e) <> None ->
  exists m before after p q, engine_steps EX EC L sch Joining sys dep m e before /\
    PQueue.pop EC (Engine.queue before) = Some (p, c, q) /\ step before = Some after.
Proof.
  intros Hrun Hpending; apply call_pending_eventually; [|exact (proj1
    (call_steps_ranked n e Hrun))|exact Hpending].
  assert (Hinherit : forall n a b, engine_steps EX EC L sch Joining sys dep n a b ->
    Acc (engine_rel EX EC L sch Joining sys dep) a ->
    Acc (engine_rel EX EC L sch Joining sys dep) b).
  { intros m a b Hsteps; induction Hsteps as [a|m a b d Hsteps IH Hstep];
      intro Hacc; [exact Hacc|].
    exact (Acc_inv (IH Hacc) Hstep). }
  apply (Hinherit n _ e Hrun).
  exact (proj1 (engine_acc EX EC L sys sch Joining stat ix HL Hheight
    (index_system_laws EX sys stat))).
Qed.

End CallPhases.

(** * Summary solving over prepared target lists *)

(** Pointwise target agreement preserves every ordered summary-row occurrence. *)
Lemma call_summary_agrees {S F P A} (cv : calls_view S F P) (sp : summary_spec F P A)
    (left right : P -> list F) :
  (forall p, left p = right p) -> summary_system cv left sp = summary_system cv right sp.
Proof.
  intro Htargets; unfold summary_system; f_equal; f_equal.
  apply flat_map_ext; intro f; apply flat_map_ext; intro p; rewrite Htargets; reflexivity.
Qed.

(** Pointwise target agreement also preserves every raw outgoing call-edge list. *)
Lemma call_out_agrees {S F P} (cv : calls_view S F P) (left right : P -> list F) :
  (forall p, left p = right p) -> forall f,
  Graph.out (call_graph cv left) f = Graph.out (call_graph cv right) f.
Proof.
  intros Htargets f; apply flat_map_ext; intro p; rewrite Htargets; reflexivity.
Qed.

(** Caching target lists preserves the full raw-graph well-formedness premise. *)
Lemma call_prepared_graph_wf {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve :
  graph_wf (call_graph cv resolve) ->
  graph_wf (call_graph cv (indexed_targets (prepare_calls EF EP cv resolve))).
Proof.
  intro Hwf; constructor.
  - exact (nodes_nodup Hwf).
  - exact (entries_in Hwf).
  - intros f e He; rewrite (call_out_agrees cv _ resolve
      (prepare_calls_targets EF EP cv resolve) f) in He.
    exact (out_source Hwf f e He).
  - intros f e Hf He; rewrite (call_out_agrees cv _ resolve
      (prepare_calls_targets EF EP cv resolve) f) in He.
    exact (out_target_in Hwf f e Hf He).
Qed.

(** Accepted listed graphs use the indexed SCC run; rejection selects the original total solver. *)
Definition solve_scc_summaries {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) : F -> A :=
  let targets := indexed_targets (prepare_calls EF EP cv resolve) in
  let graph := call_graph cv targets in
  if call_listed_check EF graph then
    call_join_solution EF (summary_constraint_encoding EF EP) (slat sp) HL Hheight
      (summary_system cv targets sp) (summary_static cv targets sp) (call_scc_scheduler EF graph)
  else proj1_sig (solve_total EF (summary_constraint_encoding EF EP) (slat sp) HL
    (Scheduler (fun _ => 1%positive) (fun _ => false)) Joining
    (summary_system cv resolve sp) (summary_static cv resolve sp) Hheight).

(** The summary run satisfies the retained equations under the full raw graph premise. *)
Theorem solve_scc_summaries_post {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) ->
  post_solution (slat sp) (summary_system cv resolve sp)
    (solve_scc_summaries EF EP cv resolve sp HL Hheight).
Proof.
  intros Hwf; unfold solve_scc_summaries.
  rewrite call_listed_check_complete by (apply call_prepared_graph_wf; exact Hwf).
  rewrite <- (call_summary_agrees cv sp _ resolve (prepare_calls_targets EF EP cv resolve)).
  apply call_join_post.
Qed.

(** Least-upper-bound laws and monotonicity make the reached summary solution least. *)
Theorem solve_scc_summaries_least {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) -> lub_laws (slat sp) ->
  monotone_system (slat sp) (summary_system cv resolve sp) ->
  least_solution (slat sp) (summary_system cv resolve sp)
    (solve_scc_summaries EF EP cv resolve sp HL Hheight).
Proof.
  intros Hwf Hlub Hmono; unfold solve_scc_summaries.
  rewrite call_listed_check_complete by (apply call_prepared_graph_wf; exact Hwf).
  rewrite <- (call_summary_agrees cv sp _ resolve (prepare_calls_targets EF EP cv resolve))
    in Hmono |- *.
  apply call_join_least; assumption.
Qed.

(** The computed summary covers every step while its function is active, including callees. *)
Theorem solve_scc_summaries_sound {S O F P A} (m : semantics S O)
    (EF : encoding F) (EP : encoding P) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) (sc : step_cover S O A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) -> calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) ->
    step_covers sc (solve_scc_summaries EF EP cv resolve sp HL Hheight f) s l s'.
Proof.
  intros Hwf Hcalls Hsummary; apply (summary_sound m cv resolve sp sc _ Hcalls Hsummary).
  apply solve_scc_summaries_post; exact Hwf.
Qed.

(** Every static summary dependency is a callee in the same or an earlier component. *)
Lemma call_summary_order {S F P A} (EF : encoding F) (cv : calls_view S F P)
    resolve (sp : summary_spec F P A) : graph_wf (call_graph cv resolve) ->
  forall c x, In c (System.constraints (summary_system cv resolve sp)) ->
    In x (deps (summary_static cv resolve sp) c) ->
    (priority (call_scc_scheduler EF (call_graph cv resolve)) x <=
      priority (call_scc_scheduler EF (call_graph cv resolve))
        (System.target (summary_system cv resolve sp) c))%positive.
Proof.
  intros Hwf [f|p g] x Hrow Hdep; [contradiction|].
  destruct Hdep as [<-|Hbad]; [|contradiction].
  apply in_app_or in Hrow; destruct Hrow as [Hlocal|Hcall].
  - apply in_map_iff in Hlocal; destruct Hlocal as [f [Hbad Hf]]; discriminate.
  - apply in_flat_map in Hcall; destruct Hcall as [f [Hf Hcall]].
    apply in_flat_map in Hcall; destruct Hcall as [q [Hq Hcall]].
    apply in_map_iff in Hcall; destruct Hcall as [h [Heq Hh]]; inversion Heq; subst q h.
    pose proof (call_graph_edge cv resolve f p g Hq Hh) as Hedge.
    pose proof (out_source Hwf f (CallEdge p g) Hedge) as Hsource.
    cbn in Hsource |- *; rewrite Hsource.
    exact (call_scc_priority EF _ f _ Hwf Hf Hedge).
Qed.

(** The selected SCC run processes every retained summary row on an actual finite prefix. *)
Lemma call_summary_fair {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) ->
  forall c, In c (System.constraints (summary_system cv resolve sp)) ->
    call_processed EF (summary_constraint_encoding EF EP) (slat sp)
      (summary_system cv resolve sp) (summary_static cv resolve sp)
      (call_scc_scheduler EF (call_graph cv resolve)) c.
Proof.
  intros Hwf c Hc; apply (call_join_fair EF _ _ HL Hheight).
  - intros [f|p g] s; reflexivity.
  - exact Hc.
Qed.

(** Consecutive successful pops cannot move from a caller component back to a callee component. *)
Lemma call_summary_phase_order {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp)))
    n e e' p c q p' c' q' :
  let sys := summary_system cv resolve sp in
  let stat := summary_static cv resolve sp in
  let sch := call_scc_scheduler EF (call_graph cv resolve) in
  let EC := summary_constraint_encoding EF EP in
  let dep := Declared stat (index_system EF sys stat) in
  graph_wf (call_graph cv resolve) ->
  engine_steps EF EC (slat sp) sch Joining sys dep n (initial_state EC sch sys) e ->
  PQueue.pop EC (Engine.queue e) = Some (p, c, q) ->
  engine_step EF EC (slat sp) sch Joining sys dep e = Some e' ->
  PQueue.pop EC (Engine.queue e') = Some (p', c', q') -> (p <= p')%positive.
Proof.
  cbn zeta; intros Hwf Hrun Hpop Hstep Hpop'.
  pose (Hsides := fun (c : summary_constraint F P) (s : F -> A) =>
    match c as row return Query.sides (System.rhs (summary_system cv resolve sp) row) s = [] with
    | SLocal _ => eq_refl
    | SCall _ _ => eq_refl
    end).
  pose (Horder := call_summary_order EF cv resolve sp Hwf).
  destruct (call_steps_ranked EF _ _ HL Hheight _ _ _ Hsides Horder n e Hrun)
    as [Hvalid Hrank].
  destruct (call_step_phase EF _ _ _ _ _ Hsides Horder e e' Hvalid Hrank Hstep)
    as (r & row & rest & Hpopr & Hr & Hrank' & Habove).
  rewrite Hpop in Hpopr; inversion Hpopr; subst r row rest.
  destruct Hheight as [Hfinite].
  pose proof (total_join_step_valid EF _ _ HL _ _ _ _ (index_system_laws EF _ _)
    Hfinite e e' Hvalid Hstep) as [Hwf' Hrest].
  destruct (PQueue.pop_min _ _ _ _ _ Hwf' Hpop') as [Hget Hmin].
  exact (Habove c' p' Hget).
Qed.

(** * Bounded contexts and their reachable graph *)

(** Reachable contexts start at roots and push the latest resolved call site. *)
Inductive reachable_context {S F P} (cv : calls_view S F P) (resolve : P -> list F)
    (k : nat) : F * list P -> Prop :=
  | context_root : forall f, In f (roots cv) -> reachable_context cv resolve k (f, [])
  | context_call : forall f c p g, reachable_context cv resolve k (f, c) ->
      In p (sites_of cv f) -> In g (resolve p) ->
      reachable_context cv resolve k (g, push_ctx k p c).

(** Enumerated bounded contexts use only listed sites and never exceed their bound. *)
Lemma call_contexts_shape {P} (sites : list P) k c :
  In c (calls_contexts sites k) <-> length c <= k /\ incl c sites.
Proof.
  split; [|intros [Hlen Hsites]; apply calls_contexts_complete; assumption].
  revert c; induction k as [|k IH]; intros c Hin.
  - destruct Hin as [<-|Hbad]; [split; [cbn; lia|intros p Hp; contradiction]|contradiction].
  - destruct Hin as [<-|Hin].
    + split; [cbn; lia|intros p Hp; contradiction].
    + apply in_flat_map in Hin; destruct Hin as [p [Hp Hin]].
      apply in_map_iff in Hin; destruct Hin as [rest [<- Hrest]].
      destruct (IH rest Hrest) as [Hlen Hsites]; split; [cbn; lia|].
      intros q [<-|Hq]; [exact Hp|apply Hsites; exact Hq].
Qed.

(** Context keys combine the function and the exact bounded list of site identities. *)
Definition call_context_encoding {F P} (EF : encoding F) (EP : encoding P) :
    encoding (F * list P) := pair_encoding EF (list_encoding EP).

(** The finite universe deduplicates keys, without changing resolver or argument lists. *)
Definition call_context_nodes {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) : list (F * list P) :=
  distinct_unknowns (call_context_encoding EF EP)
    (flat_map (fun f => map (fun c => (f, c))
      (calls_contexts (flat_map (sites_of cv) (functions cv)) k)) (functions cv)).

(** Universe membership expresses exactly listed functions and bounded listed-site contexts. *)
Lemma call_context_nodes_spec {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) f c :
  In (f, c) (call_context_nodes EF EP k cv) <->
    In f (functions cv) /\ length c <= k /\ incl c (flat_map (sites_of cv) (functions cv)).
Proof.
  unfold call_context_nodes; rewrite distinct_unknowns_spec, in_flat_map.
  split.
  - intros [g [Hg Hin]]; apply in_map_iff in Hin; destruct Hin as [d [Heq Hd]].
    inversion Heq; subst g d; split; [exact Hg|apply call_contexts_shape; exact Hd].
  - intros [Hf Hc]; exists f; split; [exact Hf|].
    apply in_map; apply call_contexts_shape; exact Hc.
Qed.

(** Context edges retain their originating context, site and callee. *)
Definition call_context_graph {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : Graph.t (F * list P) ((F * list P) * (P * F)) :=
  {| Graph.entries := map (fun f => (f, [])) (roots cv);
     Graph.nodes := call_context_nodes EF EP k cv;
     Graph.out := fun x => flat_map (fun p => map (fun g => (x, (p, g))) (resolve p))
       (sites_of cv (fst x));
     Graph.source := fst;
     Graph.target := fun e => (snd (snd e), push_ctx k (fst (snd e)) (snd (fst e))) |}.

(** Context adjacency records exactly a site occurrence and one of its resolved callees. *)
Lemma call_context_edge {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve x y p g :
  In (y, (p, g)) (Graph.out (call_context_graph EF EP k cv resolve) x) <->
    y = x /\ In p (sites_of cv (fst x)) /\ In g (resolve p).
Proof.
  cbn [call_context_graph Graph.out]; rewrite in_flat_map; split.
  - intros [q [Hq Hin]]; apply in_map_iff in Hin; destruct Hin as [h [Heq Hh]].
    inversion Heq; subst y q h; auto.
  - intros [-> [Hp Hg]]; exists p; split; [exact Hp|].
    apply in_map_iff; exists g; split; [reflexivity|exact Hg].
Qed.

(** Every contextual edge stays in the finite bounded universe on a well-formed raw call graph. *)
Lemma call_context_graph_wf {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : graph_wf (call_graph cv resolve) ->
  graph_wf (call_context_graph EF EP k cv resolve).
Proof.
  intro Hwf; constructor.
  - apply distinct_unknowns_nodup.
  - intros [f c] Hin; apply in_map_iff in Hin; destruct Hin as [g [Heq Hg]].
    inversion Heq; subst g c; apply call_context_nodes_spec; split.
    + exact (entries_in Hwf f Hg).
    + split; [cbn; lia|intros p Hp; contradiction].
  - intros x [y [p g]] Hin; apply call_context_edge in Hin; exact (proj1 Hin).
  - intros [f c] [[h d] [p g]] Hx He; apply call_context_edge in He.
    destruct He as [Heq [Hp Hg]]; inversion Heq; subst h d.
    apply call_context_nodes_spec in Hx; destruct Hx as [Hf [Hlen Hsites]].
    apply call_context_nodes_spec; split.
    + exact (out_target_in Hwf f (CallEdge p g) Hf (call_graph_edge cv resolve f p g Hp Hg)).
    + split; [apply Nat.le_trans with (m := k); [apply firstn_le_length|lia]|].
      intros q Hq.
      assert (Hfull : In q (p :: c)).
      { rewrite <- (firstn_skipn k (p :: c)); apply in_or_app; now left. }
      destruct Hfull as [<-|Hqfull].
      * apply in_flat_map; exists f; auto.
      * apply Hsites; exact Hqfull.
Qed.

(** The inductive context relation is exactly reachability in the context-edge graph. *)
Lemma call_context_reachable {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve x :
  reachable_context cv resolve k x <-> reachable (call_context_graph EF EP k cv resolve) x.
Proof.
  split.
  - intro Hreach; induction Hreach as [f Hroot|f c p g Hreach IH Hp Hg].
    + apply reachable_entry, in_map_iff; exists f; split; [reflexivity|exact Hroot].
    + apply (@reachable_step _ _ (call_context_graph EF EP k cv resolve) ((f, c), (p, g)));
        [exact IH|].
      apply call_context_edge; auto.
  - intro Hreach; induction Hreach as [x Hroot|[[f c] [p g]] Hreach IH He].
    + apply in_map_iff in Hroot; destruct Hroot as [f [<- Hf]]; apply context_root; exact Hf.
    + apply call_context_edge in He; destruct He as [_ [Hp Hg]].
      exact (context_call cv resolve k f c p g IH Hp Hg).
Qed.

(** One search from the roots prepares the reachable context list. *)
Definition call_reachable_nodes {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : list (F * list P) :=
  let graph := call_scc_graph (call_context_encoding EF EP)
    (call_context_graph EF EP k cv resolve) in
  distinct_unknowns (call_context_encoding EF EP)
    (preorder (dfs (prepare (call_context_encoding EF EP) graph) FinSet.empty
      (Graph.entries graph))).

(** Normalizing target adjacency preserves root reachability on well-formed raw graphs. *)
Lemma call_scc_reachable {X E} (EX : encoding X) (g : Graph.t X E) x :
  graph_wf g -> (reachable (call_scc_graph EX g) x <-> reachable g x).
Proof.
  intro Hwf; rewrite !reachable_iff_path; split; intros [root [es [Hroot Hpath]]].
  - destruct (call_scc_path_backward EX g root es x Hwf Hpath) as [raw Hraw].
    exists root, raw; auto.
  - destruct (call_scc_path_forward EX g root es x Hwf (entries_in Hwf root Hroot) Hpath)
      as [edges Hedges].
    exists root, edges; auto.
Qed.

(** Search membership is exactly the unchanged inductive reachable-context contract. *)
Lemma call_reachable_nodes_spec {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve x :
  graph_wf (call_graph cv resolve) ->
  (In x (call_reachable_nodes EF EP k cv resolve) <-> reachable_context cv resolve k x).
Proof.
  intro Hwf; unfold call_reachable_nodes; rewrite distinct_unknowns_spec.
  set (EX := call_context_encoding EF EP).
  set (raw := call_context_graph EF EP k cv resolve).
  set (graph := call_scc_graph EX raw).
  assert (Hraw : graph_wf raw) by (apply call_context_graph_wf; exact Hwf).
  pose proof (call_scc_ready EX raw Hraw) as Hready.
  destruct (dfs_exact EX graph (prepare EX graph) x (Graph.entries graph) FinSet.empty
    Hready (entries_in (proj1 Hready))) as [_ [_ [_ Hmember]]].
  rewrite Hmember, reachable_dfs by exact Hready.
  change (reachable (call_scc_graph EX raw) x <-> reachable_context cv resolve k x).
  rewrite (call_scc_reachable EX raw x Hraw); symmetry; apply call_context_reachable.
Qed.

(** Reuse the prepared reachable list as the node set of the dependency-closed context graph. *)
Definition call_reachable_graph {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : Graph.t (F * list P) ((F * list P) * (P * F)) :=
  let raw := call_context_graph EF EP k cv resolve in
  {| Graph.entries := Graph.entries raw;
     Graph.nodes := call_reachable_nodes EF EP k cv resolve;
     Graph.out := Graph.out raw;
     Graph.source := Graph.source raw;
     Graph.target := Graph.target raw |}.

(** Restricting to the once-built reachable context list leaves every outgoing dependency inside. *)
Lemma call_reachable_graph_wf {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : graph_wf (call_graph cv resolve) ->
  graph_wf (call_reachable_graph EF EP k cv resolve).
Proof.
  intro Hwf; pose proof (call_context_graph_wf EF EP k cv resolve Hwf) as Hraw; constructor.
  - apply distinct_unknowns_nodup.
  - intros x Hroot; apply call_reachable_nodes_spec; [exact Hwf|].
    apply (proj2 (call_context_reachable EF EP k cv resolve x)), reachable_entry; exact Hroot.
  - exact (out_source Hraw).
  - intros x e Hx He; apply call_reachable_nodes_spec; [exact Hwf|].
    apply (proj2 (call_context_reachable EF EP k cv resolve _)).
    apply (@reachable_step _ _ (call_context_graph EF EP k cv resolve) e).
    + rewrite (out_source Hraw x e He).
      apply (proj1 (call_context_reachable EF EP k cv resolve _)).
      exact (proj1 (call_reachable_nodes_spec EF EP k cv resolve x Hwf) Hx).
    + rewrite (out_source Hraw x e He); exact He.
Qed.

(** * Restriction and extension of contextual solutions *)

(** Keep exactly the original rows whose targets belong to the prepared reachable set. *)
Definition call_restrict {X C A} (EX : encoding X) (region : FinSet.t X)
    (sys : System.t X C A) : System.t X C A :=
  {| System.constraints := filter (fun c => FinSet.mem EX (System.target sys c) region)
       (System.constraints sys);
     System.target := System.target sys;
     System.rhs := System.rhs sys |}.

(** Filtering rows preserves their static read and side declarations unchanged. *)
Definition call_restrict_static {X C A} (EX : encoding X) (region : FinSet.t X)
    (sys : System.t X C A) (stat : System.static sys) :
    System.static (call_restrict EX region sys).
Proof.
  refine {| System.deps := deps stat;
            System.side_targets := side_targets stat |}.
  - exact (System.reads_within stat).
  - exact (System.sides_within stat).
Defined.

(** A post-solution of all rows remains a post-solution after target restriction. *)
Lemma call_restrict_post {X C A} (EX : encoding X) region (sys : System.t X C A)
    (L : lattice A) sigma : post_solution L sys sigma ->
  post_solution L (call_restrict EX region sys) sigma.
Proof.
  intros Hpost c Hc; apply filter_In in Hc; apply Hpost; exact (proj1 Hc).
Qed.

(** Monotonicity of retained rows is inherited from the original system. *)
Lemma call_restrict_monotone {X C A} (EX : encoding X) region (sys : System.t X C A)
    (L : lattice A) : monotone_system L sys ->
  monotone_system L (call_restrict EX region sys).
Proof.
  intros Hmono c Hc; apply filter_In in Hc; apply Hmono; exact (proj1 Hc).
Qed.

Section CallRestriction.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (Hheight : inhabited (height L))
  (sys : System.t X C A) (stat : System.static sys) (sch : scheduler X) (region : FinSet.t X).
Local Abbreviation sub := (call_restrict EX region sys).
Local Abbreviation substat := (call_restrict_static EX region sys stat).
Local Abbreviation answer := (call_join_solution EX EC L HL Hheight sub substat sch).
Hypothesis Hsides : forall c s, Query.sides (System.rhs sys c) s = [].
Hypothesis Hclosed : forall c, In c (System.constraints sys) ->
  FinSet.mem EX (System.target sys c) region = true ->
  forall x, In x (deps stat c) -> FinSet.mem EX x region = true.

(** Combining the reached restricted answer with an outer post-solution satisfies all rows. *)
Lemma call_restrict_extension (sigma : X -> A) :
  lub_laws L -> monotone_system L sys -> post_solution L sys sigma ->
  post_solution L sys (fun x => if FinSet.mem EX x region then answer x else sigma x).
Proof.
  intros Hlub Hmono Hsigma.
  assert (Hbelow : fun_leb L answer sigma).
  { apply (reached_below EX L sub _ _ HL Hlub (call_restrict_monotone EX region sys L Hmono)).
    - apply call_restrict_post; exact Hsigma.
    - apply call_join_reached. }
  intros c Hc; split; [|rewrite Hsides; intros x a Hbad; contradiction].
  destruct (FinSet.mem EX (System.target sys c) region) eqn:Htarget.
  - pose proof (call_join_post EX EC L HL Hheight sub substat sch c
      (proj2 (filter_In _ _ _) (conj Hc Htarget))) as [Hpost Hside].
    destruct (query_determined (System.rhs sys c) answer
      (fun x => if FinSet.mem EX x region then answer x else sigma x)) as [Heval Hrest].
    + intros x Hread; rewrite (Hclosed c Hc Htarget x (System.reads_within stat c answer x Hread)).
      reflexivity.
    + rewrite <- Heval; exact Hpost.
  - eapply (leb_trans HL); [apply (proj1 (Hmono c Hc))|exact (proj1 (Hsigma c Hc))].
    intro x; destruct (FinSet.mem EX x region); [apply Hbelow|apply (leb_refl HL)].
Qed.

(** Restriction agrees with every original least solution at each dependency-closed retained key. *)
Lemma call_restrict_least_agrees (sigma : X -> A) :
  lub_laws L -> monotone_system L sys -> least_solution L sys sigma ->
  forall x, FinSet.mem EX x region = true -> equivalent L (answer x) (sigma x).
Proof.
  intros Hlub Hmono [Hpost Hleast] x Hx; split.
  - apply (reached_below EX L sub _ _ HL Hlub (call_restrict_monotone EX region sys L Hmono)).
    + apply call_restrict_post; exact Hpost.
    + apply call_join_reached.
  - specialize (Hleast _ (call_restrict_extension sigma Hlub Hmono Hpost) x).
    cbn beta in Hleast; rewrite Hx in Hleast; exact Hleast.
Qed.

End CallRestriction.

(** The region index is built once from the prepared reachable graph's node list. *)
Definition call_context_region {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve : FinSet.t (F * list P) :=
  FinSet.of_list (call_context_encoding EF EP)
    (Graph.nodes (call_reachable_graph EF EP k cv resolve)).

(** Region-index membership characterizes precisely the inductively reachable contexts. *)
Lemma call_context_region_spec {S F P} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve x : graph_wf (call_graph cv resolve) ->
  (FinSet.mem (call_context_encoding EF EP) x (call_context_region EF EP k cv resolve) = true
    <-> reachable_context cv resolve k x).
Proof.
  intro Hwf; unfold call_context_region; rewrite FinSet.of_list_spec.
  apply call_reachable_nodes_spec; exact Hwf.
Qed.

(** A retained call row identifies a listed source, site and target, including parallel rows. *)
Lemma call_summary_row {S F P A} (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) p g :
  In (SCall p g) (System.constraints (summary_system cv resolve sp)) ->
  exists f, In f (functions cv) /\ In p (sites_of cv f) /\ In g (resolve p).
Proof.
  intro Hrow; apply in_app_or in Hrow; destruct Hrow as [Hlocal|Hcall].
  - apply in_map_iff in Hlocal; destruct Hlocal as [f [Hbad Hf]]; discriminate.
  - apply in_flat_map in Hcall; destruct Hcall as [f [Hf Hcall]].
    apply in_flat_map in Hcall; destruct Hcall as [q [Hq Hcall]].
    apply in_map_iff in Hcall; destruct Hcall as [h [Heq Hh]]; inversion Heq; subst q h.
    exists f; auto.
Qed.

(** Every dependency of a retained contextual row lies in the same prepared reachable region. *)
Lemma call_context_closed {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A) :
  graph_wf (call_graph cv resolve) ->
  forall row, In row (System.constraints (callstring_system k cv resolve sp)) ->
    FinSet.mem (call_context_encoding EF EP)
      (System.target (callstring_system k cv resolve sp) row)
      (call_context_region EF EP k cv resolve) = true ->
    forall x, In x (deps (callstring_static k cv resolve sp) row) ->
      FinSet.mem (call_context_encoding EF EP) x
        (call_context_region EF EP k cv resolve) = true.
Proof.
  intros Hwf [[f|p g] c] Hrow Htarget x Hdep; [contradiction|].
  destruct Hdep as [<-|Hbad]; [|contradiction].
  apply in_flat_map in Hrow; destruct Hrow as [d [Hd Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [row [Heq Hrow]]; inversion Heq; subst row d.
  destruct (call_summary_row cv resolve sp p g Hrow) as [f [Hf [Hp Hg]]].
  pose proof (out_source Hwf f (CallEdge p g) (call_graph_edge cv resolve f p g Hp Hg))
    as Hsource; cbn in Hsource.
  apply (call_context_region_spec EF EP k cv resolve _ Hwf) in Htarget.
  apply (call_context_region_spec EF EP k cv resolve _ Hwf).
  cbn [callstring_system System.target fst snd] in Htarget; rewrite Hsource in Htarget.
  exact (context_call cv resolve k f c p g Htarget Hp Hg).
Qed.

(** The accepted context path solves only the closed reachable rows and returns bottom elsewhere. *)
Definition call_context_solve {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) : F * list P -> A :=
  let EX := call_context_encoding EF EP in
  let EC := pair_encoding (summary_constraint_encoding EF EP) (list_encoding EP) in
  let graph := call_reachable_graph EF EP k cv resolve in
  let region := FinSet.of_list EX (Graph.nodes graph) in
  let sys := callstring_system k cv resolve sp in
  let stat := callstring_static k cv resolve sp in
  let result := call_join_solution EX EC (slat sp) HL Hheight
    (call_restrict EX region sys) (call_restrict_static EX region sys stat)
    (call_scc_scheduler EX graph) in
  fun x => if FinSet.mem EX x region then result x else bot (slat sp).

(** Accepted context solving leaves every key outside its constructed graph exactly bottom. *)
Lemma call_context_solve_outside {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) x :
  FinSet.mem (call_context_encoding EF EP) x (call_context_region EF EP k cv resolve) = false ->
  call_context_solve EF EP k cv resolve sp HL Hheight x = bot (slat sp).
Proof.
  intro Houtside; unfold call_context_solve; fold (call_context_region EF EP k cv resolve).
  rewrite Houtside; reflexivity.
Qed.

(** Rejection returns bottom everywhere; acceptance selects the full reachable-context engine. *)
Definition solve_reachable_callstrings {S F P A} (EF : encoding F) (EP : encoding P)
    (k : nat) (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) : F * list P -> A :=
  let targets := indexed_targets (prepare_calls EF EP cv resolve) in
  if call_listed_check EF (call_graph cv targets) then
    call_context_solve EF EP k cv targets sp HL Hheight
  else fun _ => bot (slat sp).

(** Pointwise resolver agreement preserves all original contextual rows exactly. *)
Lemma call_callstring_agrees {S F P A} k (cv : calls_view S F P) (sp : summary_spec F P A)
    (left right : P -> list F) : (forall p, left p = right p) ->
  callstring_system k cv left sp = callstring_system k cv right sp.
Proof.
  intro Htargets; unfold callstring_system; rewrite (call_summary_agrees cv sp left right Htargets).
  reflexivity.
Qed.

(** Pointwise resolver agreement preserves the unchanged inductive context relation. *)
Lemma call_context_targets_agree {S F P} k (cv : calls_view S F P) (left right : P -> list F) :
  (forall p, left p = right p) -> forall x,
    reachable_context cv left k x -> reachable_context cv right k x.
Proof.
  intros Htargets x Hreach; induction Hreach as [f Hroot|f c p g Hreach IH Hp Hg].
  - apply context_root; exact Hroot.
  - apply (context_call cv right k f c p g IH Hp); rewrite <- Htargets; exact Hg.
Qed.

(** The reachable engine agrees with any original least solution on all reachable contexts. *)
Theorem reachable_callstrings_least {S F P A} (EF : encoding F) (EP : encoding P)
    (k : nat) (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp)))
    (sigma : F * list P -> A) :
  graph_wf (call_graph cv resolve) -> lub_laws (slat sp) ->
  monotone_system (slat sp) (callstring_system k cv resolve sp) ->
  least_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  forall x, reachable_context cv resolve k x ->
    equivalent (slat sp) (solve_reachable_callstrings EF EP k cv resolve sp HL Hheight x)
      (sigma x).
Proof.
  intros Hwf Hlub Hmono Hleast x Hreach; unfold solve_reachable_callstrings.
  pose proof (call_prepared_graph_wf EF EP cv resolve Hwf) as Hprepared.
  rewrite call_listed_check_complete by exact Hprepared.
  set (targets := indexed_targets (prepare_calls EF EP cv resolve)) in *.
  assert (Htargets : forall p, targets p = resolve p) by (apply prepare_calls_targets).
  rewrite <- (call_callstring_agrees k cv sp targets resolve Htargets) in Hmono, Hleast.
  assert (Hregion : FinSet.mem (call_context_encoding EF EP) x
    (call_context_region EF EP k cv targets) = true).
  { apply call_context_region_spec; [exact Hprepared|].
    apply (call_context_targets_agree k cv resolve targets); [intro p; symmetry; apply Htargets|].
    exact Hreach. }
  unfold call_context_solve; fold (call_context_region EF EP k cv targets).
  rewrite Hregion.
  apply (call_restrict_least_agrees _ _ _ HL Hheight).
  - intros [[f|p g] c] s; reflexivity.
  - exact (call_context_closed EF EP k cv targets sp Hprepared).
  - exact Hlub.
  - exact Hmono.
  - exact Hleast.
  - exact Hregion.
Qed.

(** Retained contextual dependencies follow the callee-first SCC order of the reachable graph. *)
Lemma call_context_order {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A) :
  graph_wf (call_graph cv resolve) ->
  let EX := call_context_encoding EF EP in
  let graph := call_reachable_graph EF EP k cv resolve in
  let region := call_context_region EF EP k cv resolve in
  let sys := callstring_system k cv resolve sp in
  let stat := callstring_static k cv resolve sp in
  forall row x, In row (System.constraints (call_restrict EX region sys)) ->
    In x (deps (call_restrict_static EX region sys stat) row) ->
    (priority (call_scc_scheduler EX graph) x <=
      priority (call_scc_scheduler EX graph) (System.target sys row))%positive.
Proof.
  intros Hwf; cbn zeta; intros [[f|p g] c] x Hrow Hdep; [contradiction|].
  destruct Hdep as [<-|Hbad]; [|contradiction].
  apply filter_In in Hrow; destruct Hrow as [Hrow Hregion].
  apply in_flat_map in Hrow; destruct Hrow as [d [Hd Hrow]].
  apply in_map_iff in Hrow; destruct Hrow as [row [Heq Hrow]]; inversion Heq; subst row d.
  destruct (call_summary_row cv resolve sp p g Hrow) as [f [Hf [Hp Hg]]].
  pose proof (out_source Hwf f (CallEdge p g) (call_graph_edge cv resolve f p g Hp Hg))
    as Hsource; cbn in Hsource.
  cbn [callstring_system System.target fst snd] in Hregion |- *; rewrite Hsource in *.
  apply (call_scc_priority (call_context_encoding EF EP)
    (call_reachable_graph EF EP k cv resolve) (f, c) ((f, c), (p, g))).
  - apply call_reachable_graph_wf; exact Hwf.
  - apply FinSet.of_list_spec in Hregion; exact Hregion.
  - apply call_context_edge; auto.
Qed.

(** The actual reachable-context worklist is fair within every callee-first component phase. *)
Lemma call_context_fair {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) ->
  let EX := call_context_encoding EF EP in
  let EC := pair_encoding (summary_constraint_encoding EF EP) (list_encoding EP) in
  let region := call_context_region EF EP k cv resolve in
  let sys := callstring_system k cv resolve sp in
  let stat := callstring_static k cv resolve sp in
  forall row, In row (System.constraints (call_restrict EX region sys)) ->
    call_processed EX EC (slat sp) (call_restrict EX region sys)
      (call_restrict_static EX region sys stat)
      (call_scc_scheduler EX (call_reachable_graph EF EP k cv resolve)) row.
Proof.
  intros Hwf; cbn zeta; intros row Hrow; apply (call_join_fair _ _ _ HL Hheight).
  - intros [[f|p g] c] s; reflexivity.
  - exact Hrow.
Qed.

(** A completed binary probe observes the public accepted summary engine exactly. *)
Lemma call_summary_probe {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) fuel m :
  let targets := indexed_targets (prepare_calls EF EP cv resolve) in
  let sys := summary_system cv targets sp in
  let stat := summary_static cv targets sp in
  let sch := call_scc_scheduler EF (call_graph cv targets) in
  call_listed_check EF (call_graph cv targets) = true ->
  run_worklist EF (summary_constraint_encoding EF EP) (slat sp) sch Joining sys
    (Declared stat (index_system EF sys stat)) fuel = Some m ->
  forall f, solve_scc_summaries EF EP cv resolve sp HL Hheight f = lookup EF (slat sp) m f.
Proof.
  cbn zeta; intros Hcheck Hrun f; unfold solve_scc_summaries; rewrite Hcheck.
  apply call_join_agrees with (fuel := fuel); exact Hrun.
Qed.

(** A completed binary probe observes the accepted reachable engine at each retained context. *)
Lemma call_context_probe {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) fuel m x :
  let targets := indexed_targets (prepare_calls EF EP cv resolve) in
  let EX := call_context_encoding EF EP in
  let EC := pair_encoding (summary_constraint_encoding EF EP) (list_encoding EP) in
  let graph := call_reachable_graph EF EP k cv targets in
  let region := call_context_region EF EP k cv targets in
  let sys := callstring_system k cv targets sp in
  let stat := callstring_static k cv targets sp in
  let sub := call_restrict EX region sys in
  let substat := call_restrict_static EX region sys stat in
  call_listed_check EF (call_graph cv targets) = true ->
  FinSet.mem EX x region = true ->
  run_worklist EX EC (slat sp) (call_scc_scheduler EX graph) Joining sub
    (Declared substat (index_system EX sub substat)) fuel = Some m ->
  solve_reachable_callstrings EF EP k cv resolve sp HL Hheight x = lookup EX (slat sp) m x.
Proof.
  cbn zeta; intros Hcheck Hregion Hrun; unfold solve_reachable_callstrings; rewrite Hcheck.
  unfold call_context_solve; fold (call_context_region EF EP k cv
    (indexed_targets (prepare_calls EF EP cv resolve))); rewrite Hregion.
  apply call_join_agrees with (fuel := fuel); exact Hrun.
Qed.

(** Check rejection selects exactly the generic total joining solver on the original equations. *)
Lemma call_summary_rejected {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  call_listed_check EF (call_graph cv (indexed_targets (prepare_calls EF EP cv resolve))) = false ->
  solve_scc_summaries EF EP cv resolve sp HL Hheight =
    proj1_sig (solve_total EF (summary_constraint_encoding EF EP) (slat sp) HL
      (Scheduler (fun _ => 1%positive) (fun _ => false)) Joining
      (summary_system cv resolve sp) (summary_static cv resolve sp) Hheight).
Proof.
  intro Hcheck; unfold solve_scc_summaries; rewrite Hcheck; reflexivity.
Qed.

(** Check rejection makes every reachable-callstring query bottom, including root queries. *)
Lemma call_context_rejected {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  call_listed_check EF (call_graph cv (indexed_targets (prepare_calls EF EP cv resolve))) = false ->
  forall x, solve_reachable_callstrings EF EP k cv resolve sp HL Hheight x = bot (slat sp).
Proof.
  intros Hcheck x; unfold solve_reachable_callstrings; rewrite Hcheck; reflexivity.
Qed.

(** Earlier summary components are quiescent when the actual queue enters a later phase. *)
Lemma call_summary_quiescent {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) n e phase :
  let sys := summary_system cv resolve sp in
  let stat := summary_static cv resolve sp in
  let sch := call_scc_scheduler EF (call_graph cv resolve) in
  let EC := summary_constraint_encoding EF EP in
  graph_wf (call_graph cv resolve) ->
  engine_steps EF EC (slat sp) sch Joining sys (Declared stat (index_system EF sys stat))
    n (initial_state EC sch sys) e -> call_queue_above EC phase (Engine.queue e) ->
  forall row, In row (System.constraints sys) ->
    (priority sch (System.target sys row) < phase)%positive ->
    constraint_satisfied (slat sp) sys row (lookup EF (slat sp) (Engine.current e)).
Proof.
  cbn zeta; intros Hwf; apply (call_phase_quiescent EF _ _ HL Hheight).
  - intros [f|p g] s; reflexivity.
  - exact (call_summary_order EF cv resolve sp Hwf).
Qed.

(** The reachable-context engine also finishes earlier components before advancing phases. *)
Lemma call_context_quiescent {S F P A} (EF : encoding F) (EP : encoding P)
    k (cv : calls_view S F P) resolve (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) n e phase :
  let EX := call_context_encoding EF EP in
  let EC := pair_encoding (summary_constraint_encoding EF EP) (list_encoding EP) in
  let graph := call_reachable_graph EF EP k cv resolve in
  let region := call_context_region EF EP k cv resolve in
  let sys := call_restrict EX region (callstring_system k cv resolve sp) in
  let stat := call_restrict_static EX region (callstring_system k cv resolve sp)
    (callstring_static k cv resolve sp) in
  let sch := call_scc_scheduler EX graph in
  graph_wf (call_graph cv resolve) ->
  engine_steps EX EC (slat sp) sch Joining sys (Declared stat (index_system EX sys stat))
    n (initial_state EC sch sys) e -> call_queue_above EC phase (Engine.queue e) ->
  forall row, In row (System.constraints sys) ->
    (priority sch (System.target sys row) < phase)%positive ->
    constraint_satisfied (slat sp) sys row (lookup EX (slat sp) (Engine.current e)).
Proof.
  cbn zeta; intros Hwf; apply (call_phase_quiescent _ _ _ HL Hheight).
  - intros [[f|p g] c] s; reflexivity.
  - exact (call_context_order EF EP k cv resolve sp Hwf).
Qed.
