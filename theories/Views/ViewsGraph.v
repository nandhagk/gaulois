(** * Graph views and dense constraint systems

    Graph views classify semantic steps and generate forward and backward edge constraints.
    For example, one edge contributes one query reading its source in the forward system.
    Builds on: ViewsSemantics, GraphCore, FixpointSystem and FixpointCycles. *)

From Stdlib Require Import List Bool Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCycles.
From Gaulois.Views Require Import ViewsSemantics.
Import List.ListNotations.

(** A graph view maps states to nodes and classifies taken and stationary steps. *)
Record graph_view (S O N E : Type) : Type := GraphView {
  cfg : Graph.t N E;
  point : S -> N;
  taken : S -> list O -> S -> E -> Prop;
  stays : S -> list O -> S -> Prop
}.

Arguments GraphView {S O N E}.
Arguments cfg {S O N E}.
Arguments point {S O N E}.
Arguments taken {S O N E}.
Arguments stays {S O N E}.

(** View laws connect reachable semantic steps to a well-formed graph. *)
Record graph_view_laws {S O N E} (m : semantics S O) (gv : graph_view S O N E) : Prop := {
  cfg_wf : graph_wf (cfg gv);
  entry_points : forall s, initial m s -> In (point gv s) (Graph.entries (cfg gv));
  edge_covers : forall s l s', reachable_state m s -> step m s l s' ->
    stays gv s l s' \/ exists e, taken gv s l s' e;
  taken_edge : forall s l s' e, reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    In e (Graph.out (cfg gv) (point gv s)) /\ Graph.target (cfg gv) e = point gv s';
  stays_point : forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
    point gv s' = point gv s
}.

Arguments cfg_wf {S O N E m gv}.
Arguments entry_points {S O N E m gv}.
Arguments edge_covers {S O N E m gv}.
Arguments taken_edge {S O N E m gv}.
Arguments stays_point {S O N E m gv}.

(** Enumerating edges traverses the finite node list once. *)
Definition edges_of {N E} (g : Graph.t N E) : list E :=
  flat_map (Graph.out g) (Graph.nodes g).

(** Dense rows are either node seeds or edge transfers. *)
Inductive dense_constraint (N E : Type) : Type :=
  | Seed (n : N)
  | Flow (e : E).

Arguments Seed {N E}.
Arguments Flow {N E}.

(** Dense row codes are the corresponding tagged sum codes. *)
Definition dense_constraint_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (dense_constraint N E).
Proof.
  refine (Encoding _ (fun c => encode (sum_encoding EN EE)
    (match c with
    | Seed n => inl n
    | Flow e => inr e
    end)) _).
  intros [n|e] [n'|e'] Hcode; apply (encode_injective (sum_encoding EN EE)) in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** Forward rows seed entries and propagate facts from each edge's source to its target. *)
Definition forward_system {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A) :
    System.t N (dense_constraint N E) A :=
  {| System.constraints := map Seed (Graph.entries g) ++ map Flow (edges_of g);
     System.target := fun c =>
       match c with
       | Seed n => n
       | Flow e => Graph.target g e
       end;
     System.rhs := fun c =>
       match c with
       | Seed n => Query.Ret (init n)
       | Flow e => Query.Ask (Graph.source g e) (fun a => Query.Ret (ft e a))
       end |}.

(** Forward rows read only edge sources and have no side contributions. *)
Definition forward_static {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A) :
    System.static (forward_system g init ft).
Proof.
  refine {| System.deps := fun c =>
              match c with
              | Seed _ => []
              | Flow e => [Graph.source g e]
              end;
            System.side_targets := fun _ => [] |}.
  - intros [n|e] sigma; apply incl_refl.
  - intros [n|e] sigma; apply incl_refl.
Defined.

(** Backward rows seed all nodes and propagate target needs back to each edge's source. *)
Definition backward_system {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A) :
    System.t N (dense_constraint N E) A :=
  {| System.constraints := map Seed (Graph.nodes g) ++ map Flow (edges_of g);
     System.target := fun c =>
       match c with
       | Seed n => n
       | Flow e => Graph.source g e
       end;
     System.rhs := fun c =>
       match c with
       | Seed n => Query.Ret (exitf n)
       | Flow e => Query.Ask (Graph.target g e) (fun a => Query.Ret (bt e a))
       end |}.

(** Backward rows read only edge targets and have no side contributions. *)
Definition backward_static {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A) :
    System.static (backward_system g exitf bt).
Proof.
  refine {| System.deps := fun c =>
              match c with
              | Seed _ => []
              | Flow e => [Graph.target g e]
              end;
            System.side_targets := fun _ => [] |}.
  - intros [n|e] sigma; apply incl_refl.
  - intros [n|e] sigma; apply incl_refl.
Defined.

(** A widening predicate meets every nonempty graph cycle at an edge source. *)
Definition meets_every_cycle {N E} (g : Graph.t N E) (W : N -> bool) : Prop :=
  forall v es, es <> nil -> path g v es v ->
    exists e, In e es /\ W (Graph.source g e) = true.

(** Edge histories retain taken edges in execution order and omit stays. *)
Inductive run_edges {S O N E} (m : semantics S O) (gv : graph_view S O N E) :
    S -> list E -> S -> Prop :=
  | run_nil : forall s, run_edges m gv s nil s
  | run_cons : forall s l s' e es t, step m s l s' -> taken gv s l s' e ->
      run_edges m gv s' es t -> run_edges m gv s (e :: es) t
  | run_stay : forall s l s' es t, step m s l s' -> stays gv s l s' ->
      run_edges m gv s' es t -> run_edges m gv s es t.

Arguments run_nil {S O N E m gv}.
Arguments run_cons {S O N E m gv}.
Arguments run_stay {S O N E m gv}.

(** The last writing edge overwrites the earlier history's writer. *)
Definition last_writer {E X} (writes : E -> X -> bool) (es : list E) (x : X) : option E :=
  fold_left (fun r e => if writes e x then Some e else r) es None.

(** Arrival counts reset on entry and count back edges after the most recent reset. *)
Definition arrivals_since {E} (enter back : E -> bool) (es : list E) : nat :=
  fold_left (fun n e => if enter e then 0 else if back e then S n else n) es 0.

(** * Dense solution characterizations *)

(** A forward post-solution is exactly the entry bounds and the edge transfer bounds. *)
Theorem forward_post_solution_iff {N E A} (g : Graph.t N E) (L : lattice A) (init : N -> A)
    (ft : E -> A -> A) (sigma : N -> A) :
  post_solution L (forward_system g init ft) sigma <->
  (forall n, In n (Graph.entries g) -> leb L (init n) (sigma n) = true) /\
  (forall e, In e (edges_of g) ->
    leb L (ft e (sigma (Graph.source g e))) (sigma (Graph.target g e)) = true).
Proof.
  split.
  - intro Hpost; split.
    + intros n Hn; apply (proj1 (Hpost (Seed n) (in_or_app _ _ _ (or_introl (in_map _ _ _ Hn))))).
    + intros e He; apply (proj1 (Hpost (Flow e) (in_or_app _ _ _ (or_intror (in_map _ _ _ He))))).
  - intros [Hseed Hflow] [n|e] Hrow; split; cbn.
    + apply Hseed; apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
        apply in_map_iff in Hrow; destruct Hrow as [v [Heq Hin]]; inversion Heq; subst; assumption.
    + intros x a Hside; contradiction.
    + apply Hflow; apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
        apply in_map_iff in Hrow; destruct Hrow as [v [Heq Hin]]; inversion Heq; subst; assumption.
    + intros x a Hside; contradiction.
Qed.

(** A backward post-solution is exactly all node seeds and the reversed edge bounds. *)
Theorem backward_post_solution_iff {N E A} (g : Graph.t N E) (L : lattice A) (exitf : N -> A)
    (bt : E -> A -> A) (sigma : N -> A) :
  post_solution L (backward_system g exitf bt) sigma <->
  (forall n, In n (Graph.nodes g) -> leb L (exitf n) (sigma n) = true) /\
  (forall e, In e (edges_of g) ->
    leb L (bt e (sigma (Graph.target g e))) (sigma (Graph.source g e)) = true).
Proof.
  split.
  - intro Hpost; split.
    + intros n Hn; apply (proj1 (Hpost (Seed n) (in_or_app _ _ _ (or_introl (in_map _ _ _ Hn))))).
    + intros e He; apply (proj1 (Hpost (Flow e) (in_or_app _ _ _ (or_intror (in_map _ _ _ He))))).
  - intros [Hseed Hflow] [n|e] Hrow; split; cbn.
    + apply Hseed; apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
        apply in_map_iff in Hrow; destruct Hrow as [v [Heq Hin]]; inversion Heq; subst; assumption.
    + intros x a Hside; contradiction.
    + apply Hflow; apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
        apply in_map_iff in Hrow; destruct Hrow as [v [Heq Hin]]; inversion Heq; subst; assumption.
    + intros x a Hside; contradiction.
Qed.

(** * Paths and cycle cuts *)

Lemma graph_path_app {N E} (g : Graph.t N E) u es v fs w :
  path g u es v -> path g v fs w -> path g u (es ++ fs) w.
Proof.
  intro Hpath; induction Hpath as [u|e es v Hedge Hpath IH]; intro Htail.
  - exact Htail.
  - cbn; constructor; [exact Hedge|apply IH; exact Htail].
Qed.

Lemma edges_of_in {N E} (g : Graph.t N E) n e :
  In n (Graph.nodes g) -> In e (Graph.out g n) -> In e (edges_of g).
Proof.
  intros Hnode Hedge; apply in_flat_map; exists n; split; assumption.
Qed.

Lemma edges_of_source {N E} (g : Graph.t N E) e :
  graph_wf g -> In e (edges_of g) -> In e (Graph.out g (Graph.source g e)).
Proof.
  intros Hwf Hin; apply in_flat_map in Hin; destruct Hin as [n [Hnode Hedge]].
  rewrite (out_source Hwf n e Hedge); exact Hedge.
Qed.

Lemma forward_flow_edge {N E A} (g : Graph.t N E) init (ft : E -> A -> A) x y :
  flows (forward_static g init ft) x y ->
  exists e, In e (edges_of g) /\ x = Graph.source g e /\ y = Graph.target g e.
Proof.
  intros [c [Hrow [Hread Houtput]]]; destruct c as [n|e]; cbn in Hread;
    [contradiction|].
  destruct Houtput as [Htarget|Hside]; [|contradiction]; cbn in Htarget.
  destruct Hread as [Hread|Hread]; [|contradiction].
  exists e; split; [|split; congruence].
  apply in_app_or in Hrow; destruct Hrow as [Hseed|Hflow].
  - apply in_map_iff in Hseed; destruct Hseed as [n [Heq Hin]]; discriminate.
  - apply in_map_iff in Hflow; destruct Hflow as [e' [Heq Hin]]; inversion Heq; subst; exact Hin.
Qed.

Lemma backward_flow_edge {N E A} (g : Graph.t N E) exitf (bt : E -> A -> A) x y :
  flows (backward_static g exitf bt) x y ->
  exists e, In e (edges_of g) /\ x = Graph.target g e /\ y = Graph.source g e.
Proof.
  intros [c [Hrow [Hread Houtput]]]; destruct c as [n|e]; cbn in Hread;
    [contradiction|].
  destruct Houtput as [Htarget|Hside]; [|contradiction]; cbn in Htarget.
  destruct Hread as [Hread|Hread]; [|contradiction].
  exists e; split; [|split; congruence].
  apply in_app_or in Hrow; destruct Hrow as [Hseed|Hflow].
  - apply in_map_iff in Hseed; destruct Hseed as [n [Heq Hin]]; discriminate.
  - apply in_map_iff in Hflow; destruct Hflow as [e' [Heq Hin]]; inversion Heq; subst; exact Hin.
Qed.

Lemma forward_flow_path {N E A} (g : Graph.t N E) init (ft : E -> A -> A) W x y :
  graph_wf g ->
  clos_trans N (fun u v => flows (forward_static g init ft) u v /\ W v = false) x y ->
  exists es, es <> [] /\ path g x es y /\ W y = false /\
    forall e, In e es -> W (Graph.target g e) = false.
Proof.
  intros Hwf Hflow; induction Hflow as [x y [Hflow HW]|x y z Hxy IHxy Hyz IHyz].
  - destruct (forward_flow_edge g init ft x y Hflow) as [e [He [-> ->]]].
    exists [e]; split; [discriminate|]; split.
    + constructor; [apply edges_of_source; assumption|constructor].
    + split; [exact HW|intros e' [<-|Hfalse]; [exact HW|contradiction]].
  - destruct IHxy as [es [Hnonempty [Hpath [HW Hedges]]]].
    destruct IHyz as [fs [Hnonempty' [Hpath' [HW' Hedges']]]].
    exists (es ++ fs); split.
    + intro Hnil; apply app_eq_nil in Hnil; tauto.
    + split; [eapply graph_path_app; eassumption|]; split; [exact HW'|].
      intros e Hin; apply in_app_or in Hin; destruct Hin; [apply Hedges|apply Hedges']; assumption.
Qed.

Lemma path_sources_false {N E} (g : Graph.t N E) W x es y :
  path g x es y -> W x = false ->
  (forall e, In e es -> W (Graph.target g e) = false) ->
  forall e, In e es -> W (Graph.source g e) = false.
Proof.
  intro Hpath; induction Hpath as [x|a es y Hedge Hpath IH]; intros HW Htargets e Hin.
  - contradiction.
  - destruct Hin as [<-|Hin]; [exact HW|].
    apply IH; [apply Htargets; left; reflexivity| |exact Hin].
    intros e' Hin'; apply Htargets; right; exact Hin'.
Qed.

Lemma backward_flow_path {N E A} (g : Graph.t N E) exitf (bt : E -> A -> A) W x y :
  graph_wf g ->
  clos_trans N (fun u v => flows (backward_static g exitf bt) u v /\ W v = false) x y ->
  exists es, es <> [] /\ path g y es x /\
    forall e, In e es -> W (Graph.source g e) = false.
Proof.
  intros Hwf Hflow; induction Hflow as [x y [Hflow HW]|x y z Hxy IHxy Hyz IHyz].
  - destruct (backward_flow_edge g exitf bt x y Hflow) as [e [He [-> ->]]].
    exists [e]; split; [discriminate|]; split.
    + constructor; [apply edges_of_source; assumption|constructor].
    + intros e' [<-|Hfalse]; [exact HW|contradiction].
  - destruct IHxy as [es [Hnonempty [Hpath Hedges]]].
    destruct IHyz as [fs [Hnonempty' [Hpath' Hedges']]].
    exists (fs ++ es); split.
    + intro Hnil; apply app_eq_nil in Hnil; tauto.
    + split; [eapply graph_path_app; eassumption|].
      intros e Hin; apply in_app_or in Hin; destruct Hin; [apply Hedges'|apply Hedges]; assumption.
Qed.

(** Graph widening points cut every cycle of the forward system. *)
Theorem forward_cuts_every_cycle {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A)
    (W : N -> bool) :
  graph_wf g -> meets_every_cycle g W -> cuts_every_cycle (forward_static g init ft) W.
Proof.
  intros Hwf Hmeets x Hcycle.
  destruct (forward_flow_path g init ft W x x Hwf Hcycle)
    as [es [Hnonempty [Hpath [HW Htargets]]]].
  destruct (Hmeets x es Hnonempty Hpath) as [e [Hin He]].
  pose proof (path_sources_false g W x es x Hpath HW Htargets e Hin); congruence.
Qed.

(** The same graph widening points cut every cycle of the backward system. *)
Theorem backward_cuts_every_cycle {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A)
    (W : N -> bool) :
  graph_wf g -> meets_every_cycle g W -> cuts_every_cycle (backward_static g exitf bt) W.
Proof.
  intros Hwf Hmeets x Hcycle.
  destruct (backward_flow_path g exitf bt W x x Hwf Hcycle)
    as [es [Hnonempty [Hpath Hsources]]].
  destruct (Hmeets x es Hnonempty Hpath) as [e [Hin He]].
  specialize (Hsources e Hin); congruence.
Qed.

(** * Histories and semantic runs *)

(** Every edge history has a corresponding traced semantic run. *)
Theorem run_edges_exec {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) :
  run_edges m gv s es t -> exists tr, exec m s tr t.
Proof.
  intro Hhistory; induction Hhistory as
    [s|s l s' e es t Hstep Htaken Hhistory IH|s l s' es t Hstep Hstays Hhistory IH].
  - exists []; constructor.
  - destruct IH as [tr Hrun]; exists (l ++ tr); econstructor; eassumption.
  - destruct IH as [tr Hrun]; exists (l ++ tr); econstructor; eassumption.
Qed.

(** Runs from reachable states admit edge histories by the view's coverage law. *)
Theorem exec_run_edges {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (tr : list O) :
  graph_view_laws m gv -> reachable_state m s -> exec m s tr t ->
  exists es, run_edges m gv s es t.
Proof.
  intros Hview Hreachable Hrun; revert Hreachable.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hreachable.
  - exists []; constructor.
  - destruct (IH (reachable_state_step m s l s' Hreachable Hstep)) as [es Hhistory].
    destruct (edge_covers Hview s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
    + exists es; eapply run_stay; eassumption.
    + exists (e :: es); econstructor; eassumption.
Qed.

(** A history from a reachable state follows a path between the states' points. *)
Theorem run_edges_path {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) :
  graph_view_laws m gv -> reachable_state m s -> run_edges m gv s es t ->
  path (cfg gv) (point gv s) es (point gv t).
Proof.
  intros Hview Hreachable Hhistory; revert Hreachable.
  induction Hhistory as
    [s|s l s' e es t Hstep Htaken Hhistory IH|s l s' es t Hstep Hstays Hhistory IH];
    intro Hreachable.
  - constructor.
  - destruct (taken_edge Hview s l s' e Hreachable Hstep Htaken) as [Hout Htarget].
    pose proof (out_source (cfg_wf Hview) _ _ Hout) as Hsource.
    rewrite <- Hsource; constructor.
    + rewrite Hsource; exact Hout.
    + rewrite Htarget; apply IH; eapply reachable_state_step; eassumption.
  - rewrite <- (stays_point Hview s l s' Hreachable Hstep Hstays).
    apply IH; eapply reachable_state_step; eassumption.
Qed.

Lemma view_point_reachable {S O N E} (m : semantics S O) (gv : graph_view S O N E) s :
  graph_view_laws m gv -> reachable_state m s -> reachable (cfg gv) (point gv s).
Proof.
  intros Hview [s0 [tr [Hinitial Hrun]]].
  assert (Hreachable : reachable_state m s0).
  { exists s0, []; split; [exact Hinitial|constructor]. }
  destruct (exec_run_edges m gv s0 s tr Hview Hreachable Hrun) as [es Hhistory].
  apply reachable_iff_path; exists (point gv s0), es; split.
  - apply (entry_points Hview); exact Hinitial.
  - eapply run_edges_path; eassumption.
Qed.

Lemma view_point_in_nodes {S O N E} (m : semantics S O) (gv : graph_view S O N E) s :
  graph_view_laws m gv -> reachable_state m s -> In (point gv s) (Graph.nodes (cfg gv)).
Proof.
  intros Hview Hreachable; apply reachable_in_nodes; [apply (cfg_wf Hview)|].
  eapply view_point_reachable; eassumption.
Qed.

Lemma view_taken_edge {S O N E} (m : semantics S O) (gv : graph_view S O N E) s l s' e :
  graph_view_laws m gv -> reachable_state m s -> step m s l s' -> taken gv s l s' e ->
  In e (edges_of (cfg gv)) /\ Graph.source (cfg gv) e = point gv s /\
    Graph.target (cfg gv) e = point gv s'.
Proof.
  intros Hview Hreachable Hstep Htaken.
  destruct (taken_edge Hview s l s' e Hreachable Hstep Htaken) as [Hout Htarget].
  split.
  - eapply edges_of_in; [eapply view_point_in_nodes; eassumption|exact Hout].
  - split; [eapply out_source; [apply (cfg_wf Hview)|exact Hout]|exact Htarget].
Qed.

(** Histories concatenate in the order their edges were taken. *)
Theorem run_edges_app {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s u t : S)
    (es1 es2 : list E) :
  run_edges m gv s es1 u -> run_edges m gv u es2 t -> run_edges m gv s (es1 ++ es2) t.
Proof.
  intro Hhistory; induction Hhistory as
    [s|s l s' e es u Hstep Htaken Hhistory IH|s l s' es u Hstep Hstays Hhistory IH];
    intro Htail; cbn.
  - exact Htail.
  - econstructor; [exact Hstep|exact Htaken|apply IH; exact Htail].
  - eapply run_stay; [exact Hstep|exact Hstays|apply IH; exact Htail].
Qed.

Lemma run_edges_split_last {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    s fs t :
  run_edges m gv s fs t -> forall es e, fs = es ++ [e] ->
  exists s1 l s2, run_edges m gv s es s1 /\ step m s1 l s2 /\ taken gv s1 l s2 e /\
    run_edges m gv s2 [] t.
Proof.
  intro Hhistory; induction Hhistory as
    [s|s l s' a fs t Hstep Htaken Hhistory IH|s l s' fs t Hstep Hstays Hhistory IH];
    intros es e Heq.
  - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq as [_ Hbad]; discriminate.
  - destruct es as [|b es]; cbn in Heq; inversion Heq; subst.
    + exists s, l, s'; split; [constructor|]; repeat split; assumption.
    + destruct (IH es e eq_refl) as [s1 [l1 [s2 [Hprefix [Hlast [Hedge Hsuffix]]]]]].
      exists s1, l1, s2; split; [econstructor; eassumption|]; repeat split; assumption.
  - destruct (IH es e Heq) as [s1 [l1 [s2 [Hprefix [Hlast [Hedge Hsuffix]]]]]].
    exists s1, l1, s2; split; [eapply run_stay; eassumption|]; repeat split; assumption.
Qed.

(** A nonempty history ends with its last taken edge followed by zero or more stays. *)
Theorem run_edges_snoc_inv {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) (e : E) :
  run_edges m gv s (es ++ [e]) t <->
  exists s1 l s2, run_edges m gv s es s1 /\ step m s1 l s2 /\ taken gv s1 l s2 e /\
    run_edges m gv s2 nil t.
Proof.
  split.
  - intro Hhistory; eapply run_edges_split_last; [exact Hhistory|reflexivity].
  - intros [s1 [l [s2 [Hprefix [Hstep [Htaken Hsuffix]]]]]].
    eapply run_edges_app; [exact Hprefix|]; econstructor; eassumption.
Qed.

(** Appending a writing edge replaces the history's previous last writer. *)
Theorem last_writer_snoc {E X} (writes : E -> X -> bool) (es : list E) (e : E) (x : X) :
  last_writer writes (es ++ [e]) x = if writes e x then Some e else last_writer writes es x.
Proof.
  unfold last_writer; rewrite fold_left_app; reflexivity.
Qed.

(** Appending an edge performs exactly one reset or arrival update. *)
Theorem arrivals_since_snoc {E} (enter back : E -> bool) (es : list E) (e : E) :
  arrivals_since enter back (es ++ [e]) =
  if enter e then 0 else if back e then S (arrivals_since enter back es)
  else arrivals_since enter back es.
Proof.
  unfold arrivals_since; rewrite fold_left_app; reflexivity.
Qed.
