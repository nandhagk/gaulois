# Gaulois.Analyses

The catalogue. Each analysis is a short composition of a view from `Views`, a domain from `Order`
and `Domains`, and an engine and scheduler from `Fixpoint`, together with one generic soundness
theorem that holds for every client that satisfies the view's obligations. For example, liveness
is the backward system of a graph view whose edge transfer is `(a \ defs e) ∪ uses e`; the
theorem says that two runs from states that agree on the live-in set behave the same, for any
language whose `uses` and `defs` are honest. No toy-language content lives here: `Examples`
instantiates every entry.

Conventions, in addition to those of `views.md`:
- Every analysis has a system builder (`<name>_system`, a `system` as in `FixpointSystem.v`) and a
  soundness theorem that quantifies over any `sigma` with `post_solution L (<name>_system ...)
  sigma`. The solved form is the engine's result `{s : X -> A | post_solution L S s}`, produced by
  `solve_total` or `solve_fuel` as named under **Composition**; soundness never depends on the
  engine or the scheduler.
- Sets are `FinSet.t X` with an explicit `EX : encoding X`, so `FinSet.mem EX x a` is a boolean.
  Every analysis whose facts are sets computes on a *finite universe* `U : list X` (a `NoDup` list
  that the analysis computes from its view), so that the lattice has a `height` and a `top`: the
  facts are `finite_set EX U`, the may-lattice is `finite_powerset_lattice EX U` (join = union) and
  the must-lattice is `finite_must_lattice EX U` (bottom = `U`, join = intersection, top = the
  empty set), all from `Order`. `fmem EX x a` tests `x` in the underlying set of a fact. A
  transfer is written on raw sets and clamped back into the universe with `finite_clamp EX U`
  (asked of `Order`: the members of a raw set that lie in `U`).
- Engines. A system with a height or a widening rank and a static dependency summary goes through
  `solve_total`, with the evidence passed as `inhabits (base_height H)` or `inhabits (base_wrank
  W)`. A system whose lattice has no
  height (equality partitions, byte ranges) goes through `solve_fuel` with the lattice's `top`.
  Each **Composition** comment names which, and the evidence. Both return
  `{s | post_solution ...}`, a function.
- Histories. A fact about what happened earlier in a run (reaching definitions, availability,
  arrival counts) is stated over a run prefix `run_edges m gv s es t` of `Views`, never through
  ghost state in the client's semantics.
- Laws that a client proves are `Prop` records named `<view>_laws`; they are the only premises of a
  soundness theorem.
- Every theorem below is required and proved. Every checker has acceptance
  evidence: a completeness theorem, or a required `Example` in `Examples` that accepts a nontrivial
  input (named in the checker's comment).

## Files

| File | Contents | Card |
|---|---|---|
| `AnalysesLiveness.v` | variable view, liveness, reaching definitions, must-equality, zero-since-entry | ANA-1 |
| `AnalysesAvailable.v` | gen/kill view, available and very busy expressions, lazy code motion | ANA-1 |
| `AnalysesStructured.v` | skeleton variables; liveness, certificates, observers | EX-4, ANA-2 |
| `AnalysesCensus.v` | region table | ANA-2 |
| `AnalysesValues.v` | operator bridge; numeric value analyses | EX-5a, ANA-3 |
| `AnalysesPaths.v` | edge predicates, path facts, guard chains | ANA-3 |
| `AnalysesDemand.v` | demand framework, dead values, demanded bits, observable bits, dead-code erasure | ANA-4 |
| `AnalysesAdce.v` | aggressive dead code with control dependence | ANA-4 |
| `AnalysesNumbering.v` | dominator-scoped numbering, optimistic GVN, loop invariance | ANA-5 |
| `AnalysesEgraph.v` | direct Rewrite facade and checked external explanations | ANA-6 |
| `AnalysesRewriteDomains.v`, `AnalysesSsaRewrite.v`, `AnalysesRewriteWord.v` | Rewrite clients | REW-7 |
| `AnalysesScev.v` | chains of recurrences, recognition, trip counts, idioms | ANA-7 |
| `AnalysesCalls.v` | resolvers, recursion, summaries, stack demand, call strings | ANA-8 |
| `AnalysesCallScc.v` | indexed SCC summaries and reachable call strings | ANA-8a |
| `AnalysesInterprocedural.v` | finite distributive interprocedural tabulation | ANA-8b |
| `AnalysesCallEffects.v` | no-return and mod/ref clients | ANA-8c |
| `AnalysesPointsToBase.v`, `AnalysesPointsToDelta.v` | Andersen constraints and direct delta solver | ANA-9a |
| `AnalysesPointsTo.v` | Steensgaard, escape, allocation and zero facts | ANA-9 |
| `AnalysesMemoryBase.v` | validated accesses, dead stores, epochs and invariant loads | ANA-10a |
| `AnalysesMemoryGraph.v`, `AnalysesMemoryFrontier.v`, `AnalysesMemorySealed.v` | version graph and constructors | ANA-10b–d |
| `AnalysesMemoryWalk.v`, `AnalysesMemoryLegacy.v` | clobber queries and legacy compatibility | ANA-10e |
| `AnalysesMemoryFlow.v`, `AnalysesMemoryForward.v` | sparse flow and value bridge | ANA-10f |
| `AnalysesRules.v` | liveness, neededness, reaching definitions as Rules programs | ANA-11 |
| `AnalysesSsaLiveQuery.v` | strict SSA point liveness queries | ANA-12 |
| `AnalysesSsaLiveSets.v` | sparse all-point liveness | ANA-13 |
| `AnalysesSeg.v` | sparse available and busy expression systems | ANA-14 |
| `AnalysesSsaPreGraph.v` | factored expression SSA graph and phi translation | ANA-16 |
| `AnalysesSsaPre.v`, `AnalysesSsaPreSemantics.v` | SSA PRE placement and client realization | ANA-15 |

## Definitions

### ANA-1: dense dataflow

```coq
(* AnalysesLiveness.v. A client's variable-level description of a graph view. X is the type of
   variables (SSA values for an SSA client), Cv the type of their values. *)
Definition fmem {K} (E : encoding K) {U : list K} (k : K) (a : finite_set E U) : bool :=
  FinSet.mem E k (proj1_sig a).
Definition mentions {K} (E : encoding K) (k : K) (l : list K) : bool :=
  existsb (fun k' => Pos.eqb (encode E k) (encode E k')) l.
Record var_view (S O N E X Cv : Type) : Type := VarView {
  gview : graph_view S O N E;
  uses : E -> list X;              (* variables the edge reads, guard and trap operands included *)
  defs : E -> list X;              (* variables the edge writes *)
  exit_uses : N -> list X;         (* variables that decide whether a state at the node ends *)
  vget : S -> X -> Cv
}.
Record var_view_laws {S O N E X Cv} (m : semantics S O) (en : endings S)
    (vv : var_view S O N E X Cv) : Prop := {
  view_laws : graph_view_laws m (gview vv);
  no_stays : forall s l s', ~ stays (gview vv) s l s';
  defs_frame : forall s l s' e x, reachable_state m s -> step m s l s' ->
    taken (gview vv) s l s' e -> ~ In x (defs vv e) -> vget vv s' x = vget vv s x;
  uses_determine : forall s l s' t e, reachable_state m s -> reachable_state m t ->
    point (gview vv) t = point (gview vv) s -> step m s l s' -> taken (gview vv) s l s' e ->
    (forall x, In x (uses vv e) -> vget vv s x = vget vv t x) ->
    exists t', step m t l t' /\ taken (gview vv) t l t' e /\
      forall x, In x (defs vv e) -> vget vv s' x = vget vv t' x;
  exits_determine : forall s t, reachable_state m s -> reachable_state m t ->
    point (gview vv) t = point (gview vv) s ->
    (forall x, In x (exit_uses vv (point (gview vv) s)) -> vget vv s x = vget vv t x) ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t)
}.
(* The universe of the variable analyses: every variable that the view mentions, once. *)
Definition var_universe {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) : list X :=
  FinSet.elements (FinSet.of_list EX
    (flat_map (fun e => uses vv e ++ defs vv e) (edges_of (cfg (gview vv)))
     ++ flat_map (exit_uses vv) (Graph.nodes (cfg (gview vv))))).
Definition live_set {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) : Type :=
  finite_set EX (var_universe EX vv).
Definition live_lattice {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    lattice (live_set EX vv) := finite_powerset_lattice EX (var_universe EX vv).
Definition live_agreement {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    agreement (live_set EX vv) S :=
  Agreement (fun a s t => forall x, fmem EX x a = true -> vget vv s x = vget vv t x).
Definition liveness_transfer {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv)
    (e : E) (a : live_set EX vv) : live_set EX vv :=
  finite_clamp EX (var_universe EX vv)
    (FinSet.union EX (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (defs vv e)))
       (FinSet.of_list EX (uses vv e))).
Definition liveness_system {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  System.t N (dense_constraint N E) (live_set EX vv) :=
  backward_system (cfg (gview vv))
    (fun n => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX (exit_uses vv n)))
    (liveness_transfer EX vv).
Definition liveness_static {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  System.static (liveness_system EX vv) := backward_static _ _ _.
Definition solve_liveness {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) :
  {s : N -> live_set EX vv | post_solution (live_lattice EX vv) (liveness_system EX vv) s}.
(* solve_total EN (dense_constraint_encoding EN EE) (live_lattice EX vv) _ (rpo_scheduler ..) Joining
   (liveness_system EX vv) (liveness_static EX vv) _ *)
(* Composition. View: graph_view through var_view. Domain: finite_powerset_lattice over
   var_universe (NoDup, so finite_powerset_height gives the height). Engine: solve_total with
   Joining, liveness_static and the evidence `inhabits (base_height (finite_powerset_height ..))`. Scheduler:
   rpo_scheduler of the dependency graph, which is reverse post-order on the reverse flow. *)

(* Reaching definitions: a forward may-analysis over (variable, defining edge) pairs. The last
   definition of a variable is a function of the run prefix, Views' `last_writer`, so nothing is
   recorded in the state. *)
Definition reach_universe {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : list (X * E) :=
  FinSet.elements (FinSet.of_list (pair_encoding EX EE)
    (flat_map (fun e => map (fun x => (x, e)) (defs vv e)) (edges_of (cfg (gview vv))))).
Definition reach_set {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : Type := finite_set (pair_encoding EX EE) (reach_universe EX EE vv).
Definition reach_lattice {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : lattice (reach_set EX EE vv) :=
  finite_powerset_lattice (pair_encoding EX EE) (reach_universe EX EE vv).
(* This body is the reference equation, not a required definitional equation. The executable
   transfer captures FinSet.of_list EX (defs vv e) before filtering the fact and uses membership
   in that set for each pair. Prove pointwise equality with this entire finite_set result for
   every vv, e and a, including unlisted edges and raw views. *)
Definition reaching_transfer {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) (e : E) (a : reach_set EX EE vv) : reach_set EX EE vv :=
  finite_clamp (pair_encoding EX EE) (reach_universe EX EE vv)
    (FinSet.of_list (pair_encoding EX EE)
       (filter (fun xd => negb (mentions EX (fst xd) (defs vv e)))
          (FinSet.elements (proj1_sig a)) ++ map (fun x => (x, e)) (defs vv e))).
Definition reaching_system {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) :
  System.t N (dense_constraint N E) (reach_set EX EE vv) :=
  forward_system (cfg (gview vv)) (fun _ => bot (reach_lattice EX EE vv))
    (reaching_transfer EX EE vv).
(* This system body is also a reference equation, using the transfer reference body above.
   The executable system prepares an EE-keyed
   index of kill sets for the graph's edges once before constructing its callbacks, and retains
   that index across queries. For an edge absent from the index, its callback prepares the kill
   set from defs vv e. Thus arbitrary Flow rows retain the reference behavior. Prove equality
   of constraint lists, pointwise targets, and Query.run results for every row and assignment
   against this reference system. The result and both ordered traces are preserved, without
   functional extensionality. The public signatures and semantic theorem premises are unchanged. *)
(* Composition. Domain: finite_powerset_lattice over pair_encoding EX EE and reach_universe.
   Engine: solve_total, Joining, forward_static. Scheduler: rpo_scheduler. *)

(* Zero since entry: the variables not written since the entry, so still holding `zero`. A
   must-analysis: the fact is the set of variables known to be untouched. *)
Definition zero_lattice {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    lattice (live_set EX vv) := finite_must_lattice EX (var_universe EX vv).
Definition zero_since_entry_system {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (locals : list X) :
  System.t N (dense_constraint N E) (live_set EX vv) :=
  forward_system (cfg (gview vv))
    (fun _ => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX locals))
    (fun e a => finite_clamp EX (var_universe EX vv)
                  (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (defs vv e)))).
(* Composition. Domain: finite_must_lattice (bottom = the universe, join = intersection).
   Engine: solve_total, Joining, evidence finite_must_height. Scheduler: rpo_scheduler. *)

(* Must-equality of variables: an equality partition (Domains, DOM-7) tracks which variables hold
   the same value; an edge forgets what it defines and then merges what it copies. *)
Record copy_view (S O N E X Cv : Type) : Type := CopyView {
  cvars : var_view S O N E X Cv;
  copies : E -> list (X * X)       (* the edge ends with x = y for each (x, y) *)
}.
Definition equality_transfer {S O N E X Cv} (EX : encoding X) (cv : copy_view S O N E X Cv)
    (e : E) (p : partition EX) : partition EX :=
  fold_left (fun q xy => partition_union EX (fst xy) (snd xy) q) (copies cv e)
    (fold_left (fun q x => partition_forget EX x q) (defs (cvars cv) e) p).
Definition equality_system {S O N E X Cv} (EX : encoding X) (cv : copy_view S O N E X Cv) :
  System.t N (dense_constraint N E) (partition EX) :=
  forward_system (cfg (gview (cvars cv))) (fun _ => top_value (partition_top EX))
    (equality_transfer EX cv).
(* `partition EX`, `partition_top`, `partition_union` and `partition_forget` are DOM-7's;
   partition_forget drops x from its class and keeps the other equalities. Composition. Domain:
   partition_lattice, which has no height. Engine: solve_fuel with partition_top as the top
   fallback; the initial fact is the discrete partition. *)
```

```coq
(* AnalysesAvailable.v. A gen/kill view over expressions U. `uval s u` is the value that the
   expression u has in the state s (None when evaluating it would trap). *)
Record genkill_view (S O N E U C : Type) : Type := GenKillView {
  gkview : graph_view S O N E;
  gen : E -> list U;               (* expressions the edge computes (in its pre-state) *)
  kill : E -> U -> bool;           (* expressions whose value the edge may change *)
  uval : S -> U -> option C
}.
Record genkill_laws {S O N E U C} (m : semantics S O) (en : endings S)
    (gk : genkill_view S O N E U C) : Prop := {
  gk_view : graph_view_laws m (gkview gk);
  gk_no_stays : forall s l s', ~ stays (gkview gk) s l s';
  gen_value : forall s l s' e u, reachable_state m s -> step m s l s' ->
    taken (gkview gk) s l s' e -> In u (gen gk e) -> uval gk s' u = uval gk s u;
  kill_frame : forall s l s' e u, reachable_state m s -> step m s l s' ->
    taken (gkview gk) s l s' e -> kill gk e u = false -> uval gk s' u = uval gk s u;
  final_exit : forall s, reachable_state m s -> final en s ->
    Graph.out (cfg (gkview gk)) (point (gkview gk) s) = nil
}.
Definition expr_universe {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C) :
    list U :=
  FinSet.elements (FinSet.of_list EU (flat_map (gen gk) (edges_of (cfg (gkview gk))))).
Definition avail_set {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C) : Type :=
  finite_set EU (expr_universe EU gk).
Definition avail_lattice {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C) :
    lattice (avail_set EU gk) := finite_must_lattice EU (expr_universe EU gk).
Definition avail_transfer {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (e : E) (a : avail_set EU gk) : avail_set EU gk :=
  finite_clamp EU (expr_universe EU gk)
    (FinSet.union EU
       (FinSet.of_list EU (filter (fun u => negb (kill gk e u)) (FinSet.elements (proj1_sig a))))
       (FinSet.of_list EU (gen gk e))).
Definition available_system {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C) :
  System.t N (dense_constraint N E) (avail_set EU gk) :=
  forward_system (cfg (gkview gk)) (fun _ => finite_clamp EU (expr_universe EU gk) FinSet.empty)
    (avail_transfer EU gk).
(* Must-analysis, forward: init n = the empty fact (nothing is available at an entry), bottom =
   the whole universe. Composition. Domain: finite_must_lattice. Engine: solve_total, Joining,
   evidence finite_must_height. Scheduler: rpo_scheduler. A store-to-load forwarding client uses
   U = (range, value) pairs and the same system. *)
Definition busy_system {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C) :
  System.t N (dense_constraint N E) (avail_set EU gk) :=
  backward_system (cfg (gkview gk))
    (fun n => match Graph.out (cfg (gkview gk)) n with
              | nil => finite_clamp EU (expr_universe EU gk) FinSet.empty
              | _ => bot (avail_lattice EU gk)
              end)
    (avail_transfer EU gk).
(* Very busy (anticipated) expressions: must-analysis, backward, the same lattice; the seed is the
   empty fact at a node without out-edges and the bottom elsewhere; bt = avail_transfer. *)
(* Lazy code motion as a checked producer: any algorithm may propose insertions and deletions. *)
Record lcm_result (E N U : Type) : Type := LcmResult {
  insert : E -> list U;            (* compute u on this edge *)
  delete : N -> list U             (* the recomputation of u at this node's entry is removed *)
}.
Definition lcm_check {S O N E U C} {U1 U2 U3 : list U} (EU : encoding U)
    (gk : genkill_view S O N E U C) (avail : N -> finite_set EU U1) (busy : N -> finite_set EU U2)
    (avail2 : N -> finite_set EU U3) (r : lcm_result E N U) : bool :=
  forallb (fun e => forallb (fun u =>
      fmem EU u (busy (Graph.target (cfg (gkview gk)) e)) &&
      negb (fmem EU u (avail (Graph.source (cfg (gkview gk)) e)))) (insert r e))
    (edges_of (cfg (gkview gk))) &&
  forallb (fun n => forallb (fun u => fmem EU u (avail2 n)) (delete r n))
    (Graph.nodes (cfg (gkview gk))).
(* `avail` and `busy` are the solutions of available_system and busy_system for gk, `avail2` the
   availability of the view whose gen is extended by insert r. The producer stays untrusted.
   Acceptance evidence: `while_lcm_accepts`, a required Example in ExamplesWhileViewsTest.v. *)
```

### ANA-2: structured code

EX-4 owns `skel_vars`, `skel_vars_laws` and `act_vars` in `AnalysesStructured.v`, including
their constructors and projections. ANA-2 extends the same file after EX-4 lands and owns the
remaining declarations in this section. Both cards use these same nominal interfaces.

```coq
(* AnalysesStructured.v. Variables seen by a skeleton client. *)
Record skel_vars (A G X : Type) : Type := SkelVars {
  atom_uses : A -> list X;
  atom_defs : A -> list X;
  atom_trap_uses : A -> list X;    (* operands that decide whether the atom traps or stops *)
  guard_uses : G -> list X
}.
Record skel_vars_laws {A G St O X Cv} (C : skeleton_client A G St O) (sv : skel_vars A G X)
    (look : St -> X -> Cv) : Prop := {
  atom_frame : forall a st l st' x, atom_step C a st l st' -> ~ In x (atom_defs sv a) ->
    look st' x = look st x;
  atom_agrees : forall a st1 l st1' st2, atom_step C a st1 l st1' ->
    (forall x, In x (atom_uses sv a) -> look st1 x = look st2 x) ->
    exists st2', atom_step C a st2 l st2' /\
      forall x, In x (atom_defs sv a) -> look st1' x = look st2' x;
  guard_agrees : forall g st1 st2, (forall x, In x (guard_uses sv g) -> look st1 x = look st2 x) ->
    guard_bool C g st1 = guard_bool C g st2 /\ guard_index C g st1 = guard_index C g st2;
  trap_agrees : forall a st1 st2, (forall x, In x (atom_trap_uses sv a) -> look st1 x = look st2 x) ->
    (atom_trap C a st1 <-> atom_trap C a st2) /\ (atom_stop C a st1 <-> atom_stop C a st2);
  jump_keeps : forall p n st st' x, jump_effect C p n st st' -> look st' x = look st x
}.
(* The variables of one action. *)
Definition act_vars {A G X} (sv : skel_vars A G X) (act : action A G) : list X :=
  match act with
  | AAtom a => atom_uses sv a ++ atom_defs sv a
  | AGuard g _ => guard_uses sv g
  | AIndexIs g _ => guard_uses sv g
  | AIndexAtLeast g _ => guard_uses sv g
  | AJump _ _ => nil
  end.
(* The variables of the statement whose trap or guard decides an exit. *)
Definition skel_exit_uses {A G X} (sv : skel_vars A G X) (prog : stmt A G) (n : skel_point) :
    list X :=
  match n with
  | PEntry p => match sub prog p with
                | Some (Atom a) => atom_trap_uses sv a
                | Some (If g _ _) => guard_uses sv g
                | Some (JumpIf g _) => guard_uses sv g
                | Some (JumpTable g _ _) => guard_uses sv g
                | _ => nil
                end
  | PExit _ => nil
  end.
Definition skel_universe {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G) :
    list X :=
  FinSet.elements (FinSet.of_list EX
    (flat_map (fun e => flat_map (act_vars sv) (skel_acts prog e)) (edges_of (skeleton_graph prog))
     ++ flat_map (skel_exit_uses sv prog) (Graph.nodes (skeleton_graph prog)))).
Definition skel_set {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G) : Type :=
  finite_set EX (skel_universe EX sv prog).
Definition skel_lattice {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G) :
    lattice (skel_set EX sv prog) := finite_powerset_lattice EX (skel_universe EX sv prog).
Definition skel_actb {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G) :
    action A G -> skel_set EX sv prog -> skel_set EX sv prog := fun act a =>
  finite_clamp EX (skel_universe EX sv prog)
    (match act with
     | AAtom x => FinSet.union EX (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (atom_defs sv x)))
                    (FinSet.of_list EX (atom_uses sv x))
     | AJump _ _ => proj1_sig a
     | _ => FinSet.union EX (proj1_sig a) (FinSet.of_list EX (act_vars sv act))
     end).
Definition structured_liveness_system {A G X} (EX : encoding X) (sv : skel_vars A G X)
    (prog : stmt A G) :
  System.t skel_point (dense_constraint skel_point (skel_edge A G)) (skel_set EX sv prog) :=
  skeleton_backward prog
    (fun n => finite_clamp EX (skel_universe EX sv prog) (FinSet.of_list EX (skel_exit_uses sv prog n)))
    (skel_actb EX sv prog).
(* Composition. View: skeleton_view. Domain: finite_powerset_lattice over skel_universe (NoDup).
   Engine: solve_total, Joining, backward_static, evidence finite_powerset_height. Scheduler:
   wto_scheduler of the static skeleton system, one component per Loop (the loop heads are the
   checking points). *)

(* Loop certificates: only loop-head facts are stored. The checker recomputes every other point
   in one bottom-up pass over the skeleton and checks the inequalities. *)
Definition certificate {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G) : Type :=
  list (skel_point * skel_set EX sv prog).
Definition certificate_check {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (cert : certificate EX sv prog) : bool.
(* true iff (1) map fst cert = loop_heads prog, and (2) Fixpoint's `expand` accepts the
   cut_certificate whose cuts are the loop heads, whose stored values are cert and whose plan is
   plan_of the loop heads, on structured_liveness_system *)
Definition certificate_of {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (sigma : skel_point -> skel_set EX sv prog) : certificate EX sv prog :=
  map (fun n => (n, sigma n)) (loop_heads prog).
(* Observers: replay the certificate through an observer, folding it over every point and its
   fact, so that a client such as an interference builder stores nothing extra. *)
Definition replay_live {A G X Ob} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (cert : certificate EX sv prog) (obs : Ob -> skel_point -> skel_set EX sv prog -> Ob)
    (z : Ob) : option Ob.
(* None when the certificate is rejected; otherwise Fixpoint's `replay obs z order (lookup ..)` over
   the expanded assignment, with order = the cut points followed by the plan *)
```

```coq
(* AnalysesCensus.v *)
Definition region_table {A G R} (alg : summary_algebra A G R) (prog : stmt A G) :
  Map.t position R.   (* summarise alg (sub prog p) at every valid p, in one bottom-up pass *)
Fixpoint census_atoms {A G} (prog : stmt A G) : list A :=
  match prog with
  | Atom a => [a]
  | Seq x y | If _ x y => census_atoms x ++ census_atoms y
  | Block x | Loop x => census_atoms x
  | Jump _ | JumpIf _ _ | JumpTable _ _ _ => []
  end.
Definition occurrence_census {A G V} (EV : encoding V) (uses : A -> list V)
    (prog : stmt A G) : Map.t V N.
(* Traverse syntax once, incrementing the encoded-key count for every operand in uses a.
   Count each syntactic loop body once, including duplicate operands; do not count dynamic runs. *)
```

### ANA-3: value analyses (sparse conditional generator of VIEW-4)

EX-5a owns the first two records, `op_bridge` and `op_bridge_laws`, including their
constructors and fields. ANA-3 extends this same file after EX-5a lands, preserves those
records and uses them for the remaining declarations.

```coq
(* AnalysesValues.v. A numeric domain of Domains, a bridge from the client's operators to
   Bits, and a value view give a sparse_domain. *)
Record op_bridge (K C : Type) : Type := OpBridge {
  op_expr : K -> option Bits.expr;       (* the Bits expression the operator denotes *)
  to_word : C -> option word
}.
Record op_bridge_laws {K C} (br : op_bridge K C) (op_eval : K -> list C -> option C)
    (truth : C -> bool) : Prop := {
  bridge_word : forall c w, to_word br c = Some w -> is_word (fst w) (snd w);
  bridge_eq : forall o cs r e, op_eval o cs = Some r -> op_expr br o = Some e ->
    exists ws wr, Forall2 (fun c w => to_word br c = Some w) cs ws /\
      Bits.eval (fun i => nth i ws (1%positive, 0%Z)) e = Some wr /\ to_word br r = Some wr;
  bridge_truth : forall c w, to_word br c = Some w -> truth c = negb (Z.eqb (snd w) 0)
}.
Definition sparse_of_numeric {A K C} (ND : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) (top : A) : sparse_domain A C K.
(* fact_lat = lat ND; fact_conc a c = gamma G a w when to_word br c = Some w, and `leb (lat ND) a (bot
   (lat ND)) = false` when c is not a word; top_fact = top; op_abs o fs = abs_eval ND (fun i =>
   nth i fs top) e when op_expr br o = Some e, and top otherwise; assume_value (GConst c) a =
   meet ND a (of_const ND w z) for to_word br c = Some (w, z), and the identity for the other
   guards; assume_args o b fs = the arguments refined by abs_assume ND (fun i => nth i fs top) e
   (the fact of the truth value b at the result width of e), read back at 0 to n - 1 *)
Definition numeric_problem {S O N E V K C A} (ND : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) (top : A) (sv : ssa_view S O N E V K C) (vals : list V)
    (entry : V -> A) : sparse_problem S O N E V K C A :=
  SparseProblem S O N E V K C A sv (sparse_of_numeric ND G br top) vals entry.
(* SCCP, known bits, wrapping intervals, bits x interval and interval x congruence are
   numeric_problem with the numeric_domain of DOM-1 (constants), DOM-2, DOM-3 and DOM-4 (the
   reduced products), each with its numeric_laws; the width plumbing is `tagged_domain`. *)
(* DOM-4 product payload meanings include is_word at the explicit width. Tagged numeric meanings
   already impose that condition on TVal; product_tagged_gamma_equiv states agreement with the
   former intersection meaning. Generic analyses and component meanings retain their laws. A
   client-supplied constant product needs const_reduction_laws in addition to word_laws. *)
(* The Ssa refined point model uses a syntactic analysis carrier for ANA-12 and ANA-13; its
   point_model equals var_point_uses of that carrier. The separately proved semantic variable
   view has pending slots and different uses and defs, although both views share a graph.
   Source-variable liveness at raw points transfers only by ssa_refined_liveness. Semantic
   conclusions use the original semantic variable-view laws; intermediate facts and sets over
   the different variable carriers are not identified. *)
Definition solve_values {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (HL : lattice_laws (lift_bot_lattice (fact_lat (domain pr))))
    (sch : scheduler (sparse_unknown N E V)) (st : strategy)
    (HT : terminates (lift_bot_lattice (fact_lat (domain pr))) (sparse_static EN EV pr) sch st) :
  {s : sparse_unknown N E V -> lift_bot A |
     post_solution (lift_bot_lattice (fact_lat (domain pr))) (sparse_system EN EV pr) s} :=
  solve_total (sparse_unknown_encoding EN EE EV) (sparse_constraint_encoding EN EE EV)
    (lift_bot_lattice (fact_lat (domain pr))) HL sch st (sparse_system EN EV pr)
    (sparse_static EN EV pr) HT.
(* Composition. View: ssa_view over the activation semantics. Domain: the numeric domain under
   lift_bot. Engine: solve_total. Constants (flat) use Joining with the evidence from
   flat_height and option_height; known bits, intervals, wrapped intervals and the products use
   Widening with `wto_scheduler` (heads cut every cycle, `wto_scheduler_cuts`) and the evidence
   from their widening ranks (option_wrank). Narrowing is `narrow_checked`: kept only when the
   checker accepts the result. *)
```

```coq
(* AnalysesPaths.v. Edge predicates (Ranger style) are VIEW-5's `refined_fact`: the fact for a
   value as read in a block, refined by the guards of every dominating edge; Analyses adds no
   second definition. Path facts: a bounded disjunction (`disjunction_lattice` of Order) of facts,
   one disjunct per way of reaching the point, merged beyond k disjuncts. *)
Definition path_domain {A C K} (k : nat) (D : sparse_domain A C K) :
  sparse_domain (list A) C K.   (* over disjunction_lattice k (lat D); conc = disjunction_gamma *)
(* Guard chains: the guards that hold at a block, outermost first. *)
Definition guard_chain {S O N E V K C} (sv : ssa_view S O N E V K C) (EN : encoding N)
    (b : N) : list (condition V C) :=
  flat_map (edge_guard sv) (dominating_edges_in (make_dom_context EN (cfg (base sv))) b).
```

### ANA-4: neededness and demand

```coq
(* AnalysesDemand.v. One framework, two instances: M = bool is neededness (rules N1 to N3 of
   the 15-411 notes) and M = a bit mask is demanded bits. *)
Record demand_domain (M Cv : Type) : Type := DemandDomain {
  dlat : lattice M;                          (* bot: not demanded *)
  dagree : agreement M Cv                    (* agree m u v: u and v match on the demanded part *)
}.
Record demand_view (S O N E X Cv M : Type) : Type := DemandView {
  dgraph : graph_view S O N E;
  ddefs : E -> list X;
  dnec : E -> list (X * M);                  (* N1: demands forced by the edge's effects *)
  dback : E -> X -> M -> list (X * M);       (* N3: demands on the inputs, given a demand on a defined x *)
  dexit : N -> list (X * M);                 (* demands that decide whether the state ends *)
  dlookup : S -> X -> Cv;
  dvars : list X                             (* the universe: NoDup, every variable named above *)
}.
(* A demand is a finite map from variables to M; an absent variable has demand bot. *)
Definition demand_lattice {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) : lattice (finite_map EX (dvars dv) M) :=
  finite_pointwise_lattice EX (dvars dv) (dlat DD).
Definition dget {X M} (EX : encoding X) {U : list X} (DL : lattice M) (d : finite_map EX U M)
    (x : X) : M :=
  match Map.get EX x (proj1_sig d) with Some m => m | None => bot DL end.
Definition demand_agreement {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) : agreement (finite_map EX (dvars dv) M) S :=
  Agreement (fun d s t => forall x,
    agree (dagree DD) (dget EX (dlat DD) d x) (dlookup dv s x) (dlookup dv t x)).
Definition demand_transfer {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (e : E) (d : finite_map EX (dvars dv) M) :
  finite_map EX (dvars dv) M.
(* finite_map_clamp of the pointwise join of: d restricted to the variables outside ddefs e (N2);
   dnec e (N1); and dback e x (dget d x) for every x in ddefs e (N3) *)
Definition exit_map {X M} (EX : encoding X) (DL : lattice M) (l : list (X * M)) : Map.t X M.
(* the pointwise join of the entries of l *)
Definition demand_system {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
  System.t N (dense_constraint N E) (finite_map EX (dvars dv) M) :=
  backward_system (cfg (dgraph dv))
    (fun n => finite_map_clamp EX (dvars dv) (exit_map EX (dlat DD) (dexit dv n)))
    (demand_transfer EX DD dv).
(* Composition. Domain: finite_pointwise_lattice over dvars. Engine: solve_total, Joining,
   backward_static, evidence finite_pointwise_height with bool_height (neededness) or mask_height
   (demanded bits at one width). Scheduler: rpo_scheduler of the reverse flow. *)
(* The universe covers the view: no duplicates, and every variable named by a demand, a defined
   variable or an exit demand is in it. *)
Definition demand_vars_ok {S O N E X Cv M} (dv : demand_view S O N E X Cv M) : Prop :=
  NoDup (dvars dv) /\
  (forall e x m' y m'', In (y, m'') (dnec dv e ++ dback dv e x m') -> In y (dvars dv)) /\
  (forall n y m', In (y, m') (dexit dv n) -> In y (dvars dv)) /\
  (forall e x, In x (ddefs dv e) -> In x (dvars dv)).
(* `inv` is the invariant the run keeps (reachability, plus forward facts for demanded bits). *)
Record demand_laws {S O N E X Cv M} (m : semantics S O) (en : endings S) (inv : S -> Prop)
    (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M) : Prop := {
  d_view : graph_view_laws m (dgraph dv);
  d_no_stays : forall s l s', ~ stays (dgraph dv) s l s';
  d_frame : forall s l s' e x, inv s -> step m s l s' -> taken (dgraph dv) s l s' e ->
    ~ In x (ddefs dv e) -> dlookup dv s' x = dlookup dv s x;
  d_agreement : agreement_laws (demand_lattice EX DD dv) (demand_agreement EX DD dv) /\
    agreement_symmetric (demand_agreement EX DD dv);
  d_bot_agrees : forall u v, agree (dagree DD) (bot (dlat DD)) u v;
  d_back_bot : forall e x, dback dv e x (bot (dlat DD)) = nil;
  d_vars : demand_vars_ok dv;
  (* agreement on the demand of the edge's inputs gives the same step and agreement on d *)
  d_step : forall s l s' t e d, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    step m s l s' -> taken (dgraph dv) s l s' e ->
    agree (demand_agreement EX DD dv) (demand_transfer EX DD dv e d) s t ->
    exists t', step m t l t' /\ taken (dgraph dv) t l t' e /\
      agree (demand_agreement EX DD dv) d s' t';
  d_exits : forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    agree (demand_agreement EX DD dv)
      (finite_map_clamp EX (dvars dv) (exit_map EX (dlat DD) (dexit dv (point (dgraph dv) s)))) s t ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t)
}.
(* The effect policy: may an unread trapping instruction be deleted? Left to the client, and each
   policy has its own conclusion (`dce_conclusion` below). *)
Inductive trap_policy : Type := KeepTraps | DropUnreadTraps.
Definition effectful {I} (ef : effects I) (pol : trap_policy) (i : I) : bool :=
  observes ef i || writes ef i || allocates ef i || frees ef i || calls ef i || may_diverge ef i ||
  may_stop ef i ||
  (may_trap ef i && match pol with KeepTraps => true | DropUnreadTraps => false end).
(* A demand d is closed when the constant assignment is a post-solution: it does not depend on
   the node. *)
Definition demand_closed {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) : Prop :=
  post_solution (demand_lattice EX DD dv) (demand_system EX DD dv) (fun _ => d).
(* The closed demands are the post-solutions of one unknown: seeds exitf n and one flow per edge. *)
Definition closed_system {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
  System.t unit (dense_constraint N E) (finite_map EX (dvars dv) M).
(* constraints = map Seed (nodes g) ++ map Flow (edges_of g), g = cfg (dgraph dv); the target of
   every constraint is tt; rhs (Seed n) = Query.Ret (the seed of the backward system at n);
   rhs (Flow e) = Query.Ask tt (fun a => Query.Ret (demand_transfer EX DD dv e a)) *)
(* Boolean dead values are absent from the computed closed demand, which is least under
   strictness. *)
Definition bool_demand {Cv} : demand_domain bool Cv :=
  DemandDomain bool_lattice bool_agree.   (* agree b u v := b = true -> u = v *)
Definition needed_values {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool) :
  finite_map EX (dvars dv) bool.
(* A total inflationary worklist computes a closed demand for every view and the least closed
   demand under the premise of needed_values_least. It handles duplicate variables by a
   deduplicated finite index while returning the original finite_map carrier. The implementation
   may index node and edge occurrences of closed_system without encodings of N or E. Prove that
   the indexed constraints have exactly the same post-solutions as closed_system. Build indexes
   once. *)
Definition dead_value {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool)
    (x : X) : bool := negb (dget EX bool_lattice (needed_values EX dv) x).
(* Demanded bits: M is a Domains bit mask, dback is its backward transfer per operator, and
   forward facts (ranges) are premises through the `inv` of the agreement theorem. Observable
   bits: dnec holds the bits of each operand that an observing instruction's events expose. *)
Definition observable_bits_view {S O N E X Cv M} (dv : demand_view S O N E X Cv M)
    (payload : E -> list (X * M)) : demand_view S O N E X Cv M :=
  {| dgraph := dgraph dv; ddefs := ddefs dv; dnec := fun e => dnec dv e ++ payload e;
     dback := dback dv; dexit := dexit dv; dlookup := dlookup dv; dvars := dvars dv |}.
(* Composition. View: graph_view with the effects view supplying dnec. Domain: finite pointwise
   lattice over bool or masks. Engine: solve_total. Scheduler: rpo_scheduler of the reverse flow. *)
```

```coq
(* AnalysesDemand.v, dead-code erasure. The transformed program P' runs on the same state type and
   the same graph as the original P, and on an erased edge executes a no-op in place of the
   instruction. This is the setting of Views' two-program theorem `agreement_simulation2`, which
   `dce_sound` instantiates with a closed demand as the solution. *)
Record erasure (S O N E X Cv I : Type) : Type := Erasure {
  er_demand : demand_view S O N E X Cv bool;     (* the original program P *)
  er_graph : graph_view S O N E;                 (* the transformed program P' *)
  er_erased : E -> bool;
  er_instr : E -> option I                       (* the instruction of P on the edge *)
}.
(* The invariant of P: reachable, and under DropUnreadTraps not trapped. *)
Definition er_inv {S O} (pol : trap_policy) (m : semantics S O) (en : endings S) (s : S) : Prop :=
  reachable_state m s /\ match pol with KeepTraps => True | DropUnreadTraps => ~ trapped en s end.
(* The agreement of a state of P and a state of P' at a closed demand: the variables that the
   demand needs hold equal values. *)
Definition er_agree {S O N E X Cv I} (EX : encoding X) (er : erasure S O N E X Cv I)
    (d : finite_map EX (dvars (er_demand er)) bool) (s t : S) : Prop :=
  agree (demand_agreement EX bool_demand (er_demand er)) d s t.
Record erasure_laws {S O N E X Cv I} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (m' : semantics S O) (en' : endings S) (EX : encoding X) (er : erasure S O N E X Cv I)
    (d : finite_map EX (dvars (er_demand er)) bool) : Prop := {
  er_cfg : cfg (er_graph er) = cfg (dgraph (er_demand er));
  er_view : graph_view_laws m' (er_graph er);
  er_no_stays : forall t l t', ~ stays (er_graph er) t l t';
  (* a kept edge runs the same instruction in both programs, from states that agree at the demand
     that the edge needs *)
  er_kept_forth : forall e s l s1 t, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m s l s1 ->
    taken (dgraph (er_demand er)) s l s1 e -> er_erased er e = false ->
    agree (demand_agreement EX bool_demand (er_demand er))
      (demand_transfer EX bool_demand (er_demand er) e d) s t ->
    exists t', step m' t l t' /\ taken (er_graph er) t l t' e /\ er_agree EX er d s1 t';
  er_kept_back : forall e s t l t1, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m' t l t1 ->
    taken (er_graph er) t l t1 e -> er_erased er e = false ->
    agree (demand_agreement EX bool_demand (er_demand er))
      (demand_transfer EX bool_demand (er_demand er) e d) s t ->
    exists s1, step m s l s1 /\ taken (dgraph (er_demand er)) s l s1 e /\ er_agree EX er d s1 t1;
  (* an erased edge is a silent no-op in P' that leaves every variable alone, and P' can take it
     exactly when P can *)
  er_nop_forth : forall e s l s1 t, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m s l s1 ->
    taken (dgraph (er_demand er)) s l s1 e -> er_erased er e = true ->
    exists t', step m' t nil t' /\ taken (er_graph er) t nil t' e /\
      forall x, dlookup (er_demand er) t' x = dlookup (er_demand er) t x;
  er_nop_back : forall e s t l t1, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m' t l t1 ->
    taken (er_graph er) t l t1 e -> er_erased er e = true ->
    l = nil /\ (forall x, dlookup (er_demand er) t1 x = dlookup (er_demand er) t x) /\
    exists s1 l0, step m s l0 s1 /\ taken (dgraph (er_demand er)) s l0 s1 e;
  (* The three declared endings agree at the demand. Stuck matching follows from these and the
     two-way lock-step matches, without a decision procedure for whether a state can step. *)
  er_ends : forall s t k, k <> EndStuck -> er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> er_agree EX er d s t ->
    (ends_as m en k s <-> ends_as m' en' k t)
}.
(* No reachable state of the original run is trapped. *)
Definition never_traps {S O} (m : semantics S O) (en : endings S) (s0 : S) : Prop :=
  forall tr t, exec m s0 tr t -> ~ trapped en t.
(* Each policy has its own conclusion. KeepTraps: the programs behave the same. DropUnreadTraps:
   a refinement, which holds only when the original run does not trap. *)
Definition dce_conclusion {S O} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (s0 : S) (m' : semantics S O) (en' : endings S) (t0 : S) : Prop :=
  match pol with
  | KeepTraps => same_behaviour m en s0 m' en' t0
  | DropUnreadTraps => never_traps m en s0 -> same_behaviour m en s0 m' en' t0
  end.
```

```coq
(* AnalysesAdce.v. Aggressive dead code elimination: mark what has effects, close under control
   dependence, and keep every loop that may not terminate. `cdep g exits b n` is the control
   dependence of the Graph package: n is control dependent on the branch b. *)
Record adce_input (N E : Type) : Type := AdceInput {
  agraph : Graph.t N E;
  aexits : list N;                   (* the exits, including one node per infinite loop *)
  effectful_node : N -> bool;        (* the node's edges are effectful under the client's policy *)
  may_not_terminate : N -> bool      (* the node lies in a loop that may not terminate *)
}.
Definition adce_marked {N E} (EN : encoding N) (ai : adce_input N E) : FinSet.t N.
(* The least set M supported on Graph.nodes (agraph ai) with: an effectful or possibly
   nonterminating listed node is in M; and a listed b is in M when a listed n is in M and n is
   control dependent on b. Compute it with a worklist over reverse control dependences under the
   premises of adce_closed and adce_least. Build the control-dependence index once. *)
Definition skips_to {N E} (g : Graph.t N E) (marked : N -> bool) (n m : N) : Prop :=
  marked m = true /\ exists es, path g n es m /\
    forall e, In e es -> Graph.target g e = m \/ marked (Graph.target g e) = false.
```

### ANA-5: equality

```coq
(* AnalysesNumbering.v. Pure operations are deterministic functions of their operands (a pure
   operation may still trap: both of two congruent computations then trap together). *)
Record numbering_problem (S O N E V K C : Type) : Type := NumberingProblem {
  nsv : ssa_view S O N E V K C;
  pure : K -> bool;
  nvalues : list V
}.
Definition dominator_numbering {S O N E V K C} (EN : encoding N) (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) : V -> V.
(* leader of x: a depth-first walk of the dominator tree (the tree of Graph's `dominator_tree`,
   whose ancestry implies dominance) with a scoped Table keyed by (operator, leaders of the
   arguments); parameters of one block whose per-edge arguments have equal leaders share one *)
Definition optimistic_numbering {S O N E V K C} (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) : V -> V.
(* the coarsest congruence: start with one class per (operator or block), refine until stable *)
Definition numbering_check {S O N E V K C} (EV : encoding V) (np : numbering_problem S O N E V K C)
    (rep : V -> V) : bool.
(* every class is a congruence: its members are pure Ops of one operator with pairwise same-class
   arguments, or Params of one block (at any positions) such that, for every edge into the block,
   the arguments at the members' positions are same-class; Arbitrary values are alone. Acceptance
   evidence: `dominator_numbering_checked`, `optimistic_numbering_checked`, and the required Example
   `gvn_merges` in ExamplesSsaANA5Test.v, where the producer merges two computations *)
Record loop_info (N : Type) : Type := LoopInfo { header : N; body : N -> bool }.
Record loop_info_wf {N E} (g : Graph.t N E) (lp : loop_info N) : Prop := {
  header_in_body : body lp (header lp) = true;
  header_dominates : forall n, body lp n = true -> dominates g (header lp) n;
  single_entry : forall e, In e (edges_of g) -> body lp (Graph.target g e) = true ->
    body lp (Graph.source g e) = false -> Graph.target g e = header lp
}.
Definition invariant_in {S O N E V K C} (np : numbering_problem S O N E V K C) (lp : loop_info N)
    (x : V) : bool.
(* home x is outside the body, or def x = Op o args with pure o and every argument invariant_in;
   structural on a fuel of length (nvalues np), so a cycle of Ops answers false *)
```

### ANA-6: e-graphs

```coq
(* AnalysesEgraph.v. The external explanation checker validates replay. Equality over typed
   environments compares option results, including None = None for partial operators. A rule
   may carry a decidable side condition on its instance (for example a
   sort test), because `x * 0 -> 0` holds only for integer-sorted `x`. *)
Inductive term (K : Type) : Type := TVar (i : nat) | TApp (o : K) (args : list (term K)).
Definition denote {K C} (ev : K -> list C -> option C) (env : nat -> option C) (t : term K) :
  option C.   (* TVar i = env i; TApp o args = ev o over the denotations of args, None if any is None *)
(* `ok` says which environments are typed: every variable is bound, to a value of its sort. *)
Definition equiv_term {K C} (ev : K -> list C -> option C) (ok : (nat -> option C) -> Prop)
    (t u : term K) : Prop :=
  forall env, ok env -> denote ev env t = denote ev env u.
Definition subst_term {K} (sub : nat -> term K) (t : term K) : term K.
Definition term_vars {K} (t : term K) : list nat.
(* Traverse left to right and return every TVar index, retaining repetitions. *)
Definition legacy_subst {K} (bindings : list (term K)) (i : nat) : term K :=
  match nth_error bindings i with Some t => t | None => TVar i end.
Definition legacy_subst_bound {K} (bindings : list (term K)) (t : term K) : bool :=
  forallb (fun i => Nat.ltb i (length bindings)) (term_vars t).
Record rewrite_rule (K : Type) : Type := RewriteRule {
  rule_lhs : term K;
  rule_rhs : term K;
  rule_side : (nat -> term K) -> bool       (* a side condition on the substitution *)
}.
Definition rule_sound {K C} (ev : K -> list C -> option C) (ok : (nat -> option C) -> Prop)
    (r : rewrite_rule K) : Prop :=
  forall sub, rule_side r sub = true ->
    equiv_term ev ok (subst_term sub (rule_lhs r)) (subst_term sub (rule_rhs r)).
(* One rewrite: at a path of argument indices, apply a rule in either direction. *)
Record rewrite_step (K : Type) : Type := RewriteStep {
  step_pos : list nat;
  step_rule : nat;
  step_forward : bool;
  step_subst : list (term K)           (* the substitution for TVar 0, TVar 1, ... *)
}.
Definition replay {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t : term K)
    (steps : list (rewrite_step K)) : option (term K).
(* Resolve the rule and direction. Reject missing entries for variables in either side. Set sub
   to legacy_subst step_subst, test rule_side on that same function, compare the source at
   step_pos with subst_term sub source using EK, and replace it with subst_term sub target.
   Reject a missing rule, invalid position, failed bound, false guard or source mismatch. Process
   steps in order; the empty list returns the input. Extra bindings remain visible to the guard;
   an absent index outside both sides maps to TVar i. *)
Definition check_explanation {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t u : term K)
    (steps : list (rewrite_step K)) : bool :=
  match replay EK rules t steps with Some v => term_eqb EK v u | None => false end.
Definition term_eqb {K} (EK : encoding K) (t u : term K) : bool.
(* structural equality, comparing operators by their codes under EK *)
Definition term_cost {K} (cost : K -> nat) (t : term K) : nat.   (* the sum of cost over the nodes *)
Definition egraph (K : Type) : Type.     (* hash-consed nodes, a UnionFind of classes; abstract *)
Definition saturate {K} (EK : encoding K) (rules : list (rewrite_rule K)) (fuel : positive)
  (t : term K) : egraph K.   (* direct Rewrite producer; legacy_saturate_direct specifies it *)
Definition extract {K} (cost : K -> nat) (eg : egraph K) (t : term K) :
  option (term K * list (rewrite_step K)).   (* returns a candidate with replayable explanation *)
Definition optimise {K} (EK : encoding K) (rules : list (rewrite_rule K)) (cost : K -> nat)
    (fuel : positive) (t : term K) : option (term K) :=
  match extract cost (saturate EK rules fuel t) t with
  | Some (u, steps) =>
    if check_explanation EK rules t u steps && Nat.leb (term_cost cost u) (term_cost cost t)
    then Some u else None
  | None => None
  end.
(* Acceptance evidence: `egraph_optimise_accepts`, a required Example in ExamplesSsaANA6Test.v on
   which `optimise` returns Some of a strictly cheaper term. *)
```

### ANA-7: scalar evolution

```coq
(* AnalysesScev.v. Invariant expressions: sums and products of loop-invariant values and constants. *)
Inductive iexpr (V : Type) : Type :=
  | IVar (x : V)
  | IConst (z : Z)
  | IAdd (a b : iexpr V)
  | IMul (a b : iexpr V).
Fixpoint eval_iexpr {V} (inv : V -> Z) (e : iexpr V) : Z.
(* IVar x = inv x; IConst z = z; IAdd and IMul are the sum and the product over Z *)
Inductive chrec (V : Type) : Type :=
  | CInv (e : iexpr V)                    (* a loop-invariant expression, read in the entry state *)
  | CRec (base step : chrec V)            (* {b,+,s}: b at 0, plus s(k) from k to k+1 *)
  | CGeo (base ratio : chrec V).          (* {b,*,r}: b at 0, times r(k) from k to k+1 *)
Fixpoint eval_chrec {V} (inv : V -> Z) (c : chrec V) (k : nat) : Z.
(* CInv e = eval_iexpr inv e; for CRec b s: eval b 0 at 0 and eval (CRec b s) k + eval s k at
   S k; CGeo likewise with multiplication. Evaluation is over Z; a word result is its wrap. *)
Definition chrec_add {V} (a b : chrec V) : chrec V.      (* the CR algebra *)
Definition chrec_mul {V} (a b : chrec V) : chrec V.
Definition chrec_scale {V} (z : Z) (c : chrec V) : chrec V.
Inductive cmp_kind : Type := CmpLt | CmpLe | CmpNe.
Inductive signedness : Type := Unsigned | Signed.
(* The value an integer denotes at width w under a signedness. *)
Definition view_z (w : width) (sg : signedness) (a : Z) : Z :=
  let r := wrap w a in
  match sg with
  | Unsigned => r
  | Signed => if (r <? modulus w / 2)%Z then r else (r - modulus w)%Z
  end.
Definition test_holds (w : width) (sg : signedness) (c : cmp_kind) (a b : Z) : Prop :=
  let a' := view_z w sg a in let b' := view_z w sg b in
  match c with CmpLt => (a' < b')%Z | CmpLe => (a' <= b')%Z | CmpNe => a' <> b' end.
(* The values that a width and a signedness can hold without wrapping. *)
Definition in_range (w : width) (sg : signedness) (v : Z) : Prop :=
  match sg with
  | Unsigned => (0 <= v < modulus w)%Z
  | Signed => (- (modulus w / 2) <= v < modulus w / 2)%Z
  end.
(* The exit test of a loop header: `t_lhs c t_bound` holds when the loop continues. *)
Record loop_test (V : Type) : Type := LoopTest {
  t_cmp : cmp_kind; t_sign : signedness; t_lhs : V; t_bound : iexpr V
}.
(* A simple loop: one entry edge from outside the body and one back edge from inside it. *)
Record loop_view (S O N E V K C : Type) : Type := LoopView {
  lssa : ssa_view S O N E V K C;
  lheader : N;
  lbody : N -> bool;
  lentry : E;
  lback : E;
  ltest : option (loop_test V)
}.
Record scev_ops (K C : Type) : Type := ScevOps {
  width_of : width;
  to_Z : C -> Z;
  add_op : K -> bool;
  mul_op : K -> bool;
  const_op : K -> option Z
}.
Record scev_ops_laws {K C} (so : scev_ops K C) (op_eval : K -> list C -> option C) : Prop := {
  add_laws : forall o a b r, add_op so o = true -> op_eval o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (to_Z so a + to_Z so b);
  mul_laws : forall o a b r, mul_op so o = true -> op_eval o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (to_Z so a * to_Z so b);
  const_laws : forall o z r, const_op so o = Some z -> op_eval o nil = Some r ->
    to_Z so r = wrap (width_of so) z
}.
(* The invariants' values, read in the state s. *)
Definition inv_env {S O N E V K C} (lv : loop_view S O N E V K C) (so : scev_ops K C) (s : S)
    (y : V) : Z :=
  match val (lssa lv) s y with Some d => to_Z so d | None => 0%Z end.
(* Arrivals at the header during the current stay, as a function of the run prefix: Views'
   `arrivals_since`, where the entry edge resets the count and the back edge adds one. *)
Definition stay_arrivals {S O N E V K C} (EE : encoding E) (lv : loop_view S O N E V K C)
    (es : list E) : nat :=
  arrivals_since (fun e => Pos.eqb (encode EE e) (encode EE (lentry lv)))
    (fun e => Pos.eqb (encode EE e) (encode EE (lback lv))) es.
Record loop_view_laws {S O N E V K C} (m : semantics S O) (so : scev_ops K C)
    (lv : loop_view S O N E V K C) : Prop := {
  l_ssa : ssa_view_laws m (lssa lv);
  l_strict : strict_ssa_laws m (lssa lv);
  l_header_not_entry : ~ In (lheader lv) (Graph.entries (cfg (base (lssa lv))));
  l_entry_edge : In (lentry lv) (edges_of (cfg (base (lssa lv)))) /\
    Graph.target (cfg (base (lssa lv))) (lentry lv) = lheader lv /\
    lbody lv (Graph.source (cfg (base (lssa lv))) (lentry lv)) = false;
  l_back_edge : In (lback lv) (edges_of (cfg (base (lssa lv)))) /\
    Graph.target (cfg (base (lssa lv))) (lback lv) = lheader lv /\
    lbody lv (Graph.source (cfg (base (lssa lv))) (lback lv)) = true;
  l_simple : forall e, In e (edges_of (cfg (base (lssa lv)))) ->
    Graph.target (cfg (base (lssa lv))) e = lheader lv -> e = lentry lv \/ e = lback lv;
  (* the back edge is taken only when the exit test holds *)
  l_back_test : forall s l s' t, reachable_state m s -> point (base (lssa lv)) s = lheader lv ->
    step m s l s' -> taken (base (lssa lv)) s l s' (lback lv) -> ltest lv = Some t ->
    exists c, val (lssa lv) s (t_lhs t) = Some c /\
      test_holds (width_of so) (t_sign t) (t_cmp t) (to_Z so c) (eval_iexpr (inv_env lv so s) (t_bound t))
}.
Definition recognise {S O N E V K C} (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V) :
  option (chrec V).
(* x is a parameter of the header whose back-edge argument is x plus (or times) an invariant or a
   recognised value; its base is the entry-edge argument. A value is invariant when its home lies
   outside the body; the CR algebra handles the operators. *)
Definition trip_count {V} (inv : V -> Z) (w : width) (sg : signedness) (c : cmp_kind)
    (ch : chrec V) (bound : iexpr V) : option N.
(* the first k at which the test `eval_chrec inv ch k  c  eval_iexpr inv bound` (read at w under sg)
   fails, as a binary natural, when ch is an affine {b,+,s} whose step s is a constant and the
   bound is finite in Z; None otherwise *)
Definition nowrap_check {V} (w : width) (sg : signedness) (inv : V -> Z) (ch : chrec V)
    (bound : iexpr V) (t : N) : bool.
(* separate evidence: eval ch k for every k <= t, and the bound, lie inside the range of w under
   sg, by interval arithmetic on the base, the step and t. Acceptance evidence:
   `scev_count_up_trip`, a required Example in ExamplesSsaANA7Test.v *)
```

### ANA-8: calls

```coq
(* AnalysesCalls.v *)
Definition resolver {P F V A} (direct : P -> option F) (callee_val : P -> option V)
    (fact : V -> A) (fns : A -> option (list F)) (all : list F) (p : P) : list F :=
  match direct p with
  | Some f => [f]
  | None => match callee_val p with
            | Some v => match fns (fact v) with Some l => l | None => all end
            | None => all
            end
  end.
Definition recursive {F P} (g : Graph.t F (call_edge F P)) (f : F) : Prop :=
  exists e es, In e (Graph.out g f) /\ path g (Graph.target g e) es f.
(* Summaries are instances of the summary engine of VIEW-6 *)
Definition purity_spec {S F P} (cv : calls_view S F P) (impure_local : F -> bool) :
  summary_spec F P bool.        (* A = bool (may be impure); local = impure_local; via_call _ _ a = a *)
Definition purity_cover {S O I H} (ev : effects_view S I H) : step_cover S O bool :=
  {| step_covers := fun b s l s' => b = false -> l = nil /\ heap ev s' = heap ev s |}.
Record frame_weights (F : Type) : Type := FrameWeights { weight : F -> nat }.
Definition stack_demand {S F P} (cv : calls_view S F P) (g : Graph.t F (call_edge F P))
    (fw : frame_weights F) (f : F) : option nat.
(* None when f can reach a cycle of the call graph; else the maximum, over paths from f in the
   condensation DAG, of the sum of weight (DAG max-weight paths of Graph) *)
Definition stack_above {S F P} (cv : calls_view S F P) (fw : frame_weights F) (f : F) (s : S) : nat.
(* the sum of weight over the frames of s from the innermost up to the topmost activation of f *)
Definition callee_leaf {S F P} (cv : calls_view S F P) (f : F) : bool :=
  match sites_of cv f with nil => true | _ => false end.   (* callee shape: no call site *)
(* Call strings as unknowns: contexts are the last k call sites. *)
Definition push_ctx {P} (k : nat) (p : P) (c : list P) : list P := firstn k (p :: c).
Definition callstring_system {S F P A} (k : nat) (cv : calls_view S F P) (resolve : P -> list F)
    (sp : summary_spec F P A) :
  System.t (F * list P) (summary_constraint F P * list P) A.
(* one SLocal f per (f, c) and one SCall p g per (caller_of p, c): target (caller_of p, c), rhs =
   Query.Ask (g, push_ctx k p c) (via_call sp p g). Static: deps (SCall p g, c) =
   [(g, push_ctx k p c)]. Composition: solve_total over the condensation (scc_scheduler) with
   Joining when slat has a height (purity: bool_lattice), solve_fuel with a top otherwise *)
Definition ctx_of {S F P} (cv : calls_view S F P) (k : nat) (s : S) (i : nat) : list P.
(* the context of the i-th frame from the innermost: the last k sites of the frames below it *)
(* Interprocedural constants: the join over the call sites of the facts of the actual
   arguments. `actuals p` are the argument values at site p, `formals f` the parameters. *)
Record args_view (S F P V C : Type) : Type := ArgsView {
  actuals : P -> list V;
  formals : F -> list V;
  frame_val : S -> V -> option C         (* the innermost frame's values *)
}.
(* The callers of a function, indexed once: callee -> the call sites whose resolver may name it. *)
Definition callers_index {S F P} (EF : encoding F) (cv : calls_view S F P) (resolve : P -> list F) :
  Map.t F (list P).
(* one pass over every site p of every function and every g in resolve p, appending p to g's list *)
Definition callers_of {F P} (EF : encoding F) (ix : Map.t F (list P)) (f : F) : list P :=
  match Map.get EF f ix with Some l => l | None => nil end.
Definition arg_fact {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) (f : F) (i : nat) : A :=
  fold_left (join L)
    (flat_map (fun p => match nth_error (actuals av p) i with Some x => [fact x] | None => nil end)
       (callers_of EF ix f))
    (bot L).
```

### ANA-9: points-to

```coq
(* AnalysesPointsTo.v. Pointer-relevant instructions, seen through a memory view. A pointer value c
   denotes the allocation `loc_of s c` (an identity of type `L`) at the offset `loc_offset s c`
   (VIEW-7), and a byte is addressed by a pointer value. *)
Inductive ptr_op (V T : Type) : Type :=
  | PAlloc (x : V) (site : T)            (* x holds a fresh pointer from the site *)
  | PCopy (x y : V)                      (* x = y, a pointer-preserving operation of y, a callee
                                            parameter bound to an actual, or a call result bound to
                                            a returned value *)
  | PLoad (x p : V)                      (* x = *p *)
  | PStore (p y : V)                     (* *p = y *)
  | PEscape (x : V).                     (* x goes to unknown code, or is global *)
Inductive pts_key (V T : Type) : Type := PVal (x : V) | PHeap (t : T).
(* The sites an analysis can name: those of the allocations in ops, once each. *)
Definition site_universe {V T} (ET : encoding T) (ops : list (ptr_op V T)) : list T :=
  FinSet.elements (FinSet.of_list ET
    (flat_map (fun op => match op with PAlloc _ t => [t] | _ => nil end) ops)).
Definition pts_set {V T} (ET : encoding T) (ops : list (ptr_op V T)) : Type :=
  finite_set ET (site_universe ET ops).
Definition pts_lattice {V T} (ET : encoding T) (ops : list (ptr_op V T)) :
    lattice (pts_set ET ops) := finite_powerset_lattice ET (site_universe ET ops).
Definition andersen_system {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  System.t (pts_key V T) nat (pts_set ET ops).
(* One constraint per instruction, indexed by its position in ops (constraints = seq 0 (length ops)),
   over pts_lattice ET ops, with U = site_universe ET ops:
   PAlloc x t  : target PVal x, rhs Query.Ret {t}
   PCopy x y   : target PVal x, rhs Query.Ask (PVal y) (fun a => Query.Ret a)
   PLoad x p   : target PVal x, rhs Query.Ask (PVal p) (fun a => ask_all (map PHeap (elements a))
                 (fun bs => Query.Ret (the union of bs)))
   PStore p y  : target PVal p, rhs Query.Ask (PVal p) (fun a => Query.Ask (PVal y) (fun b =>
                 Query.Side (PHeap t) b q for each t in a, in turn, ending in Query.Ret bot))
   PEscape x   : target PVal x, rhs Query.Ret bot *)
Definition andersen_static {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  System.static (andersen_system EV ET ops).
(* deps: PLoad x p reads PVal p and every PHeap t with t in the universe; PStore p y reads PVal p
   and PVal y; PCopy x y reads PVal y; the others read nothing. side_targets: PStore contributes
   to every PHeap t with t in the universe; the others to nothing. The reads and contributions are
   the over-approximations that reads_within and sides_within need. *)
(* Composition. Domain: finite_powerset_lattice over site_universe (NoDup). Engine: solve_total,
   Joining, evidence `inhabits (base_height (finite_powerset_height ET U _))`, scheduler rpo_scheduler (the
   widening points are unused under Joining). The solved system is static, so its result is also
   checkable by cut points. *)
Record ptr_view (S V C L T : Type) : Type := PtrView {
  pmem : mem_view S V C L T;
  pval : S -> V -> option C;
  pop : S -> list (ptr_op V T);            (* the pointer effects of the next step; a call lists one
                                              PCopy per bound parameter, a return one per result *)
  held : S -> C -> option C;               (* the pointer value stored at the address that a pointer
                                              value denotes *)
  pbyte : S -> C -> option nat              (* the byte at the address that a pointer value denotes *)
}.
(* The site a value points into, and the sites that a block of a site holds pointers to. *)
Definition pts_of {S V C L T} (pv : ptr_view S V C L T) (s : S) (x : V) : option T :=
  match pval pv s x with
  | Some c => match loc_of (pmem pv) s c with
              | Some l => loc_site (pmem pv) s l
              | None => None
              end
  | None => None
  end.
Definition heap_pts {S V C L T} (pv : ptr_view S V C L T) (s : S) (t0 t : T) : Prop :=
  exists c c' l l', loc_of (pmem pv) s c = Some l /\ loc_site (pmem pv) s l = Some t0 /\
    held pv s c = Some c' /\ loc_of (pmem pv) s c' = Some l' /\ loc_site (pmem pv) s l' = Some t.
Record ptr_view_laws {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (ops : list (ptr_op V T)) : Prop := {
  pop_listed : forall s op, reachable_state m s -> In op (pop pv s) -> In op ops;
  pts_initial : forall s x t, initial m s -> pts_of pv s x = Some t -> False;
  heap_initial : forall s t0 t, initial m s -> heap_pts pv s t0 t -> False;
  pts_origin : forall s l s' x t, reachable_state m s -> step m s l s' ->
    pts_of pv s' x = Some t ->
    pts_of pv s x = Some t \/ In (PAlloc x t) (pop pv s) \/
    (exists y, In (PCopy x y) (pop pv s) /\ pts_of pv s y = Some t) \/
    (exists p t0, In (PLoad x p) (pop pv s) /\ pts_of pv s p = Some t0 /\ heap_pts pv s t0 t);
  heap_origin : forall s l s' t0 t, reachable_state m s -> step m s l s' ->
    heap_pts pv s' t0 t -> heap_pts pv s t0 t \/
    (exists p y, In (PStore p y) (pop pv s) /\ pts_of pv s p = Some t0 /\ pts_of pv s y = Some t)
}.
Record steens_result (V : Type) : Type := SteensResult {
  classes : UnionFind.t positive;
  pointee : V -> positive                  (* the class of what the value points to *)
}.
Definition may_alias {V} (r : steens_result V) (x y : V) : Prop :=
  UnionFind.equiv positive_encoding (classes r) (pointee r x) (pointee r y).
Definition steensgaard {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  steens_result V.
(* unify pointee classes: PAlloc x t with the class of site t; PCopy x y the pointees of x and y;
   PLoad x p the pointee of x with what p's pointee holds; PStore p y likewise *)
Definition escaped_sites {V T} (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) : FinSet.t T.
(* the least set containing sigma (PVal x) for every PEscape x in ops, closed under
   t in the set and t' in sigma (PHeap t) implies t' in the set *)
(* Zero-initialised bytes: a may-analysis of the bytes that may have been written. Before any
   block exists the fact is empty, which is vacuous; an allocation writes nothing (a fresh block is
   zero); every other edge adds the ranges it may write, frees and callee writes included. *)
Definition write_universe {S O N E T} (EF : encoding (footprint T)) (gv : graph_view S O N E)
    (fp : E -> list (footprint T)) : list (footprint T) :=
  FinSet.elements (FinSet.of_list EF (flat_map fp (edges_of (cfg gv)))).
Definition written_set {S O N E T} (EF : encoding (footprint T)) (gv : graph_view S O N E)
    (fp : E -> list (footprint T)) : Type := finite_set EF (write_universe EF gv fp).
Definition zero_written_system {S O N E T} (EF : encoding (footprint T)) (gv : graph_view S O N E)
    (fp : E -> list (footprint T)) :
  System.t N (dense_constraint N E) (written_set EF gv fp) :=
  forward_system (cfg gv)
    (fun _ => finite_clamp EF (write_universe EF gv fp) FinSet.empty)
    (fun e a => finite_clamp EF (write_universe EF gv fp)
                  (FinSet.union EF (proj1_sig a) (FinSet.of_list EF (fp e)))).
(* Composition. Domain: finite_powerset_lattice over write_universe (the footprints that occur).
   Engine: solve_total, Joining, forward_static. Scheduler: rpo_scheduler. `EF` is
   `footprint_encoding ET`, asked of Domains. *)
Record zero_laws {S O N E V C L T} (m : semantics S O) (gv : graph_view S O N E)
    (pv : ptr_view S V C L T) (fp : E -> list (footprint T)) : Prop := {
  z_view : graph_view_laws m gv;
  z_no_stays : forall s l s', ~ stays gv s l s';
  (* before any step, every existing block reads zero (usually: there is none) *)
  z_init : forall s c l0 t n, initial m s -> loc_of (pmem pv) s c = Some l0 ->
    loc_site (pmem pv) s l0 = Some t -> pbyte pv s c = Some n -> n = 0;
  (* a block that a step creates is zero-filled *)
  z_fresh : forall s l s' e c l0 t n, reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    loc_of (pmem pv) s c = None -> loc_of (pmem pv) s' c = Some l0 ->
    loc_site (pmem pv) s' l0 = Some t -> pbyte pv s' c = Some n -> n = 0;
  (* a byte that the edge may not write keeps a zero value *)
  z_kept : forall s l s' e c l0 t, reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    loc_of (pmem pv) s c = Some l0 -> loc_site (pmem pv) s l0 = Some t ->
    ~ covered (fp e) t (loc_offset (pmem pv) s c) 1 ->
    (forall n, pbyte pv s c = Some n -> n = 0) -> forall n, pbyte pv s' c = Some n -> n = 0
}.
```

### ANA-10a and ANA-10e: legacy memory contracts

C23 retires the unimplemented `build_memory_ssa` with its old signature. ANA-10c and ANA-10d
provide the directly proved frontier/rename and sealed-block producer contracts; ANA-10e retains
the legacy candidate type, external checker and conditional byte-preservation projection.

```coq
(* AnalysesMemoryBase.v. Byte-range facts use Domains' `range_must ET`, whose reached facts carry
   canonical footprints. Unreached means every byte of every site (the bottom, vacuous).
   `range_must_lattice ET` orders facts by reverse coverage, with join = intersection;
   `range_must_top ET` is `range_reached ET nil`; `range_add ET fs a` adds
   ranges, `range_remove ET fs a` removes the bytes that fs overlaps, `range_covers a t o w` says
   that all w bytes at offset o of the site t are covered. The lattice has no height, so
   every system below runs under `solve_fuel` with `range_must_top` as the fallback.
   Validated accesses until a barrier. `accessible s t o w`: the w bytes at offset o of some block
   of the site t can be accessed in s. *)
Record barrier_view (S O N E T : Type) : Type := BarrierView {
  bgraph : graph_view S O N E;
  validates : E -> list (footprint T);       (* ranges that the edge's successful access validates *)
  barrier : E -> bool;                       (* the edge frees, resizes, or calls what may free *)
  accessible : S -> T -> Z -> nat -> Prop
}.
(* accessible_bytes is a client obligation: the whole positive-width range is accessible in one
   allocation. Individual bytes witnessed by different allocations do not imply this property. *)
Record barrier_laws {S O N E T} (m : semantics S O) (bv : barrier_view S O N E T) : Prop := {
  b_view : graph_view_laws m (bgraph bv);
  b_no_stays : forall s l s', ~ stays (bgraph bv) s l s';
  validates_accessible : forall s l s' e f, reachable_state m s -> step m s l s' ->
    taken (bgraph bv) s l s' e -> In f (validates bv e) ->
    accessible bv s' (fp_site f) (fp_lo f) (Z.to_nat (fp_hi f - fp_lo f));
  accessible_persists : forall s l s' e t o w, reachable_state m s -> step m s l s' ->
    taken (bgraph bv) s l s' e -> barrier bv e = false -> accessible bv s t o w ->
    accessible bv s' t o w;
  accessible_sub : forall s t o w o' w', reachable_state m s -> accessible bv s t o w ->
    (o <= o')%Z -> (o' + Z.of_nat w' <= o + Z.of_nat w)%Z -> accessible bv s t o' w';
  accessible_bytes : forall s t o w, reachable_state m s -> (0 < w)%nat ->
    (forall k, (o <= k < o + Z.of_nat w)%Z -> accessible bv s t k 1) ->
    accessible bv s t o w
}.
Definition validated_system {S O N E T} (ET : encoding T) (bv : barrier_view S O N E T) :
  System.t N (dense_constraint N E) (range_must ET) :=
  forward_system (cfg (bgraph bv)) (fun _ => range_reached ET nil)
    (fun e a => range_add ET (validates bv e) (if barrier bv e then range_reached ET nil else a)).
(* Composition. Domain: range_must_lattice ET. Engine: solve_fuel, top = range_must_top ET,
   forward_static. *)
(* Dead stores: a backward must-analysis over byte ranges. `overwrites e` are the ranges the edge
   certainly writes and `mreads e` those it may read or let escape; `sagree a s t`: the memories
   of s and t agree outside the ranges a. *)
Record store_view (S O N E T : Type) (ET : encoding T) : Type := StoreView {
  sgraph : graph_view S O N E;
  overwrites : E -> list (footprint T);
  mreads : E -> list (footprint T);
  sagree : agreement (range_must ET) S
}.
Definition dead_store_transfer {S O N E T} (ET : encoding T) (sv : store_view S O N E T ET) (e : E)
    (a : range_must ET) : range_must ET :=
  range_add ET (overwrites sv e) (range_remove ET (mreads sv e) a).
Definition dead_store_system {S O N E T} (ET : encoding T) (sv : store_view S O N E T ET) :
  System.t N (dense_constraint N E) (range_must ET) :=
  backward_system (cfg (sgraph sv)) (fun _ => range_reached ET nil) (dead_store_transfer ET sv).
Record store_laws {S O N E T} (m : semantics S O) (en : endings S) (ET : encoding T)
    (sv : store_view S O N E T ET) : Prop := {
  s_view : graph_view_laws m (sgraph sv);
  s_no_stays : forall s l s', ~ stays (sgraph sv) s l s';
  s_agreement : agreement_laws (range_must_lattice ET) (sagree sv) /\ agreement_symmetric (sagree sv);
  s_step : step_agrees m (sgraph sv) (sagree sv) (reachable_state m) (dead_store_transfer ET sv);
  s_ends : ends_agree m en (sgraph sv) (sagree sv) (reachable_state m)
    (fun _ => range_reached ET nil)
}.
(* Bytes: what a node may write, and the byte at an offset of an allocation. A write is anything
   that changes a byte: a store, an allocation (which creates its bytes), a free (which removes
   them) and every write of a callee. *)
Record bytes_view (S O N E T L : Type) : Type := BytesView {
  bgv : graph_view S O N E;
  writes_at : N -> list (footprint T);
  bsite : S -> L -> option T;  (* historical site of an allocation identity, retained after free *)
  byte : S -> L -> Z -> option nat
}.
Record bytes_laws {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L) : Prop := {
  by_view : graph_view_laws m (bgv bv);
  by_no_stays : forall s l s', ~ stays (bgv bv) s l s';
  byte_site_stable : forall s l s' l0 t, reachable_state m s -> step m s l s' ->
    bsite bv s l0 = Some t -> bsite bv s' l0 = Some t;
  byte_frame : forall s l s' l0 t o, reachable_state m s -> step m s l s' ->
    bsite bv s l0 = Some t -> byte bv s' l0 o <> byte bv s l0 o ->
    covered (writes_at bv (point (bgv bv) s)) t o 1
}.
(* AnalysesMemoryLegacy.v: the external-candidate boundary. A memory node carries its function. *)
Inductive mem_node (F N : Type) : Type := MDef (f : F) (n : N) | MLive (f : F).
Record memory_ssa (F N : Type) : Type := MemorySSA {
  def_of_load : N -> option (mem_node F N)    (* the memory definition a load reads *)
}.
Definition no_clobber_check {F N E T} (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F)
    (g : Graph.t N E) (writes reads : N -> list (footprint T)) (ms : memory_ssa F N) : bool.
(* Candidate loads and definitions must be reachable graph nodes. The exact all-walk domain and
   disjointness test are specified by ANA-10e below. *)
(* Ranges that cannot overlap: no two footprints of one site have intersecting byte ranges. *)
Definition footprints_disjoint {T} (ET : encoding T) (F G : list (footprint T)) : bool :=
  forallb (fun f => forallb (fun g =>
    negb (Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site g))) ||
    Z.leb (fp_hi f) (fp_lo g) || Z.leb (fp_hi g) (fp_lo f)) G) F.
Definition invariant_load {S O N E V K C T} (ET : encoding T)
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (addr : V)
    (loop_writes : list (footprint T)) (load : footprint T) : bool :=
  invariant_in np lp addr && footprints_disjoint ET loop_writes [load].
(* the loop's writes include those of its callees, by their mod summaries *)
```

### ANA-11: the same analyses as Rules programs

```coq
(* AnalysesRules.v. From Gaulois.Rules, assumed: `program P` is a stratified list of rules
   over predicate symbols with an encoding and arities; `ground_atom P` is a predicate with a
   tuple of codes; `solve_program prog facts` is the engine's database (None if the program
   is not stratifiable); `db_holds prog db p ts` tests a tuple; `least_model` is the
   declarative model. *)
Inductive pred : Type :=
  | PUse | PDef | PSucc | PNec | PDep | PExitUse        (* input facts *)
  | PLive | PNeeded | PReaches.                          (* derived facts *)
Definition pred_encoding : encoding pred.     (* the constructors in the order above, codes 1 to 9 *)
Definition pred_arity (p : pred) : nat :=
  match p with
  | PUse | PDef | PNec | PExitUse | PLive | PNeeded => 2
  | PSucc | PDep | PReaches => 3
  end.
Definition args2 {A B} (EA : encoding A) (EB : encoding B) (a : A) (b : B) : list positive :=
  [encode EA a; encode EB b].
Definition args3 {A B C} (EA : encoding A) (EB : encoding B) (EC : encoding C) (a : A) (b : B)
    (c : C) : list positive := [encode EA a; encode EB b; encode EC c].
(* The facts range over `nodes` and `edges_of` of the graph, so that a node or edge that is not in
   the graph contributes none. *)
Definition extract_live_facts {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) : list (ground_atom pred).
(* use(e,x) for e in edges_of g and x in uses vv e; def(e,x) for x in defs vv e; succ(n,e,n') for
   n in nodes g, e in out n and n' = target e; exituse(n,x) for n in nodes g and x in exit_uses vv n *)
Definition extract_needed_facts {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) : list (ground_atom pred).
(* def(e,x) for e in edges_of g and x in ddefs dv e; nec(e,x) for (x,true) in dnec dv e;
   dep(e,x,y) for x in ddefs dv e and (y,true) in dback dv e x true; succ(n,e,n') as above;
   exituse(n,x) for n in nodes g and (x,true) in dexit dv n *)
Definition v (i : nat) : RulesSyntax.term := RulesSyntax.TVar i.
Definition atm (p : pred) (ts : list RulesSyntax.term) : RulesSyntax.atom pred :=
  RulesSyntax.Atom p ts.
Definition liveness_program : program pred :=
  Program pred_encoding pred_arity
    [ (* K1  live(n,x) :- succ(n,e,n'), use(e,x). *)
      Rule (atm PLive [v 0; v 1])
        [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PUse [v 2; v 1])];
      (* K1' live(n,x) :- exituse(n,x). *)
      Rule (atm PLive [v 0; v 1]) [LPos (atm PExitUse [v 0; v 1])];
      (* K2  live(n,x) :- succ(n,e,n'), live(n',x), !def(e,x). *)
      Rule (atm PLive [v 0; v 1])
        [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PLive [v 3; v 1]);
         LNeg (atm PDef [v 2; v 1])] ].
Definition neededness_program : program pred :=
  Program pred_encoding pred_arity
    [ (* N1  needed(n,x) :- succ(n,e,n'), nec(e,x). *)
      Rule (atm PNeeded [v 0; v 1])
        [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PNec [v 2; v 1])];
      (* N1' needed(n,x) :- exituse(n,x). *)
      Rule (atm PNeeded [v 0; v 1]) [LPos (atm PExitUse [v 0; v 1])];
      (* N2  needed(n,x) :- succ(n,e,n'), needed(n',x), !def(e,x). *)
      Rule (atm PNeeded [v 0; v 1])
        [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PNeeded [v 3; v 1]);
         LNeg (atm PDef [v 2; v 1])];
      (* N3  needed(n,y) :- succ(n,e,n'), def(e,x), dep(e,x,y), needed(n',x). *)
      Rule (atm PNeeded [v 0; v 1])
        [LPos (atm PSucc [v 0; v 2; v 3]); LPos (atm PDef [v 2; v 4]);
         LPos (atm PDep [v 2; v 4; v 1]); LPos (atm PNeeded [v 3; v 4])] ].
Definition reaching_program : program pred :=
  Program pred_encoding pred_arity
    [ (* R1  reaches(e,x,n') :- def(e,x), succ(n,e,n'). *)
      Rule (atm PReaches [v 0; v 1; v 2])
        [LPos (atm PDef [v 0; v 1]); LPos (atm PSucc [v 3; v 0; v 2])];
      (* R2  reaches(d,x,n'') :- reaches(d,x,n), succ(n,e,n''), !def(e,x). *)
      Rule (atm PReaches [v 0; v 1; v 2])
        [LPos (atm PReaches [v 0; v 1; v 3]); LPos (atm PSucc [v 3; v 4; v 2]);
         LNeg (atm PDef [v 4; v 1])] ].
(* The lattice fact that the engine's database gives: the variables x with live(n,x) in db, and so on. *)
Definition live_of_db {S O N E X Cv} (EN : encoding N) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) (n : N) : live_set EX vv :=
  finite_clamp EX (var_universe EX vv)
    (FinSet.of_list EX (filter (fun x =>
       db_holds liveness_program db PLive (args2 EN EX n x)) (var_universe EX vv))).
Definition needed_of_db {S O N E X Cv} (EN : encoding N) (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) (db : database pred) (n : N) :
    finite_map EX (dvars dv) bool :=
  finite_map_clamp EX (dvars dv)
    (Map.of_list EX (map (fun x => (x, true)) (filter (fun x =>
       db_holds neededness_program db PNeeded (args2 EN EX n x)) (dvars dv)))).
Definition reach_of_db {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) (n : N) : reach_set EX EE vv :=
  finite_clamp (pair_encoding EX EE) (reach_universe EX EE vv)
    (FinSet.of_list (pair_encoding EX EE) (filter (fun xd =>
       db_holds reaching_program db PReaches (args3 EE EX EN (snd xd) (fst xd) n))
       (reach_universe EX EE vv))).
```

## Theorems

### ANA-1

```coq
(** The live-set agreement is an agreement: reflexive, antitone in the set, and symmetric. *)
Theorem live_agreement_laws {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  agreement_laws (live_lattice EX vv) (live_agreement EX vv) /\
  agreement_symmetric (live_agreement EX vv).
(** The universe covers the view: every variable the view mentions is in it, and it has no
    duplicates, so the lattice has a height. *)
Theorem var_universe_covers {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  NoDup (var_universe EX vv) /\
  (forall e x, In e (edges_of (cfg (gview vv))) -> In x (uses vv e ++ defs vv e) ->
     In x (var_universe EX vv)) /\
  (forall n x, In n (Graph.nodes (cfg (gview vv))) -> In x (exit_uses vv n) ->
     In x (var_universe EX vv)).
(** Liveness: two runs from initial states that agree on the live-in set at their common point
    behave identically, with the same events, traps, stops and termination. *)
Theorem liveness_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (vv : var_view S O N E X Cv) (sigma : N -> live_set EX vv) (s0 t0 : S) :
  var_view_laws m en vv ->
  post_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  initial m s0 -> initial m t0 -> point (gview vv) t0 = point (gview vv) s0 ->
  (forall x, fmem EX x (sigma (point (gview vv) s0)) = true -> vget vv s0 x = vget vv t0 x) ->
  same_behaviour m en s0 m en t0.
```
Proof idea: `agreement_same_behaviour` with `R := fun _ => live_agreement EX vv`,
`inv := reachable_state m`, `bt := liveness_transfer EX vv`; `step_agrees` follows from
`uses_determine` for the edge's inputs and `defs_frame` for the rest; `ends_agree` from
`exits_determine`; the clamp is invisible because `var_universe_covers`. Card: ANA-1.

```coq
(** Reaching definitions, over run prefixes: if an edge is the last writer of x along a run from an
    initial state, the pair of x and that edge is in the fact at the point the run reaches. *)
Theorem reaching_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (EE : encoding E) (vv : var_view S O N E X Cv) (sigma : N -> reach_set EX EE vv) :
  var_view_laws m en vv ->
  post_solution (reach_lattice EX EE vv) (reaching_system EX EE vv) sigma ->
  forall s0 es s x d, initial m s0 -> run_edges m (gview vv) s0 es s ->
    last_writer (fun e y => mentions EX y (defs vv e)) es x = Some d ->
    fmem (pair_encoding EX EE) (x, d) (sigma (point (gview vv) s)) = true.
(** Zero since entry: a variable in the fact still holds the zero it was entered with. *)
Theorem zero_since_entry_sound {S O N E X Cv} (m : semantics S O) (en : endings S)
    (EX : encoding X) (vv : var_view S O N E X Cv) (locals : list X) (zero : Cv)
    (sigma : N -> live_set EX vv) :
  var_view_laws m en vv -> (forall s x, initial m s -> In x locals -> vget vv s x = zero) ->
  post_solution (zero_lattice EX vv) (zero_since_entry_system EX vv locals) sigma ->
  forall s x, reachable_state m s -> fmem EX x (sigma (point (gview vv) s)) = true ->
    vget vv s x = zero.
(** Must-equality: two variables in one class hold equal values. *)
Theorem equality_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (cv : copy_view S O N E X Cv) (sigma : N -> partition EX) :
  var_view_laws m en (cvars cv) ->
  (forall s l s' e x y, reachable_state m s -> step m s l s' ->
     taken (gview (cvars cv)) s l s' e -> In (x, y) (copies cv e) ->
     vget (cvars cv) s' x = vget (cvars cv) s' y) ->
  post_solution (partition_lattice EX) (equality_system EX cv) sigma ->
  forall s x y, reachable_state m s ->
    partition_equiv EX (sigma (point (gview (cvars cv)) s)) x y ->
    vget (cvars cv) s x = vget (cvars cv) s y.
```
Proof idea: reaching definitions by `forward_history_sound` of Views, with the concretisation
"every pair (x, d) with `last_writer .. es x = Some d` is in the fact", read through the run prefix:
the edge of the last write is a taken edge of the graph, so it lies in `reach_universe`; an edge
that writes x makes itself the last writer (`last_writer_snoc`), one that does not keeps the pair
through the transfer, and the post-solution inequality of each edge gives the pair at the next
point. Zero since entry and equality by `forward_invariant_sound` with the concretisations
"every variable of the fact holds zero" and `partition_gamma EX` read through `vget`; `defs_frame`
for kills, `partition_forget_spec` on reached facts and `partition_forget_unreached` at bottom,
the copy hypothesis and
`partition_union_spec` for unions. Card: ANA-1.

```coq
(** Available expressions, over run prefixes: an expression in the fact was computed earlier in
    the run, in a pre-state in which it had the value it has now (and no edge since has changed it). *)
Theorem available_sound {S O N E U C} (m : semantics S O) (en : endings S) (EU : encoding U)
    (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  genkill_laws m en gk ->
  post_solution (avail_lattice EU gk) (available_system EU gk) sigma ->
  forall s0 es s u, initial m s0 -> run_edges m (gkview gk) s0 es s ->
    fmem EU u (sigma (point (gkview gk) s)) = true ->
    exists es1 s1 e es2, es = es1 ++ e :: es2 /\ run_edges m (gkview gk) s0 es1 s1 /\
      run_edges m (gkview gk) s1 (e :: es2) s /\ In u (gen gk e) /\ uval gk s u = uval gk s1 u.
(** Very busy expressions: on every run that ends in a final state, an expression in the fact is
    computed before any edge that kills it. *)
Theorem busy_sound {S O N E U C} (m : semantics S O) (en : endings S) (EU : encoding U)
    (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  genkill_laws m en gk ->
  post_solution (avail_lattice EU gk) (busy_system EU gk) sigma ->
  forall s es t u, reachable_state m s -> run_edges m (gkview gk) s es t -> final en t ->
    fmem EU u (sigma (point (gkview gk) s)) = true ->
    exists es1 e es2, es = es1 ++ e :: es2 /\ In u (gen gk e) /\
      forall e', In e' es1 -> kill gk e' u = false.
```
Proof idea: the first by induction on `run_edges`: the fact after an edge is `(a minus kill) union
gen`, so a member was generated at that edge (`gen_value` keeps its value) or survived it
(`kill_frame`), and the inequality of the taken edge puts it in the fact before; at an entry the
seed is empty. The second by induction on `run_edges`: at a final state no out-edge exists
(`final_exit`), so the seed empties the fact; otherwise the backward inequality of the taken edge
says `u` is generated there or survives the edge. Card: ANA-1.

```coq
(** Lazy code motion, insertions: an accepted result inserts an expression only where it is
    anticipated, so every run that ends in a final state computes it before killing it. *)
Theorem lcm_insert_safe {S O N E U C} {U1 U2 U3 : list U} (m : semantics S O) (en : endings S)
    (EU : encoding U) (gk : genkill_view S O N E U C) (avail : N -> finite_set EU U1)
    (avail2 : N -> finite_set EU U3) (busy : N -> avail_set EU gk) (r : lcm_result E N U) :
  genkill_laws m en gk ->
  post_solution (avail_lattice EU gk) (busy_system EU gk) busy ->
  lcm_check EU gk avail busy avail2 r = true ->
  forall e u s es t, In e (edges_of (cfg (gkview gk))) -> In u (insert r e) ->
    reachable_state m s -> point (gkview gk) s = Graph.target (cfg (gkview gk)) e ->
    run_edges m (gkview gk) s es t -> final en t ->
    exists es1 e' es2, es = es1 ++ e' :: es2 /\ In u (gen gk e') /\
      forall e'', In e'' es1 -> kill gk e'' u = false.
(** Lazy code motion, deletions: in the transformed program, whose view `gk'` also generates the
    inserted expressions, every run that reaches a node whose entry recomputation is deleted
    computed the expression earlier, with the value it has now. *)
Theorem lcm_delete_current {S O N E U C} {U1 U2 : list U} (m' : semantics S O) (en' : endings S)
    (EU : encoding U) (gk gk' : genkill_view S O N E U C) (avail : N -> finite_set EU U1)
    (busy : N -> finite_set EU U2) (avail2 : N -> avail_set EU gk') (r : lcm_result E N U) :
  genkill_laws m' en' gk' -> (forall e, gen gk' e = gen gk e ++ insert r e) -> kill gk' = kill gk ->
  gkview gk' = gkview gk ->
  post_solution (avail_lattice EU gk') (available_system EU gk') avail2 ->
  lcm_check EU gk avail busy avail2 r = true ->
  forall s0 es s n u, initial m' s0 -> run_edges m' (gkview gk') s0 es s ->
    point (gkview gk') s = n -> In n (Graph.nodes (cfg (gkview gk))) -> In u (delete r n) ->
    exists es1 s1 e es2, es = es1 ++ e :: es2 /\ run_edges m' (gkview gk') s0 es1 s1 /\
      run_edges m' (gkview gk') s1 (e :: es2) s /\ In u (gen gk' e) /\
      uval gk' s u = uval gk' s1 u.
```
Proof idea: the first unfolds the first conjunct of `lcm_check` at the edge, which puts `u` in
the anticipated fact at the target, and applies `busy_sound` from the state at that node; the second
unfolds the second conjunct at `n`, which puts `u` in the availability fact of `gk'`, and applies
`available_sound` for `gk'`. Neither theorem restates the check. `lcm_check` takes the anticipated
and available solutions (any engine's) and the extended availability, so the producer stays
untrusted. Acceptance evidence: `while_lcm_accepts`. Card: ANA-1.

### ANA-2

```coq
(** Structured liveness: two runs of the skeleton machine from initial states that agree on the
    live-in set of the root behave identically. *)
Theorem structured_liveness_sound {A G St O X Cv} (EX : encoding X) (C : skeleton_client A G St O)
    (sv : skel_vars A G X) (look : St -> X -> Cv) (prog : stmt A G)
    (sigma : skel_point -> skel_set EX sv prog) (s0 t0 : mstate St) :
  skeleton_client_laws C -> skel_vars_laws C sv look ->
  post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma ->
  initial (skeleton_semantics prog C) s0 -> initial (skeleton_semantics prog C) t0 ->
  (forall x, fmem EX x (sigma (PEntry nil)) = true -> look (store_of s0) x = look (store_of t0) x) ->
  same_behaviour (skeleton_semantics prog C) (skeleton_endings prog C) s0
    (skeleton_semantics prog C) (skeleton_endings prog C) t0.
```
Proof idea: `skeleton_agreement_bisimulation` with `Ra := live_agreement` read through `look`; the
per-action lemma is `atom_agrees`, `guard_agrees` and `jump_keeps` with `jump_total` of
`skeleton_client_laws` (the other run can take the same jump), and the trap premise is `trap_agrees`
and `guard_agrees`; then
`bisimilar_same_behaviour`. Card: ANA-2.

```coq
(** A loop certificate that the checker accepts extends to a post-solution with those head facts;
    conversely every post-solution restricts to an accepted certificate. *)
Theorem certificate_sound {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (cert : certificate EX sv prog) :
  certificate_check EX sv prog cert = true ->
  exists sigma, post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma /\
    certificate_of EX sv prog sigma = cert.
Theorem certificate_complete {A G X} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (sigma : skel_point -> skel_set EX sv prog) :
  post_solution (skel_lattice EX sv prog) (structured_liveness_system EX sv prog) sigma ->
  certificate_check EX sv prog (certificate_of EX sv prog sigma) = true.
(** Replaying through an observer succeeds exactly when the certificate is accepted. *)
Theorem replay_live_iff {A G X Ob} (EX : encoding X) (sv : skel_vars A G X) (prog : stmt A G)
    (cert : certificate EX sv prog) (obs : Ob -> skel_point -> skel_set EX sv prog -> Ob) (z : Ob) :
  (exists r, replay_live EX sv prog cert obs z = Some r) <->
  certificate_check EX sv prog cert = true.
(** The region table agrees with `summarise` at every valid position. *)
Theorem region_table_agrees {A G R} (alg : summary_algebra A G R) (prog : stmt A G) (p : position) :
  Map.get position_encoding p (region_table alg prog) =
  match sub prog p with Some s => Some (summarise alg s) | None => None end.
Theorem occurrence_census_exact {A G V} (EV : encoding V) (uses : A -> list V)
    (prog : stmt A G) (v : V) :
  (match Map.get EV v (occurrence_census EV uses prog) with
   | Some n => n | None => 0%N end) =
  N.of_nat (length (filter (fun x => Pos.eqb (encode EV x) (encode EV v))
    (concat (map uses (census_atoms prog))))).
```
Proof idea: the checker tests that the certificate's keys are exactly the loop heads, recomputes
every other point from the head facts in one pass over the skeleton (`skeleton_cut_points`
guarantees that this pass is acyclic, by `plan_valid` of Fixpoint), and compares the head values
with
the recomputed ones; completeness follows because a post-solution restricted to the heads is a
valid certificate (`expand_complete` of Fixpoint, with the monotonicity of the transfers); the
region table is one post-order traversal, proved by structural induction on the statement.
Card: ANA-2.

### ANA-3

```coq
(** A numeric domain with sound abstract operators and a bridge from the client's operators to
    Bits makes a sparse domain with the laws that VIEW-4 needs. *)
Theorem sparse_of_numeric_laws {A K C} (ND : numeric_domain A) (G : concretisation A word)
    (br : op_bridge K C) (top : A) (truth : C -> bool) (op_eval : K -> list C -> option C) :
  numeric_laws ND G -> op_bridge_laws br op_eval truth ->
  (forall w z, is_word w z -> gamma G top (w, z)) -> leb (lat ND) top (bot (lat ND)) = false ->
  sparse_domain_laws (sparse_of_numeric ND G br top) truth op_eval.
(** Value analyses: constants, known bits, wrapping intervals and their reduced products are all
    sound on every client whose SSA view satisfies the laws. *)
Theorem numeric_value_sound {S O N E V K C A} (EN : encoding N) (EV : encoding V)
    (m : semantics S O) (ND : numeric_domain A)
    (G : concretisation A word) (br : op_bridge K C) (top : A) (sv : ssa_view S O N E V K C)
    (vals : list V) (entry : V -> A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m sv -> numeric_laws ND G -> op_bridge_laws br (op_eval sv) (truth sv) ->
  (forall w z, is_word w z -> gamma G top (w, z)) -> leb (lat ND) top (bot (lat ND)) = false ->
  (forall s x c, reachable_state m s -> val sv s x = Some c -> In x vals) ->
  (forall s x c, initial m s -> val sv s x = Some c ->
     exists b i, def sv x = Param b i /\ In b (Graph.entries (cfg (base sv))) /\
       gamma (fact_conc (sparse_of_numeric ND G br top)) (entry x) c) ->
  post_solution (lift_bot_lattice (lat ND))
    (sparse_system EN EV (numeric_problem ND G br top sv vals entry)) sigma ->
  forall s x c, reachable_state m s -> val sv s x = Some c ->
    gamma (lift_bot_gamma (fact_conc (sparse_of_numeric ND G br top))) (sigma (UVal x)) c.
```
Proof idea: the first unfolds the adapter: `op_sound` is the domain's abstract-operator soundness
composed with the bridge equation (`bridge_eq` gives the `Bits` result, `bridge_word` the
`is_word` premises of the domain), `top_sound` is the `top` premise, `assume_args_sound` is
`abs_assume_sound` and `bridge_truth` ties the truth value of a result to the word; the second is
`sparse_sound` with that domain. Card: ANA-3.

```coq
(** Edge predicates are VIEW-5's `refined_fact` and its theorem `refined_fact_sound`; Analyses adds
    none. Path facts: bounded disjunction keeps the domain laws. *)
Theorem path_domain_laws {A C K} (k : nat) (D : sparse_domain A C K) (truth : C -> bool)
    (op_eval : K -> list C -> option C) :
  sparse_domain_laws D truth op_eval -> sparse_domain_laws (path_domain k D) truth op_eval.
(** Guard chains: every guard of the chain at a block holds in every reachable state there, and its
    subject is defined. *)
Theorem guard_chain_holds {S O N E V K C} (m : semantics S O) (sv : ssa_view S O N E V K C)
    (EN : encoding N) :
  ssa_view_laws m sv -> strict_ssa_laws m sv ->
  forall s, reachable_state m s ->
    Forall (cond_holds sv s) (guard_chain sv EN (point (base sv) s)).
```
Proof idea: disjunction laws from Order (`disjunction_laws`, `disjunction_gamma_laws`); guard chains
by `dominated_guard_holds` for each edge of `dominating_edges_in`, which are sound by the
dominator context of VIEW-5. Card: ANA-3.

### ANA-4

```coq
(** Demand soundness: two runs from initial states that agree on the demanded part at their common
    point behave identically; neededness (M = bool), demanded bits and observable bits are
    instances. *)
Theorem demand_sound {S O N E X Cv M} (m : semantics S O) (en : endings S) (inv : S -> Prop)
    (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M)
    (sigma : N -> finite_map EX (dvars dv) M) (s0 t0 : S) :
  demand_laws m en inv EX DD dv -> invariant_of m inv ->
  post_solution (demand_lattice EX DD dv) (demand_system EX DD dv) sigma ->
  initial m s0 -> initial m t0 -> point (dgraph dv) t0 = point (dgraph dv) s0 ->
  agree (demand_agreement EX DD dv) (sigma (point (dgraph dv) s0)) s0 t0 ->
  same_behaviour m en s0 m en t0.
(** A closed demand holds at reachable states, not only at initial ones: two states at one point
    that agree on the closed demand behave identically from there on. *)
Theorem closed_demand_sound {S O N E X Cv M} (m : semantics S O) (en : endings S)
    (inv : S -> Prop) (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) :
  demand_laws m en inv EX DD dv -> invariant_of m inv -> demand_closed EX DD dv d ->
  forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    agree (demand_agreement EX DD dv) d s t -> same_behaviour m en s m en t.
(** A dead value may hold anything: states that differ only in a variable whose demand is bot in
    a closed demand behave identically. *)
Theorem dead_value_removable {S O N E X Cv M} (m : semantics S O) (en : endings S)
    (inv : S -> Prop) (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M)
    (d : finite_map EX (dvars dv) M) (x : X) :
  demand_laws m en inv EX DD dv -> invariant_of m inv -> demand_closed EX DD dv d ->
  dget EX (dlat DD) d x = bot (dlat DD) ->
  forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    (forall y, y <> x -> dlookup dv s y = dlookup dv t y) ->
    same_behaviour m en s m en t.
(** The closed demands are the post-solutions of the one-unknown system, and the least closed
    demand is closed and below every closed demand. *)
Theorem closed_system_iff {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) :
  post_solution (demand_lattice EX DD dv) (closed_system EX DD dv) (fun _ => d) <->
  demand_closed EX DD dv d.
Theorem needed_values_closed {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool) :
  demand_closed EX bool_demand dv (needed_values EX dv).
Theorem needed_values_least {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool)
    (d : finite_map EX (dvars dv) bool) :
  (forall e x, dback dv e x false = nil) ->
  demand_closed EX bool_demand dv d ->
  leb (demand_lattice EX bool_demand dv) (needed_values EX dv) d = true.
(** A step of an instruction that is not effectful emits no event, leaves the heap alone, keeps the
    number of frames, is not stopped, and under KeepTraps does not trap. *)
Theorem non_effectful_step_pure {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) (pol : trap_policy) :
  effects_laws m en ef ev ->
  forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    effectful ef pol i = false ->
    l = nil /\ depth ev s' = depth ev s /\ heap ev s' = heap ev s /\ ~ stopped en s /\
    (pol = KeepTraps -> ~ trapped en s).
```
Proof idea: `demand_sound` by `agreement_same_behaviour` with `R := fun _ => demand_agreement ..`;
`closed_demand_sound` by `bisimilar_same_behaviour`, since the constant closed demand is a
post-solution and `agreement_bisimulation` holds for every pair of `inv` states at one point;
`dead_value_removable` because agreement at `bot` is trivial (`d_bot_agrees`); the closed system by
unfolding both post-solution predicates (`Query.eval` of `Ask tt` is the value at `tt`); the least
demand by induction on the worklist. Inflationary joining and finite height give closure even for
nonmonotone transfers. Boolean strictness makes each N3 contribution monotone: the false case is
empty and the true case is fixed. Prove the indexed constraints agree with the one-unknown system,
including on raw graphs and duplicate variable lists, and preserve the least closed demand; the last
unfolds `effectful` and uses `silent`, `frame_frame`, `heap_frame`, `stop_covered` and
`trap_covered`. Pfenning's factorial example (z live but not needed) is `Examples`' instantiation.
Card: ANA-4.

```coq
(** Dead-code erasure. The erased edges write only variables that the closed demand `d` does not
    need, and their instructions are not effectful under the policy. Then the program with those
    instructions replaced by no-ops behaves like the original from initial states that agree at `d`:
    the same behaviour under KeepTraps; under DropUnreadTraps, the same behaviour whenever the
    original run does not trap. *)
Theorem dce_sound {S O N E X Cv I H} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (m' : semantics S O) (en' : endings S) (inv : S -> Prop) (EX : encoding X)
    (er : erasure S O N E X Cv I) (d : finite_map EX (dvars (er_demand er)) bool)
    (ef : effects I) (ev : effects_view S I H) (s0 t0 : S) :
  demand_laws m en inv EX bool_demand (er_demand er) -> invariant_of m inv ->
  demand_closed EX bool_demand (er_demand er) d ->
  effects_laws m en ef ev -> erasure_laws pol m en m' en' EX er d ->
  (forall e x, er_erased er e = true -> In x (ddefs (er_demand er) e) ->
     dget EX bool_lattice d x = false) ->
  (forall e, er_erased er e = true ->
     exists i, er_instr er e = Some i /\ effectful ef pol i = false) ->
  (forall s l s' e, reachable_state m s -> step m s l s' ->
     taken (dgraph (er_demand er)) s l s' e -> instr_at ev s = er_instr er e) ->
  initial m s0 -> initial m' t0 -> point (er_graph er) t0 = point (dgraph (er_demand er)) s0 ->
  er_agree EX er d s0 t0 ->
  dce_conclusion pol m en s0 m' en' t0.
```
Proof idea: `agreement_simulation2` of Views, with the lattice `demand_lattice`, the agreement
`fun _ => demand_agreement`, the solution `fun _ => d` (a post-solution of the backward system by
`demand_closed`), the exit fact `fun _ => d`, the transfer `demand_transfer`,
`inv1 := er_inv pol m en` restricted to the states
reachable from `s0`, `inv2 := reachable_state m'`, and the measures constantly zero (`d_no_stays`
and `er_no_stays` leave no stay, and every step is matched by one step, after the empty silent
run). Under DropUnreadTraps the original is first restricted to the run from `s0`, whose reachable
states are untrapped by `never_traps`, so `er_inv` is an invariant. The kept edges and the endings
are the client's laws. On an erased edge the original's step is silent (`silent` with `effectful ef
pol i = false`) and, under KeepTraps, neither traps nor stops (`non_effectful_step_pure`); it writes
only dead variables and keeps all others (`d_frame`), so the no-op step of `P'`
(`er_nop_forth`) restores agreement at `d`: a needed variable is not defined, and agreement at the
transfer `demand_transfer e d`, which is above `d` outside the defined variables, gives its equality
(`agree_antitone`); a dead variable agrees trivially (`d_bot_agrees`). The other direction is
`er_nop_back`, whose matching step of `P` is silent likewise. For stuck matching, use the
two-way step matches to show that if one state cannot step, the other cannot step either;
`er_ends` transfers the absence of the other three endings. The matching run is empty. This
argument needs agreement at `d`, which the chosen exit fact supplies. The two programs share the
graph (`er_cfg`), so both steps reach one point (`taken_edge`). This justifies deleting
`z <- z + 1` in Pfenning's example. Card: ANA-4.

```coq
(** On the listed nodes, effects, control dependences and possible divergence are kept; the
    marked set is supported on those nodes and is the least set closed under these rules. *)
Theorem adce_closed {N E} (EN : encoding N) (ai : adce_input N E) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall n, FinSet.mem EN n (adce_marked EN ai) = true -> In n (Graph.nodes (agraph ai))) /\
  (forall n, In n (Graph.nodes (agraph ai)) -> effectful_node ai n = true ->
     FinSet.mem EN n (adce_marked EN ai) = true) /\
  (forall b n, In b (Graph.nodes (agraph ai)) -> In n (Graph.nodes (agraph ai)) ->
     FinSet.mem EN n (adce_marked EN ai) = true -> cdep (agraph ai) (aexits ai) b n ->
     FinSet.mem EN b (adce_marked EN ai) = true) /\
  (forall n, In n (Graph.nodes (agraph ai)) -> may_not_terminate ai n = true ->
     FinSet.mem EN n (adce_marked EN ai) = true).
Theorem adce_least {N E} (EN : encoding N) (ai : adce_input N E) (M : FinSet.t N) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall n, In n (Graph.nodes (agraph ai)) -> effectful_node ai n = true ->
     FinSet.mem EN n M = true) ->
  (forall b n, In b (Graph.nodes (agraph ai)) -> In n (Graph.nodes (agraph ai)) ->
     FinSet.mem EN n M = true -> cdep (agraph ai) (aexits ai) b n ->
     FinSet.mem EN b M = true) ->
  (forall n, In n (Graph.nodes (agraph ai)) -> may_not_terminate ai n = true ->
     FinSet.mem EN n M = true) ->
  forall n, FinSet.mem EN n (adce_marked EN ai) = true -> FinSet.mem EN n M = true.
(** Every path from a listed unmarked node that first reaches a marked node reaches the same one. *)
Theorem adce_skip_unique {N E} (EN : encoding N) (ai : adce_input N E) (n m1 m2 : N) :
  ready EN (agraph ai) (prepare EN (agraph ai)) ->
  incl (aexits ai) (Graph.nodes (agraph ai)) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall x, In x (aexits ai) -> FinSet.mem EN x (adce_marked EN ai) = true) ->
  In n (Graph.nodes (agraph ai)) ->
  FinSet.mem EN n (adce_marked EN ai) = false ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m1 ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m2 -> m1 = m2.
```
Proof idea: `ready` includes graph well-formedness and duplicate-free outgoing lists. Derive the
reverse graph's readiness from `reverse_graph_ready` and the exactness check from
`dominator_exact_true`. Use these with `control_deps_exact` to relate the prepared index to
`cdep`. Prove support, closure and leastness by the worklist
invariant. If two out-paths of unmarked nodes first reach distinct marked nodes,
one of them is control dependent on a node of the walk, which closure would have marked (Cytron et
al.'s argument, from `GraphControlDependence`). The statement does not claim that a deletion
preserves behaviour: the erasure of `dce_sound` does. Card: ANA-4.

### ANA-5

```coq
(** A checked numbering is sound at the moment of binding: when x is bound to c, a class mate y
    whose home strictly dominates the home of x already holds c; and class mates that are
    parameters of one block are bound together, so they hold c at the same step. *)
Theorem numbering_check_sound {S O N E V K C} (m : semantics S O) (EV : encoding V)
    (np : numbering_problem S O N E V K C) (rep : V -> V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) -> numbering_check EV np rep = true ->
  forall x y s l s' c, rep x = rep y -> reachable_state m s -> step m s l s' ->
    val (nsv np) s' x = Some c -> val (nsv np) s x <> Some c ->
    (strictly_dominates (cfg (base (nsv np))) (home (nsv np) y) (home (nsv np) x) \/
     exists b i j, def (nsv np) x = Param b i /\ def (nsv np) y = Param b j) ->
    val (nsv np) s' y = Some c.
(** A use of a class member may be replaced by another: at a point that the homes of both strictly
    dominate, both values are defined and equal. *)
Theorem numbering_use_sound {S O N E V K C} (m : semantics S O) (EV : encoding V)
    (np : numbering_problem S O N E V K C) (rep : V -> V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) -> numbering_check EV np rep = true ->
  forall x y s, rep x = rep y -> reachable_state m s ->
    strictly_dominates (cfg (base (nsv np))) (home (nsv np) x) (point (base (nsv np)) s) ->
    strictly_dominates (cfg (base (nsv np))) (home (nsv np) y) (point (base (nsv np)) s) ->
    exists c, val (nsv np) s x = Some c /\ val (nsv np) s y = Some c.
(** Both producers pass the checker. *)
Theorem dominator_numbering_checked {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (EK : encoding K) (np : numbering_problem S O N E V K C) :
  numbering_check EV np (dominator_numbering EN EV EK np) = true.
Theorem optimistic_numbering_checked {S O N E V K C} (EV : encoding V) (EK : encoding K)
    (np : numbering_problem S O N E V K C) :
  numbering_check EV np (optimistic_numbering EV EK np) = true.
(** Loop invariance: during one execution of the loop, at most one step changes the value of an
    invariant. Stated by decomposition: once the value has changed between two states of the
    execution, it does not change again between the later two. *)
Theorem loop_invariant_sound {S O N E V K C} (m : semantics S O)
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (x : V) :
  ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) ->
  loop_info_wf (cfg (base (nsv np))) lp -> invariant_in np lp x = true ->
  forall s tr1 u1 tr2 u2 tr3 u3, reachable_state m s ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) s tr1 u1 ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) u1 tr2 u2 ->
    exec_in m (fun u => body lp (point (base (nsv np)) u) = true) u2 tr3 u3 ->
    val (nsv np) u1 x <> val (nsv np) u2 x -> val (nsv np) u2 x = val (nsv np) u3 x.
```
Proof idea: both numbering theorems rest on the SSA equation lemma of Views (`guard_op_defined` and
`op_args_dominate`, with `dominated_guard_holds` at dominated states): a definition whose home
strictly dominates the point holds the operation of the current values of its operands, so two
congruent definitions at such a point compute the same operation of equal operands, equal by
induction on the run for parameters (bound together at the same edge, with `value_origin`) and on
the dominance chain for operations; the producers' checks are congruence proofs, the optimistic one
by refinement to a fixed point. `loop_invariant_sound` is an induction on the invariance
derivation: a value homed outside the body is rebound only by entering its home, which a run in
the body does not do (`redefine_on_edge`, `redefine_in_stay`), and an operation of invariant
arguments is recomputed to the same value, the first recomputation being the one change.
Card: ANA-5.

### ANA-6

```coq
Theorem legacy_subst_present {K} (bindings : list (term K)) (i : nat) (t : term K) :
  nth_error bindings i = Some t -> legacy_subst bindings i = t.
Theorem legacy_subst_missing {K} (bindings : list (term K)) (i : nat) :
  nth_error bindings i = None -> legacy_subst bindings i = TVar i.
Theorem legacy_subst_bound_spec {K} (bindings : list (term K)) (t : term K) :
  legacy_subst_bound bindings t = true <->
  forall i, In i (term_vars t) -> exists u, nth_error bindings i = Some u.
(** The term comparison decides equality, since an encoding is injective. *)
Theorem term_eqb_spec {K} (EK : encoding K) (t u : term K) : term_eqb EK t u = true <-> t = u.
(** A checked explanation is a proof of equivalence over typed environments, given sound rules. *)
Theorem check_explanation_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (t u : term K)
    (steps : list (rewrite_step K)) :
  Forall (rule_sound ev ok) rules -> check_explanation EK rules t u steps = true ->
  equiv_term ev ok t u.
(** The empty explanation checks for every term. *)
Theorem check_explanation_refl {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t : term K) :
  check_explanation EK rules t t nil = true.
(** An accepted result is equivalent and no more expensive; replay checks its explanation. *)
Theorem optimise_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (cost : K -> nat)
    (fuel : positive) (t u : term K) :
  Forall (rule_sound ev ok) rules -> optimise EK rules cost fuel t = Some u ->
  equiv_term ev ok t u /\ term_cost cost u <= term_cost cost t.
```
Proof idea: replay is induction on the steps: a step rewrites the subterm at `step_pos` by an
instance of a sound rule whose side condition was checked, and `denote` is compositional, so
equivalence of subterms lifts to the whole; `term_eqb_spec` is `encode_injective` on the symbols and
induction on the term. The pipeline only returns after the check and the cost comparison. Nothing
about saturation or extraction is claimed; `egraph_optimise_accepts` shows that the pipeline
accepts. Card: ANA-6.

### ANA-7

```coq
(** The chain-of-recurrences algebra computes sums, products and scalings pointwise in k. *)
Theorem eval_chrec_add {V} (inv : V -> Z) (a b : chrec V) (k : nat) :
  eval_chrec inv (chrec_add a b) k = (eval_chrec inv a k + eval_chrec inv b k)%Z.
Theorem eval_chrec_mul {V} (inv : V -> Z) (a b : chrec V) (k : nat) :
  eval_chrec inv (chrec_mul a b) k = (eval_chrec inv a k * eval_chrec inv b k)%Z.
Theorem eval_chrec_scale {V} (inv : V -> Z) (z : Z) (c : chrec V) (k : nat) :
  eval_chrec inv (chrec_scale z c) k = (z * eval_chrec inv c k)%Z.
(** Recognition is sound: at the k-th arrival at the header during a stay, the value of a recognised
    header parameter is the recurrence evaluated at k, wrapped to the width. The arrival count is a
    function of the run prefix. *)
Theorem scev_sound {S O N E V K C} (m : semantics S O) (EE : encoding E)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V) (ch : chrec V) :
  loop_view_laws m so lv -> scev_ops_laws so (op_eval (lssa lv)) -> recognise lv so x = Some ch ->
  forall s0 es s c, initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
    point (base (lssa lv)) s = lheader lv -> val (lssa lv) s x = Some c ->
    to_Z so c = wrap (width_of so) (eval_chrec (inv_env lv so s) ch (stay_arrivals EE lv es)).
(** Trip counts, with the no-wrap evidence checked separately: the exit test holds for the first
    t arrivals and fails at the t-th, and no value up to t, nor the bound, leaves the range of the
    width under the signedness. *)
Theorem trip_count_sound {V} (inv : V -> Z) (w : width) (sg : signedness) (cmp : cmp_kind)
    (ch : chrec V) (bound : iexpr V) (t : N) :
  trip_count inv w sg cmp ch bound = Some t -> nowrap_check w sg inv ch bound t = true ->
  (forall k, (N.of_nat k < t)%N -> test_holds w sg cmp (eval_chrec inv ch k) (eval_iexpr inv bound)) /\
  ~ test_holds w sg cmp (eval_chrec inv ch (N.to_nat t)) (eval_iexpr inv bound) /\
  (forall k, (N.of_nat k <= t)%N -> in_range w sg (eval_chrec inv ch k)) /\
  in_range w sg (eval_iexpr inv bound).
(** The trip count links the loop's exit test: when the test's left side is a recognised recurrence
    and the trip count is t, a stay arrives at the header at most t times after the first. *)
Theorem loop_trip_sound {S O N E V K C} (m : semantics S O) (EE : encoding E)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (tst : loop_test V) (ch : chrec V) (t : N) :
  loop_view_laws m so lv -> scev_ops_laws so (op_eval (lssa lv)) -> ltest lv = Some tst ->
  recognise lv so (t_lhs tst) = Some ch ->
  forall s0 es s, initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
    point (base (lssa lv)) s = lheader lv ->
    trip_count (inv_env lv so s) (width_of so) (t_sign tst) (t_cmp tst) ch (t_bound tst) = Some t ->
    nowrap_check (width_of so) (t_sign tst) (inv_env lv so s) ch (t_bound tst) t = true ->
    (N.of_nat (stay_arrivals EE lv es) <= t)%N.
```
Proof idea: the algebra by induction on the recurrence; `scev_sound` by induction on the run prefix:
an entry edge resets the count and gives the base from the entry-edge argument (`value_origin`), a
back edge adds one and gives the step, other edges keep the count, and invariants do not change
during the stay (`strict_ssa_laws`); trip counts are exact arithmetic for an affine recurrence, with
no wrap by the evidence; `loop_trip_sound` by induction on the prefix with `l_back_test`: the back
edge is taken only if the test holds at the current arrival, which by `trip_count_sound` and
`scev_sound` means the arrival count is below t. Counted loops are the idiom that this card detects;
fill and copy idioms are not claimed. Card: ANA-7.

### ANA-8

```coq
(** A resolver built from value facts is sound: if the all-functions resolver satisfies the calls
    laws, and every call step lands on the direct callee or on a callee that the facts of its
    callee value name, then the built resolver satisfies the calls laws. *)
Theorem resolver_sound {S O F P V C A} (m : semantics S O) (cv : calls_view S F P)
    (direct : P -> option F) (callee_val : P -> option V) (fact : V -> A)
    (fns : A -> option (list F)) (G : concretisation A C) (val : S -> V -> option C)
    (fn_of : C -> option F) :
  calls_view_laws m cv (fun _ => functions cv) ->
  (forall s l s' p f, reachable_state m s -> step m s l s' -> In p (sites_of cv (here cv s)) ->
     frames cv s' = (here cv s, p) :: frames cv s -> here cv s' = f ->
     direct p = Some f \/ (direct p = None /\ callee_val p = None) \/
     (direct p = None /\ exists v c, callee_val p = Some v /\ val s v = Some c /\
        fn_of c = Some f /\ gamma G (fact v) c /\
        forall l0, fns (fact v) = Some l0 -> In f l0)) ->
  calls_view_laws m cv (resolver direct callee_val fact fns (functions cv)).
(** Recursion: a function active twice on the stack is on a cycle of the call graph. *)
Theorem recursive_sound {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (s : S) :
  calls_view_laws m cv resolve -> reachable_state m s -> ~ NoDup (active cv s) ->
  exists f, In f (active cv s) /\ recursive (call_graph cv resolve) f.
(** Whole-program reachability: a function unreachable in the call graph never runs. *)
Theorem unreachable_never_runs {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) :
  calls_view_laws m cv resolve -> ~ reachable (call_graph cv resolve) f ->
  forall s, reachable_state m s -> ~ In f (active cv s).
(** Purity: a function whose summary is false emits no event and leaves the heap alone, in
    its own steps and in those of its callees. *)
Theorem purity_sound {S O I H F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (ev : effects_view S I H) (impure_local : F -> bool)
    (sigma : F -> bool) :
  calls_view_laws m cv resolve -> summary_laws m cv (purity_spec cv impure_local) (purity_cover ev) ->
  post_solution (slat (purity_spec cv impure_local)) (summary_system cv resolve (purity_spec cv impure_local))
    sigma ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) -> sigma f = false ->
    l = nil /\ heap ev s' = heap ev s.
(** Stack demand: the frames above the topmost activation of f, f included, weigh at most the
    demand, when it is finite. *)
Theorem stack_demand_sound {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (fw : frame_weights F) (f : F) (d : nat) :
  calls_view_laws m cv resolve ->
  stack_demand cv (call_graph cv resolve) fw f = Some d ->
  forall s, reachable_state m s -> In f (active cv s) -> stack_above cv fw f s <= d.
(** Callee shape: a leaf function never calls. *)
Theorem callee_leaf_sound {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) :
  calls_view_laws m cv resolve -> callee_leaf cv f = true ->
  forall s l s', reachable_state m s -> here cv s = f -> step m s l s' ->
    frames cv s' = frames cv s \/ exists g p, frames cv s = (g, p) :: frames cv s'.
(** Call strings: the summary of a frame in its context covers every step. *)
Theorem callstring_sound {S O F P A} (m : semantics S O) (k : nat) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) (sc : step_cover S O A)
    (sigma : F * list P -> A) :
  calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  post_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  forall s l s' i f, reachable_state m s -> step m s l s' -> nth_error (active cv s) i = Some f ->
    step_covers sc (sigma (f, ctx_of cv k s i)) s l s'.
(** The callers index lists exactly the sites whose resolver names the function. *)
Theorem callers_index_agrees {S F P} (EF : encoding F) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) (p : P) :
  In p (callers_of EF (callers_index EF cv resolve) f) <->
  (exists g, In g (functions cv) /\ In p (sites_of cv g)) /\ In f (resolve p).
(** Interprocedural constants: a formal parameter's value lies in the join of the facts of the
    actual arguments at the call sites that may call the function. *)
Theorem arg_fact_sound {S O F P V C A} (m : semantics S O) (cv : calls_view S F P)
    (EF : encoding F) (av : args_view S F P V C) (L : lattice A) (G : concretisation A C)
    (resolve : P -> list F) (fact : V -> A) :
  calls_view_laws m cv resolve -> lattice_laws L -> concretisation_laws L G ->
  (forall s x c, reachable_state m s -> frame_val av s x = Some c -> gamma G (fact x) c) ->
  (forall s l s' p i y c, reachable_state m s -> step m s l s' ->
     frames cv s' = (here cv s, p) :: frames cv s ->
     nth_error (formals av (here cv s')) i = Some y -> frame_val av s' y = Some c ->
     exists z, nth_error (actuals av p) i = Some z /\ frame_val av s z = Some c) ->
  forall s l s' p i y c, reachable_state m s -> step m s l s' ->
    In p (sites_of cv (here cv s)) -> frames cv s' = (here cv s, p) :: frames cv s ->
    nth_error (formals av (here cv s')) i = Some y -> frame_val av s' y = Some c ->
    gamma G (arg_fact EF av (callers_index EF cv resolve) L fact (here cv s') i) c.
```
Proof idea: the resolver law is a case analysis on the three clauses against the three branches of
`resolver`, with `frames_listed` for the fallback `all`; recursion and reachability from the
frame-chain invariant of `active_reachable_in_call_graph`; purity by `summary_sound` with
`purity_cover`; stack demand because the frames above `f` form a path of the call graph out of `f`
and, when `f` reaches no cycle, a path of the condensation DAG whose weight is bounded by the
maximum-weight path; the leaf by `step_shape`; call strings by the proof of `summary_sound` with the
context carried; the index by a fold over the sites; arguments by the call-step law,
`callers_index_agrees`, the join upper bound and `gamma_monotone`. The resolver in `arg_fact_sound`
must be the one the call-step law refers to. Card: ANA-8.

### ANA-9

```coq
(** Andersen: from a post-solution of the points-to system, every pointer a value holds in a
    reachable state points to a site in its set, and every pointer stored in a block of a site
    points to a site in the heap set of that site. *)
Theorem andersen_sound {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) :
  ptr_view_laws m pv ops ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall s, reachable_state m s ->
    (forall x t, pts_of pv s x = Some t -> fmem ET t (sigma (PVal x)) = true) /\
    (forall t0 t, heap_pts pv s t0 t -> fmem ET t (sigma (PHeap t0)) = true).
(** The system is monotone, and the total engine terminates on it under every scheduler: the
    universe has no duplicates, so the lattice has a height. *)
Theorem andersen_monotone {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  monotone_system (pts_lattice ET ops) (andersen_system EV ET ops).
Theorem andersen_terminates {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sch : scheduler (pts_key V T)) :
  terminates (pts_lattice ET ops) (andersen_static EV ET ops) sch Joining.
(** Steensgaard: values that point to one site fall in one class. *)
Theorem steensgaard_sound {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T)) :
  ptr_view_laws m pv ops ->
  forall s x y t, reachable_state m s -> pts_of pv s x = Some t -> pts_of pv s y = Some t ->
    may_alias (steensgaard EV ET ops) x y.
(** Steensgaard is coarser than Andersen: values that share a site in the least Andersen solution
    are in one class. *)
Theorem steensgaard_coarser {V T} (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) (x y : V) (t : T) :
  least_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  fmem ET t (sigma (PVal x)) = true -> fmem ET t (sigma (PVal y)) = true ->
  may_alias (steensgaard EV ET ops) x y.
(** Escape: the escaped sites contain what an escaping instruction passes and what escaped sites
    point to. *)
Theorem escaped_closed {S O V C L T} (m : semantics S O) (pv : ptr_view S V C L T)
    (EV : encoding V) (ET : encoding T) (ops : list (ptr_op V T))
    (sigma : pts_key V T -> pts_set ET ops) :
  ptr_view_laws m pv ops ->
  post_solution (pts_lattice ET ops) (andersen_system EV ET ops) sigma ->
  forall s x t t', reachable_state m s -> In (PEscape x) (pop pv s) -> pts_of pv s x = Some t ->
    FinSet.mem ET t (escaped_sites ET ops sigma) = true /\
    (heap_pts pv s t t' -> FinSet.mem ET t' (escaped_sites ET ops sigma) = true).
(** Zero-initialised bytes: a byte that no footprint of the fact covers reads as zero, whenever it
    can be read. *)
Theorem zero_written_sound {S O N E V C L T} (m : semantics S O) (EF : encoding (footprint T))
    (gv : graph_view S O N E) (pv : ptr_view S V C L T) (fp : E -> list (footprint T))
    (sigma : N -> written_set EF gv fp) :
  zero_laws m gv pv fp ->
  post_solution (finite_powerset_lattice EF (write_universe EF gv fp)) (zero_written_system EF gv fp)
    sigma ->
  forall s c l0 t n, reachable_state m s -> loc_of (pmem pv) s c = Some l0 ->
    loc_site (pmem pv) s l0 = Some t ->
    ~ covered (FinSet.elements (proj1_sig (sigma (point gv s)))) t (loc_offset (pmem pv) s c) 1 ->
    pbyte pv s c = Some n -> n = 0.
```
Proof idea: `andersen_sound` by induction on `exec` with `pts_origin` and `heap_origin`: a new
fact is derived by one of the five instruction kinds (a callee parameter or a returned pointer is
a `PCopy`), and each kind's constraint (reading sets, `Side` contributions to the heap unknowns)
bounds it; the system is a post-solution, which includes the `Query.sides` bounds. Monotonicity
and termination are `monotone_query` of each right-hand side and `finite_powerset_height`. The
second and third follow the same unification argument as the least solution; escape is closure of
the least set; zero bytes by `forward_invariant_sound` with the concretisation "a byte of an
existing block outside the covered footprints reads zero when readable", using `z_init`, `z_fresh`
for a block that the step creates and `z_kept` for the others. Card: ANA-9.

### ANA-10a and ANA-10e

```coq
(** Validated accesses: a range in the fact is accessible, until a barrier. *)
Theorem validated_sound {S O N E T} (m : semantics S O) (ET : encoding T)
    (bv : barrier_view S O N E T) (sigma : N -> range_must ET) :
  barrier_laws m bv ->
  post_solution (range_must_lattice ET) (validated_system ET bv) sigma ->
  forall s t o w, reachable_state m s -> (0 < w)%nat ->
    range_covers (sigma (point (bgraph bv) s)) t o w ->
    accessible bv s t o w.
(** Dead stores: two runs from initial states that agree outside the dead ranges at their
    common point behave identically. *)
Theorem dead_store_sound {S O N E T} (m : semantics S O) (en : endings S) (ET : encoding T)
    (sv : store_view S O N E T ET) (sigma : N -> range_must ET) (s0 t0 : S) :
  store_laws m en ET sv ->
  post_solution (range_must_lattice ET) (dead_store_system ET sv) sigma ->
  initial m s0 -> initial m t0 -> point (sgraph sv) t0 = point (sgraph sv) s0 ->
  agree (sagree sv) (sigma (point (sgraph sv) s0)) s0 t0 -> same_behaviour m en s0 m en t0.
(** Disjoint footprints share no byte. *)
Theorem footprints_disjoint_sound {T} (ET : encoding T) (F G : list (footprint T)) :
  footprints_disjoint ET F G = true -> forall t o, covered F t o 1 -> covered G t o 1 -> False.
(** MemorySSA with a verified no-clobber checker: when the checker accepts, no write on any walk
    from the definition's edge to the load overlaps its bytes, so the bytes of every allocation
    that existed at the definition are unchanged; a load whose definition is live-on-entry reads
    the bytes that existed when the function was entered. *)
Theorem no_clobber_unchanged {S O N E T F L} (m : semantics S O) (bv : bytes_view S O N E T L)
    (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F) (ms : memory_ssa F N)
    (reads : N -> list (footprint T)) :
  bytes_laws m bv ->
  no_clobber_check EN EF ET f (cfg (bgv bv)) (writes_at bv) reads ms = true ->
  (forall s s1 t e1 es' n, reachable_state m s -> run_edges m (bgv bv) s (e1 :: nil) s1 ->
     run_edges m (bgv bv) s1 es' t -> point (bgv bv) t = n ->
     def_of_load ms n = Some (MDef f (Graph.source (cfg (bgv bv)) e1)) ->
     forall l ty o, covered (reads n) ty o 1 -> bsite bv s1 l = Some ty ->
       byte bv t l o = byte bv s1 l o) /\
  (forall s es t n, reachable_state m s -> In (point (bgv bv) s) (Graph.entries (cfg (bgv bv))) ->
     run_edges m (bgv bv) s es t -> point (bgv bv) t = n -> def_of_load ms n = Some (MLive f) ->
     forall l ty o, covered (reads n) ty o 1 -> bsite bv s l = Some ty ->
       byte bv t l o = byte bv s l o).
(** Immutable data: a byte of an existing allocation that no node writes keeps its value along
    every run. *)
Theorem immutable_sound {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L) (ty : T)
    (o : Z) :
  bytes_laws m bv -> (forall n, covered (writes_at bv n) ty o 1 -> False) ->
  forall s tr t l, reachable_state m s -> exec m s tr t -> bsite bv s l = Some ty ->
    byte bv t l o = byte bv s l o.
(** Invariant loads: a load with an invariant address and no write in the loop reads one value for a
    whole execution of the loop: the bytes it reads never change, and the address changes at most
    once. *)
Theorem invariant_load_sound {S O N E V K C T L} (m : semantics S O) (ET : encoding T)
    (bv : bytes_view S O N E T L) (np : numbering_problem S O N E V K C) (lp : loop_info N)
    (addr : V) (loop_writes : list (footprint T)) (load : footprint T) :
  bytes_laws m bv -> ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) ->
  loop_info_wf (cfg (base (nsv np))) lp ->
  (forall s, point (base (nsv np)) s = point (bgv bv) s) ->
  invariant_load ET np lp addr loop_writes load = true ->
  (forall n, body lp n = true -> forall f, In f (writes_at bv n) -> In f loop_writes) ->
  forall s tr t l ty o, reachable_state m s ->
    exec_in m (fun u => body lp (point (bgv bv) u) = true) s tr t -> covered [load] ty o 1 ->
    bsite bv s l = Some ty -> byte bv t l o = byte bv s l o.
```
Proof idea: validated accesses by `forward_invariant_sound` with `accessible_persists` and
`validates_accessible`; dead stores by `agreement_same_behaviour`; the checker's walk test is a
finite forward/reverse reachability over `path`, and the unchanged claim is an induction on the
run using `byte_site_stable` and `byte_frame`
(a changed byte of an existing allocation is covered by the writes of the node; allocations and
frees are among those writes); immutability and invariant loads by induction with `byte_frame`,
`footprints_disjoint_sound` and `invariant_in`. In `invariant_load_sound` the bytes half is the
disjointness of `loop_writes` from the load, and the address half is `loop_invariant_sound` for
`base`, so each execution of the load inside one execution of the loop reads the same bytes at the
same address. Acceptance evidence for the MemorySSA checker: `memoryssa_accepts`. Cards: ANA-10a
for byte and range laws; ANA-10e for the legacy checker and its byte theorem.

### ANA-11

```coq
(** The solver succeeds on each program built from a view with a well-formed graph, and the
    database it returns is the least solution of the lattice system. Liveness: *)
Theorem rules_liveness_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) :
  graph_wf (cfg (gview vv)) ->
  exists db, solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db.
Theorem rules_liveness_least {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  least_solution (live_lattice EX vv) (liveness_system EX vv) (live_of_db EN EX vv db).
(** Neededness, on the demand system with M = bool. A defined variable that is not needed demands
    nothing, which is what N3 reads. *)
Theorem rules_neededness_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) :
  graph_wf (cfg (dgraph dv)) ->
  exists db, solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db.
Theorem rules_neededness_least {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) (db : database pred) :
  graph_wf (cfg (dgraph dv)) -> demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  least_solution (demand_lattice EX bool_demand dv) (demand_system EX bool_demand dv)
    (needed_of_db EN EX dv db).
(** Reaching definitions: the database is the least solution of the forward system. *)
Theorem rules_reaching_solves {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) :
  graph_wf (cfg (gview vv)) ->
  exists db, solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db.
Theorem rules_reaching_least {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db ->
  least_solution (reach_lattice EX EE vv) (reaching_system EX EE vv) (reach_of_db EN EE EX vv db).
(** The declarative model agrees with the solver: the least model of each program holds a fact
    exactly when the lattice fact has it. *)
Theorem rules_liveness_model {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x,
    holds (least_model liveness_program (extract_live_facts EN EE EX vv)) PLive
      (args2 EN EX n x) <-> fmem EX x (live_of_db EN EX vv db n) = true.
Theorem rules_neededness_model {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (dv : demand_view S O N E X Cv bool) (db : database pred) :
  graph_wf (cfg (dgraph dv)) -> demand_vars_ok dv -> (forall e x, dback dv e x false = nil) ->
  solve_program neededness_program (extract_needed_facts EN EE EX dv) = Some db ->
  forall n x,
    holds (least_model neededness_program (extract_needed_facts EN EE EX dv)) PNeeded
      (args2 EN EX n x) <-> dget EX bool_lattice (needed_of_db EN EX dv db n) x = true.
Theorem rules_reaching_model {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program reaching_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x d,
    holds (least_model reaching_program (extract_live_facts EN EE EX vv)) PReaches
      (args3 EE EX EN d x n) <->
    fmem (pair_encoding EX EE) (x, d) (reach_of_db EN EE EX vv db n) = true.
```
Proof idea: each program is well formed (`program_wf`: its rules are safe, which is the
range restriction checked rule by rule above, and the facts have the predicates' arities) and
stratified (`PDef` is negated and has no rule, so level 0; the derived predicate is level 1), so
`solve_program_exact` gives a database that represents the least model (`holds` of
`least_model` is membership in the database, which is the `_model` theorems). The immediate
consequence operator of the program is the lattice transfer on the encoded facts, so the least model
is the least solution: the database's fact is a post-solution (each rule instance is an inequality
of the system, N3 reading `dback e x true` and `d_back_bot` making the missing case empty), and it
is below every post-solution by induction on the derivation (`stratum_least_is_derives`).
The facts are drawn from `nodes` and `edges_of`, which is why `graph_wf` is a premise: it makes
every
edge's source and target a node. Card: ANA-11.

## Algorithms and references

- **Dense frameworks.** Kildall (POPL 1973) for the edge-transfer fixed point; Kam and Ullman (1976)
  for the monotone framework; Pfenning, Platzer and Simmons, 15-411 Lecture 7 (2015), for liveness
  (K1, K2), neededness (E1 to E5 for `nec`, N1 to N3) and reaching definitions (R1, R2): the notes'
  `l` is a node here, `use`, `def` and `succ` come from the view, and `nec` from the effects view.
- **Must-analyses and code motion.** Knoop, Rüthing and Steffen, "Lazy code motion" (PLDI 1992)
  and Drechsler and Stadel's edge formulation for the earliest, latest, insert and delete sets;
  `lcm_check` validates any producer, so the algorithm is free.
- **Structured analysis and certificates.** Besson, Jensen and Pichardie (2006) and lightweight
  bytecode verification (Rose): store facts at loop heads only; Bourdoncle (1993) for nesting.
- **Values.** Wegman and Zadeck (TOPLAS 1991); known bits and wrapping intervals as in LLVM's
  `KnownBits` and `ConstantRange`; Ranger-style edge predicates (MacLeod, GCC).
- **Neededness, ADCE and dead-code erasure.** Cytron, Ferrante, Rosen, Wegman and Zadeck (TOPLAS
  1991) for ADCE with control dependence; demanded bits as in LLVM's `DemandedBits`; the erasure
  theorem is a lock-step simulation between two programs, as in verified dead-code passes.
- **Numbering.** Alpern, Wegman and Zadeck, "Detecting equality of variables in programs"
  (POPL 1988) for the optimistic partition; Briggs, Cooper and Simpson (1997) for dominator-based
  value numbering, whose scoping needs strict dominance. E-graphs: Willsey et al., "egg" (POPL
  2021),
  with explanations as in Flatt et al., "Small proofs from congruence closure" (FMCAD 2022).
- **SCEV.** Bachmann, Zima and Li, chains of recurrences (1994); van Engelen (2001) for the
  algebra; LLVM's ScalarEvolution for trip counts with separate no-wrap flags.
- **Calls.** Sharir and Pnueli (1981) for call strings; Reps, Horwitz and Sagiv (POPL 1995);
  Apinis, Seidl and Vojdani (APLAS 2012) for the dynamic, side-effecting points-to system.
- **Points-to and memory.** Andersen (1994), Steensgaard (POPL 1996); Chow et al. (1996) and
  LLVM's MemorySSA for the memory-SSA shape, with the checker walking the graph.
- **Datalog analyses.** Whaley et al. (APLAS 2005), cited in the 15-411 notes, for analyses as
  Datalog programs; here the program is a `Rules` value and the engine's database is proved equal to
  the lattice solution.

## Cross-package assumptions and semantic limits

The contracts use the following cross-package interfaces and retain these limits:
1. **Order.** Names are those of `order.md`: `finite_powerset_lattice`, `finite_must_lattice`,
   `finite_pointwise_lattice` with their heights, `finite_set` and `finite_map`, `bool_lattice`,
   `disjunction_lattice k L`, `lift_bot` with `Unreached` and `Reached`, `finite_clamp` and
   `finite_map_clamp`.
2. **Collections.** `FinSet.mem EX x a` takes the encoding; `FinSet.union`, `FinSet.diff`,
   `FinSet.of_list`, `FinSet.elements` likewise; `Map.t X M` with `Map.get EX x d`; `pair_encoding`;
   `position_encoding : encoding position`.
3. **Domains.** `numeric_domain A` with `lat`, `top_at`, `of_const`, `forward`, `assume`, `meet`;
   `numeric_laws D G` over `word`; `abs_eval` and `abs_assume`; `partition E` with
   `partition_equiv`, `partition_union`, `partition_top`, `partition_lattice` and a
   `partition_forget` (DOM-7); masks with `mask_lattice w`, `mask_agreement w` and `demand`
   (DOM-5); `footprint` and `covered`, which VIEW-7 also uses; `footprint_encoding` and
   `range_must_lattice` with its operations (DOM-6).
4. **Graph.** `path`, `dominates`, `strictly_dominates`, `edge_dominates`, `cdep g exits b n` with
   `exits_reachable`, `max_paths`, `condensation`. The dominator tree and the WTO that the
   schedulers use are directly proved internal producers; independent checkers remain available
   for external candidates.
5. **Fixpoint.** `solve_total` (static systems with termination evidence) and `solve_fuel` (binary
   fuel, top fallback), `terminates`, `least_solution`, `monotone_system`, the schedulers
   `rpo_scheduler`, `wto_scheduler`, `scc_scheduler`, and the cut-point checker `expand` that
   `certificate_check` reuses.
6. **Rules.** `program` with encoding and arities, `ground_atom`,
   `solve_program`, `database`, `db_holds`, `program_wf`,
   `stratified` and `solve_program_exact`.
7. **Interprocedural scope.** SSA-level analyses (ANA-3, ANA-4, ANA-5, ANA-7) are stated over the
   activation semantics of one function. EX-5c lifts reachability and traces from the full
   semantics to activations; it is not claimed that a property of the activation semantics of
   `same_behaviour` form transfers to the full semantics. Neededness across calls is not claimed.
8. **Loop idioms.** Only counted loops are specified; fill and copy idioms need per-iteration
   states and a statement against the memory view.
9. **Effects policy.** `trap_policy` is a parameter with a separate conclusion per policy
   (`dce_conclusion`); `allocates` is effectful under both.
10. **Rules text.** The three programs of ANA-11 are `program` values, written out above;
    the package has no text parser.
11. **Allocation sites.** `accessible`, `byte` and the zero facts are stated for allocations; a
    site with several live allocations gets the weak reading "some allocation of the site" for
    `accessible`, and facts about every allocation for `byte` and the zero facts.

## Cross-document contracts

Order provides `finite_clamp` and `finite_map_clamp`. Domains provides `partition_forget`,
`footprint`, `covered`, `footprint_encoding`, and the encoding-indexed `range_must` family.
`partition_forget_spec` requires a reached fact; `partition_forget_unreached` handles bottom.
Views provides the names and laws used above.


<!-- C19 SSA liveness contracts -->

```coq
Definition var_point_uses {S O N E X Cv} (vv : var_view S O N E X Cv) :
    point_uses N E X :=
  PointUses (cfg (gview vv)) (uses vv) (defs vv) (exit_uses vv).

Theorem syntactic_live_least {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (sigma : N -> live_set EX vv) :
  graph_wf (cfg (gview vv)) ->
  least_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    (fmem EX x (sigma n) = true <-> syntactic_live (var_point_uses vv) x n).

Theorem syntactic_live_rules {S O N E X Cv} (EN : encoding N) (EE : encoding E)
    (EX : encoding X) (vv : var_view S O N E X Cv) (db : database pred) :
  graph_wf (cfg (gview vv)) ->
  solve_program liveness_program (extract_live_facts EN EE EX vv) = Some db ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    (fmem EX x (live_of_db EN EX vv db n) = true <->
      syntactic_live (var_point_uses vv) x n).
```

## ANA-12: R/T query

`AnalysesSsaLiveQuery.v` implements the following. `ssa_query_graph` is independent of value
uses and definitions; `ssa_query_values` is rebuilt when they change. Both use finite maps, and
the query result concerns a pre-instruction point. Definitions below are propositional
specifications of executable data, not inputs that assume the desired liveness answer.

```coq
Definition reduced_path {N E} (EN : encoding N) (g : Graph.t N E)
    (dfs_result : dfs_result N E) (u v : N) : Prop :=
  exists es, path g u es v /\ Forall (fun e => ~ retreating EN g dfs_result e) es.

Definition rt_step {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) (u v : N) : Prop :=
  ~ reduced_path EN g r u v /\
  exists a e, reduced_path EN g r u a /\ In e (Graph.out g a) /\
    Graph.target g e = v /\ retreating EN g r e.

Definition rt_reaches {N E} (EN : encoding N) (g : Graph.t N E)
    (r : dfs_result N E) : N -> N -> Prop :=
  clos_refl_trans N (rt_step EN g r).

Record ssa_query_graph (N E : Type) : Type := SsaQueryGraph {
  query_cfg : Graph.t N E;
  query_dfs : dfs_result N E;
  query_dom : dom_tree N;
  query_reduced : Map.t N (FinSet.t N);
  query_back_closure : Map.t N (FinSet.t N)
}.

Record ssa_query_values (N V : Type) : Type := SsaQueryValues {
  query_def : Map.t V N;
  query_uses : Map.t V (FinSet.t N)
}.

Definition live_index_get {K V} (EK : encoding K) (k : K)
    (m : Map.t K (FinSet.t V)) : FinSet.t V :=
  match Map.get EK k m with
  | Some s => s
  | None => FinSet.empty
  end.

Definition prepare_ssa_query_graph {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) : ssa_query_graph N E.
Definition prepare_ssa_query_values {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) : ssa_query_values N V.
Definition ssa_live_query {N E V} (EN : encoding N) (EV : encoding V)
    (idx : ssa_query_graph N E) (values : ssa_query_values N V) (n : N) (x : V) : bool.
```

For each reachable node `u`, `query_reduced[u]` contains exactly the nodes reachable from `u`
in the graph with DFS retreating edges removed. `query_back_closure[u]` contains exactly the
`rt_reaches` nodes. The producer computes DFS once, R by reverse topological propagation on the
reduced graph, and T as finite closure of `rt_step`; it uses the directly proved exact dominator
backend. The value index maps each value with a reachable use to its definition point and its
reachable use points, including the source of each edge operand and all exit uses. It scans the
finite lists once during preparation, not inside the query. For a value lacking a definition,
the query returns false. Otherwise it tests whether there is a `t` in T(n) strictly dominated by
the definition and a use point `u` with `u` in R(t). Tries account for all membership, union and
construction costs; per-query scans of T and of indexed uses are explicit. There is no claim of
constant time, linear preprocessing, or a reachable semantic-path interpretation.

```coq
Theorem ssa_query_graph_structure {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) :
  ready EN g (prepare EN g) ->
  query_cfg (prepare_ssa_query_graph EN EE g) = g /\
  query_dfs (prepare_ssa_query_graph EN EE g) =
    dfs (prepare EN g) FinSet.empty (Graph.entries g) /\
  query_dom (prepare_ssa_query_graph EN EE g) = dominator_tree (prepare EN g).

Theorem ssa_query_graph_agrees {N E} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) :
  ready EN g (prepare EN g) ->
  (exists entry, Graph.entries g = [entry]) ->
  forall n u, reachable g n -> reachable g u ->
    (FinSet.mem EN u (live_index_get EN n
       (query_reduced (prepare_ssa_query_graph EN EE g))) = true <->
       reduced_path EN g (query_dfs (prepare_ssa_query_graph EN EE g)) n u) /\
    (FinSet.mem EN u (live_index_get EN n
       (query_back_closure (prepare_ssa_query_graph EN EE g))) = true <->
       rt_reaches EN g (query_dfs (prepare_ssa_query_graph EN EE g)) n u).

Theorem ssa_query_values_agree {B BE N E V} (EN : encoding N) (EV : encoding V)
    (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  forall n x, reachable (live_graph (point_model s)) n ->
    (FinSet.mem EN n (live_index_get EV x
       (query_uses (prepare_ssa_query_values EN EV s))) = true <->
       point_use_at (point_model s) n x) /\
    (point_use_at (point_model s) n x ->
       Map.get EV x (query_def (prepare_ssa_query_values EN EV s)) = point_definition s x).

Theorem ssa_live_query_exact {B BE N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  forall n x, reachable (live_graph (point_model s)) n ->
    (ssa_live_query EN EV
      (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = true <->
      syntactic_live (point_model s) x n).

Theorem ssa_live_query_dense {B BE S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) (vv : var_view S O N E V C)
    (sigma : N -> live_set EV vv) :
  point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  least_solution (live_lattice EV vv) (liveness_system EV vv) sigma ->
  forall n x, reachable (live_graph (point_model s)) n ->
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = fmem EV x (sigma n).

Theorem ssa_live_query_rules {B BE S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) (vv : var_view S O N E V C)
    (db : database pred) :
  point_model s = var_point_uses vv -> ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  solve_program liveness_program (extract_live_facts EN EE EV vv) = Some db ->
  forall n x, reachable (live_graph (point_model s)) n ->
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x = fmem EV x (live_of_db EN EV vv db n).
```

`live_index_get` is the default-empty `Map.get` helper owned by ANA-12. A separate general-graph
producer answers unreachable or non-strict input, and
is not included in `ssa_live_query_exact`. The SSA specialization only claims reachable input.
The client can select the general producer for other points. The declarations do not assert
that unreachable points are dead. Dominance and R/T remain exact on irreducible reachable CFGs.

Prove DFS edge classification and acyclicity of the reduced graph, R propagation, T closure,
and exact dominance first. The semantic step is the SSA path lemma: a path avoiding the unique
definition exists exactly when some strictly definition-dominated T point can reach a use in R.
Strictness and the all-outgoing definition condition identify the dense kill point with the
paper's node-definition convention; edge uses are placed at their own source points. At the
definition point itself, no strict use is present and every outgoing edge kills the value, so
the query and path relation are both false, including a loop back to the definition. Prove the
two directions and connect them to the executable indexes, then derive equality to the least
ANA-1 solution through `syntactic_live_least`, and to ANA-11 through `rules_liveness_least`.
The source is [Léchenet, Blazy and Pichardie 2020][liveness-study], especially Definition 1
and the online algorithm. These are proof obligations, not evidence.

[liveness-study]: https://pmc.ncbi.nlm.nih.gov/articles/PMC7324086/



## ANA-13: sparse materialized liveness

`AnalysesSsaLiveSets.v` owns the following. The result maps each point to a finite set; absent
points map to the empty set. Internally, a prepared predecessor index and per-edge definition
membership sets are constructed once. Work items are point/value pairs.

```coq
Definition sparse_live_materialize {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) : Map.t N (FinSet.t V).

Definition sparse_live_at {N V} (EN : encoding N) (EV : encoding V)
    (m : Map.t N (FinSet.t V)) (n : N) (x : V) : bool :=
  FinSet.mem EV x (live_index_get EN n m).

Theorem sparse_live_materialize_exact {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  forall n x, In n (Graph.nodes (live_graph p)) ->
    (sparse_live_at EN EV (sparse_live_materialize EN EE EV p) n x = true <->
      syntactic_live p x n).

Theorem sparse_live_materialize_dense {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (sigma : N -> live_set EV vv) :
  ready EN (cfg (gview vv)) (prepare EN (cfg (gview vv))) ->
  least_solution (live_lattice EV vv) (liveness_system EV vv) sigma ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (var_point_uses vv)) n x =
      fmem EV x (sigma n).

Theorem sparse_live_materialize_rules {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (db : database pred) :
  ready EN (cfg (gview vv)) (prepare EN (cfg (gview vv))) ->
  solve_program liveness_program (extract_live_facts EN EE EV vv) = Some db ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (var_point_uses vv)) n x =
      fmem EV x (live_of_db EN EV vv db n).

Theorem sparse_live_query_agrees {B BE N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  forall n x, reachable (live_graph (point_model s)) n ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (point_model s)) n x =
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x.
```

## Required producer behavior

Build `prepare EN (live_graph p)` once and build an `E -> FinSet.t V` definition-membership
index by traversing the finite `edges_of` list. Seed `(n,x)` for each exit use at node `n` and
for each use of every edge in `Graph.out g n`. Use-before-def means every edge-use seed is
inserted even when the same edge defines `x`. For each newly inserted `(n,x)`, traverse the
prepared predecessor edges of `n`, and insert `(source e,x)` exactly when the definition index
does not contain `x` for `e`. Insert into the result before scheduling, so each distinct pair is
enqueued at most once. Use a finite-worklist measure or binary fuel derived from node and
mentioned-value counts; no execution may return an incomplete result on fuel exhaustion.

The proof establishes seed and propagation soundness by constructors of `syntactic_live`;
completeness follows by induction over its derivation. Every pending item is processed before
return. Termination uses the finite set of nodes and values mentioned by an edge or exit;
every discovered pair strictly increases the finite result. `ready` supplies the explicit
NoDup outgoing-edge condition and predecessor agreement. Duplicate operands and same-edge
use/def do not affect set membership. Parallel edges remain distinct during traversal. The
worklist covers unreachable nodes and irreducible SCCs as well as reachable ones.

This is a sparse per-pair backward construction: it visits only discovered pairs and incoming
edges of those pairs. Account for preparation, predecessor visits, trie lookup and update
costs, and output size. A live-set result can contain quadratically many point/value pairs;
neither a linear-time nor a constant-cost union claim follows. The SSA-book loop-structure
construction is related context, not a claimed implementation of this specific producer.
The dense equations and path equivalence derive from VIEW-8 and ANA-1; the Rules theorem uses
`rules_liveness_least`, not an arbitrary post-solution.




<!-- C19 ANA-9a direct Andersen -->

## ANA-9a: directly proved delta Andersen

```coq
Definition andersen_delta {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) : pts_key V T -> pts_set ET ops.

Theorem andersen_delta_least {V T} (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
  least_solution (pts_lattice ET ops) (andersen_system EV ET ops)
    (andersen_delta EV ET ops).

Theorem andersen_delta_sound {S O V C L T} (m : semantics S O)
    (pv : ptr_view S V C L T) (EV : encoding V) (ET : encoding T)
    (ops : list (ptr_op V T)) :
  ptr_view_laws m pv ops ->
  forall s, reachable_state m s ->
    (forall x t, pts_of pv s x = Some t ->
      fmem ET t (andersen_delta EV ET ops (PVal x)) = true) /\
    (forall t0 t, heap_pts pv s t0 t ->
      fmem ET t (andersen_delta EV ET ops (PHeap t0)) = true).
```

Card: ANA-9a. Index copy edges and load/store subscriptions once. When a newly discovered
points-to fact activates a load or store edge, enqueue the source's entire accumulated set for
that edge, then propagate future deltas. Deduplicate facts and edges and use binary fuel or
well-founded recursion. Prove that all pending propagation obligations are covered, every added
fact follows from an inclusion constraint, and quiescence satisfies every constraint; induction
on derivations establishes leastness. The soundness theorem follows from `andersen_sound`.
Test an edge created after its source has received a fact, a later source delta, cyclic copies,
heap load/store, duplicate constraints and the empty input. The site denotes all allocations
at that site; it is not evidence that any concrete allocation is unique.



<!-- C19 ANA-6 facade and REW-7 clients -->

## ANA-6: direct facade and legacy compatibility

```coq
Definition legacy_signature {K} : rw_signature K unit nat :=
  RwSignature (fun _ => Some tt) (fun _ _ _ => true).
Definition legacy_embed {K} (t : term K) : rw_term K unit nat.
(* TVar i maps to RWVar tt i; TApp maps to RWApp tt with recursively embedded children. *)
Definition legacy_project {K} (t : rw_term K unit nat) : term K.
(* RWVar _ i maps to TVar i; RWApp maps to TApp with recursively projected children. *)
Definition legacy_pattern {K} (t : term K) : rw_pattern K unit nat nat.
(* TVar i maps to RWHole tt i; TApp maps to RWPApp tt with recursively translated children. *)
Definition legacy_substitution {K} (sub : nat -> term K) : rw_substitution K unit nat nat :=
  fun i => Some (legacy_embed (sub i)).
Definition legacy_semantics {K C} (ev : K -> list C -> option C) (env : nat -> option C) :
    rw_semantics K unit nat C := RwSemantics env ev.
Definition legacy_admissible {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (sem : rw_semantics K unit nat C) : Prop :=
  exists env, ok env /\ sem = legacy_semantics ev env.
Definition legacy_variables {K} (t : term K) : list nat.
(* Left-to-right traversal of variable occurrences; repetitions are retained. *)
Definition legacy_rule_holes {K} (r : rewrite_rule K) : list nat :=
  nodup Nat.eq_dec (legacy_variables (rule_lhs r) ++ legacy_variables (rule_rhs r)).
Definition legacy_total_sub {K} (sub : rw_substitution K unit nat nat) (i : nat) : term K :=
  match sub i with Some t => legacy_project t | None => TVar i end.
Definition legacy_rule {K} (r : rewrite_rule K) : rw_rule K unit nat nat :=
  RwRule (legacy_rule_holes r)
    (fun i => if existsb (Nat.eqb i) (legacy_rule_holes r) then Some tt else None)
    (legacy_pattern (rule_lhs r)) (legacy_pattern (rule_rhs r))
    (fun sub => rule_side r (legacy_total_sub sub)).
Definition legacy_at {K} (pos : list nat) (t : term K) : option (term K).
Definition legacy_replace_at {K} (pos : list nat) (t u : term K) : option (term K).
Definition rw_at {K Sort V} (pos : list nat) (t : rw_term K Sort V) : option (rw_term K Sort V).
Definition rw_replace_at {K Sort V} (pos : list nat) (t u : rw_term K Sort V) :
    option (rw_term K Sort V).
(* An empty path selects/replaces the whole tree. A nonempty path selects the indexed application
   child recursively; a variable or out-of-range index returns None. *)

Theorem legacy_project_embed {K} (t : term K) : legacy_project (legacy_embed t) = t.
Theorem legacy_embed_typed {K} (t : term K) : rw_typed legacy_signature (legacy_embed t).
Theorem legacy_denote_agrees {K C} (ev : K -> list C -> option C) (env : nat -> option C)
    (t : term K) : rw_denote (legacy_semantics ev env) (legacy_embed t) = denote ev env t.
Theorem legacy_substitute_agrees {K} (sub : nat -> term K) (t : term K) :
  rw_instantiate (legacy_substitution sub) (legacy_pattern t) = Some (legacy_embed (subst_term sub t)).
Theorem legacy_at_agrees {K} (pos : list nat) (t : term K) :
  rw_at pos (legacy_embed t) = option_map legacy_embed (legacy_at pos t).
Theorem legacy_replace_agrees {K} (pos : list nat) (t u : term K) :
  rw_replace_at pos (legacy_embed t) (legacy_embed u) =
    option_map legacy_embed (legacy_replace_at pos t u).
Theorem legacy_equiv_agrees {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (t u : term K) :
  equiv_term ev ok t u <-> rw_equiv (legacy_admissible ev ok) (legacy_embed t) (legacy_embed u).
Theorem legacy_cost_agrees {K} (cost : K -> nat) (t : term K) :
  rw_tree_cost (fun _ => 0) cost (legacy_embed t) = term_cost cost t.
Theorem legacy_rule_wf {K} (r : rewrite_rule K) : rw_rule_wf legacy_signature (legacy_rule r).
Theorem legacy_rule_sound {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (r : rewrite_rule K) :
  rule_sound ev ok r -> rw_rule_sound legacy_signature (legacy_admissible ev ok) (legacy_rule r).
Theorem legacy_guard_uses_witness {K} (r : rewrite_rule K)
    (sub : rw_substitution K unit nat nat) :
  rw_condition (legacy_rule r) sub = rule_side r (legacy_total_sub sub).
Definition legacy_graph {K} (eg : egraph K) : rw_graph K unit nat.
Definition legacy_root {K} (eg : egraph K) : option rw_id.
Theorem legacy_saturate_direct {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (fuel : positive)
    (t : term K) :
  Forall (rule_sound ev ok) rules ->
  let eg := saturate EK rules fuel t in
  rw_graph_wf legacy_signature (legacy_graph eg) /\
  rw_graph_sound legacy_signature (legacy_admissible ev ok) (map legacy_rule rules)
    (legacy_graph eg) /\
  rw_productive (legacy_graph eg) /\
  exists c, legacy_root eg = Some c /\ rw_represents (legacy_graph eg) c (legacy_embed t).
```

The finite list of holes for a legacy rule is the duplicate-free union of the variables in its
left and right terms. A guard is evaluated on a total legacy substitution. For each index with a
provided Rewrite term witness it uses `legacy_project`; for any other index it uses `TVar i`.
This is one particular total witness and does not assume guard invariance under class equality.
Extra witness entries are allowed, so a guard can inspect variables absent from both rule sides.
The adapter invokes `rule_sound` on that very same total witness. It does not claim that an
arbitrary guard agrees on pointwise equal substitution functions; no functional extensionality
or new guard law is assumed. No claim is made that finite search enumerates all possible
substitutions or satisfies every guard. This search choice does not change `rule_side` or the
external replay checker.

Under C22 replay rejects missing entries in either rule side. The guard receives exactly the
total `legacy_subst` witness used in the rule-soundness premise, including extra bindings and
`TVar i` for an absent guard-only index. `equiv_term` is equality of `option` results, including
`None = None`.

ANA-6 implements its abstract `egraph` representation, `saturate`, `extract` and `optimise` on
the directly proved Rewrite engine from the start. The producer uses the finite witness adapter,
while the legacy
`extract` result still includes a replayable explanation. Carry enough positional rule steps
for the compatibility facade to reconstruct a certificate; do not require the direct core to
produce or check an explanation for its own preservation theorem. `extract` returns `None` when
it cannot produce a certificate accepted by the original `check_explanation`. The existing
`optimise_sound`, `check_explanation_sound`, `check_explanation_refl`, `term_eqb_spec` and the
`egraph_optimise_accepts` example retain their existing statements.

## REW-7: Order and SSA clients

These declarations live outside `Gaulois.Rewrite`. The Order adapter's facts permit `None`;
therefore they do not establish definedness. A definedness or nonzero guard needs an additional
client fact and proof. No concrete domain transfer is assumed merely from lattice laws.

```coq
Definition rw_order_holds {A C} (G : concretisation A C) (a : A) (result : option C) : Prop :=
  match result with None => True | Some c => gamma G a c end.
Definition rw_order_analysis {K Sort V A C} (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) :
    rw_analysis K Sort V C A :=
  RwAnalysis (rw_order_holds G) (top_value T) (join L) transfer.
Definition rw_order_transfer_sound {K Sort V A C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) : Prop :=
  forall g facts c, rw_graph_wf sig g ->
    rw_facts_valid admissible (rw_order_analysis L T G transfer) g facts ->
    rw_fact_valid admissible (rw_order_analysis L T G transfer) g c (transfer g facts c).
Theorem rw_order_analysis_laws {K Sort V A C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) :
  lattice_laws L -> concretisation_laws L G -> top_full T G ->
  rw_order_transfer_sound sig admissible L T G transfer ->
  rw_analysis_laws sig admissible (rw_order_analysis L T G transfer).

Definition ssa_rw_semantics {S O N E V K C Sort} (sv : ssa_view S O N E V K C) (s : S) :
    rw_semantics K Sort V C := RwSemantics (val sv s) (op_eval sv).
Theorem ssa_rewrite_value {S O N E V K C Sort H} (m : semantics S O)
    (sv : ssa_view S O N E V K C) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (root : rw_id) (input output : rw_term K Sort V) (s : S) (c : C) :
  ssa_view_laws m sv -> strict_ssa_laws m sv -> reachable_state m s ->
  admissible (ssa_rw_semantics sv s) ->
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  rw_denote (ssa_rw_semantics sv s) input = Some c ->
  rw_denote (ssa_rw_semantics sv s) output = Some c.

Definition ssa_region_state (S C : Type) := (S * option (option C))%type.
Definition ssa_region_semantics {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (expr : rw_term K Sort V) : semantics (ssa_region_state S C) C :=
  Semantics (fun _ => True)
    (fun before events after =>
      snd before = None /\ fst after = fst before /\
      snd after = Some (rw_denote (ssa_rw_semantics sv (fst before)) expr) /\
      events = match rw_denote (ssa_rw_semantics sv (fst before)) expr with
               | Some c => [c] | None => [] end).
Definition ssa_region_endings {S C} : endings (ssa_region_state S C) :=
  Endings (fun st => exists c, snd st = Some (Some c)) (fun st => snd st = Some None)
    (fun _ => False).
Definition ssa_region_relation {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (a b : ssa_region_state S C) : Prop :=
  a = b /\ admissible (ssa_rw_semantics sv (fst a)).
Theorem ssa_region_bisimulation {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V) :
  rw_equiv admissible input output ->
  bisimulation (ssa_region_semantics sv input) ssa_region_endings
    (ssa_region_semantics sv output) ssa_region_endings (ssa_region_relation sv admissible).
Theorem ssa_region_rewrite_behaviour {S O N E V K C Sort H} (sv : ssa_view S O N E V K C)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (root : rw_id)
    (input output : rw_term K Sort V) (s : S) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  admissible (ssa_rw_semantics sv s) ->
  same_behaviour (ssa_region_semantics sv input) ssa_region_endings (s, None)
    (ssa_region_semantics sv output) ssa_region_endings (s, None).

Record rw_replacement_laws {S1 S2 O K Sort V C} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V) : Prop := {
  rw_replacement_bisim : rw_equiv admissible input output -> bisimulation m1 e1 m2 e2 R
}.
Theorem rw_replacement_behaviour {S1 S2 O K Sort V H C} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (root : rw_id)
    (input output : rw_term K Sort V) (s : S1) (t : S2) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  rw_replacement_laws m1 e1 m2 e2 R admissible input output -> R s t ->
  same_behaviour m1 e1 s m2 e2 t.
```

The region model evaluates one pure expression against an SSA state's current values, emitting a
successful value or trapping. The required direct bisimulation theorem covers partial operations.
It does not model the surrounding SSA program, memory, or an edit to its instruction graph. For a
whole-program result, the client's replacement law must account for region boundaries, operand
availability, traps, effects and both programs' steps. The SSA value theorem alone does not imply
the whole-program result.

## Word client

The following toy client has one 32-bit word sort and free variables numbered by `nat`. Its
operators are extensible ordinary constructors, not cases in the Rewrite kernel. `WordRotl`
demonstrates adding a constructor and semantics without changing that kernel. All arithmetic
below uses Bits at width `32%positive`; division has Bits' total zero-divisor semantics.

```coq
Inductive rw_word_op : Type := WordLit (z : Z) | WordAdd | WordMul | WordDiv | WordRotl.
Definition rw_word_encoding : encoding rw_word_op.
Definition rw_word_sig : rw_signature rw_word_op unit nat :=
  RwSignature (fun _ => Some tt)
    (fun op args _ => match op, args with
      | WordLit _, [] => true
      | WordAdd, [_; _] | WordMul, [_; _] | WordDiv, [_; _] | WordRotl, [_; _] => true
      | _, _ => false
      end).
Definition rw_word_eval (op : rw_word_op) (args : list Z) : option Z :=
  match op, args with
  | WordLit z, [] => Some (wrap 32%positive z)
  | WordAdd, [x; y] => Some (wadd 32%positive x y)
  | WordMul, [x; y] => Some (wmul 32%positive x y)
  | WordDiv, [x; y] => Some (wudiv 32%positive x y)
  | WordRotl, [x; y] => Some (wrotl 32%positive x y)
  | _, _ => None
  end.
Definition rw_word_admissible (sem : rw_semantics rw_word_op unit nat Z) : Prop :=
  rw_eval_op sem = rw_word_eval /\
  forall v z, rw_var_value sem v = Some z -> is_word 32%positive z.
Definition rw_ground_pattern {K Sort V H} (t : rw_term K Sort V) : rw_pattern K Sort V H.
(* Replace each RWVar by RWPVar and each RWApp by RWPApp, preserving the tree. *)
Definition rw_word_add_zero : rw_rule rw_word_op unit nat nat :=
  RwRule [0] (fun h => if Nat.eqb h 0 then Some tt else None)
    (RWPApp tt WordAdd [RWHole tt 0; RWPApp tt (WordLit 0%Z) []]) (RWHole tt 0)
    (fun _ => true).
Definition rw_word_mul_one : rw_rule rw_word_op unit nat nat :=
  RwRule [0] (fun h => if Nat.eqb h 0 then Some tt else None)
    (RWPApp tt WordMul [RWHole tt 0; RWPApp tt (WordLit 1%Z) []]) (RWHole tt 0)
    (fun _ => true).
Definition rw_word_rotate_zero : rw_rule rw_word_op unit nat nat :=
  RwRule [0] (fun h => if Nat.eqb h 0 then Some tt else None)
    (RWPApp tt WordRotl [RWHole tt 0; RWPApp tt (WordLit 0%Z) []]) (RWHole tt 0)
    (fun _ => true).
Definition rw_word_div_self (t : rw_term rw_word_op unit nat) : rw_rule rw_word_op unit nat nat :=
  RwRule [] (fun _ => None)
    (RWPApp tt WordDiv [rw_ground_pattern t; rw_ground_pattern t])
    (RWPApp tt (WordLit 1%Z) []) (fun _ => true).
Definition rw_word_nonzero {F} (an : rw_analysis rw_word_op unit nat Z F) (f : F) : Prop :=
  ~ rw_fact_holds an f None /\
  forall z, rw_fact_holds an f (Some z) -> is_word 32%positive z /\ z <> 0%Z.
Definition rw_word_analysis : rw_analysis rw_word_op unit nat Z (option Z) :=
  RwAnalysis
    (fun fact result => match fact with None => True | Some z => result = Some (wrap 32%positive z) end)
    None (fun a _ => a) (fun _ _ _ => None).
Definition rw_word_nonzero_check (z : Z) : bool := negb (Z.eqb (wrap 32%positive z) 0%Z).
Theorem rw_word_analysis_laws : rw_analysis_laws rw_word_sig rw_word_admissible rw_word_analysis.
Theorem rw_word_singleton_nonzero (z : Z) : rw_word_nonzero_check z = true ->
  rw_word_nonzero rw_word_analysis (Some z).
Theorem rw_word_literal_fact {H} (rules : list (rw_rule rw_word_op unit nat H))
    (g : rw_graph rw_word_op unit nat) (c : rw_id) (z : Z) :
  Forall (rw_rule_sound rw_word_sig rw_word_admissible) rules ->
  rw_graph_sound rw_word_sig rw_word_admissible rules g ->
  rw_represents g c (RWApp tt (WordLit z) []) ->
  rw_fact_valid rw_word_admissible rw_word_analysis g c (Some z).
Theorem rw_word_add_zero_sound : rw_rule_sound rw_word_sig rw_word_admissible rw_word_add_zero.
Theorem rw_word_mul_one_sound : rw_rule_sound rw_word_sig rw_word_admissible rw_word_mul_one.
Theorem rw_word_rotate_zero_sound :
  rw_rule_sound rw_word_sig rw_word_admissible rw_word_rotate_zero.
Theorem rw_word_add_zero_wf : rw_rule_wf rw_word_sig rw_word_add_zero.
Theorem rw_word_mul_one_wf : rw_rule_wf rw_word_sig rw_word_mul_one.
Theorem rw_word_rotate_zero_wf : rw_rule_wf rw_word_sig rw_word_rotate_zero.
Theorem rw_word_div_self_wf (t : rw_term rw_word_op unit nat) :
  rw_typed rw_word_sig t -> rw_rule_wf rw_word_sig (rw_word_div_self t).
Theorem rw_word_div_self_sound {F} (an : rw_analysis rw_word_op unit nat Z F) (f : F)
    (g : rw_graph rw_word_op unit nat) (c : rw_id) (t : rw_term rw_word_op unit nat) :
  rw_word_nonzero an f -> rw_fact_valid rw_word_admissible an g c f -> rw_represents g c t ->
  rw_rule_sound rw_word_sig rw_word_admissible (rw_word_div_self t).
Definition rw_word_demo_add : option (rw_term rw_word_op unit nat).
Definition rw_word_demo_mul : option (rw_term rw_word_op unit nat).
Definition rw_word_demo_rotate : option (rw_term rw_word_op unit nat).
Definition rw_word_demo_div : option (rw_term rw_word_op unit nat).
Definition rw_word_demo_zero : option (rw_term rw_word_op unit nat).
Example rw_word_add_accepts : rw_word_demo_add = Some (RWApp tt (WordLit 7%Z) []).
Example rw_word_mul_accepts : rw_word_demo_mul = Some (RWApp tt (WordLit 7%Z) []).
Example rw_word_rotate_accepts : rw_word_demo_rotate = Some (RWApp tt (WordLit 7%Z) []).
Example rw_word_div_accepts : rw_word_demo_div = Some (RWApp tt (WordLit 1%Z) []).
Example rw_word_zero_rejected : rw_word_demo_zero = None.
```

`rw_word_div_self_sound` uses a validated fact for the exact represented witness. It proves a
ground rule for that witness, including definedness; no rule-level condition depends on an
unvalidated e-class analysis. Include executable examples for add-zero, multiply-by-one, the
nonzero division case and a false zero-divisor guard. Each example must use a nonempty admissible
environment, an accepted application and extraction of the expected term. The client can add a
rotation rule by registration without changing Rewrite. The generic SSA replacement theorem
above still requires a separately proved client bisimulation.

The demos run the directly proved engine with one accepted attempt: `7 + 0`, `7 * 1`, and
`7 / 7`, respectively; the rotation demo similarly uses `rotate-left(7, 0)`. Assign weight 1 to
literals and 2 to each other operator; extract from the
original root after the run. Before registering the ground division rule, the producer tests
`rw_word_nonzero_check`. The division demo uses the valid singleton fact for 7. For the singleton
fact for 0 the check fails, no division rule is registered or attempted, and the demo returns
`None`. No explanation checker is required for these direct demos.



<!-- C19 ANA-10a to ANA-10f memory contracts -->

## ANA-10a: allocation epochs

An allocation identity `L` is distinct from its allocation site `T`. An epoch is the lifetime
of one identity, not an allocation-site counter. Sites are historical: once assigned they persist
after free. A new live identity was not previously assigned a site, so freeing and then
allocating at the same site cannot reactivate the old identity. An inactive identity whose site
was never assigned may become live as a fresh allocation. The client defines and proves
`epoch_live` for its concrete memory semantics; the bytes view does not infer liveness from a
single byte, since an allocation can be empty or contain non-integer fragments.

```coq
(* AnalysesMemoryBase.v. *)
Record epoch_view (S O N E T L : Type) : Type := EpochView {
  epoch_bytes : bytes_view S O N E T L;
  epoch_live : S -> L -> bool
}.

Record epoch_laws {S O N E T L} (m : semantics S O) (ev : epoch_view S O N E T L) : Prop := {
  epoch_byte_laws : bytes_laws m (epoch_bytes ev);
  epoch_live_site : forall s l, reachable_state m s -> epoch_live ev s l = true ->
    exists t, bsite (epoch_bytes ev) s l = Some t;
  epoch_allocate_fresh : forall s tr s' l,
    reachable_state m s -> step m s tr s' ->
    epoch_live ev s l = false -> epoch_live ev s' l = true ->
    bsite (epoch_bytes ev) s l = None /\
    exists t, bsite (epoch_bytes ev) s' l = Some t
}.

Theorem epoch_no_resurrection {S O N E T L} (m : semantics S O)
    (ev : epoch_view S O N E T L) :
  epoch_laws m ev -> forall s tr s' l t,
    reachable_state m s -> bsite (epoch_bytes ev) s l = Some t -> epoch_live ev s l = false ->
    exec m s tr s' -> epoch_live ev s' l = false /\
      bsite (epoch_bytes ev) s' l = Some t.
```

The proof inducts over `exec`, applying `byte_site_stable` on each step. If a dead identity
became live, `epoch_allocate_fresh` would say its previously assigned site was `None`, a
contradiction. Reachability propagates along the run. This theorem is about concrete identity
and does not claim that only one allocation ever has a particular site. The baseline barrier
analysis retains its existing conservative site-level `accessible` and bytewise aggregation
obligations; it does not use a site's identity as an epoch identifier.

The original `invariant_load_sound` statement proves the byte half only. Its address-invariance
claim is supplied separately by the already-contracted `loop_invariant_sound`; do not claim
that the byte theorem alone proves a value or address equality.


## ANA-10b: memory graph

## Version graph: AnalysesMemoryGraph.v

Only reachable nodes and edges belong to the represented flow. The initial virtual edge into
each CFG entry is represented by `None`, separately for each target entry. A phi operand keyed
by `Some e` belongs to that exact incoming edge; its value is the outgoing version of `e`.
Entries with backedges can need a phi merging `MemoryLive` with incoming edge values. Phi and
definition identifiers are stable structural identifiers; `memory_versions` is an enumerable
list, not a proof-bearing record. No per-function field is needed: each graph represents one
function. The caller must select the correct function's graph.

```coq
Inductive memory_version (N E : Type) : Type :=
  | MemoryLive
  | MemoryPhi (node : N)
  | MemoryDef (edge : E) (index : nat).

Record memory_graph (N E : Type) : Type := MemoryGraph {
  memory_phis : list N;
  memory_versions : list (memory_version N E);
  memory_in : N -> memory_version N E;
  memory_before : E -> nat -> option (memory_version N E);
  memory_out : E -> memory_version N E;
  memory_operand : N -> option E -> option (memory_version N E)
}.

Definition memory_occurrence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (e : E) (i : nat) (a : memory_effect T) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
  nth_error (effects e) i = Some a.

Definition memory_phi_at {N E} (mg : memory_graph N E) (n : N) : Prop :=
  In n (memory_phis mg).

Definition memory_valid_version {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (v : memory_version N E) : Prop :=
  match v with
  | MemoryLive => True
  | MemoryPhi n => reachable g n /\ memory_phi_at mg n
  | MemoryDef e i => exists a, memory_occurrence g effects e i a /\ effect_is_def a = true
  end.

Definition memory_after {N E T} (e : E) (i : nat) (a : memory_effect T)
    (v : memory_version N E) : memory_version N E :=
  if effect_is_def a then MemoryDef e i else v.

Inductive memory_edge_flow {N E T} (mg : memory_graph N E) (e : E) :
    nat -> list (memory_effect T) -> memory_version N E -> memory_version N E -> Prop :=
  | memory_edge_nil : forall i v, memory_edge_flow mg e i [] v v
  | memory_edge_cons : forall i a rest v w,
      memory_before mg e i = Some v ->
      memory_edge_flow mg e (S i) rest (memory_after e i a v) w ->
      memory_edge_flow mg e i (a :: rest) v w.

Definition memory_arrival {N E} (mg : memory_graph N E) (n : N) (key : option E)
    (v : memory_version N E) : Prop :=
  (memory_phi_at mg n /\ memory_operand mg n key = Some v /\ memory_in mg n = MemoryPhi n) \/
  (~ memory_phi_at mg n /\ memory_in mg n = v).

Record memory_graph_wf {N E T} (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) : Prop := {
  memory_cfg_wf : graph_wf g;
  memory_phis_nodup : NoDup (memory_phis mg);
  memory_phi_reachable : forall n, memory_phi_at mg n -> reachable g n;
  memory_versions_nodup : NoDup (memory_versions mg);
  memory_versions_exact : forall v, In v (memory_versions mg) <->
    memory_valid_version g effects mg v;
  memory_entries_arrive : forall n, In n (Graph.entries g) ->
    memory_arrival mg n None MemoryLive;
  memory_edges_flow : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) ->
    memory_edge_flow mg e 0 (effects e) (memory_in mg (Graph.source g e)) (memory_out mg e);
  memory_edges_arrive : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) ->
    memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e);
  memory_in_valid : forall n, reachable g n ->
    memory_valid_version g effects mg (memory_in mg n);
  memory_out_valid : forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) -> memory_valid_version g effects mg (memory_out mg e);
  memory_before_domain : forall e i,
    (exists v, memory_before mg e i = Some v) <->
    exists a, memory_occurrence g effects e i a;
  memory_operand_domain : forall n k,
    (exists v, memory_operand mg n k = Some v) <->
    memory_phi_at mg n /\
    match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end
}.

Inductive memory_path_flow {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    N -> list E -> N -> Prop :=
  | memory_path_nil : forall n, memory_path_flow g effects mg n [] n
  | memory_path_cons : forall e es n,
      In e (Graph.out g (Graph.source g e)) ->
      memory_edge_flow mg e 0 (effects e) (memory_in mg (Graph.source g e)) (memory_out mg e) ->
      memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e) ->
      memory_path_flow g effects mg (Graph.target g e) es n ->
      memory_path_flow g effects mg (Graph.source g e) (e :: es) n.

Fixpoint memory_last_defs {N E T} (e : E) (i : nat) (effects : list (memory_effect T))
    (origin : memory_version N E) : memory_version N E :=
  match effects with
  | [] => origin
  | a :: rest => memory_last_defs e (S i) rest (memory_after e i a origin)
  end.

Definition memory_last_path {N E T} (effects : E -> list (memory_effect T)) (es : list E) :
    memory_version N E :=
  fold_left (fun origin e => memory_last_defs e 0 (effects e) origin) es MemoryLive.

Inductive memory_edge_provenance {N E T} (mg : memory_graph N E) (e : E) :
    nat -> list (memory_effect T) -> memory_version N E -> memory_version N E ->
    memory_version N E -> memory_version N E -> Prop :=
  | memory_edge_provenance_nil : forall i input origin,
      memory_edge_provenance mg e i [] input origin input origin
  | memory_edge_provenance_cons : forall i a rest input origin output last,
      memory_before mg e i = Some input ->
      memory_edge_provenance mg e (S i) rest (memory_after e i a input)
        (memory_after e i a origin) output last ->
      memory_edge_provenance mg e i (a :: rest) input origin output last.

Inductive memory_provenance {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (root : N) :
    list E -> N -> memory_version N E -> memory_version N E -> Prop :=
  | memory_provenance_entry : In root (Graph.entries g) ->
      memory_arrival mg root None MemoryLive ->
      memory_provenance g effects mg root [] root (memory_in mg root) MemoryLive
  | memory_provenance_edge : forall es e origin last,
      memory_provenance g effects mg root es (Graph.source g e)
        (memory_in mg (Graph.source g e)) origin ->
      In e (Graph.out g (Graph.source g e)) ->
      memory_edge_provenance mg e 0 (effects e) (memory_in mg (Graph.source g e)) origin
        (memory_out mg e) last ->
      memory_arrival mg (Graph.target g e) (Some e) (memory_out mg e) ->
      memory_provenance g effects mg root (es ++ [e]) (Graph.target g e)
        (memory_in mg (Graph.target g e)) last.

Definition memory_occurrence_history {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (es : list E) (e : E) (i : nat)
    (input origin : memory_version N E) : Prop :=
  memory_before mg e i = Some input /\
  memory_edge_provenance mg e 0 (firstn i (effects e)) (memory_in mg (Graph.source g e))
    (memory_last_path effects es) input origin /\
  origin = memory_last_defs e 0 (firstn i (effects e)) (memory_last_path effects es).

Theorem memory_path_correspondence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival mg root None MemoryLive /\ memory_path_flow g effects mg root es n.

Theorem memory_occurrence_input_valid {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall e i a, memory_occurrence g effects e i a -> exists v,
    memory_before mg e i = Some v /\ memory_valid_version g effects mg v /\
    (effect_is_def a = true -> In (MemoryDef e i) (memory_versions mg)).

Theorem memory_definition_before_occurrence {N E T} (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
  memory_graph_wf g effects mg ->
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin,
    memory_provenance g effects mg root es (Graph.source g e)
      (memory_in mg (Graph.source g e)) (memory_last_path effects es) /\
    memory_occurrence_history g effects mg es e i input origin.

Theorem memory_execution_correspondence {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) (mg : memory_graph N E) :
  memory_effect_laws m v ->
  memory_graph_wf (cfg (effect_graph v)) (edge_effects v) mg ->
  forall s es t, initial m s -> run_edges m (effect_graph v) s es t ->
    memory_arrival mg (point (effect_graph v) s) None MemoryLive /\
    memory_path_flow (cfg (effect_graph v)) (edge_effects v) mg
      (point (effect_graph v) s) es (point (effect_graph v) t).
```

`effect_transition_byte_covered` follows by induction over the same witness of the ordered
snapshot trace and byte equality's decidability, retaining the historical site at each event.
`memory_path_correspondence` is an induction over actual `path`, not a premise restating the
result. `memory_occurrence_input_valid` follows by induction over `memory_edge_flow` and the
validity of its starting version. `memory_definition_before_occurrence` unfolds the exact
prefix of each edge and identifies the path-specific origin as live-on-entry or the last
definition before that occurrence, including earlier iterations. Each arrival selects the
operand for its actual edge; a phi alone does not change the origin.
`memory_execution_correspondence` uses `run_edges_path`,
`entry_points` and `memory_path_correspondence`. Phi selection is indexed by
the incoming path edge, and the occurrence input before a read/write effect precedes its def.
An execution may revisit the same occurrence; the finite graph identifies the static occurrence,
while the path derivation preserves the sequence of dynamic visits. ANA-10c and ANA-10d must
construct a graph and directly prove `memory_graph_wf` for all inputs in their stated domain.
Neither theorem proves a walker correct or byte/value preservation.


## ANA-10c: frontier constructor

## Split-edge dominance model: AnalysesMemoryFrontier.v

An edge may contain several effects or differ from a parallel edge. Insert a distinct synthetic
node for each edge identity; all effects of that edge execute, in order, at its synthetic node.
A fresh root has one edge to each distinct entry. The synthetic root supplies `MemoryLive` on
each virtual entry path. Node and edge tags prevent collisions with client identifiers.

```coq
Inductive memory_dom_node (N E : Type) : Type :=
  | MemoryRoot
  | MemoryBlock (n : N)
  | MemoryEdge (e : E).

Inductive memory_dom_edge (N E : Type) : Type :=
  | MemoryStart (n : N)
  | MemoryBegin (e : E)
  | MemoryEnd (e : E).

Definition memory_dom_node_encoding {N E} (EN : encoding N) (EE : encoding E) :
  encoding (memory_dom_node N E).
Definition memory_dom_edge_encoding {N E} (EN : encoding N) (EE : encoding E) :
  encoding (memory_dom_edge N E).

Definition memory_dom_graph {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  Graph.t (memory_dom_node N E) (memory_dom_edge N E).
```

Its sole entry is `MemoryRoot`; its nodes are that root, `MemoryBlock n` for each original
node, and `MemoryEdge e` for each distinct edge listed under an original node. Root successors
are `MemoryStart n` for distinct entries; block successors are `MemoryBegin e` for the distinct
outgoing edge identities of that block; an edge-node's sole successor is `MemoryEnd e`.
`MemoryStart n` goes from root to block `n`; `MemoryBegin e` goes from block `source g e` to
edge-node `e`; `MemoryEnd e` goes from edge-node `e` to block `target g e`. Deduplication is by
the supplied injective encodings, preserving membership, and normalizes duplicate listings of
the *same* edge; different parallel edge identities are retained. Build the deduplicated lists
and indexes once. The `out` list for every tag outside the node list is empty.

```coq
Definition memory_dom_defs {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) : list (memory_dom_node N E).
(* MemoryRoot followed by each distinct MemoryEdge e of a reachable edge whose effect list
   contains an effect with effect_is_def = true. Preserve first-occurrence order in edges_of g. *)

Theorem memory_dom_graph_wf {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> graph_wf (memory_dom_graph EN EE g) /\
    (forall v, NoDup (Graph.out (memory_dom_graph EN EE g) v)).

Theorem memory_dom_reachable {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> forall n,
    (reachable (memory_dom_graph EN EE g) (MemoryBlock n) <-> reachable g n).

Definition memory_frontier_build {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  { mg : memory_graph N E | memory_graph_wf g effects mg }.

Theorem memory_frontier_phi_exact {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall n, memory_phi_at (proj1_sig (memory_frontier_build EN EE g effects Hwf)) n <->
    in_idf (memory_dom_graph EN EE g) (memory_dom_defs EN EE g effects) (MemoryBlock n).

Theorem memory_frontier_path {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival (proj1_sig (memory_frontier_build EN EE g effects Hwf)) root None MemoryLive /\
    memory_path_flow g effects (proj1_sig (memory_frontier_build EN EE g effects Hwf)) root es n.
```

`memory_frontier_build` computes reachable split graph and one index, directly constructs the
exact `SimpleLT` dominator tree, then uses `direct_idf` with `memory_dom_defs`. Insert a phi at
each original block in that IDF, with all reachable predecessor-edge operands plus the virtual
entry operand where applicable. Walk the dominator tree with an explicit stack: a block phi
sets the current version; at each edge-node, record the current version before each ordered
effect and replace it with `MemoryDef e i` after each defining effect; record the outgoing
version and fill the target phi operand for that exact edge. Restore the previous version when
returning from a subtree. For nodes without a phi, `memory_in` is the unique incoming version
proved by the dominance-frontier placement argument. Build all prepared adjacency, occurrence,
phi and output indexes once. Use binary fuel or a well-founded traversal measure.

Proof obligations: establish split-graph path and reachability agreement, including duplicate
listings, parallel edges, multiple entries and entry backedges; establish GRA-7's readiness after
deduplication; prove that only original block tags need phi placement; prove the IDF property
ensures a single reaching renamed version when no phi is present; prove the stack invariant,
complete predecessor operand population, occurrence domain and version enumeration. The
dependent result carries the resulting `memory_graph_wf` proof; the phi theorem additionally
establishes the exact unpruned IDF placement, and `memory_frontier_path` follows from ANA-10b.
These are direct construction proofs, not a checker's acceptance theorem.

Count split nodes and edge identities, occurrences, direct-IDF and dominator operations,
individual phi operands and output materialization, trie key-bit costs and stack storage.
No asymptotic bound or benchmark gate follows from the contract.


## ANA-10d: sealed constructor

```coq
(* AnalysesMemorySealed.v. *)
Definition memory_sealed_build {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  { mg : memory_graph N E | memory_graph_wf g effects mg }.

Theorem memory_sealed_path {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival (proj1_sig (memory_sealed_build EN EE g effects Hwf)) root None MemoryLive /\
    memory_path_flow g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf)) root es n.

Theorem memory_sealed_definition_before_occurrence {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin,
    memory_provenance g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf))
      root es (Graph.source g e)
      (memory_in (proj1_sig (memory_sealed_build EN EE g effects Hwf)) (Graph.source g e))
      (memory_last_path effects es) /\
    memory_occurrence_history g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf))
      es e i input origin.
```

Build reachable predecessor and outgoing-edge indexes once and process edges in their prepared
order. An entry has a virtual `MemoryLive` predecessor in addition to actual predecessor edges.
Memoize each block's current entry version. On a first read from an unsealed block, or a recursive
read that meets a block already in progress, install a `MemoryPhi` placeholder *before* following
predecessors. This breaks loops. When all reachable predecessors and the virtual entry (if any)
are known, seal the block, complete one operand per exact predecessor edge, and record ordered
effect inputs and outgoing edge versions. A sealed block with a single incoming value can use it
directly when no in-progress placeholder is needed; other blocks may retain a phi even when
operands coincide. The contract does not promise minimality, pruned placement or equality of
phi identifiers with the frontier backend. An optional trivial-phi elimination is permitted only
with a separately proved substitution respecting cyclic operands and path provenance.

Prove finite termination using a decreasing measure on unprocessed edges, unresolved block
queries and unfilled operand slots, with binary fuel or well-founded recursion. Count potential
operand slots from the complete prepared predecessor and entry indexes before allocating them;
creating a placeholder must not increase the remaining-work bound. Account for every pending
work item, including work created by a first read. A placeholder is installed once; every
reachable edge and every required operand is processed once. An unfinished operand is never
exposed as finalized. Establish
initial memo/index agreement, the pending-read invariant, complete sealing, exact occurrence
domains and valid versions; prove the resulting `memory_graph_wf` directly. The dependent
result carries that proof, while the two explicit theorems follow from ANA-10b. The
path-specific definition claim is not a static dominator-tree theorem. Count index, memo and
operand operations, key bits and produced output independently; do not claim a benchmark result
or an unproved asymptotic bound.


## ANA-10e: walker and legacy projection

## Alias-aware query: AnalysesMemoryWalk.v

A scope is an over-approximation of bytes, not a concrete object identity. The query can skip
an effect only when `memory_scopes_disjoint` proves the scopes share no byte at any site.
`MemoryAll` is never considered disjoint, including from an empty scope. `MemoryCall` uses its
declared complete summary; unknown calls and barriers have `MemoryAll` write scopes. This is a
flow-insensitive safe baseline: it does not rule out a separately proved, more precise alias
oracle later. A site may summarize multiple allocation identities.

```coq
Definition memory_scopes_disjoint {T} (ET : encoding T) (a b : memory_scope T) : bool :=
  match a, b with
  | MemoryRegions fs, MemoryRegions gs => footprints_disjoint ET fs gs
  | _, _ => false
  end.

Definition memory_effect_has_read {T} (a : memory_effect T) : bool :=
  match a with
  | MemoryWrite _ => false
  | _ => true
  end.

Theorem memory_scopes_disjoint_sound {T} (ET : encoding T) (a b : memory_scope T) :
  memory_scopes_disjoint ET a b = true -> forall t o,
    memory_scope_covers a t o -> memory_scope_covers b t o -> False.

Inductive memory_walk_next {N E T} (ET : encoding T) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> memory_version N E -> Prop :=
  | memory_walk_skip_def : forall e i a previous,
      nth_error (effects e) i = Some a -> effect_is_def a = true ->
      memory_scopes_disjoint ET (effect_writes a) q = true ->
      memory_before mg e i = Some previous ->
      memory_walk_next ET effects mg q (MemoryDef e i) previous
  | memory_walk_phi : forall n key previous,
      memory_operand mg n key = Some previous ->
      memory_walk_next ET effects mg q (MemoryPhi n) previous.

Inductive memory_walk_trace {N E T} (ET : encoding T)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> list (memory_version N E) -> Prop :=
  | memory_walk_single : forall v, memory_walk_trace ET effects mg q v [v]
  | memory_walk_cons : forall v w rest, memory_walk_next ET effects mg q v w ->
      memory_walk_trace ET effects mg q w rest -> memory_walk_trace ET effects mg q v (v :: rest).

Fixpoint memory_trace_last {A} (xs : list A) : option A :=
  match xs with
  | [] => None
  | [x] => Some x
  | _ :: rest => memory_trace_last rest
  end.

Definition memory_walk_terminal {N E T} (ET : encoding T)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (q : memory_scope T)
    (v : memory_version N E) : Prop :=
  forall w, ~ memory_walk_next ET effects mg q v w.

Record memory_clobber_result (N E : Type) : Type := MemoryClobberResult {
  clobber_roots : list (memory_version N E);
  clobber_complete : bool
}.

Definition memory_clobbers {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
  memory_clobber_result N E.

Theorem memory_clobbers_cover {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg start ->
  forall trace last, memory_walk_trace ET effects mg q start trace ->
    memory_trace_last trace = Some last ->
    (memory_walk_terminal ET effects mg q last \/ ~ NoDup trace) ->
    exists hit, In hit trace /\ In hit (clobber_roots (memory_clobbers EN EE ET g effects mg q
      start fuel)).

Theorem memory_clobbers_complete {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg start ->
  clobber_complete (memory_clobbers EN EE ET g effects mg q start fuel) = true ->
  forall v, In v (clobber_roots (memory_clobbers EN EE ET g effects mg q start fuel)) <->
    memory_walk_terminal ET effects mg q v /\
    exists trace, memory_walk_trace ET effects mg q start trace /\
      memory_trace_last trace = Some v.
```

The worker builds operand and effect indexes once, then visits versions in a deduplicated binary
fuel worklist. A noninterfering def follows its `memory_before`; a phi branches over every
operand. A terminal is retained. If fuel expires, every pending version is retained as a
conservative cut and `clobber_complete` is false. If revisiting a version prevents further
expansion, retain that version as a cut and set `clobber_complete` false; this handles cyclic
phis. A completed search returns precisely the reachable terminals, with duplicates removed.
No cutoff is allowed to report live-on-entry or absence of a clobber without a proof. The cover
theorem applies to a finite path ending in a terminal or containing a cycle. Since the graph is
finite, every infinite walk has a repeated finite prefix. Account for index construction,
visited versions, phi operands, scope checks, key bits and materialized roots.

## Path-specific soundness

The dynamic witness is the same entry path, incoming phi selection and ordered occurrence prefix
as ANA-10b's `memory_provenance`. On that history define a last may-clobber by folding only
defining effects whose write scope is *not* proved disjoint from the query. The initial value is
`MemoryLive`. A skipped effect's scope disjointness is proved by
`memory_scopes_disjoint_sound`; it is not assumed from the desired byte conclusion.

```coq
Fixpoint memory_last_clobbers {N E T} (ET : encoding T) (q : memory_scope T) (e : E)
    (i : nat) (effects : list (memory_effect T)) (origin : memory_version N E) :
    memory_version N E :=
  match effects with
  | [] => origin
  | a :: rest =>
      memory_last_clobbers ET q e (S i) rest
        (if effect_is_def a && negb (memory_scopes_disjoint ET (effect_writes a) q)
         then MemoryDef e i else origin)
  end.

Definition memory_path_last_clobber {N E T} (ET : encoding T) (q : memory_scope T)
    (effects : E -> list (memory_effect T)) (es : list E) : memory_version N E :=
  fold_left (fun origin e => memory_last_clobbers ET q e 0 (effects e) origin) es MemoryLive.

Theorem memory_clobbers_follow_execution {N E T} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) (fuel : positive) :
  memory_graph_wf g effects mg ->
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin trace hit,
    memory_provenance g effects mg root es (Graph.source g e)
      (memory_in mg (Graph.source g e)) (memory_last_path effects es) /\
    memory_occurrence_history g effects mg es e i input origin /\
    memory_walk_trace ET effects mg q input trace /\
    memory_trace_last trace = Some
      (memory_last_clobbers ET q e 0 (firstn i (effects e))
        (memory_path_last_clobber ET q effects es)) /\
    In hit trace /\ In hit (clobber_roots (memory_clobbers EN EE ET g effects mg q input fuel)).
```

The proof follows the actual provenance backwards, using the selected phi operand and each
preceding occurrence. If the dynamic path has no may-clobber it ends at `MemoryLive`; otherwise
it ends at its last may-clobber. The returned hit can be a conservative phi or pending version,
and is not thereby asserted to be a concrete write. In particular, a phi's alternatives do not
mean every alternative is executed.

## Legacy boundary: AnalysesMemoryLegacy.v

The legacy checker and byte theorem above include the proposed C14 site-encoding argument.
Their statements and the Ssa examples require independent review and type-checking.

```coq
Definition legacy_nodes {N E} (g : Graph.t N E) (start : N) (es : list E) : list N :=
  start :: map (Graph.target g) es.

Definition legacy_disjoint {T} (writes reads : list (footprint T)) : Prop :=
  forall t o, covered writes t o 1 -> covered reads t o 1 -> False.

Definition legacy_disjoint_b {T} (ET : encoding T) (writes reads : list (footprint T)) : bool :=
  negb (existsb (fun f => existsb (fun h =>
    Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site h)) &&
    Z.ltb (fp_lo f) (fp_hi f) && Z.ltb (fp_lo h) (fp_hi h) &&
    Z.ltb (fp_lo f) (fp_hi h) && Z.ltb (fp_lo h) (fp_hi f)) reads) writes).

Theorem legacy_disjoint_b_correct {T} (ET : encoding T) (writes reads : list (footprint T)) :
  legacy_disjoint_b ET writes reads = true <-> legacy_disjoint writes reads.

Definition legacy_pair_clear {F N E T} (f : F) (g : Graph.t N E)
    (writes reads : N -> list (footprint T)) (load : N) (d : mem_node F N) : Prop :=
  reachable g load /\
  match d with
  | MDef f' n => f' = f /\ reachable g n /\
      forall e es, In e (Graph.out g n) -> path g (Graph.target g e) es load ->
        forall k, In k (legacy_nodes g (Graph.target g e) es) ->
          legacy_disjoint (writes k) (reads load)
  | MLive f' => f' = f /\ forall entry es, In entry (Graph.entries g) ->
      path g entry es load -> forall k, In k (legacy_nodes g entry es) ->
        legacy_disjoint (writes k) (reads load)
  end.

Theorem no_clobber_check_correct {F N E T} (EN : encoding N) (EF : encoding F)
    (ET : encoding T) (f : F) (g : Graph.t N E) (writes reads : N -> list (footprint T))
    (ms : memory_ssa F N) :
  graph_wf g ->
  (no_clobber_check EN EF ET f g writes reads ms = true <->
    forall n d, In n (Graph.nodes g) -> def_of_load ms n = Some d ->
      legacy_pair_clear f g writes reads n d).

Definition project_memory_legacy {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (f : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (writes reads : N -> list (footprint T))
    (mg : memory_graph N E) (load_occurrence : N -> option (E * nat)) (fuel : positive) :
    memory_ssa F N.

Theorem project_memory_legacy_correct {F N E T} (EN : encoding N) (EE : encoding E)
    (EF : encoding F) (ET : encoding T) (f : F) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (writes reads : N -> list (footprint T))
    (mg : memory_graph N E) (load_occurrence : N -> option (E * nat)) (fuel : positive) :
  memory_graph_wf g effects mg ->
  no_clobber_check EN EF ET f g writes reads
    (project_memory_legacy EN EE EF ET f g effects writes reads mg load_occurrence fuel) = true.

```

Under C21 the checker rejects candidates at unreachable loads and `MDef` candidates naming an
unreachable or non-node definition. This explicitly authorized restriction ensures that prepared
finite-graph indexes cover every inspected walk. It checks precisely
`legacy_pair_clear` for node-local candidates. For `MDef f n`, compute forward reachability from
all targets of outgoing edges of `n`, intersect with reverse reachability from the load, and
inspect every node in the intersection; `MLive` starts forward reachability from all entries.
Include the load, self-loops, revisits of `n` and parallel edges. Build indexes once. The
legacy projection obtains a candidate from a singleton clobber result at the supplied load
occurrence. It first requires the occurrence's edge to have source `n`, be reachable, and its
effect to satisfy `memory_effect_has_read`; an invalid occurrence gives `None`. A
`MemoryDef e i` proposes `MDef f (Graph.source g e)`, `MemoryLive` proposes
`MLive f`, and every other result proposes none. It retains a proposal only when the direct
per-load finite-reachability decision establishes `legacy_pair_clear`; otherwise it returns
`None`. The projection's proof establishes that decision directly; the optional checker is an
independent boundary for external candidates. A singleton result alone does not prove the
stronger all-walks legacy condition.

Use `legacy_disjoint_b` for reflection, not `footprints_disjoint`: the latter conservatively
rejects some empty or reversed intervals. The exact test requires both ranges to be nonempty and
their half-open intervals to intersect at an integer offset. Prove this equivalence from the
definition of `covered` and injectivity of `ET`.

The existing `no_clobber_unchanged` statement remains unchanged except for the new `ET` binder
and its checker argument. Its induction uses `byte_site_stable`, `byte_frame`, the checker
correctness theorem and `run_edges_path`. The theorem preserves every byte of the same
historical allocation identity from after the selected definition edge (or function entry) to
the load, under the existing byte-view laws. The checker and this theorem do not imply a load
returns a particular value, remains accessible, or performs no trap. The existing
`memoryssa_accepts` and `memoryssa_rejects` Ssa examples are retained with the new encoding
argument; tests additionally cover cycles revisiting the definition, a self-loop, a load-node
write, multiple entries and a parallel edge whose write invalidates the legacy projection.


## ANA-10f: sparse flow and forwarding

## Sparse source system: AnalysesMemoryFlow.v

For a fixed query scope, associate each valid version with the terminal versions reachable by
the ANA-10e `memory_walk_next` relation. A terminal is `MemoryLive` or a def that cannot be
proved disjoint. Phi nodes query every incoming operand and disjoint defs query their prior
version. Cyclic phis are solved by a finite powerset constraint system; they are not unfolded
recursively without a visited set. The result is a function returned by the existing total
joining engine. The constraint system is the independent declarative specification; no
post-solution is advertised as least without the `solve_total_least` premises.

```coq
Definition memory_version_encoding {N E} (EN : encoding N) (EE : encoding E) :
  encoding (memory_version N E).

Definition memory_flow_facts {N E} (EN : encoding N) (EE : encoding E)
    (mg : memory_graph N E) : Type :=
  finite_set (memory_version_encoding EN EE) (memory_versions mg).

Definition memory_flow_lattice {N E} (EN : encoding N) (EE : encoding E)
    (mg : memory_graph N E) : lattice (memory_flow_facts EN EE mg) :=
  finite_powerset_lattice (memory_version_encoding EN EE) (memory_versions mg).

Definition memory_flow_system {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) :
    System.t (memory_version N E) (memory_version N E) (memory_flow_facts EN EE mg).

Definition memory_flow_static {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) : System.static (memory_flow_system EN EE ET g effects mg q).

Definition memory_flow_solve {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  { s : memory_version N E -> memory_flow_facts EN EE mg |
    post_solution (memory_flow_lattice EN EE mg) (memory_flow_system EN EE ET g effects mg q) s }.

Inductive memory_flow_reaches {N E T} (ET : encoding T) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> memory_version N E -> Prop :=
  | memory_flow_terminal : forall v, memory_walk_terminal ET effects mg q v ->
      memory_flow_reaches ET effects mg q v v
  | memory_flow_step : forall v w source, memory_walk_next ET effects mg q v w ->
      memory_flow_reaches ET effects mg q w source -> memory_flow_reaches ET effects mg q v source.

Theorem memory_flow_least {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  least_solution (memory_flow_lattice EN EE mg) (memory_flow_system EN EE ET g effects mg q)
    (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf)).

Theorem memory_flow_exact {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (Hwf : memory_graph_wf g effects mg) :
  forall start source,
  memory_valid_version g effects mg start ->
  (fmem (memory_version_encoding EN EE) source
    (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf) start) = true <->
    memory_flow_reaches ET effects mg q start source).

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
```

For arbitrary graphs the system enumerates only the finite supplied versions and the prepared
edge/entry keys; on a well-formed graph these enumerate all and only relevant operands. The
system has one constraint per distinct listed version; its target is that version. Its RHS
returns the singleton version for a terminal, asks and unions each distinct `memory_walk_next`
successor for a nonterminal, and has no side targets. Invalid versions have no constraint and
therefore receive bottom. The static dependency list is exactly the successors asked by the
RHS. Build version, occurrence and phi-operand indexes once. Use the finite powerset lattice,
`solve_total` with `Joining`, finite-height termination and an existing scheduler; expose its
function result. Prove RHS monotonicity, static dependency agreement, finite-height termination,
then `memory_flow_least` using `solve_total_least`. Induct on `memory_flow_reaches` for one
direction of exactness; show the reachable-terminal interpretation is a post-solution for the
other. Only valid starting versions are promised exactness. The predicate covers finite paths;
an infinite phi cycle alone cannot be an actual finite entry-to-load execution.

For each reachable read occurrence, clients query its `memory_before` version and its read
scope. Include the actual last may-clobber using the provenance-generated walk trace in
`memory_clobbers_follow_execution`, a proof that its endpoint is terminal, and
`memory_flow_exact`. The bounded walker's arbitrary cut alone is insufficient; its completion is
not required. `MemoryLive` represents entry memory; a def represents a possibly clobbering effect,
not a proof that it wrote all queried bytes. Explain values for unknown calls and barriers as
unknown unless further client semantics supply precision.

`memory_builders_flow_agree` applies `memory_flow_execution` to both directly proved builders
on the same path and query. Their path-observed last may-clobber is the same structural
definition occurrence or live-on-entry, although phi identifiers, conservative additional
sources and materialized sets may differ. It does not assert literal graph or set equality.

## Value and byte bridge: AnalysesMemoryForward.v

The width below is a count of bytes (`nat`), not a count of machine-word bits. Byte sequences are
in increasing address order; the client's decoder chooses representation, including endianness.
The existing `byte` observation is `option nat`; the bridge requires observed bytes to be below
256. A pointer fragment or inaccessible byte may be `None`, in which case forwarding is not
proved. Object identity is the same `L` value at both accesses, never merely the same site.

```coq
Definition memory_read_bytes {S O N E T L} (bv : bytes_view S O N E T L)
    (s : S) (l : L) (o : Z) (width : nat) : option (list nat).
(* Read exactly width consecutive offsets o, o+1, ..., o+width-1 in that order. Return None
   if any byte is None; width zero returns Some []. *)

Record memory_value_view (S E L V : Type) : Type := MemoryValueView {
  store_location : S -> E -> option (L * Z * nat);
  load_location : S -> E -> option (L * Z * nat);
  stored_value : S -> E -> V -> Prop;
  loaded_value : S -> E -> V -> Prop;
  decode_memory_value : list nat -> option V
}.

Record memory_value_laws {S O N E T L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V) : Prop := {
  memory_value_byte_range : forall s l o b, reachable_state m s -> byte bv s l o = Some b ->
    (b < 256)%nat;
  memory_store_encoding : forall s tr s' e l o w v,
    reachable_state m s -> step m s tr s' -> taken (bgv bv) s tr s' e ->
    store_location vv s e = Some (l, o, w) -> stored_value vv s e v ->
    exists bs, memory_read_bytes bv s' l o w = Some bs /\ decode_memory_value vv bs = Some v;
  memory_load_decoding : forall s tr s' e l o w v,
    reachable_state m s -> step m s tr s' -> taken (bgv bv) s tr s' e ->
    load_location vv s e = Some (l, o, w) -> loaded_value vv s e v ->
    exists bs, memory_read_bytes bv s l o w = Some bs /\ decode_memory_value vv bs = Some v
}.

Theorem memory_forward_value {S O N E T F L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V)
    (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F)
    (ms : memory_ssa F N) (reads : N -> list (footprint T)) :
  bytes_laws m bv -> memory_value_laws m bv vv ->
  no_clobber_check EN EF ET f (cfg (bgv bv)) (writes_at bv) reads ms = true ->
  forall s tr s1 e es t tr' t' e' n l ty o w stored loaded,
    reachable_state m s -> step m s tr s1 -> taken (bgv bv) s tr s1 e ->
    run_edges m (bgv bv) s1 es t -> point (bgv bv) t = n ->
    step m t tr' t' -> taken (bgv bv) t tr' t' e' ->
    def_of_load ms n = Some (MDef f (Graph.source (cfg (bgv bv)) e)) ->
    store_location vv s e = Some (l, o, w) -> load_location vv t e' = Some (l, o, w) ->
    stored_value vv s e stored -> loaded_value vv t e' loaded ->
    bsite bv s1 l = Some ty -> covered (reads n) ty o w -> stored = loaded.

Theorem memory_forward_projected {S O N E T F L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V)
    (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T) (f : F)
    (effects : E -> list (memory_effect T)) (reads : N -> list (footprint T))
    (mg : memory_graph N E) (loads : N -> option (E * nat)) (fuel : positive) :
  bytes_laws m bv -> memory_value_laws m bv vv ->
  memory_graph_wf (cfg (bgv bv)) effects mg ->
  forall s tr s1 e es t tr' t' e' n l ty o w stored loaded,
    reachable_state m s -> step m s tr s1 -> taken (bgv bv) s tr s1 e ->
    run_edges m (bgv bv) s1 es t -> point (bgv bv) t = n ->
    step m t tr' t' -> taken (bgv bv) t tr' t' e' ->
    def_of_load (project_memory_legacy EN EE EF ET f (cfg (bgv bv)) effects
      (writes_at bv) reads mg loads fuel) n = Some (MDef f (Graph.source (cfg (bgv bv)) e)) ->
    store_location vv s e = Some (l, o, w) -> load_location vv t e' = Some (l, o, w) ->
    stored_value vv s e stored -> loaded_value vv t e' loaded ->
    bsite bv s1 l = Some ty -> covered (reads n) ty o w -> stored = loaded.
```

`stored_value` and `loaded_value` denote the client's actual value at the respective successful
operation; the client proves that connection as part of its adapter, not by invoking the
forwarding theorem. Both byte encoding/decoding laws concern the actual single-step witnesses,
and the locations refer to one and the same allocation identity, start offset and width.
`memory_forward_value` follows from `no_clobber_unchanged` applied bytewise, equal ordered byte
lists and determinism of `decode_memory_value`; the read operation's success is an explicit
premise. It does not assert accessibility, absence of traps or semantics for pointer fragments.
The same theorem applies to `project_memory_legacy` via its directly proved correctness result;
clients may use any valid external legacy candidate with the optional checker.



<!-- C19 call analyses -->


## ANA-8a: directly proved call analysis

```coq
Record call_index (F P : Type) : Type := CallIndex {
  indexed_targets : P -> list F;
  indexed_callers : F -> list P
}.

Definition prepare_calls {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) : call_index F P.

Theorem prepare_calls_targets {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) :
  forall p, indexed_targets (prepare_calls EF EP cv resolve) p = resolve p.

Theorem prepare_calls_callers {S F P} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) :
  forall f p, In p (indexed_callers (prepare_calls EF EP cv resolve) f) <->
    (exists g, In g (functions cv) /\ In p (sites_of cv g)) /\ In f (resolve p).

Definition solve_scc_summaries {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) : F -> A.

Theorem solve_scc_summaries_post {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) ->
  post_solution (slat sp) (summary_system cv resolve sp)
    (solve_scc_summaries EF EP cv resolve sp HL Hheight).

Theorem solve_scc_summaries_least {S F P A} (EF : encoding F) (EP : encoding P)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) -> lub_laws (slat sp) ->
  monotone_system (slat sp) (summary_system cv resolve sp) ->
  least_solution (slat sp) (summary_system cv resolve sp)
    (solve_scc_summaries EF EP cv resolve sp HL Hheight).

Theorem solve_scc_summaries_sound {S O F P A} (m : semantics S O)
    (EF : encoding F) (EP : encoding P) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) (sc : step_cover S O A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
  graph_wf (call_graph cv resolve) -> calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) ->
    step_covers sc (solve_scc_summaries EF EP cv resolve sp HL Hheight f) s l s'.

Inductive reachable_context {S F P} (cv : calls_view S F P) (resolve : P -> list F)
    (k : nat) : F * list P -> Prop :=
  | context_root : forall f, In f (roots cv) -> reachable_context cv resolve k (f, [])
  | context_call : forall f c p g, reachable_context cv resolve k (f, c) ->
      In p (sites_of cv f) -> In g (resolve p) ->
      reachable_context cv resolve k (g, push_ctx k p c).

Definition solve_reachable_callstrings {S F P A} (EF : encoding F) (EP : encoding P)
    (k : nat) (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (HL : lattice_laws (slat sp)) (Hheight : inhabited (height (slat sp))) :
    F * list P -> A.

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

Definition arg_facts_indexed {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) : F -> nat -> A.

Theorem callers_index_wf {S F P} (EF : encoding F) (cv : calls_view S F P)
    (resolve : P -> list F) : Map.wf EF (callers_index EF cv resolve).

Theorem arg_facts_indexed_agrees {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) :
  Map.wf EF ix ->
  forall f i, arg_facts_indexed EF av ix L fact f i = arg_fact EF av ix L fact f i.
```

Card ANA-8a. Prepare caller and target indexes once for listed sites; retain `resolve` as the
fallback for all other sites. Targets preserve list order and duplicates. Normalize SCC adjacency
to remove duplicates and prove that it preserves reachability and meets the SCC preconditions.
The direct SCC engine processes the condensation in
callee-before-caller order and runs a fair indexed joining worklist inside each component, without
assuming recursion has no base case. It uses the existing graph and finite-height termination
evidence; prove each local update is a `raise`, all incoming dependencies are represented and
quiescence is a global post-solution. Reached-least gives leastness only under the separate lub
and monotonicity premises; `summary_sound` supplies the semantic corollary. Unknown target lists
must conservatively include the unknown environment or be accompanied by the explicit fallback
effects described by ANA-8c. Do not infer that a list of known functions covers an external call.
Test self and mutual recursion with a base case, disconnected components, multiple callers,
duplicate targets and unresolved calls. The retained ANA-8 bounded call strings are unchanged.
For malformed graphs, the total function falls back to the existing total joining solver; its
advertised SCC guarantees above are stated only under `graph_wf`.

Build the reachable `(function, bounded-call-string)` graph from roots once, and solve its
dependency-closed equations with the finite-height SCC engine. Each reachable context's
dependencies are reachable, so restriction and extension of solutions prove the stated agreement
with a least solution of the existing system. Return bottom for contexts outside that graph. Build
argument facts in one pass over indexed callers, preserving the original fold order and duplicates,
then use indexed function/position lookups; equality needs no commutativity or associativity.
The argument map must satisfy its explicit map invariant; the prepared callers map proves it.
On malformed input `solve_reachable_callstrings` returns bottom everywhere; its agreement theorem
requires `graph_wf`.
The retained `callstring_system` enumerates the finite contexts of length at most `k` whose sites
occur in the view, including the empty context. Unreachable such contexts remain in its equations;
the reachable solver omits them. Test `k = 0`, duplicate sites and target lists, and a malformed
caller/site association that takes the generic fallback.



## ANA-8b: directly proved call analysis

```coq
Inductive ip_kind (P : Type) : Type :=
  | IpInternal
  | IpCall (site : P)
  | IpReturn (site : P).

Record ip_edge (N P D : Type) : Type := IpEdge {
  ip_source : N;
  ip_target : N;
  ip_action : ip_kind P;
  ip_pairs : list (option D * option D)
}.

Record ip_problem (N P D : Type) : Type := IpProblem {
  ip_nodes : list N;
  ip_sites : list P;
  ip_facts : list D;
  ip_edges : list (ip_edge N P D)
}.

Definition ip_problem_wf {N P D} (q : ip_problem N P D) : Prop :=
  NoDup (ip_nodes q) /\ NoDup (ip_sites q) /\ NoDup (ip_facts q) /\
  (forall e, In e (ip_edges q) -> In (ip_source e) (ip_nodes q) /\
    In (ip_target e) (ip_nodes q) /\ In (None, None) (ip_pairs e) /\
    (match ip_action e with IpInternal => True | IpCall p | IpReturn p =>
       In p (ip_sites q) end) /\
    forall x y, In (x, y) (ip_pairs e) ->
      (match x with None => True | Some d => In d (ip_facts q) end) /\
      (match y with None => True | Some d => In d (ip_facts q) end)).

Inductive ip_step {N P D} (q : ip_problem N P D) :
    N * option D * list P -> ip_edge N P D -> N * option D * list P -> Prop :=
  | ip_step_internal : forall e x y stack,
      In e (ip_edges q) -> ip_action e = IpInternal -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, stack) e (ip_target e, y, stack)
  | ip_step_call : forall e p x y stack,
      In e (ip_edges q) -> ip_action e = IpCall p -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, stack) e (ip_target e, y, p :: stack)
  | ip_step_return : forall e p x y stack,
      In e (ip_edges q) -> ip_action e = IpReturn p -> In (x, y) (ip_pairs e) ->
      ip_step q (ip_source e, x, p :: stack) e (ip_target e, y, stack).

Inductive ip_path {N P D} (q : ip_problem N P D) :
    N * option D * list P -> N * option D * list P -> Prop :=
  | ip_path_refl : forall c, ip_path q c c
  | ip_path_step : forall c e c' c'', ip_step q c e c' -> ip_path q c' c'' ->
      ip_path q c c''.

Definition ifds_solve {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start : N) (seed : option D) : N -> option D -> bool.

Theorem ifds_solve_exact {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start : N) (seed : option D) :
  ip_problem_wf q -> In start (ip_nodes q) ->
  (match seed with None => True | Some d => In d (ip_facts q) end) ->
  forall n d, ifds_solve EN EP ED q start seed n d = true <->
    exists stack, ip_path q (start, seed, []) (n, d, stack).

Record ide_problem (N P D A : Type) : Type := IdeProblem {
  ide_graph : ip_problem N P D;
  ide_lattice : lattice A;
  ide_values : list A;
  ide_weight : ip_edge N P D -> option D -> option D -> A -> A
}.

Record ide_laws {N P D A} (q : ide_problem N P D A) : Prop := {
  ide_graph_wf : ip_problem_wf (ide_graph q);
  ide_value_finite : forall a, In a (ide_values q);
  ide_lat_laws : lattice_laws (ide_lattice q);
  ide_lub_laws : lub_laws (ide_lattice q);
  ide_distributive : forall e x y a b, In e (ip_edges (ide_graph q)) ->
    In (x, y) (ip_pairs e) ->
    equivalent (ide_lattice q)
      (ide_weight q e x y (join (ide_lattice q) a b))
      (join (ide_lattice q) (ide_weight q e x y a) (ide_weight q e x y b))
}.

Inductive ide_path {N P D A} (q : ide_problem N P D A) :
    N * option D * list P -> A -> N * option D * list P -> A -> Prop :=
  | ide_path_refl : forall c a, ide_path q c a c a
  | ide_path_step : forall n x stack e n' y stack' a c b,
      ip_step (ide_graph q) (n, x, stack) e (n', y, stack') ->
      ide_path q (n', y, stack') (ide_weight q e x y a) c b ->
      ide_path q (n, x, stack) a c b.

Definition ide_solve {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (EA : encoding A) (q : ide_problem N P D A) (start : N) (seed : option D) (a : A) :
    N -> option D -> A.

Theorem ide_solve_exact {N P D A} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (EA : encoding A) (q : ide_problem N P D A) (start : N) (seed : option D) (a : A) :
  ide_laws q -> In start (ip_nodes (ide_graph q)) ->
  (match seed with None => True | Some d => In d (ip_facts (ide_graph q)) end) ->
  forall n d,
    (forall stack b, ide_path q (start, seed, []) a (n, d, stack) b ->
      leb (ide_lattice q) b (ide_solve EN EP ED EA q start seed a n d) = true) /\
    (forall upper, (forall stack b, ide_path q (start, seed, []) a (n, d, stack) b ->
       leb (ide_lattice q) b upper = true) ->
      leb (ide_lattice q) (ide_solve EN EP ED EA q start seed a n d) upper = true).
```

Card ANA-8b. `None` is the distinguished zero fact; `Some d` is a client fact. Each pair is an
exploded-graph edge, including generation edges from zero. Every path starts with an empty stack;
returns match the most recent call site, while a query may end inside a callee. A client supplies
actual internal, call, return and call-to-return edges, and must model callbacks and unknown calls
conservatively. These results are exact for that finite problem; connecting its flows and weights
to a particular language requires separate local simulation laws from that client. The interface
takes one seed; clients needing both zero and ordinary initial facts query each seed and union the
answers, or join the corresponding IDE results.

Build edge, entry, return and fact indexes once. Use tabulation of balanced procedure summaries
and propagate reachable prefixes, including recursive SCCs, with deduplicated work. For IDE,
tabulate finite value functions and compose on matched paths; finite `ide_values` bounds their
extensional possibilities, represented by finite tables without functional extensionality. Track
reachability separately from values: a reachable bottom differs from no path, and a non-strict
weight must never be applied to a nonexistent path. Prove generated summaries correspond to
balanced paths and every balanced path is represented, then prove termination and the two exactness
directions. Distinct
traces may yield different values; the IDE theorem specifies their least upper bound, including
bottom when none exists. No equality with bounded call strings is claimed.

Test a matched call/return, a mismatched return rejected, nested and mutually recursive calls,
zero-generated facts, two paths with different IDE values, a non-strict bottom transfer on an
unreachable edge, and an unknown-call edge supplied by the client. References: Reps, Horwitz and
Sagiv, POPL 1995, and Sagiv, Reps and Horwitz, POPL
1996. No implementation is copied from those papers.



## ANA-8c: directly proved call analysis

```coq
Record return_projection (S N P D : Type) : Type := ReturnProjection {
  return_config : S -> N * option D * list P;
  normal_return : S -> bool
}.

Record return_projection_laws {S O N P D} (m : semantics S O)
    (q : ip_problem N P D) (rp : return_projection S N P D) (exit : N) : Prop := {
  return_local_step : forall s l t, reachable_state m s -> step m s l t ->
    ip_path q (return_config rp s) (return_config rp t);
  return_exit : forall s, normal_return rp s = true ->
    exists d stack, return_config rp s = (exit, d, stack)
}.

Definition may_return {N P D} (EN : encoding N) (EP : encoding P) (ED : encoding D)
    (q : ip_problem N P D) (start exit : N) (seed : option D) : bool :=
  existsb (ifds_solve EN EP ED q start seed exit)
    (None :: map (@Some D) (ip_facts q)).

Theorem may_return_sound {S O N P D} (m : semantics S O) (EN : encoding N)
    (EP : encoding P) (ED : encoding D) (q : ip_problem N P D)
    (rp : return_projection S N P D) (start exit : N) (seed : option D) (s : S) :
  ip_problem_wf q -> In start (ip_nodes q) ->
  (match seed with None => True | Some d => In d (ip_facts q) end) ->
  return_projection_laws m q rp exit -> reachable_state m s ->
  return_config rp s = (start, seed, []) ->
  may_return EN EP ED q start exit seed = false ->
  forall tr t, exec m s tr t -> normal_return rp t = false.

Record modref (T : Type) (ET : encoding T) (U : list (footprint T)) : Type := ModRef {
  mr_reads : option (finite_set (footprint_encoding ET) U);
  mr_writes : option (finite_set (footprint_encoding ET) U);
  mr_allocates : bool;
  mr_frees : bool;
  mr_orders : bool
}.

Definition mr_contains {T} {ET : encoding T} {U : list (footprint T)}
    (s : option (finite_set (footprint_encoding ET) U)) (f : footprint T) : bool :=
  match s with None => true | Some v => fmem (footprint_encoding ET) f v end.

Definition unknown_modref {T} (ET : encoding T) (U : list (footprint T)) : modref T ET U :=
  ModRef None None true true true.

Definition modref_lattice {T} (ET : encoding T) (U : list (footprint T)) :
    lattice (modref T ET U).
(* Each option is ordered by set inclusion with None as top; join unions sets and propagates None.
   The three flags use false <= true and disjunction. Bottom has empty sets and false flags. *)

Theorem modref_lattice_laws {T} (ET : encoding T) (U : list (footprint T)) :
  lattice_laws (modref_lattice ET U) /\ lub_laws (modref_lattice ET U).

Theorem modref_lattice_height {T} (ET : encoding T) (U : list (footprint T)) :
  NoDup U -> inhabited (height (modref_lattice ET U)).

Definition modref_spec {F P T} (ET : encoding T) (U : list (footprint T))
    (local_effect : F -> modref T ET U) : summary_spec F P (modref T ET U).
(* slat = modref_lattice; local = local_effect; via_call is the identity. *)

Record effect_observer (S O T : Type) : Type := EffectObserver {
  actual_reads : S -> list O -> S -> list (footprint T);
  actual_writes : S -> list O -> S -> list (footprint T);
  actual_allocates : S -> list O -> S -> bool;
  actual_frees : S -> list O -> S -> bool;
  actual_orders : S -> list O -> S -> bool
}.

Definition modref_covers {S O T} {ET : encoding T} {U : list (footprint T)}
    (obs : effect_observer S O T) (a : modref T ET U) (s : S) (l : list O) (t : S) : Prop :=
  (forall f, In f (actual_reads obs s l t) -> mr_contains (mr_reads a) f = true) /\
  (forall f, In f (actual_writes obs s l t) -> mr_contains (mr_writes a) f = true) /\
  (actual_allocates obs s l t = true -> mr_allocates a = true) /\
  (actual_frees obs s l t = true -> mr_frees a = true) /\
  (actual_orders obs s l t = true -> mr_orders a = true).

Record modref_local_laws {S O F P T} (m : semantics S O) (cv : calls_view S F P)
    (ET : encoding T) (U : list (footprint T)) (obs : effect_observer S O T)
    (local_effect : F -> modref T ET U) : Prop := {
  modref_local_step : forall s l t, reachable_state m s -> step m s l t ->
    modref_covers obs (local_effect (here cv s)) s l t
}.

Theorem modref_sound {S O F P T} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (ET : encoding T) (U : list (footprint T))
    (obs : effect_observer S O T) (local_effect : F -> modref T ET U)
    (sigma : F -> modref T ET U) :
  calls_view_laws m cv resolve -> modref_local_laws m cv ET U obs local_effect ->
  post_solution (modref_lattice ET U)
    (summary_system cv resolve (modref_spec ET U local_effect)) sigma ->
  forall s l t f, reachable_state m s -> step m s l t -> In f (active cv s) ->
    modref_covers obs (sigma f) s l t.
```

Card ANA-8c. `modref_lattice` is the product of two lifted finite powerset lattices and three
Boolean lattices. The producer proves its lattice laws and finite-height evidence from a
duplicate-free U; callers may also supply a post-solution directly. For an unknown external call
or callback whose effects are not separately summarized, join `unknown_modref` into its caller's
local effect. Allocations, frees, bulk accesses and ordering effects belong in the observer; a
byte-frame client must additionally prove that its actual-byte effects cover changed bytes and
that allocation identity and lifetime obey its own laws. The theorem alone does not establish
concrete byte equality or a strong update.

For no-return, each concrete step is simulated locally by an `ip_path`; `return_exit` identifies
the normal-return observation. Concatenate those paths along `exec`, apply `ifds_solve_exact`,
and use the finite fact universe. A false result excludes only normal returns, not traps,
exceptions, resource stops or divergence. Unknown calls must include all possible return and
callback paths. A recursive cycle with a base-case return must not be classified as no-return.

Test self-recursion with a base return, a cycle without a return, mismatched returns, unknown
external calls and callbacks, allocation/free, partial read/write ranges, and ordering effects.


<!-- C19 ANA-14 SEG -->

## ANA-14: sparse evaluation graphs

Merge this section into `docs/api/analyses.md`. These declarations are binding specifications
when adopted; they have not been type-checked or proved. `AnalysesSeg.v` owns every declaration
below. ANA-1's existing dense gen/kill systems and their semantic claims remain available.

An SEG is specialized to one expression `u` in `expr_universe`. Its cut nodes include graph
entries, exits, all joins and forks, both ends of every edge that generates or kills `u`, and
one deterministically chosen point in each otherwise cut-free directed cycle. Remaining
maximal paths are contracted. Every original edge belongs to exactly one nonempty segment;
an arc is identified by the first original edge of its segment. `ready` explicitly requires
well-formedness, unique outgoing edge identities and agreement of the prepared graph index.
It does not require reducibility, reachability from an entry, or unique predecessor vertices.

```coq
Definition seg_event {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (u : U) (e : E) : bool := mentions EU u (gen gk e) || kill gk e u.

Definition seg_bit_transfer {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (b : bool) : bool :=
  mentions EU u (gen gk e) || (b && negb (kill gk e u)).

Definition seg_must_lattice : lattice bool := dual_lattice bool_lattice bool_top andb.

Record seg_index (N E : Type) : Type := SegIndex {
  seg_graph : Graph.t N E;
  seg_paths : Map.t E (list E);
  seg_interiors : Map.t N (E * nat);
  seg_forward_summary : Map.t E (bool * bool);
  seg_backward_summary : Map.t E (bool * bool)
}.

Definition seg_path {N E} (EE : encoding E) (idx : seg_index N E) (a : E) : list E :=
  match Map.get EE a (seg_paths idx) with
  | Some es => es
  | None => []
  end.

Definition seg_internal_nodes {N E} (g : Graph.t N E) (es : list E) : list N :=
  map (Graph.target g) (removelast es).

Record seg_index_laws {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (is_event : E -> bool) (idx : seg_index N E) : Prop := {
  seg_wf : ready EN (seg_graph idx) (prepare EN (seg_graph idx));
  seg_entries : Graph.entries (seg_graph idx) = Graph.entries g;
  seg_nodes_original : incl (Graph.nodes (seg_graph idx)) (Graph.nodes g);
  seg_boundaries : forall n, In n (Graph.nodes g) ->
    (In n (Graph.entries g) \/ Graph.out g n = []) -> In n (Graph.nodes (seg_graph idx));
  seg_junctions : forall n, In n (Graph.nodes g) ->
    (length (Graph.out g n) <> 1 \/ length (pred_edges (prepare EN g) n) <> 1) ->
    In n (Graph.nodes (seg_graph idx));
  seg_event_endpoints : forall e, In e (edges_of g) -> is_event e = true ->
    In (Graph.source g e) (Graph.nodes (seg_graph idx)) /\
    In (Graph.target g e) (Graph.nodes (seg_graph idx));
  seg_path_valid : forall a, In a (edges_of (seg_graph idx)) ->
    exists es, seg_path EE idx a = a :: es /\
      path g (Graph.source (seg_graph idx) a) (a :: es) (Graph.target (seg_graph idx) a);
  seg_path_nodup : forall a, In a (edges_of (seg_graph idx)) -> NoDup (seg_path EE idx a);
  seg_internal_nodup : forall a, In a (edges_of (seg_graph idx)) ->
    NoDup (seg_internal_nodes g (seg_path EE idx a));
  seg_internal_lookup : forall a k n, In a (edges_of (seg_graph idx)) ->
    nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n ->
    Map.get EN n (seg_interiors idx) = Some (a,k);
  seg_edge_partition : forall e, In e (edges_of g) ->
    exists! a, In a (edges_of (seg_graph idx)) /\ In e (seg_path EE idx a);
  seg_no_event_inside : forall a, In a (edges_of (seg_graph idx)) ->
    (exists e, In e (seg_path EE idx a) /\ is_event e = true) ->
    seg_path EE idx a = [a];
  seg_interior_unique : forall n, In n (Graph.nodes g) ->
    ~ In n (Graph.nodes (seg_graph idx)) ->
    exists a k, Map.get EN n (seg_interiors idx) = Some (a,k) /\
      In a (edges_of (seg_graph idx)) /\
      nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n;
  seg_interior_only : forall n a k, Map.get EN n (seg_interiors idx) = Some (a,k) ->
    In a (edges_of (seg_graph idx)) /\
    nth_error (seg_internal_nodes g (seg_path EE idx a)) k = Some n /\
    ~ In n (Graph.nodes (seg_graph idx));
  seg_interior_degree : forall n, In n (Graph.nodes g) ->
    ~ In n (Graph.nodes (seg_graph idx)) ->
    length (Graph.out g n) = 1 /\ length (pred_edges (prepare EN g) n) = 1
}.

Definition build_expression_seg {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : seg_index N E.

Definition seg_summary_apply {E} (EE : encoding E) (a : E) (b : bool)
    (summaries : Map.t E (bool * bool)) : bool :=
  match Map.get EE a summaries with
  | Some (f, t) => if b then t else f
  | None => b
  end.

Definition seg_forward_transfer {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E)
    (a : E) (b : bool) : bool :=
  seg_summary_apply EE a b (seg_forward_summary idx).

Definition seg_backward_transfer {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E)
    (a : E) (b : bool) : bool :=
  seg_summary_apply EE a b (seg_backward_summary idx).

Definition seg_available_system {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) :
    System.t N (dense_constraint N E) bool :=
  forward_system (seg_graph idx) (fun _ => false) (seg_forward_transfer EE EU gk u idx).

Definition seg_busy_system {S O N E U C} (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) :
    System.t N (dense_constraint N E) bool :=
  backward_system (seg_graph idx)
    (fun n => match Graph.out (seg_graph idx) n with [] => false | _ => true end)
    (seg_backward_transfer EE EU gk u idx).

Definition seg_reconstruct_available {N E} (EN : encoding N) (EE : encoding E)
    (idx : seg_index N E) (transfer : E -> bool -> bool) (cut : N -> bool) : N -> bool.
Definition seg_reconstruct_busy {N E} (EN : encoding N) (EE : encoding E)
    (idx : seg_index N E) (transfer : E -> bool -> bool) (cut : N -> bool) : N -> bool.

Definition seg_available {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : N -> bool.
Definition seg_busy {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) : N -> bool.
```

At a cut point reconstruction returns `cut n`. At a stored interior `(a,k)`, available folds
`transfer` forward from the cut source over the first `S k` segment edges; busy folds backward
from the cut target over the remaining edges after those first `S k`. Both return false for a
node outside the original graph. Segment and interior indexes are constructed once, not by
scanning paths within solver iterations. Eventless cycle anchors prevent an unrepresented node
or accidental empty boundary on a sink-free SCC. For an expression outside `expr_universe`,
`seg_available` and `seg_busy` return false on all nodes because the dense carrier clamps it.
For a member, the producers build the index, solve the appropriate must Boolean constraint
system directly with finite-height joining, and reconstruct all requested original points.

```coq
Theorem seg_must_laws : lattice_laws seg_must_lattice.
Theorem seg_must_lub : lub_laws seg_must_lattice.

Theorem seg_bit_distributive {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (a b : bool) :
  seg_bit_transfer EU gk u e (a && b) =
    (seg_bit_transfer EU gk u e a && seg_bit_transfer EU gk u e b).

Theorem build_expression_seg_correct {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  seg_index_laws EN EE (cfg (gkview gk)) (seg_event EU gk u)
    (build_expression_seg EN EE EU gk u).

Theorem build_expression_seg_summaries {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (u : U) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  forall a b, In a (edges_of (seg_graph (build_expression_seg EN EE EU gk u))) ->
    seg_forward_transfer EE EU gk u (build_expression_seg EN EE EU gk u) a b =
      fold_left (fun acc e => seg_bit_transfer EU gk u e acc)
        (seg_path EE (build_expression_seg EN EE EU gk u) a) b /\
    seg_backward_transfer EE EU gk u (build_expression_seg EN EE EU gk u) a b =
      fold_right (fun e acc => seg_bit_transfer EU gk u e acc) b
        (seg_path EE (build_expression_seg EN EE EU gk u) a).

Theorem seg_available_exact {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  least_solution (avail_lattice EU gk) (available_system EU gk) sigma ->
  forall n u, In n (Graph.nodes (cfg (gkview gk))) ->
    seg_available EN EE EU gk u n = fmem EU u (sigma n).

Theorem seg_busy_exact {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (gk : genkill_view S O N E U C) (sigma : N -> avail_set EU gk) :
  ready EN (cfg (gkview gk)) (prepare EN (cfg (gkview gk))) ->
  least_solution (avail_lattice EU gk) (busy_system EU gk) sigma ->
  forall n u, In n (Graph.nodes (cfg (gkview gk))) ->
    seg_busy EN EE EU gk u n = fmem EU u (sigma n).
```

The proof establishes `seg_bit_distributive`, the Boolean dual lattice laws, each path summary,
cut-graph coverage and both directions of least-solution reconstruction. Boundary conditions
are dual: empty on every forward entry and every backward sink; non-boundary seeds are true in
the backward must order. A cut-free sinkless cycle has the least Boolean-must solution true;
it is not treated as an exit. Partition and leastness arguments apply to all graph nodes,
including unreachable ones. This is equality to the finite syntactic equations, not to all
feasible executions. No general relational domain is assumed distributive.


[seg-paper]: https://www.cs.wustl.edu/~cytron/cse531/Resources/Papers/sprsdf.pdf


<!-- C19 ANA-15 and ANA-16 -->


## ANA-16: factored expression SSA graph and edge-specific phi translation
The statements are uncompiled contracts. This graph is an analysis representation, not an SSA
construction or general SSA repair facility. The producer discovers a finite family of typed
expression instances from the program's seeds; the caller does not supply that family.
For the factored redundancy graph and expression-phi context, see
[Kennedy et al., *Partial redundancy elimination in SSA form*][ssapre-paper].

```coq
Record pre_expression_view (S O N E U C : Type) : Type := PreExpressionView {
  pre_genkill : genkill_view S O N E U C;
  pre_total_pure : U -> bool;
  pre_recomputed : E -> option U
}.

Record pre_expr_ssa (S O B BE N E V K C U : Type) : Type := PreExprSsa {
  pre_ssa_points : ssa_points B BE N E V;
  pre_ssa_view : ssa_view S O B BE V K C;
  pre_expression : pre_expression_view S O N E U C;
  pre_seed_expressions : list U;
  pre_value_universe : list V;
  pre_expression_shape : U -> positive;
  pre_operands : U -> list V;
  pre_expr_eval : U -> (V -> option C) -> option C;
  pre_phi_translate : BE -> U -> option U;
  pre_initial_available : U -> bool;
  pre_exit_point : N -> bool
}.

Inductive pre_expr_in_family {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) : U -> Prop :=
| pre_family_seed : forall u, In u (pre_seed_expressions a) -> pre_expr_in_family a u
| pre_family_translate : forall u be u', pre_expr_in_family a u ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_phi_translate a be u = Some u' -> pre_expr_in_family a u'.

Definition pre_expr_universe {S O B BE N E V K C U} (EBE : encoding BE) (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) : list U.

Definition pre_phi_env {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) (be : BE)
    (env : V -> option C) (x : V) : option C.
Definition pre_phi_operand {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) (be : BE) (x : V) : V.
Definition pre_point_edge_index {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) : Map.t BE E.

Record pre_expr_ssa_laws {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) : Prop := {
  pre_expr_points : ssa_point_laws (pre_ssa_points a);
  pre_expr_strict : reachable_point_ssa (pre_ssa_points a);
  pre_expr_block_graph : block_graph (pre_ssa_points a) = cfg (base (pre_ssa_view a));
  pre_expr_point_graph : live_graph (point_model (pre_ssa_points a)) =
    cfg (gkview (pre_genkill (pre_expression a)));
  pre_expr_reachable_blocks : forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    reachable (block_graph (pre_ssa_points a)) b;
  pre_expr_reachable_points : forall n,
    In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
    reachable (live_graph (point_model (pre_ssa_points a))) n;
  pre_expr_entry_position : exists b n,
    Graph.entries (block_graph (pre_ssa_points a)) = [b] /\
    Graph.entries (live_graph (point_model (pre_ssa_points a))) = [n] /\
    nth_error (points_in_block (pre_ssa_points a) b) 0 = Some n;
  pre_expr_entry_no_incoming : forall b be,
    In b (Graph.entries (block_graph (pre_ssa_points a))) ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be <> b;
  pre_expr_params_nodup : forall b, NoDup (block_params (pre_ssa_points a) b);
  pre_expr_value_nodup : NoDup (pre_value_universe a);
  pre_expr_occurrences : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    In u (pre_seed_expressions a);
  pre_expr_initial_in_family : forall u, pre_initial_available a u = true -> pre_expr_in_family a u;
  pre_expr_finite_operands : forall u, pre_expr_in_family a u ->
    incl (pre_operands a u) (pre_value_universe a);
  pre_expr_shape_identity : forall u u', pre_expr_in_family a u -> pre_expr_in_family a u' ->
    pre_expression_shape a u = pre_expression_shape a u' ->
    pre_operands a u = pre_operands a u' -> u = u';
  pre_expr_shape_arity : forall u u', pre_expr_in_family a u -> pre_expr_in_family a u' ->
    pre_expression_shape a u = pre_expression_shape a u' ->
    length (pre_operands a u) = length (pre_operands a u');
  pre_expr_runtime : forall s u,
    uval (pre_genkill (pre_expression a)) s u = pre_expr_eval a u (val (pre_ssa_view a) s);
  pre_expr_operand_support : forall u env1 env2,
    (forall x, In x (pre_operands a u) -> env1 x = env2 x) ->
    pre_expr_eval a u env1 = pre_expr_eval a u env2;
  pre_expr_kill_operand : forall e u,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_expr_in_family a u -> kill (pre_genkill (pre_expression a)) e u = true ->
    exists x, In x (pre_operands a u) /\ In x (edge_def (point_model (pre_ssa_points a)) e);
  pre_expr_def_home : forall e x,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    In x (edge_def (point_model (pre_ssa_points a)) e) ->
    home (pre_ssa_view a) x = block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e);
  pre_expr_cross_no_defs : forall e be,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    block_edge_of (pre_ssa_points a) e = Some be ->
    edge_def (point_model (pre_ssa_points a)) e = [];
  pre_expr_real_internal : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    block_edge_of (pre_ssa_points a) e = None /\
    (forall b, e <> parameter_edge (pre_ssa_points a) b);
  pre_expr_closed_translation : forall be u,
    In be (edges_of (block_graph (pre_ssa_points a))) -> pre_expr_in_family a u ->
    exists u', pre_phi_translate a be u = Some u';
  pre_expr_translation_shape : forall be u u', pre_expr_in_family a u ->
    pre_phi_translate a be u = Some u' -> pre_expression_shape a u' = pre_expression_shape a u;
  pre_expr_translation_operands : forall be u u', pre_expr_in_family a u ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_phi_translate a be u = Some u' ->
    pre_operands a u' = map (pre_phi_operand EV a be) (pre_operands a u);
  pre_expr_translation_pure : forall be u u', pre_total_pure (pre_expression a) u = true ->
    pre_phi_translate a be u = Some u' -> pre_total_pure (pre_expression a) u' = true;
  pre_expr_translation_eval : forall be u u' env,
    In be (edges_of (block_graph (pre_ssa_points a))) -> pre_expr_in_family a u ->
    pre_phi_translate a be u = Some u' ->
    pre_expr_eval a u (pre_phi_env EV a be env) = pre_expr_eval a u' env
}.
```

`pre_phi_env` evaluates every incoming operand from the *same* pre-edge environment and
simultaneously assigns it to the corresponding target block parameter. For every variable not
in the target parameter list it returns its old value; `phi_args_length` makes all positional
lookups defined. `pre_phi_operand` maps a target parameter to that edge's corresponding argument
and leaves every other value unchanged; distinct parameters make this mapping unambiguous. The
translation law is local expression substitution at that edge. It includes
operation, type, width and all semantic flags through `pre_expr_eval` and the expression
identity; translation never assumes a whole-program equivalence. A client proves the bridge
between this environment operation and the actual target parameter step from its VIEW-8 and
SSA laws. A memoized worklist starts with `pre_seed_expressions`, translates each newly
discovered expression on indexed block edges, and inserts new expression instances once.
Every translation preserves the seed shape and arity and every operand is in the finite value
universe. Shape plus ordered operands injectively identifies expressions, so only finitely many
instances exist. No upfront enumeration of operand tuples is performed; a per-shape exponential
bound and the actual family and translated-edge output are charged. Compute binary fuel from
that finite bound, seed count and the number of block edges; on an input violating the laws,
fuel exhaustion returns the accumulated partial list. Prove that for inputs satisfying the laws
it cannot exhaust while work remains. A translation-closed family is a proved output, not a
caller-supplied list. Single-entry reachable strictness defines the
supported domain. Its unique entry has no incoming edges, so entry needs no virtual phi
operand. A graph with an entry backedge is outside this API and must be normalized by its
client or analyzed with the dense/SEG APIs. Clients with unreachable nodes retain dense/SEG
analyses on those nodes. Reachable irreducible components away from entry are supported.


```coq
Definition frg_defs {S O B BE N E V K C U} (EB : encoding B) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (u : U) : list B.
Inductive frg_phi_needed {S O B BE N E V K C U} (EB : encoding B) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : U -> B -> Prop :=
| frg_phi_operand_param : forall u b x, pre_expr_in_family a u ->
    In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
    In x (pre_operands a u) -> In x (block_params (pre_ssa_points a) b) ->
    frg_phi_needed EB EU a u b
| frg_phi_seed : forall u d b, pre_expr_in_family a u -> In d (frg_defs EB EU a u) ->
    in_df (block_graph (pre_ssa_points a)) d b -> frg_phi_needed EB EU a u b
| frg_phi_iter : forall u d b, frg_phi_needed EB EU a u d ->
    in_df (block_graph (pre_ssa_points a)) d b -> frg_phi_needed EB EU a u b
| frg_phi_translate_seed : forall u b be u' b', frg_phi_needed EB EU a u b ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    pre_phi_translate a be u = Some u' ->
    in_df (block_graph (pre_ssa_points a)) (Graph.source (block_graph (pre_ssa_points a)) be) b' ->
    frg_phi_needed EB EU a u' b'.
Definition frg_phi_sites {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (u : U) : FinSet.t B.
Theorem pre_expr_universe_exact {S O B BE N E V K C U} (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  NoDup (pre_expr_universe EBE EV EU a) /\
  forall u, In u (pre_expr_universe EBE EV EU a) <-> pre_expr_in_family a u.

Theorem frg_phi_sites_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall u b, pre_expr_in_family a u ->
    (FinSet.mem EB b (frg_phi_sites EB EBE EV EU a u) = true <->
      frg_phi_needed EB EU a u b).

Theorem pre_phi_env_parameter {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be i x y env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    nth_error (block_params (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) i = Some x ->
    nth_error (block_edge_args (pre_ssa_points a) be) i = Some y ->
    pre_phi_env EV a be env x = env y.

Theorem pre_point_edge_index_exact {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) :
  ssa_point_laws s -> forall be e,
    (Map.get EBE be (pre_point_edge_index EBE s) = Some e <->
      In e (edges_of (live_graph (point_model s))) /\ block_edge_of s e = Some be).

Theorem pre_phi_env_frame {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be x env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    ~ In x (block_params (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_phi_env EV a be env x = env x.

Theorem pre_phi_env_substitution {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be x env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_phi_env EV a be env x = env (pre_phi_operand EV a be x).

Theorem frg_translation_agrees {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be u u' env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_expr_in_family a u -> pre_phi_translate a be u = Some u' ->
    pre_expr_eval a u (pre_phi_env EV a be env) = pre_expr_eval a u' env.
```

```coq
Inductive frg_version (B E U : Type) : Type :=
| FrUnavailable (u : U)
| FrInitial (u : U)
| FrFresh (e : E) (u : U)
| FrPhi (b : B) (u : U).

Record frg_operand (B E U : Type) : Type := FrgOperand {
  frg_operand_version : frg_version B E U;
  frg_operand_real_use : bool
}.

Record factored_redundancy_graph (B BE E U : Type) : Type := FactoredRedundancyGraph {
  frg_versions : list (frg_version B E U);
  frg_occurrence_index : Map.t E (frg_version B E U);
  frg_fresh_index : FinSet.t E;
  frg_phi_index : FinSet.t (B * U);
  frg_phi_operands : Map.t ((B * U) * BE) (frg_operand B E U);
  frg_unsafe_seeds : FinSet.t (B * U)
}.

Definition frg_version_encoding {B E U} (EB : encoding B) (EE : encoding E)
    (EU : encoding U) : encoding (frg_version B E U).
Definition frg_version_expr {B E U} (d : frg_version B E U) : U :=
  match d with
  | FrUnavailable u | FrInitial u | FrFresh _ u | FrPhi _ u => u
  end.
Definition frg_version_point {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (d : frg_version B E U) : option N :=
  match d with
  | FrUnavailable _ => None
  | FrInitial _ => nth_error (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0
  | FrFresh e _ => Some (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
  | FrPhi b _ => Some (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b))
  end.
Definition frg_nearest_version {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (u : U) (n : N) (d : frg_version B E U) : Prop :=
  In d (frg_versions f) /\ frg_version_expr d = u /\
  exists q, frg_version_point a d = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q n /\
    forall d' q', In d' (frg_versions f) -> frg_version_expr d' = u ->
      frg_version_point a d' = Some q' ->
      dominates (live_graph (point_model (pre_ssa_points a))) q' n ->
      dominates (live_graph (point_model (pre_ssa_points a))) q' q.

Definition frg_no_dominating_real_use {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (n : N) (d : frg_version B E U) : Prop :=
  forall e, Map.get EE e (frg_occurrence_index f) = Some d ->
    ~ dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n.

Definition frg_reusable {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (u : U) (n : N) (d : frg_version B E U) : Prop :=
  frg_nearest_version a f u n d /\
  exists q, frg_version_point a d = Some q /\
    forall es, path (live_graph (point_model (pre_ssa_points a))) q es n ->
      Forall (fun e => Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q) es ->
      Forall (fun e => kill (pre_genkill (pre_expression a)) e u = false) es.

Record frg_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : Prop := {
  frg_versions_nodup : NoDup (frg_versions f);
  frg_versions_exact : forall d, In d (frg_versions f) <->
    match d with
    | FrUnavailable u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true
    | FrInitial u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
        pre_initial_available a u = true
    | FrFresh e u => In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
        pre_recomputed (pre_expression a) e = Some u /\
        FinSet.mem EE e (frg_fresh_index f) = true
    | FrPhi b u => FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true
    end;
  frg_phi_exact : forall b u, FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
    frg_phi_needed EB EU a u b;
  frg_occurrence_exact : forall e u, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
    exists d, Map.get EE e (frg_occurrence_index f) = Some d /\ In d (frg_versions f) /\
      frg_version_expr d = u /\
      (d = FrFresh e u \/ frg_reusable a f u
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d);
  frg_occurrence_domain : forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    pre_recomputed (pre_expression a) e = Some (frg_version_expr d) /\
    pre_total_pure (pre_expression a) (frg_version_expr d) = true;
  frg_fresh_exact : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    (FinSet.mem EE e (frg_fresh_index f) = true <->
      Map.get EE e (frg_occurrence_index f) = Some (FrFresh e u));
  frg_fresh_domain : forall e, FinSet.mem EE e (frg_fresh_index f) = true ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a))));
  frg_fresh_required : forall e u,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
    (FinSet.mem EE e (frg_fresh_index f) = true <->
      ~ exists d, frg_reusable a f u (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d);
  frg_operand_exact : forall b u be,
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    exists op u', pre_phi_translate a be u = Some u' /\
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op /\
      frg_version_expr (frg_operand_version op) = u' /\
      (frg_operand_version op = FrUnavailable u' \/
       exists n e, frg_version_point a (frg_operand_version op) = Some n /\
         Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some e /\
         dominates (live_graph (point_model (pre_ssa_points a))) n
           (Graph.source (live_graph (point_model (pre_ssa_points a))) e));
  frg_operand_domain : forall b u be op,
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op ->
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true /\
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.target (block_graph (pre_ssa_points a)) be = b;
  frg_operand_selection : forall b u be op pe u',
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    pre_phi_translate a be u = Some u' ->
    (frg_operand_version op = FrUnavailable u' <->
      ~ exists d, frg_reusable a f u'
        (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) d) /\
    (frg_operand_version op <> FrUnavailable u' ->
      frg_reusable a f u' (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)
        (frg_operand_version op));
  frg_operand_real_use_exact : forall b u be op pe,
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    (frg_operand_real_use op = true <->
      exists e, Map.get EE e (frg_occurrence_index f) = Some (frg_operand_version op) /\
        dominates (live_graph (point_model (pre_ssa_points a)))
          (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
          (Graph.source (live_graph (point_model (pre_ssa_points a))) pe));
  frg_down_seed_exact : forall b u,
    (FinSet.mem (pair_encoding EB EU) (b,u) (frg_unsafe_seeds f) = true <->
      exists n, In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) /\
        frg_nearest_version a f u n (FrPhi b u) /\
        frg_no_dominating_real_use EE a f n (FrPhi b u) /\
        (pre_exit_point a n = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) n = [] \/
         exists e, In e (Graph.out (live_graph (point_model (pre_ssa_points a))) n) /\
           kill (pre_genkill (pre_expression a)) e u = true /\
           pre_recomputed (pre_expression a) e <> Some u))
}.
Definition build_frg {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : factored_redundancy_graph B BE E U.

Theorem build_frg_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  frg_wf EB EBE EN EE EV EU a (build_frg EB EBE EN EE EV EU a).
```

The producer performs a deterministic exact dominator-tree depth-first walk. Each block emits an
enter event, its expression-phi definitions, instruction events in point order, one translated
operand event per outgoing edge and target phi, then an exit event for each ending point and a
leave event. Relevant alteration events occur at the corresponding point edge; every event is
indexed once by the expression family and the original edge identity. Phi sites use the exact
operand-parameter and cross-translation IDF closure defined above. The graph has the single entry
without incoming edges specified there; empty and unreachable components are outside this backend.

An implementation may keep a private event machine with persistent scoped snapshots. Its
rename rules are:

1. Enter saves the current stack depths, and leave restores them. A phi definition pushes
   `(FrPhi b u, false)` onto that expression's stack. An initial frame is `(FrInitial u,false)`
   when `pre_initial_available a u` is true and `(FrUnavailable u,false)` otherwise.
2. At `FrOccurrence e u`, inspect the top frame for the exact translated operand version. If
   it denotes an available matching version, record that version for `e` and set the current
   frame's `frg_frame_real_use` to true; do not introduce a new definition. If the top is
   unavailable, record `(FrFresh e u,true)`, mark `e` in `frg_fresh_occurrences`, and push the
   fresh frame. If a new expression class invalidates an unused phi frame, add that phi to
   `frg_down_seed` before pushing the new frame.
3. At `FrPhiOperand b u be translated`, read the translated expression's current frame at
   the source of that *particular* `be`. Store both its version and its current real-use flag
   in `frg_operand_index[(b,u,be)]`. The value flag describes occurrences since that version
   became current along this scoped rename path; it is not inferred from the version constructor.
   A missing/undefined version is recorded as `FrUnavailable translated`.
4. An alteration or exit marks the current phi down-unsafe if its frame's real-use flag is false.
   Alteration invalidates the affected expression frame. A phi-operand class mismatch similarly
   seeds the current unused phi before the frame is replaced. Exactly the paper's finite
   Rename initialization and scope restoration are performed; no CFG path is scanned in a loop.

`frg_defs EB EU a u` is the deduplicated union of the entry block, blocks containing eligible real
occurrences of `u`, and the SSA home blocks of every operand in `pre_operands a u`. Their
frontiers seed placement even when predecessor computations have different translated identities.
Separately, an operand that is a block parameter directly seeds a phi for that family expression
at the listed nonentry block itself. `frg_phi_sites` computes exactly the least relation above:
each seed's iterated frontier is included, and every phi operand recursively seeds the
predecessor block's frontier for its translated expression. Prepare a value-to-parameter-block
index once from listed nonentry blocks. Visit each family expression's ordered operands and use
that index to emit deduplicated direct seeds, then add these to the worklist with frontier seeds.
Do not rescan all block parameter lists per expression or during closure. The producer uses
GRA-5's frontier index and exact GRA-2f dominators with a deduplicated worklist over the finite
expression/block universe. Charge index and seed construction, including candidate pairs and
emitted seeds, separately from reached closure nodes and arcs. The entry sentinel's availability
is exactly `pre_initial_available`, not automatically true. Only reachable block edges feed the
translation closure.
The block and expression encodings supply executable identity to `frg_defs`; `frg_phi_sites`
also uses the block-edge and value encodings to compute the finite translated family.

`frg_phi_sites_exact` retains both directions for this enlarged relation. `frg_phi_exact` retains
the same iff and filters family expressions by `pre_total_pure`; the direct seed itself has no
purity premise. The new rule captures a join expression whose parameter translates to different
incoming expressions. It does not by itself establish global placement sufficiency or optimality;
the producer, rename, operand selection and down-safety obligations remain to be proved.

[ssapre-paper]: https://doi.org/10.1145/319301.319348


## ANA-15: SSA PRE placement and local realization

proofs. `AnalysesSsaPre.v` owns the placement and legality declarations;
`AnalysesSsaPreSemantics.v` owns the realization and behavior declarations. ANA-14 supplies
exact syntactic availability and anticipation. This first supported transformation computes
pure, total expressions after existing edges and replaces existing expression evaluations with
previously computed SSA values. It neither constructs SSA from arbitrary code nor exposes a
general SSA repair, destruction or allocation utility.
The [SSAPRE paper][ssapre-paper] supplies the placement context.

### Expression view and direct placement producer

```coq
Inductive pre_version (E U : Type) : Type :=
| PreInitial (u : U)
| PreComputed (e : E) (u : U)
| PreInserted (e : E) (u : U)
| PreMerged (parameter_edge : E) (u : U).

Definition pre_version_expr {E U} (version : pre_version E U) : U :=
  match version with
  | PreInitial u | PreComputed _ u | PreInserted _ u | PreMerged _ u => u
  end.

Record pre_plan (E U : Type) : Type := PrePlan {
  pre_insertions : Map.t E (FinSet.t U);
  pre_deletions : Map.t E (FinSet.t U);
  pre_reload_versions : Map.t E (pre_version E U);
  pre_phi_versions : Map.t ((E * E) * U) (pre_version E U)
}.

Definition pre_inserted {E U} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (e : E) (u : U) : bool :=
  FinSet.mem EU u (live_index_get EE e (pre_insertions p)).
Definition pre_deleted {E U} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (e : E) (u : U) : bool :=
  FinSet.mem EU u (live_index_get EE e (pre_deletions p)).

Definition pre_extended_view {S O N E U C} (EE : encoding E) (EU : encoding U)
    (v : pre_expression_view S O N E U C) (p : pre_plan E U) : genkill_view S O N E U C.

Definition pre_version_point {S O N E U C} (v : pre_expression_view S O N E U C)
    (version : pre_version E U) : option N :=
  match version with
  | PreInitial _ => nth_error (Graph.entries (cfg (gkview (pre_genkill v)))) 0
  | PreComputed e _ | PreInserted e _ | PreMerged e _ =>
      Some (Graph.target (cfg (gkview (pre_genkill v))) e)
  end.

Definition pre_version_written {E U} (EE : encoding E) (e : E)
    (version : pre_version E U) : bool :=
  match version with
  | PreInitial _ => false
  | PreComputed d _ | PreInserted d _ | PreMerged d _ => Pos.eqb (encode EE e) (encode EE d)
  end.

Definition pre_phi_update {E U C} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (incoming parameter_edge : E)
    (old : pre_version E U -> option C) (version : pre_version E U) : option C :=
  match version with
  | PreMerged d u =>
      if Pos.eqb (encode EE d) (encode EE parameter_edge) then
        match Map.get (pair_encoding (pair_encoding EE EE) EU) ((d,incoming),u)
          (pre_phi_versions p) with
        | Some selected => old selected
        | None => old version
        end
      else old version
  | _ => old version
  end.

Definition pre_placement_legal {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (v : pre_expression_view S O N E U C) (p : pre_plan E U) : Prop :=
  (forall e u, In e (edges_of (cfg (gkview (pre_genkill v)))) ->
    pre_inserted EE EU p e u = true ->
    pre_total_pure v u = true /\ kill (pre_genkill v) e u = false /\
    exists parameter_edge merged_u,
      Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter_edge,e),merged_u)
        (pre_phi_versions p) = Some (PreInserted e u)) /\
  (forall e u, In e (edges_of (cfg (gkview (pre_genkill v)))) ->
    pre_deleted EE EU p e u = true ->
    pre_recomputed v e = Some u /\ pre_total_pure v u = true /\
    exists version n, Map.get EE e (pre_reload_versions p) = Some version /\
      pre_version_point v version = Some n /\
      dominates (cfg (gkview (pre_genkill v))) n
        (Graph.source (cfg (gkview (pre_genkill v))) e)).

```

`pre_extended_view` keeps the original graph, kill function and expression evaluation, and
extends `gen e` by the finite set of expressions inserted *after* `e`. For a legal plan,
`kill e u = false`; consequently an inserted expression's value is unchanged by that edge under
the client's gen/kill laws. The extended finite universe includes inserted translated expressions
as well as original ones. Only original graph edges appear in either output map. A single original
edge may have multiple insertions but at most its one `pre_recomputed` deletion.

The producer is the factored SSA PRE algorithm specified below. Semantic safety does not depend
on eventual execution because inserted computations are total and silent. Account for graph
preparation, expression instances, SSA operand translation and placement output. No computational
or temporary-lifetime optimality is claimed.

```coq
Record ssapre_facts (B U : Type) : Type := SsaPreFacts {
  ssapre_downsafe : Map.t (B * U) bool;
  ssapre_can_available : Map.t (B * U) bool;
  ssapre_later : Map.t (B * U) bool
}.

Definition live_bool_get {K} (EK : encoding K) (k : K) (m : Map.t K bool) : bool :=
  match Map.get EK k m with Some b => b | None => false end.

Inductive ssapre_down_unsafe {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) : B * U -> Prop :=
| ssapre_down_seed : forall b u,
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_unsafe_seeds f) = true ->
    ssapre_down_unsafe EB EU EBE f (b,u)
| ssapre_down_step : forall b u b' u' be op,
    ssapre_down_unsafe EB EU EBE f (b',u') ->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be) (frg_phi_operands f) = Some op ->
    frg_operand_real_use op = false -> frg_operand_version op = FrPhi b u ->
    ssapre_down_unsafe EB EU EBE f (b,u).

Inductive ssapre_cannot {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) (down : B * U -> bool) :
    B * U -> Prop :=
| ssapre_cannot_seed : forall b u be op x,
    down (b,u) = false ->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op ->
    frg_operand_version op = FrUnavailable x -> ssapre_cannot EB EU EBE f down (b,u)
| ssapre_cannot_step : forall b u b' u' be op,
    ssapre_cannot EB EU EBE f down (b,u) -> down (b',u') = false ->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be) (frg_phi_operands f) = Some op ->
    frg_operand_real_use op = false -> frg_operand_version op = FrPhi b u ->
    ssapre_cannot EB EU EBE f down (b',u').

Inductive ssapre_later_reset {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) (can : B * U -> bool) :
    B * U -> Prop :=
| ssapre_later_seed : forall b u be op,
    can (b,u) = true ->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be) (frg_phi_operands f) = Some op ->
    frg_operand_real_use op = true ->
    (forall x, frg_operand_version op <> FrUnavailable x) ->
    ssapre_later_reset EB EU EBE f can (b,u)
| ssapre_later_step : forall b u b' u' be op,
    ssapre_later_reset EB EU EBE f can (b,u) -> can (b',u') = true ->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be) (frg_phi_operands f) = Some op ->
    frg_operand_version op = FrPhi b u -> ssapre_later_reset EB EU EBE f can (b',u').

Definition solve_ssapre {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : ssapre_facts B U.

Definition ssa_pre_place {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : pre_plan E U.

Theorem solve_ssapre_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  forall b u, FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_downsafe facts) = true <->
      ~ ssapre_down_unsafe EB EU EBE f (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true <->
      ~ ssapre_cannot EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_downsafe facts)) (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_later facts) = true <->
      live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true /\
      ~ ssapre_later_reset EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_can_available facts)) (b,u)).

Theorem ssa_pre_place_legal {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_placement_legal EN EE EU (pre_expression a) (ssa_pre_place EB EBE EN EE EV EU a).

Theorem ssa_pre_phi_versions_correct {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  forall b u be pe version,
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,pe),u) (pre_phi_versions p) = Some version ->
    exists u', pre_phi_translate a be u = Some u' /\ pre_version_expr version = u' /\
      (version = PreInserted pe u' \/ exists n,
        pre_version_point (pre_expression a) version = Some n /\
        dominates (live_graph (point_model (pre_ssa_points a))) n
          (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)).
```

The three inductive predicates are **least reset sets**. Down-safety begins with the
independent CFG exit/alteration seeds in `frg_unsafe_seeds`, then propagates backward through
phi operands without real uses. Can-be-available begins true and resets a non-down-safe phi
with an unavailable operand; reset propagates forward only to non-down-safe phi users through
operands without real uses. Later begins at can-be-available and resets at phis with a real-use
operand; reset propagates forward through phi users that remain can-be-available. Their exposed
Boolean flags are complements of the appropriate reset sets, not false-initialized least
availability. Construct reverse/forward operand indexes once and process each reset once.

For each phi, `will_be_avail` is `can && negb later`. The finalizer inserts on an operand if
its phi will be available and the operand is unavailable, or it has no real use and is defined
by a phi that will not be available. It resolves each incoming block edge to the unique point
edge, translates the operand expression, and records `PreInserted` for an inserted operand;
otherwise it records the actual reaching `PreInitial`, `PreComputed`, or `PreMerged` version.
It records the reaching version for each reload and deletes only an occurrence with a proved
available, dominating version. The two result maps in `pre_plan` make phi selection and reloads
reviewable. The direct producer builds the FRG, including ANA-16's operand-parameter phi seeds,
solves the reset phases, finalizes versions and returns those maps. It does not call a candidate
checker as its primary implementation.

The proof must establish the paper's reset-closure invariants, actual per-edge translation,
placement safety, every selected incoming version's dominance at that predecessor and each
reload version's dominance at the occurrence. Use ANA-16's operand and seed exactness, then
prove the phi-aware cache invariant using `pre_phi_env_substitution` and the local join law.
The realizer theorem preserves finite traces, final/trap/stop/stuck outcomes and divergence,
with bounded silent administrative steps. There is no blanket computational or temporary
lifetime optimality theorem. Charge expression discovery, IDF/rename work, FRG nodes and phi
operands, reset visits, version maps and final output; no benchmark gate is introduced.

### Realization boundary

The realizer is client-supplied because the library does not prescribe a language's instruction
syntax. The plan identifies expressions by their operation, type, width, semantic flags and
ordered operands. `pre_eval` evaluates one expression in the source state. A client's validity
law for a `pre_total_pure` expression must give a value for every reachable state at an insertion
or deletion, no memory or event effects, no trap or resource stop, and finite completion. A
client whose operations can trap, allocate, observe or stop must classify them false unless it
has a separately proved specialization that establishes those facts at every planned occurrence.

The client realizes a plan by (1) computing each insertion after its original edge, (2) replacing
each selected evaluation by an already available cached value, and (3) selecting edge-aligned
SSA values at joins using the actual predecessor edge, including parallel edges. The target may
split an edge into finitely many administrative target points. Its projection `pre_origin`
maps every boundary target point to an original point and every administrative point to the
original edge being realized. The source graph and the target graph need not be equal. A macro
target transition traverses exactly one original edge and its finite target-only administrative
chain; `pre_origin` supplies the point correspondence.

```coq
Inductive pre_origin (N E : Type) : Type :=
| PrePoint (n : N)
| PreOnEdge (e : E) (remaining : nat).

Record pre_realizer (S O N E NT ET U C : Type) : Type := PreRealizer {
  pre_source : semantics S O;
  pre_source_end : endings S;
  pre_source_graph : graph_view S O N E;
  pre_target : pre_plan E U -> semantics S O;
  pre_target_end : pre_plan E U -> endings S;
  pre_target_graph : pre_plan E U -> graph_view S O NT ET;
  pre_origin_of : pre_plan E U -> NT -> pre_origin N E;
  pre_project_edge : pre_plan E U -> ET -> option E;
  pre_eval : S -> U -> option C;
  pre_cached : S -> pre_version E U -> option C;
  pre_core_agree : S -> S -> Prop;
  pre_measure : pre_plan E U -> S -> nat
}.

Definition pre_cache_agree {S O N E NT ET U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (v : pre_expression_view S O N E U C)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) (n : N) (s t : S) : Prop :=
  pre_core_agree r s t /\
  forall e u version, Graph.source (cfg (gkview (pre_genkill v))) e = n ->
    pre_deleted EE EU p e u = true -> Map.get EE e (pre_reload_versions p) = Some version ->
    pre_cached r t version = pre_eval r s u.

Definition pre_boundary {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (n : N) (t : S) : Prop :=
  pre_origin_of r p (point (pre_target_graph r p) t) = PrePoint n.

Definition pre_exit_covered {S O B BE N E NT ET V K U C}
    (a : pre_expr_ssa S O B BE N E V K C U) (r : pre_realizer S O N E NT ET U C) : Prop :=
  forall s k, reachable_state (pre_source r) s ->
    ends_as (pre_source r) (pre_source_end r) k s ->
    pre_exit_point a (point (pre_source_graph r) s) = true.

Definition pre_phi_source_laws {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) : Prop :=
  forall be e s0 l0 s1 l1 s2,
    reachable_state (pre_source r) s0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some e ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 e ->
    step (pre_source r) s1 l1 s2 ->
    taken (pre_source_graph r) s1 l1 s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    forall x, val (pre_ssa_view a) s2 x = pre_phi_env EV a be (val (pre_ssa_view a) s0) x.

Definition pre_admin {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t : S) : Prop :=
  exists k, pre_origin_of r p (point (pre_target_graph r p) t) = PreOnEdge e k.

Inductive pre_finish {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) : S -> S -> Prop :=
| pre_finish_boundary : forall t,
    pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t -> pre_finish r p e t t
| pre_finish_admin : forall t t1 t2 te, pre_admin r p e t ->
    step (pre_target r p) t [] t1 -> taken (pre_target_graph r p) t [] t1 te ->
    pre_project_edge r p te = None -> pre_finish r p e t1 t2 -> pre_finish r p e t t2.

Definition pre_macro_step {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (e : E) (t : S) (l : list O) (t' : S) : Prop :=
  pre_boundary r p (Graph.source (cfg (pre_source_graph r)) e) t /\
  exists t1 te, step (pre_target r p) t l t1 /\
    taken (pre_target_graph r p) t l t1 te /\ pre_project_edge r p te = Some e /\
    pre_finish r p e t1 t'.

Inductive pre_paired_run {S O N E NT ET U C} (r : pre_realizer S O N E NT ET U C)
    (p : pre_plan E U) (s0 t0 : S) : S -> S -> Prop :=
| pre_paired_initial : initial (pre_source r) s0 -> initial (pre_target r p) t0 ->
    pre_boundary r p (point (pre_source_graph r) s0) t0 -> pre_core_agree r s0 t0 ->
    pre_paired_run r p s0 t0 s0 t0
| pre_paired_step : forall s t e l s' t', pre_paired_run r p s0 t0 s t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_core_agree r s' t' ->
    pre_paired_run r p s0 t0 s' t'.
```

The first target step projects to exactly one original edge. Its remaining steps are silent,
remain on that edge, and stop at its first target boundary. This retains parallel-edge identity
and prevents a macro from hiding a second original edge, including a boundary self-loop.

### Local realization laws and theorem

The public `pre_local_laws` record takes the encodings, expression view, realizer and plan. It
must contain the following independent, one-step laws, all quantified over reachable source and
target states and the specific edge being executed:

1. **Source/target graph and projection.** Source view equals `gkview (pre_genkill v)`;
   both graph-view laws hold. Target initial points project to the corresponding source entry;
   each target boundary transition either starts the same original edge or is an explicitly
   classified administrative step on it. Every boundary-to-boundary target segment contains
   exactly one original edge. Distinct incoming edges, including parallel ones, remain distinct.
2. **Operand/operation agreement.** `pre_core_agree` equates all source operands read by a
   kept operation and the values observed at endings. If operands agree, `pre_eval` agrees.
   `pre_recomputed v e = Some u` means the original edge computes precisely that expression,
   its result is the source definition, and `u` is in `gen e`.
   On an actual source step from a reachable state, a generated expression retains its
   pre-step value, as does an expression whose kill flag on the taken edge is false.
3. **Kept primitive.** If an edge is not deleted, related boundary states with the required
   input operands can take matching original and target edge primitives in both directions,
   producing the same event list and core-agreeing results. The primitive updates exactly the
   values and cache entries named by that edge's kill/gen information.
4. **Insert primitive.** For a `pre_total_pure` expression at a planned edge, computing and
   storing its value is a finite sequence of silent target administrative steps, preserves
   source-visible state, creates no trap or stop, and terminates with the inserted version
   holding `pre_eval s u` for the matching post-edge source state. It does not change other valid
   cache entries. Source and target resource observations are unchanged by these steps.
5. **Replacement primitive.** For a planned deletion, if the cache value equals evaluation at
   the source state, replacing that one operation with the cached SSA value has the same event,
   result and successor core agreement in both directions. It preserves all other valid cache
   entries. This law is local to one edge; it does not assume the whole programs equivalent.
6. **Join/rename primitive.** On each incoming edge, phi selection and any required target
   renaming select exactly the cache value carried on that edge, preserve core agreement and
   do not change events, traps, stops or unrelated valid caches. No independent general SSA
   repair interface or correctness theorem is introduced.
7. **Finite administrative progress.** Every target-only step on a projected edge is silent
   and strictly decreases `pre_measure` until the next boundary; no administrative state is a
   final, trapped, stopped or stuck state. An original edge cannot be projected more than once
   before the next boundary. These conditions exclude introduced silent divergence.
8. **Endings and initialization.** Related boundary states agree on final, trap and stop
   observations and on stuckness; corresponding initial states have the same entry and satisfy
   `pre_cache_agree`. Source and target state invariants are preserved by their own steps.

The fields below are client obligations about individual graph edges and primitive actions.
They do not assume source and target behavior equality. `pre_local_gen_value` and
`pre_local_kill_frame` are the source value clauses of ANA-1's `genkill_laws`, restricted to
reachable states and actual taken steps. They supply the source stability needed when a cache
value is computed or carried past an edge. The record does not require the full `genkill_laws`,
whose `final_exit` field would add a separate restriction. Every concrete client proves both
source value fields for its own semantics.

```coq
Record pre_local_laws {S O B BE N E NT ET V K U C} (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (v : pre_expression_view S O N E U C) (initial_available : U -> bool)
    (r : pre_realizer S O N E NT ET U C) (p : pre_plan E U) : Prop := {
  pre_local_graph :
    v = pre_expression a /\ pre_source_graph r = gkview (pre_genkill v) /\
    graph_view_laws (pre_source r) (pre_source_graph r) /\
    graph_view_laws (pre_target r p) (pre_target_graph r p) /\
    (forall s l s', ~ stays (pre_source_graph r) s l s') /\
    (forall t l t', ~ stays (pre_target_graph r p) t l t') /\
    (forall t l t', reachable_state (pre_target r p) t -> step (pre_target r p) t l t' ->
      exists te, taken (pre_target_graph r p) t l t' te /\
      match pre_origin_of r p (point (pre_target_graph r p) t) with
      | PrePoint n => exists e, pre_project_edge r p te = Some e /\
          In e (Graph.out (cfg (pre_source_graph r)) n) /\
          (pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t' \/
           pre_admin r p e t')
      | PreOnEdge e _ => pre_project_edge r p te = None /\
          (pre_admin r p e t' \/ pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t')
      end);
  pre_local_operands :
    (forall s u, pre_eval r s u = uval (pre_genkill v) s u) /\
    (forall s t u, pre_core_agree r s t -> pre_eval r s u = pre_eval r t u) /\
    (forall s u, reachable_state (pre_source r) s -> pre_total_pure v u = true ->
      exists c, pre_eval r s u = Some c) /\
    (forall e u, pre_recomputed v e = Some u -> In u (gen (pre_genkill v) e));
  pre_local_gen_value : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e -> In u (gen (pre_genkill v) e) ->
    uval (pre_genkill v) s' u = uval (pre_genkill v) s u;
  pre_local_kill_frame : forall s l s' e u,
    reachable_state (pre_source r) s -> step (pre_source r) s l s' ->
    taken (pre_source_graph r) s l s' e -> kill (pre_genkill v) e u = false ->
    uval (pre_genkill v) s' u = uval (pre_genkill v) s u;
  pre_local_kept : forall s t e,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t -> pre_core_agree r s t ->
    (forall u, pre_deleted EE EU p e u = false) ->
    (forall l s', step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      exists t', pre_macro_step r p e t l t' /\ pre_core_agree r s' t') /\
    (forall l t', pre_macro_step r p e t l t' ->
      exists s', step (pre_source r) s l s' /\ taken (pre_source_graph r) s l s' e /\
        pre_core_agree r s' t');
  pre_local_insert : forall s t e u l s' t',
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    pre_core_agree r s t -> pre_inserted EE EU p e u = true ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_cached r t' (PreInserted e u) = pre_eval r s' u;
  pre_local_replace : forall s t e u version,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t -> pre_core_agree r s t ->
    pre_deleted EE EU p e u = true -> Map.get EE e (pre_reload_versions p) = Some version ->
    pre_cached r t version = pre_eval r s u ->
    (forall l s', step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
      exists t', pre_macro_step r p e t l t' /\ pre_core_agree r s' t') /\
    (forall l t', pre_macro_step r p e t l t' ->
      exists s', step (pre_source r) s l s' /\ taken (pre_source_graph r) s l s' e /\
        pre_core_agree r s' t');
  pre_local_cache_frame : forall s t e l s' t' version,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = Graph.source (cfg (pre_source_graph r)) e ->
    pre_boundary r p (point (pre_source_graph r) s) t ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_version_written EE e version = false ->
    pre_cached r t' version = pre_cached r t version;
  pre_local_compute : forall s t e u l s' t',
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    pre_recomputed v e = Some u -> pre_deleted EE EU p e u = false ->
    step (pre_source r) s l s' -> taken (pre_source_graph r) s l s' e ->
    pre_macro_step r p e t l t' -> pre_cached r t' (PreComputed e u) = pre_eval r s u;
  pre_local_initial : forall s t u,
    initial (pre_source r) s -> initial (pre_target r p) t -> pre_core_agree r s t ->
    initial_available u = true -> pre_cached r t (PreInitial u) = pre_eval r s u;
  pre_local_phi_select : forall s0 t0 s1 t1 s2 t2 be incoming l0 l version,
    reachable_state (pre_source r) s0 -> reachable_state (pre_target r p) t0 ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    step (pre_source r) s0 l0 s1 -> taken (pre_source_graph r) s0 l0 s1 incoming ->
    pre_macro_step r p incoming t0 l0 t1 ->
    step (pre_source r) s1 l s2 ->
    taken (pre_source_graph r) s1 l s2
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_macro_step r p
      (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be)) t1 l t2 ->
    pre_cached r t2 version =
      pre_phi_update EE EU p incoming
        (parameter_edge (pre_ssa_points a) (Graph.target (block_graph (pre_ssa_points a)) be))
        (pre_cached r t1) version;
  pre_local_progress : forall t e, reachable_state (pre_target r p) t -> pre_admin r p e t ->
    ~ final (pre_target_end r p) t /\ ~ trapped (pre_target_end r p) t /\
    ~ stopped (pre_target_end r p) t /\ ~ stuck (pre_target r p) (pre_target_end r p) t /\
    running (pre_target r p) t /\
    forall l t', step (pre_target r p) t l t' -> l = [] /\
      (pre_boundary r p (Graph.target (cfg (pre_source_graph r)) e) t' \/
       (pre_admin r p e t' /\ pre_measure r p t' < pre_measure r p t));
  pre_local_endings : forall s t n k,
    reachable_state (pre_source r) s -> reachable_state (pre_target r p) t ->
    point (pre_source_graph r) s = n -> pre_boundary r p n t -> pre_core_agree r s t ->
    (ends_as (pre_source r) (pre_source_end r) k s <->
      ends_as (pre_target r p) (pre_target_end r p) k t)
}.
```

```coq
Theorem ssa_pre_cache_invariant {S O B BE N E NT ET V K U C}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (s0 t0 : S) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  pre_exit_covered a r -> pre_phi_source_laws EBE EV a r ->
  pre_local_laws EBE EN EE EV EU a (pre_expression a) (pre_initial_available a) r p ->
  forall s t, pre_paired_run r p s0 t0 s t ->
    pre_cache_agree EN EE EU (pre_expression a) r p (point (pre_source_graph r) s) s t.

Theorem ssa_pre_semantics {S O B BE N E NT ET V K U C} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (r : pre_realizer S O N E NT ET U C) (s0 t0 : S) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let v := pre_expression a in
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  pre_exit_covered a r -> pre_phi_source_laws EBE EV a r ->
  pre_local_laws EBE EN EE EV EU a v (pre_initial_available a) r p ->
  initial (pre_source r) s0 -> initial (pre_target r p) t0 ->
  pre_boundary r p (point (pre_source_graph r) s0) t0 ->
  pre_cache_agree EN EE EU v r p
    (point (pre_source_graph r) s0) s0 t0 ->
  same_behaviour (pre_source r) (pre_source_end r) s0
    (pre_target r p) (pre_target_end r p) t0.
```

The proof must establish placement legality, extend the finite availability invariant along
each projected edge using the source value fields, derive the local kept/insert/replace/phi
cases and construct the macro target view on the original graph. Apply `agreement_simulation2`
to the source and macro view; compose with `stuttering_same_behaviour` for the bounded
administrative refinement to the real target. Supply both explicit stuck matches:
`pre_local_endings` covers related boundary states, and `pre_local_progress` provides a step at
each administrative state and a decreasing measure
to construct a finite silent path to a boundary. Progress alone does not establish that the
boundary is related to the required source state. Prove the matching relation and endpoint
conditions for the same path, accounting for every nondeterministic administrative choice; if
the existing local laws do not suffice, report the precise gap for an owner ruling.
Equal events, endings including traps and resource stops, finite prefixes and divergence
are required. A client may only discharge totality and resource neutrality with actual laws for
its semantics; the placement proof itself cannot establish them. The local laws are proof
obligations for a concrete client, not an implementation result.

A source edge that changes an expression despite a false kill flag can leave a cached value
stale. The source value fields exclude this mutation and preserve generated values across the
actual step. They do not establish the full theorems or discharge the independent same-path
administrative coupling obligation above.
