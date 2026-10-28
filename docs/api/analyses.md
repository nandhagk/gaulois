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
| `AnalysesStructured.v` | structured liveness, loop certificates, observers | ANA-2 |
| `AnalysesCensus.v` | region table | ANA-2 |
| `AnalysesValues.v` | SCCP, known bits, wrapping intervals, reduced products | ANA-3 |
| `AnalysesPaths.v` | edge predicates, path facts, guard chains | ANA-3 |
| `AnalysesDemand.v` | demand framework, dead values, demanded bits, observable bits, dead-code erasure | ANA-4 |
| `AnalysesAdce.v` | aggressive dead code with control dependence | ANA-4 |
| `AnalysesNumbering.v` | dominator-scoped numbering, optimistic GVN, loop invariance | ANA-5 |
| `AnalysesEgraph.v` | e-graphs, checked explanations, extraction | ANA-6 |
| `AnalysesScev.v` | chains of recurrences, recognition, trip counts, idioms | ANA-7 |
| `AnalysesCalls.v` | resolvers, recursion, summaries, stack demand, call strings | ANA-8 |
| `AnalysesPointsTo.v` | Andersen, Steensgaard, escape, allocation and zero facts | ANA-9 |
| `AnalysesMemory.v` | validated accesses, dead stores, MemorySSA, immutability, invariant loads | ANA-10 |
| `AnalysesRules.v` | liveness, neededness, reaching definitions as Rules programs | ANA-11 |

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
   Acceptance evidence: `while_lcm_accepts`, a required Example in ExamplesWhileAnalyses.v. *)
```

### ANA-2: structured code

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
(* The variables of one action, and of the statement whose trap or guard decides an exit. *)
Definition act_vars {A G X} (sv : skel_vars A G X) (act : action A G) : list X :=
  match act with
  | AAtom a => atom_uses sv a ++ atom_defs sv a
  | AGuard g _ => guard_uses sv g
  | AIndexIs g _ => guard_uses sv g
  | AIndexAtLeast g _ => guard_uses sv g
  | AJump _ _ => nil
  end.
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
```

### ANA-3: value analyses (sparse conditional generator of VIEW-4)

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
Definition solve_values {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (HL : lattice_laws (lift_bot_lattice (fact_lat (domain pr))))
    (sch : scheduler (sparse_unknown N E V)) (st : strategy)
    (HT : terminates (lift_bot_lattice (fact_lat (domain pr))) (sparse_static pr) sch st) :
  {s : sparse_unknown N E V -> lift_bot A |
     post_solution (lift_bot_lattice (fact_lat (domain pr))) (sparse_system pr) s} :=
  solve_total (sparse_unknown_encoding EN EE EV) (sparse_constraint_encoding EN EE EV)
    (lift_bot_lattice (fact_lat (domain pr))) HL sch st (sparse_system pr) (sparse_static pr) HT.
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
(* Dead values: with M = bool, a value is dead when no closed demand needs it. *)
Definition bool_demand {Cv} : demand_domain bool Cv :=
  DemandDomain bool_lattice bool_agree.   (* agree b u v := b = true -> u = v *)
Definition needed_values {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool) :
  finite_map EX (dvars dv) bool.
(* the value at tt of solve_total on closed_system: the least closed demand, seeded by dnec and
   dexit and closed under dback; a worklist *)
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
  (* the endings other than stuck agree at the demand *)
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
(* the least set M with: effectful_node n -> n in M; n in M and cdep (agraph ai) (aexits ai) b n ->
   b in M; may_not_terminate n -> n in M; computed by a worklist over the reverse control
   dependences *)
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
   `gvn_merges` in ExamplesSsaAnalyses.v, where the producer merges two computations *)
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
(* AnalysesEgraph.v. Saturation and extraction are untrusted; a checked explanation closes the
   loop. Rules are equalities over typed environments: both sides are defined and equal, partial
   operators included. A rule may carry a decidable side condition on its instance (for example a
   sort test), because `x * 0 -> 0` holds only for integer-sorted `x`. *)
Inductive term (K : Type) : Type := TVar (i : nat) | TApp (o : K) (args : list (term K)).
Definition denote {K C} (ev : K -> list C -> option C) (env : nat -> option C) (t : term K) :
  option C.   (* TVar i = env i; TApp o args = ev o over the denotations of args, None if any is None *)
(* `ok` says which environments are typed: every variable is bound, to a value of its sort. *)
Definition equiv_term {K C} (ev : K -> list C -> option C) (ok : (nat -> option C) -> Prop)
    (t u : term K) : Prop :=
  forall env, ok env -> denote ev env t = denote ev env u.
Definition subst_term {K} (sub : nat -> term K) (t : term K) : term K.
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
(* each step checks that the subterm at step_pos is an instance of the rule's source side under
   step_subst (compared with EK), that rule_side holds of the substitution, and replaces the
   subterm by the target side *)
Definition check_explanation {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t u : term K)
    (steps : list (rewrite_step K)) : bool :=
  match replay EK rules t steps with Some v => term_eqb EK v u | None => false end.
Definition term_eqb {K} (EK : encoding K) (t u : term K) : bool.
(* structural equality, comparing operators by their codes under EK *)
Definition term_cost {K} (cost : K -> nat) (t : term K) : nat.   (* the sum of cost over the nodes *)
Definition egraph (K : Type) : Type.     (* hash-consed nodes, a UnionFind of classes; abstract *)
Definition saturate {K} (EK : encoding K) (rules : list (rewrite_rule K)) (fuel : positive)
  (t : term K) : egraph K.                                   (* untrusted *)
Definition extract {K} (cost : K -> nat) (eg : egraph K) (t : term K) :
  option (term K * list (rewrite_step K)).                   (* untrusted: best term and a path *)
Definition optimise {K} (EK : encoding K) (rules : list (rewrite_rule K)) (cost : K -> nat)
    (fuel : positive) (t : term K) : option (term K) :=
  match extract cost (saturate EK rules fuel t) t with
  | Some (u, steps) =>
    if check_explanation EK rules t u steps && Nat.leb (term_cost cost u) (term_cost cost t)
    then Some u else None
  | None => None
  end.
(* Acceptance evidence: `egraph_optimise_accepts`, a required Example in ExamplesSsaAnalyses.v on
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
   `scev_count_up_trip`, a required Example in ExamplesSsaAnalyses.v *)
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

### ANA-10: memory

```coq
(* AnalysesMemory.v. Byte-range facts use Domains' `range_must ET`, whose reached facts carry
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
  bsite : S -> L -> option T;                (* the site of an existing allocation *)
  byte : S -> L -> Z -> option nat
}.
Record bytes_laws {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L) : Prop := {
  by_view : graph_view_laws m (bgv bv);
  by_no_stays : forall s l s', ~ stays (bgv bv) s l s';
  byte_frame : forall s l s' l0 t o, reachable_state m s -> step m s l s' ->
    bsite bv s l0 = Some t -> byte bv s' l0 o <> byte bv s l0 o ->
    covered (writes_at bv (point (bgv bv) s)) t o 1
}.
(* MemorySSA: an untrusted construction and a verified no-clobber checker. A memory node carries its
   function. *)
Inductive mem_node (F N : Type) : Type := MDef (f : F) (n : N) | MLive (f : F).
Record memory_ssa (F N : Type) : Type := MemorySSA {
  def_of_load : N -> option (mem_node F N)    (* the memory definition a load reads *)
}.
Definition build_memory_ssa {F N E T} (f : F) (g : Graph.t N E) (fp : N -> list (footprint T)) :
  memory_ssa F N.
(* untrusted: any algorithm; it has no theorem *)
Definition no_clobber_check {F N E T} (EN : encoding N) (EF : encoding F) (f : F)
    (g : Graph.t N E) (writes reads : N -> list (footprint T)) (ms : memory_ssa F N) : bool.
(* for every node n of g with def_of_load ms n = Some d, d carrying the function f: for MDef f d0,
   no node reached from the target of an out-edge of d0, along any walk that ends at n (n included
   as the end), writes a range that overlaps reads n; for MLive f, the same for every walk from an
   entry of g. Both checks are one reverse search from n that stops at d0. Acceptance evidence:
   `memoryssa_accepts`, a required Example in ExamplesSsaAnalyses.v. *)
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
Theorem numeric_value_sound {S O N E V K C A} (m : semantics S O) (ND : numeric_domain A)
    (G : concretisation A word) (br : op_bridge K C) (top : A) (sv : ssa_view S O N E V K C)
    (vals : list V) (entry : V -> A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m sv -> numeric_laws ND G -> op_bridge_laws br (op_eval sv) (truth sv) ->
  (forall w z, is_word w z -> gamma G top (w, z)) -> leb (lat ND) top (bot (lat ND)) = false ->
  (forall s x c, reachable_state m s -> val sv s x = Some c -> In x vals) ->
  (forall s x c, initial m s -> val sv s x = Some c ->
     exists b i, def sv x = Param b i /\ In b (Graph.entries (cfg (base sv))) /\
       gamma (fact_conc (sparse_of_numeric ND G br top)) (entry x) c) ->
  post_solution (lift_bot_lattice (lat ND))
    (sparse_system (numeric_problem ND G br top sv vals entry)) sigma ->
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
demand by induction on the worklist (it is the least fixed point of the transfer seeds); the last
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
`demand_closed`), the transfer `demand_transfer`, `inv1 := er_inv pol m en` restricted to the states
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
`er_nop_back`, whose matching step of `P` is silent likewise. The two programs share the graph
(`er_cfg`), so both steps reach one point (`taken_edge`). This is the statement that justifies
deleting `z <- z + 1` in Pfenning's example. Card: ANA-4.

```coq
(** ADCE marking: effects are kept, control dependences are kept, divergence is kept, and the
    marked set is the least such set. *)
Theorem adce_closed {N E} (EN : encoding N) (ai : adce_input N E) :
  (forall n, effectful_node ai n = true -> FinSet.mem EN n (adce_marked EN ai) = true) /\
  (forall b n, FinSet.mem EN n (adce_marked EN ai) = true -> cdep (agraph ai) (aexits ai) b n ->
     FinSet.mem EN b (adce_marked EN ai) = true) /\
  (forall n, may_not_terminate ai n = true -> FinSet.mem EN n (adce_marked EN ai) = true).
Theorem adce_least {N E} (EN : encoding N) (ai : adce_input N E) (M : FinSet.t N) :
  (forall n, effectful_node ai n = true -> FinSet.mem EN n M = true) ->
  (forall b n, FinSet.mem EN n M = true -> cdep (agraph ai) (aexits ai) b n ->
     FinSet.mem EN b M = true) ->
  (forall n, may_not_terminate ai n = true -> FinSet.mem EN n M = true) ->
  forall n, FinSet.mem EN n (adce_marked EN ai) = true -> FinSet.mem EN n M = true.
(** An unmarked node has a unique next marked node, so removing it cannot change which marked
    node runs next. *)
Theorem adce_skip_unique {N E} (EN : encoding N) (ai : adce_input N E) (n m1 m2 : N) :
  graph_wf (agraph ai) -> exits_reachable (agraph ai) (aexits ai) ->
  (forall x, In x (aexits ai) -> FinSet.mem EN x (adce_marked EN ai) = true) ->
  FinSet.mem EN n (adce_marked EN ai) = false ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m1 ->
  skips_to (agraph ai) (fun x => FinSet.mem EN x (adce_marked EN ai)) n m2 -> m1 = m2.
```
Proof idea: closure and leastness by the worklist invariant (the worklist computes the least set
closed under the three rules); if two out-paths of unmarked nodes first reach distinct marked nodes,
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
(** The whole pipeline: saturation and extraction are arbitrary, the result is equivalent and no
    more expensive. *)
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

### ANA-10

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
    (EN : encoding N) (EF : encoding F) (f : F) (ms : memory_ssa F N)
    (reads : N -> list (footprint T)) :
  bytes_laws m bv ->
  no_clobber_check EN EF f (cfg (bgv bv)) (writes_at bv) reads ms = true ->
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
reverse search over `path`, and the unchanged claim is an induction on the run using `byte_frame`
(a changed byte of an existing allocation is covered by the writes of the node; allocations and
frees are among those writes); immutability and invariant loads by induction with `byte_frame`,
`footprints_disjoint_sound` and `invariant_in`. In `invariant_load_sound` the bytes half is the
disjointness of `loop_writes` from the load, and the address half is `loop_invariant_sound` for
`base`, so each execution of the load inside one execution of the loop reads the same bytes at the
same address. Acceptance evidence for the MemorySSA checker: `memoryssa_accepts`. Card: ANA-10.

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

## Open questions

Assumptions about other packages and unfinished choices:
1. **Order.** Names are those of `order.md`: `finite_powerset_lattice`, `finite_must_lattice`,
   `finite_pointwise_lattice` with their heights, `finite_set` and `finite_map`, `bool_lattice`,
   `disjunction_lattice k L`, `lift_bot` with `Unreached` and `Reached`. Two additions are asked:
   `finite_clamp` and `finite_map_clamp`.
2. **Collections.** `FinSet.mem EX x a` takes the encoding; `FinSet.union`, `FinSet.diff`,
   `FinSet.of_list`, `FinSet.elements` likewise; `Map.t X M` with `Map.get EX x d`; `pair_encoding`;
   `position_encoding : encoding position`.
3. **Domains.** `numeric_domain A` with `lat`, `top_at`, `of_const`, `forward`, `assume`, `meet`;
   `numeric_laws D G` over `word`; `abs_eval` and `abs_assume`; `partition E` with
   `partition_equiv`, `partition_union`, `partition_top`, `partition_lattice` and a
   `partition_forget` (asked, DOM-7); masks with `mask_lattice w`, `mask_agreement w` and `demand`
   (DOM-5); `footprint` and `covered`, which VIEW-7 also uses; `footprint_encoding` and
   `range_must_lattice` with its operations (asked, DOM-6).
4. **Graph.** `path`, `dominates`, `strictly_dominates`, `edge_dominates`, `cdep g exits b n` with
   `exits_reachable`, `max_paths`, `condensation`. The dominator tree and the WTO that the
   schedulers use are total with sound fallbacks, so no theorem here needs a producer to succeed.
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
