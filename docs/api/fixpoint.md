# Gaulois.Fixpoint

## Nested WTO iteration (FIX-5)

`FixpointNested.v` supplies a selectable directly proved nested iterator for static systems. It
does not change `wto_scheduler`, which remains the static-priority queue scheduler of FIX-3.
The two strategies can produce different widened post-solutions. Construct the dependency graph
and `wto_total` once, using `unknowns`, `dependency_graph` and the graph preparation of FIX-3.
Each target has a prebuilt list of its constraints in `System.constraints` order; do not scan the
constraint list while iterating. The WTO token list is parsed once to a well-nested component
tree with its heads, vertex-to-containing-components index, and ordered target constraint lists.

An ordered pass visits each `WVertex` once. On `WOpen h`, it visits h, then each nested body item
in order, repeating the whole component until no unknown in that component changed during the
pass. Changes by side contributions count, even when their producing constraint targets another
component; mark every containing component dirty. A complete outer pass traverses all top-level
items and repeats until no unknown anywhere changes in that pass. Thus a side contribution to a
previously visited component is not lost. On visiting x, run each constraint with target x once,
in the prebuilt order, using `Query.run` once. Process its returned target value followed by all
side contributions in `Query.run` order. An update is skipped when its contribution is already
below the current value; otherwise use `widen` at a WTO head under `Widening`, and `join` at all
other points or under `Joining`. Track changes through the same `leb` test used by
`engine_step`. Constraints with no reads still run on every required visit. All target and side
outputs are included in the graph and the component membership index.

Each invocation uses binary fuel. One fuel unit performs one constraint evaluation, or one frame
transition if no constraint is ready; it returns `None` if fuel expires before a no-change outer
pass. The implementation uses explicit frames and a binary-recursive loop, not the Gallina call
stack proportional to iteration count. Empty systems finish successfully. An initial assignment
is everywhere bottom. A `None` result never certifies a solution. Definitions and theorems:

```coq
Definition nested_run {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (st : strategy) (S : System.t X C A) (SS : System.static S) (fuel : positive) :
  option (assignment X A).
Definition nested_solve_fuel {X C A} (EX : encoding X) (EC : encoding C)
  (L : lattice A) (HL : lattice_laws L) (T : top L) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (fuel : positive) :
  {s : X -> A | post_solution L S s}.
(* Return the assignment from nested_run when it finishes, otherwise the everywhere-top function. *)
Theorem nested_run_sound {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (fuel : positive) (m : assignment X A) :
  nested_run EX EC L st S SS fuel = Some m -> post_solution L S (lookup EX L m).
Theorem nested_run_eventually {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S) :
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, nested_run EX EC L st S SS fuel = Some m.
```

Proof obligations include component nesting, dirty propagation for every side target, termination
of each pass, and a well-founded measure for the nested strategy. Prove that parsed heads are
exactly the widening points of `wto_scheduler`, and that a complete outer pass evaluates every
constraint, including those with side targets in earlier components. `nested_run_sound` follows
from the final no-change pass, independently of leastness. `nested_run_eventually` needs finite
height or the existing widening-rank and cycle-cut hypotheses; no leastness or schedule-independent
equality is claimed. The independent full checker remains available for external candidates.
Card: FIX-5.

## Observation-oriented SCC iteration (FIX-6)

`FixpointObserve.v` supplies a memory-conscious mode for static systems with no declared side
targets. It returns selected observations; the full FIX-5 engine remains available for every
static system including side effects. The fixed schedule first computes the SCCs of the declared
read-to-target dependency graph in topological order. Within each SCC it uses the nested WTO
iteration of FIX-5 on that component, initialized to bottom for its members and reading already
stabilized predecessor values as immutable inputs. Build the induced component graph, its WTO,
and the ordered target-constraint lists once. The induced WTO is computed deterministically from
the component and is not an additional field supplied by the caller. No value is evicted during
component stabilization.
A component is complete only when its nested iterator finishes; a singleton without a self-edge
is handled by the same rule. Side-free declarations guarantee that its constraints cannot update
another component. Unknowns with no target constraint retain bottom.

The plan stores the nonempty components in topological order, with each component represented by
its first member, and indexes eviction lists by that representative. Prepare the index from the
last component that declares a read of each value, counting the producer component itself. After
a component stabilizes, record every selected observation in it, then remove each value whose
last reader component is the just-completed component. Earlier external inputs remain available
through every read in the current component. No scan of all unknowns or constraints occurs in
the iteration. Observation keys must be among `unknowns`; duplicate keys are allowed. The result
map contains exactly the distinct observation keys, including bottom-valued observations.

The checker validates component coverage, membership, topological flow, the component WTOs,
side-free declarations, observation coverage, and every lifetime against the declared read
dependencies and the prepared system index. It rejects invalid plans and any declared side target.
A component's schedule, constraint order and widening choices are the same in the two executions
below. Both start with bottom values and a binary fuel budget. A fuel unit pays one nested frame
transition or one constraint evaluation; bookkeeping and component-boundary eviction do not
consume extra fuel. Both return `None` when the plan is invalid or fuel expires before all
components stabilize. On completion both return the observation map. The full-memory reference
keeps all stabilized values, while the memory-conscious execution performs the stated evictions.

```coq
Record observation_plan (X : Type) : Type := ObservationPlan {
  observation_components : list (list X);
  observation_expire : Map.t X (list X)
}.
Definition observation_prepare {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) : option (observation_plan X).
Definition observation_plan_check {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) : bool.
Definition observation_project {X A} (EX : encoding X) (L : lattice A) (roots : list X)
  (m : assignment X A) : assignment X A.
(* Fold Map.set over roots with the corresponding lookup EX L m value, starting from Map.empty. *)
Definition observation_full_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
(* The fixed-schedule execution without eviction, returning its complete assignment on success. *)
Definition observation_reference {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
Definition observation_run {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) : option (assignment X A).
Theorem observation_prepare_checked {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_prepare EX S SS ix roots = Some p ->
  observation_plan_check EX S SS ix roots p = true.
Theorem observation_run_refines {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) :
  sys_index_laws EX S SS ix ->
  observation_run EX L st S SS ix roots p fuel =
    observation_reference EX L st S SS ix roots p fuel.
Theorem observation_reference_projection {X C A} (EX : encoding X) (L : lattice A) (st : strategy)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (p : observation_plan X) (fuel : positive) :
  observation_reference EX L st S SS ix roots p fuel =
  option_map (observation_project EX L roots)
    (observation_full_reference EX L st S SS ix roots p fuel).
Theorem observation_full_reference_sound {X C A} (EX : encoding X) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (roots : list X) (p : observation_plan X) (fuel : positive)
  (m : assignment X A) :
  sys_index_laws EX S SS ix ->
  observation_full_reference EX L st S SS ix roots p fuel = Some m ->
  post_solution L S (lookup EX L m).
Theorem observation_plan_complete {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  sys_index_laws EX S SS ix ->
  (forall c, In c (System.constraints S) -> side_targets SS c = []) ->
  (forall x, In x roots -> In x (unknowns EX S SS)) ->
  exists p, observation_prepare EX S SS ix roots = Some p.
Theorem observation_run_eventually {X C A} (EX : encoding X) (L : lattice A)
  (HL : lattice_laws L) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (roots : list X) (p : observation_plan X) :
  sys_index_laws EX S SS ix -> observation_plan_check EX S SS ix roots p = true ->
  terminates L SS (wto_scheduler EX S SS) st ->
  exists fuel m, observation_run EX L st S SS ix roots p fuel = Some m.
```

Prove the reference and optimized executions have identical component-local traces and widening
histories. At each boundary they agree on all values read by a later component and on observations
already recorded. `sides_within` proves that empty declared side lists exclude actual contributions.
Prove that each derived local WTO's heads cut all cycles in its induced component, independently
of the global scheduler's head set, and use this in the eventual-completion argument. The full
reference's post-solution theorem establishes semantic utility; its projection and the refinement
theorem connect that guarantee to the returned observations.
The peak live assignment contains current-component values and earlier values with a later
declared reader; the observation map is additional retained output. No eviction within an SCC,
global memory-optimality claim, equality with a different schedule, or full-assignment result is
promised. Card: FIX-6.
Fixpoint gives every analysis one meaning: a constraint system. Each constraint has a target
unknown and a right-hand side that is a small query tree: return a value, ask another unknown, or
contribute to one. A result is a *post-solution* when every value returned and every value
contributed lies below the result. The package has one full checker, a checker that stores values
only at cut points and recomputes the rest in one pass, one worklist engine whose scheduler is a
parameter (a fuel-bounded run with a top fallback, and a total run whose termination is proved from
evidence), narrowing that is kept only when the checker accepts it, and a demand-driven local
solver whose output is validated by a checker. For example, over sets, the constraints
`a ⊒ {1}`, `b ⊒ a` and `a ⊒ b` have the least solution `a = b = {1}`; the engine returns it and
`check_post` accepts it, while `a = {1}, b = {}` is rejected.

Conventions of this document. Names are those of the anchors, as the rulings amend them.
- Query trees live in `Module Query`: `Query.t`, `Query.Ret`, `Query.Ask`, `Query.Side`,
  `Query.eval`, `Query.reads`, `Query.sides` and `Query.run`. Constraint systems live in
  `Module System`: `System.t X C A` with `System.constraints`, `System.target` and `System.rhs`, and
  `System.static S` with `System.deps`, `System.side_targets`, `System.reads_within` and
  `System.sides_within`. `Notation deps := System.deps` and `Notation side_targets :=
  System.side_targets` make the two summaries bare, as Views writes them. Graphs are `Graph.t V E`
  with `Graph.entries`, `Graph.nodes`, `Graph.out`, `Graph.source` and `Graph.target`, so no
  projection is ever shared between `System` and `Graph`.
- Sets are `FinSet.t K` and maps `Map.t K V` (Collections), written with the encoding first. A
  function that iterates `FinSet.elements` is specified only on well-formed sets, so a theorem
  about it carries `FinSet.wf`; an untrusted producer's set is normalised with
  `FinSet.of_list EX (FinSet.elements s)` before it is trusted.
- `post_solution`, `assignment`, `lookup`, `ask_all` and `side_all` are bare. `fun_leb` and
  `monotone_on_assignments` come from Order.
- Statements sit in `Section`s whose `Context` and `Variables` declare what they mention; a theorem
  is generalised over exactly the ones it uses, in declaration order.
  `Relations.Relation_Operators`, `List` and `Bool` are implicit. Every `Inductive` and `Record`
  takes its parameters implicitly in
  constructors and projections (`Arguments` declarations are omitted).
- Both solvers return a function, `{s : X -> A | post_solution L S s}`; the total solver's function
  is `lookup EX L m` of its internal map.

## Files

| File | Contents | Card |
|---|---|---|
| `FixpointQuery.v` | `Query` (`t`, `eval`, `reads`, `sides`, `run`), `ask_all`, `side_all`; determinism, `run_spec` | FIX-1 |
| `FixpointSystem.v` | `System` (`t`, `static`), `post_solution`, `assignment`, `lookup`, `monotone_query`, `monotone_system` | FIX-1 |
| `FixpointIndex.v` | `sys_index`, `index_system`: prepared contributor and reader indexes | FIX-1 |
| `FixpointCheck.v` | `check_post`, the full checker | FIX-1 |
| `FixpointCut.v` | `cut_certificate`, `plan_valid`, `expand`, `replay` | FIX-1 |
| `FixpointLeast.v` | `raise`, `reached`, `least_solution` | FIX-1 |
| `FixpointCycles.v` | `flows`, `cuts_every_cycle` | FIX-1 |
| `FixpointWorklist.v` | `scheduler`, `strategy`, `dependencies`, `Engine`, `engine_step`, the binary fuel loop, `run_worklist`, `solve_fuel`; soundness and adequacy from accessibility | FIX-2a |
| `FixpointTotal.v` | `terminates`, `engine_acc` (accessibility from the evidence), `solve_total`, `solve_total_run`, `solve_total_reached`, `solve_total_least` | FIX-2b |
| `FixpointSchedule.v` | `unknowns`, `dependency_graph`, RPO, WTO and SCC schedulers, `plan_of` | FIX-3 |
| `FixpointNarrow.v` | `narrow_pass`, `narrow_checked` | FIX-3 |
| `FixpointPartial.v` | `closed_partial`, `check_partial` | FIX-4 |
| `FixpointLocal.v` | `local_solve` (untrusted), `local_checked` | FIX-4 |
| `FixpointNested.v` | nested WTO fuel iterator and direct soundness and termination | FIX-5 |
| `FixpointObserve.v` | SCC observation iterator with validated value lifetimes | FIX-6 |
| `FixpointLocalDirect.v` | directly proved static local closure and solver | FIX-7 |

Prerequisites. FIX-2a needs FIX-1 and COL-2; FIX-2b needs FIX-2a and is the hard card (height,
widening rank, widening points that cut every cycle); FIX-3 needs FIX-2b and GRA-3a, GRA-4b, GRA-4c;
FIX-4 needs FIX-2a. A card that needs `solve_total` lists FIX-2b, one that needs only `solve_fuel`
lists FIX-2a.

## Definitions

### FIX-1: queries, systems, checkers

```coq
(* FixpointQuery.v *)
Module Query.
Inductive t (X A : Type) : Type :=
  | Ret (a : A)
  | Ask (x : X) (k : A -> t X A)
  | Side (x : X) (a : A) (q : t X A).
Fixpoint eval {X A} (q : t X A) (s : X -> A) : A :=
  match q with Ret a => a | Ask x k => eval (k (s x)) s | Side _ _ q' => eval q' s end.
Fixpoint reads {X A} (q : t X A) (s : X -> A) : list X :=
  match q with Ret _ => [] | Ask x k => x :: reads (k (s x)) s | Side _ _ q' => reads q' s end.
Fixpoint sides {X A} (q : t X A) (s : X -> A) : list (X * A) :=
  match q with Ret _ => [] | Ask x k => sides (k (s x)) s | Side x a q' => (x, a) :: sides q' s end.
(* one traversal for the value, the unknowns asked and the contributions made; every engine and
   checker calls run once per right-hand side, never eval, reads and sides separately *)
Fixpoint run {X A} (q : t X A) (s : X -> A) : A * list X * list (X * A) :=
  match q with
  | Ret a => (a, [], [])
  | Ask x k => let '(a, rs, ss) := run (k (s x)) s in (a, x :: rs, ss)
  | Side x a q' => let '(r, rs, ss) := run q' s in (r, rs, (x, a) :: ss)
  end.
End Query.
(* ask every unknown of xs in order, then continue with their values *)
Fixpoint ask_all {X A} (xs : list X) (k : list A -> Query.t X A) : Query.t X A :=
  match xs with
  | [] => k []
  | x :: xs' => Query.Ask x (fun a => ask_all xs' (fun vs => k (a :: vs)))
  end.
(* contribute every pair of l, then continue with q *)
Fixpoint side_all {X A} (l : list (X * A)) (q : Query.t X A) : Query.t X A :=
  match l with [] => q | (x, a) :: l' => Query.Side x a (side_all l' q) end.
```

The bodies of the query functions are part of the contract. Assignments and monotonicity
(`FixpointSystem.v`):

```coq
Module System.
Record t (X C A : Type) : Type := Make {
  constraints : list C;
  target : C -> X;
  rhs : C -> Query.t X A
}.
(* A static system declares over-approximations of what each constraint reads and contributes to *)
Record static {X C A} (S : t X C A) : Type := Static {
  deps : C -> list X;
  side_targets : C -> list X;
  reads_within : forall c s, incl (Query.reads (rhs S c) s) (deps c);
  sides_within : forall c s, incl (map fst (Query.sides (rhs S c) s)) (side_targets c)
}.
End System.
Notation deps := System.deps.
Notation side_targets := System.side_targets.
Definition post_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true /\
    forall x a, In (x, a) (Query.sides (System.rhs S c) s) -> leb L a (s x) = true.
(* assignments are finite maps with a default: lookup returns bot L for an absent unknown *)
Definition assignment (X A : Type) : Type := Map.t X A.
Definition lookup {X A} (EX : encoding X) (L : lattice A) (m : assignment X A) (x : X) : A :=
  match Map.get EX x m with Some a => a | None => bot L end.
(* a larger assignment gives a larger value, and each contribution is matched by a larger one *)
Definition monotone_query {X A} (L : lattice A) (q : Query.t X A) : Prop :=
  monotone_on_assignments L L (Query.eval q) /\
  forall s1 s2, fun_leb L s1 s2 -> forall x a, In (x, a) (Query.sides q s1) ->
    exists b, In (x, b) (Query.sides q s2) /\ leb L a b = true.
Definition monotone_system {X C A} (L : lattice A) (S : System.t X C A) : Prop :=
  forall c, In c (System.constraints S) -> monotone_query L (System.rhs S c).
```

Prepared indexes (`FixpointIndex.v`), built once per static system and shared by the cut-point
checker, the engine, narrowing and the partial checker:

```coq
Record sys_index (X C : Type) : Type := SysIndex {
  contributors : Map.t X (list C);       (* x -> the constraints with target x, or x among side_targets *)
  readers : Map.t X (list C)             (* x -> the constraints with x among deps *)
}.
Definition index_system {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) :
  sys_index X C.
(* one fold over System.constraints S; a constraint c is added once for each DISTINCT unknown of
   System.target S c :: side_targets SS c (contributors) and of deps SS c (readers), the distinct
   unknowns being FinSet.elements (FinSet.of_list EX ...); no constraint list is scanned later *)
Definition contributors_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C.   (* or [] *)
Definition readers_of {X C} (EX : encoding X) (ix : sys_index X C) (x : X) : list C.         (* or [] *)
Record sys_index_laws {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) : Prop := {
  contributors_agree : forall x c, In c (contributors_of EX ix x) <->
    In c (System.constraints S) /\ (System.target S c = x \/ In x (side_targets SS c));
  readers_agree : forall x c, In c (readers_of EX ix x) <->
    In c (System.constraints S) /\ In x (deps SS c);
  index_nodup : NoDup (System.constraints S) ->
    forall x, NoDup (contributors_of EX ix x) /\ NoDup (readers_of EX ix x)
}.
```

The full checker (`FixpointCheck.v`) runs every constraint once and needs no dependencies, so it
judges dynamic systems too:

```coq
Definition check_post {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : bool :=
  forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) s in
    leb L v (s (System.target S c)) && forallb (fun xa => leb L (snd xa) (s (fst xa))) ss)
    (System.constraints S).
```

The cut-point checker (`FixpointCut.v`). The certificate stores values only at the cut points
(loop heads) and orders the other unknowns; `expand` recomputes them in one pass.

```coq
Record cut_certificate (X A : Type) : Type := CutCertificate {
  cuts : FinSet.t X;                     (* the cut points *)
  stored : assignment X A;               (* the values at the cut points; absent means bot *)
  plan : list X                          (* every other unknown that has a constraint, in order *)
}.
(* the static form of the conditions `expand` tests: no duplicates, no cut point in the plan, every
   target and side target covered, and the contributors of each planned x read only cut points,
   earlier planned unknowns, or unknowns with no contributor (whose value is bot) *)
Definition plan_valid {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) : Prop :=
  NoDup plan /\ (forall x, In x plan -> FinSet.mem EX x cuts = false) /\
  (forall c, In c (System.constraints S) ->
     forall x, (x = System.target S c \/ In x (side_targets SS c)) ->
       FinSet.mem EX x cuts = true \/ In x plan) /\
  forall l1 x l2, plan = l1 ++ x :: l2 -> forall c, In c (contributors_of EX ix x) ->
    forall y, In y (deps SS c) ->
      FinSet.mem EX y cuts = true \/ In y l1 \/ contributors_of EX ix y = [].
Definition expand {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) : option (assignment X A).
(* 1. reject unless plan_valid's first three conditions hold (checked with the index);
   2. for x in plan order, with cur the assignment built so far (stored cut values, planned values,
      bot elsewhere): for each contributor c of x take (v, rs, ss) := Query.run (rhs c) cur; reject if
      rs names an unknown with contributors that is neither a cut point nor already computed;
      otherwise the value of x is the join of bot, of v for each c with target c = x, and of every
      a for (x, a) in ss (keys compared by encode);
   3. for each p in FinSet.elements (cuts cert): every contributor c of p, run on the final
      assignment, has its value (if target c = p) and its contributions to p below the stored value
      of p;
   4. return the stored values at the cut points and the computed values at the planned unknowns. *)
(* replay: fold an observer over the plan (and the cut points) with each unknown's value, keeping no
   other state: replay obs b0 (FinSet.elements (cuts cert) ++ plan cert) (lookup EX L m) *)
Definition replay {X A B} (obs : B -> X -> A -> B) (b0 : B) (order : list X) (s : X -> A) : B :=
  fold_left (fun b x => obs b x (s x)) order b0.
```

The least solution without widening (`FixpointLeast.v`). One *run* of a constraint evaluates it once
at the current assignment and joins its value into its target and each contribution into its
unknown; an update that is already below the current value is skipped, exactly as the engine
skips it. `raise` relates assignments up to pointwise equality, so no functional extensionality
is needed.

```coq
Definition join_update {X A} (EX : encoding X) (L : lattice A) (x : X) (a : A) (s : X -> A) :
  X -> A :=
  fun y => if Pos.eqb (encode EX x) (encode EX y)
           then (if leb L a (s y) then s y else join L (s y) a) else s y.
(* the updates one run of c at s makes: its value for its target, then each contribution *)
Definition run_updates {X C A} (S : System.t X C A) (c : C) (s : X -> A) : list (X * A) :=
  let '(v, _, ss) := Query.run (System.rhs S c) s in (System.target S c, v) :: ss.
Definition apply_updates {X A} (EX : encoding X) (L : lattice A) (ups : list (X * A)) (s : X -> A) :
  X -> A := fold_left (fun s' xa => join_update EX L (fst xa) (snd xa) s') ups s.
Definition raise {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A) (s t : X -> A) : Prop :=
  exists c, In c (System.constraints S) /\
    forall y, t y = apply_updates EX L (run_updates S c s) s y.
(* assignments reachable from all-bottom (up to pointwise equality) by runs *)
Definition reached {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  exists s0, (forall x, s0 x = bot L) /\ clos_refl_trans (X -> A) (raise EX L S) s0 s.
Definition least_solution {X C A} (L : lattice A) (S : System.t X C A) (s : X -> A) : Prop :=
  post_solution L S s /\ forall t, post_solution L S t -> fun_leb L s t.
```

Cycles of a static system (`FixpointCycles.v`). A set `W` of unknowns *cuts* the system when the
flows that do not enter `W` have no cycle; cut points and widening points are such sets.

```coq
(* y flows into x when a constraint that reads y has x as its target or as a side target *)
Definition flows {X C A} {S : System.t X C A} (SS : System.static S) (y x : X) : Prop :=
  exists c, In c (System.constraints S) /\ In y (deps SS c) /\
    (x = System.target S c \/ In x (side_targets SS c)).
(* the cut property: deleting the edges into W leaves no cycle of flows *)
Definition cuts_every_cycle {X C A} {S : System.t X C A} (SS : System.static S) (W : X -> bool) : Prop :=
  forall x, ~ clos_trans X (fun y z => flows SS y z /\ W z = false) x x.
```

### FIX-2a: the worklist engine (`FixpointWorklist.v`)

```coq
Record scheduler (X : Type) : Type := Scheduler {
  priority : X -> positive;              (* a constraint runs with the priority of its target; smaller first *)
  widening_point : X -> bool             (* where an update widens instead of joining *)
}.
Inductive strategy : Type := Joining | Widening.     (* Joining: every update is a join *)
(* where the engine learns what each constraint reads *)
Inductive dependencies {X C A} (S : System.t X C A) : Type :=
  | Declared (SS : System.static S) (ix : sys_index X C)   (* from deps, through the prepared index *)
  | Recorded.                                               (* from reads, as each constraint runs *)
Definition dependencies_ok {X C A} (EX : encoding X) {S : System.t X C A} (dep : dependencies S) : Prop :=
  match dep with Declared SS ix => sys_index_laws EX S SS ix | Recorded => True end.

Module Engine.
Record t (X C A : Type) : Type := State {
  current : assignment X A;              (* the values; an absent unknown holds bot *)
  queue : PQueue.t C;                    (* the constraints still to run, each at the priority of its target *)
  recorded : Map.t X (FinSet.t C)        (* with Recorded: the constraints seen to read each unknown *)
}.
End Engine.
(* every constraint queued at the priority of its target, all values bot, nothing recorded *)
Definition initial_state {X C A} (EC : encoding C) (sch : scheduler X) (S : System.t X C A) :
  Engine.t X C A.
(* one step of the engine: None when the queue is empty *)
Definition engine_step {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (e : Engine.t X C A) :
  option (Engine.t X C A).
(* None when PQueue.is_empty (Engine.queue e). Otherwise:
   1. pop the least (priority, encode c) constraint c, leaving the queue q1;
   2. s := lookup EX L (Engine.current e); (v, rs, ss) := Query.run (System.rhs S c) s;
   3. with Recorded, add c to Engine.recorded at each x of rs; Declared leaves it unchanged;
   4. for each (x, a) of (System.target S c, v) :: ss in order, with cur the map so far: nothing if
      leb L a (lookup EX L cur x) = true; otherwise the value of x becomes
      widen L (lookup EX L cur x) a when st = Widening and widening_point sch x = true, and
      join L (lookup EX L cur x) a otherwise, and every constraint d among the readers of x
      (readers_of EX ix x with Declared; FinSet.elements of recorded at x with Recorded) is pushed
      on the queue at priority (priority sch (System.target S d)). *)
Definition engine_rel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (e' e : Engine.t X C A) : Prop :=
  engine_step EX EC L sch st S dep e = Some e'.
Inductive engine_steps {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    (st : strategy) (S : System.t X C A) (dep : dependencies S) :
    nat -> Engine.t X C A -> Engine.t X C A -> Prop :=
  | steps_zero : forall e, engine_steps EX EC L sch st S dep 0 e e
  | steps_succ : forall n e e' e'', engine_steps EX EC L sch st S dep n e e' ->
      engine_rel EX EC L sch st S dep e'' e' ->
      engine_steps EX EC L sch st S dep (Datatypes.S n) e e''.
(* engine_rel orders successor before predecessor for Acc; reachability follows steps forward *)
Definition engine_reachable {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (st : strategy) (S : System.t X C A) (dep : dependencies S)
    (e : Engine.t X C A) : Prop :=
  clos_refl_trans _ (fun from to => engine_rel EX EC L sch st S dep to from)
    (initial_state EC sch S) e.

(* the fuel loop is binary-recursive, so a fuel of n costs O(log n) stack and performs n steps *)
Inductive outcome (X C A : Type) : Type := Done (m : assignment X A) | Pending (e : Engine.t X C A).
Definition then_run {X C A} (f : Engine.t X C A -> outcome X C A) (o : outcome X C A) :
  outcome X C A := match o with Done m => Done m | Pending e => f e end.
Fixpoint loop {X C A} (step : Engine.t X C A -> outcome X C A) (p : positive) (e : Engine.t X C A) :
    outcome X C A :=
  match p with
  | xH => step e                                           (* loop xH = step *)
  | xO p' => then_run (loop step p') (loop step p' e)      (* loop (xO p) = loop p after loop p *)
  | xI p' => then_run step (then_run (loop step p') (loop step p' e))   (* step after loop p after loop p *)
  end.
(* step_outcome e is Done (current e) when engine_step e = None, else Pending of the next state;
   each then_run returns at once when the queue is empty *)
Definition run_worklist {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (dep : dependencies S) (fuel : positive) :
  option (assignment X A) :=
  match loop (step_outcome EX EC L sch st S dep) fuel (initial_state EC sch S) with
  | Done m => Some m | Pending _ => None
  end.
(* the fuel variant for any system, static or not, with a top fallback *)
Definition solve_fuel {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
  (T : top L) (sch : scheduler X) (st : strategy) (S : System.t X C A) (fuel : positive) :
  {s : X -> A | post_solution L S s}.
(* match run_worklist EX EC L sch st S Recorded fuel with
   | Some m => exist _ (lookup EX L m) (run_worklist_sound ..)
   | None => exist _ (fun _ => top_value T) (top_post_solution ..) end *)
```

### FIX-2b: the total engine (`FixpointTotal.v`)

The evidence is passed as `inhabited`, so extraction erases it. A client builds it from Order:
`inhabits (base_height H)` for `H : monotone_height L`, and `inhabits (base_wrank W)` for
`W : bounded_widening_rank L`. The proof of accessibility destructs `inhabited` only into a `Prop`
goal.

```coq
Definition terminates {X C A} {S : System.t X C A} (L : lattice A) (SS : System.static S)
    (sch : scheduler X) (st : strategy) : Prop :=
  match st with
  | Joining => inhabited (height L)
  | Widening => inhabited (widening_rank L) /\ cuts_every_cycle SS (widening_point sch)
  end.
Definition solve_total {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (HL : lattice_laws L)
  (sch : scheduler X) (st : strategy) (S : System.t X C A) (SS : System.static S)
  (HT : terminates L SS sch st) : {s : X -> A | post_solution L S s}.
(* Fix on Acc (engine_rel EX EC L sch st S (Declared SS (index_system EX S SS))) at the initial
   state, accessible by engine_acc. The recursion carries engine_reachable e. At a state e with
   engine_step e = None it returns lookup EX L (Engine.current e), a post-solution by
   engine_finished_sound; at Some e' it recurses on e'. No fuel and no evidence is computed. *)
```

### FIX-3: schedulers and narrowing

```coq
(* FixpointSchedule.v *)
Definition unknowns {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : list X.
(* FinSet.elements of FinSet.of_list EX: the distinct targets, deps and side targets of the constraints *)
Definition dependency_graph {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) :
    Graph.t X (X * X).
(* Graph.nodes = Graph.entries = unknowns; Graph.out y = the edges (y, x), one for each distinct x with
   flows SS y x, found through readers_of of index_system EX S SS, with no repeated edge;
   Graph.source = fst, Graph.target = snd *)
(* each scheduler below prepares its graph once, g := dependency_graph, p := prepare EX g, and its
   theorems use ready EX g p, proved by dependency_graph_ready *)
Definition rpo_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* r := dfs p FinSet.empty (Graph.entries g); priority = position in rpo r (a map built once);
   widening points = the targets of the retreating edges, tested with ancestor_b EX r *)
Definition wto_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* w := wto_total p, the total producer of Graph (always wto_valid); priority = textual position in
   wto_order w; widening points = the heads of the components of w *)
Definition scc_scheduler {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S) : scheduler X.
(* priority x = 1 + comp * n + pos, where n = length (unknowns EX S SS), comp = the index of the
   component of x counted from the end of Tarjan's emission order of scc_within p (Graph.nodes g)
   (so a component follows every component that flows into it), and pos = the rpo position of x;
   widening points = the headers of loop_forest_of p *)
Definition plan_of {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
  (ix : sys_index X C) (cuts : FinSet.t X) : option (list X).
(* topological_sort of the flows restricted to non-cut targets, over the unknowns that are not cut *)

(* FixpointNarrow.v *)
Definition narrow_pass {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (m : assignment X A) : assignment X A.
(* one simultaneous pass over the unknowns that have contributors, reading only m: with a the join of
   bot and the contributions at lookup EX L m to x (one Query.run per constraint), the new value is
   narrow L (m x) a when leb L a (m x) = true, and m x otherwise *)
Definition narrow_checked {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) (rounds : nat) (m : assignment X A) : assignment X A :=
  let m' := Nat.iter rounds (narrow_pass EX L S SS ix) m in
  if check_post L S (lookup EX L m') then m' else m.
```

### FIX-4: closed partial solutions and the local solver

```coq
(* FixpointPartial.v: on the explored set E, every constraint whose target is in E or that may
   contribute to E reads only E and is satisfied on E *)
Definition closed_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (E : FinSet.t X) (s : X -> A) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    (forall y, In y (Query.reads (System.rhs S c) s) -> FinSet.mem EX y E = true) /\
    (FinSet.mem EX (System.target S c) E = true ->
       leb L (Query.eval (System.rhs S c) s) (s (System.target S c)) = true) /\
    forall y a, In (y, a) (Query.sides (System.rhs S c) s) -> FinSet.mem EX y E = true ->
      leb L a (s y) = true.
Definition check_partial {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) : bool.
(* for each x in FinSet.elements E and each c in contributors_of EX ix x, one Query.run on
   lookup EX L m and the three conditions *)
(* E is closed under what its constraints read *)
Definition dependency_closed {X C A} (EX : encoding X) (S : System.t X C A) (SS : System.static S)
    (E : FinSet.t X) : Prop :=
  forall c, In c (System.constraints S) ->
    (FinSet.mem EX (System.target S c) E = true \/
       exists y, In y (side_targets SS c) /\ FinSet.mem EX y E = true) ->
    forall y, In y (deps SS c) -> FinSet.mem EX y E = true.

(* FixpointLocal.v *)
Record local_result (X A : Type) : Type := LocalResult { explored : FinSet.t X; values : assignment X A }.
Definition local_solve {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
  (st : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
  (roots : list X) (fuel : positive) : option (local_result X A).
(* the worklist over the dependency closure of roots: the least set E that contains roots and is
   closed under "x in E, c in contributors_of x, y in deps c gives y in E"; the queue starts with the
   constraints that contribute to E and the engine runs as engine_step with Declared SS ix, joins or
   widening as st says; explored = E. Untrusted: no theorem about its values. Acceptance evidence:
   a required Example in Examples runs local_checked on a three-unknown cyclic system and gets Some. *)
Definition local_checked {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A) (sch : scheduler X)
    (st : strategy) (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (roots : list X) (fuel : positive) : option (local_result X A) :=
  match local_solve EX EC L sch st S SS ix roots fuel with
  | Some r =>
      let E := FinSet.of_list EX (FinSet.elements (explored r)) in   (* normalised: FinSet.wf *)
      if check_partial EX L S SS ix E (values r) && forallb (fun x => FinSet.mem EX x E) roots
      then Some (LocalResult E (values r)) else None
  | None => None
  end.
```

### FIX-7: directly proved static local solving

`FixpointLocalDirect.v` adds a trusted internal producer for finite static systems. It does not
replace FIX-4's checker or claim to solve dynamic systems. Build the finite bipartite graph once:
unknown x reaches each indexed constraint that has nominal target x or declares x as a side
target; each such constraint reaches its nominal target, all declared side targets and all
declared reads. Starting from the roots, visit each discovered unknown and constraint at most
once using the existing encodings and indexed collections. Do not scan the constraints or the
unknown universe inside the traversal. Its unknown set is `local_direct_closure`. Roots outside
the system remain in the closure and have bottom values unless constrained.

`local_direct_system` retains exactly the original constraints reached by this closure, in the
original constraint-list order, and retains their original targets and query trees. It is built
once; `local_direct_static` restricts the existing declarations to that system. Run the existing
`solve_total` on the restricted system, then construct an assignment by storing the resulting
value for each closure member. All other unknowns have the assignment's default bottom. The
termination evidence supplied by the caller is for the restricted system and the selected
scheduler and strategy. The producer never calls `check_partial` or gates its result on checker
acceptance. No least-solution claim follows from these statements for weak joins or widening.

```coq
Definition local_direct_closure {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) : FinSet.t X.
Definition local_direct_system {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) : System.t X C A.
Definition local_direct_static {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  System.static (local_direct_system EX EC S SS ix roots).
Definition local_direct {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) : local_result X A.

Theorem local_direct_closure_wf {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  FinSet.wf EX (local_direct_closure EX EC S SS ix roots).
Theorem local_direct_closure_roots {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) :
  forall x, In x roots -> FinSet.mem EX x (local_direct_closure EX EC S SS ix roots) = true.
Theorem local_direct_closure_least {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (E : FinSet.t X) :
  FinSet.wf EX E -> (forall x, In x roots -> FinSet.mem EX x E = true) ->
  (forall x c, FinSet.mem EX x E = true -> In c (contributors_of EX ix x) ->
    FinSet.mem EX (System.target S c) E = true /\
    (forall y, In y (side_targets SS c) -> FinSet.mem EX y E = true) /\
    (forall y, In y (deps SS c) -> FinSet.mem EX y E = true)) ->
  FinSet.subset EX (local_direct_closure EX EC S SS ix roots) E = true.
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
Theorem local_direct_system_constraints {X C A} (EX : encoding X) (EC : encoding C)
  (S : System.t X C A) (SS : System.static S) (ix : sys_index X C) (roots : list X) (c : C) :
  sys_index_laws EX S SS ix ->
  (In c (System.constraints (local_direct_system EX EC S SS ix roots)) <->
   In c (System.constraints S) /\
   (FinSet.mem EX (System.target S c) (local_direct_closure EX EC S SS ix roots) = true \/
    exists y, In y (side_targets SS c) /\
      FinSet.mem EX y (local_direct_closure EX EC S SS ix roots) = true)).
Theorem local_direct_roots {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  forall x, In x roots -> FinSet.mem EX x (explored (local_direct EX EC L HL sch st S SS ix roots HT)) = true.
Theorem local_direct_closed {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (HL : lattice_laws L) (sch : scheduler X) (st : strategy) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (roots : list X)
  (HT : terminates L (local_direct_static EX EC S SS ix roots) sch st) :
  sys_index_laws EX S SS ix ->
  let r := local_direct EX EC L HL sch st S SS ix roots HT in
  closed_partial EX L S SS (explored r) (lookup EX L (values r)).
```

The closure is the least set containing roots and closed under these graph edges. Prove its
termination from the finite discovered support, and prove the restricted constraints are exactly
the reached constraints. The closure theorem and `reads_within` ensure that projecting the
engine's function to a finite assignment preserves each activated query's reads, result and side
contributions. Apply `solve_total`'s direct post-solution theorem to the restricted system and
transfer it to `closed_partial`; no global functional extensionality or per-run checker is needed.
Card: FIX-7.

## Theorems

### FIX-1

```coq
Section Fix1.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).
Variables (q : Query.t X A) (s t s1 s2 : X -> A) (xs : list X) (l : list (X * A))
  (k : list A -> Query.t X A) (m : assignment X A).

(** A query depends only on the unknowns it reads: agreement on them fixes its value, reads and contributions. *)
Theorem query_determined : (forall x, In x (Query.reads q s) -> s x = t x) ->
  Query.eval q s = Query.eval q t /\ Query.reads q s = Query.reads q t /\ Query.sides q s = Query.sides q t.
(* Proof idea: induction on q; at Ask x k the asked unknown agrees, so the continuations agree. Card: FIX-1. *)
(** The one-traversal `run` returns exactly the three separate answers. *)
Theorem run_spec : Query.run q s = (Query.eval q s, Query.reads q s, Query.sides q s).
(* Proof idea: induction on q. Card: FIX-1. *)
(** `ask_all` asks the listed unknowns in order, then continues with their values. *)
Theorem ask_all_spec : Query.reads (ask_all xs k) s = xs ++ Query.reads (k (map s xs)) s /\
  Query.eval (ask_all xs k) s = Query.eval (k (map s xs)) s /\
  Query.sides (ask_all xs k) s = Query.sides (k (map s xs)) s.
(* Proof idea: induction on xs. Card: FIX-1. *)
(** `side_all` contributes the listed pairs first and then behaves as the continuation. *)
Theorem side_all_spec : Query.eval (side_all l q) s = Query.eval q s /\
  Query.reads (side_all l q) s = Query.reads q s /\ Query.sides (side_all l q) s = l ++ Query.sides q s.
(* Proof idea: induction on l. Card: FIX-1. *)

(** The full checker decides post-solutions, and the all-top assignment is one. *)
Theorem check_post_iff : check_post L S s = true <-> post_solution L S s.
(* Proof idea: forallb_forall, run_spec, and leb = true is the Prop. Card: FIX-1. *)
Theorem top_post_solution (T : top L) : post_solution L S (fun _ => top_value T).
(* Proof idea: top_greatest for the value and for every contribution. Card: FIX-1. *)

(** The prepared indexes agree with the system. *)
Theorem index_system_laws (SS : System.static S) : sys_index_laws EX S SS (index_system EX S SS).
(* Proof idea: a fold of Map.set over the constraints, each added once per distinct unknown, then the Map.get_set lemmas and FinSet.of_list_spec. Card: FIX-1. *)

(** An accepted certificate expands to a post-solution that keeps the stored cut values. *)
Theorem expand_sound (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  lattice_laws L -> sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) ->
  expand EX L S SS ix cert = Some m ->
  post_solution L S (lookup EX L m) /\
  forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L m p = lookup EX L (stored cert) p.
(* Proof idea: a planned value is the join of every contribution to it, computed on values that are already final, so query_determined gives the final evaluation the same result; FinSet.elements_spec makes step 3 cover every cut point, checked against the final assignment; join_upper_l and join_upper_r give each leb. Card: FIX-1. *)
(** Completeness: a post-solution, its values at the cut points and a valid plan are accepted, and the expansion lies below it. *)
Theorem expand_complete (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  lattice_laws L -> lub_laws L -> monotone_system L S -> sys_index_laws EX S SS ix ->
  FinSet.wf EX (cuts cert) -> post_solution L S s -> plan_valid EX S SS ix (cuts cert) (plan cert) ->
  (forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L (stored cert) p = s p) ->
  exists m, expand EX L S SS ix cert = Some m /\ fun_leb L (lookup EX L m) s.
(* Proof idea: induction along the plan: each planned value is below s by monotonicity and join_least, since its reads are cut points or earlier values below s; reads_within makes the declared dependencies of plan_valid cover the dynamic reads; the cut-point check follows from the final assignment lying below s. Card: FIX-1. *)
(** Cycle detection is built in: a valid plan exists only when the cut points cut every cycle. *)
Theorem plan_valid_cuts (SS : System.static S) (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) :
  sys_index_laws EX S SS ix -> plan_valid EX S SS ix cuts plan ->
  cuts_every_cycle SS (fun x => FinSet.mem EX x cuts).
(* Proof idea: along a cycle of non-cut unknowns each flow puts the source earlier in the plan, so positions would increase strictly around the cycle. Card: FIX-1. *)

(** Replaying folds the observer over the order with each value; an invariant kept by every visited step holds at the end. *)
Theorem replay_invariant {B} (I : B -> Prop) (obs : B -> X -> A -> B) (b0 : B) (order : list X) :
  I b0 -> (forall b x, In x order -> I b -> I (obs b x (s x))) -> I (replay obs b0 order s).
(* Proof idea: induction on order, generalising the accumulator. Card: FIX-1. *)
(** The replay order of an accepted certificate lists every unknown that has a constraint, each once. *)
Theorem replay_covers (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) -> expand EX L S SS ix cert = Some m ->
  NoDup (FinSet.elements (cuts cert) ++ plan cert) /\
  forall x, (exists c, In c (System.constraints S) /\ (x = System.target S c \/ In x (side_targets SS c))) ->
    In x (FinSet.elements (cuts cert) ++ plan cert).
(* Proof idea: plan_valid's first three conditions, which expand checks, give NoDup and coverage; FinSet.elements_spec and FinSet.elements_nodup turn membership in the cut set into membership in the list. Card: FIX-1. *)

(** Under the strong laws, runs from bottom never exceed a post-solution of a monotone system; a reached post-solution is the least solution, which is unique up to equivalence. *)
Theorem reached_below : lattice_laws L -> lub_laws L -> monotone_system L S ->
  post_solution L S t -> reached EX L S s -> fun_leb L s t.
(* Proof idea: induction on the runs: bot_least, then each update (x, a) of a run at an assignment below t satisfies leb L a (t x) by monotone_query and the post-solution inequalities of t, so join_least keeps every value below t. Card: FIX-1. *)
Theorem reached_least : lattice_laws L -> lub_laws L -> monotone_system L S ->
  reached EX L S s -> post_solution L S s -> least_solution L S s.
(* Proof idea: reached_below for every post-solution. Card: FIX-1. *)
Theorem least_solution_unique : least_solution L S s1 -> least_solution L S s2 ->
  fun_leb L s1 s2 /\ fun_leb L s2 s1.
(* Proof idea: each is below the other by minimality. Card: FIX-1. *)
End Fix1.
```

### FIX-2a

Soundness never depends on the scheduler: it holds for every `sch`.

```coq
Section Fix2a.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (dep : dependencies S) (e : Engine.t X C A)
  (m : assignment X A).
Local Notation step := (engine_step EX EC L sch st S dep).
Local Notation start := (initial_state EC sch S).

(** A finished reachable state is a post-solution, whether dependencies are declared or recorded. *)
Theorem engine_finished_sound : lattice_laws L -> dependencies_ok EX dep ->
  engine_reachable EX EC L sch st S dep e -> step e = None ->
  post_solution L S (lookup EX L (Engine.current e)).
(* Proof idea: invariant: every constraint is queued or satisfied by the current values; a pop evaluates c once (run_spec), raises go upward (join_upper_r, widen_upper_r, leb_trans), and every constraint that reads a changed unknown is queued (readers_agree and reads_within with Declared; the recorded reads with Recorded, recorded before the updates), so an unqueued constraint keeps its reads and its value (query_determined); an empty queue (PQueue.pop_none, is_empty_spec) leaves no queued constraint. Card: FIX-2a. *)

(** The binary fuel loop performs exactly one engine step per unit of fuel, and stops at an empty queue. *)
Theorem run_worklist_spec (fuel : positive) :
  run_worklist EX EC L sch st S dep fuel = Some m <->
  exists n e', (n < Pos.to_nat fuel)%nat /\ engine_steps EX EC L sch st S dep n start e' /\
    step e' = None /\ Engine.current e' = m.
(* Proof idea: induction on the fuel: loop step p e is the (Pos.to_nat p)-fold iteration of step_outcome with an early exit, because loop (xO p) and loop (xI p) compose loop p twice, and then_run keeps a Done. Card: FIX-2a. *)
(** A finished run is a post-solution. *)
Theorem run_worklist_sound (fuel : positive) : lattice_laws L -> dependencies_ok EX dep ->
  run_worklist EX EC L sch st S dep fuel = Some m -> post_solution L S (lookup EX L m).
(* Proof idea: run_worklist_spec gives a reachable finished state; engine_finished_sound. Card: FIX-2a. *)
(** Adequacy from accessibility: if the engine's step relation is accessible from the initial state, enough fuel never runs out. *)
Theorem run_worklist_acc : Acc (engine_rel EX EC L sch st S dep) start ->
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S dep fuel = Some m'.
(* Proof idea: Acc induction: from an accessible state the unique step chain reaches a state with an empty queue after some n steps; take f = n + 1 and apply run_worklist_spec. Card: FIX-2a. *)
End Fix2a.
```

### FIX-2b

```coq
Section Fix2b.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A).
Variables (sch : scheduler X) (st : strategy) (T : top L) (m : assignment X A).

(** With termination evidence the step relation is accessible from the initial state, with declared or recorded dependencies. *)
Theorem engine_acc (SS : System.static S) (ix : sys_index X C) : lattice_laws L ->
  terminates L SS sch st -> sys_index_laws EX S SS ix ->
  Acc (engine_rel EX EC L sch st S (Declared SS ix)) (initial_state EC sch S) /\
  Acc (engine_rel EX EC L sch st S Recorded) (initial_state EC sch S).
(* Proof idea: a measure that decreases at every step of a state whose queue holds only constraints of S. Joining: the pair (sum over the finite set unknowns of bound minus rank of the value, queue length), lexicographic: an effective update increases a rank (join_rank_grows, using join_upper_r and leb_trans to turn "not below" into "the join is not below"), any other pop shortens the queue. Widening: (sum over widening points of wrank of the value, sum over queued constraints of weight), where weight c = 1 + the sum, over x in target c :: side_targets c, of 1 if x is a widening point and of the total weight of the readers of x otherwise, well founded because cuts_every_cycle forbids a cycle of constraints through non-widening unknowns; an update at a widening point lowers wrank (widen_rank_progress), and one elsewhere only queues readers of total weight below that of the popped constraint. Recorded readers are among the declared ones (reads_within). The Prop goal alone lets inhabited be destructed. Card: FIX-2b. *)
(** With termination evidence, enough fuel never runs out, with declared or recorded dependencies. *)
Theorem run_worklist_adequate (SS : System.static S) : lattice_laws L -> terminates L SS sch st ->
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
     run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m') /\
  (exists f, forall fuel, (f <= fuel)%positive -> exists m',
     run_worklist EX EC L sch st S Recorded fuel = Some m').
(* Proof idea: engine_acc with index_system_laws, then run_worklist_acc. Card: FIX-2b. *)
(** With evidence, the fuel variant returns the run, not the top fallback. *)
Theorem solve_fuel_exact (HL : lattice_laws L) (SS : System.static S) : terminates L SS sch st ->
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S Recorded fuel = Some m' /\
    proj1_sig (solve_fuel EX EC L HL T sch st S fuel) = lookup EX L m'.
(* Proof idea: run_worklist_adequate for Recorded, then unfold solve_fuel. Card: FIX-2b. *)
(** The Acc-based total solver and the fuel loop compute the same function. *)
Theorem solve_total_run (HL : lattice_laws L) (SS : System.static S) (HT : terminates L SS sch st) :
  exists f, forall fuel, (f <= fuel)%positive -> exists m',
    run_worklist EX EC L sch st S (Declared SS (index_system EX S SS)) fuel = Some m' /\
    proj1_sig (solve_total EX EC L HL sch st S SS HT) = lookup EX L m'.
(* Proof idea: both follow the same deterministic chain of engine_step to its first state with an empty queue; run_worklist_spec for the fuel side, the Fix equation for the other. Card: FIX-2b. *)
(** Without widening, every value of the result was reached from bottom by runs of constraints. *)
Theorem solve_total_reached (HL : lattice_laws L) (SS : System.static S)
    (HT : terminates L SS sch Joining) :
  reached EX L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
(* Proof idea: each step is one raise (the pops evaluate at the current values; skipped updates are skipped by join_update), so the chain of engine_step from the initial state is a clos_refl_trans chain up to pointwise equality of lookup EX L. Card: FIX-2b. *)
(** Without widening, the total engine returns the least solution of a monotone system. *)
Theorem solve_total_least (HL : lattice_laws L) (SS : System.static S)
    (HT : terminates L SS sch Joining) :
  lub_laws L -> monotone_system L S ->
  least_solution L S (proj1_sig (solve_total EX EC L HL sch Joining S SS HT)).
(* Proof idea: solve_total_reached and the post-solution proof of the sigma give reached_least. Card: FIX-2b. *)
End Fix2b.
```

### FIX-3

```coq
Section Fix3.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A) (SS : System.static S).
Variables (ix : sys_index X C) (rounds : nat) (m : assignment X A) (cuts : FinSet.t X).
Local Notation g := (dependency_graph EX S SS).

(** The unknowns are exactly those that occur, once each. *)
Theorem unknowns_spec : NoDup (unknowns EX S SS) /\ forall x, In x (unknowns EX S SS) <->
  exists c, In c (System.constraints S) /\
    (x = System.target S c \/ In x (deps SS c) \/ In x (side_targets SS c)).
(* Proof idea: FinSet.elements_nodup and FinSet.of_list_spec. Card: FIX-3. *)
(** The flows of the system are the edges of its dependency graph, which is well formed and ready for the Graph algorithms. *)
Theorem dependency_graph_flows : graph_wf g /\ (forall v, NoDup (Graph.out g v)) /\
  forall y x, flows SS y x <-> exists e, In e (Graph.out g y) /\ Graph.target g e = x.
(* Proof idea: unfold dependency_graph; the unknowns list contains every end of a flow, and the edges are collected through FinSet so none repeats. Card: FIX-3. *)
Theorem dependency_graph_ready : ready EX g (prepare EX g).
(* Proof idea: prepare_ready on dependency_graph_flows. Card: FIX-3. *)

(** The widening points of each scheduler cut every cycle of flows, so a widening rank suffices for termination. *)
Theorem rpo_scheduler_cuts : cuts_every_cycle SS (widening_point (rpo_scheduler EX S SS)).
(* Proof idea: a cycle of flows is a cycle of the dependency graph, which contains a retreating edge (cycle_has_retreating_edge, with ancestor_b_agrees) whose target is a widening point on the cycle. Card: FIX-3. *)
Theorem wto_scheduler_cuts : cuts_every_cycle SS (widening_point (wto_scheduler EX S SS)).
(* Proof idea: wto_total_valid holds (the producer falls back to the all-heads order), and
   wto_valid_cycles puts the head of a component on every cycle. Card: FIX-3. *)
Theorem scc_scheduler_cuts : cuts_every_cycle SS (widening_point (scc_scheduler EX S SS)).
(* Proof idea: loop_forest_covers puts a header of loop_forest_of on every cycle. Card: FIX-3. *)

(** `plan_of` succeeds exactly when the cut points cut every cycle, and then its plan is valid. *)
Theorem plan_of_valid : sys_index_laws EX S SS ix ->
  (cuts_every_cycle SS (fun x => FinSet.mem EX x cuts) <-> exists plan, plan_of EX S SS ix cuts = Some plan) /\
  forall plan, plan_of EX S SS ix cuts = Some plan -> plan_valid EX S SS ix cuts plan.
(* Proof idea: topological_sort_correct on the flows into non-cut unknowns; plan_valid_cuts for the converse. Card: FIX-3. *)

(** Narrowing keeps soundness and never moves a value up; the checker guards the output. *)
Theorem narrow_checked_post : post_solution L S (lookup EX L m) ->
  post_solution L S (lookup EX L (narrow_checked EX L S SS ix rounds m)).
(* Proof idea: either the checker accepted the narrowed assignment (check_post_iff) or the input is returned. Card: FIX-3. *)
Theorem narrow_checked_below : lattice_laws L ->
  fun_leb L (lookup EX L (narrow_checked EX L S SS ix rounds m)) (lookup EX L m).
(* Proof idea: a pass narrows only under leb L a (m x) = true, so narrow_lower gives a decrease, else the value is kept (leb_refl); induction on rounds. Card: FIX-3. *)
End Fix3.
```

### FIX-4

```coq
Section Fix4.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A) (SS : System.static S).
Variables (ix : sys_index X C) (E : FinSet.t X) (m : assignment X A) (s t l : X -> A).

(** The checker decides closed partial solutions on a well-formed explored set, reading only the constraints that touch it. *)
Theorem check_partial_correct : sys_index_laws EX S SS ix -> FinSet.wf EX E ->
  (check_partial EX L S SS ix E m = true <-> closed_partial EX L S SS E (lookup EX L m)).
(* Proof idea: contributors_agree says the indexed constraints are exactly those with a target or declared side target in E; FinSet.elements_spec makes the iteration cover E. Card: FIX-4. *)

(** A closed partial solution is the restriction of a global post-solution, so every theorem proved
    for all post-solutions holds at its unknowns, and it lies above the least solution there. *)
Theorem closed_partial_extends (T : top L) : closed_partial EX L S SS E s ->
  exists t, post_solution L S t /\ forall x, FinSet.mem EX x E = true -> t x = s x.
(* Proof idea: t is s on E and top elsewhere; a checked constraint reads only E, so t agrees with s on its reads (query_determined) and satisfies it; any other constraint targets top, and contributes into E only if it was checked, by sides_within. Card: FIX-4. *)
Theorem closed_partial_above_least (T : top L) : closed_partial EX L S SS E s -> least_solution L S l ->
  forall x, FinSet.mem EX x E = true -> leb L (l x) (s x) = true.
(* Proof idea: closed_partial_extends gives a post-solution t; l is below t and t x = s x. Card: FIX-4. *)
(** Conversely, every post-solution restricts to a closed partial solution on each dependency-closed set. *)
Theorem post_solution_closed : post_solution L S t -> dependency_closed EX S SS E ->
  closed_partial EX L S SS E t.
(* Proof idea: reads_within puts the reads of a touched constraint in deps, hence in E; the inequalities are post_solution's. Card: FIX-4. *)

(** An accepted local run is a well-formed closed partial solution that covers its roots. *)
Theorem local_checked_sound (EC : encoding C) (sch : scheduler X) (st : strategy)
    (roots : list X) (fuel : positive) (r : local_result X A) :
  sys_index_laws EX S SS ix -> local_checked EX EC L sch st S SS ix roots fuel = Some r ->
  FinSet.wf EX (explored r) /\
  closed_partial EX L S SS (explored r) (lookup EX L (values r)) /\
  forall x, In x roots -> FinSet.mem EX x (explored r) = true.
(* Proof idea: the explored set is FinSet.of_list of an elements list, well formed by FinSet.wf_ops; the two conjuncts of the test, by check_partial_correct and forallb_forall. Card: FIX-4. *)
End Fix4.
```

## Algorithms and references

- **Worklist iteration** with a priority queue: Kildall, "A unified approach to global program
  optimization" (POPL 1973); chaotic iteration as in Nielson, Nielson and Hankin, *Principles of
  Program Analysis* (1999). Raising an unknown pushes only its readers.
- **Fuel and accessibility.** The fuel loop is binary-recursive, so `n` steps cost O(log n) stack;
  the total solver recurses on an `Acc` proof (Bove and Capretta's method), which extraction erases.
- **Widening and narrowing:** Cousot and Cousot (POPL 1977 and 1979). Widening only at a set that
  cuts every cycle: Bourdoncle, "Efficient chaotic iteration strategies with widenings" (1993).
- **Side-effecting constraint systems:** Apinis, Seidl and Vojdani, "Side-effecting constraint
  systems: a Swiss Army knife for program analysis" (APLAS 2012). The query tree `Ret`/`Ask`/`Side`
  is the free form of such a right-hand side, so reads and contributions are observable.
- **Checking only at cut points:** Besson, Jensen and Pichardie, "Proof-carrying code from
  certified abstract interpretation and fixpoint compression" (TCS 2006); Rose, "Lightweight
  bytecode verification" (J. Automated Reasoning 2003). `expand` is the one-pass recomputation.
- **Local solvers:** Le Charlier and Van Hentenryck, "A universal top-down fixpoint algorithm"
  (1992); Fecht and Seidl, "A faster solver for general systems of equations" (1999). The solver
  is untrusted; `check_partial` is the verified part.
- **Constructive fixpoints in a proof assistant:** Cachera, Jensen, Pichardie and Rusu,
  "Extracting a data flow analyser in constructive logic" (TCS 2005).

## Performance notes

- The engine keeps a `PQueue` of constraints keyed by `encoding C` with the priority of the target.
  A pop evaluates one right-hand side once (`Query.run`), costing its size; an update pushes
  `readers_of` the unknown, a prepared list, so no constraint list is scanned inside the loop. With
  `Recorded`, readers live in a `Map.t X (FinSet.t C)`, so a repeated read is not stored twice.
  The number of pops is bounded by the number of constraints times one plus the number of changes
  of what each reads.
- Each prepared index has an agreement lemma: `contributors` and `readers` with `sys_index_laws`
  (`index_system_laws`); the partial checker and narrowing reuse the same index. The schedulers
  build their dependency graph and its preparation once, outside the closures they return.
- `check_post` is O(sum of right-hand-side sizes). `expand` is one pass: O(sum over constraints of
  (1 + side targets) times right-hand-side size), with the plan position never searched (`cur` is
  a `Map`). `narrow_pass` is one evaluation of every constraint per round. `check_partial` costs the
  constraints that touch `E`, found through `contributors`, not the whole system.
- `solve_total` carries its termination proof in `Prop`, which extraction erases, so no fuel or
  evidence is passed at run time; `solve_fuel` pays one unit per pop.

## Open questions

1. **Constraint encodings.** The engine queues constraints, so the constraint type needs an
   `encoding C`; Views' `dense_constraint N E` has one by `sum_encoding`, and `E` must be encodable.
2. **WTO strategy.** `wto_scheduler` is a priority (textual position) with widening at heads. The
   recursive Bourdoncle strategy, which stabilises a component before leaving it, is not a
   priority order and is left out; the termination and soundness theorems do not need it.
3. **Lattices without a join-least law.** The least-solution theorems need `lub_laws`; for
   weak-law domains (wrapping intervals) only post-solutions are claimed.
4. **Side effects and cut points.** A contribution to `y` from `c` makes `c` a contributor of
   `y`, so a plan must place every unknown `c` reads before `y`; a system whose side effects point
   backwards needs `y` as a cut point. `flows` includes side targets for this reason.
5. **Local solver scope.** `FIX-4` needs a `System.static` (for `side_targets`); the dynamic
   points-to system of Analyses has none, so it is checked by `check_post` only.
6. **Determinism.** Pop order is `(priority, encode c)`, fixed by Collections' `PQueue`, so every
   run is reproducible; the least solution does not depend on it, a widened result may.

## Cross-document contracts

The solver results are functions carrying post-solution proofs. Schedulers prepare the static
system dependency graph; `wto_scheduler` constructs its WTO with `wto_total`. Termination
evidence is `inhabits (base_height H)` or `inhabits (base_wrank W)`. Graph preparation requires
well-formed graphs and duplicate-free outgoing edges.
