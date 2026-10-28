# Gaulois.Views

A view tells the library how one language's executions relate to a graph, a structured tree, SSA
values, effects, calls or memory. A client proves once that its semantics respects a view, and
every analysis written over that view is then sound for that client. For example, a toy language
whose state records a program point supplies `point`, proves that every step follows an out-edge
of that point, and receives a forward-invariant theorem and a liveness-style bisimulation theorem
without writing either proof.

Conventions used in every signature below:
- The type variables `S O N E V K C A F P St` are implicit and universally quantified. `S` is a
  state, `O` an observable event, `N` a graph node, `E` an edge, `V` an SSA value, `K` an
  operation, `C` a concrete value, `A` an abstract fact, `F` a function, `P` a call site and
  `St` a client store; `I`, `H`, `L` and `T` are an instruction, a heap image, an allocation
  identity and an allocation site.
- Records whose projections clash live in modules, and code writes the module, never the file.
  The graph record is `Graph.t N E` with `Graph.entries`, `Graph.nodes`, `Graph.out`,
  `Graph.source` and `Graph.target`. A constraint system is `System.t X C A` with
  `System.constraints`, `System.target` and `System.rhs`; a static one is `System.static S`, whose
  projections `deps` and `side_targets` are bare. A query tree is `Query.t X A` with the
  constructors `Query.Ret`, `Query.Ask`, `Query.Side` and the functions `Query.eval`,
  `Query.reads` and `Query.sides`. `post_solution`, `graph_wf` and `reachable` keep their names.
  `Go` and `Ret` below are the constructors of `mstate`, never `Query.Ret`, and a bare `reads` is
  the field of `effects`.
- Names of other packages are used as their documents define them: `lattice`, `leb`, `bot`, `join`,
  `top`, `gamma`, `agree`, `concretisation_laws`, `agreement_laws`, `lift_bot` with `Unreached`
  and `Reached` (Order); `path`, `reachable`, `graph_wf`, `dominates`, `strictly_dominates`,
  `edge_dominates`, `prepared`, `prepare`, `dom_tree`, `dominator_tree`, `edge_dom_index`,
  `dominating_edges` (Graph); `post_solution`, `cuts_every_cycle`, `assignment`, `lookup`,
  `solve_total`, `solve_fuel` (Fixpoint); `encoding`, `sum_encoding`, `pair_encoding`,
  `list_encoding`, `nat_encoding`, `Map.t` (Collections); `footprint` and `covered` (Domains,
  DOM-6).
- `Import ListNotations` is in force. Every `Inductive` is followed by `Arguments` declarations that
  make its type parameters implicit; they are omitted here.
- A declaration that ends in `.` with no body is a signature; the lines after it list equations
  that the body satisfies by `reflexivity`. The card writes the body.
- `sigma` is a function `N -> A` (or over another unknown type). An engine (`solve_total` or
  `solve_fuel`) returns `{s : X -> A | post_solution L S s}`, and
  `lookup EX L m` is such a function.
- A concretisation or agreement that takes the solution (`G sigma`, `R sigma`), and a premise that
  names `sigma (point gv s)`, is solution-relative: a local obligation need hold only for the fact
  that the solution assigns at that point, not for every fact, so a client may compare suspended
  frames at their continuation facts. A client with no use for the solution passes `fun _ => G0`.
- A run's result is an event. A language whose runs return a value emits it as the last event of
  the trace, so two runs with equal traces and the same ending return the same value; no ending
  carries a value.

## Files

| File | Contents | Card |
|---|---|---|
| `ViewsSsaPoints.v` | finite instruction points, edge operands and syntactic liveness | VIEW-8 |
| `ViewsSemantics.v` | endings, runs (`exec`, `exec_in`), divergence, behaviours, bisimulation and stuttering bisimulation between semantics | VIEW-1 |
| `ViewsGraph.v` | graph view and its laws, dense forward and backward generators with their cut points, run histories | VIEW-1 |
| `ViewsForward.v` | the forward-invariant theorems, over states and over histories | VIEW-1 |
| `ViewsAgreement.v` | agreement obligations, the one-program and two-program agreement theorems | VIEW-1 |
| `ViewsSkeleton.v` | skeleton syntax, positions, frame-machine semantics, client laws | VIEW-2 |
| `ViewsStructured.v` | skeleton graph (slot edges), skeleton view, generators, soundness, cut points | VIEW-2 |
| `ViewsRegion.v` | region summaries, label inventory, normal completion, nesting, skeleton depth, balanced sequences | VIEW-3 |
| `ViewsSsa.v` | SSA view and laws, sparse conditional generator, sparse soundness | VIEW-4 |
| `ViewsRefine.v` | edge argument refinement and guard back-propagation | VIEW-4 |
| `ViewsDominated.v` | strictness, the dominated-use equation lemma, the dominator context, on-demand refined facts | VIEW-5 |
| `ViewsEffects.v` | effects view and its laws | VIEW-6 |
| `ViewsCalls.v` | calls view, resolver, call graph | VIEW-6 |
| `ViewsSummary.v` | bottom-up summary engine and summary soundness over frames | VIEW-6 |
| `ViewsMemory.v` | memory view, points-to soundness template | VIEW-7 |
| `ViewsMemoryEffects.v` | ordered memory effects and execution correspondence | ANA-10b |

## Definitions

### VIEW-1: semantics adapter, graph view, dense generators

```coq
(* ViewsSemantics.v. `semantics S O` is fixed by the anchors: initial and step. *)
Record endings (S : Type) : Type := Endings {
  final : S -> Prop;                (* normal termination *)
  trapped : S -> Prop;              (* the program traps *)
  stopped : S -> Prop               (* stopped by resource exhaustion, not by the program *)
}.
Definition running {S O} (m : semantics S O) (s : S) : Prop := exists l s', step m s l s'.
Definition stuck {S O} (m : semantics S O) (en : endings S) (s : S) : Prop :=
  ~ running m s /\ ~ final en s /\ ~ trapped en s /\ ~ stopped en s.
Record endings_wf {S O} (m : semantics S O) (en : endings S) : Prop := {
  final_halts : forall s, final en s -> ~ running m s;
  trapped_halts : forall s, trapped en s -> ~ running m s;
  stopped_halts : forall s, stopped en s -> ~ running m s;
  final_not_trapped : forall s, final en s -> ~ trapped en s;
  final_not_stopped : forall s, final en s -> ~ stopped en s;
  trapped_not_stopped : forall s, trapped en s -> ~ stopped en s
}.
(* A finite run with its trace. *)
Inductive exec {S O} (m : semantics S O) : S -> list O -> S -> Prop :=
  | exec_refl : forall s, exec m s nil s
  | exec_step : forall s l s' tr s'',
      step m s l s' -> exec m s' tr s'' -> exec m s (l ++ tr) s''.
(* A finite run all of whose states, the last one included, satisfy P. *)
Inductive exec_in {S O} (m : semantics S O) (P : S -> Prop) : S -> list O -> S -> Prop :=
  | exec_in_refl : forall s, P s -> exec_in m P s nil s
  | exec_in_step : forall s l s' tr t,
      P s -> step m s l s' -> exec_in m P s' tr t -> exec_in m P s (l ++ tr) t.
(* An infinite run; its events are not constrained. *)
CoInductive diverges {S O} (m : semantics S O) : S -> Prop :=
  | diverges_step : forall s l s', step m s l s' -> diverges m s' -> diverges m s.
Definition reachable_state {S O} (m : semantics S O) (s : S) : Prop :=
  exists s0 tr, initial m s0 /\ exec m s0 tr s.
Inductive ending : Type := EndFinal | EndTrap | EndStop | EndStuck.
Definition ends_as {S O} (m : semantics S O) (en : endings S) (k : ending) (s : S) : Prop :=
  match k with
  | EndFinal => final en s
  | EndTrap => trapped en s
  | EndStop => stopped en s
  | EndStuck => stuck m en s
  end.
(* The traces after which a state can diverge. *)
Definition diverges_after {S O} (m : semantics S O) (s : S) (tr : list O) : Prop :=
  exists t, exec m s tr t /\ diverges m t.
(* Observable behaviour of a state: the (trace, ending) pairs it can finish with, the traces of
   its finite runs, and the traces after which it can diverge. Two states are equivalent when all
   three agree. By the convention above the trace includes the result. *)
Record same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (s1 : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (s2 : S2) : Prop := {
  same_finish : forall k tr,
    (exists t, exec m1 s1 tr t /\ ends_as m1 e1 k t) <->
    (exists t, exec m2 s2 tr t /\ ends_as m2 e2 k t);
  same_prefix : forall tr, (exists t, exec m1 s1 tr t) <-> (exists t, exec m2 s2 tr t);
  same_diverging_prefix : forall tr, diverges_after m1 s1 tr <-> diverges_after m2 s2 tr
}.
(* A lock-step bisimulation between two semantics over the same events. *)
Record bisimulation {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) : Prop := {
  bisim_ends : forall s t k, R s t -> (ends_as m1 e1 k s <-> ends_as m2 e2 k t);
  bisim_forth : forall s t l s', R s t -> step m1 s l s' ->
    exists t', step m2 t l t' /\ R s' t';
  bisim_back : forall s t l t', R s t -> step m2 t l t' ->
    exists s', step m1 s l s' /\ R s' t'
}.
(* A stuttering bisimulation between two semantics over the same events. Related states advance
   together; a program may take a silent step alone while its measure falls, and a step of one
   program is matched by a silent run and one step of the other. The measures bound the silent steps
   a program may take alone, so a diverging run is matched by a diverging run. Every ending,
   including stuck, is explicitly matched after a silent run. *)
Record stuttering {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (m2 : semantics S2 O)
    (e2 : endings S2) (R : S1 -> S2 -> Prop) (mu1 mu2 : S1 -> S2 -> nat) : Prop := {
  st_ends_forth : forall s t k, R s t -> ends_as m1 e1 k s ->
    exists t1, exec m2 t nil t1 /\ ends_as m2 e2 k t1;
  st_ends_back : forall s t k, R s t -> ends_as m2 e2 k t ->
    exists s1, exec m1 s nil s1 /\ ends_as m1 e1 k s1;
  st_forth : forall s t l s', R s t -> step m1 s l s' ->
    (l = nil /\ R s' t /\ mu1 s' t < mu1 s t) \/
    (exists t1 t', exec m2 t nil t1 /\ step m2 t1 l t' /\ R s' t');
  st_back : forall s t l t', R s t -> step m2 t l t' ->
    (l = nil /\ R s t' /\ mu2 s t' < mu2 s t) \/
    (exists s1 s', exec m1 s nil s1 /\ step m1 s1 l s' /\ R s' t')
}.
```

```coq
(* ViewsGraph.v *)
Record graph_view (S O N E : Type) : Type := GraphView {
  cfg : Graph.t N E;
  point : S -> N;
  taken : S -> list O -> S -> E -> Prop;   (* the step goes along edge e *)
  stays : S -> list O -> S -> Prop         (* a step that does not move the point; often empty *)
}.
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
Definition edges_of {N E} (g : Graph.t N E) : list E := flat_map (Graph.out g) (Graph.nodes g).
Inductive dense_constraint (N E : Type) : Type := Seed (n : N) | Flow (e : E).
Definition dense_constraint_encoding {N E} (EN : encoding N) (EE : encoding E) :
  encoding (dense_constraint N E).
(* the code of Seed n is that of inl n in sum_encoding EN EE, and of Flow e that of inr e *)

(* Forward: sigma n over-approximates the states at n. *)
Definition forward_system {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A) :
  System.t N (dense_constraint N E) A.
(* System.constraints = map Seed (Graph.entries g) ++ map Flow (edges_of g)
   System.target (Seed n) = n                    System.rhs (Seed n) = Query.Ret (init n)
   System.target (Flow e) = Graph.target g e     System.rhs (Flow e) =
     Query.Ask (Graph.source g e) (fun a => Query.Ret (ft e a)) *)
Definition forward_static {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A) :
  System.static (forward_system g init ft).
(* deps (Seed _) = nil; deps (Flow e) = [Graph.source g e]; side_targets _ = nil *)

(* Backward: sigma n describes what is needed at n; the edge transfer maps the fact at the
   target to a fact at the source, and exitf seeds every node. *)
Definition backward_system {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A) :
  System.t N (dense_constraint N E) A.
(* System.constraints = map Seed (Graph.nodes g) ++ map Flow (edges_of g)
   System.target (Seed n) = n                    System.rhs (Seed n) = Query.Ret (exitf n)
   System.target (Flow e) = Graph.source g e     System.rhs (Flow e) =
     Query.Ask (Graph.target g e) (fun a => Query.Ret (bt e a)) *)
Definition backward_static {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A) :
  System.static (backward_system g exitf bt).
(* deps (Seed _) = nil; deps (Flow e) = [Graph.target g e]; side_targets _ = nil *)

(* A node predicate meets every cycle when each cycle of the graph visits a node that satisfies it:
   such a predicate is a set of widening points for either generator. *)
Definition meets_every_cycle {N E} (g : Graph.t N E) (W : N -> bool) : Prop :=
  forall v es, es <> nil -> path g v es v -> exists e, In e es /\ W (Graph.source g e) = true.

(* Histories. The edges taken along a run, first edge first; a stay step takes no edge. *)
Inductive run_edges {S O N E} (m : semantics S O) (gv : graph_view S O N E) :
    S -> list E -> S -> Prop :=
  | run_nil : forall s, run_edges m gv s nil s
  | run_cons : forall s l s' e es t, step m s l s' -> taken gv s l s' e ->
      run_edges m gv s' es t -> run_edges m gv s (e :: es) t
  | run_stay : forall s l s' es t, step m s l s' -> stays gv s l s' ->
      run_edges m gv s' es t -> run_edges m gv s es t.
(* Reaching definitions over a history: the last edge of the history that writes x. *)
Definition last_writer {E X} (writes : E -> X -> bool) (es : list E) (x : X) : option E :=
  fold_left (fun r e => if writes e x then Some e else r) es None.
(* Arrival counts over a history: the edges that satisfy `back` since the last edge that satisfies
   `enter`, or since the start when there is none. *)
Definition arrivals_since {E} (enter back : E -> bool) (es : list E) : nat :=
  fold_left (fun n e => if enter e then 0 else if back e then S n else n) es 0.
```

```coq
(* ViewsAgreement.v: the per-step obligations of a backward analysis. `agree` is symmetric. *)
Definition agreement_symmetric {A C} (R : agreement A C) : Prop :=
  forall a x y, agree R a x y -> agree R a y x.
Definition agreement_swap {A C} (R : agreement A C) : agreement A C :=
  Agreement (fun a x y => agree R a y x).
Record invariant_of {S O} (m : semantics S O) (inv : S -> Prop) : Prop := {
  inv_initial : forall s, initial m s -> inv s;
  inv_step : forall s l s', inv s -> step m s l s' -> inv s';
  inv_reachable : forall s, inv s -> reachable_state m s
}.
(* Per-step agreement, relative to the solution. `inv` may carry forward facts; both runs satisfy
   it. A step of s along e, from states that agree at the input fact of e, is matched by a step of
   t along e that agrees at the fact the solution assigns to the target of e; a stay keeps the
   fact of the point. *)
Definition step_agrees {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (R : agreement A S) (inv : S -> Prop) (bt : E -> A -> A) (sigma : N -> A) : Prop :=
  (forall e s l s' t, inv s -> inv t -> point gv t = point gv s ->
    step m s l s' -> taken gv s l s' e ->
    agree R (bt e (sigma (Graph.target (cfg gv) e))) s t ->
    exists t', step m t l t' /\ taken gv t l t' e /\
      agree R (sigma (Graph.target (cfg gv) e)) s' t') /\
  (forall s l s' t, inv s -> inv t -> point gv t = point gv s ->
    step m s l s' -> stays gv s l s' -> agree R (sigma (point gv s)) s t ->
    exists t', step m t l t' /\ stays gv t l t' /\ agree R (sigma (point gv s)) s' t').
(* Agreement at the node fixes whether a state is final, trapped or stopped. *)
Definition ends_agree {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (R : agreement A S) (inv : S -> Prop) (exitf : N -> A) : Prop :=
  forall s t, inv s -> inv t -> point gv t = point gv s -> agree R (exitf (point gv s)) s t ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t).
Definition agreeing {S O N E A} (gv : graph_view S O N E) (R : agreement A S) (inv : S -> Prop)
    (sigma : N -> A) (s t : S) : Prop :=
  point gv t = point gv s /\ inv s /\ inv t /\ agree R (sigma (point gv s)) s t.

(* Two programs. An original (ma, gva) and its transform (mb, gvb) share the state type and the
   graph. `forth_agrees` is the obligation for the steps of the original: a step along an edge is
   matched by a silent run and a step of the transform that reaches the point of the successor,
   agreeing at the fact of that point; a stay is either a silent step that the transform does not
   match, while the measure mua of the original falls, or is matched likewise, so a pass that
   deletes instructions is covered. The matching step needs no edge of its own: only the point and
   the agreement are observed. *)
Definition forth_agrees {S O N E A} (ma mb : semantics S O) (gva gvb : graph_view S O N E)
    (R : agreement A S) (inva invb : S -> Prop) (bt : E -> A -> A) (sigma : N -> A)
    (mua : S -> S -> nat) : Prop :=
  (forall e s l s' t, inva s -> invb t -> point gvb t = point gva s ->
    step ma s l s' -> taken gva s l s' e ->
    agree R (bt e (sigma (Graph.target (cfg gva) e))) s t ->
    exists t1 t', exec mb t nil t1 /\ step mb t1 l t' /\ point gvb t' = point gva s' /\
      agree R (sigma (point gva s')) s' t') /\
  (forall s l s' t, inva s -> invb t -> point gvb t = point gva s ->
    step ma s l s' -> stays gva s l s' -> agree R (sigma (point gva s)) s t ->
    (l = nil /\ agree R (sigma (point gva s)) s' t /\ mua s' t < mua s t) \/
    (exists t1 t', exec mb t nil t1 /\ step mb t1 l t' /\ point gvb t' = point gva s' /\
       agree R (sigma (point gva s')) s' t')).
(* The ending obligation for one direction: every ending of one state, including stuck, is
   matched after a silent run by the same ending of the other when states agree at the exit fact.
   The obligation is per kind, so a pass that may delete a trap discharges the trap obligation of
   the original under the premise that no reachable state of the original is trapped. *)
Definition ends_forth {S O N E A} (ma mb : semantics S O) (ea eb : endings S)
    (gva gvb : graph_view S O N E) (R : agreement A S) (inva invb : S -> Prop)
    (exitf : N -> A) : Prop :=
  forall s t k, inva s -> invb t -> point gvb t = point gva s ->
    agree R (exitf (point gva s)) s t -> ends_as ma ea k s ->
    exists t1, exec mb t nil t1 /\ ends_as mb eb k t1.
(* Both directions. The roles swap, and the agreement is read the other way round. *)
Definition step_agrees2 {S O N E A} (m1 m2 : semantics S O) (gv1 gv2 : graph_view S O N E)
    (R : agreement A S) (inv1 inv2 : S -> Prop) (bt : E -> A -> A) (sigma : N -> A)
    (mu1 mu2 : S -> S -> nat) : Prop :=
  forth_agrees m1 m2 gv1 gv2 R inv1 inv2 bt sigma mu1 /\
  forth_agrees m2 m1 gv2 gv1 (agreement_swap R) inv2 inv1 bt sigma (fun t s => mu2 s t).
Definition ends_agree2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (gv1 gv2 : graph_view S O N E) (R : agreement A S) (inv1 inv2 : S -> Prop)
    (exitf : N -> A) : Prop :=
  ends_forth m1 m2 en1 en2 gv1 gv2 R inv1 inv2 exitf /\
  ends_forth m2 m1 en2 en1 gv2 gv1 (agreement_swap R) inv2 inv1 exitf.
Definition agreeing2 {S O N E A} (gv1 gv2 : graph_view S O N E) (R : agreement A S)
    (inv1 inv2 : S -> Prop) (sigma : N -> A) (s t : S) : Prop :=
  point gv2 t = point gv1 s /\ inv1 s /\ inv2 t /\ agree R (sigma (point gv1 s)) s t.
(* ViewsForward.v: the invariant that forward facts give. *)
Definition forward_inv {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (G : concretisation A S) (sigma : N -> A) (s : S) : Prop :=
  reachable_state m s /\ gamma G (sigma (point gv s)) s.
```

### VIEW-2: structured skeleton and its frame machine

```coq
(* ViewsSkeleton.v. Jumps use relative depths: depth 0 is the innermost enclosing label, and
   labels are Block (jump leaves it) and Loop (jump restarts its body). A Loop repeats its body
   when the body completes; it is left only by a jump to an enclosing Block. *)
Module Skeleton.
Inductive stmt (A G : Type) : Type :=
  | Atom (a : A)
  | Seq (s1 s2 : stmt A G)
  | If (g : G) (s1 s2 : stmt A G)
  | Block (s : stmt A G)
  | Loop (s : stmt A G)
  | Jump (n : nat)
  | JumpIf (g : G) (n : nat)
  | JumpTable (g : G) (ns : list nat) (n : nat).   (* index i jumps to nth i ns n; n is the default *)
End Skeleton.
Import Skeleton.
Inductive dir : Type := DFirst | DSecond | DBody.   (* Seq and If: first, second; Block, Loop: body *)
Definition position : Type := list dir.             (* root = nil, outermost direction first *)
Definition dir_encoding : encoding dir.             (* DFirst has code 1, DSecond 2, DBody 3 *)
Definition position_encoding : encoding position := list_encoding dir_encoding.
Definition child {A G} (s : stmt A G) (d : dir) : option (stmt A G).
Fixpoint sub {A G} (s : stmt A G) (p : position) : option (stmt A G).
(* sub s nil = Some s; sub s (d :: p) = child s d >>= fun c => sub c p *)
Fixpoint positions {A G} (s : stmt A G) : list position.
(* The valid positions in pre-order. Atom, Jump, JumpIf and JumpTable: [nil]; Seq s1 s2 and
   If _ s1 s2: nil :: map (cons DFirst) (positions s1) ++ map (cons DSecond) (positions s2);
   Block s and Loop s: nil :: map (cons DBody) (positions s) *)
Fixpoint labels_ok {A G} (d : nat) (s : stmt A G) : bool.
(* d counts the enclosing labels: labels_ok d (Block s) = labels_ok (S d) s, same for Loop;
   labels_ok d (Jump n) = n <? d; JumpTable also checks every element of ns; others recurse *)

Record skeleton_client (A G St O : Type) : Type := SkeletonClient {
  init_store : St -> Prop;
  atom_step : A -> St -> list O -> St -> Prop;
  atom_trap : A -> St -> Prop;
  atom_stop : A -> St -> Prop;
  guard_bool : G -> St -> option bool;       (* None: evaluating the guard traps *)
  guard_index : G -> St -> option nat;       (* for JumpTable; None: traps *)
  jump_effect : position -> nat -> St -> St -> Prop
    (* the effect on the store of the jump statement at p when it leaves for the label of depth n,
       for example unwinding the scopes between them *)
}.
(* What every client must provide. `jump_total` keeps the laws that mention `jump_effect` from
   being vacuous: a client whose jump effect is empty would be stuck at every jump. *)
Record skeleton_client_laws {A G St O} (C : skeleton_client A G St O) : Prop := {
  jump_total : forall p n st, exists st', jump_effect C p n st st';
  atom_progress : forall a st,
    (exists l st', atom_step C a st l st') \/ atom_trap C a st \/ atom_stop C a st;
  atom_trap_halts : forall a st, atom_trap C a st -> ~ (exists l st', atom_step C a st l st');
  atom_stop_halts : forall a st, atom_stop C a st -> ~ (exists l st', atom_step C a st l st');
  atom_trap_not_stop : forall a st, ~ (atom_trap C a st /\ atom_stop C a st)
}.
Inductive frame : Type := FSeq (p : position) | FJoin (p : position)
  | FBlock (p : position) | FLoop (p : position).   (* p is the owner statement *)
Inductive mstate (St : Type) : Type :=
  | Go (p : position) (k : list frame) (st : St)    (* about to run the statement at p *)
  | Ret (p : position) (k : list frame) (st : St).  (* the statement at p has completed *)
Fixpoint resume {St} (n : nat) (k : list frame) (st : St) : option (mstate St).
(* resume n nil st = None;  resume n (FSeq _ :: k) st = resume n k st;
   resume n (FJoin _ :: k) st = resume n k st;
   for FBlock b :: k: n = 0 gives Some (Ret b k st), n = S n' gives resume n' k st;
   for FLoop b :: k:  n = 0 gives Some (Go (b ++ [DBody]) (FLoop b :: k) st), n = S n' as above *)
Inductive skel_step {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    mstate St -> list O -> mstate St -> Prop :=
  | step_atom : forall p k st a l st', sub prog p = Some (Atom a) -> atom_step C a st l st' ->
      skel_step prog C (Go p k st) l (Ret p k st')
  | step_seq : forall p k st s1 s2, sub prog p = Some (Seq s1 s2) ->
      skel_step prog C (Go p k st) nil (Go (p ++ [DFirst]) (FSeq p :: k) st)
  | step_if : forall p k st g s1 s2 b, sub prog p = Some (If g s1 s2) ->
      guard_bool C g st = Some b ->
      skel_step prog C (Go p k st) nil (Go (p ++ [if b then DFirst else DSecond]) (FJoin p :: k) st)
  | step_block : forall p k st s, sub prog p = Some (Block s) ->
      skel_step prog C (Go p k st) nil (Go (p ++ [DBody]) (FBlock p :: k) st)
  | step_loop : forall p k st s, sub prog p = Some (Loop s) ->
      skel_step prog C (Go p k st) nil (Go (p ++ [DBody]) (FLoop p :: k) st)
  | step_jump : forall p k st n st' m, sub prog p = Some (Jump n) ->
      jump_effect C p n st st' -> resume n k st' = Some m -> skel_step prog C (Go p k st) nil m
  | step_jump_if_taken : forall p k st g n st' m, sub prog p = Some (JumpIf g n) ->
      guard_bool C g st = Some true -> jump_effect C p n st st' -> resume n k st' = Some m ->
      skel_step prog C (Go p k st) nil m
  | step_jump_if_skipped : forall p k st g n, sub prog p = Some (JumpIf g n) ->
      guard_bool C g st = Some false -> skel_step prog C (Go p k st) nil (Ret p k st)
  | step_jump_table : forall p k st g ns n i st' m, sub prog p = Some (JumpTable g ns n) ->
      guard_index C g st = Some i -> jump_effect C p (nth i ns n) st st' ->
      resume (nth i ns n) k st' = Some m -> skel_step prog C (Go p k st) nil m
  | step_ret_seq : forall c p k st,
      skel_step prog C (Ret c (FSeq p :: k) st) nil (Go (p ++ [DSecond]) (FJoin p :: k) st)
  | step_ret_join : forall c p k st, skel_step prog C (Ret c (FJoin p :: k) st) nil (Ret p k st)
  | step_ret_block : forall c p k st, skel_step prog C (Ret c (FBlock p :: k) st) nil (Ret p k st)
  | step_ret_loop : forall c p k st,
      skel_step prog C (Ret c (FLoop p :: k) st) nil (Go (p ++ [DBody]) (FLoop p :: k) st).
(* The library-owned semantics: initial states are `Go nil nil st` with `init_store C st`. *)
Definition skeleton_semantics {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  semantics (mstate St) O.
Definition store_of {St} (m : mstate St) : St.   (* the st of either constructor *)
Definition stack_of {St} (m : mstate St) : list frame.   (* the k of either constructor *)
(* final: Ret nil nil st. trapped: Go p k st with sub prog p = Some (Atom a) and atom_trap C a st,
   or a guard evaluating to None at an If, JumpIf or JumpTable. stopped: atom_stop. *)
Definition skeleton_endings {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  endings (mstate St).
```

```coq
(* ViewsStructured.v *)
Inductive skel_point : Type := PEntry (p : position) | PExit (p : position).
Definition skel_point_encoding : encoding skel_point.
(* the code of PEntry p is that of inl p in sum_encoding position_encoding position_encoding, and
   of PExit p that of inr p *)
Inductive action (A G : Type) : Type :=            (* what one edge does to the client store *)
  | AAtom (a : A)
  | AGuard (g : G) (b : bool)
  | AIndexIs (g : G) (i : nat)
  | AIndexAtLeast (g : G) (len : nat)
  | AJump (p : position) (n : nat).                (* the jump statement at p leaves for depth n *)
(* An edge is its source and its slot among the edges that leave the source; its target and
   actions are functions of the program (skel_to and skel_acts below), so an edge is a small key and
   never carries the program's atoms or guards. A and G are phantom: they tie an edge to the type of
   the program it belongs to. *)
Record skel_edge (A G : Type) : Type := SkelEdge {
  from : skel_point;
  slot : nat
}.
Definition skel_edge_encoding {A G} : encoding (skel_edge A G).
(* the code of SkelEdge v i is that of (v, i) in pair_encoding skel_point_encoding nat_encoding *)
(* The client's store change of one action, and of a list of actions in sequence. *)
Definition act_hold {A G St O} (C : skeleton_client A G St O) :
  action A G -> St -> list O -> St -> Prop.
(* act_hold C (AAtom a) st l st' := atom_step C a st l st'
   act_hold C (AGuard g b) st l st' := guard_bool C g st = Some b /\ l = nil /\ st' = st
   act_hold C (AIndexIs g i) st l st' := guard_index C g st = Some i /\ l = nil /\ st' = st
   act_hold C (AIndexAtLeast g len) st l st' :=
     (exists j, guard_index C g st = Some j /\ len <= j) /\ l = nil /\ st' = st
   act_hold C (AJump p n) st l st' := jump_effect C p n st st' /\ l = nil *)
Inductive acts_hold {A G St O} (C : skeleton_client A G St O) :
    list (action A G) -> St -> list O -> St -> Prop :=
  | holds_nil : forall st, acts_hold C nil st nil st
  | holds_cons : forall x xs st l1 st1 l2 st2,
      act_hold C x st l1 st1 -> acts_hold C xs st1 l2 st2 ->
      acts_hold C (x :: xs) st (l1 ++ l2) st2.
Definition label_point {A G} (prog : stmt A G) (p : position) (n : nat) : option skel_point.
(* The n-th enclosing label of p, innermost first, counting the Block and Loop statements at the
   proper prefixes b of p: Some (PExit b) for a Block, Some (PEntry (b ++ [DBody])) for a Loop;
   None when fewer than n + 1 labels enclose p. It agrees with `resume` on the frames of p. *)
Definition skel_out {A G} (prog : stmt A G) (v : skel_point) :
  list (skel_point * list (action A G)).
(* The edges that leave v, as (target, actions), in this order; p.d is p ++ [d]. A jump whose
   label does not exist has no edge. For v = PEntry p, by the statement at p:
     Atom a        PExit p [AAtom a]
     Seq           PEntry p.DFirst []
     If g          PEntry p.DFirst [AGuard g true];  PEntry p.DSecond [AGuard g false]
     Block, Loop   PEntry p.DBody []
     Jump n        label_point prog p n [AJump p n]
     JumpIf g n    label_point prog p n [AGuard g true; AJump p n];  PExit p [AGuard g false]
     JumpTable g ns n
                   for i < length ns, in order: label_point prog p (nth i ns n)
                     [AIndexIs g i; AJump p (nth i ns n)];
                   then label_point prog p n [AIndexAtLeast g (length ns); AJump p n]
   For v = PExit q with q = p.d, by the statement at p and the direction d:
     Seq, d = DFirst   PEntry p.DSecond []      Seq, d = DSecond   PExit p []
     If                PExit p []               Block              PExit p []
     Loop              PEntry p.DBody []
   and nothing for PExit nil. *)
Definition skel_nodes {A G} (prog : stmt A G) : list skel_point :=
  flat_map (fun p => [PEntry p; PExit p]) (positions prog).
Definition skel_to {A G} (prog : stmt A G) (e : skel_edge A G) : skel_point :=
  match nth_error (skel_out prog (from e)) (slot e) with Some (t, _) => t | None => from e end.
Definition skel_acts {A G} (prog : stmt A G) (e : skel_edge A G) : list (action A G) :=
  match nth_error (skel_out prog (from e)) (slot e) with Some (_, a) => a | None => nil end.
Definition skeleton_graph {A G} (prog : stmt A G) : Graph.t skel_point (skel_edge A G).
(* Graph.entries = [PEntry nil]; Graph.nodes = skel_nodes prog;
   Graph.out v = map (fun i => SkelEdge v i) (seq 0 (length (skel_out prog v)));
   Graph.source = from; Graph.target = skel_to prog *)
Definition skeleton_view {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  graph_view (mstate St) O skel_point (skel_edge A G).
(* point (Go p _ _) = PEntry p; point (Ret p _ _) = PExit p; cfg = skeleton_graph prog;
   taken m l m' e := In e (Graph.out (skeleton_graph prog) (point m)) /\
     point m' = Graph.target (skeleton_graph prog) e /\
     acts_hold C (skel_acts prog e) (store_of m) l (store_of m');
   stays := fun _ _ _ => False *)
Definition loop_heads {A G} (prog : stmt A G) : list skel_point.
(* PEntry (p ++ [DBody]) for every p with sub prog p = Some (Loop _), in pre-order of p *)
Definition is_loop_head {A G} (prog : stmt A G) (n : skel_point) : bool.
(* true iff n = PEntry (p ++ [DBody]) with sub prog p = Some (Loop _): test the last direction and
   the statement at the rest of the position *)
(* The endings, seen from a position: the guard or atom at p traps (stops) in store st. *)
Definition traps_at {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    (p : position) (st : St) : Prop := trapped (skeleton_endings prog C) (Go p nil st).
Definition stops_at {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    (p : position) (st : St) : Prop := stopped (skeleton_endings prog C) (Go p nil st).
(* A store agreement lifted to machine states: only the store is compared. *)
Definition store_agreement {Fa St} (Ra : agreement Fa St) : agreement Fa (mstate St) :=
  Agreement (fun a m n => agree Ra a (store_of m) (store_of n)).

(* Generators over program points: the dense generators on the skeleton graph. The client gives
   one transfer per action; an edge applies its actions in order (forward) or last-to-first
   (backward). *)
Definition skel_root (n : skel_point) : bool :=
  match n with PEntry nil => true | _ => false end.
Definition edge_fwd {A G Fa} (prog : stmt A G) (act : action A G -> Fa -> Fa)
    (e : skel_edge A G) (f : Fa) : Fa :=
  fold_left (fun f x => act x f) (skel_acts prog e) f.
Definition edge_bwd {A G Fa} (prog : stmt A G) (actb : action A G -> Fa -> Fa)
    (e : skel_edge A G) (f : Fa) : Fa :=
  fold_right actb f (skel_acts prog e).
Definition skeleton_forward {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) :
    System.t skel_point (dense_constraint skel_point (skel_edge A G)) Fa :=
  forward_system (skeleton_graph prog) (fun n => if skel_root n then init else bot L)
    (edge_fwd prog act).
Definition skeleton_forward_static {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) : System.static (skeleton_forward L prog init act) :=
  forward_static (skeleton_graph prog) (fun n => if skel_root n then init else bot L)
    (edge_fwd prog act).
Definition skeleton_backward {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) :
    System.t skel_point (dense_constraint skel_point (skel_edge A G)) Fa :=
  backward_system (skeleton_graph prog) exitf (edge_bwd prog actb).
Definition skeleton_backward_static {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) : System.static (skeleton_backward prog exitf actb) :=
  backward_static (skeleton_graph prog) exitf (edge_bwd prog actb).
```

### VIEW-3: region summaries

```coq
(* ViewsRegion.v: bottom-up folds over the skeleton. *)
Record summary_algebra (A G R : Type) : Type := SummaryAlgebra {
  on_atom : A -> R;
  on_seq : R -> R -> R;
  on_if : G -> R -> R -> R;
  on_block : R -> R;
  on_loop : R -> R;
  on_jump : nat -> R;
  on_jump_if : G -> nat -> R;
  on_jump_table : G -> list nat -> nat -> R
}.
Fixpoint summarise {A G R} (alg : summary_algebra A G R) (s : stmt A G) : R.
(* the evident fold: summarise alg (Seq s1 s2) = on_seq alg (summarise alg s1) (summarise alg s2) *)
(* An algebra is sound for a meaning when every constructor's rule preserves the meaning. *)
Record algebra_sound {A G R} (alg : summary_algebra A G R) (meaning : stmt A G -> R -> Prop) :
    Prop := {
  sound_atom : forall a, meaning (Atom a) (on_atom alg a);
  sound_seq : forall s1 s2 r1 r2,
    meaning s1 r1 -> meaning s2 r2 -> meaning (Seq s1 s2) (on_seq alg r1 r2);
  sound_if : forall g s1 s2 r1 r2,
    meaning s1 r1 -> meaning s2 r2 -> meaning (If g s1 s2) (on_if alg g r1 r2);
  sound_block : forall s r, meaning s r -> meaning (Block s) (on_block alg r);
  sound_loop : forall s r, meaning s r -> meaning (Loop s) (on_loop alg r);
  sound_jump : forall n, meaning (Jump n) (on_jump alg n);
  sound_jump_if : forall g n, meaning (JumpIf g n) (on_jump_if alg g n);
  sound_jump_table : forall g ns n, meaning (JumpTable g ns n) (on_jump_table alg g ns n)
}.
(* Label inventory: the depths, relative to the region, of the labels it may jump to that lie
   outside it. *)
Definition escapes {A G} (s : stmt A G) : list nat.
(* Atom _ = nil; Seq and If: the concatenation of the children; Jump n = [n]; JumpIf _ n = [n];
   JumpTable _ ns n = n :: ns; Block s and Loop s = lower (escapes s), where lower drops 0 and
   decrements the rest *)
(* Normal completion: can control reach the end of the region without jumping? `ok a` says
   whether the atom a can complete. *)
Definition falls {A G} (ok : A -> bool) (s : stmt A G) : bool.
(* Atom a = ok a; Seq = both children fall; If = either child falls; Jump and JumpTable = false;
   JumpIf = true; Loop _ = false; Block s = falls s || (0 is in escapes s) *)
Definition falls_at {A G} (ok : A -> bool) (prog : stmt A G) (p : position) : bool :=
  match sub prog p with Some s => falls ok s | None => false end.
Fixpoint nesting {A G} (s : stmt A G) : nat.      (* the deepest chain of enclosing labels *)
(* nesting (Block s) = S (nesting s) and nesting (Loop s) = S (nesting s);
   nesting (Seq s1 s2) = max (nesting s1) (nesting s2), likewise If; every other statement 0 *)
Fixpoint skel_depth {A G} (s : stmt A G) : nat.   (* the deepest chain of enclosing statements *)
(* skel_depth of Atom, Jump, JumpIf and JumpTable is 0; skel_depth (Block s) = S (skel_depth s),
   likewise Loop; skel_depth (Seq s1 s2) = S (max (skel_depth s1) (skel_depth s2)), likewise If.
   Positions and frame stacks are at most skel_depth long. *)
(* A balanced block. Positions are the keys of the engine's unknowns, so a long straight-line
   block must not be a right-nested chain of Seq. `seq_of_list s ss` is the statements s :: ss in
   order as a balanced tree of Seq: one statement is itself, and n >= 2 statements split into the
   first n / 2 and the rest, each built the same way. A Seq is not a label, so no jump depth
   changes. `seq_flat` lists the statements left of the Seq spine: it flattens every Seq. *)
Fixpoint seq_flat {A G} (s : stmt A G) : list (stmt A G).
(* seq_flat (Seq s1 s2) = seq_flat s1 ++ seq_flat s2; seq_flat s = [s] for every other statement *)
Definition seq_of_list {A G} (s : stmt A G) (ss : list (stmt A G)) : stmt A G.
```

### VIEW-4: the SSA view and the sparse conditional generator

```coq
(* ViewsSsa.v. K is the client's operation type; C its concrete values. One environment per
   state: a language with calls states this view over its activation semantics, where a call is
   one step that assigns an arbitrary result. EX-5c lifts reachability and traces, callee events
   included, from activations to the frames of the full semantics, so behaviour results transfer.
   The dominated-use lemmas below are false for supergraph dominance under recursion, so the graph
   is the intraprocedural one. *)
Inductive definition (N V K : Type) : Type :=
  | Op (o : K) (args : list V)
  | Param (b : N) (i : nat)          (* the i-th parameter (phi) of block b *)
  | Arbitrary.                       (* any value: a load, a call result, an input *)
Inductive guard_kind (C : Type) : Type :=
  | GTrue | GFalse | GConst (c : C) | GNotConst (c : C).
Record condition (V C : Type) : Type := Condition { subject : V; kind : guard_kind C }.
Record ssa_view (S O N E V K C : Type) : Type := SsaView {
  base : graph_view S O N E;             (* the graph view; its nodes are blocks *)
  def : V -> definition N V K;
  home : V -> N;                         (* the block that defines the value *)
  params : N -> list V;                  (* the parameter values of a block, in order *)
  edge_args : E -> list V;               (* argument i is passed to parameter i of the target *)
  edge_guard : E -> list (condition V C);(* what holds along the edge: a conjunction *)
  val : S -> V -> option C;              (* the current value, None before it is defined *)
  op_eval : K -> list C -> option C;     (* None: the operation traps or is undefined *)
  truth : C -> bool
}.
Definition holds_guard {C} (truth : C -> bool) (k : guard_kind C) (c : C) : Prop :=
  match k with
  | GTrue => truth c = true
  | GFalse => truth c = false
  | GConst c0 => c = c0
  | GNotConst c0 => c <> c0
  end.
Definition cond_holds {S O N E V K C} (sv : ssa_view S O N E V K C) (s : S) (cd : condition V C) :
    Prop :=
  exists c, val sv s (subject cd) = Some c /\ holds_guard (truth sv) (kind cd) c.
(* Operand consistency of the guards of an edge in a state: every guard subject that is an
   operation holds the result of its operation on the current values of its arguments. *)
Definition guard_ops_consistent {S O N E V K C} (sv : ssa_view S O N E V K C) (s : S) (e : E) :
    Prop :=
  forall cd o args, In cd (edge_guard sv e) -> def sv (subject cd) = Op o args ->
    exists cs c, Forall2 (fun y d => val sv s y = Some d) args cs /\
      val sv s (subject cd) = Some c /\ op_eval sv o cs = Some c.
Record ssa_view_laws {S O N E V K C} (m : semantics S O) (sv : ssa_view S O N E V K C) : Prop := {
  base_laws : graph_view_laws m (base sv);
  param_defs : forall x b i, def sv x = Param b i -> nth_error (params sv b) i = Some x;
  guards_ok : forall s l s' e, reachable_state m s -> step m s l s' -> taken (base sv) s l s' e ->
    Forall (cond_holds sv s) (edge_guard sv e);
  (* when an edge is taken, its guard subjects hold the results of their operations on the
     current values of their arguments: a block computes its comparison from the values it holds *)
  guard_op_defined : forall s l s' e, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> guard_ops_consistent sv s e;
  (* a value that gets a new binding is computed from the previous state, received along the
     taken edge, or arbitrary *)
  value_origin : forall s l s' x c, reachable_state m s -> step m s l s' ->
    val sv s' x = Some c -> val sv s x <> Some c ->
    (exists o args cs, def sv x = Op o args /\ Forall2 (fun y d => val sv s y = Some d) args cs
       /\ op_eval sv o cs = Some c) \/
    (exists e b i z, def sv x = Param b i /\ taken (base sv) s l s' e /\
       Graph.target (cfg (base sv)) e = b /\ nth_error (edge_args sv e) i = Some z /\
       val sv s z = Some c) \/
    def sv x = Arbitrary
}.

(* The domain a sparse analysis runs over. `assume_value` refines a fact by a guard on that
   value; `assume_args o b fs` refines the argument facts of a comparison `o` given that it
   returned the truth value b. Analyses builds one from a numeric domain of Domains, a bridge
   from the operators to Bits and a `top`. *)
Record sparse_domain (A C K : Type) : Type := SparseDomain {
  fact_lat : lattice A;
  fact_conc : concretisation A C;
  top_fact : A;
  op_abs : K -> list A -> A;
  assume_value : guard_kind C -> A -> A;
  assume_args : K -> bool -> list A -> list A
}.
Record sparse_domain_laws {A C K} (D : sparse_domain A C K) (truth : C -> bool)
    (op_eval : K -> list C -> option C) : Prop := {
  dom_lattice : lattice_laws (fact_lat D);
  dom_conc : concretisation_laws (fact_lat D) (fact_conc D);
  fact_bot_empty : forall c, ~ gamma (fact_conc D) (bot (fact_lat D)) c;
  top_sound : forall c, gamma (fact_conc D) (top_fact D) c;
  op_sound : forall o fs cs c, Forall2 (gamma (fact_conc D)) fs cs -> op_eval o cs = Some c ->
    gamma (fact_conc D) (op_abs D o fs) c;
  assume_value_sound : forall k a c, gamma (fact_conc D) a c -> holds_guard truth k c ->
    gamma (fact_conc D) (assume_value D k a) c;
  assume_args_sound : forall o b fs cs c, Forall2 (gamma (fact_conc D)) fs cs ->
    op_eval o cs = Some c -> truth c = b ->
    Forall2 (gamma (fact_conc D)) (assume_args D o b fs) cs
}.
(* From Order (OrderLift.v): lift_bot A with the constructors Unreached and Reached a,
   lift_bot_lattice L with Unreached as bottom, and lift_bot_gamma G, where Unreached concretises
   to nothing. *)
Definition executable {A} (LB : lattice (lift_bot A)) (a : lift_bot A) : bool :=
  negb (leb LB a (bot LB)).

Inductive sparse_unknown (N E V : Type) : Type := UVal (x : V) | UEdge (e : E) | UBlock (b : N).
Definition sparse_unknown_encoding {N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V) :
  encoding (sparse_unknown N E V).
(* the codes of the sum V + (E + N): UVal x is inl x, UEdge e is inr (inl e), UBlock b is
   inr (inr b) *)
Inductive sparse_constraint (N E V : Type) : Type :=
  | CBlockEntry (b : N) | CEntryFact (x : V) | COp (x : V) | CArbitrary (x : V)
  | CArg (e : E) (i : nat) | CEdge (e : E) | CBlock (e : E).
Definition sparse_constraint_encoding {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) : encoding (sparse_constraint N E V).
(* the codes of the sum N + (V + (V + (V + ((E * nat) + (E + E))))), constructors in order:
   CBlockEntry b is inl b, CEntryFact x is inr (inl x), ..., and CBlock e is
   inr (inr (inr (inr (inr (inr e))))) *)
Record sparse_problem (S O N E V K C A : Type) : Type := SparseProblem {
  view : ssa_view S O N E V K C;
  domain : sparse_domain A C K;
  sparse_values : list V;     (* every value that can be defined, each once *)
  entry_fact : V -> A         (* the fact for a parameter of an entry block *)
}.
Definition sparse_system {S O N E V K C A} (pr : sparse_problem S O N E V K C A) :
  System.t (sparse_unknown N E V) (sparse_constraint N E V) (lift_bot A).
(* One carrier, lift_bot A, serves values, edges and blocks; an edge or block is executable
   when its unknown is not Unreached. With g = cfg (base (view pr)) and D = domain pr, the
   constraints, their targets and the values `Query.eval (System.rhs c) s` are:
   CBlockEntry b, b in entries g      UBlock b          Reached (top_fact D)
   CEntryFact x, def x = Param b _,
     b in entries g                   UVal x            Reached (entry_fact pr x)
   COp x, def x = Op o args           UVal x            Unreached if some s (UVal y) is Unreached,
                                                        else Reached (op_abs D o (facts of args))
   CArbitrary x, def x = Arbitrary    UVal x            Reached (top_fact D)
   CArg e i, y = nth i (params (target e)),
     z = nth i (edge_args e)          UVal y            if UEdge e is executable then
                                                        refine_on_edge pr s e z else Unreached
   CEdge e                            UEdge e           Reached (top_fact D) if UBlock (source e)
                                                        is executable and edge_feasible pr s e,
                                                        else Unreached
   CBlock e                           UBlock (target e) s (UEdge e)
   The constraints list covers every x in `sparse_values pr`, every e in `edges_of g`, and every
   i below the length of edge_args e. `Query.sides` is nil everywhere. *)
Definition sparse_static {S O N E V K C A} (pr : sparse_problem S O N E V K C A) :
  System.static (sparse_system pr).
(* deps lists the unknowns each row reads, including those read by refine_on_edge and
   edge_feasible: the facts of the guard subjects of the edge and of their arguments *)
```

```coq
(* ViewsRefine.v: argument refinement on edges and guard back-propagation. *)
Definition refine_fact {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (s : sparse_unknown N E V -> lift_bot A) (e : E) (z : V) (a0 : lift_bot A) : lift_bot A.
(* If a0 is Unreached, or the fact of a value that a condition below reads is Unreached, the
   result is Unreached. Otherwise fold over edge_guard e in order, starting with a = a0 and, for
   each Condition y k:
   - y = z: a := assume_value D k a;
   - def y = Op o args, z occurs in args at position j, k is GTrue or GFalse: with
     fs the facts of args (a at every position holding z) and b = (k = GTrue),
     a := nth j (assume_args D o b fs) a.
   The result is Reached a. The start fact is a parameter so that the fold of several edges can
   feed one result into the next. *)
Definition refine_on_edge {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (s : sparse_unknown N E V -> lift_bot A) (e : E) (z : V) : lift_bot A :=
  refine_fact pr s e z (s (UVal z)).
Definition edge_feasible {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (s : sparse_unknown N E V -> lift_bot A) (e : E) : bool.
(* true iff for every condition cd in edge_guard e the fact refine_on_edge pr s e (subject cd)
   is Reached a with not (leb (fact_lat D) a (bot (fact_lat D))) *)
```

### VIEW-5: dominated uses

```coq
(* ViewsDominated.v *)
(* From Graph (GRA-2): `dominates g d n` (every entry path to n visits d), `strictly_dominates`
   and `edge_dominates g e n` (every entry path to n contains the edge e), over `path g n es n'`. *)
(* Strict SSA: a value changes only where it is defined; a guard value is defined in a block that
   dominates the guarded edge's source; and the arguments of an operation are defined in blocks
   that dominate its block. With `guard_op_defined` this gives the one SSA equation lemma,
   `dominated_guard_holds`, on which sparse refinement at dominated uses and the analyses that
   read operand values at dominated uses rest. *)
Record strict_ssa_laws {S O N E V K C} (m : semantics S O) (sv : ssa_view S O N E V K C) : Prop := {
  redefine_in_stay : forall s l s' x, reachable_state m s -> step m s l s' ->
    stays (base sv) s l s' -> val sv s' x <> val sv s x -> point (base sv) s = home sv x;
  redefine_on_edge : forall s l s' e x, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> val sv s' x <> val sv s x -> home sv x = point (base sv) s';
  guard_home : forall e cd, In e (edges_of (cfg (base sv))) -> In cd (edge_guard sv e) ->
    dominates (cfg (base sv)) (home sv (subject cd)) (Graph.source (cfg (base sv)) e);
  op_args_dominate : forall x o args y, def sv x = Op o args -> In y args ->
    dominates (cfg (base sv)) (home sv y) (home sv x)
}.
(* Built once per graph, from the successor and predecessor indexes, the dominator tree and the
   dominating-edge index. The dominator tree is total: when the exactness checker rejects the
   tree, a flat tree stands in, so every query is sound and only its precision depends on the
   tree. *)
Record dom_context (N E : Type) : Type := DomContext {
  dc_graph : Graph.t N E;
  dc_encoding : encoding N;
  dc_prepared : prepared dc_encoding dc_graph;
  dc_tree : dom_tree N;
  dc_index : Map.t N E                    (* edge_dom_index of the tree *)
}.
Definition make_dom_context {N E} (EN : encoding N) (g : Graph.t N E) : dom_context N E.
(* prepare EN g; then dominator_tree of the prepared graph; then edge_dom_index of that tree *)
(* The edges that dominate b: the sole entering edge of every block on b's dominator chain, by one
   walk of the tree and no search. *)
Definition dominating_edges_in {N E} (ctx : dom_context N E) (b : N) : list E :=
  dominating_edges (dc_prepared ctx) (dc_tree ctx) (dc_index ctx) b.
(* The fact for z as read in block b: refine by every dominating edge, applying refinement at
   the read, with no extra nodes. The fold starts at the fact of z itself. *)
Definition refined_fact {S O N E V K C A} (ctx : dom_context N E)
    (pr : sparse_problem S O N E V K C A) (s : sparse_unknown N E V -> lift_bot A) (b : N)
    (z : V) : lift_bot A :=
  fold_left (fun a e => refine_fact pr s e z a) (dominating_edges_in ctx b) (s (UVal z)).
```

### VIEW-6: effects, calls, call graph, summaries

```coq
(* ViewsEffects.v. I is the client's instruction type. Booleans are over-approximations. `reads`
   is true when the step, the trap or the stop of the instruction may depend on the heap: a load,
   a store (its validity check), an allocation (the allocator's state) and a free. *)
Record effects (I : Type) : Type := Effects {
  reads : I -> bool;
  writes : I -> bool;
  may_trap : I -> bool;
  may_diverge : I -> bool;       (* a call that may not return, an unbounded operation *)
  may_stop : I -> bool;          (* may be stopped by resource exhaustion *)
  allocates : I -> bool;
  frees : I -> bool;
  calls : I -> bool;             (* may push or pop a frame *)
  observes : I -> bool           (* may emit an event *)
}.
Record effects_view (S I H : Type) : Type := EffectsView {
  instr_at : S -> option I;      (* the instruction the next step executes *)
  heap : S -> H;                 (* the memory image *)
  heap_agree : S -> S -> Prop;   (* the states differ at most in the heap *)
  depth : S -> nat               (* the number of frames *)
}.
CoInductive diverges_within {S O} (m : semantics S O) (depth : S -> nat) (d : nat) : S -> Prop :=
  | within_step : forall s l s', step m s l s' -> d <= depth s' -> diverges_within m depth d s' ->
      diverges_within m depth d s.
Record effects_laws {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) : Prop := {
  silent : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    observes ef i = false -> l = nil;
  trap_covered : forall s i, reachable_state m s -> instr_at ev s = Some i -> trapped en s ->
    may_trap ef i = true;
  stop_covered : forall s i, reachable_state m s -> instr_at ev s = Some i -> stopped en s ->
    may_stop ef i = true;
  heap_frame : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    writes ef i = false -> allocates ef i = false -> frees ef i = false -> heap ev s' = heap ev s;
  reads_frame : forall s l s' t i, reachable_state m s -> instr_at ev s = Some i ->
    step m s l s' -> reads ef i = false -> heap_agree ev s t ->
    exists t', step m t l t' /\ heap_agree ev s' t';
  trap_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    instr_at ev s = Some i -> instr_at ev t = Some i -> reads ef i = false ->
    heap_agree ev s t -> (trapped en s <-> trapped en t);
  stop_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    instr_at ev s = Some i -> instr_at ev t = Some i -> reads ef i = false ->
    heap_agree ev s t -> (stopped en s <-> stopped en t);
  frame_frame : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    calls ef i = false -> depth ev s' = depth ev s;
  call_returns : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    calls ef i = true -> may_diverge ef i = false -> depth ev s' = S (depth ev s) ->
    ~ diverges_within m (depth ev) (depth ev s') s'
}.
```

```coq
(* ViewsCalls.v *)
Record calls_view (S F P : Type) : Type := CallsView {
  functions : list F;
  roots : list F;                        (* functions an initial state may run *)
  sites_of : F -> list P;
  caller_of : P -> F;
  here : S -> F;                         (* the function of the innermost frame *)
  frames : S -> list (F * P)             (* suspended callers, innermost first, with their sites *)
}.
Definition active {S F P} (cv : calls_view S F P) (s : S) : list F :=
  here cv s :: map fst (frames cv s).
Record call_edge (F P : Type) : Type := CallEdge { edge_site : P; edge_callee : F }.
Definition call_graph {S F P} (cv : calls_view S F P) (resolve : P -> list F) :
  Graph.t F (call_edge F P).
(* Graph.entries = roots cv; Graph.nodes = functions cv;
   Graph.out f = flat_map (fun p => map (CallEdge p) (resolve p)) (sites_of cv f);
   Graph.source (CallEdge p g) = caller_of cv p; Graph.target (CallEdge p g) = g *)
Record calls_view_laws {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) : Prop := {
  sites_caller : forall f p, In p (sites_of cv f) -> caller_of cv p = f;
  initial_roots : forall s, initial m s -> In (here cv s) (roots cv) /\ frames cv s = nil;
  frames_listed : forall s, reachable_state m s -> forall f, In f (active cv s) ->
    In f (functions cv);
  step_shape : forall s l s', reachable_state m s -> step m s l s' ->
    (here cv s' = here cv s /\ frames cv s' = frames cv s) \/
    (exists p, In p (sites_of cv (here cv s)) /\ In (here cv s') (resolve p) /\
       frames cv s' = (here cv s, p) :: frames cv s) \/
    (exists f p, frames cv s = (f, p) :: frames cv s' /\ here cv s' = f)
}.
```

```coq
(* ViewsSummary.v. A summary describes the steps taken while a function is active, the steps of
   its callees included. *)
Record summary_spec (F P A : Type) : Type := SummarySpec {
  slat : lattice A;
  local : F -> A;                        (* the function's own steps *)
  via_call : P -> F -> A -> A            (* the callee's summary seen at the call site *)
}.
Record step_cover (S O A : Type) : Type := StepCover {
  step_covers : A -> S -> list O -> S -> Prop
}.
Inductive summary_constraint (F P : Type) : Type := SLocal (f : F) | SCall (p : P) (g : F).
Definition summary_constraint_encoding {F P} (EF : encoding F) (EP : encoding P) :
  encoding (summary_constraint F P).
(* the codes of the sum F + (P * F): SLocal f is inl f and SCall p g is inr (p, g) *)
Definition summary_system {S F P A} (cv : calls_view S F P) (resolve : P -> list F)
    (sp : summary_spec F P A) : System.t F (summary_constraint F P) A.
(* System.constraints = map SLocal (functions cv) ++ every SCall p g with p in sites_of cv f,
   f in functions cv, g in resolve p;
   System.target (SLocal f) = f, System.rhs (SLocal f) = Query.Ret (local sp f);
   System.target (SCall p g) = caller_of cv p,
   System.rhs (SCall p g) = Query.Ask g (fun a => Query.Ret (via_call sp p g a)) *)
Definition summary_static {S F P A} (cv : calls_view S F P) (resolve : P -> list F)
    (sp : summary_spec F P A) : System.static (summary_system cv resolve sp).
(* deps (SLocal _) = nil; deps (SCall p g) = [g]; side_targets _ = nil *)
Record summary_laws {S O F P A} (m : semantics S O) (cv : calls_view S F P)
    (sp : summary_spec F P A) (sc : step_cover S O A) : Prop := {
  covers_monotone : forall a b s l s', leb (slat sp) a b = true -> step_covers sc a s l s' ->
    step_covers sc b s l s';
  local_covers : forall s l s', reachable_state m s -> step m s l s' ->
    step_covers sc (local sp (here cv s)) s l s';
  call_covers : forall p g a s l s', reachable_state m s -> In (caller_of cv p, p) (frames cv s) ->
    step_covers sc a s l s' -> step_covers sc (via_call sp p g a) s l s'
}.
```

### VIEW-7: memory

```coq
(* ViewsMemory.v. V values, C concrete values, L allocation identities, T allocation sites.
   `footprint` and `covered` are those of Domains (DOM-6): a footprint is an allocation site with
   a range of byte offsets, and `covered F t o w` says that the w bytes at offset o of a block
   allocated at site t lie in the union of the ranges of F. *)
Inductive mem_op (V T : Type) : Type :=
  | MemLoad (base : V) (off : Z) (width : nat)
  | MemStore (base : V) (off : Z) (width : nat) (src : V)
  | MemCopy (dst src len : V)
  | MemFill (dst len : V)
  | MemAlloc (site : T) (size : V)
  | MemFree (ptr : V).
Record mem_view (S V C L T : Type) : Type := MemView {
  mem_instr : S -> option (mem_op V T);  (* the memory operation the next step executes *)
  loc_of : S -> C -> option L;           (* the allocation that a pointer value points into *)
  loc_site : S -> L -> option T;         (* the allocation site of an allocation *)
  loc_offset : S -> C -> Z               (* the byte offset of a pointer value in its allocation *)
}.
Record mem_view_laws {S O V C L T} (m : semantics S O) (mv : mem_view S V C L T) : Prop := {
  site_stable : forall s l s' l0 t, reachable_state m s -> step m s l s' ->
    loc_site mv s l0 = Some t -> loc_site mv s' l0 = Some t
}.
(* An abstract pointer: which sites, and which start offsets inside them, it may denote. A
   footprint of ptr_reach holds start offsets, both ends included. *)
Record pointer_domain (P C T : Type) : Type := PointerDomain {
  ptr_lat : lattice P;
  ptr_conc : concretisation P C;
  ptr_reach : P -> list (footprint T)
}.
(* The bytes that an access of width w at offset off from a pointer may touch. *)
Definition access_footprint {P C T} (pd : pointer_domain P C T) (p : P) (off : Z) (w : nat) :
    list (footprint T) :=
  map (fun f => Footprint (fp_site f) (fp_lo f + off) (fp_hi f + off + Z.of_nat w))
    (ptr_reach pd p).
Record pointer_domain_laws {P S O C L V T} (m : semantics S O) (mv : mem_view S V C L T)
    (pd : pointer_domain P C T) : Prop := {
  ptr_reach_sound : forall s p c l t, reachable_state m s -> gamma (ptr_conc pd) p c ->
    loc_of mv s c = Some l -> loc_site mv s l = Some t ->
    exists f, In f (ptr_reach pd p) /\ fp_site f = t /\
      (fp_lo f <= loc_offset mv s c <= fp_hi f)%Z
}.
```

## Theorems

### VIEW-1

```coq
(** Bisimilar states have the same observable behaviour. *)
Theorem bisimilar_same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) (s : S1) (t : S2) :
  bisimulation m1 e1 m2 e2 R -> R s t -> same_behaviour m1 e1 s m2 e2 t.
(** Stuttering bisimilar states have the same observable behaviour. *)
Theorem stuttering_same_behaviour {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop) (mu1 mu2 : S1 -> S2 -> nat)
    (s : S1) (t : S2) :
  stuttering m1 e1 m2 e2 R mu1 mu2 -> R s t -> same_behaviour m1 e1 s m2 e2 t.
```
Proof idea: the first is the second with the empty silent run and no stutter (a bisimulation is a
stuttering bisimulation). For the second, finish and prefix are by induction on the `exec` of one
program, generalising the related state: a step of the run is a stutter, which keeps the other
state, or a match, whose silent run is prepended to the other program's run. Divergence after a
prefix is by induction on the run to the prefix, then coinduction with an inner well-founded
induction on the measure that skips the stutters before the first matched step. At a finite run's
endpoint, `st_ends_forth` or `st_ends_back` supplies the silent matching run and the same ending,
including `EndStuck`. This explicit obligation avoids deciding whether a transition exists.
Card: VIEW-1.

```coq
(** Observable behaviour is symmetric and transitive, so it can be chained through a toy's
    reference semantics. *)
Theorem same_behaviour_sym {S1 S2 O} (m1 : semantics S1 O) (e1 : endings S1) (s : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (t : S2) :
  same_behaviour m1 e1 s m2 e2 t -> same_behaviour m2 e2 t m1 e1 s.
Theorem same_behaviour_trans {S1 S2 S3 O} (m1 : semantics S1 O) (e1 : endings S1) (s : S1)
    (m2 : semantics S2 O) (e2 : endings S2) (t : S2) (m3 : semantics S3 O) (e3 : endings S3)
    (u : S3) :
  same_behaviour m1 e1 s m2 e2 t -> same_behaviour m2 e2 t m3 e3 u ->
  same_behaviour m1 e1 s m3 e3 u.
```
Proof idea: each component is an `iff`; compose them. Card: VIEW-1.

```coq
(** A run inside a set of states is a run, and runs inside a set concatenate. *)
Theorem exec_in_exec {S O} (m : semantics S O) (P : S -> Prop) (s t : S) (tr : list O) :
  exec_in m P s tr t -> exec m s tr t.
Theorem exec_in_app {S O} (m : semantics S O) (P : S -> Prop) (s u t : S) (tr1 tr2 : list O) :
  exec_in m P s tr1 u -> exec_in m P u tr2 t -> exec_in m P s (tr1 ++ tr2) t.
(** Reachability is an inductive invariant. *)
Theorem reachable_invariant {S O} (m : semantics S O) : invariant_of m (reachable_state m).
```
Proof idea: induction on the first run; a step from a reachable state extends its run by
`exec_step`. Card: VIEW-1.

```coq
(** A forward post-solution is exactly a seed bound plus one inequality per edge. *)
Theorem forward_post_solution_iff {N E A} (g : Graph.t N E) (L : lattice A) (init : N -> A)
    (ft : E -> A -> A) (sigma : N -> A) :
  post_solution L (forward_system g init ft) sigma <->
  (forall n, In n (Graph.entries g) -> leb L (init n) (sigma n) = true) /\
  (forall e, In e (edges_of g) ->
     leb L (ft e (sigma (Graph.source g e))) (sigma (Graph.target g e)) = true).
(** The same for the backward system: a seed at every node and one inequality per edge. *)
Theorem backward_post_solution_iff {N E A} (g : Graph.t N E) (L : lattice A) (exitf : N -> A)
    (bt : E -> A -> A) (sigma : N -> A) :
  post_solution L (backward_system g exitf bt) sigma <->
  (forall n, In n (Graph.nodes g) -> leb L (exitf n) (sigma n) = true) /\
  (forall e, In e (edges_of g) ->
     leb L (bt e (sigma (Graph.target g e))) (sigma (Graph.source g e)) = true).
```
Proof idea: unfold `post_solution`; the rhs trees are `Query.Ret` and `Query.Ask`, so `Query.sides`
is empty and `Query.eval` computes. Card: VIEW-1.

```coq
(** A node set that meets every cycle of the graph cuts every cycle of the forward system and of
    the backward system, so it is a valid set of widening points for either. *)
Theorem forward_cuts_every_cycle {N E A} (g : Graph.t N E) (init : N -> A) (ft : E -> A -> A)
    (W : N -> bool) :
  graph_wf g -> meets_every_cycle g W -> cuts_every_cycle (forward_static g init ft) W.
Theorem backward_cuts_every_cycle {N E A} (g : Graph.t N E) (exitf : N -> A) (bt : E -> A -> A)
    (W : N -> bool) :
  graph_wf g -> meets_every_cycle g W -> cuts_every_cycle (backward_static g exitf bt) W.
```
Proof idea: a flow of the forward system is an edge of `g` from its source to its target
(`out_source` identifies the source), so a cycle of flows that never enters `W` is a cycle of `g`
none of whose nodes satisfies `W`, which `meets_every_cycle` forbids. The flows of the backward
system are the reversed edges, and a reversed cycle visits the same nodes. Card: VIEW-1.

```coq
(** A history is a run, and every run of a reachable state has a history. *)
Theorem run_edges_exec {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) :
  run_edges m gv s es t -> exists tr, exec m s tr t.
Theorem exec_run_edges {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (tr : list O) :
  graph_view_laws m gv -> reachable_state m s -> exec m s tr t -> exists es, run_edges m gv s es t.
(** A history is a path of the graph from the point of its start to the point of its end. *)
Theorem run_edges_path {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) :
  graph_view_laws m gv -> reachable_state m s -> run_edges m gv s es t ->
  path (cfg gv) (point gv s) es (point gv t).
(** Histories concatenate, and a history ends with one taken step followed by stays. *)
Theorem run_edges_app {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s u t : S)
    (es1 es2 : list E) :
  run_edges m gv s es1 u -> run_edges m gv u es2 t -> run_edges m gv s (es1 ++ es2) t.
Theorem run_edges_snoc_inv {S O N E} (m : semantics S O) (gv : graph_view S O N E) (s t : S)
    (es : list E) (e : E) :
  run_edges m gv s (es ++ [e]) t <->
  exists s1 l s2, run_edges m gv s es s1 /\ step m s1 l s2 /\ taken gv s1 l s2 e /\
    run_edges m gv s2 nil t.
(** The two counts over a history extend one edge at a time. *)
Theorem last_writer_snoc {E X} (writes : E -> X -> bool) (es : list E) (e : E) (x : X) :
  last_writer writes (es ++ [e]) x = if writes e x then Some e else last_writer writes es x.
Theorem arrivals_since_snoc {E} (enter back : E -> bool) (es : list E) (e : E) :
  arrivals_since enter back (es ++ [e]) =
  if enter e then 0 else if back e then S (arrivals_since enter back es)
  else arrivals_since enter back es.
```
Proof idea: induction on the history or on `exec`, classifying each step by `edge_covers`; the path
claim uses `taken_edge` and `out_source`; the two equations are `fold_left_app`. Card: VIEW-1.

```coq
(** Forward invariant: a post-solution and per-edge local soundness, relative to the fact that
    sigma assigns at the point, give a concretisation of sigma at the point of every reachable
    state. *)
Theorem forward_invariant_sound {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A S) (init : N -> A) (ft : E -> A -> A)
    (sigma : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G sigma) ->
  (forall s, initial m s -> gamma (G sigma) (init (point gv s)) s) ->
  (forall e s l s', reachable_state m s -> step m s l s' -> taken gv s l s' e ->
     gamma (G sigma) (sigma (point gv s)) s ->
     gamma (G sigma) (ft e (sigma (point gv s))) s') ->
  (forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
     gamma (G sigma) (sigma (point gv s)) s -> gamma (G sigma) (sigma (point gv s)) s') ->
  post_solution L (forward_system (cfg gv) init ft) sigma ->
  forall s, reachable_state m s -> gamma (G sigma) (sigma (point gv s)) s.
```
Proof idea: induction on `exec`; the covering edge comes from `edge_covers` and `taken_edge`, and
`out_source` gives `Graph.source e = point s`; the bound `ft e (sigma (source e)) <= sigma (target
e)`
is `forward_post_solution_iff`; the local premise turns the fact at the point into `ft e` of it and
`gamma_monotone` carries it to the target. Card: VIEW-1.

```coq
(** Forward facts can be premises of a backward theorem: reachability together with a forward
    solution is an inductive invariant. *)
Theorem forward_inv_invariant {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A S) (init : N -> A) (ft : E -> A -> A)
    (phi : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G phi) ->
  (forall s, initial m s -> gamma (G phi) (init (point gv s)) s) ->
  (forall e s l s', reachable_state m s -> step m s l s' -> taken gv s l s' e ->
     gamma (G phi) (phi (point gv s)) s -> gamma (G phi) (ft e (phi (point gv s))) s') ->
  (forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
     gamma (G phi) (phi (point gv s)) s -> gamma (G phi) (phi (point gv s)) s') ->
  post_solution L (forward_system (cfg gv) init ft) phi ->
  invariant_of m (forward_inv m gv (G phi) phi).
```
Proof idea: `forward_invariant_sound` for the facts, `exec_step` for closure, the first component
of `forward_inv` for `inv_reachable`. Card: VIEW-1.

```coq
(** Forward facts over histories: with a concretisation that sees the edges taken so far, a
    post-solution and per-edge local soundness give a concretisation of sigma at the point of
    every state reached by a history from an initial state, which covers reaching definitions
    (`last_writer`) and arrival counts (`arrivals_since`). *)
Theorem forward_history_sound {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A (S * list E)) (init : N -> A)
    (ft : E -> A -> A) (sigma : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G sigma) ->
  (forall s, initial m s -> gamma (G sigma) (init (point gv s)) (s, nil)) ->
  (forall e s0 es s l s', initial m s0 -> run_edges m gv s0 es s -> step m s l s' ->
     taken gv s l s' e -> gamma (G sigma) (sigma (point gv s)) (s, es) ->
     gamma (G sigma) (ft e (sigma (point gv s))) (s', es ++ [e])) ->
  (forall s0 es s l s', initial m s0 -> run_edges m gv s0 es s -> step m s l s' ->
     stays gv s l s' -> gamma (G sigma) (sigma (point gv s)) (s, es) ->
     gamma (G sigma) (sigma (point gv s)) (s', es)) ->
  post_solution L (forward_system (cfg gv) init ft) sigma ->
  forall s0 es s, initial m s0 -> run_edges m gv s0 es s ->
    gamma (G sigma) (sigma (point gv s)) (s, es).
```
Proof idea: induction on a history from a state `s_mid` already reached by the prefix `es_pre`,
with the invariant `gamma (sigma (point s_mid)) (s_mid, es_pre)`. `run_nil` ends. `run_cons`
extends the prefix by the edge: the local premise gives `ft e (sigma (point s_mid))` at the
successor, `taken_edge` and `out_source` identify the source of the edge with the point, and
`forward_post_solution_iff` with `gamma_monotone` carries the fact to `sigma` of the target.
`run_stay` keeps the prefix and uses the stay premise with `stays_point`. The history classifies
every step, so `edge_covers` is not needed. The base is the seed bound at the entry that
contains the initial point. Card: VIEW-1.

```coq
(** Agreement-bisimulation: a post-solution of a backward system, per-step agreement lemmas and
    agreement at the endings make "agree under sigma at the point" a lock-step bisimulation that
    preserves events, traps, stops and termination. *)
Theorem agreement_bisimulation {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S) (inv : S -> Prop)
    (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A) :
  graph_view_laws m gv -> agreement_laws L (R sigma) -> agreement_symmetric (R sigma) ->
  invariant_of m inv -> step_agrees m gv (R sigma) inv bt sigma ->
  ends_agree m en gv (R sigma) inv exitf ->
  post_solution L (backward_system (cfg gv) exitf bt) sigma ->
  bisimulation m en m en (agreeing gv (R sigma) inv sigma).
```
Proof idea: for `s` stepping along the covering edge `e`, the backward inequality at `e` and
`agree_antitone` weaken `agree (sigma (point s))` to `agree (bt e (sigma (target e)))`,
`step_agrees`
supplies the matching step along `e` that agrees at `sigma (target e)`, and `taken_edge` fixes both
points; `bisim_back` is `bisim_forth` on the symmetric pair; the endings follow from `ends_agree` at
the exit fact, which the seed of the post-solution puts below `sigma`, and the two directions of
stepping. Card: VIEW-1.

```coq
(** Two runs from initial states that agree under sigma at their common point have equal
    observable behaviour: the same finishes, the same finite traces, and the same traces after
    which they can diverge. *)
Theorem agreement_same_behaviour {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S) (inv : S -> Prop)
    (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A) (s0 t0 : S) :
  graph_view_laws m gv -> agreement_laws L (R sigma) -> agreement_symmetric (R sigma) ->
  invariant_of m inv -> step_agrees m gv (R sigma) inv bt sigma ->
  ends_agree m en gv (R sigma) inv exitf ->
  post_solution L (backward_system (cfg gv) exitf bt) sigma ->
  initial m s0 -> initial m t0 -> point gv t0 = point gv s0 ->
  agree (R sigma) (sigma (point gv s0)) s0 t0 ->
  same_behaviour m en s0 m en t0.
```
Proof idea: `agreement_bisimulation` with `inv_initial` for both states, then
`bisimilar_same_behaviour`. Card: VIEW-1.

```coq
(** Two-program agreement: an original program (m1, gv1) and its transform (m2, gv2), over one
    state type and one graph, that satisfy the per-edge and ending obligations in both directions
    under a post-solution of the original's backward system have the same observable behaviour
    from initial states that agree under sigma at their common point. *)
Theorem agreement_simulation2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (gv1 gv2 : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S)
    (inv1 inv2 : S -> Prop) (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A)
    (mu1 mu2 : S -> S -> nat) (s0 t0 : S) :
  graph_view_laws m1 gv1 -> graph_view_laws m2 gv2 -> cfg gv2 = cfg gv1 ->
  agreement_laws L (R sigma) -> invariant_of m1 inv1 -> invariant_of m2 inv2 ->
  step_agrees2 m1 m2 gv1 gv2 (R sigma) inv1 inv2 bt sigma mu1 mu2 ->
  ends_agree2 m1 m2 en1 en2 gv1 gv2 (R sigma) inv1 inv2 exitf ->
  post_solution L (backward_system (cfg gv1) exitf bt) sigma ->
  initial m1 s0 -> initial m2 t0 -> point gv2 t0 = point gv1 s0 ->
  agree (R sigma) (sigma (point gv1 s0)) s0 t0 ->
  same_behaviour m1 en1 s0 m2 en2 t0.
```
Proof idea: `agreeing2` is a stuttering bisimulation with the measures `mu1` and `mu2`. A step of
the
original is classified by `edge_covers` of `gv1`; along an edge `e`, `taken_edge`, `out_source` and
the backward inequality of the post-solution at `e` with `agree_antitone` weaken the agreement at
the point to the input fact of `e`, so `forth_agrees` applies and its matched state is related
(`inv_step` along the silent run keeps `inv2`). The steps of the transform are classified by
`gv2`, whose graph is `cfg gv1`, and the second half of `step_agrees2` is the same argument with
the roles and the agreement swapped (`agreement_swap` keeps the laws). All four endings, including
stuck, use the seed `exitf n <= sigma n` and the corresponding `ends_agree2` obligation; then
`stuttering_same_behaviour`. Card: VIEW-1.

### VIEW-2

```coq
(** The skeleton graph lists every valid position once. *)
Theorem positions_exact {A G} (prog : stmt A G) :
  NoDup (positions prog) /\
  (forall p, In p (positions prog) <-> exists s, sub prog p = Some s).
(** The skeleton view satisfies the graph-view laws for every program and client. *)
Theorem skeleton_view_laws_hold {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  graph_view_laws (skeleton_semantics prog C) (skeleton_view prog C).
```
Proof idea: the first by induction on the statement; for the second, reachable states keep
`stack_of m` equal to the frames of the ancestors of the position, so `resume` agrees with
`label_point`; then one covering edge per `skel_step` rule, with the actions of the edge folding to
the step's store change; `graph_wf` from `positions_exact` and the table. Card: VIEW-2.

```coq
(** The skeleton's endings are well formed for every client that satisfies its laws. *)
Theorem skeleton_endings_wf {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  skeleton_client_laws C -> endings_wf (skeleton_semantics prog C) (skeleton_endings prog C).
```
Proof idea: case analysis on the machine state and the rule that applies; a trapped or stopped
state has no rule because the rule needs the guard to evaluate or the atom to step. Card: VIEW-2.

```coq
(** A program with well-nested labels, run by a client that satisfies its laws, never reaches a
    stuck state. *)
Theorem skeleton_not_stuck {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  labels_ok 0 prog = true -> skeleton_client_laws C ->
  forall m, reachable_state (skeleton_semantics prog C) m ->
    ~ stuck (skeleton_semantics prog C) (skeleton_endings prog C) m.
```
Proof idea: `labels_ok` makes `resume` total on the frame invariant and `jump_total` supplies the
jump's store; every other state has a rule or is final, trapped or stopped by `atom_progress`.
Card: VIEW-2.

```coq
(** A post-solution of the skeleton's forward system describes every reachable machine state. *)
Theorem skeleton_forward_sound {A G St O Fa} (L : lattice Fa) (Gc : concretisation Fa St)
    (prog : stmt A G) (C : skeleton_client A G St O) (init : Fa)
    (act : action A G -> Fa -> Fa) (sigma : skel_point -> Fa) :
  concretisation_laws L Gc -> (forall st, init_store C st -> gamma Gc init st) ->
  (forall x f st l st', gamma Gc f st -> act_hold C x st l st' -> gamma Gc (act x f) st') ->
  post_solution L (skeleton_forward L prog init act) sigma ->
  forall m, reachable_state (skeleton_semantics prog C) m ->
    gamma Gc (sigma (point (skeleton_view prog C) m)) (store_of m).
```
Proof idea: `forward_invariant_sound` on the skeleton view with `G := fun _ => Gc`, with one `act`
premise per edge by folding `act_hold` over `skel_acts prog e`. Card: VIEW-2.

```coq
(** Backward soundness: a post-solution of the skeleton's backward system makes agreement of the
    stores a lock-step bisimulation of the skeleton machine with itself. *)
Theorem skeleton_agreement_bisimulation {A G St O Fa} (L : lattice Fa) (Ra : agreement Fa St)
    (prog : stmt A G) (C : skeleton_client A G St O) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) (sigma : skel_point -> Fa) :
  agreement_laws L Ra -> agreement_symmetric Ra ->
  (forall x a st1 l st1' st2, act_hold C x st1 l st1' -> agree Ra (actb x a) st1 st2 ->
     exists st2', act_hold C x st2 l st2' /\ agree Ra a st1' st2') ->
  (forall p st1 st2, agree Ra (exitf (PEntry p)) st1 st2 ->
     (traps_at prog C p st1 <-> traps_at prog C p st2) /\
     (stops_at prog C p st1 <-> stops_at prog C p st2)) ->
  post_solution L (skeleton_backward prog exitf actb) sigma ->
  bisimulation (skeleton_semantics prog C) (skeleton_endings prog C)
    (skeleton_semantics prog C) (skeleton_endings prog C)
    (agreeing (skeleton_view prog C) (store_agreement Ra)
       (reachable_state (skeleton_semantics prog C)) sigma).
```
Proof idea: `agreement_bisimulation` with `inv := reachable_state`; the per-step obligation folds
the
per-action lemma along `skel_acts prog e`, from the last action to the first, for the fact
`sigma (target e)` of the solution, and `ends_agree` comes from the trap and stop premise plus the
fact that final states do not look at the store. Card: VIEW-2.

```coq
(** Every cycle of the skeleton graph visits a loop head, so the loop heads are valid cut points,
    and they cut every cycle of both generators. *)
Theorem skeleton_cut_points {A G} (prog : stmt A G) :
  meets_every_cycle (skeleton_graph prog) (is_loop_head prog).
Theorem skeleton_forward_cuts {A G Fa} (L : lattice Fa) (prog : stmt A G) (init : Fa)
    (act : action A G -> Fa -> Fa) :
  cuts_every_cycle (skeleton_forward_static L prog init act) (is_loop_head prog).
Theorem skeleton_backward_cuts {A G Fa} (prog : stmt A G) (exitf : skel_point -> Fa)
    (actb : action A G -> Fa -> Fa) :
  cuts_every_cycle (skeleton_backward_static prog exitf actb) (is_loop_head prog).
Theorem is_loop_head_iff {A G} (prog : stmt A G) (n : skel_point) :
  is_loop_head prog n = true <-> In n (loop_heads prog).
```
Proof idea: every edge that is not a loop repeat or a jump to a Loop label goes forward in the order
"entry of a position, its subtrees left to right, exit of the position"; a closed walk therefore
uses a repeat or a jump to a Loop label, whose target is a loop head, and the closed walk also
leaves that node. The two cut theorems are `forward_cuts_every_cycle` and
`backward_cuts_every_cycle` with `graph_wf` from `skeleton_view_laws_hold`. Card: VIEW-2.

### VIEW-3

```coq
(** An algebra whose rules preserve a meaning has that meaning on every statement. *)
Theorem summarise_sound {A G R} (alg : summary_algebra A G R) (meaning : stmt A G -> R -> Prop) :
  algebra_sound alg meaning -> forall s, meaning s (summarise alg s).
```
Proof idea: structural induction on the statement. Card: VIEW-3.

```coq
(** A region may jump only to labels that exist: the label inventory is below the number of
    enclosing labels exactly when the check `labels_ok` passes. *)
Theorem escapes_labels_ok {A G} (d : nat) (s : stmt A G) :
  labels_ok d s = true <-> (forall n, In n (escapes s) -> n < d).
(** The depth of the label stack never exceeds the depth of the tree, and no position is longer
    than the depth of the tree. *)
Theorem nesting_le_skel_depth {A G} (s : stmt A G) : nesting s <= skel_depth s.
Theorem position_length_le_depth {A G} (s : stmt A G) (p : position) :
  In p (positions s) -> length p <= skel_depth s.
```
Proof idea: structural induction; `lower` decrements exactly the depths that cross a label; the
equations of `nesting` and `skel_depth` add one per label and per enclosing statement. Card: VIEW-3.

```coq
(** A balanced block keeps the statements and their order, and is shallow: its depth exceeds the
    depth of its deepest statement by at most the logarithm of its length. *)
Theorem seq_of_list_flat {A G} (s : stmt A G) (ss : list (stmt A G)) :
  seq_flat (seq_of_list s ss) = flat_map seq_flat (s :: ss).
Theorem seq_of_list_depth {A G} (s : stmt A G) (ss : list (stmt A G)) :
  skel_depth (seq_of_list s ss) <=
  Nat.log2_up (S (length ss)) + fold_right Nat.max 0 (map skel_depth (s :: ss)).
```
Proof idea: strong induction on the length `n` of the list; the halves have lengths `n / 2` and
`n - n / 2`, `seq_flat` of a `Seq` is the concatenation of those of its children, and
`Nat.log2_up n = S (Nat.log2_up (n - n / 2))` for `n >= 2` bounds the depth. Card: VIEW-3.

```coq
(** Normal completion: a reachable completion of the statement at p implies `falls_at`. *)
Theorem falls_sound {A G St O} (ok : A -> bool) (prog : stmt A G)
    (C : skeleton_client A G St O) :
  (forall a st l st', atom_step C a st l st' -> ok a = true) ->
  forall p k st, reachable_state (skeleton_semantics prog C) (Ret p k st) ->
    falls_at ok prog p = true.
(** The frame stack never grows past the depth of the program. *)
Theorem frames_bounded {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
  forall m, reachable_state (skeleton_semantics prog C) m ->
    length (stack_of m) <= skel_depth prog.
```
Proof idea: both by induction on `exec`, using the frame invariant of `skeleton_view_laws_hold`
(the frames of a state are those of the proper ancestors of its position, so their number is
`length p`, at most `skel_depth prog` by `position_length_le_depth`); a `Ret p` arises from an atom
step, a completing child, a skipped `JumpIf`, or a jump whose label depth is `0` in `escapes`.
Card: VIEW-3.

### VIEW-4

```coq
(** Refining a fact by the guards of an edge is sound in a state in which the guards hold and the
    guard subjects are consistent with their operations, and whose values the facts contain:
    whatever fact the refinement starts from, if it contains the value of z, so does the result. *)
Theorem refine_fact_sound {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) (s : S) (e : E) (z : V) (a0 : lift_bot A)
    (c : C) :
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  Forall (cond_holds (view pr) s) (edge_guard (view pr) e) ->
  guard_ops_consistent (view pr) s e ->
  (forall x d, val (view pr) s x = Some d ->
     gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  val (view pr) s z = Some c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) a0 c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) (refine_fact pr sigma e z a0) c.
(** The refinement that starts from the fact of z itself. *)
Theorem refine_on_edge_sound {S O N E V K C A} (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) (s : S) (e : E) (z : V) (c : C) :
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  Forall (cond_holds (view pr) s) (edge_guard (view pr) e) ->
  guard_ops_consistent (view pr) s e ->
  (forall x d, val (view pr) s x = Some d ->
     gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  val (view pr) s z = Some c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) (refine_on_edge pr sigma e z) c.
(** A taken edge is feasible under the same premises. *)
Theorem edge_feasible_sound {S O N E V K C A} (m : semantics S O)
    (pr : sparse_problem S O N E V K C A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  forall s l s' e, reachable_state m s -> step m s l s' -> taken (base (view pr)) s l s' e ->
    (forall x d, val (view pr) s x = Some d ->
       gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
    edge_feasible pr sigma e = true.
```
Proof idea: fold over the conditions. `assume_value_sound` handles a condition on `z`; for a
condition on a comparison `y` whose definition mentions `z`, `guard_ops_consistent` gives the
argument values at the state, the facts premise puts the facts of the other arguments around
them, the fold's accumulated fact stands for `z` at every position that holds it, and
`assume_args_sound` keeps every argument value in the refined facts. A start fact or an argument
fact that were Unreached would contain no value, which the premises exclude. For feasibility,
`guards_ok` and `guard_op_defined` give the premises at the source state of the taken edge, and
`fact_bot_empty` with `gamma_monotone` shows that the refined fact of a value that exists is not
below bottom. Card: VIEW-4.

```coq
(** Sparse conditional soundness: from a post-solution of the sparse system, every reachable
    state sits in an executable block, every taken edge is executable, and every defined value
    is in the concretisation of its fact. *)
Theorem sparse_sound {S O N E V K C A} (m : semantics S O) (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  (forall s x c, reachable_state m s -> val (view pr) s x = Some c -> In x (sparse_values pr)) ->
  (forall s x c, initial m s -> val (view pr) s x = Some c ->
     exists b i, def (view pr) x = Param b i /\ In b (Graph.entries (cfg (base (view pr)))) /\
       gamma (fact_conc (domain pr)) (entry_fact pr x) c) ->
  post_solution (lift_bot_lattice (fact_lat (domain pr))) (sparse_system pr) sigma ->
  (forall s, reachable_state m s ->
     executable (lift_bot_lattice (fact_lat (domain pr)))
       (sigma (UBlock (point (base (view pr)) s))) = true) /\
  (forall s l s' e, reachable_state m s -> step m s l s' -> taken (base (view pr)) s l s' e ->
     executable (lift_bot_lattice (fact_lat (domain pr))) (sigma (UEdge e)) = true) /\
  (forall s x c, reachable_state m s -> val (view pr) s x = Some c ->
     gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) c).
```
Proof idea: induction on `exec` with the three-part invariant. A new binding is an operation (use
`op_sound`), a parameter (use the `CArg` row and `refine_on_edge_sound`, whose premises are
`guards_ok` and `guard_op_defined` at the taken edge), or arbitrary (use `top_sound`); a taken edge
is
feasible by `edge_feasible_sound`, hence executable, hence its target block is. Card: VIEW-4.

### VIEW-5

```coq
(** The dominated-use equation lemma: if the edge e dominates the block of a reachable state, every
    guard of e holds there for the current value of its subject, which is defined, and every
    guard subject defined by an operation holds the result of that operation on the current
    values of its arguments. *)
Theorem dominated_guard_holds {S O N E V K C} (m : semantics S O) (sv : ssa_view S O N E V K C) :
  ssa_view_laws m sv -> strict_ssa_laws m sv ->
  forall s e, reachable_state m s -> edge_dominates (cfg (base sv)) e (point (base sv) s) ->
    Forall (cond_holds sv s) (edge_guard sv e) /\ guard_ops_consistent sv s e.
```
Proof idea: a run from an initial state to `s` takes edges that form an entry path to the point of
`s`
(`run_edges_path`); `e` dominates that point, so the path contains `e`; cut it at the last
occurrence of `e`, at a reachable state `s1` that takes `e`. At `s1`, `guards_ok` and
`guard_op_defined` give the guards and the equations. After that last `e` the path visits no node
that dominates `Graph.source e`: the shortest entry path to such a node avoids `e`, because the
node dominates the source of `e`, and followed by the rest of the path it would reach the point of
`s` without `e`. By `redefine_in_stay` and `redefine_on_edge` no value whose home dominates the
source of `e` changes from `s1` to `s`. Those homes include the homes of the guard subjects
(`guard_home`) and of their arguments (`op_args_dominate` with the transitivity of `dominates`),
so every fact established at `s1` holds at `s`. The visited nodes include the successor of `s1`, so
an edge that returns to a node dominating its own source, a self-loop included
(`self_loop_not_edge_dominating` of GRA-2), cannot dominate the point of `s`. Card: VIEW-5.

```coq
(** The dominating edges returned by the dominator-tree walk really dominate. *)
Theorem dominating_edges_in_sound {N E} (EN : encoding N) (g : Graph.t N E) (b : N) (e : E) :
  graph_wf g -> (forall v, NoDup (Graph.out g v)) ->
  In e (dominating_edges_in (make_dom_context EN g) b) -> edge_dominates g e b.
(** On-demand refined fact: the fact for a value as read in a reachable state is sound, with
    refinement applied at the read and no extra nodes. *)
Theorem refined_fact_sound {S O N E V K C A} (m : semantics S O) (EN : encoding N)
    (ctx : dom_context N E) (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) :
  ctx = make_dom_context EN (cfg (base (view pr))) ->
  ssa_view_laws m (view pr) -> strict_ssa_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  forall s z c, reachable_state m s ->
    (forall x d, val (view pr) s x = Some d ->
       gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
    val (view pr) s z = Some c ->
    gamma (lift_bot_gamma (fact_conc (domain pr)))
      (refined_fact ctx pr sigma (point (base (view pr)) s) z) c.
```
Proof idea: the first is Graph's `dominating_edges_sound` for the tree that `make_dom_context`
builds, which is sound whether or not the checker accepted it. The second folds `refine_fact`
over the dominating edges with the invariant that the accumulated fact contains `c`: each edge
dominates the block of `s` (the first theorem, `cfg_wf` for `graph_wf`), so `dominated_guard_holds`
gives its guards and equations at `s`, and `refine_fact_sound` applies with the accumulated fact
as its start fact. The start of the fold contains `c` by the facts premise. Card: VIEW-5.

### VIEW-6

```coq
(** The call graph of a well-formed calls view is a well-formed graph. *)
Theorem call_graph_wf {S F P} (cv : calls_view S F P) (resolve : P -> list F) :
  NoDup (functions cv) -> incl (roots cv) (functions cv) ->
  (forall f p, In p (sites_of cv f) -> caller_of cv p = f /\ In f (functions cv)) ->
  (forall p g, In g (resolve p) -> In g (functions cv)) ->
  graph_wf (call_graph cv resolve).
(** Whole-program reachability: every function active in a reachable state is reachable in the
    call graph built from a sound resolver. *)
Theorem active_reachable_in_call_graph {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) :
  calls_view_laws m cv resolve ->
  forall s, reachable_state m s -> forall f, In f (active cv s) ->
    reachable (call_graph cv resolve) f.
```
Proof idea: induction on `exec` with the invariant that consecutive frames are linked by a call
edge: a call step pushes `(here s, p)` with `here s'` in `resolve p`, and a return pops. Card:
VIEW-6.

```coq
(** Summary soundness over frames: from a post-solution of the summary system, the summary of
    every function that is active covers every step taken, including the steps of callees above
    it and the facts of suspended callers. *)
Theorem summary_sound {S O F P A} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) (sc : step_cover S O A) (sigma : F -> A) :
  calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  post_solution (slat sp) (summary_system cv resolve sp) sigma ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) ->
    step_covers sc (sigma f) s l s'.
```
Proof idea: induction on the position of `f` in the stack `active cv s`. At the top,
`local_covers`, the `SLocal` row and `covers_monotone`. One frame down, `call_covers` moves
cover through the `SCall` row of the call site, using the chain invariant of the previous proof
(the callee on top of a suspended frame is in `resolve` of its site). Card: VIEW-6.

```coq
(** A run through states at non-observing instructions emits no event: the instructions of the
    states that can step all have `observes` false. *)
Theorem silent_exec_in {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) (P : S -> Prop) (s s' : S) (tr : list O) :
  effects_laws m en ef ev -> reachable_state m s -> exec_in m P s tr s' ->
  (forall t, P t -> running m t -> exists i, instr_at ev t = Some i /\ observes ef i = false) ->
  tr = nil.
```
Proof idea: induction on `exec_in`; every state of the run is reachable, and `silent` applies to the
step taken from each state that steps. Card: VIEW-6.

### VIEW-7

```coq
(** Allocation sites persist: a location keeps its site along every run. *)
Theorem loc_site_preserved {S O V C L T} (m : semantics S O) (mv : mem_view S V C L T) :
  mem_view_laws m mv ->
  forall s tr s' l0 t, reachable_state m s -> exec m s tr s' -> loc_site mv s l0 = Some t ->
    loc_site mv s' l0 = Some t.
(** Points-to soundness template: if the facts of a value analysis contain every defined value
    and the pointer domain is sound, the footprint computed from a load's or store's base
    operand covers the bytes it touches. *)
Theorem access_footprint_sound {P S O C L V T} (m : semantics S O) (mv : mem_view S V C L T)
    (pd : pointer_domain P C T) (valuation : S -> V -> option C) (sigma : V -> P) :
  pointer_domain_laws m mv pd ->
  (forall s x c, reachable_state m s -> valuation s x = Some c ->
     gamma (ptr_conc pd) (sigma x) c) ->
  forall s b off w c l t, reachable_state m s ->
    (mem_instr mv s = Some (MemLoad b off w) \/
     exists src, mem_instr mv s = Some (MemStore b off w src)) ->
    valuation s b = Some c -> loc_of mv s c = Some l -> loc_site mv s l = Some t ->
    covered (access_footprint pd (sigma b) off w) t (loc_offset mv s c + off) w.
```
Proof idea: the first by induction on `exec` with `site_stable`. The second takes the start-offset
interval witness from `ptr_reach_sound` and shifts its bounds by the offset and width. Card: VIEW-7.

## Algorithms and references

- **Dense generators and the dataflow framework.** Kildall, "A unified approach to global
  program optimization" (POPL 1973), for edge transfers over a graph; Cousot and Cousot (POPL 1977)
  for `gamma`. The edge transfer is a parameter so that guarded edges prune. Loop heads as widening
  points: Bourdoncle, "Efficient chaotic iteration strategies with widenings" (1993).
- **Liveness, neededness, reaching definitions.** Pfenning, Platzer and Simmons, 15-411 Lecture 7,
  "Dataflow Analysis" (2015): the rules K1 and K2, N1 to N3 and R1 and R2 are the backward and
  forward transfers that Analyses instantiates here; reaching definitions are stated over the
  history of a run (`run_edges`) rather than over ghost state. Agreement as a bisimulation follows
  the style of verified dead-code passes; nothing is copied from CompCert.
- **Stuttering.** Browne, Clarke and Grumberg, "Characterizing finite Kripke structures in
  propositional temporal logic" (TCS 1988), for stuttering equivalence, and De Nicola and
  Vaandrager, "Three logics for branching bisimulation" (JACM 1995); the measure that bounds the
  silent steps of each side is the device of simulations with a decreasing measure, applied to
  both directions so that behaviour is equal rather than refined.
- **Structured code.** WebAssembly's relative labels (`br n`) and Cminor's `exit n`; the
  frame machine is a continuation-passing small-step semantics. Loop heads as cut points: Besson,
  Jensen and Pichardie (2006), certificates stored at loop heads and recomputed elsewhere. A
  balanced `Seq` tree keeps positions logarithmic in the length of a block.
- **Sparse conditional analysis.** Wegman and Zadeck, "Constant propagation with conditional
  branches" (TOPLAS 1991), with block parameters in place of phis (Appel, "SSA is functional
  programming", 1998). Edge predicates follow the on-demand range work in GCC's Ranger.
- **Dominance and the equation lemma.** Cooper, Harvey and Kennedy, "A simple, fast dominance
  algorithm" (2001), supplies the dominator tree; Graph's `dominating_edges` walks it once per
  query and takes the sole entering edge of each block on the chain. Cytron, Ferrante, Rosen,
  Wegman and Zadeck (TOPLAS 1991): a definition dominates its uses, so a value cannot be
  redefined between a dominating edge and a use dominated by it.
- **Calls and summaries.** Sharir and Pnueli (1981) and Reps, Horwitz and Sagiv (IFDS, 1995) for
  summaries and call-to-return edges; Apinis, Seidl and Vojdani (APLAS 2012) for side effects,
  used by Analyses for call strings and points-to. The summary system is solved bottom-up over
  the condensation of the call graph, a scheduler of the Fixpoint package.
- **Memory.** Andersen (1994) and Steensgaard (POPL 1996) for the pointer domains that implement
  `pointer_domain`.

## Performance notes

- The dense generators have one constraint per entry or node and one per edge, and `edges_of` is
  one pass over `Graph.nodes`. A row reads one unknown (the source of an edge going forward, its
  target going backward), so Fixpoint's prepared indexes over `deps` are linear in the graph.
- Keys are small. A `skel_edge` is a point and a slot, a point is a position of at most `skel_depth`
  directions, and a balanced `seq_of_list` keeps a block of `n` statements at depth `log2 n`, so an
  encoding costs a few bit operations per direction and never grows with the length of a block.
  `skel_out prog v` is computed once per node, at the cost of the `sub` and `label_point` lookups,
  and `Graph.out v` is built by `seq`; no edge list is scanned inside a loop.
- `dom_context` is built once per graph. `check_idom` runs one blocked search per reachable node,
  O(V (V + E)); `dominating_edges_in` is one walk of the tree chain, O(depth of the block);
  `refined_fact` costs that walk plus one refinement per guard of each edge, and creates no node.
  Each index has its agreement lemma: `dominating_edges_in_sound` for the walk, and the encodings'
  injectivity for the keys.
- The sparse system has one row per value, per edge, per edge argument and per entry block; its
  unknowns and constraints are keyed by the sum codes of `sparse_unknown_encoding` and
  `sparse_constraint_encoding`. A row evaluates at most the facts of one edge's guard subjects.
- Histories (`run_edges`, `last_writer`, `arrivals_since`) are specification: statements mention
  them and no analysis builds one.
- `solve_total` carries its termination evidence in `Prop`, which extraction erases. A dense
  system over a lattice of finite height needs only that height; with widening,
  `forward_cuts_every_cycle`, `backward_cuts_every_cycle` and `skeleton_cut_points` give the cut
  evidence for the loop heads.

## Open questions

1. **Bulk memory operations.** `access_footprint` covers loads and stores. Copies and fills need
   the byte ranges of DOM-6 and a fact about the length; `MemCopy`, `MemFill`, `MemAlloc` and
   `MemFree` have no footprint theorem here.
2. **Divergence of loops.** `may_diverge` has a law only for calls; the divergence of a loop is
   control dependence, handled by ANA-4.
3. **Interprocedural agreement.** Neededness across calls on the full semantics needs an agreement
   that compares suspended frames at their continuation facts. The solution-relative premises
   (`G sigma`, `R sigma`, and `sigma` in `step_agrees`) are the hook, but no stack-aware agreement
   is defined: Analyses and Examples claim none, and `activation_lifting` (EX-5c) carries forward
   facts and traces over frames instead.
4. **Scope of the two-program theorem.** `agreement_simulation2` takes one state type and one
   graph. A pass that renumbers nodes or changes the graph (unreachable-code removal, block
   merging) needs a node correspondence and is not covered.

## Cross-document contracts

For VIEW-6, `functions` and `resolve` cover every frame actually pushed by the modeled semantics,
including callbacks. An external operation modeled as one local step is covered by the local
effects law; an external frame must be listed and resolved. An all-functions fallback is sound
only for a closed set covering every possible pushed frame. Unknown effects use ANA-8c's
`unknown_modref`, not an empty target list. The `local_covers` premise covers every reachable
concrete step at the innermost function, including locally modeled external activity;
`call_covers` lifts that step through each suspended call.

Graph provides the total dominator tree, its sound edge index, `dominates_trans` and
`reachable_in_nodes`. Domains provides bytewise `covered` and `footprint`. A pointer domain
provides an inclusive start-offset witness; `access_footprint_sound` lifts it to covered bytes.
Analyses and Examples use the names, skeleton edges, SSA laws and solution-relative premises
defined here. EX-5c lifts activation reachability and traces, including callee events.


<!-- C19 VIEW-8 contract -->

## VIEW-8: finite instruction points

`ViewsSsaPoints.v` defines the following. `B` and `BE` are block and block-edge identities;
`N` and `E` are instruction-point and point-edge identities. A client constructs this view; no
general SSA construction, destruction or repair is promised.

```coq
Record point_uses (N E V : Type) : Type := PointUses {
  live_graph : Graph.t N E;
  edge_use : E -> list V;
  edge_def : E -> list V;
  exit_use : N -> list V
}.

Inductive syntactic_live {N E V} (p : point_uses N E V) (x : V) : N -> Prop :=
| live_exit : forall n, In x (exit_use p n) -> syntactic_live p x n
| live_edge_use : forall n e, In e (Graph.out (live_graph p) n) ->
    In x (edge_use p e) -> syntactic_live p x n
| live_edge_next : forall n e, In e (Graph.out (live_graph p) n) ->
    ~ In x (edge_def p e) -> syntactic_live p x (Graph.target (live_graph p) e) ->
    syntactic_live p x n.

Inductive point_chain {N E} (g : Graph.t N E) : list N -> list E -> Prop :=
| point_chain_one : forall n, point_chain g [n] []
| point_chain_step : forall n m ns e es,
    In e (Graph.out g n) -> Graph.target g e = m ->
    point_chain g (m :: ns) es -> point_chain g (n :: m :: ns) (e :: es).

Record ssa_points (B BE N E V : Type) : Type := SsaPoints {
  point_model : point_uses N E V;
  block_graph : Graph.t B BE;
  points_in_block : B -> list N;
  instruction_edges : B -> list E;
  parameter_edge : B -> E;
  block_of_point : N -> B;
  block_edge_of : E -> option BE;
  block_params : B -> list V;
  block_edge_args : BE -> list V;
  point_definition : V -> option N
}.

Definition point_use_at {N E V} (p : point_uses N E V) (n : N) (x : V) : Prop :=
  In x (exit_use p n) \/
  exists e, In e (Graph.out (live_graph p) n) /\ In x (edge_use p e).

Record ssa_point_laws {B BE N E V} (s : ssa_points B BE N E V) : Prop := {
  points_graph_wf : graph_wf (live_graph (point_model s));
  points_out_nodup : forall n, NoDup (Graph.out (live_graph (point_model s)) n);
  blocks_graph_wf : graph_wf (block_graph s);
  blocks_out_nodup : forall b, NoDup (Graph.out (block_graph s) b);
  points_covered : forall n, In n (Graph.nodes (live_graph (point_model s))) <->
    exists b, In b (Graph.nodes (block_graph s)) /\ In n (points_in_block s b);
  points_unique : forall b, NoDup (points_in_block s b);
  points_owner : forall b n, In b (Graph.nodes (block_graph s)) ->
    In n (points_in_block s b) -> block_of_point s n = b;
  blocks_nonempty : forall b, In b (Graph.nodes (block_graph s)) ->
    points_in_block s b <> [];
  points_ordered : forall b, In b (Graph.nodes (block_graph s)) ->
    point_chain (live_graph (point_model s)) (points_in_block s b) (instruction_edges s b);
  instruction_edges_internal : forall b e,
    In b (Graph.nodes (block_graph s)) -> In e (instruction_edges s b) ->
    block_edge_of s e = None;
  instruction_edges_complete : forall n e,
    In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) -> block_edge_of s e = None ->
    In e (instruction_edges s (block_of_point s n));
  parameter_edge_first : forall b, In b (Graph.nodes (block_graph s)) ->
    nth_error (instruction_edges s b) 0 = Some (parameter_edge s b);
  parameter_edge_defs : forall b x, In b (Graph.nodes (block_graph s)) ->
    (In x (edge_def (point_model s) (parameter_edge s b)) <-> In x (block_params s b));
  point_edge_projection : forall n e, In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) ->
    match block_edge_of s e with
    | None => block_of_point s n = block_of_point s (Graph.target (live_graph (point_model s)) e)
    | Some be => In be (Graph.out (block_graph s) (block_of_point s n)) /\
        Graph.target (block_graph s) be = block_of_point s (Graph.target (live_graph (point_model s)) e) /\
        last (points_in_block s (block_of_point s n)) n = n /\
        nth_error (points_in_block s (Graph.target (block_graph s) be)) 0 =
          Some (Graph.target (live_graph (point_model s)) e)
    end;
  phi_args_length : forall be, In be (edges_of (block_graph s)) ->
    length (block_edge_args s be) = length (block_params s (Graph.target (block_graph s) be));
  phi_edge_use : forall n e be, In n (Graph.nodes (live_graph (point_model s))) ->
    In e (Graph.out (live_graph (point_model s)) n) -> block_edge_of s e = Some be ->
    forall x, In x (block_edge_args s be) -> In x (edge_use (point_model s) e);
  block_edge_covered : forall be, In be (edges_of (block_graph s)) ->
    exists n e, In n (Graph.nodes (live_graph (point_model s)) /\
      In e (Graph.out (live_graph (point_model s)) n) /\ block_edge_of s e = Some be;
  block_edge_unique : forall e1 e2 be,
    In e1 (edges_of (live_graph (point_model s))) ->
    In e2 (edges_of (live_graph (point_model s))) ->
    block_edge_of s e1 = Some be -> block_edge_of s e2 = Some be -> e1 = e2
}.

Record reachable_point_ssa {B BE N E V} (s : ssa_points B BE N E V) : Prop := {
  point_ssa_single_entry : exists entry, Graph.entries (live_graph (point_model s)) = [entry];
  point_ssa_uses_defined : forall n x,
    reachable (live_graph (point_model s)) n -> point_use_at (point_model s) n x ->
    exists d, point_definition s x = Some d /\
      reachable (live_graph (point_model s)) d /\
      strictly_dominates (live_graph (point_model s)) d n;
  point_ssa_defs_at_home : forall n e x,
    reachable (live_graph (point_model s)) n ->
    In e (Graph.out (live_graph (point_model s)) n) ->
    In x (edge_def (point_model s) e) -> point_definition s x = Some n;
  point_ssa_home_kills : forall x d e,
    point_definition s x = Some d -> reachable (live_graph (point_model s)) d ->
    In e (Graph.out (live_graph (point_model s)) d) -> In x (edge_def (point_model s) e)
}.
```

Each `points_in_block` is the finite instruction-order list, including explicit before/after
points. A block-edge point edge carries that occurrence's phi arguments, preserving
parallel edges. A client's later common intra-block parameter-definition edge writes the block
parameters; thus all incoming phi operands are read before the common static definition. The
client additionally proves its point edges' uses and definitions agree with its instruction
syntax and semantics; these are client-specific obligations rather than generic SSA laws.
Exit uses include final, trap and stop operands. Unreachable nodes still have syntactic liveness;
the strict record only restricts the reachable part. Definitions on a dynamic loop can execute
more than once. An entry value is represented by a definition edge before its uses.




<!-- C19 ANA-10b memory effects -->

## Effects and the client boundary: ViewsMemoryEffects.v

`MemoryAll` includes every byte of every object, including allocation and lifetime changes.
`MemoryRegions fs` denotes the bytes covered by `fs`; a zero-width range covers no byte.
Unknown calls use `MemoryAll` for both sides; a barrier is a read/write of `MemoryAll` and is
never skipped solely because its footprint is empty. Call summaries must include all actual
effects; exceptional or nonreturning calls need separate CFG edges for their actual transitions.
The representation imposes no fixed machine word width or address-space bound.

```coq
Inductive memory_scope (T : Type) : Type :=
  | MemoryRegions (fs : list (footprint T))
  | MemoryAll.

Definition memory_scope_covers {T} (scope : memory_scope T) (t : T) (o : Z) : Prop :=
  match scope with
  | MemoryRegions fs => covered fs t o 1
  | MemoryAll => True
  end.

Inductive memory_effect (T : Type) : Type :=
  | MemoryRead (reads : memory_scope T)
  | MemoryWrite (writes : memory_scope T)
  | MemoryReadWrite (reads writes : memory_scope T)
  | MemoryCall (reads writes : memory_scope T)
  | MemoryBarrier.

Definition effect_reads {T} (a : memory_effect T) : memory_scope T :=
  match a with
  | MemoryRead r => r
  | MemoryWrite _ => MemoryRegions []
  | MemoryReadWrite r _ => r
  | MemoryCall r _ => r
  | MemoryBarrier => MemoryAll
  end.

Definition effect_writes {T} (a : memory_effect T) : memory_scope T :=
  match a with
  | MemoryRead _ => MemoryRegions []
  | MemoryWrite w => w
  | MemoryReadWrite _ w => w
  | MemoryCall _ w => w
  | MemoryBarrier => MemoryAll
  end.

Definition effect_is_def {T} (a : memory_effect T) : bool :=
  match a with
  | MemoryRead _ => false
  | _ => true
  end.

Record memory_effect_view (S O N E T B L : Type) : Type := MemoryEffectView {
  effect_graph : graph_view S O N E;
  edge_effects : E -> list (memory_effect T);
  effect_snapshot : S -> B;
  effect_site : B -> L -> option T;
  effect_byte : B -> L -> Z -> option nat;
  effect_step : B -> memory_effect T -> B -> Prop;
  effect_read : B -> memory_effect T -> L -> Z -> Prop;
  transition_read : S -> list O -> S -> L -> Z -> Prop
}.

Inductive effect_trace {S O N E T B L}
    (v : memory_effect_view S O N E T B L) : B -> list (memory_effect T) -> B -> Prop :=
  | effect_trace_nil : forall b, effect_trace v b [] b
  | effect_trace_cons : forall b a b' rest b'',
      effect_step v b a b' -> effect_trace v b' rest b'' ->
      effect_trace v b (a :: rest) b''.

Inductive effect_trace_states {S O N E T B L}
    (v : memory_effect_view S O N E T B L) :
    B -> list (memory_effect T) -> list B -> B -> Prop :=
  | effect_states_nil : forall b, effect_trace_states v b [] [] b
  | effect_states_cons : forall b a b' rest states b'',
      effect_step v b a b' -> effect_trace_states v b' rest states b'' ->
      effect_trace_states v b (a :: rest) (b :: states) b''.

Record memory_effect_laws {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) : Prop := {
  effect_view_laws : graph_view_laws m (effect_graph v);
  effect_no_stays : forall s tr s', ~ stays (effect_graph v) s tr s';
  effect_step_trace : forall s tr s' e, reachable_state m s -> step m s tr s' ->
    taken (effect_graph v) s tr s' e -> exists states,
    effect_trace_states v (effect_snapshot v s) (edge_effects v e) states
      (effect_snapshot v s') /\
    forall l o, transition_read v s tr s' l o -> exists i b a,
      nth_error states i = Some b /\ nth_error (edge_effects v e) i = Some a /\
      effect_read v b a l o;
  effect_read_covered : forall b a l o t, effect_read v b a l o ->
    effect_site v b l = Some t -> memory_scope_covers (effect_reads a) t o;
  effect_site_stable : forall b a b' l t, effect_step v b a b' ->
    effect_site v b l = Some t -> effect_site v b' l = Some t;
  effect_byte_frame : forall b a b' l t o, effect_step v b a b' ->
    effect_site v b l = Some t -> effect_byte v b' l o <> effect_byte v b l o ->
    memory_scope_covers (effect_writes a) t o
}.

Theorem effect_transition_byte_covered {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) :
  memory_effect_laws m v ->
  forall s tr s' e l t o, reachable_state m s -> step m s tr s' ->
    taken (effect_graph v) s tr s' e -> effect_site v (effect_snapshot v s) l = Some t ->
    effect_byte v (effect_snapshot v s') l o <> effect_byte v (effect_snapshot v s) l o ->
    exists a, In a (edge_effects v e) /\ memory_scope_covers (effect_writes a) t o.
```

`transition_read` is the client's actual byte-read observation, including externally visible
reads and reads performed by callees. Its connection to the client instruction semantics is an
explicit client obligation. Intermediate `B` values are snapshots, not necessarily machine
states; the event relation and its frame laws apply to every intermediate snapshot in a trace.
The site is historical and remains after free; `effect_byte` can become `None` on free. Fresh
allocation identities and actual read observations are supplied by the client. A later value
forwarding theorem needs additional decoding, accessibility and equality laws.
