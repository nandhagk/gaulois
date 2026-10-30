# Gaulois.Rewrite

`Gaulois.Rewrite` is a standalone, directly verified equality-saturation library. Its theory
depends on Rocq Stdlib and `Gaulois.Collections` only. Clients supply signatures, interpretations,
rules, their proofs, fact validity and costs. Equality compares the entire `option` result: two
undefined evaluations are equal. No statement here implies that a partial operation is defined.
The ANA-6 compatibility surface and external explanation checker remain available in Analyses.

The public contract is organized by implementation card. Definitions written with an omitted
body specify an executable function; the accompanying equations and theorem statements fix its
meaning. A theorem is a proof obligation, not evidence of a proof. All core theorems are closed
under the global context. Dictionaries are parameterized records, without carrier `Type` fields.
At commit `3281819`, REW-1 through REW-7 and ANA-6 have landed. Their reports and independent
reviews record checked claims and finite examples under the stated premises.

## Files

| Card | Files |
|---|---|
| REW-1 | `RewriteSyntax.v`, `RewriteRules.v`, `RewriteEquality.v`, `dune` |
| REW-2 | `RewriteEgraph.v`, `RewriteIndex.v`, `RewriteRebuild.v` |
| REW-3 | `RewriteMatch.v` |
| REW-4 | `RewriteAnalysis.v` |
| REW-5 | `RewriteRun.v` |
| REW-6 | `RewriteExtract.v` |
| REW-7 | Analyses Order, SSA and word clients, specified in `analyses.md` |

## REW-1: syntax, rules and equality

Every application records its result sort and the list of its argument sorts. A signature checks
that full shape, permitting fixed or variadic operators. Free variables and pattern holes are
distinct. Holes are first-order: this contract has no binders or alpha-equivalence.

```coq
Inductive rw_term (K Sort V : Type) : Type :=
| RWVar (s : Sort) (v : V)
| RWApp (s : Sort) (op : K) (args : list (rw_term K Sort V)).
Inductive rw_pattern (K Sort V H : Type) : Type :=
| RWHole (s : Sort) (h : H)
| RWPVar (s : Sort) (v : V)
| RWPApp (s : Sort) (op : K) (args : list (rw_pattern K Sort V H)).

Definition rw_sort {K Sort V} (t : rw_term K Sort V) : Sort :=
  match t with RWVar s _ => s | RWApp s _ _ => s end.
Definition rwp_sort {K Sort V H} (p : rw_pattern K Sort V H) : Sort :=
  match p with RWHole s _ => s | RWPVar s _ => s | RWPApp s _ _ => s end.

Record rw_signature (K Sort V : Type) : Type := RwSignature {
  rw_var_sort : V -> option Sort;
  rw_operator_shape : K -> list Sort -> Sort -> bool
}.
Inductive rw_typed {K Sort V} (sig : rw_signature K Sort V) : rw_term K Sort V -> Prop :=
| rw_typed_var : forall s v, rw_var_sort sig v = Some s -> rw_typed sig (RWVar s v)
| rw_typed_app : forall s op args, Forall (rw_typed sig) args ->
    rw_operator_shape sig op (map rw_sort args) s = true ->
    rw_typed sig (RWApp s op args).
Inductive rwp_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort) :
    rw_pattern K Sort V H -> Prop :=
| rwp_typed_hole : forall s h, hs h = Some s -> rwp_typed sig hs (RWHole s h)
| rwp_typed_var : forall s v, rw_var_sort sig v = Some s -> rwp_typed sig hs (RWPVar s v)
| rwp_typed_app : forall s op args, Forall (rwp_typed sig hs) args ->
    rw_operator_shape sig op (map rwp_sort args) s = true ->
    rwp_typed sig hs (RWPApp s op args).

Definition rw_substitution (K Sort V H : Type) := H -> option (rw_term K Sort V).
Definition rw_sub_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h s, hs h = Some s -> exists t, sub h = Some t /\ rw_sort t = s /\ rw_typed sig t.
Definition rw_instantiate {K Sort V H} (sub : rw_substitution K Sort V H)
    (p : rw_pattern K Sort V H) : option (rw_term K Sort V).
(* Holes use sub; variables are unchanged; an application succeeds exactly when all children do. *)

Record rw_semantics (K Sort V C : Type) : Type := RwSemantics {
  rw_var_value : V -> option C;
  rw_eval_op : K -> list C -> option C
}.
Definition rw_denote {K Sort V C} (sem : rw_semantics K Sort V C)
    (t : rw_term K Sort V) : option C.
(* Variable lookup; strict left-to-right traversal of children followed by rw_eval_op. *)
Definition rw_equiv {K Sort V C} (admissible : rw_semantics K Sort V C -> Prop)
    (t u : rw_term K Sort V) : Prop :=
  forall sem, admissible sem -> rw_denote sem t = rw_denote sem u.

Theorem rw_instantiate_typed {K Sort V H} (sig : rw_signature K Sort V)
    (hs : H -> option Sort) (sub : rw_substitution K Sort V H) (p : rw_pattern K Sort V H) :
  rwp_typed sig hs p -> rw_sub_typed sig hs sub ->
  exists t, rw_instantiate sub p = Some t /\ rw_typed sig t /\ rw_sort t = rwp_sort p.

Record rw_rule (K Sort V H : Type) : Type := RwRule {
  rw_holes : list H;
  rw_hole_sort : H -> option Sort;
  rw_lhs : rw_pattern K Sort V H;
  rw_rhs : rw_pattern K Sort V H;
  rw_condition : rw_substitution K Sort V H -> bool
}.
Definition rw_rule_wf {K Sort V H} (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) : Prop :=
  NoDup (rw_holes r) /\
  (forall h, In h (rw_holes r) <-> exists s, rw_hole_sort r h = Some s) /\
  rwp_typed sig (rw_hole_sort r) (rw_lhs r) /\
  rwp_typed sig (rw_hole_sort r) (rw_rhs r) /\ rwp_sort (rw_lhs r) = rwp_sort (rw_rhs r).
Definition rw_rule_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (r : rw_rule K Sort V H) : Prop :=
  forall sub l r', rw_sub_typed sig (rw_hole_sort r) sub -> rw_condition r sub = true ->
    rw_instantiate sub (rw_lhs r) = Some l -> rw_instantiate sub (rw_rhs r) = Some r' ->
    rw_equiv admissible l r'.

Inductive rw_equal {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
    rw_term K Sort V -> rw_term K Sort V -> Prop :=
| rw_eq_refl : forall t, rw_equal sig admissible rules t t
| rw_eq_sym : forall t u, rw_equal sig admissible rules t u -> rw_equal sig admissible rules u t
| rw_eq_trans : forall t u v, rw_equal sig admissible rules t u ->
    rw_equal sig admissible rules u v -> rw_equal sig admissible rules t v
| rw_eq_app : forall s op ts us, Forall2 (rw_equal sig admissible rules) ts us ->
    rw_equal sig admissible rules (RWApp s op ts) (RWApp s op us)
| rw_eq_rule : forall r sub l u, In r rules -> rw_sub_typed sig (rw_hole_sort r) sub ->
    rw_condition r sub = true -> rw_instantiate sub (rw_lhs r) = Some l ->
    rw_instantiate sub (rw_rhs r) = Some u -> rw_equal sig admissible rules l u.

Theorem rw_equal_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  Forall (rw_rule_sound sig admissible) rules ->
  forall t u, rw_equal sig admissible rules t u -> rw_equiv admissible t u.
Theorem rw_equal_typed {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  Forall (rw_rule_wf sig) rules ->
  forall t u, rw_typed sig t -> rw_equal sig admissible rules t u ->
    rw_typed sig u /\ rw_sort t = rw_sort u.
```

## REW-2: represented terms and graph operations

Class identifiers and node identifiers are positive keys. Operations build prepared indexes once
per graph phase and update them as needed, rather than scanning the node list at each use. The
following abstract observers define the public representation relation. A child points to a class,
and a finite
derivation of `rw_represents` unfolds one graph node per term node; the graph itself may contain
cycles. `rw_roots` and `rw_nodes_in` enumerate exactly the allocated canonical roots and nodes.
The graph's sort is fixed at allocation and a merge of different sorts is rejected.

```coq
Definition rw_id := positive.
Inductive rw_node (K Sort V : Type) : Type :=
| RWNVar (s : Sort) (v : V)
| RWNApp (s : Sort) (op : K) (children : list rw_id).
Definition rw_node_sort {K Sort V} (n : rw_node K Sort V) : Sort :=
  match n with RWNVar s _ => s | RWNApp s _ _ => s end.

Record rw_graph (K Sort V : Type) : Type := RwGraph {
  rw_roots : list rw_id;
  rw_nodes_in : list rw_id;
  rw_class_roots : Map.t rw_id rw_id;
  rw_sorts : Map.t rw_id Sort;
  rw_nodes : Map.t rw_id (rw_id * rw_node K Sort V)
}.
Definition rw_find {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option rw_id :=
  Map.get positive_encoding c (rw_class_roots g).
Definition rw_class_sort {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option Sort :=
  Map.get positive_encoding c (rw_sorts g).
Definition rw_node_at {K Sort V} (g : rw_graph K Sort V) (n : rw_id) :
    option (rw_id * rw_node K Sort V) := Map.get positive_encoding n (rw_nodes g).
Inductive rw_represents {K Sort V} (g : rw_graph K Sort V) : rw_id -> rw_term K Sort V -> Prop :=
| rw_repr_var : forall c n owner root s v,
    rw_node_at g n = Some (owner, RWNVar s v) -> rw_find g owner = Some root ->
    rw_find g c = Some root -> rw_represents g c (RWVar s v)
| rw_repr_app : forall c n owner root s op ids ts,
    rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
    rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
    rw_represents g c (RWApp s op ts).

Definition rw_graph_wf {K Sort V} (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : Prop :=
  NoDup (rw_roots g) /\ NoDup (rw_nodes_in g) /\
  Map.wf positive_encoding (rw_class_roots g) /\ Map.wf positive_encoding (rw_sorts g) /\
  Map.wf positive_encoding (rw_nodes g) /\
  (forall c root, rw_find g c = Some root ->
    In root (rw_roots g) /\ rw_find g root = Some root /\
    exists s, rw_class_sort g c = Some s /\ rw_class_sort g root = Some s) /\
  (forall root, In root (rw_roots g) -> rw_find g root = Some root) /\
  (forall c, (exists s, rw_class_sort g c = Some s) <->
    (exists root, rw_find g c = Some root)) /\
  (forall n, In n (rw_nodes_in g) <-> exists c node, rw_node_at g n = Some (c, node)) /\
  (forall n c node, rw_node_at g n = Some (c, node) ->
    rw_class_sort g c = Some (rw_node_sort node)) /\
  (forall n c s v, rw_node_at g n = Some (c, RWNVar s v) ->
    rw_var_sort sig v = Some s) /\
  (forall n c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) ->
    exists sorts, Forall2 (fun id ty => rw_class_sort g id = Some ty) ids sorts /\
      rw_operator_shape sig op sorts s = true) /\
  (forall c t, rw_represents g c t -> rw_typed sig t).

Definition rw_graph_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) : Prop :=
  forall c t u, rw_represents g c t -> rw_represents g c u -> rw_equal sig admissible rules t u.
Definition rw_extends {K Sort V} (g g' : rw_graph K Sort V) : Prop :=
  forall c t, rw_represents g c t -> rw_represents g' c t.
Definition rw_clean {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall a b t, rw_represents g a t -> rw_represents g b t -> rw_find g a = rw_find g b.
Definition rw_productive {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall c root, rw_find g c = Some root -> exists t, rw_represents g c t.
Definition rw_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a b : rw_id) : Prop :=
  (exists t, rw_represents g a t) /\ (exists u, rw_represents g b u) /\
  forall t u, rw_represents g a t -> rw_represents g b u -> rw_equal sig admissible rules t u.

Record rw_index (K : Type) : Type := RwIndex {
  rw_index_ops : Map.t K (list rw_id);
  rw_index_parents : Map.t rw_id (list rw_id);
  rw_index_root_parents : Map.t rw_id (list rw_id)
}.
Definition rw_lookup_list {K} (E : encoding K) (k : K) (m : Map.t K (list rw_id)) : list rw_id :=
  match Map.get E k m with Some ids => ids | None => [] end.
Definition rw_index_agrees {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) : Prop :=
  Map.wf EK (rw_index_ops ix) /\ Map.wf positive_encoding (rw_index_parents ix) /\
  Map.wf positive_encoding (rw_index_root_parents ix) /\
  (forall op, NoDup (rw_lookup_list EK op (rw_index_ops ix))) /\
  (forall child, NoDup (rw_lookup_list positive_encoding child (rw_index_parents ix))) /\
  (forall root, NoDup (rw_lookup_list positive_encoding root (rw_index_root_parents ix))) /\
  (forall op n, In n (rw_lookup_list EK op (rw_index_ops ix)) <->
    exists c s ids, rw_node_at g n = Some (c, RWNApp s op ids)) /\
  (forall child n, In n (rw_lookup_list positive_encoding child (rw_index_parents ix)) <->
    exists c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids) /\
  (forall root n, In n (rw_lookup_list positive_encoding root (rw_index_root_parents ix)) <->
    exists c s op ids child, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids /\
      rw_find g child = Some root).
Definition rw_build_index {K Sort V} (EK : encoding K) (g : rw_graph K Sort V) : rw_index K.
Theorem rw_build_index_agrees {K Sort V} (EK : encoding K) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : rw_graph_wf sig g -> rw_index_agrees EK g (rw_build_index EK g).
Definition rw_parent_nodes {K Sort V} (g : rw_graph K Sort V) (ix : rw_index K) (c : rw_id) :
    list rw_id :=
  match rw_find g c with
  | Some root => rw_lookup_list positive_encoding root (rw_index_root_parents ix)
  | None => []
  end.
Theorem rw_parent_nodes_agree {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) (c n : rw_id) :
  rw_index_agrees EK g ix ->
  (In n (rw_parent_nodes g ix c) <-> exists root owner s op ids child,
    rw_find g c = Some root /\ rw_find g child = Some root /\
    rw_node_at g n = Some (owner, RWNApp s op ids) /\ In child ids).

Definition rw_empty {K Sort V} : rw_graph K Sort V.
Definition rw_add {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (t : rw_term K Sort V) : rw_graph K Sort V * rw_id.
Definition rw_union {K Sort V} (ES : encoding Sort) (g : rw_graph K Sort V)
    (a b : rw_id) : option (rw_graph K Sort V).
Definition rw_index_after_union {K Sort V} (g g' : rw_graph K Sort V) (ix : rw_index K)
    (a b : rw_id) : rw_index K.
Definition rw_index_after_node_change {K Sort V} (EK : encoding K) (g g' : rw_graph K Sort V)
    (ix : rw_index K) (n : rw_id) : rw_index K.
Definition rw_rebuild {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) : rw_graph K Sort V.
```

`rw_add` interns every node of the finite term, allocates missing classes, and returns its class.
`rw_union` returns `None` for an unallocated identifier or different class sorts; otherwise it
merges exactly the requested classes. `rw_rebuild` canonicalizes
children and repeatedly merges congruent parents until clean. It may add equalities but no new
term node; it terminates on every finite well-formed graph. Existing class identifiers remain
valid. Neither operation silently authorizes an arbitrary semantic equality: preservation requires
the explicit `rw_joinable` premise for union.

The root-parent index aggregates parents of every alias in each canonical class. After a union,
`rw_index_after_union` combines the two old root buckets into the new root bucket and removes the
obsolete bucket, without scanning nodes. After a node is canonicalized, `rw_index_after_node_change`
updates the raw, root-parent and operator buckets using only that node's old and new children.
Both updates deduplicate node identifiers; node changes account for repeated child IDs and distinct
child aliases resolving to the same root before removing or reinserting the parent.
Rebuild initializes the index once and maintains these invariants after every such change; this
includes parents that still contain a noncanonical child alias.
Rebuild keeps dirty congruence obligations in a local indexed pair worklist, not a public graph
field. A finite binary credit bounds the iteration; the prepared pair universe can be quadratic
within an operator bucket. This observation is not a complexity theorem or measurement.

```coq
Theorem rw_empty_wf {K Sort V} (sig : rw_signature K Sort V) : rw_graph_wf sig rw_empty.
Theorem rw_empty_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  rw_graph_sound sig admissible rules rw_empty.
Theorem rw_empty_productive {K Sort V} : rw_productive (@rw_empty K Sort V).
Theorem rw_add_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g -> rw_typed sig t ->
  let '(g', c) := rw_add EK ES EV g t in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\
  rw_represents g' c t.
Theorem rw_union_correct {K Sort V H C} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a b : rw_id) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_joinable sig admissible rules g a b -> rw_union ES g a b = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\
  rw_find g' a = rw_find g' b.
Theorem rw_union_structure {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (g g' : rw_graph K Sort V) (a b ra rb : rw_id) :
  rw_graph_wf sig g -> rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_union ES g a b = Some g' ->
  (forall n, rw_node_at g' n = rw_node_at g n) /\
  (forall x, (exists root, rw_find g x = Some root) <->
             (exists root, rw_find g' x = Some root)) /\
  (forall x y rx ry, rw_find g x = Some rx -> rw_find g y = Some ry ->
    (rw_find g' x = rw_find g' y <->
      rx = ry \/ (rx = ra /\ ry = rb) \/ (rx = rb /\ ry = ra))).
Theorem rw_index_after_union_agrees {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (a b : rw_id) :
  rw_graph_wf sig g -> rw_index_agrees EK g ix -> rw_union ES g a b = Some g' ->
  rw_index_agrees EK g' (rw_index_after_union g g' ix a b).
Theorem rw_index_after_node_change_agrees {K Sort V} (EK : encoding K)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (n : rw_id) :
  rw_graph_wf sig g -> rw_graph_wf sig g' -> rw_index_agrees EK g ix ->
  (forall c, rw_find g' c = rw_find g c) ->
  (forall m, m <> n -> rw_node_at g' m = rw_node_at g m) ->
  rw_index_agrees EK g' (rw_index_after_node_change EK g g' ix n).
Theorem rw_rebuild_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_graph_wf sig (rw_rebuild EK ES EV g) /\
  rw_graph_sound sig admissible rules (rw_rebuild EK ES EV g) /\
  rw_productive (rw_rebuild EK ES EV g) /\
  rw_clean (rw_rebuild EK ES EV g) /\
  rw_extends g (rw_rebuild EK ES EV g).
```

## REW-3: indexed single-pattern matching

The matcher returns finite maps from holes to classes. Repeated occurrences must resolve to the
same canonical class. It is complete for one finite first-order pattern, including graph cycles;
it does not promise multipattern joins. The caller supplies a concrete term witness for each
hole before testing a term-dependent rule condition. The matcher builds and uses operator and
parent indexes; it does not rescan all nodes for each recursive match.

```coq
Definition rwp_holes {K Sort V H} (p : rw_pattern K Sort V H) : list H.
(* Traverse the pattern left to right, collecting each hole occurrence, including repetitions. *)
Definition rw_assignment (H : Type) := Map.t H rw_id.
Definition rw_covers {K Sort V H} (EH : encoding H) (g : rw_graph K Sort V)
    (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h, In h (rwp_holes p) ->
    exists c t, Map.get EH h a = Some c /\ sub h = Some t /\ rw_represents g c t.
Definition rw_match {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (g : rw_graph K Sort V) (root : rw_id) (p : rw_pattern K Sort V H) :
    list (rw_assignment H).

Theorem rw_match_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (a : rw_assignment H)
    (sub : rw_substitution K Sort V H) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> In a (rw_match EK ES EV EH g root p) -> rw_covers EH g p a sub ->
  rw_instantiate sub p = Some t -> rw_represents g root t.
Theorem rw_match_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (root : rw_id) (p : rw_pattern K Sort V H) (sub : rw_substitution K Sort V H)
    (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_clean g ->
  rwp_typed sig (fun h => option_map rw_sort (sub h)) p ->
  rw_instantiate sub p = Some t -> rw_represents g root t ->
  exists a, In a (rw_match EK ES EV EH g root p) /\ rw_covers EH g p a sub.
```

## REW-4: validated class analyses

An analysis fact describes all outcomes, including `None`, of all finite terms represented by
the class in every admissible environment. The client chooses this interpretation and proves
its transfer and combination laws. A nonzero guard that needs successful evaluation must require
the fact to exclude both zero and `None`. Facts with contextual validity may be used only with
that context in `admissible`; they must not be promoted to a larger environment set.

```coq
Record rw_analysis (K Sort V C F : Type) : Type := RwAnalysis {
  rw_fact_holds : F -> option C -> Prop;
  rw_fact_unknown : F;
  rw_fact_combine : F -> F -> F;
  rw_fact_transfer : rw_graph K Sort V -> (rw_id -> F) -> rw_id -> F
}.
Definition rw_fact_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (c : rw_id) (f : F) : Prop :=
  forall t sem, rw_represents g c t -> admissible sem -> rw_fact_holds an f (rw_denote sem t).
Definition rw_facts_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (facts : rw_id -> F) : Prop :=
  forall c, rw_fact_valid admissible an g c (facts c).
Record rw_analysis_laws {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F) : Prop := {
  rw_unknown_valid : forall result, rw_fact_holds an (rw_fact_unknown an) result;
  rw_combine_valid : forall f h result, rw_fact_holds an f result ->
    rw_fact_holds an h result -> rw_fact_holds an (rw_fact_combine an f h) result;
  rw_transfer_valid : forall g facts c, rw_graph_wf sig g -> rw_facts_valid admissible an g facts ->
    rw_fact_valid admissible an g c (rw_fact_transfer an g facts c)
}.
Definition rw_analyse_step {K Sort V C F} (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) : rw_id -> F.
(* At c, combine its old fact with the transfer result; elsewhere retain the old fact. *)
Theorem rw_analyse_step_valid {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) :
  rw_analysis_laws sig admissible an -> rw_graph_wf sig g -> rw_facts_valid admissible an g facts ->
  rw_facts_valid admissible an g (rw_analyse_step an g facts c).
```

After any graph extension or union, a client must re-establish `rw_facts_valid` before reading
facts; unknown facts are always valid. Analysis-triggered merges go through the same `rw_union`
and `rw_joinable` proof obligation as ordinary rewrites. No convergence or least-fact result is
claimed by this single step.

## REW-5: bounded execution

An attempt names a rule, a root and a finite map of hole witnesses. A schedule is supplied by the
consumer and can use externally maintained, valid analysis facts when choosing attempts. The
runner checks typing, representation and the rule's Boolean condition before applying an attempt.
It adds the right-hand term, unions its class with the matched root, and rebuilds. Failed attempts
consume fuel and leave the graph unchanged. All fuel is binary `N`. A scheduler returning `None`
means it stopped; it does not establish a fixed point or fairness.

```coq
Record rw_attempt (K Sort V H : Type) : Type := RwAttempt {
  rw_attempt_rule : nat;
  rw_attempt_root : rw_id;
  rw_attempt_sub : Map.t H (rw_term K Sort V)
}.
Definition rw_attempt_substitution {K Sort V H} (EH : encoding H) (a : rw_attempt K Sort V H) :
    rw_substitution K Sort V H := fun h => Map.get EH h (rw_attempt_sub a).
Definition rw_check_sub {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (r : rw_rule K Sort V H)
    (sub : rw_substitution K Sort V H) : bool.
(* For every listed hole: a binding exists, has the declared sort, and is recursively typed. *)
Theorem rw_check_sub_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_check_sub EK ES EV EH sig r sub = true ->
  rw_sub_typed sig (rw_hole_sort r) sub.
Theorem rw_check_sub_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_sub_typed sig (rw_hole_sort r) sub ->
  rw_check_sub EK ES EV EH sig r sub = true.
Definition rw_rep_test {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) : bool.
Theorem rw_rep_test_spec {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> (rw_rep_test EK ES EV g c t = true <-> rw_represents g c t).
Definition rw_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a : rw_attempt K Sort V H) : option (rw_graph K Sort V).
(* Reject an absent rule, invalid substitution, false condition, failed instantiation, absent lhs,
   or failed union. Otherwise add the rhs, union it with the root and rebuild. *)
Theorem rw_apply_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a : rw_attempt K Sort V H) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_apply EK ES EV EH sig rules g a = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_clean g' /\ rw_extends g g'.

Inductive rw_stop : Type := RWStopped | RWFuelExhausted.
Record rw_run_result (K Sort V : Type) : Type := RwRunResult {
  rw_run_graph : rw_graph K Sort V;
  rw_run_stop : rw_stop
}.
Definition rw_strategy (K Sort V H : Type) := rw_graph K Sort V -> option (rw_attempt K Sort V H).
Definition rw_run {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
    rw_run_result K Sort V.
(* Zero fuel returns RWFuelExhausted; otherwise ask the strategy. None returns RWStopped.
   Some attempt applies it if accepted and continues with fuel minus one. *)
Theorem rw_run_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  let g' := rw_run_graph (rw_run EK ES EV EH sig rules strategy fuel g) in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g'.
```

## REW-6: exact finite tree extraction

The objective is the sum of nonnegative natural weights over the materialized tree, counting
repeated subtrees each time. Variable and operator weights are separate. The result is exact
among all finite represented terms, including in cyclic class graphs. It does not optimize shared
DAG size, register pressure or a cross-root objective. Materializing the output can take space
exponential in the compact graph; count output size separately. Costs are mathematical naturals.

```coq
Definition rw_tree_cost {K Sort V} (var_cost : V -> nat) (op_cost : K -> nat)
    (t : rw_term K Sort V) : nat.
(* Variables cost var_cost v; applications cost op_cost op plus the sum of child tree costs. *)
Definition rw_extract_tree {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V) (c : rw_id) :
    option (rw_term K Sort V).
Theorem rw_extract_tree_some {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_extract_tree EK ES EV var_cost op_cost g c = Some t ->
  rw_represents g c t /\
  forall u, rw_represents g c u -> rw_tree_cost var_cost op_cost t <= rw_tree_cost var_cost op_cost u.
Theorem rw_extract_tree_none {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (var_cost : V -> nat) (op_cost : K -> nat)
    (g : rw_graph K Sort V) (c : rw_id) :
  rw_graph_wf sig g -> (rw_extract_tree EK ES EV var_cost op_cost g c = None <->
    (forall t, ~ rw_represents g c t)).
Theorem rw_extract_tree_equiv {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (var_cost : V -> nat) (op_cost : K -> nat) (g : rw_graph K Sort V)
    (c : rw_id) (input output : rw_term K Sort V) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_wf sig g ->
  rw_graph_sound sig admissible rules g -> rw_represents g c input ->
  rw_extract_tree EK ES EV var_cost op_cost g c = Some output ->
  rw_equiv admissible input output /\
  rw_tree_cost var_cost op_cost output <= rw_tree_cost var_cost op_cost input.
```

The extractor considers finite-height witnesses and retains a cheapest candidate per class per
round. Removing a repeated class on a witness path cannot increase additive natural cost; thus an
optimal witness exists within the number of canonical classes whenever any witness exists.
Equal-cost choices break ties by smaller tree size and then structural order, so a zero-cost cycle
does not create a cyclic output. No productivity premise is needed for extraction: a class with
no finite witness returns `None`.
