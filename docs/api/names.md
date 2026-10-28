# Public names

Each entry gives its kind and meaning; the heading gives its owning file and card. The linked API
document owns the full signature and statement. Internal representations are not public names.

## Collections

Contract: [Collections](collections.md).

### `CollectionsEncoding.v` — COL-1a

- `encoding` — Record; injective conversion from keys to positive codes.
- `Encoding` — constructor; builds an encoding from a code function and injectivity proof.
- `encode`, `encode_injective` — fields; select the key code and its injectivity proof.
- `positive_encoding`, `N_encoding`, `nat_encoding`, `Z_encoding` — Definitions; number encodings.
- `bool_encoding`, `unit_encoding` — Definitions; Boolean and unit encodings.
- `option_encoding`, `sum_encoding` — Definitions; encodings of options and sums.
- `pair_encoding`, `list_encoding` — Definitions; linear bit-list encodings of pairs and lists.

### `CollectionsTrie.v` — COL-1b

- `Trie.t` — Type; canonical binary trie, with its representation internal to the module.
- `Trie.empty`, `Trie.is_empty` — Definitions; empty trie and emptiness test.
- `Trie.get`, `Trie.set`, `Trie.remove` — Definitions; lookup, update and removal by code.
- `Trie.map`, `Trie.combine` — Definitions; map values and combine tries position-wise.
- `Trie.fold`, `Trie.elements`, `Trie.size` — Definitions; ordered fold, bindings and count.
- `Trie.beq` — Definition; compares trie values at each position.
- `Trie.forall2` — Definition; short-circuit relation test over the first trie's bindings.
- `Trie.union_opt`, `Trie.union_with` — Definitions; combine overlaps and share one-sided subtrees.
- `Trie.key_lt` — Fixpoint; trie traversal order on positive codes.
- `Trie.extensionality` — Theorem; equal lookups imply equal canonical tries.
- `Trie.get_empty`, `Trie.is_empty_spec` — Theorems; characterise the empty trie and test.
- `Trie.get_set_same`, `Trie.get_set_other` — Theorems; lookup after setting a code.
- `Trie.get_remove_same`, `Trie.get_remove_other` — Theorems; lookup after removing a code.
- `Trie.get_map`, `Trie.get_combine` — Theorems; mapping and combining act at each position.
- `Trie.elements_sound`, `Trie.elements_complete` — Theorems; bindings and lookups agree.
- `Trie.elements_nodup`, `Trie.elements_sorted` — Theorems; bindings have distinct sorted codes.
- `Trie.fold_elements`, `Trie.size_elements` — Theorems; fold and size agree with bindings.
- `Trie.beq_pointwise`, `Trie.beq_correct` — Theorems; comparison is pointwise and decides equality.
- `Trie.forall2_spec` — Theorem; relates the traversal test to every first-trie binding.
- `Trie.get_union_with`, `Trie.union_with_combine` — Theorems; union agrees with pointwise combine.

### `CollectionsMap.v` — COL-1c

- `Map.t` — Definition; trie storing keys and values at encoded positions.
- `Map.empty`, `Map.wf` — Definitions; empty map and key-position invariant.
- `Map.code_get`, `Map.get` — Definitions; read a position or an encoded key.
- `Map.set`, `Map.remove`, `Map.map` — Definitions; update, remove or transform values.
- `Map.combine`, `Map.union_with` — Definitions; combine maps and share one-sided unions.
- `Map.fold`, `Map.elements`, `Map.size` — Definitions; ordered fold, bindings and count.
- `Map.is_empty`, `Map.mem` — Definitions; test emptiness and key membership.
- `Map.of_list` — Definition; build a map, keeping the last binding of each key.
- `Map.beq`, `Map.forall2` — Definitions; compare values and test first-map bindings.
- `Map.get_code`, `Map.code_get_empty` — Theorems; encoded lookup and empty position lookup.
- `Map.code_get_combine`, `Map.code_get_union_with` — Theorems; position-wise combination laws.
- `Map.forall2_spec` — Theorem; the relation test covers every first-map position.
- `Map.wf_union_with`, `Map.wf_empty`, `Map.wf_set` — Theorems; these operations preserve `wf`.
- `Map.wf_remove`, `Map.wf_map`, `Map.wf_combine` — Theorems; these operations preserve `wf`.
- `Map.wf_of_list` — Theorem; a map built from a list is well formed.
- `Map.mem_spec`, `Map.is_empty_spec` — Theorems; membership and emptiness tests reflect lookups.
- `Map.get_empty`, `Map.get_set_same`, `Map.get_set_other` — Theorems; empty and updated lookups.
- `Map.get_remove_same`, `Map.get_remove_other` — Theorems; lookup after removal.
- `Map.get_map`, `Map.get_combine` — Theorems; lookup after mapping and combining.
- `Map.get_of_list` — Theorem; lookup finds the last binding of a key in the input list.
- `Map.extensionality` — Theorem; well-formed maps with equal lookups are equal.
- `Map.elements_sound`, `Map.elements_complete` — Theorems; well-formed bindings and lookups agree.
- `Map.elements_nodup` — Theorem; a well-formed map's binding keys are distinct.
- `Map.fold_elements`, `Map.size_elements` — Theorems; fold and size agree with bindings.
- `Map.beq_correct` — Theorem; value comparison reflects lookup equality for well-formed maps.

### `CollectionsFinSet.v` — COL-1c

- `FinSet.t`, `FinSet.wf`, `FinSet.empty` — Definitions; finite sets, well-formedness and empty set.
- `FinSet.mem`, `FinSet.add`, `FinSet.remove` — Definitions; membership and single-key updates.
- `FinSet.union`, `FinSet.inter`, `FinSet.diff` — Definitions; union, intersection and difference.
- `FinSet.subset` — Definition; inclusion test using a short-circuit traversal.
- `FinSet.elements`, `FinSet.size`, `FinSet.is_empty` — Definitions; members, count and emptiness.
- `FinSet.of_list` — Definition; set of the keys in a list.
- `FinSet.mem_empty`, `FinSet.mem_add`, `FinSet.mem_remove` — Theorems; membership after updates.
- `FinSet.mem_union`, `FinSet.mem_inter`, `FinSet.mem_diff` — Theorems; membership in set algebra.
- `FinSet.of_list_spec` — Theorem; membership in a set built from a list is list membership.
- `FinSet.wf_ops` — Theorem; finite-set operations preserve well-formedness.
- `FinSet.extensionality`, `FinSet.subset_spec` — Theorems; extensionality and inclusion by members.
- `FinSet.elements_spec`, `FinSet.elements_nodup` — Theorems; members are listed exactly once.
- `FinSet.size_elements` — Theorem; size is the length of the elements list.
- `FinSet.mem_code`, `FinSet.union_code`, `FinSet.inter_code` — Theorems; position-level laws.
- `FinSet.diff_code`, `FinSet.subset_code` — Theorems; difference and inclusion at positions.
- `FinSet.is_empty_spec` — Theorem; emptiness is absence of members for a well-formed set.
- `FinSet.size_subset`, `FinSet.size_lt` — Theorems; inclusion bounds size, strictly if proper.
- `FinSet.size_le_length` — Theorem; a set inside a finite list is no larger than that list.
- `FinSet.union_comm`, `FinSet.union_assoc`, `FinSet.union_idem` — Theorems; union algebra.
- `FinSet.union_empty_r` — Theorem; empty set is a right identity for union.
- `FinSet.inter_comm`, `FinSet.inter_assoc`, `FinSet.inter_idem` — Theorems; intersection algebra.
- `FinSet.inter_empty_r` — Theorem; intersection with empty is empty.
- `FinSet.inter_union_distr` — Theorem; intersection distributes over union.
- `FinSet.union_inter_absorb` — Theorem; union absorbs intersection with itself.
- `FinSet.diff_self` — Theorem; a well-formed set minus itself is empty.

### `CollectionsHeap.v` — COL-2

- `PQueue.t`, `PQueue.wf`, `PQueue.empty` — Definitions; queue, invariant and empty queue.
- `PQueue.is_empty`, `PQueue.size` — Definitions; queue emptiness and live-key count.
- `PQueue.push`, `PQueue.pop` — Definitions; insert or lower a priority and remove a minimum.
- `PQueue.priority`, `PQueue.members` — Definitions; read live priorities and list held pairs.
- `PQueue.before` — Definition; lexicographic order on priority and key code.
- `PQueue.wf_empty`, `PQueue.priority_empty` — Theorems; empty queue is valid and has no priority.
- `PQueue.priority_push_same`, `PQueue.priority_push_other` — Theorems; priorities after push.
- `PQueue.size_push_new`, `PQueue.size_push_old` — Theorems; size after inserting or lowering.
- `PQueue.wf_push` — Theorem; push preserves queue well-formedness.
- `PQueue.pop_none`, `PQueue.pop_min` — Theorems; pop detects emptiness and returns a minimum.
- `PQueue.pop_rest`, `PQueue.wf_pop` — Theorems; pop removes exactly its key and preserves `wf`.
- `PQueue.members_spec`, `PQueue.members_nodup` — Theorems; members list live priorities once.
- `PQueue.size_members`, `PQueue.is_empty_spec` — Theorems; size and emptiness reflect live keys.

### `CollectionsUnionFind.v` — COL-2

- `UnionFind.t` — Record; parent and rank maps with an upper rank bound.
- `UnionFind.Forest` — constructor; builds a persistent union-find forest.
- `UnionFind.parents`, `UnionFind.ranks`, `UnionFind.max_rank` — fields; maps and rank bound.
- `UnionFind.make` — Definition; forest where every key is alone.
- `UnionFind.find` — Definition; representative and forest with compressed path.
- `UnionFind.union` — Definition; merge classes by rank.
- `UnionFind.equiv`, `UnionFind.equivb` — Definitions; class equivalence and threaded Boolean test.
- `UnionFind.keys` — Definition; distinct keys in parent or rank support.
- `UnionFind.wf` — Definition; map well-formedness and strictly increasing bounded parent ranks.
- `UnionFind.of_unions` — Definition; apply a list of unions to a fresh forest.
- `UnionFind.equiv_equivalence` — Theorem; class equivalence is an equivalence relation.
- `UnionFind.wf_make`, `UnionFind.wf_find`, `UnionFind.wf_union` — Theorems; forest invariants.
- `UnionFind.find_rep_stable` — Theorem; compression preserves representatives.
- `UnionFind.find_rep_canonical` — Theorem; a representative represents itself.
- `UnionFind.make_equiv`, `UnionFind.union_equiv` — Theorems; fresh classes and union semantics.
- `UnionFind.of_unions_equiv` — Theorem; classes are the equivalence closure of listed unions.
- `UnionFind.equivb_correct` — Theorem; the Boolean test and returned forest preserve equivalence.
- `UnionFind.keys_support` — Theorem; a key outside support has no distinct equivalent key.
- `UnionFind.keys_make`, `UnionFind.keys_union` — Theorems; support of fresh and merged forests.
- `UnionFind.keys_nodup` — Theorem; a well-formed forest's support has no duplicate keys.

### `CollectionsTable.v` — COL-2

- `Table.key`, `Table.t`, `Table.wf` — Definitions; list-key encoding, flat map and invariant.
- `Table.empty`, `Table.is_empty` — Definitions; empty table and emptiness test.
- `Table.get`, `Table.set`, `Table.remove` — Definitions; lookup, update and removal by list key.
- `Table.fold`, `Table.elements`, `Table.size` — Definitions; ordered fold, bindings and count.
- `Table.get_empty`, `Table.get_set_same`, `Table.get_set_other` — Theorems; empty and set lookups.
- `Table.get_remove_same`, `Table.get_remove_other` — Theorems; lookup after removal.
- `Table.wf_empty`, `Table.wf_set`, `Table.wf_remove` — Theorems; table invariants.
- `Table.extensionality` — Theorem; well-formed tables with equal lookups are equal.
- `Table.elements_sound`, `Table.elements_complete` — Theorems; table bindings and lookups agree.
- `Table.elements_nodup` — Theorem; well-formed table binding keys are distinct.
- `Table.fold_elements`, `Table.size_elements` — Theorems; fold and size agree with bindings.
- `Table.is_empty_spec` — Theorem; well-formed table emptiness is absence of lookups.

## Order

Contract: [Order](order.md).

### `OrderLattice.v` — ORD-1

- `lattice` — Record; comparison, bottom, join, widening and narrowing operations.
- `Lattice` — constructor; builds the operations of a lattice.
- `leb`, `bot`, `join`, `widen`, `narrow` — fields; select lattice operations.
- `lattice_laws` — Record; preorder, bottom, upper-bound and narrowing laws.
- `leb_refl`, `leb_trans`, `bot_least` — fields; preorder and least-bottom laws.
- `join_upper_l`, `join_upper_r`, `widen_upper_l`, `widen_upper_r` — fields; upper-bound laws.
- `narrow_lower`, `narrow_upper` — fields; narrowing bounds.
- `lub_laws`, `join_least` — Record and field; join is the least upper bound.
- `top`, `Top` — Record and constructor; greatest lattice element with proof.
- `top_value`, `top_greatest` — fields; select the top element and its greatest-element proof.
- `height`, `Height` — Record and constructor; bounded rank growing on strict joins.
- `rank`, `bound`, `rank_bounded`, `join_rank_grows` — fields; height rank and growth laws.
- `widening_rank`, `WideningRank` — Record and constructor; rank controlling widening steps.
- `wrank`, `widen_rank_stable`, `widen_rank_progress` — fields; rank and widening laws.
- `eqb_spec` — Definition; Boolean equality reflects equality.
- `equivalent` — Definition; two elements are below each other.
- `meet_laws` — Record; meet is a greatest lower bound.
- `meet_lower_l`, `meet_lower_r`, `meet_greatest` — fields; meet bounds and greatestness.
- `monotone_height`, `MonotoneHeight` — Record and constructor; height monotone in the order.
- `base_height`, `rank_monotone` — fields; height and its rank monotonicity proof.
- `bounded_widening_rank`, `BoundedWideningRank` — Record and constructor; bounded widening rank.
- `base_wrank`, `wbound`, `wrank_bounded` — fields; widening rank and its uniform bound.
- `height_wrank` — Definition; derives a bounded widening rank when widening is join.
- `join_monotone` — Theorem; least-upper-bound joins are monotone in both arguments.
- `join_bot_equivalent` — Theorem; joining bottom leaves an equivalent element.

### `OrderConcrete.v` — ORD-1

- `concretisation`, `Concretisation`, `gamma` — Record, constructor and field; forward meaning.
- `concretisation_laws`, `gamma_monotone` — Record and field; forward meaning is monotone.
- `agreement`, `Agreement`, `agree` — Record, constructor and field; backward agreement relation.
- `agreement_laws`, `agree_refl`, `agree_antitone` — Record and fields; agreement laws.
- `bottom_empty`, `gamma_bot_empty` — Record and field; bottom denotes no concrete value.
- `top_full`, `gamma_top_full` — Record and field; top denotes every concrete value.
- `agreement_equivalence`, `agree_sym`, `agree_trans` — Record and fields; agreement equivalence.
- `agreement_bot`, `agree_bot` — Record and field; bottom agrees on all pairs.
- `agreement_join_law`, `agree_join` — Record and field; agreement at both operands holds at join.
- `order_embedding` — Definition; a function preserves and reflects the Boolean order.
- `comap_gamma`, `comap_agree` — Definitions; pull meanings back along a carrier function.
- `gamma_join_l`, `gamma_join_r` — Theorems; each operand's meaning is contained in the join.
- `gamma_widen_l`, `gamma_widen_r` — Theorems; widening contains each operand's meaning.
- `gamma_narrow` — Theorem; narrowing contains the lower operand's meaning under its premise.
- `agree_join_l`, `agree_join_r` — Theorems; join agreement implies each operand's agreement.
- `agree_widen_l`, `agree_widen_r` — Theorems; widening agreement implies operand agreement.
- `comap_gamma_laws`, `comap_gamma_bot_empty` — Theorems; pulled-back concretisation laws.
- `comap_gamma_top_full` — Theorem; the pullback preserves full top under its premises.
- `comap_agree_laws`, `comap_agree_bot`, `comap_agree_join` — Theorems; pulled-back agreement laws.

### `OrderMonotone.v` — ORD-1

- `fun_leb` — Definition; pointwise order on assignments.
- `monotone_fun`, `monotone_fun2` — Definitions; monotonicity in one or two inputs.
- `monotone_on_assignments` — Definition; monotonicity from pointwise-ordered assignments.
- `monotone_id`, `monotone_const`, `monotone_compose` — Theorems; monotonicity closure rules.
- `monotone_join` — Theorem; join is monotone in both inputs with least-upper-bound laws.
- `monotone_on_const`, `monotone_on_lookup` — Theorems; constant and assignment lookup monotonicity.
- `monotone_on_join`, `monotone_on_compose` — Theorems; assignment monotonicity closure rules.
- `fun_leb_preorder` — Theorem; pointwise assignment order is reflexive and transitive.

### `OrderFlat.v` — ORD-1

- `flat` — Inductive; bottom, a value or top.
- `FBot`, `FVal`, `FTop` — constructors; form the three flat-domain cases.
- `flat_lattice`, `flat_top`, `flat_height` — Definitions; flat lattice, top and height.
- `flat_gamma`, `flat_agree` — Definitions; forward and backward meanings of flat values.
- `flat_laws`, `flat_lub` — Theorems; flat lattice satisfies lattice and least-upper-bound laws.
- `flat_gamma_laws`, `flat_gamma_bot_empty` — Theorems; flat concretisation laws and empty bottom.
- `flat_gamma_top_full` — Theorem; flat top denotes every concrete value.
- `flat_agree_laws`, `flat_agree_bot` — Theorems; flat agreement laws and bottom agreement.

### `OrderLift.v` — ORD-1

- `option_lattice`, `lift_bot` — Definitions; lattice and carrier with an added bottom.
- `Unreached`, `Reached`, `lift_bot_lattice` — notations; option constructors and lattice alias.
- `option_top`, `option_height`, `option_wrank` — Definitions; lifted top and termination evidence.
- `option_gamma`, `option_agree` — Definitions; meanings for the added-bottom carrier.
- `lift_bot_gamma`, `lift_bot_agree` — notations; aliases for option meanings.
- `lift_top` — Inductive; carrier with an added top.
- `Elem`, `Unknown` — constructors; original value and added top.
- `lift_top_lattice`, `lift_top_top`, `lift_top_height` — Definitions; lifted lattice and evidence.
- `lift_top_gamma`, `lift_top_agree` — Definitions; meanings for the added-top carrier.
- `option_laws`, `option_lub` — Theorems; added-bottom lattice and least-upper-bound laws.
- `option_gamma_laws`, `option_gamma_bot_empty` — Theorems; lifted concretisation and empty bottom.
- `option_agree_laws`, `option_agree_bot`, `option_agree_join` — Theorems; lifted agreement laws.
- `lift_top_laws`, `lift_top_lub` — Theorems; added-top lattice and least-upper-bound laws.
- `lift_top_gamma_laws`, `lift_top_gamma_top_full` — Theorems; added-top concretisation laws.
- `lift_top_agree_laws`, `lift_top_agree_bot`, `lift_top_agree_join` — Theorems; agreement laws.

### `OrderProduct.v` — ORD-1

- `product_lattice` — Definition; componentwise product lattice.
- `product_top`, `product_height`, `product_wrank` — Definitions; product top and termination.
- `product_gamma`, `product_agree` — Definitions; meanings requiring both components.
- `product_laws`, `product_lub` — Theorems; product lattice and least-upper-bound laws.
- `product_gamma_laws`, `product_gamma_bot_empty` — Theorems; product concretisation laws.
- `product_agree_laws`, `product_agree_join` — Theorems; product agreement laws.
- `monotone_fst`, `monotone_snd`, `monotone_pair` — Theorems; product monotonicity closure.

### `OrderReduced.v` — ORD-1

- `reduction_laws` — Record; reduction is decreasing, monotone and idempotent up to order.
- `reduce_lower`, `reduce_monotone`, `reduce_idempotent` — fields; the reduction laws.
- `reduction_sound`, `reduce_gamma` — Record and field; reduction preserves concrete meanings.
- `reduced_lattice` — Definition; product lattice with reduction in comparison, join and narrowing.
- `reduced_top`, `reduced_wrank` — Definitions; reduced-product top and widening-rank evidence.
- `reduced_laws`, `reduced_gamma_laws` — Theorems; reduced lattice and concretisation laws.
- `reduce_gamma_exact` — Theorem; sound reduction preserves the product meaning exactly.
- `reduced_top_full` — Theorem; reduced-product top denotes all values under its premises.

### `OrderDual.v` — ORD-1

- `dual_lattice` — Definition; reverses order and uses meet as join.
- `dual_top`, `dual_height` — Definitions; top and height evidence for the dual lattice.
- `dual_laws`, `dual_lub` — Theorems; dual lattice and least-upper-bound laws.

### `OrderBasic.v` — ORD-1

- `bool_lattice`, `bool_top`, `bool_height` — Definitions; Boolean lattice and its evidence.
- `bool_agree` — Definition; Boolean demand requires equality when true.
- `unit_lattice`, `unit_top`, `unit_height` — Definitions; one-element lattice and its evidence.
- `bool_laws`, `bool_lub` — Theorems; Boolean lattice and least-upper-bound laws.
- `bool_agree_laws`, `bool_agree_bot`, `bool_agree_join` — Theorems; Boolean agreement laws.
- `bool_agree_equivalence` — Theorem; Boolean agreement is an equivalence.
- `unit_laws`, `unit_lub` — Theorems; unit lattice and least-upper-bound laws.

### `OrderPowerset.v` — ORD-2

- `powerset_lattice` — Definition; finite sets ordered by inclusion.
- `powerset_gamma`, `powerset_agree` — Definitions; membership meaning and agreement on members.
- `must` — Inductive; all facts or a finite set of facts.
- `All`, `Only` — constructors; unrestricted and finite must-fact cases.
- `must_lattice`, `must_top`, `must_gamma` — Definitions; reverse-inclusion lattice and meaning.
- `within_set`, `finite_set` — Definitions; well-formed sets restricted to a finite universe.
- `finite_powerset_lattice`, `finite_powerset_top` — Definitions; finite powerset lattice and top.
- `finite_powerset_height` — Definition; size-based height for a duplicate-free universe.
- `finite_set_inter` — Definition; intersection of finite-universe sets.
- `finite_must_lattice`, `finite_must_top`, `finite_must_height` — Definitions; finite must lattice.
- `finite_clamp` — Definition; restricts a set to members of the universe.
- `finite_powerset_gamma`, `finite_powerset_agree` — Definitions; finite powerset meanings.
- `finite_must_embed`, `finite_must_gamma` — Definitions; finite must embedding and concretisation.
- `powerset_laws`, `powerset_lub` — Theorems; powerset lattice and least-upper-bound laws.
- `powerset_gamma_laws`, `powerset_gamma_bot_empty` — Theorems; powerset concretisation laws.
- `powerset_agree_laws`, `powerset_agree_bot` — Theorems; powerset agreement laws and bottom.
- `powerset_agree_join`, `powerset_agree_equivalence` — Theorems; agreement join and equivalence.
- `must_laws`, `must_lub` — Theorems; must lattice and least-upper-bound laws.
- `must_gamma_laws`, `must_gamma_bot_empty`, `must_gamma_top_full` — Theorems; must meanings.
- `finite_powerset_laws`, `finite_powerset_lub` — Theorems; finite powerset lattice laws.
- `finite_set_inter_meet` — Theorem; finite set intersection is a greatest lower bound.
- `finite_must_laws`, `finite_must_lub` — Theorems; finite must lattice laws.
- `finite_powerset_embedding`, `finite_must_embedding` — Theorems; finite-to-raw order embeddings.
- `finite_powerset_gamma_laws`, `finite_powerset_gamma_bot_empty` — Theorems; finite meanings.
- `finite_powerset_agree_laws` — Theorem; finite powerset agreement satisfies its laws.
- `finite_must_gamma_laws`, `finite_must_gamma_top_full` — Theorems; finite must meaning laws.
- `finite_clamp_mem`, `finite_clamp_in` — Theorems; clamp keeps exactly members in the universe.

### `OrderPointwise.v` — ORD-2

- `pointwise_lookup` — Definition; map lookup with a default for absent keys.
- `pointwise_lattice` — Definition; pointwise map lattice with bottom default.
- `pointwise_gamma`, `pointwise_agree` — Definitions; meanings for bottom-default maps.
- `pointwise_top_lattice`, `pointwise_top_gamma` — Definitions; maps with top default and meaning.
- `within_map`, `finite_map` — Definitions; well-formed maps restricted to a finite universe.
- `finite_pointwise_lattice`, `finite_pointwise_top` — Definitions; finite map lattice and top.
- `finite_pointwise_height`, `finite_pointwise_wrank` — Definitions; finite map termination proofs.
- `finite_pointwise_gamma`, `finite_pointwise_agree` — Definitions; finite map meanings.
- `finite_pointwise_top_lattice` — Definition; finite maps with top default and added bottom.
- `finite_pointwise_top_top`, `finite_pointwise_top_height` — Definitions; top and height evidence.
- `finite_map_clamp` — Definition; restricts a map to keys in the finite universe.
- `pointwise_laws`, `pointwise_lub` — Theorems; bottom-default pointwise lattice laws.
- `pointwise_gamma_laws`, `pointwise_agree_laws` — Theorems; pointwise meaning laws.
- `pointwise_agree_bot`, `pointwise_agree_join` — Theorems; pointwise agreement bottom and join.
- `pointwise_top_laws`, `pointwise_top_lub` — Theorems; top-default pointwise lattice laws.
- `pointwise_top_gamma_laws`, `pointwise_top_gamma_bot_empty` — Theorems; top-default meanings.
- `finite_pointwise_laws`, `finite_pointwise_lub` — Theorems; finite pointwise lattice laws.
- `monotone_pointwise_lookup`, `monotone_finite_pointwise_lookup` — Theorems; lookup monotonicity.
- `finite_pointwise_top_laws`, `finite_pointwise_top_lub` — Theorems; finite top-default laws.
- `finite_pointwise_top_embedding`, `finite_pointwise_embedding` — Theorems; finite map embeddings.
- `finite_pointwise_gamma_laws`, `finite_pointwise_agree_laws` — Theorems; finite map meaning laws.
- `finite_map_clamp_get` — Theorem; clamp keeps each lookup at a universe key.

### `OrderDisjunction.v` — ORD-2

- `join_all` — Definition; joins a list of lattice elements.
- `disjunction_leb` — Definition; tests whether each disjunct lies below an opposing disjunct.
- `compact` — Definition; collapses excess disjuncts by joining them.
- `disjunction_lattice`, `disjunction_wrank` — Definitions; capped disjunction lattice and rank.
- `disjunction_gamma` — Definition; union of the meanings of disjuncts.
- `disjunction_laws`, `disjunction_join_size` — Theorems; disjunction laws and join size bound.
- `disjunction_gamma_laws`, `disjunction_gamma_bot_empty` — Theorems; disjunction meaning laws.
- `monotone_join_all` — Theorem; elementwise ordered lists have ordered joins.

## Rules

Contract: [Rules](rules.md).

### `RulesSyntax.v` — RUL-1a

- `tuple` — Definition; a list of encoded constants.
- `term` — Inductive; a variable or an encoded constant.
- `TVar`, `TConst` — constructors; form variable and constant terms.
- `atom` — Record; a predicate and its argument terms.
- `Atom` — constructor; forms an atom from a predicate and argument terms.
- `pred`, `args` — fields; select an atom's predicate and arguments.
- `literal` — Inductive; a positive or negative atom.
- `LPos`, `LNeg` — constructors; form positive and negative literals.
- `rule` — Record; a head atom and body literals.
- `Rule` — constructor; forms a rule from its head and body.
- `head`, `body` — fields; select the head and body of a rule.
- `program` — Record; predicate encoding, arities and rules.
- `Program` — constructor; forms a program from its encoding, arities and rules.
- `penc`, `arity`, `rules` — fields; select the encoding, arities and rules of a program.
- `ground_atom` — Definition; a predicate paired with a tuple of constants.
- `lit_atom` — Definition; extracts the atom of a literal.
- `atom_vars` — Definition; lists variables occurring in an atom.
- `inst` — Definition; instantiates a term under a variable valuation.
- `ground` — Definition; instantiates an atom into a ground fact.
- `safe_rule` — Definition; requires head and negative variables in a positive literal.
- `program_wf` — Definition; requires safe rules and correct atom and fact arities.

### `RulesStratify.v` — RUL-1a

- `stratification` — Record; assigns predicate levels and a level count.
- `Stratification` — constructor; forms a stratification from levels and their bound.
- `level`, `count` — fields; select the predicate levels and their bound.
- `stratified` — Definition; checks level bounds and positive and negative dependencies.
- `stratify` — Definition; computes a stratification or reports failure.
- `stratify_sound` — Theorem; a computed stratification satisfies `stratified`.
- `stratify_complete` — Theorem; a stratifiable program receives a stratification.

### `RulesCompile.v` — RUL-1a

- `tuple_encoding` — Definition; encodes tuples as positive keys.
- `preds` — Definition; collects predicates occurring in rules and facts.
- `constants` — Definition; collects constants occurring in rules and facts.
- `in_universe` — Definition; tests a predicate and tuple against the finite universe.
- `herbrand` — Definition; proof-only list of tuples in the program universe.
- `relation` — Definition; finite tuple set inside the proof-only universe.
- `relation_lattice` — Definition; finite powerset lattice of relations.
- `restrict` — Definition; keeps a set's tuples inside a predicate's universe.
- `env_wf` — Definition; requires well-formed relations of the correct predicate arities.
- `fire_rule` — Definition; computes in-universe head tuples satisfying a rule body.
- `rconstraint` — Inductive; identifies a rule or fact constraint.
- `FromRule`, `FromFact` — constructors; identify rule and fact contributions.
- `rconstraint_encoding` — Definition; encodes rule and fact constraints.
- `stratum_system` — Definition; compiles one level into a constraint system.
- `stratum_static` — Definition; supplies static dependency evidence for that system.
- `herbrand_spec` — Theorem; characterises the tuples in the proof-only universe.
- `herbrand_nodup` — Theorem; the proof-only universe has no duplicate tuples.
- `restrict_spec` — Theorem; restriction keeps exactly the input's in-universe tuples.
- `fire_rule_exact` — Theorem; firing matches valuations satisfying a rule's body.
- `fire_rule_wf` — Theorem; firing produces a well-formed finite set.
- `fire_rule_complete` — Theorem; each satisfying in-universe valuation is fired.
- `stratum_system_monotone` — Theorem; a well-formed stratum system is monotone.

### `RulesModel.v` — RUL-1b

- `derives` — Inductive; derives facts and rule heads in one stratum.
- `derive_fact`, `derive_rule` — constructors; derive a fact or a satisfied rule head.
- `model_below` — Fixpoint; combines derivations below a given level.
- `perfect_model` — Definition; combines all strata of a stratification.
- `least_model` — Definition; selects the perfect model or the empty model on failure.
- `holds` — Definition; tests model membership of a predicate and tuple.
- `least_model_closed` — Theorem; the model contains facts and is closed under rules.
- `model_constants` — Theorem; derived atoms lie in their predicates' universes.

### `RulesSolve.v` — RUL-1b

- `database` — Definition; maps predicates to finite tuple sets.
- `rel_of` — Definition; reads a database relation, defaulting to the empty set.
- `db_holds` — Definition; tests a tuple's membership in a database relation.
- `solve_program` — Definition; solves each stratum and returns a database or failure.
- `represents` — Definition; relates well-formed database relations to a model.
- `stratum_post_solution_contains` — Theorem; a stratum post-solution contains its derivations.
- `stratum_reached_derives` — Theorem; every reached tuple has a stratum derivation.
- `stratum_least_is_derives` — Theorem; a least stratum solution contains exactly its derivations.
- `solve_program_exact` — Theorem; a well-formed stratifiable program yields its least model.
- `solve_program_none` — Theorem; an unstratifiable program yields no database.

## Float

Contract: [Float](float.md).

### `FloatInterval.v` — FLT-1

- `fle` — Definition; compares floats using the Flocq comparison.
- `subnormal` — Definition; identifies finite nonzero floats below the normal threshold.
- `fl_nn` — Definition; subtype of floats that are not NaNs.
- `fl_interval` — Record; bounds nonzero values and tracks NaN, zero and subnormal cases.
- `FlInterval` — constructor; builds an interval from bounds and flags.
- `flo`, `fhi` — fields; select lower and upper interval bounds.
- `may_nan`, `may_neg_zero`, `may_pos_zero`, `may_subnormal` — fields; track special cases.
- `fl_gamma` — Definition; states that a float belongs to an interval.
- `fl_lattice` — Definition; interval lattice with widening and narrowing.
- `fl_concretisation` — Definition; interval concretisation built from `fl_gamma`.
- `fl_top` — Definition; interval containing every float.
- `fl_top_lattice` — Definition; top evidence for the interval lattice.
- `fl_widening_rank` — Definition; bounded rank for interval widening.
- `fl_lattice_laws` — Theorem; interval lattice and concretisation satisfy their laws.
- `fl_top_sound` — Theorem; every float belongs to `fl_top`.
- `fl_bot_empty` — Theorem; the bottom interval contains no float.
- `subnormal_proper` — Theorem; a subnormal and a non-subnormal float exist.

### `FloatOps.v` — FLT-1

- `farith` — Inductive; arithmetic operators returning floats.
- `FAdd`, `FSub`, `FMul`, `FDiv` — constructors; select arithmetic operations.
- `fbop` — Inductive; arithmetic or less-than binary operation.
- `FArith`, `FLt` — constructors; select arithmetic and comparison operations.
- `nan_model` — Record; supplies NaN choices and their locality laws.
- `NanModel` — constructor; builds a NaN model from choices and proofs.
- `nan_choice`, `nan_neg`, `nan_abs` — fields; choose NaN results for the operations.
- `nan_choice_nan`, `nan_choice_local` — fields; require NaN results and local binary choice.
- `nan_neg_nan`, `nan_abs_nan` — fields; require NaN results for unary choices.
- `default_nan_model` — Definition; chooses one fixed quiet NaN for every operation.
- `fl_eval_bin` — Definition; evaluates float arithmetic with a NaN model.
- `fl_eval_neg`, `fl_eval_abs` — Definitions; evaluate negation and absolute value.
- `fl_lt` — Definition; tests float less-than, returning false for unordered values.
- `fl_bin` — Definition; computes an outward-rounded binary interval result.
- `fl_neg`, `fl_abs` — Definitions; compute interval negation and absolute value.
- `fl_assume_lt` — Definition; refines two intervals under a less-than assumption.
- `fl_bin_sound` — Theorem; binary interval evaluation contains the concrete result.
- `fl_neg_sound`, `fl_abs_sound` — Theorems; unary interval results contain concrete results.
- `fl_assume_lt_sound` — Theorem; comparison refinement retains satisfying operands.

### `FloatNan.v` — FLT-1

- `nan_demand` — Inductive; records whether a value and NaN sign or payload are demanded.
- `NotDemanded`, `Demanded` — constructors; select no demand or NaN observability flags.
- `ff_agree` — Definition; compares full floats under NaN sign and payload demands.
- `nan_agree` — Definition; compares floats under a `nan_demand`.
- `nan_domain` — Definition; demand lattice and agreement for float values.
- `nan_back` — Definition; computes operand demands from a binary operation and result demand.
- `nan_lattice_laws` — Theorem; the NaN demand lattice satisfies its lattice laws.
- `nan_domain_laws` — Theorem; NaN agreement satisfies its laws and is trivial at bottom.
- `nan_back_sound` — Theorem; computed operand demands preserve arithmetic result agreement.
- `fl_lt_agrees` — Theorem; NaN-identity agreement preserves comparison results.

### `FloatSsa.v` — FLT-1

- `fw` — Inductive; identifies the two float widths.
- `F32`, `F64` — constructors; select binary32 and binary64.
- `float_ext_tag` — Definition; assigns an extension tag to a width and operation.
- `float_ext_decode` — Definition; decodes valid float extension tags.
- `float_ext` — Definition; evaluates float extension tags on Ssa values.
- `float_ext_sigs` — Definition; lists the float extension operator signatures.
- `fl_any` — Inductive; represents unreachable, width-specific and arbitrary Ssa facts.
- `FlBot`, `FlA32`, `FlA64`, `FlOther` — constructors; form the four value-fact cases.
- `fl_any_lattice` — Definition; lattice of float and arbitrary Ssa facts.
- `fl_any_concretisation` — Definition; relates float facts to Ssa values.
- `fl_any_top` — Definition; top evidence for the Ssa float lattice.
- `fl_any_widening_rank` — Definition; bounded widening rank for the Ssa float lattice.
- `float_ssa_domain` — Definition; sparse value domain for float extension operations.
- `float_problem` — Definition; sparse float analysis problem for an Ssa function.
- `nan_domain_ssa` — Definition; NaN demand and agreement lifted to Ssa values.
- `ssa_nan_demand_view` — Definition; Ssa operand demands and backwards transfers.
- `float_ext_respects` — Theorem; extension evaluation respects the declared signatures.
- `float_ext_tag_decode` — Theorem; decoding a generated tag recovers its width and operation.
- `float_ext_decode_tag` — Theorem; a decoded tag is the tag of its decoded operation.
- `nan_domain_ssa_laws` — Theorem; the Ssa NaN demand domain satisfies its laws.
- `float_ssa_domain_laws` — Theorem; the sparse float value domain satisfies its laws.
- `ssa_float_value_sound` — Theorem; reachable Ssa values satisfy their computed float facts.
- `ssa_nan_demand_view_laws` — Theorem; the Ssa NaN demand view satisfies demand laws.
- `ssa_nan_demand_sound` — Theorem; agreeing initial states have the same behaviour.

## Graph

### `GraphCore.v` — GRA-1a

- `Graph.t`, `Graph.Make` — Record and constructor; graph with entries, nodes and labelled edges.
- `Graph.entries`, `Graph.nodes`, `Graph.out` — fields; entry nodes, all nodes and outgoing edges.
- `Graph.source`, `Graph.target` — fields; endpoints of an edge.
- `reachable`, `reachable_entry`, `reachable_step` — Inductive and constructors; entry
  reachability.
- `graph_wf` — Record; graph nodes and edge endpoints obey the graph invariants.
- `Build_graph_wf` — constructor; packages the graph well-formedness laws.
- `nodes_nodup`, `entries_in`, `out_source`, `out_target_in` — fields; graph well-formedness laws.
- `path`, `path_nil`, `path_cons` — Inductive and constructors; edge lists forming paths.
- `reaches`, `mutual` — Definitions; path reachability and mutual reachability.
- `acyclic`, `before` — Definitions; absence of nonempty cycles and strict list order.
- `set_entries`, `without`, `induced` — Definitions; change roots or restrict a graph by nodes.
- `edge_count` — Definition; sum of outgoing-list lengths over nodes.
- `reachable_iff_path`, `reachable_in_nodes` — Theorems; paths characterise reachability
  within nodes.

### `GraphPrepare.v` — GRA-1a

- `prepared`, `Prepared` — Record and constructor; indexed adjacency and binary traversal fuel.
- `out_index`, `in_index`, `fuel` — fields; successor and predecessor indexes and traversal bound.
- `prepare` — Definition; builds the indexes and fuel from a graph.
- `succ_edges`, `pred_edges` — Definitions; retrieve the indexed outgoing and incoming edges.
- `prepared_laws` — Record; the indexes agree with the graph and carry adequate fuel.
- `Build_prepared_laws` — constructor; packages prepared-index agreement and fuel laws.
- `succ_agrees`, `succ_domain` — fields; successor lists agree at nodes and are empty elsewhere.
- `pred_agrees`, `pred_domain`, `pred_nodup` — fields; predecessor membership, domain and
  uniqueness.
- `fuel_value` — field; fuel equals twice the node count plus the edge count and two.
- `ready` — Definition; graph well-formedness, unique outgoing edges and prepared-index laws.
- `reverse_graph`, `prepared_reverse` — Definitions; reverse edges and swap the prepared indexes.
- `prepare_ready`, `pred_edges_nodup` — Theorems; preparation is ready and predecessors are
  unique.
- `reverse_graph_ready`, `reverse_path` — Theorems; reversal preserves readiness and reverses
  paths.

### `GraphDfs.v` — GRA-1b

- `dfs_result`, `DfsResult` — Record and constructor; depth-first forest and traversal orders.
- `preorder`, `postorder`, `tree_edge` — fields; traversal orders and discovery edges.
- `pre_num`, `post_num`, `visited` — fields; traversal positions and reached nodes.
- `dfs`, `rpo` — Definitions; blocked iterative search and reverse postorder.
- `tree_parent`, `dfs_ancestor`, `ancestor_b` — Definitions; tree parent, ancestry and
  interval test.
- `retreating` — Definition; edge whose target is an ancestor of its source in the DFS forest.
- `dfs_exact`, `reachable_dfs`, `dfs_tree` — Theorems; exact search reachability and forest edges.
- `rpo_order`, `rpo_single_entry`, `rpo_parent_of_non_entry` — Theorems; reverse-postorder
  properties.
- `rpo_edge_classes`, `cycle_has_retreating_edge` — Theorems; edge classes and cycles in DFS.
- `ancestor_b_agrees` — Theorem; interval ancestry test agrees with DFS-tree ancestry.

### `GraphCertificate.v` — GRA-1b

- `check_path`, `tree_path` — Definitions; check an edge-list path and recover a DFS tree path.
- `check_path_correct`, `tree_path_valid` — Theorems; path checking and recovered paths are
  correct.

### `GraphDominators.v` — GRA-2a

- `dominates`, `strictly_dominates`, `immediately_dominates` — Definitions; semantic dominators.
- `dom_tree`, `DomTree` — Record and constructor; dominator forest with ancestry intervals.
- `idom`, `tin`, `tout` — fields; immediate dominators and forest traversal intervals.
- `idom_ancestor`, `forest_on` — Definitions; parent-map ancestry and forest well-formedness.
- `chk_idom`, `check_idom` — Definitions; candidate immediate dominators and exactness checker.
- `dom_tree_of`, `dominates_b` — Definitions; number a parent forest and test ancestry by
  intervals.
- `flat_idom`, `flat_tree` — Definitions; conservative fallback parent map and tree.
- `dominator_exact`, `dominator_tree` — Definitions; checker acceptance and total checked tree.
- `dominates_refl`, `dominates_trans` — Theorems; dominance is reflexive and transitive.
- `dominates_iff_unreachable_without` — Theorem; dominance corresponds to blocked reachability.
- `chk_idom_wf`, `check_idom_sound`, `check_idom_complete` — Theorems; candidate and checker laws.
- `dom_tree_of_agrees`, `flat_idom_shape` — Theorems; forest intervals and fallback shape.
- `dominator_tree_sound`, `dominator_tree_exact` — Theorems; total-tree soundness and checked
  exactness.

### `GraphEdgeDominance.v` — GRA-2b

- `edge_dominates` — Definition; every entry path to a node traverses the edge.
- `edge_dom_index`, `dominating_edges` — Definitions; indexed edge dominators and their node
  query.
- `edge_dominates_iff` — Theorem; characterises edge dominance through incoming edges and
  dominance.
- `dominating_edges_sound`, `dominating_edges_exact` — Theorems; sound and exact indexed queries.
- `self_loop_not_edge_dominating` — Theorem; a self-loop does not dominate first arrival at
  its node.

### `GraphPostDominators.v` — GRA-2b

- `post_dominates`, `post_dominator_tree` — Definitions; exit-path dominance and reversed tree.
- `post_dominates_iff_reverse` — Theorem; post-dominance is dominance in the reversed graph.
- `post_dominator_tree_sound`, `post_dominator_tree_exact` — Theorems; soundness and exactness.

### `GraphScc.v` — GRA-3a

- `scc_result`, `SccResult` — Record and constructor; components and their positive indexes.
- `components`, `component_ids`, `component_at`, `comp_of` — fields; component lists and indexes.
- `scc_within`, `scc` — Definitions; Tarjan components within a node list and the entire graph.
- `tarjan_frame`, `TarjanFrame` — Record and constructor; open node and remaining successor edges.
- `frame_node`, `frame_edges` — fields; node and remaining edges of a Tarjan frame.
- `tarjan_state`, `TarjanState` — Record and constructor; iterative Tarjan machine state.
- `frames`, `disc`, `low`, `pending`, `clock`, `emitted` — fields; stacks, numbers and output.
- `condensation` — Definition; component graph with original cross-component edges.
- `scc_within_exact`, `scc_exact` — Theorems; component partitions and mutual reachability.
- `scc_reverse_topological` — Theorem; components are emitted after those they reach.
- `condensation_correct` — Theorem; condensation is a well-formed DAG with the specified edges.

### `GraphDag.v` — GRA-3b

- `topological_order`, `topological_sort` — Definitions; topological ordering and its computation.
- `path_weight` — Definition; sum of edge weights along a path.
- `dag_paths`, `DagPaths` — Record and constructor; maximum entry-path weights and witnesses.
- `best`, `via` — fields; maximum weights and selected final edges.
- `max_paths`, `max_path_to` — Definitions; compute maximum paths and recover a witness.
- `topological_sort_correct`, `max_paths_exact`, `max_paths_cycle` — Theorems; sorting and paths.

### `GraphChain.v` — GRA-3b

- `forward_step` — Definition; unique outgoing edge of a forwarding node, when present.
- `chain`, `chain_stop`, `chain_move` — Inductive and constructors; finite forwarding chains.
- `resolution`, `Landing`, `Cyclic` — Inductive and constructors; a landing node or a cycle.
- `resolve`, `resolve_all` — Definitions; resolve one or all forwarding chains.
- `resolve_correct` — Theorem; resolution agrees with finite chains and cycle detection.

### `GraphReducible.v` — GRA-4a

- `back_edge`, `reducible`, `reducible_b` — Definitions; dominance back edge and reducibility
  test.
- `back_edge_retreating`, `reducible_iff_retreating_back` — Theorems; DFS characterisation.
- `reducible_b_sound`, `reducible_b_correct` — Theorems; test soundness and exact-tree
  correctness.

### `GraphNaturalLoops.v` — GRA-4a

- `natural_loop`, `natural_loop_nodes` — Definitions; natural-loop membership and reverse search.
- `natural_loop_nodes_exact` — Theorem; computed nodes match natural-loop membership.

### `GraphLoops.v` — GRA-4b

- `loop_forest`, `LoopForest` — Record and constructor; recursively nested loop components.
- `loop_headers`, `loop_nodes`, `loop_parent`, `loop_of` — fields; headers, members and nesting.
- `loop_forest_of`, `in_loop`, `outer_nodes` — Definitions; construct and inspect loop nesting.
- `strong_component` — Definition; maximal nonempty mutual-reachability class.
- `loop_forest_nested`, `loop_forest_exact`, `loop_forest_covers` — Theorems; nesting and
  cycle coverage.

### `GraphWto.v` — GRA-4c

- `wto_token`, `WVertex`, `WOpen`, `WClose` — Inductive and constructors; weak-order tokens.
- `wto` — Definition; flat list of weak-order tokens.
- `balanced_from`, `annotate` — Fixpoints; check nesting and attach enclosing-head stacks.
- `wto_order`, `wto_valid` — Definitions; textual vertex order and Bourdoncle validity.
- `check_wto`, `wto_of` — Definitions; weak-order checker and candidate producer.
- `wto_all_heads`, `wto_total` — Definitions; nested all-heads fallback and checked total
  producer.
- `check_wto_correct`, `wto_valid_cycles` — Theorems; checker correctness and cycle coverage.
- `wto_all_heads_valid`, `wto_total_valid` — Theorems; fallback and total producer are valid.

### `GraphFrontier.v` — GRA-5

- `in_df`, `in_idf`, `idf_step` — Definition, Inductive and constructor; frontier and closure.
- `dominance_frontier`, `iterated_frontier` — Definitions; compute frontiers and their closure.
- `dominance_chain` — Theorem; a runner chain identifies an edge's frontier witnesses.
- `dominance_frontier_exact`, `iterated_frontier_exact` — Theorems; computed frontiers are exact.

### `GraphControlDependence.v` — GRA-5

- `control_dependent`, `cdep` — Definitions; edge and node control dependence by post-dominance.
- `exits_reachable` — Definition; every graph node has a path to an exit.
- `control_deps` — Definition; index control-dependence edges by dependent node.
- `control_deps_exact` — Theorem; computed control-dependence edges match the semantic definition.

### `GraphInterference.v` — GRA-6a

- `interference`, `Interference` — Record and constructor; symmetric loop-free interference graph.
- `vertices`, `adjacent` — fields; graph vertices and neighbour sets.
- `empty_interference`, `neighbours`, `interferes` — Definitions; empty graph and adjacency
  queries.
- `interference_wf` — Record; graph symmetry, absence of self-loops and index well-formedness.
- `Build_interference_wf` — constructor; packages interference graph laws.
- `interferes_sym`, `interferes_irrefl`, `interferes_vertex` — fields; interference graph laws.
- `vertices_wf`, `adjacent_wf`, `neighbours_wf` — fields; set and map well-formedness.
- `add_point` — Definition; add interference from definitions and live values at a point.
- `add_point_exact`, `add_point_vertices`, `add_point_wf` — Theorems; observer-step properties.

### `GraphColour.v` — GRA-6a

- `colour_result`, `ColourResult` — Record and constructor; assigned colours and spilled vertices.
- `colours`, `spilled` — fields; colour assignments and spill list.
- `proper_colouring` — Record; range, coverage, adjacency and precolouring properties.
- `Build_proper_colouring` — constructor; packages proper-colouring laws.
- `colour_below_k`, `vertex_decided`, `spilled_uncoloured` — fields; colour and spill validity.
- `adjacent_differ`, `precoloured_kept` — fields; distinct neighbours and preserved precolouring.
- `check_colouring`, `precolour_ok` — Definitions; check a colouring and valid precolouring.
- `greedy_colour`, `all_spilled` — Definitions; greedy colouring and conservative spill fallback.
- `check_colouring_correct`, `greedy_colour_proper`, `greedy_no_spill` — Theorems; colouring laws.

### `GraphBriggs.v` — GRA-6b

- `briggs_colour`, `colour_checked` — Definitions; optimistic colouring and checked fallback.
- `degenerate` — Definition; graph admits complete simplification below the colour bound.
- `briggs_colour_proper`, `colour_checked_proper`, `briggs_no_spill` — Theorems; colouring
  guarantees.

## Fixpoint

### `FixpointQuery.v` — FIX-1

- `Query.t`, `Query.Ret`, `Query.Ask`, `Query.Side` — Inductive and constructors; query trees.
- `Query.eval`, `Query.reads`, `Query.sides` — Fixpoints; result, reads and contributions of a
  query.
- `Query.run` — Fixpoint; obtain result, reads and contributions in one traversal.
- `ask_all`, `side_all` — Fixpoints; sequence reads and contributions.
- `query_determined`, `run_spec` — Theorems; read agreement determines a query and `run` agrees.
- `ask_all_spec`, `side_all_spec` — Theorems; sequence helpers have the stated read and side
  effects.

### `FixpointSystem.v` — FIX-1

- `System.t`, `System.Make` — Record and constructor; a system of targeted query constraints.
- `System.constraints`, `System.target`, `System.rhs` — fields; constraints, targets and queries.
- `System.static`, `System.Static` — Record and constructor; declared reads and side targets.
- `System.deps`, `System.side_targets` — fields; declared reads and contributions for each
  constraint.
- `System.reads_within`, `System.sides_within` — fields; declarations cover actual reads and
  effects.
- `deps`, `side_targets` — Notations; aliases for static-system projections.
- `post_solution` — Definition; every result and contribution lies below its assigned unknown.
- `assignment`, `lookup` — Definitions; finite assignment and lookup with bottom default.
- `monotone_query`, `monotone_system` — Definitions; monotonicity of results and contributions.
- `top_post_solution` — Theorem; the constant top assignment satisfies every constraint.

### `FixpointIndex.v` — FIX-1

- `sys_index`, `SysIndex` — Record and constructor; indexes of contributors and readers.
- `contributors`, `readers` — fields; maps from unknowns to contributing and reading constraints.
- `index_system`, `contributors_of`, `readers_of` — Definitions; build and query static indexes.
- `sys_index_laws` — Record; membership agreement and uniqueness of index lists.
- `Build_sys_index_laws` — constructor; packages system-index agreement laws.
- `contributors_agree`, `readers_agree`, `index_nodup` — fields; index agreement and uniqueness.
- `index_system_laws` — Theorem; the constructed system index satisfies its laws.

### `FixpointCheck.v` — FIX-1

- `check_post` — Definition; check all constraint results and contributions against an assignment.
- `check_post_iff` — Theorem; the full checker decides the post-solution property.

### `FixpointCut.v` — FIX-1

- `cut_certificate`, `CutCertificate` — Record and constructor; cut values and recomputation plan.
- `cuts`, `stored`, `plan` — fields; cut points, stored values and non-cut evaluation order.
- `plan_valid` — Definition; plan coverage, uniqueness and dependency order.
- `expand` — Definition; check a cut certificate and recompute the remaining assignment.
- `replay` — Definition; fold an observer over unknowns and their assignment values.
- `expand_sound`, `expand_complete` — Theorems; accepted certificates and completeness conditions.
- `plan_valid_cuts` — Theorem; a valid plan's cut points intersect every flow cycle.
- `replay_invariant`, `replay_covers` — Theorems; observer invariants and certificate coverage.

### `FixpointLeast.v` — FIX-1

- `join_update`, `run_updates`, `apply_updates` — Definitions; collect and apply constraint
  updates.
- `raise`, `reached` — Definitions; one constraint run and assignments reachable from bottom.
- `least_solution` — Definition; post-solution below all post-solutions.
- `reached_below`, `reached_least`, `least_solution_unique` — Theorems; least-solution properties.

### `FixpointCycles.v` — FIX-1

- `flows`, `cuts_every_cycle` — Definitions; static unknown dependencies and cycle-cutting sets.

### `FixpointWorklist.v` — FIX-2a

- `scheduler`, `Scheduler` — Record and constructor; priorities and widening points.
- `priority`, `widening_point` — fields; queue priority and widening-site predicate.
- `strategy`, `Joining`, `Widening` — Inductive and constructors; update strategies.
- `dependencies`, `Declared`, `Recorded` — Inductive and constructors; static or observed reads.
- `dependencies_ok` — Definition; declared index laws or trivial recorded-dependency condition.
- `Engine.t`, `Engine.State` — Record and constructor; worklist engine state.
- `Engine.current`, `Engine.queue`, `Engine.recorded` — fields; values, pending constraints
  and reads.
- `initial_state`, `engine_step` — Definitions; initialize and advance the worklist engine.
- `engine_rel`, `engine_reachable` — Definitions; successor relation and reachable engine states.
- `engine_steps`, `steps_zero`, `steps_succ` — Inductive and constructors; finite engine runs.
- `outcome`, `Done`, `Pending` — Inductive and constructors; finished assignment or pending state.
- `then_run`, `loop` — Definition and Fixpoint; compose outcomes and run binary fuel.
- `run_worklist`, `solve_fuel` — Definitions; fuel-bounded run and sound top-fallback solver.
- `engine_finished_sound` — Theorem; a finished reachable engine state is a post-solution.
- `run_worklist_spec`, `run_worklist_sound`, `run_worklist_acc` — Theorems; run semantics and
  adequacy.

### `FixpointTotal.v` — FIX-2b

- `terminates` — Definition; height or widening-rank evidence and cycle-cutting widening points.
- `solve_total` — Definition; accessibility-based solver returning a proved post-solution.
- `engine_acc`, `run_worklist_adequate` — Theorems; evidence yields accessibility and enough fuel.
- `solve_fuel_exact`, `solve_total_run` — Theorems; sufficient fuel agrees with the solver run.
- `solve_total_reached`, `solve_total_least` — Theorems; joining reaches a least solution.

### `FixpointSchedule.v` — FIX-3

- `unknowns`, `dependency_graph` — Definitions; static unknowns and their flow graph.
- `rpo_scheduler`, `wto_scheduler`, `scc_scheduler` — Definitions; graph-based worklist
  schedulers.
- `plan_of` — Definition; derive a non-cut plan from cycle-cutting points.
- `unknowns_spec`, `dependency_graph_flows`, `dependency_graph_ready` — Theorems; graph
  construction.
- `rpo_scheduler_cuts`, `wto_scheduler_cuts`, `scc_scheduler_cuts` — Theorems; widening points
  cut cycles.
- `plan_of_valid` — Theorem; plan construction succeeds exactly for cycle-cutting points.

### `FixpointNarrow.v` — FIX-3

- `narrow_pass`, `narrow_checked` — Definitions; narrow assignments and check the resulting
  solution.
- `narrow_checked_post`, `narrow_checked_below` — Theorems; narrowing preserves soundness and
  decreases.

### `FixpointPartial.v` — FIX-4

- `closed_partial`, `dependency_closed` — Definitions; sound partial assignments and closed sets.
- `check_partial` — Definition; check constraints touching the explored set.
- `check_partial_correct` — Theorem; partial checker decides the closed-partial property.
- `closed_partial_extends`, `closed_partial_above_least` — Theorems; extension and
  least-solution bound.
- `post_solution_closed` — Theorem; a post-solution restricts to a dependency-closed partial
  solution.

### `FixpointLocal.v` — FIX-4

- `local_result`, `LocalResult` — Record and constructor; explored unknowns and their assignment.
- `explored`, `values` — fields; explored set and computed assignment.
- `local_solve`, `local_checked` — Definitions; local producer and checked partial solution.
- `local_checked_sound` — Theorem; accepted results cover roots and form a closed partial
  solution.

## Examples

Contract: [Examples](examples.md).

### `ExamplesWhileSyntax.v` — EX-1

- `var` — Definition; While variable identifier.
- `unop`, `binop` — Inductives; unary and binary word operators.
- `Neg`, `BNot`, `LNot`, `Add`, `Sub`, `Mul`, `And`, `Or`, `Xor`, `Shl`, `ShrU`, `ShrS`,
  `Eq`, `Ne`, `LtU`, `LeU`, `LtS`, `LeS` — constructors; While operators.
- `expr` — Inductive; While expression syntax.
- `EConst`, `EVar`, `EUn`, `EBin` — constructors; constants, variables and applications.
- `stmt` — Inductive; While statement syntax.
- `SSkip`, `SAssign`, `SSeq`, `SIf`, `SLoop`, `SBreak`, `SContinue`, `SOutput` — constructors;
  While statements.

### `ExamplesWhileSemantics.v` — EX-1

- `wrap32`, `signed32`, `eval_un`, `eval_bin` — Definitions; concrete 32-bit operator semantics.
- `store`, `update`, `eval_expr` — Definitions and Fixpoint; stores, updates and expression
  evaluation.
- `wframe`, `config`, `target_cont` — Inductives; control frames, configurations and jump targets.
- `KSeq`, `KJoin`, `KLoop`, `KExit`, `Run`, `Enter`, `WhileFin`, `JRun`, `JFin` — constructors;
  While control states.
- `jump_cont` — Definition; resolves a relative jump against control frames.
- `step_w` — Inductive; small-step execution with output events.
- `w_skip`, `w_assign`, `w_output`, `w_seq`, `w_if`, `w_loop`, `w_enter`, `w_break`, `w_continue`,
  `w_fin_seq`, `w_fin_join`, `w_fin_exit`, `w_fin_loop` — constructors; the While step rules.
- `while_semantics`, `while_endings`, `store_of_config`, `word_stores`, `var_encoding` —
  Definitions;
  semantics, endings, store projection, initial-store predicate and variable encoding.

### `ExamplesWhileBridge.v` — EX-4

- `un_bits`, `bin_bits`, `env2` — Definitions; translate word operators and construct operand
  environments.
- `un_bridge`, `bin_bridge`, `eval_expr_word` — Theorems; operator bridges and word preservation.

### `ExamplesWhileSkeleton.v` — EX-4

- `atom` — Inductive; atomic actions of the skeleton translation.
- `ANop`, `AAssign`, `AOutput` — constructors; While skeleton atoms.
- `loops_ok`, `to_skeleton` — Fixpoints; check loop depths and translate statements.
- `while_client` — Definition; While operations for the skeleton machine.
- `match_state` — Inductive; relates While configurations to skeleton states.
- `while_skeleton_bisimulation`, `match_state_initial`, `while_behaviour_transport` — Theorems;
  bisimulation, matching initial states and preservation of behaviour.

### `ExamplesWhileViews.v` — EX-4

- `while_skel_vars`, `while_var_view`, `while_region_alg` — Definitions; variable and region
  adapters.
- `while_effects`, `while_effects_view`, `while_demand_view`, `while_genkill_view`,
  `while_copy_view` —
  Definitions; While effects, demand, expression and copy adapters.
- `erase_dead`, `while_dce`, `while_erasure` — Fixpoint and Definitions; dead-assignment erasure.
- `while_client_laws`, `while_skel_vars_laws`, `to_skeleton_labels_ok`, `while_var_view_laws`,
  `while_effects_laws`, `while_demand_laws`, `while_genkill_laws`, `while_copy_sound`,
  `while_never_traps`, `while_erasure_laws`, `while_dce_sound` — Theorems; adapter laws and
  behaviour preservation of dead-code erasure.

### `ExamplesSsaSyntax.v` — EX-2

- `func`, `label`, `vid` — Definitions; function, block and value identifiers.
- `iw`, `msize`, `ty`, `cval`, `bop`, `sop`, `instr`, `callee`, `terminator` — Inductives;
  widths, types, values, operators and instructions.
- `W32`, `W64`, `M1`, `M2`, `M4`, `M8`, `TyI32`, `TyI64`, `TyPtr`, `TyFun`, `TyF32`, `TyF64`,
  `VInt`, `VPtr`, `VFun`, `VF32`, `VF64` — constructors; widths, types and concrete values.
- `BAdd`, `BSub`, `BMul`, `BDivU`, `BAnd`, `BOr`, `BXor`, `BShl`, `BShrU`, `BEq`, `BLtU`,
  `BLtS`, `OConst`, `OBin`, `OZext`, `OTrunc`, `OPtrAdd`, `OExt` — constructors; Ssa operators.
- `IOp`, `IAlloc`, `IFree`, `ILoad`, `IStore`, `IOutput`, `CDirect`, `CIndirect`, `TJump`, `TBr`,
  `TSwitch`, `TCall`, `TRet` — constructors; instructions, callees and terminators.
- `ty_of`, `valid_cval` — Definitions; concrete value type and integer word-range validity.
- `ssa_block`, `fdef`, `program` — Records; blocks, functions and programs.
- `SBlock`, `FDef`, `Program` — constructors; build blocks, functions and programs.
- `bparams`, `bbody`, `bterm`, `fentry`, `blocks`, `fresult`, `funcs`, `main`, `ext_sigs` — fields;
  select program structure and extension signatures.
- `find_func`, `find_block` — Definitions; look up functions and blocks.

### `ExamplesSsaTyping.v` — EX-2

- `iw_ty`, `op_sig`, `load_ok`, `static_ty`, `ext_respects`, `wf_program`, `wf_check`, `typed_env` —
  Definitions; typing, extension signatures, well-formedness and its checker.

### `ExamplesSsaTypingProofs.v` — EX-2

- `op_eval_typed`, `op_eval_valid`, `typed_state_reachable`, `typed_operands` — Theorems; operator
  and reachable-environment typing and integer ranges.
- `allocation_size_in_range`, `wf_check_sound`, `ext_respects_nil` — Theorems; allocation bounds,
  checker soundness and empty extension signatures.

### `ExamplesSsaSemantics.v` — EX-2

- `mval`, `event` — Inductives; memory fragments and observable events.
- `MInt`, `MFrag`, `EvOut`, `EvRet` — constructors; bytes and events.
- `mblock`, `sframe`, `state`, `limits` — Records; blocks, frames, machine states and limits.
- `MBlock`, `SFrame`, `State`, `Limits` — constructors; build machine state components.
- `msz`, `mbytes`, `mlive`, `msite`, `ffunc`, `flabel`, `fpc`, `fenv`, `fret`, `stack`, `mem`,
  `next_block`, `max_frames`, `max_blocks` — fields; select memory and machine state components.
- `op_eval`, `ssa_semantics`, `ssa_endings` — Definitions; operator evaluation and machine
  behaviour.
- `step_s` — Inductive; Ssa small-step semantics.

### `ExamplesSsaActivation.v` — EX-5a

- `astate` — Record; state of one function activation.
- `AState` — constructor; builds an activation state.
- `alabel`, `apc`, `aenv` — fields; select activation location and values.
- `activation`, `activation_endings` — Definitions; activation semantics and endings.

### `ExamplesSsaBridge.v` — EX-5a

- `ssa_truth`, `ssa_bridge` — Definitions; truth test and bridge to word expressions.
- `ssa_bridge_laws` — Theorem; the integer operator bridge is sound.

### `ExamplesSsaViews.v` — EX-5a

- `ssa_edge` — Record; slot-indexed Ssa graph edge.
- `SsaEdge` — constructor; builds an Ssa edge.
- `esrc`, `edst`, `eslot` — fields; select edge source, target and slot.
- `values_of`, `ssa_block_view`, `ssa_point_view` — Definitions; values and graph adapters.
- `instr_or_term` — Inductive; instruction or terminator.
- `AnInstr`, `ATerm` — constructors; embed an instruction or terminator.
- `call_site`, `ssa_effects`, `ssa_var_view`, `ssa_demand_view` — Definitions; call sites and
  adapters.
- `ssa_truth_nonzero`, `ssa_block_view_laws`, `ssa_var_view_laws`, `ssa_demand_view_laws` —
  Theorems;
  truth and Ssa adapter laws.

### `ExamplesSsaStrict.v` — EX-5c

- `frame_activation` — Definition; extracts an activation from a full state frame.
- `subtrace` — Inductive; subsequence relation on traces.
- `sub_nil`, `sub_keep`, `sub_skip` — constructors; empty, retained and skipped trace events.
- `ssa_strict_laws`, `activation_lifting` — Theorems; strict SSA and activation trace lifting.

### `ExamplesSsaEffects.v` — EX-5b

- `ssa_effects_view`, `ssa_calls`, `ssa_resolver` — Definitions; effects and call adapters.
- `ssa_effects_laws`, `ssa_calls_laws` — Theorems; the effects and calls views satisfy their laws.

### `ExamplesSsaMemory.v` — EX-6

- `full_node`, `ssa_full_view`, `ssa_mem_view` — Definitions; full-program graph and memory
  adapters.
- `full_edge` — Record; edge of the full-program graph.
- `FullEdge` — constructor; builds a full-program edge.
- `fsrc`, `fdst`, `fslot` — fields; select full-edge source, target and slot.
- `ssa_full_view_laws`, `ssa_mem_laws` — Theorems; graph and memory adapter laws.

### `ExamplesSsaPointers.v` — ANA-9

- `ssa_ptr_ops`, `ssa_ptr_view`, `ssa_footprints` — Definitions; pointer effects, view and
  footprints.
- `ssa_ptr_laws`, `ssa_zero_laws` — Theorems; pointer and zero-fact adapter laws.

### `ExamplesSsaBytes.v` — ANA-10

- `ssa_bytes_view` — Definition; byte view and coarse write ranges.
- `ssa_bytes_laws` — Theorem; byte view laws.

### `ExamplesWhileAnalyses.v` — EX-4, ANA-2

- `expr_encoding`, `while_live_at`, `while_needed`, `while_dead_var`, `loop_head`,
  `lcm_extended_view`, `lcm_avail`, `lcm_busy`, `lcm_avail2` — Definitions; EX-4 encodings,
  executable analysis wrappers and loop and code-motion fixtures.
- `while_liveness_sound`, `while_reaching_sound`, `while_zero_since_entry_sound`,
  `while_equality_sound`, `while_available_sound`, `while_busy_sound` — Theorems; EX-4
  specializations of dense analysis soundness.
- `while_structured_liveness_sound`, `while_certificate_sound`, `while_certificate_complete`,
  `while_region_table_agrees` — Theorems; ANA-2 structured analysis and certificate claims.
- `factorial_while`, `factorial_while_dce`, `z_var`, `lcm_prog`, `lcm_result_ex` — Definitions;
  EX-4 factorial and lazy-code-motion fixtures.
- `while_z_live`, `while_z_dead`, `while_dce_factorial`, `while_lcm_accepts` — Examples;
  EX-4 computed liveness, erasure and code-motion checks.

### `ExamplesSsaAnalyses.v` — EX-5a, ANA-3, ANA-5 to ANA-10

- `label_encoding`, `sop_encoding`, `const_numeric`, `const_conc`, `liveness_at` — Definitions;
  EX-5a encodings, constant domain and executable liveness wrapper.
- `ok_i32`, `mul_one_rules`, `mul_one_term`, `unit_cost` — Definitions; ANA-6 e-graph fixtures.
- `mul_one_rules_sound` — Theorem; ANA-6 validates the multiplication rewrite.
- `ssa_sccp_sound`, `ssa_guard_chain_sound` — Theorems; ANA-3 value and guard soundness.
- `ssa_dead_value_removable` — Theorem; EX-5a specializes neededness to an Ssa activation.
- `ssa_summary_sound`, `ssa_recursion_sound`, `ssa_unreachable_sound`, `ssa_stack_demand_sound`,
  `ssa_callee_leaf_sound` — Theorems; ANA-8 call and summary claims.
- `ssa_andersen_sound`, `ssa_steensgaard_sound`, `ssa_escape_sound` — Theorems; ANA-9 pointer
  and escape claims.
- `ssa_immutable_sound` — Theorem; ANA-10 preservation of unwritten bytes.
- `factorial_ssa`, `z_value`, `p_value`, `loop_header_point` — Definitions; EX-5a factorial fixture.
- `factorial_wf`, `factorial_z_live`, `factorial_z_dead`, `factorial_p_needed` — Examples; EX-5a
  computed typing, liveness and neededness checks.
- `gvn_prog`, `gvn_first`, `gvn_second`, `gvn_problem` — Definitions; ANA-5 numbering fixture.
- `gvn_merges` — Example; ANA-5 numbering accepts a common leader.
- `egraph_optimise_accepts` — Example; ANA-6 checks an e-graph rewrite.
- `count_up`, `count_up_n`, `count_up_chrec`, `count_up_inv` — Definitions; ANA-7 recurrence
  fixture.
- `scev_count_up_trip` — Example; ANA-7 computes and checks a trip count.
- `chain_graph`, `chain_writes`, `chain_writes_clobber`, `chain_reads`, `chain_ssa` — Definitions;
  ANA-10 MemorySSA fixtures.
- `memoryssa_accepts`, `memoryssa_rejects` — Examples; ANA-10 checks a valid and invalid
  clobber walk.

## Views

### `ViewsSemantics.v` — VIEW-1

- `semantics`, `Semantics` — Record, constructor; initial states and labeled steps from the anchors.
- `initial`, `step` — Fields; select initial states and labeled transitions.
- `endings`, `Endings` — Record, constructor; classify final, trapped, and stopped states.
- `final`, `trapped`, `stopped` — Fields; identify the three ending classes.
- `running`, `stuck` — Definitions; identify states with a step and states with no step
  or ending.
- `endings_wf` — Record; ending classes halt and are pairwise disjoint.
- `final_halts`, `trapped_halts`, `stopped_halts` — Fields; each ending class cannot step.
- `final_not_trapped`, `final_not_stopped`, `trapped_not_stopped` — Fields; endings are
  disjoint.
- `exec`, `exec_refl`, `exec_step` — Inductive, constructors; finite traced execution.
- `exec_in`, `exec_in_refl`, `exec_in_step` — Inductive, constructors; execution within
  a predicate.
- `diverges`, `diverges_step` — CoInductive, constructor; infinite execution.
- `reachable_state` — Definition; a state reached by a finite run from an initial state.
- `ending`, `EndFinal`, `EndTrap`, `EndStop`, `EndStuck` — Inductive, constructors;
  ending kinds.
- `ends_as` — Definition; a state has the given ending kind.
- `diverges_after` — Definition; divergence follows a finite trace.
- `same_behaviour` — Record; two states have equal finish, prefix, and divergence observations.
- `same_finish`, `same_prefix`, `same_diverging_prefix` — Fields; equal observable run sets.
- `bisimulation` — Record; lock-step matching of endings and steps in both directions.
- `bisim_ends`, `bisim_forth`, `bisim_back` — Fields; ending and step matching obligations.
- `stuttering` — Record; two-way matching with decreasing measures for unmatched silent steps.
- `st_ends_forth`, `st_ends_back` — Fields; match non-stuck endings after silent runs.
- `st_forth`, `st_back` — Fields; match steps or take a decreasing silent step.
- `bisimilar_same_behaviour` — Theorem; bisimilar states have equal observable behaviour.
- `stuttering_same_behaviour` — Theorem; stuttering-related states have equal behaviour.
- `same_behaviour_sym`, `same_behaviour_trans` — Theorems; behaviour equality is symmetric
  and transitive.
- `exec_in_exec`, `exec_in_app` — Theorems; restricted runs are runs and compose by trace
  append.

### `ViewsGraph.v` — VIEW-1

- `graph_view`, `GraphView` — Record, constructor; connect semantic states and steps to a graph.
- `cfg`, `point`, `taken`, `stays` — Fields; graph, state point, edge step, and point-preserving
  step.
- `graph_view_laws` — Record; graph and reachable semantic steps satisfy the view contract.
- `cfg_wf`, `entry_points`, `edge_covers` — Fields; graph validity, entries, and step coverage.
- `taken_edge`, `stays_point` — Fields; taken edges and stay steps agree with state points.
- `edges_of` — Definition; enumerate all graph out-edges.
- `dense_constraint`, `Seed`, `Flow` — Inductive, constructors; seed and edge-transfer
  constraints.
- `dense_constraint_encoding` — Definition; encode dense constraints using node and edge codes.
- `forward_system`, `forward_static` — Definitions; forward edge system and static dependencies.
- `backward_system`, `backward_static` — Definitions; backward edge system and static
  dependencies.
- `meets_every_cycle` — Definition; a node predicate visits each graph cycle.
- `run_edges`, `run_nil`, `run_cons`, `run_stay` — Inductive, constructors; edge history
  of a run.
- `last_writer` — Definition; last history edge writing a given value.
- `arrivals_since` — Definition; count back edges since the most recent entry edge.
- `forward_post_solution_iff`, `backward_post_solution_iff` — Theorems; characterize dense
  solutions.
- `forward_cuts_every_cycle`, `backward_cuts_every_cycle` — Theorems; graph cycle cuts
  cut flows.
- `run_edges_exec`, `exec_run_edges`, `run_edges_path` — Theorems; relate histories, runs,
  and paths.
- `run_edges_app`, `run_edges_snoc_inv` — Theorems; compose histories and decompose the
  last edge.
- `last_writer_snoc`, `arrivals_since_snoc` — Theorems; update history summaries for one edge.

### `ViewsForward.v` — VIEW-1

- `forward_inv` — Definition; reachable state satisfying the fact at its point.
- `forward_invariant_sound` — Theorem; forward post-solutions contain every reachable state.
- `forward_inv_invariant` — Theorem; the solution-relative forward predicate is an invariant.
- `forward_history_sound` — Theorem; forward facts contain the corresponding run histories.

### `ViewsAgreement.v` — VIEW-1

- `agreement_symmetric`, `agreement_swap` — Definitions; symmetry predicate and reversed
  agreement.
- `invariant_of` — Record; initial, preserved states are reachable.
- `inv_initial`, `inv_step`, `inv_reachable` — Fields; initiality, preservation, and
  reachability.
- `step_agrees`, `ends_agree`, `agreeing` — Definitions; step, ending, and state agreement
  obligations.
- `forth_agrees`, `ends_forth` — Definitions; one-direction step and ending matching
  obligations.
- `step_agrees2`, `ends_agree2`, `agreeing2` — Definitions; two-program matching and
  related states.
- `reachable_invariant` — Theorem; reachability satisfies `invariant_of`.
- `agreement_bisimulation` — Theorem; backward agreement obligations give a bisimulation.
- `agreement_same_behaviour` — Theorem; agreeing states have the same behaviour.
- `agreement_simulation2` — Theorem; two-program agreement gives a stuttering simulation.

### `ViewsSkeleton.v` — VIEW-2

- `Skeleton.stmt` — Inductive; structured statements with relative-depth jumps.
- `Skeleton.Atom`, `Skeleton.Seq`, `Skeleton.If` — Constructors; atom, sequence, and branch.
- `Skeleton.Block`, `Skeleton.Loop` — Constructors; enclosing exit and repetition labels.
- `Skeleton.Jump`, `Skeleton.JumpIf`, `Skeleton.JumpTable` — Constructors; relative-depth jumps.
- `dir`, `DFirst`, `DSecond`, `DBody` — Inductive, constructors; child directions in
  a statement.
- `position`, `dir_encoding`, `position_encoding` — Definitions; position paths and their
  encodings.
- `child`, `sub`, `positions` — Definition, fixpoints; select children, select subtrees,
  list positions.
- `labels_ok` — Fixpoint; check relative jump depths against enclosing labels.
- `skeleton_client`, `SkeletonClient` — Record, constructor; client store, atoms, guards,
  and jumps.
- `init_store`, `atom_step`, `atom_trap`, `atom_stop` — Fields; initial stores and atom
  outcomes.
- `guard_bool`, `guard_index`, `jump_effect` — Fields; guard evaluation and jump store effect.
- `skeleton_client_laws` — Record; jump totality and atom progress and ending laws.
- `jump_total`, `atom_progress` — Fields; jumps have an effect and atoms step, trap, or stop.
- `atom_trap_halts`, `atom_stop_halts`, `atom_trap_not_stop` — Fields; atom endings are
  exclusive.
- `frame`, `FSeq`, `FJoin`, `FBlock`, `FLoop` — Inductive, constructors; continuation
  stack frames.
- `mstate`, `Go`, `Ret` — Inductive, constructors; running and completed skeleton positions.
- `resume` — Fixpoint; unwind frames to a relative jump label.
- `skel_step` — Inductive; one skeleton-machine transition.
- `step_atom`, `step_seq`, `step_if`, `step_block`, `step_loop` — Constructors; enter or
  run nodes.
- `step_jump`, `step_jump_if_taken`, `step_jump_if_skipped`, `step_jump_table` — Constructors;
  jumps.
- `step_ret_seq`, `step_ret_join`, `step_ret_block`, `step_ret_loop` — Constructors;
  resume frames.
- `skeleton_semantics`, `skeleton_endings` — Definitions; machine semantics and ending
  predicates.
- `store_of`, `stack_of` — Definitions; extract store and continuation stack from a machine
  state.
- `positions_exact` — Theorem; listed positions are exactly valid subtree positions.
- `skeleton_endings_wf`, `skeleton_not_stuck` — Theorems; machine endings are valid and
  progress holds.

### `ViewsStructured.v` — VIEW-2

- `skel_point`, `PEntry`, `PExit` — Inductive, constructors; entry and exit points of
  a position.
- `skel_point_encoding` — Definition; encode a skeleton point.
- `action`, `AAtom`, `AGuard`, `AIndexIs`, `AIndexAtLeast`, `AJump` — Inductive, constructors;
  edge actions.
- `skel_edge`, `SkelEdge`, `from`, `slot` — Record, constructor, fields; edge source and slot.
- `skel_edge_encoding` — Definition; encode a skeleton edge by source and slot.
- `act_hold` — Definition; one action's relation on stores and traces.
- `acts_hold`, `holds_nil`, `holds_cons` — Inductive, constructors; sequential action execution.
- `label_point` — Definition; resolve a relative label to its skeleton point.
- `skel_out`, `skel_nodes`, `skel_to`, `skel_acts` — Definitions; graph edges, nodes,
  targets, actions.
- `skeleton_graph`, `skeleton_view` — Definitions; graph and semantic view of a skeleton.
- `loop_heads`, `is_loop_head` — Definitions; enumerate and test skeleton loop heads.
- `traps_at`, `stops_at` — Definitions; trap and stop conditions at skeleton points.
- `store_agreement` — Definition; lift store agreement to skeleton-machine states.
- `skel_root`, `edge_fwd`, `edge_bwd` — Definitions; root test and action-folded edge transfers.
- `skeleton_forward`, `skeleton_forward_static` — Definitions; forward system and static
  dependencies.
- `skeleton_backward`, `skeleton_backward_static` — Definitions; backward system and
  dependencies.
- `skeleton_view_laws_hold` — Theorem; the skeleton view satisfies the graph-view laws.
- `skeleton_forward_sound` — Theorem; skeleton forward facts contain reachable stores.
- `skeleton_agreement_bisimulation` — Theorem; backward skeleton agreement gives bisimulation.
- `skeleton_cut_points` — Theorem; loop heads meet every skeleton graph cycle.
- `skeleton_forward_cuts`, `skeleton_backward_cuts` — Theorems; loop heads cut both systems'
  flows.
- `is_loop_head_iff` — Theorem; loop-head test agrees with the list of loop heads.

### `ViewsRegion.v` — VIEW-3

- `summary_algebra`, `SummaryAlgebra` — Record, constructor; fold operations for skeleton
  statements.
- `on_atom`, `on_seq`, `on_if`, `on_block`, `on_loop` — Fields; summaries of ordinary
  constructors.
- `on_jump`, `on_jump_if`, `on_jump_table` — Fields; summaries of jump constructors.
- `summarise` — Fixpoint; fold a summary algebra over a skeleton.
- `algebra_sound` — Record; each algebra operation preserves a stated meaning.
- `sound_atom`, `sound_seq`, `sound_if`, `sound_block`, `sound_loop` — Fields; ordinary cases.
- `sound_jump`, `sound_jump_if`, `sound_jump_table` — Fields; jump cases preserve meaning.
- `escapes` — Definition; external relative label depths reached by a region's jumps.
- `falls`, `falls_at` — Definitions; possible normal completion of a region or position.
- `nesting`, `skel_depth` — Fixpoints; maximum enclosing-label and statement depths.
- `seq_flat`, `seq_of_list` — Fixpoint, definition; flatten sequences and build balanced
  sequences.
- `summarise_sound` — Theorem; a sound algebra's fold satisfies its meaning.
- `escapes_labels_ok` — Theorem; escaping labels characterize valid enclosing depths.
- `nesting_le_skel_depth`, `position_length_le_depth` — Theorems; skeleton depth bounds
  both measures.
- `seq_of_list_flat`, `seq_of_list_depth` — Theorems; balanced construction preserves order
  and depth.
- `falls_sound`, `frames_bounded` — Theorems; reachable completion and stack depth are bounded.

### `ViewsSsa.v` — VIEW-4

- `definition`, `Op`, `Param`, `Arbitrary` — Inductive, constructors; value definition forms.
- `guard_kind`, `GTrue`, `GFalse`, `GConst`, `GNotConst` — Inductive, constructors; guard tests.
- `condition`, `Condition`, `subject`, `kind` — Record, constructor, fields; value and
  guard test.
- `ssa_view`, `SsaView` — Record, constructor; SSA definitions, graph, values, and operations.
- `base`, `def`, `home`, `params` — Fields; graph and block definitions of values.
- `edge_args`, `edge_guard`, `val`, `op_eval`, `truth` — Fields; edges and concrete value
  semantics.
- `holds_guard`, `cond_holds`, `guard_ops_consistent` — Definitions; guard and operand
  consistency.
- `ssa_view_laws` — Record; SSA graph, guard, and value-origin properties.
- `base_laws`, `param_defs`, `guards_ok`, `guard_op_defined`, `value_origin` — Fields; SSA laws.
- `sparse_domain`, `SparseDomain` — Record, constructor; lattice and abstract SSA operations.
- `fact_lat`, `fact_conc`, `top_fact`, `op_abs` — Fields; sparse facts and abstract operation.
- `assume_value`, `assume_args` — Fields; refine a value or comparison arguments under a guard.
- `sparse_domain_laws` — Record; lattice, concretisation, transfer, and refinement soundness.
- `dom_lattice`, `dom_conc`, `fact_bot_empty`, `top_sound` — Fields; basic sparse domain laws.
- `op_sound`, `assume_value_sound`, `assume_args_sound` — Fields; operation and refinement laws.
- `executable` — Definition; test whether a lifted fact exceeds bottom.
- `sparse_unknown`, `UVal`, `UEdge`, `UBlock` — Inductive, constructors; sparse analysis
  unknowns.
- `sparse_unknown_encoding` — Definition; encode value, edge, and block unknowns.
- `sparse_constraint` — Inductive; sparse conditional constraint kinds.
- `CBlockEntry`, `CEntryFact`, `COp`, `CArbitrary` — Constructors; entry and value constraints.
- `CArg`, `CEdge`, `CBlock` — Constructors; edge argument, feasibility, and block constraints.
- `sparse_constraint_encoding` — Definition; encode sparse constraints.
- `sparse_problem`, `SparseProblem` — Record, constructor; view, domain, values, and
  entry facts.
- `view`, `domain`, `sparse_values`, `entry_fact` — Fields; sparse problem inputs.
- `sparse_system`, `sparse_static` — Definitions; sparse conditional system and dependencies.
- `sparse_sound` — Theorem; reachable blocks, taken edges, and defined values satisfy
  sparse facts.

### `ViewsRefine.v` — VIEW-4

- `refine_fact`, `refine_on_edge` — Definitions; refine a value fact by an edge's guards.
- `edge_feasible` — Definition; test whether edge guard refinements allow execution.
- `refine_fact_sound`, `refine_on_edge_sound` — Theorems; guard refinement retains concrete
  values.
- `edge_feasible_sound` — Theorem; a taken edge is feasible under sound facts.

### `ViewsDominated.v` — VIEW-5

- `strict_ssa_laws` — Record; redefinitions and operands obey SSA dominance restrictions.
- `redefine_in_stay`, `redefine_on_edge` — Fields; value changes occur at their defining blocks.
- `guard_home`, `op_args_dominate` — Fields; guard and operand definitions dominate their uses.
- `dom_context`, `DomContext` — Record, constructor; prepared graph and dominance indexes.
- `dc_graph`, `dc_encoding`, `dc_prepared`, `dc_tree`, `dc_index` — Fields; dominance
  context parts.
- `make_dom_context`, `dominating_edges_in` — Definitions; prepare dominance and list
  dominating edges.
- `refined_fact` — Definition; refine a value fact using the edges dominating a block.
- `dominated_guard_holds` — Theorem; guards and operand equations hold at dominated
  reachable uses.
- `dominating_edges_in_sound` — Theorem; each indexed edge semantically dominates the
  queried block.
- `refined_fact_sound` — Theorem; dominated-edge refinement retains the reachable concrete
  value.

### `ViewsEffects.v` — VIEW-6

- `effects`, `Effects` — Record, constructor; conservative instruction effect flags.
- `reads`, `writes`, `may_trap`, `may_diverge`, `may_stop` — Fields; memory and control effects.
- `allocates`, `frees`, `calls`, `observes` — Fields; allocation, frame, and event effects.
- `effects_view`, `EffectsView` — Record, constructor; instruction, heap, heap agreement,
  and depth.
- `instr_at`, `heap`, `heap_agree`, `depth` — Fields; retrieve the effects view components.
- `diverges_within`, `within_step` — CoInductive, constructor; divergence above a frame depth.
- `effects_laws` — Record; effects flags soundly describe reachable steps and endings.
- `silent`, `trap_covered`, `stop_covered` — Fields; observation, trap, and stop coverage.
- `heap_frame`, `reads_frame`, `trap_frame`, `stop_frame` — Fields; heap independence
  and framing.
- `frame_frame`, `call_returns` — Fields; frame depth and nondiverging call properties.
- `silent_exec_in` — Theorem; a run through non-observing instructions emits no event.

### `ViewsCalls.v` — VIEW-6

- `calls_view`, `CallsView` — Record, constructor; functions, call sites, and active frames.
- `functions`, `roots`, `sites_of`, `caller_of`, `here`, `frames` — Fields; call-view
  components.
- `active` — Definition; current and suspended active functions.
- `call_edge`, `CallEdge`, `edge_site`, `edge_callee` — Record, constructor, fields;
  call-graph edge.
- `call_graph` — Definition; graph of resolved call targets from function roots.
- `calls_view_laws` — Record; sites, roots, reachable frames, and call-step shape are sound.
- `sites_caller`, `initial_roots`, `frames_listed`, `step_shape` — Fields; call-view
  obligations.
- `call_graph_wf` — Theorem; a valid calls view and resolver produce a well-formed call graph.
- `active_reachable_in_call_graph` — Theorem; active functions are reachable in the call graph.

### `ViewsSummary.v` — VIEW-6

- `summary_spec`, `SummarySpec` — Record, constructor; summary lattice and local and call
  transfers.
- `slat`, `local`, `via_call` — Fields; summary lattice, local fact, and callee transfer.
- `step_cover`, `StepCover`, `step_covers` — Record, constructor, field; summary covers a step.
- `summary_constraint`, `SLocal`, `SCall` — Inductive, constructors; local and call constraints.
- `summary_constraint_encoding` — Definition; encode a function or call-site/callee constraint.
- `summary_system`, `summary_static` — Definitions; summary constraints and static dependencies.
- `summary_laws` — Record; summary coverage is monotone and covers local and callee steps.
- `covers_monotone`, `local_covers`, `call_covers` — Fields; summary coverage obligations.
- `summary_sound` — Theorem; every active function's post-solution covers the current step.

### `ViewsMemory.v` — VIEW-7

- `mem_op`, `MemLoad`, `MemStore`, `MemCopy`, `MemFill`, `MemAlloc`, `MemFree` — Inductive,
  constructors; memory operations and their operands.
- `mem_view`, `MemView` — Record, constructor; memory instruction and pointer interpretation.
- `mem_instr`, `loc_of`, `loc_site`, `loc_offset` — Fields; access operation and pointer
  location.
- `mem_view_laws`, `site_stable` — Record, field; allocation sites persist across steps.
- `pointer_domain`, `PointerDomain` — Record, constructor; abstract pointers and reachable
  ranges.
- `ptr_lat`, `ptr_conc`, `ptr_reach` — Fields; pointer lattice, concretisation, and start
  offsets.
- `access_footprint` — Definition; byte ranges touched by an offset and width from abstract
  starts.
- `pointer_domain_laws`, `ptr_reach_sound` — Record, field; pointer ranges cover concrete
  starts.
- `loc_site_preserved` — Theorem; allocation sites persist along runs.
- `access_footprint_sound` — Theorem; computed load or store footprints cover accessed bytes.

## Bits

### `BitsWord.v` — BIT-1

- `width` — Definition; Positive word width.
- `modulus` — Definition; Power-of-two modulus for a width.
- `wrap` — Definition; Reduce an integer modulo the word modulus.
- `is_word` — Definition; Recognise integers in the word range.
- `word` — Definition; Width and integer pair.
- `half` — Definition; Half of the width modulus.
- `msb` — Definition; Most significant wrapped bit.
- `signed` — Definition; Signed two’s-complement view.
- `wrap_is_word` — Theorem; States `is_word w (wrap w z)`.
- `wrap_id` — Theorem; States `is_word w z -> wrap w z = z`.
- `wrap_wrap` — Theorem; States `wrap w (wrap w z) = wrap w z`.
- `wrap_add` — Theorem; States `wrap w (x + y) = wrap w (wrap w x + wrap w y)`.
- `wrap_mul` — Theorem; States `wrap w (x * y) = wrap w (wrap w x * wrap w y)`.
- `wrap_narrow` — Theorem; States `(w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z`.

### `BitsFun.v` — BIT-1

- `wnot` — Definition; Bitwise complement.
- `wneg` — Definition; Modular negation.
- `wadd` — Definition; Modular addition.
- `wsub` — Definition; Modular subtraction.
- `wmul` — Definition; Modular multiplication.
- `wand` — Definition; Bitwise conjunction.
- `wor` — Definition; Bitwise disjunction.
- `wxor` — Definition; Bitwise exclusive-or.
- `wudiv` — Definition; Total unsigned division.
- `wurem` — Definition; Total unsigned remainder.
- `wsdiv` — Definition; Total signed division.
- `wsrem` — Definition; Total signed remainder.
- `wsmod` — Definition; Total signed modulus.
- `wshl` — Definition; Logical left shift.
- `wlshr` — Definition; Logical right shift.
- `washr` — Definition; Arithmetic right shift.
- `wrotl` — Definition; Left rotation.
- `wrotr` — Definition; Right rotation.
- `wclz` — Definition; Leading zero count.
- `wctz` — Definition; Trailing zero count.
- `wpopcnt` — Definition; Population count.
- `wult` — Definition; Unsigned less-than.
- `wule` — Definition; Unsigned less-than-or-equal.
- `wslt` — Definition; Signed less-than.
- `wsle` — Definition; Signed less-than-or-equal.

### `BitsOp.v` — BIT-1

- `op` — Inductive; Bit-vector operator syntax.
- `arity` — Definition; Number of operator operands.
- `result_width` — Definition; Check operand widths and return result width.
- `eval_op` — Definition; Evaluate a bit-vector operator.
- `word_fun1` — Definition; Select the unary same-width word function.
- `word_fun2` — Definition; Select the binary same-width word function.
- `word_cmp` — Definition; Select the word comparison function.
- `op_encoding` — Definition; Injective encoding of operators.
- `commutative` — Definition; Recognise commutative operators.
- `eval_op_total` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_width` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_arity` — Theorem; States `eval_op o xs = Some r -> List.length xs = arity o`.
- `eval_op_is_word` — Theorem; States `eval_op o xs = Some r -> is_word (fst r) (snd r)`.
- `eval_op_normalised` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_fun1` — Theorem; The operator rules agree with the word functions.
- `eval_op_fun2` — Theorem; The operator rules agree with the word functions.
- `eval_op_cmp` — Theorem; The operator rules agree with the word functions.
- `eval_op_ite` — Theorem; The operator rules agree with the word functions.
- `commutative_sound` — Theorem; Commutative operators give the same result in either order.
- `bvnot` — Constructor; Bitwise complement operator.
- `bvneg` — Constructor; Modular negation operator.
- `bvclz` — Constructor; Count leading zero bits.
- `bvctz` — Constructor; Count trailing zero bits.
- `bvpopcnt` — Constructor; Count set bits.
- `bvadd` — Constructor; Modular addition operator.
- `bvsub` — Constructor; Modular subtraction operator.
- `bvmul` — Constructor; Modular multiplication operator.
- `bvudiv` — Constructor; Total unsigned division operator.
- `bvurem` — Constructor; Total unsigned remainder operator.
- `bvsdiv` — Constructor; Total signed division operator.
- `bvsrem` — Constructor; Total signed remainder operator.
- `bvsmod` — Constructor; Total signed modulus operator.
- `bvand` — Constructor; Bitwise conjunction operator.
- `bvor` — Constructor; Bitwise disjunction operator.
- `bvxor` — Constructor; Bitwise exclusive-or operator.
- `bvshl` — Constructor; Logical left shift operator.
- `bvlshr` — Constructor; Logical right shift operator.
- `bvashr` — Constructor; Arithmetic right shift operator.
- `bvrotl` — Constructor; Left rotation operator.
- `bvrotr` — Constructor; Right rotation operator.
- `bveq` — Constructor; Equality comparison operator.
- `bvne` — Constructor; Inequality comparison operator.
- `bvult` — Constructor; Unsigned less-than operator.
- `bvule` — Constructor; Unsigned less-than-or-equal operator.
- `bvslt` — Constructor; Signed less-than operator.
- `bvsle` — Constructor; Signed less-than-or-equal operator.
- `bvite` — Constructor; Conditional selection operator.
- `bvzext` — Constructor; Zero-extension operator.
- `bvsext` — Constructor; Sign-extension operator.
- `bvtrunc` — Constructor; Truncate to a target width.
- `bvextract` — Constructor; Extract a contiguous range of bits.
- `bvconcat` — Constructor; Concatenate high and low operands.

### `BitsExpr.v` — BIT-1

- `Bits.expr` — Inductive; Bit-vector expression syntax.
- `Bits.eval_args` — Definition; Evaluate an expression list.
- `Bits.eval` — Definition; Evaluate an expression.
- `Bits.env_of` — Definition; Build an environment from words.
- `Bits.vars` — Definition; Build a list of variables.
- `eval_var` — Theorem; The evaluator, by cases on the expression.
- `eval_const` — Theorem; States `eval env (Const w z) = Some (w, wrap w z)`.
- `eval_app` — Theorem; The evaluator, by cases on the expression.
- `eval_args_nil` — Theorem; States `eval_args env nil = Some nil`.
- `eval_args_cons` — Theorem; The evaluator, by cases on the expression.
- `eval_is_word` — Theorem; States `eval env e = Some r -> is_word (fst r) (snd r)`.
- `Bits.Var` — Constructor; Read a variable by index.
- `Bits.Const` — Constructor; Literal word with a width and integer value.
- `Bits.App` — Constructor; Apply an operator to argument expressions.

### `BitsBridge.v` — BIT-1

- `bridge_op` — Definition; Relate client operator results to word operators.
- `bridge_expr` — Definition; Relate client operator results to word expressions.
- `bridge_op_expr` — Theorem;
  An operator-level bridge is an expression-level bridge through the variables 0, 1, ...

### `BitsTestbit.v` — BIT-1

- `testbit_wrap` — Theorem; The bits of a wrapped value, and equality of words by bits.
- `word_ext` — Theorem; The bits of a wrapped value, and equality of words by bits.
- `testbit_wand` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wor` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wxor` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wnot` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wshl` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `testbit_wlshr` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `testbit_washr` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `wshl_big` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `washr_big` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `wand_comm` — Theorem; States `wand w x y = wand w y x`.
- `wand_assoc` — Theorem; States `wand w x (wand w y z) = wand w (wand w x y) z`.
- `wor_comm` — Theorem; States `wor w x y = wor w y x`.
- `wor_assoc` — Theorem; States `wor w x (wor w y z) = wor w (wor w x y) z`.
- `wxor_comm` — Theorem; States `wxor w x y = wxor w y x`.
- `wxor_assoc` — Theorem; States `wxor w x (wxor w y z) = wxor w (wxor w x y) z`.
- `wxor_self` — Theorem; States `wxor w x x = 0`.
- `wand_idem` — Theorem; States `is_word w x -> wand w x x = x`.
- `wnot_involutive` — Theorem; States `is_word w x -> wnot w (wnot w x) = x`.
- `wnot_wand` — Theorem; States `wnot w (wand w x y) = wor w (wnot w x) (wnot w y)`.
- `wnot_wor` — Theorem; States `wnot w (wor w x y) = wand w (wnot w x) (wnot w y)`.
- `wand_wnot` — Theorem; States `wand w x (wnot w x) = 0`.
- `wadd_comm` — Theorem; States `wadd w x y = wadd w y x`.
- `wadd_assoc` — Theorem; States `wadd w x (wadd w y z) = wadd w (wadd w x y) z`.
- `wadd_0_r` — Theorem; States `is_word w x -> wadd w x 0 = x`.
- `wneg_wnot` — Theorem; States `wneg w x = wadd w (wnot w x) 1`.
- `wadd_wneg` — Theorem; States `wadd w x (wneg w x) = 0`.
- `wsub_wneg` — Theorem; States `wsub w x y = wadd w x (wneg w y)`.
- `wmul_comm` — Theorem; States `wmul w x y = wmul w y x`.
- `wmul_assoc` — Theorem; States `wmul w x (wmul w y z) = wmul w (wmul w x y) z`.
- `wmul_1_r` — Theorem; States `is_word w x -> wmul w x 1 = x`.
- `wmul_wadd_distr` — Theorem; Modular arithmetic identities.
- `wshl_0` — Theorem; States `is_word w x -> wshl w x 0 = x`.

### `BitsSigned.v` — BIT-2

- `signed_range` — Theorem; States `- half w <= signed w x < half w`.
- `signed_id` — Theorem; States `- half w <= z < half w -> signed w z = z`.
- `wrap_signed` — Theorem; States `wrap w (signed w x) = wrap w x`.
- `signed_wrap` — Theorem; States `signed w (wrap w x) = signed w x`.
- `signed_inj` — Theorem; States `signed w x = signed w y -> wrap w x = wrap w y`.
- `signed_neg_iff_msb` — Theorem; States `signed w x < 0 <-> msb w x = true`.
- `wadd_signed` — Theorem; States `wadd w x y = wrap w (signed w x + signed w y)`.
- `wsub_signed` — Theorem; States `wsub w x y = wrap w (signed w x - signed w y)`.
- `wslt_bias` — Theorem; Addition and comparison through the signed view.
- `wslt_wult` — Theorem; States `msb w x = msb w y -> wslt w x y = wult w x y`.
- `wsdiv_signed` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsrem_signed` — Theorem; States `wsrem w x y = wrap w (Z.rem (signed w x) (signed w y))`.
- `wsmod_signed` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsdiv_zero` — Theorem; States `wsdiv w x 0 = if msb w x then 1 else modulus w - 1`.
- `wsdiv_wsrem_euclid` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsmod_sign` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.

### `BitsArith.v` — BIT-2

- `wudiv_zero` — Theorem; States `wudiv w x 0 = modulus w - 1`.
- `wurem_zero` — Theorem; States `wurem w x 0 = wrap w x`.
- `wudiv_spec` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wurem_spec` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wurem_lt` — Theorem; States `is_word w x -> is_word w y -> y <> 0 -> wurem w x y < y`.
- `wudiv_wurem_euclid` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wmul_signed` — Theorem; States `wmul w x y = wrap w (signed w x * signed w y)`.
- `wmul_wshl` — Theorem; Multiplication and powers of two.
- `wudiv_wlshr` — Theorem; Multiplication and powers of two.
- `wurem_mask` — Theorem; Multiplication and powers of two.
- `testbit_wrotl` — Theorem; Rotations move bits cyclically, by the amount modulo the width.
- `wrotl_mod` — Theorem; States `wrotl w x y = wrotl w x (wrap w y mod Zpos w)`.
- `wrotr_wrotl` — Theorem; States `wrotr w (wrotl w x y) y = wrap w x`.
- `wclz_zero` — Theorem; States `wclz w 0 = Zpos w`.
- `wctz_zero` — Theorem; States `wctz w 0 = Zpos w`.
- `wclz_spec` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.
- `wclz_range` — Theorem; States `0 <= wclz w x <= Zpos w`.
- `wctz_spec` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.
- `wpopcnt_range` — Theorem; States `0 <= wpopcnt w x <= Zpos w`.
- `wpopcnt_wnot` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.

### `BitsExtend.v` — BIT-2

- `zext_value` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `sext_value` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `sext_signed` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `trunc_zext` — Theorem; Truncation undoes extension and commutes with addition.
- `trunc_sext` — Theorem; Truncation undoes extension and commutes with addition.
- `trunc_wadd` — Theorem; Truncation undoes extension and commutes with addition.
- `extract_concat_hi` — Theorem;
  Concatenation puts the first operand high; extract and truncation recover the parts.
- `trunc_concat_lo` — Theorem;
  Concatenation puts the first operand high; extract and truncation recover the parts.

## Domains

### `DomainsNumeric.v` — DOM-1a

- `numeric_domain` — Record; Lattice and sound abstract word operations.
- `numeric_laws` — Record; Lattice, concretisation and numeric transfer laws.
- `abs_eval` — Definition; Evaluate an expression abstractly.
- `abs_assume` — Definition; Refine an environment from an expression result.
- `env_ok` — Definition; Require every environment word to be in range.
- `env_sound` — Definition; Relate abstract and concrete environments.
- `word_domain` — Record; Width-indexed payload lattice and operations.
- `payload_sound` — Definition; Relate a width-tagged payload to a concrete word.
- `word_laws` — Record; Soundness and refinement laws for payload operations.
- `tagged` — Inductive; Empty, width-tagged or unrestricted payload.
- `tagged_lattice` — Definition; Lattice for tagged.
- `tagged_val` — Definition; Build a tagged value, collapsing empty payloads.
- `tagged_domain` — Definition; Payload domain for tagged.
- `tagged_gamma` — Definition; Concretisation for tagged.
- `width_ok` — Definition; Limit a tagged value to a maximum width.
- `capped` — Definition; Tagged values bounded by a maximum width.
- `capped_lattice` — Definition; Lattice for capped.
- `capped_height` — Definition; Finite height for capped.
- `capped_wrank` — Definition; Widening rank for capped.
- `clamp` — Definition; Replace an out-of-cap tagged value by top.
- `capped_domain` — Definition; Payload domain for capped.
- `capped_gamma` — Definition; Concretisation for capped.
- `abs_eval_var` — Theorem; States `abs_eval D env (Var i) = env i`.
- `abs_eval_const` — Theorem; States `abs_eval D env (Const w z) = of_const D w z`.
- `abs_eval_app` — Theorem; The abstract evaluator follows the expression's structure.
- `abs_eval_sound` — Theorem;
  One generic soundness theorem: abstract evaluation over-approximates concrete evaluation.
- `abs_assume_sound` — Theorem;
  A guard keeps the environment sound, and refinement only goes down.
- `abs_assume_refines` — Theorem;
  A guard keeps the environment sound, and refinement only goes down.
- `tagged_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `capped_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `tagged_numeric_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `clamp_gamma` — Theorem;
  Clamping to the cap only widens, and the capped domain is a sound numeric domain.
- `capped_numeric_laws` — Theorem;
  Clamping to the cap only widens, and the capped domain is a sound numeric domain.
- `NumericDomain` — Constructor; Construct a numeric domain from its lattice and transfers.
- `WordDomain` — Constructor; Construct a width-indexed payload domain.
- `lat` — Field; Numeric lattice, constructors or transfers.
- `top_at` — Field; Numeric lattice, constructors or transfers.
- `of_const` — Field; Numeric lattice, constructors or transfers.
- `forward` — Field; Numeric lattice, constructors or transfers.
- `assume` — Field; Numeric lattice, constructors or transfers.
- `meet` — Field; Numeric lattice, constructors or transfers.
- `lat_laws` — Field; Numeric domain law.
- `gamma_laws` — Field; Numeric domain law.
- `bot_empty` — Field; Numeric domain law.
- `top_at_sound` — Field; Numeric domain law.
- `of_const_sound` — Field; Numeric domain law.
- `forward_sound` — Field; Numeric domain law.
- `assume_sound` — Field; Numeric domain law.
- `assume_length` — Field; Numeric domain law.
- `assume_refines` — Field; Numeric domain law.
- `meet_sound` — Field; Numeric domain law.
- `meet_lower_left` — Field; Numeric domain law.
- `plat` — Field; Width-indexed payload operation.
- `ptop` — Field; Width-indexed payload operation.
- `pconst` — Field; Width-indexed payload operation.
- `pforward` — Field; Width-indexed payload operation.
- `passume` — Field; Width-indexed payload operation.
- `pmeet` — Field; Width-indexed payload operation.
- `plat_laws` — Field; Payload domain law.
- `pgamma_monotone` — Field; Payload domain law.
- `pgamma_bot_empty` — Field; Payload domain law.
- `ptop_sound` — Field; Payload domain law.
- `pconst_sound` — Field; Payload domain law.
- `pforward_sound` — Field; Payload domain law.
- `passume_sound` — Field; Payload domain law.
- `passume_refines` — Field; Payload domain law.
- `pmeet_sound` — Field; Payload domain law.
- `pmeet_lower_left` — Field; Payload domain law.
- `TBot` — Constructor; Tagged empty value.
- `TVal` — Constructor; Payload tagged with its word width.
- `TAny` — Constructor; Unrestricted word value.

### `DomainsConst.v` — DOM-1a

- `const_domain` — Definition; Payload domain for const.
- `const_gamma` — Definition; Concretisation for const.
- `const_word_laws` — Theorem; States `word_laws const_domain const_gamma`.

### `DomainsInterval.v` — DOM-1b

- `bound` — Inductive; Infinite or finite interval endpoint.

- `interval` — Inductive; Empty interval or pair of bounds.
- `interval_lattice` — Definition; Lattice for interval.
- `interval_gamma` — Definition; Concretisation for interval.
- `interval_wrank` — Definition; Widening rank for interval.
- `interval_pgamma` — Definition; Payload meaning for interval.
- `interval_domain` — Definition; Payload domain for interval.
- `interval_laws` — Theorem; States `lattice_laws (interval_lattice thresholds)`.
- `interval_lub` — Theorem; States `lub_laws (interval_lattice thresholds)`.
- `interval_gamma_laws` — Theorem;
  Intervals: a lattice with least upper bounds, monotone meaning, sound transfers.
- `interval_gamma_bot_empty` — Theorem;
  Intervals: a lattice with least upper bounds, monotone meaning, sound transfers.
- `interval_word_laws` — Theorem; States `word_laws (interval_domain thresholds) interval_pgamma`.
- `NegInf` — Constructor; Negative infinity interval bound.
- `Fin` — Constructor; Finite integer interval bound.
- `PosInf` — Constructor; Positive infinity interval bound.
- `IBot` — Constructor; Empty integer interval.
- `Itv` — Constructor; Interval with lower and upper bounds.

### `DomainsSign.v` — DOM-1a

- `sign` — Record; Set of possible signed signs.

- `sign_lattice` — Definition; Lattice for sign.
- `sign_height` — Definition; Finite height for sign.
- `sign_gamma` — Definition; Concretisation for sign.
- `sign_domain` — Definition; Payload domain for sign.
- `sign_laws` — Theorem; States `lattice_laws sign_lattice`.
- `sign_lub` — Theorem; States `lub_laws sign_lattice`.
- `sign_word_laws` — Theorem; States `word_laws sign_domain sign_gamma`.
- `Sign` — Constructor; Sign record constructor.
- `neg` — Field; Sign membership flag.
- `zero` — Field; Sign membership flag.
- `pos` — Field; Sign membership flag.

### `DomainsKnownBits.v` — DOM-2

- `tnum` — Record; Known-zero and known-one bit masks.
- `tnum_lattice` — Definition; Lattice for tnum.
- `tnum_height` — Definition; Finite height for tnum.
- `tnum_gamma` — Definition; Concretisation for tnum.
- `known_bits_domain` — Definition; Payload domain for known bits.
- `tnum_laws` — Theorem; States `lattice_laws (tnum_lattice w)`.
- `tnum_lub` — Theorem; States `lub_laws (tnum_lattice w)`.
- `known_bits_word_laws` — Theorem; States `word_laws known_bits_domain tnum_gamma`.
- `Tnum` — Constructor; Known-bits record constructor.
- `zeros` — Field; Known zero or one bit mask.
- `ones` — Field; Known zero or one bit mask.

### `DomainsWrapped.v` — DOM-3

- `wrapped_laws` — Theorem; States `lattice_laws (wrapped_lattice w)`.

- `wrapped` — Inductive; Empty, full or circular word interval.
- `wrapped_size` — Definition; Count the words in a circular interval.
- `wrapped_lattice` — Definition; Lattice for wrapped.
- `wrapped_wrank` — Definition; Widening rank for wrapped.
- `wrapped_gamma` — Definition; Concretisation for wrapped.
- `wrapped_domain` — Definition; Payload domain for wrapped.
- `wrapped_join_minimal` — Theorem;
  Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
  arcs; there is no least upper bound in general, so there is no lub_laws theorem.
- `wrapped_gamma_laws` — Theorem;
  Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
  arcs; there is no least upper bound in general, so there is no lub_laws theorem.
- `wrapped_word_laws` — Theorem; States `word_laws wrapped_domain wrapped_gamma`.
- `WBot` — Constructor; Empty circular interval.
- `WFull` — Constructor; Full circular interval.
- `WItv` — Constructor; Circular interval with two endpoints.

### `DomainsCongruence.v` — DOM-4

- `cong_laws` — Theorem; States `lattice_laws (cong_lattice w)`.

- `cong` — Inductive; Empty or modular congruence value.
- `cong_norm` — Definition; Normalise a congruence to the word width.
- `cong_lattice` — Definition; Lattice for cong.
- `cong_height` — Definition; Finite height for cong.
- `cong_gamma` — Definition; Concretisation for cong.
- `cong_domain` — Definition; Payload domain for cong.
- `cong_lub` — Theorem; States `lub_laws (cong_lattice w)`.
- `cong_word_laws` — Theorem; States `word_laws cong_domain cong_gamma`.
- `CBot` — Constructor; Empty congruence.
- `Cong` — Constructor; Congruence with modulus and residue.

### `DomainsProduct.v` — DOM-4

- `product_word_domain` — Definition; Build a reduced product of payload domains.
- `product_pgamma` — Definition; Intersect the meanings of two payloads.
- `payload_concretisation` — Definition; Expose a payload meaning as a concretisation.
- `reduction_empty` — Definition; Require reduction to collapse empty components.
- `reduce_bits_wrapped` — Definition; Exchange known-bit and circular-interval information.
- `reduce_interval_cong` — Definition; Exchange interval and congruence information.
- `reduce_const_with` — Definition; Exchange constant information with a payload.
- `bits_wrapped_domain` — Definition; Reduced product of known bits and circular intervals.
- `interval_cong_domain` — Definition; Reduced product of intervals and congruences.
- `const_product_domain` — Definition; Reduced product of constants with a payload.
- `product_word_laws` — Theorem;
  A product of two sound payload domains with a sound, monotone, idempotent reduction is sound.
- `reduce_bits_wrapped_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `reduce_interval_cong_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `reduce_const_with_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `bits_wrapped_numeric_laws` — Theorem; The three named products are sound numeric domains.
- `interval_cong_numeric_laws` — Theorem; The three named products are sound numeric domains.

### `DomainsDemanded.v` — DOM-5

- `mask_lattice` — Definition; Lattice for mask.
- `mask_height` — Definition; Finite height for mask.
- `mask_agreement` — Definition; Word agreement on selected bits.
- `demand` — Definition; Compute operand masks from a demanded result mask.
- `agree_masks` — Definition; Relate operand lists under their demanded masks.
- `consts_hold` — Definition; Check known constants against operand words.
- `masks_leb` — Definition; Pointwise inclusion of width-indexed masks.
- `mask_laws` — Theorem; States `lattice_laws (mask_lattice w)`.
- `mask_lub` — Theorem; States `lub_laws (mask_lattice w)`.
- `mask_agreement_laws` — Theorem; States `agreement_laws (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_bot` — Theorem; States `agreement_bot (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_join` — Theorem;
  States `agreement_join_law (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_equivalence` — Theorem; States `agreement_equivalence (mask_agreement w)`.
- `demand_sound` — Theorem;
  Soundness: operands of equal widths that agree under the demanded masks, and whose known
  constants are right, give results that agree under the output mask.
- `demand_zero` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.
- `demand_length` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.
- `demand_monotone` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.

### `DomainsAddress.v` — DOM-6

- `address` — Record; Site, offset and size of an abstract access.
- `access` — Definition; Concrete object, byte offset and size.
- `bytes_of` — Definition; Membership of a byte in a concrete access.
- `address_gamma` — Definition; Concretisation for address.
- `covers` — Definition; Prove one abstract access covers another.
- `disjoint` — Definition; Prove two abstract accesses disjoint.
- `may_overlap` — Definition; Conservative overlap query for abstract accesses.
- `covers_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `disjoint_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `may_overlap_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `covers_exact` — Theorem;
  The predicates are not trivially false: an exact address covers itself, and objects at different
  known sites are disjoint.
- `disjoint_sites` — Theorem;
  The predicates are not trivially false: an exact address covers itself, and objects at different
  known sites are disjoint.
- `Address` — Constructor; Address record constructor.
- `site` — Field; Address site, offset or size.
- `offset` — Field; Address site, offset or size.
- `size` — Field; Address site, offset or size.

### `DomainsPointsTo.v` — DOM-6

- `points_to` — Definition; Possible sites and an unknown-object flag.
- `points_to_laws` — Theorem; States `lattice_laws points_to_lattice`.

- `points_to_lattice` — Definition; Lattice for points to.
- `points_to_gamma` — Definition; Concretisation for points to.
- `pts_of_site` — Definition; Singleton points-to fact.
- `pts_unknown` — Definition; Points-to fact for an unknown object.
- `pts_may_alias` — Definition; Conservative alias query on points-to facts.
- `pts_must_alias` — Definition; Prove two points-to facts have one common object.
- `points_to_lub` — Theorem; States `lub_laws points_to_lattice`.
- `points_to_gamma_laws` — Theorem;
  States `concretisation_laws points_to_lattice points_to_gamma`.
- `pts_may_alias_sound` — Theorem;
  Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries.
- `pts_must_alias_sound` — Theorem;
  Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries.
- `pts_of_site_gamma` — Theorem; States `gamma points_to_gamma (pts_of_site s) p <-> p = s`.

### `DomainsByteRange.v` — DOM-6

- `range` — Definition; Half-open integer byte range.

- `ranges_wf` — Definition; Sorted, nonempty and nonadjacent range invariant.
- `byte_ranges` — Definition; Canonical list of byte ranges.
- `ranges_empty` — Definition; Empty canonical range set.
- `ranges_mem` — Definition; Test byte membership in a range set.
- `ranges_add` — Definition; Add a byte range to a range set.
- `ranges_remove` — Definition; Remove a byte range from a range set.
- `ranges_union` — Definition; Union two range sets.
- `ranges_inter` — Definition; Intersect two range sets.
- `ranges_diff` — Definition; Subtract one range set from another.
- `ranges_covers` — Definition; Test whether a range set covers a range.
- `ranges_intersects` — Definition; Test whether a range set intersects a range.
- `ranges_lattice` — Definition; Lattice for ranges.
- `ranges_gamma` — Definition; Concretisation for ranges.
- `ranges_mem_empty` — Theorem; States `ranges_mem ranges_empty b = false`.
- `ranges_mem_add` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_remove` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_union` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_inter` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_diff` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_ext` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_covers_spec` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_intersects_spec` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_laws` — Theorem; States `lattice_laws ranges_lattice`.
- `ranges_lub` — Theorem; States `lub_laws ranges_lattice`.
- `ranges_gamma_laws` — Theorem; States `concretisation_laws ranges_lattice ranges_gamma`.

### `DomainsFootprint.v` — DOM-6

- `footprint` — Record; Site and half-open byte bounds.

- `covered` — Definition; Bytewise coverage of an access by footprints.
- `written` — Definition; Byte membership in a footprint list.
- `footprint_encoding` — Definition; Injectively encode a site and its byte bounds.
- `footprints_canonical` — Definition; Require sorted, nonempty and nonadjacent footprints.
- `site_ranges` — Definition; Extract one site's byte ranges.
- `footprints_normalise` — Definition; Canonicalise a footprint list.
- `footprints_inter` — Definition; Intersect footprint lists by site and byte.
- `footprints_diff` — Definition; Subtract footprint bytes by site.
- `canonical_footprints` — Definition; Footprint lists paired with their canonicality proof.
- `range_must` — Definition; Unreachable or canonical must-written footprints.
- `range_reached` — Definition; Normalise footprints into a reached must fact.
- `range_written` — Definition; Byte membership in a must fact.
- `range_must_lattice` — Definition; Lattice for range must.
- `range_must_top` — Definition; Must fact with no known written bytes.
- `range_add` — Definition; Add written bytes to a must fact.
- `range_remove` — Definition; Forget overwritten bytes from a must fact.
- `range_covers` — Definition; Bytewise must coverage of an access.
- `range_must_gamma` — Definition; Concretisation for range must.
- `footprints_normalise_canonical` — Theorem;
  States `footprints_canonical ET (footprints_normalise ET F)`.
- `footprints_normalise_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_inter_canonical` — Theorem;
  States `footprints_canonical ET (footprints_inter ET F G)`.
- `footprints_inter_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_diff_canonical` — Theorem;
  States `footprints_canonical ET (footprints_diff ET F G)`.
- `footprints_diff_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_ext` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_canonical_ranges` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `covered_written` — Theorem;
  covered is exactly bytewise coverage, including empty accesses and noncanonical lists.
- `covered_bytewise` — Theorem;
  covered is exactly bytewise coverage, including empty accesses and noncanonical lists.
- `range_must_laws` — Theorem; States `lattice_laws (range_must_lattice ET)`.
- `range_must_lub` — Theorem; States `lub_laws (range_must_lattice ET)`.
- `range_must_leb_spec` — Theorem;
  The must lattice of ranges: a lattice with least upper bounds, ordered by bytes.
- `range_reached_written` — Theorem;
  The must lattice of ranges: a lattice with least upper bounds, ordered by bytes.
- `range_must_gamma_laws` — Theorem;
  Meaning: Unreached has no concrete states; Reached F means every footprint byte is written.
- `range_must_gamma_bot_empty` — Theorem;
  States `bottom_empty (range_must_lattice ET) range_must_gamma`.
- `range_must_gamma_top_full` — Theorem; States `top_full (range_must_top ET) range_must_gamma`.
- `range_covers_sound` — Theorem;
  Meaning: Unreached has no concrete states; Reached F means every footprint byte is written.
- `range_covers_iff_written` — Theorem;
  range_covers is exactly bytewise coverage, including an access of zero bytes.
- `range_covers_add` — Theorem;
  Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
  overlapped bytes away and keeps the others.
- `range_covers_remove` — Theorem;
  Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
  overlapped bytes away and keeps the others.
- `range_add_gamma` — Theorem;
  The operations are sound for the meaning: added bytes that are written stay written, and bytes
  outside fs keep their status when fs may have been overwritten.
- `range_remove_gamma` — Theorem;
  The operations are sound for the meaning: added bytes that are written stay written, and bytes
  outside fs keep their status when fs may have been overwritten.
- `footprint_encoding_spec` — Theorem;
  footprint_encoding is the encoding of the triple of site code and bounds, by construction.
- `Footprint` — Constructor; Footprint record constructor.
- `fp_site` — Field; Footprint site or byte bound.
- `fp_lo` — Field; Footprint site or byte bound.
- `fp_hi` — Field; Footprint site or byte bound.

### `DomainsEquality.v` — DOM-7

- `partition` — Definition; Unreachable or a well-formed equality partition.
- `partition_equiv` — Definition; Equality relation represented by a partition.
- `partition_lattice` — Definition; Lattice for partition.
- `partition_top` — Definition; Partition that knows no nontrivial equalities.
- `partition_union` — Definition; Add an equality to a partition.
- `partition_forget` — Definition; Forget all nontrivial equalities of a key.
- `key_update` — Definition; Update a keyed valuation at one key.
- `partition_test` — Definition; Test equality and return the compressed partition.
- `partition_gamma` — Definition; Concretisation for partition.
- `partition_laws` — Theorem; States `lattice_laws (partition_lattice E)`.
- `partition_lub` — Theorem; States `lub_laws (partition_lattice E)`.
- `partition_join_spec` — Theorem;
  Partitions form a lattice with least upper bounds; the join is the intersection of equivalences.
- `partition_union_spec` — Theorem; Adding an equality merges exactly the two classes.
- `partition_forget_unreached` — Theorem; States `partition_forget E x Unreached = Unreached`.
- `partition_forget_spec` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_forget_leb` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_forget_gamma` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_test_correct` — Theorem;
  The test agrees with the relation and returns an equivalent partition.
- `partition_gamma_laws` — Theorem;
  Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything.
- `partition_gamma_bot_empty` — Theorem;
  Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything.
- `partition_top_full` — Theorem; States `top_full (partition_top E) (@partition_gamma K V E)`.

### `DomainsSymbolic.v` — DOM-7

- `sym_key` — Definition; List of positive codes for a symbolic expression.

- `expr_key` — Definition; Encode an operator and its operand numbers.
- `numbering` — Record; Intern table and next available number.
- `numbering_empty` — Definition; Empty intern table with initial number.
- `intern` — Definition; Find or allocate a number for a symbolic key.
- `numbering_wf` — Definition; Bound and uniquely identify numbers in the table.
- `numbering_wf_empty` — Theorem; States `numbering_wf numbering_empty`.
- `numbering_wf_intern` — Theorem; States `numbering_wf n -> numbering_wf (snd (intern k n))`.
- `intern_get` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_found` — Theorem; States `Table.get k (ids n) = Some i -> intern k n = (i, n)`.
- `intern_fresh` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_stable` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_injective` — Theorem;
  Numbers identify keys: two keys that get one number from a threaded numbering are equal.
- `expr_key_commutative` — Theorem;
  Keys respect commutativity, and equal keys denote equal values under any valuation.
- `expr_key_eval` — Theorem;
  Keys respect commutativity, and equal keys denote equal values under any valuation.
- `Numbering` — Constructor; Numbering record constructor.
- `ids` — Field; Interned IDs or next ID.
- `next` — Field; Interned IDs or next ID.

## Analyses

### `AnalysesLiveness.v` — ANA-1

- `fmem` — Definition; Tests membership in a finite set.
- `mentions` — Definition; Tests whether an encoded key occurs in a list.
- `var_view` — Record; Describes graph edges, variable uses and definitions.
- `VarView` — Constructor; Constructs the var view record.
- `gview` — Field; Graph view used by the variable analysis.
- `uses` — Field; Variables read by an edge.
- `defs` — Field; Variables written by an edge.
- `exit_uses` — Field; Variables observable at an exit.
- `vget` — Field; Reads a variable from a state.
- `var_view_laws` — Record; Relates variable uses and definitions to steps and exits.
- `view_laws` — Field; The underlying graph view satisfies its laws.
- `no_stays` — Field; The view has no point-preserving steps.
- `defs_frame` — Field; A step leaves variables outside its definitions unchanged.
- `uses_determine` — Field; Agreement on uses determines the edge step.
- `exits_determine` — Field; Agreement on exit uses determines the ending.
- `var_universe` — Definition; Finite universe of variables mentioned by the view.
- `live_set` — Definition; Finite live-variable fact.
- `live_lattice` — Definition; Lattice of finite live-variable facts.
- `live_agreement` — Definition; Agreement of states on all live variables.
- `liveness_transfer` — Definition; Adds edge uses and removes edge definitions.
- `liveness_system` — Definition; Backward constraints for liveness.
- `liveness_static` — Definition; Declared liveness dependencies.
- `solve_liveness` — Definition; Solves the liveness constraints.
- `reach_universe` — Definition; Finite universe of variable and defining-edge pairs.
- `reach_set` — Definition; Finite reaching-definition fact.
- `reach_lattice` — Definition; Lattice of reaching definitions.
- `reaching_transfer` — Definition; Kills old definitions and generates edge definitions.
- `reaching_system` — Definition; Forward constraints for reaching definitions.
- `zero_lattice` — Definition; Must lattice of variables zero since entry.
- `zero_since_entry_system` — Definition; Forward constraints for zero-since-entry facts.
- `copy_view` — Record; Describes variable copies along graph edges.
- `CopyView` — Constructor; Constructs the copy view record.
- `cvars` — Field; Variable view underlying the copy view.
- `copies` — Field; Copies performed by an edge.
- `equality_transfer` — Definition; Forgets written variables and joins copied variables.
- `equality_system` — Definition; Forward constraints for must equality.
- `live_agreement_laws` — Theorem; Live-variable agreement satisfies the agreement laws.
- `var_universe_covers` — Theorem; The variable universe covers view uses and definitions.
- `liveness_sound` — Theorem; Agreement on live variables preserves behaviour.
- `reaching_sound` — Theorem; The fact contains each last writer along a run prefix.
- `zero_since_entry_sound` — Theorem; Every variable in the fact still holds its entry zero.
- `equality_sound` — Theorem; Variables in the same partition class have equal values.

### `AnalysesAvailable.v` — ANA-1

- `genkill_view` — Record; Describes expressions generated and killed by each edge.
- `GenKillView` — Constructor; Constructs the gen kill view record.
- `gkview` — Field; Graph view underlying gen/kill information.
- `gen` — Field; Expressions generated by an edge.
- `kill` — Field; Expressions invalidated by an edge.
- `uval` — Field; Value of an expression in a state.
- `genkill_laws` — Record; Relates generated and killed expressions to execution.
- `gk_view` — Field; The underlying graph view satisfies its laws.
- `gk_no_stays` — Field; The graph view has no point-preserving steps.
- `gen_value` — Field; Generated expressions have their computed value.
- `kill_frame` — Field; Expressions outside the kill set retain their value.
- `final_exit` — Field; Final states occur at graph exits.
- `expr_universe` — Definition; Finite universe of expressions in the view.
- `avail_set` — Definition; Finite must-fact of expressions.
- `avail_lattice` — Definition; Reverse-inclusion lattice of expression facts.
- `avail_transfer` — Definition; Applies expression kills and generations to a fact.
- `available_system` — Definition; Forward constraints for available expressions.
- `busy_system` — Definition; Backward constraints for very busy expressions.
- `lcm_result` — Record; Insertion and deletion choices for lazy code motion.
- `LcmResult` — Constructor; Constructs the lcm result record.
- `insert` — Field; Expressions inserted on an edge.
- `delete` — Field; Expressions deleted at a node.
- `lcm_check` — Definition; Checks proposed code-motion insertions and deletions.
- `available_sound` — Theorem; An available expression has a current previously computed value.
- `busy_sound` — Theorem; A very busy expression is evaluated before invalidation.
- `lcm_insert_safe` — Theorem; An accepted insertion is anticipated.
- `lcm_delete_current` — Theorem; An accepted deletion has a current available value.

### `AnalysesStructured.v` — ANA-2

- `skel_vars` — Record; Variable uses and definitions of skeleton actions.
- `SkelVars` — Constructor; Constructs the skel vars record.
- `atom_uses` — Field; Variables read by a skeleton atom.
- `atom_defs` — Field; Variables written by a skeleton atom.
- `atom_trap_uses` — Field; Variables needed to determine an atom's trapping behaviour.
- `guard_uses` — Field; Variables read by a skeleton guard.
- `skel_vars_laws` — Record; Relates skeleton variable effects to client execution.
- `atom_frame` — Field; An atom changes only its declared definitions.
- `atom_agrees` — Field; Equal atom inputs yield matching steps.
- `guard_agrees` — Field; Equal guard inputs yield the same guard result.
- `trap_agrees` — Field; Equal trap inputs yield the same trap outcome.
- `jump_keeps` — Field; A jump preserves the relevant variable values.
- `act_vars` — Definition; Variables used or defined by a skeleton action.
- `skel_exit_uses` — Definition; Variables observable at a skeleton exit.
- `skel_universe` — Definition; Finite universe of variables in a skeleton.
- `skel_set` — Definition; Finite set of skeleton variables.
- `skel_lattice` — Definition; Lattice of skeleton variable sets.
- `skel_actb` — Definition; Backward transfer for a skeleton action.
- `structured_liveness_system` — Definition; Skeleton constraints for structured liveness.
- `certificate` — Definition; Facts stored at skeleton loop heads.
- `certificate_check` — Definition; Recomputes non-head facts and validates loop-head facts.
- `certificate_of` — Definition; Restricts a solution to its loop-head facts.
- `replay_live` — Definition; Replays live facts through an observer.
- `structured_liveness_sound` — Theorem; Structured live agreement preserves behaviour.
- `certificate_sound` — Theorem; An accepted loop certificate expands to a post-solution.
- `certificate_complete` — Theorem; A post-solution yields an accepted loop certificate.
- `replay_live_iff` — Theorem; Replay covers the expanded live facts.

### `AnalysesCensus.v` — ANA-2

- `region_table` — Definition; Computes a summary at every skeleton position.
- `region_table_agrees` — Theorem; Each table entry agrees with the recursive region summary.

### `AnalysesValues.v` — ANA-3

- `op_bridge` — Record; Maps client operators and values to bit-vector expressions and words.
- `OpBridge` — Constructor; Constructs the op bridge record.
- `op_expr` — Field; Bit-vector expression for a client operator.
- `to_word` — Field; Maps a client value to a width and bit-vector word.
- `op_bridge_laws` — Record; The client operator bridge agrees with word evaluation and truth.
- `bridge_word` — Field; Mapped values satisfy the word-range condition.
- `bridge_eq` — Field; A defined client result matches the bit-vector evaluation.
- `bridge_truth` — Field; The client truth predicate agrees with the bit-vector result.
- `sparse_of_numeric` — Definition; Adapts a numeric domain to the sparse analysis interface.
- `numeric_problem` — Definition; Builds a sparse value problem from a numeric domain and bridge.
- `solve_values` — Definition; Solves a sparse value problem.
- `sparse_of_numeric_laws` — Theorem; The numeric adapter satisfies the sparse-domain laws.
- `numeric_value_sound` — Theorem; Reachable values belong to their computed numeric facts.

### `AnalysesPaths.v` — ANA-3

- `path_domain` — Definition; Bounded disjunction domain for path facts.
- `guard_chain` — Definition; Dominating guarded edges relevant to a use.
- `path_domain_laws` — Theorem; The bounded path domain satisfies the sparse-domain laws.
- `guard_chain_holds` — Theorem; Each dominating guard in the chain holds at the use.

### `AnalysesDemand.v` — ANA-4

- `demand_domain` — Record; Lattice and agreement for backward value demands.
- `DemandDomain` — Constructor; Constructs the demand domain record.
- `dlat` — Field; Lattice of demand facts.
- `dagree` — Field; Agreement relation associated with a demand.
- `demand_view` — Record; Uses, definitions and backward demand transfer for graph edges.
- `DemandView` — Constructor; Constructs the demand view record.
- `dgraph` — Field; Graph view underlying the demand analysis.
- `ddefs` — Field; Variables defined by each edge.
- `dnec` — Field; Demands required by an edge's observable effects.
- `dback` — Field; Backward operand demands for a demanded definition.
- `dexit` — Field; Demands observable at an exit.
- `dlookup` — Field; Reads the value of a variable from a state.
- `dvars` — Field; Finite variable universe of demand facts.
- `demand_lattice` — Definition; Pointwise lattice of per-variable demands.
- `dget` — Definition; Reads a variable demand with a bottom default.
- `demand_agreement` — Definition; State agreement induced by per-variable demands.
- `demand_transfer` — Definition; Propagates output demands backward across an edge.
- `exit_map` — Definition; Builds the map of demands observable at an exit.
- `demand_system` — Definition; Backward constraints for demanded values.
- `demand_vars_ok` — Definition; All demands refer to the declared finite variable universe.
- `demand_laws` — Record; Relates backward demand propagation to steps and endings.
- `d_view` — Field; The demand graph view satisfies its laws.
- `d_no_stays` — Field; The demand graph has no point-preserving steps.
- `d_frame` — Field; An edge leaves variables outside its definitions unchanged.
- `d_agreement` — Field; The demand relation satisfies agreement laws.
- `d_bot_agrees` — Field; Bottom demand relates any two values.
- `d_back_bot` — Field; Bottom output demand propagates no operand demands.
- `d_vars` — Field; Demanded variables lie in the finite universe.
- `d_step` — Field; Demand agreement is preserved across matching steps.
- `d_exits` — Field; Demand agreement preserves observable endings.
- `trap_policy` — Inductive; Choices for preserving or dropping unread traps.
- `KeepTraps` — Constructor; Preserves trap behaviour during dead-code erasure.
- `DropUnreadTraps` — Constructor; Allows unread traps under the refinement conclusion.
- `effectful` — Definition; Tests whether an instruction must be retained under the trap policy.
- `demand_closed` — Definition; A demand closed under the backward transfer and exit seeds.
- `closed_system` — Definition; Single-unknown constraint system for demand closure.
- `bool_demand` — Definition; Boolean demand domain for neededness.
- `needed_values` — Definition; Least closed Boolean demand for the view.
- `dead_value` — Definition; Tests whether a value is absent from the needed demand.
- `observable_bits_view` — Definition; Specialises demand propagation to observable bit masks.
- `erasure` — Record; Relates an original graph to an erased program.
- `Erasure` — Constructor; Constructs the erasure record.
- `er_demand` — Field; Demand view used by the erasure.
- `er_graph` — Field; Graph view of the transformed program.
- `er_erased` — Field; Identifies edges whose instruction is erased.
- `er_instr` — Field; Instruction associated with each edge.
- `er_inv` — Definition; Original-state invariant under the selected trap policy.
- `er_agree` — Definition; Agreement relation between original and transformed states.
- `erasure_laws` — Record; Matching-step and ending laws for an erasure.
- `er_cfg` — Field; The two programs have the same control-flow graph.
- `er_view` — Field; The transformed graph view satisfies its laws.
- `er_no_stays` — Field; The transformed view has no point-preserving steps.
- `er_kept_forth` — Field; A retained instruction matches an original step forward.
- `er_kept_back` — Field; A retained instruction matches a transformed step backward.
- `er_nop_forth` — Field; An erased instruction matches a transformed no-op forward.
- `er_nop_back` — Field; An erased instruction matches an original step backward.
- `er_ends` — Field; Related states have compatible observable endings.
- `never_traps` — Definition; The original run from a state never traps.
- `dce_conclusion` — Definition; Behavioural claim selected by the trap policy.
- `demand_sound` — Theorem; Agreement on demanded parts preserves behaviour.
- `closed_demand_sound` — Theorem; A closed demand gives behavioural agreement at reachable states.
- `dead_value_removable` — Theorem; States differing only in a dead value have the same behaviour.
- `closed_system_iff` — Theorem; The single-unknown system encodes demand closure.
- `needed_values_closed` — Theorem; Computed needed values are closed under demand dependencies.
- `needed_values_least` — Theorem; Computed needed values are below every closed demand.
- `non_effectful_step_pure` — Theorem; A non-effectful step is silent and preserves state.
- `dce_sound` — Theorem; Erasure satisfies the conclusion of the selected trap policy.

### `AnalysesAdce.v` — ANA-4

- `adce_input` — Record; Graph and effect information for aggressive dead-code marking.
- `AdceInput` — Constructor; Constructs the adce input record.
- `agraph` — Field; Control-flow graph for aggressive dead-code marking.
- `aexits` — Field; Exit nodes used for control dependence.
- `effectful_node` — Field; Marks a node with an observable effect.
- `may_not_terminate` — Field; Marks a node whose loop may diverge.
- `adce_marked` — Definition; Least set of nodes retained by aggressive dead-code marking.
- `skips_to` — Definition; An unmarked path reaches a marked node without earlier marked nodes.
- `adce_closed` — Theorem; Marked nodes satisfy the aggressive dead-code closure rules.
- `adce_least` — Theorem; Marked nodes are the least set closed under the marking rules.
- `adce_skip_unique` — Theorem; Unmarked paths have a unique first marked successor.

### `AnalysesNumbering.v` — ANA-5

- `numbering_problem` — Record; SSA data and purity information for value numbering.
- `NumberingProblem` — Constructor; Constructs the numbering problem record.
- `nsv` — Field; SSA view used by value numbering.
- `pure` — Field; Identifies pure operations eligible for numbering.
- `nvalues` — Field; Enumerates values considered by numbering.
- `dominator_numbering` — Definition; Computes scoped value numbers along the dominator tree.
- `optimistic_numbering` — Definition; Refines a partition to compute optimistic value numbers.
- `numbering_check` — Definition; Checks a proposed value numbering.
- `loop_info` — Record; Header and membership predicate for a loop.
- `LoopInfo` — Constructor; Constructs the loop info record.
- `header` — Field; Header of a loop.
- `body` — Field; Membership in a loop body.
- `loop_info_wf` — Record; Well-formedness conditions for loop membership and header.
- `header_in_body` — Field; The loop header belongs to its body.
- `header_dominates` — Field; The loop header dominates every body node.
- `single_entry` — Field; Every entry into the loop body passes through its header.
- `invariant_in` — Definition; Inductive loop-invariance predicate for a value.
- `numbering_check_sound` — Theorem; Accepted value numbering relates equal values at valid uses.
- `numbering_use_sound` — Theorem; Equal numbers imply equal values at a dominated use.
- `dominator_numbering_checked` — Theorem; Dominator-scoped numbering passes the numbering checker.
- `optimistic_numbering_checked` — Theorem; Optimistic numbering passes the numbering checker.
- `loop_invariant_sound` — Theorem; An invariant value changes at most once per loop execution.

### `AnalysesEgraph.v` — ANA-6

- `term` — Inductive; Variables and operator applications in e-graph terms.
- `TVar` — Constructor; A variable in an e-graph term.
- `TApp` — Constructor; An operator application in an e-graph term.
- `denote` — Definition; Evaluates a term in an environment.
- `equiv_term` — Definition; Equivalence of terms over valid environments.
- `subst_term` — Definition; Substitutes terms for variables in a term.
- `rewrite_rule` — Record; Left side, right side and side condition of a rewrite.
- `RewriteRule` — Constructor; Constructs the rewrite rule record.
- `rule_lhs` — Field; Left-hand side of a rewrite rule.
- `rule_rhs` — Field; Right-hand side of a rewrite rule.
- `rule_side` — Field; Side condition on a rewrite instance.
- `rule_sound` — Definition; A rewrite preserves denotation in valid environments.
- `rewrite_step` — Record; Position, rule, direction and substitution of a rewrite.
- `RewriteStep` — Constructor; Constructs the rewrite step record.
- `step_pos` — Field; Position of the rewritten subterm.
- `step_rule` — Field; Index of the applied rewrite rule.
- `step_forward` — Field; Direction in which the rule is applied.
- `step_subst` — Field; Substitution used for the rule instance.
- `replay` — Definition; Replays an explanation as a sequence of rewrite steps.
- `check_explanation` — Definition; Checks a replayed rewrite explanation.
- `term_eqb` — Definition; Decidable equality test for terms.
- `term_cost` — Definition; Sum of operator costs over a term.
- `egraph` — Definition; Hash-consed nodes and union-find classes for equality saturation.
- `saturate` — Definition; Runs untrusted equality saturation with bounded fuel.
- `extract` — Definition; Extracts a candidate term from an e-graph.
- `optimise` — Definition; Returns an extracted term only after explanation and cost checks.
- `term_eqb_spec` — Theorem; Term equality succeeds exactly for equal terms.
- `check_explanation_sound` — Theorem; An accepted explanation relates equivalent terms.
- `check_explanation_refl` — Theorem; The empty explanation accepts equal terms.
- `optimise_sound` — Theorem; An accepted optimisation returns an equivalent cheaper term.

### `AnalysesScev.v` — ANA-7

- `iexpr` — Inductive; Invariant expressions built from variables, constants, sums and products.
- `IVar` — Constructor; An invariant variable expression.
- `IConst` — Constructor; An invariant integer constant expression.
- `IAdd` — Constructor; The sum of two invariant expressions.
- `IMul` — Constructor; The product of two invariant expressions.
- `eval_iexpr` — Fixpoint; Evaluates an invariant expression in an invariant environment.
- `chrec` — Inductive; Chains of recurrences over invariant expressions.
- `CInv` — Constructor; A loop-invariant recurrence expression.
- `CRec` — Constructor; An additive chain of recurrences.
- `CGeo` — Constructor; A geometric chain of recurrences.
- `eval_chrec` — Fixpoint; Evaluates a recurrence at an iteration count.
- `chrec_add` — Definition; Adds two chains of recurrences.
- `chrec_mul` — Definition; Multiplies two chains of recurrences.
- `chrec_scale` — Definition; Scales a chain of recurrences by an integer.
- `cmp_kind` — Inductive; Comparison kinds used in loop tests.
- `CmpLt` — Constructor; Strict less-than comparison.
- `CmpLe` — Constructor; Less-than-or-equal comparison.
- `CmpNe` — Constructor; Not-equal comparison.
- `signedness` — Inductive; Signed or unsigned interpretation of a word.
- `Unsigned` — Constructor; Unsigned interpretation of a word.
- `Signed` — Constructor; Signed interpretation of a word.
- `view_z` — Definition; Interprets a word as signed or unsigned integer.
- `test_holds` — Definition; Interpretation of an integer comparison at a word width.
- `in_range` — Definition; Whether an integer lies in the selected word range.
- `loop_test` — Record; Comparison, signedness, recurrence and bound of a loop test.
- `LoopTest` — Constructor; Constructs the loop test record.
- `t_cmp` — Field; Comparison used by a loop exit test.
- `t_sign` — Field; Signedness of a loop exit test.
- `t_lhs` — Field; Recurrence tested at the loop exit.
- `t_bound` — Field; Loop-invariant bound in the exit test.
- `loop_view` — Record; SSA and edge information for one loop.
- `LoopView` — Constructor; Constructs the loop view record.
- `lssa` — Field; SSA view underlying the loop view.
- `lheader` — Field; Header of the analysed loop.
- `lbody` — Field; Membership in the analysed loop body.
- `lentry` — Field; Edges that enter the loop.
- `lback` — Field; Back edges of the loop.
- `ltest` — Field; Exit test associated with the loop.
- `scev_ops` — Record; Client operators and integer interpretations used by SCEV.
- `ScevOps` — Constructor; Constructs the scev ops record.
- `width_of` — Field; Word width of a concrete value.
- `to_Z` — Field; Integer interpretation of a concrete value.
- `add_op` — Field; Operator identified as addition.
- `mul_op` — Field; Operator identified as multiplication.
- `const_op` — Field; Operator identified as a constant.
- `scev_ops_laws` — Record; Operator evaluation agrees with the integer arithmetic model.
- `add_laws` — Field; Addition agrees with the integer interpretation.
- `mul_laws` — Field; Multiplication agrees with the integer interpretation.
- `const_laws` — Field; Constants agree with the integer interpretation.
- `inv_env` — Definition; Values of loop invariants in an entry state.
- `stay_arrivals` — Definition; Number of loop-header arrivals along a run prefix.
- `loop_view_laws` — Record; SSA, entry, back-edge and exit-test laws for the loop.
- `l_ssa` — Field; The loop's SSA view satisfies its laws.
- `l_strict` — Field; The loop's SSA view satisfies strictness laws.
- `l_header_not_entry` — Field; The loop header is not a graph entry.
- `l_entry_edge` — Field; Loop entry edges satisfy the view's entry condition.
- `l_back_edge` — Field; Loop back edges satisfy the view's back-edge condition.
- `l_simple` — Field; The loop has the required simple control-flow form.
- `l_back_test` — Field; Back edges obey the loop exit test.
- `recognise` — Definition; Recognises a recurrence for an SSA value.
- `trip_count` — Definition; Computes a trip count for a supported recurrence and test.
- `nowrap_check` — Definition; Checks range evidence for a recurrence and bound.
- `eval_chrec_add` — Theorem; Evaluating recurrence addition gives the sum of evaluations.
- `eval_chrec_mul` — Theorem; Evaluating recurrence multiplication gives the product of evaluations.
- `eval_chrec_scale` — Theorem; Evaluating a scaled recurrence scales its evaluation.
- `scev_sound` — Theorem; Recognised recurrence values agree with reachable loop arrivals.
- `trip_count_sound` — Theorem; A certified trip count matches the affine exit test.
- `loop_trip_sound` — Theorem; Loop back edges respect the certified trip-count bound.

### `AnalysesCalls.v` — ANA-8

- `resolver` — Definition; Selects direct, resolved indirect or fallback call targets.
- `recursive` — Definition; Whether a function belongs to a recursive call component.
- `purity_spec` — Definition; Local impurity and call dependencies for purity summaries.
- `purity_cover` — Definition; Lifts effects into the purity summary's step cover.
- `frame_weights` — Record; Stack weight assigned to each function.
- `FrameWeights` — Constructor; Constructs the frame weights record.
- `weight` — Field; Stack weight assigned to a function.
- `stack_demand` — Definition; Bounds stack demand using call-graph paths.
- `stack_above` — Definition; Actual stack weight above a frame in a state.
- `callee_leaf` — Definition; Tests whether a function has no possible callees.
- `push_ctx` — Definition; Adds a call site to a bounded call string.
- `callstring_system` — Definition; Context-indexed summary constraints.
- `ctx_of` — Definition; Call string associated with a frame in a state.
- `args_view` — Record; Actuals, formals and frame values for call arguments.
- `ArgsView` — Constructor; Constructs the args view record.
- `actuals` — Field; Actual argument values at a call site.
- `formals` — Field; Formal argument values of a callee.
- `frame_val` — Field; Reads a value from a call frame.
- `callers_index` — Definition; Indexes call sites by their possible callees.
- `callers_of` — Definition; Looks up the indexed call sites of a function.
- `arg_fact` — Definition; Joins caller argument facts for a formal parameter.
- `resolver_sound` — Theorem; The resolver includes every possible dynamic callee.
- `recursive_sound` — Theorem; A function active recursively lies in a recursive call component.
- `unreachable_never_runs` — Theorem; Functions unreachable in the call graph never become active.
- `purity_sound` — Theorem; A pure summary excludes observable effects during execution.
- `stack_demand_sound` — Theorem; The path-weight summary bounds stack demand.
- `callee_leaf_sound` — Theorem; A leaf function makes no further call.
- `callstring_sound` — Theorem; Context-indexed summaries cover the matching call strings.
- `callers_index_agrees` — Theorem; The caller index contains exactly the indexed call sites.
- `arg_fact_sound` — Theorem; Joined argument facts cover actual arguments of calls.

### `AnalysesPointsTo.v` — ANA-9

- `ptr_op` — Inductive; Pointer allocation, copy, load, store and escape operations.
- `PAlloc` — Constructor; A pointer allocation operation.
- `PCopy` — Constructor; A pointer copy operation.
- `PLoad` — Constructor; A pointer load operation.
- `PStore` — Constructor; A pointer store operation.
- `PEscape` — Constructor; A pointer escape operation.
- `pts_key` — Inductive; Pointer-value and heap-site unknowns of points-to constraints.
- `PVal` — Constructor; A points-to unknown for a value.
- `PHeap` — Constructor; A points-to unknown for a heap site.
- `site_universe` — Definition; Finite allocation sites appearing in pointer operations.
- `pts_set` — Definition; Finite points-to set over the operation's sites.
- `pts_lattice` — Definition; Finite powerset lattice for points-to sets.
- `andersen_system` — Definition; Side-effecting constraints for Andersen points-to facts.
- `andersen_static` — Definition; Declares reads and side targets for Andersen constraints.
- `ptr_view` — Record; Memory and pointer operations observed during execution.
- `PtrView` — Constructor; Constructs the ptr view record.
- `pmem` — Field; Memory view used by pointer analysis.
- `pval` — Field; Reads a pointer value from a state.
- `pop` — Field; Pointer operations represented by a step.
- `held` — Field; Pointer stored in memory at an address.
- `pbyte` — Field; Byte stored in memory at an address.
- `pts_of` — Definition; Allocation site of a pointer value in a state.
- `heap_pts` — Definition; Whether a site may contain a pointer to another site.
- `ptr_view_laws` — Record; Initial and step-origin laws for pointer targets.
- `pop_listed` — Field; Pointer operations in a step belong to the operation list.
- `pts_initial` — Field; Initial pointer targets satisfy the points-to premise.
- `heap_initial` — Field; Initial heap pointers satisfy the points-to premise.
- `pts_origin` — Field; Every new pointer target has an allowed origin.
- `heap_origin` — Field; Every new heap pointer target has an allowed origin.
- `steens_result` — Record; Pointer classes and their associated pointee classes.
- `SteensResult` — Constructor; Constructs the steens result record.
- `classes` — Field; Union-find classes of pointer variables.
- `pointee` — Field; Class of pointees associated with a pointer class.
- `may_alias` — Definition; Whether two pointer variables may share a unification class.
- `steensgaard` — Definition; Unifies pointer classes for Steensgaard points-to facts.
- `escaped_sites` — Definition; Least set of sites escaping through pointer operations.
- `write_universe` — Definition; Finite footprint universe for zero-byte facts.
- `written_set` — Definition; Finite set of written footprints.
- `zero_written_system` — Definition; Forward constraints tracking footprints written since entry.
- `zero_laws` — Record; Fresh-zero and unwritten-byte preservation laws.
- `z_view` — Field; Graph view underlying zero-byte analysis.
- `z_no_stays` — Field; The zero-byte graph has no point-preserving steps.
- `z_init` — Field; Initial existing blocks satisfy the zero-byte condition.
- `z_fresh` — Field; Fresh allocations contain zero bytes.
- `z_kept` — Field; Unwritten bytes preserve their prior zero value.
- `andersen_sound` — Theorem; The points-to solution covers reachable pointer targets.
- `andersen_monotone` — Theorem; The Andersen constraint system is monotone.
- `andersen_terminates` — Theorem; Finite points-to universes provide termination evidence.
- `steensgaard_sound` — Theorem; Unification classes cover reachable aliases.
- `steensgaard_coarser` — Theorem; Steensgaard classes include least Andersen aliases.
- `escaped_closed` — Theorem; The computed escaped-site set is closed under escape dependencies.
- `zero_written_sound` — Theorem; Uncovered bytes of existing blocks remain zero.

### `AnalysesMemory.v` — ANA-10

- `barrier_view` — Record; Validation and invalidation information for memory accesses.
- `BarrierView` — Constructor; Constructs the barrier view record.
- `bgraph` — Field; Graph view underlying the access barrier analysis.
- `validates` — Field; Accesses validated by an edge.
- `barrier` — Field; Accesses invalidated by an edge.
- `accessible` — Field; Accessibility predicate for an access.
- `barrier_laws` — Record; Accessibility laws for validation and barriers.
- `b_view` — Field; The barrier graph view satisfies its laws.
- `b_no_stays` — Field; The barrier graph has no point-preserving steps.
- `validates_accessible` — Field; A validated access is accessible.
- `accessible_persists` — Field; Accessibility persists across non-barrier steps.
- `accessible_sub` — Field; Accessibility is preserved for covered subranges.
- `accessible_bytes` — Field; An accessible range admits the specified byte access.
- `validated_system` — Definition; Constraints tracking accesses validated since barriers.
- `store_view` — Record; Overwrites, reads and agreement for dead-store analysis.
- `StoreView` — Constructor; Constructs the store view record.
- `sgraph` — Field; Graph view underlying the dead-store analysis.
- `overwrites` — Field; Byte ranges overwritten by an edge.
- `mreads` — Field; Byte ranges read by an edge.
- `sagree` — Field; State agreement for the store analysis.
- `dead_store_transfer` — Definition; Backward transfer for byte ranges covered by later writes.
- `dead_store_system` — Definition; Backward constraints for dead-store coverage.
- `store_laws` — Record; Step and ending laws for dead-store agreement.
- `s_view` — Field; The store graph view satisfies its laws.
- `s_no_stays` — Field; The store graph has no point-preserving steps.
- `s_agreement` — Field; The store relation satisfies agreement laws.
- `s_step` — Field; Store agreement is preserved by matching steps.
- `s_ends` — Field; Store agreement preserves observable endings.
- `bytes_view` — Record; Allocation sites, bytes and node write footprints.
- `BytesView` — Constructor; Constructs the bytes view record.
- `bgv` — Field; Graph view underlying byte-level memory analysis.
- `writes_at` — Field; Footprints possibly written at a node.
- `bsite` — Field; Allocation site of a live memory block.
- `byte` — Field; Byte value at an allocation and offset.
- `bytes_laws` — Record; Byte preservation and graph laws for memory steps.
- `by_view` — Field; The byte graph view satisfies its laws.
- `by_no_stays` — Field; The byte graph has no point-preserving steps.
- `byte_frame` — Field; A changed byte is covered by the node's write footprints.
- `mem_node` — Inductive; Memory definitions and live-on-entry nodes per function.
- `MDef` — Constructor; A memory definition at a function and node.
- `MLive` — Constructor; The live-on-entry memory node of a function.
- `memory_ssa` — Record; Memory definitions selected for loads.
- `MemorySSA` — Constructor; Constructs the memory ssa record.
- `def_of_load` — Field; Memory definition selected for each load.
- `build_memory_ssa` — Definition; Builds an untrusted MemorySSA candidate.
- `no_clobber_check` — Definition; Checks that a MemorySSA path has no overlapping writes.
- `footprints_disjoint` — Definition; Tests whether two footprint lists have disjoint bytes.
- `invariant_load` — Definition; Tests loop-invariant address and non-overlapping loop writes.
- `validated_sound` — Theorem; Validated access facts imply the stated accessibility property.
- `dead_store_sound` — Theorem; Covered writes justify the dead-store agreement claim.
- `footprints_disjoint_sound` — Theorem; The disjointness test implies disjoint covered bytes.
- `no_clobber_unchanged` — Theorem; An accepted no-clobber walk preserves the selected bytes.
- `immutable_sound` — Theorem; Bytes in a footprint without writes remain unchanged.
- `invariant_load_sound` — Theorem; Repeated loads in one loop execution return the same value.

### `AnalysesRules.v` — ANA-11

- `pred` — Inductive; Predicates of the liveness, neededness and reaching rule programs.
- `PUse` — Constructor; The base use predicate of the rules programs.
- `PDef` — Constructor; The base definition predicate of the rules programs.
- `PSucc` — Constructor; The control-flow successor predicate.
- `PNec` — Constructor; The necessary-value seed predicate.
- `PDep` — Constructor; The neededness dependency predicate.
- `PExitUse` — Constructor; The exit-use seed predicate.
- `PLive` — Constructor; The derived liveness predicate.
- `PNeeded` — Constructor; The derived neededness predicate.
- `PReaches` — Constructor; The derived reaching-definitions predicate.
- `pred_encoding` — Definition; Injective encoding of the rule-program predicates.
- `pred_arity` — Definition; Tuple arity of each rule-program predicate.
- `args2` — Definition; Encodes a two-element ground tuple.
- `args3` — Definition; Encodes a three-element ground tuple.
- `extract_live_facts` — Definition; Extracts liveness base facts from graph nodes and edges.
- `extract_needed_facts` — Definition; Extracts neededness base facts from the demand view.
- `v` — Definition; Constructs a rule variable from its index.
- `atm` — Definition; Constructs an atom from a predicate and its terms.
- `liveness_program` — Definition; Datalog rules for liveness.
- `neededness_program` — Definition; Datalog rules for neededness.
- `reaching_program` — Definition; Datalog rules for reaching definitions.
- `live_of_db` — Definition; Converts a rule database to liveness facts.
- `needed_of_db` — Definition; Converts a rule database to neededness facts.
- `reach_of_db` — Definition; Converts a rule database to reaching-definition facts.
- `rules_liveness_solves` — Theorem; The rules database yields a liveness post-solution.
- `rules_liveness_least` — Theorem; The rules liveness solution is least.
- `rules_neededness_solves` — Theorem; The rules database yields a neededness post-solution.
- `rules_neededness_least` — Theorem; The rules neededness solution is least.
- `rules_reaching_solves` — Theorem; The rules database yields a reaching-definitions post-solution.
- `rules_reaching_least` — Theorem; The rules reaching-definitions solution is least.
- `rules_liveness_model` — Theorem; The rules database represents the least liveness model.
- `rules_neededness_model` — Theorem; The rules database represents the least neededness model.
- `rules_reaching_model` — Theorem; The database represents the least reaching-definitions model.
