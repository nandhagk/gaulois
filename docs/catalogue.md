# Analysis catalogue

The catalogue describes the intended scope, including work not yet implemented. Contracts in
`api/` specify definitions and claims; cards assign implementation and verification work. A
catalogue entry may compose several shared domains, views, solvers and checkers.

At commit `b3e8d41` on 2026-10-29, landed work covers foundations, parts of Graph and Fixpoint,
the generic Rewrite core through witness extraction, stratified Rules solving and indexed joins,
basic views, and parts of the numeric and memory domains. Individual landed cards report checked
claims and examples; the remaining entries and compositions are not implied to be complete. The
run ledger is the current card-by-card status.

- **Graph:** reachability, RPO, merge nodes, selectable LT and Semi-NCA dominators and
  post-dominators, frontiers, control dependence, SCCs, loops, WTO, reducibility, forwarding
  chains and colouring.
- **Dense dataflow:** liveness, reaching definitions, available and very busy expressions, lazy
  code motion, must-equality, zero-since-entry.
- **Structured:** liveness with loop certificates and region summaries including
  normal completion, labels, nesting and height.
- **Values:** sparse conditional constant propagation, known bits, wrapping intervals, reduced
  products, a selectable sign-separated bit-and-bounds domain, edge predicates, path facts and
  guard chains.
- **Neededness:** dead values, demanded bits, aggressive dead code and observable bits.
- **Equality:** dominator-scoped value numbering, optimistic GVN, loop invariance and generic
  directly proved bounded e-graphs with checked explanations.
- **Loops:** chains of recurrences, trip counts with separate no-wrap evidence, and loop idioms.
- **Calls:** indirect targets, recursion, interprocedural constants, purity,
  stack demand, callee shape, reachability and call-string contexts.
- **Memory:** Andersen and Steensgaard points-to, escape, allocation and fresh-zero facts, access
  epochs, dead-store coverage, directly proved MemorySSA constructors with external checking,
  immutable data and invariant loads.
- **Float:** finite-float intervals and NaN observability over floating-point semantics.
- **Rules:** liveness, neededness and reaching definitions as stratified rules, related to their
  lattice formulations.

The planned static occurrence census counts atom operands. No-return, mod/ref and store-to-load
contracts require their stated client semantics; unknown effects remain conservative.

Float is an optional dependency for clients, but its implementation card is required for this run.
Clients choose summary components, contexts, effect policies and cache invalidation. Results
are subject to the hypotheses in their individual contracts, including well-formed views and any
required forward facts.
