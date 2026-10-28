# Analysis catalogue

Every entry below is planned and unimplemented in the current skeleton. Contracts in `api/` specify
the contracted definitions and claims; the cards assign implementation and verification work.
A catalogue entry is a composition of shared domains, views, solvers and checkers.

- **Graph:** reachability, RPO, merge nodes, selectable LT and Semi-NCA dominators and
  post-dominators, frontiers, control dependence, SCCs, loops, WTO, reducibility, forwarding
  chains and colouring.
- **Dense dataflow:** liveness, reaching definitions, available and very busy expressions, lazy
  code motion, must-equality, zero-since-entry.
- **Structured:** liveness with loop certificates and region summaries including
  normal completion, labels, nesting and height.
- **Values:** sparse conditional constant propagation, known bits, wrapping intervals, reduced
  products, edge predicates, path facts and guard chains.
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
