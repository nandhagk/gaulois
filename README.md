# Gaulois

Gaulois is a standalone Rocq library for verified program analysis. It provides common data
structures, constraint solvers, semantic views and reusable analyses without assuming a particular
compiler, graph representation, control structure or word size. It is MIT licensed.

A client supplies a graph and a sound transfer for each edge. For example, on the true edge of
`x < 10`, an interval analysis can refine an unsigned `x` to `[0, 9]`; an impossible edge produces
bottom. The library's intended solver returns a post-solution, and the view's soundness theorem
connects that result to the client's semantics. This example describes the planned API; it is not
yet an executable end-to-end client in this repository.

Read [design](docs/design.md) for the architecture, [catalogue](docs/catalogue.md) for the scope,
[trust](docs/trust.md) for evidence, and [workflow](docs/workflow.md) to build. The binding public
contracts are in [docs/api](docs/api/), with a [name index](docs/api/names.md). Contributors read
[AGENTS.md](AGENTS.md) and their assigned card as well.

| Package | Purpose |
| --- | --- |
| Collections | Encodings, canonical tries, maps, sets and supporting structures |
| Order | Lattices, domain combinators, concretisation and agreement |
| Graph | Graph algorithms, certificates and checkers |
| Fixpoint | Constraint systems, solvers, checkers and replay |
| Rules | Stratified Datalog compiled to constraint systems |
| Rewrite | Generic sorted rewriting, e-graphs and directly proved bounded saturation |
| Bits | Fixed-width word operations and expressions |
| Domains | Numeric, demand, address and equality domains |
| Views | Language semantics, graph, SSA, structured, call and memory adapters |
| Analyses | Compositions of the shared components |
| Float | Optional floating-point domains using Flocq |
| Examples | While and Ssa reference clients |

## Status

At 2026-10-28 23:41 UTC, the landed foundations include Collections, Order and Bits, numeric and
interval domain components, and the source and claims checking tool. Graph includes reachability,
two dominance producers, SCCs, loops and colouring components. Fixpoint includes checking and
fuel-bounded and total worklist solvers. Rewrite includes sorted syntax, e-graph rebuilding and
pattern matching and client-defined class analyses. Rules syntax and basic semantic views are also
present. Landed cards report kernel-checked claims and computed examples for their assigned
contracts; they do not establish the whole library. Most analyses, later views and clients remain
planned. The run ledger records
the changing card status; see [catalogue](docs/catalogue.md) for scope and [trust](docs/trust.md)
for the evidence. Contracts not yet implemented are specifications, not compiled interfaces.
