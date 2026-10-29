# Gaulois

Gaulois is a standalone Rocq library for verified program analysis. It provides common data
structures, constraint solvers, semantic views and reusable analyses without assuming a particular
compiler, graph representation, control structure or word size. It is MIT licensed.

A client supplies a graph and a sound transfer for each edge. For example, on the true edge of
`x < 10`, an interval analysis can refine an unsigned `x` to `[0, 9]`; an impossible edge produces
bottom. The library's intended solver returns a post-solution, and the view's soundness theorem
connects that result to the client's semantics. The While reference client exercises several dense
analyses; the interval example describes the intended general client API.

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

At commit `f8f35c8` on 2026-10-29, the engines, views and toys milestone M2 is reached: all
cards assigned to it have landed. Foundations, Graph, Fixpoint, domain components, stratified
Rules solving and the Rewrite core through finite witness extraction are present. Landed analyses
include dense dataflow, demand and sparse available/busy evaluation graphs. The While client has
view proofs and dense analysis examples; the Ssa language is present, while its analysis clients
remain in progress or planned. Typed extraction and a benchmark harness have landed.

The snapshot has 71 of 100 cards landed. MemorySSA constructors, advanced analyses, remaining
clients and Float remain pending. Landed cards report kernel-checked claims and computed examples
for their assigned contracts; they do not establish the whole library. See
[catalogue](docs/catalogue.md) for scope and [trust](docs/trust.md) for evidence. Contracts not yet
implemented are specifications, not compiled interfaces.
