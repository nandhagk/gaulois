# Gaulois

Gaulois is a standalone Rocq library for verified program analysis. It provides common data
structures, constraint solvers, semantic views and reusable analyses without assuming a particular
compiler, graph representation, control structure or word size. It is MIT licensed.

A client supplies a graph and a sound transfer for each edge. For example, on the true edge of
`x < 10`, an interval analysis can refine an unsigned `x` to `[0, 9]`; an impossible edge produces
bottom. The library's intended solver returns a post-solution, and the view's soundness theorem
connects that result to the client's semantics. This example describes the planned API; it is not
executable in the current skeleton.

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
| Bits | Fixed-width word operations and expressions |
| Domains | Numeric, demand, address and equality domains |
| Views | Language semantics, graph, SSA, structured, call and memory adapters |
| Analyses | Compositions of the shared components |
| Float | Optional floating-point domains using Flocq |
| Examples | While and Ssa reference clients |

## Status

The repository contains the build skeleton and API contracts. Analyses and their proofs are planned,
not implemented. The skeleton has passed a build check; the contracts have been reviewed but have
not been compiled as a whole. See [catalogue](docs/catalogue.md) for planned coverage and
[trust](docs/trust.md) for what each kind of evidence establishes.
