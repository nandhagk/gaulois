# Design

Gaulois expresses analyses as constraint systems over reusable domains and language views. Its core
uses Rocq Stdlib alone. Float is the optional Flocq-dependent package. A client chooses its own
nodes, maps its operators to the word language, and proves that its semantics respects the views it
uses. The contracts specify the intended interfaces; implementation status is in the README.

## Layers

```text
                         Analyses      Examples
                     Views    Rules    Rewrite    Float
                       Fixpoint    Domains
                     Graph  Order   Bits
                        Collections
```

The diagram indicates composition, not every dependency. `Bits` uses Collections for encodings;
package contracts and their dune theories give the precise dependencies. Collections provides
injective encodings into `positive` and canonical tries. Maps and sets hide that representation.
Dictionaries are explicit records parameterised by their carrier types, with separate `Prop` law
records and no global instances. This design supports typed extraction. Lattice laws require a
preorder, bottom and upper bounds; least-upper-bound laws are separate because some domains do not
have them.

## Constraints and checking

A right-hand side is a query tree: `Ret a` returns a value, `Ask x k` reads an unknown, and
`Side x a q` contributes a value to another unknown. A post-solution bounds all returns and side
contributions. Static systems over-approximate reads and contributions and support termination
arguments, scheduling and cut-point checking. Dynamic systems use the full checker and fuel solver.
A checked precision pass keeps its candidate only when the checker accepts it.

Engines return a function with a post-solution proof. Directly proved internal dominance, WTO,
rewriting and MemorySSA producers are planned alongside independent checkers for external or
cached candidates. The legacy explanation checker remains the boundary for external replay;
arbitrary narrowing and partial solutions retain their checked acceptance requirements. Selectable
LT and Semi-NCA dominance implementations prove the same reachable dominance relation. Schedules
with widening may produce different post-solutions.

## Views and clients

A semantics adapter describes transitions and observations, including events, traps, divergence and
resource stops. Layered graph, SSA, structured, effects, calls and memory views connect generic
analyses to a client language. A forward theorem gives invariants; backward agreement describes
which parts of two states must coincide and supports behaviour-preserving transformations. Effect
policy controls whether an unread trapping operation may be removed. Dropping such a trap gives a
conditional refinement, not unconditional equality of behaviour.

The operator bridge maps each client operator to a `Bits` expression and proves its evaluation
agrees whenever the client operation returns a result. Client traps remain in client semantics.
Edge transfers can refine facts using guards; strict SSA permits guarded facts at dominated uses
under the stated dominance and equation premises. Structured programs use a binary sequence tree,
relative jumps and a frame machine. Loop certificates are cut points in the same constraint system,
not a separate solver. Replay folds observers over points and facts without retaining extra results.

Prepared indexes carry agreement lemmas; the design avoids list scans inside loops. Engines use
binary fuel or well-founded recursion, and extraction directives live outside theories. Clients own
summary contents, contexts, effect policies and invalidation; rechecking a changed program is one
way to validate a cached result.
