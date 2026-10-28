# Verified algorithms

Use this reference when a development has a declarative specification and an
executable representation, checker, cache, graph traversal, or iterative algorithm.
For claim domains, vacuity, witnesses, observations, and evidence limits, also read
[specifications](specifications.md).

## Contents

- [Keep the specification independent](#keep-the-specification-independent)
- [Choose the right agreement](#choose-the-right-agreement)
- [Preserve collection semantics](#preserve-collection-semantics)
- [State checker guarantees separately](#state-checker-guarantees-separately)
- [Maintain prepared data](#maintain-prepared-data)
- [Observe current external state](#observe-current-external-state)
- [Prove iterative algorithms in two parts](#prove-iterative-algorithms-in-two-parts)
- [Derive fuel and measure bounds](#derive-fuel-and-measure-bounds)
- [Match theorem domains to real producers](#match-theorem-domains-to-real-producers)
- [Preserve numeric edge behavior](#preserve-numeric-edge-behavior)

## Keep the specification independent

Define the intended relation or result in the clearest representation for its
meaning, often a simple list-based or inductive specification. Define an optimized
implementation separately and prove it satisfies that specification. Do not define
the specification by calling the implementation unless the claim is explicitly
about that implementation.

Keep the simplest model available as a reference when changing data structures or
execution strategy. This lets a proof compare behavior instead of relying on two
implementations that share the same indexing or caching mistake. A list specification
is not automatically correct: state its ordering, duplicate, and failure semantics.

For prepared representations, record which source value they represent and the
invariant that makes them valid. A preparation function and its proof should establish
that invariant; a consumer should state whether it accepts only prepared values or
must validate arbitrary inputs. See [witness coupling and claim
domains](specifications.md#preserve-observations-and-witnesses).

## Choose the right agreement

Prove the comparison that matches the promised observations:

- Use exact result equality when constructors, errors, order, or returned data are
  observable and must be preserved.
- Use pointwise equality for functions when clients observe results at each input.
- Use map extensionality only when the map interface identifies maps by lookup at
  every key; check whether domain membership, order, or duplicate bindings are also
  observable.
- Use a weaker behavioral relation only when the contract explicitly permits the
  erased distinctions.

Do not infer equality of records, caches, or proof-carrying structures from equality
of their useful outputs. Prove the required extensionality and any proof-component
principles separately, or compare through an observational interface. Conversely,
do not weaken an exact contract to pointwise output agreement if clients can inspect
the representation or its failure behavior.

## Preserve collection semantics

Before replacing a list with a map, set, index, or graph representation, determine
whether the specification uses order, multiplicity, or first-match lookup. Preserve
those semantics in both the implementation and its agreement theorem.

- If lookup returns the first matching entry, prove that index construction retains
  that entry when keys repeat; a last-write-wins map is not interchangeable.
- If duplicates represent distinct occurrences, reason over occurrences or a
  multiset. Set membership alone can erase multiplicity.
- If only reachability matters, duplicate edges may be irrelevant, but prove that
  the chosen traversal preserves the same reachable vertices.

Do not add a uniqueness premise merely to simplify a proof unless the actual producer
guarantees it and the theorem is intentionally restricted to that producer's domain.
When uniqueness is required, state and prove it at the boundary where the data is
created or checked.

## State checker guarantees separately

Give a checker a declarative property to recognize, then prove the directions needed
by its callers:

- Soundness: acceptance implies the declarative property.
- Completeness: an input in the specified domain is accepted.
- Decision or reflection: the boolean result corresponds to the proposition, when
  callers need both directions.

These are distinct guarantees. A checker that always rejects may be sound but not
complete. Completeness may be required only for a producer-restricted domain; say so
explicitly and prove that producer outputs satisfy its premises. Do not present a
soundness theorem as a decision procedure or as evidence that valid inputs are
accepted.

If a checker is intended to validate arbitrary prepared data, ensure it checks every
invariant the consumer relies on, including bounds, key uniqueness, correspondence to
the source value, and consistency of cached summaries. A theorem for values returned
by a trusted constructor does not establish safety for caller-supplied values.

## Maintain prepared data

For an index, memo table, cache, or worklist summary, identify its represented source
and state an invariant connecting the two. Then establish both:

1. Initialization: preparation establishes the invariant for the initial source.
2. Preservation: every accepted update preserves the invariant for the changed source.

If updates can bypass the proved transition, validate or rebuild before relying on
the prepared value. Keep this check at the boundary that receives untrusted or stale
data. Do not turn correct cache initialization into a caller obligation when the
implementation owns construction and maintenance.

When an update changes only part of the source, prove that unaffected entries remain
valid and that invalidated entries are recomputed. A cache may be extensionally
correct at initialization yet become stale after mutation; test and prove update
cases, not just construction.

## Observe current external state

When an algorithm depends on a mutable external resource, such as a filesystem,
environment, or service, make clear whether it promises a snapshot or behavior
against the current state. Do not cache a one-time observation and silently use it
as if it tracked later changes.

If the operation can race with external changes, specify the synchronization,
versioning, snapshot, or retry protocol that makes its observation coherent. Keep
external assumptions explicit and distinguish the proved abstract interface from
the concrete service implementation. For trusted-boundary accounting, see [logical
and executable boundaries](specifications.md#separate-the-logical-and-executable-boundaries).

## Prove iterative algorithms in two parts

For a worklist or fixed-point computation, separate termination from the result it
computes. Prove a decreasing well-founded measure (or another termination argument)
for the loop. Independently prove that the returned state satisfies the desired
fixed-point or closure property.

Show that each pending item is eventually processed or otherwise justify why it may
be discarded. If processing an item can add more work, prove that additions preserve
the invariant and that termination still follows. A finite state space alone does
not prove termination if the algorithm can revisit states indefinitely; conversely,
termination alone says nothing about whether all required items were considered.

For a finite-height worklist, one possible measure adds remaining rank capacity
over the finite key domain to the number of pending items. If unchanged updates
add no work, and changed updates consume at least as much rank capacity as the
work they enqueue, propagation does not increase this measure; popping an item
strictly decreases it. Prove rank bounds, closure of keys, and the actual queue
size laws before using this argument. Enqueuing without a charged change or
allowing non-increasing ranks can invalidate it; choose another measure then.

State the fixed-point condition precisely: equality, inclusion, stability under a
transfer function, or closure under edges can differ. Prove the returned result is
the intended least/greatest solution only when the algorithm and contract require
that stronger property.

## Derive fuel and measure bounds

Connect fuel to the actual transition relation. State whether fuel counts steps,
recursive calls, constructors, or rounds, and prove that the chosen bound covers the
maximum required work. Check base cases and off-by-one behavior explicitly.

Derive arithmetic bounds for the measure from the algorithm's real input domain.
For subtraction, division, logarithms, or machine integers, prove positivity and
range conditions before using a decrease argument. Account for overflow, wrapping,
conversion, and zero-sized inputs where the carrier permits them. An informal
expectation that a producer returns positive values is not a premise until connected
to the theorem's domain.

Keep the recursion argument visible in the proof: identify what decreases in each
recursive branch, and make any generalized parameters explicit when induction must
cover changing fuel, bounds, or suffixes. Inspect the generated induction principle
when nested or indexed data changes the expected induction hypothesis.

## Match theorem domains to real producers

Read the full quantifier and premise structure of an algorithm theorem. Distinguish
arbitrary inputs from well-formed, reachable, or producer-generated inputs. A lemma
proved only for values emitted by a constructor does not establish correctness for
all values of the public type.

When a useful theorem is restricted to producer outputs, prove the connection from
the producer to the theorem's domain, then prove the consumer uses such outputs. If
an internal helper is relied on by the public result, connect it through an actual
consumer proof; an unused helper theorem does not establish integrated correctness.
Keep legitimate producer restrictions, but name them and expose the boundary where
they are guaranteed.

When a transformation changes allocation counts, do not assume future fresh identifiers
remain equal. Packing several source objects into one target frame, for example, can change
the numbering of later allocations. Maintain the actual representation relation through
those allocations and relate metadata keys through it. For a memory injection, account
for offsets, freshness, permissions, deallocation and target-only padding as required by
the model. Reuse the library's allocation/free transport lemmas and discharge their
premises; an initial injection or one allocation lemma alone is not the full simulation.

To assess whether a domain is useful, test an intended producer output and a small
forbidden or boundary case. Such examples can reveal vacuity or an overstrong
restriction, but do not replace a universal proof. See [checking whether a claim is
useful](specifications.md#check-that-the-claim-is-useful).

## Preserve numeric edge behavior

Specify zero, empty, negative, and boundary inputs according to the actual carrier
and operation. Do not equate zero with absence unless the representation and
semantics make that equivalence valid. An empty range, a zero-length object, an
unbounded limit, a missing value, and a sentinel can have different meanings.

For ranges, state endpoint inclusivity and prove that conversions, additions, and
one-past endpoints stay in bounds. For sizes and capacities, state whether zero
admits an empty payload, an empty allocation, or rejection. Check the exact operation
at minimum and maximum values rather than relying on mathematical integers when the
implementation uses bounded arithmetic.
