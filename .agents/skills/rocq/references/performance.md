# Diagnose Rocq performance

Use this reference when compilation, proof checking, reduction, extraction or a
related build becomes expensive. First identify the expensive phase and the exact
work being compared. A local timing is evidence about that setup, not a general
rule about Rocq.

## Contents

- [Locate the expensive phase](#locate-the-expensive-phase)
- [Make comparisons controlled](#make-comparisons-controlled)
- [Distinguish elaboration, reduction and checking](#distinguish-elaboration-reduction-and-checking)
- [Choose proof and representation boundaries](#choose-proof-and-representation-boundaries)
- [Interpret memory and concurrency evidence](#interpret-memory-and-concurrency-evidence)
- [Stop and report reliably](#stop-and-report-reliably)

## Locate the expensive phase

Separate at least these phases before changing a proof or representation:

| Phase | Typical work | Evidence to collect |
| --- | --- | --- |
| Parsing/elaboration | notation, implicits, typeclass search | command timing or profiler |
| Tactics | search, simplification, broad rewriting | tactic profiler or focused timing |
| Kernel checking | conversion and checking produced terms | proof or file checking time |
| Loading/serialization | compiled libraries and dependencies | build trace and target timings |
| Extraction/target compile | roots and generated code | stage-separated timings |
| Printing/diagnostics | rendering large terms or goals | time the query separately |

These phases can overlap in a user's view of one command. A slow tactic is not
necessarily a slow kernel check: tactics produce terms, then the kernel checks
them. A slow `Qed` can indicate expensive checking or conversion, but timing it
alone does not prove which. Likewise, a long `Print` or `Show` may be dominated by
rendering rather than proof construction.

Record the first slow command, target, dependency closure, source revision, tool
versions, build state, wall time and CPU time when available, peak memory, memory
measurement boundary, and parallel jobs. Preserve the first diagnostic and the
build system's report. Do not infer a kernel bottleneck from a whole-build time.

## Make comparisons controlled

Compare equivalent work under the same source, toolchain, machine, memory limit,
job count and checking level. Change one factor at a time where practical. Keep
both the raw result and enough context to reproduce the comparison.

- **Net versus total:** report the target's own time separately from total build
  time, which includes dependencies and build-system overhead. A target can get
  faster while its dependency cone gets slower, or vice versa.
- **Leaf versus dependency cone:** compare an isolated file only when its
  dependencies are already available. Also measure the intended consumer or
  dependency closure; an interface change may invalidate downstream files.
- **Cold versus warm:** label clean builds, forced rebuilds, and incremental
  no-op or warm checks separately. Confirm which compiled artifacts were reused.
  Never compare a warm result with a cold one as if they measured the same work.
- **Equivalent checking:** do not compare a development shortcut, partial check
  or interactive query with an ordinary fully checked build as equivalent
  evidence. Name what each mode establishes.
- **Repeated observations:** repeat noisy measurements and report spread, not
  only the fastest run. Keep machine load and concurrent work stable or record it.

For a proof change, inspect the diff and compare the same theorem and consumers.
Fewer lines, a shorter tactic script or a smaller source file do not establish a
speed improvement. A successful build after an unrelated edit is not a controlled
comparison.

## Distinguish elaboration, reduction and checking

Elaboration resolves notation, names, coercions, implicit arguments, typeclass
instances and dependent types. If it is slow, inspect ambiguous expressions,
large inference problems, notation expansion, and typeclass search before
changing proof opacity or executable representations.

Tactic execution and kernel checking are separate costs. Broad `auto`, repeated
rewriting, unrestricted simplification, or a large search can consume time while
constructing a proof. A compact tactic can still produce a large term, and a
small script can still require expensive kernel conversion. Profile the actual
slow command and inspect the term or context where feasible.

Conversion checks definitional equality by reduction. If conversion expands a
large recursive definition, dependent record, match or memory structure, prove
and use a smaller equation or specification lemma. Reduce only the discriminant
or field needed by the next step. Generalize changing accumulators, endpoints or
environments before induction when the induction hypothesis needs to quantify
over them.

For a proof about a large computed structure, use its pointwise or structural
laws when those give the needed observation. A local opacity boundary can keep
ordinary conversion from unfolding the bulky helper, while small fixtures may
still benefit from direct reduction. In Rocq 9.3, `vm_compute` and
`native_compute` ignore changeable `Opaque` settings; they do not unseal a proof
closed with `Qed` ([Rocq 9.3 conversion manual][rocq-conversion]).
Choose the boundary for the evaluator actually involved, and ensure the goal can
be solved through the exposed laws.

Adjustable `Opaque` settings are not permanent sealing: conversion can still unfold
those definitions. Tactic-local conversion strategies also need not persist at
`Qed`/`Defined` or independent artifact checking. A faster tactic sentence is
therefore insufficient evidence; check the finished proof and required consumers
under their actual conversion behavior.

Keep diagnostics distinct from proof checking. Large goals can be expensive to
print; queries can force computation independently of the theorem being checked.
Time the query separately and avoid using a printed term's size as a proxy for
kernel cost.

## Choose proof and representation boundaries

Prefer a proof shape that exposes the invariant the next step needs. Named helper
lemmas can replace repeated normalization of a large object with a small local
fact. They can also add declarations, imports and checking work, so measure the
real dependency closure before treating factoring as a performance win.

If an executable structure repeatedly scans lists, consider preparing an index
or cache once and proving exact agreement with the list specification. Keep the
specification useful for statements and proofs. For a cache owned and maintained
by the implementation, establish initialization and preservation internally;
do not make callers prove its invariant. A caller-supplied prepared value may
legitimately require a documented invariant, or a validation/rebuild path before
use. Compare construction cost, query cost, memory use and total workload. An
index helps only when its setup cost and representation are justified by the
uses that follow.

If the contract permits a more efficient representation, state the relation to
the existing specification and prove the required agreement. Preserve ordering,
duplicate handling, failure cases and observations. A finite computation can
exercise an implementation but does not prove a universal agreement theorem.
Inspect extracted code and runtime behavior separately when extraction changes
the representation.

Use opacity for its semantic purpose, then measure the consumer that matters.
Opaque theorem proofs generally avoid exposing proof bodies to ordinary
conversion; transparent proofs are appropriate when the proof term itself is
intentional computational data. Do not make a proof transparent merely because
an unrelated computation is slow. Do not make every lemma opaque as a blanket
optimization: a client may need its body to reduce, or the bottleneck may be
elaboration, tactic search or module abstraction instead. Keep computational
definitions transparent when clients rely on their equations, and expose small
equations through the intended interface when implementation bodies should stay
hidden.

Preparation and sharing can move work rather than remove it. An index may make
each lookup cheaper while increasing initialization and memory. A shared module
may reduce duplicated source while making applications or interfaces harder to
infer. Check initialization, compilation, checking, extraction and downstream
use separately; pilot a shared abstraction with real clients before broad
migration.

## Interpret memory and concurrency evidence

Name the measured boundary. A process's resident set, a process tree's peak, a
container or cgroup peak, and a host-wide memory reading answer different
questions. A build may use child workers whose memory is absent from a
single-process sample. Record the enforced limit and the mechanism that applied
it, including whether child processes were covered.

Treat garbage-collector settings and job counts as tuning controls, not hard memory limits.

Distinguish memory exhaustion from timeouts, manual interruption, kernel or
elaboration failures, and build-system errors. Preserve exit status, signal,
diagnostics and resource-controller evidence when available. A killed worker
without a reliable status or memory record is an unexplained failure, not proof
of an out-of-memory event. Do not retry unchanged work until the failure has
been classified and the build system's recovery guidance followed.

Bound concurrency to the available memory and processor budget. Parallel jobs
can reduce elapsed time while multiplying peak memory, so measure both. Avoid
uncontrolled overlapping builds when diagnosing a regression. Use the project's
supported job controls and artifact ownership; do not manipulate build outputs
behind the build system.

Treat caches as an experimental variable, not a universal setting. A warm cache
may hide compilation work; a disabled cache may expose more work or alter memory
pressure. Match cache state across comparisons and record it. Change a cache
policy only when the project supports it and a controlled comparison shows that
the policy addresses the measured bottleneck without invalidating artifacts or
changing the claim being measured.

## Stop and report reliably

Set a bounded target, time budget and memory limit before an expensive
experiment. Use the supported interruption mechanism, preserve the final output
and build report, and verify whether child processes stopped. A timeout or
interruption provides resource evidence only; it does not show that a proof is
false or that no result exists.

After a failure, inspect the first useful diagnostic and resource report before
retrying. Identify the change in source, environment, build state or execution
conditions that addresses the failure. Use build-system-aware recovery so stale
or incomplete artifacts are not mistaken for successful outputs.

State the conclusion at the strength of its evidence:

| Evidence | Supports |
| --- | --- |
| Source inspection | A plausible cost mechanism |
| One timed command | A measurement for that input and environment |
| Controlled repeated comparison | A change in the measured workload under stated controls |
| Fully checked proof | Kernel acceptance of that declaration and its dependencies |
| Runtime benchmark | Performance of the measured extracted or compiled program and workload |

Do not infer universal performance from one target, machine, input, warm state,
or workload. Report semantic correctness, resource use and runtime speed as
separate results.

[rocq-conversion]: https://rocq-prover.org/doc/V9.3.0/refman/proofs/writing-proofs/equality.html
