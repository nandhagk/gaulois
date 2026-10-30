# Trust and evidence

Every contracted `Theorem` is a claim to prove, not evidence by itself. A kernel-checked claim is a
proved theorem whose assumptions meet the policy below. A statement that compiles has type-checked;
it does not establish a proof. A smoke check reports an outcome on examples. An experiment reports
measurements and does not prove a general complexity or soundness claim.

At commit `1e58e42` on 2026-10-30, M2, M3, M4, M6 and M7 are reached. Landed reports and reviews
record targeted builds, examples, checks and assumption audits for their assigned claims. EX-4's
report records 123 closed assumption checks and computed While examples; its review independently
observed the repository check pass and inspected the worker's build and test evidence. These are
incremental checks, not a fresh full build. They establish claims under their stated premises, not
unimplemented contracts. The API documents are specifications and have not been compiled as a
whole. FINAL is planned to check a fresh full build.

ANA-7's C64 contract retains recurrence algebra, signed and raw observations, exact first
failure over wrapped values and separate no-wrap evidence. Its supported recognition domain
includes ranked earlier dependencies and direct doubling; unsupported nonlinear and mutual
feedback are rejected. The actual count-up client supplies its view laws and theorem applications.
Tagged word constants support signed observations while ordinary integer constants remain
mathematical coefficients. The wrapped trip search includes a proved whole-word period and first
failure; a width-two cycling example returns `None`. Finite examples also cover signed descending
recognition, no-wrap rejection, ranked dependencies and actual reachable client paths.
The approved C14 corrections rename the node carrier of `loop_trip_sound` from `N` to `Node`,
so `(t : N)` is binary natural, and make the `iexpr` and `chrec` constructor carrier arguments
implicit. These corrections are already in the published API; C64's semantic changes are separate.

The first ANA-7 review found repeated expansion of shared dependencies and requested proof
factoring. C68 retains prepared indexed dependencies through the producer, checker and compiler,
with context-validated reuse and exact agreement for valid and malformed public trees. The
cache keys distinguish complete expression structure; reuse checks rank or the relevant phi
environment and recomputes when those observations change. Arbitrary external trees may still
require structural ingestion. The original review's final-value example alone did not establish
sharing; the accepted implementation exercises the actual integrated path. The accepted full
review reports both findings resolved, checks both directions for the four plan
conditions and the compiler translation, and independently reruns the targeted build and check.
It inspects the worker's full test, formatting and 603 closed-root audit, including 63 public type
queries. The integrated fixture observes producer reuse and five checker and compiler cache hits,
including cross-binding reuse; these are finite checked observations, not an asymptotic bound.
The worker retains 222 original statements and all 52 original examples, and adds seven sharing
and context examples. The review inspects the final audit and tests rather than rerunning them.
The review records a scratch working-directory deviation and preserved cache evidence. These
incremental checks do not replace FINAL or prove source-to-native runtime correspondence.

C62 assigns legacy-qualified SSA facade compatibility to mandatory EX-7, which is active at
this snapshot. The landed client modules do not establish that compatibility. The ANA-10e C14
site-encoding correction is already present in the API: `no_clobber_check` and
`no_clobber_unchanged` pass `ET` alongside `EN` and `EF`. ANA-10a's earlier missing `sigma`
quantifier report is preserved; C67 subsequently revises the semantic field and the published
contract includes its quantified assignment. Neither historical diagnostic proves the revised law.

At commit `3281819`, M7's Rewrite cards and the ANA-6 facade have landed. Their reports and
independent reviews record targeted builds, checks, closed claims and computed examples. REW-7's
review reruns its targeted build and repository check and inspects the worker's test and audit
evidence. These are incremental checks, not a fresh proof replay for the entire library.

The facade can return `None` when it cannot produce an accepted explanation for the selected
minimum tree. Finite scheduling does not establish fairness or saturation completeness. The
extractor's optimum is for materialized additive tree cost, not shared-DAG or program cost.
The SSA region proof covers a pure expression; whole-program replacement also needs the stated
client bisimulation law. Order facts permit undefined results; nonzero facts require validation.

ANA-15's accepted review reruns its targeted build and repository check and inspects the final
630-root closed-context audit. Its source-frame diagnostic uses a manual legal plan and an actual
FRG link; it does not instantiate the formerly absent producer. The delayed-choice diagnostic
refutes the superseded stuttering method, not the behavior theorem. The completed proof instead
uses actual complete paths under the stated laws. The three owned files have 4,614, 1,770 and
2,754 lines; fixed ownership overrides the skill's file-size guidance. These checks do not prove
PRE optimality or extracted runtime correspondence.

FLT-1's accepted review checks all twenty public theorems against their stated contracts and
independently reruns `just test` and `just check`. The worker reports a targeted build and a
477-root assumption audit: 295 roots are closed, including all 102 test roots, and the remaining
182 Float roots use only the four approved identities below. The review inspects that audit; it
does not rerun it. The 31 computed examples are finite observations, not universal proofs.
Float's finite enclosure keeps both zero signs when it contains zero. Division uses the full
ordered hull when a nonzero-containing divisor envelope touches or spans zero; zero-only divisors
contribute through the exceptional-value table. These are conservative choices, not least-hull
or exact zero-sign guarantees.

The published Float API already includes the C14 `option cval` demand carriers and the
`finite_map`, `demand_lattice` and view-argument corrections to `ssa_nan_demand_sound`. C43's
full exit demands and C53's parameter-input demands are separate semantic rulings. The original
parameter omission and Flocq trust diagnostics inform those rulings; they do not prove the revised
laws. The worker reports two earlier memory failures and a test proof repair, followed by passing
final gates under the original caps. These results do not replace the planned fresh full build.

## Assumptions

Outside Float, each `Theorem` must be closed under the global context. No new axioms, `Parameter`,
`Conjecture`, `Admitted` or admitted proofs are permitted. Do not import axiom-bearing Stdlib
modules for those proofs. `gaulois check` audits kernel-reported assumptions as well as source
hygiene and layout. Individual reports also record any separate `Print Assumptions` audits.

C13 and C56 permit `Gaulois.Float` theorems to depend only on these exact axioms:
`Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec`,
`Stdlib.Reals.ClassicalDedekindReals.sig_not_dec`,
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`, and
`Stdlib.Logic.Classical_Prop.classic`. Pinned Flocq operations and bit decoders inherit `classic`
as well as the classical real-number foundations. The owner approves this additional dependency
under C56. The claims checker must use the same exact list.
This allowance does not extend to other packages, examples or tests.
FLT-1's checker controls accept each approved identity for Float and reject an unrelated Float
axiom, `classic` outside Float, and ambiguous, unrecognized or spoofed identities.

## Producers and checkers

A solver's post-solution proof establishes its stated constraints under its hypotheses. Semantic
soundness also depends on the client's view laws. Verified checkers allow untrusted producers to
supply candidates; acceptance is meaningful only under the checker's stated premises. Cards require
nontrivial accepted examples or a suitable completeness theorem so that a checker is exercised.
Checked narrowing retains the previous solution if a candidate fails. Directly proved internal
producers need their own closed correctness proofs; checkers remain available for external and
cached candidates. Legacy MemorySSA byte preservation retains its stated stronger premises and
requires a proved projection from the new version graph where applicable.

The sign-separated bit-and-bounds domain's landed card reports direct reduction and transfer
proofs under its stated contracts. Its representation alone would not establish those proofs.

`just check` compiles the selected generated closures before inspecting their fixed artifact
inventory for `Obj.magic` and Rules universe enumeration. Standard erased-proof placeholders use
`Obj.t` and `Obj.repr`; native natural numbers use an integer realization. The bounded benchmark
inputs stay within native integer range, but arbitrary-size correspondence and source-to-native
runtime correspondence are not proved. Generated code has localized warning exceptions; authored
OCaml retains its warning policy.

The behaviour theorem distinguishes the effect policies: retaining traps supports the stated
behaviour equality; deleting unread traps supports the contract's conditional refinement. Proofs
about examples demonstrate the toy clients under their own semantics, not arbitrary client code.
