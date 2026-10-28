# Specifications and trust

## Contents

- [Read the whole claim](#read-the-whole-claim)
- [Check that the claim is useful](#check-that-the-claim-is-useful)
- [Preserve observations and witnesses](#preserve-observations-and-witnesses)
- [Check simulation direction](#check-simulation-direction)
- [Keep assumptions attributable](#keep-assumptions-attributable)
- [Separate the logical and executable boundaries](#separate-the-logical-and-executable-boundaries)
- [Report evidence precisely](#report-evidence-precisely)
- [Handle a suspected false contract](#handle-a-suspected-false-contract)

## Read the whole claim

Before proving or refactoring a theorem, follow the definitions behind its statement.
An unchanged theorem line can acquire a different meaning when an imported predicate,
record field, interpretation, instance or contract alias changes.

Write down the inputs, quantifier order, premises, conclusion and observations. Identify
which inputs are arbitrary and which come from a checked producer. Check whether a theorem
concerns all states, well-formed states, reachable states, or states satisfying a relation.
These are different claims. Reachability is often the right invariant, but adding it to a
previously universal contract is a specification change that must be explicit.

Distinguish the result being promised:

| Result | What the proof must establish |
| --- | --- |
| Partial correctness | Every successful result meets the stated relation |
| Termination or totality | The specified computation terminates or produces a result |
| Checker soundness | Acceptance implies the declarative property |
| Checker completeness | The stated declarative domain implies acceptance |
| Exact agreement | Two forms return the same specified result, including failures |
| Refinement | The precise permitted relation between observable behaviors |

Prove the directions the task actually requires. Soundness does not imply completeness.
A validator can be appropriate; a sound validator that rejects everything needs a separate
success/completeness argument if useful acceptance is part of the contract.

A correctness statement can legitimately mention the algorithm it verifies. Dependency
layouts that isolate fixed contracts from candidate implementations are project policies;
their purpose is to prevent a candidate from quietly defining its own success criterion.
Preserve that separation where it is required without imposing one directory architecture
on every formalization.

## Check that the claim is useful

Try a small intended inhabitant of the domain and a small forbidden case. This does not
prove general non-vacuity or completeness, but can reveal an inconsistent premise, empty
domain, wrong quantifier order or missing observation before a long proof is attempted.

Watch for these disguises:

- A domain has been replaced by the implementation's own acceptance test without a proved
  equivalence to the requested domain.
- An existential witness is available only after assuming exactly the theorem being proved.
- An availability threshold can lie beyond every physically representable input.
- A theorem about a chosen producer is being presented as a theorem about arbitrary inputs.
- A successful executable example is being used as evidence for a universal proposition.
- A theorem is conditional on an obligation that remains open, although its wiring proof is
  complete.

Check machine boundaries mathematically: zero, negative values where the interface admits
them, one-past bounds, overflow/wraparound, empty data, duplicates, exhausted fuel and failed
allocation. Do not assume an arbitrary signed quantity is nonnegative merely because the
current producer usually returns positive values. Derive the restriction or state the real
domain. An example outside reachability can still refute an unrestricted interface theorem.

## Preserve observations and witnesses

Choose observations that distinguish the behaviors the claim is meant to preserve. An exit
code alone may erase the difference between a clean exit and a resource stop. A final value
may erase earlier host interactions or writes. Integer equality may erase floating-point
representation details. Preserve the required tags, trace order, bytes and state components.

When composing relations, use the intermediate witness supplied by the actual matching
relation. Separate existential facts about some middle value do not establish that the
diagram's chosen middle value has the required side property. Attach the side property to
the same relation/index/endpoint and carry it through composition.

Make allowed exceptional outcomes explicit. An early-stop refinement may permit a resource
failure before a source step; an exact endpoint theorem may forbid replacing a clean final
state with that failure. Check both positive examples of permitted behavior and negative
examples of the forbidden substitution. A common numeric encoding of two outcomes does not
identify their constructors.

For graph and collection specifications, distinguish sets, multisets, ordered lists and
first-match maps. Deduplicating predecessor vertices can preserve reachability while losing
edge multiplicity. A representation suitable for one property may be wrong for another.

## Check simulation direction

For semantics and compiler proofs, write the intended behavior inclusion before choosing a
simulation theorem. A source that permits both event orders can allow a compiler to choose
one. An all-source-step forward diagram may demand both orders from that target, stronger
than the intended target-to-source behavior inclusion. Use a justified strategy refinement
or another appropriate relation; do not silently change the source's undefined behavior or
event semantics to make the diagram fit.

Read the hypotheses of a theorem that converts forward simulation into backward simulation
or behavior inclusion. Receptiveness, determinacy, safety, reachability, final-state matching
and allowed early stops do real work. Establish each for the actual semantics and endpoints;
do not transfer them from a related library semantics by name alone.

A counterexample to determinacy of arbitrary raw states does not by itself refute determinacy
on reachable states or determinacy of observable behavior. Administrative silent reductions
can have several successors with the same eventual observation. If using a restricted or
quotiented relation, prove its connection to the original semantics and account for silent
divergence as well as finite paths. State the repaired domain explicitly.

## Keep assumptions attributable

Inspect `Print Assumptions` on the actual exported claim in a scratch query after checked
compilation. Compare the result with the development's intended foundations and approved
obligations. Inspect relevant declaration types and unsafe typing settings as needed.

Do not require an empty report by default. Classical logic, functional extensionality,
choice or proof irrelevance may be intentional foundations. Name them accurately and keep
new assumptions visible. Never replace a failed implementation or missing proof with a new
axiom, admission or disabled check while reporting the original claim as proved.

Treat inherited assumptions as assumptions, not evidence of their consistency. Inspect
suspicious native-service laws at zero, empty and boundary cases; contradictory laws can
make every proposition derivable. A small contradiction under explicit hypotheses can
refute that interface without asserting the entire dependency is inconsistent. Report the
exact law and domain; an assumption audit lists dependencies but is not a consistency proof.

Inspect the full theorem type after Section generalization. Inconsistent premises can be
explicit theorem arguments and therefore absent from `Print Assumptions`; a closed global
assumption report does not show those premises have a model.

Keep independent claims independently provable. Building a pair from one closed proof and
one assumed proof, then projecting the closed component, can retain the assumed component
in the dependency graph. This is a property of the resulting proof term, not a demonstration
that the projected proposition mathematically needs the extra assumption. A direct lemma
or independently constructed proof can preserve a narrower dependency boundary.

Distinguish a proof using only inherited axioms from one depending on an unfinished owned
result. Identify which direction of a checker or contract a dependency supplies. Bundling
soundness and completeness for convenience can obscure this distinction.

An audit needs a declared scope: exported claims, all theorem roots, executable roots, or a
specific release interface. A clean report over selected roots does not cover omitted ones.
If expensive dependency traversal is shared, retain attribution and negative controls for
missing, unresolved and unexpectedly dependent roots.

## Separate the logical and executable boundaries

Track four interfaces separately:

1. The logical definitions and proved propositions.
2. Executable functions linked to them by agreement/reflection theorems.
3. Extraction roots, erasure and target-language realizations.
4. Native tools, services, serializers and runtime behavior outside those proofs.

Proof material in `Prop` can disappear during extraction. Informative evidence in `Type`
can remain computational content. Native realizations can introduce
runtime dependencies that an ordinary theorem-assumption report does not characterize.
Review both graphs. A generated program running successfully does not establish the missing
logical agreement theorem, and a checked theorem does not verify arbitrary native overrides.

State conditional refinement premises as premises. A declaration that an external service
behaves correctly is not a proof of its implementation. An ABI match, successful linking,
parser example or native smoke run does not establish every semantic bridge around it.

Preserve distinctions between trusted preprocessing, verified parsing of tokens, semantic
validation, transformation correctness and serialized execution. Name the actual endpoint
of each claim. Keep a restricted client's profile at its owning boundary when a general
dependency should retain broader semantics.

## Report evidence precisely

Use descriptions that say what was checked:

| Evidence | Limit |
| --- | --- |
| Source inspection or unexecuted proof plan | No compilation or runtime result |
| Statement accepted with an open obligation | The proposition is written; its proof is open |
| Checked theorem | The kernel accepted that statement under reported assumptions |
| Concrete computed example | That instance has the checked observation |
| Runtime comparison | Those executions agree under the tested environment |
| Benchmark | That measured workload; state controls and uncertainty |

Different evidence can support one conclusion without becoming interchangeable. Distinguish
an owner's historical build report from an independent replay. An interrupted run with no
success status remains incomplete; a signal alone does not establish an out-of-memory cause.

## Handle a suspected false contract

Stop editing the implementation to accommodate the suspected defect. Minimize the example,
write the exact proposed contradiction, and separate an informal source argument from a
compiled or kernel-checked counterexample. Check implicit premises and imported aliases.

Present the failed property, intended use and smallest justified specification repair.
Follow the task's authorization for statement changes. If the proposed repair is outside it,
report the counterexample and obtain a decision before changing the fixed claim. Update
consumers and regression cases for both the new guarantee and the behavior the old statement
accidentally allowed. Do not make the claim disappear in a renamed alias.

The [Rocq 9.3 command manual][commands] documents assumption reporting; the
[extraction manual][extraction] describes its separate treatment of proofs and realizations.
Use the documentation matching the actual tool and library versions.

[commands]: https://rocq-prover.org/doc/V9.3.0/refman/proof-engine/vernacular-commands.html
[extraction]: https://rocq-prover.org/doc/V9.3.0/refman/addendum/extraction.html
