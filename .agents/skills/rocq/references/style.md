# Rocq proof and API style

## Contents

- [Name claims and interfaces](#name-claims-and-interfaces)
- [Document contracts and invariants](#document-contracts-and-invariants)
- [Open each file with a header](#open-each-file-with-a-header)
- [Lay out files and declarations](#lay-out-files-and-declarations)
- [Structure proof scripts around reasoning](#structure-proof-scripts-around-reasoning)
- [Keep automation local and legible](#keep-automation-local-and-legible)
- [Factor at reasoning boundaries](#factor-at-reasoning-boundaries)
- [Avoid cosmetic foundational churn](#avoid-cosmetic-foundational-churn)
- [Queries and experiments](#keep-queries-and-experiments-out-of-maintained-source)
- [Represent unfinished work and trust honestly](#represent-unfinished-work-and-trust-honestly)
- [Make examples discriminate behavior](#make-examples-discriminate-behavior)
- [Review the public proof artifact](#review-the-public-proof-artifact)

## Name claims and interfaces

Choose names that state the mathematical fact or public operation, not the tactic
used to establish it. Distinguish a specification, a boolean checker, its soundness
lemma, completeness lemma, and an optimized implementation. A useful name lets a
client understand the role without reading the proof body.

Use one suffix for one kind of fact across a development, so that a name predicts
its statement:

| Suffix | Statement |
| --- | --- |
| `_sound` | acceptance by a checker implies the property |
| `_complete` | the property implies acceptance |
| `_correct` | an implementation meets its fixed contract |
| `_preserved` | a step or transformation keeps a property |
| `_agrees` | two executable forms give the same result |
| `_holds` | the proof of a statement that is defined by name |

Name a condition that recurs, and use the name everywhere. Bundle state, and laws that
belong together, in a record with named fields rather than a tuple or a positional
conjunction.

Use one consistent vocabulary for a type's owners and their operations. Give
wrappers explicit input and output types when inference obscures which language,
module, or representation they use. Qualify names only enough to distinguish
them from competing declarations, with the shortest prefix that works (`List.map`);
never write a full logical path in an expression, or a file's own path inside that
file. Keep public interfaces small and avoid exporting helper names that clients
can derive from stronger, stable facts.

Before renaming, relocating, or changing implicit arguments, search actual
consumers. Source-compatible aliases can still alter type identity, notation,
instance selection, or reduction. Check representative clients after the API
change rather than judging compatibility from the declaration alone.

## Document contracts and invariants

Give every `Theorem` and every named statement that fixes a contract a one-sentence
`(** ... *)` comment saying what it means. The sentence adds the reading that the name
and type leave out; it does not restate the formula. Use `Theorem` for fixed contracts
and headline results and `Lemma` for helpers. Explain a non-obvious invariant at the
definition or proof boundary where a future maintainer needs it. Avoid comments that
narrate each tactic or repeat the proposition in prose.

Keep fixed contracts independent of implementation details. Write down the
input domain, allowed outcomes, observations, and exceptional cases before
choosing a proof decomposition. If a counterexample suggests a contract defect,
present the minimal counterexample and intended use; change the statement only
with the authority required by the project.

Attach side conditions to the same relation, index, witness, or endpoint that
uses them. An existential property about some intermediate value does not prove
the property for a different value selected by a simulation or composition.
Name helper predicates when they make that relationship explicit.

## Open each file with a header

Start every file, before its imports, with a `(** * Title` comment. Its first paragraph
says in plain words what the file does, a concrete "For example, ..." shows it on a
small case, and a final `Builds on:` line names the theories it depends on. The reader
learns the meaning before the dependencies:

```rocq
(** * Sorted insertion

    This file defines insertion into a sorted list and proves that the result is sorted.

    For example, inserting 3 into [1; 2; 5] gives [1; 2; 3; 5].
    Builds on: Order *)

From Stdlib.Lists Require Import List.
```

## Lay out files and declarations

Follow one mechanical layout, so that a diff shows only changes of meaning:

- Keep lines at most 100 columns, indent by 2 spaces, leave no tabs and no trailing
  whitespace, and end the file with a newline.
- Separate top-level items by one blank line. A comment directly above an item belongs
  to it, and a section comment `(** * Title *)` opens each group of related items.
- Put one constructor or record field on each line. Start the constructors of
  `Inductive`, `CoInductive`, `Variant` and mutual `with` declarations with `|`,
  indented two spaces beyond the declaration, and indent continuation lines at least
  four spaces beyond it.
- Start every `match` branch, in `Ltac` too, on its own line, aligned with its `match`,
  with the body indented two spaces.
- Leave record fields unprefixed. When two records clash on a projection name, put each
  record in its own module and write `Block.base b`. A `Module` is a namespace for
  names, never a wrapper that merges several files into one.
- Keep a file at most 1,500 lines, aiming for 800, and split a larger one by topic.

```rocq
(** * Shapes *)

Inductive shape : Type :=
  | Circle (radius : nat)
  | Rectangle (width height : nat).

Definition span (s : shape) : nat :=
  match s with
  | Circle radius =>
    radius + radius
  | Rectangle width _ => width
  end.
```

## Structure proof scripts around reasoning

Name hypotheses that later steps use, such as `Hstep`, `Hlookup`, or `Hbound`.
Do not depend on generated names such as `H0`, and do not assume that inversion,
destruction, or a library tactic will keep the same names after a nearby change.

Put `Proof.` and its closing `Qed.` (or `Defined.`) on their own lines, and use bullets
(`-`, then `+` and `*` for deeper levels) to mark distinct constructors, cases, and
subgoals. Use an explicit
closing step (`exact`, `assumption`, `reflexivity`, or a named lemma) when it
shows why the goal follows. Tactics such as `auto` or `eauto` are appropriate
when they discharge a bounded, well-understood residue; do not leave a
semantically important case to accidental goal-count or hint-database changes.

Keep equations through case analysis when a later theorem needs the original
match result. Use equation-bearing `destruct` for lookup and branch decisions.
After simplification, inspect whether the expression remains before rewriting it
again. Generalize changing state before induction, then verify that the resulting
induction hypothesis has the needed shape.

Prefer a visible proof outline for semantic arguments: identify the constructor,
apply the relevant inversion or simulation fact, establish the state relation,
and close the local equations. Avoid broad `repeat constructor` over nested
relations when it hides the meaningful branch or expands an unstable search.

## Keep automation local and legible

Reuse the development's established semantic inversions and tactic vocabulary
when they match the goal. Similar tactics may differ in clearing, substitution,
or generated names; inspect those effects before replacing one with another.

Declare a tactic that serves one-off repetition as `Local Ltac`. Share automation only
when multiple clients benefit from a stable interface. Comment every custom tactic with
the goal shape it handles and the work it performs; keep its behavior narrower than a
general-purpose search procedure. Do not wrap a tactic in `timeout`: success would then
depend on machine speed and load. Bound a search with a more specific tactic or an
explicit depth instead.

Prefer explicit case splits when they explain branch priority or preserve a
useful equation. Use reflection and arithmetic automation for the mathematical
residue they are designed to solve, after making conversions and range facts
explicit. Do not use `lia`, `auto`, or simplification to obscure which invariant
rules out the important case.

## Factor at reasoning boundaries

Introduce helper lemmas where they capture a reusable fact, isolate a proof
boundary, or make the next argument substantially clearer, and split a proof that
runs past about 40 lines into named lemmas at those boundaries. A helper may be
valuable even when the enclosing proof is short; conversely, cutting a proof at an
arbitrary line to meet the length guide fragments the reasoning.

Factor repeated reasoning around stable concepts such as lookup agreement,
endpoint bounds, constructor inversion, or a field-preservation equation. Keep
the helper's assumptions no stronger than the fact it proves. Avoid duplicate
facts with different names or a helper that merely wraps one tactic without
clarifying its purpose.

When a large dependent record contains both control and metadata, prove the
small projection or observational equation needed by the client. Rebuild the
whole record only when the result actually requires that equality. When a
control-flow match repeats a large continuation, factor a small discriminant
and prove it preserves branch order, errors, and payloads.

## Avoid cosmetic foundational churn

Do not change a foundational type, projection mode, transparency setting,
notation scope, global hint database, or typeclass instance solely to make one
proof shorter. Such changes affect conversion or inference throughout downstream
clients. First try a local view, named equation, small transport lemma, explicit
carrier, or restricted unfolding.

Make a broad change when it improves the actual shared interface or resolves a
measured systemic problem. Inspect the relevant consumers and compile a small
representative set before migrating a large family. Preserve public weak
principles or established conventions when clients depend on them; add a new
stronger interface alongside them if needed.

Keep `Qed` and `Defined` choices tied to use. Close proof-only results opaquely
unless computation intentionally consumes their proof terms. Keep executable
definitions transparent when clients require their computation, and expose
equations for abstract implementations through the public interface. Do not
change opacity globally to fix one blocked reduction.

## Keep queries and experiments out of maintained source

Leave no query command in maintained source. `Print` (`Print Assumptions` included),
`Check`, `Compute`, `Eval`, `About`, `Locate`, and `Search` belong in scratch files,
where they inspect declarations or evaluate examples. A repository that keeps query
tests on purpose says so in its instructions; follow them.
Keep the exact target, tool version, environment, output, and cap with the
experiment when those details affect diagnosis.

Use a computed `Definition` or named `Example` when the repository wants a
checked regression artifact. Keep that artifact declarative and reproducible;
do not leave an interactive query command as a substitute for a checked claim.
Let the repository's build system manage normal outputs and scratch locations.

## Represent unfinished work and trust honestly

Mark unfinished proofs using the project's permitted mechanism and retain the intended
statement. Keep admissions visibly distinct from established results, including in claims
that depend on them. Do not replace a failed proof with an axiom,
admission, unchecked cast, disabled guard, positivity or universe check, or weakened
statement while reporting the original theorem as proved.

Treat trust boundaries as project-specific. A development may intentionally
inherit classical axioms, proof irrelevance, functional extensionality, or native
realizations. Inspect the actual exported claim and executable roots, then
report each dependency accurately; do not require a globally empty assumption
set unless the project contract says so.

Distinguish an open statement, a compiled definition, a kernel-checked theorem,
a computed example, an extracted program, and a runtime observation. A green
build at one level does not establish the guarantees of the next. Name what was
checked, under which assumptions and configuration, and which part remains
conditional or trusted.

## Make examples discriminate behavior

Use a positive case for the intended behavior and a negative case for the nearby
forbidden behavior. Add boundary cases when they distinguish empty from
nonempty input, an exact endpoint from an overflow, a valid from malformed
shape, or a clean exit from an allowed early stop.

Keep examples small enough to understand. Prefer symbolic hypotheses or
arbitrary inputs when they preserve a stronger property without normalizing an
unrelated large concrete structure. Preserve exact traces, identifiers, result
ordering, error constructors, NaN or signed-zero representation when those are
part of the contract; a looser equality may miss a behavior change.

Do not infer a universal law from one fixture. A fixture is useful when it
distinguishes competing behaviors, but it does not replace a theorem over the
stated domain. Keep the test's role separate from a proof that establishes the
same property for all inputs.

Check that later normalization or projection cannot erase the defect before the observation.
For example, checking a list after sorting cannot distinguish earlier permutations.
Observe the order before sorting when that intermediate order is part of the contract.
Keep any intermediate-state equation tied to the actual fixture input.

## Review the public proof artifact

Before calling a result complete, inspect the final statement, theorem name,
imports, assumptions, and actual proof term's relevant dependencies. Check that
an exported theorem does not accidentally retain an unrelated open obligation
through a bundled proof or helper. Confirm the executable definition still
matches the proved specification at the boundary promised by the project.

When changing a declaration or proof interface, search downstream uses and
review the resolved constants after imports and notation are applied. Run the
repository's required formatter, checker, build, audit, extraction, or runtime
gates that apply. Report unavailable checks as unavailable rather than
substituting a weaker evidence class.
