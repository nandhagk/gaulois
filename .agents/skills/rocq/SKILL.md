---
name: rocq
description: Use when writing, editing, reviewing or debugging Rocq and Coq proof developments (*.v) - specifications, proofs, computation, extraction, modules, notation, performance and build recovery. Not for Verilog or other non-Rocq .v files.
metadata:
  file-patterns: "*.v"
---

# Rocq

Write statements that express the intended claim and proofs that expose the reasoning.
Connect executable definitions to those claims when the development includes computation.

## Scope and precedence

- Apply this skill to authored Rocq/Coq theories, their examples, and proof-related build,
  extraction and verification changes. Identify the language before applying it to a `.v` file.
- Generated and vendored files keep their conventions; repair the generator or owning patch.
- Apply the corresponding language or tool skill when changing build files, native plugins,
  extraction adapters or scripts, when that skill is available.
- The user's explicit instructions come first, then repository instructions and its pinned
  formatter, linter, build and trust configuration, then this skill. Follow an override and
  identify it in the completion report.

## Workflow

1. Read repository instructions, the relevant statement and its definitions, nearby proof
   style, consumers, pinned Rocq/Coq and library versions, and applicable references below.
2. Establish the failing target or expected observation. Preserve the relevant diagnostic,
   command and available proof state. Use the repository's supported build command.
3. Make the smallest coherent change. Compile the smallest affected target, then its
   important consumers. Check the relevant statements and assumptions, and executable
   observations when the development exposes them.
4. Finish with the required repository checks and a completion report. State the evidence
   actually obtained and any unresolved work.

## Rules

### Types and data

- Read through aliases and imported predicates before proving a statement. Check its
  quantifiers, domain, reachability conditions, failure cases and observations for vacuity.
- Preserve the requested contract and domain through implementation work. Document authorized
  specification repairs; do not silently add premises or weaken the conclusion.
- Connect specifications and executable representations by precise agreement/reflection lemmas.
  Preserve the ordering, duplicate-key and malformed-input behavior the contract specifies.
- State the invariants needed by prepared values. Prove maintained caches' initialization and
  updates, or validate/rebuild untrusted entries before use; preserve existing caller duties.
- Choose recursion and induction from the changing structure and required motive. Inspect
  generated principles for nested/indexed types instead of assuming they supply the needed IH.
- Distinguish propositional equality, definitional equality, pointwise agreement and equality
  of proof-carrying records. Use only the extensionality/UIP principles the development accepts.
- Check sorts, elimination restrictions and universe constraints when types appear to match.
  Keep computational witnesses in an appropriate data sort; choose polymorphism deliberately.

### Structure and naming

- Give definitions and lemmas one coherent job. Factor repeated reasoning into named facts
  with the weakest useful dependencies; keep independently usable claims independently proved.
  Split a proof past about 40 lines into named lemmas at its reasoning boundaries. Name a
  lemma for the fact it states, with one suffix per kind of fact (`_sound`, `_complete`,
  `_correct`, `_preserved`, `_agrees`).
- Name hypotheses that later steps use by their meaning (`Hstep`), never by generated names
  such as `H0`. Use explicit cases, bullets (`-`, `+`, `*`) and focused goals so later tactics
  do not depend on accidental goal counts. Put `Proof.` and `Qed.` on their own lines.
- Reuse the project's tactic dialect and library APIs before writing a tactic. Declare any
  other `Ltac` `Local`, with a comment saying what it does; give shared automation an explicit
  interface and small representative client checks. Never use the `timeout` tactic: whether a
  proof checks must not depend on machine speed.
- Qualify a name only to disambiguate it, with the shortest prefix that resolves it
  (`List.map`); never write a full logical path or a file's own path in code. Check imports,
  notations, hints, instances and public paths when moving code; unchanged proof text can
  resolve to different declarations.
- Write one import header at the top of the file: every `Require` (with `From`), then the
  `Import`s, grouped by origin (standard library, other libraries, the project's own), one
  line per directory. Write `Require Import` for a library that is also imported, require or
  import nothing twice, import nothing inside a `Module` or `Section`, import a module defined
  in the file right after its `End`, and qualify a notation module that may collide
  (`List.ListNotations`).
- Parenthesize a refined type in an outer signature constraint, as in
  `Module Type S <: (T with Definition t := nat).`, and keep binder and signature groups
  balanced.
- Pilot a nontrivial shared module body with actual members and downstream proofs before migrating
  many files. Preserve required type identities, declaration shapes and previous instances.
- Open every file, before its imports, with a `(** * Title` comment: a plain paragraph on what
  the file does, one concrete "For example, ..." and a `Builds on:` line. Give every `Theorem`
  and every named statement that fixes a contract a one-sentence `(** ... *)` comment saying
  what it means.
- Put one constructor or record field on each line. Start the constructors of `Inductive`,
  `CoInductive`, `Variant` and mutual `with` declarations with `|`, two spaces beyond the
  declaration, and continue lines at least four spaces beyond it. Start every `match` branch,
  `Ltac` ones included, on its own line aligned with its `match`, with the body indented two
  spaces. Leave record fields unprefixed; on a projection clash, put the record in its own
  module (`Block.base b`). A module is a namespace, never a wrapper that merges files.
- Keep lines at most 100 columns, indented by 2 spaces, with no tabs or trailing whitespace
  and a final newline. Separate top-level items by one blank line; a comment directly above an
  item belongs to it, and a section comment `(** * Title *)` opens each group. Keep a file at
  most 1,500 lines, aiming for 800, and split a larger one by topic.
- Follow repository layout and formatting. Explain a non-obvious invariant where it is
  defined or used; avoid comments that merely narrate each tactic.

### Values and text

- Make numeric carriers, scopes, coercions and implicit arguments explicit where inference
  is ambiguous. Inspect the elaborated term when the accepted expression is surprising.
- Test custom syntax against the intended constructor tree. Include precedence, associativity,
  reserved-token and importing-client cases; pretty output alone does not establish an AST.
- Preserve exact observations where they matter: outcome constructors, traces, identifiers,
  order, signed zero, NaN representation and boundary values. Numeric equality may be weaker.
- Prefer small symbolic witnesses and reusable equations to repeated normalization of large
  concrete memories, syntax trees or dependent records.

### Errors and resources

- Put every Rocq process under an explicit hard memory cap, including queries, compilation,
  extraction and independent checking. Cover child processes and aggregate parallel use;
  verify the actual envelope and keep retries capped.
- Read the first useful diagnostic and build report before retrying. Classify parsing,
  elaboration, tactic, conversion/kernel, artifact/environment and resource failures separately.
- Preserve equations needed after case analysis and keep changing accumulators, environments
  or endpoints sufficiently generalized. Inspect the new IH/context before another rewrite.
- Reduce only what the next step needs. Before broad computation, try a specification lemma,
  a named intermediate equation, an explicit witness or a smaller dependent return clause.
- Treat opacity as an API choice. Prefer `Qed` for proof-only lemmas; keep computational
  definitions transparent when their consumers need reduction. Diagnose the exact blocked term.
- Profile an actual bottleneck before changing global runtime settings or abstraction strategy.
  Compare equivalent targets and checking levels; fewer lines are not a speed measurement.
- Stop resource-heavy experiments through the supported interruption path. Keep the failure
  evidence and use build-system-aware recovery; do not edit managed build outputs.

### Interfaces (CLI, I/O, processes)

- Use the project's declared environment and logical load paths; record actual versions when
  no pin exists. Check library bindings and generated interfaces as well as tool versions.
- Keep source specifications, executable algorithms, extraction realizations and deployed
  behavior distinct. Review the actual extraction roots and any native replacements.
- Couple side properties to the witnesses, matching relation and endpoints used by a dependent
  composition. Build the required correspondence when witnesses are mapped or transported.
- Preserve public statements, argument order, implicits, module identity and computational
  equations through refactors; make intentional API migrations explicit and check real consumers.
- Keep query commands (`Print`, `Check`, `Compute`, `Eval`, `About`, `Locate`, `Search`) out
  of maintained source: run them in scratch and contain their generated outputs and caches.
  Follow project conventions for normal build artifacts.

### Tooling and verification

- Complete ordinary checked compilation before claiming a proof. Treat `.vos` and other
  development shortcuts according to their checking level; use the required release gate.
- Inspect assumptions of actual claims and extraction dependencies of executable roots. State
  intended foundations explicitly; do not add axioms, admissions or unsafe checks to hide failure.
- Validate semantic outcomes as well as process status. A recovering interactive REPL can
  print an error and still exit zero; prefer a strict batch/query harness for automation.
- Use positive, negative and boundary cases that discriminate the intended behavior. A finite
  fixture, a compiled statement and a universal proved theorem provide different evidence.
- Run the relevant formatting, hygiene, build, trust and runtime checks. Report failures and
  unavailable checks accurately; do not attribute an unrelated baseline failure to the change.
- For performance claims, record source/tool versions, target, recompiled dependencies, cap,
  jobs, wall/CPU time and the kind of memory measurement. Preserve comparable controls.

## References

| Read before | File |
| --- | --- |
| Specifications or trust boundaries | [Statements](references/specifications.md) |
| Proofs, induction or dependent rewriting | [Proofs](references/proofs.md) |
| Reduction, recursion, transparency or extraction | [Computation](references/computation.md) |
| Indexed data, checkers, caches or algorithms | [Algorithms](references/verified-algorithms.md) |
| Modules, imports or library interfaces | [Modules](references/modules-and-libraries.md) |
| Notation, scopes, coercions or printers | [Syntax](references/notation.md) |
| Build time, memory use or expensive checking | [Performance](references/performance.md) |
| Tools, artifacts, load paths or failed builds | [Recovery](references/build-and-recovery.md) |
| File headers, layout, names, comments or automation in maintained theories | [Style](references/style.md) |

## Completion report

End with a rocq report: one line per rule group, marked changed (with paths), reviewed
unchanged (with reason) or not applicable. Combine groups sharing an outcome. List checks
and results, remaining assumptions/obligations, checks that could not run, and evidence limits.
