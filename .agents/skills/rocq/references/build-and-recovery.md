# Build, diagnose and recover

## Contents

- [Reproduce the real environment](#reproduce-the-real-environment)
- [Cap every Rocq process](#cap-every-rocq-process)
- [Use a strict diagnostic harness](#use-a-strict-diagnostic-harness)
- [Classify the failure before retrying](#classify-the-failure-before-retrying)
- [Recover artifacts through their owner](#recover-artifacts-through-their-owner)
- [Handle interruption and resource failure](#handle-interruption-and-resource-failure)
- [Choose an appropriate checking level](#choose-an-appropriate-checking-level)
- [Finish at the promised boundary](#finish-at-the-promised-boundary)
- [Versioned references](#versioned-references)

Use this reference when a proof fails outside its expected context, an incremental build
behaves inconsistently, or a command fails, hangs or appears successful without a result.

## Reproduce the real environment

Read the repository's build instructions before choosing a compiler command. Use its
supported wrapper, dependency manager and pinned shell when present. Do not bypass a
wrapper to avoid its locks, warning policy, assumption audit or resource limits.

Record the actual compiler and library versions. Modern Rocq installations can use
`rocq compile` and `rocq repl`; older developments may use `coqc` and `coqtop`. Query the
installed interface under the same resource cap and environment as the build instead of
assuming command spelling, flags, standard-library layout or plugin compatibility.

Check the logical load-path mapping as well as filesystem paths. A directory existing on
disk does not establish that `Require` resolves its intended logical library. Preserve the
project's distinction between `-Q` and recursive `-R` mappings and its logical prefixes.
Use the mappings produced by the actual build configuration; avoid inventing overlapping
prefixes or silently loading a second copy of a library.

Check the build tool's selected workspace root separately from the shell's working
directory. A nested scratch snapshot can be absorbed into an ancestor workspace. Use
the tool's supported root-selection mechanism through the project wrapper when needed;
record that replay setup change without attributing it to a failed proof.

For dependencies, check source revision, submodule state, package versions, plugins and
native bindings. An installed compiler with the right version can still load incompatible
compiled libraries or a different runtime adapter. Keep environment repairs distinct from
proof repairs so their evidence and scope remain clear.

## Cap every Rocq process

Apply an explicit hard memory cap before launching compilation, queries, extraction,
proof checking or a version/help probe. Cover child processes and aggregate concurrent
use. A compiler-specific heap target or garbage-collector tuning variable is not a hard
process-tree memory limit.

Use a mechanism supported by the host and project, such as a cgroup, container or job
limit. Verify the effective limit from inside the envelope with a lightweight shell probe;
check swap policy and inheritance rather than assuming the wrapper's name guarantees them.
A virtual-address-space limit and a resident-memory cgroup limit constrain different things;
record the mechanism and units.

If the requested hard cap cannot be enforced, do not launch Rocq. Use an environment with
working enforcement or report that execution cannot proceed. An advisory limit or lower job
count does not satisfy a hard-cap requirement.

Keep retries capped. If the cap is reached, diagnose the expensive phase and reduce the
target, concurrency or computation first. Raise the cap only within the available resource
budget and task constraints. Set a time budget as a separate control: a timeout does not
limit peak memory, and a memory cap does not stop an infinite or very slow computation.

Put scratch source, outputs, redirected logs, extracted files and tactic caches in an
approved scratch directory. Check the command's working directory and implicit output
locations before running it. Preserve pre-existing artifacts and evidence; do not clean
unrelated files merely because their names look temporary.

## Use a strict diagnostic harness

Prefer ordinary batch compilation for a reproducible proof check. An interactive REPL
can recover after an error and later exit zero, so process success alone can misclassify
a failed command. In Rocq 9.3, `Set Rocqtop Exit On Error.` makes a query session stop on
an error; check the installed version's behavior before relying on an equivalent option.

Preserve both exit status and relevant output. Keep the first useful error, target,
command, working directory, environment, memory cap and interruption status. When using a
pipeline, preserve the compiler's status rather than accepting only the final filter's
status. A log excerpt without its process outcome is incomplete evidence.

Use `Check`, `About`, `Print`, `Locate`, `Search` or explicit printing for a focused
question in scratch. A query that accepts a term checks that term's type; it does not prove
an admitted theorem or establish an executable's behavior. Keep assumption reports and
runtime observations separate from query success.

For an expected failure, inspect its cause. `Fail` accepts many kinds of command failure;
an ill-typed statement, missing import or bad path can satisfy a negative test intended to
exercise a deeper proof boundary. Pair it with a control that reaches that boundary.

## Classify the failure before retrying

| Failure | First useful check |
| --- | --- |
| Token or grammar error | Small syntax fragment, active notation, preceding delimiter |
| Unknown or ambiguous name | Actual imports, qualification, scopes and logical mapping |
| Type or implicit mismatch | Elaborated arguments, selected instance and module interface |
| Failed rewrite | Exact goal, equation orientation, instantiated lemma and current IH |
| Guard or positivity rejection | Actual recursive subterm or inductive occurrence |
| Conversion or slow closure | Opaque dependency, dependent index or expanded term |
| Inconsistent assumptions/artifact | Matching compiled dependencies, flags and load paths |
| Extraction or native failure | Actual roots, mappings, generated types and linked bindings |
| Missing output or stopped worker | Exit/signal, build report and resource-controller record |

Read the first useful diagnostic and the build system's report before another attempt.
Revise the working diagnosis and test it with a focused target or a relevant change
in environment, build state or command. Repeating the same failed command without changing
relevant state usually adds no evidence.

Reduce the problem without removing the failure mechanism. Keep the relevant imports,
module sealing, implicit arguments, recursion certificate, dependent indices or extraction
mapping. A minimized example that bypasses the blocked dependency cannot explain the
original failure. Compile the proposed theorem statement before attempting a long proof.

Check important consumers after a local fix. A file compiling establishes neither that its
public API stayed compatible nor that its intended consumer actually uses the new lemma.

## Recover artifacts through their owner

Let the build system manage its outputs. Do not copy a `.vo`, edit generated dependencies,
rewrite a build-directory source or delete selected artifacts behind its back. Such changes
can invalidate dependency tracking or make later observations depend on stale files.

For inconsistent compiled assumptions or missing libraries, first check toolchain, source
revision, logical paths and duplicate installations. Then rebuild the affected producer
and consumers using the project's supported invalidation or cleanup command. Do not change
a theorem to accommodate an artifact from a different interface.

Choose the smallest valid recovery boundary. Rebuild the dependency cone when its inputs
changed; reserve a full clean for evidence that narrower recovery is insufficient or for
the required release procedure. Keep logs before cleanup, since cleaning can remove the
diagnostic context needed to explain the failure.

Preserve build locks and concurrent work. A wait for a lock is an infrastructure wait,
not proof-search time or a failed theorem. Coordinate competing builds, and avoid cleaning
a shared output directory while another process owns it. If a wrapper itself fails before
Rocq starts, report that as a wrapper/environment failure.

For generated or vendored code, repair the generator, configuration or maintained patch
at its actual source. Verify regeneration and the generated consumer together. Preserve
upstream conventions and keep the maintained patch small enough to explain its necessity.

## Handle interruption and resource failure

Use the repository's supported cancellation path. Preserve its report, confirm child
processes stopped, and release locks through their normal owner. Do not use a stronger
signal merely to shorten a legitimate shared-build wait.

Distinguish a confirmed memory-limit event from a timeout, manual interruption, signal,
compiler error or unexplained missing artifact. An exit code associated with a killed
process is not sufficient to identify the cause without supporting diagnostics or resource
records. Report uncertainty when those records are missing.

After interruption, follow the build system's recovery instructions before retrying.
Inspect the partial run's diagnostics; do not count an old `.vo`, an earlier success line,
or an unfinished background process as completion of the current run.

Prefer a fresh report path for each attempt in a diagnostic harness. If reusing a path,
archive the previous evidence, then invalidate the current success report before starting.
Record success only after the required checks finish.

Use [performance diagnosis](performance.md) to investigate expensive checking. Keep
wall-clock limits, abstract evaluator fuel and mathematical termination measures distinct.
A larger fuel or memory budget does not prove the intended theorem.

## Choose an appropriate checking level

Distinguish interactive progress, statement checking, ordinary checked compilation,
independent artifact checking and executable tests. Name the mode and any skipped work.

Development modes such as `.vos` can omit opaque proof checking. Follow the installed
version's checking workflow and the repository's release gate before claiming a completed
proof. In Rocq 9.3, `-vok` checks the current source's proofs while loading dependencies as
`.vos`, with a `.vo` fallback for empty interface stubs; it does not check every dependency's
proof. Do not use existence of a compiled-looking artifact as a
substitute for the required check. Diagnostic or scheduling shortcuts are useful only
when their weaker evidence is understood and recorded.

Review the actual assumptions of promised claims, including imported aliases and
admitted dependencies. A theorem closed with `Qed` can still depend on an admission or
accepted axiom. Conversely, an intended foundational axiom is not a newly introduced
obligation. See [specifications and trust](specifications.md).

If independent checking is required, use the version-compatible checker and the intended
dependency closure under the same cap. It checks logical artifacts under its trust model;
it does not validate a native runtime binding or prove extraction correctness by itself.
Rocq 9.3's `rocqchk` recursively checks compiled `.vo` libraries' logical information, with
options that affect the checked closure. It does not validate notation, implicit-argument
associations or other nonlogical metadata; compile real importing clients to check those.

## Finish at the promised boundary

Run the smallest affected target during iteration, then its important clients and the
checks required for the delivered change. Use the project's publish gate when publishing
is authorized; do not equate a leaf build with completion of that gate.

Check formatting and hygiene through the configured tools. Fix an owned warning's cause
or follow an explicitly accepted policy; do not add a broad warning suppression to make
a build appear clean. Warning categories and defaults are version-sensitive.

Check which tests and audited roots actually ran. An empty test alias or an audit over an
empty root list can exit successfully without exercising the promised property. Preserve
the relevant inventory when changing test registration, extraction roots or build aliases.

Report what changed, the exact checks and outcomes, remaining assumptions or obligations,
and any unavailable checks. Separate unrelated baseline failures from new regressions.
For benchmarks, record equivalent targets and controls; for runtime tests, report the
inputs and observations actually compared. Do not turn missing evidence into a success.

## Versioned references

- [Using Rocq, Rocq 9.3][tools]
- [Vernacular commands, Rocq 9.3][commands]
- [Program extraction, Rocq 9.3][extraction]

[tools]: <https://rocq-prover.org/doc/V9.3.0/refman/practical-tools/coq-commands.html>
[commands]: <https://rocq-prover.org/doc/V9.3.0/refman/proof-engine/vernacular-commands.html>
[extraction]: <https://rocq-prover.org/doc/V9.3.0/refman/addendum/extraction.html>
