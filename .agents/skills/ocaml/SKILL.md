---
name: ocaml
description: Use when writing, editing, reviewing or refactoring hand-written OCaml (.ml, .mli, dune files) built on Core and ppx_jane - owning modules and interfaces, domain types, derivers, Or_error and resource handling, Command_unix tools, expect tests, formatting and warnings. Not for generated OCaml.
metadata:
  file-patterns: "*.ml *.mli *.mll *.mly dune dune-project"
---

# OCaml

Give every concept a module that owns its type, make invalid states unrepresentable, derive
what Core and ppx_jane can derive, and return errors as values.

## Scope and precedence

- These rules apply to all hand-written OCaml, including native plugins and support code
  inside another language's tooling; a file's directory does not exempt it.
- Never edit generated OCaml by hand: change its source or the hand-written wrapper and
  regenerate. Build generated modules in their own dune stanza with their own warning policy.
- The user's explicit instructions come first, then the repository's own instructions
  (AGENTS.md, CLAUDE.md, dune and ocamlformat configuration); then this skill. When one of
  them overrides a rule here, follow it and say so in the completion report.

## Workflow

1. Before editing, read the repository's instructions, the dune files and `.mli` interfaces
   involved, and the references for the rule groups the change touches. Use the pinned
   environment: run builds in the repository's Nix shell.
2. Apply the rules to every line you write or change, tests included.
3. Before finishing, build with the warning policy, run the expect tests, format with the
   pinned ocamlformat, and write the completion report.

## Rules

### Types and data

- Give each concept an owning module whose main type is `t`, used as `Status.t`; a file is
  already a module, so its main type is `type t`. Declare no bare named types such as
  `type status = ...` unless an external interface forces one, and then say why in a comment.
- Use ordinary variants, not polymorphic variants, unless an external API requires them, and
  records, not tuples, for anything with more than one meaningful part.
- Use `Nonempty_list.t` for sequences that must contain an element, in arguments, fields and
  return types. Validate ordinary lists once at external boundaries and preserve the invariant
  through internal APIs; keep lists where empty is valid or a foreign interface requires them.
- Represent modes, states and outcomes as variants with named constructors, never as boolean
  data. A classification that callers branch on is an outcome too: return a variant naming
  its cases (`Success | Failure`), not an `is_success` boolean. Keep booleans for plain tests
  passed to a filter or combined with `&&`. Convert a foreign boolean flag into a variant at
  the boundary; a protocol between owned components is not foreign.
- Use ordinary variants for closed semantic choices such as owners, diagnostic reasons,
  kinds and modes, never strings used as selectors or context classifiers. Carry open source
  names, paths and foreign text as payloads, reusing existing semantic types; keep real text
  as strings.
- Model the general concept, not the instances you know: no constructor or field serves only
  one known instance. Describe what instances differ in as data, one record per instance; when
  adding an instance should need no code change, load those records from an S-expression file
  with `[@@deriving of_sexp]`, validated where it is read.
- Give a value with meaning beyond its representation its own module with an abstract `t`
  and a validating constructor (`Size.t`, not a raw `int`). Carry paths, identities,
  digests, indices, addresses and extents in their semantic types, reusing existing types
  before adding wrappers.
- A constructor that cannot fail returns `t`, not `t Or_error.t`. Expose a record whose
  fields are already validated; keep `t` abstract only for a cross-field invariant, with
  getters from `[@@deriving fields ~getters]`.
- Use `int` for sizes, offsets and counts, never `int64`; convert at a foreign boundary.
- Give each setting's default as a typed constant in the module that owns the setting, and
  derive help text from it.

### Structure and naming

- Write an `.mli` for every module except `main.ml`, exposing only what callers need. Give
  an item a `(** ... *)` comment when its name and type do not say what it does, or when
  callers must know a precondition, invariant, unit, effect or raising convention; never
  restate the signature in words.
- Name files and directories in lowercase snake_case (`engine_limits.ml`); a file
  implementing a module whose name a dependency fixes keeps the dependency's spelling.
- Keep one concept per module, at most about 300 lines, and split a module that mixes
  stages. Never name a submodule after a Core module it would shadow; modules of a wrapped
  library need no project prefix.
- Keep conversions in the type's module (`Keys.Line.of_key`) and give formatting its own
  operation.
- Annotate record construction and patterns with their type, `({ image; steps } : Options.t)`,
  never `Options.{ ... }` or `x.Module.field`; destructure a foreign record once, where it
  enters. Match a list instead of calling `List.hd_exn`.
- Never qualify just one constructor to anchor later unqualified siblings. Annotate the
  parameter, scrutinee or function signature with its existing type and use unqualified
  siblings consistently; if qualification is needed, qualify every sibling of that family.
  Treat nested and tuple families independently; add no broad opens or wrapper types to
  avoid annotations.
- Keep functions short, about 30 lines: lift helpers to the top level, separate a traversal
  from its per-node checks, and extract real stages rather than forwarding helpers.
- Label arguments whose roles the types do not make plain, in internal helpers too: leave a
  one-argument function unlabelled, label two arguments when they could be swapped, and with
  three or more label every argument except the value the function is about. Take a callback
  as `~f`, after the other arguments, as Core does (`with_temp_dir ~prefix ~f`).
- Prefer pipelines and `@@` to nested application, never eta-expand, and turn a check
  repeated twice into a named helper.
- Write constant callbacks explicitly as `fun () -> value` or `fun (_ : t) -> value`;
  never use `Fn.const`.
- Thread state functionally by returning an updated `t`, and comment each mutation that must
  stay. Use `Array.make_matrix` for two-dimensional data.

### Values and text

- Define every fixed spelling or number once, tests included, as a named constant in its
  owning module, or as a variant when the values form a closed set; derive related values.
- Use Core and ppx_jane, and derive instead of hand-writing:
  `[@@deriving sexp_of, compare, equal, enumerate, string]`, and `ppx_yojson_conv`
  instead of hand-built JSON. Derive only the directions you use.
- Derive string conversions with `[@@deriving string ~capitalize:"kebab-case"]`, or the rule
  that matches the external spelling; never hand-write `to_string` or `of_string` matches.
- After `open Core`, compare `int`s with `=`, `<` and `compare`, other types with their
  module's `equal` and `compare`, and use opened modules without a `Core.` prefix.
- Use typed PPX comparisons for composite types, such as `[%equal: string option]` and
  `[%compare: string list]`, rather than chaining container comparators. Preserve a foreign
  or context-dependent comparator when it defines different identity or ordering semantics.
- Find an item by name through a `Map.t` keyed by the name's type, built once where the
  collection is made; never through chains of string comparisons or matches on string
  literals.
- Build typed S-expressions with `[%sexp (value : M.t)]`.
- Never build or match S-expressions by hand: no `Sexp.Atom` or `Sexp.List` constructor or
  pattern in any spelling (qualified, through a local or global open of `Sexp`, or resolved
  by a type annotation), in any OCaml source, tests and tools included. Model the data as a
  type, derive its converters with `[@@deriving sexp]` (just `of_sexp` or `sexp_of` when one
  direction is used) and describe the shape with attributes such as `[@sexp.option]` and
  `[@@sexp.allow_extra_fields]`. A hand-built tree repeats the type's shape where the
  compiler cannot check it, and loses the field-level errors of the derived reader.
- Build text with `[%string]`; never `^`, `Printf`, `Format` or printf-style functions.
  Write to the standard streams with Stdio's helpers: `print_endline` and `print_string` for
  standard output, `prerr_endline` for standard error, and `print_s` and `eprint_s` for
  S-expressions. Keep `Out_channel` for files and other explicit channels, never for
  `Out_channel.output_line stdout`. Interpolate a typed value as `%{value#Type}`, never
  `%{Type.to_string value}`; in `[%message]`, pass it as `(value : Type.t)`. Put long or
  foreign-language text in a `templates/` file that a dune rule embeds, and write short
  multi-line literals as `{|...|}`.

### Errors and resources

- Never raise for a failure: return `Or_error.t`, or `Result.t` with a typed error when
  callers must tell failures apart. Raise only where a convention expects it (an `of_string`
  that Core's interfaces call, an `_exn` twin of a safe function), and wrap raising foreign
  code in `Or_error.try_with` at its boundary. Tests may raise.
- Sequence with `let%bind.Or_error` and map with `let%map.Or_error` (`.Result` and `.Option`
  likewise); never forward errors with a hand-written `match`. Keep explicit matches for
  recovery, cleanup, aggregation and status policy.
- Build structured failures with `Or_error.error_s [%sexp (error : t)]`; never render an
  S-expression to a string to rebuild an error.
- Keep `Or_error.error_string` for a fixed message with no data, and use it sparingly; a
  message with values is `[%message ...]`, never `[%string ...]`. Never `Or_error.errorf` or
  `failwith`.
- Write an error's payload with `[%message "what failed" (value : T.t)]` or an `Error`
  constructor, never `raise_s (Sexp.Atom ...)`; where a raise is conventional, use
  `raise_s [%message ...]`.
- Keep conversions and constructors pure: return notes and warnings as typed values and print
  them where the command reports. Do nothing with effects at module load.
- Use Core's system modules (`Core_unix`, `Filename_unix`, `Sys_unix`); never alias the
  standard library's `Unix`.
- Give each acquire/release pair one `with_*` function that owns both halves and takes the
  scoped body as `~f`, or `let%with` where the project has ppx_with. The owner cleans up
  after errors and exceptions, resolves operation and cleanup failures once, and never skips
  a release.

### Interfaces (CLI, I/O, processes)

- Build command-line tools with `Command_unix`, `Command.basic_or_error`, `Command.group` for
  subcommands, and ppx_jane's command syntax; prefer subcommands to mode flags.
- A command converts arguments, reports diagnostics and calls domain operations. Decide a
  closed choice once, where the value enters, with `Command.Arg_type.enumerated (module M)`,
  then `match` on the variant; never re-test strings.
- Pass arguments through to another program with `flag "--" escape`; never read or rewrite
  `Sys.argv` around `Command`, and never declare dummy flags.

### Tooling and verification

- Write tests as expect tests in an `(inline_tests)` library beside the code. Print typed
  values (a record or variant deriving `sexp_of`, or an `Ascii_table` of typed rows) and keep
  the expectation inline; write no assertion helpers, test runners or manifests.
- Name a test file `test_<module>.ml` and each test with a plain phrase. Write one test per
  behaviour or small table, with setup, action, output and `[%expect]` kept together.
- Format with the pinned ocamlformat, Jane Street profile, at the repository's line width
  (100 by default). Compile with `-w +a-40-42-44 -warn-error +a -alert ++deprecated`, and
  explain each disabled warning in the dune file in plain words, with an example.
- Pass `--no-update-lock-file` to flake commands. Accept an intended expectation change with
  `dune promote` only after reading the diff.

## References

| Read before | File |
| --- | --- |
| defining types, records, variants, constructors or defaults | [references/types-and-data.md](references/types-and-data.md) |
| creating modules, files or interfaces, or changing functions or patterns | [references/structure-and-naming.md](references/structure-and-naming.md) |
| adding constants, derivers, string conversions, comparisons, S-expressions or text | [references/values-and-text.md](references/values-and-text.md) |
| handling errors, effects, processes or resources | [references/errors-and-resources.md](references/errors-and-resources.md) |
| writing tests, or changing dune flags, warnings or formatting | [references/verification.md](references/verification.md) |

## Completion report

End the final message with an ocaml report: one line for each rule group above, marked
changed (with the paths), reviewed unchanged (with the reason) or not applicable; then the
build, test and format commands that ran with their results, and those that could not run.
Combine groups that share an outcome.
