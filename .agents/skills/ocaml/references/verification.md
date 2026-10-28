# Verification

Detail for the "Tooling and verification" rules of the ocaml skill.

## Contents

- Expect tests
- What a test prints
- Organizing tests
- Formatting and warnings
- Builds

## Expect tests

- Write tests as expect tests (`let%expect_test` from ppx_expect, part of ppx_jane). Print
  the value under test as a typed table or a pretty S-expression, or capture a command's
  stdout, stderr and exit status, and keep the expected output inline in
  `[%expect {| ... |}]`.
- Write no hand-rolled assertion helpers, test runners or expectation manifests.
- Put tests in an `(inline_tests)` library beside the code they test. Accept an intended
  change with `dune promote` after reading its diff.
- Test the library API directly; run the executable only to test the command line itself
  (flags, exit status, help).

## What a test prints

- What a test prints is a proper type owned by a module, such as:

  ```ocaml
  module Case_outcome = struct
    type t =
      | Accepted of { warnings : Warning.t list }
      | Rejected of { diagnostic : string }
    [@@deriving sexp_of]
  end
  ```

  Render typed rows through table columns, or derive `sexp_of` and use
  `print_s [%sexp (outcome : Case_outcome.t)]`. Never print ad-hoc tuples or polymorphic
  variants.
- Prefer Textutils's `Ascii_table` for repeated comparable rows, such as size conversions,
  limits and signatures. Pass typed records to typed columns rather than turning observations
  into string-list rows. Use `to_string_noattr` with an explicit width and ASCII bars for
  deterministic output, without truncating or suppressing observed facts. Take Textutils from
  the project's pinned dependencies.
- Keep nested structures as pretty S-expressions; avoid `~mach:()` when it makes them dense
  or overlong. Preserve exact captured text when testing command output, diagnostics or help.

## Organizing tests

- A type or helper used by one test only is a local module inside that test
  (`let module Size_row = struct ... end in`); only what several tests share sits at the top
  of the test file.
- Name a test module after the module it tests, with a `test_` prefix (`test_size.ml` tests
  `Size`), so that it cannot collide with the module under test; never a plural or a suffix
  such as `sizes.ml` or `size_checks.ml`.
- Write one `let%expect_test` per behaviour or per small table of inputs; a table prints one
  line per input, so that a change shows exactly which input moved.
- Keep each logical group's setup, action, printed observation and `[%expect]` close
  together. Within one scenario, several print and expect pairs may make the steps easier to
  follow; independent behaviours get separate named tests. Do not collect unrelated
  observations into one expectation at the bottom, and keep enough input context in a table
  to identify each result.
- Name an expect test with a plain phrase, spaces included, saying what it shows
  (`let%expect_test "sizes round up to 16 bytes"`), never a snake_case identifier. When the
  name cannot say exactly what is checked, add a `(** ... *)` comment above the test.

## Formatting and warnings

- Format with the pinned ocamlformat, Jane Street profile, at the repository's line width
  (100 unless it says otherwise).
- Compile hand-written code with `-w +a-40-42-44 -warn-error +a -alert ++deprecated`.
- Explain each disabled warning in the dune file in plain words, with a one-line example of
  the code it would reject. Warnings 40 and 42 flag record fields named through a type
  annotation without opening their module (`({ stack; heap } : Config.t)`, the style above);
  44 flags an `open` that deliberately hides names (`open Core` hiding `List`). Disable 4 only
  for deliberately fail-closed matches on an extensible AST.

## Builds

- Run builds inside the repository's Nix shell (`nix develop` or direnv), and pass
  `--no-update-lock-file` to flake commands.
- Build generated modules in their own dune stanza with their own warning policy.
