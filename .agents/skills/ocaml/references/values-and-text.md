# Values and text

Detail for the "Values and text" rules of the ocaml skill.

## Contents

- Constants
- Derivers
- String conversions
- Core modules and comparisons
- S-expressions
- Building and writing text

## Constants

- Define every fixed spelling or number once, tests included, as a named constant in its
  owning module: reserved names, defaults, limits, alignments, file modes. When the values
  form a closed set, use a variant (`I32 | F64 | Void`) instead.
- Derive related values from the constant (`String.length prefix`, a default's printed form)
  instead of repeating them.

## Derivers

- Use Core and ppx_jane. Derive code instead of writing it by hand:
  `[@@deriving sexp_of, compare, equal, enumerate, string]`, and ppx_yojson_conv
  (`[@@deriving yojson_of]` when only encoding is needed) instead of building JSON trees.
- Derive only the directions you use (`to_string`, `sexp_of`). An unused decoder adds code,
  and its wildcard match trips warning 4, which must never be silenced around a derivation.

## String conversions

- Derive string conversions with ppx_string_conv (part of ppx_jane):
  `[@@deriving string ~capitalize:"kebab-case"]`, or whichever rule matches the external
  spelling (`snake_case`, `lower sentence case`, ...), with `[@rename "..."]` only for
  exceptions. Never hand-write a `to_string` or `of_string` match, or a lookup through `all`.
- Parse a closed-set command-line argument with `Command.Arg_type.enumerated (module M)`,
  which also lists the values in `--help`. Generate a family of similar flags by mapping over
  the variant's `all`.
- A derived `of_string` raises by convention; wrap it with `Option.try_with` or
  `Or_error.try_with` where a caller needs a value.

## Core modules and comparisons

- After `open Core`, use `Map`, `List` and the other opened modules directly, without
  redundant `Core.Map` prefixes. Repair shadowing at its owner.
- Adapt a foreign container once into a Core container with the correct semantic comparator,
  reusing existing native key types. Preserve ordering, duplicate policy and identity
  semantics: a native, environment-sensitive comparison is not automatically replaceable by
  a derived or polymorphic comparator.
- After `open Core`, the top-level `=`, `<>`, `<`, `>` and `compare` are specialised to
  `int`: compare ints with them (`count = 1`, `~compare`), never with `Int.equal` or
  `Int.compare`. Other types use their module's `equal` and `compare` (`String.equal`), and a
  type gets its own from `[@@deriving equal, compare]`, not `let equal = Int.equal`.
- For composite types, use `[%equal: string option]`, `[%equal: Entry.t list]` or
  `[%compare: string list]` instead of chains such as `Option.equal String.equal`.
  A native or context-dependent comparator retains its semantics; do not replace it with a
  structural comparison merely to use the PPX.
- Look named items up in a `Map.t` keyed by the name's own type, built once where the
  collection is made (`Map.of_alist_or_error (module Name) entries`), so a duplicate name
  fails there. Chains of `String.equal` or a `match` on string literals scatter the set of
  names through the code and miss a new one silently.

## S-expressions

- Construct typed S-expressions with `[%sexp (value : Module.t)]`, in production code and
  tests, rather than calling `Module.sexp_of_t value`.
- Keep an explicit converter reference when a callback or a module or external interface
  requires the function, or when the syntax extension cannot express the conversion; never
  replace a required converter binding with a value.
- Never build or match S-expressions by hand. The ban covers the `Sexp.Atom` and `Sexp.List`
  constructors and patterns in every spelling: qualified (`Sexp.List [ Sexp.Atom "name" ]`),
  through a local open (`Sexp.(List [ Atom "name" ])`, `let open Sexp in`), after
  `open Sexp`, or resolved by a type annotation (`(Atom "name" : Sexp.t)`), in production
  code, tests and tools alike. A hand-built tree repeats the type's shape where the compiler
  cannot check it, and a hand-written reader loses the field-level errors that the derived
  one reports.
- Model the data as a type and derive its converters. Use `[@@deriving sexp]`, or just
  `of_sexp` when the code only reads and `sexp_of` when it only prints. Describe the shape in
  the type with ppx_sexp_conv attributes: `[@sexp.option]` for a field that may be absent,
  `[@sexp.list]` for a list that may be omitted when empty, `[@default x]` for a default, and
  `[@@sexp.allow_extra_fields]` for a record that must ignore fields it does not know:

  ```ocaml
  type t =
    { name : string
    ; flags : string list [@sexp.list]
    ; source : string option [@sexp.option]
    }
  [@@deriving of_sexp] [@@sexp.allow_extra_fields]
  ```

  This reads `((name small) (source SMALL_SRC) (extra 1))` as `flags = []` and
  `source = Some "SMALL_SRC"`, and ignores `extra`.

## Building and writing text

- Build text with `[%string]` interpolation. Never use `^`, printf-style functions, `Printf`
  or `Format`, and do not add an `Import` module that shadows them.
- Write to the standard streams with Stdio's helpers, which Core re-exports:
  `print_endline text` and `print_string text` for standard output, `prerr_endline text` for
  standard error, and `print_s [%sexp (value : T.t)]` and `eprint_s ...` for S-expressions.
  Keep `Out_channel` for files and other explicit channels (`Out_channel.with_file`,
  `Out_channel.output_string channel`); never spell a write that a helper covers through
  `Out_channel` (`Out_channel.output_line stdout text`, `Out_channel.output_string stdout
  text`, `Out_channel.output_line stderr text`). Stdio has no `prerr_string`, so text without
  a final newline goes to `Out_channel.output_string stderr text`.
- Interpolate a value of a type with a string conversion as `%{value#Type}`, which calls
  `Type.to_string`: `[%string "level %{level#Level}"]`, never
  `[%string "level %{Level.to_string level}"]`. `[%message]` has no `%{...}` interpolation:
  pass the value annotated, `[%message "unknown level" (level : Level.t)]`, which converts it
  with `Level.sexp_of_t` and tags it, instead of `(Level.to_string level)`.
- Keep text in another language (C, Rocq) or longer than a few lines in a `templates/` file
  beside its library, embedded at build time by a dune rule (`%{read:...}`). Write short
  multi-line literals as `{|...|}`.
