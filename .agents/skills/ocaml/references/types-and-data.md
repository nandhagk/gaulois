# Types and data

Detail for the "Types and data" rules of the ocaml skill.

## Contents

- Owning modules
- Variants, records and booleans
- Instances as data
- Semantic types
- Constructors and records
- Defaults and integers

## Owning modules

- Each concept has an owning module whose main type is `t`:
  `module Status = struct type t = ... end`, used as `Status.t`. A file is already a module,
  so its main type is `type t = ...`, and further concepts in that file get named submodules.
- Declare no bare named types (`type status = ...`), whether aliases, records or variants.
  This applies to interfaces and tests too. A bare type is acceptable only when it cannot be
  avoided, such as an external interface or a type dependency that cannot take this shape;
  document why `Module.t` cannot be used.

## Variants, records and booleans

- Use ordinary variants, not polymorphic variants, unless an external API requires them.
- Use records, not tuples, for anything with more than one meaningful part; a positional
  `(int * int) list` is a list of records waiting to be named.
- Represent modes, states and outcomes with named variant constructors, never with booleans
  as data in fields, parameters or results. Flags that an external interface requires stay
  booleans.
- A function that classifies a value returns a variant naming the classes, so every branch
  says what it handles and a new class shows up at every match. Return
  `Success | Failure of { code : int }` rather than offer `is_success : t -> bool` and make
  callers look the code up again; `Marker | Plain` rather than `is_marker`. A boolean stays
  right for a plain test that is only passed to a filter or combined with `&&` or `||`.
- Convert a required foreign boolean flag into a descriptive variant at the boundary with the
  owned model. A report or protocol between two owned components is not a foreign interface:
  change its producers and consumers together when its representation changes.
- Use ordinary variants for closed semantic choices and categories: owners, diagnostic
  reasons, kinds and modes. Do not pass string literals or string parameters as selectors
  or context classifiers. For example, a diagnostic owner separates its category from its
  dynamic source name:

  ```ocaml
  module Owner = struct
    type t =
      | Alignment
      | Aggregate of string
  end
  ```

- Pass typed values to `invalid ~owner ~problem`, rather than `invalid "alignment" ...`.
  Keep genuinely open source names, paths and foreign text as payloads, using existing
  semantic types where available. Here the aggregate name is real text, so it remains a
  string; the closed owner category is a variant. This does not make known allocator
  instances into constructors; model those as data below.
- Prefer types that admit only valid states to repeated run-time checks.
- When a sequence must be nonempty, use Jane Street's `Nonempty_list.t` rather than rejecting
  `[]` repeatedly or defining a local wrapper. Carry it in function arguments, record fields
  and results whenever the invariant holds. Validate external ordinary lists once, and use
  nonempty-preserving operations such as `map` internally. Filtering can legitimately return
  an ordinary list; foreign interfaces and sequences that permit no elements keep lists.

## Instances as data

- A type models the concept, never the instances known today. One constructor per supported
  backend, or fields that only one backend fills, turn every new instance into edits across
  every match. Give the concept one record of what instances differ in (a name, a source
  location, extra flags), and keep a small variant inside it only for behaviour that really
  differs.
- When adding an instance should need no code change, keep the records in an S-expression
  file read with `[@@deriving of_sexp]`, validate them where they are loaded (unique names,
  referenced files present), and look them up through a `Map.t` built from them once:

  ```text
  ((name small) (source SMALL_SRC) (flags (-DSMALL_PAGES=1)))
  ((name fast) (source FAST_SRC) (flags ()))
  ```

## Semantic types

- Give a value whose meaning goes beyond its representation its own module with an abstract
  `t` and a validating constructor: `Size.t` for a byte count that must be a multiple of 16
  below 2^32, not a raw `int`; a variant with `[@@deriving enumerate, string]` for a closed
  set of names, not strings. Unwrap to the raw form only at a foreign boundary.
- When changing a record, audit the interfaces, errors and callers too. Carry paths, logical
  identities, digests, indices, addresses and extents in their actual semantic types:
  different digest algorithms, or an address and a byte count, are not interchangeable, and a
  scalar alias in an interface does not make them so.
- Reuse native identity types and existing owners before adding wrappers. Give an infallible
  wrapper an infallible constructor, and do not invent validation, file-system resolution or
  version grammars to justify a type.
- With typed fields, prefer role names (`original`, `snapshot`, `digest`) to representation
  suffixes (`original_path`, `content_digest`) when the suffix adds no distinction.

## Constructors and records

- A constructor that cannot fail returns `t`, never `t Or_error.t`.
- When every field is already a validated type, expose the record instead of hiding it
  behind `create` and hand-written getters.
- Keep `t` abstract only for an invariant that spans fields, and then derive its getters with
  `[@@deriving fields ~getters]` (ppx_fields_conv, part of ppx_jane) instead of writing
  `let name ({ name; _ } : t) = name`.

## Defaults and integers

- Give each setting's default as a typed constant in the module that owns the setting
  (`Size.Stack.default`, `Allocator.Name.default`), and derive help text from it. Never
  collect defaults in a separate list or file.
- Represent integers with `int`, never `int64` or `Int64`: the 63-bit `int` covers sizes,
  offsets and counts. Wrap it in a domain type when it means something, and convert at the
  boundary when a foreign API insists on a fixed width.
