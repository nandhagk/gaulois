# Structure and naming

Detail for the "Structure and naming" rules of the ocaml skill.

## Contents

- Interfaces
- Files and modules
- Records and projections
- Functions
- State and data layout

## Interfaces

- Write an `.mli` for every module except `main.ml`. Expose what callers need and keep
  representations private where that helps.
- Give a value or type a `(** ... *)` doc comment when its name and type do not say what it
  does, or when callers must know something the signature hides: a precondition, an
  invariant (`Size.t` is a multiple of 16 below 2^32), units, an effect, or a raising
  convention. Leave self-descriptive items bare (`val to_string : t -> string`), and never
  restate the signature in words.

## Files and modules

- Name OCaml files and directories in lowercase snake_case (`engine_limits.ml`,
  `main_prelude.mli`, `tests/runner/`). The module name (`Engine_limits`) comes from the
  file, so a file name is never capitalised.
- The exception is a file implementing a module whose name a dependency fixes, which keeps
  the dependency's spelling (`CBuiltins.ml`); a folder holding only such files may keep the
  name the project gives it.
- Keep one concept per module, at most about 300 lines, and split a module that mixes stages
  such as parsing, renaming and code generation.
- Modules of a wrapped dune library need no project prefix (`Steps`, not `Project_steps`).
  Check a new name against unwrapped dependencies, because a local module silently shadows
  theirs, and never name a submodule after a Core module it would shadow (`Bytes`, `String`,
  `List`).
- Keep conversions in the type's module (`Keys.Line.of_key`, `Keys.Line.of_arrow`) and give
  formatting its own operation (`Hex.word`).

## Records and projections

- Annotate record construction and patterns with their type,
  `({ image; max_steps } : Options.t)`, never `Options.{ image; max_steps }`.
- Never project a field as `x.Module.field`. Destructure with an annotated record pattern,
  `let ({ types; funcs; _ } : Wasm.Module.t) = m in`, or call a getter derived with
  `[@@deriving fields ~getters]` on your own records. Destructure a foreign record once,
  where it enters.
- Never qualify only the first or one constructor to establish the type for later
  unqualified siblings. Annotate the existing parameter, scrutinee or function signature,
  then use unqualified patterns consistently:

  ```ocaml
  let source (form : Main_form.t) =
    match form with
    | Void -> ""
    | Arguments -> Prelude_templates.main_arguments
    | Environment -> Prelude_templates.main_environment
  ;;
  ```

- If qualification is needed, qualify every sibling of the same constructor family.
  Treat nested and tuple families independently: qualifying an outer constructor does not
  require qualifying an inner family. Add no broad opens or wrapper types to avoid an
  annotation; keep the annotated-record rule above.
- Match a list instead of using `List.hd_exn`.

## Functions

- Keep functions short, about 30 lines. Lift helpers to the top level instead of nesting
  closures inside one function, and separate the traversal (which nodes) from the per-node
  checks (what to report).
- Confine a necessary accumulator to one small function, with a comment saying why.
- Extract meaningful semantic stages. Moving result plumbing into forwarding helpers,
  compressing lines, or passing a large context record does not improve a design.
- Prefer pipelines to nested application (`result |> Sail.uint |> Big_int.to_int`), and use
  low-precedence application where it removes parentheses:
  `Or_error.try_with @@ fun () -> ...`, never `Or_error.try_with (fun () -> ...)`.
- Never eta-expand: pass the function or a partial application,
  `~f:(Warning.equal Long_double)`, not `~f:(fun warning -> Warning.equal warning Long_double)`.
  A check repeated twice becomes a named helper.
- Constant callbacks are explicit: `fun () -> value` or `fun (_ : t) -> value`. Do not use
  `Fn.const`; the lambda makes the ignored input and its type clear.
- Label arguments so a call reads without the definition at hand, internal helpers included:
  leave a one-argument function unlabelled; with two, label them when they share a type or
  their order is arbitrary (`copy ~src ~dst`); with three or more, label every argument
  except the value the function is about, which stays positional for pipelines
  (`List.fold items ~init ~f`).
- Take a callback as `~f`, after the other arguments, so a `fun` body closes the call; name a
  second callback by its role (`~finally`, `~on_error`). A `with_*` owner takes its body as
  `~f` too.
- Write scoped operations with ppx_with when the project has it:
  `let%with x = with_thing args in body` (`let%with.tilde` for a `~f` argument), instead of
  passing a closure.

## State and data layout

- Thread state functionally: return an updated `t` instead of mutating fields through
  unit-returning updates. Comment each mutation that must stay, such as a flag written by a
  signal handler or the globals of a generated model.
- Use `Array.make_matrix` for two-dimensional data, not a flat array indexed
  `row * columns + column`.
