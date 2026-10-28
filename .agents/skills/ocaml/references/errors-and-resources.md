# Errors and resources

Detail for the "Errors and resources" rules of the ocaml skill.

## Contents

- Returning errors
- Binding syntax
- Structured errors
- Explicit matches
- Purity and effects
- System modules
- Resource ownership

## Returning errors

- Never raise for a failure. Return `Or_error.t`, or a `Result.t` with a typed error variant
  when callers must tell failures apart, and thread it to the boundary that can act on it.
- Raise only where a convention expects it, such as an `of_string` that Core's interfaces
  call (`Stringable`, sexp converters) or an `_exn` function beside its non-raising form.
- Wrap foreign code that raises in `Or_error.try_with` at its boundary.
- Tests are exempt: a failed check may simply raise.

## Binding syntax

- Sequence success-only steps in `Or_error.t` with `let%bind.Or_error`, and map a pure
  success with `let%map.Or_error`. Never spell unchanged error forwarding as
  `match result with Error error -> Error error | Ok value -> ...`, including through
  aliased variants.
- Keep a genuinely typed `Result.t` error with `let%bind.Result` and `let%map.Result` when
  the pinned Result API exposes the syntax, and `Result.bind` or `Result.map` only when it
  does not. Do not erase the error type to force an `Or_error` binding.
- Map and bind an `Option` with `let%map.Option` and `let%bind.Option` rather than piping into
  `Option.map ~f:(fun ...)`; use the `Or_error` forms instead of closure-based plumbing.

## Structured errors

- Construct structured failures with `Or_error.error_s [%sexp (error : t)]`. Use
  `Error.create_s [%sexp (error : t)]` only where an operation consumes an `Error.t`.
- Never render a typed S-expression to a string and rebuild it with `Error.of_string` or
  `Or_error.error_string`. Keep nested errors structured, and render human text only at the
  reporting boundary.
- Use `Or_error.error_string` sparingly, and only for a fixed message that carries no data:
  `Or_error.error_string "standard input requires -x"`. When the message carries values,
  write `Or_error.error_s [%message "missing argument" (spelling : Spelling.t)]`, never
  `Or_error.error_string [%string "missing argument to %{spelling#Spelling}"]`; the payload
  stays typed and printable as data. Never use `Or_error.errorf` or `failwith`.
- When callers branch on a failure (a driver mapping usage errors to exit codes and wording,
  for example), return `Result.t` with a typed error variant, and render its human text once,
  at the boundary that reports it.
- Write the payload of an error, or of a conventional `raise_s`, with
  `[%message "what failed" (value : T.t)]` or an `Error` constructor, never as a hand-built
  tree: `raise_s [%message "unknown level" (level : Level.t)]`, not
  `raise_s (Sexp.Atom "unknown level")`. The S-expression rules are in
  [values-and-text.md](values-and-text.md#s-expressions).

## Explicit matches

- Explicit matches remain the right tool for recovery, cleanup, aggregation and status
  policy. Preserve execution order, the attempt to release every resource, and the
  precedence of the primary error.
- Compute independently required cleanup results before binding their values; binding the
  calls themselves can skip later releases. Do not replace first-error selection with
  applicative `and`, or deliberate error accumulation with short-circuiting binds.

## Purity and effects

- Keep conversions and constructors (`of_string`, `of_*`, `create`, `parse`, `classify`)
  pure: no output and no global state. Return notes and warnings as typed values and print
  them where the command reports its result; only functions named as actions (`print`,
  `initialize`, `run`) have effects.
- Do nothing with side effects at module load; a constant may use an `_exn` constructor on a
  known-good literal.

## System modules

- Use Core's system modules (`Core_unix`, `Filename_unix`, `Sys_unix`) for processes, files
  and descriptors: `Core_unix.create_process_with_fds`, `Core_unix.waitpid` with its
  `Exit_or_signal.t`, `Core_unix.with_file`.
- Never alias the standard library's `Unix` to get past Core's deprecation.

## Resource ownership

- Give each acquire/release pair one `with_*` function that owns both halves, such as
  `Temp_file.with_file ~prefix ~suffix ~f`, which creates a file, passes its path to the body
  `~f` and removes it. Callers never write `Exn.protect ~finally` around a resource. Where
  the project has ppx_with, `let%with` expresses the same scope.
- Keep resource-backed work linear inside that scope. The owner cleans up after returned
  errors and unexpected callback exceptions, then resolves the operation and cleanup outcomes
  once. Do not scatter release calls through success and error branches, and do not create a
  family of forwarding helpers to finish each path.
- Inside the owner, use the pinned library's scoped finalization when its error model fits.
  `Exn.protect` can bracket a foreign callback that returns a plain value within one
  `try_with`; returned `Error` values need explicit, result-aware cleanup. Keep both the
  operation's and the cleanup's failures, with typed context. Do not invent a protect API
  the library does not have.
- Express a write, close and commit sequence through one scoped operation instead of a table
  of per-step results or helpers that carry earlier results along. Keep primary and
  secondary error selection at the owner.
- A commit's success means the commit happened, not that it was skipped. Record completed
  releases and transfers so that finalization cannot release a reused descriptor or remove
  a published output. A failed close does not by itself show who owns the resource; follow
  the pinned API's release semantics.
- Use the pinned library's resource-management facilities where they fit, and do not
  introduce a generic lifetime framework or policy flags for one concrete lifecycle.
