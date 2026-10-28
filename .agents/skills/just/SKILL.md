---
name: just
description: Use when writing, editing, reviewing or refactoring justfiles (justfile, *.just modules) - modules and recipe organisation, prerequisites, argument forwarding, working directories, shells and settings, checked against the pinned Just version.
metadata:
  file-patterns: "justfile Justfile .justfile *.just"
---

# Just

A justfile is a thin, discoverable front end to the project's tools: modules for namespaces,
prerequisites for pipelines, and Just's own parameters, attributes, listing and help instead
of custom dispatch.

## Scope and precedence

- These rules apply to every justfile and `*.just` module in the repository.
- The user's explicit instructions come first, then the repository's own instructions
  (AGENTS.md, CLAUDE.md and the existing justfile conventions); then this skill. When one of
  them overrides a rule here, follow it and say so in the completion report.
- Confirm every feature against the Just version the repository pins (its flake or lock
  file) instead of assuming newer syntax.

## Workflow

1. Before editing, read the root justfile, the modules it loads, the shared settings file,
   and the pinned Just version.
2. Apply the rules to every recipe you add or change.
3. Before finishing, inspect the result with `just --list`, `just --show RECIPE`,
   `just --usage RECIPE` and `just --dry-run RECIPE ...`, run `just --fmt --check`, run each
   changed recipe once, and write the completion report.

## Rules

### Modules and organisation

- Group recipes into modules, which are subcommands: `mod c "just/c.just"` gives
  `just c build`. Never encode a namespace in a recipe name (`c-build`, `ocaml-run`).
- Give each module a `[default]` recipe, mark intermediate pipeline steps `[private]` with
  plain names (`generate`, `compile`), and use `[group("...")]` to arrange long listings.
- Let root recipes aggregate module recipes through `module::recipe` dependencies, for
  example `format: model::format c::format`.
- Modules have independent settings and their own default working directory. Keep shared
  settings (the shell, `set positional-arguments`, paths such as
  `build := env("PROJECT_BUILD", justfile_directory() / "build")`) in one file that every
  module imports explicitly, and `set working-directory := ".."` in a module whose recipes
  use repository-root paths. Check the working directory whenever a recipe moves between
  modules.
- Document each public recipe with a comment above it; `just --list` shows it.

### Recipes

- Give each recipe one command. Compose multi-step work with prerequisites (generate, then
  compile, then run), including parameterised ones such as `run program: (assemble program)`,
  instead of chaining commands inside one recipe.
- Define a shared invocation once. When recipes repeat a command prefix (a lock, a memory cap,
  an environment, a tool with fixed options), put it in one `[private]` recipe that takes the
  varying part as `+args`, and let each recipe delegate with a recursive call that keeps
  argument boundaries: `just run check "$@"`, or `just MODULE run check "$@"` inside a module.
  A dependency cannot do this when arguments vary, because `(run "check" args)` passes a
  variadic parameter as one space-joined argument. A fixed prefix without arguments may be a
  variable instead.
- Keep wrappers thin: the wrapped tool owns its behaviour and option parsing. When Just owns
  an option, declare it with an attribute such as `[arg("config", long="config")]`; forward
  tool-owned options unchanged rather than parsing them twice.
- Recipes invoke workflows; they do not implement them. Recovery, metadata, logging and
  finalization belong in the owning tool's command-line interface, and a script recipe is not
  an exception: keep only the shell glue needed to invoke the operation within its existing
  limits.
- When the workflow already runs inside a pinned shell, ordinary recipes use that
  environment. Keep shell activation in explicit environment-entry recipes instead of
  repeating it in every command.
- Ordinary recipe lines run in separate shells. Set a strict shell
  (`set shell := ["bash", "-euo", "pipefail", "-c"]`), and use a script recipe
  (`[script("bash", "-euo", "pipefail")]`) only when lines share shell state.
- Use `[no-cd]` when a recipe must run in the caller's directory, and pass that directory on
  explicitly if the tool needs it.
- Recipes are not test harnesses: no per-case recipes and no golden-output diffs. A `test`
  recipe builds what the tests need and forwards its arguments to the test runner.

### Arguments

- With `set positional-arguments`, forward arguments as `"$@"` (or `"${@:2}"` after leading
  parameters) so that each keeps its boundary. Never interpolate user input into shell text.
- Use `*args` for optional forwarding and `+args` when at least one argument is required.
- Forward options and arguments to an already selected tool directly with `"$@"`, without
  requiring `--`: `just build --jobs 3`. Preserve delimiters owned by the wrapped tool.
- Require `--` only to introduce a separate executable command: `just capped -- make all`.
  Just owns declared `[arg]` options; check the pinned version's parsing, including whether
  it consumes `--`, before forwarding.

## Completion report

End the final message with a just report: one line each for modules and organisation,
recipes, and arguments, marked changed (with the recipes), reviewed unchanged (with the
reason) or not applicable; then the inspection, formatting and recipe runs that took place
with their results, and those that could not run.
