# Agent instructions

Read `README.md`, `docs/design.md`, `docs/trust.md`, `docs/workflow.md`, your card and its cited
`docs/api` sections before working. For run mechanics read `run/RUNBOOK.md` in the primary
checkout. `docs/api/*.md` fixes public names, types and theorem statements; `docs/api/names.md`
indexes them. A change of meaning needs an owner ruling. For minimal fixes to a contract that does
not type-check, has a mismatched name or lacks an obvious well-formedness premise, follow C14 in
`run/DECISIONS.md`: report the exact fix for review and the next docs checkpoint.

## Skills

Before editing a matching authored file, read the skill and its required references completely.
Apply it to every line changed. Repository instructions and explicit owner instructions take
precedence. Generated and vendored files retain their own conventions.

| Files | Skill |
| --- | --- |
| `*.v` | `.agents/skills/rocq/SKILL.md` |
| `*.ml`, `*.mli`, `*.mll`, `*.mly`, `dune`, `dune-project` | `.agents/skills/ocaml/SKILL.md` |
| `justfile`, `Justfile`, `.justfile`, `*.just` | `.agents/skills/just/SKILL.md` |
| C++ source and headers, `CMakeLists.txt`, `*.cmake` | `cpp` |
| `*.py`, `*.pyi` | `python` |
| `*.typ` | `typst-review` |

End your report with the completion report of each skill applied. Do not use Python.

## Design invariants

- Core packages depend only on Rocq Stdlib; only Float may use Flocq.
- Pass dictionaries explicitly as records parametric in their types, with laws in separate `Prop`
  records. Do not put a carrier `Type` field in a dictionary or create global instances.
- Keys have injective encodings into `positive`; maps and sets use canonical binary tries.
- Require the weak lattice laws; least-upper-bound laws are separate. Model analyses as constraint
  systems, with full checking and static-system cut-point checking.
- Build indexes once; do not scan lists inside loops. Use binary fuel or well-founded recursion.
- Every `.v` basename is unique and begins with its package name. Theories contain no `Extract`
  directives; extraction choices belong to clients.
- Prove every contracted claim. Do not add axioms, `Admitted`, `admit`, or `give_up`. The sole
  exception is the exact Flocq-related axiom allowance for Float in C13; no other package may
  depend on axioms. See `docs/trust.md`.

## Work and verification

Use `just` inside the pinned shell for builds, tests, checks and formatting, never raw `dune`.
Never modify `_build/` by hand. Follow the resource caps and target restrictions in the runbook.
Rocq tests are `Example`s in `tests/`, checked by computation. OCaml tests are inline expect tests
at the bottom of the module's own `.ml`; this overrides the OCaml skill's test-file rule.

Work only on assigned paths and branches. Stage and commit explicit paths; do not amend, rebase or
force-push published work. Workers do not push; landers follow the runbook. Never copy source from
another library. Implementation workers do not edit prose documentation, including `docs/api`;
report documentation impacts and C14 fixes for the owner to incorporate.
