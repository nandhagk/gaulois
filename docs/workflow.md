# Workflow

Use the pinned Nix development shell from the repository root:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 -- \
  nix develop --no-update-lock-file
just --list
just slice-cap
just build
just test
just check
```

The pinned setup reports Rocq 9.3.0, Stdlib 9.2.0, Flocq 4.2.2, OCaml 5.5.0, dune 3.23.1,
ocamlformat 0.29.0 and just 1.58.0. The shell enables the shared Dune cache in hardlink mode at
`~/.cache/gaulois/dune` and unsets `LD_LIBRARY_PATH`.

`just build` builds all default targets; pass targets to restrict it, for example
`just build theories/Graph`. `just test` builds the tests, examples and inline tests. `just check`
checks formatting, source hygiene, layout, theorem assumptions and the selected extraction
artifacts, including their generated native compilation. `just fmt` formats sources; if it rewrites
files, run it again to check the resulting state. `just bench -help` describes the bounded benchmark
options and defaults; for example, `just bench -start 8 -steps 3 -repetitions 3` runs a small
experiment.

The recipes run in `gaulois.slice` with a 1536 MiB default per-command memory cap and no swap;
`build` and `test` use two jobs. `just slice-cap` sets the shared slice cap to 9 GiB until reboot;
`just slice-cap 4G` lowers it for a competing workload. Agents follow the implementation runbook
and recorded run-specific rulings for resource limits, including one heavy command at a time.
A build can warn about dependency theories that do not yet contain a `.v` file and still succeed.

Landed cards report their own focused builds and checks; they do not substitute for the planned
fresh FINAL build. Run tests appropriate to each card and follow `run/RUNBOOK.md` for reviews,
claims audits and landing. The examples layout checker repair has landed; individual example
cards still require their own verification and review.
Focused measurements may use the harness for a specific unresolved choice; benchmarks are not a
completion gate. Its timings include workload construction and validation, and are experiments,
not complexity proofs.
