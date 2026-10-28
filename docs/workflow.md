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
currently checks formatting; TOOL-1 adds the source and claims checks. `just fmt` formats sources;
if it rewrites files, run it again to check the resulting state. The planned bench arrives with
TOOL-2; there is no bench recipe yet.

The recipes run in `gaulois.slice` with a 1536 MiB default per-command memory cap and no swap;
`build` and `test` use two jobs. `just slice-cap` sets the shared slice cap to 9 GiB until reboot;
`just slice-cap 4G` lowers it for a competing workload. The implementation runbook fixes stricter
rules for agents, including one heavy command at a time and no override of the per-command cap.
A fresh skeleton build can warn about empty dependency theories and still succeed.

The setup's previous capped `nix develop --no-update-lock-file -c just build` succeeded. This
records a
skeleton smoke check, not a full implementation build. Run tests appropriate to each card and
follow `run/RUNBOOK.md` for reviews, claims audits and landing.
