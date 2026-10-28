{ pkgs }:
let
  # The stock Rocq 9.3 package set: every package below comes from the binary cache.
  rocq = pkgs.rocqPackages_9_3;
  # The OCaml package set that this Rocq was built with, so the tools use the same compiler.
  ocaml = rocq.rocq-core.ocamlPackages;
in
{
  devShell = pkgs.mkShell {
    packages = [
      rocq.rocq-core
      # Rocq 9 ships its standard library as a separate package; Rocq finds it through ROCQPATH.
      rocq.stdlib
      # Only the optional float package uses Flocq.
      rocq.flocq
      ocaml.ocaml
      ocaml.findlib
      ocaml.dune_3
      ocaml.ocamlformat
      # The libraries of the OCaml tools and of their inline tests.
      ocaml.core
      ocaml.core_unix
      ocaml.ppx_jane
      ocaml.ppx_expect
      pkgs.just
      pkgs.git
      pkgs.ripgrep
    ];
    shellHook = ''
      # Share built Rocq and OCaml artifacts between worktrees through Dune's cache.
      export DUNE_CACHE=enabled
      # Hardlinks avoid copying every cached file into _build.
      export DUNE_CACHE_STORAGE_MODE=hardlink
      # One cache root for every Gaulois worktree, outside the repository.
      export DUNE_CACHE_ROOT="''${XDG_CACHE_HOME:-$HOME/.cache}/gaulois/dune"
      # A host library path would shadow the Nix store paths of the pinned toolchain.
      unset LD_LIBRARY_PATH
    '';
  };
}
