open Core

(** Audits authored Rocq sources under the repository root, defaulting to the working directory.
    Claims are replayed using the pinned Rocq executable and built dependency load paths.
    Import hygiene requires the pinned Stdlib sources available through ROCQPATH.
    The [extraction] subcommand inspects the four generated artifacts supplied by Dune; its
    alias also requires successful compilation of the generated library. *)
val command : Command.t
