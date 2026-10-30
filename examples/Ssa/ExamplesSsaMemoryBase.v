(** * SSA immutable-memory client

    The client applies historical byte framing to full-program SSA executions.
    For example, an integer byte outside every write summary retains its value across calls.
    Builds on: ExamplesSsaAnalyses, ExamplesSsaBytes and AnalysesMemoryBase. *)

From Stdlib Require Import List ZArith.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics.
From Gaulois.Analyses Require Import AnalysesMemoryBase.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping
  ExamplesSsaSemantics ExamplesSsaAnalyses ExamplesSsaBytes.

Section SsaAnalysisWrappers.
Context (ext : nat -> list cval -> option cval) (P : program) (lim : limits).
Local Abbreviation m := (ssa_semantics ext P lim).
Local Abbreviation bv := (ssa_bytes_view ext P lim).

(** Every existing SSA allocation byte outside all write summaries retains its observation. *)
Theorem ssa_immutable_sound (ty : vid) (o : Z) :
  wf_program ext P -> (forall n, covered (writes_at bv n) ty o 1 -> False) ->
  forall s tr t l, reachable_state m s -> exec m s tr t -> bsite bv s l = Some ty ->
    byte bv t l o = byte bv s l o.
Proof.
  intros Hwf Hwrites; apply (immutable_sound m bv ty o).
  - apply ssa_bytes_laws; exact Hwf.
  - exact Hwrites.
Qed.
End SsaAnalysisWrappers.
