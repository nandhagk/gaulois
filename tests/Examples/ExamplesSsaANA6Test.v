(** * Checked SSA rewriting

    The compatibility pipeline extracts a strictly cheaper SSA term with a checked explanation.
    For example, multiplying the first 32-bit input by one returns that input.
    Builds on: AnalysesEgraph and ExamplesSsaAnalyses. *)

From Stdlib Require Import List NArith.
From Gaulois.Analyses Require Import AnalysesEgraph.
From Gaulois.Examples.Ssa Require Import ExamplesSsaAnalyses.
Import List.ListNotations.

(** Direct core saturation and legacy replay accept a nontrivial cheaper SSA result. *)
Example egraph_optimise_accepts :
  optimise sop_encoding mul_one_rules unit_cost 100%positive mul_one_term = Some (TVar 0).
Proof.
  vm_compute; reflexivity.
Qed.
