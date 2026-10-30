(** * Computed legacy MemorySSA examples

    The same candidate accepts disjoint stores and rejects partial overlap.
    For example, the second store's range [4,8) invalidates the eight-byte load.
    Builds on: ExamplesSsaMemoryLegacy and AnalysesMemoryLegacy. *)

From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Analyses Require Import AnalysesMemoryLegacy.
From Gaulois.Examples.Ssa Require Import ExamplesSsaMemoryLegacy.

(** Distinct sites preserve the nontrivial first-store candidate. *)
Example memoryssa_accepts :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0
    chain_graph chain_writes chain_reads chain_ssa = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** A partially overlapping second store invalidates that same candidate. *)
Example memoryssa_rejects :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0
    chain_graph chain_writes_clobber chain_reads chain_ssa = false.
Proof.
  vm_compute; reflexivity.
Qed.
