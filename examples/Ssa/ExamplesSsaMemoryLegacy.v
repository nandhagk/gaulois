(** * Legacy MemorySSA chain fixtures

    Two stores to distinct sites precede a load from the first site.
    For example, changing the second store to a partial overlap invalidates the candidate.
    Builds on: ExamplesSsaAnalyses and AnalysesMemoryLegacy. *)

From Stdlib Require Import List ZArith.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Analyses Require Import AnalysesMemoryLegacy.
From Gaulois.Examples.Ssa Require Import ExamplesSsaAnalyses.
Import List.ListNotations.

(** The two edge identities leave nodes zero and one in a three-node chain. *)
Definition chain_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1] | _ => [] end;
     Graph.source := fun e => e;
     Graph.target := S |}.

(** The first two nodes write disjoint allocation sites. *)
Definition chain_writes : nat -> list (footprint nat) :=
  fun n => match n with
  | 0 => [Footprint 0 0%Z 8%Z]
  | 1 => [Footprint 1 0%Z 8%Z]
  | _ => []
  end.

(** The second write instead overlaps the upper half of the queried range. *)
Definition chain_writes_clobber : nat -> list (footprint nat) :=
  fun n => match n with
  | 0 => [Footprint 0 0%Z 8%Z]
  | 1 => [Footprint 0 4%Z 8%Z]
  | _ => []
  end.

(** Only the final node reads the eight bytes of site zero. *)
Definition chain_reads : nat -> list (footprint nat) :=
  fun n => match n with
  | 2 => [Footprint 0 0%Z 8%Z]
  | _ => []
  end.

(** The final load proposes the first node's memory definition in function zero. *)
Definition chain_ssa : memory_ssa nat nat :=
  MemorySSA (fun n => match n with 2 => Some (MDef 0 0) | _ => None end).
