(** * Computed backward memory and legacy boundaries

    These fixtures exercise actual constructed version graphs and exact Boolean decisions.
    For example, a cyclic entry phi retains both its live operand and a conservative cycle cut.
    Builds on: AnalysesMemorySealed, AnalysesMemoryWalk and AnalysesMemoryLegacy. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemorySealed
  AnalysesMemoryWalk AnalysesMemoryLegacy.
From Gaulois.Examples.Ssa Require Import ExamplesSsaMemoryLegacy.
Import List.ListNotations.

Definition site_a : memory_scope nat := MemoryRegions [Footprint 0 0%Z 8%Z].
Definition site_b : memory_scope nat := MemoryRegions [Footprint 1 0%Z 8%Z].
Definition overlap_a : memory_scope nat := MemoryRegions [Footprint 0 4%Z 8%Z].

Definition walk_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun n => if Nat.ltb n 3 then [n] else [];
     Graph.source := fun e => e;
     Graph.target := S |}.

Lemma walk_graph_wf : graph_wf walk_graph.
Proof.
  constructor; cbn [walk_graph Graph.nodes Graph.entries Graph.out Graph.source Graph.target].
  - repeat constructor; cbn; intuition congruence.
  - intros n [->|Hfalse]; [left; reflexivity|contradiction].
  - intros n e Hin; destruct (Nat.ltb n 3); cbn in Hin;
      [destruct Hin as [->|Hfalse]; [reflexivity|contradiction]|contradiction].
  - intros n e Hn Hin; destruct n as [|[|[|n]]]; cbn in *;
      try (destruct Hin as [<-|Hfalse]; [cbn; auto|contradiction]).
    destruct Hn as [Hfalse|[Hfalse|[Hfalse|[Heq|Hfalse]]]];
      try discriminate; try contradiction; subst n; cbn in Hin; contradiction.
Qed.

Definition walk_effects (middle : memory_effect nat) (e : nat) : list (memory_effect nat) :=
  match e with
  | 0 => [MemoryWrite site_a]
  | 1 => [middle]
  | 2 => [MemoryRead site_a]
  | _ => []
  end.

Definition walk_versions (middle : memory_effect nat) : memory_graph nat nat :=
  proj1_sig (memory_sealed_build nat_encoding nat_encoding walk_graph
    (walk_effects middle) walk_graph_wf).

Definition walk_query (middle : memory_effect nat) (fuel : positive) :
    memory_clobber_result nat nat :=
  memory_clobbers nat_encoding nat_encoding nat_encoding walk_graph (walk_effects middle)
    (walk_versions middle) site_a (MemoryDef 1 0) fuel.

Example nonalias_walk :
  (clobber_roots (walk_query (MemoryWrite site_b) 8%positive),
   clobber_complete (walk_query (MemoryWrite site_b) 8%positive)) = ([MemoryDef 0 0], true).
Proof.
  vm_compute; reflexivity.
Qed.

Example frontier_backend_nonalias_walk :
  clobber_roots (memory_clobbers nat_encoding nat_encoding nat_encoding walk_graph
    (walk_effects (MemoryWrite site_b))
    (proj1_sig (memory_frontier_build nat_encoding nat_encoding walk_graph
      (walk_effects (MemoryWrite site_b)) walk_graph_wf)) site_a (MemoryDef 1 0) 8%positive) =
    [MemoryDef 0 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_overlap_walk :
  (clobber_roots (walk_query (MemoryWrite overlap_a) 8%positive),
   clobber_complete (walk_query (MemoryWrite overlap_a) 8%positive)) = ([MemoryDef 1 0], true).
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_call_walk :
  clobber_roots (walk_query (MemoryCall MemoryAll MemoryAll) 8%positive) = [MemoryDef 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example barrier_walk :
  clobber_roots (walk_query MemoryBarrier 8%positive) = [MemoryDef 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example all_memory_is_never_disjoint :
  (memory_scopes_disjoint nat_encoding MemoryAll (MemoryRegions []),
   memory_scopes_disjoint nat_encoding (MemoryRegions []) MemoryAll) = (false, false).
Proof.
  reflexivity.
Qed.

Example fuel_exhaustion_retains_frontier :
  (clobber_roots (walk_query (MemoryWrite site_b) 1%positive),
   clobber_complete (walk_query (MemoryWrite site_b) 1%positive)) = ([MemoryPhi 1], false).
Proof.
  vm_compute; reflexivity.
Qed.

Example actual_ordered_inputs :
  (memory_before (walk_versions (MemoryWrite site_b)) 0 0,
   memory_before (walk_versions (MemoryWrite site_b)) 1 0,
   memory_before (walk_versions (MemoryWrite site_b)) 2 0) =
  (Some (MemoryPhi 0), Some (MemoryPhi 1), Some (MemoryPhi 2)).
Proof.
  vm_compute; reflexivity.
Qed.

Example chain_dynamic_origins :
  (memory_last_path (walk_effects (MemoryWrite site_b)) [0; 1] : memory_version nat nat,
   memory_path_last_clobber nat_encoding site_a (walk_effects (MemoryWrite site_b)) [0; 1]
     : memory_version nat nat) = (MemoryDef 1 0, MemoryDef 0 0).
Proof.
  reflexivity.
Qed.

Definition project_chain (writes : nat -> list (footprint nat)) : memory_ssa nat nat :=
  project_memory_legacy nat_encoding nat_encoding nat_encoding nat_encoding 0 walk_graph
    (walk_effects (MemoryWrite site_b)) writes chain_reads (walk_versions (MemoryWrite site_b))
    (fun n => match n with 2 => Some (2, 0) | _ => None end) 16%positive.

Example nonempty_accepted_projection :
  (def_of_load (project_chain chain_writes) 2,
   no_clobber_check nat_encoding nat_encoding nat_encoding 0 walk_graph chain_writes chain_reads
     (project_chain chain_writes)) = (Some (MDef 0 0), true).
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_still_requires_legacy_clearance :
  (clobber_roots (walk_query (MemoryWrite site_b) 16%positive),
   def_of_load (project_chain chain_writes_clobber) 2) = ([MemoryDef 0 0], None).
Proof.
  vm_compute; reflexivity.
Qed.

Example load_node_write_rejects :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 chain_graph
    (fun n => if Nat.eqb n 2 then [Footprint 0 0%Z 1%Z] else chain_writes n)
    chain_reads chain_ssa = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition revisit_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1; 2] | _ => [] end;
     Graph.source := fun e => match e with 0 => 0 | _ => 1 end;
     Graph.target := fun e => match e with 0 => 1 | 1 => 0 | _ => 2 end |}.

Example revisiting_definition_rejects :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 revisit_graph
    chain_writes chain_reads chain_ssa = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition self_graph : Graph.t nat nat :=
  {| Graph.entries := [0]; Graph.nodes := [0; 1];
     Graph.out := fun n => match n with 0 => [0; 1] | _ => [] end;
     Graph.source := fun _ => 0;
     Graph.target := fun e => match e with 0 => 0 | _ => 1 end |}.

Example definition_self_loop_rejects :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 self_graph
    chain_writes (fun _ => [Footprint 0 0%Z 1%Z])
    (MemorySSA (fun n => if Nat.eqb n 1 then Some (MDef 0 0) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_and_reversed_ranges :
  (legacy_disjoint_b nat_encoding [Footprint 0 4%Z 4%Z] [Footprint 0 0%Z 8%Z],
   legacy_disjoint_b nat_encoding [Footprint 0 6%Z 4%Z] [Footprint 0 0%Z 8%Z],
   legacy_disjoint_b nat_encoding [Footprint 0 0%Z 8%Z] [Footprint 0 6%Z 4%Z]) =
  (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition unreachable_graph : Graph.t nat nat :=
  {| Graph.entries := [0]; Graph.nodes := [0; 1]; Graph.out := fun _ => [];
     Graph.source := fun _ => 0; Graph.target := fun _ => 0 |}.

Example unreachable_load_rejected :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 unreachable_graph
    (fun _ => []) (fun _ => [])
    (MemorySSA (fun n => if Nat.eqb n 1 then Some (MLive 0) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unreachable_definition_rejected :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 unreachable_graph
    (fun _ => []) (fun _ => [])
    (MemorySSA (fun n => if Nat.eqb n 0 then Some (MDef 0 1) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example nonnode_definition_rejected :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 chain_graph
    chain_writes chain_reads
    (MemorySSA (fun n => if Nat.eqb n 2 then Some (MDef 0 99) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition multiple_entries : Graph.t nat nat :=
  {| Graph.entries := [0; 1]; Graph.nodes := [0; 1; 2];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1] | _ => [] end;
     Graph.source := fun e => e; Graph.target := fun _ => 2 |}.

Example all_entries_are_checked :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 multiple_entries
    (fun n => if Nat.eqb n 1 then [Footprint 0 0%Z 1%Z] else []) chain_reads
    (MemorySSA (fun n => if Nat.eqb n 2 then Some (MLive 0) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition cyclic_phi_graph : Graph.t nat nat :=
  {| Graph.entries := [0]; Graph.nodes := [0];
     Graph.out := fun n => if Nat.eqb n 0 then [0] else [];
     Graph.source := fun _ => 0; Graph.target := fun _ => 0 |}.

Lemma cyclic_phi_graph_wf : graph_wf cyclic_phi_graph.
Proof.
  constructor; cbn [cyclic_phi_graph Graph.nodes Graph.entries Graph.out Graph.source Graph.target].
  - repeat constructor; cbn; tauto.
  - intros n [->|Hfalse]; [left; reflexivity|contradiction].
  - intros n e Hin; destruct n; cbn in Hin; [destruct Hin as [<-|Hfalse]|];
      try contradiction; reflexivity.
  - intros n e Hin Hedge; left; reflexivity.
Qed.

Definition cyclic_phi_versions : memory_graph nat nat :=
  proj1_sig (memory_sealed_build nat_encoding nat_encoding cyclic_phi_graph
    (fun _ => [MemoryRead site_a]) cyclic_phi_graph_wf).

Definition cyclic_phi_result : memory_clobber_result nat nat :=
  memory_clobbers nat_encoding nat_encoding nat_encoding cyclic_phi_graph
    (fun _ => [MemoryRead site_a]) cyclic_phi_versions site_a (MemoryPhi 0) 16%positive.

Example cyclic_phi_retains_cut :
  (memory_in cyclic_phi_versions 0, memory_operand cyclic_phi_versions 0 None,
   memory_operand cyclic_phi_versions 0 (Some 0), clobber_roots cyclic_phi_result,
   clobber_complete cyclic_phi_result) =
  (MemoryPhi 0, Some MemoryLive, Some (MemoryPhi 0), [MemoryPhi 0; MemoryLive], false).
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_phi_history_keeps_live_origin :
  (memory_last_path (fun _ : nat => [MemoryRead site_a]) [0; 0; 0] : memory_version nat nat,
   memory_path_last_clobber nat_encoding site_a (fun _ : nat => [MemoryRead site_a]) [0; 0; 0]
     : memory_version nat nat) = (MemoryLive, MemoryLive).
Proof.
  reflexivity.
Qed.

Definition parallel_graph : Graph.t nat nat :=
  {| Graph.entries := [0]; Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1; 2] | 2 => [3] | _ => [] end;
     Graph.source := fun e => match e with 0 => 0 | 3 => 2 | _ => 1 end;
     Graph.target := fun e => match e with 0 => 1 | 3 => 3 | _ => 2 end |}.

Lemma parallel_graph_wf : graph_wf parallel_graph.
Proof.
  constructor; cbn [parallel_graph Graph.nodes Graph.entries Graph.out Graph.source Graph.target].
  - repeat constructor; cbn; intuition congruence.
  - intros n [->|Hfalse]; [left; reflexivity|contradiction].
  - intros n e Hin; destruct n as [|[|[|n]]]; cbn in Hin; try contradiction;
      destruct Hin as [Heq|Hin]; [subst e; reflexivity| |subst e; reflexivity| |
        subst e; reflexivity|contradiction]; try contradiction.
    destruct Hin as [Heq|Hfalse]; [subst e; reflexivity|contradiction].
  - intros n e Hn Hin; destruct n as [|[|[|n]]]; cbn in Hin; try contradiction;
      destruct Hin as [Heq|Hin]; [subst e; cbn; auto| |subst e; cbn; auto| |
        subst e; cbn; auto|contradiction]; try contradiction.
    destruct Hin as [Heq|Hfalse]; [subst e; cbn; auto|contradiction].
Qed.

Definition parallel_effects (e : nat) : list (memory_effect nat) :=
  match e with
  | 0 => [MemoryWrite site_a]
  | 1 => [MemoryWrite site_b]
  | 2 => [MemoryWrite overlap_a]
  | 3 => [MemoryRead site_a]
  | _ => []
  end.

Definition parallel_versions : memory_graph nat nat :=
  proj1_sig (memory_sealed_build nat_encoding nat_encoding parallel_graph parallel_effects
    parallel_graph_wf).

Definition parallel_projection : memory_ssa nat nat :=
  project_memory_legacy nat_encoding nat_encoding nat_encoding nat_encoding 0 parallel_graph
    parallel_effects chain_writes_clobber chain_reads parallel_versions
    (fun n => if Nat.eqb n 2 then Some (3, 0) else None) 32%positive.

Example parallel_clobber_invalidates_projection :
  (existsb (fun v => match v with MemoryDef 2 0 => true | _ => false end)
     (clobber_roots (memory_clobbers nat_encoding nat_encoding nat_encoding parallel_graph
       parallel_effects parallel_versions site_a (memory_in parallel_versions 2) 32%positive)),
   def_of_load parallel_projection 2,
   no_clobber_check nat_encoding nat_encoding nat_encoding 0 parallel_graph
     chain_writes_clobber chain_reads chain_ssa) = (true, None, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example invalid_occurrences_propose_nothing :
  (def_of_load (project_memory_legacy nat_encoding nat_encoding nat_encoding nat_encoding 0
    walk_graph (walk_effects (MemoryWrite site_b)) chain_writes chain_reads
    (walk_versions (MemoryWrite site_b)) (fun _ => Some (1, 0)) 16%positive) 2,
   def_of_load (project_memory_legacy nat_encoding nat_encoding nat_encoding nat_encoding 0
    walk_graph (walk_effects (MemoryWrite site_b)) chain_writes chain_reads
    (walk_versions (MemoryWrite site_b)) (fun _ => Some (2, 1)) 16%positive) 2) = (None, None).
Proof.
  vm_compute; reflexivity.
Qed.
