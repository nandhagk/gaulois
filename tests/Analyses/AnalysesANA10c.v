(** * Computed frontier MemorySSA graphs

    These examples inspect versions, ordered occurrence inputs and exact-edge operands.
    For example, an entry loop merges live-on-entry with its backedge definition.
    Builds on: AnalysesMemoryFrontier. *)

From Stdlib Require Import List Arith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier.
Import List.ListNotations.

Definition ana10c_diamond : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun n => match n with 0 => [0; 1] | 1 => [2] | 2 => [3] | _ => [] end;
     Graph.source := fun e => match e with 2 => 1 | 3 => 2 | _ => 0 end;
     Graph.target := fun e => match e with 0 => 1 | 1 => 2 | _ => 3 end |}.

Lemma ana10c_diamond_wf : graph_wf ana10c_diamond.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [Heq|Hfalse]; [subst n; left; reflexivity|contradiction].
  - intros n e Hedge; destruct n as [|[|[|n]]]; destruct e as [|[|[|[|e]]]];
      cbn in *; intuition congruence.
  - intros n e Hnode Hedge; destruct n as [|[|[|n]]]; destruct e as [|[|[|[|e]]]];
      cbn in *; intuition congruence.
Qed.

Definition ana10c_diamond_effects (e : nat) : list (memory_effect unit) :=
  match e with
  | 2 => [MemoryWrite MemoryAll]
  | 3 => [MemoryWrite MemoryAll]
  | _ => []
  end.

Definition ana10c_diamond_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_diamond
    ana10c_diamond_effects ana10c_diamond_wf).

Example ana10c_diamond_phis : memory_phis ana10c_diamond_memory = [3].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10c_diamond_versions : memory_versions ana10c_diamond_memory =
  [MemoryLive; MemoryPhi 3; MemoryDef 2 0; MemoryDef 3 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10c_diamond_operands :
  (memory_operand ana10c_diamond_memory 3 (Some 2),
   memory_operand ana10c_diamond_memory 3 (Some 3),
   memory_operand ana10c_diamond_memory 3 None,
   memory_in ana10c_diamond_memory 3) =
  (Some (MemoryDef 2 0), Some (MemoryDef 3 0), None, MemoryPhi 3).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_parallel : Graph.t nat nat :=
  {| Graph.entries := [0; 0];
     Graph.nodes := [0; 1];
     Graph.out := fun n => match n with 0 => [0; 0; 1] | _ => [] end;
     Graph.source := fun _ => 0;
     Graph.target := fun _ => 1 |}.

Lemma ana10c_parallel_wf : graph_wf ana10c_parallel.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [Heq|[Heq|Hfalse]];
      [subst n; left; reflexivity|subst n; left; reflexivity|contradiction].
  - intros n e Hedge; destruct n; [reflexivity|contradiction].
  - intros n e Hnode Hedge; right; left; reflexivity.
Qed.

Definition ana10c_parallel_effects (e : nat) : list (memory_effect unit) :=
  match e with
  | 0 => [MemoryWrite MemoryAll]
  | 1 => [MemoryReadWrite MemoryAll MemoryAll]
  | _ => []
  end.

Definition ana10c_parallel_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_parallel
    ana10c_parallel_effects ana10c_parallel_wf).

Example ana10c_parallel_identity :
  (Graph.out (memory_dom_graph nat_encoding nat_encoding ana10c_parallel) MemoryRoot,
   Graph.out (memory_dom_graph nat_encoding nat_encoding ana10c_parallel) (MemoryBlock 0),
   memory_phis ana10c_parallel_memory,
   memory_operand ana10c_parallel_memory 1 (Some 0),
   memory_operand ana10c_parallel_memory 1 (Some 1)) =
  ([MemoryStart 0], [MemoryBegin 0; MemoryBegin 1], [1],
   Some (MemoryDef 0 0), Some (MemoryDef 1 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10c_parallel_readwrite_prior :
  memory_before ana10c_parallel_memory 1 0 = Some MemoryLive.
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_entry_loop : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1] | _ => [] end;
     Graph.source := fun e => match e with 0 => 0 | _ => 1 end;
     Graph.target := fun e => match e with 0 => 1 | _ => 0 end |}.

Lemma ana10c_entry_loop_wf : graph_wf ana10c_entry_loop.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [Heq|Hfalse]; [subst n; left; reflexivity|contradiction].
  - intros n e Hedge; destruct n as [|[|n]]; destruct e as [|[|e]]; cbn in *; intuition congruence.
  - intros n e Hnode Hedge; destruct n as [|[|n]]; destruct e as [|[|e]];
      cbn in *; intuition congruence.
Qed.

Definition ana10c_entry_effects (e : nat) : list (memory_effect unit) :=
  match e with 1 => [MemoryWrite MemoryAll] | _ => [] end.

Definition ana10c_entry_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_entry_loop
    ana10c_entry_effects ana10c_entry_loop_wf).

Example ana10c_entry_backedge_operands :
  (memory_phis ana10c_entry_memory, memory_in ana10c_entry_memory 0,
   memory_operand ana10c_entry_memory 0 None,
   memory_operand ana10c_entry_memory 0 (Some 1),
   memory_before ana10c_entry_memory 1 0) =
  ([0], MemoryPhi 0, Some MemoryLive, Some (MemoryDef 1 0), Some (MemoryPhi 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_cycle : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun n => match n with 0 => [0] | 1 => [1; 2] | _ => [] end;
     Graph.source := fun e => match e with 0 => 0 | _ => 1 end;
     Graph.target := fun _ => 1 |}.

Lemma ana10c_cycle_wf : graph_wf ana10c_cycle.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [Heq|Hfalse]; [subst n; left; reflexivity|contradiction].
  - intros n e Hedge; destruct n as [|[|n]]; destruct e as [|[|[|e]]];
      cbn in *; intuition congruence.
  - intros n e Hnode Hedge; right; left; reflexivity.
Qed.

Definition ana10c_cycle_effects (e : nat) : list (memory_effect unit) :=
  match e with 2 => [MemoryWrite MemoryAll] | _ => [] end.

Definition ana10c_cycle_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_cycle
    ana10c_cycle_effects ana10c_cycle_wf).

Example ana10c_cyclic_phi :
  (memory_phis ana10c_cycle_memory,
   memory_operand ana10c_cycle_memory 1 (Some 0),
   memory_operand ana10c_cycle_memory 1 (Some 1),
   memory_operand ana10c_cycle_memory 1 (Some 2)) =
  ([1], Some MemoryLive, Some (MemoryPhi 1), Some (MemoryDef 2 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_linear : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun n => match n with 0 => [0] | _ => [] end;
     Graph.source := fun _ => 0;
     Graph.target := fun _ => 1 |}.

Lemma ana10c_linear_wf : graph_wf ana10c_linear.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n [Heq|Hfalse]; [subst n; left; reflexivity|contradiction].
  - intros n e Hedge; destruct n; [reflexivity|contradiction].
  - intros n e Hnode Hedge; right; left; reflexivity.
Qed.

Definition ana10c_ordered_effects (e : nat) : list (memory_effect unit) :=
  match e with
  | 0 => [MemoryRead MemoryAll; MemoryWrite MemoryAll; MemoryReadWrite MemoryAll MemoryAll;
      MemoryRead MemoryAll; MemoryBarrier; MemoryRead MemoryAll]
  | _ => []
  end.

Definition ana10c_ordered_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_linear
    ana10c_ordered_effects ana10c_linear_wf).

Example ana10c_multiple_ordered_inputs :
  map (memory_before ana10c_ordered_memory 0) [0; 1; 2; 3; 4; 5; 6] =
  [Some MemoryLive; Some MemoryLive; Some (MemoryDef 0 1); Some (MemoryDef 0 2);
   Some (MemoryDef 0 2); Some (MemoryDef 0 4); None].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10c_readwrite_uses_prior_version :
  memory_before ana10c_ordered_memory 0 2 = Some (MemoryDef 0 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10c_multiple_definitions_inventory :
  (memory_phis ana10c_ordered_memory, memory_versions ana10c_ordered_memory,
   memory_out ana10c_ordered_memory 0, memory_in ana10c_ordered_memory 1) =
  ([], [MemoryLive; MemoryDef 0 1; MemoryDef 0 2; MemoryDef 0 4], MemoryDef 0 4, MemoryDef 0 4).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_empty : Graph.t nat nat :=
  {| Graph.entries := [];
     Graph.nodes := [];
     Graph.out := fun _ => [];
     Graph.source := fun e => e;
     Graph.target := fun e => e |}.

Lemma ana10c_empty_wf : graph_wf ana10c_empty.
Proof.
  constructor; cbn; [constructor|intros n Hfalse|intros n e Hfalse|intros n e Hfalse];
    contradiction.
Qed.

Definition ana10c_empty_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_empty
    ana10c_ordered_effects ana10c_empty_wf).

Example ana10c_empty_graph :
  (memory_phis ana10c_empty_memory, memory_versions ana10c_empty_memory,
   memory_before ana10c_empty_memory 0 0, memory_operand ana10c_empty_memory 0 None) =
  ([], [MemoryLive], None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_two_entries := set_entries ana10c_diamond [0; 2].

Lemma ana10c_two_entries_wf : graph_wf ana10c_two_entries.
Proof.
  constructor.
  - exact (nodes_nodup ana10c_diamond_wf).
  - intros n [Heq|[Heq|Hfalse]]; subst; cbn; auto.
  - exact (out_source ana10c_diamond_wf).
  - exact (out_target_in ana10c_diamond_wf).
Qed.

Definition ana10c_two_entries_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_two_entries
    ana10c_diamond_effects ana10c_two_entries_wf).

Example ana10c_all_entries_live :
  (memory_in ana10c_two_entries_memory 0, memory_in ana10c_two_entries_memory 2,
   memory_phis ana10c_two_entries_memory,
   Graph.out (memory_dom_graph nat_encoding nat_encoding ana10c_two_entries) MemoryRoot) =
  (MemoryLive, MemoryLive, [3], [MemoryStart 0; MemoryStart 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_read_loop_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_entry_loop
    (fun _ => [MemoryRead (@MemoryAll unit)]) ana10c_entry_loop_wf).

Example ana10c_read_loop_needs_no_phi :
  (memory_phis ana10c_read_loop_memory, memory_versions ana10c_read_loop_memory,
   memory_before ana10c_read_loop_memory 1 0, memory_out ana10c_read_loop_memory 1) =
  ([], [MemoryLive], Some MemoryLive, MemoryLive).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10c_outside : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0];
     Graph.out := fun n => if Nat.eqb n 17 then [17] else [];
     Graph.source := fun e => e;
     Graph.target := fun e => S e |}.

Lemma ana10c_outside_wf : graph_wf ana10c_outside.
Proof.
  constructor.
  - constructor; [intro Hfalse; exact Hfalse|constructor].
  - intros n Hentry; exact Hentry.
  - intros n e Hedge; change (In e (if Nat.eqb n 17 then [17] else [])) in Hedge.
    destruct (Nat.eqb n 17) eqn:Hn; [|contradiction].
    apply Nat.eqb_eq in Hn; subst n; destruct Hedge as [Heq|Hfalse];
      [subst e; reflexivity|contradiction].
  - intros n e [Heq|Hfalse] Hedge; [subst n; contradiction|contradiction].
Qed.

Definition ana10c_outside_memory := proj1_sig
  (memory_frontier_build nat_encoding nat_encoding ana10c_outside
    (fun _ => [MemoryWrite (@MemoryAll unit)]) ana10c_outside_wf).

Example ana10c_unlisted_adjacency_is_empty :
  (Graph.out (memory_dom_graph nat_encoding nat_encoding ana10c_outside) (MemoryBlock 17),
   Graph.out (memory_dom_graph nat_encoding nat_encoding ana10c_outside) (MemoryEdge 17),
   memory_versions ana10c_outside_memory, memory_before ana10c_outside_memory 17 0) =
  ([], [], [MemoryLive], None).
Proof.
  vm_compute; reflexivity.
Qed.
