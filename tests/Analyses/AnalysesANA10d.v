(** * Computed sealed-memory construction fixtures

    These observations exercise the actual indexed constructor on loops and parallel edges.
    For example, an entry backedge has separate live and defining incoming operands.
    Builds on: AnalysesMemorySealed, GraphCore and CollectionsEncoding. *)

From Stdlib Require Import List Bool Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemorySealed.
Import List.ListNotations.

Definition fixture_edge : Type := nat * (nat * nat).

Definition fixture_encoding : encoding fixture_edge :=
  pair_encoding nat_encoding (pair_encoding nat_encoding nat_encoding).

Definition fixture_cfg (count : nat) (entries : list nat) (edges : list fixture_edge) :
    Graph.t nat fixture_edge :=
  {| Graph.entries := entries;
     Graph.nodes := seq 0 count;
     Graph.out := fun n => filter (fun e => Nat.eqb (fst (snd e)) n) edges;
     Graph.source := fun e => fst (snd e);
     Graph.target := fun e => snd (snd e) |}.

Lemma fixture_cfg_wf count entries edges :
  forallb (fun n => n <? count) entries = true ->
  forallb (fun e => snd (snd e) <? count) edges = true ->
  graph_wf (fixture_cfg count entries edges).
Proof.
  intros Hentries Hedges; rewrite forallb_forall in Hentries, Hedges; constructor.
  - apply seq_NoDup.
  - intros n Hin; apply in_seq; split; [lia|].
    apply Nat.ltb_lt; apply Hentries; exact Hin.
  - intros n e Hedge; apply filter_In in Hedge; apply Nat.eqb_eq; exact (proj2 Hedge).
  - intros n e Hn Hedge; apply filter_In in Hedge; apply in_seq; split; [lia|].
    apply Nat.ltb_lt; apply Hedges; exact (proj1 Hedge).
Qed.

Definition loop_edge : fixture_edge := (0, (0, 0)).
Definition entry_loop := fixture_cfg 1 [0] [loop_edge].

Lemma entry_loop_wf : graph_wf entry_loop.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition loop_effects (_ : fixture_edge) : list (memory_effect unit) :=
  [MemoryReadWrite MemoryAll MemoryAll].

Definition entry_loop_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding entry_loop loop_effects entry_loop_wf).

Example entry_backedge_keeps_both_operands :
  (memory_operand entry_loop_memory 0 None,
    memory_operand entry_loop_memory 0 (Some loop_edge),
    memory_before entry_loop_memory loop_edge 0, memory_out entry_loop_memory loop_edge) =
  (Some MemoryLive, Some (MemoryDef loop_edge 0), Some (MemoryPhi 0), MemoryDef loop_edge 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example entry_placeholder_precedes_operand_completion :
  let ix := sealed_prepare nat_encoding fixture_encoding entry_loop in
  let first := sealed_indexed_step nat_encoding fixture_encoding entry_loop ix
    (sealed_plans fixture_encoding entry_loop loop_effects ix) (sealed_initial ix) in
  (FinSet.mem nat_encoding 0 (sealed_memo (sealed_data first)),
    FinSet.mem nat_encoding 0 (sealed_closed (sealed_data first)),
    Map.size (sealed_edge_index (sealed_data first)), sealed_stack first) =
  (true, false, 0, [(0, [None; Some loop_edge])]).
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_entry_loop_last_definition :
  (memory_last_path loop_effects [] : memory_version nat fixture_edge,
    memory_last_path loop_effects [loop_edge; loop_edge] : memory_version nat fixture_edge) =
  (MemoryLive, MemoryDef loop_edge 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ingress : fixture_edge := (0, (0, 1)).
Definition self_edge : fixture_edge := (1, (1, 1)).
Definition self_cfg := fixture_cfg 2 [0] [ingress; self_edge].

Lemma self_cfg_wf : graph_wf self_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition self_effects (e : fixture_edge) : list (memory_effect unit) :=
  if Nat.eqb (fst e) 1 then [MemoryWrite MemoryAll] else [].

Definition self_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding self_cfg self_effects self_cfg_wf).

Example nonentry_self_loop_has_no_virtual_operand :
  (memory_operand self_memory 1 None, memory_operand self_memory 1 (Some ingress),
    memory_operand self_memory 1 (Some self_edge), memory_before self_memory self_edge 0) =
  (None, Some (MemoryPhi 0), Some (MemoryDef self_edge 0), Some (MemoryPhi 1)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition to_body : fixture_edge := (1, (1, 2)).
Definition from_body : fixture_edge := (2, (2, 1)).
Definition multi_cfg := fixture_cfg 3 [0] [ingress; to_body; from_body].

Lemma multi_cfg_wf : graph_wf multi_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition multi_effects (e : fixture_edge) : list (memory_effect unit) :=
  match fst e with
  | 0 => []
  | 1 => [MemoryWrite MemoryAll]
  | _ => [MemoryBarrier]
  end.

Definition multi_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding multi_cfg multi_effects multi_cfg_wf).

Example multi_node_loop_completes_recursive_operands :
  (memory_operand multi_memory 1 (Some from_body),
    memory_operand multi_memory 2 (Some to_body), memory_before multi_memory from_body 0) =
  (Some (MemoryDef from_body 0), Some (MemoryDef to_body 0), Some (MemoryPhi 2)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition parallel_a : fixture_edge := (0, (0, 1)).
Definition parallel_b : fixture_edge := (1, (0, 1)).
Definition parallel_cfg := fixture_cfg 2 [0] [parallel_a; parallel_b].

Lemma parallel_cfg_wf : graph_wf parallel_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition ordered_effects (e : fixture_edge) : list (memory_effect unit) :=
  if Nat.eqb (fst e) 0 then
    [MemoryRead MemoryAll; MemoryWrite MemoryAll; MemoryRead MemoryAll;
      MemoryReadWrite MemoryAll MemoryAll; MemoryRead MemoryAll;
      MemoryCall MemoryAll MemoryAll; MemoryBarrier]
  else [MemoryWrite MemoryAll; MemoryRead MemoryAll].

Definition parallel_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding parallel_cfg ordered_effects parallel_cfg_wf).

Example parallel_identities_have_distinct_operands :
  (memory_operand parallel_memory 1 (Some parallel_a),
    memory_operand parallel_memory 1 (Some parallel_b),
    memory_operand parallel_memory 0 (Some parallel_a)) =
  (Some (MemoryDef parallel_a 6), Some (MemoryDef parallel_b 0), None).
Proof.
  vm_compute; reflexivity.
Qed.

Example ordered_reads_writes_calls_and_barriers :
  map (memory_before parallel_memory parallel_a) (seq 0 8) =
  [Some (MemoryPhi 0); Some (MemoryPhi 0); Some (MemoryDef parallel_a 1);
    Some (MemoryDef parallel_a 1); Some (MemoryDef parallel_a 3);
    Some (MemoryDef parallel_a 3); Some (MemoryDef parallel_a 5); None].
Proof.
  vm_compute; reflexivity.
Qed.

Definition duplicate_cfg := fixture_cfg 2 [0; 0]
  [parallel_a; parallel_a; parallel_b; parallel_b].

Lemma duplicate_cfg_wf : graph_wf duplicate_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition duplicate_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding duplicate_cfg ordered_effects
    duplicate_cfg_wf).

Example duplicate_listings_normalize_only_identical_edges :
  (memory_phis duplicate_memory, length (memory_versions duplicate_memory),
    memory_operand duplicate_memory 1 (Some parallel_a),
    memory_operand duplicate_memory 1 (Some parallel_b)) =
  ([1; 0], 8, Some (MemoryDef parallel_a 6), Some (MemoryDef parallel_b 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_work_is_completed_once :
  let ix := sealed_prepare nat_encoding fixture_encoding duplicate_cfg in
  let result := sealed_indexed_run nat_encoding fixture_encoding duplicate_cfg ordered_effects ix in
  (length (sealed_plan_edges fixture_encoding ix),
    Map.size (sealed_edge_index (sealed_data result)),
    FinSet.size (sealed_virtual (sealed_data result)),
    sealed_roots result, sealed_stack result) = (2, 2, 1, [], []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition left_ingress : fixture_edge := (0, (0, 2)).
Definition right_ingress : fixture_edge := (1, (1, 3)).
Definition left_to_right : fixture_edge := (2, (2, 3)).
Definition right_to_left : fixture_edge := (3, (3, 2)).
Definition irreducible_cfg := fixture_cfg 4 [0; 1]
  [left_ingress; right_ingress; left_to_right; right_to_left].

Lemma irreducible_cfg_wf : graph_wf irreducible_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition irreducible_effects (e : fixture_edge) : list (memory_effect unit) :=
  if fst e <? 2 then [] else [MemoryWrite MemoryAll].

Definition irreducible_memory := proj1_sig (memory_sealed_build nat_encoding fixture_encoding
  irreducible_cfg irreducible_effects irreducible_cfg_wf).

Example irreducible_multi_entry_scc_keeps_each_ingress :
  (memory_operand irreducible_memory 2 (Some left_ingress),
    memory_operand irreducible_memory 2 (Some right_to_left),
    memory_operand irreducible_memory 3 (Some right_ingress),
    memory_operand irreducible_memory 3 (Some left_to_right)) =
  (Some (MemoryPhi 0), Some (MemoryDef right_to_left 0),
    Some (MemoryPhi 1), Some (MemoryDef left_to_right 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Example multiple_entries_each_receive_live :
  (memory_operand irreducible_memory 0 None, memory_operand irreducible_memory 1 None,
    memory_operand irreducible_memory 2 None, memory_operand irreducible_memory 3 None) =
  (Some MemoryLive, Some MemoryLive, None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Definition reverse_entry : fixture_edge := (1, (1, 0)).
Definition cyclic_entries_cfg := fixture_cfg 2 [0; 1] [ingress; reverse_entry].

Lemma cyclic_entries_cfg_wf : graph_wf cyclic_entries_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition cyclic_entries_memory := proj1_sig (memory_sealed_build nat_encoding fixture_encoding
  cyclic_entries_cfg loop_effects cyclic_entries_cfg_wf).

Example backedges_into_every_entry_keep_live_operands :
  (memory_operand cyclic_entries_memory 0 None, memory_operand cyclic_entries_memory 1 None,
    memory_operand cyclic_entries_memory 0 (Some reverse_entry),
    memory_operand cyclic_entries_memory 1 (Some ingress)) =
  (Some MemoryLive, Some MemoryLive, Some (MemoryDef reverse_entry 0), Some (MemoryDef ingress 0)).
Proof.
  vm_compute; reflexivity.
Qed.

Definition no_effects (_ : fixture_edge) : list (memory_effect unit) := [].
Definition empty_cfg := fixture_cfg 0 [] [].

Lemma empty_cfg_wf : graph_wf empty_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition empty_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding empty_cfg no_effects empty_cfg_wf).

Example empty_graph_still_inventories_live :
  (memory_phis empty_memory, memory_versions empty_memory, memory_in empty_memory 99,
    memory_before empty_memory loop_edge 0, memory_operand empty_memory 99 None) =
  ([], [MemoryLive], MemoryLive, None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Definition next_edge : fixture_edge := (1, (1, 2)).
Definition unreachable_edge : fixture_edge := (2, (3, 3)).
Definition effectless_cfg := fixture_cfg 4 [0] [ingress; next_edge; unreachable_edge].

Lemma effectless_cfg_wf : graph_wf effectless_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition effectless_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding effectless_cfg no_effects effectless_cfg_wf).

Example no_effects_preserve_flow_and_exclude_unreachable_nodes :
  (memory_phis effectless_memory, length (memory_versions effectless_memory),
    memory_out effectless_memory ingress, memory_out effectless_memory next_edge,
    memory_before effectless_memory ingress 0, memory_operand effectless_memory 3 None,
    memory_operand effectless_memory 3 (Some unreachable_edge)) =
  ([1; 0; 2], 4, MemoryPhi 0, MemoryPhi 1, None, None, None).
Proof.
  vm_compute; reflexivity.
Qed.
