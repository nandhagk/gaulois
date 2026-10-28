(** * Lengauer--Tarjan parent-map examples

    Boolean map comparisons check every parent, including omitted roots and unreachable nodes.
    For example, a semidominator can defer to an earlier vertex whose parent is corrected later.
    Builds on: GraphLengauerTarjan, GraphSemiDominators and Collections maps. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators
  GraphLengauerTarjan.
Import List.ListNotations.

(** Edge identities preserve distinct parallel edges between the same pair of vertices. *)
Definition lt_test_graph (roots : list nat) (adjacency : nat -> list (nat * nat))
    : Graph.t nat (nat * (nat * nat)) :=
  {| Graph.entries := roots;
     Graph.nodes := [0; 1; 2; 3; 4; 5; 6];
     Graph.out := fun v => map (fun e => (v, e)) (adjacency v);
     Graph.source := fst;
     Graph.target := fun e => fst (snd e) |}.

Definition lt_test_bindings (g : Graph.t nat (nat * (nat * nat)))
    (expected : list (nat * nat)) : bool :=
  Map.beq Nat.eqb (simple_lt_idom (prepare nat_encoding g))
    (Map.of_list nat_encoding expected).

Example lt_empty_graph :
  lt_test_bindings
    {| Graph.entries := [];
       Graph.nodes := [];
       Graph.out := fun _ => [];
       Graph.source := fst;
       Graph.target := fun e => fst (snd e) |} [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition lt_test_chain : Graph.t nat (nat * (nat * nat)) :=
  lt_test_graph [0] (fun v => match v with
    | 0 => [(1, 0)]
    | 1 => [(2, 0)]
    | _ => []
    end).

Example lt_empty_entries : lt_test_bindings (set_entries lt_test_chain []) [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_chain_omits_root_and_unreachable :
  lt_test_bindings lt_test_chain [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition lt_test_diamond : Graph.t nat (nat * (nat * nat)) :=
  lt_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (2, 0)]
    | 1 => [(3, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | _ => []
    end).

Example lt_diamond :
  lt_test_bindings lt_test_diamond [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_multiple_entries_and_duplicate_entry :
  lt_test_bindings (set_entries lt_test_diamond [1; 2; 1]) [(4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_single_root : lt_test_bindings (lt_test_graph [0] (fun _ => [])) [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_self_loops :
  lt_test_bindings (lt_test_graph [0] (fun v => match v with
    | 0 => [(0, 0); (1, 0)]
    | 1 => [(1, 0); (2, 0)]
    | 2 => [(2, 0)]
    | _ => []
    end)) [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_parallel_edges :
  lt_test_bindings (lt_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (1, 1)]
    | 1 => [(2, 0); (2, 1)]
    | _ => []
    end)) [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Vertex 4 has semidominator 1, but paths through 2 and 3 make its immediate dominator 0. *)
Definition lt_test_correction : Graph.t nat (nat * (nat * nat)) :=
  lt_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (2, 0)]
    | 1 => [(3, 0); (4, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | _ => []
    end).

Example lt_deferred_parent_correction :
  lt_test_bindings lt_test_correction [(1, 0); (2, 0); (3, 0); (4, 0)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_bucket_defers_to_earlier_vertex :
  let p := prepare nat_encoding lt_test_correction in
  match Map.get (virtual_encoding nat_encoding) (inl 4)
    (lt_provisional (virtual_encoding nat_encoding) (virtual_graph nat_encoding lt_test_correction)
      (virtual_dfs p) (semidominators p)) with
  | Some (inl u) => Nat.eqb u 3
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example lt_semidominator_is_not_always_the_parent :
  let p := prepare nat_encoding lt_test_correction in
  match Map.get (virtual_encoding nat_encoding) (inl 4) (semidominators p),
        Map.get nat_encoding 4 (simple_lt_idom p) with
  | Some (inl s), Some d => Nat.eqb s 1 && Nat.eqb d 0
  | _, _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.
