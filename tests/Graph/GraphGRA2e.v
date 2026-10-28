(** * Semi-NCA parent-map examples

    Boolean comparisons observe the complete parent map, including omitted roots and
    unreachable vertices.
    For example, a semidominator numbered before a DFS parent can require several parent visits.
    Builds on: GraphSemiNca, GraphSemiDominators and Collections maps. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators
  GraphSemiNca.
Import List.ListNotations.

(** The second edge component distinguishes parallel edges with the same endpoints. *)
Definition nca_test_graph (roots : list nat) (adjacency : nat -> list (nat * nat))
    : Graph.t nat (nat * (nat * nat)) :=
  {| Graph.entries := roots;
     Graph.nodes := [0; 1; 2; 3; 4; 5; 6; 7];
     Graph.out := fun v => map (fun e => (v, e)) (adjacency v);
     Graph.source := fst;
     Graph.target := fun e => fst (snd e) |}.

Definition nca_test_bindings (g : Graph.t nat (nat * (nat * nat)))
    (expected : list (nat * nat)) : bool :=
  Map.beq Nat.eqb (semi_nca_idom (prepare nat_encoding g))
    (Map.of_list nat_encoding expected).

Example nca_empty_graph :
  nca_test_bindings
    {| Graph.entries := [];
       Graph.nodes := [];
       Graph.out := fun _ => [];
       Graph.source := fst;
       Graph.target := fun e => fst (snd e) |} [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition nca_test_chain : Graph.t nat (nat * (nat * nat)) :=
  nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0)]
    | 1 => [(2, 0)]
    | _ => []
    end).

Example nca_empty_entries : nca_test_bindings (set_entries nca_test_chain []) [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_chain_omits_root : nca_test_bindings nca_test_chain [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition nca_test_diamond : Graph.t nat (nat * (nat * nat)) :=
  nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (2, 0)]
    | 1 => [(3, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | _ => []
    end).

Example nca_diamond :
  nca_test_bindings nca_test_diamond [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_multiple_entries_with_duplicate_entry :
  nca_test_bindings (set_entries nca_test_diamond [1; 2; 1]) [(4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_single_isolated_entry :
  nca_test_bindings (nca_test_graph [0] (fun _ => [])) [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_self_loops :
  nca_test_bindings (nca_test_graph [0] (fun v => match v with
    | 0 => [(0, 0); (1, 0)]
    | 1 => [(1, 0); (2, 0)]
    | 2 => [(2, 0)]
    | _ => []
    end)) [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_parallel_edges :
  nca_test_bindings (nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (1, 1)]
    | 1 => [(2, 0); (2, 1)]
    | _ => []
    end)) [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_unreachable_cycle :
  nca_test_bindings (nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0)]
    | 1 => [(2, 0)]
    | 6 => [(7, 0)]
    | 7 => [(6, 0)]
    | _ => []
    end)) [(1, 0); (2, 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The extra route through 2 makes 0 the parent of 4 although its semidominator is 1. *)
Definition nca_test_crossing : Graph.t nat (nat * (nat * nat)) :=
  nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (2, 0)]
    | 1 => [(3, 0); (4, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | _ => []
    end).

Example nca_crossing_paths :
  nca_test_bindings nca_test_crossing [(1, 0); (2, 0); (3, 0); (4, 0)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_semidominator_differs_from_parent :
  let p := prepare nat_encoding nca_test_crossing in
  match Map.get (virtual_encoding nat_encoding) (inl 4) (semidominators p),
        Map.get nat_encoding 4 (semi_nca_idom p) with
  | Some (inl s), Some a => Nat.eqb s 1 && Nat.eqb a 0
  | _, _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nca_walks_several_parents :
  nca_test_bindings (nca_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (5, 0)]
    | 1 => [(2, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | 5 => [(4, 0)]
    | _ => []
    end)) [(1, 0); (2, 1); (3, 2); (4, 0); (5, 0)] = true.
Proof.
  vm_compute; reflexivity.
Qed.
