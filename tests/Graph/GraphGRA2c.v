(** * Shared semidominator examples

    Boolean binding comparisons exercise reverse-order settlement and compressed-path queries.
    For example, a path through later DFS vertices improves a node beyond its tree parent.
    Builds on: GraphSemiDominators and Collections encodings and maps. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominance GraphSemiDominators.
Import List.ListNotations.

(** Small adjacency fixtures keep edge identity separate from source and target. *)
Definition semi_test_graph (roots : list nat) (adjacency : nat -> list (nat * nat))
    : Graph.t nat (nat * (nat * nat)) :=
  {| Graph.entries := roots;
     Graph.nodes := [0; 1; 2; 3; 4; 5; 6];
     Graph.out := fun v => map (fun e => (v, e)) (adjacency v);
     Graph.source := fst;
     Graph.target := fun e => fst (snd e) |}.

Definition semi_test_vertex_eqb (u v : nat + unit) : bool :=
  match u, v with
  | inl x, inl y => Nat.eqb x y
  | inr _, inr _ => true
  | _, _ => false
  end.

(** Compare every binding, including any unexpected root or unreachable binding. *)
Definition semi_test_bindings (g : Graph.t nat (nat * (nat * nat)))
    (expected : list ((nat + unit) * (nat + unit))) : bool :=
  Map.beq semi_test_vertex_eqb (semidominators (prepare nat_encoding g))
    (Map.of_list (virtual_encoding nat_encoding) expected).

Definition semi_test_chain : Graph.t nat (nat * (nat * nat)) :=
  semi_test_graph [0] (fun v => match v with
    | 0 => [(1, 0)]
    | 1 => [(2, 0)]
    | _ => []
    end).

Example semi_empty_entries :
  semi_test_bindings (set_entries semi_test_chain []) [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example semi_chain_and_unreachable_omissions :
  semi_test_bindings semi_test_chain
    [(inl 0, inr tt); (inl 1, inl 0); (inl 2, inl 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition semi_test_diamond : Graph.t nat (nat * (nat * nat)) :=
  semi_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (2, 0)]
    | 1 => [(3, 0)]
    | 2 => [(3, 0)]
    | _ => []
    end).

Example semi_diamond :
  semi_test_bindings semi_test_diamond
    [(inl 0, inr tt); (inl 1, inl 0); (inl 2, inl 0); (inl 3, inl 0)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition semi_test_back_edges : Graph.t nat (nat * (nat * nat)) :=
  semi_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (3, 0)]
    | 1 => [(2, 0)]
    | 2 => [(3, 0)]
    | 3 => [(4, 0)]
    | 4 => [(2, 0); (1, 0)]
    | _ => []
    end).

Example semi_later_internal_path_and_reused_compression :
  semi_test_bindings semi_test_back_edges
    [(inl 0, inr tt); (inl 1, inl 0); (inl 2, inl 0);
     (inl 3, inl 0); (inl 4, inl 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example semi_self_loop :
  semi_test_bindings (semi_test_graph [0] (fun v => match v with
    | 0 => [(0, 0); (1, 0)]
    | 1 => [(1, 0)]
    | _ => []
    end)) [(inl 0, inr tt); (inl 1, inl 0)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example semi_multiple_entries :
  semi_test_bindings (set_entries semi_test_diamond [1; 2; 1])
    [(inl 1, inr tt); (inl 2, inr tt); (inl 3, inr tt)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example semi_parallel_edges :
  semi_test_bindings (semi_test_graph [0] (fun v => match v with
    | 0 => [(1, 0); (1, 1)]
    | 1 => [(2, 0); (2, 1)]
    | _ => []
    end)) [(inl 0, inr tt); (inl 1, inl 0); (inl 2, inl 1)] = true.
Proof.
  vm_compute; reflexivity.
Qed.
