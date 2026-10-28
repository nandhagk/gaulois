(** * Depth-first search examples

    These examples check traversal order, blocked vertices and path certificates.
    For example, a cycle from one to two and back to one has a retreating closing edge.
    Builds on: GraphCore, GraphPrepare, GraphDfs and GraphCertificate. *)

From Stdlib Require Import List Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphCertificate.
Import List.ListNotations.

Definition dfs_example_graph : Graph.t nat nat :=
  {| Graph.entries := [0; 3];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [10]
       | 1 => [11]
       | 2 => [12]
       | 3 => [13]
       | _ => []
       end;
     Graph.source := fun e => match e with
       | 10 => 0
       | 11 => 1
       | 12 => 2
       | _ => 3
       end;
     Graph.target := fun e => match e with
       | 10 => 1
       | 11 => 2
       | 12 => 1
       | _ => 2
       end |}.

Definition dfs_example_prepared := prepare nat_encoding dfs_example_graph.

Definition dfs_example_result := dfs dfs_example_prepared FinSet.empty [0; 3].

Definition dfs_empty_graph : Graph.t nat nat :=
  {| Graph.entries := [];
     Graph.nodes := [];
     Graph.out := fun _ => [];
     Graph.source := fun e => e;
     Graph.target := fun e => e |}.

Example dfs_empty_graph_search :
  preorder (dfs (prepare nat_encoding dfs_empty_graph) FinSet.empty []) = [] /\
  postorder (dfs (prepare nat_encoding dfs_empty_graph) FinSet.empty []) = [] /\
  FinSet.mem nat_encoding 0
    (visited (dfs (prepare nat_encoding dfs_empty_graph) FinSet.empty [])) = false.
Proof.
  vm_compute; auto.
Qed.

Example dfs_empty_roots : preorder (dfs dfs_example_prepared FinSet.empty []) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example dfs_multiple_roots_and_cycle :
  preorder dfs_example_result = [0; 1; 2; 3] /\
  postorder dfs_example_result = [2; 1; 0; 3] /\ rpo dfs_example_result = [3; 0; 1; 2].
Proof.
  vm_compute; auto.
Qed.

Example dfs_blocked_search :
  preorder (dfs dfs_example_prepared (FinSet.of_list nat_encoding [1]) [0; 3]) = [0; 3; 2] /\
  preorder (dfs dfs_example_prepared (FinSet.of_list nat_encoding [0; 3]) [0; 3]) = [].
Proof.
  vm_compute; auto.
Qed.

Example dfs_skipped_roots :
  preorder (dfs dfs_example_prepared FinSet.empty [0; 1; 0; 3; 3]) = [0; 1; 2; 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example dfs_positions_and_ancestry :
  Map.get nat_encoding 2 (tree_edge dfs_example_result) = Some 11 /\
  Map.get nat_encoding 2 (pre_num dfs_example_result) = Some 3%positive /\
  Map.get nat_encoding 2 (post_num dfs_example_result) = Some 1%positive /\
  ancestor_b nat_encoding dfs_example_result 1 2 = true /\
  ancestor_b nat_encoding dfs_example_result 3 2 = false.
Proof.
  vm_compute; auto.
Qed.

Example path_certificate_accepts :
  check_path dfs_example_prepared Nat.eqb 0 [10; 11; 12; 11] 2 = true /\
  check_path dfs_example_prepared Nat.eqb 3 [99] 2 = false /\
  check_path dfs_example_prepared Nat.eqb 0 [11] 2 = false /\
  check_path dfs_example_prepared Nat.eqb 0 [10] 2 = false.
Proof.
  vm_compute; auto.
Qed.

Example tree_certificate_recovers :
  tree_path dfs_example_prepared dfs_example_result 2 = Some (0, [10; 11]) /\
  tree_path dfs_example_prepared dfs_example_result 4 = None.
Proof.
  vm_compute; auto.
Qed.
