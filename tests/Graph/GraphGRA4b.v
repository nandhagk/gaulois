(** * Loop nesting examples

    These examples distinguish recursive loops, irreducible entries and innermost ownership.
    For example, a three-level loop has three different headers and two immediate parents.
    Builds on: GraphLoops, GraphPrepare and Collections encodings, maps and sets. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphLoops.
Import List.ListNotations.

Definition gra4b_graph (roots : list nat) (adjacency : nat -> list nat)
    : Graph.t nat (nat * nat) :=
  Graph.Make roots [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]
    (fun v => map (fun w => (v, w)) (adjacency v)) fst snd.

Definition gra4b_nested : Graph.t nat (nat * nat) :=
  gra4b_graph [0] (fun v => match v with
  | 0 => [1; 6]
  | 1 => [2; 5]
  | 2 => [3; 1]
  | 3 => [4; 2]
  | 4 => [3]
  | 6 => [7]
  | 7 => [6]
  | 8 => [9]
  | 9 => [8]
  | _ => []
  end).

Definition gra4b_nested_prepared := prepare nat_encoding gra4b_nested.
Definition gra4b_nested_forest := loop_forest_of gra4b_nested_prepared.

Example gra4b_three_levels_outer_first :
  loop_headers gra4b_nested_forest = [1; 2; 3; 6].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4b_nested_members_include_descendants :
  Map.get nat_encoding 1 (loop_nodes gra4b_nested_forest) =
    Some (FinSet.of_list nat_encoding [1; 2; 3; 4]) /\
  Map.get nat_encoding 2 (loop_nodes gra4b_nested_forest) =
    Some (FinSet.of_list nat_encoding [2; 3; 4]) /\
  Map.get nat_encoding 3 (loop_nodes gra4b_nested_forest) =
    Some (FinSet.of_list nat_encoding [3; 4]).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_immediate_parents :
  map (fun h => Map.get nat_encoding h (loop_parent gra4b_nested_forest)) [1; 2; 3; 6] =
    [None; Some 1; Some 2; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4b_owners_are_innermost :
  map (fun v => Map.get nat_encoding v (loop_of gra4b_nested_forest))
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] =
    [None; Some 1; Some 2; Some 3; Some 3; None; Some 6; Some 6; None; None; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4b_disjoint_sibling_members :
  Map.get nat_encoding 6 (loop_nodes gra4b_nested_forest) =
    Some (FinSet.of_list nat_encoding [6; 7]) /\
  Map.get nat_encoding 5 (loop_nodes gra4b_nested_forest) = None /\
  Map.get nat_encoding 8 (loop_nodes gra4b_nested_forest) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_child_ambient_removes_only_immediate_header :
  outer_nodes gra4b_nested_prepared gra4b_nested_forest 2 =
    FinSet.of_list nat_encoding [2; 3; 4] /\
  outer_nodes gra4b_nested_prepared gra4b_nested_forest 3 =
    FinSet.of_list nat_encoding [3; 4] /\
  outer_nodes gra4b_nested_prepared gra4b_nested_forest 1 =
    FinSet.of_list nat_encoding [0; 1; 2; 3; 4; 5; 6; 7].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_duplicate_roots_preserve_all_queries :
  loop_forest_of (prepare nat_encoding (set_entries gra4b_nested [0; 0])) =
    gra4b_nested_forest.
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra4b_irreducible : Graph.t nat (nat * nat) :=
  gra4b_graph [0] (fun v => match v with
  | 0 => [1; 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => [1; 2; 4]
  | 4 => [4]
  | _ => []
  end).

Definition gra4b_irreducible_forest :=
  loop_forest_of (prepare nat_encoding gra4b_irreducible).

Example gra4b_irreducible_recursion :
  loop_headers gra4b_irreducible_forest = [4; 1; 3] /\
  Map.get nat_encoding 1 (loop_nodes gra4b_irreducible_forest) =
    Some (FinSet.of_list nat_encoding [1; 2; 3]) /\
  Map.get nat_encoding 3 (loop_nodes gra4b_irreducible_forest) =
    Some (FinSet.of_list nat_encoding [2; 3]) /\
  Map.get nat_encoding 3 (loop_parent gra4b_irreducible_forest) = Some 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_header_is_rpo_first_not_component_list_first :
  rpo (dfs (prepare nat_encoding gra4b_irreducible) FinSet.empty [0]) = [0; 1; 3; 4; 2] /\
  loop_choose nat_encoding
    (post_num (dfs (prepare nat_encoding gra4b_irreducible) FinSet.empty [0])) [3; 2; 1] = Some 1.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra4b_irreducible_inner_cycle_gets_its_own_header :
  map (fun v => Map.get nat_encoding v (loop_of gra4b_irreducible_forest)) [0; 1; 2; 3; 4] =
    [None; Some 1; Some 3; Some 3; Some 4] /\
  Map.get nat_encoding 4 (loop_parent gra4b_irreducible_forest) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra4b_multiple_graph_entries_change_the_outer_header :
  let f := loop_forest_of (prepare nat_encoding (set_entries gra4b_irreducible [2; 1])) in
  loop_headers f = [4; 2; 3] /\
  Map.get nat_encoding 3 (loop_parent f) = Some 2 /\
  Map.get nat_encoding 3 (loop_nodes f) = Some (FinSet.of_list nat_encoding [1; 3]) /\
  Map.get nat_encoding 1 (loop_of f) = Some 3.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_unreachable_irreducible_component_is_absent :
  let f := loop_forest_of (prepare nat_encoding (set_entries gra4b_irreducible [4])) in
  loop_headers f = [4] /\
  Map.get nat_encoding 1 (loop_nodes f) = None /\
  Map.get nat_encoding 2 (loop_of f) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_no_entries_produce_no_loops :
  loop_forest_of (prepare nat_encoding (set_entries gra4b_irreducible [])) =
    LoopForest [] Map.empty Map.empty Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4b_acyclic_diamond_has_no_loops :
  loop_headers (loop_forest_of (prepare nat_encoding
    (gra4b_graph [0] (fun v => match v with
    | 0 => [1; 2]
    | 1 => [3]
    | 2 => [3]
    | _ => []
    end)))) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4b_self_loop_at_graph_entry :
  let f := loop_forest_of (prepare nat_encoding
    (gra4b_graph [0] (fun v => match v with
    | 0 => [0; 1]
    | _ => []
    end))) in
  loop_headers f = [0] /\
  Map.get nat_encoding 0 (loop_nodes f) = Some (FinSet.of_list nat_encoding [0]) /\
  Map.get nat_encoding 0 (loop_of f) = Some 0 /\
  Map.get nat_encoding 1 (loop_of f) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra4b_empty_graph :
  loop_forest_of (prepare nat_encoding
    (Graph.Make [] [] (fun _ : nat => []) (@fst nat nat) (@snd nat nat))) =
    LoopForest [] Map.empty Map.empty Map.empty.
Proof.
  vm_compute; reflexivity.
Qed.
