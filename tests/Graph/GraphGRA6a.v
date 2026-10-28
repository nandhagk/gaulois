(** * Interference and colouring examples

    These examples exercise move exclusion, checker acceptance and greedy colour selection.
    For example, a triangle spills one vertex with two colours and none with three colours.
    Builds on: GraphInterference, GraphColour, CollectionsEncoding, CollectionsMap,
    CollectionsFinSet. *)

From Stdlib Require Import List Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphInterference GraphColour.
Import List.ListNotations.

Definition empty_live_graph : interference nat :=
  add_point nat_encoding [0; 1] None FinSet.empty empty_interference.

Definition move_graph : interference nat :=
  add_point nat_encoding [0] (Some 1) (FinSet.of_list nat_encoding [0; 1; 2])
    empty_interference.

Definition path_graph : interference nat :=
  add_point nat_encoding [1] None (FinSet.of_list nat_encoding [2]) move_graph.

Definition triangle_graph : interference nat :=
  add_point nat_encoding [0; 1] None (FinSet.of_list nat_encoding [0; 1; 2])
    empty_interference.

Definition path_colouring : colour_result nat :=
  ColourResult (Map.of_list nat_encoding [(0, 0); (1, 0); (2, 1)]) [].

Example empty_live_adds_vertices_only :
  FinSet.mem nat_encoding 0 (vertices empty_live_graph) = true /\
  FinSet.mem nat_encoding 1 (vertices empty_live_graph) = true /\
  FinSet.is_empty (neighbours nat_encoding empty_live_graph 0) = true /\
  FinSet.is_empty (neighbours nat_encoding empty_live_graph 1) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example move_and_self_exclusion :
  FinSet.mem nat_encoding 0 (neighbours nat_encoding move_graph 0) = false /\
  FinSet.mem nat_encoding 1 (neighbours nat_encoding move_graph 0) = false /\
  FinSet.mem nat_encoding 2 (neighbours nat_encoding move_graph 0) = true /\
  FinSet.mem nat_encoding 0 (neighbours nat_encoding move_graph 2) = true /\
  FinSet.mem nat_encoding 1 (vertices move_graph) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example checker_accepts_path :
  check_colouring nat_encoding path_graph 2 Map.empty path_colouring = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example checker_rejects_equal_neighbours :
  check_colouring nat_encoding path_graph 2 Map.empty
    (ColourResult (Map.of_list nat_encoding [(0, 0); (1, 0); (2, 0)]) []) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example checker_rejects_missing_and_coloured_spills :
  check_colouring nat_encoding path_graph 2 Map.empty
    (ColourResult (Map.of_list nat_encoding [(0, 0); (1, 0)]) []) = false /\
  check_colouring nat_encoding path_graph 2 Map.empty
    (ColourResult (colours path_colouring) [2]) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example checker_checks_external_bindings_and_precolours :
  check_colouring nat_encoding path_graph 2 Map.empty
    (ColourResult (Map.set nat_encoding 9 2 (colours path_colouring)) []) = false /\
  check_colouring nat_encoding path_graph 2 (Map.set nat_encoding 9 1 Map.empty)
    path_colouring = false /\
  check_colouring nat_encoding path_graph 2 (Map.set nat_encoding 9 1 Map.empty)
    (ColourResult (Map.set nat_encoding 9 1 (colours path_colouring)) []) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example greedy_respects_move_preference :
  Map.get nat_encoding 0
    (colours (greedy_colour nat_encoding empty_live_graph 2
      (Map.set nat_encoding 1 1 Map.empty) [(0, 1)] [0; 1])) = Some 1 /\
  Map.get nat_encoding 0
    (colours (greedy_colour nat_encoding move_graph 3
      (Map.of_list nat_encoding [(1, 2); (2, 0)]) [(0, 1); (0, 2)] [0; 1; 2])) = Some 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example greedy_triangle_and_spill :
  check_colouring nat_encoding triangle_graph 2 Map.empty
    (greedy_colour nat_encoding triangle_graph 2 Map.empty [] [0; 1; 2; 2]) = true /\
  Map.get nat_encoding 2
    (colours (greedy_colour nat_encoding triangle_graph 2 Map.empty [] [0; 1; 2])) = None /\
  spilled (greedy_colour nat_encoding triangle_graph 3 Map.empty [] [0; 1; 2]) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example zero_palette_and_empty_graph :
  check_colouring nat_encoding path_graph 0 Map.empty
    (greedy_colour nat_encoding path_graph 0 Map.empty [] [0; 1; 2]) = true /\
  spilled (greedy_colour nat_encoding empty_interference 0 Map.empty [] []) = [] /\
  check_colouring nat_encoding path_graph 2 Map.empty
    (all_spilled nat_encoding path_graph Map.empty) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
