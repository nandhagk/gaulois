(** * Optimistic colouring examples

    These computations exercise precolours, move bias, spills and complete simplification.
    For example, a four-vertex path needs no spill with two colours even when a poor greedy order
    would spill a vertex.
    Builds on: GraphInterference, GraphColour, GraphBriggs, CollectionsEncoding, CollectionsMap,
    CollectionsFinSet. *)

From Stdlib Require Import List Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphInterference GraphColour GraphBriggs.
Import List.ListNotations.

Definition briggs_path : interference nat :=
  add_point nat_encoding [2] None (FinSet.of_list nat_encoding [3])
    (add_point nat_encoding [1] None (FinSet.of_list nat_encoding [2])
      (add_point nat_encoding [0] None (FinSet.of_list nat_encoding [1]) empty_interference)).

Definition briggs_triangle : interference nat :=
  add_point nat_encoding [0; 1] None (FinSet.of_list nat_encoding [0; 1; 2]) empty_interference.

Definition briggs_star : interference nat :=
  add_point nat_encoding [0] None (FinSet.of_list nat_encoding [1; 2; 3; 4]) empty_interference.

Definition briggs_cycle : interference nat :=
  add_point nat_encoding [3] None (FinSet.of_list nat_encoding [0]) briggs_path.

Definition briggs_move_graph : interference nat :=
  add_point nat_encoding [0] (Some 1) (FinSet.of_list nat_encoding [1; 2]) empty_interference.

Example briggs_star_is_degenerate : degenerate nat_encoding briggs_star 2.
Proof.
  exists [1; 2; 3; 4; 0]; split.
  - repeat constructor; cbn; intuition congruence.
  - split.
    + intro v; rewrite <- (FinSet.elements_spec nat_encoding v (vertices briggs_star)).
      * vm_compute; intuition congruence.
      * unfold briggs_star, add_point; cbn [vertices empty_interference].
        repeat first [apply FinSet.wf_union | apply FinSet.wf_fold_add | apply Map.wf_empty].
    + intros prefix v suffix Heq.
      destruct prefix as [|a [|b [|c [|d [|e prefix]]]]];
        cbn in Heq; try solve [inversion Heq; subst; vm_compute; lia].
      pose proof (f_equal (@length nat) Heq) as Hlength.
      cbn in Hlength; rewrite length_app in Hlength; cbn in Hlength; lia.
Qed.

Example briggs_precoloured_graph :
  let pre := Map.set nat_encoding 1 1 Map.empty in
  let res := briggs_colour nat_encoding briggs_move_graph 3 pre [(0, 1)] in
  Map.get nat_encoding 1 (colours res) = Some 1 /\
  Map.get nat_encoding 0 (colours res) = Some 1 /\
  spilled res = [] /\
  check_colouring nat_encoding briggs_move_graph 3 pre res = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example briggs_actual_spill :
  let res := briggs_colour nat_encoding briggs_triangle 2 Map.empty [] in
  length (spilled res) = 1 /\
  check_colouring nat_encoding briggs_triangle 2 Map.empty res = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example briggs_optimistic_candidate_colours_successfully :
  let res := briggs_colour nat_encoding briggs_cycle 2 Map.empty [] in
  spilled res = [] /\
  check_colouring nat_encoding briggs_cycle 2 Map.empty res = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example briggs_degenerate_path_avoids_greedy_spill :
  length (spilled (greedy_colour nat_encoding briggs_path 2 Map.empty [] [0; 3; 1; 2])) = 1 /\
  spilled (briggs_colour nat_encoding briggs_path 2 Map.empty []) = [] /\
  check_colouring nat_encoding briggs_path 2 Map.empty
    (briggs_colour nat_encoding briggs_path 2 Map.empty []) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example briggs_degenerate_high_degree_star :
  FinSet.size (neighbours nat_encoding briggs_star 0) = 4 /\
  spilled (briggs_colour nat_encoding briggs_star 2 Map.empty [(1, 2); (3, 4)]) = [] /\
  check_colouring nat_encoding briggs_star 2 Map.empty
    (colour_checked nat_encoding briggs_star 2 Map.empty [(1, 2); (3, 4)]) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example briggs_zero_colours_and_empty_graph :
  length (spilled (briggs_colour nat_encoding briggs_path 0 Map.empty [])) = 4 /\
  check_colouring nat_encoding briggs_path 0 Map.empty
    (colour_checked nat_encoding briggs_path 0 Map.empty []) = true /\
  spilled (briggs_colour nat_encoding empty_interference 0 Map.empty []) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
