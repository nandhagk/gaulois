(** * Dense finite-universe set examples

    These examples compute preparation, packed operations and finite-set conversions.
    For example, [7; 2; 7; 9; 2] prepares the ordered universe [7; 2; 9].
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet, CollectionsDenseSet. *)

From Stdlib Require Import List NArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet.

Import List.ListNotations.

Local Open Scope N_scope.

Definition col3_empty := dense_prepare N_encoding [].

Definition col3_universe := dense_prepare N_encoding [7; 2; 7; 9; 2].

Example col3_empty_preparation :
  dense_keys col3_empty = [] /\ dense_length col3_empty = 0 /\
  Map.get N_encoding 7 (dense_index col3_empty) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example col3_first_occurrences :
  dense_keys col3_universe = [7; 2; 9] /\ dense_length col3_universe = 3.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_exact_positions :
  List.map (fun k => Map.get N_encoding k (dense_index col3_universe)) [7; 2; 9; 42] =
    [Some 0; Some 1; Some 2; None].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_empty_membership :
  List.map (fun k => dense_mem N_encoding col3_universe k dense_empty) [7; 2; 9; 42] =
    [false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_sparse_membership :
  List.map (fun k => dense_mem N_encoding col3_universe k 5) [7; 2; 9; 42] =
    [true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_full_membership :
  List.map (fun k => dense_mem N_encoding col3_universe k 7) [7; 2; 9; 42] =
    [true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_high_bits_do_not_add_members :
  List.map (fun k => dense_mem N_encoding col3_universe k 129) [7; 2; 9; 42] =
    [true; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_empty_universe_ignores_raw_bits :
  dense_mem N_encoding col3_empty 7 255 = false /\
  dense_union col3_empty 255 127 = 0 /\
  dense_inter col3_empty 255 127 = 0 /\
  dense_diff col3_empty 255 127 = 0 /\
  dense_subset col3_empty 255 0 = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example col3_add_members :
  dense_add N_encoding col3_universe 2 5 = 7 /\
  dense_add N_encoding col3_universe 7 5 = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_add_masks_raw_bits :
  dense_add N_encoding col3_universe 2 129 = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_remove_members :
  dense_remove N_encoding col3_universe 2 7 = 5 /\
  dense_remove N_encoding col3_universe 2 5 = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_remove_masks_raw_bits :
  dense_remove N_encoding col3_universe 2 255 = 5.
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_outside_updates_leave_raw_input_unchanged :
  dense_add N_encoding col3_universe 42 129 = 129 /\
  dense_remove N_encoding col3_universe 42 129 = 129.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_union_sparse :
  dense_union col3_universe 1 4 = 5.
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_union_masks_raw_inputs :
  dense_union col3_universe 129 132 = 5 /\
  dense_union col3_universe 255 0 = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_intersection_masks_raw_inputs :
  dense_inter col3_universe 255 130 = 2 /\
  dense_inter col3_universe 128 128 = 0.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_difference_masks_raw_inputs :
  dense_diff col3_universe 255 130 = 5 /\
  dense_diff col3_universe 129 1 = 0.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_subset_checks_low_bits_only :
  dense_subset col3_universe 128 0 = true /\
  dense_subset col3_universe 129 0 = false /\
  dense_subset col3_universe 5 135 = true /\
  dense_subset col3_universe 7 5 = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example col3_conversion_enumerates_universe_order :
  dense_selected (dense_keys col3_universe) 133 = [7; 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_to_finset_sparse :
  dense_to_finset N_encoding col3_universe 133 = FinSet.of_list N_encoding [7; 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_to_finset_empty :
  dense_to_finset N_encoding col3_empty 255 = FinSet.empty /\
  dense_to_finset N_encoding col3_universe 128 = FinSet.empty.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_from_finset_restricts_outside_keys :
  dense_of_finset N_encoding col3_universe (FinSet.of_list N_encoding [42; 9; 7; 9]) = 5.
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_from_finset_full :
  dense_of_finset N_encoding col3_universe (FinSet.of_list N_encoding [9; 7; 2]) = 7 /\
  dense_of_finset N_encoding col3_empty (FinSet.of_list N_encoding [7]) = 0.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example col3_raw_roundtrip_drops_high_bits :
  dense_of_finset N_encoding col3_universe
    (dense_to_finset N_encoding col3_universe 133) = 5.
Proof.
  vm_compute; reflexivity.
Qed.

Example col3_singleton_boundary :
  dense_length (dense_prepare N_encoding [7; 7]) = 1 /\
  dense_union (dense_prepare N_encoding [7; 7]) 2 0 = 0 /\
  dense_union (dense_prepare N_encoding [7; 7]) 3 0 = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
