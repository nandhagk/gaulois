(** * Memory-domain boundary examples

    Computed fixtures distinguish exact objects, summary sites, byte gaps and must joins.
    For example, adjacent writes normalize to one footprint and a must join keeps their overlap.
    Builds on: DomainsAddress, DomainsPointsTo, DomainsByteRange and DomainsFootprint. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderLift.
From Gaulois.Domains Require Import DomainsInterval DomainsAddress DomainsPointsTo
  DomainsByteRange DomainsFootprint.
Import List.ListNotations.

Local Open Scope Z_scope.

Definition dom6_exact (s : positive) (o : Z) (n : nat) : address :=
  Address (Some s) (Itv (Fin o) (Fin o)) n.

Definition dom6_summary : address := Address None (Itv (Fin 0) (Fin 0)) 4.

Example dom6_cover_negative_start :
  covers (dom6_exact 1 (-4) 8) (dom6_exact 1 0 4) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_cover_moving_offsets :
  covers (dom6_exact 1 (-2) 12) (Address (Some 1%positive) (Itv (Fin 0) (Fin 6)) 4) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_cover_rejects_one_past :
  covers (dom6_exact 1 0 4) (dom6_exact 1 1 4) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_known_disjoint_objects :
  disjoint (dom6_exact 1 0 4) (dom6_exact 2 0 4) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_touching_accesses_are_disjoint :
  disjoint (dom6_exact 1 (-4) 4) (dom6_exact 1 0 3) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_nontrivial_overlap :
  may_overlap (dom6_exact 1 (-1) 4) (dom6_exact 1 0 2) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_summary_cannot_prove_same_object :
  (covers dom6_summary dom6_summary, disjoint dom6_summary dom6_summary) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_empty_offsets_are_disjoint :
  disjoint (Address None (Itv (Fin 7) (Fin 6)) 4) dom6_summary = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_size_arithmetic_is_unbounded_integer :
  covers (dom6_exact 1 (-9223372036854775808) 8)
    (dom6_exact 1 (-9223372036854775804) 4) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_zero_width_exact_cover : covers (dom6_exact 1 7 0) (dom6_exact 1 7 0) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_empty_offsets_keep_coverage_site_and_singleton_conditions :
  (covers (dom6_exact 1 0 4) (Address (Some 2%positive) IBot 2),
    covers (Address (Some 1%positive) (Itv (Fin 0) (Fin 1)) 4)
      (Address (Some 1%positive) IBot 2),
    covers (dom6_exact 1 0 4) (Address (Some 1%positive) (Itv PosInf PosInf) 100)) =
    (false, false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_singletons_may_and_must_alias :
  (pts_may_alias (pts_of_site 3) (pts_of_site 3),
    pts_must_alias (pts_of_site 3) (pts_of_site 3)) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_distinct_singletons_do_not_alias :
  (pts_may_alias (pts_of_site 2) (pts_of_site 3),
    pts_must_alias (pts_of_site 2) (pts_of_site 3)) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_unknown_may_but_not_must_alias :
  (pts_may_alias pts_unknown (pts_of_site 3), pts_must_alias pts_unknown pts_unknown) =
    (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_multiple_targets_are_not_must_aliases :
  pts_must_alias (join points_to_lattice (pts_of_site 1) (pts_of_site 2)) (pts_of_site 1) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_alias_queries_use_positions_of_raw_sets :
  pts_must_alias (Trie.set 1%positive (9%positive, tt) Trie.empty, false) (pts_of_site 1) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition dom6_ranges : byte_ranges := ranges_add (5, 8) (ranges_add (0, 2) ranges_empty).

Example dom6_ranges_canonical_order : proj1_sig dom6_ranges = [(0, 2); (5, 8)].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_adjacent_ranges_coalesce :
  proj1_sig (ranges_add (2, 5) dom6_ranges) = [(0, 8)].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_removal_splits_ranges :
  proj1_sig (ranges_remove (1, 6) dom6_ranges) = [(0, 1); (6, 8)].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_intersection_keeps_two_pieces :
  proj1_sig (ranges_inter dom6_ranges (ranges_single (1, 6))) = [(1, 2); (5, 6)].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_difference_skips_and_reuses_right_ranges :
  proj1_sig (ranges_diff (ranges_add (9, 12) dom6_ranges)
    (ranges_add (7, 10) (ranges_single ((-3), 1)))) = [(1, 2); (5, 7); (10, 12)].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_empty_and_inverted_additions :
  (proj1_sig (ranges_add (3, 3) dom6_ranges), proj1_sig (ranges_add (9, 4) dom6_ranges)) =
    (proj1_sig dom6_ranges, proj1_sig dom6_ranges).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_gap_rejects_coverage :
  (ranges_covers dom6_ranges (0, 8), ranges_intersects dom6_ranges (1, 6)) = (false, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_empty_query_boundaries :
  (ranges_covers ranges_empty (3, 3), ranges_covers ranges_empty (7, 2),
    ranges_intersects dom6_ranges (2, 5), ranges_intersects dom6_ranges (1, 1)) =
    (true, true, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_membership_respects_both_half_open_endpoints :
  map (ranges_mem dom6_ranges) [0; 1; 2; 5; 7; 8] = [true; true; false; true; true; false].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_range_inclusion_and_empty_difference :
  (ranges_subset dom6_ranges (ranges_single (0, 9)),
    ranges_is_empty (ranges_diff dom6_ranges dom6_ranges)) = (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Definition dom6_footprints : list (footprint positive) :=
  [Footprint 2%positive 8 10; Footprint 1%positive 2 4; Footprint 1%positive 0 2;
   Footprint 1%positive 7 7; Footprint 2%positive (-2) 0].

Example dom6_normalization_sorts_numeric_sites_and_merges_adjacency :
  footprints_normalise positive_encoding dom6_footprints =
    [Footprint 1%positive 0 4; Footprint 2%positive (-2) 0; Footprint 2%positive 8 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_normalization_uses_numeric_not_trie_order :
  footprints_normalise positive_encoding [Footprint 3%positive 0 1; Footprint 2%positive 0 1;
    Footprint 1%positive 0 1] =
    [Footprint 1%positive 0 1; Footprint 2%positive 0 1; Footprint 3%positive 0 1].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_footprint_intersection_is_per_site :
  footprints_inter positive_encoding dom6_footprints
    [Footprint 1%positive 1 3; Footprint 2%positive 9 12; Footprint 3%positive 0 100] =
    [Footprint 1%positive 1 3; Footprint 2%positive 9 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_footprint_difference_removes_only_matching_sites :
  footprints_diff positive_encoding dom6_footprints
    [Footprint 1%positive 1 3; Footprint 3%positive (-100) 100] =
    [Footprint 1%positive 0 1; Footprint 1%positive 3 4;
      Footprint 2%positive (-2) 0; Footprint 2%positive 8 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_must_order_is_reverse_byte_inclusion :
  (OrderLattice.leb (range_must_lattice positive_encoding)
     (range_reached positive_encoding [Footprint 1%positive 0 8])
     (range_reached positive_encoding [Footprint 1%positive 2 6]),
   OrderLattice.leb (range_must_lattice positive_encoding)
     (range_reached positive_encoding [Footprint 1%positive 2 6])
     (range_reached positive_encoding [Footprint 1%positive 0 8])) = (true, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_must_join_keeps_common_bytes :
  match join (range_must_lattice positive_encoding)
    (range_reached positive_encoding [Footprint 1%positive 0 6])
    (range_reached positive_encoding [Footprint 1%positive 2 8]) with
  | Unreached => []
  | Reached F => proj1_sig F
  end = [Footprint 1%positive 2 6].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_add_remove_keeps_unreached :
  (range_add positive_encoding dom6_footprints Unreached,
    range_remove positive_encoding dom6_footprints Unreached) = (Unreached, Unreached).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_reached_add_normalizes_adjacency :
  match range_add positive_encoding [Footprint 1%positive 2 5]
    (range_reached positive_encoding [Footprint 1%positive 0 2]) with
  | Unreached => []
  | Reached F => proj1_sig F
  end = [Footprint 1%positive 0 5].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_reached_remove_splits_footprints :
  match range_remove positive_encoding [Footprint 1%positive 1 3]
    (range_reached positive_encoding [Footprint 1%positive 0 4]) with
  | Unreached => []
  | Reached F => proj1_sig F
  end = [Footprint 1%positive 0 1; Footprint 1%positive 3 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_coverage_across_adjacent_raw_footprints : covered dom6_footprints 1%positive 0 4.
Proof.
  intros k Hk. apply (proj1 (footprint_index_written _ positive_encoding dom6_footprints _ k)).
  apply (proj1 (ranges_covers_spec
    (footprint_lookup positive_encoding (footprint_index positive_encoding dom6_footprints)
      1%positive) (0, 4))).
  - vm_compute. reflexivity.
  - exact Hk.
Qed.

Example dom6_reached_empty_differs_from_unreached :
  OrderLattice.leb (range_must_lattice positive_encoding)
    (range_reached positive_encoding []) Unreached = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom6_zero_width_access_is_covered :
  range_covers (range_reached positive_encoding []) 1%positive 17 0.
Proof.
  intros k Hk. cbn in Hk. lia.
Qed.

Example dom6_footprint_encoding_keeps_bounds :
  Pos.eqb (encode (footprint_encoding positive_encoding) (Footprint 1%positive (-2) 3))
    (encode (footprint_encoding positive_encoding) (Footprint 1%positive (-2) 4)) = false.
Proof.
  vm_compute. reflexivity.
Qed.
