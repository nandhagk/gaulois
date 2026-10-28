(** * Finite order boundary examples

    Computed examples distinguish defaults, finite support, must intersection and disjunction caps.
    For example, a missing boolean key reads false with bottom-default and true with top-default.
    Builds on: CollectionsFinSet, OrderPowerset, OrderPointwise and OrderDisjunction. *)

From Stdlib Require Import List Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderPowerset OrderPointwise
  OrderDisjunction.

Import List.ListNotations.

Example finite_empty_universe :
  FinSet.size (proj1_sig (finite_clamp nat_encoding [] (FinSet.of_list nat_encoding [1; 2]))) = 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_nonempty_universe :
  FinSet.elements (proj1_sig (top_value (finite_powerset_top nat_encoding [0; 1; 2]))) =
  [1; 0; 2].
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_clamp_keeps_inside :
  let s := finite_clamp nat_encoding [1; 2] (FinSet.of_list nat_encoding [1; 3]) in
  (FinSet.mem nat_encoding 1 (proj1_sig s), FinSet.mem nat_encoding 3 (proj1_sig s)) =
  (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_must_intersection :
  let a := finite_clamp nat_encoding [1; 2; 3] (FinSet.of_list nat_encoding [1; 2]) in
  let b := finite_clamp nat_encoding [1; 2; 3] (FinSet.of_list nat_encoding [2; 3]) in
  FinSet.elements (proj1_sig (join (finite_must_lattice nat_encoding [1; 2; 3]) a b)) = [2].
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_must_comparison :
  let L := must_lattice nat_encoding in
  (leb L All (Only (FinSet.of_list nat_encoding [1])),
   leb L (Only (FinSet.of_list nat_encoding [1; 2])) (Only (FinSet.of_list nat_encoding [1])),
   leb L (Only FinSet.empty) All) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example raw_must_join :
  join (must_lattice nat_encoding) (Only (FinSet.of_list nat_encoding [1; 2]))
    (Only (FinSet.of_list nat_encoding [2; 3])) = Only (FinSet.of_list nat_encoding [2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example powerset_comparisons :
  let L := powerset_lattice nat_encoding in
  (leb L (FinSet.of_list nat_encoding [1]) (FinSet.of_list nat_encoding [1; 2]),
   leb L (FinSet.of_list nat_encoding [3]) (FinSet.of_list nat_encoding [1; 2])) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_powerset_comparison :
  let a := finite_clamp nat_encoding [1; 2] (FinSet.of_list nat_encoding [1]) in
  let b := top_value (finite_powerset_top nat_encoding [1; 2]) in
  (leb (finite_powerset_lattice nat_encoding [1; 2]) a b,
   leb (finite_must_lattice nat_encoding [1; 2]) a b) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example pointwise_bottom_default :
  let m := Map.set nat_encoding 1 true Map.empty in
  (pointwise_lookup nat_encoding false m 2,
   leb (pointwise_lattice nat_encoding bool_lattice) Map.empty m,
   leb (pointwise_lattice nat_encoding bool_lattice) m Map.empty) = (false, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example pointwise_top_default :
  let m := Map.set nat_encoding 1 false Map.empty in
  let L := pointwise_top_lattice nat_encoding bool_lattice bool_top in
  (pointwise_lookup nat_encoding true m 2,
   leb L (Some m) (Some Map.empty), leb L (Some Map.empty) (Some m),
   leb L None (Some m), leb L (Some m) None) = (true, true, false, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_map_clamp_boundary :
  let m := Map.of_list nat_encoding [(1, true); (3, false)] in
  let clamped := proj1_sig (finite_map_clamp nat_encoding [1; 2] m) in
  (Map.get nat_encoding 1 clamped, Map.get nat_encoding 2 clamped,
   Map.get nat_encoding 3 clamped) = (Some true, None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_map_defaults :
  let a := finite_map_clamp nat_encoding [1; 2] (Map.set nat_encoding 1 true Map.empty) in
  let b := finite_map_clamp nat_encoding [1; 2] Map.empty in
  (leb (finite_pointwise_lattice nat_encoding [1; 2] bool_lattice) a b,
   leb (finite_pointwise_top_lattice nat_encoding [1; 2] bool_lattice bool_top)
     (Some a) (Some b)) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example pointwise_raw_position :
  let malformed := Trie.set 1%positive (99, true) Map.empty in
  leb (pointwise_lattice nat_encoding bool_lattice) malformed
    (Map.set nat_encoding 0 true Map.empty) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_cap :
  join (disjunction_lattice 2 bool_lattice) [false; true] [false; true] = [false; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_zero_cap : join (disjunction_lattice 0 bool_lattice) [] [true] = [true].
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_comparison :
  (disjunction_leb bool_lattice [false; true] [true],
   disjunction_leb bool_lattice [true] [false]) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example disjunction_collapsing_widen :
  widen (disjunction_lattice 3 bool_lattice) [false] [true; false] = [true].
Proof.
  vm_compute; reflexivity.
Qed.
