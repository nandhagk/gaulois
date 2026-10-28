(** * Encoded map and finite-set examples

    These computation checks cover replacement, position access, comparisons and set algebra.
    For example, a repeated list binding replaces its earlier value without increasing size.
    Builds on: CollectionsEncoding, CollectionsTrie, CollectionsMap, CollectionsFinSet. *)

From Stdlib Require Import List Bool PArith Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
Import List.ListNotations.

Definition numbers : Map.t nat nat :=
  Map.of_list nat_encoding [(2, 20); (0, 10); (1, 30); (2, 99)].

Example empty_map_observations :
  (Map.get nat_encoding 0 (@Map.empty nat nat), Map.size (@Map.empty nat nat),
    Map.is_empty (@Map.empty nat nat), Map.mem nat_encoding 0 (@Map.empty nat nat)) =
  (None, 0, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example map_last_binding_wins :
  (Map.get nat_encoding 2 numbers, Map.get nat_encoding 4 numbers,
    Map.size numbers, Map.is_empty numbers, Map.mem nat_encoding 1 numbers) =
  (Some 99, None, 3, false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example map_elements_follow_code_order : Map.elements numbers = [(1, 30); (0, 10); (2, 99)].
Proof.
  vm_compute; reflexivity.
Qed.

Example map_fold_visits_each_binding :
  Map.fold (fun acc k v => (k, v) :: acc) numbers [] = [(2, 99); (0, 10); (1, 30)].
Proof.
  vm_compute; reflexivity.
Qed.

Example map_replacement_and_removal :
  (Map.get nat_encoding 0 (Map.set nat_encoding 0 50 numbers),
    Map.size (Map.set nat_encoding 0 50 numbers),
    Map.get nat_encoding 0 (Map.remove nat_encoding 0 numbers),
    Map.get nat_encoding 1 (Map.remove nat_encoding 0 numbers),
    Map.size (Map.remove nat_encoding 8 numbers)) = (Some 50, 3, None, Some 30, 3).
Proof.
  vm_compute; reflexivity.
Qed.

Example map_value_mapping :
  Map.elements (Map.map S numbers) = [(1, 31); (0, 11); (2, 100)].
Proof.
  vm_compute; reflexivity.
Qed.

Definition other_numbers : Map.t nat nat := Map.of_list nat_encoding [(1, 2); (3, 4)].

Definition add_options (a b : option nat) : option nat :=
  match a, b with
  | Some x, Some y => Some (x + y)
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.

Example map_combining :
  (Map.elements (Map.combine nat_encoding add_options numbers other_numbers),
    Map.elements (Map.union_with Nat.add numbers other_numbers)) =
  ([(3, 4); (1, 32); (0, 10); (2, 99)], [(3, 4); (1, 32); (0, 10); (2, 99)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example map_value_equality_accepts_and_rejects :
  (Map.beq Nat.eqb numbers (Map.of_list nat_encoding [(0, 10); (2, 99); (1, 30)]),
    Map.beq Nat.eqb numbers (Map.set nat_encoding 1 31 numbers),
    Map.beq Nat.eqb numbers (Map.remove nat_encoding 1 numbers)) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition value_le (v : nat) (o : option nat) : bool :=
  match o with
  | Some w => Nat.leb v w
  | None => false
  end.

Example map_forall2_accepts_and_rejects :
  (Map.forall2 value_le numbers (Map.map S numbers),
    Map.forall2 value_le numbers other_numbers,
    Map.forall2 value_le other_numbers numbers) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition misplaced_map : Map.t nat nat := Trie.set 2%positive (99, 7) Trie.empty.

Example malformed_map_reads_positions :
  (Map.get nat_encoding 1 misplaced_map, Map.get nat_encoding 99 misplaced_map,
    Map.code_get 2%positive misplaced_map, Map.elements misplaced_map) =
  (Some 7, None, Some 7, [(99, 7)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example malformed_map_combines_and_keeps_left_key :
  Map.elements (Map.combine nat_encoding add_options misplaced_map
    (Trie.set 2%positive (42, 9) Trie.empty)) = [(99, 16)] /\
  Map.elements (Map.union_with Nat.add misplaced_map
    (Trie.set 2%positive (42, 9) Trie.empty)) = [(99, 16)].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example combine_cannot_invent_an_absent_key :
  Map.is_empty (Map.combine nat_encoding (fun _ _ => Some 7)
    (@Map.empty nat nat) (@Map.empty nat nat)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition small_set : FinSet.t nat := FinSet.of_list nat_encoding [0; 1; 2; 1].
Definition second_set : FinSet.t nat := FinSet.of_list nat_encoding [1; 3].

Example empty_set_observations :
  (FinSet.mem nat_encoding 0 (@FinSet.empty nat), FinSet.is_empty (@FinSet.empty nat),
    FinSet.size (@FinSet.empty nat), FinSet.subset nat_encoding FinSet.empty small_set) =
  (false, true, 0, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example set_duplicates_and_membership :
  (FinSet.elements small_set, FinSet.size small_set,
    FinSet.mem nat_encoding 1 small_set, FinSet.mem nat_encoding 3 small_set,
    FinSet.is_empty small_set) = ([1; 0; 2], 3, true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example set_update_observations :
  (FinSet.elements (FinSet.add nat_encoding 1 small_set),
    FinSet.elements (FinSet.remove nat_encoding 1 small_set),
    FinSet.size (FinSet.add nat_encoding 3 small_set)) = ([1; 0; 2], [0; 2], 4).
Proof.
  vm_compute; reflexivity.
Qed.

Example set_union_intersection_difference :
  (FinSet.elements (FinSet.union nat_encoding small_set second_set),
    FinSet.elements (FinSet.inter nat_encoding small_set second_set),
    FinSet.elements (FinSet.diff nat_encoding small_set second_set)) =
  ([3; 1; 0; 2], [1], [0; 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example set_subset_accepts_and_rejects :
  (FinSet.subset nat_encoding (FinSet.inter nat_encoding small_set second_set) small_set,
    FinSet.subset nat_encoding small_set second_set,
    FinSet.subset nat_encoding second_set small_set) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example set_algebra_boundaries :
  (FinSet.elements (FinSet.union nat_encoding small_set small_set),
    FinSet.elements (FinSet.inter nat_encoding small_set FinSet.empty),
    FinSet.is_empty (FinSet.diff nat_encoding small_set small_set)) =
  ([1; 0; 2], [], true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition misplaced_set : FinSet.t nat := Trie.set 2%positive (99, tt) Trie.empty.
Definition same_position_set : FinSet.t nat := Trie.set 2%positive (42, tt) Trie.empty.

Example malformed_sets_use_positions :
  (FinSet.mem nat_encoding 1 misplaced_set, FinSet.mem nat_encoding 99 misplaced_set,
    FinSet.subset nat_encoding misplaced_set same_position_set,
    FinSet.elements (FinSet.union nat_encoding misplaced_set same_position_set),
    FinSet.elements (FinSet.inter nat_encoding misplaced_set same_position_set),
    FinSet.is_empty (FinSet.diff nat_encoding misplaced_set same_position_set)) =
  (true, false, true, [99], [99], true).
Proof.
  vm_compute; reflexivity.
Qed.
