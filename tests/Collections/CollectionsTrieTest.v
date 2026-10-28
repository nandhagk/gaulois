(** * Canonical trie examples

    These examples check updates, canonical removal, ordered traversal and the
    structural checkers on overlapping and disjoint maps.

    For example, the seven keys 1 through 7 are listed as 4, 2, 6, 1, 5, 3, 7.
    Builds on: CollectionsTrie and Stdlib lists, booleans and binary integers. *)

From Stdlib Require Import ZArith List Bool.
From Gaulois.Collections Require Import CollectionsTrie.

Import List.ListNotations.

Definition trie_small : Trie.t nat :=
  Trie.set 1 10 (Trie.set 2 20 (Trie.set 3 30 Trie.empty)).

Definition trie_full : Trie.t nat :=
  Trie.set 4 40 (Trie.set 5 50 (Trie.set 6 60 (Trie.set 7 70 trie_small))).

Definition trie_overlap : Trie.t nat :=
  Trie.set 2 3 (Trie.set 3 4 (Trie.set 8 5 Trie.empty)).

Definition trie_disjoint : Trie.t nat := Trie.set 8 80 (Trie.set 13 130 Trie.empty).

Example trie_empty_observations :
  (Trie.is_empty (@Trie.empty nat), Trie.get 13 (@Trie.empty nat),
   Trie.elements (@Trie.empty nat), Trie.size (@Trie.empty nat)) = (true, None, [], 0).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_lookup_bits :
  List.map (fun p => Trie.get p trie_full) [1; 2; 3; 4; 5; 6; 7; 8]%positive =
  [Some 10; Some 20; Some 30; Some 40; Some 50; Some 60; Some 70; None].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_update_replaces :
  Trie.elements (Trie.set 2 99 trie_small) = [(2%positive, 99); (1%positive, 10); (3%positive, 30)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_update_deep_path :
  (Trie.get 13 (Trie.set 13 130 trie_full), Trie.get 5 (Trie.set 13 130 trie_full)) =
  (Some 130, Some 50).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_removal_collapses_paths :
  Trie.remove 13 (Trie.remove 8 trie_disjoint) = (@Trie.empty nat).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_removal_preserves_children :
  Trie.elements (Trie.remove 1 (Trie.remove 2 trie_full)) =
  [(4%positive, 40); (6%positive, 60); (5%positive, 50); (3%positive, 30); (7%positive, 70)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_remove_absent : Trie.remove 8 trie_small = trie_small.
Proof.
  vm_compute. reflexivity.
Qed.

(* Removing each subset of the three root-level bindings exercises all seven node shapes. *)
Example trie_seven_shapes :
  List.map (fun ps => Trie.elements (List.fold_left (fun tr p => Trie.remove p tr) ps trie_small))
    [[1; 2]; [2; 3]; [2]; [1; 3]; [1]; [3]; []; [1; 2; 3]]%positive =
  [[(3%positive, 30)]; [(1%positive, 10)]; [(1%positive, 10); (3%positive, 30)];
   [(2%positive, 20)]; [(2%positive, 20); (3%positive, 30)];
   [(2%positive, 20); (1%positive, 10)];
   [(2%positive, 20); (1%positive, 10); (3%positive, 30)]; []].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_traversal_order :
  Trie.elements trie_full =
  [(4%positive, 40); (2%positive, 20); (6%positive, 60); (1%positive, 10);
   (5%positive, 50); (3%positive, 30); (7%positive, 70)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_fold_order :
  Trie.fold (fun acc p _ => p :: acc) trie_full [] = [7; 3; 5; 1; 6; 2; 4]%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_fold_values : Trie.fold (fun n _ v => n + v) trie_full 5 = 285.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_size_counts_bindings : (Trie.size trie_full, Trie.size trie_disjoint) = (7, 2).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_map_values :
  Trie.elements (Trie.map S trie_small) = [(2%positive, 21); (1%positive, 11); (3%positive, 31)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_combine_overlap_and_filter :
  Trie.elements (Trie.combine (fun a b =>
    match a, b with
    | Some x, Some y => Some (x + y)
    | None, Some y => Some y
    | _, _ => None
    end) trie_small trie_overlap) = [(8%positive, 5); (2%positive, 23); (3%positive, 34)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_combine_disjoint :
  Trie.is_empty (Trie.combine (fun a b =>
    match a, b with
    | Some x, Some y => Some (x + y)
    | _, _ => None
    end)
    trie_full trie_disjoint) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_comparison_accepts_equal_bindings :
  Trie.beq Nat.eqb trie_small (Trie.set 3 30 (Trie.set 2 20 (Trie.set 1 10 Trie.empty))) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_comparison_rejects_value_and_support_changes :
  (Trie.beq Nat.eqb trie_small (Trie.set 1 11 trie_small),
   Trie.beq Nat.eqb trie_small trie_full,
   Trie.beq (fun _ _ => true) trie_full trie_small) = (false, false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Definition trie_value_le (a : nat) (ob : option nat) : bool :=
  match ob with
  | Some b => Nat.leb a b
  | None => false
  end.

Example trie_forall2_accepts_subset : Trie.forall2 trie_value_le trie_small trie_full = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_forall2_rejects_missing_or_smaller_values :
  (Trie.forall2 trie_value_le trie_full trie_small,
   Trie.forall2 trie_value_le trie_small trie_overlap) = (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_forall2_empty : Trie.forall2 trie_value_le Trie.empty trie_full = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_union_overlaps_in_argument_order :
  Trie.elements (Trie.union_with Nat.sub trie_small trie_overlap) =
  [(8%positive, 5); (2%positive, 17); (1%positive, 10); (3%positive, 26)].
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_union_disjoint :
  (Trie.get 13 (Trie.union_with Nat.add trie_full trie_disjoint),
   Trie.get 4 (Trie.union_with Nat.add trie_full trie_disjoint),
   Trie.size (Trie.union_with Nat.add trie_full trie_disjoint)) = (Some 130, Some 40, 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_union_empty_operands :
  (Trie.union_with Nat.add trie_full Trie.empty, Trie.union_with Nat.add Trie.empty trie_full) =
  (trie_full, trie_full).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_union_opt_cases :
  (Trie.union_opt Nat.sub (Some 9) (Some 2), Trie.union_opt Nat.sub (Some 9) None,
   Trie.union_opt Nat.sub None (Some 2), Trie.union_opt Nat.sub None None) =
  (Some 7, Some 9, Some 2, None).
Proof.
  vm_compute. reflexivity.
Qed.

Example trie_key_order_differs_from_numeric_order :
  Trie.key_lt 4 2 /\ Trie.key_lt 2 1 /\ Trie.key_lt 1 5 /\ ~ Trie.key_lt 3 2.
Proof.
  vm_compute. tauto.
Qed.
