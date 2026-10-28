(** * Dominator selector and boundary checker examples

    Boolean observations compare both backends, external parents and fallback intervals.
    For example, a checker rejects a branch as the parent of a diamond's join.
    Builds on: GraphDominators and Collections encodings and maps. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominators.
Import List.ListNotations.

Definition dom_test_graph (roots : list nat) (adjacency : nat -> list nat)
    : Graph.t nat (nat * nat) :=
  {| Graph.entries := roots;
     Graph.nodes := [0; 1; 2; 3; 4; 5; 6; 7];
     Graph.out := fun v => map (fun w => (v, w)) (adjacency v);
     Graph.source := fst;
     Graph.target := snd |}.

Definition dom_test_chain : Graph.t nat (nat * nat) :=
  dom_test_graph [0] (fun v => match v with
  | 0 => [1]
  | 1 => [2]
  | 2 => [3]
  | _ => []
  end).

Definition dom_test_diamond : Graph.t nat (nat * nat) :=
  dom_test_graph [0] (fun v => match v with
  | 0 => [1; 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => [4]
  | 6 => [7]
  | 7 => [6]
  | _ => []
  end).

Definition dom_test_parents (g : Graph.t nat (nat * nat)) (algorithm : dom_algorithm)
    (expected : list (nat * nat)) : bool :=
  Map.beq Nat.eqb (idom (dominator_tree_with (prepare nat_encoding g) algorithm))
    (Map.of_list nat_encoding expected).

Definition dom_test_check (g : Graph.t nat (nat * nat)) (parents : list (nat * nat)) : bool :=
  check_idom (prepare nat_encoding g) (Map.of_list nat_encoding parents).

Example dom_lt_chain :
  dom_test_parents dom_test_chain SimpleLT [(1, 0); (2, 1); (3, 2)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_nca_chain :
  dom_test_parents dom_test_chain SemiNCA [(1, 0); (2, 1); (3, 2)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_lt_diamond :
  dom_test_parents dom_test_diamond SimpleLT [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_nca_diamond :
  dom_test_parents dom_test_diamond SemiNCA [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_multi_entry_diamond_lt :
  dom_test_parents (set_entries dom_test_diamond [1; 2; 1]) SimpleLT [(4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_multi_entry_diamond_nca :
  dom_test_parents (set_entries dom_test_diamond [1; 2; 1]) SemiNCA [(4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_backend_intervals_agree :
  let p := prepare nat_encoding dom_test_diamond in
  let lt := dominator_tree_with p SimpleLT in
  let nca := dominator_tree_with p SemiNCA in
  Map.beq Pos.eqb (tin lt) (tin nca) && Map.beq Pos.eqb (tout lt) (tout nca) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_nested_interval_and_sibling :
  let t := dominator_tree (prepare nat_encoding dom_test_diamond) in
  dominates_b nat_encoding t 0 4 && dominates_b nat_encoding t 3 4 &&
  negb (dominates_b nat_encoding t 1 3) && negb (dominates_b nat_encoding t 4 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_unreachable_intervals_absent :
  let t := dominator_tree (prepare nat_encoding dom_test_diamond) in
  negb (Map.mem nat_encoding 6 (tin t)) &&
  negb (Map.mem nat_encoding 7 (tout t)) &&
  negb (dominates_b nat_encoding t 6 6) &&
  negb (dominates_b nat_encoding t 6 4) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_accepts_nontrivial_external_tree :
  dom_test_check dom_test_diamond [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_accepts_multi_entry_forest :
  dom_test_check (set_entries dom_test_diamond [1; 2; 1]) [(4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_accepts_nca :
  let p := prepare nat_encoding dom_test_diamond in
  check_idom p (idom (dominator_tree_with p SemiNCA)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_missing_parent :
  dom_test_check dom_test_chain [(1, 0); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_skipped_parent :
  dom_test_check dom_test_chain [(1, 0); (2, 0); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_wrong_diamond_parent :
  dom_test_check dom_test_diamond [(1, 0); (2, 0); (3, 1); (4, 3)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_self_parent :
  dom_test_check dom_test_chain [(0, 0); (1, 0); (2, 1); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_parent_cycle :
  dom_test_check dom_test_chain [(1, 2); (2, 1); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_unreachable_key :
  dom_test_check dom_test_chain [(1, 0); (2, 1); (3, 2); (6, 0)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_unreachable_parent :
  dom_test_check dom_test_chain [(1, 0); (2, 6); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_non_node_parent :
  dom_test_check dom_test_chain [(1, 0); (2, 99); (3, 2)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_empty_entries :
  let g := set_entries dom_test_chain [] in
  dom_test_parents g SimpleLT [] && dom_test_parents g SemiNCA [] &&
  dom_test_check g [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_empty_entries_rejects_binding :
  dom_test_check (set_entries dom_test_chain []) [(1, 0)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_default_boundary_query :
  dominator_exact (prepare nat_encoding dom_test_diamond) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_flat_single_entry_star :
  Map.beq Nat.eqb (flat_idom (prepare nat_encoding dom_test_chain))
    (Map.of_list nat_encoding [(1, 0); (2, 0); (3, 0)]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_flat_duplicate_single_entry_star :
  Map.beq Nat.eqb (flat_idom (prepare nat_encoding (set_entries dom_test_chain [0; 0])))
    (Map.of_list nat_encoding [(1, 0); (2, 0); (3, 0)]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_flat_multiple_entries :
  Map.is_empty (flat_idom (prepare nat_encoding (set_entries dom_test_diamond [1; 2]))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_flat_interval_is_conservative :
  let t := flat_tree (prepare nat_encoding dom_test_chain) in
  dominates_b nat_encoding t 0 3 && negb (dominates_b nat_encoding t 1 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_checker_rejects_imprecise_flat_tree :
  let p := prepare nat_encoding dom_test_chain in
  check_idom p (flat_idom p) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition dom_test_irreducible : Graph.t nat (nat * nat) :=
  dom_test_graph [0] (fun v => match v with
  | 0 => [1; 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => [1; 2; 4]
  | 4 => [4]
  | _ => []
  end).

Example dom_cycle_both_backends_and_checker :
  dom_test_parents dom_test_irreducible SimpleLT [(1, 0); (2, 0); (3, 0); (4, 3)] &&
  dom_test_parents dom_test_irreducible SemiNCA [(1, 0); (2, 0); (3, 0); (4, 3)] &&
  dom_test_check dom_test_irreducible [(1, 0); (2, 0); (3, 0); (4, 3)] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_empty_graph :
  let g : Graph.t nat (nat * nat) :=
    {| Graph.entries := [];
       Graph.nodes := [];
       Graph.out := fun _ => [];
       Graph.source := fst;
       Graph.target := snd |} in
  let p := prepare nat_encoding g in
  dom_test_parents g SimpleLT [] && dom_test_parents g SemiNCA [] &&
  dom_test_check g [] && Map.is_empty (tin (flat_tree p)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom_isolated_entry :
  let g := dom_test_graph [0] (fun _ => []) in
  let t := dominator_tree (prepare nat_encoding g) in
  dom_test_parents g SimpleLT [] && dom_test_parents g SemiNCA [] &&
  dom_test_check g [] && dominates_b nat_encoding t 0 0 = true.
Proof.
  vm_compute; reflexivity.
Qed.
