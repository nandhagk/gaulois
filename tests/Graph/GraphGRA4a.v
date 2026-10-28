(** * Reducibility and natural-loop examples

    Computed cases distinguish nested loops, irreducible entries and stopped reverse searches.
    For example, an outer loop contains its inner loop but excludes the header's predecessor.
    Builds on: GraphReducible, GraphNaturalLoops and GraphDominators. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominators
  GraphReducible GraphNaturalLoops.
Import List.ListNotations.

Definition loop_test_graph (roots : list nat) (adjacency : nat -> list nat)
    : Graph.t nat (nat * nat) :=
  {| Graph.entries := roots;
     Graph.nodes := [0; 1; 2; 3; 4; 5; 6; 7; 8];
     Graph.out := fun v => map (fun w => (v, w)) (adjacency v);
     Graph.source := fst;
     Graph.target := snd |}.

Definition loop_test_nested : Graph.t nat (nat * nat) :=
  loop_test_graph [0] (fun v => match v with
  | 0 => [1]
  | 1 => [2; 5]
  | 2 => [3; 4]
  | 3 => [2; 4]
  | 4 => [1]
  | 5 => [6]
  | 6 => [5]
  | 7 => [8]
  | 8 => [7]
  | _ => []
  end).

Definition loop_test_irreducible : Graph.t nat (nat * nat) :=
  loop_test_graph [0] (fun v => match v with
  | 0 => [1; 2]
  | 1 => [3]
  | 2 => [3]
  | 3 => [1; 2; 4]
  | 4 => [4]
  | _ => []
  end).

Definition loop_test_check (g : Graph.t nat (nat * nat)) : bool :=
  let p := prepare nat_encoding g in reducible_b p (dominator_tree p).

Example reducible_nested_cycles : loop_test_check loop_test_nested = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_nested_cycles_semi_nca :
  let p := prepare nat_encoding loop_test_nested in
  reducible_b p (dominator_tree_with p SemiNCA) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example irreducible_two_entry_cycle : loop_test_check loop_test_irreducible = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example irreducible_extra_graph_entry :
  loop_test_check (set_entries loop_test_nested [0; 2]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_duplicate_entries :
  loop_test_check (set_entries loop_test_nested [0; 0]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducibility_ignores_unreachable_irreducibility :
  loop_test_check (set_entries loop_test_irreducible [4]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_no_entries :
  loop_test_check (set_entries loop_test_irreducible []) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_acyclic_diamond :
  loop_test_check (loop_test_graph [0] (fun v => match v with
  | 0 => [1; 2]
  | 1 => [3]
  | 2 => [3]
  | _ => []
  end)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_empty_graph :
  loop_test_check
    {| Graph.entries := [];
       Graph.nodes := [];
       Graph.out := fun _ => [];
       Graph.source := fst;
       Graph.target := snd |} = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_outer_loop_includes_inner_loop_and_header :
  natural_loop_nodes (prepare nat_encoding loop_test_nested) (4, 1) =
    FinSet.of_list nat_encoding [1; 2; 3; 4].
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_inner_loop_stops_at_header :
  natural_loop_nodes (prepare nat_encoding loop_test_nested) (3, 2) =
    FinSet.of_list nat_encoding [2; 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_separate_loop :
  natural_loop_nodes (prepare nat_encoding loop_test_nested) (6, 5) =
    FinSet.of_list nat_encoding [5; 6].
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_unreachable_loop :
  natural_loop_nodes (prepare nat_encoding loop_test_nested) (8, 7) =
    FinSet.of_list nat_encoding [7; 8].
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_self_loop_is_only_header :
  natural_loop_nodes (prepare nat_encoding loop_test_irreducible) (4, 4) =
    FinSet.of_list nat_encoding [4].
Proof.
  vm_compute; reflexivity.
Qed.

Example reducible_self_loop_at_entry :
  loop_test_check (loop_test_graph [0] (fun v => match v with
  | 0 => [0; 1]
  | _ => []
  end)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example natural_irreducible_edge_still_has_a_stopped_reverse_search :
  natural_loop_nodes (prepare nat_encoding loop_test_irreducible) (3, 1) =
    FinSet.of_list nat_encoding [0; 1; 2; 3].
Proof.
  vm_compute; reflexivity.
Qed.

(** Outside vertices may have edges into the finite graph, but have no prepared index entry. *)
Definition loop_test_outside : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1];
     Graph.out := fun v => map (fun w => (v, w)) (if Nat.eqb v 1 then [0] else [1]);
     Graph.source := fst;
     Graph.target := snd |}.

Example natural_loop_requires_the_queried_node_domain :
  ready nat_encoding loop_test_outside (prepare nat_encoding loop_test_outside) /\
  back_edge loop_test_outside (1, 0) /\
  natural_loop nat_encoding loop_test_outside (1, 0) 2 /\
  FinSet.mem nat_encoding 2
    (natural_loop_nodes (prepare nat_encoding loop_test_outside) (1, 0)) = false.
Proof.
  split.
  - apply prepare_ready; [constructor|].
    + cbn; constructor; [simpl; intuition discriminate|].
      constructor; [simpl; intuition|constructor].
    + intros v [Heq|Hin]; [subst v; cbn; auto|contradiction].
    + intros v e Hin; apply in_map_iff in Hin; destruct Hin as [w [Heq _]].
      subst e; reflexivity.
    + intros v e Hv Hin; apply in_map_iff in Hin; destruct Hin as [w [Heq Hin]].
      subst e; cbn in *; destruct (Nat.eqb v 1);
        destruct Hin as [Heq|Hin]; try contradiction; subst w; auto.
    + intro v; cbn; destruct (Nat.eqb v 1); cbn;
        constructor; [simpl; intuition|constructor|simpl; intuition|constructor].
  - split.
    + split; [vm_compute; auto|]; split.
      * apply (@reachable_step nat (nat * nat) loop_test_outside (0, 1)).
        -- constructor; cbn; auto.
        -- vm_compute; auto.
      * intros s es Hentry Hpath; left; cbn in Hentry.
        destruct Hentry as [Heq|Hin]; [subst s; reflexivity|contradiction].
    + split; [|vm_compute; reflexivity].
      right; exists [(2, 1)].
      refine (@path_cons nat (nat * nat)
        (without nat_encoding (FinSet.add nat_encoding 0 FinSet.empty) loop_test_outside)
        (2, 1) [] 1 _ _).
      * vm_compute; auto.
      * constructor.
Qed.
