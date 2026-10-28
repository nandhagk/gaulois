(** * Edge and post-dominance examples

    Small graphs exercise indexed edge queries and reverse dominator trees.
    For example, a self-loop is excluded while a unique incoming edge is collected.
    Builds on: GraphEdgeDominance and GraphPostDominators. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominators
  GraphEdgeDominance GraphPostDominators.
Import List.ListNotations.

Definition edge_test_graph : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [(0, 1)]
       | 1 => [(1, 1); (1, 2); (1, 3)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example edge_unique_and_loop :
  let p := prepare nat_encoding edge_test_graph in
  let t := dominator_tree p in
  Map.get nat_encoding 1 (edge_dom_index p t) = Some (0, 1) /\
  dominating_edges p t (edge_dom_index p t) 2 = [(0, 1); (1, 2)].
Proof.
  vm_compute; auto.
Qed.

Definition edge_test_diamond : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [(0, 1); (0, 2)]
       | 1 => [(1, 3)]
       | 2 => [(2, 3)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example edge_multiple_incoming :
  let p := prepare nat_encoding edge_test_diamond in
  let t := dominator_tree p in
  Map.get nat_encoding 3 (edge_dom_index p t) = None /\
  dominating_edges p t (edge_dom_index p t) 3 = [].
Proof.
  vm_compute; auto.
Qed.

Example post_multiple_exits :
  let p := prepare nat_encoding edge_test_graph in
  let t := post_dominator_tree p [2; 3] in
  dominates_b nat_encoding t 1 0 && negb (dominates_b nat_encoding t 2 1) &&
  negb (dominates_b nat_encoding t 3 1) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example edge_and_post_checker_accept :
  let p := prepare nat_encoding edge_test_graph in
  dominator_exact p && dominator_exact (prepared_reverse p [2; 3]) = true.
Proof.
  vm_compute; reflexivity.
Qed.
