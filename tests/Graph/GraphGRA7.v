(** * Direct iterated-frontier queries

    Boolean observations compare direct queries with a separately materialized frontier closure.
    For example, killing a first join also prevents propagation to a later live join.
    Builds on: GraphIdf, GraphFrontier and GraphDominators. *)

From Stdlib Require Import List Bool Arith PArith NArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphFrontier GraphIdf.
Import List.ListNotations.

Definition idf_diamond : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v =>
       match v with
       | 0 => [(0, 1); (0, 2)]
       | 1 => [(1, 3)]
       | 2 => [(2, 3)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition idf_loop : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v =>
       match v with
       | 0 => [(0, 1)]
       | 1 => [(1, 2); (1, 3)]
       | 2 => [(2, 1)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition idf_entry_loop : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0];
     Graph.out := fun v =>
       match v with
       | 0 => [(0, 0)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition idf_multiple_entries : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0; 1];
     Graph.nodes := [0; 1; 2; 3; 4];
     Graph.out := fun v =>
       match v with
       | 0 => [(0, 2)]
       | 1 => [(1, 2)]
       | 2 => [(2, 3)]
       | 4 => [(4, 2)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition idf_nested_joins : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3; 4];
     Graph.out := fun v =>
       match v with
       | 0 => [(0, 1); (0, 4)]
       | 1 => [(1, 2); (1, 3)]
       | 2 => [(2, 3)]
       | 3 => [(3, 4)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition idf_observe (nodes : list nat) (result : FinSet.t nat) : list bool :=
  map (fun v => FinSet.mem nat_encoding v result) nodes.

Definition idf_materialized_pruned {E} {g : Graph.t nat E}
    (p : prepared nat_encoding g) defs live : FinSet.t nat :=
  let frontiers := dominance_frontier p (dominator_tree p) in
  let pruned := Map.map
    (fun targets => FinSet.of_list nat_encoding (filter live (FinSet.elements targets)))
    frontiers in
  iterated_frontier p pruned defs.

Definition idf_compare {E} (g : Graph.t nat E) defs live : bool :=
  let p := prepare nat_encoding g in
  let t := dominator_tree p in
  let direct := direct_idf p t defs in
  let materialized := iterated_frontier p (dominance_frontier p t) defs in
  let pruned := direct_pruned_idf p t defs live in
  let reference := idf_materialized_pruned p defs live in
  forallb (fun v => Bool.eqb (FinSet.mem nat_encoding v direct)
    (FinSet.mem nat_encoding v materialized) &&
    Bool.eqb (FinSet.mem nat_encoding v pruned) (FinSet.mem nat_encoding v reference))
    (99 :: Graph.nodes g).

Example idf_empty_definitions :
  let p := prepare nat_encoding idf_diamond in
  let t := dominator_tree p in
  idf_observe [0; 1; 2; 3; 99] (direct_idf p t []) = [false; false; false; false; false] /\
  idf_observe [0; 1; 2; 3; 99] (direct_pruned_idf p t [] (fun _ => true)) =
    [false; false; false; false; false] /\
  idf_compare idf_diamond [] (fun _ => true) = true.
Proof.
  vm_compute; auto.
Qed.

Example idf_diamond_join :
  let p := prepare nat_encoding idf_diamond in
  let t := dominator_tree p in
  idf_observe [0; 1; 2; 3; 99] (direct_idf p t [1; 2; 1; 99]) =
    [false; false; false; true; false] /\
  idf_observe [0; 1; 2; 3] (direct_pruned_idf p t [1] (fun v => Nat.eqb v 3)) =
    [false; false; false; true] /\
  idf_compare idf_diamond [1; 2; 1; 99] (fun v => Nat.eqb v 3) = true.
Proof.
  vm_compute; auto.
Qed.

Example idf_loop_self_frontier :
  let p := prepare nat_encoding idf_loop in
  let t := dominator_tree p in
  idf_observe [0; 1; 2; 3] (direct_idf p t [1; 2]) = [false; true; false; false] /\
  idf_observe [0; 1; 2; 3] (direct_pruned_idf p t [1; 2] (fun v => Nat.eqb v 1)) =
    [false; true; false; false] /\
  idf_compare idf_loop [1; 2] (fun v => Nat.eqb v 1) = true.
Proof.
  vm_compute; auto.
Qed.

Example idf_single_predecessor_entry_loop :
  let p := prepare nat_encoding idf_entry_loop in
  let t := dominator_tree p in
  FinSet.mem nat_encoding 0 (direct_idf p t [0]) &&
    FinSet.mem nat_encoding 0 (direct_pruned_idf p t [0] (fun _ => true)) &&
    negb (FinSet.mem nat_encoding 0 (direct_pruned_idf p t [0] (fun _ => false))) &&
    idf_compare idf_entry_loop [0] (fun _ => false) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example idf_multiple_roots_and_unreachable_definition :
  let p := prepare nat_encoding idf_multiple_entries in
  let t := dominator_tree p in
  idf_observe [0; 1; 2; 3; 4; 99] (direct_idf p t [0; 1; 4; 99]) =
    [false; false; true; false; false; false] /\
  idf_observe [0; 1; 2; 3; 4] (direct_pruned_idf p t [0; 1; 4] (fun v => Nat.eqb v 2)) =
    [false; false; true; false; false] /\
  idf_observe [0; 1; 2; 3; 4] (direct_idf p t [4; 99]) =
    [false; false; false; false; false] /\
  idf_compare idf_multiple_entries [0; 1; 4; 99] (fun v => Nat.eqb v 2) = true.
Proof.
  vm_compute; auto.
Qed.

Example idf_pruning_suppresses_further_propagation :
  let p := prepare nat_encoding idf_nested_joins in
  let t := dominator_tree p in
  idf_observe [0; 1; 2; 3; 4] (direct_idf p t [2]) = [false; false; false; true; true] /\
  idf_observe [0; 1; 2; 3; 4] (direct_pruned_idf p t [2] (fun v => Nat.eqb v 3)) =
    [false; false; false; true; false] /\
  idf_observe [0; 1; 2; 3; 4] (direct_pruned_idf p t [2] (fun v => Nat.eqb v 4)) =
    [false; false; false; false; false] /\
  idf_observe [0; 1; 2; 3; 4] (direct_pruned_idf p t [3] (fun v => Nat.eqb v 4)) =
    [false; false; false; false; true] /\
  idf_compare idf_nested_joins [2] (fun v => Nat.eqb v 3) &&
    idf_compare idf_nested_joins [2] (fun v => Nat.eqb v 4) = true.
Proof.
  vm_compute; auto.
Qed.

Example idf_priority_uses_tree_depth :
  let p := prepare nat_encoding idf_nested_joins in
  let t := dominator_tree p in
  let forest := dom_forest p (idom t) in
  let tree := prepare nat_encoding forest in
  let levels := idf_levels nat_encoding (idom t) forest tree in
  let initial := idf_initial nat_encoding (fuel p) levels [4; 2] in
  match PQueue.pop nat_encoding (IdfState.pending initial) with
  | Some (_, root, _) => Nat.eqb root 2 &&
      Pos.eqb (idf_level nat_encoding levels 0) 1 &&
      Pos.eqb (idf_level nat_encoding levels 2) 3 &&
      Pos.eqb (idf_level nat_encoding levels 4) 2
  | None => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example idf_shared_scan_and_distinct_output_costs :
  let p := prepare nat_encoding idf_nested_joins in
  let t := dominator_tree p in
  let forest := dom_forest p (idom t) in
  let tree := prepare nat_encoding forest in
  let levels := idf_levels nat_encoding (idom t) forest tree in
  let initial := idf_initial nat_encoding (fuel p) levels [0; 1; 2; 2] in
  let result := idf_run p t forest tree levels (fun _ => true) 6 initial in
  N.eqb (IdfState.edge_visits result) 6 &&
    N.eqb (IdfState.output_count result) 2 &&
    Nat.eqb (length (IdfState.trace result)) 5 &&
    Nat.eqb (FinSet.size (IdfState.scanned result)) 5 = true.
Proof.
  vm_compute; reflexivity.
Qed.
