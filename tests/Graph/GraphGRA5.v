(** * Frontier and edgewise control-dependence examples

    Computed examples distinguish frontier closure, loops and parallel branch-edge identities.
    For example, a diamond join is emitted by each arm but not by their common dominator.
    Builds on: GraphFrontier and GraphControlDependence. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDominators GraphPostDominators
  GraphFrontier GraphControlDependence.
Import List.ListNotations.

Definition frontier_diamond : Graph.t nat (nat * nat) :=
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

Definition frontier_has {V} (EV : encoding V) (m : Map.t V (FinSet.t V)) (d n : V) : bool :=
  match Map.get EV d m with
  | Some s => FinSet.mem EV n s
  | None => false
  end.

Example frontier_diamond_join :
  let p := prepare nat_encoding frontier_diamond in
  let df := dominance_frontier p (dominator_tree p) in
  frontier_has nat_encoding df 1 3 && frontier_has nat_encoding df 2 3 &&
  negb (frontier_has nat_encoding df 0 3) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example frontier_diamond_closure :
  let p := prepare nat_encoding frontier_diamond in
  let df := dominance_frontier p (dominator_tree p) in
  FinSet.elements (iterated_frontier p df [1; 99]) = [3].
Proof.
  vm_compute; reflexivity.
Qed.

Definition frontier_loop : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [(0, 1)]
       | 1 => [(1, 2); (1, 3)]
       | 2 => [(2, 1)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example frontier_loop_header :
  let p := prepare nat_encoding frontier_loop in
  let df := dominance_frontier p (dominator_tree p) in
  frontier_has nat_encoding df 1 1 && frontier_has nat_encoding df 2 1 &&
  negb (frontier_has nat_encoding df 0 1) = true /\
  FinSet.elements (iterated_frontier p df [2]) = [1].
Proof.
  vm_compute; auto.
Qed.

Definition frontier_entry_loop : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0];
     Graph.out := fun v => match v with
       | 0 => [(0, 0)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example frontier_single_predecessor_entry_loop :
  let p := prepare nat_encoding frontier_entry_loop in
  let df := dominance_frontier p (dominator_tree p) in
  frontier_has nat_encoding df 0 0 = true /\
  FinSet.elements (iterated_frontier p df [0]) = [0].
Proof.
  vm_compute; auto.
Qed.

Definition frontier_multiple_entries : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0; 1];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [(0, 2)]
       | 1 => [(1, 2)]
       | 3 => [(3, 2)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example frontier_roots_inclusive_unreachable_predecessor_ignored :
  let p := prepare nat_encoding frontier_multiple_entries in
  let df := dominance_frontier p (dominator_tree p) in
  frontier_has nat_encoding df 0 2 && frontier_has nat_encoding df 1 2 &&
  negb (frontier_has nat_encoding df 3 2) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition frontier_nested_joins : Graph.t nat (nat * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3; 4];
     Graph.out := fun v => match v with
       | 0 => [(0, 1); (0, 4)]
       | 1 => [(1, 2); (1, 3)]
       | 2 => [(2, 3)]
       | 3 => [(3, 4)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Example frontier_closure_takes_two_steps :
  let p := prepare nat_encoding frontier_nested_joins in
  let df := dominance_frontier p (dominator_tree p) in
  frontier_has nat_encoding df 2 3 && negb (frontier_has nat_encoding df 2 4) &&
  frontier_has nat_encoding df 3 4 &&
  FinSet.mem nat_encoding 3 (iterated_frontier p df [2]) &&
  FinSet.mem nat_encoding 4 (iterated_frontier p df [2]) &&
  negb (FinSet.mem nat_encoding 2 (iterated_frontier p df [2])) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition control_parallel_diamond : Graph.t nat ((nat * nat) * nat) :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun v => match v with
       | 0 => [((0, 1), 0); ((0, 1), 1); ((0, 2), 2)]
       | 1 => [((1, 3), 3)]
       | 2 => [((2, 3), 4)]
       | _ => []
       end;
     Graph.source := fun e => fst (fst e);
     Graph.target := fun e => snd (fst e) |}.

Definition control_has (m : Map.t nat (list ((nat * nat) * nat))) (n id : nat) : bool :=
  match Map.get nat_encoding n m with
  | Some edges => existsb (fun e => Nat.eqb (snd e) id) edges
  | None => false
  end.

Example control_edge_by_edge :
  let p := prepare nat_encoding control_parallel_diamond in
  let cd := control_deps p [3] (post_dominator_tree p [3]) in
  control_has cd 1 0 && control_has cd 1 1 && negb (control_has cd 1 2) &&
  control_has cd 2 2 && negb (control_has cd 2 0) &&
  negb (control_has cd 3 0) && negb (control_has cd 3 2) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example frontier_checker_accepts_diamond_loop_and_parallel_reverse :
  let pd := prepare nat_encoding frontier_diamond in
  let pl := prepare nat_encoding frontier_loop in
  let pc := prepare nat_encoding control_parallel_diamond in
  dominator_exact pd && dominator_exact pl &&
  dominator_exact (prepared_reverse pc [3]) = true.
Proof.
  vm_compute; reflexivity.
Qed.
