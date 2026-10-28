(** * Graph preparation examples

    These examples exercise empty and multi-entry graphs and reversed adjacency.
    For example, distinct parallel edges remain distinct in a predecessor list.
    Builds on: GraphCore, GraphPrepare and CollectionsEncoding. *)

From Stdlib Require Import List Arith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
Import List.ListNotations.

(** * Computed examples *)

Definition empty_graph : Graph.t nat nat :=
  {| Graph.entries := []; Graph.nodes := []; Graph.out := fun _ => [];
     Graph.source := fun e => e; Graph.target := fun e => e |}.

Definition example_graph : Graph.t nat nat :=
  {| Graph.entries := [0; 1]; Graph.nodes := [0; 1; 2];
     Graph.out := fun v => match v with
       | 0 => [10; 11]
       | 1 => [12]
       | _ => []
       end;
     Graph.source := fun e => if Nat.eqb e 12 then 1 else 0;
     Graph.target := fun _ => 2 |}.

Example empty_indexes :
  succ_edges (prepare nat_encoding empty_graph) 0 = [] /\
  pred_edges (prepare nat_encoding empty_graph) 0 = [].
Proof.
  vm_compute; auto.
Qed.

Example multi_entry_indexes :
  Graph.entries example_graph = [0; 1] /\
  succ_edges (prepare nat_encoding example_graph) 0 = [10; 11] /\
  pred_edges (prepare nat_encoding example_graph) 2 = [10; 11; 12].
Proof.
  vm_compute; auto.
Qed.

Example reversed_edges :
  Graph.out (reverse_graph (prepare nat_encoding example_graph) [2]) 2 = [10; 11; 12] /\
  NoDup (Graph.out (reverse_graph (prepare nat_encoding example_graph) [2]) 2).
Proof.
  vm_compute; split; [reflexivity|].
  repeat (apply NoDup_cons; [simpl; intuition discriminate|]); apply NoDup_nil.
Qed.
