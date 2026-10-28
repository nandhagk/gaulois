(** * Semantic dominance and virtual-root examples

    Boolean observations exercise entry deduplication, paths, reachability and parent erasure.
    For example, two entries meet at node two, which dominates their common successor three.
    Builds on: GraphDominance, GraphDfs, GraphCertificate and Collections encodings and maps. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphCertificate GraphDominance.
Import List.ListNotations.

(** * Fixtures and Boolean observations *)

Definition dominance_example_graph : Graph.t nat nat :=
  {| Graph.entries := [1; 0; 1; 0];
     Graph.nodes := [0; 1; 2; 3; 4];
     Graph.out := fun v => match v with
       | 0 => [10]
       | 1 => [11]
       | 2 => [12]
       | 3 => [13]
       | 4 => [14]
       | _ => []
       end;
     Graph.source := fun e => match e with
       | 10 => 0
       | 11 => 1
       | 12 => 2
       | 13 => 3
       | _ => 4
       end;
     Graph.target := fun e => match e with
       | 12 => 3
       | 14 => 3
       | _ => 2
       end |}.

Definition dominance_example_prepared := prepare nat_encoding dominance_example_graph.

Definition dominance_virtual_prepared := virtual_prepared dominance_example_prepared.

Definition virtual_edge_eqb (a b : nat + nat) : bool :=
  match a, b with
  | inl x, inl y => Nat.eqb x y
  | inr x, inr y => Nat.eqb x y
  | _, _ => false
  end.

Definition dominance_deleted_observation (d n : nat) : bool :=
  negb (FinSet.mem nat_encoding n (visited (dfs dominance_example_prepared
    (FinSet.add nat_encoding d FinSet.empty) (Graph.entries dominance_example_graph)))).

Definition virtual_deleted_observation (d n : nat) : bool :=
  negb (FinSet.mem (virtual_encoding nat_encoding) (inl n)
    (visited (dfs dominance_virtual_prepared
      (FinSet.add (virtual_encoding nat_encoding) (inl d) FinSet.empty) [inr tt]))).

(** * Computed examples *)

Example virtual_entries_keep_first_occurrences :
  (match virtual_entries nat_encoding dominance_example_graph with
   | [x; y] => Nat.eqb x 1 && Nat.eqb y 0
   | _ => false
   end) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_empty_entries :
  let p := virtual_prepared
    (prepare nat_encoding (set_entries dominance_example_graph [])) in
  map (fun v => FinSet.mem (virtual_encoding nat_encoding) v
    (visited (dfs p FinSet.empty [inr tt]))) [inr tt; inl 0; inl 3; inl 4] =
  [true; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_multiple_entries_and_unreachable_node :
  map (fun v => FinSet.mem (virtual_encoding nat_encoding) v
    (visited (dfs dominance_virtual_prepared FinSet.empty [inr tt])))
    [inr tt; inl 0; inl 1; inl 2; inl 3; inl 4] =
  [true; true; true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_path_certificates :
  [check_path dominance_virtual_prepared virtual_edge_eqb (inr tt)
     [inr 1; inl 11; inl 12; inl 13; inl 12] (inl 3);
   check_path dominance_virtual_prepared virtual_edge_eqb (inr tt)
     [inr 0; inl 10; inl 12] (inl 3);
   check_path dominance_virtual_prepared virtual_edge_eqb (inr tt) [inr 4] (inl 4);
   check_path dominance_virtual_prepared virtual_edge_eqb (inr tt)
     [inr 1; inr 0] (inl 0);
   check_path dominance_virtual_prepared virtual_edge_eqb (inr tt) [inl 10] (inl 2);
   check_path dominance_virtual_prepared virtual_edge_eqb (inr tt) [] (inl 0)] =
  [true; true; false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example dominance_deletion_observations :
  map (fun dn => dominance_deleted_observation (fst dn) (snd dn))
    [(2, 3); (0, 3); (1, 3); (3, 3); (4, 3); (0, 4); (2, 0)] =
  [true; false; false; true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_dominance_deletion_agrees :
  map (fun dn => Bool.eqb
    (dominance_deleted_observation (fst dn) (snd dn))
    (virtual_deleted_observation (fst dn) (snd dn)))
    [(2, 3); (0, 3); (1, 3); (3, 3); (4, 3); (0, 4); (2, 0)] =
  [true; true; true; true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Definition virtual_parent_example : Map.t (nat + unit) (nat + unit) :=
  Map.of_list (virtual_encoding nat_encoding)
    [(inl 0, inr tt); (inl 1, inr tt); (inl 2, inr tt); (inl 3, inl 2)].

Example virtual_parent_erasure :
  let m := erase_virtual_parents nat_encoding virtual_parent_example in
  [Map.mem nat_encoding 0 m;
   Map.mem nat_encoding 1 m;
   Map.mem nat_encoding 2 m;
   match Map.get nat_encoding 3 m with
   | Some p => Nat.eqb p 2
   | None => false
   end;
   Map.mem nat_encoding 4 m] = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example virtual_root_encoding_is_fresh :
  negb (Pos.eqb (encode (virtual_encoding nat_encoding) (inr tt))
    (encode (virtual_encoding nat_encoding) (inl 0))) = true.
Proof.
  vm_compute; reflexivity.
Qed.
