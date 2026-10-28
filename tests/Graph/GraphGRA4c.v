(** * Weak topological order examples

    These computations distinguish nested components, scope boundaries and malformed orders.
    For example, the edge 3 to 2 requires 3 to remain inside the component headed by 2.
    Builds on: GraphWto and Collections encodings. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphWto.
Import List.ListNotations.

Definition gra4c_empty : Graph.t nat (nat * nat) :=
  Graph.Make [] [] (fun _ => []) fst snd.

Example gra4c_empty_order :
  wto_of (prepare nat_encoding gra4c_empty) = [] /\
  check_wto (prepare nat_encoding gra4c_empty) [] = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition gra4c_nested : Graph.t nat (nat * nat) :=
  Graph.Make [0] [0; 1; 2; 3; 4; 5; 6]
    (fun v => match v with
      | 0 => [(0, 1)]
      | 1 => [(1, 2)]
      | 2 => [(2, 3)]
      | 3 => [(3, 2); (3, 1); (3, 4)]
      | 4 => [(4, 5)]
      | 5 => [(5, 4)]
      | 6 => [(6, 6)]
      | _ => []
      end) fst snd.

Definition gra4c_nested_prepared := prepare nat_encoding gra4c_nested.

Definition gra4c_nested_order : wto nat :=
  [WVertex 0; WOpen 1; WOpen 2; WVertex 3; WClose; WClose;
   WOpen 4; WVertex 5; WClose].

Example gra4c_producer_nested : wto_of gra4c_nested_prepared = gra4c_nested_order.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_nested_accepts : check_wto gra4c_nested_prepared gra4c_nested_order = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_nested_annotations :
  annotate [] gra4c_nested_order =
  [(0, []); (1, [1]); (2, [2; 1]); (3, [2; 1]); (4, [4]); (5, [4])].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_nested_total :
  wto_total gra4c_nested_prepared = gra4c_nested_order /\
  check_wto gra4c_nested_prepared (wto_total gra4c_nested_prepared) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra4c_flat_cycle_rejected :
  check_wto gra4c_nested_prepared
    [WVertex 0; WVertex 1; WVertex 2; WVertex 3; WVertex 4; WVertex 5] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_close_boundary_rejected :
  check_wto gra4c_nested_prepared
    [WVertex 0; WOpen 1; WOpen 2; WClose; WVertex 3; WClose;
     WOpen 4; WVertex 5; WClose] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_missing_vertex_rejected :
  check_wto gra4c_nested_prepared
    [WOpen 1; WOpen 2; WVertex 3; WClose; WClose; WOpen 4; WVertex 5; WClose] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_unreachable_vertex_rejected :
  check_wto gra4c_nested_prepared (wto_all_heads [0; 1; 2; 3; 4; 5; 6]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_duplicate_vertex_rejected :
  check_wto gra4c_nested_prepared (WVertex 0 :: gra4c_nested_order) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_extra_close_rejected :
  check_wto gra4c_nested_prepared (gra4c_nested_order ++ [WClose]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_missing_close_rejected :
  check_wto gra4c_nested_prepared
    [WVertex 0; WOpen 1; WOpen 2; WVertex 3; WClose; WClose; WOpen 4; WVertex 5] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_fallback_shape :
  wto_all_heads [0; 1; 2] = [WOpen 0; WOpen 1; WOpen 2; WClose; WClose; WClose].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra4c_fallback_accepts_arbitrary_order :
  check_wto gra4c_nested_prepared (wto_all_heads [5; 3; 0; 4; 2; 1]) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra4c_self : Graph.t nat (nat * nat) :=
  Graph.Make [7] [7] (fun v => if Nat.eqb v 7 then [(7, 7)] else []) fst snd.

Example gra4c_singleton_self_loop :
  let p := prepare nat_encoding gra4c_self in
  wto_of p = [WOpen 7; WClose] /\
  check_wto p [WOpen 7; WClose] = true /\ check_wto p [WVertex 7] = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition gra4c_irreducible : Graph.t nat (nat * nat) :=
  Graph.Make [0] [0; 1; 2; 3; 4]
    (fun v => match v with
      | 0 => [(0, 1); (0, 2)]
      | 1 => [(1, 3)]
      | 2 => [(2, 3)]
      | 3 => [(3, 1); (3, 2); (3, 4)]
      | _ => []
      end) fst snd.

Example gra4c_irreducible_nested :
  let p := prepare nat_encoding gra4c_irreducible in
  wto_of p = [WVertex 0; WOpen 1; WOpen 3; WVertex 2; WClose; WClose; WVertex 4] /\
  check_wto p (wto_of p) = true /\
  check_wto p [WVertex 0; WOpen 1; WVertex 3; WVertex 2; WClose; WVertex 4] = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition gra4c_dag : Graph.t nat (nat * nat) :=
  Graph.Make [0; 4] [0; 1; 2; 3; 4]
    (fun v => match v with
      | 0 => [(0, 1); (0, 2)]
      | 1 => [(1, 3)]
      | 2 => [(2, 3)]
      | _ => []
      end) fst snd.

Example gra4c_dag_has_no_component_tokens :
  let p := prepare nat_encoding gra4c_dag in
  wto_of p = map WVertex (wto_order (wto_of p)) /\ check_wto p (wto_of p) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.
