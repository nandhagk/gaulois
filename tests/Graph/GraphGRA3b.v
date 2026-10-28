(** * DAG paths and forwarding examples

    Computed examples cover signed maximum weights, unreachable cycles and memoised landings.
    For example, a heavier two-edge route wins even when its intermediate vertex is visited later.
    Builds on: GraphDag, GraphChain and Collections encodings. *)

From Stdlib Require Import List ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDag GraphChain.
Import List.ListNotations.

Definition gra3b_empty : Graph.t nat nat := Graph.Make [] [] (fun _ => []) id id.

Example gra3b_empty_sort : topological_sort (prepare nat_encoding gra3b_empty) = Some [].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_empty_paths :
  option_map (fun r => Map.get nat_encoding 0 (best r))
    (max_paths (prepare nat_encoding gra3b_empty) (fun _ => 1%Z)) = Some None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3b_source (e : nat) : nat :=
  match e with
  | 0 | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | _ => 5
  end.

Definition gra3b_target (e : nat) : nat :=
  match e with
  | 0 => 1
  | 1 => 2
  | 2 | 3 => 3
  | 4 => 4
  | _ => 5
  end.

Definition gra3b_weight (e : nat) : Z :=
  match e with
  | 0 => 2%Z
  | 1 => 5%Z
  | 2 => 9%Z
  | 3 => 1%Z
  | 4 => (-20)%Z
  | _ => 1%Z
  end.

Definition gra3b_dag : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2; 3; 4; 5]
    (fun v => match v with
      | 0 => [0; 1]
      | 1 => [2]
      | 2 => [3]
      | 3 => [4]
      | _ => []
      end) gra3b_source gra3b_target.

Definition gra3b_dag_prepared := prepare nat_encoding gra3b_dag.

Example gra3b_sort_all_nodes : topological_sort gra3b_dag_prepared = Some [5; 0; 2; 1; 3; 4].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_search_check_accepts :
  dag_search_ok gra3b_dag_prepared
    (dfs gra3b_dag_prepared FinSet.empty (Graph.entries gra3b_dag)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_weighted_branch :
  option_map (fun r => (Map.get nat_encoding 3 (best r),
    max_path_to gra3b_dag_prepared r 3))
    (max_paths gra3b_dag_prepared gra3b_weight) = Some (Some 11%Z, Some (0, [0; 2])).
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_negative_and_unreachable :
  option_map (fun r => (Map.get nat_encoding 4 (best r),
    Map.get nat_encoding 5 (best r), max_path_to gra3b_dag_prepared r 5))
    (max_paths gra3b_dag_prepared gra3b_weight) = Some (Some (-9)%Z, None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3b_entry_dag := set_entries gra3b_dag [0; 4; 4].
Definition gra3b_entry_prepared := prepare nat_encoding gra3b_entry_dag.

Example gra3b_empty_entry_path_wins :
  option_map (fun r => (Map.get nat_encoding 4 (best r),
    max_path_to gra3b_entry_prepared r 4))
    (max_paths gra3b_entry_prepared gra3b_weight) = Some (Some 0%Z, Some (4, [])).
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3b_unreachable_cycle : Graph.t nat nat :=
  Graph.Make (Graph.entries gra3b_dag) (Graph.nodes gra3b_dag)
    (fun v => match v with 5 => [5] | _ => Graph.out gra3b_dag v end)
    gra3b_source gra3b_target.

Definition gra3b_unreachable_prepared := prepare nat_encoding gra3b_unreachable_cycle.

Example gra3b_sort_rejects_unreachable_cycle : topological_sort gra3b_unreachable_prepared = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_paths_allow_unreachable_cycle :
  option_map (fun r => Map.get nat_encoding 3 (best r))
    (max_paths gra3b_unreachable_prepared gra3b_weight) = Some (Some 11%Z).
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3b_reachable_cycle := set_entries gra3b_unreachable_cycle [0; 5].

Example gra3b_paths_reject_reachable_cycle :
  max_paths (prepare nat_encoding gra3b_reachable_cycle) gra3b_weight = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3b_forward_graph : Graph.t nat (nat * nat) :=
  Graph.Make [] [0; 1; 2; 3; 4; 5; 6; 7]
    (fun v => match v with
      | 0 => [(0, 1)]
      | 1 => [(1, 2)]
      | 3 => [(3, 4)]
      | 4 => [(4, 3)]
      | 5 => [(5, 5)]
      | 6 => [(6, 1); (6, 2)]
      | 7 => [(7, 2)]
      | _ => []
      end) fst snd.

Definition gra3b_forward_prepared := prepare nat_encoding gra3b_forward_graph.
Definition gra3b_fwd (v : nat) := negb (Nat.eqb v 7).

Example gra3b_forward_landing : resolve gra3b_forward_prepared gra3b_fwd 0 = Landing 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3b_forward_cycles :
  resolve gra3b_forward_prepared gra3b_fwd 3 = Cyclic /\
  resolve gra3b_forward_prepared gra3b_fwd 5 = Cyclic.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra3b_forward_stops :
  resolve gra3b_forward_prepared gra3b_fwd 6 = Landing 6 /\
  resolve gra3b_forward_prepared gra3b_fwd 7 = Landing 7.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra3b_forward_memo :
  Map.get nat_encoding 0 (resolve_all gra3b_forward_prepared gra3b_fwd) = Some (Landing 2) /\
  Map.get nat_encoding 1 (resolve_all gra3b_forward_prepared gra3b_fwd) = Some (Landing 2) /\
  Map.get nat_encoding 2 (resolve_all gra3b_forward_prepared gra3b_fwd) = Some (Landing 2) /\
  Map.get nat_encoding 4 (resolve_all gra3b_forward_prepared gra3b_fwd) = Some Cyclic /\
  Map.get nat_encoding 8 (resolve_all gra3b_forward_prepared gra3b_fwd) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
