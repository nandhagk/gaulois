(** * Tarjan and condensation examples

    Computed examples distinguish component order, region boundaries and original edge identity.
    For example, two cycles joined by one edge are emitted in reverse topological order.
    Builds on: GraphScc and Collections encodings. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphScc.
Import List.ListNotations.

Definition gra3a_empty : Graph.t nat (nat * nat) :=
  Graph.Make [] [] (fun _ => []) fst snd.

Example gra3a_empty_components : components (scc (prepare nat_encoding gra3a_empty)) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Definition gra3a_graph : Graph.t nat (nat * nat) :=
  Graph.Make [0; 0; 5] [0; 1; 2; 3; 4; 5]
    (fun v => match v with
      | 0 => [(0, 1)]
      | 1 => [(1, 2)]
      | 2 => [(2, 1); (2, 3)]
      | 3 => [(3, 4)]
      | 4 => [(4, 3)]
      | 5 => [(5, 5)]
      | _ => []
      end) fst snd.

Definition gra3a_prepared := prepare nat_encoding gra3a_graph.

Example gra3a_empty_region : components (scc_within gra3a_prepared []) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_singleton : components (scc_within gra3a_prepared [0]) = [[0]].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_singleton_loop : components (scc_within gra3a_prepared [5]) = [[5]].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_cycle : components (scc_within gra3a_prepared [1; 2]) = [[2; 1]].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_disconnected_and_order :
  components (scc gra3a_prepared) = [[4; 3]; [2; 1]; [0]; [5]] /\
  component_ids (scc gra3a_prepared) = [1; 2; 3; 4]%positive.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example gra3a_duplicate_region :
  components (scc_within gra3a_prepared [1; 2; 1; 2]) = [[2; 1]].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_region_ignores_exit :
  components (scc_within gra3a_prepared [0; 2]) = [[0]; [2]].
Proof.
  vm_compute; reflexivity.
Qed.

Example gra3a_component_indexes :
  Trie.get 2%positive (component_at (scc gra3a_prepared)) = Some [2; 1] /\
  Map.get nat_encoding 1 (comp_of (scc gra3a_prepared)) = Some 2%positive /\
  Map.get nat_encoding 2 (comp_of (scc gra3a_prepared)) = Some 2%positive /\
  Map.get nat_encoding 6 (comp_of (scc gra3a_prepared)) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition gra3a_condensed := condensation gra3a_prepared (scc gra3a_prepared).

Example gra3a_condensation :
  Graph.nodes gra3a_condensed = [4; 3; 2; 1]%positive /\
  Graph.entries gra3a_condensed = [3; 4]%positive /\
  Graph.out gra3a_condensed 3%positive = [(0, 1)] /\
  Graph.out gra3a_condensed 2%positive = [(2, 3)] /\
  Graph.out gra3a_condensed 1%positive = [] /\
  Graph.out gra3a_condensed 4%positive = [] /\
  Graph.source gra3a_condensed (2, 3) = 2%positive /\
  Graph.target gra3a_condensed (2, 3) = 1%positive.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example gra3a_condensation_topological :
  topological_order gra3a_condensed [4; 3; 2; 1]%positive.
Proof.
  split.
  - repeat constructor; vm_compute; intuition discriminate.
  - split; [intro c; reflexivity|].
    intros e Hnode Hedge.
    change (In (Graph.source gra3a_condensed e) [4; 3; 2; 1]%positive) in Hnode.
    destruct Hnode as [Hc|[Hc|[Hc|[Hc|Hfalse]]]]; [| | | |contradiction].
    all: rewrite <- Hc in Hedge; vm_compute in Hedge; try contradiction.
    all: destruct Hedge as [Heq|Hfalse]; [subst e|contradiction].
    + change (before [4; 3; 2; 1]%positive 3%positive 2%positive).
      exists [4]%positive, [], [1]%positive; reflexivity.
    + change (before [4; 3; 2; 1]%positive 2%positive 1%positive).
      exists [4; 3]%positive, [], []; reflexivity.
Qed.

(** A cross edge to a closed pending sibling uses its discovery number, not its lowlink. *)
Definition gra3a_pending_cross : Graph.t nat (nat * nat) :=
  Graph.Make [0] [0; 1; 2]
    (fun v => match v with
      | 0 => [(0, 1); (0, 2)]
      | 1 => [(1, 0)]
      | 2 => [(2, 1)]
      | _ => []
      end) fst snd.

Example gra3a_pending_cross_component :
  components (scc (prepare nat_encoding gra3a_pending_cross)) = [[2; 1; 0]].
Proof.
  vm_compute; reflexivity.
Qed.

(** Distinct edges with identical endpoints must both survive condensation. *)
Definition gra3a_parallel : Graph.t nat nat :=
  Graph.Make [0] [0; 1]
    (fun v => match v with 0 => [10; 11] | _ => [] end)
    (fun _ => 0) (fun _ => 1).

Example gra3a_condensation_keeps_parallel_edges :
  let p := prepare nat_encoding gra3a_parallel in
  Graph.out (condensation p (scc p)) 2%positive = [10; 11].
Proof.
  vm_compute; reflexivity.
Qed.
