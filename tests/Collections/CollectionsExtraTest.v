(** * Priority queue, union-find and table boundary examples

    These examples compute observable results for duplicates, compression and list keys.
    For example, a priority tie pops the smaller encoded key first.
    Builds on: CollectionsHeap, CollectionsUnionFind, CollectionsTable. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap
  CollectionsUnionFind CollectionsTable.
Import List.ListNotations.
Local Open Scope positive_scope.

Definition queue_ties : PQueue.t positive :=
  PQueue.push positive_encoding 3 2 (PQueue.push positive_encoding 3 1 PQueue.empty).

(** Equal priorities use encoded key order. *)
Example queue_tie_order :
  option_map (fun result => (fst (fst result), snd (fst result)))
    (PQueue.pop positive_encoding queue_ties) = Some (3%positive, 1%positive).
Proof.
  vm_compute; reflexivity.
Qed.

Definition queue_stale : PQueue.t positive :=
  PQueue.push positive_encoding 7 2
    (PQueue.push positive_encoding 2 1 (PQueue.push positive_encoding 5 1 PQueue.empty)).

(** Decreasing a priority keeps one live binding and skips its obsolete absent entry later. *)
Example queue_stale_absent :
  PQueue.size queue_stale = 2%nat /\
  match PQueue.pop positive_encoding queue_stale with
  | Some (p, k, rest) =>
    (p, k) = (2%positive, 1%positive) /\ PQueue.priority positive_encoding 1 rest = None /\
    match PQueue.pop positive_encoding rest with
    | Some (p', k', final) =>
      (p', k') = (7%positive, 2%positive) /\ PQueue.pop positive_encoding final = None
    | None => False
    end
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** A stale entry is skipped even when its key has a different live priority. *)
Example queue_stale_present :
  let q := PQueue.push positive_encoding 2 1
    (PQueue.push positive_encoding 5 1 PQueue.empty) in
  match PQueue.pop positive_encoding q with
  | Some (p, k, rest) =>
    (p, k) = (2%positive, 1%positive) /\
    let reinserted := PQueue.push positive_encoding 7 1 rest in
    PQueue.priority positive_encoding 1 reinserted = Some 7%positive /\
    match PQueue.pop positive_encoding reinserted with
    | Some (p', k', final) =>
      (p', k') = (7%positive, 1%positive) /\ PQueue.pop positive_encoding final = None
    | None => False
    end
  | None => False
  end.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Carrying through several occupied ranks preserves both persistent branches. *)
Example queue_persistent_carry :
  let q := List.fold_left (fun q k => PQueue.push positive_encoding 3 k q)
    [7; 6; 5; 4; 3; 2; 1] PQueue.empty in
  let extended := PQueue.push positive_encoding 2 8 q in
  option_map (fun result => (fst (fst result), snd (fst result)))
    (PQueue.pop positive_encoding q) = Some (3%positive, 1%positive) /\
  option_map (fun result => (fst (fst result), snd (fst result)))
    (PQueue.pop positive_encoding extended) = Some (2%positive, 8%positive) /\
  PQueue.size q = 7%nat /\ PQueue.size extended = 8%nat.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Pushing a larger priority preserves the smaller live priority and count. *)
Example queue_priority_minimum :
  let q := PQueue.push positive_encoding 9 1 queue_stale in
  PQueue.priority positive_encoding 1 q = Some 2%positive /\ PQueue.size q = 2%nat /\
  PQueue.priority positive_encoding 9 q = None /\ PQueue.is_empty q = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Empty queues have no member to pop. *)
Example queue_empty_boundary :
  PQueue.pop positive_encoding PQueue.empty = None /\
  PQueue.is_empty (@PQueue.empty positive) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition forest_pairs : list (positive * positive) := [(1, 2); (3, 4); (1, 3)].

Definition forest : UnionFind.t positive := UnionFind.of_unions positive_encoding forest_pairs.

(** Balanced rank ties produce a two-link path and a bounded maximum rank. *)
Example union_find_rank_path :
  UnionFind.max_rank forest = 2%nat /\ Map.get positive_encoding 4 (UnionFind.parents forest) =
    Some 3%positive /\ fst (UnionFind.find positive_encoding 4 forest) = 1%positive.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Finding a non-root compresses its path while preserving the ranks. *)
Example union_find_compression :
  let compressed := snd (UnionFind.find positive_encoding 4 forest) in
  Map.get positive_encoding 4 (UnionFind.parents compressed) = Some 1%positive /\
  UnionFind.ranks compressed = UnionFind.ranks forest /\
  fst (UnionFind.equivb positive_encoding 2 4 compressed) = true /\
  fst (UnionFind.equivb positive_encoding 4 9 compressed) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Repeated and reflexive unions preserve classes and add an isolated key to support. *)
Example union_find_repeated_unions :
  let uf := UnionFind.union positive_encoding 9 9
    (UnionFind.union positive_encoding 2 4 forest) in
  fst (UnionFind.equivb positive_encoding 1 4 uf) = true /\
  fst (UnionFind.equivb positive_encoding 1 9 uf) = false /\
  List.length (UnionFind.keys positive_encoding uf) = 5%nat.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Absent keys remain singleton roots in a fresh forest. *)
Example union_find_absent :
  UnionFind.find positive_encoding 8 UnionFind.make = (8%positive, UnionFind.make) /\
  fst (UnionFind.equivb positive_encoding 8 9 UnionFind.make) = false /\
  UnionFind.keys positive_encoding (@UnionFind.make positive) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Local Open Scope nat_scope.

Definition flat_table : Table.t nat :=
  Table.set [] 10 (Table.set [1%positive; 2%positive] 20 Table.empty).

(** Empty lists are ordinary keys, independent of nonempty and prefix keys. *)
Example table_list_keys :
  Table.get [] flat_table = Some 10 /\
  Table.get [1%positive; 2%positive] flat_table = Some 20 /\
  Table.get [1%positive] flat_table = None /\ Table.size flat_table = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Replacing and removing the empty key leaves other complete keys alone. *)
Example table_update_remove :
  let t := Table.remove [] (Table.set [] 30 flat_table) in
  Table.get [] t = None /\ Table.get [1%positive; 2%positive] t = Some 20 /\ Table.size t = 1 /\
  Table.is_empty (Table.remove [1%positive; 2%positive] t) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
