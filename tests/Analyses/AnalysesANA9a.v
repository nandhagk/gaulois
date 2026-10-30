(** * Indexed Andersen regression examples

    Concrete observations cover late edges, subsequent deltas, cycles and empty domains.
    For example, a store edge activated after its source's old fact still delivers that fact.
    Builds on: AnalysesPointsToBase and AnalysesPointsToDelta. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesPointsToBase AnalysesPointsToDelta.
Import List.ListNotations.

(** The last seed is processed first: x's old fact precedes p's edge activation and z's delta. *)
Definition late_ops : list (ptr_op nat nat) :=
  [PCopy 1 3; PAlloc 3 30; PAlloc 2 10; PAlloc 1 20; PStore 2 1; PLoad 4 2].

Definition late_key_encoding := pts_encoding nat_encoding nat_encoding.
Definition late_atom_encoding := sum_encoding nat_encoding late_key_encoding.

Definition late_snapshot (fuel : positive) :=
  PtsDelta.run late_key_encoding late_atom_encoding
    (AndersenDelta.consequences nat_encoding nat_encoding
      (AndersenDelta.index_subscriptions nat_encoding late_ops)) fuel
    (AndersenDelta.initial nat_encoding nat_encoding late_ops).

Definition snapshot_fact fuel k t : bool :=
  FinSet.mem late_atom_encoding (inl t)
    (PtsDelta.row late_key_encoding (PtsDelta.current (late_snapshot fuel)) k).

Definition snapshot_edge fuel s d : bool :=
  FinSet.mem late_atom_encoding (inr d)
    (PtsDelta.row late_key_encoding (PtsDelta.current (late_snapshot fuel)) s).

(** An old source fact exists before the store edge and before the later source delta. *)
Example old_fact_before_activation :
  (snapshot_fact 1 (PVal 1) 20,
   snapshot_edge 1 (PVal 1) (PHeap 10),
   snapshot_fact 1 (PVal 1) 30) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** The new edge is queued while its source still contains only the old fact. *)
Example late_edge_activated :
  (snapshot_edge 2 (PVal 1) (PHeap 10),
   snapshot_fact 2 (PHeap 10) 20,
   snapshot_fact 2 (PVal 1) 30) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Processing the new edge delivers the accumulated old fact before the later delta. *)
Example late_edge_delivers_old_fact :
  (snapshot_fact 4 (PHeap 10) 20,
   snapshot_fact 4 (PHeap 10) 30,
   snapshot_fact 4 (PVal 1) 30) = (true, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** A later source delta also crosses the already activated edge. *)
Example late_edge_delivers_later_delta :
  (snapshot_fact 8 (PVal 1) 30, snapshot_fact 8 (PHeap 10) 30) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** All value and heap rows retain exactly the expected load/store facts. *)
Example late_load_store_result :
  map (fun k => map (fun t => fmem nat_encoding t
    (andersen_delta nat_encoding nat_encoding late_ops k)) [10; 20; 30])
    [PVal 1; PVal 2; PVal 3; PVal 4; PHeap 10; PHeap 20; PHeap 30] =
    [[false; true; true]; [true; false; false]; [false; false; true];
     [false; true; true]; [false; true; true]; [false; false; false];
     [false; false; false]].
Proof.
  vm_compute; reflexivity.
Qed.

(** Cycles and repeated allocation, copy, load and store effects do not duplicate work. *)
Definition cyclic_ops : list (ptr_op nat nat) :=
  [PAlloc 0 7; PCopy 1 0; PCopy 0 1; PCopy 1 0; PAlloc 0 7;
   PStore 1 0; PStore 1 0; PLoad 2 1; PLoad 2 1; PEscape 2].

Example cyclic_duplicate_result :
  map (fun k =>
    (fmem nat_encoding 7 (andersen_delta nat_encoding nat_encoding cyclic_ops k),
     FinSet.size (proj1_sig (andersen_delta nat_encoding nat_encoding cyclic_ops k))))
    [PVal 0; PVal 1; PVal 2; PHeap 7] = [(true, 1); (true, 1); (true, 1); (true, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_events_processed_once :
  FinSet.size (PtsDelta.processed (AndersenDelta.solved nat_encoding nat_encoding cyclic_ops)) = 8.
Proof.
  vm_compute; reflexivity.
Qed.

(** Distinct duplicate instruction occurrences retain their ordered bounded indices. *)
Example duplicate_occurrence_positions :
  map (@proj1_sig _ _)
    (System.constraints (andersen_system nat_encoding nat_encoding cyclic_ops)) =
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_input_result :
  map (fun k => FinSet.size (proj1_sig
    (andersen_delta nat_encoding nat_encoding ([] : list (ptr_op nat nat)) k)))
    [PVal 0; PHeap 0] = [0; 0].
Proof.
  vm_compute; reflexivity.
Qed.

(** The empty carrier has an encoding and needs no invented default pointer. *)
Definition pts_empty_encoding : encoding Empty_set.
Proof.
  refine (Encoding Empty_set (fun x => match x with end) _); intros x; destruct x.
Defined.

Example empty_carrier_constraints :
  System.constraints (andersen_system pts_empty_encoding pts_empty_encoding []) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_carrier_delta_quiescent :
  PtsDelta.pending (AndersenDelta.solved pts_empty_encoding pts_empty_encoding []) = [].
Proof.
  vm_compute; reflexivity.
Qed.
