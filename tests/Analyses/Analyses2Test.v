(** * Structured catalogue regressions

    These computations distinguish valid loop certificates, observer coverage and static counts.
    For example, two operands in a loop body count twice even though the loop may run forever.
    Builds on: AnalysesStructured, AnalysesCensus and the While region algebra. *)

From Stdlib Require Import List Bool NArith ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset.
From Gaulois.Views Require Import ViewsSkeleton ViewsStructured ViewsRegion ViewsGraph.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesStructured AnalysesCensus.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSkeleton
  ExamplesWhileViews ExamplesWhileAnalyses.
Import List.ListNotations Skeleton.

Definition catalogue_vars : skel_vars nat unit nat :=
  {| atom_uses := fun x => [x; x];
     atom_defs := fun _ => [];
     atom_trap_uses := fun _ => [];
     guard_uses := fun _ => [] |}.

Definition catalogue_empty : Skeleton.stmt nat unit := Jump 0.
Definition catalogue_loop : Skeleton.stmt nat unit := Loop (Atom 7).
Definition catalogue_nested : Skeleton.stmt nat unit :=
  Block (Seq (Atom 2) (Loop (Seq (Atom 7) (JumpIf tt 1)))).

Definition catalogue_top (prog : Skeleton.stmt nat unit) :
    skel_set nat_encoding catalogue_vars prog :=
  top_value (finite_powerset_top nat_encoding (skel_universe nat_encoding catalogue_vars prog)).

Definition catalogue_cert (prog : Skeleton.stmt nat unit) :=
  certificate_of nat_encoding catalogue_vars prog (fun _ => catalogue_top prog).

Example certificate_no_heads_accepts :
  certificate_check nat_encoding catalogue_vars catalogue_empty [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_loop_accepts :
  certificate_check nat_encoding catalogue_vars catalogue_loop
    (catalogue_cert catalogue_loop) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_nested_accepts :
  certificate_check nat_encoding catalogue_vars catalogue_nested
    (catalogue_cert catalogue_nested) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_missing_head_rejects :
  certificate_check nat_encoding catalogue_vars catalogue_loop [] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_wrong_head_rejects :
  certificate_check nat_encoding catalogue_vars catalogue_loop
    [(PEntry [], catalogue_top catalogue_loop)] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_duplicate_head_rejects :
  certificate_check nat_encoding catalogue_vars catalogue_loop
    (catalogue_cert catalogue_loop ++ catalogue_cert catalogue_loop) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition catalogue_two_loops : Skeleton.stmt nat unit := Seq (Loop (Atom 2)) (Loop (Atom 7)).

Example certificate_two_heads_accepts :
  certificate_check nat_encoding catalogue_vars catalogue_two_loops
    (catalogue_cert catalogue_two_loops) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_reordered_heads_rejects :
  certificate_check nat_encoding catalogue_vars catalogue_two_loops
    (rev (catalogue_cert catalogue_two_loops)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example certificate_insufficient_fact_rejects :
  certificate_check nat_encoding catalogue_vars catalogue_loop
    [(PEntry [DBody], bot (skel_lattice nat_encoding catalogue_vars catalogue_loop))] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example replay_counts_every_point :
  replay_live nat_encoding catalogue_vars catalogue_loop (catalogue_cert catalogue_loop)
    (fun count _ _ => S count) 0 = Some 4.
Proof.
  vm_compute; reflexivity.
Qed.

Example replay_covers_exact_point_set :
  option_map (fun seen => FinSet.subset skel_point_encoding seen
    (FinSet.of_list skel_point_encoding (skel_nodes catalogue_nested)) &&
    FinSet.subset skel_point_encoding
      (FinSet.of_list skel_point_encoding (skel_nodes catalogue_nested)) seen)
    (replay_live nat_encoding catalogue_vars catalogue_nested (catalogue_cert catalogue_nested)
      (fun seen point _ => FinSet.add skel_point_encoding point seen) FinSet.empty) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example replay_sees_nonempty_expanded_fact :
  replay_live nat_encoding catalogue_vars catalogue_loop (catalogue_cert catalogue_loop)
    (fun seen _ fact => seen || fmem nat_encoding 7 fact) false = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example replay_rejected_certificate_is_none :
  replay_live nat_encoding catalogue_vars catalogue_loop [] (fun count _ _ => S count) 0 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example census_loop_duplicates :
  Map.get nat_encoding 7
    (occurrence_census nat_encoding (fun x => [x; x]) catalogue_loop) = Some 2%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example census_nested_counts :
  Map.get nat_encoding 7
    (occurrence_census nat_encoding (fun x => [x; x; 7]) catalogue_nested) = Some 4%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example census_absent_key :
  Map.get nat_encoding 99
    (occurrence_census nat_encoding (fun x => [x; x]) catalogue_nested) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example census_empty_syntax :
  Map.get nat_encoding 7 (occurrence_census nat_encoding (fun x => [x]) catalogue_empty) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition catalogue_regions : Skeleton.stmt atom expr :=
  Block (Seq (Jump 0) (Loop (JumpTable (EConst 0%Z) [2; 0; 2] 3))).

Example region_product_root :
  Map.get position_encoding [] (region_table (while_region_alg SSkip) catalogue_regions) =
    Some (true, [1; 0; 0]).
Proof.
  vm_compute; reflexivity.
Qed.

Example region_product_inner_loop :
  Map.get position_encoding [DBody; DSecond]
    (region_table (while_region_alg SSkip) catalogue_regions) = Some (false, [2; 1; 1]).
Proof.
  vm_compute; reflexivity.
Qed.

Example region_invalid_position :
  Map.get position_encoding [DFirst]
    (region_table (while_region_alg SSkip) catalogue_regions) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition catalogue_size_alg : summary_algebra nat unit nat :=
  {| on_atom := fun _ => 1;
     on_seq := fun x y => S (x + y);
     on_if := fun _ x y => S (x + y);
     on_block := S;
     on_loop := S;
     on_jump := fun _ => 1;
     on_jump_if := fun _ _ => 1;
     on_jump_table := fun _ _ _ => 1 |}.

Example region_other_carrier :
  Map.get position_encoding [DBody; DSecond]
    (region_table catalogue_size_alg catalogue_nested) = Some 4.
Proof.
  vm_compute; reflexivity.
Qed.
