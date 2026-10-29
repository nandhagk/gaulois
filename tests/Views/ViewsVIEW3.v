(** * Region-summary boundary examples

    These examples check empty regions, escaping labels and balanced sequence shapes.
    For example, five statements split into groups of two and three rather than a sequence spine.
    Builds on: ViewsRegion and ViewsSkeleton. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Views Require Import ViewsSkeleton ViewsRegion.
Import List.ListNotations Skeleton.

Definition empty_region : stmt (list nat) bool := Atom [].

Example empty_region_inventory : escapes empty_region = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_region_completes : falls (fun _ => true) empty_region = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_region_depths : nesting empty_region = 0 /\ skel_depth empty_region = 0.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition nested_region : stmt nat bool :=
  Block (Seq (Atom 0) (Loop (If true (Jump 1) (Jump 0)))).

Example nested_region_inventory : escapes nested_region = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_region_exits_its_block : falls (Nat.eqb 0) nested_region = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_loop_does_not_fall :
  falls_at (Nat.eqb 0) nested_region [DBody; DSecond] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_region_depths : nesting nested_region = 2 /\ skel_depth nested_region = 4.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example invalid_position_does_not_fall : falls_at (Nat.eqb 0) nested_region [DFirst] = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition escaping_region : stmt nat bool :=
  Seq (Jump 2) (If false (JumpIf true 1) (JumpTable false [0; 3; 1] 2)).

Example escape_order_and_duplicates : escapes escaping_region = [2; 1; 2; 0; 3; 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example crossing_one_label : escapes (Block escaping_region) = [1; 0; 1; 2; 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example crossing_two_labels : escapes (Block (Loop escaping_region)) = [0; 0; 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example inventory_bound_accepts : labels_ok 4 escaping_region = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example inventory_bound_rejects : labels_ok 3 escaping_region = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example sequence_needs_both_children :
  falls (Nat.eqb 0) (@Seq nat bool (Atom 0) (Atom 1)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example either_branch_may_complete :
  falls (Nat.eqb 0) (@If nat bool false (Atom 0) (Jump 0)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example conditional_jump_may_skip : falls (Nat.eqb 0) (@JumpIf nat bool true 7) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example table_never_completes_itself :
  falls (Nat.eqb 0) (@JumpTable nat bool false [0; 1] 2) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition node_count : summary_algebra nat bool nat :=
  {| on_atom := fun _ => 1;
     on_seq := fun x y => S (x + y);
     on_if := fun _ x y => S (x + y);
     on_block := S;
     on_loop := S;
     on_jump := fun _ => 1;
     on_jump_if := fun _ _ => 1;
     on_jump_table := fun _ _ _ => 1 |}.

Example fold_visits_every_constructor :
  summarise node_count
    (Seq (Jump 0) (Seq (Atom 0)
      (If true (Block (JumpIf false 0)) (Loop (JumpTable true [0; 1] 2))))) = 9.
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_sequence_is_itself :
  seq_of_list (@Block nat bool (Atom 0)) [] = Block (Atom 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example odd_sequence_uses_floor_split :
  seq_of_list (@Atom nat bool 0) [Atom 1; Atom 2; Atom 3; Atom 4] =
    Seq (Seq (Atom 0) (Atom 1)) (Seq (Atom 2) (Seq (Atom 3) (Atom 4))).
Proof.
  vm_compute; reflexivity.
Qed.

Example even_sequence_uses_equal_halves :
  seq_of_list (@Atom nat bool 0) [Atom 1; Atom 2; Atom 3] =
    Seq (Seq (Atom 0) (Atom 1)) (Seq (Atom 2) (Atom 3)).
Proof.
  vm_compute; reflexivity.
Qed.

Example eight_atoms_have_depth_three :
  skel_depth (seq_of_list (@Atom nat bool 0)
    [Atom 1; Atom 2; Atom 3; Atom 4; Atom 5; Atom 6; Atom 7]) = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example balanced_sequence_keeps_nested_leaves_and_labels :
  seq_flat (seq_of_list (@Seq nat bool (Atom 0) (Jump 2))
    [Block (Atom 1); Seq (Atom 2) (JumpIf true 1)]) =
    [Atom 0; Jump 2; Block (Atom 1); Atom 2; JumpIf true 1] /\
  escapes (seq_of_list (@Jump nat bool 2) [Block (Jump 1); Loop (Jump 0)]) = [2; 0].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example logarithmic_bound_includes_deepest_leaf :
  skel_depth (seq_of_list nested_region [Atom 0; Atom 1; Atom 2; Atom 3]) = 6 /\
  Nat.log2_up 5 + fold_right Nat.max 0
    (map skel_depth [nested_region; Atom 0; Atom 1; Atom 2; Atom 3]) = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.
