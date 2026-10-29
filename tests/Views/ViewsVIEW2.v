(** * Structured skeleton boundary examples

    These examples compute nested labels, continuation returns and action-sensitive constraints.
    For example, a jump through an inner loop exits the surrounding block at relative depth one.
    Builds on: ViewsSkeleton, ViewsStructured, OrderBasic and FixpointSystem. *)

From Stdlib Require Import List Bool Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderBasic OrderConcrete.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Views Require Import
  ViewsSemantics ViewsGraph ViewsAgreement ViewsSkeleton ViewsStructured.
Import List.ListNotations Skeleton.

Definition nested_program : stmt nat nat :=
  Block (Seq (Atom 0) (Loop (If 2 (Jump 1) (Jump 0)))).

Definition test_client : skeleton_client nat nat nat nat :=
  {| init_store := fun _ => True;
     atom_step := fun a st l st' => a = 0 /\ l = [st] /\ st' = S st;
     atom_trap := fun a _ => a = 1;
     atom_stop := fun a _ => 2 <= a;
     guard_bool := fun g _ =>
       match g with
       | 0 => None
       | 1 => Some false
       | _ => Some true
       end;
     guard_index := fun g st => if g =? 0 then None else Some st;
     jump_effect := fun _ _ st st' => st' = st |}.

Example test_client_lawful : skeleton_client_laws test_client.
Proof.
  constructor.
  - intros p n st; exists st; reflexivity.
  - intros [|[|a]] st.
    + left; exists [st], (S st); repeat split; reflexivity.
    + right; left; reflexivity.
    + right; right; cbn; auto with arith.
  - intros a st Htrap [l [st' [Hatom _]]]; cbn in Htrap; congruence.
  - intros a st Hstop [l [st' [Hatom _]]]; cbn in Hstop; subst a; inversion Hstop.
  - intros a st [Htrap Hstop]; cbn in Htrap, Hstop; lia.
Qed.

Example nested_labels_valid : labels_ok 0 nested_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example top_jump_invalid : labels_ok 0 (@Jump nat nat 0) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example table_checks_every_label :
  labels_ok 0 (@Block nat nat (JumpTable 1 [0; 1] 0)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_positions : positions nested_program =
  [[]; [DBody]; [DBody; DFirst]; [DBody; DSecond]; [DBody; DSecond; DBody];
   [DBody; DSecond; DBody; DFirst]; [DBody; DSecond; DBody; DSecond]].
Proof.
  vm_compute; reflexivity.
Qed.

Example nested_label_destinations :
  label_point nested_program [DBody; DSecond; DBody; DFirst] 0 =
    Some (PEntry [DBody; DSecond; DBody]) /\
  label_point nested_program [DBody; DSecond; DBody; DFirst] 1 = Some (PExit []) /\
  label_point nested_program [DBody; DSecond; DBody; DFirst] 2 = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example labels_at_valid_proper_prefixes :
  label_point (@Block nat nat (Atom 0)) [DBody; DFirst] 0 = Some (PExit []) /\
  label_point (@Block nat nat (Atom 0)) [DFirst] 0 = Some (PExit []) /\
  label_point (@Loop nat nat (Atom 0)) [DSecond] 0 = Some (PEntry [DBody]) /\
  label_point (@Block nat nat (Atom 0)) [] 0 = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example resume_skips_administrative_frames :
  resume 1 [FJoin [DBody; DSecond; DBody]; FLoop [DBody; DSecond];
    FJoin [DBody]; FBlock []] 6 = Some (Ret [] [] 6).
Proof.
  vm_compute; reflexivity.
Qed.

Example resume_restarts_loop :
  resume 0 [FSeq [DBody]; FLoop []; FBlock []] 7 =
    Some (Go [DBody] [FLoop []; FBlock []] 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example seq_return_edge :
  skel_out nested_program (PExit [DBody; DFirst]) =
    [(PEntry [DBody; DSecond], [])].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_return_edge :
  skel_out nested_program (PExit [DBody; DSecond; DBody]) =
    [(PEntry [DBody; DSecond; DBody], [])].
Proof.
  vm_compute; reflexivity.
Qed.

Example branch_return_edge :
  skel_out nested_program (PExit [DBody; DSecond; DBody; DFirst]) =
    [(PExit [DBody; DSecond; DBody], [])].
Proof.
  vm_compute; reflexivity.
Qed.

Example block_return_edge :
  skel_out nested_program (PExit [DBody]) = [(PExit [], [])].
Proof.
  vm_compute; reflexivity.
Qed.

Definition table_program : stmt nat nat := Block (Loop (JumpTable 1 [0; 1; 0] 1)).

Example table_parallel_slots :
  skel_out table_program (PEntry [DBody; DBody]) =
    [(PEntry [DBody; DBody], [AIndexIs 1 0; AJump [DBody; DBody] 0]);
     (PExit [], [AIndexIs 1 1; AJump [DBody; DBody] 1]);
     (PEntry [DBody; DBody], [AIndexIs 1 2; AJump [DBody; DBody] 0]);
     (PExit [], [AIndexAtLeast 1 3; AJump [DBody; DBody] 1])].
Proof.
  vm_compute; reflexivity.
Qed.

Example table_encoding_preserves_slots :
  encode skel_edge_encoding (@SkelEdge nat nat (PEntry [DBody; DBody]) 0) <>
    encode skel_edge_encoding (@SkelEdge nat nat (PEntry [DBody; DBody]) 2).
Proof.
  vm_compute; discriminate.
Qed.

Example missing_taken_label_keeps_skip :
  skel_out (@JumpIf nat nat 2 0) (PEntry []) = [(PExit [], [AGuard 2 false])].
Proof.
  vm_compute; reflexivity.
Qed.

Example loop_head_inventory :
  loop_heads nested_program = [PEntry [DBody; DSecond; DBody]] /\
  is_loop_head nested_program (PEntry [DBody; DSecond; DBody]) = true /\
  is_loop_head nested_program (PEntry [DBody]) = false /\
  is_loop_head nested_program (PExit [DBody; DSecond; DBody]) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example final_and_failure_endings :
  final (skeleton_endings nested_program test_client) (Ret [] [] 6) /\
  trapped (skeleton_endings (Atom 1) test_client) (Go [] [] 0) /\
  stopped (skeleton_endings (Atom 2) test_client) (Go [] [] 0) /\
  trapped (skeleton_endings (If 0 (Atom 0) (Atom 0)) test_client) (Go [] [] 0).
Proof.
  vm_compute; repeat split; auto.
Qed.

Definition order_transfer (x : action nat nat) (f : nat) : nat :=
  match x with
  | AIndexIs _ _ => S f
  | AJump _ _ => 2 * f
  | _ => f
  end.

Example action_orders :
  edge_fwd table_program order_transfer (SkelEdge (PEntry [DBody; DBody]) 0) 3 = 8 /\
  edge_bwd table_program order_transfer (SkelEdge (PEntry [DBody; DBody]) 0) 3 = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dense_dependency_directions :
  System.deps (skeleton_forward_static bool_lattice table_program false (fun _ f => f))
    (Flow (SkelEdge (PEntry [DBody; DBody]) 1)) = [PEntry [DBody; DBody]] /\
  System.deps (skeleton_backward_static table_program (fun _ => false) (fun _ f => f))
    (Flow (SkelEdge (PEntry [DBody; DBody]) 1)) = [PExit []].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example nested_execution : exec (skeleton_semantics nested_program test_client)
  (Go [] [] 5) [5] (Ret [] [] 6).
Proof.
  change (exec (skeleton_semantics nested_program test_client)
    (Go [] [] 5) ([] ++ [5]) (Ret [] [] 6)).
  eapply exec_step; [eapply step_block; reflexivity|].
  change (exec (skeleton_semantics nested_program test_client)
    (Go [DBody] [FBlock []] 5) ([] ++ [5]) (Ret [] [] 6)).
  eapply exec_step; [eapply step_seq; reflexivity|].
  change (exec (skeleton_semantics nested_program test_client)
    (Go [DBody; DFirst] [FSeq [DBody]; FBlock []] 5) ([5] ++ []) (Ret [] [] 6)).
  eapply exec_step.
  - eapply step_atom; [reflexivity|repeat split; reflexivity].
  - change (exec (skeleton_semantics nested_program test_client)
      (Ret [DBody; DFirst] [FSeq [DBody]; FBlock []] 6) ([] ++ []) (Ret [] [] 6)).
    eapply exec_step; [apply step_ret_seq|].
    eapply exec_step with (l := []) (tr := []); [eapply step_loop; reflexivity|].
    eapply exec_step with (l := []) (tr := []);
      [eapply step_if with (b := true); reflexivity|].
    eapply exec_step with (l := []) (tr := []); [eapply step_jump; reflexivity|constructor].
Qed.

Example nested_progress_instance :
  ~ stuck (skeleton_semantics nested_program test_client)
    (skeleton_endings nested_program test_client) (Go [] [] 5).
Proof.
  eapply skeleton_not_stuck; [reflexivity|exact test_client_lawful|].
  exists (Go [] [] 5), []; split; [exists 5; split; [reflexivity|exact I]|constructor].
Qed.

(** * Prepared-index boundaries *)

Example indexed_parallel_slots_and_default :
  Graph.out (skeleton_graph table_program) (PEntry [DBody; DBody]) =
    map (SkelEdge (PEntry [DBody; DBody])) [0; 1; 2; 3] /\
  skel_to table_program (SkelEdge (PEntry [DBody; DBody]) 2) =
    PEntry [DBody; DBody] /\
  skel_to table_program (SkelEdge (PEntry [DBody; DBody]) 3) = PExit [] /\
  skel_acts table_program (SkelEdge (PEntry [DBody; DBody]) 3) =
    [AIndexAtLeast 1 3; AJump [DBody; DBody] 1].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example indexed_out_of_range_slot :
  skel_to table_program (SkelEdge (PEntry [DBody; DBody]) 4) = PEntry [DBody; DBody] /\
  skel_acts table_program (SkelEdge (PEntry [DBody; DBody]) 4) = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example invalid_positions_have_no_indexed_edges :
  Graph.out (skeleton_graph (@Loop nat nat (Atom 0))) (PEntry [DSecond]) = [] /\
  Graph.out (skeleton_graph (@Loop nat nat (Atom 0))) (PExit [DSecond]) = [] /\
  skel_to (@Loop nat nat (Atom 0)) (SkelEdge (PExit [DSecond]) 0) = PExit [DSecond] /\
  skel_acts (@Loop nat nat (Atom 0)) (SkelEdge (PEntry [DSecond]) 0) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition partially_invalid_table : stmt nat nat := Block (JumpTable 1 [0; 1; 0] 1).

Example indexed_omitted_labels_keep_original_guard_indices :
  Graph.out (skeleton_graph partially_invalid_table) (PEntry [DBody]) =
    [SkelEdge (PEntry [DBody]) 0; SkelEdge (PEntry [DBody]) 1] /\
  skel_to partially_invalid_table (SkelEdge (PEntry [DBody]) 1) = PExit [] /\
  skel_acts partially_invalid_table (SkelEdge (PEntry [DBody]) 1) =
    [AIndexIs 1 2; AJump [DBody] 0] /\
  skel_acts partially_invalid_table (SkelEdge (PEntry [DBody]) 2) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition equal_subtrees_program : stmt nat nat := Seq (Block (Jump 0)) (Block (Jump 0)).

Example equal_subtrees_keep_distinct_occurrences :
  Graph.out (skeleton_graph equal_subtrees_program) (PEntry [DFirst; DBody]) =
    [SkelEdge (PEntry [DFirst; DBody]) 0] /\
  Graph.out (skeleton_graph equal_subtrees_program) (PEntry [DSecond; DBody]) =
    [SkelEdge (PEntry [DSecond; DBody]) 0] /\
  skel_to equal_subtrees_program (SkelEdge (PEntry [DFirst; DBody]) 0) = PExit [DFirst] /\
  skel_to equal_subtrees_program (SkelEdge (PEntry [DSecond; DBody]) 0) = PExit [DSecond] /\
  skel_acts equal_subtrees_program (SkelEdge (PEntry [DFirst; DBody]) 0) =
    [AJump [DFirst; DBody] 0] /\
  skel_acts equal_subtrees_program (SkelEdge (PEntry [DSecond; DBody]) 0) =
    [AJump [DSecond; DBody] 0].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example unlisted_seed_observations :
  let system := skeleton_forward bool_lattice (@Atom nat nat 0) true (fun _ f => negb f) in
  let row := Seed (PEntry [DFirst]) in
  ~ In row (System.constraints system) /\
  System.target system row = PEntry [DFirst] /\
  Query.eval (System.rhs system row) (fun _ => true) = false /\
  Query.reads (System.rhs system row) (fun _ => true) = [] /\
  Query.sides (System.rhs system row) (fun _ => true) = [].
Proof.
  vm_compute; intuition discriminate.
Qed.

Example unlisted_flow_observations :
  let system := skeleton_backward (@Atom nat nat 0) (fun _ => false) (fun _ f => negb f) in
  let row := Flow (SkelEdge (PEntry [DFirst]) 0) in
  ~ In row (System.constraints system) /\
  System.target system row = PEntry [DFirst] /\
  Query.eval (System.rhs system row) (fun _ => true) = true /\
  Query.reads (System.rhs system row) (fun _ => true) = [PEntry [DFirst]] /\
  Query.sides (System.rhs system row) (fun _ => true) = [] /\
  deps (skeleton_backward_static (@Atom nat nat 0) (fun _ => false) (fun _ f => negb f)) row =
    [PEntry [DFirst]].
Proof.
  vm_compute; intuition discriminate.
Qed.

Example malformed_jump_is_stuck :
  ends_as (skeleton_semantics (Jump 0) test_client)
    (skeleton_endings (Jump 0) test_client) EndStuck (Go [] [] 0).
Proof.
  split.
  - intros [l [m Hstep]]; inversion Hstep; subst; cbn in *; discriminate.
  - cbn; tauto.
Qed.

Example malformed_jump_agreement_bisimulation :
  bisimulation (skeleton_semantics (Jump 0) test_client)
    (skeleton_endings (Jump 0) test_client)
    (skeleton_semantics (Jump 0) test_client) (skeleton_endings (Jump 0) test_client)
    (agreeing (skeleton_view (Jump 0) test_client) (store_agreement bool_agree)
      (reachable_state (skeleton_semantics (Jump 0) test_client)) (fun _ => true)).
Proof.
  apply (skeleton_agreement_bisimulation bool_lattice bool_agree (Jump 0) test_client
    (fun _ => true) (fun _ _ => true) (fun _ => true)).
  - apply bool_agree_laws.
  - intros a x y Hsame Ha; symmetry; apply Hsame; exact Ha.
  - intros x a st l st' other Hact Hsame.
    assert (st = other) by (apply Hsame; reflexivity); subst other.
    exists st'; split; [exact Hact|intros _; reflexivity].
  - intros p st other Hsame.
    assert (st = other) by (apply Hsame; reflexivity); subst other; tauto.
  - apply (top_post_solution bool_lattice _ bool_top).
Qed.
