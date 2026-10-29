(** * Legacy explanations and direct Rewrite production

    These examples distinguish accepted rewriting from missing bindings and malformed steps.
    For example, a guard sees extra bindings and defaults missing other indices to variables.
    Builds on: AnalysesEgraph and RewriteRun. *)

From Stdlib Require Import List PeanoNat NArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph RewriteRun.
From Gaulois.Analyses Require Import AnalysesEgraph.
Import List.ListNotations.

Module ANA6Fixture.

Definition one : term nat := TApp 1 [].

Definition times (x y : term nat) : term nat := TApp 0 [x; y].

Definition evaluate (op : nat) (args : list nat) : option nat :=
  match op, args with
  | 0, [x; y] => Some (x * y)
  | 1, [] => Some 1
  | _, _ => None
  end.

Definition multiply_one : rewrite_rule nat :=
  RewriteRule (times (TVar 0) one) (TVar 0) (fun _ => true).

Definition rules : list (rewrite_rule nat) := [multiply_one].

Definition input : term nat := times (TVar 0) one.

Definition root_step (forward : bool) (bindings : list (term nat)) : rewrite_step nat :=
  RewriteStep [] 0 forward bindings.

Definition rhs_only : list (rewrite_rule nat) :=
  [RewriteRule (TVar 0) (TVar 1) (fun _ => true)].

Definition absent_guard : rewrite_rule nat :=
  RewriteRule (TVar 0) (TVar 0) (fun sub => term_eqb nat_encoding (sub 5) (TVar 5)).

Definition extra_guard : rewrite_rule nat :=
  RewriteRule (TVar 0) (TVar 0) (fun sub => term_eqb nat_encoding (sub 1) (TVar 9)).

Example multiplication_rule_sound : Forall (rule_sound evaluate (fun _ => True)) rules.
Proof.
  constructor; [|constructor]; intros sub Hguard env Hok.
  change (denote evaluate env (times (sub 0) one) = denote evaluate env (sub 0)).
  unfold times at 1.
  rewrite denote_binary.
  change (match denote evaluate env (sub 0) with
    | Some n => Some (n * 1)
    | None => None
    end = denote evaluate env (sub 0)).
  destruct (denote evaluate env (sub 0)); [rewrite Nat.mul_1_r|]; reflexivity.
Qed.

End ANA6Fixture.
Import ANA6Fixture.

Example explanation_reflexive : check_explanation nat_encoding rules input input [] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_forward :
  check_explanation nat_encoding rules (times (TVar 3) one) (TVar 3)
    [root_step true [TVar 3]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_backward :
  check_explanation nat_encoding rules (TVar 3) (times (TVar 3) one)
    [root_step false [TVar 3]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_nested_position :
  check_explanation nat_encoding rules (times input one) input
    [RewriteStep [0] 0 true [TVar 0]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_invalid_rule :
  replay nat_encoding rules input [RewriteStep [] 1 true [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_wrong_instance :
  replay nat_encoding rules input [root_step true [TVar 1]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_invalid_position :
  replay nat_encoding rules input [RewriteStep [2] 0 true [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_position_below_variable :
  replay nat_encoding rules input [RewriteStep [0; 0] 0 true [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_missing_lhs :
  replay nat_encoding rules input [root_step true []] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_missing_lhs_backward :
  replay nat_encoding rules (TVar 0) [root_step false []] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_missing_rhs :
  replay nat_encoding rhs_only (TVar 0) [root_step true [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_missing_rhs_backward :
  replay nat_encoding rhs_only (TVar 1) [root_step false [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_false_guard :
  replay nat_encoding [RewriteRule (TVar 0) (TVar 0) (fun _ => false)] (TVar 0)
    [root_step true [TVar 0]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_absent_guard_index :
  check_explanation nat_encoding [absent_guard] (TVar 2) (TVar 2)
    [root_step true [TVar 2]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_extra_guard_binding :
  check_explanation nat_encoding [extra_guard] (TVar 2) (TVar 2)
    [root_step true [TVar 2; TVar 9]] = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example explanation_absent_extra_guard_binding :
  replay nat_encoding [extra_guard] (TVar 2) [root_step true [TVar 2]] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example variables_preserve_order_and_duplicates :
  term_vars (times (TVar 3) (times (TVar 0) (TVar 3))) = [3; 0; 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example absent_bindings_preserve_variable :
  legacy_subst [one] 5 = TVar 5 /\ legacy_subst_bound [one] (TVar 5) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example equivalence_includes_none :
  equiv_term evaluate (fun _ => True) (TApp 2 []) (TApp 3 []).
Proof.
  intros env Hok; reflexivity.
Qed.

Example undefined_rewrite_is_accepted :
  check_explanation nat_encoding rules input (TVar 0) [root_step true [TVar 0]] = true /\
  denote evaluate (fun _ => None) input = None /\
  denote evaluate (fun _ => None) (TVar 0) = None.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

Example core_guard_observes_absent_index :
  rw_condition (legacy_rule absent_guard)
    (fun i => if Nat.eqb i 0 then Some (RWVar tt 2) else None) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example core_guard_observes_extra_binding :
  rw_condition (legacy_rule extra_guard)
    (fun i => if Nat.eqb i 0 then Some (RWVar tt 2)
      else if Nat.eqb i 1 then Some (RWVar tt 9) else None) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example optimise_strictly_cheaper :
  optimise nat_encoding rules (fun _ => 1) 100%positive input = Some (TVar 0) /\
  term_cost (fun _ => 1) (TVar 0 : term nat) < term_cost (fun _ => 1) input.
Proof.
  vm_compute; split; [reflexivity|repeat constructor].
Qed.

Example extraction_retains_positional_certificate :
  extract (fun _ => 1) (saturate nat_encoding rules 10%positive input) input =
    Some (TVar 0, [root_step true [TVar 0]]).
Proof.
  vm_compute; reflexivity.
Qed.

Example bounded_one_attempt :
  optimise nat_encoding rules (fun _ => 1) 1%positive (times input one) = Some input.
Proof.
  vm_compute; reflexivity.
Qed.

Example bounded_two_attempts :
  optimise nat_encoding rules (fun _ => 1) 2%positive (times input one) = Some (TVar 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example producer_nested_position :
  optimise nat_encoding rules (fun _ => 1) 2%positive (TApp 2 [input]) = Some (TApp 2 [TVar 0]).
Proof.
  vm_compute; reflexivity.
Qed.

Example producer_without_rules :
  optimise nat_encoding [] (fun _ => 1) 100%positive input = Some input.
Proof.
  vm_compute; reflexivity.
Qed.

Example producer_invariants :
  let eg := saturate nat_encoding rules 10%positive input in
  rw_graph_wf legacy_signature (legacy_graph eg) /\
  rw_graph_sound legacy_signature (legacy_admissible evaluate (fun _ => True))
    (map legacy_rule rules) (legacy_graph eg) /\
  rw_productive (legacy_graph eg) /\
  exists c, legacy_root eg = Some c /\ rw_represents (legacy_graph eg) c (legacy_embed input).
Proof.
  apply legacy_saturate_direct; exact multiplication_rule_sound.
Qed.

Example producer_core_represents_simplified_term :
  let eg := saturate nat_encoding rules 10%positive input in
  rw_rep_test nat_encoding unit_encoding nat_encoding (legacy_graph eg)
    (legacy_egraph_root eg) (legacy_embed (TVar 0)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example direct_extraction_semantics :
  equiv_term evaluate (fun _ => True) input (TVar 0) /\
  term_cost (fun _ => 1) (TVar 0 : term nat) <= term_cost (fun _ => 1) input.
Proof.
  eapply (legacy_extract_sound nat_encoding evaluate (fun _ => True)
    rules (fun _ => 1) 10%positive input (TVar 0) [root_step true [TVar 0]]).
  - exact multiplication_rule_sound.
  - vm_compute; reflexivity.
Qed.
