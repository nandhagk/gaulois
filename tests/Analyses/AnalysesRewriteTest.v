(** * Rewrite client examples

    These examples compute word rewrites and distinguish guards, undefined operations and traps.
    For example, seven divided by itself rewrites to one while zero fails rule registration.
    Builds on: the Rewrite clients and AnalysesEgraph. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Order Require Import OrderConcrete.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph RewriteAnalysis
  RewriteRun RewriteExtract.
From Gaulois.Analyses Require Import AnalysesRewriteDomains AnalysesSsaRewrite AnalysesRewriteWord
  AnalysesEgraph.
From Gaulois.Examples.Ssa Require Import ExamplesSsaTyping ExamplesSsaAnalyses.
Import List.ListNotations.

(** Direct add-zero rewriting extracts the cheaper literal. *)
Example rw_word_add_accepts : rw_word_demo_add = Some (RWApp tt (WordLit 7%Z) []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Direct multiply-one rewriting extracts the cheaper literal. *)
Example rw_word_mul_accepts : rw_word_demo_mul = Some (RWApp tt (WordLit 7%Z) []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Registering the client rotation rule extracts the cheaper literal. *)
Example rw_word_rotate_accepts : rw_word_demo_rotate = Some (RWApp tt (WordLit 7%Z) []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Fact-justified direct division extracts the literal one. *)
Example rw_word_div_accepts : rw_word_demo_div = Some (RWApp tt (WordLit 1%Z) []).
Proof.
  vm_compute; reflexivity.
Qed.

(** A zero singleton fails before any division rule is registered or attempted. *)
Example rw_word_zero_rejected : rw_word_demo_zero = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition rw_word_test_semantics : rw_semantics rw_word_op unit nat Z :=
  RwSemantics rw_word_op unit nat Z (fun _ => Some 7%Z) rw_word_eval.

Example rw_word_environment_inhabited : rw_word_admissible rw_word_test_semantics.
Proof.
  split; [reflexivity|].
  intros variable value Hvalue; injection Hvalue as <-.
  change (0 <= 7 < 4294967296)%Z; lia.
Qed.

Definition rw_word_test_literal (z : Z) : rw_term rw_word_op unit nat := RWApp tt (WordLit z) [].

Definition rw_word_test_source (op : rw_word_op) (z : Z) : rw_term rw_word_op unit nat :=
  RWApp tt op [rw_word_test_literal 7%Z; rw_word_test_literal z].

Definition rw_word_test_bindings : Map.t nat (rw_term rw_word_op unit nat) :=
  Map.set nat_encoding 0%nat (rw_word_test_literal 7%Z) Map.empty.

Definition rw_word_test_application (rule : rw_rule rw_word_op unit nat nat)
    (input : rw_term rw_word_op unit nat) (bindings : Map.t nat (rw_term rw_word_op unit nat)) :=
  let '(g, root) := rw_add rw_word_encoding unit_encoding nat_encoding rw_empty input in
  rw_apply rw_word_encoding unit_encoding nat_encoding nat_encoding rw_word_sig [rule] g
    (RwAttempt 0%nat root bindings).

Definition rw_word_test_accepted (rule : rw_rule rw_word_op unit nat nat)
    (input : rw_term rw_word_op unit nat) (bindings : Map.t nat (rw_term rw_word_op unit nat)) :=
  match rw_word_test_application rule input bindings with
  | Some _ => true
  | None => false
  end.

Example rw_word_all_attempts_accepted :
  [rw_word_test_accepted rw_word_add_zero (rw_word_test_source WordAdd 0%Z) rw_word_test_bindings;
   rw_word_test_accepted rw_word_mul_one (rw_word_test_source WordMul 1%Z) rw_word_test_bindings;
   rw_word_test_accepted rw_word_rotate_zero (rw_word_test_source WordRotl 0%Z)
     rw_word_test_bindings;
   rw_word_test_accepted (rw_word_div_self (rw_word_test_literal 7%Z))
     (rw_word_test_source WordDiv 7%Z) Map.empty] = [true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example rw_word_demo_values_in_admissible_environment :
  rw_word_admissible rw_word_test_semantics /\
  rw_var_value rw_word_test_semantics 0%nat = Some 7%Z /\
  rw_denote rw_word_test_semantics (rw_word_test_source WordAdd 0%Z) = Some 7%Z /\
  rw_denote rw_word_test_semantics (rw_word_test_source WordMul 1%Z) = Some 7%Z /\
  rw_denote rw_word_test_semantics (rw_word_test_source WordRotl 0%Z) = Some 7%Z /\
  rw_denote rw_word_test_semantics (rw_word_test_source WordDiv 7%Z) = Some 1%Z.
Proof.
  split; [exact rw_word_environment_inhabited|].
  vm_compute; repeat split; reflexivity.
Qed.

Example rw_word_demo_costs_strictly_drop :
  (rw_tree_cost (fun _ => 1%nat) rw_word_cost (rw_word_test_literal 7%Z) <
    rw_tree_cost (fun _ => 1%nat) rw_word_cost (rw_word_test_source WordAdd 0%Z))%nat /\
  (rw_tree_cost (fun _ => 1%nat) rw_word_cost (rw_word_test_literal 1%Z) <
    rw_tree_cost (fun _ => 1%nat) rw_word_cost (rw_word_test_source WordDiv 7%Z))%nat.
Proof.
  vm_compute; split; lia.
Qed.

Definition rw_word_test_false_rule : rw_rule rw_word_op unit nat nat :=
  RwRule rw_word_op unit nat nat (rw_holes rw_word_add_zero) (rw_hole_sort rw_word_add_zero)
    (rw_lhs rw_word_add_zero) (rw_rhs rw_word_add_zero) (fun _ => false).

Example rw_word_arbitrary_false_guard_rejected :
  let '(g, root) := rw_add rw_word_encoding unit_encoding nat_encoding rw_empty
    (rw_word_test_source WordAdd 0%Z) in
  rw_rep_test rw_word_encoding unit_encoding nat_encoding g root
    (rw_word_test_source WordAdd 0%Z) = true /\
  rw_word_test_application rw_word_test_false_rule (rw_word_test_source WordAdd 0%Z)
    rw_word_test_bindings = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example rw_word_partial_operator : rw_word_eval WordAdd [7%Z] = None /\
  rw_denote rw_word_test_semantics (RWApp tt WordAdd []) = None.
Proof.
  split; reflexivity.
Qed.

Example rw_word_wrapped_zero_rejected :
  rw_word_register_division 0%Z = None /\ rw_word_register_division 4294967296%Z = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example rw_word_unknown_not_nonzero : ~ rw_word_nonzero rw_word_analysis None.
Proof.
  intros [Hdefined Hnonzero]; exact (Hdefined I).
Qed.

Example rw_word_zero_division_is_not_one :
  ~ rw_equiv rw_word_admissible
    (RWApp tt WordDiv [rw_word_test_literal 0%Z; rw_word_test_literal 0%Z])
    (rw_word_test_literal 1%Z).
Proof.
  intro Hequal; specialize (Hequal rw_word_test_semantics rw_word_environment_inhabited).
  vm_compute in Hequal; discriminate.
Qed.

Example rw_word_registered_division_justified :
  rw_rule_wf rw_word_sig (rw_word_div_self (rw_word_test_literal 7%Z)) /\
  rw_rule_sound rw_word_sig rw_word_admissible (rw_word_div_self (rw_word_test_literal 7%Z)).
Proof.
  split.
  - apply (rw_word_register_division_wf 7%Z); reflexivity.
  - apply (rw_word_register_division_sound 7%Z); reflexivity.
Qed.

Definition rw_word_test_legacy_rule : rewrite_rule rw_word_op :=
  RewriteRule (TApp WordAdd [TVar 0; TApp (WordLit 0%Z) []]) (TVar 0)
    (fun _ => true).

Example rw_word_invalid_external_explanation_rejected :
  check_explanation rw_word_encoding [rw_word_test_legacy_rule]
    (TApp WordAdd [TVar 0; TApp (WordLit 0%Z) []]) (TVar 0)
    [RewriteStep [] 0 true []] = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** The original ANA-6 multiply-by-one acceptance equation is rerun unchanged. *)
Example rw_legacy_multiply_one_still_accepts :
  optimise sop_encoding mul_one_rules unit_cost 100%positive mul_one_term = Some (TVar 0).
Proof.
  vm_compute; reflexivity.
Qed.

Definition rw_word_test_ssa : ssa_view unit Z unit unit nat rw_word_op Z :=
  {| base := {| cfg := Graph.Make [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt);
               point := fun _ => tt;
               taken := fun _ _ _ _ => False;
               stays := fun _ _ _ => False |};
     def := fun _ => Arbitrary;
     home := fun _ => tt;
     params := fun _ => [];
     edge_args := fun _ => [];
     edge_guard := fun _ => [];
     val := fun _ _ => Some 7%Z;
     op_eval := rw_word_eval;
     truth := fun z => negb (Z.eqb z 0%Z) |}.

Example rw_word_ssa_admissible : rw_word_admissible (ssa_rw_semantics rw_word_test_ssa tt).
Proof.
  exact rw_word_environment_inhabited.
Qed.

Lemma rw_word_test_add_typed : rw_typed rw_word_sig (rw_word_test_source WordAdd 0%Z).
Proof.
  apply rw_typed_app; [|reflexivity].
  constructor; [apply rw_typed_app; [constructor|reflexivity]|].
  constructor; [apply rw_typed_app; [constructor|reflexivity]|constructor].
Qed.

Example rw_word_add_preserves_values :
  rw_equiv rw_word_admissible (rw_word_test_source WordAdd 0%Z) (rw_word_test_literal 7%Z).
Proof.
  apply (proj1 (rw_word_demo_run_sound rw_word_add_zero (rw_word_test_source WordAdd 0%Z)
    (rw_word_test_literal 7%Z) rw_word_test_bindings rw_word_add_zero_wf rw_word_add_zero_sound
    rw_word_test_add_typed rw_word_add_accepts)).
Qed.

Example rw_word_add_region_behaviour :
  same_behaviour (ssa_region_semantics rw_word_test_ssa (rw_word_test_source WordAdd 0%Z))
    ssa_region_endings (tt, None)
    (ssa_region_semantics rw_word_test_ssa (rw_word_test_literal 7%Z))
    ssa_region_endings (tt, None).
Proof.
  eapply bisimilar_same_behaviour.
  - apply ssa_region_bisimulation; exact rw_word_add_preserves_values.
  - split; [reflexivity|exact rw_word_ssa_admissible].
Qed.

Example rw_word_successful_region_emits_value :
  step (ssa_region_semantics rw_word_test_ssa (rw_word_test_source WordAdd 0%Z))
    (tt, None) [7%Z] (tt, Some (Some 7%Z)) /\
  final (@ssa_region_endings unit Z) (tt, Some (Some 7%Z)).
Proof.
  split; [repeat split; reflexivity|exists 7%Z; reflexivity].
Qed.

Example rw_word_partial_region_traps :
  step (ssa_region_semantics rw_word_test_ssa (RWApp tt WordAdd []))
    (tt, None) [] (tt, Some None) /\ trapped (@ssa_region_endings unit Z) (tt, Some None).
Proof.
  split; [repeat split; reflexivity|reflexivity].
Qed.

Example rw_order_undefined_permitted {A C} (G : concretisation A C) (a : A) :
  rw_order_holds G a None.
Proof.
  exact I.
Qed.

Example rw_word_partial_region_bisimulation :
  bisimulation
    (ssa_region_semantics rw_word_test_ssa
      (RWApp tt WordAdd [RWApp tt WordAdd []; rw_word_test_literal 0%Z])) ssa_region_endings
    (ssa_region_semantics rw_word_test_ssa (RWApp tt WordAdd [])) ssa_region_endings
    (ssa_region_relation rw_word_test_ssa rw_word_admissible).
Proof.
  apply ssa_region_bisimulation; intros sem [Heval Hvars].
  cbn [rw_denote]; now rewrite Heval.
Qed.
