(** * Finite minimum-cost extraction examples

    These fixtures distinguish cost, size, structural ties and absence of finite witnesses.
    For example, a productive zero-cost self-cycle still returns a finite leaf.
    Builds on: RewriteEgraph, RewriteRebuild and RewriteExtract. *)

From Stdlib Require Import List PArith NArith PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteEgraph RewriteRebuild RewriteExtract.
Import List.ListNotations.

Bind Scope positive_scope with rw_id.

Definition extract_signature : rw_signature nat unit nat :=
  RwSignature _ _ _ (fun _ => Some tt) (fun _ _ _ => true).

Definition extract := rw_extract_tree nat_encoding unit_encoding nat_encoding.

Definition extract_leaf : rw_graph nat unit nat := rw_allocate rw_empty 1 (RWNVar tt 7).

Lemma extract_leaf_layout : rw_layout extract_signature extract_leaf.
Proof.
  apply rw_allocate_layout.
  - apply rw_wf_layout, rw_empty_wf.
  - split; reflexivity.
  - reflexivity.
Qed.

Definition extract_unary := rw_allocate extract_leaf 2 (RWNApp tt 3 [1]%positive).

Lemma extract_unary_layout : rw_layout extract_signature extract_unary.
Proof.
  apply rw_allocate_layout.
  - exact extract_leaf_layout.
  - split; reflexivity.
  - exists [tt]; split; [constructor; [reflexivity|constructor]|reflexivity].
Qed.

Definition extract_cycle := rw_merge extract_unary 1 2.

Lemma extract_cycle_wf : rw_graph_wf extract_signature extract_cycle.
Proof.
  apply rw_layout_wf; apply (rw_merge_layout extract_signature extract_unary 1 2 tt).
  - exact extract_unary_layout.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example extract_acyclic_optimum :
  extract (fun v => v) (fun op => op) extract_unary 2 = Some (RWApp tt 3 [RWVar tt 7]).
Proof.
  vm_compute; reflexivity.
Qed.

Example extract_positive_cycle :
  extract (fun v => v) (fun op => op) extract_cycle 1 = Some (RWVar tt 7) /\
  rw_tree_cost (fun v => v) (fun op => op) (RWApp tt 3 [RWVar tt 7]) = 10.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example extract_zero_cost_cycle :
  extract (fun _ => 0) (fun _ => 0) extract_cycle 1 = Some (RWVar tt 7) /\
  extract (fun _ => 0) (fun _ => 0) extract_cycle 2 = Some (RWVar tt 7).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example extract_cycle_minimum :
  forall u, rw_represents extract_cycle 2 u ->
    rw_tree_cost (fun v => v) (fun op => op) (RWVar tt 7) <=
      rw_tree_cost (fun v => v) (fun op => op) u.
Proof.
  exact (proj2 (rw_extract_tree_some nat_encoding unit_encoding nat_encoding extract_signature
    (fun v => v) (fun op => op) extract_cycle 2 (RWVar tt 7) extract_cycle_wf eq_refl)).
Qed.

Definition extract_unproductive := rw_replace extract_leaf 1 1 (RWNApp tt 0 [1]%positive).

Lemma extract_unproductive_layout : rw_layout extract_signature extract_unproductive.
Proof.
  apply (rw_replace_layout extract_signature extract_leaf 1 1 (RWNVar tt 7)).
  - exact extract_leaf_layout.
  - reflexivity.
  - reflexivity.
  - exists [tt]; split; [constructor; [reflexivity|constructor]|reflexivity].
Qed.

Example extract_unproductive_cycle :
  extract (fun _ => 0) (fun _ => 0) extract_unproductive 1 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example extract_unproductive_has_no_witness :
  forall t, ~ rw_represents extract_unproductive 1 t.
Proof.
  apply (proj1 (rw_extract_tree_none nat_encoding unit_encoding nat_encoding extract_signature
    (fun _ => 0) (fun _ => 0) extract_unproductive 1
    (rw_layout_wf extract_signature extract_unproductive extract_unproductive_layout))).
  reflexivity.
Qed.

Definition extract_mixed := rw_allocate extract_unproductive 2 (RWNVar tt 2).

Example extract_mixed_wf : rw_graph_wf extract_signature extract_mixed.
Proof.
  apply rw_layout_wf, rw_allocate_layout.
  - exact extract_unproductive_layout.
  - split; reflexivity.
  - reflexivity.
Qed.

Example extract_productivity_is_per_class :
  extract (fun v => v) (fun op => op) extract_mixed 1 = None /\
  extract (fun v => v) (fun op => op) extract_mixed 2 = Some (RWVar tt 2) /\
  extract (fun v => v) (fun op => op) extract_mixed 3 = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition extract_two_leaves := rw_allocate extract_leaf 2 (RWNVar tt 2).

Lemma extract_two_leaves_layout : rw_layout extract_signature extract_two_leaves.
Proof.
  apply rw_allocate_layout.
  - exact extract_leaf_layout.
  - split; reflexivity.
  - reflexivity.
Qed.

Definition extract_choice_base := rw_allocate extract_two_leaves 3 (RWNApp tt 0 [2]%positive).

Lemma extract_choice_base_layout : rw_layout extract_signature extract_choice_base.
Proof.
  apply rw_allocate_layout.
  - exact extract_two_leaves_layout.
  - split; reflexivity.
  - exists [tt]; split; [constructor; [reflexivity|constructor]|reflexivity].
Qed.

Definition extract_choice := rw_merge extract_choice_base 1 3.

Lemma extract_choice_layout : rw_layout extract_signature extract_choice.
Proof.
  apply (rw_merge_layout extract_signature extract_choice_base 1 3 tt).
  - exact extract_choice_base_layout.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example extract_later_round_improves :
  option_map rw_candidate_tree (rw_tree_get extract_choice
    (rw_tree_rounds nat_encoding unit_encoding nat_encoding (fun v => v) (fun op => op)
      extract_choice 1%N) 1) = Some (RWVar tt 7) /\
  extract (fun v => v) (fun op => op) extract_choice 1 = Some (RWApp tt 0 [RWVar tt 2]) /\
  extract (fun v => v) (fun op => op) extract_choice 3 = Some (RWApp tt 0 [RWVar tt 2]).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example extract_size_precedes_structure :
  extract (fun _ => 0) (fun _ => 0) extract_choice 1 = Some (RWVar tt 7).
Proof.
  vm_compute; reflexivity.
Qed.

Definition extract_choice_cycle_base := rw_allocate extract_choice 4 (RWNApp tt 0 [1]%positive).

Definition extract_choice_cycle := rw_merge extract_choice_cycle_base 1 4.

Example extract_choice_cycle_wf : rw_graph_wf extract_signature extract_choice_cycle.
Proof.
  apply rw_layout_wf; apply (rw_merge_layout extract_signature extract_choice_cycle_base 1 4 tt).
  - apply rw_allocate_layout.
    + exact extract_choice_layout.
    + split; reflexivity.
    + exists [tt]; split; [constructor; [reflexivity|constructor]|reflexivity].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example extract_improves_despite_zero_cost_cycle :
  extract (fun v => v) (fun _ => 0) extract_choice_cycle 1 = Some (RWApp tt 0 [RWVar tt 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition extract_tie := rw_merge extract_two_leaves 1 2.

Definition extract_tie_reordered : rw_graph nat unit nat := rw_merge
  (rw_allocate (rw_allocate rw_empty 2 (RWNVar tt 7)) 1 (RWNVar tt 2)) 1 2.

Example extract_structure_precedes_node_order :
  extract (fun _ => 0) (fun _ => 0) extract_tie 1 = Some (RWVar tt 2) /\
  extract (fun _ => 0) (fun _ => 0) extract_tie_reordered 1 = Some (RWVar tt 2).
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition extract_operator_tie := rw_merge
  (rw_allocate extract_unary 3 (RWNApp tt 1 [1]%positive)) 2 3.

Example extract_operator_structure_breaks_ties :
  extract (fun v => v) (fun _ => 0) extract_operator_tie 2 = Some (RWApp tt 1 [RWVar tt 7]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition extract_duplicated := rw_allocate extract_two_leaves 4 (RWNApp tt 3 [2; 2]%positive).

Example extract_materialized_cost_counts_both_children :
  extract (fun v => v) (fun op => op) extract_duplicated 4 =
    Some (RWApp tt 3 [RWVar tt 2; RWVar tt 2]) /\
  rw_tree_cost (fun v => v) (fun op => op) (RWApp tt 3 [RWVar tt 2; RWVar tt 2]) = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.
