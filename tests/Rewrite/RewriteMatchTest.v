(** * Indexed matcher examples

    These examples distinguish canonical repeated holes, literal variables and sorted shapes.
    For example, two different node derivations of one assignment appear only once.
    Builds on: RewriteMatch, RewriteEgraph and RewriteRebuild. *)

From Stdlib Require Import List Bool PArith PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteRebuild RewriteMatch.
Import List.ListNotations.

Bind Scope positive_scope with rw_id.

Definition match_fixture : rw_graph nat bool nat :=
  RwGraph [1; 2; 3]%positive [1; 2; 3; 4; 5; 6; 7; 8]%positive
    (Map.of_list positive_encoding [(1, 1); (2, 2); (3, 3); (4, 1)]%positive)
    (Map.of_list positive_encoding [(1%positive, false); (2%positive, false);
      (3%positive, false); (4%positive, false)])
    (Map.of_list positive_encoding
      [(1%positive, (1%positive, RWNVar false 0));
       (2%positive, (2%positive, RWNVar false 1));
       (3%positive, (3%positive, RWNApp false 0 [1; 1]%positive));
       (4%positive, (3%positive, RWNApp false 0 [1; 2]%positive));
       (5%positive, (3%positive, RWNApp false 1 [1; 3]%positive));
       (6%positive, (3%positive, RWNApp false 1 [2; 3]%positive));
       (7%positive, (3%positive, RWNApp false 0 [4; 1]%positive));
       (8%positive, (3%positive, RWNApp false 2 [1; 2]%positive))]).

Definition match_compute := rw_match nat_encoding bool_encoding nat_encoding nat_encoding.

Definition match_repeated : rw_pattern nat bool nat nat :=
  RWPApp false 0 [RWHole false 0; RWHole false 0].

Definition match_nested : rw_pattern nat bool nat nat :=
  RWPApp false 1 [RWHole false 0;
    RWPApp false 0 [RWHole false 0; RWHole false 1]].

Example holes_preserve_order_and_repetitions : rwp_holes match_nested = [0; 0; 1].
Proof.
  reflexivity.
Qed.

Example repeated_holes_compare_canonical_aliases :
  map (Map.elements) (match_compute match_fixture 3 match_repeated) = [[(0, 1%positive)]].
Proof.
  vm_compute; reflexivity.
Qed.

Example repeated_holes_reject_distinct_classes :
  match_compute match_fixture 3
    (RWPApp false 2 [RWHole false 0; RWHole false 0]) = [] /\
  length (match_compute match_fixture 3
    (RWPApp false 2 [RWHole false 0; RWHole false 1])) = 1.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example literal_variables_remain_distinct :
  match_compute match_fixture 1 (RWPVar false 0) = [Map.empty] /\
  match_compute match_fixture 1 (RWPVar false 1) = [].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example sort_mismatches_rejected :
  match_compute match_fixture 1 (RWHole true 0) = [] /\
  match_compute match_fixture 1 (RWPVar true 0) = [] /\
  match_compute match_fixture 3 (RWPApp true 0 [RWHole false 0; RWHole false 1]) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example missing_classes_operators_and_wrong_arity_rejected :
  match_compute match_fixture 99 (RWHole false 0) = [] /\
  match_compute match_fixture 3 (RWPApp false 99 [RWHole false 0; RWHole false 1]) = [] /\
  match_compute match_fixture 3 (RWPApp false 0 [RWHole false 0]) = [].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition match_has_binding (h : nat) (c : rw_id) (a : rw_assignment nat) : bool :=
  match Map.get nat_encoding h a with
  | Some actual => Pos.eqb actual c
  | None => false
  end.

Example parent_index_keeps_multiple_assignments :
  let results := match_compute match_fixture 3 match_nested in
  length results = 2 /\
  existsb (fun a => match_has_binding 0 1 a && match_has_binding 1 1 a) results = true /\
  existsb (fun a => match_has_binding 0 1 a && match_has_binding 1 2 a) results = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example finite_patterns_match_cycles :
  let p := RWPApp false 1 [RWHole false 0; match_nested] in
  length (match_compute match_fixture 3 p) = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Definition match_signature : rw_signature nat bool nat :=
  RwSignature _ _ _ (fun _ => Some false)
    (fun _ sorts result => negb result && forallb negb sorts).

Definition match_term : rw_term nat bool nat :=
  RWApp false 1 [RWVar false 0; RWApp false 0 [RWVar false 0; RWVar false 1]].

Definition match_added := rw_add nat_encoding bool_encoding nat_encoding rw_empty match_term.

Definition match_graph := rw_rebuild nat_encoding bool_encoding nat_encoding (fst match_added).

Definition match_root := snd match_added.

Definition match_sub (h : nat) : option (rw_term nat bool nat) :=
  if Nat.eq_dec h 0 then Some (RWVar false 0) else
    if Nat.eq_dec h 1 then Some (RWVar false 1) else None.

Example match_term_is_typed : rw_typed match_signature match_term.
Proof.
  apply rw_typed_app; [|reflexivity]; constructor.
  - apply rw_typed_var; reflexivity.
  - constructor; [|constructor]; apply rw_typed_app; [|reflexivity]; constructor.
    + apply rw_typed_var; reflexivity.
    + constructor; [apply rw_typed_var; reflexivity|constructor].
Qed.

Example match_graph_is_prepared :
  rw_graph_wf match_signature match_graph /\ rw_clean match_graph /\
  rw_represents match_graph match_root match_term.
Proof.
  pose proof (rw_add_correct nat_encoding bool_encoding nat_encoding match_signature
    (fun _ : rw_semantics nat bool nat unit => True)
    ([] : list (rw_rule nat bool nat unit)) rw_empty match_term
    (rw_empty_wf match_signature) (rw_empty_sound match_signature _ _)
    rw_empty_productive match_term_is_typed) as Hadded.
  change (rw_graph_wf match_signature (fst match_added) /\
    rw_graph_sound match_signature (fun _ : rw_semantics nat bool nat unit => True)
      ([] : list (rw_rule nat bool nat unit)) (fst match_added) /\
    rw_productive (fst match_added) /\ rw_extends rw_empty (fst match_added) /\
    rw_represents (fst match_added) match_root match_term) in Hadded.
  destruct Hadded as [Hwf [Hsound [Hproductive [Hextends Hrepr]]]].
  destruct (rw_rebuild_correct nat_encoding bool_encoding nat_encoding match_signature
    (fun _ : rw_semantics nat bool nat unit => True)
    ([] : list (rw_rule nat bool nat unit)) (fst match_added) Hwf Hsound Hproductive)
    as [Hwf' [Hsound' [Hproductive' [Hclean Hextends']]]].
  split; [exact Hwf'|]; split; [exact Hclean|apply Hextends'; exact Hrepr].
Qed.

Example nontrivial_match_is_computed :
  length (match_compute match_graph match_root match_nested) = 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example nontrivial_match_is_covered_and_sound :
  exists a, In a (match_compute match_graph match_root match_nested) /\
    rw_covers nat_encoding match_graph match_nested a match_sub /\
    rw_represents match_graph match_root match_term.
Proof.
  destruct match_graph_is_prepared as [Hwf [Hclean Hrepr]].
  assert (Htyped : rwp_typed match_signature
    (fun h => option_map rw_sort (match_sub h)) match_nested).
  { apply rwp_typed_app; [|reflexivity]; constructor.
    - apply rwp_typed_hole; reflexivity.
    - constructor; [|constructor]; apply rwp_typed_app; [|reflexivity]; constructor.
      + apply rwp_typed_hole; reflexivity.
      + constructor; [apply rwp_typed_hole; reflexivity|constructor]. }
  destruct (rw_match_complete nat_encoding bool_encoding nat_encoding nat_encoding
    match_signature match_graph match_root match_nested match_sub match_term Hwf Hclean
    Htyped eq_refl Hrepr) as [a [Hin Hcover]].
  exists a; split; [exact Hin|]; split; [exact Hcover|].
  exact (rw_match_sound nat_encoding bool_encoding nat_encoding nat_encoding
    match_signature match_graph match_root match_nested a match_sub match_term
    Hwf Hin Hcover eq_refl).
Qed.

(** The old completeness premises permit this wrong-sort hole instantiation. *)
Example completeness_needs_hole_sort_agreement :
  rw_graph_wf match_signature match_graph /\ rw_clean match_graph /\
  rw_represents match_graph 2 (RWVar false 0) /\
  rw_instantiate match_sub (RWHole true 0) = Some (RWVar false 0) /\
  match_compute match_graph 2 (RWHole true 0) = [].
Proof.
  destruct match_graph_is_prepared as [Hwf [Hclean Hrepr]].
  split; [exact Hwf|]; split; [exact Hclean|]; split.
  - apply (rw_repr_var _ 2 2 2 2 false 0); vm_compute; reflexivity.
  - vm_compute; split; reflexivity.
Qed.
