(** * Matched interprocedural tabulation examples

    Computed observations distinguish matching, recursion, zero generation, and absent paths.
    For example, a non-strict weight on an unreachable edge still leaves its target at bottom.
    Builds on: AnalysesInterprocedural and OrderBasic. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Analyses Require Import AnalysesInterprocedural.
Import List.ListNotations.

Definition simple_matched : ip_problem nat nat unit :=
  IpProblem [0; 1; 2] [0] []
    [IpEdge 0 1 (IpCall 0) [(None, None)];
     IpEdge 1 2 (IpReturn 0) [(None, None)]].

Definition simple_matched_rules := IpTab.rules simple_matched nat_encoding (0, None).
Definition simple_matched_encoding := IpTab.fact_encoding nat_encoding unit_encoding.

Definition simple_matched_map :=
  match IpHorn.probe simple_matched_encoding simple_matched_rules 64 with
  | Some m => m
  | None => Map.empty
  end.

Example simple_matched_probe_completed :
  IpHorn.probe simple_matched_encoding simple_matched_rules 64 = Some simple_matched_map.
Proof.
  vm_compute; reflexivity.
Qed.

Example simple_matched_reachable :
  ifds_solve nat_encoding nat_encoding unit_encoding simple_matched 0 None 2 None = true.
Proof.
  change (IpHorn.solve simple_matched_encoding simple_matched_rules (inr (2, None)) = true).
  rewrite (IpHorn.solve_probe _ _ _ _ simple_matched_probe_completed).
  vm_compute; reflexivity.
Qed.

Definition bool_pairs : list (option bool * option bool) :=
  [(None, None); (Some false, Some false); (Some true, Some true)].

Definition recursive_fixture : ip_problem nat nat bool :=
  IpProblem (seq 0 10) [0; 1; 2; 3; 9] [false; true]
    [IpEdge 0 1 IpInternal ((None, Some false) :: bool_pairs);
     IpEdge 1 2 (IpCall 0) bool_pairs;
     IpEdge 2 3 (IpCall 1) bool_pairs;
     IpEdge 3 4 (IpReturn 1) bool_pairs;
     IpEdge 4 5 (IpReturn 0) bool_pairs;
     IpEdge 3 6 (IpReturn 9) bool_pairs;
     IpEdge 1 7 IpInternal ((None, Some false) :: (None, Some true) :: bool_pairs);
     IpEdge 7 8 (IpReturn 9) bool_pairs;
     IpEdge 0 9 (IpReturn 0) bool_pairs;
     IpEdge 2 3 (IpCall 2) bool_pairs;
     IpEdge 3 2 (IpCall 3) ((None, Some true) :: bool_pairs);
     IpEdge 4 3 (IpReturn 3) bool_pairs;
     IpEdge 3 4 (IpReturn 2) bool_pairs;
     IpEdge 2 4 IpInternal bool_pairs].

Lemma bool_fact_in_fixture d : IpTab.valid_fact recursive_fixture d.
Proof.
  destruct d as [[|] |]; cbn; auto.
Qed.

Example recursive_fixture_wf : ip_problem_wf recursive_fixture.
Proof.
  split; [apply seq_NoDup |]; split; [|split].
  - repeat constructor; cbn; intuition congruence.
  - repeat constructor; cbn; intuition congruence.
  - intros e He; cbn [recursive_fixture ip_edges] in He.
    destruct He as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- |
      [<- | [<- | [<- | [<- | [<- | [<- | Hbad]]]]]]]]]]]]]]; try contradiction;
      cbn [ip_source ip_target ip_action ip_pairs recursive_fixture ip_nodes ip_sites bool_pairs
        seq In];
      repeat split; auto 20.
    all: apply bool_fact_in_fixture.
Qed.

Definition recursive_rules := IpTab.rules recursive_fixture nat_encoding (0, None).
Definition recursive_encoding := IpTab.fact_encoding nat_encoding bool_encoding.

Definition recursive_map :=
  match IpHorn.probe recursive_encoding recursive_rules 4096 with
  | Some m => m
  | None => Map.empty
  end.

Example recursive_probe_completed :
  IpHorn.probe recursive_encoding recursive_rules 4096 = Some recursive_map.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma recursive_engine_agrees :
  ifds_solve nat_encoding nat_encoding bool_encoding recursive_fixture 0 None =
    fun n d => lookup recursive_encoding bool_lattice recursive_map (inr (n, d)).
Proof.
  unfold ifds_solve; fold recursive_encoding recursive_rules.
  now rewrite (IpHorn.solve_probe _ _ _ _ recursive_probe_completed).
Qed.

Example matched_nested_recursive_zero_and_unknown_accepted :
  let answer := ifds_solve nat_encoding nat_encoding bool_encoding recursive_fixture 0 None in
  [answer 1 (Some false); answer 3 (Some false); answer 4 (Some false);
   answer 5 (Some false); answer 5 (Some true); answer 2 (Some true);
   answer 7 (Some true); answer 0 None] = repeat true 8.
Proof.
  rewrite recursive_engine_agrees; vm_compute; reflexivity.
Qed.

Example mismatched_unknown_return_empty_stack_and_outside_rejected :
  let answer := ifds_solve nat_encoding nat_encoding bool_encoding recursive_fixture 0 None in
  [answer 6 (Some false); answer 8 (Some true); answer 9 None; answer 10 None] = repeat false 4.
Proof.
  rewrite recursive_engine_agrees; vm_compute; reflexivity.
Qed.

Definition zero_pairs : list (option unit * option unit) := [(None, None)].

Definition weighted_graph : ip_problem nat nat unit :=
  IpProblem (seq 0 11) [0; 1] []
    [IpEdge 0 1 IpInternal zero_pairs;
     IpEdge 0 2 IpInternal zero_pairs;
     IpEdge 1 3 IpInternal zero_pairs;
     IpEdge 2 3 IpInternal zero_pairs;
     IpEdge 4 5 IpInternal zero_pairs;
     IpEdge 0 6 IpInternal zero_pairs;
     IpEdge 6 7 (IpReturn 1) zero_pairs;
     IpEdge 0 8 (IpCall 0) zero_pairs;
     IpEdge 8 9 (IpReturn 0) zero_pairs;
     IpEdge 8 10 (IpReturn 1) zero_pairs].

Definition weight (e : ip_edge nat nat unit) (_ _ : option unit) (a : bool) : bool :=
  if Nat.eqb (ip_source e) 4 || Nat.eqb (ip_target e) 2 ||
    Nat.eqb (ip_target e) 6 || Nat.eqb (ip_target e) 9 then true else a.

Definition weighted_fixture : ide_problem nat nat unit bool :=
  IdeProblem weighted_graph bool_lattice [false; true] weight.

Example weighted_graph_wf : ip_problem_wf weighted_graph.
Proof.
  split; [apply seq_NoDup |]; split; [|split].
  - repeat constructor; cbn; intuition congruence.
  - constructor.
  - intros e He; cbn [weighted_graph ip_edges] in He.
    destruct He as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hbad]]]]]]]]]];
      try contradiction; cbn [ip_source ip_target ip_action ip_pairs weighted_graph ip_nodes
        ip_sites zero_pairs seq In]; repeat split; auto 20.
    all: destruct x as [[] |], y as [[] |]; cbn in *; intuition congruence.
Qed.

Example weighted_fixture_laws : ide_laws weighted_fixture.
Proof.
  constructor.
  - exact weighted_graph_wf.
  - intros []; cbn; auto.
  - exact bool_laws.
  - exact bool_lub.
  - intros e x y a b He Hxy.
    change (equivalent bool_lattice (weight e x y (a || b))
      (weight e x y a || weight e x y b)).
    unfold weight; destruct (Nat.eqb (ip_source e) 4 || Nat.eqb (ip_target e) 2 ||
      Nat.eqb (ip_target e) 6 || Nat.eqb (ip_target e) 9);
      destruct a, b; split; reflexivity.
Qed.

Definition weighted_encoding := IpTab.fact_encoding nat_encoding
  (IdeTab.lifted_encoding unit_encoding bool_encoding).

Definition weighted_rules := IpTab.rules
  (IdeTab.graph unit_encoding bool_encoding weighted_fixture) nat_encoding
  (0, Some (None, IdeTab.domain bool_encoding weighted_fixture)).

Definition weighted_map :=
  match IpHorn.probe weighted_encoding weighted_rules 16384 with
  | Some m => m
  | None => Map.empty
  end.

Example weighted_probe_completed :
  IpHorn.probe weighted_encoding weighted_rules 16384 = Some weighted_map.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma weighted_engine_agrees :
  IdeTab.reachable nat_encoding nat_encoding unit_encoding bool_encoding weighted_fixture 0 None =
    fun n d => lookup weighted_encoding bool_lattice weighted_map (inr (n, d)).
Proof.
  change ((fun n d => IpHorn.solve weighted_encoding weighted_rules (inr (n, d))) =
    fun n d => lookup weighted_encoding bool_lattice weighted_map (inr (n, d))).
  now rewrite (IpHorn.solve_probe _ _ _ _ weighted_probe_completed).
Qed.

Example ide_distinct_paths_unreachable_nonstrict_unknown_and_matched :
  let answer := ide_solve nat_encoding nat_encoding unit_encoding bool_encoding
    weighted_fixture 0 None false in
  map (fun n => answer n None) (seq 0 11) =
    [false; false; true; true; false; false; true; false; false; true; false].
Proof.
  unfold ide_solve, IdeTab.result, IdeTab.contributions.
  rewrite weighted_engine_agrees; vm_compute; reflexivity.
Qed.

Example ide_unreachable_weight_is_nonstrict :
  weight (IpEdge 4 5 IpInternal zero_pairs) None None false = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition weighted_recursive_graph : ip_problem nat nat unit :=
  IpProblem (seq 0 6) [0; 1; 2; 9] []
    [IpEdge 0 1 (IpCall 0) zero_pairs;
     IpEdge 1 2 (IpCall 1) zero_pairs;
     IpEdge 2 1 (IpCall 2) zero_pairs;
     IpEdge 1 3 IpInternal zero_pairs;
     IpEdge 3 2 (IpReturn 2) zero_pairs;
     IpEdge 2 3 (IpReturn 1) zero_pairs;
     IpEdge 3 4 (IpReturn 0) zero_pairs;
     IpEdge 2 5 (IpReturn 9) zero_pairs].

Definition recursive_weight (e : ip_edge nat nat unit) (_ _ : option unit) (a : bool) : bool :=
  match ip_action e with
  | IpCall p => if Nat.eqb p 2 then true else a
  | _ => a
  end.

Definition weighted_recursive_fixture : ide_problem nat nat unit bool :=
  IdeProblem weighted_recursive_graph bool_lattice [false; true] recursive_weight.

Example weighted_recursive_graph_wf : ip_problem_wf weighted_recursive_graph.
Proof.
  split; [apply seq_NoDup |]; split; [|split].
  - repeat constructor; cbn; intuition congruence.
  - constructor.
  - intros e He; cbn [weighted_recursive_graph ip_edges] in He.
    destruct He as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hbad]]]]]]]];
      try contradiction; cbn [ip_source ip_target ip_action ip_pairs weighted_recursive_graph
        ip_nodes ip_sites zero_pairs seq In]; repeat split; auto 20.
    all: destruct x as [[] |], y as [[] |]; cbn in *; intuition congruence.
Qed.

Example weighted_recursive_fixture_laws : ide_laws weighted_recursive_fixture.
Proof.
  constructor.
  - exact weighted_recursive_graph_wf.
  - intros []; cbn; auto.
  - exact bool_laws.
  - exact bool_lub.
  - intros e x y a b He Hxy.
    change (equivalent bool_lattice (recursive_weight e x y (a || b))
      (recursive_weight e x y a || recursive_weight e x y b)).
    unfold recursive_weight; destruct (ip_action e) as [|p|p];
      [|destruct (Nat.eqb p 2)|]; destruct a, b; split; reflexivity.
Qed.

Definition weighted_recursive_rules := IpTab.rules
  (IdeTab.graph unit_encoding bool_encoding weighted_recursive_fixture) nat_encoding
  (0, Some (None, IdeTab.domain bool_encoding weighted_recursive_fixture)).

Definition weighted_recursive_map :=
  match IpHorn.probe weighted_encoding weighted_recursive_rules 16384 with
  | Some m => m
  | None => Map.empty
  end.

Example weighted_recursive_probe_completed :
  IpHorn.probe weighted_encoding weighted_recursive_rules 16384 = Some weighted_recursive_map.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma weighted_recursive_engine_agrees :
  IdeTab.reachable nat_encoding nat_encoding unit_encoding bool_encoding
    weighted_recursive_fixture 0 None =
    fun n d => lookup weighted_encoding bool_lattice weighted_recursive_map (inr (n, d)).
Proof.
  change ((fun n d => IpHorn.solve weighted_encoding weighted_recursive_rules (inr (n, d))) =
    fun n d => lookup weighted_encoding bool_lattice weighted_recursive_map (inr (n, d))).
  now rewrite (IpHorn.solve_probe _ _ _ _ weighted_recursive_probe_completed).
Qed.

Example ide_nested_mutual_recursion_retains_changed_value_and_rejects_mismatch :
  let answer := ide_solve nat_encoding nat_encoding unit_encoding bool_encoding
    weighted_recursive_fixture 0 None false in
  [answer 0 None; answer 1 None; answer 2 None; answer 3 None; answer 4 None; answer 5 None] =
    [false; true; true; true; true; false].
Proof.
  unfold ide_solve, IdeTab.result, IdeTab.contributions.
  rewrite weighted_recursive_engine_agrees; vm_compute; reflexivity.
Qed.

Example ide_recursive_result_bounds_all_matched_paths : forall stack b,
  ide_path weighted_recursive_fixture (0, None, []) false (4, None, stack) b ->
  leb bool_lattice b (ide_solve nat_encoding nat_encoding unit_encoding bool_encoding
    weighted_recursive_fixture 0 None false 4 None) = true.
Proof.
  apply ide_solve_exact; [exact weighted_recursive_fixture_laws | cbn; auto | exact I].
Qed.

Definition generation_graph : ip_problem nat nat unit :=
  IpProblem [0; 1; 2] [0] [tt]
    [IpEdge 0 1 IpInternal [(None, None); (None, Some tt)];
     IpEdge 1 2 (IpCall 0) [(None, None); (Some tt, Some tt)]].

Definition generation_fixture : ide_problem nat nat unit bool :=
  IdeProblem generation_graph bool_lattice [false; true] (fun _ _ _ _ => true).

Definition generation_rules := IpTab.rules
  (IdeTab.graph unit_encoding bool_encoding generation_fixture) nat_encoding
  (0, Some (None, IdeTab.domain bool_encoding generation_fixture)).

Definition generation_map :=
  match IpHorn.probe weighted_encoding generation_rules 4096 with
  | Some m => m
  | None => Map.empty
  end.

Example generation_probe_completed :
  IpHorn.probe weighted_encoding generation_rules 4096 = Some generation_map.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma generation_engine_agrees :
  IdeTab.reachable nat_encoding nat_encoding unit_encoding bool_encoding generation_fixture 0 None =
    fun n d => lookup weighted_encoding bool_lattice generation_map (inr (n, d)).
Proof.
  change ((fun n d => IpHorn.solve weighted_encoding generation_rules (inr (n, d))) =
    fun n d => lookup weighted_encoding bool_lattice generation_map (inr (n, d))).
  now rewrite (IpHorn.solve_probe _ _ _ _ generation_probe_completed).
Qed.

Example ide_zero_generation_and_pending_callee_preserve_reachability :
  let answer := ide_solve nat_encoding nat_encoding unit_encoding bool_encoding
    generation_fixture 0 None false in
  [answer 0 (Some tt); answer 1 (Some tt); answer 2 (Some tt); answer 1 None] =
    [false; true; true; true].
Proof.
  unfold ide_solve, IdeTab.result, IdeTab.contributions.
  rewrite generation_engine_agrees; vm_compute; reflexivity.
Qed.
