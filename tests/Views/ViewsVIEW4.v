(** * Sparse SSA boundary examples

    These computations exercise sparse rows, guard refinement and parallel phi operands.
    For example, two incoming edge occurrences pass different operands to the same parameter.
    Builds on: ViewsSsa, ViewsRefine, OrderFlat and FixpointCheck. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift OrderFlat.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsRefine.
Import List.ListNotations.

Definition test_truth (n : nat) : bool := negb (Nat.eqb n 0).

Definition test_meet (a b : flat nat) : flat nat :=
  match a, b with
  | FBot, _ | _, FBot => FBot
  | FTop, _ => b
  | _, FTop => a
  | FVal n, FVal m => if Nat.eqb n m then FVal n else FBot
  end.

Definition test_guard (k : guard_kind nat) (n : nat) : bool :=
  match k with
  | GTrue => test_truth n
  | GFalse => negb (test_truth n)
  | GConst m => Nat.eqb n m
  | GNotConst m => negb (Nat.eqb n m)
  end.

Definition test_assume (k : guard_kind nat) (a : flat nat) : flat nat :=
  match a with
  | FBot => FBot
  | FVal n => if test_guard k n then FVal n else FBot
  | FTop =>
    match k with
    | GConst n => FVal n
    | _ => FTop
    end
  end.

Definition test_eval (o : bool) (cs : list nat) : option nat :=
  match o, cs with
  | true, [n; m] => Some (if Nat.eqb n m then 1 else 0)
  | false, [n] => Some n
  | _, _ => None
  end.

Definition test_inverse (o b : bool) (fs : list (flat nat)) : list (flat nat) :=
  match o, b, fs with
  | true, true, [a; a'] => [test_meet a a'; test_meet a' a]
  | false, _, [a] => [test_assume (if b then GTrue else GFalse) a]
  | _, _, _ => fs
  end.

Definition test_domain : sparse_domain (flat nat) nat bool :=
  {| fact_lat := flat_lattice Nat.eqb;
     fact_conc := flat_gamma eq;
     top_fact := FTop;
     op_abs := fun _ _ => FTop;
     assume_value := test_assume;
     assume_args := test_inverse |}.

Definition test_graph : Graph.t nat nat :=
  {| Graph.entries := [0];
     Graph.nodes := [0; 1; 2; 3];
     Graph.out := fun b =>
       match b with
       | 0 => [0; 1]
       | 1 => [2; 3]
       | _ => []
       end;
     Graph.source := fun e => if e <? 2 then 0 else 1;
     Graph.target := fun e =>
       match e with
       | 0 | 1 => 1
       | 2 => 2
       | _ => 3
       end |}.

Definition test_base : graph_view unit unit nat nat :=
  {| cfg := test_graph;
     point := fun _ => 0;
     taken := fun _ _ _ _ => False;
     stays := fun _ _ _ => False |}.

Definition test_view : ssa_view unit unit nat nat nat bool nat :=
  {| base := test_base;
     def := fun x =>
       match x with
       | 0 => Param 0 0
       | 1 => Param 0 1
       | 2 => Param 1 0
       | 3 => Param 1 1
       | 4 => Op true [2; 3]
       | 5 | 6 => Arbitrary
       | 7 => Op false [8]
       | 8 => Param 3 0
       | 9 => Op true [2; 2]
       | _ => Arbitrary
       end;
     home := fun x => if x <? 2 then 0 else if x =? 8 then 3 else 1;
     params := fun b =>
       match b with
       | 0 => [0; 1]
       | 1 => [2; 3]
       | 3 => [8]
       | _ => []
       end;
     edge_args := fun e =>
       match e with
       | 0 => [0; 1]
       | 1 => [1; 0]
       | 3 => [2]
       | _ => []
       end;
     edge_guard := fun e =>
       match e with
       | 0 => [Condition 0 (GConst 3)]
       | 1 => [Condition 0 (GConst 4)]
       | 2 => [Condition 4 GTrue]
       | 3 => [Condition 4 GFalse]
       | 4 => [Condition 9 GTrue]
       | 5 => [Condition 2 (GConst 7); Condition 4 GTrue]
       | _ => []
       end;
     val := fun _ _ => None;
     op_eval := test_eval;
     truth := test_truth |}.

Definition test_problem : sparse_problem unit unit nat nat nat bool nat (flat nat) :=
  SparseProblem test_view test_domain [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]
    (fun x => if x =? 0 then FVal 3 else FVal 5).

Definition test_sigma (u : sparse_unknown nat nat nat) : lift_bot (flat nat) :=
  match u with
  | UVal x =>
    match x with
    | 0 | 2 => Some (FVal 3)
    | 1 | 3 => Some (FVal 5)
    | 4 | 5 | 6 | 9 => Some FTop
    | _ => None
    end
  | UEdge e => if (e =? 0) || (e =? 2) || (e =? 3) then Some FTop else None
  | UBlock b => Some FTop
  end.

Definition test_row (r : sparse_constraint nat nat nat) : lift_bot (flat nat) :=
  Query.eval (System.rhs (sparse_system nat_encoding nat_encoding test_problem) r) test_sigma.

Example entry_block_is_seeded : test_row (CBlockEntry 0) = Some FTop.
Proof.
  reflexivity.
Qed.

Example entry_parameters_have_distinct_facts :
  (test_row (CEntryFact 0), test_row (CEntryFact 1)) = (Some (FVal 3), Some (FVal 5)).
Proof.
  reflexivity.
Qed.

Example arbitrary_inputs_and_results_stay_unknown :
  (test_row (CArbitrary 5), test_row (CArbitrary 6)) = (Some FTop, Some FTop).
Proof.
  reflexivity.
Qed.

Example operations_wait_for_operands : test_row (COp 7) = None.
Proof.
  reflexivity.
Qed.

Example true_entry_guard_is_feasible : edge_feasible nat_encoding test_problem test_sigma 0 = true.
Proof.
  reflexivity.
Qed.

Example contradictory_entry_guard_is_infeasible :
  edge_feasible nat_encoding test_problem test_sigma 1 = false.
Proof.
  reflexivity.
Qed.

Example executable_edge_checks_its_guard :
  (test_row (CEdge 0), test_row (CEdge 1)) = (Some FTop, None).
Proof.
  reflexivity.
Qed.

Example parallel_phi_arguments_keep_positions :
  (test_row (CArg 0 0), test_row (CArg 0 1)) = (Some (FVal 3), Some (FVal 5)).
Proof.
  reflexivity.
Qed.

Example unexecuted_parallel_edge_does_not_transfer : test_row (CArg 1 0) = None.
Proof.
  reflexivity.
Qed.

Definition parallel_view : ssa_view unit unit nat nat nat bool nat :=
  {| base := test_base;
     def := def test_view;
     home := home test_view;
     params := params test_view;
     edge_args := edge_args test_view;
     edge_guard := fun _ => [];
     val := val test_view;
     op_eval := test_eval;
     truth := test_truth |}.

Definition parallel_problem := SparseProblem parallel_view test_domain [0; 1; 2; 3]
  (entry_fact test_problem).

Definition parallel_sigma (u : sparse_unknown nat nat nat) : lift_bot (flat nat) :=
  match u with
  | UEdge _ => Some FTop
  | _ => test_sigma u
  end.

Example parallel_edges_pass_different_operands :
  map (fun r => Query.eval (System.rhs
    (sparse_system nat_encoding nat_encoding parallel_problem) r) parallel_sigma)
    [CArg 0 0; CArg 0 1; CArg 1 0; CArg 1 1] =
  [Some (FVal 3); Some (FVal 5); Some (FVal 5); Some (FVal 3)].
Proof.
  reflexivity.
Qed.

Example inverse_comparison_detects_disjoint_operands :
  refine_on_edge nat_encoding test_problem test_sigma 2 2 = Some FBot.
Proof.
  reflexivity.
Qed.

Example every_repeated_operand_uses_the_start_fact :
  refine_fact nat_encoding test_problem test_sigma 4 2 (Some (FVal 7)) = Some (FVal 7).
Proof.
  reflexivity.
Qed.

Example several_conditions_thread_the_accumulated_fact :
  refine_fact nat_encoding test_problem test_sigma 5 2 (Some FTop) = Some FBot.
Proof.
  reflexivity.
Qed.

Example missing_guard_subject_blocks_refinement :
  refine_on_edge nat_encoding test_problem (fun _ => None) 0 0 = None.
Proof.
  reflexivity.
Qed.

Example unreachable_start_stays_unreachable :
  refine_fact nat_encoding test_problem test_sigma 4 2 None = None.
Proof.
  reflexivity.
Qed.

Example unrelated_operands_do_not_change_the_start_fact :
  refine_fact nat_encoding test_problem
    (fun u =>
      match u with
      | UVal 4 => Some FTop
      | _ => None
      end) 2 5 (Some (FVal 11)) = Some (FVal 11).
Proof.
  reflexivity.
Qed.

Example static_dependencies_include_comparison_arguments :
  deps (sparse_static nat_encoding nat_encoding test_problem) (CArg 3 0) =
  [UEdge 3; UVal 2; UVal 4; UVal 2; UVal 3].
Proof.
  reflexivity.
Qed.

Example unknown_and_constraint_tags_are_distinct :
  (Pos.eqb (encode (sparse_unknown_encoding nat_encoding nat_encoding nat_encoding) (UVal 0))
    (encode (sparse_unknown_encoding nat_encoding nat_encoding nat_encoding) (UEdge 0)),
   Pos.eqb (encode (sparse_constraint_encoding nat_encoding nat_encoding nat_encoding) (CEdge 0))
    (encode (sparse_constraint_encoding nat_encoding nat_encoding nat_encoding) (CBlock 0))) =
  (false, false).
Proof.
  reflexivity.
Qed.

Example full_checker_accepts_a_nontrivial_sparse_problem :
  check_post (lift_bot_lattice (fact_lat test_domain))
    (sparse_system nat_encoding nat_encoding test_problem) (fun _ => Some FTop) = true.
Proof.
  reflexivity.
Qed.

Example full_checker_rejects_missing_executable_edges :
  check_post (lift_bot_lattice (fact_lat test_domain))
    (sparse_system nat_encoding nat_encoding test_problem)
    (fun u =>
      match u with
      | UEdge _ => None
      | _ => Some FTop
      end) = false.
Proof.
  reflexivity.
Qed.

Definition unreachable_sigma (u : sparse_unknown nat nat nat) : lift_bot (flat nat) :=
  match u with
  | UBlock 0 => Some FTop
  | UBlock _ | UEdge _ => None
  | UVal _ => Some FTop
  end.

Example unreachable_blocks_cannot_enable_outgoing_edges :
  Query.eval (System.rhs (sparse_system nat_encoding nat_encoding test_problem) (CEdge 2))
    unreachable_sigma = None.
Proof.
  reflexivity.
Qed.

Example unreachable_edge_leaves_its_target_unreached :
  Query.eval (System.rhs (sparse_system nat_encoding nat_encoding test_problem) (CBlock 2))
    unreachable_sigma = None.
Proof.
  reflexivity.
Qed.

Section UnchangedBinding.
Context {C : Type} (c : C).

Definition unchanged_semantics : semantics bool unit :=
  Semantics (fun s => s = false)
    (fun s l s' => s = false /\ l = [] /\ s' = true).

Definition unchanged_graph : Graph.t unit Empty_set :=
  {| Graph.entries := [tt];
     Graph.nodes := [tt];
     Graph.out := fun _ => [];
     Graph.source := fun e : Empty_set => match e with end;
     Graph.target := fun e : Empty_set => match e with end |}.

Definition unchanged_base : graph_view bool unit unit Empty_set :=
  {| cfg := unchanged_graph;
     point := fun _ => tt;
     taken := fun _ _ _ _ => False;
     stays := fun _ _ _ => True |}.

Definition unchanged_view : ssa_view bool unit unit Empty_set unit unit C :=
  {| base := unchanged_base;
     def := fun _ => Param tt 0;
     home := fun _ => tt;
     params := fun _ => [tt];
     edge_args := fun e : Empty_set => match e with end;
     edge_guard := fun e : Empty_set => match e with end;
     val := fun _ _ => Some c;
     op_eval := fun _ _ => None;
     truth := fun _ => false |}.

Example unchanged_bindings_satisfy_the_constructive_origin_law :
  ssa_view_laws unchanged_semantics unchanged_view.
Proof.
  constructor.
  - constructor.
    + constructor.
      * constructor; [intro Hin; contradiction|constructor].
      * intros [] Hin; now left.
      * intros [] e Hin; contradiction.
      * intros [] e Hin Hedge; contradiction.
    + intros s Hs; now left.
    + intros s l s' Hreachable Hstep; now left.
    + intros s l s' e Hreachable Hstep Htaken; contradiction.
    + intros s l s' Hreachable Hstep Hstay; reflexivity.
  - intros [] [] i Hdef; inversion Hdef; reflexivity.
  - intros s l s' e; destruct e.
  - intros s l s' e; destruct e.
  - intros s l s' [] d Hreachable Hstep Hval; left; exact Hval.
Qed.

Example unchanged_binding_survives_a_real_step :
  step unchanged_semantics false [] true /\
  val unchanged_view false tt = val unchanged_view true tt.
Proof.
  split; [split; [reflexivity|split; reflexivity]|reflexivity].
Qed.

Definition unchanged_domain : sparse_domain (flat unit) C unit :=
  {| fact_lat := flat_lattice (fun _ _ => true);
     fact_conc := flat_gamma (fun _ d => d = c);
     top_fact := FTop;
     op_abs := fun _ _ => FTop;
     assume_value := fun _ a => a;
     assume_args := fun _ _ fs => fs |}.

Example unchanged_domain_is_sound :
  sparse_domain_laws unchanged_domain (truth unchanged_view) (op_eval unchanged_view).
Proof.
  assert (Heq : forall x y : unit, true = true <-> x = y).
  { intros [] []; split; intro H; reflexivity. }
  constructor.
  - apply flat_laws; exact Heq.
  - apply flat_gamma_laws; exact Heq.
  - intros d Hfalse; exact Hfalse.
  - intro d; exact I.
  - intros o fs cs d Hfs Hop; exact I.
  - intros k a d Ha Hguard; exact Ha.
  - intros o b fs cs d Hfs Hop Htruth; exact Hfs.
Qed.

Definition unchanged_problem := SparseProblem unchanged_view unchanged_domain [tt]
  (fun _ => FVal tt).

Definition unchanged_sigma (u : sparse_unknown unit Empty_set unit) : lift_bot (flat unit) :=
  match u with
  | UVal _ => Some (FVal tt)
  | UBlock _ => Some FTop
  | UEdge e => match e with end
  end.

Example unchanged_sparse_solution_is_accepted :
  check_post (lift_bot_lattice (fact_lat unchanged_domain))
    (sparse_system unit_encoding unit_encoding unchanged_problem) unchanged_sigma = true.
Proof.
  reflexivity.
Qed.

Example sparse_soundness_covers_the_unchanged_successor :
  gamma (lift_bot_gamma (fact_conc unchanged_domain)) (unchanged_sigma (UVal tt)) c.
Proof.
  assert (Hcoverage : forall s x d, reachable_state unchanged_semantics s ->
    val unchanged_view s x = Some d -> In x (sparse_values unchanged_problem)).
  { intros s [] d Hreachable Hval; now left. }
  assert (Hinitial : forall s x d, initial unchanged_semantics s ->
    val unchanged_view s x = Some d ->
    exists b i, def unchanged_view x = Param b i /\
      In b (Graph.entries unchanged_graph) /\
      gamma (fact_conc unchanged_domain) (entry_fact unchanged_problem x) d).
  { intros s [] d Hstart Hval; exists tt, 0; split; [reflexivity|split; [now left|]].
    cbn in Hval; injection Hval as Hvalue; subst d; reflexivity. }
  assert (Hpost : post_solution (lift_bot_lattice (fact_lat unchanged_domain))
    (sparse_system unit_encoding unit_encoding unchanged_problem) unchanged_sigma).
  { apply check_post_iff; exact unchanged_sparse_solution_is_accepted. }
  destruct (sparse_sound unit_encoding unit_encoding unchanged_semantics unchanged_problem
    unchanged_sigma unchanged_bindings_satisfy_the_constructive_origin_law
    unchanged_domain_is_sound Hcoverage Hinitial Hpost) as [Hblocks [Hedges Hvalues]].
  apply (Hvalues true tt c); [|reflexivity].
  exists false, []; split; [reflexivity|].
  change (exec unchanged_semantics false ([] ++ []) true).
  econstructor; [split; [reflexivity|split; reflexivity]|constructor].
Qed.

End UnchangedBinding.
