(** * Branching Rules analyses

    Computations compare the stratified Rules database with total lattice-engine results.
    For example, a dead assignment's input remains syntactically live but is not needed.
    Builds on: AnalysesRules, RulesDelta and FixpointTotal. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset OrderPointwise OrderBasic.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointCheck FixpointIndex
  FixpointLeast FixpointWorklist FixpointTotal FixpointSchedule.
From Gaulois.Views Require Import ViewsGraph.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesSolve RulesJoin RulesDelta.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesDemand AnalysesRules.
Import List.ListNotations.

Definition branch_graph : Graph.t nat nat :=
  Graph.Make [0] [0; 1; 2; 3; 4]
    (fun n => match n with
      | 0 => [0; 1]
      | 1 => [2]
      | 2 => [3]
      | 3 => [4]
      | _ => []
      end)
    (fun e => match e with
      | 0 | 1 => 0
      | 2 => 1
      | 3 => 2
      | _ => 3
      end)
    (fun e => match e with
      | 0 => 1
      | 1 => 2
      | 2 | 3 => 3
      | _ => 4
      end).

Definition branch_view : graph_view nat unit nat nat :=
  GraphView branch_graph id (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition branch_vars : var_view nat unit nat nat nat unit :=
  VarView branch_view
    (fun e => match e with
      | 0 => [1]
      | 1 => [2]
      | 2 => [0; 9]
      | 3 => [3]
      | 4 => [0]
      | _ => []
      end)
    (fun e => match e with
      | 0 | 1 | 3 => [0]
      | 2 => [5]
      | _ => []
      end)
    (fun n => if Nat.eqb n 4 then [4] else []) (fun _ _ => tt).

Definition branch_demand : demand_view nat unit nat nat nat unit bool :=
  DemandView nat unit nat nat nat unit bool branch_view (defs branch_vars)
    (fun e => match e with
      | 2 | 4 => [(0, true); (5, false)]
      | _ => []
      end)
    (fun e x b => if b then
      match e with
      | 0 => if Nat.eqb x 0 then [(1, true)] else []
      | 1 => if Nat.eqb x 0 then [(2, true)] else []
      | 2 => if Nat.eqb x 5 then [(9, true)] else []
      | 3 => if Nat.eqb x 0 then [(3, true)] else []
      | _ => []
      end else [])
    (fun n => if Nat.eqb n 4 then [(4, true)] else [])
    (fun _ _ => tt) [0; 1; 2; 3; 4; 5; 9].

Example branch_graph_wf : graph_wf branch_graph.
Proof.
  constructor.
  - repeat constructor; cbn; intuition congruence.
  - intros n [<-|Hbad]; [cbn; auto|contradiction].
  - intros n e Hout; destruct n as [|[|[|[|n]]]]; cbn in Hout;
      repeat destruct Hout as [<-|Hout]; try contradiction; reflexivity.
  - intros n e Hn Hout; destruct n as [|[|[|[|n]]]]; cbn in Hout;
      repeat destruct Hout as [<-|Hout]; try contradiction; cbn; auto 8.
Qed.

Example branch_demand_vars : demand_vars_ok branch_demand.
Proof.
  split; [repeat constructor; cbn; intuition congruence|]; split.
  - intros e x b y c Hin; destruct e as [|[|[|[|[|e]]]]]; destruct b;
      cbn in Hin; repeat match type of Hin with
      | context [if ?test then _ else _] => destruct test
      end; cbn in Hin; repeat destruct Hin as [Hin|Hin];
      try contradiction; injection Hin as <- <-; cbn; auto 10.
  - split.
    + intros n y b Hin; cbn in Hin; destruct (Nat.eqb n 4); cbn in Hin;
        [destruct Hin as [Hin|Hin]; [injection Hin as <- <-; cbn; auto 10|contradiction]|
         contradiction].
    + intros e x Hin; destruct e as [|[|[|[|e]]]]; cbn in Hin;
        repeat destruct Hin as [<-|Hin]; try contradiction; cbn; auto 10.
Qed.

Example branch_false_strict e x : dback branch_demand e x false = [].
Proof.
  reflexivity.
Qed.

Local Definition live_facts :=
  extract_live_facts nat_encoding nat_encoding nat_encoding branch_vars.
Local Definition needed_facts :=
  extract_needed_facts nat_encoding nat_encoding nat_encoding branch_demand.

Local Lemma live_program_wf : program_wf liveness_program live_facts.
Proof.
  split; [exact (proj1 AnalysesRules.analysis_programs_rules_wf)|
    apply AnalysesRules.live_facts_arity].
Qed.

Local Lemma needed_program_wf : program_wf neededness_program needed_facts.
Proof.
  split; [exact (proj1 (proj2 AnalysesRules.analysis_programs_rules_wf))|
    apply AnalysesRules.needed_facts_arity].
Qed.

Local Lemma reach_program_wf : program_wf reaching_program live_facts.
Proof.
  split; [exact (proj2 (proj2 AnalysesRules.analysis_programs_rules_wf))|
    apply AnalysesRules.live_facts_arity].
Qed.

Local Definition observe_live db :=
  map (fun n => map (fun x => fmem nat_encoding x
    (live_of_db nat_encoding nat_encoding branch_vars db n)) (dvars branch_demand))
    (Graph.nodes branch_graph).

Local Definition observe_needed db :=
  map (fun n => map (fun x => dget nat_encoding bool_lattice
    (needed_of_db nat_encoding nat_encoding branch_demand db n) x) (dvars branch_demand))
    (Graph.nodes branch_graph).

Local Definition observe_reach db :=
  map (fun n => map (fun xd => fmem (pair_encoding nat_encoding nat_encoding) xd
    (reach_of_db nat_encoding nat_encoding nat_encoding branch_vars db n))
    (reach_universe nat_encoding nat_encoding branch_vars)) (Graph.nodes branch_graph).

(* A completed finite delta run computes observations of the actual reference solver, through
   the proved agreement of both stratified engines. No fuel exhaustion supplies a result. *)
Local Lemma rules_computation {B} (prog : program pred) facts (observe : database pred -> B)
    (answer : B) : program_wf prog facts -> (exists st, stratified prog st) ->
  (forall db db', (forall p ts, db_holds prog db p ts = db_holds prog db' p ts) ->
    observe db = observe db') ->
  option_map observe (delta_bounded_program IndexedNested prog facts 32) = Some answer ->
  option_map observe (solve_program prog facts) = Some answer.
Proof.
  intros Hwf Hstrat Hobserve Hcompute.
  destruct (delta_bounded_program IndexedNested prog facts 32) as [delta|] eqn:Hdelta;
    [|discriminate].
  destruct (solve_program_exact prog facts Hwf Hstrat) as [db [Hsolve Hmodel]].
  rewrite Hsolve; cbn in Hcompute |- *; rewrite <- Hcompute; f_equal; apply Hobserve.
  exact (solve_program_delta_agrees IndexedNested prog facts db delta Hwf Hsolve
    (delta_bounded_program_agrees IndexedNested prog facts 32 delta Hdelta)).
Qed.

Local Lemma observe_live_agrees db db' :
  (forall p ts, db_holds liveness_program db p ts = db_holds liveness_program db' p ts) ->
  observe_live db = observe_live db'.
Proof.
  intro Hdb; unfold observe_live; apply map_ext; intro n; apply map_ext; intro x.
  unfold live_of_db; assert (Hfilter :
    filter (fun y => db_holds liveness_program db PLive (args2 nat_encoding nat_encoding n y))
      (var_universe nat_encoding branch_vars) =
    filter (fun y => db_holds liveness_program db' PLive (args2 nat_encoding nat_encoding n y))
      (var_universe nat_encoding branch_vars)) by (apply filter_ext; intro y; apply Hdb).
  rewrite Hfilter; reflexivity.
Qed.

Local Lemma observe_needed_agrees db db' :
  (forall p ts, db_holds neededness_program db p ts = db_holds neededness_program db' p ts) ->
  observe_needed db = observe_needed db'.
Proof.
  intro Hdb; unfold observe_needed; apply map_ext; intro n; apply map_ext; intro x.
  unfold needed_of_db; assert (Hfilter :
    filter (fun y => db_holds neededness_program db PNeeded (args2 nat_encoding nat_encoding n y))
      (dvars branch_demand) =
    filter (fun y => db_holds neededness_program db' PNeeded (args2 nat_encoding nat_encoding n y))
      (dvars branch_demand)) by (apply filter_ext; intro y; apply Hdb).
  rewrite Hfilter; reflexivity.
Qed.

Local Lemma observe_reach_agrees db db' :
  (forall p ts, db_holds reaching_program db p ts = db_holds reaching_program db' p ts) ->
  observe_reach db = observe_reach db'.
Proof.
  intro Hdb; unfold observe_reach; apply map_ext; intro n; apply map_ext; intro xd.
  unfold reach_of_db; assert (Hfilter :
    filter (fun yd => db_holds reaching_program db PReaches
      (args3 nat_encoding nat_encoding nat_encoding (snd yd) (fst yd) n))
      (reach_universe nat_encoding nat_encoding branch_vars) =
    filter (fun yd => db_holds reaching_program db' PReaches
      (args3 nat_encoding nat_encoding nat_encoding (snd yd) (fst yd) n))
      (reach_universe nat_encoding nat_encoding branch_vars))
    by (apply filter_ext; intro yd; apply Hdb).
  rewrite Hfilter; reflexivity.
Qed.

Local Definition computed {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sys : System.t X C A) (ss : System.static sys) : X -> A :=
  let sch := rpo_scheduler EX sys ss in
  lookup EX L (match run_worklist EX EC L sch Joining sys
    (Declared ss (index_system EX sys ss)) 256 with
    | Some m => m
    | None => Map.empty
    end).

Local Lemma total_computation {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sys : System.t X C A) (ss : System.static sys)
    (HT : terminates L ss (rpo_scheduler EX sys ss) Joining) :
  (match run_worklist EX EC L (rpo_scheduler EX sys ss) Joining sys
    (Declared ss (index_system EX sys ss)) 256 with Some _ => true | None => false end) = true ->
  proj1_sig (solve_total EX EC L HL (rpo_scheduler EX sys ss) Joining sys ss HT) =
    computed EX EC L sys ss.
Proof.
  unfold computed; destruct (run_worklist EX EC L (rpo_scheduler EX sys ss) Joining sys
    (Declared ss (index_system EX sys ss)) 256) as [m|] eqn:Hrun; [intro Hdone|discriminate].
  destruct (solve_total_run EX EC L sys (rpo_scheduler EX sys ss) Joining HL ss HT)
    as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [m' [Hrun' Heq]].
  pose proof (total_completed_runs_unique EX EC L (rpo_scheduler EX sys ss) Joining sys _
    fuel 256 m' m Hrun' Hrun) as Hsame; now rewrite Hsame in Heq.
Qed.

Local Definition live_result :=
  proj1_sig (solve_liveness nat_encoding nat_encoding nat_encoding branch_vars).

Local Definition needed_result :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (demand_lattice nat_encoding bool_demand branch_demand)
    (finite_pointwise_laws _ _ _ bool_laws)
    (rpo_scheduler nat_encoding (demand_system nat_encoding bool_demand branch_demand)
      (backward_static _ _ _)) Joining
    (demand_system nat_encoding bool_demand branch_demand) (backward_static _ _ _)
    (inhabits (base_height (finite_pointwise_height _ _ (proj1 branch_demand_vars)
      bool_laws bool_lub bool_height)))).

Local Definition reach_result :=
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (reach_lattice nat_encoding nat_encoding branch_vars) (finite_powerset_laws _ _)
    (rpo_scheduler nat_encoding (reaching_system nat_encoding nat_encoding branch_vars)
      (forward_static _ _ _)) Joining
    (reaching_system nat_encoding nat_encoding branch_vars) (forward_static _ _ _)
    (inhabits (base_height (finite_powerset_height _ _
      (FinSet.elements_nodup _ _ (FinSet.wf_fold_add _ _ _ (Map.wf_empty _))))))).

(** Every live bit at every listed node agrees between the two total engines. *)
Example branch_live_matches_lattice :
  option_map observe_live (solve_program liveness_program live_facts) =
  Some (map (fun n => map (fun x => fmem nat_encoding x (live_result n))
    (dvars branch_demand)) (Graph.nodes branch_graph)).
Proof.
  unfold live_result, solve_liveness; rewrite total_computation by (vm_compute; reflexivity).
  apply rules_computation.
  - exact live_program_wf.
  - exists AnalysesRules.analysis_strata; exact (proj1 AnalysesRules.analysis_programs_stratified).
  - exact observe_live_agrees.
  - vm_compute; reflexivity.
Qed.

(** Every needed bit agrees, including true dependencies and excluded false necessity facts. *)
Example branch_needed_matches_lattice :
  option_map observe_needed (solve_program neededness_program needed_facts) =
  Some (map (fun n => map (fun x => dget nat_encoding bool_lattice (needed_result n) x)
    (dvars branch_demand)) (Graph.nodes branch_graph)).
Proof.
  unfold needed_result; rewrite total_computation by (vm_compute; reflexivity).
  apply rules_computation.
  - exact needed_program_wf.
  - exists AnalysesRules.analysis_strata.
    exact (proj1 (proj2 AnalysesRules.analysis_programs_stratified)).
  - exact observe_needed_agrees.
  - vm_compute; reflexivity.
Qed.

(** All possible variable/writer pairs agree after the branch merge and redefinition. *)
Example branch_reach_matches_lattice :
  option_map observe_reach (solve_program reaching_program live_facts) =
  Some (map (fun n => map (fun xd => fmem (pair_encoding nat_encoding nat_encoding) xd
    (reach_result n)) (reach_universe nat_encoding nat_encoding branch_vars))
    (Graph.nodes branch_graph)).
Proof.
  unfold reach_result; rewrite total_computation by (vm_compute; reflexivity).
  apply rules_computation.
  - exact reach_program_wf.
  - exists AnalysesRules.analysis_strata.
    exact (proj2 (proj2 AnalysesRules.analysis_programs_stratified)).
  - exact observe_reach_agrees.
  - vm_compute; reflexivity.
Qed.

(** Negation reads a completed input stratum in all three nonempty programs. *)
Example branch_stratifications :
  option_map count (stratify liveness_program) = Some 2 /\
  option_map count (stratify neededness_program) = Some 2 /\
  option_map count (stratify reaching_program) = Some 2.
Proof.
  vm_compute; auto.
Qed.

(** Dead inputs 2 and 9 distinguish syntactic uses from conditional neededness. *)
Example branch_needed_observations :
  option_map observe_needed (solve_program neededness_program needed_facts) = Some
    [[false; true; false; true; true; false; false];
     [true; false; false; false; true; false; false];
     [false; false; false; true; true; false; false];
     [true; false; false; false; true; false; false];
     [false; false; false; false; true; false; false]].
Proof.
  rewrite branch_needed_matches_lattice; unfold needed_result.
  rewrite total_computation by (vm_compute; reflexivity); vm_compute; reflexivity.
Qed.

(** The full lattice checker accepts nonempty results of all three genuine total runs. *)
Example branch_full_checkers_accept :
  check_post (live_lattice nat_encoding branch_vars)
    (liveness_system nat_encoding branch_vars) live_result = true /\
  check_post (demand_lattice nat_encoding bool_demand branch_demand)
    (demand_system nat_encoding bool_demand branch_demand) needed_result = true /\
  check_post (reach_lattice nat_encoding nat_encoding branch_vars)
    (reaching_system nat_encoding nat_encoding branch_vars) reach_result = true /\
  fmem nat_encoding 9 (live_result 0) = true /\
  dget nat_encoding bool_lattice (needed_result 0) 1 = true /\
  fmem (pair_encoding nat_encoding nat_encoding) (0, 3) (reach_result 3) = true.
Proof.
  unfold live_result, solve_liveness, needed_result, reach_result.
  repeat rewrite total_computation by (vm_compute; reflexivity); vm_compute;
    repeat split; reflexivity.
Qed.

Definition duplicate_graph : Graph.t nat nat :=
  Graph.Make [] [0; 0] (fun n => if Nat.eqb n 0 then [0; 0] else [7])
    (fun _ => 99) (fun _ => 8).

Definition duplicate_vars : var_view nat unit nat nat nat unit :=
  VarView (GraphView duplicate_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun e => if Nat.eqb e 0 then [1; 1] else [7]) (fun _ => [2; 2])
    (fun _ => [3; 3]) (fun _ _ => tt).

(** Raw extraction preserves occurrences and does not invent the unlisted node's edge. *)
Example duplicate_extraction :
  length (extract_live_facts nat_encoding nat_encoding nat_encoding duplicate_vars) = 24 /\
  existsb (fun f => match fst f with
    | PUse => List.existsb (Pos.eqb (encode nat_encoding 7)) (snd f)
    | _ => false
    end) (extract_live_facts nat_encoding nat_encoding nat_encoding duplicate_vars) = false.
Proof.
  vm_compute; auto.
Qed.
