(** * Sparse expression graph regressions

    Computed examples compare sparse reconstruction with the least dense joining solutions.
    For example, an unreachable eventless cycle retains the full fact in both directions.
    Builds on: AnalysesSeg, AnalysesAvailable and FixpointTotal. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointLeast FixpointWorklist FixpointTotal
  FixpointSchedule FixpointIndex.
From Gaulois.Views Require Import ViewsGraph.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesAvailable AnalysesSeg.
Import List.ListNotations.

Local Definition test_map {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys) : assignment X A :=
  match run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 512 with
  | Some result => result
  | None => Map.empty
  end.

Local Definition test_success {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys) : bool :=
  match run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 512 with
  | Some _ => true
  | None => false
  end.

Local Lemma test_total_computation {X C A} (EX : encoding X) (EC : encoding C) (L : lattice A)
    (HL : lattice_laws L) (sch : scheduler X) (sys : System.t X C A) (ss : System.static sys)
    (HT : terminates L ss sch Joining) :
  test_success EX EC L sch sys ss = true ->
  proj1_sig (solve_total EX EC L HL sch Joining sys ss HT) =
    lookup EX L (test_map EX EC L sch sys ss).
Proof.
  unfold test_success, test_map.
  destruct (run_worklist EX EC L sch Joining sys (Declared ss (index_system EX sys ss)) 512)
    as [result|] eqn:Hrun; [intro Hsuccess|discriminate].
  destruct (solve_total_run EX EC L sys sch Joining HL ss HT) as [fuel Hfuel].
  destruct (Hfuel fuel (Pos.le_refl fuel)) as [other [Hother Heq]].
  pose proof (total_completed_runs_unique EX EC L sch Joining sys _ fuel 512 other result
    Hother Hrun) as Hsame; now rewrite Hsame in Heq.
Qed.

Local Definition expression_fixture : Type := genkill_view nat unit nat nat nat unit.

Local Definition universe_nodup (gk : expression_fixture) : NoDup (expr_universe nat_encoding gk).
Proof.
  unfold expr_universe; apply (FinSet.elements_nodup nat_encoding), FinSet.wf_fold_add,
    Map.wf_empty.
Qed.

Local Definition dense_available (gk : expression_fixture) : nat -> avail_set nat_encoding gk :=
  let sys := available_system nat_encoding gk in
  let ss := forward_static _ _ _ in
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (avail_lattice nat_encoding gk) (finite_must_laws _ _)
    (rpo_scheduler nat_encoding sys ss) Joining sys ss
    (inhabits (base_height (finite_must_height _ _ (universe_nodup gk))))).

Local Definition dense_busy (gk : expression_fixture) : nat -> avail_set nat_encoding gk :=
  let sys := busy_system nat_encoding gk in
  let ss := backward_static _ _ _ in
  proj1_sig (solve_total nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (avail_lattice nat_encoding gk) (finite_must_laws _ _)
    (rpo_scheduler nat_encoding sys ss) Joining sys ss
    (inhabits (base_height (finite_must_height _ _ (universe_nodup gk))))).

Local Lemma dense_available_least gk :
  least_solution (avail_lattice nat_encoding gk) (available_system nat_encoding gk)
    (dense_available gk).
Proof.
  unfold dense_available; apply solve_total_least; [apply finite_must_lub|].
  apply (AnalysesSeg.seg_forward_system_monotone _ (finite_must_laws _ _)).
  intros e He; apply AnalysesSeg.seg_dense_transfer_monotone.
Qed.

Local Lemma dense_busy_least gk :
  least_solution (avail_lattice nat_encoding gk) (busy_system nat_encoding gk) (dense_busy gk).
Proof.
  unfold dense_busy; apply solve_total_least; [apply finite_must_lub|].
  apply (AnalysesSeg.seg_backward_system_monotone _ (finite_must_laws _ _)).
  intros e He; apply AnalysesSeg.seg_dense_transfer_monotone.
Qed.

(** The fixture has two entries, a fork, a join, parallel edges and two closed components. *)
Definition seg_sample_graph : Graph.t nat nat :=
  Graph.Make [0; 5] [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]
    (fun n => match n with
              | 0 => [0; 1]
              | 1 => [2]
              | 2 => [3; 4]
              | 3 => [5]
              | 4 => [6]
              | 5 => [7]
              | 7 => [8]
              | 8 => [9]
              | 9 => [10]
              | 10 => [11]
              | 11 => [12]
              | _ => []
              end)
    (fun e => match e with
              | 0 | 1 => 0
              | 2 => 1
              | 3 | 4 => 2
              | 5 => 3
              | 6 => 4
              | 7 => 5
              | 8 => 7
              | 9 => 8
              | 10 => 9
              | 11 => 10
              | _ => 11
              end)
    (fun e => match e with
              | 0 => 1
              | 1 => 2
              | 2 | 3 | 4 => 3
              | 5 => 4
              | 6 | 7 => 6
              | 8 => 7
              | 9 => 9
              | 10 => 10
              | 11 => 8
              | _ => 12
              end).

Definition seg_sample : expression_fixture :=
  GenKillView (GraphView seg_sample_graph id (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun e => match e with 5 | 12 => [7] | _ => [] end)
    (fun e u => (Nat.eqb e 5 || Nat.eqb e 6) && Nat.eqb u 7) (fun _ _ => Some tt).

Definition seg_sample_index :=
  build_expression_seg nat_encoding nat_encoding nat_encoding seg_sample 7.

Local Lemma sample_ready :
  ready nat_encoding seg_sample_graph (prepare nat_encoding seg_sample_graph).
Proof.
  apply prepare_ready.
  - constructor.
    + cbn; repeat constructor; cbn; intuition discriminate.
    + intros n [<-|[<-|Hnone]]; cbn; auto 15.
    + intros n e He.
      destruct n as [|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]; cbn in He;
        repeat destruct He as [He|He]; try contradiction; subst e; reflexivity.
    + intros n e Hn He; cbn in Hn.
      repeat destruct Hn as [Hn|Hn]; try contradiction; subst n; cbn in He;
        repeat destruct He as [He|He]; try contradiction; subst e; cbn; auto 15.
  - intro n; destruct n as [|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]; cbn;
      repeat constructor; cbn; intuition discriminate.
Qed.

(** Degree-one paths contract, while the two parallel arcs and one anchor per cycle survive. *)
Example seg_sample_paths :
  Graph.nodes (seg_graph seg_sample_index) = [0; 2; 3; 4; 5; 6; 7; 10; 11; 12] /\
  seg_path nat_encoding seg_sample_index 0 = [0; 2] /\
  seg_path nat_encoding seg_sample_index 3 = [3] /\
  seg_path nat_encoding seg_sample_index 4 = [4] /\
  seg_path nat_encoding seg_sample_index 8 = [8] /\
  seg_path nat_encoding seg_sample_index 11 = [11; 9; 10] /\
  Map.get nat_encoding 1 (seg_interiors seg_sample_index) = Some (0,0) /\
  Map.get nat_encoding 8 (seg_interiors seg_sample_index) = Some (11,0) /\
  Map.get nat_encoding 9 (seg_interiors seg_sample_index) = Some (11,1).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Summary tables preserve identity, a kill, and generation taking precedence over a kill. *)
Example seg_sample_summaries :
  map (fun a =>
    (seg_forward_transfer nat_encoding nat_encoding seg_sample 7 seg_sample_index a false,
     seg_forward_transfer nat_encoding nat_encoding seg_sample 7 seg_sample_index a true))
    [0; 5; 6; 11]
    = [(false,true); (true,true); (false,false); (false,true)] /\
  map (fun a =>
    (seg_backward_transfer nat_encoding nat_encoding seg_sample 7 seg_sample_index a false,
     seg_backward_transfer nat_encoding nat_encoding seg_sample 7 seg_sample_index a true))
    [0; 5; 6; 11]
    = [(false,true); (true,true); (false,false); (false,true)].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Forward facts agree with ANA-1's least solution at every original point. *)
Local Lemma seg_sample_available_contract :
  map (seg_available nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
  map (fun n => fmem nat_encoding 7 (dense_available seg_sample n)) (Graph.nodes seg_sample_graph).
Proof.
  apply map_ext_in; intros n Hn.
  apply seg_available_exact; [exact sample_ready|apply dense_available_least|exact Hn].
Qed.

(** Backward facts agree with ANA-1's least solution at every original point. *)
Local Lemma seg_sample_busy_contract :
  map (seg_busy nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
  map (fun n => fmem nat_encoding 7 (dense_busy seg_sample n)) (Graph.nodes seg_sample_graph).
Proof.
  apply map_ext_in; intros n Hn.
  apply seg_busy_exact; [exact sample_ready|apply dense_busy_least|exact Hn].
Qed.

(** The total dense solver's completed run gives the expected forward boundary facts. *)
Example seg_sample_available_values :
  map (fun n => fmem nat_encoding 7 (dense_available seg_sample n)) (Graph.nodes seg_sample_graph) =
    [false; false; false; false; true; false; false; true; true; true; true; true; true].
Proof.
  unfold dense_available; rewrite test_total_computation;
    [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

(** Exit seeds are empty, while both unreachable closed cycles retain their full fact. *)
Example seg_sample_busy_values :
  map (fun n => fmem nat_encoding 7 (dense_busy seg_sample n)) (Graph.nodes seg_sample_graph) =
    [true; true; true; true; false; false; false; true; true; true; true; true; false].
Proof.
  unfold dense_busy; rewrite test_total_computation;
    [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

(** Sparse forward execution reconstructs all contracted points and both closed components. *)
Example seg_sample_sparse_available_values :
  map (seg_available nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
    [false; false; false; false; true; false; false; true; true; true; true; true; true].
Proof.
  unfold seg_available.
  assert (Hu : FinSet.mem nat_encoding 7 (FinSet.of_list nat_encoding
    (expr_universe nat_encoding seg_sample)) = true) by (vm_compute; reflexivity).
  rewrite Hu; unfold AnalysesSeg.seg_available_cut; rewrite test_total_computation;
    [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

(** Sparse backward execution retains full facts on sinkless cycles and empty facts at exits. *)
Example seg_sample_sparse_busy_values :
  map (seg_busy nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
    [true; true; true; true; false; false; false; true; true; true; true; true; false].
Proof.
  unfold seg_busy.
  assert (Hu : FinSet.mem nat_encoding 7 (FinSet.of_list nat_encoding
    (expr_universe nat_encoding seg_sample)) = true) by (vm_compute; reflexivity).
  rewrite Hu; unfold AnalysesSeg.seg_busy_cut; rewrite test_total_computation;
    [vm_compute; reflexivity|vm_compute; reflexivity].
Qed.

(** The independently executed forward systems agree on every original node. *)
Example seg_sample_available_exact :
  map (seg_available nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
  map (fun n => fmem nat_encoding 7 (dense_available seg_sample n)) (Graph.nodes seg_sample_graph).
Proof.
  rewrite seg_sample_sparse_available_values, seg_sample_available_values; reflexivity.
Qed.

(** The independently executed backward systems agree on every original node. *)
Example seg_sample_busy_exact :
  map (seg_busy nat_encoding nat_encoding nat_encoding seg_sample 7)
    (Graph.nodes seg_sample_graph) =
  map (fun n => fmem nat_encoding 7 (dense_busy seg_sample n)) (Graph.nodes seg_sample_graph).
Proof.
  rewrite seg_sample_sparse_busy_values, seg_sample_busy_values; reflexivity.
Qed.

(** Absent expressions are false on the entire graph and on an unlisted point. *)
Example seg_absent_expression :
  map (seg_available nat_encoding nat_encoding nat_encoding seg_sample 99) [0; 1; 7; 8; 9; 10; 99] =
    [false; false; false; false; false; false; false] /\
  map (seg_busy nat_encoding nat_encoding nat_encoding seg_sample 99) [0; 1; 7; 8; 9; 10; 99] =
    [false; false; false; false; false; false; false].
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition seg_empty : expression_fixture :=
  GenKillView (GraphView (Graph.Make [] [] (fun _ => []) id id) id
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (fun _ => []) (fun _ _ => false) (fun _ _ => Some tt).

(** Empty graphs have no sparse nodes or paths and return false in either direction. *)
Example seg_empty_graph :
  Graph.nodes (seg_graph
    (build_expression_seg nat_encoding nat_encoding nat_encoding seg_empty 7)) = [] /\
  seg_available nat_encoding nat_encoding nat_encoding seg_empty 7 0 = false /\
  seg_busy nat_encoding nat_encoding nat_encoding seg_empty 7 0 = false.
Proof.
  vm_compute; auto.
Qed.

(** The empty graph's independently solved finite carriers also contain no expression. *)
Example seg_empty_dense :
  (fmem nat_encoding 7 (dense_available seg_empty 0),
   fmem nat_encoding 7 (dense_busy seg_empty 0)) = (false,false).
Proof.
  unfold dense_available, dense_busy;
    repeat rewrite test_total_computation by (vm_compute; reflexivity).
  vm_compute; reflexivity.
Qed.

(** A present expression still returns false outside the original point domain. *)
Example seg_unlisted_point :
  (seg_available nat_encoding nat_encoding nat_encoding seg_sample 7 99,
   seg_busy nat_encoding nat_encoding nat_encoding seg_sample 7 99) = (false,false).
Proof.
  unfold seg_available, seg_busy.
  assert (Hu : FinSet.mem nat_encoding 7 (FinSet.of_list nat_encoding
    (expr_universe nat_encoding seg_sample)) = true) by (vm_compute; reflexivity).
  rewrite Hu; unfold AnalysesSeg.seg_available_cut, AnalysesSeg.seg_busy_cut;
    repeat rewrite test_total_computation by (vm_compute; reflexivity).
  vm_compute; reflexivity.
Qed.

Definition seg_entry_loop : expression_fixture :=
  GenKillView (GraphView (set_entries seg_sample_graph [0; 5; 7]) id
    (fun _ _ _ _ => False) (fun _ _ _ => False))
    (gen seg_sample) (kill seg_sample) (uval seg_sample).

(** Making a closed loop an entry empties availability while its busy fact remains unconstrained. *)
Example seg_entry_loop_seed :
  (seg_available nat_encoding nat_encoding nat_encoding seg_entry_loop 7 7,
   fmem nat_encoding 7 (dense_available seg_entry_loop 7),
   seg_busy nat_encoding nat_encoding nat_encoding seg_entry_loop 7 7,
   fmem nat_encoding 7 (dense_busy seg_entry_loop 7)) = (false,false,true,true).
Proof.
  unfold seg_available, seg_busy, dense_available, dense_busy.
  assert (Hu : FinSet.mem nat_encoding 7 (FinSet.of_list nat_encoding
    (expr_universe nat_encoding seg_entry_loop)) = true) by (vm_compute; reflexivity).
  rewrite Hu; unfold AnalysesSeg.seg_available_cut, AnalysesSeg.seg_busy_cut;
    repeat rewrite test_total_computation by (vm_compute; reflexivity).
  vm_compute; reflexivity.
Qed.

(** Finite dense carriers clamp the same absent expression even on the unreachable SCC. *)
Example seg_absent_dense :
  map (fun n => (fmem nat_encoding 99 (dense_available seg_sample n),
    fmem nat_encoding 99 (dense_busy seg_sample n))) [0; 1; 7; 8; 9; 10] =
    [(false,false); (false,false); (false,false); (false,false); (false,false); (false,false)].
Proof.
  unfold dense_available, dense_busy;
    repeat rewrite test_total_computation by (vm_compute; reflexivity).
  vm_compute; reflexivity.
Qed.
