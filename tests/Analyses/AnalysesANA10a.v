(** * Memory range and historical-identity regressions

    Computed observations distinguish cleared validations, partial coverage and allocation epochs.
    For example, a second allocation at site 2 has a new identity while the first one stays dead.
    Builds on: AnalysesMemoryBase, ExamplesSsaBytes and the checked SSA test runner. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist FixpointCheck.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement.
From Gaulois.Analyses Require Import AnalysesMemoryBase.
From Gaulois.Examples.While Require Import ExamplesWhileSemantics.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSyntax ExamplesSsaTyping ExamplesSsaSemantics
  ExamplesSsaTypingProofs ExamplesSsaViews ExamplesSsaMemory ExamplesSsaPointers ExamplesSsaBytes
  ExamplesSsaMemoryBase.
From Gaulois.Tests.Analyses Require Import Analyses9Test.
Import List.ListNotations.
Local Open Scope nat_scope.

(** * Executable range-system observations *)

Definition ana10a_range_query (a : range_must nat_encoding) (site : nat) (lo hi : Z) : bool :=
  match a with
  | Unreached => true
  | Reached fs => footprints_subset nat_encoding [Footprint site lo hi] (proj1_sig fs)
  end.

Definition ana10a_range_graph : graph_view unit unit nat nat :=
  GraphView (Graph.Make [0] [0; 1; 2; 3; 4]
    (fun n => if n <? 4 then [n] else []) (fun e => e) S)
    (fun _ => 0) (fun _ _ _ _ => False) (fun _ _ _ => False).

(** Edges 1 and 3 model free and uncertain-call barriers; edge 2 also validates a new range. *)
Definition ana10a_barriers : barrier_view unit unit nat nat nat :=
  BarrierView ana10a_range_graph
    (fun e => match e with
      | 0 => [Footprint 10 0%Z 8%Z]
      | 2 => [Footprint 20 4%Z 8%Z]
      | _ => []
      end)
    (fun e => negb (Nat.eqb e 0))
    (fun _ _ _ _ => True).

Definition ana10a_validation_edge e a :=
  Query.eval (System.rhs (validated_system nat_encoding ana10a_barriers) (Flow e)) (fun _ => a).

Example ana10a_free_and_unknown_call_clear :
  map (fun e => ana10a_range_query
    (ana10a_validation_edge e (range_reached nat_encoding [Footprint 10 0%Z 8%Z]))
    10 0%Z 1%Z) [1; 3] = [false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_barrier_clears_before_current_validation :
  let result := ana10a_validation_edge 2
    (range_reached nat_encoding [Footprint 10 0%Z 8%Z]) in
  (ana10a_range_query result 10 0%Z 1%Z,
   ana10a_range_query result 20 4%Z 8%Z) = (false, true).
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10a_validation_solution fuel :=
  solve_fuel nat_encoding (dense_constraint_encoding nat_encoding nat_encoding)
    (range_must_lattice nat_encoding) (range_must_laws nat_encoding)
    (range_must_top nat_encoding) (Scheduler (encode nat_encoding) (fun _ => false))
    Joining (validated_system nat_encoding ana10a_barriers) fuel.

Example ana10a_fuel_solver_validations :
  map (fun n => (ana10a_range_query (proj1_sig (ana10a_validation_solution 128%positive) n)
      10 0%Z 8%Z,
    ana10a_range_query (proj1_sig (ana10a_validation_solution 128%positive) n)
      20 4%Z 8%Z)) [0; 1; 2; 3; 4] =
  [(false, false); (true, false); (false, false); (false, true); (false, false)].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_fuel_exhaustion_returns_empty_facts :
  map (fun n => ana10a_range_query (proj1_sig (ana10a_validation_solution 1%positive) n)
    10 0%Z 1%Z) [0; 1; 2; 3; 4] = [false; false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10a_stores : store_view unit unit nat nat nat nat_encoding :=
  StoreView ana10a_range_graph (fun _ => [Footprint 10 0%Z 2%Z])
    (fun _ => [Footprint 10 4%Z 6%Z]) (Agreement _ _ (fun _ s t => s = t))
    (fun _ => exist _ (footprints_normalise nat_encoding [])
      (footprints_normalise_canonical nat_encoding [])).

Definition ana10a_backward_fact :=
  Query.eval (System.rhs (dead_store_system nat_encoding ana10a_stores) (Flow 0))
    (fun _ => range_reached nat_encoding [Footprint 10 2%Z 8%Z]).

Example ana10a_backward_partial_byte_coverage :
  map (fun bounds => ana10a_range_query ana10a_backward_fact 10 (fst bounds) (snd bounds))
    [(0%Z, 4%Z); (4%Z, 6%Z); (6%Z, 8%Z); (0%Z, 8%Z)] =
  [true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_join_keeps_only_shared_bytes :
  let fact := join (range_must_lattice nat_encoding)
    (range_reached nat_encoding [Footprint 10 0%Z 8%Z])
    (range_reached nat_encoding [Footprint 10 4%Z 12%Z]) in
  (ana10a_range_query fact 10 4%Z 8%Z, ana10a_range_query fact 10 0%Z 8%Z) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_overlap_adjacency_and_distinct_sites :
  map (fun fs => footprints_disjoint nat_encoding [Footprint 10 0%Z 8%Z] fs)
    [[Footprint 10 7%Z 9%Z]; [Footprint 10 8%Z 9%Z];
     [Footprint 11 0%Z 8%Z]; []; [Footprint 10 (-1)%Z 0%Z]] =
    [false; true; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Actual SSA epoch laws *)

Definition ana10a_ssa_epoch ext P lim : epoch_view state event full_node full_edge vid nat :=
  EpochView (ssa_bytes_view ext P lim)
    (fun s b => match mem s b with
      | Some mb => mlive mb
      | None => false
      end).

(** Concrete SSA liveness, including empty and fragment-only blocks, satisfies epoch freshness. *)
Example ana10a_ssa_epoch_laws ext P lim :
  wf_program ext P -> epoch_laws (ssa_semantics ext P lim) (ana10a_ssa_epoch ext P lim).
Proof.
  intro Hwf; constructor.
  - apply ssa_bytes_laws; exact Hwf.
  - intros s b Hreach Hlive.
    change (match mem s b with Some mb => mlive mb | None => false end = true) in Hlive.
    destruct (mem s b) as [mb|] eqn:Hblock; [|discriminate].
    exists (msite mb); change (option_map msite (mem s b) = Some (msite mb)).
    rewrite Hblock; reflexivity.
  - intros s tr t location Hreach Hstep Hdead Hlive.
    change (match mem s location with Some mb => mlive mb | None => false end = false) in Hdead.
    change (match mem t location with Some mb => mlive mb | None => false end = true) in Hlive.
    change (option_map msite (mem s location) = None /\
      exists site, option_map msite (mem t location) = Some site).
    destruct Hstep; cbn [mem] in *; try congruence.
    + unfold memory_set in Hlive |- *.
      destruct (Nat.eq_dec location nb) as [->|Hne]; [|congruence].
      assert (Hfresh : m nb = None).
      { exact (full_memory_fresh_reachable ext P lim _ Hreach nb (Nat.le_refl nb)). }
      rewrite Hfresh.
      split; [reflexivity|exists x; reflexivity].
    + unfold memory_set in Hlive.
      destruct (Nat.eq_dec location b); [discriminate|congruence].
    + unfold memory_set in Hlive.
      destruct (Nat.eq_dec location b) as [->|Hne]; [|congruence].
      match goal with Hget : m b = Some mb,
        Hstore : memory_store sz mb off v = Some mb' |- _ =>
        rewrite Hget in Hdead;
        unfold memory_store in Hstore;
        destruct (access_ok mb off sz && store_shape sz v);
        [injection Hstore as <-|discriminate]
      end.
      cbn [mlive] in Hlive; congruence.
Qed.

Definition ana10a_repeat_entry := SBlock [(0, TyI64); (4, TyI32)] [] (TJump 1 [0; 4]).
Definition ana10a_repeat_loop := SBlock [(1, TyI64); (3, TyI32)]
  [IAlloc 2 1; IStore M1 2 3; IFree 2] (TJump 1 [1; 3]).
Definition ana10a_repeat_function :=
  FDef 0 [(0, ana10a_repeat_entry); (1, ana10a_repeat_loop)] TyPtr.
Definition ana10a_repeat_program := Program [(0, ana10a_repeat_function)] 0 [].
Definition ana10a_repeat_env size :=
  env_set (env_set (fun _ => None) 0 (VInt W64 size)) 4 (VInt W32 7%Z).
Definition ana10a_repeat_start :=
  State [SFrame 0 0 0 (ana10a_repeat_env 8%Z) 0] (fun _ => None) 0.
Definition ana10a_repeat_at fuel :=
  observed_run fuel no_ext ana10a_repeat_program ana10a_repeat_start.
Definition ana10a_repeat_bytes := ssa_bytes_view no_ext ana10a_repeat_program pointer_limits.
Definition ana10a_repeat_epoch := ana10a_ssa_epoch no_ext ana10a_repeat_program pointer_limits.

Example ana10a_repeat_checker : wf_check ana10a_repeat_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_repeat_wf : wf_program no_ext ana10a_repeat_program.
Proof.
  apply wf_check_sound; [apply ext_respects_nil; reflexivity|exact ana10a_repeat_checker].
Qed.

Example ana10a_repeat_initial :
  initial (ssa_semantics no_ext ana10a_repeat_program pointer_limits) ana10a_repeat_start.
Proof.
  exists ana10a_repeat_function, ana10a_repeat_entry,
    [VInt W64 8%Z; VInt W32 7%Z], (ana10a_repeat_env 8%Z).
  repeat split; try reflexivity.
  constructor; [cbn [valid_cval]; lia|constructor; [cbn [valid_cval]; lia|constructor]].
Qed.

Example ana10a_repeat_run_reachable fuel :
  reachable_state (ssa_semantics no_ext ana10a_repeat_program pointer_limits)
    (ana10a_repeat_at fuel).
Proof.
  unfold ana10a_repeat_at, observed_run.
  destruct (pointer_run fuel no_ext ana10a_repeat_program pointer_limits ana10a_repeat_start)
    as [s|] eqn:Hrun.
  - eapply pointer_run_reachable; [|exact Hrun].
    exists ana10a_repeat_start, []; split; [exact ana10a_repeat_initial|constructor].
  - exists ana10a_repeat_start, []; split; [exact ana10a_repeat_initial|constructor].
Qed.

Example ana10a_actual_allocation_store_and_free_bytes :
  map (fun fuel => (bsite ana10a_repeat_bytes (ana10a_repeat_at fuel) 0,
    byte ana10a_repeat_bytes (ana10a_repeat_at fuel) 0 0%Z))
    [2%positive; 3%positive; 4%positive] = [(Some 2, Some 0); (Some 2, Some 7); (Some 2, None)].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_actual_two_identities_at_same_site :
  let s := ana10a_repeat_at 6%positive in
  (next_block s, bsite ana10a_repeat_bytes s 0, bsite ana10a_repeat_bytes s 1,
   epoch_live ana10a_repeat_epoch s 0, epoch_live ana10a_repeat_epoch s 1,
   byte ana10a_repeat_bytes s 0 0%Z, byte ana10a_repeat_bytes s 1 0%Z) =
  (2, Some 2, Some 2, false, true, None, Some 0).
Proof.
  vm_compute; reflexivity.
Qed.

(** The two-identity fixture satisfies every epoch law on its actual well-formed SSA semantics. *)
Example ana10a_nontrivial_epoch_fixture :
  epoch_laws (ssa_semantics no_ext ana10a_repeat_program pointer_limits) ana10a_repeat_epoch.
Proof.
  apply ana10a_ssa_epoch_laws; exact ana10a_repeat_wf.
Qed.

(** No later execution can revive identity 0 once the first iteration frees it. *)
Example ana10a_old_identity_cannot_resurrect tr s :
  exec (ssa_semantics no_ext ana10a_repeat_program pointer_limits) (ana10a_repeat_at 4%positive)
    tr s -> epoch_live ana10a_repeat_epoch s 0 = false /\
      bsite ana10a_repeat_bytes s 0 = Some 2.
Proof.
  intro Hrun; eapply (epoch_no_resurrection _ _ ana10a_nontrivial_epoch_fixture
    (ana10a_repeat_at 4%positive) tr s 0 2).
  - apply ana10a_repeat_run_reachable.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - exact Hrun.
Qed.

Example ana10a_attempted_resurrection_keeps_old_identity_dead :
  map (fun fuel => epoch_live ana10a_repeat_epoch (ana10a_repeat_at fuel) 0)
    [4%positive; 5%positive; 6%positive; 7%positive; 8%positive; 10%positive] =
    [false; false; false; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition ana10a_zero_start :=
  State [SFrame 0 0 0 (ana10a_repeat_env 0%Z) 0] (fun _ => None) 0.
Definition ana10a_zero_live :=
  observed_run 2%positive no_ext ana10a_repeat_program ana10a_zero_start.

Example ana10a_live_zero_byte_allocation :
  (bsite ana10a_repeat_bytes ana10a_zero_live 0,
   epoch_live ana10a_repeat_epoch ana10a_zero_live 0,
   byte ana10a_repeat_bytes ana10a_zero_live 0 0%Z,
   option_map msz (mem ana10a_zero_live 0)) = (Some 2, true, None, Some 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_alloc_store_free_summaries_use_full_64_bit_range :
  map (writes_at ana10a_repeat_bytes) [(0, 1, 0); (0, 1, 1); (0, 1, 2)] =
    [[Footprint 2 0%Z (2 ^ 64)%Z]; [Footprint 2 0%Z (2 ^ 64)%Z];
     [Footprint 2 0%Z (2 ^ 64)%Z]].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Actual callee writes *)

Definition ana10a_call_entry := SBlock [(0, TyI64); (1, TyI32)] [IAlloc 2 0]
  (TCall (CDirect 1) [2; 1] 1).
Definition ana10a_call_cont := SBlock [(3, TyI32)] [] (TRet 3).
Definition ana10a_callee := SBlock [(4, TyPtr); (5, TyI32)] [IStore M1 4 5] (TRet 5).
Definition ana10a_call_program := Program
  [(0, FDef 0 [(0, ana10a_call_entry); (1, ana10a_call_cont)] TyI32);
   (1, FDef 0 [(0, ana10a_callee)] TyI32)] 0 [].
Definition ana10a_call_start := State [SFrame 0 0 0
  (env_set (env_set (fun _ => None) 0 (VInt W64 8%Z)) 1 (VInt W32 23%Z)) 0]
  (fun _ => None) 0.
Definition ana10a_call_bytes := ssa_bytes_view no_ext ana10a_call_program pointer_limits.

Example ana10a_call_program_checker : wf_check ana10a_call_program = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_call_and_callee_summaries :
  map (writes_at ana10a_call_bytes) [(0, 0, 0); (0, 0, 1); (1, 0, 0)] =
  [[Footprint 2 0%Z (2 ^ 64)%Z]; [Footprint 2 0%Z (2 ^ 64)%Z];
   [Footprint 2 0%Z (2 ^ 64)%Z]].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_actual_callee_changes_the_existing_byte :
  map (fun fuel => byte ana10a_call_bytes
    (observed_run fuel no_ext ana10a_call_program ana10a_call_start) 0 0%Z)
    [1%positive; 2%positive; 3%positive; 4%positive] = [Some 0; Some 0; Some 23; Some 23].
Proof.
  vm_compute; reflexivity.
Qed.

(** * Concrete finite dead-byte client *)

Inductive ana10a_node : Type :=
  | ABranch
  | ALeft
  | ARight
  | AJoin
  | AHole
  | AOverlap
  | AMaybe
  | AReadCycle
  | ANoReadCycle
  | AFinal
  | ATrap
  | AStop
  | AStuck.

Inductive ana10a_edge : Type :=
  | AChooseLeft
  | AChooseRight
  | AWriteLeft
  | AWriteRight
  | ALeaveJoin
  | AWriteHole
  | AWriteOverlap
  | ALeaveMaybe
  | AReadBack
  | ANoReadBack.

Definition ana10a_nodes :=
  [ABranch; ALeft; ARight; AJoin; AHole; AOverlap; AMaybe; AReadCycle; ANoReadCycle;
   AFinal; ATrap; AStop; AStuck].

Definition ana10a_source e :=
  match e with
  | AChooseLeft | AChooseRight => ABranch
  | AWriteLeft => ALeft
  | AWriteRight => ARight
  | ALeaveJoin => AJoin
  | AWriteHole => AHole
  | AWriteOverlap => AOverlap
  | ALeaveMaybe => AMaybe
  | AReadBack => AReadCycle
  | ANoReadBack => ANoReadCycle
  end.

Definition ana10a_target e :=
  match e with
  | AChooseLeft => ALeft
  | AChooseRight => ARight
  | AWriteLeft | AWriteRight => AJoin
  | ALeaveJoin | AWriteHole | AWriteOverlap | ALeaveMaybe => AFinal
  | AReadBack => AReadCycle
  | ANoReadBack => ANoReadCycle
  end.

Definition ana10a_out n :=
  match n with
  | ABranch => [AChooseLeft; AChooseRight]
  | ALeft => [AWriteLeft]
  | ARight => [AWriteRight]
  | AJoin => [ALeaveJoin]
  | AHole => [AWriteHole]
  | AOverlap => [AWriteOverlap]
  | AMaybe => [ALeaveMaybe]
  | AReadCycle => [AReadBack]
  | ANoReadCycle => [ANoReadBack]
  | AFinal | ATrap | AStop | AStuck => []
  end.

Definition ana10a_cfg :=
  Graph.Make ana10a_nodes ana10a_nodes ana10a_out ana10a_source ana10a_target.

(** The two boolean allocation identities have the same historical site 10. *)
Record ana10a_memory_state : Type := AMemoryState {
  ana10a_pc : ana10a_node;
  ana10a_halt : bool;
  ana10a_memory : bool -> Z -> nat
}.

Definition ana10a_write_bounds e : Z * Z :=
  match e with
  | AWriteLeft | AWriteOverlap | ALeaveMaybe => (0%Z, 4%Z)
  | AWriteRight => (2%Z, 6%Z)
  | AWriteHole => (0%Z, 8%Z)
  | _ => (0%Z, 0%Z)
  end.

Definition ana10a_overwrites e : list (footprint nat) :=
  let bounds := ana10a_write_bounds e in [Footprint 10 (fst bounds) (snd bounds)].

Definition ana10a_reads e : list (footprint nat) :=
  match e with
  | AWriteHole => [Footprint 10 4%Z 6%Z]
  | AWriteOverlap => [Footprint 10 2%Z 3%Z]
  | AReadBack => [Footprint 10 1%Z 2%Z]
  | _ => []
  end.

Definition ana10a_writes_byte e o : bool :=
  let bounds := ana10a_write_bounds e in (fst bounds <=? o)%Z && (o <? snd bounds)%Z.

Definition ana10a_update e (memory : bool -> Z -> nat) : bool -> Z -> nat :=
  fun identity o => if ana10a_writes_byte e o then 0 else memory identity o.

Definition ana10a_events e (memory : bool -> Z -> nat) : list nat :=
  match e with
  | AWriteHole => [memory false 4%Z; memory true 4%Z; memory false 5%Z; memory true 5%Z]
  | AWriteOverlap => [memory false 2%Z; memory true 2%Z]
  | AReadBack => [memory false 1%Z; memory true 1%Z]
  | _ => []
  end.

Definition ana10a_enabled e h :=
  match e with
  | ALeaveMaybe => negb h
  | _ => true
  end.

(** An edge observes its old read bytes and then overwrites its definite ranges in both objects. *)
Definition ana10a_action e s tr t : Prop :=
  ana10a_pc s = ana10a_source e /\ ana10a_enabled e (ana10a_halt s) = true /\
  tr = ana10a_events e (ana10a_memory s) /\
  t = AMemoryState (ana10a_target e) (ana10a_halt s)
    (ana10a_update e (ana10a_memory s)).

Definition ana10a_machine : semantics ana10a_memory_state nat :=
  Semantics (fun _ => True) (fun s tr t => exists e, ana10a_action e s tr t).

Definition ana10a_endings : endings ana10a_memory_state :=
  Endings (fun s => ana10a_pc s = AFinal \/
      (ana10a_pc s = AMaybe /\ ana10a_halt s = true))
    (fun s => ana10a_pc s = ATrap) (fun s => ana10a_pc s = AStop).

Definition ana10a_graph : graph_view ana10a_memory_state nat ana10a_node ana10a_edge :=
  GraphView ana10a_cfg ana10a_pc (fun s tr t e => ana10a_action e s tr t)
    (fun _ _ _ => False).

Definition ana10a_may_end n :=
  match n with
  | AMaybe | AFinal | ATrap | AStop | AStuck => true
  | _ => false
  end.

(** Prepare the listed overwrite union once; no node query rebuilds it or scans the edges. *)
Definition ana10a_write_boundary : canonical_footprints nat_encoding :=
  let ranges := flat_map ana10a_overwrites (edges_of ana10a_cfg) in
  exist _ (footprints_normalise nat_encoding ranges)
    (footprints_normalise_canonical nat_encoding ranges).

Definition ana10a_empty_boundary : canonical_footprints nat_encoding :=
  exist _ (footprints_normalise nat_encoding [])
    (footprints_normalise_canonical nat_encoding []).

Definition ana10a_boundary n :=
  if ana10a_may_end n then ana10a_empty_boundary else ana10a_write_boundary.

Definition ana10a_identity_site (_ : bool) : nat := 10.

(** Agreement fixes control and every byte outside the fact, separately for each identity. *)
Definition ana10a_agreement : agreement (range_must nat_encoding) ana10a_memory_state :=
  Agreement _ _ (fun a s t => ana10a_halt s = ana10a_halt t /\
    forall identity o, ~ range_written a (ana10a_identity_site identity) o ->
      ana10a_memory s identity o = ana10a_memory t identity o).

Definition ana10a_memory_view :
    store_view ana10a_memory_state nat ana10a_node ana10a_edge nat nat_encoding :=
  StoreView ana10a_graph ana10a_overwrites ana10a_reads ana10a_agreement ana10a_boundary.

Lemma ana10a_node_listed n : In n ana10a_nodes.
Proof.
  destruct n; unfold ana10a_nodes; simpl; tauto.
Qed.

Lemma ana10a_edge_listed e : In e (ana10a_out (ana10a_source e)).
Proof.
  destruct e; cbn; auto.
Qed.

Lemma ana10a_cfg_wf : graph_wf ana10a_cfg.
Proof.
  constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros n Hin; exact Hin.
  - intros n e Hin; destruct n, e; cbn in Hin |- *; intuition discriminate.
  - intros n e Hn He; apply ana10a_node_listed.
Qed.

(** Every actual memory-machine step has its listed source and target edge. *)
Example ana10a_graph_laws : graph_view_laws ana10a_machine ana10a_graph.
Proof.
  constructor.
  - exact ana10a_cfg_wf.
  - intros s Hinitial; apply ana10a_node_listed.
  - intros s tr t Hreach [e Hstep]; right; exists e; exact Hstep.
  - intros s tr t e Hreach Hstep [Hsource [Henabled [Htrace ->]]].
    cbn [ana10a_graph point cfg ana10a_pc]; split; [|reflexivity].
    rewrite Hsource; apply ana10a_edge_listed.
  - intros s tr t Hreach Hstep Hstay; contradiction.
Qed.

Lemma ana10a_running_edge e s :
  ana10a_pc s = ana10a_source e -> ana10a_enabled e (ana10a_halt s) = true ->
  running ana10a_machine s.
Proof.
  intros Hsource Henabled.
  exists (ana10a_events e (ana10a_memory s)),
    (AMemoryState (ana10a_target e) (ana10a_halt s) (ana10a_update e (ana10a_memory s))).
  exists e; repeat split; assumption.
Qed.

(** The may-end classifier includes every final, trap, stop and stuck state. *)
Example ana10a_ending_classifier s k :
  ends_as ana10a_machine ana10a_endings k s -> ana10a_may_end (ana10a_pc s) = true.
Proof.
  destruct s as [n h memory]; destruct k; cbn [ends_as ana10a_endings final trapped stopped].
  - intros [->|[-> Hhalt]]; reflexivity.
  - intros ->; reflexivity.
  - intros ->; reflexivity.
  - intros [Hnotrun Hrest]; destruct n; try reflexivity; exfalso; apply Hnotrun.
    + eapply ana10a_running_edge with (e := AChooseLeft); reflexivity.
    + eapply ana10a_running_edge with (e := AWriteLeft); reflexivity.
    + eapply ana10a_running_edge with (e := AWriteRight); reflexivity.
    + eapply ana10a_running_edge with (e := ALeaveJoin); reflexivity.
    + eapply ana10a_running_edge with (e := AWriteHole); reflexivity.
    + eapply ana10a_running_edge with (e := AWriteOverlap); reflexivity.
    + eapply ana10a_running_edge with (e := AReadBack); reflexivity.
    + eapply ana10a_running_edge with (e := ANoReadBack); reflexivity.
Qed.

Lemma ana10a_agreement_laws :
  agreement_laws (range_must_lattice nat_encoding) ana10a_agreement.
Proof.
  constructor.
  - intros a s; split; [reflexivity|intros identity o Houtside; reflexivity].
  - intros a b s t Hle [Hhalt Hmemory]; split; [exact Hhalt|].
    intros identity o Houtside; apply Hmemory.
    destruct a as [F|], b as [G|]; try discriminate; cbn [range_written] in *.
    + intro Hin; apply Houtside; apply (proj1 (range_must_reached_order _ _ _ _) Hle); exact Hin.
    + exfalso; apply Houtside; exact I.
    + exfalso; apply Houtside; exact I.
Qed.

Lemma ana10a_writes_byte_spec e o :
  ana10a_writes_byte e o = true <-> written (ana10a_overwrites e) 10 o.
Proof.
  unfold ana10a_writes_byte, ana10a_overwrites.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt, written_cons.
  cbn; split.
  - intros Hbounds; left; tauto.
  - intros [[Hsite Hbounds]|Hempty]; [exact Hbounds|exfalso; exact (written_nil _ _ _ Hempty)].
Qed.

Lemma ana10a_read_agrees e a s t o identity :
  a <> Unreached ->
  agree ana10a_agreement (dead_store_transfer nat_encoding ana10a_memory_view e a) s t ->
  written (ana10a_reads e) 10 o ->
  ana10a_memory s identity o = ana10a_memory t identity o.
Proof.
  intros Hreached [Hhalt Hmemory] Hread; apply Hmemory.
  rewrite dead_store_transfer_written by exact Hreached.
  intros [Hwrite Hnotread]; exact (Hnotread Hread).
Qed.

Lemma ana10a_events_agree e a s t :
  a <> Unreached ->
  agree ana10a_agreement (dead_store_transfer nat_encoding ana10a_memory_view e a) s t ->
  ana10a_events e (ana10a_memory s) = ana10a_events e (ana10a_memory t).
Proof.
  intros Hreached Hagree.
  assert (Hreads : forall identity o, written (ana10a_reads e) 10 o ->
    ana10a_memory s identity o = ana10a_memory t identity o).
  { intros identity o Hread; eapply ana10a_read_agrees; eassumption. }
  destruct e; cbn [ana10a_events]; try reflexivity.
  all: repeat (apply f_equal2;
    [apply Hreads; unfold ana10a_reads; apply written_cons; left; cbn;
      split; [reflexivity|lia]|]); reflexivity.
Qed.

Lemma ana10a_update_agrees e a s t :
  a <> Unreached ->
  agree ana10a_agreement (dead_store_transfer nat_encoding ana10a_memory_view e a) s t ->
  agree ana10a_agreement a
    (AMemoryState (ana10a_target e) (ana10a_halt s) (ana10a_update e (ana10a_memory s)))
    (AMemoryState (ana10a_target e) (ana10a_halt t) (ana10a_update e (ana10a_memory t))).
Proof.
  intros Hreached [Hhalt Hmemory]; split; [exact Hhalt|].
  intros identity o Houtside.
  change ((if ana10a_writes_byte e o then 0 else ana10a_memory s identity o) =
    (if ana10a_writes_byte e o then 0 else ana10a_memory t identity o)).
  destruct (ana10a_writes_byte e o) eqn:Hwrite; [reflexivity|].
  apply Hmemory; rewrite dead_store_transfer_written by exact Hreached.
  intros [[Hnew|Hold] Hnotread].
  - apply ana10a_writes_byte_spec in Hnew; congruence.
  - exact (Houtside Hold).
Qed.

(** These relational laws hold for every reached assignment, independently of any solution. *)
Example ana10a_memory_step_law sigma :
  dead_store_reached nat_encoding ana10a_memory_view sigma ->
  step_agrees ana10a_machine ana10a_graph ana10a_agreement (reachable_state ana10a_machine)
    (dead_store_transfer nat_encoding ana10a_memory_view) sigma.
Proof.
  intro Hreached; split.
  - intros e s tr s' t Hs Ht Hpoint Hstep [Hsource [Henabled [Htrace ->]]] Hagree.
    assert (Htarget : sigma (ana10a_target e) <> Unreached).
    { apply Hreached; apply ana10a_node_listed. }
    pose proof (ana10a_events_agree e _ s t Htarget Hagree) as Hevents.
    destruct Hagree as [Hhalt Hmemory].
    exists (AMemoryState (ana10a_target e) (ana10a_halt t)
      (ana10a_update e (ana10a_memory t))).
    assert (Hmatch : ana10a_action e t tr
      (AMemoryState (ana10a_target e) (ana10a_halt t)
        (ana10a_update e (ana10a_memory t)))).
    { change (ana10a_pc t = ana10a_pc s) in Hpoint.
      unfold ana10a_action; repeat split; congruence. }
    split; [exists e; exact Hmatch|]; split; [exact Hmatch|].
    apply ana10a_update_agrees; [exact Htarget|split; assumption].
  - intros s tr s' t Hs Ht Hpoint Hstep Hstay Hagree; contradiction.
Qed.

(** Ending classifications depend on the fixed point and control bit at the actual boundary. *)
Example ana10a_memory_ending_law :
  ends_agree ana10a_machine ana10a_endings ana10a_graph ana10a_agreement
    (reachable_state ana10a_machine) (fun n => Reached (ana10a_boundary n)).
Proof.
  intros s t Hs Ht Hpoint [Hhalt Hmemory].
  change (ana10a_pc t = ana10a_pc s) in Hpoint.
  cbn [ana10a_endings final trapped stopped]; rewrite Hpoint, Hhalt; tauto.
Qed.

(** All C67 laws are inhabited by concrete reads, writes and identity-sensitive agreement. *)
Example ana10a_memory_laws :
  store_laws ana10a_machine ana10a_endings nat_encoding ana10a_memory_view.
Proof.
  constructor.
  - exact ana10a_graph_laws.
  - intros s tr t Hstay; exact Hstay.
  - split; [exact ana10a_agreement_laws|].
    intros a s t [Hhalt Hmemory]; split; [symmetry; exact Hhalt|].
    intros identity o Houtside; symmetry; apply Hmemory; exact Houtside.
  - intros s k Hreach Hend.
    change (leb (range_must_lattice nat_encoding) (range_reached nat_encoding [])
      (Reached (ana10a_boundary (ana10a_pc s))) = true).
    unfold ana10a_boundary; rewrite (ana10a_ending_classifier s k Hend).
    apply range_must_refl.
  - exact ana10a_memory_step_law.
  - exact ana10a_memory_ending_law.
Qed.

Definition ana10a_node_encoding : encoding ana10a_node.
Proof.
  refine (Encoding _ (fun n => match n with
    | ABranch => 1%positive
    | ALeft => 2%positive
    | ARight => 3%positive
    | AJoin => 4%positive
    | AHole => 5%positive
    | AOverlap => 6%positive
    | AMaybe => 7%positive
    | AReadCycle => 8%positive
    | ANoReadCycle => 9%positive
    | AFinal => 10%positive
    | ATrap => 11%positive
    | AStop => 12%positive
    | AStuck => 13%positive
    end) _).
  intros n n'; destruct n, n'; cbn; intro Hcode; try discriminate; reflexivity.
Defined.

Definition ana10a_edge_encoding : encoding ana10a_edge.
Proof.
  refine (Encoding _ (fun e => match e with
    | AChooseLeft => 1%positive
    | AChooseRight => 2%positive
    | AWriteLeft => 3%positive
    | AWriteRight => 4%positive
    | ALeaveJoin => 5%positive
    | AWriteHole => 6%positive
    | AWriteOverlap => 7%positive
    | ALeaveMaybe => 8%positive
    | AReadBack => 9%positive
    | ANoReadBack => 10%positive
    end) _).
  intros e e'; destruct e, e'; cbn; intro Hcode; try discriminate; reflexivity.
Defined.

Definition ana10a_dead_solution fuel :=
  solve_fuel ana10a_node_encoding
    (dense_constraint_encoding ana10a_node_encoding ana10a_edge_encoding)
    (range_must_lattice nat_encoding) (range_must_laws nat_encoding)
    (range_must_top nat_encoding) (Scheduler (encode ana10a_node_encoding) (fun _ => false))
    Joining (dead_store_system nat_encoding ana10a_memory_view) fuel.

Definition ana10a_dead_facts := proj1_sig (ana10a_dead_solution 512%positive).

Definition ana10a_payload (a : range_must nat_encoding) : option (list (footprint nat)) :=
  match a with
  | Unreached => None
  | Reached ranges => Some (proj1_sig ranges)
  end.

Example ana10a_prepared_union_is_canonical :
  (proj1_sig ana10a_write_boundary, proj1_sig (ana10a_boundary AFinal)) =
    ([Footprint 10 0%Z 8%Z], []).
Proof.
  vm_compute; reflexivity.
Qed.

(** Solved branch facts retain only bytes overwritten on both actual alternatives. *)
Example ana10a_solved_branch_intersection :
  map (fun n => ana10a_payload (ana10a_dead_facts n)) [ABranch; ALeft; ARight; AJoin] =
    [Some [Footprint 10 2%Z 4%Z]; Some [Footprint 10 0%Z 4%Z];
     Some [Footprint 10 2%Z 6%Z]; Some []].
Proof.
  vm_compute; reflexivity.
Qed.

(** Reads remove holes even when the same edge definitely overwrites those bytes. *)
Example ana10a_solved_read_hole_and_overlap :
  map (fun n => ana10a_payload (ana10a_dead_facts n)) [AHole; AOverlap] =
    [Some [Footprint 10 0%Z 4%Z; Footprint 10 6%Z 8%Z];
     Some [Footprint 10 0%Z 2%Z; Footprint 10 3%Z 4%Z]].
Proof.
  vm_compute; reflexivity.
Qed.

(** Every possible ending is empty, even when its graph node has an outgoing overwrite. *)
Example ana10a_solved_terminal_boundaries :
  (map (fun n => ana10a_payload (ana10a_dead_facts n)) [AMaybe; AFinal; ATrap; AStop; AStuck],
   ana10a_out AMaybe) = ([Some []; Some []; Some []; Some []; Some []], [ALeaveMaybe]).
Proof.
  vm_compute; reflexivity.
Qed.

(** Exit-free cycles retain only their unobservable bytes, with no eventual-overwrite premise. *)
Example ana10a_solved_separate_exit_free_cycles :
  map (fun n => ana10a_payload (ana10a_dead_facts n)) [AReadCycle; ANoReadCycle] =
    [Some [Footprint 10 0%Z 1%Z; Footprint 10 2%Z 8%Z]; Some [Footprint 10 0%Z 8%Z]].
Proof.
  vm_compute; reflexivity.
Qed.

Example ana10a_solved_positive_width_and_disjoint_site :
  (ana10a_range_query (ana10a_dead_facts ABranch) 10 2%Z 4%Z,
   ana10a_range_query (ana10a_dead_facts ABranch) 11 2%Z 4%Z,
   map (fun n => ana10a_payload (proj1_sig (ana10a_dead_solution 1%positive) n)) ana10a_nodes) =
    (true, false, map (fun _ => Some []) ana10a_nodes).
Proof.
  vm_compute; reflexivity.
Qed.

(** Normalization coalesces adjacent and overlapping ranges without merging distinct sites. *)
Example ana10a_canonical_adjacent_overlapping_and_separate_sites :
  footprints_normalise nat_encoding
    [Footprint 10 2%Z 4%Z; Footprint 10 0%Z 2%Z; Footprint 10 3%Z 6%Z;
     Footprint 11 0%Z 2%Z; Footprint 10 9%Z 9%Z] =
    [Footprint 10 0%Z 6%Z; Footprint 11 0%Z 2%Z].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma ana10a_every_state_reachable s : reachable_state ana10a_machine s.
Proof.
  exists s, []; split; [exact I|constructor].
Qed.

(** Both closed cycles admit actual infinite executions, including a cycle that reads old bytes. *)
Example ana10a_cycles_diverge e s :
  (e = AReadBack \/ e = ANoReadBack) -> ana10a_pc s = ana10a_source e ->
  diverges ana10a_machine s.
Proof.
  revert e s; cofix IH; intros e s Hcycle Hsource.
  econstructor.
  - exists e; unfold ana10a_action; repeat split; try reflexivity; [exact Hsource|].
    destruct Hcycle as [Hread|Hsilent]; subst e; reflexivity.
  - eapply IH; [exact Hcycle|].
    destruct Hcycle as [Hread|Hsilent]; subst e; reflexivity.
Qed.

Definition ana10a_zero_memory : bool -> Z -> nat := fun _ _ => 0.

(** Final, trap, stop and stuck are all inhabited actual endings in the same concrete semantics. *)
Example ana10a_actual_endings :
  ends_as ana10a_machine ana10a_endings EndFinal (AMemoryState AMaybe true ana10a_zero_memory) /\
  ends_as ana10a_machine ana10a_endings EndTrap (AMemoryState ATrap false ana10a_zero_memory) /\
  ends_as ana10a_machine ana10a_endings EndStop (AMemoryState AStop false ana10a_zero_memory) /\
  ends_as ana10a_machine ana10a_endings EndStuck (AMemoryState AStuck false ana10a_zero_memory).
Proof.
  split; [right; split; reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  split.
  - intros [tr [t [e [Hsource Hrest]]]]; destruct e; discriminate Hsource.
  - cbn [ana10a_endings final trapped stopped ana10a_pc]; intuition discriminate.
Qed.

Lemma ana10a_range_query_sound a site lo hi :
  ana10a_range_query a site lo hi = true ->
  forall k, (lo <= k < hi)%Z -> range_written a site k.
Proof.
  destruct a as [ranges|]; intros Hquery k Hbounds; [|exact I].
  change (footprints_subset nat_encoding [Footprint site lo hi] (proj1_sig ranges) = true)
    in Hquery.
  apply (proj1 (footprints_subset_spec nat nat_encoding
    [Footprint site lo hi] (proj1_sig ranges)) Hquery site k).
  exists (Footprint site lo hi); split; [left; reflexivity|]; cbn; tauto.
Qed.

(** The positive branch observation proves two actual covered bytes in a reached solution. *)
Example ana10a_solved_positive_coverage : range_covers (ana10a_dead_facts ABranch) 10 2%Z 2.
Proof.
  intros k Hbounds.
  eapply ana10a_range_query_sound; [|exact Hbounds].
  vm_compute; reflexivity.
Qed.

Definition ana10a_changed_memory (identity : bool) (o : Z) : nat :=
  if Z.eqb o 2%Z then if identity then 17 else 29 else 0.

Lemma ana10a_changed_agrees a n :
  range_written a 10 2%Z ->
  agree ana10a_agreement a (AMemoryState n false ana10a_changed_memory)
    (AMemoryState n false ana10a_zero_memory).
Proof.
  intro Hcovered; split; [reflexivity|]; intros identity o Houtside.
  change ((if Z.eqb o 2%Z then if identity then 17 else 29 else 0) = 0).
  destruct (Z.eqb o 2%Z) eqn:Heq; [|reflexivity].
  apply Z.eqb_eq in Heq; subst o; exfalso; exact (Houtside Hcovered).
Qed.

Example ana10a_concrete_same_site_distinct_memories :
  (ana10a_identity_site false, ana10a_identity_site true,
   ana10a_changed_memory false 2%Z, ana10a_changed_memory true 2%Z,
   ana10a_zero_memory false 2%Z, ana10a_zero_memory true 2%Z) = (10, 10, 29, 17, 0, 0).
Proof.
  reflexivity.
Qed.

(** Overlapping reads observe both old identities before the same edge overwrites their bytes. *)
Example ana10a_read_write_observes_old_bytes :
  (ana10a_events AWriteOverlap ana10a_changed_memory,
   ana10a_events AWriteOverlap ana10a_zero_memory,
   ana10a_update AWriteOverlap ana10a_changed_memory false 2%Z,
   ana10a_update AWriteOverlap ana10a_changed_memory true 2%Z,
   ana10a_range_query (ana10a_dead_facts AOverlap) 10 2%Z 3%Z) =
    ([29; 17], [0; 0], 0, 0, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** The may-final node has a genuine outgoing transition when its control bit permits it. *)
Example ana10a_may_end_node_also_steps :
  running ana10a_machine (AMemoryState AMaybe false ana10a_zero_memory).
Proof.
  eapply ana10a_running_edge with (e := ALeaveMaybe); reflexivity.
Qed.

(** The original behaviour theorem applies to two genuinely different initial concrete memories. *)
Example ana10a_concrete_dead_store_behaviour :
  same_behaviour ana10a_machine ana10a_endings
    (AMemoryState ABranch false ana10a_changed_memory)
    ana10a_machine ana10a_endings (AMemoryState ABranch false ana10a_zero_memory).
Proof.
  eapply (dead_store_sound ana10a_machine ana10a_endings nat_encoding
    ana10a_memory_view ana10a_dead_facts).
  - exact ana10a_memory_laws.
  - exact (proj2_sig (ana10a_dead_solution 512%positive)).
  - exact I.
  - exact I.
  - reflexivity.
  - apply ana10a_changed_agrees; apply ana10a_solved_positive_coverage; cbn; lia.
Qed.

(** Empty dead-range agreement fixes every byte of both same-site identities, at every offset. *)
Example ana10a_empty_agreement_is_complete s t :
  agree ana10a_agreement (range_reached nat_encoding []) s t <->
  ana10a_halt s = ana10a_halt t /\
    forall identity o, ana10a_memory s identity o = ana10a_memory t identity o.
Proof.
  split; intros [Hhalt Hmemory]; split; [exact Hhalt| |exact Hhalt|].
  - intros identity o; apply Hmemory; rewrite range_reached_written; apply written_nil.
  - intros identity o Houtside; apply Hmemory.
Qed.

(** Actual endpoints recover full concrete memory agreement through the internal endpoint lemma. *)
Example ana10a_endpoint_complete_memory sigma s t k :
  post_solution (range_must_lattice nat_encoding)
    (dead_store_system nat_encoding ana10a_memory_view) sigma ->
  ends_as ana10a_machine ana10a_endings k s ->
  agree ana10a_agreement (sigma (ana10a_pc s)) s t ->
  forall identity o, ana10a_memory s identity o = ana10a_memory t identity o.
Proof.
  intros Hpost Hend Hagree.
  assert (Hempty : agree ana10a_agreement (range_reached nat_encoding []) s t).
  { eapply (dead_store_terminal_agreement ana10a_machine ana10a_endings nat_encoding
      ana10a_memory_view sigma s t k); [exact ana10a_memory_laws|exact Hpost| |exact Hend|].
    - apply ana10a_every_state_reachable.
    - exact Hagree. }
  exact (proj2 (proj1 (ana10a_empty_agreement_is_complete s t) Hempty)).
Qed.

(** Matching the overwrite restores every byte, including the two initially different ones. *)
Example ana10a_overwrite_endpoint_restores_both_identities :
  exists t, step ana10a_machine (AMemoryState AHole false ana10a_zero_memory)
      (ana10a_events AWriteHole ana10a_changed_memory) t /\
    forall identity o, ana10a_update AWriteHole ana10a_changed_memory identity o =
      ana10a_memory t identity o.
Proof.
  pose proof (proj2_sig (ana10a_dead_solution 512%positive)) as Hpost.
  pose proof (dead_store_post_reached nat_encoding ana10a_memory_view ana10a_dead_facts Hpost)
    as Hreached.
  set (s := AMemoryState AHole false ana10a_changed_memory).
  set (t := AMemoryState AHole false ana10a_zero_memory).
  set (s' := AMemoryState AFinal false (ana10a_update AWriteHole ana10a_changed_memory)).
  assert (Hrel : agreeing ana10a_graph ana10a_agreement (reachable_state ana10a_machine)
    ana10a_dead_facts s t).
  { split; [reflexivity|]; split; [apply ana10a_every_state_reachable|].
    split; [apply ana10a_every_state_reachable|].
    apply ana10a_changed_agrees.
    eapply ana10a_range_query_sound with (lo := 0%Z) (hi := 4%Z); [|lia].
    vm_compute; reflexivity. }
  assert (Hstep : step ana10a_machine s (ana10a_events AWriteHole ana10a_changed_memory) s').
  { exists AWriteHole; repeat split; reflexivity. }
  destruct (agreement_step ana10a_machine ana10a_graph (range_must_lattice nat_encoding)
    ana10a_agreement (reachable_state ana10a_machine) (fun n => Reached (ana10a_boundary n))
    (dead_store_transfer nat_encoding ana10a_memory_view) ana10a_dead_facts
    ana10a_graph_laws ana10a_agreement_laws (reachable_invariant ana10a_machine)
    (ana10a_memory_step_law ana10a_dead_facts Hreached) Hpost s t _ s' Hrel Hstep)
    as [t' [Hmatch [Hpoint [Hs [Ht Hagree]]]]].
  exists t'; split; [exact Hmatch|].
  apply (ana10a_endpoint_complete_memory ana10a_dead_facts s' t' EndFinal Hpost); [|exact Hagree].
  left; reflexivity.
Qed.
