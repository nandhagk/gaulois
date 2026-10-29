(** * Instruction-point SSA boundary examples

    These fixtures retain parallel phi edges, a loop and an unreachable component.
    For example, the two entry-to-loop edges pass different values to one parameter edge.
    Builds on: ViewsSsaPoints, GraphDfs, GraphDominance and Collections encodings. *)

From Stdlib Require Import List PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance.
From Gaulois.Views Require Import ViewsSsaPoints.
Import List.ListNotations.

(** * A finite ordered SSA view *)

Inductive fixture_block : Type :=
  | EntryBlock
  | LoopBlock
  | DeadBlock.

Inductive fixture_block_edge : Type :=
  | LeftIncoming
  | RightIncoming
  | LoopIncoming.

Inductive fixture_point : Type :=
  | EntryBefore
  | EntryBody
  | EntryAfter
  | LoopBefore
  | LoopBody
  | LoopAfter
  | DeadBefore
  | DeadAfter.

Inductive fixture_edge : Type :=
  | EntryParameters
  | EntryInstruction
  | LeftPhi
  | RightPhi
  | LoopParameters
  | LoopInstruction
  | BackPhi
  | DeadParameters.

Inductive fixture_value : Type :=
  | InputLeft
  | InputRight
  | PhiValue
  | NextValue
  | UndefinedDead.

Definition fixture_blocks : Graph.t fixture_block fixture_block_edge :=
  {| Graph.entries := [EntryBlock];
     Graph.nodes := [EntryBlock; LoopBlock; DeadBlock];
     Graph.out := fun b =>
       match b with
       | EntryBlock => [LeftIncoming; RightIncoming]
       | LoopBlock => [LoopIncoming]
       | DeadBlock => []
       end;
     Graph.source := fun e =>
       match e with
       | LeftIncoming | RightIncoming => EntryBlock
       | LoopIncoming => LoopBlock
       end;
     Graph.target := fun _ => LoopBlock |}.

Definition fixture_graph : Graph.t fixture_point fixture_edge :=
  {| Graph.entries := [EntryBefore];
     Graph.nodes := [EntryBefore; EntryBody; EntryAfter; LoopBefore; LoopBody; LoopAfter;
       DeadBefore; DeadAfter];
     Graph.out := fun n =>
       match n with
       | EntryBefore => [EntryParameters]
       | EntryBody => [EntryInstruction]
       | EntryAfter => [LeftPhi; RightPhi]
       | LoopBefore => [LoopParameters]
       | LoopBody => [LoopInstruction]
       | LoopAfter => [BackPhi]
       | DeadBefore => [DeadParameters]
       | DeadAfter => []
       end;
     Graph.source := fun e =>
       match e with
       | EntryParameters => EntryBefore
       | EntryInstruction => EntryBody
       | LeftPhi | RightPhi => EntryAfter
       | LoopParameters => LoopBefore
       | LoopInstruction => LoopBody
       | BackPhi => LoopAfter
       | DeadParameters => DeadBefore
       end;
     Graph.target := fun e =>
       match e with
       | EntryParameters => EntryBody
       | EntryInstruction => EntryAfter
       | LeftPhi | RightPhi | BackPhi => LoopBefore
       | LoopParameters => LoopBody
       | LoopInstruction => LoopAfter
       | DeadParameters => DeadAfter
       end |}.

Definition fixture_uses : point_uses fixture_point fixture_edge fixture_value :=
  {| live_graph := fixture_graph;
     edge_use := fun e =>
       match e with
       | EntryInstruction | LeftPhi => [InputLeft]
       | RightPhi => [InputRight]
       | LoopInstruction => [PhiValue]
       | BackPhi => [NextValue]
       | _ => []
       end;
     edge_def := fun e =>
       match e with
       | EntryParameters => [InputLeft; InputRight]
       | LoopParameters => [PhiValue]
       | LoopInstruction => [NextValue]
       | _ => []
       end;
     exit_use := fun n =>
       match n with
       | LoopAfter => [PhiValue; NextValue]
       | DeadAfter => [UndefinedDead]
       | _ => []
       end |}.

Definition fixture_ssa :
    ssa_points fixture_block fixture_block_edge fixture_point fixture_edge fixture_value :=
  {| point_model := fixture_uses;
     block_graph := fixture_blocks;
     points_in_block := fun b =>
       match b with
       | EntryBlock => [EntryBefore; EntryBody; EntryAfter]
       | LoopBlock => [LoopBefore; LoopBody; LoopAfter]
       | DeadBlock => [DeadBefore; DeadAfter]
       end;
     instruction_edges := fun b =>
       match b with
       | EntryBlock => [EntryParameters; EntryInstruction]
       | LoopBlock => [LoopParameters; LoopInstruction]
       | DeadBlock => [DeadParameters]
       end;
     parameter_edge := fun b =>
       match b with
       | EntryBlock => EntryParameters
       | LoopBlock => LoopParameters
       | DeadBlock => DeadParameters
       end;
     block_of_point := fun n =>
       match n with
       | EntryBefore | EntryBody | EntryAfter => EntryBlock
       | LoopBefore | LoopBody | LoopAfter => LoopBlock
       | DeadBefore | DeadAfter => DeadBlock
       end;
     block_edge_of := fun e =>
       match e with
       | LeftPhi => Some LeftIncoming
       | RightPhi => Some RightIncoming
       | BackPhi => Some LoopIncoming
       | _ => None
       end;
     block_params := fun b =>
       match b with
       | EntryBlock => [InputLeft; InputRight]
       | LoopBlock => [PhiValue]
       | DeadBlock => []
       end;
     block_edge_args := fun be =>
       match be with
       | LeftIncoming => [InputLeft]
       | RightIncoming => [InputRight]
       | LoopIncoming => [NextValue]
       end;
     point_definition := fun x =>
       match x with
       | InputLeft | InputRight => Some EntryBefore
       | PhiValue => Some LoopBefore
       | NextValue => Some LoopBody
       | UndefinedDead => None
       end |}.

(** Constructor lists in this fixture contain pairwise distinct elements. *)
Local Ltac fixture_distinct := repeat constructor; cbn; intuition discriminate.

Example fixture_point_graph_wf : graph_wf fixture_graph.
Proof.
  constructor.
  - fixture_distinct.
  - intros n Hentry; cbn in Hentry; destruct Hentry as [<-|[]]; now left.
  - intros n e Hedge; destruct n, e; cbn in Hedge |- *; intuition congruence.
  - intros n e _ Hedge; destruct n, e; cbn in Hedge |- *; intuition congruence.
Qed.

Example fixture_point_out_nodup : forall n, NoDup (Graph.out fixture_graph n).
Proof.
  intro n; destruct n; fixture_distinct.
Qed.

Example fixture_block_graph_wf : graph_wf fixture_blocks.
Proof.
  constructor.
  - fixture_distinct.
  - intros b Hentry; cbn in Hentry; destruct Hentry as [<-|[]]; now left.
  - intros b e Hedge; destruct b, e; cbn in Hedge |- *; intuition congruence.
  - intros b e _ Hedge; destruct b, e; cbn in Hedge |- *; intuition congruence.
Qed.

Example fixture_ssa_laws : ssa_point_laws fixture_ssa.
Proof.
  constructor.
  - exact fixture_point_graph_wf.
  - exact fixture_point_out_nodup.
  - exact fixture_block_graph_wf.
  - intro b; destruct b; fixture_distinct.
  - intro n; split; intro Hnode.
    + exists (block_of_point fixture_ssa n); destruct n; cbn; tauto.
    + destruct n; cbn; tauto.
  - intro b; destruct b; fixture_distinct.
  - intros b n _ Hin; destruct b, n; cbn in Hin |- *; intuition congruence.
  - intros b _; destruct b; discriminate.
  - intros b _; destruct b; cbn;
      repeat (eapply point_chain_step; [now left|reflexivity|]); apply point_chain_one.
  - intros b e _ Hin; destruct b, e; cbn in Hin |- *; intuition congruence.
  - intros n e _ Hedge Hinternal; destruct n, e; cbn in Hedge, Hinternal |- *;
      intuition congruence.
  - intros b _; destruct b; reflexivity.
  - intros b x _; destruct b; reflexivity.
  - intros n e _ Hedge; destruct n, e; cbn in Hedge |- *; intuition congruence.
  - intros be _; destruct be; reflexivity.
  - intros n e be _ Hedge Hprojection x Harg; destruct n, e, be;
      cbn in Hedge, Hprojection, Harg |- *; intuition congruence.
  - intros be _; destruct be.
    + exists EntryAfter, LeftPhi; cbn; tauto.
    + exists EntryAfter, RightPhi; cbn; tauto.
    + exists LoopAfter, BackPhi; cbn; tauto.
  - intros e1 e2 be _ _ Hfirst Hsecond; destruct e1, e2, be;
      cbn in Hfirst, Hsecond |- *; congruence.
Qed.

Example parallel_phi_operands :
  (Graph.source fixture_graph LeftPhi, Graph.target fixture_graph LeftPhi,
   block_edge_of fixture_ssa LeftPhi, edge_use fixture_uses LeftPhi) =
    (EntryAfter, LoopBefore, Some LeftIncoming, [InputLeft]) /\
  (Graph.source fixture_graph RightPhi, Graph.target fixture_graph RightPhi,
   block_edge_of fixture_ssa RightPhi, edge_use fixture_uses RightPhi) =
    (EntryAfter, LoopBefore, Some RightIncoming, [InputRight]) /\
  LeftPhi <> RightPhi.
Proof.
  vm_compute; repeat split; discriminate.
Qed.

Example common_parameter_edge_after_phi_operands :
  Graph.target fixture_graph LeftPhi = LoopBefore /\
  Graph.target fixture_graph RightPhi = LoopBefore /\
  Graph.target fixture_graph BackPhi = LoopBefore /\
  nth_error (instruction_edges fixture_ssa LoopBlock) 0 = Some LoopParameters /\
  Graph.source fixture_graph LoopParameters = LoopBefore /\
  edge_def fixture_uses LoopParameters = [PhiValue].
Proof.
  vm_compute; repeat split.
Qed.

Example loop_carried_phi :
  block_edge_args fixture_ssa LoopIncoming = [NextValue] /\
  edge_use fixture_uses BackPhi = [NextValue] /\
  edge_def fixture_uses LoopInstruction = [NextValue] /\
  edge_def fixture_uses LoopParameters = [PhiValue] /\
  Graph.target fixture_graph BackPhi = Graph.source fixture_graph LoopParameters.
Proof.
  vm_compute; repeat split.
Qed.

(** * Reachability and static homes *)

Definition fixture_point_encoding : encoding fixture_point.
Proof.
  refine (Encoding fixture_point
    (fun n =>
       match n with
       | EntryBefore => 1%positive
       | EntryBody => 2%positive
       | EntryAfter => 3%positive
       | LoopBefore => 4%positive
       | LoopBody => 5%positive
       | LoopAfter => 6%positive
       | DeadBefore => 7%positive
       | DeadAfter => 8%positive
       end) _).
  intros [] [] Hcode; cbn in Hcode; congruence.
Defined.

Definition fixture_prepared := prepare fixture_point_encoding fixture_graph.

Example fixture_ready : ready fixture_point_encoding fixture_graph fixture_prepared.
Proof.
  apply prepare_ready; [exact fixture_point_graph_wf|exact fixture_point_out_nodup].
Qed.

Example fixture_dominance_from_search d n :
  FinSet.mem fixture_point_encoding n
    (visited (dfs fixture_prepared (FinSet.add fixture_point_encoding d FinSet.empty)
      [EntryBefore])) = false -> dominates fixture_graph d n.
Proof.
  intro Habsent; apply (proj2 (dominates_iff_unreachable_without
    fixture_point_encoding fixture_graph d n)); intro Hreachable.
  pose proof (dfs_exact fixture_point_encoding fixture_graph fixture_prepared n [EntryBefore]
    (FinSet.add fixture_point_encoding d FinSet.empty) fixture_ready
    (entries_in fixture_point_graph_wf)) as [Hexact _].
  change (reachable (without fixture_point_encoding
    (FinSet.add fixture_point_encoding d FinSet.empty)
    (set_entries fixture_graph [EntryBefore])) n) in Hreachable.
  apply (proj2 Hexact) in Hreachable; rewrite Habsent in Hreachable; discriminate.
Qed.

Example unreachable_component :
  In DeadBefore (Graph.nodes (live_graph (point_model fixture_ssa))) /\
  In DeadAfter (points_in_block fixture_ssa DeadBlock) /\
  point_definition fixture_ssa UndefinedDead = None /\
  FinSet.mem fixture_point_encoding DeadAfter
    (visited (dfs fixture_prepared FinSet.empty [EntryBefore])) = false.
Proof.
  vm_compute; intuition congruence.
Qed.

Example reachable_undefined_use_excluded n :
  reachable fixture_graph n -> n <> DeadBefore /\ n <> DeadAfter.
Proof.
  intro Hreachable.
  apply (proj2 (reachable_dfs fixture_point_encoding fixture_graph fixture_prepared n
    fixture_ready)) in Hreachable.
  destruct n; vm_compute in Hreachable |- *; intuition discriminate.
Qed.

Example fixture_reachable_ssa : reachable_point_ssa fixture_ssa.
Proof.
  constructor.
  - exists EntryBefore; reflexivity.
  - intros n x Hreachable Huse.
    pose proof (reachable_undefined_use_excluded n Hreachable) as Hnotdead.
    destruct n, x; cbn [point_use_at fixture_uses fixture_graph point_model fixture_ssa]
      in Huse; try solve [intuition discriminate].
    all: destruct Huse as [Hexit|[e [Hedge Huse]]];
      try solve [cbn in Hexit; intuition discriminate].
    all: try (destruct e; cbn in Hedge, Huse; try solve [intuition discriminate]).
    all: eexists; split; [reflexivity|split].
    all: try (apply (proj1 (reachable_dfs fixture_point_encoding fixture_graph fixture_prepared _
      fixture_ready)); vm_compute; reflexivity).
    all: split; [apply fixture_dominance_from_search; vm_compute; reflexivity|discriminate].
  - intros n e x _ Hedge Hdef; destruct n, e, x; cbn in Hedge, Hdef |- *;
      intuition congruence.
  - intros x d e Hhome _ Hedge; destruct x, d, e; cbn in Hhome, Hedge |- *;
      intuition congruence.
Qed.

Example loop_repeats_the_same_static_definitions :
  path fixture_graph LoopBefore [LoopParameters; LoopInstruction; BackPhi;
    LoopParameters; LoopInstruction; BackPhi] LoopBefore /\
  point_definition fixture_ssa PhiValue = Some LoopBefore /\
  point_definition fixture_ssa NextValue = Some LoopBody.
Proof.
  split.
  - apply (path_cons (g := fixture_graph) LoopParameters); [now left|].
    apply (path_cons (g := fixture_graph) LoopInstruction); [now left|].
    apply (path_cons (g := fixture_graph) BackPhi); [now left|].
    apply (path_cons (g := fixture_graph) LoopParameters); [now left|].
    apply (path_cons (g := fixture_graph) LoopInstruction); [now left|].
    apply (path_cons (g := fixture_graph) BackPhi); [now left|apply path_nil].
  - vm_compute; split; reflexivity.
Qed.

(** * Use before definition on one edge *)

Definition same_edge_uses : point_uses bool unit nat :=
  {| live_graph :=
       {| Graph.entries := [false];
          Graph.nodes := [false; true];
          Graph.out := fun n => if n then [] else [tt];
          Graph.source := fun _ => false;
          Graph.target := fun _ => true |};
     edge_use := fun _ => [0];
     edge_def := fun _ => [0];
     exit_use := fun _ => [] |}.

Example same_edge_use_and_definition :
  (edge_use same_edge_uses tt, edge_def same_edge_uses tt) = ([0], [0]).
Proof.
  vm_compute; reflexivity.
Qed.

Example same_edge_use_is_live : syntactic_live same_edge_uses 0 false.
Proof.
  apply live_edge_use with (e := tt); vm_compute; now left.
Qed.

Example same_edge_no_use_after_definition : ~ syntactic_live same_edge_uses 0 true.
Proof.
  intro Hlive; inversion Hlive as [n Hexit|n e Hedge Huse|n e Hedge Hkill Hnext].
  - cbn in Hexit; contradiction.
  - cbn in Hedge; contradiction.
  - cbn in Hedge; contradiction.
Qed.

Example kill_blocks_later_use : ~ syntactic_live fixture_uses PhiValue LoopBefore.
Proof.
  intro Hlive; inversion Hlive as [n Hexit|n e Hedge Huse|n e Hedge Hkill Hnext]; subst.
  - cbn in Hexit; contradiction.
  - cbn in Hedge; destruct Hedge as [<-|[]]; cbn in Huse; contradiction.
  - cbn in Hedge; destruct Hedge as [<-|[]]; apply Hkill; now left.
Qed.

Example unreachable_use_is_syntactically_live :
  syntactic_live fixture_uses UndefinedDead DeadBefore.
Proof.
  apply live_edge_next with (e := DeadParameters); [now left|cbn; tauto|].
  apply live_exit; now left.
Qed.

(** * Exit operands *)

Inductive fixture_exit : Type :=
  | FinalPoint
  | TrapPoint
  | StopPoint.

Definition fixture_exit_uses : point_uses fixture_exit Empty_set nat :=
  {| live_graph :=
       {| Graph.entries := [FinalPoint; TrapPoint; StopPoint];
          Graph.nodes := [FinalPoint; TrapPoint; StopPoint];
          Graph.out := fun _ => [];
          Graph.source := fun e : Empty_set => match e with end;
          Graph.target := fun e : Empty_set => match e with end |};
     edge_use := fun e : Empty_set => match e with end;
     edge_def := fun e : Empty_set => match e with end;
     exit_use := fun n =>
       match n with
       | FinalPoint => [10]
       | TrapPoint => [20]
       | StopPoint => [30]
       end |}.

Example final_trap_stop_exit_operands :
  (exit_use fixture_exit_uses FinalPoint, exit_use fixture_exit_uses TrapPoint,
   exit_use fixture_exit_uses StopPoint) = ([10], [20], [30]).
Proof.
  vm_compute; reflexivity.
Qed.

Example final_trap_stop_are_live :
  syntactic_live fixture_exit_uses 10 FinalPoint /\
  syntactic_live fixture_exit_uses 20 TrapPoint /\
  syntactic_live fixture_exit_uses 30 StopPoint.
Proof.
  repeat split; apply live_exit; vm_compute; now left.
Qed.
