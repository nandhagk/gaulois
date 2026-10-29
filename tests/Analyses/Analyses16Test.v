(** * Expression family and phi-placement examples

    A diamond computes a successor expression on each branch before binding a join parameter.
    For example, the left and right edges substitute different values for the join expression.
    Builds on: AnalysesSsaPreGraph, ViewsSsaPoints and GraphDominators. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators.
From Gaulois.Views Require Import ViewsGraph ViewsSsa ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesAvailable AnalysesSsaPreGraph.
Import List.ListNotations.

Inductive pre_test_block : Type :=
  | PreEntry
  | PreLeft
  | PreRight
  | PreJoin.

Inductive pre_test_block_edge : Type :=
  | PreToLeft
  | PreToRight
  | PreLeftJoin
  | PreRightJoin
  | PreExit.

Inductive pre_test_stage : Type :=
  | PreBefore
  | PreBody
  | PreBetween
  | PreAfter.

Inductive pre_test_value : Type :=
  | PreX
  | PreY
  | PreZ.

Inductive pre_test_edge : Type :=
  | PreBind (b : pre_test_block)
  | PreCompute (b : pre_test_block)
  | PreAgain (b : pre_test_block)
  | PreCross (be : pre_test_block_edge).

Definition pre_test_block_encoding : encoding pre_test_block.
Proof.
  refine (Encoding _ (fun b => match b with
    | PreEntry => 1%positive
    | PreLeft => 2%positive
    | PreRight => 3%positive
    | PreJoin => 4%positive
    end) _).
  intros [] [] Heq; cbn in Heq; congruence.
Defined.

Definition pre_test_block_edge_encoding : encoding pre_test_block_edge.
Proof.
  refine (Encoding _ (fun be => match be with
    | PreToLeft => 1%positive
    | PreToRight => 2%positive
    | PreLeftJoin => 3%positive
    | PreRightJoin => 4%positive
    | PreExit => 5%positive
    end) _).
  intros [] [] Heq; cbn in Heq; congruence.
Defined.

Definition pre_test_stage_encoding : encoding pre_test_stage.
Proof.
  refine (Encoding _ (fun stage => match stage with
    | PreBefore => 1%positive
    | PreBody => 2%positive
    | PreBetween => 3%positive
    | PreAfter => 4%positive
    end) _).
  intros [] [] Heq; cbn in Heq; congruence.
Defined.

Definition pre_test_value_encoding : encoding pre_test_value.
Proof.
  refine (Encoding _ (fun x => match x with
    | PreX => 1%positive
    | PreY => 2%positive
    | PreZ => 3%positive
    end) _).
  intros [] [] Heq; cbn in Heq; congruence.
Defined.

Definition pre_test_point_encoding :=
  pair_encoding pre_test_block_encoding pre_test_stage_encoding.

Definition pre_test_edge_encoding : encoding pre_test_edge.
Proof.
  set (codes := sum_encoding pre_test_block_encoding
    (sum_encoding pre_test_block_encoding
      (sum_encoding pre_test_block_encoding pre_test_block_edge_encoding))).
  refine (Encoding _ (fun e => encode codes (match e with
    | PreBind b => inl b
    | PreCompute b => inr (inl b)
    | PreAgain b => inr (inr (inl b))
    | PreCross be => inr (inr (inr be))
    end)) _).
  intros e e' Heq; apply (encode_injective codes) in Heq.
  destruct e, e'; cbn in Heq; inversion Heq; reflexivity.
Defined.

Definition pre_test_blocks : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft; PreToRight]
       | PreLeft => [PreLeftJoin]
       | PreRight => [PreRightJoin]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreToRight | PreExit => PreEntry
       | PreLeftJoin => PreLeft
       | PreRightJoin => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreExit => PreLeft
       | PreToRight => PreRight
       | PreLeftJoin | PreRightJoin => PreJoin
       end |}.

Definition pre_test_points : Graph.t (pre_test_block * pre_test_stage) pre_test_edge :=
  {| Graph.entries := [(PreEntry, PreBefore)];
     Graph.nodes := list_prod (Graph.nodes pre_test_blocks)
       [PreBefore; PreBody; PreBetween; PreAfter];
     Graph.out := fun n => match n with
       | (b, PreBefore) => [PreBind b]
       | (b, PreBody) => [PreCompute b]
       | (b, PreBetween) => [PreAgain b]
       | (b, PreAfter) => map PreCross (Graph.out pre_test_blocks b)
       end;
     Graph.source := fun e => match e with
       | PreBind b => (b, PreBefore)
       | PreCompute b => (b, PreBody)
       | PreAgain b => (b, PreBetween)
       | PreCross be => (Graph.source pre_test_blocks be, PreAfter)
       end;
     Graph.target := fun e => match e with
       | PreBind b => (b, PreBody)
       | PreCompute b => (b, PreBetween)
       | PreAgain b => (b, PreAfter)
       | PreCross be => (Graph.target pre_test_blocks be, PreBefore)
       end |}.

Definition pre_test_params (b : pre_test_block) : list pre_test_value :=
  match b with
  | PreEntry => [PreX; PreY]
  | PreJoin => [PreZ]
  | PreLeft | PreRight => []
  end.

Definition pre_test_args (be : pre_test_block_edge) : list pre_test_value :=
  match be with
  | PreLeftJoin => [PreX]
  | PreRightJoin => [PreY]
  | PreToLeft | PreToRight | PreExit => []
  end.

Definition pre_test_occurrence (e : pre_test_edge) : option pre_test_value :=
  match e with
  | PreCompute PreLeft => Some PreX
  | PreCompute PreRight => Some PreY
  | PreCompute PreJoin => Some PreZ
  | PreAgain PreLeft => Some PreX
  | PreAgain PreRight => Some PreY
  | PreAgain PreJoin => Some PreZ
  | _ => None
  end.

Definition pre_test_model : point_uses (pre_test_block * pre_test_stage)
    pre_test_edge pre_test_value :=
  {| live_graph := pre_test_points;
     edge_use := fun e => match e with
       | PreBind _ => []
       | PreCompute _ | PreAgain _ => match pre_test_occurrence e with
         | Some x => [x]
         | None => []
         end
       | PreCross be => pre_test_args be
       end;
     edge_def := fun e => match e with
       | PreBind b => pre_test_params b
       | _ => []
       end;
     exit_use := fun _ => [] |}.

Definition pre_test_definition (x : pre_test_value) : pre_test_block * pre_test_stage :=
  match x with
  | PreX | PreY => (PreEntry, PreBefore)
  | PreZ => (PreJoin, PreBefore)
  end.

Definition pre_test_ssa : ssa_points pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value :=
  {| point_model := pre_test_model;
     block_graph := pre_test_blocks;
     points_in_block := fun b => [(b, PreBefore); (b, PreBody); (b, PreBetween); (b, PreAfter)];
     instruction_edges := fun b => [PreBind b; PreCompute b; PreAgain b];
     parameter_edge := PreBind;
     block_of_point := fst;
     block_edge_of := fun e => match e with
       | PreCross be => Some be
       | _ => None
       end;
     block_params := pre_test_params;
     block_edge_args := pre_test_args;
     point_definition := fun x => Some (pre_test_definition x) |}.

Definition pre_test_block_view : graph_view unit unit pre_test_block pre_test_block_edge :=
  GraphView pre_test_blocks (fun _ => PreEntry) (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition pre_test_point_view : graph_view unit unit
    (pre_test_block * pre_test_stage) pre_test_edge :=
  GraphView pre_test_points (fun _ => (PreEntry, PreBefore))
    (fun _ _ _ _ => False) (fun _ _ _ => False).

Definition pre_test_view : ssa_view unit unit pre_test_block pre_test_block_edge
    pre_test_value unit nat :=
  {| base := pre_test_block_view;
     def := fun x => match x with
       | PreX => Param PreEntry 0
       | PreY => Param PreEntry 1
       | PreZ => Param PreJoin 0
       end;
     home := fun x => fst (pre_test_definition x);
     params := pre_test_params;
     edge_args := pre_test_args;
     edge_guard := fun _ => [];
     val := fun _ _ => Some 0;
     op_eval := fun _ _ => Some 0;
     truth := fun _ => false |}.

Definition pre_test_translate (be : pre_test_block_edge) (x : pre_test_value) : pre_test_value :=
  match be, x with
  | PreLeftJoin, PreZ => PreX
  | PreRightJoin, PreZ => PreY
  | _, _ => x
  end.

Definition pre_test_expression : pre_expr_ssa unit unit pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value unit nat pre_test_value :=
  {| pre_ssa_points := pre_test_ssa;
     pre_ssa_view := pre_test_view;
     pre_expression := PreExpressionView
       (GenKillView pre_test_point_view (fun e => match pre_test_occurrence e with
         | Some x => [x]
         | None => []
         end) (fun e x => existsb (fun y => Pos.eqb (encode pre_test_value_encoding x)
           (encode pre_test_value_encoding y)) (edge_def pre_test_model e)) (fun _ _ => Some 1))
       (fun _ => true) pre_test_occurrence;
     pre_seed_expressions := [PreX; PreY; PreZ];
     pre_value_universe := [PreX; PreY; PreZ];
     pre_expression_shape := fun _ => 1%positive;
     pre_operands := fun x => [x];
     pre_expr_eval := fun x env => option_map S (env x);
     pre_phi_translate := fun be x => Some (pre_test_translate be x);
     pre_initial_available := fun _ => false;
     pre_exit_point := fun _ => false |}.

(* Exhaust the small fixture carriers when checking graph and SSA structure. *)
Local Ltac pre_test_cases :=
  repeat match goal with
  | b : pre_test_block |- _ => destruct b
  | be : pre_test_block_edge |- _ => destruct be
  | stage : pre_test_stage |- _ => destruct stage
  | e : pre_test_edge |- _ => destruct e
  | x : pre_test_value |- _ => destruct x
  | n : pre_test_block * pre_test_stage |- _ => destruct n
  end.

(* Distinct constructor lists discharge the finite graph's structural uniqueness checks. *)
Local Ltac pre_test_distinct := repeat constructor; cbn; intuition congruence.

(** The block diamond is well formed and has no incoming entry edge. *)
Example pre_test_blocks_wf : graph_wf pre_test_blocks.
Proof.
  constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
Qed.

(** All before, body and after points obey the original block-edge identities. *)
Example pre_test_points_wf : graph_wf pre_test_points.
Proof.
  constructor.
  - pre_test_distinct.
  - intros [b stage] Hentry; pre_test_cases; cbn in *; intuition congruence.
  - intros n e Hedge; pre_test_cases; cbn in *; intuition congruence.
  - intros n e Hnode Hedge; pre_test_cases; cbn in *; intuition congruence.
Qed.

(** The finite point fixture satisfies every ordered-point and phi-edge law. *)
Example pre_test_points_laws : ssa_point_laws pre_test_ssa.
Proof.
  constructor.
  - exact pre_test_points_wf.
  - intro n; pre_test_cases; pre_test_distinct.
  - exact pre_test_blocks_wf.
  - intro b; pre_test_cases; pre_test_distinct.
  - intros [b stage]; split; intro Hnode.
    + exists b; pre_test_cases; cbn; tauto.
    + pre_test_cases; cbn; tauto.
  - intro b; pre_test_cases; pre_test_distinct.
  - intros b n Hb Hin; pre_test_cases; cbn in *; intuition congruence.
  - intros b Hb; destruct b; discriminate.
  - intros b Hb; cbn;
      repeat (eapply point_chain_step; [now left|reflexivity|]); apply point_chain_one.
  - intros b e Hb Hin; pre_test_cases; cbn in *; intuition congruence.
  - intros n e Hn He Hi; pre_test_cases; cbn in *; intuition congruence.
  - intros b Hb; reflexivity.
  - intros b x Hb; reflexivity.
  - intros n e Hn He; pre_test_cases; cbn in *; intuition congruence.
  - intros be Hbe; destruct be; reflexivity.
  - intros n e be Hn He Hp x Hx; destruct e as [b|b|b|edge];
      cbn in Hp; try discriminate.
    inversion Hp; subst edge; exact Hx.
  - intros be Hbe; exists (Graph.source pre_test_blocks be, PreAfter), (PreCross be).
    destruct be; cbn in *; intuition congruence.
  - intros e1 e2 be He1 He2 Hp1 Hp2; destruct e1, e2;
      cbn in Hp1, Hp2; congruence.
Qed.

(** * Constant-expression control-flow fixtures *)

Definition pre_flow_points (g : Graph.t pre_test_block pre_test_block_edge) :
    Graph.t (pre_test_block * pre_test_stage) pre_test_edge :=
  {| Graph.entries := [(PreEntry, PreBefore)];
     Graph.nodes := list_prod [PreEntry; PreLeft; PreRight; PreJoin]
       [PreBefore; PreBody; PreBetween; PreAfter];
     Graph.out := fun n => match n with
       | (b, PreBefore) => [PreBind b]
       | (b, PreBody) => [PreCompute b]
       | (b, PreBetween) => [PreAgain b]
       | (b, PreAfter) => map PreCross (Graph.out g b)
       end;
     Graph.source := fun e => match e with
       | PreBind b => (b, PreBefore)
       | PreCompute b => (b, PreBody)
       | PreAgain b => (b, PreBetween)
       | PreCross be => (Graph.source g be, PreAfter)
       end;
     Graph.target := fun e => match e with
       | PreBind b => (b, PreBody)
       | PreCompute b => (b, PreBetween)
       | PreAgain b => (b, PreAfter)
       | PreCross be => (Graph.target g be, PreBefore)
       end |}.

Definition pre_flow_model g : point_uses (pre_test_block * pre_test_stage) pre_test_edge unit :=
  {| live_graph := pre_flow_points g;
     edge_use := fun _ => [];
     edge_def := fun _ => [];
     exit_use := fun _ => [] |}.

Definition pre_flow_ssa g : ssa_points pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge unit :=
  {| point_model := pre_flow_model g;
     block_graph := g;
     points_in_block := fun b => [(b, PreBefore); (b, PreBody); (b, PreBetween); (b, PreAfter)];
     instruction_edges := fun b => [PreBind b; PreCompute b; PreAgain b];
     parameter_edge := PreBind;
     block_of_point := fst;
     block_edge_of := fun e => match e with
       | PreCross be => Some be
       | _ => None
       end;
     block_params := fun _ => [];
     block_edge_args := fun _ => [];
     point_definition := fun _ => None |}.

Definition pre_flow_expression g (occurs : pre_test_edge -> bool) :
    pre_expr_ssa unit unit pre_test_block pre_test_block_edge
      (pre_test_block * pre_test_stage) pre_test_edge unit unit nat unit :=
  {| pre_ssa_points := pre_flow_ssa g;
     pre_ssa_view := SsaView
       (GraphView g (fun _ => PreEntry) (fun _ _ _ _ => False) (fun _ _ _ => False))
       (fun _ => Param PreEntry 0) (fun _ => PreEntry) (fun _ => []) (fun _ => [])
       (fun _ => []) (fun _ _ => Some 0) (fun _ _ => Some 0) (fun _ => false);
     pre_expression := PreExpressionView
       (GenKillView (GraphView (pre_flow_points g) (fun _ => (PreEntry, PreBefore))
         (fun _ _ _ _ => False) (fun _ _ _ => False))
         (fun e => if occurs e then [tt] else []) (fun _ _ => false) (fun _ _ => Some 0))
       (fun _ => true) (fun e => if occurs e then Some tt else None);
     pre_seed_expressions := [tt];
     pre_value_universe := [];
     pre_expression_shape := fun _ => 1%positive;
     pre_operands := fun _ => [];
     pre_expr_eval := fun _ _ => Some 0;
     pre_phi_translate := fun _ _ => Some tt;
     pre_initial_available := fun _ => false;
     pre_exit_point := fun _ => false |}.

Local Ltac pre_flow_cross_members :=
  repeat match goal with
  | H : In _ (map PreCross _) |- _ =>
      apply in_map_iff in H; destruct H as [flow_edge [flow_eq H]];
      try discriminate; injection flow_eq as flow_eq; subst flow_edge
  end.

Local Lemma pre_flow_points_wf g : graph_wf g ->
  Graph.nodes g = [PreEntry; PreLeft; PreRight; PreJoin] -> graph_wf (pre_flow_points g).
Proof.
  intros Hgraph Hnodes; constructor.
  - pre_test_distinct.
  - intros [b stage] Hin; destruct b, stage; cbn in *; intuition congruence.
  - intros [b stage] e Hin; destruct stage; destruct e as [owner|owner|owner|be];
      cbn in *;
      try (intuition congruence); pre_flow_cross_members.
    rewrite (out_source Hgraph b be Hin); reflexivity.
  - intros [b stage] e Hnode Hin; clear Hnode; destruct stage; destruct e as [owner|owner|owner|be];
      cbn in *;
      try solve [destruct b; cbn in *; intuition congruence]; pre_flow_cross_members.
    change (In (Graph.target g be, PreBefore) (list_prod
      [PreEntry; PreLeft; PreRight; PreJoin] [PreBefore; PreBody; PreBetween; PreAfter])).
    apply in_prod_iff; split; [|cbn; tauto].
    rewrite <- Hnodes; apply (out_target_in Hgraph b be); [rewrite Hnodes; destruct b; cbn; tauto|].
    exact Hin.
Qed.

Local Lemma pre_flow_points_laws g : graph_wf g ->
  Graph.nodes g = [PreEntry; PreLeft; PreRight; PreJoin] ->
  (forall b, NoDup (Graph.out g b)) -> ssa_point_laws (pre_flow_ssa g).
Proof.
  intros Hgraph Hnodes Hout; constructor.
  - apply pre_flow_points_wf; assumption.
  - intros [b stage]; destruct stage; cbn; try pre_test_distinct.
    apply nodup_map_injective; [intros be be' Heq; inversion Heq; reflexivity|apply Hout].
  - exact Hgraph.
  - exact Hout.
  - intros [b stage]; split; intro Hin.
    + clear Hin; exists b; split.
      * change (In b (Graph.nodes g)); rewrite Hnodes; destruct b; cbn; tauto.
      * destruct stage; cbn; intuition congruence.
    + clear Hin; destruct b, stage; cbn; intuition congruence.
  - intro b; destruct b; pre_test_distinct.
  - intros b [owner stage] Hb Hin; cbn in *; intuition congruence.
  - intros b Hb; discriminate.
  - intros b Hb; cbn; repeat (eapply point_chain_step; [now left|reflexivity|]);
      apply point_chain_one.
  - intros b e Hb Hin; destruct e; cbn in *; intuition congruence.
  - intros [b stage] e Hnode Hin Hi; clear Hnode; destruct stage, e; cbn in *;
      try (intuition congruence); pre_flow_cross_members.
  - intros b Hb; reflexivity.
  - intros b x Hb; reflexivity.
  - intros [b stage] e Hnode Hin; clear Hnode; destruct stage; destruct e as [owner|owner|owner|be];
    cbn in *;
      try (intuition congruence); pre_flow_cross_members.
    split; [exact Hin|]; repeat split; reflexivity.
  - intros be Hbe; reflexivity.
  - intros n e be Hn He Hproject x Huse; contradiction.
  - intros be Hbe; apply in_flat_map in Hbe; destruct Hbe as [b [Hb Hedge]].
    exists (b, PreAfter), (PreCross be); cbn; split.
    + change (In (b, PreAfter) (list_prod [PreEntry; PreLeft; PreRight; PreJoin]
        [PreBefore; PreBody; PreBetween; PreAfter])).
      apply in_prod_iff; split; [rewrite <- Hnodes; exact Hb|cbn; tauto].
    + split; [apply in_map; exact Hedge|reflexivity].
  - intros e e' be He He' Hp Hp'; destruct e, e'; cbn in *; congruence.
Qed.

Local Lemma pre_flow_laws g occurs :
  graph_wf g -> Graph.nodes g = [PreEntry; PreLeft; PreRight; PreJoin] ->
  Graph.entries g = [PreEntry] -> (forall b, NoDup (Graph.out g b)) ->
  (forall b, reachable g b) -> (forall n, reachable (pre_flow_points g) n) ->
  (forall be, In be (edges_of g) -> Graph.target g be <> PreEntry) ->
  (forall b, occurs (PreBind b) = false) ->
  (forall be, occurs (PreCross be) = false) ->
  pre_expr_ssa_laws unit_encoding (pre_flow_expression g occurs).
Proof.
  intros Hgraph Hnodes Hentry Hout Hreach Hpointsreach Hnoentry Hbind Hcross; constructor.
  - apply pre_flow_points_laws; assumption.
  - constructor.
    + exists (PreEntry, PreBefore); reflexivity.
    + intros n x Hn [Hexit|[e [He Huse]]]; contradiction.
    + intros n e x Hn He Hdef; contradiction.
    + intros x d e Hdef; discriminate.
  - reflexivity.
  - reflexivity.
  - intros b Hb; apply Hreach.
  - intros n Hn; apply Hpointsreach.
  - exists PreEntry, (PreEntry, PreBefore); repeat split; try reflexivity; exact Hentry.
  - intros b be Hb Hbe; cbn in Hb; rewrite Hentry in Hb.
    destruct Hb as [Heq|Hfalse]; [subst b; exact (Hnoentry be Hbe)|contradiction].
  - intro b; constructor.
  - constructor.
  - intros e [] Hcomputed; left; reflexivity.
  - intros u Hinitial; discriminate.
  - intros u Hu x Hx; contradiction.
  - intros [] [] Hu Hv Hshape Hoperands; reflexivity.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; reflexivity.
  - intros e u He Hu Hkill; discriminate.
  - intros e x He Hdef; contradiction.
  - intros e be He Hprojection; reflexivity.
  - intros e u Hcomputed; destruct e as [b|b|b|be]; cbn in Hcomputed.
    + rewrite Hbind in Hcomputed; discriminate.
    + split; [reflexivity|intros block Hfalse; discriminate].
    + split; [reflexivity|intros block Hfalse; discriminate].
    + rewrite Hcross in Hcomputed; discriminate.
  - intros be u Hbe Hu; exists tt; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; reflexivity.
Qed.

(** * Operand-sensitive control-flow fixtures *)

Definition pre_operand_model {V} g (parameters : pre_test_block -> list V)
    (arguments : pre_test_block_edge -> list V) (ordinary uses : pre_test_edge -> list V) :
    point_uses (pre_test_block * pre_test_stage) pre_test_edge V :=
  {| live_graph := pre_flow_points g;
     edge_use := fun e => match e with
       | PreBind _ => []
       | PreCross be => arguments be
       | _ => uses e
       end;
     edge_def := fun e => match e with
       | PreBind b => parameters b
       | PreCross _ => []
       | _ => ordinary e
       end;
     exit_use := fun _ => [] |}.

Definition pre_operand_points {V} g parameters arguments ordinary uses
    (definition_point : V -> option (pre_test_block * pre_test_stage)) :
    ssa_points pre_test_block pre_test_block_edge (pre_test_block * pre_test_stage) pre_test_edge V
      :=
  {| point_model := pre_operand_model g parameters arguments ordinary uses;
     block_graph := g;
     points_in_block := fun b => [(b, PreBefore); (b, PreBody); (b, PreBetween); (b, PreAfter)];
     instruction_edges := fun b => [PreBind b; PreCompute b; PreAgain b];
     parameter_edge := PreBind;
     block_of_point := fst;
     block_edge_of := fun e => match e with
       | PreCross be => Some be
       | _ => None
       end;
     block_params := parameters;
     block_edge_args := arguments;
     point_definition := definition_point |}.

Local Lemma pre_operand_points_laws {V} g parameters arguments ordinary uses
    (definition_point : V -> option (pre_test_block * pre_test_stage)) :
  graph_wf g -> Graph.nodes g = [PreEntry; PreLeft; PreRight; PreJoin] ->
  (forall b, NoDup (Graph.out g b)) ->
  (forall be, In be (edges_of g) -> length (arguments be) = length (parameters (Graph.target g be)))
    ->
  ssa_point_laws (pre_operand_points g parameters arguments ordinary uses definition_point).
Proof.
  intros Hgraph Hnodes Hout Hlength; pose proof (pre_flow_points_laws g Hgraph Hnodes Hout) as
    Hflow.
  constructor.
  - exact (points_graph_wf Hflow).
  - exact (points_out_nodup Hflow).
  - exact (blocks_graph_wf Hflow).
  - exact (blocks_out_nodup Hflow).
  - exact (points_covered Hflow).
  - exact (points_unique Hflow).
  - exact (points_owner Hflow).
  - exact (blocks_nonempty Hflow).
  - exact (points_ordered Hflow).
  - exact (instruction_edges_internal Hflow).
  - exact (instruction_edges_complete Hflow).
  - exact (parameter_edge_first Hflow).
  - intros b x Hb; reflexivity.
  - exact (point_edge_projection Hflow).
  - exact Hlength.
  - intros n e be Hn He Hprojection x Huse; destruct e as [b|b|b|edge];
      cbn in Hprojection; try discriminate.
    inversion Hprojection; subst edge; exact Huse.
  - exact (block_edge_covered Hflow).
  - exact (block_edge_unique Hflow).
Qed.

Definition pre_operand_use {V} (occurs : pre_test_edge -> option V) e : list V :=
  match occurs e with
  | Some x => [x]
  | None => []
  end.

Definition pre_operand_rename {V} (EV : encoding V) (g : Graph.t pre_test_block pre_test_block_edge)
    (parameters : pre_test_block -> list V) (arguments : pre_test_block_edge -> list V) be x : V :=
  match Map.get EV x (Map.of_list EV (combine (parameters (Graph.target g be)) (arguments be))) with
  | Some y => y
  | None => x
  end.

Definition pre_operand_expression {V} (EV : encoding V) g parameters arguments ordinary occurs
    (view_definition : V -> definition pre_test_block V unit)
    (definition_point : V -> pre_test_block * pre_test_stage) initial universe :
    pre_expr_ssa unit unit pre_test_block pre_test_block_edge
      (pre_test_block * pre_test_stage) pre_test_edge V unit nat V :=
  {| pre_ssa_points := pre_operand_points g parameters arguments ordinary (pre_operand_use occurs)
       (fun x => Some (definition_point x));
     pre_ssa_view := SsaView
       (GraphView g (fun _ => PreEntry) (fun _ _ _ _ => False) (fun _ _ _ => False))
       view_definition (fun x => fst (definition_point x)) parameters arguments
       (fun _ => []) (fun _ _ => Some 0) (fun _ _ => Some 0) (fun _ => false);
     pre_expression := PreExpressionView
       (GenKillView (GraphView (pre_flow_points g) (fun _ => (PreEntry, PreBefore))
         (fun _ _ _ _ => False) (fun _ _ _ => False)) (pre_operand_use occurs)
         (fun e x => existsb (fun y => Pos.eqb (encode EV x) (encode EV y))
           (edge_def (pre_operand_model g parameters arguments ordinary (pre_operand_use occurs))
             e))
         (fun _ _ => Some 1)) (fun _ => true) occurs;
     pre_seed_expressions := universe;
     pre_value_universe := universe;
     pre_expression_shape := fun _ => 1%positive;
     pre_operands := fun x => [x];
     pre_expr_eval := fun x env => option_map S (env x);
     pre_phi_translate := fun be x => Some (pre_operand_rename EV g parameters arguments be x);
     pre_initial_available := initial;
     pre_exit_point := fun _ => false |}.

Local Lemma pre_operand_member {V} (EV : encoding V) x xs :
  existsb (fun y => Pos.eqb (encode EV x) (encode EV y)) xs = true -> In x xs.
Proof.
  intro Hmember; apply existsb_exists in Hmember; destruct Hmember as [y [Hy Heq]].
  apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst y; exact Hy.
Qed.

Local Lemma pre_operand_strict {V} g parameters arguments ordinary uses
    (definition_point : V -> pre_test_block * pre_test_stage) :
  ready pre_test_point_encoding (pre_flow_points g)
    (prepare pre_test_point_encoding (pre_flow_points g)) ->
  (forall n, reachable (pre_flow_points g) n) ->
  (forall n x, point_use_at (pre_operand_model g parameters arguments ordinary uses) n x ->
    dominates_b pre_test_point_encoding
      (dominator_tree (prepare pre_test_point_encoding (pre_flow_points g)))
      (definition_point x) n = true /\ definition_point x <> n) ->
  (forall n e x, In e (Graph.out (pre_flow_points g) n) ->
    In x (edge_def (pre_operand_model g parameters arguments ordinary uses) e) ->
    definition_point x = n) ->
  (forall x e, In e (Graph.out (pre_flow_points g) (definition_point x)) ->
    In x (edge_def (pre_operand_model g parameters arguments ordinary uses) e)) ->
  reachable_point_ssa (pre_operand_points g parameters arguments ordinary uses
    (fun x => Some (definition_point x))).
Proof.
  intros Hready Hreach Huses Hdefinitions Hkills; constructor.
  - exists (PreEntry, PreBefore); reflexivity.
  - intros n x Hreachable Huse; exists (definition_point x); split; [reflexivity|].
    split; [apply Hreach|]; destruct (Huses n x Huse) as [Hdominates Hne]; split; [|exact Hne].
    apply (proj1 (proj1 (dominator_tree_exact pre_test_point_encoding (pre_flow_points g) _
      Hready (dominator_exact_true _ _ _ Hready)) _ n Hreachable)); exact Hdominates.
  - intros n e x Hn He Hdef; change (Some (definition_point x) = Some n).
    f_equal; exact (Hdefinitions n e x He Hdef).
  - intros x d e Hdef Hd He; cbn in Hdef; inversion Hdef; subst d; exact (Hkills x e He).
Qed.

Local Lemma pre_operand_laws {V} (EV : encoding V) g parameters arguments ordinary occurs
    (view_definition : V -> definition pre_test_block V unit) definition_point initial universe :
  graph_wf g -> Graph.nodes g = [PreEntry; PreLeft; PreRight; PreJoin] ->
  Graph.entries g = [PreEntry] -> (forall b, NoDup (Graph.out g b)) ->
  (forall b, reachable g b) -> (forall n, reachable (pre_flow_points g) n) ->
  (forall be, In be (edges_of g) -> Graph.target g be <> PreEntry) ->
  (forall b, NoDup (parameters b)) -> NoDup universe -> (forall x, In x universe) ->
  (forall be, In be (edges_of g) -> length (arguments be) = length (parameters (Graph.target g be)))
    ->
  (forall b, occurs (PreBind b) = None) -> (forall be, occurs (PreCross be) = None) ->
  reachable_point_ssa (pre_operand_points g parameters arguments ordinary (pre_operand_use occurs)
    (fun x => Some (definition_point x))) ->
  (forall e x, In e (edges_of (pre_flow_points g)) ->
    In x (edge_def (pre_operand_model g parameters arguments ordinary (pre_operand_use occurs)) e)
      ->
    fst (definition_point x) = fst (Graph.source (pre_flow_points g) e)) ->
  pre_expr_ssa_laws EV (pre_operand_expression EV g parameters arguments ordinary occurs
    view_definition definition_point initial universe).
Proof.
  intros Hgraph Hnodes Hentry Hout Hreach Hpointsreach Hnoentry Hparameters Hvalues Hcomplete
    Hlength Hbind Hcross Hstrict Hhome; constructor.
  - apply pre_operand_points_laws; assumption.
  - exact Hstrict.
  - reflexivity.
  - reflexivity.
  - intros b Hb; apply Hreach.
  - intros n Hn; apply Hpointsreach.
  - exists PreEntry, (PreEntry, PreBefore); repeat split; try reflexivity; exact Hentry.
  - intros b be Hb Hbe; cbn in Hb; rewrite Hentry in Hb.
    destruct Hb as [Heq|Hfalse]; [subst b; exact (Hnoentry be Hbe)|contradiction].
  - exact Hparameters.
  - exact Hvalues.
  - intros e u Hcomputed; apply Hcomplete.
  - intros u Hinitial; apply pre_family_seed; apply Hcomplete.
  - intros u Hu x Hx; cbn in Hx; destruct Hx as [Heq|Hfalse];
      [subst x; apply Hcomplete|contradiction].
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u (or_introl eq_refl)); reflexivity.
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    exact (pre_operand_member EV u _ Hkill).
  - exact Hhome.
  - intros e be He Hproject; destruct e; cbn in Hproject; try discriminate; reflexivity.
  - intros e u Hcomputed; destruct e as [b|b|b|be]; cbn in Hcomputed.
    + rewrite Hbind in Hcomputed; discriminate.
    + split; [reflexivity|intros block Hfalse; discriminate].
    + split; [reflexivity|intros block Hfalse; discriminate].
    + rewrite Hcross in Hcomputed; discriminate.
  - intros be u Hbe Hu; eexists; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; cbn in Htranslate; inversion Htranslate; subst v; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; cbn in Htranslate; inversion Htranslate; subst v;
    reflexivity.
Qed.

Definition pre_parallel_blocks (two : bool) : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft]
       | PreLeft => [PreToRight]
       | PreRight => if two then [PreLeftJoin; PreRightJoin] else [PreLeftJoin]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreExit => PreEntry
       | PreToRight => PreLeft
       | PreLeftJoin | PreRightJoin => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreExit => PreLeft
       | PreToRight => PreRight
       | PreLeftJoin | PreRightJoin => PreJoin
       end |}.

Definition pre_parallel_occurs (e : pre_test_edge) : option pre_test_value :=
  match e with
  | PreCompute PreRight => Some PreX
  | PreAgain PreRight => Some PreY
  | PreCompute PreJoin => Some PreZ
  | _ => None
  end.

Definition pre_parallel_expression two := pre_operand_expression pre_test_value_encoding
  (pre_parallel_blocks two) pre_test_params pre_test_args (fun _ => []) pre_parallel_occurs
  (def pre_test_view) pre_test_definition (fun _ => false) [PreX; PreY; PreZ].

Example pre_parallel_blocks_wf : forall two, graph_wf (pre_parallel_blocks two).
Proof.
  intro two; constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; destruct two; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; destruct two; pre_test_cases; cbn in *; intuition congruence.
Qed.

Example pre_parallel_blocks_ready : forall two, ready pre_test_block_encoding (pre_parallel_blocks
  two)
    (prepare pre_test_block_encoding (pre_parallel_blocks two)).
Proof.
  intro two; apply prepare_ready; [apply pre_parallel_blocks_wf|].
  intro b; destruct two, b; pre_test_distinct.
Qed.

Example pre_parallel_points_ready : forall two,
  ready pre_test_point_encoding (pre_flow_points (pre_parallel_blocks two))
    (prepare pre_test_point_encoding (pre_flow_points (pre_parallel_blocks two))).
Proof.
  intro two; apply prepare_ready.
  - apply pre_flow_points_wf; [apply pre_parallel_blocks_wf|reflexivity].
  - exact (points_out_nodup (pre_flow_points_laws _ (pre_parallel_blocks_wf two) eq_refl
      ltac:(intro b; destruct two, b; pre_test_distinct))).
Qed.

Example pre_parallel_reachable : forall two n, reachable (pre_flow_points (pre_parallel_blocks two))
  n.
Proof.
  intros two [b stage]; apply (reachable_dfs pre_test_point_encoding _ _ (b, stage)
    (pre_parallel_points_ready two)); destruct two, b, stage; vm_compute; reflexivity.
Qed.

Local Lemma pre_parallel_uses_dominate : forall two n x,
  point_use_at (pre_operand_model (pre_parallel_blocks two) pre_test_params pre_test_args
    (fun _ => []) (pre_operand_use pre_parallel_occurs)) n x ->
  dominates_b pre_test_point_encoding
    (dominator_tree (prepare pre_test_point_encoding (pre_flow_points (pre_parallel_blocks two))))
    (pre_test_definition x) n = true /\ pre_test_definition x <> n.
Proof.
  intros two n x [Hexit|[e [Hedge Huse]]]; [contradiction|].
  destruct two; pre_test_cases; cbn in Hedge, Huse; try (exfalso; intuition congruence).
  all: (vm_compute; split; [reflexivity|discriminate]).
Qed.

Example pre_parallel_strict : forall two,
  reachable_point_ssa (pre_operand_points (pre_parallel_blocks two) pre_test_params pre_test_args
    (fun _ => []) (pre_operand_use pre_parallel_occurs) (fun x => Some (pre_test_definition x))).
Proof.
  intro two; apply pre_operand_strict.
  - apply pre_parallel_points_ready.
  - apply pre_parallel_reachable.
  - apply pre_parallel_uses_dominate.
  - intros n e x He Hdef; destruct two; pre_test_cases; cbn in *; intuition congruence.
  - intros x e He; destruct two; pre_test_cases; cbn in *; intuition congruence.
Qed.

(** Both the parallel-edge and single-predecessor variants satisfy the full adopted laws. *)
Example pre_parallel_expression_laws : forall two,
  pre_expr_ssa_laws pre_test_value_encoding (pre_parallel_expression two).
Proof.
  intro two; apply pre_operand_laws.
  - apply pre_parallel_blocks_wf.
  - reflexivity.
  - reflexivity.
  - intro b; destruct two, b; pre_test_distinct.
  - intro b; apply (reachable_dfs pre_test_block_encoding _ _ b (pre_parallel_blocks_ready two));
      destruct two, b; vm_compute; reflexivity.
  - apply pre_parallel_reachable.
  - intros be Hbe; destruct be; discriminate.
  - intro b; destruct b; pre_test_distinct.
  - pre_test_distinct.
  - intro x; destruct x; cbn; tauto.
  - intros be Hbe; destruct be; reflexivity.
  - intro b; reflexivity.
  - intro be; reflexivity.
  - apply pre_parallel_strict.
  - intros e x He Hdef; destruct two; pre_test_cases; cbn in *; intuition congruence.
Qed.

Definition pre_parallel_frg two := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
  (pre_parallel_expression two).

(** Distinct incoming identities with identical endpoints read different expression versions. *)
Example pre_parallel_distinct_arguments :
  Graph.source (pre_parallel_blocks true) PreLeftJoin =
    Graph.source (pre_parallel_blocks true) PreRightJoin /\
  Graph.target (pre_parallel_blocks true) PreLeftJoin =
    Graph.target (pre_parallel_blocks true) PreRightJoin /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreZ), PreLeftJoin)
    (frg_phi_operands (pre_parallel_frg true)) =
      Some (FrgOperand (FrFresh (PreCompute PreRight) PreX) true) /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreZ), PreRightJoin)
    (frg_phi_operands (pre_parallel_frg true)) =
      Some (FrgOperand (FrFresh (PreAgain PreRight) PreY) true).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** A listed non-entry parameter seeds its phi even with one incoming edge. *)
Example pre_single_predecessor_parameter_phi :
  length (pred_edges (prepare pre_test_block_encoding (pre_parallel_blocks false)) PreJoin) = 1 /\
  FinSet.mem (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreJoin, PreZ)
    (frg_phi_index (pre_parallel_frg false)) = true /\
  Map.get pre_test_edge_encoding (PreCompute PreJoin)
    (frg_occurrence_index (pre_parallel_frg false)) = Some (FrPhi PreJoin PreZ).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example pre_single_predecessor_needed :
  frg_phi_needed pre_test_block_encoding pre_test_value_encoding
    (pre_parallel_expression false) PreZ PreJoin.
Proof.
  eapply frg_phi_operand_param with (x := PreZ).
  - apply pre_family_seed; cbn; tauto.
  - cbn; tauto.
  - cbn; intuition discriminate.
  - left; reflexivity.
  - left; reflexivity.
Qed.

Definition pre_kill_cycle_blocks : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft]
       | PreLeft => [PreLeftJoin]
       | PreRight => [PreToRight; PreRightJoin]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreExit => PreEntry
       | PreLeftJoin => PreLeft
       | PreToRight | PreRightJoin => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreToRight | PreExit => PreLeft
       | PreLeftJoin => PreRight
       | PreRightJoin => PreJoin
       end |}.

Definition pre_kill_blocks (cyclic : bool) := if cyclic then pre_kill_cycle_blocks else
  pre_test_blocks.

Definition pre_kill_params (b : pre_test_block) : list pre_test_value :=
  match b with
  | PreEntry => [PreX; PreZ]
  | _ => []
  end.

Definition pre_kill_ordinary (e : pre_test_edge) : list pre_test_value :=
  match e with
  | PreCompute PreLeft => [PreY]
  | _ => []
  end.

Definition pre_kill_occurs (cyclic : bool) (e : pre_test_edge) : option pre_test_value :=
  match e with
  | PreCompute PreEntry => Some PreX
  | PreCompute PreRight => if cyclic then Some PreY else None
  | _ => None
  end.

Definition pre_kill_definition (x : pre_test_value) : pre_test_block * pre_test_stage :=
  match x with
  | PreY => (PreLeft, PreBody)
  | _ => (PreEntry, PreBefore)
  end.

Definition pre_kill_view_definition (x : pre_test_value) : definition pre_test_block pre_test_value
  unit :=
  match x with
  | PreX => Param PreEntry 0
  | PreZ => Param PreEntry 1
  | PreY => Op tt []
  end.

Definition pre_kill_initial cyclic (x : pre_test_value) : bool :=
  match x with
  | PreY => negb cyclic
  | _ => false
  end.

Definition pre_kill_expression cyclic := pre_operand_expression pre_test_value_encoding
  (pre_kill_blocks cyclic) pre_kill_params (fun _ => []) pre_kill_ordinary (pre_kill_occurs cyclic)
  pre_kill_view_definition pre_kill_definition (pre_kill_initial cyclic) [PreX; PreY; PreZ].

Example pre_kill_cycle_blocks_wf : graph_wf pre_kill_cycle_blocks.
Proof.
  constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
Qed.

Example pre_kill_blocks_wf : forall cyclic, graph_wf (pre_kill_blocks cyclic).
Proof.
  intros []; [exact pre_kill_cycle_blocks_wf|exact pre_test_blocks_wf].
Qed.

Example pre_kill_blocks_ready : forall cyclic, ready pre_test_block_encoding (pre_kill_blocks
  cyclic)
    (prepare pre_test_block_encoding (pre_kill_blocks cyclic)).
Proof.
  intro cyclic; apply prepare_ready; [apply pre_kill_blocks_wf|].
  intro b; destruct cyclic, b; pre_test_distinct.
Qed.

Example pre_kill_points_ready : forall cyclic,
  ready pre_test_point_encoding (pre_flow_points (pre_kill_blocks cyclic))
    (prepare pre_test_point_encoding (pre_flow_points (pre_kill_blocks cyclic))).
Proof.
  intro cyclic; apply prepare_ready.
  - apply pre_flow_points_wf; [apply pre_kill_blocks_wf|destruct cyclic; reflexivity].
  - exact (points_out_nodup (pre_flow_points_laws _ (pre_kill_blocks_wf cyclic)
      ltac:(destruct cyclic; reflexivity) ltac:(intro b; destruct cyclic, b; pre_test_distinct))).
Qed.

Example pre_kill_reachable : forall cyclic n, reachable (pre_flow_points (pre_kill_blocks cyclic))
  n.
Proof.
  intros cyclic [b stage]; apply (reachable_dfs pre_test_point_encoding _ _ (b, stage)
    (pre_kill_points_ready cyclic)); destruct cyclic, b, stage; vm_compute; reflexivity.
Qed.

Local Lemma pre_kill_uses_dominate : forall cyclic n x,
  point_use_at (pre_operand_model (pre_kill_blocks cyclic) pre_kill_params (fun _ => [])
    pre_kill_ordinary (pre_operand_use (pre_kill_occurs cyclic))) n x ->
  dominates_b pre_test_point_encoding
    (dominator_tree (prepare pre_test_point_encoding (pre_flow_points (pre_kill_blocks cyclic))))
    (pre_kill_definition x) n = true /\ pre_kill_definition x <> n.
Proof.
  intros cyclic n x [Hexit|[e [Hedge Huse]]]; [contradiction|].
  destruct cyclic; pre_test_cases; cbn in Hedge, Huse; try (exfalso; intuition congruence).
  all: (vm_compute; split; [reflexivity|discriminate]).
Qed.

Example pre_kill_strict : forall cyclic,
  reachable_point_ssa (pre_operand_points (pre_kill_blocks cyclic) pre_kill_params (fun _ => [])
    pre_kill_ordinary (pre_operand_use (pre_kill_occurs cyclic)) (fun x => Some (pre_kill_definition
      x))).
Proof.
  intro cyclic; apply pre_operand_strict.
  - apply pre_kill_points_ready.
  - apply pre_kill_reachable.
  - apply pre_kill_uses_dominate.
  - intros n e x He Hdef; destruct cyclic; pre_test_cases; cbn in *; intuition congruence.
  - intros x e He; destruct cyclic; pre_test_cases; cbn in *; intuition congruence.
Qed.

(** Ordinary definitions kill an operand on one branch or before a cyclic recomputation. *)
Example pre_kill_expression_laws : forall cyclic,
  pre_expr_ssa_laws pre_test_value_encoding (pre_kill_expression cyclic).
Proof.
  intro cyclic; apply pre_operand_laws.
  - apply pre_kill_blocks_wf.
  - destruct cyclic; reflexivity.
  - destruct cyclic; reflexivity.
  - intro b; destruct cyclic, b; pre_test_distinct.
  - intro b; apply (reachable_dfs pre_test_block_encoding _ _ b (pre_kill_blocks_ready cyclic));
      destruct cyclic, b; vm_compute; reflexivity.
  - apply pre_kill_reachable.
  - intros be Hbe; destruct cyclic, be; discriminate.
  - intro b; destruct b; pre_test_distinct.
  - pre_test_distinct.
  - intro x; destruct x; cbn; tauto.
  - intros be Hbe; destruct cyclic, be; reflexivity.
  - intro b; reflexivity.
  - intro be; reflexivity.
  - apply pre_kill_strict.
  - intros e x He Hdef; destruct cyclic; pre_test_cases; cbn in *; intuition congruence.
Qed.

Definition pre_kill_frg cyclic := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
  (pre_kill_expression cyclic).

(** The killed branch is unavailable while the other incoming edge keeps its initial version. *)
Example pre_one_branch_kill_arguments :
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreY), PreLeftJoin)
    (frg_phi_operands (pre_kill_frg false)) = Some (FrgOperand (FrUnavailable PreY) false) /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreY), PreRightJoin)
    (frg_phi_operands (pre_kill_frg false)) = Some (FrgOperand (FrInitial PreY) false) /\
  FinSet.mem (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreJoin, PreY)
    (frg_unsafe_seeds (pre_kill_frg false)) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The cycle's kill forces a fresh body version and marks the unused incoming phi unsafe. *)
Example pre_cyclic_kill_requires_fresh :
  Map.get pre_test_edge_encoding (PreCompute PreRight) (frg_occurrence_index (pre_kill_frg true)) =
    Some (FrFresh (PreCompute PreRight) PreY) /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreRight) (frg_fresh_index (pre_kill_frg true)) =
    true /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreLeft, PreY), PreToRight)
    (frg_phi_operands (pre_kill_frg true)) =
      Some (FrgOperand (FrFresh (PreCompute PreRight) PreY) true) /\
  FinSet.mem (pair_encoding pre_test_block_encoding pre_test_value_encoding) (PreLeft, PreY)
    (frg_unsafe_seeds (pre_kill_frg true)) = true.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition pre_entry_self_loop : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft; PreToRight]
       | PreLeft => [PreLeftJoin]
       | PreRight => [PreRightJoin]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreToRight | PreExit => PreEntry
       | PreLeftJoin => PreLeft
       | PreRightJoin => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft => PreEntry
       | PreToRight | PreExit => PreLeft
       | PreLeftJoin => PreRight
       | PreRightJoin => PreJoin
       end |}.

(** The entry self-loop violates the supported no-incoming-entry domain. *)
Example pre_entry_self_loop_rejected :
  ~ pre_expr_ssa_laws unit_encoding
    (pre_flow_expression pre_entry_self_loop (fun _ => false)).
Proof.
  intro Hlaw; apply (pre_expr_entry_no_incoming unit_encoding _ Hlaw PreEntry PreToLeft).
  - left; reflexivity.
  - cbn; tauto.
  - reflexivity.
Qed.

Definition pre_loop_blocks : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft]
       | PreLeft => [PreToRight; PreLeftJoin]
       | PreRight => [PreRightJoin]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreExit => PreEntry
       | PreToRight | PreLeftJoin => PreLeft
       | PreRightJoin => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreToRight | PreExit => PreLeft
       | PreLeftJoin => PreRight
       | PreRightJoin => PreJoin
       end |}.

Definition pre_loop_occurs (e : pre_test_edge) : bool :=
  match e with
  | PreCompute PreEntry | PreCompute PreLeft => true
  | _ => false
  end.

Example pre_loop_blocks_wf : graph_wf pre_loop_blocks.
Proof.
  constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
Qed.

Example pre_loop_blocks_ready : ready pre_test_block_encoding pre_loop_blocks
    (prepare pre_test_block_encoding pre_loop_blocks).
Proof.
  apply prepare_ready; [exact pre_loop_blocks_wf|intro b; destruct b; pre_test_distinct].
Qed.

Example pre_loop_points_ready : ready pre_test_point_encoding (pre_flow_points pre_loop_blocks)
    (prepare pre_test_point_encoding (pre_flow_points pre_loop_blocks)).
Proof.
  apply prepare_ready.
  - apply pre_flow_points_wf; [exact pre_loop_blocks_wf|reflexivity].
  - exact (points_out_nodup (pre_flow_points_laws pre_loop_blocks pre_loop_blocks_wf eq_refl
      ltac:(intro b; destruct b; pre_test_distinct))).
Qed.

(** The loop fixture satisfies every graph, point, SSA and expression law. *)
Example pre_loop_expression_laws :
  pre_expr_ssa_laws unit_encoding (pre_flow_expression pre_loop_blocks pre_loop_occurs).
Proof.
  apply pre_flow_laws.
  - exact pre_loop_blocks_wf.
  - reflexivity.
  - reflexivity.
  - intro b; destruct b; pre_test_distinct.
  - intro b; apply (reachable_dfs pre_test_block_encoding pre_loop_blocks _ b
      pre_loop_blocks_ready); destruct b; vm_compute; reflexivity.
  - intros [b stage]; apply (reachable_dfs pre_test_point_encoding
      (pre_flow_points pre_loop_blocks) _ (b, stage) pre_loop_points_ready);
      destruct b, stage; vm_compute; reflexivity.
  - intros be Hbe; destruct be; discriminate.
  - intro b; reflexivity.
  - intro be; reflexivity.
Qed.

Definition pre_loop_frg := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding unit_encoding unit_encoding
  (pre_flow_expression pre_loop_blocks pre_loop_occurs).

(** The backedge closes a finite phi link rather than creating an unrolled version. *)
Example pre_loop_cyclic_link :
  FinSet.mem (pair_encoding pre_test_block_encoding unit_encoding) (PreLeft, tt)
    (frg_phi_index pre_loop_frg) = true /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding unit_encoding)
      pre_test_block_edge_encoding) ((PreLeft, tt), PreToRight)
    (frg_phi_operands pre_loop_frg) = Some (FrgOperand (FrPhi PreLeft tt) true) /\
  Map.get pre_test_edge_encoding (PreCompute PreLeft) (frg_occurrence_index pre_loop_frg) =
    Some (FrPhi PreLeft tt) /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreLeft) (frg_fresh_index pre_loop_frg) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition pre_irreducible_blocks : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft; PreToRight]
       | PreLeft => [PreLeftJoin]
       | PreRight => [PreRightJoin; PreExit]
       | PreJoin => []
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreToRight => PreEntry
       | PreLeftJoin => PreLeft
       | PreRightJoin | PreExit => PreRight
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreRightJoin => PreLeft
       | PreToRight | PreLeftJoin => PreRight
       | PreExit => PreJoin
       end |}.

Example pre_irreducible_blocks_wf : graph_wf pre_irreducible_blocks.
Proof.
  constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
Qed.

Example pre_irreducible_blocks_ready : ready pre_test_block_encoding pre_irreducible_blocks
    (prepare pre_test_block_encoding pre_irreducible_blocks).
Proof.
  apply prepare_ready; [exact pre_irreducible_blocks_wf|intro b; destruct b; pre_test_distinct].
Qed.

Example pre_irreducible_points_ready :
  ready pre_test_point_encoding (pre_flow_points pre_irreducible_blocks)
    (prepare pre_test_point_encoding (pre_flow_points pre_irreducible_blocks)).
Proof.
  apply prepare_ready.
  - apply pre_flow_points_wf; [exact pre_irreducible_blocks_wf|reflexivity].
  - exact (points_out_nodup (pre_flow_points_laws pre_irreducible_blocks
      pre_irreducible_blocks_wf eq_refl ltac:(intro b; destruct b; pre_test_distinct))).
Qed.

Example pre_irreducible_expression_laws :
  pre_expr_ssa_laws unit_encoding (pre_flow_expression pre_irreducible_blocks pre_loop_occurs).
Proof.
  apply pre_flow_laws.
  - exact pre_irreducible_blocks_wf.
  - reflexivity.
  - reflexivity.
  - intro b; destruct b; pre_test_distinct.
  - intro b; apply (reachable_dfs pre_test_block_encoding pre_irreducible_blocks _ b
      pre_irreducible_blocks_ready); destruct b; vm_compute; reflexivity.
  - intros [b stage]; apply (reachable_dfs pre_test_point_encoding
      (pre_flow_points pre_irreducible_blocks) _ (b, stage) pre_irreducible_points_ready);
      destruct b, stage; vm_compute; reflexivity.
  - intros be Hbe; destruct be; discriminate.
  - intro b; reflexivity.
  - intro be; reflexivity.
Qed.

Definition pre_irreducible_frg := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding unit_encoding unit_encoding
  (pre_flow_expression pre_irreducible_blocks pre_loop_occurs).

(** Two entries into the cycle retain distinct expression phis without unrolling it. *)
Example pre_irreducible_phi_sites :
  FinSet.mem (pair_encoding pre_test_block_encoding unit_encoding) (PreLeft, tt)
    (frg_phi_index pre_irreducible_frg) = true /\
  FinSet.mem (pair_encoding pre_test_block_encoding unit_encoding) (PreRight, tt)
    (frg_phi_index pre_irreducible_frg) = true /\
  Map.get pre_test_edge_encoding (PreCompute PreLeft) (frg_occurrence_index pre_irreducible_frg) =
    Some (FrPhi PreLeft tt).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example pre_test_points_ready : ready pre_test_point_encoding pre_test_points
    (prepare pre_test_point_encoding pre_test_points).
Proof.
  apply prepare_ready; [exact pre_test_points_wf|].
  intro n; pre_test_cases; pre_test_distinct.
Qed.

Example pre_test_blocks_ready : ready pre_test_block_encoding pre_test_blocks
    (prepare pre_test_block_encoding pre_test_blocks).
Proof.
  apply prepare_ready; [exact pre_test_blocks_wf|].
  intro b; destruct b; pre_test_distinct.
Qed.

(** Every listed point of this diamond is reachable from its unique entry. *)
Example pre_test_reachable : forall n, reachable pre_test_points n.
Proof.
  intro n; apply (reachable_dfs pre_test_point_encoding pre_test_points _ n
    pre_test_points_ready); pre_test_cases; vm_compute; reflexivity.
Qed.

Local Lemma pre_test_uses_dominate : forall n x, point_use_at pre_test_model n x ->
  dominates_b pre_test_point_encoding
    (dominator_tree (prepare pre_test_point_encoding pre_test_points))
    (pre_test_definition x) n = true /\ pre_test_definition x <> n.
Proof.
  intros n x [Hexit|[e [Hedge Huse]]]; [contradiction|].
  pre_test_cases; cbn in Hedge, Huse; try (exfalso; intuition congruence).
  all: (vm_compute; split; [reflexivity|discriminate]).
Qed.

(** Branch expressions and the join expression use strictly dominating parameter definitions. *)
Example pre_test_strict : reachable_point_ssa pre_test_ssa.
Proof.
  constructor.
  - exists (PreEntry, PreBefore); reflexivity.
  - intros n x Hreachable Huse; exists (pre_test_definition x); split; [reflexivity|].
    split; [apply pre_test_reachable|].
    destruct (pre_test_uses_dominate n x Huse) as [Hdominates Hne]; split; [|exact Hne].
    apply (proj1 (proj1 (dominator_tree_exact pre_test_point_encoding pre_test_points _
      pre_test_points_ready (dominator_exact_true _ _ _ pre_test_points_ready))
      _ n Hreachable)); exact Hdominates.
  - intros n e x Hn He Hdef; pre_test_cases; cbn in *; intuition congruence.
  - intros x d e Hdef Hd He; destruct x; cbn in Hdef; inversion Hdef; subst d;
      pre_test_cases; cbn in *; intuition congruence.
Qed.

(** The expression diamond inhabits the full adopted ANA-16 domain. *)
Example pre_test_expression_laws :
  pre_expr_ssa_laws pre_test_value_encoding pre_test_expression.
Proof.
  constructor.
  - exact pre_test_points_laws.
  - exact pre_test_strict.
  - reflexivity.
  - reflexivity.
  - intros b Hb; apply (reachable_dfs pre_test_block_encoding pre_test_blocks _ b
      pre_test_blocks_ready); destruct b; vm_compute; reflexivity.
  - intros n Hn; apply pre_test_reachable.
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intro b; destruct b; pre_test_distinct.
  - pre_test_distinct.
  - intros e u Hcomputed; destruct u; cbn; tauto.
  - intros u Hinitial; discriminate.
  - intros u Hfamily x Hx; pre_test_cases; cbn in *; intuition congruence.
  - intros u v Hu Hv Hshape Hoperands; cbn in Hoperands; congruence.
  - intros u v Hu Hv Hshape; reflexivity.
  - intros s u; reflexivity.
  - intros u env1 env2 Hagree; cbn; rewrite (Hagree u); [reflexivity|left; reflexivity].
  - intros e u He Hu Hkill; exists u; split; [left; reflexivity|].
    pre_test_cases; cbn in *; intuition congruence.
  - intros e x He Hdef; pre_test_cases; cbn in *; intuition congruence.
  - intros e be He Hproject; pre_test_cases; cbn in *; intuition congruence.
  - intros e u Hcomputed; destruct e as [b|b|b|be]; try discriminate.
    all: destruct b; cbn in Hcomputed; try discriminate.
    all: (split; [reflexivity|intros block Hfalse; discriminate]).
  - intros be u Hbe Hu; exists (pre_test_translate be u); reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v Hu Hbe Htranslate; pre_test_cases; cbn in *; intuition congruence.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be u v env Hbe Hu Htranslate; destruct be, u;
      cbn in Htranslate; inversion Htranslate; subst v; reflexivity.
Qed.

(** Left and right phi edges substitute different predecessor expression instances. *)
Example pre_test_edge_translation :
  pre_phi_translate pre_test_expression PreLeftJoin PreZ = Some PreX /\
  pre_phi_translate pre_test_expression PreRightJoin PreZ = Some PreY.
Proof.
  split; reflexivity.
Qed.

(** A local expression substitution evaluates the selected incoming operand. *)
Example pre_test_translation_evaluation : forall env,
  pre_expr_eval pre_test_expression PreZ
    (pre_phi_env pre_test_value_encoding pre_test_expression PreLeftJoin env) =
  pre_expr_eval pre_test_expression PreX env.
Proof.
  intro env; reflexivity.
Qed.

(** The finite memo table retains all three operand-distinct expression instances. *)
Example pre_test_discovery :
  pre_expr_universe pre_test_block_edge_encoding pre_test_value_encoding
    pre_test_value_encoding pre_test_expression = [PreY; PreX; PreZ].
Proof.
  vm_compute; reflexivity.
Qed.

(** The adopted definition seeds for the join expression are entry and join only. *)
Example pre_test_join_definitions :
  frg_defs pre_test_block_encoding pre_test_value_encoding pre_test_expression PreZ =
    [PreJoin; PreEntry].
Proof.
  vm_compute; reflexivity.
Qed.

(** Each incoming expression has a frontier phi at the merge. *)
Example pre_test_incoming_phis :
  FinSet.mem pre_test_block_encoding PreJoin
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_expression PreX) = true /\
  FinSet.mem pre_test_block_encoding PreJoin
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_expression PreY) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The target parameter directly seeds its own expression phi at the join. *)
Example pre_test_join_phi_present :
  FinSet.mem pre_test_block_encoding PreJoin
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_expression PreZ) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The direct parameter rule derives the join phi independently of producer choice. *)
Example pre_test_join_phi_needed :
  frg_phi_needed pre_test_block_encoding pre_test_value_encoding
      pre_test_expression PreZ PreJoin.
Proof.
  eapply frg_phi_operand_param with (x := PreZ).
  - apply pre_family_seed; cbn; tauto.
  - cbn; tauto.
  - cbn; intuition discriminate.
  - left; reflexivity.
  - left; reflexivity.
Qed.

(** An operand absent from a block's parameters cannot satisfy the direct seed premise. *)
Example pre_test_direct_nonmember :
  ~ exists x, In x (pre_operands pre_test_expression PreX) /\
    In x (block_params pre_test_ssa PreJoin).
Proof.
  intros [x [Hoperand Hparam]]; destruct x; cbn in *; intuition discriminate.
Qed.

(** Entry parameters do not create expression phis at the unavailable entry sentinel. *)
Example pre_test_entry_phi_absent : forall u,
  FinSet.mem pre_test_block_encoding PreEntry
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_expression u) = false.
Proof.
  intro u; destruct u; vm_compute; reflexivity.
Qed.

Definition pre_test_boundary_blocks : Graph.t pre_test_block pre_test_block_edge :=
  Graph.Make [PreEntry] [PreEntry; PreLeft; PreRight] (fun _ => [])
    (Graph.source pre_test_blocks) (Graph.target pre_test_blocks).

Definition pre_test_boundary_ssa : ssa_points pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value :=
  SsaPoints pre_test_model pre_test_boundary_blocks (points_in_block pre_test_ssa)
    (instruction_edges pre_test_ssa) (parameter_edge pre_test_ssa)
    (block_of_point pre_test_ssa) (block_edge_of pre_test_ssa)
    (block_params pre_test_ssa) (block_edge_args pre_test_ssa) (point_definition pre_test_ssa).

Definition pre_test_boundary_expression : pre_expr_ssa unit unit pre_test_block
    pre_test_block_edge (pre_test_block * pre_test_stage) pre_test_edge
    pre_test_value unit nat pre_test_value :=
  PreExprSsa pre_test_boundary_ssa (pre_ssa_view pre_test_expression)
    (pre_expression pre_test_expression) (pre_seed_expressions pre_test_expression)
    (pre_value_universe pre_test_expression) (pre_expression_shape pre_test_expression)
    (pre_operands pre_test_expression) (pre_expr_eval pre_test_expression)
    (pre_phi_translate pre_test_expression) (pre_initial_available pre_test_expression)
    (pre_exit_point pre_test_expression).

(** The raw boundary fixture excludes its parameter-bearing join from direct seeding. *)
Example pre_test_unlisted_parameter_phi_absent :
  FinSet.mem pre_test_block_encoding PreJoin
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_boundary_expression PreZ) = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** Listed nonentry blocks without a matching parameter also receive no direct seed. *)
Example pre_test_listed_nonmember_phi_absent :
  FinSet.mem pre_test_block_encoding PreLeft
    (frg_phi_sites pre_test_block_encoding pre_test_block_edge_encoding pre_test_value_encoding
      pre_test_value_encoding pre_test_boundary_expression PreX) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition pre_test_frg := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
  pre_test_expression.

(** The materialized graph includes the join parameter's directly seeded expression phi. *)
Example pre_test_frg_join_phi :
  FinSet.mem (pair_encoding pre_test_block_encoding pre_test_value_encoding)
    (PreJoin, PreZ) (frg_phi_index pre_test_frg) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Each join operand links to the real definition for its own translated expression. *)
Example pre_test_frg_join_arguments :
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreZ), PreLeftJoin)
    (frg_phi_operands pre_test_frg) =
      Some (FrgOperand (FrFresh (PreCompute PreLeft) PreX) true) /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_test_value_encoding)
      pre_test_block_edge_encoding) ((PreJoin, PreZ), PreRightJoin)
    (frg_phi_operands pre_test_frg) =
      Some (FrgOperand (FrFresh (PreCompute PreRight) PreY) true).
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The join occurrence reuses the phi while the two branch occurrences define fresh versions. *)
Example pre_test_frg_occurrences :
  Map.get pre_test_edge_encoding (PreCompute PreJoin) (frg_occurrence_index pre_test_frg) =
    Some (FrPhi PreJoin PreZ) /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreLeft) (frg_fresh_index pre_test_frg) = true /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreRight) (frg_fresh_index pre_test_frg) = true /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreJoin) (frg_fresh_index pre_test_frg) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** An absent entry computation remains an unavailable sentinel and has no initial definition. *)
Example pre_test_frg_unavailable_entry :
  FinSet.mem (frg_version_encoding pre_test_block_encoding pre_test_edge_encoding
      pre_test_value_encoding) (FrUnavailable PreZ)
    (FinSet.of_list (frg_version_encoding pre_test_block_encoding pre_test_edge_encoding
      pre_test_value_encoding) (frg_versions pre_test_frg)) = true /\
  FinSet.mem (frg_version_encoding pre_test_block_encoding pre_test_edge_encoding
      pre_test_value_encoding) (FrInitial PreZ)
    (FinSet.of_list (frg_version_encoding pre_test_block_encoding pre_test_edge_encoding
      pre_test_value_encoding) (frg_versions pre_test_frg)) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A second identical instruction in one block reuses the first real definition. *)
Example pre_test_sequential_reuse :
  Map.get pre_test_edge_encoding (PreAgain PreLeft) (frg_occurrence_index pre_test_frg) =
    Some (FrFresh (PreCompute PreLeft) PreX) /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreLeft) (frg_fresh_index pre_test_frg) = true /\
  FinSet.mem pre_test_edge_encoding (PreAgain PreLeft) (frg_fresh_index pre_test_frg) = false /\
  Map.get pre_test_edge_encoding (PreAgain PreJoin) (frg_occurrence_index pre_test_frg) =
    Some (FrPhi PreJoin PreZ).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition pre_test_invalid_universe : pre_expr_ssa unit unit pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_test_value unit nat pre_test_value :=
  PreExprSsa (pre_ssa_points pre_test_expression) (pre_ssa_view pre_test_expression)
    (pre_expression pre_test_expression) (pre_seed_expressions pre_test_expression) [PreX; PreY]
    (pre_expression_shape pre_test_expression) (pre_operands pre_test_expression)
    (pre_expr_eval pre_test_expression) (pre_phi_translate pre_test_expression)
    (pre_initial_available pre_test_expression) (pre_exit_point pre_test_expression).

(** Omitting a seeded operand from the finite value universe violates the family laws. *)
Example pre_test_invalid_universe_rejected :
  ~ pre_expr_ssa_laws pre_test_value_encoding pre_test_invalid_universe.
Proof.
  intro Hlaw.
  assert (Hfamily : pre_expr_in_family pre_test_invalid_universe PreZ).
  { apply pre_family_seed; cbn; tauto. }
  pose proof (pre_expr_finite_operands pre_test_value_encoding pre_test_invalid_universe Hlaw
    PreZ Hfamily PreZ (or_introl eq_refl)) as Hbound.
  cbn in Hbound; intuition discriminate.
Qed.

(** * Ordered two-operand expressions and simultaneous parameter exchange *)

Inductive pre_pair_value : Type :=
  | PreA
  | PreB
  | PreC
  | PreD.

Definition pre_pair_value_encoding : encoding pre_pair_value.
Proof.
  refine (Encoding _ (fun x => match x with
    | PreA => 1%positive
    | PreB => 2%positive
    | PreC => 3%positive
    | PreD => 4%positive
    end) _).
  intros [] [] Heq; cbn in Heq; congruence.
Defined.

Definition pre_pair_expression_encoding := pair_encoding pre_pair_value_encoding
  pre_pair_value_encoding.

Definition pre_pair_blocks : Graph.t pre_test_block pre_test_block_edge :=
  {| Graph.entries := [PreEntry];
     Graph.nodes := [PreEntry; PreLeft; PreRight; PreJoin];
     Graph.out := fun b => match b with
       | PreEntry => [PreToLeft]
       | PreLeft => [PreToRight]
       | PreRight => [PreLeftJoin]
       | PreJoin => [PreRightJoin]
       end;
     Graph.source := fun be => match be with
       | PreToLeft | PreExit => PreEntry
       | PreToRight => PreLeft
       | PreLeftJoin => PreRight
       | PreRightJoin => PreJoin
       end;
     Graph.target := fun be => match be with
       | PreToLeft | PreExit => PreLeft
       | PreToRight => PreRight
       | PreLeftJoin | PreRightJoin => PreJoin
       end |}.

Definition pre_pair_parameters b : list pre_pair_value :=
  match b with
  | PreEntry => [PreA; PreB]
  | PreJoin => [PreC; PreD]
  | _ => []
  end.

Definition pre_pair_arguments be : list pre_pair_value :=
  match be with
  | PreLeftJoin => [PreA; PreB]
  | PreRightJoin => [PreD; PreC]
  | _ => []
  end.

Definition pre_pair_definition x : pre_test_block * pre_test_stage :=
  match x with
  | PreA | PreB => (PreEntry, PreBefore)
  | PreC | PreD => (PreJoin, PreBefore)
  end.

Definition pre_pair_view_definition x : definition pre_test_block pre_pair_value unit :=
  match x with
  | PreA => Param PreEntry 0
  | PreB => Param PreEntry 1
  | PreC => Param PreJoin 0
  | PreD => Param PreJoin 1
  end.

Definition pre_pair_occurs e : option (pre_pair_value * pre_pair_value) :=
  match e with
  | PreCompute PreEntry => Some (PreA, PreB)
  | PreAgain PreEntry => Some (PreB, PreA)
  | PreCompute PreJoin => Some (PreC, PreD)
  | PreAgain PreJoin => Some (PreD, PreC)
  | _ => None
  end.

Definition pre_pair_operands (u : pre_pair_value * pre_pair_value) := [fst u; snd u].

Definition pre_pair_use e : list pre_pair_value :=
  match pre_pair_occurs e with
  | Some u => pre_pair_operands u
  | None => []
  end.

Definition pre_pair_model := pre_operand_model pre_pair_blocks pre_pair_parameters
  pre_pair_arguments
  (fun _ => []) pre_pair_use.

Definition pre_pair_points := pre_operand_points pre_pair_blocks pre_pair_parameters
  pre_pair_arguments
  (fun _ => []) pre_pair_use (fun x => Some (pre_pair_definition x)).

Definition pre_pair_eval (u : pre_pair_value * pre_pair_value) (env : pre_pair_value -> option nat)
  :=
  match env (fst u), env (snd u) with
  | Some x, Some y => Some (10 * x + y)
  | _, _ => None
  end.

Definition pre_pair_translate be (u : pre_pair_value * pre_pair_value) := Some
  (pre_operand_rename pre_pair_value_encoding pre_pair_blocks pre_pair_parameters pre_pair_arguments
    be (fst u),
   pre_operand_rename pre_pair_value_encoding pre_pair_blocks pre_pair_parameters pre_pair_arguments
     be (snd u)).

Definition pre_pair_expression : pre_expr_ssa unit unit pre_test_block pre_test_block_edge
    (pre_test_block * pre_test_stage) pre_test_edge pre_pair_value unit nat
    (pre_pair_value * pre_pair_value) :=
  {| pre_ssa_points := pre_pair_points;
     pre_ssa_view := SsaView
       (GraphView pre_pair_blocks (fun _ => PreEntry) (fun _ _ _ _ => False) (fun _ _ _ => False))
       pre_pair_view_definition (fun x => fst (pre_pair_definition x)) pre_pair_parameters
         pre_pair_arguments
       (fun _ => []) (fun _ _ => Some 0) (fun _ _ => Some 0) (fun _ => false);
     pre_expression := PreExpressionView
       (GenKillView (GraphView (pre_flow_points pre_pair_blocks) (fun _ => (PreEntry, PreBefore))
         (fun _ _ _ _ => False) (fun _ _ _ => False))
         (fun e => match pre_pair_occurs e with
           | Some u => [u]
           | None => []
           end)
         (fun e u => existsb (fun x => existsb (fun y =>
           Pos.eqb (encode pre_pair_value_encoding x) (encode pre_pair_value_encoding y))
           (edge_def pre_pair_model e)) (pre_pair_operands u)) (fun _ _ => Some 0))
       (fun _ => true) pre_pair_occurs;
     pre_seed_expressions := [(PreA, PreB); (PreB, PreA); (PreC, PreD); (PreD, PreC)];
     pre_value_universe := [PreA; PreB; PreC; PreD];
     pre_expression_shape := fun _ => 1%positive;
     pre_operands := pre_pair_operands;
     pre_expr_eval := pre_pair_eval;
     pre_phi_translate := pre_pair_translate;
     pre_initial_available := fun _ => false;
     pre_exit_point := fun _ => false |}.

Example pre_pair_blocks_wf : graph_wf pre_pair_blocks.
Proof.
  constructor.
  - pre_test_distinct.
  - intros b Hb; destruct b; cbn in *; tauto.
  - intros b be Hbe; pre_test_cases; cbn in *; intuition congruence.
  - intros b be Hb Hbe; pre_test_cases; cbn in *; intuition congruence.
Qed.

Example pre_pair_blocks_ready : ready pre_test_block_encoding pre_pair_blocks
    (prepare pre_test_block_encoding pre_pair_blocks).
Proof.
  apply prepare_ready; [exact pre_pair_blocks_wf|intro b; destruct b; pre_test_distinct].
Qed.

Example pre_pair_points_ready : ready pre_test_point_encoding (pre_flow_points pre_pair_blocks)
    (prepare pre_test_point_encoding (pre_flow_points pre_pair_blocks)).
Proof.
  apply prepare_ready.
  - apply pre_flow_points_wf; [exact pre_pair_blocks_wf|reflexivity].
  - exact (points_out_nodup (pre_flow_points_laws pre_pair_blocks pre_pair_blocks_wf eq_refl
      ltac:(intro b; destruct b; pre_test_distinct))).
Qed.

Example pre_pair_reachable : forall n, reachable (pre_flow_points pre_pair_blocks) n.
Proof.
  intros [b stage]; apply (reachable_dfs pre_test_point_encoding _ _ (b, stage)
    pre_pair_points_ready); destruct b, stage; vm_compute; reflexivity.
Qed.

Local Lemma pre_pair_uses_dominate : forall n x, point_use_at pre_pair_model n x ->
  dominates_b pre_test_point_encoding
    (dominator_tree (prepare pre_test_point_encoding (pre_flow_points pre_pair_blocks)))
    (pre_pair_definition x) n = true /\ pre_pair_definition x <> n.
Proof.
  intros n x [Hexit|[e [Hedge Huse]]]; [contradiction|].
  destruct e as [b|b|b|be]; [cbn in Huse; contradiction|destruct b|destruct b|destruct be];
    cbn in Huse; try contradiction.
  all: destruct Huse as [Heq|[Heq|Hfalse]]; try contradiction; subst x.
  all: destruct n as [b stage]; destruct b, stage; cbn in Hedge;
    try (exfalso; intuition congruence).
  all: vm_compute; split; [reflexivity|discriminate].
Qed.

Example pre_pair_strict : reachable_point_ssa pre_pair_points.
Proof.
  apply pre_operand_strict.
  - exact pre_pair_points_ready.
  - exact pre_pair_reachable.
  - exact pre_pair_uses_dominate.
  - intros n e x He Hdef; destruct e as [b|b|b|be]; cbn in Hdef; try contradiction.
    destruct b; cbn in Hdef; try contradiction.
    all: destruct Hdef as [Heq|[Heq|Hfalse]]; try contradiction; subst x.
    all: pre_test_cases; cbn in *; intuition congruence.
  - intros x e He; destruct x; pre_test_cases; cbn in *; intuition congruence.
Qed.

(** The ordered-pair fixture satisfies the complete reachable, finite-expression SSA domain. *)
Example pre_pair_expression_laws : pre_expr_ssa_laws pre_pair_value_encoding pre_pair_expression.
Proof.
  constructor.
  - apply pre_operand_points_laws.
    + exact pre_pair_blocks_wf.
    + reflexivity.
    + intro b; destruct b; pre_test_distinct.
    + intros be Hbe; destruct be; reflexivity.
  - exact pre_pair_strict.
  - reflexivity.
  - reflexivity.
  - intros b Hb; apply (reachable_dfs pre_test_block_encoding _ _ b pre_pair_blocks_ready);
      destruct b; vm_compute; reflexivity.
  - intros n Hn; exact (pre_pair_reachable n).
  - exists PreEntry, (PreEntry, PreBefore); repeat split; reflexivity.
  - intros b be Hb Hbe; cbn in Hb; destruct Hb as [Heq|Hfalse];
      [subst b; destruct be; discriminate|contradiction].
  - intro b; destruct b; pre_test_distinct.
  - pre_test_distinct.
  - intros e u Hcomputed; destruct e as [b|b|b|be]; cbn in Hcomputed; try discriminate;
      destruct b; cbn in Hcomputed; try discriminate;
      inversion Hcomputed; subst u; cbn; tauto.
  - intros u Hfalse; discriminate.
  - intros [x y] Hfamily z Hz; cbn in Hz; destruct Hz as [Heq|[Heq|Hfalse]];
      [subst z; destruct x; cbn; tauto|subst z; destruct y; cbn; tauto|contradiction].
  - intros [x y] [z w] Hfamily Hfamily' Hshape Hoperands; cbn in Hoperands;
      inversion Hoperands; reflexivity.
  - intros [x y] [z w] Hfamily Hfamily' Hshape; reflexivity.
  - intros s [x y]; reflexivity.
  - intros [x y] env1 env2 Hagree.
    change (pre_pair_eval (x, y) env1 = pre_pair_eval (x, y) env2).
    unfold pre_pair_eval; cbn [fst snd].
      rewrite (Hagree x (or_introl eq_refl)), (Hagree y (or_intror (or_introl eq_refl)));
        reflexivity.
  - intros e u He Hu Hkill; apply existsb_exists in Hkill; destruct Hkill as [x [Hx Hdefined]].
    exists x; split; [exact Hx|exact (pre_operand_member pre_pair_value_encoding x _ Hdefined)].
  - intros e x He Hdef; destruct e as [b|b|b|be]; cbn in Hdef; try contradiction.
    destruct b; cbn in Hdef; try contradiction.
    all: destruct Hdef as [Heq|[Heq|Hfalse]]; try contradiction; subst x; reflexivity.
  - intros e be He Hproject; destruct e; cbn in Hproject; try discriminate; reflexivity.
  - intros e u Hcomputed; destruct e as [b|b|b|be]; cbn in Hcomputed; try discriminate.
    all: split; [reflexivity|intros block Hfalse; discriminate].
  - intros be u Hbe Hu; eexists; reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be [x y] v Hu Hbe Htranslate; cbn in Htranslate; inversion Htranslate; subst v;
    reflexivity.
  - intros be u v Hu Htranslate; reflexivity.
  - intros be [x y] v env Hbe Hu Htranslate; cbn in Htranslate; inversion Htranslate; subst v;
    reflexivity.
Qed.

Definition pre_pair_frg := build_frg pre_test_block_encoding pre_test_block_edge_encoding
  pre_test_point_encoding pre_test_edge_encoding pre_pair_value_encoding
    pre_pair_expression_encoding
  pre_pair_expression.

(** Exchanging two parameters reads the same original environment for both operands. *)
Example pre_pair_simultaneous_exchange :
  pre_phi_translate pre_pair_expression PreRightJoin (PreC, PreD) = Some (PreD, PreC) /\
  pre_operands pre_pair_expression (PreD, PreC) = [PreD; PreC] /\
  pre_expr_eval pre_pair_expression (PreC, PreD)
    (pre_phi_env pre_pair_value_encoding pre_pair_expression PreRightJoin
      (fun x => Some (match x with
        | PreC => 3
        | PreD => 7
        | _ => 0
        end))) = Some 73 /\
  pre_expr_eval pre_pair_expression (PreD, PreC)
    (fun x => Some (match x with
      | PreC => 3
      | PreD => 7
      | _ => 0
      end)) = Some 73.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The backedge exchanges the two phi versions while the incoming edge reads its real version. *)
Example pre_pair_cyclic_versions :
  FinSet.mem (pair_encoding pre_test_block_encoding pre_pair_expression_encoding)
    (PreJoin, (PreC, PreD)) (frg_phi_index pre_pair_frg) = true /\
  FinSet.mem (pair_encoding pre_test_block_encoding pre_pair_expression_encoding)
    (PreJoin, (PreD, PreC)) (frg_phi_index pre_pair_frg) = true /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_pair_expression_encoding)
      pre_test_block_edge_encoding) ((PreJoin, (PreC, PreD)), PreLeftJoin)
    (frg_phi_operands pre_pair_frg) = Some (FrgOperand (FrFresh (PreCompute PreEntry) (PreA, PreB))
      true) /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_pair_expression_encoding)
      pre_test_block_edge_encoding) ((PreJoin, (PreC, PreD)), PreRightJoin)
    (frg_phi_operands pre_pair_frg) = Some (FrgOperand (FrPhi PreJoin (PreD, PreC)) true) /\
  Map.get (pair_encoding (pair_encoding pre_test_block_encoding pre_pair_expression_encoding)
      pre_test_block_edge_encoding) ((PreJoin, (PreD, PreC)), PreRightJoin)
    (frg_phi_operands pre_pair_frg) = Some (FrgOperand (FrPhi PreJoin (PreC, PreD)) true) /\
  FinSet.mem pre_test_edge_encoding (PreCompute PreJoin) (frg_fresh_index pre_pair_frg) = false /\
  length (frg_versions pre_pair_frg) = 8.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example pre_pair_frg_wf : frg_wf pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_pair_value_encoding
      pre_pair_expression_encoding
    pre_pair_expression pre_pair_frg.
Proof.
  apply build_frg_wf; [exact pre_pair_expression_laws|exact pre_pair_blocks_ready|exact
    pre_pair_points_ready].
Qed.

(** The computed diamond instantiates every producer obligation. *)
Example pre_test_frg_wf : frg_wf pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    pre_test_expression pre_test_frg.
Proof.
  apply build_frg_wf; [exact pre_test_expression_laws|exact pre_test_blocks_ready|exact
    pre_test_points_ready].
Qed.

Example pre_parallel_frg_wf : forall two, frg_wf pre_test_block_encoding
  pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    (pre_parallel_expression two) (pre_parallel_frg two).
Proof.
  intro two; apply build_frg_wf; [apply pre_parallel_expression_laws|
    apply pre_parallel_blocks_ready|apply pre_parallel_points_ready].
Qed.

Example pre_kill_frg_wf : forall cyclic, frg_wf pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding pre_test_value_encoding pre_test_value_encoding
    (pre_kill_expression cyclic) (pre_kill_frg cyclic).
Proof.
  intro cyclic; apply build_frg_wf; [apply pre_kill_expression_laws|
    apply pre_kill_blocks_ready|apply pre_kill_points_ready].
Qed.

Example pre_loop_frg_wf : frg_wf pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding unit_encoding unit_encoding
    (pre_flow_expression pre_loop_blocks pre_loop_occurs) pre_loop_frg.
Proof.
  apply build_frg_wf; [exact pre_loop_expression_laws|exact pre_loop_blocks_ready|exact
    pre_loop_points_ready].
Qed.

Example pre_irreducible_frg_wf : frg_wf pre_test_block_encoding pre_test_block_edge_encoding
    pre_test_point_encoding pre_test_edge_encoding unit_encoding unit_encoding
    (pre_flow_expression pre_irreducible_blocks pre_loop_occurs) pre_irreducible_frg.
Proof.
  apply build_frg_wf; [exact pre_irreducible_expression_laws|
    exact pre_irreducible_blocks_ready|exact pre_irreducible_points_ready].
Qed.

(** Alteration setup considers only the deduplicated expressions incident to edge definitions. *)
Definition pre_pair_alter_family := [(PreC, PreC); (PreC, PreD); (PreA, PreB)].

Definition pre_pair_alter_operands := AnalysesSsaPreGraph.pre_rename_operand_index
  pre_pair_value_encoding pre_pair_expression_encoding pre_pair_expression pre_pair_alter_family.

Definition pre_pair_alter_candidates e := AnalysesSsaPreGraph.pre_rename_alter_candidates
  pre_pair_value_encoding pre_pair_expression_encoding pre_pair_expression pre_pair_alter_operands
    e.

(** An edge without definitions has no alteration candidates and invokes no kill filter element. *)
Example pre_pair_alter_no_definitions : pre_pair_alter_candidates (PreCompute PreEntry) = [].
Proof.
  vm_compute; reflexivity.
Qed.

(** Repeated operands and overlapping definition incidences still yield each candidate once. *)
Example pre_pair_alter_deduplicated :
  length (pre_pair_alter_candidates (PreBind PreJoin)) = 2 /\
  FinSet.mem pre_pair_expression_encoding (PreC, PreC)
    (FinSet.of_list pre_pair_expression_encoding
      (pre_pair_alter_candidates (PreBind PreJoin))) = true /\
  FinSet.mem pre_pair_expression_encoding (PreC, PreD)
    (FinSet.of_list pre_pair_expression_encoding
      (pre_pair_alter_candidates (PreBind PreJoin))) = true /\
  FinSet.mem pre_pair_expression_encoding (PreA, PreB)
    (FinSet.of_list pre_pair_expression_encoding
      (pre_pair_alter_candidates (PreBind PreJoin))) = false.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
