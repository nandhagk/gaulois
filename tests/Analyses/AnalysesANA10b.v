(** * Ordered memory graph fixtures

    Finite fixtures distinguish effect positions, parallel edges and entry-backedge operands.
    For example, write/read and read/write edges arrive at one phi with different definitions.
    Builds on: AnalysesMemoryGraph, ViewsMemoryEffects and GraphCore. *)

From Stdlib Require Import List.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph.
Import List.ListNotations.

Definition parallel_cfg : Graph.t bool bool :=
  {| Graph.entries := [false];
     Graph.nodes := [false; true];
     Graph.out := fun n => if n then [] else [false; true];
     Graph.source := fun _ => false;
     Graph.target := fun _ => true |}.

Definition parallel_effects (e : bool) : list (memory_effect unit) :=
  if e then [MemoryWrite MemoryAll; MemoryRead MemoryAll]
  else [MemoryRead MemoryAll; MemoryWrite MemoryAll].

Definition parallel_output (e : bool) : memory_version bool bool :=
  if e then MemoryDef true 0 else MemoryDef false 1.

Definition parallel_memory : memory_graph bool bool :=
  {| memory_phis := [true];
     memory_versions := [MemoryLive; MemoryPhi true; MemoryDef false 1; MemoryDef true 0];
     memory_in := fun n => if n then MemoryPhi true else MemoryLive;
     memory_before := fun e i =>
       match i with
       | 0 => Some MemoryLive
       | 1 => Some (if e then MemoryDef true 0 else MemoryLive)
       | _ => None
       end;
     memory_out := parallel_output;
     memory_operand := fun n k =>
       if n then
         match k with
         | None => None
         | Some e => Some (parallel_output e)
         end
       else None |}.

Example read_then_write_incoming :
  (memory_before parallel_memory false 0, memory_before parallel_memory false 1,
    memory_out parallel_memory false) =
  (Some MemoryLive, Some MemoryLive, MemoryDef false 1).
Proof.
  reflexivity.
Qed.

Example write_then_read_incoming :
  (memory_before parallel_memory true 0, memory_before parallel_memory true 1,
    memory_out parallel_memory true) =
  (Some MemoryLive, Some (MemoryDef true 0), MemoryDef true 0).
Proof.
  reflexivity.
Qed.

Example parallel_phi_operands :
  (memory_operand parallel_memory true (Some false),
    memory_operand parallel_memory true (Some true)) =
  (Some (MemoryDef false 1), Some (MemoryDef true 0)).
Proof.
  reflexivity.
Qed.

Example occurrence_out_of_range : memory_before parallel_memory false 2 = None.
Proof.
  reflexivity.
Qed.

Example barrier_all_memory :
  (effect_reads (MemoryBarrier : memory_effect unit),
    effect_writes (MemoryBarrier : memory_effect unit),
    effect_is_def (MemoryBarrier : memory_effect unit)) = (MemoryAll, MemoryAll, true).
Proof.
  reflexivity.
Qed.

Example unknown_call_defines_memory :
  (effect_reads (MemoryCall MemoryAll MemoryAll : memory_effect unit),
    effect_writes (MemoryCall MemoryAll MemoryAll : memory_effect unit),
    effect_is_def (MemoryCall MemoryAll MemoryAll : memory_effect unit)) =
  (MemoryAll, MemoryAll, true).
Proof.
  reflexivity.
Qed.

Lemma parallel_cfg_wf : graph_wf parallel_cfg.
Proof.
  constructor.
  - constructor; [cbn; intuition discriminate|].
    constructor; [cbn; tauto|constructor].
  - intros n [Hentry|Hentry]; [subst n; cbn; auto|contradiction].
  - intros n e Hedge; destruct n; cbn in Hedge; [contradiction|reflexivity].
  - intros n e Hnode Hedge; destruct n; cbn in Hedge; [contradiction|].
    cbn; auto.
Qed.

Lemma parallel_reachable (n : bool) : reachable parallel_cfg n.
Proof.
  destruct n.
  - apply (@reachable_step bool bool parallel_cfg false).
    + constructor; cbn; auto.
    + cbn; auto.
  - constructor; cbn; auto.
Qed.

Lemma parallel_valid_definition e i :
  memory_valid_version parallel_cfg parallel_effects parallel_memory (MemoryDef e i) <->
  (e = false /\ i = 1) \/ (e = true /\ i = 0).
Proof.
  unfold memory_valid_version, memory_occurrence.
  destruct e; destruct i as [|[|i]]; cbn [parallel_effects effect_is_def];
    split; intro Hvalid.
  - right; auto.
  - exists (MemoryWrite MemoryAll); split; [|reflexivity].
    split; [cbn; auto|split; [apply parallel_reachable|reflexivity]].
  - destruct Hvalid as [a [[Hedge [Hreach Hnth]] Hdef]].
    injection Hnth as Heffect; subst a; discriminate Hdef.
  - destruct Hvalid as [[Heq Hindex]|[Heq Hindex]]; discriminate.
  - destruct Hvalid as [a [[Hedge [Hreach Hnth]] Hdef]].
    destruct i; discriminate Hnth.
  - destruct Hvalid as [[Heq Hindex]|[Heq Hindex]]; discriminate.
  - destruct Hvalid as [a [[Hedge [Hreach Hnth]] Hdef]].
    injection Hnth as Heffect; subst a; discriminate Hdef.
  - destruct Hvalid as [[Heq Hindex]|[Heq Hindex]]; discriminate.
  - left; auto.
  - exists (MemoryWrite MemoryAll); split; [|reflexivity].
    split; [cbn; auto|split; [apply parallel_reachable|reflexivity]].
  - destruct Hvalid as [a [[Hedge [Hreach Hnth]] Hdef]].
    destruct i; discriminate Hnth.
  - destruct Hvalid as [[Heq Hindex]|[Heq Hindex]]; discriminate.
Qed.

Lemma parallel_before_domain e i :
  (exists v, memory_before parallel_memory e i = Some v) <->
  exists a, memory_occurrence parallel_cfg parallel_effects e i a.
Proof.
  destruct i as [|[|i]]; split.
  - intros Hbefore; exists (if e then MemoryWrite MemoryAll else MemoryRead MemoryAll).
    split; [destruct e; cbn; auto|split; [apply parallel_reachable|destruct e; reflexivity]].
  - intros Hocc; exists MemoryLive; reflexivity.
  - intros Hbefore; exists (if e then MemoryRead MemoryAll else MemoryWrite MemoryAll).
    split; [destruct e; cbn; auto|split; [apply parallel_reachable|destruct e; reflexivity]].
  - intros Hocc; exists (if e then MemoryDef true 0 else MemoryLive); reflexivity.
  - intros [v Hbefore]; discriminate.
  - intros [a [Hedge [Hreach Hnth]]]; destruct e; cbn in Hnth;
      destruct i; discriminate Hnth.
Qed.

Lemma parallel_operand_domain n k :
  (exists v, memory_operand parallel_memory n k = Some v) <->
  memory_phi_at parallel_memory n /\
  match k with
  | None => In n (Graph.entries parallel_cfg)
  | Some e => In e (Graph.out parallel_cfg (Graph.source parallel_cfg e)) /\
      reachable parallel_cfg (Graph.source parallel_cfg e) /\ Graph.target parallel_cfg e = n
  end.
Proof.
  destruct n; destruct k as [e|]; split.
  - intro Hdomain; split; [cbn; auto|].
    split; [destruct e; cbn; auto|split; [apply parallel_reachable|reflexivity]].
  - intro Hdomain; exists (parallel_output e); reflexivity.
  - intros [v Hdomain]; discriminate.
  - intros [Hphi Hentry]; cbn in Hentry; intuition discriminate.
  - intros [v Hdomain]; discriminate.
  - intros [Hphi Hincoming]; cbn in Hphi; intuition discriminate.
  - intros [v Hdomain]; discriminate.
  - intros [Hphi Hentry]; cbn in Hphi; intuition discriminate.
Qed.

(** Two parallel edges carrying different definitions satisfy every local graph law. *)
Example parallel_memory_wf : memory_graph_wf parallel_cfg parallel_effects parallel_memory.
Proof.
  constructor.
  - exact parallel_cfg_wf.
  - constructor; [cbn; tauto|constructor].
  - intros n Hphi; apply parallel_reachable.
  - cbn; constructor; [cbn; intuition discriminate|].
    constructor; [cbn; intuition discriminate|].
    constructor; [cbn; intuition discriminate|].
    constructor; [cbn; tauto|constructor].
  - intros [|n|e i].
    + cbn; tauto.
    + destruct n.
      * split; intro Hvalid.
        -- split; [apply parallel_reachable|cbn; auto].
        -- cbn; auto.
      * cbn [memory_valid_version memory_phi_at parallel_memory]; cbn; intuition congruence.
    + rewrite parallel_valid_definition; cbn; intuition congruence.
  - intros n [Hentry|Hentry]; [subst n|contradiction].
    right; split; [cbn; intuition discriminate|reflexivity].
  - intros e Hedge Hreach; destruct e; cbn [parallel_effects parallel_output parallel_memory].
    + constructor; [reflexivity|constructor; [reflexivity|constructor]].
    + constructor; [reflexivity|constructor; [reflexivity|constructor]].
  - intros e Hedge Hreach; left; split; [cbn; auto|split; reflexivity].
  - intros n Hreach; destruct n; cbn; [split; [apply parallel_reachable|cbn; auto]|exact I].
  - intros e Hedge Hreach; destruct e; apply parallel_valid_definition; auto.
  - exact parallel_before_domain.
  - exact parallel_operand_domain.
Qed.

Definition backedge_cfg : Graph.t unit unit :=
  {| Graph.entries := [tt];
     Graph.nodes := [tt];
     Graph.out := fun _ => [tt];
     Graph.source := fun _ => tt;
     Graph.target := fun _ => tt |}.

Definition backedge_effects (_ : unit) : list (memory_effect unit) :=
  [MemoryReadWrite MemoryAll MemoryAll].

Definition backedge_memory : memory_graph unit unit :=
  {| memory_phis := [tt];
     memory_versions := [MemoryLive; MemoryPhi tt; MemoryDef tt 0];
     memory_in := fun _ => MemoryPhi tt;
     memory_before := fun _ i => match i with 0 => Some (MemoryPhi tt) | _ => None end;
     memory_out := fun _ => MemoryDef tt 0;
     memory_operand := fun _ k =>
       match k with
       | None => Some MemoryLive
       | Some _ => Some (MemoryDef tt 0)
       end |}.

Example entry_backedge_operands :
  (memory_operand backedge_memory tt None, memory_operand backedge_memory tt (Some tt),
    memory_before backedge_memory tt 0,
    memory_after tt 0 (MemoryReadWrite MemoryAll MemoryAll : memory_effect unit)
      (MemoryPhi tt : memory_version unit unit)) =
  (Some MemoryLive, Some (MemoryDef tt 0), Some (MemoryPhi tt), MemoryDef tt 0).
Proof.
  reflexivity.
Qed.

Example repeated_path_last_definition :
  (memory_last_path backedge_effects [] : memory_version unit unit,
    memory_last_path backedge_effects [tt; tt] : memory_version unit unit) =
  (MemoryLive, MemoryDef tt 0).
Proof.
  reflexivity.
Qed.

Lemma backedge_reachable : reachable backedge_cfg tt.
Proof.
  constructor; cbn; auto.
Qed.

Lemma backedge_valid_definition i :
  memory_valid_version backedge_cfg backedge_effects backedge_memory (MemoryDef tt i) <->
  i = 0.
Proof.
  destruct i as [|i].
  - split; [reflexivity|intro Hindex].
    exists (MemoryReadWrite MemoryAll MemoryAll); split; [|reflexivity].
    split; [cbn; auto|split; [exact backedge_reachable|reflexivity]].
  - split; [|discriminate].
    intros [a [Hocc Hdef]]; destruct Hocc as [Hedge [Hreach Hnth]].
    cbn in Hnth; destruct i; discriminate Hnth.
Qed.

(** An entry phi merges its virtual live operand with an actual self-edge definition. *)
Example backedge_memory_wf : memory_graph_wf backedge_cfg backedge_effects backedge_memory.
Proof.
  constructor.
  - constructor.
    + constructor; [cbn; tauto|constructor].
    + intros [] Hentry; cbn; auto.
    + intros [] [] Hedge; reflexivity.
    + intros [] [] Hnode Hedge; cbn; auto.
  - constructor; [cbn; tauto|constructor].
  - intros [] Hphi; exact backedge_reachable.
  - cbn; constructor; [cbn; intuition discriminate|].
    constructor; [cbn; intuition discriminate|constructor; [cbn; tauto|constructor]].
  - intros [|[]|[] i].
    + cbn; tauto.
    + split; intro Hvalid; [split; [exact backedge_reachable|cbn; auto]|cbn; auto].
    + rewrite backedge_valid_definition; cbn; intuition congruence.
  - intros [] Hentry; left; split; [cbn; auto|split; reflexivity].
  - intros [] Hedge Hreach; constructor; [reflexivity|constructor].
  - intros [] Hedge Hreach; left; split; [cbn; auto|split; reflexivity].
  - intros [] Hreach; split; [exact backedge_reachable|cbn; auto].
  - intros [] Hedge Hreach; apply backedge_valid_definition; reflexivity.
  - intros [] [|i]; split.
    + intros Hbefore; exists (MemoryReadWrite MemoryAll MemoryAll).
      split; [cbn; auto|split; [exact backedge_reachable|reflexivity]].
    + intros Hocc; exists (MemoryPhi tt); reflexivity.
    + intros [v Hbefore]; discriminate.
    + intros [a [Hedge [Hreach Hnth]]]; cbn in Hnth;
        destruct i; discriminate Hnth.
  - intros [] [[]|]; split; intro Hdomain.
    + split; [cbn; auto|split; [cbn; auto|split; [exact backedge_reachable|reflexivity]]].
    + exists (MemoryDef tt 0); reflexivity.
    + split; cbn; auto.
    + exists MemoryLive; reflexivity.
Qed.

(** Repeated visits retain the exact history in the universal occurrence theorem. *)
Example backedge_occurrence_history : exists input origin,
  memory_provenance backedge_cfg backedge_effects backedge_memory tt [tt; tt] tt
    (MemoryPhi tt) (MemoryDef tt 0) /\
  memory_occurrence_history backedge_cfg backedge_effects backedge_memory [tt; tt] tt 0
    input origin.
Proof.
  apply (memory_definition_before_occurrence _ _ _ backedge_memory_wf tt [tt; tt] tt 0
    (MemoryReadWrite MemoryAll MemoryAll)).
  - cbn; auto.
  - apply (@path_cons unit unit backedge_cfg tt [tt] tt); [cbn; auto|].
    apply (@path_cons unit unit backedge_cfg tt [] tt); [cbn; auto|constructor].
  - split; [cbn; auto|split; [exact backedge_reachable|reflexivity]].
Qed.

Definition empty_effect_cfg : Graph.t unit Empty_set :=
  {| Graph.entries := [tt];
     Graph.nodes := [tt];
     Graph.out := fun _ => [];
     Graph.source := fun (e : Empty_set) => match e with end;
     Graph.target := fun (e : Empty_set) => match e with end |}.

Definition empty_effects (e : Empty_set) : list (memory_effect unit) := match e with end.

Definition empty_memory : memory_graph unit Empty_set :=
  {| memory_phis := [];
     memory_versions := [MemoryLive];
     memory_in := fun _ => MemoryLive;
     memory_before := fun (e : Empty_set) _ => match e with end;
     memory_out := fun (e : Empty_set) => match e with end;
     memory_operand := fun _ _ => None |}.

Example empty_effect_graph_retains_live :
  (memory_versions empty_memory, memory_in empty_memory tt) = ([MemoryLive], MemoryLive).
Proof.
  reflexivity.
Qed.

(** Live-on-entry remains a valid inventoried version when the graph has no effects or edges. *)
Example empty_memory_wf : memory_graph_wf empty_effect_cfg empty_effects empty_memory.
Proof.
  constructor.
  - constructor.
    + constructor; [cbn; tauto|constructor].
    + intros [] Hentry; cbn; auto.
    + intros n [] Hedge.
    + intros n [] Hnode Hedge.
  - constructor.
  - intros n Hphi; contradiction.
  - constructor; [cbn; tauto|constructor].
  - intros [|[]|[] i].
    + cbn; tauto.
    + split.
      * intros [Hequal|Hfalse]; [discriminate|contradiction].
      * intros [Hreach Hphi]; exfalso; exact Hphi.
  - intros [] Hentry; right; split; [cbn; tauto|reflexivity].
  - intros [] Hedge Hreach.
  - intros [] Hedge Hreach.
  - intros [] Hreach; exact I.
  - intros [] Hedge Hreach.
  - intros [] i.
  - intros [] [[]|]; cbn; split.
    + intros [v Hoperand]; discriminate.
    + intros [Hphi Hentry]; contradiction.
Qed.
