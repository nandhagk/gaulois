(** * Normal-return and five-component effect examples

    Computed queries distinguish recursive base cases, other endings and callback effects.
    For example, a callback footprint outside the finite universe requires an unknown summary.
    Builds on: AnalysesCallEffects, AnalysesInterprocedural and ViewsCalls. *)

From Stdlib Require Import List Bool Arith PArith ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderPowerset.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointWorklist.
From Gaulois.Views Require Import ViewsSemantics ViewsCalls ViewsSummary.
From Gaulois.Analyses Require Import AnalysesInterprocedural AnalysesCallEffects AnalysesLiveness.
Import List.ListNotations.

(** * Matched recursion and normal-return observations *)

Definition return_pairs : list (option unit * option unit) :=
  [(None, None); (Some tt, Some tt)].

Definition return_problem : ip_problem nat nat unit :=
  IpProblem (seq 0 8) [0; 1] [tt]
    [IpEdge 0 0 (IpCall 0) return_pairs;
     IpEdge 0 1 IpInternal ((None, Some tt) :: return_pairs);
     IpEdge 1 1 (IpReturn 0) return_pairs;
     IpEdge 2 2 IpInternal return_pairs;
     IpEdge 2 3 IpInternal return_pairs;
     IpEdge 2 4 IpInternal return_pairs;
     IpEdge 5 5 (IpCall 1) return_pairs;
     IpEdge 5 6 IpInternal return_pairs;
     IpEdge 6 6 (IpReturn 1) return_pairs;
     IpEdge 5 7 (IpReturn 0) return_pairs].

Lemma return_fact_listed d : IpTab.valid_fact return_problem d.
Proof.
  destruct d as [[] |]; cbn; auto.
Qed.

Example return_problem_wf : ip_problem_wf return_problem.
Proof.
  split; [apply seq_NoDup |]; split; [|split].
  - repeat constructor; cbn; intuition congruence.
  - repeat constructor; cbn; intuition congruence.
  - intros e He; cbn [return_problem ip_edges] in He.
    destruct He as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hbad]]]]]]]]]];
      try contradiction; cbn [ip_source ip_target ip_action ip_pairs return_problem ip_nodes
        ip_sites return_pairs seq In]; repeat split; auto 12.
    all: apply return_fact_listed.
Qed.

Definition return_rules start := IpTab.rules return_problem nat_encoding (start, None).
Definition return_encoding := IpTab.fact_encoding nat_encoding unit_encoding.

Definition return_map start :=
  match IpHorn.probe return_encoding (return_rules start) 2048 with
  | Some m => m
  | None => Map.empty
  end.

Example return_probe_base_completed :
  IpHorn.probe return_encoding (return_rules 0) 2048 = Some (return_map 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example return_probe_loop_completed :
  IpHorn.probe return_encoding (return_rules 2) 2048 = Some (return_map 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example return_probe_unknown_completed :
  IpHorn.probe return_encoding (return_rules 5) 2048 = Some (return_map 5).
Proof.
  vm_compute; reflexivity.
Qed.

Lemma return_engine_agrees start :
  IpHorn.probe return_encoding (return_rules start) 2048 = Some (return_map start) ->
  ifds_solve nat_encoding nat_encoding unit_encoding return_problem start None =
    fun n d => lookup return_encoding bool_lattice (return_map start) (inr (n, d)).
Proof.
  intro Hprobe; unfold ifds_solve; fold return_encoding; fold (return_rules start).
  rewrite (IpHorn.solve_probe _ _ _ _ Hprobe); reflexivity.
Qed.

Example self_recursion_base_returns_and_generates :
  (may_return nat_encoding nat_encoding unit_encoding return_problem 0 1 None,
    ifds_solve nat_encoding nat_encoding unit_encoding return_problem 0 None 1 (Some tt)) =
  (true, true).
Proof.
  unfold may_return; rewrite (return_engine_agrees 0 return_probe_base_completed).
  vm_compute; reflexivity.
Qed.

Example loop_has_no_normal_return_but_reaches_trap_and_stop :
  (may_return nat_encoding nat_encoding unit_encoding return_problem 2 1 None,
    ifds_solve nat_encoding nat_encoding unit_encoding return_problem 2 None 3 None,
    ifds_solve nat_encoding nat_encoding unit_encoding return_problem 2 None 4 None) =
  (false, true, true).
Proof.
  unfold may_return; rewrite (return_engine_agrees 2 return_probe_loop_completed).
  vm_compute; reflexivity.
Qed.

Example unknown_call_and_callback_return_but_mismatch_rejected :
  (may_return nat_encoding nat_encoding unit_encoding return_problem 5 6 None,
    may_return nat_encoding nat_encoding unit_encoding return_problem 5 7 None) = (true, false).
Proof.
  unfold may_return; rewrite (return_engine_agrees 5 return_probe_unknown_completed).
  vm_compute; reflexivity.
Qed.

Definition ordinary_entry : ip_problem nat nat unit := IpProblem [0] [] [tt] [].
Definition ordinary_rules := IpTab.rules ordinary_entry nat_encoding (0, Some tt).
Definition ordinary_map :=
  match IpHorn.probe return_encoding ordinary_rules 16 with
  | Some m => m
  | None => Map.empty
  end.

Example ordinary_probe_completed :
  IpHorn.probe return_encoding ordinary_rules 16 = Some ordinary_map.
Proof.
  vm_compute; reflexivity.
Qed.

Example return_query_includes_ordinary_fact_without_zero :
  (may_return nat_encoding nat_encoding unit_encoding ordinary_entry 0 0 (Some tt),
    ifds_solve nat_encoding nat_encoding unit_encoding ordinary_entry 0 (Some tt) 0 None) =
  (true, false).
Proof.
  unfold may_return, ifds_solve; fold ordinary_rules return_encoding.
  rewrite (IpHorn.solve_probe _ _ _ _ ordinary_probe_completed); vm_compute; reflexivity.
Qed.

Definition return_state := (nat * option unit * list nat)%type.

Definition return_semantics : semantics return_state unit :=
  Semantics (fun s => s = (2, None, []))
    (fun s l t => l = [] /\ exists e, ip_step return_problem s e t).

Definition return_view : return_projection return_state nat nat unit :=
  ReturnProjection (fun s => s) (fun s => Nat.eqb (fst (fst s)) 1 &&
    match snd s with
    | [] => true
    | _ :: _ => false
    end).

Lemma return_view_laws : return_projection_laws return_semantics return_problem return_view 1.
Proof.
  constructor.
  - intros s l t Hreachable [_ [e Hstep]].
    eapply ip_path_step; [exact Hstep | apply ip_path_refl].
  - intros [[n d] stack] Hnormal.
    apply andb_true_iff in Hnormal as [Hnode Hstack].
    apply Nat.eqb_eq in Hnode; cbn in Hnode; subst n.
    exists d, stack; reflexivity.
Qed.

Example ending_observations :
  map (normal_return return_view)
    [(1, None, []); (1, None, [0]); (3, None, []); (4, None, [])] =
    [true; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition return_ending (s : return_state) : option ending :=
  if normal_return return_view s then Some EndFinal else
    if Nat.eqb (fst (fst s)) 3 then Some EndTrap else
      if Nat.eqb (fst (fst s)) 4 then Some EndStop else None.

Example trap_and_resource_stop_retain_distinct_tags :
  map return_ending [(1, None, []); (3, None, []); (4, None, []); (2, None, [])] =
    [Some EndFinal; Some EndTrap; Some EndStop; None].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma loop_run_excludes_only_normal_return :
  forall tr t, exec return_semantics (2, None, []) tr t -> normal_return return_view t = false.
Proof.
  apply (may_return_sound return_semantics nat_encoding nat_encoding unit_encoding return_problem
    return_view 2 1 None (2, None, []) return_problem_wf).
  - cbn; auto.
  - exact I.
  - exact return_view_laws.
  - exists (2, None, []), []; split; [reflexivity | constructor].
  - reflexivity.
  - exact (f_equal (fun p => fst (fst p))
      loop_has_no_normal_return_but_reaches_trap_and_stop).
Qed.

(** * Footprints, flags and actual callback frames *)

Definition read_half : footprint nat := Footprint 7 0 2.
Definition write_half : footprint nat := Footprint 7 2 4.
Definition other_half : footprint nat := Footprint 7 4 6.
Definition callback_range : footprint nat := Footprint 99 (-4) 12.
Definition effect_universe := [read_half; write_half; other_half].
Definition effect_lattice := modref_lattice nat_encoding effect_universe.

Definition effect_set fs :=
  finite_clamp (footprint_encoding nat_encoding) effect_universe
    (FinSet.of_list (footprint_encoding nat_encoding) fs).

Definition read_effect : modref nat nat_encoding effect_universe :=
  ModRef (Some (effect_set [read_half])) (Some (effect_set [])) true false false.

Definition write_effect : modref nat nat_encoding effect_universe :=
  ModRef (Some (effect_set [])) (Some (effect_set [write_half])) false true true.

Definition finite_effect := join effect_lattice read_effect write_effect.

Definition effect_bits (a : modref nat nat_encoding effect_universe) : list bool :=
  [mr_contains (mr_reads a) read_half; mr_contains (mr_reads a) write_half;
   mr_contains (mr_writes a) read_half; mr_contains (mr_writes a) write_half;
   mr_contains (mr_reads a) other_half; mr_contains (mr_writes a) other_half;
   mr_allocates a; mr_frees a; mr_orders a].

Example partial_reads_writes_allocation_free_and_order :
  effect_bits finite_effect = [true; false; false; true; false; false; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example allocation_free_and_order_are_independent :
  let free_only : modref nat nat_encoding effect_universe :=
    ModRef (Some (effect_set [])) (Some (effect_set [])) false true false in
  let order_only : modref nat nat_encoding effect_universe :=
    ModRef (Some (effect_set [])) (Some (effect_set [])) false false true in
  [mr_allocates read_effect; mr_frees read_effect; mr_orders read_effect;
   mr_allocates write_effect; mr_frees write_effect; mr_orders write_effect;
   mr_frees free_only; mr_orders free_only; mr_frees order_only; mr_orders order_only;
   mr_frees (join effect_lattice free_only order_only);
   mr_orders (join effect_lattice free_only order_only)] =
  [true; false; false; false; true; true; true; false; false; true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example bottom_and_unknown :
  (effect_bits (bot effect_lattice), effect_bits (unknown_modref nat_encoding effect_universe),
    mr_contains (mr_reads (unknown_modref nat_encoding effect_universe)) callback_range,
    mr_contains (mr_writes (unknown_modref nat_encoding effect_universe)) callback_range) =
  (repeat false 9, repeat true 9, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_lattice_comparisons :
  [leb effect_lattice read_effect finite_effect; leb effect_lattice write_effect finite_effect;
   leb effect_lattice finite_effect read_effect;
   leb effect_lattice finite_effect (unknown_modref nat_encoding effect_universe);
   leb effect_lattice (unknown_modref nat_encoding effect_universe) finite_effect] =
  [true; true; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition effect_view : calls_view nat nat nat :=
  CallsView [0; 1; 2; 3] [0; 3]
    (fun f => if Nat.eqb f 0 then [0] else if Nat.eqb f 1 then [1] else [])
    (fun p => p)
    (fun s => match s with
      | 1 | 4 => 1
      | 2 | 3 => 2
      | 8 | 9 | 10 => 3
      | _ => 0
      end)
    (fun s => match s with
      | 1 | 4 => [(0, 0)]
      | 2 | 3 => [(1, 1); (0, 0)]
      | _ => []
      end).

Definition effect_resolver p := if Nat.eqb p 0 then [1] else if Nat.eqb p 1 then [2] else [].

Inductive effect_step : nat -> list unit -> nat -> Prop :=
  | effect_enter : effect_step 0 [] 1
  | effect_callback : effect_step 1 [] 2
  | effect_unknown : effect_step 2 [tt] 3
  | effect_callback_return : effect_step 3 [] 4
  | effect_return : effect_step 4 [] 5
  | effect_read_allocate : effect_step 8 [] 9
  | effect_write_free_order : effect_step 9 [] 10.

Definition effect_semantics : semantics nat unit :=
  Semantics (fun s => s = 0 \/ s = 8) effect_step.

Definition effect_observations : effect_observer nat unit nat :=
  EffectObserver
    (fun s _ _ => match s with
      | 2 => [callback_range]
      | 8 => [read_half]
      | _ => []
      end)
    (fun s _ _ => match s with
      | 2 => [callback_range]
      | 9 => [write_half]
      | _ => []
      end)
    (fun s _ _ => Nat.eqb s 2 || Nat.eqb s 8)
    (fun s _ _ => Nat.eqb s 2 || Nat.eqb s 9)
    (fun s _ _ => Nat.eqb s 2 || Nat.eqb s 9).

Definition local_effects f : modref nat nat_encoding effect_universe :=
  match f with
  | 2 => unknown_modref nat_encoding effect_universe
  | 3 => finite_effect
  | _ => bot effect_lattice
  end.

Definition effect_summaries f : modref nat nat_encoding effect_universe :=
  if Nat.eqb f 3 then finite_effect else unknown_modref nat_encoding effect_universe.

Definition observes_effects (a : modref nat nat_encoding effect_universe) s l t : bool :=
  forallb (mr_contains (mr_reads a)) (actual_reads effect_observations s l t) &&
  forallb (mr_contains (mr_writes a)) (actual_writes effect_observations s l t) &&
  implb (actual_allocates effect_observations s l t) (mr_allocates a) &&
  implb (actual_frees effect_observations s l t) (mr_frees a) &&
  implb (actual_orders effect_observations s l t) (mr_orders a).

Lemma observes_effects_covers a s l t :
  observes_effects a s l t = true -> modref_covers effect_observations a s l t.
Proof.
  unfold observes_effects; repeat rewrite andb_true_iff.
  intros [[[[Hr Hw] Ha] Hf] Ho]; repeat split.
  - intros f Hin; exact (proj1 (forallb_forall _ _) Hr f Hin).
  - intros f Hin; exact (proj1 (forallb_forall _ _) Hw f Hin).
  - intro Halloc; rewrite Halloc in Ha; exact Ha.
  - intro Hfree; rewrite Hfree in Hf; exact Hf.
  - intro Horder; rewrite Horder in Ho; exact Ho.
Qed.

Lemma effect_calls_laws : calls_view_laws effect_semantics effect_view effect_resolver.
Proof.
  constructor.
  - intros f p Hsite; unfold effect_view, sites_of in Hsite; cbn in Hsite.
    destruct (Nat.eqb f 0) eqn:Hroot.
    + apply Nat.eqb_eq in Hroot; subst f; destruct Hsite as [<- | []]; reflexivity.
    + destruct (Nat.eqb f 1) eqn:Hchild; [|contradiction].
      apply Nat.eqb_eq in Hchild; subst f; destruct Hsite as [<- | []]; reflexivity.
  - intros s [-> | ->]; cbn; auto.
  - intros s Hreachable f Hactive.
    do 11 (destruct s as [|s]; [cbn in *; tauto |]); cbn in *; tauto.
  - intros s l t Hreachable Hstep; destruct Hstep; cbn.
    + right; left; exists 0; cbn; auto.
    + right; left; exists 1; cbn; auto.
    + left; auto.
    + right; right; exists 1, 1; auto.
    + right; right; exists 0, 0; auto.
    + left; auto.
    + left; auto.
Qed.

Lemma effect_local_laws :
  modref_local_laws effect_semantics effect_view nat_encoding effect_universe
    effect_observations local_effects.
Proof.
  constructor; intros s l t Hreachable Hstep; apply observes_effects_covers.
  destruct Hstep; vm_compute; reflexivity.
Qed.

Lemma effect_post_solution :
  post_solution effect_lattice
    (summary_system effect_view effect_resolver
      (modref_spec nat_encoding effect_universe local_effects)) effect_summaries.
Proof.
  intros c Hrow; cbn [summary_system effect_view functions sites_of effect_resolver] in Hrow.
  destruct Hrow as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]].
  all: split; [vm_compute; reflexivity | cbn; intros a Ha; contradiction].
Qed.

Example callback_effects_cover_all_active_callers :
  map (fun f => observes_effects (effect_summaries f) 2 [tt] 3)
    (active effect_view 2) = [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_callback_effect_would_miss_every_observation :
  observes_effects (bot effect_lattice) 2 [tt] 3 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example finite_observations_and_partial_negative_controls :
  [observes_effects finite_effect 8 [] 9; observes_effects finite_effect 9 [] 10;
   observes_effects read_effect 9 [] 10; observes_effects write_effect 8 [] 9;
   observes_effects finite_effect 2 [tt] 3] = [true; true; false; false; false].
Proof.
  vm_compute; reflexivity.
Qed.

Lemma callback_semantic_summary_covers :
  forall f, In f (active effect_view 2) ->
    modref_covers effect_observations (effect_summaries f) 2 [tt] 3.
Proof.
  intros f Hactive; eapply (modref_sound effect_semantics effect_view effect_resolver
    nat_encoding effect_universe effect_observations local_effects effect_summaries).
  - exact effect_calls_laws.
  - exact effect_local_laws.
  - exact effect_post_solution.
  - exists 0, []; split; [left; reflexivity |].
    change (exec effect_semantics 0 ([] ++ ([] ++ [])) 2).
    eapply exec_step; [apply effect_enter |].
    eapply exec_step; [apply effect_callback | constructor].
  - apply effect_unknown.
  - exact Hactive.
Qed.
