(** * Demand and aggressive dead-code regression cases

    These examples distinguish strict propagation, nonmonotone closure and erasure policies.
    For example, Boolean N3 propagation discovers a three-variable chain from one exit demand.
    Builds on: AnalysesDemand, AnalysesAdce and ViewsSemantics. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderBasic OrderPointwise.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointCheck.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement ViewsEffects.
From Gaulois.Analyses Require Import AnalysesDemand AnalysesAdce.
Import List.ListNotations.

Definition computed_needed {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) : finite_map EX (dvars dv) bool :=
  match demand_worklist_run EX dv 128%positive with
  | Some result => lookup unit_encoding (demand_lattice EX bool_demand dv) result tt
  | None => bot (demand_lattice EX bool_demand dv)
  end.

Lemma computed_needed_exact {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) : demand_worklist_run EX dv 128%positive <> None ->
  needed_values EX dv = computed_needed EX dv.
Proof.
  intro Hfinished; unfold computed_needed.
  destruct (demand_worklist_run EX dv 128%positive) as [result|] eqn:Hrun; [|contradiction].
  exact (needed_values_from_run EX dv _ result Hrun).
Qed.

Definition demand_loop : Graph.t unit unit :=
  {| Graph.nodes := [tt];
     Graph.entries := [tt];
     Graph.out := fun _ => [tt];
     Graph.source := fun _ => tt;
     Graph.target := fun _ => tt |}.

Definition demand_loop_view : graph_view unit unit unit unit :=
  {| cfg := demand_loop;
     point := fun _ => tt;
     taken := fun _ _ _ _ => True;
     stays := fun _ _ _ => False |}.

Definition strict_chain : demand_view unit unit unit unit nat unit bool :=
  {| dgraph := demand_loop_view;
     ddefs := fun _ => [0; 1; 2];
     dnec := fun _ => [];
     dback := fun _ x (needed : bool) => if needed then
       match x with
       | 0 => [(1, true)]
       | 1 => [(2, true)]
       | _ => []
       end else [];
     dexit := fun _ => [(0, true)];
     dlookup := fun _ _ => tt;
     dvars := [0; 1; 2; 3] |}.

Example strict_n3_chain :
  map (dget nat_encoding bool_lattice (needed_values nat_encoding strict_chain)) [0; 1; 2; 3] =
  [true; true; true; false].
Proof.
  rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Example strict_n3_least : forall d, demand_closed nat_encoding bool_demand strict_chain d ->
  leb (demand_lattice nat_encoding bool_demand strict_chain)
    (needed_values nat_encoding strict_chain) d = true.
Proof.
  intros d Hclosed; apply needed_values_least; [intros [] x; reflexivity|exact Hclosed].
Qed.

Example strict_n3_checker_accepts :
  check_post (demand_lattice nat_encoding bool_demand strict_chain)
    (demand_system nat_encoding bool_demand strict_chain)
    (fun _ => computed_needed nat_encoding strict_chain) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example observable_payload_kept : dead_value nat_encoding
  (observable_bits_view strict_chain (fun _ => [(3, true)])) 3 = false.
Proof.
  unfold dead_value; rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Definition nonmonotone : demand_view unit unit unit unit nat unit bool :=
  {| dgraph := demand_loop_view;
     ddefs := fun _ => [0; 1];
     dnec := fun _ => [];
     dback := fun _ x (needed : bool) => if needed then [] else
       match x with
       | 0 => [(1, true)]
       | _ => [(0, true)]
       end;
     dexit := fun _ => [];
     dlookup := fun _ _ => tt;
     dvars := [0; 1] |}.

Example nonmonotone_closure_result :
  map (dget nat_encoding bool_lattice (needed_values nat_encoding nonmonotone)) [0; 1] =
  [true; true].
Proof.
  rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Example nonmonotone_still_closed : demand_closed nat_encoding bool_demand nonmonotone
  (needed_values nat_encoding nonmonotone).
Proof.
  apply needed_values_closed.
Qed.

Definition duplicate_raw_graph : Graph.t unit unit :=
  {| Graph.nodes := [tt; tt];
     Graph.entries := [];
     Graph.out := fun _ => [tt; tt];
     Graph.source := fun _ => tt;
     Graph.target := fun _ => tt |}.

Definition duplicate_raw_view : demand_view unit unit unit unit nat unit bool :=
  {| dgraph := {| cfg := duplicate_raw_graph;
       point := fun _ => tt;
       taken := fun _ _ _ _ => False;
       stays := fun _ _ _ => False |};
     ddefs := ddefs strict_chain;
     dnec := dnec strict_chain;
     dback := dback strict_chain;
     dexit := dexit strict_chain;
     dlookup := dlookup strict_chain;
     dvars := [0; 1; 0; 2; 1; 3] |}.

Example duplicate_raw_n3_chain :
  map (dget nat_encoding bool_lattice (needed_values nat_encoding duplicate_raw_view))
    [0; 1; 2; 3] = [true; true; true; false].
Proof.
  rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Example duplicate_raw_closed : demand_closed nat_encoding bool_demand duplicate_raw_view
  (needed_values nat_encoding duplicate_raw_view).
Proof.
  apply needed_values_closed.
Qed.

Definition empty_cfg : Graph.t nat (nat * nat) :=
  {| Graph.nodes := [];
     Graph.entries := [];
     Graph.out := fun _ => [];
     Graph.source := fst;
     Graph.target := snd |}.

Definition empty_view : demand_view unit unit nat (nat * nat) nat unit bool :=
  {| dgraph := {| cfg := empty_cfg;
       point := fun _ => 0;
       taken := fun _ _ _ _ => False;
       stays := fun _ _ _ => False |};
     ddefs := fun _ => [];
     dnec := fun _ => [(0, true)];
     dback := fun _ _ _ => [];
     dexit := fun _ => [(0, true)];
     dlookup := fun _ _ => tt;
     dvars := [0] |}.

Example empty_demand_is_dead : dead_value nat_encoding empty_view 0 = true.
Proof.
  unfold dead_value; rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Definition forced_view : demand_view unit unit unit unit nat unit bool :=
  {| dgraph := demand_loop_view;
     ddefs := fun _ => [];
     dnec := fun _ => [(0, true)];
     dback := fun _ _ _ => [];
     dexit := fun _ => [];
     dlookup := fun _ _ => tt;
     dvars := [0] |}.

Example effectful_operand_needed : dead_value nat_encoding forced_view 0 = false.
Proof.
  unfold dead_value; rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Definition diamond : Graph.t nat (nat * nat) :=
  {| Graph.nodes := [0; 1; 2; 3];
     Graph.entries := [0];
     Graph.out := fun n => match n with
       | 0 => [(0, 1); (0, 2)]
       | 1 => [(1, 3)]
       | 2 => [(2, 3)]
       | _ => []
       end;
     Graph.source := fst;
     Graph.target := snd |}.

Definition diamond_adce : adce_input nat (nat * nat) :=
  {| agraph := diamond;
     aexits := [3];
     effectful_node := fun n => Nat.eqb n 1 || Nat.eqb n 2;
     may_not_terminate := fun _ => false |}.

Example two_marked_successors_keep_branch :
  map (fun n => FinSet.mem nat_encoding n (adce_marked nat_encoding diamond_adce)) [0; 1; 2; 3] =
  [true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_adce : adce_input nat (nat * nat) :=
  {| agraph := empty_cfg;
     aexits := [];
     effectful_node := fun _ => true;
     may_not_terminate := fun _ => true |}.

Example empty_graph_ignores_outside_effects :
  FinSet.is_empty (adce_marked nat_encoding empty_adce) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition diverging_adce : adce_input unit unit :=
  {| agraph := demand_loop;
     aexits := [tt];
     effectful_node := fun _ => false;
     may_not_terminate := fun _ => true |}.

Example possibly_diverging_loop_kept : FinSet.mem unit_encoding tt
  (adce_marked unit_encoding diverging_adce) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition pure_effects : effects unit :=
  {| reads := fun _ => false;
     writes := fun _ => false;
     may_trap := fun _ => false;
     may_diverge := fun _ => false;
     may_stop := fun _ => false;
     allocates := fun _ => false;
     frees := fun _ => false;
     calls := fun _ => false;
     observes := fun _ => false |}.

Definition trap_effects : effects unit :=
  {| reads := fun _ => false;
     writes := fun _ => false;
     may_trap := fun _ => true;
     may_diverge := fun _ => false;
     may_stop := fun _ => false;
     allocates := fun _ => false;
     frees := fun _ => false;
     calls := fun _ => false;
     observes := fun _ => false |}.

Example trap_policies_differ : effectful trap_effects KeepTraps tt = true /\
  effectful trap_effects DropUnreadTraps tt = false.
Proof.
  vm_compute; auto.
Qed.

(** * A constant assignment erased to a no-op *)

Definition erase_state := (bool * bool)%type.

Definition source : semantics erase_state unit :=
  {| initial := fun s => fst s = false;
     step := fun s l s' => fst s = false /\ l = [] /\ s' = (true, true) |}.

Definition target : semantics erase_state unit :=
  {| initial := fun s => fst s = false;
     step := fun s l s' => fst s = false /\ l = [] /\ s' = (true, snd s) |}.

Definition erase_endings : endings erase_state :=
  {| final := fun s => fst s = true;
     trapped := fun _ => False;
     stopped := fun _ => False |}.

Definition erase_cfg : Graph.t bool unit :=
  {| Graph.nodes := [false; true];
     Graph.entries := [false];
     Graph.out := fun p => if p then [] else [tt];
     Graph.source := fun _ => false;
     Graph.target := fun _ => true |}.

Definition erase_graph : graph_view erase_state unit bool unit :=
  {| cfg := erase_cfg;
     point := fst;
     taken := fun _ _ _ _ => True;
     stays := fun _ _ _ => False |}.

Definition erase_demand : demand_view erase_state unit bool unit unit bool bool :=
  {| dgraph := erase_graph;
     ddefs := fun _ => [tt];
     dnec := fun _ => [];
     dback := fun _ _ _ => [];
     dexit := fun _ => [];
     dlookup := fun s _ => snd s;
     dvars := [tt] |}.

Definition erased_constant : erasure erase_state unit bool unit unit bool unit :=
  {| er_demand := erase_demand;
     er_graph := erase_graph;
     er_erased := fun _ => true;
     er_instr := fun _ => Some tt |}.

Definition erase_effects_view : effects_view erase_state unit unit :=
  {| instr_at := fun _ => Some tt;
     heap := fun _ => tt;
     heap_agree := eq;
     depth := fun _ => 0 |}.

Definition erase_fact := needed_values unit_encoding erase_demand.

Example erased_constant_is_dead : dget unit_encoding bool_lattice erase_fact tt = false.
Proof.
  unfold erase_fact; rewrite computed_needed_exact by (vm_compute; discriminate).
  vm_compute; reflexivity.
Qed.

Lemma erase_graph_wf : graph_wf erase_cfg.
Proof.
  constructor.
  - repeat constructor; cbn; intuition congruence.
  - intros p [Heq|Hfalse]; [subst p; now left|contradiction].
  - intros p [] Hedge; destruct p; cbn in Hedge; [contradiction|reflexivity].
  - intros p [] Hp Hedge; right; left; reflexivity.
Qed.

Lemma erase_source_view : graph_view_laws source erase_graph.
Proof.
  constructor.
  - exact erase_graph_wf.
  - intros s Hs; left; symmetry; exact Hs.
  - intros s l s' Hreach Hstep; right; exists tt; exact I.
  - intros s l s' [] Hreach [Hp [Hl Hs']] Htaken; subst s'; split.
    + cbn; rewrite Hp; now left.
    + reflexivity.
  - intros s l s' Hreach Hstep Hstay; contradiction.
Qed.

Lemma erase_target_view : graph_view_laws target erase_graph.
Proof.
  constructor.
  - exact erase_graph_wf.
  - intros s Hs; left; symmetry; exact Hs.
  - intros s l s' Hreach Hstep; right; exists tt; exact I.
  - intros s l s' [] Hreach [Hp [Hl Hs']] Htaken; subst s'; split.
    + cbn; rewrite Hp; now left.
    + reflexivity.
  - intros s l s' Hreach Hstep Hstay; contradiction.
Qed.

Lemma erase_demand_laws : demand_laws source erase_endings (reachable_state source)
  unit_encoding bool_demand erase_demand.
Proof.
  constructor.
  - exact erase_source_view.
  - intros s l s' Hstay; contradiction.
  - intros s l s' [] [] Hreach Hstep Htaken Hnot; exfalso; apply Hnot; now left.
  - split.
    + constructor.
      * intros d s [] Hneeded; reflexivity.
      * intros a b s t Hab Hagree [] Hneeded.
        apply Hagree; exact (proj1 (demand_bool_leb_iff unit_encoding _ a b) Hab tt Hneeded).
    + intros d s t Hagree [] Hneeded; symmetry; exact (Hagree tt Hneeded).
  - intros u v Hfalse; discriminate.
  - intros [] []; reflexivity.
  - split; [repeat constructor; cbn; tauto|].
    split; [intros [] [] m [] m' Hnamed; contradiction|].
    split; [intros n [] m Hnamed; contradiction|intros [] [] Hdef; now left].
  - intros s l s' t [] d Hs Ht Hp [Hpc [Hl Hs']] Htaken Hagree; subst s'.
    change (fst t = fst s) in Hp.
    exists (true, true); split.
    + split; [change (fst t = false); rewrite Hp; exact Hpc|auto].
    + split; [exact I|intros [] Hneeded; reflexivity].
  - intros s t Hs Ht Hp Hagree; change (fst t = fst s) in Hp; cbn; rewrite Hp; tauto.
Qed.

Lemma erase_pure_laws : effects_laws source erase_endings pure_effects erase_effects_view.
Proof.
  constructor.
  - intros s l s' [] Hreach Hinstr [Hp [Hl Hs']] Hobs; exact Hl.
  - intros s [] Hreach Hinstr Htrap; contradiction.
  - intros s [] Hreach Hinstr Hstop; contradiction.
  - intros s l s' [] Hreach Hinstr Hstep Hw Ha Hf; reflexivity.
  - intros s l s' t [] Hreach Hinstr Hstep Hreads Heq.
    change (s = t) in Heq; subst t; exists s'; split; [exact Hstep|reflexivity].
  - intros s t [] Hs Ht Hi Hj Hr Hagree; tauto.
  - intros s t [] Hs Ht Hi Hj Hr Hagree; tauto.
  - intros s l s' [] Hreach Hinstr Hstep Hcall; reflexivity.
  - intros s l s' [] Hreach Hinstr Hstep Hcall; discriminate.
Qed.

Lemma erased_constant_laws pol : erasure_laws pol source erase_endings target erase_endings
  unit_encoding erased_constant erase_fact.
Proof.
  constructor.
  - reflexivity.
  - exact erase_target_view.
  - intros s l s' Hstay; contradiction.
  - intros e s l s' t Hs Ht Hp Hstep Htaken Herased; discriminate.
  - intros e s t l t' Hs Ht Hp Hstep Htaken Herased; discriminate.
  - intros [] s l s' t Hs Ht Hp [Hpc [Hl Hs']] Htaken Herased.
    change (fst t = fst s) in Hp.
    exists (true, snd t); split.
    + split; [change (fst t = false); rewrite Hp; exact Hpc|auto].
    + split; [exact I|intros []; reflexivity].
  - intros [] s t l t' Hs Ht Hp [Hpc [Hl Ht']] Htaken Herased; subst t'.
    change (fst t = fst s) in Hp.
    split; [exact Hl|]; split; [intros []; reflexivity|].
    exists (true, true), []; split.
    + split; [change (fst s = false); rewrite <- Hp; exact Hpc|auto].
    + exact I.
  - intros s t k Hnot Hs Ht Hp Hagree; change (fst t = fst s) in Hp.
    destruct k; cbn; try tauto.
    + rewrite Hp; tauto.
Qed.

Lemma erased_constant_sound pol : dce_conclusion pol source erase_endings (false, false)
  target erase_endings (false, false).
Proof.
  eapply dce_sound with (inv := reachable_state source) (ef := pure_effects)
    (ev := erase_effects_view) (er := erased_constant) (d := erase_fact).
  - exact erase_demand_laws.
  - apply reachable_invariant.
  - apply needed_values_closed.
  - exact erase_pure_laws.
  - apply erased_constant_laws.
  - intros [] [] Herased Hdef; exact erased_constant_is_dead.
  - intros [] Herased; exists tt; split; [reflexivity|destruct pol; reflexivity].
  - intros s l s' [] Hreach Hstep Htaken; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros [] Hneeded; reflexivity.
Qed.

Example erased_assignment_keep_traps : same_behaviour source erase_endings (false, false)
  target erase_endings (false, false).
Proof.
  exact (erased_constant_sound KeepTraps).
Qed.

Example erased_assignment_drop_unread_traps : same_behaviour source erase_endings (false, false)
  target erase_endings (false, false).
Proof.
  apply (erased_constant_sound DropUnreadTraps); intros tr s Hrun Htrap; exact Htrap.
Qed.

Example erasure_changes_only_the_dead_value : step source (false, false) [] (true, true) /\
  step target (false, false) [] (true, false).
Proof.
  vm_compute; auto.
Qed.
