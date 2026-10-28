(** * Dense views, histories and constructive endpoint examples

    These examples exercise dense queries, accepted cuts and silent ending matching.
    For example, a stuck source matches a target only after its administrative silent step.
    Builds on: ViewsSemantics, ViewsGraph, ViewsForward, ViewsAgreement and FixpointCut. *)

From Stdlib Require Import List Bool Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderConcrete.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointCut FixpointCycles.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsForward ViewsAgreement.
Import List.ListNotations.

(** * Dense generators and cut acceptance *)

Definition empty_graph : Graph.t unit unit := Graph.Make [] [] (fun _ => []) (fun _ => tt)
  (fun _ => tt).

Definition line_graph : Graph.t bool unit := Graph.Make [true] [true; false]
  (fun b => if b then [tt] else []) (fun _ => true) (fun _ => false).

Example empty_dense_systems :
  System.constraints (forward_system empty_graph (fun _ => false) (fun _ a => a)) = [] /\
  System.constraints (backward_system empty_graph (fun _ => false) (fun _ a => a)) = [] /\
  check_post bool_lattice (forward_system empty_graph (fun _ => false) (fun _ a => a))
    (fun _ => false) = true.
Proof.
  vm_compute; auto.
Qed.

Example dense_rows_and_codes :
  System.constraints (forward_system line_graph (fun _ => true) (fun _ a => a)) =
    [Seed true; Flow tt] /\
  System.constraints (backward_system line_graph (fun _ => true) (fun _ a => a)) =
    [Seed true; Seed false; Flow tt] /\
  encode (dense_constraint_encoding bool_encoding unit_encoding) (Seed true) =
    encode (sum_encoding bool_encoding unit_encoding) (inl true) /\
  encode (dense_constraint_encoding bool_encoding unit_encoding) (Flow tt) =
    encode (sum_encoding bool_encoding unit_encoding) (inr tt).
Proof.
  vm_compute; auto.
Qed.

Example forward_backward_read_opposite_endpoints :
  Query.run (System.rhs (forward_system line_graph (fun _ => false) (fun _ a => a)) (Flow tt))
    (fun b => b) = (true, [true], []) /\
  Query.run (System.rhs (backward_system line_graph (fun _ => false) (fun _ a => a)) (Flow tt))
    (fun b => b) = (false, [false], []) /\
  deps (forward_static line_graph (fun _ => false) (fun _ a => a)) (Flow tt) = [true] /\
  deps (backward_static line_graph (fun _ => false) (fun _ a => a)) (Flow tt) = [false].
Proof.
  vm_compute; auto.
Qed.

Example forward_checker_accepts_and_rejects :
  check_post bool_lattice (forward_system line_graph (fun _ => true) (fun _ a => a))
    (fun _ => true) = true /\
  check_post bool_lattice (forward_system line_graph (fun _ => true) (fun _ a => a))
    (fun b => b) = false.
Proof.
  vm_compute; auto.
Qed.

Definition line_forward := forward_system line_graph (fun _ => true) (fun _ a => a).
Definition line_static := forward_static line_graph (fun _ => true) (fun _ a => a).
Definition line_index := index_system bool_encoding line_forward line_static.

Example dense_cut_accepts :
  option_map (fun m => map (lookup bool_encoding bool_lattice m) [true; false])
    (expand bool_encoding bool_lattice line_forward line_static line_index
      (CutCertificate FinSet.empty Map.empty [true; false])) = Some [true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example dense_cut_rejects_reversed_plan :
  expand bool_encoding bool_lattice line_forward line_static line_index
    (CutCertificate FinSet.empty Map.empty [false; true]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition cycle_graph : Graph.t bool bool := Graph.Make [true] [true; false]
  (fun b => [b]) (fun b => b) negb.

Example cycle_cut_accepts :
  let sys := forward_system cycle_graph (fun _ => true) (fun _ a => a) in
  let ss := forward_static cycle_graph (fun _ => true) (fun _ a => a) in
  option_map (fun m => map (lookup bool_encoding bool_lattice m) [true; false])
    (expand bool_encoding bool_lattice sys ss (index_system bool_encoding sys ss)
      (CutCertificate (FinSet.of_list bool_encoding [true])
        (Map.set bool_encoding true true Map.empty) [false])) = Some [true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example uncut_cycle_rejects :
  let sys := forward_system cycle_graph (fun _ => true) (fun _ a => a) in
  let ss := forward_static cycle_graph (fun _ => true) (fun _ a => a) in
  expand bool_encoding bool_lattice sys ss (index_system bool_encoding sys ss)
    (CutCertificate FinSet.empty Map.empty [true; false]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cycle_graph_wf : graph_wf cycle_graph.
Proof.
  constructor; cbn.
  - constructor; [intros [Hbad|Hbad]; [discriminate|contradiction]|].
    constructor; [intro Hbad; contradiction|constructor].
  - intros v [<-|Hbad]; [left; reflexivity|contradiction].
  - intros v e [<-|Hbad]; [reflexivity|contradiction].
  - intros [] [] Hnode [Heq|Hbad]; cbn in *; try discriminate; try contradiction; auto.
Qed.

Example cycle_meets_true : meets_every_cycle cycle_graph (fun b => b).
Proof.
  intros v es Hnonempty Hpath; destruct es as [|e es]; [contradiction|].
  assert (He : e = v) by (inversion Hpath; cbn in *; congruence).
  subst e; destruct v.
  - exists true; split; [left; reflexivity|reflexivity].
  - inversion Hpath as [|e rest v Hout Htail]; subst; cbn in Htail.
    inversion Htail as [|e' rest' v' Hout' Htail']; cbn in *; subst.
    exists true; split; [right; left; reflexivity|reflexivity].
Qed.

Example graph_cuts_both_dense_directions :
  cuts_every_cycle (forward_static cycle_graph (fun _ => true) (fun _ a => a)) (fun b => b) /\
  cuts_every_cycle (backward_static cycle_graph (fun _ => false) (fun _ a => a)) (fun b => b).
Proof.
  split.
  - apply forward_cuts_every_cycle; [exact cycle_graph_wf|exact cycle_meets_true].
  - apply backward_cuts_every_cycle; [exact cycle_graph_wf|exact cycle_meets_true].
Qed.

(** * Histories and forward soundness *)

Definition line_semantics : semantics bool nat :=
  Semantics (fun b => b = true) (fun s l t => s = true /\ l = [7] /\ t = false).

Definition line_view : graph_view bool nat bool unit :=
  GraphView line_graph (fun b => b) (fun _ _ _ _ => True) (fun _ _ _ => False).

Example line_graph_wf : graph_wf line_graph.
Proof.
  constructor; cbn.
  - constructor; [intros [Hbad|Hbad]; [discriminate|contradiction]|].
    constructor; [intro Hbad; contradiction|constructor].
  - intros v [<-|Hbad]; [left; reflexivity|contradiction].
  - intros [] [] Hin; cbn in Hin; [reflexivity|contradiction].
  - intros [] [] Hnode Hedge; cbn in *; [right; left; reflexivity|contradiction].
Qed.

Example line_view_laws : graph_view_laws line_semantics line_view.
Proof.
  constructor.
  - exact line_graph_wf.
  - intros s ->; cbn; auto.
  - intros s l s' Hreachable Hstep; right; exists tt; exact I.
  - intros s l s' [] Hreachable [-> [-> ->]] Htaken; cbn; auto.
  - intros s l s' Hreachable Hstep Hstay; contradiction.
Qed.

Example one_edge_history : run_edges line_semantics line_view true [tt] false.
Proof.
  eapply run_cons with (l := [7]); [repeat split|exact I|constructor].
Qed.

Example history_summary_updates :
  last_writer (fun e x => Nat.eqb e x) [1; 2; 1; 3] 1 = Some 1 /\
  last_writer (fun e x => Nat.eqb e x) [1; 2; 1; 3] 4 = None /\
  arrivals_since (Nat.eqb 0) (Nat.eqb 1) [1; 1; 0; 1; 2; 1] = 2 /\
  arrivals_since (Nat.eqb 0) (Nat.eqb 1) [1; 1; 0] = 0.
Proof.
  vm_compute; auto.
Qed.

Definition present : concretisation bool bool := Concretisation bool bool (fun a _ => a = true).

Example present_laws : concretisation_laws bool_lattice present.
Proof.
  constructor; intros [] [] c Hle Hfact; cbn in *; congruence.
Qed.

Example forward_reachable_fact : forall s, reachable_state line_semantics s ->
  gamma present ((fun _ => true) (point line_view s)) s.
Proof.
  apply (forward_invariant_sound line_semantics line_view bool_lattice (fun _ => present)
    (fun _ => true) (fun _ a => a) (fun _ => true)).
  - exact line_view_laws.
  - exact present_laws.
  - intros s Hinitial; reflexivity.
  - intros e s l s' Hreachable Hstep Htaken Hfact; exact Hfact.
  - intros s l s' Hreachable Hstep Hstay Hfact; contradiction.
  - apply check_post_iff; vm_compute; reflexivity.
Qed.

Definition history_present : concretisation bool (bool * list unit) :=
  Concretisation bool (bool * list unit) (fun a sh => snd sh <> [] -> a = true).

Example history_forward_fact : forall s0 es s, initial line_semantics s0 ->
  run_edges line_semantics line_view s0 es s ->
  gamma history_present (negb s) (s, es).
Proof.
  apply (forward_history_sound line_semantics line_view bool_lattice (fun _ => history_present)
    (fun _ => false) (fun _ _ => true) negb).
  - exact line_view_laws.
  - constructor; intros [] [] c Hle Hfact; cbn in *; try discriminate; auto.
  - intros s Hinitial Hnonempty; exfalso; apply Hnonempty; reflexivity.
  - intros e s0 es s l s' Hinitial Hhistory Hstep Htaken Hfact Hnonempty; reflexivity.
  - intros s0 es s l s' Hinitial Hhistory Hstep Hstay Hfact; contradiction.
  - apply check_post_iff; vm_compute; reflexivity.
Qed.

Example nonempty_history_observes_fact : forall s0 es s, initial line_semantics s0 ->
  run_edges line_semantics line_view s0 es s -> es <> [] -> negb s = true.
Proof.
  intros s0 es s Hinitial Hhistory Hnonempty.
  exact (history_forward_fact s0 es s Hinitial Hhistory Hnonempty).
Qed.

(** * Silent stuck-endpoint matching *)

Definition quiet : semantics bool nat := Semantics (fun _ => True) (fun _ _ _ => False).
Definition delay : semantics bool nat :=
  Semantics (fun _ => True) (fun s l t => s = true /\ l = [] /\ t = false).
Definition loop : semantics bool nat :=
  Semantics (fun _ => True) (fun s l t => l = [] /\ t = s).
Definition no_endings : endings bool := Endings (fun _ => False) (fun _ => False) (fun _ => False).

Example quiet_stuck : forall b, ends_as quiet no_endings EndStuck b.
Proof.
  intro b; split; [intros [l [t Hstep]]; exact Hstep|repeat split; intro Hbad; exact Hbad].
Qed.

Example delay_false_stuck : ends_as delay no_endings EndStuck false.
Proof.
  split.
  - intros [l [t [Hbad Hrest]]]; discriminate.
  - repeat split; intro Hbad; exact Hbad.
Qed.

Example delay_run : forall b, exec delay b [] false.
Proof.
  intros []; [|constructor].
  eapply exec_step with (l := []) (tr := []); [repeat split|constructor].
Qed.

Example quiet_delay_stuttering : stuttering quiet no_endings delay no_endings
  (fun _ _ => True) (fun _ _ => 0) (fun _ t => if t then 1 else 0).
Proof.
  constructor.
  - intros s t [] Hrel Hend; cbn in Hend; try contradiction.
    exists false; split; [apply delay_run|exact delay_false_stuck].
  - intros s t [] Hrel Hend; cbn in Hend; try contradiction.
    exists s; split; [constructor|apply quiet_stuck].
  - intros s t l s' Hrel Hstep; contradiction.
  - intros s t l t' Hrel [-> [-> ->]]; left; cbn; repeat split; auto.
Qed.

Example silent_stuck_behaviour : same_behaviour quiet no_endings true delay no_endings true.
Proof.
  eapply stuttering_same_behaviour; [exact quiet_delay_stuttering|exact I].
Qed.

Definition one_point_graph : Graph.t unit unit :=
  Graph.Make [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt).
Definition one_point_view : graph_view bool nat unit unit :=
  GraphView one_point_graph (fun _ => tt) (fun _ _ _ _ => False) (fun _ _ _ => True).
Definition all_agree : agreement unit bool := Agreement unit bool (fun _ _ _ => True).

Example unmatched_stuck_rejects_ends_forth :
  ~ ends_forth quiet loop no_endings no_endings one_point_view one_point_view all_agree
    (fun _ => True) (fun _ => True) (fun _ => tt).
Proof.
  intro Hends.
  destruct (Hends true true EndStuck I I eq_refl I (quiet_stuck true)) as [t [Hrun [Hhalt Hrest]]].
  apply Hhalt; exists [], t; split; reflexivity.
Qed.

Example one_point_view_laws : forall m, graph_view_laws m one_point_view.
Proof.
  intro m; constructor.
  - constructor; cbn.
    + constructor; [intro Hbad; contradiction|constructor].
    + intros [] Hin; left; reflexivity.
    + intros [] [] Hin; contradiction.
    + intros [] [] Hnode Hin; contradiction.
  - intros s Hinitial; left; reflexivity.
  - intros s l s' Hreachable Hstep; left; exact I.
  - intros s l s' e Hreachable Hstep Htaken; contradiction.
  - intros s l s' Hreachable Hstep Hstays; reflexivity.
Qed.

Example all_agree_laws : agreement_laws unit_lattice all_agree.
Proof.
  constructor; intros; exact I.
Qed.

Example quiet_delay_agreement2 : same_behaviour quiet no_endings true delay no_endings true.
Proof.
  eapply (agreement_simulation2 quiet delay no_endings no_endings
    one_point_view one_point_view unit_lattice (fun _ => all_agree)
    (reachable_state quiet) (reachable_state delay) (fun _ => tt) (fun _ _ => tt)
    (fun _ => tt) (fun _ _ => 0) (fun _ t => if t then 1 else 0) true true).
  - apply one_point_view_laws.
  - apply one_point_view_laws.
  - reflexivity.
  - exact all_agree_laws.
  - apply reachable_invariant.
  - apply reachable_invariant.
  - split; split.
    + intros e s l s' t Hs Ht Hpoint Hstep Htaken; contradiction.
    + intros s l s' t Hs Ht Hpoint Hstep; contradiction.
    + intros e s l s' t Hs Ht Hpoint Hstep Htaken; contradiction.
    + intros s l s' t Hs Ht Hpoint [-> [-> ->]] Hstay Hagree; left; cbn; auto.
  - split.
    + intros s t [] Hs Ht Hpoint Hagree Hend; cbn in Hend; try contradiction.
      exists false; split; [apply delay_run|exact delay_false_stuck].
    + intros s t [] Hs Ht Hpoint Hagree Hend; cbn in Hend; try contradiction.
      exists t; split; [constructor|apply quiet_stuck].
  - apply check_post_iff; vm_compute; reflexivity.
  - exact I.
  - exact I.
  - reflexivity.
  - exact I.
Qed.

Example divergence_preserved : diverges loop true.
Proof.
  apply (diverges_from_progress loop (fun _ => True)).
  - intros s Hs; exists [], s; split; [split; reflexivity|exact I].
  - exact I.
Qed.

(** * Productive matching after silent prefixes *)

Definition visible_loop : semantics bool nat :=
  Semantics (fun _ => True) (fun s l t => l = [7] /\ t = s).

Definition alternating : semantics bool nat := Semantics (fun _ => True)
  (fun (s : bool) l t => if s then l = [] /\ t = false else l = [7] /\ t = true).

Example silent_prefix_stuttering : stuttering visible_loop no_endings alternating no_endings
  (fun _ _ => True) (fun _ _ => 0) (fun _ t => if t then 1 else 0).
Proof.
  constructor.
  - intros s t [] Hrel Hend; cbn in Hend; try contradiction.
    destruct Hend as [Hhalt Hrest]; exfalso; apply Hhalt; exists [7], s; split; reflexivity.
  - intros s t [] Hrel Hend; cbn in Hend; try contradiction.
    destruct Hend as [Hhalt Hrest]; exfalso; apply Hhalt; destruct t.
    + exists [], false; split; reflexivity.
    + exists [7], true; split; reflexivity.
  - intros s t l s' Hrel [-> ->]; right; exists false, true; split.
    + destruct t; [|constructor].
      eapply exec_step with (l := []) (tr := []); [split; reflexivity|constructor].
    + split; [split; reflexivity|exact I].
  - intros s [] l t' Hrel Hstep; cbn in Hstep; destruct Hstep as [-> ->].
    + left; cbn; auto.
    + right; exists s, s; split; [constructor|]; split; [split; reflexivity|exact I].
Qed.

Example divergence_matches_silent_prefix : diverges alternating true.
Proof.
  apply (stuttering_diverges visible_loop no_endings alternating no_endings _ _ _
    silent_prefix_stuttering true true I).
  apply (diverges_from_progress visible_loop (fun _ => True)).
  - intros s Hs; exists [7], s; split; [split; reflexivity|exact I].
  - exact I.
Qed.

Example diverging_prefix_behaviour :
  same_behaviour visible_loop no_endings true alternating no_endings true.
Proof.
  eapply stuttering_same_behaviour; [exact silent_prefix_stuttering|exact I].
Qed.
