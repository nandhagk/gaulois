(** * Backward facts and behavioural agreement

    Solution-relative local obligations turn backward post-solutions into bisimulations.
    For example, a deleted silent instruction is covered by a decreasing stuttering measure.
    Builds on: ViewsSemantics, ViewsGraph and OrderConcrete. *)

From Stdlib Require Import List.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph.
Import List.ListNotations.

(** Symmetric agreements can compare states in either order at the same fact. *)
Definition agreement_symmetric {A C} (R : agreement A C) : Prop :=
  forall a x y, agree R a x y -> agree R a y x.

(** Swapping agreement reverses only its two concrete arguments. *)
Definition agreement_swap {A C} (R : agreement A C) : agreement A C :=
  Agreement A C (fun a x y => agree R a y x).

(** An invariant contains initial states, is preserved by steps and implies reachability. *)
Record invariant_of {S O} (m : semantics S O) (inv : S -> Prop) : Prop := {
  inv_initial : forall s, initial m s -> inv s;
  inv_step : forall s l s', inv s -> step m s l s' -> inv s';
  inv_reachable : forall s, inv s -> reachable_state m s
}.

Arguments inv_initial {S O m inv}.
Arguments inv_step {S O m inv}.
Arguments inv_reachable {S O m inv}.

(** Local lock-step obligations preserve the solution's target fact on taken and stay steps. *)
Definition step_agrees {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (R : agreement A S) (inv : S -> Prop) (bt : E -> A -> A) (sigma : N -> A) : Prop :=
  (forall e s l s' t, inv s -> inv t -> point gv t = point gv s ->
    step m s l s' -> taken gv s l s' e ->
    agree R (bt e (sigma (Graph.target (cfg gv) e))) s t ->
    exists t', step m t l t' /\ taken gv t l t' e /\
      agree R (sigma (Graph.target (cfg gv) e)) s' t') /\
  (forall s l s' t, inv s -> inv t -> point gv t = point gv s ->
    step m s l s' -> stays gv s l s' -> agree R (sigma (point gv s)) s t ->
    exists t', step m t l t' /\ stays gv t l t' /\ agree R (sigma (point gv s)) s' t').

(** Exit agreement fixes the three declared ending classifications. *)
Definition ends_agree {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (R : agreement A S) (inv : S -> Prop) (exitf : N -> A) : Prop :=
  forall s t, inv s -> inv t -> point gv t = point gv s -> agree R (exitf (point gv s)) s t ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t).

(** Related states share a point, satisfy the invariant and agree at its solution fact. *)
Definition agreeing {S O N E A} (gv : graph_view S O N E) (R : agreement A S) (inv : S -> Prop)
    (sigma : N -> A) (s t : S) : Prop :=
  point gv t = point gv s /\ inv s /\ inv t /\ agree R (sigma (point gv s)) s t.

(** One program's steps match after silent runs or decrease its unmatched-stay measure. *)
Definition forth_agrees {S O N E A} (ma mb : semantics S O) (gva gvb : graph_view S O N E)
    (R : agreement A S) (inva invb : S -> Prop) (bt : E -> A -> A) (sigma : N -> A)
    (mua : S -> S -> nat) : Prop :=
  (forall e s l s' t, inva s -> invb t -> point gvb t = point gva s ->
    step ma s l s' -> taken gva s l s' e ->
    agree R (bt e (sigma (Graph.target (cfg gva) e))) s t ->
    exists t1 t', exec mb t nil t1 /\ step mb t1 l t' /\ point gvb t' = point gva s' /\
      agree R (sigma (point gva s')) s' t') /\
  (forall s l s' t, inva s -> invb t -> point gvb t = point gva s ->
    step ma s l s' -> stays gva s l s' -> agree R (sigma (point gva s)) s t ->
    (l = nil /\ agree R (sigma (point gva s)) s' t /\ mua s' t < mua s t) \/
    (exists t1 t', exec mb t nil t1 /\ step mb t1 l t' /\ point gvb t' = point gva s' /\
      agree R (sigma (point gva s')) s' t')).

(** Every ending, including stuck, must have a silent matching run of the same kind. *)
Definition ends_forth {S O N E A} (ma mb : semantics S O) (ea eb : endings S)
    (gva gvb : graph_view S O N E) (R : agreement A S) (inva invb : S -> Prop)
    (exitf : N -> A) : Prop :=
  forall s t k, inva s -> invb t -> point gvb t = point gva s ->
    agree R (exitf (point gva s)) s t -> ends_as ma ea k s ->
    exists t1, exec mb t nil t1 /\ ends_as mb eb k t1.

(** Two-program step obligations use the reversed agreement in the return direction. *)
Definition step_agrees2 {S O N E A} (m1 m2 : semantics S O) (gv1 gv2 : graph_view S O N E)
    (R : agreement A S) (inv1 inv2 : S -> Prop) (bt : E -> A -> A) (sigma : N -> A)
    (mu1 mu2 : S -> S -> nat) : Prop :=
  forth_agrees m1 m2 gv1 gv2 R inv1 inv2 bt sigma mu1 /\
  forth_agrees m2 m1 gv2 gv1 (agreement_swap R) inv2 inv1 bt sigma (fun t s => mu2 s t).

(** Two-program ending obligations explicitly match all four kinds in both directions. *)
Definition ends_agree2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (gv1 gv2 : graph_view S O N E) (R : agreement A S) (inv1 inv2 : S -> Prop)
    (exitf : N -> A) : Prop :=
  ends_forth m1 m2 en1 en2 gv1 gv2 R inv1 inv2 exitf /\
  ends_forth m2 m1 en2 en1 gv2 gv1 (agreement_swap R) inv2 inv1 exitf.

(** Two-program related states share a point and satisfy their own invariants. *)
Definition agreeing2 {S O N E A} (gv1 gv2 : graph_view S O N E) (R : agreement A S)
    (inv1 inv2 : S -> Prop) (sigma : N -> A) (s t : S) : Prop :=
  point gv2 t = point gv1 s /\ inv1 s /\ inv2 t /\ agree R (sigma (point gv1 s)) s t.

(** * Invariants *)

(** Reachability holds initially and is preserved by every transition. *)
Theorem reachable_invariant {S O} (m : semantics S O) : invariant_of m (reachable_state m).
Proof.
  constructor.
  - intros s Hinitial; exists s, []; split; [exact Hinitial|constructor].
  - intros s l s' Hreachable Hstep; eapply reachable_state_step; eassumption.
  - intros s Hreachable; exact Hreachable.
Qed.

Lemma invariant_exec {S O} (m : semantics S O) inv :
  invariant_of m inv -> forall s tr t, exec m s tr t -> inv s -> inv t.
Proof.
  intros Hinv s tr t Hrun; induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intro Hs.
  - exact Hs.
  - apply IH; eapply inv_step; eassumption.
Qed.

Lemma agreement_swap_laws {A C} (L : lattice A) (R : agreement A C) :
  agreement_laws L R -> agreement_laws L (agreement_swap R).
Proof.
  intro HR; constructor.
  - intros a c; apply (agree_refl HR).
  - intros a b x y Hab Hxy; apply (agree_antitone HR a b y x Hab Hxy).
Qed.

Lemma agreeing_sym {S O N E A} (gv : graph_view S O N E) (R : agreement A S) inv sigma s t :
  agreement_symmetric R -> agreeing gv R inv sigma s t -> agreeing gv R inv sigma t s.
Proof.
  intros Hsym [Hpoint [Hs [Ht Hagree]]]; unfold agreeing.
  split; [symmetry; exact Hpoint|]; split; [exact Ht|]; split; [exact Hs|].
  rewrite Hpoint; apply Hsym; exact Hagree.
Qed.

(** * Lock-step agreement *)

Lemma agreement_step {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) R inv exitf bt sigma :
  graph_view_laws m gv -> agreement_laws L R -> invariant_of m inv ->
  step_agrees m gv R inv bt sigma -> post_solution L (backward_system (cfg gv) exitf bt) sigma ->
  forall s t l s', agreeing gv R inv sigma s t -> step m s l s' ->
  exists t', step m t l t' /\ agreeing gv R inv sigma s' t'.
Proof.
  intros Hview HR Hinv [Hedge Hstay] Hpost s t l s' [Hpoint [Hs [Ht Hagree]]] Hstep.
  pose proof (inv_reachable Hinv s Hs) as Hreachable.
  destruct (edge_covers Hview s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - destruct (Hstay s l s' t Hs Ht Hpoint Hstep Hstays Hagree)
      as [t' [Hmatch [Hstays' Hagree']]].
    exists t'; split; [exact Hmatch|].
    pose proof (stays_point Hview s l s' Hreachable Hstep Hstays) as Hsource.
    pose proof (stays_point Hview t l t' (inv_reachable Hinv t Ht) Hmatch Hstays') as Htarget.
    unfold agreeing; rewrite Hsource, Htarget; repeat split; try assumption.
    + exact (inv_step Hinv s l s' Hs Hstep).
    + exact (inv_step Hinv t l t' Ht Hmatch).
  - destruct (view_taken_edge m gv s l s' e Hview Hreachable Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (proj1 (backward_post_solution_iff _ _ _ _ _ ) Hpost) as [Hseed Hflow].
    assert (Hinput : agree R (bt e (sigma (Graph.target (cfg gv) e))) s t).
    { eapply (agree_antitone HR); [apply Hflow; exact He|rewrite Hsource; exact Hagree]. }
    destruct (Hedge e s l s' t Hs Ht Hpoint Hstep Htaken Hinput)
      as [t' [Hmatch [Htaken' Hagree']]].
    destruct (taken_edge Hview t l t' e (inv_reachable Hinv t Ht) Hmatch Htaken')
      as [Hout' Htarget'].
    exists t'; split; [exact Hmatch|]; unfold agreeing; repeat split.
    + congruence.
    + exact (inv_step Hinv s l s' Hs Hstep).
    + exact (inv_step Hinv t l t' Ht Hmatch).
    + rewrite <- Htarget; exact Hagree'.
Qed.

(** A backward post-solution and local agreement obligations give a lock-step bisimulation. *)
Theorem agreement_bisimulation {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S) (inv : S -> Prop)
    (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A) :
  graph_view_laws m gv -> agreement_laws L (R sigma) -> agreement_symmetric (R sigma) ->
  invariant_of m inv -> step_agrees m gv (R sigma) inv bt sigma ->
  ends_agree m en gv (R sigma) inv exitf ->
  post_solution L (backward_system (cfg gv) exitf bt) sigma ->
  bisimulation m en m en (agreeing gv (R sigma) inv sigma).
Proof.
  intros Hview HR Hsym Hinv Hstep Hends Hpost.
  pose proof (agreement_step m gv L (R sigma) inv exitf bt sigma
    Hview HR Hinv Hstep Hpost) as Hmatch.
  constructor.
  - intros s t k Hrel; destruct Hrel as [Hpoint [Hs [Ht Hagree]]].
    destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
    assert (Hexit : agree (R sigma) (exitf (point gv s)) s t).
    { eapply (agree_antitone HR); [apply Hseed|exact Hagree].
      eapply view_point_in_nodes; [exact Hview|apply (inv_reachable Hinv); exact Hs]. }
    destruct (Hends s t Hs Ht Hpoint Hexit) as [Hfinal [Htrap Hstop]].
    assert (Hrel : agreeing gv (R sigma) inv sigma s t) by (repeat split; assumption).
    assert (Hreverse : agreeing gv (R sigma) inv sigma t s).
    { apply agreeing_sym; assumption. }
    assert (Hrunning : running m s <-> running m t).
    { split; intros [l [u Hrun]].
      - destruct (Hmatch s t l u Hrel Hrun) as [v [Hrun' Hrel']].
        exists l, v; exact Hrun'.
      - destruct (Hmatch t s l u Hreverse Hrun) as [v [Hrun' Hrel']].
        exists l, v; exact Hrun'. }
    destruct k; cbn; [exact Hfinal|exact Htrap|exact Hstop|unfold stuck; tauto].
  - exact Hmatch.
  - intros s t l t' Hrel Hrun.
    destruct (Hmatch t s l t' (agreeing_sym _ _ _ _ _ _ Hsym Hrel) Hrun)
      as [s' [Hrun' Hrel']].
    exists s'; split; [exact Hrun'|apply agreeing_sym; assumption].
Qed.

(** Initially agreeing runs of one program have equal observable behaviour. *)
Theorem agreement_same_behaviour {S O N E A} (m : semantics S O) (en : endings S)
    (gv : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S) (inv : S -> Prop)
    (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A) (s0 t0 : S) :
  graph_view_laws m gv -> agreement_laws L (R sigma) -> agreement_symmetric (R sigma) ->
  invariant_of m inv -> step_agrees m gv (R sigma) inv bt sigma ->
  ends_agree m en gv (R sigma) inv exitf ->
  post_solution L (backward_system (cfg gv) exitf bt) sigma ->
  initial m s0 -> initial m t0 -> point gv t0 = point gv s0 ->
  agree (R sigma) (sigma (point gv s0)) s0 t0 ->
  same_behaviour m en s0 m en t0.
Proof.
  intros Hview HR Hsym Hinv Hstep Hends Hpost Hs Ht Hpoint Hagree.
  eapply bisimilar_same_behaviour.
  - eapply agreement_bisimulation; eassumption.
  - unfold agreeing; repeat split; try assumption; apply (inv_initial Hinv); assumption.
Qed.

(** * Two-program agreement *)

Lemma agreeing2_swap {S O N E A} (gv1 gv2 : graph_view S O N E)
    (R : agreement A S) inv1 inv2 sigma s t :
  agreeing2 gv1 gv2 R inv1 inv2 sigma s t <->
  agreeing2 gv2 gv1 (agreement_swap R) inv2 inv1 sigma t s.
Proof.
  unfold agreeing2, agreement_swap; cbn; split; intros [Hpoint [Hs [Ht Hagree]]].
  - rewrite Hpoint; repeat split; try assumption; symmetry; exact Hpoint.
  - rewrite Hpoint; repeat split; try assumption; symmetry; exact Hpoint.
Qed.

Lemma agreement_forth {S O N E A} (ma mb : semantics S O) (gva gvb : graph_view S O N E)
    (L : lattice A) R inva invb exitf bt sigma mua :
  graph_view_laws ma gva -> agreement_laws L R -> invariant_of ma inva -> invariant_of mb invb ->
  forth_agrees ma mb gva gvb R inva invb bt sigma mua ->
  post_solution L (backward_system (cfg gva) exitf bt) sigma ->
  forall s t l s', agreeing2 gva gvb R inva invb sigma s t -> step ma s l s' ->
  (l = [] /\ agreeing2 gva gvb R inva invb sigma s' t /\ mua s' t < mua s t) \/
  (exists t1 t', exec mb t [] t1 /\ step mb t1 l t' /\
    agreeing2 gva gvb R inva invb sigma s' t').
Proof.
  intros Hview HR Hinva Hinvb [Hedge Hstay] Hpost s t l s'
    [Hpoint [Hs [Ht Hagree]]] Hstep.
  pose proof (inv_reachable Hinva s Hs) as Hreachable.
  assert (Hs' : inva s') by (eapply inv_step; eassumption).
  destruct (edge_covers Hview s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - destruct (Hstay s l s' t Hs Ht Hpoint Hstep Hstays Hagree)
      as [[Hsilent [Hagree' Hdecrease]]|[t1 [t' [Hprefix [Hmatch [Hpoint' Hagree']]]]]].
    + left; split; [exact Hsilent|]; split; [|exact Hdecrease].
      unfold agreeing2; rewrite (stays_point Hview s l s' Hreachable Hstep Hstays).
      repeat split; assumption.
    + right; exists t1, t'; split; [exact Hprefix|]; split; [exact Hmatch|].
      unfold agreeing2; repeat split; try assumption.
      eapply inv_step; [exact Hinvb| |exact Hmatch].
      eapply invariant_exec; eassumption.
  - destruct (view_taken_edge ma gva s l s' e Hview Hreachable Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
    assert (Hinput : agree R (bt e (sigma (Graph.target (cfg gva) e))) s t).
    { eapply (agree_antitone HR); [apply Hflow; exact He|rewrite Hsource; exact Hagree]. }
    destruct (Hedge e s l s' t Hs Ht Hpoint Hstep Htaken Hinput)
      as [t1 [t' [Hprefix [Hmatch [Hpoint' Hagree']]]]].
    right; exists t1, t'; split; [exact Hprefix|]; split; [exact Hmatch|].
    unfold agreeing2; repeat split; try assumption.
    eapply inv_step; [exact Hinvb| |exact Hmatch]; eapply invariant_exec; eassumption.
Qed.

Lemma agreement_ends_forth {S O N E A} (ma mb : semantics S O) ea eb
    (gva gvb : graph_view S O N E) (L : lattice A) R inva invb exitf bt sigma :
  graph_view_laws ma gva -> agreement_laws L R -> invariant_of ma inva ->
  ends_forth ma mb ea eb gva gvb R inva invb exitf ->
  post_solution L (backward_system (cfg gva) exitf bt) sigma ->
  forall s t k, agreeing2 gva gvb R inva invb sigma s t -> ends_as ma ea k s ->
  exists t1, exec mb t [] t1 /\ ends_as mb eb k t1.
Proof.
  intros Hview HR Hinv Hends Hpost s t k [Hpoint [Hs [Ht Hagree]]] Hend.
  apply (Hends s t k Hs Ht Hpoint); [|exact Hend].
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  eapply (agree_antitone HR); [apply Hseed|exact Hagree].
  eapply view_point_in_nodes; [exact Hview|apply (inv_reachable Hinv); exact Hs].
Qed.

(** Two initially agreeing programs with the two-way local obligations have equal behaviour. *)
Theorem agreement_simulation2 {S O N E A} (m1 m2 : semantics S O) (en1 en2 : endings S)
    (gv1 gv2 : graph_view S O N E) (L : lattice A) (R : (N -> A) -> agreement A S)
    (inv1 inv2 : S -> Prop) (exitf : N -> A) (bt : E -> A -> A) (sigma : N -> A)
    (mu1 mu2 : S -> S -> nat) (s0 t0 : S) :
  graph_view_laws m1 gv1 -> graph_view_laws m2 gv2 -> cfg gv2 = cfg gv1 ->
  agreement_laws L (R sigma) -> invariant_of m1 inv1 -> invariant_of m2 inv2 ->
  step_agrees2 m1 m2 gv1 gv2 (R sigma) inv1 inv2 bt sigma mu1 mu2 ->
  ends_agree2 m1 m2 en1 en2 gv1 gv2 (R sigma) inv1 inv2 exitf ->
  post_solution L (backward_system (cfg gv1) exitf bt) sigma ->
  initial m1 s0 -> initial m2 t0 -> point gv2 t0 = point gv1 s0 ->
  agree (R sigma) (sigma (point gv1 s0)) s0 t0 ->
  same_behaviour m1 en1 s0 m2 en2 t0.
Proof.
  intros Hview1 Hview2 Hcfg HR Hinv1 Hinv2 [Hforth Hback] [Hends1 Hends2]
    Hpost Hs0 Ht0 Hpoint Hagree.
  assert (Hpost2 : post_solution L (backward_system (cfg gv2) exitf bt) sigma).
  { rewrite Hcfg; exact Hpost. }
  pose proof (agreement_swap_laws L (R sigma) HR) as HRswap.
  eapply stuttering_same_behaviour with (R := agreeing2 gv1 gv2 (R sigma) inv1 inv2 sigma)
    (mu1 := mu1) (mu2 := mu2).
  - constructor.
    + eapply agreement_ends_forth; eassumption.
    + intros s t k Hrel Hend.
      eapply (agreement_ends_forth m2 m1 en2 en1 gv2 gv1 L (agreement_swap (R sigma))
        inv2 inv1 exitf bt sigma Hview2 HRswap Hinv2 Hends2 Hpost2 t s k).
      * apply agreeing2_swap; exact Hrel.
      * exact Hend.
    + eapply agreement_forth; eassumption.
    + intros s t l t' Hrel Hstep.
      destruct (agreement_forth m2 m1 gv2 gv1 L (agreement_swap (R sigma)) inv2 inv1
        exitf bt sigma (fun t s => mu2 s t) Hview2 HRswap Hinv2 Hinv1 Hback Hpost2
        t s l t' (proj1 (agreeing2_swap _ _ _ _ _ _ _ _) Hrel) Hstep)
        as [[Hsilent [Hrel' Hdecrease]]|[s1 [s' [Hprefix [Hmatch Hrel']]]]].
      * left; split; [exact Hsilent|]; split; [apply agreeing2_swap; exact Hrel'|exact Hdecrease].
      * right; exists s1, s'; split; [exact Hprefix|]; split; [exact Hmatch|].
        apply agreeing2_swap; exact Hrel'.
  - unfold agreeing2; repeat split; try assumption.
    + apply (inv_initial Hinv1); exact Hs0.
    + apply (inv_initial Hinv2); exact Ht0.
Qed.
