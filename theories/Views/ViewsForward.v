(** * Forward invariants over states and histories

    Forward post-solutions contain the concrete states and edge histories of reachable runs.
    For example, a reaching-definition fact can observe the last writer in a run's history.
    Builds on: ViewsSemantics, ViewsGraph, ViewsAgreement and OrderConcrete. *)

From Stdlib Require Import List.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement.
Import List.ListNotations.

(** A forward invariant combines reachability with the solution's concretisation at the point. *)
Definition forward_inv {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (G : concretisation A S) (sigma : N -> A) (s : S) : Prop :=
  reachable_state m s /\ gamma G (sigma (point gv s)) s.

Lemma forward_fact_step {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : concretisation A S) init ft sigma :
  graph_view_laws m gv -> concretisation_laws L G ->
  (forall e s l s', reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    gamma G (sigma (point gv s)) s -> gamma G (ft e (sigma (point gv s))) s') ->
  (forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
    gamma G (sigma (point gv s)) s -> gamma G (sigma (point gv s)) s') ->
  post_solution L (forward_system (cfg gv) init ft) sigma ->
  forall s l s', reachable_state m s -> step m s l s' ->
    gamma G (sigma (point gv s)) s -> gamma G (sigma (point gv s')) s'.
Proof.
  intros Hview HG Hedge Hstay Hpost s l s' Hreachable Hstep Hfact.
  destruct (edge_covers Hview s l s' Hreachable Hstep) as [Hstays|[e Htaken]].
  - rewrite (stays_point Hview s l s' Hreachable Hstep Hstays).
    eapply Hstay; eassumption.
  - destruct (view_taken_edge m gv s l s' e Hview Hreachable Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
    eapply (gamma_monotone HG).
    + rewrite <- Htarget; apply Hflow; exact He.
    + rewrite Hsource; eapply Hedge; eassumption.
Qed.

Lemma forward_initial_fact {S O N E A C} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : concretisation A C) init ft sigma s c :
  graph_view_laws m gv -> concretisation_laws L G -> initial m s ->
  gamma G (init (point gv s)) c -> post_solution L (forward_system (cfg gv) init ft) sigma ->
  gamma G (sigma (point gv s)) c.
Proof.
  intros Hview HG Hinitial Hfact Hpost.
  destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  eapply (gamma_monotone HG); [apply Hseed; apply (entry_points Hview); exact Hinitial|exact Hfact].
Qed.

(** A forward post-solution and its local soundness obligations contain every reachable state. *)
Theorem forward_invariant_sound {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A S) (init : N -> A) (ft : E -> A -> A)
    (sigma : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G sigma) ->
  (forall s, initial m s -> gamma (G sigma) (init (point gv s)) s) ->
  (forall e s l s', reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    gamma (G sigma) (sigma (point gv s)) s ->
    gamma (G sigma) (ft e (sigma (point gv s))) s') ->
  (forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
    gamma (G sigma) (sigma (point gv s)) s -> gamma (G sigma) (sigma (point gv s)) s') ->
  post_solution L (forward_system (cfg gv) init ft) sigma ->
  forall s, reachable_state m s -> gamma (G sigma) (sigma (point gv s)) s.
Proof.
  intros Hview HG Hinitial Hedge Hstay Hpost s [s0 [tr [Hs0 Hrun]]].
  assert (Hreachable : reachable_state m s0).
  { exists s0, []; split; [exact Hs0|constructor]. }
  assert (Hfact : gamma (G sigma) (sigma (point gv s0)) s0).
  { eapply forward_initial_fact;
      [exact Hview|exact HG|exact Hs0|apply Hinitial; exact Hs0|exact Hpost]. }
  clear Hs0; revert Hreachable Hfact.
  induction Hrun as [s|s l s' tr t Hstep Hrun IH]; intros Hreachable Hfact.
  - exact Hfact.
  - apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply forward_fact_step; eassumption.
Qed.

(** Reachability together with the forward solution is an inductive invariant. *)
Theorem forward_inv_invariant {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A S) (init : N -> A) (ft : E -> A -> A)
    (phi : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G phi) ->
  (forall s, initial m s -> gamma (G phi) (init (point gv s)) s) ->
  (forall e s l s', reachable_state m s -> step m s l s' -> taken gv s l s' e ->
    gamma (G phi) (phi (point gv s)) s -> gamma (G phi) (ft e (phi (point gv s))) s') ->
  (forall s l s', reachable_state m s -> step m s l s' -> stays gv s l s' ->
    gamma (G phi) (phi (point gv s)) s -> gamma (G phi) (phi (point gv s)) s') ->
  post_solution L (forward_system (cfg gv) init ft) phi ->
  invariant_of m (forward_inv m gv (G phi) phi).
Proof.
  intros Hview HG Hinitial Hedge Hstay Hpost.
  pose proof (forward_invariant_sound m gv L G init ft phi
    Hview HG Hinitial Hedge Hstay Hpost) as Hsound.
  constructor.
  - intros s Hs; split; [|apply Hsound].
    + exists s, []; split; [exact Hs|constructor].
    + exists s, []; split; [exact Hs|constructor].
  - intros s l s' [Hreachable Hfact] Hstep.
    assert (Hreachable' : reachable_state m s') by (eapply reachable_state_step; eassumption).
    split; [exact Hreachable'|apply Hsound; exact Hreachable'].
  - intros s [Hreachable Hfact]; exact Hreachable.
Qed.

Lemma history_reachable {S O N E} (m : semantics S O) (gv : graph_view S O N E) s0 es s :
  initial m s0 -> run_edges m gv s0 es s -> reachable_state m s.
Proof.
  intros Hinitial Hhistory.
  destruct (run_edges_exec m gv s0 s es Hhistory) as [tr Hrun].
  exists s0, tr; split; assumption.
Qed.

(** Forward history soundness follows an accumulated prefix while traversing the remaining run. *)
Theorem forward_history_sound {S O N E A} (m : semantics S O) (gv : graph_view S O N E)
    (L : lattice A) (G : (N -> A) -> concretisation A (S * list E)) (init : N -> A)
    (ft : E -> A -> A) (sigma : N -> A) :
  graph_view_laws m gv -> concretisation_laws L (G sigma) ->
  (forall s, initial m s -> gamma (G sigma) (init (point gv s)) (s, nil)) ->
  (forall e s0 es s l s', initial m s0 -> run_edges m gv s0 es s -> step m s l s' ->
    taken gv s l s' e -> gamma (G sigma) (sigma (point gv s)) (s, es) ->
    gamma (G sigma) (ft e (sigma (point gv s))) (s', es ++ [e])) ->
  (forall s0 es s l s', initial m s0 -> run_edges m gv s0 es s -> step m s l s' ->
    stays gv s l s' -> gamma (G sigma) (sigma (point gv s)) (s, es) ->
    gamma (G sigma) (sigma (point gv s)) (s', es)) ->
  post_solution L (forward_system (cfg gv) init ft) sigma ->
  forall s0 es s, initial m s0 -> run_edges m gv s0 es s ->
    gamma (G sigma) (sigma (point gv s)) (s, es).
Proof.
  intros Hview HG Hinitial Hedge Hstay Hpost s0 es s Hs0 Hhistory.
  destruct (proj1 (forward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  assert (Hextend : forall mid fs t, run_edges m gv mid fs t -> forall pre,
    run_edges m gv s0 pre mid -> gamma (G sigma) (sigma (point gv mid)) (mid, pre) ->
    gamma (G sigma) (sigma (point gv t)) (t, pre ++ fs)).
  { intros mid fs t Hsuffix; induction Hsuffix as
      [mid|mid l mid' e fs t Hstep Htaken Hsuffix IH|
       mid l mid' fs t Hstep Hstays Hsuffix IH]; intros pre Hprefix Hfact.
    - rewrite app_nil_r; exact Hfact.
    - assert (Hreachable : reachable_state m mid) by (eapply history_reachable; eassumption).
      destruct (view_taken_edge m gv mid l mid' e Hview Hreachable Hstep Htaken)
        as [He [Hsource Htarget]].
      replace (pre ++ e :: fs) with ((pre ++ [e]) ++ fs) by
        (rewrite <- app_assoc; reflexivity).
      apply IH.
      + eapply run_edges_app; [exact Hprefix|].
        econstructor; [exact Hstep|exact Htaken|constructor].
      + eapply (gamma_monotone HG).
        * rewrite <- Htarget; apply Hflow; exact He.
        * rewrite Hsource; eapply Hedge; eassumption.
    - assert (Hreachable : reachable_state m mid) by (eapply history_reachable; eassumption).
      apply IH.
      + rewrite <- (app_nil_r pre); eapply run_edges_app; [exact Hprefix|].
        eapply run_stay; [exact Hstep|exact Hstays|constructor].
      + rewrite (stays_point Hview mid l mid' Hreachable Hstep Hstays).
        eapply Hstay; eassumption. }
  apply (Hextend s0 es s Hhistory []); [constructor|].
  eapply forward_initial_fact;
    [exact Hview|exact HG|exact Hs0|apply Hinitial; exact Hs0|exact Hpost].
Qed.
