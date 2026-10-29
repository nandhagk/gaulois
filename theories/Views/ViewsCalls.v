(** * Calls, resolver graphs and suspended frames

    Call views list functions and expose the current function and suspended callers.
    For example, a recursive push adds an edge from a function to itself.
    Builds on: ViewsSemantics and GraphCore. *)

From Stdlib Require Import List.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics.
Import List.ListNotations.

(** The finite inventory covers every pushed frame, including callbacks and external frames. *)
Record calls_view (S F P : Type) : Type := CallsView {
  functions : list F;
  roots : list F;
  sites_of : F -> list P;
  caller_of : P -> F;
  here : S -> F;
  frames : S -> list (F * P)
}.

Arguments CallsView {S F P}.
Arguments functions {S F P}.
Arguments roots {S F P}.
Arguments sites_of {S F P}.
Arguments caller_of {S F P}.
Arguments here {S F P}.
Arguments frames {S F P}.

(** Active functions are listed from the innermost function to the outermost caller. *)
Definition active {S F P} (cv : calls_view S F P) (s : S) : list F :=
  here cv s :: map fst (frames cv s).

(** A call edge retains both its call-site identity and its resolved target. *)
Record call_edge (F P : Type) : Type := CallEdge {
  edge_site : P;
  edge_callee : F
}.

Arguments CallEdge {F P}.
Arguments edge_site {F P}.
Arguments edge_callee {F P}.

(** The call graph enumerates resolver targets in function-site and resolver-list order. *)
Definition call_graph {S F P} (cv : calls_view S F P) (resolve : P -> list F) :
    Graph.t F (call_edge F P) :=
  {| Graph.entries := roots cv;
     Graph.nodes := functions cv;
     Graph.out := fun f => flat_map (fun p => map (CallEdge p) (resolve p)) (sites_of cv f);
     Graph.source := fun e => caller_of cv (edge_site e);
     Graph.target := edge_callee |}.

(** View laws require every actual push, callbacks included, to be listed and resolved. *)
Record calls_view_laws {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) : Prop := {
  sites_caller : forall f p, In p (sites_of cv f) -> caller_of cv p = f;
  initial_roots : forall s, initial m s -> In (here cv s) (roots cv) /\ frames cv s = nil;
  frames_listed : forall s, reachable_state m s -> forall f, In f (active cv s) ->
    In f (functions cv);
  step_shape : forall s l s', reachable_state m s -> step m s l s' ->
    (here cv s' = here cv s /\ frames cv s' = frames cv s) \/
    (exists p, In p (sites_of cv (here cv s)) /\ In (here cv s') (resolve p) /\
       frames cv s' = (here cv s, p) :: frames cv s) \/
    (exists f p, frames cv s = (f, p) :: frames cv s' /\ here cv s' = f)
}.

Arguments sites_caller {S O F P m cv resolve}.
Arguments initial_roots {S O F P m cv resolve}.
Arguments frames_listed {S O F P m cv resolve}.
Arguments step_shape {S O F P m cv resolve}.

(** A resolved site contributes exactly its tagged target edge to its caller's out-list. *)
Lemma call_graph_edge {S F P} (cv : calls_view S F P) resolve f p g :
  In p (sites_of cv f) -> In g (resolve p) ->
  In (CallEdge p g) (Graph.out (call_graph cv resolve) f).
Proof.
  intros Hsite Htarget; apply in_flat_map; exists p; split; [exact Hsite|].
  apply in_map; exact Htarget.
Qed.

(** The call graph of a well-formed calls view is a well-formed graph. *)
Theorem call_graph_wf {S F P} (cv : calls_view S F P) (resolve : P -> list F) :
  NoDup (functions cv) -> incl (roots cv) (functions cv) ->
  (forall f p, In p (sites_of cv f) -> caller_of cv p = f /\ In f (functions cv)) ->
  (forall p g, In g (resolve p) -> In g (functions cv)) ->
  graph_wf (call_graph cv resolve).
Proof.
  intros Hnodes Hroots Hsites Hresolve; constructor.
  - exact Hnodes.
  - exact Hroots.
  - intros f e Hedge; apply in_flat_map in Hedge.
    destruct Hedge as [p [Hsite Hedge]]; apply in_map_iff in Hedge.
    destruct Hedge as [g [<- Htarget]]; exact (proj1 (Hsites f p Hsite)).
  - intros f e Hf Hedge; apply in_flat_map in Hedge.
    destruct Hedge as [p [Hsite Hedge]]; apply in_map_iff in Hedge.
    destruct Hedge as [g [<- Htarget]]; exact (Hresolve p g Htarget).
Qed.

(** Each suspended caller is linked to the callee directly above it by its resolver. *)
Fixpoint frames_linked {S F P} (cv : calls_view S F P) (resolve : P -> list F)
    (callee : F) (stack : list (F * P)) : Prop :=
  match stack with
  | [] => True
  | (f, p) :: rest => caller_of cv p = f /\ In p (sites_of cv f) /\
      In callee (resolve p) /\ frames_linked cv resolve f rest
  end.

Lemma frames_linked_step {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s l s', reachable_state m s -> step m s l s' ->
  frames_linked cv resolve (here cv s) (frames cv s) ->
  frames_linked cv resolve (here cv s') (frames cv s').
Proof.
  intros Hlaws s l s' Hreachable Hstep Hlinked.
  destruct (step_shape Hlaws s l s' Hreachable Hstep) as
    [[Hhere Hframes]|[[p [Hsite [Htarget Hframes]]]|[f [p [Hframes Hhere]]]]].
  - rewrite Hhere, Hframes; exact Hlinked.
  - rewrite Hframes; cbn; split; [eapply sites_caller; eassumption|].
    split; [exact Hsite|split; assumption].
  - rewrite Hframes in Hlinked; cbn in Hlinked; rewrite Hhere.
    exact (proj2 (proj2 (proj2 Hlinked))).
Qed.

Lemma frames_linked_exec {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s tr t, exec m s tr t -> reachable_state m s ->
  frames_linked cv resolve (here cv s) (frames cv s) ->
  frames_linked cv resolve (here cv t) (frames cv t).
Proof.
  intros Hlaws s tr t Hrun; induction Hrun as [s|s l s' tr t Hstep Hrun IH].
  - intros Hreachable Hlinked; exact Hlinked.
  - intros Hreachable Hlinked; apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply frames_linked_step; eassumption.
Qed.

(** Every reachable stack retains the links established by its call pushes. *)
Lemma reachable_frames_linked {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s, reachable_state m s ->
  frames_linked cv resolve (here cv s) (frames cv s).
Proof.
  intros Hlaws s [s0 [tr [Hinitial Hrun]]].
  eapply frames_linked_exec; [exact Hlaws|exact Hrun| |].
  - exists s0, []; split; [exact Hinitial|constructor].
  - rewrite (proj2 (initial_roots Hlaws s0 Hinitial)); exact I.
Qed.

Lemma active_reachable_step {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s l s', reachable_state m s -> step m s l s' ->
  (forall f, In f (active cv s) -> reachable (call_graph cv resolve) f) ->
  forall f, In f (active cv s') -> reachable (call_graph cv resolve) f.
Proof.
  intros Hlaws s l s' Hreachable Hstep Hactive f Hin.
  unfold active in Hin.
  destruct (step_shape Hlaws s l s' Hreachable Hstep) as
    [[Hhere Hframes]|[[p [Hsite [Htarget Hframes]]]|[g [p [Hframes Hhere]]]]].
  - rewrite Hhere, Hframes in Hin; apply Hactive; exact Hin.
  - rewrite Hframes in Hin; cbn in Hin; destruct Hin as [<-|Hin].
    + pose proof (sites_caller Hlaws _ _ Hsite) as Hcaller.
      change (reachable (call_graph cv resolve)
        (Graph.target (call_graph cv resolve) (CallEdge p (here cv s')))).
      apply reachable_step.
      * cbn; rewrite Hcaller; apply Hactive; left; reflexivity.
      * cbn; rewrite Hcaller; apply call_graph_edge; assumption.
    + apply Hactive; exact Hin.
  - rewrite Hhere in Hin; apply Hactive; unfold active; rewrite Hframes; cbn.
    right; exact Hin.
Qed.

Lemma active_reachable_exec {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s tr t, exec m s tr t -> reachable_state m s ->
  (forall f, In f (active cv s) -> reachable (call_graph cv resolve) f) ->
  forall f, In f (active cv t) -> reachable (call_graph cv resolve) f.
Proof.
  intros Hlaws s tr t Hrun; induction Hrun as [s|s l s' tr t Hstep Hrun IH].
  - intros Hreachable Hactive; exact Hactive.
  - intros Hreachable Hactive; apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply active_reachable_step; eassumption.
Qed.

(** Every function active in a reachable state is reachable from a call-graph root. *)
Theorem active_reachable_in_call_graph {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) :
  calls_view_laws m cv resolve ->
  forall s, reachable_state m s -> forall f, In f (active cv s) ->
    reachable (call_graph cv resolve) f.
Proof.
  intros Hlaws s [s0 [tr [Hinitial Hrun]]].
  eapply active_reachable_exec; [exact Hlaws|exact Hrun| |].
  - exists s0, []; split; [exact Hinitial|constructor].
  - intros f Hin; unfold active in Hin.
    destruct (initial_roots Hlaws s0 Hinitial) as [Hroot Hframes].
    rewrite Hframes in Hin; cbn in Hin; destruct Hin as [<-|[]].
    apply reachable_entry; exact Hroot.
Qed.
