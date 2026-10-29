(** * SSA expression rewriting and behaviour

    Represented equalities preserve SSA expression values and a one-expression region semantics.
    For example, replacing an equivalent partial expression preserves its trap outcome as well.
    Builds on: ViewsSsa, ViewsDominated, ViewsSemantics and RewriteEquality. *)

From Stdlib Require Import List.
From Gaulois.Views Require Import ViewsSemantics ViewsSsa ViewsDominated.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph.
Import List.ListNotations.

(** The current SSA environment and its operator evaluator interpret Rewrite expressions. *)
Definition ssa_rw_semantics {S O N E V K C Sort} (sv : ssa_view S O N E V K C) (s : S) :
    rw_semantics K Sort V C := RwSemantics K Sort V C (val sv s) (op_eval sv).

(** Two terms in a sound class preserve a successful SSA expression value. *)
Theorem ssa_rewrite_value {S O N E V K C Sort H} (m : semantics S O)
    (sv : ssa_view S O N E V K C) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (root : rw_id) (input output : rw_term K Sort V) (s : S) (c : C) :
  ssa_view_laws m sv -> strict_ssa_laws m sv -> reachable_state m s ->
  admissible (ssa_rw_semantics sv s) ->
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  rw_denote (ssa_rw_semantics sv s) input = Some c ->
  rw_denote (ssa_rw_semantics sv s) output = Some c.
Proof.
  intros Hview Hstrict Hreachable Hadmissible Hrules Hgraph Hinput Houtput Hvalue.
  pose proof (rw_equal_sound sig admissible rules Hrules input output
    (Hgraph root input output Hinput Houtput) (ssa_rw_semantics sv s) Hadmissible) as Hequal.
  now rewrite <- Hequal.
Qed.

(** A region retains its SSA state and distinguishes unevaluated from undefined evaluation. *)
Definition ssa_region_state (S C : Type) := (S * option (option C))%type.

(** A pure region emits one successful value or silently records an undefined result. *)
Definition ssa_region_semantics {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (expr : rw_term K Sort V) : semantics (ssa_region_state S C) C :=
  Semantics (fun _ => True)
    (fun before events after =>
      snd before = None /\ fst after = fst before /\
      snd after = Some (rw_denote (ssa_rw_semantics sv (fst before)) expr) /\
      events = match rw_denote (ssa_rw_semantics sv (fst before)) expr with
               | Some c => [c]
               | None => []
               end).

(** Successful regions terminate normally and undefined regions trap, without a resource stop. *)
Definition ssa_region_endings {S C} : endings (ssa_region_state S C) :=
  Endings (fun st => exists c, snd st = Some (Some c)) (fun st => snd st = Some None)
    (fun _ => False).

(** Related regions have identical states with an admissible current SSA interpretation. *)
Definition ssa_region_relation {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (a b : ssa_region_state S C) : Prop :=
  a = b /\ admissible (ssa_rw_semantics sv (fst a)).

Lemma ssa_region_step_agrees {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V)
    (a b : ssa_region_state S C) (events : list C) :
  rw_equiv admissible input output -> admissible (ssa_rw_semantics sv (fst a)) ->
  (step (ssa_region_semantics sv input) a events b <->
    step (ssa_region_semantics sv output) a events b).
Proof.
  intros Hequal Hadmissible; cbv beta iota zeta delta [ssa_region_semantics step].
  now rewrite (Hequal _ Hadmissible).
Qed.

Lemma ssa_region_running_agrees {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V)
    (a : ssa_region_state S C) :
  rw_equiv admissible input output -> admissible (ssa_rw_semantics sv (fst a)) ->
  (running (ssa_region_semantics sv input) a <-> running (ssa_region_semantics sv output) a).
Proof.
  intros Hequal Hadmissible; split; intros [events [b Hstep]]; exists events, b.
  - apply (ssa_region_step_agrees sv admissible input output a b events Hequal Hadmissible).
    exact Hstep.
  - apply (ssa_region_step_agrees sv admissible input output a b events Hequal Hadmissible).
    exact Hstep.
Qed.

(** Equivalent expressions give a direct bisimulation including traps and stuck endpoints. *)
Theorem ssa_region_bisimulation {S O N E V K C Sort} (sv : ssa_view S O N E V K C)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V) :
  rw_equiv admissible input output ->
  bisimulation (ssa_region_semantics sv input) ssa_region_endings
    (ssa_region_semantics sv output) ssa_region_endings (ssa_region_relation sv admissible).
Proof.
  intro Hequal; constructor.
  - intros a b k [-> Hadmissible]; destruct k; cbn [ends_as]; try reflexivity.
    unfold stuck; now rewrite (ssa_region_running_agrees sv admissible input output b
      Hequal Hadmissible).
  - intros a b events after [-> Hadmissible] Hstep; exists after; split.
    + apply (ssa_region_step_agrees sv admissible input output b after events
        Hequal Hadmissible); exact Hstep.
    + split; [reflexivity|].
      destruct Hstep as [_ [Hstate _]]; now rewrite Hstate.
  - intros a b events after [-> Hadmissible] Hstep; exists after; split.
    + apply (ssa_region_step_agrees sv admissible input output b after events
        Hequal Hadmissible); exact Hstep.
    + split; [reflexivity|].
      destruct Hstep as [_ [Hstate _]]; now rewrite Hstate.
Qed.

(** Rewriting within a sound class preserves the pure region's complete observable behaviour. *)
Theorem ssa_region_rewrite_behaviour {S O N E V K C Sort H} (sv : ssa_view S O N E V K C)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (root : rw_id)
    (input output : rw_term K Sort V) (s : S) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  admissible (ssa_rw_semantics sv s) ->
  same_behaviour (ssa_region_semantics sv input) ssa_region_endings (s, None)
    (ssa_region_semantics sv output) ssa_region_endings (s, None).
Proof.
  intros Hrules Hgraph Hinput Houtput Hadmissible; eapply bisimilar_same_behaviour.
  - apply ssa_region_bisimulation.
    exact (rw_equal_sound sig admissible rules Hrules input output
      (Hgraph root input output Hinput Houtput)).
  - split; [reflexivity|exact Hadmissible].
Qed.

(** Clients connect expression equivalence to a whole-program replacement bisimulation. *)
Record rw_replacement_laws {S1 S2 O K Sort V C} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    (admissible : rw_semantics K Sort V C -> Prop) (input output : rw_term K Sort V) : Prop := {
  rw_replacement_bisim : rw_equiv admissible input output -> bisimulation m1 e1 m2 e2 R
}.

(** A client's replacement law transfers sound class equality to whole-program behaviour. *)
Theorem rw_replacement_behaviour {S1 S2 O K Sort V H C} (m1 : semantics S1 O) (e1 : endings S1)
    (m2 : semantics S2 O) (e2 : endings S2) (R : S1 -> S2 -> Prop)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (root : rw_id)
    (input output : rw_term K Sort V) (s : S1) (t : S2) :
  Forall (rw_rule_sound sig admissible) rules -> rw_graph_sound sig admissible rules g ->
  rw_represents g root input -> rw_represents g root output ->
  rw_replacement_laws m1 e1 m2 e2 R admissible input output -> R s t ->
  same_behaviour m1 e1 s m2 e2 t.
Proof.
  intros Hrules Hgraph Hinput Houtput Hreplacement Hrelated.
  apply (bisimilar_same_behaviour m1 e1 m2 e2 R s t); [|exact Hrelated].
  apply (rw_replacement_bisim _ _ _ _ _ _ _ _ Hreplacement).
  exact (rw_equal_sound sig admissible rules Hrules input output
    (Hgraph root input output Hinput Houtput)).
Qed.
