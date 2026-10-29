(** * Instruction effects and silent runs

    Conservative flags describe observations, heap dependence and frame changes.
    For example, a finite run through non-observing instructions has an empty trace.
    Builds on: ViewsSemantics. *)

From Stdlib Require Import List Arith.
From Gaulois.Views Require Import ViewsSemantics.

(** Effect flags over-approximate an instruction's possible dependencies and actions. *)
Record effects (I : Type) : Type := Effects {
  reads : I -> bool;
  writes : I -> bool;
  may_trap : I -> bool;
  may_diverge : I -> bool;
  may_stop : I -> bool;
  allocates : I -> bool;
  frees : I -> bool;
  calls : I -> bool;
  observes : I -> bool
}.

Arguments Effects {I}.
Arguments reads {I}.
Arguments writes {I}.
Arguments may_trap {I}.
Arguments may_diverge {I}.
Arguments may_stop {I}.
Arguments allocates {I}.
Arguments frees {I}.
Arguments calls {I}.
Arguments observes {I}.

(** An effects view exposes instructions, heap images and frame depth. *)
Record effects_view (S I H : Type) : Type := EffectsView {
  instr_at : S -> option I;
  heap : S -> H;
  heap_agree : S -> S -> Prop;
  depth : S -> nat
}.

Arguments EffectsView {S I H}.
Arguments instr_at {S I H}.
Arguments heap {S I H}.
Arguments heap_agree {S I H}.
Arguments depth {S I H}.

(** Divergence within a frame never crosses below its depth after a transition. *)
CoInductive diverges_within {S O} (m : semantics S O) (depth : S -> nat) (d : nat) :
    S -> Prop :=
  | within_step : forall s l s', step m s l s' -> d <= depth s' ->
      diverges_within m depth d s' -> diverges_within m depth d s.

Arguments within_step {S O m depth d}.

(** Effects laws connect flags to reachable transitions, endings and heap independence. *)
Record effects_laws {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) : Prop := {
  silent : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    observes ef i = false -> l = nil;
  trap_covered : forall s i, reachable_state m s -> instr_at ev s = Some i -> trapped en s ->
    may_trap ef i = true;
  stop_covered : forall s i, reachable_state m s -> instr_at ev s = Some i -> stopped en s ->
    may_stop ef i = true;
  heap_frame : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    writes ef i = false -> allocates ef i = false -> frees ef i = false -> heap ev s' = heap ev s;
  reads_frame : forall s l s' t i, reachable_state m s -> instr_at ev s = Some i ->
    step m s l s' -> reads ef i = false -> heap_agree ev s t ->
    exists t', step m t l t' /\ heap_agree ev s' t';
  trap_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    instr_at ev s = Some i -> instr_at ev t = Some i -> reads ef i = false ->
    heap_agree ev s t -> (trapped en s <-> trapped en t);
  stop_frame : forall s t i, reachable_state m s -> reachable_state m t ->
    instr_at ev s = Some i -> instr_at ev t = Some i -> reads ef i = false ->
    heap_agree ev s t -> (stopped en s <-> stopped en t);
  frame_frame : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    calls ef i = false -> depth ev s' = depth ev s;
  call_returns : forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    calls ef i = true -> may_diverge ef i = false -> depth ev s' = Datatypes.S (depth ev s) ->
    ~ diverges_within m (depth ev) (depth ev s') s'
}.

Arguments silent {S O I H m en ef ev}.
Arguments trap_covered {S O I H m en ef ev}.
Arguments stop_covered {S O I H m en ef ev}.
Arguments heap_frame {S O I H m en ef ev}.
Arguments reads_frame {S O I H m en ef ev}.
Arguments trap_frame {S O I H m en ef ev}.
Arguments stop_frame {S O I H m en ef ev}.
Arguments frame_frame {S O I H m en ef ev}.
Arguments call_returns {S O I H m en ef ev}.

(** A restricted run whose running states have non-observing instructions emits no event. *)
Theorem silent_exec_in {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) (P : S -> Prop) (s s' : S) (tr : list O) :
  effects_laws m en ef ev -> reachable_state m s -> exec_in m P s tr s' ->
  (forall t, P t -> running m t -> exists i, instr_at ev t = Some i /\ observes ef i = false) ->
  tr = nil.
Proof.
  intros Hlaws Hreachable Hrun Hquiet; revert Hreachable.
  induction Hrun as [s HP|s l s' tr t HP Hstep Hrun IH]; intro Hreachable.
  - reflexivity.
  - destruct (Hquiet s HP (ex_intro _ l (ex_intro _ s' Hstep))) as [i [Hinstr Hsilent]].
    rewrite (silent Hlaws s l s' i Hreachable Hinstr Hstep Hsilent).
    cbn; apply IH; eapply reachable_state_step; eassumption.
Qed.
