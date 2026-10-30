(** * Ordered memory effects

    Ordered effects connect each graph edge to one trace of memory snapshots and observations.
    For example, a read followed by a write observes the snapshot before that write.
    Builds on: ViewsSemantics, ViewsGraph and DomainsFootprint. *)

From Stdlib Require Import List ZArith Arith.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph.
Import List.ListNotations.

(** A scope covers bounded site ranges or every byte, including lifetime changes. *)
Inductive memory_scope (T : Type) : Type :=
  | MemoryRegions (fs : list (footprint T))
  | MemoryAll.

Arguments MemoryRegions {T}.
Arguments MemoryAll {T}.

(** Scope membership observes one byte of a historical allocation site. *)
Definition memory_scope_covers {T} (scope : memory_scope T) (t : T) (o : Z) : Prop :=
  match scope with
  | MemoryRegions fs => covered fs t o 1
  | MemoryAll => True
  end.

(** Effects distinguish pure reads from definitions, calls and barriers. *)
Inductive memory_effect (T : Type) : Type :=
  | MemoryRead (reads : memory_scope T)
  | MemoryWrite (writes : memory_scope T)
  | MemoryReadWrite (reads writes : memory_scope T)
  | MemoryCall (reads writes : memory_scope T)
  | MemoryBarrier.

Arguments MemoryRead {T}.
Arguments MemoryWrite {T}.
Arguments MemoryReadWrite {T}.
Arguments MemoryCall {T}.
Arguments MemoryBarrier {T}.

(** Every barrier observes all memory, independently of any bounded footprint. *)
Definition effect_reads {T} (a : memory_effect T) : memory_scope T :=
  match a with
  | MemoryRead r => r
  | MemoryWrite _ => MemoryRegions []
  | MemoryReadWrite r _ => r
  | MemoryCall r _ => r
  | MemoryBarrier => MemoryAll
  end.

(** Calls and read/write effects expose their write side separately from their reads. *)
Definition effect_writes {T} (a : memory_effect T) : memory_scope T :=
  match a with
  | MemoryRead _ => MemoryRegions []
  | MemoryWrite w => w
  | MemoryReadWrite _ w => w
  | MemoryCall _ w => w
  | MemoryBarrier => MemoryAll
  end.

(** Only a pure read preserves the incoming structural version. *)
Definition effect_is_def {T} (a : memory_effect T) : bool :=
  match a with
  | MemoryRead _ => false
  | _ => true
  end.

(** The client supplies ordered effects, historical sites, snapshots and actual reads. *)
Record memory_effect_view (S O N E T B L : Type) : Type := MemoryEffectView {
  effect_graph : graph_view S O N E;
  edge_effects : E -> list (memory_effect T);
  effect_snapshot : S -> B;
  effect_site : B -> L -> option T;
  effect_byte : B -> L -> Z -> option nat;
  effect_step : B -> memory_effect T -> B -> Prop;
  effect_read : B -> memory_effect T -> L -> Z -> Prop;
  transition_read : S -> list O -> S -> L -> Z -> Prop
}.

Arguments MemoryEffectView {S O N E T B L}.
Arguments effect_graph {S O N E T B L}.
Arguments edge_effects {S O N E T B L}.
Arguments effect_snapshot {S O N E T B L}.
Arguments effect_site {S O N E T B L}.
Arguments effect_byte {S O N E T B L}.
Arguments effect_step {S O N E T B L}.
Arguments effect_read {S O N E T B L}.
Arguments transition_read {S O N E T B L}.

(** A trace executes the effects in their edge order. *)
Inductive effect_trace {S O N E T B L}
    (v : memory_effect_view S O N E T B L) : B -> list (memory_effect T) -> B -> Prop :=
  | effect_trace_nil : forall b, effect_trace v b [] b
  | effect_trace_cons : forall b a b' rest b'',
      effect_step v b a b' -> effect_trace v b' rest b'' ->
      effect_trace v b (a :: rest) b''.

(** The recorded states are exactly the incoming snapshots of the ordered effects. *)
Inductive effect_trace_states {S O N E T B L}
    (v : memory_effect_view S O N E T B L) :
    B -> list (memory_effect T) -> list B -> B -> Prop :=
  | effect_states_nil : forall b, effect_trace_states v b [] [] b
  | effect_states_cons : forall b a b' rest states b'',
      effect_step v b a b' -> effect_trace_states v b' rest states b'' ->
      effect_trace_states v b (a :: rest) (b :: states) b''.

(** All reads of a transition share one snapshot trace whose steps preserve historical sites. *)
Record memory_effect_laws {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) : Prop := {
  effect_view_laws : graph_view_laws m (effect_graph v);
  effect_no_stays : forall s tr s', ~ stays (effect_graph v) s tr s';
  effect_step_trace : forall s tr s' e, reachable_state m s -> step m s tr s' ->
    taken (effect_graph v) s tr s' e -> exists states,
    effect_trace_states v (effect_snapshot v s) (edge_effects v e) states
      (effect_snapshot v s') /\
    forall l o, transition_read v s tr s' l o -> exists i b a,
      nth_error states i = Some b /\ nth_error (edge_effects v e) i = Some a /\
      effect_read v b a l o;
  effect_read_covered : forall b a l o t, effect_read v b a l o ->
    effect_site v b l = Some t -> memory_scope_covers (effect_reads a) t o;
  effect_site_stable : forall b a b' l t, effect_step v b a b' ->
    effect_site v b l = Some t -> effect_site v b' l = Some t;
  effect_byte_frame : forall b a b' l t o, effect_step v b a b' ->
    effect_site v b l = Some t -> effect_byte v b' l o <> effect_byte v b l o ->
    memory_scope_covers (effect_writes a) t o
}.

Arguments effect_view_laws {S O N E T B L m v}.
Arguments effect_no_stays {S O N E T B L m v}.
Arguments effect_step_trace {S O N E T B L m v}.
Arguments effect_read_covered {S O N E T B L m v}.
Arguments effect_site_stable {S O N E T B L m v}.
Arguments effect_byte_frame {S O N E T B L m v}.

Lemma effect_byte_eq_dec (x y : option nat) : {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Qed.

Lemma effect_trace_states_byte_covered {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) (Hlaws : memory_effect_laws m v)
    b effects states b' :
  effect_trace_states v b effects states b' ->
  forall l t o, effect_site v b l = Some t ->
    effect_byte v b' l o <> effect_byte v b l o ->
    exists a, In a effects /\ memory_scope_covers (effect_writes a) t o.
Proof.
  intro Htrace; induction Htrace as [b|b a middle rest states last Hstep Htrace IH];
    intros l t o Hsite Hchanged.
  - exfalso; apply Hchanged; reflexivity.
  - destruct (effect_byte_eq_dec (effect_byte v middle l o) (effect_byte v b l o))
      as [Hequal|Hdifferent].
    + destruct (IH l t o (effect_site_stable Hlaws b a middle l t Hstep Hsite))
        as [writer [Hin Hcovers]].
      * rewrite Hequal; exact Hchanged.
      * exists writer; split; [right; exact Hin|exact Hcovers].
    + exists a; split; [left; reflexivity|].
      eapply effect_byte_frame; eassumption.
Qed.

(** Every changed byte of an existing identity belongs to a write in the actual edge trace. *)
Theorem effect_transition_byte_covered {S O N E T B L} (m : semantics S O)
    (v : memory_effect_view S O N E T B L) :
  memory_effect_laws m v ->
  forall s tr s' e l t o, reachable_state m s -> step m s tr s' ->
    taken (effect_graph v) s tr s' e -> effect_site v (effect_snapshot v s) l = Some t ->
    effect_byte v (effect_snapshot v s') l o <> effect_byte v (effect_snapshot v s) l o ->
    exists a, In a (edge_effects v e) /\ memory_scope_covers (effect_writes a) t o.
Proof.
  intros Hlaws s tr s' e l t o Hreachable Hstep Htaken Hsite Hchanged.
  destruct (effect_step_trace Hlaws s tr s' e Hreachable Hstep Htaken)
    as [states [Htrace Hreads]].
  eapply effect_trace_states_byte_covered; eassumption.
Qed.
