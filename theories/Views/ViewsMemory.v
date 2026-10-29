(** * Memory views and pointer footprints

    Memory views interpret pointer values and retain allocation sites along executions.
    For example, an access of two bytes from a pointer at offset 3 touches offsets 3 and 4.
    Builds on: ViewsSemantics, OrderConcrete and DomainsFootprint. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics.

Local Open Scope Z_scope.

(** Memory operations describe their operands without fixing a client's execution semantics. *)
Inductive mem_op (V T : Type) : Type :=
  | MemLoad (base : V) (off : Z) (width : nat)
  | MemStore (base : V) (off : Z) (width : nat) (src : V)
  | MemCopy (dst src len : V)
  | MemFill (dst len : V)
  | MemAlloc (site : T) (size : V)
  | MemFree (ptr : V).

Arguments MemLoad {V T}.
Arguments MemStore {V T}.
Arguments MemCopy {V T}.
Arguments MemFill {V T}.
Arguments MemAlloc {V T}.
Arguments MemFree {V T}.

(** A memory view identifies the next operation, pointer allocation and byte offset. *)
Record mem_view (S V C L T : Type) : Type := MemView {
  mem_instr : S -> option (mem_op V T);
  loc_of : S -> C -> option L;
  loc_site : S -> L -> option T;
  loc_offset : S -> C -> Z
}.

Arguments MemView {S V C L T}.
Arguments mem_instr {S V C L T}.
Arguments loc_of {S V C L T}.
Arguments loc_site {S V C L T}.
Arguments loc_offset {S V C L T}.

(** An identity's historical allocation site persists even when its storage is freed. *)
Record mem_view_laws {S O V C L T} (m : semantics S O) (mv : mem_view S V C L T) : Prop := {
  site_stable : forall s l s' l0 t, reachable_state m s -> step m s l s' ->
    loc_site mv s l0 = Some t -> loc_site mv s' l0 = Some t
}.

Arguments site_stable {S O V C L T m mv}.

(** Pointer ranges describe possible start offsets with both endpoints included. *)
Record pointer_domain (P C T : Type) : Type := PointerDomain {
  ptr_lat : lattice P;
  ptr_conc : concretisation P C;
  ptr_reach : P -> list (footprint T)
}.

Arguments PointerDomain {P C T}.
Arguments ptr_lat {P C T}.
Arguments ptr_conc {P C T}.
Arguments ptr_reach {P C T}.

(** Shifting start intervals and extending their upper endpoints covers possible access bytes. *)
Definition access_footprint {P C T} (pd : pointer_domain P C T) (p : P) (off : Z) (w : nat) :
    list (footprint T) :=
  map (fun f => Footprint (fp_site f) (fp_lo f + off) (fp_hi f + off + Z.of_nat w))
    (ptr_reach pd p).

(** Every denoted pointer has a start-offset witness at its concrete allocation site. *)
Record pointer_domain_laws {P S O C L V T} (m : semantics S O) (mv : mem_view S V C L T)
    (pd : pointer_domain P C T) : Prop := {
  ptr_reach_sound : forall s p c l t, reachable_state m s -> gamma (ptr_conc pd) p c ->
    loc_of mv s c = Some l -> loc_site mv s l = Some t ->
    exists f, In f (ptr_reach pd p) /\ fp_site f = t /\
      (fp_lo f <= loc_offset mv s c <= fp_hi f)%Z
}.

Arguments ptr_reach_sound {P S O C L V T m mv pd}.

(** Allocation sites persist: a location keeps its site along every run. *)
Theorem loc_site_preserved {S O V C L T} (m : semantics S O) (mv : mem_view S V C L T) :
  mem_view_laws m mv ->
  forall s tr s' l0 t, reachable_state m s -> exec m s tr s' -> loc_site mv s l0 = Some t ->
    loc_site mv s' l0 = Some t.
Proof.
  intros Hlaws s tr s' l0 t Hreachable Hrun.
  revert Hreachable.
  induction Hrun as [s|s l s' tr s'' Hstep Hrun IH]; intros Hreachable Hsite.
  - exact Hsite.
  - apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply site_stable; eassumption.
Qed.

(** Sound pointer facts cover every byte touched by a load or store using the base operand. *)
Theorem access_footprint_sound {P S O C L V T} (m : semantics S O) (mv : mem_view S V C L T)
    (pd : pointer_domain P C T) (valuation : S -> V -> option C) (sigma : V -> P) :
  pointer_domain_laws m mv pd ->
  (forall s x c, reachable_state m s -> valuation s x = Some c ->
     gamma (ptr_conc pd) (sigma x) c) ->
  forall s b off w c l t, reachable_state m s ->
    (mem_instr mv s = Some (MemLoad b off w) \/
     exists src, mem_instr mv s = Some (MemStore b off w src)) ->
    valuation s b = Some c -> loc_of mv s c = Some l -> loc_site mv s l = Some t ->
    covered (access_footprint pd (sigma b) off w) t (loc_offset mv s c + off) w.
Proof.
  intros Hpointer Hvaluation s b off w c l t Hreachable Hoperation Hvalue Hlocation Hsite.
  pose proof (Hvaluation s b c Hreachable Hvalue) as Hconcrete.
  destruct (ptr_reach_sound Hpointer s (sigma b) c l t Hreachable Hconcrete Hlocation Hsite)
    as [f [Hin [Hsitef Hoffset]]].
  intros k Hbyte.
  exists (Footprint (fp_site f) (fp_lo f + off) (fp_hi f + off + Z.of_nat w)).
  split.
  - apply in_map_iff; exists f; split; [reflexivity|exact Hin].
  - cbn; split; [exact Hsitef|lia].
Qed.
