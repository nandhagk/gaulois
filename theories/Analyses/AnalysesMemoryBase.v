(** * Validated ranges, dead stores and allocation epochs

    Memory analyses combine byte-range facts with local semantic laws and retain historical
    allocation identities when storage is freed.
    For example, freeing one allocation and allocating again at its site cannot revive it.
    Builds on: DomainsFootprint, ViewsForward, ViewsAgreement and AnalysesNumbering. *)

From Stdlib Require Import List Bool ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsForward ViewsAgreement ViewsSsa
  ViewsDominated.
From Gaulois.Analyses Require Import AnalysesNumbering.
Import List.ListNotations.

(** * Access validation *)

(** A barrier invalidates previous access guarantees before the edge's validations are added. *)
Record barrier_view (S O N E T : Type) : Type := BarrierView {
  bgraph : graph_view S O N E;
  validates : E -> list (footprint T);
  barrier : E -> bool;
  accessible : S -> T -> Z -> nat -> Prop
}.

Arguments BarrierView {S O N E T}.
Arguments bgraph {S O N E T}.
Arguments validates {S O N E T}.
Arguments barrier {S O N E T}.
Arguments accessible {S O N E T}.

(** Access laws justify validation, nonbarrier transport, subranges and bytewise aggregation. *)
Record barrier_laws {S O N E T} (m : semantics S O) (bv : barrier_view S O N E T) : Prop := {
  b_view : graph_view_laws m (bgraph bv);
  b_no_stays : forall s l s', ~ stays (bgraph bv) s l s';
  validates_accessible : forall s l s' e f, reachable_state m s -> step m s l s' ->
    taken (bgraph bv) s l s' e -> In f (validates bv e) ->
    accessible bv s' (fp_site f) (fp_lo f) (Z.to_nat (fp_hi f - fp_lo f));
  accessible_persists : forall s l s' e t o w, reachable_state m s -> step m s l s' ->
    taken (bgraph bv) s l s' e -> barrier bv e = false -> accessible bv s t o w ->
    accessible bv s' t o w;
  accessible_sub : forall s t o w o' w', reachable_state m s -> accessible bv s t o w ->
    (o <= o')%Z -> (o' + Z.of_nat w' <= o + Z.of_nat w)%Z -> accessible bv s t o' w';
  accessible_bytes : forall s t o w, reachable_state m s -> (0 < w)%nat ->
    (forall k, (o <= k < o + Z.of_nat w)%Z -> accessible bv s t k 1) ->
    accessible bv s t o w
}.

Arguments Build_barrier_laws {S O N E T m bv}.
Arguments b_view {S O N E T m bv}.
Arguments b_no_stays {S O N E T m bv}.
Arguments validates_accessible {S O N E T m bv}.
Arguments accessible_persists {S O N E T m bv}.
Arguments accessible_sub {S O N E T m bv}.
Arguments accessible_bytes {S O N E T m bv}.

(** Entry facts are empty; a barrier clears old facts before inserting current validations. *)
Definition validated_system {S O N E T} (ET : encoding T) (bv : barrier_view S O N E T) :
  System.t N (dense_constraint N E) (range_must ET) :=
  forward_system (cfg (bgraph bv)) (fun _ => range_reached ET nil)
    (fun e a => range_add ET (validates bv e)
      (if barrier bv e then range_reached ET nil else a)).

Definition validated_gamma {S O N E T} (ET : encoding T) (bv : barrier_view S O N E T) :
    concretisation (range_must ET) S :=
  {| gamma := fun a s => gamma range_must_gamma a (fun t k => accessible bv s t k 1) |}.

Lemma validated_gamma_laws {S O N E T} (ET : encoding T) (bv : barrier_view S O N E T) :
  concretisation_laws (range_must_lattice ET) (validated_gamma ET bv).
Proof.
  constructor; intros a b s Hle Hgamma.
  exact (gamma_monotone (range_must_gamma_laws ET) a b _ Hle Hgamma).
Qed.

Lemma validated_footprint_byte {S O N E T} (m : semantics S O)
    (bv : barrier_view S O N E T) (laws : barrier_laws m bv) s l s' e f k :
  reachable_state m s -> step m s l s' -> taken (bgraph bv) s l s' e ->
  In f (validates bv e) -> (fp_lo f <= k < fp_hi f)%Z ->
  accessible bv s' (fp_site f) k 1.
Proof.
  intros Hreach Hstep Htaken Hin Hbounds.
  eapply (accessible_sub laws).
  - eapply reachable_state_step; eassumption.
  - eapply (validates_accessible laws); eassumption.
  - lia.
  - rewrite Z2Nat.id by lia; cbn; lia.
Qed.

Lemma validated_transfer_sound {S O N E T} (m : semantics S O) (ET : encoding T)
    (bv : barrier_view S O N E T) (laws : barrier_laws m bv) a e s l s' :
  reachable_state m s -> step m s l s' -> taken (bgraph bv) s l s' e ->
  gamma (validated_gamma ET bv) a s ->
  gamma (validated_gamma ET bv)
    (range_add ET (validates bv e) (if barrier bv e then range_reached ET [] else a)) s'.
Proof.
  intros Hreach Hstep Htaken Hgamma; apply range_add_gamma.
  - destruct (barrier bv e) eqn:Hbarrier.
    + apply (gamma_top_full (range_must_gamma_top_full ET)).
    + destruct a as [F|]; [|contradiction].
      intros t k Hwritten; eapply (accessible_persists laws); try eassumption.
      exact (Hgamma t k Hwritten).
  - intros f k Hin Hbounds; eapply validated_footprint_byte; eassumption.
Qed.

(** A positive-width validated range is accessible at every reachable state. *)
Theorem validated_sound {S O N E T} (m : semantics S O) (ET : encoding T)
    (bv : barrier_view S O N E T) (sigma : N -> range_must ET) :
  barrier_laws m bv ->
  post_solution (range_must_lattice ET) (validated_system ET bv) sigma ->
  forall s t o w, reachable_state m s -> (0 < w)%nat ->
    range_covers (sigma (point (bgraph bv) s)) t o w -> accessible bv s t o w.
Proof.
  intros laws Hpost.
  assert (Hsound : forall s, reachable_state m s ->
    gamma (validated_gamma ET bv) (sigma (point (bgraph bv) s)) s).
  { eapply (forward_invariant_sound m (bgraph bv) (range_must_lattice ET)
      (fun _ => validated_gamma ET bv)); [exact (b_view laws)| | | | |exact Hpost].
    - apply validated_gamma_laws.
    - intros s Hinitial; apply (gamma_top_full (range_must_gamma_top_full ET)).
    - intros e s l s' Hreach Hstep Htaken Hgamma.
      eapply validated_transfer_sound; eassumption.
    - intros s l s' Hreach Hstep Hstay; exfalso; exact (b_no_stays laws s l s' Hstay). }
  intros s t o w Hreach Hpositive Hcovers.
  apply (accessible_bytes laws s t o w Hreach Hpositive).
  intros k Hk.
  exact (range_covers_sound ET _ t o w _ (Hsound s Hreach) Hcovers k Hk).
Qed.

(** * Backward dead-byte coverage *)

(** Store observations describe definite overwrites, possible reads and outside-range agreement. *)
Record store_view (S O N E T : Type) (ET : encoding T) : Type := StoreView {
  sgraph : graph_view S O N E;
  overwrites : E -> list (footprint T);
  mreads : E -> list (footprint T);
  sagree : agreement (range_must ET) S;
  store_boundary : N -> canonical_footprints ET
}.

Arguments StoreView {S O N E T ET}.
Arguments sgraph {S O N E T ET}.
Arguments overwrites {S O N E T ET}.
Arguments mreads {S O N E T ET}.
Arguments sagree {S O N E T ET}.
Arguments store_boundary {S O N E T ET}.

(** Reads remove old-byte dependencies after adding definite writes, so overlapping reads win. *)
Definition dead_store_transfer {S O N E T} (ET : encoding T) (sv : store_view S O N E T ET)
    (e : E) (a : range_must ET) : range_must ET :=
  range_remove ET (mreads sv e) (range_add ET (overwrites sv e) a).

(** Every listed node is seeded with its prepared reached boundary. *)
Definition dead_store_system {S O N E T} (ET : encoding T) (sv : store_view S O N E T ET) :
  System.t N (dense_constraint N E) (range_must ET) :=
  backward_system (cfg (sgraph sv))
    (fun n => Reached (store_boundary sv n)) (dead_store_transfer ET sv).

(** Local step laws apply to all assignments reached at listed graph nodes. *)
Definition dead_store_reached {S O N E T} (ET : encoding T)
    (sv : store_view S O N E T ET) (sigma : N -> range_must ET) : Prop :=
  forall n, In n (Graph.nodes (cfg (sgraph sv))) -> sigma n <> Unreached.

(** A reached transfer keeps exactly the nonread bytes in the old fact or definite writes. *)
Lemma dead_store_transfer_written {S O N E T} (ET : encoding T)
    (sv : store_view S O N E T ET) e a t k :
  a <> Unreached ->
  (range_written (dead_store_transfer ET sv e a) t k <->
    (written (overwrites sv e) t k \/ range_written a t k) /\
      ~ written (mreads sv e) t k).
Proof.
  destruct a as [F|]; intro Hreached; [|contradiction].
  unfold dead_store_transfer;
    cbn [range_add range_remove range_reached range_written proj1_sig].
  rewrite footprints_normalise_written, footprints_diff_written.
  rewrite footprints_normalise_written, written_app; reflexivity.
Qed.

(** Local store laws match steps and endings while preserving outside-dead-range agreement. *)
Record store_laws {S O N E T} (m : semantics S O) (en : endings S) (ET : encoding T)
    (sv : store_view S O N E T ET) : Prop := {
  s_view : graph_view_laws m (sgraph sv);
  s_no_stays : forall s l s', ~ stays (sgraph sv) s l s';
  s_agreement : agreement_laws (range_must_lattice ET) (sagree sv) /\
    agreement_symmetric (sagree sv);
  s_terminal_boundary : forall s k, reachable_state m s -> ends_as m en k s ->
    leb (range_must_lattice ET) (range_reached ET nil)
      (Reached (store_boundary sv (point (sgraph sv) s))) = true;
  s_step : forall sigma, dead_store_reached ET sv sigma ->
    step_agrees m (sgraph sv) (sagree sv) (reachable_state m)
      (dead_store_transfer ET sv) sigma;
  s_ends : ends_agree m en (sgraph sv) (sagree sv) (reachable_state m)
    (fun n => Reached (store_boundary sv n))
}.

Arguments Build_store_laws {S O N E T m en ET sv}.
Arguments s_view {S O N E T m en ET sv}.
Arguments s_no_stays {S O N E T m en ET sv}.
Arguments s_agreement {S O N E T m en ET sv}.
Arguments s_terminal_boundary {S O N E T m en ET sv}.
Arguments s_step {S O N E T m en ET sv}.
Arguments s_ends {S O N E T m en ET sv}.

(** Reached seeds force every listed post-solution fact to be reached. *)
Lemma dead_store_post_reached {S O N E T} (ET : encoding T)
    (sv : store_view S O N E T ET) (sigma : N -> range_must ET) :
  post_solution (range_must_lattice ET) (dead_store_system ET sv) sigma ->
  dead_store_reached ET sv sigma.
Proof.
  intros Hpost n Hin Heq.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  specialize (Hseed n Hin); rewrite Heq in Hseed; discriminate.
Qed.

(** At every actual ending, solution agreement entails agreement outside the empty dead range. *)
Lemma dead_store_terminal_agreement {S O N E T} (m : semantics S O) (en : endings S)
    (ET : encoding T) (sv : store_view S O N E T ET) (sigma : N -> range_must ET) s t k :
  store_laws m en ET sv ->
  post_solution (range_must_lattice ET) (dead_store_system ET sv) sigma ->
  reachable_state m s -> ends_as m en k s ->
  agree (sagree sv) (sigma (point (sgraph sv) s)) s t ->
  agree (sagree sv) (range_reached ET nil) s t.
Proof.
  intros laws Hpost Hreach Hend Hagree.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  eapply (agree_antitone (proj1 (s_agreement laws))); [|exact Hagree].
  eapply (leb_trans (range_must_laws ET)).
  - exact (s_terminal_boundary laws s k Hreach Hend).
  - apply Hseed; eapply view_point_in_nodes; [exact (s_view laws)|exact Hreach].
Qed.

(** Initial memories agreeing outside dead bytes have the same complete behaviours. *)
Theorem dead_store_sound {S O N E T} (m : semantics S O) (en : endings S) (ET : encoding T)
    (sv : store_view S O N E T ET) (sigma : N -> range_must ET) (s0 t0 : S) :
  store_laws m en ET sv ->
  post_solution (range_must_lattice ET) (dead_store_system ET sv) sigma ->
  initial m s0 -> initial m t0 -> point (sgraph sv) t0 = point (sgraph sv) s0 ->
  agree (sagree sv) (sigma (point (sgraph sv) s0)) s0 t0 -> same_behaviour m en s0 m en t0.
Proof.
  intros laws Hpost Hs Ht Hpoint Hagree.
  eapply (agreement_same_behaviour m en (sgraph sv) (range_must_lattice ET)
    (fun _ => sagree sv) (reachable_state m)); try eassumption.
  - exact (s_view laws).
  - exact (proj1 (s_agreement laws)).
  - exact (proj2 (s_agreement laws)).
  - apply reachable_invariant.
  - apply (s_step laws sigma); apply dead_store_post_reached; exact Hpost.
  - exact (s_ends laws).
Qed.

(** * Historical identities and byte framing *)

(** Byte observations keep an allocation's historical site independently of byte readability. *)
Record bytes_view (S O N E T L : Type) : Type := BytesView {
  bgv : graph_view S O N E;
  writes_at : N -> list (footprint T);
  bsite : S -> L -> option T;
  byte : S -> L -> Z -> option nat
}.

Arguments BytesView {S O N E T L}.
Arguments bgv {S O N E T L}.
Arguments writes_at {S O N E T L}.
Arguments bsite {S O N E T L}.
Arguments byte {S O N E T L}.

(** Every step retains historical sites and covers each changed byte of an existing identity. *)
Record bytes_laws {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L) : Prop := {
  by_view : graph_view_laws m (bgv bv);
  by_no_stays : forall s l s', ~ stays (bgv bv) s l s';
  byte_site_stable : forall s l s' l0 t, reachable_state m s -> step m s l s' ->
    bsite bv s l0 = Some t -> bsite bv s' l0 = Some t;
  byte_frame : forall s l s' l0 t o, reachable_state m s -> step m s l s' ->
    bsite bv s l0 = Some t -> byte bv s' l0 o <> byte bv s l0 o ->
    covered (writes_at bv (point (bgv bv) s)) t o 1
}.

Arguments Build_bytes_laws {S O N E T L m bv}.
Arguments by_view {S O N E T L m bv}.
Arguments by_no_stays {S O N E T L m bv}.
Arguments byte_site_stable {S O N E T L m bv}.
Arguments byte_frame {S O N E T L m bv}.

(** Disjointness checks every pair of same-site half-open footprints without enumerating bytes. *)
Definition footprints_disjoint {T} (ET : encoding T) (F G : list (footprint T)) : bool :=
  forallb (fun f => forallb (fun g =>
    negb (Pos.eqb (encode ET (fp_site f)) (encode ET (fp_site g))) ||
    Z.leb (fp_hi f) (fp_lo g) || Z.leb (fp_hi g) (fp_lo f)) G) F.

(** An invariant load requires recursive address invariance and disjoint loop write footprints. *)
Definition invariant_load {S O N E V K C T} (ET : encoding T)
    (np : numbering_problem S O N E V K C) (lp : loop_info N) (addr : V)
    (loop_writes : list (footprint T)) (load : footprint T) : bool :=
  invariant_in np lp addr && footprints_disjoint ET loop_writes [load].

(** Accepted footprint disjointness rules out any shared byte. *)
Theorem footprints_disjoint_sound {T} (ET : encoding T) (F G : list (footprint T)) :
  footprints_disjoint ET F G = true -> forall t o,
    covered F t o 1 -> covered G t o 1 -> False.
Proof.
  intros Hdisjoint t o HF HG.
  destruct (HF o ltac:(cbn; lia)) as [f [Hf [Hsitef Hboundsf]]].
  destruct (HG o ltac:(cbn; lia)) as [g [Hg [Hsiteg Hboundsg]]].
  unfold footprints_disjoint in Hdisjoint.
  apply forallb_forall with (x := f) in Hdisjoint; [|exact Hf].
  apply forallb_forall with (x := g) in Hdisjoint; [|exact Hg].
  rewrite Hsitef, Hsiteg, Pos.eqb_refl in Hdisjoint; cbn in Hdisjoint.
  apply orb_true_iff in Hdisjoint as [Hbefore|Hafter];
    apply Z.leb_le in Hbefore || apply Z.leb_le in Hafter; lia.
Qed.

Lemma bytes_unwritten_step {S O N E T L} (m : semantics S O)
    (bv : bytes_view S O N E T L) (laws : bytes_laws m bv) s tr t l ty o :
  reachable_state m s -> step m s tr t -> bsite bv s l = Some ty ->
  ~ covered (writes_at bv (point (bgv bv) s)) ty o 1 -> byte bv t l o = byte bv s l o.
Proof.
  intros Hreach Hstep Hsite Houtside.
  assert (Hdecision : {byte bv t l o = byte bv s l o} +
    {byte bv t l o <> byte bv s l o}) by (decide equality; apply Nat.eq_dec).
  destruct Hdecision as [Heq|Hne].
  - exact Heq.
  - exfalso; apply Houtside; eapply (byte_frame laws); eassumption.
Qed.

(** A byte at a historical identity never changes when every node excludes it from its writes. *)
Theorem immutable_sound {S O N E T L} (m : semantics S O) (bv : bytes_view S O N E T L)
    (ty : T) (o : Z) :
  bytes_laws m bv -> (forall n, covered (writes_at bv n) ty o 1 -> False) ->
  forall s tr t l, reachable_state m s -> exec m s tr t -> bsite bv s l = Some ty ->
    byte bv t l o = byte bv s l o.
Proof.
  intros laws Hwrites s tr t l Hreach Hrun; revert Hreach.
  induction Hrun as [s|s tr s' rest t Hstep Hrun IH]; intros Hreach Hsite.
  - reflexivity.
  - rewrite (IH (reachable_state_step m s tr s' Hreach Hstep)
      (byte_site_stable laws s tr s' l ty Hreach Hstep Hsite)).
    eapply (bytes_unwritten_step m bv laws); try eassumption.
    exact (Hwrites _).
Qed.

Lemma covered_inclusion {T} (F G : list (footprint T)) t o w :
  incl F G -> covered F t o w -> covered G t o w.
Proof.
  intros Hin Hcovered k Hk; destruct (Hcovered k Hk) as [f [Hf Hbounds]].
  exists f; split; [apply Hin; exact Hf|exact Hbounds].
Qed.

(** During a loop execution, disjoint writes preserve the bytes of the load's original identity. *)
Theorem invariant_load_sound {S O N E V K C T L} (m : semantics S O) (ET : encoding T)
    (bv : bytes_view S O N E T L) (np : numbering_problem S O N E V K C) (lp : loop_info N)
    (addr : V) (loop_writes : list (footprint T)) (load : footprint T) :
  bytes_laws m bv -> ssa_view_laws m (nsv np) -> strict_ssa_laws m (nsv np) ->
  loop_info_wf (cfg (base (nsv np))) lp ->
  (forall s, point (base (nsv np)) s = point (bgv bv) s) ->
  invariant_load ET np lp addr loop_writes load = true ->
  (forall n, body lp n = true -> forall f, In f (writes_at bv n) -> In f loop_writes) ->
  forall s tr t l ty o, reachable_state m s ->
    exec_in m (fun u => body lp (point (bgv bv) u) = true) s tr t ->
    covered [load] ty o 1 -> bsite bv s l = Some ty -> byte bv t l o = byte bv s l o.
Proof.
  intros laws Hssa Hstrict Hloop Hpoints Hload Hwrites.
  apply andb_true_iff in Hload as [Haddr Hdisjoint].
  intros s tr t l ty o Hreach Hrun Hcovered; revert Hreach.
  induction Hrun as [s Hbody|s tr s' rest t Hbody Hstep Hrun IH]; intros Hreach Hsite.
  - reflexivity.
  - rewrite (IH (reachable_state_step m s tr s' Hreach Hstep)
      (byte_site_stable laws s tr s' l ty Hreach Hstep Hsite)).
    eapply bytes_unwritten_step; try eassumption.
    intro Hwritten; eapply (footprints_disjoint_sound ET loop_writes [load] Hdisjoint ty o).
    + eapply covered_inclusion; [exact (Hwrites _ Hbody)|exact Hwritten].
    + exact Hcovered.
Qed.

(** * Allocation epochs *)

(** Liveness is independent of byte readability, so zero-byte allocations can be live. *)
Record epoch_view (S O N E T L : Type) : Type := EpochView {
  epoch_bytes : bytes_view S O N E T L;
  epoch_live : S -> L -> bool
}.

Arguments EpochView {S O N E T L}.
Arguments epoch_bytes {S O N E T L}.
Arguments epoch_live {S O N E T L}.

(** Newly live identities must have had no historical site before their allocation. *)
Record epoch_laws {S O N E T L} (m : semantics S O) (ev : epoch_view S O N E T L) : Prop := {
  epoch_byte_laws : bytes_laws m (epoch_bytes ev);
  epoch_live_site : forall s l, reachable_state m s -> epoch_live ev s l = true ->
    exists t, bsite (epoch_bytes ev) s l = Some t;
  epoch_allocate_fresh : forall s tr s' l, reachable_state m s -> step m s tr s' ->
    epoch_live ev s l = false -> epoch_live ev s' l = true ->
    bsite (epoch_bytes ev) s l = None /\ exists t, bsite (epoch_bytes ev) s' l = Some t
}.

Arguments Build_epoch_laws {S O N E T L m ev}.
Arguments epoch_byte_laws {S O N E T L m ev}.
Arguments epoch_live_site {S O N E T L m ev}.
Arguments epoch_allocate_fresh {S O N E T L m ev}.

Lemma epoch_dead_step {S O N E T L} (m : semantics S O)
    (ev : epoch_view S O N E T L) (laws : epoch_laws m ev) s tr s' l t :
  reachable_state m s -> step m s tr s' -> bsite (epoch_bytes ev) s l = Some t ->
  epoch_live ev s l = false -> epoch_live ev s' l = false.
Proof.
  intros Hreach Hstep Hsite Hdead; destruct (epoch_live ev s' l) eqn:Hlive; [|reflexivity].
  destruct (epoch_allocate_fresh laws s tr s' l Hreach Hstep Hdead Hlive) as [Hnone _].
  congruence.
Qed.

(** A freed identity retains its site and remains dead throughout every later finite run. *)
Theorem epoch_no_resurrection {S O N E T L} (m : semantics S O)
    (ev : epoch_view S O N E T L) :
  epoch_laws m ev -> forall s tr s' l t,
    reachable_state m s -> bsite (epoch_bytes ev) s l = Some t -> epoch_live ev s l = false ->
    exec m s tr s' -> epoch_live ev s' l = false /\ bsite (epoch_bytes ev) s' l = Some t.
Proof.
  intros laws s tr s' l t Hreach Hsite Hdead Hrun; revert Hreach Hsite Hdead.
  induction Hrun as [s|s tr u rest v Hstep Hrun IH]; intros Hreach Hsite Hdead.
  - split; assumption.
  - apply IH.
    + eapply reachable_state_step; eassumption.
    + eapply (byte_site_stable (epoch_byte_laws laws)); eassumption.
    + eapply epoch_dead_step; eassumption.
Qed.
