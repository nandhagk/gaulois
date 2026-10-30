(** * Computed sparse sources and successful value observations

    These fixtures distinguish finite source unions from conservative walker cuts and byte values.
    For example, a cyclic entry phi has the singleton live source even when the walker cuts it.
    Builds on: AnalysesMemoryFlow, AnalysesMemoryForward and the ANA-10d/e graph fixtures. *)

From Stdlib Require Import List Bool ZArith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderPowerset.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointTotal
  FixpointSchedule.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesMemoryBase AnalysesMemoryGraph
  AnalysesMemoryFrontier AnalysesMemorySealed AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesMemoryFlow AnalysesMemoryForward.
From Gaulois.Examples.Ssa Require Import ExamplesSsaSemantics ExamplesSsaBytes
  ExamplesSsaMemoryLegacy.
From Gaulois.Tests.Analyses Require Import Analyses9Test AnalysesANA10d AnalysesANA10e.
Import List.ListNotations.
Local Open Scope nat_scope.

(** A successful bounded observation uses the same declared joining engine as the total solver. *)
Definition flow_probe {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects mg q :=
  let EV := memory_version_encoding EN EE in
  let sys := memory_flow_system EN EE ET g effects mg q in
  let ss := memory_flow_static EN EE ET g effects mg q in
  run_worklist EV EV (memory_flow_lattice EN EE mg) (rpo_scheduler EV sys ss) Joining sys
    (Declared ss (index_system EV sys ss)) 256%positive.

(** A completed probe is exactly the public total function, independently of its fuel. *)
Lemma flow_probe_agrees {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects mg q
    (Hwf : memory_graph_wf g effects mg) values :
  flow_probe EN EE ET g effects mg q = Some values ->
  proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf) =
    lookup (memory_version_encoding EN EE) (memory_flow_lattice EN EE mg) values.
Proof.
  intro Hprobe.
  destruct (solve_total_run (memory_version_encoding EN EE) (memory_version_encoding EN EE)
    (memory_flow_lattice EN EE mg) (memory_flow_system EN EE ET g effects mg q)
    (rpo_scheduler (memory_version_encoding EN EE) (memory_flow_system EN EE ET g effects mg q)
      (memory_flow_static EN EE ET g effects mg q)) Joining (finite_powerset_laws _ _)
    (memory_flow_static EN EE ET g effects mg q)
    (memory_flow_termination EN EE ET g effects mg q Hwf)) as [fuel Hrun].
  destruct (Hrun fuel (Pos.le_refl fuel)) as [other [Hother Hagree]].
  pose proof (total_completed_runs_unique _ _ _ _ _ _ _ fuel 256%positive
    other values Hother Hprobe) as Heq.
  subst other; exact Hagree.
Qed.

(** None records fuel exhaustion rather than claiming an empty source set. *)
Definition flow_sources {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects mg q start :=
  match flow_probe EN EE ET g effects mg q with
  | None => None
  | Some values => Some (FinSet.elements (proj1_sig
      (lookup (memory_version_encoding EN EE) (memory_flow_lattice EN EE mg) values start)))
  end.

(** Every successful source-list observation describes the actual public total result. *)
Lemma flow_sources_agrees {N E T} EN EE (ET : encoding T) (g : Graph.t N E) effects mg q
    (Hwf : memory_graph_wf g effects mg) start sources :
  flow_sources EN EE ET g effects mg q start = Some sources ->
  FinSet.elements (proj1_sig (proj1_sig (memory_flow_solve EN EE ET g effects mg q Hwf) start)) =
    sources.
Proof.
  unfold flow_sources; destruct (flow_probe EN EE ET g effects mg q) as [values|] eqn:Hprobe;
    [|discriminate].
  intro Hsources; inversion Hsources; subst sources.
  rewrite (flow_probe_agrees EN EE ET g effects mg q Hwf values Hprobe); reflexivity.
Qed.

Definition chain_sources middle :=
  flow_sources nat_encoding nat_encoding nat_encoding walk_graph (walk_effects middle)
    (walk_versions middle) site_a (MemoryPhi 2).

Example disjoint_write_singleton : chain_sources (MemoryWrite site_b) = Some [MemoryDef 0 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example actual_total_singleton :
  FinSet.elements (proj1_sig (proj1_sig (memory_flow_solve nat_encoding nat_encoding nat_encoding
    walk_graph (walk_effects (MemoryWrite site_b)) (walk_versions (MemoryWrite site_b)) site_a
    (proj2_sig (memory_sealed_build nat_encoding nat_encoding walk_graph
      (walk_effects (MemoryWrite site_b)) walk_graph_wf))) (MemoryPhi 2))) = [MemoryDef 0 0].
Proof.
  apply flow_sources_agrees; vm_compute; reflexivity.
Qed.

Example overlapping_write_is_source : chain_sources (MemoryWrite overlap_a) = Some [MemoryDef 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_overwrite_is_not_old_value :
  (chain_sources (MemoryWrite overlap_a),
   memory_scopes_disjoint nat_encoding overlap_a site_a) = (Some [MemoryDef 1 0], false).
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_call_is_explicit_source :
  chain_sources (MemoryCall MemoryAll MemoryAll) = Some [MemoryDef 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example barrier_is_explicit_source : chain_sources MemoryBarrier = Some [MemoryDef 1 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example cyclic_phi_fixed_point :
  flow_sources nat_encoding nat_encoding nat_encoding cyclic_phi_graph
    (fun _ => [MemoryRead site_a]) cyclic_phi_versions site_a (MemoryPhi 0) = Some [MemoryLive].
Proof.
  vm_compute; reflexivity.
Qed.

Example invalid_version_is_bottom :
  flow_sources nat_encoding nat_encoding nat_encoding cyclic_phi_graph
    (fun _ => [MemoryRead site_a]) cyclic_phi_versions site_a (MemoryDef 40 9) = Some [].
Proof.
  vm_compute; reflexivity.
Qed.

Definition cyclic_store_effects (e : fixture_edge) : list (memory_effect nat) :=
  if Nat.eqb (fst e) 0 then [MemoryWrite site_a] else [MemoryRead site_a].

Definition cyclic_store_memory := proj1_sig (memory_sealed_build nat_encoding fixture_encoding
  self_cfg cyclic_store_effects self_cfg_wf).

Example cyclic_phi_with_store_source :
  flow_sources nat_encoding fixture_encoding nat_encoding self_cfg cyclic_store_effects
    cyclic_store_memory site_a (MemoryPhi 1) = Some [MemoryDef ingress 0].
Proof.
  vm_compute; reflexivity.
Qed.

Definition diamond_edges : list fixture_edge :=
  [(0, (0, 1)); (1, (0, 2)); (2, (1, 3)); (3, (2, 3)); (4, (3, 4))].
Definition diamond_cfg := fixture_cfg 5 [0] diamond_edges.

Lemma diamond_cfg_wf : graph_wf diamond_cfg.
Proof.
  apply fixture_cfg_wf; reflexivity.
Qed.

Definition diamond_effects (e : fixture_edge) : list (memory_effect nat) :=
  match fst e with
  | 2 | 3 => [MemoryWrite site_a]
  | 4 => [MemoryRead site_a]
  | _ => []
  end.

Definition diamond_memory := proj1_sig
  (memory_sealed_build nat_encoding fixture_encoding diamond_cfg diamond_effects diamond_cfg_wf).

Example diamond_sources :
  flow_sources nat_encoding fixture_encoding nat_encoding diamond_cfg diamond_effects
    diamond_memory site_a (MemoryPhi 3) =
    Some [MemoryDef (3, (2, 3)) 0; MemoryDef (2, (1, 3)) 0].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_actual_histories :
  (memory_path_last_clobber nat_encoding site_a diamond_effects [(0, (0, 1)); (2, (1, 3))]
      : memory_version nat fixture_edge,
   memory_path_last_clobber nat_encoding site_a diamond_effects [(1, (0, 2)); (3, (2, 3))]
      : memory_version nat fixture_edge) =
    (MemoryDef (2, (1, 3)) 0, MemoryDef (3, (2, 3)) 0).
Proof.
  reflexivity.
Qed.

Example both_builders_singleton :
  flow_sources nat_encoding nat_encoding nat_encoding walk_graph
    (walk_effects (MemoryWrite site_b))
    (proj1_sig (memory_frontier_build nat_encoding nat_encoding walk_graph
      (walk_effects (MemoryWrite site_b)) walk_graph_wf)) site_a (MemoryDef 1 0) =
    Some [MemoryDef 0 0].
Proof.
  vm_compute; reflexivity.
Qed.

(** * A concrete successful store and load *)

Definition value_machine : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s tr t => (s < 3)%nat /\ tr = [] /\ t = S s).

Definition value_graph : graph_view nat unit nat nat :=
  GraphView walk_graph (fun s => s) (fun s _ _ e => e = s) (fun _ _ _ => False).

(** The two object identities deliberately have the same historical allocation site. *)
Definition value_byte (s : nat) (identity : bool) (o : Z) : option nat :=
  if identity then
    if Z.eqb o 0 then Some 90 else if Z.eqb o 1 then Some 91 else None
  else if Nat.eqb s 0 then None
    else if Z.eqb o 0 then Some 42 else if Z.eqb o 1 then Some 43 else None.

Definition value_writes (n : nat) : list (footprint nat) :=
  if Nat.eqb n 0 then [Footprint 0 0%Z 2%Z] else [].

Definition value_reads (n : nat) : list (footprint nat) :=
  if Nat.eqb n 2 then [Footprint 0 0%Z 2%Z] else [].

Definition value_bytes : bytes_view nat unit nat nat nat bool :=
  BytesView value_graph value_writes (fun _ _ => Some 0) value_byte.

Definition value_decode (bs : list nat) : option nat :=
  match bs with
  | [lo; hi] => Some (lo + 256 * hi)%nat
  | _ => None
  end.

Definition value_view : memory_value_view nat nat bool nat :=
  MemoryValueView
    (fun s e => if Nat.eqb s 0 && Nat.eqb e 0 then Some (false, 0%Z, 2) else None)
    (fun s e => if Nat.eqb s 2 && Nat.eqb e 2 then Some (false, 0%Z, 2) else None)
    (fun s e v => s = 0 /\ e = 0 /\ v = N.to_nat 11050%N)
    (fun s e v => s = 2 /\ e = 2 /\ v = N.to_nat 11050%N) value_decode.

Lemma value_graph_laws : graph_view_laws value_machine value_graph.
Proof.
  constructor.
  - exact walk_graph_wf.
  - intros s ->; left; reflexivity.
  - intros s tr t Hreachable Hstep; right; exists s; reflexivity.
  - intros s tr t e Hreachable [Hbound [Htr ->]] ->; split.
    + cbn [value_graph cfg point walk_graph Graph.out].
      assert (Htest : Nat.ltb s 3 = true) by (apply Nat.ltb_lt; exact Hbound).
      rewrite Htest; left; reflexivity.
    + reflexivity.
  - intros s tr t Hreachable Hstep Hfalse; contradiction.
Qed.

Lemma value_bytes_laws : bytes_laws value_machine value_bytes.
Proof.
  constructor.
  - exact value_graph_laws.
  - intros s tr t Hfalse; contradiction.
  - intros s tr t identity site Hreachable Hstep Hsite; exact Hsite.
  - intros s tr t identity site o Hreachable [Hbound [Htr ->]] Hsite Hchange.
    cbn [value_bytes bsite] in Hsite; inversion Hsite; subst site.
    destruct s as [|s].
    + cbn [value_bytes writes_at value_writes value_graph point].
      destruct identity; cbn [value_bytes byte value_byte] in Hchange; [contradiction|].
      destruct (Z.eqb o 0) eqn:Hlo; [apply Z.eqb_eq in Hlo; subst o|].
      * intros k Hk; exists (Footprint 0 0%Z 2%Z); cbn; split; [auto|split; [reflexivity|lia]].
      * destruct (Z.eqb o 1) eqn:Hhi; [apply Z.eqb_eq in Hhi; subst o|contradiction].
        intros k Hk; exists (Footprint 0 0%Z 2%Z); cbn; split; [auto|split; [reflexivity|lia]].
    + exfalso; apply Hchange; destruct identity; reflexivity.
Qed.

Lemma value_view_laws : memory_value_laws value_machine value_bytes value_view.
Proof.
  constructor.
  - intros s identity o b Hreachable Hbyte.
    destruct identity, s; cbn [value_bytes byte value_byte] in Hbyte; try discriminate;
      destruct (Z.eqb o 0); destruct (Z.eqb o 1); inversion Hbyte; lia.
  - intros s tr t e identity o w v Hreachable Hstep Htaken Hlocation [-> [-> ->]].
    inversion Hlocation; subst identity o w.
    destruct Hstep as [_ [_ ->]]; exists [42; 43]; split; reflexivity.
  - intros s tr t e identity o w v Hreachable Hstep Htaken Hlocation [-> [-> ->]].
    inversion Hlocation; subst identity o w; exists [42; 43]; split; reflexivity.
Qed.

Definition value_effects (e : nat) : list (memory_effect nat) :=
  match e with
  | 0 => [MemoryWrite (MemoryRegions [Footprint 0 0%Z 2%Z])]
  | 2 => [MemoryRead (MemoryRegions [Footprint 0 0%Z 2%Z])]
  | _ => []
  end.

Definition value_memory := proj1_sig
  (memory_sealed_build nat_encoding nat_encoding walk_graph value_effects walk_graph_wf).

Definition value_projection := project_memory_legacy nat_encoding nat_encoding nat_encoding
  nat_encoding 0 walk_graph value_effects value_writes value_reads value_memory
  (fun n => if Nat.eqb n 2 then Some (2, 0) else None) 32%positive.

Example successful_forwarded_value :
  (def_of_load value_projection 2,
   memory_read_bytes value_bytes 1 false 0%Z 2,
   memory_read_bytes value_bytes 2 false 0%Z 2,
   option_map N.of_nat (value_decode [42; 43])) =
    (Some (MDef 0 0), Some [42; 43], Some [42; 43], Some 11050%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example singleton_source_and_forwarded_value :
  (flow_sources nat_encoding nat_encoding nat_encoding walk_graph value_effects value_memory
      (MemoryRegions [Footprint 0 0%Z 2%Z]) (MemoryPhi 2),
   option_map N.of_nat (value_decode [42; 43])) = (Some [MemoryDef 0 0], Some 11050%N).
Proof.
  vm_compute; reflexivity.
Qed.

(** The actual store/load pair also instantiates the universal projected theorem. *)
Lemma successful_forwarding_applies stored loaded :
  stored_value value_view 0 0 stored -> loaded_value value_view 2 2 loaded -> stored = loaded.
Proof.
  intros Hstored Hloaded.
  eapply (memory_forward_projected value_machine value_bytes value_view nat_encoding nat_encoding
    nat_encoding nat_encoding 0 value_effects value_reads value_memory
    (fun n => if Nat.eqb n 2 then Some (2, 0) else None) 32%positive
    value_bytes_laws value_view_laws
    (proj2_sig (memory_sealed_build nat_encoding nat_encoding walk_graph value_effects
      walk_graph_wf)) 0 [] 1 0 [1] 2 [] 3 2 2 false 0 0%Z 2 stored loaded).
  - exists 0, []; split; [reflexivity|constructor].
  - repeat split; reflexivity || lia.
  - reflexivity.
  - econstructor; [repeat split; reflexivity || lia|reflexivity|constructor].
  - reflexivity.
  - repeat split; reflexivity || lia.
  - reflexivity.
  - vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - exact Hstored.
  - exact Hloaded.
  - reflexivity.
  - intros k Hk; exists (Footprint 0 0%Z 2%Z); cbn; auto.
Qed.

Example same_site_different_objects :
  (bsite value_bytes 2 false, bsite value_bytes 2 true,
   memory_read_bytes value_bytes 2 false 0%Z 2,
   memory_read_bytes value_bytes 2 true 0%Z 2,
   option_map N.of_nat (value_decode [90; 91])) =
    (Some 0, Some 0, Some [42; 43], Some [90; 91], Some 23386%N).
Proof.
  vm_compute; reflexivity.
Qed.

Example unavailable_bytes_do_not_decode :
  (memory_read_bytes value_bytes 0 false 0%Z 2,
   memory_read_bytes value_bytes 2 false 0%Z 3) = (None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Example pointer_fragment_is_unavailable :
  memory_read_bytes (ssa_bytes_view no_ext fragment_program pointer_limits)
    (fragment_at 2%positive) 0 0%Z 8 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_integer_and_fragment_bytes :
  (memory_read_bytes (ssa_bytes_view no_ext fragment_program pointer_limits)
      (fragment_at 7%positive) 0 4%Z 1,
   memory_read_bytes (ssa_bytes_view no_ext fragment_program pointer_limits)
      (fragment_at 7%positive) 0 3%Z 2,
   memory_read_bytes (ssa_bytes_view no_ext fragment_program pointer_limits)
      (fragment_at 10%positive) 0 4%Z 1) = (Some [7], None, None).
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_width_and_boundary_ranges :
  (memory_read_bytes value_bytes 0 false (-100)%Z 0,
   memory_read_bytes value_bytes 2 false 1%Z 1,
   memory_read_bytes value_bytes 2 false 2%Z 1,
   memory_read_bytes value_bytes 2 false (-1)%Z 1,
   memory_scopes_disjoint nat_encoding (MemoryRegions [Footprint 0 2%Z 3%Z])
     (MemoryRegions [Footprint 0 0%Z 2%Z])) =
    (Some [], Some [43], None, None, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example ascending_arbitrary_byte_width :
  memory_read_from (fun offset => Some (Z.to_nat (offset mod 256)%Z)) 250%Z 12 =
    Some [250; 251; 252; 253; 254; 255; 0; 1; 2; 3; 4; 5].
Proof.
  vm_compute; reflexivity.
Qed.

Example partial_overlap_forwarding_rejected :
  def_of_load (project_chain chain_writes_clobber) 2 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_call_forwarding_rejected :
  no_clobber_check nat_encoding nat_encoding nat_encoding 0 walk_graph
    (fun n => if Nat.eqb n 1 then [Footprint 0 0%Z 8%Z] else chain_writes n)
    chain_reads (MemorySSA (fun n => if Nat.eqb n 2 then Some (MDef 0 0) else None)) = false.
Proof.
  vm_compute; reflexivity.
Qed.
