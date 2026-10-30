(** * Successful memory value forwarding

    Increasing-address byte observations connect preserved memory to a client's decoder.
    For example, a successful two-byte load can recover a preceding store to the same object.
    Builds on: AnalysesMemoryLegacy, AnalysesMemoryBase and ViewsSemantics. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryBase AnalysesMemoryGraph AnalysesMemoryLegacy.
Import List.ListNotations.

(** The output width controls structural recursion, rather than an execution fuel bound. *)
Fixpoint memory_read_from (observe : Z -> option nat) (o : Z) (width : nat) : option (list nat) :=
  match width with
  | O => Some []
  | S rest =>
    match observe o with
    | None => None
    | Some b =>
      match memory_read_from observe (o + 1)%Z rest with
      | None => None
      | Some bs => Some (b :: bs)
      end
    end
  end.

(** Read exactly the requested consecutive bytes in increasing address order. *)
Definition memory_read_bytes {S O N E T L} (bv : bytes_view S O N E T L)
    (s : S) (l : L) (o : Z) (width : nat) : option (list nat) :=
  memory_read_from (byte bv s l) o width.

(** The client identifies successful accesses and supplies its own representation decoder. *)
Record memory_value_view (S E L V : Type) : Type := MemoryValueView {
  store_location : S -> E -> option (L * Z * nat);
  load_location : S -> E -> option (L * Z * nat);
  stored_value : S -> E -> V -> Prop;
  loaded_value : S -> E -> V -> Prop;
  decode_memory_value : list nat -> option V
}.

Arguments MemoryValueView {S E L V}.
Arguments store_location {S E L V}.
Arguments load_location {S E L V}.
Arguments stored_value {S E L V}.
Arguments loaded_value {S E L V}.
Arguments decode_memory_value {S E L V}.

(** Byte bounds and actual successful steps connect stores and loads to the same decoder. *)
Record memory_value_laws {S O N E T L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V) : Prop := {
  memory_value_byte_range : forall s l o b, reachable_state m s -> byte bv s l o = Some b ->
    (b < 256)%nat;
  memory_store_encoding : forall s tr s' e l o w v,
    reachable_state m s -> step m s tr s' -> taken (bgv bv) s tr s' e ->
    store_location vv s e = Some (l, o, w) -> stored_value vv s e v ->
    exists bs, memory_read_bytes bv s' l o w = Some bs /\ decode_memory_value vv bs = Some v;
  memory_load_decoding : forall s tr s' e l o w v,
    reachable_state m s -> step m s tr s' -> taken (bgv bv) s tr s' e ->
    load_location vv s e = Some (l, o, w) -> loaded_value vv s e v ->
    exists bs, memory_read_bytes bv s l o w = Some bs /\ decode_memory_value vv bs = Some v
}.

Arguments memory_value_byte_range {S O N E T L V m bv vv}.
Arguments memory_store_encoding {S O N E T L V m bv vv}.
Arguments memory_load_decoding {S O N E T L V m bv vv}.

(** Equal observations throughout an exact range give equal ordered byte lists. *)
Lemma memory_read_from_equal observe1 observe2 width : forall o,
  (forall k, (o <= k < o + Z.of_nat width)%Z -> observe1 k = observe2 k) ->
  memory_read_from observe1 o width = memory_read_from observe2 o width.
Proof.
  induction width as [|width IH]; intros o Hagree; [reflexivity|].
  cbn [memory_read_from]; rewrite Hagree by (rewrite Nat2Z.inj_succ; lia).
  rewrite (IH (o + 1)%Z) by (intros k Hk; apply Hagree; rewrite Nat2Z.inj_succ; lia).
  reflexivity.
Qed.

(** Successful byte observations have the requested length, including the empty range. *)
Lemma memory_read_from_length observe width : forall o bs,
  memory_read_from observe o width = Some bs -> length bs = width.
Proof.
  induction width as [|width IH]; intros o bs Hread.
  - inversion Hread; reflexivity.
  - cbn [memory_read_from] in Hread; destruct (observe o) as [b|]; [|discriminate].
    destruct (memory_read_from observe (o + 1)%Z width) as [rest|] eqn:Hrest;
      [|discriminate].
    inversion Hread; subst bs; cbn; f_equal; eapply IH; exact Hrest.
Qed.

(** Client range laws bound each byte of every successful ordered observation. *)
Lemma memory_read_bytes_range {S O N E T L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V) :
  memory_value_laws m bv vv -> forall s l o w bs,
  reachable_state m s -> memory_read_bytes bv s l o w = Some bs ->
  Forall (fun b => (b < 256)%nat) bs.
Proof.
  intros Hlaws s l o w; revert o; induction w as [|w IH]; intros o bs Hreachable Hread.
  - inversion Hread; constructor.
  - cbn [memory_read_bytes memory_read_from] in Hread.
    destruct (byte bv s l o) as [b|] eqn:Hbyte; [|discriminate].
    destruct (memory_read_from (byte bv s l) (o + 1)%Z w) as [rest|] eqn:Hrest;
      [|discriminate].
    inversion Hread; subst bs; constructor.
    + eapply (memory_value_byte_range Hlaws); eassumption.
    + apply (IH (o + 1)%Z rest Hreachable); exact Hrest.
Qed.

(** Successful same-object, same-range accesses decode equal values after byte preservation. *)
Theorem memory_forward_value {S O N E T F L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V)
    (EN : encoding N) (EF : encoding F) (ET : encoding T) (f : F)
    (ms : memory_ssa F N) (reads : N -> list (footprint T)) :
  bytes_laws m bv -> memory_value_laws m bv vv ->
  no_clobber_check EN EF ET f (cfg (bgv bv)) (writes_at bv) reads ms = true ->
  forall s tr s1 e es t tr' t' e' n l ty o w stored loaded,
    reachable_state m s -> step m s tr s1 -> taken (bgv bv) s tr s1 e ->
    run_edges m (bgv bv) s1 es t -> point (bgv bv) t = n ->
    step m t tr' t' -> taken (bgv bv) t tr' t' e' ->
    def_of_load ms n = Some (MDef f (Graph.source (cfg (bgv bv)) e)) ->
    store_location vv s e = Some (l, o, w) -> load_location vv t e' = Some (l, o, w) ->
    stored_value vv s e stored -> loaded_value vv t e' loaded ->
    bsite bv s1 l = Some ty -> covered (reads n) ty o w -> stored = loaded.
Proof.
  intros Hbytes Hvalues Hcheck s tr s1 e es t tr' t' e' n l ty o w stored loaded
    Hreachable Hstore_step Hstore_taken Hrun Hpoint Hload_step Hload_taken Hdef
    Hstore_location Hload_location Hstored Hloaded Hsite Hcovered.
  assert (Hreachable1 : reachable_state m s1).
  { eapply reachable_state_step; eassumption. }
  assert (Hreachable_t : reachable_state m t).
  { eapply legacy_run_reachable; eassumption. }
  destruct (memory_store_encoding Hvalues s tr s1 e l o w stored Hreachable Hstore_step
    Hstore_taken Hstore_location Hstored) as [store_bytes [Hstore_read Hstore_decode]].
  destruct (memory_load_decoding Hvalues t tr' t' e' l o w loaded Hreachable_t Hload_step
    Hload_taken Hload_location Hloaded) as [load_bytes [Hload_read Hload_decode]].
  assert (Hsame : memory_read_bytes bv t l o w = memory_read_bytes bv s1 l o w).
  { apply memory_read_from_equal; intros k Hrange.
    eapply (proj1 (no_clobber_unchanged m bv EN EF ET f ms reads Hbytes Hcheck)
      s s1 t e es n Hreachable).
    - econstructor; [exact Hstore_step|exact Hstore_taken|constructor].
    - exact Hrun.
    - exact Hpoint.
    - exact Hdef.
    - intros j Hj; apply Hcovered; cbn in Hj; lia.
    - exact Hsite. }
  rewrite Hload_read, Hstore_read in Hsame; inversion Hsame; subst load_bytes.
  rewrite Hstore_decode in Hload_decode; inversion Hload_decode; reflexivity.
Qed.

(** The directly proved legacy projection supplies the certificate without an acceptance premise. *)
Theorem memory_forward_projected {S O N E T F L V} (m : semantics S O)
    (bv : bytes_view S O N E T L) (vv : memory_value_view S E L V)
    (EN : encoding N) (EE : encoding E) (EF : encoding F) (ET : encoding T) (f : F)
    (effects : E -> list (memory_effect T)) (reads : N -> list (footprint T))
    (mg : memory_graph N E) (loads : N -> option (E * nat)) (fuel : positive) :
  bytes_laws m bv -> memory_value_laws m bv vv ->
  memory_graph_wf (cfg (bgv bv)) effects mg ->
  forall s tr s1 e es t tr' t' e' n l ty o w stored loaded,
    reachable_state m s -> step m s tr s1 -> taken (bgv bv) s tr s1 e ->
    run_edges m (bgv bv) s1 es t -> point (bgv bv) t = n ->
    step m t tr' t' -> taken (bgv bv) t tr' t' e' ->
    def_of_load (project_memory_legacy EN EE EF ET f (cfg (bgv bv)) effects
      (writes_at bv) reads mg loads fuel) n = Some (MDef f (Graph.source (cfg (bgv bv)) e)) ->
    store_location vv s e = Some (l, o, w) -> load_location vv t e' = Some (l, o, w) ->
    stored_value vv s e stored -> loaded_value vv t e' loaded ->
    bsite bv s1 l = Some ty -> covered (reads n) ty o w -> stored = loaded.
Proof.
  intros Hbytes Hvalues Hwf.
  apply (memory_forward_value m bv vv EN EF ET f
    (project_memory_legacy EN EE EF ET f (cfg (bgv bv)) effects
      (writes_at bv) reads mg loads fuel) reads); [exact Hbytes|exact Hvalues|].
  apply project_memory_legacy_correct; exact Hwf.
Qed.
