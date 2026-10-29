(** * Backward value demand and dead-code erasure

    Demands describe the parts of values that determine observable behaviour.
    For example, an unused assignment contributes no Boolean operand demand.
    Builds on: OrderPointwise, ViewsAgreement, ViewsEffects and FixpointTotal. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderMonotone OrderBasic
  OrderPointwise.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointLeast
  FixpointWorklist FixpointTotal FixpointSchedule.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsAgreement ViewsEffects.
Import List.ListNotations.

(** A demand domain pairs its order with value agreement. *)
Record demand_domain (M Cv : Type) : Type := DemandDomain {
  dlat : lattice M;
  dagree : agreement M Cv
}.

Arguments DemandDomain {M Cv}.
Arguments dlat {M Cv}.
Arguments dagree {M Cv}.

(** A view supplies forced, backward and exit demands over a finite variable universe. *)
Record demand_view (S O N E X Cv M : Type) : Type := DemandView {
  dgraph : graph_view S O N E;
  ddefs : E -> list X;
  dnec : E -> list (X * M);
  dback : E -> X -> M -> list (X * M);
  dexit : N -> list (X * M);
  dlookup : S -> X -> Cv;
  dvars : list X
}.

Arguments dgraph {S O N E X Cv M}.
Arguments ddefs {S O N E X Cv M}.
Arguments dnec {S O N E X Cv M}.
Arguments dback {S O N E X Cv M}.
Arguments dexit {S O N E X Cv M}.
Arguments dlookup {S O N E X Cv M}.
Arguments dvars {S O N E X Cv M}.

(** Missing variable bindings have bottom demand. *)
Definition demand_lattice {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) : lattice (finite_map EX (dvars dv) M) :=
  finite_pointwise_lattice EX (dvars dv) (dlat DD).

(** Read a variable demand with the lattice bottom as default. *)
Definition dget {X M} (EX : encoding X) {U : list X} (DL : lattice M)
    (d : finite_map EX U M) (x : X) : M :=
  pointwise_lookup EX (bot DL) (proj1_sig d) x.

Lemma demand_universe_wf {X} (EX : encoding X) (U : list X) :
  FinSet.wf EX (FinSet.of_list EX U).
Proof.
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Definition demand_clamp_map {X M} (EX : encoding X) (keys : FinSet.t X)
    (raw : Map.t X M) : Map.t X M :=
  Map.combine EX (fun key value =>
    match key with
    | Some _ => value
    | None => None
    end) keys raw.

Lemma demand_clamp_map_wf {X M} (EX : encoding X) (keys : FinSet.t X) (raw : Map.t X M) :
  FinSet.wf EX keys -> Map.wf EX (demand_clamp_map EX keys raw).
Proof.
  intros Hkeys p x value Hget; unfold demand_clamp_map, Map.combine in Hget.
  rewrite Trie.get_combine in Hget by reflexivity.
  destruct (Trie.get p keys) as [[key []]|] eqn:Hkey;
    destruct (Trie.get p raw) as [[other val]|];
    cbn [Map.combine_pair] in Hget; try discriminate.
  injection Hget as Heq Hvalue; subst x value; exact (Hkeys p key tt Hkey).
Qed.

Lemma demand_clamp_map_within {X M} (EX : encoding X) (U : list X) (raw : Map.t X M) :
  within_map EX U (demand_clamp_map EX (FinSet.of_list EX U) raw).
Proof.
  split; [apply demand_clamp_map_wf, demand_universe_wf|].
  intros x Hget; unfold demand_clamp_map in Hget; rewrite Map.get_combine in Hget by reflexivity.
  destruct (Map.get EX x (FinSet.of_list EX U)) as [[]|] eqn:Hkey; [|contradiction].
  apply (proj1 (FinSet.of_list_spec EX x U)); unfold FinSet.mem, Map.mem; rewrite Hkey; reflexivity.
Qed.

(** Prepare a canonical finite key index once; clamping then combines tries without list scans. *)
Definition demand_index_clamp {X M} (EX : encoding X) (U : list X) :
    Map.t X M -> finite_map EX U M :=
  let keys := FinSet.of_list EX U in
  fun raw => exist _ (demand_clamp_map EX keys raw) (demand_clamp_map_within EX U raw).

Lemma demand_index_clamp_get {X M} (EX : encoding X) (U : list X) (raw : Map.t X M) x :
  In x U -> Map.get EX x (proj1_sig (demand_index_clamp EX U raw)) = Map.get EX x raw.
Proof.
  intro Hin; cbn [demand_index_clamp proj1_sig]; unfold demand_clamp_map.
  rewrite Map.get_combine by reflexivity.
  pose proof (proj2 (FinSet.of_list_spec EX x U) Hin) as Hmem.
  unfold FinSet.mem, Map.mem in Hmem.
  destruct (Map.get EX x (FinSet.of_list EX U)) as [[]|]; [reflexivity|discriminate].
Qed.

(** Indexed clamping preserves the entire raw map of the finite-map reference operation. *)
Lemma demand_index_clamp_agrees {X M} (EX : encoding X) (U : list X) (raw : Map.t X M) :
  proj1_sig (demand_index_clamp EX U raw) = proj1_sig (finite_map_clamp EX U raw).
Proof.
  apply (Map.extensionality EX).
  - exact (proj1 (proj2_sig (demand_index_clamp EX U raw))).
  - exact (proj1 (proj2_sig (finite_map_clamp EX U raw))).
  - intro x; destruct (in_dec (encoded_eq_dec EX) x U) as [Hin|Hout].
    + rewrite demand_index_clamp_get, finite_map_clamp_get by exact Hin; reflexivity.
    + rewrite !finite_map_out by exact Hout; reflexivity.
Qed.

(** States agree on every part of every demanded value. *)
Definition demand_agreement {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) : agreement (finite_map EX (dvars dv) M) S :=
  {| agree := fun d s t => forall x,
       agree (dagree DD) (dget EX (dlat DD) d x) (dlookup dv s x) (dlookup dv t x) |}.

(** Combine repeated entries using the demand join. *)
Fixpoint exit_map {X M} (EX : encoding X) (DL : lattice M) (l : list (X * M)) : Map.t X M :=
  match l with
  | [] => Map.empty
  | (x, m) :: rest =>
    Map.union_with (join DL) (Map.set EX x m Map.empty) (exit_map EX DL rest)
  end.

Definition demand_retain {X M} (EX : encoding X) (defined : FinSet.t X)
    (d : Map.t X M) : Map.t X M :=
  Map.combine EX (fun a b =>
    match b with
    | Some _ => None
    | None => a
    end) d defined.

(** Prepare the definition-membership index before propagating a fact across an edge. *)
Definition demand_transfer {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
    E -> finite_map EX (dvars dv) M -> finite_map EX (dvars dv) M :=
  let clamp := demand_index_clamp EX (dvars dv) in
  fun e => let defined := FinSet.of_list EX (ddefs dv e) in
  let forced := exit_map EX (dlat DD) (dnec dv e) in
  fun d => clamp
    (Map.union_with (join (dlat DD)) (demand_retain EX defined (proj1_sig d))
      (Map.union_with (join (dlat DD)) forced
        (exit_map EX (dlat DD)
          (flat_map (fun x => dback dv e x (dget EX (dlat DD) d x)) (ddefs dv e))))).

(** Backward constraints seed every node and propagate demands across every listed edge. *)
Definition demand_system {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
    System.t N (dense_constraint N E) (finite_map EX (dvars dv) M) :=
  backward_system (cfg (dgraph dv))
    (fun n => finite_map_clamp EX (dvars dv) (exit_map EX (dlat DD) (dexit dv n)))
    (demand_transfer EX DD dv).

(** All variables named by the view belong to its duplicate-free universe. *)
Definition demand_vars_ok {S O N E X Cv M} (dv : demand_view S O N E X Cv M) : Prop :=
  NoDup (dvars dv) /\
  (forall e x m' y m'', In (y, m'') (dnec dv e ++ dback dv e x m') -> In y (dvars dv)) /\
  (forall n y m', In (y, m') (dexit dv n) -> In y (dvars dv)) /\
  (forall e x, In x (ddefs dv e) -> In x (dvars dv)).

(** The client connects demand agreement with matching steps and observable endings. *)
Record demand_laws {S O N E X Cv M} (m : semantics S O) (en : endings S) (inv : S -> Prop)
    (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M) : Prop := {
  d_view : graph_view_laws m (dgraph dv);
  d_no_stays : forall s l s', ~ stays (dgraph dv) s l s';
  d_frame : forall s l s' e x, inv s -> step m s l s' -> taken (dgraph dv) s l s' e ->
    ~ In x (ddefs dv e) -> dlookup dv s' x = dlookup dv s x;
  d_agreement : agreement_laws (demand_lattice EX DD dv) (demand_agreement EX DD dv) /\
    agreement_symmetric (demand_agreement EX DD dv);
  d_bot_agrees : forall u v, agree (dagree DD) (bot (dlat DD)) u v;
  d_back_bot : forall e x, dback dv e x (bot (dlat DD)) = nil;
  d_vars : demand_vars_ok dv;
  d_step : forall s l s' t e d, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    step m s l s' -> taken (dgraph dv) s l s' e ->
    agree (demand_agreement EX DD dv) (demand_transfer EX DD dv e d) s t ->
    exists t', step m t l t' /\ taken (dgraph dv) t l t' e /\
      agree (demand_agreement EX DD dv) d s' t';
  d_exits : forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    agree (demand_agreement EX DD dv)
      (finite_map_clamp EX (dvars dv) (exit_map EX (dlat DD) (dexit dv (point (dgraph dv) s))))
      s t ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t)
}.

Arguments d_view {S O N E X Cv M m en inv EX DD dv}.
Arguments d_no_stays {S O N E X Cv M m en inv EX DD dv}.
Arguments d_frame {S O N E X Cv M m en inv EX DD dv}.
Arguments d_agreement {S O N E X Cv M m en inv EX DD dv}.
Arguments d_bot_agrees {S O N E X Cv M m en inv EX DD dv}.
Arguments d_back_bot {S O N E X Cv M m en inv EX DD dv}.
Arguments d_vars {S O N E X Cv M m en inv EX DD dv}.
Arguments d_step {S O N E X Cv M m en inv EX DD dv}.
Arguments d_exits {S O N E X Cv M m en inv EX DD dv}.

(** Trap retention is a client-selected policy. *)
Inductive trap_policy : Type :=
  | KeepTraps
  | DropUnreadTraps.

(** Observable effects, resource stops and possible divergence always retain an instruction. *)
Definition effectful {I} (ef : effects I) (pol : trap_policy) (i : I) : bool :=
  observes ef i || writes ef i || allocates ef i || frees ef i || calls ef i || may_diverge ef i ||
  may_stop ef i || (may_trap ef i &&
    match pol with
    | KeepTraps => true
    | DropUnreadTraps => false
    end).

(** A constant demand is closed when it satisfies all backward constraints. *)
Definition demand_closed {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) : Prop :=
  post_solution (demand_lattice EX DD dv) (demand_system EX DD dv) (fun _ => d).

(** The reference closure system identifies every graph point with one unknown. *)
Definition closed_system {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
    System.t unit (dense_constraint N E) (finite_map EX (dvars dv) M) :=
  {| System.constraints := map Seed (Graph.nodes (cfg (dgraph dv))) ++
       map Flow (edges_of (cfg (dgraph dv)));
     System.target := fun _ => tt;
     System.rhs := fun c => match c with
       | Seed n => Query.Ret
           (finite_map_clamp EX (dvars dv) (exit_map EX (dlat DD) (dexit dv n)))
       | Flow e => Query.Ask tt (fun d => Query.Ret (demand_transfer EX DD dv e d))
       end |}.

(** Boolean demand requires equality exactly when the flag is true. *)
Definition bool_demand {Cv} : demand_domain bool Cv := DemandDomain bool_lattice bool_agree.

(** Adding payload demands specializes the same framework to observed value parts. *)
Definition observable_bits_view {S O N E X Cv M} (dv : demand_view S O N E X Cv M)
    (payload : E -> list (X * M)) : demand_view S O N E X Cv M :=
  {| dgraph := dgraph dv;
     ddefs := ddefs dv;
     dnec := fun e => dnec dv e ++ payload e;
     dback := dback dv;
     dexit := dexit dv;
     dlookup := dlookup dv;
     dvars := dvars dv |}.

(** * Generic semantic soundness *)

Lemma demand_step_agrees {S O N E X Cv M} (m : semantics S O) (en : endings S)
    (inv : S -> Prop) (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (sigma : N -> finite_map EX (dvars dv) M) :
  demand_laws m en inv EX DD dv ->
  step_agrees m (dgraph dv) (demand_agreement EX DD dv) inv (demand_transfer EX DD dv) sigma.
Proof.
  intro Hlaws; split.
  - intros e s l s' t Hs Ht Hp Hstep Htaken Hagree.
    exact (d_step Hlaws s l s' t e (sigma (Graph.target (cfg (dgraph dv)) e))
      Hs Ht Hp Hstep Htaken Hagree).
  - intros s l s' t Hs Ht Hp Hstep Hstay Hagree.
    exfalso; exact (d_no_stays Hlaws s l s' Hstay).
Qed.

(** * Occurrence-indexed closure worklist *)

Fixpoint demand_index {A} (start : nat) (rows : list A) : Map.t nat A :=
  match rows with
  | [] => Map.empty
  | row :: rest => Map.set nat_encoding start row (demand_index (Datatypes.S start) rest)
  end.

Lemma demand_index_wf {A} (rows : list A) start :
  Map.wf nat_encoding (demand_index start rows).
Proof.
  revert start; induction rows as [|row rest IH]; intro start; cbn [demand_index].
  - apply Map.wf_empty.
  - apply Map.wf_set; apply IH.
Qed.

Lemma demand_index_before {A} (rows : list A) start key : key < start ->
  Map.get nat_encoding key (demand_index start rows) = None.
Proof.
  revert start; induction rows as [|row rest IH]; intros start Hlt; cbn [demand_index].
  - apply Map.get_empty.
  - rewrite Map.get_set_other by lia; apply IH; lia.
Qed.

Lemma demand_index_sound {A} (rows : list A) start key row :
  Map.get nat_encoding key (demand_index start rows) = Some row -> In row rows.
Proof.
  revert start; induction rows as [|head rest IH]; intros start Hget; cbn [demand_index] in Hget.
  - rewrite Map.get_empty in Hget; discriminate.
  - destruct (Nat.eq_dec key start) as [Heq|Hne].
    + subst key; rewrite Map.get_set_same in Hget; injection Hget as Heq; subst row; now left.
    + rewrite Map.get_set_other in Hget by exact Hne; right; eapply IH; exact Hget.
Qed.

Lemma demand_index_complete {A} (rows : list A) start row :
  In row rows -> exists key, Map.get nat_encoding key (demand_index start rows) = Some row.
Proof.
  revert start; induction rows as [|head rest IH]; intros start Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst head; exists start; apply Map.get_set_same.
  - destruct (IH (Datatypes.S start) Hin) as [key Hget].
    assert (Hne : key <> start).
    { intro Heq; subst key; rewrite demand_index_before in Hget by lia; discriminate. }
    exists key; cbn [demand_index]; rewrite Map.get_set_other by exact Hne; exact Hget.
Qed.

Definition demand_row_keys {A} (index : Map.t nat A) : list nat :=
  map fst (Map.elements index).

Lemma demand_row_key_get {A} (index : Map.t nat A) key : Map.wf nat_encoding index ->
  In key (demand_row_keys index) <-> exists row, Map.get nat_encoding key index = Some row.
Proof.
  intro Hwf; unfold demand_row_keys; rewrite in_map_iff; split.
  - intros [[i row] [Heq Hin]]; cbn in Heq; subst i; exists row.
    apply Map.elements_sound; assumption.
  - intros [row Hget]; exists (key, row); split; [reflexivity|].
    apply (Map.elements_complete nat_encoding); assumption.
Qed.

(** All rows read the same unknown; occurrence keys require no client node or edge encoding. *)
Definition demand_indexed_system {A} (L : lattice A) (rows : list (A -> A)) :
    System.t unit nat A :=
  let index := demand_index 0 rows in
  {| System.constraints := demand_row_keys index;
     System.target := fun _ => tt;
     System.rhs := fun key => Query.Ask tt (fun a => Query.Ret
       (match Map.get nat_encoding key index with
        | Some row => row a
        | None => bot L
        end)) |}.

Definition demand_indexed_static {A} (L : lattice A) (rows : list (A -> A)) :
    System.static (demand_indexed_system L rows).
Proof.
  refine {| System.deps := fun _ => [tt]; System.side_targets := fun _ => [] |}.
  - intros key sigma x Hin; exact Hin.
  - intros key sigma x Hin; exact Hin.
Defined.

(** The finite index preserves exactly the closure inequalities of the supplied rows. *)
Lemma demand_indexed_post_iff {A} (L : lattice A) (rows : list (A -> A)) (sigma : unit -> A) :
  post_solution L (demand_indexed_system L rows) sigma <->
  forall row, In row rows -> leb L (row (sigma tt)) (sigma tt) = true.
Proof.
  split.
  - intros Hpost row Hin.
    destruct (demand_index_complete rows 0 row Hin) as [key Hget].
    assert (Hkey : In key (System.constraints (demand_indexed_system L rows))).
    { apply demand_row_key_get; [apply demand_index_wf|exists row; exact Hget]. }
    specialize (Hpost key Hkey); cbn [demand_indexed_system System.rhs Query.eval] in Hpost.
    rewrite Hget in Hpost; exact (proj1 Hpost).
  - intros Hrows key Hkey; split.
    + apply demand_row_key_get in Hkey; [|apply demand_index_wf].
      destruct Hkey as [row Hget].
      cbn [demand_indexed_system System.rhs Query.eval System.target]; rewrite Hget.
      apply Hrows; eapply demand_index_sound; exact Hget.
    + intros x a Hin; contradiction.
Qed.

Definition demand_rows {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) :
    list (finite_map EX (dvars dv) M -> finite_map EX (dvars dv) M) :=
  map (fun n => let seed := finite_map_clamp EX (dvars dv)
    (exit_map EX (dlat DD) (dexit dv n)) in fun _ => seed) (Graph.nodes (cfg (dgraph dv))) ++
  map (demand_transfer EX DD dv) (edges_of (cfg (dgraph dv))).

(** The executable occurrence index and the reference system have the same post-solutions. *)
Lemma demand_indexed_closed_iff {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (sigma : unit -> finite_map EX (dvars dv) M) :
  post_solution (demand_lattice EX DD dv)
    (demand_indexed_system (demand_lattice EX DD dv) (demand_rows EX DD dv)) sigma <->
  post_solution (demand_lattice EX DD dv) (closed_system EX DD dv) sigma.
Proof.
  rewrite demand_indexed_post_iff; unfold demand_rows; split.
  - intros Hrows [n|e] Hin; split; try (intros x a Hside; contradiction).
    + apply (Hrows (fun _ => finite_map_clamp EX (dvars dv)
        (exit_map EX (dlat DD) (dexit dv n)))).
      apply in_app_or in Hin; apply in_or_app; left; apply in_map_iff.
      destruct Hin as [Hin|Hin]; apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]].
      * injection Heq as Heq; subst x; exists n; auto.
      * discriminate.
    + apply (Hrows (demand_transfer EX DD dv e)).
      apply in_app_or in Hin; apply in_or_app; right; apply in_map_iff.
      destruct Hin as [Hin|Hin]; apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]].
      * discriminate.
      * injection Heq as Heq; subst x; exists e; auto.
  - intros Hpost row Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
      apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]]; subst row.
    + exact (proj1 (Hpost (Seed x) (in_or_app _ _ _ (or_introl (in_map _ _ _ Hx))))).
    + exact (proj1 (Hpost (Flow x) (in_or_app _ _ _ (or_intror (in_map _ _ _ Hx))))).
Qed.

Definition demand_distinct {X} (EX : encoding X) (U : list X) : list X :=
  FinSet.elements (FinSet.of_list EX U).

Lemma demand_distinct_spec {X} (EX : encoding X) (U : list X) x :
  In x (demand_distinct EX U) <-> In x U.
Proof.
  unfold demand_distinct; rewrite FinSet.elements_spec by apply demand_universe_wf.
  apply FinSet.of_list_spec.
Qed.

Definition demand_reindex {X M} (EX : encoding X) (U : list X) (d : finite_map EX U M) :
    finite_map EX (demand_distinct EX U) M.
Proof.
  refine (exist _ (proj1_sig d) _); split; [exact (proj1 (proj2_sig d))|].
  intros x Hget; apply demand_distinct_spec; exact (proj2 (proj2_sig d) x Hget).
Defined.

(** A duplicate-free key index supplies a height without changing the returned map carrier. *)
Definition demand_bool_height {X} (EX : encoding X) (U : list X) :
    monotone_height (finite_pointwise_lattice EX U bool_lattice).
Proof.
  pose (H := finite_pointwise_height EX (demand_distinct EX U)
    (FinSet.elements_nodup EX _ (demand_universe_wf EX U)) bool_laws bool_lub bool_height).
  unshelve refine (@MonotoneHeight _ _
    (@Height _ _ (fun d => rank (base_height H) (demand_reindex EX U d))
      (bound (base_height H)) _ _) _).
  - intro d; exact (rank_bounded (base_height H) (demand_reindex EX U d)).
  - intros a b Hbad; exact (join_rank_grows (base_height H)
      (demand_reindex EX U a) (demand_reindex EX U b) Hbad).
  - intros a b Hab; exact (rank_monotone H (demand_reindex EX U a) (demand_reindex EX U b) Hab).
Defined.

Definition demand_solver {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :=
  let L := demand_lattice EX bool_demand dv in
  let rows := demand_rows EX bool_demand dv in
  let sys := demand_indexed_system L rows in
  let static := demand_indexed_static L rows in
  solve_total unit_encoding nat_encoding L (finite_pointwise_laws EX _ _ bool_laws)
    (rpo_scheduler unit_encoding sys static) Joining sys static
    (inhabits (base_height (demand_bool_height EX (dvars dv)))).

(** An inflationary finite worklist returns a closed demand even for nonmonotone raw views. *)
Definition needed_values {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) : finite_map EX (dvars dv) bool :=
  proj1_sig (demand_solver EX dv) tt.

(** Dead values have no Boolean demand in the computed closed map. *)
Definition dead_value {S O N E X Cv} (EX : encoding X) (dv : demand_view S O N E X Cv bool)
    (x : X) : bool := negb (dget EX bool_lattice (needed_values EX dv) x).

Definition demand_worklist_run {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) (fuel : positive) :=
  let L := demand_lattice EX bool_demand dv in
  let rows := demand_rows EX bool_demand dv in
  let sys := demand_indexed_system L rows in
  let static := demand_indexed_static L rows in
  run_worklist unit_encoding nat_encoding L (rpo_scheduler unit_encoding sys static) Joining sys
    (Declared static (index_system unit_encoding sys static)) fuel.

(** A completed executable worklist run computes exactly the total producer's map. *)
Lemma needed_values_from_run {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) fuel result :
  demand_worklist_run EX dv fuel = Some result ->
  needed_values EX dv = lookup unit_encoding (demand_lattice EX bool_demand dv) result tt.
Proof.
  intro Hrun.
  pose (L := demand_lattice EX bool_demand dv).
  pose (rows := demand_rows EX bool_demand dv).
  pose (sys := demand_indexed_system L rows).
  pose (static := demand_indexed_static L rows).
  pose (sch := rpo_scheduler unit_encoding sys static).
  destruct (solve_total_run unit_encoding nat_encoding L sys sch Joining
    (finite_pointwise_laws EX _ _ bool_laws) static
    (inhabits (base_height (demand_bool_height EX (dvars dv))))) as [f Hfuel].
  destruct (Hfuel f (Pos.le_refl f)) as [m [Hfinished Heq]].
  pose proof (total_completed_runs_unique unit_encoding nat_encoding L sch Joining sys _
    f fuel m result Hfinished Hrun) as Hsame.
  rewrite Hsame in Heq.
  exact (f_equal (fun values => values tt) Heq).
Qed.

(** Initial states agreeing under any backward post-solution have identical behaviour. *)
Theorem demand_sound {S O N E X Cv M} (m : semantics S O) (en : endings S) (inv : S -> Prop)
    (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M)
    (sigma : N -> finite_map EX (dvars dv) M) (s0 t0 : S) :
  demand_laws m en inv EX DD dv -> invariant_of m inv ->
  post_solution (demand_lattice EX DD dv) (demand_system EX DD dv) sigma ->
  initial m s0 -> initial m t0 -> point (dgraph dv) t0 = point (dgraph dv) s0 ->
  agree (demand_agreement EX DD dv) (sigma (point (dgraph dv) s0)) s0 t0 ->
  same_behaviour m en s0 m en t0.
Proof.
  intros Hlaws Hinv Hpost Hs Ht Hp Hagree.
  eapply agreement_same_behaviour with
    (R := fun _ => demand_agreement EX DD dv) (inv := inv)
    (exitf := fun n => finite_map_clamp EX (dvars dv)
      (exit_map EX (dlat DD) (dexit dv n))) (bt := demand_transfer EX DD dv).
  - exact (d_view Hlaws).
  - exact (proj1 (d_agreement Hlaws)).
  - exact (proj2 (d_agreement Hlaws)).
  - exact Hinv.
  - apply demand_step_agrees with (en := en); exact Hlaws.
  - exact (d_exits Hlaws).
  - exact Hpost.
  - exact Hs.
  - exact Ht.
  - exact Hp.
  - exact Hagree.
Qed.

(** Closed demands also relate arbitrary states satisfying the invariant at one point. *)
Theorem closed_demand_sound {S O N E X Cv M} (m : semantics S O) (en : endings S)
    (inv : S -> Prop) (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) :
  demand_laws m en inv EX DD dv -> invariant_of m inv -> demand_closed EX DD dv d ->
  forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    agree (demand_agreement EX DD dv) d s t -> same_behaviour m en s m en t.
Proof.
  intros Hlaws Hinv Hpost s t Hs Ht Hp Hagree.
  eapply bisimilar_same_behaviour.
  - eapply agreement_bisimulation with
      (R := fun _ => demand_agreement EX DD dv) (inv := inv) (sigma := fun _ => d)
      (exitf := fun n => finite_map_clamp EX (dvars dv)
        (exit_map EX (dlat DD) (dexit dv n))) (bt := demand_transfer EX DD dv).
    + exact (d_view Hlaws).
    + exact (proj1 (d_agreement Hlaws)).
    + exact (proj2 (d_agreement Hlaws)).
    + exact Hinv.
    + apply demand_step_agrees with (en := en); exact Hlaws.
    + exact (d_exits Hlaws).
    + exact Hpost.
  - exact (conj Hp (conj Hs (conj Ht Hagree))).
Qed.

(** Changing only a bottom-demanded variable preserves behaviour under a closed demand. *)
Theorem dead_value_removable {S O N E X Cv M} (m : semantics S O) (en : endings S)
    (inv : S -> Prop) (EX : encoding X) (DD : demand_domain M Cv) (dv : demand_view S O N E X Cv M)
    (d : finite_map EX (dvars dv) M) (x : X) :
  demand_laws m en inv EX DD dv -> invariant_of m inv -> demand_closed EX DD dv d ->
  dget EX (dlat DD) d x = bot (dlat DD) ->
  forall s t, inv s -> inv t -> point (dgraph dv) t = point (dgraph dv) s ->
    (forall y, y <> x -> dlookup dv s y = dlookup dv t y) ->
    same_behaviour m en s m en t.
Proof.
  intros Hlaws Hinv Hclosed Hdead s t Hs Ht Hp Hsame.
  eapply closed_demand_sound; try eassumption.
  intro y; destruct (encoded_eq_dec EX y x) as [Heq|Hne].
  - subst y; rewrite Hdead; apply (d_bot_agrees Hlaws).
  - rewrite <- (Hsame y Hne).
    exact (agree_refl (proj1 (d_agreement Hlaws)) d s y).
Qed.

(** Identifying graph points preserves precisely the constant post-solutions. *)
Theorem closed_system_iff {S O N E X Cv M} (EX : encoding X) (DD : demand_domain M Cv)
    (dv : demand_view S O N E X Cv M) (d : finite_map EX (dvars dv) M) :
  post_solution (demand_lattice EX DD dv) (closed_system EX DD dv) (fun _ => d) <->
  demand_closed EX DD dv d.
Proof.
  unfold demand_closed, demand_system; rewrite backward_post_solution_iff.
  split.
  - intro Hpost; split; intros x Hin.
    + exact (proj1 (Hpost (Seed x) (in_or_app _ _ _ (or_introl (in_map _ _ _ Hin))))).
    + exact (proj1 (Hpost (Flow x) (in_or_app _ _ _ (or_intror (in_map _ _ _ Hin))))).
  - intros [Hseed Hflow] [n|e] Hin; split; cbn [closed_system System.rhs Query.eval Query.sides].
    + apply Hseed; cbn [closed_system System.constraints] in Hin.
      apply in_app_or in Hin; destruct Hin as [Hin|Hin]; apply in_map_iff in Hin;
        destruct Hin as [x [Heq Hx]]; [injection Heq as Heq; subst x; exact Hx|discriminate].
    + intros x a Hin'; contradiction.
    + apply Hflow; cbn [closed_system System.constraints] in Hin.
      apply in_app_or in Hin; destruct Hin as [Hin|Hin]; apply in_map_iff in Hin;
        destruct Hin as [x [Heq Hx]]; [discriminate|injection Heq as Heq; subst x; exact Hx].
    + intros x a Hin'; contradiction.
Qed.

(** Every view, including duplicate-variable and malformed-graph inputs, has a closed result. *)
Theorem needed_values_closed {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :
  demand_closed EX bool_demand dv (needed_values EX dv).
Proof.
  apply closed_system_iff, demand_indexed_closed_iff, demand_indexed_post_iff.
  exact (proj1 (demand_indexed_post_iff _ _ _) (proj2_sig (demand_solver EX dv))).
Qed.

(** * Boolean monotonicity and leastness *)

Lemma demand_bool_leb_iff {X} (EX : encoding X) (U : list X) (a b : finite_map EX U bool) :
  leb (finite_pointwise_lattice EX U bool_lattice) a b = true <->
  forall x, dget EX bool_lattice a x = true -> dget EX bool_lattice b x = true.
Proof.
  split.
  - intros Hab x Hx.
    pose proof (monotone_finite_pointwise_lookup EX U bool_lattice bool_laws x a b Hab) as Hle.
    change (implb (dget EX bool_lattice a x) (dget EX bool_lattice b x) = true) in Hle.
    rewrite Hx in Hle; exact Hle.
  - intro Hkeys; apply Map.forall2_spec; intros p value Hget.
    destruct (map_code_key EX _ p value (proj1 (proj2_sig a)) Hget) as [x Hcode]; subst p.
    change (Map.get EX x (proj1_sig a) = Some value) in Hget.
    change (implb value (dget EX bool_lattice b x) = true).
    destruct value; [|reflexivity]; apply Hkeys.
    unfold dget, pointwise_lookup; rewrite Hget; reflexivity.
Qed.

Lemma demand_bool_union_get {X} (EX : encoding X) (a b : Map.t X bool) x :
  pointwise_lookup EX false (Map.union_with orb a b) x =
  pointwise_lookup EX false a x || pointwise_lookup EX false b x.
Proof.
  unfold pointwise_lookup, Map.get; rewrite Map.code_get_union_with.
  destruct (Map.code_get (encode EX x) a) as [v|], (Map.code_get (encode EX x) b) as [w|];
    cbn [Trie.union_opt]; try reflexivity; symmetry; apply orb_false_r.
Qed.

Lemma demand_bool_exit_true {X} (EX : encoding X) (l : list (X * bool)) x :
  pointwise_lookup EX false (exit_map EX bool_lattice l) x = true <-> In (x, true) l.
Proof.
  induction l as [|[y b] rest IH].
  - cbn [exit_map In]; unfold pointwise_lookup; rewrite Map.get_empty; split;
      [discriminate|contradiction].
  - cbn [exit_map]; rewrite demand_bool_union_get, orb_true_iff, IH.
    destruct (encoded_eq_dec EX x y) as [Heq|Hne].
    + subst y; unfold pointwise_lookup at 1; rewrite Map.get_set_same.
      cbn [In]; destruct b; cbn; intuition congruence.
    + unfold pointwise_lookup at 1; rewrite Map.get_set_other by exact Hne.
      rewrite Map.get_empty; cbn [In]; intuition congruence.
Qed.

Lemma demand_bool_retain_get {X} (EX : encoding X) (defined : FinSet.t X)
    (d : Map.t X bool) x :
  pointwise_lookup EX false (demand_retain EX defined d) x =
  if FinSet.mem EX x defined then false else pointwise_lookup EX false d x.
Proof.
  unfold pointwise_lookup, demand_retain; rewrite Map.get_combine by reflexivity.
  unfold FinSet.mem, Map.mem; destruct (Map.get EX x defined) as [[]|]; reflexivity.
Qed.

Lemma demand_bool_transfer_true {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) (e : E) (d : finite_map EX (dvars dv) bool) x :
  dget EX bool_lattice (demand_transfer EX bool_demand dv e d) x = true <->
  In x (dvars dv) /\
  ((FinSet.mem EX x (FinSet.of_list EX (ddefs dv e)) = false /\
      dget EX bool_lattice d x = true) \/
    In (x, true) (dnec dv e) \/
    exists y, In y (ddefs dv e) /\ In (x, true) (dback dv e y (dget EX bool_lattice d y))).
Proof.
  destruct (in_dec (encoded_eq_dec EX) x (dvars dv)) as [Hin|Hout].
  - unfold dget, demand_transfer, bool_demand; cbn [dlat].
    unfold pointwise_lookup at 1; rewrite demand_index_clamp_get by exact Hin.
    change (pointwise_lookup EX false
      (Map.union_with orb (demand_retain EX (FinSet.of_list EX (ddefs dv e)) (proj1_sig d))
        (Map.union_with orb (exit_map EX bool_lattice (dnec dv e))
          (exit_map EX bool_lattice
            (flat_map (fun y => dback dv e y (dget EX bool_lattice d y)) (ddefs dv e))))) x =
      true <-> In x (dvars dv) /\
      ((FinSet.mem EX x (FinSet.of_list EX (ddefs dv e)) = false /\
          dget EX bool_lattice d x = true) \/
        In (x, true) (dnec dv e) \/
        exists y, In y (ddefs dv e) /\
          In (x, true) (dback dv e y (dget EX bool_lattice d y)))).
    rewrite !demand_bool_union_get, !orb_true_iff, !demand_bool_exit_true.
    rewrite demand_bool_retain_get, in_flat_map.
    fold (dget EX bool_lattice d x).
    destruct (FinSet.mem EX x (FinSet.of_list EX (ddefs dv e))); cbn; intuition discriminate.
  - assert (Hzero : dget EX bool_lattice (demand_transfer EX bool_demand dv e d) x = false).
    { unfold dget, pointwise_lookup; rewrite finite_map_out by exact Hout; reflexivity. }
    rewrite Hzero; split; [discriminate|intros [Hin _]; contradiction].
Qed.

(** Empty false-demand propagation makes every Boolean edge transfer monotone. *)
Lemma demand_bool_transfer_monotone {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :
  (forall e x, dback dv e x false = nil) -> forall e,
  monotone_fun (demand_lattice EX bool_demand dv) (demand_lattice EX bool_demand dv)
    (demand_transfer EX bool_demand dv e).
Proof.
  intros Hstrict e a b Hab; apply demand_bool_leb_iff; intros x Hx.
  apply demand_bool_transfer_true in Hx; apply demand_bool_transfer_true.
  destruct Hx as [Hin [Hkeep|[Hforced|[y [Hy Hback]]]]]; split; try exact Hin.
  - left; destruct Hkeep as [Hnot Hneeded]; split; [exact Hnot|].
    exact (proj1 (demand_bool_leb_iff EX _ a b) Hab x Hneeded).
  - right; left; exact Hforced.
  - right; right; exists y; split; [exact Hy|].
    destruct (dget EX bool_lattice a y) eqn:Ha.
    + pose proof (proj1 (demand_bool_leb_iff EX _ a b) Hab y Ha) as Hb.
      rewrite Hb; exact Hback.
    + rewrite Hstrict in Hback; contradiction.
Qed.

Lemma demand_rows_monotone {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) :
  (forall e x, dback dv e x false = nil) -> forall row,
  In row (demand_rows EX bool_demand dv) ->
  monotone_fun (demand_lattice EX bool_demand dv) (demand_lattice EX bool_demand dv) row.
Proof.
  intros Hstrict row Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
    apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]]; subst row.
  - intros a b Hab; apply (leb_refl (finite_pointwise_laws EX _ _ bool_laws)).
  - apply demand_bool_transfer_monotone; exact Hstrict.
Qed.

Lemma demand_indexed_monotone {A} (L : lattice A) (rows : list (A -> A)) :
  lattice_laws L -> (forall row, In row rows -> monotone_fun L L row) ->
  monotone_system L (demand_indexed_system L rows).
Proof.
  intros Hlaws Hrows key Hkey; split.
  - intros sigma tau Hle; cbn [demand_indexed_system System.rhs Query.eval].
    destruct (Map.get nat_encoding key (demand_index 0 rows)) as [row|] eqn:Hget.
    + apply Hrows; [eapply demand_index_sound; exact Hget|apply Hle].
    + apply (leb_refl Hlaws).
  - intros sigma tau Hle x a Hin; contradiction.
Qed.

(** Under false-demand strictness, the computed closed demand is below every closed demand. *)
Theorem needed_values_least {S O N E X Cv} (EX : encoding X)
    (dv : demand_view S O N E X Cv bool) (d : finite_map EX (dvars dv) bool) :
  (forall e x, dback dv e x false = nil) ->
  demand_closed EX bool_demand dv d ->
  leb (demand_lattice EX bool_demand dv) (needed_values EX dv) d = true.
Proof.
  intros Hstrict Hclosed.
  pose (L := demand_lattice EX bool_demand dv).
  pose (rows := demand_rows EX bool_demand dv).
  pose (sys := demand_indexed_system L rows).
  pose (static := demand_indexed_static L rows).
  pose (HL := finite_pointwise_laws EX (dvars dv) bool_lattice bool_laws).
  pose (HT := inhabits (base_height (demand_bool_height EX (dvars dv)))).
  pose proof (solve_total_least unit_encoding nat_encoding L sys
    (rpo_scheduler unit_encoding sys static) HL static HT
    (finite_pointwise_lub EX _ _ bool_laws bool_lub)) as Hleast.
  assert (Hmono : monotone_system L sys).
  { apply demand_indexed_monotone; [exact HL|apply demand_rows_monotone; exact Hstrict]. }
  specialize (Hleast Hmono).
  assert (Hpost : post_solution L sys (fun _ => d)).
  { apply demand_indexed_closed_iff, closed_system_iff; exact Hclosed. }
  exact (proj2 Hleast (fun _ => d) Hpost tt).
Qed.

(** * Effects and two-program erasure *)

(** A non-effectful instruction is silent, preserves heap and frames, and cannot stop. *)
Theorem non_effectful_step_pure {S O I H} (m : semantics S O) (en : endings S) (ef : effects I)
    (ev : effects_view S I H) (pol : trap_policy) :
  effects_laws m en ef ev ->
  forall s l s' i, reachable_state m s -> instr_at ev s = Some i -> step m s l s' ->
    effectful ef pol i = false ->
    l = nil /\ depth ev s' = depth ev s /\ heap ev s' = heap ev s /\ ~ stopped en s /\
    (pol = KeepTraps -> ~ trapped en s).
Proof.
  intros Hlaws s l s' i Hreach Hinstr Hstep Heffect.
  unfold effectful in Heffect; repeat rewrite orb_false_iff in Heffect.
  destruct Heffect as [[[[[[[Hobs Hwrite] Halloc] Hfree] Hcall] Hdiverge] Hstop] Htrap].
  split; [exact (silent Hlaws s l s' i Hreach Hinstr Hstep Hobs)|].
  split; [exact (frame_frame Hlaws s l s' i Hreach Hinstr Hstep Hcall)|].
  split; [exact (heap_frame Hlaws s l s' i Hreach Hinstr Hstep Hwrite Halloc Hfree)|].
  split.
  - intro Hstopped; pose proof (stop_covered Hlaws s i Hreach Hinstr Hstopped); congruence.
  - intros Hpol Htrapped; subst pol; rewrite andb_true_r in Htrap.
    pose proof (trap_covered Hlaws s i Hreach Hinstr Htrapped); congruence.
Qed.

(** Erasure replaces selected original instructions by no-ops on the same graph. *)
Record erasure (S O N E X Cv I : Type) : Type := Erasure {
  er_demand : demand_view S O N E X Cv bool;
  er_graph : graph_view S O N E;
  er_erased : E -> bool;
  er_instr : E -> option I
}.

Arguments er_demand {S O N E X Cv I}.
Arguments er_graph {S O N E X Cv I}.
Arguments er_erased {S O N E X Cv I}.
Arguments er_instr {S O N E X Cv I}.

(** The original run is reachable and, for the trap-dropping policy, untrapped. *)
Definition er_inv {S O} (pol : trap_policy) (m : semantics S O) (en : endings S) (s : S) : Prop :=
  reachable_state m s /\
  match pol with
  | KeepTraps => True
  | DropUnreadTraps => ~ trapped en s
  end.

(** Original and transformed states agree on every needed variable. *)
Definition er_agree {S O N E X Cv I} (EX : encoding X) (er : erasure S O N E X Cv I)
    (d : finite_map EX (dvars (er_demand er)) bool) (s t : S) : Prop :=
  agree (demand_agreement EX bool_demand (er_demand er)) d s t.

(** Local kept-edge, no-op and ending laws connect the two programs. *)
Record erasure_laws {S O N E X Cv I} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (m' : semantics S O) (en' : endings S) (EX : encoding X) (er : erasure S O N E X Cv I)
    (d : finite_map EX (dvars (er_demand er)) bool) : Prop := {
  er_cfg : cfg (er_graph er) = cfg (dgraph (er_demand er));
  er_view : graph_view_laws m' (er_graph er);
  er_no_stays : forall t l t', ~ stays (er_graph er) t l t';
  er_kept_forth : forall e s l s1 t, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m s l s1 ->
    taken (dgraph (er_demand er)) s l s1 e -> er_erased er e = false ->
    agree (demand_agreement EX bool_demand (er_demand er))
      (demand_transfer EX bool_demand (er_demand er) e d) s t ->
    exists t', step m' t l t' /\ taken (er_graph er) t l t' e /\ er_agree EX er d s1 t';
  er_kept_back : forall e s t l t1, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m' t l t1 ->
    taken (er_graph er) t l t1 e -> er_erased er e = false ->
    agree (demand_agreement EX bool_demand (er_demand er))
      (demand_transfer EX bool_demand (er_demand er) e d) s t ->
    exists s1, step m s l s1 /\ taken (dgraph (er_demand er)) s l s1 e /\ er_agree EX er d s1 t1;
  er_nop_forth : forall e s l s1 t, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m s l s1 ->
    taken (dgraph (er_demand er)) s l s1 e -> er_erased er e = true ->
    exists t', step m' t nil t' /\ taken (er_graph er) t nil t' e /\
      forall x, dlookup (er_demand er) t' x = dlookup (er_demand er) t x;
  er_nop_back : forall e s t l t1, er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> step m' t l t1 ->
    taken (er_graph er) t l t1 e -> er_erased er e = true ->
    l = nil /\ (forall x, dlookup (er_demand er) t1 x = dlookup (er_demand er) t x) /\
    exists s1 l0, step m s l0 s1 /\ taken (dgraph (er_demand er)) s l0 s1 e;
  er_ends : forall s t k, k <> EndStuck -> er_inv pol m en s -> reachable_state m' t ->
    point (er_graph er) t = point (dgraph (er_demand er)) s -> er_agree EX er d s t ->
    (ends_as m en k s <-> ends_as m' en' k t)
}.

Arguments er_cfg {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_view {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_no_stays {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_kept_forth {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_kept_back {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_nop_forth {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_nop_back {S O N E X Cv I pol m en m' en' EX er d}.
Arguments er_ends {S O N E X Cv I pol m en m' en' EX er d}.

(** No state reached from the designated original state traps. *)
Definition never_traps {S O} (m : semantics S O) (en : endings S) (s0 : S) : Prop :=
  forall tr t, exec m s0 tr t -> ~ trapped en t.

(** Trap retention gives equality; trap dropping gives equality conditional on an untrapped run. *)
Definition dce_conclusion {S O} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (s0 : S) (m' : semantics S O) (en' : endings S) (t0 : S) : Prop :=
  match pol with
  | KeepTraps => same_behaviour m en s0 m' en' t0
  | DropUnreadTraps => never_traps m en s0 -> same_behaviour m en s0 m' en' t0
  end.

Section ErasureProof.
Context {S O N E X Cv I H : Type} (pol : trap_policy) (m : semantics S O) (en : endings S)
  (m' : semantics S O) (en' : endings S) (inv : S -> Prop) (EX : encoding X)
  (er : erasure S O N E X Cv I) (d : finite_map EX (dvars (er_demand er)) bool)
  (ef : effects I) (ev : effects_view S I H).
Hypotheses
  (Hdemand : demand_laws m en inv EX bool_demand (er_demand er))
  (Hinvariant : invariant_of m inv)
  (Hclosed : demand_closed EX bool_demand (er_demand er) d)
  (Heffects : effects_laws m en ef ev)
  (Herasure : erasure_laws pol m en m' en' EX er d)
  (Hdead : forall e x, er_erased er e = true -> In x (ddefs (er_demand er) e) ->
    dget EX bool_lattice d x = false)
  (Hpure : forall e, er_erased er e = true ->
    exists i, er_instr er e = Some i /\ effectful ef pol i = false)
  (Hinstruct : forall s l s' e, reachable_state m s -> step m s l s' ->
    taken (dgraph (er_demand er)) s l s' e -> instr_at ev s = er_instr er e).

Lemma erasure_silent e s l s' : reachable_state m s -> step m s l s' ->
  taken (dgraph (er_demand er)) s l s' e -> er_erased er e = true -> l = nil.
Proof.
  intros Hreach Hstep Htaken Herased; destruct (Hpure e Herased) as [i [Hi Hpurei]].
  apply (proj1 (non_effectful_step_pure m en ef ev pol Heffects s l s' i Hreach
    ltac:(rewrite (Hinstruct s l s' e Hreach Hstep Htaken); exact Hi) Hstep Hpurei)).
Qed.

Lemma erasure_input_agrees e s t : In e (edges_of (cfg (dgraph (er_demand er)))) ->
  er_agree EX er d s t ->
  agree (demand_agreement EX bool_demand (er_demand er))
    (demand_transfer EX bool_demand (er_demand er) e d) s t.
Proof.
  intros He Hagree; apply (agree_antitone (proj1 (d_agreement Hdemand)) _ d s t); [|exact Hagree].
  exact (proj2 (proj1 (backward_post_solution_iff _ _ _ _ _) Hclosed) e He).
Qed.

Lemma erasure_successor_points e s l s' t l' t' :
  reachable_state m s -> reachable_state m' t -> step m s l s' -> step m' t l' t' ->
  taken (dgraph (er_demand er)) s l s' e -> taken (er_graph er) t l' t' e ->
  point (er_graph er) t' = point (dgraph (er_demand er)) s'.
Proof.
  intros Hs Ht Hstep Hstep' Htaken Htaken'.
  pose proof (proj2 (taken_edge (d_view Hdemand) s l s' e Hs Hstep Htaken)) as Htarget.
  pose proof (proj2 (taken_edge (er_view Herasure) t l' t' e Ht Hstep' Htaken')) as Htarget'.
  rewrite (er_cfg Herasure) in Htarget'; congruence.
Qed.

Lemma erasure_nop_agrees e s l s' t t' : inv s -> step m s l s' ->
  taken (dgraph (er_demand er)) s l s' e -> er_erased er e = true -> er_agree EX er d s t ->
  (forall x, dlookup (er_demand er) t' x = dlookup (er_demand er) t x) ->
  er_agree EX er d s' t'.
Proof.
  intros Hinv Hstep Htaken Herased Hagree Hnop x Hneeded.
  change (dget EX bool_lattice d x = true) in Hneeded.
  assert (Hnot : ~ In x (ddefs (er_demand er) e)).
  { intro Hdef; rewrite (Hdead e x Herased Hdef) in Hneeded; discriminate. }
  rewrite (d_frame Hdemand s l s' e x Hinv Hstep Htaken Hnot), Hnop.
  exact (Hagree x Hneeded).
Qed.

Lemma erasure_edge_forth e s l s' t : inv s -> er_inv pol m en s -> reachable_state m' t ->
  point (er_graph er) t = point (dgraph (er_demand er)) s -> er_agree EX er d s t ->
  step m s l s' -> taken (dgraph (er_demand er)) s l s' e ->
  exists t', step m' t l t' /\ point (er_graph er) t' = point (dgraph (er_demand er)) s' /\
    er_agree EX er d s' t'.
Proof.
  intros Hinv Hs Ht Hp Hagree Hstep Htaken; destruct (er_erased er e) eqn:Herased.
  - pose proof (erasure_silent e s l s' (proj1 Hs) Hstep Htaken Herased) as Hnil; subst l.
    destruct (er_nop_forth Herasure e s [] s' t Hs Ht Hp Hstep Htaken Herased)
      as [t' [Hstep' [Htaken' Hnop]]].
    exists t'; split; [exact Hstep'|]; split.
    + exact (erasure_successor_points e s [] s' t [] t'
        (proj1 Hs) Ht Hstep Hstep' Htaken Htaken').
    + exact (erasure_nop_agrees e s [] s' t t' Hinv Hstep Htaken Herased Hagree Hnop).
  - assert (He : In e (edges_of (cfg (dgraph (er_demand er))))).
    { exact (proj1 (view_taken_edge m _ s l s' e (d_view Hdemand) (proj1 Hs) Hstep Htaken)). }
    destruct (er_kept_forth Herasure e s l s' t Hs Ht Hp Hstep Htaken Herased
      (erasure_input_agrees e s t He Hagree)) as [t' [Hstep' [Htaken' Hagree']]].
    exists t'; split; [exact Hstep'|]; split.
    + exact (erasure_successor_points e s l s' t l t' (proj1 Hs) Ht Hstep Hstep' Htaken Htaken').
    + exact Hagree'.
Qed.

Lemma erasure_edge_back e s t l t' : inv s -> er_inv pol m en s -> reachable_state m' t ->
  point (er_graph er) t = point (dgraph (er_demand er)) s -> er_agree EX er d s t ->
  step m' t l t' -> taken (er_graph er) t l t' e ->
  exists s', step m s l s' /\ point (er_graph er) t' = point (dgraph (er_demand er)) s' /\
    er_agree EX er d s' t'.
Proof.
  intros Hinv Hs Ht Hp Hagree Hstep' Htaken'; destruct (er_erased er e) eqn:Herased.
  - destruct (er_nop_back Herasure e s t l t' Hs Ht Hp Hstep' Htaken' Herased)
      as [Hnil [Hnop [s' [l0 [Hstep Htaken]]]]]; subst l.
    pose proof (erasure_silent e s l0 s' (proj1 Hs) Hstep Htaken Herased) as Hnil; subst l0.
    exists s'; split; [exact Hstep|]; split.
    + exact (erasure_successor_points e s [] s' t [] t'
        (proj1 Hs) Ht Hstep Hstep' Htaken Htaken').
    + exact (erasure_nop_agrees e s [] s' t t' Hinv Hstep Htaken Herased Hagree Hnop).
  - assert (He : In e (edges_of (cfg (dgraph (er_demand er))))).
    { rewrite <- (er_cfg Herasure).
      exact (proj1 (view_taken_edge m' _ t l t' e (er_view Herasure) Ht Hstep' Htaken')). }
    destruct (er_kept_back Herasure e s t l t' Hs Ht Hp Hstep' Htaken' Herased
      (erasure_input_agrees e s t He Hagree)) as [s' [Hstep [Htaken Hagree']]].
    exists s'; split; [exact Hstep|]; split.
    + exact (erasure_successor_points e s l s' t l t' (proj1 Hs) Ht Hstep Hstep' Htaken Htaken').
    + exact Hagree'.
Qed.

Context (s0 : S).
Hypotheses (Hs0 : initial m s0)
  (Hsafe : forall tr s, exec m s0 tr s ->
    match pol with
    | KeepTraps => True
    | DropUnreadTraps => ~ trapped en s
    end).

(** Coupling a pair to the same original run keeps the trap-dropping invariant constructive. *)
Definition erasure_run_relation (s t : S) : Prop :=
  (exists tr, exec m s0 tr s) /\ reachable_state m' t /\
  point (er_graph er) t = point (dgraph (er_demand er)) s /\ er_agree EX er d s t.

Lemma erasure_run_invariant s tr : exec m s0 tr s -> inv s /\ er_inv pol m en s.
Proof.
  intro Hrun; split.
  - eapply invariant_exec; [exact Hinvariant|exact Hrun|].
    exact (inv_initial Hinvariant s0 Hs0).
  - split; [exists s0, tr; auto|exact (Hsafe tr s Hrun)].
Qed.

Lemma erasure_run_forth s t l s' : erasure_run_relation s t -> step m s l s' ->
  exists t', step m' t l t' /\ erasure_run_relation s' t'.
Proof.
  intros [[tr Hrun] [Ht [Hp Hagree]]] Hstep.
  destruct (erasure_run_invariant s tr Hrun) as [Hinv Hs].
  destruct (edge_covers (d_view Hdemand) s l s' (proj1 Hs) Hstep) as [Hstay|[e Htaken]].
  - exfalso; exact (d_no_stays Hdemand s l s' Hstay).
  - destruct (erasure_edge_forth e s l s' t Hinv Hs Ht Hp Hagree Hstep Htaken)
      as [t' [Hstep' [Hp' Hagree']]].
    exists t'; split; [exact Hstep'|].
    split; [exists (tr ++ l); eapply exec_app; [exact Hrun|apply exec_one; exact Hstep]|].
    split; [eapply reachable_state_step; eassumption|auto].
Qed.

Lemma erasure_run_back s t l t' : erasure_run_relation s t -> step m' t l t' ->
  exists s', step m s l s' /\ erasure_run_relation s' t'.
Proof.
  intros [[tr Hrun] [Ht [Hp Hagree]]] Hstep'.
  destruct (erasure_run_invariant s tr Hrun) as [Hinv Hs].
  destruct (edge_covers (er_view Herasure) t l t' Ht Hstep') as [Hstay|[e Htaken']].
  - exfalso; exact (er_no_stays Herasure t l t' Hstay).
  - destruct (erasure_edge_back e s t l t' Hinv Hs Ht Hp Hagree Hstep' Htaken')
      as [s' [Hstep [Hp' Hagree']]].
    exists s'; split; [exact Hstep|].
    split; [exists (tr ++ l); eapply exec_app; [exact Hrun|apply exec_one; exact Hstep]|].
    split; [eapply reachable_state_step; eassumption|auto].
Qed.

Lemma erasure_run_endings s t k : erasure_run_relation s t ->
  (ends_as m en k s <-> ends_as m' en' k t).
Proof.
  intro Hrel; destruct Hrel as [[tr Hrun] [Ht [Hp Hagree]]].
  destruct (erasure_run_invariant s tr Hrun) as [Hinv Hs].
  assert (Hends : forall k, k <> EndStuck -> (ends_as m en k s <-> ends_as m' en' k t)).
  { intros ending Hnot; exact (er_ends Herasure s t ending Hnot Hs Ht Hp Hagree). }
  destruct k; try (apply Hends; discriminate).
  assert (Hrunning : running m s <-> running m' t).
  { split; intros [l [u Hstep]].
    - destruct (erasure_run_forth s t l u
        (conj (ex_intro _ tr Hrun) (conj Ht (conj Hp Hagree))) Hstep) as [v [Hmatch _]].
      exists l, v; exact Hmatch.
    - destruct (erasure_run_back s t l u
        (conj (ex_intro _ tr Hrun) (conj Ht (conj Hp Hagree))) Hstep) as [v [Hmatch _]].
      exists l, v; exact Hmatch. }
  pose proof (Hends EndFinal ltac:(discriminate)) as Hfinal.
  pose proof (Hends EndTrap ltac:(discriminate)) as Htrap.
  pose proof (Hends EndStop ltac:(discriminate)) as Hstop.
  cbn [ends_as] in *; unfold stuck; tauto.
Qed.

Lemma erasure_run_bisimulation : bisimulation m en m' en' erasure_run_relation.
Proof.
  constructor.
  - exact erasure_run_endings.
  - exact erasure_run_forth.
  - exact erasure_run_back.
Qed.
End ErasureProof.

(** Erasing pure instructions defining only dead values preserves the policy's behaviour claim. *)
Theorem dce_sound {S O N E X Cv I H} (pol : trap_policy) (m : semantics S O) (en : endings S)
    (m' : semantics S O) (en' : endings S) (inv : S -> Prop) (EX : encoding X)
    (er : erasure S O N E X Cv I) (d : finite_map EX (dvars (er_demand er)) bool)
    (ef : effects I) (ev : effects_view S I H) (s0 t0 : S) :
  demand_laws m en inv EX bool_demand (er_demand er) -> invariant_of m inv ->
  demand_closed EX bool_demand (er_demand er) d ->
  effects_laws m en ef ev -> erasure_laws pol m en m' en' EX er d ->
  (forall e x, er_erased er e = true -> In x (ddefs (er_demand er) e) ->
     dget EX bool_lattice d x = false) ->
  (forall e, er_erased er e = true ->
     exists i, er_instr er e = Some i /\ effectful ef pol i = false) ->
  (forall s l s' e, reachable_state m s -> step m s l s' ->
     taken (dgraph (er_demand er)) s l s' e -> instr_at ev s = er_instr er e) ->
  initial m s0 -> initial m' t0 -> point (er_graph er) t0 = point (dgraph (er_demand er)) s0 ->
  er_agree EX er d s0 t0 -> dce_conclusion pol m en s0 m' en' t0.
Proof.
  intros Hdemand Hinv Hclosed Heffects Herasure Hdead Hpure Hinstruct Hs0 Ht0 Hp Hagree.
  assert (Hsound : (forall tr s, exec m s0 tr s ->
      match pol with
      | KeepTraps => True
      | DropUnreadTraps => ~ trapped en s
      end) ->
    same_behaviour m en s0 m' en' t0).
  { intro Hsafe; eapply bisimilar_same_behaviour.
    - exact (erasure_run_bisimulation pol m en m' en' inv EX er d ef ev
        Hdemand Hinv Hclosed Heffects Herasure Hdead Hpure Hinstruct s0 Hs0 Hsafe).
    - split; [exists []; constructor|].
      split; [exists t0, []; split; [exact Ht0|constructor]|auto]. }
  destruct pol; cbn [dce_conclusion].
  - apply Hsound; intros tr s Hrun; constructor.
  - intro Hsafe; apply Hsound; exact Hsafe.
Qed.
