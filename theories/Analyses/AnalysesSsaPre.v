(** * SSA PRE reset phases and direct placement

    Indexed reset closures and Finalize construct cached versions and translated edge placements.
    For example, a reload can select the version saved by an earlier computation.
    Builds on: AnalysesSsaPreGraph, AnalysesSsaLiveQuery and Collections maps. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators
  GraphLengauerTarjan GraphFrontier.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesAvailable AnalysesSsaLiveQuery
  AnalysesSsaPreGraph.
Import List.ListNotations.

(** A cache version comes from entry, a real computation, an insertion or a parameter edge. *)
Inductive pre_version (E U : Type) : Type :=
  | PreInitial (u : U)
  | PreComputed (e : E) (u : U)
  | PreInserted (e : E) (u : U)
  | PreMerged (parameter_edge : E) (u : U).
Arguments PreInitial {E U}.
Arguments PreComputed {E U}.
Arguments PreInserted {E U}.
Arguments PreMerged {E U}.

(** Each version retains the exact expression whose value it stores. *)
Definition pre_version_expr {E U} (version : pre_version E U) : U :=
  match version with
  | PreInitial u | PreComputed _ u | PreInserted _ u | PreMerged _ u => u
  end.

(** Distinct cache origins and exact expression identities have injective positive encodings. *)
Definition pre_version_encoding {E U} (EE : encoding E) (EU : encoding U) :
    encoding (pre_version E U).
Proof.
  pose (codes := sum_encoding EU (sum_encoding (pair_encoding EE EU)
    (sum_encoding (pair_encoding EE EU) (pair_encoding EE EU)))).
  refine (Encoding _ (fun version => encode codes (match version with
    | PreInitial u => inl u
    | PreComputed e u => inr (inl (e,u))
    | PreInserted e u => inr (inr (inl (e,u)))
    | PreMerged e u => inr (inr (inr (e,u)))
    end)) _).
  intros version version' Hcode; apply (encode_injective codes) in Hcode.
  destruct version, version'; inversion Hcode; subst; reflexivity.
Defined.

(** A plan records edge computations, reloads and edge-specific parameter selections. *)
Record pre_plan (E U : Type) : Type := PrePlan {
  pre_insertions : Map.t E (FinSet.t U);
  pre_deletions : Map.t E (FinSet.t U);
  pre_reload_versions : Map.t E (pre_version E U);
  pre_phi_versions : Map.t ((E * E) * U) (pre_version E U)
}.
Arguments PrePlan {E U}.
Arguments pre_insertions {E U}.
Arguments pre_deletions {E U}.
Arguments pre_reload_versions {E U}.
Arguments pre_phi_versions {E U}.

(** Insertion membership defaults to the empty edge set. *)
Definition pre_inserted {E U} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (e : E) (u : U) : bool :=
  FinSet.mem EU u (live_index_get EE e (pre_insertions p)).

(** Deletion membership defaults to the empty edge set. *)
Definition pre_deleted {E U} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (e : E) (u : U) : bool :=
  FinSet.mem EU u (live_index_get EE e (pre_deletions p)).

(** Insertions extend generation after the original edge while retaining its graph and kills. *)
Definition pre_extended_view {S O N E U C} (EE : encoding E) (EU : encoding U)
    (v : pre_expression_view S O N E U C) (p : pre_plan E U) : genkill_view S O N E U C :=
  GenKillView (gkview (pre_genkill v))
    (fun e => gen (pre_genkill v) e ++
      FinSet.elements (live_index_get EE e (pre_insertions p)))
    (kill (pre_genkill v)) (uval (pre_genkill v)).

(** A version is available at entry or at the target of its defining edge. *)
Definition pre_version_point {S O N E U C} (v : pre_expression_view S O N E U C)
    (version : pre_version E U) : option N :=
  match version with
  | PreInitial _ => nth_error (Graph.entries (cfg (gkview (pre_genkill v)))) 0
  | PreComputed e _ | PreInserted e _ | PreMerged e _ =>
    Some (Graph.target (cfg (gkview (pre_genkill v))) e)
  end.

(** Only a version's own defining edge can write its cache slot. *)
Definition pre_version_written {E U} (EE : encoding E) (e : E)
    (version : pre_version E U) : bool :=
  match version with
  | PreInitial _ => false
  | PreComputed d _ | PreInserted d _ | PreMerged d _ =>
    Pos.eqb (encode EE e) (encode EE d)
  end.

(** Parameter updates read the selected predecessor version from the same old cache. *)
Definition pre_phi_update {E U C} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (incoming parameter_edge : E)
    (old : pre_version E U -> option C) (version : pre_version E U) : option C :=
  match version with
  | PreMerged d u =>
    if Pos.eqb (encode EE d) (encode EE parameter_edge) then
      match Map.get (pair_encoding (pair_encoding EE EE) EU) ((d,incoming),u)
        (pre_phi_versions p) with
      | Some selected => old selected
      | None => old version
      end
    else old version
  | _ => old version
  end.

(** Legal insertions are pure and non-killing, and reload versions dominate their uses. *)
Definition pre_placement_legal {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (v : pre_expression_view S O N E U C) (p : pre_plan E U) : Prop :=
  (forall e u, In e (edges_of (cfg (gkview (pre_genkill v)))) ->
    pre_inserted EE EU p e u = true ->
    pre_total_pure v u = true /\ kill (pre_genkill v) e u = false /\
    exists parameter_edge merged_u,
      Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter_edge,e),merged_u)
        (pre_phi_versions p) = Some (PreInserted e u)) /\
  (forall e u, In e (edges_of (cfg (gkview (pre_genkill v)))) ->
    pre_deleted EE EU p e u = true ->
    pre_recomputed v e = Some u /\ pre_total_pure v u = true /\
    exists version n, Map.get EE e (pre_reload_versions p) = Some version /\
      pre_version_point v version = Some n /\
      dominates (cfg (gkview (pre_genkill v))) n
        (Graph.source (cfg (gkview (pre_genkill v))) e)).

(** The three exposed flags complement the independent least reset closures. *)
Record ssapre_facts (B U : Type) : Type := SsaPreFacts {
  ssapre_downsafe : Map.t (B * U) bool;
  ssapre_can_available : Map.t (B * U) bool;
  ssapre_later : Map.t (B * U) bool
}.
Arguments SsaPreFacts {B U}.
Arguments ssapre_downsafe {B U}.
Arguments ssapre_can_available {B U}.
Arguments ssapre_later {B U}.

(** Missing Boolean entries denote false. *)
Definition live_bool_get {K} (EK : encoding K) (k : K) (m : Map.t K bool) : bool :=
  match Map.get EK k m with
  | Some b => b
  | None => false
  end.

(** Unsafe down-safety resets flow backward through phi operands without intervening real uses. *)
Inductive ssapre_down_unsafe {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) : B * U -> Prop :=
  | ssapre_down_seed : forall b u,
      FinSet.mem (pair_encoding EB EU) (b,u) (frg_unsafe_seeds f) = true ->
      ssapre_down_unsafe EB EU EBE f (b,u)
  | ssapre_down_step : forall b u b' u' be op,
      ssapre_down_unsafe EB EU EBE f (b',u') ->
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be)
        (frg_phi_operands f) = Some op ->
      frg_operand_real_use op = false -> frg_operand_version op = FrPhi b u ->
      ssapre_down_unsafe EB EU EBE f (b,u).

(** Can-availability resets start at non-down-safe unavailable operands and flow to their users. *)
Inductive ssapre_cannot {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) (down : B * U -> bool) :
    B * U -> Prop :=
  | ssapre_cannot_seed : forall b u be op x,
      down (b,u) = false ->
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
        (frg_phi_operands f) = Some op ->
      frg_operand_version op = FrUnavailable x -> ssapre_cannot EB EU EBE f down (b,u)
  | ssapre_cannot_step : forall b u b' u' be op,
      ssapre_cannot EB EU EBE f down (b,u) -> down (b',u') = false ->
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be)
        (frg_phi_operands f) = Some op ->
      frg_operand_real_use op = false -> frg_operand_version op = FrPhi b u ->
      ssapre_cannot EB EU EBE f down (b',u').

(** Later resets start at real-use operands and flow through can-available phi users. *)
Inductive ssapre_later_reset {B BE E U} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U) (can : B * U -> bool) :
    B * U -> Prop :=
  | ssapre_later_seed : forall b u be op,
      can (b,u) = true ->
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
        (frg_phi_operands f) = Some op -> frg_operand_real_use op = true ->
      (forall x, frg_operand_version op <> FrUnavailable x) ->
      ssapre_later_reset EB EU EBE f can (b,u)
  | ssapre_later_step : forall b u b' u' be op,
      ssapre_later_reset EB EU EBE f can (b,u) -> can (b',u') = true ->
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b',u'),be)
        (frg_phi_operands f) = Some op -> frg_operand_version op = FrPhi b u ->
      ssapre_later_reset EB EU EBE f can (b',u').

(** * Indexed finite reset closure *)

Local Definition pre_reset_add_arc {K} (EK : encoding K)
    (idx : Map.t K (FinSet.t K)) (arc : K * K) : Map.t K (FinSet.t K) :=
  Map.set EK (fst arc) (FinSet.add EK (snd arc) (live_index_get EK (fst arc) idx)) idx.

Local Definition pre_reset_index {K} (EK : encoding K) (arcs : list (K * K)) :=
  fold_left (pre_reset_add_arc EK) arcs Map.empty.

Local Definition pre_reset_graph {K} (EK : encoding K) (seeds : list K)
    (arcs : list (K * K)) : Graph.t K (K * K) :=
  let idx := pre_reset_index EK arcs in
  Graph.Make seeds
    (FinSet.elements (FinSet.of_list EK (seeds ++ flat_map (fun ab => [fst ab; snd ab]) arcs)))
    (fun k => map (fun k' => (k,k')) (FinSet.elements (live_index_get EK k idx))) fst snd.

Local Definition pre_reset_closure {K} (EK : encoding K) (seeds : list K)
    (arcs : list (K * K)) : FinSet.t K :=
  let g := pre_reset_graph EK seeds arcs in
  visited (dfs (prepare EK g) FinSet.empty seeds).

Inductive pre_reset_reached {K} (seeds : list K) (arcs : list (K * K)) : K -> Prop :=
  | pre_reset_seed : forall k, In k seeds -> pre_reset_reached seeds arcs k
  | pre_reset_step : forall k k', pre_reset_reached seeds arcs k -> In (k,k') arcs ->
      pre_reset_reached seeds arcs k'.

Local Lemma pre_reset_add_member {K} (EK : encoding K) idx a k k' :
  FinSet.mem EK k' (live_index_get EK k (pre_reset_add_arc EK idx a)) = true <->
    (k,k') = a \/ FinSet.mem EK k' (live_index_get EK k idx) = true.
Proof.
  destruct a as [x y].
  change (FinSet.mem EK k' (live_index_get EK k
    (Map.set EK x (FinSet.add EK y (live_index_get EK x idx)) idx)) = true <->
    (k,k') = (x,y) \/ FinSet.mem EK k' (live_index_get EK k idx) = true).
  destruct (Pos.eq_dec (encode EK k) (encode EK x)) as [Heq|Hne].
  - apply (encode_injective EK) in Heq; subst k.
    unfold live_index_get; rewrite Map.get_set_same, FinSet.mem_add.
    split; intros [H|H]; [left; subst k'; reflexivity|right; exact H| |right; exact H].
    injection H as H; left; exact H.
  - assert (k <> x) as Hkeys by (intro Heq; subst k; contradiction).
    unfold live_index_get; rewrite Map.get_set_other by exact Hkeys.
    split; [auto|intros [Heq|Hmem]; [injection Heq as Heq; contradiction|exact Hmem]].
Qed.

Local Lemma pre_reset_fold_member {K} (EK : encoding K) arcs idx k k' :
  FinSet.mem EK k' (live_index_get EK k (fold_left (pre_reset_add_arc EK) arcs idx)) = true <->
    In (k,k') arcs \/ FinSet.mem EK k' (live_index_get EK k idx) = true.
Proof.
  revert idx; induction arcs as [|a arcs IH]; intro idx.
  - change (FinSet.mem EK k' (live_index_get EK k idx) = true <->
      False \/ FinSet.mem EK k' (live_index_get EK k idx) = true); tauto.
  - change (FinSet.mem EK k' (live_index_get EK k
      (fold_left (pre_reset_add_arc EK) arcs (pre_reset_add_arc EK idx a))) = true <->
      In (k,k') (a :: arcs) \/ FinSet.mem EK k' (live_index_get EK k idx) = true).
    rewrite IH, pre_reset_add_member; cbn; intuition congruence.
Qed.

Local Lemma pre_reset_index_member {K} (EK : encoding K) arcs k k' :
  FinSet.mem EK k' (live_index_get EK k (pre_reset_index EK arcs)) = true <->
    In (k,k') arcs.
Proof.
  unfold pre_reset_index; rewrite pre_reset_fold_member.
  unfold live_index_get; rewrite Map.get_empty, FinSet.mem_empty; intuition discriminate.
Qed.

Local Lemma pre_reset_index_wf {K} (EK : encoding K) arcs :
  forall k, FinSet.wf EK (live_index_get EK k (pre_reset_index EK arcs)).
Proof.
  assert (forall idx, (forall k, FinSet.wf EK (live_index_get EK k idx)) ->
    forall k, FinSet.wf EK (live_index_get EK k (fold_left (pre_reset_add_arc EK) arcs idx)))
    as Hfold.
  { induction arcs as [|[x y] arcs IH]; intros idx Hidx k; cbn [fold_left].
    - apply Hidx.
    - apply IH; intro q; unfold pre_reset_add_arc; cbn [fst snd].
      destruct (Pos.eq_dec (encode EK q) (encode EK x)) as [Heq|Hne].
      + apply (encode_injective EK) in Heq; subst q; unfold live_index_get at 1.
        rewrite Map.get_set_same; apply Map.wf_set, Hidx.
      + unfold live_index_get at 1; rewrite Map.get_set_other
          by (intro Heq; subst q; contradiction); apply Hidx. }
  apply Hfold; intro k; unfold live_index_get; rewrite Map.get_empty; apply Map.wf_empty.
Qed.

Local Lemma pre_reset_graph_out {K} (EK : encoding K) seeds arcs k arc :
  In arc (Graph.out (pre_reset_graph EK seeds arcs) k) <-> fst arc = k /\ In arc arcs.
Proof.
  destruct arc as [x y]; unfold pre_reset_graph; cbn [Graph.out fst].
  rewrite in_map_iff; split.
  - intros [z [Heq Hin]]; injection Heq as -> ->; split; [reflexivity|].
    apply (proj1 (pre_reset_index_member EK arcs x y)), (proj1 (FinSet.elements_spec EK _ _
      (pre_reset_index_wf EK arcs _))); exact Hin.
  - intros [-> Hin]; exists y; split; [reflexivity|].
    apply (proj2 (FinSet.elements_spec EK _ _ (pre_reset_index_wf EK arcs _))),
      (proj2 (pre_reset_index_member EK arcs k y)); exact Hin.
Qed.

Local Lemma pre_reset_list_wf {K} (EK : encoding K) (keys : list K) :
  FinSet.wf EK (FinSet.of_list EK keys).
Proof.
  apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Local Lemma pre_reset_graph_ready {K} (EK : encoding K) seeds arcs :
  ready EK (pre_reset_graph EK seeds arcs) (prepare EK (pre_reset_graph EK seeds arcs)).
Proof.
  assert (forall k, In k (seeds ++ flat_map (fun ab => [fst ab; snd ab]) arcs) ->
    In k (Graph.nodes (pre_reset_graph EK seeds arcs))) as Hnode.
  { intros k Hin; unfold pre_reset_graph; cbn [Graph.nodes].
    apply (proj2 (FinSet.elements_spec EK _ _ (pre_reset_list_wf EK _))),
      FinSet.of_list_spec; exact Hin. }
  apply prepare_ready.
  - constructor.
    + apply (FinSet.elements_nodup EK), pre_reset_list_wf.
    + intros k Hin; apply Hnode, in_or_app; left; exact Hin.
    + intros k arc Hin; apply pre_reset_graph_out in Hin; exact (proj1 Hin).
    + intros k [x y] Hk Hin; apply pre_reset_graph_out in Hin.
      apply Hnode, in_or_app; right; apply in_flat_map.
      exists (x,y); cbn; split; [exact (proj2 Hin)|auto].
  - intro k; unfold pre_reset_graph; cbn [Graph.out].
    apply nodup_map_injective.
    + intros x y Heq; injection Heq; auto.
    + apply (FinSet.elements_nodup EK), pre_reset_index_wf.
Qed.

Local Lemma pre_reset_closure_exact {K} (EK : encoding K) seeds arcs k :
  FinSet.mem EK k (pre_reset_closure EK seeds arcs) = true <->
    pre_reset_reached seeds arcs k.
Proof.
  unfold pre_reset_closure.
  rewrite (reachable_dfs EK _ _ k (pre_reset_graph_ready EK seeds arcs)); split.
  - intro Hreach; induction Hreach as [k Hin|[x y] Hreach IH Hin].
    + apply pre_reset_seed; exact Hin.
    + apply pre_reset_graph_out in Hin; eapply pre_reset_step; eauto; exact (proj2 Hin).
  - intro Hreach; induction Hreach as [k Hin|x y Hreach IH Hin].
    + apply reachable_entry; exact Hin.
    + apply (@reachable_step K (K * K) (pre_reset_graph EK seeds arcs) (x,y)); [exact IH|].
      apply pre_reset_graph_out; split; [reflexivity|exact Hin].
Qed.

Local Definition pre_reset_flags {K} (EK : encoding K) (keys : list K)
    (flag : K -> bool) : Map.t K bool :=
  fold_right (fun k m => Map.set EK k (flag k) m) Map.empty keys.

Local Lemma pre_reset_flags_get {K} (EK : encoding K) keys flag k :
  In k keys -> live_bool_get EK k (pre_reset_flags EK keys flag) = flag k.
Proof.
  induction keys as [|q keys IH]; intro Hin; [contradiction|].
  unfold pre_reset_flags in *; cbn [fold_right].
  destruct (Pos.eq_dec (encode EK k) (encode EK q)) as [Heq|Hne].
  - apply (encode_injective EK) in Heq; subst q; unfold live_bool_get.
    rewrite Map.get_set_same; reflexivity.
  - unfold live_bool_get at 1; rewrite Map.get_set_other
      by (intro Heq; subst q; contradiction).
    apply IH; destruct Hin as [Heq|Hin]; [subst q; contradiction|exact Hin].
Qed.

Local Definition pre_reset_emit {B BE E U X}
    (emit : B * U -> BE -> frg_operand B E U -> list X)
    (links : list (((B * U) * BE) * frg_operand B E U)) : list X :=
  flat_map (fun link => emit (fst (fst link)) (snd (fst link)) (snd link)) links.

Local Definition pre_down_arcs {B BE E U}
    (links : list (((B * U) * BE) * frg_operand B E U)) : list ((B * U) * (B * U)) :=
  pre_reset_emit (fun k _ op =>
    if frg_operand_real_use op then [] else
    match frg_operand_version op with
    | FrPhi b u => [(k,(b,u))]
    | _ => []
    end) links.

Local Definition pre_cannot_seeds {B BE E U} (down : B * U -> bool)
    (links : list (((B * U) * BE) * frg_operand B E U)) : list (B * U) :=
  pre_reset_emit (fun k _ op =>
    if down k then [] else
    match frg_operand_version op with
    | FrUnavailable _ => [k]
    | _ => []
    end) links.

Local Definition pre_cannot_arcs {B BE E U} (down : B * U -> bool)
    (links : list (((B * U) * BE) * frg_operand B E U)) : list ((B * U) * (B * U)) :=
  pre_reset_emit (fun k _ op =>
    if down k || frg_operand_real_use op then [] else
    match frg_operand_version op with
    | FrPhi b u => [((b,u),k)]
    | _ => []
    end) links.

Local Definition pre_later_seeds {B BE E U} (can : B * U -> bool)
    (links : list (((B * U) * BE) * frg_operand B E U)) : list (B * U) :=
  pre_reset_emit (fun k _ op =>
    if can k && frg_operand_real_use op then
      match frg_operand_version op with
      | FrUnavailable _ => []
      | _ => [k]
      end
    else []) links.

Local Definition pre_later_arcs {B BE E U} (can : B * U -> bool)
    (links : list (((B * U) * BE) * frg_operand B E U)) : list ((B * U) * (B * U)) :=
  pre_reset_emit (fun k _ op =>
    if can k then
      match frg_operand_version op with
      | FrPhi b u => [((b,u),k)]
      | _ => []
      end
    else []) links.

(** The solver indexes phi-operand incidences once per phase and visits each reset once. *)
Definition solve_ssapre {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : ssapre_facts B U :=
  let EK := pair_encoding EB EU in
  let keys := FinSet.elements (frg_phi_index f) in
  let links := Map.elements (frg_phi_operands f) in
  let unsafe := pre_reset_closure EK (FinSet.elements (frg_unsafe_seeds f))
    (pre_down_arcs links) in
  let down := pre_reset_flags EK keys (fun k => negb (FinSet.mem EK k unsafe)) in
  let get_down := fun k => live_bool_get EK k down in
  let cannot := pre_reset_closure EK (pre_cannot_seeds get_down links)
    (pre_cannot_arcs get_down links) in
  let can := pre_reset_flags EK keys (fun k => negb (FinSet.mem EK k cannot)) in
  let get_can := fun k => live_bool_get EK k can in
  let reset := pre_reset_closure EK (pre_later_seeds get_can links)
    (pre_later_arcs get_can links) in
  SsaPreFacts down can
    (pre_reset_flags EK keys (fun k => get_can k && negb (FinSet.mem EK k reset))).

Local Lemma pre_reset_emit_spec {B BE E U X} (EB : encoding B) (EU : encoding U)
    (EBE : encoding BE) (f : factored_redundancy_graph B BE E U)
    (emit : B * U -> BE -> frg_operand B E U -> list X) x :
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  (In x (pre_reset_emit emit (Map.elements (frg_phi_operands f))) <->
    exists k be op, Map.get (pair_encoding (pair_encoding EB EU) EBE) (k,be)
      (frg_phi_operands f) = Some op /\ In x (emit k be op)).
Proof.
  intro Hwf; unfold pre_reset_emit; rewrite in_flat_map; split.
  - intros [[[k be] op] [Hin Hemit]]; exists k, be, op; split; [|exact Hemit].
    eapply Map.elements_sound; eassumption.
  - intros [k [be [op [Hget Hemit]]]]; exists ((k,be),op); split; [|exact Hemit].
    eapply Map.elements_complete; eassumption.
Qed.

Section ResetExactness.
  Context {B BE E U : Type}.
  Variables (EB : encoding B) (EU : encoding U) (EBE : encoding BE)
    (f : factored_redundancy_graph B BE E U).
  Hypothesis Hlinks : Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f).
  Local Abbreviation links := (Map.elements (frg_phi_operands f)).
  Local Abbreviation lookup := (Map.get (pair_encoding (pair_encoding EB EU) EBE)).

  Local Lemma pre_down_arcs_spec : forall k k',
    In (k,k') (pre_down_arcs links) <-> exists be op,
      lookup (k,be) (frg_phi_operands f) = Some op /\ frg_operand_real_use op = false /\
      frg_operand_version op = FrPhi (fst k') (snd k').
  Proof.
    intros [b u] [b' u']; unfold pre_down_arcs; rewrite pre_reset_emit_spec by exact Hlinks.
    split.
    - intros [k [be [op [Hget Hin]]]]; destruct (frg_operand_real_use op) eqn:Hreal;
        [contradiction|].
      destruct (frg_operand_version op) as [x|x|e x|d x] eqn:Hversion;
        cbn in Hin; try contradiction.
      destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      exists be, op; repeat split; assumption.
    - intros [be [op [Hget [Hreal Hversion]]]]; exists (b,u), be, op.
      split; [exact Hget|]; rewrite Hreal, Hversion; left; reflexivity.
  Qed.

  Local Lemma pre_cannot_seeds_spec : forall down k,
    In k (pre_cannot_seeds down links) <-> down k = false /\ exists be op x,
      lookup (k,be) (frg_phi_operands f) = Some op /\
      frg_operand_version op = FrUnavailable x.
  Proof.
    intros down k; unfold pre_cannot_seeds; rewrite pre_reset_emit_spec by exact Hlinks.
    split.
    - intros [q [be [op [Hget Hin]]]]; destruct (down q) eqn:Hdown; [contradiction|].
      destruct (frg_operand_version op) as [x|x|e x|b x] eqn:Hversion;
        cbn in Hin; try contradiction.
      destruct Hin as [->|Hfalse]; [|contradiction]; split; [exact Hdown|].
      exists be, op, x; split; assumption.
    - intros [Hdown [be [op [x [Hget Hversion]]]]]; exists k, be, op; split; [exact Hget|].
      rewrite Hdown, Hversion; left; reflexivity.
  Qed.

  Local Lemma pre_cannot_arcs_spec : forall down k k',
    In (k,k') (pre_cannot_arcs down links) <-> down k' = false /\ exists be op,
      lookup (k',be) (frg_phi_operands f) = Some op /\ frg_operand_real_use op = false /\
      frg_operand_version op = FrPhi (fst k) (snd k).
  Proof.
    intros down [b u] [b' u']; unfold pre_cannot_arcs;
      rewrite pre_reset_emit_spec by exact Hlinks; split.
    - intros [q [be [op [Hget Hin]]]]; destruct (down q) eqn:Hdown;
        destruct (frg_operand_real_use op) eqn:Hreal; cbn in Hin; try contradiction.
      destruct (frg_operand_version op) as [x|x|e x|d x] eqn:Hversion;
        cbn in Hin; try contradiction.
      destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      split; [exact Hdown|]; exists be, op; repeat split; assumption.
    - intros [Hdown [be [op [Hget [Hreal Hversion]]]]]; exists (b',u'), be, op.
      split; [exact Hget|]; rewrite Hdown, Hreal, Hversion; left; reflexivity.
  Qed.

  Local Lemma pre_later_seeds_spec : forall can k,
    In k (pre_later_seeds can links) <-> can k = true /\ exists be op,
      lookup (k,be) (frg_phi_operands f) = Some op /\ frg_operand_real_use op = true /\
      forall x, frg_operand_version op <> FrUnavailable x.
  Proof.
    intros can k; unfold pre_later_seeds; rewrite pre_reset_emit_spec by exact Hlinks; split.
    - intros [q [be [op [Hget Hin]]]]; destruct (can q) eqn:Hcan;
        destruct (frg_operand_real_use op) eqn:Hreal; cbn in Hin; try contradiction.
      destruct (frg_operand_version op) as [x|x|e x|b x] eqn:Hversion;
        cbn in Hin; try contradiction.
      all: destruct Hin as [->|Hfalse]; [|contradiction].
      all: split; [exact Hcan|].
      all: exists be, op; split; [exact Hget|]; split; [exact Hreal|].
      all: intros y Heq; rewrite Hversion in Heq; discriminate.
    - intros [Hcan [be [op [Hget [Hreal Havailable]]]]]; exists k, be, op.
      split; [exact Hget|]; rewrite Hcan, Hreal.
      destruct (frg_operand_version op) eqn:Hversion; try (left; reflexivity).
      exfalso; exact (Havailable u eq_refl).
  Qed.

  Local Lemma pre_later_arcs_spec : forall can k k',
    In (k,k') (pre_later_arcs can links) <-> can k' = true /\ exists be op,
      lookup (k',be) (frg_phi_operands f) = Some op /\
      frg_operand_version op = FrPhi (fst k) (snd k).
  Proof.
    intros can [b u] [b' u']; unfold pre_later_arcs;
      rewrite pre_reset_emit_spec by exact Hlinks; split.
    - intros [q [be [op [Hget Hin]]]]; destruct (can q) eqn:Hcan; [|contradiction].
      destruct (frg_operand_version op) as [x|x|e x|d x] eqn:Hversion;
        cbn in Hin; try contradiction.
      destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
      split; [exact Hcan|]; exists be, op; split; assumption.
    - intros [Hcan [be [op [Hget Hversion]]]]; exists (b',u'), be, op.
      split; [exact Hget|]; rewrite Hcan, Hversion; left; reflexivity.
  Qed.

  Local Lemma pre_down_closure_exact : FinSet.wf (pair_encoding EB EU) (frg_unsafe_seeds f) ->
    forall k, FinSet.mem (pair_encoding EB EU) k
      (pre_reset_closure (pair_encoding EB EU) (FinSet.elements (frg_unsafe_seeds f))
        (pre_down_arcs links)) = true <-> ssapre_down_unsafe EB EU EBE f k.
  Proof.
    intros Hunsafe k; rewrite pre_reset_closure_exact; split.
    - intro Hreach; induction Hreach as [[b u] Hin|[b u] [b' u'] Hreach IH Hin].
      + apply ssapre_down_seed, (proj1 (FinSet.elements_spec _ _ _ Hunsafe)); exact Hin.
      + apply pre_down_arcs_spec in Hin; destruct Hin as [be [op [Hget [Hreal Hversion]]]].
        eapply ssapre_down_step; eassumption.
    - intro Hreset; induction Hreset as [b u Hseed|b u b' u' be op Hreset IH Hget Hreal Hversion].
      + apply pre_reset_seed, (proj2 (FinSet.elements_spec _ _ _ Hunsafe)); exact Hseed.
      + eapply pre_reset_step; [exact IH|]; apply pre_down_arcs_spec.
        exists be, op; repeat split; assumption.
  Qed.

  Local Lemma pre_cannot_closure_exact : forall down k,
    FinSet.mem (pair_encoding EB EU) k
      (pre_reset_closure (pair_encoding EB EU) (pre_cannot_seeds down links)
        (pre_cannot_arcs down links)) = true <-> ssapre_cannot EB EU EBE f down k.
  Proof.
    intros down k; rewrite pre_reset_closure_exact; split.
    - intro Hreach; induction Hreach as [[b u] Hin|[b u] [b' u'] Hreach IH Hin].
      + apply pre_cannot_seeds_spec in Hin; destruct Hin as [Hdown [be [op [x [Hget Hversion]]]]].
        eapply ssapre_cannot_seed; eassumption.
      + apply pre_cannot_arcs_spec in Hin.
        destruct Hin as [Hdown [be [op [Hget [Hreal Hversion]]]]].
        eapply ssapre_cannot_step; eassumption.
    - intro Hreset; induction Hreset as [b u be op x Hdown Hget Hversion|
        b u b' u' be op Hreset IH Hdown Hget Hreal Hversion].
      + apply pre_reset_seed, pre_cannot_seeds_spec; split; [exact Hdown|].
        exists be, op, x; split; assumption.
      + eapply pre_reset_step; [exact IH|]; apply pre_cannot_arcs_spec; split; [exact Hdown|].
        exists be, op; repeat split; assumption.
  Qed.

  Local Lemma pre_later_closure_exact : forall can k,
    FinSet.mem (pair_encoding EB EU) k
      (pre_reset_closure (pair_encoding EB EU) (pre_later_seeds can links)
        (pre_later_arcs can links)) = true <-> ssapre_later_reset EB EU EBE f can k.
  Proof.
    intros can k; rewrite pre_reset_closure_exact; split.
    - intro Hreach; induction Hreach as [[b u] Hin|[b u] [b' u'] Hreach IH Hin].
      + apply pre_later_seeds_spec in Hin; destruct Hin as [Hcan [be [op [Hget [Hreal Havail]]]]].
        eapply ssapre_later_seed; eassumption.
      + apply pre_later_arcs_spec in Hin; destruct Hin as [Hcan [be [op [Hget Hversion]]]].
        eapply ssapre_later_step; eassumption.
    - intro Hreset; induction Hreset as [b u be op Hcan Hget Hreal Havail|
        b u b' u' be op Hreset IH Hcan Hget Hversion].
      + apply pre_reset_seed, pre_later_seeds_spec; split; [exact Hcan|].
        exists be, op; repeat split; assumption.
      + eapply pre_reset_step; [exact IH|]; apply pre_later_arcs_spec; split; [exact Hcan|].
        exists be, op; split; assumption.
  Qed.
End ResetExactness.

Local Lemma pre_ssapre_reset_exact {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) :
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  FinSet.wf (pair_encoding EB EU) (frg_unsafe_seeds f) ->
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  forall b u, FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_downsafe facts) = true <->
      ~ ssapre_down_unsafe EB EU EBE f (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true <->
      ~ ssapre_cannot EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_downsafe facts)) (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_later facts) = true <->
      live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true /\
      ~ ssapre_later_reset EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_can_available facts)) (b,u)).
Proof.
  intros Hphi Hlinks Hunsafe; cbn zeta; intros b u Hmember.
  pose (keys := FinSet.elements (frg_phi_index f)).
  pose (links := Map.elements (frg_phi_operands f)).
  pose (unsafe := pre_reset_closure (pair_encoding EB EU)
    (FinSet.elements (frg_unsafe_seeds f)) (pre_down_arcs links)).
  pose (down := pre_reset_flags (pair_encoding EB EU) keys
    (fun k => negb (FinSet.mem (pair_encoding EB EU) k unsafe))).
  pose (get_down := fun k => live_bool_get (pair_encoding EB EU) k down).
  pose (cannot := pre_reset_closure (pair_encoding EB EU)
    (pre_cannot_seeds get_down links) (pre_cannot_arcs get_down links)).
  pose (can := pre_reset_flags (pair_encoding EB EU) keys
    (fun k => negb (FinSet.mem (pair_encoding EB EU) k cannot))).
  pose (get_can := fun k => live_bool_get (pair_encoding EB EU) k can).
  pose (reset := pre_reset_closure (pair_encoding EB EU)
    (pre_later_seeds get_can links) (pre_later_arcs get_can links)).
  assert (In (b,u) keys) as Hkey.
  { apply (proj2 (FinSet.elements_spec _ _ _ Hphi)); exact Hmember. }
  change ((get_down (b,u) = true <-> ~ ssapre_down_unsafe EB EU EBE f (b,u)) /\
    (get_can (b,u) = true <-> ~ ssapre_cannot EB EU EBE f get_down (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u)
      (pre_reset_flags (pair_encoding EB EU) keys
        (fun k => get_can k && negb (FinSet.mem (pair_encoding EB EU) k reset))) = true <->
      get_can (b,u) = true /\ ~ ssapre_later_reset EB EU EBE f get_can (b,u))).
  split; [|split].
  - unfold get_down, down; rewrite pre_reset_flags_get by exact Hkey.
    rewrite <- (pre_down_closure_exact EB EU EBE f Hlinks Hunsafe (b,u)).
    change (negb (FinSet.mem (pair_encoding EB EU) (b,u) unsafe) = true <->
      FinSet.mem (pair_encoding EB EU) (b,u) unsafe <> true).
    destruct (FinSet.mem (pair_encoding EB EU) (b,u) unsafe); cbn; intuition discriminate.
  - unfold get_can, can; rewrite pre_reset_flags_get by exact Hkey.
    rewrite <- (pre_cannot_closure_exact EB EU EBE f Hlinks get_down (b,u)).
    change (negb (FinSet.mem (pair_encoding EB EU) (b,u) cannot) = true <->
      FinSet.mem (pair_encoding EB EU) (b,u) cannot <> true).
    destruct (FinSet.mem (pair_encoding EB EU) (b,u) cannot); cbn; intuition discriminate.
  - rewrite pre_reset_flags_get by exact Hkey.
    rewrite <- (pre_later_closure_exact EB EU EBE f Hlinks get_can (b,u)).
    change (get_can (b,u) && negb (FinSet.mem (pair_encoding EB EU) (b,u) reset) = true <->
      get_can (b,u) = true /\ FinSet.mem (pair_encoding EB EU) (b,u) reset <> true).
    destruct (get_can (b,u)), (FinSet.mem (pair_encoding EB EU) (b,u) reset);
      cbn; intuition discriminate.
Qed.

(** The three computed flags are exactly the complements of the adopted least reset sets. *)
Theorem solve_ssapre_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  forall b u, FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_downsafe facts) = true <->
      ~ ssapre_down_unsafe EB EU EBE f (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true <->
      ~ ssapre_cannot EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_downsafe facts)) (b,u)) /\
    (live_bool_get (pair_encoding EB EU) (b,u) (ssapre_later facts) = true <->
      live_bool_get (pair_encoding EB EU) (b,u) (ssapre_can_available facts) = true /\
      ~ ssapre_later_reset EB EU EBE f
        (fun k => live_bool_get (pair_encoding EB EU) k (ssapre_can_available facts)) (b,u)).
Proof.
  intros Ha Hb Hn; cbn zeta.
  destruct (build_frg_indexes_wf EB EBE EN EE EV EU a)
    as [Hocc [Hfresh [Hphi [Hlinks Hunsafe]]]].
  apply pre_ssapre_reset_exact; assumption.
Qed.

(** * Direct Finalize and version resolution *)

Local Definition pre_finalize_will {B U} (EB : encoding B) (EU : encoding U)
    (facts : ssapre_facts B U) (k : B * U) : bool :=
  live_bool_get (pair_encoding EB EU) k (ssapre_can_available facts) &&
    negb (live_bool_get (pair_encoding EB EU) k (ssapre_later facts)).

Local Definition pre_finalize_insert_operand {B E U} (EB : encoding B) (EU : encoding U)
    (facts : ssapre_facts B U) (op : frg_operand B E U) : bool :=
  match frg_operand_version op with
  | FrUnavailable _ => true
  | FrPhi b u => negb (frg_operand_real_use op) && negb (pre_finalize_will EB EU facts (b,u))
  | _ => false
  end.

Local Definition pre_finalize_add_row {K X} (EK : encoding K)
    (rows : Map.t K (list X)) (item : K * X) : Map.t K (list X) :=
  Map.set EK (fst item) (snd item :: index_edges EK rows (fst item)) rows.

Local Definition pre_finalize_phi_rows {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) : Map.t N (list (B * U)) :=
  fold_left (pre_finalize_add_row EN)
    (flat_map (fun k => if pre_finalize_will EB EU facts k then
      [(Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) (fst k)), k)] else [])
      (FinSet.elements (frg_phi_index f))) Map.empty.

(** An indexed argument retains the original incoming edge and its complete FRG operand. *)
Record pre_finalize_argument (B BE E U : Type) : Type := PreFinalizeArgument {
  pre_arg_block : B;
  pre_arg_expression : U;
  pre_arg_block_edge : BE;
  pre_arg_point_edge : E;
  pre_arg_operand : frg_operand B E U
}.
Arguments PreFinalizeArgument {B BE E U}.
Arguments pre_arg_block {B BE E U}.
Arguments pre_arg_expression {B BE E U}.
Arguments pre_arg_block_edge {B BE E U}.
Arguments pre_arg_point_edge {B BE E U}.
Arguments pre_arg_operand {B BE E U}.

Local Definition pre_finalize_argument_rows {S O B BE N E V K C U}
    (EBE : encoding BE) (EN : encoding N) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : Map.t N (list (pre_finalize_argument B BE E U)) :=
  let points := pre_point_edge_index EBE (pre_ssa_points a) in
  fold_left (pre_finalize_add_row EN)
    (flat_map (fun link => let '(((b,u),be),op) := link in
      match Map.get EBE be points with
      | Some pe => [(Graph.source (live_graph (point_model (pre_ssa_points a))) pe,
          PreFinalizeArgument b u be pe op)]
      | None => []
      end) (Map.elements (frg_phi_operands f))) Map.empty.

Local Definition pre_finalize_scope B E U := Map.t (frg_version B E U) (pre_version E U).
Local Definition pre_finalize_work B E U := (pre_finalize_scope B E U * pre_plan E U)%type.

Local Definition pre_finalize_initial {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (versions : list (frg_version B E U)) :
    pre_finalize_scope B E U :=
  fold_left (fun scope version => match version with
    | FrInitial u => if pre_initial_available a u then
        Map.set (frg_version_encoding EB EE EU) version (PreInitial u) scope else scope
    | _ => scope
    end) versions Map.empty.

Local Definition pre_finalize_available {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (tree : dom_tree N)
    (scope : pre_finalize_scope B E U) (d : frg_version B E U) (u : U) (n : N) :
    option (pre_version E U) :=
  match Map.get (frg_version_encoding EB EE EU) d scope with
  | None => None
  | Some version =>
    if Pos.eqb (encode EU (pre_version_expr version)) (encode EU u) then
      match pre_version_point (pre_expression a) version with
      | Some q => if dominates_b EN tree q n then Some version else None
      | None => None
      end
    else None
  end.

Local Definition pre_finalize_define_phi {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (scope : pre_finalize_scope B E U)
    (k : B * U) : pre_finalize_scope B E U :=
  Map.set (frg_version_encoding EB EE EU) (FrPhi (fst k) (snd k))
    (PreMerged (parameter_edge (pre_ssa_points a) (fst k)) (snd k)) scope.

Local Definition pre_finalize_occurrence {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (tree : dom_tree N) (work : pre_finalize_work B E U) (e : E) : pre_finalize_work B E U :=
  let '(scope,p) := work in
  match pre_recomputed (pre_expression a) e, Map.get EE e (frg_occurrence_index f) with
  | Some u, Some d =>
    if pre_total_pure (pre_expression a) u then
      match pre_finalize_available EB EN EE EU a tree scope d u
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) with
      | Some version =>
        (scope, PrePlan (pre_insertions p) (pre_deletions p)
          (Map.set EE e version (pre_reload_versions p)) (pre_phi_versions p))
      | None =>
        (Map.set (frg_version_encoding EB EE EU) d (PreComputed e u) scope,p)
      end
    else work
  | _, _ => work
  end.

Local Definition pre_finalize_select {E U} (EE : encoding E) (EU : encoding U)
    (p : pre_plan E U) (parameter incoming : E) (u : U) (version : pre_version E U) :=
  PrePlan (pre_insertions p) (pre_deletions p) (pre_reload_versions p)
    (Map.set (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),u) version
      (pre_phi_versions p)).

Local Definition pre_finalize_argument_step {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (facts : ssapre_facts B U)
    (tree : dom_tree N) (scope : pre_finalize_scope B E U) (p : pre_plan E U)
    (arg : pre_finalize_argument B BE E U) : pre_plan E U :=
  let b := pre_arg_block arg in
  let u := pre_arg_expression arg in
  let incoming := pre_arg_point_edge arg in
  let parameter := parameter_edge (pre_ssa_points a) b in
  if pre_finalize_will EB EU facts (b,u) then
    match pre_phi_translate a (pre_arg_block_edge arg) u with
    | None => p
    | Some translated =>
      if pre_finalize_insert_operand EB EU facts (pre_arg_operand arg) then
        if pre_total_pure (pre_expression a) translated &&
            negb (kill (pre_genkill (pre_expression a)) incoming translated)
        then pre_finalize_select EE EU p parameter incoming u (PreInserted incoming translated)
        else p
      else
        match pre_finalize_available EB EN EE EU a tree scope
          (frg_operand_version (pre_arg_operand arg)) translated
          (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming) with
        | Some version => pre_finalize_select EE EU p parameter incoming u version
        | None => p
        end
    end
  else p.

Local Definition pre_finalize_node {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) (tree : dom_tree N)
    (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (phis : Map.t N (list (B * U)))
    (arguments : Map.t N (list (pre_finalize_argument B BE E U)))
    (work : pre_finalize_work B E U) (n : N) : pre_finalize_work B E U :=
  let '(scope,p) := work in
  let scope := fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope in
  let p := fold_left (pre_finalize_argument_step EB EN EE EU a facts tree scope)
    (index_edges EN arguments n) p in
  fold_left (pre_finalize_occurrence EB EN EE EU a f tree) (succ_edges points n) (scope,p).

Local Definition pre_finalize_table_step {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) (tree : dom_tree N)
    (points : prepared EN (live_graph (point_model (pre_ssa_points a))))
    (phis : Map.t N (list (B * U)))
    (arguments : Map.t N (list (pre_finalize_argument B BE E U)))
    (initial : pre_finalize_scope B E U)
    (work : Map.t N (pre_finalize_scope B E U) * pre_plan E U) (n : N) :=
  let '(outputs,p) := work in
  let scope := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end in
  let '(scope,p) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
    (scope,p) n in
  (Map.set EN n scope outputs,p).

Local Definition pre_finalize_add_expression {E U} (EE : encoding E) (EU : encoding U)
    (rows : Map.t E (FinSet.t U)) (item : E * U) : Map.t E (FinSet.t U) :=
  Map.set EE (fst item) (FinSet.add EU (snd item) (live_index_get EE (fst item) rows)) rows.

Local Definition pre_finalize_expression_rows {E U} (EE : encoding E) (EU : encoding U)
    (items : list (E * U)) : Map.t E (FinSet.t U) :=
  fold_left (pre_finalize_add_expression EE EU) items Map.empty.

Local Definition pre_finalize_materialize {S O N E U C} (EE : encoding E) (EU : encoding U)
    (v : pre_expression_view S O N E U C) (p : pre_plan E U) : pre_plan E U :=
  let insertions := pre_finalize_expression_rows EE EU
    (flat_map (fun binding => match snd binding with
    | PreInserted e u => [(e,u)]
    | _ => []
    end) (Map.elements (pre_phi_versions p))) in
  let deletions := pre_finalize_expression_rows EE EU (flat_map (fun binding =>
    match pre_recomputed v (fst binding) with
    | Some u => [(fst binding,u)]
    | None => []
    end) (Map.elements (pre_reload_versions p))) in
  PrePlan insertions deletions (pre_reload_versions p) (pre_phi_versions p).

Local Definition pre_finalize_build {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (facts : ssapre_facts B U) : pre_plan E U :=
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let parents := simple_lt_idom points in
  let search := dom_search points parents in
  let tree := DomTree parents (pre_num search) (post_num search) in
  let order := preorder search in
  let phis := pre_finalize_phi_rows EB EN EU a f facts in
  let arguments := pre_finalize_argument_rows EBE EN a f in
  let scope := pre_finalize_initial EB EE EU a (frg_versions f) in
  let result := fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments scope)
    order (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty) in
  snd result.

(** Finalize visits dominator preorder, resolves available class definitions and emits both maps. *)
Definition ssa_pre_place {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : pre_plan E U :=
  let f := build_frg EB EBE EN EE EV EU a in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  pre_finalize_materialize EE EU (pre_expression a)
    (pre_finalize_build EB EBE EN EE EV EU a f facts).

(** Only initial, computed and merged definitions enter the class-to-definition table. *)
Definition pre_finalize_regular {E U} (version : pre_version E U) : Prop :=
  match version with
  | PreInserted _ _ => False
  | _ => True
  end.

(** A reload has an eligible expression and a definition dominating that particular occurrence. *)
Definition pre_finalize_reload_property {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) e version : Prop :=
  exists u n, pre_recomputed (pre_expression a) e = Some u /\
    pre_total_pure (pre_expression a) u = true /\ pre_version_expr version = u /\
    pre_version_point (pre_expression a) version = Some n /\
    dominates (live_graph (point_model (pre_ssa_points a))) n
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e).

(** Each phi selection retains translation, edge identity and its inserted or dominating origin. *)
Definition pre_finalize_phi_property {S O B BE N E V K C U} (EBE : encoding BE)
    (a : pre_expr_ssa S O B BE N E V K C U) parameter incoming u version : Prop :=
  exists b be translated,
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming /\
    Graph.target (block_graph (pre_ssa_points a)) be = b /\
    parameter = parameter_edge (pre_ssa_points a) b /\
    pre_phi_translate a be u = Some translated /\ pre_version_expr version = translated /\
    ((version = PreInserted incoming translated /\
       pre_total_pure (pre_expression a) translated = true /\
       kill (pre_genkill (pre_expression a)) incoming translated = false) \/
     (pre_finalize_regular version /\ exists n,
       pre_version_point (pre_expression a) version = Some n /\
       dominates (live_graph (point_model (pre_ssa_points a))) n
         (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming))).

(** Finalize keeps canonical output maps and independently reviewable placement provenance. *)
Record pre_finalize_invariant {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (work : pre_finalize_work B E U) : Prop := {
  pre_finalize_scope_regular : forall d version,
    Map.get (frg_version_encoding EB EE EU) d (fst work) = Some version ->
    pre_finalize_regular version;
  pre_finalize_reload_wf : Map.wf EE (pre_reload_versions (snd work));
  pre_finalize_phi_wf : Map.wf (pair_encoding (pair_encoding EE EE) EU)
    (pre_phi_versions (snd work));
  pre_finalize_reloads_safe : forall e version,
    Map.get EE e (pre_reload_versions (snd work)) = Some version ->
    pre_finalize_reload_property a e version;
  pre_finalize_phis_safe : forall parameter incoming u version,
    Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),u)
      (pre_phi_versions (snd work)) = Some version ->
    pre_finalize_phi_property EBE a parameter incoming u version
}.

Local Lemma pre_finalize_get_set {K X} (EK : encoding K) (m : Map.t K X) k x q y :
  Map.get EK q (Map.set EK k x m) = Some y ->
    (q = k /\ y = x) \/ Map.get EK q m = Some y.
Proof.
  destruct (Pos.eq_dec (encode EK q) (encode EK k)) as [Heq|Hne].
  - apply (encode_injective EK) in Heq; subst q; rewrite Map.get_set_same.
    intro Hvalue; injection Hvalue as ->; left; split; reflexivity.
  - rewrite Map.get_set_other by (intro Heq; subst q; contradiction); auto.
Qed.

Local Lemma pre_finalize_available_spec {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (tree : dom_tree N) scope d u n version :
  (forall q n', dominates_b EN tree q n' = true ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n') ->
  (forall d' version', Map.get (frg_version_encoding EB EE EU) d' scope = Some version' ->
    pre_finalize_regular version') ->
  pre_finalize_available EB EN EE EU a tree scope d u n = Some version ->
  pre_finalize_regular version /\ pre_version_expr version = u /\ exists q,
    pre_version_point (pre_expression a) version = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q n.
Proof.
  intros Htree Hregular Havailable; unfold pre_finalize_available in Havailable.
  destruct (Map.get (frg_version_encoding EB EE EU) d scope) as [selected|] eqn:Hget;
    [|discriminate].
  destruct (Pos.eqb (encode EU (pre_version_expr selected)) (encode EU u)) eqn:Hexpr;
    [|discriminate].
  destruct (pre_version_point (pre_expression a) selected) as [q|] eqn:Hpoint;
    [|discriminate].
  destruct (dominates_b EN tree q n) eqn:Hdom; [|discriminate].
  injection Havailable as ->; split; [eapply Hregular; exact Hget|].
  split.
  - apply (encode_injective EU), Pos.eqb_eq; exact Hexpr.
  - exists q; split; [exact Hpoint|apply Htree; exact Hdom].
Qed.

Local Lemma pre_finalize_scope_set_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope p d version :
  pre_finalize_invariant EB EBE EE EU a (scope,p) -> pre_finalize_regular version ->
  pre_finalize_invariant EB EBE EE EU a
    (Map.set (frg_version_encoding EB EE EU) d version scope,p).
Proof.
  intros [Hregular Hreload_wf Hphi_wf Hreload Hphi] Hversion; constructor; try assumption.
  intros d' version' Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[Heq ->]|Hget]; [exact Hversion|eapply Hregular; exact Hget].
Qed.

Local Lemma pre_finalize_reload_set_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope p e version :
  pre_finalize_invariant EB EBE EE EU a (scope,p) -> pre_finalize_reload_property a e version ->
  pre_finalize_invariant EB EBE EE EU a (scope,
    PrePlan (pre_insertions p) (pre_deletions p)
      (Map.set EE e version (pre_reload_versions p)) (pre_phi_versions p)).
Proof.
  intros [Hregular Hreload_wf Hphi_wf Hreload Hphi] Hversion; constructor; try assumption.
  - apply Map.wf_set; exact Hreload_wf.
  - intros e' version' Hget; apply pre_finalize_get_set in Hget.
    destruct Hget as [[-> ->]|Hget]; [exact Hversion|eapply Hreload; exact Hget].
Qed.

Local Lemma pre_finalize_phi_set_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope p parameter incoming u version :
  pre_finalize_invariant EB EBE EE EU a (scope,p) ->
  pre_finalize_phi_property EBE a parameter incoming u version ->
  pre_finalize_invariant EB EBE EE EU a
    (scope,pre_finalize_select EE EU p parameter incoming u version).
Proof.
  intros [Hregular Hreload_wf Hphi_wf Hreload Hphi] Hversion; constructor; try assumption.
  - apply Map.wf_set; exact Hphi_wf.
  - intros parameter' incoming' u' version' Hget; apply pre_finalize_get_set in Hget.
    destruct Hget as [[Heq ->]|Hget].
    + inversion Heq; subst; exact Hversion.
    + eapply Hphi; exact Hget.
Qed.

Local Lemma pre_finalize_occurrence_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) tree work e :
  (forall q n, dominates_b EN tree q n = true ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n) ->
  pre_finalize_invariant EB EBE EE EU a work ->
  pre_finalize_invariant EB EBE EE EU a
    (pre_finalize_occurrence EB EN EE EU a f tree work e).
Proof.
  intros Htree Hinv; destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
    destruct (Map.get EE e (frg_occurrence_index f)) as [d|]; try exact Hinv.
  destruct (pre_total_pure (pre_expression a) u) eqn:Hpure; [|exact Hinv].
  destruct (pre_finalize_available EB EN EE EU a tree scope d u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as [version|]
    eqn:Havailable.
  - apply pre_finalize_reload_set_safe; [exact Hinv|].
    destruct (pre_finalize_available_spec EB EN EE EU a tree scope d u _ version Htree
      (pre_finalize_scope_regular _ _ _ _ _ _ Hinv) Havailable)
      as [Hregular [Hexpr [q [Hpoint Hdom]]]].
    exists u, q; repeat split; assumption.
  - apply pre_finalize_scope_set_safe; [exact Hinv|exact I].
Qed.

Local Lemma pre_finalize_fold_invariant {X A} (step : X -> A -> X) (P : X -> Prop)
    (items : list A) (initial : X) :
  P initial -> (forall x item, In item items -> P x -> P (step x item)) ->
  P (fold_left step items initial).
Proof.
  revert initial; induction items as [|item items IH]; intros initial Hinitial Hstep.
  - exact Hinitial.
  - apply IH.
    + apply Hstep; [left; reflexivity|exact Hinitial].
    + intros x next Hin Hx; apply Hstep; [right; exact Hin|exact Hx].
Qed.

Local Lemma pre_finalize_argument_step_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) facts tree scope p arg :
  (forall q n, dominates_b EN tree q n = true ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n) ->
  Map.get EBE (pre_arg_block_edge arg) (pre_point_edge_index EBE (pre_ssa_points a)) =
    Some (pre_arg_point_edge arg) ->
  Graph.target (block_graph (pre_ssa_points a)) (pre_arg_block_edge arg) = pre_arg_block arg ->
  pre_finalize_invariant EB EBE EE EU a (scope,p) ->
  pre_finalize_invariant EB EBE EE EU a
    (scope,pre_finalize_argument_step EB EN EE EU a facts tree scope p arg).
Proof.
  intros Htree Hindex Htarget Hinv; destruct arg as [b u be incoming op].
  unfold pre_finalize_argument_step; cbn [pre_arg_block pre_arg_expression pre_arg_block_edge
    pre_arg_point_edge pre_arg_operand] in *.
  destruct (pre_finalize_will EB EU facts (b,u)); [|exact Hinv].
  destruct (pre_phi_translate a be u) as [translated|] eqn:Htranslate; [|exact Hinv].
  destruct (pre_finalize_insert_operand EB EU facts op).
  - destruct (pre_total_pure (pre_expression a) translated &&
      negb (kill (pre_genkill (pre_expression a)) incoming translated)) eqn:Hguard;
      [|exact Hinv].
    apply pre_finalize_phi_set_safe; [exact Hinv|].
    exists b, be, translated; split; [exact Hindex|]; split; [exact Htarget|].
    split; [reflexivity|]; split; [exact Htranslate|]; split; [reflexivity|]; left.
    apply andb_true_iff in Hguard; destruct Hguard as [Hpure Hkill].
    apply negb_true_iff in Hkill; split; [reflexivity|]; split; assumption.
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version op)
      translated (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming))
      as [version|] eqn:Havailable; [|exact Hinv].
    apply pre_finalize_phi_set_safe; [exact Hinv|].
    destruct (pre_finalize_available_spec EB EN EE EU a tree scope (frg_operand_version op)
      translated _ version Htree (pre_finalize_scope_regular _ _ _ _ _ _ Hinv) Havailable)
      as [Hregular [Hexpr Hdefinition]].
    exists b, be, translated; split; [exact Hindex|]; split; [exact Htarget|].
    split; [reflexivity|]; split; [exact Htranslate|]; split; [exact Hexpr|].
    right; split; assumption.
Qed.

Local Lemma pre_finalize_row_property {K X} (EK : encoding K) (P : X -> Prop) rows item :
  (forall k x, In x (index_edges EK rows k) -> P x) -> P (snd item) ->
  forall k x, In x (index_edges EK (pre_finalize_add_row EK rows item) k) -> P x.
Proof.
  intros Hrows Hitem k x; destruct item as [q y]; unfold pre_finalize_add_row.
  change (In x (index_edges EK (Map.set EK q (y :: index_edges EK rows q) rows) k) -> P x).
  destruct (Pos.eq_dec (encode EK k) (encode EK q)) as [Heq|Hne].
  - apply (encode_injective EK) in Heq; subst k; unfold index_edges at 1.
    rewrite Map.get_set_same; intros [->|Hin]; [exact Hitem|eapply Hrows; exact Hin].
  - unfold index_edges at 1; rewrite Map.get_set_other
      by (intro Heq; subst k; contradiction); apply Hrows.
Qed.

Local Lemma pre_finalize_argument_rows_good {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) :
  frg_wf EB EBE EN EE EV EU a f ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  forall n arg, In arg (index_edges EN (pre_finalize_argument_rows EBE EN a f) n) ->
    Map.get EBE (pre_arg_block_edge arg) (pre_point_edge_index EBE (pre_ssa_points a)) =
      Some (pre_arg_point_edge arg) /\
    Graph.target (block_graph (pre_ssa_points a)) (pre_arg_block_edge arg) = pre_arg_block arg.
Proof.
  intros Hfrg Hwf; unfold pre_finalize_argument_rows.
  apply pre_finalize_fold_invariant.
  - intros n arg Hin; unfold index_edges in Hin; rewrite Map.get_empty in Hin; contradiction.
  - intros rows item Hin Hrows; apply pre_finalize_row_property; [exact Hrows|].
    apply in_flat_map in Hin; destruct Hin as [[[[b u] be] op] [Hlink Hin]].
    destruct (Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)))
      as [incoming|] eqn:Hindex; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; subst item; split; [exact Hindex|].
    apply (Map.elements_sound _ _ _ _ Hwf) in Hlink.
    exact (proj2 (proj2 (frg_operand_domain _ _ _ _ _ _ _ _ Hfrg b u be op Hlink))).
Qed.

Local Lemma pre_finalize_phi_fold_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope p phis :
  pre_finalize_invariant EB EBE EE EU a (scope,p) ->
  pre_finalize_invariant EB EBE EE EU a
    (fold_left (pre_finalize_define_phi EB EE EU a) phis scope,p).
Proof.
  intro Hinv; eapply (pre_finalize_fold_invariant _
    (fun scope' => pre_finalize_invariant EB EBE EE EU a (scope',p))); [exact Hinv|].
  intros scope' [b u] Hin Hscope; apply pre_finalize_scope_set_safe; [exact Hscope|exact I].
Qed.

Local Lemma pre_finalize_node_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) facts tree points phis arguments work n :
  (forall q n', dominates_b EN tree q n' = true ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n') ->
  (forall arg, In arg (index_edges EN arguments n) ->
    Map.get EBE (pre_arg_block_edge arg) (pre_point_edge_index EBE (pre_ssa_points a)) =
      Some (pre_arg_point_edge arg) /\
    Graph.target (block_graph (pre_ssa_points a)) (pre_arg_block_edge arg) = pre_arg_block arg) ->
  pre_finalize_invariant EB EBE EE EU a work ->
  pre_finalize_invariant EB EBE EE EU a
    (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n).
Proof.
  intros Htree Harguments Hinv; destruct work as [scope p]; unfold pre_finalize_node.
  pose proof (pre_finalize_phi_fold_safe EB EBE EE EU a scope p (index_edges EN phis n) Hinv)
    as Hphis.
  assert (pre_finalize_invariant EB EBE EE EU a
    (fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope,
      fold_left (pre_finalize_argument_step EB EN EE EU a facts tree
        (fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope))
        (index_edges EN arguments n) p)) as Harguments_done.
  { eapply (pre_finalize_fold_invariant _ (fun p' => pre_finalize_invariant EB EBE EE EU a
      (fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope,p')));
      [exact Hphis|].
    intros p' arg Hin Harg; destruct (Harguments arg Hin) as [Hindex Htarget].
    eapply pre_finalize_argument_step_safe; eassumption. }
  eapply pre_finalize_fold_invariant; [exact Harguments_done|].
  intros work e Hin Hwork; eapply pre_finalize_occurrence_safe; eassumption.
Qed.

Local Lemma pre_finalize_add_expression_member {E U} (EE : encoding E) (EU : encoding U)
    rows item e u :
  FinSet.mem EU u (live_index_get EE e (pre_finalize_add_expression EE EU rows item)) = true <->
    (e,u) = item \/ FinSet.mem EU u (live_index_get EE e rows) = true.
Proof.
  destruct item as [q x].
  change (FinSet.mem EU u (live_index_get EE e
    (Map.set EE q (FinSet.add EU x (live_index_get EE q rows)) rows)) = true <->
    (e,u) = (q,x) \/ FinSet.mem EU u (live_index_get EE e rows) = true).
  destruct (Pos.eq_dec (encode EE e) (encode EE q)) as [Heq|Hne].
  - apply (encode_injective EE) in Heq; subst q; unfold live_index_get.
    rewrite Map.get_set_same, FinSet.mem_add.
    split; intros [H|H]; [left; subst u; reflexivity|right; exact H| |right; exact H].
    injection H as H; left; exact H.
  - unfold live_index_get; rewrite Map.get_set_other
      by (intro Heq; subst e; contradiction).
    split; [auto|intros [Heq|Hmem]; [congruence|exact Hmem]].
Qed.

Local Lemma pre_finalize_expression_rows_member {E U} (EE : encoding E) (EU : encoding U)
    items e u :
  FinSet.mem EU u (live_index_get EE e (pre_finalize_expression_rows EE EU items)) = true <->
    In (e,u) items.
Proof.
  assert (forall rows, FinSet.mem EU u (live_index_get EE e
    (fold_left (pre_finalize_add_expression EE EU) items rows)) = true <->
    In (e,u) items \/ FinSet.mem EU u (live_index_get EE e rows) = true) as Hfold.
  { induction items as [|item items IH]; intro rows.
    - change (FinSet.mem EU u (live_index_get EE e rows) = true <->
        False \/ FinSet.mem EU u (live_index_get EE e rows) = true); tauto.
    - change (FinSet.mem EU u (live_index_get EE e
        (fold_left (pre_finalize_add_expression EE EU) items
          (pre_finalize_add_expression EE EU rows item))) = true <->
        In (e,u) (item :: items) \/ FinSet.mem EU u (live_index_get EE e rows) = true).
      rewrite IH, pre_finalize_add_expression_member; cbn; intuition congruence. }
  unfold pre_finalize_expression_rows; rewrite Hfold.
  unfold live_index_get; rewrite Map.get_empty, FinSet.mem_empty; intuition discriminate.
Qed.

Local Lemma pre_finalize_materialized_insertion {S O N E U C}
    (EE : encoding E) (EU : encoding U) (v : pre_expression_view S O N E U C) p e u :
  Map.wf (pair_encoding (pair_encoding EE EE) EU) (pre_phi_versions p) ->
  (pre_inserted EE EU (pre_finalize_materialize EE EU v p) e u = true <->
    exists parameter incoming merged_u,
      Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),merged_u)
        (pre_phi_versions p) = Some (PreInserted e u)).
Proof.
  intro Hwf; unfold pre_inserted; change (FinSet.mem EU u (live_index_get EE e
    (pre_finalize_expression_rows EE EU (flat_map (fun binding => match snd binding with
      | PreInserted e' u' => [(e',u')]
      | _ => []
      end) (Map.elements (pre_phi_versions p))))) = true <->
      exists parameter incoming merged_u,
        Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),merged_u)
          (pre_phi_versions p) = Some (PreInserted e u)).
  rewrite pre_finalize_expression_rows_member, in_flat_map; split.
  - intros [[[[parameter incoming] merged_u] version] [Hbinding Hin]].
    destruct version as [x|d x|d x|d x]; cbn in Hin; try contradiction.
    destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst d x.
    exists parameter, incoming, merged_u; eapply Map.elements_sound; eassumption.
  - intros [parameter [incoming [merged_u Hget]]].
    exists (((parameter,incoming),merged_u),PreInserted e u); split.
    + eapply Map.elements_complete; eassumption.
    + left; reflexivity.
Qed.

Local Lemma pre_finalize_materialized_deletion {S O N E U C}
    (EE : encoding E) (EU : encoding U) (v : pre_expression_view S O N E U C) p e u :
  Map.wf EE (pre_reload_versions p) ->
  (pre_deleted EE EU (pre_finalize_materialize EE EU v p) e u = true <->
    pre_recomputed v e = Some u /\ exists version,
      Map.get EE e (pre_reload_versions p) = Some version).
Proof.
  intro Hwf; unfold pre_deleted; change (FinSet.mem EU u (live_index_get EE e
    (pre_finalize_expression_rows EE EU (flat_map (fun binding =>
      match pre_recomputed v (fst binding) with
      | Some x => [(fst binding,x)]
      | None => []
      end) (Map.elements (pre_reload_versions p))))) = true <->
      pre_recomputed v e = Some u /\ exists version,
        Map.get EE e (pre_reload_versions p) = Some version).
  rewrite pre_finalize_expression_rows_member, in_flat_map; split.
  - intros [[d version] [Hbinding Hin]].
    cbn [fst] in Hin.
    destruct (pre_recomputed v d) as [x|] eqn:Hcomputed; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst d x.
    split; [exact Hcomputed|]; exists version; eapply Map.elements_sound; eassumption.
  - intros [Hcomputed [version Hget]]; exists (e,version); split.
    + eapply Map.elements_complete; eassumption.
    + cbn [fst]; rewrite Hcomputed; left; reflexivity.
Qed.

Local Lemma pre_finalize_initial_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) versions :
  pre_finalize_invariant EB EBE EE EU a
    (pre_finalize_initial EB EE EU a versions,PrePlan Map.empty Map.empty Map.empty Map.empty).
Proof.
  unfold pre_finalize_initial; apply pre_finalize_fold_invariant.
  - constructor.
    + intros d version Hget.
      change (Map.get (frg_version_encoding EB EE EU) d Map.empty = Some version) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    + apply Map.wf_empty.
    + apply Map.wf_empty.
    + intros e version Hget; change (Map.get EE e Map.empty = Some version) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    + intros parameter incoming u version Hget.
      change (Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),u)
        Map.empty = Some version) in Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros scope version Hin Hscope; destruct version; try exact Hscope.
    destruct (pre_initial_available a u); [|exact Hscope].
    apply pre_finalize_scope_set_safe; [exact Hscope|exact I].
Qed.

Local Lemma pre_finalize_replace_scope {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope p scope' :
  pre_finalize_invariant EB EBE EE EU a (scope,p) ->
  (forall d version, Map.get (frg_version_encoding EB EE EU) d scope' = Some version ->
    pre_finalize_regular version) -> pre_finalize_invariant EB EBE EE EU a (scope',p).
Proof.
  intros [Hregular Hreload_wf Hphi_wf Hreload Hphi] Hscope; constructor; assumption.
Qed.

Local Definition pre_finalize_table_invariant {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (work : Map.t N (pre_finalize_scope B E U) * pre_plan E U) : Prop :=
  pre_finalize_invariant EB EBE EE EU a (Map.empty,snd work) /\
  forall n scope, Map.get EN n (fst work) = Some scope -> forall d version,
    Map.get (frg_version_encoding EB EE EU) d scope = Some version -> pre_finalize_regular version.

Local Lemma pre_finalize_table_step_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments initial work n :
  (forall q n', dominates_b EN tree q n' = true ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n') ->
  (forall arg, In arg (index_edges EN arguments n) ->
    Map.get EBE (pre_arg_block_edge arg) (pre_point_edge_index EBE (pre_ssa_points a)) =
      Some (pre_arg_point_edge arg) /\
    Graph.target (block_graph (pre_ssa_points a)) (pre_arg_block_edge arg) = pre_arg_block arg) ->
  (forall d version, Map.get (frg_version_encoding EB EE EU) d initial = Some version ->
    pre_finalize_regular version) ->
  pre_finalize_table_invariant EB EBE EN EE EU a work ->
  pre_finalize_table_invariant EB EBE EN EE EU a
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial work n).
Proof.
  intros Htree Harguments Hinitial; destruct work as [outputs p]; intros [Hplan Houtputs].
  unfold pre_finalize_table_step; cbn [fst snd] in Hplan, Houtputs.
  pose (scope := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end).
  assert (pre_finalize_invariant EB EBE EE EU a (scope,p)) as Hscope.
  { eapply pre_finalize_replace_scope; [exact Hplan|]; unfold scope.
    destruct (Map.get EN n (idom tree)) as [parent|]; [|exact Hinitial].
    destruct (Map.get EN parent outputs) as [frames|] eqn:Hget; [|exact Hinitial].
    eapply Houtputs; exact Hget. }
  pose proof (pre_finalize_node_safe EB EBE EN EE EU a f facts tree points phis arguments
    (scope,p) n Htree Harguments Hscope) as Hnode.
  change (pre_finalize_table_invariant EB EBE EN EE EU a
    (let '(frames,output) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (scope,p) n in (Map.set EN n frames outputs,output))).
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (scope,p) n)
    as [frames output]; split.
  - eapply pre_finalize_replace_scope; [exact Hnode|].
    intros d version Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros n' frames' Hget d version Hversion; apply pre_finalize_get_set in Hget.
    destruct Hget as [[Heq ->]|Hget].
    + eapply pre_finalize_scope_regular; eassumption.
    + eapply Houtputs; eassumption.
Qed.

Local Lemma pre_finalize_build_safe {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) facts :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  frg_wf EB EBE EN EE EV EU a f ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  exists scope, pre_finalize_invariant EB EBE EE EU a
    (scope,pre_finalize_build EB EBE EN EE EV EU a f facts).
Proof.
  intros Hready Hfrg Hlinks; unfold pre_finalize_build.
  pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
  pose (tree := dominator_tree points).
  pose (phis := pre_finalize_phi_rows EB EN EU a f facts).
  pose (arguments := pre_finalize_argument_rows EBE EN a f).
  pose (scope := pre_finalize_initial EB EE EU a (frg_versions f)).
  pose proof (pre_finalize_initial_safe EB EBE EE EU a (frg_versions f)) as Hinitial.
  pose proof (proj1 (proj2 (proj2 (dominator_tree_sound EN _ points Hready)))) as Htree.
  assert (pre_finalize_table_invariant EB EBE EN EE EU a
    (fold_left (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments scope)
      (preorder (dom_search points (idom tree)))
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) as Hresult.
  { apply pre_finalize_fold_invariant.
    - split; [exact (pre_finalize_initial_safe EB EBE EE EU a [])|].
      intros n frames Hget; change (Map.get EN n Map.empty = Some frames) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    - intros work n Hin Hwork; eapply pre_finalize_table_step_safe; try eassumption.
      + intros arg Harg; eapply pre_finalize_argument_rows_good; eassumption.
      + exact (pre_finalize_scope_regular _ _ _ _ _ _ Hinitial). }
  change (exists scope', pre_finalize_invariant EB EBE EE EU a
    (scope',snd (fold_left
      (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments scope)
      (preorder (dom_search points (idom tree)))
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)))).
  destruct (fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments scope)
    (preorder (dom_search points (idom tree)))
    (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)) as [outputs p].
  exists Map.empty; exact (proj1 Hresult).
Qed.

Local Lemma pre_place_raw_invariant {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  exists scope, pre_finalize_invariant EB EBE EE EU a
    (scope,pre_finalize_build EB EBE EN EE EV EU a f (solve_ssapre EB EBE EN EE EV EU a f)).
Proof.
  intros Ha Hb Hn; cbn zeta; apply pre_finalize_build_safe; [exact Hn| |].
  - apply build_frg_wf; assumption.
  - exact (proj1 (proj2 (proj2 (proj2 (build_frg_indexes_wf EB EBE EN EE EV EU a))))).
Qed.

(** Every insertion is safe and every deleted occurrence has a pure dominating reload version. *)
Theorem ssa_pre_place_legal {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_placement_legal EN EE EU (pre_expression a) (ssa_pre_place EB EBE EN EE EV EU a).
Proof.
  intros Ha Hb Hn.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (facts := solve_ssapre EB EBE EN EE EV EU a f).
  pose (raw := pre_finalize_build EB EBE EN EE EV EU a f facts).
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  change (pre_finalize_invariant EB EBE EE EU a (scope,raw)) in Hinv.
  change (pre_placement_legal EN EE EU (pre_expression a)
    (pre_finalize_materialize EE EU (pre_expression a) raw)); split.
  - intros e u He Hinsert; apply (proj1 (pre_finalize_materialized_insertion EE EU _ raw e u
      (pre_finalize_phi_wf _ _ _ _ _ _ Hinv))) in Hinsert.
    destruct Hinsert as [parameter [incoming [merged_u Hget]]].
    pose proof (pre_finalize_phis_safe _ _ _ _ _ _ Hinv parameter incoming merged_u
      (PreInserted e u) Hget) as Hselection.
    destruct Hselection as [b [be [translated [Hindex [Htarget [Hparameter
      [Htranslate [Hexpr Horigin]]]]]]]].
    destruct Horigin as [[Hversion [Hpure Hkill]]|[Hregular Hdefinition]];
      [|exact (False_rect _ Hregular)].
    inversion Hversion; subst; split; [exact Hpure|]; split; [exact Hkill|].
    eexists; exists merged_u; exact Hget.
  - intros e u He Hdelete; apply (proj1 (pre_finalize_materialized_deletion EE EU _ raw e u
      (pre_finalize_reload_wf _ _ _ _ _ _ Hinv))) in Hdelete.
    destruct Hdelete as [Hcomputed [version Hget]].
    destruct (pre_finalize_reloads_safe _ _ _ _ _ _ Hinv e version Hget)
      as [u' [n [Hcomputed' [Hpure [Hexpr [Hpoint Hdom]]]]]].
    rewrite Hcomputed in Hcomputed'; injection Hcomputed' as ->.
    split; [exact Hcomputed|]; split; [exact Hpure|]; exists version, n.
    split; [exact Hget|]; split; [exact Hpoint|].
    rewrite <- (pre_expr_point_graph EV a Ha); exact Hdom.
Qed.

(** Each incoming phi version belongs to that edge's translated expression and dominates its use. *)
Theorem ssa_pre_phi_versions_correct {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  forall b u be pe version,
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,pe),u) (pre_phi_versions p) = Some version ->
    exists u', pre_phi_translate a be u = Some u' /\ pre_version_expr version = u' /\
      (version = PreInserted pe u' \/ exists n,
        pre_version_point (pre_expression a) version = Some n /\
        dominates (live_graph (point_model (pre_ssa_points a))) n
          (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)).
Proof.
  intros Ha Hb Hn; cbn zeta; intros b u be pe version Hindex Htarget Hget.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (facts := solve_ssapre EB EBE EN EE EV EU a f).
  pose (raw := pre_finalize_build EB EBE EN EE EV EU a f facts).
  change (Map.get (pair_encoding (pair_encoding EE EE) EU)
    ((parameter_edge (pre_ssa_points a) b,pe),u) (pre_phi_versions raw) = Some version) in Hget.
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  change (pre_finalize_invariant EB EBE EE EU a (scope,raw)) in Hinv.
  destruct (pre_finalize_phis_safe _ _ _ _ _ _ Hinv
    (parameter_edge (pre_ssa_points a) b) pe u version Hget)
    as [b' [be' [translated [Hindex' [Htarget' [Hparameter
      [Htranslate [Hexpr Horigin]]]]]]]].
  pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
    (pre_expr_points EV a Ha) be pe) Hindex)) as Hedge.
  pose proof (proj2 (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
    (pre_expr_points EV a Ha) be' pe) Hindex')) as Hedge'.
  assert (be' = be) by congruence; subst be'.
  exists translated; split; [exact Htranslate|]; split; [exact Hexpr|].
  destruct Horigin as [[Hinsert Hrest]|[Hregular Hdefinition]]; [left; exact Hinsert|].
  right; exact Hdefinition.
Qed.

(** Every produced deletion has exactly the original expression and an explicit reload entry. *)
Lemma ssa_pre_deletions_defined {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  forall e u, pre_deleted EE EU p e u = true ->
    pre_recomputed (pre_expression a) e = Some u /\
      exists version, Map.get EE e (pre_reload_versions p) = Some version.
Proof.
  intros Ha Hb Hn; cbn zeta; intros e u Hdeleted.
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  apply (proj1 (pre_finalize_materialized_deletion EE EU _ _ e u
    (pre_finalize_reload_wf _ _ _ _ _ _ Hinv))); exact Hdeleted.
Qed.

(** * Finite output support *)

(** Every possible phi output key comes from one indexed FRG operand and its actual edge. *)
Definition pre_finalize_phi_keys {S O B BE N E V K C U} (EBE : encoding BE)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : list ((E * E) * U) :=
  flat_map (fun binding => let '(((b,u),be),op) := binding in
    match Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) with
    | Some incoming => [((parameter_edge (pre_ssa_points a) b,incoming),u)]
    | None => []
    end) (Map.elements (frg_phi_operands f)).

Local Definition pre_finalize_supported {S O B BE N E V K C U} (EBE : encoding BE)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) (p : pre_plan E U) : Prop :=
  (forall e version, Map.get EE e (pre_reload_versions p) = Some version ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a))))) /\
  forall key version,
    Map.get (pair_encoding (pair_encoding EE EE) EU) key (pre_phi_versions p) = Some version ->
    In key (pre_finalize_phi_keys EBE a f).

Local Lemma pre_finalize_argument_keys {S O B BE N E V K C U}
    (EBE : encoding BE) (EN : encoding N) (a : pre_expr_ssa S O B BE N E V K C U) f :
  forall n arg, In arg (index_edges EN (pre_finalize_argument_rows EBE EN a f) n) ->
    In ((parameter_edge (pre_ssa_points a) (pre_arg_block arg),pre_arg_point_edge arg),
      pre_arg_expression arg) (pre_finalize_phi_keys EBE a f).
Proof.
  unfold pre_finalize_argument_rows; apply pre_finalize_fold_invariant.
  - intros n arg Hin; unfold index_edges in Hin; rewrite Map.get_empty in Hin; contradiction.
  - intros rows item Hin Hrows; apply pre_finalize_row_property; [exact Hrows|].
    apply in_flat_map in Hin; destruct Hin as [[[[b u] be] op] [Hlink Hin]].
    destruct (Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)))
      as [incoming|] eqn:Hindex; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; subst item.
    unfold pre_finalize_phi_keys; apply in_flat_map; exists (((b,u),be),op).
    split; [exact Hlink|]; rewrite Hindex; left; reflexivity.
Qed.

Local Lemma pre_finalize_select_supported {S O B BE N E V K C U}
    (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f p parameter incoming u version :
  pre_finalize_supported EBE EE EU a f p ->
  In ((parameter,incoming),u) (pre_finalize_phi_keys EBE a f) ->
  pre_finalize_supported EBE EE EU a f
    (pre_finalize_select EE EU p parameter incoming u version).
Proof.
  intros [Hreload Hphi] Hkey; split; [exact Hreload|].
  intros key selected Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[-> Hvalue]|Hget]; [exact Hkey|eapply Hphi; exact Hget].
Qed.

Local Lemma pre_finalize_argument_supported {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f facts tree scope p arg :
  pre_finalize_supported EBE EE EU a f p ->
  In ((parameter_edge (pre_ssa_points a) (pre_arg_block arg),pre_arg_point_edge arg),
    pre_arg_expression arg) (pre_finalize_phi_keys EBE a f) ->
  pre_finalize_supported EBE EE EU a f
    (pre_finalize_argument_step EB EN EE EU a facts tree scope p arg).
Proof.
  intros Hsupport Hkey; destruct arg as [b u be incoming op].
  unfold pre_finalize_argument_step; cbn [pre_arg_block pre_arg_expression pre_arg_block_edge
    pre_arg_point_edge pre_arg_operand] in *.
  destruct (pre_finalize_will EB EU facts (b,u)); [|exact Hsupport].
  destruct (pre_phi_translate a be u) as [translated|]; [|exact Hsupport].
  destruct (pre_finalize_insert_operand EB EU facts op).
  - destruct (pre_total_pure (pre_expression a) translated &&
      negb (kill (pre_genkill (pre_expression a)) incoming translated)); [|exact Hsupport].
    apply pre_finalize_select_supported; assumption.
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version op)
      translated (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming))
      as [version|]; [|exact Hsupport].
    apply pre_finalize_select_supported; assumption.
Qed.

Local Lemma pre_finalize_occurrence_supported {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  frg_wf EB EBE EN EE EV EU a f -> pre_finalize_supported EBE EE EU a f (snd work) ->
  pre_finalize_supported EBE EE EU a f
    (snd (pre_finalize_occurrence EB EN EE EU a f tree work e)).
Proof.
  intros Hfrg Hsupport; destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|];
    destruct (Map.get EE e (frg_occurrence_index f)) as [d|] eqn:Hclass; try exact Hsupport.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hsupport].
  destruct (pre_finalize_available EB EN EE EU a tree scope d u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as [version|];
    [|exact Hsupport].
  destruct Hsupport as [Hreload Hphi]; split; [|exact Hphi].
  intros edge selected Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[-> Hvalue]|Hget].
  - exact (proj1 (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)).
  - eapply Hreload; exact Hget.
Qed.

Local Lemma pre_finalize_node_supported {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments work n :
  frg_wf EB EBE EN EE EV EU a f ->
  (forall arg, In arg (index_edges EN arguments n) ->
    In ((parameter_edge (pre_ssa_points a) (pre_arg_block arg),pre_arg_point_edge arg),
      pre_arg_expression arg) (pre_finalize_phi_keys EBE a f)) ->
  pre_finalize_supported EBE EE EU a f (snd work) ->
  pre_finalize_supported EBE EE EU a f
    (snd (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)).
Proof.
  intros Hfrg Harguments Hsupport; destruct work as [scope p]; unfold pre_finalize_node.
  apply (pre_finalize_fold_invariant _ (fun work =>
    pre_finalize_supported EBE EE EU a f (snd work))).
  - cbn [snd]; apply pre_finalize_fold_invariant; [exact Hsupport|].
    intros p' arg Hin Hp'; apply pre_finalize_argument_supported; [exact Hp'|].
    apply Harguments; exact Hin.
  - intros work e Hin Hwork; eapply pre_finalize_occurrence_supported; eassumption.
Qed.

Local Lemma pre_finalize_build_supported {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f facts :
  frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_supported EBE EE EU a f (pre_finalize_build EB EBE EN EE EV EU a f facts).
Proof.
  intro Hfrg; unfold pre_finalize_build.
  apply (pre_finalize_fold_invariant _ (fun work =>
    pre_finalize_supported EBE EE EU a f (snd work))).
  - split.
    + intros key version Hget; change (Map.get EE key Map.empty = Some version) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    + intros key version Hget.
      change (Map.get (pair_encoding (pair_encoding EE EE) EU) key Map.empty = Some version)
        in Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros [outputs p] n Hin Hsupport; unfold pre_finalize_table_step.
    pose (input := match Map.get EN n
      (idom (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))) with
      | Some parent => match Map.get EN parent outputs with
        | Some scope => scope
        | None => pre_finalize_initial EB EE EU a (frg_versions f)
        end
      | None => pre_finalize_initial EB EE EU a (frg_versions f)
      end).
    change (pre_finalize_supported EBE EE EU a f
      (snd (let '(frames,output) := pre_finalize_node EB EN EE EU a f facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (input,p) n in (Map.set EN n frames outputs,output)))).
    pose proof (pre_finalize_node_supported EB EBE EN EE EV EU a f facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (input,p) n Hfrg
      (fun arg Harg => pre_finalize_argument_keys EBE EN a f n arg Harg) Hsupport) as Hnode.
    destruct (pre_finalize_node EB EN EE EU a f facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (input,p) n) as [frames output]; exact Hnode.
Qed.

(** Candidate construction contributes at most one output key per indexed FRG operand. *)
Lemma pre_finalize_phi_keys_bound {S O B BE N E V K C U} (EBE : encoding BE)
    (a : pre_expr_ssa S O B BE N E V K C U) f :
  length (pre_finalize_phi_keys EBE a f) <= length (Map.elements (frg_phi_operands f)).
Proof.
  unfold pre_finalize_phi_keys; induction (Map.elements (frg_phi_operands f))
    as [|[[[b u] be] op] rest IH]; [reflexivity|].
  cbn [flat_map]; destruct (Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)));
    cbn; lia.
Qed.

(** Canonical output maps contain only original edges and indexed phi candidates. *)
Theorem ssa_pre_output_supported {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  (forall e version, Map.get EE e (pre_reload_versions p) = Some version ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a))))) /\
  (forall key version,
    Map.get (pair_encoding (pair_encoding EE EE) EU) key (pre_phi_versions p) = Some version ->
    In key (pre_finalize_phi_keys EBE a f)) /\
  length (Map.elements (pre_reload_versions p)) <=
    length (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
  length (Map.elements (pre_phi_versions p)) <= length (Map.elements (frg_phi_operands f)).
Proof.
  intros Ha Hb Hn; cbn zeta.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (raw := pre_finalize_build EB EBE EN EE EV EU a f (solve_ssapre EB EBE EN EE EV EU a f)).
  pose proof (pre_finalize_build_supported EB EBE EN EE EV EU a f
    (solve_ssapre EB EBE EN EE EV EU a f) (build_frg_wf EB EBE EN EE EV EU a Ha Hb Hn))
    as Hsupport.
  destruct Hsupport as [Hreload Hphi]; split; [exact Hreload|]; split; [exact Hphi|].
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  change (pre_finalize_invariant EB EBE EE EU a (scope,raw)) in Hinv.
  split.
  - assert (length (map fst (Map.elements (pre_reload_versions raw))) <=
      length (edges_of (live_graph (point_model (pre_ssa_points a))))) as Hbound.
    { apply NoDup_incl_length.
      - apply (Map.elements_nodup EE); exact (pre_finalize_reload_wf _ _ _ _ _ _ Hinv).
      - intros e Hin; apply in_map_iff in Hin; destruct Hin as [[edge version] [Heq Hin]].
        cbn in Heq; subst edge; eapply Hreload.
        eapply Map.elements_sound; [exact (pre_finalize_reload_wf _ _ _ _ _ _ Hinv)|exact Hin]. }
    rewrite length_map in Hbound; exact Hbound.
  - assert (length (map fst (Map.elements (pre_phi_versions raw))) <=
      length (pre_finalize_phi_keys EBE a f)) as Hbound.
    { apply NoDup_incl_length.
      - apply (Map.elements_nodup (pair_encoding (pair_encoding EE EE) EU)).
        exact (pre_finalize_phi_wf _ _ _ _ _ _ Hinv).
      - intros key Hin; apply in_map_iff in Hin; destruct Hin as [[key' version] [Heq Hin]].
        cbn in Heq; subst key'; eapply Hphi.
        eapply Map.elements_sound; [exact (pre_finalize_phi_wf _ _ _ _ _ _ Hinv)|exact Hin]. }
    rewrite length_map in Hbound.
    eapply Nat.le_trans; [exact Hbound|apply pre_finalize_phi_keys_bound].
Qed.

Local Lemma pre_finalize_phi_key_family {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f
    parameter incoming u :
  frg_wf EB EBE EN EE EV EU a f ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  In ((parameter,incoming),u) (pre_finalize_phi_keys EBE a f) -> pre_expr_in_family a u.
Proof.
  intros Hfrg Hwf Hin; unfold pre_finalize_phi_keys in Hin; apply in_flat_map in Hin.
  destruct Hin as [[[[b x] be] op] [Hbinding Hin]].
  destruct (Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)))
    as [edge|] eqn:Hindex; [|contradiction].
  destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst x.
  apply (Map.elements_sound _ _ _ _ Hwf) in Hbinding.
  pose proof (proj1 (frg_operand_domain _ _ _ _ _ _ _ _ Hfrg b u be op Hbinding)) as Hphi.
  exact (proj1 (proj1 (frg_phi_exact _ _ _ _ _ _ _ _ Hfrg b u) Hphi)).
Qed.

Local Lemma pre_point_index_block_listed {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) be incoming :
  ssa_point_laws s -> Map.get EBE be (pre_point_edge_index EBE s) = Some incoming ->
  In incoming (edges_of (live_graph (point_model s))) /\ In be (edges_of (block_graph s)).
Proof.
  intros Hpoints Hindex.
  destruct (proj1 (pre_point_edge_index_exact EBE s Hpoints be incoming) Hindex)
    as [Hin Hblock]; split; [exact Hin|].
  apply in_flat_map in Hin; destruct Hin as [n [Hn Hout]].
  pose proof (point_edge_projection Hpoints n incoming Hn Hout) as Hproject.
  rewrite Hblock in Hproject; destruct Hproject as [Hbe Hrest].
  apply in_flat_map; exists (block_of_point s n); split; [|exact Hbe].
  destruct (proj1 (points_covered Hpoints n) Hn) as [b [Hb Hmember]].
  rewrite (points_owner Hpoints b n Hb Hmember); exact Hb.
Qed.

(** Insertions and deletions preserve the discovered finite family and use original graph edges. *)
Theorem ssa_pre_output_universe {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  forall e u, pre_inserted EE EU p e u = true \/ pre_deleted EE EU p e u = true ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    In u (pre_expr_universe EBE EV EU a).
Proof.
  intros Ha Hb Hn; cbn zeta; intros e u Houtput.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (raw := pre_finalize_build EB EBE EN EE EV EU a f (solve_ssapre EB EBE EN EE EV EU a f)).
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  change (pre_finalize_invariant EB EBE EE EU a (scope,raw)) in Hinv.
  destruct (ssa_pre_output_supported EB EBE EN EE EV EU a Ha Hb Hn)
    as [Hreload [Hphi Hbounds]].
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  destruct Houtput as [Hinsert|Hdelete].
  - apply (proj1 (pre_finalize_materialized_insertion EE EU _ raw e u
      (pre_finalize_phi_wf _ _ _ _ _ _ Hinv))) in Hinsert.
    destruct Hinsert as [parameter [incoming [merged Hget]]].
    pose proof (Hphi ((parameter,incoming),merged) (PreInserted e u) Hget) as Hkey.
    assert (pre_expr_in_family a merged) as Hfamily.
    { eapply pre_finalize_phi_key_family; [exact Hfrg| |exact Hkey].
      exact (proj1 (proj2 (proj2 (proj2 (build_frg_indexes_wf EB EBE EN EE EV EU a))))). }
    destruct (pre_finalize_phis_safe _ _ _ _ _ _ Hinv parameter incoming merged
      (PreInserted e u) Hget) as [b [be [translated [Hindex [Htarget [Hparameter
        [Htranslate [Hexpr Horigin]]]]]]]].
    destruct Horigin as [[Hversion Hsafe]|[Hregular Hdefinition]]; [|contradiction].
    inversion Hversion; subst incoming translated.
    destruct (pre_point_index_block_listed EBE (pre_ssa_points a) be e
      (pre_expr_points EV a Ha) Hindex) as [Hedge Hbe].
    split; [exact Hedge|]; apply (proj2 (proj2 (pre_expr_universe_exact EBE EV EU a Ha) u)).
    eapply pre_family_translate; eassumption.
  - destruct (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e u Hdelete)
      as [Hcomputed [version Hget]].
    split; [eapply Hreload; exact Hget|].
    apply (proj2 (proj2 (pre_expr_universe_exact EBE EV EU a Ha) u)), pre_family_seed.
    exact (pre_expr_occurrences EV a Ha e u Hcomputed).
Qed.

Local Lemma pre_finalize_expression_rows_wf {E U} (EE : encoding E) (EU : encoding U) items :
  forall e, FinSet.wf EU (live_index_get EE e (pre_finalize_expression_rows EE EU items)).
Proof.
  unfold pre_finalize_expression_rows; apply pre_finalize_fold_invariant.
  - intro e; unfold live_index_get; rewrite Map.get_empty; apply Map.wf_empty.
  - intros rows [edge u] Hin Hrows e; unfold pre_finalize_add_expression; cbn [fst snd].
    destruct (dfs_eq_dec EE e edge) as [->|Hne]; unfold live_index_get.
    + rewrite Map.get_set_same; apply Map.wf_set; exact (Hrows edge).
    + rewrite Map.get_set_other by exact Hne; exact (Hrows e).
Qed.

(** The finite insertion and deletion rows remain canonical even for malformed raw inputs. *)
Lemma ssa_pre_output_rows_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  let p := ssa_pre_place EB EBE EN EE EV EU a in forall e,
    FinSet.wf EU (live_index_get EE e (pre_insertions p)) /\
    FinSet.wf EU (live_index_get EE e (pre_deletions p)).
Proof.
  cbn zeta; intro e; unfold ssa_pre_place, pre_finalize_materialize;
    cbn [pre_insertions pre_deletions]; split; apply pre_finalize_expression_rows_wf.
Qed.

(** Each edge has at most one deletion and at most one insertion per selected phi input. *)
Theorem ssa_pre_output_row_bounds {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let p := ssa_pre_place EB EBE EN EE EV EU a in forall e,
    length (FinSet.elements (live_index_get EE e (pre_insertions p))) <=
      length (Map.elements (frg_phi_operands f)) /\
    length (FinSet.elements (live_index_get EE e (pre_deletions p))) <= 1.
Proof.
  intros Ha Hb Hn; cbn zeta; intro e.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (raw := pre_finalize_build EB EBE EN EE EV EU a f (solve_ssapre EB EBE EN EE EV EU a f)).
  pose (p := ssa_pre_place EB EBE EN EE EV EU a).
  destruct (pre_place_raw_invariant EB EBE EN EE EV EU a Ha Hb Hn) as [scope Hinv].
  change (pre_finalize_invariant EB EBE EE EU a (scope,raw)) in Hinv.
  destruct (ssa_pre_output_rows_wf EB EBE EN EE EV EU a e) as [Hinsert_wf Hdelete_wf].
  split.
  - assert (FinSet.size (live_index_get EE e (pre_insertions p)) <=
      length (map (fun binding => pre_version_expr (snd binding))
        (Map.elements (pre_phi_versions raw)))) as Hbound.
    { apply (FinSet.size_le_length EU); [exact Hinsert_wf|].
      intros u Hmem; apply (proj1 (pre_finalize_materialized_insertion EE EU
        (pre_expression a) raw e u
        (pre_finalize_phi_wf _ _ _ _ _ _ Hinv))) in Hmem.
      destruct Hmem as [parameter [incoming [merged Hget]]].
      apply in_map_iff; exists (((parameter,incoming),merged),PreInserted e u).
      split; [reflexivity|]; apply (Map.elements_complete _ _ _ _
        (pre_finalize_phi_wf _ _ _ _ _ _ Hinv)); exact Hget. }
    rewrite FinSet.size_elements, length_map in Hbound.
    destruct (ssa_pre_output_supported EB EBE EN EE EV EU a Ha Hb Hn)
      as [Hreload [Hphi [Hreload_bound Hphi_bound]]].
    eapply Nat.le_trans; [exact Hbound|exact Hphi_bound].
  - assert (NoDup (FinSet.elements (live_index_get EE e (pre_deletions p)))) as Hnodup.
    { apply (FinSet.elements_nodup EU); exact Hdelete_wf. }
    destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed.
    + change (length (FinSet.elements (live_index_get EE e (pre_deletions p))) <= length [u]).
      apply NoDup_incl_length; [exact Hnodup|].
      intros x Hin; apply (proj1 (FinSet.elements_spec EU x _ Hdelete_wf)) in Hin.
      destruct (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e x Hin)
        as [Hcomputed' Hget].
      rewrite Hcomputed in Hcomputed'; injection Hcomputed' as ->; left; reflexivity.
    + assert (length (FinSet.elements (live_index_get EE e (pre_deletions p))) <= length (@nil U))
        as Hempty.
      { apply NoDup_incl_length; [exact Hnodup|].
        intros x Hin; apply (proj1 (FinSet.elements_spec EU x _ Hdelete_wf)) in Hin.
        destruct (ssa_pre_deletions_defined EB EBE EN EE EV EU a Ha Hb Hn e x Hin)
          as [Hcomputed' Hget]; congruence. }
      eapply Nat.le_trans; [exact Hempty|cbn; lia].
Qed.

(** Extending generation adds only translated instances from the already discovered family. *)
Theorem ssa_pre_extended_universe {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  incl (expr_universe EU (pre_extended_view EE EU (pre_expression a) p))
    (expr_universe EU (pre_genkill (pre_expression a)) ++ pre_expr_universe EBE EV EU a).
Proof.
  intros Ha Hb Hn; cbn zeta; intros u Hin.
  assert (forall xs, FinSet.wf EU (FinSet.of_list EU xs)) as Hoflist.
  { intro xs; unfold FinSet.of_list; apply FinSet.wf_fold_add, Map.wf_empty. }
  unfold expr_universe in Hin; apply (proj1 (FinSet.elements_spec EU u _ (Hoflist _))) in Hin.
  apply FinSet.of_list_spec in Hin; apply in_flat_map in Hin; destruct Hin as [e [Hedge Hu]].
  change (In u (gen (pre_genkill (pre_expression a)) e ++
    FinSet.elements (live_index_get EE e
      (pre_insertions (ssa_pre_place EB EBE EN EE EV EU a))))) in Hu.
  apply in_app_iff in Hu; apply in_or_app; destruct Hu as [Horiginal|Hinserted].
  - left; unfold expr_universe; apply (proj2 (FinSet.elements_spec EU u _ (Hoflist _))).
    apply FinSet.of_list_spec, in_flat_map; exists e; split; assumption.
  - right.
    apply (proj1 (FinSet.elements_spec EU u _
      (proj1 (ssa_pre_output_rows_wf EB EBE EN EE EV EU a e)))) in Hinserted.
    exact (proj2 (ssa_pre_output_universe EB EBE EN EE EV EU a Ha Hb Hn e u
      (or_introl Hinserted))).
Qed.

(** Summing the finite rows bounds all emitted edge-expression cells on the original graph. *)
Theorem ssa_pre_output_cardinality_bounds {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  let edges := edges_of (live_graph (point_model (pre_ssa_points a))) in
  fold_right (fun e total => length (FinSet.elements
    (live_index_get EE e (pre_insertions p))) + total) 0 edges <=
      length edges * length (Map.elements (frg_phi_operands (build_frg EB EBE EN EE EV EU a))) /\
  fold_right (fun e total => length (FinSet.elements
    (live_index_get EE e (pre_deletions p))) + total) 0 edges <= length edges.
Proof.
  intros Ha Hb Hn; cbn zeta.
  generalize (edges_of (live_graph (point_model (pre_ssa_points a)))); intro edges.
  induction edges as [|e edges [Hinsertion Hdeletion]].
  - split; reflexivity.
  - destruct (ssa_pre_output_row_bounds EB EBE EN EE EV EU a Ha Hb Hn e)
      as [Hinsert Hdelete].
    cbn [fold_right length Nat.mul]; split; lia.
Qed.

(** * Completeness interfaces for Finalize scopes *)

(** Exact dominance queries accept every matching definition present in the current scope. *)
Lemma pre_finalize_available_complete {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d u n version q :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  Map.get (frg_version_encoding EB EE EU) d scope = Some version ->
  pre_version_expr version = u -> pre_version_point (pre_expression a) version = Some q ->
  dominates (live_graph (point_model (pre_ssa_points a))) q n ->
  pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
    scope d u n = Some version.
Proof.
  intros Hready Hreachable Hget Hexpr Hpoint Hdom.
  unfold pre_finalize_available; rewrite Hget, Hexpr, Pos.eqb_refl, Hpoint.
  assert (dominates_b EN
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) q n = true)
    as Hquery.
  { exact (proj2 (proj1 (dominator_tree_with_exact EN _ _ Hready SimpleLT) q n Hreachable)
      Hdom). }
  rewrite Hquery; reflexivity.
Qed.

Local Lemma pre_finalize_row_member {K X} (EK : encoding K)
    (rows : Map.t K (list X)) (item : K * X) (k : K) (x : X) :
  In x (index_edges EK (pre_finalize_add_row EK rows item) k) <->
    (k,x) = item \/ In x (index_edges EK rows k).
Proof.
  destruct item as [key value]; unfold pre_finalize_add_row; cbn [fst snd].
  destruct (dfs_eq_dec EK k key) as [->|Hne]; unfold index_edges at 1.
  - rewrite Map.get_set_same; change (value = x \/ In x (index_edges EK rows key) <->
      (key,x) = (key,value) \/ In x (index_edges EK rows key)); intuition congruence.
  - rewrite Map.get_set_other by exact Hne.
    split; [auto|intros [Heq|Hin]; [congruence|exact Hin]].
Qed.

Local Lemma pre_finalize_rows_member {K X} (EK : encoding K)
    (items : list (K * X)) (k : K) (x : X) :
  In x (index_edges EK (fold_left (pre_finalize_add_row EK) items Map.empty) k) <->
    In (k,x) items.
Proof.
  assert (forall rows,
    In x (index_edges EK (fold_left (pre_finalize_add_row EK) items rows) k) <->
      In (k,x) items \/ In x (index_edges EK rows k)) as Hfold.
  { induction items as [|item items IH]; intro rows.
    - cbn [fold_left In]; tauto.
    - cbn [fold_left]; rewrite IH, pre_finalize_row_member; cbn [In]; intuition congruence. }
  rewrite Hfold; unfold index_edges; rewrite Map.get_empty; cbn; tauto.
Qed.

(** Every materialized expression phi is indexed at its parameter edge's target. *)
Lemma pre_finalize_phi_rows_exact {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts n b u :
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  (In (b,u) (index_edges EN (pre_finalize_phi_rows EB EN EU a f facts) n) <->
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true /\
    pre_finalize_will EB EU facts (b,u) = true /\
    n = Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)).
Proof.
  intro Hwf; unfold pre_finalize_phi_rows; rewrite pre_finalize_rows_member, in_flat_map.
  split.
  - intros [[block expression] [Hphi Hin]].
    destruct (pre_finalize_will EB EU facts (block,expression)) eqn:Hwill; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst block expression.
    split; [apply (proj1 (FinSet.elements_spec _ _ _ Hwf)); exact Hphi|].
    split; [exact Hwill|reflexivity].
  - intros [Hphi [Hwill ->]]; exists (b,u); split.
    + apply (proj2 (FinSet.elements_spec _ _ _ Hwf)); exact Hphi.
    + rewrite Hwill; left; reflexivity.
Qed.

(** Every FRG operand has its exact argument in the once-built source-point bucket. *)
Lemma pre_finalize_argument_rows_exact {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f n b u be incoming op :
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  (In (PreFinalizeArgument b u be incoming op)
      (index_edges EN (pre_finalize_argument_rows EBE EN a f) n) <->
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
      (frg_phi_operands f) = Some op /\
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming /\
    n = Graph.source (live_graph (point_model (pre_ssa_points a))) incoming).
Proof.
  intro Hwf; unfold pre_finalize_argument_rows; rewrite pre_finalize_rows_member, in_flat_map.
  split.
  - intros [[[[block expression] edge] operand] [Hbinding Hin]].
    destruct (Map.get EBE edge (pre_point_edge_index EBE (pre_ssa_points a)))
      as [point_edge|] eqn:Hindex; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
    split; [eapply Map.elements_sound; eassumption|].
    split; [exact Hindex|reflexivity].
  - intros [Hbinding [Hindex ->]]; exists (((b,u),be),op); split.
    + eapply Map.elements_complete; eassumption.
    + rewrite Hindex; left; reflexivity.
Qed.

(** Finalize's dominator preorder visits every reachable point exactly once. *)
Lemma pre_finalize_order_exact {N E} (EN : encoding N) (g : Graph.t N E) n :
  ready EN g (prepare EN g) ->
  let points := prepare EN g in
  let order := preorder (dom_search points (idom (dominator_tree points))) in
  NoDup order /\ (In n order <-> reachable g n).
Proof.
  intros Hready; cbn zeta; pose (points := prepare EN g).
  pose (parents := idom (dominator_tree points)).
  destruct (simple_lt_idom_exact EN g points Hready) as [Hmap [Hforest Hexact]].
  change (Map.wf EN parents) in Hmap; change (forest_on EN g parents) in Hforest.
  pose proof (dom_forest_ready EN g points parents Hready Hmap (proj1 Hforest)) as Hready_f.
  destruct (dfs_exact EN (dom_forest points parents) (prepare EN (dom_forest points parents)) n
    (Graph.entries (dom_forest points parents)) FinSet.empty Hready_f
    (entries_in (proj1 Hready_f))) as [Hvisited [Hnodup [Hpermutation Hpre]]].
  split; [exact Hnodup|].
  change (In n (preorder (dfs (prepare EN (dom_forest points parents)) FinSet.empty
    (Graph.entries (dom_forest points parents)))) <-> reachable g n).
  rewrite Hpre.
  exact (dom_forest_coverage EN g points parents Hready Hmap (proj1 Hforest)
    (proj2 Hforest) n).
Qed.

(** Every immediate parent's snapshot precedes the child that consumes it. *)
Lemma pre_finalize_parent_before {N E} (EN : encoding N) (g : Graph.t N E) n parent :
  ready EN g (prepare EN g) ->
  Map.get EN n (idom (dominator_tree (prepare EN g))) = Some parent ->
  before (preorder (dom_search (prepare EN g) (idom (dominator_tree (prepare EN g))))) parent n.
Proof.
  intros Hready Hparent; pose (points := prepare EN g).
  pose (parents := idom (dominator_tree points)).
  destruct (simple_lt_idom_exact EN g points Hready) as [Hmap [Hforest Hexact]].
  change (Map.wf EN parents) in Hmap; change (forest_on EN g parents) in Hforest.
  change (Map.get EN n parents = Some parent) in Hparent.
  pose proof (dom_forest_ready EN g points parents Hready Hmap (proj1 Hforest)) as Hready_f.
  assert (FinSet.mem EN n (visited (dom_search points parents)) = true) as Hvisited.
  { apply (proj2 (dom_forest_coverage EN g points parents Hready Hmap (proj1 Hforest)
      (proj2 Hforest) n)); exact (proj1 (proj1 Hforest n parent Hparent)). }
  destruct (dfs_tree EN (dom_forest points parents) (prepare EN (dom_forest points parents)) n
    (Graph.entries (dom_forest points parents)) FinSet.empty Hready_f
    (entries_in (proj1 Hready_f)) Hvisited)
    as [[Hroot Htree]|[e [Htree [Hedge [Htarget [Hvisited_parent Hbefore]]]]]].
  - apply (dom_roots EN g points parents Hready n) in Hroot.
    destruct Hroot as [Hreachable Hnone]; congruence.
  - change (e = n) in Htarget; subst e.
    change (before (preorder (dom_search points parents))
      (match Map.get EN n parents with Some p => p | None => n end) n) in Hbefore.
    rewrite Hparent in Hbefore; exact Hbefore.
Qed.

Local Lemma pre_finalize_before_prefix {N} (prefix suffix : list N) parent n :
  NoDup (prefix ++ n :: suffix) -> before (prefix ++ n :: suffix) parent n -> In parent prefix.
Proof.
  induction prefix as [|head prefix IH]; intros Hnodup Hbefore.
  - exfalso; exact (dfs_before_head_false n suffix parent Hnodup Hbefore).
  - cbn [app] in Hnodup, Hbefore; apply dfs_before_cons in Hbefore.
    destruct Hbefore as [[-> Hin]|Hbefore]; [left; reflexivity|].
    right; apply IH; [inversion Hnodup; assumption|exact Hbefore].
Qed.

Local Lemma pre_finalize_table_step_defined {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments initial work n q :
  (exists scope, Map.get EN q (fst work) = Some scope) \/ q = n ->
  exists scope, Map.get EN q (fst
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial work n)) =
      Some scope.
Proof.
  intros Hdefined; destruct work as [outputs p]; unfold pre_finalize_table_step.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end,p) n) as [scope output]; cbn [fst].
  destruct (dfs_eq_dec EN q n) as [->|Hne].
  - exists scope; apply Map.get_set_same.
  - destruct Hdefined as [[old Hget]|Heq]; [|contradiction].
    exists old; rewrite Map.get_set_other by exact Hne; exact Hget.
Qed.

Local Lemma pre_finalize_table_coverage {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments initial
    nodes work q :
  (exists scope, Map.get EN q (fst work) = Some scope) \/ In q nodes ->
  exists scope, Map.get EN q (fst (fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
    nodes work)) = Some scope.
Proof.
  revert work; induction nodes as [|n nodes IH]; intros work Hdefined.
  - destruct Hdefined as [Hdefined|Hfalse]; [exact Hdefined|contradiction].
  - cbn [fold_left]; apply IH.
    destruct Hdefined as [Hdefined|[Heq|Hin]].
    + left; apply pre_finalize_table_step_defined; left; exact Hdefined.
    + left; apply pre_finalize_table_step_defined; right; symmetry; exact Heq.
    + right; exact Hin.
Qed.

(** A valid parent lookup cannot fall back to the initial scope during the actual traversal. *)
Lemma pre_finalize_parent_snapshot {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts phis arguments initial
    prefix suffix n parent :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  preorder (dom_search points (idom tree)) = prefix ++ n :: suffix ->
  Map.get EN n (idom tree) = Some parent ->
  exists scope, Map.get EN parent (fst (fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
    prefix (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) = Some scope.
Proof.
  intros Hready; cbn zeta; intros Horder Hparent.
  apply pre_finalize_table_coverage; right.
  apply (pre_finalize_before_prefix prefix suffix parent n).
  - rewrite <- Horder; exact (proj1 (pre_finalize_order_exact EN _ n Hready)).
  - rewrite <- Horder; apply pre_finalize_parent_before; assumption.
Qed.

(** Every eligible initial class is present in the initial Finalize scope. *)
Lemma pre_finalize_initial_complete {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) versions u :
  pre_initial_available a u = true -> In (FrInitial u) versions ->
  Map.get (frg_version_encoding EB EE EU) (FrInitial u)
    (pre_finalize_initial EB EE EU a versions) = Some (PreInitial u).
Proof.
  intros Havailable Hin; unfold pre_finalize_initial.
  assert (forall (scope : pre_finalize_scope B E U),
    Map.get (frg_version_encoding EB EE EU) (FrInitial u) scope = Some (PreInitial u) \/
      In (FrInitial u) versions ->
    Map.get (frg_version_encoding EB EE EU) (FrInitial u)
      (fold_left (fun scope version => match version with
      | FrInitial x => if pre_initial_available a x then
          Map.set (frg_version_encoding EB EE EU) version (PreInitial x) scope else scope
      | _ => scope
      end) versions scope) = Some (PreInitial u)) as Hfold.
  { clear Hin; induction versions as [|version versions IH]; intros scope Hdefined.
    - destruct Hdefined as [Hget|Hfalse]; [exact Hget|contradiction].
    - cbn [fold_left]; apply IH; destruct Hdefined as [Hget|[Hhead|Hrest]].
      + left; destruct version as [x|x|e x|b x]; try exact Hget.
        destruct (pre_initial_available a x); [|exact Hget].
        destruct (dfs_eq_dec EU u x) as [->|Hne].
        * apply Map.get_set_same.
        * rewrite Map.get_set_other; [exact Hget|intro Heq; injection Heq as Heq; contradiction].
      + subst version; left; rewrite Havailable; apply Map.get_set_same.
      + right; exact Hrest. }
  apply Hfold; right; exact Hin.
Qed.

(** A block's parameter edge starts at its first point in the ordered instruction chain. *)
Lemma pre_parameter_source_first {B BE N E V} (s : ssa_points B BE N E V) b :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  exists first, nth_error (points_in_block s b) 0 = Some first /\
    Graph.source (live_graph (point_model s)) (parameter_edge s b) = first.
Proof.
  intros Hpoints Hb; pose proof (points_ordered Hpoints b Hb) as Hchain.
  pose proof (parameter_edge_first Hpoints b Hb) as Hfirst.
  destruct Hchain as [n|n m ns e es Hout Htarget Hchain]; [discriminate Hfirst|].
  cbn in Hfirst; injection Hfirst as Heq; subst e; exists n; split; [reflexivity|].
  exact (out_source (points_graph_wf Hpoints) n (parameter_edge s b) Hout).
Qed.

(** No listed point edge enters the unique C19 entry point. *)
Lemma pre_point_entry_no_incoming {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e n :
  pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  In n (Graph.entries (live_graph (point_model (pre_ssa_points a)))) ->
  Graph.target (live_graph (point_model (pre_ssa_points a))) e <> n.
Proof.
  intros Ha Hedge Hentry Heq; pose proof (pre_expr_points EV a Ha) as Hpoints.
  destruct (block_edge_of (pre_ssa_points a) e) as [be|] eqn:Hblock.
  - destruct (pre_expr_entry_position EV a Ha) as [entry [first [Hb [Hn Hfirst]]]].
    rewrite Hn in Hentry; destruct Hentry as [Hentry|Hfalse]; [subst n|contradiction].
    assert (In entry (Graph.nodes (block_graph (pre_ssa_points a)))) as Hentry_block.
    { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hb; left; reflexivity. }
    assert (block_of_point (pre_ssa_points a) first = entry) as Howner.
    { apply (points_owner Hpoints); [exact Hentry_block|eapply nth_error_In; exact Hfirst]. }
    apply in_flat_map in Hedge; destruct Hedge as [source [Hsource Hout]].
    pose proof (point_edge_projection Hpoints source e Hsource Hout) as Hproject.
    rewrite Hblock, Heq, Howner in Hproject; destruct Hproject as [Hbe [Htarget Hrest]].
    apply (pre_expr_entry_no_incoming EV a Ha entry be).
    + rewrite Hb; left; reflexivity.
    + apply in_flat_map; exists (block_of_point (pre_ssa_points a) source); split; [|exact Hbe].
      exact (proj1 (AnalysesSsaPreGraph.pre_point_owner_listed _ source Hpoints Hsource)).
    + exact Htarget.
  - exact (AnalysesSsaPreGraph.pre_internal_target_not_entry EV a e n Ha Hedge Hblock
      Hentry Heq).
Qed.

(** Every actual predecessor of a parameter source is its particular incoming block edge. *)
Lemma pre_parameter_predecessor {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) b incoming :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  In incoming (edges_of (live_graph (point_model s))) ->
  Graph.target (live_graph (point_model s)) incoming =
    Graph.source (live_graph (point_model s)) (parameter_edge s b) ->
  exists be, Map.get EBE be (pre_point_edge_index EBE s) = Some incoming /\
    Graph.target (block_graph s) be = b.
Proof.
  intros Hpoints Hb Hedge Htarget.
  destruct (pre_parameter_source_first s b Hpoints Hb) as [first [Hfirst Hsource]].
  destruct (block_edge_of s incoming) as [be|] eqn:Hblock.
  - exists be; split.
    + apply (proj2 (pre_point_edge_index_exact EBE s Hpoints be incoming)); split; assumption.
    + apply in_flat_map in Hedge; destruct Hedge as [n [Hn Hout]].
      pose proof (point_edge_projection Hpoints n incoming Hn Hout) as Hproject.
      rewrite Hblock, Htarget, Hsource in Hproject; destruct Hproject as [Hbe [Howner Hrest]].
      rewrite (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)) in Howner.
      exact Howner.
  - exfalso; apply (AnalysesSsaPreGraph.pre_internal_target_not_first s incoming b first
      Hpoints Hedge Hblock Hb Hfirst); rewrite Htarget; exact Hsource.
Qed.

(** A nonentry block's parameter source cannot be the unique source entry. *)
Lemma pre_parameter_source_nonentry {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) b :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
  ~ In (Graph.source (live_graph (point_model (pre_ssa_points a)))
    (parameter_edge (pre_ssa_points a) b))
    (Graph.entries (live_graph (point_model (pre_ssa_points a)))).
Proof.
  intros Ha Hb Hnonentry Hin; pose proof (pre_expr_points EV a Ha) as Hpoints.
  destruct (pre_parameter_source_first (pre_ssa_points a) b Hpoints Hb)
    as [first [Hfirst Hsource]].
  destruct (pre_expr_entry_position EV a Ha) as [entry [entry_point [Hentries [Hpoints_entry He]]]].
  rewrite Hpoints_entry, Hsource in Hin; destruct Hin as [Heq|Hfalse]; [|contradiction].
  assert (In entry (Graph.nodes (block_graph (pre_ssa_points a)))) as Hentry.
  { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hentries; left; reflexivity. }
  assert (b = entry) as ->.
  { rewrite <- (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)).
    rewrite <- Heq; exact (points_owner Hpoints entry entry_point Hentry (nth_error_In _ _ He)). }
  apply Hnonentry; rewrite Hentries; left; reflexivity.
Qed.

(** A written cache version is defined at the actual target of its writing edge. *)
Lemma pre_version_written_target {S O N E U C} (EE : encoding E)
    (v : pre_expression_view S O N E U C) e version :
  pre_version_written EE e version = true ->
  pre_version_point v version = Some (Graph.target (cfg (gkview (pre_genkill v))) e).
Proof.
  destruct version as [u|d u|d u|d u]; cbn [pre_version_written]; intro Hwritten;
    [discriminate| | |]; apply Pos.eqb_eq, (encode_injective EE) in Hwritten;
    subst d; reflexivity.
Qed.

(** A step whose target differs from a version's defining point cannot write that slot. *)
Lemma pre_version_unwritten_target {S O N E U C} (EE : encoding E)
    (v : pre_expression_view S O N E U C) e version q :
  pre_version_point v version = Some q -> Graph.target (cfg (gkview (pre_genkill v))) e <> q ->
  pre_version_written EE e version = false.
Proof.
  intros Hpoint Hdifferent; destruct (pre_version_written EE e version) eqn:Hwritten;
    [|reflexivity].
  pose proof (pre_version_written_target EE v e version Hwritten) as Htarget.
  rewrite Hpoint in Htarget; injection Htarget as Heq.
  exfalso; apply Hdifferent; symmetry; exact Heq.
Qed.

(** A real occurrence's FRG class defines its expression no later than that occurrence's result. *)
Lemma pre_frg_computation_origin {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f e u d :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_recomputed (pre_expression a) e = Some u ->
  Map.get EE e (frg_occurrence_index f) = Some d ->
  frg_version_expr d = u /\ exists q, frg_version_point a d = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Ha Hfrg Hcomputed Hclass.
  destruct (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)
    as [Hedge [Hcomputed' Hpure]].
  assert (frg_version_expr d = u) as Hexpr by congruence.
  rewrite Hexpr in Hpure; split; [exact Hexpr|].
  destruct (frg_occurrence_exact _ _ _ _ _ _ _ _ Hfrg e u Hedge Hcomputed Hpure)
    as [selected [Hselected [Hmember [Hselected_expr Horigin]]]].
  rewrite Hclass in Hselected; injection Hselected as <-.
  destruct Horigin as [->|[[Hmember' [Hexpr' [q [Hpoint [Hdom Hnearest]]]]] Hstable]].
  - eexists; split; [reflexivity|apply dominates_refl].
  - exists q; split; [exact Hpoint|].
    eapply dominates_trans; [exact Hdom|].
    apply (AnalysesSsaPreGraph.pre_internal_source_dominates EV a e Ha Hedge).
    exact (proj1 (pre_expr_real_internal EV a Ha e u Hcomputed)).
Qed.

(** A resolved definition retains its expression class and the class's dominating point. *)
Definition pre_finalize_version_origin {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) d version : Prop :=
  pre_version_expr version = frg_version_expr d /\ exists class_point version_point,
    frg_version_point a d = Some class_point /\
    pre_version_point (pre_expression a) version = Some version_point /\
    dominates (live_graph (point_model (pre_ssa_points a))) class_point version_point.

(** A scope slot retains the original class point as a dominator of its actual definition. *)
Definition pre_finalize_scope_origin {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (scope : pre_finalize_scope B E U) : Prop :=
  forall d version, Map.get (frg_version_encoding EB EE EU) d scope = Some version ->
    pre_finalize_version_origin a d version.

Local Lemma pre_finalize_scope_origin_set {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d version :
  pre_finalize_scope_origin EB EE EU a scope ->
  pre_version_expr version = frg_version_expr d ->
  (exists class_point version_point, frg_version_point a d = Some class_point /\
    pre_version_point (pre_expression a) version = Some version_point /\
    dominates (live_graph (point_model (pre_ssa_points a))) class_point version_point) ->
  pre_finalize_scope_origin EB EE EU a
    (Map.set (frg_version_encoding EB EE EU) d version scope).
Proof.
  intros Hscope Hexpr Horigin query selected Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[-> ->]|Hget]; [split; assumption|eapply Hscope; exact Hget].
Qed.

(** Initial scope construction retains exact entry origins for every stored eligible class. *)
Lemma pre_finalize_initial_origin {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) versions :
  pre_expr_ssa_laws EV a ->
  pre_finalize_scope_origin EB EE EU a (pre_finalize_initial EB EE EU a versions).
Proof.
  intro Ha; unfold pre_finalize_initial; apply pre_finalize_fold_invariant.
  - intros d version Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros scope d Hin Hscope; destruct d as [u|u|e u|b u]; try exact Hscope.
    destruct (pre_initial_available a u); [|exact Hscope].
    apply pre_finalize_scope_origin_set; [exact Hscope|reflexivity|].
    destruct (pre_expr_entry_position EV a Ha) as [entry [first [Hb [Hn Hfirst]]]].
    exists first, first; split.
    + cbn [frg_version_point]; rewrite Hn; reflexivity.
    + split; [|apply dominates_refl].
      unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha), Hn; reflexivity.
Qed.

Local Lemma pre_finalize_phi_origin {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope k :
  pre_expr_ssa_laws EV a -> pre_finalize_scope_origin EB EE EU a scope ->
  pre_finalize_scope_origin EB EE EU a (pre_finalize_define_phi EB EE EU a scope k).
Proof.
  intros Ha Hscope; destruct k as [b u]; apply pre_finalize_scope_origin_set;
    [exact Hscope|reflexivity|].
  exists (Graph.target (live_graph (point_model (pre_ssa_points a)))
    (parameter_edge (pre_ssa_points a) b)),
    (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)); split; [reflexivity|].
  split; [|apply dominates_refl].
  unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha); reflexivity.
Qed.

Local Lemma pre_finalize_occurrence_origin {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a (fst work) ->
  pre_finalize_scope_origin EB EE EU a
    (fst (pre_finalize_occurrence EB EN EE EU a f tree work e)).
Proof.
  intros Ha Hfrg Hscope; destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
    destruct (Map.get EE e (frg_occurrence_index f)) as [d|] eqn:Hclass; try exact Hscope.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hscope].
  destruct (pre_finalize_available EB EN EE EU a tree scope d u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)); [exact Hscope|].
  destruct (pre_frg_computation_origin EB EBE EN EE EV EU a f e u d Ha Hfrg Hcomputed Hclass)
    as [Hexpr [q [Hpoint Hdom]]].
  apply pre_finalize_scope_origin_set; [exact Hscope|symmetry; exact Hexpr|].
  exists q, (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
  split; [exact Hpoint|]; split; [|exact Hdom].
  unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha); reflexivity.
Qed.

Local Lemma pre_finalize_node_origin {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a (fst work) ->
  pre_finalize_scope_origin EB EE EU a
    (fst (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)).
Proof.
  intros Ha Hfrg Hscope; destruct work as [scope p]; unfold pre_finalize_node.
  apply (pre_finalize_fold_invariant _ (fun work =>
    pre_finalize_scope_origin EB EE EU a (fst work))).
  - cbn [fst]; apply pre_finalize_fold_invariant; [exact Hscope|].
    intros frames k Hin Hframes; apply (pre_finalize_phi_origin EB EE EV EU a); assumption.
  - intros work e Hin Hwork; eapply pre_finalize_occurrence_origin; eassumption.
Qed.

Local Lemma pre_finalize_table_origin {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments initial work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a initial ->
  (forall point scope, Map.get EN point (fst work) = Some scope ->
    pre_finalize_scope_origin EB EE EU a scope) ->
  forall point scope, Map.get EN point (fst
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial work n)) =
      Some scope -> pre_finalize_scope_origin EB EE EU a scope.
Proof.
  intros Ha Hfrg Hinitial Houtputs; destruct work as [outputs p].
  unfold pre_finalize_table_step.
  pose (input := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end).
  assert (pre_finalize_scope_origin EB EE EU a input) as Hinput.
  { unfold input; destruct (Map.get EN n (idom tree)) as [parent|]; [|exact Hinitial].
    destruct (Map.get EN parent outputs) as [scope|] eqn:Hget; [|exact Hinitial].
    eapply Houtputs; exact Hget. }
  change (forall point scope, Map.get EN point (fst
    (let '(frames,output) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (input,p) n in (Map.set EN n frames outputs,output))) = Some scope ->
    pre_finalize_scope_origin EB EE EU a scope).
  pose proof (pre_finalize_node_origin EB EBE EN EE EV EU a f facts tree points phis arguments
    (input,p) n Ha Hfrg Hinput) as Hnode.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n)
    as [frames output]; cbn [fst] in Hnode |- *.
  intros point scope Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[Heq ->]|Hget]; [exact Hnode|eapply Houtputs; exact Hget].
Qed.

(** Every snapshot, including any traversal prefix, preserves its class-to-definition origin. *)
Lemma pre_finalize_scopes_origin {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments nodes :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  forall point scope, Map.get EN point (fst (fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments
      (pre_finalize_initial EB EE EU a (frg_versions f)))
    nodes (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) = Some scope ->
    pre_finalize_scope_origin EB EE EU a scope.
Proof.
  intros Ha Hfrg; apply (pre_finalize_fold_invariant _ (fun work =>
    forall point scope, Map.get EN point (fst work) = Some scope ->
      pre_finalize_scope_origin EB EE EU a scope)).
  - intros point scope Hget; change (Map.get EN point Map.empty = Some scope) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros work n Hin Hwork; eapply pre_finalize_table_origin; try eassumption.
    apply (pre_finalize_initial_origin EB EE EV EU a); exact Ha.
Qed.

(** An accepted availability query reads the same class slot it returns. *)
Lemma pre_finalize_available_lookup {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) tree scope d u n version :
  pre_finalize_available EB EN EE EU a tree scope d u n = Some version ->
  Map.get (frg_version_encoding EB EE EU) d scope = Some version.
Proof.
  unfold pre_finalize_available; destruct (Map.get (frg_version_encoding EB EE EU) d scope)
    as [selected|] eqn:Hget; [|discriminate].
  destruct (Pos.eqb (encode EU (pre_version_expr selected)) (encode EU u)); [|discriminate].
  destruct (pre_version_point (pre_expression a) selected) as [q|]; [|discriminate].
  destruct (dominates_b EN tree q n); [|discriminate].
  intro Hselected; injection Hselected as ->; reflexivity.
Qed.

(** A recorded reload carries the class-to-definition origin of the exact slot it selected. *)
Definition pre_finalize_reload_origins {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (p : pre_plan E U) : Prop :=
  forall e version, Map.get EE e (pre_reload_versions p) = Some version ->
    exists d, Map.get EE e (frg_occurrence_index f) = Some d /\
      pre_finalize_version_origin a d version.

Local Lemma pre_finalize_argument_reload_origins {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree scope p arg :
  pre_finalize_reload_origins EE a f p -> pre_finalize_reload_origins EE a f
    (pre_finalize_argument_step EB EN EE EU a facts tree scope p arg).
Proof.
  intro Hreload; destruct arg as [b u be incoming op]; unfold pre_finalize_argument_step;
    cbn [pre_arg_block pre_arg_expression pre_arg_block_edge pre_arg_point_edge pre_arg_operand].
  destruct (pre_finalize_will EB EU facts (b,u)); [|exact Hreload].
  destruct (pre_phi_translate a be u) as [translated|]; [|exact Hreload].
  destruct (pre_finalize_insert_operand EB EU facts op).
  - destruct (pre_total_pure (pre_expression a) translated &&
      negb (kill (pre_genkill (pre_expression a)) incoming translated)); exact Hreload.
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version op)
      translated (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming));
      exact Hreload.
Qed.

Local Lemma pre_finalize_occurrence_reload_origins {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a (fst work) /\
    pre_finalize_reload_origins EE a f (snd work) ->
  pre_finalize_scope_origin EB EE EU a
    (fst (pre_finalize_occurrence EB EN EE EU a f tree work e)) /\
  pre_finalize_reload_origins EE a f
    (snd (pre_finalize_occurrence EB EN EE EU a f tree work e)).
Proof.
  intros Ha Hfrg [Hscope Hreload]; split.
  - eapply pre_finalize_occurrence_origin; eassumption.
  - destruct work as [scope p]; unfold pre_finalize_occurrence.
    destruct (pre_recomputed (pre_expression a) e) as [u|];
      destruct (Map.get EE e (frg_occurrence_index f)) as [d|] eqn:Hclass; try exact Hreload.
    destruct (pre_total_pure (pre_expression a) u); [|exact Hreload].
    destruct (pre_finalize_available EB EN EE EU a tree scope d u
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as [version|]
      eqn:Havailable; [|exact Hreload].
    intros edge selected Hget; apply pre_finalize_get_set in Hget.
    destruct Hget as [[-> ->]|Hget]; [|eapply Hreload; exact Hget].
    exists d; split; [exact Hclass|]; apply Hscope.
    eapply pre_finalize_available_lookup; exact Havailable.
Qed.

Local Lemma pre_finalize_node_reload_origins {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a (fst work) /\
    pre_finalize_reload_origins EE a f (snd work) ->
  pre_finalize_scope_origin EB EE EU a
    (fst (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)) /\
  pre_finalize_reload_origins EE a f
    (snd (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)).
Proof.
  intros Ha Hfrg [Hscope Hreload]; destruct work as [scope p]; unfold pre_finalize_node.
  apply (pre_finalize_fold_invariant _ (fun work =>
    pre_finalize_scope_origin EB EE EU a (fst work) /\
      pre_finalize_reload_origins EE a f (snd work))).
  - split; cbn [fst snd].
    + apply pre_finalize_fold_invariant; [exact Hscope|].
      intros frames k Hin Hframes; apply (pre_finalize_phi_origin EB EE EV EU a); assumption.
    + apply pre_finalize_fold_invariant; [exact Hreload|].
      intros p' arg Hin Hp'; apply pre_finalize_argument_reload_origins; exact Hp'.
  - intros work e Hin Hwork; eapply pre_finalize_occurrence_reload_origins; eassumption.
Qed.

Local Definition pre_finalize_origin_table {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f
    (work : Map.t N (pre_finalize_scope B E U) * pre_plan E U) : Prop :=
  pre_finalize_reload_origins EE a f (snd work) /\
  forall point scope, Map.get EN point (fst work) = Some scope ->
    pre_finalize_scope_origin EB EE EU a scope.

Local Lemma pre_finalize_origin_table_step {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments initial work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  pre_finalize_scope_origin EB EE EU a initial -> pre_finalize_origin_table EB EN EE EU a f work ->
  pre_finalize_origin_table EB EN EE EU a f
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial work n).
Proof.
  intros Ha Hfrg Hinitial [Hreload Houtputs]; destruct work as [outputs p].
  unfold pre_finalize_table_step.
  pose (input := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end).
  assert (pre_finalize_scope_origin EB EE EU a input) as Hinput.
  { unfold input; destruct (Map.get EN n (idom tree)) as [parent|]; [|exact Hinitial].
    destruct (Map.get EN parent outputs) as [scope|] eqn:Hget; [|exact Hinitial].
    eapply Houtputs; exact Hget. }
  change (pre_finalize_origin_table EB EN EE EU a f
    (let '(frames,output) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (input,p) n in (Map.set EN n frames outputs,output))).
  pose proof (pre_finalize_node_reload_origins EB EBE EN EE EV EU a f facts tree points phis
    arguments (input,p) n Ha Hfrg (conj Hinput Hreload)) as Hnode.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n)
    as [frames output]; destruct Hnode as [Hframes Houtput]; split; [exact Houtput|].
  intros point scope Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[Heq ->]|Hget]; [exact Hframes|eapply Houtputs; exact Hget].
Qed.

(** Every actual reload preserves the originating FRG class and its defining-point dominance. *)
Theorem ssa_pre_reload_origins {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_finalize_reload_origins EE a (build_frg EB EBE EN EE EV EU a)
    (ssa_pre_place EB EBE EN EE EV EU a).
Proof.
  intros Ha Hb Hn; unfold ssa_pre_place, pre_finalize_materialize; cbn [pre_reload_versions].
  pose (f := build_frg EB EBE EN EE EV EU a).
  assert (pre_finalize_origin_table EB EN EE EU a f
    (fold_left
      (pre_finalize_table_step EB EN EE EU a f (solve_ssapre EB EBE EN EE EV EU a f)
        (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
        (prepare EN (live_graph (point_model (pre_ssa_points a))))
        (pre_finalize_phi_rows EB EN EU a f (solve_ssapre EB EBE EN EE EV EU a f))
        (pre_finalize_argument_rows EBE EN a f)
        (pre_finalize_initial EB EE EU a (frg_versions f)))
      (preorder (dom_search (prepare EN (live_graph (point_model (pre_ssa_points a))))
        (idom (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))))))
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) as Hresult.
  { apply pre_finalize_fold_invariant.
    - split.
      + intros e version Hget; change (Map.get EE e Map.empty = Some version) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
      + intros point scope Hget; change (Map.get EN point Map.empty = Some scope) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
    - intros work n Hin Hwork; eapply pre_finalize_origin_table_step; try eassumption.
      + apply build_frg_wf; assumption.
      + apply (pre_finalize_initial_origin EB EE EV EU a); exact Ha. }
  exact (proj1 Hresult).
Qed.

(** A noninserted phi input retains the actual FRG operand class it resolves. *)
Definition pre_finalize_phi_origins {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) (p : pre_plan E U) : Prop :=
  forall parameter incoming u version,
    Map.get (pair_encoding (pair_encoding EE EE) EU) ((parameter,incoming),u)
      (pre_phi_versions p) = Some version -> pre_finalize_regular version ->
    exists b be op, parameter = parameter_edge (pre_ssa_points a) b /\
      Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming /\
      Graph.target (block_graph (pre_ssa_points a)) be = b /\
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
        (frg_phi_operands f) = Some op /\
      pre_finalize_version_origin a (frg_operand_version op) version.

Local Definition pre_finalize_argument_metadata {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (arg : pre_finalize_argument B BE E U) : Prop :=
  Map.get (pair_encoding (pair_encoding EB EU) EBE)
    ((pre_arg_block arg,pre_arg_expression arg),pre_arg_block_edge arg)
    (frg_phi_operands f) = Some (pre_arg_operand arg) /\
  Map.get EBE (pre_arg_block_edge arg) (pre_point_edge_index EBE (pre_ssa_points a)) =
    Some (pre_arg_point_edge arg) /\
  Graph.target (block_graph (pre_ssa_points a)) (pre_arg_block_edge arg) = pre_arg_block arg.

Local Lemma pre_finalize_argument_metadata_rows {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f n arg :
  frg_wf EB EBE EN EE EV EU a f ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  In arg (index_edges EN (pre_finalize_argument_rows EBE EN a f) n) ->
  pre_finalize_argument_metadata EB EBE EU a f arg.
Proof.
  intros Hfrg Hwf Hin; destruct arg as [b u be incoming op].
  apply (proj1 (pre_finalize_argument_rows_exact EB EBE EN EE EU a f n b u be incoming op Hwf))
    in Hin; destruct Hin as [Hbinding [Hindex Hsource]].
  split; [exact Hbinding|]; split; [exact Hindex|].
  exact (proj2 (proj2 (frg_operand_domain _ _ _ _ _ _ _ _ Hfrg b u be op Hbinding))).
Qed.

Local Lemma pre_finalize_argument_phi_origins {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f facts tree scope p arg :
  pre_finalize_scope_origin EB EE EU a scope ->
  pre_finalize_argument_metadata EB EBE EU a f arg -> pre_finalize_phi_origins EB EBE EE EU a f p ->
  pre_finalize_phi_origins EB EBE EE EU a f
    (pre_finalize_argument_step EB EN EE EU a facts tree scope p arg).
Proof.
  intros Hscope Hmetadata Hphi; destruct arg as [b u be incoming op].
  destruct Hmetadata as [Hbinding [Hindex Htarget]].
  unfold pre_finalize_argument_step; cbn [pre_arg_block pre_arg_expression pre_arg_block_edge
    pre_arg_point_edge pre_arg_operand] in *.
  destruct (pre_finalize_will EB EU facts (b,u)); [|exact Hphi].
  destruct (pre_phi_translate a be u) as [translated|]; [|exact Hphi].
  destruct (pre_finalize_insert_operand EB EU facts op).
  - destruct (pre_total_pure (pre_expression a) translated &&
      negb (kill (pre_genkill (pre_expression a)) incoming translated)); [|exact Hphi].
    intros parameter' incoming' u' selected Hget Hregular; apply pre_finalize_get_set in Hget.
    destruct Hget as [[Hkey ->]|Hget]; [exact (False_rect _ Hregular)|].
    eapply Hphi; eassumption.
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version op)
      translated (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming))
      as [version|] eqn:Havailable; [|exact Hphi].
    intros parameter' incoming' u' selected Hget Hregular; apply pre_finalize_get_set in Hget.
    destruct Hget as [[Hkey ->]|Hget]; [|eapply Hphi; eassumption].
    inversion Hkey; subst parameter' incoming' u'.
    exists b, be, op; split; [reflexivity|]; split; [exact Hindex|].
    split; [exact Htarget|]; split; [exact Hbinding|].
    apply Hscope; eapply pre_finalize_available_lookup; exact Havailable.
Qed.

Local Lemma pre_finalize_occurrence_phi_origins {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  pre_finalize_phi_origins EB EBE EE EU a f (snd work) ->
  pre_finalize_phi_origins EB EBE EE EU a f
    (snd (pre_finalize_occurrence EB EN EE EU a f tree work e)).
Proof.
  intros Hphi; destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|];
    destruct (Map.get EE e (frg_occurrence_index f)) as [d|]; try exact Hphi.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hphi].
  destruct (pre_finalize_available EB EN EE EU a tree scope d u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)); exact Hphi.
Qed.

Local Lemma pre_finalize_node_phi_origins {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  (forall arg, In arg (index_edges EN arguments n) ->
    pre_finalize_argument_metadata EB EBE EU a f arg) ->
  pre_finalize_scope_origin EB EE EU a (fst work) /\
    pre_finalize_phi_origins EB EBE EE EU a f (snd work) ->
  pre_finalize_scope_origin EB EE EU a
    (fst (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)) /\
  pre_finalize_phi_origins EB EBE EE EU a f
    (snd (pre_finalize_node EB EN EE EU a f facts tree points phis arguments work n)).
Proof.
  intros Ha Hfrg Harguments [Hscope Hphi]; destruct work as [scope p]; unfold pre_finalize_node.
  assert (pre_finalize_scope_origin EB EE EU a
    (fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope)) as Hframes.
  { apply pre_finalize_fold_invariant; [exact Hscope|].
    intros frames k Hin Horigin; apply (pre_finalize_phi_origin EB EE EV EU a); assumption. }
  apply (pre_finalize_fold_invariant _ (fun work =>
    pre_finalize_scope_origin EB EE EU a (fst work) /\
      pre_finalize_phi_origins EB EBE EE EU a f (snd work))).
  - split; [exact Hframes|]; cbn [snd].
    apply pre_finalize_fold_invariant; [exact Hphi|].
    intros p' arg Hin Hp'; apply pre_finalize_argument_phi_origins;
      [exact Hframes|apply Harguments; exact Hin|exact Hp'].
  - intros work e Hin [Horigin Hplan]; split.
    + eapply pre_finalize_occurrence_origin; eassumption.
    + apply pre_finalize_occurrence_phi_origins; exact Hplan.
Qed.

Local Definition pre_finalize_phi_origin_table {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f
    (work : Map.t N (pre_finalize_scope B E U) * pre_plan E U) : Prop :=
  pre_finalize_phi_origins EB EBE EE EU a f (snd work) /\
  forall point scope, Map.get EN point (fst work) = Some scope ->
    pre_finalize_scope_origin EB EE EU a scope.

Local Lemma pre_finalize_phi_origin_table_step {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts tree points phis arguments initial work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  (forall arg, In arg (index_edges EN arguments n) ->
    pre_finalize_argument_metadata EB EBE EU a f arg) ->
  pre_finalize_scope_origin EB EE EU a initial ->
  pre_finalize_phi_origin_table EB EBE EN EE EU a f work ->
  pre_finalize_phi_origin_table EB EBE EN EE EU a f
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial work n).
Proof.
  intros Ha Hfrg Harguments Hinitial [Hphi Houtputs]; destruct work as [outputs p].
  unfold pre_finalize_table_step.
  pose (input := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end).
  assert (pre_finalize_scope_origin EB EE EU a input) as Hinput.
  { unfold input; destruct (Map.get EN n (idom tree)) as [parent|]; [|exact Hinitial].
    destruct (Map.get EN parent outputs) as [scope|] eqn:Hget; [|exact Hinitial].
    eapply Houtputs; exact Hget. }
  change (pre_finalize_phi_origin_table EB EBE EN EE EU a f
    (let '(frames,output) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (input,p) n in (Map.set EN n frames outputs,output))).
  pose proof (pre_finalize_node_phi_origins EB EBE EN EE EV EU a f facts tree points phis
    arguments (input,p) n Ha Hfrg Harguments (conj Hinput Hphi)) as Hnode.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n)
    as [frames output]; destruct Hnode as [Hframes Houtput]; split; [exact Houtput|].
  intros point scope Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[Heq ->]|Hget]; [exact Hframes|eapply Houtputs; exact Hget].
Qed.

(** Every produced regular phi input retains the actual edge-specific operand's class origin. *)
Theorem ssa_pre_phi_origins {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_finalize_phi_origins EB EBE EE EU a (build_frg EB EBE EN EE EV EU a)
    (ssa_pre_place EB EBE EN EE EV EU a).
Proof.
  intros Ha Hb Hn; unfold ssa_pre_place, pre_finalize_materialize; cbn [pre_phi_versions].
  pose (f := build_frg EB EBE EN EE EV EU a).
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  assert (pre_finalize_phi_origin_table EB EBE EN EE EU a f
    (fold_left
      (pre_finalize_table_step EB EN EE EU a f (solve_ssapre EB EBE EN EE EV EU a f)
        (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
        (prepare EN (live_graph (point_model (pre_ssa_points a))))
        (pre_finalize_phi_rows EB EN EU a f (solve_ssapre EB EBE EN EE EV EU a f))
        (pre_finalize_argument_rows EBE EN a f)
        (pre_finalize_initial EB EE EU a (frg_versions f)))
      (preorder (dom_search (prepare EN (live_graph (point_model (pre_ssa_points a))))
        (idom (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))))))
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) as Hresult.
  { apply pre_finalize_fold_invariant.
    - split.
      + intros parameter incoming u version Hget Hregular.
        change (Map.get (pair_encoding (pair_encoding EE EE) EU)
          ((parameter,incoming),u) Map.empty = Some version) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
      + intros point scope Hget; change (Map.get EN point Map.empty = Some scope) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
    - intros work n Hin Hwork; eapply pre_finalize_phi_origin_table_step; try eassumption.
      + intros arg Harg; eapply pre_finalize_argument_metadata_rows; [exact Hfrg| |exact Harg].
        exact (proj1 (proj2 (proj2 (proj2 (build_frg_indexes_wf EB EBE EN EE EV EU a))))).
      + apply (pre_finalize_initial_origin EB EE EV EU a); exact Ha. }
  exact (proj1 Hresult).
Qed.

(** Every required expression phi belongs to a listed nonentry block under C19. *)
Lemma pre_phi_needed_nonentry {S O B BE N E V K C U} (EB : encoding B) (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u b :
  pre_expr_ssa_laws EV a -> frg_phi_needed EB EU a u b ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))).
Proof.
  intros Ha Hphi; pose proof (pre_expr_points EV a Ha) as Hpoints.
  assert (forall d block, in_df (block_graph (pre_ssa_points a)) d block ->
    In block (Graph.nodes (block_graph (pre_ssa_points a))) /\
      ~ In block (Graph.entries (block_graph (pre_ssa_points a)))) as Hfrontier.
  { intros d block [edge [Hout [Htarget [Hreachable Hrest]]]].
    assert (In (Graph.source (block_graph (pre_ssa_points a)) edge)
      (Graph.nodes (block_graph (pre_ssa_points a)))) as Hsource.
    { eapply reachable_in_nodes; [exact (blocks_graph_wf Hpoints)|exact Hreachable]. }
    split.
    - rewrite <- Htarget; eapply out_target_in; [exact (blocks_graph_wf Hpoints)|
        exact Hsource|exact Hout].
    - intro Hentry; apply (pre_expr_entry_no_incoming EV a Ha block edge Hentry).
      + apply in_flat_map; eexists; split; [exact Hsource|exact Hout].
      + exact Htarget. }
  destruct Hphi as [u block x Hfamily Hblock Hnonentry Hoperand Hparameter|
    u d block Hfamily Hdefinition Hdf|u d block Hneeded Hdf|
    u block be translated owner Hneeded Hedge Htarget Htranslate Hdf].
  - split; assumption.
  - eapply Hfrontier; exact Hdf.
  - eapply Hfrontier; exact Hdf.
  - eapply Hfrontier; exact Hdf.
Qed.

(** * Complete Finalize scopes *)

(** Two internal instruction edges with the same source belong to the same chain position. *)
Lemma pre_internal_source_unique {B BE N E V} (s : ssa_points B BE N E V) e e' :
  ssa_point_laws s -> In e (edges_of (live_graph (point_model s))) ->
  In e' (edges_of (live_graph (point_model s))) ->
  block_edge_of s e = None -> block_edge_of s e' = None ->
  Graph.source (live_graph (point_model s)) e =
    Graph.source (live_graph (point_model s)) e' -> e = e'.
Proof.
  intros Hpoints He He' Hi Hi' Hsource.
  destruct (AnalysesSsaPreGraph.pre_internal_edge_block s e Hpoints He Hi)
    as [b [Hb [Hedge Htarget]]].
  destruct (AnalysesSsaPreGraph.pre_internal_edge_block s e' Hpoints He' Hi')
    as [c [Hc [Hedge' Htarget']]].
  assert (b = c) as Heq.
  { rewrite <- (points_owner Hpoints b _ Hb
      (AnalysesSsaPreGraph.pre_chain_source_member _ _ _ e
        (points_graph_wf Hpoints) (points_ordered Hpoints b Hb) Hedge)).
    rewrite Hsource; exact (points_owner Hpoints c _ Hc
      (AnalysesSsaPreGraph.pre_chain_source_member _ _ _ e'
        (points_graph_wf Hpoints) (points_ordered Hpoints c Hc) Hedge')). }
  subst c; eapply AnalysesSsaPreGraph.pre_chain_source_unique.
  - exact (points_graph_wf Hpoints).
  - exact (points_ordered Hpoints b Hb).
  - exact (points_unique Hpoints b).
  - exact Hedge.
  - exact Hedge'.
  - exact Hsource.
Qed.

(** A point dominating an entry is that entry, by the empty entry path. *)
Lemma pre_dominates_entry {N E} (g : Graph.t N E) q n :
  In n (Graph.entries g) -> dominates g q n -> q = n.
Proof.
  intros Hentry Hdom; destruct (Hdom n [] Hentry (path_nil n)) as [Heq|[e [Hfalse Htarget]]].
  - exact Heq.
  - contradiction.
Qed.

(** A slot is available when its exact value definition dominates the query point. *)
Definition pre_finalize_slot_available {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d n : Prop :=
  exists version q, Map.get (frg_version_encoding EB EE EU) d scope = Some version /\
    pre_version_expr version = frg_version_expr d /\
    pre_version_point (pre_expression a) version = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q n.

(** Entry classes, enabled phis and dominating real uses are the complete scope demands. *)
Definition pre_finalize_need {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    facts (strict_phi : bool) n d : Prop :=
  (exists u, d = FrInitial u /\ In d (frg_versions f)) \/
  (exists b u, d = FrPhi b u /\
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true /\
    pre_finalize_will EB EU facts (b,u) = true /\
    (if strict_phi then strictly_dominates else dominates)
      (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b)) n) \/
  exists e, Map.get EE e (frg_occurrence_index f) = Some d /\
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n.

(** Input scopes exclude the current point's phis; the following definition pass adds them. *)
Definition pre_finalize_ready {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts strict_phi n scope : Prop :=
  forall d, pre_finalize_need EB EE EU a f facts strict_phi n d ->
    pre_finalize_slot_available EB EE EU a scope d n.

Local Lemma pre_finalize_need_full {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts n d :
  pre_finalize_need EB EE EU a f facts true n d ->
  pre_finalize_need EB EE EU a f facts false n d.
Proof.
  intros [Hinitial|[Hphi|Hreal]]; [left; exact Hinitial| |right; right; exact Hreal].
  destruct Hphi as [b [u [Hd [Hmember [Hwill [Hdom Hne]]]]]].
  right; left; exists b, u; repeat split; assumption.
Qed.

Local Lemma pre_finalize_slot_mono {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d n m :
  pre_finalize_slot_available EB EE EU a scope d n ->
  dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  pre_finalize_slot_available EB EE EU a scope d m.
Proof.
  intros [version [q [Hget [Hexpr [Hpoint Hdom]]]]] Hlater.
  exists version, q; split; [exact Hget|]; split; [exact Hexpr|]; split; [exact Hpoint|].
  eapply dominates_trans; eassumption.
Qed.

(** A complete scope discharges the actual availability query without a fallback premise. *)
Lemma pre_finalize_ready_lookup {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts strict_phi scope d u n :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  pre_finalize_ready EB EE EU a f facts strict_phi n scope ->
  pre_finalize_need EB EE EU a f facts strict_phi n d -> frg_version_expr d = u ->
  exists version, pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
    scope d u n = Some version.
Proof.
  intros Hready Hreachable Hscope Hneed Hexpr.
  destruct (Hscope d Hneed) as [version [q [Hget [Hvalue [Hpoint Hdom]]]]].
  exists version; eapply pre_finalize_available_complete; try eassumption.
  rewrite Hvalue; exact Hexpr.
Qed.

Local Lemma pre_finalize_phi_slot_preserved {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d n b u :
  pre_expr_ssa_laws EV a ->
  dominates (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)) n ->
  pre_finalize_slot_available EB EE EU a scope d n ->
  pre_finalize_slot_available EB EE EU a
    (pre_finalize_define_phi EB EE EU a scope (b,u)) d n.
Proof.
  intros Ha Hdom [version [q [Hget [Hexpr [Hpoint Havailable]]]]].
  destruct (dfs_eq_dec (frg_version_encoding EB EE EU) d (FrPhi b u)) as [->|Hne].
  - exists (PreMerged (parameter_edge (pre_ssa_points a) b) u),
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b)).
    split; [apply Map.get_set_same|]; split; [reflexivity|]; split; [|exact Hdom].
    unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha); reflexivity.
  - exists version, q; split; [|split; [exact Hexpr|split; assumption]].
    unfold pre_finalize_define_phi; cbn [fst snd]; rewrite Map.get_set_other by exact Hne.
    exact Hget.
Qed.

Local Lemma pre_finalize_phi_fold_slot {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d n phis :
  pre_expr_ssa_laws EV a ->
  (forall b u, In (b,u) phis ->
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b)) n) ->
  pre_finalize_slot_available EB EE EU a scope d n ->
  pre_finalize_slot_available EB EE EU a
    (fold_left (pre_finalize_define_phi EB EE EU a) phis scope) d n.
Proof.
  intros Ha Hphis Hscope; apply pre_finalize_fold_invariant; [exact Hscope|].
  intros frames [b u] Hin Hframes; apply (pre_finalize_phi_slot_preserved EB EE EV EU a);
    [exact Ha|exact (Hphis b u Hin)|exact Hframes].
Qed.

(** Defining a listed phi leaves its exact merged slot in the resulting scope. *)
Lemma pre_finalize_phi_fold_complete {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) phis scope b u :
  In (b,u) phis -> Map.get (frg_version_encoding EB EE EU) (FrPhi b u)
    (fold_left (pre_finalize_define_phi EB EE EU a) phis scope) =
      Some (PreMerged (parameter_edge (pre_ssa_points a) b) u).
Proof.
  assert (forall frames,
    Map.get (frg_version_encoding EB EE EU) (FrPhi b u) frames =
      Some (PreMerged (parameter_edge (pre_ssa_points a) b) u) \/ In (b,u) phis ->
    Map.get (frg_version_encoding EB EE EU) (FrPhi b u)
      (fold_left (pre_finalize_define_phi EB EE EU a) phis frames) =
        Some (PreMerged (parameter_edge (pre_ssa_points a) b) u)) as Hfold.
  { induction phis as [|[block expression] phis IH]; intros frames Hdefined.
    - destruct Hdefined as [Hget|Hfalse]; [exact Hget|contradiction].
    - cbn [fold_left]; apply IH; destruct Hdefined as [Hget|[Heq|Hin]].
      + left; unfold pre_finalize_define_phi; cbn [fst snd].
        destruct (dfs_eq_dec (frg_version_encoding EB EE EU)
          (FrPhi b u) (FrPhi block expression)) as [Heq|Hne].
        * injection Heq as -> ->; apply Map.get_set_same.
        * rewrite Map.get_set_other by exact Hne; exact Hget.
      + inversion Heq; subst block expression; left; apply Map.get_set_same.
      + right; exact Hin. }
  intro Hin; apply Hfold; right; exact Hin.
Qed.

(** The point's enabled phi definitions complete its inherited input scope. *)
Lemma pre_finalize_phis_ready {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts n scope :
  pre_expr_ssa_laws EV a -> FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  pre_finalize_ready EB EE EU a f facts true n scope ->
  pre_finalize_ready EB EE EU a f facts false n
    (fold_left (pre_finalize_define_phi EB EE EU a)
      (index_edges EN (pre_finalize_phi_rows EB EN EU a f facts) n) scope).
Proof.
  intros Ha Hwf Hscope d Hneed.
  assert (forall block expression,
    In (block,expression) (index_edges EN (pre_finalize_phi_rows EB EN EU a f facts) n) ->
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) block)) n) as Hphis.
  { intros block expression Hin.
    apply (proj1 (pre_finalize_phi_rows_exact EB EN EU a f facts n block expression Hwf))
      in Hin; destruct Hin as [Hmember [Hwill ->]]; apply dominates_refl. }
  assert (pre_finalize_need EB EE EU a f facts true n d ->
    pre_finalize_slot_available EB EE EU a
      (fold_left (pre_finalize_define_phi EB EE EU a)
        (index_edges EN (pre_finalize_phi_rows EB EN EU a f facts) n) scope) d n) as Hinherited.
  { intro Hinput; apply (pre_finalize_phi_fold_slot EB EE EV EU a);
      [exact Ha|exact Hphis|apply Hscope; exact Hinput]. }
  destruct Hneed as [Hinitial|[Hphi|Hreal]].
  - apply Hinherited; left; exact Hinitial.
  - destruct Hphi as [b [u [-> [Hmember [Hwill Hdom]]]]].
    destruct (dfs_eq_dec EN
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b)) n) as [Heq|Hne].
    + exists (PreMerged (parameter_edge (pre_ssa_points a) b) u), n; split.
      * apply pre_finalize_phi_fold_complete.
        apply (proj2 (pre_finalize_phi_rows_exact EB EN EU a f facts n b u Hwf)).
        split; [exact Hmember|]; split; [exact Hwill|symmetry; exact Heq].
      * split; [reflexivity|]; split; [|apply dominates_refl].
        unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha), Heq; reflexivity.
    + apply Hinherited; right; left; exists b, u; split; [reflexivity|].
      split; [exact Hmember|]; split; [exact Hwill|split; assumption].
  - apply Hinherited; right; right; exact Hreal.
Qed.

(** A reachable parentless point is the unique entry in the supported point graph. *)
Lemma pre_finalize_root_entry {S O B BE N E V K C U} (EN : encoding N) (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) n :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  Map.get EN n (idom (dominator_tree
    (prepare EN (live_graph (point_model (pre_ssa_points a)))))) = None ->
  In n (Graph.entries (live_graph (point_model (pre_ssa_points a)))).
Proof.
  intros Ha Hready Hreachable Hnone.
  destruct (pre_expr_entry_position EV a Ha) as [b [first [Hb [Hentries Hfirst]]]].
  destruct (dfs_eq_dec EN n first) as [->|Hne]; [rewrite Hentries; left; reflexivity|].
  assert (dominates (live_graph (point_model (pre_ssa_points a))) first n) as Hdom.
  { intros start es Hentry Hpath; rewrite Hentries in Hentry.
    destruct Hentry as [->|Hfalse]; [left; reflexivity|contradiction]. }
  pose proof (proj1 (proj2 (proj2 (dominator_tree_with_exact EN _ _ Hready SimpleLT))
    n Hreachable) Hnone) as Hparentless.
  exfalso; apply (Hparentless first); split; [exact Hdom|congruence].
Qed.

Local Lemma pre_initial_version_point {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) u n :
  pre_expr_ssa_laws EV a -> In n (Graph.entries (live_graph (point_model (pre_ssa_points a)))) ->
  pre_version_point (pre_expression a) (PreInitial u) = Some n.
Proof.
  intros Ha Hentry; destruct (pre_expr_entry_position EV a Ha)
    as [b [first [Hb [Hentries Hfirst]]]].
  rewrite Hentries in Hentry; destruct Hentry as [->|Hfalse]; [|contradiction].
  unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha), Hentries; reflexivity.
Qed.

(** Initial eligible definitions satisfy every inherited demand at the unique entry. *)
Lemma pre_finalize_initial_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f facts n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  In n (Graph.entries (live_graph (point_model (pre_ssa_points a)))) ->
  pre_finalize_ready EB EE EU a f facts true n
    (pre_finalize_initial EB EE EU a (frg_versions f)).
Proof.
  intros Ha Hfrg Hentry d [Hinitial|[Hphi|Hreal]].
  - destruct Hinitial as [u [-> Hmember]].
    pose proof (proj1 (frg_versions_exact _ _ _ _ _ _ _ _ Hfrg (FrInitial u)) Hmember)
      as [Hfamily [Hpure Havailable]].
    exists (PreInitial u), n; split.
    + apply pre_finalize_initial_complete; assumption.
    + split; [reflexivity|]; split; [apply (pre_initial_version_point EV a); assumption|].
      apply dominates_refl.
  - destruct Hphi as [b [u [Hd [Hmember [Hwill [Hdom Hne]]]]]].
    exfalso; apply Hne; eapply pre_dominates_entry; eassumption.
  - destruct Hreal as [e [Hclass Hdom]].
    pose proof (proj1 (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)) as Hedge.
    pose proof (pre_dominates_entry _ _ n Hentry Hdom) as Heq.
    exfalso; exact (pre_point_entry_no_incoming EV a e n Ha Hedge Hentry Heq).
Qed.

Local Lemma pre_finalize_occurrence_slot_preserved {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f work e d n :
  frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  Graph.source (live_graph (point_model (pre_ssa_points a))) e = n ->
  pre_finalize_slot_available EB EE EU a (fst work) d n ->
  pre_finalize_slot_available EB EE EU a
    (fst (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) work e)) d n.
Proof.
  intros Hfrg Hready Hreachable Hsource Hslot; destruct work as [scope p].
  unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
    destruct (Map.get EE e (frg_occurrence_index f)) as [class|] eqn:Hclass; try exact Hslot.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hslot].
  destruct (pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) scope class u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as [version|]
    eqn:Havailable; [exact Hslot|].
  destruct (dfs_eq_dec (frg_version_encoding EB EE EU) d class) as [Heq|Hne].
  - subst class.
    destruct Hslot as [selected [q [Hget [Hexpr [Hpoint Hdom]]]]].
    pose proof (proj1 (proj2 (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)))
      as Hcomputed'.
    assert (pre_version_expr selected = u) as Hvalue by congruence.
    pose proof (pre_finalize_available_complete EB EN EE EU a scope d u n selected q
      Hready Hreachable Hget Hvalue Hpoint Hdom) as Hquery.
    rewrite Hsource, Hquery in Havailable; discriminate.
  - destruct Hslot as [selected [q [Hget [Hexpr [Hpoint Hdom]]]]].
    exists selected, q; split; [|split; [exact Hexpr|split; assumption]].
    cbn [fst]; rewrite Map.get_set_other by exact Hne; exact Hget.
Qed.

Local Lemma pre_finalize_available_slot {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope d n version :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
    scope d (frg_version_expr d) n = Some version ->
  pre_finalize_slot_available EB EE EU a scope d n.
Proof.
  intros Hready Havailable; unfold pre_finalize_available in Havailable.
  destruct (Map.get (frg_version_encoding EB EE EU) d scope) as [selected|] eqn:Hget;
    [|discriminate].
  destruct (Pos.eqb (encode EU (pre_version_expr selected))
    (encode EU (frg_version_expr d))) eqn:Hexpr; [|discriminate].
  destruct (pre_version_point (pre_expression a) selected) as [q|] eqn:Hpoint;
    [|discriminate].
  destruct (dominates_b EN
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) q n)
    eqn:Hdom; [|discriminate].
  exists selected, q; split; [exact Hget|]; split.
  - apply (encode_injective EU), Pos.eqb_eq; exact Hexpr.
  - split; [exact Hpoint|].
    exact (proj1 (proj2 (proj2 (dominator_tree_sound EN _ _ Hready))) q n Hdom).
Qed.

(** Processing a real occurrence supplies its class at the instruction's result point. *)
Lemma pre_finalize_occurrence_supplies {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f work e d :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  Map.get EE e (frg_occurrence_index f) = Some d ->
  pre_finalize_slot_available EB EE EU a
    (fst (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) work e))
    d (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Ha Hfrg Hready Hclass; destruct work as [scope p].
  destruct (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)
    as [Hedge [Hcomputed Hpure]].
  unfold pre_finalize_occurrence; rewrite Hcomputed, Hclass, Hpure.
  destruct (pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) scope d
    (frg_version_expr d) (Graph.source (live_graph (point_model (pre_ssa_points a))) e))
    as [version|] eqn:Havailable; cbn [fst].
  - apply (pre_finalize_slot_mono EB EE EU a scope d
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)).
    + eapply pre_finalize_available_slot; eassumption.
    + apply (AnalysesSsaPreGraph.pre_internal_source_dominates EV a e Ha Hedge).
      exact (proj1 (pre_expr_real_internal EV a Ha e _ Hcomputed)).
  - exists (PreComputed e (frg_version_expr d)),
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
    split; [apply Map.get_set_same|]; split; [reflexivity|]; split.
    + unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha); reflexivity.
    + apply dominates_refl.
Qed.

Local Lemma pre_finalize_occurrence_result_preserved {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f work e d next :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  Map.get EE e (frg_occurrence_index f) = Some d ->
  Graph.source (live_graph (point_model (pre_ssa_points a))) next =
    Graph.source (live_graph (point_model (pre_ssa_points a))) e ->
  pre_finalize_slot_available EB EE EU a (fst work) d
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e) ->
  pre_finalize_slot_available EB EE EU a
    (fst (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) work next))
    d (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Ha Hfrg Hclass Hsource Hslot; destruct work as [scope p].
  unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) next) as [u|] eqn:Hcomputed;
    destruct (Map.get EE next (frg_occurrence_index f)) as [class|] eqn:Hnext;
    try exact Hslot.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hslot].
  destruct (pre_finalize_available EB EN EE EU a
    (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) scope class u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) next)); [exact Hslot|].
  pose proof (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)
    as [Hedge [Hcomputed_e Hpure_e]].
  pose proof (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg next class Hnext)
    as [Hedge_next Hrest].
  assert (next = e) as Heq.
  { eapply pre_internal_source_unique; try eassumption.
    - exact (pre_expr_points EV a Ha).
    - exact (proj1 (pre_expr_real_internal EV a Ha next u Hcomputed)).
    - exact (proj1 (pre_expr_real_internal EV a Ha e _ Hcomputed_e)). }
  subst next; rewrite Hclass in Hnext; injection Hnext as <-.
  assert (u = frg_version_expr d) as -> by congruence.
  exists (PreComputed e (frg_version_expr d)),
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
  split; [apply Map.get_set_same|]; split; [reflexivity|]; split.
  - unfold pre_version_point; rewrite <- (pre_expr_point_graph EV a Ha); reflexivity.
  - apply dominates_refl.
Qed.

(** The outgoing fold retains the actual result supplied by each real instruction in its bucket. *)
Lemma pre_finalize_occurrences_supply {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f work edges e d :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  Map.get EE e (frg_occurrence_index f) = Some d -> In e edges ->
  (forall next, In next edges -> Graph.source (live_graph (point_model (pre_ssa_points a)))
    next = Graph.source (live_graph (point_model (pre_ssa_points a))) e) ->
  pre_finalize_slot_available EB EE EU a
    (fst (fold_left (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))) edges work))
    d (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Ha Hfrg Hready Hclass Hin Hsources; apply in_split in Hin.
  destruct Hin as [prefix [suffix ->]]; rewrite fold_left_app; cbn [fold_left].
  apply pre_finalize_fold_invariant.
  - apply (pre_finalize_occurrence_supplies EB EBE EN EE EV EU a); assumption.
  - intros nextwork next Hin Hslot.
    apply (pre_finalize_occurrence_result_preserved EB EBE EN EE EV EU a f nextwork e d next);
      try assumption.
    apply Hsources, in_or_app; right; right; exact Hin.
Qed.

Local Lemma pre_finalize_occurrences_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts work n edges :
  frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  (forall e, In e edges -> Graph.source (live_graph (point_model (pre_ssa_points a))) e = n) ->
  pre_finalize_ready EB EE EU a f facts false n (fst work) ->
  pre_finalize_ready EB EE EU a f facts false n
    (fst (fold_left (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))) edges work)).
Proof.
  intros Hfrg Hready Hreachable Hsources Hscope d Hneed.
  apply pre_finalize_fold_invariant; [apply Hscope; exact Hneed|].
  intros nextwork e Hin Hslot.
  apply (pre_finalize_occurrence_slot_preserved EB EBE EN EE EV EU a);
    [exact Hfrg|exact Hready|exact Hreachable|apply Hsources; exact Hin|exact Hslot].
Qed.

(** A child's inherited demand either already dominates its parent or is that parent's result. *)
Lemma pre_finalize_child_need {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts n child d :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n child ->
  pre_finalize_need EB EE EU a f facts true child d ->
  pre_finalize_need EB EE EU a f facts false n d \/
    exists e, Map.get EE e (frg_occurrence_index f) = Some d /\
      Graph.target (live_graph (point_model (pre_ssa_points a))) e = child.
Proof.
  intros [Hstrict Hnearest] [Hinitial|[Hphi|Hreal]].
  - left; left; exact Hinitial.
  - destruct Hphi as [b [u [Hd [Hmember [Hwill Hdom]]]]].
    left; right; left; exists b, u; repeat split; try assumption.
    apply Hnearest; exact Hdom.
  - destruct Hreal as [e [Hclass Hdom]].
    destruct (dfs_eq_dec EN (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
      child) as [Heq|Hne].
    + right; exists e; split; assumption.
    + left; right; right; exists e; split; [exact Hclass|].
      apply Hnearest; split; assumption.
Qed.

Local Lemma pre_finalize_succ_sources {S O B BE N E V K C U} (EN : encoding N)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) n :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  forall e, In e (succ_edges
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) n) ->
    Graph.source (live_graph (point_model (pre_ssa_points a))) e = n.
Proof.
  intros Ha Hready Hreachable e Hin.
  assert (In n (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) as Hnode.
  { eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hreachable]. }
  rewrite (succ_agrees (proj2 (proj2 Hready)) n Hnode) in Hin.
  exact (out_source (proj1 Hready) n e Hin).
Qed.

(** The completed outgoing scope supplies every inherited demand of each immediate child. *)
Lemma pre_finalize_child_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts work n child :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  reachable (live_graph (point_model (pre_ssa_points a))) child ->
  Map.get EN child (idom (dominator_tree
    (prepare EN (live_graph (point_model (pre_ssa_points a)))))) = Some n ->
  pre_finalize_ready EB EE EU a f facts false n (fst work) ->
  pre_finalize_ready EB EE EU a f facts true child
    (fst (fold_left (pre_finalize_occurrence EB EN EE EU a f
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))))
      (succ_edges (prepare EN (live_graph (point_model (pre_ssa_points a)))) n) work)).
Proof.
  intros Ha Hfrg Hready Hreachable Hchild Hparent Hscope d Hneed.
  pose proof (proj1 (proj1 (proj2 (dominator_tree_with_exact EN _ _ Hready SimpleLT))
    n child Hchild) Hparent) as Himmediate.
  destruct (pre_finalize_child_need EB EN EE EU a f facts n child d Himmediate Hneed)
    as [Hprior|[e [Hclass Htarget]]].
  - apply (pre_finalize_slot_mono EB EE EU a _ d n).
    + apply (pre_finalize_occurrences_ready EB EBE EN EE EV EU a f facts work n);
        try assumption.
      apply (pre_finalize_succ_sources EN EV a); assumption.
    + exact (proj1 (proj1 Himmediate)).
  - destruct (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)
      as [Hedge [Hcomputed Hpure]].
    pose proof (AnalysesSsaPreGraph.pre_internal_immediate EV a e Ha Hedge
      (proj1 (pre_expr_real_internal EV a Ha e _ Hcomputed))) as Hreal_parent.
    rewrite Htarget in Hreal_parent.
    pose proof (proj2 (proj1 (proj2 (dominator_tree_with_exact EN _ _ Hready SimpleLT))
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e) child Hchild)
      Hreal_parent) as Hreal_get.
    change (Map.get EN child (idom (dominator_tree
      (prepare EN (live_graph (point_model (pre_ssa_points a)))))) =
      Some (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) in Hreal_get.
    rewrite Hparent in Hreal_get; injection Hreal_get as Hsource.
    rewrite <- Htarget; apply (pre_finalize_occurrences_supply EB EBE EN EE EV EU a);
      try assumption.
    + assert (In n (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) as Hnode.
      { eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hreachable]. }
      rewrite (succ_agrees (proj2 (proj2 Hready)) n Hnode), Hsource.
      exact (proj2 (AnalysesSsaPreGraph.pre_listed_edge_out _ e (proj1 Hready) Hedge)).
    + intros next Hin; rewrite <- Hsource.
      apply (pre_finalize_succ_sources EN EV a n Ha Hready Hreachable next Hin).
Qed.

(** A saved output scope supplies the input of every immediate dominator child. *)
Definition pre_finalize_forward_ready {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts n scope : Prop :=
  forall child, reachable (live_graph (point_model (pre_ssa_points a))) child ->
    Map.get EN child (idom (dominator_tree
      (prepare EN (live_graph (point_model (pre_ssa_points a)))))) = Some n ->
    pre_finalize_ready EB EE EU a f facts true child scope.

Local Lemma pre_finalize_node_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts scope p n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  pre_finalize_ready EB EE EU a f facts true n scope ->
  pre_finalize_forward_ready EB EN EE EU a f facts n
    (fst (pre_finalize_node EB EN EE EU a f facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (scope,p) n)).
Proof.
  intros Ha Hfrg Hready Hwf Hreachable Hscope child Hchild Hparent.
  unfold pre_finalize_node; apply (pre_finalize_child_ready EB EBE EN EE EV EU a);
    try assumption.
  apply (pre_finalize_phis_ready EB EN EE EV EU a); assumption.
Qed.

(** Every actual traversal prefix stores complete output scopes for subsequent children. *)
Lemma pre_finalize_scopes_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts prefix suffix :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  let phis := pre_finalize_phi_rows EB EN EU a f facts in
  let arguments := pre_finalize_argument_rows EBE EN a f in
  let initial := pre_finalize_initial EB EE EU a (frg_versions f) in
  preorder (dom_search points (idom tree)) = prefix ++ suffix ->
  forall point scope, Map.get EN point (fst (fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
    prefix (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty))) = Some scope ->
    pre_finalize_forward_ready EB EN EE EU a f facts point scope.
Proof.
  intros Ha Hfrg Hready Hwf; cbn zeta; revert suffix.
  induction prefix using rev_ind; intros suffix Horder point scope Hget.
  - change (Map.get EN point Map.empty = Some scope) in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - assert (preorder (dom_search
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (idom (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))))) =
      prefix ++ x :: suffix) as Hsplit.
    { rewrite Horder, <- app_assoc; reflexivity. }
    pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
    pose (tree := dominator_tree points).
    pose (phis := pre_finalize_phi_rows EB EN EU a f facts).
    pose (arguments := pre_finalize_argument_rows EBE EN a f).
    pose (initial := pre_finalize_initial EB EE EU a (frg_versions f)).
    pose (previous := fold_left
      (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
      prefix (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)).
    assert (reachable (live_graph (point_model (pre_ssa_points a))) x) as Hreachable.
    { apply (proj1 (proj2 (pre_finalize_order_exact EN _ x Hready))).
      rewrite Hsplit; apply in_or_app; right; left; reflexivity. }
    assert (pre_finalize_ready EB EE EU a f facts true x
      (match Map.get EN x (idom tree) with
      | None => initial
      | Some parent => match Map.get EN parent (fst previous) with
        | None => initial
        | Some frames => frames
        end
      end)) as Hinput.
    { destruct (Map.get EN x (idom tree)) as [parent|] eqn:Hparent.
      - destruct (pre_finalize_parent_snapshot EB EN EE EU a f facts phis arguments initial
          prefix suffix x parent Hready Hsplit Hparent) as [frames Hframes].
        change (Map.get EN parent (fst previous) = Some frames) in Hframes.
        rewrite Hframes; apply (IHprefix (x :: suffix) Hsplit parent frames Hframes x);
          assumption.
      - apply (pre_finalize_initial_ready EB EBE EN EE EV EU a f facts x Ha Hfrg).
        apply (pre_finalize_root_entry EN EV a x); assumption. }
    assert (forall saved frames, Map.get EN saved (fst previous) = Some frames ->
      pre_finalize_forward_ready EB EN EE EU a f facts saved frames) as Houtputs.
    { intros saved frames Hframes; apply (IHprefix (x :: suffix) Hsplit saved frames).
      exact Hframes. }
    rewrite fold_left_app in Hget; cbn [fold_left] in Hget.
    change (Map.get EN point (fst
      (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial
        previous x)) = Some scope) in Hget.
    destruct previous as [outputs p]; cbn [fst snd] in Hinput.
    unfold pre_finalize_table_step in Hget.
    pose proof (pre_finalize_node_ready EB EBE EN EE EV EU a f facts _ p x
      Ha Hfrg Hready Hwf Hreachable Hinput) as Hnode.
    destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (match Map.get EN x (idom tree) with
      | None => initial
      | Some parent => match Map.get EN parent outputs with
        | None => initial
        | Some frames => frames
        end
      end,p) x) as [frames output] eqn:Hresult.
    change (pre_finalize_forward_ready EB EN EE EU a f facts x
      (fst (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
        (match Map.get EN x (idom tree) with
        | None => initial
        | Some parent => match Map.get EN parent outputs with
          | None => initial
          | Some frames => frames
          end
        end,p) x))) in Hnode.
    rewrite Hresult in Hnode; cbn [fst] in Hnode, Hget.
    apply pre_finalize_get_set in Hget; destruct Hget as [[-> ->]|Hget].
    + exact Hnode.
    + apply (Houtputs point scope); exact Hget.
Qed.

(** Every actual node receives a complete input scope from its recorded parent snapshot. *)
Lemma pre_finalize_input_ready {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts prefix suffix n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  let phis := pre_finalize_phi_rows EB EN EU a f facts in
  let arguments := pre_finalize_argument_rows EBE EN a f in
  let initial := pre_finalize_initial EB EE EU a (frg_versions f) in
  let previous := fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
    prefix (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty) in
  preorder (dom_search points (idom tree)) = prefix ++ n :: suffix ->
  pre_finalize_ready EB EE EU a f facts true n
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent (fst previous) with
      | None => initial
      | Some scope => scope
      end
    end).
Proof.
  intros Ha Hfrg Hready Hwf; cbn zeta; intro Horder.
  assert (reachable (live_graph (point_model (pre_ssa_points a))) n) as Hreachable.
  { apply (proj1 (proj2 (pre_finalize_order_exact EN _ n Hready))).
    rewrite Horder; apply in_or_app; right; left; reflexivity. }
  destruct (Map.get EN n (idom (dominator_tree
    (prepare EN (live_graph (point_model (pre_ssa_points a))))))) as [parent|] eqn:Hparent.
  - destruct (pre_finalize_parent_snapshot EB EN EE EU a f facts
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (pre_finalize_initial EB EE EU a (frg_versions f)) prefix suffix n parent Hready Horder
      Hparent) as [scope Hscope].
    rewrite Hscope.
    apply (pre_finalize_scopes_ready EB EBE EN EE EV EU a f facts prefix (n :: suffix)
      Ha Hfrg Hready Hwf Horder parent scope Hscope n Hreachable Hparent).
  - apply (pre_finalize_initial_ready EB EBE EN EE EV EU a f facts n Ha Hfrg).
    apply (pre_finalize_root_entry EN EV a n); assumption.
Qed.

(** A noninserted valid FRG operand is one of the complete demands at its incoming source. *)
Lemma pre_finalize_operand_need {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts b u be incoming op translated :
  frg_wf EB EBE EN EE EV EU a f ->
  Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
    (frg_phi_operands f) = Some op ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
  pre_phi_translate a be u = Some translated ->
  pre_finalize_insert_operand EB EU facts op = false ->
  pre_finalize_need EB EE EU a f facts false
    (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming)
    (frg_operand_version op) /\ frg_version_expr (frg_operand_version op) = translated.
Proof.
  intros Hfrg Hbinding Hindex Htranslate Hinsert.
  assert (frg_operand_version op <> FrUnavailable translated) as Havailable.
  { intro Heq; unfold pre_finalize_insert_operand in Hinsert; rewrite Heq in Hinsert;
      discriminate. }
  pose proof (proj2 (frg_operand_selection _ _ _ _ _ _ _ _ Hfrg b u be op incoming translated
    Hbinding Hindex Htranslate) Havailable) as [[Hmember [Hexpr [q [Hpoint [Hdom Hnearest]]]]]
    Hregion].
  split; [|exact Hexpr].
  destruct (frg_operand_version op) as [x|x|e x|block x] eqn:Hversion.
  - unfold pre_finalize_insert_operand in Hinsert; rewrite Hversion in Hinsert; discriminate.
  - left; exists x; split; [reflexivity|exact Hmember].
  - apply (proj1 (frg_versions_exact _ _ _ _ _ _ _ _ Hfrg (FrFresh e x))) in Hmember.
    destruct Hmember as [Hedge [Hcomputed Hfresh]].
    right; right; exists e; split.
    + exact (proj1 (frg_fresh_exact _ _ _ _ _ _ _ _ Hfrg e x Hcomputed) Hfresh).
    + cbn [frg_version_point] in Hpoint; injection Hpoint as <-; exact Hdom.
  - destruct (frg_operand_real_use op) eqn:Hreal.
    + right; right; apply (proj1 (frg_operand_real_use_exact _ _ _ _ _ _ _ _ Hfrg
        b u be op incoming Hbinding Hindex)) in Hreal.
      rewrite Hversion in Hreal; exact Hreal.
    + right; left; exists block, x; split; [reflexivity|]; split.
      * exact (proj1 (frg_versions_exact _ _ _ _ _ _ _ _ Hfrg (FrPhi block x)) Hmember).
      * split.
        -- unfold pre_finalize_insert_operand in Hinsert; rewrite Hversion, Hreal in Hinsert.
           cbn [negb andb] in Hinsert; apply negb_false_iff; exact Hinsert.
        -- cbn [frg_version_point] in Hpoint; injection Hpoint as <-; exact Hdom.
Qed.

Local Lemma pre_finalize_cross_nonkill {S O B BE N E V K C U}
    (EBE : encoding BE) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    be incoming u :
  pre_expr_ssa_laws EV a ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
  pre_expr_in_family a u -> kill (pre_genkill (pre_expression a)) incoming u = false.
Proof.
  intros Ha Hindex Hfamily.
  destruct (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
    (pre_expr_points EV a Ha) be incoming) Hindex) as [Hedge Hbe].
  destruct (kill (pre_genkill (pre_expression a)) incoming u) eqn:Hkill; [|reflexivity].
  destruct (pre_expr_kill_operand EV a Ha incoming u Hedge Hfamily Hkill)
    as [x [Hoperand Hdefined]].
  rewrite (pre_expr_cross_no_defs EV a Ha incoming be Hedge Hbe) in Hdefined; contradiction.
Qed.

(** Every enabled, valid argument records an input; no failed raw lookup drops the decision. *)
Lemma pre_finalize_argument_resolved {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts scope p b u be incoming op :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a)))
    (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming) ->
  pre_finalize_ready EB EE EU a f facts false
    (Graph.source (live_graph (point_model (pre_ssa_points a))) incoming) scope ->
  Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
    (frg_phi_operands f) = Some op ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
  pre_finalize_will EB EU facts (b,u) = true ->
  exists version, Map.get (pair_encoding (pair_encoding EE EE) EU)
    ((parameter_edge (pre_ssa_points a) b,incoming),u)
    (pre_phi_versions (pre_finalize_argument_step EB EN EE EU a facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))) scope p
      (PreFinalizeArgument b u be incoming op))) = Some version.
Proof.
  intros Ha Hfrg Hready Hreachable Hscope Hbinding Hindex Hwill.
  destruct (frg_operand_domain _ _ _ _ _ _ _ _ Hfrg b u be op Hbinding)
    as [Hmember [Hedge Htarget]].
  destruct (frg_operand_exact _ _ _ _ _ _ _ _ Hfrg b u be Hmember Hedge Htarget)
    as [selected [translated [Htranslate [Hselected [Hexpr Horigin]]]]].
  rewrite Hbinding in Hselected; injection Hselected as <-.
  unfold pre_finalize_argument_step; cbn [pre_arg_block pre_arg_expression pre_arg_block_edge
    pre_arg_point_edge pre_arg_operand]; rewrite Hwill, Htranslate.
  destruct (pre_finalize_insert_operand EB EU facts op) eqn:Hinsert.
  - destruct (proj1 (frg_phi_exact _ _ _ _ _ _ _ _ Hfrg b u) Hmember)
      as [Hfamily [Hpure Hneeded]].
    rewrite (pre_expr_translation_pure EV a Ha be u translated Hpure Htranslate).
    assert (pre_expr_in_family a translated) as Htranslated.
    { eapply pre_family_translate; eassumption. }
    rewrite (pre_finalize_cross_nonkill EBE EV a be incoming translated Ha Hindex Htranslated).
    cbn [negb andb]; eexists; apply Map.get_set_same.
  - destruct (pre_finalize_operand_need EB EBE EN EE EV EU a f facts b u be incoming op
      translated Hfrg Hbinding Hindex Htranslate Hinsert) as [Hneed Hvalue].
    destruct (pre_finalize_ready_lookup EB EN EE EU a f facts false scope
      (frg_operand_version op) translated _ Hready Hreachable Hscope Hneed Hvalue)
      as [version Havailable].
    rewrite Havailable; exists version; apply Map.get_set_same.
Qed.

Local Lemma pre_finalize_select_defined {E U} (EE : encoding E) (EU : encoding U)
    p parameter incoming u version key :
  (exists selected, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions p) = Some selected) ->
  exists selected, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (pre_finalize_select EE EU p parameter incoming u version)) = Some selected.
Proof.
  intros [selected Hget]; unfold pre_finalize_select; cbn [pre_phi_versions].
  destruct (dfs_eq_dec (pair_encoding (pair_encoding EE EE) EU) key ((parameter,incoming),u))
    as [->|Hne].
  - exists version; apply Map.get_set_same.
  - exists selected; rewrite Map.get_set_other by exact Hne; exact Hget.
Qed.

Local Lemma pre_finalize_argument_defined {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) facts tree scope p arg key :
  (exists selected, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions p) = Some selected) ->
  exists selected, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (pre_finalize_argument_step EB EN EE EU a facts tree scope p arg)) =
      Some selected.
Proof.
  intro Hdefined; unfold pre_finalize_argument_step.
  destruct (pre_finalize_will EB EU facts (pre_arg_block arg,pre_arg_expression arg));
    [|exact Hdefined].
  destruct (pre_phi_translate a (pre_arg_block_edge arg) (pre_arg_expression arg));
    [|exact Hdefined].
  destruct (pre_finalize_insert_operand EB EU facts (pre_arg_operand arg)).
  - destruct (pre_total_pure (pre_expression a) u &&
      negb (kill (pre_genkill (pre_expression a)) (pre_arg_point_edge arg) u));
      [apply pre_finalize_select_defined; exact Hdefined|exact Hdefined].
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version
      (pre_arg_operand arg)) u (Graph.source (live_graph (point_model (pre_ssa_points a)))
        (pre_arg_point_edge arg))); [apply pre_finalize_select_defined; exact Hdefined|
      exact Hdefined].
Qed.

Local Lemma pre_finalize_occurrence_phi_same {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  pre_phi_versions (snd (pre_finalize_occurrence EB EN EE EU a f tree work e)) =
    pre_phi_versions (snd work).
Proof.
  destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e);
    destruct (Map.get EE e (frg_occurrence_index f)); try reflexivity.
  destruct (pre_total_pure (pre_expression a) u); [|reflexivity].
  destruct (pre_finalize_available EB EN EE EU a tree scope f0 u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)); reflexivity.
Qed.

Local Lemma pre_finalize_occurrences_phi_same {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f tree work edges :
  pre_phi_versions (snd (fold_left (pre_finalize_occurrence EB EN EE EU a f tree)
    edges work)) = pre_phi_versions (snd work).
Proof.
  revert work; induction edges as [|e edges IH]; intro work; [reflexivity|].
  cbn [fold_left]; rewrite IH; apply pre_finalize_occurrence_phi_same.
Qed.

Local Lemma pre_finalize_node_defined {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments work n key :
  (exists version, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (snd work)) = Some version) ->
  exists version, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (snd (pre_finalize_node EB EN EE EU a f facts tree points phis
      arguments work n))) = Some version.
Proof.
  destruct work as [scope p]; intro Hdefined; unfold pre_finalize_node.
  rewrite pre_finalize_occurrences_phi_same; cbn [snd].
  apply pre_finalize_fold_invariant; [exact Hdefined|].
  intros next arg Hin Hnext; apply pre_finalize_argument_defined; exact Hnext.
Qed.

Local Lemma pre_finalize_table_defined {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments initial work n
    key :
  (exists version, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (snd work)) = Some version) ->
  exists version, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions (snd (pre_finalize_table_step EB EN EE EU a f facts tree points phis
      arguments initial work n))) = Some version.
Proof.
  destruct work as [outputs p]; intro Hdefined; unfold pre_finalize_table_step.
  pose proof (pre_finalize_node_defined EB EN EE EU a f facts tree points phis arguments
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end,p) n key Hdefined) as Hnode.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end,p) n); exact Hnode.
Qed.

(** A node records every enabled incoming argument before processing its outgoing instructions. *)
Lemma pre_finalize_node_resolved {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts scope p n b u be incoming op :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  pre_finalize_ready EB EE EU a f facts true n scope ->
  Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b,u),be)
    (frg_phi_operands f) = Some op ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
  n = Graph.source (live_graph (point_model (pre_ssa_points a))) incoming ->
  pre_finalize_will EB EU facts (b,u) = true ->
  exists version, Map.get (pair_encoding (pair_encoding EE EE) EU)
    ((parameter_edge (pre_ssa_points a) b,incoming),u)
    (pre_phi_versions (snd (pre_finalize_node EB EN EE EU a f facts
      (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a)))))
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (scope,p) n))) = Some version.
Proof.
  intros Ha Hfrg Hready Hphis Harguments Hreachable Hscope Hbinding Hindex Hsource Hwill.
  pose proof (pre_finalize_phis_ready EB EN EE EV EU a f facts n scope Ha Hphis Hscope)
    as Hfull.
  assert (In (PreFinalizeArgument b u be incoming op)
    (index_edges EN (pre_finalize_argument_rows EBE EN a f) n)) as Hin.
  { apply (proj2 (pre_finalize_argument_rows_exact EB EBE EN EE EU a f n b u be incoming op
      Harguments)); repeat split; assumption. }
  apply in_split in Hin; destruct Hin as [prefix [suffix Hrows]].
  unfold pre_finalize_node; rewrite pre_finalize_occurrences_phi_same; cbn [snd].
  rewrite Hrows, fold_left_app; cbn [fold_left].
  apply pre_finalize_fold_invariant.
  - apply (pre_finalize_argument_resolved EB EBE EN EE EV EU a f facts);
      try assumption; rewrite <- Hsource; assumption.
  - intros next arg Hin Hdefined; apply pre_finalize_argument_defined; exact Hdefined.
Qed.

Local Lemma pre_finalize_table_phi_same {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts tree points phis arguments initial outputs p
    n :
  pre_phi_versions (snd (pre_finalize_table_step EB EN EE EU a f facts tree points phis
    arguments initial (outputs,p) n)) =
  pre_phi_versions (snd (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end,p) n)).
Proof.
  unfold pre_finalize_table_step.
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end,p) n); reflexivity.
Qed.

(** All required cells of every enabled phi are present in the actual executable placement. *)
Theorem ssa_pre_phi_inputs_complete {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  forall b u be incoming,
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
    pre_finalize_will EB EU facts (b,u) = true ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some incoming ->
    exists version, Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,incoming),u)
      (pre_phi_versions (ssa_pre_place EB EBE EN EE EV EU a)) = Some version.
Proof.
  intros Ha Hb Hn; cbn zeta; intros b u be incoming Hphi Hwill Hbe Htarget Hindex.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (facts := solve_ssapre EB EBE EN EE EV EU a f).
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  destruct (build_frg_indexes_wf EB EBE EN EE EV EU a)
    as [Hoccurrences [Hfresh [Hphis [Harguments Hunsafe]]]].
  destruct (frg_operand_exact _ _ _ _ _ _ _ _ Hfrg b u be Hphi Hbe Htarget)
    as [op [translated [Htranslate [Hbinding Hrest]]]].
  destruct (proj1 (pre_point_edge_index_exact EBE (pre_ssa_points a)
    (pre_expr_points EV a Ha) be incoming) Hindex) as [Hincoming Hproject].
  pose (n := Graph.source (live_graph (point_model (pre_ssa_points a))) incoming).
  assert (reachable (live_graph (point_model (pre_ssa_points a))) n) as Hreachable.
  { apply (pre_expr_reachable_points EV a Ha).
    exact (proj1 (AnalysesSsaPreGraph.pre_listed_edge_out _ incoming (proj1 Hn) Hincoming)). }
  pose proof (proj2 (proj2 (pre_finalize_order_exact EN _ n Hn)) Hreachable) as Hmember.
  apply in_split in Hmember; destruct Hmember as [prefix [suffix Horder]].
  pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
  pose (tree := dominator_tree points).
  pose (phis := pre_finalize_phi_rows EB EN EU a f facts).
  pose (arguments := pre_finalize_argument_rows EBE EN a f).
  pose (initial := pre_finalize_initial EB EE EU a (frg_versions f)).
  pose (previous := fold_left
    (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
    prefix (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)).
  pose proof (pre_finalize_input_ready EB EBE EN EE EV EU a f facts prefix suffix n
    Ha Hfrg Hn Hphis Horder) as Hinput.
  change (preorder (dom_search points (idom tree)) = prefix ++ n :: suffix) in Horder.
  change (pre_finalize_ready EB EE EU a f facts true n
    (match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent (fst previous) with
      | None => initial
      | Some scope => scope
      end
    end)) in Hinput.
  unfold ssa_pre_place, pre_finalize_materialize; cbn [pre_phi_versions].
  change (exists version, Map.get (pair_encoding (pair_encoding EE EE) EU)
    ((parameter_edge (pre_ssa_points a) b,incoming),u)
    (pre_phi_versions (snd (fold_left
      (pre_finalize_table_step EB EN EE EU a f facts tree points phis arguments initial)
      (preorder (dom_search points (idom tree)))
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)))) = Some version).
  rewrite Horder, fold_left_app; cbn [fold_left].
  apply pre_finalize_fold_invariant.
  - change (exists version, Map.get (pair_encoding (pair_encoding EE EE) EU)
      ((parameter_edge (pre_ssa_points a) b,incoming),u)
      (pre_phi_versions (snd (pre_finalize_table_step EB EN EE EU a f facts tree points phis
        arguments initial previous n))) = Some version).
    destruct previous as [outputs p]; rewrite pre_finalize_table_phi_same.
    cbn [fst] in Hinput.
    apply (pre_finalize_node_resolved EB EBE EN EE EV EU a f facts _ p n b u be incoming op
      Ha Hfrg Hn Hphis Harguments Hreachable Hinput Hbinding Hindex eq_refl Hwill).
  - intros next point Hin Hdefined; apply pre_finalize_table_defined; exact Hdefined.
Qed.

(** * Retained definitions and snapshot provenance *)

(** Regular slots refer to eligible entry values, retained real instructions or enabled phis. *)
Definition pre_finalize_kept_version {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    facts (p : pre_plan E U) (version : pre_version E U) : Prop :=
  match version with
  | PreInitial u => pre_initial_available a u = true
  | PreComputed e u =>
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
      pre_recomputed (pre_expression a) e = Some u /\
      Map.get EE e (pre_reload_versions p) = None
  | PreMerged parameter u => exists b, parameter = parameter_edge (pre_ssa_points a) b /\
    FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true /\
      pre_finalize_will EB EU facts (b,u) = true
  | PreInserted _ _ => False
  end.

(** Computed slots in a snapshot originate in the already visited source-point prefix. *)
Definition pre_finalize_live_version {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done p version : Prop :=
  pre_finalize_kept_version EB EE EU a f facts p version /\
    match version with
    | PreComputed e _ => In (Graph.source (live_graph (point_model (pre_ssa_points a))) e) done
    | _ => True
    end.

(** A work item keeps its selected definitions and records only previously visited reloads. *)
Record pre_finalize_live {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done
    (work : pre_finalize_work B E U) : Prop := {
  pre_finalize_live_scope : forall d version,
    Map.get (frg_version_encoding EB EE EU) d (fst work) = Some version ->
    pre_finalize_live_version EB EE EU a f facts done (snd work) version;
  pre_finalize_live_reload : forall e version,
    Map.get EE e (pre_reload_versions (snd work)) = Some version ->
    pre_finalize_live_version EB EE EU a f facts done (snd work) version;
  pre_finalize_live_phi : forall key version,
    Map.get (pair_encoding (pair_encoding EE EE) EU) key
      (pre_phi_versions (snd work)) = Some version -> pre_finalize_regular version ->
    pre_finalize_live_version EB EE EU a f facts done (snd work) version;
  pre_finalize_live_sources : forall e version,
    Map.get EE e (pre_reload_versions (snd work)) = Some version ->
    In (Graph.source (live_graph (point_model (pre_ssa_points a))) e) done
}.

Local Lemma pre_finalize_live_version_frame {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done later p p' version :
  incl done later -> pre_reload_versions p' = pre_reload_versions p ->
  pre_finalize_live_version EB EE EU a f facts done p version ->
  pre_finalize_live_version EB EE EU a f facts later p' version.
Proof.
  intros Hlater Hframe Hlive; destruct version as [u|e u|e u|e u];
    destruct Hlive as [Hkept Hsource].
  - split; [exact Hkept|exact I].
  - destruct Hkept as [Hedge [Hcomputed Hnone]]; split.
    + split; [exact Hedge|]; split; [exact Hcomputed|].
      cbn [pre_finalize_kept_version]; rewrite Hframe; exact Hnone.
    + apply Hlater; exact Hsource.
  - contradiction.
  - split; [exact Hkept|exact I].
Qed.

Local Lemma pre_finalize_initial_live {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done p versions :
  forall d version, Map.get (frg_version_encoding EB EE EU) d
    (pre_finalize_initial EB EE EU a versions) = Some version ->
    pre_finalize_live_version EB EE EU a f facts done p version.
Proof.
  unfold pre_finalize_initial; apply (pre_finalize_fold_invariant _ (fun scope =>
    forall d version, Map.get (frg_version_encoding EB EE EU) d scope = Some version ->
      pre_finalize_live_version EB EE EU a f facts done p version)).
  - intros d version Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros scope d Hin Hscope; destruct d as [u|u|e u|b u]; try exact Hscope.
    destruct (pre_initial_available a u) eqn:Havailable; [|exact Hscope].
    intros query version Hget; apply pre_finalize_get_set in Hget.
    destruct Hget as [[Heq ->]|Hget]; [split; [exact Havailable|exact I]|
      eapply Hscope; exact Hget].
Qed.

Local Lemma pre_finalize_live_replace_scope {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done scope scope' p :
  pre_finalize_live EB EE EU a f facts done (scope,p) ->
  (forall d version, Map.get (frg_version_encoding EB EE EU) d scope' = Some version ->
    pre_finalize_live_version EB EE EU a f facts done p version) ->
  pre_finalize_live EB EE EU a f facts done (scope',p).
Proof.
  intros [Hscope Hreload Hphi Hsources] Hscope'; constructor; assumption.
Qed.

Local Lemma pre_finalize_define_phi_live {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done scope p b u :
  FinSet.mem (pair_encoding EB EU) (b,u) (frg_phi_index f) = true ->
  pre_finalize_will EB EU facts (b,u) = true ->
  pre_finalize_live EB EE EU a f facts done (scope,p) ->
  pre_finalize_live EB EE EU a f facts done (pre_finalize_define_phi EB EE EU a scope (b,u),p).
Proof.
  intros Hmember Hwill Hlive; apply (pre_finalize_live_replace_scope EB EE EU a _ _ _ scope);
    [exact Hlive|].
  intros d version Hget; apply pre_finalize_get_set in Hget.
  destruct Hget as [[Heq ->]|Hget].
  - split; [exists b; repeat split; assumption|exact I].
  - exact (pre_finalize_live_scope EB EE EU a f facts done (scope,p) Hlive d version Hget).
Qed.

Local Lemma pre_finalize_select_live {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done scope p parameter incoming u version :
  pre_finalize_live EB EE EU a f facts done (scope,p) ->
  (pre_finalize_regular version ->
    pre_finalize_live_version EB EE EU a f facts done p version) ->
  pre_finalize_live EB EE EU a f facts done
    (scope,pre_finalize_select EE EU p parameter incoming u version).
Proof.
  intros Hlive Hversion; destruct Hlive as [Hscope Hreload Hphi Hsources].
  assert (forall selected, pre_finalize_live_version EB EE EU a f facts done p selected ->
    pre_finalize_live_version EB EE EU a f facts done
      (pre_finalize_select EE EU p parameter incoming u version) selected) as Hframe.
  { intros selected Hselected; eapply pre_finalize_live_version_frame;
      [apply incl_refl|reflexivity|exact Hselected]. }
  constructor; cbn [fst snd].
  - intros d selected Hget; apply Hframe; eapply Hscope; exact Hget.
  - intros e selected Hget; apply Hframe; eapply Hreload; exact Hget.
  - intros key selected Hget Hregular; apply pre_finalize_get_set in Hget.
    apply Hframe; destruct Hget as [[Heq ->]|Hget];
      [apply Hversion; exact Hregular|eapply Hphi; eassumption].
  - exact Hsources.
Qed.

Local Lemma pre_finalize_argument_live {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done tree scope p arg :
  pre_finalize_live EB EE EU a f facts done (scope,p) ->
  pre_finalize_live EB EE EU a f facts done
    (scope,pre_finalize_argument_step EB EN EE EU a facts tree scope p arg).
Proof.
  intro Hlive; unfold pre_finalize_argument_step.
  destruct (pre_finalize_will EB EU facts (pre_arg_block arg,pre_arg_expression arg));
    [|exact Hlive].
  destruct (pre_phi_translate a (pre_arg_block_edge arg) (pre_arg_expression arg)); [|exact Hlive].
  destruct (pre_finalize_insert_operand EB EU facts (pre_arg_operand arg)).
  - destruct (pre_total_pure (pre_expression a) u &&
      negb (kill (pre_genkill (pre_expression a)) (pre_arg_point_edge arg) u)); [|exact Hlive].
    apply (pre_finalize_select_live EB EE EU a); [exact Hlive|intro Hfalse; contradiction].
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version
      (pre_arg_operand arg)) u (Graph.source (live_graph (point_model (pre_ssa_points a)))
        (pre_arg_point_edge arg))) as [version|] eqn:Havailable; [|exact Hlive].
    apply (pre_finalize_select_live EB EE EU a); [exact Hlive|intro Hregular].
    eapply (pre_finalize_live_scope EB EE EU a f facts done (scope,p) Hlive).
    eapply pre_finalize_available_lookup; exact Havailable.
Qed.

Local Lemma pre_finalize_fold_fixed {X A} (step : X -> A -> X) items initial :
  (forall work item, In item items -> step work item = work) ->
  fold_left step items initial = initial.
Proof.
  intro Hfixed; apply (pre_finalize_fold_invariant step (fun work => work = initial)).
  - reflexivity.
  - intros work item Hin ->; apply Hfixed; exact Hin.
Qed.

Local Lemma pre_finalize_fold_single {X A} (EA : encoding A) (step : X -> A -> X) items item :
  NoDup items -> In item items ->
  (forall work next, In next items -> next <> item -> step work next = work) ->
  forall initial, fold_left step items initial = step initial item.
Proof.
  induction items as [|head items IH]; intros Hnodup Hin Hfixed initial; [contradiction|].
  inversion Hnodup as [|head' items' Hfresh Htail]; subst head' items'.
  destruct (dfs_eq_dec EA head item) as [->|Hne]; cbn [fold_left].
  - apply pre_finalize_fold_fixed; intros work next Hnext.
    apply Hfixed; [right; exact Hnext|intro Heq; subst next; contradiction].
  - rewrite Hfixed by (try (left; reflexivity); exact Hne).
    apply IH; [exact Htail|destruct Hin as [Heq|Hin]; [congruence|exact Hin]|].
    intros work next Hnext Hnext_ne; apply Hfixed; [right; exact Hnext|exact Hnext_ne].
Qed.

Local Lemma pre_finalize_occurrence_none {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f tree work e :
  pre_recomputed (pre_expression a) e = None ->
  pre_finalize_occurrence EB EN EE EU a f tree work e = work.
Proof.
  intro Hnone; destruct work as [scope p]; unfold pre_finalize_occurrence; rewrite Hnone;
    reflexivity.
Qed.

Local Lemma pre_finalize_computation_cases {S O N E U C}
    (v : pre_expression_view S O N E U C) edges :
  (forall e, In e edges -> pre_recomputed v e = None) \/
    exists e u, In e edges /\ pre_recomputed v e = Some u.
Proof.
  induction edges as [|e edges IH].
  - left; intros next Hin; contradiction.
  - destruct (pre_recomputed v e) as [u|] eqn:Hcomputed.
    + right; exists e, u; split; [left; reflexivity|exact Hcomputed].
    + destruct IH as [Hnone|[next [u [Hin Hnext]]]].
      * left; intros next [->|Hin]; [exact Hcomputed|apply Hnone; exact Hin].
      * right; exists next, u; split; [right; exact Hin|exact Hnext].
Qed.

(** A source point has at most one real instruction, and its outgoing fold processes it once. *)
Lemma pre_finalize_occurrences_single {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) f tree n :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  let edges := succ_edges (prepare EN (live_graph (point_model (pre_ssa_points a)))) n in
  (forall work, fold_left (pre_finalize_occurrence EB EN EE EU a f tree) edges work = work) \/
    exists e u, In e edges /\ pre_recomputed (pre_expression a) e = Some u /\
      forall work, fold_left (pre_finalize_occurrence EB EN EE EU a f tree) edges work =
        pre_finalize_occurrence EB EN EE EU a f tree work e.
Proof.
  intros Ha Hready Hreachable; cbn zeta.
  assert (In n (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) as Hnode.
  { eapply reachable_in_nodes; [exact (proj1 Hready)|exact Hreachable]. }
  pose proof (succ_agrees (proj2 (proj2 Hready)) n Hnode) as Hedges.
  destruct (pre_finalize_computation_cases (pre_expression a)
    (succ_edges (prepare EN (live_graph (point_model (pre_ssa_points a)))) n))
    as [Hnone|[e [u [Hin Hcomputed]]]].
  - left; intro work; apply pre_finalize_fold_fixed; intros next edge Hedge.
    apply pre_finalize_occurrence_none, Hnone; exact Hedge.
  - right; exists e, u; split; [exact Hin|]; split; [exact Hcomputed|].
    apply pre_finalize_fold_single; [exact EE| |exact Hin|].
    + rewrite Hedges; exact (proj1 (proj2 Hready) n).
    + intros work next Hnext Hne; apply pre_finalize_occurrence_none.
      destruct (pre_recomputed (pre_expression a) next) as [expression|] eqn:Hnext_computed;
        [|reflexivity].
      exfalso; apply Hne; eapply pre_internal_source_unique.
      * exact (pre_expr_points EV a Ha).
      * rewrite Hedges in Hnext; apply in_flat_map; exists n; split; assumption.
      * rewrite Hedges in Hin; apply in_flat_map; exists n; split; assumption.
      * exact (proj1 (pre_expr_real_internal EV a Ha next expression Hnext_computed)).
      * exact (proj1 (pre_expr_real_internal EV a Ha e u Hcomputed)).
      * rewrite (pre_finalize_succ_sources EN EV a n Ha Hready Hreachable next Hnext),
          (pre_finalize_succ_sources EN EV a n Ha Hready Hreachable e Hin); reflexivity.
Qed.

Local Lemma pre_finalize_live_mono {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done later work :
  incl done later -> pre_finalize_live EB EE EU a f facts done work ->
  pre_finalize_live EB EE EU a f facts later work.
Proof.
  intros Hlater [Hscope Hreload Hphi Hsources]; constructor.
  - intros d version Hget; eapply pre_finalize_live_version_frame;
      [exact Hlater|reflexivity|eapply Hscope; exact Hget].
  - intros e version Hget; eapply pre_finalize_live_version_frame;
      [exact Hlater|reflexivity|eapply Hreload; exact Hget].
  - intros key version Hget Hregular; eapply pre_finalize_live_version_frame;
      [exact Hlater|reflexivity|eapply Hphi; eassumption].
  - intros e version Hget; apply Hlater; eapply Hsources; exact Hget.
Qed.

Local Lemma pre_finalize_live_reload_frame {S O B BE N E V K C U}
    (EB : encoding B) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done n p e selected version :
  ~ In n done -> Graph.source (live_graph (point_model (pre_ssa_points a))) e = n ->
  pre_finalize_live_version EB EE EU a f facts done p version ->
  pre_finalize_live_version EB EE EU a f facts (done ++ [n])
    (PrePlan (pre_insertions p) (pre_deletions p)
      (Map.set EE e selected (pre_reload_versions p)) (pre_phi_versions p)) version.
Proof.
  intros Hfresh Hsource [Hkept Hvisited]; destruct version as [u|q u|q u|q u].
  - split; [exact Hkept|exact I].
  - destruct Hkept as [Hedge [Hcomputed Hnone]]; split.
    + split; [exact Hedge|]; split; [exact Hcomputed|].
      cbn [pre_reload_versions]; rewrite Map.get_set_other; [exact Hnone|].
      intro Heq; subst q; apply Hfresh; rewrite <- Hsource; exact Hvisited.
    + apply in_or_app; left; exact Hvisited.
  - contradiction.
  - split; [exact Hkept|exact I].
Qed.

(** Processing a fresh instruction retains earlier definitions and marks its own result kept. *)
Lemma pre_finalize_occurrence_live {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts done tree work e n :
  frg_wf EB EBE EN EE EV EU a f -> ~ In n done ->
  Graph.source (live_graph (point_model (pre_ssa_points a))) e = n ->
  pre_finalize_live EB EE EU a f facts done work ->
  pre_finalize_live EB EE EU a f facts (done ++ [n])
    (pre_finalize_occurrence EB EN EE EU a f tree work e) /\
  forall version, pre_finalize_live_version EB EE EU a f facts done (snd work) version ->
    pre_finalize_live_version EB EE EU a f facts (done ++ [n])
      (snd (pre_finalize_occurrence EB EN EE EU a f tree work e)) version.
Proof.
  intros Hfrg Hfresh Hsource Hlive.
  assert (incl done (done ++ [n])) as Hincl.
  { intros point Hin; apply in_or_app; left; exact Hin. }
  assert (pre_finalize_live EB EE EU a f facts (done ++ [n]) work /\
    forall version, pre_finalize_live_version EB EE EU a f facts done (snd work) version ->
      pre_finalize_live_version EB EE EU a f facts (done ++ [n]) (snd work) version) as Hsame.
  { split; [apply (pre_finalize_live_mono EB EE EU a f facts done); assumption|].
    intros version Hversion; eapply pre_finalize_live_version_frame;
      [exact Hincl|reflexivity|exact Hversion]. }
  destruct work as [scope p]; unfold pre_finalize_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
    destruct (Map.get EE e (frg_occurrence_index f)) as [d|] eqn:Hclass; try exact Hsame.
  destruct (pre_total_pure (pre_expression a) u); [|exact Hsame].
  destruct (pre_finalize_available EB EN EE EU a tree scope d u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) as [selected|]
    eqn:Havailable.
  - assert (forall version, pre_finalize_live_version EB EE EU a f facts done p version ->
      pre_finalize_live_version EB EE EU a f facts (done ++ [n])
        (PrePlan (pre_insertions p) (pre_deletions p)
          (Map.set EE e selected (pre_reload_versions p)) (pre_phi_versions p)) version)
      as Hframe.
    { intros version Hversion; apply (pre_finalize_live_reload_frame EB EE EU a);
        assumption. }
    split; [|exact Hframe]; constructor; cbn [fst snd pre_reload_versions pre_phi_versions].
    + intros class version Hget; apply Hframe.
      exact (pre_finalize_live_scope EB EE EU a f facts done (scope,p) Hlive class version Hget).
    + intros edge version Hget; apply Hframe; apply pre_finalize_get_set in Hget.
      destruct Hget as [[-> ->]|Hget].
      * eapply (pre_finalize_live_scope EB EE EU a f facts done (scope,p) Hlive).
        eapply pre_finalize_available_lookup; exact Havailable.
      * exact (pre_finalize_live_reload EB EE EU a f facts done (scope,p) Hlive edge version Hget).
    + intros key version Hget Hregular; apply Hframe.
      exact (pre_finalize_live_phi EB EE EU a f facts done (scope,p) Hlive key version Hget
        Hregular).
    + intros edge version Hget; apply pre_finalize_get_set in Hget.
      destruct Hget as [[-> ->]|Hget].
      * rewrite Hsource; apply in_or_app; right; left; reflexivity.
      * apply Hincl.
        exact (pre_finalize_live_sources EB EE EU a f facts done (scope,p) Hlive edge version
          Hget).
  - assert (Map.get EE e (pre_reload_versions p) = None) as Hnone.
    { destruct (Map.get EE e (pre_reload_versions p)) as [version|] eqn:Hget;
        [|reflexivity].
      exfalso; apply Hfresh; rewrite <- Hsource.
      exact (pre_finalize_live_sources EB EE EU a f facts done (scope,p) Hlive e version Hget). }
    destruct Hsame as [Hlater Hframe]; split; [|exact Hframe].
    apply (pre_finalize_live_replace_scope EB EE EU a f facts (done ++ [n]) scope);
      [exact Hlater|].
    intros class version Hget; apply pre_finalize_get_set in Hget.
    destruct Hget as [[-> ->]|Hget].
    + split.
      * split.
        -- exact (proj1 (frg_occurrence_domain _ _ _ _ _ _ _ _ Hfrg e d Hclass)).
        -- split; assumption.
      * rewrite Hsource; apply in_or_app; right; left; reflexivity.
    + exact (pre_finalize_live_scope EB EE EU a f facts (done ++ [n]) (scope,p) Hlater class
        version Hget).
Qed.

Local Lemma pre_finalize_argument_reload_same {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) facts tree scope p arg :
  pre_reload_versions (pre_finalize_argument_step EB EN EE EU a facts tree scope p arg) =
    pre_reload_versions p.
Proof.
  unfold pre_finalize_argument_step.
  destruct (pre_finalize_will EB EU facts (pre_arg_block arg,pre_arg_expression arg));
    [|reflexivity].
  destruct (pre_phi_translate a (pre_arg_block_edge arg) (pre_arg_expression arg));
    [|reflexivity].
  destruct (pre_finalize_insert_operand EB EU facts (pre_arg_operand arg)).
  - destruct (pre_total_pure (pre_expression a) u &&
      negb (kill (pre_genkill (pre_expression a)) (pre_arg_point_edge arg) u)); reflexivity.
  - destruct (pre_finalize_available EB EN EE EU a tree scope (frg_operand_version
      (pre_arg_operand arg)) u (Graph.source (live_graph (point_model (pre_ssa_points a)))
        (pre_arg_point_edge arg))); reflexivity.
Qed.

Local Lemma pre_finalize_arguments_reload_same {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) facts tree scope p arguments :
  pre_reload_versions (fold_left (pre_finalize_argument_step EB EN EE EU a facts tree scope)
    arguments p) = pre_reload_versions p.
Proof.
  revert p; induction arguments as [|arg arguments IH]; intro p; [reflexivity|].
  cbn [fold_left]; rewrite IH; apply pre_finalize_argument_reload_same.
Qed.

(** A complete node preserves earlier selected definitions and adds only its retained result. *)
Lemma pre_finalize_node_live {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts done scope p n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n -> ~ In n done ->
  pre_finalize_live EB EE EU a f facts done (scope,p) ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  let phis := pre_finalize_phi_rows EB EN EU a f facts in
  let arguments := pre_finalize_argument_rows EBE EN a f in
  let output := pre_finalize_node EB EN EE EU a f facts tree points phis arguments (scope,p) n in
  pre_finalize_live EB EE EU a f facts (done ++ [n]) output /\
  forall version, pre_finalize_live_version EB EE EU a f facts done p version ->
    pre_finalize_live_version EB EE EU a f facts (done ++ [n]) (snd output) version.
Proof.
  intros Ha Hfrg Hready Hwf Hreachable Hfresh Hlive; cbn zeta.
  pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
  pose (tree := dominator_tree points).
  pose (phis := pre_finalize_phi_rows EB EN EU a f facts).
  pose (arguments := pre_finalize_argument_rows EBE EN a f).
  pose (frames := fold_left (pre_finalize_define_phi EB EE EU a) (index_edges EN phis n) scope).
  pose (selected := fold_left (pre_finalize_argument_step EB EN EE EU a facts tree frames)
    (index_edges EN arguments n) p).
  assert (pre_finalize_live EB EE EU a f facts done (frames,p)) as Hphis.
  { unfold frames; apply (pre_finalize_fold_invariant _ (fun next =>
      pre_finalize_live EB EE EU a f facts done (next,p))); [exact Hlive|].
    intros next [b u] Hin Hnext.
    apply (proj1 (pre_finalize_phi_rows_exact EB EN EU a f facts n b u Hwf)) in Hin.
    destruct Hin as [Hmember [Hwill Hpoint]].
    apply pre_finalize_define_phi_live; assumption. }
  assert (pre_finalize_live EB EE EU a f facts done (frames,selected)) as Harguments.
  { unfold selected; apply (pre_finalize_fold_invariant _ (fun next =>
      pre_finalize_live EB EE EU a f facts done (frames,next))); [exact Hphis|].
    intros next arg Hin Hnext; apply (pre_finalize_argument_live EB EN EE EU a); exact Hnext. }
  assert (forall version, pre_finalize_live_version EB EE EU a f facts done p version ->
    pre_finalize_live_version EB EE EU a f facts done selected version) as Hselected.
  { intros version Hversion; apply (pre_finalize_live_version_frame EB EE EU a f facts done
      done p selected version);
      [apply incl_refl|apply pre_finalize_arguments_reload_same|exact Hversion]. }
  change (pre_finalize_live EB EE EU a f facts (done ++ [n])
      (fold_left (pre_finalize_occurrence EB EN EE EU a f tree) (succ_edges points n)
        (frames,selected)) /\
    forall version, pre_finalize_live_version EB EE EU a f facts done p version ->
      pre_finalize_live_version EB EE EU a f facts (done ++ [n])
        (snd (fold_left (pre_finalize_occurrence EB EN EE EU a f tree) (succ_edges points n)
          (frames,selected))) version).
  destruct (pre_finalize_occurrences_single EB EN EE EV EU a f tree n Ha Hready Hreachable)
    as [Hnone|[e [u [Hin [Hcomputed Hsingle]]]]].
  - fold points in Hnone; rewrite Hnone; split.
    + apply (pre_finalize_live_mono EB EE EU a f facts done); [|exact Harguments].
      intros point Hpoint; apply in_or_app; left; exact Hpoint.
    + intros version Hversion; eapply pre_finalize_live_version_frame;
        [|reflexivity|apply Hselected; exact Hversion].
      intros point Hpoint; apply in_or_app; left; exact Hpoint.
  - fold points in Hsingle; rewrite Hsingle.
    destruct (pre_finalize_occurrence_live EB EBE EN EE EV EU a f facts done tree
      (frames,selected) e n Hfrg Hfresh
      (pre_finalize_succ_sources EN EV a n Ha Hready Hreachable e Hin) Harguments)
      as [Houtput Hframe].
    split; [exact Houtput|]; intros version Hversion; apply Hframe, Hselected; exact Hversion.
Qed.

(** Snapshot validity is coupled to the same current plan, including all retained computations. *)
Definition pre_finalize_live_table {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f facts done
    (work : Map.t N (pre_finalize_scope B E U) * pre_plan E U) : Prop :=
  pre_finalize_live EB EE EU a f facts done (Map.empty,snd work) /\
    forall point scope, Map.get EN point (fst work) = Some scope ->
      forall d version, Map.get (frg_version_encoding EB EE EU) d scope = Some version ->
        pre_finalize_live_version EB EE EU a f facts done (snd work) version.

Local Lemma pre_finalize_table_live {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts done work n :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n -> ~ In n done ->
  pre_finalize_live_table EB EN EE EU a f facts done work ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  pre_finalize_live_table EB EN EE EU a f facts (done ++ [n])
    (pre_finalize_table_step EB EN EE EU a f facts tree points
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (pre_finalize_initial EB EE EU a (frg_versions f)) work n).
Proof.
  intros Ha Hfrg Hready Hwf Hreachable Hfresh [Hplan Houtputs]; cbn zeta.
  destruct work as [outputs p]; unfold pre_finalize_table_step.
  pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
  pose (tree := dominator_tree points).
  pose (phis := pre_finalize_phi_rows EB EN EU a f facts).
  pose (arguments := pre_finalize_argument_rows EBE EN a f).
  pose (initial := pre_finalize_initial EB EE EU a (frg_versions f)).
  pose (input := match Map.get EN n (idom tree) with
    | None => initial
    | Some parent => match Map.get EN parent outputs with
      | None => initial
      | Some scope => scope
      end
    end).
  assert (pre_finalize_live EB EE EU a f facts done (input,p)) as Hinput.
  { apply (pre_finalize_live_replace_scope EB EE EU a f facts done Map.empty);
      [exact Hplan|].
    unfold input; destruct (Map.get EN n (idom tree)) as [parent|].
    - destruct (Map.get EN parent outputs) as [scope|] eqn:Hget.
      + exact (Houtputs parent scope Hget).
      + apply pre_finalize_initial_live.
    - apply pre_finalize_initial_live. }
  destruct (pre_finalize_node_live EB EBE EN EE EV EU a f facts done input p n
    Ha Hfrg Hready Hwf Hreachable Hfresh Hinput) as [Hnode Hframe].
  change (pre_finalize_live EB EE EU a f facts (done ++ [n])
    (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n)) in Hnode.
  change (forall version, pre_finalize_live_version EB EE EU a f facts done p version ->
    pre_finalize_live_version EB EE EU a f facts (done ++ [n])
      (snd (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n))
      version) in Hframe.
  change (pre_finalize_live_table EB EN EE EU a f facts (done ++ [n])
    (let '(scope,output) := pre_finalize_node EB EN EE EU a f facts tree points phis arguments
      (input,p) n in (Map.set EN n scope outputs,output))).
  destruct (pre_finalize_node EB EN EE EU a f facts tree points phis arguments (input,p) n)
    as [scope output] eqn:Hresult.
  cbn [snd] in Hframe.
  split.
  - apply (pre_finalize_live_replace_scope EB EE EU a f facts (done ++ [n]) scope);
      [exact Hnode|].
    intros d version Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros point frames Hget d version Hversion; cbn [fst snd] in Hget |- *.
    apply pre_finalize_get_set in Hget; destruct Hget as [[-> ->]|Hget].
    + exact (pre_finalize_live_scope EB EE EU a f facts (done ++ [n]) (scope,output) Hnode
        d version Hversion).
    + apply Hframe; exact (Houtputs point frames Hget d version Hversion).
Qed.

Local Lemma pre_finalize_prefix_fresh {N} (prefix suffix : list N) n :
  NoDup (prefix ++ n :: suffix) -> ~ In n prefix.
Proof.
  induction prefix as [|head prefix IH]; intro Hnodup; [intro Hfalse; contradiction|].
  inversion Hnodup as [|head' rest Hfresh Htail]; subst head' rest.
  intros [Heq|Hin].
  - subst head; apply Hfresh; apply in_or_app; right; left; reflexivity.
  - exact (IH Htail Hin).
Qed.

(** Every actual prefix preserves retained definitions in all snapshots and both selected maps. *)
Lemma pre_finalize_prefix_live {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    f facts prefix suffix :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) ->
  let points := prepare EN (live_graph (point_model (pre_ssa_points a))) in
  let tree := dominator_tree points in
  preorder (dom_search points (idom tree)) = prefix ++ suffix ->
  pre_finalize_live_table EB EN EE EU a f facts prefix
    (fold_left (pre_finalize_table_step EB EN EE EU a f facts tree points
      (pre_finalize_phi_rows EB EN EU a f facts) (pre_finalize_argument_rows EBE EN a f)
      (pre_finalize_initial EB EE EU a (frg_versions f))) prefix
      (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)).
Proof.
  intros Ha Hfrg Hready Hwf; cbn zeta; revert suffix.
  induction prefix using rev_ind; intros suffix Horder.
  - split.
    + change (pre_finalize_live EB EE EU a f facts []
        (Map.empty,PrePlan Map.empty Map.empty Map.empty Map.empty)).
      constructor.
      * intros d version Hget; change (Map.get (frg_version_encoding EB EE EU) d Map.empty =
          Some version) in Hget; rewrite Map.get_empty in Hget; discriminate.
      * intros e version Hget; change (Map.get EE e Map.empty = Some version) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
      * intros key version Hget; change (Map.get (pair_encoding (pair_encoding EE EE) EU)
          key Map.empty = Some version) in Hget; rewrite Map.get_empty in Hget; discriminate.
      * intros e version Hget; change (Map.get EE e Map.empty = Some version) in Hget.
        rewrite Map.get_empty in Hget; discriminate.
    + intros point scope Hget; change (Map.get EN point Map.empty = Some scope) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
  - assert (preorder (dom_search
      (prepare EN (live_graph (point_model (pre_ssa_points a))))
      (idom (dominator_tree (prepare EN (live_graph (point_model (pre_ssa_points a))))))) =
      prefix ++ x :: suffix) as Hsplit.
    { rewrite Horder, <- app_assoc; reflexivity. }
    rewrite fold_left_app; cbn [fold_left].
    apply (pre_finalize_table_live EB EBE EN EE EV EU a f facts prefix);
      try assumption.
    + apply (proj1 (proj2 (pre_finalize_order_exact EN _ x Hready))).
      rewrite Hsplit; apply in_or_app; right; left; reflexivity.
    + apply (pre_finalize_prefix_fresh prefix suffix x).
      rewrite <- Hsplit; exact (proj1 (pre_finalize_order_exact EN _ x Hready)).
    + apply (IHprefix (x :: suffix)); exact Hsplit.
Qed.

(** All regular versions selected by the actual placement denote retained or enabled definitions. *)
Theorem ssa_pre_selected_versions_kept {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  let f := build_frg EB EBE EN EE EV EU a in
  let facts := solve_ssapre EB EBE EN EE EV EU a f in
  let p := ssa_pre_place EB EBE EN EE EV EU a in
  (forall e version, Map.get EE e (pre_reload_versions p) = Some version ->
    pre_finalize_kept_version EB EE EU a f facts p version) /\
  (forall key version, Map.get (pair_encoding (pair_encoding EE EE) EU) key
    (pre_phi_versions p) = Some version -> pre_finalize_regular version ->
    pre_finalize_kept_version EB EE EU a f facts p version).
Proof.
  intros Ha Hb Hn; cbn zeta.
  pose (f := build_frg EB EBE EN EE EV EU a).
  pose (facts := solve_ssapre EB EBE EN EE EV EU a f).
  pose (points := prepare EN (live_graph (point_model (pre_ssa_points a)))).
  pose (tree := dominator_tree points).
  pose (order := preorder (dom_search points (idom tree))).
  assert (frg_wf EB EBE EN EE EV EU a f) as Hfrg by (apply build_frg_wf; assumption).
  pose proof (proj1 (proj2 (proj2 (build_frg_indexes_wf EB EBE EN EE EV EU a)))) as Hwf.
  destruct (pre_finalize_prefix_live EB EBE EN EE EV EU a f facts order [] Ha Hfrg Hn Hwf
    (eq_sym (app_nil_r order))) as [Hplan Houtputs].
  change (pre_finalize_live EB EE EU a f facts order
    (Map.empty,pre_finalize_build EB EBE EN EE EV EU a f facts)) in Hplan.
  split.
  - intros e version Hget.
    change (Map.get EE e (pre_reload_versions
      (pre_finalize_build EB EBE EN EE EV EU a f facts)) = Some version) in Hget.
    pose proof (proj1 (pre_finalize_live_reload EB EE EU a f facts order
      (Map.empty,pre_finalize_build EB EBE EN EE EV EU a f facts) Hplan e version Hget)) as Hkept.
    destruct version; exact Hkept.
  - intros key version Hget Hregular.
    change (Map.get (pair_encoding (pair_encoding EE EE) EU) key (pre_phi_versions
      (pre_finalize_build EB EBE EN EE EV EU a f facts)) = Some version) in Hget.
    pose proof (proj1 (pre_finalize_live_phi EB EE EU a f facts order
      (Map.empty,pre_finalize_build EB EBE EN EE EV EU a f facts) Hplan key version Hget
        Hregular)) as Hkept.
    destruct version; exact Hkept.
Qed.
