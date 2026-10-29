(** * Dense variable analyses

    Finite variable universes support liveness, reaching definitions, zeros and equalities.
    For example, an edge reading and defining x still requires x in its live input.
    Builds on: CollectionsFinSet, OrderPowerset, DomainsEquality, Views and FixpointTotal. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderPowerset OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointWorklist
  FixpointTotal FixpointSchedule.
From Gaulois.Domains Require Import DomainsEquality.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsForward ViewsAgreement
  ViewsSsaPoints.
Import List.ListNotations.

(** Membership ignores the finite carrier's erased support proof. *)
Definition fmem {K} (E : encoding K) {U : list K} (k : K) (a : finite_set E U) : bool :=
  FinSet.mem E k (proj1_sig a).

(** Mention tests compare injective codes. *)
Definition mentions {K} (E : encoding K) (k : K) (l : list K) : bool :=
  existsb (fun k' => Pos.eqb (encode E k) (encode E k')) l.

Local Lemma list_set_wf {K} (E : encoding K) (xs : list K) :
  FinSet.wf E (FinSet.of_list E xs).
Proof.
  apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Local Lemma mentions_spec {K} (E : encoding K) (x : K) (xs : list K) :
  mentions E x xs = true <-> In x xs.
Proof.
  unfold mentions; rewrite existsb_exists; split.
  - intros [y [Hy Hcode]]; apply Pos.eqb_eq in Hcode.
    apply (encode_injective E) in Hcode; now subst y.
  - intro Hx; exists x; split; [exact Hx|apply Pos.eqb_refl].
Qed.

Local Lemma mentions_false {K} (E : encoding K) (x : K) (xs : list K) :
  mentions E x xs = false <-> ~ In x xs.
Proof.
  rewrite <- (mentions_spec E x xs); destruct (mentions E x xs); intuition congruence.
Qed.

Local Lemma clamp_spec {K} (E : encoding K) (U : list K) s x :
  fmem E x (finite_clamp E U s) = true <-> In x U /\ FinSet.mem E x s = true.
Proof.
  change (FinSet.mem E x (FinSet.of_list E (filter (fun k => FinSet.mem E k s) U)) = true
    <-> In x U /\ FinSet.mem E x s = true).
  rewrite FinSet.of_list_spec, filter_In; reflexivity.
Qed.

(** A variable view records the inputs, outputs and exit observations of graph edges. *)
Record var_view (S O N E X Cv : Type) : Type := VarView {
  gview : graph_view S O N E;
  uses : E -> list X;
  defs : E -> list X;
  exit_uses : N -> list X;
  vget : S -> X -> Cv
}.

Arguments VarView {S O N E X Cv}.
Arguments gview {S O N E X Cv}.
Arguments uses {S O N E X Cv}.
Arguments defs {S O N E X Cv}.
Arguments exit_uses {S O N E X Cv}.
Arguments vget {S O N E X Cv}.

(** View laws connect input agreement and unwritten variables with actual steps and endings. *)
Record var_view_laws {S O N E X Cv} (m : semantics S O) (en : endings S)
    (vv : var_view S O N E X Cv) : Prop := {
  view_laws : graph_view_laws m (gview vv);
  no_stays : forall s l s', ~ stays (gview vv) s l s';
  defs_frame : forall s l s' e x, reachable_state m s -> step m s l s' ->
    taken (gview vv) s l s' e -> ~ In x (defs vv e) -> vget vv s' x = vget vv s x;
  uses_determine : forall s l s' t e, reachable_state m s -> reachable_state m t ->
    point (gview vv) t = point (gview vv) s -> step m s l s' -> taken (gview vv) s l s' e ->
    (forall x, In x (uses vv e) -> vget vv s x = vget vv t x) ->
    exists t', step m t l t' /\ taken (gview vv) t l t' e /\
      forall x, In x (defs vv e) -> vget vv s' x = vget vv t' x;
  exits_determine : forall s t, reachable_state m s -> reachable_state m t ->
    point (gview vv) t = point (gview vv) s ->
    (forall x, In x (exit_uses vv (point (gview vv) s)) -> vget vv s x = vget vv t x) ->
    (final en s <-> final en t) /\ (trapped en s <-> trapped en t) /\
    (stopped en s <-> stopped en t)
}.

Arguments view_laws {S O N E X Cv m en vv}.
Arguments no_stays {S O N E X Cv m en vv}.
Arguments defs_frame {S O N E X Cv m en vv}.
Arguments uses_determine {S O N E X Cv m en vv}.
Arguments exits_determine {S O N E X Cv m en vv}.

(** The variable universe deduplicates every use, definition and exit operand. *)
Definition var_universe {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    list X :=
  FinSet.elements (FinSet.of_list EX
    (flat_map (fun e => uses vv e ++ defs vv e) (edges_of (cfg (gview vv)))
     ++ flat_map (exit_uses vv) (Graph.nodes (cfg (gview vv))))).

(** Live facts carry finite support in the view's variable universe. *)
Definition live_set {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) : Type :=
  finite_set EX (var_universe EX vv).

(** Liveness orders needs by inclusion. *)
Definition live_lattice {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    lattice (live_set EX vv) := finite_powerset_lattice EX (var_universe EX vv).

(** States agree when their live variables have equal values. *)
Definition live_agreement {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    agreement (live_set EX vv) S :=
  {| agree := fun a s t => forall x, fmem EX x a = true -> vget vv s x = vget vv t x |}.

(** Uses are read before definitions overwrite their outputs. *)
Definition liveness_transfer {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv)
    (e : E) (a : live_set EX vv) : live_set EX vv :=
  finite_clamp EX (var_universe EX vv)
    (FinSet.union EX (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (defs vv e)))
       (FinSet.of_list EX (uses vv e))).

(** Every node contributes its exit uses to the backward equations. *)
Definition liveness_system {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    System.t N (dense_constraint N E) (live_set EX vv) :=
  backward_system (cfg (gview vv))
    (fun n => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX (exit_uses vv n)))
    (liveness_transfer EX vv).

(** Liveness reads only each flow edge's target. *)
Definition liveness_static {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  System.static (liveness_system EX vv) := backward_static _ _ _.

(** Live agreement is reflexive, antitone in needs and symmetric. *)
Theorem live_agreement_laws {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  agreement_laws (live_lattice EX vv) (live_agreement EX vv) /\
  agreement_symmetric (live_agreement EX vv).
Proof.
  split.
  - constructor.
    + intros a s x Hx; reflexivity.
    + intros a b s t Hab Hagree x Hx; apply Hagree.
      exact (set_member_subset EX _ _ Hab x Hx).
  - intros a s t Hagree x Hx; symmetry; apply Hagree; exact Hx.
Qed.

(** Every mentioned variable is covered, and the universe contains no duplicates. *)
Theorem var_universe_covers {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
  NoDup (var_universe EX vv) /\
  (forall e x, In e (edges_of (cfg (gview vv))) -> In x (uses vv e ++ defs vv e) ->
     In x (var_universe EX vv)) /\
  (forall n x, In n (Graph.nodes (cfg (gview vv))) -> In x (exit_uses vv n) ->
     In x (var_universe EX vv)).
Proof.
  unfold var_universe; split.
  - apply (FinSet.elements_nodup EX), list_set_wf.
  - split.
    + intros e x He Hx.
      apply (proj2 (FinSet.elements_spec EX x _ (list_set_wf EX _))).
      apply FinSet.of_list_spec, in_or_app; left; apply in_flat_map.
      exists e; split; assumption.
    + intros n x Hn Hx.
      apply (proj2 (FinSet.elements_spec EX x _ (list_set_wf EX _))).
      apply FinSet.of_list_spec, in_or_app; right; apply in_flat_map.
      exists n; split; assumption.
Qed.

(** The total joining solver returns a checked liveness post-solution. *)
Definition solve_liveness {S O N E X Cv} (EN : encoding N) (EE : encoding E) (EX : encoding X)
    (vv : var_view S O N E X Cv) :
    {s : N -> live_set EX vv | post_solution (live_lattice EX vv) (liveness_system EX vv) s} :=
  solve_total EN (dense_constraint_encoding EN EE) (live_lattice EX vv)
    (finite_powerset_laws EX _) (rpo_scheduler EN _ (liveness_static EX vv)) Joining
    (liveness_system EX vv) (liveness_static EX vv)
    (inhabits (base_height (finite_powerset_height EX _ (proj1 (var_universe_covers EX vv))))).

(** Reaching facts enumerate the variables each graph edge defines. *)
Definition reach_universe {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : list (X * E) :=
  FinSet.elements (FinSet.of_list (pair_encoding EX EE)
    (flat_map (fun e => map (fun x => (x, e)) (defs vv e)) (edges_of (cfg (gview vv))))).

(** Reaching-definition facts have finite pair support. *)
Definition reach_set {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : Type :=
  finite_set (pair_encoding EX EE) (reach_universe EX EE vv).

(** Reaching definitions use the may-set order. *)
Definition reach_lattice {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) : lattice (reach_set EX EE vv) :=
  finite_powerset_lattice (pair_encoding EX EE) (reach_universe EX EE vv).

(** The reference removes previous writers by testing the original definition list. *)
Local Definition reaching_transfer_reference {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) (e : E) (a : reach_set EX EE vv) : reach_set EX EE vv :=
  finite_clamp (pair_encoding EX EE) (reach_universe EX EE vv)
    (FinSet.of_list (pair_encoding EX EE)
       (filter (fun xd => negb (mentions EX (fst xd) (defs vv e)))
          (FinSet.elements (proj1_sig a)) ++ map (fun x => (x, e)) (defs vv e))).

(** Each fact pair uses the same kill set, prepared before the fact traversal. *)
Local Definition reaching_with_kill {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) (e : E) (killed : FinSet.t X)
    (a : reach_set EX EE vv) : reach_set EX EE vv :=
  finite_clamp (pair_encoding EX EE) (reach_universe EX EE vv)
    (FinSet.of_list (pair_encoding EX EE)
       (filter (fun xd => negb (FinSet.mem EX (fst xd) killed))
          (FinSet.elements (proj1_sig a)) ++ map (fun x => (x, e)) (defs vv e))).

(** Writing a variable replaces its previous defining edges with the current edge. *)
Definition reaching_transfer {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) (e : E) (a : reach_set EX EE vv) : reach_set EX EE vv :=
  let killed := FinSet.of_list EX (defs vv e) in
  reaching_with_kill EX EE vv e killed a.

Local Definition reaching_kill_index {E X} (EX : encoding X) (EE : encoding E)
    (writes : E -> list X) (es : list E) : Map.t E (FinSet.t X) :=
  fold_right (fun e ix =>
    match Map.get EE e ix with
    | Some _ => ix
    | None => Map.set EE e (FinSet.of_list EX (writes e)) ix
    end) Map.empty es.

(* Missing rows are observable through arbitrary Flow queries, even in malformed views. *)
Local Definition reaching_kill_lookup {E X} (EX : encoding X) (EE : encoding E)
    (writes : E -> list X) (ix : Map.t E (FinSet.t X)) (e : E) : FinSet.t X :=
  match Map.get EE e ix with
  | Some killed => killed
  | None => FinSet.of_list EX (writes e)
  end.

(** Entries have no defining edge; callbacks retain the graph's prepared kill index. *)
Definition reaching_system {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) :
    System.t N (dense_constraint N E) (reach_set EX EE vv) :=
  let ix := reaching_kill_index EX EE (defs vv) (edges_of (cfg (gview vv))) in
  forward_system (cfg (gview vv)) (fun _ => bot (reach_lattice EX EE vv))
    (fun e => reaching_with_kill EX EE vv e (reaching_kill_lookup EX EE (defs vv) ix e)).

(** The system reference uses the original transfer equation on every flow row. *)
Local Definition reaching_system_reference {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) :
    System.t N (dense_constraint N E) (reach_set EX EE vv) :=
  forward_system (cfg (gview vv)) (fun _ => bot (reach_lattice EX EE vv))
    (reaching_transfer_reference EX EE vv).

Local Lemma mentions_index_agrees {X} (EX : encoding X) x xs :
  FinSet.mem EX x (FinSet.of_list EX xs) = mentions EX x xs.
Proof.
  apply eq_true_iff_eq; rewrite FinSet.of_list_spec, mentions_spec; reflexivity.
Qed.

(** Indexed filtering preserves the entire finite fact, including its support proof. *)
Local Lemma reaching_transfer_agrees {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) e a :
  reaching_transfer EX EE vv e a = reaching_transfer_reference EX EE vv e a.
Proof.
  unfold reaching_transfer, reaching_with_kill, reaching_transfer_reference.
  assert (Hfilter : filter
    (fun xd => negb (FinSet.mem EX (fst xd) (FinSet.of_list EX (defs vv e))))
    (FinSet.elements (proj1_sig a)) = filter
    (fun xd => negb (mentions EX (fst xd) (defs vv e))) (FinSet.elements (proj1_sig a))).
  { apply filter_ext; intros [x d]; now rewrite mentions_index_agrees. }
  now rewrite Hfilter.
Qed.

(** Preparation stores exactly the kill set of each listed edge, even with duplicates. *)
Local Lemma reaching_kill_index_get {E X} (EX : encoding X) (EE : encoding E)
    (writes : E -> list X) es e :
  Map.get EE e (reaching_kill_index EX EE writes es) =
    if mentions EE e es then Some (FinSet.of_list EX (writes e)) else None.
Proof.
  revert e; induction es as [|d es IH]; intro e; [apply Map.get_empty|].
  cbn [reaching_kill_index fold_right mentions existsb].
  fold (reaching_kill_index EX EE writes es).
  destruct (Pos.eqb (encode EE e) (encode EE d)) eqn:Hsame.
  - apply Pos.eqb_eq, (encode_injective EE) in Hsame; subst d.
    destruct (Map.get EE e (reaching_kill_index EX EE writes es)) eqn:Hget.
    + rewrite (IH e) in Hget.
      destruct (mentions EE e es) eqn:Hlisted; [|discriminate].
      rewrite (IH e), Hlisted; reflexivity.
    + apply Map.get_set_same.
  - destruct (Map.get EE d (reaching_kill_index EX EE writes es)) eqn:Hget.
    + apply IH.
    + rewrite Map.get_set_other; [apply IH|].
      intro Heq; subst d; rewrite Pos.eqb_refl in Hsame; discriminate.
Qed.

(** Indexed and fallback lookup both recover the exact source kill set. *)
Local Lemma reaching_kill_lookup_agrees {E X} (EX : encoding X) (EE : encoding E)
    (writes : E -> list X) es e :
  reaching_kill_lookup EX EE writes (reaching_kill_index EX EE writes es) e =
    FinSet.of_list EX (writes e).
Proof.
  unfold reaching_kill_lookup; rewrite reaching_kill_index_get.
  destruct (mentions EE e es); reflexivity.
Qed.

(** All rows and assignments preserve targets, results and the two ordered query traces. *)
Local Lemma reaching_system_agrees {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) :
  System.constraints (reaching_system EX EE vv) =
    System.constraints (reaching_system_reference EX EE vv) /\
  (forall c, System.target (reaching_system EX EE vv) c =
    System.target (reaching_system_reference EX EE vv) c) /\
  forall c sigma, Query.run (System.rhs (reaching_system EX EE vv) c) sigma =
    Query.run (System.rhs (reaching_system_reference EX EE vv) c) sigma.
Proof.
  split; [reflexivity|]; split; [intro c; reflexivity|].
  intros [n|e] sigma; [reflexivity|].
  cbn [reaching_system reaching_system_reference forward_system System.rhs Query.run].
  rewrite reaching_kill_lookup_agrees.
  change ((reaching_transfer EX EE vv e (sigma (Graph.source (cfg (gview vv)) e)),
    [Graph.source (cfg (gview vv)) e], ([] : list (N * reach_set EX EE vv))) =
    (reaching_transfer_reference EX EE vv e (sigma (Graph.source (cfg (gview vv)) e)),
    [Graph.source (cfg (gview vv)) e], [])).
  now rewrite reaching_transfer_agrees.
Qed.

Local Lemma reaching_post_solution_iff {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) sigma :
  post_solution (reach_lattice EX EE vv) (reaching_system EX EE vv) sigma <->
  post_solution (reach_lattice EX EE vv)
    (forward_system (cfg (gview vv)) (fun _ => bot (reach_lattice EX EE vv))
      (reaching_transfer EX EE vv)) sigma.
Proof.
  unfold reaching_system; rewrite !forward_post_solution_iff.
  assert (Htransfer : forall e a,
    reaching_with_kill EX EE vv e (reaching_kill_lookup EX EE (defs vv)
      (reaching_kill_index EX EE (defs vv) (edges_of (cfg (gview vv)))) e) a =
    reaching_transfer EX EE vv e a).
  { intros e a; unfold reaching_transfer; now rewrite reaching_kill_lookup_agrees. }
  split; intros [Hseed Hflow]; split; [exact Hseed| |exact Hseed|].
  - intros e He; specialize (Hflow e He); now rewrite Htransfer in Hflow.
  - intros e He; rewrite Htransfer; exact (Hflow e He).
Qed.

(** Untouched variables are must-facts ordered by reverse inclusion. *)
Definition zero_lattice {S O N E X Cv} (EX : encoding X) (vv : var_view S O N E X Cv) :
    lattice (live_set EX vv) := finite_must_lattice EX (var_universe EX vv).

(** The zero analysis seeds locals and forgets every variable written on an edge. *)
Definition zero_since_entry_system {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (locals : list X) :
    System.t N (dense_constraint N E) (live_set EX vv) :=
  forward_system (cfg (gview vv))
    (fun _ => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX locals))
    (fun e a => finite_clamp EX (var_universe EX vv)
                  (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (defs vv e)))).

(** Copies describe equalities established in the edge's resulting state. *)
Record copy_view (S O N E X Cv : Type) : Type := CopyView {
  cvars : var_view S O N E X Cv;
  copies : E -> list (X * X)
}.

Arguments CopyView {S O N E X Cv}.
Arguments cvars {S O N E X Cv}.
Arguments copies {S O N E X Cv}.

(** Equality transfer forgets all written variables before adding resulting copies. *)
Definition equality_transfer {S O N E X Cv} (EX : encoding X) (cv : copy_view S O N E X Cv)
    (e : E) (p : partition EX) : partition EX :=
  fold_left (fun q xy => partition_union EX (fst xy) (snd xy) q) (copies cv e)
    (fold_left (fun q x => partition_forget EX x q) (defs (cvars cv) e) p).

(** Entry partitions are discrete, so no equality of distinct variables is assumed. *)
Definition equality_system {S O N E X Cv} (EX : encoding X) (cv : copy_view S O N E X Cv) :
    System.t N (dense_constraint N E) (partition EX) :=
  forward_system (cfg (gview (cvars cv))) (fun _ => top_value (partition_top EX))
    (equality_transfer EX cv).

(** The syntactic point model uses the same read-before-write convention as the transfer. *)
Definition var_point_uses {S O N E X Cv} (vv : var_view S O N E X Cv) : point_uses N E X :=
  PointUses (cfg (gview vv)) (uses vv) (defs vv) (exit_uses vv).

(** * Liveness and observable agreement *)

Local Lemma live_transfer_spec {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) e a x :
  In e (edges_of (cfg (gview vv))) ->
  (fmem EX x (liveness_transfer EX vv e a) = true <->
    (fmem EX x a = true /\ ~ In x (defs vv e)) \/ In x (uses vv e)).
Proof.
  intro He; unfold liveness_transfer; rewrite clamp_spec, FinSet.mem_union,
    FinSet.mem_diff, !FinSet.of_list_spec.
  assert (Hnot : FinSet.mem EX x (FinSet.of_list EX (defs vv e)) = false <->
    ~ In x (defs vv e)).
  { rewrite <- (FinSet.of_list_spec EX x (defs vv e)).
    destruct (FinSet.mem EX x (FinSet.of_list EX (defs vv e))); intuition congruence. }
  rewrite Hnot; split; [tauto|].
  intro Hx; split; [|exact Hx]; destruct Hx as [[Hx Hdef]|Huse].
  - exact (proj2 (proj2_sig a) x Hx).
  - apply (proj1 (proj2 (var_universe_covers EX vv)) e x He), in_or_app; now left.
Qed.

Local Lemma live_exit_spec {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) n x : In n (Graph.nodes (cfg (gview vv))) ->
  (fmem EX x (finite_clamp EX (var_universe EX vv)
    (FinSet.of_list EX (exit_uses vv n))) = true <-> In x (exit_uses vv n)).
Proof.
  intro Hn; rewrite clamp_spec, FinSet.of_list_spec.
  split; [tauto|]; intro Hx; split; [|exact Hx].
  exact (proj2 (proj2 (var_universe_covers EX vv)) n x Hn Hx).
Qed.

Local Lemma live_step_agrees {S O N E X Cv} (m : semantics S O) (en : endings S)
    (EX : encoding X) (vv : var_view S O N E X Cv) sigma :
  var_view_laws m en vv ->
  step_agrees m (gview vv) (live_agreement EX vv) (reachable_state m)
    (liveness_transfer EX vv) sigma.
Proof.
  intro Hvv; split.
  - intros e s l s' t Hs Ht Hpoint Hstep Htaken Hagree.
    destruct (view_taken_edge m (gview vv) s l s' e (view_laws Hvv) Hs Hstep Htaken)
      as [He [Hsource Htarget]].
    destruct (uses_determine Hvv s l s' t e Hs Ht Hpoint Hstep Htaken)
      as [t' [Htstep [Httaken Hdefs]]].
    + intros x Hx; apply Hagree, live_transfer_spec; [exact He|now right].
    + exists t'; split; [exact Htstep|]; split; [exact Httaken|].
      intros x Hx; destruct (FinSet.mem EX x (FinSet.of_list EX (defs vv e))) eqn:Hdef.
      * apply Hdefs; now apply FinSet.of_list_spec in Hdef.
      * assert (Hnot : ~ In x (defs vv e)).
        { intro Hin; pose proof (proj2 (FinSet.of_list_spec EX x _) Hin); congruence. }
        rewrite (defs_frame Hvv s l s' e x Hs Hstep Htaken Hnot).
        rewrite (defs_frame Hvv t l t' e x Ht Htstep Httaken Hnot).
        apply Hagree, live_transfer_spec; [exact He|left; split; assumption].
  - intros s l s' t Hs Ht Hpoint Hstep Hstay Hagree.
    exfalso; exact (no_stays Hvv s l s' Hstay).
Qed.

(** Initial states agreeing on a liveness post-solution have identical observable behaviour. *)
Theorem liveness_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (vv : var_view S O N E X Cv) (sigma : N -> live_set EX vv) (s0 t0 : S) :
  var_view_laws m en vv ->
  post_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  initial m s0 -> initial m t0 -> point (gview vv) t0 = point (gview vv) s0 ->
  (forall x, fmem EX x (sigma (point (gview vv) s0)) = true -> vget vv s0 x = vget vv t0 x) ->
  same_behaviour m en s0 m en t0.
Proof.
  intros Hvv Hpost Hs0 Ht0 Hpoint Hagree.
  eapply (agreement_same_behaviour m en (gview vv) (live_lattice EX vv)
    (fun _ => live_agreement EX vv) (reachable_state m)
    (fun n => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX (exit_uses vv n)))
    (liveness_transfer EX vv) sigma s0 t0).
  - exact (view_laws Hvv).
  - exact (proj1 (live_agreement_laws EX vv)).
  - exact (proj2 (live_agreement_laws EX vv)).
  - constructor.
    + intros s Hs; exists s, []; split; [exact Hs|constructor].
    + intros s l s' Hs Hstep; eapply reachable_state_step; eassumption.
    + intros s Hs; exact Hs.
  - exact (live_step_agrees m en EX vv sigma Hvv).
  - intros s t Hs Ht Hpt Hlive; apply (exits_determine Hvv s t Hs Ht Hpt).
    intros x Hx; apply Hlive, live_exit_spec.
    + eapply view_point_in_nodes; [exact (view_laws Hvv)|exact Hs].
    + exact Hx.
  - exact Hpost.
  - exact Hs0.
  - exact Ht0.
  - exact Hpoint.
  - exact Hagree.
Qed.

(** * Forward history and invariant analyses *)

Local Lemma reach_universe_covers {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) e x :
  In e (edges_of (cfg (gview vv))) -> In x (defs vv e) ->
  In (x, e) (reach_universe EX EE vv).
Proof.
  intros He Hx; unfold reach_universe.
  apply (proj2 (FinSet.elements_spec (pair_encoding EX EE) _ _
    (list_set_wf _ _))), FinSet.of_list_spec, in_flat_map.
  exists e; split; [exact He|apply in_map_iff; exists x; split; [reflexivity|exact Hx]].
Qed.

Local Lemma reaching_transfer_spec {S O N E X Cv} (EX : encoding X) (EE : encoding E)
    (vv : var_view S O N E X Cv) e a x d :
  In e (edges_of (cfg (gview vv))) ->
  (fmem (pair_encoding EX EE) (x, d) (reaching_transfer EX EE vv e a) = true <->
    (fmem (pair_encoding EX EE) (x, d) a = true /\ mentions EX x (defs vv e) = false) \/
    (d = e /\ In x (defs vv e))).
Proof.
  intro He; rewrite reaching_transfer_agrees; unfold reaching_transfer_reference.
  rewrite clamp_spec, FinSet.of_list_spec, in_app_iff,
    filter_In, (FinSet.elements_spec _ _ _ (proj1 (proj2_sig a))), Bool.negb_true_iff.
  cbn [fst]; assert (Hgen : In (x, d) (map (fun y => (y, e)) (defs vv e)) <->
    d = e /\ In x (defs vv e)).
  { rewrite in_map_iff; split.
    - intros [y [Heq Hy]]; inversion Heq; now subst.
    - intros [-> Hx]; exists x; auto. }
  rewrite Hgen; split; [tauto|]; intro Hx; split; [|exact Hx].
  destruct Hx as [[Hx Hkill]|[-> Hdef]].
  - exact (proj2 (proj2_sig a) (x, d) Hx).
  - apply reach_universe_covers; assumption.
Qed.

(** A history's last writer is present in every reaching-definition post-solution. *)
Theorem reaching_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (EE : encoding E) (vv : var_view S O N E X Cv) (sigma : N -> reach_set EX EE vv) :
  var_view_laws m en vv ->
  post_solution (reach_lattice EX EE vv) (reaching_system EX EE vv) sigma ->
  forall s0 es s x d, initial m s0 -> run_edges m (gview vv) s0 es s ->
    last_writer (fun e y => mentions EX y (defs vv e)) es x = Some d ->
    fmem (pair_encoding EX EE) (x, d) (sigma (point (gview vv) s)) = true.
Proof.
  intros Hvv Hpost.
  pose proof (proj1 (reaching_post_solution_iff EX EE vv sigma) Hpost) as Hforward.
  pose (G := {| gamma := fun (a : reach_set EX EE vv) (se : S * list E) => forall x d,
      last_writer (fun e y => mentions EX y (defs vv e)) (snd se) x = Some d ->
      fmem (pair_encoding EX EE) (x, d) a = true |}).
  assert (HG : concretisation_laws (reach_lattice EX EE vv) G).
  { constructor; intros a b se Hab Ha x d Hwriter.
    exact (set_member_subset _ _ _ Hab (x, d) (Ha x d Hwriter)). }
  assert (Hsound := forward_history_sound m (gview vv) (reach_lattice EX EE vv)
    (fun _ => G) (fun _ => bot (reach_lattice EX EE vv))
    (reaching_transfer EX EE vv) sigma (view_laws Hvv) HG).
  assert (Hfacts : forall s0 es s, initial m s0 -> run_edges m (gview vv) s0 es s ->
    gamma G (sigma (point (gview vv) s)) (s, es)).
  { apply Hsound; clear Hsound.
  - intros s Hs x d Hwriter; discriminate.
  - intros e s0 es s l s' Hs0 Hhistory Hstep Htaken Hfact x d Hwriter.
    change (last_writer (fun e y => mentions EX y (defs vv e)) (es ++ [e]) x = Some d)
      in Hwriter.
    rewrite last_writer_snoc in Hwriter.
    assert (Hs : reachable_state m s) by (eapply history_reachable; eassumption).
    destruct (view_taken_edge m (gview vv) s l s' e (view_laws Hvv) Hs Hstep Htaken)
      as [He Hends].
    apply reaching_transfer_spec; [exact He|].
    destruct (mentions EX x (defs vv e)) eqn:Hwrite.
    + inversion Hwriter; subst d; right; split; [reflexivity|].
      now apply mentions_spec in Hwrite.
    + left; split; [exact (Hfact x d Hwriter)|reflexivity].
  - intros s0 es s l s' Hs0 Hhistory Hstep Hstay Hfact.
    exfalso; exact (no_stays Hvv s l s' Hstay).
  - exact Hforward. }
  intros s0 es s x d Hs0 Hrun Hwriter; exact (Hfacts s0 es s Hs0 Hrun x d Hwriter).
Qed.

(** Every untouched local in the post-solution still holds its initial zero. *)
Theorem zero_since_entry_sound {S O N E X Cv} (m : semantics S O) (en : endings S)
    (EX : encoding X) (vv : var_view S O N E X Cv) (locals : list X) (zero : Cv)
    (sigma : N -> live_set EX vv) :
  var_view_laws m en vv -> (forall s x, initial m s -> In x locals -> vget vv s x = zero) ->
  post_solution (zero_lattice EX vv) (zero_since_entry_system EX vv locals) sigma ->
  forall s x, reachable_state m s -> fmem EX x (sigma (point (gview vv) s)) = true ->
    vget vv s x = zero.
Proof.
  intros Hvv Hinitial Hpost.
  pose (G := finite_must_gamma EX (var_universe EX vv) (fun x s => vget vv s x = zero)).
  assert (Hsound := forward_invariant_sound m (gview vv) (zero_lattice EX vv)
    (fun _ => G) (fun _ => finite_clamp EX (var_universe EX vv) (FinSet.of_list EX locals))
    (fun e a => finite_clamp EX (var_universe EX vv)
      (FinSet.diff EX (proj1_sig a) (FinSet.of_list EX (defs vv e)))) sigma
    (view_laws Hvv) (finite_must_gamma_laws EX _ _) ).
  assert (Hfacts : forall s, reachable_state m s -> gamma G (sigma (point (gview vv) s)) s).
  { apply Hsound; clear Hsound.
    - intros s Hs x Hx; apply clamp_spec in Hx; destruct Hx as [_ Hx].
      apply Hinitial; [exact Hs|now apply FinSet.of_list_spec in Hx].
    - intros e s l s' Hs Hstep Htaken Hfact x Hx.
      apply clamp_spec in Hx; destruct Hx as [_ Hx]; apply FinSet.mem_diff in Hx.
      destruct Hx as [Hx Hnot].
      assert (Hundef : ~ In x (defs vv e)).
      { intro Hin; pose proof (proj2 (FinSet.of_list_spec EX x _) Hin); congruence. }
      rewrite (defs_frame Hvv s l s' e x Hs Hstep Htaken Hundef); now apply Hfact.
    - intros s l s' Hs Hstep Hstay Hfact; exfalso; exact (no_stays Hvv s l s' Hstay).
    - exact Hpost. }
  intros s x Hs Hx; exact (Hfacts s Hs x Hx).
Qed.

Local Lemma forgets_reached {X} (EX : encoding X) xs (p : partition EX) :
  p <> Unreached -> fold_left (fun q x => partition_forget EX x q) xs p <> Unreached.
Proof.
  revert p; induction xs as [|x xs IH]; intros p Hp; cbn; [exact Hp|].
  apply IH; destruct p; [discriminate|contradiction].
Qed.

Local Lemma forgets_spec {X} (EX : encoding X) xs (p : partition EX) a b :
  p <> Unreached ->
  partition_equiv EX (fold_left (fun q x => partition_forget EX x q) xs p) a b ->
  a = b \/ (partition_equiv EX p a b /\ ~ In a xs /\ ~ In b xs).
Proof.
  revert p; induction xs as [|x xs IH]; intros p Hp Hab; cbn in *.
  - right; tauto.
  - assert (Hp' : partition_forget EX x p <> Unreached).
    { destruct p; [discriminate|contradiction]. }
    destruct (IH _ Hp' Hab) as [Heq|[Hab' [Ha Hb]]]; [now left|].
    apply partition_forget_spec in Hab'; [|exact Hp].
    destruct Hab' as [[Hab' [Hax Hbx]]|[Hax Hbx]].
    + right; split; [exact Hab'|]; cbn; intuition congruence.
    + left; congruence.
Qed.

Local Lemma copies_gamma {X Cv} (EX : encoding X) xys (p : partition EX) (look : X -> Cv) :
  gamma (partition_gamma EX) p look ->
  (forall x y, In (x, y) xys -> look x = look y) ->
  gamma (partition_gamma EX)
    (fold_left (fun q xy => partition_union EX (fst xy) (snd xy) q) xys p) look.
Proof.
  revert p; induction xys as [|[x y] xys IH]; intros p Hp Hcopies; cbn; [exact Hp|].
  apply IH.
  - destruct p as [u|]; [|contradiction].
    intros a b Hab; change (partition_equiv EX (partition_union EX x y (Reached u)) a b)
      in Hab; apply partition_union_spec in Hab.
    destruct Hab as [Hab|[[Hax Hyb]|[Hay Hxb]]].
    + exact (Hp a b Hab).
    + transitivity (look x); [exact (Hp a x Hax)|].
      transitivity (look y); [apply Hcopies; now left|exact (Hp y b Hyb)].
    + transitivity (look y); [exact (Hp a y Hay)|].
      transitivity (look x); [symmetry; apply Hcopies; now left|exact (Hp x b Hxb)].
  - intros a b Hab; apply Hcopies; now right.
Qed.

Local Lemma equality_transfer_gamma {S O N E X Cv} (m : semantics S O) (en : endings S)
    (EX : encoding X) (cv : copy_view S O N E X Cv) e p s l s' :
  var_view_laws m en (cvars cv) -> reachable_state m s -> step m s l s' ->
  taken (gview (cvars cv)) s l s' e ->
  (forall x y, In (x, y) (copies cv e) -> vget (cvars cv) s' x = vget (cvars cv) s' y) ->
  gamma (partition_gamma EX) p (vget (cvars cv) s) ->
  gamma (partition_gamma EX) (equality_transfer EX cv e p) (vget (cvars cv) s').
Proof.
  intros Hvv Hs Hstep Htaken Hcopies Hp; unfold equality_transfer; apply copies_gamma;
    [|exact Hcopies].
  assert (Hreached : p <> Unreached) by (destruct p; [discriminate|contradiction]).
  pose proof (forgets_reached EX (defs (cvars cv) e) p Hreached) as Hresult.
  remember (fold_left (fun q x => partition_forget EX x q) (defs (cvars cv) e) p) as q
    eqn:Hq; destruct q as [u|]; [|contradiction].
  intros a b Hab; change (partition_equiv EX (Reached u) a b) in Hab.
  rewrite Hq in Hab; apply forgets_spec in Hab; [|exact Hreached].
  destruct Hab as [->|[Hab [Ha Hb]]]; [reflexivity|].
  rewrite (defs_frame Hvv s l s' e a Hs Hstep Htaken Ha),
    (defs_frame Hvv s l s' e b Hs Hstep Htaken Hb).
  destruct p; [exact (Hp a b Hab)|contradiction].
Qed.

(** Variables in the same post-solution partition hold equal values at reachable states. *)
Theorem equality_sound {S O N E X Cv} (m : semantics S O) (en : endings S) (EX : encoding X)
    (cv : copy_view S O N E X Cv) (sigma : N -> partition EX) :
  var_view_laws m en (cvars cv) ->
  (forall s l s' e x y, reachable_state m s -> step m s l s' ->
     taken (gview (cvars cv)) s l s' e -> In (x, y) (copies cv e) ->
     vget (cvars cv) s' x = vget (cvars cv) s' y) ->
  post_solution (partition_lattice EX) (equality_system EX cv) sigma ->
  forall s x y, reachable_state m s ->
    partition_equiv EX (sigma (point (gview (cvars cv)) s)) x y ->
    vget (cvars cv) s x = vget (cvars cv) s y.
Proof.
  intros Hvv Hcopies Hpost.
  pose (G := {| gamma := fun (p : partition EX) s =>
    gamma (partition_gamma EX) p (vget (cvars cv) s) |}).
  assert (HG : concretisation_laws (partition_lattice EX) G).
  { constructor; intros p q s Hpq Hp; exact (gamma_monotone (partition_gamma_laws EX)
      p q (vget (cvars cv) s) Hpq Hp). }
  assert (Hfacts : forall s, reachable_state m s ->
    gamma G (sigma (point (gview (cvars cv)) s)) s).
  { eapply (forward_invariant_sound m (gview (cvars cv)) (partition_lattice EX)
      (fun _ => G) (fun _ => top_value (partition_top EX))
      (equality_transfer EX cv) sigma).
    - exact (view_laws Hvv).
    - exact HG.
    - intros s Hs; exact (gamma_top_full (partition_top_full EX) (vget (cvars cv) s)).
    - intros e s l s' Hs Hstep Htaken Hp; eapply equality_transfer_gamma;
        [exact Hvv|exact Hs|exact Hstep|exact Htaken| |exact Hp].
      intros x y Hxy; eapply Hcopies; eassumption.
    - intros s l s' Hs Hstep Hstay Hp; exfalso; exact (no_stays Hvv s l s' Hstay).
    - exact Hpost. }
  intros s x y Hs Hxy; specialize (Hfacts s Hs).
  destruct (sigma (point (gview (cvars cv)) s)); [exact (Hfacts x y Hxy)|contradiction].
Qed.

(** * Exact finite-path liveness *)

(* These counting lemmas reason about finite predicates; they are erased proof arguments,
   rather than an iteration algorithm or a fuel bound supplied to an executable solver. *)
Local Lemma filter_count_bound {A} (xs : list A) (p : A -> bool) :
  length (filter p xs) <= length xs.
Proof.
  induction xs as [|x xs IH]; cbn; [lia|]; destruct (p x); cbn; lia.
Qed.

Local Lemma filter_count_mono {A} (xs : list A) (p q : A -> bool) :
  (forall x, In x xs -> p x = true -> q x = true) ->
  length (filter p xs) <= length (filter q xs).
Proof.
  induction xs as [|x xs IH]; intro Hpq; cbn; [lia|].
  assert (Htail : length (filter p xs) <= length (filter q xs)).
  { apply IH; intros y Hy; apply Hpq; now right. }
  specialize (Hpq x (or_introl eq_refl)); destruct (p x), (q x); cbn in *;
    try discriminate; lia.
Qed.

Local Lemma filter_count_same {A} (xs : list A) (p q : A -> bool) :
  (forall x, In x xs -> p x = true -> q x = true) ->
  length (filter p xs) = length (filter q xs) -> forall x, In x xs -> p x = q x.
Proof.
  induction xs as [|a xs IH]; intros Hpq Hcount x Hx; [contradiction|].
  assert (Htail : forall y, In y xs -> p y = true -> q y = true).
  { intros y Hy; apply Hpq; now right. }
  pose proof (filter_count_mono xs p q Htail) as Hle.
  specialize (Hpq a (or_introl eq_refl)); cbn in Hcount.
  destruct (p a) eqn:Hp, (q a) eqn:Hq; cbn in Hcount; try discriminate;
    try (exfalso; lia).
  - destruct Hx as [<-|Hx]; [now rewrite Hp, Hq|apply IH; [exact Htail|lia|exact Hx]].
  - destruct Hx as [<-|Hx]; [now rewrite Hp, Hq|apply IH; [exact Htail|lia|exact Hx]].
Qed.

Local Lemma finite_predicate_closure {A} (xs : list A) (F : (A -> bool) -> A -> bool)
    (P : (A -> bool) -> Prop) :
  (forall b x, b x = true -> F b x = true) ->
  (forall b, P b -> P (F b)) -> P (fun _ => false) ->
  exists b, P b /\ forall x, In x xs -> F b x = b x.
Proof.
  intros Hgrow Hpreserve Hempty.
  assert (Hsearch : forall k b, length xs - length (filter b xs) <= k -> P b ->
    exists c, P c /\ forall x, In x xs -> F c x = c x).
  { induction k as [|k IH]; intros b Hcapacity Hb.
    - pose proof (filter_count_bound xs (F b)) as Hbound.
      pose proof (filter_count_mono xs b (F b) (fun x _ => Hgrow b x)) as Hle.
      assert (Heq : length (filter b xs) = length (filter (F b) xs)) by lia.
      exists b; split; [exact Hb|]; intros x Hx; symmetry.
      exact (filter_count_same xs b (F b) (fun x _ => Hgrow b x) Heq x Hx).
    - pose proof (filter_count_bound xs (F b)) as Hbound.
      pose proof (filter_count_mono xs b (F b) (fun x _ => Hgrow b x)) as Hle.
      destruct (Nat.eq_dec (length (filter b xs)) (length (filter (F b) xs))) as [Heq|Hne].
      + exists b; split; [exact Hb|]; intros x Hx; symmetry.
        exact (filter_count_same xs b (F b) (fun x _ => Hgrow b x) Heq x Hx).
      + apply (IH (F b)); [lia|now apply Hpreserve]. }
  apply (Hsearch (length xs) (fun _ => false)); [lia|exact Hempty].
Qed.

Local Definition live_close {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (x : X) (b : N -> bool) (n : N) : bool :=
  b n || mentions EX x (exit_uses vv n) ||
    existsb (fun e => mentions EX x (uses vv e) ||
      (negb (mentions EX x (defs vv e)) && b (Graph.target (cfg (gview vv)) e)))
      (Graph.out (cfg (gview vv)) n).

Local Lemma live_close_spec {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) x b n :
  live_close EX vv x b n = true <->
    b n = true \/ In x (exit_uses vv n) \/
    exists e, In e (Graph.out (cfg (gview vv)) n) /\
      (In x (uses vv e) \/ (~ In x (defs vv e) /\ b (Graph.target (cfg (gview vv)) e) = true)).
Proof.
  unfold live_close; rewrite !orb_true_iff, mentions_spec, existsb_exists.
  split.
  - intros [[Hb|Hexit]|[e [He Hedge]]]; [now left|right; now left|].
    right; right; exists e; split; [exact He|].
    rewrite orb_true_iff, andb_true_iff, negb_true_iff, mentions_spec, mentions_false in Hedge.
    exact Hedge.
  - intros [Hb|[Hexit|[e [He Hedge]]]]; [left; now left|left; now right|].
    right; exists e; split; [exact He|].
    rewrite orb_true_iff, andb_true_iff, negb_true_iff, mentions_spec, mentions_false.
    exact Hedge.
Qed.

Local Lemma syntactic_live_closure {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) x :
  exists b, (forall n, b n = true -> syntactic_live (var_point_uses vv) x n) /\
    forall n, In n (Graph.nodes (cfg (gview vv))) -> live_close EX vv x b n = b n.
Proof.
  apply (finite_predicate_closure (Graph.nodes (cfg (gview vv))) (live_close EX vv x)
    (fun b => forall n, b n = true -> syntactic_live (var_point_uses vv) x n)).
  - intros b n Hb; apply live_close_spec; now left.
  - intros b Hb n Hn; apply live_close_spec in Hn.
    destruct Hn as [Hn|[Hexit|[e [He [Huse|[Hdef Hnext]]]]]].
    + now apply Hb.
    + apply live_exit; exact Hexit.
    + eapply live_edge_use; eassumption.
    + eapply live_edge_next; [exact He|exact Hdef|now apply Hb].
  - intros n Hfalse; discriminate.
Qed.

Local Definition live_candidate {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (x : X) (b : N -> bool) (n : N) : live_set EX vv :=
  finite_clamp EX (var_universe EX vv)
    (FinSet.of_list EX (filter (fun y => negb (Pos.eqb (encode EX y) (encode EX x)) || b n)
      (var_universe EX vv))).

Local Lemma live_candidate_spec {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) x b n y :
  fmem EX y (live_candidate EX vv x b n) = true <->
    In y (var_universe EX vv) /\
      (Pos.eqb (encode EX y) (encode EX x) = false \/ b n = true).
Proof.
  unfold live_candidate; rewrite clamp_spec, FinSet.of_list_spec, filter_In, orb_true_iff,
    negb_true_iff; tauto.
Qed.

Local Lemma live_candidate_post {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) x b :
  graph_wf (cfg (gview vv)) ->
  (forall n, In n (Graph.nodes (cfg (gview vv))) -> live_close EX vv x b n = b n) ->
  post_solution (live_lattice EX vv) (liveness_system EX vv) (live_candidate EX vv x b).
Proof.
  intros Hwf Hclosed; apply backward_post_solution_iff; split.
  - intros n Hn; apply FinSet.subset_spec; [apply list_set_wf|].
    intros y Hy; apply (live_exit_spec EX vv n y Hn) in Hy; apply live_candidate_spec.
    split; [exact (proj2 (proj2 (var_universe_covers EX vv)) n y Hn Hy)|].
    destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy; [|now left].
    apply Pos.eqb_eq, (encode_injective EX) in Hxy; subst y; right.
    rewrite <- Hclosed by exact Hn; apply live_close_spec; right; now left.
  - intros e He; apply FinSet.subset_spec; [apply list_set_wf|].
    intros y Hy; apply (live_transfer_spec EX vv e _ y He) in Hy.
    assert (Hsource : In (Graph.source (cfg (gview vv)) e) (Graph.nodes (cfg (gview vv)))).
    { apply in_flat_map in He; destruct He as [n [Hn Hout]].
      now rewrite (out_source Hwf n e Hout). }
    apply live_candidate_spec; split.
    + destruct Hy as [[Hy Hdef]|Huse].
      * exact (proj2 (proj2_sig (live_candidate EX vv x b _)) y Hy).
      * apply (proj1 (proj2 (var_universe_covers EX vv)) e y He), in_or_app; now left.
    + destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Hxy; [|now left].
      apply Pos.eqb_eq, (encode_injective EX) in Hxy; subst y; right.
      rewrite <- Hclosed by exact Hsource; apply live_close_spec; right; right.
      exists e; split; [apply edges_of_source; assumption|].
      destruct Hy as [[Hy Hdef]|Huse]; [right|now left].
      apply live_candidate_spec in Hy; destruct Hy as [_ [Hbad|Hnext]].
      * rewrite Pos.eqb_refl in Hbad; discriminate.
      * split; assumption.
Qed.

Local Lemma syntactic_live_in_post {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) sigma :
  graph_wf (cfg (gview vv)) -> post_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    syntactic_live (var_point_uses vv) x n -> fmem EX x (sigma n) = true.
Proof.
  intros Hwf Hpost n x Hn Hlive.
  destruct (proj1 (backward_post_solution_iff _ _ _ _ _) Hpost) as [Hseed Hflow].
  revert Hn; induction Hlive as [n Hexit|n e Hout Huse|n e Hout Hdef Hlive IH]; intro Hn.
  - apply (set_member_subset EX _ _ (Hseed n Hn)), live_exit_spec; assumption.
  - assert (He : In e (edges_of (cfg (gview vv)))) by (eapply edges_of_in; eassumption).
    rewrite <- (out_source Hwf n e Hout).
    apply (set_member_subset EX _ _ (Hflow e He)), live_transfer_spec; [exact He|now right].
  - assert (He : In e (edges_of (cfg (gview vv)))) by (eapply edges_of_in; eassumption).
    rewrite <- (out_source Hwf n e Hout).
    apply (set_member_subset EX _ _ (Hflow e He)), live_transfer_spec; [exact He|left].
    split; [apply IH; eapply out_target_in; eassumption|exact Hdef].
Qed.

(** The least dense solution equals finite-path liveness, even at unreachable nodes. *)
Theorem syntactic_live_least {S O N E X Cv} (EX : encoding X)
    (vv : var_view S O N E X Cv) (sigma : N -> live_set EX vv) :
  graph_wf (cfg (gview vv)) ->
  least_solution (live_lattice EX vv) (liveness_system EX vv) sigma ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    (fmem EX x (sigma n) = true <-> syntactic_live (var_point_uses vv) x n).
Proof.
  intros Hwf [Hpost Hleast] n x Hn; split.
  - intro Hx; destruct (syntactic_live_closure EX vv x) as [b [Hsound Hclosed]].
    pose proof (Hleast _ (live_candidate_post EX vv x b Hwf Hclosed) n) as Hbelow.
    pose proof (set_member_subset EX _ _ Hbelow x Hx) as Hcandidate.
    apply live_candidate_spec in Hcandidate; destruct Hcandidate as [_ [Hbad|Hb]].
    + rewrite Pos.eqb_refl in Hbad; discriminate.
    + exact (Hsound n Hb).
  - intro Hlive; exact (syntactic_live_in_post EX vv sigma Hwf Hpost n x Hn Hlive).
Qed.
