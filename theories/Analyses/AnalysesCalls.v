(** * Call resolvers and contextual summaries

    Call facts resolve targets, index callers and propagate summaries through actual frames.
    For example, an unresolved indirect call conservatively names every listed function.
    Builds on: ViewsCalls, ViewsSummary, GraphDag and OrderConcrete. *)

From Stdlib Require Import List Bool PArith Lia ZArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderConcrete.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc GraphDag.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsEffects ViewsCalls ViewsSummary.
Import List.ListNotations.

(** Direct targets take precedence; unavailable indirect facts use the closed inventory. *)
Definition resolver {P F V A} (direct : P -> option F) (callee_val : P -> option V)
    (fact : V -> A) (fns : A -> option (list F)) (all : list F) (p : P) : list F :=
  match direct p with
  | Some f => [f]
  | None =>
    match callee_val p with
    | Some v =>
      match fns (fact v) with
      | Some fs => fs
      | None => all
      end
    | None => all
    end
  end.

(** Recursion is witnessed by a nonempty return path from a function to itself. *)
Definition recursive {F P} (g : Graph.t F (call_edge F P)) (f : F) : Prop :=
  exists e es, In e (Graph.out g f) /\ path g (Graph.target g e) es f.

(** Purity summaries record whether a function or one of its callees may be impure. *)
Definition purity_spec {S F P} (_ : calls_view S F P) (impure_local : F -> bool) :
    summary_spec F P bool :=
  SummarySpec bool_lattice impure_local (fun _ _ a => a).

(** A false impurity summary guarantees silence and an unchanged heap. *)
Definition purity_cover {S O I H} (ev : effects_view S I H) : step_cover S O bool :=
  StepCover (fun b s l s' => b = false -> l = nil /\ heap ev s' = heap ev s).

(** Each activation has a client-selected nonnegative frame weight. *)
Record frame_weights (F : Type) : Type := FrameWeights {
  weight : F -> nat
}.

Arguments FrameWeights {F}.
Arguments weight {F}.

(** A leaf has no syntactic call site. *)
Definition callee_leaf {S F P} (cv : calls_view S F P) (f : F) : bool :=
  match sites_of cv f with
  | [] => true
  | _ => false
  end.

(** The latest call site is retained first, up to the selected context bound. *)
Definition push_ctx {P} (k : nat) (p : P) (c : list P) : list P := firstn k (p :: c).

(** Enumerate contexts of every length up to the bound, using only listed sites. *)
Fixpoint calls_contexts {P} (sites : list P) (k : nat) : list (list P) :=
  match k with
  | 0 => [[]]
  | Datatypes.S n => [] :: flat_map (fun p => map (cons p) (calls_contexts sites n)) sites
  end.

(** A row retains the caller's context and reads its callee in the pushed context. *)
Definition callstring_system {S F P A} (k : nat) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) :
    System.t (F * list P) (summary_constraint F P * list P) A :=
  {| System.constraints := flat_map (fun c => map (fun row => (row, c))
       (System.constraints (summary_system cv resolve sp)))
       (calls_contexts (flat_map (sites_of cv) (functions cv)) k);
     System.target := fun row =>
       match fst row with
       | SLocal f => (f, snd row)
       | SCall p _ => (caller_of cv p, snd row)
       end;
     System.rhs := fun row =>
       match fst row with
       | SLocal f => Query.Ret (local sp f)
       | SCall p g => Query.Ask (g, push_ctx k p (snd row))
           (fun a => Query.Ret (via_call sp p g a))
       end |}.

(** A frame's context lists the latest suspended sites below that activation. *)
Definition ctx_of {S F P} (cv : calls_view S F P) (k : nat) (s : S) (i : nat) : list P :=
  firstn k (map snd (skipn i (frames cv s))).

(** The contextual rows have exactly one dependency per call row. *)
Definition callstring_static {S F P A} (k : nat) (cv : calls_view S F P)
    (resolve : P -> list F) (sp : summary_spec F P A) :
    System.static (callstring_system k cv resolve sp).
Proof.
  refine {| System.deps := fun row =>
    match fst row with
    | SLocal _ => []
    | SCall p g => [(g, push_ctx k p (snd row))]
    end;
    System.side_targets := fun _ => [] |}.
  - intros [[f|p g] c] sigma; apply incl_refl.
  - intros [[f|p g] c] sigma; apply incl_refl.
Defined.

(** * Finite call-graph paths *)

(** Index each listed source once, merging parallel sites into distinct target functions. *)
Definition calls_target_index {F E} (EF : encoding F) (g : Graph.t F E) :
    Map.t F (list (F * F)) :=
  fold_right (fun f ix => Map.set EF f
    (map (pair f) (FinSet.elements (FinSet.of_list EF (map (Graph.target g) (Graph.out g f)))))
    ix) Map.empty (Graph.nodes g).

(** The finite graph shares raw nodes, uses the query as entry, and reads only its index. *)
Definition calls_finite_graph {F E} (EF : encoding F) (g : Graph.t F E) (f : F) :
    Graph.t F (F * F) :=
  {| Graph.nodes := Graph.nodes g;
     Graph.entries := [f];
     Graph.out := index_edges EF (calls_target_index EF g);
     Graph.source := fst;
     Graph.target := snd |}.

Lemma calls_index_lookup {F E} (EF : encoding F) (g : Graph.t F E) vs v :
  index_edges EF (fold_right (fun f ix => Map.set EF f
    (map (pair f) (FinSet.elements (FinSet.of_list EF (map (Graph.target g) (Graph.out g f)))))
    ix) Map.empty vs) v =
  if existsb (fun u => Pos.eqb (encode EF u) (encode EF v)) vs
  then map (pair v)
    (FinSet.elements (FinSet.of_list EF (map (Graph.target g) (Graph.out g v)))) else [].
Proof.
  induction vs as [|u vs IH]; cbn.
  - unfold index_edges; rewrite Map.get_empty; reflexivity.
  - destruct (Pos.eqb (encode EF u) (encode EF v)) eqn:Heq.
    + apply Pos.eqb_eq, (encode_injective EF) in Heq; subst u.
      unfold index_edges; rewrite Map.get_set_same; reflexivity.
    + unfold index_edges at 1; rewrite Map.get_set_other; [exact IH|].
      intro Hequal; subst u; rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Lemma calls_finite_out {F E} (EF : encoding F) (g : Graph.t F E) f v :
  Graph.out (calls_finite_graph EF g f) v =
  if existsb (fun u => Pos.eqb (encode EF u) (encode EF v)) (Graph.nodes g)
  then map (pair v)
    (FinSet.elements (FinSet.of_list EF (map (Graph.target g) (Graph.out g v)))) else [].
Proof.
  apply calls_index_lookup.
Qed.

Lemma calls_listed_test {F} (EF : encoding F) vs v :
  existsb (fun u => Pos.eqb (encode EF u) (encode EF v)) vs = true <-> In v vs.
Proof.
  rewrite existsb_exists; split.
  - intros [u [Hu Heq]]; apply Pos.eqb_eq, (encode_injective EF) in Heq; subst u; exact Hu.
  - intro Hv; exists v; split; [exact Hv|apply Pos.eqb_refl].
Qed.

Lemma calls_finite_edge {F E} (EF : encoding F) (g : Graph.t F E) f u v :
  In (u, v) (Graph.out (calls_finite_graph EF g f) u) <->
  In u (Graph.nodes g) /\ exists e, In e (Graph.out g u) /\ Graph.target g e = v.
Proof.
  rewrite calls_finite_out.
  destruct (existsb _ _) eqn:Hlisted.
  - apply calls_listed_test in Hlisted.
    rewrite in_map_iff; split.
    + intros [x [Heq Hx]]; inversion Heq; subst x; split; [exact Hlisted|].
      apply (FinSet.elements_spec EF) in Hx;
        [|unfold FinSet.of_list; apply FinSet.wf_fold_add, Map.wf_empty].
      apply FinSet.of_list_spec in Hx; apply in_map_iff in Hx.
      destruct Hx as [e [Htarget He]]; exists e; auto.
    + intros [_ [e [He Heq]]]; exists v; split; [reflexivity|].
      apply (FinSet.elements_spec EF);
        [unfold FinSet.of_list; apply FinSet.wf_fold_add, Map.wf_empty|].
      apply FinSet.of_list_spec; apply in_map_iff; exists e; auto.
  - split; [contradiction|].
    intros [Hu _]; pose proof (proj2 (calls_listed_test EF (Graph.nodes g) u) Hu); congruence.
Qed.

Lemma calls_finite_source {F E} (EF : encoding F) (g : Graph.t F E) f v e :
  In e (Graph.out (calls_finite_graph EF g f) v) -> fst e = v.
Proof.
  rewrite calls_finite_out; destruct (existsb _ _); [|contradiction].
  rewrite in_map_iff; intros [u [<- _]]; reflexivity.
Qed.

Lemma calls_finite_ready {F E} (EF : encoding F) (g : Graph.t F E) f :
  graph_wf g -> In f (Graph.nodes g) ->
  ready EF (calls_finite_graph EF g f) (prepare EF (calls_finite_graph EF g f)).
Proof.
  intros Hwf Hf; apply prepare_ready.
  - constructor.
    + exact (nodes_nodup Hwf).
    + intros v [<-|[]]; exact Hf.
    + apply calls_finite_source.
    + intros u [v w] Hu He; cbn.
      pose proof (calls_finite_source EF g f u (v, w) He) as Heq; cbn in Heq; subst v.
      apply calls_finite_edge in He; destruct He as [_ [e [He <-]]].
      eapply out_target_in; eassumption.
  - intro v; rewrite calls_finite_out; destruct (existsb _ _); [|constructor].
    assert (Hnd : NoDup
      (FinSet.elements (FinSet.of_list EF (map (Graph.target g) (Graph.out g v))))).
    { apply (FinSet.elements_nodup EF).
      unfold FinSet.of_list; apply FinSet.wf_fold_add, Map.wf_empty. }
    induction Hnd as [|x xs Hnot Hnd IH]; cbn; [constructor|].
    constructor; [|exact IH].
    rewrite in_map_iff; intros [y [Heq Hin]]; inversion Heq; subst y; contradiction.
Qed.

(** Frame-path weight counts only targets; the starting frame is added by demand. *)
Definition calls_path_weight {F E} (g : Graph.t F E) (fw : frame_weights F) (es : list E) : nat :=
  fold_right (fun e n => weight fw (Graph.target g e) + n) 0 es.

Lemma calls_path_nodes {F E} (g : Graph.t F E) u es v :
  graph_wf g -> In u (Graph.nodes g) -> path g u es v -> In v (Graph.nodes g).
Proof.
  intros Hwf Hu Hpath; induction Hpath as [v|e es v He Hpath IH].
  - exact Hu.
  - apply IH; eapply out_target_in; eassumption.
Qed.

Lemma calls_path_forward {F E} (EF : encoding F) (g : Graph.t F E) root fw u es v :
  graph_wf g -> In u (Graph.nodes g) -> path g u es v ->
  exists fs, path (calls_finite_graph EF g root) u fs v /\ length fs = length es /\
    calls_path_weight (calls_finite_graph EF g root) fw fs = calls_path_weight g fw es.
Proof.
  intros Hwf Hu Hpath; induction Hpath as [v|e es v He Hpath IH].
  - exists []; split; [constructor|split; reflexivity].
  - destruct (IH (out_target_in Hwf _ _ Hu He)) as [fs [Hfs [Hlength Hweight]]].
    exists ((Graph.source g e, Graph.target g e) :: fs); split.
    + apply (path_cons (g := calls_finite_graph EF g root)
        (Graph.source g e, Graph.target g e) fs v); [|exact Hfs].
      apply calls_finite_edge; split; [exact Hu|exists e; auto].
    + split; [cbn; congruence|].
      change (weight fw (Graph.target g e) +
        calls_path_weight (calls_finite_graph EF g root) fw fs =
        weight fw (Graph.target g e) + calls_path_weight g fw es).
      rewrite Hweight; reflexivity.
Qed.

Lemma calls_path_backward {F E} (EF : encoding F) (g : Graph.t F E) root fw u fs v :
  graph_wf g -> path (calls_finite_graph EF g root) u fs v ->
  exists es, path g u es v /\ length es = length fs /\
    calls_path_weight g fw es = calls_path_weight (calls_finite_graph EF g root) fw fs.
Proof.
  intros Hwf Hpath; induction Hpath as [v|[u w] fs v He Hpath IH].
  - exists []; split; [constructor|split; reflexivity].
  - cbn in *; apply (calls_finite_edge EF g root u w) in He.
    destruct He as [_ [e [He Htarget]]], IH as [es [Hes [Hlength Hweight]]].
    exists (e :: es); split.
    + rewrite <- Htarget in Hes; rewrite <- (out_source Hwf u e He).
      apply (path_cons e es v).
      * rewrite (out_source Hwf u e He); exact He.
      * exact Hes.
    + split; [cbn; congruence|].
      change (weight fw (Graph.target g e) + calls_path_weight g fw es =
        weight fw w + calls_path_weight (calls_finite_graph EF g root) fw fs).
      rewrite Htarget, Hweight; reflexivity.
Qed.

(** A reachable cycle has an explicit prefix and a nonempty closed suffix. *)
Definition calls_reachable_cycle {F E} (g : Graph.t F E) f : Prop :=
  exists v prefix e suffix, path g f prefix v /\ path g v (e :: suffix) v.

Lemma calls_cycles_agree {F E} (EF : encoding F) (g : Graph.t F E) root :
  graph_wf g -> In root (Graph.nodes g) ->
  (calls_reachable_cycle g root <->
    calls_reachable_cycle (calls_finite_graph EF g root) root).
Proof.
  intros Hwf Hroot; split.
  - intros [v [prefix [e [suffix [Hprefix Hcycle]]]]].
    destruct (calls_path_forward EF g root (FrameWeights (fun _ => 0)) _ _ _
      Hwf Hroot Hprefix) as [ps [Hps _]].
    pose proof (calls_path_nodes g _ _ _ Hwf Hroot Hprefix) as Hv.
    destruct (calls_path_forward EF g root (FrameWeights (fun _ => 0)) _ _ _
      Hwf Hv Hcycle) as [fs [Hfs [Hlength _]]].
    destruct fs as [|q qs]; [discriminate|].
    exists v, ps, q, qs; auto.
  - intros [v [prefix [e [suffix [Hprefix Hcycle]]]]].
    destruct (calls_path_backward EF g root (FrameWeights (fun _ => 0)) _ _ _
      Hwf Hprefix) as [ps [Hps _]].
    destruct (calls_path_backward EF g root (FrameWeights (fun _ => 0)) _ _ _
      Hwf Hcycle) as [fs [Hfs [Hlength _]]].
    destruct fs as [|q qs]; [discriminate|].
    exists v, ps, q, qs; auto.
Qed.

Lemma calls_single_entry_reachable {F E} (g : Graph.t F E) f v :
  Graph.entries g = [f] -> (reachable g v <-> exists es, path g f es v).
Proof.
  intro Hentry; rewrite reachable_iff_path; rewrite Hentry; split.
  - intros [s [es [[<-|[]] Hpath]]]; exists es; exact Hpath.
  - intros [es Hpath]; exists f, es; split; [left; reflexivity|exact Hpath].
Qed.

Lemma calls_max_paths_acyclic {F E} (EF : encoding F) (g : Graph.t F E)
    (p : prepared EF g) w r :
  ready EF g p -> max_paths p w = Some r ->
  forall v es, reachable g v -> es <> [] -> ~ path g v es v.
Proof.
  intros Hready Hsome v es Hreach Hne Hpath; pose proof Hready as [Hwf _].
  assert (Hok : dag_search_ok p (dfs p FinSet.empty (Graph.entries g)) = true).
  { unfold max_paths in Hsome; destruct (dag_search_ok p _) eqn:Htest;
      [reflexivity|discriminate]. }
  assert (Hmembers : forall x,
    In x (rpo (dfs p FinSet.empty (Graph.entries g))) <-> reachable g x).
  { intro x; rewrite (dag_rpo_members EF g p _ x Hready (entries_in Hwf)).
    apply reachable_dfs; exact Hready. }
  pose proof (dfs_rpo_nodup EF g p _ Hready (entries_in Hwf)) as Hnd.
  assert (Hedges : forall e,
    In (Graph.source g e) (rpo (dfs p FinSet.empty (Graph.entries g))) ->
    In e (Graph.out g (Graph.source g e)) ->
    before (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.source g e) (Graph.target g e)).
  { intros e Hin He; apply Hmembers in Hin.
    apply (proj2 (reachable_dfs EF g p _ Hready)) in Hin.
    destruct (rpo_edge_classes EF g p _ Hready (entries_in Hwf) e Hin He)
      as [Hbefore|Hback]; [exact Hbefore|].
    exfalso; exact (proj1 (dag_search_ok_correct EF g p _ Hready (entries_in Hwf))
      Hok e Hin He Hback). }
  destruct (dag_order_path g _ Hnd Hedges v es v Hpath
    (proj2 (Hmembers v) Hreach)) as [Hnil|Hbefore].
  - contradiction.
  - exact (dfs_before_irrefl _ _ Hnd Hbefore).
Qed.

Lemma calls_max_paths_cycle {F E} (EF : encoding F) (g : Graph.t F E)
    (p : prepared EF g) w f :
  ready EF g p -> Graph.entries g = [f] ->
  (max_paths p w = None <-> calls_reachable_cycle g f).
Proof.
  intros Hready Hentry; split.
  - intro Hnone.
    destruct (max_paths_cycle EF g p w Hready Hnone) as [v [es [Hv [Hne Hpath]]]].
    apply (calls_single_entry_reachable g f v Hentry) in Hv.
    destruct Hv as [prefix Hprefix], es as [|e suffix]; [contradiction|].
    exists v, prefix, e, suffix; auto.
  - intros [v [prefix [e [suffix [Hprefix Hcycle]]]]].
    destruct (max_paths p w) as [r|] eqn:Hmax; [|reflexivity].
    exfalso; apply (calls_max_paths_acyclic EF g p w r Hready Hmax v (e :: suffix)).
    + apply (calls_single_entry_reachable g f v Hentry); exists prefix; exact Hprefix.
    + discriminate.
    + exact Hcycle.
Qed.

Lemma calls_path_weight_Z {F E} (g : Graph.t F E) fw es :
  Z.of_nat (calls_path_weight g fw es) =
    path_weight (fun e => Z.of_nat (weight fw (Graph.target g e))) es.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  change (Z.of_nat (weight fw (Graph.target g e) + calls_path_weight g fw es) =
    (Z.of_nat (weight fw (Graph.target g e)) +
      path_weight (fun e => Z.of_nat (weight fw (Graph.target g e))) es)%Z).
  rewrite Nat2Z.inj_add, IH; reflexivity.
Qed.

(** Read a best distance as a natural, using the empty path's zero for absent entries. *)
Definition calls_best_nat {F E} (EF : encoding F) (r : dag_paths F E) (v : F) : nat :=
  match Map.get EF v (best r) with
  | Some b => Z.to_nat b
  | None => 0
  end.

(** Demand reroots the indexed graph and adds the starting activation to its maximum distance. *)
Definition stack_demand {S F P} (EF : encoding F) (_ : calls_view S F P)
    (g : Graph.t F (call_edge F P)) (fw : frame_weights F) (f : F) : option nat :=
  let indexed := calls_finite_graph EF g f in
  match max_paths (prepare EF indexed) (fun e => Z.of_nat (weight fw (snd e))) with
  | None => None
  | Some r => Some (weight fw f + fold_right Nat.max 0 (map (calls_best_nat EF r) (Graph.nodes g)))
  end.

Lemma calls_best_spec {F E} (EF : encoding F) (g : Graph.t F E) fw f r :
  graph_wf g -> In f (Graph.nodes g) ->
  max_paths (prepare EF (calls_finite_graph EF g f))
    (fun e => Z.of_nat (weight fw (snd e))) = Some r ->
  forall v,
    (forall es, path g f es v -> calls_path_weight g fw es <= calls_best_nat EF r v) /\
    (exists es w, path g f es w /\ calls_path_weight g fw es = calls_best_nat EF r v).
Proof.
  intros Hwf Hf Hmax v.
  pose proof (calls_finite_ready EF g f Hwf Hf) as Hready.
  pose proof (calls_max_paths_acyclic EF _ _ _ r Hready Hmax) as Hacyclic.
  destruct (max_paths_exact EF _ _ (fun e => Z.of_nat (weight fw (snd e)))
    Hready Hacyclic) as [r' [Hr Hspec]].
  rewrite Hmax in Hr; inversion Hr; subst r'.
  destruct (Hspec v) as [Hdomain Hbest].
  unfold calls_best_nat; destruct (Map.get EF v (best r)) as [b|] eqn:Hb.
  - destruct (Hbest b eq_refl) as [[start [fs [_ [Hentry [Hpath Hweight]]]]] Hbound].
    destruct Hentry as [Heq|[]]; cbn in Heq; subst start.
    destruct (calls_path_backward EF g f fw f fs v Hwf Hpath)
      as [es [Hes [_ Hsame]]].
    assert (Hnat : Z.of_nat (calls_path_weight g fw es) = b).
    { rewrite Hsame, calls_path_weight_Z; exact Hweight. }
    assert (Hto : Z.to_nat b = calls_path_weight g fw es).
    { rewrite <- Hnat, Nat2Z.id; reflexivity. }
    rewrite Hto; split.
    + intros ps Hps.
      destruct (calls_path_forward EF g f fw f ps v Hwf Hf Hps)
        as [qs [Hqs [_ Hsameqs]]].
      specialize (Hbound f qs (or_introl eq_refl) Hqs).
      change (path_weight (fun e => Z.of_nat
        (weight fw (Graph.target (calls_finite_graph EF g f) e))) qs <= b)%Z in Hbound.
      rewrite <- (calls_path_weight_Z (calls_finite_graph EF g f) fw qs),
        Hsameqs, <- Hnat in Hbound; lia.
    + exists es, v; auto.
  - split.
    + intros es Hes.
      destruct (calls_path_forward EF g f fw f es v Hwf Hf Hes) as [fs [Hfs _]].
      assert (Hv : reachable (calls_finite_graph EF g f) v).
      { apply (calls_single_entry_reachable (calls_finite_graph EF g f) f v eq_refl).
        exists fs; exact Hfs. }
      apply Hdomain in Hv; destruct Hv as [b Hbad]; congruence.
    + exists [], f; split; [constructor|reflexivity].
Qed.

Lemma calls_maximum_upper xs n : In n xs -> n <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|x xs IH]; [contradiction|].
  intros [<-|Hin]; cbn.
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma calls_maximum_attained (Q : nat -> Prop) xs :
  Q 0 -> (forall n, In n xs -> Q n) -> Q (fold_right Nat.max 0 xs).
Proof.
  intros Hzero; induction xs as [|x xs IH]; intro Hall; [exact Hzero|].
  cbn; destruct (Nat.le_ge_cases x (fold_right Nat.max 0 xs)) as [Hle|Hge].
  - rewrite Nat.max_r by exact Hle; apply IH; intros n Hn; apply Hall; right; exact Hn.
  - rewrite Nat.max_l by exact Hge; apply Hall; left; reflexivity.
Qed.

(** Exact demand detects reachable nonempty raw cycles and attains every finite maximum. *)
Theorem stack_demand_exact {S F P} (EF : encoding F) (cv : calls_view S F P)
    (g : Graph.t F (call_edge F P)) (fw : frame_weights F) (f : F) :
  graph_wf g -> In f (Graph.nodes g) ->
  (stack_demand EF cv g fw f = None <->
    exists v prefix e suffix, path g f prefix v /\ path g v (e :: suffix) v) /\
  (forall d, stack_demand EF cv g fw f = Some d ->
    (forall es v, path g f es v ->
      weight fw f + fold_right (fun e n => weight fw (Graph.target g e) + n) 0 es <= d) /\
    (exists es v, path g f es v /\
      weight fw f + fold_right (fun e n => weight fw (Graph.target g e) + n) 0 es = d)).
Proof.
  intros Hwf Hf; pose proof (calls_finite_ready EF g f Hwf Hf) as Hready.
  split.
  - change (stack_demand EF cv g fw f = None <-> calls_reachable_cycle g f).
    rewrite (calls_cycles_agree EF g f Hwf Hf).
    rewrite <- (calls_max_paths_cycle EF _ _
      (fun e => Z.of_nat (weight fw (snd e))) f Hready eq_refl).
    unfold stack_demand; destruct (max_paths _ _); split; congruence.
  - intros d Hd; unfold stack_demand in Hd.
    destruct (max_paths _ _) as [r|] eqn:Hmax; [|discriminate].
    inversion Hd; subst d; split.
    + intros es v Hpath.
      pose proof (proj1 (calls_best_spec EF g fw f r Hwf Hf Hmax v) es Hpath) as Hle.
      assert (Hv : In v (Graph.nodes g)) by (eapply calls_path_nodes; eassumption).
      pose proof (calls_maximum_upper (map (calls_best_nat EF r) (Graph.nodes g))
        (calls_best_nat EF r v) (in_map (calls_best_nat EF r) _ _ Hv)) as Hmaxle.
      unfold calls_path_weight in Hle; lia.
    + assert (Hwitness : exists es v, path g f es v /\ calls_path_weight g fw es =
        fold_right Nat.max 0 (map (calls_best_nat EF r) (Graph.nodes g))).
      { apply (calls_maximum_attained
          (fun n => exists es v, path g f es v /\ calls_path_weight g fw es = n)).
        - exists [], f; split; [constructor|reflexivity].
        - intros n Hin; apply in_map_iff in Hin; destruct Hin as [v [<- _]].
          exact (proj2 (calls_best_spec EF g fw f r Hwf Hf Hmax v)). }
      destruct Hwitness as [es [v [Hpath Hweight]]]; exists es, v; split; [exact Hpath|].
      change (weight fw f + calls_path_weight g fw es = weight fw f +
        fold_right Nat.max 0 (map (calls_best_nat EF r) (Graph.nodes g))).
      rewrite Hweight; reflexivity.
Qed.

(** Sum an innermost-first frame prefix through the first occurrence of the selected function. *)
Fixpoint calls_frame_sum {F} (EF : encoding F) (fw : frame_weights F) (f : F)
    (stack : list F) : nat :=
  match stack with
  | [] => 0
  | g :: rest => weight fw g +
      if Pos.eqb (encode EF g) (encode EF f) then 0 else calls_frame_sum EF fw f rest
  end.

(** Active frame weights include the first activation of the query, or the entire absent prefix. *)
Definition stack_above {S F P} (EF : encoding F) (cv : calls_view S F P)
    (fw : frame_weights F) (f : F) (s : S) : nat :=
  calls_frame_sum EF fw f (active cv s).

Lemma calls_path_weight_app {F E} (g : Graph.t F E) fw es fs :
  calls_path_weight g fw (es ++ fs) = calls_path_weight g fw es + calls_path_weight g fw fs.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  change (weight fw (Graph.target g e) + calls_path_weight g fw (es ++ fs) =
    weight fw (Graph.target g e) + calls_path_weight g fw es + calls_path_weight g fw fs).
  rewrite IH; lia.
Qed.

Lemma calls_frames_weight_path {S F P} (EF : encoding F) (cv : calls_view S F P)
    resolve fw stack : forall g f,
  frames_linked cv resolve g stack -> In f (g :: map fst stack) ->
  exists es, path (call_graph cv resolve) f es g /\
    calls_frame_sum EF fw f (g :: map fst stack) =
      weight fw f + calls_path_weight (call_graph cv resolve) fw es.
Proof.
  induction stack as [|[caller p] rest IH]; intros g f Hlinked Hin.
  - destruct Hin as [<-|[]]; exists []; split; [constructor|].
    cbn [calls_frame_sum]; rewrite Pos.eqb_refl; cbn; lia.
  - change (In f (g :: caller :: map fst rest)) in Hin.
    destruct (Pos.eqb (encode EF g) (encode EF f)) eqn:Hequal.
    + apply Pos.eqb_eq, (encode_injective EF) in Hequal; subst g.
      exists []; split; [constructor|].
      cbn [calls_frame_sum]; rewrite Pos.eqb_refl; cbn; lia.
    + destruct Hin as [Heq|Hin].
      { subst f; rewrite Pos.eqb_refl in Hequal; discriminate. }
      destruct Hlinked as [Hcaller [Hsite [Htarget Hlinked]]].
      destruct (IH caller f Hlinked Hin) as [es [Hpath Hweight]].
      exists (es ++ [CallEdge p g]); split.
      * eapply path_snoc; [exact Hpath|symmetry; exact Hcaller|].
        apply call_graph_edge; assumption.
      * change (weight fw g +
          (if Pos.eqb (encode EF g) (encode EF f) then 0
           else calls_frame_sum EF fw f (caller :: map fst rest)) =
          weight fw f + calls_path_weight (call_graph cv resolve) fw (es ++ [CallEdge p g])).
        rewrite Hequal, Hweight, calls_path_weight_app.
        change (weight fw g + (weight fw f + calls_path_weight (call_graph cv resolve) fw es) =
          weight fw f + (calls_path_weight (call_graph cv resolve) fw es + (weight fw g + 0))).
        lia.
Qed.

(** A finite exact demand bounds the actual frame chain through the query's first activation. *)
Theorem stack_demand_sound {S O F P} (EF : encoding F) (m : semantics S O)
    (cv : calls_view S F P) (resolve : P -> list F) (fw : frame_weights F)
    (f : F) (d : nat) :
  calls_view_laws m cv resolve -> graph_wf (call_graph cv resolve) ->
  stack_demand EF cv (call_graph cv resolve) fw f = Some d ->
  forall s, reachable_state m s -> In f (active cv s) -> stack_above EF cv fw f s <= d.
Proof.
  intros Hcalls Hwf Hd s Hreach Hin.
  pose proof (frames_listed Hcalls s Hreach f Hin) as Hf.
  destruct (calls_frames_weight_path EF cv resolve fw (frames cv s) (here cv s) f
    (reachable_frames_linked m cv resolve Hcalls s Hreach) Hin) as [es [Hpath Hweight]].
  unfold stack_above, active; rewrite Hweight.
  exact (proj1 (proj2 (stack_demand_exact EF cv (call_graph cv resolve) fw f Hwf Hf) d Hd)
    es (here cv s) Hpath).
Qed.

Lemma calls_contexts_complete {P} (sites : list P) k c :
  length c <= k -> incl c sites -> In c (calls_contexts sites k).
Proof.
  revert c; induction k as [|k IH]; intros [|p c] Hlength Hin; cbn in *.
  - left; reflexivity.
  - lia.
  - left; reflexivity.
  - right; apply in_flat_map; exists p; split; [apply Hin; left; reflexivity|].
    apply in_map; apply IH; [lia|].
    intros q Hq; apply Hin; right; exact Hq.
Qed.

Lemma calls_context_push {P} k (p : P) xs :
  push_ctx k p (firstn k xs) = firstn k (p :: xs).
Proof.
  destruct k as [|k]; [reflexivity|].
  change (p :: firstn k (firstn (Datatypes.S k) xs) = p :: firstn k xs).
  rewrite firstn_firstn, Nat.min_l by lia; reflexivity.
Qed.

Lemma calls_context_listed {S O F P} (m : semantics S O) (cv : calls_view S F P)
    resolve k s stack :
  calls_view_laws m cv resolve -> reachable_state m s -> incl stack (frames cv s) ->
  In (firstn k (map snd stack))
    (calls_contexts (flat_map (sites_of cv) (functions cv)) k).
Proof.
  intros Hcalls Hreach Hin; apply calls_contexts_complete.
  - rewrite length_firstn; apply Nat.le_min_l.
  - intros p Hp.
    assert (Hfull : In p (map snd stack)).
    { rewrite <- (firstn_skipn k (map snd stack)); apply in_or_app; left; exact Hp. }
    apply in_map_iff in Hfull.
    destruct Hfull as [[f q] [Heq Hframe]]; cbn in Heq; subst q.
    pose proof (reachable_frames_linked m cv resolve Hcalls s Hreach) as Hlinked.
    assert (Hsite : forall g frames, frames_linked cv resolve g frames ->
      In (f, p) frames -> In p (sites_of cv f)).
    { intros g frames; revert g; induction frames as [|[h q] rest IH];
        intros g Hlinks Hmember; [contradiction|].
      destruct Hlinks as [_ [Hq [_ Hrest]]]; destruct Hmember as [Heq|Hmember].
      - inversion Heq; subst; exact Hq.
      - eapply IH; eassumption. }
    apply in_flat_map; exists f; split.
    + apply (frames_listed Hcalls s Hreach); right; apply in_map_iff.
      exists (f, p); split; [reflexivity|exact (Hin _ Hframe)].
    + eapply Hsite; [exact Hlinked|apply Hin; exact Hframe].
Qed.

Lemma callstring_row_listed {S F P A} k (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) row c :
  In c (calls_contexts (flat_map (sites_of cv) (functions cv)) k) ->
  In row (System.constraints (summary_system cv resolve sp)) ->
  In (row, c) (System.constraints (callstring_system k cv resolve sp)).
Proof.
  intros Hcontext Hrow; apply in_flat_map; exists c; split; [exact Hcontext|].
  apply in_map_iff; exists row; split; [reflexivity|exact Hrow].
Qed.

Lemma callstring_local_bound {S F P A} k (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) sigma f c :
  post_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  In f (functions cv) ->
  In c (calls_contexts (flat_map (sites_of cv) (functions cv)) k) ->
  leb (slat sp) (local sp f) (sigma (f, c)) = true.
Proof.
  intros Hpost Hf Hc.
  assert (Hrow : In (SLocal f, c) (System.constraints (callstring_system k cv resolve sp))).
  { apply callstring_row_listed; [exact Hc|].
    apply in_or_app; left; apply in_map; exact Hf. }
  exact (proj1 (Hpost (SLocal f, c) Hrow)).
Qed.

Lemma callstring_call_bound {S F P A} k (cv : calls_view S F P) resolve
    (sp : summary_spec F P A) sigma f p g c :
  post_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  In f (functions cv) -> In p (sites_of cv f) -> In g (resolve p) ->
  In c (calls_contexts (flat_map (sites_of cv) (functions cv)) k) ->
  leb (slat sp) (via_call sp p g (sigma (g, push_ctx k p c)))
    (sigma (caller_of cv p, c)) = true.
Proof.
  intros Hpost Hf Hp Hg Hc.
  assert (Hrow : In (SCall p g, c) (System.constraints (callstring_system k cv resolve sp))).
  { apply callstring_row_listed; [exact Hc|].
    apply in_or_app; right; apply in_flat_map; exists f; split; [exact Hf|].
    apply in_flat_map; exists p; split; [exact Hp|apply in_map; exact Hg]. }
  exact (proj1 (Hpost (SCall p g, c) Hrow)).
Qed.

Lemma callstring_frames_cover {S O F P A} (m : semantics S O) k
    (cv : calls_view S F P) resolve (sp : summary_spec F P A) (sc : step_cover S O A)
    sigma s l s' :
  calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  post_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  reachable_state m s -> forall stack g,
  frames_linked cv resolve g stack -> incl stack (frames cv s) ->
  step_covers sc (sigma (g, firstn k (map snd stack))) s l s' ->
  forall i f, nth_error (g :: map fst stack) i = Some f ->
  step_covers sc (sigma (f, firstn k (map snd (skipn i stack)))) s l s'.
Proof.
  intros Hcalls Hsummary Hpost Hreach stack.
  induction stack as [|[caller p] rest IH]; intros g Hlinked Hin Hcover [|i] f Hnth.
  - cbn in Hnth; inversion Hnth; subst f; exact Hcover.
  - cbn in Hnth; destruct i; discriminate.
  - cbn in Hnth; inversion Hnth; subst f; exact Hcover.
  - cbn in Hnth; cbn [skipn].
    destruct Hlinked as [Hcaller [Hsite [Htarget Hlinked]]].
    eapply (IH caller Hlinked); [| |exact Hnth].
    + intros fr Hfr; apply Hin; right; exact Hfr.
    + eapply (covers_monotone Hsummary).
      * rewrite <- Hcaller; eapply callstring_call_bound;
          [exact Hpost| |exact Hsite|exact Htarget|].
        -- apply (frames_listed Hcalls s Hreach); right; apply in_map_iff.
           exists (caller, p); split; [reflexivity|apply Hin; left; reflexivity].
        -- eapply calls_context_listed; [exact Hcalls|exact Hreach|].
           intros fr Hfr; apply Hin; right; exact Hfr.
      * apply (call_covers Hsummary p g _ s l s' Hreach).
        -- rewrite Hcaller; apply Hin; left; reflexivity.
        -- rewrite calls_context_push; exact Hcover.
Qed.

(** Each active frame's bounded-context summary covers every actual transition above it. *)
Theorem callstring_sound {S O F P A} (m : semantics S O) (k : nat)
    (cv : calls_view S F P) (resolve : P -> list F) (sp : summary_spec F P A)
    (sc : step_cover S O A) (sigma : F * list P -> A) :
  calls_view_laws m cv resolve -> summary_laws m cv sp sc ->
  post_solution (slat sp) (callstring_system k cv resolve sp) sigma ->
  forall s l s' i f, reachable_state m s -> step m s l s' ->
    nth_error (active cv s) i = Some f ->
    step_covers sc (sigma (f, ctx_of cv k s i)) s l s'.
Proof.
  intros Hcalls Hsummary Hpost s l s' i f Hreach Hstep Hnth.
  eapply callstring_frames_cover; [exact Hcalls|exact Hsummary|exact Hpost|exact Hreach| | | |].
  - eapply reachable_frames_linked; eassumption.
  - apply incl_refl.
  - eapply (covers_monotone Hsummary).
    + eapply callstring_local_bound; [exact Hpost| |].
      * apply (frames_listed Hcalls s Hreach); left; reflexivity.
      * eapply calls_context_listed; [exact Hcalls|exact Hreach|apply incl_refl].
    + exact (local_covers Hsummary s l s' Hreach Hstep).
  - exact Hnth.
Qed.

(** Actual and formal argument positions share the innermost frame's value observation. *)
Record args_view (S F P V C : Type) : Type := ArgsView {
  actuals : P -> list V;
  formals : F -> list V;
  frame_val : S -> V -> option C
}.

Arguments ArgsView {S F P V C}.
Arguments actuals {S F P V C}.
Arguments formals {S F P V C}.
Arguments frame_val {S F P V C}.

(** Absent caller buckets denote the empty list. *)
Definition callers_of {F P} (EF : encoding F) (ix : Map.t F (list P)) (f : F) : list P :=
  match Map.get EF f ix with
  | Some ps => ps
  | None => []
  end.

(** Build target buckets in source order, traversing each site and resolver occurrence once. *)
Definition callers_index {S F P} (EF : encoding F) (cv : calls_view S F P)
    (resolve : P -> list F) : Map.t F (list P) :=
  fold_right (fun p ix =>
    fold_right (fun f acc => Map.set EF f (p :: callers_of EF acc f) acc) ix (resolve p))
    Map.empty (flat_map (sites_of cv) (functions cv)).

(** Each formal receives the join of the corresponding actual facts at all indexed sites. *)
Definition arg_fact {S F P V C A} (EF : encoding F) (av : args_view S F P V C)
    (ix : Map.t F (list P)) (L : lattice A) (fact : V -> A) (f : F) (i : nat) : A :=
  fold_left (join L)
    (flat_map (fun p =>
      match nth_error (actuals av p) i with
      | Some x => [fact x]
      | None => []
      end) (callers_of EF ix f)) (bot L).

(** The refined resolver preserves all call-view laws under the stated value coverage. *)
Theorem resolver_sound {S O F P V C A} (m : semantics S O) (cv : calls_view S F P)
    (direct : P -> option F) (callee_val : P -> option V) (fact : V -> A)
    (fns : A -> option (list F)) (G : concretisation A C) (val : S -> V -> option C)
    (fn_of : C -> option F) :
  calls_view_laws m cv (fun _ => functions cv) ->
  (forall s l s' p f, reachable_state m s -> step m s l s' ->
    In p (sites_of cv (here cv s)) ->
    frames cv s' = (here cv s, p) :: frames cv s -> here cv s' = f ->
    direct p = Some f \/ (direct p = None /\ callee_val p = None) \/
    (direct p = None /\ exists v c, callee_val p = Some v /\ val s v = Some c /\
      fn_of c = Some f /\ gamma G (fact v) c /\
      forall fs, fns (fact v) = Some fs -> In f fs)) ->
  calls_view_laws m cv (resolver direct callee_val fact fns (functions cv)).
Proof.
  intros Hcalls Htargets; constructor.
  - exact (sites_caller Hcalls).
  - exact (initial_roots Hcalls).
  - exact (frames_listed Hcalls).
  - intros s l s' Hreach Hstep.
    destruct (step_shape Hcalls s l s' Hreach Hstep) as [Hstay|[Hcall|Hreturn]].
    + left; exact Hstay.
    + right; left; destruct Hcall as [p [Hsite [Hlisted Hframes]]].
      exists p; split; [exact Hsite|]; split; [|exact Hframes].
      destruct (Htargets s l s' p (here cv s') Hreach Hstep Hsite Hframes eq_refl)
        as [Hdirect|[[Hdirect Hnone]|[Hdirect [v [c [Hv [Hval [Hfn [Hgamma Hfs]]]]]]]]].
      * unfold resolver; rewrite Hdirect; left; reflexivity.
      * unfold resolver; rewrite Hdirect, Hnone; exact Hlisted.
      * unfold resolver; rewrite Hdirect, Hv.
        destruct (fns (fact v)) as [fs|] eqn:Hfact; [apply Hfs; reflexivity|exact Hlisted].
    + right; right; exact Hreturn.
Qed.

(** Encoded function identifiers have constructive equality. *)
Definition calls_eq_dec {F} (EF : encoding F) (f g : F) : {f = g} + {f <> g}.
Proof.
  destruct (Pos.eq_dec (encode EF f) (encode EF g)) as [Heq|Hne].
  - left; apply (encode_injective EF); exact Heq.
  - right; intro Heq; subst g; contradiction.
Defined.

Lemma calls_frame_path {S F P} (cv : calls_view S F P) resolve g stack :
  frames_linked cv resolve g stack -> forall f, In f (map fst stack) ->
  exists es, es <> [] /\ path (call_graph cv resolve) f es g.
Proof.
  revert g; induction stack as [|[caller p] rest IH]; intros g Hlinked f Hin.
  - contradiction.
  - destruct Hlinked as [Hcaller [Hsite [Htarget Hlinked]]].
    assert (Hedge : In (CallEdge p g) (Graph.out (call_graph cv resolve) caller)).
    { apply call_graph_edge; assumption. }
    assert (Hone : path (call_graph cv resolve) caller [CallEdge p g] g).
    { rewrite <- Hcaller; apply (path_cons (g := call_graph cv resolve) (CallEdge p g) [] g).
      - cbn; rewrite Hcaller; exact Hedge.
      - constructor. }
    destruct Hin as [Heq|Hin].
    + subst f; exists [CallEdge p g]; split; [discriminate|exact Hone].
    + destruct (IH caller Hlinked f Hin) as [es [Hne Hpath]].
      exists (es ++ [CallEdge p g]); split.
      * intro Hnil; apply app_eq_nil in Hnil; destruct Hnil as [_ Hbad]; discriminate.
      * eapply tarjan_path_append; eassumption.
Qed.

Lemma calls_cycle_of_path {F P} (g : Graph.t F (call_edge F P)) f es :
  es <> [] -> path g f es f -> recursive g f.
Proof.
  intros Hne Hpath; inversion Hpath; subst; [contradiction|].
  eexists; eexists; split; eassumption.
Qed.

Lemma calls_duplicate_cycle {S F P} (EF : encoding F) (cv : calls_view S F P)
    resolve stack : forall g,
  frames_linked cv resolve g stack -> ~ NoDup (g :: map fst stack) ->
  exists f, In f (g :: map fst stack) /\ recursive (call_graph cv resolve) f.
Proof.
  induction stack as [|[caller p] rest IH]; intros g Hlinked Hdup.
  - exfalso; apply Hdup; constructor; [intro H; exact H|constructor].
  - destruct (in_dec (calls_eq_dec EF) g (map fst ((caller, p) :: rest)))
      as [Hin|Hnot].
    + destruct (calls_frame_path cv resolve g _ Hlinked g Hin) as [es [Hne Hpath]].
      exists g; split; [left; reflexivity|eapply calls_cycle_of_path; eassumption].
    + destruct Hlinked as [_ [_ [_ Hlinked]]].
      destruct (IH caller Hlinked) as [f [Hin Hcycle]].
      * intro Hnd; apply Hdup; constructor; assumption.
      * exists f; split; [right; exact Hin|exact Hcycle].
Qed.

(** A duplicate active function has a genuine nonempty call-graph cycle. *)
Theorem recursive_sound {S O F P} (EF : encoding F) (m : semantics S O)
    (cv : calls_view S F P) (resolve : P -> list F) (s : S) :
  calls_view_laws m cv resolve -> reachable_state m s -> ~ NoDup (active cv s) ->
  exists f, In f (active cv s) /\ recursive (call_graph cv resolve) f.
Proof.
  intros Hcalls Hreach Hdup; apply (calls_duplicate_cycle EF cv resolve (frames cv s)).
  - eapply reachable_frames_linked; eassumption.
  - exact Hdup.
Qed.

(** Call-graph unreachability excludes a function from every reachable active stack. *)
Theorem unreachable_never_runs {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) :
  calls_view_laws m cv resolve -> ~ reachable (call_graph cv resolve) f ->
  forall s, reachable_state m s -> ~ In f (active cv s).
Proof.
  intros Hcalls Hnot s Hreach Hin; apply Hnot.
  exact (active_reachable_in_call_graph m cv resolve Hcalls s Hreach f Hin).
Qed.

(** False purity summaries cover the same transition through every suspended caller. *)
Theorem purity_sound {S O I H F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (ev : effects_view S I H) (impure_local : F -> bool)
    (sigma : F -> bool) :
  calls_view_laws m cv resolve ->
  summary_laws m cv (purity_spec cv impure_local) (purity_cover ev) ->
  post_solution (slat (purity_spec cv impure_local))
    (summary_system cv resolve (purity_spec cv impure_local)) sigma ->
  forall s l s' f, reachable_state m s -> step m s l s' -> In f (active cv s) ->
    sigma f = false -> l = nil /\ heap ev s' = heap ev s.
Proof.
  intros Hcalls Hsummary Hpost s l s' f Hreach Hstep Hin Hpure.
  exact (summary_sound m cv resolve (purity_spec cv impure_local) (purity_cover ev)
    sigma Hcalls Hsummary Hpost s l s' f Hreach Hstep Hin Hpure).
Qed.

(** A leaf transition preserves the suspended stack or returns to its caller. *)
Theorem callee_leaf_sound {S O F P} (m : semantics S O) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) :
  calls_view_laws m cv resolve -> callee_leaf cv f = true ->
  forall s l s', reachable_state m s -> here cv s = f -> step m s l s' ->
    frames cv s' = frames cv s \/ exists g p, frames cv s = (g, p) :: frames cv s'.
Proof.
  intros Hcalls Hleaf s l s' Hreach Hhere Hstep.
  destruct (step_shape Hcalls s l s' Hreach Hstep) as
    [[_ Hframes]|[[p [Hsite _]]|[g [p [Hframes _]]]]].
  - left; exact Hframes.
  - unfold callee_leaf in Hleaf; rewrite Hhere in Hsite.
    destruct (sites_of cv f); [contradiction|discriminate].
  - right; exists g, p; exact Hframes.
Qed.

Lemma callers_bucket_agrees {F P} (EF : encoding F) (ps : list F) (p : P) ix f q :
  In q (callers_of EF
    (fold_right (fun g acc => Map.set EF g (p :: callers_of EF acc g) acc) ix ps) f) <->
  (q = p /\ In f ps) \/ In q (callers_of EF ix f).
Proof.
  induction ps as [|g ps IH]; cbn [fold_right].
  - cbn; tauto.
  - destruct (Pos.eq_dec (encode EF f) (encode EF g)) as [Heq|Hne].
    + apply (encode_injective EF) in Heq; subst g.
      unfold callers_of at 1; rewrite Map.get_set_same.
      change (p = q \/ In q (callers_of EF
        (fold_right (fun g acc => Map.set EF g (p :: callers_of EF acc g) acc) ix ps) f) <->
        (q = p /\ (f = f \/ In f ps)) \/ In q (callers_of EF ix f)).
      rewrite IH; intuition congruence.
    + assert (Hfg : f <> g) by (intro Heq; subst; contradiction).
      unfold callers_of at 1; rewrite Map.get_set_other by exact Hfg.
      change (In q (callers_of EF
        (fold_right (fun g acc => Map.set EF g (p :: callers_of EF acc g) acc) ix ps) f) <->
        (q = p /\ In f (g :: ps)) \/ In q (callers_of EF ix f)).
      rewrite IH; cbn; intuition congruence.
Qed.

Lemma callers_sites_agrees {F P} (EF : encoding F) (resolve : P -> list F) sites ix f p :
  In p (callers_of EF (fold_right (fun q acc => fold_right
    (fun g acc => Map.set EF g (q :: callers_of EF acc g) acc) acc (resolve q)) ix sites) f)
  <-> (In p sites /\ In f (resolve p)) \/ In p (callers_of EF ix f).
Proof.
  induction sites as [|q sites IH]; cbn [fold_right].
  - cbn; tauto.
  - rewrite callers_bucket_agrees, IH; cbn; intuition congruence.
Qed.

(** Caller buckets contain exactly the listed sites whose resolver includes the queried target. *)
Theorem callers_index_agrees {S F P} (EF : encoding F) (cv : calls_view S F P)
    (resolve : P -> list F) (f : F) (p : P) :
  In p (callers_of EF (callers_index EF cv resolve) f) <->
  (exists g, In g (functions cv) /\ In p (sites_of cv g)) /\ In f (resolve p).
Proof.
  unfold callers_index; rewrite callers_sites_agrees.
  unfold callers_of; rewrite Map.get_empty; cbn; rewrite in_flat_map; tauto.
Qed.

Lemma calls_push_resolved {S O F P} (m : semantics S O) (cv : calls_view S F P) resolve :
  calls_view_laws m cv resolve -> forall s l s' p,
  reachable_state m s -> step m s l s' ->
  frames cv s' = (here cv s, p) :: frames cv s -> In (here cv s') (resolve p).
Proof.
  intros Hcalls s l s' p Hreach Hstep Hpush.
  destruct (step_shape Hcalls s l s' Hreach Hstep) as
    [[_ Hstay]|[[q [_ [Htarget Hframes]]]|[f [q [Hpop _]]]]].
  - pose proof (f_equal (@length (F * P)) Hpush) as Hlength.
    rewrite Hstay in Hlength; cbn in Hlength; lia.
  - rewrite Hpush in Hframes; inversion Hframes; subst q; exact Htarget.
  - pose proof (f_equal (@length (F * P)) Hpush) as Hlength.
    rewrite Hpop in Hlength; cbn in Hlength; lia.
Qed.

Lemma calls_join_member {A} (L : lattice A) : lattice_laws L -> forall xs a b,
  In a xs -> leb L a (fold_left (join L) xs b) = true.
Proof.
  intros Hlaws xs; induction xs as [|x xs IH]; intros a b Hin; [contradiction|].
  cbn; destruct Hin as [<-|Hin].
  - assert (Hacc : forall ys b, leb L b (fold_left (join L) ys b) = true).
    { induction ys as [|y ys IHy]; intro z; cbn.
      - apply (leb_refl Hlaws).
      - eapply (leb_trans Hlaws); [apply (join_upper_l Hlaws)|apply IHy]. }
    eapply (leb_trans Hlaws); [apply (join_upper_r Hlaws)|apply Hacc].
  - apply IH; exact Hin.
Qed.

(** The actual argument facts soundly cover each initialized formal on an actual call push. *)
Theorem arg_fact_sound {S O F P V C A} (m : semantics S O) (cv : calls_view S F P)
    (EF : encoding F) (av : args_view S F P V C) (L : lattice A) (G : concretisation A C)
    (resolve : P -> list F) (fact : V -> A) :
  calls_view_laws m cv resolve -> lattice_laws L -> concretisation_laws L G ->
  (forall s x c, reachable_state m s -> frame_val av s x = Some c -> gamma G (fact x) c) ->
  (forall s l s' p i y c, reachable_state m s -> step m s l s' ->
    frames cv s' = (here cv s, p) :: frames cv s ->
    nth_error (formals av (here cv s')) i = Some y -> frame_val av s' y = Some c ->
    exists z, nth_error (actuals av p) i = Some z /\ frame_val av s z = Some c) ->
  forall s l s' p i y c, reachable_state m s -> step m s l s' ->
    In p (sites_of cv (here cv s)) -> frames cv s' = (here cv s, p) :: frames cv s ->
    nth_error (formals av (here cv s')) i = Some y -> frame_val av s' y = Some c ->
    gamma G (arg_fact EF av (callers_index EF cv resolve) L fact (here cv s') i) c.
Proof.
  intros Hcalls Hlaws Hgamma Hfacts Hargs s l s' p i y c
    Hreach Hstep Hsite Hpush Hformal Hvalue.
  destruct (Hargs s l s' p i y c Hreach Hstep Hpush Hformal Hvalue) as [z [Hz Hval]].
  eapply (gamma_monotone Hgamma); [|exact (Hfacts s z c Hreach Hval)].
  unfold arg_fact; apply calls_join_member; [exact Hlaws|].
  apply in_flat_map; exists p; split.
  - apply callers_index_agrees; split.
    + exists (here cv s); split; [|exact Hsite].
      apply (frames_listed Hcalls s Hreach); left; reflexivity.
    + eapply calls_push_resolved; eassumption.
  - rewrite Hz; left; reflexivity.
Qed.
