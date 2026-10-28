(** * Prepared graph indexes

    Preparation indexes outgoing and incoming edges and computes binary traversal fuel.
    For example, a missing node has an empty adjacency list.
    Builds on: GraphCore and Collections maps. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Graph Require Import GraphCore.
Import List.ListNotations.

(** * Indexed adjacency *)

(** A prepared graph carries both adjacency indexes and a traversal bound. *)
Record prepared {V E} (EV : encoding V) (g : Graph.t V E) : Type := Prepared {
  out_index : Map.t V (list E);
  in_index : Map.t V (list E);
  fuel : positive
}.
Arguments Prepared {V E EV g}.
Arguments out_index {V E EV g}.
Arguments in_index {V E EV g}.
Arguments fuel {V E EV g}.

(** Return a stored adjacency list, defaulting to the empty list. *)
Definition index_edges {V E} (EV : encoding V) (m : Map.t V (list E)) (v : V) : list E :=
  match Map.get EV v m with
  | Some es => es
  | None => []
  end.

(** Read the indexed successors of a node. *)
Definition succ_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) : list E := index_edges EV (out_index p) v.

(** Read the indexed predecessors of a node. *)
Definition pred_edges {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) : list E := index_edges EV (in_index p) v.

(** Insert an incoming edge at the front of its target's list. *)
Definition index_edge {V E} (EV : encoding V) (g : Graph.t V E)
    (e : E) (m : Map.t V (list E)) : Map.t V (list E) :=
  Map.set EV (Graph.target g e) (e :: index_edges EV m (Graph.target g e)) m.

(** Construct adjacency indexes in node order and compute the traversal bound. *)
Definition prepare {V E} (EV : encoding V) (g : Graph.t V E) : prepared EV g :=
  {| out_index := fold_right (fun v m => Map.set EV v (Graph.out g v) m)
       Map.empty (Graph.nodes g);
     in_index := fold_right (fun v m => fold_right (index_edge EV g) m (Graph.out g v))
       Map.empty (Graph.nodes g);
     fuel := Pos.of_succ_nat (2 * length (Graph.nodes g) + edge_count g + 1) |}.

(** Prepared indexes agree with their graph and bound traversal. *)
Record prepared_laws {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop := {
  succ_agrees : forall v, In v (Graph.nodes g) -> succ_edges p v = Graph.out g v;
  succ_domain : forall v, ~ In v (Graph.nodes g) -> succ_edges p v = [];
  pred_agrees : forall v e, In v (Graph.nodes g) ->
    (In e (pred_edges p v) <->
     exists u, In u (Graph.nodes g) /\ In e (Graph.out g u) /\ Graph.target g e = v);
  pred_domain : forall v, ~ In v (Graph.nodes g) -> pred_edges p v = [];
  pred_nodup : forall v, NoDup (pred_edges p v);
  fuel_value : Pos.to_nat (fuel p) = 2 * length (Graph.nodes g) + edge_count g + 2
}.
Arguments Build_prepared_laws {V E EV g p} _ _ _ _ _ _.
Arguments succ_agrees {V E EV g p} _ v _.
Arguments succ_domain {V E EV g p} _ v _.
Arguments pred_agrees {V E EV g p} _ v e _.
Arguments pred_domain {V E EV g p} _ v _.
Arguments pred_nodup {V E EV g p} _ v.
Arguments fuel_value {V E EV g p} _.

(** Readiness combines graph, edge uniqueness and index laws. *)
Definition ready {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) : Prop :=
  graph_wf g /\ (forall v, NoDup (Graph.out g v)) /\ prepared_laws EV g p.

(** Reverse each edge and use the supplied exits as entries. *)
Definition reverse_graph {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (exits : list V) : Graph.t V E :=
  {| Graph.entries := exits; Graph.nodes := Graph.nodes g; Graph.out := pred_edges p;
     Graph.source := Graph.target g; Graph.target := Graph.source g |}.

(** Swap the indexes of a prepared graph for its reversal. *)
Definition prepared_reverse {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (exits : list V) : prepared EV (reverse_graph p exits) :=
  {| out_index := in_index p; in_index := out_index p; fuel := fuel p |}.

(** * Index construction laws *)

Lemma index_edge_at {V E} (EV : encoding V) (g : Graph.t V E) e m v :
  index_edges EV (index_edge EV g e m) v =
    if Pos.eqb (encode EV (Graph.target g e)) (encode EV v)
    then e :: index_edges EV m v else index_edges EV m v.
Proof.
  unfold index_edge, index_edges.
  destruct (Pos.eqb (encode EV (Graph.target g e)) (encode EV v)) eqn:Heq.
  - apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst v.
    rewrite Map.get_set_same; reflexivity.
  - apply Pos.eqb_neq in Heq; rewrite Map.get_set_other; [reflexivity|].
    intro H; subst v; apply Heq; reflexivity.
Qed.

Lemma index_edge_fold {V E} (EV : encoding V) (g : Graph.t V E) es m v :
  index_edges EV (fold_right (index_edge EV g) m es) v =
    filter (fun e => Pos.eqb (encode EV (Graph.target g e)) (encode EV v)) es ++
    index_edges EV m v.
Proof.
  induction es as [|e es IH]; simpl; [reflexivity|].
  rewrite index_edge_at, IH.
  destruct (Pos.eqb (encode EV (Graph.target g e)) (encode EV v)); reflexivity.
Qed.

Lemma index_nodes_fold {V E} (EV : encoding V) (g : Graph.t V E) vs m v :
  index_edges EV
    (fold_right (fun u acc => fold_right (index_edge EV g) acc (Graph.out g u)) m vs) v =
  filter (fun e => Pos.eqb (encode EV (Graph.target g e)) (encode EV v))
    (flat_map (Graph.out g) vs) ++ index_edges EV m v.
Proof.
  induction vs as [|u vs IH]; simpl; [reflexivity|].
  rewrite index_edge_fold, IH, filter_app, app_assoc; reflexivity.
Qed.

Lemma prepare_pred {V E} (EV : encoding V) (g : Graph.t V E) v :
  pred_edges (prepare EV g) v =
  filter (fun e => Pos.eqb (encode EV (Graph.target g e)) (encode EV v))
    (flat_map (Graph.out g) (Graph.nodes g)).
Proof.
  unfold pred_edges, prepare; simpl; rewrite index_nodes_fold.
  unfold index_edges; rewrite Map.get_empty, app_nil_r; reflexivity.
Qed.

Lemma prepare_succ {V E} (EV : encoding V) (g : Graph.t V E) vs v :
  index_edges EV (fold_right (fun u m => Map.set EV u (Graph.out g u) m) Map.empty vs) v =
  if existsb (fun u => Pos.eqb (encode EV u) (encode EV v)) vs
  then Graph.out g v else [].
Proof.
  induction vs as [|u vs IH]; simpl.
  - unfold index_edges; rewrite Map.get_empty; reflexivity.
  - destruct (Pos.eqb (encode EV u) (encode EV v)) eqn:Heq.
    + apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst u.
      unfold index_edges; rewrite Map.get_set_same; reflexivity.
    + assert (Hne : v <> u).
      { intro H; subst u; rewrite Pos.eqb_refl in Heq; discriminate. }
      unfold index_edges at 1; rewrite Map.get_set_other by exact Hne; exact IH.
Qed.

Lemma nodup_app_disjoint {A} (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros Hxs Hys Hdis; induction Hxs as [|x xs Hnot Hxs IH]; simpl; [exact Hys|].
  constructor.
  - rewrite in_app_iff; intros [Hin|Hin]; [contradiction|].
    eapply Hdis; [left; reflexivity|exact Hin].
  - apply IH; intros y Hin; apply Hdis; right; exact Hin.
Qed.

Lemma graph_edges_nodup {V E} (g : Graph.t V E) vs :
  NoDup vs -> (forall v, NoDup (Graph.out g v)) ->
  (forall v e, In e (Graph.out g v) -> Graph.source g e = v) ->
  NoDup (flat_map (Graph.out g) vs).
Proof.
  intros Hnodes Hedges Hsource; induction Hnodes as [|v vs Hnot Hnodes IH]; simpl.
  - constructor.
  - apply nodup_app_disjoint; [apply Hedges|exact IH|].
    intros e He Hin; apply in_flat_map in Hin.
    destruct Hin as [u [Hu Heu]].
    apply Hnot; assert (u = v) by (rewrite <- (Hsource u e Heu), (Hsource v e He); reflexivity).
    now subst u.
Qed.

(** Preparation establishes the graph's index and fuel laws. *)
Theorem prepare_ready {V E} (EV : encoding V) (g : Graph.t V E) :
  graph_wf g -> (forall x, NoDup (Graph.out g x)) -> ready EV g (prepare EV g).
Proof.
  intros Hwf Hedges; split; [exact Hwf|]; split; [exact Hedges|].
  constructor.
  - intros v Hin; unfold succ_edges, prepare; simpl; rewrite prepare_succ.
    assert (Hex : existsb (fun u => Pos.eqb (encode EV u) (encode EV v))
      (Graph.nodes g) = true).
    { apply existsb_exists; exists v; split; [exact Hin|apply Pos.eqb_refl]. }
    now rewrite Hex.
  - intros v Hnot; unfold succ_edges, prepare; simpl; rewrite prepare_succ.
    destruct (existsb _ _) eqn:Hex; [|reflexivity].
    apply existsb_exists in Hex; destruct Hex as [u [Hu Heq]].
    apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst u; contradiction.
  - intros v e Hin; rewrite prepare_pred, filter_In; split.
    + intros [He Heq]; apply in_flat_map in He; destruct He as [u [Hu He]].
      apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; eauto.
    + intros [u [Hu [He Heq]]]; split.
      * apply in_flat_map; exists u; auto.
      * subst v; apply Pos.eqb_refl.
  - intros v Hnot; rewrite prepare_pred.
    destruct (filter _ _) as [|e es] eqn:Hfilter; [reflexivity|].
    assert (He : In e (filter (fun e => Pos.eqb (encode EV (Graph.target g e))
      (encode EV v)) (flat_map (Graph.out g) (Graph.nodes g)))) by
      (rewrite Hfilter; left; reflexivity).
    apply filter_In in He; destruct He as [He Heq].
    apply in_flat_map in He; destruct He as [u [Hu He]].
    apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq.
    exfalso; apply Hnot; rewrite <- Heq; eapply out_target_in; eauto.
  - intro v; rewrite prepare_pred; apply NoDup_filter.
    apply graph_edges_nodup; [apply (nodes_nodup Hwf)|exact Hedges|].
    intros; eapply out_source; eauto.
  - simpl; rewrite SuccNat2Pos.id_succ; lia.
Qed.

(** Ready predecessor lists contain no repeated edge. *)
Theorem pred_edges_nodup {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (v : V) : ready EV g p -> NoDup (pred_edges p v).
Proof.
  intros [_ [_ Hlaws]]; apply (pred_nodup Hlaws).
Qed.

Lemma reverse_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits :
  ready EV g p -> incl exits (Graph.nodes g) -> graph_wf (reverse_graph p exits).
Proof.
  intros [Hwf [Hunique Hlaws]] Hexit; constructor; simpl.
  - apply (nodes_nodup Hwf).
  - exact Hexit.
  - intros v e He; destruct (in_dec (fun x y =>
      match Pos.eq_dec (encode EV x) (encode EV y) with
      | left H => left (encode_injective EV x y H)
      | right H => right (fun Heq => H (f_equal (encode EV) Heq))
      end) v (Graph.nodes g)) as [Hin|Hnot].
    + apply (pred_agrees Hlaws v e Hin) in He; destruct He as [u [Hu [He Heq]]].
      exact Heq.
    + rewrite (pred_domain Hlaws v Hnot) in He; contradiction.
  - intros v e Hv He; apply (pred_agrees Hlaws v e Hv) in He.
    destruct He as [u [Hu [He _]]]. rewrite (out_source Hwf u e He); exact Hu.
Qed.

Lemma flat_edges_length {V E} (g : Graph.t V E) vs :
  length (flat_map (Graph.out g) vs) =
  fold_right (fun v n => length (Graph.out g v) + n) 0 vs.
Proof.
  induction vs as [|v vs IH]; simpl; [reflexivity|].
  rewrite length_app, IH; reflexivity.
Qed.

Lemma reverse_edge_count {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits :
  ready EV g p -> incl exits (Graph.nodes g) -> edge_count (reverse_graph p exits) = edge_count g.
Proof.
  intros Hready Hexit.
  destruct Hready as [Hwf [Hunique Hlaws]].
  assert (Hrev : graph_wf (reverse_graph p exits)).
  { apply reverse_wf; [exact (conj Hwf (conj Hunique Hlaws))|exact Hexit]. }
  assert (Hperm : Permutation (flat_map (Graph.out (reverse_graph p exits)) (Graph.nodes g))
    (flat_map (Graph.out g) (Graph.nodes g))).
  { apply NoDup_Permutation.
    - apply graph_edges_nodup; [apply (nodes_nodup Hwf)| |].
      + intro v; apply (pred_nodup Hlaws).
      + intros v e He; eapply out_source; [exact Hrev|exact He].
    - apply graph_edges_nodup; [apply (nodes_nodup Hwf)|exact Hunique|].
      intros; eapply out_source; eauto.
    - intro e; repeat rewrite in_flat_map; split.
      + intros [v [Hv He]]; simpl in He.
        apply (pred_agrees Hlaws v e Hv) in He.
        destruct He as [u [Hu [He _]]]; eauto.
      + intros [u [Hu He]].
        assert (Hv : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
        exists (Graph.target g e); split; [exact Hv|]. simpl.
        apply (pred_agrees Hlaws _ _ Hv); exists u; auto. }
  apply Permutation_length in Hperm; repeat rewrite flat_edges_length in Hperm; exact Hperm.
Qed.

(** Reversal preserves readiness when its entries are nodes. *)
Theorem reverse_graph_ready {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (exits : list V) :
  ready EV g p -> incl exits (Graph.nodes g) ->
  ready EV (reverse_graph p exits) (prepared_reverse p exits).
Proof.
  intros Hready Hexit; pose proof Hready as [Hwf [Hunique Hlaws]].
  split; [apply reverse_wf; assumption|]; split.
  - intro v; apply (pred_nodup Hlaws).
  - constructor; simpl.
    + intros v Hin; reflexivity.
    + intros v Hnot; apply (pred_domain Hlaws); exact Hnot.
    + intros v e Hv; unfold pred_edges, prepared_reverse; simpl; fold (succ_edges p v).
      rewrite (succ_agrees Hlaws v Hv); split.
      * intro He; exists (Graph.target g e); split.
        -- eapply out_target_in; eauto.
        -- split; [|eapply out_source; eauto].
           apply (pred_agrees Hlaws); [eapply out_target_in; eauto|].
           exists v; auto.
      * intros [u [Hu [He Heq]]].
        apply (pred_agrees Hlaws u e Hu) in He.
        destruct He as [w [Hw [He Htarget]]].
        assert (Graph.source g e = w) by (eapply out_source; eauto).
        subst v; subst w; exact He.
    + intros v Hnot; unfold pred_edges, prepared_reverse; simpl; apply (succ_domain Hlaws).
      exact Hnot.
    + intro v; unfold pred_edges, prepared_reverse; simpl; fold (succ_edges p v).
      destruct (in_dec (fun x y =>
        match Pos.eq_dec (encode EV x) (encode EV y) with
        | left H => left (encode_injective EV x y H)
        | right H => right (fun Heq => H (f_equal (encode EV) Heq))
        end) v (Graph.nodes g)) as [Hin|Hnot].
      * rewrite (succ_agrees Hlaws v Hin); apply Hunique.
      * rewrite (succ_domain Hlaws v Hnot); constructor.
    + change (Pos.to_nat (fuel p) = 2 * length (Graph.nodes g) +
        edge_count (reverse_graph p exits) + 2).
      rewrite (reverse_edge_count EV g p exits Hready Hexit); apply (fuel_value Hlaws).
Qed.

Lemma path_reverse_forward {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits u es v :
  ready EV g p -> In u (Graph.nodes g) -> path g u es v ->
  path (reverse_graph p exits) v (rev es) u.
Proof.
  intros [Hwf [Hunique Hlaws]] Hu Hpath; induction Hpath as [v|e es w Hedge Hpath IH].
  - simpl; constructor.
  - simpl in *.
    assert (Ht : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
    specialize (IH Ht).
    eapply path_snoc; [exact IH|reflexivity|].
    simpl; apply (pred_agrees Hlaws _ _ Ht).
    exists (Graph.source g e); auto.
Qed.

Lemma path_reverse_backward {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) exits u es v :
  ready EV g p -> In u (Graph.nodes g) ->
  path (reverse_graph p exits) u es v -> path g v (rev es) u.
Proof.
  intros [Hwf [Hunique Hlaws]] Hu Hpath.
  induction Hpath as [v|e es w Hedge Hpath IH].
  - simpl; constructor.
  - simpl in *; apply (pred_agrees Hlaws _ _ Hu) in Hedge.
    destruct Hedge as [x [Hx [He Heq]]].
    assert (Hsource : Graph.source g e = x) by (eapply out_source; eauto).
    assert (Hs : In (Graph.source g e) (Graph.nodes g)) by (rewrite Hsource; exact Hx).
    specialize (IH Hs); eapply path_snoc; [exact IH|reflexivity|].
    rewrite Hsource; exact He.
Qed.

(** Reversal reverses exactly the paths between graph nodes. *)
Theorem reverse_path {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (u v : V) (es : list E) (exits : list V) :
  ready EV g p -> In u (Graph.nodes g) -> In v (Graph.nodes g) ->
  (path g u es v <-> path (reverse_graph p exits) v (rev es) u).
Proof.
  intros Hready Hu Hv; split.
  - apply path_reverse_forward; assumption.
  - intro Hpath.
    pose proof (path_reverse_backward EV g p exits v (rev es) u Hready Hv Hpath) as Hreverse.
    now rewrite rev_involutive in Hreverse.
Qed.
