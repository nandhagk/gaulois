(** * Reducibility through DFS back edges

    Reducibility means that each reachable cycle contains a dominance back edge.
    For example, the edge from a loop body to its dominating header is a back edge.
    Builds on: GraphCore, GraphPrepare, GraphDfs, GraphDominance and GraphDominators. *)

From Stdlib Require Import List Bool PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance GraphDominators.
Import List.ListNotations.

(** A reachable edge is a back edge when its target dominates its source. *)
Definition back_edge {V E} (g : Graph.t V E) (e : E) : Prop :=
  In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
  dominates g (Graph.target g e) (Graph.source g e).

(** Each nonempty reachable cycle must contain a dominance back edge. *)
Definition reducible {V E} (g : Graph.t V E) : Prop :=
  forall v es, reachable g v -> es <> [] -> path g v es v ->
    exists e, In e es /\ back_edge g e.

(** Test every indexed outgoing edge of the DFS preorder with two interval queries. *)
Definition reducible_b {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (t : dom_tree V) : bool :=
  let r := dfs p FinSet.empty (Graph.entries g) in
  forallb (fun v => forallb (fun e =>
    negb (ancestor_b EV r (Graph.target g e) (Graph.source g e)) ||
    dominates_b EV t (Graph.target g e) (Graph.source g e)) (succ_edges p v)) (preorder r).

Section Reducibility.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Local Abbreviation R := (dfs p FinSet.empty (Graph.entries g)).

Lemma reducible_path_app u es v fs w :
  path g u es v -> path g v fs w -> path g u (es ++ fs) w.
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Htail.
  - exact Htail.
  - cbn; constructor; [exact Hedge|apply IH; exact Htail].
Qed.

Lemma reducible_parent v e : ready EV g p -> Map.get EV v (tree_edge R) = Some e ->
  In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
  exists a b, Map.get EV (Graph.source g e) (pre_num R) = Some a /\
    Map.get EV v (pre_num R) = Some b /\ Pos.lt a b.
Proof.
  intros Hready He; pose proof Hready as [Hwf _].
  destruct (dfs_final_spec EV g p FinSet.empty (Graph.entries g) Hready (entries_in Hwf))
    as [_ [Hlabels _]].
  unfold dfs in He; cbn [tree_edge] in He.
  destruct (dfs_parent_labels _ _ _ _ Hlabels v e He)
    as [_ [_ [Hedge [Htarget Hrank]]]].
  exact (conj Hedge (conj Htarget Hrank)).
Qed.

Lemma reducible_ancestor_path u v : ready EV g p -> dfs_ancestor EV g R u v ->
  exists es, path g u es v /\
    forall e, In e es -> Map.get EV (Graph.target g e) (tree_edge R) = Some e.
Proof.
  intros Hready Hanc; induction Hanc as [u v [e [He Hsource]]|u|u w v Huw IHuw Hwv IHwv].
  - destruct (reducible_parent v e Hready He) as [Hedge [Htarget _]].
    exists [e]; split.
    + rewrite <- Hsource, <- Htarget; constructor; [exact Hedge|constructor].
    + intros a [Heq|Hin]; [subst a; rewrite Htarget; exact He|contradiction].
  - exists []; split; [constructor|intros e Hin; contradiction].
  - destruct IHuw as [es [Hes Htree]], IHwv as [fs [Hfs Htree']].
    exists (es ++ fs); split; [eapply reducible_path_app; eauto|].
    intros e Hin; apply in_app_iff in Hin; destruct Hin; auto.
Qed.

Lemma reducible_tree_path_ancestor u es v : path g u es v ->
  (forall e, In e es -> Map.get EV (Graph.target g e) (tree_edge R) = Some e) ->
  dfs_ancestor EV g R u v /\
    forall e, In e es -> dfs_ancestor EV g R (Graph.target g e) v.
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Htree.
  - split; [apply rt_refl|intros e Hin; contradiction].
  - destruct (IH ltac:(intros a Ha; apply Htree; right; exact Ha)) as [Hanc Htargets].
    split.
    + eapply rt_trans; [apply rt_step; exists e; split; [apply Htree; left|]; reflexivity|].
      exact Hanc.
    + intros a [Heq|Hin]; [subst a; exact Hanc|apply Htargets; exact Hin].
Qed.

Lemma reducible_root_path v : ready EV g p -> reachable g v ->
  exists s es, In s (Graph.entries g) /\ path g s es v /\
    forall e, In e es -> Map.get EV (Graph.target g e) (tree_edge R) = Some e.
Proof.
  intros Hready Hv; pose proof Hready as [Hwf _].
  apply (proj2 (reachable_dfs EV g p v Hready)) in Hv.
  destruct (dfs_final_spec EV g p FinSet.empty (Graph.entries g) Hready (entries_in Hwf))
    as [Hinv [Hlabels _]].
  unfold dfs in Hv; cbn [visited] in Hv.
  apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hv.
  destruct (dfs_ancestry_root EV g (Graph.entries g) _ v Hlabels Hv)
    as [s [Hroot Hanc]].
  change (dfs_ancestor EV g R s v) in Hanc.
  destruct (reducible_ancestor_path s v Hready Hanc) as [es [Hpath Htree]].
  exists s, es; auto.
Qed.

Lemma reducible_dominates_ancestor d v : ready EV g p -> reachable g v ->
  dominates g d v -> dfs_ancestor EV g R d v.
Proof.
  intros Hready Hv Hdom.
  destruct (reducible_root_path v Hready Hv) as [s [es [Hroot [Hpath Htree]]]].
  destruct (reducible_tree_path_ancestor s es v Hpath Htree) as [Hanc Htargets].
  destruct (Hdom s es Hroot Hpath) as [Heq|[e [Hin Heq]]].
  - subst d; exact Hanc.
  - subst d; apply Htargets; exact Hin.
Qed.

Lemma reducible_ancestor_rank u v : ready EV g p -> dfs_ancestor EV g R u v ->
  forall a, Map.get EV u (pre_num R) = Some a ->
    exists b, Map.get EV v (pre_num R) = Some b /\ Pos.le a b.
Proof.
  intros Hready Hanc; induction Hanc as [u v [e [He Hsource]]|u|u w v Huw IHuw Hwv IHwv];
    intros a Ha.
  - destruct (reducible_parent v e Hready He) as [_ [_ [c [d [Hc [Hd Hlt]]]]]].
    rewrite Hsource, Ha in Hc; inversion Hc; subst c.
    exists d; split; [exact Hd|apply Pos.lt_le_incl; exact Hlt].
  - exists a; split; [exact Ha|apply Pos.le_refl].
  - destruct (IHuw a Ha) as [b [Hb Hab]].
    destruct (IHwv b Hb) as [c [Hc Hbc]].
    exists c; split; [exact Hc|eapply Pos.le_trans; eauto].
Qed.

(** A dominance back edge always returns to a DFS ancestor of its source. *)
Theorem back_edge_retreating e : ready EV g p -> back_edge g e -> retreating EV g R e.
Proof.
  intros Hready [_ [Hreach Hdom]].
  exact (reducible_dominates_ancestor _ _ Hready Hreach Hdom).
Qed.

Lemma reducible_parent_not_back e : ready EV g p ->
  Map.get EV (Graph.target g e) (tree_edge R) = Some e -> ~ back_edge g e.
Proof.
  intros Hready He Hback.
  destruct (reducible_parent _ e Hready He) as [_ [_ [a [b [Ha [Hb Hlt]]]]]].
  pose proof (back_edge_retreating e Hready Hback) as Hanc.
  destruct (reducible_ancestor_rank _ _ Hready Hanc b Hb) as [c [Hc Hle]].
  rewrite Ha in Hc; inversion Hc; subst c.
  apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; lia.
Qed.

Lemma reducible_path_edge u es v : path g u es v -> reachable g u ->
  forall e, In e es -> In e (Graph.out g (Graph.source g e)) /\
    reachable g (Graph.source g e).
Proof.
  intro Hpath; induction Hpath as [v|a es v Hedge Hpath IH]; intros Hreach e Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; auto.
    + apply IH; [eapply reachable_step; eauto|exact Hin].
Qed.

(** The cycle definition is equivalent to requiring every reachable retreating edge to be back. *)
Theorem reducible_iff_retreating_back : ready EV g p ->
  (reducible g <-> forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) -> retreating EV g R e -> back_edge g e).
Proof.
  intro Hready; split.
  - intros Hreducible e Hedge Hreach Hretreat.
    destruct (reducible_ancestor_path _ _ Hready Hretreat) as [es [Hpath Htree]].
    assert (Hcycle : path g (Graph.target g e) (es ++ [e]) (Graph.target g e)).
    { eapply reducible_path_app; [exact Hpath|constructor; [exact Hedge|constructor]]. }
    assert (Hnonempty : es ++ [e] <> []).
    { intro Hnil; apply app_eq_nil in Hnil; destruct Hnil as [_ Hnil]; discriminate. }
    destruct (Hreducible _ _ (reachable_step e Hreach Hedge) Hnonempty Hcycle)
      as [a [Hin Hback]].
    apply in_app_iff in Hin; destruct Hin as [Hin|[Heq|Hin]].
    + exfalso; apply (reducible_parent_not_back a Hready (Htree a Hin)); exact Hback.
    + subst a; exact Hback.
    + contradiction.
  - intros Hback v es Hreach Hnonempty Hpath.
    destruct (cycle_has_retreating_edge EV g p v es (Graph.entries g) Hready
      (entries_in (proj1 Hready)) (proj2 (reachable_dfs EV g p v Hready) Hreach)
      Hnonempty Hpath) as [e [Hin Hretreat]].
    exists e; split; [exact Hin|].
    destruct (reducible_path_edge _ _ _ Hpath Hreach e Hin) as [Hedge Hsource].
    apply Hback; assumption.
Qed.

Lemma reducible_preorder v : ready EV g p -> (In v (preorder R) <-> reachable g v).
Proof.
  intro Hready.
  destruct (dfs_exact EV g p v (Graph.entries g) FinSet.empty Hready
    (entries_in (proj1 Hready))) as [_ [_ [_ Hin]]].
  rewrite Hin; apply reachable_dfs; exact Hready.
Qed.

Lemma reducible_b_edges t : ready EV g p ->
  (reducible_b p t = true <-> forall e, In e (Graph.out g (Graph.source g e)) ->
    reachable g (Graph.source g e) -> retreating EV g R e ->
    dominates_b EV t (Graph.target g e) (Graph.source g e) = true).
Proof.
  intro Hready; pose proof Hready as [Hwf [_ Hlaws]].
  unfold reducible_b; rewrite forallb_forall; split.
  - intros Htests e Hedge Hsource Hretreat.
    specialize (Htests _ (proj2 (reducible_preorder _ Hready) Hsource)).
    apply forallb_forall with (x := e) in Htests.
    + assert (Htarget : reachable g (Graph.target g e)) by (eapply reachable_step; eauto).
      assert (Hancestor : ancestor_b EV R (Graph.target g e) (Graph.source g e) = true).
      { apply (proj2 (ancestor_b_agrees EV g p _ _ (Graph.entries g) FinSet.empty
          Hready (entries_in Hwf)
          (proj2 (reachable_dfs EV g p _ Hready) Htarget)
          (proj2 (reachable_dfs EV g p _ Hready) Hsource))); exact Hretreat. }
      rewrite Hancestor in Htests; exact Htests.
    + rewrite (succ_agrees Hlaws _ (reachable_in_nodes g _ Hwf Hsource)); exact Hedge.
  - intros Htests v Hv; apply forallb_forall; intros e He.
    apply (reducible_preorder v Hready) in Hv.
    rewrite (succ_agrees Hlaws v (reachable_in_nodes g v Hwf Hv)) in He.
    pose proof (out_source Hwf v e He) as Hsource.
    assert (Hedge : In e (Graph.out g (Graph.source g e))) by (rewrite Hsource; exact He).
    assert (Hs : reachable g (Graph.source g e)) by (rewrite Hsource; exact Hv).
    destruct (ancestor_b EV R (Graph.target g e) (Graph.source g e)) eqn:Hancestor;
      cbn; [|reflexivity].
    apply Htests; [exact Hedge|exact Hs|].
    apply (proj1 (ancestor_b_agrees EV g p _ _ (Graph.entries g) FinSet.empty Hready
      (entries_in Hwf)
      (proj2 (reachable_dfs EV g p _ Hready) (reachable_step e Hs Hedge))
      (proj2 (reachable_dfs EV g p _ Hready) Hs))); exact Hancestor.
Qed.

(** Acceptance with the total dominator tree implies semantic reducibility. *)
Theorem reducible_b_sound : ready EV g p ->
  reducible_b p (dominator_tree p) = true -> reducible g.
Proof.
  intros Hready Htest.
  apply (proj2 (reducible_iff_retreating_back Hready)).
  intros e Hedge Hreach Hretreat; split; [exact Hedge|]; split; [exact Hreach|].
  destruct (dominator_tree_sound EV g p Hready) as [_ [_ [Hsound _]]].
  apply Hsound; apply (proj1 (reducible_b_edges _ Hready) Htest e); assumption.
Qed.

(** With an exact dominator tree the test decides semantic reducibility. *)
Theorem reducible_b_correct : ready EV g p -> dominator_exact p = true ->
  (reducible_b p (dominator_tree p) = true <-> reducible g).
Proof.
  intros Hready Hexact; split; [apply reducible_b_sound; exact Hready|].
  intro Hreducible; apply (proj2 (reducible_b_edges _ Hready)).
  intros e Hedge Hreach Hretreat.
  destruct (proj1 (reducible_iff_retreating_back Hready) Hreducible e Hedge Hreach Hretreat)
    as [_ [_ Hdom]].
  destruct (dominator_tree_exact EV g p Hready Hexact) as [Hdominance _].
  apply (proj2 (Hdominance _ _ Hreach)); exact Hdom.
Qed.

End Reducibility.
