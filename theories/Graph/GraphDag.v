(** * Acyclic orders and maximum paths

    DFS intervals detect cycles and reverse postorder schedules maximum-weight relaxation.
    For example, two routes to a join retain the heavier route and its final edge.
    Builds on: GraphCore, GraphPrepare, GraphDfs, GraphCertificate and GraphScc. *)

From Stdlib Require Import List Bool PArith ZArith Lia Relations.Relation_Operators.
From Stdlib.Sorting Require Import Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphCertificate GraphScc.
Import List.ListNotations.

(** Check the indexed outgoing edges of precisely the visited vertices. *)
Definition dag_search_ok {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : bool :=
  forallb (fun v => forallb (fun e =>
    negb (ancestor_b EV r (Graph.target g e) (Graph.source g e)))
    (succ_edges p v)) (preorder r).

(** Sort all nodes, including components unreachable from the entries. *)
Definition topological_sort {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : option (list V) :=
  let r := dfs p FinSet.empty (Graph.nodes g) in
  if dag_search_ok p r then Some (rpo r) else None.

(** Sum signed edge weights, with zero for the empty path. *)
Definition path_weight {E} (w : E -> Z) (es : list E) : Z :=
  fold_right (fun e acc => (w e + acc)%Z) 0%Z es.

(** Distances and selected incoming edges describe maximum entry paths. *)
Record dag_paths (V E : Type) : Type := DagPaths {
  best : Map.t V Z;
  via : Map.t V E
}.

Arguments DagPaths {V E}.
Arguments best {V E}.
Arguments via {V E}.

Section DagOrder.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).

Lemma dag_forallb_false {A} (f : A -> bool) xs :
  forallb f xs = false -> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; cbn; [discriminate|].
  destruct (f x) eqn:Hx; cbn.
  - intro H; destruct (IH H) as [y [Hy Hf]]; exists y; auto.
  - intros _; exists x; auto.
Qed.

Lemma dag_rpo_members roots v : ready EV g p -> incl roots (Graph.nodes g) ->
  (In v (rpo (dfs p FinSet.empty roots)) <->
   FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true).
Proof.
  intros Hready Hroots.
  destruct (dfs_exact EV g p v roots FinSet.empty Hready Hroots)
    as [_ [_ [Hperm Hin]]].
  unfold rpo; rewrite <- in_rev.
  split; intro Hv.
  - apply Hin; eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hv].
  - eapply Permutation_in; [exact Hperm|apply Hin; exact Hv].
Qed.

Lemma dag_pre_nodes roots v : ready EV g p -> incl roots (Graph.nodes g) ->
  In v (preorder (dfs p FinSet.empty roots)) -> In v (Graph.nodes g).
Proof.
  intros Hready Hroots Hv; destruct Hready as [Hwf [Hout Hp]].
  destruct (dfs_exact EV g p v roots FinSet.empty (conj Hwf (conj Hout Hp)) Hroots)
    as [Hex [_ [_ Hin]]].
  apply Hin, Hex in Hv; apply dfs_empty_reachable in Hv.
  apply (reachable_in_nodes (set_entries g roots) v); [|exact Hv].
  destruct Hwf; constructor; cbn; assumption.
Qed.

Lemma dag_root_visited roots v : ready EV g p -> incl roots (Graph.nodes g) ->
  In v roots -> FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true.
Proof.
  intros Hready Hroots Hv.
  destruct (dfs_exact EV g p v roots FinSet.empty Hready Hroots) as [Hex _].
  apply Hex, dfs_empty_reachable, reachable_entry; exact Hv.
Qed.

Lemma dag_ancestor_path roots u v : ready EV g p -> incl roots (Graph.nodes g) ->
  dfs_ancestor EV g (dfs p FinSet.empty roots) u v -> exists es, path g u es v.
Proof.
  intros Hready Hroots Hanc.
  destruct (dfs_final_spec EV g p FinSet.empty roots Hready Hroots)
    as [_ [Hlabels _]].
  induction Hanc as [u v [e [He Hsource]]|u|u z v Huz IHuz Hzv IHzv].
  - unfold dfs in He; cbn [tree_edge] in He.
    destruct (dfs_parent_labels _ _ _ _ Hlabels v e He)
      as [_ [_ [Hedge [Htarget _]]]].
    exists [e]; rewrite <- Hsource, <- Htarget; constructor; [exact Hedge|constructor].
  - exists []; constructor.
  - destruct IHuz as [es Hes], IHzv as [fs Hfs].
    exists (es ++ fs); eapply tarjan_path_append; eassumption.
Qed.

Lemma dag_retreat_cycle roots e : ready EV g p -> incl roots (Graph.nodes g) ->
  In e (Graph.out g (Graph.source g e)) ->
  retreating EV g (dfs p FinSet.empty roots) e ->
  exists es, es <> [] /\ path g (Graph.source g e) es (Graph.source g e).
Proof.
  intros Hready Hroots Hedge Hback.
  destruct (dag_ancestor_path roots _ _ Hready Hroots Hback) as [es Hpath].
  exists (e :: es); split; [discriminate|constructor; assumption].
Qed.

Lemma dag_search_ok_correct roots : ready EV g p -> incl roots (Graph.nodes g) ->
  (dag_search_ok p (dfs p FinSet.empty roots) = true <->
   forall e, FinSet.mem EV (Graph.source g e)
       (visited (dfs p FinSet.empty roots)) = true ->
     In e (Graph.out g (Graph.source g e)) ->
     ~ retreating EV g (dfs p FinSet.empty roots) e).
Proof.
  intros Hready Hroots; pose proof Hready as [Hwf [_ Hp]].
  unfold dag_search_ok; rewrite forallb_forall.
  split.
  - intros Hcheck e Hsource Hedge Hback.
    destruct (dfs_exact EV g p (Graph.source g e) roots FinSet.empty Hready Hroots)
      as [_ [_ [_ Hin]]].
    pose proof (Hcheck _ (proj2 Hin Hsource)) as Hv.
    rewrite forallb_forall in Hv.
    assert (Hnode : In (Graph.source g e) (Graph.nodes g)).
    { apply dag_pre_nodes with roots; [exact Hready|exact Hroots|apply Hin; exact Hsource]. }
    rewrite (succ_agrees Hp _ Hnode) in Hv.
    specialize (Hv e Hedge); apply negb_true_iff in Hv.
    pose proof (dfs_visited_edge EV g p roots e Hready Hroots Hsource Hedge) as Htarget.
    apply (proj2 (ancestor_b_agrees EV g p _ _ roots FinSet.empty Hready Hroots
      Htarget Hsource)) in Hback; congruence.
  - intros Hback v Hv; rewrite forallb_forall; intros e He.
    pose proof (dag_pre_nodes roots v Hready Hroots Hv) as Hnode.
    rewrite (succ_agrees Hp _ Hnode) in He.
    pose proof (out_source Hwf _ _ He) as Hsource; subst v.
    destruct (dfs_exact EV g p (Graph.source g e) roots FinSet.empty Hready Hroots)
      as [_ [_ [_ Hin]]].
    apply Hin in Hv.
    pose proof (dfs_visited_edge EV g p roots e Hready Hroots Hv He) as Htarget.
    apply negb_true_iff; destruct (ancestor_b EV (dfs p FinSet.empty roots)
      (Graph.target g e) (Graph.source g e)) eqn:Htest; [|reflexivity].
    exfalso; apply (Hback e Hv He).
    apply (proj1 (ancestor_b_agrees EV g p _ _ roots FinSet.empty Hready Hroots
      Htarget Hv)); exact Htest.
Qed.

Lemma dag_search_failure roots : ready EV g p -> incl roots (Graph.nodes g) ->
  dag_search_ok p (dfs p FinSet.empty roots) = false ->
  exists v es, FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true /\
    es <> [] /\ path g v es v.
Proof.
  intros Hready Hroots Hfalse; pose proof Hready as [Hwf [_ Hp]].
  unfold dag_search_ok in Hfalse; apply dag_forallb_false in Hfalse.
  destruct Hfalse as [v [Hv He]]; apply dag_forallb_false in He.
  destruct He as [e [He Hback]].
  pose proof (dag_pre_nodes roots v Hready Hroots Hv) as Hnode.
  rewrite (succ_agrees Hp _ Hnode) in He.
  pose proof (out_source Hwf _ _ He) as Hsource; subst v.
  destruct (dfs_exact EV g p (Graph.source g e) roots FinSet.empty Hready Hroots)
    as [_ [_ [_ Hin]]]; apply Hin in Hv.
  pose proof (dfs_visited_edge EV g p roots e Hready Hroots Hv He) as Htarget.
  apply negb_false_iff in Hback.
  apply (proj1 (ancestor_b_agrees EV g p _ _ roots FinSet.empty Hready Hroots
    Htarget Hv)) in Hback.
  destruct (dag_retreat_cycle roots e Hready Hroots He Hback) as [es [Hne Hpath]].
  exists (Graph.source g e), es; auto.
Qed.

Lemma dag_order_path l : NoDup l ->
  (forall e, In (Graph.source g e) l -> In e (Graph.out g (Graph.source g e)) ->
    before l (Graph.source g e) (Graph.target g e)) ->
  forall u es v, path g u es v -> In u l -> es = [] \/ before l u v.
Proof.
  intros Hnd Hedges u es v Hpath; induction Hpath as [v|e es v He Hpath IH]; intro Hu.
  - left; reflexivity.
  - pose proof (Hedges e Hu He) as Hbefore.
    assert (Hin : In (Graph.target g e) l).
    { destruct Hbefore as [a [b [c ->]]]; apply in_or_app; right; cbn; right.
      apply in_or_app; right; left; reflexivity. }
    destruct (IH Hin) as [Hnil|Htail].
    + subst es; inversion Hpath; subst; right; exact Hbefore.
    + right; eapply dfs_before_trans; eassumption.
Qed.

(** A topological sort exists exactly when the graph is acyclic. *)
Theorem topological_sort_correct : ready EV g p ->
  (forall l, topological_sort p = Some l -> topological_order g l) /\
  (topological_sort p = None <-> ~ acyclic g).
Proof.
  intro Hready; pose proof Hready as [Hwf [_ Hp]].
  assert (Hroots : incl (Graph.nodes g) (Graph.nodes g)) by (intros x Hx; exact Hx).
  assert (Hmembers : forall v, In v (rpo (dfs p FinSet.empty (Graph.nodes g))) <->
    In v (Graph.nodes g)).
  { intro v; rewrite (dag_rpo_members _ v Hready Hroots); split.
    - intro Hv; destruct (dfs_exact EV g p v _ FinSet.empty Hready Hroots)
        as [_ [_ [_ Hin]]].
      apply dag_pre_nodes with (Graph.nodes g); [exact Hready|exact Hroots|apply Hin; exact Hv].
    - apply dag_root_visited; assumption. }
  assert (Hsound : forall l, topological_sort p = Some l -> topological_order g l).
  { intros l Hsort; unfold topological_sort in Hsort.
    destruct (dag_search_ok p (dfs p FinSet.empty (Graph.nodes g))) eqn:Hok;
      [inversion Hsort; subst l|discriminate].
    split; [apply dfs_rpo_nodup; assumption|]; split; [exact Hmembers|].
    intros e Hnode Hedge.
    pose proof (dag_root_visited _ _ Hready Hroots Hnode) as Hv.
    destruct (rpo_edge_classes EV g p _ Hready Hroots e Hv Hedge) as [Hbefore|Hback].
    - exact Hbefore.
    - exfalso; apply (proj1 (dag_search_ok_correct _ Hready Hroots) Hok e Hv Hedge Hback). }
  split; [exact Hsound|]; split.
  - intros Hnone Hacyclic; unfold topological_sort in Hnone.
    destruct (dag_search_ok p (dfs p FinSet.empty (Graph.nodes g))) eqn:Hok;
      [discriminate|].
    destruct (dag_search_failure _ Hready Hroots Hok) as [v [es [Hv [Hne Hpath]]]].
    apply Hne, Hacyclic with v; [apply Hmembers, dag_rpo_members; eassumption|exact Hpath].
  - intro Hnot; destruct (topological_sort p) as [l|] eqn:Hsort; [|reflexivity].
    exfalso; apply Hnot; destruct (Hsound l eq_refl) as [Hnd [Hmem Hedges]].
    intros v es Hv Hpath.
    destruct (dag_order_path l Hnd ltac:(intros e He; apply Hedges; apply Hmem; exact He)
      v es v Hpath (proj2 (Hmem v) Hv)) as [Hnil|Hbefore]; [exact Hnil|].
    exfalso; exact (dfs_before_irrefl l v Hnd Hbefore).
Qed.

End DagOrder.

(** * Dynamic programming *)

(** Keep the incumbent on ties, including an empty entry path of equal weight. *)
Definition dag_offer {E} (b : Z) (e : option E) (old : option (Z * option E)) :=
  match old with
  | None => Some (b, e)
  | Some (a, via_) => if Z.leb b a then old else Some (b, e)
  end.

(** Read each incoming edge once, using the already settled predecessor distances. *)
Fixpoint dag_incoming {V E} (EV : encoding V) (g : Graph.t V E) (w : E -> Z)
    (r : dag_paths V E) (es : list E) (initial : option (Z * option E)) :=
  match es with
  | [] => initial
  | e :: rest =>
    let old := dag_incoming EV g w r rest initial in
    match Map.get EV (Graph.source g e) (best r) with
    | None => old
    | Some a => dag_offer (a + w e)%Z (Some e) old
    end
  end.

(** Write one distance and clear a previous final edge when the empty route wins. *)
Definition dag_write {V E} (EV : encoding V) (r : dag_paths V E) (v : V)
    (b : Z) (edge : option E) : dag_paths V E :=
  DagPaths (Map.set EV v b (best r))
    (match edge with
    | None => Map.remove EV v (via r)
    | Some e => Map.set EV v e (via r)
    end).

(** Set one vertex after all its predecessors have been settled. *)
Definition dag_vertex {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (entries : FinSet.t V) (w : E -> Z) (r : dag_paths V E) (v : V) :=
  let initial := if FinSet.mem EV v entries then Some (0%Z, None) else None in
  match dag_incoming EV g w r (pred_edges p v) initial with
  | None => r
  | Some (b, edge) => dag_write EV r v b edge
  end.

(** Maximum paths use the entry search only, allowing unreachable cycles. *)
Definition max_paths {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (w : E -> Z) : option (dag_paths V E) :=
  let search := dfs p FinSet.empty (Graph.entries g) in
  if dag_search_ok p search then
    Some (fold_left (dag_vertex p (FinSet.of_list EV (Graph.entries g)) w)
      (rpo search) (DagPaths Map.empty Map.empty))
  else None.

(** Reuse the binary parent walker to recover the selected final-edge chain. *)
Definition max_path_to {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dag_paths V E) (v : V) : option (V * list E) :=
  match Map.get EV v (best r) with
  | None => None
  | Some _ =>
    let tree := DfsResult [] [] (via r) Map.empty Map.empty FinSet.empty in
    let '(done_, s, es) := tree_path_run (EV := EV) (g := g) tree (fuel p) (false, v, []) in
    if done_ then Some (s, es) else None
  end.

(** A route records the same final edges followed by witness recovery. *)
Inductive dag_route {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dag_paths V E) (done_ : list V) : V -> V -> list E -> Prop :=
  | dag_route_root : forall s, In s done_ -> In s (Graph.entries g) ->
      Map.get EV s (via r) = None -> dag_route EV g r done_ s s []
  | dag_route_edge : forall s u es e, dag_route EV g r done_ u s es ->
      In (Graph.target g e) done_ -> Graph.source g e = u ->
      In e (Graph.out g u) -> Map.get EV (Graph.target g e) (via r) = Some e ->
      dag_route EV g r done_ (Graph.target g e) s (es ++ [e]).

Section DagPaths.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
  (w : E -> Z).

Lemma dag_offer_correct b (e : option E) old :
  (forall a edge, dag_offer b e old = Some (a, edge) ->
    (a = b /\ edge = e) \/ old = Some (a, edge)) /\
  (forall a edge, dag_offer b e old = Some (a, edge) -> (b <= a)%Z) /\
  (forall a edge c ce, old = Some (c, ce) -> dag_offer b e old = Some (a, edge) ->
    (c <= a)%Z) /\ dag_offer b e old <> None.
Proof.
  unfold dag_offer; destruct old as [[c ce]|].
  - destruct (Z.leb b c) eqn:Hle.
    + apply Z.leb_le in Hle; split.
      * intros a edge H; right; exact H.
      * split; [intros a edge H; inversion H; subst; exact Hle|].
        split; [intros a edge d de Hd Ha; inversion Hd; inversion Ha; subst; lia|discriminate].
    + apply Z.leb_gt in Hle; split.
      * intros a edge H; inversion H; subst; left; auto.
      * split; [intros a edge H; inversion H; subst; lia|].
        split; [intros a edge d de Hd Ha; inversion Hd; inversion Ha; subst; lia|discriminate].
  - split.
    + intros a edge H; inversion H; subst; left; auto.
    + split; [intros a edge H; inversion H; subst; lia|].
      split; [intros a edge c ce H; discriminate|discriminate].
Qed.

Definition dag_candidate (r : dag_paths V E) es initial b edge : Prop :=
  initial = Some (b, edge) \/ exists e a,
    In e es /\ Map.get EV (Graph.source g e) (best r) = Some a /\
    b = (a + w e)%Z /\ edge = Some e.

Lemma dag_incoming_correct r es initial :
  (forall b edge, dag_incoming EV g w r es initial = Some (b, edge) ->
    dag_candidate r es initial b edge) /\
  (forall b edge, dag_candidate r es initial b edge ->
    exists a ae, dag_incoming EV g w r es initial = Some (a, ae) /\ (b <= a)%Z).
Proof.
  induction es as [|e es IH]; cbn [dag_incoming].
  - split.
    + intros b edge H; left; exact H.
    + intros b edge [H|[a [c [Hfalse _]]]]; [exists b, edge; auto with zarith|contradiction].
  - destruct IH as [Hsound Hupper].
    destruct (Map.get EV (Graph.source g e) (best r)) as [a|] eqn:Ha.
    + destruct (dag_offer_correct (a + w e)%Z (Some e)
        (dag_incoming EV g w r es initial)) as [Hpick [Hnew [Hold Hsome]]].
      split.
      * intros b edge Hb; destruct (Hpick b edge Hb) as [[-> ->]|Htail].
        -- right; exists e, a; exact (conj (or_introl eq_refl)
             (conj Ha (conj eq_refl eq_refl))).
        -- destruct (Hsound _ _ Htail) as [Hinit|[f [c [Hf [Hc [Heq Hedge]]]]]].
           ++ left; exact Hinit.
           ++ right; exists f, c; exact (conj (or_intror Hf)
                (conj Hc (conj Heq Hedge))).
      * intros b edge [Hinit|[f [c [[Hfe|Hf] [Hc [-> ->]]]]]].
        -- destruct (Hupper b edge (or_introl Hinit)) as [d [de [Hd Hbd]]].
           destruct (dag_offer (a + w e)%Z (Some e) (dag_incoming EV g w r es initial))
             as [[z ze]|] eqn:Hz; [exists z, ze; split; [reflexivity|]|contradiction].
           specialize (Hold z ze d de Hd eq_refl); lia.
        -- subst f; rewrite Ha in Hc; inversion Hc; subst c.
           destruct (dag_offer (a + w e)%Z (Some e) (dag_incoming EV g w r es initial))
             as [[z ze]|] eqn:Hz.
           ++ exists z, ze; split; [reflexivity|apply Hnew with ze; reflexivity].
           ++ contradiction.
        -- destruct (Hupper (c + w f)%Z (Some f)
             (or_intror (ex_intro _ f (ex_intro _ c (conj Hf (conj Hc (conj eq_refl eq_refl)))))))
             as [d [de [Hd Hbd]]].
           destruct (dag_offer (a + w e)%Z (Some e) (dag_incoming EV g w r es initial))
             as [[z ze]|] eqn:Hz; [exists z, ze; split; [reflexivity|]|contradiction].
           specialize (Hold z ze d de Hd eq_refl); lia.
    + split.
      * intros b edge Hb; destruct (Hsound _ _ Hb) as [H|[f [c [Hf Hrest]]]].
        -- left; exact H.
        -- right; exists f, c; split; [right; exact Hf|exact Hrest].
      * intros b edge [H|[f [c [[Hfe|Hf] Hrest]]]].
        -- apply (Hupper b edge); left; exact H.
        -- subst f; destruct Hrest as [Hc _]; congruence.
        -- apply (Hupper b edge); right; exists f, c; exact (conj Hf Hrest).
Qed.

Lemma dag_route_transport r done_ r' done' v s es : dag_route EV g r done_ v s es ->
  incl done_ done' ->
  (forall x, In x done_ -> Map.get EV x (via r') = Map.get EV x (via r)) ->
  dag_route EV g r' done' v s es.
Proof.
  intro Hroute; induction Hroute as [s Hs Hentry Hnone|s u es e Hroute IH Ht Hsrc He Hvia];
    intros Hin Heq.
  - constructor; [apply Hin; exact Hs|exact Hentry|rewrite Heq; assumption].
  - econstructor; [apply IH; assumption|apply Hin; exact Ht|exact Hsrc|exact He|].
    rewrite Heq; assumption.
Qed.

Lemma dag_route_path r done_ v s es : dag_route EV g r done_ v s es ->
  In s (Graph.entries g) /\ path g s es v.
Proof.
  intro Hroute; induction Hroute as [s Hs Hentry Hnone|s u es e Hroute [Hs Hp] Ht Hsrc He Hvia].
  - split; [exact Hentry|constructor].
  - split; [exact Hs|eapply path_snoc; [exact Hp|symmetry; exact Hsrc|exact He]].
Qed.

Lemma dag_path_weight_app es fs : path_weight w (es ++ fs) =
  (path_weight w es + path_weight w fs)%Z.
Proof.
  induction es as [|e es IH].
  - change (path_weight w fs = (0 + path_weight w fs)%Z); lia.
  - change ((w e + path_weight w (es ++ fs))%Z =
      (w e + path_weight w es + path_weight w fs)%Z).
    rewrite IH; lia.
Qed.

Lemma dag_path_last s es v : path g s es v -> es <> [] ->
  exists prefix e, es = prefix ++ [e] /\ path g s prefix (Graph.source g e) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v.
Proof.
  intro Hpath; induction Hpath as [v|e es v He Hpath IH]; intro Hne; [contradiction|].
  destruct es as [|a es].
  - inversion Hpath; subst; exists [], e; repeat split; [constructor|exact He].
  - destruct (IH ltac:(discriminate)) as [prefix [f [Hparts [Hp [Hf Ht]]]]].
    exists (e :: prefix), f; split; [cbn; congruence|].
    split; [constructor; assumption|auto].
Qed.

Lemma dag_iter_step {A} (f : A -> A) n x : Pos.iter f (f x) n = f (Pos.iter f x n).
Proof.
  induction n using Pos.peano_ind; [reflexivity|rewrite !Pos.iter_succ, IHn; reflexivity].
Qed.

Lemma dag_route_walk r done_ v s es : dag_route EV g r done_ v s es ->
  forall n acc, length es < Pos.to_nat n ->
  Pos.iter (tree_path_step (EV := EV) (g := g)
    (DfsResult [] [] (via r) Map.empty Map.empty FinSet.empty)) (false, v, acc) n =
    (true, s, es ++ acc).
Proof.
  intro Hroute; induction Hroute as [s Hs Hentry Hnone|s u es e Hroute IH Ht Hsrc He Hvia].
  - intros n acc Hbound; induction n using Pos.peano_ind.
    + cbn [Pos.iter tree_path_step tree_edge]; rewrite Hnone; reflexivity.
    + rewrite Pos.iter_succ, IHn by (pose proof (Pos2Nat.is_pos n); cbn; lia).
      reflexivity.
  - intros n acc Hbound; induction n using Pos.peano_ind.
    + cbn in Hbound; rewrite length_app in Hbound; cbn in Hbound; lia.
    + rewrite Pos.iter_succ, <- dag_iter_step.
      cbn [tree_path_step tree_edge]; rewrite Hvia, Hsrc.
      rewrite IH by (rewrite length_app, Pos2Nat.inj_succ in Hbound; cbn in Hbound; lia).
      rewrite <- app_assoc; reflexivity.
Qed.

Lemma dag_route_recover r done_ v s es b :
  Map.get EV v (best r) = Some b -> dag_route EV g r done_ v s es ->
  length es < Pos.to_nat (fuel p) -> max_path_to p r v = Some (s, es).
Proof.
  intros Hb Hroute Hbound; unfold max_path_to; rewrite Hb, tree_path_run_agrees.
  rewrite (dag_route_walk r done_ v s es Hroute (fuel p) [] Hbound), app_nil_r; reflexivity.
Qed.

Lemma dag_before_prefix (done_ : list V) v rest u : NoDup (done_ ++ v :: rest) ->
  before (done_ ++ v :: rest) u v -> In u done_.
Proof.
  induction done_ as [|a done_ IH]; cbn; intros Hnd Hbefore.
  - exfalso; eapply dfs_before_head_false; eassumption.
  - apply dfs_before_cons in Hbefore.
    destruct Hbefore as [[-> Hin]|Hbefore]; [left; reflexivity|].
    right; apply IH; [inversion Hnd; assumption|exact Hbefore].
Qed.

(** The settled prefix has exact weights, bounded routes and no extra distance bindings. *)
Definition dag_valid (done_ : list V) (r : dag_paths V E) : Prop :=
  (forall v, In v done_ <-> exists b, Map.get EV v (best r) = Some b) /\
  (forall v b, Map.get EV v (best r) = Some b ->
    (exists s es, dag_route EV g r done_ v s es /\ path_weight w es = b /\
      length es < length done_) /\
    (forall s es, In s (Graph.entries g) -> path g s es v -> (path_weight w es <= b)%Z)).

Lemma dag_valid_empty : dag_valid [] (DagPaths Map.empty Map.empty : dag_paths V E).
Proof.
  split.
  - intro v; cbn; rewrite Map.get_empty; split; [contradiction|intros [b H]; discriminate].
  - intros v b H; cbn in H; rewrite Map.get_empty in H; discriminate.
Qed.

Lemma dag_write_via_other (r : dag_paths V E) v b edge x : x <> v ->
  Map.get EV x (via (dag_write EV r v b edge)) = Map.get EV x (via r).
Proof.
  intro Hne; destruct edge; cbn [dag_write via];
    [apply Map.get_set_other|apply Map.get_remove_other]; exact Hne.
Qed.

Lemma dag_write_route r done_ v b edge x s es : ~ In v done_ ->
  dag_route EV g r done_ x s es ->
  dag_route EV g (dag_write EV r v b edge) (done_ ++ [v]) x s es.
Proof.
  intros Hfresh Hroute; eapply dag_route_transport; [exact Hroute| |].
  - intros a Ha; apply in_or_app; left; exact Ha.
  - intros a Ha; apply dag_write_via_other; intro Heq; subst a; contradiction.
Qed.

Lemma dag_candidate_route r done_ v b edge initial : ready EV g p ->
  ~ In v done_ -> In v (Graph.nodes g) -> dag_valid done_ r ->
  initial = (if FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))
    then Some (0%Z, None) else None) ->
  dag_candidate r (pred_edges p v) initial b edge ->
  exists s es, dag_route EV g (dag_write EV r v b edge) (done_ ++ [v]) v s es /\
    path_weight w es = b /\ length es < length (done_ ++ [v]).
Proof.
  intros Hready Hfresh Hv [Hdomain Hvalid] -> Hcand.
  destruct Hready as [Hwf [_ Hp]].
  destruct Hcand as [Hinitial|[e [a [He [Ha [-> ->]]]]]].
  - destruct (FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))) eqn:Hentry;
      [inversion Hinitial; subst b edge|discriminate].
    apply FinSet.of_list_spec in Hentry.
    exists v, []; split.
    + constructor; [apply in_or_app; right; left; reflexivity|exact Hentry|].
      cbn [dag_write via]; apply Map.get_remove_same.
    + split; [reflexivity|rewrite length_app; cbn; lia].
  - apply (proj1 (pred_agrees Hp v e Hv)) in He.
    destruct He as [u [Hu [He Htarget]]].
    pose proof (out_source Hwf u e He) as Hsource.
    destruct (Hvalid _ _ Ha) as [[s [es [Hroute [Hweight Hlength]]]] Hmax].
    subst v.
    exists s, (es ++ [e]); split.
    + eapply dag_route_edge with (u := Graph.source g e).
      * apply dag_write_route; [exact Hfresh|exact Hroute].
      * apply in_or_app; right; left; reflexivity.
      * reflexivity.
      * rewrite Hsource; exact He.
      * cbn [dag_write via]; apply Map.get_set_same.
    + split.
      * rewrite dag_path_weight_app, Hweight.
        change ((a + (w e + 0))%Z = (a + w e)%Z); lia.
      * rewrite !length_app; cbn; lia.
Qed.

Lemma dag_path_candidate order done_ v rest r s es :
  NoDup order -> order = done_ ++ v :: rest ->
  (forall x, In x order <-> reachable g x) ->
  (forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before order (Graph.source g e) (Graph.target g e)) ->
  ready EV g p -> dag_valid done_ r -> In s (Graph.entries g) -> path g s es v ->
  exists b edge, dag_candidate r (pred_edges p v)
      (if FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))
       then Some (0%Z, None) else None) b edge /\ (path_weight w es <= b)%Z.
Proof.
  intros Hnd Horder Hmembers Hedges Hready [Hdomain Hvalid] Hentry Hpath.
  pose proof Hready as [Hwf [_ Hp]].
  destruct es as [|a es].
  - inversion Hpath; subst.
    assert (Hin : FinSet.mem EV v (FinSet.of_list EV (Graph.entries g)) = true).
    { apply FinSet.of_list_spec; exact Hentry. }
    exists 0%Z, None; rewrite Hin; split; [left; reflexivity|change (0 <= 0)%Z; lia].
  - destruct (dag_path_last s (a :: es) v Hpath ltac:(discriminate))
      as [prefix [e [Hparts [Hprefix [He Htarget]]]]].
    assert (Hreach : reachable g (Graph.source g e)).
    { apply reachable_iff_path; exists s, prefix; auto. }
    assert (Hdone : In (Graph.source g e) done_).
    { apply (dag_before_prefix done_ v rest); [rewrite <- Horder; exact Hnd|].
      rewrite <- Horder, <- Htarget; apply Hedges; assumption. }
    destruct (proj1 (Hdomain _) Hdone) as [b Hb].
    destruct (Hvalid _ _ Hb) as [_ Hmax].
    exists (b + w e)%Z, (Some e); split.
    + right; exists e, b; split.
      * apply (proj2 (pred_agrees Hp v e
          (reachable_in_nodes g v Hwf ltac:(apply reachable_iff_path; exists s, (a :: es); auto)))).
        exists (Graph.source g e); split; [apply reachable_in_nodes; assumption|auto].
      * exact (conj Hb (conj eq_refl eq_refl)).
    + rewrite Hparts, dag_path_weight_app.
      change ((path_weight w prefix + (w e + 0) <= b + w e)%Z).
      specialize (Hmax s prefix Hentry Hprefix); lia.
Qed.

Lemma dag_vertex_valid order done_ v rest r :
  NoDup order -> order = done_ ++ v :: rest ->
  (forall x, In x order <-> reachable g x) ->
  (forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before order (Graph.source g e) (Graph.target g e)) ->
  ready EV g p -> dag_valid done_ r ->
  dag_valid (done_ ++ [v]) (dag_vertex p (FinSet.of_list EV (Graph.entries g)) w r v).
Proof.
  intros Hnd Horder Hmembers Hedges Hready Hvalid.
  pose proof Hvalid as [Hdomain Hweights].
  assert (Hv : reachable g v).
  { apply Hmembers; rewrite Horder; apply in_or_app; right; left; reflexivity. }
  assert (Hfresh : ~ In v done_).
  { intro Hin; apply (dfs_before_irrefl order v Hnd).
    rewrite Horder; apply tarjan_before_cross; [exact Hin|left; reflexivity]. }
  destruct (proj1 (reachable_iff_path g v) Hv) as [s [es [Hs Hpath]]].
  destruct (dag_path_candidate order done_ v rest r s es Hnd Horder Hmembers
    Hedges Hready Hvalid Hs Hpath) as [c [ce [Hcandidate Hbound]]].
  destruct (dag_incoming_correct r (pred_edges p v)
    (if FinSet.mem EV v (FinSet.of_list EV (Graph.entries g))
     then Some (0%Z, None) else None)) as [Hsound Hupper].
  destruct (Hupper c ce Hcandidate) as [b [edge [Hcompute Hcb]]].
  unfold dag_vertex; rewrite Hcompute.
  assert (Hlookup : forall x, In x done_ ->
    Map.get EV x (best (dag_write EV r v b edge)) = Map.get EV x (best r)).
  { intros x Hx; cbn [dag_write best]; apply Map.get_set_other; intro Heq; subst; contradiction. }
  split.
  - intro x; rewrite in_app_iff; cbn; split.
    + intros [Hx|[Heq|Hfalse]]; [|subst x|contradiction].
      * destruct (proj1 (Hdomain x) Hx) as [a Ha]; exists a; rewrite Hlookup; assumption.
      * exists b; cbn [dag_write best]; apply Map.get_set_same.
    + intros [a Ha]; destruct (dfs_eq_dec EV x v) as [Heq|Hne]; [right; auto|left].
      cbn [dag_write best] in Ha; rewrite Map.get_set_other in Ha by exact Hne.
      apply Hdomain; exists a; exact Ha.
  - intros x a Ha; destruct (dfs_eq_dec EV x v) as [Heq|Hne].
    + subst x; cbn [dag_write best] in Ha; rewrite Map.get_set_same in Ha;
        inversion Ha; subst a.
      split.
      * apply (dag_candidate_route r done_ v b edge _ Hready Hfresh
          (reachable_in_nodes g v (proj1 Hready) Hv) Hvalid eq_refl).
        apply Hsound; exact Hcompute.
      * intros start edges Hentry Hp.
        destruct (dag_path_candidate order done_ v rest r start edges Hnd Horder Hmembers
          Hedges Hready Hvalid Hentry Hp) as [d [de [Hcand Hweight]]].
        destruct (Hupper d de Hcand) as [z [ze [Hz Hdz]]].
        rewrite Hcompute in Hz; inversion Hz; subst; lia.
    + cbn [dag_write best] in Ha; rewrite Map.get_set_other in Ha by exact Hne.
      destruct (Hweights x a Ha) as [[start [edges [Hroute [Hweight Hlength]]]] Hmax].
      split.
      * exists start, edges; split; [apply dag_write_route; assumption|].
        split; [exact Hweight|rewrite length_app; cbn; lia].
      * exact Hmax.
Qed.

Lemma dag_fold_valid order remaining done_ r :
  NoDup order -> order = done_ ++ remaining ->
  (forall x, In x order <-> reachable g x) ->
  (forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before order (Graph.source g e) (Graph.target g e)) ->
  ready EV g p -> dag_valid done_ r ->
  dag_valid order
    (fold_left (dag_vertex p (FinSet.of_list EV (Graph.entries g)) w) remaining r).
Proof.
  revert done_ r; induction remaining as [|v remaining IH];
    intros done_ r Hnd Horder Hmembers Hedges Hready Hvalid.
  - cbn; rewrite app_nil_r in Horder; subst order; exact Hvalid.
  - cbn [fold_left]; apply (IH (done_ ++ [v])).
    + exact Hnd.
    + rewrite <- app_assoc; exact Horder.
    + exact Hmembers.
    + exact Hedges.
    + exact Hready.
    + eapply dag_vertex_valid; eassumption.
Qed.

Lemma dag_reachable_order : ready EV g p ->
  (forall v es, reachable g v -> es <> [] -> ~ path g v es v) ->
  dag_search_ok p (dfs p FinSet.empty (Graph.entries g)) = true /\
  (forall x, In x (rpo (dfs p FinSet.empty (Graph.entries g))) <-> reachable g x) /\
  (forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.source g e) (Graph.target g e)).
Proof.
  intros Hready Hacyclic; pose proof Hready as [Hwf _].
  assert (Hok : dag_search_ok p (dfs p FinSet.empty (Graph.entries g)) = true).
  { destruct (dag_search_ok p (dfs p FinSet.empty (Graph.entries g))) eqn:Htest;
      [reflexivity|].
    destruct (dag_search_failure EV g p _ Hready (entries_in Hwf) Htest)
      as [v [es [Hv [Hne Hpath]]]].
    exfalso; apply (Hacyclic v es).
    - apply reachable_dfs in Hv; eassumption.
    - exact Hne.
    - exact Hpath. }
  split; [exact Hok|]; split.
  - intro x; rewrite (dag_rpo_members EV g p _ x Hready (entries_in Hwf)).
    apply reachable_dfs; exact Hready.
  - intros e Hsource He; apply (proj2 (reachable_dfs EV g p _ Hready)) in Hsource.
    destruct (rpo_edge_classes EV g p _ Hready (entries_in Hwf) e Hsource He)
      as [Hbefore|Hback]; [exact Hbefore|].
    exfalso; apply (proj1 (dag_search_ok_correct EV g p _ Hready (entries_in Hwf))
      Hok e Hsource He Hback).
Qed.

(** Maximum entry-path weights are attained by the paths recovered from final-edge choices. *)
Theorem max_paths_exact : ready EV g p ->
  (forall v es, reachable g v -> es <> [] -> ~ path g v es v) ->
  exists r, max_paths p w = Some r /\ forall v,
    (reachable g v <-> exists b, Map.get EV v (best r) = Some b) /\
    forall b, Map.get EV v (best r) = Some b ->
      (exists s es, max_path_to p r v = Some (s, es) /\ In s (Graph.entries g) /\
        path g s es v /\ path_weight w es = b) /\
      (forall s es, In s (Graph.entries g) -> path g s es v -> (path_weight w es <= b)%Z).
Proof.
  intros Hready Hacyclic; pose proof Hready as [Hwf [_ Hp]].
  destruct (dag_reachable_order Hready Hacyclic) as [Hok [Hmembers Hedges]].
  pose proof (dfs_rpo_nodup EV g p _ Hready (entries_in Hwf)) as Hnd.
  pose proof (dag_fold_valid _ _ [] (DagPaths Map.empty Map.empty) Hnd eq_refl
    Hmembers Hedges Hready dag_valid_empty) as [Hdomain Hvalid].
  eexists; split; [unfold max_paths; rewrite Hok; reflexivity|].
  intro v; split; [rewrite <- Hmembers; apply Hdomain|].
  intros b Hb; destruct (Hvalid v b Hb) as [[s [es [Hroute [Hweight Hlength]]]] Hmax].
  split; [|exact Hmax].
  destruct (dag_route_path _ _ _ _ _ Hroute) as [Hentry Hpath].
  exists s, es; split.
  - eapply dag_route_recover; [exact Hb|exact Hroute|].
    assert (Hinc : incl (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.nodes g)).
    { intros x Hx; apply reachable_in_nodes; [exact Hwf|apply Hmembers; exact Hx]. }
    pose proof (NoDup_incl_length Hnd Hinc) as Hsize.
    rewrite (fuel_value Hp); lia.
  - auto.
Qed.

(** A failed maximum-path computation provides a reachable nonempty cycle. *)
Theorem max_paths_cycle : ready EV g p -> max_paths p w = None ->
  exists v es, reachable g v /\ es <> [] /\ path g v es v.
Proof.
  intros Hready Hnone; pose proof Hready as [Hwf _]; unfold max_paths in Hnone.
  destruct (dag_search_ok p (dfs p FinSet.empty (Graph.entries g))) eqn:Hok;
    [discriminate|].
  destruct (dag_search_failure EV g p _ Hready (entries_in Hwf) Hok)
    as [v [es [Hv [Hne Hpath]]]].
  exists v, es; split; [apply (proj1 (reachable_dfs EV g p v Hready)); exact Hv|auto].
Qed.

End DagPaths.
