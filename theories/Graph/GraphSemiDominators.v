(** * Semidominators and linked-path minima

    Reverse discovery order settles semidominators using indexed predecessors and link/eval.
    For example, the two arms of a diamond give its join the common branch's semidominator.
    Builds on: GraphDfs, GraphDominance and Collections maps. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat Permutation.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance.
Import List.ListNotations.
Import DfsState.

(** * Path specification *)

(** A nonempty semidominator path has all its internal vertices numbered after its endpoint. *)
Definition semidom_path {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (u n : V) : Prop :=
  exists es k h, es <> [] /\ path g u es n /\ Map.get EV n (pre_num r) = Some k /\
    Map.get EV u (pre_num r) = Some h /\
    forall pre e post, es = pre ++ e :: post -> post <> [] ->
      exists j, Map.get EV (Graph.target g e) (pre_num r) = Some j /\ Pos.lt k j.

(** A semidominator has the least discovery number among all semidominator-path starts. *)
Definition semidominator {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (u n : V) : Prop :=
  semidom_path EV g r u n /\
  exists k, Map.get EV u (pre_num r) = Some k /\
    forall v, semidom_path EV g r v n ->
      exists j, Map.get EV v (pre_num r) = Some j /\ Pos.le k j.

(** Both dominator algorithms use discovery order from the same fresh-root search. *)
Definition virtual_dfs {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : dfs_result (V + unit) (E + V) :=
  dfs (virtual_prepared p) FinSet.empty [inr tt].

(** A missing discovery number is used only by the total, defensive malformed-input path. *)
Definition semi_rank {V E} (EV : encoding V) (r : dfs_result V E) (v : V) : positive :=
  match Map.get EV v (pre_num r) with
  | Some k => k
  | None => 1%positive
  end.

(** Choose a minimum while retaining the first argument on equal scores. *)
Definition semi_min {V} (score : V -> positive) (u v : V) : V :=
  if Pos.leb (score u) (score v) then u else v.

Lemma semi_min_member {V} (score : V -> positive) u v :
  semi_min score u v = u \/ semi_min score u v = v.
Proof.
  unfold semi_min; destruct (Pos.leb (score u) (score v)); auto.
Qed.

Lemma semi_min_bounds {V} (score : V -> positive) u v :
  Pos.le (score (semi_min score u v)) (score u) /\
  Pos.le (score (semi_min score u v)) (score v).
Proof.
  unfold semi_min; destruct (Pos.leb (score u) (score v)) eqn:Hle.
  - apply Pos.leb_le in Hle; split; [apply Pos.le_refl|exact Hle].
  - apply Pos.leb_gt in Hle; split; [apply Pos.lt_le_incl; exact Hle|apply Pos.le_refl].
Qed.

(** * Original segments and compressed labels *)

Module SemiLinks.

(** The original links are retained separately from the compressed shortcuts and labels. *)
Record t (V : Type) : Type := Make {
  original : Map.t V V;
  shortcut : Map.t V V;
  labels : Map.t V V
}.
Arguments Make {V}.
Arguments original {V}.
Arguments shortcut {V}.
Arguments labels {V}.

End SemiLinks.
Import SemiLinks.

(** An absent explicit label denotes the vertex itself. *)
Definition semi_label {V} (EV : encoding V) (st : SemiLinks.t V) (v : V) : V :=
  match Map.get EV v (labels st) with
  | Some u => u
  | None => v
  end.

(** A segment lists original-link vertices, including its start and excluding its endpoint. *)
Inductive semi_segment {V} (EV : encoding V) (m : Map.t V V)
    : V -> V -> list V -> Prop :=
  | SemiSegmentNil : forall v, semi_segment EV m v v []
  | SemiSegmentCons : forall v a root xs, Map.get EV v m = Some a ->
      semi_segment EV m a root xs -> semi_segment EV m v root (v :: xs).
Arguments SemiSegmentNil {V EV m} v.
Arguments SemiSegmentCons {V EV m} v a root xs _ _.

(** A minimum names an actual segment member as well as bounding every member's score. *)
Definition semi_minimum {V} (score : V -> positive) (u : V) (xs : list V) : Prop :=
  In u xs /\ forall v, In v xs -> Pos.le (score u) (score v).

(** Every shortcut labels exactly its original segment, and both forests have the same roots. *)
Record semi_links_valid {V} (EV : encoding V) (score : V -> positive)
    (st : SemiLinks.t V) : Prop := {
  semi_roots : forall v, Map.get EV v (shortcut st) = None <->
    Map.get EV v (original st) = None;
  semi_shortcuts : forall v a, Map.get EV v (shortcut st) = Some a ->
    exists xs, xs <> [] /\ semi_segment EV (original st) v a xs /\
      semi_minimum score (semi_label EV st v) xs
}.

Lemma semi_segment_app {V} (EV : encoding V) m u v w xs ys :
  semi_segment EV m u v xs -> semi_segment EV m v w ys ->
  semi_segment EV m u w (xs ++ ys).
Proof.
  intros Hfirst Hlast; induction Hfirst as [u|u a v xs Hlink Hsegment IH].
  - exact Hlast.
  - cbn [app]; eapply SemiSegmentCons; [exact Hlink|apply IH; exact Hlast].
Qed.

Lemma semi_segment_decreases {V} (EV : encoding V) m (rank : V -> positive) :
  (forall v a, Map.get EV v m = Some a -> Pos.lt (rank a) (rank v)) ->
  forall v a xs, semi_segment EV m v a xs ->
    (xs = [] /\ v = a) \/ Pos.lt (rank a) (rank v).
Proof.
  intros Hrank v a xs Hsegment; induction Hsegment as [v|v b a xs Hlink Hsegment IH].
  - left; auto.
  - right; destruct IH as [[_ Heq]|Hlt].
    + subst a; apply Hrank; exact Hlink.
    + eapply Pos.lt_trans; [exact Hlt|apply Hrank; exact Hlink].
Qed.

Lemma semi_shortcut_decreases {V} (EV : encoding V) score st (rank : V -> positive) :
  semi_links_valid EV score st ->
  (forall v a, Map.get EV v (original st) = Some a -> Pos.lt (rank a) (rank v)) ->
  forall v a, Map.get EV v (shortcut st) = Some a -> Pos.lt (rank a) (rank v).
Proof.
  intros Hvalid Hrank v a Hlink.
  destruct (semi_shortcuts _ _ _ Hvalid v a Hlink) as [xs [Hnonempty [Hsegment _]]].
  destruct (semi_segment_decreases EV _ rank Hrank v a xs Hsegment)
    as [[Hempty _]|Hlt]; [contradiction|exact Hlt].
Qed.

Lemma semi_minimum_app {V} (score : V -> positive) u v xs ys :
  semi_minimum score u xs -> semi_minimum score v ys ->
  semi_minimum score (semi_min score u v) (xs ++ ys).
Proof.
  intros [Hu Humin] [Hv Hvmin]; split.
  - destruct (semi_min_member score u v) as [Heq|Heq]; rewrite Heq;
      apply in_or_app; auto.
  - intros w Hw; apply in_app_or in Hw.
    destruct (semi_min_bounds score u v) as [Hleft Hright].
    destruct Hw as [Hw|Hw].
    + eapply Pos.le_trans; [exact Hleft|apply Humin; exact Hw].
    + eapply Pos.le_trans; [exact Hright|apply Hvmin; exact Hw].
Qed.

(** Updating a shortcut leaves the uncompressed forest untouched. *)
Definition semi_shortcut_set {V} (EV : encoding V) (st : SemiLinks.t V) v root best
    : SemiLinks.t V :=
  SemiLinks.Make (original st) (Map.set EV v root (shortcut st))
    (Map.set EV v best (labels st)).

(** A query returns the compressed state, its forest root, and an optional nonroot minimum. *)
Definition semi_query_result (V : Type) : Type := SemiLinks.t V * (V * option V).

(** Decide the termination measure with binary comparison; conversions remain proof-only. *)
Definition semi_rank_less (a b : positive) :
    {Pos.to_nat a < Pos.to_nat b} + {~ Pos.to_nat a < Pos.to_nat b}.
Proof.
  destruct (Pos.ltb a b) eqn:Hlt.
  - left; apply Pos2Nat.inj_lt; apply Pos.ltb_lt; exact Hlt.
  - right; apply Pos.ltb_ge in Hlt; apply Pos2Nat.inj_le in Hlt; lia.
Defined.

(** One recursive query combines the stored segment with the parent's remaining linked path. *)
Definition semi_compress_body {V} (EV : encoding V) (rank score : V -> positive)
    (st : SemiLinks.t V) (v : V)
    (rec : forall a, Pos.to_nat (rank a) < Pos.to_nat (rank v) -> semi_query_result V)
    : semi_query_result V :=
  match Map.get EV v (shortcut st) with
  | None => (st, (v, None))
  | Some a =>
    match semi_rank_less (rank a) (rank v) with
    | left Hdecrease =>
      let '(st', (root, part)) := rec a Hdecrease in
      let best := match part with
        | None => semi_label EV st v
        | Some u => semi_min score (semi_label EV st v) u
        end in
      (semi_shortcut_set EV st' v root best, (root, Some best))
    | right _ => (st, (v, None))
    end
  end.

(** Well-founded recursion follows strictly decreasing discovery numbers, without unary fuel. *)
Definition semi_compress {V} (EV : encoding V) (rank score : V -> positive)
    (st : SemiLinks.t V) : V -> semi_query_result V :=
  Fix (well_founded_ltof V (fun v => Pos.to_nat (rank v)))
    (fun _ => semi_query_result V) (semi_compress_body EV rank score st).

Lemma semi_compress_unfold {V} (EV : encoding V) rank score st v :
  semi_compress EV rank score st v =
    semi_compress_body EV rank score st v (fun a _ => semi_compress EV rank score st a).
Proof.
  unfold semi_compress.
  apply (Fix_eq (well_founded_ltof V (fun x => Pos.to_nat (rank x)))
    (fun _ => semi_query_result V) (semi_compress_body EV rank score st)).
  intros x f h Hagree; unfold semi_compress_body.
  destruct (Map.get EV x (shortcut st)) as [a|]; [|reflexivity].
  destruct (semi_rank_less (rank a) (rank x)) as [Hlt|Hnot];
    [rewrite (Hagree a Hlt)|]; reflexivity.
Qed.

Lemma semi_segment_linked {V} (EV : encoding V) m v root xs :
  semi_segment EV m v root xs -> forall u, In u xs -> exists a, Map.get EV u m = Some a.
Proof.
  intro Hsegment; induction Hsegment as [v|v a root xs Hlink Hsegment IH];
    intros u Hin; [contradiction|].
  destruct Hin as [Heq|Hin]; [subst u; eauto|apply IH; exact Hin].
Qed.

Lemma semi_shortcut_set_valid {V} (EV : encoding V) score st v root best xs :
  semi_links_valid EV score st -> xs <> [] ->
  semi_segment EV (original st) v root xs -> semi_minimum score best xs ->
  semi_links_valid EV score (semi_shortcut_set EV st v root best).
Proof.
  intros Hvalid Hnonempty Hsegment Hminimum; constructor.
  - intro x; cbn [semi_shortcut_set shortcut original].
    destruct (dfs_eq_dec EV x v) as [Heq|Hne].
    + subst x; rewrite Map.get_set_same; split; [discriminate|].
      intro Hnone; inversion Hsegment; subst; [contradiction|congruence].
    + rewrite Map.get_set_other by exact Hne; apply (semi_roots _ _ _ Hvalid).
  - intros x a Hget; cbn [semi_shortcut_set shortcut] in Hget.
    destruct (dfs_eq_dec EV x v) as [Heq|Hne].
    + subst x; rewrite Map.get_set_same in Hget; inversion Hget; subst a.
      exists xs; split; [exact Hnonempty|]; split; [exact Hsegment|].
      unfold semi_label; cbn [semi_shortcut_set labels]; rewrite Map.get_set_same.
      exact Hminimum.
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (semi_shortcuts _ _ _ Hvalid x a Hget) as [ys [Hys [Hpath Hmin]]].
      exists ys; split; [exact Hys|]; split; [exact Hpath|].
      unfold semi_label; cbn [semi_shortcut_set labels].
      rewrite Map.get_set_other by exact Hne; exact Hmin.
Qed.

(** The returned minimum covers precisely the queried original path, excluding its root. *)
Definition semi_query_valid {V} (EV : encoding V) (score : V -> positive)
    (st : SemiLinks.t V) (v : V) (result : semi_query_result V) : Prop :=
  let '(st', (root, part)) := result in
  original st' = original st /\ semi_links_valid EV score st' /\
  Map.get EV root (original st) = None /\
  exists xs, semi_segment EV (original st) v root xs /\
    match part with
    | None => xs = []
    | Some best => xs <> [] /\ semi_minimum score best xs
    end.

(** Compression preserves every shortcut segment and returns its original-path minimum. *)
Lemma semi_compress_correct {V} (EV : encoding V) rank score st :
  semi_links_valid EV score st ->
  (forall v a, Map.get EV v (original st) = Some a -> Pos.lt (rank a) (rank v)) ->
  forall v, semi_query_valid EV score st v (semi_compress EV rank score st v).
Proof.
  intros Hvalid Hrank.
  apply (well_founded_induction (well_founded_ltof V (fun v => Pos.to_nat (rank v)))).
  intros v IH; rewrite semi_compress_unfold; unfold semi_compress_body.
  destruct (Map.get EV v (shortcut st)) as [a|] eqn:Hlink.
  - pose proof (semi_shortcut_decreases EV score st rank Hvalid Hrank v a Hlink) as Hlt.
    apply Pos2Nat.inj_lt in Hlt.
    destruct (semi_rank_less (rank a) (rank v)) as [Hdec|Hnot];
      [|contradiction].
    specialize (IH a Hdec).
    destruct (semi_compress EV rank score st a) as [st' [root part]] eqn:Hquery.
    cbn [semi_query_valid] in IH.
    destruct IH as [Horiginal [Hvalid' [Hroot [ys [Hrest Hminimum]]]]].
    destruct (semi_shortcuts _ _ _ Hvalid v a Hlink)
      as [xs [Hxs [Hsegment Hlabel]]].
    assert (Hwhole : semi_segment EV (original st) v root (xs ++ ys)).
    { eapply semi_segment_app; eauto. }
    assert (Hnonempty : xs ++ ys <> []).
    { intro Heq; apply app_eq_nil in Heq; tauto. }
    destruct part as [best|]; cbn.
    + destruct Hminimum as [_ Hbest].
      pose proof (semi_minimum_app score _ _ _ _ Hlabel Hbest) as Hcombined.
      split; [exact Horiginal|]; split.
      * apply semi_shortcut_set_valid with (xs := xs ++ ys); try assumption.
        rewrite Horiginal; exact Hwhole.
      * split; [exact Hroot|]; exists (xs ++ ys); auto.
    + subst ys; rewrite app_nil_r in Hwhole.
      split; [exact Horiginal|]; split.
      * apply semi_shortcut_set_valid with (xs := xs); try assumption.
        rewrite Horiginal; exact Hwhole.
      * split; [exact Hroot|]; exists xs; auto.
  - cbn [semi_query_valid]; split; [reflexivity|]; split; [exact Hvalid|]; split.
    + apply (proj1 (semi_roots _ _ _ Hvalid v)); exact Hlink.
    + exists []; split; [constructor|reflexivity].
Qed.

(** Eval exposes the selected segment vertex and threads all compression changes to its caller. *)
Definition semi_eval {V} (EV : encoding V) rank score st v : SemiLinks.t V * V :=
  let '(st', (_, part)) := semi_compress EV rank score st v in
  (st', match part with
    | Some best => best
    | None => v
    end).

(** Empty linked forests satisfy the segment invariant for every score function. *)
Definition semi_links_empty {V} : SemiLinks.t V :=
  SemiLinks.Make Map.empty Map.empty Map.empty.

Lemma semi_links_empty_valid {V} (EV : encoding V) score :
  semi_links_valid EV score (@semi_links_empty V).
Proof.
  constructor; cbn [semi_links_empty original shortcut].
  - intro v; reflexivity.
  - intros v a Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Link attaches a previously unlinked root and starts its one-vertex label segment. *)
Definition semi_link {V} (EV : encoding V) (st : SemiLinks.t V) v parent : SemiLinks.t V :=
  SemiLinks.Make (Map.set EV v parent (original st))
    (Map.set EV v parent (shortcut st)) (Map.set EV v v (labels st)).

Lemma semi_segment_extend {V} (EV : encoding V) m v parent :
  Map.get EV v m = None -> forall u root xs,
  semi_segment EV m u root xs -> semi_segment EV (Map.set EV v parent m) u root xs.
Proof.
  intros Hnone u root xs Hsegment.
  induction Hsegment as [u|u a root xs Hlink Hsegment IH].
  - constructor.
  - eapply SemiSegmentCons; [|exact IH].
    rewrite Map.get_set_other; [exact Hlink|intro Heq; subst u; congruence].
Qed.

(** Linking a root preserves all older segments because an old segment cannot contain a root. *)
Lemma semi_link_valid {V} (EV : encoding V) score st v parent :
  semi_links_valid EV score st -> Map.get EV v (original st) = None ->
  semi_links_valid EV score (semi_link EV st v parent).
Proof.
  intros Hvalid Hnone; constructor.
  - intro x; cbn [semi_link shortcut original].
    destruct (dfs_eq_dec EV x v) as [Heq|Hne].
    + subst x; rewrite !Map.get_set_same; reflexivity.
    + rewrite !Map.get_set_other by exact Hne; apply (semi_roots _ _ _ Hvalid).
  - intros x a Hget; cbn [semi_link shortcut] in Hget.
    destruct (dfs_eq_dec EV x v) as [Heq|Hne].
    + subst x; rewrite Map.get_set_same in Hget; inversion Hget; subst a.
      exists [v]; split; [discriminate|]; split.
      * eapply SemiSegmentCons; [apply Map.get_set_same|constructor].
      * unfold semi_label; cbn [semi_link labels]; rewrite Map.get_set_same.
        split; [left; reflexivity|].
        intros x [Heq|Hfalse]; [subst x; apply Pos.le_refl|contradiction].
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (semi_shortcuts _ _ _ Hvalid x a Hget) as [xs [Hxs [Hpath Hmin]]].
      exists xs; split; [exact Hxs|]; split.
      * apply semi_segment_extend; assumption.
      * unfold semi_label; cbn [semi_link labels]; rewrite Map.get_set_other by exact Hne.
        exact Hmin.
Qed.

Lemma semi_links_rescore {V} (EV : encoding V) score score' st :
  semi_links_valid EV score st ->
  (forall v a, Map.get EV v (original st) = Some a -> score' v = score v) ->
  semi_links_valid EV score' st.
Proof.
  intros Hvalid Hagree; constructor; [exact (semi_roots _ _ _ Hvalid)|].
  intros v a Hlink.
  destruct (semi_shortcuts _ _ _ Hvalid v a Hlink) as [xs [Hxs [Hpath [Hin Hmin]]]].
  exists xs; split; [exact Hxs|]; split; [exact Hpath|]; split; [exact Hin|].
  intros u Hu.
  destruct (semi_segment_linked EV _ _ _ _ Hpath _ Hin) as [b Hbest].
  destruct (semi_segment_linked EV _ _ _ _ Hpath _ Hu) as [c Hmember].
  rewrite (Hagree _ _ Hbest), (Hagree _ _ Hmember); apply Hmin; exact Hu.
Qed.

(** * Reverse-order settlement *)

Module SemiState.

(** Settled semidominators and the maintained link/eval forest form one threaded state. *)
Record t (V : Type) : Type := Make {
  result : Map.t V V;
  links : SemiLinks.t V
}.
Arguments Make {V}.
Arguments result {V}.
Arguments links {V}.

End SemiState.
Import SemiState.

(** Unsettled vertices initially name themselves, without materializing identity bindings. *)
Definition semi_value {V} (EV : encoding V) (semis : Map.t V V) (v : V) : V :=
  match Map.get EV v semis with
  | Some u => u
  | None => v
  end.

(** A predecessor query ignores an unreachable source and otherwise minimizes its eval score. *)
Definition semi_predecessor {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) (acc : SemiLinks.t V * V) (e : E)
    : SemiLinks.t V * V :=
  let '(st, best) := acc in
  let v := Graph.source g e in
  match Map.get EV v (pre_num r) with
  | None => (st, best)
  | Some _ =>
    let '(st', u) := semi_eval EV (semi_rank EV r)
      (fun x => semi_rank EV r (semi_value EV semis x)) st v in
    (st', semi_min (semi_rank EV r) best (semi_value EV semis u))
  end.

(** Settle one nonroot vertex, then link it to its discovery parent. *)
Definition semi_settle {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) (st : SemiState.t V) (w : V)
    : SemiState.t V :=
  match Map.get EV w (tree_edge r) with
  | None => st
  | Some e =>
    let parent := Graph.source g e in
    let '(st', best) := fold_left (semi_predecessor EV g r (result st))
      (pred_edges p w) (links st, parent) in
    SemiState.Make (Map.set EV w best (result st)) (semi_link EV st' w parent)
  end.

(** One reverse discovery traversal settles the map, sharing its predecessor and forest state. *)
Definition semi_compute {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (r : dfs_result V E) : SemiState.t V :=
  fold_left (semi_settle p r) (rev (preorder r)) (SemiState.Make Map.empty semi_links_empty).

(** Shared semidominators omit the fresh root and every unreachable client vertex. *)
Definition semidominators {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : Map.t (V + unit) (V + unit) :=
  let vp := virtual_prepared p in
  let r := dfs vp FinSet.empty [inr tt] in
  result (semi_compute vp r).

Lemma semi_settle_wf {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    r st w : Map.wf EV (result st) -> Map.wf EV (result (semi_settle p r st w)).
Proof.
  intro Hwf; unfold semi_settle.
  destruct (Map.get EV w (tree_edge r)) as [e|]; [|exact Hwf].
  destruct (fold_left _ _ _) as [links' best]; cbn [result]; apply Map.wf_set; exact Hwf.
Qed.

Lemma semi_compute_wf {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) r :
  Map.wf EV (result (semi_compute p r)).
Proof.
  unfold semi_compute.
  assert (Hfold : forall xs st, Map.wf EV (result st) ->
    Map.wf EV (result (fold_left (semi_settle p r) xs st))).
  { intro xs; induction xs as [|v xs IH]; intros st Hwf; cbn [fold_left];
      [exact Hwf|apply IH; apply semi_settle_wf; exact Hwf]. }
  apply Hfold; apply Map.wf_empty.
Qed.

(** The reverse-order producer always builds a well-formed semidominator map. *)
Theorem semidominators_wf {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> Map.wf (virtual_encoding EV) (semidominators p).
Proof.
  intro Hready; apply semi_compute_wf.
Qed.

(** * Search facts used by reverse-order reasoning *)

(** A numbered vertex is one reached by this search. *)
Definition semi_live {V E} (EV : encoding V) (r : dfs_result V E) (v : V) : Prop :=
  exists k, Map.get EV v (pre_num r) = Some k.

Definition semi_post_rank {V E} (EV : encoding V) (r : dfs_result V E) (v : V)
    : positive :=
  match Map.get EV v (post_num r) with
  | Some k => k
  | None => 1%positive
  end.

(** Numbering, tree and edge facts isolate the DFS boundary of the semidominator proof. *)
Record semi_search_laws {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (root : V) : Prop := {
  semi_live_exact : forall v, semi_live EV r v <-> reachable g v;
  semi_search_numbering : exists next,
    dfs_numbering EV (rev (preorder r)) (pre_num r) next;
  semi_parent_numbered : forall v e, Map.get EV v (tree_edge r) = Some e ->
    semi_live EV r v /\ semi_live EV r (Graph.source g e) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
    Pos.lt (semi_rank EV r (Graph.source g e)) (semi_rank EV r v);
  semi_unlinked_entry : forall v, semi_live EV r v ->
    Map.get EV v (tree_edge r) = None -> v = root;
  semi_search_rooted : forall v, semi_live EV r v -> dfs_ancestor EV g r root v;
  semi_search_intervals : forall u v, semi_live EV r u -> semi_live EV r v ->
    (ancestor_b EV r u v = true <-> dfs_ancestor EV g r u v);
  semi_post_numbered : forall v, semi_live EV r v ->
    exists k, Map.get EV v (post_num r) = Some k;
  semi_search_edge_order : forall e, semi_live EV r (Graph.source g e) ->
    In e (Graph.out g (Graph.source g e)) ->
    Pos.lt (semi_post_rank EV r (Graph.target g e)) (semi_post_rank EV r (Graph.source g e)) \/
    dfs_ancestor EV g r (Graph.target g e) (Graph.source g e)
}.

Lemma semi_rank_numbered {V E} (EV : encoding V) (r : dfs_result V E) v k :
  Map.get EV v (pre_num r) = Some k -> semi_rank EV r v = k.
Proof.
  intro Hget; unfold semi_rank; rewrite Hget; reflexivity.
Qed.

Lemma semi_post_rank_numbered {V E} (EV : encoding V) (r : dfs_result V E) v k :
  Map.get EV v (post_num r) = Some k -> semi_post_rank EV r v = k.
Proof.
  intro Hget; unfold semi_post_rank; rewrite Hget; reflexivity.
Qed.

Lemma semi_single_search_laws {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) root : ready EV g p -> Graph.entries g = [root] ->
  semi_search_laws EV g (dfs p FinSet.empty [root]) root.
Proof.
  intros Hready Hentries; pose proof Hready as [Hwf _].
  assert (Hroots : incl [root] (Graph.nodes g)).
  { rewrite <- Hentries; intros v Hv; exact (entries_in Hwf v Hv). }
  destruct (dfs_final_spec EV g p FinSet.empty [root] Hready Hroots)
    as [Hinv [Hlabels Hinterval]].
  set (st := fold_left (dfs_root p FinSet.empty) [root] dfs_initial) in *.
  assert (Hlive : forall v, semi_live EV (dfs p FinSet.empty [root]) v <-> In v (pre st)).
  { intro v; unfold semi_live, dfs; cbn [pre_num].
    apply (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)). }
  constructor.
  - intro v; rewrite Hlive.
    pose proof (reachable_dfs EV g p v Hready) as Hreach; rewrite Hentries in Hreach.
    unfold dfs in Hreach; cbn [visited] in Hreach.
    rewrite <- (dfs_seen_pre _ _ _ _ _ _ Hinv); exact Hreach.
  - exists (pre_clock st); unfold dfs; cbn [preorder pre_num]; rewrite rev_involutive.
    apply (dfs_pre_numbering _ _ _ _ Hlabels).
  - intros v e Hget; unfold dfs in Hget; cbn [tree_edge] in Hget.
    destruct (dfs_parent_labels _ _ _ _ Hlabels v e Hget)
      as [Hv [Hs [He [Ht [a [b [Ha [Hb Hlt]]]]]]]].
    split; [apply Hlive; exact Hv|]; split; [apply Hlive; exact Hs|].
    split; [exact He|]; split; [exact Ht|].
    rewrite (semi_rank_numbered EV (dfs p FinSet.empty [root]) _ a Ha),
      (semi_rank_numbered EV (dfs p FinSet.empty [root]) _ b Hb); exact Hlt.
  - intros v Hv Hget; apply Hlive in Hv.
    unfold dfs in Hget; cbn [tree_edge] in Hget.
    destruct (dfs_root_labels _ _ _ _ Hlabels v Hv Hget) as [Heq|Hfalse];
      [symmetry; exact Heq|contradiction].
  - intros v Hv; apply Hlive in Hv.
    destruct (dfs_ancestry_root EV g [root] st v Hlabels Hv)
      as [s [[Heq|Hfalse] Hancestor]]; [subst s; exact Hancestor|contradiction].
  - intros u v Hu Hv; apply ancestor_b_agrees; try assumption;
      unfold dfs; cbn [visited]; apply (dfs_seen_pre _ _ _ _ _ _ Hinv); apply Hlive;
      assumption.
  - intros v Hv; apply Hlive in Hv; unfold dfs; cbn [post_num].
    apply (dfs_final_post_number EV g FinSet.empty [root] st v Hinv Hlabels Hv).
  - intros e Hsource Hedge; apply Hlive in Hsource.
    apply (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv)) in Hsource.
    destruct (dfs_finished_classes _ _ _ _ _ Hinterval _ e Hsource Hedge)
      as [Hblocked|[[a [b [Ha [Hb Hlt]]]]|Hancestor]].
    + rewrite FinSet.mem_empty in Hblocked; discriminate.
    + left; rewrite (semi_post_rank_numbered EV (dfs p FinSet.empty [root]) _ a Ha),
        (semi_post_rank_numbered EV (dfs p FinSet.empty [root]) _ b Hb); exact Hlt.
    + right; exact Hancestor.
Qed.

Lemma semi_number_injective {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) root :
  semi_search_laws EV g r root -> forall u v,
  semi_live EV r u -> semi_live EV r v -> semi_rank EV r u = semi_rank EV r v -> u = v.
Proof.
  intros Hlaws u v [a Ha] [b Hb] Heq.
  rewrite (semi_rank_numbered EV r u a Ha), (semi_rank_numbered EV r v b Hb) in Heq.
  subst b; destruct (semi_search_numbering _ _ _ _ Hlaws) as [next Hnumber].
  eapply dfs_numbering_injective; eauto.
Qed.

Lemma semi_ancestor_order {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) root :
  semi_search_laws EV g r root -> forall u v, dfs_ancestor EV g r u v ->
  u = v \/ Pos.lt (semi_rank EV r u) (semi_rank EV r v).
Proof.
  intros Hlaws u v Hancestor; induction Hancestor as [u v [e [He Hsource]]|u|
    u x v Hux IHux Hxv IHxv].
  - right; subst u; apply (semi_parent_numbered _ _ _ _ Hlaws v e He).
  - left; reflexivity.
  - destruct IHux as [Heq|Hlt], IHxv as [Heq'|Hlt']; subst; auto.
    right; eapply Pos.lt_trans; eauto.
Qed.

Lemma semi_ancestor_live {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) root :
  semi_search_laws EV g r root -> forall u v, semi_live EV r u ->
  dfs_ancestor EV g r u v -> semi_live EV r v.
Proof.
  intros Hlaws u v Hu Hancestor; induction Hancestor as [u v [e [He _]]|u|
    u x v Hux IHux Hxv IHxv].
  - apply (semi_parent_numbered _ _ _ _ Hlaws v e He).
  - exact Hu.
  - apply IHxv; apply IHux; exact Hu.
Qed.

Lemma semi_ancestor_cut {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) root :
  semi_search_laws EV g r root -> forall a b v,
  dfs_ancestor EV g r a v -> dfs_ancestor EV g r b v ->
  Pos.le (semi_rank EV r a) (semi_rank EV r b) -> dfs_ancestor EV g r a b.
Proof.
  intros Hlaws a b v Ha.
  pose proof (clos_rt_rtn1 V (tree_parent EV g r) a v Ha) as Hchain.
  clear Ha; revert b; induction Hchain as [|v x [e [He Hsource]] Hav IH]; intros b Hb Hle.
  - destruct (semi_ancestor_order EV g r root Hlaws b a Hb) as [Heq|Hlt].
    + subst b; apply rt_refl.
    + exfalso; apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; lia.
  - pose proof (clos_rt_rtn1 V (tree_parent EV g r) b x Hb) as Hchainb.
    inversion Hchainb as [|v' x' [f [Hf Hsource']] Hbv]; subst.
    + apply (clos_rtn1_rt V (tree_parent EV g r) a x).
      eapply Relation_Operators.rtn1_trans; [exists e; auto|exact Hav].
    + rewrite He in Hf; inversion Hf; subst f; apply IH; [|exact Hle].
      apply (clos_rtn1_rt V (tree_parent EV g r)); exact Hbv.
Qed.

Section SemiPathTheory.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (root : V).
Hypothesis Hsearch : semi_search_laws EV g r root.
Local Abbreviation rank := (semi_rank EV r).
Local Abbreviation postrank := (semi_post_rank EV r).

Lemma semi_live_step e : semi_live EV r (Graph.source g e) ->
  In e (Graph.out g (Graph.source g e)) -> semi_live EV r (Graph.target g e).
Proof.
  intros Hlive Hedge; apply (semi_live_exact _ _ _ _ Hsearch).
  eapply reachable_step; [apply (semi_live_exact _ _ _ _ Hsearch); exact Hlive|exact Hedge].
Qed.

Lemma semi_interval_bounds u v : semi_live EV r u -> semi_live EV r v ->
  (dfs_ancestor EV g r u v <-> Pos.le (rank u) (rank v) /\ Pos.le (postrank v) (postrank u)).
Proof.
  intros Hu Hv; rewrite <- (semi_search_intervals _ _ _ _ Hsearch u v Hu Hv).
  destruct (semi_post_numbered _ _ _ _ Hsearch u Hu) as [c Hc].
  destruct (semi_post_numbered _ _ _ _ Hsearch v Hv) as [d Hd].
  destruct Hu as [a Ha]; destruct Hv as [b Hb].
  unfold ancestor_b, semi_rank, semi_post_rank; rewrite Ha, Hb, Hc, Hd.
  rewrite andb_true_iff, !Pos.leb_le; reflexivity.
Qed.

Lemma semi_subtree_edge a e : semi_live EV r a -> semi_live EV r (Graph.source g e) ->
  dfs_ancestor EV g r a (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
  Pos.le (rank a) (rank (Graph.target g e)) -> dfs_ancestor EV g r a (Graph.target g e).
Proof.
  intros Ha Hsource Hancestor Hedge Hrank.
  pose proof (semi_live_step e Hsource Hedge) as Htarget.
  destruct (semi_search_edge_order _ _ _ _ Hsearch e Hsource Hedge) as [Hpost|Hback].
  - apply (semi_interval_bounds a _ Ha Htarget); split; [exact Hrank|].
    apply (semi_interval_bounds a _ Ha Hsource) in Hancestor.
    eapply Pos.le_trans; [apply Pos.lt_le_incl; exact Hpost|exact (proj2 Hancestor)].
  - eapply semi_ancestor_cut; eauto.
Qed.

Lemma semi_path_region a s es n : semi_live EV r a -> path g s es n ->
  semi_live EV r s -> dfs_ancestor EV g r a s ->
  (forall e, In e es -> Pos.le (rank a) (rank (Graph.target g e))) ->
  dfs_ancestor EV g r a n.
Proof.
  intros Ha Hpath; induction Hpath as [s|e es n Hedge Hpath IH]; intros Hs Hancestor Hbounds.
  - exact Hancestor.
  - apply IH.
    + apply semi_live_step; assumption.
    + apply semi_subtree_edge; try assumption; apply Hbounds; left; reflexivity.
    + intros f Hf; apply Hbounds; right; exact Hf.
Qed.

Lemma semi_path_live s es n : path g s es n -> semi_live EV r s ->
  semi_live EV r n /\ forall e, In e es -> semi_live EV r (Graph.target g e).
Proof.
  intro Hpath; induction Hpath as [s|e es n Hedge Hpath IH]; intro Hs.
  - split; [exact Hs|intros e Hfalse; contradiction].
  - pose proof (semi_live_step e Hs Hedge) as Htarget.
    destruct (IH Htarget) as [Hn Hall]; split; [exact Hn|].
    intros f [Heq|Hf]; [subst f; exact Htarget|apply Hall; exact Hf].
Qed.

Lemma semi_path_app s xs u ys n : path g s xs u -> path g u ys n -> path g s (xs ++ ys) n.
Proof.
  intros Hfirst Hlast; induction Hfirst as [s|e xs u Hedge Hpath IH].
  - exact Hlast.
  - cbn [app]; constructor; [exact Hedge|apply IH; exact Hlast].
Qed.

(** The final edge target is exempt from the strict internal-rank condition. *)
Fixpoint semi_internal_above (k : positive) (es : list E) : Prop :=
  match es with
  | [] => True
  | e :: rest =>
    match rest with
    | [] => True
    | _ :: _ => Pos.lt k (rank (Graph.target g e)) /\ semi_internal_above k rest
    end
  end.

Lemma semi_internal_decomposition k es : semi_internal_above k es <->
  forall pre e post, es = pre ++ e :: post -> post <> [] -> Pos.lt k (rank (Graph.target g e)).
Proof.
  induction es as [|a es IH].
  - split; [|intros _; exact I].
    intros _ pre e post Heq Hnonempty; apply (f_equal (@length E)) in Heq.
    rewrite length_app in Heq; cbn [length] in Heq; lia.
  - destruct es as [|b es].
    + split; [|intros _; exact I].
      intros _ pre e post Heq Hnonempty; apply (f_equal (@length E)) in Heq.
      rewrite length_app in Heq; cbn [length] in Heq.
      assert (length post > 0) by (destruct post; [contradiction|cbn; lia]); lia.
    + change ((Pos.lt k (rank (Graph.target g a)) /\
        semi_internal_above k (b :: es)) <-> forall pre e post,
        a :: b :: es = pre ++ e :: post -> post <> [] ->
        Pos.lt k (rank (Graph.target g e))); rewrite IH; split.
      * intros [Ha Htail] [|x pre] e post Heq Hnonempty; cbn [app] in Heq.
        -- inversion Heq; subst e; exact Ha.
        -- inversion Heq; subst x; apply (Htail pre e post); assumption.
      * intro Hall; split.
        -- apply (Hall [] a (b :: es)); [reflexivity|discriminate].
        -- intros pre e post Heq Hnonempty.
           apply (Hall (a :: pre) e post); [cbn; now rewrite Heq|exact Hnonempty].
Qed.

Lemma semi_path_characterization u n : semidom_path EV g r u n <->
  semi_live EV r u /\ semi_live EV r n /\
  exists es, es <> [] /\ path g u es n /\ semi_internal_above (rank n) es.
Proof.
  split.
  - intros [es [k [h [Hnonempty [Hpath [Hk [Hh Hinternal]]]]]]].
    split; [exists h; exact Hh|]; split; [exists k; exact Hk|].
    exists es; split; [exact Hnonempty|]; split; [exact Hpath|].
    apply semi_internal_decomposition; intros pre e post Heq Hpost.
    destruct (Hinternal pre e post Heq Hpost) as [j [Hj Hlt]].
    rewrite (semi_rank_numbered EV r n k Hk), (semi_rank_numbered EV r _ j Hj); exact Hlt.
  - intros [[h Hh] [[k Hk] [es [Hnonempty [Hpath Hinternal]]]]].
    exists es, k, h; split; [exact Hnonempty|]; split; [exact Hpath|]; split; [exact Hk|].
    split; [exact Hh|]; intros pre e post Heq Hpost.
    assert (Hin : In e es) by (rewrite Heq; apply in_or_app; right; left; reflexivity).
    destruct (proj2 (semi_path_live u es n Hpath (ex_intro _ h Hh)) e Hin) as [j Hj].
    exists j; split; [exact Hj|].
    pose proof (proj1 (semi_internal_decomposition (rank n) es) Hinternal
      pre e post Heq Hpost) as Hrank.
    rewrite (semi_rank_numbered EV r n k Hk), (semi_rank_numbered EV r _ j Hj) in Hrank.
    exact Hrank.
Qed.

Lemma semi_internal_prepend k e es : es <> [] ->
  Pos.lt k (rank (Graph.target g e)) -> semi_internal_above k es ->
  semi_internal_above k (e :: es).
Proof.
  intros Hnonempty Hrank Hinternal; destruct es; [contradiction|]; split; assumption.
Qed.

(** The first minimum target splits a path into a semidominator prefix and a high suffix. *)
Lemma semi_path_minimum s es n : path g s es n -> es <> [] ->
  exists u pre post, es = pre ++ post /\ pre <> [] /\ path g s pre u /\ path g u post n /\
    semi_internal_above (rank u) pre /\
    forall e, In e es -> Pos.le (rank u) (rank (Graph.target g e)).
Proof.
  intro Hpath; induction Hpath as [s|e es n Hedge Hpath IH]; intro Hnonempty;
    [contradiction|].
  destruct es as [|f es].
  - apply dominance_path_nil_inv in Hpath; subst n.
    exists (Graph.target g e), [e], []; split; [reflexivity|]; split; [discriminate|].
    split; [constructor; [exact Hedge|constructor]|]; split; [constructor|].
    split; [exact I|].
    intros a [Heq|Hfalse]; [subst a; apply Pos.le_refl|contradiction].
  - destruct (IH ltac:(discriminate))
      as [u [pre [post [Hsplit [Hpre [Hfirst [Hlast [Hint Hmin]]]]]]]].
    destruct (Pos.leb (rank (Graph.target g e)) (rank u)) eqn:Hcompare.
    + apply Pos.leb_le in Hcompare.
      exists (Graph.target g e), [e], (f :: es); split; [reflexivity|]; split;
        [discriminate|]; split; [constructor; [exact Hedge|constructor]|].
      split; [exact Hpath|]; split; [exact I|].
      intros a [Heq|Hin]; [subst a; apply Pos.le_refl|].
      eapply Pos.le_trans; [exact Hcompare|apply Hmin; exact Hin].
    + apply Pos.leb_gt in Hcompare.
      exists u, (e :: pre), post; split; [cbn; now rewrite Hsplit|]; split; [discriminate|].
      split; [constructor; assumption|]; split; [exact Hlast|]; split.
      * apply semi_internal_prepend; assumption.
      * intros a [Heq|Hin]; [subst a; apply Pos.lt_le_incl; exact Hcompare|apply Hmin; exact Hin].
Qed.

Lemma semi_path_last s es n : path g s es n -> es <> [] ->
  exists pre e, es = pre ++ [e] /\ path g s pre (Graph.source g e) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = n.
Proof.
  intro Hpath; induction Hpath as [s|e es n Hedge Hpath IH]; intro Hnonempty;
    [contradiction|].
  destruct es as [|f es].
  - apply dominance_path_nil_inv in Hpath; exists [], e; split; [reflexivity|].
    split; [constructor|]; split; [exact Hedge|exact Hpath].
  - destruct (IH ltac:(discriminate)) as [pre [last [Hsplit [Hprefix [Hlast Htarget]]]]].
    exists (e :: pre), last; split; [cbn; now rewrite Hsplit|].
    split; [constructor; assumption|auto].
Qed.

Lemma semi_single_edge e : semi_live EV r (Graph.source g e) ->
  In e (Graph.out g (Graph.source g e)) ->
  semidom_path EV g r (Graph.source g e) (Graph.target g e).
Proof.
  intros Hlive Hedge; apply semi_path_characterization; split; [exact Hlive|].
  split; [apply semi_live_step; assumption|].
  exists [e]; split; [discriminate|]; split; [constructor; [exact Hedge|constructor]|exact I].
Qed.

Lemma semi_internal_snoc k es e :
  (forall a, In a es -> Pos.lt k (rank (Graph.target g a))) ->
  semi_internal_above k (es ++ [e]).
Proof.
  induction es as [|a es IH]; intro Hall; [exact I|].
  apply semi_internal_prepend.
  - intro Heq; apply app_eq_nil in Heq; destruct Heq as [_ Hfalse]; discriminate.
  - apply Hall; left; reflexivity.
  - apply IH; intros b Hb; apply Hall; right; exact Hb.
Qed.

Lemma semi_internal_lower k s es n : path g s es n ->
  semi_internal_above (rank n) es -> Pos.lt k (rank n) ->
  forall e, In e es -> Pos.lt k (rank (Graph.target g e)).
Proof.
  intro Hpath; induction Hpath as [s|a es n Hedge Hpath IH]; intros Hinternal Hlt e Hin;
    [contradiction|].
  destruct es as [|b es].
  - destruct Hin as [Heq|Hfalse]; [subst e|contradiction].
    apply dominance_path_nil_inv in Hpath; now rewrite Hpath.
  - destruct Hinternal as [Ha Hrest]; destruct Hin as [Heq|Hin].
    + subst e; eapply Pos.lt_trans; eauto.
    + apply IH; assumption.
Qed.

Lemma semi_tree_path u v : dfs_ancestor EV g r u v ->
  exists es, path g u es v /\
    forall e, In e es -> Pos.le (rank u) (rank (Graph.target g e)).
Proof.
  intro Hancestor; pose proof (clos_rt_rtn1 V (tree_parent EV g r) u v Hancestor) as Hchain.
  clear Hancestor.
  induction Hchain as [|a v [e [He Hsource]] Hchain IH].
  - exists []; split; [constructor|intros e Hfalse; contradiction].
  - destruct IH as [es [Hpath Hbounds]].
    destruct (semi_parent_numbered _ _ _ _ Hsearch v e He) as [_ [_ [Hedge [Htarget Hlt]]]].
    exists (es ++ [e]); split.
    + rewrite <- Htarget; eapply path_snoc; [exact Hpath|symmetry; exact Hsource|].
      rewrite <- Hsource; exact Hedge.
    + intros f Hf; apply in_app_or in Hf; destruct Hf as [Hf|[Heq|Hfalse]].
      * apply Hbounds; exact Hf.
      * subst f; rewrite Htarget.
        destruct (semi_ancestor_order EV g r root Hsearch u a
          (clos_rtn1_rt V (tree_parent EV g r) u a Hchain)) as [Heq|Hua].
        -- rewrite Heq, <- Hsource; apply Pos.lt_le_incl; exact Hlt.
        -- eapply Pos.le_trans; [apply Pos.lt_le_incl; exact Hua|].
           apply Pos.lt_le_incl; now rewrite <- Hsource.
      * contradiction.
Qed.

(** An already settled descendant supplies a semidominator path through its tree suffix. *)
Lemma semi_path_extend s u v w e : semidom_path EV g r s u ->
  Pos.lt (rank w) (rank u) -> dfs_ancestor EV g r u v ->
  Graph.source g e = v -> Graph.target g e = w -> In e (Graph.out g v) ->
  semidom_path EV g r s w.
Proof.
  intros Hsemi Hrank Hancestor Hsource Htarget Hedge.
  apply semi_path_characterization in Hsemi.
  destruct Hsemi as [Hs [Hu [prefix [Hprefix [Hpath Hinternal]]]]].
  destruct (semi_tree_path u v Hancestor) as [suffix [Htree Hbounds]].
  assert (Hw : semi_live EV r w).
  { rewrite <- Htarget; apply semi_live_step.
    - rewrite Hsource; eapply semi_ancestor_live; eauto.
    - now rewrite Hsource. }
  apply semi_path_characterization; split; [exact Hs|]; split; [exact Hw|].
  exists ((prefix ++ suffix) ++ [e]); split.
  - intro Hempty; apply app_eq_nil in Hempty; destruct Hempty as [_ Hfalse]; discriminate.
  - split.
    + rewrite <- Htarget; eapply path_snoc; [eapply semi_path_app; eauto|symmetry; exact Hsource|
        exact Hedge].
    + apply semi_internal_snoc; intros f Hf; apply in_app_or in Hf; destruct Hf as [Hf|Hf].
      * exact (semi_internal_lower (rank w) s prefix u Hpath Hinternal Hrank f Hf).
      * eapply Pos.lt_le_trans; [exact Hrank|apply Hbounds; exact Hf].
Qed.

(** Every semidominator path splits at a minimum internal vertex on a predecessor's tree path. *)
Lemma semi_path_predecessor s w : semidom_path EV g r s w ->
  exists e, In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = w /\
    semi_live EV r (Graph.source g e) /\
    (s = Graph.source g e \/ exists u, Pos.lt (rank w) (rank u) /\
      dfs_ancestor EV g r u (Graph.source g e) /\ semidom_path EV g r s u).
Proof.
  intro Hsemi; apply semi_path_characterization in Hsemi.
  destruct Hsemi as [Hs [Hw [es [Hnonempty [Hpath Hinternal]]]]].
  destruct (semi_path_last s es w Hpath Hnonempty)
    as [prefix [e [Hsplit [Hprefix [Hedge Htarget]]]]].
  exists e; split; [exact Hedge|]; split; [exact Htarget|]; split.
  - apply (proj1 (semi_path_live _ _ _ Hprefix Hs)).
  - destruct prefix as [|a prefix].
    + left; apply dominance_path_nil_inv in Hprefix; exact Hprefix.
    + right; destruct (semi_path_minimum s (a :: prefix) _ Hprefix ltac:(discriminate))
        as [u [first [last [Hparts [Hfirst [Hfirstpath [Hlastpath [Hfirstinternal Hminimum]]]]]]]].
      assert (Hhigh : forall f, In f (a :: prefix) -> Pos.lt (rank w) (rank (Graph.target g f))).
      { intros f Hf; apply in_split in Hf; destruct Hf as [left [right Heq]].
        apply (proj1 (semi_internal_decomposition (rank w) es) Hinternal
          left f (right ++ [e])).
        - rewrite Hsplit, Heq; rewrite <- app_assoc; reflexivity.
        - intro Hempty; apply app_eq_nil in Hempty; destruct Hempty as [_ Hfalse]; discriminate. }
      assert (Hu : semi_live EV r u) by (apply (proj1 (semi_path_live _ _ _ Hfirstpath Hs))).
      assert (Hrank : Pos.lt (rank w) (rank u)).
      { destruct (semi_path_last s first u Hfirstpath Hfirst)
          as [pre [f [Hlast [_ [_ Htargetf]]]]].
        rewrite <- Htargetf; apply Hhigh; rewrite Hparts, Hlast.
        apply in_or_app; left; apply in_or_app; right; left; reflexivity. }
      exists u; split; [exact Hrank|]; split.
      * eapply semi_path_region; [exact Hu|exact Hlastpath|exact Hu|apply rt_refl|].
        intros f Hf; apply Hminimum; rewrite Hparts; apply in_or_app; right; exact Hf.
      * apply semi_path_characterization; split; [exact Hs|]; split; [exact Hu|].
        exists first; auto.
Qed.

Lemma semidominator_unique u v n : semidominator EV g r u n ->
  semidominator EV g r v n -> u = v.
Proof.
  intros [Hupath [a [Ha Humin]]] [Hvpath [b [Hb Hvmin]]].
  destruct (Humin v Hvpath) as [b' [Hb' Hab]].
  destruct (Hvmin u Hupath) as [a' [Ha' Hba]].
  rewrite Ha in Ha'; injection Ha' as <-; rewrite Hb in Hb'; injection Hb' as <-.
  assert (Heq : a = b) by (apply Pos.le_antisym; assumption).
  apply (semi_number_injective EV g r root Hsearch u v); try (eexists; eauto).
  rewrite (semi_rank_numbered EV r u a Ha), (semi_rank_numbered EV r v b Hb); exact Heq.
Qed.

Lemma semi_root_parent_none : Map.get EV root (tree_edge r) = None.
Proof.
  destruct (Map.get EV root (tree_edge r)) as [e|] eqn:Hget; [|reflexivity].
  destruct (semi_parent_numbered _ _ _ _ Hsearch root e Hget) as [_ [Hs [_ [_ Hlt]]]].
  pose proof (semi_search_rooted _ _ _ _ Hsearch _ Hs) as Hancestor.
  destruct (semi_ancestor_order EV g r root Hsearch _ _ Hancestor) as [Heq|Hrank].
  - rewrite <- Heq in Hlt; exfalso; exact (Pos.lt_irrefl _ Hlt).
  - exfalso; apply Pos2Nat.inj_lt in Hrank, Hlt; lia.
Qed.

Lemma semi_parent_exists v : semi_live EV r v -> v <> root ->
  exists e, Map.get EV v (tree_edge r) = Some e.
Proof.
  intros Hv Hdistinct; destruct (Map.get EV v (tree_edge r)) as [e|] eqn:Hget; [eauto|].
  exfalso; apply Hdistinct; apply (semi_unlinked_entry _ _ _ _ Hsearch); assumption.
Qed.

Lemma semi_semidominator_bound u v : v <> root -> semidominator EV g r u v ->
  Pos.lt (rank u) (rank v).
Proof.
  intros Hdistinct [Hpath [k [Hk Hminimum]]].
  destruct (proj1 (semi_path_characterization u v) Hpath) as [_ [Hv _]].
  destruct (semi_parent_exists v Hv Hdistinct) as [e He].
  destruct (semi_parent_numbered _ _ _ _ Hsearch v e He) as [_ [Hs [Hedge [Ht Hlt]]]].
  pose proof (semi_single_edge e Hs Hedge) as Hcandidate; rewrite Ht in Hcandidate.
  destruct (Hminimum _ Hcandidate) as [j [Hj Hle]].
  rewrite (semi_rank_numbered EV r _ k Hk), (semi_rank_numbered EV r _ j Hj) in *.
  eapply Pos.le_lt_trans; eauto.
Qed.

(** At cutoff k the original forest contains exactly the tree links of vertices numbered above k. *)
Definition semi_cut_forest (k : positive) (st : SemiLinks.t V) : Prop :=
  forall v a, Map.get EV v (original st) = Some a <->
    tree_parent EV g r a v /\ Pos.lt k (rank v).

Lemma semi_cut_rank k st : semi_cut_forest k st ->
  forall v a, Map.get EV v (original st) = Some a -> Pos.lt (rank a) (rank v).
Proof.
  intros Hforest v a Hget; apply Hforest in Hget; destruct Hget as [[e [He Hsource]] _].
  rewrite <- Hsource; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
Qed.

Lemma semi_cut_root_low k st v : semi_cut_forest k st -> Pos.le (rank root) k ->
  semi_live EV r v -> Map.get EV v (original st) = None -> Pos.le (rank v) k.
Proof.
  intros Hforest Hroot Hv Hnone.
  destruct (Pos.leb (rank v) k) eqn:Hle; [apply Pos.leb_le; exact Hle|].
  apply Pos.leb_gt in Hle.
  destruct (dfs_eq_dec EV v root) as [Heq|Hdistinct]; [subst v; exact Hroot|].
  destruct (semi_parent_exists v Hv Hdistinct) as [e He].
  assert (Hsome : Map.get EV v (original st) = Some (Graph.source g e)).
  { apply Hforest; split; [exists e; auto|exact Hle]. }
  congruence.
Qed.

Lemma semi_cut_segment_live k st v a xs : semi_cut_forest k st ->
  semi_segment EV (original st) v a xs -> semi_live EV r v -> semi_live EV r a.
Proof.
  intros Hforest Hsegment; induction Hsegment as [v|v b a xs Hlink Hsegment IH]; intro Hv;
    [exact Hv|].
  apply IH; apply Hforest in Hlink; destruct Hlink as [[e [He Hsource]] _].
  rewrite <- Hsource; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
Qed.

Lemma semi_cut_segment_members k st v a xs : semi_cut_forest k st ->
  semi_segment EV (original st) v a xs -> forall u, In u xs ->
  Pos.lt k (rank u) /\ semi_live EV r u /\ dfs_ancestor EV g r u v.
Proof.
  intros Hforest Hsegment; induction Hsegment as [v|v b a xs Hlink Hsegment IH];
    intros u Hin; [contradiction|].
  apply Hforest in Hlink; destruct Hlink as [Hparent Hhigh].
  destruct Hin as [Heq|Hin].
  - subst u; split; [exact Hhigh|]; split; [|apply rt_refl].
    destruct Hparent as [e [He _]]; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
  - destruct (IH u Hin) as [Hrank [Hlive Hancestor]].
    split; [exact Hrank|]; split; [exact Hlive|].
    eapply rt_trans; [exact Hancestor|apply rt_step; exact Hparent].
Qed.

Lemma semi_cut_segment_covers k st v a xs : semi_cut_forest k st ->
  semi_segment EV (original st) v a xs -> Pos.le (rank a) k -> forall u,
  Pos.lt k (rank u) -> dfs_ancestor EV g r u v -> In u xs.
Proof.
  intros Hforest Hsegment; induction Hsegment as [v|v b a xs Hlink Hsegment IH];
    intros Hlow u Hhigh Hancestor.
  - destruct (semi_ancestor_order EV g r root Hsearch u v Hancestor) as [Heq|Hrank].
    + rewrite Heq in Hhigh; apply Pos2Nat.inj_le in Hlow; apply Pos2Nat.inj_lt in Hhigh; lia.
    + apply Pos2Nat.inj_lt in Hrank, Hhigh; apply Pos2Nat.inj_le in Hlow; lia.
  - destruct (dfs_eq_dec EV u v) as [Heq|Hdistinct]; [left; symmetry; exact Heq|right].
    apply Hforest in Hlink; destruct Hlink as [[e [He Hsource]] _].
    pose proof (clos_rt_rtn1 V (tree_parent EV g r) u v Hancestor) as Hchain.
    inversion Hchain as [|p q [f [Hf Hsource']] Hprefix]; subst.
    + contradiction.
    + rewrite He in Hf; inversion Hf; subst f.
      apply IH; [exact Hlow|exact Hhigh|].
      apply (clos_rtn1_rt V (tree_parent EV g r)); exact Hprefix.
Qed.

(** Eval minimizes every high ancestor of the predecessor and preserves the cutoff forest. *)
Lemma semi_eval_minima k score st v : semi_links_valid EV score st ->
  semi_cut_forest k st -> Pos.le (rank root) k -> semi_live EV r v ->
  let '(st', best) := semi_eval EV rank score st v in
  original st' = original st /\ semi_links_valid EV score st' /\
  ((best = v /\ Pos.le (rank v) k) \/
    (Pos.lt k (rank best) /\ semi_live EV r best /\ dfs_ancestor EV g r best v)) /\
  Pos.le (score best) (score v) /\
  forall u, Pos.lt k (rank u) -> dfs_ancestor EV g r u v -> Pos.le (score best) (score u).
Proof.
  intros Hvalid Hforest Hroot Hv.
  pose proof (semi_compress_correct EV rank score st Hvalid (semi_cut_rank k st Hforest) v)
    as Hquery.
  unfold semi_eval; destruct (semi_compress EV rank score st v) as [st' [a part]] eqn:Hrun.
  cbn [semi_query_valid] in Hquery.
  destruct Hquery as [Horiginal [Hvalid' [Hnone [xs [Hsegment Hminimum]]]]].
  pose proof (semi_cut_segment_live k st v a xs Hforest Hsegment Hv) as Ha.
  pose proof (semi_cut_root_low k st a Hforest Hroot Ha Hnone) as Hlow.
  split; [exact Horiginal|]; split; [exact Hvalid'|].
  destruct part as [best|]; cbn.
  - destruct Hminimum as [Hnonempty [Hin Hmin]].
    split; [right; eapply semi_cut_segment_members; eauto|]; split.
    + apply Hmin; inversion Hsegment; subst; [contradiction|left; reflexivity].
    + intros u Hhigh Hancestor; apply Hmin.
      eapply semi_cut_segment_covers; eauto.
  - subst xs; inversion Hsegment; subst a; split; [left; auto|]; split; [apply Pos.le_refl|].
    intros u Hhigh Hancestor.
    pose proof (semi_cut_segment_covers k st v v [] Hforest Hsegment Hlow u Hhigh Hancestor)
      as Hfalse; contradiction.
Qed.

End SemiPathTheory.

(** * Settlement invariants *)

(** Settled bindings are exact, and original links follow precisely their discovery parents. *)
Record semi_settled {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (root : V) (done : list V) (st : SemiState.t V) : Prop := {
  semi_settled_sound : forall v u, Map.get EV v (result st) = Some u ->
    In v done /\ v <> root /\ semidominator EV g r u v;
  semi_settled_total : forall v, In v done -> v <> root -> Map.get EV v (result st) <> None;
  semi_original_agrees : forall v, Map.get EV v (original (links st)) =
    match Map.get EV v (result st) with
    | None => None
    | Some _ => option_map (Graph.source g) (Map.get EV v (tree_edge r))
    end;
  semi_settled_links : semi_links_valid EV
    (fun v => semi_rank EV r (semi_value EV (result st) v)) (links st)
}.

(** Above the current cutoff every visited vertex has a settled, exact semidominator. *)
Record semi_values_ready {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    (root : V) (k : positive) (semis : Map.t V V) : Prop := {
  semi_values_sound : forall v u, Map.get EV v semis = Some u ->
    v <> root /\ semidominator EV g r u v;
  semi_values_domain : forall v, semi_live EV r v ->
    (Map.get EV v semis <> None <-> Pos.lt k (semi_rank EV r v))
}.

Section SemiSettlement.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (root : V).
Hypothesis Hsearch : semi_search_laws EV g r root.
Local Abbreviation rank := (semi_rank EV r).
Local Abbreviation score semis := (fun v => rank (semi_value EV semis v)).

Lemma semi_value_bound k semis v : semi_values_ready EV g r root k semis ->
  Pos.le (score semis v) (rank v).
Proof.
  intro Hvalues; unfold semi_value.
  destruct (Map.get EV v semis) as [u|] eqn:Hget; [|apply Pos.le_refl].
  destruct (semi_values_sound _ _ _ _ _ _ Hvalues v u Hget) as [Hdistinct Hsemi].
  apply Pos.lt_le_incl; eapply semi_semidominator_bound; eauto.
Qed.

Lemma semi_values_low k semis v : semi_values_ready EV g r root k semis ->
  semi_live EV r v -> Pos.le (rank v) k -> Map.get EV v semis = None.
Proof.
  intros Hvalues Hv Hlow; destruct (Map.get EV v semis) as [u|] eqn:Hget;
    [|reflexivity].
  assert (Hhigh : Pos.lt k (rank v)).
  { apply (semi_values_domain _ _ _ _ _ _ Hvalues v Hv); rewrite Hget; discriminate. }
  apply Pos2Nat.inj_lt in Hhigh; apply Pos2Nat.inj_le in Hlow; lia.
Qed.

(** The predecessor bound includes its own rank and every already settled ancestor's score. *)
Definition semi_incoming_bound (w : V) (semis : Map.t V V) (e : E) (best : V) : Prop :=
  Pos.le (rank best) (rank (Graph.source g e)) /\
  forall u, Pos.lt (rank w) (rank u) -> dfs_ancestor EV g r u (Graph.source g e) ->
    Pos.le (rank best) (score semis u).

Lemma semi_incoming_lower w semis e a b : Pos.le (rank a) (rank b) ->
  semi_incoming_bound w semis e b -> semi_incoming_bound w semis e a.
Proof.
  intros Hle [Hsource Hall]; split.
  - eapply Pos.le_trans; eauto.
  - intros u Hhigh Hancestor; eapply Pos.le_trans; [exact Hle|apply Hall; assumption].
Qed.

Lemma semi_eval_candidate w semis st e :
  semi_values_ready EV g r root (rank w) semis ->
  semi_links_valid EV (score semis) st -> semi_cut_forest EV g r (rank w) st ->
  Pos.le (rank root) (rank w) -> semi_live EV r (Graph.source g e) ->
  In e (Graph.out g (Graph.source g e)) -> Graph.target g e = w ->
  let '(st', best) := semi_eval EV rank (score semis) st (Graph.source g e) in
  original st' = original st /\ semi_links_valid EV (score semis) st' /\
  semidom_path EV g r (semi_value EV semis best) w /\
  semi_incoming_bound w semis e (semi_value EV semis best).
Proof.
  intros Hvalues Hvalid Hforest Hroot Hsource Hedge Htarget.
  pose proof (semi_eval_minima EV g r root Hsearch (rank w) (score semis) st _
    Hvalid Hforest Hroot Hsource) as Hquery.
  destruct (semi_eval EV rank (score semis) st (Graph.source g e)) as [st' best] eqn:Hrun.
  destruct Hquery as [Horiginal [Hvalid' [Hbest [Hscore Hall]]]].
  split; [exact Horiginal|]; split; [exact Hvalid'|]; split.
  - destruct Hbest as [[Heq Hlow]|[Hhigh [Hlive Hancestor]]].
    + subst best; unfold semi_value.
      rewrite (semi_values_low (rank w) semis _ Hvalues Hsource Hlow).
      rewrite <- Htarget; apply (semi_single_edge EV g r root Hsearch e Hsource Hedge).
    + assert (Hsome : Map.get EV best semis <> None).
      { apply (semi_values_domain _ _ _ _ _ _ Hvalues best Hlive); exact Hhigh. }
      unfold semi_value; destruct (Map.get EV best semis) as [u|] eqn:Hget;
        [|contradiction].
      destruct (semi_values_sound _ _ _ _ _ _ Hvalues best u Hget) as [_ [Hpath _]].
      eapply semi_path_extend; eauto.
  - split.
    + eapply Pos.le_trans; [exact Hscore|apply (semi_value_bound (rank w) semis _ Hvalues)].
    + exact Hall.
Qed.

Lemma semi_predecessor_correct w semis es st best :
  semi_values_ready EV g r root (rank w) semis ->
  semi_links_valid EV (score semis) st -> semi_cut_forest EV g r (rank w) st ->
  Pos.le (rank root) (rank w) -> semidom_path EV g r best w ->
  (forall e, In e es -> In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = w) ->
  let '(st', best') := fold_left (semi_predecessor EV g r semis) es (st, best) in
  original st' = original st /\ semi_links_valid EV (score semis) st' /\
  semidom_path EV g r best' w /\ Pos.le (rank best') (rank best) /\
  forall e, In e es -> semi_live EV r (Graph.source g e) ->
    semi_incoming_bound w semis e best'.
Proof.
  intros Hvalues; revert st best; induction es as [|e es IH];
    intros st best Hvalid Hforest Hroot Hpath Hedges.
  - cbn [fold_left]; split; [reflexivity|]; split; [exact Hvalid|];
      split; [exact Hpath|]; split; [apply Pos.le_refl|intros e Hfalse; contradiction].
  - destruct (Hedges e (or_introl eq_refl)) as [Hedge Htarget].
    assert (Htail : forall f, In f es ->
      In f (Graph.out g (Graph.source g f)) /\ Graph.target g f = w).
    { intros f Hf; apply Hedges; right; exact Hf. }
    cbn [fold_left semi_predecessor].
    destruct (Map.get EV (Graph.source g e) (pre_num r)) as [number|] eqn:Hnumber.
    + assert (Hsource : semi_live EV r (Graph.source g e)) by (exists number; exact Hnumber).
      pose proof (semi_eval_candidate w semis st e Hvalues Hvalid Hforest Hroot Hsource
        Hedge Htarget) as Hquery.
      destruct (semi_eval EV rank (score semis) st (Graph.source g e)) as [st1 chosen] eqn:Hrun.
      destruct Hquery as [Horiginal [Hvalid1 [Hcandidate Hbound]]].
      set (best1 := semi_min rank best (semi_value EV semis chosen)).
      assert (Hpath1 : semidom_path EV g r best1 w).
      { unfold best1.
        destruct (semi_min_member rank best (semi_value EV semis chosen)) as [Heq|Heq];
          rewrite Heq; assumption. }
      assert (Hforest1 : semi_cut_forest EV g r (rank w) st1).
      { unfold semi_cut_forest in *; rewrite Horiginal; exact Hforest. }
      specialize (IH st1 best1 Hvalid1 Hforest1 Hroot Hpath1 Htail).
      destruct (fold_left (semi_predecessor EV g r semis) es (st1, best1))
        as [st2 best2] eqn:Hrest.
      destruct IH as [Horiginal2 [Hvalid2 [Hpath2 [Hle2 Hall]]]].
      split; [congruence|]; split; [exact Hvalid2|]; split; [exact Hpath2|]; split.
      * eapply Pos.le_trans; [exact Hle2|apply (proj1 (semi_min_bounds rank _ _))].
      * intros f [Heq|Hf] Hlive.
        -- subst f; apply (semi_incoming_lower w semis e best2 best1 Hle2).
           apply (semi_incoming_lower w semis e best1 (semi_value EV semis chosen));
             [apply (proj2 (semi_min_bounds rank _ _))|exact Hbound].
        -- apply Hall; assumption.
    + specialize (IH st best Hvalid Hforest Hroot Hpath Htail).
      destruct (fold_left (semi_predecessor EV g r semis) es (st, best)) as [st' best'] eqn:Hrest.
      destruct IH as [Horiginal [Hvalid' [Hpath' [Hle Hall]]]].
      split; [exact Horiginal|]; split; [exact Hvalid'|]; split; [exact Hpath'|]; split;
        [exact Hle|].
      intros f [Heq|Hf] Hlive.
      * subst f; destruct Hlive as [k Hk]; rewrite Hnumber in Hk; discriminate.
      * apply Hall; assumption.
Qed.

Lemma semi_root_bound w : semi_live EV r w -> Pos.le (rank root) (rank w).
Proof.
  intro Hw; destruct (semi_ancestor_order EV g r root Hsearch root w
    (semi_search_rooted _ _ _ _ Hsearch w Hw)) as [Heq|Hlt].
  - rewrite Heq; apply Pos.le_refl.
  - apply Pos.lt_le_incl; exact Hlt.
Qed.

Lemma semi_settled_values done st w : semi_settled EV g r root done st ->
  semi_live EV r w -> (forall v, semi_live EV r v ->
    (In v done <-> Pos.lt (rank w) (rank v))) ->
  semi_values_ready EV g r root (rank w) (result st).
Proof.
  intros Hsettled Hw Hcut; constructor.
  - intros v u Hget; exact (proj2 (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget)).
  - intros v Hv; split.
    + intro Hsome; destruct (Map.get EV v (result st)) as [u|] eqn:Hget; [|contradiction].
      apply Hcut; [exact Hv|apply (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget)].
    + intro Hhigh; apply (semi_settled_total _ _ _ _ _ _ Hsettled).
      * apply Hcut; assumption.
      * intro Heq; subst v; pose proof (semi_root_bound w Hw) as Hlow.
        apply Pos2Nat.inj_lt in Hhigh; apply Pos2Nat.inj_le in Hlow; lia.
Qed.

Lemma semi_settled_forest done st w : semi_settled EV g r root done st ->
  semi_values_ready EV g r root (rank w) (result st) ->
  semi_cut_forest EV g r (rank w) (links st).
Proof.
  intros Hsettled Hvalues v a; rewrite (semi_original_agrees _ _ _ _ _ _ Hsettled v).
  destruct (Map.get EV v (result st)) as [u|] eqn:Hvalue.
  - destruct (Map.get EV v (tree_edge r)) as [e|] eqn:Hedge; cbn [option_map].
    + split.
      * intro Heq; injection Heq as Heq; split; [exists e; auto|].
        apply (semi_values_domain _ _ _ _ _ _ Hvalues v).
        -- apply (semi_parent_numbered _ _ _ _ Hsearch v e Hedge).
        -- rewrite Hvalue; discriminate.
      * intros [[f [Hf Hsource]] _]; rewrite Hedge in Hf; injection Hf as <-;
          now rewrite Hsource.
    + split; [discriminate|intros [[f [Hf _]] _]; congruence].
  - split; [discriminate|].
    intros [[e [He _]] Hhigh].
    assert (Hv : semi_live EV r v) by (apply (semi_parent_numbered _ _ _ _ Hsearch v e He)).
    pose proof (proj2 (semi_values_domain _ _ _ _ _ _ Hvalues v Hv) Hhigh) as Hsome;
      contradiction.
Qed.

Lemma semi_settled_rescore done st w best ls : semi_settled EV g r root done st ->
  Map.get EV w (result st) = None -> original ls = original (links st) ->
  semi_links_valid EV (score (result st)) ls ->
  semi_links_valid EV (score (Map.set EV w best (result st))) ls.
Proof.
  intros Hsettled Hnone Horiginal Hvalid; eapply semi_links_rescore; [exact Hvalid|].
  intros v a Hget; rewrite Horiginal, (semi_original_agrees _ _ _ _ _ _ Hsettled v) in Hget.
  assert (Hdistinct : v <> w).
  { intro Heq; subst v; rewrite Hnone in Hget; discriminate. }
  unfold semi_value; rewrite Map.get_set_other by exact Hdistinct; reflexivity.
Qed.

Lemma semi_live_number v : semi_live EV r v -> Map.get EV v (pre_num r) = Some (rank v).
Proof.
  intros [k Hk]; now rewrite (semi_rank_numbered EV r v k Hk).
Qed.

Lemma semi_predecessor_exact (p : prepared EV g) semis w best : ready EV g p ->
  semi_live EV r w -> semi_values_ready EV g r root (rank w) semis ->
  semidom_path EV g r best w ->
  (forall e, In e (pred_edges p w) -> semi_live EV r (Graph.source g e) ->
    semi_incoming_bound w semis e best) -> semidominator EV g r best w.
Proof.
  intros Hready Hw Hvalues Hpath Hall.
  assert (Hminimal : forall s, semidom_path EV g r s w -> Pos.le (rank best) (rank s)).
  {
    intros s Hsemi.
    destruct (semi_path_predecessor EV g r root Hsearch s w Hsemi)
      as [e [He [Ht [Hsource Hsplit]]]].
    assert (Hin : In e (pred_edges p w)).
    { destruct Hready as [Hwf [_ Hprepared]].
      apply (pred_agrees Hprepared w e (reachable_in_nodes g w Hwf
        (proj1 (semi_live_exact _ _ _ _ Hsearch w) Hw))).
      exists (Graph.source g e); split.
      - apply reachable_in_nodes; [exact Hwf|].
        apply (semi_live_exact _ _ _ _ Hsearch); exact Hsource.
      - auto. }
    destruct (Hall e Hin Hsource) as [Hdirect Hancestors].
    destruct Hsplit as [Heq|[u [Hhigh [Hancestor Hprefix]]]].
    - now rewrite Heq.
    - assert (Hu : semi_live EV r u).
      { destruct Hprefix as [es [k [h [_ [_ [Hk _]]]]]]; exists k; exact Hk. }
      pose proof (proj2 (semi_values_domain _ _ _ _ _ _ Hvalues u Hu) Hhigh) as Hsome.
      destruct (Map.get EV u semis) as [v|] eqn:Hget; [|contradiction].
      destruct (semi_values_sound _ _ _ _ _ _ Hvalues u v Hget)
        as [_ [_ [k [Hk Hminimum]]]].
      destruct (Hminimum s Hprefix) as [j [Hj Hle]].
      specialize (Hancestors u Hhigh Hancestor); unfold semi_value in Hancestors;
        rewrite Hget in Hancestors.
      rewrite <- (semi_rank_numbered EV r v k Hk), <- (semi_rank_numbered EV r s j Hj) in Hle.
      eapply Pos.le_trans; eauto.
  }
  split; [exact Hpath|]; exists (rank best); split.
  - apply semi_live_number; destruct Hpath as [es [k [h [_ [_ [_ [Hh _]]]]]]].
    exists h; exact Hh.
  - intros s Hsemi; exists (rank s); split.
    + apply semi_live_number; destruct Hsemi as [es [k [h [_ [_ [_ [Hh _]]]]]]].
      exists h; exact Hh.
    + apply Hminimal; exact Hsemi.
Qed.

Lemma semi_settled_insert done st w edge ls best : semi_settled EV g r root done st ->
  Map.get EV w (result st) = None -> Map.get EV w (tree_edge r) = Some edge -> w <> root ->
  original ls = original (links st) -> semi_links_valid EV (score (result st)) ls ->
  semidominator EV g r best w ->
  semi_settled EV g r root (w :: done)
    (SemiState.Make (Map.set EV w best (result st)) (semi_link EV ls w (Graph.source g edge))).
Proof.
  intros Hsettled Hnone Htree Hdistinct Horiginal Hvalid Hexact.
  constructor; cbn [result links semi_link original].
  - intros v u Hget; destruct (dfs_eq_dec EV v w) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same in Hget; injection Hget as <-.
      split; [left; reflexivity|auto].
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget) as [Hin Hsound].
      split; [right; exact Hin|exact Hsound].
  - intros v [Heq|Hin] Hnonroot.
    + subst v; rewrite Map.get_set_same; discriminate.
    + destruct (dfs_eq_dec EV v w) as [Heq|Hne];
        [subst v; rewrite Map.get_set_same; discriminate|].
      rewrite Map.get_set_other by exact Hne; apply (semi_settled_total _ _ _ _ _ _ Hsettled);
        assumption.
  - intro v; destruct (dfs_eq_dec EV v w) as [Heq|Hne].
    + subst v; rewrite !Map.get_set_same, Htree; reflexivity.
    + rewrite !Map.get_set_other by exact Hne; rewrite Horiginal.
      apply (semi_original_agrees _ _ _ _ _ _ Hsettled).
  - apply semi_link_valid.
    + eapply semi_settled_rescore; eauto.
    + rewrite Horiginal, (semi_original_agrees _ _ _ _ _ _ Hsettled w), Hnone; reflexivity.
Qed.

Lemma semi_settle_exact (p : prepared EV g) done st w : ready EV g p ->
  semi_settled EV g r root done st -> semi_live EV r w ->
  (forall v, semi_live EV r v -> (In v done <-> Pos.lt (rank w) (rank v))) ->
  semi_settled EV g r root (w :: done) (semi_settle p r st w).
Proof.
  intros Hready Hsettled Hw Hcut.
  assert (Hnone : Map.get EV w (result st) = None).
  { destruct (Map.get EV w (result st)) as [u|] eqn:Hget; [|reflexivity].
    destruct (semi_settled_sound _ _ _ _ _ _ Hsettled w u Hget) as [Hin _].
    apply (proj1 (Hcut w Hw)) in Hin; exfalso; exact (Pos.lt_irrefl _ Hin). }
  unfold semi_settle; destruct (Map.get EV w (tree_edge r)) as [edge|] eqn:Htree.
  - pose proof (semi_settled_values done st w Hsettled Hw Hcut) as Hvalues.
    pose proof (semi_settled_forest done st w Hsettled Hvalues) as Hforest.
    destruct (semi_parent_numbered _ _ _ _ Hsearch w edge Htree)
      as [_ [Hparent [Hedge [Htarget Hparentrank]]]].
    assert (Hparentpath : semidom_path EV g r (Graph.source g edge) w).
    { rewrite <- Htarget; apply (semi_single_edge EV g r root Hsearch edge Hparent Hedge). }
    assert (Hedges : forall e, In e (pred_edges p w) ->
      In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = w).
    { intros e Hin; destruct Hready as [Hwf [_ Hprepared]].
      apply (pred_agrees Hprepared w e (reachable_in_nodes g w Hwf
        (proj1 (semi_live_exact _ _ _ _ Hsearch w) Hw))) in Hin.
      destruct Hin as [v [_ [He Ht]]]; rewrite (out_source Hwf v e He); auto. }
    pose proof (semi_predecessor_correct w (result st) (pred_edges p w) (links st)
      (Graph.source g edge) Hvalues (semi_settled_links _ _ _ _ _ _ Hsettled) Hforest
      (semi_root_bound w Hw) Hparentpath Hedges) as Hfold.
    destruct (fold_left (semi_predecessor EV g r (result st)) (pred_edges p w)
      (links st, Graph.source g edge)) as [ls best] eqn:Hrun.
    destruct Hfold as [Horiginal [Hvalid [Hpath [Hbound Hall]]]].
    assert (Hdistinct : w <> root).
    { intro Heq; rewrite Heq, (semi_root_parent_none EV g r root Hsearch) in Htree;
        discriminate. }
    pose proof (semi_predecessor_exact p (result st) w best Hready Hw Hvalues Hpath Hall)
      as Hexact.
    eapply semi_settled_insert; eauto.
  - assert (Heq : w = root) by (apply (semi_unlinked_entry _ _ _ _ Hsearch); assumption).
    constructor.
    + intros v u Hget; destruct (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget)
        as [Hin Hsound]; split; [right; exact Hin|exact Hsound].
    + intros v [Hvw|Hin] Hdistinct; [subst v; contradiction|].
      apply (semi_settled_total _ _ _ _ _ _ Hsettled); assumption.
    + apply (semi_original_agrees _ _ _ _ _ _ Hsettled).
    + apply (semi_settled_links _ _ _ _ _ _ Hsettled).
Qed.

Lemma semi_settled_empty : semi_settled EV g r root []
  (SemiState.Make Map.empty semi_links_empty).
Proof.
  constructor; cbn [result links semi_links_empty original].
  - intros v u Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v Hfalse; contradiction.
  - intro v; rewrite !Map.get_empty; reflexivity.
  - apply semi_links_empty_valid.
Qed.

Lemma semi_reverse_fold (p : prepared EV g) todo done st : ready EV g p ->
  semi_settled EV g r root done st ->
  (forall v, semi_live EV r v <-> In v done \/ In v todo) ->
  (forall u v, before todo u v -> Pos.lt (rank v) (rank u)) ->
  (forall u v, In u done -> In v todo -> Pos.lt (rank v) (rank u)) ->
  exists final, (forall v, In v final <-> In v done \/ In v todo) /\
    semi_settled EV g r root final (fold_left (semi_settle p r) todo st).
Proof.
  intro Hready; revert done st; induction todo as [|w todo IH];
    intros done st Hsettled Hcover Horder Hgap.
  - exists done; split; [intro v; cbn; tauto|exact Hsettled].
  - assert (Hw : semi_live EV r w) by (apply Hcover; right; left; reflexivity).
    assert (Hhead : forall v, In v todo -> Pos.lt (rank v) (rank w)).
    { intros v Hv; apply Horder; apply (proj2 (dfs_before_cons todo w w v)); left; auto. }
    assert (Hcut : forall v, semi_live EV r v -> (In v done <-> Pos.lt (rank w) (rank v))).
    { intros v Hv; split.
      - intro Hin; apply Hgap; [exact Hin|left; reflexivity].
      - intro Hhigh; apply Hcover in Hv; destruct Hv as [Hin|[Heq|Hin]]; [exact Hin| |].
        + subst v; exfalso; exact (Pos.lt_irrefl _ Hhigh).
        + pose proof (Hhead v Hin) as Hlow; apply Pos2Nat.inj_lt in Hlow, Hhigh; lia. }
    pose proof (semi_settle_exact p done st w Hready Hsettled Hw Hcut) as Hsettled1.
    assert (Hcover1 : forall v, semi_live EV r v <-> In v (w :: done) \/ In v todo).
    { intro v; rewrite Hcover; cbn; tauto. }
    assert (Horder1 : forall u v, before todo u v -> Pos.lt (rank v) (rank u)).
    { intros u v Hbefore; apply Horder; apply (proj2 (dfs_before_cons todo w u v)); right;
        exact Hbefore. }
    assert (Hgap1 : forall u v, In u (w :: done) -> In v todo -> Pos.lt (rank v) (rank u)).
    { intros u v [Heq|Hin] Hv; [subst u; apply Hhead; exact Hv|].
      apply Hgap; [exact Hin|right; exact Hv]. }
    destruct (IH (w :: done) (semi_settle p r st w) Hsettled1 Hcover1 Horder1 Hgap1)
      as [final [Hfinal Hresult]].
    exists final; split; [intro v; rewrite Hfinal; cbn; tauto|exact Hresult].
Qed.

(** Reverse traversal settles every reached nonroot vertex to its unique path minimum. *)
Lemma semi_compute_exact (p : prepared EV g) : ready EV g p -> forall u n,
  (Map.get EV n (result (semi_compute p r)) = Some u <->
    semi_live EV r n /\ n <> root /\ semidominator EV g r u n).
Proof.
  intro Hready; destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
  set (todo := rev (preorder r)) in *.
  assert (Hlisting : forall v, semi_live EV r v <-> In v todo).
  { intro v; apply (dfs_numbering_domain EV todo (pre_num r) next Hnumber). }
  assert (Horder : forall u v, before todo u v -> Pos.lt (rank v) (rank u)).
  { intros u v Hbefore.
    pose proof (proj1 (dfs_before_indices todo u v) Hbefore) as [i [j [_ [Hi Hj]]]].
    assert (Hu : semi_live EV r u) by (apply Hlisting; eapply nth_error_In; exact Hi).
    assert (Hv : semi_live EV r v) by (apply Hlisting; eapply nth_error_In; exact Hj).
    apply (proj1 (dfs_numbering_order EV todo (pre_num r) next Hnumber v u (rank v) (rank u)
      (semi_live_number v Hv) (semi_live_number u Hu))).
    apply (proj1 (dfs_before_reverse todo u v)); exact Hbefore. }
  destruct (semi_reverse_fold p todo [] (SemiState.Make Map.empty semi_links_empty) Hready
    semi_settled_empty ltac:(intro v; rewrite Hlisting; cbn; tauto) Horder
    ltac:(intros u v Hfalse; contradiction)) as [final [Hfinal Hsettled]].
  change (semi_settled EV g r root final (semi_compute p r)) in Hsettled.
  intros u n; split.
  - intro Hget; destruct (semi_settled_sound _ _ _ _ _ _ Hsettled n u Hget)
      as [Hin [Hdistinct Hexact]].
    split; [apply Hlisting; apply Hfinal in Hin; destruct Hin as [Hfalse|Hin];
      [contradiction|exact Hin]|auto].
  - intros [Hlive [Hdistinct Hexact]].
    assert (Hin : In n final) by (apply Hfinal; right; apply Hlisting; exact Hlive).
    pose proof (semi_settled_total _ _ _ _ _ _ Hsettled n Hin Hdistinct) as Hsome.
    destruct (Map.get EV n (result (semi_compute p r))) as [v|] eqn:Hget; [|contradiction].
    destruct (semi_settled_sound _ _ _ _ _ _ Hsettled n v Hget) as [_ [_ Hvalue]].
    pose proof (semidominator_unique EV g r root Hsearch v u n Hvalue Hexact) as Heq.
    now rewrite Heq.
Qed.

End SemiSettlement.

(** Shared semidominator bindings are exactly the least-ranked paths on the fresh-root DFS. *)
Theorem semidominators_exact {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> forall u n,
  (Map.get (virtual_encoding EV) n (semidominators p) = Some u <->
   reachable (virtual_graph EV g) n /\ n <> inr tt /\
   semidominator (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p) u n).
Proof.
  intros Hready u n.
  pose proof (virtual_graph_ready EV g p Hready) as Hvirtual.
  pose proof (semi_single_search_laws (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (inr tt) Hvirtual eq_refl) as Hsearch.
  pose proof (semi_compute_exact (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) Hsearch (virtual_prepared p) Hvirtual u n) as Hexact.
  rewrite (semi_live_exact _ _ _ _ Hsearch n) in Hexact; exact Hexact.
Qed.
