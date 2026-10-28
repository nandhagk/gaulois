(** * Lengauer--Tarjan dominators

    Indexed buckets settle provisional parents using shared linked-path minima; a forward
    traversal corrects those parents before removing the fresh virtual root.
    For example, the join of a diamond has the branch vertex as its immediate dominator.
    Builds on: GraphSemiDominators, GraphDominance and Collections maps. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat Permutation.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators.
Import List.ListNotations.

(** * Indexed bucket settlement and correction *)

(** Apart from the shared search and semidominator phase, the outer passes visit each vertex
    and bucket membership a constant number of times. Charge link/eval segment traversal
    separately. Trie operations cost the encoded key length, rank comparisons cost their
    binary lengths, and erasure enumeration includes trie traversal and emitted key bits.
    These are source-level operation counts, not a proved transfer of the paper's array bound. *)

Definition lt_bucket {V} (EV : encoding V) (buckets : Map.t V (list V)) (s : V) : list V :=
  match Map.get EV s buckets with
  | None => []
  | Some members => members
  end.

Definition lt_bucket_insert {V} (EV : encoding V) (semis : Map.t V V)
    (buckets : Map.t V (list V)) (v : V) : Map.t V (list V) :=
  match Map.get EV v semis with
  | None => buckets
  | Some s => Map.set EV s (v :: lt_bucket EV buckets s) buckets
  end.

(** All semidominators are available before settlement, so their buckets are indexed once. *)
Definition lt_bucket_index {V} (EV : encoding V) (semis : Map.t V V) (order : list V)
    : Map.t V (list V) :=
  fold_left (lt_bucket_insert EV semis) order Map.empty.

Lemma lt_bucket_insert_in {V} (EV : encoding V) semis buckets x s v :
  In v (lt_bucket EV (lt_bucket_insert EV semis buckets x) s) <->
  (v = x /\ Map.get EV x semis = Some s) \/ In v (lt_bucket EV buckets s).
Proof.
  unfold lt_bucket_insert; destruct (Map.get EV x semis) as [a|] eqn:Hsemi.
  - destruct (dfs_eq_dec EV s a) as [Heq|Hdistinct].
    + subst s; unfold lt_bucket at 1; rewrite Map.get_set_same; cbn; split.
      * intros [Heq|Hin]; [left; split; [symmetry; exact Heq|reflexivity]|right; exact Hin].
      * intros [[Heq _]|Hin]; [left; symmetry; exact Heq|right; exact Hin].
    + unfold lt_bucket at 1; rewrite Map.get_set_other by exact Hdistinct; split.
      * intro Hin; right; exact Hin.
      * intros [[_ Heq]|Hin]; [injection Heq as Heq; exfalso; apply Hdistinct;
          symmetry; exact Heq|exact Hin].
  - split; [intro Hin; right; exact Hin|intros [[_ Hfalse]|Hin];
      [discriminate|exact Hin]].
Qed.

Lemma lt_bucket_fold_in {V} (EV : encoding V) semis order : forall buckets s v,
  In v (lt_bucket EV (fold_left (lt_bucket_insert EV semis) order buckets) s) <->
  In v (lt_bucket EV buckets s) \/ (In v order /\ Map.get EV v semis = Some s).
Proof.
  induction order as [|x order IH]; intros buckets s v; cbn [fold_left].
  - cbn; tauto.
  - rewrite IH, lt_bucket_insert_in; cbn [In]; split.
    + intros [[[Heq Hsemi]|Hin]|[Hin Hsemi]]; subst; auto.
    + intros [Hin|[[Heq|Hin] Hsemi]]; subst; auto.
Qed.

Lemma lt_bucket_index_in {V} (EV : encoding V) semis order s v :
  In v (lt_bucket EV (lt_bucket_index EV semis order) s) <->
  In v order /\ Map.get EV v semis = Some s.
Proof.
  unfold lt_bucket_index; rewrite lt_bucket_fold_in; unfold lt_bucket.
  rewrite Map.get_empty; cbn; tauto.
Qed.

Module LtState.

(** The reverse traversal threads compression changes and provisional parents together. *)
Record t (V : Type) : Type := Make {
  links : SemiLinks.t V;
  parents : Map.t V V
}.
Arguments Make {V}.
Arguments links {V}.
Arguments parents {V}.

End LtState.
Import LtState.

(** A bucket member either names the bucket root or defers to the minimum-score ancestor. *)
Definition lt_bucket_member {V E} (EV : encoding V) (r : dfs_result V E)
    (semis : Map.t V V) (s : V) (st : LtState.t V) (v : V) : LtState.t V :=
  let rank := semi_rank EV r in
  let score := fun x => rank (semi_value EV semis x) in
  let '(ls, u) := semi_eval EV rank score (links st) v in
  LtState.Make ls (Map.set EV v (if Pos.ltb (score u) (rank s) then u else s) (parents st)).

(** At a vertex, settle its bucket before linking that vertex to its DFS parent. *)
Definition lt_reverse_step {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) (buckets : Map.t V (list V))
    (st : LtState.t V) (s : V) : LtState.t V :=
  let st' := fold_left (lt_bucket_member EV r semis s) (lt_bucket EV buckets s) st in
  match Map.get EV s (tree_edge r) with
  | None => st'
  | Some e => LtState.Make (semi_link EV (links st') s (Graph.source g e)) (parents st')
  end.

(** Each bucket is read once in reverse discovery order; it needs no repeated membership scan. *)
Definition lt_provisional {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V :=
  let buckets := lt_bucket_index EV semis (preorder r) in
  parents (fold_left (lt_reverse_step EV g r semis buckets) (rev (preorder r))
    (LtState.Make semi_links_empty Map.empty)).

(** A deferred parent is corrected using its already settled immediate dominator. *)
Definition lt_correct_step {V} (EV : encoding V) (semis provisional : Map.t V V)
    (corrected : Map.t V V) (v : V) : Map.t V V :=
  match Map.get EV v provisional with
  | None => corrected
  | Some u =>
    let parent := if Pos.eqb (encode EV u) (encode EV (semi_value EV semis v))
      then u else semi_value EV corrected u in
    Map.set EV v parent corrected
  end.

(** Forward discovery order resolves every deferred parent after its earlier dependency. *)
Definition lt_compute {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V :=
  fold_left (lt_correct_step EV semis (lt_provisional EV g r semis)) (preorder r) Map.empty.

(** Simple LT erases fresh-root parent bindings after indexed settlement and correction. *)
Definition simple_lt_idom {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : Map.t V V :=
  let vp := virtual_prepared p in
  let r := dfs vp FinSet.empty [inr tt] in
  let semis := SemiState.result (semi_compute vp r) in
  erase_virtual_parents EV
    (lt_compute (virtual_encoding EV) (virtual_graph EV g) r semis).

(** * Semidominator cuts characterize dominance *)

Section LtCuts.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (root : V).
Hypothesis Hsearch : semi_search_laws EV g r root.
Hypothesis Hentries : Graph.entries g = [root].
Variable semis : Map.t V V.
Hypothesis Hsemis : forall v, semi_live EV r v -> v <> root ->
  semidominator EV g r (semi_value EV semis v) v.
Local Abbreviation rank := (semi_rank EV r).
Local Abbreviation sv := (semi_value EV semis).
Local Abbreviation anc := (dfs_ancestor EV g r).

(** A cut blocks every semidominator shortcut crossing its position on the tree path. *)
Definition lt_cut (d n : V) : Prop :=
  anc d n /\ forall w, anc w n -> Pos.lt (rank d) (rank w) ->
    Pos.le (rank d) (rank (sv w)).

Lemma lt_ancestor_rank u v : anc u v -> Pos.le (rank u) (rank v).
Proof.
  intro Hancestor; destruct (semi_ancestor_order EV g r root Hsearch u v Hancestor)
    as [Heq|Hlt]; [subst v; apply Pos.le_refl|apply Pos.lt_le_incl; exact Hlt].
Qed.

Lemma lt_ancestor_source_live u v : semi_live EV r v -> anc u v -> semi_live EV r u.
Proof.
  intros Hv Hancestor; induction Hancestor as [u v [e [He Hsource]]|u|
    u w v Huw IHuw Hwv IHwv].
  - subst u; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
  - exact Hv.
  - apply IHuw; apply IHwv; exact Hv.
Qed.

Lemma lt_root_live : semi_live EV r root.
Proof.
  apply (semi_live_exact _ _ _ _ Hsearch); constructor; rewrite Hentries; left; reflexivity.
Qed.

Lemma lt_semidominator_ancestor v : semi_live EV r v -> v <> root -> anc (sv v) v.
Proof.
  intros Hv Hnonroot; pose proof (Hsemis v Hv Hnonroot) as [Hpath _].
  pose proof (semi_semidominator_bound EV g r root Hsearch (sv v) v Hnonroot
    (Hsemis v Hv Hnonroot)) as Hlt.
  apply (semi_path_characterization EV g r root Hsearch) in Hpath.
  destruct Hpath as [Hs [_ [es [_ [Hpath Hinternal]]]]].
  eapply semi_path_region; [exact Hsearch|exact Hs|exact Hpath|exact Hs|apply rt_refl|].
  intros e He; apply Pos.lt_le_incl.
  eapply semi_internal_lower; eauto.
Qed.

Lemma lt_cut_refl v : lt_cut v v.
Proof.
  split; [apply rt_refl|]; intros w Hancestor Hlt.
  pose proof (lt_ancestor_rank w v Hancestor) as Hle.
  apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; exfalso; lia.
Qed.

Lemma lt_cut_prefix d u v : lt_cut d v -> anc u v -> Pos.le (rank d) (rank u) ->
  lt_cut d u.
Proof.
  intros [Hd Hcuts] Hu Hle; split.
  - eapply semi_ancestor_cut; eauto.
  - intros w Hw Hlt; apply Hcuts; [eapply rt_trans; eauto|exact Hlt].
Qed.

Lemma lt_cut_bound d v : lt_cut d v -> d <> v -> Pos.le (rank d) (rank (sv v)).
Proof.
  intros [Hancestor Hcuts] Hdistinct; apply Hcuts; [apply rt_refl|].
  destruct (semi_ancestor_order EV g r root Hsearch d v Hancestor) as [Heq|Hlt];
    [contradiction|exact Hlt].
Qed.

(** A tree path exposes the ancestry of every vertex that occurs along it. *)
Lemma lt_tree_path u v : anc u v -> exists es, path g u es v /\
  forall e, In e es -> anc u (Graph.target g e) /\ anc (Graph.target g e) v.
Proof.
  intro Hancestor; pose proof (clos_rt_rtn1 V (tree_parent EV g r) u v Hancestor) as Hchain.
  clear Hancestor.
  induction Hchain as [|a v [e [He Hsource]] Hchain IH].
  - exists []; split; [constructor|intros e Hfalse; contradiction].
  - destruct IH as [es [Hpath Hvertices]].
    destruct (semi_parent_numbered _ _ _ _ Hsearch v e He) as [_ [_ [Hedge [Htarget _]]]].
    assert (Hparent : anc a v) by (apply rt_step; exists e; auto).
    exists (es ++ [e]); split.
    + rewrite <- Htarget; eapply path_snoc; [exact Hpath|symmetry; exact Hsource|].
      now rewrite <- Hsource.
    + intros f Hf; apply in_app_or in Hf; destruct Hf as [Hf|[Heq|Hfalse]].
      * destruct (Hvertices f Hf) as [Hfirst Hlast]; split; [exact Hfirst|].
        eapply rt_trans; eauto.
      * subst f; rewrite Htarget; split; [|apply rt_refl].
        eapply rt_trans; [apply (clos_rtn1_rt V (tree_parent EV g r)); exact Hchain|
          exact Hparent].
      * contradiction.
Qed.

Lemma lt_dominates_ancestor d v : semi_live EV r v -> dominates g d v -> anc d v.
Proof.
  intros Hv Hdom.
  destruct (lt_tree_path root v (semi_search_rooted _ _ _ _ Hsearch v Hv))
    as [es [Hpath Hvertices]].
  destruct (Hdom root es ltac:(rewrite Hentries; left; reflexivity) Hpath)
    as [Heq|[e [He Htarget]]].
  - subst d; apply (semi_search_rooted _ _ _ _ Hsearch v Hv).
  - rewrite <- Htarget; exact (proj2 (Hvertices e He)).
Qed.

Lemma lt_dominates_prefix d w v : dominates g d v -> anc w v ->
  Pos.lt (rank d) (rank w) -> dominates g d w.
Proof.
  intros Hdom Hancestor Hlt s es Hentry Hpath.
  destruct (lt_tree_path w v Hancestor) as [suffix [Hsuffix Hvertices]].
  destruct (Hdom s (es ++ suffix) Hentry
    (semi_path_app g s es w suffix v Hpath Hsuffix))
    as [Heq|[e [He Htarget]]]; [left; exact Heq|].
  apply in_app_or in He; destruct He as [He|He]; [right; eauto|].
  destruct (Hvertices e He) as [Hfirst _]; rewrite Htarget in Hfirst.
  pose proof (lt_ancestor_rank w d Hfirst) as Hle.
  apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; exfalso; lia.
Qed.

Lemma lt_dominates_semi_bound d v : semi_live EV r v -> v <> root ->
  dominates g d v -> d <> v -> Pos.le (rank d) (rank (sv v)).
Proof.
  intros Hv Hnonroot Hdom Hdistinct.
  pose proof (lt_dominates_ancestor d v Hv Hdom) as Hancestor.
  destruct (semi_ancestor_order EV g r root Hsearch d v Hancestor)
    as [Heq|Hlt]; [contradiction|].
  destruct (Hsemis v Hv Hnonroot) as [Hsemipath _].
  apply (semi_path_characterization EV g r root Hsearch) in Hsemipath.
  destruct Hsemipath as [Hs [_ [suffix [_ [Hsuffix Hinternal]]]]].
  destruct (lt_tree_path root (sv v) (semi_search_rooted _ _ _ _ Hsearch _ Hs))
    as [prefix [Hprefix Hvertices]].
  destruct (Hdom root (prefix ++ suffix) ltac:(rewrite Hentries; left; reflexivity)
    (semi_path_app g _ _ _ _ _ Hprefix Hsuffix))
    as [Heq|[e [He Htarget]]].
  - subst d; apply lt_ancestor_rank; apply (semi_search_rooted _ _ _ _ Hsearch _ Hs).
  - apply in_app_or in He; destruct He as [He|He].
    + rewrite <- Htarget; apply lt_ancestor_rank; exact (proj2 (Hvertices e He)).
    + pose proof (semi_internal_lower EV g r (rank d) (sv v) suffix v
        Hsuffix Hinternal Hlt e He) as Hfalse.
      rewrite Htarget in Hfalse; exfalso; exact (Pos.lt_irrefl _ Hfalse).
Qed.

Lemma lt_dominates_cut d v : semi_live EV r v -> dominates g d v -> lt_cut d v.
Proof.
  intros Hv Hdom; split; [apply lt_dominates_ancestor; assumption|].
  intros w Hancestor Hlt.
  assert (Hw : semi_live EV r w) by (eapply lt_ancestor_source_live; eauto).
  assert (Hnonroot : w <> root).
  { intro Heq; subst w.
    pose proof (lt_ancestor_rank root d (semi_search_rooted _ _ _ _ Hsearch d
      (lt_ancestor_source_live d v Hv (lt_dominates_ancestor d v Hv Hdom)))) as Hle.
    apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; lia. }
  apply lt_dominates_semi_bound; [exact Hw|exact Hnonroot| |].
  - eapply lt_dominates_prefix; eauto.
  - intro Heq; subst w; exact (Pos.lt_irrefl _ Hlt).
Qed.

(** After the last vertex below a threshold, every remaining target is above it. *)
Lemma lt_high_suffix s es n k : path g s es n -> semi_live EV r s -> Pos.le k (rank n) ->
  (forall e, In e es -> Pos.le k (rank (Graph.target g e))) \/
  exists u suffix, path g u suffix n /\ semi_live EV r u /\ Pos.lt (rank u) k /\
    incl suffix es /\ forall e, In e suffix -> Pos.le k (rank (Graph.target g e)).
Proof.
  intro Hpath; induction Hpath as [s|e es n Hedge Hpath IH]; intros Hs Hn.
  - left; intros e Hfalse; contradiction.
  - pose proof (semi_live_step EV g r root Hsearch e Hs Hedge) as Htarget.
    destruct (IH Htarget Hn) as [Hall|[u [suffix [Hp [Hu [Hlow [Hin Hall]]]]]]].
    + destruct (Pos.leb k (rank (Graph.target g e))) eqn:Hcompare.
      * apply Pos.leb_le in Hcompare; left; intros f [Heq|Hf];
          [subst f; exact Hcompare|apply Hall; exact Hf].
      * apply Pos.leb_gt in Hcompare; right; exists (Graph.target g e), es.
        split; [exact Hpath|]; split; [exact Htarget|]; split; [exact Hcompare|].
        split; [intros f Hf; right; exact Hf|exact Hall].
    + right; exists u, suffix; split; [exact Hp|]; split; [exact Hu|];
        split; [exact Hlow|]; split; [|exact Hall].
      intros f Hf; right; apply Hin; exact Hf.
Qed.

Lemma lt_semi_minimum_bound u v : semi_live EV r v -> v <> root ->
  semidom_path EV g r u v -> Pos.le (rank (sv v)) (rank u).
Proof.
  intros Hv Hnonroot Hpath; destruct (Hsemis v Hv Hnonroot) as [_ [k [Hk Hminimum]]].
  destruct (Hminimum u Hpath) as [j [Hj Hle]].
  rewrite (semi_rank_numbered EV r _ k Hk), (semi_rank_numbered EV r _ j Hj); exact Hle.
Qed.

Lemma lt_live_rank_strict u v : semi_live EV r u -> semi_live EV r v -> u <> v ->
  Pos.le (rank u) (rank v) -> Pos.lt (rank u) (rank v).
Proof.
  intros Hu Hv Hdistinct Hle.
  assert (Hne : Pos.to_nat (rank u) <> Pos.to_nat (rank v)).
  { intro Heq; apply Hdistinct; eapply semi_number_injective; eauto;
      apply Pos2Nat.inj; exact Heq. }
  apply Pos2Nat.inj_le in Hle; apply Pos2Nat.inj_lt; lia.
Qed.

(** A path entering above a cut from below it would exhibit a forbidden semidominator. *)
Lemma lt_cut_low_suffix d n u suffix : semi_live EV r n -> lt_cut d n ->
  Pos.lt (rank root) (rank d) -> semi_live EV r u -> Pos.lt (rank u) (rank d) ->
  path g u suffix n ->
  (forall e, In e suffix -> Pos.le (rank d) (rank (Graph.target g e))) ->
  (forall e, In e suffix -> Graph.target g e <> d) -> False.
Proof.
  intros Hn [Hancestor Hcuts] Hrootlt Hu Hlow Hp Hall Havoid.
  assert (Hnonempty : suffix <> []).
  { intro Heq; subst suffix; apply dominance_path_nil_inv in Hp; subst u.
    pose proof (lt_ancestor_rank d n Hancestor) as Hle.
    apply Pos2Nat.inj_lt in Hlow; apply Pos2Nat.inj_le in Hle; lia. }
  destruct (semi_path_minimum EV g r u suffix n Hp Hnonempty)
    as [w [prefix [last [Hsplit [Hprefix [Hfirst [Hlast [Hinternal Hminimum]]]]]]]].
  destruct (semi_path_last g u prefix w Hfirst Hprefix)
    as [pre [e [Hlastedge [_ [_ Htarget]]]]].
  assert (Hmember : In e suffix).
  { rewrite Hsplit, Hlastedge; apply in_or_app; left.
    apply in_or_app; right; left; reflexivity. }
  assert (Hw : semi_live EV r w).
  { apply (proj1 (semi_path_live EV g r root Hsearch u prefix w Hfirst Hu)). }
  assert (Hhigh : Pos.le (rank d) (rank w)).
  { rewrite <- Htarget; apply Hall; rewrite Hsplit, Hlastedge; apply in_or_app; left.
    apply in_or_app; right; left; reflexivity. }
  assert (Hwn : anc w n).
  { eapply semi_path_region; [exact Hsearch|exact Hw|exact Hlast|exact Hw|apply rt_refl|].
    intros f Hf; apply Hminimum; rewrite Hsplit; apply in_or_app; right; exact Hf. }
  assert (Hdw : d <> w) by (intro Heq; subst d; apply (Havoid e Hmember); exact Htarget).
  assert (Hdwlt : Pos.lt (rank d) (rank w)).
  { apply lt_live_rank_strict; [exact (lt_ancestor_source_live d n Hn Hancestor)|exact Hw|
      exact Hdw|exact Hhigh]. }
  assert (Hwnonroot : w <> root).
  { intro Heq; rewrite Heq in Hdwlt.
    exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hrootlt Hdwlt)). }
  assert (Hsemipath : semidom_path EV g r u w).
  { apply (semi_path_characterization EV g r root Hsearch); split; [exact Hu|].
    split; [exact Hw|]; exists prefix; auto. }
  pose proof (lt_semi_minimum_bound u w Hw Hwnonroot Hsemipath) as Hbound.
  pose proof (Hcuts w Hwn Hdwlt) as Hcut.
  apply Pos2Nat.inj_le in Hbound, Hcut; apply Pos2Nat.inj_lt in Hlow; lia.
Qed.

Lemma lt_cut_dominates d n : semi_live EV r n -> lt_cut d n -> dominates g d n.
Proof.
  intros Hn Hcut s es Hentry Hpath.
  rewrite Hentries in Hentry; destruct Hentry as [Heq|Hfalse]; [subst s|contradiction].
  destruct (path_occurrence_dec EV g d root es) as [Hoccurs|[Hnonroot Havoid]];
    [exact Hoccurs|exfalso].
  assert (Hd : semi_live EV r d) by (eapply lt_ancestor_source_live; [exact Hn|exact (proj1 Hcut)]).
  assert (Hrootlt : Pos.lt (rank root) (rank d)).
  { destruct (semi_ancestor_order EV g r root Hsearch root d
      (semi_search_rooted _ _ _ _ Hsearch d Hd)) as [Heq|Hlt];
      [symmetry in Heq; contradiction|exact Hlt]. }
  destruct (lt_high_suffix root es n (rank d) Hpath lt_root_live
    (lt_ancestor_rank d n (proj1 Hcut))) as [Hall|[u [suffix [Hp [Hu [Hlow [Hin Hall]]]]]]].
  - exact (lt_cut_low_suffix d n root es Hn Hcut Hrootlt lt_root_live Hrootlt Hpath Hall Havoid).
  - apply (lt_cut_low_suffix d n u suffix Hn Hcut Hrootlt Hu Hlow Hp Hall).
    intros e He; apply Havoid; apply Hin; exact He.
Qed.

(** Dominance is exactly the absence of a semidominator shortcut across the tree cut. *)
Lemma lt_cut_exact d n : semi_live EV r n -> (dominates g d n <-> lt_cut d n).
Proof.
  intro Hn; split; [apply lt_dominates_cut|apply lt_cut_dominates]; exact Hn.
Qed.

(** Eval minimizes semidominator ranks on the tree segment below the bucket root. *)
Definition lt_segment_minimum (s v u : V) : Prop :=
  anc u v /\ Pos.lt (rank s) (rank u) /\
  forall w, anc w v -> Pos.lt (rank s) (rank w) ->
    Pos.le (rank (sv u)) (rank (sv w)).

Lemma lt_cut_settled_parent v u : semi_live EV r v -> v <> root ->
  lt_segment_minimum (sv v) v u -> Pos.le (rank (sv v)) (rank (sv u)) ->
  forall d, (lt_cut d v /\ d <> v <-> lt_cut d (sv v)).
Proof.
  intros Hv Hnonroot [Huv [Hsu Hmin]] Hgood d.
  pose proof (lt_semidominator_ancestor v Hv Hnonroot) as Hsv.
  pose proof (semi_semidominator_bound EV g r root Hsearch _ _ Hnonroot
    (Hsemis v Hv Hnonroot)) as Hsvlt.
  split.
  - intros [Hcut Hdistinct]; apply (lt_cut_prefix d (sv v) v Hcut Hsv).
    apply lt_cut_bound; assumption.
  - intros [Hd Hcuts]; split.
    + split; [eapply rt_trans; eauto|]; intros w Hw Hdw.
      destruct (Pos.leb (rank w) (rank (sv v))) eqn:Hcompare.
      * apply Pos.leb_le in Hcompare; apply Hcuts; [|exact Hdw].
        eapply semi_ancestor_cut; eauto.
      * apply Pos.leb_gt in Hcompare.
        eapply Pos.le_trans; [apply lt_ancestor_rank; exact Hd|].
        eapply Pos.le_trans; [exact Hgood|apply Hmin; assumption].
    + intro Heq; subst d; pose proof (lt_ancestor_rank v (sv v) Hd) as Hle.
      apply Pos2Nat.inj_le in Hle; apply Pos2Nat.inj_lt in Hsvlt; lia.
Qed.

Lemma lt_cut_deferred_parent v u : semi_live EV r v -> v <> root ->
  lt_segment_minimum (sv v) v u -> Pos.lt (rank (sv u)) (rank (sv v)) ->
  forall d, (lt_cut d v /\ d <> v <-> lt_cut d u /\ d <> u).
Proof.
  intros Hv Hnonroot [Huv [Hsu Hmin]] Hlow d; split.
  - intros [Hcut Hdistinct].
    pose proof (lt_cut_bound d v Hcut Hdistinct) as Hbound; split.
    + apply (lt_cut_prefix d u v Hcut Huv); eapply Pos.le_trans;
        [exact Hbound|apply Pos.lt_le_incl; exact Hsu].
    + intro Heq; subst d; apply Pos2Nat.inj_le in Hbound; apply Pos2Nat.inj_lt in Hsu; lia.
  - intros [Hcut Hdistinct].
    pose proof (lt_cut_bound d u Hcut Hdistinct) as Hbound.
    assert (Hds : Pos.lt (rank d) (rank (sv v))) by (eapply Pos.le_lt_trans; eauto).
    split.
    + split; [eapply rt_trans; [exact (proj1 Hcut)|exact Huv]|].
      intros w Hw Hdw; destruct (Pos.leb (rank w) (rank (sv v))) eqn:Hcompare.
      * apply Pos.leb_le in Hcompare; apply (proj2 Hcut); [|exact Hdw].
        eapply semi_ancestor_cut; [exact Hsearch|exact Hw|exact Huv|].
        eapply Pos.le_trans; [exact Hcompare|apply Pos.lt_le_incl; exact Hsu].
      * apply Pos.leb_gt in Hcompare; eapply Pos.le_trans; [exact Hbound|].
        apply Hmin; assumption.
    + intro Heq; subst d; pose proof (lt_ancestor_rank u v Huv) as Hle.
      apply Pos2Nat.inj_le in Hle; apply Pos2Nat.inj_lt in Hds, Hsu; lia.
Qed.

(** A provisional parent either is the semidominator or defers to an earlier vertex. *)
Definition lt_parent_choice (v a : V) : Prop :=
  (a = sv v /\ forall d, lt_cut d v /\ d <> v <-> lt_cut d a) \/
  (a <> sv v /\ semi_live EV r a /\ a <> root /\ Pos.lt (rank a) (rank v) /\
    forall d, lt_cut d v /\ d <> v <-> lt_cut d a /\ d <> a).

Lemma lt_minimum_parent_choice s v u : semi_live EV r v -> v <> root -> sv v = s ->
  lt_segment_minimum s v u ->
  lt_parent_choice v (if Pos.ltb (rank (sv u)) (rank s) then u else s).
Proof.
  intros Hv Hnonroot Hsemi Hminimum; subst s.
  destruct (Pos.ltb (rank (sv u)) (rank (sv v))) eqn:Hcompare.
  - apply Pos.ltb_lt in Hcompare.
    destruct Hminimum as [Huv [Hsu Hmin]]; right; split.
    + intro Heq; rewrite Heq in Hsu; exact (Pos.lt_irrefl _ Hsu).
    + split; [eapply lt_ancestor_source_live; eauto|]; split.
      * intro Heq; rewrite Heq in Hsu.
        pose proof (lt_ancestor_rank root (sv v) (semi_search_rooted _ _ _ _ Hsearch _
          (lt_ancestor_source_live (sv v) v Hv (lt_semidominator_ancestor v Hv Hnonroot))))
          as Hle.
        exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hsu Hle)).
      * split.
        -- destruct (semi_ancestor_order EV g r root Hsearch u v Huv) as [Heq|Hlt];
             [rewrite Heq in Hcompare; exact (False_rect _ (Pos.lt_irrefl _ Hcompare))|exact Hlt].
        -- apply lt_cut_deferred_parent; [exact Hv|exact Hnonroot|split; [exact Huv|auto]|
             exact Hcompare].
  - apply Pos.ltb_ge in Hcompare; left; split; [reflexivity|].
    apply lt_cut_settled_parent with (u := u); assumption.
Qed.

Lemma lt_bucket_query s v st : semi_live EV r s -> semi_live EV r v -> v <> root ->
  sv v = s -> semi_links_valid EV (fun x => rank (sv x)) (links st) ->
  semi_cut_forest EV g r (rank s) (links st) ->
  let st' := lt_bucket_member EV r semis s st v in
  SemiLinks.original (links st') = SemiLinks.original (links st) /\
  semi_links_valid EV (fun x => rank (sv x)) (links st') /\
  exists a, parents st' = Map.set EV v a (parents st) /\ lt_parent_choice v a.
Proof.
  intros Hs Hv Hnonroot Hsemi Hvalid Hforest.
  pose proof (semi_eval_minima EV g r root Hsearch (rank s) (fun x => rank (sv x))
    (links st) v Hvalid Hforest
    (lt_ancestor_rank root s (semi_search_rooted _ _ _ _ Hsearch s Hs)) Hv) as Hquery.
  unfold lt_bucket_member; destruct (semi_eval EV rank (fun x => rank (sv x)) (links st) v)
    as [ls u] eqn:Hrun; cbn [links parents] in *.
  destruct Hquery as [Horiginal [Hvalid' [Hposition [Hbound Hminimum]]]].
  split; [exact Horiginal|]; split; [exact Hvalid'|].
  eexists; split; [reflexivity|]; apply lt_minimum_parent_choice; try assumption.
  destruct Hposition as [[Heq Hlow]|[Hhigh [_ Hancestor]]].
  - pose proof (semi_semidominator_bound EV g r root Hsearch _ _ Hnonroot
      (Hsemis v Hv Hnonroot)) as Hlt; rewrite Hsemi in Hlt.
    apply Pos2Nat.inj_le in Hlow; apply Pos2Nat.inj_lt in Hlt; exfalso; lia.
  - split; [exact Hancestor|auto].
Qed.

Lemma lt_bucket_fold_exact s members : forall st,
  semi_live EV r s ->
  (forall v, In v members -> semi_live EV r v /\ v <> root /\ sv v = s) ->
  semi_links_valid EV (fun x => rank (sv x)) (links st) ->
  semi_cut_forest EV g r (rank s) (links st) ->
  let st' := fold_left (lt_bucket_member EV r semis s) members st in
  SemiLinks.original (links st') = SemiLinks.original (links st) /\
  semi_links_valid EV (fun x => rank (sv x)) (links st') /\
  (forall v a, Map.get EV v (parents st') = Some a ->
    Map.get EV v (parents st) = Some a \/ (In v members /\ lt_parent_choice v a)) /\
  (forall v, Map.get EV v (parents st) <> None \/ In v members ->
    Map.get EV v (parents st') <> None).
Proof.
  induction members as [|v members IH]; intros st Hs Hmembers Hvalid Hforest.
  - cbn [fold_left]; split; [reflexivity|]; split; [exact Hvalid|].
    split; [intros x a Hget; left; exact Hget|intros x [Hsome|Hfalse];
      [exact Hsome|contradiction]].
  - destruct (Hmembers v (or_introl eq_refl)) as [Hv [Hnonroot Hsemi]].
    pose proof (lt_bucket_query s v st Hs Hv Hnonroot Hsemi Hvalid Hforest)
      as [Horiginal [Hvalid1 [a [Hparents Hchoice]]]].
    set (st1 := lt_bucket_member EV r semis s st v) in *.
    assert (Hforest1 : semi_cut_forest EV g r (rank s) (links st1)).
    { unfold semi_cut_forest in *; rewrite Horiginal; exact Hforest. }
    destruct (IH st1 Hs ltac:(intros x Hx; apply Hmembers; right; exact Hx)
      Hvalid1 Hforest1) as [Horiginal2 [Hvalid2 [Hsound Htotal]]].
    cbn [fold_left]; split.
    { transitivity (SemiLinks.original (links st1)); assumption. }
    split; [exact Hvalid2|]; split.
    + intros x b Hget; destruct (Hsound x b Hget) as [Hget1|[Hin Hchoice1]].
      * rewrite Hparents in Hget1; destruct (dfs_eq_dec EV x v) as [Heq|Hdistinct].
        -- subst x; rewrite Map.get_set_same in Hget1; injection Hget1 as <-.
           right; split; [left; reflexivity|exact Hchoice].
        -- rewrite Map.get_set_other in Hget1 by exact Hdistinct; left; exact Hget1.
      * right; split; [right; exact Hin|exact Hchoice1].
    + intros x [Hsome|[Heq|Hin]]; apply Htotal.
      * left; rewrite Hparents; destruct (dfs_eq_dec EV x v) as [Heq|Hdistinct].
        -- subst x; rewrite Map.get_set_same; discriminate.
        -- rewrite Map.get_set_other by exact Hdistinct; exact Hsome.
      * left; subst x; rewrite Hparents, Map.get_set_same; discriminate.
      * right; exact Hin.
Qed.

Hypothesis Hdomain : forall v, Map.get EV v semis <> None <-> semi_live EV r v /\ v <> root.

Lemma lt_semi_lookup v : semi_live EV r v -> v <> root -> Map.get EV v semis = Some (sv v).
Proof.
  intros Hv Hnonroot; pose proof (proj2 (Hdomain v) (conj Hv Hnonroot)) as Hsome.
  unfold semi_value; destruct (Map.get EV v semis); [reflexivity|contradiction].
Qed.

Lemma lt_preorder_live v : In v (preorder r) <-> semi_live EV r v.
Proof.
  destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
  rewrite (in_rev (preorder r) v); symmetry.
  apply (dfs_numbering_domain EV _ _ _ Hnumber).
Qed.

Lemma lt_reverse_order u v : before (rev (preorder r)) u v -> Pos.lt (rank v) (rank u).
Proof.
  intro Hbefore; destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
  destruct (dfs_before_indices (rev (preorder r)) u v) as [Hindices _].
  destruct (Hindices Hbefore) as [i [j [_ [Hi Hj]]]].
  assert (Hu : semi_live EV r u).
  { apply lt_preorder_live; apply (proj2 (in_rev (preorder r) u)); eapply nth_error_In; eauto. }
  assert (Hv : semi_live EV r v).
  { apply lt_preorder_live; apply (proj2 (in_rev (preorder r) v)); eapply nth_error_In; eauto. }
  destruct Hu as [a Ha]; destruct Hv as [b Hb].
  rewrite (semi_rank_numbered EV r u a Ha), (semi_rank_numbered EV r v b Hb).
  apply (proj1 (dfs_numbering_order EV _ _ _ Hnumber v u b a Hb Ha)).
  apply (proj1 (dfs_before_reverse (rev (preorder r)) u v)); exact Hbefore.
Qed.

(** Processed buckets account for precisely the provisional bindings, and links are DFS links. *)
Record lt_reverse_valid (done : list V) (st : LtState.t V) : Prop := {
  lt_reverse_links : semi_links_valid EV (fun x => rank (sv x)) (links st);
  lt_reverse_original : forall v a, Map.get EV v (SemiLinks.original (links st)) = Some a <->
    tree_parent EV g r a v /\ In v done;
  lt_reverse_sound : forall v a, Map.get EV v (parents st) = Some a ->
    semi_live EV r v /\ v <> root /\ In (sv v) done /\ lt_parent_choice v a;
  lt_reverse_total : forall v, semi_live EV r v -> v <> root -> In (sv v) done ->
    Map.get EV v (parents st) <> None
}.

Lemma lt_reverse_cut_forest done st s : lt_reverse_valid done st ->
  (forall v, semi_live EV r v -> In v done <-> Pos.lt (rank s) (rank v)) ->
  semi_cut_forest EV g r (rank s) (links st).
Proof.
  intros Hvalid Hcut v a; rewrite (lt_reverse_original _ _ Hvalid); split.
  - intros [Hparent Hin]; split; [exact Hparent|apply Hcut; [|exact Hin]].
    destruct Hparent as [e [He _]]; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
  - intros [Hparent Hhigh]; split; [exact Hparent|apply Hcut; [|exact Hhigh]].
    destruct Hparent as [e [He _]]; apply (semi_parent_numbered _ _ _ _ Hsearch v e He).
Qed.

Lemma lt_bucket_index_member s v :
  In v (lt_bucket EV (lt_bucket_index EV semis (preorder r)) s) ->
  semi_live EV r v /\ v <> root /\ sv v = s.
Proof.
  intro Hin; apply lt_bucket_index_in in Hin; destruct Hin as [_ Hget].
  assert (Hsome : Map.get EV v semis <> None) by (rewrite Hget; discriminate).
  destruct (proj1 (Hdomain v) Hsome) as [Hv Hnonroot].
  split; [exact Hv|]; split; [exact Hnonroot|unfold semi_value; rewrite Hget; reflexivity].
Qed.

(** Linking the current vertex changes only the processed-link domain, not settled parents. *)
Lemma lt_reverse_finish done st s : semi_links_valid EV (fun x => rank (sv x)) (links st) ->
  (forall v a, Map.get EV v (SemiLinks.original (links st)) = Some a <->
    tree_parent EV g r a v /\ In v done) ->
  Map.get EV s (SemiLinks.original (links st)) = None ->
  (forall v a, Map.get EV v (parents st) = Some a ->
    semi_live EV r v /\ v <> root /\ In (sv v) (s :: done) /\ lt_parent_choice v a) ->
  (forall v, semi_live EV r v -> v <> root -> In (sv v) (s :: done) ->
    Map.get EV v (parents st) <> None) ->
  lt_reverse_valid (s :: done)
    (match Map.get EV s (tree_edge r) with
    | None => st
    | Some e => LtState.Make (semi_link EV (links st) s (Graph.source g e)) (parents st)
    end).
Proof.
  intros Hlinks Horiginal Hnone Hsound Htotal.
  destruct (Map.get EV s (tree_edge r)) as [e|] eqn:Htree; constructor;
    cbn [links parents semi_link SemiLinks.original].
  - apply semi_link_valid; assumption.
  - intros v a; destruct (dfs_eq_dec EV v s) as [Heq|Hdistinct].
    + subst v; rewrite Map.get_set_same; split.
      * intro Heq; injection Heq as <-; split; [exists e; auto|left; reflexivity].
      * intros [[f [Hf Hsource]] _]; rewrite Htree in Hf; injection Hf as <-.
        now rewrite Hsource.
    + rewrite Map.get_set_other by exact Hdistinct; rewrite Horiginal.
      split; intros [Hparent Hin]; split; [exact Hparent|right; exact Hin|exact Hparent|].
      destruct Hin as [Heq|Hin]; [symmetry in Heq; contradiction|exact Hin].
  - exact Hsound.
  - exact Htotal.
  - exact Hlinks.
  - intros v a; rewrite Horiginal; split; intros [Hparent Hin]; split;
      [exact Hparent|right; exact Hin|exact Hparent|].
    destruct Hin as [Heq|Hin]; [subst v|exact Hin].
    destruct Hparent as [e [He _]]; rewrite Htree in He; discriminate.
  - exact Hsound.
  - exact Htotal.
Qed.

Lemma lt_reverse_step_exact done st s : lt_reverse_valid done st -> semi_live EV r s ->
  (forall v, semi_live EV r v -> (In v done <-> Pos.lt (rank s) (rank v))) ->
  lt_reverse_valid (s :: done)
    (lt_reverse_step EV g r semis (lt_bucket_index EV semis (preorder r)) st s).
Proof.
  intros Hvalid Hs Hcut.
  pose proof (lt_reverse_cut_forest done st s Hvalid Hcut) as Hforest.
  set (members := lt_bucket EV (lt_bucket_index EV semis (preorder r)) s).
  pose proof (lt_bucket_fold_exact s members st Hs (lt_bucket_index_member s)
    (lt_reverse_links _ _ Hvalid) Hforest) as Hfold.
  set (st1 := fold_left (lt_bucket_member EV r semis s) members st) in *.
  destruct Hfold as [Horiginal [Hlinks [Hsound Htotal]]].
  assert (Hsound1 : forall v a, Map.get EV v (parents st1) = Some a ->
    semi_live EV r v /\ v <> root /\ In (sv v) (s :: done) /\ lt_parent_choice v a).
  { intros v a Hget; destruct (Hsound v a Hget) as [Hold|[Hin Hchoice]].
    - destruct (lt_reverse_sound _ _ Hvalid v a Hold) as [Hv [Hnonroot [Hin Hchoice]]].
      split; [exact Hv|]; split; [exact Hnonroot|]; split; [right; exact Hin|exact Hchoice].
    - destruct (lt_bucket_index_member s v Hin) as [Hv [Hnonroot Heq]].
      split; [exact Hv|]; split; [exact Hnonroot|]; split; [left; symmetry; exact Heq|
        exact Hchoice]. }
  assert (Htotal1 : forall v, semi_live EV r v -> v <> root -> In (sv v) (s :: done) ->
    Map.get EV v (parents st1) <> None).
  { intros v Hv Hnonroot [Heq|Hin]; apply Htotal.
    - right; apply lt_bucket_index_in; split; [apply lt_preorder_live; exact Hv|].
      rewrite Heq; apply lt_semi_lookup; assumption.
    - left; apply (lt_reverse_total _ _ Hvalid); assumption. }
  assert (Horiginal1 : forall v a, Map.get EV v (SemiLinks.original (links st1)) = Some a <->
    tree_parent EV g r a v /\ In v done).
  { intros v a; rewrite Horiginal; apply (lt_reverse_original _ _ Hvalid). }
  unfold lt_reverse_step; fold members; fold st1.
  apply lt_reverse_finish; try assumption.
  destruct (Map.get EV s (SemiLinks.original (links st1))) as [a|] eqn:Hget;
    [|reflexivity].
  apply Horiginal1 in Hget; destruct Hget as [_ Hin]; apply Hcut in Hin; [|exact Hs].
  exfalso; exact (Pos.lt_irrefl _ Hin).
Qed.

Lemma lt_reverse_empty : lt_reverse_valid [] (LtState.Make semi_links_empty Map.empty).
Proof.
  constructor; cbn [links parents semi_links_empty SemiLinks.original].
  - apply semi_links_empty_valid.
  - intros v a; rewrite Map.get_empty; split; [discriminate|intros [_ Hfalse]; contradiction].
  - intros v a Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v _ _ Hfalse; contradiction.
Qed.

Lemma lt_reverse_fold todo : forall done st,
  lt_reverse_valid done st ->
  (forall v, semi_live EV r v <-> In v done \/ In v todo) ->
  (forall u v, before todo u v -> Pos.lt (rank v) (rank u)) ->
  (forall u v, In u done -> In v todo -> Pos.lt (rank v) (rank u)) ->
  exists final, (forall v, In v final <-> In v done \/ In v todo) /\
    lt_reverse_valid final (fold_left
      (lt_reverse_step EV g r semis (lt_bucket_index EV semis (preorder r))) todo st).
Proof.
  induction todo as [|s todo IH]; intros done st Hvalid Hcover Horder Hgap.
  - exists done; split; [intro v; cbn; tauto|exact Hvalid].
  - assert (Hs : semi_live EV r s) by (apply Hcover; right; left; reflexivity).
    assert (Hhead : forall v, In v todo -> Pos.lt (rank v) (rank s)).
    { intros v Hv; apply Horder; apply (proj2 (dfs_before_cons todo s s v)); left; auto. }
    assert (Hcut : forall v, semi_live EV r v -> In v done <-> Pos.lt (rank s) (rank v)).
    { intros v Hv; split.
      - intro Hin; apply Hgap; [exact Hin|left; reflexivity].
      - intro Hhigh; apply Hcover in Hv; destruct Hv as [Hin|[Heq|Hin]]; [exact Hin| |].
        + subst v; exfalso; exact (Pos.lt_irrefl _ Hhigh).
        + pose proof (Hhead v Hin) as Hlow; apply Pos2Nat.inj_lt in Hlow, Hhigh; lia. }
    destruct (IH (s :: done)
      (lt_reverse_step EV g r semis (lt_bucket_index EV semis (preorder r)) st s)
      (lt_reverse_step_exact done st s Hvalid Hs Hcut)
      ltac:(intro v; rewrite Hcover; cbn; tauto)
      ltac:(intros u v Hb; apply Horder; apply (proj2 (dfs_before_cons todo s u v));
        right; exact Hb)
      ltac:(intros u v [Heq|Hin] Hv; [subst u; apply Hhead; exact Hv|
        apply Hgap; [exact Hin|right; exact Hv]])) as [final [Hfinal Hresult]].
    exists final; split; [intro v; rewrite Hfinal; cbn; tauto|exact Hresult].
Qed.

(** Every reached nonroot vertex receives a provisional parent satisfying the LT correction law. *)
Lemma lt_provisional_exact :
  (forall v a, Map.get EV v (lt_provisional EV g r semis) = Some a ->
    semi_live EV r v /\ v <> root /\ lt_parent_choice v a) /\
  (forall v, semi_live EV r v -> v <> root ->
    Map.get EV v (lt_provisional EV g r semis) <> None).
Proof.
  destruct (lt_reverse_fold (rev (preorder r)) [] (LtState.Make semi_links_empty Map.empty)
    lt_reverse_empty
    ltac:(intro v; cbn; rewrite <- in_rev; rewrite lt_preorder_live; tauto)
    lt_reverse_order ltac:(intros u v Hfalse; contradiction))
    as [final [Hfinal Hresult]].
  change (lt_reverse_valid final
    (fold_left (lt_reverse_step EV g r semis (lt_bucket_index EV semis (preorder r)))
      (rev (preorder r)) (LtState.Make semi_links_empty Map.empty))) in Hresult.
  split.
  - intros v a Hget; destruct (lt_reverse_sound _ _ Hresult v a Hget)
      as [Hv [Hnonroot [_ Hchoice]]]; auto.
  - intros v Hv Hnonroot; apply (lt_reverse_total _ _ Hresult); try assumption.
    apply Hfinal; right; apply (proj1 (in_rev (preorder r) (sv v))).
    apply lt_preorder_live; eapply lt_ancestor_source_live;
      [exact Hv|apply lt_semidominator_ancestor; assumption].
Qed.

(** A corrected parent represents precisely the strict dominators of its child. *)
Definition lt_parent_property (v a : V) : Prop :=
  semi_live EV r a /\ Pos.lt (rank a) (rank v) /\
    forall d, lt_cut d v /\ d <> v <-> lt_cut d a.

Record lt_correct_valid (done : list V) (m : Map.t V V) : Prop := {
  lt_correct_sound : forall v a, Map.get EV v m = Some a ->
    In v done /\ semi_live EV r v /\ v <> root /\ lt_parent_property v a;
  lt_correct_total : forall v, In v done -> semi_live EV r v -> v <> root ->
    Map.get EV v m <> None
}.

Lemma lt_correct_parent done m v a : lt_correct_valid done m ->
  semi_live EV r v -> v <> root ->
  (forall u, semi_live EV r u -> Pos.lt (rank u) (rank v) -> In u done) ->
  Map.get EV v (lt_provisional EV g r semis) = Some a ->
  exists b, lt_correct_step EV semis (lt_provisional EV g r semis) m v = Map.set EV v b m /\
    lt_parent_property v b.
Proof.
  intros Hvalid Hv Hnonroot Hprior Hget.
  destruct (proj1 lt_provisional_exact v a Hget) as [_ [_ Hchoice]].
  unfold lt_correct_step; rewrite Hget.
  destruct Hchoice as [[Heq Hlaw]|[Hdistinct [Ha [Hanonroot [Hrank Hlaw]]]]].
  - subst a; rewrite Pos.eqb_refl; exists (sv v); split; [reflexivity|].
    split.
    + eapply lt_ancestor_source_live; [exact Hv|apply lt_semidominator_ancestor; assumption].
    + split; [|exact Hlaw].
      apply (semi_semidominator_bound EV g r root Hsearch); [exact Hnonroot|apply Hsemis;
        assumption].
  - assert (Hneq : Pos.eqb (encode EV a) (encode EV (sv v)) = false).
    { apply Pos.eqb_neq; intro Heq; apply Hdistinct; apply (encode_injective EV); exact Heq. }
    rewrite Hneq.
    pose proof (lt_correct_total _ _ Hvalid a (Hprior a Ha Hrank) Ha Hanonroot) as Hsome.
    destruct (Map.get EV a m) as [b|] eqn:Hparent; [|contradiction].
    unfold semi_value; rewrite Hparent; exists b; split; [reflexivity|].
    destruct (lt_correct_sound _ _ Hvalid a b Hparent) as [_ [_ [_ [Hb [Hbrank Hblaw]]]]].
    split; [exact Hb|]; split; [eapply Pos.lt_trans; eauto|].
    intro d; rewrite Hlaw, Hblaw; reflexivity.
Qed.

Lemma lt_correct_step_exact done m v : lt_correct_valid done m -> semi_live EV r v ->
  (forall u, semi_live EV r u -> Pos.lt (rank u) (rank v) -> In u done) ->
  lt_correct_valid (v :: done)
    (lt_correct_step EV semis (lt_provisional EV g r semis) m v).
Proof.
  intros Hvalid Hv Hprior.
  destruct (Map.get EV v (lt_provisional EV g r semis)) as [a|] eqn:Hget.
  - destruct (proj1 lt_provisional_exact v a Hget) as [_ [Hnonroot _]].
    destruct (lt_correct_parent done m v a Hvalid Hv Hnonroot Hprior Hget)
      as [b [Hstep Hproperty]]; rewrite Hstep; constructor.
    + intros x c Hlookup; destruct (dfs_eq_dec EV x v) as [Heq|Hdistinct].
      * subst x; rewrite Map.get_set_same in Hlookup; injection Hlookup as <-.
        split; [left; reflexivity|]; split; [exact Hv|auto].
      * rewrite Map.get_set_other in Hlookup by exact Hdistinct.
        destruct (lt_correct_sound _ _ Hvalid x c Hlookup) as [Hin Hsound].
        split; [right; exact Hin|exact Hsound].
    + intros x [Heq|Hin] Hx Hnonrootx.
      * subst x; rewrite Map.get_set_same; discriminate.
      * destruct (dfs_eq_dec EV x v) as [Heq|Hdistinct];
          [subst x; rewrite Map.get_set_same; discriminate|].
        rewrite Map.get_set_other by exact Hdistinct; apply (lt_correct_total _ _ Hvalid);
          assumption.
  - unfold lt_correct_step; rewrite Hget; constructor.
    + intros x a Hlookup; destruct (lt_correct_sound _ _ Hvalid x a Hlookup) as [Hin Hsound].
      split; [right; exact Hin|exact Hsound].
    + intros x [Heq|Hin] Hx Hnonrootx.
      * subst x; pose proof (proj2 lt_provisional_exact v Hv Hnonrootx) as Hsome;
          contradiction.
      * apply (lt_correct_total _ _ Hvalid); assumption.
Qed.

Lemma lt_correct_fold todo : forall done m,
  lt_correct_valid done m ->
  (forall v, semi_live EV r v <-> In v done \/ In v todo) ->
  (forall u v, before todo u v -> Pos.lt (rank u) (rank v)) ->
  (forall u v, In u done -> In v todo -> Pos.lt (rank u) (rank v)) ->
  exists final, (forall v, In v final <-> In v done \/ In v todo) /\
    lt_correct_valid final
      (fold_left (lt_correct_step EV semis (lt_provisional EV g r semis)) todo m).
Proof.
  induction todo as [|v todo IH]; intros done m Hvalid Hcover Horder Hgap.
  - exists done; split; [intro x; cbn; tauto|exact Hvalid].
  - assert (Hv : semi_live EV r v) by (apply Hcover; right; left; reflexivity).
    assert (Hhead : forall x, In x todo -> Pos.lt (rank v) (rank x)).
    { intros x Hx; apply Horder; apply (proj2 (dfs_before_cons todo v v x)); left; auto. }
    assert (Hprior : forall u, semi_live EV r u -> Pos.lt (rank u) (rank v) -> In u done).
    { intros u Hu Hlow; apply Hcover in Hu; destruct Hu as [Hin|[Heq|Hin]]; [exact Hin| |].
      - subst u; exfalso; exact (Pos.lt_irrefl _ Hlow).
      - pose proof (Hhead u Hin) as Hhigh; apply Pos2Nat.inj_lt in Hlow, Hhigh; lia. }
    destruct (IH (v :: done) (lt_correct_step EV semis (lt_provisional EV g r semis) m v)
      (lt_correct_step_exact done m v Hvalid Hv Hprior)
      ltac:(intro x; rewrite Hcover; cbn; tauto)
      ltac:(intros x y Hb; apply Horder; apply (proj2 (dfs_before_cons todo v x y));
        right; exact Hb)
      ltac:(intros x y [Heq|Hin] Hy; [subst x; apply Hhead; exact Hy|
        apply Hgap; [exact Hin|right; exact Hy]])) as [final [Hfinal Hresult]].
    exists final; split; [intro x; rewrite Hfinal; cbn; tauto|exact Hresult].
Qed.

Lemma lt_compute_parents :
  (forall v a, Map.get EV v (lt_compute EV g r semis) = Some a ->
    semi_live EV r v /\ v <> root /\ lt_parent_property v a) /\
  (forall v, semi_live EV r v -> v <> root -> Map.get EV v (lt_compute EV g r semis) <> None).
Proof.
  assert (Hempty : lt_correct_valid [] Map.empty).
  { constructor; [intros v a Hget; rewrite Map.get_empty in Hget; discriminate|
      intros v Hfalse; contradiction]. }
  assert (Horder : forall u v, before (preorder r) u v -> Pos.lt (rank u) (rank v)).
  { intros u v Hb; apply lt_reverse_order.
    apply (proj1 (dfs_before_reverse (preorder r) u v)); exact Hb. }
  destruct (lt_correct_fold (preorder r) [] Map.empty Hempty
    ltac:(intro v; cbn; rewrite lt_preorder_live; tauto) Horder
    ltac:(intros u v Hfalse; contradiction)) as [final [Hfinal Hresult]].
  split.
  - intros v a Hget; destruct (lt_correct_sound _ _ Hresult v a Hget) as [_ Hsound];
      exact Hsound.
  - intros v Hv Hnonroot; apply (lt_correct_total _ _ Hresult); try assumption.
    apply Hfinal; right; apply lt_preorder_live; exact Hv.
Qed.

Lemma lt_compute_root_none : Map.get EV root (lt_compute EV g r semis) = None.
Proof.
  destruct (Map.get EV root (lt_compute EV g r semis)) as [a|] eqn:Hget;
    [|reflexivity].
  destruct (proj1 lt_compute_parents root a Hget) as [_ [Hnonroot _]]; contradiction.
Qed.

Lemma lt_ancestor_root d : anc d root -> d = root.
Proof.
  intro Hancestor; pose proof (clos_rt_rtn1 V (tree_parent EV g r) d root Hancestor) as Hchain.
  inversion Hchain as [|a v [e [He _]] Hprefix]; subst; [reflexivity|].
  rewrite (semi_root_parent_none EV g r root Hsearch) in He; discriminate.
Qed.

Lemma lt_compute_ancestor_sound d n : idom_ancestor EV (lt_compute EV g r semis) d n ->
  dominates g d n.
Proof.
  intro Hancestor; induction Hancestor as [d n Hget|n|d u n Hdu IHdu Hun IHun].
  - destruct (proj1 lt_compute_parents n d Hget) as [Hn [_ [_ [_ Hlaw]]]].
    apply lt_cut_dominates; [exact Hn|].
    apply (proj2 (Hlaw d)); apply lt_cut_refl.
  - apply dominates_refl.
  - eapply dominates_trans; eauto.
Qed.

Lemma lt_compute_cut_complete d n : semi_live EV r n -> lt_cut d n ->
  idom_ancestor EV (lt_compute EV g r semis) d n.
Proof.
  revert n; refine (well_founded_induction
    (well_founded_ltof V (fun n => Pos.to_nat (rank n)))
    (fun n => semi_live EV r n -> lt_cut d n ->
      idom_ancestor EV (lt_compute EV g r semis) d n) _).
  intros n IH Hn Hcut; destruct (dfs_eq_dec EV d n) as [Heq|Hdistinct].
  - subst d; apply rt_refl.
  - assert (Hnonroot : n <> root).
    { intro Heq; subst n; apply Hdistinct; apply lt_ancestor_root; exact (proj1 Hcut). }
    pose proof (proj2 lt_compute_parents n Hn Hnonroot) as Hsome.
    destruct (Map.get EV n (lt_compute EV g r semis)) as [a|] eqn:Hparent;
      [|contradiction].
    destruct (proj1 lt_compute_parents n a Hparent) as [_ [_ [Ha [Hrank Hlaw]]]].
    eapply rt_trans; [apply (IH a)|apply rt_step; exact Hparent].
    + unfold ltof; apply Pos2Nat.inj_lt; exact Hrank.
    + exact Ha.
    + apply (proj1 (Hlaw d)); auto.
Qed.

(** The corrected forest's ancestry is exactly semantic dominance. *)
Lemma lt_compute_exact :
  forest_on EV g (lt_compute EV g r semis) /\
  forall d n, semi_live EV r n ->
    (dominates g d n <-> idom_ancestor EV (lt_compute EV g r semis) d n).
Proof.
  split.
  - split.
    + intros v a Hget; destruct (proj1 lt_compute_parents v a Hget) as [Hv [_ [Ha _]]].
      split; apply (semi_live_exact _ _ _ _ Hsearch); assumption.
    + refine (well_founded_induction (well_founded_ltof V (fun v => Pos.to_nat (rank v)))
        (fun v => Acc (fun a v => Map.get EV v (lt_compute EV g r semis) = Some a) v) _).
      intros v IH; constructor; intros a Hget; apply IH; unfold ltof.
      destruct (proj1 lt_compute_parents v a Hget) as [_ [_ [_ [Hrank _]]]].
      apply Pos2Nat.inj_lt; exact Hrank.
  - intros d n Hn; split.
    + intro Hdom; apply lt_compute_cut_complete; [exact Hn|apply lt_dominates_cut; assumption].
    + apply lt_compute_ancestor_sound.
Qed.

End LtCuts.

(** * Well-formed maps and shared inputs *)

Lemma lt_bucket_fold_wf {V E} (EV : encoding V) (r : dfs_result V E) semis s members :
  forall st, Map.wf EV (parents st) ->
    Map.wf EV (parents (fold_left (lt_bucket_member EV r semis s) members st)).
Proof.
  induction members as [|v members IH]; intros st Hwf; [exact Hwf|].
  cbn [fold_left]; apply IH; unfold lt_bucket_member.
  destruct (semi_eval EV (semi_rank EV r)
    (fun x => semi_rank EV r (semi_value EV semis x)) (links st) v) as [ls u].
  cbn [parents]; apply Map.wf_set; exact Hwf.
Qed.

Lemma lt_reverse_step_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis buckets st s : Map.wf EV (parents st) ->
  Map.wf EV (parents (lt_reverse_step EV g r semis buckets st s)).
Proof.
  intro Hwf; pose proof (lt_bucket_fold_wf EV r semis s (lt_bucket EV buckets s) st Hwf)
    as Hbucket; unfold lt_reverse_step.
  destruct (Map.get EV s (tree_edge r)); exact Hbucket.
Qed.

Lemma lt_provisional_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis : Map.wf EV (lt_provisional EV g r semis).
Proof.
  unfold lt_provisional; generalize (rev (preorder r)) as order.
  intro order; assert (Hfold : forall st, Map.wf EV (parents st) ->
    Map.wf EV (parents (fold_left
      (lt_reverse_step EV g r semis (lt_bucket_index EV semis (preorder r))) order st))).
  { induction order as [|v order IH]; intros st Hwf; [exact Hwf|].
    cbn [fold_left]; apply IH; apply lt_reverse_step_wf; exact Hwf. }
  apply Hfold; apply Map.wf_empty.
Qed.

Lemma lt_compute_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis : Map.wf EV (lt_compute EV g r semis).
Proof.
  unfold lt_compute; generalize (preorder r) as order.
  intro order; assert (Hfold : forall m, Map.wf EV m -> Map.wf EV
    (fold_left (lt_correct_step EV semis (lt_provisional EV g r semis)) order m)).
  { induction order as [|v order IH]; intros m Hwf; [exact Hwf|].
    cbn [fold_left]; apply IH; unfold lt_correct_step.
    destruct (Map.get EV v (lt_provisional EV g r semis)); [apply Map.wf_set|]; exact Hwf. }
  apply Hfold; apply Map.wf_empty.
Qed.

(** The shared reverse traversal supplies every reached nonroot vertex's semidominator. *)
Lemma lt_shared_values {V E} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E)
    root (p : prepared EV g) : ready EV g p -> semi_search_laws EV g r root ->
  let semis := SemiState.result (semi_compute p r) in
  (forall v, Map.get EV v semis <> None <-> semi_live EV r v /\ v <> root) /\
  (forall v, semi_live EV r v -> v <> root ->
    semidominator EV g r (semi_value EV semis v) v).
Proof.
  intros Hready Hsearch.
  assert (Hlisting : forall v, semi_live EV r v <-> In v (rev (preorder r))).
  { intro v; destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
    apply (dfs_numbering_domain EV _ _ _ Hnumber). }
  destruct (semi_reverse_fold EV g r root Hsearch p (rev (preorder r)) []
    (SemiState.Make Map.empty semi_links_empty) Hready
    (semi_settled_empty EV g r root)
    ltac:(intro v; cbn; rewrite Hlisting; tauto)
    (lt_reverse_order EV g r root Hsearch)
    ltac:(intros u v Hfalse; contradiction)) as [final [Hfinal Hsettled]].
  change (semi_settled EV g r root final (semi_compute p r)) in Hsettled.
  assert (Htotal : forall v, semi_live EV r v -> v <> root ->
    Map.get EV v (SemiState.result (semi_compute p r)) <> None).
  { intros v Hv Hnonroot; apply (semi_settled_total _ _ _ _ _ _ Hsettled); [|exact Hnonroot].
    apply Hfinal; right; apply Hlisting; exact Hv. }
  split.
  - intro v; split; [|intros [Hv Hnonroot]; apply Htotal; assumption].
    intro Hsome; destruct (Map.get EV v (SemiState.result (semi_compute p r))) as [u|]
      eqn:Hget; [|contradiction].
    destruct (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget) as [Hin [Hnonroot _]].
    split; [apply Hlisting; apply Hfinal in Hin; cbn in Hin; tauto|exact Hnonroot].
  - intros v Hv Hnonroot; pose proof (Htotal v Hv Hnonroot) as Hsome.
    unfold semi_value; destruct (Map.get EV v (SemiState.result (semi_compute p r))) as [u|]
      eqn:Hget; [|contradiction].
    exact (proj2 (proj2 (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget))).
Qed.

(** * Removing the virtual root *)

Lemma lt_erase_virtual_ancestor {V} (EV : encoding V)
    (m : Map.t (V + unit) (V + unit)) : Map.wf (virtual_encoding EV) m ->
  Map.get (virtual_encoding EV) (inr tt) m = None -> forall d n,
  (idom_ancestor (virtual_encoding EV) m (inl d) (inl n) <->
   idom_ancestor EV (erase_virtual_parents EV m) d n).
Proof.
  intros Hwf Hroot d n; split.
  - assert (Hlower : forall v, idom_ancestor (virtual_encoding EV) m (inl d) v ->
      match v with
      | inl x => idom_ancestor EV (erase_virtual_parents EV m) d x
      | inr _ => False
      end).
    { intros v Hancestor; pose proof (clos_rt_rtn1 (V + unit)
        (fun u v => Map.get (virtual_encoding EV) v m = Some u) (inl d) v Hancestor)
        as Hchain.
      clear Hancestor.
      induction Hchain as [|a v Hget Hprefix IH]; [apply rt_refl|].
      destruct a as [a|[]], v as [v|[]]; cbn in *; try contradiction;
        try (rewrite Hroot in Hget; discriminate).
      eapply rt_trans; [exact IH|apply rt_step].
      apply (proj2 (erase_virtual_parents_get EV m Hwf v a)); exact Hget. }
    apply Hlower.
  - intro Hancestor; induction Hancestor as [d n Hget|n|d u n Hdu IHdu Hun IHun].
    + apply rt_step; apply (proj1 (erase_virtual_parents_get EV m Hwf n d)); exact Hget.
    + apply rt_refl.
    + eapply rt_trans; eauto.
Qed.

Lemma lt_erase_virtual_forest {V E} (EV : encoding V) (g : Graph.t V E)
    (m : Map.t (V + unit) (V + unit)) : Map.wf (virtual_encoding EV) m ->
  forest_on (virtual_encoding EV) (virtual_graph EV g) m ->
  forest_on EV g (erase_virtual_parents EV m).
Proof.
  intros Hwf [Hdomain Hwellfounded]; split.
  - intros v a Hget; apply (erase_virtual_parents_get EV m Hwf v a) in Hget.
    destruct (Hdomain _ _ Hget) as [Hv Ha]; split.
    + apply (proj1 (virtual_reachable_iff EV g v)); exact Hv.
    + apply (proj1 (virtual_reachable_iff EV g a)); exact Ha.
  - assert (Hacc : forall v,
      Acc (fun u v => Map.get (virtual_encoding EV) v m = Some u) v ->
      forall x, v = inl x -> Acc (fun u v =>
        Map.get EV v (erase_virtual_parents EV m) = Some u) x).
    { intros v Hacc; induction Hacc as [v Hparents IH]; intros x Heq; subst v.
      constructor; intros y Hget; apply (IH (inl y)); [|reflexivity].
      apply (proj1 (erase_virtual_parents_get EV m Hwf x y)); exact Hget. }
    intro v; apply (Hacc (inl v) (Hwellfounded (inl v)) v eq_refl).
Qed.

(** Simple LT produces an exact parent forest for semantic dominance on reachable vertices. *)
Theorem simple_lt_idom_exact {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p ->
  Map.wf EV (simple_lt_idom p) /\ forest_on EV g (simple_lt_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (simple_lt_idom p) d n)).
Proof.
  intro Hready; pose proof (virtual_graph_ready EV g p Hready) as Hvirtual.
  pose proof (semi_single_search_laws (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (inr tt) Hvirtual eq_refl) as Hsearch.
  destruct (lt_shared_values (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) (virtual_prepared p) Hvirtual Hsearch) as [Hdomain Hsemis].
  change (forall v, Map.get (virtual_encoding EV) v (semidominators p) <> None <->
    semi_live (virtual_encoding EV) (virtual_dfs p) v /\ v <> inr tt) in Hdomain.
  change (forall v, semi_live (virtual_encoding EV) (virtual_dfs p) v -> v <> inr tt ->
    semidominator (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (semi_value (virtual_encoding EV) (semidominators p) v) v) in Hsemis.
  pose proof (lt_compute_wf (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (semidominators p)) as Hwf.
  destruct (lt_compute_exact (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) Hsearch eq_refl (semidominators p) Hsemis Hdomain) as [Hforest Hexact].
  pose proof (lt_compute_root_none (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) Hsearch (semidominators p) Hsemis Hdomain) as Hroot.
  unfold simple_lt_idom; split; [apply erase_virtual_parents_wf|]; split.
  - apply lt_erase_virtual_forest; assumption.
  - intros d n Hn; rewrite (virtual_dominates_iff EV g p Hready d n).
    rewrite (Hexact (inl d) (inl n)) by
      (apply (semi_live_exact _ _ _ _ Hsearch); apply virtual_reachable_iff; exact Hn).
    apply lt_erase_virtual_ancestor; assumption.
Qed.
