(** * Semi-NCA dominators

    Shared semidominators guide a forward pass that walks already constructed dominator
    parents from each DFS parent to the nearest common ancestor.
    For example, a diamond's join walks past either arm to the branching vertex.
    Builds on: GraphSemiDominators, GraphDominance and Collections maps. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat.
From Stdlib.Relations Require Import Relation_Operators Operators_Properties.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphSemiDominators.
Import List.ListNotations.

(** * Rank-decreasing parent walks *)

(** One walk follows settled parents while its vertex is numbered after the semidominator.
    A failed rank check only protects totality on malformed intermediate maps. *)
Definition nca_walk_body {V} (EV : encoding V) (rank : V -> positive)
    (limit : positive) (m : Map.t V V) (v : V)
    (rec : forall a, Pos.to_nat (rank a) < Pos.to_nat (rank v) -> V) : V :=
  if Pos.leb (rank v) limit then v else
    match Map.get EV v m with
    | None => v
    | Some a =>
      match semi_rank_less (rank a) (rank v) with
      | left Hdecrease => rec a Hdecrease
      | right _ => v
      end
    end.

(** Well-founded recursion counts strict discovery-rank descent rather than unary fuel. *)
Definition nca_walk {V} (EV : encoding V) (rank : V -> positive)
    (limit : positive) (m : Map.t V V) : V -> V :=
  Fix (well_founded_ltof V (fun v => Pos.to_nat (rank v)))
    (fun _ => V) (nca_walk_body EV rank limit m).

Lemma nca_walk_unfold {V} (EV : encoding V) rank limit m v :
  nca_walk EV rank limit m v =
    nca_walk_body EV rank limit m v (fun a _ => nca_walk EV rank limit m a).
Proof.
  unfold nca_walk.
  apply (Fix_eq (well_founded_ltof V (fun x => Pos.to_nat (rank x)))
    (fun _ => V) (nca_walk_body EV rank limit m)).
  intros x f h Hagree; unfold nca_walk_body.
  destruct (Pos.leb (rank x) limit); [reflexivity|].
  destruct (Map.get EV x m) as [a|]; [|reflexivity].
  destruct (semi_rank_less (rank a) (rank x)) as [Hlt|Hnot];
    [apply Hagree|reflexivity].
Qed.

(** A vertex obtains the first settled dominator at or before its semidominator's rank. *)
Definition nca_step {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) (m : Map.t V V) (v : V) : Map.t V V :=
  match Map.get EV v (tree_edge r) with
  | None => m
  | Some e =>
    let rank := semi_rank EV r in
    Map.set EV v (nca_walk EV rank (rank (semi_value EV semis v)) m (Graph.source g e)) m
  end.

(** The forward pass constructs each parent using only the parents of earlier vertices. *)
Definition nca_compute {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (semis : Map.t V V) : Map.t V V :=
  fold_left (nca_step EV g r semis) (preorder r) Map.empty.

(** Beyond shared DFS and semidominators, the pass visits each reached vertex once and
    charges each walked parent separately. Each walk visit uses one threshold comparison,
    at most one parent lookup and rank-decrease comparison, and at most three preorder-rank
    lookups. Each outer step reads one DFS parent and, for a nonroot, one semidominator and
    its rank, then writes one parent. A walk has no repeated vertex; total visits can be
    quadratic in the reached vertices. Trie accesses pay the encoded key length and rank
    operations their binary length; erasure pays trie traversal and emitted key-bit costs.
    These source-level counts are not a proved machine-time complexity bound. *)

(** Semi-NCA uses one fresh-root DFS and the common semidominator phase, then erases that root. *)
Definition semi_nca_idom {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : Map.t V V :=
  let vp := virtual_prepared p in
  let r := dfs vp FinSet.empty [inr tt] in
  let semis := SemiState.result (semi_compute vp r) in
  erase_virtual_parents EV
    (nca_compute (virtual_encoding EV) (virtual_graph EV g) r semis).

(** * The nearest-common-ancestor characterization *)

Section NcaProof.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (r : dfs_result V E) (root : V).
Hypothesis Hsearch : semi_search_laws EV g r root.
Hypothesis Hentries : Graph.entries g = [root].
Variable semis : Map.t V V.
Hypothesis Hsemis : forall v, semi_live EV r v -> v <> root ->
  semidominator EV g r (semi_value EV semis v) v.
Local Abbreviation rank := (semi_rank EV r).
Local Abbreviation sv := (semi_value EV semis).
Local Abbreviation anc := (dfs_ancestor EV g r).

(** A tree cut is closed when no descendant's semidominator jumps across it. *)
Definition nca_cut (d n : V) : Prop :=
  anc d n /\ forall w, anc w n -> Pos.lt (rank d) (rank w) ->
    Pos.le (rank d) (rank (sv w)).
Local Abbreviation cut := nca_cut.

Lemma nca_ancestor_rank u v : anc u v -> Pos.le (rank u) (rank v).
Proof.
  intro Hancestor; destruct (semi_ancestor_order EV g r root Hsearch u v Hancestor)
    as [Heq|Hlt]; [subst v; apply Pos.le_refl|apply Pos.lt_le_incl; exact Hlt].
Qed.

Lemma nca_ancestor_live u v : semi_live EV r v -> anc u v -> semi_live EV r u.
Proof.
  intros Hv Hancestor; induction Hancestor as [u v [e [Hedge Hsource]]|u|
    u w v Huw IHuw Hwv IHwv].
  - subst u; apply (semi_parent_numbered _ _ _ _ Hsearch v e Hedge).
  - exact Hv.
  - apply IHuw; apply IHwv; exact Hv.
Qed.

Lemma nca_root_live : semi_live EV r root.
Proof.
  apply (semi_live_exact _ _ _ _ Hsearch); constructor; rewrite Hentries; left; reflexivity.
Qed.

Lemma nca_root_bound v : semi_live EV r v -> Pos.le (rank root) (rank v).
Proof.
  intro Hv; apply nca_ancestor_rank; apply (semi_search_rooted _ _ _ _ Hsearch v Hv).
Qed.

Lemma nca_semidominator_ancestor v : semi_live EV r v -> v <> root -> anc (sv v) v.
Proof.
  intros Hv Hnonroot.
  pose proof (Hsemis v Hv Hnonroot) as Hsemi.
  pose proof (semi_semidominator_bound EV g r root Hsearch _ _ Hnonroot Hsemi) as Hlt.
  destruct Hsemi as [Hpath _].
  apply (semi_path_characterization EV g r root Hsearch) in Hpath.
  destruct Hpath as [Hs [_ [es [_ [Hpath Habove]]]]].
  apply (semi_path_region EV g r root Hsearch (sv v) (sv v) es v Hs Hpath Hs
    (rt_refl _ _ _)); intros e He.
  apply Pos.lt_le_incl; eapply semi_internal_lower; eauto.
Qed.

Lemma nca_cut_refl v : cut v v.
Proof.
  split; [apply rt_refl|]; intros w Hw Hlt.
  pose proof (nca_ancestor_rank w v Hw) as Hle.
  apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; exfalso; lia.
Qed.

Lemma nca_cut_prefix d u v : cut d v -> anc u v -> Pos.le (rank d) (rank u) -> cut d u.
Proof.
  intros [Hd Hall] Hu Hle; split; [eapply semi_ancestor_cut; eauto|].
  intros w Hw Hlt; apply Hall; [eapply rt_trans; eauto|exact Hlt].
Qed.

Lemma nca_cut_bound d v : cut d v -> d <> v -> Pos.le (rank d) (rank (sv v)).
Proof.
  intros [Hd Hall] Hdistinct; apply Hall; [apply rt_refl|].
  destruct (semi_ancestor_order EV g r root Hsearch d v Hd) as [Heq|Hlt];
    [contradiction|exact Hlt].
Qed.

(** The DFS tree supplies an entry path whose vertices retain both ancestry endpoints. *)
Lemma nca_tree_path u v : anc u v -> exists es, path g u es v /\
  forall e, In e es -> anc u (Graph.target g e) /\ anc (Graph.target g e) v.
Proof.
  intro Hancestor; apply clos_rt_rtn1 in Hancestor.
  induction Hancestor as [|p v [e [Hget Hsource]] Hprefix IH].
  - exists []; split; [constructor|intros e Hfalse; contradiction].
  - destruct IH as [es [Hpath Hvertices]].
    destruct (semi_parent_numbered _ _ _ _ Hsearch v e Hget)
      as [_ [_ [Hedge [Htarget _]]]].
    assert (Hpv : anc p v) by (apply rt_step; exists e; auto).
    assert (Huv : anc u v).
    { eapply rt_trans; [apply clos_rtn1_rt; exact Hprefix|exact Hpv]. }
    exists (es ++ [e]); split.
    + rewrite <- Htarget; eapply path_snoc; [exact Hpath|symmetry; exact Hsource|].
      rewrite <- Hsource; exact Hedge.
    + intros f Hf; apply in_app_or in Hf; destruct Hf as [Hf|[Heq|Hfalse]].
      * destruct (Hvertices f Hf) as [Hfirst Hlast]; split; [exact Hfirst|].
        eapply rt_trans; eauto.
      * subst f; rewrite Htarget; split; [exact Huv|apply rt_refl].
      * contradiction.
Qed.

Lemma nca_dominates_ancestor d v : semi_live EV r v -> dominates g d v -> anc d v.
Proof.
  intros Hv Hdom.
  destruct (nca_tree_path root v (semi_search_rooted _ _ _ _ Hsearch v Hv))
    as [es [Hpath Hvertices]].
  destruct (Hdom root es ltac:(rewrite Hentries; left; reflexivity) Hpath)
    as [Heq|[e [He Htarget]]].
  - subst d; apply (semi_search_rooted _ _ _ _ Hsearch v Hv).
  - rewrite <- Htarget; exact (proj2 (Hvertices e He)).
Qed.

Lemma nca_dominates_prefix d u v : dominates g d v -> anc u v ->
  Pos.lt (rank d) (rank u) -> dominates g d u.
Proof.
  intros Hdom Hu Hlt s es Hentry Hpath.
  destruct (nca_tree_path u v Hu) as [suffix [Hsuffix Hvertices]].
  destruct (Hdom s (es ++ suffix) Hentry
    (semi_path_app g s es u suffix v Hpath Hsuffix)) as [Heq|[e [He Htarget]]].
  - left; exact Heq.
  - apply in_app_or in He; destruct He as [He|He]; [right; eauto|].
    destruct (Hvertices e He) as [Hfirst _]; rewrite Htarget in Hfirst.
    pose proof (nca_ancestor_rank u d Hfirst) as Hle.
    apply Pos2Nat.inj_lt in Hlt; apply Pos2Nat.inj_le in Hle; exfalso; lia.
Qed.

Lemma nca_dominates_semi_bound d v : semi_live EV r v -> v <> root ->
  dominates g d v -> d <> v -> Pos.le (rank d) (rank (sv v)).
Proof.
  intros Hv Hnonroot Hdom Hdistinct.
  pose proof (nca_dominates_ancestor d v Hv Hdom) as Hd.
  destruct (semi_ancestor_order EV g r root Hsearch d v Hd) as [Heq|Hlt];
    [contradiction|].
  destruct (Hsemis v Hv Hnonroot) as [Hsemipath _].
  apply (semi_path_characterization EV g r root Hsearch) in Hsemipath.
  destruct Hsemipath as [Hs [_ [suffix [_ [Hsuffix Habove]]]]].
  destruct (nca_tree_path root (sv v) (semi_search_rooted _ _ _ _ Hsearch _ Hs))
    as [prefix [Hprefix Hvertices]].
  destruct (Hdom root (prefix ++ suffix) ltac:(rewrite Hentries; left; reflexivity)
    (semi_path_app g _ _ _ _ _ Hprefix Hsuffix)) as [Heq|[e [He Htarget]]].
  - subst d; apply nca_root_bound; exact Hs.
  - apply in_app_or in He; destruct He as [He|He].
    + rewrite <- Htarget; apply nca_ancestor_rank; exact (proj2 (Hvertices e He)).
    + pose proof (semi_internal_lower EV g r (rank d) (sv v) suffix v
        Hsuffix Habove Hlt e He) as Hfalse.
      rewrite Htarget in Hfalse; exfalso; exact (Pos.lt_irrefl _ Hfalse).
Qed.

Lemma nca_dominates_cut d v : semi_live EV r v -> dominates g d v -> cut d v.
Proof.
  intros Hv Hdom; pose proof (nca_dominates_ancestor d v Hv Hdom) as Hd.
  split; [exact Hd|]; intros w Hw Hlt.
  assert (Hwlive : semi_live EV r w) by (eapply nca_ancestor_live; eauto).
  assert (Hdroot : Pos.le (rank root) (rank d)).
  { apply nca_root_bound; exact (nca_ancestor_live d v Hv Hd). }
  assert (Hnonroot : w <> root).
  { intro Heq; subst w; apply Pos2Nat.inj_lt in Hlt;
      apply Pos2Nat.inj_le in Hdroot; lia. }
  apply nca_dominates_semi_bound; [exact Hwlive|exact Hnonroot| |].
  - eapply nca_dominates_prefix; eauto.
  - intro Heq; subst w; exact (Pos.lt_irrefl _ Hlt).
Qed.

(** The last vertex below a rank threshold leaves a suffix entirely above that threshold. *)
Lemma nca_high_suffix s es n k : path g s es n -> semi_live EV r s -> Pos.le k (rank n) ->
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
    + right; exists u, suffix; split; [exact Hp|]; split; [exact Hu|]; split; [exact Hlow|].
      split; [intros f Hf; right; apply Hin; exact Hf|exact Hall].
Qed.

Lemma nca_semi_minimum_bound u v : semi_live EV r v -> v <> root ->
  semidom_path EV g r u v -> Pos.le (rank (sv v)) (rank u).
Proof.
  intros Hv Hnonroot Hp; destruct (Hsemis v Hv Hnonroot) as [_ [k [Hk Hminimum]]].
  destruct (Hminimum u Hp) as [j [Hj Hle]].
  rewrite (semi_rank_numbered EV r _ k Hk), (semi_rank_numbered EV r _ j Hj); exact Hle.
Qed.

(** Avoiding a closed cut creates a semidominator path that contradicts its lower bound. *)
Lemma nca_cut_avoiding_suffix d n u es : semi_live EV r n -> cut d n ->
  semi_live EV r u -> Pos.lt (rank u) (rank d) -> path g u es n ->
  (forall e, In e es -> Pos.le (rank d) (rank (Graph.target g e))) ->
  (forall e, In e es -> Graph.target g e <> d) -> False.
Proof.
  intros Hn [Hd Hcuts] Hu Hlow Hpath Habove Havoid.
  assert (Hnonempty : es <> []).
  { intro Heq; subst es; apply dominance_path_nil_inv in Hpath; subst u.
    pose proof (nca_ancestor_rank d n Hd) as Hle.
    apply Pos2Nat.inj_lt in Hlow; apply Pos2Nat.inj_le in Hle; lia. }
  destruct (semi_path_minimum EV g r u es n Hpath Hnonempty)
    as [w [prefix [suffix [Hsplit [Hpre [Hfirst [Hlast [Hinternal Hminimum]]]]]]]].
  destruct (semi_path_last g u prefix w Hfirst Hpre)
    as [pre [e [Hlastedge [_ [_ Htarget]]]]].
  assert (Hmember : In e es).
  { rewrite Hsplit, Hlastedge; apply in_or_app; left; apply in_or_app; right;
      left; reflexivity. }
  assert (Hw : semi_live EV r w).
  { exact (proj1 (semi_path_live EV g r root Hsearch u prefix w Hfirst Hu)). }
  assert (Hhigh : Pos.le (rank d) (rank w)).
  { rewrite <- Htarget; apply Habove; exact Hmember. }
  assert (Hwn : anc w n).
  { eapply semi_path_region; [exact Hsearch|exact Hw|exact Hlast|exact Hw|apply rt_refl|].
    intros f Hf; apply Hminimum; rewrite Hsplit; apply in_or_app; right; exact Hf. }
  assert (Hdw : d <> w) by (intro Heq; subst d; apply (Havoid e Hmember); exact Htarget).
  assert (Hrankne : rank d <> rank w).
  { intro Heq; apply Hdw; eapply semi_number_injective; eauto using nca_ancestor_live. }
  assert (Hstrict : Pos.lt (rank d) (rank w)).
  { apply Pos2Nat.inj_lt; apply Pos2Nat.inj_le in Hhigh.
    assert (Pos.to_nat (rank d) <> Pos.to_nat (rank w)) by
      (intro Heq; apply Hrankne; apply Pos2Nat.inj; exact Heq); lia. }
  assert (Hnonroot : w <> root).
  { intro Heq; rewrite Heq in Hstrict.
    pose proof (nca_root_bound d (nca_ancestor_live d n Hn Hd)) as Hroot.
    exact (Pos.lt_irrefl _ (Pos.le_lt_trans _ _ _ Hroot Hstrict)). }
  assert (Hsemi : semidom_path EV g r u w).
  { apply (semi_path_characterization EV g r root Hsearch); split; [exact Hu|].
    split; [exact Hw|]; exists prefix; auto. }
  pose proof (nca_semi_minimum_bound u w Hw Hnonroot Hsemi) as Hbound.
  pose proof (Hcuts w Hwn Hstrict) as Hcut.
  apply Pos2Nat.inj_le in Hbound, Hcut; apply Pos2Nat.inj_lt in Hlow; lia.
Qed.

Lemma nca_cut_dominates d n : semi_live EV r n -> cut d n -> dominates g d n.
Proof.
  intros Hn Hcut s es Hentry Hpath.
  rewrite Hentries in Hentry; destruct Hentry as [Heq|Hfalse]; [subst s|contradiction].
  destruct (path_occurrence_dec EV g d root es) as [Hoccurs|[Hdistinct Havoid]];
    [exact Hoccurs|exfalso].
  assert (Hd : semi_live EV r d) by (eapply nca_ancestor_live; [exact Hn|exact (proj1 Hcut)]).
  assert (Hrootlt : Pos.lt (rank root) (rank d)).
  { destruct (semi_ancestor_order EV g r root Hsearch root d
      (semi_search_rooted _ _ _ _ Hsearch d Hd)) as [Heq|Hlt];
      [symmetry in Heq; contradiction|exact Hlt]. }
  destruct (nca_high_suffix root es n (rank d) Hpath nca_root_live
    (nca_ancestor_rank d n (proj1 Hcut))) as [Hall|[u [suffix [Hp [Hu [Hlow [Hin Hall]]]]]]].
  - exact (nca_cut_avoiding_suffix d n root es Hn Hcut nca_root_live Hrootlt Hpath Hall Havoid).
  - apply (nca_cut_avoiding_suffix d n u suffix Hn Hcut Hu Hlow Hp Hall).
    intros e He; apply Havoid; apply Hin; exact He.
Qed.

(** Semantic dominance is precisely the semidominator closure of a DFS ancestor cut. *)
Lemma nca_cut_exact d n : semi_live EV r n -> (dominates g d n <-> cut d n).
Proof.
  intro Hn; split; [apply nca_dominates_cut|apply nca_cut_dominates]; exact Hn.
Qed.

Lemma nca_parent_ancestor e v d : Map.get EV v (tree_edge r) = Some e ->
  anc d v -> d <> v -> anc d (Graph.source g e).
Proof.
  intros Hparent Hancestor Hdistinct.
  pose proof (clos_rt_rtn1 V (tree_parent EV g r) d v Hancestor) as Hchain.
  inversion Hchain as [|a x [f [Hget Hsource]] Hprefix]; subst.
  - contradiction.
  - rewrite Hparent in Hget; injection Hget as <-.
    apply (clos_rtn1_rt V (tree_parent EV g r)); exact Hprefix.
Qed.

(** Strict dominators of a vertex are its DFS parent's dominators below the semi-rank bound. *)
Lemma nca_cut_parent v e : semi_live EV r v -> v <> root ->
  Map.get EV v (tree_edge r) = Some e -> forall d,
    (cut d v /\ d <> v <-> cut d (Graph.source g e) /\ Pos.le (rank d) (rank (sv v))).
Proof.
  intros Hv Hnonroot Hparent d.
  destruct (semi_parent_numbered _ _ _ _ Hsearch v e Hparent)
    as [_ [Hp [_ [_ Hrank]]]].
  assert (Hpv : anc (Graph.source g e) v) by (apply rt_step; exists e; auto).
  split.
  - intros [Hcut Hdistinct]; split.
    + apply (nca_cut_prefix d (Graph.source g e) v Hcut Hpv).
      apply nca_ancestor_rank; eapply nca_parent_ancestor; eauto; exact (proj1 Hcut).
    + apply nca_cut_bound; assumption.
  - intros [[Hd Hcuts] Hbound]; split.
    + split; [eapply rt_trans; [exact Hd|exact Hpv]|].
      intros w Hw Hdw; destruct (dfs_eq_dec EV w v) as [Heq|Hdistinct].
      * subst w; exact Hbound.
      * apply Hcuts; [eapply nca_parent_ancestor; eauto|exact Hdw].
    + intro Heq; subst d.
      pose proof (nca_ancestor_rank _ _ Hd) as Hle.
      apply Pos2Nat.inj_le in Hle; apply Pos2Nat.inj_lt in Hrank; lia.
Qed.

(** The strict dominators of a vertex are the common dominators of its two Semi-NCA inputs. *)
Lemma nca_common_cuts v e : semi_live EV r v -> v <> root ->
  Map.get EV v (tree_edge r) = Some e -> forall d,
    (cut d v /\ d <> v <-> cut d (Graph.source g e) /\ cut d (sv v)).
Proof.
  intros Hv Hnonroot Hparent d; rewrite (nca_cut_parent v e Hv Hnonroot Hparent d).
  assert (Hsemi : anc (sv v) (Graph.source g e)).
  { apply (nca_parent_ancestor e v (sv v) Hparent).
    - apply nca_semidominator_ancestor; assumption.
    - intro Heq; pose proof (semi_semidominator_bound EV g r root Hsearch _ _ Hnonroot
        (Hsemis v Hv Hnonroot)) as Hlt; rewrite Heq in Hlt; exact (Pos.lt_irrefl _ Hlt). }
  split.
  - intros [Hp Hbound]; split; [exact Hp|].
    eapply nca_cut_prefix; eauto.
  - intros [Hp Hsemi']; split; [exact Hp|apply nca_ancestor_rank; exact (proj1 Hsemi')].
Qed.

(** A parent's cut law states that its ancestors are exactly the child's strict dominators. *)
Definition nca_parent_property (v a : V) : Prop :=
  semi_live EV r a /\ Pos.lt (rank a) (rank v) /\
    forall d, cut d v /\ d <> v <-> cut d a.

(** The partial map contains exactly processed nonroots, with their exact cut laws. *)
Record nca_valid (done : list V) (m : Map.t V V) : Prop := {
  nca_sound : forall v a, Map.get EV v m = Some a ->
    In v done /\ semi_live EV r v /\ v <> root /\ nca_parent_property v a;
  nca_total : forall v, In v done -> semi_live EV r v -> v <> root ->
    Map.get EV v m <> None
}.

(** An exact parent is the nearest common dominator of the DFS parent and semidominator. *)
Lemma nca_parent_is_nearest v e a : semi_live EV r v -> v <> root ->
  Map.get EV v (tree_edge r) = Some e -> nca_parent_property v a ->
  cut a (Graph.source g e) /\ cut a (sv v) /\
    forall d, cut d (Graph.source g e) -> cut d (sv v) -> cut d a.
Proof.
  intros Hv Hnonroot Hparent [_ [_ Hlaw]].
  pose proof (proj2 (Hlaw a) (nca_cut_refl a)) as Hstrict.
  destruct (proj1 (nca_common_cuts v e Hv Hnonroot Hparent a) Hstrict) as [Hp Hs].
  split; [exact Hp|]; split; [exact Hs|].
  intros d Hdp Hds; apply (proj1 (Hlaw d)).
  apply (proj2 (nca_common_cuts v e Hv Hnonroot Hparent d)); split; assumption.
Qed.

(** Walking removes precisely the dominators numbered above the bound. *)
Lemma nca_walk_correct done m current limit : nca_valid done m ->
  Pos.le (rank root) limit ->
  (forall u, semi_live EV r u -> Pos.lt (rank u) (rank current) -> In u done) ->
  forall v, semi_live EV r v -> Pos.lt (rank v) (rank current) ->
    let a := nca_walk EV rank limit m v in
    semi_live EV r a /\ Pos.le (rank a) (rank v) /\ Pos.le (rank a) limit /\
      forall d, cut d v /\ Pos.le (rank d) limit <-> cut d a.
Proof.
  intros Hvalid Hroot Hprior.
  refine (well_founded_induction (well_founded_ltof V (fun v => Pos.to_nat (rank v)))
    (fun v => semi_live EV r v -> Pos.lt (rank v) (rank current) ->
      let a := nca_walk EV rank limit m v in
      semi_live EV r a /\ Pos.le (rank a) (rank v) /\ Pos.le (rank a) limit /\
        forall d, cut d v /\ Pos.le (rank d) limit <-> cut d a) _).
  intros v IH Hv Hbefore; rewrite nca_walk_unfold; unfold nca_walk_body.
  destruct (Pos.leb (rank v) limit) eqn:Hcompare.
  - apply Pos.leb_le in Hcompare; split; [exact Hv|]; split; [apply Pos.le_refl|].
    split; [exact Hcompare|]; intro d; split; [tauto|].
    intro Hcut; split; [exact Hcut|].
    eapply Pos.le_trans; [apply nca_ancestor_rank; exact (proj1 Hcut)|
      exact Hcompare].
  - apply Pos.leb_gt in Hcompare.
    assert (Hnonroot : v <> root).
    { intro Heq; subst v; apply Pos2Nat.inj_le in Hroot;
        apply Pos2Nat.inj_lt in Hcompare; lia. }
    pose proof (nca_total _ _ Hvalid v (Hprior v Hv Hbefore) Hv Hnonroot) as Hsome.
    destruct (Map.get EV v m) as [b|] eqn:Hparent; [|contradiction].
    destruct (nca_sound _ _ Hvalid v b Hparent) as [_ [_ [_ [Hb [Hrank Hlaw]]]]].
    destruct (semi_rank_less (rank b) (rank v)) as [Hdecrease|Hnot].
    + destruct (IH b Hdecrease Hb (Pos.lt_trans _ _ _ Hrank Hbefore))
        as [Ha [Hav [Halimit Hresult]]].
      split; [exact Ha|]; split; [eapply Pos.le_trans; [exact Hav|apply Pos.lt_le_incl;
        exact Hrank]|]; split; [exact Halimit|].
      intro d; rewrite <- Hresult; split.
      * intros [Hcut Hbound]; split; [apply (proj1 (Hlaw d)); split; [exact Hcut|]|exact Hbound].
        intro Heq; subst d; apply Pos2Nat.inj_le in Hbound;
          apply Pos2Nat.inj_lt in Hcompare; lia.
      * intros [Hcut Hbound]; split; [exact (proj1 (proj2 (Hlaw d) Hcut))|exact Hbound].
    + exfalso; apply Hnot; apply Pos2Nat.inj_lt; exact Hrank.
Qed.

(** A settled walk installs the exact nearest-common-ancestor parent for the next vertex. *)
Lemma nca_step_parent done m v e : nca_valid done m -> semi_live EV r v ->
  Map.get EV v (tree_edge r) = Some e ->
  (forall u, semi_live EV r u -> Pos.lt (rank u) (rank v) -> In u done) ->
  exists a, nca_step EV g r semis m v = Map.set EV v a m /\ nca_parent_property v a.
Proof.
  intros Hvalid Hv Hparent Hprior.
  destruct (semi_parent_numbered _ _ _ _ Hsearch v e Hparent)
    as [_ [Hp [_ [_ Hrank]]]].
  assert (Hnonroot : v <> root).
  { intro Heq; subst v; rewrite (semi_root_parent_none EV g r root Hsearch) in Hparent;
      discriminate. }
  assert (Hs : semi_live EV r (sv v)).
  { apply (nca_ancestor_live (sv v) v Hv); apply nca_semidominator_ancestor; assumption. }
  pose proof (nca_walk_correct done m v (rank (sv v)) Hvalid
    (nca_root_bound (sv v) Hs) Hprior (Graph.source g e) Hp Hrank)
    as [Ha [Hle [Hlimit Hlaw]]].
  exists (nca_walk EV rank (rank (sv v)) m (Graph.source g e)); split.
  - unfold nca_step; rewrite Hparent; reflexivity.
  - split; [exact Ha|]; split; [exact (Pos.le_lt_trans _ _ _ Hle Hrank)|].
    intro d; rewrite (nca_cut_parent v e Hv Hnonroot Hparent d); apply Hlaw.
Qed.

Lemma nca_step_exact done m v : nca_valid done m -> semi_live EV r v ->
  (forall u, semi_live EV r u -> Pos.lt (rank u) (rank v) -> In u done) ->
  nca_valid (v :: done) (nca_step EV g r semis m v).
Proof.
  intros Hvalid Hv Hprior; destruct (Map.get EV v (tree_edge r)) as [e|] eqn:Hparent.
  - destruct (nca_step_parent done m v e Hvalid Hv Hparent Hprior)
      as [a [Hstep Hproperty]]; rewrite Hstep; constructor.
    + intros x b Hget; destruct (dfs_eq_dec EV x v) as [Heq|Hdistinct].
      * subst x; rewrite Map.get_set_same in Hget; injection Hget as <-.
        split; [left; reflexivity|]; split; [exact Hv|]; split; [|exact Hproperty].
        intro Heq; subst v; rewrite (semi_root_parent_none EV g r root Hsearch) in Hparent;
          discriminate.
      * rewrite Map.get_set_other in Hget by exact Hdistinct.
        destruct (nca_sound _ _ Hvalid x b Hget) as [Hin Hsound]; split;
          [right; exact Hin|exact Hsound].
    + intros x [Heq|Hin] Hx Hnonroot; destruct (dfs_eq_dec EV x v) as [Heq'|Hdistinct].
      * subst x; rewrite Map.get_set_same; discriminate.
      * subst x; contradiction.
      * subst x; rewrite Map.get_set_same; discriminate.
      * rewrite Map.get_set_other by exact Hdistinct; apply (nca_total _ _ Hvalid);
          assumption.
  - assert (Heq : v = root) by (apply (semi_unlinked_entry _ _ _ _ Hsearch); assumption).
    unfold nca_step; rewrite Hparent; constructor.
    + intros x a Hget; destruct (nca_sound _ _ Hvalid x a Hget) as [Hin Hsound].
      split; [right; exact Hin|exact Hsound].
    + intros x [Hxv|Hin] Hx Hnonroot; [subst x; contradiction|].
      apply (nca_total _ _ Hvalid); assumption.
Qed.

(** Ordered prefix processing makes every dependency available before it is walked. *)
Lemma nca_forward_fold todo : forall done m,
  nca_valid done m ->
  (forall v, semi_live EV r v <-> In v done \/ In v todo) ->
  (forall u v, before todo u v -> Pos.lt (rank u) (rank v)) ->
  (forall u v, In u done -> In v todo -> Pos.lt (rank u) (rank v)) ->
  exists final, (forall v, In v final <-> In v done \/ In v todo) /\
    nca_valid final (fold_left (nca_step EV g r semis) todo m).
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
    destruct (IH (v :: done) (nca_step EV g r semis m v)
      (nca_step_exact done m v Hvalid Hv Hprior)
      ltac:(intro x; rewrite Hcover; cbn; tauto)
      ltac:(intros x y Hb; apply Horder; apply (proj2 (dfs_before_cons todo v x y));
        right; exact Hb)
      ltac:(intros x y [Heq|Hin] Hy; [subst x; apply Hhead; exact Hy|
        apply Hgap; [exact Hin|right; exact Hy]])) as [final [Hfinal Hresult]].
    exists final; split; [intro x; rewrite Hfinal; cbn; tauto|exact Hresult].
Qed.

Lemma nca_preorder_live v : In v (preorder r) <-> semi_live EV r v.
Proof.
  destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
  rewrite (in_rev (preorder r) v); symmetry; apply (dfs_numbering_domain EV _ _ _ Hnumber).
Qed.

Lemma nca_preorder_rank u v : before (preorder r) u v -> Pos.lt (rank u) (rank v).
Proof.
  intro Hbefore; destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
  destruct (dfs_before_indices (preorder r) u v) as [Hindices _].
  destruct (Hindices Hbefore) as [i [j [_ [Hi Hj]]]].
  assert (Hu : semi_live EV r u) by (apply nca_preorder_live; eapply nth_error_In; eauto).
  assert (Hv : semi_live EV r v) by (apply nca_preorder_live; eapply nth_error_In; eauto).
  destruct Hu as [a Ha]; destruct Hv as [b Hb].
  rewrite (semi_rank_numbered EV r u a Ha), (semi_rank_numbered EV r v b Hb).
  apply (proj1 (dfs_numbering_order EV _ _ _ Hnumber u v a b Ha Hb)).
  rewrite rev_involutive; exact Hbefore.
Qed.

(** Every produced binding is exact and every reached nonroot obtains a binding. *)
Lemma nca_compute_parents :
  (forall v a, Map.get EV v (nca_compute EV g r semis) = Some a ->
    semi_live EV r v /\ v <> root /\ nca_parent_property v a) /\
  (forall v, semi_live EV r v -> v <> root -> Map.get EV v (nca_compute EV g r semis) <> None).
Proof.
  assert (Hempty : nca_valid [] Map.empty).
  { constructor; [intros v a Hget; rewrite Map.get_empty in Hget; discriminate|
      intros v Hfalse; contradiction]. }
  destruct (nca_forward_fold (preorder r) [] Map.empty Hempty
    ltac:(intro v; cbn; rewrite nca_preorder_live; tauto) nca_preorder_rank
    ltac:(intros u v Hfalse; contradiction)) as [final [Hfinal Hresult]].
  split.
  - intros v a Hget; exact (proj2 (nca_sound _ _ Hresult v a Hget)).
  - intros v Hv Hnonroot; apply (nca_total _ _ Hresult); try assumption.
    apply Hfinal; right; apply nca_preorder_live; exact Hv.
Qed.

Lemma nca_compute_root_none : Map.get EV root (nca_compute EV g r semis) = None.
Proof.
  destruct (Map.get EV root (nca_compute EV g r semis)) as [a|] eqn:Hget;
    [|reflexivity].
  destruct (proj1 nca_compute_parents root a Hget) as [_ [Hnonroot _]]; contradiction.
Qed.

Lemma nca_ancestor_root d : anc d root -> d = root.
Proof.
  intro Hancestor; apply clos_rt_rtn1 in Hancestor.
  inversion Hancestor as [|a v [e [Hget _]] Hprefix]; subst; [reflexivity|].
  rewrite (semi_root_parent_none EV g r root Hsearch) in Hget; discriminate.
Qed.

Lemma nca_compute_ancestor_sound d n : idom_ancestor EV (nca_compute EV g r semis) d n ->
  dominates g d n.
Proof.
  intro Hancestor; induction Hancestor as [d n Hget|n|d u n Hdu IHdu Hun IHun].
  - destruct (proj1 nca_compute_parents n d Hget) as [Hn [_ [_ [_ Hlaw]]]].
    apply nca_cut_dominates; [exact Hn|].
    exact (proj1 (proj2 (Hlaw d) (nca_cut_refl d))).
  - apply dominates_refl.
  - eapply dominates_trans; eauto.
Qed.

Lemma nca_compute_cut_complete d : forall n, semi_live EV r n -> cut d n ->
  idom_ancestor EV (nca_compute EV g r semis) d n.
Proof.
  refine (well_founded_induction (well_founded_ltof V (fun n => Pos.to_nat (rank n)))
    (fun n => semi_live EV r n -> cut d n ->
      idom_ancestor EV (nca_compute EV g r semis) d n) _).
  intros n IH Hn Hcut; destruct (dfs_eq_dec EV d n) as [Heq|Hdistinct];
    [subst d; apply rt_refl|].
  assert (Hnonroot : n <> root).
  { intro Heq; subst n; apply Hdistinct; apply nca_ancestor_root; exact (proj1 Hcut). }
  pose proof (proj2 nca_compute_parents n Hn Hnonroot) as Hsome.
  destruct (Map.get EV n (nca_compute EV g r semis)) as [a|] eqn:Hget; [|contradiction].
  destruct (proj1 nca_compute_parents n a Hget) as [_ [_ [Ha [Hrank Hlaw]]]].
  eapply rt_trans; [apply (IH a)|apply rt_step; exact Hget].
  - unfold ltof; apply Pos2Nat.inj_lt; exact Hrank.
  - exact Ha.
  - apply (proj1 (Hlaw d)); split; assumption.
Qed.

(** Rank descent makes the parent map a forest, and its paths coincide with dominance. *)
Lemma nca_compute_exact :
  forest_on EV g (nca_compute EV g r semis) /\
  forall d n, semi_live EV r n ->
    (dominates g d n <-> idom_ancestor EV (nca_compute EV g r semis) d n).
Proof.
  split.
  - split.
    + intros v a Hget; destruct (proj1 nca_compute_parents v a Hget) as [Hv [_ [Ha _]]].
      split; apply (semi_live_exact _ _ _ _ Hsearch); assumption.
    + refine (well_founded_induction (well_founded_ltof V (fun v => Pos.to_nat (rank v)))
        (fun v => Acc (fun a v => Map.get EV v (nca_compute EV g r semis) = Some a) v) _).
      intros v IH; constructor; intros a Hget; apply IH; unfold ltof.
      destruct (proj1 nca_compute_parents v a Hget) as [_ [_ [_ [Hrank _]]]].
      apply Pos2Nat.inj_lt; exact Hrank.
  - intros d n Hn; split.
    + intro Hdom; apply nca_compute_cut_complete; [exact Hn|apply nca_dominates_cut; assumption].
    + apply nca_compute_ancestor_sound.
Qed.

(** The two NCA inputs have exactly the produced parent's ancestor set in the final forest. *)
Lemma nca_compute_nearest v e a : Map.get EV v (tree_edge r) = Some e ->
  Map.get EV v (nca_compute EV g r semis) = Some a ->
  idom_ancestor EV (nca_compute EV g r semis) a (Graph.source g e) /\
  idom_ancestor EV (nca_compute EV g r semis) a (sv v) /\
  forall d, idom_ancestor EV (nca_compute EV g r semis) d (Graph.source g e) ->
    idom_ancestor EV (nca_compute EV g r semis) d (sv v) ->
    idom_ancestor EV (nca_compute EV g r semis) d a.
Proof.
  intros Htree Hget.
  destruct (proj1 nca_compute_parents v a Hget) as [Hv [Hnonroot Hproperty]].
  destruct (nca_parent_is_nearest v e a Hv Hnonroot Htree Hproperty) as [Hp [Hs Hnearest]].
  destruct Hproperty as [Ha _].
  pose proof (proj2 (semi_parent_numbered _ _ _ _ Hsearch v e Htree)) as Hparent.
  assert (Hslive : semi_live EV r (sv v)).
  { apply (nca_ancestor_live (sv v) v Hv); apply nca_semidominator_ancestor; assumption. }
  split; [apply nca_compute_cut_complete; [exact (proj1 Hparent)|exact Hp]|].
  split; [apply nca_compute_cut_complete; [exact Hslive|exact Hs]|].
  intros d Hdp Hds; apply nca_compute_cut_complete; [exact Ha|].
  apply Hnearest.
  - apply nca_dominates_cut; [exact (proj1 Hparent)|apply nca_compute_ancestor_sound; exact Hdp].
  - apply nca_dominates_cut; [exact Hslive|apply nca_compute_ancestor_sound; exact Hds].
Qed.

End NcaProof.

(** * Shared phase and virtual-root projection *)

Lemma nca_compute_wf {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) semis : Map.wf EV (nca_compute EV g r semis).
Proof.
  unfold nca_compute; generalize (preorder r) as order; intro order.
  assert (Hfold : forall m, Map.wf EV m ->
    Map.wf EV (fold_left (nca_step EV g r semis) order m)).
  { induction order as [|v order IH]; intros m Hwf; [exact Hwf|].
    cbn [fold_left]; apply IH; unfold nca_step.
    destruct (Map.get EV v (tree_edge r)); [apply Map.wf_set|]; exact Hwf. }
  apply Hfold; apply Map.wf_empty.
Qed.

(** Settlement supplies a semidominator to every reached vertex except the root. *)
Lemma nca_shared_semidominators {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) root (p : prepared EV g) : ready EV g p ->
  semi_search_laws EV g r root ->
  forall v, semi_live EV r v -> v <> root ->
    semidominator EV g r (semi_value EV (SemiState.result (semi_compute p r)) v) v.
Proof.
  intros Hready Hsearch.
  assert (Hlisting : forall v, semi_live EV r v <-> In v (rev (preorder r))).
  { intro v; destruct (semi_search_numbering _ _ _ _ Hsearch) as [next Hnumber].
    apply (dfs_numbering_domain EV _ _ _ Hnumber). }
  assert (Horder : forall u v, before (rev (preorder r)) u v ->
    Pos.lt (semi_rank EV r v) (semi_rank EV r u)).
  { intros u v Hbefore.
    apply (nca_preorder_rank EV g r root Hsearch v u).
    apply (proj1 (dfs_before_reverse (rev (preorder r)) u v)) in Hbefore.
    rewrite rev_involutive in Hbefore; exact Hbefore. }
  destruct (semi_reverse_fold EV g r root Hsearch p (rev (preorder r)) []
    (SemiState.Make Map.empty semi_links_empty) Hready
    (semi_settled_empty EV g r root)
    ltac:(intro v; cbn; rewrite Hlisting; tauto) Horder
    ltac:(intros u v Hfalse; contradiction)) as [final [Hfinal Hsettled]].
  change (semi_settled EV g r root final (semi_compute p r)) in Hsettled.
  intros v Hv Hnonroot.
  assert (Hin : In v final) by (apply Hfinal; right; apply Hlisting; exact Hv).
  pose proof (semi_settled_total _ _ _ _ _ _ Hsettled v Hin Hnonroot) as Hsome.
  unfold semi_value; destruct (Map.get EV v (SemiState.result (semi_compute p r)))
    as [u|] eqn:Hget; [|contradiction].
  exact (proj2 (proj2 (semi_settled_sound _ _ _ _ _ _ Hsettled v u Hget))).
Qed.

(** Root erasure preserves every ancestor relation between real vertices. *)
Lemma nca_erase_ancestor {V} (EV : encoding V) (m : Map.t (V + unit) (V + unit)) :
  Map.wf (virtual_encoding EV) m -> Map.get (virtual_encoding EV) (inr tt) m = None ->
  forall d n, (idom_ancestor (virtual_encoding EV) m (inl d) (inl n) <->
    idom_ancestor EV (erase_virtual_parents EV m) d n).
Proof.
  intros Hwf Hroot d n; split.
  - assert (Hlower : forall v, idom_ancestor (virtual_encoding EV) m (inl d) v ->
      match v with
      | inl x => idom_ancestor EV (erase_virtual_parents EV m) d x
      | inr _ => False
      end).
    { intros v Hancestor; apply clos_rt_rtn1 in Hancestor.
      induction Hancestor as [|a v Hget Hprefix IH]; [apply rt_refl|].
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

Lemma nca_erase_forest {V E} (EV : encoding V) (g : Graph.t V E)
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

(** Semi-NCA produces an exact forest for semantic dominance on all reachable client vertices. *)
Theorem semi_nca_idom_exact {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p ->
  Map.wf EV (semi_nca_idom p) /\ forest_on EV g (semi_nca_idom p) /\
  (forall d n, reachable g n ->
    (dominates g d n <-> idom_ancestor EV (semi_nca_idom p) d n)).
Proof.
  intro Hready; pose proof (virtual_graph_ready EV g p Hready) as Hvirtual.
  pose proof (semi_single_search_laws (virtual_encoding EV) (virtual_graph EV g)
    (virtual_prepared p) (inr tt) Hvirtual eq_refl) as Hsearch.
  pose proof (nca_shared_semidominators (virtual_encoding EV) (virtual_graph EV g)
    (virtual_dfs p) (inr tt) (virtual_prepared p) Hvirtual Hsearch) as Hsemis.
  change (forall v, semi_live (virtual_encoding EV) (virtual_dfs p) v -> v <> inr tt ->
    semidominator (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
      (semi_value (virtual_encoding EV) (semidominators p) v) v) in Hsemis.
  pose proof (nca_compute_wf (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (semidominators p)) as Hwf.
  destruct (nca_compute_exact (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) Hsearch eq_refl (semidominators p) Hsemis) as [Hforest Hexact].
  pose proof (nca_compute_root_none (virtual_encoding EV) (virtual_graph EV g) (virtual_dfs p)
    (inr tt) Hsearch (semidominators p) Hsemis) as Hroot.
  unfold semi_nca_idom; split; [apply erase_virtual_parents_wf|]; split.
  - apply nca_erase_forest; assumption.
  - intros d n Hn; rewrite (virtual_dominates_iff EV g p Hready d n).
    rewrite (Hexact (inl d) (inl n)) by
      (apply (semi_live_exact _ _ _ _ Hsearch); apply virtual_reachable_iff; exact Hn).
    apply nca_erase_ancestor; assumption.
Qed.
