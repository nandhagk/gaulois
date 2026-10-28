(** * Finite sorted e-graphs

    E-classes are finite indexed grammars whose derivations describe finite terms.
    For example, a variable class can also contain an application referring to itself.
    Builds on: CollectionsEncoding, CollectionsMap and RewriteEquality. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality.
Import List.ListNotations.

(** Class and node identifiers use distinct namespaces of positive keys. *)
Definition rw_id := positive.

(** A node stores a variable or an operator with class-valued children. *)
Inductive rw_node (K Sort V : Type) : Type :=
  | RWNVar (s : Sort) (v : V)
  | RWNApp (s : Sort) (op : K) (children : list rw_id).

Arguments RWNVar {K Sort V}.
Arguments RWNApp {K Sort V}.

(** A node retains its declared result sort. *)
Definition rw_node_sort {K Sort V} (n : rw_node K Sort V) : Sort :=
  match n with
  | RWNVar s _ => s
  | RWNApp s _ _ => s
  end.

(** Class aliases point directly to canonical roots; node owners may remain aliases. *)
Record rw_graph (K Sort V : Type) : Type := RwGraph {
  rw_roots : list rw_id;
  rw_nodes_in : list rw_id;
  rw_class_roots : Map.t rw_id rw_id;
  rw_sorts : Map.t rw_id Sort;
  rw_nodes : Map.t rw_id (rw_id * rw_node K Sort V)
}.

Arguments RwGraph {K Sort V}.
Arguments rw_roots {K Sort V}.
Arguments rw_nodes_in {K Sort V}.
Arguments rw_class_roots {K Sort V}.
Arguments rw_sorts {K Sort V}.
Arguments rw_nodes {K Sort V}.

(** Finding an unallocated class fails. *)
Definition rw_find {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option rw_id :=
  Map.get positive_encoding c (rw_class_roots g).

(** Class sorts remain attached to every allocated alias. *)
Definition rw_class_sort {K Sort V} (g : rw_graph K Sort V) (c : rw_id) : option Sort :=
  Map.get positive_encoding c (rw_sorts g).

(** Node lookup returns the owning class and its production. *)
Definition rw_node_at {K Sort V} (g : rw_graph K Sort V) (n : rw_id) :
    option (rw_id * rw_node K Sort V) := Map.get positive_encoding n (rw_nodes g).

(** Representation unfolds finitely many productions, even when the grammar is cyclic. *)
Inductive rw_represents {K Sort V} (g : rw_graph K Sort V) :
    rw_id -> rw_term K Sort V -> Prop :=
  | rw_repr_var : forall c n owner root s v,
      rw_node_at g n = Some (owner, RWNVar s v) -> rw_find g owner = Some root ->
      rw_find g c = Some root -> rw_represents g c (RWVar s v)
  | rw_repr_app : forall c n owner root s op ids ts,
      rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
      rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
      rw_represents g c (RWApp s op ts).

(** Well-formed graphs enumerate exactly their roots and nodes and respect signature sorts. *)
Definition rw_graph_wf {K Sort V} (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : Prop :=
  NoDup (rw_roots g) /\ NoDup (rw_nodes_in g) /\
  Map.wf positive_encoding (rw_class_roots g) /\ Map.wf positive_encoding (rw_sorts g) /\
  Map.wf positive_encoding (rw_nodes g) /\
  (forall c root, rw_find g c = Some root ->
    In root (rw_roots g) /\ rw_find g root = Some root /\
    exists s, rw_class_sort g c = Some s /\ rw_class_sort g root = Some s) /\
  (forall root, In root (rw_roots g) -> rw_find g root = Some root) /\
  (forall c, (exists s, rw_class_sort g c = Some s) <->
    (exists root, rw_find g c = Some root)) /\
  (forall n, In n (rw_nodes_in g) <-> exists c node, rw_node_at g n = Some (c, node)) /\
  (forall n c node, rw_node_at g n = Some (c, node) ->
    rw_class_sort g c = Some (rw_node_sort node)) /\
  (forall n c s v, rw_node_at g n = Some (c, RWNVar s v) ->
    rw_var_sort sig v = Some s) /\
  (forall n c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) ->
    exists sorts, Forall2 (fun id ty => rw_class_sort g id = Some ty) ids sorts /\
      rw_operator_shape sig op sorts s = true) /\
  (forall c t, rw_represents g c t -> rw_typed sig t).

(** Every pair of finite terms in a class is equal in the client's generated theory. *)
Definition rw_graph_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) : Prop :=
  forall c t u, rw_represents g c t -> rw_represents g c u ->
    rw_equal sig admissible rules t u.

(** Extensions retain every represented finite term at its existing identifier. *)
Definition rw_extends {K Sort V} (g g' : rw_graph K Sort V) : Prop :=
  forall c t, rw_represents g c t -> rw_represents g' c t.

(** A clean graph places any common represented term in one canonical class. *)
Definition rw_clean {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall a b t, rw_represents g a t -> rw_represents g b t -> rw_find g a = rw_find g b.

(** Every allocated class has a finite derivation. *)
Definition rw_productive {K Sort V} (g : rw_graph K Sort V) : Prop :=
  forall c root, rw_find g c = Some root -> exists t, rw_represents g c t.

(** A justified union relates nonempty classes whose finite terms are pairwise equal. *)
Definition rw_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a b : rw_id) : Prop :=
  (exists t, rw_represents g a t) /\ (exists u, rw_represents g b u) /\
  forall t u, rw_represents g a t -> rw_represents g b u ->
    rw_equal sig admissible rules t u.

(** * Structural proof interface *)

(** These local obligations omit the typing consequence derived below by finite induction. *)
Record rw_layout {K Sort V} (sig : rw_signature K Sort V) (g : rw_graph K Sort V) :
    Prop := {
  rw_layout_roots : NoDup (rw_roots g);
  rw_layout_nodes : NoDup (rw_nodes_in g);
  rw_layout_classes : Map.wf positive_encoding (rw_class_roots g);
  rw_layout_sorts : Map.wf positive_encoding (rw_sorts g);
  rw_layout_productions : Map.wf positive_encoding (rw_nodes g);
  rw_layout_find : forall c root, rw_find g c = Some root ->
    In root (rw_roots g) /\ rw_find g root = Some root /\
    exists s, rw_class_sort g c = Some s /\ rw_class_sort g root = Some s;
  rw_layout_root : forall root, In root (rw_roots g) -> rw_find g root = Some root;
  rw_layout_domain : forall c, (exists s, rw_class_sort g c = Some s) <->
    (exists root, rw_find g c = Some root);
  rw_layout_enumerates : forall n, In n (rw_nodes_in g) <->
    exists c node, rw_node_at g n = Some (c, node);
  rw_layout_owner : forall n c node, rw_node_at g n = Some (c, node) ->
    rw_class_sort g c = Some (rw_node_sort node);
  rw_layout_var : forall n c s v, rw_node_at g n = Some (c, RWNVar s v) ->
    rw_var_sort sig v = Some s;
  rw_layout_app : forall n c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) ->
    exists sorts, Forall2 (fun id ty => rw_class_sort g id = Some ty) ids sorts /\
      rw_operator_shape sig op sorts s = true
}.

Lemma rw_wf_layout {K Sort V} (sig : rw_signature K Sort V) g :
  rw_graph_wf sig g -> rw_layout sig g.
Proof.
  intros [Hr [Hn [Hc [Hs [Hp [Hf [Hrt [Hd [He [Ho [Hv [Ha Ht]]]]]]]]]]]].
  constructor; assumption.
Qed.

(** Nested representation induction retains the hypotheses for every represented child. *)
Lemma rw_represents_ind_all {K Sort V} (g : rw_graph K Sort V)
    (P : rw_id -> rw_term K Sort V -> Prop)
    (Hvar : forall c n owner root s v,
      rw_node_at g n = Some (owner, RWNVar s v) -> rw_find g owner = Some root ->
      rw_find g c = Some root -> P c (RWVar s v))
    (Happ : forall c n owner root s op ids ts,
      rw_node_at g n = Some (owner, RWNApp s op ids) -> rw_find g owner = Some root ->
      rw_find g c = Some root -> Forall2 (rw_represents g) ids ts ->
      Forall2 P ids ts -> P c (RWApp s op ts)) :
  forall c t, rw_represents g c t -> P c t.
Proof.
  fix IH 3.
  intros c t Hrepr; destruct Hrepr as [c n owner root s v Hnode Ho Hc|
    c n owner root s op ids ts Hnode Ho Hc Hargs].
  - exact (Hvar c n owner root s v Hnode Ho Hc).
  - apply (Happ c n owner root s op ids ts Hnode Ho Hc Hargs).
    clear Hnode Ho Hc.
    induction Hargs as [|id t ids ts Hrepr Hrest IHrest].
    + constructor.
    + constructor; [exact (IH id t Hrepr)|exact IHrest].
Qed.

Lemma rw_represents_find {K Sort V} (g : rw_graph K Sort V) c t :
  rw_represents g c t -> exists root, rw_find g c = Some root.
Proof.
  intro Hrepr; destruct Hrepr; eauto.
Qed.

Lemma rw_represents_alias {K Sort V} (g : rw_graph K Sort V) c d t :
  rw_find g c = rw_find g d -> rw_represents g c t -> rw_represents g d t.
Proof.
  intros Heq Hrepr; destruct Hrepr as [c n owner root s v Hnode Ho Hc|
    c n owner root s op ids ts Hnode Ho Hc Hargs].
  - exact (rw_repr_var g d n owner root s v Hnode Ho (eq_trans (eq_sym Heq) Hc)).
  - exact (rw_repr_app g d n owner root s op ids ts Hnode Ho
      (eq_trans (eq_sym Heq) Hc) Hargs).
Qed.

Lemma rw_layout_same_sort {K Sort V} (sig : rw_signature K Sort V) g a b root :
  rw_layout sig g -> rw_find g a = Some root -> rw_find g b = Some root ->
  rw_class_sort g a = rw_class_sort g b.
Proof.
  intros Hwf Ha Hb.
  destruct (rw_layout_find sig g Hwf a root Ha) as [_ [_ [sa [Has Hrs]]]].
  destruct (rw_layout_find sig g Hwf b root Hb) as [_ [_ [sb [Hbs Hrt]]]].
  congruence.
Qed.

Lemma rw_layout_represents_sort {K Sort V} (sig : rw_signature K Sort V) g c t :
  rw_layout sig g -> rw_represents g c t -> rw_class_sort g c = Some (rw_sort t).
Proof.
  intros Hwf Hrepr; destruct Hrepr as [c n owner root s v Hnode Ho Hc|
    c n owner root s op ids ts Hnode Ho Hc Hargs]; cbn.
  - rewrite (rw_layout_same_sort sig g c owner root Hwf Hc Ho).
    exact (rw_layout_owner sig g Hwf n owner _ Hnode).
  - rewrite (rw_layout_same_sort sig g c owner root Hwf Hc Ho).
    exact (rw_layout_owner sig g Hwf n owner _ Hnode).
Qed.

Lemma rw_layout_represents_typed {K Sort V} (sig : rw_signature K Sort V) g :
  rw_layout sig g -> forall c t, rw_represents g c t -> rw_typed sig t.
Proof.
  intro Hwf; apply (rw_represents_ind_all g (fun _ t => rw_typed sig t)).
  - intros c n owner root s v Hnode Ho Hc; apply rw_typed_var.
    exact (rw_layout_var sig g Hwf n owner s v Hnode).
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    destruct (rw_layout_app sig g Hwf n owner s op ids Hnode)
      as [sorts [Hsorts Hshape]].
    assert (Htypes : Forall (rw_typed sig) ts).
    { clear Hnode Hargs Hsorts Hshape.
      induction IHargs as [|id t ids ts Htyped Hrest IHrest].
      - constructor.
      - constructor; assumption. }
    assert (Heq : sorts = map rw_sort ts).
    { clear Htypes Hshape IHargs Hnode; revert sorts Hsorts.
      induction Hargs as [|id t ids ts Hrepr Hrest IHrest]; intros sorts Hsorts;
        inversion Hsorts as [|id' ty ids' tys Hsort Htail]; subst.
      - reflexivity.
      - cbn; f_equal.
        + pose proof (rw_layout_represents_sort sig g id t Hwf Hrepr); congruence.
        + exact (IHrest _ Htail). }
    apply rw_typed_app; [exact Htypes|now rewrite <- Heq].
Qed.

Lemma rw_layout_wf {K Sort V} (sig : rw_signature K Sort V) g :
  rw_layout sig g -> rw_graph_wf sig g.
Proof.
  intro Hwf; pose proof (rw_layout_represents_typed sig g Hwf) as Htyped.
  destruct Hwf as [Hr Hn Hc Hs Hp Hf Hrt Hd He Ho Hv Ha].
  exact (conj Hr (conj Hn (conj Hc (conj Hs (conj Hp (conj Hf (conj Hrt
    (conj Hd (conj He (conj Ho (conj Hv (conj Ha Htyped)))))))))))).
Qed.

Lemma rw_extends_refl {K Sort V} (g : rw_graph K Sort V) : rw_extends g g.
Proof.
  intros c t Hrepr; exact Hrepr.
Qed.

Lemma rw_extends_trans {K Sort V} (g h j : rw_graph K Sort V) :
  rw_extends g h -> rw_extends h j -> rw_extends g j.
Proof.
  intros Hgh Hhj c t Hrepr; apply Hhj; apply Hgh; exact Hrepr.
Qed.

(** * Empty graph *)

(** The empty graph allocates neither classes nor productions. *)
Definition rw_empty {K Sort V} : rw_graph K Sort V :=
  RwGraph [] [] Map.empty Map.empty Map.empty.

Lemma rw_empty_no_represents {K Sort V} c (t : rw_term K Sort V) :
  ~ rw_represents rw_empty c t.
Proof.
  intro Hrepr; destruct (rw_represents_find rw_empty c t Hrepr) as [root Hfind].
  change (Map.get positive_encoding c Map.empty = Some root) in Hfind.
  rewrite Map.get_empty in Hfind; discriminate.
Qed.

(** Empty graphs satisfy all finite representation and signature invariants. *)
Theorem rw_empty_wf {K Sort V} (sig : rw_signature K Sort V) : rw_graph_wf sig rw_empty.
Proof.
  apply rw_layout_wf; constructor; cbn.
  - constructor.
  - constructor.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - intros c root Hfind; change (Map.get positive_encoding c Map.empty = Some root) in Hfind.
    rewrite Map.get_empty in Hfind; discriminate.
  - intros root Hin; contradiction.
  - intro c; unfold rw_class_sort, rw_find; cbn; rewrite !Map.get_empty.
    split; intros [x Hx]; discriminate.
  - intro n; unfold rw_node_at; cbn; rewrite Map.get_empty.
    split; [contradiction|intros [c [node Hnode]]; discriminate].
  - intros n c node Hnode; change (Map.get positive_encoding n Map.empty = Some (c, node))
      in Hnode; rewrite Map.get_empty in Hnode;
      discriminate.
  - intros n c s v Hnode; change (Map.get positive_encoding n Map.empty =
      Some (c, @RWNVar K Sort V s v)) in Hnode; rewrite Map.get_empty in Hnode;
      discriminate.
  - intros n c s op ids Hnode; change (Map.get positive_encoding n Map.empty =
      Some (c, @RWNApp K Sort V s op ids)) in Hnode; rewrite Map.get_empty in Hnode;
      discriminate.
Qed.

(** The empty graph has no represented terms that could contradict soundness. *)
Theorem rw_empty_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H)) :
  rw_graph_sound sig admissible rules rw_empty.
Proof.
  intros c t u Hrepr; exfalso; exact (rw_empty_no_represents c t Hrepr).
Qed.

(** Productivity of an empty allocation domain is vacuous. *)
Theorem rw_empty_productive {K Sort V} : rw_productive (@rw_empty K Sort V).
Proof.
  intros c root Hfind; change (Map.get positive_encoding c Map.empty = Some root) in Hfind.
  rewrite Map.get_empty in Hfind; discriminate.
Qed.

(** * Exact class merging *)

Definition rw_collapse (from into x : rw_id) : rw_id :=
  if Pos.eq_dec x from then into else x.

Lemma rw_collapse_same from into : rw_collapse from into from = into.
Proof.
  unfold rw_collapse; destruct (Pos.eq_dec from from); congruence.
Qed.

Lemma rw_collapse_other from into x : x <> from -> rw_collapse from into x = x.
Proof.
  intro Hne; unfold rw_collapse; destruct (Pos.eq_dec x from); congruence.
Qed.

Lemma rw_collapse_equal from into x y :
  rw_collapse from into x = rw_collapse from into y <->
    x = y \/ (x = into /\ y = from) \/ (x = from /\ y = into).
Proof.
  unfold rw_collapse; destruct (Pos.eq_dec x from), (Pos.eq_dec y from);
    intuition congruence.
Qed.

(** Merging redirects class aliases and enumerates the surviving root exactly once. *)
Definition rw_merge {K Sort V} (g : rw_graph K Sort V) (ra rb : rw_id) :
    rw_graph K Sort V :=
  RwGraph (ra :: filter (fun r => negb (Pos.eqb r ra || Pos.eqb r rb)) (rw_roots g))
    (rw_nodes_in g) (Map.map (rw_collapse rb ra) (rw_class_roots g))
    (rw_sorts g) (rw_nodes g).

Lemma rw_merge_find {K Sort V} (g : rw_graph K Sort V) ra rb c :
  rw_find (rw_merge g ra rb) c = option_map (rw_collapse rb ra) (rw_find g c).
Proof.
  unfold rw_find; apply Map.get_map.
Qed.

Lemma rw_merge_root_in {K Sort V} (g : rw_graph K Sort V) ra rb r :
  In r (rw_roots (rw_merge g ra rb)) <->
    r = ra \/ (In r (rw_roots g) /\ r <> ra /\ r <> rb).
Proof.
  cbn; rewrite filter_In, Bool.negb_true_iff, Bool.orb_false_iff, !Pos.eqb_neq.
  intuition congruence.
Qed.

Lemma rw_merge_domain {K Sort V} (g : rw_graph K Sort V) ra rb c :
  (exists root, rw_find g c = Some root) <->
    (exists root, rw_find (rw_merge g ra rb) c = Some root).
Proof.
  rewrite rw_merge_find; destruct (rw_find g c) as [root|]; cbn.
  - split; intro H; eauto.
  - split; intros [root Hroot]; discriminate.
Qed.

Lemma rw_merge_extends {K Sort V} (g : rw_graph K Sort V) ra rb :
  rw_extends g (rw_merge g ra rb).
Proof.
  unfold rw_extends.
  apply (rw_represents_ind_all g (rw_represents (rw_merge g ra rb))).
  - intros c n owner root s v Hnode Ho Hc.
    eapply rw_repr_var; [exact Hnode| |]; rewrite rw_merge_find;
      [rewrite Ho|rewrite Hc]; reflexivity.
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    eapply rw_repr_app; [exact Hnode| | |exact IHargs]; rewrite rw_merge_find;
      [rewrite Ho|rewrite Hc]; reflexivity.
Qed.

Lemma rw_merge_layout {K Sort V} (sig : rw_signature K Sort V) g ra rb s :
  rw_layout sig g -> rw_find g ra = Some ra -> rw_find g rb = Some rb ->
  rw_class_sort g ra = Some s -> rw_class_sort g rb = Some s ->
  rw_layout sig (rw_merge g ra rb).
Proof.
  intros Hwf Hra Hrb Hsa Hsb; constructor.
  - cbn; constructor.
    + rewrite filter_In; intros [_ Hkeep]; apply Bool.negb_true_iff in Hkeep.
      rewrite Pos.eqb_refl in Hkeep; discriminate.
    + apply NoDup_filter; exact (rw_layout_roots sig g Hwf).
  - exact (rw_layout_nodes sig g Hwf).
  - apply Map.wf_map; exact (rw_layout_classes sig g Hwf).
  - exact (rw_layout_sorts sig g Hwf).
  - exact (rw_layout_productions sig g Hwf).
  - intros c root Hfind; rewrite rw_merge_find in Hfind.
    destruct (rw_find g c) as [old|] eqn:Hc; cbn in Hfind; try discriminate.
    injection Hfind as Hroot; subst root.
    destruct (rw_layout_find sig g Hwf c old Hc) as [Hin [Hr [ty [Hsc Hsr]]]].
    destruct (Pos.eq_dec old rb) as [Heq|Hne].
    + subst old; rewrite rw_collapse_same; split; [apply rw_merge_root_in; auto|].
      split.
      * rewrite rw_merge_find, Hra; cbn.
        destruct (Pos.eq_dec ra rb) as [->|Hdiff].
        -- rewrite rw_collapse_same; reflexivity.
        -- rewrite rw_collapse_other by exact Hdiff; reflexivity.
      * change (exists ty, rw_class_sort g c = Some ty /\ rw_class_sort g ra = Some ty).
        exists s; split; [congruence|exact Hsa].
    + rewrite rw_collapse_other by exact Hne; split.
      * apply rw_merge_root_in; destruct (Pos.eq_dec old ra); auto.
      * split; [rewrite rw_merge_find, Hr; cbn; now rewrite rw_collapse_other|].
        exists ty; split; assumption.
  - intros root Hin; apply rw_merge_root_in in Hin.
    destruct Hin as [->|[Hin [Hne Hnr]]]; rewrite rw_merge_find.
    + rewrite Hra; cbn; destruct (Pos.eq_dec ra rb) as [->|Hne].
      * rewrite rw_collapse_same; reflexivity.
      * rewrite rw_collapse_other by exact Hne; reflexivity.
    + rewrite (rw_layout_root sig g Hwf root Hin); cbn.
      rewrite rw_collapse_other by exact Hnr; reflexivity.
  - intro c; rewrite <- rw_merge_domain; exact (rw_layout_domain sig g Hwf c).
  - exact (rw_layout_enumerates sig g Hwf).
  - exact (rw_layout_owner sig g Hwf).
  - exact (rw_layout_var sig g Hwf).
  - exact (rw_layout_app sig g Hwf).
Qed.

(** Union rejects missing or differently sorted classes and otherwise merges exactly them. *)
Definition rw_union {K Sort V} (ES : encoding Sort) (g : rw_graph K Sort V)
    (a b : rw_id) : option (rw_graph K Sort V) :=
  match rw_find g a, rw_find g b, rw_class_sort g a, rw_class_sort g b with
  | Some ra, Some rb, Some sa, Some sb =>
    if Pos.eq_dec (encode ES sa) (encode ES sb) then Some (rw_merge g ra rb) else None
  | _, _, _, _ => None
  end.

Lemma rw_union_inv {K Sort V} (ES : encoding Sort) (g g' : rw_graph K Sort V) a b :
  rw_union ES g a b = Some g' -> exists ra rb s,
    rw_find g a = Some ra /\ rw_find g b = Some rb /\
    rw_class_sort g a = Some s /\ rw_class_sort g b = Some s /\ g' = rw_merge g ra rb.
Proof.
  unfold rw_union; destruct (rw_find g a) as [ra|] eqn:Ha; try discriminate.
  destruct (rw_find g b) as [rb|] eqn:Hb; try discriminate.
  destruct (rw_class_sort g a) as [sa|] eqn:Hsa; try discriminate.
  destruct (rw_class_sort g b) as [sb|] eqn:Hsb; try discriminate.
  destruct (Pos.eq_dec (encode ES sa) (encode ES sb)) as [Heq|Hne]; try discriminate.
  apply (encode_injective ES) in Heq; subst sb; intro Hresult; injection Hresult as <-.
  exists ra, rb, sa; repeat split; assumption.
Qed.

(** A union preserves nodes and allocation and identifies precisely its two input classes. *)
Theorem rw_union_structure {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (g g' : rw_graph K Sort V) (a b ra rb : rw_id) :
  rw_graph_wf sig g -> rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_union ES g a b = Some g' ->
  (forall n, rw_node_at g' n = rw_node_at g n) /\
  (forall x, (exists root, rw_find g x = Some root) <->
             (exists root, rw_find g' x = Some root)) /\
  (forall x y rx ry, rw_find g x = Some rx -> rw_find g y = Some ry ->
    (rw_find g' x = rw_find g' y <->
      rx = ry \/ (rx = ra /\ ry = rb) \/ (rx = rb /\ ry = ra))).
Proof.
  intros Hwf Ha Hb Hunion.
  destruct (rw_union_inv ES g g' a b Hunion)
    as [ra' [rb' [s [Ha' [Hb' [Hsa [Hsb ->]]]]]]].
  assert (ra' = ra) by congruence; assert (rb' = rb) by congruence; subst ra' rb'.
  split; [intro n; reflexivity|]; split; [intro x; apply rw_merge_domain|].
  intros x y rx ry Hx Hy; rewrite !rw_merge_find, Hx, Hy; cbn.
  rewrite <- rw_collapse_equal; split; congruence.
Qed.

(** * Soundness of a justified structural merge *)

Lemma rw_merge_related {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    g a b ra rb :
  rw_graph_sound sig admissible rules g -> rw_joinable sig admissible rules g a b ->
  rw_find g a = Some ra -> rw_find g b = Some rb ->
  forall c d t u, rw_represents g c t -> rw_represents g d u ->
    rw_find (rw_merge g ra rb) c = rw_find (rw_merge g ra rb) d ->
    rw_equal sig admissible rules t u.
Proof.
  intros Hsound [_ [_ Hjoin]] Ha Hb c d t u Ht Hu Heq.
  destruct (rw_represents_find g c t Ht) as [rc Hc].
  destruct (rw_represents_find g d u Hu) as [rd Hd].
  rewrite !rw_merge_find, Hc, Hd in Heq; cbn in Heq; injection Heq as Heq.
  apply rw_collapse_equal in Heq; destruct Heq as [Heq|[[-> ->]|[-> ->]]].
  - apply (Hsound c t u Ht); apply (rw_represents_alias g d c u); [congruence|exact Hu].
  - apply Hjoin.
    + apply (rw_represents_alias g c a t); [congruence|exact Ht].
    + apply (rw_represents_alias g d b u); [congruence|exact Hu].
  - apply rw_eq_sym; apply Hjoin.
    + apply (rw_represents_alias g d a u); [congruence|exact Hu].
    + apply (rw_represents_alias g c b t); [congruence|exact Ht].
Qed.

Lemma rw_merge_represents_old {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) a b ra rb :
  rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_joinable sig admissible rules g a b ->
  rw_find g a = Some ra -> rw_find g b = Some rb ->
  forall c t, rw_represents (rw_merge g ra rb) c t ->
    exists u, rw_represents g c u /\ rw_equal sig admissible rules t u.
Proof.
  intros Hsound Hproductive Hjoin Ha Hb.
  apply (rw_represents_ind_all (rw_merge g ra rb)
    (fun c t => exists u, rw_represents g c u /\ rw_equal sig admissible rules t u)).
  - intros c n owner root s v Hnode Ho Hc.
    assert (Hdomain : exists old, rw_find g c = Some old).
    { apply (proj2 (rw_merge_domain g ra rb c)); eauto. }
    destruct Hdomain as [rc Hrc]; destruct (Hproductive c rc Hrc) as [u Hu].
    assert (Howner : exists old, rw_find g owner = Some old).
    { apply (proj2 (rw_merge_domain g ra rb owner)); eauto. }
    destruct Howner as [ro Hro].
    assert (Ht : rw_represents g owner (RWVar s v)).
    { exact (rw_repr_var g owner n owner ro s v Hnode Hro Hro). }
    exists u; split; [exact Hu|].
    apply (rw_merge_related sig admissible rules g a b ra rb Hsound Hjoin Ha Hb
      owner c (RWVar s v) u Ht Hu); congruence.
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    assert (Hchildren : exists us, Forall2 (rw_represents g) ids us /\
        Forall2 (rw_equal sig admissible rules) ts us).
    { clear Hnode Hargs; induction IHargs as [|id t ids ts [u [Hu Heq]] Hrest IHrest].
      - exists []; split; constructor.
      - destruct IHrest as [us [Hus Heqs]]; exists (u :: us); split; constructor; assumption. }
    destruct Hchildren as [us [Hus Heqs]].
    assert (Hdomain : exists old, rw_find g c = Some old).
    { apply (proj2 (rw_merge_domain g ra rb c)); eauto. }
    destruct Hdomain as [rc Hrc]; destruct (Hproductive c rc Hrc) as [u Hu].
    assert (Howner : exists old, rw_find g owner = Some old).
    { apply (proj2 (rw_merge_domain g ra rb owner)); eauto. }
    destruct Howner as [ro Hro].
    assert (Ht : rw_represents g owner (RWApp s op us)).
    { exact (rw_repr_app g owner n owner ro s op ids us Hnode Hro Hro Hus). }
    exists u; split; [exact Hu|].
    apply (rw_eq_trans sig admissible rules _ (RWApp s op us)).
    + apply rw_eq_app; exact Heqs.
    + apply (rw_merge_related sig admissible rules g a b ra rb Hsound Hjoin Ha Hb
        owner c (RWApp s op us) u Ht Hu); congruence.
Qed.

(** Justified unions preserve typing, semantic equality, productivity and every old term. *)
Theorem rw_union_correct {K Sort V H C} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a b : rw_id) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_joinable sig admissible rules g a b -> rw_union ES g a b = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\ rw_find g' a = rw_find g' b.
Proof.
  intros Hwf Hsound Hproductive Hjoin Hunion.
  destruct (rw_union_inv ES g g' a b Hunion)
    as [ra [rb [s [Ha [Hb [Hsa [Hsb ->]]]]]]].
  pose proof (rw_wf_layout sig g Hwf) as Hlayout.
  destruct (rw_layout_find sig g Hlayout a ra Ha) as [_ [Hra [sa [Hsa' Hsra]]]].
  destruct (rw_layout_find sig g Hlayout b rb Hb) as [_ [Hrb [sb [Hsb' Hsrb]]]].
  assert (Hsra' : rw_class_sort g ra = Some s) by congruence.
  assert (Hsrb' : rw_class_sort g rb = Some s) by congruence.
  split.
  - apply rw_layout_wf; exact (rw_merge_layout sig g ra rb s Hlayout Hra Hrb Hsra' Hsrb').
  - split.
    + intros c t u Ht Hu.
      destruct (rw_merge_represents_old sig admissible rules g a b ra rb
        Hsound Hproductive Hjoin Ha Hb c t Ht) as [t' [Ht' Htt']].
      destruct (rw_merge_represents_old sig admissible rules g a b ra rb
        Hsound Hproductive Hjoin Ha Hb c u Hu) as [u' [Hu' Huu']].
      eapply rw_eq_trans; [exact Htt'|].
      eapply rw_eq_trans; [exact (Hsound c t' u' Ht' Hu')|].
      apply rw_eq_sym; exact Huu'.
    + split.
      * intros c root Hfind.
        destruct (proj2 (rw_merge_domain g ra rb c) (ex_intro _ root Hfind)) as [old Hold].
        destruct (Hproductive c old Hold) as [t Ht]; exists t; apply rw_merge_extends; exact Ht.
      * split; [apply rw_merge_extends|].
        rewrite !rw_merge_find, Ha, Hb; cbn; f_equal; apply rw_collapse_equal; auto.
Qed.

(** * Fresh productions *)

(** A local production witness supplies finite terms for all of its children. *)
Inductive rw_node_represents {K Sort V} (g : rw_graph K Sort V) :
    rw_node K Sort V -> rw_term K Sort V -> Prop :=
  | rw_node_repr_var : forall s v, rw_node_represents g (RWNVar s v) (RWVar s v)
  | rw_node_repr_app : forall s op ids ts, Forall2 (rw_represents g) ids ts ->
      rw_node_represents g (RWNApp s op ids) (RWApp s op ts).

(** A locally valid production refers only to allocated classes of the required sorts. *)
Definition rw_node_valid {K Sort V} (sig : rw_signature K Sort V) (g : rw_graph K Sort V)
    (node : rw_node K Sort V) : Prop :=
  match node with
  | RWNVar s v => rw_var_sort sig v = Some s
  | RWNApp s op ids => exists sorts,
    Forall2 (fun id ty => rw_class_sort g id = Some ty) ids sorts /\
      rw_operator_shape sig op sorts s = true
  end.

Definition rw_unused {K Sort V} (g : rw_graph K Sort V) (p : rw_id) : Prop :=
  rw_find g p = None /\ rw_node_at g p = None.

(** Allocation uses one fresh identifier in both independent namespaces. *)
Definition rw_allocate {K Sort V} (g : rw_graph K Sort V) p
    (node : rw_node K Sort V) : rw_graph K Sort V :=
  RwGraph (p :: rw_roots g) (p :: rw_nodes_in g)
    (Map.set positive_encoding p p (rw_class_roots g))
    (Map.set positive_encoding p (rw_node_sort node) (rw_sorts g))
    (Map.set positive_encoding p (p, node) (rw_nodes g)).

Lemma rw_allocate_find {K Sort V} (g : rw_graph K Sort V) p node c :
  rw_find (rw_allocate g p node) c =
    if Pos.eq_dec c p then Some p else rw_find g c.
Proof.
  change (Map.get positive_encoding c (Map.set positive_encoding p p (rw_class_roots g)) =
    if Pos.eq_dec c p then Some p else rw_find g c).
  destruct (Pos.eq_dec c p) as [->|Hne].
  - apply Map.get_set_same.
  - apply Map.get_set_other; exact Hne.
Qed.

Lemma rw_allocate_sort {K Sort V} (g : rw_graph K Sort V) p node c :
  rw_class_sort (rw_allocate g p node) c =
    if Pos.eq_dec c p then Some (rw_node_sort node) else rw_class_sort g c.
Proof.
  change (Map.get positive_encoding c
    (Map.set positive_encoding p (rw_node_sort node) (rw_sorts g)) =
    if Pos.eq_dec c p then Some (rw_node_sort node) else rw_class_sort g c).
  destruct (Pos.eq_dec c p) as [->|Hne].
  - apply Map.get_set_same.
  - apply Map.get_set_other; exact Hne.
Qed.

Lemma rw_allocate_node {K Sort V} (g : rw_graph K Sort V) p node n :
  rw_node_at (rw_allocate g p node) n =
    if Pos.eq_dec n p then Some (p, node) else rw_node_at g n.
Proof.
  change (Map.get positive_encoding n (Map.set positive_encoding p (p, node) (rw_nodes g)) =
    if Pos.eq_dec n p then Some (p, node) else rw_node_at g n).
  destruct (Pos.eq_dec n p) as [->|Hne].
  - apply Map.get_set_same.
  - apply Map.get_set_other; exact Hne.
Qed.

Lemma rw_unused_sort {K Sort V} (sig : rw_signature K Sort V) g p :
  rw_layout sig g -> rw_unused g p -> rw_class_sort g p = None.
Proof.
  intros Hwf [Hfind Hnode]; destruct (rw_class_sort g p) as [s|] eqn:Hs; auto.
  destruct (proj1 (rw_layout_domain sig g Hwf p) (ex_intro _ s Hs)) as [r Hr]; congruence.
Qed.

Lemma rw_allocated_not_fresh {K Sort V} (sig : rw_signature K Sort V) g p c root :
  rw_layout sig g -> rw_unused g p -> rw_find g c = Some root -> c <> p /\ root <> p.
Proof.
  intros Hwf [Hp Hnode] Hc; split; [congruence|].
  destruct (rw_layout_find sig g Hwf c root Hc) as [_ [Hr _]]; congruence.
Qed.

Lemma rw_allocate_find_old {K Sort V} (sig : rw_signature K Sort V) g p node c root :
  rw_layout sig g -> rw_unused g p -> rw_find g c = Some root ->
  rw_find (rw_allocate g p node) c = Some root.
Proof.
  intros Hwf Hfresh Hc; rewrite rw_allocate_find.
  destruct (Pos.eq_dec c p); [subst; destruct Hfresh; congruence|exact Hc].
Qed.

Lemma rw_allocate_extends {K Sort V} (sig : rw_signature K Sort V) g p node :
  rw_layout sig g -> rw_unused g p -> rw_extends g (rw_allocate g p node).
Proof.
  intros Hwf Hfresh; unfold rw_extends.
  apply (rw_represents_ind_all g (rw_represents (rw_allocate g p node))).
  - intros c n owner root s v Hnode Ho Hc.
    apply (rw_repr_var _ c n owner root s v).
    + rewrite rw_allocate_node; destruct (Pos.eq_dec n p); [subst; destruct Hfresh; congruence|].
      exact Hnode.
    + exact (rw_allocate_find_old sig g p node owner root Hwf Hfresh Ho).
    + exact (rw_allocate_find_old sig g p node c root Hwf Hfresh Hc).
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs.
    apply (rw_repr_app _ c n owner root s op ids ts).
    + rewrite rw_allocate_node; destruct (Pos.eq_dec n p); [subst; destruct Hfresh; congruence|].
      exact Hnode.
    + exact (rw_allocate_find_old sig g p node owner root Hwf Hfresh Ho).
    + exact (rw_allocate_find_old sig g p node c root Hwf Hfresh Hc).
    + exact IHargs.
Qed.

Lemma rw_node_valid_children {K Sort V} (sig : rw_signature K Sort V) g s op ids :
  rw_layout sig g -> rw_node_valid sig g (RWNApp s op ids) ->
  Forall (fun id => exists root, rw_find g id = Some root) ids.
Proof.
  intros Hwf [sorts [Hsorts Hshape]]; clear Hshape.
  induction Hsorts as [|id ty ids tys Hsort Hrest IHrest]; constructor; auto.
  apply (proj1 (rw_layout_domain sig g Hwf id)); eauto.
Qed.

Lemma rw_node_valid_allocate {K Sort V} (sig : rw_signature K Sort V) g p node other :
  rw_layout sig g -> rw_unused g p -> rw_node_valid sig g other ->
  rw_node_valid sig (rw_allocate g p node) other.
Proof.
  intros Hwf Hfresh Hvalid; destruct other as [s v|s op ids]; cbn in *; auto.
  destruct Hvalid as [sorts [Hsorts Hshape]]; exists sorts; split; [|exact Hshape].
  clear Hshape; induction Hsorts as [|id ty ids tys Hsort Hrest IHrest]; constructor; auto.
  rewrite rw_allocate_sort; destruct (Pos.eq_dec id p) as [->|Hne]; [|exact Hsort].
  pose proof (rw_unused_sort sig g p Hwf Hfresh); congruence.
Qed.

Lemma rw_allocate_layout {K Sort V} (sig : rw_signature K Sort V) g p node :
  rw_layout sig g -> rw_unused g p -> rw_node_valid sig g node ->
  rw_layout sig (rw_allocate g p node).
Proof.
  intros Hwf Hfresh Hvalid; pose proof Hfresh as [Hp Hnp].
  pose proof (rw_unused_sort sig g p Hwf Hfresh) as Hsp; constructor.
  - cbn; constructor; [intro Hin; pose proof (rw_layout_root sig g Hwf p Hin); congruence|].
    exact (rw_layout_roots sig g Hwf).
  - cbn; constructor.
    + intro Hin; destruct (proj1 (rw_layout_enumerates sig g Hwf p) Hin)
        as [c [other Hnode]]; congruence.
    + exact (rw_layout_nodes sig g Hwf).
  - apply Map.wf_set; exact (rw_layout_classes sig g Hwf).
  - apply Map.wf_set; exact (rw_layout_sorts sig g Hwf).
  - apply Map.wf_set; exact (rw_layout_productions sig g Hwf).
  - intros c root Hfind; rewrite rw_allocate_find in Hfind.
    destruct (Pos.eq_dec c p) as [->|Hne].
    + injection Hfind as <-; split; [cbn; auto|]; split.
      * rewrite rw_allocate_find; destruct (Pos.eq_dec p p); congruence.
      * exists (rw_node_sort node); rewrite rw_allocate_sort;
          destruct (Pos.eq_dec p p); auto; contradiction.
    + destruct (rw_layout_find sig g Hwf c root Hfind) as [Hin [Hr [s [Hsc Hsr]]]].
      destruct (rw_allocated_not_fresh sig g p c root Hwf Hfresh Hfind) as [_ Hrp].
      split; [cbn; auto|]; split.
      * rewrite rw_allocate_find; destruct (Pos.eq_dec root p); congruence.
      * exists s; rewrite !rw_allocate_sort; destruct (Pos.eq_dec c p),
          (Pos.eq_dec root p); intuition congruence.
  - intros root [Heq|Hin].
    + subst root; rewrite rw_allocate_find; destruct (Pos.eq_dec p p); congruence.
    + apply (rw_allocate_find_old sig g p node root root Hwf Hfresh).
      exact (rw_layout_root sig g Hwf root Hin).
  - intro c; rewrite rw_allocate_find, rw_allocate_sort.
    destruct (Pos.eq_dec c p); [split; intro H; eauto|exact (rw_layout_domain sig g Hwf c)].
  - intro n; rewrite rw_allocate_node; cbn.
    destruct (Pos.eq_dec n p) as [->|Hne].
    + split; intro H; eauto.
    + rewrite (rw_layout_enumerates sig g Hwf n); intuition congruence.
  - intros n c other Hnode; rewrite rw_allocate_node in Hnode.
    destruct (Pos.eq_dec n p) as [->|Hne].
    + injection Hnode as <- <-; rewrite rw_allocate_sort;
        destruct (Pos.eq_dec p p); congruence.
    + pose proof (rw_layout_owner sig g Hwf n c other Hnode) as Hsort.
      rewrite rw_allocate_sort; destruct (Pos.eq_dec c p); [subst; congruence|exact Hsort].
  - intros n c s v Hnode; rewrite rw_allocate_node in Hnode.
    destruct (Pos.eq_dec n p) as [->|Hne].
    + injection Hnode as Howner Hother; subst c node; exact Hvalid.
    + exact (rw_layout_var sig g Hwf n c s v Hnode).
  - intros n c s op ids Hnode; rewrite rw_allocate_node in Hnode.
    assert (Hold : rw_node_valid sig g (RWNApp s op ids)).
    { destruct (Pos.eq_dec n p) as [->|Hne].
      - injection Hnode as Howner Hother; subst c node; exact Hvalid.
      - exact (rw_layout_app sig g Hwf n c s op ids Hnode). }
    exact (rw_node_valid_allocate sig g p node (RWNApp s op ids) Hwf Hfresh Hold).
Qed.

Lemma rw_allocate_old_represents {K Sort V} (sig : rw_signature K Sort V) g p node :
  rw_layout sig g -> rw_unused g p -> rw_node_valid sig g node ->
  forall c t, rw_represents (rw_allocate g p node) c t ->
    (exists root, rw_find g c = Some root) -> rw_represents g c t.
Proof.
  intros Hwf Hfresh Hvalid.
  apply (rw_represents_ind_all (rw_allocate g p node)
    (fun c t => (exists root, rw_find g c = Some root) -> rw_represents g c t)).
  - intros c n owner root s v Hnode Ho Hc [rc Hrc].
    rewrite (rw_allocate_find_old sig g p node c rc Hwf Hfresh Hrc) in Hc.
    injection Hc as <-; rewrite rw_allocate_node in Hnode.
    destruct (Pos.eq_dec n p) as [->|Hne].
    + injection Hnode as <- Hnode; rewrite rw_allocate_find in Ho.
      destruct (Pos.eq_dec p p); [|contradiction]; injection Ho as Heq.
      destruct (rw_allocated_not_fresh sig g p c rc Hwf Hfresh Hrc); congruence.
    + pose proof (rw_layout_owner sig g Hwf n owner _ Hnode) as Hsort.
      destruct (proj1 (rw_layout_domain sig g Hwf owner) (ex_intro _ _ Hsort)) as [ro Hro].
      rewrite (rw_allocate_find_old sig g p node owner ro Hwf Hfresh Hro) in Ho.
      injection Ho as <-; exact (rw_repr_var g c n owner ro s v Hnode Hro Hrc).
  - intros c n owner root s op ids ts Hnode Ho Hc Hargs IHargs [rc Hrc].
    rewrite (rw_allocate_find_old sig g p node c rc Hwf Hfresh Hrc) in Hc.
    injection Hc as <-; rewrite rw_allocate_node in Hnode.
    destruct (Pos.eq_dec n p) as [->|Hne].
    + injection Hnode as <- Hnode; rewrite rw_allocate_find in Ho.
      destruct (Pos.eq_dec p p); [|contradiction]; injection Ho as Heq.
      destruct (rw_allocated_not_fresh sig g p c rc Hwf Hfresh Hrc); congruence.
    + pose proof (rw_layout_owner sig g Hwf n owner _ Hnode) as Hsort.
      destruct (proj1 (rw_layout_domain sig g Hwf owner) (ex_intro _ _ Hsort)) as [ro Hro].
      rewrite (rw_allocate_find_old sig g p node owner ro Hwf Hfresh Hro) in Ho.
      injection Ho as <-; eapply rw_repr_app; [exact Hnode|exact Hro|exact Hrc|].
      pose proof (rw_node_valid_children sig g s op ids Hwf
        (rw_layout_app sig g Hwf n owner s op ids Hnode)) as Hdomains.
      clear Hnode Hargs Hsort; revert Hdomains.
      induction IHargs as [|id t ids ts IHt Hrest IHrest]; intro Hdomains.
      * constructor.
      * inversion Hdomains as [|id' ids' Hdomain Htail]; subst.
        constructor; [exact (IHt Hdomain)|exact (IHrest Htail)].
Qed.

Lemma rw_Forall2_guard {A B} (P Q : A -> B -> Prop) (D : A -> Prop) xs ys :
  Forall2 P xs ys -> Forall D xs ->
  (forall x y, D x -> P x y -> Q x y) -> Forall2 Q xs ys.
Proof.
  intro Hrel; induction Hrel as [|x y xs ys Hxy Hrest IHrest]; intros Hd Himpl.
  - constructor.
  - inversion Hd as [|x' xs' Hdx Hds]; subst; constructor.
    + exact (Himpl x y Hdx Hxy).
    + exact (IHrest Hds Himpl).
Qed.

Lemma rw_allocate_new_represents {K Sort V} (sig : rw_signature K Sort V) g p node t :
  rw_layout sig g -> rw_unused g p -> rw_node_valid sig g node ->
  rw_represents (rw_allocate g p node) p t -> rw_node_represents g node t.
Proof.
  intros Hwf Hfresh Hvalid Hrepr; destruct Hfresh as [Hp Hnp].
  inversion Hrepr as [c n owner root s v Hnode Ho Hc|
    c n owner root s op ids ts Hnode Ho Hc Hargs]; subst c;
    rewrite rw_allocate_find in Hc; destruct (Pos.eq_dec p p); try contradiction;
    injection Hc as <-; rewrite rw_allocate_node in Hnode;
    destruct (Pos.eq_dec n p) as [->|Hne].
  - injection Hnode as Howner Hother; subst owner node; constructor.
  - pose proof (rw_layout_owner sig g Hwf n owner _ Hnode) as Hsort.
    destruct (proj1 (rw_layout_domain sig g Hwf owner) (ex_intro _ _ Hsort)) as [ro Hro].
    rewrite (rw_allocate_find_old sig g p node owner ro Hwf (conj Hp Hnp) Hro) in Ho.
    injection Ho as Heq; destruct (rw_allocated_not_fresh sig g p owner ro Hwf
      (conj Hp Hnp) Hro); congruence.
  - injection Hnode as Howner Hother; subst owner node; constructor.
    pose proof (rw_node_valid_children sig g s op ids Hwf Hvalid) as Hdomains.
    apply (rw_Forall2_guard _ _ _ ids ts Hargs Hdomains).
    intros id u Hdomain Hchild.
    exact (rw_allocate_old_represents sig g p (RWNApp s op ids) Hwf
      (conj Hp Hnp) Hvalid id u Hchild Hdomain).
  - pose proof (rw_layout_owner sig g Hwf n owner _ Hnode) as Hsort.
    destruct (proj1 (rw_layout_domain sig g Hwf owner) (ex_intro _ _ Hsort)) as [ro Hro].
    rewrite (rw_allocate_find_old sig g p node owner ro Hwf (conj Hp Hnp) Hro) in Ho.
    injection Ho as Heq; destruct (rw_allocated_not_fresh sig g p owner ro Hwf
      (conj Hp Hnp) Hro); congruence.
Qed.

Lemma rw_node_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    g node t u :
  rw_graph_sound sig admissible rules g -> rw_node_represents g node t ->
  rw_node_represents g node u -> rw_equal sig admissible rules t u.
Proof.
  intros Hsound Ht Hu; destruct Ht as [s v|s op ids ts Hts];
    inversion Hu as [s' v'|s' op' ids' us Hus]; subst.
  - apply rw_eq_refl.
  - apply rw_eq_app; clear Hu; revert us Hus.
    induction Hts as [|id t ids ts Ht Hrest IHrest]; intros us Hus;
      inversion Hus as [|id' u ids' us' Hu Htail]; subst; constructor.
    + exact (Hsound id t u Ht Hu).
    + exact (IHrest _ Htail).
Qed.

Lemma rw_node_represents_extends {K Sort V} (g h : rw_graph K Sort V) node t :
  rw_extends g h -> rw_node_represents g node t -> rw_node_represents h node t.
Proof.
  intros Hext Hrepr; destruct Hrepr as [s v|s op ids ts Hargs]; constructor.
  induction Hargs as [|id t ids ts Ht Hrest IHrest]; constructor; auto.
Qed.

Lemma rw_node_owner_represents {K Sort V} (g : rw_graph K Sort V) n owner root node t :
  rw_node_at g n = Some (owner, node) -> rw_find g owner = Some root ->
  rw_find g root = Some root -> rw_node_represents g node t -> rw_represents g root t.
Proof.
  intros Hnode Ho Hr Hrepr; destruct Hrepr as [s v|s op ids ts Hargs].
  - exact (rw_repr_var g root n owner root s v Hnode Ho Hr).
  - exact (rw_repr_app g root n owner root s op ids ts Hnode Ho Hr Hargs).
Qed.

Lemma rw_allocate_correct {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    g p node t :
  rw_layout sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_unused g p -> rw_node_valid sig g node -> rw_node_represents g node t ->
  rw_layout sig (rw_allocate g p node) /\
  rw_graph_sound sig admissible rules (rw_allocate g p node) /\
  rw_productive (rw_allocate g p node) /\ rw_extends g (rw_allocate g p node) /\
  rw_represents (rw_allocate g p node) p t.
Proof.
  intros Hwf Hsound Hproductive Hfresh Hvalid Ht.
  pose proof (rw_allocate_extends sig g p node Hwf Hfresh) as Hext.
  assert (Hnew : rw_represents (rw_allocate g p node) p t).
  { apply (rw_node_owner_represents _ p p p node t).
    - rewrite rw_allocate_node; destruct (Pos.eq_dec p p); congruence.
    - rewrite rw_allocate_find; destruct (Pos.eq_dec p p); congruence.
    - rewrite rw_allocate_find; destruct (Pos.eq_dec p p); congruence.
    - exact (rw_node_represents_extends g _ node t Hext Ht). }
  split; [exact (rw_allocate_layout sig g p node Hwf Hfresh Hvalid)|]; split.
  - intros c u v Hu Hv; destruct (Pos.eq_dec c p) as [->|Hne].
    + exact (rw_node_sound sig admissible rules g node u v Hsound
        (rw_allocate_new_represents sig g p node u Hwf Hfresh Hvalid Hu)
        (rw_allocate_new_represents sig g p node v Hwf Hfresh Hvalid Hv)).
    + destruct (rw_represents_find _ c u Hu) as [root Hfind].
      rewrite rw_allocate_find in Hfind; destruct (Pos.eq_dec c p); [contradiction|].
      apply (Hsound c u v);
        eapply rw_allocate_old_represents; eauto.
  - split.
    + intros c root Hfind; rewrite rw_allocate_find in Hfind.
      destruct (Pos.eq_dec c p) as [->|Hne]; [eauto|].
      destruct (Hproductive c root Hfind) as [u Hu]; exists u; exact (Hext c u Hu).
    + split; assumption.
Qed.

(** * Canonical node keys and indexed interning *)

Definition rw_node_key {K Sort V} (node : rw_node K Sort V) :
    (Sort * V) + (Sort * (K * list rw_id)) :=
  match node with
  | RWNVar s v => inl (s, v)
  | RWNApp s op ids => inr (s, (op, ids))
  end.

Definition rw_node_encoding {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) : encoding (rw_node K Sort V).
Proof.
  refine (Encoding _ (fun node => encode (sum_encoding (pair_encoding ES EV)
    (pair_encoding ES (pair_encoding EK (list_encoding positive_encoding))))
      (rw_node_key node)) _).
  intros [s v|s op ids] [s' v'|s' op' ids'] Heq;
    apply encode_injective in Heq; cbn in Heq; inversion Heq; reflexivity.
Defined.

Definition rw_canonical_id {K Sort V} (g : rw_graph K Sort V) c : rw_id :=
  match rw_find g c with
  | Some root => root
  | None => c
  end.

Definition rw_canonical_node {K Sort V} (g : rw_graph K Sort V)
    (node : rw_node K Sort V) : rw_node K Sort V :=
  match node with
  | RWNVar s v => RWNVar s v
  | RWNApp s op ids => RWNApp s op (map (rw_canonical_id g) ids)
  end.

Lemma rw_canonical_find {K Sort V} (sig : rw_signature K Sort V) g c :
  rw_layout sig g -> rw_find g (rw_canonical_id g c) = rw_find g c.
Proof.
  intro Hwf; unfold rw_canonical_id; destruct (rw_find g c) as [root|] eqn:Hfind; auto.
  exact (proj1 (proj2 (rw_layout_find sig g Hwf c root Hfind))).
Qed.

Lemma rw_canonical_node_represents {K Sort V} (sig : rw_signature K Sort V) g node t :
  rw_layout sig g ->
  (rw_node_represents g (rw_canonical_node g node) t <-> rw_node_represents g node t).
Proof.
  intro Hwf; destruct node as [s v|s op ids]; cbn; [reflexivity|]; split; intro Hrepr.
  - inversion Hrepr as [|s' op' ids' ts Hargs]; subst; constructor.
    clear Hrepr; revert ts Hargs; induction ids as [|id ids IHids]; intros ts Hargs;
      inversion Hargs as [|id' t ids' ts' Ht Htail]; subst; constructor.
    + apply (rw_represents_alias g (rw_canonical_id g id) id t).
      * exact (rw_canonical_find sig g id Hwf).
      * exact Ht.
    + exact (IHids _ Htail).
  - inversion Hrepr as [|s' op' ids' ts Hargs]; subst; constructor.
    clear Hrepr; induction Hargs as [|id t ids ts Ht Hrest IHrest]; cbn; constructor.
    + apply (rw_represents_alias g id (rw_canonical_id g id) t).
      * symmetry; exact (rw_canonical_find sig g id Hwf).
      * exact Ht.
    + exact IHrest.
Qed.

(** The next identifier bounds all allocated keys in both namespaces. *)
Definition rw_bound {K Sort V} (g : rw_graph K Sort V) p : Prop :=
  (forall c root, rw_find g c = Some root -> (c < p)%positive) /\
  (forall n owner node, rw_node_at g n = Some (owner, node) -> (n < p)%positive).

Definition rw_first_fresh {K Sort V} (g : rw_graph K Sort V) : rw_id :=
  Pos.succ (fold_right Pos.max 1%positive
    (map fst (Map.elements (rw_class_roots g)) ++ map fst (Map.elements (rw_nodes g)))).

Lemma rw_maximum_bound xs x :
  In x xs -> (x <= fold_right Pos.max 1%positive xs)%positive.
Proof.
  induction xs as [|y ys IHys]; cbn; [contradiction|].
  intros [->|Hin]; [apply Pos.le_max_l|].
  eapply Pos.le_trans; [exact (IHys Hin)|apply Pos.le_max_r].
Qed.

Lemma rw_first_fresh_bound {K Sort V} (sig : rw_signature K Sort V) g :
  rw_layout sig g -> rw_bound g (rw_first_fresh g).
Proof.
  intro Hwf; unfold rw_bound, rw_first_fresh; split.
  - intros c root Hfind; apply Pos.le_lt_trans with
      (m := fold_right Pos.max 1%positive
        (map fst (Map.elements (rw_class_roots g)) ++ map fst (Map.elements (rw_nodes g)))).
    + apply rw_maximum_bound; apply in_or_app; left; apply in_map_iff.
      exists (c, root); split; [reflexivity|].
      apply (Map.elements_complete positive_encoding); [exact (rw_layout_classes sig g Hwf)|].
      exact Hfind.
    + apply Pos.lt_succ_diag_r.
  - intros n owner node Hnode; apply Pos.le_lt_trans with
      (m := fold_right Pos.max 1%positive
        (map fst (Map.elements (rw_class_roots g)) ++ map fst (Map.elements (rw_nodes g)))).
    + apply rw_maximum_bound; apply in_or_app; right; apply in_map_iff.
      exists (n, (owner, node)); split; [reflexivity|].
      apply (Map.elements_complete positive_encoding);
        [exact (rw_layout_productions sig g Hwf)|exact Hnode].
    + apply Pos.lt_succ_diag_r.
Qed.

Lemma rw_bound_unused {K Sort V} (g : rw_graph K Sort V) p :
  rw_bound g p -> rw_unused g p.
Proof.
  intros [Hclasses Hnodes]; split.
  - destruct (rw_find g p) as [root|] eqn:Hfind; auto.
    specialize (Hclasses p root Hfind); lia.
  - destruct (rw_node_at g p) as [[owner node]|] eqn:Hnode; auto.
    specialize (Hnodes p owner node Hnode); lia.
Qed.

Lemma rw_allocate_bound {K Sort V} (g : rw_graph K Sort V) p node :
  rw_bound g p -> rw_bound (rw_allocate g p node) (Pos.succ p).
Proof.
  intros [Hclasses Hnodes]; split.
  - intros c root Hfind; rewrite rw_allocate_find in Hfind.
    destruct (Pos.eq_dec c p) as [->|Hne]; [lia|].
    specialize (Hclasses c root Hfind); lia.
  - intros n owner other Hnode; rewrite rw_allocate_node in Hnode.
    destruct (Pos.eq_dec n p) as [->|Hne]; [lia|].
    specialize (Hnodes n owner other Hnode); lia.
Qed.

(** A term phase threads its finite memo table and fresh-key bound through allocations. *)
Record rw_store (K Sort V : Type) : Type := RwStore {
  rw_store_graph : rw_graph K Sort V;
  rw_store_memo : Map.t rw_id rw_id;
  rw_store_next : rw_id
}.

Arguments RwStore {K Sort V}.
Arguments rw_store_graph {K Sort V}.
Arguments rw_store_memo {K Sort V}.
Arguments rw_store_next {K Sort V}.

Definition rw_memo {K Sort V} (EN : encoding (rw_node K Sort V)) (g : rw_graph K Sort V) :
    Map.t rw_id rw_id :=
  Map.fold (fun memo n owned => Map.set positive_encoding
    (encode EN (rw_canonical_node g (snd owned))) n memo) (rw_nodes g) Map.empty.

Definition rw_allocate_store {K Sort V} (EN : encoding (rw_node K Sort V))
    (st : rw_store K Sort V) node : rw_store K Sort V * rw_id :=
  let p := rw_store_next st in
  (RwStore (rw_allocate (rw_store_graph st) p node)
    (Map.set positive_encoding (encode EN node) p (rw_store_memo st)) (Pos.succ p), p).

(** A memo hit is resolved through its stored node, so even malformed input tables are safe. *)
Definition rw_intern {K Sort V} (EN : encoding (rw_node K Sort V))
    (st : rw_store K Sort V) (node : rw_node K Sort V) : rw_store K Sort V * rw_id :=
  match Map.get positive_encoding (encode EN node) (rw_store_memo st) with
  | Some n =>
    match rw_node_at (rw_store_graph st) n with
    | Some (owner, other) =>
      match rw_find (rw_store_graph st) owner with
      | Some root =>
        if Pos.eq_dec (encode EN (rw_canonical_node (rw_store_graph st) other))
          (encode EN node) then (st, root) else rw_allocate_store EN st node
      | None => rw_allocate_store EN st node
      end
    | None => rw_allocate_store EN st node
    end
  | None => rw_allocate_store EN st node
  end.

(** Prepared term phases carry structural, semantic, productivity and freshness invariants. *)
Record rw_store_ok {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (st : rw_store K Sort V) : Prop := {
  rw_store_layout : rw_layout sig (rw_store_graph st);
  rw_store_sound : rw_graph_sound sig admissible rules (rw_store_graph st);
  rw_store_productive : rw_productive (rw_store_graph st);
  rw_store_bound : rw_bound (rw_store_graph st) (rw_store_next st)
}.

(** A successful insertion extends its input and returns a canonical class for the term. *)
Definition rw_added {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (st : rw_store K Sort V) (t : rw_term K Sort V) (result : rw_store K Sort V * rw_id) :
    Prop :=
  let '(st', c) := result in
  rw_store_ok sig admissible rules st' /\ rw_extends (rw_store_graph st) (rw_store_graph st') /\
  rw_represents (rw_store_graph st') c t /\ rw_find (rw_store_graph st') c = Some c.

Lemma rw_allocate_store_correct {K Sort V H C} (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) st node t :
  rw_store_ok sig admissible rules st -> rw_node_valid sig (rw_store_graph st) node ->
  rw_node_represents (rw_store_graph st) node t ->
  rw_added sig admissible rules st t (rw_allocate_store EN st node).
Proof.
  intros Hst Hvalid Ht; destruct Hst as [Hwf Hsound Hproductive Hbound].
  destruct (rw_allocate_correct sig admissible rules _ _ node t Hwf Hsound Hproductive
    (rw_bound_unused _ _ Hbound) Hvalid Ht) as [Hwf' [Hsound' [Hproductive' [Hext Hrepr]]]].
  unfold rw_allocate_store, rw_added; cbn [rw_store_graph rw_store_next].
  split.
  - constructor; try assumption; apply rw_allocate_bound; exact Hbound.
  - split; [exact Hext|]; split; [exact Hrepr|].
    rewrite rw_allocate_find; destruct (Pos.eq_dec (rw_store_next st) (rw_store_next st));
      congruence.
Qed.

Lemma rw_intern_correct {K Sort V H C} (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) st node t :
  rw_store_ok sig admissible rules st -> rw_node_valid sig (rw_store_graph st) node ->
  rw_node_represents (rw_store_graph st) node t ->
  rw_added sig admissible rules st t (rw_intern EN st node).
Proof.
  intros Hst Hvalid Ht.
  pose proof (rw_allocate_store_correct EN sig admissible rules st node t Hst Hvalid Ht)
    as Hallocate; unfold rw_intern.
  destruct (Map.get positive_encoding (encode EN node) (rw_store_memo st)) as [n|];
    [|exact Hallocate].
  destruct (rw_node_at (rw_store_graph st) n) as [[owner other]|] eqn:Hnode;
    [|exact Hallocate].
  destruct (rw_find (rw_store_graph st) owner) as [root|] eqn:Ho; [|exact Hallocate].
  destruct (Pos.eq_dec (encode EN (rw_canonical_node (rw_store_graph st) other))
    (encode EN node)) as [Heq|Hne]; [|exact Hallocate].
  apply (encode_injective EN) in Heq.
  pose proof (rw_store_layout sig admissible rules st Hst) as Hwf.
  pose proof (proj1 (proj2 (rw_layout_find sig _ Hwf owner root Ho))) as Hr.
  split; [exact Hst|]; split; [apply rw_extends_refl|]; split; [|exact Hr].
  apply (rw_node_owner_represents _ n owner root other t Hnode Ho Hr).
  apply (proj1 (rw_canonical_node_represents sig _ other t Hwf)); now rewrite Heq.
Qed.

(** Recursive term insertion threads the memo table without rescanning existing nodes. *)
Fixpoint rw_add_term {K Sort V} (EN : encoding (rw_node K Sort V))
    (t : rw_term K Sort V) (st : rw_store K Sort V) : rw_store K Sort V * rw_id :=
  match t with
  | RWVar s v => rw_intern EN st (RWNVar s v)
  | RWApp s op args =>
    let '(st', ids) := (fix go (ts : list (rw_term K Sort V)) (st : rw_store K Sort V) :=
      match ts with
      | [] => (st, [])
      | t :: ts =>
        let '(st1, id) := rw_add_term EN t st in
        let '(st2, ids) := go ts st1 in
        (st2, id :: ids)
      end) args st in
    rw_intern EN st' (RWNApp s op ids)
  end.

Definition rw_add_terms {K Sort V} (EN : encoding (rw_node K Sort V))
    (ts : list (rw_term K Sort V)) (st : rw_store K Sort V) : rw_store K Sort V * list rw_id :=
  (fix go (ts : list (rw_term K Sort V)) (st : rw_store K Sort V) :=
    match ts with
    | [] => (st, [])
    | t :: ts =>
      let '(st1, id) := rw_add_term EN t st in
      let '(st2, ids) := go ts st1 in
      (st2, id :: ids)
    end) ts st.

Lemma rw_add_terms_cons {K Sort V} (EN : encoding (rw_node K Sort V)) t ts st :
  rw_add_terms EN (t :: ts) st =
    let '(st1, id) := rw_add_term EN t st in
    let '(st2, ids) := rw_add_terms EN ts st1 in (st2, id :: ids).
Proof.
  reflexivity.
Qed.

Lemma rw_add_terms_correct {K Sort V H C} (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) ts :
  Forall (fun t => forall st, rw_store_ok sig admissible rules st ->
    rw_added sig admissible rules st t (rw_add_term EN t st)) ts ->
  forall st, rw_store_ok sig admissible rules st ->
  let '(st', ids) := rw_add_terms EN ts st in
  rw_store_ok sig admissible rules st' /\ rw_extends (rw_store_graph st) (rw_store_graph st') /\
  Forall2 (rw_represents (rw_store_graph st')) ids ts.
Proof.
  intro Hterms; induction Hterms as [|t ts Ht Hrest IHrest]; intros st Hst.
  - split; [exact Hst|]; split; [apply rw_extends_refl|constructor].
  - rewrite rw_add_terms_cons.
    specialize (Ht st Hst); unfold rw_added in Ht.
    destruct (rw_add_term EN t st) as [st1 id].
    destruct Ht as [Hst1 [Hext1 [Hrepr Hroot]]].
    specialize (IHrest st1 Hst1); destruct (rw_add_terms EN ts st1) as [st2 ids].
    destruct IHrest as [Hst2 [Hext2 Hreprs]].
    split; [exact Hst2|]; split.
    + eapply rw_extends_trans; eassumption.
    + constructor; [exact (Hext2 id t Hrepr)|exact Hreprs].
Qed.

Lemma rw_add_term_correct {K Sort V H C} (EN : encoding (rw_node K Sort V))
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) :
  forall t, rw_typed sig t -> forall st, rw_store_ok sig admissible rules st ->
    rw_added sig admissible rules st t (rw_add_term EN t st).
Proof.
  fix IH 2; intros t Htyped st Hst; destruct Htyped as [s v Hsort|s op ts Htypes Hshape].
  - apply rw_intern_correct; [exact Hst|exact Hsort|constructor].
  - assert (Hterms : Forall (fun t => forall st, rw_store_ok sig admissible rules st ->
        rw_added sig admissible rules st t (rw_add_term EN t st)) ts).
    { clear Hshape; induction Htypes as [|t ts Ht Hrest IHrest]; constructor.
      - exact (IH t Ht).
      - exact IHrest. }
    pose proof (rw_add_terms_correct EN sig admissible rules ts Hterms st Hst) as Hchildren.
    change (rw_added sig admissible rules st (RWApp s op ts)
      (let '(st', ids) := rw_add_terms EN ts st in rw_intern EN st' (RWNApp s op ids))).
    destruct (rw_add_terms EN ts st) as [st' ids].
    destruct Hchildren as [Hst' [Hext Hreprs]].
    assert (Hvalid : rw_node_valid sig (rw_store_graph st') (RWNApp s op ids)).
    { exists (map rw_sort ts); split; [|exact Hshape].
      clear Hterms Htypes Hshape Hext; induction Hreprs as [|id t ids ts Ht Hrest IHrest];
        cbn; constructor.
      - exact (rw_layout_represents_sort sig _
          id t (rw_store_layout sig admissible rules st' Hst') Ht).
      - exact IHrest. }
    pose proof (rw_intern_correct EN sig admissible rules st' (RWNApp s op ids)
      (RWApp s op ts) Hst' Hvalid (rw_node_repr_app _ s op ids ts Hreprs)) as Hresult.
    unfold rw_added in *; destruct (rw_intern EN st' (RWNApp s op ids)) as [st'' c].
    destruct Hresult as [Hst'' [Hext' [Hrepr Hroot]]].
    split; [exact Hst''|]; split; [eapply rw_extends_trans; eassumption|].
    split; assumption.
Qed.

(** Term insertion prepares one canonical memo table and one fresh-key bound. *)
Definition rw_add {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (t : rw_term K Sort V) : rw_graph K Sort V * rw_id :=
  let EN := rw_node_encoding EK ES EV in
  let '(st, c) := rw_add_term EN t (RwStore g (rw_memo EN g) (rw_first_fresh g)) in
  (rw_store_graph st, c).

(** Interning a typed finite term preserves all invariants and returns its represented class. *)
Theorem rw_add_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (g : rw_graph K Sort V) (t : rw_term K Sort V) :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g -> rw_typed sig t ->
  let '(g', c) := rw_add EK ES EV g t in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g' /\ rw_represents g' c t.
Proof.
  intros Hwf Hsound Hproductive Htyped; unfold rw_add.
  pose proof (rw_wf_layout sig g Hwf) as Hlayout.
  assert (Hst : rw_store_ok sig admissible rules
      (RwStore g (rw_memo (rw_node_encoding EK ES EV) g) (rw_first_fresh g))).
  { constructor; try assumption; exact (rw_first_fresh_bound sig g Hlayout). }
  pose proof (rw_add_term_correct (rw_node_encoding EK ES EV) sig admissible rules
    t Htyped _ Hst) as Hresult.
  unfold rw_added in Hresult; destruct (rw_add_term _ t _) as [st c].
  destruct Hresult as [[Hlayout' Hsound' Hproductive' Hbound] [Hext [Hrepr Hroot]]].
  split; [apply rw_layout_wf; exact Hlayout'|].
  exact (conj Hsound' (conj Hproductive' (conj Hext Hrepr))).
Qed.
