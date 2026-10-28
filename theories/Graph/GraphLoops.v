(** * Recursive loop nesting

    Recursive SCC decomposition removes the first reverse-postorder vertex of each loop.
    For example, removing an outer header exposes the SCC of a nested inner loop.
    Builds on: GraphCore, GraphPrepare, GraphDfs, GraphScc and Collections maps and sets. *)

From Stdlib Require Import List Bool Arith NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
Import List.ListNotations.

(** Headers are outer-first; node sets include nested loops and owners select innermost loops. *)
Record loop_forest (V : Type) : Type := LoopForest {
  loop_headers : list V;
  loop_nodes : Map.t V (FinSet.t V);
  loop_parent : Map.t V V;
  loop_of : Map.t V V
}.
Arguments LoopForest {V}.
Arguments loop_headers {V}.
Arguments loop_nodes {V}.
Arguments loop_parent {V}.
Arguments loop_of {V}.

(** Membership uses the stored complete set of a loop. *)
Definition in_loop {V} (EV : encoding V) (f : loop_forest V) (h x : V) : Prop :=
  exists s, Map.get EV h (loop_nodes f) = Some s /\ FinSet.mem EV x s = true.

(** A child lives in its parent's nodes minus that parent's header. *)
Definition outer_nodes {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (f : loop_forest V) (h : V) : FinSet.t V :=
  match Map.get EV h (loop_parent f) with
  | Some h' =>
    match Map.get EV h' (loop_nodes f) with
    | Some s => FinSet.remove EV h' s
    | None => FinSet.empty
    end
  | None => visited (dfs p FinSet.empty (Graph.entries g))
  end.

(** A strong component is a nonempty maximal mutual-reachability class. *)
Definition strong_component {V E} (g : Graph.t V E) (S : V -> Prop) : Prop :=
  (exists v, S v) /\
  (forall u v, S u -> S v -> mutual g u v) /\
  (forall u v, S u -> mutual g u v -> S v).

(** One emitted loop stores its immediate parent and its members in SCC emission order. *)
Record loop_entry (V : Type) : Type := LoopEntry {
  loop_head : V;
  loop_members : list V;
  loop_enclosing : option V;
  loop_region : list V
}.
Arguments LoopEntry {V}.
Arguments loop_head {V}.
Arguments loop_members {V}.
Arguments loop_enclosing {V}.
Arguments loop_region {V}.

(** Finishing numbers give constant-index comparisons for the first vertex in reverse postorder. *)
Definition loop_rank {V} (EV : encoding V) (numbers : Map.t V positive) (v : V) : positive :=
  match Map.get EV v numbers with
  | Some n => n
  | None => 1%positive
  end.

(** Choose the maximum finishing number by a single component traversal. *)
Fixpoint loop_choose {V} (EV : encoding V) (numbers : Map.t V positive) (c : list V)
    : option V :=
  match c with
  | [] => None
  | v :: rest =>
    match loop_choose EV numbers rest with
    | None => Some v
    | Some w =>
      Some (if Pos.leb (loop_rank EV numbers w) (loop_rank EV numbers v) then v else w)
    end
  end.

(** Delete only the chosen header; membership in unrelated lists is never scanned. *)
Definition loop_without {V} (EV : encoding V) (h : V) (c : list V) : list V :=
  filter (fun v => negb (Pos.eqb (encode EV v) (encode EV h))) c.

(** A singleton is a loop exactly when its prepared successor list contains a self edge. *)
Definition loop_cyclic {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (c : list V) : bool :=
  match c with
  | [] => false
  | [v] => existsb (fun e => Pos.eqb (encode EV (Graph.target g e)) (encode EV v))
      (succ_edges p v)
  | _ :: _ :: _ => true
  end.

(** A cyclic SCC emits one loop followed by the recursively exposed children. *)
Definition loop_block {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V))
    (parent : option V) (region c : list V) : list (loop_entry V) :=
  if loop_cyclic p c then
    match loop_choose EV numbers c with
    | Some h => LoopEntry h c parent region :: descend (Some h) (loop_without EV h c)
    | None => []
    end
  else [].

(** One layer computes SCCs without constructing a filtered graph or scanning unrelated lists. *)
Definition loop_layer {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (numbers : Map.t V positive)
    (descend : option V -> list V -> list (loop_entry V))
    (parent : option V) (region : list V) : list (loop_entry V) :=
  flat_map (loop_block p numbers descend parent region) (components (scc_within p region)).

(** Binary depth fuel suffices because every descent removes one distinct member of its region. *)
Definition loop_entries {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : list (loop_entry V) :=
  let search := dfs p FinSet.empty (Graph.entries g) in
  N.iter (N.of_nat (length (preorder search))) (loop_layer p (post_num search))
    (fun _ _ => []) None (preorder search).

(** Index optional entry values once; absent values create no binding. *)
Fixpoint loop_bindings {A K B} (EK : encoding K) (key : A -> K) (value : A -> option B)
    (entries : list A) : Map.t K B :=
  match entries with
  | [] => Map.empty
  | a :: rest =>
    let index := loop_bindings EK key value rest in
    match value a with
    | Some b => Map.set EK (key a) b index
    | None => index
    end
  end.

(** Later entries override earlier entries, so descendants own their members. *)
Fixpoint loop_owners {V} (EV : encoding V) (entries : list (loop_entry V)) : Map.t V V :=
  match entries with
  | [] => Map.empty
  | a :: rest =>
    Map.union_with (fun _ deeper => deeper)
      (Map.map (fun _ => loop_head a) (FinSet.of_list EV (loop_members a)))
      (loop_owners EV rest)
  end.

(** Materialize the four public observations without retaining the proof's regional witnesses. *)
Definition loop_pack {V} (EV : encoding V) (entries : list (loop_entry V)) : loop_forest V :=
  LoopForest (map loop_head entries)
    (loop_bindings EV loop_head (fun a => Some (FinSet.of_list EV (loop_members a))) entries)
    (loop_bindings EV loop_head loop_enclosing entries) (loop_owners EV entries).

(** Construct the actual recursive nesting forest over the reachable part of the graph. *)
Definition loop_forest_of {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : loop_forest V :=
  loop_pack EV (loop_entries p).

(** * Region and component facts *)

Lemma loop_without_spec {V} (EV : encoding V) h c v :
  In v (loop_without EV h c) <-> In v c /\ v <> h.
Proof.
  unfold loop_without; rewrite filter_In, negb_true_iff, Pos.eqb_neq.
  split; intros [Hin Hne]; split; [exact Hin| |exact Hin|].
  - intro Heq; subst v; contradiction.
  - intro Heq; apply Hne; apply (encode_injective EV); exact Heq.
Qed.

Lemma loop_before_app {A} (xs ys : list A) a b :
  before (xs ++ ys) a b ->
  before xs a b \/ before ys a b \/ (In a xs /\ In b ys).
Proof.
  induction xs as [|x xs IH]; cbn [app]; [auto|].
  rewrite dfs_before_cons; intros [[Heq Hin]|Hbefore].
  - subst a; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + left; apply dfs_before_cons; left; auto.
    + right; right; split; [left; reflexivity|exact Hin].
  - destruct (IH Hbefore) as [Hleft|[Hright|[Ha Hb]]].
    + left; apply dfs_before_cons; right; exact Hleft.
    + right; left; exact Hright.
    + right; right; split; [right; exact Ha|exact Hb].
Qed.

Lemma loop_before_suffix {A} (xs ys : list A) a b :
  before ys a b -> before (xs ++ ys) a b.
Proof.
  intros [first [middle [last Heq]]]; exists (xs ++ first), middle, last.
  rewrite Heq, app_assoc; reflexivity.
Qed.

Lemma loop_before_prefix {A} (xs ys : list A) a b :
  before xs a b -> before (xs ++ ys) a b.
Proof.
  intros [first [middle [last Heq]]]; exists first, middle, (last ++ ys).
  rewrite Heq, <- !app_assoc; cbn [app]; rewrite <- app_assoc; reflexivity.
Qed.

Lemma loop_before_members {A} (xs : list A) a b : before xs a b -> In a xs /\ In b xs.
Proof.
  intros [first [middle [last Heq]]]; subst xs; split.
  - apply in_or_app; right; left; reflexivity.
  - apply in_or_app; right; right; apply in_or_app; right; left; reflexivity.
Qed.

Lemma loop_nodup_app {A} (xs ys : list A) :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> ~ In x ys) -> NoDup (xs ++ ys).
Proof.
  intros Hxs Hys Hdisjoint; induction Hxs as [|x xs Hfresh Hxs IH]; cbn; [exact Hys|].
  constructor.
  - rewrite in_app_iff; intros [Hin|Hin].
    + exact (Hfresh Hin).
    + exact (Hdisjoint x (or_introl eq_refl) Hin).
  - apply IH; intros y Hin; apply Hdisjoint; right; exact Hin.
Qed.

(** The semantic obligations of one component are independent of the map representation. *)
Definition loop_entry_exact {V E} (EV : encoding V) (g : Graph.t V E) (order : list V)
    (a : loop_entry V) : Prop :=
  In (loop_head a) (loop_members a) /\
  incl (loop_members a) (loop_region a) /\
  strong_component (induced EV (FinSet.of_list EV (loop_region a)) g)
    (fun v => In v (loop_members a)) /\
  (exists es, es <> [] /\
    path (induced EV (FinSet.of_list EV (loop_region a)) g) (loop_head a) es (loop_head a)) /\
  forall y, In y (loop_members a) -> y = loop_head a \/ before order (loop_head a) y.

(** Earlier overlapping entries contain every later member, and parents identify exact regions. *)
Record loop_valid {V E} (EV : encoding V) (g : Graph.t V E) (order region : list V)
    (parent : option V) (entries : list (loop_entry V)) : Prop := {
  loop_valid_domain : forall a, In a entries -> incl (loop_members a) region;
  loop_valid_heads : NoDup (map loop_head entries);
  loop_valid_exact : forall a, In a entries -> loop_entry_exact EV g order a;
  loop_valid_parents : forall a, In a entries ->
    (loop_enclosing a = parent /\
      forall y, In y (loop_region a) <-> In y region) \/
    exists b, before entries b a /\ loop_enclosing a = Some (loop_head b) /\
      forall y, In y (loop_region a) <-> In y (loop_members b) /\ y <> loop_head b;
  loop_valid_order : forall a b, before entries a b ->
    forall y, In y (loop_members a) -> In y (loop_members b) ->
      incl (loop_members b) (loop_members a) /\ ~ In (loop_head a) (loop_members b)
}.

Lemma loop_valid_empty {V E} (EV : encoding V) (g : Graph.t V E) order region parent :
  loop_valid EV g order region parent [].
Proof.
  constructor; cbn; try (intros; contradiction); [constructor|].
  intros a b Hbefore; apply loop_before_members in Hbefore.
  destruct Hbefore as [Hin _]; contradiction.
Qed.

Lemma loop_valid_append {V E} (EV : encoding V) (g : Graph.t V E)
    order region parent left right :
  loop_valid EV g order region parent left -> loop_valid EV g order region parent right ->
  (forall a b y, In a left -> In b right ->
    In y (loop_members a) -> ~ In y (loop_members b)) ->
  loop_valid EV g order region parent (left ++ right).
Proof.
  intros Hl Hr Hdisjoint; constructor.
  - intros a Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + exact (loop_valid_domain _ _ _ _ _ _ Hl a Hin).
    + exact (loop_valid_domain _ _ _ _ _ _ Hr a Hin).
  - rewrite map_app; apply loop_nodup_app;
      [exact (loop_valid_heads _ _ _ _ _ _ Hl)|exact (loop_valid_heads _ _ _ _ _ _ Hr)|].
    intros h Ha Hb; apply in_map_iff in Ha, Hb.
    destruct Ha as [a [Ha Hain]], Hb as [b [Hb Hbin]].
    destruct (loop_valid_exact _ _ _ _ _ _ Hl a Hain) as [Hself _].
    apply (Hdisjoint a b h Hain Hbin); [rewrite <- Ha; exact Hself|].
    rewrite <- Hb; exact (proj1 (loop_valid_exact _ _ _ _ _ _ Hr b Hbin)).
  - intros a Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + exact (loop_valid_exact _ _ _ _ _ _ Hl a Hin).
    + exact (loop_valid_exact _ _ _ _ _ _ Hr a Hin).
  - intros a Hin; apply in_app_iff in Hin; destruct Hin as [Hin|Hin].
    + destruct (loop_valid_parents _ _ _ _ _ _ Hl a Hin) as [Hroot|[b [Hbefore Hrest]]].
      * left; exact Hroot.
      * right; exists b; split; [apply loop_before_prefix; exact Hbefore|exact Hrest].
    + destruct (loop_valid_parents _ _ _ _ _ _ Hr a Hin) as [Hroot|[b [Hbefore Hrest]]].
      * left; exact Hroot.
      * right; exists b; split; [apply loop_before_suffix; exact Hbefore|exact Hrest].
  - intros a b Hbefore y Hay Hby; apply loop_before_app in Hbefore.
    destruct Hbefore as [Hleft|[Hright|[Ha Hb]]].
    + exact (loop_valid_order _ _ _ _ _ _ Hl a b Hleft y Hay Hby).
    + exact (loop_valid_order _ _ _ _ _ _ Hr a b Hright y Hay Hby).
    + exfalso; exact (Hdisjoint a b y Ha Hb Hay Hby).
Qed.

Lemma loop_valid_node {V E} (EV : encoding V) (g : Graph.t V E)
    order region parent h c children :
  loop_entry_exact EV g order (LoopEntry h c parent region) ->
  loop_valid EV g order (loop_without EV h c) (Some h) children ->
  loop_valid EV g order region parent (LoopEntry h c parent region :: children).
Proof.
  intros Hroot Hchildren.
  destruct Hroot as [Hself [Hsub Hrest]].
  constructor.
  - intros a [Heq|Hin].
    + subst a; exact Hsub.
    + intros y Hy; apply Hsub.
      pose proof (loop_valid_domain _ _ _ _ _ _ Hchildren a Hin y Hy) as Hchild.
      apply loop_without_spec in Hchild; tauto.
  - cbn; constructor; [|exact (loop_valid_heads _ _ _ _ _ _ Hchildren)].
    intro Hin; apply in_map_iff in Hin; destruct Hin as [a [Heq Hin]].
    pose proof (proj1 (loop_valid_exact _ _ _ _ _ _ Hchildren a Hin)) as Hhead.
    pose proof (loop_valid_domain _ _ _ _ _ _ Hchildren a Hin _ Hhead) as Hdomain.
    apply loop_without_spec in Hdomain; cbn in Heq; tauto.
  - intros a [Heq|Hin].
    + subst a; split; [exact Hself|split; assumption].
    + exact (loop_valid_exact _ _ _ _ _ _ Hchildren a Hin).
  - intros a [Heq|Hin].
    + subst a; left; split; [reflexivity|intro y; reflexivity].
    + destruct (loop_valid_parents _ _ _ _ _ _ Hchildren a Hin)
        as [[Hparent Hregion]|[b [Hbefore Hrest']]].
      * right; exists (LoopEntry h c parent region); split.
        -- apply dfs_before_cons; left; auto.
        -- split; [exact Hparent|]; intro y; rewrite Hregion, loop_without_spec; reflexivity.
      * right; exists b; split; [apply dfs_before_cons; right; exact Hbefore|exact Hrest'].
  - intros a b Hbefore y Hay Hby; apply dfs_before_cons in Hbefore.
    destruct Hbefore as [[Heq Hin]|Hbefore].
    + subst a; split.
      * intros z Hz.
        pose proof (loop_valid_domain _ _ _ _ _ _ Hchildren b Hin z Hz) as Hdomain.
        apply loop_without_spec in Hdomain; exact (proj1 Hdomain).
      * intro Hbad.
        pose proof (loop_valid_domain _ _ _ _ _ _ Hchildren b Hin h Hbad) as Hdomain.
        apply loop_without_spec in Hdomain; tauto.
    + exact (loop_valid_order _ _ _ _ _ _ Hchildren a b Hbefore y Hay Hby).
Qed.

Lemma loop_choose_spec {V} (EV : encoding V) numbers c h :
  loop_choose EV numbers c = Some h ->
  In h c /\ forall v, In v c -> (loop_rank EV numbers v <= loop_rank EV numbers h)%positive.
Proof.
  revert h; induction c as [|v rest IH]; intro h; cbn [loop_choose]; [discriminate|].
  destruct (loop_choose EV numbers rest) as [w|] eqn:Hchoose.
  - destruct (Pos.leb (loop_rank EV numbers w) (loop_rank EV numbers v)) eqn:Hle;
      intro Heq; inversion Heq; subst h; destruct (IH w eq_refl) as [Hw Hmax].
    + split; [left; reflexivity|].
      intros y [Hy|Hin]; [subst y; apply Pos.le_refl|].
      apply Pos.leb_le in Hle; eapply Pos.le_trans; [apply Hmax; exact Hin|exact Hle].
    + split; [right; exact Hw|].
      intros y [Hy|Hin]; [subst y; apply Pos.lt_le_incl; apply Pos.leb_gt; exact Hle|].
      apply Hmax; exact Hin.
  - intro Heq; inversion Heq; subst h; split; [left; reflexivity|].
    intros y [Hy|Hin]; [subst y; apply Pos.le_refl|].
    destruct rest as [|a tail]; [contradiction|].
    cbn [loop_choose] in Hchoose; destruct (loop_choose EV numbers tail); discriminate.
Qed.

Lemma loop_choose_nonempty {V} (EV : encoding V) numbers c :
  c <> [] -> exists h, loop_choose EV numbers c = Some h.
Proof.
  destruct c as [|v rest]; [contradiction|].
  cbn [loop_choose]; destruct (loop_choose EV numbers rest); eauto.
Qed.

Lemma loop_path_induced {V E} (EV : encoding V) (g : Graph.t V E) keep u es v :
  path (induced EV keep g) u es v <->
  path g u es v /\ forall e, In e es -> FinSet.mem EV (Graph.target g e) keep = true.
Proof.
  split.
  - intro Hpath; induction Hpath as [v|e es v Hedge Hpath [IH Htargets]].
    + split; [constructor|intros e Hin; contradiction].
    + apply filter_In in Hedge; destruct Hedge as [Hedge Htarget].
      split; [exact (@path_cons V E g e es v Hedge IH)|].
      intros a [Heq|Hin]; [subst a; exact Htarget|apply Htargets; exact Hin].
  - intros [Hpath Htargets]; induction Hpath as [v|e es v Hedge Hpath IH].
    + constructor.
    + apply (@path_cons V E (induced EV keep g) e es v).
      * apply filter_In; split; [exact Hedge|apply Htargets; left; reflexivity].
      * apply IH; intros a Hin; apply Htargets; right; exact Hin.
Qed.

Lemma loop_path_endpoint {V E} (g : Graph.t V E) u es v :
  path g u es v -> v = u \/ In v (map (Graph.target g) es).
Proof.
  intro Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; [auto|].
  right; cbn; destruct IH as [Heq|Hin]; [left; symmetry; exact Heq|right; exact Hin].
Qed.

Lemma loop_path_region {V E} (EV : encoding V) (g : Graph.t V E) region u es v :
  In u region -> path (induced EV (FinSet.of_list EV region) g) u es v -> In v region.
Proof.
  intros Hu Hpath; destruct (loop_path_endpoint _ _ _ _ Hpath) as [Heq|Hin].
  - subst v; exact Hu.
  - apply in_map_iff in Hin; destruct Hin as [e [Heq Hin]].
    apply loop_path_induced in Hpath; destruct Hpath as [_ Htargets].
    subst v; change (In (Graph.target g e) region).
    apply (proj1 (FinSet.of_list_spec EV _ _)); apply Htargets; exact Hin.
Qed.

Lemma loop_path_split {V E} (g : Graph.t V E) u es v e :
  path g u es v -> In e es ->
  exists first last, path g u first (Graph.target g e) /\
    path g (Graph.target g e) last v /\ first ++ last = es.
Proof.
  intro Hpath; induction Hpath as [v|a es v Hedge Hpath IH]; intro Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst a; exists [e], es; split; [constructor; [exact Hedge|constructor]|auto].
  - destruct (IH Hin) as [first [last [Hfirst [Hlast Heq]]]].
    exists (a :: first), last; split; [constructor; assumption|].
    split; [exact Hlast|cbn; rewrite Heq; reflexivity].
Qed.

Lemma loop_cycle_mutual {V E} (g : Graph.t V E) v es y :
  path g v es v -> (y = v \/ In y (map (Graph.target g) es)) -> mutual g v y.
Proof.
  intros Hpath [Heq|Hin].
  - subst y; split; exists []; constructor.
  - apply in_map_iff in Hin; destruct Hin as [e [Heq Hin]]; subst y.
    destruct (loop_path_split _ _ _ _ e Hpath Hin) as [first [last [Hfirst [Hlast _]]]].
    split; [exists first|exists last]; assumption.
Qed.

Lemma loop_component_owner {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region c :
  In c (components (scc_within p region)) ->
  exists i, forall v, Map.get EV v (comp_of (scc_within p region)) = Some i <-> In v c.
Proof.
  intro Hc; destruct (scc_within_indexes EV g p region)
    as [_ [_ [Hlength [Hat [_ [Howner _]]]]]].
  destruct (tarjan_combine_total_right _ _ c Hlength Hc) as [i Hi].
  apply Hat in Hi; exists i; intro v; rewrite Howner.
  split.
  - intros [d [Hd Hv]]; rewrite Hi in Hd; inversion Hd; subst d; exact Hv.
  - intro Hv; exists c; auto.
Qed.

Lemma loop_component_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region c :
  ready EV g p -> incl region (Graph.nodes g) ->
  In c (components (scc_within p region)) ->
  NoDup c /\ incl c region /\
  strong_component (induced EV (FinSet.of_list EV region) g) (fun v => In v c).
Proof.
  intros Hready Hregion Hc.
  destruct (scc_within_indexes EV g p region) as [Hnodup [Hnonempty _]].
  pose proof (scc_within_members EV g p region Hready Hregion) as Hmembers.
  assert (Hsub : incl c region).
  { intros v Hv; apply Hmembers; apply in_concat; exists c; auto. }
  split.
  - destruct (in_split c _ Hc) as [first [last Hsplit]].
    rewrite Hsplit, concat_app in Hnodup; cbn [concat] in Hnodup.
    apply (tarjan_nodup_prefix c (concat last)).
    apply (tarjan_nodup_suffix (concat first) (c ++ concat last)); exact Hnodup.
  - split; [exact Hsub|].
    destruct (loop_component_owner EV g p region c Hc) as [i Hi].
    split.
    + destruct c as [|v rest]; [exfalso; apply (Hnonempty [] Hc); reflexivity|].
      exists v; left; reflexivity.
    + split.
      * intros u v Hu Hv; apply (proj1 (scc_within_mutual EV g p region u v
          Hready Hregion (Hsub u Hu) (Hsub v Hv))).
        exists i; split; apply Hi; assumption.
      * intros u v Hu Hmutual.
        destruct Hmutual as [[first Hfirst] [last Hlast]].
        assert (Hv : In v region) by (eapply loop_path_region; eauto).
        destruct (proj2 (scc_within_mutual EV g p region u v Hready Hregion
          (Hsub u Hu) Hv) (conj (ex_intro _ first Hfirst) (ex_intro _ last Hlast)))
          as [j [Huj Hvj]].
        apply Hi in Hu; rewrite Hu in Huj; inversion Huj; subst j; apply Hi; exact Hvj.
Qed.

Lemma loop_rank_order {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) h y :
  ready EV g p -> In h (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  In y (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  (loop_rank EV (post_num (dfs p FinSet.empty (Graph.entries g))) y <=
    loop_rank EV (post_num (dfs p FinSet.empty (Graph.entries g))) h)%positive ->
  y = h \/ before (rpo (dfs p FinSet.empty (Graph.entries g))) h y.
Proof.
  intros Hready Hh Hy Hle; pose proof Hready as [Hwf _].
  destruct (dfs_final_spec EV g p FinSet.empty (Graph.entries g) Hready (entries_in Hwf))
    as [Hinv [Hlabels _]].
  set (st := fold_left (dfs_root p FinSet.empty) (Graph.entries g) dfs_initial) in *.
  change (In h (rev (DfsState.pre st))) in Hh.
  change (In y (rev (DfsState.pre st))) in Hy.
  apply (proj2 (in_rev _ _)) in Hh, Hy.
  destruct (dfs_final_post_number EV g FinSet.empty (Graph.entries g) st h Hinv Hlabels Hh)
    as [a Ha].
  destruct (dfs_final_post_number EV g FinSet.empty (Graph.entries g) st y Hinv Hlabels Hy)
    as [b Hb].
  change (loop_rank EV (DfsState.post_index st) y <=
    loop_rank EV (DfsState.post_index st) h)%positive in Hle.
  unfold loop_rank in Hle; rewrite Ha, Hb in Hle.
  destruct (Pos.eq_dec b a) as [Heq|Hne].
  - left; subst b; eapply dfs_numbering_injective;
      [exact (dfs_post_numbering _ _ _ _ Hlabels)|exact Hb|exact Ha].
  - right; unfold rpo, dfs; change (before (rev (rev (DfsState.post st))) h y).
    rewrite rev_involutive; apply (proj2 (dfs_before_reverse (DfsState.post st) h y)).
    apply (proj2 (dfs_numbering_order EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)
      y h b a Hb Ha)); apply Pos.lt_eq_cases in Hle; tauto.
Qed.

Lemma loop_without_length {V} (EV : encoding V) h c :
  In h c -> length (loop_without EV h c) < length c.
Proof.
  unfold loop_without; induction c as [|v rest IH]; intro Hin; [contradiction|].
  cbn [filter]; destruct (Pos.eqb (encode EV v) (encode EV h)) eqn:Heq; cbn.
  - apply Nat.lt_succ_r.
    rewrite <- (filter_length (fun v => negb (Pos.eqb (encode EV v) (encode EV h))) rest).
    apply Nat.le_add_r.
  - destruct Hin as [Heqh|Hin].
    + subst v; rewrite Pos.eqb_refl in Heq; discriminate.
    + specialize (IH Hin); lia.
Qed.

Lemma loop_component_cycle {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region c h :
  ready EV g p -> incl region (Graph.nodes g) ->
  NoDup c -> incl c region -> In h c ->
  strong_component (induced EV (FinSet.of_list EV region) g) (fun v => In v c) ->
  loop_cyclic p c = true ->
  exists es, es <> [] /\ path (induced EV (FinSet.of_list EV region) g) h es h.
Proof.
  intros Hready Hregion Hnodup Hsub Hh [_ [Hmutual _]] Hcyclic.
  destruct c as [|v [|w rest]]; [contradiction| |].
  - destruct Hh as [Heq|Hin]; [subst v|contradiction].
    apply existsb_exists in Hcyclic; destruct Hcyclic as [e [He Hedge]].
    apply Pos.eqb_eq in Hedge; apply (encode_injective EV) in Hedge.
    pose proof Hready as [Hwf [_ Hprepared]].
    rewrite (succ_agrees Hprepared h (Hregion h (Hsub h (or_introl eq_refl)))) in He.
    pose proof (out_source Hwf h e He) as Hsource.
    exists [e]; split; [discriminate|].
    rewrite <- Hsource at 1; rewrite <- Hedge at 1.
    apply (@path_cons V E (induced EV (FinSet.of_list EV region) g) e []
      (Graph.target g e)); [|constructor].
    change (In e (filter (fun e => FinSet.mem EV (Graph.target g e)
      (FinSet.of_list EV region)) (Graph.out g (Graph.source g e)))).
    apply filter_In; split; [rewrite Hsource; exact He|].
    apply FinSet.of_list_spec; rewrite Hedge; apply Hsub; left; reflexivity.
  - assert (Hother : exists y, In y (v :: w :: rest) /\ y <> h).
    { destruct (dfs_eq_dec EV v h) as [Heq|Hne].
      - subst v; exists w; split; [right; left; reflexivity|].
        inversion Hnodup as [|a tail Hfresh Htail]; subst.
        intro Heq; subst w; apply Hfresh; left; reflexivity.
      - exists v; split; [left; reflexivity|exact Hne]. }
    destruct Hother as [y [Hy Hne]].
    destruct (Hmutual h y Hh Hy) as [[first Hfirst] [last Hlast]].
    exists (first ++ last); split.
    + intro Hempty; apply app_eq_nil in Hempty; destruct Hempty as [Hempty _].
      subst first; inversion Hfirst; subst y; apply Hne; reflexivity.
    + eapply tarjan_path_append; eauto.
Qed.

Lemma loop_cycle_component {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region c v es :
  ready EV g p -> incl region (Graph.nodes g) -> incl c region ->
  In v c -> es <> [] -> path (induced EV (FinSet.of_list EV region) g) v es v ->
  (forall y, y = v \/ In y (map (Graph.target g) es) -> In y c) ->
  loop_cyclic p c = true.
Proof.
  intros Hready Hregion Hsub Hv Hnonempty Hpath Hpoints.
  destruct c as [|h [|w rest]]; [contradiction| |reflexivity].
  destruct Hv as [Heq|Hin]; [subst h|contradiction].
  destruct es as [|e es]; [contradiction|].
  inversion Hpath as [|a tail endpoint Hedge Htail]; subst.
  assert (Htarget : Graph.target g e = Graph.source g e).
  { specialize (Hpoints (Graph.target g e) (or_intror (or_introl eq_refl))).
    cbn in Hpoints; destruct Hpoints as [Heq|Hin]; [symmetry; exact Heq|contradiction]. }
  cbn [loop_cyclic]; apply existsb_exists; exists e; split.
  - pose proof Hready as [_ [_ Hprepared]].
    rewrite (succ_agrees Hprepared _ (Hregion _ (Hsub _ (or_introl eq_refl)))) .
    apply filter_In in Hedge; exact (proj1 Hedge).
  - rewrite Htarget; apply Pos.eqb_refl.
Qed.

Lemma loop_search_domain {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p ->
  incl (preorder (dfs p FinSet.empty (Graph.entries g))) (Graph.nodes g).
Proof.
  intros Hready v Hin; pose proof Hready as [Hwf _].
  destruct (dfs_exact EV g p v (Graph.entries g) FinSet.empty Hready (entries_in Hwf))
    as [_ [_ [_ Hpre]]].
  apply (reachable_in_nodes g v Hwf); apply (reachable_dfs EV g p v Hready).
  apply Hpre; exact Hin.
Qed.

Lemma loop_blocks_valid {V E} (EV : encoding V) (g : Graph.t V E)
    order region parent (blocks : list V -> list (loop_entry V)) cs :
  NoDup (concat cs) ->
  (forall c, In c cs -> loop_valid EV g order region parent (blocks c) /\
    forall a, In a (blocks c) -> incl (loop_members a) c) ->
  loop_valid EV g order region parent (flat_map blocks cs).
Proof.
  induction cs as [|c rest IH]; intros Hnodup Hblocks; cbn [flat_map];
    [apply loop_valid_empty|].
  cbn [concat] in Hnodup.
  destruct (Hblocks c (or_introl eq_refl)) as [Hc Hcdomain].
  apply loop_valid_append; [exact Hc| |].
  - apply IH.
    + apply (tarjan_nodup_suffix c); exact Hnodup.
    + intros d Hd; apply Hblocks; right; exact Hd.
  - intros a b y Ha Hb Hay Hby; apply in_flat_map in Hb.
    destruct Hb as [d [Hd Hb]].
    destruct (Hblocks d (or_intror Hd)) as [_ Hddomain].
    apply (tarjan_nodup_disjoint c (concat rest) Hnodup y (Hcdomain a Ha y Hay)).
    apply in_concat; exists d; split; [exact Hd|exact (Hddomain b Hb y Hby)].
Qed.

Lemma loop_block_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region parent descend c :
  ready EV g p -> incl region (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  In c (components (scc_within p region)) ->
  (forall child parent', incl child region -> length child < length region ->
    loop_valid EV g (rpo (dfs p FinSet.empty (Graph.entries g))) child parent'
      (descend parent' child)) ->
  loop_valid EV g (rpo (dfs p FinSet.empty (Graph.entries g))) region parent
    (loop_block p (post_num (dfs p FinSet.empty (Graph.entries g))) descend parent region c) /\
  forall a, In a
    (loop_block p (post_num (dfs p FinSet.empty (Graph.entries g))) descend parent region c) ->
    incl (loop_members a) c.
Proof.
  intros Hready Hregion Hc Hdescend.
  assert (Hnodes : incl region (Graph.nodes g)).
  { intros v Hv; apply (loop_search_domain EV g p Hready); apply Hregion; exact Hv. }
  destruct (loop_component_spec EV g p region c Hready Hnodes Hc)
    as [Hnodup [Hsub Hstrong]].
  unfold loop_block; destruct (loop_cyclic p c) eqn:Hcyclic;
    [|split; [apply loop_valid_empty|intros a Hin; contradiction]].
  destruct (loop_choose EV (post_num (dfs p FinSet.empty (Graph.entries g))) c)
    as [h|] eqn:Hchoose; [|split; [apply loop_valid_empty|intros a Hin; contradiction]].
  destruct (loop_choose_spec EV _ c h Hchoose) as [Hh Hrank].
  assert (Hchildsub : incl (loop_without EV h c) region).
  { intros v Hv; apply loop_without_spec in Hv; apply Hsub; tauto. }
  assert (Hchildsmall : length (loop_without EV h c) < length region).
  { pose proof (loop_without_length EV h c Hh).
    pose proof (NoDup_incl_length Hnodup Hsub); lia. }
  pose proof (Hdescend _ (Some h) Hchildsub Hchildsmall) as Hchildren.
  split.
  - apply loop_valid_node; [|exact Hchildren].
    split; [exact Hh|]; split; [exact Hsub|]; split; [exact Hstrong|]; split.
    + apply (loop_component_cycle EV g p region c h Hready Hnodes Hnodup Hsub Hh
        Hstrong Hcyclic).
    + intros y Hy; apply (loop_rank_order EV g p h y Hready
        (Hregion h (Hsub h Hh)) (Hregion y (Hsub y Hy)) (Hrank y Hy)).
  - intros a [Heq|Hin] y Hy.
    + subst a; exact Hy.
    + pose proof (loop_valid_domain _ _ _ _ _ _ Hchildren a Hin y Hy) as Hdomain.
      apply loop_without_spec in Hdomain; exact (proj1 Hdomain).
Qed.

Lemma loop_iter_valid {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> forall n region parent,
  incl region (preorder (dfs p FinSet.empty (Graph.entries g))) ->
  length region <= N.to_nat n ->
  loop_valid EV g (rpo (dfs p FinSet.empty (Graph.entries g))) region parent
    (N.iter n (loop_layer p (post_num (dfs p FinSet.empty (Graph.entries g))))
      (fun _ _ => []) parent region).
Proof.
  intro Hready; induction n using N.peano_ind; intros region parent Hregion Hlength.
  - apply loop_valid_empty.
  - rewrite N.iter_succ; unfold loop_layer at 1.
    apply loop_blocks_valid.
    + exact (proj1 (scc_within_indexes EV g p region)).
    + intros c Hc; apply loop_block_valid; [exact Hready|exact Hregion|exact Hc|].
      intros child parent' Hsub Hsmall; apply IHn.
      * intros v Hv; apply Hregion; apply Hsub; exact Hv.
      * rewrite N2Nat.inj_succ in Hlength; lia.
Qed.

Lemma loop_entries_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p ->
  loop_valid EV g (rpo (dfs p FinSet.empty (Graph.entries g)))
    (preorder (dfs p FinSet.empty (Graph.entries g))) None (loop_entries p).
Proof.
  intro Hready; unfold loop_entries; apply loop_iter_valid; [exact Hready| |].
  - intros v Hv; exact Hv.
  - rewrite Nat2N.id; apply Nat.le_refl.
Qed.

(** * Cycle coverage of the recursive producer *)

Lemma loop_cycle_scc {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region v es :
  ready EV g p -> incl region (Graph.nodes g) -> In v region -> es <> [] ->
  path (induced EV (FinSet.of_list EV region) g) v es v ->
  exists c, In c (components (scc_within p region)) /\ NoDup c /\ incl c region /\
    In v c /\ loop_cyclic p c = true /\
    forall y, y = v \/ In y (map (Graph.target g) es) -> In y c.
Proof.
  intros Hready Hregion Hv Hnonempty Hpath.
  destruct (scc_within_owner_total EV g p region v Hready Hregion Hv) as [i Hi].
  destruct (scc_within_indexes EV g p region) as [_ [_ [_ [Hat [_ [Howner _]]]]]].
  apply Howner in Hi; destruct Hi as [c [Hc Hvc]].
  assert (Hcin : In c (components (scc_within p region))).
  { apply Hat in Hc; eapply in_combine_r; exact Hc. }
  destruct (loop_component_spec EV g p region c Hready Hregion Hcin)
    as [Hnodup [Hsub Hstrong]].
  assert (Hpoints : forall y, y = v \/ In y (map (Graph.target g) es) -> In y c).
  { intros y Hy; apply (proj2 (proj2 Hstrong) v y Hvc).
    apply (loop_cycle_mutual (induced EV (FinSet.of_list EV region) g) v es y Hpath Hy). }
  exists c; split; [exact Hcin|]; split; [exact Hnodup|]; split; [exact Hsub|].
  split; [exact Hvc|]; split; [|exact Hpoints].
  exact (loop_cycle_component EV g p region c v es Hready Hregion Hsub Hvc
    Hnonempty Hpath Hpoints).
Qed.

Lemma loop_cycle_without {V E} (EV : encoding V) (g : Graph.t V E) region c h v es :
  path (induced EV (FinSet.of_list EV region) g) v es v ->
  (forall y, y = v \/ In y (map (Graph.target g) es) -> In y c) ->
  ~ In h (v :: map (Graph.target g) es) ->
  In v (loop_without EV h c) /\
  path (induced EV (FinSet.of_list EV (loop_without EV h c)) g) v es v.
Proof.
  intros Hpath Hpoints Hoff; split.
  - apply loop_without_spec; split; [apply Hpoints; left; reflexivity|].
    intro Heq; subst v; apply Hoff; left; reflexivity.
  - apply loop_path_induced; apply loop_path_induced in Hpath; split; [tauto|].
    intros e He; apply FinSet.of_list_spec; apply loop_without_spec; split.
    + apply Hpoints; right; apply in_map; exact He.
    + intro Heq; apply Hoff; right; rewrite <- Heq; apply in_map; exact He.
Qed.

Lemma loop_iter_covers {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> forall n region parent v es,
  incl region (Graph.nodes g) -> length region <= N.to_nat n -> In v region ->
  es <> [] -> path (induced EV (FinSet.of_list EV region) g) v es v ->
  exists a, In a (N.iter n (loop_layer p (post_num (dfs p FinSet.empty (Graph.entries g))))
      (fun _ _ => []) parent region) /\
    (loop_head a = v \/ In (loop_head a) (map (Graph.target g) es)) /\
    forall y, y = v \/ In y (map (Graph.target g) es) -> In y (loop_members a).
Proof.
  intro Hready; induction n using N.peano_ind;
    intros region parent v es Hregion Hlength Hv Hnonempty Hpath.
  - cbn in Hlength; destruct region; [contradiction|cbn in Hlength; lia].
  - destruct (loop_cycle_scc EV g p region v es Hready Hregion Hv Hnonempty Hpath)
      as [c [Hcin [Hnodup [Hsub [Hvc [Hcyclic Hpoints]]]]]].
    destruct (loop_choose_nonempty EV (post_num (dfs p FinSet.empty (Graph.entries g))) c
      ltac:(intro Heq; subst c; contradiction)) as [h Hchoose].
    destruct (loop_choose_spec EV _ c h Hchoose) as [Hh Hrank].
    rewrite N.iter_succ; unfold loop_layer at 1.
    destruct (in_dec (dfs_eq_dec EV) h (v :: map (Graph.target g) es)) as [Hon|Hoff].
    + exists (LoopEntry h c parent region); split.
      * apply in_flat_map; exists c; split; [exact Hcin|].
        unfold loop_block; rewrite Hcyclic, Hchoose; left; reflexivity.
      * split; [cbn; destruct Hon as [Heq|Hin]; [left; symmetry; exact Heq|right; exact Hin]|].
        exact Hpoints.
    + assert (Hchild : incl (loop_without EV h c) (Graph.nodes g)).
      { intros y Hy; apply loop_without_spec in Hy; apply Hregion; apply Hsub; tauto. }
      destruct (loop_cycle_without EV g region c h v es Hpath Hpoints Hoff)
        as [Hvchild Hpathchild].
      assert (Hsmall : length (loop_without EV h c) <= N.to_nat n).
      { pose proof (loop_without_length EV h c Hh).
        pose proof (NoDup_incl_length Hnodup Hsub).
        rewrite N2Nat.inj_succ in Hlength; lia. }
      destruct (IHn _ (Some h) v es Hchild Hsmall Hvchild Hnonempty Hpathchild)
        as [a [Ha Hrest]].
      exists a; split; [|exact Hrest].
      apply in_flat_map; exists c; split; [exact Hcin|].
      unfold loop_block; rewrite Hcyclic, Hchoose; right; exact Ha.
Qed.

(** * Exact observations of the materialized maps *)

Lemma loop_bindings_get {A K B} (EK : encoding K) (key : A -> K) (value : A -> option B)
    entries k b : NoDup (map key entries) ->
  (Map.get EK k (loop_bindings EK key value entries) = Some b <->
    exists a, In a entries /\ key a = k /\ value a = Some b).
Proof.
  intro Hnodup; induction entries as [|a rest IH]; cbn [loop_bindings] in *.
  - rewrite Map.get_empty; split; [discriminate|intros [a [Hin _]]; contradiction].
  - inversion Hnodup as [|head tail Hfresh Htail]; subst; specialize (IH Htail).
    destruct (dfs_eq_dec EK k (key a)) as [Heq|Hne].
    + subst k; destruct (value a) as [v|] eqn:Hvalue.
      * rewrite Map.get_set_same; split.
        -- intro Hget; inversion Hget; subst v; exists a.
           split; [left; reflexivity|split; [reflexivity|exact Hvalue]].
        -- intros [a' [[Heq|Hin] [Hkey Hval]]].
           ++ subst a'; rewrite Hvalue in Hval; exact Hval.
           ++ exfalso; apply Hfresh; rewrite <- Hkey; apply in_map; exact Hin.
      * rewrite IH; split.
        -- intros [a' [Hin [Hkey _]]]; exfalso; apply Hfresh.
           rewrite <- Hkey; apply in_map; exact Hin.
        -- intros [a' [[Heq|Hin] [Hkey Hval]]].
           ++ subst a'; rewrite Hvalue in Hval; discriminate.
           ++ exfalso; apply Hfresh; rewrite <- Hkey; apply in_map; exact Hin.
    + destruct (value a) as [v|] eqn:Hvalue;
        [rewrite Map.get_set_other by exact Hne|]; rewrite IH; split.
      * intros [a' [Hin Hrest]]; exists a'; split; [right; exact Hin|exact Hrest].
      * intros [a' [[Heq|Hin] [Hkey Hval]]];
          [subst a'; exfalso; apply Hne; symmetry; exact Hkey|exists a'; auto].
      * intros [a' [Hin Hrest]]; exists a'; split; [right; exact Hin|exact Hrest].
      * intros [a' [[Heq|Hin] [Hkey Hval]]];
          [subst a'; exfalso; apply Hne; symmetry; exact Hkey|exists a'; auto].
Qed.

Lemma loop_owners_get {V} (EV : encoding V) a rest y :
  Map.get EV y (loop_owners EV (a :: rest)) =
  match Map.get EV y (loop_owners EV rest) with
  | Some h => Some h
  | None =>
    if FinSet.mem EV y (FinSet.of_list EV (loop_members a)) then Some (loop_head a) else None
  end.
Proof.
  cbn [loop_owners]; rewrite Map.get_code, Map.code_get_union_with.
  change (Trie.union_opt (fun _ deeper => deeper)
    (Map.get EV y (Map.map (fun _ => loop_head a) (FinSet.of_list EV (loop_members a))))
    (Map.get EV y (loop_owners EV rest)) =
    match Map.get EV y (loop_owners EV rest) with
    | Some h => Some h
    | None => if FinSet.mem EV y (FinSet.of_list EV (loop_members a))
        then Some (loop_head a) else None
    end).
  rewrite Map.get_map; unfold FinSet.mem, Map.mem.
  destruct (Map.get EV y (loop_owners EV rest)),
    (Map.get EV y (FinSet.of_list EV (loop_members a))); reflexivity.
Qed.

Lemma loop_owners_spec {V} (EV : encoding V) entries :
  (forall a, In a entries -> In (loop_head a) (loop_members a)) ->
  (forall a b, before entries a b -> forall y,
    In y (loop_members a) -> In y (loop_members b) -> incl (loop_members b) (loop_members a)) ->
  forall y,
  (forall h, Map.get EV y (loop_owners EV entries) = Some h ->
    (exists a, In a entries /\ loop_head a = h /\ In y (loop_members a)) /\
    forall a, In a entries -> In y (loop_members a) -> In h (loop_members a)) /\
  (Map.get EV y (loop_owners EV entries) = None ->
    forall a, In a entries -> ~ In y (loop_members a)).
Proof.
  induction entries as [|a rest IH]; intros Hself Horder y.
  - cbn [loop_owners]; rewrite Map.get_empty; split;
      [intros h Hget; discriminate|intros _ a Hin; contradiction].
  - destruct (IH ltac:(intros b Hb; apply Hself; right; exact Hb)
      ltac:(intros b c Hbefore; apply Horder; apply dfs_before_cons; right; exact Hbefore) y)
      as [Hsome Hnone].
    rewrite loop_owners_get; destruct (Map.get EV y (loop_owners EV rest)) as [h|] eqn:Hget.
    + split; [|discriminate].
      intros h' Heq; inversion Heq; subst h'.
      destruct (Hsome h eq_refl) as [[b [Hb [Hhead Hy]]] Hinner].
      split; [exists b; split; [right; exact Hb|auto]|].
      intros c [Hca|Hc] Hcy; [subst c|apply Hinner; assumption].
      rewrite <- Hhead.
      apply (Horder a b ltac:(apply dfs_before_cons; left; auto) y Hcy Hy (loop_head b)).
      apply Hself; right; exact Hb.
    + destruct (FinSet.mem EV y (FinSet.of_list EV (loop_members a))) eqn:Hmem.
      * apply FinSet.of_list_spec in Hmem; split; [|discriminate].
        intros h Heq; inversion Heq; subst h; split.
        -- exists a; split; [left; reflexivity|auto].
        -- intros b [Hba|Hb] Hby; [subst b; apply Hself; left; reflexivity|].
           exfalso; exact (Hnone eq_refl b Hb Hby).
      * split; [intros h Hbad; discriminate|].
        intros _ b [Heq|Hb] Hby.
        -- subst b; apply (proj2 (FinSet.of_list_spec EV y (loop_members a))) in Hby; congruence.
        -- exact (Hnone eq_refl b Hb Hby).
Qed.

Lemma loop_key_unique {A K} (key : A -> K) entries :
  NoDup (map key entries) -> forall a b,
  In a entries -> In b entries -> key a = key b -> a = b.
Proof.
  induction entries as [|first rest IH]; intros Hnodup a b Ha Hb Hkey; [contradiction|].
  inversion Hnodup as [|head tail Hfresh Htail]; subst.
  destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
  - congruence.
  - subst a; exfalso; apply Hfresh; rewrite Hkey; apply in_map; exact Hb.
  - subst b; exfalso; apply Hfresh; rewrite <- Hkey; apply in_map; exact Ha.
  - apply IH; assumption.
Qed.

Lemma loop_bindings_at {A K B} (EK : encoding K) (key : A -> K) (value : A -> option B)
    entries a : NoDup (map key entries) -> In a entries ->
  Map.get EK (key a) (loop_bindings EK key value entries) = value a.
Proof.
  intros Hnodup Ha; destruct (value a) as [b|] eqn:Hvalue.
  - apply (proj2 (loop_bindings_get EK key value entries (key a) b Hnodup)).
    exists a; auto.
  - destruct (Map.get EK (key a) (loop_bindings EK key value entries)) as [b|] eqn:Hget;
      [|reflexivity].
    apply (proj1 (loop_bindings_get EK key value entries (key a) b Hnodup)) in Hget.
    destruct Hget as [a' [Ha' [Hkey Hval]]].
    assert (Heq : a' = a) by (apply (loop_key_unique key entries Hnodup); assumption).
    subst a'; congruence.
Qed.

Lemma loop_pack_node_at {V} (EV : encoding V) entries a :
  NoDup (map loop_head entries) -> In a entries ->
  Map.get EV (loop_head a) (loop_nodes (loop_pack EV entries)) =
    Some (FinSet.of_list EV (loop_members a)).
Proof.
  intros Hnodup Ha; exact (loop_bindings_at EV loop_head
    (fun a => Some (FinSet.of_list EV (loop_members a))) entries a Hnodup Ha).
Qed.

Lemma loop_pack_parent_at {V} (EV : encoding V) entries a :
  NoDup (map loop_head entries) -> In a entries ->
  Map.get EV (loop_head a) (loop_parent (loop_pack EV entries)) = loop_enclosing a.
Proof.
  intros Hnodup Ha; exact (loop_bindings_at EV loop_head loop_enclosing entries a Hnodup Ha).
Qed.

Lemma loop_pack_member_at {V} (EV : encoding V) entries a y :
  NoDup (map loop_head entries) -> In a entries ->
  (in_loop EV (loop_pack EV entries) (loop_head a) y <-> In y (loop_members a)).
Proof.
  intros Hnodup Ha; unfold in_loop; rewrite (loop_pack_node_at EV entries a Hnodup Ha).
  split.
  - intros [s [Heq Hmem]]; inversion Heq; subst s.
    exact (proj1 (FinSet.of_list_spec EV y (loop_members a)) Hmem).
  - intro Hy; exists (FinSet.of_list EV (loop_members a)); split; [reflexivity|].
    apply FinSet.of_list_spec; exact Hy.
Qed.

Lemma loop_pack_member {V} (EV : encoding V) entries h y :
  NoDup (map loop_head entries) ->
  (in_loop EV (loop_pack EV entries) h y <->
    exists a, In a entries /\ loop_head a = h /\ In y (loop_members a)).
Proof.
  intro Hnodup; split.
  - intros [s [Hget Hmem]]; cbn [loop_pack loop_nodes] in Hget.
    apply (proj1 (loop_bindings_get EV loop_head _ entries h s Hnodup)) in Hget.
    destruct Hget as [a [Ha [Hhead Heq]]]; inversion Heq; subst s.
    exists a; split; [exact Ha|split; [exact Hhead|]].
    exact (proj1 (FinSet.of_list_spec EV y (loop_members a)) Hmem).
  - intros [a [Ha [Hhead Hy]]]; subst h; apply loop_pack_member_at; assumption.
Qed.

Lemma loop_outer_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) a : ready EV g p -> In a (loop_entries p) -> forall y,
  FinSet.mem EV y (outer_nodes p (loop_forest_of p) (loop_head a)) = true <->
    In y (loop_region a).
Proof.
  intros Hready Ha y; pose proof (loop_entries_valid EV g p Hready) as Hvalid.
  pose proof (loop_valid_heads _ _ _ _ _ _ Hvalid) as Hnodup.
  unfold loop_forest_of, outer_nodes.
  rewrite (loop_pack_parent_at EV _ a Hnodup Ha).
  destruct (loop_valid_parents _ _ _ _ _ _ Hvalid a Ha)
    as [[Hparent Hregion]|[b [Hbefore [Hparent Hregion]]]].
  - rewrite Hparent; cbn; rewrite Hregion.
    pose proof Hready as [Hwf _].
    destruct (dfs_exact EV g p y (Graph.entries g) FinSet.empty Hready (entries_in Hwf))
      as [_ [_ [_ Hpre]]].
    symmetry; exact Hpre.
  - rewrite Hparent.
    destruct (loop_before_members _ _ _ Hbefore) as [Hb _].
    rewrite (loop_pack_node_at EV _ b Hnodup Hb), FinSet.mem_remove, FinSet.of_list_spec.
    rewrite Hregion; tauto.
Qed.

Lemma loop_path_agrees {V E} (EV : encoding V) (g : Graph.t V E) keep1 keep2 :
  (forall y, FinSet.mem EV y keep1 = true <-> FinSet.mem EV y keep2 = true) ->
  forall u es v, path (induced EV keep1 g) u es v <-> path (induced EV keep2 g) u es v.
Proof.
  intros Hagrees u es v; rewrite !loop_path_induced; split; intros [Hpath Htargets];
    split; [exact Hpath| |exact Hpath|]; intros e He; apply Hagrees; apply Htargets; exact He.
Qed.

Lemma loop_strong_agrees {V E} (g1 g2 : Graph.t V E) (S T : V -> Prop) :
  (forall u es v, path g1 u es v <-> path g2 u es v) ->
  (forall v, S v <-> T v) -> strong_component g1 S -> strong_component g2 T.
Proof.
  intros Hpaths Hsets [[v Hv] [Hmutual Hmaximal]]; split.
  - exists v; apply Hsets; exact Hv.
  - split.
    + intros u w Hu Hw; apply Hsets in Hu, Hw.
      destruct (Hmutual u w Hu Hw) as [[first Hfirst] [last Hlast]].
      split; [exists first|exists last]; apply Hpaths; assumption.
    + intros u w Hu [[first Hfirst] [last Hlast]]; apply Hsets.
      apply (Hmaximal u w); [apply Hsets; exact Hu|].
      split; [exists first|exists last]; apply Hpaths; assumption.
Qed.

Lemma loop_before_map {A B} (f : A -> B) entries a b :
  before entries a b -> before (map f entries) (f a) (f b).
Proof.
  intros [first [middle [last Heq]]]; exists (map f first), (map f middle), (map f last).
  rewrite Heq, map_app; cbn [map]; rewrite map_app; reflexivity.
Qed.

Lemma loop_pack_parent_nested {V E} (EV : encoding V) (g : Graph.t V E)
    order region entries : loop_valid EV g order region None entries ->
  forall h h', Map.get EV h (loop_parent (loop_pack EV entries)) = Some h' ->
  before (loop_headers (loop_pack EV entries)) h' h /\
  (forall y, in_loop EV (loop_pack EV entries) h y -> in_loop EV (loop_pack EV entries) h' y) /\
  ~ in_loop EV (loop_pack EV entries) h h'.
Proof.
  intros Hvalid h h' Hget; pose proof (loop_valid_heads _ _ _ _ _ _ Hvalid) as Hnodup.
  cbn [loop_pack loop_parent] in Hget.
  apply (proj1 (loop_bindings_get EV loop_head _ entries h h' Hnodup)) in Hget.
  destruct Hget as [a [Ha [Hhead Hparent]]]; subst h.
  destruct (loop_valid_parents _ _ _ _ _ _ Hvalid a Ha)
    as [[Hroot _]|[b [Hbefore [Hparent' Hregion']]]]; [congruence|].
  rewrite Hparent in Hparent'; inversion Hparent'; subst h'.
  destruct (loop_before_members _ _ _ Hbefore) as [Hb _].
  pose proof (proj1 (proj2 (loop_valid_exact _ _ _ _ _ _ Hvalid a Ha))) as Hsub.
  split; [apply loop_before_map; exact Hbefore|]; split.
  - intros y Hy; apply (proj1 (loop_pack_member_at EV entries a y Hnodup Ha)) in Hy.
    apply loop_pack_member_at; [exact Hnodup|exact Hb|].
    exact (proj1 (proj1 (Hregion' y) (Hsub y Hy))).
  - intro Hbad; apply (proj1 (loop_pack_member_at EV entries a _ Hnodup Ha)) in Hbad.
    pose proof (proj1 (Hregion' _) (Hsub _ Hbad)) as [_ Hne]; apply Hne; reflexivity.
Qed.

Lemma loop_pack_owners {V E} (EV : encoding V) (g : Graph.t V E) order region entries :
  loop_valid EV g order region None entries ->
  (forall y h, Map.get EV y (loop_of (loop_pack EV entries)) = Some h ->
    in_loop EV (loop_pack EV entries) h y /\
    forall h', in_loop EV (loop_pack EV entries) h' y -> in_loop EV (loop_pack EV entries) h' h) /\
  (forall y, Map.get EV y (loop_of (loop_pack EV entries)) = None ->
    forall h, ~ in_loop EV (loop_pack EV entries) h y).
Proof.
  intro Hvalid; pose proof (loop_valid_heads _ _ _ _ _ _ Hvalid) as Hnodup.
  assert (Howners := loop_owners_spec EV entries
    ltac:(intros a Ha; exact (proj1 (loop_valid_exact _ _ _ _ _ _ Hvalid a Ha)))
    ltac:(intros a b Hbefore y Hay Hby;
      exact (proj1 (loop_valid_order _ _ _ _ _ _ Hvalid a b Hbefore y Hay Hby)))).
  split.
  - intros y h Hget; destruct (proj1 (Howners y) h Hget)
      as [[a [Ha [Hhead Hy]]] Hinner].
    split.
    + rewrite <- Hhead; apply loop_pack_member_at; assumption.
    + intros h' Hin; apply (proj1 (loop_pack_member EV entries h' y Hnodup)) in Hin.
      destruct Hin as [b [Hb [Hhead' Hyb]]]; rewrite <- Hhead'.
      apply loop_pack_member_at; [exact Hnodup|exact Hb|apply Hinner; assumption].
  - intros y Hget h Hin; apply (proj1 (loop_pack_member EV entries h y Hnodup)) in Hin.
    destruct Hin as [a [Ha [_ Hy]]]; exact (proj2 (Howners y) Hget a Ha Hy).
Qed.

Lemma loop_pack_nested {V E} (EV : encoding V) (g : Graph.t V E) order region entries :
  incl region (Graph.nodes g) -> loop_valid EV g order region None entries ->
  let f := loop_pack EV entries in
  (forall h, In h (loop_headers f) <-> exists s, Map.get EV h (loop_nodes f) = Some s) /\
  NoDup (loop_headers f) /\
  (forall h, In h (loop_headers f) -> In h (Graph.nodes g) /\ in_loop EV f h h) /\
  (forall h h', Map.get EV h (loop_parent f) = Some h' ->
    before (loop_headers f) h' h /\
    (forall y, in_loop EV f h y -> in_loop EV f h' y) /\ ~ in_loop EV f h h') /\
  (forall y h, Map.get EV y (loop_of f) = Some h ->
    in_loop EV f h y /\ forall h', in_loop EV f h' y -> in_loop EV f h' h) /\
  (forall y, Map.get EV y (loop_of f) = None -> forall h, ~ in_loop EV f h y).
Proof.
  intros Hregion Hvalid; cbn zeta.
  pose proof (loop_valid_heads _ _ _ _ _ _ Hvalid) as Hnodup.
  split.
  - intro h; split.
    + intros Hin; apply in_map_iff in Hin; destruct Hin as [a [Hhead Ha]].
      subst h; exists (FinSet.of_list EV (loop_members a)); apply loop_pack_node_at; assumption.
    + intros [s Hget]; cbn [loop_pack loop_nodes] in Hget.
      apply (proj1 (loop_bindings_get EV loop_head _ entries h s Hnodup)) in Hget.
      destruct Hget as [a [Ha [Hhead _]]]; rewrite <- Hhead; apply in_map; exact Ha.
  - split; [exact Hnodup|]; split.
    + intros h Hin; apply in_map_iff in Hin; destruct Hin as [a [Hhead Ha]]; subst h.
      pose proof (proj1 (loop_valid_exact _ _ _ _ _ _ Hvalid a Ha)) as Hself.
      split.
      * apply Hregion; exact (loop_valid_domain _ _ _ _ _ _ Hvalid a Ha _ Hself).
      * apply loop_pack_member_at; assumption.
    + split.
      * apply (loop_pack_parent_nested EV g order region entries Hvalid).
      * apply (loop_pack_owners EV g order region entries Hvalid).
Qed.

(** * Public loop forest guarantees *)

Section Gra4b.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Local Abbreviation F := (loop_forest_of p).

(** Every header occurs once, parents nest strictly, and owner queries select innermost loops. *)
Theorem loop_forest_nested : ready EV g p ->
  (forall h, In h (loop_headers F) <-> exists s, Map.get EV h (loop_nodes F) = Some s) /\
  NoDup (loop_headers F) /\
  (forall h, In h (loop_headers F) -> In h (Graph.nodes g) /\ in_loop EV F h h) /\
  (forall h h', Map.get EV h (loop_parent F) = Some h' ->
     before (loop_headers F) h' h /\
     (forall y, in_loop EV F h y -> in_loop EV F h' y) /\ ~ in_loop EV F h h') /\
  (forall y h, Map.get EV y (loop_of F) = Some h ->
     in_loop EV F h y /\ forall h', in_loop EV F h' y -> in_loop EV F h' h) /\
  (forall y, Map.get EV y (loop_of F) = None -> forall h, ~ in_loop EV F h y).
Proof.
  intro Hready; apply (loop_pack_nested EV g
    (rpo (dfs p FinSet.empty (Graph.entries g)))
    (preorder (dfs p FinSet.empty (Graph.entries g))) (loop_entries p)).
  - apply loop_search_domain; exact Hready.
  - apply loop_entries_valid; exact Hready.
Qed.

(** Every loop is precisely a cyclic SCC of its ambient region with its first RPO node as header. *)
Theorem loop_forest_exact : ready EV g p -> forall h, In h (loop_headers F) ->
  strong_component (induced EV (outer_nodes p F h) g) (in_loop EV F h) /\
  (exists es, es <> [] /\ path (induced EV (outer_nodes p F h) g) h es h) /\
  (forall y, in_loop EV F h y ->
    y = h \/ before (rpo (dfs p FinSet.empty (Graph.entries g))) h y).
Proof.
  intros Hready h Hin; apply in_map_iff in Hin; destruct Hin as [a [Hhead Ha]]; subst h.
  pose proof (loop_entries_valid EV g p Hready) as Hvalid.
  pose proof (loop_valid_heads _ _ _ _ _ _ Hvalid) as Hnodup.
  destruct (loop_valid_exact _ _ _ _ _ _ Hvalid a Ha)
    as [Hself [Hsub [Hstrong [Hcycle Hfirst]]]].
  assert (Hpaths : forall u es v,
    path (induced EV (FinSet.of_list EV (loop_region a)) g) u es v <->
    path (induced EV (outer_nodes p F (loop_head a)) g) u es v).
  { apply loop_path_agrees; intro y.
    rewrite (loop_outer_agrees EV g p a Hready Ha y), FinSet.of_list_spec; reflexivity. }
  split.
  - apply (loop_strong_agrees _ _ (fun v => In v (loop_members a))
      (in_loop EV F (loop_head a)) Hpaths); [|exact Hstrong].
    intro y; symmetry; apply loop_pack_member_at; assumption.
  - split.
    + destruct Hcycle as [es [Hnonempty Hpath]]; exists es; split; [exact Hnonempty|].
      apply Hpaths; exact Hpath.
    + intros y Hy; apply Hfirst; apply (proj1 (loop_pack_member_at EV _ a y Hnodup Ha)); exact Hy.
Qed.

End Gra4b.

Lemma loop_path_reachable {V E} (g : Graph.t V E) v es w :
  path g v es w -> reachable g v ->
  forall y, y = v \/ In y (map (Graph.target g) es) -> reachable g y.
Proof.
  intro Hpath; induction Hpath as [v|e es w Hedge Hpath IH]; intros Hreach y Hy.
  - destruct Hy as [Heq|Hin]; [subst y; exact Hreach|contradiction].
  - destruct Hy as [Heq|[Heq|Hin]].
    + subst y; exact Hreach.
    + subst y; eapply reachable_step; eauto.
    + apply IH; [eapply reachable_step; eauto|right; exact Hin].
Qed.

Section LoopCoverage.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Local Abbreviation F := (loop_forest_of p).

(** Every reachable cycle is covered by a loop headed by a vertex on that same cycle. *)
Theorem loop_forest_covers : ready EV g p -> forall v es,
  reachable g v -> es <> [] -> path g v es v ->
  exists h, In h (loop_headers F) /\
    (h = v \/ In h (map (Graph.target g) es)) /\
    forall y, (y = v \/ In y (map (Graph.target g) es)) -> in_loop EV F h y.
Proof.
  intros Hready v es Hreach Hnonempty Hpath; pose proof Hready as [Hwf _].
  assert (Hpre : forall y, reachable g y ->
    In y (preorder (dfs p FinSet.empty (Graph.entries g)))).
  { intros y Hy; destruct (dfs_exact EV g p y (Graph.entries g) FinSet.empty
      Hready (entries_in Hwf)) as [_ [_ [_ Hpre]]].
    apply Hpre; apply (reachable_dfs EV g p y Hready); exact Hy. }
  assert (Hregionpath : path
    (induced EV (FinSet.of_list EV (preorder (dfs p FinSet.empty (Graph.entries g)))) g)
    v es v).
  { apply loop_path_induced; split; [exact Hpath|].
    intros e He; apply FinSet.of_list_spec; apply Hpre.
    apply (loop_path_reachable g v es v Hpath Hreach (Graph.target g e)).
    right; apply in_map; exact He. }
  destruct (loop_iter_covers EV g p Hready
    (N.of_nat (length (preorder (dfs p FinSet.empty (Graph.entries g)))))
    (preorder (dfs p FinSet.empty (Graph.entries g))) None v es
    (loop_search_domain EV g p Hready) ltac:(rewrite Nat2N.id; lia)
    (Hpre v Hreach) Hnonempty Hregionpath) as [a [Ha [Hon Hpoints]]].
  change (In a (loop_entries p)) in Ha.
  exists (loop_head a); split; [apply in_map; exact Ha|split; [exact Hon|]].
  intros y Hy; apply loop_pack_member_at;
    [exact (loop_valid_heads _ _ _ _ _ _ (loop_entries_valid EV g p Hready))|exact Ha|].
  apply Hpoints; exact Hy.
Qed.

End LoopCoverage.
