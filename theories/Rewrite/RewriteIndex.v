(** * Maintained e-graph incidence indexes

    Deduplicated buckets index operators, raw children and all aliases of canonical children.
    For example, merging child classes combines their parent buckets without scanning nodes.
    Builds on: CollectionsMap and RewriteEgraph. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteEgraph.
Import List.ListNotations.

(** The root-parent table aggregates every raw alias of each canonical child class. *)
Record rw_index (K : Type) : Type := RwIndex {
  rw_index_ops : Map.t K (list rw_id);
  rw_index_parents : Map.t rw_id (list rw_id);
  rw_index_root_parents : Map.t rw_id (list rw_id)
}.

Arguments RwIndex {K}.
Arguments rw_index_ops {K}.
Arguments rw_index_parents {K}.
Arguments rw_index_root_parents {K}.

(** Absent buckets contain no identifiers. *)
Definition rw_lookup_list {K} (E : encoding K) (k : K) (m : Map.t K (list rw_id)) :
    list rw_id :=
  match Map.get E k m with
  | Some ids => ids
  | None => []
  end.

(** Index agreement gives exact, duplicate-free incidence in all three tables. *)
Definition rw_index_agrees {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) : Prop :=
  Map.wf EK (rw_index_ops ix) /\ Map.wf positive_encoding (rw_index_parents ix) /\
  Map.wf positive_encoding (rw_index_root_parents ix) /\
  (forall op, NoDup (rw_lookup_list EK op (rw_index_ops ix))) /\
  (forall child, NoDup (rw_lookup_list positive_encoding child (rw_index_parents ix))) /\
  (forall root, NoDup (rw_lookup_list positive_encoding root (rw_index_root_parents ix))) /\
  (forall op n, In n (rw_lookup_list EK op (rw_index_ops ix)) <->
    exists c s ids, rw_node_at g n = Some (c, RWNApp s op ids)) /\
  (forall child n, In n (rw_lookup_list positive_encoding child (rw_index_parents ix)) <->
    exists c s op ids, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids) /\
  (forall root n, In n (rw_lookup_list positive_encoding root (rw_index_root_parents ix)) <->
    exists c s op ids child, rw_node_at g n = Some (c, RWNApp s op ids) /\ In child ids /\
      rw_find g child = Some root).

(** * Generic finite incidence tables *)

Definition rw_bucket_insert {A} (E : encoding A) k n (table : Map.t A (list rw_id)) :=
  Map.set E k (nodup Pos.eq_dec (n :: rw_lookup_list E k table)) table.

Definition rw_bucket_remove {A} (E : encoding A) k n (table : Map.t A (list rw_id)) :=
  Map.set E k (remove Pos.eq_dec n (rw_lookup_list E k table)) table.

Lemma rw_lookup_set {A} (E : encoding A) k j ids table :
  rw_lookup_list E k (Map.set E j ids table) =
    if Pos.eq_dec (encode E k) (encode E j) then ids else rw_lookup_list E k table.
Proof.
  unfold rw_lookup_list; destruct (Pos.eq_dec (encode E k) (encode E j)) as [Heq|Hne].
  - apply (encode_injective E) in Heq; subst j; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other; [reflexivity|congruence].
Qed.

Lemma rw_bucket_insert_in {A} (E : encoding A) k j n m table :
  In m (rw_lookup_list E k (rw_bucket_insert E j n table)) <->
    (k = j /\ m = n) \/ In m (rw_lookup_list E k table).
Proof.
  unfold rw_bucket_insert; rewrite rw_lookup_set.
  destruct (Pos.eq_dec (encode E k) (encode E j)) as [Heq|Hne].
  - apply (encode_injective E) in Heq; subst j; rewrite nodup_In; cbn; intuition congruence.
  - intuition congruence.
Qed.

Lemma rw_bucket_remove_in {A} (E : encoding A) k j n m table :
  In m (rw_lookup_list E k (rw_bucket_remove E j n table)) <->
    In m (rw_lookup_list E k table) /\ ~ (k = j /\ m = n).
Proof.
  unfold rw_bucket_remove; rewrite rw_lookup_set.
  destruct (Pos.eq_dec (encode E k) (encode E j)) as [Heq|Hne].
  - apply (encode_injective E) in Heq; subst j; split.
    + intro Hin; apply in_remove in Hin; intuition congruence.
    + intros [Hin Hne]; apply in_in_remove; [intro Heq; apply Hne; auto|exact Hin].
  - intuition congruence.
Qed.

Definition rw_table_add {A} (E : encoding A) keys n table : Map.t A (list rw_id) :=
  fold_right (fun key table => rw_bucket_insert E key n table) table keys.

Definition rw_table_remove {A} (E : encoding A) keys n table : Map.t A (list rw_id) :=
  fold_right (fun key table => rw_bucket_remove E key n table) table keys.

Lemma rw_table_add_in {A} (E : encoding A) keys n table k m :
  In m (rw_lookup_list E k (rw_table_add E keys n table)) <->
    (m = n /\ In k keys) \/ In m (rw_lookup_list E k table).
Proof.
  induction keys as [|key keys IHkeys]; cbn [rw_table_add fold_right].
  - cbn; tauto.
  - rewrite rw_bucket_insert_in, IHkeys; cbn; intuition congruence.
Qed.

Lemma rw_table_remove_in {A} (E : encoding A) keys n table k m :
  In m (rw_lookup_list E k (rw_table_remove E keys n table)) <->
    In m (rw_lookup_list E k table) /\ ~ (m = n /\ In k keys).
Proof.
  induction keys as [|key keys IHkeys]; cbn [rw_table_remove fold_right].
  - cbn; tauto.
  - rewrite rw_bucket_remove_in, IHkeys; cbn.
    assert (Hsym : key = k <-> k = key) by (split; congruence).
    rewrite Hsym; tauto.
Qed.

(** A table is prepared when its map is valid and all buckets are sets of node identifiers. *)
Definition rw_table_wf {A} (E : encoding A) table : Prop :=
  Map.wf E table /\ forall k, NoDup (rw_lookup_list E k table).

Lemma rw_table_add_wf {A} (E : encoding A) keys n table :
  rw_table_wf E table -> rw_table_wf E (rw_table_add E keys n table).
Proof.
  intro Hwf; induction keys as [|key keys [Hmap Hlists]]; [exact Hwf|]; split.
  - apply Map.wf_set; exact Hmap.
  - intro k; unfold rw_table_add; cbn [fold_right]; unfold rw_bucket_insert.
    rewrite rw_lookup_set; destruct (Pos.eq_dec (encode E k) (encode E key));
      [apply NoDup_nodup|apply Hlists].
Qed.

Lemma rw_remove_nodup n ids : NoDup ids -> NoDup (remove Pos.eq_dec n ids).
Proof.
  intro Hnodup; induction Hnodup as [|id ids Houtside Hrest IHrest]; cbn.
  - constructor.
  - destruct (Pos.eq_dec n id); [exact IHrest|]; constructor; [|exact IHrest].
    intro Hin; apply in_remove in Hin; tauto.
Qed.

Lemma rw_table_remove_wf {A} (E : encoding A) keys n table :
  rw_table_wf E table -> rw_table_wf E (rw_table_remove E keys n table).
Proof.
  intro Hwf; induction keys as [|key keys [Hmap Hlists]]; [exact Hwf|]; split.
  - apply Map.wf_set; exact Hmap.
  - intro k; unfold rw_table_remove; cbn [fold_right]; unfold rw_bucket_remove.
    rewrite rw_lookup_set; destruct (Pos.eq_dec (encode E k) (encode E key));
      [|apply Hlists].
    apply rw_remove_nodup; apply Hlists.
Qed.

Definition rw_operator_keys {K Sort V} (node : rw_node K Sort V) : list K :=
  match node with
  | RWNVar _ _ => []
  | RWNApp _ op _ => [op]
  end.

Definition rw_child_keys {K Sort V} (node : rw_node K Sort V) : list rw_id :=
  match node with
  | RWNVar _ _ => []
  | RWNApp _ _ ids => ids
  end.

Definition rw_root_keys {K Sort V} (g : rw_graph K Sort V) (node : rw_node K Sort V) :
    list rw_id :=
  flat_map (fun child => match rw_find g child with
    | Some root => [root]
    | None => []
    end) (rw_child_keys node).

Lemma rw_root_keys_in {K Sort V} (g : rw_graph K Sort V) node root :
  In root (rw_root_keys g node) <->
    exists child, In child (rw_child_keys node) /\ rw_find g child = Some root.
Proof.
  unfold rw_root_keys; rewrite in_flat_map; split.
  - intros [child [Hin Hroot]]; destruct (rw_find g child) as [r|] eqn:Hfind;
      cbn in Hroot; [|contradiction].
    destruct Hroot as [Heq|Hfalse]; [subst r; eauto|contradiction].
  - intros [child [Hin Hfind]]; exists child; rewrite Hfind; cbn; auto.
Qed.

Definition rw_table_incidence {A K Sort V} (E : encoding A) (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> list A) table : Prop :=
  rw_table_wf E table /\ forall key n, In n (rw_lookup_list E key table) <->
    exists owner node, rw_node_at g n = Some (owner, node) /\ In key (keys node).

Fixpoint rw_build_table_on {A K Sort V} (E : encoding A) (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> list A) ids : Map.t A (list rw_id) :=
  match ids with
  | [] => Map.empty
  | n :: ids =>
    let table := rw_build_table_on E g keys ids in
    match rw_node_at g n with
    | Some (_, node) => rw_table_add E (keys node) n table
    | None => table
    end
  end.

Lemma rw_build_table_on_correct {A K Sort V} (E : encoding A) (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> list A) ids :
  rw_table_wf E (rw_build_table_on E g keys ids) /\
  forall key n, In n (rw_lookup_list E key (rw_build_table_on E g keys ids)) <->
    In n ids /\ exists owner node, rw_node_at g n = Some (owner, node) /\ In key (keys node).
Proof.
  induction ids as [|id ids [Hwf IHids]]; cbn [rw_build_table_on].
  - split.
    + split; [apply Map.wf_empty|]; intro k; unfold rw_lookup_list; rewrite Map.get_empty;
        constructor.
    + intros k n; unfold rw_lookup_list; rewrite Map.get_empty; cbn; tauto.
  - destruct (rw_node_at g id) as [[owner node]|] eqn:Hnode; split.
    + apply rw_table_add_wf; exact Hwf.
    + intros k n; rewrite rw_table_add_in, IHids; cbn; split.
      * intros [[-> Hin]|[Hin Hexists]]; [split; [auto|eauto]|auto].
      * intros [[Heq|Hin] [c [other [Hother Hkey]]]].
        -- subst n; assert (other = node) by congruence; subst other; auto.
        -- right; split; [exact Hin|eauto].
    + exact Hwf.
    + intros k n; rewrite IHids; cbn; split; [tauto|].
      intros [[Heq|Hin] [c [other [Hother Hkey]]]]; [subst n; congruence|].
      split; [exact Hin|eauto].
Qed.

Definition rw_build_table {A K Sort V} (E : encoding A) (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> list A) := rw_build_table_on E g keys (rw_nodes_in g).

Lemma rw_build_table_correct {A K Sort V} (E : encoding A) (sig : rw_signature K Sort V)
    g (keys : rw_node K Sort V -> list A) :
  rw_graph_wf sig g -> rw_table_incidence E g keys (rw_build_table E g keys).
Proof.
  intro Hwf; destruct (rw_build_table_on_correct E g keys (rw_nodes_in g)) as [Htable Hinc].
  split; [exact Htable|]; intros key n; rewrite Hinc; split; [tauto|].
  intros [owner [node [Hnode Hin]]]; split; [|eauto].
  apply (proj2 (rw_layout_enumerates sig g (rw_wf_layout sig g Hwf) n)); eauto.
Qed.

Lemma rw_index_incidence {K Sort V} (EK : encoding K) (g : rw_graph K Sort V) ix :
  rw_index_agrees EK g ix <->
    rw_table_incidence EK g rw_operator_keys (rw_index_ops ix) /\
    rw_table_incidence positive_encoding g rw_child_keys (rw_index_parents ix) /\
    rw_table_incidence positive_encoding g (rw_root_keys g) (rw_index_root_parents ix).
Proof.
  unfold rw_index_agrees, rw_table_incidence, rw_table_wf; split.
  - intros [Hop [Hp [Hr [Hopl [Hpl [Hrl [Hops [Hps Hrs]]]]]]]].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    + intros op n; rewrite Hops; split.
      * intros [c [s [ids Hnode]]]; exists c, (RWNApp s op ids); cbn; auto.
      * intros [c [[s v|s op' ids] [Hnode Hin]]]; cbn in Hin; [contradiction|].
        destruct Hin as [Heq|Hfalse]; [subst op'; exists c, s, ids; exact Hnode|contradiction].
    + intros child n; rewrite Hps; split.
      * intros [c [s [op [ids [Hnode Hin]]]]]; exists c, (RWNApp s op ids); auto.
      * intros [c [[s v|s op ids] [Hnode Hin]]]; cbn in Hin; [contradiction|eauto 8].
    + intros root n; rewrite Hrs; split.
      * intros [c [s [op [ids [child [Hnode [Hin Hfind]]]]]]].
        exists c, (RWNApp s op ids); split; [exact Hnode|].
        apply rw_root_keys_in; exists child; auto.
      * intros [c [[s v|s op ids] [Hnode Hin]]]; apply rw_root_keys_in in Hin;
          destruct Hin as [child [Hin Hfind]]; cbn in Hin; [contradiction|eauto 9].
  - intros [[[Hop Hopl] Hops] [[[Hp Hpl] Hps] [[Hr Hrl] Hrs]]].
    do 6 (split; [assumption|]); split.
    + intros op n; rewrite Hops; split.
      * intros [c [[s v|s op' ids] [Hnode Hin]]]; cbn in Hin; [contradiction|].
        destruct Hin as [Heq|Hfalse]; [subst op'; exists c, s, ids; exact Hnode|contradiction].
      * intros [c [s [ids Hnode]]]; exists c, (RWNApp s op ids); cbn; auto.
    + split.
      * intros child n; rewrite Hps; split.
        -- intros [c [[s v|s op ids] [Hnode Hin]]]; cbn in Hin; [contradiction|eauto 8].
        -- intros [c [s [op [ids [Hnode Hin]]]]]; exists c, (RWNApp s op ids); auto.
      * intros root n; rewrite Hrs; split.
        -- intros [c [[s v|s op ids] [Hnode Hin]]]; apply rw_root_keys_in in Hin;
             destruct Hin as [child [Hin Hfind]]; cbn in Hin; [contradiction|eauto 9].
        -- intros [c [s [op [ids [child [Hnode [Hin Hfind]]]]]]].
           exists c, (RWNApp s op ids); split; [exact Hnode|].
           apply rw_root_keys_in; exists child; auto.
Qed.

(** Index construction traverses the finite node enumeration once per component. *)
Definition rw_build_index {K Sort V} (EK : encoding K) (g : rw_graph K Sort V) : rw_index K :=
  RwIndex (rw_build_table EK g rw_operator_keys)
    (rw_build_table positive_encoding g rw_child_keys)
    (rw_build_table positive_encoding g (rw_root_keys g)).

(** Building incidence tables establishes all three exact agreement invariants. *)
Theorem rw_build_index_agrees {K Sort V} (EK : encoding K) (sig : rw_signature K Sort V)
    (g : rw_graph K Sort V) : rw_graph_wf sig g -> rw_index_agrees EK g (rw_build_index EK g).
Proof.
  intro Hwf; apply rw_index_incidence; split; [|split];
    apply (rw_build_table_correct _ sig); exact Hwf.
Qed.

(** Parent lookup uses the current canonical root, including parents with old raw aliases. *)
Definition rw_parent_nodes {K Sort V} (g : rw_graph K Sort V) (ix : rw_index K) (c : rw_id) :
    list rw_id :=
  match rw_find g c with
  | Some root => rw_lookup_list positive_encoding root (rw_index_root_parents ix)
  | None => []
  end.

(** Root buckets contain exactly nodes mentioning some alias of the requested class. *)
Theorem rw_parent_nodes_agree {K Sort V} (EK : encoding K) (g : rw_graph K Sort V)
    (ix : rw_index K) (c n : rw_id) :
  rw_index_agrees EK g ix ->
  (In n (rw_parent_nodes g ix c) <-> exists root owner s op ids child,
    rw_find g c = Some root /\ rw_find g child = Some root /\
    rw_node_at g n = Some (owner, RWNApp s op ids) /\ In child ids).
Proof.
  intros [_ [_ [_ [_ [_ [_ [_ [_ Hroots]]]]]]]]; unfold rw_parent_nodes.
  destruct (rw_find g c) as [root|] eqn:Hfind.
  - rewrite Hroots; split.
    + intros [owner [s [op [ids [child [Hnode [Hin Hchild]]]]]]].
      exists root, owner, s, op, ids, child; repeat split; assumption.
    + intros [r [owner [s [op [ids [child [Heq [Hchild [Hnode Hin]]]]]]]]].
      assert (r = root) by congruence; subst r.
      exists owner, s, op, ids, child; repeat split; assumption.
  - cbn; split; [contradiction|].
    intros [root [owner [s [op [ids [child [Hbad Hrest]]]]]]]; discriminate.
Qed.

(** * Incremental union *)

Lemma rw_collapse_fixed from into : rw_collapse from into into = into.
Proof.
  unfold rw_collapse; destruct (Pos.eq_dec into from); congruence.
Qed.

Definition rw_merge_table (table : Map.t rw_id (list rw_id)) ra rb :=
  Map.set positive_encoding ra
    (nodup Pos.eq_dec (rw_lookup_list positive_encoding ra table ++
      rw_lookup_list positive_encoding rb table)) (Map.remove positive_encoding rb table).

Lemma rw_merge_table_lookup table ra rb r :
  rw_lookup_list positive_encoding r (rw_merge_table table ra rb) =
    if Pos.eq_dec r ra then nodup Pos.eq_dec
      (rw_lookup_list positive_encoding ra table ++ rw_lookup_list positive_encoding rb table)
    else if Pos.eq_dec r rb then [] else rw_lookup_list positive_encoding r table.
Proof.
  unfold rw_merge_table; rewrite rw_lookup_set; cbn [encode positive_encoding].
  destruct (Pos.eq_dec r ra); [reflexivity|].
  unfold rw_lookup_list; destruct (Pos.eq_dec r rb) as [->|Hne].
  - rewrite Map.get_remove_same; reflexivity.
  - rewrite Map.get_remove_other by exact Hne; reflexivity.
Qed.

Lemma rw_merge_table_in table ra rb r n :
  In n (rw_lookup_list positive_encoding r (rw_merge_table table ra rb)) <->
    exists old, In n (rw_lookup_list positive_encoding old table) /\
      rw_collapse rb ra old = r.
Proof.
  rewrite rw_merge_table_lookup; destruct (Pos.eq_dec r ra) as [->|Hra].
  - rewrite nodup_In, in_app_iff; split.
    + intros [Hin|Hin]; [exists ra|exists rb]; split; auto;
        [apply rw_collapse_fixed|apply rw_collapse_same].
    + intros [old [Hin Heq]]; unfold rw_collapse in Heq.
      destruct (Pos.eq_dec old rb) as [->|Hne]; [auto|subst old; auto].
  - destruct (Pos.eq_dec r rb) as [->|Hrb]; cbn; split.
    + contradiction.
    + intros [old [Hin Heq]]; unfold rw_collapse in Heq.
      destruct (Pos.eq_dec old rb); congruence.
    + intro Hin; exists r; split; [exact Hin|apply rw_collapse_other; exact Hrb].
    + intros [old [Hin Heq]]; unfold rw_collapse in Heq.
      destruct (Pos.eq_dec old rb); [congruence|subst old; exact Hin].
Qed.

Lemma rw_merge_table_wf table ra rb :
  rw_table_wf positive_encoding table -> rw_table_wf positive_encoding (rw_merge_table table ra rb).
Proof.
  intros [Hwf Hlists]; split.
  - apply Map.wf_set; apply Map.wf_remove; exact Hwf.
  - intro r; rewrite rw_merge_table_lookup.
    destruct (Pos.eq_dec r ra); [apply NoDup_nodup|].
    destruct (Pos.eq_dec r rb); [constructor|apply Hlists].
Qed.

(** A union changes only the two old root buckets and the surviving root bucket. *)
Definition rw_index_after_union {K Sort V} (g g' : rw_graph K Sort V) (ix : rw_index K)
    (a b : rw_id) : rw_index K :=
  match rw_find g a, rw_find g b, rw_find g' a with
  | Some ra, Some rb, Some root =>
    RwIndex (rw_index_ops ix) (rw_index_parents ix)
      (Map.set positive_encoding root
        (nodup Pos.eq_dec (rw_lookup_list positive_encoding ra (rw_index_root_parents ix) ++
          rw_lookup_list positive_encoding rb (rw_index_root_parents ix)))
        (Map.remove positive_encoding rb (Map.remove positive_encoding ra
          (rw_index_root_parents ix))))
  | _, _, _ => ix
  end.

Lemma rw_index_after_union_merge {K Sort V} (g : rw_graph K Sort V) ix a b ra rb :
  Map.wf positive_encoding (rw_index_root_parents ix) ->
  rw_find g a = Some ra -> rw_find g b = Some rb ->
  rw_index_after_union g (rw_merge g ra rb) ix a b =
    RwIndex (rw_index_ops ix) (rw_index_parents ix)
      (rw_merge_table (rw_index_root_parents ix) ra rb).
Proof.
  intros Htable Ha Hb; unfold rw_index_after_union; rewrite Ha, Hb, rw_merge_find, Ha.
  cbn [option_map]; rewrite rw_collapse_fixed; f_equal.
  apply (Map.extensionality positive_encoding).
  - apply Map.wf_set; apply Map.wf_remove; apply Map.wf_remove; exact Htable.
  - apply Map.wf_set; apply Map.wf_remove; exact Htable.
  - intro r; unfold rw_merge_table; destruct (Pos.eq_dec r ra) as [->|Hra].
    + rewrite !Map.get_set_same; reflexivity.
    + rewrite !Map.get_set_other by exact Hra.
      destruct (Pos.eq_dec r rb) as [->|Hrb].
      * rewrite !Map.get_remove_same; reflexivity.
      * rewrite !Map.get_remove_other by assumption; reflexivity.
Qed.

Lemma rw_incidence_transport {A K Sort V} (E : encoding A) (g g' : rw_graph K Sort V)
    keys keys' table :
  rw_table_incidence E g keys table ->
  (forall n, rw_node_at g' n = rw_node_at g n) ->
  (forall node, keys' node = keys node) -> rw_table_incidence E g' keys' table.
Proof.
  intros [Hwf Hinc] Hnodes Hkeys; split; [exact Hwf|].
  intros key n; rewrite Hinc; setoid_rewrite Hnodes; setoid_rewrite Hkeys; reflexivity.
Qed.

Lemma rw_merge_root_incidence {K Sort V} (g : rw_graph K Sort V) ra rb table :
  rw_table_incidence positive_encoding g (rw_root_keys g) table ->
  rw_table_incidence positive_encoding (rw_merge g ra rb) (rw_root_keys (rw_merge g ra rb))
    (rw_merge_table table ra rb).
Proof.
  intros [Hwf Hinc]; split; [apply rw_merge_table_wf; exact Hwf|].
  intros root n; rewrite rw_merge_table_in; split.
  - intros [old [Hin Heq]]; apply Hinc in Hin.
    destruct Hin as [owner [node [Hnode Hkey]]].
    apply rw_root_keys_in in Hkey; destruct Hkey as [child [Hin Hfind]].
    exists owner, node; split; [exact Hnode|]; apply rw_root_keys_in; exists child.
    split; [exact Hin|]; rewrite rw_merge_find, Hfind; cbn; congruence.
  - intros [owner [node [Hnode Hkey]]]; apply rw_root_keys_in in Hkey.
    destruct Hkey as [child [Hin Hfind]]; rewrite rw_merge_find in Hfind.
    destruct (rw_find g child) as [old|] eqn:Hold; cbn in Hfind; try discriminate.
    exists old; split; [|congruence]; apply Hinc; exists owner, node; split; [exact Hnode|].
    apply rw_root_keys_in; exists child; auto.
Qed.

(** The maintained root index remains exact after a successful union, including old aliases. *)
Theorem rw_index_after_union_agrees {K Sort V} (EK : encoding K) (ES : encoding Sort)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (a b : rw_id) :
  rw_graph_wf sig g -> rw_index_agrees EK g ix -> rw_union ES g a b = Some g' ->
  rw_index_agrees EK g' (rw_index_after_union g g' ix a b).
Proof.
  intros Hwf Hix Hunion; destruct (rw_union_inv ES g g' a b Hunion)
    as [ra [rb [s [Ha [Hb [Hsa [Hsb ->]]]]]]].
  pose proof (proj1 (proj2 (proj2 Hix))) as Htable.
  rewrite (rw_index_after_union_merge g ix a b ra rb Htable Ha Hb).
  apply rw_index_incidence in Hix; destruct Hix as [Hops [Hparents Hroots]].
  apply rw_index_incidence; split; [|split].
  - eapply rw_incidence_transport; [exact Hops|intro n; reflexivity|intro node; reflexivity].
  - eapply rw_incidence_transport; [exact Hparents|intro n; reflexivity|intro node; reflexivity].
  - apply rw_merge_root_incidence; exact Hroots.
Qed.

(** * Incremental production changes *)

Definition rw_node_keys_at {A K Sort V} (g : rw_graph K Sort V)
    (keys : rw_node K Sort V -> list A) n : list A :=
  match rw_node_at g n with
  | Some (_, node) => keys node
  | None => []
  end.

Definition rw_update_table {A K Sort V} (E : encoding A) (g g' : rw_graph K Sort V)
    keys keys' table n : Map.t A (list rw_id) :=
  rw_table_add E (rw_node_keys_at g' keys' n) n
    (rw_table_remove E (rw_node_keys_at g keys n) n table).

Lemma rw_update_table_correct {A K Sort V} (E : encoding A) (g g' : rw_graph K Sort V)
    keys keys' table n :
  rw_table_incidence E g keys table ->
  (forall m, m <> n -> rw_node_at g' m = rw_node_at g m) ->
  (forall node, keys' node = keys node) ->
  rw_table_incidence E g' keys' (rw_update_table E g g' keys keys' table n).
Proof.
  intros [Hwf Hinc] Hnodes Hkeys; split.
  - apply rw_table_add_wf; apply rw_table_remove_wf; exact Hwf.
  - intros key m; unfold rw_update_table; rewrite rw_table_add_in, rw_table_remove_in, Hinc.
    destruct (Pos.eq_dec m n) as [->|Hne].
    + unfold rw_node_keys_at; destruct (rw_node_at g n) as [[owner node]|] eqn:Hnode;
        destruct (rw_node_at g' n) as [[owner' node']|] eqn:Hnode'; cbn.
      * split.
        -- intros [[Heq Hin]|[[c [other [Hother Hin]]] Havoid]].
           ++ exists owner', node'; auto.
           ++ assert (other = node) by congruence; subst other; exfalso; apply Havoid; auto.
        -- intros [c [other [Hother Hin]]]; assert (other = node') by congruence;
             subst other; auto.
      * split.
        -- intros [[Heq Hfalse]|[[c [other [Hother Hin]]] Havoid]]; [contradiction|].
           assert (other = node) by congruence; subst other; exfalso; apply Havoid; auto.
        -- intros [c [other [Hother Hin]]]; discriminate.
      * split.
        -- intros [[Heq Hin]|[[c [other [Hother Hin]]] Havoid]];
             [exists owner', node'; auto|discriminate].
        -- intros [c [other [Hother Hin]]]; assert (other = node') by congruence;
             subst other; auto.
      * split.
        -- intros [[Heq Hfalse]|[[c [other [Hother Hin]]] Havoid]];
             [contradiction|discriminate].
        -- intros [c [other [Hother Hin]]]; discriminate.
    + rewrite (Hnodes m Hne); setoid_rewrite Hkeys; intuition congruence.
Qed.

(** Updating one node touches only its old and new operator, raw-child and root-child keys. *)
Definition rw_index_after_node_change {K Sort V} (EK : encoding K) (g g' : rw_graph K Sort V)
    (ix : rw_index K) (n : rw_id) : rw_index K :=
  RwIndex (rw_update_table EK g g' rw_operator_keys rw_operator_keys (rw_index_ops ix) n)
    (rw_update_table positive_encoding g g' rw_child_keys rw_child_keys (rw_index_parents ix) n)
    (rw_update_table positive_encoding g g' (rw_root_keys g) (rw_root_keys g')
      (rw_index_root_parents ix) n).

(** Local production replacement preserves exact buckets when class representatives agree. *)
Theorem rw_index_after_node_change_agrees {K Sort V} (EK : encoding K)
    (sig : rw_signature K Sort V) (g g' : rw_graph K Sort V) (ix : rw_index K) (n : rw_id) :
  rw_graph_wf sig g -> rw_graph_wf sig g' -> rw_index_agrees EK g ix ->
  (forall c, rw_find g' c = rw_find g c) ->
  (forall m, m <> n -> rw_node_at g' m = rw_node_at g m) ->
  rw_index_agrees EK g' (rw_index_after_node_change EK g g' ix n).
Proof.
  intros Hwf Hwf' Hix Hfind Hnodes; apply rw_index_incidence in Hix.
  destruct Hix as [Hops [Hparents Hroots]]; apply rw_index_incidence; split; [|split].
  - apply rw_update_table_correct; [exact Hops|exact Hnodes|intro node; reflexivity].
  - apply rw_update_table_correct; [exact Hparents|exact Hnodes|intro node; reflexivity].
  - apply rw_update_table_correct; [exact Hroots|exact Hnodes|].
    intro node; unfold rw_root_keys; apply flat_map_ext; intro child; now rewrite Hfind.
Qed.
