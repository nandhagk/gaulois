(** * Semantic dominance and a fresh virtual root

    Dominance quantifies over every path from an entry, and parent maps describe forests.
    For example, two entries that both flow through a common node acquire one fresh root.
    Builds on: GraphCore, GraphPrepare and Collections encodings, maps and finite sets. *)

From Stdlib Require Import List Bool PArith.
From Stdlib.Relations Require Import Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
Import List.ListNotations.

(** * Semantic dominance and parent forests *)

(** A dominator occurs on every entry path, including its first node. *)
Definition dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n ->
    d = s \/ exists e, In e es /\ Graph.target g e = d.

(** A strict dominator is a distinct dominator. *)
Definition strictly_dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  dominates g d n /\ d <> n.

(** An immediate dominator is dominated by every strict dominator of its child. *)
Definition immediately_dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  strictly_dominates g d n /\
  forall x, strictly_dominates g x n -> dominates g x d.

(** Parent-map ancestry includes the node itself. *)
Definition idom_ancestor {V} (EV : encoding V) (m : Map.t V V) : V -> V -> Prop :=
  clos_refl_trans V (fun u v => Map.get EV v m = Some u).

(** A parent forest has reachable bindings and well-founded parent chains. *)
Definition forest_on {V E} (EV : encoding V) (g : Graph.t V E) (m : Map.t V V) : Prop :=
  (forall v u, Map.get EV v m = Some u -> reachable g v /\ reachable g u) /\
  well_founded (fun u v => Map.get EV v m = Some u).

Lemma path_endpoint {V E} (g : Graph.t V E) s es n :
  path g s es n -> n = s \/ exists e, In e es /\ Graph.target g e = n.
Proof.
  intro Hpath; induction Hpath as [v|e es n Hedge Hpath IH].
  - left; reflexivity.
  - right; destruct IH as [Heq|[a [Hin Heq]]].
    + exists e; split; [left; reflexivity|symmetry; exact Heq].
    + exists a; split; [right; exact Hin|exact Heq].
Qed.

Lemma path_prefix_target {V E} (g : Graph.t V E) s es n e :
  path g s es n -> In e es ->
  exists pre, path g s pre (Graph.target g e) /\ incl pre es.
Proof.
  intro Hpath; induction Hpath as [v|a es n Hedge Hpath IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; exists [a]; split.
      * constructor; [exact Hedge|constructor].
      * intros aedge [Heq|Hin]; [left; exact Heq|contradiction].
    + destruct (IH Hin) as [pre [Hpre Hsub]].
      exists (a :: pre); split.
      * constructor; assumption.
      * intros aedge [Heq|He]; [left; exact Heq|right; apply Hsub; exact He].
Qed.

(** Every node dominates itself, including an unreachable node. *)
Theorem dominates_refl {V E} (g : Graph.t V E) (n : V) : dominates g n n.
Proof.
  intros s es Hentry Hpath; apply path_endpoint; exact Hpath.
Qed.

(** A dominator of a dominator occurs on every path to the dominated node. *)
Theorem dominates_trans {V E} (g : Graph.t V E) :
  forall a b c, dominates g a b -> dominates g b c -> dominates g a c.
Proof.
  intros a b c Hab Hbc s es Hentry Hpath.
  destruct (Hbc s es Hentry Hpath) as [Heq|[e [Hin Htarget]]].
  - subst b; destruct (Hab s [] Hentry (path_nil s)) as [Heq|[e [Hin _]]].
    + left; exact Heq.
    + contradiction.
  - destruct (path_prefix_target g s es c e Hpath Hin) as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre.
    destruct (Hab s pre Hentry Hpre) as [Heq|[aedge [Ha Htargeta]]].
    + left; exact Heq.
    + right; exists aedge; split; [apply Hsub; exact Ha|exact Htargeta].
Qed.

(** * Deleting a dominator *)

Lemma singleton_absent {V} (EV : encoding V) (d v : V) :
  FinSet.mem EV v (FinSet.add EV d FinSet.empty) = false <-> v <> d.
Proof.
  rewrite <- Bool.not_true_iff_false, FinSet.mem_add, FinSet.mem_empty.
  split.
  - intros Hnot Heq; apply Hnot; left; exact Heq.
  - intros Hne [Heq|Hfalse]; [contradiction|discriminate].
Qed.

Lemma path_without {V E} (EV : encoding V) (blocked : FinSet.t V)
    (g : Graph.t V E) s es n :
  path (without EV blocked g) s es n <->
  path g s es n /\
  forall e, In e es -> FinSet.mem EV (Graph.target g e) blocked = false.
Proof.
  split.
  - intro Hpath; induction Hpath as [v|e es n Hedge Hpath IH].
    + split; [constructor|intros e Hin; contradiction].
    + apply filter_In in Hedge; destruct Hedge as [Hedge Hfree].
      apply Bool.negb_true_iff in Hfree.
      destruct IH as [Horiginal Htargets]; split.
      * exact (@path_cons V E g e es n Hedge Horiginal).
      * intros a [Heq|Hin]; [subst a; exact Hfree|apply Htargets; exact Hin].
  - intros [Hpath Htargets]; induction Hpath as [v|e es n Hedge Hpath IH].
    + constructor.
    + refine (@path_cons V E (without EV blocked g) e es n _ _).
      * apply filter_In; split; [exact Hedge|].
        apply Bool.negb_true_iff; apply Htargets; left; reflexivity.
      * apply IH; intros a Hin; apply Htargets; right; exact Hin.
Qed.

Lemma reachable_without {V E} (EV : encoding V) (blocked : FinSet.t V)
    (g : Graph.t V E) n :
  reachable (without EV blocked g) n <->
  exists s es, In s (Graph.entries g) /\ path g s es n /\
    FinSet.mem EV s blocked = false /\
    forall e, In e es -> FinSet.mem EV (Graph.target g e) blocked = false.
Proof.
  rewrite reachable_iff_path; split.
  - intros [s [es [Hentry Hpath]]].
    apply filter_In in Hentry; destruct Hentry as [Hentry Hfree].
    apply Bool.negb_true_iff in Hfree.
    apply path_without in Hpath; destruct Hpath as [Hpath Htargets].
    exists s, es; auto.
  - intros [s [es [Hentry [Hpath [Hfree Htargets]]]]].
    exists s, es; split.
    + apply filter_In; split; [exact Hentry|now apply Bool.negb_true_iff].
    + apply path_without; auto.
Qed.

Lemma path_occurrence_dec {V E} (EV : encoding V) (g : Graph.t V E) d s es :
  {d = s \/ exists e, In e es /\ Graph.target g e = d} +
  {d <> s /\ forall e, In e es -> Graph.target g e <> d}.
Proof.
  destruct (Pos.eq_dec (encode EV d) (encode EV s)) as [Heq|Hne].
  - left; left; apply (encode_injective EV); exact Heq.
  - assert (Hstart : d <> s) by (intro Heq; subst s; contradiction).
    induction es as [|e es IH].
    + right; split; [exact Hstart|intros a Hin; contradiction].
    + destruct (Pos.eq_dec (encode EV (Graph.target g e)) (encode EV d))
        as [Heq|Hneedge].
      * left; right; exists e; split; [left; reflexivity|].
        apply (encode_injective EV); exact Heq.
      * destruct IH as [Hoccurs|[_ Htargets]].
        -- left; destruct Hoccurs as [Heq|[a [Hin Htarget]]].
           ++ left; exact Heq.
           ++ right; exists a; split; [right; exact Hin|exact Htarget].
        -- right; split; [exact Hstart|].
           intros a [Heq|Hin].
           ++ subst a; intro Heq; rewrite Heq in Hneedge; contradiction.
           ++ apply Htargets; exact Hin.
Qed.

(** Deleting a dominator makes precisely its dominated nodes unreachable. *)
Theorem dominates_iff_unreachable_without {V E} (EV : encoding V)
    (g : Graph.t V E) (d n : V) :
  dominates g d n <-> ~ reachable (without EV (FinSet.add EV d FinSet.empty) g) n.
Proof.
  split.
  - intros Hdom Hreach; apply reachable_without in Hreach.
    destruct Hreach as [s [es [Hentry [Hpath [Hfree Htargets]]]]].
    apply singleton_absent in Hfree.
    destruct (Hdom s es Hentry Hpath) as [Heq|[e [Hin Htarget]]].
    + apply Hfree; symmetry; exact Heq.
    + pose proof (Htargets e Hin) as Hfreeedge.
      apply singleton_absent in Hfreeedge; contradiction.
  - intros Hunreach s es Hentry Hpath.
    destruct (path_occurrence_dec EV g d s es) as [Hoccurs|[Hstart Htargets]].
    + exact Hoccurs.
    + exfalso; apply Hunreach; apply reachable_without.
      exists s, es; split; [exact Hentry|]; split; [exact Hpath|]; split.
      * apply singleton_absent; intro Heq; apply Hstart; symmetry; exact Heq.
      * intros e Hin; apply singleton_absent; apply Htargets; exact Hin.
Qed.

(** * First-occurrence entry traversal *)

(** Retain entries not already indexed, adding each retained entry to the index. *)
Fixpoint virtual_entries_from {V} (EV : encoding V) (seen : FinSet.t V)
    (entries : list V) : list V :=
  match entries with
  | [] => []
  | v :: rest =>
    if FinSet.mem EV v seen then virtual_entries_from EV seen rest
    else v :: virtual_entries_from EV (FinSet.add EV v seen) rest
  end.

(** Synthetic entry edges follow distinct entries in their first-occurrence order. *)
Definition virtual_entries {V E} (EV : encoding V) (g : Graph.t V E) : list V :=
  virtual_entries_from EV FinSet.empty (Graph.entries g).

Lemma virtual_entries_from_in {V} (EV : encoding V) entries :
  forall seen v, In v (virtual_entries_from EV seen entries) <->
    In v entries /\ FinSet.mem EV v seen = false.
Proof.
  induction entries as [|x rest IH]; intros seen v; simpl.
  - tauto.
  - destruct (FinSet.mem EV x seen) eqn:Hx.
    + cbn; rewrite IH; split.
      * intros [Hin Hfree]; split; [right; exact Hin|exact Hfree].
      * intros [[Heq|Hin] Hfree]; [subst v; congruence|auto].
    + cbn; rewrite IH; split.
      * intros [Heq|[Hin Hfree]].
        -- subst v; auto.
        -- apply Bool.not_true_iff_false in Hfree; rewrite FinSet.mem_add in Hfree.
           split; [right; exact Hin|apply Bool.not_true_iff_false; tauto].
      * intros [[Heq|Hin] Hfree].
        -- left; exact Heq.
        -- destruct (Pos.eq_dec (encode EV v) (encode EV x)) as [Heq|Hne].
           ++ left; symmetry; apply (encode_injective EV); exact Heq.
           ++ right; split; [exact Hin|].
              apply Bool.not_true_iff_false; rewrite FinSet.mem_add.
              intros [Heq|Htrue]; [subst v; contradiction|congruence].
Qed.

Lemma virtual_entries_from_nodup {V} (EV : encoding V) entries :
  forall seen, NoDup (virtual_entries_from EV seen entries).
Proof.
  induction entries as [|x rest IH]; intro seen; simpl; [constructor|].
  destruct (FinSet.mem EV x seen); [apply IH|].
  constructor; [|apply IH].
  rewrite virtual_entries_from_in; intros [_ Hfree].
  apply Bool.not_true_iff_false in Hfree; apply Hfree; apply FinSet.mem_add; auto.
Qed.

(** The virtual-entry list contains exactly the entries without repetitions. *)
Theorem virtual_entries_exact {V E} (EV : encoding V) (g : Graph.t V E) :
  NoDup (virtual_entries EV g) /\
  (forall v, In v (virtual_entries EV g) <-> In v (Graph.entries g)).
Proof.
  split; [apply virtual_entries_from_nodup|].
  intro v; unfold virtual_entries; rewrite virtual_entries_from_in, FinSet.mem_empty; tauto.
Qed.

(** * Tagged virtual-root graph *)

(** A fresh root points to each distinct entry, and original edges retain their identities. *)
Definition virtual_graph {V E} (EV : encoding V) (g : Graph.t V E)
    : Graph.t (V + unit) (E + V) :=
  {| Graph.entries := [inr tt];
     Graph.nodes := map (@inl V unit) (Graph.nodes g) ++ [inr tt];
     Graph.out := fun v => match v with
       | inl x => map (@inl E V) (Graph.out g x)
       | inr _ => map (@inr E V) (virtual_entries EV g)
       end;
     Graph.source := fun e => match e with
       | inl x => inl (Graph.source g x)
       | inr _ => inr tt
       end;
     Graph.target := fun e => match e with
       | inl x => inl (Graph.target g x)
       | inr x => inl x
       end |}.

(** Tagged vertex codes distinguish every client vertex from the fresh root. *)
Definition virtual_encoding {V} (EV : encoding V) : encoding (V + unit) :=
  sum_encoding EV unit_encoding.

(** Preparation builds indexes for the graph with its fresh root. *)
Definition virtual_prepared {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : prepared (virtual_encoding EV) (virtual_graph EV g) :=
  prepare (virtual_encoding EV) (virtual_graph EV g).

Lemma nodup_map_injective {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinjective Hnodup; induction Hnodup as [|x xs Hnot Hnodup IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intros Hin; apply in_map_iff in Hin; destruct Hin as [y [Heq Hin]].
    apply Hinjective in Heq; subst y; contradiction.
Qed.

Lemma virtual_node_in {V E} (EV : encoding V) (g : Graph.t V E) v :
  In (inl v) (Graph.nodes (virtual_graph EV g)) <-> In v (Graph.nodes g).
Proof.
  change (In (inl v) (map (@inl V unit) (Graph.nodes g) ++ [inr tt]) <->
    In v (Graph.nodes g)).
  rewrite in_app_iff; split.
  - intros [Hin|[Heq|Hin]].
    + apply in_map_iff in Hin; destruct Hin as [u [Heq Hin]].
      inversion Heq; subst u; exact Hin.
    + discriminate.
    + contradiction.
  - intro Hin; left; apply in_map; exact Hin.
Qed.

Lemma virtual_graph_wf {V E} (EV : encoding V) (g : Graph.t V E) :
  graph_wf g -> graph_wf (virtual_graph EV g).
Proof.
  intro Hwf; constructor.
  - apply nodup_app_disjoint.
    + apply nodup_map_injective; [intros x y Heq; now inversion Heq|].
      apply (nodes_nodup Hwf).
    + constructor; [simpl; tauto|constructor].
    + intros v Hin [Heq|Hnone]; [|contradiction].
      apply in_map_iff in Hin; destruct Hin as [u [Hu _]].
      subst v; discriminate.
  - intros v [Heq|Hin]; [subst v|contradiction].
    apply in_or_app; right; left; reflexivity.
  - intros [v|[]] [e|s] Hin; cbn [virtual_graph] in *;
      apply in_map_iff in Hin; destruct Hin as [x [Heq Hin]].
    + inversion Heq; subst x.
      exact (f_equal (@inl V unit) (out_source Hwf v e Hin)).
    + discriminate.
    + discriminate.
    + reflexivity.
  - intros [v|[]] [e|s] Hnode Hin; cbn [virtual_graph] in Hin;
      apply in_map_iff in Hin; destruct Hin as [x [Heq Hin]].
    + inversion Heq; subst x; apply virtual_node_in.
      eapply out_target_in; [exact Hwf|apply (proj1 (virtual_node_in EV g v));
        exact Hnode|exact Hin].
    + discriminate.
    + discriminate.
    + inversion Heq; subst x; apply virtual_node_in.
      eapply entries_in; [exact Hwf|].
      apply (proj2 (virtual_entries_exact EV g) s); exact Hin.
Qed.

Lemma virtual_out_nodup {V E} (EV : encoding V) (g : Graph.t V E) :
  (forall v, NoDup (Graph.out g v)) ->
  forall v, NoDup (Graph.out (virtual_graph EV g) v).
Proof.
  intros Hout [v|[]]; cbn [virtual_graph]; apply nodup_map_injective.
  - intros x y Heq; now inversion Heq.
  - apply Hout.
  - intros x y Heq; now inversion Heq.
  - apply (proj1 (virtual_entries_exact EV g)).
Qed.

(** The fresh-root graph has well-formed indexes and duplicate-free outgoing edges. *)
Theorem virtual_graph_ready {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p -> ready (virtual_encoding EV) (virtual_graph EV g) (virtual_prepared p).
Proof.
  intros [Hwf [Hout Hprepared]]; apply prepare_ready.
  - apply virtual_graph_wf; exact Hwf.
  - apply virtual_out_nodup; exact Hout.
Qed.

(** * Virtual paths *)

Lemma dominance_path_nil_inv {V E} (g : Graph.t V E) s n :
  path g s [] n -> s = n.
Proof.
  intro Hpath; inversion Hpath; reflexivity.
Qed.

Lemma dominance_path_cons_inv {V E} (g : Graph.t V E) s e es n :
  path g s (e :: es) n ->
  s = Graph.source g e /\ In e (Graph.out g (Graph.source g e)) /\
    path g (Graph.target g e) es n.
Proof.
  intro Hpath; inversion Hpath as [|a rest w Hedge Htail]; subst.
  split; [reflexivity|]; split; assumption.
Qed.

Lemma virtual_path_lift {V E} (EV : encoding V) (g : Graph.t V E) s es n :
  path g s es n ->
  path (virtual_graph EV g) (inl s) (map (@inl E V) es) (inl n).
Proof.
  intro Hpath; induction Hpath as [v|e es n Hedge Hpath IH]; simpl.
  - constructor.
  - apply (@path_cons (V + unit) (E + V) (virtual_graph EV g)
      (inl e) (map (@inl E V) es) (inl n)); [|exact IH].
    apply in_map; exact Hedge.
Qed.

Lemma virtual_path_lower {V E} (EV : encoding V) (g : Graph.t V E) :
  forall ves s n, path (virtual_graph EV g) (inl s) ves (inl n) ->
    exists es, ves = map (@inl E V) es /\ path g s es n.
Proof.
  induction ves as [|[e|entry] ves IH]; intros s n Hpath.
  - apply dominance_path_nil_inv in Hpath; inversion Hpath; subst n.
    exists []; split; [reflexivity|constructor].
  - apply dominance_path_cons_inv in Hpath.
    destruct Hpath as [Hsource [Hedge Htail]]; cbn [virtual_graph] in *.
    inversion Hsource; subst s.
    apply in_map_iff in Hedge; destruct Hedge as [a [Heq Hedge]].
    inversion Heq; subst a.
    destruct (IH (Graph.target g e) n Htail) as [es [Hes Horiginal]].
    exists (e :: es); split; [simpl; now rewrite Hes|constructor; assumption].
  - apply dominance_path_cons_inv in Hpath; destruct Hpath as [Hsource _].
    discriminate.
Qed.

Lemma virtual_original_path_iff {V E} (EV : encoding V) (g : Graph.t V E) s es n :
  path (virtual_graph EV g) (inl s) (map (@inl E V) es) (inl n) <-> path g s es n.
Proof.
  split; [|apply virtual_path_lift].
  intro Hpath; apply virtual_path_lower in Hpath.
  destruct Hpath as [other [Heq Horiginal]].
  assert (Hlists : es = other).
  { clear Horiginal; revert other Heq; induction es as [|e es IH];
      intros [|a other] Heq; try discriminate; [reflexivity|].
    injection Heq as Heq Hrest; inversion Heq; f_equal; apply IH; exact Hrest. }
  subst other; exact Horiginal.
Qed.

Lemma virtual_entry_path {V E} (EV : encoding V) (g : Graph.t V E) s es n :
  path (virtual_graph EV g) (inr tt) (inr s :: map (@inl E V) es) (inl n) <->
  In s (Graph.entries g) /\ path g s es n.
Proof.
  split.
  - intro Hpath; apply dominance_path_cons_inv in Hpath.
    destruct Hpath as [_ [Hentry Hpath]]; cbn [virtual_graph] in Hentry, Hpath.
    apply in_map_iff in Hentry; destruct Hentry as [entry [Heq Hentry]].
    inversion Heq; subst entry; split.
    + apply (proj2 (virtual_entries_exact EV g) s); exact Hentry.
    + apply (proj1 (virtual_original_path_iff EV g s es n)); exact Hpath.
  - intros [Hentry Hpath].
    apply (@path_cons (V + unit) (E + V) (virtual_graph EV g)
      (inr s) (map (@inl E V) es) (inl n)).
    + apply in_map; apply (proj2 (virtual_entries_exact EV g) s); exact Hentry.
    + apply virtual_path_lift; exact Hpath.
Qed.

(** An entry path is exactly its synthetic first edge followed by the original edges. *)
Theorem virtual_path_iff {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p -> forall s es n,
  (path (virtual_graph EV g) (inr tt) (inr s :: map (@inl E V) es) (inl n) <->
   In s (Graph.entries g) /\ path g s es n).
Proof.
  intros Hready s es n; apply virtual_entry_path.
Qed.

Lemma virtual_root_path {V E} (EV : encoding V) (g : Graph.t V E) ves n :
  path (virtual_graph EV g) (inr tt) ves (inl n) ->
  exists s es, ves = inr s :: map (@inl E V) es /\
    In s (Graph.entries g) /\ path g s es n.
Proof.
  destruct ves as [|[e|s] ves]; intro Hpath.
  - apply dominance_path_nil_inv in Hpath; discriminate.
  - apply dominance_path_cons_inv in Hpath; destruct Hpath as [Hsource _].
    discriminate.
  - pose proof Hpath as Htail; apply dominance_path_cons_inv in Htail.
    destruct Htail as [_ [_ Htail]]; cbn [virtual_graph] in Htail.
    apply virtual_path_lower in Htail; destruct Htail as [es [Hes Horiginal]].
    subst ves; apply virtual_entry_path in Hpath.
    exists s, es; auto.
Qed.

Lemma virtual_reachable_iff {V E} (EV : encoding V) (g : Graph.t V E) n :
  reachable (virtual_graph EV g) (inl n) <-> reachable g n.
Proof.
  split; intro Hreach; apply reachable_iff_path in Hreach;
    destruct Hreach as [s [es [Hentry Hpath]]].
  - destruct Hentry as [Heq|Hin]; [subst s|contradiction].
    apply virtual_root_path in Hpath.
    destruct Hpath as [entry [original [_ [Hentry Hpath]]]].
    apply reachable_iff_path; exists entry, original; auto.
  - apply reachable_iff_path; exists (inr tt), (inr s :: map (@inl E V) es).
    split; [left; reflexivity|apply virtual_entry_path; auto].
Qed.

Lemma virtual_path_occurrence {V E} (EV : encoding V) (g : Graph.t V E) d s es :
  (exists e, In e (inr s :: map (@inl E V) es) /\
    Graph.target (virtual_graph EV g) e = inl d) <->
  d = s \/ exists e, In e es /\ Graph.target g e = d.
Proof.
  split.
  - intros [e [[Heq|Hin] Htarget]].
    + subst e; inversion Htarget; left; reflexivity.
    + apply in_map_iff in Hin; destruct Hin as [a [Heq Hin]].
      subst e; inversion Htarget; right; exists a; auto.
  - intros [Heq|[e [Hin Htarget]]].
    + subst d; exists (inr s); split; [left; reflexivity|reflexivity].
    + exists (inl e); split.
      * right; apply in_map; exact Hin.
      * exact (f_equal (@inl V unit) Htarget).
Qed.

(** Real-node dominance is unchanged by adjoining the fresh virtual root. *)
Theorem virtual_dominates_iff {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p -> forall d n,
  (dominates g d n <-> dominates (virtual_graph EV g) (inl d) (inl n)).
Proof.
  intros Hready d n; split.
  - intros Hdom root ves Hentry Hpath.
    destruct Hentry as [Heq|Hin]; [subst root|contradiction].
    apply virtual_root_path in Hpath.
    destruct Hpath as [s [es [Heq [Hentry Hpath]]]]; subst ves.
    right; apply virtual_path_occurrence; apply Hdom; assumption.
  - intros Hdom s es Hentry Hpath.
    assert (Hvirtual : path (virtual_graph EV g) (inr tt)
      (inr s :: map (@inl E V) es) (inl n)).
    { apply virtual_entry_path; auto. }
    destruct (Hdom (inr tt) (inr s :: map (@inl E V) es)
      (or_introl eq_refl) Hvirtual) as [Heq|Hoccurs]; [discriminate|].
    apply (proj1 (virtual_path_occurrence EV g d s es)); exact Hoccurs.
Qed.

(** * Erasing virtual-root parents *)

(** Project real parent bindings and omit every binding involving the virtual root. *)
Definition erase_virtual_parents {V} (EV : encoding V)
    (m : Map.t (V + unit) (V + unit)) : Map.t V V :=
  fold_right (fun binding result =>
    match binding with
    | (inl v, inl u) => Map.set EV v u result
    | _ => result
    end) Map.empty (Map.elements m).

Lemma erase_virtual_parent_list_get {V} (EV : encoding V)
    (bindings : list ((V + unit) * (V + unit))) :
  NoDup (map fst bindings) -> forall v u,
  Map.get EV v (fold_right (fun binding result =>
    match binding with
    | (inl child, inl parent) => Map.set EV child parent result
    | _ => result
    end) Map.empty bindings) = Some u <-> In (inl v, inl u) bindings.
Proof.
  intro Hnodup; induction bindings as [|[[child|[]] [parent|[]]] rest IH];
    intros v u; inversion Hnodup as [|key keys Hnot Hrest]; subst; simpl.
  - rewrite Map.get_empty; split; [discriminate|contradiction].
  - destruct (Pos.eq_dec (encode EV v) (encode EV child)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst v; rewrite Map.get_set_same.
      split.
      * intro Heq; inversion Heq; left; reflexivity.
      * intros [Heq|Hin]; [inversion Heq; reflexivity|].
        exfalso; apply Hnot; apply in_map_iff; exists (inl child, inl u); auto.
    + rewrite Map.get_set_other by (intro Heq; subst child; contradiction).
      rewrite (IH Hrest); split.
      * intro Hin; right; exact Hin.
      * intros [Heq|Hin]; [inversion Heq; subst child; contradiction|exact Hin].
  - rewrite (IH Hrest); split.
    + intro Hin; right; exact Hin.
    + intros [Heq|Hin]; [discriminate|exact Hin].
  - rewrite (IH Hrest); split.
    + intro Hin; right; exact Hin.
    + intros [Heq|Hin]; [discriminate|exact Hin].
  - rewrite (IH Hrest); split.
    + intro Hin; right; exact Hin.
    + intros [Heq|Hin]; [discriminate|exact Hin].
Qed.

(** Real parent lookups survive erasure exactly, while virtual-root parents are omitted. *)
Lemma erase_virtual_parents_get {V} (EV : encoding V)
    (m : Map.t (V + unit) (V + unit)) :
  Map.wf (virtual_encoding EV) m -> forall v u,
  (Map.get EV v (erase_virtual_parents EV m) = Some u <->
   Map.get (virtual_encoding EV) (inl v) m = Some (inl u)).
Proof.
  intros Hwf v u; unfold erase_virtual_parents.
  rewrite erase_virtual_parent_list_get by
    (apply (Map.elements_nodup (virtual_encoding EV)); exact Hwf).
  split.
  - apply Map.elements_sound; exact Hwf.
  - apply Map.elements_complete; exact Hwf.
Qed.

(** Projecting the virtual parent map always produces a well-formed client map. *)
Lemma erase_virtual_parents_wf {V} (EV : encoding V)
    (m : Map.t (V + unit) (V + unit)) : Map.wf EV (erase_virtual_parents EV m).
Proof.
  unfold erase_virtual_parents; induction (Map.elements m)
    as [|[[v|[]] [u|[]]] rest IH]; simpl;
    [apply Map.wf_empty|apply Map.wf_set; exact IH|exact IH|exact IH|exact IH].
Qed.

(** Every entry path in the virtual graph starts at its fresh root. *)
Lemma virtual_root_dominates {V E} (EV : encoding V) (g : Graph.t V E) n :
  dominates (virtual_graph EV g) (inr tt) n.
Proof.
  intros root es [Heq|Hin] Hpath; [left; exact Heq|contradiction].
Qed.

(** Real immediate dominators coincide before and after adding the virtual root. *)
Lemma virtual_immediately_dominates_iff {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) : ready EV g p -> forall d n,
  (immediately_dominates g d n <->
   immediately_dominates (virtual_graph EV g) (inl d) (inl n)).
Proof.
  intros Hready d n; split.
  - intros [[Hdom Hdistinct] Himmediate]; split.
    + split.
      * apply (proj1 (virtual_dominates_iff EV g p Hready d n)); exact Hdom.
      * intro Heq; inversion Heq; contradiction.
    + intros [x|[]] [Hdomx Hdistinctx].
      * apply (proj1 (virtual_dominates_iff EV g p Hready x d)); apply Himmediate.
        split.
        -- apply (proj2 (virtual_dominates_iff EV g p Hready x n)); exact Hdomx.
        -- intro Heq; subst x; contradiction.
      * apply virtual_root_dominates.
  - intros [[Hdom Hdistinct] Himmediate]; split.
    + split.
      * apply (proj2 (virtual_dominates_iff EV g p Hready d n)); exact Hdom.
      * intro Heq; subst d; contradiction.
    + intros x [Hdomx Hdistinctx].
      apply (proj2 (virtual_dominates_iff EV g p Hready x d)); apply Himmediate.
      split.
      * apply (proj1 (virtual_dominates_iff EV g p Hready x n)); exact Hdomx.
      * intro Heq; inversion Heq; contradiction.
Qed.

(** Erasure transfers exact real parent bindings on reachable children to immediate dominators. *)
Lemma erase_virtual_parents_exact {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (m : Map.t (V + unit) (V + unit)) :
  ready EV g p -> Map.wf (virtual_encoding EV) m ->
  (forall d n, reachable (virtual_graph EV g) (inl n) ->
    Map.get (virtual_encoding EV) (inl n) m = Some (inl d) <->
    immediately_dominates (virtual_graph EV g) (inl d) (inl n)) ->
  forall d n, reachable g n -> Map.get EV n (erase_virtual_parents EV m) = Some d <->
    immediately_dominates g d n.
Proof.
  intros Hready Hwf Hexact d n Hreach.
  rewrite erase_virtual_parents_get by exact Hwf.
  rewrite Hexact by (apply virtual_reachable_iff; exact Hreach).
  symmetry; apply (virtual_immediately_dominates_iff EV g p Hready).
Qed.
