(** * Interference from live values

    An observer adds symmetric edges between definitions and live values, excluding moves.
    For example, defining [a] with [b] live adds both directions of the edge [a, b].
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
Import List.ListNotations.

(** An interference graph stores its vertices and indexed neighbour sets. *)
Record interference (V : Type) : Type := Interference {
  vertices : FinSet.t V;
  adjacent : Map.t V (FinSet.t V)
}.
Arguments Interference {V}.
Arguments vertices {V}.
Arguments adjacent {V}.

(** The empty graph has neither vertices nor edges. *)
Definition empty_interference {V} : interference V :=
  Interference FinSet.empty Map.empty.

(** A missing adjacency binding denotes an empty neighbour set. *)
Definition neighbours {V} (EV : encoding V) (ig : interference V) (v : V) : FinSet.t V :=
  match Map.get EV v (adjacent ig) with
  | Some s => s
  | None => FinSet.empty
  end.

(** Interference means membership in the source vertex's neighbour set. *)
Definition interferes {V} (EV : encoding V) (ig : interference V) (u v : V) : Prop :=
  FinSet.mem EV v (neighbours EV ig u) = true.

(** Well-formed interference is symmetric, loop-free, and indexed by well-formed collections. *)
Record interference_wf {V} (EV : encoding V) (ig : interference V) : Prop := {
  interferes_sym : forall u v, interferes EV ig u v -> interferes EV ig v u;
  interferes_irrefl : forall v, ~ interferes EV ig v v;
  interferes_vertex : forall u v, interferes EV ig u v -> FinSet.mem EV u (vertices ig) = true;
  vertices_wf : FinSet.wf EV (vertices ig);
  adjacent_wf : Map.wf EV (adjacent ig);
  neighbours_wf : forall v, FinSet.wf EV (neighbours EV ig v)
}.
Arguments Build_interference_wf {V EV ig}.
Arguments interferes_sym {V EV ig}.
Arguments interferes_irrefl {V EV ig}.
Arguments interferes_vertex {V EV ig}.
Arguments vertices_wf {V EV ig}.
Arguments adjacent_wf {V EV ig}.
Arguments neighbours_wf {V EV ig}.

Section Observer.
Context {V : Type} (EV : encoding V).

Local Definition key_eq_dec (u v : V) : {u = v} + {u <> v}.
Proof.
  destruct (Pos.eq_dec (encode EV u) (encode EV v)) as [Heq|Hne].
  - left; apply (encode_injective EV); exact Heq.
  - right; intro Heq; subst v; contradiction.
Defined.

Local Definition source_eq_dec (x : V) (src : option V) : {Some x = src} + {Some x <> src}.
Proof.
  destruct src as [s|].
  - destruct (key_eq_dec x s) as [Heq|Hne].
    + left; exact (f_equal (@Some V) Heq).
    + right; intro Heq; inversion Heq; contradiction.
  - right; discriminate.
Defined.

(* Each direction reads the original neighbour set; distinct endpoints prevent interference
   between the two updates. Vertex coverage is installed once by [add_point]. *)
Local Definition add_pair (src : option V) (ig : interference V) (edge : V * V)
    : interference V :=
  let '(d, x) := edge in
  if key_eq_dec d x then ig else
  if source_eq_dec x src then ig else
  Interference (vertices ig)
    (Map.set EV x (FinSet.add EV d (neighbours EV ig x))
      (Map.set EV d (FinSet.add EV x (neighbours EV ig d)) (adjacent ig))).

Local Lemma add_pair_exact src ig d x u v :
  interferes EV (add_pair src ig (d, x)) u v <->
  interferes EV ig u v \/
  (d <> x /\ Some x <> src /\ ((u = d /\ v = x) \/ (u = x /\ v = d))).
Proof.
  unfold add_pair.
  destruct (key_eq_dec d x) as [Hsame|Hdistinct]; [subst x; tauto|].
  destruct (source_eq_dec x src) as [Hmove|Hmove]; [tauto|].
  unfold interferes, neighbours; cbn [adjacent].
  destruct (key_eq_dec u x) as [Hx|Hx].
  - subst u; rewrite Map.get_set_same, FinSet.mem_add; intuition congruence.
  - rewrite Map.get_set_other by exact Hx.
    destruct (key_eq_dec u d) as [Hd|Hd].
    + subst u; rewrite Map.get_set_same, FinSet.mem_add; intuition congruence.
    + rewrite Map.get_set_other by exact Hd; intuition congruence.
Qed.

Local Lemma add_pair_indexes src ig edge :
  Map.wf EV (adjacent ig) -> (forall v, FinSet.wf EV (neighbours EV ig v)) ->
  Map.wf EV (adjacent (add_pair src ig edge)) /\
  forall v, FinSet.wf EV (neighbours EV (add_pair src ig edge) v).
Proof.
  destruct edge as [d x]; intros Hmap Hsets; unfold add_pair.
  destruct (key_eq_dec d x); [auto|].
  destruct (source_eq_dec x src); [auto|].
  split.
  - cbn [adjacent]; apply Map.wf_set; apply Map.wf_set; exact Hmap.
  - intro v; unfold neighbours; cbn [adjacent].
    destruct (key_eq_dec v x) as [Hx|Hx].
    + subst v; rewrite Map.get_set_same; apply Map.wf_set; apply Hsets.
    + rewrite Map.get_set_other by exact Hx.
      destruct (key_eq_dec v d) as [Hd|Hd].
      * subst v; rewrite Map.get_set_same; apply Map.wf_set; apply Hsets.
      * rewrite Map.get_set_other by exact Hd; apply Hsets.
Qed.

Local Lemma add_pairs_exact src edges ig u v :
  interferes EV (fold_left (add_pair src) edges ig) u v <->
  interferes EV ig u v \/ exists d x, In (d, x) edges /\ d <> x /\ Some x <> src /\
    ((u = d /\ v = x) \/ (u = x /\ v = d)).
Proof.
  revert ig; induction edges as [|[d x] edges IH]; intro ig; cbn -[add_pair].
  - split; [auto|intros [Hedge|[a [b [Hin _]]]]; [exact Hedge|contradiction]].
  - rewrite IH, add_pair_exact; cbn.
    split.
    + intros [[Hedge|Hnew]|[a [b [Hin Hnew]]]]; [auto| |].
      * right; exists d, x; auto.
      * right; exists a, b; auto.
    + intros [Hedge|[a [b [[Heq|Hin] Hnew]]]]; [auto| |].
      * inversion Heq; subst a b; auto.
      * right; exists a, b; auto.
Qed.

Local Lemma add_pairs_indexes src edges ig :
  Map.wf EV (adjacent ig) -> (forall v, FinSet.wf EV (neighbours EV ig v)) ->
  Map.wf EV (adjacent (fold_left (add_pair src) edges ig)) /\
  forall v, FinSet.wf EV (neighbours EV (fold_left (add_pair src) edges ig) v).
Proof.
  revert ig; induction edges as [|edge edges IH]; intros ig Hmap Hsets; cbn.
  - auto.
  - destruct (add_pair_indexes src ig edge Hmap Hsets) as [Hmap' Hsets'].
    apply IH; assumption.
Qed.

Local Definition point_pairs (defs : list V) (live : FinSet.t V) : list (V * V) :=
  let live_values := FinSet.elements live in
  flat_map (fun d => List.map (fun x => (d, x)) live_values) defs.

Local Lemma point_pairs_spec defs live d x : FinSet.wf EV live ->
  (In (d, x) (point_pairs defs live) <-> In d defs /\ FinSet.mem EV x live = true).
Proof.
  intro Hlive; unfold point_pairs; rewrite in_flat_map; split.
  - intros [a [Ha Hpair]]; apply in_map_iff in Hpair.
    destruct Hpair as [b [Heq Hb]]; inversion Heq; subst a b.
    split; [exact Ha|apply (FinSet.elements_spec EV); assumption].
  - intros [Hd Hx]; exists d; split; [exact Hd|].
    apply in_map_iff; exists x; split; [reflexivity|].
    apply (FinSet.elements_spec EV); assumption.
Qed.

(** A point adds all definition/live edges except self edges and move-source edges. *)
Definition add_point (defs : list V) (src : option V) (live : FinSet.t V)
    (ig : interference V) : interference V :=
  Interference
    (FinSet.union EV (vertices ig) (FinSet.union EV (FinSet.of_list EV defs) live))
    (adjacent (fold_left (add_pair src) (point_pairs defs live) ig)).

(** The observer adds exactly the permitted definition/live edges in both directions. *)
Theorem add_point_exact ig defs src live : FinSet.wf EV live -> forall u v,
  interferes EV (add_point defs src live ig) u v <->
  (interferes EV ig u v \/
   (In u defs /\ FinSet.mem EV v live = true /\ v <> u /\ Some v <> src) \/
   (In v defs /\ FinSet.mem EV u live = true /\ u <> v /\ Some u <> src)).
Proof.
  intros Hlive u v; change (interferes EV
    (fold_left (add_pair src) (point_pairs defs live) ig) u v <->
    (interferes EV ig u v \/
     (In u defs /\ FinSet.mem EV v live = true /\ v <> u /\ Some v <> src) \/
     (In v defs /\ FinSet.mem EV u live = true /\ u <> v /\ Some u <> src))).
  rewrite add_pairs_exact; split.
  - intros [Hedge|[d [x [Hin [Hne [Hsrc Hends]]]]]]; [auto|].
    apply (point_pairs_spec defs live d x Hlive) in Hin.
    destruct Hends as [[Hu Hv]|[Hu Hv]]; subst u v; intuition congruence.
  - intros [Hedge|[Hnew|Hnew]]; [auto| |].
    + right; exists u, v; rewrite point_pairs_spec by exact Hlive; intuition congruence.
    + right; exists v, u; rewrite point_pairs_spec by exact Hlive; intuition congruence.
Qed.

(** Every previous vertex, definition and live value is a vertex after the observer step. *)
Theorem add_point_vertices ig defs src live : FinSet.wf EV live -> forall v,
  FinSet.mem EV v (vertices (add_point defs src live ig)) = true <->
  (FinSet.mem EV v (vertices ig) = true \/ In v defs \/ FinSet.mem EV v live = true).
Proof.
  intros Hlive v; cbn [add_point vertices].
  rewrite !FinSet.mem_union, FinSet.of_list_spec; tauto.
Qed.

(** Adding a point preserves symmetry, absence of loops, vertex coverage and valid indexes. *)
Theorem add_point_wf ig defs src live : interference_wf EV ig -> FinSet.wf EV live ->
  interference_wf EV (add_point defs src live ig).
Proof.
  intros Hig Hlive; constructor.
  - intros u v Hedge; apply add_point_exact; [exact Hlive|].
    apply add_point_exact in Hedge; [|exact Hlive].
    destruct Hedge as [Hedge|[Hedge|Hedge]].
    + left; apply (interferes_sym Hig); exact Hedge.
    + auto.
    + auto.
  - intros v Hedge; apply add_point_exact in Hedge; [|exact Hlive].
    destruct Hedge as [Hedge|[Hedge|Hedge]].
    + exact (interferes_irrefl Hig v Hedge).
    + destruct Hedge as [_ [_ [Hne _]]]; apply Hne; reflexivity.
    + destruct Hedge as [_ [_ [Hne _]]]; apply Hne; reflexivity.
  - intros u v Hedge; apply add_point_vertices; [exact Hlive|].
    apply add_point_exact in Hedge; [|exact Hlive].
    destruct Hedge as [Hedge|[Hedge|Hedge]].
    + left; exact (interferes_vertex Hig u v Hedge).
    + right; left; exact (proj1 Hedge).
    + right; right; exact (proj1 (proj2 Hedge)).
  - cbn [add_point vertices]; apply FinSet.wf_union; [exact (vertices_wf Hig)|].
    apply FinSet.wf_union; [apply FinSet.wf_fold_add; apply Map.wf_empty|exact Hlive].
  - exact (proj1 (add_pairs_indexes src (point_pairs defs live) ig
      (adjacent_wf Hig) (neighbours_wf Hig))).
  - exact (proj2 (add_pairs_indexes src (point_pairs defs live) ig
      (adjacent_wf Hig) (neighbours_wf Hig))).
Qed.

End Observer.
