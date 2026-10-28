(** * Weak topological orders

    Balanced tokens represent nested components and their distinguished heads.
    For example, [WOpen 0; WVertex 1; WClose] represents the component (0 1).
    Builds on: GraphCore, GraphPrepare, GraphDfs, GraphScc and Collections maps and sets. *)

From Stdlib Require Import List Bool PArith Arith Lia Wf_nat Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphScc.
Import List.ListNotations.

(** A token emits a vertex, opens a headed component, or closes its innermost component. *)
Inductive wto_token (V : Type) : Type :=
  | WVertex (v : V)
  | WOpen (h : V)
  | WClose.
Arguments WVertex {V} v.
Arguments WOpen {V} h.
Arguments WClose {V}.

(** A weak order is a flat sequence of nesting tokens. *)
Definition wto (V : Type) : Type := list (wto_token V).

(** Balance checks every close and requires all incoming and newly opened frames to close. *)
Fixpoint balanced_from {V} (d : nat) (w : wto V) : bool :=
  match w with
  | [] => Nat.eqb d 0
  | WVertex _ :: rest => balanced_from d rest
  | WOpen _ :: rest => balanced_from (S d) rest
  | WClose :: rest =>
    match d with
    | O => false
    | S previous => balanced_from previous rest
    end
  end.

(** An annotation records each vertex's innermost-first enclosing heads. *)
Fixpoint annotate {V} (stack : list V) (w : wto V) : list (V * list V) :=
  match w with
  | [] => []
  | WVertex v :: rest => (v, stack) :: annotate stack rest
  | WOpen h :: rest => (h, h :: stack) :: annotate (h :: stack) rest
  | WClose :: rest => annotate (tl stack) rest
  end.

(** Textual order includes the head at every opening token. *)
Definition wto_order {V} (w : wto V) : list V := map fst (annotate [] w).

(** Every reachable edge goes forward or returns to an enclosing head. *)
Definition wto_valid {V E} (g : Graph.t V E) (w : wto V) : Prop :=
  balanced_from 0 w = true /\ NoDup (wto_order w) /\
  (forall v, In v (wto_order w) <-> reachable g v) /\
  forall e, reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
    before (wto_order w) (Graph.source g e) (Graph.target g e) \/
    exists st, In (Graph.source g e, st) (annotate [] w) /\ In (Graph.target g e) st.

(** The universal fallback opens every listed vertex, then closes every frame. *)
Definition wto_all_heads {V} (order : list V) : wto V :=
  map (fun h => WOpen h) order ++ repeat (WClose : wto_token V) (length order).

(** * Token composition *)

Fixpoint wto_vertices {V} (w : wto V) : list V :=
  match w with
  | [] => []
  | WVertex v :: rest => v :: wto_vertices rest
  | WOpen h :: rest => h :: wto_vertices rest
  | WClose :: rest => wto_vertices rest
  end.

Lemma annotate_vertices {V} (w : wto V) stack :
  map fst (annotate stack w) = wto_vertices w.
Proof.
  revert stack; induction w as [|[v|h|] rest IH]; intro stack; cbn; auto.
  - rewrite IH; reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** * Interval indexing *)

Module WtoSpan.

(** Reverse token positions make an enclosing head's interval closed at both ends. *)
Record t : Type := Make {
  pos : positive;
  finish : positive;
  head : bool
}.

End WtoSpan.
Import WtoSpan.

Module WtoScan.

(** Unmatched closing positions are frames for openings encountered further to the left. *)
Record t (V : Type) : Type := Make {
  next : positive;
  closes : list positive;
  rows : list (V * WtoSpan.t)
}.
Arguments Make {V}.
Arguments next {V}.
Arguments closes {V}.
Arguments rows {V}.

End WtoScan.
Import WtoScan.

(** A right-to-left token pass matches each opening with its closing position. *)
Definition wto_scan_step {V} (token : wto_token V) (st : WtoScan.t V) : WtoScan.t V :=
  match token with
  | WVertex v =>
    WtoScan.Make (Pos.succ (next st)) (closes st)
      ((v, WtoSpan.Make (next st) (next st) false) :: rows st)
  | WOpen h =>
    WtoScan.Make (Pos.succ (next st)) (tl (closes st))
      ((h, WtoSpan.Make (next st) (hd (next st) (closes st)) true) :: rows st)
  | WClose => WtoScan.Make (Pos.succ (next st)) (next st :: closes st) (rows st)
  end.

Definition wto_scan {V} (w : wto V) (st : WtoScan.t V) : WtoScan.t V :=
  fold_right wto_scan_step st w.

Definition wto_spans {V} (w : wto V) : list (V * WtoSpan.t) :=
  rows (wto_scan w (WtoScan.Make 1%positive [] [])).

Definition wto_span_map {V} (EV : encoding V) (spans : list (V * WtoSpan.t))
    : Map.t V WtoSpan.t :=
  fold_right (fun vs m => Map.set EV (fst vs) (snd vs) m) Map.empty spans.

(** Every key is inserted once; a duplicate is rejected before checking edges. *)
Fixpoint wto_unique {V} (EV : encoding V) (seen : FinSet.t V) (vs : list V) : bool :=
  match vs with
  | [] => true
  | v :: rest => negb (FinSet.mem EV v seen) && wto_unique EV (FinSet.add EV v seen) rest
  end.

Definition wto_edge_b {V} (EV : encoding V) (index : Map.t V WtoSpan.t) (u v : V)
    : bool :=
  match Map.get EV u index, Map.get EV v index with
  | Some a, Some b =>
    Pos.ltb (pos b) (pos a) ||
    (head b && Pos.leb (finish b) (pos a) && Pos.leb (pos a) (pos b))
  | _, _ => false
  end.

(** The independent checker uses intervals, exact reachability, and one scan of each adjacency. *)
Definition check_wto {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (w : wto V) : bool :=
  let spans := wto_spans w in
  let order := map fst spans in
  let index := wto_span_map EV spans in
  let search := dfs p FinSet.empty (Graph.entries g) in
  balanced_from 0 w && wto_unique EV FinSet.empty order &&
  forallb (fun v => FinSet.mem EV v (visited search)) order &&
  forallb (fun v => Map.mem EV v index) (preorder search) &&
  forallb (fun v => forallb
    (fun e => wto_edge_b EV index v (Graph.target g e)) (succ_edges p v)) order.

(** * Recursive SCC construction *)

(** The reverse-postorder ranks are built once and queried while selecting component heads. *)
Definition wto_ranks {V} (EV : encoding V) (order : list V) : Map.t V positive :=
  snd (fold_left (fun acc v =>
    (Pos.succ (fst acc), Map.set EV v (fst acc) (snd acc))) order
    (1%positive, Map.empty)).

Definition wto_rank {V} (EV : encoding V) (ranks : Map.t V positive) (v : V) : positive :=
  match Map.get EV v ranks with
  | Some n => n
  | None => 1%positive
  end.

Definition wto_earlier {V} (EV : encoding V) (ranks : Map.t V positive) (u v : V) : V :=
  if Pos.leb (wto_rank EV ranks u) (wto_rank EV ranks v) then u else v.

Definition wto_remove {V} (EV : encoding V) (h : V) (vs : list V) : list V :=
  filter (fun v => negb (Pos.eqb (encode EV h) (encode EV v))) vs.

Definition wto_self_loop {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (v : V) : bool :=
  existsb (fun e => Pos.eqb (encode EV v) (encode EV (Graph.target g e))) (succ_edges p v).

(** A component is opened exactly when it has several vertices or a singleton self-loop. *)
Definition wto_component {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V)
    (component : list V) : wto V :=
  match component with
  | [] => []
  | h :: rest =>
    let header := fold_left (wto_earlier EV ranks) rest h in
    match rest with
    | [] => if wto_self_loop p h then [WOpen h; WClose] else [WVertex h]
    | _ :: _ => WOpen header :: recur (wto_remove EV header component) ++ [WClose]
    end
  end.

(** Reverse Tarjan emission makes every edge between components go forward. *)
Definition wto_unfold {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (ranks : Map.t V positive) (recur : list V -> wto V)
    (region : list V) : wto V :=
  flat_map (wto_component p ranks recur) (rev (components (scc_within p region))).

(** Binary depth covers the strictly shrinking region at every recursive component opening. *)
Definition wto_of {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : wto V :=
  let order := rpo (dfs p FinSet.empty (Graph.entries g)) in
  let ranks := wto_ranks EV order in
  Pos.iter (wto_unfold p ranks) (fun _ => []) (Pos.of_succ_nat (length order)) order.

(** Internal schedules use the directly constructed order. *)
Definition wto_total {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) : wto V := wto_of p.

Lemma wto_order_vertices {V} (w : wto V) : wto_order w = wto_vertices w.
Proof.
  apply annotate_vertices.
Qed.

Lemma wto_vertices_app {V} (first last : wto V) :
  wto_vertices (first ++ last) = wto_vertices first ++ wto_vertices last.
Proof.
  induction first as [|[v|h|] first IH]; cbn; rewrite ?IH; reflexivity.
Qed.

Lemma wto_vertices_closes {V} n :
  wto_vertices (repeat (WClose : wto_token V) n) = [].
Proof.
  induction n; cbn; assumption || reflexivity.
Qed.

Lemma balanced_closes {V} n :
  balanced_from n (repeat (WClose : wto_token V) n) = true.
Proof.
  induction n; cbn; assumption || reflexivity.
Qed.

Lemma balanced_opens {V} (order : list V) d tail :
  balanced_from d (map (fun h => WOpen h) order ++ tail) =
  balanced_from (length order + d) tail.
Proof.
  revert d; induction order as [|h rest IH]; intro d; cbn; [reflexivity|].
  rewrite IH; f_equal; lia.
Qed.

Lemma annotate_closes {V} n (stack : list V) :
  annotate stack (repeat (WClose : wto_token V) n) = [].
Proof.
  revert stack; induction n; intro stack; cbn; auto.
Qed.

Lemma all_heads_order {V} (order : list V) : wto_order (wto_all_heads order) = order.
Proof.
  rewrite wto_order_vertices; unfold wto_all_heads.
  rewrite wto_vertices_app, wto_vertices_closes, app_nil_r.
  induction order; cbn; congruence.
Qed.

Lemma annotate_append_closes {V} (pre : wto V) n stack :
  annotate stack (pre ++ repeat WClose n) = annotate stack pre.
Proof.
  revert stack; induction pre as [|[v|h|] rest IH]; intro stack; cbn.
  - apply annotate_closes.
  - f_equal; apply IH.
  - f_equal; apply IH.
  - apply IH.
Qed.

Lemma opens_annotation {V} (pre post : list V) v stack :
  In (v, v :: rev pre ++ stack)
    (annotate stack (map (fun h => WOpen h) (pre ++ v :: post))).
Proof.
  revert stack; induction pre as [|h pre IH]; intro stack; cbn.
  - left; reflexivity.
  - right; rewrite <- app_assoc; apply IH.
Qed.

(** Any duplicate-free listing of the reachable nodes yields a valid nested fallback. *)
Theorem wto_all_heads_valid {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (order : list V) :
  ready EV g p -> NoDup order -> (forall v, In v order <-> reachable g v) ->
  wto_valid g (wto_all_heads order).
Proof.
  intros Hready Hnodup Hreach; unfold wto_valid; rewrite all_heads_order.
  split.
  - unfold wto_all_heads; rewrite balanced_opens, Nat.add_0_r; apply balanced_closes.
  - split; [exact Hnodup|]; split; [exact Hreach|].
    intros e Hsource Hedge.
    destruct (in_split _ _ (proj2 (Hreach _) Hsource)) as [pre [post Horder]].
    assert (Htarget : In (Graph.target g e) order).
    { apply Hreach; eapply reachable_step; eauto. }
    rewrite Horder in Htarget.
    apply in_app_or in Htarget; destruct Htarget as [Hpre|[Heq|Hpost]].
    + right; exists (Graph.source g e :: rev pre); split.
      * unfold wto_all_heads; rewrite annotate_append_closes, Horder.
        pose proof (opens_annotation pre post (Graph.source g e) []) as Hannot.
        rewrite app_nil_r in Hannot; exact Hannot.
      * right; rewrite <- in_rev; exact Hpre.
    + right; exists (Graph.source g e :: rev pre); split.
      * unfold wto_all_heads; rewrite annotate_append_closes, Horder.
        pose proof (opens_annotation pre post (Graph.source g e) []) as Hannot.
        rewrite app_nil_r in Hannot; exact Hannot.
      * left; exact Heq.
    + left; destruct (in_split _ _ Hpost) as [middle [last Hsplit]].
      exists pre, middle, last; rewrite Horder, Hsplit; reflexivity.
Qed.

(** * Well-nested token segments *)

(** A segment consists of vertices and properly closed, recursively nested components. *)
Inductive wto_nested {V} : wto V -> Prop :=
  | WtoNestedNil : wto_nested []
  | WtoNestedVertex : forall v tail,
      wto_nested tail -> wto_nested (WVertex v :: tail)
  | WtoNestedOpen : forall h body tail,
      wto_nested body -> wto_nested tail ->
      wto_nested (WOpen h :: body ++ WClose :: tail).

Lemma wto_nested_app {V} (first last : wto V) :
  wto_nested first -> wto_nested last -> wto_nested (first ++ last).
Proof.
  intros Hfirst Hlast; induction Hfirst as [|v tail Htail IH|h body tail Hbody IHbody Htail IHtail].
  - exact Hlast.
  - cbn; constructor; exact IH.
  - cbn; rewrite <- app_assoc; cbn; constructor; assumption.
Qed.

Lemma wto_nested_balance {V} (w : wto V) :
  wto_nested w -> forall d tail, balanced_from d (w ++ tail) = balanced_from d tail.
Proof.
  intro Hnested; induction Hnested as [|v rest Hrest IH|h body rest Hbody IHbody Hrest IHrest];
    intros d tail; cbn.
  - reflexivity.
  - apply IH.
  - rewrite <- app_assoc, IHbody; cbn; apply IHrest.
Qed.

Lemma wto_nested_annotate {V} (w : wto V) :
  wto_nested w -> forall stack tail,
    annotate stack (w ++ tail) =
    map (fun vs => (fst vs, snd vs ++ stack)) (annotate [] w) ++ annotate stack tail.
Proof.
  intro Hnested; induction Hnested as [|v rest Hrest IH|h body rest Hbody IHbody Hrest IHrest];
    intros stack tail; cbn.
  - reflexivity.
  - rewrite IH; cbn; reflexivity.
  - rewrite <- app_assoc, IHbody; cbn.
    rewrite IHrest, (IHbody [h] (WClose :: rest)); cbn.
    rewrite map_app; cbn; rewrite map_map, <- app_assoc.
    f_equal; f_equal.
    apply map_ext; intros [v st]; cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma balanced_split {V} (w : wto V) :
  forall d, balanced_from (S d) w = true ->
  exists body tail, w = body ++ WClose :: tail /\
    wto_nested body /\ balanced_from d tail = true.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length (wto_token V)))).
  intros d Hbalanced; destruct w as [|[v|h|] rest]; cbn in Hbalanced.
  - discriminate.
  - destruct (IH rest ltac:(unfold ltof; cbn; lia) d Hbalanced)
      as [body [tail [Hsplit [Hbody Htail]]]].
    exists (WVertex v :: body), tail; split; [cbn; rewrite Hsplit; reflexivity|].
    split; [constructor; exact Hbody|exact Htail].
  - destruct (IH rest ltac:(unfold ltof; cbn; lia) (S d) Hbalanced)
      as [body [middle [Hsplit [Hbody Hmiddle]]]].
    destruct (IH middle ltac:(unfold ltof; cbn; rewrite Hsplit, length_app; cbn; lia)
      d Hmiddle) as [last [tail [Hlast [Hnested Htail]]]].
    exists (WOpen h :: body ++ WClose :: last), tail; split.
    + cbn; rewrite Hsplit, Hlast, <- app_assoc; reflexivity.
    + split; [constructor; assumption|exact Htail].
  - exists [], rest; cbn; split; [reflexivity|].
    split; [constructor|exact Hbalanced].
Qed.

Lemma balanced_nested {V} (w : wto V) : balanced_from 0 w = true -> wto_nested w.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@length (wto_token V)))).
  intro Hbalanced; destruct w as [|[v|h|] rest]; cbn in Hbalanced.
  - constructor.
  - constructor; apply IH; [unfold ltof; cbn; lia|exact Hbalanced].
  - destruct (balanced_split rest 0 Hbalanced) as [body [tail [Hsplit [Hbody Htail]]]].
    rewrite Hsplit; constructor; [exact Hbody|].
    apply IH; [unfold ltof; cbn; rewrite Hsplit, length_app; cbn; lia|exact Htail].
  - discriminate.
Qed.

(** * Local construction certificates *)

(** Local orders cover a region and constrain exactly the edges with both ends in that region. *)
Record wto_region {V E} (g : Graph.t V E) (region : list V) (w : wto V) : Prop := {
  wto_region_nested : wto_nested w;
  wto_region_members : Permutation (wto_order w) region;
  wto_region_edges : forall e,
    In (Graph.source g e) region -> In (Graph.target g e) region ->
    In e (Graph.out g (Graph.source g e)) ->
    before (wto_order w) (Graph.source g e) (Graph.target g e) \/
    exists st, In (Graph.source g e, st) (annotate [] w) /\ In (Graph.target g e) st
}.

Lemma wto_order_app {V} (first last : wto V) :
  wto_order (first ++ last) = wto_order first ++ wto_order last.
Proof.
  rewrite !wto_order_vertices; apply wto_vertices_app.
Qed.

Lemma wto_annotate_app {V} (first last : wto V) :
  wto_nested first -> annotate [] (first ++ last) = annotate [] first ++ annotate [] last.
Proof.
  intro Hnested; rewrite (wto_nested_annotate first Hnested).
  assert (Hmap : map (fun vs : V * list V => (fst vs, snd vs ++ []))
    (annotate [] first) = annotate [] first).
  { induction (annotate [] first) as [|[v st] rest IH]; cbn; [reflexivity|].
    rewrite app_nil_r, IH; reflexivity. }
  rewrite Hmap; reflexivity.
Qed.

Lemma wto_before_suffix {V} (pre post : list V) u v :
  before pre u v -> before (pre ++ post) u v.
Proof.
  intros [a [b [c Hsplit]]]; exists a, b, (c ++ post).
  rewrite Hsplit, <- app_assoc; cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma wto_before_map {A B} (f : A -> B) xs u v :
  before xs u v -> before (map f xs) (f u) (f v).
Proof.
  intros [a [b [c Hsplit]]]; exists (map f a), (map f b), (map f c).
  rewrite Hsplit, map_app; cbn; rewrite map_app; reflexivity.
Qed.

Lemma wto_flat_order {V A} (f : A -> wto V) xs :
  wto_order (flat_map f xs) = flat_map (fun x => wto_order (f x)) xs.
Proof.
  induction xs as [|x rest IH]; cbn [flat_map]; [reflexivity|].
  rewrite wto_order_app, IH; reflexivity.
Qed.

Lemma wto_flat_nested {V A} (f : A -> wto V) xs :
  (forall x, In x xs -> wto_nested (f x)) -> wto_nested (flat_map f xs).
Proof.
  induction xs as [|x rest IH]; intro Hall; cbn [flat_map].
  - constructor.
  - apply wto_nested_app; [apply Hall; left; reflexivity|].
    apply IH; intros y Hy; apply Hall; right; exact Hy.
Qed.

Lemma wto_flat_annotation {V A} (f : A -> wto V) xs x v st :
  (forall y, In y xs -> wto_nested (f y)) -> In x xs ->
  In (v, st) (annotate [] (f x)) -> In (v, st) (annotate [] (flat_map f xs)).
Proof.
  induction xs as [|y rest IH]; intros Hall Hin Hannot; [contradiction|].
  cbn [flat_map]; rewrite wto_annotate_app by (apply Hall; left; reflexivity).
  destruct Hin as [Heq|Hin].
  - subst y; apply in_or_app; left; exact Hannot.
  - apply in_or_app; right; apply IH; [|exact Hin|exact Hannot].
    intros z Hz; apply Hall; right; exact Hz.
Qed.

Lemma wto_flat_before_inside {V A} (f : A -> wto V) xs x u v :
  In x xs -> before (wto_order (f x)) u v ->
  before (wto_order (flat_map f xs)) u v.
Proof.
  intros Hin Hbefore; destruct (in_split _ _ Hin) as [pre [post Hsplit]].
  rewrite Hsplit, flat_map_app; cbn [flat_map]; rewrite !wto_order_app.
  apply tarjan_before_prefix, wto_before_suffix; exact Hbefore.
Qed.

Lemma wto_flat_before_cross {V A} (f : A -> wto V) xs x y u v :
  before xs x y -> In u (wto_order (f x)) -> In v (wto_order (f y)) ->
  before (wto_order (flat_map f xs)) u v.
Proof.
  intros [pre [middle [post Hsplit]]] Hu Hv.
  rewrite Hsplit, !flat_map_app; cbn [flat_map]; rewrite !wto_order_app.
  apply tarjan_before_prefix, tarjan_before_cross; [exact Hu|].
  rewrite flat_map_app, wto_order_app; cbn [flat_map]; rewrite wto_order_app.
  apply in_or_app; right; apply in_or_app; left; exact Hv.
Qed.

Lemma wto_remove_spec {V} (EV : encoding V) h xs v :
  In v (wto_remove EV h xs) <-> In v xs /\ v <> h.
Proof.
  unfold wto_remove; rewrite filter_In, negb_true_iff, Pos.eqb_neq.
  split; intros [Hin Hne]; split; [exact Hin| |exact Hin|].
  - intro Heq; subst v; contradiction.
  - intro Heq; apply Hne, (encode_injective EV); symmetry; exact Heq.
Qed.

Lemma wto_earlier_member {V} (EV : encoding V) ranks xs h :
  In (fold_left (wto_earlier EV ranks) xs h) (h :: xs).
Proof.
  revert h; induction xs as [|v rest IH]; intro h; cbn; [left; reflexivity|].
  specialize (IH (wto_earlier EV ranks h v)); unfold wto_earlier in IH.
  destruct (Pos.leb (wto_rank EV ranks h) (wto_rank EV ranks v)) eqn:Hchoice.
  - unfold wto_earlier; rewrite Hchoice; destruct IH as [Heq|Hin].
    + left; exact Heq.
    + right; right; exact Hin.
  - unfold wto_earlier; rewrite Hchoice; right; exact IH.
Qed.

Lemma wto_remove_shorter {V} (EV : encoding V) h xs :
  In h xs -> length (wto_remove EV h xs) < length xs.
Proof.
  induction xs as [|v rest IH]; intro Hin; [contradiction|].
  unfold wto_remove in *; cbn; destruct (Pos.eqb (encode EV h) (encode EV v)) eqn:Heq.
  - pose proof (filter_length_le (fun x => negb (Pos.eqb (encode EV h) (encode EV x))) rest).
    cbn; lia.
  - cbn; destruct Hin as [Heqv|Hin].
    + subst v; rewrite Pos.eqb_refl in Heq; discriminate.
    + specialize (IH Hin); lia.
Qed.

Lemma wto_open_order {V} h (body : wto V) :
  wto_order (WOpen h :: body ++ [WClose]) = h :: wto_order body.
Proof.
  rewrite !wto_order_vertices; cbn; rewrite wto_vertices_app; cbn.
  rewrite app_nil_r; reflexivity.
Qed.

Lemma wto_open_annotation {V} h (body : wto V) :
  wto_nested body -> annotate [] (WOpen h :: body ++ [WClose]) =
    (h, [h]) :: map (fun vs => (fst vs, snd vs ++ [h])) (annotate [] body).
Proof.
  intro Hbody; cbn; rewrite wto_nested_annotate by exact Hbody; cbn.
  rewrite app_nil_r; reflexivity.
Qed.

Lemma wto_open_region {V E} (g : Graph.t V E) h rest body :
  wto_region g rest body ->
  wto_region g (h :: rest) (WOpen h :: body ++ [WClose]).
Proof.
  intros [Hnested Hperm Hedges]; constructor.
  - change (wto_nested (WOpen h :: body ++ WClose :: [])).
    constructor; [exact Hnested|constructor].
  - rewrite wto_open_order; constructor; exact Hperm.
  - intros e Hsource Htarget Hedge.
    rewrite wto_open_order, wto_open_annotation by exact Hnested.
    destruct Htarget as [Htarget|Htarget].
    + right.
      destruct Hsource as [Hsource|Hsource].
      * exists [h]; split; [left; congruence|left; congruence].
      * assert (Hin : In (Graph.source g e) (map fst (annotate [] body))).
        { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hsource]. }
        apply in_map_iff in Hin; destruct Hin as [[v st] [Heq Hin]]; cbn in Heq; subst v.
        exists (st ++ [h]); split.
        -- right; apply in_map_iff; exists (Graph.source g e, st); auto.
        -- apply in_or_app; right; left; congruence.
    + destruct Hsource as [Hsource|Hsource].
      * left; apply dfs_before_cons; left; split; [symmetry; exact Hsource|].
        eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Htarget].
      * destruct (Hedges e Hsource Htarget Hedge) as [Hbefore|[st [Hannot Hhead]]].
        -- left; apply dfs_before_cons; right; exact Hbefore.
        -- right; exists (st ++ [h]); split.
           ++ right; apply in_map_iff; exists (Graph.source g e, st); auto.
           ++ apply in_or_app; left; exact Hhead.
Qed.

Lemma wto_region_permutation {V E} (g : Graph.t V E) first last w :
  Permutation first last -> wto_region g first w -> wto_region g last w.
Proof.
  intros Hperm [Hnested Hmembers Hedges]; constructor; [exact Hnested| |].
  - eapply Permutation_trans; eauto.
  - intros e Hsource Htarget Hedge; apply Hedges; [| |exact Hedge].
    + eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hsource].
    + eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Htarget].
Qed.

Lemma wto_remove_permutation {V} (EV : encoding V) h region :
  NoDup region -> In h region -> Permutation (h :: wto_remove EV h region) region.
Proof.
  intros Hnodup Hmember; apply NoDup_Permutation; [|exact Hnodup|].
  - constructor.
    + rewrite wto_remove_spec; tauto.
    + apply NoDup_filter; exact Hnodup.
  - intro v; cbn; rewrite wto_remove_spec.
    destruct (dfs_eq_dec EV v h); subst; intuition congruence.
Qed.

Lemma wto_component_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) ranks recur component :
  ready EV g p -> incl component (Graph.nodes g) -> NoDup component ->
  (forall h, In h component ->
    wto_region g (wto_remove EV h component) (recur (wto_remove EV h component))) ->
  wto_region g component (wto_component p ranks recur component).
Proof.
  intros Hready Hnodes Hnodup Hrecur; destruct component as [|h [|v rest]].
  - constructor; [constructor|constructor|intros e Hfalse; contradiction].
  - unfold wto_component; cbn [fold_left].
    destruct (wto_self_loop p h) eqn:Hself.
    + change (wto_region g [h] (WOpen h :: [] ++ [WClose])).
      apply wto_open_region; constructor; [constructor|constructor|].
      intros e Hfalse; contradiction.
    + constructor; [constructor; constructor|constructor; constructor|].
      intros e Hsource Htarget Hedge; cbn in Hsource, Htarget.
      destruct Hsource as [Hsource|Hfalse]; [|contradiction].
      destruct Htarget as [Htarget|Hfalse]; [|contradiction].
      exfalso; unfold wto_self_loop in Hself.
      assert (Hloop : existsb
        (fun edge => Pos.eqb (encode EV h) (encode EV (Graph.target g edge)))
        (succ_edges p h) = true).
      { apply existsb_exists; exists e; split.
        - destruct Hready as [_ [_ Hp]].
          rewrite (succ_agrees Hp h (Hnodes h (or_introl eq_refl))).
          rewrite Hsource; exact Hedge.
        - rewrite <- Htarget; apply Pos.eqb_refl. }
      congruence.
  - unfold wto_component.
    set (header := fold_left (wto_earlier EV ranks) (v :: rest) h).
    assert (Hheader : In header (h :: v :: rest)) by apply wto_earlier_member.
    eapply wto_region_permutation; [apply wto_remove_permutation; eassumption|].
    apply wto_open_region; apply Hrecur; exact Hheader.
Qed.

Lemma wto_before_map_inverse {A B} (f : A -> B) xs u v :
  NoDup (map f xs) -> In u xs -> In v xs ->
  before (map f xs) (f u) (f v) -> before xs u v.
Proof.
  induction xs as [|x rest IH]; intros Hnodup Hu Hv Hbefore; [contradiction|].
  inversion Hnodup as [|head tail Hfresh Htail]; subst.
  destruct Hu as [Hequ|Hu], Hv as [Heqv|Hv].
  - subst u v; exfalso; exact (dfs_before_head_false (f x) (map f rest) (f x)
      Hnodup Hbefore).
  - subst u; apply dfs_before_cons; left; auto.
  - subst v; exfalso; exact (dfs_before_head_false (f x) (map f rest) (f u)
      Hnodup Hbefore).
  - apply dfs_before_cons in Hbefore; destruct Hbefore as [[Heq _]|Hbefore].
    + exfalso; apply Hfresh; rewrite <- Heq; apply in_map; exact Hu.
    + apply dfs_before_cons; right; apply IH; assumption.
Qed.

Lemma wto_combine_maps {A B} (xs : list A) (ys : list B) :
  length xs = length ys ->
  map fst (combine xs ys) = xs /\ map snd (combine xs ys) = ys.
Proof.
  revert ys; induction xs as [|x rest IH]; intros [|y tail] Hlength;
    cbn in Hlength |- *; try discriminate; [auto|].
  destruct (IH tail ltac:(lia)) as [Hfst Hsnd]; rewrite Hfst, Hsnd; auto.
Qed.

Lemma wto_scc_component_nodes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region c :
  ready EV g p -> incl region (Graph.nodes g) ->
  In c (components (scc_within p region)) -> NoDup c /\ incl c region.
Proof.
  intros Hready Hregion Hc.
  destruct (scc_within_indexes EV g p region) as [Hnodup _].
  split.
  - destruct (in_split _ _ Hc) as [pre [post Hsplit]].
    rewrite Hsplit, concat_app in Hnodup; cbn in Hnodup.
    apply (tarjan_nodup_prefix c (concat post)).
    apply (tarjan_nodup_suffix (concat pre)); exact Hnodup.
  - intros v Hv; apply (proj1 (scc_within_members EV g p region Hready Hregion v)).
    apply in_concat; exists c; auto.
Qed.

Lemma wto_scc_edge_order {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) region e first last :
  ready EV g p -> incl region (Graph.nodes g) ->
  In first (components (scc_within p region)) ->
  In last (components (scc_within p region)) ->
  In (Graph.source g e) first -> In (Graph.target g e) last ->
  In e (Graph.out g (Graph.source g e)) ->
  first = last \/ before (rev (components (scc_within p region))) first last.
Proof.
  intros Hready Hregion Hfirst Hlast Hsource Htarget Hedge.
  set (r := scc_within p region) in *.
  destruct (scc_within_indexes EV g p region)
    as [_ [_ [Hlength [Hat [Hids [Howner Horder]]]]]].
  change (length (component_ids r) = length (components r)) in Hlength.
  destruct (tarjan_combine_total_right _ _ first Hlength Hfirst) as [i Hi].
  destruct (tarjan_combine_total_right _ _ last Hlength Hlast) as [j Hj].
  assert (Hsi : Map.get EV (Graph.source g e) (comp_of r) = Some i).
  { apply Howner; exists first; split; [apply Hat; exact Hi|exact Hsource]. }
  assert (Htj : Map.get EV (Graph.target g e) (comp_of r) = Some j).
  { apply Howner; exists last; split; [apply Hat; exact Hj|exact Htarget]. }
  destruct (wto_scc_component_nodes EV g p region first Hready Hregion Hfirst) as [_ Hfirstin].
  destruct (wto_scc_component_nodes EV g p region last Hready Hregion Hlast) as [_ Hlastin].
  destruct (scc_reverse_topological EV g p e region Hready Hregion Hedge
    (Hfirstin _ Hsource) (Hlastin _ Htarget)) as [a [b [Ha [Hb Hle]]]].
  change (Map.get EV (Graph.source g e) (comp_of r) = Some a) in Ha.
  change (Map.get EV (Graph.target g e) (comp_of r) = Some b) in Hb.
  rewrite Hsi in Ha; inversion Ha; subst a.
  rewrite Htj in Hb; inversion Hb; subst b.
  destruct (Pos.eq_dec i j) as [Heq|Hne].
  - subst j; left; apply Hat in Hi, Hj; rewrite Hi in Hj; inversion Hj; reflexivity.
  - right.
    assert (Hbefore : before (rev (component_ids r)) i j).
    { apply Horder.
      - eapply in_combine_l; exact Hi.
      - eapply in_combine_l; exact Hj.
      - apply Pos.le_lteq in Hle; destruct Hle as [Hlt|Heq]; [exact Hlt|congruence]. }
    destruct (wto_combine_maps _ _ Hlength) as [Hfst Hsnd].
    assert (Hpair : before (rev (combine (component_ids r) (components r)))
      (i, first) (j, last)).
    { apply (wto_before_map_inverse fst).
      - rewrite map_rev, Hfst; apply NoDup_rev; exact Hids.
      - rewrite <- in_rev; exact Hi.
      - rewrite <- in_rev; exact Hj.
      - rewrite map_rev, Hfst; exact Hbefore. }
    pose proof (wto_before_map snd _ _ _ Hpair) as Hresult.
    rewrite map_rev, Hsnd in Hresult; exact Hresult.
Qed.

Lemma wto_flat_permutation {V E} (g : Graph.t V E) (f : list V -> wto V) cs :
  (forall c, In c cs -> wto_region g c (f c)) ->
  Permutation (wto_order (flat_map f cs)) (concat cs).
Proof.
  induction cs as [|c rest IH]; intro Hall; cbn [flat_map concat].
  - constructor.
  - rewrite wto_order_app; apply Permutation_app.
    + exact (wto_region_members _ _ _ (Hall c (or_introl eq_refl))).
    + apply IH; intros d Hd; apply Hall; right; exact Hd.
Qed.

Lemma wto_unfold_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) ranks recur region :
  ready EV g p -> incl region (Graph.nodes g) -> NoDup region ->
  (forall c, In c (components (scc_within p region)) ->
    wto_region g c (wto_component p ranks recur c)) ->
  wto_region g region (wto_unfold p ranks recur region).
Proof.
  intros Hready Hnodes Hnodup Hcomponent.
  set (cs := components (scc_within p region)) in *.
  set (f := wto_component p ranks recur) in *.
  assert (Hall : forall c, In c (rev cs) -> wto_region g c (f c)).
  { intros c Hc; apply Hcomponent; rewrite in_rev; exact Hc. }
  assert (Hnested : forall c, In c (rev cs) -> wto_nested (f c)).
  { intros c Hc; exact (wto_region_nested _ _ _ (Hall c Hc)). }
  change (wto_region g region (flat_map f (rev cs))); constructor.
  - apply wto_flat_nested; exact Hnested.
  - eapply Permutation_trans; [exact (wto_flat_permutation g f (rev cs) Hall)|].
    apply NoDup_Permutation.
    + eapply Permutation_NoDup; [apply Permutation_sym; apply tarjan_concat_rev|].
      exact (proj1 (scc_within_indexes EV g p region)).
    + exact Hnodup.
    + intro v; rewrite tarjan_concat_rev_in.
      apply scc_within_members; assumption.
  - intros e Hsource Htarget Hedge.
    apply (proj2 (scc_within_members EV g p region Hready Hnodes _)) in Hsource, Htarget.
    apply in_concat in Hsource, Htarget.
    destruct Hsource as [first [Hfirst Hsource]], Htarget as [last [Hlast Htarget]].
    assert (Hfirstrev : In first (rev cs)) by (rewrite <- in_rev; exact Hfirst).
    assert (Hlastrev : In last (rev cs)) by (rewrite <- in_rev; exact Hlast).
    destruct (wto_scc_edge_order EV g p region e first last Hready Hnodes
      Hfirst Hlast Hsource Htarget Hedge) as [Heq|Hbefore].
    + subst last; destruct (wto_region_edges _ _ _ (Hall first Hfirstrev)
        e Hsource Htarget Hedge) as [Hedgeorder|[st [Hannot Hhead]]].
      * left; eapply wto_flat_before_inside; eauto.
      * right; exists st; split; [|exact Hhead].
        eapply wto_flat_annotation; eauto.
    + left; eapply wto_flat_before_cross; [exact Hbefore| |].
      * eapply Permutation_in; [apply Permutation_sym;
          exact (wto_region_members _ _ _ (Hall first Hfirstrev))|exact Hsource].
      * eapply Permutation_in; [apply Permutation_sym;
          exact (wto_region_members _ _ _ (Hall last Hlastrev))|exact Htarget].
Qed.

Lemma wto_iter_region {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) ranks n :
  ready EV g p -> forall region, incl region (Graph.nodes g) -> NoDup region ->
  length region < Pos.to_nat n ->
  wto_region g region
    (Pos.iter (wto_unfold p ranks) (fun _ => []) n region).
Proof.
  intro Hready; induction n using Pos.peano_ind; intros region Hnodes Hnodup Hsize.
  - assert (Hempty : region = []) by (destruct region; cbn in Hsize; [reflexivity|lia]).
    subst region; change (wto_region g [] []); constructor;
      [constructor|constructor|intros e Hfalse; contradiction].
  - rewrite Pos.iter_succ; apply wto_unfold_region; [exact Hready|exact Hnodes|exact Hnodup|].
    intros c Hc.
    destruct (wto_scc_component_nodes EV g p region c Hready Hnodes Hc) as [Hcnodup Hcin].
    apply wto_component_region; [exact Hready| |exact Hcnodup|].
    + intros v Hv; apply Hnodes, Hcin; exact Hv.
    + intros h Hh; apply IHn.
      * intros v Hv; apply wto_remove_spec in Hv; apply Hnodes, Hcin; tauto.
      * apply NoDup_filter; exact Hcnodup.
      * pose proof (wto_remove_shorter EV h c Hh) as Hshort.
        pose proof (NoDup_incl_length Hcnodup Hcin) as Hlength.
        rewrite Pos2Nat.inj_succ in Hsize; lia.
Qed.

Lemma wto_reachable_order {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) :
  ready EV g p ->
  NoDup (rpo (dfs p FinSet.empty (Graph.entries g))) /\
  (forall v, In v (rpo (dfs p FinSet.empty (Graph.entries g))) <-> reachable g v).
Proof.
  intro Hready; pose proof Hready as [Hwf _].
  split.
  - apply dfs_rpo_nodup; [exact Hready|exact (entries_in Hwf)].
  - intro v; unfold rpo; rewrite <- in_rev.
    rewrite <- (reachable_dfs EV g p v Hready).
    destruct (dfs_exact EV g p v (Graph.entries g) FinSet.empty
      Hready (entries_in Hwf)) as [_ [_ [Hperm Hmem]]].
    rewrite <- Hmem; split; intro Hin; eapply Permutation_in;
      [apply Permutation_sym; exact Hperm|exact Hin|exact Hperm|exact Hin].
Qed.

Lemma wto_region_valid {V E} (g : Graph.t V E) region w :
  NoDup region -> (forall v, In v region <-> reachable g v) ->
  wto_region g region w -> wto_valid g w.
Proof.
  intros Hnodup Hreach [Hnested Hperm Hedges].
  assert (Hmembers : forall v, In v (wto_order w) <-> reachable g v).
  { intro v; rewrite <- Hreach; split; intro Hin; eapply Permutation_in;
      [exact Hperm|exact Hin|apply Permutation_sym; exact Hperm|exact Hin]. }
  unfold wto_valid; split.
  - pose proof (wto_nested_balance w Hnested 0 []) as Hbalance.
    rewrite app_nil_r in Hbalance; exact Hbalance.
  - split.
    + eapply Permutation_NoDup; [apply Permutation_sym; exact Hperm|exact Hnodup].
    + split; [exact Hmembers|].
      intros e Hsource Hedge; apply Hedges; [apply Hreach; exact Hsource| |exact Hedge].
      apply Hreach; eapply reachable_step; eauto.
Qed.

(** The recursive SCC producer directly satisfies the weak-order definition. *)
Theorem wto_of_valid {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> wto_valid g (wto_of p).
Proof.
  intro Hready; pose proof Hready as [Hwf _].
  destruct (wto_reachable_order EV g p Hready) as [Hnodup Hreach].
  unfold wto_of; apply (wto_region_valid g (rpo (dfs p FinSet.empty (Graph.entries g))));
    [exact Hnodup|exact Hreach|].
  apply wto_iter_region; [exact Hready| |exact Hnodup|].
  - intros v Hv; apply (reachable_in_nodes g v Hwf), Hreach; exact Hv.
  - rewrite SuccNat2Pos.id_succ; lia.
Qed.

(** The total internal producer inherits the direct construction proof. *)
Theorem wto_total_valid {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g) :
  ready EV g p -> wto_valid g (wto_total p).
Proof.
  apply wto_of_valid.
Qed.

(** * Agreement of intervals and nesting *)

Definition wto_scope {V} (w : wto V) (u v : V) : Prop :=
  exists st, In (u, st) (annotate [] w) /\ In v st.

Definition wto_span_scope {V} (spans : list (V * WtoSpan.t)) (u v : V) : Prop :=
  exists a b, In (u, a) spans /\ In (v, b) spans /\ head b = true /\
    Pos.to_nat (finish b) <= Pos.to_nat (pos a) <= Pos.to_nat (pos b).

Definition wto_span_before {V} (spans : list (V * WtoSpan.t)) (u v : V) : Prop :=
  exists a b, In (u, a) spans /\ In (v, b) spans /\
    Pos.to_nat (pos b) < Pos.to_nat (pos a).

(** The interval derivation follows the same closed segments as the token grammar. *)
Inductive wto_intervals {V} : wto V -> positive -> positive ->
    list (V * WtoSpan.t) -> Prop :=
  | WtoIntervalsNil : forall n, wto_intervals [] n n []
  | WtoIntervalsVertex : forall v tail lo mid spans,
      wto_intervals tail lo mid spans ->
      wto_intervals (WVertex v :: tail) lo (Pos.succ mid)
        ((v, WtoSpan.Make mid mid false) :: spans)
  | WtoIntervalsOpen : forall h body tail lo stop mid inside outside,
      wto_intervals tail lo stop outside ->
      wto_intervals body (Pos.succ stop) mid inside ->
      wto_intervals (WOpen h :: body ++ WClose :: tail) lo (Pos.succ mid)
        ((h, WtoSpan.Make mid stop true) :: inside ++ outside).

Lemma wto_scan_app {V} (first last : wto V) st :
  wto_scan (first ++ last) st = wto_scan first (wto_scan last st).
Proof.
  unfold wto_scan; apply fold_right_app.
Qed.

Lemma wto_scan_intervals {V} (w : wto V) :
  wto_nested w -> forall n cs acc, exists stop spans,
  wto_intervals w n stop spans /\
  wto_scan w (WtoScan.Make n cs acc) = WtoScan.Make stop cs (spans ++ acc).
Proof.
  intro Hnested; induction Hnested as [|v tail Htail IH|h body tail Hbody IHbody Htail IHtail];
    intros n cs acc.
  - exists n, []; split; [constructor|reflexivity].
  - destruct (IH n cs acc) as [stop [spans [Hinterval Hscan]]].
    exists (Pos.succ stop), ((v, WtoSpan.Make stop stop false) :: spans).
    split; [constructor; exact Hinterval|].
    change (wto_scan_step (WVertex v) (wto_scan tail (WtoScan.Make n cs acc)) =
      WtoScan.Make (Pos.succ stop) cs
        (((v, WtoSpan.Make stop stop false) :: spans) ++ acc)).
    rewrite Hscan; reflexivity.
  - destruct (IHtail n cs acc) as [stop [outside [Houtside Htailrun]]].
    destruct (IHbody (Pos.succ stop) (stop :: cs) (outside ++ acc))
      as [mid [inside [Hinside Hbodyrun]]].
    exists (Pos.succ mid), ((h, WtoSpan.Make mid stop true) :: inside ++ outside).
    split; [constructor; assumption|].
    change (wto_scan_step (WOpen h)
      (wto_scan (body ++ WClose :: tail) (WtoScan.Make n cs acc)) =
      WtoScan.Make (Pos.succ mid) cs
        (((h, WtoSpan.Make mid stop true) :: inside ++ outside) ++ acc)).
    rewrite wto_scan_app.
    change (wto_scan_step (WOpen h)
      (wto_scan body (wto_scan_step WClose (wto_scan tail (WtoScan.Make n cs acc)))) =
      WtoScan.Make (Pos.succ mid) cs
        (((h, WtoSpan.Make mid stop true) :: inside ++ outside) ++ acc)).
    rewrite Htailrun; cbn [wto_scan_step next closes rows]; rewrite Hbodyrun.
    cbn [wto_scan_step next closes rows hd tl]; rewrite app_assoc; reflexivity.
Qed.

Lemma wto_intervals_bounds {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans ->
  Pos.to_nat lo <= Pos.to_nat hi /\
  forall v s, In (v, s) spans ->
    Pos.to_nat lo <= Pos.to_nat (finish s) /\
    Pos.to_nat (finish s) <= Pos.to_nat (pos s) /\
    Pos.to_nat (pos s) < Pos.to_nat hi.
Proof.
  intro Hinterval; induction Hinterval as
    [n|v tail lo mid spans Htail [Hle Hbounds]|
     h body tail lo stop mid inside outside Htail [Hle Houtside] Hbody [Hmid Hinside]];
    rewrite ?Pos2Nat.inj_succ in *; split; try lia.
  - intros v s Hfalse; contradiction.
  - intros u s [Heq|Hin].
    + inversion Heq; subst; cbn; rewrite ?Pos2Nat.inj_succ; lia.
    + specialize (Hbounds u s Hin); rewrite ?Pos2Nat.inj_succ; lia.
  - intros u s [Heq|Hin].
    + inversion Heq; subst; cbn; rewrite ?Pos2Nat.inj_succ; lia.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * specialize (Hinside u s Hin); rewrite ?Pos2Nat.inj_succ in *; lia.
      * specialize (Houtside u s Hin); rewrite ?Pos2Nat.inj_succ; lia.
Qed.

Lemma wto_intervals_vertices {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans -> map fst spans = wto_vertices w.
Proof.
  intro Hinterval; induction Hinterval as
    [n|v tail lo mid spans Htail IH|
     h body tail lo stop mid inside outside Htail IHtail Hbody IHbody];
    cbn; rewrite ?map_app, ?wto_vertices_app; cbn; rewrite ?IH, ?IHtail, ?IHbody; reflexivity.
Qed.

Inductive wto_descending {V} : list (V * WtoSpan.t) -> Prop :=
  | WtoDescendingNil : wto_descending []
  | WtoDescendingCons : forall v s rest,
      (forall u t, In (u, t) rest -> Pos.to_nat (pos t) < Pos.to_nat (pos s)) ->
      wto_descending rest -> wto_descending ((v, s) :: rest).

Lemma wto_descending_app {V} (first last : list (V * WtoSpan.t)) :
  wto_descending first -> wto_descending last ->
  (forall u a v b, In (u, a) first -> In (v, b) last ->
    Pos.to_nat (pos b) < Pos.to_nat (pos a)) -> wto_descending (first ++ last).
Proof.
  intros Hfirst Hlast Hcross.
  induction Hfirst as [|v s rest Hless Hrest IH]; cbn; [exact Hlast|].
  constructor.
  - intros u t Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
      [exact (Hless u t Hin)|eapply Hcross; [left; reflexivity|exact Hin]].
  - apply IH; intros x a y b Hx Hy; apply (Hcross x a y b); [right; exact Hx|exact Hy].
Qed.

Lemma wto_intervals_descending {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans -> wto_descending spans.
Proof.
  intro Hinterval; induction Hinterval as
    [n|v tail lo mid spans Htail IH|
     h body tail lo stop mid inside outside Htail IHtail Hbody IHbody];
    constructor; try assumption.
  - intros u t Hin; pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) u t Hin);
      cbn; lia.
  - intros u t Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    + pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) u t Hin); cbn; lia.
    + pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) u t Hin).
      pose proof (proj1 (wto_intervals_bounds _ _ _ _ Hbody)); cbn.
      rewrite Pos2Nat.inj_succ in *; lia.
  - apply wto_descending_app; [exact IHbody|exact IHtail|].
    intros u a v b Hu Hv.
    pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) u a Hu).
    pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) v b Hv).
    rewrite Pos2Nat.inj_succ in *; lia.
Qed.

Lemma wto_span_before_correct {V} (spans : list (V * WtoSpan.t)) :
  wto_descending spans -> forall u v,
  before (map fst spans) u v <-> wto_span_before spans u v.
Proof.
  intro Hsorted; induction Hsorted as [|x s rest Hless Hsorted IH]; intros u v.
  - split; [intros [a [b [c Hfalse]]]; destruct a; discriminate|
      intros [a [b [Hfalse _]]]; contradiction].
  - cbn [map fst]; rewrite dfs_before_cons; unfold wto_span_before in *.
    split.
    + intros [[Heq Hin]|Hbefore].
      * subst u; apply in_map_iff in Hin; destruct Hin as [[y b] [Heq Hin]]; cbn in Heq.
        subst y; exists s, b; split; [left; reflexivity|].
        split; [right; exact Hin|exact (Hless v b Hin)].
      * apply IH in Hbefore; destruct Hbefore as [a [b [Ha [Hb Hlt]]]].
        exists a, b; split; [right; exact Ha|]; split; [right; exact Hb|exact Hlt].
    + intros [a [b [[Heqa|Ha] [[Heqb|Hb] Hlt]]]].
      * inversion Heqa; inversion Heqb; subst; lia.
      * inversion Heqa; subst; left; split; [reflexivity|].
        apply in_map with (f := @fst V WtoSpan.t) in Hb; exact Hb.
      * inversion Heqb; subst; specialize (Hless u a Ha); lia.
      * right; apply IH; exists a, b; auto.
Qed.

Lemma wto_scope_vertex {V} x (tail : wto V) u v :
  wto_scope (WVertex x :: tail) u v <-> wto_scope tail u v.
Proof.
  unfold wto_scope; cbn; split.
  - intros [st [[Heq|Hin] Hv]]; [inversion Heq; subst; contradiction|exists st; auto].
  - intros [st [Hin Hv]]; exists st; auto.
Qed.

Lemma wto_scope_component {V} h (body tail : wto V) u v :
  wto_nested body ->
  (wto_scope (WOpen h :: body ++ WClose :: tail) u v <->
   wto_scope body u v \/ wto_scope tail u v \/
   (v = h /\ (u = h \/ In u (wto_order body)))).
Proof.
  intro Hnested; unfold wto_scope; cbn [annotate].
  rewrite wto_nested_annotate by exact Hnested; cbn [annotate tl].
  split.
  - intros [st [[Heq|Hin] Hv]].
    + inversion Heq; subst; cbn in Hv; right; right; intuition congruence.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * apply in_map_iff in Hin; destruct Hin as [[x inner] [Heq Hin]].
        cbn in Heq; inversion Heq; subst x st.
        apply in_app_or in Hv; destruct Hv as [Hv|[Hv|Hfalse]].
        -- left; exists inner; auto.
        -- right; right; split; [symmetry; exact Hv|right].
           apply in_map with (f := @fst V (list V)) in Hin; exact Hin.
        -- contradiction.
      * right; left; exists st; auto.
  - intros [[st [Hin Hv]]|[[st [Hin Hv]]|[Heq [Hu|Hu]]]].
    + exists (st ++ [h]); split.
      * right; apply in_or_app; left; apply in_map_iff; exists (u, st); auto.
      * apply in_or_app; left; exact Hv.
    + exists st; split; [right; apply in_or_app; right; exact Hin|exact Hv].
    + subst u v; exists [h]; cbn; auto.
    + apply in_map_iff in Hu; destruct Hu as [[x st] [Hx Hin]]; cbn in Hx; subst x v.
      exists (st ++ [h]); split.
      * right; apply in_or_app; left; apply in_map_iff; exists (u, st); auto.
      * apply in_or_app; right; left; reflexivity.
Qed.

Lemma wto_span_scope_vertex {V} x n (rest : list (V * WtoSpan.t)) u v :
  (forall y s, In (y, s) rest -> Pos.to_nat (pos s) < Pos.to_nat n) ->
  (wto_span_scope ((x, WtoSpan.Make n n false) :: rest) u v <->
   wto_span_scope rest u v).
Proof.
  intro Hbound; unfold wto_span_scope; split.
  - intros [a [b [[Ha|Ha] [[Hb|Hb] [Hhead Hrange]]]]].
    + inversion Hb; subst; discriminate.
    + inversion Ha; subst; cbn in Hrange; specialize (Hbound v b Hb); lia.
    + inversion Hb; subst; discriminate.
    + exists a, b; auto.
  - intros [a [b [Ha [Hb Hrange]]]]; exists a, b; cbn; auto.
Qed.

Lemma wto_span_scope_component {V} h stop mid
    (inside outside : list (V * WtoSpan.t)) u v :
  Pos.to_nat stop <= Pos.to_nat mid ->
  (forall x s, In (x, s) inside ->
    Pos.to_nat stop < Pos.to_nat (finish s) /\
    Pos.to_nat (finish s) <= Pos.to_nat (pos s) < Pos.to_nat mid) ->
  (forall x s, In (x, s) outside ->
    Pos.to_nat (finish s) <= Pos.to_nat (pos s) < Pos.to_nat stop) ->
  (wto_span_scope ((h, WtoSpan.Make mid stop true) :: inside ++ outside) u v <->
   wto_span_scope inside u v \/ wto_span_scope outside u v \/
   (v = h /\ (u = h \/ In u (map fst inside)))).
Proof.
  intros Hstop Hinside Houtside; unfold wto_span_scope; split.
  - intros [a [b [[Ha|Ha] [[Hb|Hb] [Hhead Hrange]]]]].
    + inversion Ha; inversion Hb; subst; right; right; auto.
    + inversion Ha; subst; apply in_app_or in Hb; destruct Hb as [Hb|Hb].
      * specialize (Hinside v b Hb); cbn in Hrange; lia.
      * specialize (Houtside v b Hb); cbn in Hrange; lia.
    + inversion Hb; subst; apply in_app_or in Ha; destruct Ha as [Ha|Ha].
      * right; right; split; [reflexivity|right].
        apply in_map with (f := @fst V WtoSpan.t) in Ha; exact Ha.
      * specialize (Houtside u a Ha); cbn in Hrange; lia.
    + apply in_app_or in Ha, Hb; destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
      * left; exists a, b; auto.
      * specialize (Hinside u a Ha); specialize (Houtside v b Hb); lia.
      * specialize (Houtside u a Ha); specialize (Hinside v b Hb); lia.
      * right; left; exists a, b; auto.
  - intros [[a [b [Ha [Hb Hrange]]]]|[[a [b [Ha [Hb Hrange]]]]|[Heq [Hu|Hu]]]].
    + exists a, b; split; [right; apply in_or_app; left; exact Ha|].
      split; [right; apply in_or_app; left; exact Hb|exact Hrange].
    + exists a, b; split; [right; apply in_or_app; right; exact Ha|].
      split; [right; apply in_or_app; right; exact Hb|exact Hrange].
    + subst u v; exists (WtoSpan.Make mid stop true), (WtoSpan.Make mid stop true).
      cbn; repeat split; auto; lia.
    + subst v; apply in_map_iff in Hu; destruct Hu as [[x a] [Hx Ha]]; cbn in Hx; subst x.
      exists a, (WtoSpan.Make mid stop true); split.
      * right; apply in_or_app; left; exact Ha.
      * split; [left; reflexivity|]; cbn.
        specialize (Hinside u a Ha); split; [reflexivity|lia].
Qed.

Lemma wto_intervals_nested {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans -> wto_nested w.
Proof.
  intro Hinterval; induction Hinterval; constructor; assumption.
Qed.

Lemma wto_intervals_scope {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans -> forall u v,
    wto_scope w u v <-> wto_span_scope spans u v.
Proof.
  intro Hinterval; induction Hinterval as
    [n|x tail lo mid spans Htail IH|
     h body tail lo stop mid inside outside Htail IHtail Hbody IHbody]; intros u v.
  - unfold wto_scope, wto_span_scope; cbn; firstorder.
  - rewrite wto_scope_vertex, wto_span_scope_vertex; [apply IH|].
    intros y s Hin; exact (proj2 (proj2 (proj2 (wto_intervals_bounds _ _ _ _ Htail) y s Hin))).
  - rewrite wto_scope_component, wto_span_scope_component.
    + rewrite IHbody, IHtail, wto_order_vertices, <- (wto_intervals_vertices _ _ _ _ Hbody).
      reflexivity.
    + pose proof (proj1 (wto_intervals_bounds _ _ _ _ Hbody));
        rewrite Pos2Nat.inj_succ in *; lia.
    + intros x s Hin; pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) x s Hin).
      rewrite Pos2Nat.inj_succ in *; lia.
    + intros x s Hin; pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) x s Hin); lia.
    + eapply wto_intervals_nested; exact Hbody.
Qed.

Lemma wto_spans_correct {V} (w : wto V) : balanced_from 0 w = true ->
  map fst (wto_spans w) = wto_order w /\ wto_descending (wto_spans w) /\
  forall u v, wto_scope w u v <-> wto_span_scope (wto_spans w) u v.
Proof.
  intro Hbalanced.
  destruct (wto_scan_intervals w (balanced_nested w Hbalanced) 1%positive [] [])
    as [stop [spans [Hinterval Hscan]]].
  unfold wto_spans; rewrite Hscan; cbn [rows]; rewrite app_nil_r.
  split; [rewrite wto_order_vertices; eapply wto_intervals_vertices; exact Hinterval|].
  split; [eapply wto_intervals_descending; exact Hinterval|].
  eapply wto_intervals_scope; exact Hinterval.
Qed.

Lemma wto_span_map_correct {V} (EV : encoding V) spans :
  NoDup (map fst spans) -> forall v s,
  Map.get EV v (wto_span_map EV spans) = Some s <-> In (v, s) spans.
Proof.
  induction spans as [|[x t] rest IH]; intros Hnodup v s; cbn [wto_span_map fold_right fst snd].
  - rewrite Map.get_empty; cbn; split; [discriminate|contradiction].
  - inversion Hnodup as [|head tail Hfresh Htail]; subst.
    destruct (dfs_eq_dec EV v x) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same; split.
      * intro Heq; inversion Heq; left; reflexivity.
      * intros [Heq|Hin]; [inversion Heq; reflexivity|].
        exfalso; apply Hfresh; apply in_map with (f := @fst V WtoSpan.t) in Hin; exact Hin.
    + rewrite Map.get_set_other by exact Hne; rewrite IH by exact Htail.
      cbn; split; [auto|intros [Heq|Hin]; [inversion Heq; subst; contradiction|exact Hin]].
Qed.

Lemma wto_mem_add_false {V} (EV : encoding V) v h seen :
  FinSet.mem EV v (FinSet.add EV h seen) = false <->
  v <> h /\ FinSet.mem EV v seen = false.
Proof.
  rewrite dfs_mem_add; destruct (dfs_eq_dec EV v h); cbn; intuition discriminate.
Qed.

Lemma wto_unique_correct {V} (EV : encoding V) vs : forall seen,
  wto_unique EV seen vs = true <->
  NoDup vs /\ forall v, In v vs -> FinSet.mem EV v seen = false.
Proof.
  induction vs as [|h rest IH]; intro seen; cbn [wto_unique].
  - split; [intros _; split; [constructor|intros v Hfalse; contradiction]|reflexivity].
  - rewrite andb_true_iff, negb_true_iff, IH; split.
    + intros [Hfresh [Hnodup Hrest]]; split.
      * constructor; [intro Hin; specialize (Hrest h Hin); rewrite wto_mem_add_false in Hrest;
          tauto|exact Hnodup].
      * intros v [Heq|Hin]; [subst v; exact Hfresh|].
        specialize (Hrest v Hin); rewrite wto_mem_add_false in Hrest; tauto.
    + intros [Hnodup Hall]; inversion Hnodup as [|head tail Hfresh Htail]; subst.
      split; [apply Hall; left; reflexivity|]; split; [exact Htail|].
      intros v Hin; rewrite wto_mem_add_false; split.
      * intro Heq; subst v; contradiction.
      * apply Hall; right; exact Hin.
Qed.

Lemma wto_edge_b_correct {V} (EV : encoding V) w u v :
  balanced_from 0 w = true -> NoDup (wto_order w) ->
  (wto_edge_b EV (wto_span_map EV (wto_spans w)) u v = true <->
   before (wto_order w) u v \/ wto_scope w u v).
Proof.
  intros Hbalanced Hnodup.
  destruct (wto_spans_correct w Hbalanced) as [Hvertices [Hsorted Hscope]].
  assert (Hdistinct : NoDup (map fst (wto_spans w))) by (rewrite Hvertices; exact Hnodup).
  rewrite <- Hvertices, wto_span_before_correct by exact Hsorted.
  rewrite Hscope; unfold wto_edge_b; split.
  - destruct (Map.get EV u (wto_span_map EV (wto_spans w))) as [a|] eqn:Ha;
      [|discriminate].
    destruct (Map.get EV v (wto_span_map EV (wto_spans w))) as [b|] eqn:Hb;
      [|discriminate].
    apply wto_span_map_correct in Ha, Hb; try exact Hdistinct.
    rewrite orb_true_iff, !andb_true_iff, Pos.ltb_lt, !Pos.leb_le.
    rewrite Pos2Nat.inj_lt, !Pos2Nat.inj_le.
    intros [Hlt|[[Hhead Hlo] Hhi]]; [left; exists a, b; auto|right; exists a, b; auto].
  - intros [[a [b [Ha [Hb Hlt]]]]|[a [b [Ha [Hb [Hhead Hrange]]]]]];
      apply (proj2 (wto_span_map_correct EV _ Hdistinct _ _)) in Ha, Hb;
      rewrite Ha, Hb; apply orb_true_iff.
    + left; apply Pos.ltb_lt, Pos2Nat.inj_lt; exact Hlt.
    + right; rewrite !andb_true_iff, !Pos.leb_le, !Pos2Nat.inj_le; tauto.
Qed.

Lemma wto_pre_reachable {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) v : ready EV g p ->
  (In v (preorder (dfs p FinSet.empty (Graph.entries g))) <-> reachable g v).
Proof.
  intro Hready; pose proof Hready as [Hwf _].
  destruct (dfs_exact EV g p v (Graph.entries g) FinSet.empty Hready (entries_in Hwf))
    as [_ [_ [_ Hmem]]].
  rewrite Hmem; apply reachable_dfs; exact Hready.
Qed.

(** The interval checker decides the public Bourdoncle weak-order predicate. *)
Theorem check_wto_correct {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (w : wto V) :
  ready EV g p -> (check_wto p w = true <-> wto_valid g w).
Proof.
  intro Hready; pose proof Hready as [Hwf [_ Hp]]; unfold check_wto; cbn zeta.
  rewrite !andb_true_iff; split.
  - intros [[[[Hbalanced Hunique] Hreachable] Hcover] Hedges].
    destruct (wto_spans_correct w Hbalanced) as [Hvertices _].
    rewrite Hvertices in Hunique, Hreachable, Hedges.
    apply wto_unique_correct in Hunique; destruct Hunique as [Hnodup _].
    rewrite forallb_forall in Hreachable, Hcover, Hedges.
    assert (Hexact : forall v, In v (wto_order w) <-> reachable g v).
    { intro v; split.
      - intro Hin; apply (reachable_dfs EV g p v Hready), Hreachable; exact Hin.
      - intro Hreach; apply (proj2 (wto_pre_reachable EV g p v Hready)) in Hreach.
        specialize (Hcover v Hreach); apply Map.mem_spec in Hcover.
        destruct (Map.get EV v (wto_span_map EV (wto_spans w))) as [s|] eqn:Hget;
          [|contradiction].
        rewrite <- Hvertices; apply in_map_iff; exists (v, s); split; [reflexivity|].
        apply (proj1 (wto_span_map_correct EV _
          ltac:(rewrite Hvertices; exact Hnodup) v s)); exact Hget. }
    unfold wto_valid; split; [exact Hbalanced|]; split; [exact Hnodup|].
    split; [exact Hexact|]; intros e Hsource Hedge.
    specialize (Hedges _ (proj2 (Hexact _) Hsource)); rewrite forallb_forall in Hedges.
    rewrite (succ_agrees Hp _ (reachable_in_nodes g _ Hwf Hsource)) in Hedges.
    apply (proj1 (wto_edge_b_correct EV w _ _ Hbalanced Hnodup)), Hedges; exact Hedge.
  - intros [Hbalanced [Hnodup [Hexact Hedges]]].
    destruct (wto_spans_correct w Hbalanced) as [Hvertices _].
    rewrite Hvertices; split; [split; [split; [split|]|]|].
    + exact Hbalanced.
    + apply wto_unique_correct; split; [exact Hnodup|].
      intros v _; apply FinSet.mem_empty.
    + apply forallb_forall; intros v Hin; apply reachable_dfs; [exact Hready|].
      apply Hexact; exact Hin.
    + apply forallb_forall; intros v Hin; apply Map.mem_spec.
      apply (proj1 (wto_pre_reachable EV g p v Hready)), (proj2 (Hexact v)) in Hin.
      rewrite <- Hvertices in Hin; apply in_map_iff in Hin.
      destruct Hin as [[x s] [Heq Hspan]]; cbn in Heq; subst x.
      rewrite (proj2 (wto_span_map_correct EV _ ltac:(rewrite Hvertices; exact Hnodup) v s)
        Hspan); discriminate.
    + apply forallb_forall; intros v Hin; apply forallb_forall; intros e Hedge.
      assert (Hreach : reachable g v) by (apply Hexact; exact Hin).
      rewrite (succ_agrees Hp _ (reachable_in_nodes g _ Hwf Hreach)) in Hedge.
      pose proof (out_source Hwf v e Hedge) as Hsource; subst v.
      apply (proj2 (wto_edge_b_correct EV w _ _ Hbalanced Hnodup)), Hedges; assumption.
Qed.

Lemma wto_intervals_laminar {V} w lo hi (spans : list (V * WtoSpan.t)) :
  wto_intervals w lo hi spans -> forall h a v b,
  In (h, a) spans -> In (v, b) spans -> head a = true -> head b = true ->
  Pos.to_nat (pos b) <= Pos.to_nat (pos a) ->
  Pos.to_nat (finish a) <= Pos.to_nat (pos b) ->
  Pos.to_nat (finish a) <= Pos.to_nat (finish b).
Proof.
  intro Hinterval; induction Hinterval as
    [n|x tail lo mid spans Htail IH|
     x body tail lo stop mid inside outside Htail IHtail Hbody IHbody];
    intros h a v b Ha Hb Hheada Hheadb Horder Hcontains; [contradiction| |].
  - destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
    + inversion Ha; subst; discriminate.
    + inversion Ha; subst; discriminate.
    + inversion Hb; subst; discriminate.
    + eapply IH; eauto.
  - destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
    + inversion Ha; inversion Hb; subst; lia.
    + inversion Ha; subst; apply in_app_or in Hb; destruct Hb as [Hb|Hb].
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) v b Hb).
        cbn; rewrite Pos2Nat.inj_succ in *; lia.
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) v b Hb).
        cbn in Hcontains; lia.
    + inversion Hb; subst; apply in_app_or in Ha; destruct Ha as [Ha|Ha].
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) h a Ha).
        cbn in Horder; lia.
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) h a Ha).
        pose proof (proj1 (wto_intervals_bounds _ _ _ _ Hbody)).
        cbn in Horder; rewrite Pos2Nat.inj_succ in *; lia.
    + apply in_app_or in Ha, Hb; destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
      * eapply IHbody; eauto.
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) h a Ha).
        pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) v b Hb).
        rewrite Pos2Nat.inj_succ in *; lia.
      * pose proof (proj2 (wto_intervals_bounds _ _ _ _ Htail) h a Ha).
        pose proof (proj2 (wto_intervals_bounds _ _ _ _ Hbody) v b Hb).
        rewrite Pos2Nat.inj_succ in *; lia.
      * eapply IHtail; eauto.
Qed.

Lemma wto_rows_functional {V A} (spans : list (V * A)) :
  NoDup (map fst spans) -> forall v a b, In (v, a) spans -> In (v, b) spans -> a = b.
Proof.
  induction spans as [|[x s] rest IH]; intros Hnodup v a b Ha Hb; [contradiction|].
  inversion Hnodup as [|head tail Hfresh Htail]; subst.
  destruct Ha as [Ha|Ha], Hb as [Hb|Hb].
  - inversion Ha; inversion Hb; congruence.
  - inversion Ha; subst; exfalso; apply Hfresh.
    apply in_map with (f := @fst V A) in Hb; exact Hb.
  - inversion Hb; subst; exfalso; apply Hfresh.
    apply in_map with (f := @fst V A) in Ha; exact Ha.
  - eapply IH; eauto.
Qed.

Lemma wto_cycle_maximum {V} (spans : list (V * WtoSpan.t)) :
  NoDup (map fst spans) -> forall vs, vs <> [] ->
  (forall v, In v vs -> exists s, In (v, s) spans) ->
  exists h a, In h vs /\ In (h, a) spans /\ forall v b,
    In v vs -> In (v, b) spans -> Pos.to_nat (pos b) <= Pos.to_nat (pos a).
Proof.
  intros Hnodup vs; induction vs as [|x rest IH]; intros Hnonempty Hall; [contradiction|].
  destruct (Hall x (or_introl eq_refl)) as [s Hs].
  destruct rest as [|y rest].
  - exists x, s; split; [left; reflexivity|]; split; [exact Hs|].
    intros v b [Heq|Hfalse] Hb; [subst v|contradiction].
    pose proof (wto_rows_functional spans Hnodup x s b Hs Hb); subst; lia.
  - destruct (IH ltac:(discriminate) ltac:(intros v Hv; apply Hall; right; exact Hv))
      as [h [a [Hh [Ha Hmax]]]].
    destruct (le_dec (Pos.to_nat (pos s)) (Pos.to_nat (pos a))) as [Hle|Hgt].
    + exists h, a; split; [right; exact Hh|]; split; [exact Ha|].
      intros v b [Heq|Hin] Hb; [subst v|exact (Hmax v b Hin Hb)].
      pose proof (wto_rows_functional spans Hnodup x s b Hs Hb); subst; exact Hle.
    + exists x, s; split; [left; reflexivity|]; split; [exact Hs|].
      intros v b [Heq|Hin] Hb.
      * subst v; pose proof (wto_rows_functional spans Hnodup x s b Hs Hb); subst; lia.
      * specialize (Hmax v b Hin Hb); lia.
Qed.

Lemma wto_path_edges {V E} (g : Graph.t V E) u es z :
  path g u es z -> reachable g u -> forall e, In e es ->
  (Graph.source g e = u \/ In (Graph.source g e) (map (Graph.target g) es)) /\
  reachable g (Graph.source g e) /\ In e (Graph.out g (Graph.source g e)).
Proof.
  intro Hpath; induction Hpath as [v|a es z Hedge Hpath IH]; intros Hreach e Hin;
    [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst e; split; [left; reflexivity|auto].
  - destruct (IH (reachable_step a Hreach Hedge) e Hin) as [Hsource Hrest].
    split; [right; cbn; destruct Hsource as [Heq|Hlocal];
      [left; symmetry; exact Heq|right; exact Hlocal]
      |exact Hrest].
Qed.

Lemma wto_path_last {V E} (g : Graph.t V E) u es z :
  path g u es z -> es <> [] -> In z (map (Graph.target g) es).
Proof.
  intro Hpath; induction Hpath as [v|e es z Hedge Hpath IH]; intro Hnonempty;
    [contradiction|].
  destruct es as [|a es]; cbn; [inversion Hpath; left; reflexivity|right; apply IH; discriminate].
Qed.

Lemma wto_path_backwards {V E} (g : Graph.t V E) (P : V -> Prop) u es z :
  path g u es z ->
  (forall e, In e es -> P (Graph.target g e) -> P (Graph.source g e)) ->
  (forall y, In y (map (Graph.target g) es) -> P y -> P u) /\
  (P z -> forall y, y = u \/ In y (map (Graph.target g) es) -> P y).
Proof.
  intro Hpath; induction Hpath as [v|e es z Hedge Hpath IH]; intro Hstep.
  - split; [intros y Hfalse; contradiction|].
    intros Hv y [Heq|Hfalse]; [subst; exact Hv|contradiction].
  - destruct (IH ltac:(intros a Ha; apply Hstep; right; exact Ha)) as [Hhit Hall].
    split.
    + intros y [Heq|Hin] Hy.
      * subst y; apply Hstep; [left; reflexivity|exact Hy].
      * apply Hstep; [left; reflexivity|exact (Hhit y Hin Hy)].
    + intros Hz y [Heq|[Heq|Hin]].
      * subst y; apply Hstep; [left; reflexivity|apply Hall; [exact Hz|left; reflexivity]].
      * subst y; apply Hall; [exact Hz|left; reflexivity].
      * apply Hall; [exact Hz|right; exact Hin].
Qed.

Lemma wto_valid_indexed_edges {V E} (g : Graph.t V E) w lo hi spans :
  wto_valid g w -> wto_intervals w lo hi spans -> forall e a b,
  reachable g (Graph.source g e) -> In e (Graph.out g (Graph.source g e)) ->
  In (Graph.source g e, a) spans -> In (Graph.target g e, b) spans ->
  Pos.to_nat (pos b) < Pos.to_nat (pos a) \/
  (head b = true /\ Pos.to_nat (finish b) <= Pos.to_nat (pos a) <= Pos.to_nat (pos b)).
Proof.
  intros [_ [Hnodup [_ Hedges]]] Hinterval e a b Hreach Hout Ha Hb.
  assert (Hvertices : map fst spans = wto_order w).
  { rewrite wto_order_vertices; eapply wto_intervals_vertices; exact Hinterval. }
  assert (Hdistinct : NoDup (map fst spans)) by (rewrite Hvertices; exact Hnodup).
  destruct (Hedges e Hreach Hout) as [Hbefore|Hscope].
  - rewrite <- Hvertices in Hbefore.
    apply (proj1 (wto_span_before_correct spans
      (wto_intervals_descending _ _ _ _ Hinterval) _ _)) in Hbefore.
    destruct Hbefore as [a' [b' [Ha' [Hb' Hlt]]]].
    pose proof (wto_rows_functional spans Hdistinct _ a a' Ha Ha') as Heqa.
    pose proof (wto_rows_functional spans Hdistinct _ b b' Hb Hb') as Heqb.
    subst a' b'; left; exact Hlt.
  - apply (proj1 (wto_intervals_scope _ _ _ _ Hinterval _ _)) in Hscope.
    destruct Hscope as [a' [b' [Ha' [Hb' Hrange]]]].
    pose proof (wto_rows_functional spans Hdistinct _ a a' Ha Ha') as Heqa.
    pose proof (wto_rows_functional spans Hdistinct _ b b' Hb Hb') as Heqb.
    subst a' b'; right; exact Hrange.
Qed.

Lemma wto_cycle_interval_closure {V E} (g : Graph.t V E) w lo hi spans v es h a :
  wto_intervals w lo hi spans -> path g v es v ->
  In (h, a) spans -> head a = true -> In h (map (Graph.target g) es) ->
  (forall e, In e es -> In (Graph.source g e) (map (Graph.target g) es)) ->
  (forall x, In x (map (Graph.target g) es) -> exists b, In (x, b) spans) ->
  (forall e c b, In e es -> In (Graph.source g e, c) spans ->
    In (Graph.target g e, b) spans ->
    Pos.to_nat (pos b) < Pos.to_nat (pos c) \/
    (head b = true /\ Pos.to_nat (finish b) <= Pos.to_nat (pos c) <= Pos.to_nat (pos b))) ->
  (forall y b, In y (map (Graph.target g) es) -> In (y, b) spans ->
    Pos.to_nat (pos b) <= Pos.to_nat (pos a)) ->
  forall y, y = v \/ In y (map (Graph.target g) es) ->
    exists b, In (y, b) spans /\ Pos.to_nat (finish a) <= Pos.to_nat (pos b).
Proof.
  intros Hinterval Hpath Ha Hhead Hh Hsource Hmember Hedge Hmax.
  set (P := fun x => exists b, In (x, b) spans /\
    Pos.to_nat (finish a) <= Pos.to_nat (pos b)).
  assert (Hback : forall e, In e es -> P (Graph.target g e) -> P (Graph.source g e)).
  { intros e Hin [b [Hb Hlower]]; destruct (Hmember _ (Hsource e Hin)) as [c Hc].
    exists c; split; [exact Hc|].
    destruct (Hedge e c b Hin Hc Hb) as [Hforward|[Hheadb Hrange]]; [lia|].
    assert (Htarget : In (Graph.target g e) (map (Graph.target g) es)) by (apply in_map; exact Hin).
    pose proof (wto_intervals_laminar _ _ _ _ Hinterval h a (Graph.target g e) b
      Ha Hb Hhead Hheadb (Hmax _ b Htarget Hb) Hlower); lia. }
  destruct (wto_path_backwards g P _ _ _ Hpath Hback) as [Hhit Hall].
  assert (Ph : P h).
  { exists a; split; [exact Ha|].
    exact (proj1 (proj2 (proj2 (wto_intervals_bounds _ _ _ _ Hinterval) h a Ha))). }
  assert (Pv : P v) by (exact (Hhit h Hh Ph)).
  exact (Hall Pv).
Qed.

(** Every nonempty reachable cycle lies in a component headed by a vertex on that cycle. *)
Theorem wto_valid_cycles {V E} (g : Graph.t V E) (w : wto V) :
  wto_valid g w -> forall v es, reachable g v -> es <> [] -> path g v es v ->
  exists h, (h = v \/ In h (map (Graph.target g) es)) /\
    forall y st, (y = v \/ In y (map (Graph.target g) es)) ->
    In (y, st) (annotate [] w) -> In h st.
Proof.
  intros Hvalid v es Hv Hnonempty Hpath.
  pose proof Hvalid as [Hbalanced [Hnodup [Hreachable Hedges]]].
  destruct (wto_scan_intervals w (balanced_nested w Hbalanced) 1%positive [] [])
    as [stop [spans [Hinterval Hscan]]].
  assert (Hvertices : map fst spans = wto_order w).
  { rewrite wto_order_vertices; eapply wto_intervals_vertices; exact Hinterval. }
  assert (Hdistinct : NoDup (map fst spans)) by (rewrite Hvertices; exact Hnodup).
  assert (Hstart : In v (map (Graph.target g) es)) by (eapply wto_path_last; eauto).
  assert (Hsource : forall e, In e es -> In (Graph.source g e) (map (Graph.target g) es)).
  { intros e Hin; destruct (wto_path_edges g _ _ _ Hpath Hv e Hin) as [[Heq|Hlocal] _];
      [rewrite Heq; exact Hstart|exact Hlocal]. }
  assert (Hmember : forall x, In x (map (Graph.target g) es) -> exists s, In (x, s) spans).
  { intros x Hin; apply in_map_iff in Hin; destruct Hin as [e [Heq Hin]]; subst x.
    destruct (wto_path_edges g _ _ _ Hpath Hv e Hin) as [_ [Hreach Hedge]].
    assert (Htarget : reachable g (Graph.target g e)) by (eapply reachable_step; eauto).
    apply Hreachable in Htarget; rewrite <- Hvertices in Htarget.
    apply in_map_iff in Htarget; destruct Htarget as [[x s] [Heq Hs]]; cbn in Heq.
    subst x; exists s; exact Hs. }
  assert (Hedge : forall e c b, In e es -> In (Graph.source g e, c) spans ->
    In (Graph.target g e, b) spans ->
    Pos.to_nat (pos b) < Pos.to_nat (pos c) \/
    (head b = true /\ Pos.to_nat (finish b) <= Pos.to_nat (pos c) <= Pos.to_nat (pos b))).
  { intros e c b Hin Hc Hb.
    destruct (wto_path_edges g _ _ _ Hpath Hv e Hin) as [_ [Hreach Hout]].
    eapply wto_valid_indexed_edges; eauto. }
  destruct (wto_cycle_maximum spans Hdistinct (map (Graph.target g) es)
    ltac:(destruct es; [contradiction|discriminate]) Hmember)
    as [h [a [Hh [Ha Hmax]]]].
  assert (Hhead : head a = true).
  { apply in_map_iff in Hh; destruct Hh as [e [Heq Hin]].
    destruct (Hmember _ (Hsource e Hin)) as [b Hb].
    assert (Htarget : In (Graph.target g e, a) spans) by (rewrite Heq; exact Ha).
    destruct (Hedge e b a Hin Hb Htarget) as [Hlt|[Hhead Hrange]]; [|exact Hhead].
    specialize (Hmax _ b (Hsource e Hin) Hb); lia. }
  pose proof (wto_cycle_interval_closure g _ _ _ _ v es h a Hinterval Hpath
    Ha Hhead Hh Hsource Hmember Hedge Hmax) as Hall.
  exists h; split; [right; exact Hh|].
  intros y st Hcycle Hannot.
  destruct (Hall y Hcycle) as [b [Hb Hlower]].
  assert (Hy : In y (map (Graph.target g) es)).
  { destruct Hcycle as [Heq|Hy]; [subst y; exact Hstart|exact Hy]. }
  assert (Hscope : wto_scope w y h).
  { apply (proj2 (wto_intervals_scope _ _ _ _ Hinterval y h)).
    exists b, a; repeat split; try assumption; exact (Hmax y b Hy Hb). }
  destruct Hscope as [inner [Hinner Hcontains]].
  pose proof (wto_rows_functional (annotate [] w) Hnodup y inner st Hinner Hannot) as Heq.
  subst inner; exact Hcontains.
Qed.
