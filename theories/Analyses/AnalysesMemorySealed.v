(** * Sealed whole-memory construction

    Memoized reads install a stable incomplete phi before inspecting its predecessors.
    An explicit stack completes all operands before sealing a block and retains every phi.
    For example, an entry self-loop receives both a live entry operand and its own edge operand.
    Builds on: GraphPrepare, GraphDfs, FixpointIndex and AnalysesMemoryGraph. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Gaulois.Fixpoint Require Import FixpointIndex.
From Gaulois.Views Require Import ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph.
Import List.ListNotations.

(** * Preparation *)

Definition sealed_eq_dec {K} (EK : encoding K) (x y : K) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode EK x) (encode EK y)) as [Heq|Hne].
  - left; apply (encode_injective EK); exact Heq.
  - right; intro Heq; subst y; contradiction.
Defined.

Definition sealed_table {K V} (EK : encoding K) (keys : list K) (value : K -> V) :
    Map.t K V :=
  fold_right (fun k table => Map.set EK k (value k) table) Map.empty keys.

Lemma sealed_table_lookup {K V} (EK : encoding K) keys (value : K -> V) k v :
  Map.get EK k (sealed_table EK keys value) = Some v <-> In k keys /\ v = value k.
Proof.
  induction keys as [|a keys IH]; unfold sealed_table; cbn [fold_right In].
  - rewrite Map.get_empty; split; [discriminate|tauto].
  - destruct (sealed_eq_dec EK k a) as [->|Hne].
    + rewrite Map.get_set_same; split.
      * intro Heq; inversion Heq; split; [left; reflexivity|reflexivity].
      * intros [_ ->]; reflexivity.
    + rewrite Map.get_set_other by exact Hne; rewrite IH; cbn; intuition congruence.
Qed.

(** * Ordered edge materialization *)

(** Each processed edge stores one indexed input per occurrence and its final version. *)
Record sealed_edge (N E : Type) : Type := SealedEdge {
  sealed_inputs : Map.t nat (memory_version N E);
  sealed_output : memory_version N E;
  sealed_definitions : list (memory_version N E)
}.

Arguments SealedEdge {N E}.
Arguments sealed_inputs {N E}.
Arguments sealed_output {N E}.
Arguments sealed_definitions {N E}.

Fixpoint sealed_scan {N E T} (e : E) (start : nat) (xs : list (memory_effect T))
    (input : memory_version N E) : sealed_edge N E :=
  match xs with
  | [] => SealedEdge Map.empty input []
  | a :: rest =>
    let tail := sealed_scan e (S start) rest (memory_after e start a input) in
    SealedEdge (Map.set nat_encoding start input (sealed_inputs tail)) (sealed_output tail)
      (if effect_is_def a then MemoryDef e start :: sealed_definitions tail
       else sealed_definitions tail)
  end.

Lemma sealed_scan_output {N E T} (e : E) start (xs : list (memory_effect T))
    (input : memory_version N E) :
  sealed_output (sealed_scan e start xs input) = memory_last_defs e start xs input.
Proof.
  revert start input; induction xs as [|a xs IH]; intros start input;
    cbn [sealed_scan sealed_output memory_last_defs]; [reflexivity|apply IH].
Qed.

Lemma sealed_scan_lookup {N E T} (e : E) start (xs : list (memory_effect T))
    (input : memory_version N E) k a :
  nth_error xs k = Some a ->
  Map.get nat_encoding (start + k) (sealed_inputs (sealed_scan e start xs input)) =
    Some (memory_last_defs e start (firstn k xs) input).
Proof.
  revert start input k a; induction xs as [|head xs IH]; intros start input [|k] a Hnth;
    cbn [nth_error] in Hnth; try discriminate.
  - cbn [sealed_scan sealed_inputs firstn memory_last_defs]; rewrite Nat.add_0_r.
    apply Map.get_set_same.
  - cbn [sealed_scan sealed_inputs firstn memory_last_defs].
    rewrite Map.get_set_other by lia.
    replace (start + S k) with (S start + k) by lia; eapply IH; exact Hnth.
Qed.

Lemma sealed_scan_domain {N E T} (e : E) start (xs : list (memory_effect T))
    (input : memory_version N E) j v :
  Map.get nat_encoding j (sealed_inputs (sealed_scan e start xs input)) = Some v ->
  exists k a, j = start + k /\ nth_error xs k = Some a.
Proof.
  revert start input; induction xs as [|a xs IH]; intros start input Hget.
  - cbn [sealed_scan sealed_inputs] in Hget; rewrite Map.get_empty in Hget; discriminate.
  - cbn [sealed_scan sealed_inputs] in Hget.
    destruct (Nat.eq_dec j start) as [->|Hne].
    + exists 0, a; split; [lia|reflexivity].
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (IH (S start) (memory_after e start a input) Hget) as [k [b [Hj Hnth]]].
      exists (S k), b; split; [lia|exact Hnth].
Qed.

Lemma sealed_scan_definitions {N E T} (e : E) start (xs : list (memory_effect T))
    (input : memory_version N E) v :
  In v (sealed_definitions (sealed_scan e start xs input)) <->
  exists k a, nth_error xs k = Some a /\ effect_is_def a = true /\
    v = MemoryDef e (start + k).
Proof.
  revert start input; induction xs as [|a xs IH]; intros start input.
  - cbn [sealed_scan sealed_definitions In]; split; [contradiction|].
    intros [[|k] [a [Hnth _]]]; discriminate.
  - cbn [sealed_scan sealed_definitions]; destruct (effect_is_def a) eqn:Hdef.
    + cbn [In]; rewrite IH; split.
      * intros [Heq|[k [b [Hnth [Hb Hv]]]]].
        -- exists 0, a; split; [reflexivity|split; [exact Hdef|]].
           rewrite Nat.add_0_r; symmetry; exact Heq.
        -- exists (S k), b; split; [exact Hnth|split; [exact Hb|]].
           replace (start + S k) with (S start + k) by lia; exact Hv.
      * intros [[|k] [b [Hnth [Hb Hv]]]].
        -- cbn [nth_error] in Hnth; inversion Hnth; subst b.
           left; rewrite Nat.add_0_r in Hv; symmetry; exact Hv.
        -- right; exists k, b; split; [exact Hnth|split; [exact Hb|]].
           replace (S start + k) with (start + S k) by lia; exact Hv.
    + rewrite IH; split.
      * intros [k [b [Hnth [Hb Hv]]]]; exists (S k), b.
        split; [exact Hnth|split; [exact Hb|]].
        replace (start + S k) with (S start + k) by lia; exact Hv.
      * intros [[|k] [b [Hnth [Hb Hv]]]].
        -- cbn [nth_error] in Hnth; inversion Hnth; subst b; congruence.
        -- exists k, b; split; [exact Hnth|split; [exact Hb|]].
           replace (S start + k) with (start + S k) by lia; exact Hv.
Qed.

Lemma sealed_prefix_flow {N E T} (mg : memory_graph N E) (e : E) start
    (xs : list (memory_effect T)) input :
  (forall k a, nth_error xs k = Some a ->
    memory_before mg e (start + k) = Some (memory_last_defs e start (firstn k xs) input)) ->
  memory_edge_flow mg e start xs input (memory_last_defs e start xs input).
Proof.
  revert start input; induction xs as [|a xs IH]; intros start input Hlookup.
  - constructor.
  - cbn [memory_last_defs]; constructor.
    + specialize (Hlookup 0 a eq_refl); rewrite Nat.add_0_r in Hlookup; exact Hlookup.
    + apply IH; intros k b Hnth.
      specialize (Hlookup (S k) b Hnth).
      replace (start + S k) with (S start + k) in Hlookup by lia; exact Hlookup.
Qed.

Lemma sealed_table_hit {K V} (EK : encoding K) keys (value : K -> V) k :
  In k keys -> Map.get EK k (sealed_table EK keys value) = Some (value k).
Proof.
  intro Hin; apply sealed_table_lookup; split; [exact Hin|reflexivity].
Qed.

Lemma sealed_table_miss {K V} (EK : encoding K) keys (value : K -> V) k :
  ~ In k keys -> Map.get EK k (sealed_table EK keys value) = None.
Proof.
  intro Hnot; destruct (Map.get EK k (sealed_table EK keys value)) as [v|] eqn:Hget.
  - apply sealed_table_lookup in Hget; tauto.
  - reflexivity.
Qed.

Lemma sealed_some_nodup {K} (xs : list K) : NoDup xs -> NoDup (map Some xs).
Proof.
  intro Hnodup; induction Hnodup as [|x xs Hfresh Hnodup IH]; cbn [map].
  - constructor.
  - constructor; [|exact IH].
    rewrite in_map_iff; intros [y [Heq Hin]]; inversion Heq; subst y; contradiction.
Qed.

Definition sealed_cfg {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
    Graph.t N E :=
  let adjacency := sealed_table EN (Graph.nodes g)
    (fun n => distinct_unknowns EE (Graph.out g n)) in
  {| Graph.entries := Graph.entries g;
     Graph.nodes := Graph.nodes g;
     Graph.out := index_edges EN adjacency;
     Graph.source := Graph.source g;
     Graph.target := Graph.target g |}.

Lemma sealed_cfg_out {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) n :
  In n (Graph.nodes g) ->
  Graph.out (sealed_cfg EN EE g) n = distinct_unknowns EE (Graph.out g n).
Proof.
  intro Hin; unfold sealed_cfg; cbn [Graph.out]; unfold index_edges.
  rewrite sealed_table_hit by exact Hin.
  reflexivity.
Qed.

Lemma sealed_cfg_edge {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) n e :
  In e (Graph.out (sealed_cfg EN EE g) n) <->
  In n (Graph.nodes g) /\ In e (Graph.out g n).
Proof.
  destruct (in_dec (sealed_eq_dec EN) n (Graph.nodes g)) as [Hin|Hnot].
  - rewrite sealed_cfg_out by exact Hin; rewrite distinct_unknowns_spec; tauto.
  - unfold sealed_cfg; cbn [Graph.out]; unfold index_edges.
    rewrite sealed_table_miss by exact Hnot.
    cbn; tauto.
Qed.

Lemma sealed_cfg_ready {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> ready EN (sealed_cfg EN EE g) (prepare EN (sealed_cfg EN EE g)).
Proof.
  intro Hwf; apply prepare_ready.
  - constructor.
    + exact (nodes_nodup Hwf).
    + exact (entries_in Hwf).
    + intros n e He; apply sealed_cfg_edge in He; exact (out_source Hwf n e (proj2 He)).
    + intros n e Hn He; apply sealed_cfg_edge in He.
      exact (out_target_in Hwf n e Hn (proj2 He)).
  - intro n; destruct (in_dec (sealed_eq_dec EN) n (Graph.nodes g)) as [Hin|Hnot].
    + rewrite sealed_cfg_out by exact Hin; apply distinct_unknowns_nodup.
    + unfold sealed_cfg; cbn [Graph.out]; unfold index_edges.
      rewrite sealed_table_miss by exact Hnot; constructor.
Qed.

Lemma sealed_cfg_reachable {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) n :
  graph_wf g -> (reachable (sealed_cfg EN EE g) n <-> reachable g n).
Proof.
  intro Hwf; split; intro Hreach; induction Hreach as [n Hentry|e Hreach IH Hedge].
  - constructor; exact Hentry.
  - apply (@reachable_step N E g e); [exact IH|].
    apply sealed_cfg_edge in Hedge; exact (proj2 Hedge).
  - constructor; exact Hentry.
  - apply (@reachable_step N E (sealed_cfg EN EE g) e); [exact IH|].
    apply sealed_cfg_edge; split; [|exact Hedge].
    apply (reachable_in_nodes g _ Hwf); exact Hreach.
Qed.

(** The prepared domain and slots preserve exact edges and one virtual slot at every entry. *)
Record sealed_index (N E : Type) : Type := SealedIndex {
  sealed_nodes : list N;
  sealed_slots : N -> list (option E)
}.

Arguments SealedIndex {N E}.
Arguments sealed_nodes {N E}.
Arguments sealed_slots {N E}.

(** Slot membership fixes the full operand domain before any placeholder is allocated. *)
Record sealed_index_laws {N E} (g : Graph.t N E) (ix : sealed_index N E) : Prop := {
  sealed_nodes_nodup : NoDup (sealed_nodes ix);
  sealed_nodes_exact : forall n, In n (sealed_nodes ix) <-> reachable g n;
  sealed_slots_nodup : forall n, NoDup (sealed_slots ix n);
  sealed_slots_exact : forall n k, In k (sealed_slots ix n) <->
    reachable g n /\
    match k with
    | None => In n (Graph.entries g)
    | Some e => In e (Graph.out g (Graph.source g e)) /\
        reachable g (Graph.source g e) /\ Graph.target g e = n
    end
}.

Arguments sealed_nodes_nodup {N E g ix}.
Arguments sealed_nodes_exact {N E g ix}.
Arguments sealed_slots_nodup {N E g ix}.
Arguments sealed_slots_exact {N E g ix}.

Definition sealed_prepare {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
    sealed_index N E :=
  let normalized := sealed_cfg EN EE g in
  let adjacency := prepare EN normalized in
  let reached := visited (dfs adjacency FinSet.empty (Graph.entries g)) in
  let nodes := filter (fun n => FinSet.mem EN n reached) (Graph.nodes g) in
  let entries := FinSet.of_list EN (Graph.entries g) in
  let slots := sealed_table EN nodes (fun n =>
    (if FinSet.mem EN n entries then [None] else []) ++
    map Some (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
      (pred_edges adjacency n))) in
  SealedIndex nodes (index_edges EN slots).

Lemma sealed_prepare_laws {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E) :
  graph_wf g -> sealed_index_laws g (sealed_prepare EN EE g).
Proof.
  intro Hwf.
  set (normalized := sealed_cfg EN EE g).
  set (adjacency := prepare EN normalized).
  set (reached := visited (dfs adjacency FinSet.empty (Graph.entries g))).
  set (nodes := filter (fun n => FinSet.mem EN n reached) (Graph.nodes g)).
  assert (Hready : ready EN normalized adjacency) by (apply sealed_cfg_ready; exact Hwf).
  assert (Hreached : forall n, FinSet.mem EN n reached = true <-> reachable g n).
  { intro n; change (FinSet.mem EN n
      (visited (dfs adjacency FinSet.empty (Graph.entries normalized))) = true <->
      reachable g n).
    rewrite (reachable_dfs EN normalized adjacency n Hready).
    apply sealed_cfg_reachable; exact Hwf. }
  assert (Hnodes : forall n, In n nodes <-> reachable g n).
  { intro n; unfold nodes; rewrite filter_In, Hreached; split; [tauto|].
    intro Hr; split; [apply (reachable_in_nodes g n Hwf Hr)|exact Hr]. }
  assert (Hpred : forall n e, reachable g n ->
    (In e (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
      (pred_edges adjacency n)) <->
    In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
      Graph.target g e = n)).
  { intros n e Hn; rewrite filter_In, Hreached.
    rewrite (pred_agrees (proj2 (proj2 Hready)) n e).
    - split.
      + intros [[u [Hu [He Htarget]]] Hsource]; apply sealed_cfg_edge in He.
        split; [rewrite (out_source Hwf u e (proj2 He)); exact (proj2 He)|].
        split; [exact Hsource|exact Htarget].
      + intros [He [Hr Htarget]]; split; [|exact Hr].
        exists (Graph.source g e); split.
        * apply (reachable_in_nodes g _ Hwf Hr).
        * split; [apply sealed_cfg_edge; split; [apply (reachable_in_nodes g _ Hwf Hr)|
            exact He]|exact Htarget].
    - apply (reachable_in_nodes g n Hwf Hn). }
  change (sealed_index_laws g
    (SealedIndex nodes (index_edges EN (sealed_table EN nodes (fun n =>
      (if FinSet.mem EN n (FinSet.of_list EN (Graph.entries g)) then [None] else []) ++
      map Some (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
        (pred_edges adjacency n))))))).
  constructor; cbn [sealed_nodes sealed_slots].
  - apply NoDup_filter; exact (nodes_nodup Hwf).
  - exact Hnodes.
  - intro n; destruct (in_dec (sealed_eq_dec EN) n nodes) as [Hin|Hnot].
    + unfold index_edges; rewrite sealed_table_hit by exact Hin.
      apply nodup_app_disjoint.
      * destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.entries g))); repeat constructor;
          cbn; tauto.
      * apply sealed_some_nodup.
        apply NoDup_filter; apply (pred_edges_nodup EN normalized adjacency n Hready).
      * intros k Hk; destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.entries g)))
          in Hk; cbn in Hk; [|contradiction].
        destruct Hk as [<-|Hfalse]; [|contradiction].
        rewrite in_map_iff; intros [e [Heq _]]; discriminate.
    + unfold index_edges; rewrite sealed_table_miss by exact Hnot; constructor.
  - intros n k; destruct (in_dec (sealed_eq_dec EN) n nodes) as [Hin|Hnot].
    + unfold index_edges; rewrite sealed_table_hit by exact Hin.
      rewrite in_app_iff; specialize (Hnodes n); destruct k as [e|].
      * assert (Hsome : In (Some e)
          (map Some (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
            (pred_edges adjacency n))) <->
          In e (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
            (pred_edges adjacency n))).
        { rewrite in_map_iff; split.
          - intros [a [Heq Ha]]; inversion Heq; subst a; exact Ha.
          - intro He; exists e; split; [reflexivity|exact He]. }
        rewrite Hsome, Hpred by tauto.
        destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.entries g))); cbn [In];
          intuition congruence.
      * assert (Hnone : ~ In None
          (map Some (filter (fun e => FinSet.mem EN (Graph.source g e) reached)
            (pred_edges adjacency n)))).
        { rewrite in_map_iff; intros [e [Heq _]]; discriminate. }
        rewrite <- (FinSet.of_list_spec EN n (Graph.entries g)).
        destruct (FinSet.mem EN n (FinSet.of_list EN (Graph.entries g))); cbn [In];
          intuition congruence.
    + unfold index_edges; rewrite sealed_table_miss by exact Hnot; cbn.
      rewrite Hnodes in Hnot; tauto.
Qed.

(** * Memoized reads and sealing *)

(** A memo member represents the stable version [MemoryPhi n], even while it is incomplete. *)
Record sealed_store (N E : Type) : Type := SealedStore {
  sealed_memo : FinSet.t N;
  sealed_closed : FinSet.t N;
  sealed_virtual : FinSet.t N;
  sealed_edge_index : Map.t E (sealed_edge N E)
}.

Arguments SealedStore {N E}.
Arguments sealed_memo {N E}.
Arguments sealed_closed {N E}.
Arguments sealed_virtual {N E}.
Arguments sealed_edge_index {N E}.

(** Frames retain the unprocessed suffix of the once-prepared operand slots. *)
Record sealed_machine (N E : Type) : Type := SealedMachine {
  sealed_data : sealed_store N E;
  sealed_roots : list N;
  sealed_stack : list (N * list (option E))
}.

Arguments SealedMachine {N E}.
Arguments sealed_data {N E}.
Arguments sealed_roots {N E}.
Arguments sealed_stack {N E}.

Definition sealed_open {N E} (EN : encoding N) n (st : sealed_store N E) :=
  SealedStore (FinSet.add EN n (sealed_memo st)) (sealed_closed st) (sealed_virtual st)
    (sealed_edge_index st).

Definition sealed_close {N E} (EN : encoding N) n (st : sealed_store N E) :=
  SealedStore (sealed_memo st) (FinSet.add EN n (sealed_closed st)) (sealed_virtual st)
    (sealed_edge_index st).

Definition sealed_enter {N E} (EN : encoding N) n (st : sealed_store N E) :=
  SealedStore (sealed_memo st) (sealed_closed st) (FinSet.add EN n (sealed_virtual st))
    (sealed_edge_index st).

Definition sealed_record {N E T} (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) e (st : sealed_store N E) :=
  SealedStore (sealed_memo st) (sealed_closed st) (sealed_virtual st)
    (Map.set EE e (sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e)))
      (sealed_edge_index st)).

Definition sealed_initial {N E} (ix : sealed_index N E) : sealed_machine N E :=
  SealedMachine (SealedStore FinSet.empty FinSet.empty FinSet.empty Map.empty)
    (sealed_nodes ix) [].

(** A recursive read installs its memo and frame before any predecessor read can revisit it. *)
Definition sealed_step {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E)
    (machine : sealed_machine N E) : sealed_machine N E :=
  let st := sealed_data machine in
  let roots := sealed_roots machine in
  match sealed_stack machine with
  | [] =>
    match roots with
    | [] => machine
    | n :: rest =>
      if FinSet.mem EN n (sealed_memo st) then SealedMachine st rest []
      else SealedMachine (sealed_open EN n st) rest [(n, sealed_slots ix n)]
    end
  | (n, []) :: stack =>
    SealedMachine (sealed_close EN n st) roots stack
  | (n, None :: keys) :: stack =>
    SealedMachine (sealed_enter EN n st) roots ((n, keys) :: stack)
  | (n, Some e :: keys) :: stack =>
    if FinSet.mem EN (Graph.source g e) (sealed_memo st) then
      SealedMachine (sealed_record EE g effects e st) roots ((n, keys) :: stack)
    else
      SealedMachine (sealed_open EN (Graph.source g e) st) roots
        ((Graph.source g e, sealed_slots ix (Graph.source g e)) ::
          (n, Some e :: keys) :: stack)
  end.

Definition sealed_filled {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (st : sealed_store N E) n (key : option E) : Prop :=
  match key with
  | None => FinSet.mem EN n (sealed_virtual st) = true
  | Some e => Graph.target g e = n /\ exists data,
      Map.get EE e (sealed_edge_index st) = Some data
  end.

(** Closed blocks have every prepared slot, including their virtual entry when present. *)
Definition sealed_complete {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (ix : sealed_index N E) (st : sealed_store N E) n : Prop :=
  forall key, In key (sealed_slots ix n) -> sealed_filled EN EE g st n key.

Definition sealed_frame {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (ix : sealed_index N E) (st : sealed_store N E) (frame : N * list (option E)) : Prop :=
  let '(n, rest) := frame in
  FinSet.mem EN n (sealed_memo st) = true /\ reachable g n /\
  FinSet.mem EN n (sealed_closed st) = false /\
  exists prefix, sealed_slots ix n = prefix ++ rest /\
    forall key, In key prefix -> sealed_filled EN EE g st n key.

(** Stored memo values, completed operands and ordered edges agree with their prepared domains. *)
Record sealed_store_laws {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E)
    (st : sealed_store N E) : Prop := {
  sealed_memo_wf : FinSet.wf EN (sealed_memo st);
  sealed_closed_wf : FinSet.wf EN (sealed_closed st);
  sealed_virtual_wf : FinSet.wf EN (sealed_virtual st);
  sealed_edge_wf : Map.wf EE (sealed_edge_index st);
  sealed_memo_reachable : forall n,
    FinSet.mem EN n (sealed_memo st) = true -> reachable g n;
  sealed_closed_complete : forall n,
    FinSet.mem EN n (sealed_closed st) = true ->
    FinSet.mem EN n (sealed_memo st) = true /\ sealed_complete EN EE g ix st n;
  sealed_virtual_entry : forall n,
    FinSet.mem EN n (sealed_virtual st) = true ->
    In n (Graph.entries g) /\ FinSet.mem EN n (sealed_memo st) = true;
  sealed_record_agrees : forall e data,
    Map.get EE e (sealed_edge_index st) = Some data ->
    In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e) /\
    FinSet.mem EN (Graph.source g e) (sealed_memo st) = true /\
    FinSet.mem EN (Graph.target g e) (sealed_memo st) = true /\
    data = sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e))
}.

Arguments sealed_memo_wf {N E T EN EE g effects ix st}.
Arguments sealed_closed_wf {N E T EN EE g effects ix st}.
Arguments sealed_virtual_wf {N E T EN EE g effects ix st}.
Arguments sealed_edge_wf {N E T EN EE g effects ix st}.
Arguments sealed_memo_reachable {N E T EN EE g effects ix st}.
Arguments sealed_closed_complete {N E T EN EE g effects ix st}.
Arguments sealed_virtual_entry {N E T EN EE g effects ix st}.
Arguments sealed_record_agrees {N E T EN EE g effects ix st}.

(** Pending frames account for every allocated but unsealed read; roots cover all other reads. *)
Record sealed_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E)
    (machine : sealed_machine N E) : Prop := {
  sealed_store_valid : sealed_store_laws EN EE g effects ix (sealed_data machine);
  sealed_frames : Forall (sealed_frame EN EE g ix (sealed_data machine))
    (sealed_stack machine);
  sealed_frame_owners : NoDup (map fst (sealed_stack machine));
  sealed_pending_reads : forall n,
    FinSet.mem EN n (sealed_memo (sealed_data machine)) = true ->
    FinSet.mem EN n (sealed_closed (sealed_data machine)) = true \/
    In n (map fst (sealed_stack machine));
  sealed_unread_roots : forall n, reachable g n ->
    FinSet.mem EN n (sealed_memo (sealed_data machine)) = false -> In n (sealed_roots machine);
  sealed_roots_reachable : forall n, In n (sealed_roots machine) -> reachable g n;
  sealed_fresh_slots : forall n rest, In (n, rest) (sealed_stack machine) ->
    forall key, In key rest -> ~ sealed_filled EN EE g (sealed_data machine) n key
}.

Arguments sealed_store_valid {N E T EN EE g effects ix machine}.
Arguments sealed_frames {N E T EN EE g effects ix machine}.
Arguments sealed_frame_owners {N E T EN EE g effects ix machine}.
Arguments sealed_pending_reads {N E T EN EE g effects ix machine}.
Arguments sealed_unread_roots {N E T EN EE g effects ix machine}.
Arguments sealed_roots_reachable {N E T EN EE g effects ix machine}.
Arguments sealed_fresh_slots {N E T EN EE g effects ix machine}.

Lemma sealed_mem_same {K} (EK : encoding K) n set :
  FinSet.mem EK n (FinSet.add EK n set) = true.
Proof.
  apply FinSet.mem_add; left; reflexivity.
Qed.

Lemma sealed_mem_other {K} (EK : encoding K) n m set :
  n <> m -> FinSet.mem EK n (FinSet.add EK m set) = FinSet.mem EK n set.
Proof.
  intro Hne; destruct (FinSet.mem EK n (FinSet.add EK m set)) eqn:Hnew;
    destruct (FinSet.mem EK n set) eqn:Hold; try reflexivity.
  - apply FinSet.mem_add in Hnew; destruct Hnew as [Heq|Htrue]; congruence.
  - assert (Htrue : FinSet.mem EK n (FinSet.add EK m set) = true).
    { apply FinSet.mem_add; right; exact Hold. }
    congruence.
Qed.

Definition sealed_extends {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (st next : sealed_store N E) : Prop :=
  (forall n, FinSet.mem EN n (sealed_memo st) = true ->
    FinSet.mem EN n (sealed_memo next) = true) /\
  forall n key, sealed_filled EN EE g st n key -> sealed_filled EN EE g next n key.

Lemma sealed_open_extends {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    n (st : sealed_store N E) : sealed_extends EN EE g st (sealed_open EN n st).
Proof.
  split.
  - intros m Hm; apply FinSet.mem_add; right; exact Hm.
  - intros m [e|] Hfilled; exact Hfilled.
Qed.

Lemma sealed_enter_extends {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    n (st : sealed_store N E) : sealed_extends EN EE g st (sealed_enter EN n st).
Proof.
  split; [intros m Hm; exact Hm|].
  intros m [e|] Hfilled; [exact Hfilled|].
  apply FinSet.mem_add; right; exact Hfilled.
Qed.

Lemma sealed_record_extends {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) e (st : sealed_store N E) :
  sealed_extends EN EE g st (sealed_record EE g effects e st).
Proof.
  split; [intros m Hm; exact Hm|].
  intros n [a|] Hfilled; [|exact Hfilled].
  destruct Hfilled as [Htarget [data Hdata]]; split; [exact Htarget|].
  destruct (sealed_eq_dec EE a e) as [->|Hne].
  - eexists; apply Map.get_set_same.
  - exists data; apply (eq_trans (Map.get_set_other EE a e _ _ Hne)); exact Hdata.
Qed.

Lemma sealed_complete_extends {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (ix : sealed_index N E) st next n :
  sealed_extends EN EE g st next -> sealed_complete EN EE g ix st n ->
  sealed_complete EN EE g ix next n.
Proof.
  intros [_ Hfilled] Hcomplete key Hkey; apply Hfilled, Hcomplete; exact Hkey.
Qed.

Lemma sealed_frame_extends {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (ix : sealed_index N E) st next frame :
  sealed_extends EN EE g st next -> sealed_frame EN EE g ix st frame ->
  (forall n, FinSet.mem EN n (sealed_closed next) = FinSet.mem EN n (sealed_closed st)) ->
  sealed_frame EN EE g ix next frame.
Proof.
  intros [Hmemo Hfilled]; destruct frame as [n rest]; cbn [sealed_frame].
  intros [Hmem [Hreach [Hopen [prefix [Hslots Hprefix]]]]] Hclosed.
  split; [apply Hmemo; exact Hmem|split; [exact Hreach|]].
  split; [rewrite Hclosed; exact Hopen|].
  exists prefix; split; [exact Hslots|]; intros key Hkey; apply Hfilled, Hprefix; exact Hkey.
Qed.

Lemma sealed_initial_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E) :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix (sealed_initial ix).
Proof.
  intro Hix; constructor; cbn [sealed_initial sealed_data sealed_memo sealed_closed
    sealed_virtual sealed_edge_index sealed_roots sealed_stack].
  - constructor; cbn [sealed_memo sealed_closed sealed_virtual sealed_edge_index].
    + apply Map.wf_empty.
    + apply Map.wf_empty.
    + apply Map.wf_empty.
    + apply Map.wf_empty.
    + intros n Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
    + intros n Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
    + intros n Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
    + intros e data Hget; rewrite Map.get_empty in Hget; discriminate.
  - constructor.
  - constructor.
  - intros n Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
  - intros n Hreach _; apply (sealed_nodes_exact Hix); exact Hreach.
  - intros n Hin; apply (sealed_nodes_exact Hix); exact Hin.
  - intros n rest Hin; contradiction.
Qed.

Lemma sealed_open_laws {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st n :
  sealed_store_laws EN EE g effects ix st -> reachable g n ->
  sealed_store_laws EN EE g effects ix (sealed_open EN n st).
Proof.
  intros Hst Hreach; pose proof (sealed_open_extends EN EE g n st) as Hextends.
  constructor; cbn [sealed_open sealed_memo sealed_closed sealed_virtual sealed_edge_index].
  - apply Map.wf_set; exact (sealed_memo_wf Hst).
  - exact (sealed_closed_wf Hst).
  - exact (sealed_virtual_wf Hst).
  - exact (sealed_edge_wf Hst).
  - intros m Hmem; apply FinSet.mem_add in Hmem; destruct Hmem as [->|Hmem].
    + exact Hreach.
    + exact (sealed_memo_reachable Hst m Hmem).
  - intros m Hmem; destruct (sealed_closed_complete Hst m Hmem) as [Hmemo Hcomplete].
    split; [apply (proj1 Hextends); exact Hmemo|].
    eapply sealed_complete_extends; [exact Hextends|exact Hcomplete].
  - intros m Hmem; destruct (sealed_virtual_entry Hst m Hmem) as [Hentry Hmemo].
    split; [exact Hentry|apply (proj1 Hextends); exact Hmemo].
  - intros e data Hget; destruct (sealed_record_agrees Hst e data Hget)
      as [Hedge [Hr [Hsource [Htarget Hdata]]]].
    split; [exact Hedge|split; [exact Hr|]].
    split; [apply (proj1 Hextends); exact Hsource|].
    split; [apply (proj1 Hextends); exact Htarget|exact Hdata].
Qed.

Lemma sealed_close_laws {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st n :
  sealed_store_laws EN EE g effects ix st -> FinSet.mem EN n (sealed_memo st) = true ->
  sealed_complete EN EE g ix st n ->
  sealed_store_laws EN EE g effects ix (sealed_close EN n st).
Proof.
  intros Hst Hmemo Hcomplete; constructor;
    cbn [sealed_close sealed_memo sealed_closed sealed_virtual sealed_edge_index].
  - exact (sealed_memo_wf Hst).
  - apply Map.wf_set; exact (sealed_closed_wf Hst).
  - exact (sealed_virtual_wf Hst).
  - exact (sealed_edge_wf Hst).
  - exact (sealed_memo_reachable Hst).
  - intros m Hmem; apply FinSet.mem_add in Hmem; destruct Hmem as [->|Hmem].
    + split; [exact Hmemo|exact Hcomplete].
    + exact (sealed_closed_complete Hst m Hmem).
  - exact (sealed_virtual_entry Hst).
  - exact (sealed_record_agrees Hst).
Qed.

Lemma sealed_enter_laws {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st n :
  sealed_store_laws EN EE g effects ix st -> FinSet.mem EN n (sealed_memo st) = true ->
  In n (Graph.entries g) -> sealed_store_laws EN EE g effects ix (sealed_enter EN n st).
Proof.
  intros Hst Hmemo Hentry; pose proof (sealed_enter_extends EN EE g n st) as Hextends.
  constructor; cbn [sealed_enter sealed_memo sealed_closed sealed_virtual sealed_edge_index].
  - exact (sealed_memo_wf Hst).
  - exact (sealed_closed_wf Hst).
  - apply Map.wf_set; exact (sealed_virtual_wf Hst).
  - exact (sealed_edge_wf Hst).
  - exact (sealed_memo_reachable Hst).
  - intros m Hmem; destruct (sealed_closed_complete Hst m Hmem) as [Hm Hcomplete].
    split; [exact Hm|eapply sealed_complete_extends; [exact Hextends|exact Hcomplete]].
  - intros m Hmem; apply FinSet.mem_add in Hmem; destruct Hmem as [->|Hmem].
    + split; assumption.
    + exact (sealed_virtual_entry Hst m Hmem).
  - exact (sealed_record_agrees Hst).
Qed.

Lemma sealed_record_laws {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st e :
  sealed_store_laws EN EE g effects ix st -> In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> FinSet.mem EN (Graph.source g e) (sealed_memo st) = true ->
  FinSet.mem EN (Graph.target g e) (sealed_memo st) = true ->
  sealed_store_laws EN EE g effects ix (sealed_record EE g effects e st).
Proof.
  intros Hst Hedge Hreach Hsource Htarget.
  pose proof (sealed_record_extends EN EE g effects e st) as Hextends.
  constructor; cbn [sealed_record sealed_memo sealed_closed sealed_virtual sealed_edge_index].
  - exact (sealed_memo_wf Hst).
  - exact (sealed_closed_wf Hst).
  - exact (sealed_virtual_wf Hst).
  - apply Map.wf_set; exact (sealed_edge_wf Hst).
  - exact (sealed_memo_reachable Hst).
  - intros m Hmem; destruct (sealed_closed_complete Hst m Hmem) as [Hm Hcomplete].
    split; [exact Hm|eapply sealed_complete_extends; [exact Hextends|exact Hcomplete]].
  - exact (sealed_virtual_entry Hst).
  - intros a data Hget; destruct (sealed_eq_dec EE a e) as [->|Hne].
    + rewrite Map.get_set_same in Hget; inversion Hget; subst data.
      split; [exact Hedge|split; [exact Hreach|]].
      split; [exact Hsource|split; [exact Htarget|reflexivity]].
    + rewrite Map.get_set_other in Hget by exact Hne.
      exact (sealed_record_agrees Hst a data Hget).
Qed.

Lemma sealed_frame_key {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    ix st n key rest :
  sealed_frame EN EE g ix st (n, key :: rest) -> In key (sealed_slots ix n).
Proof.
  intros [_ [_ [_ [prefix [Hslots _]]]]]; rewrite Hslots, in_app_iff.
  right; left; reflexivity.
Qed.

Lemma sealed_frame_advance {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    ix st next n key rest :
  sealed_extends EN EE g st next -> sealed_frame EN EE g ix st (n, key :: rest) ->
  (forall m, FinSet.mem EN m (sealed_closed next) = FinSet.mem EN m (sealed_closed st)) ->
  sealed_filled EN EE g next n key -> sealed_frame EN EE g ix next (n, rest).
Proof.
  intros Hextends Hframe Hclosed Hkey.
  pose proof (sealed_frame_extends EN EE g ix st next (n, key :: rest)
    Hextends Hframe Hclosed) as [Hmemo [Hreach [Hopen [prefix [Hslots Hprefix]]]]].
  split; [exact Hmemo|split; [exact Hreach|split; [exact Hopen|]]].
  exists (prefix ++ [key]); split.
  - rewrite Hslots, <- app_assoc; reflexivity.
  - intros k Hk; apply in_app_iff in Hk; destruct Hk as [Hk|Hk].
    + apply Hprefix; exact Hk.
    + cbn [In] in Hk; destruct Hk as [<-|Hfalse]; [exact Hkey|contradiction].
Qed.

Lemma sealed_frame_complete {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    ix st n :
  sealed_frame EN EE g ix st (n, []) -> sealed_complete EN EE g ix st n.
Proof.
  intros [_ [_ [_ [prefix [Hslots Hprefix]]]]] key Hkey.
  rewrite app_nil_r in Hslots; rewrite Hslots in Hkey; apply Hprefix; exact Hkey.
Qed.

Lemma sealed_stack_memo {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    ix st stack n :
  Forall (sealed_frame EN EE g ix st) stack -> In n (map fst stack) ->
  FinSet.mem EN n (sealed_memo st) = true.
Proof.
  intros Hframes Hin; apply in_map_iff in Hin.
  destruct Hin as [[m rest] [Heq Hin]]; cbn in Heq; subst m.
  rewrite Forall_forall in Hframes; specialize (Hframes (n, rest) Hin).
  exact (proj1 Hframes).
Qed.

Lemma sealed_unread_unfilled {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st n key :
  sealed_store_laws EN EE g effects ix st -> FinSet.mem EN n (sealed_memo st) = false ->
  ~ sealed_filled EN EE g st n key.
Proof.
  intros Hst Hfresh; destruct key as [e|].
  - intros [Htarget [data Hget]].
    destruct (sealed_record_agrees Hst e data Hget) as [_ [_ [_ [Hmemo _]]]].
    rewrite Htarget in Hmemo; congruence.
  - intro Hvirtual; destruct (sealed_virtual_entry Hst n Hvirtual) as [_ Hmemo]; congruence.
Qed.

Lemma sealed_push_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st roots stack n next_roots :
  sealed_invariant EN EE g effects ix (SealedMachine st roots stack) -> reachable g n ->
  FinSet.mem EN n (sealed_memo st) = false -> incl next_roots roots ->
  (forall m, m <> n -> In m roots -> In m next_roots) ->
  sealed_invariant EN EE g effects ix
    (SealedMachine (sealed_open EN n st) next_roots ((n, sealed_slots ix n) :: stack)).
Proof.
  intros Hinv Hreach Hfresh Hsubset Hkeep.
  pose proof (sealed_store_valid Hinv) as Hst.
  pose proof (sealed_open_extends EN EE g n st) as Hextends.
  assert (Hopen : FinSet.mem EN n (sealed_closed st) = false).
  { destruct (FinSet.mem EN n (sealed_closed st)) eqn:Hclosed; [|reflexivity].
    destruct (sealed_closed_complete Hst n Hclosed) as [Hmemo _].
    cbn [sealed_data] in Hmemo; congruence. }
  constructor; cbn [sealed_data sealed_roots sealed_stack].
  - apply sealed_open_laws; assumption.
  - constructor.
    + split; [apply sealed_mem_same|split; [exact Hreach|split; [exact Hopen|]]].
      exists []; split; [reflexivity|intros key Hkey; contradiction].
    + rewrite Forall_forall; intros frame Hframe.
      eapply sealed_frame_extends; [exact Hextends| |reflexivity].
      eapply Forall_forall; [exact (sealed_frames Hinv)|exact Hframe].
  - cbn [map fst]; constructor; [|exact (sealed_frame_owners Hinv)].
    intro Hin; pose proof (sealed_stack_memo EN EE g ix st stack n
      (sealed_frames Hinv) Hin); congruence.
  - intros m Hmemo; apply FinSet.mem_add in Hmemo; destruct Hmemo as [->|Hmemo].
    + right; left; reflexivity.
    + destruct (sealed_pending_reads Hinv m Hmemo) as [Hclosed|Hpending].
      * left; exact Hclosed.
      * right; right; exact Hpending.
  - intros m Hr Hmemo; cbn [sealed_open sealed_memo] in Hmemo.
    assert (Hne : m <> n) by (intro Heq; subst m; rewrite sealed_mem_same in Hmemo;
      discriminate).
    rewrite sealed_mem_other in Hmemo by exact Hne.
    apply Hkeep; [exact Hne|exact (sealed_unread_roots Hinv m Hr Hmemo)].
  - intros m Hin; apply (sealed_roots_reachable Hinv m), Hsubset; exact Hin.
  - intros m rest Hin key Hkey Hfilled; cbn [In] in Hin.
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst m rest; eapply sealed_unread_unfilled;
        [exact Hst|exact Hfresh|exact Hfilled].
    + apply (sealed_fresh_slots Hinv m rest Hin key Hkey); exact Hfilled.
Qed.

Lemma sealed_skip_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st n roots stack :
  sealed_invariant EN EE g effects ix (SealedMachine st (n :: roots) stack) ->
  FinSet.mem EN n (sealed_memo st) = true ->
  sealed_invariant EN EE g effects ix (SealedMachine st roots stack).
Proof.
  intros Hinv Hmemo; constructor.
  - exact (sealed_store_valid Hinv).
  - exact (sealed_frames Hinv).
  - exact (sealed_frame_owners Hinv).
  - exact (sealed_pending_reads Hinv).
  - intros m Hr Hfresh; cbn [sealed_data] in Hfresh.
    destruct (sealed_unread_roots Hinv m Hr Hfresh) as [Heq|Hin].
    + subst m; congruence.
    + exact Hin.
  - intros m Hin; apply (sealed_roots_reachable Hinv m); right; exact Hin.
  - exact (sealed_fresh_slots Hinv).
Qed.

Definition sealed_changes_slot {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (st next : sealed_store N E) n key : Prop :=
  forall m k, sealed_filled EN EE g next m k ->
    sealed_filled EN EE g st m k \/ (m = n /\ k = key).

Lemma sealed_enter_changes {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    n (st : sealed_store N E) : sealed_changes_slot EN EE g st (sealed_enter EN n st) n None.
Proof.
  intros m [e|] Hfilled; [left; exact Hfilled|].
  apply FinSet.mem_add in Hfilled; destruct Hfilled as [Heq|Hold].
  - right; split; [exact Heq|reflexivity].
  - left; exact Hold.
Qed.

Lemma sealed_record_changes {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) e (st : sealed_store N E) :
  sealed_changes_slot EN EE g st (sealed_record EE g effects e st) (Graph.target g e) (Some e).
Proof.
  intros n [a|] Hfilled; [|left; exact Hfilled].
  destruct Hfilled as [Htarget [data Hget]].
  destruct (sealed_eq_dec EE a e) as [->|Hne].
  - right; split; [symmetry; exact Htarget|reflexivity].
  - left; split; [exact Htarget|exists data].
    cbn [sealed_record sealed_edge_index] in Hget.
    rewrite Map.get_set_other in Hget by exact Hne; exact Hget.
Qed.

Lemma sealed_nodup_suffix {K} (prefix rest : list K) : NoDup (prefix ++ rest) -> NoDup rest.
Proof.
  induction prefix as [|key prefix IH]; intro Hunique; [exact Hunique|].
  inversion Hunique as [|? ? Hfresh Htail]; subst; apply IH; exact Htail.
Qed.

Lemma sealed_current_not_pending {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st roots n key rest stack m keys k :
  sealed_index_laws g ix ->
  sealed_invariant EN EE g effects ix (SealedMachine st roots ((n, key :: rest) :: stack)) ->
  In (m, keys) ((n, rest) :: stack) -> In k keys -> ~ (m = n /\ k = key).
Proof.
  intros Hix Hinv Hin Hkey [-> ->].
  cbn [In] in Hin; destruct Hin as [Heq|Hin].
  - inversion Heq; subst keys.
    destruct (Forall_inv (sealed_frames Hinv)) as [_ [_ [_ [prefix [Hslots _]]]]].
    pose proof (sealed_slots_nodup Hix n) as Hunique; rewrite Hslots in Hunique.
    apply sealed_nodup_suffix in Hunique; inversion Hunique as [|? ? Hfresh Htail]; subst.
    contradiction.
  - pose proof (sealed_frame_owners Hinv) as Howners.
    inversion Howners as [|? ? Hfresh Htail]; subst.
    apply Hfresh, in_map_iff; exists (n, keys); split; [reflexivity|exact Hin].
Qed.

Lemma sealed_advance_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st next roots n key rest stack :
  sealed_index_laws g ix ->
  sealed_invariant EN EE g effects ix (SealedMachine st roots ((n, key :: rest) :: stack)) ->
  sealed_store_laws EN EE g effects ix next -> sealed_extends EN EE g st next ->
  (forall m, FinSet.mem EN m (sealed_memo next) = FinSet.mem EN m (sealed_memo st)) ->
  (forall m, FinSet.mem EN m (sealed_closed next) = FinSet.mem EN m (sealed_closed st)) ->
  sealed_filled EN EE g next n key -> sealed_changes_slot EN EE g st next n key ->
  sealed_invariant EN EE g effects ix (SealedMachine next roots ((n, rest) :: stack)).
Proof.
  intros Hix Hinv Hst Hextends Hmemo Hclosed Hfilled Hchange.
  pose proof (sealed_frames Hinv) as Hallframes.
  inversion Hallframes as [|? ? Hframe Hframes]; subst.
  constructor; cbn [sealed_data sealed_roots sealed_stack].
  - exact Hst.
  - constructor.
    + eapply sealed_frame_advance; eassumption.
    + rewrite Forall_forall; intros frame Hin.
      eapply sealed_frame_extends; [exact Hextends| |exact Hclosed].
      eapply Forall_forall; [exact Hframes|exact Hin].
  - exact (sealed_frame_owners Hinv).
  - intros m Hmem; rewrite Hmemo in Hmem.
    rewrite Hclosed; exact (sealed_pending_reads Hinv m Hmem).
  - intros m Hr Hmem; rewrite Hmemo in Hmem; exact (sealed_unread_roots Hinv m Hr Hmem).
  - exact (sealed_roots_reachable Hinv).
  - intros m keys Hin k Hk Hnew; destruct (Hchange m k Hnew) as [Hold|Hcurrent].
    + cbn [In] in Hin; destruct Hin as [Heq|Hin].
      * inversion Heq; subst m keys.
        apply (sealed_fresh_slots Hinv n (key :: rest) (or_introl eq_refl) k
          (or_intror Hk)); exact Hold.
      * apply (sealed_fresh_slots Hinv m keys (or_intror Hin) k Hk); exact Hold.
    + exact (sealed_current_not_pending EN EE g effects ix st roots n key rest stack
        m keys k Hix Hinv Hin Hk Hcurrent).
Qed.

Lemma sealed_frame_close {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    ix st n m rest :
  m <> n -> sealed_frame EN EE g ix st (m, rest) ->
  sealed_frame EN EE g ix (sealed_close EN n st) (m, rest).
Proof.
  intros Hne [Hmemo [Hreach [Hopen Hprefix]]].
  split; [exact Hmemo|split; [exact Hreach|split; [|exact Hprefix]]].
  cbn [sealed_close sealed_closed]; rewrite sealed_mem_other by exact Hne; exact Hopen.
Qed.

Lemma sealed_finish_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix st roots n stack :
  sealed_invariant EN EE g effects ix (SealedMachine st roots ((n, []) :: stack)) ->
  sealed_invariant EN EE g effects ix (SealedMachine (sealed_close EN n st) roots stack).
Proof.
  intro Hinv; pose proof (sealed_frames Hinv) as Hallframes.
  pose proof (sealed_frame_owners Hinv) as Hunique.
  inversion Hallframes as [|? ? Hframe Hframes]; subst.
  inversion Hunique as [|? ? Hfresh Howners]; subst.
  constructor; cbn [sealed_data sealed_roots sealed_stack].
  - apply sealed_close_laws; [exact (sealed_store_valid Hinv)|exact (proj1 Hframe)|].
    apply sealed_frame_complete; exact Hframe.
  - rewrite Forall_forall; intros [m rest] Hin.
    apply sealed_frame_close.
    + intro Heq; subst m; apply Hfresh; apply in_map_iff.
      exists (n, rest); split; [reflexivity|exact Hin].
    + eapply Forall_forall; [exact Hframes|exact Hin].
  - exact Howners.
  - intros m Hmem; destruct (sealed_pending_reads Hinv m Hmem) as [Hclosed|Hpending].
    + left; apply FinSet.mem_add; right; exact Hclosed.
    + cbn [sealed_stack map fst In] in Hpending; destruct Hpending as [<-|Hpending].
      * left; apply sealed_mem_same.
      * right; exact Hpending.
  - exact (sealed_unread_roots Hinv).
  - exact (sealed_roots_reachable Hinv).
  - intros m keys Hin key Hkey Hfilled.
    apply (sealed_fresh_slots Hinv m keys (or_intror Hin) key Hkey); exact Hfilled.
Qed.

Lemma sealed_step_invariant {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix machine ->
  sealed_invariant EN EE g effects ix (sealed_step EN EE g effects ix machine).
Proof.
  intros Hix Hinv; destruct machine as [st roots [|[n [|[e|] rest]] stack]];
    cbn [sealed_step sealed_data sealed_roots sealed_stack].
  - destruct roots as [|n roots]; [exact Hinv|].
    destruct (FinSet.mem EN n (sealed_memo st)) eqn:Hmemo.
    + apply sealed_skip_invariant with (n := n); assumption.
    + eapply sealed_push_invariant; [exact Hinv| |exact Hmemo| |].
      * apply (sealed_roots_reachable Hinv n); left; reflexivity.
      * intros m Hm; right; exact Hm.
      * intros m Hne [Heq|Hin]; [congruence|exact Hin].
  - apply sealed_finish_invariant; exact Hinv.
  - pose proof (Forall_inv (sealed_frames Hinv)) as Hframe.
    pose proof (sealed_frame_key EN EE g ix st n (Some e) rest Hframe) as Hslot.
    apply (sealed_slots_exact Hix) in Hslot.
    destruct Hslot as [Hn [Hedge [Hreach Htarget]]].
    destruct (FinSet.mem EN (Graph.source g e) (sealed_memo st)) eqn:Hmemo.
    + eapply sealed_advance_invariant; [exact Hix|exact Hinv| | |reflexivity|reflexivity| |].
      * apply sealed_record_laws; [exact (sealed_store_valid Hinv)|exact Hedge|
          exact Hreach|exact Hmemo|].
        rewrite Htarget; exact (proj1 Hframe).
      * apply sealed_record_extends.
      * split; [exact Htarget|]; eexists; apply Map.get_set_same.
      * rewrite <- Htarget; apply sealed_record_changes.
    + eapply sealed_push_invariant; [exact Hinv|exact Hreach|exact Hmemo| |].
      * intros m Hm; exact Hm.
      * intros m _ Hm; exact Hm.
  - pose proof (Forall_inv (sealed_frames Hinv)) as Hframe.
    pose proof (sealed_frame_key EN EE g ix st n None rest Hframe) as Hslot.
    apply (sealed_slots_exact Hix) in Hslot.
    eapply sealed_advance_invariant; [exact Hix|exact Hinv| | |reflexivity|reflexivity| |].
    + apply sealed_enter_laws; [exact (sealed_store_valid Hinv)|exact (proj1 Hframe)|].
      exact (proj2 Hslot).
    + apply sealed_enter_extends.
    + apply sealed_mem_same.
    + apply sealed_enter_changes.
Qed.

(** * Finite work, including slots not allocated yet *)

Definition sealed_credit {N E} (ix : sealed_index N E) n : nat :=
  2 + length (sealed_slots ix n).

Fixpoint sealed_white {N E} (EN : encoding N) (ix : sealed_index N E) (memo : FinSet.t N)
    (nodes : list N) : nat :=
  match nodes with
  | [] => 0
  | n :: rest =>
    (if FinSet.mem EN n memo then 0 else sealed_credit ix n) + sealed_white EN ix memo rest
  end.

Fixpoint sealed_stack_work {N E} (stack : list (N * list (option E))) : nat :=
  match stack with
  | [] => 0
  | (_, rest) :: stack => S (length rest) + sealed_stack_work stack
  end.

(** Uninstalled blocks are charged for their read, seal and every potential operand slot. *)
Definition sealed_measure {N E} (EN : encoding N) (ix : sealed_index N E)
    (machine : sealed_machine N E) : nat :=
  sealed_white EN ix (sealed_memo (sealed_data machine)) (sealed_nodes ix) +
  sealed_stack_work (sealed_stack machine) + length (sealed_roots machine).

Definition sealed_terminal {N E} (machine : sealed_machine N E) : Prop :=
  sealed_roots machine = [] /\ sealed_stack machine = [].

Definition sealed_terminal_dec {N E} (machine : sealed_machine N E) :
    {sealed_terminal machine} + {~ sealed_terminal machine}.
Proof.
  destruct machine as [st [|n roots] [|frame stack]]; unfold sealed_terminal;
    cbn [sealed_roots sealed_stack]; try (right; intuition discriminate).
  left; split; reflexivity.
Defined.

Lemma sealed_white_other {N E} (EN : encoding N) (ix : sealed_index N E) memo n nodes :
  ~ In n nodes ->
  sealed_white EN ix (FinSet.add EN n memo) nodes = sealed_white EN ix memo nodes.
Proof.
  induction nodes as [|m nodes IH]; intro Hnot; cbn [sealed_white]; [reflexivity|].
  rewrite sealed_mem_other by (intro Heq; subst m; apply Hnot; left; reflexivity).
  rewrite IH by (intro Hin; apply Hnot; right; exact Hin); reflexivity.
Qed.

Lemma sealed_white_open {N E} (EN : encoding N) (ix : sealed_index N E) memo n nodes :
  NoDup nodes -> In n nodes -> FinSet.mem EN n memo = false ->
  sealed_white EN ix memo nodes =
    sealed_credit ix n + sealed_white EN ix (FinSet.add EN n memo) nodes.
Proof.
  intro Hunique; induction Hunique as [|m nodes Hfresh Hunique IH]; intros Hin Hmemo.
  - contradiction.
  - cbn [In] in Hin; cbn [sealed_white].
    destruct (sealed_eq_dec EN m n) as [->|Hne].
    + rewrite Hmemo, sealed_mem_same, sealed_white_other by exact Hfresh; lia.
    + rewrite sealed_mem_other by exact Hne.
      assert (Htail : In n nodes) by (destruct Hin as [Heq|Hin]; [congruence|exact Hin]).
      specialize (IH Htail Hmemo); destruct (FinSet.mem EN m memo); lia.
Qed.

(** Each transition consumes credit; installing a placeholder pays for all newly pending work. *)
Lemma sealed_step_decreases {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix machine ->
  ~ sealed_terminal machine ->
  sealed_measure EN ix (sealed_step EN EE g effects ix machine) < sealed_measure EN ix machine.
Proof.
  intros Hix Hinv Hactive; destruct machine as [st roots [|[n [|[e|] rest]] stack]].
  - destruct roots as [|n roots]; [exfalso; apply Hactive; split; reflexivity|].
    cbn [sealed_step sealed_data sealed_roots sealed_stack].
    destruct (FinSet.mem EN n (sealed_memo st)) eqn:Hmemo.
    + unfold sealed_measure; cbn [sealed_data sealed_stack sealed_roots length]; lia.
    + assert (Hn : In n (sealed_nodes ix)).
      { apply (sealed_nodes_exact Hix), (sealed_roots_reachable Hinv n); left; reflexivity. }
      pose proof (sealed_white_open EN ix (sealed_memo st) n (sealed_nodes ix)
        (sealed_nodes_nodup Hix) Hn Hmemo) as Hcredit.
      unfold sealed_measure; cbn [sealed_data sealed_stack sealed_roots sealed_stack_work
        sealed_open sealed_memo length].
      unfold sealed_credit in Hcredit; lia.
  - unfold sealed_measure; cbn [sealed_step sealed_data sealed_stack sealed_roots
      sealed_stack_work sealed_close sealed_memo length]; lia.
  - cbn [sealed_step sealed_data sealed_roots sealed_stack].
    destruct (FinSet.mem EN (Graph.source g e) (sealed_memo st)) eqn:Hmemo.
    + unfold sealed_measure; cbn [sealed_data sealed_stack sealed_roots sealed_stack_work
        sealed_record sealed_memo length]; lia.
    + pose proof (Forall_inv (sealed_frames Hinv)) as Hframe.
      pose proof (sealed_frame_key EN EE g ix st n (Some e) rest Hframe) as Hslot.
      apply (sealed_slots_exact Hix) in Hslot.
      destruct Hslot as [_ [_ [Hreach _]]].
      pose proof (sealed_white_open EN ix (sealed_memo st) (Graph.source g e)
        (sealed_nodes ix) (sealed_nodes_nodup Hix)
        (proj2 (sealed_nodes_exact Hix _) Hreach) Hmemo) as Hcredit.
      unfold sealed_measure; cbn [sealed_data sealed_stack sealed_roots sealed_stack_work
        sealed_open sealed_memo length].
      unfold sealed_credit in Hcredit; lia.
  - unfold sealed_measure; cbn [sealed_step sealed_data sealed_stack sealed_roots
      sealed_stack_work sealed_enter sealed_memo length]; lia.
Qed.

Lemma sealed_step_terminal {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine :
  sealed_terminal machine -> sealed_step EN EE g effects ix machine = machine.
Proof.
  destruct machine as [st roots stack]; intros [Hroots Hstack]; cbn in Hroots, Hstack.
  subst roots stack; reflexivity.
Qed.

Lemma sealed_iter_spec {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine steps :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix machine ->
  let result := Pos.iter (sealed_step EN EE g effects ix) machine steps in
  sealed_invariant EN EE g effects ix result /\
  (sealed_terminal result \/
    sealed_measure EN ix result + Pos.to_nat steps <= sealed_measure EN ix machine).
Proof.
  intros Hix Hinv; induction steps using Pos.peano_ind.
  - cbn [Pos.iter]; split; [apply sealed_step_invariant; assumption|].
    destruct (sealed_terminal_dec machine) as [Hdone|Hactive].
    + rewrite sealed_step_terminal by exact Hdone; left; exact Hdone.
    + right; change (sealed_measure EN ix (sealed_step EN EE g effects ix machine) + 1 <=
        sealed_measure EN ix machine).
      pose proof (sealed_step_decreases EN EE g effects ix machine Hix Hinv Hactive); lia.
  - rewrite Pos.iter_succ.
    destruct IHsteps as [Hstate Hbound].
    set (previous := Pos.iter (sealed_step EN EE g effects ix) machine steps) in *.
    split; [apply sealed_step_invariant; assumption|].
    destruct (sealed_terminal_dec previous) as [Hdone|Hactive].
    + rewrite sealed_step_terminal by exact Hdone; left; exact Hdone.
    + destruct Hbound as [Hdone|Hbound]; [contradiction|].
      right; pose proof (sealed_step_decreases EN EE g effects ix previous Hix Hstate Hactive).
      rewrite Pos2Nat.inj_succ; lia.
Qed.

Definition sealed_capacity {N E} (ix : sealed_index N E) : nat :=
  fold_right (fun n total => sealed_credit ix n + total) 0 (sealed_nodes ix).

Definition sealed_run {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E) : sealed_machine N E :=
  Pos.iter (sealed_step EN EE g effects ix) (sealed_initial ix)
    (Pos.of_succ_nat (sealed_capacity ix + length (sealed_nodes ix))).

Lemma sealed_initial_measure {N E} (EN : encoding N) (ix : sealed_index N E) :
  sealed_measure EN ix (sealed_initial ix) = sealed_capacity ix + length (sealed_nodes ix).
Proof.
  unfold sealed_measure, sealed_initial, sealed_capacity;
    cbn [sealed_data sealed_memo sealed_stack sealed_stack_work sealed_roots].
  assert (Hwhite : forall nodes, sealed_white EN ix FinSet.empty nodes =
    fold_right (fun n total => sealed_credit ix n + total) 0 nodes).
  { intro nodes; induction nodes as [|n nodes IH]; cbn [sealed_white fold_right].
    - reflexivity.
    - rewrite FinSet.mem_empty, IH; reflexivity. }
  rewrite Hwhite; lia.
Qed.

(** The input-derived binary bound finishes every pending read and every operand frame. *)
Lemma sealed_run_complete {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix :
  sealed_index_laws g ix ->
  sealed_invariant EN EE g effects ix (sealed_run EN EE g effects ix) /\
  sealed_terminal (sealed_run EN EE g effects ix).
Proof.
  intro Hix; destruct (sealed_iter_spec EN EE g effects ix (sealed_initial ix)
    (Pos.of_succ_nat (sealed_capacity ix + length (sealed_nodes ix))) Hix
    (sealed_initial_invariant EN EE g effects ix Hix)) as [Hinv [Hdone|Hbound]].
  - split; [exact Hinv|exact Hdone].
  - rewrite sealed_initial_measure, SuccNat2Pos.id_succ in Hbound; lia.
Qed.

Lemma sealed_terminal_closed {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine n :
  sealed_invariant EN EE g effects ix machine -> sealed_terminal machine -> reachable g n ->
  FinSet.mem EN n (sealed_memo (sealed_data machine)) = true /\
  FinSet.mem EN n (sealed_closed (sealed_data machine)) = true.
Proof.
  intros Hinv [Hroots Hstack] Hreach.
  assert (Hmemo : FinSet.mem EN n (sealed_memo (sealed_data machine)) = true).
  { destruct (FinSet.mem EN n (sealed_memo (sealed_data machine))) eqn:Hmemo; [reflexivity|].
    pose proof (sealed_unread_roots Hinv n Hreach Hmemo) as Hin; rewrite Hroots in Hin.
    contradiction. }
  split; [exact Hmemo|].
  destruct (sealed_pending_reads Hinv n Hmemo) as [Hclosed|Hin]; [exact Hclosed|].
  rewrite Hstack in Hin; contradiction.
Qed.

(** * Finalized graph observations *)

Definition sealed_version_encoding {N E} (EN : encoding N) (EE : encoding E) :
    encoding (memory_version N E).
Proof.
  refine (Encoding (memory_version N E) (fun v => match v with
    | MemoryLive => xH
    | MemoryPhi n => xO (encode EN n)
    | MemoryDef e i => xI (encode (pair_encoding EE nat_encoding) (e, i))
    end) _).
  intros [|n|e i] [|m|f j] Heq; cbn in Heq; try discriminate; try reflexivity.
  - injection Heq as Hcode; f_equal; apply (encode_injective EN); exact Hcode.
  - injection Heq as Hcode.
    change (encode (pair_encoding EE nat_encoding) (e, i) =
      encode (pair_encoding EE nat_encoding) (f, j)) in Hcode.
    apply (encode_injective (pair_encoding EE nat_encoding)) in Hcode.
    inversion Hcode; reflexivity.
Defined.

Definition sealed_def_inventory {N E} (st : sealed_store N E) : list (memory_version N E) :=
  flat_map (fun binding => sealed_definitions (snd binding)) (Map.elements (sealed_edge_index st)).

Definition sealed_graph {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (st : sealed_store N E) : memory_graph N E :=
  let phis := FinSet.elements (sealed_memo st) in
  MemoryGraph phis
    (distinct_unknowns (sealed_version_encoding EN EE)
      (MemoryLive :: (map MemoryPhi phis ++ sealed_def_inventory st)))
    (fun n => if FinSet.mem EN n (sealed_memo st) then MemoryPhi n else MemoryLive)
    (fun e i => match Map.get EE e (sealed_edge_index st) with
      | Some data => Map.get nat_encoding i (sealed_inputs data)
      | None => None
      end)
    (fun e => match Map.get EE e (sealed_edge_index st) with
      | Some data => sealed_output data
      | None => MemoryLive
      end)
    (fun n key => if FinSet.mem EN n (sealed_closed st) then
      match key with
      | None => if FinSet.mem EN n (sealed_virtual st) then Some MemoryLive else None
      | Some e => if Pos.eqb (encode EN (Graph.target g e)) (encode EN n) then
          option_map sealed_output (Map.get EE e (sealed_edge_index st))
        else None
      end
      else None).

Section Finalization.
Context {N E T : Type} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
  (effects : E -> list (memory_effect T)) (ix : sealed_index N E) (st : sealed_store N E).
Hypotheses (Hix : sealed_index_laws g ix) (Hst : sealed_store_laws EN EE g effects ix st)
  (Hclosed : forall n, reachable g n -> FinSet.mem EN n (sealed_closed st) = true).

Lemma sealed_final_memo n : FinSet.mem EN n (sealed_memo st) = true <-> reachable g n.
Proof.
  split; [exact (sealed_memo_reachable Hst n)|].
  intro Hreach; exact (proj1 (sealed_closed_complete Hst n (Hclosed n Hreach))).
Qed.

Lemma sealed_final_phi n : memory_phi_at (sealed_graph EN EE g st) n <-> reachable g n.
Proof.
  unfold memory_phi_at; cbn [sealed_graph memory_phis].
  rewrite FinSet.elements_spec by exact (sealed_memo_wf Hst); apply sealed_final_memo.
Qed.

Lemma sealed_final_input n : reachable g n ->
  memory_in (sealed_graph EN EE g st) n = MemoryPhi n.
Proof.
  intro Hreach; cbn [sealed_graph memory_in]; rewrite (proj2 (sealed_final_memo n) Hreach).
  reflexivity.
Qed.

Lemma sealed_final_edge e : In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> Map.get EE e (sealed_edge_index st) =
    Some (sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e))).
Proof.
  intros Hedge Hreach; assert (Htarget : reachable g (Graph.target g e)).
  { eapply reachable_step; eassumption. }
  pose proof (proj2 (sealed_closed_complete Hst _ (Hclosed _ Htarget))) as Hcomplete.
  assert (Hslot : In (Some e) (sealed_slots ix (Graph.target g e))).
  { apply (sealed_slots_exact Hix); split; [exact Htarget|].
    split; [exact Hedge|split; [exact Hreach|reflexivity]]. }
  destruct (Hcomplete (Some e) Hslot) as [_ [data Hget]].
  destruct (sealed_record_agrees Hst e data Hget) as [_ [_ [_ [_ ->]]]]; exact Hget.
Qed.

Lemma sealed_final_virtual n : In n (Graph.entries g) ->
  FinSet.mem EN n (sealed_virtual st) = true.
Proof.
  intro Hentry; assert (Hreach : reachable g n) by (constructor; exact Hentry).
  apply (proj2 (sealed_closed_complete Hst n (Hclosed n Hreach)) None).
  apply (sealed_slots_exact Hix); split; assumption.
Qed.

Lemma sealed_inventory_exact v : In v (sealed_def_inventory st) <->
  exists e i a, v = MemoryDef e i /\ memory_occurrence g effects e i a /\
    effect_is_def a = true.
Proof.
  unfold sealed_def_inventory; rewrite in_flat_map; split.
  - intros [[e data] [Hbinding Hdef]]; cbn [snd] in Hdef.
    apply (Map.elements_sound EE) in Hbinding; [|exact (sealed_edge_wf Hst)].
    destruct (sealed_record_agrees Hst e data Hbinding) as [He [Hr [_ [_ ->]]]].
    apply sealed_scan_definitions in Hdef; destruct Hdef as [i [a [Hnth [Ha Hv]]]].
    exists e, i, a; split; [exact Hv|split; [|exact Ha]].
    split; [exact He|split; assumption].
  - intros [e [i [a [-> [[He [Hr Hnth]] Ha]]]]].
    exists (e, sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e))); split.
    + apply (Map.elements_complete EE); [exact (sealed_edge_wf Hst)|].
      apply sealed_final_edge; assumption.
    + cbn [snd]; apply sealed_scan_definitions; exists i, a.
      split; [exact Hnth|split; [exact Ha|reflexivity]].
Qed.

Lemma sealed_versions_exact v : In v (memory_versions (sealed_graph EN EE g st)) <->
  memory_valid_version g effects (sealed_graph EN EE g st) v.
Proof.
  cbn [sealed_graph memory_versions]; rewrite distinct_unknowns_spec; cbn [In].
  rewrite in_app_iff, in_map_iff, sealed_inventory_exact.
  destruct v as [|n|e i]; cbn [memory_valid_version].
  - split; [intros _; exact I|intros _; left; reflexivity].
  - split.
    + intros [Hbad|[[m [Heq Hin]]|[a [j [effect [Hbad _]]]]]]; try discriminate.
      inversion Heq; subst m; split; [apply sealed_final_phi; exact Hin|exact Hin].
    + intros [_ Hin]; right; left; exists n; split; [reflexivity|exact Hin].
  - split.
    + intros [Hbad|[[m [Hbad _]]|[a [j [effect [Heq [Hocc Hdef]]]]]]]; try discriminate.
      inversion Heq; subst a j; exists effect; split; assumption.
    + intros [effect [Hocc Hdef]]; right; right; exists e, i, effect.
      split; [reflexivity|split; assumption].
Qed.

Lemma sealed_before_domain e i :
  (exists v, memory_before (sealed_graph EN EE g st) e i = Some v) <->
  exists a, memory_occurrence g effects e i a.
Proof.
  cbn [sealed_graph memory_before]; split.
  - intros [v Hget]; destruct (Map.get EE e (sealed_edge_index st)) as [data|] eqn:Hedge;
      [|discriminate].
    destruct (sealed_record_agrees Hst e data Hedge) as [He [Hr [_ [_ Hdata]]]].
    rewrite Hdata in Hget; apply sealed_scan_domain in Hget.
    destruct Hget as [k [a [Hi Hnth]]]; cbn in Hi; subst k.
    exists a; split; [exact He|split; assumption].
  - intros [a [He [Hr Hnth]]]; rewrite sealed_final_edge by assumption.
    exists (memory_last_defs e 0 (firstn i (effects e)) (MemoryPhi (Graph.source g e))).
    exact (sealed_scan_lookup e 0 (effects e) (MemoryPhi (Graph.source g e)) i a Hnth).
Qed.

Lemma sealed_operand_domain n key :
  (exists v, memory_operand (sealed_graph EN EE g st) n key = Some v) <->
  memory_phi_at (sealed_graph EN EE g st) n /\
  match key with
  | None => In n (Graph.entries g)
  | Some e => In e (Graph.out g (Graph.source g e)) /\
      reachable g (Graph.source g e) /\ Graph.target g e = n
  end.
Proof.
  rewrite sealed_final_phi; cbn [sealed_graph memory_operand]; split.
  - intros [v Hget]; destruct (FinSet.mem EN n (sealed_closed st)) eqn:Hdone;
      [|discriminate].
    split; [apply sealed_final_memo; exact (proj1 (sealed_closed_complete Hst n Hdone))|].
    destruct key as [e|].
    + destruct (Pos.eqb (encode EN (Graph.target g e)) (encode EN n)) eqn:Htarget;
        [|discriminate].
      apply Pos.eqb_eq, (encode_injective EN) in Htarget.
      destruct (Map.get EE e (sealed_edge_index st)) as [data|] eqn:Hedge;
        [|discriminate].
      destruct (sealed_record_agrees Hst e data Hedge) as [He [Hr _]].
      split; [exact He|split; assumption].
    + destruct (FinSet.mem EN n (sealed_virtual st)) eqn:Hentry; [|discriminate].
      exact (proj1 (sealed_virtual_entry Hst n Hentry)).
  - intros [Hreach Hkey]; rewrite (Hclosed n Hreach); destruct key as [e|].
    + destruct Hkey as [He [Hr Htarget]]; rewrite Htarget, Pos.eqb_refl.
      rewrite sealed_final_edge by assumption; eexists; reflexivity.
    + rewrite sealed_final_virtual by exact Hkey; exists MemoryLive; reflexivity.
Qed.

Lemma sealed_last_valid (mg : memory_graph N E) e start (xs : list (memory_effect T)) input :
  memory_valid_version g effects mg input ->
  (forall k a, nth_error xs k = Some a -> effect_is_def a = true ->
    memory_valid_version g effects mg (MemoryDef e (start + k))) ->
  memory_valid_version g effects mg (memory_last_defs e start xs input).
Proof.
  revert start input; induction xs as [|a xs IH]; intros start input Hinput Hdefs.
  - exact Hinput.
  - cbn [memory_last_defs]; apply IH.
    + unfold memory_after; destruct (effect_is_def a) eqn:Hdef; [|exact Hinput].
      replace start with (start + 0) by lia; apply (Hdefs 0 a eq_refl Hdef).
    + intros k b Hnth Hdef; replace (S start + k) with (start + S k) by lia.
      apply (Hdefs (S k) b Hnth Hdef).
Qed.

(** Local memo, complete-slot and edge-record invariants directly establish every graph law. *)
Lemma sealed_graph_well_formed : graph_wf g -> memory_graph_wf g effects (sealed_graph EN EE g st).
Proof.
  intro Hwf; constructor.
  - exact Hwf.
  - apply (FinSet.elements_nodup EN); exact (sealed_memo_wf Hst).
  - intros n Hphi; apply sealed_final_phi; exact Hphi.
  - apply distinct_unknowns_nodup.
  - exact sealed_versions_exact.
  - intros n Hentry; left; split; [apply sealed_final_phi; constructor; exact Hentry|].
    split; [|apply sealed_final_input; constructor; exact Hentry].
    cbn [sealed_graph memory_operand]; rewrite Hclosed by (constructor; exact Hentry).
    rewrite sealed_final_virtual by exact Hentry; reflexivity.
  - intros e He Hr; rewrite sealed_final_input by exact Hr.
    cbn [sealed_graph memory_out]; rewrite sealed_final_edge by assumption.
    rewrite sealed_scan_output; apply sealed_prefix_flow; intros k a Hnth.
    cbn [sealed_graph memory_before]; rewrite sealed_final_edge by assumption.
    apply (sealed_scan_lookup e 0 (effects e) (MemoryPhi (Graph.source g e)) k a Hnth).
  - intros e He Hr; assert (Ht : reachable g (Graph.target g e)).
    { eapply reachable_step; eassumption. }
    left; split; [apply sealed_final_phi; exact Ht|].
    split; [|apply sealed_final_input; exact Ht].
    cbn [sealed_graph memory_operand memory_out]; rewrite (Hclosed _ Ht), Pos.eqb_refl.
    rewrite sealed_final_edge by assumption; reflexivity.
  - intros n Hr; rewrite sealed_final_input by exact Hr; split; [exact Hr|].
    apply sealed_final_phi; exact Hr.
  - intros e He Hr; cbn [sealed_graph memory_out]; rewrite sealed_final_edge by assumption.
    rewrite sealed_scan_output; apply sealed_last_valid.
    + split; [exact Hr|apply sealed_final_phi; exact Hr].
    + intros k a Hnth Hdef; exists a; split; [|exact Hdef].
      split; [exact He|split; assumption].
  - exact sealed_before_domain.
  - exact sealed_operand_domain.
Qed.

End Finalization.

(** * Once-prepared occurrence indexes *)

Definition sealed_plan_edges {N E} (EE : encoding E) (ix : sealed_index N E) : list E :=
  distinct_unknowns EE (flat_map (fun n => flat_map (fun key => match key with
    | Some e => [e]
    | None => []
    end) (sealed_slots ix n)) (sealed_nodes ix)).

Lemma sealed_plan_edges_exact {N E} (EE : encoding E) (g : Graph.t N E) ix e :
  sealed_index_laws g ix -> (In e (sealed_plan_edges EE ix) <->
    In e (Graph.out g (Graph.source g e)) /\ reachable g (Graph.source g e)).
Proof.
  intro Hix; unfold sealed_plan_edges; rewrite distinct_unknowns_spec, in_flat_map; split.
  - intros [n [Hnode Hslots]]; apply in_flat_map in Hslots.
    destruct Hslots as [[a|] [Hslot Hin]]; [|contradiction].
    cbn [In] in Hin; destruct Hin as [->|Hfalse]; [|contradiction].
    apply (sealed_slots_exact Hix) in Hslot; tauto.
  - intros [Hedge Hreach]; assert (Ht : reachable g (Graph.target g e)).
    { eapply reachable_step; eassumption. }
    exists (Graph.target g e); split; [apply (sealed_nodes_exact Hix); exact Ht|].
    apply in_flat_map; exists (Some e); split.
    + apply (sealed_slots_exact Hix); split; [exact Ht|].
      split; [exact Hedge|split; [exact Hreach|reflexivity]].
    + left; reflexivity.
Qed.

(** The ordered occurrence maps are built once per distinct reachable edge before the loop. *)
Definition sealed_plans {N E T} (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E) :
    Map.t E (sealed_edge N E) :=
  sealed_table EE (sealed_plan_edges EE ix)
    (fun e => sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e))).

Lemma sealed_plans_hit {N E T} (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix e :
  sealed_index_laws g ix -> In e (Graph.out g (Graph.source g e)) ->
  reachable g (Graph.source g e) -> Map.get EE e (sealed_plans EE g effects ix) =
    Some (sealed_scan e 0 (effects e) (MemoryPhi (Graph.source g e))).
Proof.
  intros Hix Hedge Hreach; unfold sealed_plans.
  apply (sealed_table_hit EE (sealed_plan_edges EE ix)
    (fun a => sealed_scan a 0 (effects a) (MemoryPhi (Graph.source g a))) e).
  apply (sealed_plan_edges_exact EE g ix e Hix).
  split; assumption.
Qed.

Definition sealed_indexed_record {N E} (EE : encoding E) (plans : Map.t E (sealed_edge N E))
    e (st : sealed_store N E) : sealed_store N E :=
  let data := match Map.get EE e plans with
    | Some data => data
    | None => SealedEdge Map.empty MemoryLive []
    end in
  SealedStore (sealed_memo st) (sealed_closed st) (sealed_virtual st)
    (Map.set EE e data (sealed_edge_index st)).

(** The executable worklist only reads prepared slots and occurrence maps through trie lookups. *)
Definition sealed_indexed_step {N E} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (ix : sealed_index N E) (plans : Map.t E (sealed_edge N E))
    (machine : sealed_machine N E) : sealed_machine N E :=
  let st := sealed_data machine in
  let roots := sealed_roots machine in
  match sealed_stack machine with
  | [] =>
    match roots with
    | [] => machine
    | n :: rest =>
      if FinSet.mem EN n (sealed_memo st) then SealedMachine st rest []
      else SealedMachine (sealed_open EN n st) rest [(n, sealed_slots ix n)]
    end
  | (n, []) :: stack => SealedMachine (sealed_close EN n st) roots stack
  | (n, None :: keys) :: stack =>
    SealedMachine (sealed_enter EN n st) roots ((n, keys) :: stack)
  | (n, Some e :: keys) :: stack =>
    if FinSet.mem EN (Graph.source g e) (sealed_memo st) then
      SealedMachine (sealed_indexed_record EE plans e st) roots ((n, keys) :: stack)
    else SealedMachine (sealed_open EN (Graph.source g e) st) roots
      ((Graph.source g e, sealed_slots ix (Graph.source g e)) ::
        (n, Some e :: keys) :: stack)
  end.

Lemma sealed_indexed_step_agrees {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix machine ->
  sealed_indexed_step EN EE g ix (sealed_plans EE g effects ix) machine =
    sealed_step EN EE g effects ix machine.
Proof.
  intros Hix Hinv; destruct machine as [st roots [|[n [|[e|] rest]] stack]];
    cbn [sealed_indexed_step sealed_step sealed_data sealed_roots sealed_stack];
    try reflexivity.
  destruct (FinSet.mem EN (Graph.source g e) (sealed_memo st)); [|reflexivity].
  pose proof (sealed_frame_key EN EE g ix st n (Some e) rest
    (Forall_inv (sealed_frames Hinv))) as Hslot.
  apply (sealed_slots_exact Hix) in Hslot; destruct Hslot as [_ [Hedge [Hreach _]]].
  unfold sealed_indexed_record; rewrite sealed_plans_hit by assumption; reflexivity.
Qed.

Lemma sealed_indexed_iter_agrees {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) ix machine steps :
  sealed_index_laws g ix -> sealed_invariant EN EE g effects ix machine ->
  Pos.iter (sealed_indexed_step EN EE g ix (sealed_plans EE g effects ix)) machine steps =
    Pos.iter (sealed_step EN EE g effects ix) machine steps.
Proof.
  intros Hix Hinv; induction steps using Pos.peano_ind.
  - cbn [Pos.iter]; apply sealed_indexed_step_agrees; assumption.
  - rewrite !Pos.iter_succ, IHsteps; apply sealed_indexed_step_agrees; [exact Hix|].
    exact (proj1 (sealed_iter_spec EN EE g effects ix machine steps Hix Hinv)).
Qed.

Definition sealed_indexed_run {N E T} (EN : encoding N) (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) (ix : sealed_index N E) : sealed_machine N E :=
  let plans := sealed_plans EE g effects ix in
  Pos.iter (sealed_indexed_step EN EE g ix plans) (sealed_initial ix)
    (Pos.of_succ_nat (sealed_capacity ix + length (sealed_nodes ix))).

Lemma sealed_indexed_run_complete {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) ix :
  sealed_index_laws g ix ->
  sealed_invariant EN EE g effects ix (sealed_indexed_run EN EE g effects ix) /\
  sealed_terminal (sealed_indexed_run EN EE g effects ix).
Proof.
  intro Hix; unfold sealed_indexed_run; rewrite sealed_indexed_iter_agrees.
  - apply sealed_run_complete; exact Hix.
  - exact Hix.
  - apply sealed_initial_invariant; exact Hix.
Qed.

(** * Public constructor and same-history correspondence *)

(** Sealed reads produce a completely sealed whole-memory graph with direct construction laws. *)
Definition memory_sealed_build {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
    { mg : memory_graph N E | memory_graph_wf g effects mg }.
Proof.
  set (ix := sealed_prepare EN EE g).
  set (machine := sealed_indexed_run EN EE g effects ix).
  exists (sealed_graph EN EE g (sealed_data machine)).
  pose proof (sealed_prepare_laws EN EE g Hwf) as Hix.
  destruct (sealed_indexed_run_complete EN EE g effects ix Hix) as [Hinv Hdone].
  apply (sealed_graph_well_formed EN EE g effects ix (sealed_data machine) Hix
    (sealed_store_valid Hinv)); [|exact Hwf].
  intros n Hreach; exact (proj2 (sealed_terminal_closed EN EE g effects ix machine n
    Hinv Hdone Hreach)).
Defined.

(** Every entry-rooted path selects the operand of each exact incoming edge. *)
Theorem memory_sealed_path {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es n, In root (Graph.entries g) -> path g root es n ->
    memory_arrival (proj1_sig (memory_sealed_build EN EE g effects Hwf)) root None MemoryLive /\
    memory_path_flow g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf)) root es n.
Proof.
  apply memory_path_correspondence; exact (proj2_sig (memory_sealed_build EN EE g effects Hwf)).
Qed.

(** The same finite history determines the exact dynamic last definition before an occurrence. *)
Theorem memory_sealed_definition_before_occurrence {N E T} (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (Hwf : graph_wf g) :
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin,
    memory_provenance g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf))
      root es (Graph.source g e)
      (memory_in (proj1_sig (memory_sealed_build EN EE g effects Hwf)) (Graph.source g e))
      (memory_last_path effects es) /\
    memory_occurrence_history g effects (proj1_sig (memory_sealed_build EN EE g effects Hwf))
      es e i input origin.
Proof.
  apply memory_definition_before_occurrence.
  exact (proj2_sig (memory_sealed_build EN EE g effects Hwf)).
Qed.
