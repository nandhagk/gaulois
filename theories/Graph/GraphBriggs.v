(** * Optimistic register colouring

    Simplification removes low-degree vertices before optimistic spill candidates, and selection
    reuses the greedy move bias in reverse removal order.
    For example, a star simplifies with two colours even when its centre has many neighbours.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet, GraphInterference,
    GraphColour. *)

From Stdlib Require Import List Bool Arith NArith Lia Sorting.Permutation.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphInterference GraphColour.
Import List.ListNotations.

(** A degeneracy witness lists each vertex once, with fewer than [k] later neighbours. *)
Definition degenerate {V} (EV : encoding V) (ig : interference V) (k : nat) : Prop :=
  exists order, NoDup order /\ (forall v, FinSet.mem EV v (vertices ig) = true <-> In v order) /\
    forall l1 v l2, order = l1 ++ v :: l2 ->
      length (filter (fun u => FinSet.mem EV u (neighbours EV ig v)) l2) < k.

Section Briggs.
Context {V : Type} (EV : encoding V).

Local Definition vertex_eq_dec (u v : V) : {u = v} + {u <> v}.
Proof.
  destruct (Pos.eq_dec (encode EV u) (encode EV v)) as [Heq|Hne].
  - left; apply (encode_injective EV); exact Heq.
  - right; intro Heq; subst v; contradiction.
Defined.

Local Definition lookup_set (m : Map.t V (FinSet.t V)) (v : V) : FinSet.t V :=
  match Map.get EV v m with
  | Some s => s
  | None => FinSet.empty
  end.

Local Definition lookup_degree (m : Map.t V nat) (v : V) : nat :=
  match Map.get EV v m with
  | Some d => d
  | None => 0
  end.

Local Definition bucket (bs : Map.t nat (FinSet.t V)) (d : nat) : FinSet.t V :=
  match Map.get nat_encoding d bs with
  | Some s => s
  | None => FinSet.empty
  end.

Local Definition put_bucket (bs : Map.t nat (FinSet.t V)) (d : nat) (v : V)
    : Map.t nat (FinSet.t V) :=
  Map.set nat_encoding d (FinSet.add EV v (bucket bs d)) bs.

Local Definition move_bucket (bs : Map.t nat (FinSet.t V)) (old new : nat) (v : V)
    : Map.t nat (FinSet.t V) :=
  put_bucket (Map.set nat_encoding old (FinSet.remove EV v (bucket bs old)) bs) new v.

(* Buckets retain removed vertices lazily. Both queue selection paths validate membership in
   [active], so those entries never participate in simplification again. *)
Record simplify_state : Type := SimplifyState {
  active : FinSet.t V;
  links : Map.t V (FinSet.t V);
  degree_index : Map.t V nat;
  buckets : Map.t nat (FinSet.t V);
  low : list V;
  candidates : list V;
  select_order : list V
}.

Local Definition degree (s : simplify_state) (v : V) : nat :=
  lookup_degree (degree_index s) v.

Local Definition initial_degrees (ig : interference V) (vs : list V) : Map.t V nat :=
  Map.of_list EV (List.map (fun v => (v, FinSet.size (neighbours EV ig v))) vs).

Local Definition initial_state (ig : interference V) (k : nat) : simplify_state :=
  let vs := FinSet.elements (vertices ig) in
  let ds := initial_degrees ig vs in
  SimplifyState (vertices ig) (adjacent ig) ds
    (fold_left (fun bs v => put_bucket bs (lookup_degree ds v) v) vs Map.empty)
    (filter (fun v => Nat.ltb (lookup_degree ds v) k) vs) vs [].

(* Each local queue entry is consumed once. Refreshing a neighbour may enqueue it again, so
   stale entries cost at most the initial vertices plus the traversed interference edges. *)
Local Fixpoint pop_valid (valid : V -> bool) (queue : list V) : option (V * list V) :=
  match queue with
  | [] => None
  | v :: rest => if valid v then Some (v, rest) else pop_valid valid rest
  end.

Local Definition low_valid (k : nat) (s : simplify_state) (v : V) : bool :=
  FinSet.mem EV v (active s) && Nat.ltb (degree s v) k &&
    FinSet.mem EV v (bucket (buckets s) (degree s v)).

Local Definition pick_vertex (k : nat) (s : simplify_state)
    : option (V * list V * list V) :=
  match pop_valid (low_valid k s) (low s) with
  | Some (v, rest) => Some (v, rest, candidates s)
  | None =>
    match pop_valid (fun v => FinSet.mem EV v (active s)) (candidates s) with
    | Some (v, rest) => Some (v, [], rest)
    | None => None
    end
  end.

Local Definition refresh (k : nat) (v : V) (original : Map.t V (FinSet.t V))
    (original_degrees : Map.t V nat)
    (s : simplify_state) (u : V) : simplify_state :=
  let before := lookup_set original u in
  let after := FinSet.remove EV v before in
  let old := lookup_degree original_degrees u in
  let new := Nat.pred old in
  SimplifyState (active s) (Map.set EV u after (links s))
    (Map.set EV u new (degree_index s)) (move_bucket (buckets s) old new u)
    (if Nat.ltb new k then u :: low s else low s)
    (candidates s) (select_order s).

Local Definition remove_vertex (k : nat) (s : simplify_state) (v : V)
    (lows highs : list V) : simplify_state :=
  fold_left (refresh k v (links s) (degree_index s))
    (FinSet.elements (lookup_set (links s) v))
    (SimplifyState (FinSet.remove EV v (active s)) (links s) (degree_index s) (buckets s)
      lows highs (v :: select_order s)).

Local Definition simplify_step (k : nat) (s : simplify_state) : simplify_state :=
  match pick_vertex k s with
  | Some (v, lows, highs) => remove_vertex k s v lows highs
  | None => s
  end.

(* Binary iteration removes one active vertex at each successful step. The proofs below show
   that exactly [size vertices] steps suffice, including the empty graph. *)
Local Definition simplify (ig : interference V) (k : nat) : simplify_state :=
  N.iter (N.of_nat (FinSet.size (vertices ig))) (simplify_step k) (initial_state ig k).

(** Optimistic simplification selects in reverse removal order with indexed move preferences. *)
Definition briggs_colour (ig : interference V) (k : nat) (pre : Map.t V nat)
    (moves : list (V * V)) : colour_result V :=
  greedy_colour EV ig k pre moves (select_order (simplify ig k)).

(** The wrapper retains accepted candidates and otherwise spills every unprecoloured vertex. *)
Definition colour_checked (ig : interference V) (k : nat) (pre : Map.t V nat)
    (moves : list (V * V)) : colour_result V :=
  let r := briggs_colour ig k pre moves in
  if check_colouring EV ig k pre r then r else all_spilled EV ig pre.

(** * Queue and collection facts *)

Local Lemma pop_valid_some valid queue v rest : pop_valid valid queue = Some (v, rest) ->
  valid v = true /\ In v queue /\
  (forall u, In u queue -> valid u = true -> u <> v -> In u rest).
Proof.
  induction queue as [|u queue IH]; cbn; [discriminate|].
  destruct (valid u) eqn:Hu.
  - intro Heq; inversion Heq; subst u rest; split; [exact Hu|].
    split; [left; reflexivity|].
    intros w [Hsame|Hin] Hw Hne; [congruence|exact Hin].
  - intro Hpop; destruct (IH Hpop) as [Hv [Hin Hrest]].
    split; [exact Hv|]; split; [right; exact Hin|].
    intros w [Heq|Hw] Hvalid Hne; [subst w; congruence|apply Hrest; assumption].
Qed.

Local Lemma pop_valid_none valid queue : pop_valid valid queue = None ->
  forall v, In v queue -> valid v = false.
Proof.
  induction queue as [|u queue IH]; cbn; [tauto|].
  destruct (valid u) eqn:Hu; [discriminate|].
  intros Hpop v [Heq|Hin]; [subst v; exact Hu|apply IH; assumption].
Qed.

Local Lemma lookup_set_set m u v value :
  lookup_set (Map.set EV u value m) v = if vertex_eq_dec v u then value else lookup_set m v.
Proof.
  unfold lookup_set; destruct (vertex_eq_dec v u) as [Heq|Hne].
  - subst v; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma lookup_degree_set m u v value :
  lookup_degree (Map.set EV u value m) v =
    if vertex_eq_dec v u then value else lookup_degree m v.
Proof.
  unfold lookup_degree; destruct (vertex_eq_dec v u) as [Heq|Hne].
  - subst v; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma initial_degrees_agree ig vs u : In u vs ->
  lookup_degree (initial_degrees ig vs) u = FinSet.size (neighbours EV ig u).
Proof.
  unfold initial_degrees, Map.of_list; remember (@Map.empty V nat) as m.
  assert (Hfold : forall todo m,
    (In u todo \/ Map.get EV u m = Some (FinSet.size (neighbours EV ig u))) ->
    Map.get EV u (fold_left (fun m vc => Map.set EV (fst vc) (snd vc) m)
      (List.map (fun v => (v, FinSet.size (neighbours EV ig v))) todo) m) =
      Some (FinSet.size (neighbours EV ig u))).
  { induction todo as [|v todo IH]; intros start Hcover; cbn [List.map fold_left fst snd].
    - destruct Hcover as [Hfalse|Hget]; [contradiction|exact Hget].
    - apply IH; destruct Hcover as [[Heq|Hin]|Hget].
      + subst v; right; apply Map.get_set_same.
      + left; exact Hin.
      + destruct (vertex_eq_dec u v) as [Heq|Hne].
        * subst v; right; apply Map.get_set_same.
        * right; rewrite Map.get_set_other by exact Hne; exact Hget. }
  intro Hin; unfold lookup_degree; rewrite Hfold by (left; exact Hin); reflexivity.
Qed.

Local Lemma bucket_put bs d u e v :
  FinSet.mem EV v (bucket (put_bucket bs d u) e) = true <->
  (e = d /\ v = u) \/ FinSet.mem EV v (bucket bs e) = true.
Proof.
  unfold put_bucket, bucket; destruct (Nat.eq_dec e d) as [Heq|Hne].
  - subst e; rewrite Map.get_set_same, FinSet.mem_add; tauto.
  - rewrite Map.get_set_other by exact Hne; intuition congruence.
Qed.

Local Lemma bucket_move_same bs old new u :
  FinSet.mem EV u (bucket (move_bucket bs old new u) new) = true.
Proof.
  unfold move_bucket; apply bucket_put; left; auto.
Qed.

Local Lemma bucket_move_other bs old new u e v : v <> u ->
  FinSet.mem EV v (bucket (move_bucket bs old new u) e) =
  FinSet.mem EV v (bucket bs e).
Proof.
  intro Hne; apply eq_true_iff_eq; unfold move_bucket; rewrite bucket_put.
  unfold bucket; destruct (Nat.eq_dec e old) as [Heq|Hother].
  - subst e; rewrite Map.get_set_same, FinSet.mem_remove; intuition congruence.
  - rewrite Map.get_set_other by exact Hother; intuition congruence.
Qed.

Local Lemma remove_size s v : FinSet.wf EV s -> FinSet.mem EV v s = true ->
  S (FinSet.size (FinSet.remove EV v s)) = FinSet.size s.
Proof.
  intros Hwf Hv.
  assert (Hperm : Permutation (FinSet.elements s)
    (v :: FinSet.elements (FinSet.remove EV v s))).
  { apply NoDup_Permutation.
    - apply (FinSet.elements_nodup EV); exact Hwf.
    - constructor.
      + intro Hin; apply (FinSet.elements_spec EV) in Hin; [|apply Map.wf_remove; exact Hwf].
        apply FinSet.mem_remove in Hin; tauto.
      + apply (FinSet.elements_nodup EV); apply Map.wf_remove; exact Hwf.
    - intro u; rewrite (FinSet.elements_spec EV) by exact Hwf.
      cbn; rewrite (FinSet.elements_spec EV) by (apply Map.wf_remove; exact Hwf).
      rewrite FinSet.mem_remove; destruct (vertex_eq_dec u v); subst; intuition congruence. }
  pose proof (Permutation_length Hperm); rewrite !FinSet.size_elements; cbn in *; lia.
Qed.

Local Lemma remove_add s v : FinSet.wf EV s -> FinSet.mem EV v s = true ->
  FinSet.add EV v (FinSet.remove EV v s) = s.
Proof.
  intros Hwf Hv; apply (FinSet.extensionality EV).
  - apply Map.wf_set; apply Map.wf_remove; exact Hwf.
  - exact Hwf.
  - intro u; apply eq_true_iff_eq; rewrite FinSet.mem_add, FinSet.mem_remove.
    destruct (vertex_eq_dec u v); subst; intuition congruence.
Qed.

(** * Maintained simplify indexes *)

Local Lemma refresh_fixed k v original ds todo s :
  active (fold_left (refresh k v original ds) todo s) = active s /\
  candidates (fold_left (refresh k v original ds) todo s) = candidates s /\
  select_order (fold_left (refresh k v original ds) todo s) = select_order s.
Proof.
  revert s; induction todo as [|u todo IH]; intro s; cbn; [auto|].
  destruct (IH (refresh k v original ds s u)) as [Ha [Hc Hs]].
  cbn [refresh active candidates select_order] in Ha, Hc, Hs; auto.
Qed.

Local Lemma refresh_links k v original ds todo s u :
  lookup_set (links (fold_left (refresh k v original ds) todo s)) u =
  if in_dec vertex_eq_dec u todo then FinSet.remove EV v (lookup_set original u)
  else lookup_set (links s) u.
Proof.
  revert s; induction todo as [|w todo IH]; intro s; cbn [fold_left].
  - destruct (in_dec vertex_eq_dec u []); [contradiction|reflexivity].
  - rewrite IH; cbn [refresh links]; rewrite lookup_set_set.
    destruct (in_dec vertex_eq_dec u todo) as [Hin|Hnot].
    + destruct (in_dec vertex_eq_dec u (w :: todo)) as [Hall|Hnone]; [reflexivity|].
      exfalso; apply Hnone; right; exact Hin.
    + destruct (vertex_eq_dec u w) as [Heq|Hne].
      * subst w; destruct (in_dec vertex_eq_dec u (u :: todo)) as [Hall|Hnone].
        -- reflexivity.
        -- exfalso; apply Hnone; left; reflexivity.
      * destruct (in_dec vertex_eq_dec u (w :: todo)) as [Hall|Hnone]; [|reflexivity].
        exfalso; destruct Hall as [Heq|Hin]; [congruence|contradiction].
Qed.

Local Lemma refresh_degrees k v original ds todo s u :
  degree (fold_left (refresh k v original ds) todo s) u =
  if in_dec vertex_eq_dec u todo then Nat.pred (lookup_degree ds u) else degree s u.
Proof.
  revert s; induction todo as [|w todo IH]; intro s; cbn [fold_left].
  - destruct (in_dec vertex_eq_dec u []); [contradiction|reflexivity].
  - rewrite IH; unfold degree; cbn [refresh degree_index]; rewrite lookup_degree_set.
    destruct (in_dec vertex_eq_dec u todo) as [Hin|Hnot].
    + destruct (in_dec vertex_eq_dec u (w :: todo)) as [Hall|Hnone]; [reflexivity|].
      exfalso; apply Hnone; right; exact Hin.
    + destruct (vertex_eq_dec u w) as [Heq|Hne].
      * subst w; destruct (in_dec vertex_eq_dec u (u :: todo)) as [Hall|Hnone].
        -- reflexivity.
        -- exfalso; apply Hnone; left; reflexivity.
      * destruct (in_dec vertex_eq_dec u (w :: todo)) as [Hall|Hnone]; [|reflexivity].
        exfalso; destruct Hall as [Heq|Hin]; [congruence|contradiction].
Qed.

Local Lemma refresh_low_keeps k v original ds todo s :
  incl (low s) (low (fold_left (refresh k v original ds) todo s)).
Proof.
  revert s; induction todo as [|u todo IH]; intros s w Hin; cbn [fold_left].
  - exact Hin.
  - apply IH; cbn [refresh low].
    destruct (Nat.ltb (Nat.pred (lookup_degree ds u)) k);
      cbn; auto.
Qed.

Local Lemma refresh_low_adds k v original ds todo s u : In u todo ->
  Nat.pred (lookup_degree ds u) < k ->
  In u (low (fold_left (refresh k v original ds) todo s)).
Proof.
  revert s; induction todo as [|w todo IH]; intros s Hin Hdegree; cbn in Hin.
  - contradiction.
  - cbn [fold_left]; destruct Hin as [Heq|Hin].
    + subst w; apply refresh_low_keeps; cbn [refresh low].
      rewrite (proj2 (Nat.ltb_lt _ _) Hdegree); left; reflexivity.
    + apply IH; assumption.
Qed.

Local Definition bucket_agrees (ig : interference V) (s : simplify_state) : Prop :=
  forall u, FinSet.mem EV u (vertices ig) = true ->
    FinSet.mem EV u (bucket (buckets s) (degree s u)) = true.

Local Lemma refresh_buckets ig k v original ds todo s : bucket_agrees ig s ->
  bucket_agrees ig (fold_left (refresh k v original ds) todo s).
Proof.
  revert s; induction todo as [|w todo IH]; intros s Hbucket; cbn [fold_left].
  - exact Hbucket.
  - apply IH; intros u Hu; unfold degree; cbn [refresh degree_index buckets].
    rewrite lookup_degree_set; destruct (vertex_eq_dec u w) as [Heq|Hne].
    + subst u; apply bucket_move_same.
    + rewrite bucket_move_other by exact Hne; apply Hbucket; exact Hu.
Qed.

Local Lemma refresh_sets k v original ds todo s :
  (forall u, FinSet.wf EV (lookup_set original u)) ->
  (forall u, FinSet.wf EV (lookup_set (links s) u)) ->
  forall u, FinSet.wf EV (lookup_set (links (fold_left (refresh k v original ds) todo s)) u).
Proof.
  intros Horiginal Hsets u; rewrite refresh_links.
  destruct (in_dec vertex_eq_dec u todo).
  - apply Map.wf_remove; apply Horiginal.
  - apply Hsets.
Qed.

(** The internal invariant ties each active adjacency cache to the original graph. *)
Record simplify_valid (ig : interference V) (k : nat) (s : simplify_state) : Prop := {
  active_wf : FinSet.wf EV (active s);
  active_vertex : forall u, FinSet.mem EV u (active s) = true ->
    FinSet.mem EV u (vertices ig) = true;
  links_wf : forall u, FinSet.wf EV (lookup_set (links s) u);
  degrees_agree : forall u, FinSet.mem EV u (active s) = true ->
    degree s u = FinSet.size (lookup_set (links s) u);
  links_agree : forall u, FinSet.mem EV u (active s) = true -> forall w,
    FinSet.mem EV w (lookup_set (links s) u) = true <->
    FinSet.mem EV w (active s) = true /\ interferes EV ig u w;
  buckets_agree : bucket_agrees ig s;
  low_complete : forall u, FinSet.mem EV u (active s) = true -> degree s u < k ->
    In u (low s);
  candidates_complete : forall u, FinSet.mem EV u (active s) = true -> In u (candidates s);
  vertices_covered : forall u, FinSet.mem EV u (vertices ig) = true ->
    FinSet.mem EV u (active s) = true \/ In u (select_order s)
}.

Local Lemma initial_buckets ig (f : V -> nat) vs bs :
  (forall u, FinSet.mem EV u (vertices ig) = true -> In u vs \/
    FinSet.mem EV u (bucket bs (f u)) = true) ->
  forall u, FinSet.mem EV u (vertices ig) = true ->
  FinSet.mem EV u
    (bucket (fold_left (fun bs v => put_bucket bs (f v) v) vs bs) (f u)) = true.
Proof.
  revert bs; induction vs as [|v vs IH]; intros bs Hcover u Hu; cbn [fold_left].
  - destruct (Hcover u Hu) as [Hfalse|Hbucket]; [contradiction|exact Hbucket].
  - apply IH; [|exact Hu]; intros w Hw.
    destruct (Hcover w Hw) as [[Heq|Hin]|Hbucket].
    + subst w; right; apply bucket_put; left; auto.
    + left; exact Hin.
    + right; apply bucket_put; right; exact Hbucket.
Qed.

Local Lemma initial_valid ig k : interference_wf EV ig ->
  simplify_valid ig k (initial_state ig k).
Proof.
  intro Hig; constructor; cbn [initial_state active links candidates select_order low degree].
  - apply (vertices_wf Hig).
  - auto.
  - apply (neighbours_wf Hig).
  - intros u Hu; unfold degree; cbn [initial_state degree_index links].
    apply initial_degrees_agree; apply (FinSet.elements_spec EV).
    + apply (vertices_wf Hig).
    + exact Hu.
  - intros u Hu w; change (interferes EV ig u w <->
      FinSet.mem EV w (vertices ig) = true /\ interferes EV ig u w).
    split; [intro Hedge; split|tauto].
    + apply (interferes_vertex Hig w u); apply (interferes_sym Hig); exact Hedge.
    + exact Hedge.
  - intros u Hu; unfold degree; cbn [initial_state buckets degree_index].
    apply (initial_buckets ig); [|exact Hu]; intros w Hw; left.
    apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hw].
  - intros u Hu Hdegree; apply filter_In; split.
    + apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hu].
    + apply Nat.ltb_lt; exact Hdegree.
  - intros u Hu; apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hu].
  - auto.
Qed.

Local Lemma pick_some ig k s v lows highs : simplify_valid ig k s ->
  pick_vertex k s = Some (v, lows, highs) ->
  FinSet.mem EV v (active s) = true /\
  (forall u, FinSet.mem EV u (active s) = true -> u <> v -> In u highs) /\
  (forall u, FinSet.mem EV u (active s) = true -> degree s u < k -> u <> v -> In u lows).
Proof.
  intros Hvalid; unfold pick_vertex.
  destruct (pop_valid (low_valid k s) (low s)) as [[w rest]|] eqn:Hlow.
  - intro Heq; inversion Heq; subst w rest highs.
    destruct (pop_valid_some _ _ _ _ Hlow) as [Hw [_ Hrest]].
    unfold low_valid in Hw; apply andb_true_iff in Hw; destruct Hw as [Hw _].
    apply andb_true_iff in Hw; destruct Hw as [Hw _]; split; [exact Hw|].
    split; [intros u Hu _; apply (candidates_complete _ _ _ Hvalid); exact Hu|].
    intros u Hu Hdegree Hne; apply Hrest.
    + apply (low_complete _ _ _ Hvalid); assumption.
    + unfold low_valid; rewrite Hu, (proj2 (Nat.ltb_lt _ _) Hdegree).
      rewrite (buckets_agree _ _ _ Hvalid u (active_vertex _ _ _ Hvalid u Hu)); reflexivity.
    + exact Hne.
  - destruct (pop_valid (fun u => FinSet.mem EV u (active s)) (candidates s))
      as [[w rest]|] eqn:Hhigh; [|discriminate].
    intro Heq; inversion Heq; subst w lows rest.
    destruct (pop_valid_some _ _ _ _ Hhigh) as [Hw [_ Hrest]]; split; [exact Hw|].
    split.
    + intros u Hu Hne; apply Hrest.
      * apply (candidates_complete _ _ _ Hvalid); exact Hu.
      * exact Hu.
      * exact Hne.
    + intros u Hu Hdegree Hne; exfalso.
      pose proof (pop_valid_none _ _ Hlow u
        (low_complete _ _ _ Hvalid u Hu Hdegree)) as Hfalse.
      unfold low_valid in Hfalse; rewrite Hu, (proj2 (Nat.ltb_lt _ _) Hdegree) in Hfalse.
      rewrite (buckets_agree _ _ _ Hvalid u (active_vertex _ _ _ Hvalid u Hu)) in Hfalse.
      discriminate.
Qed.

Local Lemma pick_none ig k s : simplify_valid ig k s -> pick_vertex k s = None ->
  forall u, FinSet.mem EV u (active s) = false.
Proof.
  intros Hvalid; unfold pick_vertex.
  destruct (pop_valid (low_valid k s) (low s)) as [[v rest]|]; [discriminate|].
  destruct (pop_valid (fun u => FinSet.mem EV u (active s)) (candidates s))
    as [[v rest]|] eqn:Hhigh; [discriminate|].
  intros _ u; destruct (FinSet.mem EV u (active s)) eqn:Hu; [|reflexivity].
  pose proof (pop_valid_none _ _ Hhigh u (candidates_complete _ _ _ Hvalid u Hu)); congruence.
Qed.

Local Lemma remove_degrees ig k s v lows highs : interference_wf EV ig ->
  simplify_valid ig k s -> FinSet.mem EV v (active s) = true ->
  forall u, FinSet.mem EV u (active (remove_vertex k s v lows highs)) = true ->
    degree (remove_vertex k s v lows highs) u =
      FinSet.size (lookup_set (links (remove_vertex k s v lows highs)) u).
Proof.
  intros Hig Hvalid Hv; unfold remove_vertex.
  set (todo := FinSet.elements (lookup_set (links s) v)).
  set (start := SimplifyState (FinSet.remove EV v (active s)) (links s) (degree_index s) (buckets s)
    lows highs (v :: select_order s)).
  rewrite (proj1 (refresh_fixed k v (links s) (degree_index s) todo start)); cbn [start active].
  intros u Hu; apply FinSet.mem_remove in Hu; destruct Hu as [Huv Hu].
  rewrite refresh_degrees, refresh_links; cbn [start degree degree_index links].
  destruct (in_dec vertex_eq_dec u todo) as [Hin|Hnot].
  - assert (Hvu : FinSet.mem EV v (lookup_set (links s) u) = true).
    { apply (links_agree _ _ _ Hvalid u Hu v); split; [exact Hv|].
      apply (interferes_sym Hig).
      apply (FinSet.elements_spec EV) in Hin; [|apply (links_wf _ _ _ Hvalid)].
      apply (links_agree _ _ _ Hvalid v Hv u) in Hin; exact (proj2 Hin). }
    change (Nat.pred (degree s u) =
      FinSet.size (FinSet.remove EV v (lookup_set (links s) u))).
    rewrite (degrees_agree _ _ _ Hvalid u Hu).
    pose proof (remove_size _ _ (links_wf _ _ _ Hvalid u) Hvu); lia.
  - apply (degrees_agree _ _ _ Hvalid u Hu).
Qed.

Local Lemma remove_links ig k s v lows highs : interference_wf EV ig ->
  simplify_valid ig k s -> FinSet.mem EV v (active s) = true ->
  forall u, FinSet.mem EV u (active (remove_vertex k s v lows highs)) = true -> forall w,
    FinSet.mem EV w (lookup_set (links (remove_vertex k s v lows highs)) u) = true <->
      FinSet.mem EV w (active (remove_vertex k s v lows highs)) = true /\ interferes EV ig u w.
Proof.
  intros Hig Hvalid Hv; unfold remove_vertex.
  set (todo := FinSet.elements (lookup_set (links s) v)).
  set (start := SimplifyState (FinSet.remove EV v (active s)) (links s) (degree_index s) (buckets s)
    lows highs (v :: select_order s)).
  rewrite (proj1 (refresh_fixed k v (links s) (degree_index s) todo start)); cbn [start active].
  intros u Hu w; apply FinSet.mem_remove in Hu; destruct Hu as [Huv Hu].
  rewrite refresh_links; cbn [start links].
  destruct (in_dec vertex_eq_dec u todo) as [Hin|Hnot].
  - rewrite FinSet.mem_remove, (links_agree _ _ _ Hvalid u Hu w), FinSet.mem_remove; tauto.
  - rewrite (links_agree _ _ _ Hvalid u Hu w), FinSet.mem_remove; split.
    + intros [Hw Hedge]; split; [split; [|exact Hw]|exact Hedge].
      intro Heq; subst w; apply Hnot; unfold todo.
      apply (FinSet.elements_spec EV); [apply (links_wf _ _ _ Hvalid)|].
      apply (links_agree _ _ _ Hvalid v Hv u); split; [exact Hu|].
      apply (interferes_sym Hig); exact Hedge.
    + tauto.
Qed.

Local Lemma remove_valid ig k s v lows highs : interference_wf EV ig ->
  simplify_valid ig k s -> pick_vertex k s = Some (v, lows, highs) ->
  simplify_valid ig k (remove_vertex k s v lows highs).
Proof.
  intros Hig Hvalid Hpick.
  destruct (pick_some ig k s v lows highs Hvalid Hpick) as [Hv [Hhigh Hlow]].
  unfold remove_vertex.
  set (todo := FinSet.elements (lookup_set (links s) v)).
  set (start := SimplifyState (FinSet.remove EV v (active s)) (links s) (degree_index s) (buckets s)
    lows highs (v :: select_order s)).
  destruct (refresh_fixed k v (links s) (degree_index s) todo start)
    as [Hactive [Hcandidates Hselect]].
  constructor.
  - rewrite Hactive; cbn [start active]; apply Map.wf_remove; apply (active_wf _ _ _ Hvalid).
  - rewrite Hactive; cbn [start active]; intros u Hu; apply FinSet.mem_remove in Hu.
    apply (active_vertex _ _ _ Hvalid); exact (proj2 Hu).
  - apply refresh_sets; apply (links_wf _ _ _ Hvalid).
  - apply (remove_degrees ig k s v lows highs); assumption.
  - apply (remove_links ig k s v lows highs); assumption.
  - apply refresh_buckets; exact (buckets_agree _ _ _ Hvalid).
  - rewrite Hactive; cbn [start active]; intros u Hu Hdegree.
    apply FinSet.mem_remove in Hu; destruct Hu as [Huv Hu].
    rewrite refresh_degrees in Hdegree; cbn [start degree degree_index] in Hdegree.
    destruct (in_dec vertex_eq_dec u todo) as [Hin|Hnot].
    + apply refresh_low_adds; assumption.
    + apply refresh_low_keeps; cbn [start low]; apply Hlow; assumption.
  - rewrite Hactive, Hcandidates; cbn [start active candidates]; intros u Hu.
    apply FinSet.mem_remove in Hu; apply Hhigh; tauto.
  - rewrite Hactive, Hselect; cbn [start active select_order]; intros u Hu.
    destruct (vertices_covered _ _ _ Hvalid u Hu) as [Hactive_u|Hselected].
    + destruct (vertex_eq_dec u v) as [Heq|Hne].
      * subst u; right; left; reflexivity.
      * left; apply FinSet.mem_remove; auto.
    + right; right; exact Hselected.
Qed.

Local Lemma step_valid ig k s : interference_wf EV ig -> simplify_valid ig k s ->
  simplify_valid ig k (simplify_step k s).
Proof.
  intros Hig Hvalid; unfold simplify_step.
  destruct (pick_vertex k s) as [[[v lows] highs]|] eqn:Hpick.
  - apply remove_valid; assumption.
  - exact Hvalid.
Qed.

Local Lemma step_size ig k s : simplify_valid ig k s ->
  FinSet.size (active (simplify_step k s)) = Nat.pred (FinSet.size (active s)).
Proof.
  intro Hvalid; unfold simplify_step.
  destruct (pick_vertex k s) as [[[v lows] highs]|] eqn:Hpick.
  - unfold remove_vertex; rewrite (proj1 (refresh_fixed _ _ _ _ _ _)); cbn [active].
    pose proof (remove_size (active s) v (active_wf _ _ _ Hvalid)
      (proj1 (pick_some _ _ _ _ _ _ Hvalid Hpick))); lia.
  - assert (Hempty : active s = FinSet.empty).
    { apply (FinSet.extensionality EV); [apply (active_wf _ _ _ Hvalid)|apply Map.wf_empty|].
      intro u; rewrite FinSet.mem_empty; exact (pick_none ig k s Hvalid Hpick u). }
    rewrite Hempty; reflexivity.
Qed.

Local Lemma simplify_valid_final ig k : interference_wf EV ig ->
  simplify_valid ig k (simplify ig k) /\ FinSet.size (active (simplify ig k)) = 0.
Proof.
  intro Hig.
  assert (Hiter : forall n, simplify_valid ig k
      (N.iter n (simplify_step k) (initial_state ig k)) /\
      FinSet.size (active (N.iter n (simplify_step k) (initial_state ig k))) =
        FinSet.size (vertices ig) - N.to_nat n).
  { intro n; induction n using N.peano_ind.
    - cbn; split; [apply initial_valid; exact Hig|lia].
    - rewrite N.iter_succ, N2Nat.inj_succ.
      destruct IHn as [Hvalid Hsize]; split.
      + apply step_valid; assumption.
      + rewrite (step_size ig k _ Hvalid), Hsize; lia. }
  unfold simplify; specialize (Hiter (N.of_nat (FinSet.size (vertices ig)))).
  rewrite Nat2N.id, Nat.sub_diag in Hiter; exact Hiter.
Qed.

Local Lemma simplify_covers ig k : interference_wf EV ig ->
  forall u, FinSet.mem EV u (vertices ig) = true -> In u (select_order (simplify ig k)).
Proof.
  intros Hig u Hu; destruct (simplify_valid_final ig k Hig) as [Hvalid Hsize].
  destruct (vertices_covered _ _ _ Hvalid u Hu) as [Hactive|Hselected]; [|exact Hselected].
  apply (FinSet.elements_spec EV) in Hactive; [|apply (active_wf _ _ _ Hvalid)].
  rewrite FinSet.size_elements in Hsize.
  apply length_zero_iff_nil in Hsize; rewrite Hsize in Hactive; contradiction.
Qed.

(** Chaitin-Briggs selection is proper for every well-formed graph and valid precolouring. *)
Theorem briggs_colour_proper ig k pre moves : interference_wf EV ig -> Map.wf EV pre ->
  precolour_ok EV ig k pre -> proper_colouring EV ig k pre (briggs_colour ig k pre moves).
Proof.
  intros Hig Hpre Hvalid; unfold briggs_colour; apply greedy_colour_proper; try assumption.
  apply simplify_covers; exact Hig.
Qed.

Local Lemma all_spilled_proper ig k pre : interference_wf EV ig ->
  precolour_ok EV ig k pre -> proper_colouring EV ig k pre (all_spilled EV ig pre).
Proof.
  intros Hig [Hrange Hedges]; constructor; cbn [all_spilled colours spilled].
  - exact Hrange.
  - intros u Hu; destruct (Map.get EV u pre) as [c|] eqn:Hget.
    + left; exists c; reflexivity.
    + right; apply filter_In; split.
      * apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hu].
      * unfold Map.mem; rewrite Hget; reflexivity.
  - intros u Hin; apply filter_In in Hin; destruct Hin as [_ Hin]; apply negb_true_iff in Hin.
    unfold Map.mem in Hin; destruct (Map.get EV u pre); congruence.
  - exact Hedges.
  - auto.
Qed.

(** Checker acceptance and the conservative fallback both give a proper result. *)
Theorem colour_checked_proper ig k pre moves : interference_wf EV ig -> Map.wf EV pre ->
  precolour_ok EV ig k pre -> proper_colouring EV ig k pre (colour_checked ig k pre moves).
Proof.
  intros Hig Hpre Hvalid; unfold colour_checked.
  destruct (check_colouring EV ig k pre (briggs_colour ig k pre moves)) eqn:Hcheck.
  - assert (Hwf : Map.wf EV (colours (briggs_colour ig k pre moves))).
    { unfold briggs_colour, greedy_colour; cbn [colours].
      apply GraphColour.colour_loop_wf; exact Hpre. }
    apply (proj1 (check_colouring_correct EV ig k pre _ Hig Hpre Hwf)); exact Hcheck.
  - apply all_spilled_proper; assumption.
Qed.

(** * Degeneracy and safe selection *)

Local Lemma first_active (a : FinSet.t V) vs :
  (exists v, In v vs /\ FinSet.mem EV v a = true) ->
  exists prefix v suffix, vs = prefix ++ v :: suffix /\ FinSet.mem EV v a = true /\
    forall u, In u prefix -> FinSet.mem EV u a = false.
Proof.
  induction vs as [|w vs IH]; intros [u [Hin Hu]]; cbn in Hin; [contradiction|].
  destruct (FinSet.mem EV w a) eqn:Hw.
  - exists [], w, vs; cbn; repeat split; auto; tauto.
  - assert (Htail : exists u, In u vs /\ FinSet.mem EV u a = true).
    { exists u; split; [destruct Hin as [Heq|Hin]; [subst u; congruence|exact Hin]|exact Hu]. }
    destruct (IH Htail) as [prefix [v [suffix [Hvs [Hv Hprefix]]]]].
    exists (w :: prefix), v, suffix; cbn; split; [rewrite Hvs; reflexivity|].
    split; [exact Hv|]; intros x [Heq|Hx]; [subst x; exact Hw|apply Hprefix; exact Hx].
Qed.

Local Lemma active_low_exists ig k s : interference_wf EV ig -> degenerate EV ig k ->
  simplify_valid ig k s -> (exists u, FinSet.mem EV u (active s) = true) ->
  exists v, FinSet.mem EV v (active s) = true /\ degree s v < k.
Proof.
  intros Hig [order [Hnodup [Horder Hdegree]]] Hvalid [u Hu].
  assert (Hex : exists u, In u order /\ FinSet.mem EV u (active s) = true).
  { exists u; split; [apply Horder; apply (active_vertex _ _ _ Hvalid); exact Hu|exact Hu]. }
  destruct (first_active (active s) order Hex)
    as [prefix [v [suffix [Heq [Hv Hprefix]]]]].
  exists v; split; [exact Hv|].
  specialize (Hdegree prefix v suffix Heq).
  assert (Hbound : degree s v <=
    length (filter (fun w => FinSet.mem EV w (neighbours EV ig v)) suffix)).
  { rewrite (degrees_agree _ _ _ Hvalid v Hv); apply (FinSet.size_le_length EV).
    - apply (links_wf _ _ _ Hvalid).
    - intros w Hw; apply (links_agree _ _ _ Hvalid v Hv w) in Hw.
      destruct Hw as [Hw Hedge]; apply filter_In; split; [|exact Hedge].
      assert (Hin : In w order) by (apply Horder; apply (active_vertex _ _ _ Hvalid); exact Hw).
      rewrite Heq in Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Hsame|Hin]].
      + specialize (Hprefix w Hin); congruence.
      + subst w; exfalso; exact (interferes_irrefl Hig v Hedge).
      + exact Hin. }
  lia.
Qed.

Local Lemma pick_low ig k s v lows highs : simplify_valid ig k s ->
  (exists u, FinSet.mem EV u (active s) = true /\ degree s u < k) ->
  pick_vertex k s = Some (v, lows, highs) -> degree s v < k.
Proof.
  intros Hvalid [u [Hu Hdegree]]; unfold pick_vertex.
  assert (Hvalid_u : low_valid k s u = true).
  { unfold low_valid; rewrite Hu, (proj2 (Nat.ltb_lt _ _) Hdegree).
    rewrite (buckets_agree _ _ _ Hvalid u (active_vertex _ _ _ Hvalid u Hu)); reflexivity. }
  destruct (pop_valid (low_valid k s) (low s)) as [[w rest]|] eqn:Hpop.
  - intro Heq; inversion Heq; subst w.
    pose proof (proj1 (pop_valid_some _ _ _ _ Hpop)) as Hv.
    unfold low_valid in Hv; apply andb_true_iff in Hv; destruct Hv as [Hv _].
    apply andb_true_iff in Hv; apply Nat.ltb_lt; exact (proj2 Hv).
  - pose proof (pop_valid_none _ _ Hpop u (low_complete _ _ _ Hvalid u Hu Hdegree)).
    congruence.
Qed.

(* [safe_stack a order] allows any currently coloured domain contained in [a]. Each
   successive choice has fewer than [k] neighbours in that conservative domain. *)
Local Fixpoint safe_stack (ig : interference V) (k : nat) (a : FinSet.t V)
    (order : list V) : Prop :=
  match order with
  | [] => True
  | v :: rest => FinSet.size (FinSet.inter EV (neighbours EV ig v) a) < k /\
      safe_stack ig k (FinSet.add EV v a) rest
  end.

Local Lemma step_safe ig k s : interference_wf EV ig -> degenerate EV ig k ->
  simplify_valid ig k s -> safe_stack ig k (active s) (select_order s) ->
  safe_stack ig k (active (simplify_step k s)) (select_order (simplify_step k s)).
Proof.
  intros Hig Hdeg Hvalid Hsafe; unfold simplify_step.
  destruct (pick_vertex k s) as [[[v lows] highs]|] eqn:Hpick; [|exact Hsafe].
  pose proof (proj1 (pick_some _ _ _ _ _ _ Hvalid Hpick)) as Hv.
  assert (Hdegree : degree s v < k).
  { apply (pick_low ig k s v lows highs Hvalid); [|exact Hpick].
    apply (active_low_exists ig k s); try assumption; exists v; exact Hv. }
  unfold remove_vertex.
  destruct (refresh_fixed k v (links s) (degree_index s)
    (FinSet.elements (lookup_set (links s) v))
    (SimplifyState (FinSet.remove EV v (active s)) (links s) (degree_index s) (buckets s)
      lows highs (v :: select_order s))) as [Ha [_ Ho]].
  rewrite Ha, Ho; cbn [active select_order safe_stack]; split.
  - assert (Hbound : FinSet.size
      (FinSet.inter EV (neighbours EV ig v) (FinSet.remove EV v (active s))) <= degree s v).
    { rewrite (degrees_agree _ _ _ Hvalid v Hv); apply (FinSet.size_subset EV).
      - apply FinSet.wf_inter; [apply (neighbours_wf Hig)|].
        apply Map.wf_remove; apply (active_wf _ _ _ Hvalid).
      - apply (links_wf _ _ _ Hvalid).
      - apply (FinSet.subset_spec EV).
        + apply FinSet.wf_inter; [apply (neighbours_wf Hig)|].
          apply Map.wf_remove; apply (active_wf _ _ _ Hvalid).
        + intros w Hw; apply FinSet.mem_inter in Hw; destruct Hw as [Hedge Hw].
          apply FinSet.mem_remove in Hw; apply (links_agree _ _ _ Hvalid v Hv w); tauto. }
    lia.
  - rewrite (remove_add (active s) v (active_wf _ _ _ Hvalid) Hv); exact Hsafe.
Qed.

Local Lemma simplify_safe ig k : interference_wf EV ig -> degenerate EV ig k ->
  safe_stack ig k FinSet.empty (select_order (simplify ig k)).
Proof.
  intros Hig Hdeg.
  assert (Hiter : forall n, simplify_valid ig k
      (N.iter n (simplify_step k) (initial_state ig k)) /\
      safe_stack ig k (active (N.iter n (simplify_step k) (initial_state ig k)))
        (select_order (N.iter n (simplify_step k) (initial_state ig k)))).
  { intro n; induction n using N.peano_ind.
    - split; [apply initial_valid; exact Hig|exact I].
    - rewrite N.iter_succ; destruct IHn as [Hvalid Hsafe]; split.
      + apply step_valid; assumption.
      + apply step_safe; assumption. }
  specialize (Hiter (N.of_nat (FinSet.size (vertices ig)))); fold (simplify ig k) in Hiter.
  destruct Hiter as [Hvalid Hsafe].
  destruct (simplify_valid_final ig k Hig) as [_ Hsize].
  assert (Hempty : active (simplify ig k) = FinSet.empty).
  { apply (FinSet.extensionality EV); [apply (active_wf _ _ _ Hvalid)|apply Map.wf_empty|].
    intro u; rewrite FinSet.mem_empty.
    destruct (FinSet.mem EV u (active (simplify ig k))) eqn:Hu; [|reflexivity].
    apply (FinSet.elements_spec EV) in Hu; [|apply (active_wf _ _ _ Hvalid)].
    rewrite FinSet.size_elements in Hsize; apply length_zero_iff_nil in Hsize.
    rewrite Hsize in Hu; contradiction. }
  rewrite Hempty in Hsafe; exact Hsafe.
Qed.

Local Lemma forbidden_bound ig a m v : interference_wf EV ig -> FinSet.wf EV a ->
  (forall u c, Map.get EV u m = Some c -> FinSet.mem EV u a = true) ->
  FinSet.size (GraphColour.forbidden EV ig m v) <=
    FinSet.size (FinSet.inter EV (neighbours EV ig v) a).
Proof.
  intros Hig Ha Hdomain.
  set (allowed := FinSet.inter EV (neighbours EV ig v) a).
  assert (Hallowed : FinSet.wf EV allowed).
  { apply FinSet.wf_inter; [apply (neighbours_wf Hig)|exact Ha]. }
  set (values := List.map (fun u =>
    match Map.get EV u m with Some c => c | None => 0 end) (FinSet.elements allowed)).
  assert (Hbound : FinSet.size (GraphColour.forbidden EV ig m v) <= length values).
  { apply (FinSet.size_le_length nat_encoding).
    - unfold GraphColour.forbidden; apply FinSet.wf_fold_add; apply Map.wf_empty.
    - intros c Hc; apply (GraphColour.forbidden_spec EV) in Hc;
        [|apply (neighbours_wf Hig)].
      destruct Hc as [u [Hedge Hget]]; unfold values; apply in_map_iff.
      exists u; split; [rewrite Hget; reflexivity|].
      apply (FinSet.elements_spec EV); [exact Hallowed|].
      unfold allowed; apply FinSet.mem_inter; split; [exact Hedge|eapply Hdomain; exact Hget]. }
  unfold values in Hbound; rewrite length_map, <- FinSet.size_elements in Hbound; exact Hbound.
Qed.

Local Lemma step_domain ig k index m a v :
  (forall u c, Map.get EV u m = Some c -> FinSet.mem EV u a = true) ->
  forall u c, Map.get EV u (GraphColour.colour_step EV ig k index m v) = Some c ->
    FinSet.mem EV u (FinSet.add EV v a) = true.
Proof.
  intros Hdomain u c; unfold GraphColour.colour_step.
  destruct (Map.get EV v m); [intro Hget; apply FinSet.mem_add; right; eapply Hdomain; exact Hget|].
  destruct (GraphColour.choose_colour k (GraphColour.forbidden EV ig m v)
    (GraphColour.preferred_colour EV k (GraphColour.forbidden EV ig m v) index m v)).
  - intro Hget; apply FinSet.mem_add; destruct (vertex_eq_dec u v) as [Heq|Hne].
    + left; exact Heq.
    + right; rewrite Map.get_set_other in Hget by exact Hne; eapply Hdomain; exact Hget.
  - intro Hget; apply FinSet.mem_add; right; eapply Hdomain; exact Hget.
Qed.

Local Lemma step_fills ig k index m a v : interference_wf EV ig -> FinSet.wf EV a ->
  (forall u c, Map.get EV u m = Some c -> FinSet.mem EV u a = true) ->
  FinSet.size (FinSet.inter EV (neighbours EV ig v) a) < k ->
  exists c, Map.get EV v (GraphColour.colour_step EV ig k index m v) = Some c.
Proof.
  intros Hig Ha Hdomain Hdegree; unfold GraphColour.colour_step.
  destruct (Map.get EV v m) as [c|] eqn:Hget; [exists c; exact Hget|].
  destruct (GraphColour.choose_colour_exists k (GraphColour.forbidden EV ig m v)
    (GraphColour.preferred_colour EV k (GraphColour.forbidden EV ig m v) index m v))
      as [c Hchoice].
  - unfold GraphColour.forbidden; apply FinSet.wf_fold_add; apply Map.wf_empty.
  - pose proof (forbidden_bound ig a m v Hig Ha Hdomain); lia.
  - rewrite Hchoice, Map.get_set_same; exists c; reflexivity.
Qed.

Local Lemma safe_selection_total ig k index order a m : interference_wf EV ig ->
  FinSet.wf EV a -> safe_stack ig k a order ->
  (forall u c, Map.get EV u m = Some c -> FinSet.mem EV u a = true) ->
  forall u, In u order ->
    exists c, Map.get EV u (GraphColour.colour_loop EV ig k index order m) = Some c.
Proof.
  intro Hig; revert a m; induction order as [|v order IH]; intros a m Ha Hsafe Hdomain u Hin.
  - contradiction.
  - cbn [safe_stack] in Hsafe; destruct Hsafe as [Hdegree Hsafe].
    cbn [GraphColour.colour_loop]; destruct Hin as [Heq|Hin].
    + subst u; destruct (step_fills ig k index m a v Hig Ha Hdomain Hdegree) as [c Hget].
      exists c; apply GraphColour.colour_loop_keeps; exact Hget.
    + apply (IH (FinSet.add EV v a)).
      * apply Map.wf_set; exact Ha.
      * exact Hsafe.
      * apply step_domain; exact Hdomain.
      * exact Hin.
Qed.

(** A complete low-degree simplification guarantees that selection spills no vertex. *)
Theorem briggs_no_spill ig k moves : interference_wf EV ig -> degenerate EV ig k ->
  spilled (briggs_colour ig k Map.empty moves) = [].
Proof.
  intros Hig Hdeg; unfold briggs_colour, greedy_colour; cbn [spilled].
  apply GraphColour.filter_none; intros v Hin.
  apply (FinSet.elements_spec EV) in Hin; [|apply (vertices_wf Hig)].
  assert (Hdomain : forall u c, Map.get EV u (@Map.empty V nat) = Some c ->
    FinSet.mem EV u FinSet.empty = true).
  { intros u c Hfalse; rewrite Map.get_empty in Hfalse; discriminate. }
  destruct (safe_selection_total ig k (GraphColour.move_index EV moves)
    (select_order (simplify ig k)) FinSet.empty Map.empty Hig (Map.wf_empty EV)
      (simplify_safe ig k Hig Hdeg) Hdomain v (simplify_covers ig k Hig v Hin)) as [c Hget].
  unfold GraphColour.no_colour, Map.mem; rewrite Hget; reflexivity.
Qed.

End Briggs.
