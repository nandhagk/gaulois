(** * Greedy register colouring

    A colouring assigns bounded colours while spilling vertices that have no available colour.
    For example, the endpoints of one interference edge receive different colours with two colours.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet, GraphInterference. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphInterference.
Import List.ListNotations.

(** A colouring records assigned colours and the vertices left in memory. *)
Record colour_result (V : Type) : Type := ColourResult {
  colours : Map.t V nat;
  spilled : list V
}.
Arguments ColourResult {V}.
Arguments colours {V}.
Arguments spilled {V}.

(** Proper colourings cover the graph, respect edges and preserve every precolour. *)
Record proper_colouring {V} (EV : encoding V) (ig : interference V) (k : nat)
    (pre : Map.t V nat) (res : colour_result V) : Prop := {
  colour_below_k : forall v c, Map.get EV v (colours res) = Some c -> c < k;
  vertex_decided : forall v, FinSet.mem EV v (vertices ig) = true ->
    (exists c, Map.get EV v (colours res) = Some c) \/ In v (spilled res);
  spilled_uncoloured : forall v, In v (spilled res) -> Map.get EV v (colours res) = None;
  adjacent_differ : forall u v cu cv, interferes EV ig u v ->
    Map.get EV u (colours res) = Some cu -> Map.get EV v (colours res) = Some cv -> cu <> cv;
  precoloured_kept : forall v c, Map.get EV v pre = Some c ->
    Map.get EV v (colours res) = Some c
}.
Arguments Build_proper_colouring {V EV ig k pre res}.
Arguments colour_below_k {V EV ig k pre res}.
Arguments vertex_decided {V EV ig k pre res}.
Arguments spilled_uncoloured {V EV ig k pre res}.
Arguments adjacent_differ {V EV ig k pre res}.
Arguments precoloured_kept {V EV ig k pre res}.

(** Valid precolours are in range and differ across every coloured interference edge. *)
Definition precolour_ok {V} (EV : encoding V) (ig : interference V) (k : nat)
    (pre : Map.t V nat) : Prop :=
  (forall v c, Map.get EV v pre = Some c -> c < k) /\
  forall u v cu cv, interferes EV ig u v -> Map.get EV u pre = Some cu ->
    Map.get EV v pre = Some cv -> cu <> cv.

Section Colouring.
Context {V : Type} (EV : encoding V).

Local Definition no_colour (m : Map.t V nat) (v : V) : bool :=
  negb (Map.mem EV v m).

Local Lemma no_colour_spec m v : no_colour m v = true <-> Map.get EV v m = None.
Proof.
  unfold no_colour, Map.mem; destruct (Map.get EV v m); cbn; split; congruence.
Qed.

Local Lemma filter_none (f : V -> bool) vs :
  (forall v, In v vs -> f v = false) -> filter f vs = [].
Proof.
  induction vs as [|v vs IH]; intro Hnone; cbn.
  - reflexivity.
  - rewrite Hnone by (left; reflexivity); apply IH.
    intros u Hin; apply Hnone; right; exact Hin.
Qed.

Local Definition check_range k (m : Map.t V nat) : bool :=
  forallb (fun vc => Nat.ltb (snd vc) k) (Map.elements m).

Local Lemma check_range_spec k m : Map.wf EV m ->
  (check_range k m = true <-> forall v c, Map.get EV v m = Some c -> c < k).
Proof.
  intro Hwf; unfold check_range; rewrite forallb_forall; split.
  - intros Hcheck v c Hget; apply Nat.ltb_lt.
    exact (Hcheck (v, c) (Map.elements_complete EV v c m Hwf Hget)).
  - intros Hbound [v c] Hin; apply Nat.ltb_lt; apply (Hbound v c).
    apply (Map.elements_sound EV); assumption.
Qed.

Local Definition vertex_edges (ig : interference V) (m : Map.t V nat) (u : V) : bool :=
  match Map.get EV u m with
  | None => true
  | Some cu => forallb (fun v =>
      match Map.get EV v m with
      | None => true
      | Some cv => negb (Nat.eqb cu cv)
      end) (FinSet.elements (neighbours EV ig u))
  end.

Local Definition check_edges (ig : interference V) (m : Map.t V nat) : bool :=
  forallb (vertex_edges ig m) (FinSet.elements (vertices ig)).

Local Lemma check_edges_spec ig m : interference_wf EV ig ->
  (check_edges ig m = true <-> forall u v cu cv, interferes EV ig u v ->
    Map.get EV u m = Some cu -> Map.get EV v m = Some cv -> cu <> cv).
Proof.
  intro Hig; unfold check_edges, vertex_edges; rewrite forallb_forall; split.
  - intros Hcheck u v cu cv Hedge Hu Hv.
    specialize (Hcheck u (proj2 (FinSet.elements_spec EV u (vertices ig)
      (vertices_wf Hig)) (interferes_vertex Hig u v Hedge))).
    rewrite Hu in Hcheck; apply forallb_forall with (x := v) in Hcheck.
    + rewrite Hv, negb_true_iff, Nat.eqb_neq in Hcheck; exact Hcheck.
    + apply (FinSet.elements_spec EV); [apply (neighbours_wf Hig)|exact Hedge].
  - intros Hedges u Hu; destruct (Map.get EV u m) as [cu|] eqn:Hget; [|reflexivity].
    apply forallb_forall; intros v Hv.
    destruct (Map.get EV v m) as [cv|] eqn:Hother; [|reflexivity].
    apply negb_true_iff; apply Nat.eqb_neq; apply (Hedges u v cu cv); try assumption.
    apply (FinSet.elements_spec EV); [apply (neighbours_wf Hig)|exact Hv].
Qed.

Local Definition check_kept (pre m : Map.t V nat) : bool :=
  forallb (fun vc =>
    match Map.get EV (fst vc) m with
    | Some c => Nat.eqb (snd vc) c
    | None => false
    end) (Map.elements pre).

Local Lemma check_kept_spec pre m : Map.wf EV pre ->
  (check_kept pre m = true <-> forall v c, Map.get EV v pre = Some c ->
    Map.get EV v m = Some c).
Proof.
  intro Hpre; unfold check_kept; rewrite forallb_forall; split.
  - intros Hcheck v c Hget.
    specialize (Hcheck (v, c) (Map.elements_complete EV v c pre Hpre Hget)); cbn in Hcheck.
    destruct (Map.get EV v m) as [d|]; [|discriminate].
    apply Nat.eqb_eq in Hcheck; subst d; reflexivity.
  - intros Hkept [v c] Hin; cbn.
    rewrite (Hkept v c (Map.elements_sound EV v c pre Hpre Hin)); apply Nat.eqb_refl.
Qed.

Local Lemma forallb_conjunction (p q : V -> bool) vs :
  forallb (fun v => p v && q v) vs = true <->
  forallb p vs = true /\ forallb q vs = true.
Proof.
  induction vs as [|v vs IH]; cbn.
  - tauto.
  - rewrite !andb_true_iff, IH; tauto.
Qed.

(** The checker indexes spills and checks coverage and adjacency in one graph pass. *)
Definition check_colouring (ig : interference V) (k : nat) (pre : Map.t V nat)
    (res : colour_result V) : bool :=
  let spill_set := FinSet.of_list EV (spilled res) in
  check_range k (colours res) &&
  forallb (fun v => (Map.mem EV v (colours res) || FinSet.mem EV v spill_set) &&
      vertex_edges ig (colours res) v)
    (FinSet.elements (vertices ig)) &&
  forallb (no_colour (colours res)) (spilled res) &&
  check_kept pre (colours res).

(** The checker accepts exactly proper colourings of a well-formed graph and maps. *)
Theorem check_colouring_correct ig k pre : forall res,
  interference_wf EV ig -> Map.wf EV pre -> Map.wf EV (colours res) ->
  (check_colouring ig k pre res = true <-> proper_colouring EV ig k pre res).
Proof.
  intros res Hig Hpre Hmap; unfold check_colouring; rewrite !andb_true_iff.
  rewrite forallb_conjunction; fold (check_edges ig (colours res)).
  rewrite check_range_spec by exact Hmap.
  rewrite check_edges_spec by exact Hig.
  rewrite check_kept_spec by exact Hpre.
  split.
  - intros [[[Hrange [Hcover Hedges]] Hspill] Hkept]; constructor; try assumption.
    + intros v Hv; apply forallb_forall with (x := v) in Hcover.
      * apply orb_true_iff in Hcover; destruct Hcover as [Hget|Hin].
        -- left; apply Map.mem_spec in Hget.
           destruct (Map.get EV v (colours res)) as [c|]; [exists c; reflexivity|contradiction].
        -- right; apply FinSet.of_list_spec in Hin; exact Hin.
      * apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hv].
    + intros v Hin; apply no_colour_spec; apply forallb_forall with (x := v) in Hspill;
        assumption.
  - intro Hproper; repeat split.
    + exact (colour_below_k Hproper).
    + apply forallb_forall; intros v Hin; apply orb_true_iff.
      apply (FinSet.elements_spec EV) in Hin; [|apply (vertices_wf Hig)].
      destruct (vertex_decided Hproper v Hin) as [[c Hget]|Hspill].
      * left; apply Map.mem_spec; rewrite Hget; discriminate.
      * right; apply FinSet.of_list_spec; exact Hspill.
    + exact (adjacent_differ Hproper).
    + apply forallb_forall; intros v Hin; apply no_colour_spec.
      exact (spilled_uncoloured Hproper v Hin).
    + exact (precoloured_kept Hproper).
Qed.

(** The conservative fallback keeps precolours and spills all other graph vertices. *)
Definition all_spilled (ig : interference V) (pre : Map.t V nat) : colour_result V :=
  ColourResult pre (filter (fun v => negb (Map.mem EV v pre)) (FinSet.elements (vertices ig))).

Local Definition move_partners (index : Map.t V (list V)) (v : V) : list V :=
  match Map.get EV v index with
  | Some partners => partners
  | None => []
  end.

Local Definition index_partner (index : Map.t V (list V)) (u v : V) : Map.t V (list V) :=
  Map.set EV u (v :: move_partners index u) index.

(* Move partners are indexed once, in reverse occurrence order. Selection reads only the
   current vertex's partner list, rather than scanning the complete move list at each step. *)
Local Definition move_index (moves : list (V * V)) : Map.t V (list V) :=
  fold_left (fun index uv =>
    index_partner (index_partner index (fst uv) (snd uv)) (snd uv) (fst uv)) moves Map.empty.

Local Definition neighbour_colours (ig : interference V) (m : Map.t V nat) (v : V)
    : list nat :=
  flat_map (fun u =>
    match Map.get EV u m with
    | Some c => [c]
    | None => []
    end) (FinSet.elements (neighbours EV ig v)).

Local Definition forbidden (ig : interference V) (m : Map.t V nat) (v : V) : FinSet.t nat :=
  FinSet.of_list nat_encoding (neighbour_colours ig m v).

Local Lemma forbidden_spec ig m v c : FinSet.wf EV (neighbours EV ig v) ->
  (FinSet.mem nat_encoding c (forbidden ig m v) = true <->
    exists u, interferes EV ig v u /\ Map.get EV u m = Some c).
Proof.
  intro Hwf; unfold forbidden, neighbour_colours; rewrite FinSet.of_list_spec, in_flat_map.
  split.
  - intros [u [Hu Hc]]; exists u; split.
    + apply (FinSet.elements_spec EV); assumption.
    + destruct (Map.get EV u m) as [d|] eqn:Hget; cbn in Hc; [|contradiction].
      destruct Hc as [Heq|Hfalse]; [subst d; reflexivity|contradiction].
  - intros [u [Hedge Hget]]; exists u; split.
    + apply (FinSet.elements_spec EV); assumption.
    + rewrite Hget; cbn; auto.
Qed.

Local Lemma neighbour_colours_length ig m v :
  length (neighbour_colours ig m v) <= length (FinSet.elements (neighbours EV ig v)).
Proof.
  unfold neighbour_colours; induction (FinSet.elements (neighbours EV ig v)) as [|u us IH].
  - cbn; lia.
  - cbn; destruct (Map.get EV u m); cbn; lia.
Qed.

Local Lemma forbidden_size ig m v :
  FinSet.size (forbidden ig m v) <= FinSet.size (neighbours EV ig v).
Proof.
  unfold forbidden; eapply Nat.le_trans.
  - apply (FinSet.size_le_length nat_encoding _ (neighbour_colours ig m v)).
    + apply FinSet.wf_fold_add; apply Map.wf_empty.
    + intros c Hmem; apply FinSet.of_list_spec in Hmem; exact Hmem.
  - rewrite FinSet.size_elements; apply neighbour_colours_length.
Qed.

Local Definition first_free (k : nat) (blocked : FinSet.t nat) : option nat :=
  find (fun c => negb (FinSet.mem nat_encoding c blocked)) (seq 0 k).

Local Definition choose_colour (k : nat) (blocked : FinSet.t nat) (preferred : option nat)
    : option nat :=
  match preferred with
  | Some c =>
    if Nat.ltb c k && negb (FinSet.mem nat_encoding c blocked)
    then Some c else first_free k blocked
  | None => first_free k blocked
  end.

Local Lemma first_free_sound k blocked c : first_free k blocked = Some c ->
  c < k /\ FinSet.mem nat_encoding c blocked = false.
Proof.
  unfold first_free; intro Hfind; apply find_some in Hfind.
  destruct Hfind as [Hin Hfree]; apply in_seq in Hin; apply negb_true_iff in Hfree.
  split; [lia|exact Hfree].
Qed.

Local Lemma choose_colour_sound k blocked preferred c :
  choose_colour k blocked preferred = Some c ->
  c < k /\ FinSet.mem nat_encoding c blocked = false.
Proof.
  unfold choose_colour; destruct preferred as [p|]; [|apply first_free_sound].
  destruct (Nat.ltb p k && negb (FinSet.mem nat_encoding p blocked)) eqn:Hfree.
  - intro Heq; inversion Heq; subst p; apply andb_true_iff in Hfree.
    destruct Hfree as [Hrange Hfree]; apply Nat.ltb_lt in Hrange.
    apply negb_true_iff in Hfree; auto.
  - apply first_free_sound.
Qed.

Local Lemma first_free_exists k blocked : FinSet.wf nat_encoding blocked ->
  FinSet.size blocked < k -> exists c, first_free k blocked = Some c.
Proof.
  intros Hwf Hsize; destruct (first_free k blocked) as [c|] eqn:Hfind; [eauto|].
  assert (Hincl : incl (seq 0 k) (FinSet.elements blocked)).
  { intros c Hin; apply (FinSet.elements_spec nat_encoding); [exact Hwf|].
    unfold first_free in Hfind; apply find_none with (x := c) in Hfind; [|exact Hin].
    apply negb_false_iff in Hfind; exact Hfind. }
  assert (Hnodup : NoDup (seq 0 k)) by apply seq_NoDup.
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  rewrite length_seq, <- FinSet.size_elements in Hlength; lia.
Qed.

Local Lemma choose_colour_exists k blocked preferred : FinSet.wf nat_encoding blocked ->
  FinSet.size blocked < k -> exists c, choose_colour k blocked preferred = Some c.
Proof.
  intros Hwf Hsize; unfold choose_colour; destruct preferred as [c|].
  - destruct (Nat.ltb c k && negb (FinSet.mem nat_encoding c blocked)).
    + eauto.
    + apply first_free_exists; assumption.
  - apply first_free_exists; assumption.
Qed.

Local Definition preferred_colour (k : nat) (blocked : FinSet.t nat)
    (index : Map.t V (list V)) (m : Map.t V nat) (v : V) : option nat :=
  match find (fun partner =>
    match Map.get EV partner m with
    | Some c => Nat.ltb c k && negb (FinSet.mem nat_encoding c blocked)
    | None => false
    end) (move_partners index v) with
  | Some partner => Map.get EV partner m
  | None => None
  end.

Local Definition colour_step (ig : interference V) (k : nat) (index : Map.t V (list V))
    (m : Map.t V nat) (v : V) : Map.t V nat :=
  match Map.get EV v m with
  | Some _ => m
  | None =>
    let blocked := forbidden ig m v in
    match choose_colour k blocked (preferred_colour k blocked index m v) with
    | Some c => Map.set EV v c m
    | None => m
    end
  end.

Local Fixpoint colour_loop (ig : interference V) (k : nat) (index : Map.t V (list V))
    (order : list V) (m : Map.t V nat) : Map.t V nat :=
  match order with
  | [] => m
  | v :: rest => colour_loop ig k index rest (colour_step ig k index m v)
  end.

(** Greedy selection uses an indexed move preference, then the lowest available colour. *)
Definition greedy_colour (ig : interference V) (k : nat) (pre : Map.t V nat)
    (moves : list (V * V)) (order : list V) : colour_result V :=
  let m := colour_loop ig k (move_index moves) order pre in
  ColourResult m (filter (no_colour m) (FinSet.elements (vertices ig))).

Local Lemma colour_step_keeps ig k index m v u c : Map.get EV u m = Some c ->
  Map.get EV u (colour_step ig k index m v) = Some c.
Proof.
  intro Hget; unfold colour_step; destruct (Map.get EV v m) as [d|] eqn:Hv; [exact Hget|].
  destruct (choose_colour k (forbidden ig m v)
    (preferred_colour k (forbidden ig m v) index m v)); [|exact Hget].
  rewrite Map.get_set_other; [exact Hget|intro Heq; subst u; congruence].
Qed.

Local Lemma colour_loop_keeps ig k index order m u c : Map.get EV u m = Some c ->
  Map.get EV u (colour_loop ig k index order m) = Some c.
Proof.
  revert m; induction order as [|v order IH]; intros m Hget; cbn [colour_loop].
  - exact Hget.
  - apply IH; apply colour_step_keeps; exact Hget.
Qed.

Local Lemma colour_step_wf ig k index m v : Map.wf EV m ->
  Map.wf EV (colour_step ig k index m v).
Proof.
  intro Hwf; unfold colour_step; destruct (Map.get EV v m); [exact Hwf|].
  destruct (choose_colour k (forbidden ig m v)
    (preferred_colour k (forbidden ig m v) index m v));
    [apply Map.wf_set; exact Hwf|exact Hwf].
Qed.

Local Lemma colour_loop_wf ig k index order m : Map.wf EV m ->
  Map.wf EV (colour_loop ig k index order m).
Proof.
  revert m; induction order as [|v order IH]; intros m Hwf; cbn [colour_loop].
  - exact Hwf.
  - apply IH; apply colour_step_wf; exact Hwf.
Qed.

Local Lemma assign_valid ig k m v c : interference_wf EV ig -> precolour_ok EV ig k m ->
  c < k -> FinSet.mem nat_encoding c (forbidden ig m v) = false ->
  precolour_ok EV ig k (Map.set EV v c m).
Proof.
  intros Hig [Hrange Hedges] Hbound Hfree; split.
  - intros u d Hget; destruct (Pos.eq_dec (encode EV u) (encode EV v)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst u; rewrite Map.get_set_same in Hget.
      inversion Hget; subst d; exact Hbound.
    + rewrite Map.get_set_other in Hget; [eapply Hrange; exact Hget|].
      intro Heq; subst u; contradiction.
  - intros u w cu cw Hedge Hu Hw.
    destruct (Pos.eq_dec (encode EV u) (encode EV v)) as [Hu'|Hu'];
      destruct (Pos.eq_dec (encode EV w) (encode EV v)) as [Hw'|Hw'].
    + apply (encode_injective EV) in Hu'; apply (encode_injective EV) in Hw'; subst u w.
      exfalso; exact (interferes_irrefl Hig v Hedge).
    + apply (encode_injective EV) in Hu'; subst u; rewrite Map.get_set_same in Hu.
      inversion Hu; subst cu; rewrite Map.get_set_other in Hw by
        (intro Heq; subst w; contradiction).
      intro Heq; subst cw.
      assert (Hblocked : FinSet.mem nat_encoding c (forbidden ig m v) = true).
      { apply forbidden_spec; [apply (neighbours_wf Hig)|exists w; auto]. }
      congruence.
    + apply (encode_injective EV) in Hw'; subst w; rewrite Map.get_set_same in Hw.
      inversion Hw; subst cw; rewrite Map.get_set_other in Hu by
        (intro Heq; subst u; contradiction).
      intro Heq; subst cu.
      assert (Hblocked : FinSet.mem nat_encoding c (forbidden ig m v) = true).
      { apply forbidden_spec; [apply (neighbours_wf Hig)|].
        exists u; split; [apply (interferes_sym Hig); exact Hedge|exact Hu]. }
      congruence.
    + rewrite Map.get_set_other in Hu by (intro Heq; subst u; contradiction).
      rewrite Map.get_set_other in Hw by (intro Heq; subst w; contradiction).
      exact (Hedges u w cu cw Hedge Hu Hw).
Qed.

Local Lemma colour_step_valid ig k index m v : interference_wf EV ig ->
  precolour_ok EV ig k m -> precolour_ok EV ig k (colour_step ig k index m v).
Proof.
  intros Hig Hvalid; unfold colour_step; destruct (Map.get EV v m); [exact Hvalid|].
  destruct (choose_colour k (forbidden ig m v)
    (preferred_colour k (forbidden ig m v) index m v)) as [c|] eqn:Hchoice;
    [|exact Hvalid].
  destruct (choose_colour_sound _ _ _ _ Hchoice) as [Hbound Hfree].
  apply assign_valid; assumption.
Qed.

Local Lemma colour_loop_valid ig k index order m : interference_wf EV ig ->
  precolour_ok EV ig k m -> precolour_ok EV ig k (colour_loop ig k index order m).
Proof.
  intros Hig; revert m; induction order as [|v order IH]; intros m Hvalid; cbn [colour_loop].
  - exact Hvalid.
  - apply IH; apply colour_step_valid; assumption.
Qed.

(** Greedy output is proper for any covering order and any move preferences. *)
Theorem greedy_colour_proper ig k pre moves order : interference_wf EV ig -> Map.wf EV pre ->
  precolour_ok EV ig k pre ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  proper_colouring EV ig k pre (greedy_colour ig k pre moves order).
Proof.
  intros Hig Hpre Hvalid Horder; unfold greedy_colour.
  set (m := colour_loop ig k (move_index moves) order pre).
  destruct (colour_loop_valid ig k (move_index moves) order pre Hig Hvalid)
    as [Hrange Hedges].
  constructor; cbn [colours spilled]; try assumption.
  - intros v Hv; destruct (Map.get EV v m) as [c|] eqn:Hget.
    + left; exists c; reflexivity.
    + right; apply filter_In; split.
      * apply (FinSet.elements_spec EV); [apply (vertices_wf Hig)|exact Hv].
      * apply no_colour_spec; exact Hget.
  - intros v Hin; apply filter_In in Hin; apply no_colour_spec; exact (proj2 Hin).
  - intros v c Hget; apply colour_loop_keeps; exact Hget.
Qed.

Local Lemma colour_step_decides ig k index m v :
  FinSet.size (neighbours EV ig v) < k ->
  exists c, Map.get EV v (colour_step ig k index m v) = Some c.
Proof.
  intro Hdegree; unfold colour_step; destruct (Map.get EV v m) as [c|] eqn:Hget; [eauto|].
  assert (Hsize : FinSet.size (forbidden ig m v) < k).
  { pose proof (forbidden_size ig m v); lia. }
  destruct (choose_colour_exists k (forbidden ig m v)
    (preferred_colour k (forbidden ig m v) index m v)) as [c Hchoice].
  - unfold forbidden; apply FinSet.wf_fold_add; apply Map.wf_empty.
  - exact Hsize.
  - rewrite Hchoice, Map.get_set_same; eauto.
Qed.

Local Lemma colour_loop_decides ig k index order m :
  (forall v, FinSet.size (neighbours EV ig v) < k) -> forall v, In v order ->
  exists c, Map.get EV v (colour_loop ig k index order m) = Some c.
Proof.
  intro Hdegree; revert m; induction order as [|u order IH]; intros m v Hin; cbn in Hin.
  - contradiction.
  - cbn [colour_loop]; destruct Hin as [Heq|Hin].
    + subst u; destruct (colour_step_decides ig k index m v (Hdegree v)) as [c Hget].
      exists c; apply colour_loop_keeps; exact Hget.
    + apply IH; exact Hin.
Qed.

(** Fewer than [k] neighbours at every vertex ensures that greedy selection never spills. *)
Theorem greedy_no_spill ig k moves order : interference_wf EV ig ->
  (forall v, (FinSet.size (neighbours EV ig v) < k)%nat) ->
  (forall v, FinSet.mem EV v (vertices ig) = true -> In v order) ->
  spilled (greedy_colour ig k Map.empty moves order) = [].
Proof.
  intros Hig Hdegree Horder; unfold greedy_colour; cbn [spilled].
  apply filter_none; intros v Hin.
  apply (FinSet.elements_spec EV) in Hin; [|apply (vertices_wf Hig)].
  destruct (colour_loop_decides ig k (move_index moves) order Map.empty Hdegree v
    (Horder v Hin)) as [c Hget].
  unfold no_colour, Map.mem; rewrite Hget; reflexivity.
Qed.

End Colouring.
