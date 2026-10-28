(** * Depth-first forests

    Explicit frames visit each unblocked node once and record discovery and finishing orders.
    For example, searching 0 to 1 to 0 discovers [0; 1] and finishes [1; 0].
    Builds on: GraphCore, GraphPrepare and Collections maps and finite sets. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
Import List.ListNotations.

(** The search result contains traversal orders, discovery edges and their position indexes. *)
Record dfs_result (V E : Type) : Type := DfsResult {
  preorder : list V;
  postorder : list V;
  tree_edge : Map.t V E;
  pre_num : Map.t V positive;
  post_num : Map.t V positive;
  visited : FinSet.t V
}.
Arguments DfsResult {V E}.
Arguments preorder {V E}.
Arguments postorder {V E}.
Arguments tree_edge {V E}.
Arguments pre_num {V E}.
Arguments post_num {V E}.
Arguments visited {V E}.

(** * Explicit-stack traversal *)

Module DfsState.

(** Orders are accumulated backwards; clocks give the next one-based position. *)
Record t (V E : Type) : Type := Make {
  pre : list V;
  post : list V;
  parent : Map.t V E;
  pre_index : Map.t V positive;
  post_index : Map.t V positive;
  seen : FinSet.t V;
  pre_clock : positive;
  post_clock : positive
}.
Arguments Make {V E}.
Arguments pre {V E}.
Arguments post {V E}.
Arguments parent {V E}.
Arguments pre_index {V E}.
Arguments post_index {V E}.
Arguments seen {V E}.
Arguments pre_clock {V E}.
Arguments post_clock {V E}.

End DfsState.
Import DfsState.

(** The initial state has no discovered vertices and both clocks at one. *)
Definition dfs_initial {V E} : DfsState.t V E :=
  DfsState.Make [] [] Map.empty Map.empty Map.empty FinSet.empty 1%positive 1%positive.

(** Discover a fresh vertex, optionally recording the edge used to enter it. *)
Definition dfs_discover {V E} (EV : encoding V) (v : V) (via : option E)
    (st : DfsState.t V E) : DfsState.t V E :=
  DfsState.Make (v :: pre st) (post st)
    (match via with
     | Some e => Map.set EV v e (parent st)
     | None => parent st
     end)
    (Map.set EV v (pre_clock st) (pre_index st)) (post_index st)
    (FinSet.add EV v (seen st)) (Pos.succ (pre_clock st)) (post_clock st).

(** Finish the vertex at an exhausted frame. *)
Definition dfs_finish {V E} (EV : encoding V) (v : V) (st : DfsState.t V E)
    : DfsState.t V E :=
  DfsState.Make (pre st) (v :: post st) (parent st) (pre_index st)
    (Map.set EV v (post_clock st) (post_index st)) (seen st)
    (pre_clock st) (Pos.succ (post_clock st)).

(** A frame stores its vertex and only the successor edges still to inspect. *)
Definition dfs_stack (V E : Type) : Type := list (V * list E).

(** One transition either pops a finished frame or inspects its next edge. *)
Definition dfs_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V)
    (work : dfs_stack V E * DfsState.t V E) : dfs_stack V E * DfsState.t V E :=
  let '(stack, st) := work in
  match stack with
  | [] => ([], st)
  | (v, []) :: rest => (rest, dfs_finish EV v st)
  | (v, e :: es) :: rest =>
    let w := Graph.target g e in
    if FinSet.mem EV w blocked || FinSet.mem EV w (seen st)
    then ((v, es) :: rest, st)
    else ((w, succ_edges p w) :: (v, es) :: rest, dfs_discover EV w (Some e) st)
  end.

(** Binary blocks stop immediately when their frame stack is empty. *)
Fixpoint dfs_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (n : positive)
    (work : dfs_stack V E * DfsState.t V E) : dfs_stack V E * DfsState.t V E :=
  match fst work with
  | [] => work
  | _ :: _ =>
    match n with
    | xH => dfs_step p blocked work
    | xO k => dfs_run p blocked k (dfs_run p blocked k work)
    | xI k => dfs_step p blocked (dfs_run p blocked k (dfs_run p blocked k work))
    end
  end.

Lemma dfs_iter_empty {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked (st : DfsState.t V E) n :
  Pos.iter (dfs_step p blocked) ([], st) n = ([], st).
Proof.
  induction n using Pos.peano_ind.
  - reflexivity.
  - rewrite Pos.iter_succ, IHn; reflexivity.
Qed.

Lemma dfs_run_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked n work :
  dfs_run p blocked n work = Pos.iter (dfs_step p blocked) work n.
Proof.
  revert work; induction n as [n IH|n IH|]; intros [stack st]; destruct stack as [|frame rest].
  - symmetry; apply dfs_iter_empty.
  - cbn [dfs_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO n)).
  - symmetry; apply dfs_iter_empty.
  - cbn [dfs_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** A fresh root runs with prepared binary fuel; skipped roots consume no traversal fuel. *)
Definition dfs_root {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (blocked : FinSet.t V) (st : DfsState.t V E) (v : V)
    : DfsState.t V E :=
  if FinSet.mem EV v blocked || FinSet.mem EV v (seen st)
  then st
  else snd (dfs_run p blocked (fuel p)
    ([(v, succ_edges p v)], dfs_discover EV v None st)).

(** Search roots in order, starting a depth-first run only for a fresh unblocked root. *)
Definition dfs {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (blocked : FinSet.t V) (roots : list V) : dfs_result V E :=
  let st := fold_left (dfs_root p blocked) roots dfs_initial in
  DfsResult (rev (pre st)) (rev (post st)) (parent st)
    (pre_index st) (post_index st) (seen st).

(** Reverse postorder lists parents before their descendants. *)
Definition rpo {V E} (r : dfs_result V E) : list V := rev (postorder r).

(** A discovery edge makes its source the target's tree parent. *)
Definition tree_parent {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (u v : V) : Prop :=
  exists e, Map.get EV v (tree_edge r) = Some e /\ Graph.source g e = u.

(** Tree ancestry includes the vertex itself. *)
Definition dfs_ancestor {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) : V -> V -> Prop :=
  clos_refl_trans V (tree_parent EV g r).

(** Nested discovery and finishing intervals decide ancestry of visited vertices. *)
Definition ancestor_b {V E} (EV : encoding V) (r : dfs_result V E) (u v : V) : bool :=
  match Map.get EV u (pre_num r), Map.get EV v (pre_num r),
        Map.get EV u (post_num r), Map.get EV v (post_num r) with
  | Some a, Some b, Some c, Some d => Pos.leb a b && Pos.leb d c
  | _, _, _, _ => false
  end.

(** A retreating edge targets its source or an ancestor of its source. *)
Definition retreating {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) (e : E) : Prop :=
  dfs_ancestor EV g r (Graph.target g e) (Graph.source g e).

(** * Discovery and pending-work invariants *)

(** Encoded equality gives a constructive equality decision for vertices. *)
Definition dfs_eq_dec {V} (EV : encoding V) (u v : V) : {u = v} + {u <> v}.
Proof.
  destruct (Pos.eq_dec (encode EV u) (encode EV v)) as [Heq|Hne].
  - left; apply (encode_injective EV); exact Heq.
  - right; intro Heq; subst v; apply Hne; reflexivity.
Defined.

Lemma dfs_mem_add {V} (EV : encoding V) (u v : V) s :
  FinSet.mem EV u (FinSet.add EV v s) =
  if dfs_eq_dec EV u v then true else FinSet.mem EV u s.
Proof.
  destruct (dfs_eq_dec EV u v) as [Heq|Hne].
  - subst v; apply FinSet.mem_add; left; reflexivity.
  - apply eq_true_iff_eq; rewrite FinSet.mem_add; tauto.
Qed.

(** * A decreasing work measure *)

(** Undiscovered vertices pay for discovery, finishing and all of their outgoing edges. *)
Fixpoint dfs_white_work {V E} (EV : encoding V) (g : Graph.t V E)
    (s : FinSet.t V) (vs : list V) : nat :=
  match vs with
  | [] => 0
  | v :: rest =>
    (if FinSet.mem EV v s then 0 else length (Graph.out g v) + 2) +
    dfs_white_work EV g s rest
  end.

Lemma dfs_white_work_other {V E} (EV : encoding V) (g : Graph.t V E) s v vs :
  ~ In v vs ->
  dfs_white_work EV g (FinSet.add EV v s) vs = dfs_white_work EV g s vs.
Proof.
  induction vs as [|w vs IH]; intro Hnot; cbn [dfs_white_work fold_right]; [reflexivity|].
  rewrite dfs_mem_add; destruct (dfs_eq_dec EV w v) as [Heq|Hne].
  - subst w; exfalso; apply Hnot; left; reflexivity.
  - rewrite IH; [reflexivity|intro Hin; apply Hnot; right; exact Hin].
Qed.

Lemma dfs_white_work_add {V E} (EV : encoding V) (g : Graph.t V E) s v vs :
  NoDup vs -> In v vs -> FinSet.mem EV v s = false ->
  dfs_white_work EV g (FinSet.add EV v s) vs + length (Graph.out g v) + 2 =
  dfs_white_work EV g s vs.
Proof.
  intros Hnodup; induction Hnodup as [|w vs Hnot Hnodup IH]; intros Hin Hfresh.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst w; cbn [dfs_white_work fold_right]; rewrite dfs_mem_add, Hfresh.
      destruct (dfs_eq_dec EV v v) as [_|Hne]; [|contradiction].
      rewrite dfs_white_work_other by exact Hnot; lia.
    + cbn [dfs_white_work fold_right]; rewrite dfs_mem_add.
      destruct (dfs_eq_dec EV w v) as [Heq|Hne].
      * subst w; contradiction.
      * specialize (IH Hin Hfresh); destruct (FinSet.mem EV w s); lia.
Qed.

Lemma dfs_white_work_bound {V E} (EV : encoding V) (g : Graph.t V E) s vs :
  dfs_white_work EV g s vs <=
  2 * length vs + fold_right (fun v n => length (Graph.out g v) + n) 0 vs.
Proof.
  induction vs as [|v vs IH]; cbn [dfs_white_work fold_right length].
  - lia.
  - destruct (FinSet.mem EV v s); lia.
Qed.

(** Each open frame pays for its remaining edges and its final pop. *)
Fixpoint dfs_stack_work {V E} (stack : dfs_stack V E) : nat :=
  match stack with
  | [] => 0
  | (_, es) :: rest => length es + 1 + dfs_stack_work rest
  end.

(** This proof measure charges each graph edge only at its source. *)
Definition dfs_work {V E} (EV : encoding V) (g : Graph.t V E)
    (work : dfs_stack V E * DfsState.t V E) : nat :=
  dfs_white_work EV g (seen (snd work)) (Graph.nodes g) + dfs_stack_work (fst work).

(** Previously discovered vertices remain discovered after any transition. *)
Definition dfs_extends {V E} (EV : encoding V) (st st' : DfsState.t V E) : Prop :=
  forall v, FinSet.mem EV v (seen st) = true -> FinSet.mem EV v (seen st') = true.

Lemma dfs_step_extends {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked stack st :
  dfs_extends EV st (snd (dfs_step p blocked (stack, st))).
Proof.
  intros w Hmem; destruct stack as [|[v [|e es]] rest]; cbn [dfs_step]; try exact Hmem.
  destruct (_ || _); cbn [dfs_discover]; [exact Hmem|].
  apply FinSet.mem_add; right; exact Hmem.
Qed.

(** Each edge absent from the remaining suffix has already had its target considered. *)
Definition dfs_pending {V E} (EV : encoding V) (g : Graph.t V E) blocked
    (st : DfsState.t V E) (v : V) (es : list E) : Prop :=
  incl es (Graph.out g v) /\
  forall e, In e (Graph.out g v) ->
    In e es \/ FinSet.mem EV (Graph.target g e) (seen st) = true \/
    FinSet.mem EV (Graph.target g e) blocked = true.

(** Open frames and finished vertices partition the distinct discovery list. *)
Record dfs_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (blocked : FinSet.t V) (roots : list V) (stack : dfs_stack V E)
    (st : DfsState.t V E) : Prop := {
  dfs_seen_pre : forall v, FinSet.mem EV v (seen st) = true <-> In v (pre st);
  dfs_pre_nodup : NoDup (pre st);
  dfs_partition : Permutation (pre st) (map fst stack ++ post st);
  dfs_pre_nodes : incl (pre st) (Graph.nodes g);
  dfs_pre_reachable : forall v, In v (pre st) ->
    reachable (without EV blocked (set_entries g roots)) v;
  dfs_frames : forall v es, In (v, es) stack -> dfs_pending EV g blocked st v es;
  dfs_finished : forall v, In v (post st) -> forall e, In e (Graph.out g v) ->
    FinSet.mem EV (Graph.target g e) (seen st) = true \/
    FinSet.mem EV (Graph.target g e) blocked = true
}.

Lemma dfs_pending_extends {V E} (EV : encoding V) (g : Graph.t V E)
    blocked st st' v es :
  dfs_extends EV st st' -> dfs_pending EV g blocked st v es ->
  dfs_pending EV g blocked st' v es.
Proof.
  intros Hext [Hincl Hdone]; split; [exact Hincl|].
  intros e He; destruct (Hdone e He) as [Hpending|[Hseen|Hblocked]]; auto.
Qed.

Lemma dfs_frame_node {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st v es :
  dfs_invariant EV g blocked roots stack st -> In (v, es) stack ->
  In v (Graph.nodes g) /\ In v (pre st).
Proof.
  intros Hinv Hin.
  assert (Hpre : In v (pre st)).
  { apply (Permutation_in _ (Permutation_sym (dfs_partition _ _ _ _ _ _ Hinv))).
    apply in_or_app; left; apply in_map_iff; exists (v, es); auto. }
  split; [apply (dfs_pre_nodes _ _ _ _ _ _ Hinv); exact Hpre|exact Hpre].
Qed.

Lemma dfs_initial_invariant {V E} (EV : encoding V) (g : Graph.t V E) blocked roots :
  dfs_invariant EV g blocked roots [] (@dfs_initial V E).
Proof.
  constructor; cbn [dfs_initial].
  - intro v; change (FinSet.mem EV v FinSet.empty = true <-> False).
    rewrite FinSet.mem_empty; split; [discriminate|contradiction].
  - constructor.
  - constructor.
  - intros v Hin; contradiction.
  - intros v Hin; contradiction.
  - intros v es Hin; contradiction.
  - intros v Hin; contradiction.
Qed.

Lemma dfs_pending_considered {V E} (EV : encoding V) (g : Graph.t V E)
    blocked st v e es :
  dfs_pending EV g blocked st v (e :: es) ->
  (FinSet.mem EV (Graph.target g e) (seen st) = true \/
    FinSet.mem EV (Graph.target g e) blocked = true) ->
  dfs_pending EV g blocked st v es.
Proof.
  intros [Hincl Hdone] Hconsidered; split.
  - intros a Ha; apply Hincl; right; exact Ha.
  - intros a Ha; destruct (Hdone a Ha) as [[Heq|Hin]|Hfinished]; [subst a|auto|auto].
    right; exact Hconsidered.
Qed.

Lemma dfs_finish_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots v rest st :
  dfs_invariant EV g blocked roots ((v, []) :: rest) st ->
  dfs_invariant EV g blocked roots rest (dfs_finish EV v st).
Proof.
  intros [Hseen Hnodup Hpart Hnodes Hreach Hframes Hfinished].
  constructor; cbn [dfs_finish]; try assumption.
  - change (Permutation (pre st) (map fst rest ++ v :: post st)).
    eapply Permutation_trans; [exact Hpart|]; apply Permutation_middle.
  - intros w edges Hin; apply (Hframes w edges); right; exact Hin.
  - intros w [Heq|Hin] a Ha.
    + subst w; destruct (Hframes v [] (or_introl eq_refl)) as [_ Hdone].
      destruct (Hdone a Ha) as [Hfalse|Hcomplete]; [contradiction|exact Hcomplete].
    + apply (Hfinished w Hin a Ha).
Qed.

Lemma dfs_skip_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots v e es rest st :
  dfs_invariant EV g blocked roots ((v, e :: es) :: rest) st ->
  (FinSet.mem EV (Graph.target g e) (seen st) = true \/
    FinSet.mem EV (Graph.target g e) blocked = true) ->
  dfs_invariant EV g blocked roots ((v, es) :: rest) st.
Proof.
  intros [Hseen Hnodup Hpart Hnodes Hreach Hframes Hfinished] Hconsidered.
  constructor; try assumption; intros w edges [Heq|Hin].
  - inversion Heq; subst w edges; eapply dfs_pending_considered; [|exact Hconsidered].
    apply Hframes; left; reflexivity.
  - apply Hframes; right; exact Hin.
Qed.

Lemma dfs_discover_pending {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots v e es rest st :
  ready EV g p -> dfs_invariant EV g blocked roots ((v, e :: es) :: rest) st ->
  In (Graph.target g e) (Graph.nodes g) ->
  forall w edges,
  In (w, edges) ((Graph.target g e, succ_edges p (Graph.target g e)) :: (v, es) :: rest) ->
  dfs_pending EV g blocked (dfs_discover EV (Graph.target g e) (Some e) st) w edges.
Proof.
  intros [_ [_ Hlaws]] Hinv Htarget w edges [Heq|[Heq|Hin]].
  - inversion Heq; subst w edges; rewrite (succ_agrees Hlaws _ Htarget).
    split; [intros a Ha; exact Ha|intros a Ha; left; exact Ha].
  - inversion Heq; subst w edges; apply dfs_pending_considered with (e := e).
    + eapply dfs_pending_extends; [|apply (dfs_frames _ _ _ _ _ _ Hinv); left; reflexivity].
      intros x Hx; cbn [dfs_discover seen]; apply FinSet.mem_add; right; exact Hx.
    + left; cbn [dfs_discover seen]; apply FinSet.mem_add; left; reflexivity.
  - eapply dfs_pending_extends; [|apply (dfs_frames _ _ _ _ _ _ Hinv); right; exact Hin].
    intros x Hx; cbn [dfs_discover seen]; apply FinSet.mem_add; right; exact Hx.
Qed.

Lemma dfs_discover_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots v e es rest st :
  ready EV g p -> dfs_invariant EV g blocked roots ((v, e :: es) :: rest) st ->
  FinSet.mem EV (Graph.target g e) blocked = false ->
  FinSet.mem EV (Graph.target g e) (seen st) = false ->
  dfs_invariant EV g blocked roots
    ((Graph.target g e, succ_edges p (Graph.target g e)) :: (v, es) :: rest)
    (dfs_discover EV (Graph.target g e) (Some e) st).
Proof.
  intros Hready Hinv Hblocked Hfresh; pose proof Hready as [Hwf [_ Hlaws]].
  destruct (dfs_frame_node EV g blocked roots _ st v (e :: es) Hinv (or_introl eq_refl))
    as [Hvnode Hv].
  destruct (dfs_frames _ _ _ _ _ _ Hinv v (e :: es) (or_introl eq_refl)) as [Hincl _].
  assert (Hedge : In e (Graph.out g v)) by (apply Hincl; left; reflexivity).
  assert (Hsource : Graph.source g e = v) by (eapply out_source; eauto).
  assert (Htarget : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
  pose proof (dfs_discover_pending EV g p blocked roots v e es rest st Hready Hinv Htarget)
    as Hpending.
  destruct Hinv as [Hseen Hnodup Hpart Hnodes Hreach Hframes Hfinished].
  constructor; cbn [dfs_discover pre post seen].
  - intro w; rewrite FinSet.mem_add, Hseen; cbn; intuition congruence.
  - constructor; [intro Hin; apply Hseen in Hin; congruence|exact Hnodup].
  - apply perm_skip; exact Hpart.
  - intros w [Heq|Hin]; [subst w; exact Htarget|apply Hnodes; exact Hin].
  - intros w [Heq|Hin]; [subst w|apply Hreach; exact Hin].
    apply (@reachable_step V E (without EV blocked (set_entries g roots)) e); cbn.
    + rewrite Hsource; apply Hreach; exact Hv.
    + apply filter_In; split; [rewrite Hsource; exact Hedge|rewrite Hblocked; reflexivity].
  - exact Hpending.
  - intros w Hin a Ha; destruct (Hfinished w Hin a Ha) as [Hm|Hb].
    + left; apply FinSet.mem_add; right; exact Hm.
    + right; exact Hb.
Qed.

Lemma dfs_step_invariant {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots stack st :
  ready EV g p -> dfs_invariant EV g blocked roots stack st ->
  dfs_invariant EV g blocked roots (fst (dfs_step p blocked (stack, st)))
    (snd (dfs_step p blocked (stack, st))).
Proof.
  intros Hready Hinv; destruct stack as [|[v [|e es]] rest]; cbn [dfs_step fst snd].
  - exact Hinv.
  - apply dfs_finish_invariant; exact Hinv.
  - destruct (FinSet.mem EV (Graph.target g e) blocked ||
      FinSet.mem EV (Graph.target g e) (seen st)) eqn:Hskip.
    + apply orb_true_iff in Hskip; apply dfs_skip_invariant with (e := e); [exact Hinv|tauto].
    + apply orb_false_iff in Hskip; apply dfs_discover_invariant; tauto.
Qed.

Lemma dfs_step_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots stack st :
  ready EV g p -> dfs_invariant EV g blocked roots stack st -> stack <> [] ->
  dfs_work EV g (dfs_step p blocked (stack, st)) < dfs_work EV g (stack, st).
Proof.
  intros [Hwf [Hunique Hlaws]] Hinv Hnonempty.
  destruct stack as [|[v [|e es]] rest]; [contradiction| |].
  - cbn [dfs_step]; unfold dfs_work; cbn [dfs_stack_work dfs_finish seen fst snd]; lia.
  - assert (Hedge : In e (Graph.out g v)).
    { destruct (dfs_frames _ _ _ _ _ _ Hinv v (e :: es) (or_introl eq_refl)) as [Hi _].
      apply Hi; left; reflexivity. }
    destruct (dfs_frame_node EV g blocked roots _ st v (e :: es) Hinv
      (or_introl eq_refl)) as [Hv _].
    assert (Ht : In (Graph.target g e) (Graph.nodes g)) by (eapply out_target_in; eauto).
    cbn [dfs_step].
    destruct (FinSet.mem EV (Graph.target g e) blocked ||
      FinSet.mem EV (Graph.target g e) (seen st)) eqn:Hskip.
    + unfold dfs_work; cbn [dfs_stack_work fst snd length]; lia.
    + apply orb_false_iff in Hskip; destruct Hskip as [_ Hfresh].
      pose proof (dfs_white_work_add EV g (seen st) (Graph.target g e)
        (Graph.nodes g) (nodes_nodup Hwf) Ht Hfresh) as Hcredit.
      unfold dfs_work; cbn [dfs_stack_work dfs_discover seen fst snd length].
      rewrite (succ_agrees Hlaws _ Ht); lia.
Qed.

Lemma dfs_iter_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots work n :
  ready EV g p -> dfs_invariant EV g blocked roots (fst work) (snd work) ->
  let result := Pos.iter (dfs_step p blocked) work n in
  dfs_invariant EV g blocked roots (fst result) (snd result) /\
  dfs_extends EV (snd work) (snd result) /\
  (fst result = [] \/ dfs_work EV g result + Pos.to_nat n <= dfs_work EV g work).
Proof.
  intros Hready Hinv; induction n using Pos.peano_ind.
  - destruct work as [stack st]; cbn [Pos.iter].
    split; [apply dfs_step_invariant; assumption|].
    split; [apply dfs_step_extends|].
    destruct stack as [|frame rest].
    + left; reflexivity.
    + right; pose proof (dfs_step_decreases EV g p blocked roots (frame :: rest) st
        Hready Hinv ltac:(discriminate)) as Hdecrease.
      change (dfs_work EV g (dfs_step p blocked (frame :: rest, st)) + 1 <=
        dfs_work EV g (frame :: rest, st)).
      rewrite Nat.add_1_r; exact Hdecrease.
  - rewrite Pos.iter_succ.
    destruct (Pos.iter (dfs_step p blocked) work n) as [stack st] eqn:Hrun.
    destruct IHn as [Hstate [Hext Hbound]]; cbn [fst snd] in Hstate, Hext, Hbound.
    split; [apply dfs_step_invariant; assumption|].
    split.
    + intros v Hv; apply (dfs_step_extends EV g p blocked stack st).
      apply Hext; exact Hv.
    + destruct stack as [|frame rest]; [left; reflexivity|].
      destruct Hbound as [Hfalse|Hbound]; [discriminate|].
      right; pose proof (dfs_step_decreases EV g p blocked roots (frame :: rest) st
        Hready Hstate ltac:(discriminate)) as Hdecrease.
      rewrite Pos2Nat.inj_succ, Nat.add_succ_r, <- Nat.add_succ_l.
      eapply Nat.le_trans; [apply Nat.add_le_mono_r; exact Hdecrease|exact Hbound].
Qed.

Lemma dfs_root_start {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots st v :
  ready EV g p -> dfs_invariant EV g blocked roots [] st -> In v roots ->
  In v (Graph.nodes g) -> FinSet.mem EV v blocked = false ->
  FinSet.mem EV v (seen st) = false ->
  dfs_invariant EV g blocked roots [(v, succ_edges p v)] (dfs_discover EV v None st).
Proof.
  intros [_ [_ Hlaws]] [Hs Hn Hp Hnodes Hr Hframes Hfinished] Hroot Hv Hb Hfresh.
  constructor; cbn [dfs_discover pre post seen].
  - intro w; rewrite FinSet.mem_add, Hs; simpl; intuition congruence.
  - constructor; [intro Hin; apply Hs in Hin; congruence|exact Hn].
  - apply perm_skip; exact Hp.
  - intros w [Heq|Hin]; [subst w; exact Hv|apply Hnodes; exact Hin].
  - intros w [Heq|Hin]; [subst w|apply Hr; exact Hin].
    apply reachable_entry; apply filter_In; split; [exact Hroot|rewrite Hb; reflexivity].
  - intros w es [Heq|Hin]; [inversion Heq; subst w es|contradiction].
    rewrite (succ_agrees Hlaws _ Hv); split; [intros e He; exact He|].
    intros e He; left; exact He.
  - intros w Hin e He; destruct (Hfinished w Hin e He) as [Hm|Hb'].
    + left; apply FinSet.mem_add; right; exact Hm.
    + right; exact Hb'.
Qed.

Lemma dfs_root_credit {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) st v :
  ready EV g p -> In v (Graph.nodes g) -> FinSet.mem EV v (seen st) = false ->
  dfs_work EV g ([(v, succ_edges p v)], dfs_discover EV v None st) < Pos.to_nat (fuel p).
Proof.
  intros [Hwf [_ Hlaws]] Hv Hfresh.
  pose proof (dfs_white_work_add EV g (seen st) v (Graph.nodes g)
    (nodes_nodup Hwf) Hv Hfresh) as Hadd.
  pose proof (dfs_white_work_bound EV g (seen st) (Graph.nodes g)) as Htotal.
  unfold dfs_work; cbn [dfs_discover seen dfs_stack_work fst snd length].
  rewrite (succ_agrees Hlaws _ Hv), (fuel_value Hlaws); unfold edge_count; lia.
Qed.

Lemma dfs_root_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots st v :
  ready EV g p -> dfs_invariant EV g blocked roots [] st -> In v roots ->
  In v (Graph.nodes g) ->
  dfs_invariant EV g blocked roots [] (dfs_root p blocked st v) /\
  dfs_extends EV st (dfs_root p blocked st v) /\
  (FinSet.mem EV v (seen (dfs_root p blocked st v)) = true \/
   FinSet.mem EV v blocked = true).
Proof.
  intros Hready Hinv Hroot Hv; unfold dfs_root; rewrite dfs_run_agrees.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (seen st)) eqn:Hskip.
  - split; [exact Hinv|]; split; [intros w Hw; exact Hw|].
    apply orb_true_iff in Hskip; tauto.
  - apply orb_false_iff in Hskip; destruct Hskip as [Hb Hfresh].
    pose proof (dfs_root_start EV g p blocked roots st v Hready Hinv Hroot Hv Hb Hfresh)
      as Hstart.
    pose proof (dfs_iter_spec EV g p blocked roots
      ([(v, succ_edges p v)], dfs_discover EV v None st) (fuel p) Hready Hstart)
      as [Hstate [Hext Hbound]].
    pose proof (dfs_root_credit EV g p st v Hready Hv Hfresh) as Hcredit.
    destruct (Pos.iter (dfs_step p blocked)
      ([(v, succ_edges p v)], dfs_discover EV v None st) (fuel p)) as [stack st'].
    cbn in Hstate, Hext, Hbound; destruct Hbound as [Hempty|Hfalse]; [subst stack|lia].
    split; [exact Hstate|]; split.
    + intros w Hw; apply Hext; cbn [dfs_discover seen].
      apply FinSet.mem_add; right; exact Hw.
    + left; apply Hext; cbn [dfs_discover seen]; apply FinSet.mem_add; left; reflexivity.
Qed.

Lemma dfs_fold_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots todo st :
  ready EV g p -> incl roots (Graph.nodes g) -> incl todo roots ->
  dfs_invariant EV g blocked roots [] st ->
  let st' := fold_left (dfs_root p blocked) todo st in
  dfs_invariant EV g blocked roots [] st' /\ dfs_extends EV st st' /\
  forall v, In v todo -> FinSet.mem EV v (seen st') = true \/ FinSet.mem EV v blocked = true.
Proof.
  intros Hready Hnodes; revert st.
  induction todo as [|v todo IH]; intros st Htodo Hinv; cbn [fold_left].
  - split; [exact Hinv|]; split; [intros w Hw; exact Hw|intros w Hin; contradiction].
  - destruct (dfs_root_spec EV g p blocked roots st v Hready Hinv
      (Htodo v (or_introl eq_refl)) (Hnodes v (Htodo v (or_introl eq_refl))))
      as [Hroot [Hext Hvisited]].
    destruct (IH (dfs_root p blocked st v) ltac:(intros w Hw; apply Htodo; right; exact Hw)
      Hroot) as [Hfinal [Hmore Hdone]].
    split; [exact Hfinal|]; split.
    + intros w Hw; apply Hmore; apply Hext; exact Hw.
    + intros w [Heq|Hin].
      * subst w; destruct Hvisited as [Hmem|Hb]; [left; apply Hmore; exact Hmem|auto].
      * apply Hdone; exact Hin.
Qed.

Lemma dfs_closed_reachable {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st :
  dfs_invariant EV g blocked roots [] st ->
  (forall v, In v roots -> FinSet.mem EV v (seen st) = true \/
    FinSet.mem EV v blocked = true) ->
  forall v, reachable (without EV blocked (set_entries g roots)) v ->
    FinSet.mem EV v (seen st) = true.
Proof.
  intros Hinv Hroots v Hreach.
  induction Hreach as [v Hin|e Hreach IH Hin].
  - apply filter_In in Hin; destruct Hin as [Hin Hb].
    apply negb_true_iff in Hb; destruct (Hroots v Hin); congruence.
  - apply filter_In in Hin; destruct Hin as [Hin Hb].
    apply negb_true_iff in Hb.
    change (FinSet.mem EV (Graph.target g e) blocked = false) in Hb.
    change (FinSet.mem EV (Graph.target g e) (seen st) = true).
    assert (Hpost : In (Graph.source g e) (post st)).
    { apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in IH.
      exact (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv) IH). }
    destruct (dfs_finished _ _ _ _ _ _ Hinv _ Hpost e Hin); congruence.
Qed.

(** Search visits exactly the unblocked reachable vertices once, with matching finishing order. *)
Theorem dfs_exact {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (v : V) (roots : list V) (blocked : FinSet.t V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  (FinSet.mem EV v (visited (dfs p blocked roots)) = true <->
   reachable (without EV blocked (set_entries g roots)) v) /\
  NoDup (preorder (dfs p blocked roots)) /\
  Permutation (preorder (dfs p blocked roots)) (postorder (dfs p blocked roots)) /\
  (In v (preorder (dfs p blocked roots)) <->
   FinSet.mem EV v (visited (dfs p blocked roots)) = true).
Proof.
  intros Hready Hroots.
  destruct (dfs_fold_spec EV g p blocked roots roots dfs_initial Hready Hroots
    ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots))
    as [Hinv [_ Hdone]].
  unfold dfs; cbn [preorder postorder visited].
  split.
  - split.
    + intro Hmem; apply (dfs_pre_reachable _ _ _ _ _ _ Hinv).
      apply (dfs_seen_pre _ _ _ _ _ _ Hinv); exact Hmem.
    + apply dfs_closed_reachable; assumption.
  - split.
    + apply NoDup_rev; apply (dfs_pre_nodup _ _ _ _ _ _ Hinv).
    + split.
      * apply Permutation_rev'; exact (dfs_partition _ _ _ _ _ _ Hinv).
      * rewrite <- in_rev; symmetry; apply (dfs_seen_pre _ _ _ _ _ _ Hinv).
Qed.

Lemma dfs_empty_reachable {V E} (EV : encoding V) (g : Graph.t V E) v :
  reachable (without EV FinSet.empty g) v <-> reachable g v.
Proof.
  split; intro Hreach.
  - induction Hreach as [v Hin|e Hreach IH Hin].
    + apply reachable_entry; apply filter_In in Hin; tauto.
    + apply (@reachable_step V E g e); [exact IH|]. apply filter_In in Hin; tauto.
  - induction Hreach as [v Hin|e Hreach IH Hin].
    + apply reachable_entry; apply filter_In; split; [exact Hin|].
      rewrite FinSet.mem_empty; reflexivity.
    + apply (@reachable_step V E (without EV FinSet.empty g) e); [exact IH|].
      apply filter_In; split; [exact Hin|rewrite FinSet.mem_empty; reflexivity].
Qed.

(** Plain search from graph entries visits exactly the reachable vertices. *)
Theorem reachable_dfs {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (v : V) :
  ready EV g p ->
  (FinSet.mem EV v (visited (dfs p FinSet.empty (Graph.entries g))) = true <-> reachable g v).
Proof.
  intro Hready; pose proof Hready as [Hwf _].
  destruct (dfs_exact EV g p v (Graph.entries g) FinSet.empty Hready
    (entries_in Hwf)) as [Hexact _].
  rewrite Hexact, dfs_empty_reachable.
  destruct g; reflexivity.
Qed.

(** * Position indexes and discovery edges *)

(** Numbering records successive insertion of fresh vertices, newest first. *)
Inductive dfs_numbering {V} (EV : encoding V)
    : list V -> Map.t V positive -> positive -> Prop :=
  | DfsNumberingEmpty : dfs_numbering EV [] Map.empty 1%positive
  | DfsNumberingAdd : forall xs m next v,
      dfs_numbering EV xs m next -> ~ In v xs ->
      dfs_numbering EV (v :: xs) (Map.set EV v next m) (Pos.succ next).

Lemma dfs_numbering_size {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> Pos.to_nat next = S (length xs).
Proof.
  intro Hnum; induction Hnum; [reflexivity|].
  rewrite Pos2Nat.inj_succ; cbn [length]; lia.
Qed.

Lemma dfs_numbering_nodup {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> NoDup xs.
Proof.
  intro Hnum; induction Hnum; constructor; assumption.
Qed.

Lemma dfs_numbering_domain {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall v, (exists k, Map.get EV v m = Some k) <-> In v xs.
Proof.
  intro Hnum; induction Hnum as [|xs m next w Hnum IH Hfresh]; intro v.
  - rewrite Map.get_empty; simpl; split; [intros [k Hk]; discriminate|contradiction].
  - destruct (dfs_eq_dec EV v w) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same; simpl; split; [auto|intros _; eauto].
    + rewrite Map.get_set_other by exact Hne; rewrite IH; simpl; intuition congruence.
Qed.

Lemma dfs_numbering_bound {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall v k, Map.get EV v m = Some k -> Pos.lt k next.
Proof.
  intro Hnum; induction Hnum as [|xs m next w Hnum IH Hfresh]; intros v k Hget.
  - rewrite Map.get_empty in Hget; discriminate.
  - destruct (dfs_eq_dec EV v w) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same in Hget; inversion Hget; apply Pos.lt_succ_diag_r.
    + rewrite Map.get_set_other in Hget by exact Hne.
      eapply Pos.lt_trans; [apply (IH v k Hget)|apply Pos.lt_succ_diag_r].
Qed.

Lemma dfs_numbering_position {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall v k, Map.get EV v m = Some k ->
  exists newer older, xs = newer ++ v :: older /\ Pos.to_nat k = S (length older).
Proof.
  intro Hnum; induction Hnum as [|xs m next w Hnum IH Hfresh]; intros v k Hget.
  - rewrite Map.get_empty in Hget; discriminate.
  - destruct (dfs_eq_dec EV v w) as [Heq|Hne].
    + subst v; rewrite Map.get_set_same in Hget; inversion Hget; subst k.
      exists [], xs; split; [reflexivity|apply (dfs_numbering_size EV xs m next Hnum)].
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (IH v k Hget) as [newer [older [Heq Hpos]]].
      exists (w :: newer), older; split; [cbn; rewrite Heq; reflexivity|exact Hpos].
Qed.

Lemma dfs_numbering_nth {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall v k, Map.get EV v m = Some k ->
  nth_error (rev xs) (Nat.pred (Pos.to_nat k)) = Some v.
Proof.
  intros Hnum v k Hget.
  destruct (dfs_numbering_position EV xs m next Hnum v k Hget)
    as [newer [older [Heq Hpos]]].
  rewrite Heq, rev_app_distr; cbn [rev]; rewrite <- app_assoc, Hpos; cbn [Nat.pred].
  rewrite <- length_rev at 1; rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag; reflexivity.
Qed.

Lemma dfs_before_indices {V} (xs : list V) u v :
  before xs u v <-> exists i j,
    i < j /\ nth_error xs i = Some u /\ nth_error xs j = Some v.
Proof.
  split.
  - intros [first [middle [last Heq]]]; subst xs.
    exists (length first), (length first + S (length middle)); split; [lia|]; split.
    + rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
    + rewrite nth_error_app2 by lia.
      replace (length first + S (length middle) - length first) with (S (length middle))
        by lia.
      cbn [nth_error]; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity.
  - intros [i [j [Hlt [Hu Hv]]]]; revert xs j Hlt Hu Hv.
    induction i as [|i IH]; intros [|w xs] [|j] Hlt Hu Hv; try discriminate; try lia.
    + cbn [nth_error] in Hu, Hv; inversion Hu; subst w.
      destruct (nth_error_split xs j Hv) as [middle [last [Heq _]]].
      exists [], middle, last; cbn; rewrite Heq; reflexivity.
    + cbn [nth_error] in Hu, Hv.
      destruct (IH xs j ltac:(lia) Hu Hv) as [first [middle [last Heq]]].
      exists (w :: first), middle, last; cbn; rewrite Heq; reflexivity.
Qed.

Lemma dfs_numbering_order {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall u v a b,
  Map.get EV u m = Some a -> Map.get EV v m = Some b ->
  (before (rev xs) u v <-> Pos.lt a b).
Proof.
  intros Hnum u v a b Hu Hv.
  pose proof (dfs_numbering_nth EV xs m next Hnum u a Hu) as Hna.
  pose proof (dfs_numbering_nth EV xs m next Hnum v b Hv) as Hnb.
  pose proof (NoDup_rev (dfs_numbering_nodup EV xs m next Hnum)) as Hnodup.
  pose proof (Pos2Nat.is_pos a) as Ha; pose proof (Pos2Nat.is_pos b) as Hb.
  rewrite dfs_before_indices, Pos2Nat.inj_lt; split.
  - intros [i [j [Hij [Hi Hj]]]].
    assert (Hia : i = Nat.pred (Pos.to_nat a)).
    { apply (proj1 (NoDup_nth_error _) Hnodup); [apply nth_error_Some; congruence|congruence]. }
    assert (Hjb : j = Nat.pred (Pos.to_nat b)).
    { apply (proj1 (NoDup_nth_error _) Hnodup); [apply nth_error_Some; congruence|congruence]. }
    lia.
  - intro Hlt; exists (Nat.pred (Pos.to_nat a)), (Nat.pred (Pos.to_nat b)).
    split; [lia|]; split; assumption.
Qed.

(** Labels connect every discovery edge to two numbered vertices and the original graph. *)
Record dfs_labels {V E} (EV : encoding V) (g : Graph.t V E) (roots : list V)
    (st : DfsState.t V E) : Prop := {
  dfs_pre_numbering : dfs_numbering EV (pre st) (pre_index st) (pre_clock st);
  dfs_post_numbering : dfs_numbering EV (post st) (post_index st) (post_clock st);
  dfs_parent_labels : forall v e, Map.get EV v (parent st) = Some e ->
    In v (pre st) /\ In (Graph.source g e) (pre st) /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
    exists a b, Map.get EV (Graph.source g e) (pre_index st) = Some a /\
      Map.get EV v (pre_index st) = Some b /\ Pos.lt a b;
  dfs_root_labels : forall v, In v (pre st) -> Map.get EV v (parent st) = None -> In v roots
}.

Lemma dfs_parent_absent {V E} (EV : encoding V) (g : Graph.t V E) roots st v :
  dfs_labels EV g roots st -> ~ In v (pre st) -> Map.get EV v (parent st) = None.
Proof.
  intros Hlabels Hfresh; destruct (Map.get EV v (parent st)) as [e|] eqn:Hget;
    [|reflexivity].
  destruct (dfs_parent_labels _ _ _ _ Hlabels v e Hget) as [Hin _]; contradiction.
Qed.

Lemma dfs_discover_labels {V E} (EV : encoding V) (g : Graph.t V E) roots st v via :
  dfs_labels EV g roots st -> ~ In v (pre st) ->
  (match via with
   | None => In v roots
   | Some e => In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
       In (Graph.source g e) (pre st)
   end) ->
  dfs_labels EV g roots (dfs_discover EV v via st).
Proof.
  intros Hlabels Hfresh Hvia.
  pose proof (dfs_parent_absent EV g roots st v Hlabels Hfresh) as Hnone.
  destruct Hlabels as [Hpre Hpost Hparents Hroots].
  constructor; cbn [dfs_discover pre post pre_index post_index pre_clock post_clock parent].
  - constructor; assumption.
  - exact Hpost.
  - intros w e Hget; destruct via as [a|].
    + destruct (dfs_eq_dec EV w v) as [Heq|Hne].
      * subst w; rewrite Map.get_set_same in Hget; inversion Hget; subst e.
        destruct Hvia as [Hedge [Htarget Hsource]].
        split; [left; reflexivity|]; split; [right; exact Hsource|].
        split; [exact Hedge|]; split; [exact Htarget|].
        destruct (proj2 (dfs_numbering_domain EV _ _ _ Hpre _) Hsource) as [k Hk].
        exists k, (pre_clock st); split.
        -- rewrite Map.get_set_other; [exact Hk|intro Heq; rewrite Heq in Hsource; contradiction].
        -- split; [apply Map.get_set_same|apply (dfs_numbering_bound EV _ _ _ Hpre _ _ Hk)].
      * rewrite Map.get_set_other in Hget by exact Hne.
        destruct (Hparents w e Hget) as [Hw [Hs [He [Ht [a' [b' [Ha [Hb Hlt]]]]]]]].
        split; [right; exact Hw|]; split; [right; exact Hs|]; split; [exact He|].
        split; [exact Ht|]; exists a', b'; split.
        -- rewrite Map.get_set_other; [exact Ha|intro Heq; rewrite Heq in Hs; contradiction].
        -- rewrite Map.get_set_other by exact Hne; auto.
    + destruct (Hparents w e Hget) as [Hw [Hs [He [Ht [a [b [Ha [Hb Hlt]]]]]]]].
      split; [right; exact Hw|]; split; [right; exact Hs|]; split; [exact He|].
      split; [exact Ht|]; exists a, b; split.
      * rewrite Map.get_set_other; [exact Ha|intro Heq; rewrite Heq in Hs; contradiction].
      * rewrite Map.get_set_other; [auto|intro Heq; rewrite Heq in Hw; contradiction].
  - intros w [Heq|Hw] Hget.
    + subst w; destruct via as [e|]; [rewrite Map.get_set_same in Hget; discriminate|exact Hvia].
    + apply Hroots; [exact Hw|].
      destruct via as [e|]; [rewrite Map.get_set_other in Hget|]; try exact Hget.
      intro Heq; subst w; contradiction.
Qed.

Lemma dfs_nodup_disjoint {V} (xs ys : list V) :
  NoDup (xs ++ ys) -> forall v, In v xs -> ~ In v ys.
Proof.
  intro Hnodup; induction xs as [|w xs IH]; intros v Hin; [contradiction|].
  inversion Hnodup as [|w' rest Hnot Htail]; subst w' rest.
  destruct Hin as [Heq|Hin].
  - subst v; intro Hy; apply Hnot; apply in_or_app; right; exact Hy.
  - apply IH; assumption.
Qed.

Lemma dfs_frame_not_finished {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st v es :
  dfs_invariant EV g blocked roots stack st -> In (v, es) stack -> ~ In v (post st).
Proof.
  intros Hinv Hin; eapply dfs_nodup_disjoint.
  - apply (Permutation_NoDup (dfs_partition _ _ _ _ _ _ Hinv)).
    apply (dfs_pre_nodup _ _ _ _ _ _ Hinv).
  - apply in_map_iff; exists (v, es); auto.
Qed.

Lemma dfs_finish_labels {V E} (EV : encoding V) (g : Graph.t V E) roots st v :
  dfs_labels EV g roots st -> ~ In v (post st) -> dfs_labels EV g roots (dfs_finish EV v st).
Proof.
  intros [Hpre Hpost Hparent Hroot] Hfresh.
  constructor; cbn [dfs_finish pre post pre_index post_index pre_clock post_clock parent].
  - exact Hpre.
  - constructor; assumption.
  - exact Hparent.
  - exact Hroot.
Qed.

Lemma dfs_step_labels {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots stack st :
  ready EV g p -> dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  dfs_labels EV g roots (snd (dfs_step p blocked (stack, st))).
Proof.
  intros [Hwf [_ Hlaws]] Hinv Hlabels.
  destruct stack as [|[v [|e es]] rest]; cbn [dfs_step snd]; [exact Hlabels| |].
  - apply dfs_finish_labels; [exact Hlabels|].
    eapply dfs_frame_not_finished; [exact Hinv|left; reflexivity].
  - destruct (FinSet.mem EV (Graph.target g e) blocked ||
      FinSet.mem EV (Graph.target g e) (seen st)) eqn:Hskip; [exact Hlabels|].
    apply dfs_discover_labels; [exact Hlabels| |].
    + apply orb_false_iff in Hskip; destruct Hskip as [_ Hfresh].
      intro Hin; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hin; congruence.
    + destruct (dfs_frames _ _ _ _ _ _ Hinv v (e :: es) (or_introl eq_refl)) as [Hi _].
      assert (He : In e (Graph.out g v)) by (apply Hi; left; reflexivity).
      assert (Hs : Graph.source g e = v) by (eapply out_source; eauto).
      split; [rewrite Hs; exact He|]; split; [reflexivity|].
      rewrite Hs; apply (dfs_frame_node EV g blocked roots _ st v (e :: es) Hinv
        (or_introl eq_refl)).
Qed.

Lemma dfs_initial_labels {V E} (EV : encoding V) (g : Graph.t V E) roots :
  dfs_labels EV g roots (@dfs_initial V E).
Proof.
  constructor; cbn [dfs_initial pre post pre_index post_index pre_clock post_clock parent].
  - constructor.
  - constructor.
  - intros v e Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v Hin; contradiction.
Qed.

Lemma dfs_root_labels_preserved {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots st v :
  ready EV g p -> dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st ->
  In v roots -> In v (Graph.nodes g) -> dfs_labels EV g roots (dfs_root p blocked st v).
Proof.
  intros Hready Hinv Hlabels Hroot Hv; unfold dfs_root; rewrite dfs_run_agrees.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (seen st)) eqn:Hskip;
    [exact Hlabels|].
  apply orb_false_iff in Hskip; destruct Hskip as [Hb Hfresh].
  assert (Hstart : dfs_invariant EV g blocked roots [(v, succ_edges p v)]
    (dfs_discover EV v None st) /\ dfs_labels EV g roots (dfs_discover EV v None st)).
  { split.
    - apply dfs_root_start; assumption.
    - apply dfs_discover_labels; [exact Hlabels| |exact Hroot].
      intro Hin; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hin; congruence. }
  pose proof (Pos.iter_invariant (fuel p) _ (dfs_step p blocked)
    (fun work => dfs_invariant EV g blocked roots (fst work) (snd work) /\
      dfs_labels EV g roots (snd work))) as Hiterate.
  refine (proj2 (Hiterate _ ([(v, succ_edges p v)], dfs_discover EV v None st) Hstart)).
  intros [stack st'] [Hi Hl]; split.
  - apply dfs_step_invariant; assumption.
  - apply dfs_step_labels; assumption.
Qed.

Lemma dfs_fold_labels {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots todo st :
  ready EV g p -> incl roots (Graph.nodes g) -> incl todo roots ->
  dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st ->
  dfs_labels EV g roots (fold_left (dfs_root p blocked) todo st).
Proof.
  intros Hready Hnodes; revert st.
  induction todo as [|v todo IH]; intros st Htodo Hinv Hlabels; cbn [fold_left];
    [exact Hlabels|].
  apply IH.
  - intros w Hw; apply Htodo; right; exact Hw.
  - apply (proj1 (dfs_root_spec EV g p blocked roots st v Hready Hinv
      (Htodo v (or_introl eq_refl)) (Hnodes v (Htodo v (or_introl eq_refl))))).
  - apply dfs_root_labels_preserved; try assumption.
    + apply Htodo; left; reflexivity.
    + apply Hnodes; apply Htodo; left; reflexivity.
Qed.

(** Every visited nonroot has a valid discovery edge from an earlier visited parent. *)
Theorem dfs_tree {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (v : V) (roots : list V) (blocked : FinSet.t V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited (dfs p blocked roots)) = true ->
  (In v roots /\ Map.get EV v (tree_edge (dfs p blocked roots)) = None) \/
  (exists e, Map.get EV v (tree_edge (dfs p blocked roots)) = Some e /\
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
    FinSet.mem EV (Graph.source g e) (visited (dfs p blocked roots)) = true /\
    before (preorder (dfs p blocked roots)) (Graph.source g e) v).
Proof.
  intros Hready Hroots Hvisited.
  pose proof (dfs_fold_labels EV g p blocked roots roots dfs_initial Hready Hroots
    ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)
    (dfs_initial_labels EV g roots)) as Hlabels.
  destruct (dfs_fold_spec EV g p blocked roots roots dfs_initial Hready Hroots
    ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)) as [Hinv _].
  unfold dfs in *; cbn [tree_edge preorder visited] in *.
  apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hvisited.
  destruct (Map.get EV v (parent (fold_left (dfs_root p blocked) roots dfs_initial)))
    as [e|] eqn:Hparent.
  - right; exists e; split; [reflexivity|].
    destruct (dfs_parent_labels _ _ _ _ Hlabels v e Hparent)
      as [_ [Hs [He [Ht [a [b [Ha [Hb Hlt]]]]]]]].
    split; [exact He|]; split; [exact Ht|]; split.
    + apply (dfs_seen_pre _ _ _ _ _ _ Hinv); exact Hs.
    + apply (dfs_numbering_order EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)
        _ _ a b Ha Hb); exact Hlt.
  - left; split; [apply (dfs_root_labels _ _ _ _ Hlabels); assumption|reflexivity].
Qed.

(** * Open intervals and tree ancestry *)

Lemma dfs_before_cons {V} (xs : list V) w u v :
  before (w :: xs) u v <-> (u = w /\ In v xs) \/ before xs u v.
Proof.
  split.
  - intros [[|a first] [middle [last Heq]]].
    + cbn in Heq; inversion Heq; subst w xs; left; split; [reflexivity|].
      apply in_or_app; right; left; reflexivity.
    + cbn in Heq; inversion Heq; subst a xs; right; exists first, middle, last; reflexivity.
  - intros [[Heq Hin]|[first [middle [last Heq]]]].
    + subst u; apply in_split in Hin; destruct Hin as [middle [last Heq]]; subst xs.
      exists [], middle, last; reflexivity.
    + exists (w :: first), middle, last; cbn; rewrite Heq; reflexivity.
Qed.

Lemma dfs_before_reverse {V} (xs : list V) u v :
  before xs u v <-> before (rev xs) v u.
Proof.
  assert (Hforward : forall (xs : list V) (u v : V),
    before xs u v -> before (rev xs) v u).
  { intros ys a b [first [middle [last Heq]]].
    exists (rev last), (rev middle), (rev first).
    rewrite Heq, !rev_app_distr; cbn [rev]; rewrite rev_app_distr; cbn [rev].
    repeat rewrite <- app_assoc; reflexivity. }
  split; [apply Hforward|].
  intro H; apply Hforward in H; rewrite rev_involutive in H; exact H.
Qed.

Lemma dfs_numbering_injective {V} (EV : encoding V) xs m next :
  dfs_numbering EV xs m next -> forall u v k,
  Map.get EV u m = Some k -> Map.get EV v m = Some k -> u = v.
Proof.
  intros Hnum u v k Hu Hv.
  pose proof (dfs_numbering_nth EV xs m next Hnum u k Hu) as Hnu.
  pose proof (dfs_numbering_nth EV xs m next Hnum v k Hv) as Hnv; congruence.
Qed.

(** Internal ancestry depends only on the discovery-edge map. *)
Definition dfs_ancestry {V E} (EV : encoding V) (g : Graph.t V E)
    (m : Map.t V E) : V -> V -> Prop :=
  clos_refl_trans V (fun u v => exists e, Map.get EV v m = Some e /\ Graph.source g e = u).

Lemma dfs_ancestry_no_out {V E} (EV : encoding V) (g : Graph.t V E) m w :
  (forall v e, Map.get EV v m = Some e -> Graph.source g e <> w) ->
  forall u v, dfs_ancestry EV g m u v -> u = w -> v = w.
Proof.
  intros Hout u v H; induction H as [u v [e [He Hsource]]|u|u x v Hux IHux Hxv IHxv];
    intro Hu.
  - exfalso; apply (Hout v e He); congruence.
  - exact Hu.
  - apply IHxv; apply IHux; exact Hu.
Qed.

Lemma dfs_ancestry_no_in {V E} (EV : encoding V) (g : Graph.t V E) m w :
  Map.get EV w m = None -> forall u v, dfs_ancestry EV g m u v -> v = w -> u = w.
Proof.
  intros Hnone u v H; induction H as [u v [e [He Hsource]]|u|u x v Hux IHux Hxv IHxv];
    intro Hv.
  - subst v; rewrite Hnone in He; discriminate.
  - exact Hv.
  - apply IHux; apply IHxv; exact Hv.
Qed.

Lemma dfs_ancestry_set {V E} (EV : encoding V) (g : Graph.t V E) m w edge :
  Map.get EV w m = None ->
  (forall v e, Map.get EV v m = Some e -> Graph.source g e <> w) ->
  forall u v,
  dfs_ancestry EV g (Map.set EV w edge m) u v <->
  dfs_ancestry EV g m u v \/
    (v = w /\ dfs_ancestry EV g m u (Graph.source g edge)).
Proof.
  intros Hnone Hout.
  assert (Hembed : forall u v, dfs_ancestry EV g m u v ->
    dfs_ancestry EV g (Map.set EV w edge m) u v).
  { intros u v H; induction H as [u v [e [He Hs]]|u|u x v Hux IHux Hxv IHxv].
    - apply rt_step; exists e; split; [|exact Hs].
      rewrite Map.get_set_other; [exact He|intro Heq; subst v; congruence].
    - apply rt_refl.
    - eapply rt_trans; eassumption. }
  intros u v; split.
  - intro H; induction H as [u v [e [He Hs]]|u|u x v Hux IHux Hxv IHxv].
    + destruct (dfs_eq_dec EV v w) as [Heq|Hne].
      * subst v; rewrite Map.get_set_same in He; inversion He; subst e.
        right; split; [reflexivity|subst u; apply rt_refl].
      * rewrite Map.get_set_other in He by exact Hne; left; apply rt_step; eauto.
    + left; apply rt_refl.
    + destruct IHux as [Hux'|[Hx Hux']], IHxv as [Hxv'|[Hv Hxv']].
      * left; eapply rt_trans; eassumption.
      * right; split; [exact Hv|]; eapply rt_trans; eassumption.
      * right; split; [eapply dfs_ancestry_no_out; eauto|exact Hux'].
      * right; split; assumption.
  - intros [H|[Hv H]]; [apply Hembed; exact H|].
    subst v; eapply rt_trans; [apply Hembed; exact H|].
    apply rt_step; exists edge; split; [apply Map.get_set_same|reflexivity].
Qed.

(** An unfinished interval extends beyond every interval already closed. *)
Definition dfs_open_interval {V E} (EV : encoding V) (st : DfsState.t V E)
    (u v : V) : bool :=
  match Map.get EV u (pre_index st), Map.get EV v (pre_index st) with
  | Some a, Some b => Pos.leb a b &&
    match Map.get EV u (post_index st), Map.get EV v (post_index st) with
    | None, _ => true
    | Some c, Some d => Pos.leb d c
    | Some _, None => false
    end
  | _, _ => false
  end.

(** Open frames keep their discovery order, with the most recently discovered one on top. *)
Definition dfs_stack_order {V E} (stack : dfs_stack V E) (st : DfsState.t V E) : Prop :=
  forall u v, before (map fst stack) u v -> before (pre st) u v.

(** The interval invariant also records the classification of already finished outgoing edges. *)
Record dfs_intervals {V E} (EV : encoding V) (g : Graph.t V E) blocked
    (stack : dfs_stack V E) (st : DfsState.t V E) : Prop := {
  dfs_stack_ordered : dfs_stack_order stack st;
  dfs_interval_tree : forall u v, In u (pre st) -> In v (pre st) ->
    (dfs_open_interval EV st u v = true <-> dfs_ancestry EV g (parent st) u v);
  dfs_finished_classes : forall u e, In u (post st) -> In e (Graph.out g u) ->
    FinSet.mem EV (Graph.target g e) blocked = true \/
    (exists j k, Map.get EV (Graph.target g e) (post_index st) = Some j /\
      Map.get EV u (post_index st) = Some k /\ Pos.lt j k) \/
    dfs_ancestry EV g (parent st) (Graph.target g e) u
}.

Lemma dfs_post_in_pre {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st v :
  dfs_invariant EV g blocked roots stack st -> In v (post st) -> In v (pre st).
Proof.
  intros Hinv Hv; apply (Permutation_in _ (Permutation_sym (dfs_partition _ _ _ _ _ _ Hinv))).
  apply in_or_app; right; exact Hv.
Qed.

Lemma dfs_unfinished_in_stack {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st v :
  dfs_invariant EV g blocked roots stack st -> In v (pre st) -> ~ In v (post st) ->
  In v (map fst stack).
Proof.
  intros Hinv Hv Hnot.
  apply (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv)) in Hv.
  apply in_app_iff in Hv; tauto.
Qed.

Lemma dfs_top_rank {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st top edges rest w a b :
  dfs_invariant EV g blocked roots ((top, edges) :: rest) st ->
  dfs_labels EV g roots st -> dfs_stack_order ((top, edges) :: rest) st ->
  In w (pre st) -> Map.get EV w (post_index st) = None ->
  Map.get EV w (pre_index st) = Some a -> Map.get EV top (pre_index st) = Some b ->
  Pos.le a b.
Proof.
  intros Hinv Hlabels Horder Hw Hnone Ha Hb.
  assert (Hnot : ~ In w (post st)).
  { intro Hin; apply (dfs_numbering_domain EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels))
      in Hin; destruct Hin as [k Hk]; congruence. }
  pose proof (dfs_unfinished_in_stack EV g blocked roots _ st w Hinv Hw Hnot) as Hstack.
  cbn [map fst] in Hstack; destruct Hstack as [Heq|Hin].
  - subst w; rewrite Ha in Hb; inversion Hb; apply Pos.le_refl.
  - apply Pos.lt_le_incl.
    apply (dfs_numbering_order EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)
      w top a b Ha Hb).
    apply (proj1 (dfs_before_reverse (pre st) top w)); apply Horder.
    apply dfs_before_cons; left; split;
      [reflexivity|exact Hin].
Qed.

Lemma dfs_fresh_post_absent {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st v :
  dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  ~ In v (pre st) -> Map.get EV v (post_index st) = None.
Proof.
  intros Hinv Hlabels Hfresh; destruct (Map.get EV v (post_index st)) as [k|] eqn:Hget;
    [|reflexivity].
  exfalso; apply Hfresh; eapply dfs_post_in_pre; [exact Hinv|].
  apply (dfs_numbering_domain EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)); eauto.
Qed.

Lemma dfs_top_post_absent {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st top edges rest :
  dfs_invariant EV g blocked roots ((top, edges) :: rest) st ->
  dfs_labels EV g roots st -> Map.get EV top (post_index st) = None.
Proof.
  intros Hinv Hlabels; destruct (Map.get EV top (post_index st)) as [k|] eqn:Hget;
    [|reflexivity].
  exfalso; apply (dfs_frame_not_finished EV g blocked roots _ st top edges Hinv
    (or_introl eq_refl)).
  apply (dfs_numbering_domain EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)); eauto.
Qed.

Lemma dfs_finish_interval {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st top edges rest u v :
  dfs_invariant EV g blocked roots ((top, edges) :: rest) st ->
  dfs_labels EV g roots st -> dfs_stack_order ((top, edges) :: rest) st ->
  In u (pre st) -> In v (pre st) ->
  dfs_open_interval EV (dfs_finish EV top st) u v = dfs_open_interval EV st u v.
Proof.
  intros Hinv Hlabels Horder Hu Hv.
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) u) Hu)
    as [a Ha].
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v) Hv)
    as [b Hb].
  pose proof (dfs_top_post_absent EV g blocked roots st top edges rest Hinv Hlabels) as Hnone.
  unfold dfs_open_interval; cbn [dfs_finish pre_index post_index]; rewrite Ha, Hb.
  destruct (dfs_eq_dec EV u top) as [Hu'|Hu']; destruct (dfs_eq_dec EV v top) as [Hv'|Hv'].
  - subst u v; rewrite Map.get_set_same, Hnone, Pos.leb_refl; reflexivity.
  - subst u; rewrite Map.get_set_same, Map.get_set_other by exact Hv'.
    rewrite Hnone; destruct (Map.get EV v (post_index st)) as [d|] eqn:Hd.
    + assert (Hle : Pos.leb d (post_clock st) = true).
      { apply Pos.leb_le; apply Pos.lt_le_incl.
        apply (dfs_numbering_bound EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels) v d Hd). }
      rewrite Hle; reflexivity.
    + assert (Hfalse : Pos.leb a b = false).
      { apply not_true_is_false; intro Hle; apply Pos.leb_le in Hle.
        pose proof (dfs_top_rank EV g blocked roots st top edges rest v b a
          Hinv Hlabels Horder Hv Hd Hb Ha) as Hback.
        assert (Heq : a = b) by (apply Pos.le_antisym; assumption).
        apply Hv'; eapply (dfs_numbering_injective EV _ _ _
          (dfs_pre_numbering _ _ _ _ Hlabels) v top b).
        - exact Hb.
        - rewrite Heq in Ha; exact Ha. }
      rewrite Hfalse; reflexivity.
  - subst v; rewrite Map.get_set_other by exact Hu'; rewrite Map.get_set_same, Hnone.
    destruct (Map.get EV u (post_index st)) as [c|] eqn:Hc; [|reflexivity].
    assert (Hfalse : Pos.leb (post_clock st) c = false).
    { apply Pos.leb_gt.
      apply (dfs_numbering_bound EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels) u c Hc). }
    rewrite Hfalse; reflexivity.
  - rewrite !Map.get_set_other by assumption; reflexivity.
Qed.

Lemma dfs_discover_interval_old {V E} (EV : encoding V) (st : DfsState.t V E)
    w via u v :
  ~ In w (pre st) -> In u (pre st) -> In v (pre st) ->
  dfs_open_interval EV (dfs_discover EV w via st) u v = dfs_open_interval EV st u v.
Proof.
  intros Hfresh Hu Hv; unfold dfs_open_interval; cbn [dfs_discover pre_index post_index].
  rewrite !Map.get_set_other; [reflexivity| |]; intro Heq; subst; contradiction.
Qed.

Lemma dfs_discover_interval_left {V E} (EV : encoding V) (g : Graph.t V E)
    roots st w via v :
  dfs_labels EV g roots st -> ~ In w (pre st) -> In v (pre st) ->
  dfs_open_interval EV (dfs_discover EV w via st) w v = false.
Proof.
  intros Hlabels Hfresh Hv.
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v) Hv)
    as [k Hk].
  unfold dfs_open_interval; cbn [dfs_discover pre_index post_index].
  rewrite Map.get_set_same, Map.get_set_other; [|intro Heq; subst v; contradiction].
  rewrite Hk.
  assert (Hfalse : Pos.leb (pre_clock st) k = false).
  { apply Pos.leb_gt.
    apply (dfs_numbering_bound EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v k Hk). }
  rewrite Hfalse; reflexivity.
Qed.

Lemma dfs_discover_interval_right {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st w via u :
  dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  ~ In w (pre st) -> In u (pre st) ->
  (dfs_open_interval EV (dfs_discover EV w via st) u w = true <->
   Map.get EV u (post_index st) = None).
Proof.
  intros Hinv Hlabels Hfresh Hu.
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) u) Hu)
    as [k Hk].
  pose proof (dfs_fresh_post_absent EV g blocked roots stack st w Hinv Hlabels Hfresh)
    as Hnone.
  unfold dfs_open_interval; cbn [dfs_discover pre_index post_index].
  rewrite Map.get_set_other; [|intro Heq; subst u; contradiction].
  rewrite Map.get_set_same, Hk, Hnone.
  assert (Hle : Pos.leb k (pre_clock st) = true).
  { apply Pos.leb_le; apply Pos.lt_le_incl.
    apply (dfs_numbering_bound EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) u k Hk). }
  rewrite Hle; destruct (Map.get EV u (post_index st)); cbn; split; congruence.
Qed.

Lemma dfs_discover_interval_self {V E} (EV : encoding V) (st : DfsState.t V E) w via :
  dfs_open_interval EV (dfs_discover EV w via st) w w = true.
Proof.
  unfold dfs_open_interval; cbn [dfs_discover pre_index post_index].
  rewrite Map.get_set_same, Pos.leb_refl.
  destruct (Map.get EV w (post_index st)); cbn; [apply Pos.leb_refl|reflexivity].
Qed.

Lemma dfs_active_ancestor {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st top edges rest u :
  dfs_invariant EV g blocked roots ((top, edges) :: rest) st ->
  dfs_labels EV g roots st -> dfs_intervals EV g blocked ((top, edges) :: rest) st ->
  In u (pre st) ->
  (dfs_ancestry EV g (parent st) u top <-> Map.get EV u (post_index st) = None).
Proof.
  intros Hinv Hlabels Hinterval Hu.
  destruct (dfs_frame_node EV g blocked roots _ st top edges Hinv (or_introl eq_refl))
    as [_ Htop].
  rewrite <- (dfs_interval_tree _ _ _ _ _ Hinterval u top Hu Htop).
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) u) Hu)
    as [a Ha].
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) top) Htop)
    as [b Hb].
  pose proof (dfs_top_post_absent EV g blocked roots st top edges rest Hinv Hlabels) as Hnone.
  unfold dfs_open_interval; rewrite Ha, Hb, Hnone.
  destruct (Map.get EV u (post_index st)) as [c|] eqn:Hpost.
  - rewrite andb_false_r; split; discriminate.
  - assert (Hle : Pos.leb a b = true).
    { apply Pos.leb_le; exact (dfs_top_rank EV g blocked roots st top edges rest u a b
        Hinv Hlabels (dfs_stack_ordered _ _ _ _ _ Hinterval) Hu Hpost Ha Hb). }
    rewrite Hle; split; reflexivity.
Qed.

Lemma dfs_discover_ancestry {V E} (EV : encoding V) (g : Graph.t V E)
    roots st w via :
  dfs_labels EV g roots st -> ~ In w (pre st) -> forall u v,
  dfs_ancestry EV g (parent (dfs_discover EV w via st)) u v <->
  dfs_ancestry EV g (parent st) u v \/
    match via with
    | None => False
    | Some e => v = w /\ dfs_ancestry EV g (parent st) u (Graph.source g e)
    end.
Proof.
  intros Hlabels Hfresh u v; destruct via as [e|]; cbn [dfs_discover parent]; [|tauto].
  apply dfs_ancestry_set.
  - apply (dfs_parent_absent EV g roots st w Hlabels Hfresh).
  - intros x a Ha Heq; apply Hfresh; rewrite <- Heq.
    destruct (dfs_parent_labels _ _ _ _ Hlabels x a Ha) as [_ [Hs _]]; exact Hs.
Qed.

Lemma dfs_discover_tree_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st w via :
  dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked stack st -> ~ In w (pre st) ->
  (match via with
   | None => stack = []
   | Some e => exists top edges rest, stack = (top, edges) :: rest /\ Graph.source g e = top
   end) ->
  forall u v, In u (pre (dfs_discover EV w via st)) ->
    In v (pre (dfs_discover EV w via st)) ->
    (dfs_open_interval EV (dfs_discover EV w via st) u v = true <->
     dfs_ancestry EV g (parent (dfs_discover EV w via st)) u v).
Proof.
  intros Hinv Hlabels Hinterval Hfresh Hvia.
  assert (Hout : forall x e, Map.get EV x (parent st) = Some e -> Graph.source g e <> w).
  { intros x e He Heq; apply Hfresh; rewrite <- Heq.
    destruct (dfs_parent_labels _ _ _ _ Hlabels x e He) as [_ [Hs _]]; exact Hs. }
  pose proof (dfs_parent_absent EV g roots st w Hlabels Hfresh) as Hnone.
  intros u v Hu Hv; cbn [dfs_discover pre] in Hu, Hv.
  destruct Hu as [Hu|Hu], Hv as [Hv|Hv].
  - subst u v; rewrite dfs_discover_interval_self; split; [intros _; apply rt_refl|reflexivity].
  - subst u; rewrite (dfs_discover_interval_left EV g roots st w via v Hlabels Hfresh Hv).
    split; [discriminate|intro Hanc; exfalso].
    apply (dfs_discover_ancestry EV g roots st w via Hlabels Hfresh) in Hanc.
    destruct Hanc as [Hanc|Hanc].
    + apply Hfresh; assert (v = w) by (eapply dfs_ancestry_no_out; eauto).
      subst v; exact Hv.
    + destruct via; [destruct Hanc as [Heq _]; subst v; contradiction|contradiction].
  - subst v.
    rewrite (dfs_discover_interval_right EV g blocked roots stack st w via u
      Hinv Hlabels Hfresh Hu), (dfs_discover_ancestry EV g roots st w via Hlabels Hfresh).
    assert (Hnot : ~ dfs_ancestry EV g (parent st) u w).
    { intro H; apply Hfresh; assert (u = w) by (eapply dfs_ancestry_no_in; eauto).
      subst u; exact Hu. }
    destruct via as [e|].
    + destruct Hvia as [top [edges [rest [Hstack Hsource]]]]; subst stack.
      rewrite Hsource, (dfs_active_ancestor EV g blocked roots st top edges rest u
        Hinv Hlabels Hinterval Hu); tauto.
    + subst stack; cbn; split; [|tauto].
      intro Hpost; exfalso.
      assert (Hnotpost : ~ In u (post st)).
      { intro Hin; apply (dfs_numbering_domain EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels))
          in Hin; destruct Hin as [k Hk]; congruence. }
      pose proof (dfs_unfinished_in_stack EV g blocked roots [] st u Hinv Hu Hnotpost)
        as Hfalse; contradiction.
  - rewrite (dfs_discover_interval_old EV st w via u v Hfresh Hu Hv).
    rewrite (dfs_interval_tree _ _ _ _ _ Hinterval u v Hu Hv).
    rewrite (dfs_discover_ancestry EV g roots st w via Hlabels Hfresh).
    destruct via; [cbn; split; [auto|intros [H|[Heq _]]; [exact H|subst v; contradiction]]|tauto].
Qed.

Lemma dfs_discover_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots stack st w via edges :
  dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked stack st -> ~ In w (pre st) ->
  (match via with
   | None => stack = []
   | Some e => exists top pending rest,
       stack = (top, pending) :: rest /\ Graph.source g e = top
   end) ->
  dfs_intervals EV g blocked ((w, edges) :: stack) (dfs_discover EV w via st).
Proof.
  intros Hinv Hlabels Hinterval Hfresh Hvia; constructor.
  - intros u v Hbefore; cbn [map fst] in Hbefore; apply dfs_before_cons in Hbefore.
    cbn [dfs_discover pre]; apply dfs_before_cons.
    destruct Hbefore as [[Heq Hin]|Hbefore].
    + left; split; [exact Heq|].
      apply (Permutation_in _ (Permutation_sym (dfs_partition _ _ _ _ _ _ Hinv))).
      apply in_or_app; left; exact Hin.
    + right; apply (dfs_stack_ordered _ _ _ _ _ Hinterval); exact Hbefore.
  - eapply dfs_discover_tree_intervals; eassumption.
  - intros u e Hu He; cbn [dfs_discover post] in Hu.
    destruct (dfs_finished_classes _ _ _ _ _ Hinterval u e Hu He)
      as [Hb|[Hforward|Hback]].
    + left; exact Hb.
    + right; left; exact Hforward.
    + right; right; apply (dfs_discover_ancestry EV g roots st w via Hlabels Hfresh).
      left; exact Hback.
Qed.

Lemma dfs_intervals_stack {V E} (EV : encoding V) (g : Graph.t V E)
    blocked stack stack' st :
  map fst stack = map fst stack' -> dfs_intervals EV g blocked stack st ->
  dfs_intervals EV g blocked stack' st.
Proof.
  intros Heq [Horder Htree Hclasses]; constructor; try assumption.
  intros u v Hbefore; apply Horder; rewrite Heq; exact Hbefore.
Qed.

Lemma dfs_finish_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st top rest :
  dfs_invariant EV g blocked roots ((top, []) :: rest) st ->
  dfs_labels EV g roots st -> dfs_intervals EV g blocked ((top, []) :: rest) st ->
  dfs_intervals EV g blocked rest (dfs_finish EV top st).
Proof.
  intros Hinv Hlabels Hinterval.
  pose proof (dfs_top_post_absent EV g blocked roots st top [] rest Hinv Hlabels) as Hnone.
  constructor.
  - intros u v Hbefore; cbn [dfs_finish pre].
    apply (dfs_stack_ordered _ _ _ _ _ Hinterval); apply dfs_before_cons; right; exact Hbefore.
  - intros u v Hu Hv; cbn [dfs_finish pre] in Hu, Hv.
    rewrite (dfs_finish_interval EV g blocked roots st top [] rest u v Hinv Hlabels
      (dfs_stack_ordered _ _ _ _ _ Hinterval) Hu Hv).
    apply (dfs_interval_tree _ _ _ _ _ Hinterval); assumption.
  - intros u e Hu He; cbn [dfs_finish post] in Hu.
    destruct Hu as [Hu|Hu].
    + subst u.
      destruct (dfs_frames _ _ _ _ _ _ Hinv top [] (or_introl eq_refl)) as [_ Hdone].
      destruct (Hdone e He) as [Hfalse|[Hm|Hb]]; [contradiction| |left; exact Hb].
      apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hm.
      destruct (Map.get EV (Graph.target g e) (post_index st)) as [j|] eqn:Hj.
      * right; left; exists j, (post_clock st); cbn [dfs_finish post_index].
        split.
        -- rewrite Map.get_set_other; [exact Hj|intro Heq; rewrite Heq, Hnone in Hj; discriminate].
        -- split; [apply Map.get_set_same|].
           apply (dfs_numbering_bound EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels) _ j Hj).
      * right; right; cbn [dfs_finish parent].
        apply (dfs_active_ancestor EV g blocked roots st top [] rest _ Hinv Hlabels Hinterval Hm).
        exact Hj.
    + destruct (dfs_finished_classes _ _ _ _ _ Hinterval u e Hu He)
        as [Hb|[[j [k [Hj [Hk Hlt]]]]|Hback]].
      * left; exact Hb.
      * right; left; exists j, k; cbn [dfs_finish post_index].
        rewrite !Map.get_set_other; [auto| |]; intro Heq; subst;
          rewrite Hnone in *; discriminate.
      * right; right; exact Hback.
Qed.

Lemma dfs_initial_intervals {V E} (EV : encoding V) (g : Graph.t V E) blocked :
  dfs_intervals EV g blocked [] (@dfs_initial V E).
Proof.
  constructor; cbn [dfs_initial pre post map].
  - intros u v Hbefore; destruct Hbefore as [xs [ys [zs Hfalse]]].
    destruct xs; discriminate.
  - intros u v Hu; contradiction.
  - intros u e Hu; contradiction.
Qed.

Lemma dfs_step_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots stack st :
  ready EV g p -> dfs_invariant EV g blocked roots stack st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked stack st ->
  dfs_intervals EV g blocked (fst (dfs_step p blocked (stack, st)))
    (snd (dfs_step p blocked (stack, st))).
Proof.
  intros [Hwf [_ Hlaws]] Hinv Hlabels Hinterval.
  destruct stack as [|[v [|e es]] rest]; cbn [dfs_step fst snd]; [exact Hinterval| |].
  - apply (dfs_finish_intervals EV g blocked roots st v rest); assumption.
  - destruct (FinSet.mem EV (Graph.target g e) blocked ||
      FinSet.mem EV (Graph.target g e) (seen st)) eqn:Hskip.
    + exact (dfs_intervals_stack EV g blocked ((v, e :: es) :: rest)
        ((v, es) :: rest) st eq_refl Hinterval).
    + eapply (dfs_intervals_stack EV g blocked
        ((Graph.target g e, succ_edges p (Graph.target g e)) :: (v, e :: es) :: rest)
        ((Graph.target g e, succ_edges p (Graph.target g e)) :: (v, es) :: rest)
        (dfs_discover EV (Graph.target g e) (Some e) st) eq_refl).
      apply (dfs_discover_intervals EV g blocked roots ((v, e :: es) :: rest));
        try assumption.
      * apply orb_false_iff in Hskip; destruct Hskip as [_ Hfresh].
        intro Hin; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hin; congruence.
      * exists v, (e :: es), rest; split; [reflexivity|].
        apply (out_source Hwf v e).
        destruct (dfs_frames _ _ _ _ _ _ Hinv v (e :: es) (or_introl eq_refl)) as [Hi _].
        apply Hi; left; reflexivity.
Qed.

Lemma dfs_root_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots st v :
  ready EV g p -> dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked [] st -> In v roots -> In v (Graph.nodes g) ->
  dfs_intervals EV g blocked [] (dfs_root p blocked st v).
Proof.
  intros Hready Hinv Hlabels Hinterval Hroot Hv.
  unfold dfs_root in *; rewrite dfs_run_agrees in *.
  destruct (FinSet.mem EV v blocked || FinSet.mem EV v (seen st)) eqn:Hskip;
    [exact Hinterval|].
  apply orb_false_iff in Hskip; destruct Hskip as [Hb Hfresh].
  assert (Hstart : dfs_invariant EV g blocked roots [(v, succ_edges p v)]
    (dfs_discover EV v None st) /\ dfs_labels EV g roots (dfs_discover EV v None st) /\
    dfs_intervals EV g blocked [(v, succ_edges p v)] (dfs_discover EV v None st)).
  { split; [apply dfs_root_start; assumption|]; split.
    - apply dfs_discover_labels; [exact Hlabels| |exact Hroot].
      intro Hin; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hin; congruence.
    - apply (dfs_discover_intervals EV g blocked roots []); try assumption; [|reflexivity].
      intro Hin; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hin; congruence. }
  pose proof (Pos.iter_invariant (fuel p) _ (dfs_step p blocked)
    (fun work => dfs_invariant EV g blocked roots (fst work) (snd work) /\
      dfs_labels EV g roots (snd work) /\ dfs_intervals EV g blocked (fst work) (snd work)))
    as Hiterate.
  assert (Hpreserve : forall work,
    (dfs_invariant EV g blocked roots (fst work) (snd work) /\
      dfs_labels EV g roots (snd work) /\ dfs_intervals EV g blocked (fst work) (snd work)) ->
    (dfs_invariant EV g blocked roots (fst (dfs_step p blocked work))
      (snd (dfs_step p blocked work)) /\
      dfs_labels EV g roots (snd (dfs_step p blocked work)) /\
      dfs_intervals EV g blocked (fst (dfs_step p blocked work))
        (snd (dfs_step p blocked work)))).
  { intros [stack st'] [Hi [Hl Ht]]; split; [apply dfs_step_invariant; assumption|]; split.
    - apply dfs_step_labels; assumption.
    - apply dfs_step_intervals with (roots := roots); assumption. }
  destruct (Hiterate Hpreserve ([(v, succ_edges p v)], dfs_discover EV v None st) Hstart)
    as [Hi [_ Ht]].
  destruct (Pos.iter (dfs_step p blocked)
    ([(v, succ_edges p v)], dfs_discover EV v None st) (fuel p)) as [stack st'] eqn:Hrun.
  eapply dfs_intervals_stack; [|exact Ht].
  pose proof (dfs_iter_spec EV g p blocked roots
    ([(v, succ_edges p v)], dfs_discover EV v None st) (fuel p) Hready (proj1 Hstart))
    as [_ [_ Hbound]].
  rewrite Hrun in Hbound; cbn [fst snd] in Hbound.
  destruct Hbound as [Hempty|Hbound]; [subst stack; reflexivity|].
  pose proof (dfs_root_credit EV g p st v Hready Hv Hfresh) as Hcredit; lia.
Qed.

Lemma dfs_fold_intervals {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots todo st :
  ready EV g p -> incl roots (Graph.nodes g) -> incl todo roots ->
  dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked [] st ->
  dfs_intervals EV g blocked [] (fold_left (dfs_root p blocked) todo st).
Proof.
  intros Hready Hnodes; revert st.
  induction todo as [|v todo IH]; intros st Htodo Hinv Hlabels Hinterval; cbn [fold_left];
    [exact Hinterval|].
  assert (Hroot : In v roots) by (apply Htodo; left; reflexivity).
  assert (Hv : In v (Graph.nodes g)) by (apply Hnodes; exact Hroot).
  apply IH.
  - intros w Hw; apply Htodo; right; exact Hw.
  - exact (proj1 (dfs_root_spec EV g p blocked roots st v Hready Hinv Hroot Hv)).
  - apply dfs_root_labels_preserved; assumption.
  - apply dfs_root_intervals with (roots := roots); assumption.
Qed.

Lemma dfs_final_spec {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) blocked roots :
  ready EV g p -> incl roots (Graph.nodes g) ->
  let st := fold_left (dfs_root p blocked) roots dfs_initial in
  dfs_invariant EV g blocked roots [] st /\ dfs_labels EV g roots st /\
  dfs_intervals EV g blocked [] st.
Proof.
  intros Hready Hroots; split.
  - exact (proj1 (dfs_fold_spec EV g p blocked roots roots dfs_initial Hready Hroots
      ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots))).
  - split.
    + apply dfs_fold_labels; try assumption.
      * intros w Hw; exact Hw.
      * apply dfs_initial_invariant.
      * apply dfs_initial_labels.
    + apply dfs_fold_intervals with (roots := roots); try assumption.
      * intros w Hw; exact Hw.
      * apply dfs_initial_invariant.
      * apply dfs_initial_labels.
      * apply dfs_initial_intervals.
Qed.

Lemma dfs_final_post_number {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st v :
  dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st -> In v (pre st) ->
  exists k, Map.get EV v (post_index st) = Some k.
Proof.
  intros Hinv Hlabels Hv.
  apply (dfs_numbering_domain EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)).
  exact (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv) Hv).
Qed.

(** On visited vertices the interval test is exactly reflexive discovery-tree ancestry. *)
Theorem ancestor_b_agrees {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (u v : V) (roots : list V) (blocked : FinSet.t V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV u (visited (dfs p blocked roots)) = true ->
  FinSet.mem EV v (visited (dfs p blocked roots)) = true ->
  (ancestor_b EV (dfs p blocked roots) u v = true <->
   dfs_ancestor EV g (dfs p blocked roots) u v).
Proof.
  intros Hready Hroots Hu Hv.
  destruct (dfs_final_spec EV g p blocked roots Hready Hroots) as [Hinv [Hlabels Hinterval]].
  unfold dfs in *; cbn [visited] in Hu, Hv.
  apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hu, Hv.
  pose proof (dfs_interval_tree _ _ _ _ _ Hinterval u v Hu Hv) as Hexact.
  destruct (dfs_final_post_number EV g blocked roots _ u Hinv Hlabels Hu) as [c Hc].
  destruct (dfs_final_post_number EV g blocked roots _ v Hinv Hlabels Hv) as [d Hd].
  unfold ancestor_b; cbn [pre_num post_num tree_edge].
  rewrite Hc, Hd.
  unfold dfs_open_interval in Hexact; rewrite Hc, Hd in Hexact.
  exact Hexact.
Qed.

Lemma dfs_ancestry_target {V E} (EV : encoding V) (g : Graph.t V E) roots st u v :
  dfs_labels EV g roots st -> In u (pre st) ->
  dfs_ancestry EV g (parent st) u v -> In v (pre st).
Proof.
  intros Hlabels Hu Hanc; induction Hanc as [u v [e [He _]]|u|u w v Huw IHuw Hwv IHwv].
  - apply (dfs_parent_labels _ _ _ _ Hlabels v e He).
  - exact Hu.
  - apply IHwv; apply IHuw; exact Hu.
Qed.

Lemma dfs_ancestry_order {V E} (EV : encoding V) (g : Graph.t V E)
    blocked roots st u v :
  dfs_invariant EV g blocked roots [] st -> dfs_labels EV g roots st ->
  dfs_intervals EV g blocked [] st -> In u (pre st) ->
  dfs_ancestry EV g (parent st) u v -> u = v \/ before (post st) u v.
Proof.
  intros Hinv Hlabels Hinterval Hu Hanc.
  pose proof (dfs_ancestry_target EV g roots st u v Hlabels Hu Hanc) as Hv.
  destruct (dfs_final_post_number EV g blocked roots st u Hinv Hlabels Hu) as [a Ha].
  destruct (dfs_final_post_number EV g blocked roots st v Hinv Hlabels Hv) as [b Hb].
  apply (dfs_interval_tree _ _ _ _ _ Hinterval u v Hu Hv) in Hanc.
  unfold dfs_open_interval in Hanc; rewrite Ha, Hb in Hanc.
  destruct (Map.get EV u (pre_index st)), (Map.get EV v (pre_index st)); try discriminate.
  apply andb_true_iff in Hanc; destruct Hanc as [_ Hle]; apply Pos.leb_le in Hle.
  destruct (Pos.eq_dec a b) as [Heq|Hne].
  - left; subst b; eapply dfs_numbering_injective; eauto using dfs_post_numbering.
  - right; apply (proj2 (dfs_before_reverse (post st) u v)).
    apply (dfs_numbering_order EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels) v u b a Hb Ha).
    apply Pos2Nat.inj_lt; apply Pos2Nat.inj_le in Hle.
    assert (Hnatne : Pos.to_nat a <> Pos.to_nat b).
    { intro Heq; apply Hne; apply Pos2Nat.inj; exact Heq. }
    lia.
Qed.

(** Reverse postorder puts every discovery parent before its child and each root before its tree. *)
Theorem rpo_order {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (v : V) (roots : list V) (blocked : FinSet.t V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  (forall e, Map.get EV v (tree_edge (dfs p blocked roots)) = Some e ->
    before (rpo (dfs p blocked roots)) (Graph.source g e) v) /\
  (forall w, In v roots -> Map.get EV v (tree_edge (dfs p blocked roots)) = None ->
    FinSet.mem EV v (visited (dfs p blocked roots)) = true ->
    dfs_ancestor EV g (dfs p blocked roots) v w ->
    w = v \/ before (rpo (dfs p blocked roots)) v w).
Proof.
  intros Hready Hroots.
  destruct (dfs_final_spec EV g p blocked roots Hready Hroots) as [Hinv [Hlabels Hinterval]].
  unfold dfs, rpo; cbn [tree_edge visited postorder]; rewrite rev_involutive.
  split.
  - intros e He.
    destruct (dfs_parent_labels _ _ _ _ Hlabels v e He)
      as [Hv [Hs [_ [_ [a [b [Ha [Hb Hlt]]]]]]]].
    assert (Hanc : dfs_ancestry EV g (parent (fold_left (dfs_root p blocked) roots dfs_initial))
      (Graph.source g e) v).
    { apply rt_step; exists e; auto. }
    destruct (dfs_ancestry_order EV g blocked roots _ _ _ Hinv Hlabels Hinterval Hs Hanc)
      as [Heq|Hbefore]; [|exact Hbefore].
    rewrite Heq, Hb in Ha; inversion Ha; subst b; exfalso; exact (Pos.lt_irrefl a Hlt).
  - intros w Hroot Hnone Hv Hanc.
    apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hv.
    destruct (dfs_ancestry_order EV g blocked roots _ v w Hinv Hlabels Hinterval Hv Hanc)
      as [Heq|Hbefore]; [left; symmetry; exact Heq|right; exact Hbefore].
Qed.

(** Every reachable nonentry has a discovery parent earlier in reverse postorder. *)
Theorem rpo_parent_of_non_entry {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (v : V) :
  ready EV g p -> reachable g v -> ~ In v (Graph.entries g) ->
  exists e, Map.get EV v (tree_edge (dfs p FinSet.empty (Graph.entries g))) = Some e /\
    before (rpo (dfs p FinSet.empty (Graph.entries g))) (Graph.source g e) v.
Proof.
  intros Hready Hreach Hnot; pose proof Hready as [Hwf _].
  pose proof (proj2 (reachable_dfs EV g p v Hready) Hreach) as Hv.
  destruct (dfs_tree EV g p v (Graph.entries g) FinSet.empty Hready (entries_in Hwf) Hv)
    as [[Hin _]|[e [He _]]]; [contradiction|].
  exists e; split; [exact He|].
  apply (proj1 (rpo_order EV g p v (Graph.entries g) FinSet.empty Hready (entries_in Hwf)) e He).
Qed.

(** Every outgoing edge of a visited vertex goes forward in RPO or retreats to a tree ancestor. *)
Theorem rpo_edge_classes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (roots : list V) :
  ready EV g p -> incl roots (Graph.nodes g) -> forall e,
  FinSet.mem EV (Graph.source g e) (visited (dfs p FinSet.empty roots)) = true ->
  In e (Graph.out g (Graph.source g e)) ->
  before (rpo (dfs p FinSet.empty roots)) (Graph.source g e) (Graph.target g e) \/
    retreating EV g (dfs p FinSet.empty roots) e.
Proof.
  intros Hready Hroots e Hv He.
  destruct (dfs_final_spec EV g p FinSet.empty roots Hready Hroots)
    as [Hinv [Hlabels Hinterval]].
  unfold dfs in *; cbn [visited] in Hv.
  apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hv.
  apply (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv)) in Hv.
  destruct (dfs_finished_classes _ _ _ _ _ Hinterval _ e Hv He)
    as [Hfalse|[[j [k [Hj [Hk Hlt]]]]|Hback]].
  - rewrite FinSet.mem_empty in Hfalse; discriminate.
  - left; unfold rpo; cbn [postorder]; rewrite rev_involutive.
    apply (proj2 (dfs_before_reverse _ _ _)).
    apply (dfs_numbering_order EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)
      _ _ j k Hj Hk); exact Hlt.
  - right; exact Hback.
Qed.

Lemma dfs_ancestry_root {V E} (EV : encoding V) (g : Graph.t V E) roots st v :
  dfs_labels EV g roots st -> In v (pre st) ->
  exists s, In s roots /\ dfs_ancestry EV g (parent st) s v.
Proof.
  intros Hlabels Hv.
  assert (Hrooted : forall n v k, Pos.to_nat k = n -> In v (pre st) ->
    Map.get EV v (pre_index st) = Some k ->
    exists s, In s roots /\ dfs_ancestry EV g (parent st) s v).
  { intro n; induction n using lt_wf_ind; intros w k Hsize Hw Hk.
    destruct (Map.get EV w (parent st)) as [e|] eqn:He.
    - destruct (dfs_parent_labels _ _ _ _ Hlabels w e He)
        as [_ [Hs [_ [_ [a [b [Ha [Hb Hlt]]]]]]]].
      rewrite Hk in Hb; inversion Hb; subst b.
      apply Pos2Nat.inj_lt in Hlt; rewrite Hsize in Hlt.
      destruct (H (Pos.to_nat a) Hlt (Graph.source g e) a eq_refl Hs Ha)
        as [s [Hroot Hanc]].
      exists s; split; [exact Hroot|]; eapply rt_trans; [exact Hanc|].
      apply rt_step; exists e; auto.
    - exists w; split; [apply (dfs_root_labels _ _ _ _ Hlabels w Hw He)|apply rt_refl]. }
  destruct (proj2 (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v) Hv)
    as [k Hk].
  apply (Hrooted (Pos.to_nat k) v k eq_refl Hv Hk).
Qed.

Lemma dfs_before_head_false {V} (v : V) xs u :
  NoDup (v :: xs) -> ~ before (v :: xs) u v.
Proof.
  intros Hnodup Hbefore; apply dfs_before_indices in Hbefore.
  destruct Hbefore as [i [j [Hlt [Hi Hj]]]].
  assert (Heq : 0 = j).
  { apply (proj1 (NoDup_nth_error _) Hnodup); [cbn; lia|cbn; symmetry; exact Hj]. }
  lia.
Qed.

(** With one graph entry, reverse postorder begins with that entry. *)
Theorem rpo_single_entry {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (s : V) :
  ready EV g p -> Graph.entries g = [s] ->
  exists rest, rpo (dfs p FinSet.empty (Graph.entries g)) = s :: rest.
Proof.
  intros Hready Hentry; pose proof Hready as [Hwf _].
  destruct (dfs_final_spec EV g p FinSet.empty (Graph.entries g) Hready (entries_in Hwf))
    as [Hinv [Hlabels Hinterval]].
  assert (Hs : In s (pre (fold_left (dfs_root p FinSet.empty) (Graph.entries g) dfs_initial))).
  { apply (dfs_seen_pre _ _ _ _ _ _ Hinv).
    apply (proj2 (reachable_dfs EV g p s Hready)); constructor; rewrite Hentry; left; reflexivity. }
  unfold rpo, dfs; cbn [postorder]; rewrite rev_involutive.
  destruct (post (fold_left (dfs_root p FinSet.empty) (Graph.entries g) dfs_initial))
    as [|head rest] eqn:Hpost.
  - apply (Permutation_in _ (dfs_partition _ _ _ _ _ _ Hinv)) in Hs.
    rewrite Hpost in Hs; contradiction.
  - assert (Hhead : In head
      (pre (fold_left (dfs_root p FinSet.empty) (Graph.entries g) dfs_initial))).
    { eapply dfs_post_in_pre; [exact Hinv|rewrite Hpost; left; reflexivity]. }
    destruct (dfs_ancestry_root EV g (Graph.entries g) _ head Hlabels Hhead)
      as [root [Hroot Hanc]].
    rewrite Hentry in Hroot; destruct Hroot as [Heq|Hfalse]; [subst root|contradiction].
    destruct (dfs_ancestry_order EV g FinSet.empty (Graph.entries g) _ s head
      Hinv Hlabels Hinterval Hs Hanc) as [Heq|Hbefore].
    + subst head; exists rest; reflexivity.
    + exfalso; rewrite Hpost in Hbefore; apply (dfs_before_head_false head rest s);
        [|exact Hbefore].
      rewrite <- Hpost; apply (dfs_numbering_nodup EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)).
Qed.

Lemma dfs_before_trans {V} (xs : list V) u v w :
  NoDup xs -> before xs u v -> before xs v w -> before xs u w.
Proof.
  intros Hnodup Huv Hvw; apply dfs_before_indices in Huv, Hvw.
  destruct Huv as [i [j [Hij [Hi Hj]]]], Hvw as [j' [k [Hjk [Hj' Hk]]]].
  assert (Heq : j = j').
  { apply (proj1 (NoDup_nth_error _) Hnodup); [apply nth_error_Some; congruence|congruence]. }
  apply dfs_before_indices; exists i, k; split; [lia|auto].
Qed.

Lemma dfs_before_irrefl {V} (xs : list V) v : NoDup xs -> ~ before xs v v.
Proof.
  intros Hnodup Hbefore; apply dfs_before_indices in Hbefore.
  destruct Hbefore as [i [j [Hij [Hi Hj]]]].
  assert (Heq : i = j).
  { apply (proj1 (NoDup_nth_error _) Hnodup); [apply nth_error_Some; congruence|congruence]. }
  lia.
Qed.

Lemma dfs_rpo_nodup {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots :
  ready EV g p -> incl roots (Graph.nodes g) -> NoDup (rpo (dfs p FinSet.empty roots)).
Proof.
  intros Hready Hroots; unfold rpo; apply NoDup_rev.
  destruct (dfs_final_spec EV g p FinSet.empty roots Hready Hroots) as [_ [Hlabels _]].
  unfold dfs; cbn [postorder]; apply NoDup_rev.
  apply (dfs_numbering_nodup EV _ _ _ (dfs_post_numbering _ _ _ _ Hlabels)).
Qed.

Lemma dfs_visited_edge {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots e :
  ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV (Graph.source g e) (visited (dfs p FinSet.empty roots)) = true ->
  In e (Graph.out g (Graph.source g e)) ->
  FinSet.mem EV (Graph.target g e) (visited (dfs p FinSet.empty roots)) = true.
Proof.
  intros Hready Hroots Hsource He.
  destruct (dfs_exact EV g p (Graph.source g e) roots FinSet.empty Hready Hroots) as [Hs _].
  destruct (dfs_exact EV g p (Graph.target g e) roots FinSet.empty Hready Hroots) as [Ht _].
  apply Ht; apply Hs in Hsource.
  apply (@reachable_step V E (without EV FinSet.empty (set_entries g roots)) e).
  - exact Hsource.
  - apply filter_In; split; [exact He|rewrite FinSet.mem_empty; reflexivity].
Qed.

Lemma dfs_path_classes {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots u es v :
  ready EV g p -> incl roots (Graph.nodes g) -> path g u es v ->
  FinSet.mem EV u (visited (dfs p FinSet.empty roots)) = true ->
  (es = [] /\ u = v) \/ before (rpo (dfs p FinSet.empty roots)) u v \/
    exists e, In e es /\ retreating EV g (dfs p FinSet.empty roots) e.
Proof.
  intros Hready Hroots Hpath; induction Hpath as [v|e es v Hedge Hpath IH]; intro Hu.
  - left; auto.
  - destruct (rpo_edge_classes EV g p roots Hready Hroots e Hu Hedge) as [Hforward|Hback].
    + pose proof (dfs_visited_edge EV g p roots e Hready Hroots Hu Hedge) as Htarget.
      destruct (IH Htarget) as [[Hnil Heq]|[Htail|[a [Ha Hretreat]]]].
      * right; left; rewrite <- Heq; exact Hforward.
      * right; left; eapply dfs_before_trans; [apply dfs_rpo_nodup; eassumption| |]; eassumption.
      * right; right; exists a; split; [right; exact Ha|exact Hretreat].
    + right; right; exists e; split; [left; reflexivity|exact Hback].
Qed.

(** A nonempty cycle through a visited vertex contains an edge retreating to a tree ancestor. *)
Theorem cycle_has_retreating_edge {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (v : V) (es : list E) (roots : list V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited (dfs p FinSet.empty roots)) = true ->
  es <> [] -> path g v es v ->
  exists e, In e es /\ retreating EV g (dfs p FinSet.empty roots) e.
Proof.
  intros Hready Hroots Hv Hnonempty Hpath.
  destruct (dfs_path_classes EV g p roots v es v Hready Hroots Hpath Hv)
    as [[Hnil _]|[Hbefore|Hretreat]]; [contradiction| |exact Hretreat].
  exfalso; apply (dfs_before_irrefl _ v (dfs_rpo_nodup EV g p roots Hready Hroots)); exact Hbefore.
Qed.
