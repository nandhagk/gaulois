(** * Conservative backward memory queries

    Indexed backward walks retain terminals and every frontier stopped by fuel or a revisit.
    For example, a write to another site is skipped, whereas an unknown call remains a root.
    Builds on: AnalysesMemoryGraph, AnalysesMemoryFrontier and AnalysesMemoryBase. *)

From Stdlib Require Import List Bool Arith PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
From Gaulois.Domains Require Import DomainsFootprint.
From Gaulois.Views Require Import ViewsGraph ViewsMemoryEffects.
From Gaulois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemoryBase.
Import List.ListNotations.

(** A successful scope test excludes a common byte at every allocation site. *)
Definition memory_scopes_disjoint {T} (ET : encoding T) (a b : memory_scope T) : bool :=
  match a, b with
  | MemoryRegions fs, MemoryRegions gs => footprints_disjoint ET fs gs
  | _, _ => false
  end.

(** Every effect except a write can carry a read observation. *)
Definition memory_effect_has_read {T} (a : memory_effect T) : bool :=
  match a with
  | MemoryWrite _ => false
  | _ => true
  end.

(** Positively disjoint scopes share no covered byte. *)
Theorem memory_scopes_disjoint_sound {T} (ET : encoding T) (a b : memory_scope T) :
  memory_scopes_disjoint ET a b = true -> forall t o,
    memory_scope_covers a t o -> memory_scope_covers b t o -> False.
Proof.
  destruct a as [fs|], b as [gs|]; cbn [memory_scopes_disjoint memory_scope_covers];
    try discriminate; apply footprints_disjoint_sound.
Qed.

(** Backward steps skip only proved disjoint definitions and select explicit phi operands. *)
Inductive memory_walk_next {N E T} (ET : encoding T) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> memory_version N E -> Prop :=
  | memory_walk_skip_def : forall e i a previous,
      nth_error (effects e) i = Some a -> effect_is_def a = true ->
      memory_scopes_disjoint ET (effect_writes a) q = true ->
      memory_before mg e i = Some previous ->
      memory_walk_next ET effects mg q (MemoryDef e i) previous
  | memory_walk_phi : forall n key previous,
      memory_operand mg n key = Some previous ->
      memory_walk_next ET effects mg q (MemoryPhi n) previous.

(** A trace retains all versions, including repeated dynamic visits. *)
Inductive memory_walk_trace {N E T} (ET : encoding T)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (q : memory_scope T) :
    memory_version N E -> list (memory_version N E) -> Prop :=
  | memory_walk_single : forall v, memory_walk_trace ET effects mg q v [v]
  | memory_walk_cons : forall v w rest, memory_walk_next ET effects mg q v w ->
      memory_walk_trace ET effects mg q w rest -> memory_walk_trace ET effects mg q v (v :: rest).

(** The last element is absent only for an empty list. *)
Fixpoint memory_trace_last {A} (xs : list A) : option A :=
  match xs with
  | [] => None
  | [x] => Some x
  | _ :: rest => memory_trace_last rest
  end.

(** A terminal version has no permitted backward successor. *)
Definition memory_walk_terminal {N E T} (ET : encoding T)
    (effects : E -> list (memory_effect T)) (mg : memory_graph N E) (q : memory_scope T)
    (v : memory_version N E) : Prop :=
  forall w, ~ memory_walk_next ET effects mg q v w.

(** Roots include conservative cuts whenever the finite search is incomplete. *)
Record memory_clobber_result (N E : Type) : Type := MemoryClobberResult {
  clobber_roots : list (memory_version N E);
  clobber_complete : bool
}.

Arguments MemoryClobberResult {N E}.
Arguments clobber_roots {N E}.
Arguments clobber_complete {N E}.

(** * A finite worklist certificate

    Discovery ranks strictly increase along expanded edges unless an edge meets a retained cut
    or pending work. Revisited versions become cuts, so convergence and cycles are both safe. *)

Inductive memory_search_path {V} (next : V -> list V) : V -> list V -> Prop :=
  | memory_search_single : forall v, memory_search_path next v [v]
  | memory_search_cons : forall v w xs, In w (next v) -> memory_search_path next w xs ->
      memory_search_path next v (v :: xs).

Definition memory_search_reaches {V} (next : V -> list V) (start v : V) : Prop :=
  exists xs, memory_search_path next start xs /\ memory_trace_last xs = Some v.

Lemma memory_search_nonempty {V} next v (xs : list V) :
  memory_search_path next v xs -> xs <> [].
Proof.
  intro Hpath; destruct Hpath; discriminate.
Qed.

Lemma memory_search_head {V} next v (xs : list V) :
  memory_search_path next v xs -> In v xs.
Proof.
  intro Hpath; destruct Hpath; left; reflexivity.
Qed.

Lemma memory_search_last_cons {V} next v w (xs : list V) :
  memory_search_path next w xs -> memory_trace_last (v :: xs) = memory_trace_last xs.
Proof.
  intro Hpath; destruct Hpath; reflexivity.
Qed.

Lemma memory_search_refl {V} next (v : V) : memory_search_reaches next v v.
Proof.
  exists [v]; split; [constructor|reflexivity].
Qed.

Lemma memory_search_extend {V} next start (v w : V) :
  memory_search_reaches next start v -> In w (next v) -> memory_search_reaches next start w.
Proof.
  intros [xs [Hpath Hlast]] Hedge; induction Hpath as [head|head u xs Hvu Hpath IH].
  - cbn in Hlast; inversion Hlast; subst v; exists [head; w]; split.
    + econstructor; [exact Hedge|constructor].
    + reflexivity.
  - rewrite (memory_search_last_cons next head u xs Hpath) in Hlast.
    destruct (IH Hlast) as [ys [Hys Hlastys]].
    exists (head :: ys); split; [econstructor; eassumption|].
    rewrite (memory_search_last_cons next head u ys Hys); exact Hlastys.
Qed.

Record memory_search_state (V : Type) : Type := MemorySearchState {
  memory_search_todo : list V;
  memory_search_seen : Map.t V nat;
  memory_search_clock : nat;
  memory_search_roots : FinSet.t V;
  memory_search_complete : bool
}.

Arguments MemorySearchState {V}.
Arguments memory_search_todo {V}.
Arguments memory_search_seen {V}.
Arguments memory_search_clock {V}.
Arguments memory_search_roots {V}.
Arguments memory_search_complete {V}.

Definition memory_search_start {V} (v : V) : memory_search_state V :=
  MemorySearchState [v] Map.empty 0 FinSet.empty true.

Definition memory_search_step {V} (EV : encoding V) (next : V -> list V)
    (st : memory_search_state V) : memory_search_state V :=
  match memory_search_todo st with
  | [] => st
  | v :: rest =>
    match Map.get EV v (memory_search_seen st) with
    | Some _ => MemorySearchState rest (memory_search_seen st) (memory_search_clock st)
        (FinSet.add EV v (memory_search_roots st)) false
    | None =>
      let seen := Map.set EV v (memory_search_clock st) (memory_search_seen st) in
      match next v with
      | [] => MemorySearchState rest seen (S (memory_search_clock st))
          (FinSet.add EV v (memory_search_roots st)) (memory_search_complete st)
      | w :: ws => MemorySearchState ((w :: ws) ++ rest) seen (S (memory_search_clock st))
          (memory_search_roots st) (memory_search_complete st)
      end
    end
  end.

(** Binary fuel counts worklist transitions; empty work stops immediately. *)
Fixpoint memory_search_run {V} (EV : encoding V) (next : V -> list V) (fuel : positive)
    (st : memory_search_state V) : memory_search_state V :=
  match memory_search_todo st with
  | [] => st
  | _ =>
    match fuel with
    | xH => memory_search_step EV next st
    | xO half => memory_search_run EV next half (memory_search_run EV next half st)
    | xI half => memory_search_step EV next
        (memory_search_run EV next half (memory_search_run EV next half st))
    end
  end.

Record memory_search_invariant {V} (EV : encoding V) (next : V -> list V) (start : V)
    (st : memory_search_state V) : Prop := {
  memory_search_root_wf : FinSet.wf EV (memory_search_roots st);
  memory_search_rank_bound : forall v rank, Map.get EV v (memory_search_seen st) = Some rank ->
    rank < memory_search_clock st;
  memory_search_seen_terminal : forall v rank,
    Map.get EV v (memory_search_seen st) = Some rank -> next v = [] ->
    FinSet.mem EV v (memory_search_roots st) = true;
  memory_search_start_covered : In start (memory_search_todo st) \/
    FinSet.mem EV start (memory_search_roots st) = true \/
    exists rank, Map.get EV start (memory_search_seen st) = Some rank;
  memory_search_edges_covered : forall v rank w,
    Map.get EV v (memory_search_seen st) = Some rank -> In w (next v) ->
    In w (memory_search_todo st) \/ FinSet.mem EV w (memory_search_roots st) = true \/
    exists later, Map.get EV w (memory_search_seen st) = Some later /\ rank < later;
  memory_search_todo_reachable : forall v, In v (memory_search_todo st) ->
    memory_search_reaches next start v;
  memory_search_roots_reachable : forall v, FinSet.mem EV v (memory_search_roots st) = true ->
    memory_search_reaches next start v;
  memory_search_roots_terminal : memory_search_complete st = true -> forall v,
    FinSet.mem EV v (memory_search_roots st) = true -> next v = []
}.

Lemma memory_search_initial {V} (EV : encoding V) next (start : V) :
  memory_search_invariant EV next start (memory_search_start start).
Proof.
  constructor; cbn [memory_search_start memory_search_roots memory_search_seen
    memory_search_todo memory_search_clock memory_search_complete].
  - apply Map.wf_empty.
  - intros v rank Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v rank Hget; rewrite Map.get_empty in Hget; discriminate.
  - left; left; reflexivity.
  - intros v rank w Hget; rewrite Map.get_empty in Hget; discriminate.
  - intros v [->|Hfalse]; [apply memory_search_refl|contradiction].
  - intros v Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
  - intros _ v Hmem; rewrite FinSet.mem_empty in Hmem; discriminate.
Qed.

Lemma memory_search_repeat_invariant {V} (EV : encoding V) next start v rest seen clock roots
    complete :
  memory_search_invariant EV next start (MemorySearchState (v :: rest) seen clock roots complete) ->
  memory_search_invariant EV next start
    (MemorySearchState rest seen clock (FinSet.add EV v roots) false).
Proof.
  intros [Hwf Hbound Hseen_terminal Hstart Hedges Htodo Hroots Hterminal]; cbn in *.
  constructor; cbn.
  - apply Map.wf_set; exact Hwf.
  - exact Hbound.
  - intros u r Hget Hnext; apply FinSet.mem_add; right; eapply Hseen_terminal; eassumption.
  - destruct Hstart as [[Heq|Hin]|[Hroot|Hfound]].
    + subst start; right; left; apply FinSet.mem_add; left; reflexivity.
    + left; exact Hin.
    + right; left; apply FinSet.mem_add; right; exact Hroot.
    + right; right; exact Hfound.
  - intros u r w Hget Hedge; destruct (Hedges u r w Hget Hedge)
      as [[Heq|Hin]|[Hroot|Hlater]].
    + subst w; right; left; apply FinSet.mem_add; left; reflexivity.
    + left; exact Hin.
    + right; left; apply FinSet.mem_add; right; exact Hroot.
    + right; right; exact Hlater.
  - intros u Hin; apply Htodo; right; exact Hin.
  - intros u Hmem; apply FinSet.mem_add in Hmem as [->|Hmem].
    + apply Htodo; left; reflexivity.
    + apply Hroots; exact Hmem.
  - discriminate.
Qed.

Record memory_search_fresh_facts {V} (EV : encoding V) (next : V -> list V) start v rest
    (seen : Map.t V nat) clock roots : Prop := {
  memory_fresh_bound : forall u r, Map.get EV u (Map.set EV v clock seen) = Some r ->
    r < S clock;
  memory_fresh_start : In start rest \/ FinSet.mem EV start roots = true \/
    exists r, Map.get EV start (Map.set EV v clock seen) = Some r;
  memory_fresh_edges : forall u r w, Map.get EV u seen = Some r -> In w (next u) ->
    In w rest \/ FinSet.mem EV w roots = true \/
    exists later, Map.get EV w (Map.set EV v clock seen) = Some later /\ r < later
}.

Lemma memory_search_prepare_fresh {V} (EV : encoding V) next start v rest seen clock roots
    complete :
  memory_search_invariant EV next start (MemorySearchState (v :: rest) seen clock roots complete) ->
  Map.get EV v seen = None ->
  memory_search_fresh_facts EV next start v rest seen clock roots.
Proof.
  intros [Hwf Hbound Hseen_terminal Hstart Hedges Htodo Hroots Hterminal] Hseen; cbn in *.
  assert (Hold_get : forall u r, Map.get EV u seen = Some r ->
    Map.get EV u (Map.set EV v clock seen) = Some r).
  { intros u r Hget; rewrite Map.get_set_other; [exact Hget|congruence]. }
  constructor.
  - intros u r Hget; destruct (dfs_eq_dec EV u v) as [->|Hne].
    + rewrite Map.get_set_same in Hget; inversion Hget; lia.
    + rewrite Map.get_set_other in Hget by exact Hne; specialize (Hbound u r Hget); lia.
  - destruct Hstart as [[->|Hin]|[Hroot|[r Hget]]].
    + right; right; exists clock; apply Map.get_set_same.
    + left; exact Hin.
    + right; left; exact Hroot.
    + right; right; exists r; apply Hold_get; exact Hget.
  - intros u r w Hget Hedge; destruct (Hedges u r w Hget Hedge)
      as [[->|Hin]|[Hroot|[later [Hlater Hlt]]]].
    + right; right; exists clock; split; [apply Map.get_set_same|eapply Hbound; exact Hget].
    + left; exact Hin.
    + right; left; exact Hroot.
    + right; right; exists later; split; [apply Hold_get; exact Hlater|exact Hlt].
Qed.

Lemma memory_search_terminal_invariant {V} (EV : encoding V) next start v rest seen clock roots
    complete :
  memory_search_invariant EV next start (MemorySearchState (v :: rest) seen clock roots complete) ->
  memory_search_fresh_facts EV next start v rest seen clock roots -> next v = [] ->
  memory_search_invariant EV next start
    (MemorySearchState rest (Map.set EV v clock seen) (S clock) (FinSet.add EV v roots) complete).
Proof.
  intros [Hwf Hbound Hseen_terminal Hstart Hedges Htodo Hroots Hterminal]
    [Hnew_bound Hnew_start Hold_edges] Hnext; cbn in *; constructor; cbn.
  - apply Map.wf_set; exact Hwf.
  - exact Hnew_bound.
  - intros u r Hget Hnil; apply FinSet.mem_add.
    destruct (dfs_eq_dec EV u v) as [->|Hne]; [left; reflexivity|right].
    rewrite Map.get_set_other in Hget by exact Hne; eapply Hseen_terminal; eassumption.
  - destruct Hnew_start as [Hin|[Hroot|Hget]]; [left; exact Hin| |right; right; exact Hget].
    right; left; apply FinSet.mem_add; right; exact Hroot.
  - intros u r z Hget Hedge; destruct (dfs_eq_dec EV u v) as [->|Hne].
    + rewrite Hnext in Hedge; contradiction.
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (Hold_edges u r z Hget Hedge) as [Hin|[Hroot|Hlater]].
      * left; exact Hin.
      * right; left; apply FinSet.mem_add; right; exact Hroot.
      * right; right; exact Hlater.
  - intros u Hin; apply Htodo; right; exact Hin.
  - intros u Hmem; apply FinSet.mem_add in Hmem as [->|Hmem].
    + apply Htodo; left; reflexivity.
    + apply Hroots; exact Hmem.
  - intros Hcomplete u Hmem; apply FinSet.mem_add in Hmem as [->|Hmem].
    + exact Hnext.
    + apply Hterminal; assumption.
Qed.

Lemma memory_search_branch_invariant {V} (EV : encoding V) next start v rest seen clock roots
    complete w ws :
  memory_search_invariant EV next start (MemorySearchState (v :: rest) seen clock roots complete) ->
  memory_search_fresh_facts EV next start v rest seen clock roots -> next v = w :: ws ->
  memory_search_invariant EV next start
    (MemorySearchState ((w :: ws) ++ rest) (Map.set EV v clock seen) (S clock) roots complete).
Proof.
  intros [Hwf Hbound Hseen_terminal Hstart Hedges Htodo Hroots Hterminal]
    [Hnew_bound Hnew_start Hold_edges] Hnext; cbn in *; constructor; cbn.
  - exact Hwf.
  - exact Hnew_bound.
  - intros u r Hget Hnil; destruct (dfs_eq_dec EV u v) as [->|Hne]; [congruence|].
    rewrite Map.get_set_other in Hget by exact Hne; eapply Hseen_terminal; eassumption.
  - destruct Hnew_start as [Hin|Hrest].
    + left; change (In start ((w :: ws) ++ rest)); apply in_or_app; right; exact Hin.
    + right; exact Hrest.
  - intros u r z Hget Hedge; destruct (dfs_eq_dec EV u v) as [->|Hne].
    + left; change (In z ((w :: ws) ++ rest)); apply in_or_app; left.
      rewrite <- Hnext; exact Hedge.
    + rewrite Map.get_set_other in Hget by exact Hne.
      destruct (Hold_edges u r z Hget Hedge) as [Hin|Hrest].
      * left; change (In z ((w :: ws) ++ rest)); apply in_or_app; right; exact Hin.
      * right; exact Hrest.
  - intros u Hin; change (In u ((w :: ws) ++ rest)) in Hin.
    apply in_app_or in Hin as [Hin|Hin].
    + eapply memory_search_extend; [apply Htodo; left; reflexivity|].
      rewrite Hnext; exact Hin.
    + apply Htodo; right; exact Hin.
  - exact Hroots.
  - exact Hterminal.
Qed.

Lemma memory_search_step_invariant {V} (EV : encoding V) next start
    (st : memory_search_state V) :
  memory_search_invariant EV next start st ->
  memory_search_invariant EV next start (memory_search_step EV next st).
Proof.
  destruct st as [todo seen clock roots complete]; destruct todo as [|v rest];
    [exact (fun H => H)|].
  intro Hinv; cbn [memory_search_step memory_search_todo memory_search_seen].
  destruct (Map.get EV v seen) as [rank|] eqn:Hseen.
  - eapply memory_search_repeat_invariant; exact Hinv.
  - pose proof (memory_search_prepare_fresh EV next start v rest seen clock roots complete
      Hinv Hseen) as Hfresh.
    destruct (next v) as [|w ws] eqn:Hnext.
    + apply memory_search_terminal_invariant; assumption.
    + eapply memory_search_branch_invariant; eassumption.
Qed.

Lemma memory_search_run_invariant {V} (EV : encoding V) next start fuel
    (st : memory_search_state V) :
  memory_search_invariant EV next start st ->
  memory_search_invariant EV next start (memory_search_run EV next fuel st).
Proof.
  revert st; induction fuel as [half IH|half IH|]; intros st Hinv;
    cbn [memory_search_run]; destruct (memory_search_todo st); try exact Hinv.
  - apply memory_search_step_invariant, IH, IH; exact Hinv.
  - apply IH, IH; exact Hinv.
  - apply memory_search_step_invariant; exact Hinv.
Qed.

Definition memory_search_boundary {V} (EV : encoding V) (st : memory_search_state V)
    (v : V) : bool :=
  FinSet.mem EV v (memory_search_roots st) ||
    FinSet.mem EV v (FinSet.of_list EV (memory_search_todo st)).

Lemma memory_search_boundary_correct {V} (EV : encoding V) (st : memory_search_state V) v :
  memory_search_boundary EV st v = true <->
    FinSet.mem EV v (memory_search_roots st) = true \/ In v (memory_search_todo st).
Proof.
  unfold memory_search_boundary; rewrite orb_true_iff, FinSet.of_list_spec; reflexivity.
Qed.

Definition memory_search_result {V} (EV : encoding V) (st : memory_search_state V) : list V :=
  memory_distinct EV (FinSet.elements (memory_search_roots st) ++ memory_search_todo st).

Lemma memory_search_result_correct {V} (EV : encoding V) next start
    (st : memory_search_state V) v :
  memory_search_invariant EV next start st ->
  (In v (memory_search_result EV st) <-> memory_search_boundary EV st v = true).
Proof.
  intro Hinv; unfold memory_search_result; rewrite memory_distinct_in, in_app_iff.
  rewrite FinSet.elements_spec by exact (memory_search_root_wf _ _ _ _ Hinv).
  symmetry; apply memory_search_boundary_correct.
Qed.

Lemma memory_trace_last_in {V} (xs : list V) v : memory_trace_last xs = Some v -> In v xs.
Proof.
  induction xs as [|x xs IH]; [discriminate|].
  destruct xs as [|y ys].
  - cbn; intro Heq; inversion Heq; left; reflexivity.
  - intro Hlast; right; apply IH; exact Hlast.
Qed.

Lemma memory_search_rank_path {V} (EV : encoding V) next start
    (st : memory_search_state V) v xs rank :
  memory_search_invariant EV next start st -> memory_search_path next v xs ->
  (forall u, In u xs -> memory_search_boundary EV st u = false) ->
  Map.get EV v (memory_search_seen st) = Some rank ->
  NoDup xs /\ forall u, In u xs -> exists later,
    Map.get EV u (memory_search_seen st) = Some later /\ rank <= later.
Proof.
  intros Hinv Hpath; revert rank.
  induction Hpath as [v|v w xs Hedge Hpath IH]; intros rank Houtside Hget.
  - split.
    + constructor; [cbn; tauto|constructor].
    + intros u [->|Hfalse]; [exists rank; auto|contradiction].
  - assert (Hw : memory_search_boundary EV st w = false).
    { apply Houtside; right; apply (memory_search_head next w xs Hpath). }
    destruct (memory_search_edges_covered _ _ _ _ Hinv v rank w Hget Hedge)
      as [Hpending|[Hroot|[later [Hlater Hlt]]]].
    + exfalso; assert (Htrue : memory_search_boundary EV st w = true).
      { apply memory_search_boundary_correct; right; exact Hpending. }
      congruence.
    + exfalso; assert (Htrue : memory_search_boundary EV st w = true).
      { apply memory_search_boundary_correct; left; exact Hroot. }
      congruence.
    + destruct (IH later ltac:(intros u Hu; apply Houtside; right; exact Hu) Hlater)
        as [Hnodup Hranks].
      split.
      * constructor; [|exact Hnodup].
        intro Hin; destruct (Hranks v Hin) as [r [Hrank Hle]].
        rewrite Hget in Hrank; inversion Hrank; lia.
      * intros u [->|Hin].
        -- exists rank; auto.
        -- destruct (Hranks u Hin) as [r [Hrank Hle]]; exists r; split; [exact Hrank|lia].
Qed.

Lemma memory_search_cover {V} (EV : encoding V) next start
    (st : memory_search_state V) xs last :
  memory_search_invariant EV next start st -> memory_search_path next start xs ->
  memory_trace_last xs = Some last -> (next last = [] \/ ~ NoDup xs) ->
  exists hit, In hit xs /\ In hit (memory_search_result EV st).
Proof.
  intros Hinv Hpath Hlast Hend.
  destruct (existsb (memory_search_boundary EV st) xs) eqn:Hhit.
  - apply existsb_exists in Hhit; destruct Hhit as [hit [Hin Hmem]].
    exists hit; split; [exact Hin|apply (memory_search_result_correct EV next start st hit Hinv)].
    exact Hmem.
  - assert (Houtside : forall u, In u xs -> memory_search_boundary EV st u = false).
    { intros u Hin; destruct (memory_search_boundary EV st u) eqn:Hmem; [|reflexivity].
      assert (Htrue : existsb (memory_search_boundary EV st) xs = true).
      { apply existsb_exists; exists u; auto. }
      congruence. }
    assert (Hstart : memory_search_boundary EV st start = false).
    { apply Houtside; apply (memory_search_head next start xs Hpath). }
    destruct (memory_search_start_covered _ _ _ _ Hinv) as [Hpending|[Hroot|[rank Hget]]].
    + exfalso; assert (Htrue : memory_search_boundary EV st start = true).
      { apply memory_search_boundary_correct; right; exact Hpending. }
      congruence.
    + exfalso; assert (Htrue : memory_search_boundary EV st start = true).
      { apply memory_search_boundary_correct; left; exact Hroot. }
      congruence.
    + destruct (memory_search_rank_path EV next start st start xs rank Hinv Hpath Houtside Hget)
        as [Hnodup Hranks].
      exfalso; destruct Hend as [Hnil|Hcycle]; [|contradiction].
      destruct (Hranks last (memory_trace_last_in xs last Hlast)) as [r [Hrank Hle]].
      assert (Htrue : memory_search_boundary EV st last = true).
      { apply memory_search_boundary_correct; left.
        eapply (memory_search_seen_terminal _ _ _ _ Hinv); eassumption. }
      specialize (Houtside last (memory_trace_last_in xs last Hlast)); congruence.
Qed.

Lemma memory_search_result_reachable {V} (EV : encoding V) next start
    (st : memory_search_state V) v :
  memory_search_invariant EV next start st -> In v (memory_search_result EV st) ->
  memory_search_reaches next start v.
Proof.
  intros Hinv Hin; apply (memory_search_result_correct EV next start st v Hinv) in Hin.
  apply memory_search_boundary_correct in Hin as [Hroot|Htodo].
  - apply (memory_search_roots_reachable _ _ _ _ Hinv); exact Hroot.
  - apply (memory_search_todo_reachable _ _ _ _ Hinv); exact Htodo.
Qed.

Lemma memory_search_result_terminal {V} (EV : encoding V) next start
    (st : memory_search_state V) v :
  memory_search_invariant EV next start st -> memory_search_todo st = [] ->
  memory_search_complete st = true -> In v (memory_search_result EV st) -> next v = [].
Proof.
  intros Hinv Hdone Hcomplete Hin.
  apply (memory_search_result_correct EV next start st v Hinv) in Hin.
  apply memory_search_boundary_correct in Hin as [Hroot|Htodo].
  - apply (memory_search_roots_terminal _ _ _ _ Hinv); assumption.
  - rewrite Hdone in Htodo; contradiction.
Qed.

(** * Prepared memory adjacency *)

Fixpoint memory_walk_effects_from {T} (start : nat) (xs : list (memory_effect T)) :
    Map.t nat (memory_effect T) :=
  match xs with
  | [] => Map.empty
  | a :: rest => Map.set nat_encoding start a (memory_walk_effects_from (S start) rest)
  end.

Lemma memory_walk_effects_lookup {T} (xs : list (memory_effect T)) start i :
  Map.get nat_encoding (start + i) (memory_walk_effects_from start xs) = nth_error xs i.
Proof.
  revert start i; induction xs as [|a xs IH]; intros start [|i];
    cbn [memory_walk_effects_from nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same.
  - rewrite Map.get_set_other by lia.
    replace (start + S i) with (S start + i) by lia; apply IH.
Qed.

Definition memory_walk_effect_table {N E T} (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) : Map.t E (Map.t nat (memory_effect T)) :=
  memory_result_index EE (fun e => memory_walk_effects_from 0 (effects e))
    (memory_distinct EE (edges_of g)).

Definition memory_walk_effect_get {E T} (EE : encoding E)
    (table : Map.t E (Map.t nat (memory_effect T))) (e : E) (i : nat) :
    option (memory_effect T) :=
  match Map.get EE e table with
  | Some row => Map.get nat_encoding i row
  | None => None
  end.

Lemma memory_walk_effect_get_correct {N E T} (EE : encoding E) (g : Graph.t N E)
    (effects : E -> list (memory_effect T)) e i :
  In e (edges_of g) ->
  memory_walk_effect_get EE (memory_walk_effect_table EE g effects) e i = nth_error (effects e) i.
Proof.
  intro Hin; unfold memory_walk_effect_get, memory_walk_effect_table.
  rewrite memory_result_index_at by (apply memory_distinct_in; exact Hin).
  change (Map.get nat_encoding (0 + i) (memory_walk_effects_from 0 (effects e)) =
    nth_error (effects e) i); apply memory_walk_effects_lookup.
Qed.

Definition memory_walk_operands {N E} (mg : memory_graph N E) n (keys : list (option E)) :
    list (memory_version N E) :=
  flat_map (fun key => match memory_operand mg n key with
    | Some v => [v]
    | None => []
    end) keys.

Lemma memory_walk_operands_correct {N E} (mg : memory_graph N E) n keys v :
  In v (memory_walk_operands mg n keys) <->
    exists key, In key keys /\ memory_operand mg n key = Some v.
Proof.
  unfold memory_walk_operands; rewrite in_flat_map; split.
  - intros [key [Hin Hvalue]]; destruct (memory_operand mg n key) as [w|] eqn:Hget;
      cbn in Hvalue; [|contradiction].
    destruct Hvalue as [->|Hfalse]; [exists key; auto|contradiction].
  - intros [key [Hin Hget]]; exists key; split; [exact Hin|].
    rewrite Hget; left; reflexivity.
Qed.

Definition memory_walk_raw_next {N E T} (EE : encoding E) (ET : encoding T)
    (table : Map.t E (Map.t nat (memory_effect T)))
    (incoming : N -> list E) (mg : memory_graph N E) (q : memory_scope T)
    (v : memory_version N E) : list (memory_version N E) :=
  match v with
  | MemoryLive => []
  | MemoryPhi n => memory_walk_operands mg n (None :: map Some (incoming n))
  | MemoryDef e i =>
    match memory_walk_effect_get EE table e i, memory_before mg e i with
    | Some a, Some previous =>
      if effect_is_def a && memory_scopes_disjoint ET (effect_writes a) q then [previous] else []
    | _, _ => []
    end
  end.

Definition memory_walk_index {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) : Map.t (memory_version N E) (list (memory_version N E)) :=
  let table := memory_walk_effect_table EE g effects in
  let p := prepare EN g in
  memory_result_index (memory_frontier_version_encoding EN EE)
    (memory_walk_raw_next EE ET table (pred_edges p) mg q) (memory_versions mg).

Definition memory_walk_successors {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) : memory_version N E -> list (memory_version N E) :=
  index_edges (memory_frontier_version_encoding EN EE) (memory_walk_index EN EE ET g effects mg q).

Lemma memory_walk_edge_listed {N E T} (g : Graph.t N E) effects (mg : memory_graph N E)
    (Hwf : @memory_graph_wf N E T g effects mg) e :
  In e (Graph.out g (Graph.source g e)) -> reachable g (Graph.source g e) -> In e (edges_of g).
Proof.
  intros Hedge Hreach; apply in_flat_map; exists (Graph.source g e); split; [|exact Hedge].
  apply (reachable_in_nodes g _ (memory_cfg_wf Hwf)); exact Hreach.
Qed.

Lemma memory_walk_operand_key {N E T} (EN : encoding N) (g : Graph.t N E)
    effects (mg : memory_graph N E) (Hwf : @memory_graph_wf N E T g effects mg) n key previous :
  memory_operand mg n key = Some previous ->
  In key (None :: map Some (pred_edges (prepare EN g) n)).
Proof.
  intro Hoperand; destruct key as [e|]; [right|left; reflexivity].
  apply in_map; rewrite prepare_pred; apply filter_In.
  destruct (proj1 (memory_operand_domain Hwf n (Some e)) (ex_intro _ previous Hoperand))
    as [_ [Hedge [Hreach Htarget]]].
  split.
  - eapply memory_walk_edge_listed; eassumption.
  - rewrite Htarget; apply Pos.eqb_refl.
Qed.

Lemma memory_walk_successors_correct {N E T} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) effects (mg : memory_graph N E) q v w :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (In w (memory_walk_successors EN EE ET g effects mg q v) <->
    memory_walk_next ET effects mg q v w).
Proof.
  intros Hwf Hvalid; unfold memory_walk_successors, memory_walk_index, index_edges.
  rewrite memory_result_index_at by (apply (memory_versions_exact Hwf); exact Hvalid).
  destruct v as [|n|e i]; cbn [memory_walk_raw_next].
  - split; [contradiction|intro Hnext; inversion Hnext].
  - rewrite memory_walk_operands_correct; split.
    + intros [key [_ Hget]]; eapply memory_walk_phi; exact Hget.
    + intro Hnext; inversion Hnext as [|node key previous Hget]; subst.
      exists key; split; [eapply memory_walk_operand_key; eassumption|exact Hget].
  - destruct Hvalid as [a [[Hedge [Hreach Hnth]] Hdef]].
    rewrite memory_walk_effect_get_correct by (eapply memory_walk_edge_listed; eassumption).
    rewrite Hnth, Hdef; cbn [andb].
    destruct (memory_before mg e i) as [previous|] eqn:Hbefore;
      destruct (memory_scopes_disjoint ET (effect_writes a) q) eqn:Hdisjoint; cbn.
    + split.
      * intros [->|Hfalse]; [eapply memory_walk_skip_def; eassumption|contradiction].
      * intro Hnext; inversion Hnext as [edge j observed prev Hfound Hdefines Hclear Hlookup|];
          subst; rewrite Hnth in Hfound; inversion Hfound; subst; left; congruence.
    + split; [contradiction|intro Hnext].
      inversion Hnext as [edge j observed prev Hfound Hdefines Hclear Hlookup|]; subst.
      rewrite Hnth in Hfound; inversion Hfound; subst; congruence.
    + split; [contradiction|intro Hnext].
      inversion Hnext as [edge j observed prev Hfound Hdefines Hclear Hlookup|]; subst; congruence.
    + split; [contradiction|intro Hnext].
      inversion Hnext as [edge j observed prev Hfound Hdefines Hclear Hlookup|]; subst; congruence.
Qed.

Lemma memory_walk_operand_valid {N E T} (g : Graph.t N E) effects (mg : memory_graph N E)
    (Hwf : @memory_graph_wf N E T g effects mg) n key previous :
  memory_operand mg n key = Some previous -> memory_valid_version g effects mg previous.
Proof.
  intro Hget; destruct (proj1 (memory_operand_domain Hwf n key) (ex_intro _ previous Hget))
    as [Hphi Hkey].
  destruct key as [e|].
  - destruct Hkey as [Hedge [Hreach Htarget]].
    pose proof (memory_edges_arrive Hwf e Hedge Hreach) as Harrival; rewrite Htarget in Harrival.
    destruct Harrival as [[_ [Hoperand _]]|[Hnot _]]; [|contradiction].
    rewrite Hget in Hoperand; inversion Hoperand; subst previous.
    apply (memory_out_valid Hwf); assumption.
  - pose proof (memory_entries_arrive Hwf n Hkey) as Harrival.
    destruct Harrival as [[_ [Hoperand _]]|[Hnot _]]; [|contradiction].
    rewrite Hget in Hoperand; inversion Hoperand; subst previous; exact I.
Qed.

Lemma memory_walk_next_valid {N E T} (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q v w :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  memory_walk_next ET effects mg q v w -> memory_valid_version g effects mg w.
Proof.
  intros Hwf Hvalid Hnext; destruct Hnext as [e i a previous Hnth Hdef Hclear Hbefore|
    n key previous Hoperand].
  - destruct Hvalid as [observed [Hocc Hdefines]].
    destruct (memory_occurrence_input_valid g effects mg Hwf e i observed Hocc)
      as [input [Hinput [Hvalid _]]].
    rewrite Hbefore in Hinput; inversion Hinput; subst input; exact Hvalid.
  - eapply memory_walk_operand_valid; eassumption.
Qed.

Lemma memory_walk_trace_valid {N E T} (ET : encoding T) (g : Graph.t N E) effects
    (mg : memory_graph N E) q v xs :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  memory_walk_trace ET effects mg q v xs ->
  forall w, In w xs -> memory_valid_version g effects mg w.
Proof.
  intros Hwf Hvalid Htrace; revert Hvalid.
  induction Htrace as [v|v u xs Hedge Htrace IH]; intros Hvalid w Hin.
  - destruct Hin as [->|Hfalse]; [exact Hvalid|contradiction].
  - destruct Hin as [->|Hin]; [exact Hvalid|].
    apply IH; [eapply memory_walk_next_valid; eassumption|exact Hin].
Qed.

Lemma memory_walk_trace_search {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) effects (mg : memory_graph N E) q v xs :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (memory_walk_trace ET effects mg q v xs <->
    memory_search_path (memory_walk_successors EN EE ET g effects mg q) v xs).
Proof.
  intros Hwf Hvalid; split; intro Htrace; revert Hvalid.
  - induction Htrace as [v|v w xs Hedge Htrace IH]; intro Hvalid.
    + constructor.
    + econstructor.
      * apply (memory_walk_successors_correct EN EE ET g effects mg q v w Hwf Hvalid).
        exact Hedge.
      * apply IH; eapply memory_walk_next_valid; eassumption.
  - induction Htrace as [v|v w xs Hedge Htrace IH]; intro Hvalid.
    + constructor.
    + apply (memory_walk_successors_correct EN EE ET g effects mg q v w Hwf Hvalid) in Hedge.
      econstructor; [exact Hedge|apply IH; eapply memory_walk_next_valid; eassumption].
Qed.

Lemma memory_walk_terminal_correct {N E T} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) effects (mg : memory_graph N E) q v :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg v ->
  (memory_walk_successors EN EE ET g effects mg q v = [] <->
    memory_walk_terminal ET effects mg q v).
Proof.
  intros Hwf Hvalid; split.
  - intros Hnil w Hnext.
    apply (memory_walk_successors_correct EN EE ET g effects mg q v w Hwf Hvalid) in Hnext.
    rewrite Hnil in Hnext; contradiction.
  - intro Hterminal; destruct (memory_walk_successors EN EE ET g effects mg q v)
      as [|w ws] eqn:Hnext; [reflexivity|].
    exfalso; apply (Hterminal w).
    apply (memory_walk_successors_correct EN EE ET g effects mg q v w Hwf Hvalid).
    rewrite Hnext; left; reflexivity.
Qed.

(** The finite query materializes adjacency once and retains every pending version on cutoff. *)
Definition memory_clobbers {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
    memory_clobber_result N E :=
  let EV := memory_frontier_version_encoding EN EE in
  let next := memory_walk_successors EN EE ET g effects mg q in
  let st := memory_search_run EV next fuel (memory_search_start start) in
  MemoryClobberResult (memory_search_result EV st)
    (memory_search_complete st && match memory_search_todo st with [] => true | _ => false end).

(** Every terminal or repeated backward trace meets a retained terminal or conservative cut. *)
Theorem memory_clobbers_cover {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg start ->
  forall trace last, memory_walk_trace ET effects mg q start trace ->
    memory_trace_last trace = Some last ->
    (memory_walk_terminal ET effects mg q last \/ ~ NoDup trace) ->
    exists hit, In hit trace /\ In hit (clobber_roots (memory_clobbers EN EE ET g effects mg q
      start fuel)).
Proof.
  intros Hwf Hvalid trace last Htrace Hlast Hend.
  unfold memory_clobbers; cbn [clobber_roots].
  eapply memory_search_cover.
  - apply memory_search_run_invariant, memory_search_initial.
  - apply (memory_walk_trace_search EN EE ET g effects mg q start trace Hwf Hvalid); exact Htrace.
  - exact Hlast.
  - destruct Hend as [Hterminal|Hcycle]; [left|right; exact Hcycle].
    apply (memory_walk_terminal_correct EN EE ET g effects mg q last Hwf).
    + eapply memory_walk_trace_valid; [exact Hwf|exact Hvalid|exact Htrace|].
      eapply memory_trace_last_in; exact Hlast.
    + exact Hterminal.
Qed.

Lemma memory_walk_terminal_hit {N E T} (ET : encoding T) effects (mg : memory_graph N E)
    q v xs hit :
  memory_walk_trace ET effects mg q v xs -> In hit xs ->
  memory_walk_terminal ET effects mg q hit -> memory_trace_last xs = Some hit.
Proof.
  intro Htrace; induction Htrace as [v|v w xs Hedge Htrace IH]; intros Hin Hterminal.
  - destruct Hin as [->|Hfalse]; [reflexivity|contradiction].
  - destruct Hin as [->|Hin].
    + exfalso; exact (Hterminal w Hedge).
    + destruct Htrace; cbn [memory_trace_last]; apply IH; assumption.
Qed.

(** A completed search returns exactly the reachable backward terminals. *)
Theorem memory_clobbers_complete {N E T} (EN : encoding N) (EE : encoding E) (ET : encoding T)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E)
    (q : memory_scope T) (start : memory_version N E) (fuel : positive) :
  memory_graph_wf g effects mg -> memory_valid_version g effects mg start ->
  clobber_complete (memory_clobbers EN EE ET g effects mg q start fuel) = true ->
  forall v, In v (clobber_roots (memory_clobbers EN EE ET g effects mg q start fuel)) <->
    memory_walk_terminal ET effects mg q v /\
    exists trace, memory_walk_trace ET effects mg q start trace /\
      memory_trace_last trace = Some v.
Proof.
  intros Hwf Hvalid Hcomplete.
  set (EV := memory_frontier_version_encoding EN EE).
  set (next := memory_walk_successors EN EE ET g effects mg q).
  set (st := memory_search_run EV next fuel (memory_search_start start)).
  assert (Hinv : memory_search_invariant EV next start st).
  { apply memory_search_run_invariant, memory_search_initial. }
  change (memory_search_complete st &&
    match memory_search_todo st with [] => true | _ => false end = true) in Hcomplete.
  apply andb_true_iff in Hcomplete as [Hcomplete Hdone].
  assert (Hempty : memory_search_todo st = []).
  { destruct (memory_search_todo st); [reflexivity|discriminate]. }
  assert (Hroot : forall v, In v (memory_search_result EV st) ->
    memory_walk_terminal ET effects mg q v /\ exists trace,
    memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace = Some v).
  { intros v Hin.
    destruct (memory_search_result_reachable EV next start st v Hinv Hin)
      as [trace [Htrace Hlast]].
    apply (memory_walk_trace_search EN EE ET g effects mg q start trace Hwf Hvalid) in Htrace.
    split.
    - apply (memory_walk_terminal_correct EN EE ET g effects mg q v Hwf).
      + eapply memory_walk_trace_valid; [exact Hwf|exact Hvalid|exact Htrace|].
        eapply memory_trace_last_in; exact Hlast.
      + eapply memory_search_result_terminal; eassumption.
    - exists trace; auto. }
  intro v; change (In v (memory_search_result EV st) <->
    memory_walk_terminal ET effects mg q v /\ exists trace,
    memory_walk_trace ET effects mg q start trace /\ memory_trace_last trace = Some v).
  split; [apply Hroot|].
  intros [Hterminal [trace [Htrace Hlast]]].
  destruct (memory_clobbers_cover EN EE ET g effects mg q start fuel Hwf Hvalid
    trace v Htrace Hlast (or_introl Hterminal)) as [hit [Hhit Hroot_hit]].
  change (In hit (memory_search_result EV st)) in Hroot_hit.
  pose proof (memory_walk_terminal_hit ET effects mg q start trace hit Htrace Hhit
    (proj1 (Hroot hit Hroot_hit))) as Heq.
  rewrite Hlast in Heq; inversion Heq; subst hit; exact Hroot_hit.
Qed.

(** * Backward walks on the actual dynamic history *)

(** Only definitions whose writes may overlap replace the last may-clobber. *)
Fixpoint memory_last_clobbers {N E T} (ET : encoding T) (q : memory_scope T) (e : E)
    (i : nat) (effects : list (memory_effect T)) (origin : memory_version N E) :
    memory_version N E :=
  match effects with
  | [] => origin
  | a :: rest =>
    memory_last_clobbers ET q e (S i) rest
      (if effect_is_def a && negb (memory_scopes_disjoint ET (effect_writes a) q)
       then MemoryDef e i else origin)
  end.

(** The fold follows every actual edge visit in its original execution order. *)
Definition memory_path_last_clobber {N E T} (ET : encoding T) (q : memory_scope T)
    (effects : E -> list (memory_effect T)) (es : list E) : memory_version N E :=
  fold_left (fun origin e => memory_last_clobbers ET q e 0 (effects e) origin) es MemoryLive.

Lemma memory_walk_live_terminal {N E T} (ET : encoding T) effects (mg : memory_graph N E) q :
  memory_walk_terminal ET effects mg q MemoryLive.
Proof.
  intros w Hnext; inversion Hnext.
Qed.

Lemma memory_walk_clobber_terminal {N E T} (ET : encoding T) effects
    (mg : memory_graph N E) q e i a :
  nth_error (effects e) i = Some a -> memory_scopes_disjoint ET (effect_writes a) q = false ->
  memory_walk_terminal ET effects mg q (MemoryDef e i).
Proof.
  intros Hnth Hclear w Hnext.
  inversion Hnext as [edge j observed previous Hfound Hdef Hdisjoint Hbefore|]; subst.
  rewrite Hnth in Hfound; inversion Hfound; subst observed; congruence.
Qed.

Lemma memory_walk_arrival_trace {N E T} (ET : encoding T) effects (mg : memory_graph N E)
    q n key input trace last :
  memory_arrival mg n key input -> memory_walk_trace ET effects mg q input trace ->
  memory_trace_last trace = Some last -> exists arrived,
    memory_walk_trace ET effects mg q (memory_in mg n) arrived /\
    memory_trace_last arrived = Some last.
Proof.
  intros [[Hphi [Hoperand Hinput]]|[Hnot Hinput]] Htrace Hlast.
  - exists (MemoryPhi n :: trace); split.
    + rewrite Hinput; econstructor; [eapply memory_walk_phi; exact Hoperand|exact Htrace].
    + destruct Htrace; exact Hlast.
  - rewrite Hinput; exists trace; auto.
Qed.

Lemma memory_walk_edge_history {N E T} (ET : encoding T) effects (mg : memory_graph N E)
    q e start xs input origin output last :
  memory_edge_provenance mg e start xs input origin output last ->
  (forall j a, nth_error xs j = Some a -> nth_error (effects e) (start + j) = Some a) ->
  forall trace clobber, memory_walk_trace ET effects mg q input trace ->
    memory_trace_last trace = Some clobber -> memory_walk_terminal ET effects mg q clobber ->
    exists result, memory_walk_trace ET effects mg q output result /\
      memory_trace_last result = Some (memory_last_clobbers ET q e start xs clobber) /\
      memory_walk_terminal ET effects mg q (memory_last_clobbers ET q e start xs clobber).
Proof.
  intro Hflow; induction Hflow as [start input origin|
    start a xs input origin output last Hbefore Hflow IH]; intros Hpositions trace clobber
    Htrace Hlast Hterminal.
  - exists trace; auto.
  - assert (Hposition : nth_error (effects e) start = Some a).
    { replace start with (start + 0) by lia; apply Hpositions; reflexivity. }
    assert (Hrest : forall j observed, nth_error xs j = Some observed ->
      nth_error (effects e) (S start + j) = Some observed).
    { intros j observed Hnth; replace (S start + j) with (start + S j) by lia.
      apply Hpositions; exact Hnth. }
    cbn [memory_last_clobbers].
    unfold memory_after in IH.
    destruct (effect_is_def a) eqn:Hdef; cbn [andb] in *.
    + destruct (memory_scopes_disjoint ET (effect_writes a) q) eqn:Hclear; cbn [negb].
      * apply (IH Hrest (MemoryDef e start :: trace) clobber).
        -- econstructor; [eapply memory_walk_skip_def; eassumption|exact Htrace].
        -- destruct Htrace; exact Hlast.
        -- exact Hterminal.
      * apply (IH Hrest [MemoryDef e start] (MemoryDef e start)).
        -- constructor.
        -- reflexivity.
        -- eapply memory_walk_clobber_terminal; eassumption.
    + apply (IH Hrest trace clobber); assumption.
Qed.

Lemma memory_walk_provenance_history {N E T} (ET : encoding T) (g : Graph.t N E)
    effects (mg : memory_graph N E) q root es n input origin :
  memory_provenance g effects mg root es n input origin -> exists trace,
    memory_walk_trace ET effects mg q input trace /\
    memory_trace_last trace = Some (memory_path_last_clobber ET q effects es) /\
    memory_walk_terminal ET effects mg q (memory_path_last_clobber ET q effects es).
Proof.
  intro Hprovenance; induction Hprovenance as [Hentry Harrival|
    es e origin last Hprovenance IH Hedge Hflow Harrival].
  - destruct (memory_walk_arrival_trace ET effects mg q root None MemoryLive [MemoryLive]
      MemoryLive Harrival (memory_walk_single ET effects mg q MemoryLive) eq_refl)
      as [trace [Htrace Hlast]].
    exists trace; split; [exact Htrace|split; [exact Hlast|apply memory_walk_live_terminal]].
  - destruct IH as [trace [Htrace [Hlast Hterminal]]].
    destruct (memory_walk_edge_history ET effects mg q e 0 (effects e) _ _ _ _ Hflow
      ltac:(intros j a Hnth; exact Hnth) trace _ Htrace Hlast Hterminal)
      as [edge_trace [Hedge_trace [Hedge_last Hedge_terminal]]].
    destruct (memory_walk_arrival_trace ET effects mg q _ (Some e) _ edge_trace _
      Harrival Hedge_trace Hedge_last) as [arrived [Harrived Harrived_last]].
    unfold memory_path_last_clobber; rewrite fold_left_app; cbn [fold_left].
    exists arrived; split; [exact Harrived|split; assumption].
Qed.

Lemma memory_walk_prefix_position {A} (xs : list A) i j a :
  nth_error (firstn i xs) j = Some a -> nth_error xs j = Some a.
Proof.
  revert xs j; induction i as [|i IH]; intros [|x xs] [|j] Hnth;
    cbn [firstn nth_error] in *; try discriminate; [exact Hnth|eapply IH; exact Hnth].
Qed.

(** The selected dynamic history reaches its last may-clobber and meets the computed frontier. *)
Theorem memory_clobbers_follow_execution {N E T} (EN : encoding N) (EE : encoding E)
    (ET : encoding T) (g : Graph.t N E) (effects : E -> list (memory_effect T))
    (mg : memory_graph N E) (q : memory_scope T) (fuel : positive) :
  memory_graph_wf g effects mg ->
  forall root es e i a, In root (Graph.entries g) -> path g root es (Graph.source g e) ->
    memory_occurrence g effects e i a -> exists input origin trace hit,
    memory_provenance g effects mg root es (Graph.source g e)
      (memory_in mg (Graph.source g e)) (memory_last_path effects es) /\
    memory_occurrence_history g effects mg es e i input origin /\
    memory_walk_trace ET effects mg q input trace /\
    memory_trace_last trace = Some
      (memory_last_clobbers ET q e 0 (firstn i (effects e))
        (memory_path_last_clobber ET q effects es)) /\
    In hit trace /\ In hit (clobber_roots (memory_clobbers EN EE ET g effects mg q input fuel)).
Proof.
  intros Hwf root es e i a Hentry Hpath Hocc.
  destruct (memory_definition_before_occurrence g effects mg Hwf root es e i a Hentry Hpath Hocc)
    as [input [origin [Hprovenance Hhistory]]].
  destruct (memory_walk_provenance_history ET g effects mg q root es _ _ _ Hprovenance)
    as [prefix [Hprefix [Hprefix_last Hprefix_terminal]]].
  destruct Hhistory as [Hbefore [Hflow Horigin]].
  destruct (memory_walk_edge_history ET effects mg q e 0 (firstn i (effects e)) _ _ _ _ Hflow
    ltac:(intros j observed Hnth; eapply memory_walk_prefix_position; exact Hnth)
    prefix _ Hprefix Hprefix_last Hprefix_terminal) as [trace [Htrace [Hlast Hterminal]]].
  destruct (memory_occurrence_input_valid g effects mg Hwf e i a Hocc)
    as [incoming [Hincoming [Hvalid _]]].
  rewrite Hbefore in Hincoming; inversion Hincoming; subst incoming.
  destruct (memory_clobbers_cover EN EE ET g effects mg q input fuel Hwf Hvalid trace _
    Htrace Hlast (or_introl Hterminal)) as [hit [Hhit Hroot]].
  exists input, origin, trace, hit; split; [exact Hprovenance|].
  split; [split; [exact Hbefore|split; assumption]|].
  split; [exact Htrace|split; [exact Hlast|split; assumption]].
Qed.
