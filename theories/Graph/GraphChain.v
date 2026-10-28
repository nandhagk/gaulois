(** * Forwarding-chain resolution

    A memoised functional walk resolves every node to its terminal node or to a cycle.
    For example, a forwarding self-loop is cyclic while a branch is a landing node.
    Builds on: GraphCore, GraphPrepare and Collections maps and sets. *)

From Stdlib Require Import List Bool PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
Import List.ListNotations.

(** A forwarding node moves only when its outgoing list contains exactly one edge. *)
Definition forward_step {V E} (g : Graph.t V E) (fwd : V -> bool) (v : V) : option E :=
  if fwd v then match Graph.out g v with [e] => Some e | _ => None end else None.

(** A finite chain follows all forwarding steps and stops only at a landing node. *)
Inductive chain {V E} (g : Graph.t V E) (fwd : V -> bool) : V -> list E -> V -> Prop :=
  | chain_stop : forall v, forward_step g fwd v = None -> chain g fwd v [] v
  | chain_move : forall v e es x, forward_step g fwd v = Some e ->
      chain g fwd (Graph.target g e) es x -> chain g fwd v (e :: es) x.

Arguments chain_stop {V E g fwd} v _.
Arguments chain_move {V E g fwd} v e es x _ _.

(** Resolution distinguishes a finite landing from a forwarding cycle. *)
Inductive resolution (V : Type) : Type :=
  | Landing (x : V)
  | Cyclic.

Arguments Landing {V}.
Arguments Cyclic {V}.

(** The executable walk reads the prepared adjacency index. *)
Definition chain_index_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (v : V) : option E :=
  if fwd v then match succ_edges p v with [e] => Some e | _ => None end else None.

Module ChainWork.

(** The trail is kept for a single memo-table update when the walk stops. *)
Record t (V : Type) : Type := Make {
  current : V;
  trail : list V;
  seen : FinSet.t V;
  answer : option (resolution V)
}.

Arguments Make {V}.
Arguments current {V}.
Arguments trail {V}.
Arguments seen {V}.
Arguments answer {V}.

End ChainWork.

(** A cached result or a repeated vertex stops the walk before taking another edge. *)
Definition chain_walk_step {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (cache : Map.t V (resolution V))
    (work : ChainWork.t V) : ChainWork.t V :=
  match ChainWork.answer work with
  | Some _ => work
  | None =>
    let v := ChainWork.current work in
    let finish := fun result =>
      ChainWork.Make v (ChainWork.trail work) (ChainWork.seen work) (Some result) in
    match Map.get EV v cache with
    | Some result => finish result
    | None =>
      if FinSet.mem EV v (ChainWork.seen work) then finish Cyclic
      else
        match chain_index_step p fwd v with
        | None => finish (Landing v)
        | Some e => ChainWork.Make (Graph.target g e) (v :: ChainWork.trail work)
            (FinSet.add EV v (ChainWork.seen work)) None
        end
    end
  end.

(** Binary fuel is short-circuited as soon as an answer is available. *)
Fixpoint chain_walk_run {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (cache : Map.t V (resolution V))
    (n : positive) (work : ChainWork.t V) : ChainWork.t V :=
  match ChainWork.answer work with
  | Some _ => work
  | None =>
    match n with
    | xH => chain_walk_step p fwd cache work
    | xO k => chain_walk_run p fwd cache k (chain_walk_run p fwd cache k work)
    | xI k => chain_walk_step p fwd cache
        (chain_walk_run p fwd cache k (chain_walk_run p fwd cache k work))
    end
  end.

(** Start one walk with an empty local guard, retaining the shared memo table. *)
Definition chain_walk {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (cache : Map.t V (resolution V)) (v : V) :=
  chain_walk_run p fwd cache (fuel p) (ChainWork.Make v [] FinSet.empty None).

(** The fallback makes arbitrary malformed prepared values total; ready walks always finish. *)
Definition chain_answer {V} (work : ChainWork.t V) : resolution V :=
  match ChainWork.answer work with
  | Some result => result
  | None => Cyclic
  end.

(** Resolve one node with the same guarded walker used by the all-node producer. *)
Definition resolve {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (v : V) : resolution V :=
  chain_answer (chain_walk p fwd Map.empty v).

(** Cache the common answer for the endpoint and every forwarding predecessor just walked. *)
Definition chain_memo_root {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) (cache : Map.t V (resolution V)) (v : V) :=
  match Map.get EV v cache with
  | Some _ => cache
  | None =>
    let work := chain_walk p fwd cache v in
    let result := chain_answer work in
    fold_left (fun m x => Map.set EV x result m)
      (ChainWork.current work :: ChainWork.trail work) cache
  end.

(** Reuse all results of each walk, so later roots never traverse an already resolved chain. *)
Definition resolve_all {V E} {EV : encoding V} {g : Graph.t V E}
    (p : prepared EV g) (fwd : V -> bool) : Map.t V (resolution V) :=
  fold_left (chain_memo_root p fwd) (Graph.nodes g) Map.empty.

(** A prefix may stop anywhere, but all of its edges are forwarding steps. *)
Inductive chain_prefix {V E} (g : Graph.t V E) (fwd : V -> bool) :
    V -> list E -> V -> Prop :=
  | chain_prefix_nil : forall v, chain_prefix g fwd v [] v
  | chain_prefix_cons : forall v e es x, forward_step g fwd v = Some e ->
      chain_prefix g fwd (Graph.target g e) es x -> chain_prefix g fwd v (e :: es) x.

Section Chains.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
  (fwd : V -> bool).

Lemma chain_unique v es x : chain g fwd v es x ->
  forall fs y, chain g fwd v fs y -> es = fs /\ x = y.
Proof.
  intro Hchain; induction Hchain as [v Hnone|v e es x Hstep Htail IH]; intros fs y Hother.
  - inversion Hother as [v' Hnone'|v' e' fs' y' Hstep' Htail']; subst.
    + auto.
    + congruence.
  - inversion Hother as [v' Hnone'|v' e' fs' y' Hstep' Htail']; subst.
    + congruence.
    + assert (Heq : e = e') by congruence; subst e'.
      destruct (IH _ _ Htail') as [-> ->]; auto.
Qed.

Lemma chain_prefix_append u es v : chain_prefix g fwd u es v ->
  forall fs x, chain_prefix g fwd v fs x -> chain_prefix g fwd u (es ++ fs) x.
Proof.
  intro Hprefix; induction Hprefix as [v|v e es x Hstep Htail IH]; intros fs y Hsuffix.
  - exact Hsuffix.
  - cbn; constructor; [exact Hstep|apply IH; exact Hsuffix].
Qed.

Lemma chain_prefix_complete u es v : chain_prefix g fwd u es v ->
  forall fs x, chain g fwd v fs x -> chain g fwd u (es ++ fs) x.
Proof.
  intro Hprefix; induction Hprefix as [v|v e es x Hstep Htail IH]; intros fs y Hsuffix.
  - exact Hsuffix.
  - cbn; constructor; [exact Hstep|apply IH; exact Hsuffix].
Qed.

Lemma chain_prefix_equiv u es v : chain_prefix g fwd u es v ->
  forall x, (exists fs, chain g fwd u fs x) <-> exists fs, chain g fwd v fs x.
Proof.
  intro Hprefix; induction Hprefix as [v|v e es y Hstep Htail IH]; intro x.
  - reflexivity.
  - rewrite <- IH; split.
    + intros [fs Hchain]; inversion Hchain as [v' Hnone|v' e' rest x' He Hrest]; subst;
        [congruence|].
      assert (Heq : e = e') by congruence; subst e'; exists rest; exact Hrest.
    + intros [fs Hchain]; exists (e :: fs); constructor; assumption.
Qed.

Lemma chain_prefix_cycle v es : chain_prefix g fwd v es v -> es <> [] ->
  forall fs x, ~ chain g fwd v fs x.
Proof.
  intros Hprefix Hne fs x Hchain.
  pose proof (chain_prefix_complete v es v Hprefix fs x Hchain) as Hlong.
  destruct (chain_unique v fs x Hchain (es ++ fs) x Hlong) as [Heq _].
  apply Hne, length_zero_iff_nil; apply (f_equal (@length E)) in Heq.
  rewrite length_app in Heq; lia.
Qed.

(** A semantic result records the exact finite-chain landings. *)
Definition chain_sem v (result : resolution V) : Prop :=
  forall x, result = Landing x <-> exists es, chain g fwd v es x.

(** Every memoised binding has the same meaning as a fresh walk. *)
Definition chain_cache_valid (cache : Map.t V (resolution V)) : Prop :=
  forall v result, Map.get EV v cache = Some result -> chain_sem v result.

Lemma chain_sem_unique v r r' : chain_sem v r -> chain_sem v r' -> r = r'.
Proof.
  intros Hr Hr'; destruct r as [x|], r' as [y|]; [| | |reflexivity].
  - destruct (proj1 (Hr x) eq_refl) as [es Hes].
    destruct (proj1 (Hr' y) eq_refl) as [fs Hfs].
    destruct (chain_unique v es x Hes fs y Hfs) as [_ ->]; reflexivity.
  - pose proof (proj2 (Hr' x) (proj1 (Hr x) eq_refl)) as Hfalse; discriminate.
  - pose proof (proj2 (Hr y) (proj1 (Hr' y) eq_refl)) as Hfalse; discriminate.
Qed.

Lemma chain_sem_prefix u es v result : chain_prefix g fwd u es v ->
  chain_sem v result -> chain_sem u result.
Proof.
  intros Hprefix Hsem x; rewrite (Hsem x); symmetry;
    apply chain_prefix_equiv with es; exact Hprefix.
Qed.

Lemma chain_sem_stop v : forward_step g fwd v = None -> chain_sem v (Landing v).
Proof.
  intros Hnone x; split.
  - intro Heq; inversion Heq; subst; exists []; constructor; exact Hnone.
  - intros [es Hchain].
    destruct (chain_unique v [] v (chain_stop v Hnone) es x Hchain) as [_ ->].
    reflexivity.
Qed.

Lemma chain_sem_cycle v : (forall es x, ~ chain g fwd v es x) -> chain_sem v Cyclic.
Proof.
  intros Hnone x; split; [discriminate|intros [es Hchain]; exfalso; exact (Hnone es x Hchain)].
Qed.

Lemma chain_index_agrees v : ready EV g p -> In v (Graph.nodes g) ->
  chain_index_step p fwd v = forward_step g fwd v.
Proof.
  intros [_ [_ Hp]] Hv; unfold chain_index_step, forward_step; rewrite (succ_agrees Hp v Hv).
  reflexivity.
Qed.

Lemma chain_forward_edge v e : forward_step g fwd v = Some e -> In e (Graph.out g v).
Proof.
  unfold forward_step; destruct (fwd v); [|discriminate].
  destruct (Graph.out g v) as [|a [|b rest]]; try discriminate.
  intro H; inversion H; subst; left; reflexivity.
Qed.

(** Each trail member has a nonempty forwarding prefix to the current endpoint. *)
Record chain_work_valid (root : V) (work : ChainWork.t V) : Prop := {
  chain_work_nodup : NoDup (ChainWork.trail work);
  chain_work_nodes : incl (ChainWork.trail work) (Graph.nodes g);
  chain_work_current : In (ChainWork.current work) (Graph.nodes g);
  chain_work_seen : forall x,
    FinSet.mem EV x (ChainWork.seen work) = true <-> In x (ChainWork.trail work);
  chain_work_prefixes : forall x, In x (ChainWork.trail work) ->
    exists es, es <> [] /\ chain_prefix g fwd x es (ChainWork.current work);
  chain_work_start : exists es, chain_prefix g fwd root es (ChainWork.current work);
  chain_work_root : root = ChainWork.current work \/ In root (ChainWork.trail work);
  chain_work_sem : forall result, ChainWork.answer work = Some result ->
    chain_sem (ChainWork.current work) result
}.

Lemma chain_work_initial v : In v (Graph.nodes g) ->
  chain_work_valid v (ChainWork.Make v [] FinSet.empty None).
Proof.
  intro Hv; constructor; cbn.
  - constructor.
  - intros x H; contradiction.
  - exact Hv.
  - intro x; rewrite FinSet.mem_empty; split; [discriminate|contradiction].
  - intros x H; contradiction.
  - exists []; constructor.
  - left; reflexivity.
  - intros result H; discriminate.
Qed.

Lemma chain_work_finish root v trail seen answer result :
  chain_work_valid root (ChainWork.Make v trail seen answer) -> chain_sem v result ->
  chain_work_valid root (ChainWork.Make v trail seen (Some result)).
Proof.
  intros Hvalid Hsem; destruct Hvalid; constructor; cbn in *; try assumption.
  intros r H; inversion H; subst r; exact Hsem.
Qed.

Lemma chain_work_advance root v trail seen e : ready EV g p ->
  chain_work_valid root (ChainWork.Make v trail seen None) ->
  FinSet.mem EV v seen = false -> forward_step g fwd v = Some e ->
  chain_work_valid root
    (ChainWork.Make (Graph.target g e) (v :: trail) (FinSet.add EV v seen) None).
Proof.
  intros Hready Hvalid Hfresh Hstep; pose proof Hready as [Hwf _].
  destruct Hvalid as [Hnd Hnodes Hv Hseen Hprefixes Hstart Hroot Hsem]; cbn in *.
  assert (Hedge : In e (Graph.out g v)) by (apply chain_forward_edge; exact Hstep).
  assert (Hsingle : chain_prefix g fwd v [e] (Graph.target g e)).
  { constructor; [exact Hstep|constructor]. }
  constructor; cbn.
  - constructor; [intro Hin; apply Hseen in Hin; congruence|exact Hnd].
  - intros x [->|Hin]; [exact Hv|apply Hnodes; exact Hin].
  - apply (out_target_in Hwf v e Hv Hedge).
  - intro x; rewrite FinSet.mem_add, Hseen; cbn; split;
      intros [Heq|Hin]; [left; symmetry; exact Heq|right; exact Hin|
        left; symmetry; exact Heq|right; exact Hin].
  - intros x [->|Hin].
    + exists [e]; split; [discriminate|exact Hsingle].
    + destruct (Hprefixes x Hin) as [es [Hne Hpre]].
      exists (es ++ [e]); split.
      * intro Heq; apply (f_equal (@length E)) in Heq; rewrite length_app in Heq; cbn in Heq; lia.
      * eapply chain_prefix_append; eassumption.
  - destruct Hstart as [es Hpre]; exists (es ++ [e]); eapply chain_prefix_append; eassumption.
  - right; destruct Hroot as [->|Hin]; [left; reflexivity|right; exact Hin].
  - intros result H; discriminate.
Qed.

Lemma chain_walk_step_valid root cache work : ready EV g p -> chain_cache_valid cache ->
  chain_work_valid root work -> chain_work_valid root (chain_walk_step p fwd cache work).
Proof.
  intros Hready Hcache Hvalid; destruct work as [v trail seen answer].
  destruct answer as [result|]; [exact Hvalid|].
  cbn [chain_walk_step ChainWork.answer ChainWork.current ChainWork.trail ChainWork.seen].
  destruct (Map.get EV v cache) as [result|] eqn:Hcache_v.
  - apply chain_work_finish with None; [exact Hvalid|apply Hcache; exact Hcache_v].
  - destruct (FinSet.mem EV v seen) eqn:Hseen.
    + apply chain_work_finish with None; [exact Hvalid|].
      apply chain_sem_cycle; apply (chain_work_seen _ _ Hvalid) in Hseen.
      destruct (chain_work_prefixes _ _ Hvalid v Hseen) as [es [Hne Hprefix]].
      apply chain_prefix_cycle with es; assumption.
    + destruct (chain_index_step p fwd v) as [e|] eqn:Hstep.
      * apply chain_work_advance; [exact Hready|exact Hvalid|exact Hseen|].
        rewrite <- chain_index_agrees;
          [exact Hstep|exact Hready|exact (chain_work_current _ _ Hvalid)].
      * apply chain_work_finish with None; [exact Hvalid|apply chain_sem_stop].
        rewrite <- chain_index_agrees;
          [exact Hstep|exact Hready|exact (chain_work_current _ _ Hvalid)].
Qed.

Lemma chain_walk_step_progress cache work :
  ChainWork.answer (chain_walk_step p fwd cache work) = None ->
  ChainWork.answer work = None /\
  length (ChainWork.trail (chain_walk_step p fwd cache work)) =
    S (length (ChainWork.trail work)).
Proof.
  destruct work as [v trail seen [result|]]; cbn [chain_walk_step ChainWork.answer];
    [discriminate|].
  cbn [ChainWork.current ChainWork.trail ChainWork.seen].
  destruct (Map.get EV v cache); [discriminate|].
  destruct (FinSet.mem EV v seen); [discriminate|].
  destruct (chain_index_step p fwd v); cbn; [auto|discriminate].
Qed.

Lemma chain_walk_iter_done cache work n : ChainWork.answer work <> None ->
  Pos.iter (chain_walk_step p fwd cache) work n = work.
Proof.
  intro Hdone; induction n using Pos.peano_ind.
  - change (chain_walk_step p fwd cache work = work).
    unfold chain_walk_step; destruct (ChainWork.answer work); [reflexivity|contradiction].
  - rewrite Pos.iter_succ, IHn; unfold chain_walk_step;
      destruct (ChainWork.answer work); [reflexivity|contradiction].
Qed.

Lemma chain_walk_run_agrees cache n work : chain_walk_run p fwd cache n work =
  Pos.iter (chain_walk_step p fwd cache) work n.
Proof.
  revert work; induction n as [n IH|n IH|]; intro work;
    destruct (ChainWork.answer work) as [result|] eqn:Hanswer.
  - cbn [chain_walk_run]; rewrite Hanswer; symmetry; apply chain_walk_iter_done; congruence.
  - cbn [chain_walk_run]; rewrite Hanswer, !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO n)).
  - cbn [chain_walk_run]; rewrite Hanswer; symmetry; apply chain_walk_iter_done; congruence.
  - cbn [chain_walk_run]; rewrite Hanswer, !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - cbn [chain_walk_run]; rewrite Hanswer; symmetry; apply chain_walk_iter_done; congruence.
  - cbn [chain_walk_run]; rewrite Hanswer; reflexivity.
Qed.

Lemma chain_walk_iter_valid root cache work n : ready EV g p -> chain_cache_valid cache ->
  chain_work_valid root work ->
  chain_work_valid root (Pos.iter (chain_walk_step p fwd cache) work n) /\
  (ChainWork.answer (Pos.iter (chain_walk_step p fwd cache) work n) = None ->
   length (ChainWork.trail (Pos.iter (chain_walk_step p fwd cache) work n)) =
     length (ChainWork.trail work) + Pos.to_nat n).
Proof.
  intros Hready Hcache Hvalid; induction n using Pos.peano_ind.
  - cbn [Pos.iter]; split.
    + apply chain_walk_step_valid; assumption.
    + intro Hnone; destruct (chain_walk_step_progress cache work Hnone) as [_ Hlength]; cbn; lia.
  - rewrite Pos.iter_succ; destruct IHn as [Hinv Hlength]; split.
    + apply chain_walk_step_valid; assumption.
    + intro Hnone.
      destruct (chain_walk_step_progress cache _ Hnone) as [Hactive Hstep].
      rewrite Hstep, (Hlength Hactive), Pos2Nat.inj_succ; lia.
Qed.

Lemma chain_walk_finished cache v : ready EV g p -> chain_cache_valid cache ->
  In v (Graph.nodes g) ->
  chain_work_valid v (chain_walk p fwd cache v) /\
  exists result, ChainWork.answer (chain_walk p fwd cache v) = Some result.
Proof.
  intros Hready Hcache Hv; pose proof Hready as [_ [_ Hp]].
  unfold chain_walk; rewrite chain_walk_run_agrees.
  destruct (chain_walk_iter_valid v cache _ (fuel p) Hready Hcache (chain_work_initial v Hv))
    as [Hvalid Hlength].
  split; [exact Hvalid|].
  destruct (ChainWork.answer (Pos.iter (chain_walk_step p fwd cache)
    (ChainWork.Make v [] FinSet.empty None) (fuel p))) as [result|] eqn:Hanswer;
    [exists result; reflexivity|].
  specialize (Hlength eq_refl).
  pose proof (NoDup_incl_length (chain_work_nodup _ _ Hvalid)
    (chain_work_nodes _ _ Hvalid)) as Hsize.
  cbn in Hlength; rewrite (fuel_value Hp) in Hlength; lia.
Qed.

Lemma chain_walk_sem cache v : ready EV g p -> chain_cache_valid cache ->
  In v (Graph.nodes g) ->
  chain_sem v (chain_answer (chain_walk p fwd cache v)) /\
  (forall x, In x (ChainWork.current (chain_walk p fwd cache v) ::
      ChainWork.trail (chain_walk p fwd cache v)) ->
    chain_sem x (chain_answer (chain_walk p fwd cache v))) /\
  In v (ChainWork.current (chain_walk p fwd cache v) ::
    ChainWork.trail (chain_walk p fwd cache v)).
Proof.
  intros Hready Hcache Hv.
  destruct (chain_walk_finished cache v Hready Hcache Hv) as [Hvalid [result Hanswer]].
  unfold chain_answer; rewrite Hanswer.
  pose proof (chain_work_sem _ _ Hvalid result Hanswer) as Hsem.
  split.
  - destruct (chain_work_start _ _ Hvalid) as [es Hprefix].
    eapply chain_sem_prefix; eassumption.
  - split.
    + intros x [Heq|Hin]; [subst x; exact Hsem|].
      destruct (chain_work_prefixes _ _ Hvalid x Hin) as [es [_ Hprefix]].
      eapply chain_sem_prefix; eassumption.
    + destruct (chain_work_root _ _ Hvalid) as [Heq|Hin];
        [left; symmetry; exact Heq|right; exact Hin].
Qed.

Lemma chain_cache_empty : chain_cache_valid (Map.empty : Map.t V (resolution V)).
Proof.
  intros v result H; rewrite Map.get_empty in H; discriminate.
Qed.

Lemma chain_cache_set cache v result : chain_cache_valid cache -> chain_sem v result ->
  chain_cache_valid (Map.set EV v result cache).
Proof.
  intros Hcache Hsem x r Hget; destruct (Pos.eq_dec (encode EV x) (encode EV v)) as [Heq|Hne].
  - apply (encode_injective EV) in Heq; subst x.
    rewrite Map.get_set_same in Hget; inversion Hget; subst r; exact Hsem.
  - rewrite Map.get_set_other in Hget.
    + apply Hcache; exact Hget.
    + intro Heq; subst x; contradiction.
Qed.

Lemma chain_fill_valid xs cache result : chain_cache_valid cache ->
  (forall x, In x xs -> chain_sem x result) ->
  chain_cache_valid (fold_left (fun m x => Map.set EV x result m) xs cache).
Proof.
  revert cache; induction xs as [|v xs IH]; intros cache Hcache Hsem; cbn [fold_left].
  - exact Hcache.
  - apply IH.
    + apply chain_cache_set; [exact Hcache|apply Hsem; left; reflexivity].
    + intros x Hx; apply Hsem; right; exact Hx.
Qed.

Lemma chain_fill_present xs cache (result : resolution V) x :
  (exists r, Map.get EV x cache = Some r) \/ In x xs ->
  exists r, Map.get EV x (fold_left (fun m v => Map.set EV v result m) xs cache) = Some r.
Proof.
  revert cache; induction xs as [|v xs IH]; intros cache Hin; cbn [fold_left].
  - destruct Hin as [H|H]; [exact H|contradiction].
  - apply IH; destruct (Pos.eq_dec (encode EV x) (encode EV v)) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x.
      left; exists result; apply Map.get_set_same.
    + destruct Hin as [[r Hr]|[Heq|Hin]].
      * left; exists r; rewrite Map.get_set_other; [exact Hr|intro Heq; subst; contradiction].
      * subst x; contradiction.
      * right; exact Hin.
Qed.

Lemma chain_memo_root_valid cache v : ready EV g p -> chain_cache_valid cache ->
  In v (Graph.nodes g) ->
  chain_cache_valid (chain_memo_root p fwd cache v) /\
  (forall x, (exists r, Map.get EV x cache = Some r) \/ x = v ->
    exists r, Map.get EV x (chain_memo_root p fwd cache v) = Some r).
Proof.
  intros Hready Hcache Hv; unfold chain_memo_root.
  destruct (Map.get EV v cache) as [result|] eqn:Hget.
  - split; [exact Hcache|].
    intros x [[r Hr]|Heq]; [exists r; exact Hr|subst x; exists result; exact Hget].
  - destruct (chain_walk_sem cache v Hready Hcache Hv) as [_ [Hall Hmember]].
    split; [apply chain_fill_valid; assumption|].
    intros x [Hpresent|Heq]; apply chain_fill_present; [left; exact Hpresent|].
    right; subst x; exact Hmember.
Qed.

Lemma chain_memo_fold_valid roots cache : ready EV g p -> chain_cache_valid cache ->
  incl roots (Graph.nodes g) ->
  chain_cache_valid (fold_left (chain_memo_root p fwd) roots cache) /\
  (forall x, (exists r, Map.get EV x cache = Some r) \/ In x roots ->
    exists r, Map.get EV x (fold_left (chain_memo_root p fwd) roots cache) = Some r).
Proof.
  revert cache; induction roots as [|v roots IH]; intros cache Hready Hcache Hnodes.
  - cbn; split; [exact Hcache|intros x [H|H]; [exact H|contradiction]].
  - cbn [fold_left].
    destruct (chain_memo_root_valid cache v Hready Hcache (Hnodes v (or_introl eq_refl)))
      as [Hvalid Hpresent].
    destruct (IH _ Hready Hvalid ltac:(intros x Hx; apply Hnodes; right; exact Hx))
      as [Hfinal Hfinal_present].
    split; [exact Hfinal|].
    intros x [Hinitial|[Heq|Hin]]; apply Hfinal_present.
    + left; apply Hpresent; left; exact Hinitial.
    + left; apply Hpresent; right; symmetry; exact Heq.
    + right; exact Hin.
Qed.

Lemma resolve_sem v : ready EV g p -> In v (Graph.nodes g) -> chain_sem v (resolve p fwd v).
Proof.
  intros Hready Hv; apply (proj1 (chain_walk_sem Map.empty v Hready chain_cache_empty Hv)).
Qed.

End Chains.

Section ChainContract.
Context {V E : Type} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g).
Variables (v : V) (fwd : V -> bool).

(** Resolution recognizes precisely the finite forwarding landings and memoises every node. *)
Theorem resolve_correct : ready EV g p -> In v (Graph.nodes g) ->
  (forall x, resolve p fwd v = Landing x <-> exists es, chain g fwd v es x) /\
  (resolve p fwd v = Cyclic <-> forall es x, ~ chain g fwd v es x) /\
  Map.get EV v (resolve_all p fwd) = Some (resolve p fwd v).
Proof.
  intros Hready Hv; pose proof (resolve_sem EV g p fwd v Hready Hv) as Hsem.
  split; [exact Hsem|]; split.
  - split.
    + intros Hcyclic es x Hchain.
      pose proof (proj2 (Hsem x) (ex_intro _ es Hchain)) as Hlanding; congruence.
    + intro Hnone; destruct (resolve p fwd v) as [x|] eqn:Hresolve; [|reflexivity].
      destruct (proj1 (Hsem x) eq_refl) as [es Hchain]; exfalso; exact (Hnone es x Hchain).
  - destruct (chain_memo_fold_valid EV g p fwd (Graph.nodes g) Map.empty Hready
      (chain_cache_empty EV g fwd)
      ltac:(intros x Hx; exact Hx)) as [Hvalid Hpresent].
    destruct (Hpresent v (or_intror Hv)) as [result Hresult].
    unfold resolve_all; rewrite Hresult; f_equal.
    apply (chain_sem_unique g fwd v); [apply Hvalid; exact Hresult|exact Hsem].
Qed.

End ChainContract.
