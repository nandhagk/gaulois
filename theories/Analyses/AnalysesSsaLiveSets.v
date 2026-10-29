(** * Sparse materialized point liveness

    A seeded backward worklist inserts each point/value pair before scheduling it.
    For example, an edge that both reads and defines a value still seeds its source.
    Builds on: GraphPrepare, ViewsSsaPoints, AnalysesLiveness, AnalysesRules and
    AnalysesSsaLiveQuery. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare.
From Gaulois.Fixpoint Require Import FixpointLeast.
From Gaulois.Views Require Import ViewsGraph ViewsSsaPoints.
From Gaulois.Rules Require Import RulesModel RulesSolve.
From Gaulois.Analyses Require Import AnalysesLiveness AnalysesRules AnalysesSsaLiveQuery.
Import List.ListNotations.

(** Absent point rows represent the empty live set. *)
Definition sparse_live_at {N V} (EN : encoding N) (EV : encoding V)
    (m : Map.t N (FinSet.t V)) (n : N) (x : V) : bool :=
  FinSet.mem EV x (live_index_get EN n m).

(** * Insert before scheduling *)

Local Definition sl_state N V := (Map.t N (FinSet.t V) * list (N * V))%type.

Local Definition sl_has {N V} (EN : encoding N) (EV : encoding V)
    (st : sl_state N V) (q : N * V) := sparse_live_at EN EV (fst st) (fst q) (snd q).

Local Definition sl_add {N V} (EN : encoding N) (EV : encoding V)
    (st : sl_state N V) (q : N * V) : sl_state N V :=
  if sl_has EN EV st q then st else
    (Map.set EN (fst q) (FinSet.add EV (snd q) (live_index_get EN (fst q) (fst st)))
      (fst st), q :: snd st).

Local Definition sl_adds {N V} (EN : encoding N) (EV : encoding V)
    (qs : list (N * V)) (st : sl_state N V) := fold_left (sl_add EN EV) qs st.

Local Lemma sl_set_has {N V} (EN : encoding N) (EV : encoding V)
    (m : Map.t N (FinSet.t V)) (a q : N * V) :
  sparse_live_at EN EV
    (Map.set EN (fst a) (FinSet.add EV (snd a) (live_index_get EN (fst a) m)) m)
    (fst q) (snd q) = true <->
  q = a \/ sparse_live_at EN EV m (fst q) (snd q) = true.
Proof.
  destruct a as [n x], q as [k y]; cbn.
  destruct (Pos.eq_dec (encode EN k) (encode EN n)) as [Hsame|Hother].
  - apply (encode_injective EN) in Hsame; subst k.
    unfold sparse_live_at, live_index_get; rewrite Map.get_set_same, FinSet.mem_add.
    split.
    + intros [Heq|Hmem]; [left; subst y; reflexivity|right; exact Hmem].
    + intros [Heq|Hmem]; [injection Heq as Heq; left; exact Heq|right; exact Hmem].
  - assert (Hne : k <> n) by (intro Heq; subst k; contradiction).
    unfold sparse_live_at, live_index_get; rewrite Map.get_set_other by exact Hne.
    split; [auto|intros [Heq|Hmem]; [injection Heq as Heq; contradiction|exact Hmem]].
Qed.

Local Lemma sl_add_has {N V} (EN : encoding N) (EV : encoding V)
    (st : sl_state N V) a q :
  sl_has EN EV (sl_add EN EV st a) q = true <-> q = a \/ sl_has EN EV st q = true.
Proof.
  unfold sl_add; destruct (sl_has EN EV st a) eqn:Hseen.
  - split; [auto|intros [->|Hmem]; assumption].
  - apply sl_set_has.
Qed.

Local Lemma sl_adds_has {N V} (EN : encoding N) (EV : encoding V) qs st q :
  sl_has EN EV (sl_adds EN EV qs st) q = true <->
  In q qs \/ sl_has EN EV st q = true.
Proof.
  revert st; induction qs as [|a qs IH]; intro st.
  - cbn; tauto.
  - change (sl_has EN EV (sl_adds EN EV qs (sl_add EN EV st a)) q = true <->
      In q (a :: qs) \/ sl_has EN EV st q = true).
    rewrite IH, sl_add_has; cbn; intuition congruence.
Qed.

Local Lemma sl_adds_pending {N V} (EN : encoding N) (EV : encoding V) qs st q :
  In q (snd st) -> In q (snd (sl_adds EN EV qs st)).
Proof.
  revert st; induction qs as [|a qs IH]; intros st Hpending; cbn [sl_adds fold_left].
  - exact Hpending.
  - apply IH; unfold sl_add; destruct (sl_has EN EV st a); cbn; auto.
Qed.

Local Lemma sl_adds_fresh {N V} (EN : encoding N) (EV : encoding V) qs st q :
  sl_has EN EV (sl_adds EN EV qs st) q = true ->
  sl_has EN EV st q = true \/ In q (snd (sl_adds EN EV qs st)).
Proof.
  revert st; induction qs as [|a qs IH]; intros st Hmem.
  - left; exact Hmem.
  - cbn [sl_adds fold_left] in *; apply IH in Hmem.
    destruct Hmem as [Hmem|Hpending]; [|auto].
    unfold sl_add in Hmem; destruct (sl_has EN EV st a) eqn:Hseen; [auto|].
    apply sl_set_has in Hmem; destruct Hmem as [->|Hmem]; [|auto].
    right; apply sl_adds_pending; unfold sl_add; rewrite Hseen; cbn; auto.
Qed.

Local Definition sl_pending {N V} (EN : encoding N) (EV : encoding V)
    (st : sl_state N V) :=
  NoDup (snd st) /\ forall q, In q (snd st) -> sl_has EN EV st q = true.

Local Lemma sl_add_pending {N V} (EN : encoding N) (EV : encoding V) st a :
  sl_pending EN EV st -> sl_pending EN EV (sl_add EN EV st a).
Proof.
  intros [Hnodup Hseen]; unfold sl_add; destruct (sl_has EN EV st a) eqn:Hmem.
  - split; assumption.
  - split; cbn.
    + constructor; [intro Hin; apply Hseen in Hin; congruence|exact Hnodup].
    + intros q [->|Hin]; apply sl_set_has; [auto|right; apply Hseen; exact Hin].
Qed.

Local Lemma sl_adds_pending_seen {N V} (EN : encoding N) (EV : encoding V) qs st :
  sl_pending EN EV st -> sl_pending EN EV (sl_adds EN EV qs st).
Proof.
  revert st; induction qs as [|a qs IH]; intros st Hpending; cbn [sl_adds fold_left].
  - exact Hpending.
  - apply IH, sl_add_pending; exact Hpending.
Qed.

Local Lemma sl_adds_safe {N V} (EN : encoding N) (EV : encoding V)
    (P : N * V -> Prop) qs st :
  (forall q, In q qs -> P q) -> (forall q, sl_has EN EV st q = true -> P q) ->
  forall q, sl_has EN EV (sl_adds EN EV qs st) q = true -> P q.
Proof.
  intros Hnew Hold q Hmem; apply sl_adds_has in Hmem.
  destruct Hmem; [apply Hnew|apply Hold]; assumption.
Qed.

(** * Finite sparse saturation *)

Local Definition sl_step {N V} (EN : encoding N) (EV : encoding V)
    (next : N * V -> list (N * V)) (st : sl_state N V) :=
  match snd st with
  | [] => st
  | q :: rest => sl_adds EN EV (next q) (fst st, rest)
  end.

(* Binary blocks stop as soon as the worklist is empty; fuel counts processed pairs. *)
Local Fixpoint sl_run {N V} (EN : encoding N) (EV : encoding V)
    (next : N * V -> list (N * V)) (fuel : positive) (st : sl_state N V) :=
  match snd st with
  | [] => st
  | _ :: _ =>
    match fuel with
    | xH => sl_step EN EV next st
    | xO k => sl_run EN EV next k (sl_run EN EV next k st)
    | xI k => sl_step EN EV next (sl_run EN EV next k (sl_run EN EV next k st))
    end
  end.

Local Lemma sl_iter_empty {N V} (EN : encoding N) (EV : encoding V) next m fuel :
  Pos.iter (sl_step EN EV next) (m, []) fuel = (m, []).
Proof.
  induction fuel using Pos.peano_ind.
  - reflexivity.
  - rewrite Pos.iter_succ, IHfuel; reflexivity.
Qed.

Local Lemma sl_run_agrees {N V} (EN : encoding N) (EV : encoding V) next fuel st :
  sl_run EN EV next fuel st = Pos.iter (sl_step EN EV next) st fuel.
Proof.
  revert st; induction fuel as [k IH|k IH|]; intros [m work]; destruct work as [|a rest].
  - symmetry; apply sl_iter_empty.
  - cbn [sl_run snd]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO k)).
  - symmetry; apply sl_iter_empty.
  - cbn [sl_run snd]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* A seen pair is either pending or all of its immediate consequences are already seen. *)
Local Definition sl_frontier {N V} (EN : encoding N) (EV : encoding V)
    (next : N * V -> list (N * V)) (st : sl_state N V) :=
  forall q, sl_has EN EV st q = true ->
    In q (snd st) \/ forall r, In r (next q) -> sl_has EN EV st r = true.

Local Lemma sl_step_frontier {N V} (EN : encoding N) (EV : encoding V) next st :
  sl_frontier EN EV next st -> sl_frontier EN EV next (sl_step EN EV next st).
Proof.
  destruct st as [m [|a rest]]; intro Hfront; [exact Hfront|].
  intros q Hmem; cbn [sl_step snd fst] in *.
  destruct (sl_adds_fresh EN EV (next a) (m, rest) q Hmem) as [Hold|Hpending];
    [|auto].
  destruct (Hfront q Hold) as [[Heq|Hpending]|Hclosed].
  - subst q; right; intros r Hin; apply sl_adds_has; auto.
  - left; apply sl_adds_pending; exact Hpending.
  - right; intros r Hin; apply sl_adds_has; right; apply Hclosed; exact Hin.
Qed.

Local Definition sl_measure {N V} (EN : encoding N) (EV : encoding V)
    (universe : list (N * V)) (st : sl_state N V) :=
  length (filter (fun q => negb (sl_has EN EV st q)) universe) + length (snd st).

Local Lemma sl_filter_le {A} (f g : A -> bool) xs :
  (forall a, f a = true -> g a = true) -> length (filter f xs) <= length (filter g xs).
Proof.
  intro Hincl; induction xs as [|a xs IH]; cbn; [lia|].
  specialize (Hincl a); destruct (f a), (g a); cbn in *; try lia; discriminate.
Qed.

Local Lemma sl_filter_lt {A} (f g : A -> bool) xs a :
  (forall b, f b = true -> g b = true) -> In a xs -> f a = false -> g a = true ->
  length (filter f xs) < length (filter g xs).
Proof.
  intros Hincl Hin Hf Hg; apply in_split in Hin; destruct Hin as [before [after ->]].
  rewrite !filter_app, !length_app; cbn; rewrite Hf, Hg; cbn.
  pose proof (sl_filter_le f g before Hincl) as Hbefore.
  pose proof (sl_filter_le f g after Hincl) as Hafter; lia.
Qed.

Local Lemma sl_add_measure {N V} (EN : encoding N) (EV : encoding V) universe st a :
  In a universe -> sl_measure EN EV universe (sl_add EN EV st a) <=
    sl_measure EN EV universe st.
Proof.
  intro Hin; unfold sl_add; destruct (sl_has EN EV st a) eqn:Hseen; [lia|].
  unfold sl_measure; cbn [snd].
  assert (Hincl : forall q,
    negb (sl_has EN EV
      (Map.set EN (fst a) (FinSet.add EV (snd a) (live_index_get EN (fst a) (fst st)))
        (fst st), a :: snd st) q) = true -> negb (sl_has EN EV st q) = true).
  { intros q Hnew; apply negb_true_iff; apply negb_true_iff in Hnew.
    destruct (sl_has EN EV st q) eqn:Hold; [|reflexivity].
    assert (Hpresent : sl_has EN EV
      (Map.set EN (fst a) (FinSet.add EV (snd a) (live_index_get EN (fst a) (fst st)))
        (fst st), a :: snd st) q = true) by (apply sl_set_has; auto).
    congruence. }
  assert (Hgone : sl_has EN EV
    (Map.set EN (fst a) (FinSet.add EV (snd a) (live_index_get EN (fst a) (fst st)))
      (fst st), a :: snd st) a = true).
  { apply sl_set_has; auto. }
  assert (Hgone' : negb (sl_has EN EV
    (Map.set EN (fst a) (FinSet.add EV (snd a) (live_index_get EN (fst a) (fst st)))
      (fst st), a :: snd st) a) = false) by (rewrite Hgone; reflexivity).
  assert (Hfresh : negb (sl_has EN EV st a) = true) by (rewrite Hseen; reflexivity).
  pose proof (sl_filter_lt _ _ universe a Hincl Hin Hgone' Hfresh) as Hremoved.
  cbn [sl_has fst snd length] in *; lia.
Qed.

Local Lemma sl_adds_measure {N V} (EN : encoding N) (EV : encoding V) universe qs st :
  incl qs universe -> sl_measure EN EV universe (sl_adds EN EV qs st) <=
    sl_measure EN EV universe st.
Proof.
  revert st; induction qs as [|a qs IH]; intros st Hincl; [apply Nat.le_refl|].
  change (sl_measure EN EV universe (sl_adds EN EV qs (sl_add EN EV st a)) <=
    sl_measure EN EV universe st).
  pose proof (sl_add_measure EN EV universe st a (Hincl a (or_introl eq_refl))) as Hadd.
  specialize (IH (sl_add EN EV st a) ltac:(intros q Hq; apply Hincl; right; exact Hq)); lia.
Qed.

Local Lemma sl_step_decreases {N V} (EN : encoding N) (EV : encoding V) universe next st :
  (forall q, sl_has EN EV st q = true -> In q universe) ->
  sl_pending EN EV st ->
  (forall q, In q universe -> incl (next q) universe) -> snd st <> [] ->
  sl_measure EN EV universe (sl_step EN EV next st) < sl_measure EN EV universe st.
Proof.
  destruct st as [m [|a rest]]; intros Hsupport [_ Hseen] Hnext Hnonempty; [contradiction|].
  assert (Ha : In a universe) by (apply Hsupport, Hseen; cbn; auto).
  pose proof (sl_adds_measure EN EV universe (next a) (m, rest) (Hnext a Ha)) as Hadd.
  cbn [sl_step snd fst] in *; unfold sl_measure, sl_has in *.
  cbn [fst snd length] in *; lia.
Qed.

(* The finite universe and safety predicate are proof parameters, never loop inputs. *)
Local Definition sl_invariant {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds (safe : N * V -> Prop) (st : sl_state N V) :=
  (forall q, sl_has EN EV st q = true -> In q universe) /\
  sl_pending EN EV st /\
  (forall q, sl_has EN EV st q = true -> safe q) /\
  (forall q, In q seeds -> sl_has EN EV st q = true) /\
  sl_frontier EN EV next st.

Local Lemma sl_initial_invariant {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds safe :
  incl seeds universe -> (forall q, In q seeds -> safe q) ->
  sl_invariant EN EV universe next seeds safe (sl_adds EN EV seeds (Map.empty, [])).
Proof.
  intros Hsupport Hsafe.
  assert (Hempty : forall q, sl_has EN EV (Map.empty, []) q = false).
  { intros [n x]; unfold sl_has, sparse_live_at, live_index_get; cbn.
    rewrite Map.get_empty; apply FinSet.mem_empty. }
  split.
  - intros q Hmem; apply sl_adds_has in Hmem; destruct Hmem as [Hseed|Hbad]; [auto|].
    rewrite Hempty in Hbad; discriminate.
  - split.
    + apply sl_adds_pending_seen; split; [constructor|intros q Hbad; contradiction].
    + split.
      * intros q Hmem; apply sl_adds_has in Hmem; destruct Hmem as [Hseed|Hbad]; [auto|].
        rewrite Hempty in Hbad; discriminate.
      * split.
        -- intros q Hin; apply sl_adds_has; auto.
        -- intros q Hmem; apply sl_adds_fresh in Hmem; destruct Hmem as [Hbad|Hpending]; [|auto].
           rewrite Hempty in Hbad; discriminate.
Qed.

Local Lemma sl_step_invariant {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds safe st :
  (forall q, In q universe -> incl (next q) universe) ->
  (forall q, safe q -> forall r, In r (next q) -> safe r) ->
  sl_invariant EN EV universe next seeds safe st ->
  sl_invariant EN EV universe next seeds safe (sl_step EN EV next st).
Proof.
  intros Hnext Hsafe Hinv; destruct st as [m [|a rest]]; [exact Hinv|].
  destruct Hinv as [Hsupport [[Hnodup Hseen] [Hsound [Hseeds Hfront]]]].
  assert (Ha : sl_has EN EV (m, a :: rest) a = true) by (apply Hseen; cbn; auto).
  assert (Htail : sl_pending EN EV (m, rest)).
  { split; [inversion Hnodup; assumption|intros q Hin; apply Hseen; cbn; auto]. }
  cbn [sl_step snd fst]; split.
  - apply sl_adds_safe; [apply Hnext, Hsupport; exact Ha|exact Hsupport].
  - split; [apply sl_adds_pending_seen; exact Htail|].
    split.
    + apply sl_adds_safe; [apply Hsafe, Hsound; exact Ha|exact Hsound].
    + split.
      * intros q Hin; apply sl_adds_has; right; apply Hseeds; exact Hin.
      * apply (sl_step_frontier EN EV next (m, a :: rest) Hfront).
Qed.

Local Lemma sl_iter_invariant {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds safe st fuel :
  (forall q, In q universe -> incl (next q) universe) ->
  (forall q, safe q -> forall r, In r (next q) -> safe r) ->
  sl_invariant EN EV universe next seeds safe st ->
  sl_invariant EN EV universe next seeds safe (Pos.iter (sl_step EN EV next) st fuel).
Proof.
  intros Hnext Hsafe Hinv.
  induction fuel using Pos.peano_ind.
  - apply sl_step_invariant; assumption.
  - rewrite Pos.iter_succ; apply sl_step_invariant; assumption.
Qed.

Local Lemma sl_iter_bound {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds safe st fuel :
  (forall q, In q universe -> incl (next q) universe) ->
  (forall q, safe q -> forall r, In r (next q) -> safe r) ->
  sl_invariant EN EV universe next seeds safe st ->
  snd (Pos.iter (sl_step EN EV next) st fuel) = [] \/
    sl_measure EN EV universe (Pos.iter (sl_step EN EV next) st fuel) +
      Pos.to_nat fuel <= sl_measure EN EV universe st.
Proof.
  intros Hnext Hsafe Hinv; induction fuel using Pos.peano_ind.
  - destruct (snd st) as [|a rest] eqn:Hwork.
    + left; change (snd (sl_step EN EV next st) = []); unfold sl_step; rewrite Hwork.
      exact Hwork.
    + right; cbn [Pos.iter Pos.to_nat].
      pose proof (sl_step_decreases EN EV universe next st (proj1 Hinv)
        (proj1 (proj2 Hinv)) Hnext ltac:(rewrite Hwork; discriminate)) as Hdecrease; lia.
  - rewrite Pos.iter_succ.
    destruct IHfuel as [Hempty|Hbound].
    + left; unfold sl_step at 1; rewrite Hempty; exact Hempty.
    + destruct (snd (Pos.iter (sl_step EN EV next) st fuel)) as [|a rest] eqn:Hwork.
      * left; unfold sl_step at 1; rewrite Hwork; exact Hwork.
      * right.
        pose proof (sl_iter_invariant EN EV universe next seeds safe st fuel
          Hnext Hsafe Hinv) as Hi.
        pose proof (sl_step_decreases EN EV universe next _ (proj1 Hi)
          (proj1 (proj2 Hi)) Hnext ltac:(rewrite Hwork; discriminate)) as Hdecrease.
        rewrite Pos2Nat.inj_succ; lia.
Qed.

Local Lemma sl_run_complete {N V} (EN : encoding N) (EV : encoding V)
    universe next seeds safe fuel :
  incl seeds universe -> (forall q, In q seeds -> safe q) ->
  (forall q, In q universe -> incl (next q) universe) ->
  (forall q, safe q -> forall r, In r (next q) -> safe r) ->
  length universe < Pos.to_nat fuel ->
  let result := sl_run EN EV next fuel (sl_adds EN EV seeds (Map.empty, [])) in
  snd result = [] /\ sl_invariant EN EV universe next seeds safe result.
Proof.
  intros Hsupport Hseeds Hnext Hsafe Hfuel; cbn zeta; rewrite sl_run_agrees.
  pose proof (sl_initial_invariant EN EV universe next seeds safe Hsupport Hseeds) as Hi.
  split; [|apply sl_iter_invariant; assumption].
  destruct (sl_iter_bound EN EV universe next seeds safe _ fuel Hnext Hsafe Hi)
    as [Hempty|Hbound]; [exact Hempty|].
  pose proof (sl_adds_measure EN EV universe seeds (Map.empty, []) Hsupport) as Hinitial.
  assert (Hmeasure : sl_measure EN EV universe (Map.empty, []) = length universe).
  { unfold sl_measure; cbn [snd]; rewrite Nat.add_0_r.
    replace (filter (fun q => negb (sl_has EN EV (Map.empty, []) q)) universe)
      with universe; [reflexivity|].
    assert (Htrue : forall q, negb (sl_has EN EV (Map.empty, []) q) = true).
    { intros [n x]; unfold sl_has, sparse_live_at, live_index_get; cbn.
      rewrite Map.get_empty, FinSet.mem_empty; reflexivity. }
    clear Hinitial Hbound Hi Hsupport Hseeds Hnext Hsafe Hfuel.
    induction universe as [|q qs IH]; cbn [filter]; [reflexivity|].
    rewrite Htrue, <- IH; reflexivity. }
  rewrite Hmeasure in Hinitial; lia.
Qed.

(** * Prepared uses and definition membership *)

Local Definition sl_seeds {N E V} (p : point_uses N E V) : list (N * V) :=
  flat_map (fun n => map (fun x => (n, x))
    (exit_use p n ++ flat_map (edge_use p) (Graph.out (live_graph p) n)))
    (Graph.nodes (live_graph p)).

Local Definition sl_def_index {N E V} (EE : encoding E) (EV : encoding V)
    (p : point_uses N E V) :=
  fold_right (fun e m => Map.set EE e (FinSet.of_list EV (edge_def p e)) m)
    Map.empty (edges_of (live_graph p)).

Local Definition sl_back {N E V} (EV : encoding V) (EE : encoding E)
    (p : point_uses N E V) {EN : encoding N} (prepared : prepared EN (live_graph p))
    (defs : Map.t E (FinSet.t V)) (q : N * V) : list (N * V) :=
  map (fun e => (Graph.source (live_graph p) e, snd q))
    (filter (fun e => negb (FinSet.mem EV (snd q) (live_index_get EE e defs)))
      (pred_edges prepared (fst q))).

(* Multiply the separately converted counts in binary, without a unary product allocation. *)
Local Definition sl_budget {N E V} (p : point_uses N E V) : positive :=
  Pos.mul (Pos.of_succ_nat (length (Graph.nodes (live_graph p))))
    (Pos.of_succ_nat (length (sl_seeds p))).

(** Preparation and definition sets are shared by every sparse worklist step. *)
Definition sparse_live_materialize {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) : Map.t N (FinSet.t V) :=
  let prepared := prepare EN (live_graph p) in
  let defs := sl_def_index EE EV p in
  let seeds := sl_seeds p in
  let initial := sl_adds EN EV seeds (Map.empty, []) in
  fst (sl_run EN EV (sl_back EV EE p prepared defs)
    (Pos.mul (Pos.of_succ_nat (length (Graph.nodes (live_graph p))))
      (Pos.of_succ_nat (length seeds))) initial).

Local Lemma sl_seeds_agree {N E V} (p : point_uses N E V) n x :
  In (n, x) (sl_seeds p) <->
  In n (Graph.nodes (live_graph p)) /\ point_use_at p n x.
Proof.
  unfold sl_seeds; rewrite in_flat_map; split.
  - intros [k [Hnode Hin]]; apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hin]]; injection Heq as <- <-; split; [exact Hnode|].
    apply in_app_iff in Hin; destruct Hin as [Hexit|Hedge]; [left; exact Hexit|].
    right; apply in_flat_map in Hedge; exact Hedge.
  - intros [Hnode Huse]; exists n; split; [exact Hnode|].
    apply in_map_iff; exists x; split; [reflexivity|].
    apply in_app_iff; destruct Huse as [Hexit|Hedge]; [auto|].
    right; apply in_flat_map; exact Hedge.
Qed.

Local Lemma sl_def_get {N E V} (EE : encoding E) (EV : encoding V)
    (p : point_uses N E V) es e : In e es ->
  Map.get EE e (fold_right (fun a m => Map.set EE a (FinSet.of_list EV (edge_def p a)) m)
    Map.empty es) = Some (FinSet.of_list EV (edge_def p e)).
Proof.
  induction es as [|a es IH]; cbn; [contradiction|].
  intros [->|Hin]; [apply Map.get_set_same|].
  destruct (Pos.eq_dec (encode EE e) (encode EE a)) as [Heq|Hne].
  - apply (encode_injective EE) in Heq; subst a; apply Map.get_set_same.
  - rewrite Map.get_set_other; [apply IH; exact Hin|].
    intro Heq; subst a; contradiction.
Qed.

Local Lemma sl_defs_agree {N E V} (EE : encoding E) (EV : encoding V)
    (p : point_uses N E V) e x : In e (edges_of (live_graph p)) ->
  (FinSet.mem EV x (live_index_get EE e (sl_def_index EE EV p)) = true <->
    In x (edge_def p e)).
Proof.
  intro Hedge; unfold live_index_get, sl_def_index.
  rewrite (sl_def_get EE EV p _ e Hedge); apply FinSet.of_list_spec.
Qed.

Local Lemma sl_edge_listed {N E} (g : Graph.t N E) n e :
  In n (Graph.nodes g) -> In e (Graph.out g n) -> In e (edges_of g).
Proof.
  intros Hn He; unfold edges_of; apply in_flat_map; exists n; auto.
Qed.

Local Lemma sl_back_agrees {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) n x k y :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  In n (Graph.nodes (live_graph p)) ->
  (In (k, y) (sl_back EV EE p (prepare EN (live_graph p)) (sl_def_index EE EV p) (n, x)) <->
    y = x /\ In k (Graph.nodes (live_graph p)) /\
    exists e, In e (Graph.out (live_graph p) k) /\
      Graph.target (live_graph p) e = n /\ ~ In x (edge_def p e)).
Proof.
  intros [Hwf [_ Hprepared]] Hnode; unfold sl_back; cbn [fst snd]; rewrite in_map_iff.
  split.
  - intros [e [Heq Hin]]; injection Heq as <- <-.
    apply filter_In in Hin; destruct Hin as [Hpred Hkill].
    apply (pred_agrees Hprepared n e Hnode) in Hpred.
    destruct Hpred as [k [Hk [Hedge Htarget]]].
    pose proof (out_source Hwf k e Hedge) as Hsource; rewrite Hsource.
    split; [reflexivity|split; [exact Hk|exists e; split; [exact Hedge|]]].
    split; [exact Htarget|]; intro Hdef.
    apply negb_true_iff in Hkill.
    assert (Hmem : FinSet.mem EV x (live_index_get EE e (sl_def_index EE EV p)) = true).
    { apply sl_defs_agree; [eapply sl_edge_listed; eassumption|exact Hdef]. }
    congruence.
  - intros [-> [Hk [e [Hedge [Htarget Hkill]]]]]; exists e.
    split; [rewrite (out_source Hwf k e Hedge); reflexivity|].
    apply filter_In; split.
    + apply (pred_agrees Hprepared n e Hnode); exists k; auto.
    + apply negb_true_iff; destruct (FinSet.mem EV x
        (live_index_get EE e (sl_def_index EE EV p))) eqn:Hmem; [|reflexivity].
      exfalso; apply Hkill; apply sl_defs_agree in Hmem; [exact Hmem|].
      eapply sl_edge_listed; eassumption.
Qed.

(* This cross-product is used only by proofs; the executable fuel computes its length. *)
Local Definition sl_universe {N E V} (p : point_uses N E V) : list (N * V) :=
  flat_map (fun n => map (fun q => (n, snd q)) (sl_seeds p)) (Graph.nodes (live_graph p)).

Local Lemma sl_universe_agrees {N E V} (p : point_uses N E V) n x :
  In (n, x) (sl_universe p) <->
  In n (Graph.nodes (live_graph p)) /\ exists k, In (k, x) (sl_seeds p).
Proof.
  unfold sl_universe; rewrite in_flat_map; split.
  - intros [k [Hnode Hin]]; apply in_map_iff in Hin.
    destruct Hin as [[a y] [Heq Hin]]; cbn in Heq; injection Heq as <- <-.
    split; [exact Hnode|exists a; exact Hin].
  - intros [Hnode [k Hin]]; exists n; split; [exact Hnode|].
    apply in_map_iff; exists (k, x); auto.
Qed.

Local Lemma sl_universe_length {N E V} (p : point_uses N E V) :
  length (sl_universe p) = length (Graph.nodes (live_graph p)) * length (sl_seeds p).
Proof.
  unfold sl_universe; induction (Graph.nodes (live_graph p)) as [|n ns IH]; cbn; [reflexivity|].
  rewrite length_app, length_map, IH; reflexivity.
Qed.

Local Lemma sl_seeds_support {N E V} (p : point_uses N E V) :
  incl (sl_seeds p) (sl_universe p).
Proof.
  intros [n x] Hin; apply sl_universe_agrees; split; [apply sl_seeds_agree in Hin; tauto|].
  exists n; exact Hin.
Qed.

Local Lemma sl_back_support {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  forall q, In q (sl_universe p) ->
    incl (sl_back EV EE p (prepare EN (live_graph p)) (sl_def_index EE EV p) q)
      (sl_universe p).
Proof.
  intros Hready [n x] Hq [k y] Hr.
  apply sl_universe_agrees in Hq; destruct Hq as [Hn Hvalue].
  apply (sl_back_agrees EN EE EV p n x k y Hready Hn) in Hr.
  destruct Hr as [-> [Hk _]]; apply sl_universe_agrees; auto.
Qed.

Local Lemma sl_seeds_sound {N E V} (p : point_uses N E V) :
  forall q, In q (sl_seeds p) -> syntactic_live p (snd q) (fst q).
Proof.
  intros [n x] Hin; apply sl_seeds_agree in Hin; destruct Hin as [_ [Hexit|[e [Hedge Huse]]]].
  - apply live_exit; exact Hexit.
  - eapply live_edge_use; eassumption.
Qed.

Local Lemma sl_back_sound {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  forall q, In q (sl_universe p) /\ syntactic_live p (snd q) (fst q) ->
    forall r, In r (sl_back EV EE p (prepare EN (live_graph p)) (sl_def_index EE EV p) q) ->
      In r (sl_universe p) /\ syntactic_live p (snd r) (fst r).
Proof.
  intros Hready [n x] [Hq Hlive] [k y] Hr; split.
  - eapply sl_back_support; eassumption.
  - apply sl_universe_agrees in Hq; destruct Hq as [Hn _].
    apply (sl_back_agrees EN EE EV p n x k y Hready Hn) in Hr.
    destruct Hr as [-> [_ [e [Hedge [Htarget Hkill]]]]].
    eapply live_edge_next; [exact Hedge|exact Hkill|rewrite Htarget; exact Hlive].
Qed.

Local Lemma sl_materialize_finished {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  let next := sl_back EV EE p (prepare EN (live_graph p)) (sl_def_index EE EV p) in
  let initial := sl_adds EN EV (sl_seeds p) (Map.empty, []) in
  let result := sl_run EN EV next (sl_budget p) initial in
  snd result = [] /\ sl_invariant EN EV (sl_universe p) next (sl_seeds p)
    (fun q => In q (sl_universe p) /\ syntactic_live p (snd q) (fst q)) result.
Proof.
  intro Hready; cbn zeta; apply sl_run_complete.
  - apply sl_seeds_support.
  - intros q Hin; split; [apply sl_seeds_support|apply sl_seeds_sound]; exact Hin.
  - apply sl_back_support; exact Hready.
  - apply sl_back_sound; exact Hready.
  - unfold sl_budget; rewrite sl_universe_length, Pos2Nat.inj_mul, !SuccNat2Pos.id_succ; nia.
Qed.

Local Lemma sl_materialize_closed {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  let m := sparse_live_materialize EN EE EV p in
  (forall n x, sparse_live_at EN EV m n x = true -> syntactic_live p x n) /\
  (forall n x, In (n, x) (sl_seeds p) -> sparse_live_at EN EV m n x = true) /\
  (forall n x k y, In n (Graph.nodes (live_graph p)) ->
    sparse_live_at EN EV m n x = true ->
    In (k, y) (sl_back EV EE p (prepare EN (live_graph p)) (sl_def_index EE EV p) (n, x)) ->
    sparse_live_at EN EV m k y = true).
Proof.
  intro Hready; pose proof (sl_materialize_finished EN EE EV p Hready) as [Hempty Hinv].
  destruct Hinv as [_ [_ [Hsound [Hseeds Hfront]]]]; split.
  - intros n x Hmem; exact (proj2 (Hsound (n, x) Hmem)).
  - split; [intros n x; apply (Hseeds (n, x))|].
    intros n x k y Hnode Hmem Hback.
    destruct (Hfront (n, x) Hmem) as [Hpending|Hclosed].
    + rewrite Hempty in Hpending; contradiction.
    + exact (Hclosed (k, y) Hback).
Qed.

(** The sparse result is exactly finite syntactic liveness at every listed point. *)
Theorem sparse_live_materialize_exact {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  forall n x, In n (Graph.nodes (live_graph p)) ->
    (sparse_live_at EN EV (sparse_live_materialize EN EE EV p) n x = true <->
      syntactic_live p x n).
Proof.
  intros Hready n x Hnode.
  destruct (sl_materialize_closed EN EE EV p Hready) as [Hsound [Hseeds Hclosed]].
  split; [apply Hsound|intro Hlive; revert Hnode].
  induction Hlive as [n Hexit|n e Hedge Huse|n e Hedge Hkill Hlive IH]; intro Hnode.
  - apply Hseeds, sl_seeds_agree; split; [exact Hnode|left; exact Hexit].
  - apply Hseeds, sl_seeds_agree; split; [exact Hnode|right; exists e; auto].
  - assert (Htarget : In (Graph.target (live_graph p) e) (Graph.nodes (live_graph p))).
    { eapply out_target_in; [exact (proj1 Hready)|exact Hnode|exact Hedge]. }
    eapply (Hclosed (Graph.target (live_graph p) e) x n x Htarget (IH Htarget)).
    apply sl_back_agrees; [exact Hready|exact Htarget|].
    split; [reflexivity|split; [exact Hnode|exists e; auto]].
Qed.

(** Every returned pair has, and every kill-free path inserts, a finite terminal-use witness. *)
Local Lemma sl_materialize_path {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (p : point_uses N E V) n x :
  ready EN (live_graph p) (prepare EN (live_graph p)) ->
  In n (Graph.nodes (live_graph p)) ->
  (sparse_live_at EN EV (sparse_live_materialize EN EE EV p) n x = true <->
    exists m es, path (live_graph p) n es m /\
      Forall (fun e => ~ In x (edge_def p e)) es /\ point_use_at p m x).
Proof.
  intros Hready Hnode.
  rewrite (sparse_live_materialize_exact EN EE EV p Hready n x Hnode).
  apply ViewsSsaPoints.syntactic_live_path_iff; exact (proj1 Hready).
Qed.

(** Equality to dense liveness requires the dense least solution, including unreachable nodes. *)
Theorem sparse_live_materialize_dense {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (sigma : N -> live_set EV vv) :
  ready EN (cfg (gview vv)) (prepare EN (cfg (gview vv))) ->
  least_solution (live_lattice EV vv) (liveness_system EV vv) sigma ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (var_point_uses vv)) n x =
      fmem EV x (sigma n).
Proof.
  intros Hready Hleast n x Hnode; apply eq_true_iff_eq.
  rewrite (sparse_live_materialize_exact EN EE EV (var_point_uses vv) Hready n x Hnode).
  symmetry; apply syntactic_live_least; [exact (proj1 Hready)|exact Hleast|exact Hnode].
Qed.

(** Successful Rules solving returns the same all-point least liveness bits. *)
Theorem sparse_live_materialize_rules {S O N E V C} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (vv : var_view S O N E V C) (db : database pred) :
  ready EN (cfg (gview vv)) (prepare EN (cfg (gview vv))) ->
  solve_program liveness_program (extract_live_facts EN EE EV vv) = Some db ->
  forall n x, In n (Graph.nodes (cfg (gview vv))) ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (var_point_uses vv)) n x =
      fmem EV x (live_of_db EN EV vv db n).
Proof.
  intros Hready Hsolve; apply sparse_live_materialize_dense; [exact Hready|].
  apply (rules_liveness_least EN EE EV vv db (proj1 Hready) Hsolve).
Qed.

(** Strict SSA and reachable query input identify materialized bits with the R/T query. *)
Theorem sparse_live_query_agrees {B BE N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (s : ssa_points B BE N E V) :
  ssa_point_laws s -> reachable_point_ssa s ->
  ready EN (live_graph (point_model s)) (prepare EN (live_graph (point_model s))) ->
  forall n x, reachable (live_graph (point_model s)) n ->
    sparse_live_at EN EV (sparse_live_materialize EN EE EV (point_model s)) n x =
    ssa_live_query EN EV (prepare_ssa_query_graph EN EE (live_graph (point_model s)))
      (prepare_ssa_query_values EN EV s) n x.
Proof.
  intros Hlaws Hssa Hready n x Hreach; apply eq_true_iff_eq.
  rewrite (sparse_live_materialize_exact EN EE EV (point_model s) Hready n x
    (reachable_in_nodes _ _ (proj1 Hready) Hreach)).
  symmetry; apply ssa_live_query_exact; assumption.
Qed.
