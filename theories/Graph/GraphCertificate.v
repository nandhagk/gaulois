(** * Graph path certificates

    Edge-list certificates check their endpoints and indexed successor membership.
    For example, an empty certificate is accepted exactly when its two endpoints agree.
    Builds on: GraphCore, GraphPrepare and GraphDfs. *)

From Stdlib Require Import List Bool PArith Arith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs.
Import List.ListNotations.

(** Check each listed edge at its current endpoint, then check the final endpoint. *)
Fixpoint check_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (eqE : E -> E -> bool) (s : V) (es : list E) (v : V) : bool :=
  match es with
  | [] => Pos.eqb (encode EV s) (encode EV v)
  | e :: rest =>
    Pos.eqb (encode EV s) (encode EV (Graph.source g e)) &&
    existsb (eqE e) (succ_edges p s) && check_path p eqE (Graph.target g e) rest v
  end.

(** Following parent edges prepends them to the growing path, without a final reversal. *)
Definition tree_path_step {V E} {EV : encoding V} {g : Graph.t V E}
    (r : dfs_result V E) (work : bool * V * list E) : bool * V * list E :=
  let '(done_, v, es) := work in
  if done_ then work
  else
    match Map.get EV v (tree_edge r) with
    | None => (true, v, es)
    | Some e => (false, Graph.source g e, e :: es)
    end.

(** Binary blocks stop as soon as the parent walk has found its root. *)
Fixpoint tree_path_run {V E} {EV : encoding V} {g : Graph.t V E}
    (r : dfs_result V E) (n : positive) (work : bool * V * list E) : bool * V * list E :=
  let '(done_, _, _) := work in
  if done_ then work else
    match n with
    | xH => tree_path_step (EV := EV) (g := g) r work
    | xO k => tree_path_run (EV := EV) (g := g) r k
        (tree_path_run (EV := EV) (g := g) r k work)
    | xI k => tree_path_step (EV := EV) (g := g) r
        (tree_path_run (EV := EV) (g := g) r k
          (tree_path_run (EV := EV) (g := g) r k work))
    end.

Lemma tree_path_iter_done {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) v es n :
  Pos.iter (tree_path_step (EV := EV) (g := g) r) (true, v, es) n = (true, v, es).
Proof.
  induction n using Pos.peano_ind; [reflexivity|rewrite Pos.iter_succ, IHn; reflexivity].
Qed.

Lemma tree_path_run_agrees {V E} (EV : encoding V) (g : Graph.t V E)
    (r : dfs_result V E) n work :
  tree_path_run (EV := EV) (g := g) r n work =
    Pos.iter (tree_path_step (EV := EV) (g := g) r) work n.
Proof.
  revert work; induction n as [n IH|n IH|]; intros [[done_ v] es]; destruct done_.
  - symmetry; apply tree_path_iter_done.
  - cbn [tree_path_run]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO n)).
  - symmetry; apply tree_path_iter_done.
  - cbn [tree_path_run]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Recover a tree path with prepared binary fuel, rejecting an unfinished parent walk. *)
Definition tree_path {V E} {EV : encoding V} {g : Graph.t V E} (p : prepared EV g)
    (r : dfs_result V E) (v : V) : option (V * list E) :=
  if FinSet.mem EV v (visited r) then
    let '(done_, s, es) :=
      tree_path_run (EV := EV) (g := g) r (fuel p) (false, v, []) in
    if done_ then Some (s, es) else None
  else None.

(** A checked edge-list certificate is exactly a graph path between its endpoints. *)
Theorem check_path_correct {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) (v s : V) (es : list E) (eqE : E -> E -> bool) :
  ready EV g p -> (forall a b, eqE a b = true <-> a = b) -> In s (Graph.nodes g) ->
  (check_path p eqE s es v = true <-> path g s es v).
Proof.
  intros [Hwf [_ Hlaws]] Heq; revert s.
  induction es as [|e es IH]; intros s Hnode; cbn [check_path].
  - rewrite Pos.eqb_eq; split.
    + intro H; apply (encode_injective EV) in H; subst v; constructor.
    + intro H; inversion H; reflexivity.
  - rewrite !andb_true_iff, Pos.eqb_eq.
    split.
    + intros [[Hsource Hin] Htail].
      apply (encode_injective EV) in Hsource; subst s.
      apply existsb_exists in Hin; destruct Hin as [a [Hin Ha]].
      apply Heq in Ha; subst a; rewrite (succ_agrees Hlaws _ Hnode) in Hin.
      constructor; [exact Hin|]. apply IH; [|exact Htail].
      eapply out_target_in; eauto.
    + intro Hpath; inversion Hpath as [|a rest w Hin Htail]; subst.
      split; [split; [reflexivity|]|].
      * apply existsb_exists; exists e; split.
        -- rewrite (succ_agrees Hlaws _ Hnode); exact Hin.
        -- apply Heq; reflexivity.
      * apply IH; [|exact Htail]. eapply out_target_in; eauto.
Qed.

(** * Terminating parent walks *)

(** A numbered discovery forest has valid edges and strictly smaller parent ranks. *)
Record tree_path_laws {V E} (EV : encoding V) (g : Graph.t V E)
    (roots : list V) (r : dfs_result V E) : Prop := {
  tree_path_numbered : forall v, FinSet.mem EV v (visited r) = true ->
    exists k, Map.get EV v (pre_num r) = Some k;
  tree_path_root : forall v, FinSet.mem EV v (visited r) = true ->
    Map.get EV v (tree_edge r) = None -> In v roots;
  tree_path_parent : forall v e, FinSet.mem EV v (visited r) = true ->
    Map.get EV v (tree_edge r) = Some e ->
    In e (Graph.out g (Graph.source g e)) /\ Graph.target g e = v /\
    FinSet.mem EV (Graph.source g e) (visited r) = true /\
    forall k, Map.get EV v (pre_num r) = Some k ->
      exists j, Map.get EV (Graph.source g e) (pre_num r) = Some j /\ Pos.lt j k
}.

Lemma dfs_tree_path_laws {V E} (EV : encoding V) (g : Graph.t V E)
    (p : prepared EV g) roots blocked :
  ready EV g p -> incl roots (Graph.nodes g) ->
  tree_path_laws EV g roots (dfs p blocked roots).
Proof.
  intros Hready Hroots.
  pose proof (dfs_fold_labels EV g p blocked roots roots dfs_initial Hready Hroots
    ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)
    (dfs_initial_labels EV g roots)) as Hlabels.
  destruct (dfs_fold_spec EV g p blocked roots roots dfs_initial Hready Hroots
    ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)) as [Hinv _].
  constructor; unfold dfs; cbn [visited tree_edge pre_num].
  - intros v Hv; apply (dfs_seen_pre _ _ _ _ _ _ Hinv) in Hv.
    apply (dfs_numbering_domain EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)); exact Hv.
  - intros v Hv Hnone; apply (dfs_root_labels _ _ _ _ Hlabels); [|exact Hnone].
    apply (dfs_seen_pre _ _ _ _ _ _ Hinv); exact Hv.
  - intros v e Hv He.
    destruct (dfs_parent_labels _ _ _ _ Hlabels v e He)
      as [_ [Hs [Hedge [Ht [a [b [Ha [Hb Hlt]]]]]]]].
    split; [exact Hedge|]; split; [exact Ht|]; split.
    + apply (dfs_seen_pre _ _ _ _ _ _ Hinv); exact Hs.
    + intros k Hk; rewrite Hb in Hk; inversion Hk; subst k; exists a; auto.
Qed.

(** A walk carries a valid path from its current vertex to its fixed destination. *)
Definition tree_walk_ok {V E} (EV : encoding V) (g : Graph.t V E) roots
    (r : dfs_result V E) (target : V) (work : bool * V * list E) : Prop :=
  let '(done_, v, es) := work in
  FinSet.mem EV v (visited r) = true /\ path g v es target /\
  (done_ = true -> In v roots /\ Map.get EV v (tree_edge r) = None).

(** A completed walk has zero remaining rank. *)
Definition tree_walk_measure {V E} (EV : encoding V) (r : dfs_result V E)
    (work : bool * V * list E) : nat :=
  let '(done_, v, _) := work in
  if done_ then 0 else
    match Map.get EV v (pre_num r) with
    | None => 0
    | Some k => Pos.to_nat k
    end.

(** The stop flag is independent of the current endpoint and accumulated certificate. *)
Definition tree_walk_done {V E} (work : bool * V * list E) : bool :=
  let '(done_, _, _) := work in done_.

Lemma tree_walk_step_preserved {V E} (EV : encoding V) (g : Graph.t V E) roots r target work :
  tree_path_laws EV g roots r -> tree_walk_ok EV g roots r target work ->
  tree_walk_ok EV g roots r target (tree_path_step (EV := EV) (g := g) r work).
Proof.
  intros Hlaws; destruct work as [[done_ v] es]; intros [Hv [Hpath Hroot]].
  destruct done_; cbn [tree_path_step tree_walk_ok]; [auto|].
  destruct (Map.get EV v (tree_edge r)) as [e|] eqn:He.
  - destruct (tree_path_parent _ _ _ _ Hlaws v e Hv He) as [Hedge [Ht [Hs _]]].
    split; [exact Hs|]; split; [|discriminate].
    constructor; [exact Hedge|rewrite Ht; exact Hpath].
  - split; [exact Hv|]; split; [exact Hpath|].
    intros _; split; [apply (tree_path_root _ _ _ _ Hlaws v Hv He)|exact He].
Qed.

Lemma tree_walk_step_decreases {V E} (EV : encoding V) (g : Graph.t V E)
    roots r target work :
  tree_path_laws EV g roots r -> tree_walk_ok EV g roots r target work ->
  tree_walk_done work = false ->
  tree_walk_measure EV r (tree_path_step (EV := EV) (g := g) r work) <
    tree_walk_measure EV r work.
Proof.
  intros Hlaws; destruct work as [[done_ v] es]; intros [Hv _] Hdone.
  destruct done_; [discriminate|].
  destruct (tree_path_numbered _ _ _ _ Hlaws v Hv) as [k Hk].
  unfold tree_path_step; cbn [tree_walk_measure]; rewrite Hk.
  destruct (Map.get EV v (tree_edge r)) as [e|] eqn:He.
  - destruct (tree_path_parent _ _ _ _ Hlaws v e Hv He) as [_ [_ [_ Hrank]]].
    destruct (Hrank k Hk) as [j [Hj Hlt]].
    cbn [tree_walk_measure]; rewrite Hj; apply Pos2Nat.inj_lt; exact Hlt.
  - cbn [tree_walk_measure]; apply Pos2Nat.is_pos.
Qed.

Lemma tree_walk_iter_bound {V E} (EV : encoding V) (g : Graph.t V E)
    roots r target work n :
  tree_path_laws EV g roots r -> tree_walk_ok EV g roots r target work ->
  let result := Pos.iter (tree_path_step (EV := EV) (g := g) r) work n in
  tree_walk_ok EV g roots r target result /\
  (tree_walk_done result = true \/
    tree_walk_measure EV r result + Pos.to_nat n <= tree_walk_measure EV r work).
Proof.
  intros Hlaws Hstart; induction n using Pos.peano_ind.
  - cbn [Pos.iter]; split; [apply tree_walk_step_preserved; assumption|].
    destruct work as [[done_ v] es]; destruct done_; [left; reflexivity|].
    right; change (tree_walk_measure EV r (tree_path_step (EV := EV) (g := g) r
      (false, v, es)) + 1 <= tree_walk_measure EV r (false, v, es)).
    rewrite Nat.add_1_r; apply (tree_walk_step_decreases EV g roots r target);
      try assumption; reflexivity.
  - rewrite Pos.iter_succ.
    destruct IHn as [Hok Hbound].
    split; [apply tree_walk_step_preserved; assumption|].
    destruct (Pos.iter (tree_path_step (EV := EV) (g := g) r) work n)
      as [[done_ v] es] eqn:Hrun.
    destruct done_; [left; reflexivity|].
    destruct Hbound as [Hfalse|Hbound]; [discriminate|].
    right; pose proof (tree_walk_step_decreases EV g roots r target (false, v, es)
      Hlaws Hok eq_refl) as Hdecrease.
    rewrite Pos2Nat.inj_succ, Nat.add_succ_r, <- Nat.add_succ_l.
    eapply Nat.le_trans; [apply Nat.add_le_mono_r; exact Hdecrease|exact Hbound].
Qed.

(** Every visited vertex has a recovered valid discovery path from one of the supplied roots. *)
Theorem tree_path_valid {V E} (EV : encoding V) (g : Graph.t V E) (p : prepared EV g)
    (v : V) (roots : list V) (blocked : FinSet.t V) :
  ready EV g p -> incl roots (Graph.nodes g) ->
  FinSet.mem EV v (visited (dfs p blocked roots)) = true ->
  exists s es, tree_path p (dfs p blocked roots) v = Some (s, es) /\
    In s roots /\ path g s es v.
Proof.
  intros Hready Hroots Hv.
  pose proof (dfs_tree_path_laws EV g p roots blocked Hready Hroots) as Hlaws.
  assert (Hstart : tree_walk_ok EV g roots (dfs p blocked roots) v (false, v, [])).
  { split; [exact Hv|]; split; [constructor|discriminate]. }
  pose proof (tree_walk_iter_bound EV g roots (dfs p blocked roots) v
    (false, v, []) (fuel p) Hlaws Hstart) as [Hok Hbound].
  assert (Hrank : tree_walk_measure EV (dfs p blocked roots) (false, v, []) <
    Pos.to_nat (fuel p)).
  { pose proof (dfs_fold_labels EV g p blocked roots roots dfs_initial Hready Hroots
      ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)
      (dfs_initial_labels EV g roots)) as Hlabels.
    destruct (tree_path_numbered _ _ _ _ Hlaws v Hv) as [k Hk].
    cbn [tree_walk_measure]; rewrite Hk.
    pose proof Hready as [Hwf [_ Hprepared]].
    unfold dfs in Hk; cbn [pre_num] in Hk.
    pose proof (dfs_numbering_bound EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels) v k Hk)
      as Hlt.
    apply Pos2Nat.inj_lt in Hlt.
    rewrite (dfs_numbering_size EV _ _ _ (dfs_pre_numbering _ _ _ _ Hlabels)) in Hlt.
    destruct (dfs_fold_spec EV g p blocked roots roots dfs_initial Hready Hroots
      ltac:(intros w Hw; exact Hw) (dfs_initial_invariant EV g blocked roots)) as [Hinv _].
    pose proof (NoDup_incl_length (dfs_pre_nodup _ _ _ _ _ _ Hinv)
      (dfs_pre_nodes _ _ _ _ _ _ Hinv)) as Hsize.
    rewrite (fuel_value Hprepared); lia. }
  unfold tree_path; rewrite Hv, tree_path_run_agrees.
  destruct (Pos.iter (tree_path_step (EV := EV) (g := g) (dfs p blocked roots))
    (false, v, []) (fuel p)) as [[done_ s] es] eqn:Hrun.
  destruct done_.
  - exists s, es; split; [reflexivity|].
    destruct Hok as [_ [Hpath Hroot]]; destruct (Hroot eq_refl) as [Hs _]; auto.
  - destruct Hbound as [Hfalse|Hbound]; [discriminate|lia].
Qed.
