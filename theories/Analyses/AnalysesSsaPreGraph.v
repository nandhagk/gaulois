(** * Factored expression SSA graphs

    Expression instances retain their ordered SSA operands across simultaneous incoming-edge
    substitutions. For example, parallel edges to one block can translate its expression to
    two different predecessor expressions.
    Builds on: AnalysesAvailable, ViewsSsaPoints, ViewsSsa, GraphFrontier and Collections maps. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphDominance
  GraphDominators GraphFrontier GraphIdf GraphSemiDominators GraphLoops GraphLengauerTarjan.
From Gaulois.Views Require Import ViewsGraph ViewsSsa ViewsSsaPoints.
From Gaulois.Analyses Require Import AnalysesAvailable.
Import List.ListNotations.

(** * Expression views and simultaneous substitution *)

(** The eligible expressions are pure recomputations in a gen/kill view. *)
Record pre_expression_view (S O N E U C : Type) : Type := PreExpressionView {
  pre_genkill : genkill_view S O N E U C;
  pre_total_pure : U -> bool;
  pre_recomputed : E -> option U
}.
Arguments PreExpressionView {S O N E U C}.
Arguments pre_genkill {S O N E U C}.
Arguments pre_total_pure {S O N E U C}.
Arguments pre_recomputed {S O N E U C}.

(** A client supplies expression syntax, evaluation and each incoming edge's substitution. *)
Record pre_expr_ssa (S O B BE N E V K C U : Type) : Type := PreExprSsa {
  pre_ssa_points : ssa_points B BE N E V;
  pre_ssa_view : ssa_view S O B BE V K C;
  pre_expression : pre_expression_view S O N E U C;
  pre_seed_expressions : list U;
  pre_value_universe : list V;
  pre_expression_shape : U -> positive;
  pre_operands : U -> list V;
  pre_expr_eval : U -> (V -> option C) -> option C;
  pre_phi_translate : BE -> U -> option U;
  pre_initial_available : U -> bool;
  pre_exit_point : N -> bool
}.
Arguments PreExprSsa {S O B BE N E V K C U}.
Arguments pre_ssa_points {S O B BE N E V K C U}.
Arguments pre_ssa_view {S O B BE N E V K C U}.
Arguments pre_expression {S O B BE N E V K C U}.
Arguments pre_seed_expressions {S O B BE N E V K C U}.
Arguments pre_value_universe {S O B BE N E V K C U}.
Arguments pre_expression_shape {S O B BE N E V K C U}.
Arguments pre_operands {S O B BE N E V K C U}.
Arguments pre_expr_eval {S O B BE N E V K C U}.
Arguments pre_phi_translate {S O B BE N E V K C U}.
Arguments pre_initial_available {S O B BE N E V K C U}.
Arguments pre_exit_point {S O B BE N E V K C U}.

(** The family is the least closure of seed instances under listed block-edge translation. *)
Inductive pre_expr_in_family {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) : U -> Prop :=
  | pre_family_seed : forall u, In u (pre_seed_expressions a) -> pre_expr_in_family a u
  | pre_family_translate : forall u be u', pre_expr_in_family a u ->
      In be (edges_of (block_graph (pre_ssa_points a))) ->
      pre_phi_translate a be u = Some u' -> pre_expr_in_family a u'.

(** Target parameters map to positional incoming arguments and other values map to themselves. *)
Definition pre_phi_operand {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) (be : BE) : V -> V :=
  let s := pre_ssa_points a in
  let substitution := Map.of_list EV
    (combine (block_params s (Graph.target (block_graph s) be)) (block_edge_args s be)) in
  fun x => match Map.get EV x substitution with
  | Some y => y
  | None => x
  end.

(** Each target parameter reads its own argument from the same pre-edge environment. *)
Definition pre_phi_env {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) (be : BE)
    (env : V -> option C) : V -> option C :=
  let operand := pre_phi_operand EV a be in
  fun x => env (operand x).

(** Each block-edge identity indexes its unique point-edge occurrence. *)
Definition pre_point_edge_index {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) : Map.t BE E :=
  Map.of_list EBE (flat_map (fun e => match block_edge_of s e with
    | Some be => [(be, e)]
    | None => []
    end) (edges_of (live_graph (point_model s)))).

(** The supported domain has one reachable entry and a finite shape-bounded expression family. *)
Record pre_expr_ssa_laws {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) : Prop := {
  pre_expr_points : ssa_point_laws (pre_ssa_points a);
  pre_expr_strict : reachable_point_ssa (pre_ssa_points a);
  pre_expr_block_graph : block_graph (pre_ssa_points a) = cfg (base (pre_ssa_view a));
  pre_expr_point_graph : live_graph (point_model (pre_ssa_points a)) =
    cfg (gkview (pre_genkill (pre_expression a)));
  pre_expr_reachable_blocks : forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    reachable (block_graph (pre_ssa_points a)) b;
  pre_expr_reachable_points : forall n,
    In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
    reachable (live_graph (point_model (pre_ssa_points a))) n;
  pre_expr_entry_position : exists b n,
    Graph.entries (block_graph (pre_ssa_points a)) = [b] /\
    Graph.entries (live_graph (point_model (pre_ssa_points a))) = [n] /\
    nth_error (points_in_block (pre_ssa_points a) b) 0 = Some n;
  pre_expr_entry_no_incoming : forall b be,
    In b (Graph.entries (block_graph (pre_ssa_points a))) ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be <> b;
  pre_expr_params_nodup : forall b, NoDup (block_params (pre_ssa_points a) b);
  pre_expr_value_nodup : NoDup (pre_value_universe a);
  pre_expr_occurrences : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    In u (pre_seed_expressions a);
  pre_expr_initial_in_family : forall u, pre_initial_available a u = true ->
    pre_expr_in_family a u;
  pre_expr_finite_operands : forall u, pre_expr_in_family a u ->
    incl (pre_operands a u) (pre_value_universe a);
  pre_expr_shape_identity : forall u u', pre_expr_in_family a u -> pre_expr_in_family a u' ->
    pre_expression_shape a u = pre_expression_shape a u' ->
    pre_operands a u = pre_operands a u' -> u = u';
  pre_expr_shape_arity : forall u u', pre_expr_in_family a u -> pre_expr_in_family a u' ->
    pre_expression_shape a u = pre_expression_shape a u' ->
    length (pre_operands a u) = length (pre_operands a u');
  pre_expr_runtime : forall s u,
    uval (pre_genkill (pre_expression a)) s u = pre_expr_eval a u (val (pre_ssa_view a) s);
  pre_expr_operand_support : forall u env1 env2,
    (forall x, In x (pre_operands a u) -> env1 x = env2 x) ->
    pre_expr_eval a u env1 = pre_expr_eval a u env2;
  pre_expr_kill_operand : forall e u,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_expr_in_family a u -> kill (pre_genkill (pre_expression a)) e u = true ->
    exists x, In x (pre_operands a u) /\
      In x (edge_def (point_model (pre_ssa_points a)) e);
  pre_expr_def_home : forall e x,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    In x (edge_def (point_model (pre_ssa_points a)) e) ->
    home (pre_ssa_view a) x = block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e);
  pre_expr_cross_no_defs : forall e be,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    block_edge_of (pre_ssa_points a) e = Some be ->
    edge_def (point_model (pre_ssa_points a)) e = [];
  pre_expr_real_internal : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    block_edge_of (pre_ssa_points a) e = None /\
    (forall b, e <> parameter_edge (pre_ssa_points a) b);
  pre_expr_closed_translation : forall be u,
    In be (edges_of (block_graph (pre_ssa_points a))) -> pre_expr_in_family a u ->
    exists u', pre_phi_translate a be u = Some u';
  pre_expr_translation_shape : forall be u u', pre_expr_in_family a u ->
    pre_phi_translate a be u = Some u' -> pre_expression_shape a u' = pre_expression_shape a u;
  pre_expr_translation_operands : forall be u u', pre_expr_in_family a u ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_phi_translate a be u = Some u' ->
    pre_operands a u' = map (pre_phi_operand EV a be) (pre_operands a u);
  pre_expr_translation_pure : forall be u u', pre_total_pure (pre_expression a) u = true ->
    pre_phi_translate a be u = Some u' -> pre_total_pure (pre_expression a) u' = true;
  pre_expr_translation_eval : forall be u u' env,
    In be (edges_of (block_graph (pre_ssa_points a))) -> pre_expr_in_family a u ->
    pre_phi_translate a be u = Some u' ->
    pre_expr_eval a u (pre_phi_env EV a be env) = pre_expr_eval a u' env
}.

(** * Positional substitution laws *)

Local Lemma pre_combine_member {X Y} (xs : list X) (ys : list Y) i x y :
  nth_error xs i = Some x -> nth_error ys i = Some y -> In (x, y) (combine xs ys).
Proof.
  revert xs ys; induction i as [|i IH]; intros [|a xs] [|b ys] Hx Hy;
    cbn in *; try discriminate.
  - inversion Hx; inversion Hy; subst; left; reflexivity.
  - right; exact (IH xs ys Hx Hy).
Qed.

Local Lemma pre_chain_edges_nodup {N E} (g : Graph.t N E) ns es :
  graph_wf g -> point_chain g ns es -> NoDup ns -> NoDup es.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n m ns edge es Hedge Htarget Hchain IH];
    intro Hnodup; [constructor|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail]; constructor.
  - intro Hin; apply Hfresh.
    assert (Hsource : In (Graph.source g edge) (m :: ns)).
    { clear Hfresh Htarget IH Htail; induction Hchain as
        [point|point next points e edges He Ht Hchain IH]; [contradiction|].
      destruct Hin as [Heq|Hin].
      - subst e; rewrite (out_source Hwf point edge He); left; reflexivity.
      - right; exact (IH Hin). }
    rewrite (out_source Hwf n edge Hedge) in Hsource; exact Hsource.
  - apply IH; exact Htail.
Qed.

Local Lemma pre_chain_edge_not_self {N E} (g : Graph.t N E) ns es :
  graph_wf g -> point_chain g ns es -> NoDup ns ->
  forall e, In e es -> Graph.source g e <> Graph.target g e.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n m ns edge es Hedge Htarget Hchain IH];
    intros Hnodup e He; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  destruct He as [Heq|Hin].
  - subst e; rewrite (out_source Hwf n edge Hedge), Htarget.
    intro Heq; apply Hfresh; left; symmetry; exact Heq.
  - exact (IH Htail e Hin).
Qed.

Local Lemma pre_last_default {X} (xs : list X) x y :
  xs <> [] -> last xs x = last xs y.
Proof.
  induction xs as [|head rest IH]; [contradiction|].
  intros Hnonempty; destruct rest as [|next rest]; [reflexivity|].
  cbn [last]; apply IH; discriminate.
Qed.

Local Lemma pre_combine_keys {X Y} (xs : list X) (ys : list Y) :
  length xs = length ys -> map fst (combine xs ys) = xs.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys] Hlen; cbn in *;
    try discriminate; [reflexivity|].
  f_equal; apply IH; lia.
Qed.

Local Lemma pre_map_list_unique {X Y} (EX : encoding X) (pairs : list (X * Y)) x y :
  (forall z, In (x, z) pairs -> z = y) -> In (x, y) pairs ->
  Map.get EX x (Map.of_list EX pairs) = Some y.
Proof.
  intros Hunique Hin; rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode EX (fst kv)) (encode EX x))
    (rev pairs)) as [[k v]|] eqn:Hfind.
  - apply find_some in Hfind; destruct Hfind as [Hmember Hkey].
    cbn in Hkey; apply Pos.eqb_eq in Hkey; apply (encode_injective EX) in Hkey; subst k.
    apply in_rev in Hmember; cbn; f_equal; apply Hunique; exact Hmember.
  - pose proof (find_none _ _ Hfind (x, y) (proj1 (in_rev _ _) Hin)) as Hfalse.
    cbn in Hfalse; rewrite Pos.eqb_refl in Hfalse; discriminate.
Qed.

Local Lemma pre_map_list_member {X Y} (EX : encoding X) (pairs : list (X * Y)) x y :
  NoDup (map fst pairs) -> In (x, y) pairs -> Map.get EX x (Map.of_list EX pairs) = Some y.
Proof.
  intros Hnodup Hin; apply pre_map_list_unique; [|exact Hin].
  assert (Hunique : forall z, In (x, z) pairs -> z = y).
  { induction pairs as [|[k v] pairs IH]; [contradiction|].
    inversion Hnodup as [|key keys Hfresh Htail]; subst.
    intros z Hz; cbn in Hin, Hz; destruct Hin as [Heq|Hin], Hz as [Heq'|Hz].
    - congruence.
    - inversion Heq; subst k v; exfalso; apply Hfresh.
      exact (in_map fst _ _ Hz).
    - inversion Heq'; subst k v; exfalso; apply Hfresh.
      exact (in_map fst _ _ Hin).
    - exact (IH Htail Hin z Hz). }
  exact Hunique.
Qed.

Local Lemma pre_map_list_sound {X Y} (EX : encoding X) (pairs : list (X * Y)) x y :
  Map.get EX x (Map.of_list EX pairs) = Some y -> In (x, y) pairs.
Proof.
  rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode EX (fst kv)) (encode EX x))
    (rev pairs)) as [[k v]|] eqn:Hfind; [|discriminate].
  cbn; intro Heq; inversion Heq; subst v.
  apply find_some in Hfind; destruct Hfind as [Hin Hkey].
  cbn in Hkey; apply Pos.eqb_eq in Hkey; apply (encode_injective EX) in Hkey; subst k.
  apply in_rev in Hin; exact Hin.
Qed.

Local Lemma pre_point_edge_pairs {B BE N E V} (s : ssa_points B BE N E V) be e :
  In (be, e) (flat_map (fun pe => match block_edge_of s pe with
    | Some key => [(key, pe)]
    | None => []
    end) (edges_of (live_graph (point_model s)))) <->
  In e (edges_of (live_graph (point_model s))) /\ block_edge_of s e = Some be.
Proof.
  rewrite in_flat_map; split.
  - intros [pe [Hin Hpair]]; destruct (block_edge_of s pe) as [key|] eqn:Hkey;
      cbn in Hpair; [|contradiction].
    destruct Hpair as [Heq|Hfalse]; [inversion Heq; subst; auto|contradiction].
  - intros [Hin Hkey]; exists e; split; [exact Hin|rewrite Hkey; left; reflexivity].
Qed.

(** The prepared edge index preserves individual parallel edges and covers every point edge. *)
Theorem pre_point_edge_index_exact {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) :
  ssa_point_laws s -> forall be e,
    (Map.get EBE be (pre_point_edge_index EBE s) = Some e <->
      In e (edges_of (live_graph (point_model s))) /\ block_edge_of s e = Some be).
Proof.
  intros Hlaw be e; unfold pre_point_edge_index; split.
  - intro Hget; apply pre_point_edge_pairs; apply (pre_map_list_sound EBE); exact Hget.
  - intros [Hin Hkey]; apply pre_map_list_unique.
    + intros pe Hpair; apply pre_point_edge_pairs in Hpair; destruct Hpair as [Hpe Hproject].
      exact (block_edge_unique Hlaw pe e be Hpe Hin Hproject Hkey).
    + apply pre_point_edge_pairs; auto.
Qed.

(** Parameter substitution reads the argument at the same incoming-edge position. *)
Theorem pre_phi_env_parameter {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be i x y env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    nth_error (block_params (pre_ssa_points a)
      (Graph.target (block_graph (pre_ssa_points a)) be)) i = Some x ->
    nth_error (block_edge_args (pre_ssa_points a) be) i = Some y ->
    pre_phi_env EV a be env x = env y.
Proof.
  intros Hlaw be i x y env Hedge Hx Hy; unfold pre_phi_env, pre_phi_operand.
  assert (Hlength := phi_args_length (pre_expr_points EV a Hlaw) be Hedge).
  rewrite (pre_map_list_member EV _ x y).
  - reflexivity.
  - rewrite pre_combine_keys by lia; apply (pre_expr_params_nodup EV a Hlaw).
  - eapply pre_combine_member; eassumption.
Qed.

(** Simultaneous assignment leaves values outside the target parameter list unchanged. *)
Theorem pre_phi_env_frame {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be x env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    ~ In x (block_params (pre_ssa_points a)
      (Graph.target (block_graph (pre_ssa_points a)) be)) ->
    pre_phi_env EV a be env x = env x.
Proof.
  intros Hlaw be x env Hedge Houtside; unfold pre_phi_env, pre_phi_operand.
  rewrite Map.get_of_list.
  destruct (find (fun kv => Pos.eqb (encode EV (fst kv)) (encode EV x))
    (rev (combine (block_params (pre_ssa_points a)
      (Graph.target (block_graph (pre_ssa_points a)) be))
      (block_edge_args (pre_ssa_points a) be)))) as [[p y]|] eqn:Hfind.
  - exfalso; apply find_some in Hfind; destruct Hfind as [Hin Heq].
    cbn in Heq; apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst p.
    apply in_rev in Hin; apply Houtside; pose proof (in_map fst _ _ Hin) as Hkeys.
    rewrite pre_combine_keys in Hkeys.
    + exact Hkeys.
    + symmetry; apply (phi_args_length (pre_expr_points EV a Hlaw) be Hedge).
  - reflexivity.
Qed.

(** Environment substitution is exactly composition with the positional operand map. *)
Theorem pre_phi_env_substitution {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be x env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_phi_env EV a be env x = env (pre_phi_operand EV a be x).
Proof.
  intros Hlaw be x env Hedge; reflexivity.
Qed.

(** Each translated expression evaluates in the incoming environment as the original after phi. *)
Theorem frg_translation_agrees {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  forall be u u' env, In be (edges_of (block_graph (pre_ssa_points a))) ->
    pre_expr_in_family a u -> pre_phi_translate a be u = Some u' ->
    pre_expr_eval a u (pre_phi_env EV a be env) = pre_expr_eval a u' env.
Proof.
  intros Hlaw; exact (pre_expr_translation_eval EV a Hlaw).
Qed.

(** * Memoized finite discovery *)

(* A work item is translated only on its first pop. Duplicate arrivals cost one pop each.
   The bound is computed with binary arithmetic, without enumerating operand tuples. *)
Local Definition pre_family_bound {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) : BinNums.N :=
  let values := N.of_nat (length (pre_value_universe a)) in
  fold_right (fun u count =>
    N.pow values (N.of_nat (length (pre_operands a u))) + count)%N
    0%N (pre_seed_expressions a).

Local Definition pre_translated {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (bes : list BE) (u : U) : list U :=
  flat_map (fun be => match pre_phi_translate a be u with
    | Some translated => [translated]
    | None => []
    end) bes.

Local Definition pre_discover_step {X} (EX : encoding X) (next : X -> list X)
    (work : list X * FinSet.t X) : list X * FinSet.t X :=
  let '(pending, seen) := work in
  match pending with
  | [] => work
  | x :: rest =>
    if FinSet.mem EX x seen then (rest, seen)
    else (next x ++ rest, FinSet.add EX x seen)
  end.

Local Fixpoint pre_discover_run {X} (EX : encoding X) (next : X -> list X)
    (fuel : positive) (work : list X * FinSet.t X) : list X * FinSet.t X :=
  match fst work with
  | [] => work
  | _ :: _ =>
    match fuel with
    | xH => pre_discover_step EX next work
    | xO p => pre_discover_run EX next p (pre_discover_run EX next p work)
    | xI p => pre_discover_step EX next
        (pre_discover_run EX next p (pre_discover_run EX next p work))
    end
  end.

(** Seeded discovery returns every memoized instance, even on a malformed partial run. *)
Definition pre_expr_universe {S O B BE N E V K C U} (EBE : encoding BE) (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) : list U :=
  let bes := FinSet.elements (FinSet.of_list EBE (edges_of (block_graph (pre_ssa_points a)))) in
  let bound := (N.of_nat (length (pre_seed_expressions a)) +
    pre_family_bound a * (1 + N.of_nat (length bes)))%N in
  FinSet.elements (snd (pre_discover_run EU (pre_translated a bes) (N.succ_pos bound)
    (pre_seed_expressions a, FinSet.empty))).

(* This list is used only in proofs to count signatures. The executable discovery above
   computes the exponential number, and never calls this enumeration. *)
Local Fixpoint pre_operand_tuples {V} (values : list V) (arity : nat) : list (list V) :=
  match arity with
  | O => [[]]
  | S n => flat_map (fun x => map (cons x) (pre_operand_tuples values n)) values
  end.

Local Lemma pre_operand_tuples_exact {V} (values operands : list V) :
  In operands (pre_operand_tuples values (length operands)) <-> incl operands values.
Proof.
  induction operands as [|x operands IH]; cbn [pre_operand_tuples length].
  - split; [intros _ y Hfalse; contradiction|intros _; left; reflexivity].
  - rewrite in_flat_map; split.
    + intros [v [Hv Hmap]]; apply in_map_iff in Hmap.
      destruct Hmap as [xs [Heq Hin]]; inversion Heq; subst v xs.
      intros y [Hsame|Hy]; [subst y; exact Hv|apply (proj1 IH Hin); exact Hy].
    + intro Hincl; exists x; split; [apply Hincl; left; reflexivity|].
      apply in_map_iff; exists operands; split; [reflexivity|apply IH].
      intros y Hy; apply Hincl; right; exact Hy.
Qed.

Local Lemma pre_operand_tuples_length {V} (values : list V) arity :
  length (pre_operand_tuples values arity) = Nat.pow (length values) arity.
Proof.
  induction arity as [|arity IH]; [reflexivity|].
  cbn [pre_operand_tuples Nat.pow].
  assert (Hcount : forall vals : list V,
    length (flat_map (fun x => map (cons x) (pre_operand_tuples values arity)) vals) =
      length vals * length (pre_operand_tuples values arity)).
  { intro vals; induction vals as [|x vals IHvals]; cbn [flat_map length]; [reflexivity|].
    rewrite length_app, length_map, IHvals; lia. }
  rewrite Hcount, IH; reflexivity.
Qed.

Local Definition pre_signatures {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) : list (positive * list V) :=
  flat_map (fun seed => map (fun operands => (pre_expression_shape a seed, operands))
    (pre_operand_tuples (pre_value_universe a) (length (pre_operands a seed))))
    (pre_seed_expressions a).

Local Lemma pre_family_seed_shape {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a -> forall u, pre_expr_in_family a u ->
  exists seed, In seed (pre_seed_expressions a) /\
    pre_expression_shape a u = pre_expression_shape a seed /\
    length (pre_operands a u) = length (pre_operands a seed).
Proof.
  intros Hlaw u Hfamily; induction Hfamily as [u Hseed|u be u' Hfamily IH Hedge Htranslate].
  - exists u; auto.
  - destruct IH as [seed [Hseed [Hshape Harity]]]; exists seed; split; [exact Hseed|].
    pose proof (pre_expr_translation_shape EV a Hlaw be u u' Hfamily Htranslate) as Hstep.
    split; [congruence|].
    rewrite (pre_expr_shape_arity EV a Hlaw u' u).
    + exact Harity.
    + eapply pre_family_translate; eassumption.
    + exact Hfamily.
    + exact Hstep.
Qed.

Local Lemma pre_family_signature {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) u :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In (pre_expression_shape a u, pre_operands a u) (pre_signatures a).
Proof.
  intros Hlaw Hfamily.
  destruct (pre_family_seed_shape EV a Hlaw u Hfamily) as [seed [Hseed [Hshape Harity]]].
  unfold pre_signatures; apply in_flat_map; exists seed; split; [exact Hseed|].
  apply in_map_iff; exists (pre_operands a u); split; [congruence|].
  rewrite <- Harity; apply pre_operand_tuples_exact.
  apply (pre_expr_finite_operands EV a Hlaw u Hfamily).
Qed.

Local Lemma pre_signatures_length {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) :
  N.of_nat (length (pre_signatures a)) = pre_family_bound a.
Proof.
  unfold pre_signatures, pre_family_bound.
  induction (pre_seed_expressions a) as [|seed seeds IH]; [reflexivity|].
  cbn [flat_map fold_right]; rewrite length_app, length_map, pre_operand_tuples_length.
  rewrite Nat2N.inj_add, Nat2N.inj_pow, IH; reflexivity.
Qed.

Local Lemma pre_family_cardinal {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) (xs : list U) :
  pre_expr_ssa_laws EV a -> NoDup xs -> Forall (pre_expr_in_family a) xs ->
  (N.of_nat (length xs) <= pre_family_bound a)%N.
Proof.
  intros Hlaw Hnodup Hfamily.
  set (signature := fun u => (pre_expression_shape a u, pre_operands a u)).
  assert (Hinject : forall u v, In u xs -> In v xs -> signature u = signature v -> u = v).
  { intros u v Hu Hv Heq; inversion Heq as [[Hshape Hoperands]].
    apply (pre_expr_shape_identity EV a Hlaw u v).
    - exact (proj1 (Forall_forall _ _) Hfamily u Hu).
    - exact (proj1 (Forall_forall _ _) Hfamily v Hv).
    - exact Hshape.
    - exact Hoperands. }
  assert (Hmap : NoDup (map signature xs)).
  { clear Hfamily; induction Hnodup as [|u xs Hfresh Hnodup IH]; [constructor|].
    cbn; constructor.
    - intro Hin; apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; apply Hfresh.
      assert (u = v) by (apply Hinject; [left; reflexivity|right; exact Hv|symmetry; exact Heq]).
      subst u; exact Hv.
    - apply IH; intros u' v Hu Hv; apply Hinject; right; assumption. }
  rewrite <- (pre_signatures_length a).
  apply (proj1 (N.compare_le_iff _ _)); rewrite <- Nat2N.inj_compare.
  apply (proj2 (Nat.compare_le_iff _ _)).
  rewrite <- (length_map signature xs).
  apply NoDup_incl_length; [exact Hmap|].
  intros pair Hin; apply in_map_iff in Hin; destruct Hin as [u [Heq Hu]]; subst pair.
  apply (pre_family_signature EV a u Hlaw).
  exact (proj1 (Forall_forall _ _) Hfamily u Hu).
Qed.

Local Definition pre_discover_valid {X} (EX : encoding X) (P : X -> Prop)
    (work : list X * FinSet.t X) : Prop :=
  FinSet.wf EX (snd work) /\ Forall P (FinSet.elements (snd work)) /\ Forall P (fst work).

Local Lemma pre_discover_valid_step {X} (EX : encoding X) (P : X -> Prop) next work :
  (forall x y, P x -> In y (next x) -> P y) ->
  pre_discover_valid EX P work -> pre_discover_valid EX P (pre_discover_step EX next work).
Proof.
  intros Hnext Hvalid; destruct work as [[|x rest] seen]; [exact Hvalid|].
  destruct Hvalid as [Hwf [Hseen Hpending]].
  pose proof (Forall_inv Hpending) as Hx.
  pose proof (Forall_inv_tail Hpending) as Hrest.
  unfold pre_discover_step; cbn [fst snd].
  destruct (FinSet.mem EX x seen) eqn:Hmem.
  - split; [exact Hwf|split; assumption].
  - split; [apply Map.wf_set; exact Hwf|]; split.
    + apply Forall_forall; intros y Hy; apply (FinSet.elements_spec EX) in Hy;
        [|apply Map.wf_set; exact Hwf].
      apply FinSet.mem_add in Hy; destruct Hy as [Heq|Hy]; [subst y; exact Hx|].
      apply (proj1 (Forall_forall _ _) Hseen y); apply (FinSet.elements_spec EX); assumption.
    + apply Forall_app; split; [apply Forall_forall; intros y Hy; eapply Hnext; eassumption|].
      exact Hrest.
Qed.

Local Definition pre_discover_measure {X} (capacity degree : nat)
    (work : list X * FinSet.t X) : nat :=
  (capacity - FinSet.size (snd work)) * (degree + 1) + length (fst work).

Local Lemma pre_discover_measure_step {X} (EX : encoding X) (P : X -> Prop) next
    capacity degree work :
  (forall xs, NoDup xs -> Forall P xs -> length xs <= capacity) ->
  (forall x, length (next x) <= degree) ->
  (forall x y, P x -> In y (next x) -> P y) ->
  pre_discover_valid EX P work -> fst work <> [] ->
  pre_discover_measure capacity degree (pre_discover_step EX next work) <
    pre_discover_measure capacity degree work.
Proof.
  intros Hcard Hdegree Hnext Hvalid Hnonempty.
  destruct work as [[|x rest] seen]; [contradiction|].
  destruct Hvalid as [Hwf [Hseen Hpending]].
  unfold pre_discover_step; cbn [fst snd]; destruct (FinSet.mem EX x seen) eqn:Hmem.
  - unfold pre_discover_measure; cbn [fst snd length]; lia.
  - assert (Hnewwf : FinSet.wf EX (FinSet.add EX x seen)) by (apply Map.wf_set; exact Hwf).
    assert (Hnewfamily : Forall P (FinSet.elements (FinSet.add EX x seen))).
    { pose proof (pre_discover_valid_step EX P next (x :: rest, seen) Hnext) as Hstep.
      specialize (Hstep (conj Hwf (conj Hseen Hpending))).
      unfold pre_discover_step in Hstep; rewrite Hmem in Hstep; exact (proj1 (proj2 Hstep)). }
    assert (Hnewbound : FinSet.size (FinSet.add EX x seen) <= capacity).
    { rewrite FinSet.size_elements; apply Hcard;
        [apply (FinSet.elements_nodup EX); exact Hnewwf|exact Hnewfamily]. }
    assert (Hgrow : FinSet.size seen < FinSet.size (FinSet.add EX x seen)).
    { apply (FinSet.size_lt EX); try assumption.
      - apply (FinSet.subset_spec EX); [exact Hwf|].
        intros y Hy; apply FinSet.mem_add; right; exact Hy.
      - destruct (FinSet.subset EX (FinSet.add EX x seen) seen) eqn:Hsubset;
          [|reflexivity].
        pose proof (proj1 (FinSet.subset_spec EX (FinSet.add EX x seen) seen Hnewwf)
          Hsubset x (proj2 (FinSet.mem_add EX x x seen) (or_introl eq_refl))) as Hinclude.
        congruence. }
    pose proof (Hdegree x) as Hlength.
    unfold pre_discover_measure; cbn [fst snd]; rewrite length_app; cbn [length]; nia.
Qed.

Local Lemma pre_discover_empty_iter {X} (EX : encoding X) next seen fuel :
  Pos.iter (pre_discover_step EX next) ([], seen) fuel = ([], seen).
Proof.
  induction fuel using Pos.peano_ind; [reflexivity|].
  rewrite Pos.iter_succ, IHfuel; reflexivity.
Qed.

Local Lemma pre_discover_run_agrees {X} (EX : encoding X) next fuel work :
  pre_discover_run EX next fuel work = Pos.iter (pre_discover_step EX next) work fuel.
Proof.
  revert work; induction fuel as [p IH|p IH|]; intros [[|x rest] seen].
  - symmetry; apply pre_discover_empty_iter.
  - cbn [pre_discover_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO p)).
  - symmetry; apply pre_discover_empty_iter.
  - cbn [pre_discover_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Local Lemma pre_discover_iter_bound {X} (EX : encoding X) (P : X -> Prop) next
    capacity degree fuel work :
  (forall xs, NoDup xs -> Forall P xs -> length xs <= capacity) ->
  (forall x, length (next x) <= degree) ->
  (forall x y, P x -> In y (next x) -> P y) ->
  pre_discover_valid EX P work ->
  let result := Pos.iter (pre_discover_step EX next) work fuel in
  pre_discover_valid EX P result /\
    (fst result = [] \/ pre_discover_measure capacity degree result + Pos.to_nat fuel <=
      pre_discover_measure capacity degree work).
Proof.
  intros Hcard Hdegree Hnext; induction fuel using Pos.peano_ind; intro Hvalid.
  - cbn [Pos.iter]; split; [apply pre_discover_valid_step; assumption|].
    destruct (fst work) as [|x rest] eqn:Hpending.
    + destruct work as [pending seen]; cbn in Hpending; subst pending; left; reflexivity.
    + right; assert (Hnonempty : fst work <> []) by congruence.
      pose proof (pre_discover_measure_step EX P next capacity degree work
        Hcard Hdegree Hnext Hvalid Hnonempty) as Hdecrease; cbn [Pos.to_nat]; lia.
  - rewrite Pos.iter_succ; specialize (IHfuel Hvalid).
    destruct IHfuel as [Hmid [Hempty|Hbound]].
    + destruct (Pos.iter (pre_discover_step EX next) work fuel) as [pending seen] eqn:Hmidwork.
      cbn in Hempty; subst pending; split; [exact Hmid|left; reflexivity].
    + split; [apply pre_discover_valid_step; assumption|].
      destruct (fst (Pos.iter (pre_discover_step EX next) work fuel)) as [|x rest] eqn:Hpending.
      * destruct (Pos.iter (pre_discover_step EX next) work fuel) as [pending seen].
        cbn in Hpending; subst pending; left; reflexivity.
      * right; assert (Hnonempty : fst
          (Pos.iter (pre_discover_step EX next) work fuel) <> []) by congruence.
        pose proof (pre_discover_measure_step EX P next capacity degree
          (Pos.iter (pre_discover_step EX next) work fuel)
          Hcard Hdegree Hnext Hmid Hnonempty) as Hdecrease.
        rewrite Pos2Nat.inj_succ; lia.
Qed.

Local Definition pre_discover_available {X} (EX : encoding X)
    (work : list X * FinSet.t X) (x : X) : Prop :=
  FinSet.mem EX x (snd work) = true \/ In x (fst work).

Local Lemma pre_discover_available_step {X} (EX : encoding X) next work x :
  pre_discover_available EX work x ->
  pre_discover_available EX (pre_discover_step EX next work) x.
Proof.
  destruct work as [[|y rest] seen]; [exact (fun H => H)|].
  unfold pre_discover_available, pre_discover_step; cbn [fst snd].
  destruct (FinSet.mem EX y seen) eqn:Hseen.
  - intros [Hmem|[Heq|Hin]]; [left; exact Hmem|subst x; left; exact Hseen|right; exact Hin].
  - intros [Hmem|[Heq|Hin]].
    + left; apply FinSet.mem_add; right; exact Hmem.
    + subst x; left; apply FinSet.mem_add; left; reflexivity.
    + right; apply in_or_app; right; exact Hin.
Qed.

Local Definition pre_discover_covers {X} (EX : encoding X) next (seeds : list X)
    (work : list X * FinSet.t X) : Prop :=
  (forall x, In x seeds -> pre_discover_available EX work x) /\
  (forall x y, FinSet.mem EX x (snd work) = true -> In y (next x) ->
    pre_discover_available EX work y).

Local Lemma pre_discover_covers_step {X} (EX : encoding X) next seeds work :
  pre_discover_covers EX next seeds work ->
  pre_discover_covers EX next seeds (pre_discover_step EX next work).
Proof.
  intros [Hseeds Hclosure]; split.
  - intros x Hin; apply pre_discover_available_step; apply Hseeds; exact Hin.
  - destruct work as [[|x rest] seen]; [exact Hclosure|].
    unfold pre_discover_step; cbn [fst snd]; destruct (FinSet.mem EX x seen) eqn:Hseen.
    + intros y z Hy Hz.
      pose proof (pre_discover_available_step EX next (x :: rest, seen) z
        (Hclosure y z Hy Hz)) as Hkeep.
      unfold pre_discover_step in Hkeep; rewrite Hseen in Hkeep; exact Hkeep.
    + intros y z Hy Hz; apply FinSet.mem_add in Hy; destruct Hy as [Heq|Hy].
      * subst y; right; apply in_or_app; left; exact Hz.
      * change (pre_discover_available EX (next x ++ rest, FinSet.add EX x seen) z).
        pose proof (pre_discover_available_step EX next (x :: rest, seen) z
          (Hclosure y z Hy Hz)) as Hkeep.
        unfold pre_discover_step in Hkeep; rewrite Hseen in Hkeep; exact Hkeep.
Qed.

Local Lemma pre_discover_covers_iter {X} (EX : encoding X) next seeds fuel work :
  pre_discover_covers EX next seeds work ->
  pre_discover_covers EX next seeds (Pos.iter (pre_discover_step EX next) work fuel).
Proof.
  intro Hcovers; induction fuel using Pos.peano_ind.
  - apply pre_discover_covers_step; exact Hcovers.
  - rewrite Pos.iter_succ; apply pre_discover_covers_step; exact IHfuel.
Qed.

Local Lemma pre_translated_spec {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) bes u v :
  In v (pre_translated a bes u) <->
    exists be, In be bes /\ pre_phi_translate a be u = Some v.
Proof.
  unfold pre_translated; rewrite in_flat_map; split.
  - intros [be [Hin Hv]]; destruct (pre_phi_translate a be u) as [w|] eqn:Htranslate;
      cbn in Hv; [|contradiction].
    destruct Hv as [Heq|Hfalse]; [subst w; exists be; auto|contradiction].
  - intros [be [Hin Htranslate]]; exists be; split; [exact Hin|].
    rewrite Htranslate; left; reflexivity.
Qed.

Local Lemma pre_translated_length {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) bes u :
  length (pre_translated a bes u) <= length bes.
Proof.
  unfold pre_translated; induction bes as [|be bes IH]; [reflexivity|].
  cbn [flat_map]; rewrite length_app.
  destruct (pre_phi_translate a be u); cbn [length]; lia.
Qed.

Local Lemma pre_binary_succ_nat (n : BinNums.N) :
  Pos.to_nat (N.succ_pos n) = S (N.to_nat n).
Proof.
  destruct n as [|p]; [reflexivity|]; cbn; rewrite Pos2Nat.inj_succ; reflexivity.
Qed.

Local Lemma pre_family_discovery_parameters {S O B BE N E V K C U}
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) bes :
  pre_expr_ssa_laws EV a -> incl bes (edges_of (block_graph (pre_ssa_points a))) ->
  (forall u v, pre_expr_in_family a u -> In v (pre_translated a bes u) ->
    pre_expr_in_family a v) /\
  (forall xs, NoDup xs -> Forall (pre_expr_in_family a) xs ->
    length xs <= N.to_nat (pre_family_bound a)) /\
  pre_discover_valid EU (pre_expr_in_family a) (pre_seed_expressions a, FinSet.empty).
Proof.
  intros Hlaw Hbes; split.
  - intros u v Hu Hv; apply pre_translated_spec in Hv; destruct Hv as [be [Hbe Htranslate]].
    eapply pre_family_translate; [exact Hu|apply Hbes; exact Hbe|exact Htranslate].
  - split.
    + intros xs Hnodup Hfamily; apply Nat.compare_le_iff.
      rewrite <- (Nat2N.id (length xs)) at 1; rewrite <- N2Nat.inj_compare.
      apply N.compare_le_iff; apply (pre_family_cardinal EV a xs Hlaw Hnodup Hfamily).
    + split; [apply Map.wf_empty|]; split; apply Forall_forall.
      * intros u Hu; apply (FinSet.elements_spec EU) in Hu;
        [cbn [snd] in Hu; rewrite FinSet.mem_empty in Hu; discriminate|apply Map.wf_empty].
      * intros u Hu; apply pre_family_seed; exact Hu.
Qed.

Local Lemma pre_family_discovery_finished {S O B BE N E V K C U}
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) bes :
  pre_expr_ssa_laws EV a -> incl bes (edges_of (block_graph (pre_ssa_points a))) ->
  let bound := (N.of_nat (length (pre_seed_expressions a)) +
    pre_family_bound a * (1 + N.of_nat (length bes)))%N in
  let result := Pos.iter (pre_discover_step EU (pre_translated a bes))
    (pre_seed_expressions a, FinSet.empty) (N.succ_pos bound) in
  pre_discover_valid EU (pre_expr_in_family a) result /\ fst result = [].
Proof.
  intros Hlaw Hbes.
  destruct (pre_family_discovery_parameters EV EU a bes Hlaw Hbes)
    as [Hnext [Hcard Hinitial]].
  set (bound := (N.of_nat (length (pre_seed_expressions a)) +
    pre_family_bound a * (1 + N.of_nat (length bes)))%N).
  destruct (pre_discover_iter_bound EU (pre_expr_in_family a) (pre_translated a bes)
    (N.to_nat (pre_family_bound a)) (length bes) (N.succ_pos bound)
    (pre_seed_expressions a, FinSet.empty) Hcard
    (pre_translated_length a bes) Hnext Hinitial) as [Hvalid Hfinished].
  split; [exact Hvalid|]; destruct Hfinished as [Hdone|Hbound]; [exact Hdone|].
  rewrite pre_binary_succ_nat in Hbound.
  unfold pre_discover_measure in Hbound; cbn [fst snd] in Hbound.
  change (FinSet.size (@FinSet.empty U)) with 0 in Hbound.
  unfold bound in Hbound; rewrite N2Nat.inj_add, N2Nat.inj_mul, N2Nat.inj_add,
    !Nat2N.id in Hbound.
  change (Pos.to_nat 1%positive) with 1 in Hbound; nia.
Qed.

(** Discovery terminates before exhausting its shape/operand bound and computes the least family. *)
Theorem pre_expr_universe_exact {S O B BE N E V K C U} (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  NoDup (pre_expr_universe EBE EV EU a) /\
  forall u, In u (pre_expr_universe EBE EV EU a) <-> pre_expr_in_family a u.
Proof.
  intro Hlaw; set (bes := FinSet.elements
    (FinSet.of_list EBE (edges_of (block_graph (pre_ssa_points a))))).
  assert (Hbes : forall be, In be bes <-> In be (edges_of (block_graph (pre_ssa_points a)))).
  { intro be; unfold bes; rewrite FinSet.elements_spec, FinSet.of_list_spec;
      [reflexivity|apply FinSet.wf_fold_add; apply Map.wf_empty]. }
  set (next := pre_translated a bes).
  set (bound := (N.of_nat (length (pre_seed_expressions a)) +
    pre_family_bound a * (1 + N.of_nat (length bes)))%N).
  set (result := Pos.iter (pre_discover_step EU next)
    (pre_seed_expressions a, FinSet.empty) (N.succ_pos bound)).
  destruct (pre_family_discovery_finished EV EU a bes Hlaw
    (fun be Hbe => proj1 (Hbes be) Hbe)) as [Hvalid Hdone].
  change (pre_discover_valid EU (pre_expr_in_family a) result) in Hvalid.
  change (fst result = []) in Hdone.
  assert (Hcovers : pre_discover_covers EU next (pre_seed_expressions a) result).
  { apply pre_discover_covers_iter; split.
    - intros u Hu; right; exact Hu.
    - intros u v Hfalse; cbn [snd] in Hfalse.
      rewrite FinSet.mem_empty in Hfalse; discriminate. }
  assert (Havailable : forall u, pre_discover_available EU result u ->
    FinSet.mem EU u (snd result) = true).
  { intros u [Hu|Hu]; [exact Hu|rewrite Hdone in Hu; contradiction]. }
  assert (Hcomplete : forall u, pre_expr_in_family a u ->
    FinSet.mem EU u (snd result) = true).
  { intros u Hfamily; induction Hfamily as [u Hseed|u be v Hu IH Hbe Htranslate].
    - apply Havailable; apply (proj1 Hcovers); exact Hseed.
    - apply Havailable; apply (proj2 Hcovers u v IH); apply pre_translated_spec.
      exists be; split; [apply Hbes; exact Hbe|exact Htranslate]. }
  assert (Heq : pre_expr_universe EBE EV EU a = FinSet.elements (snd result)).
  { unfold pre_expr_universe; rewrite pre_discover_run_agrees; reflexivity. }
  rewrite Heq; destruct Hvalid as [Hwf [Hfamily Hpending]]; split.
  - apply (FinSet.elements_nodup EU); exact Hwf.
  - intro u; split.
    + intro Hu; exact (proj1 (Forall_forall _ _) Hfamily u Hu).
    + intro Hu; apply (FinSet.elements_spec EU); [exact Hwf|apply Hcomplete; exact Hu].
Qed.

(** * Expression definition seeds *)

Local Definition pre_group_add {X Y} (EX : encoding X) (EY : encoding Y)
    (index : Map.t X (FinSet.t Y)) (key : X * Y) : Map.t X (FinSet.t Y) :=
  let '(x, y) := key in
  let old := match Map.get EX x index with
  | Some values => values
  | None => FinSet.empty
  end in
  Map.set EX x (FinSet.add EY y old) index.

Local Definition pre_group_lookup {X Y} (EX : encoding X)
    (index : Map.t X (FinSet.t Y)) (x : X) : FinSet.t Y :=
  match Map.get EX x index with
  | Some values => values
  | None => FinSet.empty
  end.

Local Definition pre_occurrence_blocks {S O B BE N E V K C U}
    (EB : encoding B) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
    Map.t U (FinSet.t B) :=
  fold_left (pre_group_add EU EB)
    (flat_map (fun e => match pre_recomputed (pre_expression a) e with
    | Some u =>
      if pre_total_pure (pre_expression a) u then [(u, block_of_point (pre_ssa_points a)
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e))] else []
    | None => []
    end) (edges_of (live_graph (point_model (pre_ssa_points a))))) Map.empty.

(** Definition seeds include entry, eligible real occurrences and every operand's home. *)
Definition frg_defs {S O B BE N E V K C U} (EB : encoding B) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : U -> list B :=
  let occurrences := pre_occurrence_blocks EB EU a in
  let entry := FinSet.of_list EB (Graph.entries (block_graph (pre_ssa_points a))) in
  fun u =>
    let real := match Map.get EU u occurrences with
    | Some blocks => blocks
    | None => FinSet.empty
    end in
    FinSet.elements (FinSet.union EB real (FinSet.union EB entry
      (FinSet.of_list EB (map (home (pre_ssa_view a)) (pre_operands a u))))).

(** Phi sites form the least frontier closure, including recursively translated operands. *)
Inductive frg_phi_needed {S O B BE N E V K C U} (EB : encoding B) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : U -> B -> Prop :=
  | frg_phi_operand_param : forall u b x, pre_expr_in_family a u ->
      In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
      ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
      In x (pre_operands a u) -> In x (block_params (pre_ssa_points a) b) ->
      frg_phi_needed EB EU a u b
  | frg_phi_seed : forall u d b, pre_expr_in_family a u -> In d (frg_defs EB EU a u) ->
      in_df (block_graph (pre_ssa_points a)) d b -> frg_phi_needed EB EU a u b
  | frg_phi_iter : forall u d b, frg_phi_needed EB EU a u d ->
      in_df (block_graph (pre_ssa_points a)) d b -> frg_phi_needed EB EU a u b
  | frg_phi_translate_seed : forall u b be u' b', frg_phi_needed EB EU a u b ->
      In be (edges_of (block_graph (pre_ssa_points a))) ->
      Graph.target (block_graph (pre_ssa_points a)) be = b ->
      pre_phi_translate a be u = Some u' ->
      in_df (block_graph (pre_ssa_points a))
        (Graph.source (block_graph (pre_ssa_points a)) be) b' ->
      frg_phi_needed EB EU a u' b'.

Local Lemma frg_phi_needed_family {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u b :
  frg_phi_needed EB EU a u b -> pre_expr_in_family a u.
Proof.
  intro Hneeded; induction Hneeded as
    [u b x Hfamily Hb Hentry Hoperand Hparam|
     u d b Hfamily Hdef Hfrontier|u d b Hneeded IH Hfrontier|
     u b be u' b' Hneeded IH Hedge Htarget Htranslate Hfrontier].
  - exact Hfamily.
  - exact Hfamily.
  - exact IH.
  - eapply pre_family_translate; eassumption.
Qed.

(** * Indexed cross-translation frontier closure *)

Local Definition pre_phi_next {S O B BE N E V K C U} (EB : encoding B) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a)))
    (df : Map.t B (FinSet.t B)) (key : U * B) : list (U * B) :=
  let '(u, b) := key in
  FinSet.elements (FinSet.of_list (pair_encoding EU EB)
    (map (fun c => (u, c)) (frontier_successors EB df b) ++
      flat_map (fun be => match pre_phi_translate a be u with
        | Some v => map (fun c => (v, c))
            (frontier_successors EB df (Graph.source (block_graph (pre_ssa_points a)) be))
        | None => []
        end) (pred_edges p b))).

(* This index traverses listed nonentry parameters once, independently of the family. *)
Local Definition pre_parameter_blocks {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) : Map.t V (FinSet.t B) :=
  let s := pre_ssa_points a in
  let entries := FinSet.of_list EB (Graph.entries (block_graph s)) in
  fold_left (pre_group_add EV EB)
    (flat_map (fun b => if FinSet.mem EB b entries then []
      else map (fun x => (x, b)) (block_params s b)) (Graph.nodes (block_graph s))) Map.empty.

Local Definition pre_phi_direct {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (family : list U) : list (U * B) :=
  let parameters := pre_parameter_blocks EB EV a in
  FinSet.elements (FinSet.of_list (pair_encoding EU EB)
    (flat_map (fun u => flat_map (fun x => map (fun b => (u, b))
      (FinSet.elements (pre_group_lookup EV parameters x))) (pre_operands a u)) family)).

Local Definition pre_phi_starts {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (family : list U) (df : Map.t B (FinSet.t B)) : list (U * B) :=
  let definitions := frg_defs EB EU a in
  pre_phi_direct EB EV EU a family ++
  flat_map (fun u => flat_map (fun d => map (fun b => (u, b))
    (frontier_successors EB df d)) (definitions u)) family.

Local Definition pre_phi_graph_from {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a))) (df : Map.t B (FinSet.t B))
    (family : list U) : Graph.t (U * B) ((U * B) * (U * B)) :=
  {| Graph.entries := pre_phi_starts EB EV EU a family df;
     Graph.nodes := list_prod family (Graph.nodes (block_graph (pre_ssa_points a)));
     Graph.out := fun key => map (fun next => (key, next)) (pre_phi_next EB EU a p df key);
     Graph.source := fst;
     Graph.target := snd |}.

Local Definition pre_phi_graph {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : Graph.t (U * B) ((U * B) * (U * B)) :=
  let p := prepare EB (block_graph (pre_ssa_points a)) in
  pre_phi_graph_from EB EV EU a p (dominance_frontier p (dominator_tree p))
    (pre_expr_universe EBE EV EU a).

Local Definition pre_phi_sites_graph {B U} (EB : encoding B) (EU : encoding U)
    (graph : Graph.t (U * B) ((U * B) * (U * B))) : U -> FinSet.t B :=
  let p := prepare (pair_encoding EU EB) graph in
  let sites := preorder (dfs p FinSet.empty (Graph.entries graph)) in
  let index := fold_left (pre_group_add EU EB) sites Map.empty in
  pre_group_lookup EU index.

(** A single indexed product-graph traversal computes every expression's phi sites. *)
Definition frg_phi_sites {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
    U -> FinSet.t B := pre_phi_sites_graph EB EU (pre_phi_graph EB EBE EV EU a).

Local Lemma pre_group_add_exact {X Y} (EX : encoding X) (EY : encoding Y)
    index x y key :
  FinSet.mem EY y (pre_group_lookup EX (pre_group_add EX EY index key) x) = true <->
    key = (x, y) \/ FinSet.mem EY y (pre_group_lookup EX index x) = true.
Proof.
  destruct key as [a b]; unfold pre_group_add, pre_group_lookup.
  destruct (dfs_eq_dec EX x a) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same, FinSet.mem_add.
    destruct (Map.get EX x index) as [old|]; cbn; intuition congruence.
  - rewrite Map.get_set_other by exact Hne; intuition congruence.
Qed.

Local Lemma pre_group_fold_exact {X Y} (EX : encoding X) (EY : encoding Y)
    keys index x y :
  FinSet.mem EY y (pre_group_lookup EX
    (fold_left (pre_group_add EX EY) keys index) x) = true <->
  In (x, y) keys \/ FinSet.mem EY y (pre_group_lookup EX index x) = true.
Proof.
  revert index; induction keys as [|key keys IH]; intro index; cbn [fold_left In].
  - tauto.
  - rewrite IH, pre_group_add_exact; tauto.
Qed.

Local Lemma pre_group_fold_wf {X Y} (EX : encoding X) (EY : encoding Y) keys index :
  (forall x, FinSet.wf EY (pre_group_lookup EX index x)) ->
  forall x, FinSet.wf EY (pre_group_lookup EX
    (fold_left (pre_group_add EX EY) keys index) x).
Proof.
  revert index; induction keys as [|[a b] keys IH]; intros index Hwf x; [apply Hwf|].
  cbn [fold_left]; apply IH; intro y.
  unfold pre_group_add, pre_group_lookup.
  destruct (dfs_eq_dec EX y a) as [Heq|Hne].
  - subst y; rewrite Map.get_set_same.
    apply Map.wf_set; apply (Hwf a).
  - rewrite Map.get_set_other by exact Hne; apply Hwf.
Qed.

Local Lemma pre_parameter_blocks_exact {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) x b :
  In b (FinSet.elements (pre_group_lookup EV (pre_parameter_blocks EB EV a) x)) <->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))) /\
    In x (block_params (pre_ssa_points a) b).
Proof.
  unfold pre_parameter_blocks.
  rewrite (FinSet.elements_spec EB).
  2: { apply pre_group_fold_wf; intro y; unfold pre_group_lookup.
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact.
  unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite in_flat_map; split.
  - intros [[c [Hc Hin]]|Hfalse]; [|discriminate].
    destruct (FinSet.mem EB c
      (FinSet.of_list EB (Graph.entries (block_graph (pre_ssa_points a))))) eqn:Hentry;
      [contradiction|].
    apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]]; inversion Heq; subst c y.
    split; [exact Hc|]; split; [|exact Hy].
    intro Hin; apply (proj2 (FinSet.of_list_spec EB _ _)) in Hin; congruence.
  - intros [Hb [Hentry Hparam]]; left; exists b; split; [exact Hb|].
    destruct (FinSet.mem EB b
      (FinSet.of_list EB (Graph.entries (block_graph (pre_ssa_points a))))) eqn:Hmem.
    + apply FinSet.of_list_spec in Hmem; contradiction.
    + apply in_map_iff; exists x; auto.
Qed.

Local Lemma pre_phi_direct_exact {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    family u b :
  In (u, b) (pre_phi_direct EB EV EU a family) <->
  In u family /\ In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
    ~ In b (Graph.entries (block_graph (pre_ssa_points a))) /\
    exists x, In x (pre_operands a u) /\ In x (block_params (pre_ssa_points a) b).
Proof.
  unfold pre_phi_direct; rewrite FinSet.elements_spec;
    [|apply FinSet.wf_fold_add; apply Map.wf_empty].
  rewrite FinSet.of_list_spec, in_flat_map; split.
  - intros [v [Hv Hin]]; apply in_flat_map in Hin; destruct Hin as [x [Hx Hin]].
    apply in_map_iff in Hin; destruct Hin as [c [Heq Hc]]; inversion Heq; subst v c.
    apply pre_parameter_blocks_exact in Hc; destruct Hc as [Hb [Hentry Hparam]].
    split; [exact Hv|]; split; [exact Hb|]; split; [exact Hentry|exists x; auto].
  - intros [Hu [Hb [Hentry [x [Hx Hparam]]]]]; exists u; split; [exact Hu|].
    apply in_flat_map; exists x; split; [exact Hx|].
    apply in_map_iff; exists b; split; [reflexivity|].
    apply pre_parameter_blocks_exact; auto.
Qed.

Local Lemma pre_pred_edges_exact {B BE} (EB : encoding B) (g : Graph.t B BE)
    (p : prepared EB g) b be : ready EB g p -> In b (Graph.nodes g) ->
  (In be (pred_edges p b) <-> In be (edges_of g) /\ Graph.target g be = b).
Proof.
  intros Hready Hb; rewrite (pred_agrees (proj2 (proj2 Hready)) b be Hb).
  split.
  - intros [source [Hsource [Hedge Htarget]]]; split; [|exact Htarget].
    apply in_flat_map; exists source; auto.
  - intros [Hedge Htarget]; apply in_flat_map in Hedge.
    destruct Hedge as [source [Hsource Hedge]]; exists source; auto.
Qed.

Local Lemma pre_frontier_exact {B BE} (EB : encoding B) (g : Graph.t B BE)
    (p : prepared EB g) d b : ready EB g p ->
  (In b (frontier_successors EB (dominance_frontier p (dominator_tree p)) d) <->
    in_df g d b).
Proof.
  intro Hready; rewrite frontier_successors_spec by apply dominance_frontier_wf.
  apply dominance_frontier_exact; [exact Hready|apply dominator_exact_true; exact Hready].
Qed.

Local Lemma pre_phi_next_exact {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a))) u b v c :
  ready EB (block_graph (pre_ssa_points a)) p ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  (In (v, c) (pre_phi_next EB EU a p (dominance_frontier p (dominator_tree p)) (u, b)) <->
    (v = u /\ in_df (block_graph (pre_ssa_points a)) b c) \/
    exists be, In be (edges_of (block_graph (pre_ssa_points a))) /\
      Graph.target (block_graph (pre_ssa_points a)) be = b /\
      pre_phi_translate a be u = Some v /\
      in_df (block_graph (pre_ssa_points a))
        (Graph.source (block_graph (pre_ssa_points a)) be) c).
Proof.
  intros Hready Hb; unfold pre_phi_next; rewrite FinSet.elements_spec;
    [|apply FinSet.wf_fold_add; apply Map.wf_empty].
  rewrite FinSet.of_list_spec, in_app_iff, in_flat_map; split.
  - intros [Hin|[be [Hbe Hin]]].
    + apply in_map_iff in Hin; destruct Hin as [d [Heq Hin]]; inversion Heq; subst d v.
      left; split; [reflexivity|apply (pre_frontier_exact EB _ p); assumption].
    + apply (pre_pred_edges_exact EB _ p b be Hready Hb) in Hbe.
      destruct (pre_phi_translate a be u) as [w|] eqn:Htranslate; [|contradiction].
      apply in_map_iff in Hin; destruct Hin as [d [Heq Hin]]; inversion Heq; subst d w.
      right; exists be; split; [exact (proj1 Hbe)|]; split; [exact (proj2 Hbe)|].
      split; [exact Htranslate|apply (pre_frontier_exact EB _ p); assumption].
  - intros [[Heq Hdf]|[be [Hbe [Htarget [Htranslate Hdf]]]]].
    + subst v; left; apply in_map_iff; exists c; split; [reflexivity|].
      apply (pre_frontier_exact EB _ p); assumption.
    + right; exists be; split.
      * apply (pre_pred_edges_exact EB _ p b be Hready Hb); auto.
      * rewrite Htranslate; apply in_map_iff; exists c; split; [reflexivity|].
        apply (pre_frontier_exact EB _ p); assumption.
Qed.

Local Lemma pre_phi_starts_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u b :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  (In (u, b) (Graph.entries (pre_phi_graph EB EBE EV EU a)) <->
    pre_expr_in_family a u /\
      ((In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
        ~ In b (Graph.entries (block_graph (pre_ssa_points a))) /\
        exists x, In x (pre_operands a u) /\ In x (block_params (pre_ssa_points a) b)) \/
       exists d, In d (frg_defs EB EU a u) /\
         in_df (block_graph (pre_ssa_points a)) d b)).
Proof.
  intros Hlaw Hready; unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.entries].
  unfold pre_phi_starts.
  rewrite in_app_iff, pre_phi_direct_exact; split.
  - intros [[Hu Hdirect]|Hfrontier].
    + split; [apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hu|].
      left; exact Hdirect.
    + apply in_flat_map in Hfrontier; destruct Hfrontier as [v [Hv Hin]].
      apply in_flat_map in Hin; destruct Hin as [d [Hd Hin]].
      apply in_map_iff in Hin; destruct Hin as [c [Heq Hc]]; inversion Heq; subst v c.
      split; [apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hv|].
      right; exists d; split; [exact Hd|].
      apply (pre_frontier_exact EB _ (prepare EB (block_graph (pre_ssa_points a)))); assumption.
  - intros [Hu [Hdirect|[d [Hd Hdf]]]].
    + left; split; [|exact Hdirect].
      apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hu.
    + right; apply in_flat_map; exists u; split.
      * apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hu.
      * apply in_flat_map; exists d; split; [exact Hd|].
        apply in_map_iff; exists b; split; [reflexivity|].
        apply (pre_frontier_exact EB _ (prepare EB (block_graph (pre_ssa_points a)))); assumption.
Qed.

Local Lemma frg_phi_needed_nodes {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u b :
  graph_wf (block_graph (pre_ssa_points a)) -> frg_phi_needed EB EU a u b ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))).
Proof.
  intros Hwf Hneeded; destruct Hneeded as
    [u b x Hfamily Hb Hentry Hoperand Hparam|
     u d b Hfamily Hdef Hdf|u d b Hneeded Hdf|
     u b be u' b' Hneeded Hedge Htarget Htranslate Hdf].
  - exact Hb.
  - exact (proj2 (in_df_nodes _ d b Hwf Hdf)).
  - exact (proj2 (in_df_nodes _ d b Hwf Hdf)).
  - exact (proj2 (in_df_nodes _ _ b' Hwf Hdf)).
Qed.

Local Lemma pre_list_prod_nodup {X Y} (xs : list X) (ys : list Y) :
  NoDup xs -> NoDup ys -> NoDup (list_prod xs ys).
Proof.
  intros Hxs Hys; induction Hxs as [|x xs Hfresh Hxs IH]; [constructor|].
  cbn [list_prod]; apply nodup_app_disjoint.
  - apply nodup_map_injective; [intros a b Heq; congruence|exact Hys].
  - exact IH.
  - intros [a b] Hin Htail; apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hy]]; inversion Heq; subst a b.
    apply in_prod_iff in Htail; exact (Hfresh (proj1 Htail)).
Qed.

Local Lemma pre_phi_next_nodes {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a))) u b v c :
  pre_expr_ssa_laws EV a -> ready EB (block_graph (pre_ssa_points a)) p ->
  pre_expr_in_family a u -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In (v, c) (pre_phi_next EB EU a p (dominance_frontier p (dominator_tree p)) (u, b)) ->
  pre_expr_in_family a v /\ In c (Graph.nodes (block_graph (pre_ssa_points a))).
Proof.
  intros Hlaw Hready Hu Hb Hnext.
  apply (pre_phi_next_exact EB EU a p u b v c Hready Hb) in Hnext.
  destruct Hnext as [[Heq Hdf]|[be [Hbe [Htarget [Htranslate Hdf]]]]].
  - subst v; split; [exact Hu|exact (proj2 (in_df_nodes _ b c (proj1 Hready) Hdf))].
  - split.
    + eapply pre_family_translate; eassumption.
    + exact (proj2 (in_df_nodes _ _ c (proj1 Hready) Hdf)).
Qed.

Local Lemma pre_phi_graph_ready {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready (pair_encoding EU EB) (pre_phi_graph EB EBE EV EU a)
    (prepare (pair_encoding EU EB) (pre_phi_graph EB EBE EV EU a)).
Proof.
  intros Hlaw Hready; apply prepare_ready.
  - constructor.
    + unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.nodes]; apply pre_list_prod_nodup.
      * exact (proj1 (pre_expr_universe_exact EBE EV EU a Hlaw)).
      * exact (nodes_nodup (proj1 Hready)).
    + intros [u b] Hin; apply (pre_phi_starts_exact EB EBE EV EU a u b Hlaw Hready) in Hin.
      destruct Hin as [Hu [Hdirect|[d [Hd Hdf]]]].
      * unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.nodes]; apply in_prod.
        -- apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hu.
        -- exact (proj1 Hdirect).
      * unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.nodes]; apply in_prod.
        -- apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hu.
        -- exact (proj2 (in_df_nodes _ d b (proj1 Hready) Hdf)).
    + intros key [from next] Hin; unfold pre_phi_graph, pre_phi_graph_from in Hin.
      cbn [Graph.out] in Hin.
      apply in_map_iff in Hin; destruct Hin as [target [Heq Hin]]; cbn; congruence.
    + intros [u b] [from [v c]] Hnode Hedge.
      unfold pre_phi_graph, pre_phi_graph_from in Hnode, Hedge |- *.
      cbn [Graph.nodes Graph.out Graph.target] in Hnode, Hedge |- *.
      apply in_prod_iff in Hnode.
      destruct Hnode as [Hu Hb]; apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw))
        in Hu.
      apply in_map_iff in Hedge; destruct Hedge as [next [Heq Hnext]].
      inversion Heq; subst from next.
      destruct (pre_phi_next_nodes EB EV EU a _ u b v c Hlaw Hready Hu Hb Hnext)
        as [Hv Hc].
      apply in_prod; [apply (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); exact Hv|].
      exact Hc.
  - intros [u b]; unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.out].
    apply nodup_map_injective.
    + intros x y Heq; congruence.
    + unfold pre_phi_next; apply (FinSet.elements_nodup (pair_encoding EU EB)).
      apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Local Lemma pre_phi_graph_edge {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u b v c :
  In ((u, b), (v, c)) (Graph.out (pre_phi_graph EB EBE EV EU a) (u, b)) <->
  In (v, c) (pre_phi_next EB EU a (prepare EB (block_graph (pre_ssa_points a)))
    (dominance_frontier (prepare EB (block_graph (pre_ssa_points a)))
      (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))) (u, b)).
Proof.
  unfold pre_phi_graph, pre_phi_graph_from; cbn [Graph.out]; rewrite in_map_iff; split.
  - intros [next [Heq Hin]]; inversion Heq; subst next; exact Hin.
  - intro Hin; exists (v, c); auto.
Qed.

Local Lemma pre_phi_graph_reachable {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u b :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  (reachable (pre_phi_graph EB EBE EV EU a) (u, b) <-> frg_phi_needed EB EU a u b).
Proof.
  intros Hlaw Hready; split.
  - assert (Hsound : forall key, reachable (pre_phi_graph EB EBE EV EU a) key ->
      frg_phi_needed EB EU a (fst key) (snd key)).
    { intros key Hreach; induction Hreach as [[v c] Hentry|[[v c] [w d]] Hreach IH Hedge].
      - apply (pre_phi_starts_exact EB EBE EV EU a v c Hlaw Hready) in Hentry.
        destruct Hentry as [Hv [[Hc [Hnonentry [x [Hoperand Hparam]]]]|
          [source [Hsource Hdf]]]].
        + eapply frg_phi_operand_param; eassumption.
        + eapply frg_phi_seed; eassumption.
      - change (frg_phi_needed EB EU a v c) in IH.
        apply pre_phi_graph_edge in Hedge.
        apply (pre_phi_next_exact EB EU a _ v c w d Hready) in Hedge.
        + destruct Hedge as [[Heq Hdf]|[be [Hbe [Htarget [Htranslate Hdf]]]]].
          * subst w; eapply frg_phi_iter; eassumption.
          * eapply frg_phi_translate_seed; eassumption.
        + exact (frg_phi_needed_nodes EB EU a v c (proj1 Hready) IH). }
    exact (Hsound (u, b)).
  - intro Hneeded; induction Hneeded as
      [v c x Hv Hc Hentry Hoperand Hparam|
       v source c Hv Hsource Hdf|v source c Hneeded IH Hdf|
       v c be w d Hneeded IH Hbe Htarget Htranslate Hdf].
    + apply reachable_entry; apply (pre_phi_starts_exact EB EBE EV EU a v c Hlaw Hready).
      split; [exact Hv|left; split; [exact Hc|]; split; [exact Hentry|exists x; auto]].
    + apply reachable_entry; apply (pre_phi_starts_exact EB EBE EV EU a v c Hlaw Hready).
      split; [exact Hv|right; exists source; auto].
    + apply (@reachable_step _ _ (pre_phi_graph EB EBE EV EU a) ((v, source), (v, c))).
      * exact IH.
      * apply pre_phi_graph_edge; apply (pre_phi_next_exact EB EU a _ v source v c Hready).
        -- exact (frg_phi_needed_nodes EB EU a v source (proj1 Hready) Hneeded).
        -- left; auto.
    + apply (@reachable_step _ _ (pre_phi_graph EB EBE EV EU a) ((v, c), (w, d))).
      * exact IH.
      * apply pre_phi_graph_edge; apply (pre_phi_next_exact EB EU a _ v c w d Hready).
        -- exact (frg_phi_needed_nodes EB EU a v c (proj1 Hready) Hneeded).
        -- right; exists be; auto.
Qed.

(** Indexed phi sites are exactly the least cross-translation frontier closure. *)
Theorem frg_phi_sites_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall u b, pre_expr_in_family a u ->
    (FinSet.mem EB b (frg_phi_sites EB EBE EV EU a u) = true <->
      frg_phi_needed EB EU a u b).
Proof.
  intros Hlaw Hready u b Hu; unfold frg_phi_sites, pre_phi_sites_graph.
  rewrite pre_group_fold_exact.
  unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  assert (Hprepared := pre_phi_graph_ready EB EBE EV EU a Hlaw Hready).
  pose proof (dfs_exact (pair_encoding EU EB) (pre_phi_graph EB EBE EV EU a) _
    (u, b) _ FinSet.empty Hprepared (entries_in (proj1 Hprepared))) as Hdfs.
  rewrite (proj2 (proj2 (proj2 Hdfs))), reachable_dfs by exact Hprepared.
  rewrite (pre_phi_graph_reachable EB EBE EV EU a u b Hlaw Hready); intuition discriminate.
Qed.

(** * Expression versions and links *)

(** Unavailable entry values remain distinct from existing initial expression values. *)
Inductive frg_version (B E U : Type) : Type :=
  | FrUnavailable (u : U)
  | FrInitial (u : U)
  | FrFresh (e : E) (u : U)
  | FrPhi (b : B) (u : U).
Arguments FrUnavailable {B E U}.
Arguments FrInitial {B E U}.
Arguments FrFresh {B E U}.
Arguments FrPhi {B E U}.

(** Every incoming link retains whether a real occurrence dominates its edge position. *)
Record frg_operand (B E U : Type) : Type := FrgOperand {
  frg_operand_version : frg_version B E U;
  frg_operand_real_use : bool
}.
Arguments FrgOperand {B E U}.
Arguments frg_operand_version {B E U}.
Arguments frg_operand_real_use {B E U}.

(** The graph indexes real occurrences, phi definitions and individual incoming edge links. *)
Record factored_redundancy_graph (B BE E U : Type) : Type := FactoredRedundancyGraph {
  frg_versions : list (frg_version B E U);
  frg_occurrence_index : Map.t E (frg_version B E U);
  frg_fresh_index : FinSet.t E;
  frg_phi_index : FinSet.t (B * U);
  frg_phi_operands : Map.t ((B * U) * BE) (frg_operand B E U);
  frg_unsafe_seeds : FinSet.t (B * U)
}.
Arguments FactoredRedundancyGraph {B BE E U}.
Arguments frg_versions {B BE E U}.
Arguments frg_occurrence_index {B BE E U}.
Arguments frg_fresh_index {B BE E U}.
Arguments frg_phi_index {B BE E U}.
Arguments frg_phi_operands {B BE E U}.
Arguments frg_unsafe_seeds {B BE E U}.

Local Definition frg_version_key {B E U} (d : frg_version B E U) :
    U + (U + ((E * U) + (B * U))) :=
  match d with
  | FrUnavailable u => inl u
  | FrInitial u => inr (inl u)
  | FrFresh e u => inr (inr (inl (e, u)))
  | FrPhi b u => inr (inr (inr (b, u)))
  end.

(** Constructor tags and exact expression identities give injective version codes. *)
Definition frg_version_encoding {B E U} (EB : encoding B) (EE : encoding E)
    (EU : encoding U) : encoding (frg_version B E U).
Proof.
  set (EK := sum_encoding EU
    (sum_encoding EU (sum_encoding (pair_encoding EE EU) (pair_encoding EB EU)))).
  refine (Encoding _ (fun d => encode EK (frg_version_key d)) _).
  intros x y Heq; apply (encode_injective EK) in Heq.
  destruct x, y; cbn [frg_version_key] in Heq; inversion Heq; reflexivity.
Defined.

(** A version's expression includes all of its typed, ordered operand identities. *)
Definition frg_version_expr {B E U} (d : frg_version B E U) : U :=
  match d with
  | FrUnavailable u => u
  | FrInitial u => u
  | FrFresh _ u => u
  | FrPhi _ u => u
  end.

(** Real definitions occur after their instruction, and phi definitions after parameter binding. *)
Definition frg_version_point {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (d : frg_version B E U) : option N :=
  match d with
  | FrUnavailable _ => None
  | FrInitial _ => nth_error (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0
  | FrFresh e _ => Some (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
  | FrPhi b _ => Some (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b))
  end.

(** The nearest definition is dominated by every other matching definition reaching the point. *)
Definition frg_nearest_version {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (u : U) (n : N) (d : frg_version B E U) : Prop :=
  In d (frg_versions f) /\ frg_version_expr d = u /\
  exists q, frg_version_point a d = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q n /\
    forall d' q', In d' (frg_versions f) -> frg_version_expr d' = u ->
      frg_version_point a d' = Some q' ->
      dominates (live_graph (point_model (pre_ssa_points a))) q' n ->
      dominates (live_graph (point_model (pre_ssa_points a))) q' q.

(** A phi's unused frame has no real occurrence of its version dominating the current point. *)
Definition frg_no_dominating_real_use {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (n : N) (d : frg_version B E U) : Prop :=
  forall e, Map.get EE e (frg_occurrence_index f) = Some d ->
    ~ dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n.

(** A reusable nearest version has no intervening kill before any return to its definition. *)
Definition frg_reusable {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (u : U) (n : N) (d : frg_version B E U) : Prop :=
  frg_nearest_version a f u n d /\
  exists q, frg_version_point a d = Some q /\
    forall es, path (live_graph (point_model (pre_ssa_points a))) q es n ->
      Forall (fun e => Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q) es ->
      Forall (fun e => kill (pre_genkill (pre_expression a)) e u = false) es.

(** The graph contains exactly its eligible definitions and selects reusable nearest versions. *)
Record frg_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) : Prop := {
  frg_versions_nodup : NoDup (frg_versions f);
  frg_versions_exact : forall d, In d (frg_versions f) <->
    match d with
    | FrUnavailable u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true
    | FrInitial u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
        pre_initial_available a u = true
    | FrFresh e u => In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
        pre_recomputed (pre_expression a) e = Some u /\
        FinSet.mem EE e (frg_fresh_index f) = true
    | FrPhi b u => FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index f) = true
    end;
  frg_phi_exact : forall b u,
    FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index f) = true <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
    frg_phi_needed EB EU a u b;
  frg_occurrence_exact : forall e u,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
    exists d, Map.get EE e (frg_occurrence_index f) = Some d /\ In d (frg_versions f) /\
      frg_version_expr d = u /\
      (d = FrFresh e u \/ frg_reusable a f u
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d);
  frg_occurrence_domain : forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    pre_recomputed (pre_expression a) e = Some (frg_version_expr d) /\
    pre_total_pure (pre_expression a) (frg_version_expr d) = true;
  frg_fresh_exact : forall e u, pre_recomputed (pre_expression a) e = Some u ->
    (FinSet.mem EE e (frg_fresh_index f) = true <->
      Map.get EE e (frg_occurrence_index f) = Some (FrFresh e u));
  frg_fresh_domain : forall e, FinSet.mem EE e (frg_fresh_index f) = true ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a))));
  frg_fresh_required : forall e u,
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
    (FinSet.mem EE e (frg_fresh_index f) = true <->
      ~ exists d, frg_reusable a f u
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d);
  frg_operand_exact : forall b u be,
    FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index f) = true ->
    In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.target (block_graph (pre_ssa_points a)) be = b ->
    exists op u', pre_phi_translate a be u = Some u' /\
      Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
        (frg_phi_operands f) = Some op /\
      frg_version_expr (frg_operand_version op) = u' /\
      (frg_operand_version op = FrUnavailable u' \/
       exists n e, frg_version_point a (frg_operand_version op) = Some n /\
         Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some e /\
         dominates (live_graph (point_model (pre_ssa_points a))) n
           (Graph.source (live_graph (point_model (pre_ssa_points a))) e));
  frg_operand_domain : forall b u be op,
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
      (frg_phi_operands f) = Some op ->
    FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index f) = true /\
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.target (block_graph (pre_ssa_points a)) be = b;
  frg_operand_selection : forall b u be op pe u',
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
      (frg_phi_operands f) = Some op ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    pre_phi_translate a be u = Some u' ->
    (frg_operand_version op = FrUnavailable u' <->
      ~ exists d, frg_reusable a f u'
        (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) d) /\
    (frg_operand_version op <> FrUnavailable u' ->
      frg_reusable a f u' (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)
        (frg_operand_version op));
  frg_operand_real_use_exact : forall b u be op pe,
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
      (frg_phi_operands f) = Some op ->
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
    (frg_operand_real_use op = true <->
      exists e, Map.get EE e (frg_occurrence_index f) = Some (frg_operand_version op) /\
        dominates (live_graph (point_model (pre_ssa_points a)))
          (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
          (Graph.source (live_graph (point_model (pre_ssa_points a))) pe));
  frg_down_seed_exact : forall b u,
    (FinSet.mem (pair_encoding EB EU) (b, u) (frg_unsafe_seeds f) = true <->
      exists n, In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) /\
        frg_nearest_version a f u n (FrPhi b u) /\
        frg_no_dominating_real_use EE a f n (FrPhi b u) /\
        (pre_exit_point a n = true \/
         Graph.out (live_graph (point_model (pre_ssa_points a))) n = [] \/
         exists e, In e (Graph.out (live_graph (point_model (pre_ssa_points a))) n) /\
           kill (pre_genkill (pre_expression a)) e u = true /\
           pre_recomputed (pre_expression a) e <> Some u))
}.

(** * Uniqueness of expression definition points *)

Local Lemma pre_tail_member {A} (x : A) xs : In x (tl xs) -> In x xs.
Proof.
  destruct xs; cbn; tauto.
Qed.

Local Lemma pre_chain_target {N E} (g : Graph.t N E) ns es e :
  point_chain g ns es -> In e es -> In (Graph.target g e) (tl ns).
Proof.
  intros Hchain; induction Hchain as [n|n m ns a es Ha Htarget Hchain IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; cbn; left; symmetry; exact Htarget.
    + cbn; right; exact (IH Hin).
Qed.

Local Lemma pre_chain_target_unique {N E} (g : Graph.t N E) ns es :
  point_chain g ns es -> NoDup ns -> forall e e', In e es -> In e' es ->
  Graph.target g e = Graph.target g e' -> e = e'.
Proof.
  intro Hchain; induction Hchain as [n|n m ns a es Ha Htarget Hchain IH];
    intros Hnodup e e' He He' Heq; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  apply NoDup_cons_iff in Htail; destruct Htail as [Hfresh' Htail'].
  destruct He as [He|He], He' as [He'|He'].
  - congruence.
  - subst e; exfalso; apply Hfresh'; rewrite <- Htarget, Heq.
    exact (pre_chain_target g _ _ e' Hchain He').
  - subst e'; exfalso; apply Hfresh'; rewrite <- Htarget, <- Heq.
    exact (pre_chain_target g _ _ e Hchain He).
  - apply IH; [constructor; assumption|exact He|exact He'|exact Heq].
Qed.

Local Lemma pre_point_owner_listed {B BE N E V} (s : ssa_points B BE N E V) n :
  ssa_point_laws s -> In n (Graph.nodes (live_graph (point_model s))) ->
  In (block_of_point s n) (Graph.nodes (block_graph s)) /\
    In n (points_in_block s (block_of_point s n)).
Proof.
  intros Hlaw Hn; apply (points_covered Hlaw) in Hn.
  destruct Hn as [b [Hb Hn]].
  rewrite (points_owner Hlaw b n Hb Hn); auto.
Qed.

Local Lemma pre_internal_edge_block {B BE N E V} (s : ssa_points B BE N E V) e :
  ssa_point_laws s -> In e (edges_of (live_graph (point_model s))) ->
  block_edge_of s e = None -> exists b,
    In b (Graph.nodes (block_graph s)) /\ In e (instruction_edges s b) /\
    In (Graph.target (live_graph (point_model s)) e) (tl (points_in_block s b)).
Proof.
  intros Hlaw He Hinternal; apply in_flat_map in He; destruct He as [n [Hn He]].
  pose proof (out_source (points_graph_wf Hlaw) n e He) as Hsource.
  destruct (pre_point_owner_listed s n Hlaw Hn) as [Hb Hpoint].
  pose proof (instruction_edges_complete Hlaw n e Hn He Hinternal) as Hin.
  exists (block_of_point s n); split; [exact Hb|]; split; [exact Hin|].
  exact (pre_chain_target _ _ _ e (points_ordered Hlaw _ Hb) Hin).
Qed.

Local Lemma pre_internal_target_unique {B BE N E V} (s : ssa_points B BE N E V) e e' :
  ssa_point_laws s -> In e (edges_of (live_graph (point_model s))) ->
  In e' (edges_of (live_graph (point_model s))) ->
  block_edge_of s e = None -> block_edge_of s e' = None ->
  Graph.target (live_graph (point_model s)) e =
    Graph.target (live_graph (point_model s)) e' -> e = e'.
Proof.
  intros Hlaw He He' Hi Hi' Heq.
  destruct (pre_internal_edge_block s e Hlaw He Hi) as [b [Hb [Hedge Htarget]]].
  destruct (pre_internal_edge_block s e' Hlaw He' Hi') as [c [Hc [Hedge' Htarget']]].
  assert (Hbc : b = c).
  { rewrite <- (points_owner Hlaw b _ Hb (pre_tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hlaw c _ Hc (pre_tail_member _ _ Htarget')). }
  subst c; eapply pre_chain_target_unique.
  - exact (points_ordered Hlaw b Hb).
  - exact (points_unique Hlaw b).
  - exact Hedge.
  - exact Hedge'.
  - exact Heq.
Qed.

Local Lemma pre_chain_edge_source {N E} (g : Graph.t N E) ns es e :
  point_chain g ns es -> In e es ->
  exists n, In n ns /\ In e (Graph.out g n).
Proof.
  intro Hchain; induction Hchain as [n|n m ns a es Ha Htarget Hchain IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e; exists n; split; [left; reflexivity|exact Ha].
    + destruct (IH Hin) as [q [Hq Hedge]].
      exists q; split; [right; exact Hq|exact Hedge].
Qed.

Local Lemma pre_instruction_edge_listed {B BE N E V} (s : ssa_points B BE N E V) b e :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  In e (instruction_edges s b) -> In e (edges_of (live_graph (point_model s))).
Proof.
  intros Hlaw Hb He.
  destruct (pre_chain_edge_source _ _ _ e (points_ordered Hlaw b Hb) He)
    as [n [Hn Hedge]].
  apply in_flat_map; exists n; split; [|exact Hedge].
  apply (points_covered Hlaw); exists b; auto.
Qed.

Local Lemma pre_parameter_edge_listed {B BE N E V} (s : ssa_points B BE N E V) b :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  In (parameter_edge s b) (edges_of (live_graph (point_model s))) /\
    block_edge_of s (parameter_edge s b) = None.
Proof.
  intros Hlaw Hb.
  pose proof (nth_error_In _ _ (parameter_edge_first Hlaw b Hb)) as He.
  split.
  - exact (pre_instruction_edge_listed s b _ Hlaw Hb He).
  - exact (instruction_edges_internal Hlaw b _ Hb He).
Qed.

Local Lemma pre_internal_target_not_entry {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e n :
  pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  In n (Graph.entries (live_graph (point_model (pre_ssa_points a)))) ->
  Graph.target (live_graph (point_model (pre_ssa_points a))) e <> n.
Proof.
  intros Hlaw He Hi Hentry Heq; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hb [Hn Hfirst]]]].
  rewrite Hn in Hentry; destruct Hentry as [Hentry|Hfalse]; [subst n|contradiction].
  assert (Hentryblock : In entry (Graph.nodes (block_graph (pre_ssa_points a)))).
  { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hb; left; reflexivity. }
  destruct (pre_internal_edge_block _ e Hpoints He Hi) as [b [Hblock [Hedge Htarget]]].
  assert (Hfirstpoint : In first (points_in_block (pre_ssa_points a) entry)).
  { exact (nth_error_In _ _ Hfirst). }
  assert (Howner : b = entry).
  { rewrite <- (points_owner Hpoints b _ Hblock (pre_tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hpoints entry first Hentryblock Hfirstpoint). }
  subst b; rewrite Heq in Htarget.
  pose proof (points_unique Hpoints entry) as Hunique.
  destruct (points_in_block (pre_ssa_points a) entry) as [|head rest];
    cbn in Hfirst; [discriminate|].
  inversion Hfirst; subst head; inversion Hunique; subst; contradiction.
Qed.

Local Lemma pre_version_point_injective {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) d d' q :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  In d (frg_versions f) -> In d' (frg_versions f) ->
  frg_version_expr d = frg_version_expr d' ->
  frg_version_point a d = Some q -> frg_version_point a d' = Some q -> d = d'.
Proof.
  intros Hlaw Hwf Hd Hd' Hexpr Hpoint Hpoint'.
  apply (frg_versions_exact EB EBE EN EE EV EU a f Hwf) in Hd, Hd'.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct d as [u|u|e u|b u], d' as [v|v|e' v|c v];
    cbn [frg_version_point frg_version_expr] in Hexpr, Hpoint, Hpoint';
    try discriminate; subst v; try reflexivity.
  - exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact (proj1 Hd')| | |].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
    + apply nth_error_In in Hpoint; inversion Hpoint'; subst q; exact Hpoint.
    + inversion Hpoint'; reflexivity.
  - apply (frg_phi_exact EB EBE EN EE EV EU a f Hwf) in Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He Hi].
    exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |].
    + apply nth_error_In in Hpoint; inversion Hpoint'; subst q; exact Hpoint.
    + inversion Hpoint'; reflexivity.
  - exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact (proj1 Hd)| | |].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
    + apply nth_error_In in Hpoint'; inversion Hpoint; subst q; exact Hpoint'.
    + inversion Hpoint; reflexivity.
  - inversion Hpoint; inversion Hpoint'; subst q.
    f_equal; eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd)|
      exact (proj1 Hd')| | |congruence].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
  - apply (frg_phi_exact EB EBE EN EE EV EU a f Hwf) in Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He Hi].
    assert (Heq : e = parameter_edge (pre_ssa_points a) c).
    { eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd)|exact He| |exact Hi|].
      - exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
      - congruence. }
    exfalso; exact (proj2 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd))) c Heq).
  - apply (frg_phi_exact EB EBE EN EE EV EU a f Hwf) in Hd.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |].
    + apply nth_error_In in Hpoint'; inversion Hpoint; subst q; exact Hpoint'.
    + inversion Hpoint; reflexivity.
  - apply (frg_phi_exact EB EBE EN EE EV EU a f Hwf) in Hd.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    assert (Heq : e' = parameter_edge (pre_ssa_points a) b).
    { eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd')|exact He| |exact Hi|].
      - exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
      - congruence. }
    exfalso; exact (proj2 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd'))) b Heq).
  - apply (frg_phi_exact EB EBE EN EE EV EU a f Hwf) in Hd, Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He' Hi'].
    destruct (pre_internal_edge_block _ _ Hpoints He Hi) as [owner [Ho [Hedge Htarget]]].
    pose proof (pre_chain_target _ _ _ _ (points_ordered Hpoints b Hb)
      (nth_error_In _ _ (parameter_edge_first Hpoints b Hb))) as Htargetb.
    pose proof (pre_chain_target _ _ _ _ (points_ordered Hpoints c Hc)
      (nth_error_In _ _ (parameter_edge_first Hpoints c Hc))) as Htargetc.
    f_equal; rewrite <- (points_owner Hpoints b _ Hb (pre_tail_member _ _ Htargetb)).
    replace (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)) with
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) c)) by congruence.
    exact (points_owner Hpoints c _ Hc (pre_tail_member _ _ Htargetc)).
Qed.

(** At a reachable point an eligible expression has at most one nearest graph version. *)
Theorem frg_nearest_version_unique {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) u n d d' :
  pre_expr_ssa_laws EV a -> frg_wf EB EBE EN EE EV EU a f ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  frg_nearest_version a f u n d -> frg_nearest_version a f u n d' -> d = d'.
Proof.
  intros Hlaw Hwf Hready Hn [Hd [Hexpr [q [Hq [Hdom Hnearest]]]]]
    [Hd' [Hexpr' [q' [Hq' [Hdom' Hnearest']]]]].
  assert (Heq : q = q').
  { apply (idf_dominance_antisym EN _ _ Hready q q').
    - exact (dom_dominator_reachable _ q n Hn Hdom).
    - exact (dom_dominator_reachable _ q' n Hn Hdom').
    - exact (Hnearest' d q Hd Hexpr Hq Hdom).
    - exact (Hnearest d' q' Hd' Hexpr' Hq' Hdom'). }
  subst q'; eapply pre_version_point_injective; eauto; congruence.
Qed.

(** * Indexed scoped renaming *)

(* Invalid frames retain their nearest definition and real-use history for scope invariants. *)
Local Definition pre_rename_scope (B E U : Type) := Map.t U (frg_operand B E U * bool).

Record pre_rename_acc (B BE E U : Type) : Type := PreRenameAcc {
  pre_rename_occurrences : Map.t E (frg_version B E U);
  pre_rename_fresh : FinSet.t E;
  pre_rename_links : Map.t ((B * U) * BE) (frg_operand B E U);
  pre_rename_unsafe : FinSet.t (B * U)
}.
Arguments PreRenameAcc {B BE E U}.
Arguments pre_rename_occurrences {B BE E U}.
Arguments pre_rename_fresh {B BE E U}.
Arguments pre_rename_links {B BE E U}.
Arguments pre_rename_unsafe {B BE E U}.

Local Definition pre_rename_top {B E U} (EU : encoding U)
    (scope : pre_rename_scope B E U) (u : U) : frg_operand B E U * bool :=
  match Map.get EU u scope with
  | Some frame => frame
  | None => (FrgOperand (FrUnavailable u) false, false)
  end.

Local Definition pre_initial_frame {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u : frg_operand B E U * bool :=
  let available := pre_initial_available a u in
  (FrgOperand (if available then FrInitial u else FrUnavailable u) false, available).

Local Definition pre_initial_scope {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (family : list U) : pre_rename_scope B E U :=
  Map.of_list EU (map (fun u => (u, pre_initial_frame a u)) family).

Local Definition pre_rename_mark {B BE E U} (EB : encoding B) (EU : encoding U)
    (scope : pre_rename_scope B E U) (acc : pre_rename_acc B BE E U) (u : U) :=
  match pre_rename_top EU scope u with
  | (FrgOperand (FrPhi b v) false, _) =>
    PreRenameAcc (pre_rename_occurrences acc) (pre_rename_fresh acc) (pre_rename_links acc)
      (FinSet.add (pair_encoding EB EU) (b, v) (pre_rename_unsafe acc))
  | _ => acc
  end.

Local Definition pre_same_expression {U} (EU : encoding U) (v : option U) (u : U) : bool :=
  match v with
  | Some x => Pos.eqb (encode EU x) (encode EU u)
  | None => false
  end.

Local Definition pre_rename_alter {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) (u : U) :=
  let '(scope, acc) := work in
  let marked := if pre_same_expression EU (pre_recomputed (pre_expression a) e) u
    then acc else pre_rename_mark EB EU scope acc u in
  (Map.set EU u (fst (pre_rename_top EU scope u), false) scope, marked).

Local Definition pre_rename_occurrence {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) :
    (pre_rename_scope B E U * pre_rename_acc B BE E U) * option U :=
  let '(scope, acc) := work in
  match pre_recomputed (pre_expression a) e with
  | None => (work, None)
  | Some u =>
    if pre_total_pure (pre_expression a) u then
      let '(frame, available) := pre_rename_top EU scope u in
      let fresh := if available then
        match frg_operand_version frame with
        | FrUnavailable _ => true
        | _ => negb (Pos.eqb (encode EU (frg_version_expr (frg_operand_version frame)))
            (encode EU u))
        end else true in
      let d := if fresh then FrFresh e u else frg_operand_version frame in
      let updated := PreRenameAcc (Map.set EE e d (pre_rename_occurrences acc))
        (if fresh then FinSet.add EE e (pre_rename_fresh acc) else pre_rename_fresh acc)
        (pre_rename_links acc) (pre_rename_unsafe acc) in
      ((if fresh then scope else Map.set EU u (FrgOperand d true, true) scope, updated),
       if fresh then Some u else None)
    else (work, None)
  end.

Local Definition pre_rename_phi_index {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (sites : U -> FinSet.t B) family : FinSet.t (B * U) :=
  FinSet.of_list (pair_encoding EB EU) (flat_map (fun u =>
    if pre_total_pure (pre_expression a) u then
      map (fun b => (b, u)) (FinSet.elements (sites u)) else []) family).

Local Lemma pre_phi_sites_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u :
  FinSet.wf EB (frg_phi_sites EB EBE EV EU a u).
Proof.
  unfold frg_phi_sites, pre_phi_sites_graph; apply pre_group_fold_wf.
  intro v; unfold pre_group_lookup; rewrite Map.get_empty; apply Map.wf_empty.
Qed.

Local Lemma pre_rename_phi_index_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\
    pre_total_pure (pre_expression a) v = true) ->
  (FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_phi_index EB EU a (frg_phi_sites EB EBE EV EU a) family) = true <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
    frg_phi_needed EB EU a u b).
Proof.
  intros Hlaw Hready Hfamily; unfold pre_rename_phi_index.
  rewrite FinSet.of_list_spec, in_flat_map; split.
  - intros [v [Hv Hin]]; destruct (Hfamily v) as [Hsound Hcomplete].
    destruct (Hsound Hv) as [Hmember Hpure]; rewrite Hpure in Hin.
    apply in_map_iff in Hin; destruct Hin as [c [Heq Hc]]; inversion Heq; subst c v.
    split; [exact Hmember|]; split; [exact Hpure|].
    apply (frg_phi_sites_exact EB EBE EV EU a Hlaw Hready u b Hmember).
    apply (FinSet.elements_spec EB); [apply pre_phi_sites_wf|exact Hc].
  - intros [Hmember [Hpure Hneeded]]; exists u; split; [apply Hfamily; auto|].
    rewrite Hpure; apply in_map_iff; exists b; split; [reflexivity|].
    apply (FinSet.elements_spec EB); [apply pre_phi_sites_wf|].
    apply (frg_phi_sites_exact EB EBE EV EU a Hlaw Hready u b Hmember); exact Hneeded.
Qed.

(* Invert ordered family operands once; an edge visits only expressions incident to its defs. *)
Local Definition pre_rename_operand_index {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family :=
  fold_left (pre_group_add EV EU)
    (flat_map (fun u => map (fun x => (x, u)) (pre_operands a u)) family) Map.empty.

Local Definition pre_rename_alter_candidates {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (operands : Map.t V (FinSet.t U)) e : list U :=
  FinSet.elements (FinSet.of_list EU (flat_map
    (fun x => FinSet.elements (pre_group_lookup EV operands x))
    (edge_def (point_model (pre_ssa_points a)) e))).

Local Definition pre_rename_alter_index {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family :=
  let operands := pre_rename_operand_index EV EU a family in
  fold_left (pre_group_add EE EU)
    (flat_map (fun e => map (fun u => (e, u))
      (filter (fun u => kill (pre_genkill (pre_expression a)) e u)
        (pre_rename_alter_candidates EV EU a operands e)))
      (edges_of (live_graph (point_model (pre_ssa_points a))))) Map.empty.

Local Definition pre_rename_exit_index {S O B BE N E V K C U} (EN : encoding N)
    (a : pre_expr_ssa S O B BE N E V K C U) (family : list U) : Map.t N (list U) :=
  Map.of_list EN (flat_map (fun n =>
    if pre_exit_point a n then [(n, family)] else
    match Graph.out (live_graph (point_model (pre_ssa_points a))) n with
    | [] => [(n, family)]
    | _ => []
    end) (Graph.nodes (live_graph (point_model (pre_ssa_points a))))).

Local Definition pre_rename_exit {B BE N E U} (EB : encoding B) (EN : encoding N)
    (EU : encoding U) (exits : Map.t N (list U)) n
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) :=
  let '(scope, acc) := work in
  (scope, fold_left (pre_rename_mark EB EU scope) (index_edges EN exits n) acc).

Local Definition pre_rename_definitions {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (phis : Map.t B (FinSet.t U)) b e fresh (scope : pre_rename_scope B E U) :=
  let scope := match fresh with
  | Some u => Map.set EU u (FrgOperand (FrFresh e u) true, true) scope
  | None => scope
  end in
  if Pos.eqb (encode EE e) (encode EE (parameter_edge (pre_ssa_points a) b))
    then fold_left (fun frames u => Map.set EU u (FrgOperand (FrPhi b u) false, true) frames)
      (FinSet.elements (pre_group_lookup EB phis b)) scope else scope.

Local Definition pre_rename_instruction {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (alterations : Map.t E (FinSet.t U)) (exits : Map.t N (list U))
    (phis : Map.t B (FinSet.t U)) b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e :=
  let '(observed, fresh) := pre_rename_occurrence EB EE EU a e work in
  let altered := fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) observed in
  let '(scope, acc) := altered in
  pre_rename_exit EB EN EU exits
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (pre_rename_definitions EB EE EU a phis b e fresh scope, acc).

Local Definition pre_rename_argument_index {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a))) (phis : FinSet.t (B * U)) :=
  fold_left (pre_group_add EB (pair_encoding EBE EU))
    (flat_map (fun key => let '(b, u) := key in
      map (fun be => (Graph.source (block_graph (pre_ssa_points a)) be, (be, u)))
        (pred_edges p b)) (FinSet.elements phis)) Map.empty.

Local Definition pre_rename_argument {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (scope : pre_rename_scope B E U) (acc : pre_rename_acc B BE E U) (argument : BE * U) :=
  let '(be, u) := argument in
  match pre_phi_translate a be u with
  | None => acc
  | Some translated =>
    let '(frame, available) := pre_rename_top EU scope translated in
    let op := if available && Pos.eqb (encode EU (frg_version_expr (frg_operand_version frame)))
      (encode EU translated) then frame else FrgOperand (FrUnavailable translated) false in
    PreRenameAcc (pre_rename_occurrences acc) (pre_rename_fresh acc)
      (Map.set (pair_encoding (pair_encoding EB EU) EBE)
        ((Graph.target (block_graph (pre_ssa_points a)) be, u), be) op (pre_rename_links acc))
      (pre_rename_unsafe acc)
  end.

Local Definition pre_rename_block {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (alterations : Map.t E (FinSet.t U)) (exits : Map.t N (list U))
    (phis : Map.t B (FinSet.t U)) (arguments : Map.t B (FinSet.t (BE * U))) b
    (scope : pre_rename_scope B E U) (acc : pre_rename_acc B BE E U) :=
  let entered := match points_in_block (pre_ssa_points a) b with
  | [] => (scope, acc)
  | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
  end in
  let '(scope, acc) := fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered in
  (scope, fold_left (pre_rename_argument EB EBE EU a scope)
    (FinSet.elements (pre_group_lookup EB arguments b)) acc).

Local Definition pre_rename_work (B BE E U : Type) :=
  (list (B * pre_rename_scope B E U) * FinSet.t B * pre_rename_acc B BE E U)%type.

Local Definition pre_rename_step {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (children : Map.t B (list B)) (alterations : Map.t E (FinSet.t U))
    (exits : Map.t N (list U)) (phis : Map.t B (FinSet.t U))
    (arguments : Map.t B (FinSet.t (BE * U))) (work : pre_rename_work B BE E U) :=
  let '(tasks, seen, acc) := work in
  match tasks with
  | [] => work
  | (b, scope) :: rest =>
    if FinSet.mem EB b seen then (rest, seen, acc) else
      let '(scope, acc) := pre_rename_block EB EBE EN EE EU a alterations exits phis arguments
        b scope acc in
      (map (fun child => (child, scope)) (index_edges EB children b) ++ rest,
       FinSet.add EB b seen, acc)
  end.

Local Fixpoint pre_rename_run {B BE E U} (step : pre_rename_work B BE E U ->
    pre_rename_work B BE E U) (fuel : positive) (work : pre_rename_work B BE E U) :=
  match fst (fst work) with
  | [] => work
  | _ =>
    match fuel with
    | xH => step work
    | xO p => pre_rename_run step p (pre_rename_run step p work)
    | xI p => step (pre_rename_run step p (pre_rename_run step p work))
    end
  end.

(* Each unvisited parent binding pays for the one child task it can still emit. *)
Local Fixpoint pre_rename_credit {B} (EB : encoding B) (parents : list (B * B))
    (seen : FinSet.t B) : nat :=
  match parents with
  | [] => 0
  | (_, parent) :: rest =>
    if FinSet.mem EB parent seen then pre_rename_credit EB rest seen
    else S (pre_rename_credit EB rest seen)
  end.

Local Lemma pre_children_at {B} (EB : encoding B) child parent parents b :
  index_edges EB (dom_children EB ((child, parent) :: parents)) b =
  if dfs_eq_dec EB b parent then child :: index_edges EB (dom_children EB parents) b
  else index_edges EB (dom_children EB parents) b.
Proof.
  cbn [dom_children]; unfold index_edges at 1.
  destruct (dfs_eq_dec EB b parent) as [Heq|Hne].
  - subst b; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma pre_rename_credit_spent {B} (EB : encoding B) parents seen b :
  FinSet.mem EB b seen = false ->
  pre_rename_credit EB parents (FinSet.add EB b seen) +
    length (index_edges EB (dom_children EB parents) b) = pre_rename_credit EB parents seen.
Proof.
  intro Hfresh; induction parents as [|[child parent] parents IH].
  - unfold index_edges; cbn [dom_children pre_rename_credit]; rewrite Map.get_empty; reflexivity.
  - rewrite pre_children_at; cbn [pre_rename_credit]; rewrite dfs_mem_add.
    destruct (dfs_eq_dec EB b parent) as [Heq|Hne].
    + subst parent; destruct (dfs_eq_dec EB b b); [|congruence].
      rewrite Hfresh; cbn [length]; lia.
    + destruct (dfs_eq_dec EB parent b); [congruence|].
      destruct (FinSet.mem EB parent seen); cbn [length]; lia.
Qed.

Local Lemma pre_rename_credit_initial {B} (EB : encoding B) parents :
  pre_rename_credit EB parents FinSet.empty = length parents.
Proof.
  induction parents as [|[child parent] parents IH]; cbn [pre_rename_credit length];
    [reflexivity|rewrite FinSet.mem_empty, IH; reflexivity].
Qed.

Local Definition pre_rename_measure {B BE E U} (EB : encoding B) parents
    (work : pre_rename_work B BE E U) :=
  let '(tasks, seen, _) := work in length tasks + pre_rename_credit EB parents seen.

Local Lemma pre_rename_step_decreases {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) parents alterations exits phis arguments work :
  fst (fst work) <> [] ->
  pre_rename_measure EB parents (pre_rename_step EB EBE EN EE EU a (dom_children EB parents)
    alterations exits phis arguments work) < pre_rename_measure EB parents work.
Proof.
  destruct work as [[[|[b scope] rest] seen] acc]; [contradiction|]; intro Hpending.
  unfold pre_rename_step, pre_rename_measure; cbn [fst].
  destruct (FinSet.mem EB b seen) eqn:Hseen; [cbn [length]; lia|].
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output].
  cbn; rewrite length_app, length_map.
  pose proof (pre_rename_credit_spent EB parents seen b Hseen); lia.
Qed.

Local Lemma pre_rename_run_agrees {B BE E U} step :
  (forall seen acc, step ([], seen, acc) = ([], seen, acc)) ->
  forall fuel (work : pre_rename_work B BE E U),
    pre_rename_run step fuel work = Pos.iter step work fuel.
Proof.
  intro Hempty.
  assert (Hfixed : forall seen acc fuel, Pos.iter step ([], seen, acc) fuel = ([], seen, acc)).
  { intros seen acc fuel; induction fuel using Pos.peano_ind.
    - apply Hempty.
    - rewrite Pos.iter_succ, IHfuel; apply Hempty. }
  intro fuel; induction fuel as [p IH|p IH|]; intros [[[|task rest] seen] acc].
  - symmetry; apply Hfixed.
  - cbn [pre_rename_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag.
    symmetry; apply (Pos.iter_succ (xO p)).
  - symmetry; apply Hfixed.
  - cbn [pre_rename_run fst]; rewrite !IH, <- Pos.iter_add, Pos.add_diag; reflexivity.
  - symmetry; apply Hfixed.
  - reflexivity.
Qed.

Local Definition pre_rename_keys {B BE E U} (work : pre_rename_work B BE E U) :=
  (map fst (fst (fst work)), snd (fst work)).

Local Lemma pre_rename_keys_step {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_rename_keys (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments
    work) = pre_discover_step EB (index_edges EB children) (pre_rename_keys work).
Proof.
  destruct work as [[[|[b scope] rest] seen] acc]; [reflexivity|].
  unfold pre_rename_step, pre_rename_keys, pre_discover_step; cbn [fst snd map].
  destruct (FinSet.mem EB b seen); [reflexivity|].
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output].
  cbn [fst snd]; rewrite map_app, map_map.
  cbn [fst]; rewrite map_id; reflexivity.
Qed.

Local Lemma pre_rename_keys_iter {B BE E U} (EB : encoding B) children step :
  (forall work : pre_rename_work B BE E U, pre_rename_keys (step work) =
    pre_discover_step EB children (pre_rename_keys work)) ->
  forall fuel work, pre_rename_keys (Pos.iter step work fuel) =
    Pos.iter (pre_discover_step EB children) (pre_rename_keys work) fuel.
Proof.
  intros Hstep fuel; induction fuel using Pos.peano_ind; intro work.
  - apply Hstep.
  - rewrite !Pos.iter_succ, Hstep, IHfuel; reflexivity.
Qed.

Local Lemma pre_rename_iter_bound {B BE E U} (EB : encoding B) parents step :
  (forall seen acc, step ([], seen, acc) = ([], seen, acc)) ->
  (forall work : pre_rename_work B BE E U, fst (fst work) <> [] ->
    pre_rename_measure EB parents (step work) < pre_rename_measure EB parents work) ->
  forall fuel work, fst (fst (Pos.iter step work fuel)) = [] \/
    pre_rename_measure EB parents (Pos.iter step work fuel) + Pos.to_nat fuel <=
      pre_rename_measure EB parents work.
Proof.
  intros Hempty Hstep fuel; induction fuel using Pos.peano_ind; intro work.
  - cbn [Pos.iter]; destruct work as [[[|task rest] seen] acc].
    + left; rewrite Hempty; reflexivity.
    + right; pose proof (Hstep ((task :: rest, seen), acc) ltac:(discriminate)).
      cbn [Pos.to_nat]; lia.
  - rewrite Pos.iter_succ; destruct (IHfuel work) as [Hdone|Hbound].
    + destruct (Pos.iter step work fuel) as [[tasks seen] acc]; cbn in Hdone; subst tasks.
      left; rewrite Hempty; reflexivity.
    + destruct (Pos.iter step work fuel) as [[[|task rest] seen] acc] eqn:Hmid.
      * left; rewrite Hempty; reflexivity.
      * right; pose proof (Hstep ((task :: rest, seen), acc) ltac:(discriminate)).
        rewrite Pos2Nat.inj_succ; lia.
Qed.

Local Lemma pre_rename_nonexhaustion {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) parents alterations exits phis arguments
    roots scope acc :
  fst (fst (pre_rename_run
    (pre_rename_step EB EBE EN EE EU a (dom_children EB parents) alterations exits phis arguments)
    (Pos.of_succ_nat (length roots + length parents))
    (map (fun b => (b, scope)) roots, FinSet.empty, acc))) = [].
Proof.
  rewrite pre_rename_run_agrees by reflexivity.
  destruct (pre_rename_iter_bound EB parents
    (pre_rename_step EB EBE EN EE EU a (dom_children EB parents) alterations exits phis arguments)
    ltac:(reflexivity) (pre_rename_step_decreases EB EBE EN EE EU a parents alterations exits
      phis arguments) (Pos.of_succ_nat (length roots + length parents))
    (map (fun b => (b, scope)) roots, FinSet.empty, acc)) as [Hdone|Hbound].
  - exact Hdone.
  - unfold pre_rename_measure in Hbound; cbn in Hbound.
    rewrite length_map, pre_rename_credit_initial, SuccNat2Pos.id_succ in Hbound; lia.
Qed.

Local Lemma pre_rename_seen_all {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    alterations exits phis arguments scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  let p := prepare EB (block_graph (pre_ssa_points a)) in
  let parents := Map.elements (idom (dominator_tree p)) in
  let roots := Graph.entries (block_graph (pre_ssa_points a)) in
  let result := pre_rename_run (pre_rename_step EB EBE EN EE EU a (dom_children EB parents)
    alterations exits phis arguments) (Pos.of_succ_nat (length roots + length parents))
    (map (fun b => (b, scope)) roots, FinSet.empty, acc) in
  forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    FinSet.mem EB b (snd (fst result)) = true.
Proof.
  intros Hlaw Hready p parents roots result b Hb.
  set (next := index_edges EB (dom_children EB parents)).
  assert (Hkeys : pre_rename_keys result = Pos.iter (pre_discover_step EB next)
    (roots, FinSet.empty) (Pos.of_succ_nat (length roots + length parents))).
  { unfold result; rewrite pre_rename_run_agrees by reflexivity.
    rewrite (pre_rename_keys_iter EB next _
      (pre_rename_keys_step EB EBE EN EE EU a _ alterations exits phis arguments)).
    unfold pre_rename_keys; cbn [fst snd map]; rewrite map_map; cbn [fst].
    rewrite map_id; reflexivity. }
  assert (Hcovers : pre_discover_covers EB next roots (pre_rename_keys result)).
  { rewrite Hkeys; apply pre_discover_covers_iter; split.
    - intros v Hv; right; exact Hv.
    - intros v w Hfalse; cbn [snd] in Hfalse; rewrite FinSet.mem_empty in Hfalse;
        discriminate. }
  assert (Hdone : fst (pre_rename_keys result) = []).
  { unfold pre_rename_keys, result; rewrite (pre_rename_nonexhaustion EB EBE EN EE EU a parents
      alterations exits phis arguments roots scope acc); reflexivity. }
  assert (Havailable : forall v, pre_discover_available EB (pre_rename_keys result) v ->
    FinSet.mem EB v (snd (fst result)) = true).
  { intros v [Hmem|Hin]; [exact Hmem|rewrite Hdone in Hin; contradiction]. }
  assert (Hreached : forall v,
    reachable (set_entries (dom_forest p (idom (dominator_tree p))) roots) v ->
    FinSet.mem EB v (snd (fst result)) = true).
  { intros v Hreach; induction Hreach as [v Hv|child Hparent IH Hedge].
    - apply Havailable; apply (proj1 Hcovers); exact Hv.
    - apply Havailable; apply (proj2 Hcovers _ child IH); exact Hedge. }
  apply Hreached.
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hentry [Hpoints Hfirst]]]].
  assert (Hdom : dominates (block_graph (pre_ssa_points a)) entry b).
  { intros start es Hstart Hpath; rewrite Hentry in Hstart.
    destruct Hstart as [Heq|Hfalse]; [left; exact Heq|contradiction]. }
  pose proof (pre_expr_reachable_blocks EV a Hlaw b Hb) as Hreachable.
  destruct (idf_tree_reaches EB _ p Hready entry b
    (proj1 (idf_dominance_anc EB _ p Hready entry b Hreachable) Hdom)) as [es Hpath].
  apply reachable_iff_path; exists entry, es; split.
  - unfold roots; rewrite Hentry; left; reflexivity.
  - apply idf_path_entries; exact Hpath.
Qed.

Local Definition pre_rename_fresh_versions {S O B BE N E V K C U}
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U)
    (acc : pre_rename_acc B BE E U) : list (frg_version B E U) :=
  flat_map (fun e => if FinSet.mem EE e (pre_rename_fresh acc) then
    match pre_recomputed (pre_expression a) e with
    | Some u => [FrFresh e u]
    | None => []
    end else []) (edges_of (live_graph (point_model (pre_ssa_points a)))).

Local Lemma pre_rename_fresh_versions_spec {S O B BE N E V K C U}
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U) acc d :
  In d (pre_rename_fresh_versions EE a acc) <->
  exists e u, d = FrFresh e u /\
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    pre_recomputed (pre_expression a) e = Some u /\
    FinSet.mem EE e (pre_rename_fresh acc) = true.
Proof.
  unfold pre_rename_fresh_versions; rewrite in_flat_map; split.
  - intros [e [He Hin]]; destruct (FinSet.mem EE e (pre_rename_fresh acc)) eqn:Hfresh;
      [|contradiction].
    destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
      [|contradiction].
    destruct Hin as [Heq|Hfalse]; [exists e, u; auto|contradiction].
  - intros [e [u [Heq [He [Hcomputed Hfresh]]]]]; subst d.
    exists e; split; [exact He|rewrite Hfresh, Hcomputed; left; reflexivity].
Qed.

Local Definition pre_rename_versions {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (family : list U) (phis : FinSet.t (B * U)) (acc : pre_rename_acc B BE E U) :=
  FinSet.elements (FinSet.of_list (frg_version_encoding EB EE EU)
    (map FrUnavailable family ++ map FrInitial (filter (pre_initial_available a) family) ++
      map (fun key => FrPhi (fst key) (snd key)) (FinSet.elements phis) ++
      pre_rename_fresh_versions EE a acc)).

Local Lemma pre_rename_phi_versions_spec {B E U} (EB : encoding B) (EU : encoding U)
    (phis : FinSet.t (B * U)) (d : frg_version B E U) :
  FinSet.wf (pair_encoding EB EU) phis ->
  (In d (map (fun key => FrPhi (fst key) (snd key)) (FinSet.elements phis)) <->
    exists b u, d = FrPhi b u /\ FinSet.mem (pair_encoding EB EU) (b, u) phis = true).
Proof.
  intro Hwf; rewrite in_map_iff; split.
  - intros [[b u] [Heq Hin]]; exists b, u; split; [symmetry; exact Heq|].
    apply (FinSet.elements_spec (pair_encoding EB EU)); assumption.
  - intros [b [u [Heq Hmem]]]; subst d; exists (b, u); split; [reflexivity|].
    apply (FinSet.elements_spec (pair_encoding EB EU)); assumption.
Qed.

Local Lemma pre_rename_versions_spec {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    family phis acc d : FinSet.wf (pair_encoding EB EU) phis ->
  (In d (pre_rename_versions EB EE EU a family phis acc) <->
    match d with
    | FrUnavailable u => In u family
    | FrInitial u => In u family /\ pre_initial_available a u = true
    | FrFresh e u => In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
        pre_recomputed (pre_expression a) e = Some u /\
        FinSet.mem EE e (pre_rename_fresh acc) = true
    | FrPhi b u => FinSet.mem (pair_encoding EB EU) (b, u) phis = true
    end).
Proof.
  intro Hphis; unfold pre_rename_versions.
  rewrite (FinSet.elements_spec (frg_version_encoding EB EE EU));
    [|apply FinSet.wf_fold_add; apply Map.wf_empty].
  rewrite (FinSet.of_list_spec (frg_version_encoding EB EE EU)), !in_app_iff.
  rewrite (pre_rename_phi_versions_spec EB EU phis d Hphis).
  rewrite (pre_rename_fresh_versions_spec EE a acc d), !in_map_iff.
  setoid_rewrite filter_In.
  clear Hphis; destruct d as [u|u|e u|b u]; split.
  - intros [[v [Heq Hv]]|[[v [Heq Hv]]|[[c [v [Heq Hv]]]|[e' [v [Heq Hv]]]]]];
      inversion Heq; subst; assumption.
  - intro Hu; left; exists u; auto.
  - intros [[v [Heq Hv]]|[[v [Heq Hv]]|[[c [v [Heq Hv]]]|[e' [v [Heq Hv]]]]]];
      inversion Heq; subst; assumption.
  - intro Hu; right; left; exists u; auto.
  - intros [[v [Heq Hv]]|[[v [Heq Hv]]|[[c [v [Heq Hv]]]|[e' [v [Heq Hv]]]]]];
      inversion Heq; subst; assumption.
  - intro Hu; right; right; right; exists e, u; auto.
  - intros [[v [Heq Hv]]|[[v [Heq Hv]]|[[c [v [Heq Hv]]]|[e' [v [Heq Hv]]]]]];
      inversion Heq; subst; assumption.
  - intro Hu; right; right; left; exists b, u; auto.
Qed.

(** Exact dominator scopes retain edge-specific links, including links closing a cycle. *)
Definition build_frg {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : factored_redundancy_graph B BE E U :=
  let p := prepare EB (block_graph (pre_ssa_points a)) in
  let tree := dominator_tree p in
  let all_family := pre_expr_universe EBE EV EU a in
  let sites := pre_phi_sites_graph EB EU
    (pre_phi_graph_from EB EV EU a p (dominance_frontier p tree) all_family) in
  let family := filter (pre_total_pure (pre_expression a)) all_family in
  let phis := pre_rename_phi_index EB EU a sites family in
  let phi_blocks := fold_left (pre_group_add EB EU) (FinSet.elements phis) Map.empty in
  let alterations := pre_rename_alter_index EE EV EU a family in
  let exits := pre_rename_exit_index EN a family in
  let arguments := pre_rename_argument_index EB EBE EU a p phis in
  let parents := Map.elements (idom tree) in
  let children := dom_children EB parents in
  let scope := pre_initial_scope EU a family in
  let roots := Graph.entries (block_graph (pre_ssa_points a)) in
  let initial := (map (fun b => (b, scope)) roots, FinSet.empty,
    PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty) in
  let result := pre_rename_run
    (pre_rename_step EB EBE EN EE EU a children alterations exits phi_blocks arguments)
    (Pos.of_succ_nat (length roots + length parents)) initial in
  let acc := snd result in
  FactoredRedundancyGraph
    (pre_rename_versions EB EE EU a family phis acc)
    (pre_rename_occurrences acc) (pre_rename_fresh acc) phis
    (pre_rename_links acc) (pre_rename_unsafe acc).

(** The producer's phi index has exactly the adopted pure-family placement relation. *)
Theorem build_frg_phi_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall b u, FinSet.mem (pair_encoding EB EU) (b, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
    frg_phi_needed EB EU a u b.
Proof.
  intros Hlaw Hready b u.
  change (FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_phi_index EB EU a (frg_phi_sites EB EBE EV EU a)
      (filter (pre_total_pure (pre_expression a)) (pre_expr_universe EBE EV EU a))) = true <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
      frg_phi_needed EB EU a u b).
  apply pre_rename_phi_index_exact; [exact Hlaw|exact Hready|].
  intro v; rewrite filter_In, (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); tauto.
Qed.

(** Materialization deduplicates every graph version by its constructor and exact identities. *)
Theorem build_frg_versions_nodup {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  NoDup (frg_versions (build_frg EB EBE EN EE EV EU a)).
Proof.
  unfold build_frg; cbn [frg_versions]; unfold pre_rename_versions.
  apply (FinSet.elements_nodup (frg_version_encoding EB EE EU)).
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

(** Materialized versions are exactly the sentinels, selected initials, fresh nodes and phis. *)
Theorem build_frg_versions_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a -> forall d, In d (frg_versions (build_frg EB EBE EN EE EV EU a)) <->
    match d with
    | FrUnavailable u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true
    | FrInitial u => pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true /\
        pre_initial_available a u = true
    | FrFresh e u => In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
        pre_recomputed (pre_expression a) e = Some u /\
        FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) = true
    | FrPhi b u => FinSet.mem (pair_encoding EB EU) (b, u)
        (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true
    end.
Proof.
  intros Hlaw d; unfold build_frg; cbn [frg_versions frg_fresh_index frg_phi_index].
  eapply iff_trans; [apply pre_rename_versions_spec|].
  - unfold pre_rename_phi_index; apply FinSet.wf_fold_add; apply Map.wf_empty.
  - destruct d; try reflexivity.
    + rewrite filter_In, (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); tauto.
    + rewrite filter_In, (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw)); tauto.
Qed.

(** * Ordered point paths and block projection *)

Local Definition pre_project_edges {B BE N E V} (s : ssa_points B BE N E V)
    (es : list E) : list BE :=
  flat_map (fun e => match block_edge_of s e with
    | Some be => [be]
    | None => []
    end) es.

Local Lemma pre_project_path {B BE N E V} (s : ssa_points B BE N E V) n es m :
  ssa_point_laws s -> In n (Graph.nodes (live_graph (point_model s))) ->
  path (live_graph (point_model s)) n es m ->
  path (block_graph s) (block_of_point s n) (pre_project_edges s es) (block_of_point s m).
Proof.
  intros Hlaw Hn Hpath; revert Hn.
  induction Hpath as [n|e es m Hedge Hpath IH]; intro Hn; [constructor|].
  pose proof (out_target_in (points_graph_wf Hlaw) _ e Hn Hedge) as Htarget.
  pose proof (point_edge_projection Hlaw _ e Hn Hedge) as Hprojection.
  unfold pre_project_edges; cbn [flat_map].
  destruct (block_edge_of s e) as [be|] eqn:Hbe.
  - destruct Hprojection as [Hedge' [Htarget' [Hlast Hfirst]]].
    pose proof (out_source (blocks_graph_wf Hlaw) _ be Hedge') as Hsource.
    cbn [app]; rewrite <- Hsource; constructor.
    + rewrite Hsource; exact Hedge'.
    + rewrite Htarget'; exact (IH Htarget).
  - rewrite Hprojection; exact (IH Htarget).
Qed.

Local Lemma pre_internal_target_not_first {B BE N E V} (s : ssa_points B BE N E V)
    e b first :
  ssa_point_laws s -> In e (edges_of (live_graph (point_model s))) ->
  block_edge_of s e = None -> In b (Graph.nodes (block_graph s)) ->
  nth_error (points_in_block s b) 0 = Some first ->
  Graph.target (live_graph (point_model s)) e <> first.
Proof.
  intros Hlaw He Hi Hb Hfirst Heq.
  destruct (pre_internal_edge_block s e Hlaw He Hi) as [owner [Ho [Hedge Htarget]]].
  assert (Howner : owner = b).
  { rewrite <- (points_owner Hlaw owner _ Ho (pre_tail_member _ _ Htarget)).
    rewrite Heq; exact (points_owner Hlaw b first Hb (nth_error_In _ _ Hfirst)). }
  subst owner; rewrite Heq in Htarget.
  pose proof (points_unique Hlaw b) as Hunique.
  destruct (points_in_block s b) as [|head rest]; cbn in Hfirst; [discriminate|].
  inversion Hfirst; subst head; apply NoDup_cons_iff in Hunique; tauto.
Qed.

Local Lemma pre_internal_incoming_unique {B BE N E V} (s : ssa_points B BE N E V) e e' :
  ssa_point_laws s -> In e (edges_of (live_graph (point_model s))) ->
  block_edge_of s e = None -> In e' (edges_of (live_graph (point_model s))) ->
  Graph.target (live_graph (point_model s)) e' =
    Graph.target (live_graph (point_model s)) e -> e' = e.
Proof.
  intros Hlaw He Hi He' Heq; destruct (block_edge_of s e') as [be|] eqn:Hi'.
  - apply in_flat_map in He'; destruct He' as [n [Hn Hedge]].
    pose proof (point_edge_projection Hlaw n e' Hn Hedge) as Hprojection.
    rewrite Hi' in Hprojection; destruct Hprojection as [Hbe [Htarget [Hlast Hfirst]]].
    destruct (pre_point_owner_listed s n Hlaw Hn) as [Hb Hpoint].
    pose proof (out_target_in (blocks_graph_wf Hlaw) _ be Hb Hbe) as Htargetblock.
    exfalso; apply (pre_internal_target_not_first s e _ _ Hlaw He Hi Htargetblock Hfirst).
    symmetry; exact Heq.
  - eapply pre_internal_target_unique; [exact Hlaw|exact He'|exact He|exact Hi'|exact Hi|].
    exact Heq.
Qed.

Local Lemma pre_unique_incoming_dominates {N E} (g : Graph.t N E) e :
  graph_wf g ->
  (forall n, In n (Graph.entries g) -> Graph.target g e <> n) ->
  (forall e', In e' (edges_of g) -> Graph.target g e' = Graph.target g e -> e' = e) ->
  dominates g (Graph.source g e) (Graph.target g e).
Proof.
  intros Hwf Hentry Hunique start es Hstart Hpath.
  destruct es as [|a es].
  - apply dominance_path_nil_inv in Hpath; exfalso; apply (Hentry start Hstart).
    symmetry; exact Hpath.
  - destruct (semi_path_last g start (a :: es) _ Hpath ltac:(discriminate))
      as [prefix [last [Hsplit [Hprefix [Hlast Htarget]]]]].
    assert (Hlisted : In last (edges_of g)).
    { apply in_flat_map; exists (Graph.source g last); split; [|exact Hlast].
      apply (reachable_in_nodes g _ Hwf); apply reachable_iff_path.
      exists start, prefix; auto. }
    specialize (Hunique last Hlisted Htarget); subst last.
    destruct (path_endpoint g start prefix (Graph.source g e) Hprefix)
      as [Heq|[earlier [Hin Heq]]].
    + left; exact Heq.
    + right; exists earlier; split; [rewrite Hsplit; apply in_or_app; left; exact Hin|exact Heq].
Qed.

Local Lemma pre_internal_source_dominates {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e :
  pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  dominates (live_graph (point_model (pre_ssa_points a)))
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Hlaw He Hi; apply pre_unique_incoming_dominates.
  - exact (points_graph_wf (pre_expr_points EV a Hlaw)).
  - intros n Hn; exact (pre_internal_target_not_entry EV a e n Hlaw He Hi Hn).
  - intros e' He' Heq; exact (pre_internal_incoming_unique _ e e'
      (pre_expr_points EV a Hlaw) He Hi He' Heq).
Qed.

Local Lemma pre_chain_member_dominates_last {N E} (g : Graph.t N E) ns es default :
  graph_wf g -> point_chain g ns es ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
  forall q, In q ns -> dominates g q (last ns default).
Proof.
  intros Hwf Hchain; induction Hchain as [n|n m ns e es He Htarget Hchain IH];
    intros Hedges q Hq.
  - destruct Hq as [Heq|Hfalse]; [subst q; apply dominates_refl|contradiction].
  - assert (Htail : forall a, In a es -> dominates g (Graph.source g a) (Graph.target g a)).
    { intros a Ha; apply Hedges; right; exact Ha. }
    change (dominates g q (last (m :: ns) default)).
    destruct Hq as [Heq|Hq]; [subst q|exact (IH Htail q Hq)].
    eapply dominates_trans with (b := m).
    + pose proof (Hedges e (or_introl eq_refl)) as Hdom.
      rewrite (out_source Hwf n e He), Htarget in Hdom; exact Hdom.
    + apply IH; [exact Htail|left; reflexivity].
Qed.

Local Lemma pre_block_member_dominates_last {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) b q default :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In q (points_in_block (pre_ssa_points a) b) ->
  dominates (live_graph (point_model (pre_ssa_points a))) q
    (last (points_in_block (pre_ssa_points a) b) default).
Proof.
  intros Hlaw Hb Hq; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  eapply pre_chain_member_dominates_last; [exact (points_graph_wf Hpoints)|
    exact (points_ordered Hpoints b Hb)| |exact Hq].
  intros e He; apply (pre_internal_source_dominates EV a e Hlaw).
  - exact (pre_instruction_edge_listed _ b e Hpoints Hb He).
  - exact (instruction_edges_internal Hpoints b e Hb He).
Qed.

Local Lemma pre_project_edges_spec {B BE N E V} (s : ssa_points B BE N E V) es be :
  In be (pre_project_edges s es) <->
  exists e, In e es /\ block_edge_of s e = Some be.
Proof.
  unfold pre_project_edges; rewrite in_flat_map; split.
  - intros [e [He Hin]]; destruct (block_edge_of s e) as [b|] eqn:Hbe;
      [|contradiction].
    destruct Hin as [Heq|Hfalse]; [subst b; exists e; auto|contradiction].
  - intros [e [He Hbe]]; exists e; split; [exact He|rewrite Hbe; left; reflexivity].
Qed.

Local Lemma pre_path_edges_listed {N E} (g : Graph.t N E) start es n :
  graph_wf g -> In start (Graph.nodes g) -> path g start es n -> incl es (edges_of g).
Proof.
  intros Hwf Hstart Hpath; revert Hstart.
  induction Hpath as [n|e es n He Hpath IH]; intros Hstart a Ha; [contradiction|].
  destruct Ha as [Heq|Ha].
  - subst a; apply in_flat_map; exists (Graph.source g e); auto.
  - apply IH; [exact (out_target_in Hwf _ e Hstart He)|exact Ha].
Qed.

Local Lemma pre_path_prefix_source {N E} (g : Graph.t N E) start es n e :
  path g start es n -> In e es ->
  exists prefix, path g start prefix (Graph.source g e) /\ incl prefix es.
Proof.
  intro Hpath; induction Hpath as [n|a es n Ha Hpath IH]; intro He; [contradiction|].
  destruct He as [Heq|He].
  - subst a; exists []; split; [constructor|intros x Hfalse; contradiction].
  - destruct (IH He) as [prefix [Hprefix Hincl]]; exists (a :: prefix); split.
    + constructor; assumption.
    + intros x [Heq|Hx]; [left; exact Heq|right; apply Hincl; exact Hx].
Qed.

Local Lemma pre_path_leaves {N E} (g : Graph.t N E) start es n b :
  path g start es n -> b <> n ->
  (b = start \/ exists e, In e es /\ Graph.target g e = b) ->
  exists e, In e es /\ Graph.source g e = b.
Proof.
  intro Hpath; induction Hpath as [n|e es n He Hpath IH]; intros Hdifferent Hvisit.
  - destruct Hvisit as [Heq|[e [Hfalse Htarget]]]; [congruence|contradiction].
  - destruct Hvisit as [Heq|[a [[Heq|Ha] Htarget]]].
    + exists e; split; [left; reflexivity|symmetry; exact Heq].
    + subst a; destruct (IH Hdifferent (or_introl (eq_sym Htarget))) as [a [Ha Hsource]].
      exists a; split; [right; exact Ha|exact Hsource].
    + destruct (IH Hdifferent (or_intror (ex_intro _ a (conj Ha Htarget))))
        as [a' [Ha' Hsource]].
      exists a'; split; [right; exact Ha'|exact Hsource].
Qed.

Local Lemma pre_block_point_dominates {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) b q n :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In q (points_in_block (pre_ssa_points a) b) -> b <> block_of_point (pre_ssa_points a) n ->
  dominates (block_graph (pre_ssa_points a)) b (block_of_point (pre_ssa_points a) n) ->
  dominates (live_graph (point_model (pre_ssa_points a))) q n.
Proof.
  intros Hlaw Hb Hq Hdifferent Hdom start es Hstart Hpath.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hblocks [Hentries Hfirst]]]].
  rewrite Hentries in Hstart; destruct Hstart as [Heq|Hfalse]; [subst start|contradiction].
  assert (Hentry : In first (Graph.entries (live_graph (point_model (pre_ssa_points a))))).
  { rewrite Hentries; left; reflexivity. }
  assert (Hentryblock : In entry (Graph.nodes (block_graph (pre_ssa_points a)))).
  { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hblocks; left; reflexivity. }
  assert (Howner : block_of_point (pre_ssa_points a) first = entry).
  { exact (points_owner Hpoints entry first Hentryblock (nth_error_In _ _ Hfirst)). }
  pose proof (pre_project_path _ first es n Hpoints
    (entries_in (points_graph_wf Hpoints) first Hentry) Hpath) as Hprojected.
  assert (Hentryowner : In (block_of_point (pre_ssa_points a) first)
    (Graph.entries (block_graph (pre_ssa_points a)))).
  { rewrite Howner, Hblocks; left; reflexivity. }
  destruct (pre_path_leaves _ _ _ _ b Hprojected Hdifferent
    (Hdom _ _ Hentryowner Hprojected)) as [be [Hbe Hsource]].
  apply pre_project_edges_spec in Hbe; destruct Hbe as [e [He Hbe]].
  pose proof (pre_path_edges_listed _ first es n (points_graph_wf Hpoints)
    (entries_in (points_graph_wf Hpoints) first Hentry) Hpath e He) as Hlisted.
  apply in_flat_map in Hlisted; destruct Hlisted as [source [Hsourcepoint Hedge]].
  pose proof (out_source (points_graph_wf Hpoints) source e Hedge) as Hsourceeq.
  subst source.
  pose proof (point_edge_projection Hpoints _ e Hsourcepoint Hedge) as Hprojection.
  rewrite Hbe in Hprojection; destruct Hprojection as [Hedge' [Htarget [Hlast Hfirst']]].
  pose proof (out_source (blocks_graph_wf Hpoints) _ be Hedge') as Hsourceblock.
  rewrite Hsource in Hsourceblock; rewrite <- Hsourceblock in Hlast.
  pose proof (pre_block_member_dominates_last EV a b q
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) Hlaw Hb Hq) as Hdomsource.
  rewrite Hlast in Hdomsource.
  destruct (pre_path_prefix_source _ first es n e Hpath He) as [prefix [Hprefix Hincl]].
  destruct (Hdomsource first prefix Hentry Hprefix) as [Heq|[earlier [Hearlier Heq]]].
  - left; exact Heq.
  - right; exists earlier; split; [apply Hincl; exact Hearlier|exact Heq].
Qed.

Local Lemma pre_chain_path {N E} (g : Graph.t N E) ns es first default :
  graph_wf g -> point_chain g ns es -> nth_error ns 0 = Some first ->
  path g first es (last ns default).
Proof.
  intros Hwf Hchain; revert first.
  induction Hchain as [n|n m ns e es He Htarget Hchain IH]; intros first Hfirst;
    cbn in Hfirst; inversion Hfirst; subst first.
  - constructor.
  - change (path g n (e :: es) (last (m :: ns) default)).
    rewrite <- (out_source Hwf n e He); constructor.
    + rewrite (out_source Hwf n e He); exact He.
    + rewrite Htarget; apply IH; reflexivity.
Qed.

Local Lemma pre_chain_prefix {N E} (g : Graph.t N E) ns es first :
  graph_wf g -> point_chain g ns es -> nth_error ns 0 = Some first ->
  forall n, In n ns -> exists prefix, path g first prefix n /\ incl prefix es.
Proof.
  intros Hwf Hchain; revert first.
  induction Hchain as [n|n m ns e es He Htarget Hchain IH]; intros first Hfirst q Hq;
    cbn in Hfirst; inversion Hfirst; subst first.
  - destruct Hq as [Heq|Hfalse]; [subst q|contradiction].
    exists []; split; [constructor|intros a Hfalse; contradiction].
  - destruct Hq as [Heq|Hq].
    + subst q; exists []; split; [constructor|intros a Hfalse; contradiction].
    + destruct (IH m eq_refl q Hq) as [prefix [Hprefix Hincl]].
      exists (e :: prefix); split.
      * rewrite <- (out_source Hwf n e He); constructor.
        -- rewrite (out_source Hwf n e He); exact He.
        -- rewrite Htarget; exact Hprefix.
      * intros a [Heq|Ha]; [left; exact Heq|right; apply Hincl; exact Ha].
Qed.

Local Lemma pre_project_edges_app {B BE N E V} (s : ssa_points B BE N E V) xs ys :
  pre_project_edges s (xs ++ ys) = pre_project_edges s xs ++ pre_project_edges s ys.
Proof.
  unfold pre_project_edges; apply flat_map_app.
Qed.

Local Lemma pre_project_internal {B BE N E V} (s : ssa_points B BE N E V) es :
  (forall e, In e es -> block_edge_of s e = None) -> pre_project_edges s es = [].
Proof.
  intro Hinternal; revert Hinternal; induction es as [|e es IH]; intro Hinternal;
    [reflexivity|].
  unfold pre_project_edges; cbn [flat_map]; rewrite (Hinternal e (or_introl eq_refl)).
  apply IH; intros a Ha; apply Hinternal; right; exact Ha.
Qed.

Local Lemma pre_lift_block_edge {B BE N E V} (s : ssa_points B BE N E V) be first :
  ssa_point_laws s -> In be (edges_of (block_graph s)) ->
  nth_error (points_in_block s (Graph.source (block_graph s) be)) 0 = Some first ->
  exists es next, path (live_graph (point_model s)) first es next /\
    nth_error (points_in_block s (Graph.target (block_graph s) be)) 0 = Some next /\
    pre_project_edges s es = [be].
Proof.
  intros Hlaw Hbe Hfirst.
  destruct (block_edge_covered Hlaw be Hbe) as [n [e [Hn [He Hprojection]]]].
  pose proof (point_edge_projection Hlaw n e Hn He) as Hpoint.
  rewrite Hprojection in Hpoint; destruct Hpoint as [Hedge [Htarget [Hlast Hnext]]].
  pose proof (out_source (blocks_graph_wf Hlaw) _ be Hedge) as Hsource.
  destruct (pre_point_owner_listed s n Hlaw Hn) as [Hb Hmember].
  rewrite <- Hsource in Hb, Hlast.
  exists (instruction_edges s (Graph.source (block_graph s) be) ++ [e]),
    (Graph.target (live_graph (point_model s)) e); split.
  - eapply path_snoc with (v := n).
    + rewrite <- Hlast; apply pre_chain_path.
      * exact (points_graph_wf Hlaw).
      * exact (points_ordered Hlaw _ Hb).
      * exact Hfirst.
    + symmetry; exact (out_source (points_graph_wf Hlaw) n e He).
    + exact He.
  - split; [exact Hnext|]; rewrite pre_project_edges_app.
    rewrite pre_project_internal.
    + unfold pre_project_edges; cbn [flat_map]; rewrite Hprojection; reflexivity.
    + intros a Ha; exact (instruction_edges_internal Hlaw _ a Hb Ha).
Qed.

Local Lemma pre_lift_block_path {B BE N E V} (s : ssa_points B BE N E V) b bes c :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) -> path (block_graph s) b bes c ->
  forall first, nth_error (points_in_block s b) 0 = Some first ->
  exists es next, path (live_graph (point_model s)) first es next /\
    nth_error (points_in_block s c) 0 = Some next /\ pre_project_edges s es = bes.
Proof.
  intros Hlaw Hb Hpath; revert Hb.
  induction Hpath as [b|be bes c Hbe Hpath IH]; intros Hb first Hfirst.
  - exists [], first; split; [constructor|auto].
  - assert (Hlisted : In be (edges_of (block_graph s))).
    { apply in_flat_map; exists (Graph.source (block_graph s) be); auto. }
    destruct (pre_lift_block_edge s be first Hlaw Hlisted Hfirst)
      as [prefix [mid [Hprefix [Hmid Hprojected]]]].
    destruct (IH (out_target_in (blocks_graph_wf Hlaw) _ be Hb Hbe) mid Hmid)
      as [suffix [last [Hsuffix [Hlast Hprojected']]]].
    exists (prefix ++ suffix), last; split.
    + eapply idf_path_app; eassumption.
    + split; [exact Hlast|rewrite pre_project_edges_app, Hprojected, Hprojected'; reflexivity].
Qed.

Local Lemma pre_point_visit_owner {B BE N E V} (s : ssa_points B BE N E V) start es n q :
  ssa_point_laws s -> In start (Graph.nodes (live_graph (point_model s))) ->
  path (live_graph (point_model s)) start es n ->
  (q = start \/ exists e, In e es /\ Graph.target (live_graph (point_model s)) e = q) ->
  block_of_point s q = block_of_point s start \/
    exists be, In be (pre_project_edges s es) /\
      Graph.target (block_graph s) be = block_of_point s q.
Proof.
  intros Hlaw Hstart Hpath [Heq|[e [He Htarget]]]; [subst q; left; reflexivity|].
  destruct (path_prefix_target _ start es n e Hpath He) as [prefix [Hprefix Hincl]].
  pose proof (pre_project_path s start prefix _ Hlaw Hstart Hprefix) as Hprojected.
  rewrite Htarget in Hprojected.
  destruct (path_endpoint _ _ _ _ Hprojected) as [Heq|[be [Hbe Htarget']]].
  - left; exact Heq.
  - right; exists be; split; [|exact Htarget'].
    apply pre_project_edges_spec in Hbe; destruct Hbe as [pe [Hpe Hbe]].
    apply pre_project_edges_spec; exists pe; split; [apply Hincl; exact Hpe|exact Hbe].
Qed.

Local Lemma pre_point_block_dominates {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) q n :
  pre_expr_ssa_laws EV a -> In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
  dominates (live_graph (point_model (pre_ssa_points a))) q n ->
  dominates (block_graph (pre_ssa_points a)) (block_of_point (pre_ssa_points a) q)
    (block_of_point (pre_ssa_points a) n).
Proof.
  intros Hlaw Hn Hdom start bes Hstart Hpath.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hblocks [Hentries Hfirst]]]].
  rewrite Hblocks in Hstart; destruct Hstart as [Heq|Hfalse]; [subst start|contradiction].
  assert (Hentry : In entry (Graph.nodes (block_graph (pre_ssa_points a)))).
  { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hblocks; left; reflexivity. }
  destruct (pre_lift_block_path _ entry bes _ Hpoints Hentry Hpath first Hfirst)
    as [prefix [mid [Hprefix [Hmid Hprojected]]]].
  destruct (pre_point_owner_listed _ n Hpoints Hn) as [Hb Hmember].
  destruct (pre_chain_prefix _ _ _ mid (points_graph_wf Hpoints)
    (points_ordered Hpoints _ Hb) Hmid n Hmember) as [suffix [Hsuffix Hincl]].
  assert (Hprojected' : pre_project_edges (pre_ssa_points a) suffix = []).
  { apply pre_project_internal; intros e He.
    exact (instruction_edges_internal Hpoints _ e Hb (Hincl e He)). }
  assert (Hpointentry : In first (Graph.entries (live_graph (point_model (pre_ssa_points a))))).
  { rewrite Hentries; left; reflexivity. }
  assert (Hcombined : path (live_graph (point_model (pre_ssa_points a))) first
    (prefix ++ suffix) n) by (eapply idf_path_app; eassumption).
  destruct (pre_point_visit_owner _ first (prefix ++ suffix) n q Hpoints
    (entries_in (points_graph_wf Hpoints) first Hpointentry) Hcombined
    (Hdom first _ Hpointentry Hcombined)) as [Howner|[be [Hbe Htarget]]].
  - left; rewrite Howner; exact (points_owner Hpoints entry first Hentry (nth_error_In _ _ Hfirst)).
  - right; exists be; split; [|exact Htarget].
    rewrite pre_project_edges_app, Hprojected, Hprojected', app_nil_r in Hbe; exact Hbe.
Qed.

Local Lemma pre_path_dominance_chain {N E} (g : Graph.t N E) start es n :
  path g start es n ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
  dominates g start n.
Proof.
  intro Hpath; induction Hpath as [n|e es n He Hpath IH]; intro Hedges.
  - apply dominates_refl.
  - eapply dominates_trans; [apply Hedges; left; reflexivity|].
    apply IH; intros a Ha; apply Hedges; right; exact Ha.
Qed.

Local Lemma pre_nth_error_unique {X} (xs : list X) i j x :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof.
  intros Hnodup Hi Hj; apply (proj1 (NoDup_nth_error xs) Hnodup).
  - apply nth_error_Some; congruence.
  - congruence.
Qed.

Local Lemma pre_chain_index_dominates {N E} (g : Graph.t N E) ns es :
  graph_wf g -> point_chain g ns es ->
  (forall e, In e es -> dominates g (Graph.source g e) (Graph.target g e)) ->
  forall i j q n, nth_error ns i = Some q -> nth_error ns j = Some n -> i <= j ->
    dominates g q n.
Proof.
  intros Hwf Hchain; induction Hchain as [head|head next ns e es He Htarget Hchain IH];
    intros Hedges i j q n Hq Hn Horder.
  - assert (Hi : i < length [head]) by (apply nth_error_Some; congruence).
    assert (Hj : j < length [head]) by (apply nth_error_Some; congruence).
    cbn [length] in Hi, Hj; assert (Hi0 : i = 0) by lia; assert (Hj0 : j = 0) by lia.
    subst i j; cbn in Hq, Hn.
    inversion Hq; inversion Hn; subst; apply dominates_refl.
  - destruct i as [|i].
    + cbn in Hq; inversion Hq; subst q.
      destruct (pre_chain_prefix g _ _ head Hwf
        (point_chain_step head next ns e es He Htarget Hchain) eq_refl n
        (nth_error_In _ _ Hn)) as [prefix [Hprefix Hincl]].
      apply (pre_path_dominance_chain g head prefix n Hprefix).
      intros a Ha; apply Hedges; apply Hincl; exact Ha.
    + destruct j as [|j]; [lia|].
      apply (IH ltac:(intros a Ha; apply Hedges; right; exact Ha) i j q n Hq Hn); lia.
Qed.

Local Lemma pre_block_instruction_order {S O B BE N E V K C U} (EN : encoding N)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) b i j q n :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) i = Some q ->
  nth_error (points_in_block (pre_ssa_points a) b) j = Some n ->
  (dominates (live_graph (point_model (pre_ssa_points a))) q n <-> i <= j).
Proof.
  intros Hlaw Hready Hb Hq Hn; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  assert (Hforward : forall k l x y,
    nth_error (points_in_block (pre_ssa_points a) b) k = Some x ->
    nth_error (points_in_block (pre_ssa_points a) b) l = Some y -> k <= l ->
    dominates (live_graph (point_model (pre_ssa_points a))) x y).
  { apply (pre_chain_index_dominates _ _ (instruction_edges (pre_ssa_points a) b));
      [exact (points_graph_wf Hpoints)|
      exact (points_ordered Hpoints b Hb)|].
    intros e He; apply (pre_internal_source_dominates EV a e Hlaw).
    - exact (pre_instruction_edge_listed _ b e Hpoints Hb He).
    - exact (instruction_edges_internal Hpoints b e Hb He). }
  split; [|exact (Hforward i j q n Hq Hn)].
  intro Hdom; destruct (Nat.le_gt_cases i j) as [Hle|Hgt]; [exact Hle|].
  assert (Heq : q = n).
  { apply (idf_dominance_antisym EN _ _ Hready q n).
    - apply (pre_expr_reachable_points EV a Hlaw); apply (points_covered Hpoints).
      exists b; split; [exact Hb|exact (nth_error_In _ _ Hq)].
    - apply (pre_expr_reachable_points EV a Hlaw); apply (points_covered Hpoints).
      exists b; split; [exact Hb|exact (nth_error_In _ _ Hn)].
    - exact Hdom.
    - apply (Hforward j i n q Hn Hq); lia. }
  subst n; pose proof (pre_nth_error_unique _ i j q (points_unique Hpoints b) Hq Hn); lia.
Qed.

(** * Frontier coverage of expression alterations *)

Local Lemma pre_occurrence_blocks_wf {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u :
  FinSet.wf EB (pre_group_lookup EU (pre_occurrence_blocks EB EU a) u).
Proof.
  unfold pre_occurrence_blocks; apply pre_group_fold_wf.
  intro v; unfold pre_group_lookup; rewrite Map.get_empty; apply Map.wf_empty.
Qed.

Local Lemma pre_occurrence_blocks_spec {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u b :
  FinSet.mem EB b (pre_group_lookup EU (pre_occurrence_blocks EB EU a) u) = true <->
  exists e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u = true /\
    block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e) = b.
Proof.
  unfold pre_occurrence_blocks; rewrite pre_group_fold_exact.
  unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty, in_flat_map; split.
  - intros [[e [He Hin]]|Hfalse]; [|discriminate].
    destruct (pre_recomputed (pre_expression a) e) as [v|] eqn:Hcomputed;
      [|contradiction].
    destruct (pre_total_pure (pre_expression a) v) eqn:Hpure; [|contradiction].
    destruct Hin as [Heq|Hfalse]; [inversion Heq; subst v b; exists e; auto|contradiction].
  - intros [e [He [Hcomputed [Hpure Hblock]]]]; left; exists e; split; [exact He|].
    rewrite Hcomputed, Hpure, Hblock; left; reflexivity.
Qed.

Local Lemma frg_defs_spec {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u b :
  In b (frg_defs EB EU a u) <->
    (exists e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
      pre_recomputed (pre_expression a) e = Some u /\
      pre_total_pure (pre_expression a) u = true /\
      block_of_point (pre_ssa_points a)
        (Graph.source (live_graph (point_model (pre_ssa_points a))) e) = b) \/
    In b (Graph.entries (block_graph (pre_ssa_points a))) \/
    exists x, home (pre_ssa_view a) x = b /\ In x (pre_operands a u).
Proof.
  unfold frg_defs.
  rewrite (FinSet.elements_spec EB).
  2: { apply FinSet.wf_union; [apply pre_occurrence_blocks_wf|].
       apply FinSet.wf_union; apply FinSet.wf_fold_add; apply Map.wf_empty. }
  rewrite !FinSet.mem_union.
  fold (pre_group_lookup EU (pre_occurrence_blocks EB EU a) u).
  rewrite pre_occurrence_blocks_spec, !FinSet.of_list_spec, in_map_iff.
  reflexivity.
Qed.

Local Lemma pre_operand_frontier_phi {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u x b :
  pre_expr_in_family a u -> In x (pre_operands a u) ->
  in_df (block_graph (pre_ssa_points a)) (home (pre_ssa_view a) x) b ->
  frg_phi_needed EB EU a u b.
Proof.
  intros Hfamily Hoperand Hfrontier; eapply frg_phi_seed; [exact Hfamily| |exact Hfrontier].
  apply frg_defs_spec; right; right; exists x; auto.
Qed.

Local Lemma pre_kill_frontier_phi {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) u e b :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  kill (pre_genkill (pre_expression a)) e u = true ->
  in_df (block_graph (pre_ssa_points a))
    (block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) b ->
  frg_phi_needed EB EU a u b.
Proof.
  intros Hlaw Hfamily He Hkill Hfrontier.
  destruct (pre_expr_kill_operand EV a Hlaw e u He Hfamily Hkill) as [x [Hx Hdef]].
  pose proof (pre_expr_def_home EV a Hlaw e x He Hdef) as Hhome.
  apply (pre_operand_frontier_phi EB EU a u x b Hfamily Hx).
  rewrite Hhome; exact Hfrontier.
Qed.

Local Lemma pre_chain_source_member {N E} (g : Graph.t N E) ns es e :
  graph_wf g -> point_chain g ns es -> In e es -> In (Graph.source g e) ns.
Proof.
  intros Hwf Hchain He; destruct (pre_chain_edge_source g ns es e Hchain He)
    as [n [Hn Hedge]].
  rewrite (out_source Hwf n e Hedge); exact Hn.
Qed.

Local Lemma pre_chain_source_unique {N E} (g : Graph.t N E) ns es :
  graph_wf g -> point_chain g ns es -> NoDup ns ->
  forall e e', In e es -> In e' es -> Graph.source g e = Graph.source g e' -> e = e'.
Proof.
  intros Hwf Hchain; induction Hchain as [n|n m ns a es Ha Htarget Hchain IH];
    intros Hnodup e e' He He' Heq; [contradiction|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  destruct He as [He|He], He' as [He'|He'].
  - congruence.
  - subst e; exfalso; apply Hfresh; rewrite <- (out_source Hwf n a Ha), Heq.
    exact (pre_chain_source_member g _ _ e' Hwf Hchain He').
  - subst e'; exfalso; apply Hfresh; rewrite <- (out_source Hwf n a Ha), <- Heq.
    exact (pre_chain_source_member g _ _ e Hwf Hchain He).
  - exact (IH Htail e e' He He' Heq).
Qed.

Local Lemma pre_chain_last_member {N E} (g : Graph.t N E) ns es default :
  point_chain g ns es -> In (last ns default) ns.
Proof.
  intro Hchain; induction Hchain as [n|n m ns e es He Htarget Hchain IH].
  - left; reflexivity.
  - right; exact IH.
Qed.

Local Lemma pre_chain_first_edge {N E} (g : Graph.t N E) ns es first parameter :
  point_chain g ns es -> NoDup ns -> nth_error ns 0 = Some first ->
  nth_error es 0 = Some parameter ->
  In parameter (Graph.out g first) /\ last ns first <> first.
Proof.
  intros Hchain; destruct Hchain as [n|n m ns e es He Htarget Hchain];
    intros Hnodup Hfirst Hparameter; [discriminate|].
  cbn in Hfirst, Hparameter; inversion Hfirst; inversion Hparameter; subst first parameter.
  split; [exact He|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Htail].
  change (last (m :: ns) n <> n); intro Hlast; apply Hfresh.
  rewrite <- Hlast; exact (pre_chain_last_member g _ _ n Hchain).
Qed.

Local Lemma pre_first_out_parameter {B BE N E V} (s : ssa_points B BE N E V) b first e :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  nth_error (points_in_block s b) 0 = Some first ->
  In e (Graph.out (live_graph (point_model s)) first) -> e = parameter_edge s b.
Proof.
  intros Hlaw Hb Hfirst He.
  pose proof (points_ordered Hlaw b Hb) as Hchain.
  pose proof (parameter_edge_first Hlaw b Hb) as Hparameter.
  destruct (pre_chain_first_edge _ _ _ first _ Hchain (points_unique Hlaw b)
    Hfirst Hparameter) as [Hparameterout Hlast].
  pose proof (points_owner Hlaw b first Hb (nth_error_In _ _ Hfirst)) as Howner.
  assert (Hlisted : In first (Graph.nodes (live_graph (point_model s)))).
  { apply (points_covered Hlaw); exists b; split; [exact Hb|exact (nth_error_In _ _ Hfirst)]. }
  destruct (block_edge_of s e) as [be|] eqn:Hbe.
  - pose proof (point_edge_projection Hlaw first e Hlisted He) as Hprojection.
    rewrite Hbe in Hprojection; destruct Hprojection as [Hedge [Htarget [Hending Hnext]]].
    rewrite Howner in Hending; contradiction.
  - pose proof (instruction_edges_complete Hlaw first e Hlisted He Hbe) as Hin.
    rewrite Howner in Hin; eapply pre_chain_source_unique.
    + exact (points_graph_wf Hlaw).
    + exact Hchain.
    + exact (points_unique Hlaw b).
    + exact Hin.
    + exact (nth_error_In _ _ Hparameter).
    + rewrite (out_source (points_graph_wf Hlaw) first e He),
        (out_source (points_graph_wf Hlaw) first _ Hparameterout); reflexivity.
Qed.

Local Lemma pre_listed_edge_out {N E} (g : Graph.t N E) e : graph_wf g ->
  In e (edges_of g) -> In (Graph.source g e) (Graph.nodes g) /\
    In e (Graph.out g (Graph.source g e)).
Proof.
  intros Hwf He; apply in_flat_map in He; destruct He as [n [Hn He]].
  rewrite (out_source Hwf n e He); auto.
Qed.

(* Real computations and incoming-operand positions occur after the block's parameter edge. *)
Local Definition pre_observed_point {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (n : N) : Prop :=
  (exists e u, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    Graph.source (live_graph (point_model (pre_ssa_points a))) e = n /\
    pre_recomputed (pre_expression a) e = Some u) \/
  (exists e be, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    Graph.source (live_graph (point_model (pre_ssa_points a))) e = n /\
    block_edge_of (pre_ssa_points a) e = Some be).

Local Lemma pre_observed_not_first {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) b first n :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  pre_observed_point a n -> n <> first.
Proof.
  intros Hlaw Hb Hfirst Hobserved Heq; subst n.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct Hobserved as [[e [u [He [Hsource Hcomputed]]]]|[e [be [He [Hsource Hbe]]]]].
  - destruct (pre_listed_edge_out _ e (points_graph_wf Hpoints) He) as [Hnode Hout].
    rewrite Hsource in Hout.
    pose proof (pre_first_out_parameter _ b first e Hpoints Hb Hfirst Hout) as Hparameter.
    exact (proj2 (pre_expr_real_internal EV a Hlaw e u Hcomputed) b Hparameter).
  - destruct (pre_listed_edge_out _ e (points_graph_wf Hpoints) He) as [Hnode Hout].
    rewrite Hsource in Hout.
    pose proof (pre_first_out_parameter _ b first e Hpoints Hb Hfirst Hout) as Hparameter.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [Hlisted Hinternal].
    rewrite Hparameter in Hbe; congruence.
Qed.

Local Lemma pre_parameter_point_on_path {B BE N E V} (s : ssa_points B BE N E V)
    b first es n : ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  nth_error (points_in_block s b) 0 = Some first ->
  path (live_graph (point_model s)) first es n -> n <> first ->
  exists e, In e es /\ Graph.target (live_graph (point_model s)) e =
    Graph.target (live_graph (point_model s)) (parameter_edge s b).
Proof.
  intros Hlaw Hb Hfirst Hpath Hdifferent; destruct Hpath as [n|e es n He Hpath].
  - contradiction.
  - pose proof (pre_first_out_parameter s b _ e Hlaw Hb Hfirst He) as Hparameter.
    exists e; split; [left; reflexivity|rewrite Hparameter; reflexivity].
Qed.

Local Lemma pre_observed_listed {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) n :
  pre_expr_ssa_laws EV a -> pre_observed_point a n ->
  In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))).
Proof.
  intros Hlaw Hobserved; pose proof (points_graph_wf (pre_expr_points EV a Hlaw)) as Hwf.
  destruct Hobserved as [[e [u [He [Hsource Hcomputed]]]]|[e [be [He [Hsource Hbe]]]]].
  - rewrite <- Hsource; exact (proj1 (pre_listed_edge_out _ e Hwf He)).
  - rewrite <- Hsource; exact (proj1 (pre_listed_edge_out _ e Hwf He)).
Qed.

Local Lemma pre_chain_first_target {N E} (g : Graph.t N E) ns es parameter :
  point_chain g ns es -> nth_error es 0 = Some parameter ->
  nth_error ns 1 = Some (Graph.target g parameter).
Proof.
  intro Hchain; destruct Hchain as [n|n m ns e es He Htarget Hchain]; intro Hparameter;
    [discriminate|].
  cbn in Hparameter; inversion Hparameter; subst parameter; cbn; f_equal; symmetry; exact Htarget.
Qed.

Local Lemma pre_parameter_target_position {B BE N E V} (s : ssa_points B BE N E V) b :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) ->
  nth_error (points_in_block s b) 1 =
    Some (Graph.target (live_graph (point_model s)) (parameter_edge s b)).
Proof.
  intros Hlaw Hb; eapply pre_chain_first_target; [exact (points_ordered Hlaw b Hb)|].
  exact (parameter_edge_first Hlaw b Hb).
Qed.

Local Lemma pre_phi_point_dominates {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) b n :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_observed_point a n ->
  dominates (block_graph (pre_ssa_points a)) b (block_of_point (pre_ssa_points a) n) ->
  dominates (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)) n.
Proof.
  intros Hlaw Hb Hobserved Hdom; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_parameter_target_position _ b Hpoints Hb) as Hphi.
  destruct (dfs_eq_dec EB b (block_of_point (pre_ssa_points a) n)) as [Heq|Hne].
  - destruct (pre_point_owner_listed _ n Hpoints (pre_observed_listed EV a n Hlaw Hobserved))
      as [Hblock Hmember].
    rewrite <- Heq in Hmember.
    destruct (In_nth_error _ _ Hmember) as [j Hn].
    destruct j as [|j].
    + exfalso; exact (pre_observed_not_first EV a b n n Hlaw Hb Hn Hobserved eq_refl).
    + eapply (pre_chain_index_dominates _ _ (instruction_edges (pre_ssa_points a) b)).
      * exact (points_graph_wf Hpoints).
      * exact (points_ordered Hpoints b Hb).
      * intros e He; apply (pre_internal_source_dominates EV a e Hlaw).
        -- exact (pre_instruction_edge_listed _ b e Hpoints Hb He).
        -- exact (instruction_edges_internal Hpoints b e Hb He).
      * exact Hphi.
      * exact Hn.
      * lia.
  - apply (pre_block_point_dominates EV a b _ n Hlaw Hb
      (nth_error_In _ _ Hphi) Hne Hdom).
Qed.

Local Lemma pre_phi_point_on_projected_path {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) start es n b be :
  pre_expr_ssa_laws EV a -> In start (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
  path (live_graph (point_model (pre_ssa_points a))) start es n -> pre_observed_point a n ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In be (pre_project_edges (pre_ssa_points a) es) ->
  Graph.target (block_graph (pre_ssa_points a)) be = b ->
  exists e, In e es /\ Graph.target (live_graph (point_model (pre_ssa_points a))) e =
    Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b).
Proof.
  intros Hlaw Hstart Hpath Hobserved Hb Hbe Htarget.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  apply pre_project_edges_spec in Hbe; destruct Hbe as [e [He Hbe]].
  pose proof (pre_path_edges_listed _ start es n (points_graph_wf Hpoints) Hstart Hpath e He)
    as Hlisted.
  destruct (pre_listed_edge_out _ e (points_graph_wf Hpoints) Hlisted) as [Hsource Hout].
  pose proof (point_edge_projection Hpoints _ e Hsource Hout) as Hprojection.
  rewrite Hbe in Hprojection; destruct Hprojection as [Hedge [Hblock [Hlast Hfirst]]].
  rewrite Htarget in Hfirst.
  destruct (loop_path_split _ start es n e Hpath He)
    as [prefix [suffix [Hprefix [Hsuffix Hsplit]]]].
  destruct (pre_parameter_point_on_path _ b _ suffix n Hpoints Hb Hfirst Hsuffix
    (pre_observed_not_first EV a b _ n Hlaw Hb Hfirst Hobserved)) as [aedge [Ha Htarget']].
  exists aedge; split; [rewrite <- Hsplit; apply in_or_app; right; exact Ha|exact Htarget'].
Qed.

Local Definition pre_strict_dom_dec {B BE} (EB : encoding B) (g : Graph.t B BE)
    (p : prepared EB g) (Hready : ready EB g p) b c (Hc : reachable g c) :
    {strictly_dominates g b c} + {~ strictly_dominates g b c}.
Proof.
  pose proof (proj1 (dominator_tree_exact EB g p Hready
    (dominator_exact_true EB g p Hready)) b c Hc) as Hexact.
  destruct (dominates_b EB (dominator_tree p) b c) eqn:Hdom.
  - destruct (dfs_eq_dec EB b c) as [Heq|Hne].
    + right; intros [Hdominates Hdifferent]; contradiction.
    + left; split; [apply Hexact; reflexivity|exact Hne].
  - right; intros [Hdominates Hdifferent]; apply Hexact in Hdominates; congruence.
Defined.

Local Lemma pre_frontier_track {B BE} (EB : encoding B) (g : Graph.t B BE)
    (p : prepared EB g) (Sphi : B -> Prop) d start es n :
  ready EB g p ->
  (forall b c, (b = d \/ Sphi b) -> in_df g b c -> Sphi c) ->
  path g start es n -> reachable g start -> forall root,
  (root = d \/ Sphi root) -> dominates g root start ->
  exists r, dominates g r n /\
    ((r = root /\ forall e, In e es -> strictly_dominates g root (Graph.target g e)) \/
     (Sphi r /\ exists e, In e es /\ Graph.target g e = r)).
Proof.
  intros Hready Hclosed Hpath; induction Hpath as [v|e es n He Hpath IH];
    intros Hreachable root Hroot Hdom.
  - exists root; split; [exact Hdom|left; split; [reflexivity|intros a Hfalse; contradiction]].
  - pose proof (reachable_step e Hreachable He) as Htarget.
    destruct (pre_strict_dom_dec EB g p Hready root _ Htarget) as [Hstrict|Hnot].
    + destruct (IH Htarget root Hroot (proj1 Hstrict)) as [r [Hr [Hsame|Hphi]]].
      * exists r; split; [exact Hr|left].
        destruct Hsame as [Heq Hall]; split; [exact Heq|].
        intros a [Heq'|Ha]; [subst a; exact Hstrict|apply Hall; exact Ha].
      * exists r; split; [exact Hr|right].
        destruct Hphi as [Hphi [a [Ha Htarget']]]; split; [exact Hphi|].
        exists a; split; [right; exact Ha|exact Htarget'].
    + assert (Hphi : Sphi (Graph.target g e)).
      { apply (Hclosed root _ Hroot); exists e; repeat split; assumption || reflexivity. }
      destruct (IH Htarget (Graph.target g e) (or_intror Hphi) (dominates_refl g _))
        as [r [Hr [[Heq Hall]|[Hphi' [a [Ha Htarget']]]]]].
      * exists r; split; [exact Hr|right]; subst r; split; [exact Hphi|].
        exists e; split; [left; reflexivity|reflexivity].
      * exists r; split; [exact Hr|right]; split; [exact Hphi'|].
        exists a; split; [right; exact Ha|exact Htarget'].
Qed.

(** * Reusable versions and dominating alterations *)

Local Lemma pre_path_last_visit {N E} (EN : encoding N) (g : Graph.t N E) q start es n :
  path g start es n ->
  (q = start \/ exists e, In e es /\ Graph.target g e = q) ->
  exists suffix, path g q suffix n /\ incl suffix es /\
    Forall (fun e => Graph.target g e <> q) suffix.
Proof.
  intro Hpath; induction Hpath as [n|e es n He Hpath IH]; intro Hvisit.
  - destruct Hvisit as [Heq|[e [Hfalse Htarget]]]; [subst q|contradiction].
    exists []; split; [constructor|split; [intros a Hfalse; contradiction|constructor]].
  - destruct (path_occurrence_dec EN g q (Graph.target g e) es) as [Htail|[Hdifferent Hclear]].
    + destruct (IH Htail) as [suffix [Hsuffix [Hincl Hfree]]].
      exists suffix; split; [exact Hsuffix|]; split; [|exact Hfree].
      intros a Ha; right; apply Hincl; exact Ha.
    + destruct Hvisit as [Heq|[a [[Heq|Ha] Htarget]]].
      * subst q; exists (e :: es); split; [constructor; assumption|]; split.
        -- intros a Ha; exact Ha.
        -- apply Forall_forall; intros a [Heq|Ha]; [subst a; congruence|apply Hclear; exact Ha].
      * subst a; congruence.
      * exfalso; exact (Hclear a Ha Htarget).
Qed.

Local Lemma pre_dominating_path {N E} (EN : encoding N) (g : Graph.t N E) q n :
  reachable g n -> dominates g q n ->
  exists es, path g q es n /\ Forall (fun e => Graph.target g e <> q) es.
Proof.
  intros Hn Hdom; apply reachable_iff_path in Hn; destruct Hn as [start [es [Hentry Hpath]]].
  destruct (pre_path_last_visit EN g q start es n Hpath (Hdom start es Hentry Hpath))
    as [suffix [Hsuffix [Hincl Hfree]]].
  exists suffix; auto.
Qed.

Local Lemma pre_dominance_suffix {N E} (g : Graph.t N E) q start es n :
  dominates g q n -> path g start es n ->
  Forall (fun e => Graph.target g e <> q) es -> dominates g q start.
Proof.
  intros Hdom Hpath Hfree entry prefix Hentry Hprefix.
  assert (Hcombined : path g entry (prefix ++ es) n) by (eapply idf_path_app; eassumption).
  destruct (Hdom entry _ Hentry Hcombined) as [Heq|[e [He Htarget]]]; [left; exact Heq|].
  apply in_app_iff in He; destruct He as [He|He].
  - right; exists e; auto.
  - exfalso; exact (proj1 (Forall_forall _ _) Hfree e He Htarget).
Qed.

Local Lemma pre_nearest_path_excludes_definition {S O B BE N E V K C U}
    (EN : encoding N) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) u n d q d' q' es :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  frg_nearest_version a f u n d -> frg_version_point a d = Some q ->
  In d' (frg_versions f) -> frg_version_expr d' = u -> frg_version_point a d' = Some q' ->
  dominates (live_graph (point_model (pre_ssa_points a))) q' n ->
  path (live_graph (point_model (pre_ssa_points a))) q es n ->
  Forall (fun e => Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q) es ->
  (exists e, In e es /\ Graph.target (live_graph (point_model (pre_ssa_points a))) e = q') ->
  False.
Proof.
  intros Hready Hn [Hd [Hexpr [position [Hposition [Hdom Hnearest]]]]] Hq
    Hd' Hexpr' Hq' Hdom' Hpath Hfree [e [He Htarget]].
  assert (Heq : position = q) by congruence; subst position.
  pose proof (Hnearest d' q' Hd' Hexpr' Hq' Hdom') as Hback.
  destruct (loop_path_split _ q es n e Hpath He) as [prefix [suffix [Hprefix [Hsuffix Hsplit]]]].
  rewrite Htarget in Hsuffix.
  assert (Hsuffixfree : Forall (fun e =>
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q) suffix).
  { pose proof Hfree as Hboth; rewrite <- Hsplit in Hboth; apply Forall_app in Hboth.
    exact (proj2 Hboth). }
  pose proof (pre_dominance_suffix _ q q' suffix n Hdom Hsuffix Hsuffixfree) as Hforward.
  assert (Heq : q = q').
  { apply (idf_dominance_antisym EN _ _ Hready q q').
    - exact (dom_dominator_reachable _ q n Hn Hdom).
    - exact (dom_dominator_reachable _ q' n Hn Hdom').
    - exact Hforward.
    - exact Hback. }
  exact (proj1 (Forall_forall _ _) Hfree e He ltac:(congruence)).
Qed.

Local Lemma pre_kill_internal {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e u :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  kill (pre_genkill (pre_expression a)) e u = true -> block_edge_of (pre_ssa_points a) e = None.
Proof.
  intros Hlaw Hfamily He Hkill.
  destruct (pre_expr_kill_operand EV a Hlaw e u He Hfamily Hkill) as [x [Hx Hdef]].
  destruct (block_edge_of (pre_ssa_points a) e) as [be|] eqn:Hbe; [|reflexivity].
  rewrite (pre_expr_cross_no_defs EV a Hlaw e be He Hbe) in Hdef; contradiction.
Qed.

Local Lemma pre_project_empty {B BE N E V} (s : ssa_points B BE N E V) es :
  pre_project_edges s es = [] -> forall e, In e es -> block_edge_of s e = None.
Proof.
  intros Hempty e He; destruct (block_edge_of s e) as [be|] eqn:Hbe; [|reflexivity].
  assert (Hin : In be (pre_project_edges s es)).
  { apply pre_project_edges_spec; exists e; auto. }
  rewrite Hempty in Hin; contradiction.
Qed.

Local Lemma pre_kill_reaching_boundary {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    u e suffix n :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_expr_in_family a u -> In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  kill (pre_genkill (pre_expression a)) e u = true ->
  path (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e) suffix n ->
  pre_observed_point a n ->
  dominates (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n \/
  exists b, frg_phi_needed EB EU a u b /\
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b)) n /\
    exists pe, In pe suffix /\ Graph.target (live_graph (point_model (pre_ssa_points a))) pe =
      Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) b).
Proof.
  intros Hlaw Hready Hfamily He Hkill Hpath Hobserved.
  set (s := pre_ssa_points a); set (pg := live_graph (point_model s)); set (bg := block_graph s).
  set (d := block_of_point s (Graph.source pg e)).
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_listed_edge_out pg e (points_graph_wf Hpoints) He) as [Hsource Hout].
  pose proof (out_target_in (points_graph_wf Hpoints) _ e Hsource Hout) as Htarget.
  destruct (pre_point_owner_listed s _ Hpoints Hsource) as [Hd Hsourcepoint].
  pose proof (point_edge_projection Hpoints _ e Hsource Hout) as Howner.
  rewrite (pre_kill_internal EV a e u Hlaw Hfamily He Hkill) in Howner.
  change (d = block_of_point s (Graph.target pg e)) in Howner.
  pose proof (pre_project_path s _ suffix n Hpoints Htarget Hpath) as Hprojected.
  change (path bg (block_of_point s (Graph.target pg e)) (pre_project_edges s suffix)
    (block_of_point s n)) in Hprojected.
  rewrite <- Howner in Hprojected.
  assert (Hclosed : forall root c, (root = d \/ frg_phi_needed EB EU a u root) ->
    in_df bg root c -> frg_phi_needed EB EU a u c).
  { intros root c [Heq|Hphi] Hfrontier.
    - subst root; exact (pre_kill_frontier_phi EB EV EU a u e c Hlaw Hfamily He Hkill Hfrontier).
    - eapply frg_phi_iter; eassumption. }
  destruct (pre_frontier_track EB bg (prepare EB bg) (frg_phi_needed EB EU a u) d d
    (pre_project_edges s suffix) (block_of_point s n) Hready Hclosed Hprojected
    (pre_expr_reachable_blocks EV a Hlaw d Hd) d (or_introl eq_refl) (dominates_refl bg d))
    as [root [Hdom [[Heq Hall]|[Hphi [be [Hbe Hblock]]]]]].
  - left; destruct (pre_project_edges s suffix) as [|be bes] eqn:Hedges.
    + apply (pre_path_dominance_chain pg _ suffix n Hpath); intros pe Hpe.
      apply (pre_internal_source_dominates EV a pe Hlaw).
      * exact (pre_path_edges_listed pg _ suffix n (points_graph_wf Hpoints)
          Htarget Hpath pe Hpe).
      * exact (pre_project_empty s suffix Hedges pe Hpe).
    + rewrite ?Hedges in Hprojected.
      destruct (semi_path_last bg d (be :: bes) _ Hprojected ltac:(discriminate))
        as [prefix [last [Hsplit [Hprefix [Hlast Hlasttarget]]]]].
      assert (Hstrict : strictly_dominates bg d (block_of_point s n)).
      { rewrite <- Hlasttarget; apply Hall; rewrite ?Hedges, Hsplit.
        apply in_or_app; right; left; reflexivity. }
      destruct (pre_point_owner_listed s _ Hpoints Htarget) as [Htargetblock Htargetpoint].
      change (In (Graph.target pg e)
        (points_in_block s (block_of_point s (Graph.target pg e)))) in Htargetpoint.
      rewrite <- Howner in Htargetpoint.
      exact (pre_block_point_dominates EV a d _ n Hlaw Hd Htargetpoint
        (proj2 Hstrict) (proj1 Hstrict)).
  - right; exists root; split; [exact Hphi|].
    pose proof (frg_phi_needed_nodes EB EU a u root (blocks_graph_wf Hpoints) Hphi) as Hroot.
    split; [exact (pre_phi_point_dominates EB EV a root n Hlaw Hroot Hobserved Hdom)|].
    exact (pre_phi_point_on_projected_path EV a _ suffix n root be Hlaw Htarget Hpath
      Hobserved Hroot Hbe Hblock).
Qed.

(* Alterations strictly below a definition and dominating the use are precisely local kills. *)
Local Definition pre_no_dominating_kill {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u q n : Prop :=
  forall e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    strictly_dominates (live_graph (point_model (pre_ssa_points a))) q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) ->
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n ->
    kill (pre_genkill (pre_expression a)) e u = false.

Local Lemma pre_reusable_of_dominating_kills {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n d q :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> pre_observed_point a n ->
  (forall b, frg_phi_needed EB EU a u b -> In (FrPhi b u) (frg_versions f)) ->
  frg_nearest_version a f u n d -> frg_version_point a d = Some q ->
  pre_no_dominating_kill a u q n -> frg_reusable a f u n d.
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hobserved Hphis Hnearest Hq Hkills.
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (pre_expr_reachable_points EV a Hlaw n
    (pre_observed_listed EV a n Hlaw Hobserved)) as Hreachable.
  destruct Hnearest as [Hd [Hexpr [position [Hposition [Hdom Hmax]]]]].
  assert (Heq : position = q) by congruence; subst position.
  assert (Hnearest : frg_nearest_version a f u n d).
  { split; [exact Hd|]; split; [exact Hexpr|exists q; auto]. }
  split; [exact Hnearest|exists q; split; [exact Hq|]].
  intros es Hpath Hfree; apply Forall_forall; intros e He.
  destruct (kill (pre_genkill (pre_expression a)) e u) eqn:Hkill; [|reflexivity].
  exfalso.
  pose proof (dom_dominator_reachable _ q n Hreachable Hdom) as Hqreachable.
  pose proof (reachable_in_nodes _ q (points_graph_wf Hssa) Hqreachable) as Hqlisted.
  pose proof (pre_path_edges_listed _ q es n (points_graph_wf Hssa) Hqlisted Hpath e He)
    as Hlisted.
  destruct (loop_path_split _ q es n e Hpath He) as [prefix [suffix [Hprefix [Hsuffix Hsplit]]]].
  assert (Hsuffixfree : Forall (fun e =>
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> q) suffix).
  { pose proof Hfree as Hboth; rewrite <- Hsplit in Hboth; apply Forall_app in Hboth.
    exact (proj2 Hboth). }
  destruct (pre_kill_reaching_boundary EB EV EU a u e suffix n Hlaw Hblocks Hfamily
    Hlisted Hkill Hsuffix Hobserved) as [Htargetdom|[b [Hphi [Hphidom [pe [Hpe Htarget]]]]]].
  - pose proof (pre_dominance_suffix _ q _ suffix n Hdom Hsuffix Hsuffixfree) as Hforward.
    assert (Hstrict : strictly_dominates (live_graph (point_model (pre_ssa_points a))) q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)).
    { split; [exact Hforward|].
      pose proof (proj1 (Forall_forall _ _) Hfree e He) as Hne; congruence. }
    pose proof (Hkills e Hlisted Hstrict Htargetdom); congruence.
  - eapply (pre_nearest_path_excludes_definition EN a f u n d q (FrPhi b u) _ es
      Hpoints Hreachable Hnearest Hq (Hphis b Hphi) eq_refl eq_refl Hphidom Hpath Hfree).
    exists pe; split; [rewrite <- Hsplit; apply in_or_app; right; exact Hpe|exact Htarget].
Qed.

Local Lemma pre_reusable_dominating_kills {S O B BE N E V K C U}
    (EN : encoding N) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) u n d q :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> reachable (live_graph (point_model (pre_ssa_points a))) n ->
  frg_reusable a f u n d -> frg_version_point a d = Some q ->
  pre_no_dominating_kill a u q n.
Proof.
  intros Hlaw Hready Hfamily Hreachable [Hnearest [safe_position [Hsafe_position Hsafe]]] Hq.
  destruct Hnearest as [Hd [Hexpr [position [Hposition [Hdom Hmax]]]]].
  assert (Heq : position = q) by congruence; subst position.
  assert (Heq : safe_position = q) by congruence; subst safe_position.
  intros e Hlisted Hstrict Htargetdom.
  destruct (kill (pre_genkill (pre_expression a)) e u) eqn:Hkill; [|reflexivity]; exfalso.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_kill_internal EV a e u Hlaw Hfamily Hlisted Hkill) as Hinternal.
  destruct (pre_dominating_path EN _ q n Hreachable Hdom) as [es [Hpath Hfree]].
  destruct (path_occurrence_dec EN (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e) q es)
    as [[Heq|[aedge [Ha Htarget]]]|[Hdifferent Hclear]].
  - exact (proj2 Hstrict (eq_sym Heq)).
  - pose proof (dom_dominator_reachable _ q n Hreachable Hdom) as Hqreachable.
    pose proof (pre_path_edges_listed _ q es n (points_graph_wf Hpoints)
      (reachable_in_nodes _ q (points_graph_wf Hpoints) Hqreachable) Hpath aedge Ha) as Halisted.
    pose proof (pre_internal_incoming_unique _ e aedge Hpoints Hlisted Hinternal
      Halisted Htarget) as Heq; subst aedge.
    pose proof (proj1 (Forall_forall _ _) (Hsafe es Hpath Hfree) e Ha); congruence.
  - assert (Hfree_target : Forall (fun aedge =>
      Graph.target (live_graph (point_model (pre_ssa_points a))) aedge <>
      Graph.target (live_graph (point_model (pre_ssa_points a))) e) es).
    { apply Forall_forall; exact Hclear. }
    pose proof (pre_dominance_suffix _ _ q es n Htargetdom Hpath Hfree_target) as Hback.
    apply (proj2 Hstrict).
    apply (idf_dominance_antisym EN _ _ Hready q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)).
    + exact (dom_dominator_reachable _ q n Hreachable Hdom).
    + exact (dom_dominator_reachable _ _ n Hreachable Htargetdom).
    + exact (proj1 Hstrict).
    + exact Hback.
Qed.

(** * Dominator-scope boundaries *)

Local Lemma pre_point_strict_dom_first {S O B BE N E V K C U} (EN : encoding N)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) b first q :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  strictly_dominates (live_graph (point_model (pre_ssa_points a))) q first ->
  strictly_dominates (block_graph (pre_ssa_points a)) (block_of_point (pre_ssa_points a) q) b.
Proof.
  intros Hlaw Hready Hb Hfirst [Hdom Hne]; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  assert (Hfirstlisted : In first (Graph.nodes (live_graph (point_model (pre_ssa_points a))))).
  { apply (points_covered Hpoints); exists b; split; [exact Hb|exact (nth_error_In _ _ Hfirst)]. }
  pose proof (pre_point_block_dominates EV a q first Hlaw Hfirstlisted Hdom) as Hblockdom.
  pose proof (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)) as Hownerfirst.
  rewrite Hownerfirst in Hblockdom; split; [exact Hblockdom|].
  intro Howner.
  pose proof (dom_dominator_reachable _ q first
    (pre_expr_reachable_points EV a Hlaw first Hfirstlisted) Hdom) as Hqreachable.
  destruct (pre_point_owner_listed _ q Hpoints
    (reachable_in_nodes _ q (points_graph_wf Hpoints) Hqreachable)) as [Hqb Hqmember].
  rewrite Howner in Hqmember; destruct (In_nth_error _ _ Hqmember) as [i Hi].
  pose proof (proj1 (pre_block_instruction_order EN EV a b i 0 q first Hlaw Hready
    Hb Hi Hfirst) Hdom) as Horder.
  assert (Hi0 : i = 0) by lia; subst i; apply Hne; congruence.
Qed.

Local Lemma pre_block_parent_immediate {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) b c first :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In c (Graph.nodes (block_graph (pre_ssa_points a))) ->
  Map.get EB c (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))) = Some b ->
  nth_error (points_in_block (pre_ssa_points a) c) 0 = Some first ->
  immediately_dominates (live_graph (point_model (pre_ssa_points a)))
    (last (points_in_block (pre_ssa_points a) b) first) first.
Proof.
  intros Hlaw Hblocks Hready Hb Hc Hparent Hfirst.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_chain_last_member _ _ _ first (points_ordered Hpoints b Hb)) as Hlast.
  pose proof (points_owner Hpoints b _ Hb Hlast) as Hownerlast.
  pose proof (points_owner Hpoints c first Hc (nth_error_In _ _ Hfirst)) as Hownerfirst.
  pose proof (proj1 (proj2 (dominator_tree_exact EB _ _ Hblocks
    (dominator_exact_true _ _ _ Hblocks))) b c
      (pre_expr_reachable_blocks EV a Hlaw c Hc)) as Hparentexact.
  apply Hparentexact in Hparent; destruct Hparent as [[Hblockdom Hblockne] Hblockmin].
  split.
  - split.
    + apply (pre_block_point_dominates EV a b _ first Hlaw Hb Hlast).
      * rewrite Hownerfirst; exact Hblockne.
      * rewrite Hownerfirst; exact Hblockdom.
    + intro Heq; rewrite Heq in Hownerlast; congruence.
  - intros q Hqstrict.
    pose proof (pre_point_strict_dom_first EN EV a c first q Hlaw Hready Hc Hfirst Hqstrict)
      as Hqblock.
    pose proof (Hblockmin _ Hqblock) as Hqparent.
    assert (Hfirstlisted : In first
      (Graph.nodes (live_graph (point_model (pre_ssa_points a))))).
    { apply (points_covered Hpoints); exists c; split; [exact Hc|exact (nth_error_In _ _ Hfirst)]. }
    pose proof (dom_dominator_reachable _ q first
      (pre_expr_reachable_points EV a Hlaw first Hfirstlisted) (proj1 Hqstrict)) as Hqreachable.
    destruct (pre_point_owner_listed _ q Hpoints
      (reachable_in_nodes _ q (points_graph_wf Hpoints) Hqreachable)) as [Hqb Hqmember].
    destruct (dfs_eq_dec EB (block_of_point (pre_ssa_points a) q) b) as [Heq|Hne].
    + rewrite Heq in Hqmember; exact (pre_block_member_dominates_last EV a b q first
        Hlaw Hb Hqmember).
    + apply (pre_block_point_dominates EV a _ q _ Hlaw Hqb Hqmember).
      * rewrite Hownerlast; exact Hne.
      * rewrite Hownerlast; exact Hqparent.
Qed.

(** * Meaning of a scoped frame *)

Local Definition pre_real_use_at {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    n d : Prop :=
  exists e, Map.get EE e (frg_occurrence_index f) = Some d /\
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) n.

Local Definition pre_no_reaching_version {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n : Prop := forall d q, In d (frg_versions f) -> frg_version_expr d = u ->
      frg_version_point a d = Some q ->
      ~ dominates (live_graph (point_model (pre_ssa_points a))) q n.

(* A frame keeps the nearest definition even when its availability bit has been cleared. *)
Local Definition pre_frame_laws {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n (frame : frg_operand B E U * bool) : Prop :=
  let d := frg_operand_version (fst frame) in
  frg_version_expr d = u /\
  (frg_operand_real_use (fst frame) = true <-> pre_real_use_at EE a f n d) /\
  match frg_version_point a d with
  | Some q => frg_nearest_version a f u n d /\
      (snd frame = true <-> pre_no_dominating_kill a u q n)
  | None => d = FrUnavailable u /\ snd frame = false /\ pre_no_reaching_version a f u n
  end.

Local Definition pre_scope_laws {S O B BE N E V K C U} (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    n (scope : pre_rename_scope B E U) : Prop := forall u,
  pre_expr_in_family a u -> pre_total_pure (pre_expression a) u = true ->
  pre_frame_laws EE a f u n (pre_rename_top EU scope u).

Local Lemma pre_nearest_points_agree {S O B BE N E V K C U} (EN : encoding N)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n d q d' q' :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  frg_nearest_version a f u n d -> frg_version_point a d = Some q ->
  frg_nearest_version a f u n d' -> frg_version_point a d' = Some q' -> q = q'.
Proof.
  intros Hready Hn [Hd [Hexpr [position [Hposition [Hdom Hnearest]]]]] Hq
    [Hd' [Hexpr' [position' [Hposition' [Hdom' Hnearest']]]]] Hq'.
  assert (Heq : position = q) by congruence; subst position.
  assert (Heq : position' = q') by congruence; subst position'.
  apply (idf_dominance_antisym EN _ _ Hready q q').
  - exact (dom_dominator_reachable _ q n Hn Hdom).
  - exact (dom_dominator_reachable _ q' n Hn Hdom').
  - exact (Hnearest' d q Hd Hexpr Hq Hdom).
  - exact (Hnearest d' q' Hd' Hexpr' Hq' Hdom').
Qed.

Local Lemma pre_frame_availability {S O B BE N E V K C U}
    (EB : encoding B) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    u n frame :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> pre_observed_point a n ->
  (forall b, frg_phi_needed EB EU a u b -> In (FrPhi b u) (frg_versions f)) ->
  pre_frame_laws EE a f u n frame ->
  (snd frame = true <-> exists d, frg_reusable a f u n d) /\
  (snd frame = true -> frg_reusable a f u n (frg_operand_version (fst frame))).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hobserved Hphis [Hexpr [Hreal Hreaching]].
  pose proof (pre_expr_reachable_points EV a Hlaw n
    (pre_observed_listed EV a n Hlaw Hobserved)) as Hn.
  destruct (frg_version_point a (frg_operand_version (fst frame))) as [q|] eqn:Hq.
  - destruct Hreaching as [Hnearest Havailable].
    assert (Hsound : snd frame = true ->
      frg_reusable a f u n (frg_operand_version (fst frame))).
    { intro Htrue; apply (pre_reusable_of_dominating_kills EB EN EV EU a f u n _ q
        Hlaw Hblocks Hpoints Hfamily Hobserved Hphis Hnearest Hq).
      apply Havailable; exact Htrue. }
    split; [split|exact Hsound].
    + intro Htrue; exists (frg_operand_version (fst frame)); apply Hsound; exact Htrue.
    + intros [d Hd]; pose proof Hd as Hboth; destruct Hboth as [Hnearest' [q' [Hq' Hsafe]]].
      pose proof (pre_nearest_points_agree EN a f u n _ q d q' Hpoints Hn Hnearest Hq
        Hnearest' Hq') as Heq.
      apply Havailable; rewrite Heq.
      exact (pre_reusable_dominating_kills EN EV a f u n d q' Hlaw Hpoints Hfamily Hn Hd Hq').
  - destruct Hreaching as [Hunavailable [Hfalse Hnone]].
    split; [split|].
    + intro Htrue; congruence.
    + intros [d [[Hd [Hvalue [q [Hpoint [Hdom Hnearest]]]]] Hsafe]].
      exfalso; exact (Hnone d q Hd Hvalue Hpoint Hdom).
    + intro Htrue; congruence.
Qed.

(** * Definition provenance during the walk *)

Local Definition pre_frame_sound {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u n (frame : frg_operand B E U * bool) : Prop :=
  let d := frg_operand_version (fst frame) in
  frg_version_expr d = u /\
  (forall q, frg_version_point a d = Some q ->
    dominates (live_graph (point_model (pre_ssa_points a))) q n) /\
  (snd frame = true -> exists q, frg_version_point a d = Some q).

Local Definition pre_scope_sound {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) n (scope : pre_rename_scope B E U) : Prop :=
  forall u, pre_frame_sound a u n (pre_rename_top EU scope u).

Local Lemma pre_rename_top_set {B E U} (EU : encoding U) scope u v
    (frame : frg_operand B E U * bool) :
  pre_rename_top EU (Map.set EU v frame scope) u =
    if dfs_eq_dec EU u v then frame else pre_rename_top EU scope u.
Proof.
  unfold pre_rename_top; destruct (dfs_eq_dec EU u v) as [Heq|Hne].
  - subst u; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma pre_frame_sound_monotone {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u n m frame :
  dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  pre_frame_sound a u n frame -> pre_frame_sound a u m frame.
Proof.
  intros Hdom [Hexpr [Hpoint Havailable]]; split; [exact Hexpr|]; split; [|exact Havailable].
  intros q Hq; eapply dominates_trans; [apply Hpoint; exact Hq|exact Hdom].
Qed.

Local Lemma pre_scope_sound_monotone {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) n m scope :
  dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  pre_scope_sound EU a n scope -> pre_scope_sound EU a m scope.
Proof.
  intros Hdom Hscope u; apply (pre_frame_sound_monotone a u n m _ Hdom (Hscope u)).
Qed.

Local Lemma pre_scope_sound_set {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) n scope u frame :
  pre_scope_sound EU a n scope -> pre_frame_sound a u n frame ->
  pre_scope_sound EU a n (Map.set EU u frame scope).
Proof.
  intros Hscope Hframe v; rewrite pre_rename_top_set.
  destruct (dfs_eq_dec EU v u) as [Heq|Hne]; [subst v; exact Hframe|apply Hscope].
Qed.

Local Lemma pre_frame_sound_unavailable {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u n :
  pre_frame_sound a u n (FrgOperand (FrUnavailable u) false, false).
Proof.
  split; [reflexivity|]; split; [intros q Hfalse; discriminate|intros Hfalse; discriminate].
Qed.

Local Lemma pre_initial_frame_sound {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) u first :
  Graph.entries (live_graph (point_model (pre_ssa_points a))) = [first] ->
  pre_frame_sound a u first (pre_initial_frame a u).
Proof.
  intro Hentries; unfold pre_initial_frame.
  destruct (pre_initial_available a u); [|apply pre_frame_sound_unavailable].
  split; [reflexivity|]; split.
  - intros q Hpoint; change (nth_error
      (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0 = Some q) in Hpoint.
    rewrite Hentries in Hpoint.
    cbn in Hpoint; inversion Hpoint; subst q; apply dominates_refl.
  - intros Htrue; exists first; change (nth_error
      (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0 = Some first).
    rewrite Hentries; reflexivity.
Qed.

Local Lemma pre_initial_scope_sound {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family first :
  Graph.entries (live_graph (point_model (pre_ssa_points a))) = [first] ->
  pre_scope_sound EU a first (pre_initial_scope EU a family).
Proof.
  intros Hentries u; unfold pre_rename_top, pre_initial_scope.
  destruct (Map.get EU u (Map.of_list EU (map (fun v => (v, pre_initial_frame a v)) family)))
    as [frame|] eqn:Hget; [|apply pre_frame_sound_unavailable].
  apply (pre_map_list_sound EU) in Hget; apply in_map_iff in Hget.
  destruct Hget as [v [Heq Hv]]; injection Heq as Hkey Hframe; subst v frame.
  apply pre_initial_frame_sound; exact Hentries.
Qed.

Local Lemma pre_fold_projection {A X Y} (step : A -> X -> A) (observe : A -> Y) xs initial :
  (forall acc x, observe (step acc x) = observe acc) ->
  observe (fold_left step xs initial) = observe initial.
Proof.
  intro Hstep; revert initial; induction xs as [|x xs IH]; intro initial; [reflexivity|].
  cbn [fold_left]; rewrite IH, Hstep; reflexivity.
Qed.

Local Lemma pre_rename_mark_data {B BE E U} (EB : encoding B) (EU : encoding U)
    scope (acc : pre_rename_acc B BE E U) u :
  pre_rename_occurrences (pre_rename_mark EB EU scope acc u) = pre_rename_occurrences acc /\
  pre_rename_fresh (pre_rename_mark EB EU scope acc u) = pre_rename_fresh acc /\
  pre_rename_links (pre_rename_mark EB EU scope acc u) = pre_rename_links acc.
Proof.
  unfold pre_rename_mark; destruct (pre_rename_top EU scope u) as [[d real] available].
  destruct d; destruct real; repeat split; reflexivity.
Qed.

Local Definition pre_occurrence_entry_sound {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) e d : Prop :=
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
  pre_recomputed (pre_expression a) e = Some (frg_version_expr d) /\
  pre_total_pure (pre_expression a) (frg_version_expr d) = true /\
  exists q, frg_version_point a d = Some q /\
    dominates (live_graph (point_model (pre_ssa_points a))) q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e).

Local Definition pre_occurrence_index_sound {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (index : Map.t E (frg_version B E U)) : Prop :=
  forall e d, Map.get EE e index = Some d -> pre_occurrence_entry_sound a e d.

Local Lemma pre_occurrence_index_set {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) index e d :
  pre_occurrence_index_sound EE a index -> pre_occurrence_entry_sound a e d ->
  pre_occurrence_index_sound EE a (Map.set EE e d index).
Proof.
  intros Hindex Hentry key value Hget; destruct (dfs_eq_dec EE key e) as [Heq|Hne].
  - subst key; rewrite Map.get_set_same in Hget; inversion Hget; subst value; exact Hentry.
  - rewrite Map.get_set_other in Hget by exact Hne; exact (Hindex key value Hget).
Qed.

Local Lemma pre_occurrence_index_empty {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_occurrence_index_sound EE a Map.empty.
Proof.
  intros e d Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Local Lemma pre_rename_exit_scope {B BE N E U} (EB : encoding B) (EN : encoding N)
    (EU : encoding U) exits n scope (acc : pre_rename_acc B BE E U) :
  fst (pre_rename_exit EB EN EU exits n (scope, acc)) = scope /\
  pre_rename_occurrences (snd (pre_rename_exit EB EN EU exits n (scope, acc))) =
    pre_rename_occurrences acc.
Proof.
  unfold pre_rename_exit; cbn [fst snd]; split; [reflexivity|].
  apply pre_fold_projection; intros output u; exact (proj1 (pre_rename_mark_data EB EU _ output u)).
Qed.

Local Lemma pre_rename_argument_occurrences {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope acc argument :
  pre_rename_occurrences (pre_rename_argument EB EBE EU a scope acc argument) =
    pre_rename_occurrences acc.
Proof.
  destruct argument as [be u]; unfold pre_rename_argument.
  destruct (pre_phi_translate a be u) as [v|]; [|reflexivity].
  destruct (pre_rename_top EU scope v); reflexivity.
Qed.

Local Lemma pre_rename_occurrence_sound {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e scope acc :
  pre_expr_ssa_laws EV a -> In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_scope_sound EU a (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_occurrence_index_sound EE a (pre_rename_occurrences acc) ->
  let result := pre_rename_occurrence EB EE EU a e (scope, acc) in
  pre_scope_sound EU a (Graph.source (live_graph (point_model (pre_ssa_points a))) e)
    (fst (fst result)) /\
  pre_occurrence_index_sound EE a (pre_rename_occurrences (snd (fst result))).
Proof.
  intros Hlaw He Hscope Hindex; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed;
    [|exact (conj Hscope Hindex)].
  destruct (pre_total_pure (pre_expression a) u) eqn:Hpure; [|exact (conj Hscope Hindex)].
  destruct (pre_rename_top EU scope u) as [[d real] available] eqn:Htop.
  pose proof (Hscope u) as Hframe; rewrite Htop in Hframe.
  destruct Hframe as [Hexpr [Hpoint Havailable]]; cbn [fst snd frg_operand_version] in *.
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true) eqn:Hfresh; cbn [fst snd pre_rename_occurrences].
  - split; [exact Hscope|]; apply pre_occurrence_index_set.
    + exact Hindex.
    + split; [exact He|]; split; [exact Hcomputed|]; split; [exact Hpure|].
      exists (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
      split; [reflexivity|apply dominates_refl].
  - assert (Htrue : available = true) by (destruct available; [reflexivity|discriminate]).
    destruct (Havailable Htrue) as [q Hq]; split.
    + apply pre_scope_sound_set; [exact Hscope|].
      split; [exact Hexpr|]; split; [exact Hpoint|intros Hflag; exists q; exact Hq].
    + apply pre_occurrence_index_set; [exact Hindex|].
      split; [exact He|]; rewrite Hexpr; split; [exact Hcomputed|]; split; [exact Hpure|].
      exists q; split; [exact Hq|]; eapply dominates_trans; [exact (Hpoint q Hq)|].
      exact (pre_internal_source_dominates EV a e Hlaw He
        (proj1 (pre_expr_real_internal EV a Hlaw e u Hcomputed))).
Qed.

Local Lemma pre_fold_invariant {A X} (step : A -> X -> A) (P : A -> Prop) xs initial :
  (forall acc x, P acc -> P (step acc x)) -> P initial -> P (fold_left step xs initial).
Proof.
  intros Hstep; revert initial; induction xs as [|x xs IH]; intros initial Hinitial;
    [exact Hinitial|].
  cbn [fold_left]; apply IH; apply Hstep; exact Hinitial.
Qed.

Local Lemma pre_frame_sound_fresh {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) e u :
  pre_frame_sound a u (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (FrgOperand (FrFresh e u) true, true).
Proof.
  split; [reflexivity|]; split.
  - intros q Hq; inversion Hq; subst q; apply dominates_refl.
  - intros Htrue; exists (Graph.target (live_graph (point_model (pre_ssa_points a))) e);
    reflexivity.
Qed.

Local Lemma pre_frame_sound_phi {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) b u :
  pre_frame_sound a u (Graph.target (live_graph (point_model (pre_ssa_points a)))
    (parameter_edge (pre_ssa_points a) b)) (FrgOperand (FrPhi b u) false, true).
Proof.
  split; [reflexivity|]; split.
  - intros q Hq; inversion Hq; subst q; apply dominates_refl.
  - intros Htrue; exists (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)); reflexivity.
Qed.

Local Lemma pre_rename_definitions_sound {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    phis b e fresh scope :
  pre_scope_sound EU a (Graph.target (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_scope_sound EU a (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (pre_rename_definitions EB EE EU a phis b e fresh scope).
Proof.
  intro Hscope; unfold pre_rename_definitions.
  assert (Hfresh : pre_scope_sound EU a
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (match fresh with
     | Some u => Map.set EU u (FrgOperand (FrFresh e u) true, true) scope
     | None => scope
     end)).
  { destruct fresh; [apply pre_scope_sound_set; [exact Hscope|apply pre_frame_sound_fresh]|exact
    Hscope]. }
  destruct (Pos.eqb (encode EE e) (encode EE (parameter_edge (pre_ssa_points a) b)))
    eqn:Hparameter; [|exact Hfresh].
  apply Pos.eqb_eq in Hparameter; apply (encode_injective EE) in Hparameter; subst e.
  eapply pre_fold_invariant; [|exact Hfresh].
  intros frames u Hframes; apply pre_scope_sound_set; [exact Hframes|apply pre_frame_sound_phi].
Qed.

Local Lemma pre_rename_alter_sound {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    n e scope acc u :
  pre_scope_sound EU a n scope -> pre_occurrence_index_sound EE a (pre_rename_occurrences acc) ->
  pre_scope_sound EU a n (fst (pre_rename_alter EB EU a e (scope, acc) u)) /\
  pre_occurrence_index_sound EE a
    (pre_rename_occurrences (snd (pre_rename_alter EB EU a e (scope, acc) u))).
Proof.
  intros Hscope Hindex; unfold pre_rename_alter; cbn [fst snd]; split.
  - apply pre_scope_sound_set; [exact Hscope|].
    destruct (Hscope u) as [Hexpr [Hpoint Havailable]].
    split; [exact Hexpr|]; split; [exact Hpoint|intros Hfalse; discriminate].
  - destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) u);
      [exact Hindex|].
    rewrite (proj1 (pre_rename_mark_data EB EU scope acc u)); exact Hindex.
Qed.

Local Lemma pre_rename_alters_sound {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    n e xs work :
  pre_scope_sound EU a n (fst work) /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd work)) ->
  let result := fold_left (pre_rename_alter EB EU a e) xs work in
  pre_scope_sound EU a n (fst result) /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd result)).
Proof.
  intro Hwork; apply pre_fold_invariant; [|exact Hwork].
  intros [scope acc] u [Hscope Hindex]; exact
    (pre_rename_alter_sound EB EE EU a n e scope acc u Hscope Hindex).
Qed.

Local Lemma pre_rename_exit_sound {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) exits n scope (acc : pre_rename_acc B BE E U) :
  pre_scope_sound EU a n scope -> pre_occurrence_index_sound EE a (pre_rename_occurrences acc) ->
  pre_scope_sound EU a n (fst (pre_rename_exit EB EN EU exits n (scope, acc))) /\
  pre_occurrence_index_sound EE a
    (pre_rename_occurrences (snd (pre_rename_exit EB EN EU exits n (scope, acc)))).
Proof.
  intros Hscope Hindex; destruct (pre_rename_exit_scope EB EN EU exits n scope acc)
    as [Hframes Hoccurrences].
  rewrite Hframes, Hoccurrences; auto.
Qed.

Local Lemma pre_rename_instruction_sound {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b e scope acc :
  pre_expr_ssa_laws EV a -> In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  pre_scope_sound EU a (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_occurrence_index_sound EE a (pre_rename_occurrences acc) ->
  let result := pre_rename_instruction EB EN EE EU a alterations exits phis b (scope, acc) e in
  pre_scope_sound EU a (Graph.target (live_graph (point_model (pre_ssa_points a))) e) (fst result)
    /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd result)).
Proof.
  intros Hlaw He Hinternal Hscope Hindex.
  pose proof (pre_rename_occurrence_sound EB EE EV EU a e scope acc Hlaw He Hscope Hindex)
    as Hobserved.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e (scope, acc)) as [[frames output] fresh]
    eqn:Hobserve; rewrite ?Hobserve in Hobserved; cbn [fst snd] in Hobserved.
  pose proof (pre_rename_alters_sound EB EE EU a
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) e
    (FinSet.elements (pre_group_lookup EE alterations e)) (frames, output) Hobserved) as Haltered.
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (frames, output))
    as [frames' output'] eqn:Halter.
  rewrite ?Halter in Haltered; cbn [fst snd] in Haltered.
  destruct Haltered as [Hframes Houtput].
  apply pre_rename_exit_sound; [|exact Houtput].
  apply pre_rename_definitions_sound.
  exact (pre_scope_sound_monotone EU a _ _ frames'
    (pre_internal_source_dominates EV a e Hlaw He Hinternal) Hframes).
Qed.

Local Lemma pre_rename_instructions_sound {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b ns es first default :
  pre_expr_ssa_laws EV a -> point_chain (live_graph (point_model (pre_ssa_points a))) ns es ->
  nth_error ns 0 = Some first ->
  In first (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
  (forall e, In e es -> block_edge_of (pre_ssa_points a) e = None) ->
  forall work, pre_scope_sound EU a first (fst work) /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd work)) ->
  let result := fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b) es work in
  pre_scope_sound EU a (last ns default) (fst result) /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd result)).
Proof.
  intros Hlaw Hchain; revert first.
  induction Hchain as [n|n m ns e es He Htarget Hchain IH];
    intros first Hfirst Hnode Hinternal [scope acc] [Hscope Hindex];
    cbn in Hfirst; inversion Hfirst; subst first; [exact (conj Hscope Hindex)|].
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (out_source (points_graph_wf Hpoints) n e He) as Hsource.
  assert (Hlisted : In e (edges_of (live_graph (point_model (pre_ssa_points a))))).
  { apply in_flat_map; exists n; auto. }
  assert (Hsource_scope : pre_scope_sound EU a
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope).
  { rewrite Hsource; exact Hscope. }
  pose proof (pre_rename_instruction_sound EB EN EE EV EU a alterations exits phis b e scope acc
    Hlaw Hlisted (Hinternal e (or_introl eq_refl)) Hsource_scope Hindex) as Hnext.
  rewrite Htarget in Hnext.
  apply (IH m eq_refl
    ltac:(rewrite <- Htarget; exact (out_target_in (points_graph_wf Hpoints) n e Hnode He))
    ltac:(intros edge Hedge; apply Hinternal; right; exact Hedge) _ Hnext).
Qed.

Local Lemma pre_rename_block_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b first scope acc :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  pre_scope_sound EU a first scope -> pre_occurrence_index_sound EE a (pre_rename_occurrences acc)
    ->
  let result := pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc in
  pre_scope_sound EU a (last (points_in_block (pre_ssa_points a) b) first) (fst result) /\
    pre_occurrence_index_sound EE a (pre_rename_occurrences (snd result)).
Proof.
  intros Hlaw Hb Hfirst Hscope Hindex; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  assert (Hentered : (match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end) = pre_rename_exit EB EN EU exits first (scope, acc)).
  { destruct (points_in_block (pre_ssa_points a) b) as [|head rest]; cbn in Hfirst;
      [discriminate|inversion Hfirst; reflexivity]. }
  pose proof (pre_rename_instructions_sound EB EN EE EV EU a alterations exits phis b
    (points_in_block (pre_ssa_points a) b) (instruction_edges (pre_ssa_points a) b) first first
    Hlaw (points_ordered Hpoints b Hb) Hfirst
    ltac:(apply (points_covered Hpoints); exists b; split;
      [exact Hb|exact (nth_error_In _ _ Hfirst)])
    ltac:(intros e He; exact (instruction_edges_internal Hpoints b e Hb He)) _
    (pre_rename_exit_sound EB EN EE EU a exits first scope acc Hscope Hindex)) as Hbody.
  unfold pre_rename_block; rewrite Hentered.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) (pre_rename_exit EB EN EU exits first (scope, acc)))
    as [frames output] eqn:Hfold.
  rewrite ?Hfold in Hbody; cbn [fst snd] in Hbody; split; [exact (proj1 Hbody)|].
  cbn [snd]; rewrite (pre_fold_projection _ pre_rename_occurrences _ output
    (pre_rename_argument_occurrences EB EBE EU a frames)); exact (proj2 Hbody).
Qed.

Local Definition pre_pending_sound {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (tasks : list (B * pre_rename_scope B E U)) : Prop :=
  forall b scope, In (b, scope) tasks ->
    In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
    exists first, nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first /\
      pre_scope_sound EU a first scope.

Local Definition pre_work_sound {S O B BE N E V K C U} (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (work : pre_rename_work B BE E U) : Prop :=
  pre_pending_sound EU a (fst (fst work)) /\
  pre_occurrence_index_sound EE a (pre_rename_occurrences (snd work)).

Local Lemma pre_rename_children_sound {S O B BE N E V K C U} (EB : encoding B)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    b first scope :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_scope_sound EU a (last (points_in_block (pre_ssa_points a) b) first) scope ->
  pre_pending_sound EU a (map (fun c => (c, scope))
    (index_edges EB (dom_children EB
      (Map.elements (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))))) b)).
Proof.
  intros Hlaw Hready Hb Hscope c frames Hin; apply in_map_iff in Hin.
  destruct Hin as [child [Heq Hchild]]; inversion Heq; subst child frames.
  apply dom_children_in in Hchild.
  assert (Hmap : Map.wf EB
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))).
  { apply (chk_idom_wf EB _ _ Hready). }
  apply (Map.elements_sound EB c b _ Hmap) in Hchild.
  destruct (simple_lt_idom_exact EB _ _ Hready) as [Hwf [[Hdomain Hforest] Hexact]].
  destruct (Hdomain c b Hchild) as [Hcreach Hbreach].
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (reachable_in_nodes _ c (blocks_graph_wf Hpoints) Hcreach) as Hc.
  split; [exact Hc|].
  destruct (points_in_block (pre_ssa_points a) c) as [|head rest] eqn:Hlist.
  { exfalso; apply (blocks_nonempty Hpoints c Hc); exact Hlist. }
  exists head; split; [reflexivity|].
  apply (pre_scope_sound_monotone EU a
    (last (points_in_block (pre_ssa_points a) b) first) head scope); [|exact Hscope].
  pose proof (proj2 (proj2 (proj2 (dominator_tree_sound EB _ _ Hready))) c b Hchild)
    as [Hdom Hne].
  apply (pre_block_point_dominates EV a b _ head Hlaw Hb
    (pre_chain_last_member _ _ _ first (points_ordered Hpoints b Hb))).
  - rewrite (points_owner Hpoints c head Hc ltac:(rewrite Hlist; left; reflexivity)); exact Hne.
  - rewrite (points_owner Hpoints c head Hc ltac:(rewrite Hlist; left; reflexivity)); exact Hdom.
Qed.

Local Lemma pre_rename_step_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_work_sound EE EU a work ->
  pre_work_sound EE EU a (pre_rename_step EB EBE EN EE EU a
    (dom_children EB (Map.elements (idom (dominator_tree
      (prepare EB (block_graph (pre_ssa_points a))))))) alterations exits phis arguments work).
Proof.
  intros Hlaw Hready; destruct work as [[[|[b scope] rest] seen] acc];
    [exact (fun H => H)|].
  intros [Hpending Hindex]; unfold pre_rename_step; cbn [fst snd].
  assert (Hrest : pre_pending_sound EU a rest).
  { intros c frames Hin; apply Hpending; right; exact Hin. }
  destruct (FinSet.mem EB b seen) eqn:Hseen; [exact (conj Hrest Hindex)|].
  destruct (Hpending b scope (or_introl eq_refl)) as [Hb [first [Hfirst Hscope]]].
  pose proof (pre_rename_block_sound EB EBE EN EE EV EU a alterations exits phis arguments
    b first scope acc Hlaw Hb Hfirst Hscope Hindex) as Hblock.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output] eqn:Hresult; rewrite ?Hresult in Hblock; cbn [fst snd] in Hblock.
  split; [|exact (proj2 Hblock)].
  intros c values Hin; apply in_app_iff in Hin; destruct Hin as [Hchild|Htail].
  - exact (pre_rename_children_sound EB EV EU a b first frames Hlaw Hready Hb
      (proj1 Hblock) c values Hchild).
  - exact (Hrest c values Htail).
Qed.

Local Lemma pre_iter_invariant {X} (step : X -> X) (P : X -> Prop) fuel initial :
  (forall x, P x -> P (step x)) -> P initial -> P (Pos.iter step initial fuel).
Proof.
  intros Hstep; induction fuel using Pos.peano_ind; intro Hinitial.
  - apply Hstep; exact Hinitial.
  - rewrite Pos.iter_succ; apply Hstep; apply IHfuel; exact Hinitial.
Qed.

Local Lemma pre_rename_run_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments fuel work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_work_sound EE EU a work ->
  pre_work_sound EE EU a (pre_rename_run (pre_rename_step EB EBE EN EE EU a
    (dom_children EB (Map.elements (idom (dominator_tree
      (prepare EB (block_graph (pre_ssa_points a))))))) alterations exits phis arguments)
    fuel work).
Proof.
  intros Hlaw Hready Hwork; rewrite pre_rename_run_agrees by reflexivity.
  apply pre_iter_invariant; [|exact Hwork].
  intros state Hstate; exact (pre_rename_step_sound EB EBE EN EE EV EU a
    alterations exits phis arguments state Hlaw Hready Hstate).
Qed.

Local Lemma pre_initial_work_sound {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family :
  pre_expr_ssa_laws EV a ->
  pre_work_sound EE EU a
    (map (fun b => (b, pre_initial_scope EU a family))
      (Graph.entries (block_graph (pre_ssa_points a))), FinSet.empty,
      PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty).
Proof.
  intro Hlaw; split; [|apply pre_occurrence_index_empty].
  intros b scope Hin; apply in_map_iff in Hin.
  destruct Hin as [entry [Heq Hentry]]; inversion Heq; subst entry scope.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  split; [exact (entries_in (blocks_graph_wf Hpoints) b Hentry)|].
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hblocks [Hpoint Hfirst]]]].
  rewrite Hblocks in Hentry; destruct Hentry as [Hsame|Hfalse]; [subst b|contradiction].
  exists first; split; [exact Hfirst|apply pre_initial_scope_sound; exact Hpoint].
Qed.

(** Every recorded occurrence is a listed pure recomputation with a reaching definition. *)
Theorem build_frg_occurrence_provenance {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall e d, Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) = Some d ->
    pre_occurrence_entry_sound a e d.
Proof.
  intros Hlaw Hready; unfold build_frg; cbn zeta; cbn [frg_occurrence_index].
  apply (proj2 (pre_rename_run_sound EB EBE EN EE EV EU a _ _ _ _ _ _ Hlaw Hready
    (pre_initial_work_sound EE EV EU a _ Hlaw))).
Qed.

Local Lemma pre_rename_alter_occurrences {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) u :
  pre_rename_occurrences (snd (pre_rename_alter EB EU a e work u)) =
    pre_rename_occurrences (snd work).
Proof.
  destruct work as [scope acc]; unfold pre_rename_alter; cbn [snd].
  destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) u);
    [reflexivity|exact (proj1 (pre_rename_mark_data EB EU scope acc u))].
Qed.

Local Lemma pre_rename_instruction_occurrences {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e :
  pre_rename_occurrences (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e)) =
  pre_rename_occurrences (snd (fst (pre_rename_occurrence EB EE EU a e work))).
Proof.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e work) as [[scope acc] fresh]; cbn [fst snd].
  pose proof (pre_fold_projection (pre_rename_alter EB EU a e)
    (fun state => pre_rename_occurrences (snd state))
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)
    (pre_rename_alter_occurrences EB EU a e)) as Hfold.
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)) as [frames output].
  cbn [snd] in Hfold; rewrite (proj2 (pre_rename_exit_scope EB EN EU exits _ _ output)).
  exact Hfold.
Qed.

Local Lemma pre_rename_occurrence_other {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    e scope (acc : pre_rename_acc B BE E U) key : key <> e ->
  Map.get EE key (pre_rename_occurrences
    (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc))))) =
    Map.get EE key (pre_rename_occurrences acc).
Proof.
  intro Hne; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|]; [|reflexivity].
  destruct (pre_total_pure (pre_expression a) u); [|reflexivity].
  destruct (pre_rename_top EU scope u) as [[d real] available].
  cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true); cbn [fst snd pre_rename_occurrences];
    rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Local Lemma pre_rename_occurrence_present {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    e u scope (acc : pre_rename_acc B BE E U) :
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (pre_rename_occurrences
    (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc))))) = Some d.
Proof.
  intros Hcomputed Hpure; unfold pre_rename_occurrence; rewrite Hcomputed, Hpure.
  destruct (pre_rename_top EU scope u) as [[d real] available].
  cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true); cbn [fst snd pre_rename_occurrences];
    eexists; apply Map.get_set_same.
Qed.

Local Lemma pre_rename_instruction_other {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e key : key <> e ->
  Map.get EE key (pre_rename_occurrences (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e))) =
    Map.get EE key (pre_rename_occurrences (snd work)).
Proof.
  intro Hne; rewrite pre_rename_instruction_occurrences; destruct work as [scope acc].
  exact (pre_rename_occurrence_other EB EE EU a e scope acc key Hne).
Qed.

Local Lemma pre_rename_instructions_other {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b es
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) key : ~ In key es ->
  Map.get EE key (pre_rename_occurrences (snd (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis b) es work))) =
    Map.get EE key (pre_rename_occurrences (snd work)).
Proof.
  revert work; induction es as [|e es IH]; intros work Houtside; [reflexivity|].
  cbn [fold_left]; rewrite IH by (intro Hin; apply Houtside; right; exact Hin).
  apply pre_rename_instruction_other; intro Heq; apply Houtside; left; symmetry; exact Heq.
Qed.

Local Lemma pre_rename_block_other {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc key :
  ~ In key (instruction_edges (pre_ssa_points a) b) ->
  Map.get EE key (pre_rename_occurrences (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))) =
    Map.get EE key (pre_rename_occurrences acc).
Proof.
  intro Houtside; unfold pre_rename_block.
  set (entered := match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end).
  pose proof (pre_rename_instructions_other EB EN EE EU a alterations exits phis b
    (instruction_edges (pre_ssa_points a) b) entered key Houtside) as Hbody.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
  cbn [snd] in Hbody; cbn [snd].
  rewrite (pre_fold_projection _ pre_rename_occurrences _ output
    (pre_rename_argument_occurrences EB EBE EU a frames)), Hbody.
  unfold entered; destruct (points_in_block (pre_ssa_points a) b); [reflexivity|].
  rewrite (proj2 (pre_rename_exit_scope EB EN EU exits n scope acc)); reflexivity.
Qed.

Local Lemma pre_instruction_owner {B BE N E V} (s : ssa_points B BE N E V) b e :
  ssa_point_laws s -> In b (Graph.nodes (block_graph s)) -> In e (instruction_edges s b) ->
  block_of_point s (Graph.source (live_graph (point_model s)) e) = b.
Proof.
  intros Hlaw Hb He; apply (points_owner Hlaw b _ Hb).
  exact (pre_chain_source_member _ _ _ e (points_graph_wf Hlaw)
    (points_ordered Hlaw b Hb) He).
Qed.

Local Definition pre_occurrences_completed {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U) seen
    (index : Map.t E (frg_version B E U)) : Prop :=
  forall e d, Map.get EE e index = Some d -> FinSet.mem EB
    (block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) seen = true.

Local Definition pre_index_extends {X Y} (EX : encoding X) (before after : Map.t X Y) : Prop :=
  forall x y, Map.get EX x before = Some y -> Map.get EX x after = Some y.

Local Lemma pre_rename_block_preserves {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc seen :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  FinSet.mem EB b seen = false ->
  pre_occurrences_completed EB EE a seen (pre_rename_occurrences acc) ->
  pre_index_extends EE (pre_rename_occurrences acc) (pre_rename_occurrences (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intros Hlaw Hb Hfresh Hcompleted key value Hget.
  rewrite pre_rename_block_other; [exact Hget|].
  intro Hin; pose proof (Hcompleted key value Hget) as Hseen.
  rewrite (pre_instruction_owner _ b key (pre_expr_points EV a Hlaw) Hb Hin) in Hseen;
    congruence.
Qed.

Local Lemma pre_rename_block_completed {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc seen :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_occurrences_completed EB EE a seen (pre_rename_occurrences acc) ->
  pre_occurrences_completed EB EE a (FinSet.add EB b seen) (pre_rename_occurrences (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intros Hlaw Hb Hcompleted key value Hget; rewrite dfs_mem_add.
  destruct (dfs_eq_dec EB (block_of_point (pre_ssa_points a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) key)) b) as [Heq|Hne];
    [reflexivity|].
  apply (Hcompleted key value); rewrite pre_rename_block_other in Hget; [exact Hget|].
  intro Hin; apply Hne; exact
    (pre_instruction_owner _ b key (pre_expr_points EV a Hlaw) Hb Hin).
Qed.

Local Definition pre_work_completed {S O B BE N E V K C U} (EB : encoding B) (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (work : pre_rename_work B BE E U) : Prop :=
  pre_occurrences_completed EB EE a (snd (fst work)) (pre_rename_occurrences (snd work)).

Local Lemma pre_rename_step_completed {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_expr_ssa_laws EV a -> pre_work_sound EE EU a work -> pre_work_completed EB EE a work ->
  pre_work_completed EB EE a (pre_rename_step EB EBE EN EE EU a children
    alterations exits phis arguments work) /\
  pre_index_extends EE (pre_rename_occurrences (snd work)) (pre_rename_occurrences (snd
    (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work))).
Proof.
  intros Hlaw; destruct work as [[[|[b scope] rest] seen] acc];
    intros [Hpending Hindex] Hcompleted.
  - split; [exact Hcompleted|intros key value Hget; exact Hget].
  - unfold pre_rename_step; cbn [fst snd].
    destruct (FinSet.mem EB b seen) eqn:Hseen.
    + split; [exact Hcompleted|intros key value Hget; exact Hget].
    + destruct (Hpending b scope (or_introl eq_refl)) as [Hb Hframes].
      pose proof (pre_rename_block_completed EB EBE EN EE EV EU a alterations exits phis
        arguments b scope acc seen Hlaw Hb Hcompleted) as Hdone.
      pose proof (pre_rename_block_preserves EB EBE EN EE EV EU a alterations exits phis
        arguments b scope acc seen Hlaw Hb Hseen Hcompleted) as Hpreserved.
      destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
        as [frames output] eqn:Hblock.
      rewrite ?Hblock in Hdone, Hpreserved; cbn [fst snd] in *; split; assumption.
Qed.

Local Lemma pre_index_extends_trans {X Y} (EX : encoding X) (a b c : Map.t X Y) :
  pre_index_extends EX a b -> pre_index_extends EX b c -> pre_index_extends EX a c.
Proof.
  intros Hab Hbc x y Hget; apply Hbc; apply Hab; exact Hget.
Qed.

Local Lemma pre_rename_iter_completed {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments fuel work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_work_sound EE EU a work -> pre_work_completed EB EE a work ->
  let step := pre_rename_step EB EBE EN EE EU a (dom_children EB (Map.elements
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))))
      alterations exits phis arguments in
  pre_work_sound EE EU a (Pos.iter step work fuel) /\
  pre_work_completed EB EE a (Pos.iter step work fuel) /\
  pre_index_extends EE (pre_rename_occurrences (snd work))
    (pre_rename_occurrences (snd (Pos.iter step work fuel))).
Proof.
  intros Hlaw Hready Hsound Hcompleted step; induction fuel using Pos.peano_ind.
  - split.
    + exact (pre_rename_step_sound EB EBE EN EE EV EU a _ _ _ _ work Hlaw Hready Hsound).
    + exact (pre_rename_step_completed EB EBE EN EE EV EU a _ _ _ _ _ work
        Hlaw Hsound Hcompleted).
  - rewrite Pos.iter_succ; destruct IHfuel as [Hmid [Hdone Hextends]].
    pose proof (pre_rename_step_completed EB EBE EN EE EV EU a
      (dom_children EB (Map.elements (idom (dominator_tree
        (prepare EB (block_graph (pre_ssa_points a))))))) alterations exits phis arguments
      (Pos.iter step work fuel) Hlaw Hmid Hdone) as [Hdone' Hextends'].
    split; [exact (pre_rename_step_sound EB EBE EN EE EV EU a _ _ _ _
      (Pos.iter step work fuel) Hlaw Hready Hmid)|].
    split; [exact Hdone'|eapply pre_index_extends_trans; [exact Hextends|exact Hextends']].
Qed.

(** * Point-by-point frame transfer *)

Local Lemma pre_strict_target_dominates_source {N E} (g : Graph.t N E) e q :
  In e (Graph.out g (Graph.source g e)) ->
  strictly_dominates g q (Graph.target g e) -> dominates g q (Graph.source g e).
Proof.
  intros Hedge [Hdom Hne] start es Hentry Hpath.
  assert (Hsingle : path g (Graph.source g e) [e] (Graph.target g e)).
  { eapply path_cons; [exact Hedge|apply path_nil]. }
  destruct (Hdom start (es ++ [e]) Hentry (idf_path_app g _ _ _ _ _ Hpath Hsingle))
    as [Heq|[edge [Hin Htarget]]]; [left; exact Heq|].
  apply in_app_iff in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
  - right; exists edge; auto.
  - subst edge; exfalso; apply Hne; symmetry; exact Htarget.
  - contradiction.
Qed.

Local Lemma pre_internal_immediate {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e :
  pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  immediately_dominates (live_graph (point_model (pre_ssa_points a)))
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Hlaw He Hi; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_internal_edge_block _ e Hpoints He Hi) as [b [Hb [Hin Htarget]]].
  split; [split|].
  - exact (pre_internal_source_dominates EV a e Hlaw He Hi).
  - exact (pre_chain_edge_not_self _ _ _ (points_graph_wf Hpoints)
      (points_ordered Hpoints b Hb) (points_unique Hpoints b) e Hin).
  - intros q Hstrict; exact (pre_strict_target_dominates_source _ e q
      (proj2 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He)) Hstrict).
Qed.

Local Lemma pre_nearest_advance {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) f u n m d :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  (forall d', In d' (frg_versions f) -> frg_version_expr d' = u ->
    frg_version_point a d' <> Some m) ->
  frg_nearest_version a f u n d -> frg_nearest_version a f u m d.
Proof.
  intros [[Hdom Hne] Hminimal] Hnone [Hd [Hexpr [q [Hpoint [Hreach Hnearest]]]]].
  split; [exact Hd|]; split; [exact Hexpr|]; exists q; split; [exact Hpoint|]; split.
  - eapply dominates_trans; [exact Hreach|exact Hdom].
  - intros d' q' Hd' Hu' Hq' Hdom'.
    apply (Hnearest d' q' Hd' Hu' Hq'); apply Hminimal; split; [exact Hdom'|].
    intro Heq; subst q'; exact (Hnone d' Hd' Hu' Hq').
Qed.

Local Lemma pre_no_reaching_advance {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) f u n m :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  (forall d, In d (frg_versions f) -> frg_version_expr d = u ->
    frg_version_point a d <> Some m) ->
  pre_no_reaching_version a f u n -> pre_no_reaching_version a f u m.
Proof.
  intros [[Hdom Hne] Hminimal] Hnone Hold d q Hd Hu Hq Hreach.
  apply (Hold d q Hd Hu Hq); apply Hminimal; split; [exact Hreach|].
  intro Heq; subst q; exact (Hnone d Hd Hu Hq).
Qed.

Local Lemma pre_real_use_advance {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) f n m d :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  (forall e, Map.get EE e (frg_occurrence_index f) = Some d ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> m) ->
  (pre_real_use_at EE a f m d <-> pre_real_use_at EE a f n d).
Proof.
  intros [[Hdom Hne] Hminimal] Hnone; split; intros [e [Hget Hreach]]; exists e;
    split; [exact Hget| |exact Hget|].
  - apply Hminimal; split; [exact Hreach|exact (Hnone e Hget)].
  - eapply dominates_trans; [exact Hreach|exact Hdom].
Qed.

Local Lemma pre_kills_gap {S O B BE N E V K C U} (EN : encoding N)
    (a : pre_expr_ssa S O B BE N E V K C U) u q n m :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  (forall e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e = m ->
    kill (pre_genkill (pre_expression a)) e u = false) ->
  (pre_no_dominating_kill a u q m <-> pre_no_dominating_kill a u q n).
Proof.
  intros [[Hdom Hne] Hminimal] Hnone; split; intros Hsafe e He Hstrict Hreach.
  - apply (Hsafe e He Hstrict); eapply dominates_trans; [exact Hreach|exact Hdom].
  - destruct (dfs_eq_dec EN
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) m) as [Heq|Hneq].
    + exact (Hnone e He Heq).
    + apply (Hsafe e He Hstrict); apply Hminimal; split; assumption.
Qed.

Local Lemma pre_frame_gap {S O B BE N E V K C U} (EN : encoding N) (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) f u n m frame :
  immediately_dominates (live_graph (point_model (pre_ssa_points a))) n m ->
  (forall d, In d (frg_versions f) -> frg_version_expr d = u ->
    frg_version_point a d <> Some m) ->
  (forall e, Map.get EE e (frg_occurrence_index f) =
    Some (frg_operand_version (fst frame)) ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> m) ->
  (forall e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e = m ->
    kill (pre_genkill (pre_expression a)) e u = false) ->
  pre_frame_laws EE a f u n frame -> pre_frame_laws EE a f u m frame.
Proof.
  intros Himmediate Hdefinitions Hoccurrences Hkills [Hexpr [Hreal Hdefinition]].
  split; [exact Hexpr|]; split.
  - rewrite (pre_real_use_advance EE a f n m _ Himmediate Hoccurrences); exact Hreal.
  - destruct (frg_version_point a (frg_operand_version (fst frame))) as [q|] eqn:Hq.
    + destruct Hdefinition as [Hnearest Havailable]; split.
      * exact (pre_nearest_advance a f u n m _ Himmediate Hdefinitions Hnearest).
      * rewrite (pre_kills_gap EN a u q n m Himmediate Hkills); exact Havailable.
    + destruct Hdefinition as [Hunavailable [Hfalse Hnone]].
      split; [exact Hunavailable|]; split; [exact Hfalse|].
      exact (pre_no_reaching_advance a f u n m Himmediate Hdefinitions Hnone).
Qed.

Local Lemma pre_kills_instruction {S O B BE N E V K C U} (EN : encoding N)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) u q e :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  dominates (live_graph (point_model (pre_ssa_points a))) q
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) ->
  (pre_no_dominating_kill a u q
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) <->
    pre_no_dominating_kill a u q
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e) /\
    kill (pre_genkill (pre_expression a)) e u = false).
Proof.
  intros Hlaw Hready Hfamily He Hi Hq; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_internal_immediate EV a e Hlaw He Hi) as [[Hdom Hne] Hminimal].
  assert (Hsource : reachable (live_graph (point_model (pre_ssa_points a)))
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)).
  { pose proof He as Hlisted; apply in_flat_map in Hlisted.
    destruct Hlisted as [source [Hnode Hout]].
    rewrite (out_source (points_graph_wf Hpoints) source e Hout).
    exact (pre_expr_reachable_points EV a Hlaw source Hnode). }
  assert (Hqstrict : strictly_dominates (live_graph (point_model (pre_ssa_points a))) q
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)).
  { split; [eapply dominates_trans; [exact Hq|exact Hdom]|].
    intro Heq; subst q; apply Hne.
    exact (idf_dominance_antisym EN _ _ Hready _ _ Hsource
      (pre_expr_reachable_points EV a Hlaw _
        (out_target_in (points_graph_wf Hpoints) _ e
          (reachable_in_nodes _ _ (points_graph_wf Hpoints) Hsource)
          (proj2 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He)))) Hdom Hq). }
  split.
  - intro Hsafe; split.
    + intros edge Hedge Hstrict Hreach; apply (Hsafe edge Hedge Hstrict).
      eapply dominates_trans; [exact Hreach|exact Hdom].
    + apply (Hsafe e He Hqstrict); apply dominates_refl.
  - intros [Hsafe Hkill] edge Hedge Hstrict Hreach.
    destruct (dfs_eq_dec EN (Graph.target (live_graph (point_model (pre_ssa_points a))) edge)
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)) as [Heq|Hneq].
    + pose proof (pre_internal_incoming_unique _ e edge Hpoints He Hi Hedge Heq) as Hsame.
      subst edge; exact Hkill.
    + apply (Hsafe edge Hedge Hstrict); apply Hminimal; split; assumption.
Qed.

Local Lemma pre_rename_alters_top {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e xs
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) u :
  pre_rename_top EU (fst (fold_left (pre_rename_alter EB EU a e) xs work)) u =
    if in_dec (dfs_eq_dec EU) u xs then (fst (pre_rename_top EU (fst work) u), false)
    else pre_rename_top EU (fst work) u.
Proof.
  revert work; induction xs as [|x xs IH]; intros [scope acc]; [reflexivity|].
  cbn [fold_left]; rewrite IH; unfold pre_rename_alter; cbn [fst].
  rewrite !pre_rename_top_set.
  destruct (dfs_eq_dec EU u x) as [Heq|Hne].
  - subst x; destruct (in_dec (dfs_eq_dec EU) u xs) as [Hin|Hout],
      (in_dec (dfs_eq_dec EU) u (u :: xs)) as [Hin'|Hout']; cbn [fst]; try reflexivity;
      exfalso; apply Hout'; left; reflexivity.
  - destruct (in_dec (dfs_eq_dec EU) u xs) as [Hin|Hout],
      (in_dec (dfs_eq_dec EU) u (x :: xs)) as [Hin'|Hout']; try reflexivity.
    + exfalso; apply Hout'; right; exact Hin.
    + exfalso; apply Hout; destruct Hin' as [Heq|Hin']; [congruence|exact Hin'].
Qed.

Local Lemma pre_rename_phis_top {B E U} (EU : encoding U) b xs
    (scope : pre_rename_scope B E U) u :
  pre_rename_top EU (fold_left
    (fun frames v => Map.set EU v (FrgOperand (FrPhi b v) false, true) frames) xs scope) u =
    if in_dec (dfs_eq_dec EU) u xs then (FrgOperand (FrPhi b u) false, true)
    else pre_rename_top EU scope u.
Proof.
  revert scope; induction xs as [|x xs IH]; intro scope; [reflexivity|].
  cbn [fold_left]; rewrite IH, !pre_rename_top_set.
  destruct (dfs_eq_dec EU u x) as [Heq|Hne].
  - subst x; destruct (in_dec (dfs_eq_dec EU) u xs) as [Hin|Hout],
      (in_dec (dfs_eq_dec EU) u (u :: xs)) as [Hin'|Hout']; try reflexivity;
      exfalso; apply Hout'; left; reflexivity.
  - destruct (in_dec (dfs_eq_dec EU) u xs) as [Hin|Hout],
      (in_dec (dfs_eq_dec EU) u (x :: xs)) as [Hin'|Hout']; try reflexivity.
    + exfalso; apply Hout'; right; exact Hin.
    + exfalso; apply Hout; destruct Hin' as [Heq|Hin']; [congruence|exact Hin'].
Qed.

Local Lemma pre_rename_operand_index_exact {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family x u :
  In u (FinSet.elements (pre_group_lookup EV (pre_rename_operand_index EV EU a family) x)) <->
    In u family /\ In x (pre_operands a u).
Proof.
  unfold pre_rename_operand_index; rewrite (FinSet.elements_spec EU).
  2: { apply pre_group_fold_wf; intro key; unfold pre_group_lookup;
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact; unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite in_flat_map; split.
  - intros [[v [Hv Hin]]|Hfalse]; [|discriminate].
    apply in_map_iff in Hin; destruct Hin as [y [Heq Hy]]; inversion Heq; subst y v; auto.
  - intros [Hu Hx]; left; exists u; split; [exact Hu|].
    apply in_map_iff; exists x; auto.
Qed.

Local Lemma pre_rename_alter_candidates_exact {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family e u :
  In u (pre_rename_alter_candidates EV EU a (pre_rename_operand_index EV EU a family) e) <->
    In u family /\ exists x, In x (edge_def (point_model (pre_ssa_points a)) e) /\
      In x (pre_operands a u).
Proof.
  unfold pre_rename_alter_candidates; rewrite (FinSet.elements_spec EU).
  2: { apply FinSet.wf_fold_add; apply Map.wf_empty. }
  rewrite FinSet.of_list_spec, in_flat_map; split.
  - intros [x [Hx Hu]]; apply pre_rename_operand_index_exact in Hu.
    destruct Hu as [Hu Hoperand]; split; [exact Hu|exists x; auto].
  - intros [Hu [x [Hx Hoperand]]]; exists x; split; [exact Hx|].
    apply pre_rename_operand_index_exact; auto.
Qed.

Local Lemma pre_rename_alter_candidates_nodup {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) operands e :
  NoDup (pre_rename_alter_candidates EV EU a operands e).
Proof.
  unfold pre_rename_alter_candidates; apply (FinSet.elements_nodup EU).
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Local Lemma pre_rename_alter_candidates_empty {S O B BE N E V K C U} (EV : encoding V)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) operands e :
  edge_def (point_model (pre_ssa_points a)) e = [] ->
  pre_rename_alter_candidates EV EU a operands e = [].
Proof.
  intro Hdefs; unfold pre_rename_alter_candidates; rewrite Hdefs; reflexivity.
Qed.

Local Lemma pre_rename_alter_index_sound {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family e u :
  In u (FinSet.elements (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e)) ->
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    In u family /\ kill (pre_genkill (pre_expression a)) e u = true.
Proof.
  unfold pre_rename_alter_index; cbn zeta; rewrite (FinSet.elements_spec EU).
  2: { apply pre_group_fold_wf; intro key; unfold pre_group_lookup;
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact; unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite in_flat_map; intros [[edge [Hedge Hin]]|Hfalse]; [|discriminate].
  apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; inversion Heq; subst edge v.
  apply filter_In in Hv; destruct Hv as [Hu Hkill].
  apply pre_rename_alter_candidates_exact in Hu; tauto.
Qed.

Local Lemma pre_rename_alter_index_exact {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) family e u :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In u (FinSet.elements (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e)) <->
    In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
    In u family /\ kill (pre_genkill (pre_expression a)) e u = true.
Proof.
  intros Hlaw Hmember; split; [apply pre_rename_alter_index_sound|].
  intros [He [Hu Hkill]]; unfold pre_rename_alter_index; cbn zeta.
  rewrite (FinSet.elements_spec EU).
  2: { apply pre_group_fold_wf; intro key; unfold pre_group_lookup;
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact; unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite in_flat_map; left; exists e; split; [exact He|].
  apply in_map_iff; exists u; split; [reflexivity|]; apply filter_In; split; [|exact Hkill].
  apply pre_rename_alter_candidates_exact; split; [exact Hu|].
  destruct (pre_expr_kill_operand EV a Hlaw e u He Hmember Hkill) as [x [Hx Hdef]].
  exists x; auto.
Qed.

Local Definition pre_definition_edges {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U) : Prop :=
  forall d, In d (frg_versions f) -> match d with
  | FrFresh e _ => In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
      block_edge_of (pre_ssa_points a) e = None
  | FrPhi b _ => In b (Graph.nodes (block_graph (pre_ssa_points a)))
  | _ => True
  end.

Local Lemma pre_build_definition_edges {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) : pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_definition_edges a (build_frg EB EBE EN EE EV EU a).
Proof.
  intros Hlaw Hready d Hd; apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw)
    in Hd; destruct d as [u|u|e u|b u]; try exact I.
  - destruct Hd as [He [Hcomputed Hfresh]]; split; [exact He|].
    exact (proj1 (pre_expr_real_internal EV a Hlaw e u Hcomputed)).
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd.
    destruct Hd as [Hfamily [Hpure Hneeded]].
    exact (frg_phi_needed_nodes EB EU a u b
      (blocks_graph_wf (pre_expr_points EV a Hlaw)) Hneeded).
Qed.

Local Lemma pre_definition_first_initial {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) f b first d :
  ssa_point_laws (pre_ssa_points a) -> pre_definition_edges a f ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  In d (frg_versions f) -> frg_version_point a d = Some first ->
  d = FrInitial (frg_version_expr d).
Proof.
  intros Hpoints Hedges Hb Hfirst Hd Hpoint; pose proof (Hedges d Hd) as Hshape.
  destruct d as [u|u|e u|owner u]; [discriminate|reflexivity| |].
  - destruct Hshape as [He Hi]; exfalso.
    apply (pre_internal_target_not_first _ e b first Hpoints He Hi Hb Hfirst).
    inversion Hpoint; reflexivity.
  - destruct (pre_parameter_edge_listed _ owner Hpoints Hshape) as [He Hi]; exfalso.
    apply (pre_internal_target_not_first _ _ b first Hpoints He Hi Hb Hfirst).
    inversion Hpoint; reflexivity.
Qed.

Local Lemma pre_entry_dominator {N E} (g : Graph.t N E) first q :
  In first (Graph.entries g) -> dominates g q first -> q = first.
Proof.
  intros Hentry Hdom; destruct (Hdom first [] Hentry (path_nil first)) as [Heq|[e [Hin Heq]]];
    [exact Heq|contradiction].
Qed.

Local Lemma pre_initial_scope_top {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family u : In u family ->
  pre_rename_top EU (pre_initial_scope EU a family) u = pre_initial_frame a u.
Proof.
  intro Hu; unfold pre_rename_top, pre_initial_scope.
  rewrite (pre_map_list_unique EU _ u (pre_initial_frame a u)); [reflexivity| |].
  - intros frame Hin; apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]];
      injection Heq as Hkey Hframe; subst v; symmetry; exact Hframe.
  - apply in_map_iff; exists u; split; [reflexivity|exact Hu].
Qed.

Local Lemma pre_initial_frame_laws {S O B BE N E V K C U} (EE : encoding E) (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) f u b first :
  pre_expr_ssa_laws EV a -> pre_definition_edges a f ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  Graph.entries (live_graph (point_model (pre_ssa_points a))) = [first] ->
  (In (FrInitial u) (frg_versions f) <-> pre_initial_available a u = true) ->
  (forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    pre_occurrence_entry_sound a e d) ->
  pre_frame_laws EE a f u first (pre_initial_frame a u).
Proof.
  intros Hlaw Hedges Hb Hfirst Hentry Hinitial Hoccurrences.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  assert (Hin : In first (Graph.entries (live_graph (point_model (pre_ssa_points a))))).
  { rewrite Hentry; left; reflexivity. }
  assert (Hreal : forall d, ~ pre_real_use_at EE a f first d).
  { intros d [e [Hget Hdom]]; destruct (Hoccurrences e d Hget)
      as [He [Hcomputed [Hpure Hdefinition]]].
    assert (Hinternal : block_edge_of (pre_ssa_points a) e = None).
    { exact (proj1 (pre_expr_real_internal EV a Hlaw e _ Hcomputed)). }
    apply (pre_internal_target_not_first _ e b first Hpoints He Hinternal Hb Hfirst).
    exact (pre_entry_dominator _ first _ Hin Hdom). }
  unfold pre_initial_frame; destruct (pre_initial_available a u) eqn:Havailable;
    cbn [pre_frame_laws fst snd frg_operand_version frg_operand_real_use frg_version_expr].
  - split; [reflexivity|]; split; [split; [discriminate|intro Hfalse; exfalso; apply (Hreal _
    Hfalse)]|].
    unfold frg_version_point; rewrite Hentry; cbn; split.
    + split; [apply Hinitial; reflexivity|]; split; [reflexivity|].
      exists first; split.
      { change (nth_error (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0 =
          Some first); rewrite Hentry; reflexivity. }
      split; [apply dominates_refl|].
      intros d q Hd Hexpr Hpoint Hdom; rewrite (pre_entry_dominator _ first q Hin Hdom).
      apply dominates_refl.
    + split; [|intros Hsafe; reflexivity].
      intros Htrue e He [Hdom Hne] Hback; exfalso; apply Hne.
      symmetry; exact (pre_entry_dominator _ first _ Hin Hback).
  - split; [reflexivity|]; split; [split; [discriminate|intro Hfalse; exfalso; apply (Hreal _
    Hfalse)]|].
    split; [reflexivity|]; split; [reflexivity|].
    intros d q Hd Hexpr Hpoint Hdom.
    pose proof (pre_entry_dominator _ first q Hin Hdom) as Heq; subst q.
    pose proof (pre_definition_first_initial a f b first d Hpoints Hedges Hb Hfirst Hd Hpoint)
      as Hdinitial.
    rewrite Hexpr in Hdinitial; subst d; apply Hinitial in Hd; congruence.
Qed.

Local Lemma pre_real_use_instruction {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f e d :
  pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  (forall edge version, Map.get EE edge (frg_occurrence_index f) = Some version ->
    pre_occurrence_entry_sound a edge version) ->
  (pre_real_use_at EE a f
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) d <->
    pre_real_use_at EE a f
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d \/
    Map.get EE e (frg_occurrence_index f) = Some d).
Proof.
  intros Hlaw He Hi Hoccurrences; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  split.
  - intros [edge [Hget Hdom]]; destruct (dfs_eq_dec EE edge e) as [Heq|Hne];
      [subst edge; right; exact Hget|left].
    exists edge; split; [exact Hget|].
    apply (pre_strict_target_dominates_source _ e _
      (proj2 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He))).
    split; [exact Hdom|]; intro Heq; apply Hne.
    exact (pre_internal_incoming_unique _ e edge Hpoints He Hi
      (proj1 (Hoccurrences edge d Hget)) Heq).
  - intros [[edge [Hget Hdom]]|Hget].
    + exists edge; split; [exact Hget|]; eapply dominates_trans;
        [exact Hdom|exact (pre_internal_source_dominates EV a e Hlaw He Hi)].
    + exists e; split; [exact Hget|apply dominates_refl].
Qed.

Local Lemma pre_no_kill_at_definition {S O B BE N E V K C U} (EN : encoding N)
    (a : pre_expr_ssa S O B BE N E V K C U) u n :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  pre_no_dominating_kill a u n n.
Proof.
  intros Hready Hn e He [Hdom Hne] Hback; exfalso; apply Hne.
  exact (idf_dominance_antisym EN _ _ Hready _ _ Hn
    (dom_dominator_reachable _ _ n Hn Hback) Hdom Hback).
Qed.

Local Lemma pre_definition_frame_laws {S O B BE N E V K C U} (EN : encoding N)
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U) f u n d real :
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  In d (frg_versions f) -> frg_version_expr d = u -> frg_version_point a d = Some n ->
  (real = true <-> pre_real_use_at EE a f n d) ->
  pre_frame_laws EE a f u n (FrgOperand d real, true).
Proof.
  intros Hready Hn Hd Hexpr Hpoint Hreal; unfold pre_frame_laws.
  cbn [fst snd frg_operand_version frg_operand_real_use]; rewrite Hpoint.
  split; [exact Hexpr|]; split; [exact Hreal|]; split.
  - split; [exact Hd|]; split; [exact Hexpr|]; exists n; split; [exact Hpoint|].
    split; [apply dominates_refl|intros d' q' Hd' Hexpr' Hpoint' Hdom; exact Hdom].
  - split; [intros Htrue; exact (pre_no_kill_at_definition EN a u n Hready Hn)|
      intros Hsafe; reflexivity].
Qed.

Local Lemma pre_phi_no_real_use {S O B BE N E V K C U} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f b u :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  (forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    pre_occurrence_entry_sound a e d) ->
  ~ pre_real_use_at EE a f
    (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)) (FrPhi b u).
Proof.
  intros Hlaw Hready Hb Hoccurrences [e [Hget Hdom]].
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (Hoccurrences e (FrPhi b u) Hget) as [He [Hcomputed [Hpure [q [Hpoint Hreaches]]]]].
  inversion Hpoint; subst q.
  destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [Hparameter Hinternal].
  pose proof (proj1 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He)) as Hsource.
  pose proof (out_target_in (points_graph_wf Hpoints) _ e Hsource
    (proj2 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He))) as Htarget.
  assert (Heq : Graph.target (live_graph (point_model (pre_ssa_points a))) e =
    Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)).
  { apply (idf_dominance_antisym EN _ _ Hready).
    - exact (pre_expr_reachable_points EV a Hlaw _ Htarget).
    - exact (dom_dominator_reachable _ _ _
        (pre_expr_reachable_points EV a Hlaw _ Htarget) Hreaches).
    - exact Hdom.
    - exact Hreaches. }
  pose proof (pre_internal_incoming_unique _ _ e Hpoints Hparameter Hinternal He Heq) as Hsame.
  exact (proj2 (pre_expr_real_internal EV a Hlaw e u Hcomputed) b Hsame).
Qed.

Local Lemma pre_build_initial_scope_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b first :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  Graph.entries (live_graph (point_model (pre_ssa_points a))) = [first] ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first
    (pre_initial_scope EU a
      (filter (pre_total_pure (pre_expression a)) (pre_expr_universe EBE EV EU a))).
Proof.
  intros Hlaw Hready Hb Hfirst Hentry u Hfamily Hpure.
  rewrite pre_initial_scope_top.
  2: { apply filter_In; split; [apply (pre_expr_universe_exact EBE EV EU a Hlaw)|]; assumption. }
  apply (pre_initial_frame_laws EE EV a _ u b first Hlaw
    (pre_build_definition_edges EB EBE EN EE EV EU a Hlaw Hready) Hb Hfirst Hentry).
  - rewrite (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw); tauto.
  - exact (build_frg_occurrence_provenance EB EBE EN EE EV EU a Hlaw Hready).
Qed.

Local Lemma pre_no_definition_at_nonentry_first {S O B BE N E V K C U}
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f b first :
  pre_expr_ssa_laws EV a -> pre_definition_edges a f ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  ~ In b (Graph.entries (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  forall d, In d (frg_versions f) -> frg_version_point a d <> Some first.
Proof.
  intros Hlaw Hedges Hb Hnonentry Hfirst d Hd Hpoint.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_definition_first_initial a f b first d Hpoints Hedges Hb Hfirst Hd Hpoint)
    as Hinitial; rewrite Hinitial in Hpoint.
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [point [Hentry [Hpointentry Hposition]]]].
  change (nth_error (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0 = Some first)
    in Hpoint; rewrite Hpointentry in Hpoint; cbn in Hpoint; inversion Hpoint; subst point.
  assert (Hentrylisted : In entry (Graph.nodes (block_graph (pre_ssa_points a)))).
  { apply (entries_in (blocks_graph_wf Hpoints)); rewrite Hentry; left; reflexivity. }
  pose proof (points_owner Hpoints b first Hb (nth_error_In _ _ Hfirst)) as Howner.
  pose proof (points_owner Hpoints entry first Hentrylisted (nth_error_In _ _ Hposition))
    as Howner'.
  apply Hnonentry; rewrite Hentry; left; congruence.
Qed.

Local Lemma pre_no_occurrence_at_first {S O B BE N E V K C U} (EE : encoding E)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    (f : factored_redundancy_graph B BE E U) b first :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  (forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    pre_occurrence_entry_sound a e d) ->
  forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e <> first.
Proof.
  intros Hlaw Hb Hfirst Hoccurrences e d Hget.
  destruct (Hoccurrences e d Hget) as [He [Hcomputed Hrest]].
  exact (pre_internal_target_not_first _ e b first (pre_expr_points EV a Hlaw) He
    (proj1 (pre_expr_real_internal EV a Hlaw e _ Hcomputed)) Hb Hfirst).
Qed.

Local Lemma pre_no_kill_at_first {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) b first u :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  forall e, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
    Graph.target (live_graph (point_model (pre_ssa_points a))) e = first ->
    kill (pre_genkill (pre_expression a)) e u = false.
Proof.
  intros Hlaw Hfamily Hb Hfirst e He Htarget.
  destruct (kill (pre_genkill (pre_expression a)) e u) eqn:Hkill; [|reflexivity].
  exfalso; exact (pre_internal_target_not_first _ e b first (pre_expr_points EV a Hlaw) He
    (pre_kill_internal EV a e u Hlaw Hfamily He Hkill) Hb Hfirst Htarget).
Qed.

Local Lemma pre_parent_nonentry {S O B BE N E V K C U} (EB : encoding B)
    (a : pre_expr_ssa S O B BE N E V K C U) b c :
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  Map.get EB c (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))) = Some b ->
  ~ In c (Graph.entries (block_graph (pre_ssa_points a))).
Proof.
  intros Hready Hparent Hentry.
  pose proof (proj2 (proj2 (proj2 (dominator_tree_sound EB _ _ Hready))) c b Hparent)
    as [Hdom Hne].
  exact (Hne (pre_entry_dominator _ c b Hentry Hdom)).
Qed.

Local Lemma pre_scope_parent_laws {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f b c first scope :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_definition_edges a f ->
  (forall e d, Map.get EE e (frg_occurrence_index f) = Some d ->
    pre_occurrence_entry_sound a e d) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In c (Graph.nodes (block_graph (pre_ssa_points a))) ->
  Map.get EB c (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))) = Some b ->
  nth_error (points_in_block (pre_ssa_points a) c) 0 = Some first ->
  pre_scope_laws EE EU a f (last (points_in_block (pre_ssa_points a) b) first) scope ->
  pre_scope_laws EE EU a f first scope.
Proof.
  intros Hlaw Hblocks Hpoints Hedges Hoccurrences Hb Hc Hparent Hfirst Hscope u Hfamily Hpure.
  eapply (pre_frame_gap EN EE a f u
    (last (points_in_block (pre_ssa_points a) b) first) first).
  - exact (pre_block_parent_immediate EB EN EV a b c first
      Hlaw Hblocks Hpoints Hb Hc Hparent Hfirst).
  - intros d Hd Hexpr; exact (pre_no_definition_at_nonentry_first EV a f c first
      Hlaw Hedges Hc (pre_parent_nonentry EB a b c Hblocks Hparent) Hfirst d Hd).
  - intros e Hget; exact (pre_no_occurrence_at_first EE EV a f c first
      Hlaw Hc Hfirst Hoccurrences e _ Hget).
  - exact (pre_no_kill_at_first EV a c first u Hlaw Hfamily Hc Hfirst).
  - exact (Hscope u Hfamily Hpure).
Qed.

Local Lemma pre_frame_laws_sound {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) f u n frame :
  pre_frame_laws EE a f u n frame -> pre_frame_sound a u n frame.
Proof.
  intros [Hexpr [Hreal Hdefinition]]; split; [exact Hexpr|].
  destruct (frg_version_point a (frg_operand_version (fst frame))) as [q|] eqn:Hq.
  - destruct Hdefinition as [[Hd [Hu [position [Hposition [Hdom Hnearest]]]]] Havailable].
    assert (Heq : position = q) by congruence; subst position; split.
    + intros point Hpoint; assert (Hsame : point = q) by congruence; subst point; exact Hdom.
    + intros Htrue; exists q; reflexivity.
  - destruct Hdefinition as [Hunavailable [Hfalse Hnone]]; split.
    + intros q Hpoint; congruence.
    + intro Htrue; congruence.
Qed.

Local Lemma pre_frame_fresh_test {S O B BE N E V K C U} (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u n (frame : frg_operand B E U) available :
  pre_frame_sound a u n (frame, available) ->
  (if available then match frg_operand_version frame with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr (frg_operand_version frame))) (encode EU u))
    end else true) = negb available.
Proof.
  intros [Hexpr [Hpoint Havailable]]; destruct available; [|reflexivity].
  destruct frame as [d real]; cbn [fst snd frg_operand_version] in *.
  destruct d; cbn [frg_version_expr] in *.
  - destruct (Havailable eq_refl) as [q Hq]; discriminate.
  - rewrite Hexpr, Pos.eqb_refl; reflexivity.
  - rewrite Hexpr, Pos.eqb_refl; reflexivity.
  - rewrite Hexpr, Pos.eqb_refl; reflexivity.
Qed.

Local Lemma pre_rename_occurrence_decision {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    e u n scope (acc : pre_rename_acc B BE E U) :
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  pre_frame_sound a u n (pre_rename_top EU scope u) ->
  let frame := pre_rename_top EU scope u in
  pre_rename_occurrence EB EE EU a e (scope, acc) =
    if snd frame then
      ((Map.set EU u (FrgOperand (frg_operand_version (fst frame)) true, true) scope,
        PreRenameAcc (Map.set EE e (frg_operand_version (fst frame)) (pre_rename_occurrences acc))
          (pre_rename_fresh acc) (pre_rename_links acc) (pre_rename_unsafe acc)), None)
    else
      ((scope, PreRenameAcc (Map.set EE e (FrFresh e u) (pre_rename_occurrences acc))
        (FinSet.add EE e (pre_rename_fresh acc)) (pre_rename_links acc) (pre_rename_unsafe acc)),
       Some u).
Proof.
  intros Hcomputed Hpure Hsound frame; unfold pre_rename_occurrence; rewrite Hcomputed, Hpure.
  unfold frame; destruct (pre_rename_top EU scope u) as [operand available] eqn:Htop.
  rewrite (pre_frame_fresh_test EU a u n operand available Hsound).
  destruct available; reflexivity.
Qed.

Local Lemma pre_rename_alter_fresh {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) u :
  pre_rename_fresh (snd (pre_rename_alter EB EU a e work u)) = pre_rename_fresh (snd work).
Proof.
  destruct work as [scope acc]; unfold pre_rename_alter; cbn [snd].
  destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) u);
    [reflexivity|exact (proj1 (proj2 (pre_rename_mark_data EB EU scope acc u)))].
Qed.

Local Lemma pre_rename_exit_fresh {B BE N E U} (EB : encoding B) (EN : encoding N)
    (EU : encoding U) exits n scope (acc : pre_rename_acc B BE E U) :
  pre_rename_fresh (snd (pre_rename_exit EB EN EU exits n (scope, acc))) = pre_rename_fresh acc.
Proof.
  unfold pre_rename_exit; cbn [snd].
  apply pre_fold_projection; intros output u.
  exact (proj1 (proj2 (pre_rename_mark_data EB EU scope output u))).
Qed.

Local Lemma pre_rename_argument_fresh {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope (acc : pre_rename_acc B BE E U) key :
  pre_rename_fresh (pre_rename_argument EB EBE EU a scope acc key) = pre_rename_fresh acc.
Proof.
  destruct key as [be u]; unfold pre_rename_argument.
  destruct (pre_phi_translate a be u) as [v|]; [|reflexivity].
  destruct (pre_rename_top EU scope v) as [frame available]; reflexivity.
Qed.

Local Lemma pre_rename_instruction_fresh {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e :
  pre_rename_fresh (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e)) =
  pre_rename_fresh (snd (fst (pre_rename_occurrence EB EE EU a e work))).
Proof.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e work) as [[scope acc] fresh]; cbn [fst snd].
  pose proof (pre_fold_projection (pre_rename_alter EB EU a e)
    (fun state => pre_rename_fresh (snd state))
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)
    (pre_rename_alter_fresh EB EU a e)) as Hfold.
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)) as [frames output].
  cbn [fst snd] in Hfold |- *.
  exact (eq_trans (pre_rename_exit_fresh EB EN EU exits
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (pre_rename_definitions EB EE EU a phis b e fresh frames) output) Hfold).
Qed.

Local Lemma pre_rename_occurrence_fresh_other {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    e scope (acc : pre_rename_acc B BE E U) key : key <> e ->
  FinSet.mem EE key (pre_rename_fresh
    (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc))))) =
    FinSet.mem EE key (pre_rename_fresh acc).
Proof.
  intro Hne; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|]; [|reflexivity].
  destruct (pre_total_pure (pre_expression a) u); [|reflexivity].
  destruct (pre_rename_top EU scope u) as [[d real] available]; cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true); cbn [fst snd pre_rename_fresh]; [|reflexivity].
  rewrite dfs_mem_add; destruct (dfs_eq_dec EE key e); [congruence|reflexivity].
Qed.

Local Lemma pre_rename_instruction_fresh_other {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e key : key <> e ->
  FinSet.mem EE key (pre_rename_fresh (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e))) =
    FinSet.mem EE key (pre_rename_fresh (snd work)).
Proof.
  intro Hne; rewrite pre_rename_instruction_fresh; destruct work as [scope acc].
  exact (pre_rename_occurrence_fresh_other EB EE EU a e scope acc key Hne).
Qed.

Local Lemma pre_rename_instructions_fresh_other {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b es
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) key : ~ In key es ->
  FinSet.mem EE key (pre_rename_fresh (snd (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis b) es work))) =
    FinSet.mem EE key (pre_rename_fresh (snd work)).
Proof.
  revert work; induction es as [|e es IH]; intros work Houtside; [reflexivity|].
  cbn [fold_left]; rewrite IH by (intro Hin; apply Houtside; right; exact Hin).
  apply pre_rename_instruction_fresh_other; intro Heq; apply Houtside; left; symmetry; exact Heq.
Qed.

Local Lemma pre_rename_block_fresh_other {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc key :
  ~ In key (instruction_edges (pre_ssa_points a) b) ->
  FinSet.mem EE key (pre_rename_fresh (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))) =
    FinSet.mem EE key (pre_rename_fresh acc).
Proof.
  intro Houtside; unfold pre_rename_block.
  set (entered := match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end).
  pose proof (pre_rename_instructions_fresh_other EB EN EE EU a alterations exits phis b
    (instruction_edges (pre_ssa_points a) b) entered key Houtside) as Hbody.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
  cbn [snd] in Hbody; cbn [snd].
  rewrite (pre_fold_projection _ pre_rename_fresh _ output
    (pre_rename_argument_fresh EB EBE EU a frames)), Hbody.
  unfold entered; destruct (points_in_block (pre_ssa_points a) b); [reflexivity|].
  rewrite (pre_rename_exit_fresh EB EN EU exits n scope acc); reflexivity.
Qed.

Local Definition pre_fresh_completed {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U) seen (fresh : FinSet.t E) : Prop :=
  forall e, FinSet.mem EE e fresh = true -> FinSet.mem EB
    (block_of_point (pre_ssa_points a)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e)) seen = true.

Local Lemma pre_rename_block_fresh_completed {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc seen :
  pre_expr_ssa_laws EV a -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_fresh_completed EB EE a seen (pre_rename_fresh acc) ->
  pre_fresh_completed EB EE a (FinSet.add EB b seen) (pre_rename_fresh (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intros Hlaw Hb Hcompleted key Hget; rewrite dfs_mem_add.
  destruct (dfs_eq_dec EB (block_of_point (pre_ssa_points a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) key)) b) as [Heq|Hne];
    [reflexivity|].
  apply (Hcompleted key); rewrite pre_rename_block_fresh_other in Hget; [exact Hget|].
  intro Hin; apply Hne; exact
    (pre_instruction_owner _ b key (pre_expr_points EV a Hlaw) Hb Hin).
Qed.

Local Lemma pre_rename_step_seen {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work b :
  FinSet.mem EB b (snd (fst work)) = true -> FinSet.mem EB b (snd (fst
    (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work))) = true.
Proof.
  destruct work as [[[|[block scope] rest] seen] acc]; [exact (fun H => H)|].
  unfold pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB block seen);
    [exact (fun H => H)|].
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments block scope acc)
    as [frames output]; cbn [fst snd]; intro Hseen.
  rewrite dfs_mem_add; destruct (dfs_eq_dec EB b block); [reflexivity|exact Hseen].
Qed.

Local Lemma pre_rename_step_protected {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work key :
  pre_expr_ssa_laws EV a -> pre_work_sound EE EU a work ->
  FinSet.mem EB (block_of_point (pre_ssa_points a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) key)) (snd (fst work)) = true ->
  let result := pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work in
  Map.get EE key (pre_rename_occurrences (snd result)) =
    Map.get EE key (pre_rename_occurrences (snd work)) /\
  FinSet.mem EE key (pre_rename_fresh (snd result)) =
    FinSet.mem EE key (pre_rename_fresh (snd work)).
Proof.
  intros Hlaw; destruct work as [[[|[b scope] rest] seen] acc];
    intros [Hpending Hindex] Hseen; [split; reflexivity|].
  cbn [fst snd] in Hseen.
  unfold pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen) eqn:Hb;
    [split; reflexivity|].
  destruct (Hpending b scope (or_introl eq_refl)) as [Hlisted Hframes].
  assert (Houtside : ~ In key (instruction_edges (pre_ssa_points a) b)).
  { intro Hin; rewrite (pre_instruction_owner _ b key (pre_expr_points EV a Hlaw) Hlisted Hin)
      in Hseen; congruence. }
  pose proof (pre_rename_block_other EB EBE EN EE EU a alterations exits phis arguments b scope
    acc key Houtside) as Hoccurrence.
  pose proof (pre_rename_block_fresh_other EB EBE EN EE EU a alterations exits phis arguments b
    scope acc key Houtside) as Hfresh.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output] eqn:Hblock; rewrite ?Hblock in Hoccurrence, Hfresh;
    cbn [fst snd] in *; split; assumption.
Qed.

(** A proof trace exposes finite prefixes without changing the producer's binary recursion. *)
Inductive pre_walk_trace {X : Type} (step : X -> X) : X -> X -> Prop :=
  | pre_walk_done : forall x, pre_walk_trace step x x
  | pre_walk_next : forall x final, pre_walk_trace step (step x) final ->
      pre_walk_trace step x final.

Local Lemma pre_walk_trace_trans {X} (step : X -> X) x y z :
  pre_walk_trace step x y -> pre_walk_trace step y z -> pre_walk_trace step x z.
Proof.
  intros Hxy Hyz; induction Hxy; [exact Hyz|constructor; exact (IHHxy Hyz)].
Qed.

Local Lemma pre_walk_trace_iter {X} (step : X -> X) fuel x :
  pre_walk_trace step x (Pos.iter step x fuel).
Proof.
  induction fuel using Pos.peano_ind.
  - constructor; constructor.
  - rewrite Pos.iter_succ; eapply pre_walk_trace_trans; [exact IHfuel|constructor; constructor].
Qed.

Local Lemma pre_rename_trace_protected {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments work final key :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_work_sound EE EU a work ->
  pre_walk_trace (pre_rename_step EB EBE EN EE EU a (dom_children EB (Map.elements
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))))
      alterations exits phis arguments) work final ->
  FinSet.mem EB (block_of_point (pre_ssa_points a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) key)) (snd (fst work)) = true ->
  Map.get EE key (pre_rename_occurrences (snd final)) =
    Map.get EE key (pre_rename_occurrences (snd work)) /\
  FinSet.mem EE key (pre_rename_fresh (snd final)) =
    FinSet.mem EE key (pre_rename_fresh (snd work)).
Proof.
  intros Hlaw Hready Hsound Htrace; revert Hsound; induction Htrace as [work|work final Htrace IH];
    intros Hsound Hseen; [split; reflexivity|].
  pose proof (pre_rename_step_protected EB EBE EN EE EV EU a
    (dom_children EB (Map.elements (idom (dominator_tree
      (prepare EB (block_graph (pre_ssa_points a))))))) alterations exits phis arguments
    work key Hlaw Hsound Hseen)
    as [Hoccurrence Hfresh].
  destruct (IH (pre_rename_step_sound EB EBE EN EE EV EU a _ _ _ _ work Hlaw Hready Hsound)
    (pre_rename_step_seen EB EBE EN EE EU a _ _ _ _ _ work _ Hseen)) as [Hoccurrence' Hfresh'].
  rewrite Hoccurrence', Hfresh'; split; assumption.
Qed.

Local Lemma pre_build_definition_at_target {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b e u d :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  In d (frg_versions (build_frg EB EBE EN EE EV EU a)) -> frg_version_expr d = u ->
  frg_version_point a d = Some (Graph.target (live_graph (point_model (pre_ssa_points a))) e) ->
  d = FrFresh e u \/ (e = parameter_edge (pre_ssa_points a) b /\ d = FrPhi b u).
Proof.
  intros Hlaw Hready Hb Hin Hd Hexpr Hpoint; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (pre_instruction_edge_listed _ b e Hpoints Hb Hin) as He.
  pose proof (instruction_edges_internal Hpoints b e Hb Hin) as Hi.
  pose proof (pre_build_definition_edges EB EBE EN EE EV EU a Hlaw Hready d Hd) as Hshape.
  destruct d as [x|x|edge x|owner x]; cbn [frg_version_expr] in Hexpr; subst x.
  - discriminate.
  - exfalso; change (nth_error
      (Graph.entries (live_graph (point_model (pre_ssa_points a)))) 0 = Some
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)) in Hpoint.
    exact (pre_internal_target_not_entry EV a e _ Hlaw He Hi
      (nth_error_In _ _ Hpoint) eq_refl).
  - destruct Hshape as [Hedge Hinternal]; inversion Hpoint as [Heq].
    pose proof (pre_internal_incoming_unique _ e edge Hpoints He Hi Hedge Heq) as Hsame.
    subst edge; left; reflexivity.
  - destruct (pre_parameter_edge_listed _ owner Hpoints Hshape) as [Hparameter Hinternal].
    inversion Hpoint as [Heq].
    pose proof (pre_internal_incoming_unique _ e _ Hpoints He Hi Hparameter Heq) as Hsame.
    pose proof (pre_instruction_owner _ owner _ Hpoints Hshape
      (nth_error_In _ _ (parameter_edge_first Hpoints owner Hshape))) as Howner.
    rewrite Hsame in Howner; rewrite (pre_instruction_owner _ b e Hpoints Hb Hin) in Howner.
    subst owner; right; split; [symmetry; exact Hsame|reflexivity].
Qed.

Local Lemma pre_build_no_definition_at_target {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b e u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  ~ In (FrFresh e u) (frg_versions (build_frg EB EBE EN EE EV EU a)) ->
  (e = parameter_edge (pre_ssa_points a) b -> FinSet.mem (pair_encoding EB EU) (b, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = false) ->
  forall d, In d (frg_versions (build_frg EB EBE EN EE EV EU a)) -> frg_version_expr d = u ->
    frg_version_point a d <>
      Some (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Hlaw Hready Hb Hin Hfresh Hphi d Hd Hexpr Hpoint.
  destruct (pre_build_definition_at_target EB EBE EN EE EV EU a b e u d
    Hlaw Hready Hb Hin Hd Hexpr Hpoint) as [Heq|[Hparameter Heq]]; subst d.
  - exact (Hfresh Hd).
  - apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw) in Hd.
    rewrite (Hphi Hparameter) in Hd; discriminate.
Qed.

Local Lemma pre_frame_instruction {S O B BE N E V K C U} (EN : encoding N)
    (EE : encoding E) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U)
    f u e frame real available :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  (forall d, In d (frg_versions f) -> frg_version_expr d = u ->
    frg_version_point a d <> Some
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)) ->
  available = (snd frame && negb (kill (pre_genkill (pre_expression a)) e u)) ->
  (real = true <-> pre_real_use_at EE a f
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (frg_operand_version (fst frame))) ->
  pre_frame_laws EE a f u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) frame ->
  pre_frame_laws EE a f u
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (FrgOperand (frg_operand_version (fst frame)) real, available).
Proof.
  intros Hlaw Hready Hfamily He Hi Hnone Havailable Hreal
    [Hexpr [Holdreal Hdefinition]].
  unfold pre_frame_laws; cbn [fst snd frg_operand_version frg_operand_real_use].
  split; [exact Hexpr|]; split; [exact Hreal|].
  pose proof (pre_internal_immediate EV a e Hlaw He Hi) as Himmediate.
  destruct (frg_version_point a (frg_operand_version (fst frame))) as [q|] eqn:Hq.
  - destruct Hdefinition as [Hnearest Holdavailable]; split.
    + exact (pre_nearest_advance a f u _ _ _ Himmediate Hnone Hnearest).
    + rewrite Havailable, Bool.andb_true_iff, Bool.negb_true_iff, Holdavailable.
      apply iff_sym; apply (pre_kills_instruction EN EV a u q e Hlaw Hready Hfamily He Hi).
      destruct Hnearest as [Hd [Hu [position [Hpoint [Hdom Hnearest]]]]].
      assert (Heq : position = q) by congruence; subst position; exact Hdom.
  - destruct Hdefinition as [Hunavailable [Hfalse Hnoreach]].
    split; [exact Hunavailable|]; split.
    + rewrite Havailable, Hfalse; reflexivity.
    + exact (pre_no_reaching_advance a f u _ _ Himmediate Hnone Hnoreach).
Qed.

Local Lemma pre_rename_phi_blocks_exact {B U} (EB : encoding B) (EU : encoding U)
    (phis : FinSet.t (B * U)) b u : FinSet.wf (pair_encoding EB EU) phis ->
  (In u (FinSet.elements (pre_group_lookup EB
    (fold_left (pre_group_add EB EU) (FinSet.elements phis) Map.empty) b)) <->
    FinSet.mem (pair_encoding EB EU) (b, u) phis = true).
Proof.
  intro Hphis; rewrite (FinSet.elements_spec EU).
  2: { apply pre_group_fold_wf; intro key; unfold pre_group_lookup;
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact; unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite (FinSet.elements_spec (pair_encoding EB EU)) by exact Hphis.
  split; [intros [Hmem|Hfalse]; [exact Hmem|discriminate]|intro Hmem; left; exact Hmem].
Qed.

Local Lemma pre_rename_argument_index_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    (p : prepared EB (block_graph (pre_ssa_points a))) phis b be u :
  ready EB (block_graph (pre_ssa_points a)) p -> FinSet.wf (pair_encoding EB EU) phis ->
  (In (be, u) (FinSet.elements (pre_group_lookup EB
      (pre_rename_argument_index EB EBE EU a p phis) b)) <->
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.source (block_graph (pre_ssa_points a)) be = b /\
    FinSet.mem (pair_encoding EB EU)
      (Graph.target (block_graph (pre_ssa_points a)) be, u) phis = true).
Proof.
  intros Hready Hphis; unfold pre_rename_argument_index.
  rewrite (FinSet.elements_spec (pair_encoding EBE EU)).
  2: { apply pre_group_fold_wf; intro key; unfold pre_group_lookup;
       rewrite Map.get_empty; apply Map.wf_empty. }
  rewrite pre_group_fold_exact; unfold pre_group_lookup; rewrite Map.get_empty, FinSet.mem_empty.
  rewrite in_flat_map; split.
  - intros [[[target v] [Hphi Hin]]|Hfalse]; [|discriminate].
    apply in_map_iff in Hin; destruct Hin as [edge [Heq Hedge]]; inversion Heq; subst edge v.
    assert (Hlisted : In target (Graph.nodes (block_graph (pre_ssa_points a)))).
    { destruct (in_dec (dfs_eq_dec EB) target
        (Graph.nodes (block_graph (pre_ssa_points a)))) as [Hin|Hout]; [exact Hin|].
      rewrite (pred_domain (proj2 (proj2 Hready)) target Hout) in Hedge; contradiction. }
    apply (pre_pred_edges_exact EB _ p target be Hready Hlisted) in Hedge.
    destruct Hedge as [Hbe Htarget]; split; [exact Hbe|]; split; [congruence|].
    rewrite Htarget; apply (FinSet.elements_spec (pair_encoding EB EU)); assumption.
  - intros [Hbe [Hsource Hphi]]; left.
    exists (Graph.target (block_graph (pre_ssa_points a)) be, u); split.
    + apply (FinSet.elements_spec (pair_encoding EB EU)); assumption.
    + apply in_map_iff; exists be; split; [rewrite Hsource; reflexivity|].
      apply (pre_pred_edges_exact EB _ p _ be Hready); [|auto].
      apply in_flat_map in Hbe; destruct Hbe as [source [Hnode Hedge]].
      exact (out_target_in (proj1 Hready) source be Hnode Hedge).
Qed.

Local Lemma pre_rename_instruction_present {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e u :
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (pre_rename_occurrences (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e))) = Some d.
Proof.
  intros Hcomputed Hpure; rewrite pre_rename_instruction_occurrences.
  destruct work as [scope acc]; exact
    (pre_rename_occurrence_present EB EE EU a e u scope acc Hcomputed Hpure).
Qed.

Local Lemma pre_rename_instructions_present {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b es :
  NoDup es -> forall work e u, In e es -> pre_recomputed (pre_expression a) e = Some u ->
  pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (pre_rename_occurrences (snd (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis b) es work))) = Some d.
Proof.
  intro Hnodup; induction Hnodup as [|edge es Hfresh Hnodup IH];
    intros work e u Hin Hcomputed Hpure; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst edge; cbn [fold_left]; rewrite pre_rename_instructions_other by exact Hfresh.
    exact (pre_rename_instruction_present EB EN EE EU a alterations exits phis b work e u
      Hcomputed Hpure).
  - cbn [fold_left]; exact (IH _ e u Hin Hcomputed Hpure).
Qed.

Local Lemma pre_rename_block_present {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc e u :
  ssa_point_laws (pre_ssa_points a) -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (pre_rename_occurrences (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))) = Some d.
Proof.
  intros Hpoints Hb He Hcomputed Hpure; unfold pre_rename_block.
  set (entered := match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end).
  pose proof (pre_rename_instructions_present EB EN EE EU a alterations exits phis b
    (instruction_edges (pre_ssa_points a) b)
    (pre_chain_edges_nodup _ _ _ (points_graph_wf Hpoints)
      (points_ordered Hpoints b Hb) (points_unique Hpoints b)) entered e u He Hcomputed Hpure)
    as Hbody.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
  cbn [snd] in Hbody; cbn [snd].
  rewrite (pre_fold_projection _ pre_rename_occurrences _ output
    (pre_rename_argument_occurrences EB EBE EU a frames)); exact Hbody.
Qed.

Local Definition pre_occurrences_total {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U) seen
    (index : Map.t E (frg_version B E U)) : Prop :=
  forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  FinSet.mem EB b seen = true -> forall e u, In e (instruction_edges (pre_ssa_points a) b) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e index = Some d.

Local Lemma pre_rename_step_total {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_expr_ssa_laws EV a -> pre_work_sound EE EU a work ->
  pre_occurrences_total EB EE a (snd (fst work)) (pre_rename_occurrences (snd work)) ->
  let result := pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work in
  pre_occurrences_total EB EE a (snd (fst result)) (pre_rename_occurrences (snd result)).
Proof.
  intros Hlaw; destruct work as [[[|[b scope] rest] seen] acc];
    intros [Hpending Hindex] Htotal; [exact Htotal|].
  unfold pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen) eqn:Hseen;
    [exact Htotal|].
  destruct (Hpending b scope (or_introl eq_refl)) as [Hb Hframes].
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output] eqn:Hresult; cbn [fst snd].
  intros block Hblock Hmember e u He Hcomputed Hpure.
  assert (Hblock' : FinSet.mem EB block (FinSet.add EB b seen) = true).
  { exact Hmember. }
  rewrite dfs_mem_add in Hblock'; destruct (dfs_eq_dec EB block b) as [Heq|Hne].
  - subst block.
    pose proof (pre_rename_block_present EB EBE EN EE EU a alterations exits phis arguments
      b scope acc e u Hpoints Hb He Hcomputed Hpure) as Hpresent.
    rewrite Hresult in Hpresent; exact Hpresent.
  - destruct (Htotal block Hblock Hblock' e u He Hcomputed Hpure) as [d Hd]; exists d.
    pose proof (pre_rename_block_other EB EBE EN EE EU a alterations exits phis arguments b
      scope acc e) as Hother.
    assert (Houtside : ~ In e (instruction_edges (pre_ssa_points a) b)).
    { intro Hin; apply Hne; pose proof (pre_instruction_owner _ block e Hpoints Hblock He)
        as Howner; rewrite (pre_instruction_owner _ b e Hpoints Hb Hin) in Howner;
        symmetry; exact Howner. }
    specialize (Hother Houtside).
    rewrite Hresult in Hother; cbn [snd] in Hother; rewrite Hother; exact Hd.
Qed.

Local Lemma pre_rename_run_total_on_seen {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments fuel work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_work_sound EE EU a work ->
  pre_occurrences_total EB EE a (snd (fst work)) (pre_rename_occurrences (snd work)) ->
  let result := pre_rename_run (pre_rename_step EB EBE EN EE EU a (dom_children EB (Map.elements
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))))
      alterations exits phis arguments) fuel work in
  pre_occurrences_total EB EE a (snd (fst result)) (pre_rename_occurrences (snd result)).
Proof.
  intros Hlaw Hready Hsound Htotal; rewrite pre_rename_run_agrees by reflexivity.
  refine (proj2 (pre_iter_invariant _ (fun state => pre_work_sound EE EU a state /\
    pre_occurrences_total EB EE a (snd (fst state)) (pre_rename_occurrences (snd state)))
    fuel work _ (conj Hsound Htotal))).
  intros state [Hstate Hcovered]; split.
  - exact (pre_rename_step_sound EB EBE EN EE EV EU a alterations exits phis arguments
      state Hlaw Hready Hstate).
  - exact (pre_rename_step_total EB EBE EN EE EV EU a _ alterations exits phis arguments
      state Hlaw Hstate Hcovered).
Qed.

Local Lemma pre_rename_run_eligible {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments family :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  let parents := Map.elements (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))
    in
  let roots := Graph.entries (block_graph (pre_ssa_points a)) in
  let scope := pre_initial_scope EU a family in
  let initial := (map (fun b => (b, scope)) roots, FinSet.empty,
    PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty) in
  let result := pre_rename_run (pre_rename_step EB EBE EN EE EU a (dom_children EB parents)
    alterations exits phis arguments) (Pos.of_succ_nat (length roots + length parents)) initial in
  forall e u, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (pre_rename_occurrences (snd result)) = Some d.
Proof.
  intros Hlaw Hready parents roots scope initial result e u He Hcomputed Hpure.
  pose proof (pre_initial_work_sound EE EV EU a family Hlaw) as Hsound.
  assert (Hinitial : pre_occurrences_total EB EE a (snd (fst initial))
    (pre_rename_occurrences (snd initial))).
  { intros b Hb Hfalse; cbn [initial snd fst] in Hfalse;
      rewrite FinSet.mem_empty in Hfalse; discriminate. }
  pose proof (pre_rename_run_total_on_seen EB EBE EN EE EV EU a alterations exits phis arguments
    (Pos.of_succ_nat (length roots + length parents)) initial Hlaw Hready Hsound Hinitial)
    as Htotal.
  destruct (pre_internal_edge_block _ e (pre_expr_points EV a Hlaw) He
    (proj1 (pre_expr_real_internal EV a Hlaw e u Hcomputed))) as [b [Hb [Hin Htarget]]].
  exact (Htotal b Hb (pre_rename_seen_all EB EBE EN EE EV EU a alterations exits phis arguments
    scope (PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty) Hlaw Hready b Hb)
    e u Hin Hcomputed Hpure).
Qed.

(** Every listed eligible recomputation has a finite graph occurrence. *)
Theorem build_frg_occurrence_total {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall e u, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  exists d, Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) = Some d.
Proof.
  intros Hlaw Hready; unfold build_frg; cbn zeta; cbn [frg_occurrence_index].
  apply (pre_rename_run_eligible EB EBE EN EE EV EU a _ _ _ _ _ Hlaw Hready).
Qed.

Local Lemma pre_rename_alters_query {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    family e (work : pre_rename_scope B E U * pre_rename_acc B BE E U) u :
  pre_expr_ssa_laws EV a -> pre_expr_in_family a u ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) -> In u family ->
  pre_rename_top EU (fst (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e)) work)) u =
    (fst (pre_rename_top EU (fst work) u),
      snd (pre_rename_top EU (fst work) u) && negb (kill (pre_genkill (pre_expression a)) e u)).
Proof.
  intros Hlaw Hmember He Hu; rewrite pre_rename_alters_top.
  destruct (in_dec (dfs_eq_dec EU) u (FinSet.elements
    (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e))) as [Hin|Hout].
  - apply (pre_rename_alter_index_sound EE EV EU a family e u) in Hin.
    destruct Hin as [Hedge [Hfamily Hkill]]; rewrite Hkill, andb_false_r; reflexivity.
  - assert (Hkill : kill (pre_genkill (pre_expression a)) e u = false).
    { destruct (kill (pre_genkill (pre_expression a)) e u) eqn:Hkill; [|reflexivity].
      exfalso; apply Hout; apply (pre_rename_alter_index_exact EE EV EU a family e u
        Hlaw Hmember); auto. }
    rewrite Hkill, andb_true_r; destruct (pre_rename_top EU (fst work) u); reflexivity.
Qed.

Local Lemma pre_rename_definitions_top {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    phis b e fresh (scope : pre_rename_scope B E U) u :
  pre_rename_top EU (pre_rename_definitions EB EE EU a phis b e fresh scope) u =
    if Pos.eqb (encode EE e) (encode EE (parameter_edge (pre_ssa_points a) b)) then
      if in_dec (dfs_eq_dec EU) u (FinSet.elements (pre_group_lookup EB phis b))
      then (FrgOperand (FrPhi b u) false, true)
      else match fresh with
        | Some v => if dfs_eq_dec EU u v then (FrgOperand (FrFresh e v) true, true)
            else pre_rename_top EU scope u
        | None => pre_rename_top EU scope u
        end
    else match fresh with
      | Some v => if dfs_eq_dec EU u v then (FrgOperand (FrFresh e v) true, true)
          else pre_rename_top EU scope u
      | None => pre_rename_top EU scope u
      end.
Proof.
  unfold pre_rename_definitions.
  destruct (Pos.eqb (encode EE e) (encode EE (parameter_edge (pre_ssa_points a) b))).
  - rewrite pre_rename_phis_top; destruct (in_dec (dfs_eq_dec EU) u
      (FinSet.elements (pre_group_lookup EB phis b))); [reflexivity|].
    destruct fresh; [rewrite pre_rename_top_set|]; reflexivity.
  - destruct fresh; [rewrite pre_rename_top_set|]; reflexivity.
Qed.

Local Definition pre_work_fresh_completed {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (a : pre_expr_ssa S O B BE N E V K C U)
    (work : pre_rename_work B BE E U) : Prop :=
  pre_fresh_completed EB EE a (snd (fst work)) (pre_rename_fresh (snd work)).

Local Lemma pre_rename_step_fresh_completed {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_expr_ssa_laws EV a -> pre_work_sound EE EU a work ->
  pre_work_fresh_completed EB EE a work ->
  pre_work_fresh_completed EB EE a
    (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work).
Proof.
  intros Hlaw; destruct work as [[[|[b scope] rest] seen] acc];
    intros [Hpending Hindex] Hcompleted; [exact Hcompleted|].
  unfold pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen);
    [exact Hcompleted|].
  destruct (Hpending b scope (or_introl eq_refl)) as [Hb Hframes].
  pose proof (pre_rename_block_fresh_completed EB EBE EN EE EV EU a alterations exits phis
    arguments b scope acc seen Hlaw Hb Hcompleted) as Hdone.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output] eqn:Hblock; rewrite ?Hblock in Hdone; exact Hdone.
Qed.

Local Lemma pre_block_unwritten {S O B BE N E V K C U} (EB : encoding B) (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) b seen (acc : pre_rename_acc B BE E U) :
  ssa_point_laws (pre_ssa_points a) -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  FinSet.mem EB b seen = false ->
  pre_occurrences_completed EB EE a seen (pre_rename_occurrences acc) ->
  pre_fresh_completed EB EE a seen (pre_rename_fresh acc) ->
  forall e, In e (instruction_edges (pre_ssa_points a) b) ->
  Map.get EE e (pre_rename_occurrences acc) = None /\
    FinSet.mem EE e (pre_rename_fresh acc) = false.
Proof.
  intros Hpoints Hb Hnew Hoccurrences Hfresh e He.
  pose proof (pre_instruction_owner _ b e Hpoints Hb He) as Howner; split.
  - destruct (Map.get EE e (pre_rename_occurrences acc)) as [d|] eqn:Hget; [|reflexivity].
    pose proof (Hoccurrences e d Hget) as Hseen; rewrite Howner in Hseen; congruence.
  - destruct (FinSet.mem EE e (pre_rename_fresh acc)) eqn:Hget; [|reflexivity].
    pose proof (Hfresh e Hget) as Hseen; rewrite Howner in Hseen; congruence.
Qed.

Local Lemma pre_walk_trace_invariant {X} (step : X -> X) (P : X -> Prop) x final :
  pre_walk_trace step x final -> (forall state, P state -> P (step state)) -> P x -> P final.
Proof.
  intros Htrace Hstep; induction Htrace; intro Hinitial; [exact Hinitial|].
  apply IHHtrace; apply Hstep; exact Hinitial.
Qed.

Local Definition pre_instruction_packet {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    e (result : pre_rename_scope B E U * pre_rename_acc B BE E U) : Prop :=
  Map.get EE e (frg_occurrence_index f) = Map.get EE e (pre_rename_occurrences (snd result)) /\
  FinSet.mem EE e (frg_fresh_index f) = FinSet.mem EE e (pre_rename_fresh (snd result)).

Local Lemma pre_instruction_packet_real {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f alterations exits phis b e u n scope acc :
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  pre_frame_sound a u n (pre_rename_top EU scope u) ->
  FinSet.mem EE e (pre_rename_fresh acc) = false ->
  pre_instruction_packet EE a f e
    (pre_rename_instruction EB EN EE EU a alterations exits phis b (scope, acc) e) ->
  let frame := pre_rename_top EU scope u in
  Map.get EE e (frg_occurrence_index f) =
    Some (if snd frame then frg_operand_version (fst frame) else FrFresh e u) /\
  FinSet.mem EE e (frg_fresh_index f) = negb (snd frame).
Proof.
  intros Hcomputed Hpure Hsound Hfresh [Hoccurrence Hflag] frame.
  rewrite pre_rename_instruction_occurrences in Hoccurrence.
  rewrite pre_rename_instruction_fresh in Hflag.
  rewrite (pre_rename_occurrence_decision EB EE EU a e u n scope acc Hcomputed Hpure Hsound)
    in Hoccurrence, Hflag.
  unfold frame; destruct (snd (pre_rename_top EU scope u)) eqn:Havailable;
    cbn [fst snd pre_rename_occurrences pre_rename_fresh negb] in Hoccurrence, Hflag |- *.
  - rewrite Map.get_set_same in Hoccurrence; rewrite Hfresh in Hflag; auto.
  - rewrite Map.get_set_same in Hoccurrence.
    assert (Hadded : FinSet.mem EE e (FinSet.add EE e (pre_rename_fresh acc)) = true).
    { apply FinSet.mem_add; left; reflexivity. }
    rewrite Hadded in Hflag; auto.
Qed.

Local Lemma pre_instruction_packet_ineligible {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f alterations exits phis b e scope acc :
  (pre_recomputed (pre_expression a) e = None \/ exists u,
    pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u = false) ->
  Map.get EE e (pre_rename_occurrences acc) = None ->
  FinSet.mem EE e (pre_rename_fresh acc) = false ->
  pre_instruction_packet EE a f e
    (pre_rename_instruction EB EN EE EU a alterations exits phis b (scope, acc) e) ->
  Map.get EE e (frg_occurrence_index f) = None /\ FinSet.mem EE e (frg_fresh_index f) = false.
Proof.
  intros Hcomputed Hoccurrence Hfresh [Hget Hflag].
  rewrite pre_rename_instruction_occurrences in Hget; rewrite pre_rename_instruction_fresh in Hflag.
  unfold pre_rename_occurrence in Hget, Hflag.
  destruct Hcomputed as [Hnone|[u [Hsome Hpure]]].
  - rewrite Hnone in Hget, Hflag; cbn [fst snd] in Hget, Hflag; rewrite Hoccurrence in Hget;
      rewrite Hfresh in Hflag; auto.
  - rewrite Hsome, Hpure in Hget, Hflag; cbn [fst snd] in Hget, Hflag;
      rewrite Hoccurrence in Hget; rewrite Hfresh in Hflag; auto.
Qed.

Local Lemma pre_rename_instruction_top {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e u :
  pre_rename_top EU (fst
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e)) u =
  let '(observed, fresh) := pre_rename_occurrence EB EE EU a e work in
  pre_rename_top EU (pre_rename_definitions EB EE EU a phis b e fresh
    (fst (fold_left (pre_rename_alter EB EU a e)
      (FinSet.elements (pre_group_lookup EE alterations e)) observed))) u.
Proof.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e work) as [[scope acc] fresh].
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)) as [frames output].
  cbn [fst snd]; rewrite (proj1 (pre_rename_exit_scope EB EN EU exits _ _ output)); reflexivity.
Qed.

Local Lemma pre_build_phi_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  FinSet.wf (pair_encoding EB EU) (frg_phi_index (build_frg EB EBE EN EE EV EU a)).
Proof.
  unfold build_frg; cbn [frg_phi_index]; unfold pre_rename_phi_index.
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Local Lemma pre_build_fresh_present {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e u : pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_recomputed (pre_expression a) e = Some u ->
  FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) = true ->
  In (FrFresh e u) (frg_versions (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw He Hcomputed Hfresh; apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw).
  auto.
Qed.

Local Lemma pre_build_fresh_absent {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e u : pre_expr_ssa_laws EV a ->
  (FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) = false \/
    pre_recomputed (pre_expression a) e <> Some u) ->
  ~ In (FrFresh e u) (frg_versions (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw Hnone Hin; apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw) in Hin.
  destruct Hin as [He [Hcomputed Hfresh]]; destruct Hnone; congruence.
Qed.

Local Lemma pre_target_reachable {S O B BE N E V K C U} (EV : encoding V)
    (a : pre_expr_ssa S O B BE N E V K C U) e : pre_expr_ssa_laws EV a ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a)))
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e).
Proof.
  intros Hlaw He; pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct (pre_listed_edge_out _ e (points_graph_wf Hpoints) He) as [Hsource Hedge].
  exact (pre_expr_reachable_points EV a Hlaw _
    (out_target_in (points_graph_wf Hpoints) _ e Hsource Hedge)).
Qed.

Local Lemma pre_rename_occurrence_skipped {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) :
  (pre_recomputed (pre_expression a) e = None \/ exists u,
    pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u = false) ->
  pre_rename_occurrence EB EE EU a e work = (work, None).
Proof.
  intros [Hnone|[u [Hsome Hpure]]]; destruct work as [scope acc];
    unfold pre_rename_occurrence; [rewrite Hnone|rewrite Hsome, Hpure]; reflexivity.
Qed.

Local Lemma pre_rename_instruction_skipped_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b e scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  (pre_recomputed (pre_expression a) e = None \/ exists u,
    pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u = false) ->
  Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) = None ->
  FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) = false ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (fst (pre_rename_instruction EB EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (fold_left (pre_group_add EB EU)
        (FinSet.elements (frg_phi_index (build_frg EB EBE EN EE EV EU a))) Map.empty)
      b (scope, acc) e)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hin Hskip Hget Hfresh Hscope u Hu Hpure.
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (pre_instruction_edge_listed _ b e Hssa Hb Hin) as He.
  pose proof (instruction_edges_internal Hssa b e Hb Hin) as Hi.
  pose proof (Hscope u Hu Hpure) as Hframe.
  pose proof (pre_build_phi_wf EB EBE EN EE EV EU a) as Hphis.
  pose proof (build_frg_occurrence_provenance EB EBE EN EE EV EU a Hlaw Hblocks) as Hoccurrences.
  rewrite pre_rename_instruction_top, (pre_rename_occurrence_skipped EB EE EU a e _ Hskip).
  cbn [fst snd]; rewrite pre_rename_definitions_top.
  destruct (Pos.eqb (encode EE e) (encode EE (parameter_edge (pre_ssa_points a) b))) eqn:Hparameter.
  - destruct (in_dec (dfs_eq_dec EU) u (FinSet.elements (pre_group_lookup EB
      (fold_left (pre_group_add EB EU)
        (FinSet.elements (frg_phi_index (build_frg EB EBE EN EE EV EU a))) Map.empty) b)))
      as [Hphi|Hnphi].
    + apply Pos.eqb_eq in Hparameter; apply (encode_injective EE) in Hparameter; subst e.
      apply (pre_definition_frame_laws EN EE a _ u _ (FrPhi b u) false Hpoints
        (pre_target_reachable EV a _ Hlaw He)).
      * apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw).
        apply (pre_rename_phi_blocks_exact EB EU _ b u Hphis); exact Hphi.
      * reflexivity.
      * reflexivity.
      * split; [discriminate|intro Hreal; exfalso].
        exact (pre_phi_no_real_use EN EE EV a _ b u Hlaw Hpoints Hb Hoccurrences Hreal).
    + rewrite (pre_rename_alters_query EB EE EV EU a family e (scope, acc) u Hlaw Hu He
        (proj2 (Hfamily u) (conj Hu Hpure))).
      assert (Hphiabsent : FinSet.mem (pair_encoding EB EU) (b, u)
        (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = false).
      { destruct (FinSet.mem (pair_encoding EB EU) (b, u)
          (frg_phi_index (build_frg EB EBE EN EE EV EU a))) eqn:Hmem; [|reflexivity].
        exfalso; apply Hnphi; apply (pre_rename_phi_blocks_exact EB EU _ b u Hphis); exact Hmem. }
      cbn [fst snd].
      destruct (pre_rename_top EU scope u) as [[d real] available] eqn:Htop.
      apply (pre_frame_instruction EN EE EV a _ u e (FrgOperand d real, available) real
        (available && negb (kill (pre_genkill (pre_expression a)) e u)) Hlaw Hpoints Hu He Hi).
      * apply (pre_build_no_definition_at_target EB EBE EN EE EV EU a b e u Hlaw Hblocks Hb Hin).
        -- apply (pre_build_fresh_absent EB EBE EN EE EV EU a e u Hlaw); left; exact Hfresh.
        -- intros Heq; exact Hphiabsent.
      * reflexivity.
      * rewrite (pre_real_use_instruction EE EV a _ e d Hlaw He Hi Hoccurrences).
        rewrite Hget; cbn [pre_frame_laws fst snd frg_operand_real_use] in Hframe.
        destruct Hframe as [Hexpr [Hreal Hdefinition]]; split.
        -- intro Htrue; left; apply Hreal; exact Htrue.
        -- intros [Huse|Hfalse]; [apply Hreal; exact Huse|discriminate].
      * exact Hframe.
  - rewrite (pre_rename_alters_query EB EE EV EU a family e (scope, acc) u Hlaw Hu He
      (proj2 (Hfamily u) (conj Hu Hpure))).
    cbn [fst snd].
    destruct (pre_rename_top EU scope u) as [[d real] available] eqn:Htop.
    apply (pre_frame_instruction EN EE EV a _ u e (FrgOperand d real, available) real
      (available && negb (kill (pre_genkill (pre_expression a)) e u)) Hlaw Hpoints Hu He Hi).
    + apply (pre_build_no_definition_at_target EB EBE EN EE EV EU a b e u Hlaw Hblocks Hb Hin).
      * apply (pre_build_fresh_absent EB EBE EN EE EV EU a e u Hlaw); left; exact Hfresh.
      * intro Heq; rewrite Heq, Pos.eqb_refl in Hparameter; discriminate.
    + reflexivity.
    + rewrite (pre_real_use_instruction EE EV a _ e d Hlaw He Hi Hoccurrences), Hget.
      cbn [pre_frame_laws fst snd frg_operand_real_use] in Hframe.
      destruct Hframe as [Hexpr [Hreal Hdefinition]]; split.
      * intro Htrue; left; apply Hreal; exact Htrue.
      * intros [Huse|Hfalse]; [apply Hreal; exact Huse|discriminate].
    + exact Hframe.
Qed.

Local Lemma pre_frame_unchanged_instruction {S O B BE N E V K C U} (EN : encoding N)
    (EE : encoding E) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f u e frame :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  (forall d, In d (frg_versions f) -> frg_version_expr d = u ->
    frg_version_point a d <> Some
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)) ->
  (forall edge version, Map.get EE edge (frg_occurrence_index f) = Some version ->
    pre_occurrence_entry_sound a edge version) ->
  Map.get EE e (frg_occurrence_index f) <> Some (frg_operand_version (fst frame)) ->
  pre_frame_laws EE a f u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) frame ->
  pre_frame_laws EE a f u
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (fst frame, snd frame && negb (kill (pre_genkill (pre_expression a)) e u)).
Proof.
  intros Hlaw Hready Hfamily He Hi Hnone Hoccurrences Hcurrent Hframe.
  destruct frame as [[d real] available]; cbn [fst snd frg_operand_version] in *.
  apply (pre_frame_instruction EN EE EV a f u e (FrgOperand d real, available) real
    (available && negb (kill (pre_genkill (pre_expression a)) e u))
    Hlaw Hready Hfamily He Hi Hnone eq_refl); [|exact Hframe].
  rewrite (pre_real_use_instruction EE EV a f e d Hlaw He Hi Hoccurrences).
  pose proof (proj1 (proj2 Hframe)) as Hreal; cbn [fst frg_operand_real_use] in Hreal.
  split.
  - intro Htrue; left; apply Hreal; exact Htrue.
  - intros [Huse|Hget]; [apply Hreal; exact Huse|exfalso; exact (Hcurrent Hget)].
Qed.

Local Lemma pre_frame_reused_instruction {S O B BE N E V K C U} (EN : encoding N)
    (EE : encoding E) (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f u e operand :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  (forall d, In d (frg_versions f) -> frg_version_expr d = u ->
    frg_version_point a d <> Some
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)) ->
  Map.get EE e (frg_occurrence_index f) = Some (frg_operand_version operand) ->
  pre_frame_laws EE a f u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) (operand, true) ->
  pre_frame_laws EE a f u
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (FrgOperand (frg_operand_version operand) true,
      negb (kill (pre_genkill (pre_expression a)) e u)).
Proof.
  intros Hlaw Hready Hfamily He Hi Hnone Hget Hframe.
  apply (pre_frame_instruction EN EE EV a f u e (operand, true) true
    (negb (kill (pre_genkill (pre_expression a)) e u))
    Hlaw Hready Hfamily He Hi Hnone eq_refl); [|exact Hframe].
  split; [intros Htrue; exists e; split; [exact Hget|apply dominates_refl]|intros Hreal;
    reflexivity].
Qed.

Local Lemma pre_rename_instruction_real_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b e v scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  pre_recomputed (pre_expression a) e = Some v -> pre_total_pure (pre_expression a) v = true ->
  FinSet.mem EE e (pre_rename_fresh acc) = false ->
  pre_instruction_packet EE a (build_frg EB EBE EN EE EV EU a) e
    (pre_rename_instruction EB EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (fold_left (pre_group_add EB EU)
        (FinSet.elements (frg_phi_index (build_frg EB EBE EN EE EV EU a))) Map.empty)
      b (scope, acc) e) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (fst (pre_rename_instruction EB EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (fold_left (pre_group_add EB EU)
        (FinSet.elements (frg_phi_index (build_frg EB EBE EN EE EV EU a))) Map.empty)
      b (scope, acc) e)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hin Hcomputed Hpurev Hfresh Hpacket Hscope.
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (pre_instruction_edge_listed _ b e Hssa Hb Hin) as He.
  pose proof (instruction_edges_internal Hssa b e Hb Hin) as Hi.
  assert (Hv : pre_expr_in_family a v).
  { apply pre_family_seed; exact (pre_expr_occurrences EV a Hlaw e v Hcomputed). }
  pose proof (Hscope v Hv Hpurev) as Hframev.
  pose proof (pre_frame_laws_sound EE a _ v _ _ Hframev) as Hsoundv.
  pose proof (pre_rename_occurrence_decision EB EE EU a e v _ scope acc Hcomputed Hpurev Hsoundv)
    as Hdecision.
  pose proof (pre_instruction_packet_real EB EN EE EU a _ _ _ _ b e v _ scope acc
    Hcomputed Hpurev Hsoundv Hfresh Hpacket) as Hdata.
  assert (Hparameter : Pos.eqb (encode EE e)
    (encode EE (parameter_edge (pre_ssa_points a) b)) = false).
  { apply Pos.eqb_neq; intro Heq; apply (encode_injective EE) in Heq.
    exact (proj2 (pre_expr_real_internal EV a Hlaw e v Hcomputed) b Heq). }
  pose proof (build_frg_occurrence_provenance EB EBE EN EE EV EU a Hlaw Hblocks) as Hoccurrences.
  intros u Hu Hpure; pose proof (Hscope u Hu Hpure) as Hframeu.
  assert (Hufamily : In u family) by (apply Hfamily; auto).
  rewrite pre_rename_instruction_top, Hdecision.
  destruct (pre_rename_top EU scope v) as [operand available] eqn:Htopv.
  cbn [fst snd] in Hdata |- *; destruct available; cbn [fst snd] in Hdata |- *;
    destruct Hdata as [Hget Hflag].
  - rewrite pre_rename_definitions_top, Hparameter.
    rewrite (pre_rename_alters_query EB EE EV EU a family e _ u Hlaw Hu He Hufamily);
      cbn [fst snd].
    rewrite pre_rename_top_set; destruct (dfs_eq_dec EU u v) as [Heq|Hne].
    + subst u; apply (pre_frame_reused_instruction EN EE EV a _ v e operand
        Hlaw Hpoints Hv He Hi); [|exact Hget|exact Hframev].
      apply (pre_build_no_definition_at_target EB EBE EN EE EV EU a b e v Hlaw Hblocks Hb Hin).
      * apply (pre_build_fresh_absent EB EBE EN EE EV EU a e v Hlaw); left; exact Hflag.
      * intro Heq; rewrite Heq, Pos.eqb_refl in Hparameter; discriminate.
    + apply (pre_frame_unchanged_instruction EN EE EV a _ u e (pre_rename_top EU scope u)
        Hlaw Hpoints Hu He Hi); [|exact Hoccurrences| |exact Hframeu].
      * apply (pre_build_no_definition_at_target EB EBE EN EE EV EU a b e u Hlaw Hblocks Hb Hin).
        -- apply (pre_build_fresh_absent EB EBE EN EE EV EU a e u Hlaw); left; exact Hflag.
        -- intro Heq; rewrite Heq, Pos.eqb_refl in Hparameter; discriminate.
      * intro Hcurrent; rewrite Hget in Hcurrent; injection Hcurrent as Heq.
        pose proof (proj1 Hframev) as Hexprv; pose proof (proj1 Hframeu) as Hexpru.
        cbn [fst frg_operand_version] in Hexprv; rewrite Heq in Hexprv; congruence.
  - rewrite pre_rename_definitions_top, Hparameter.
    destruct (dfs_eq_dec EU u v) as [Heq|Hne].
    + subst u; apply (pre_definition_frame_laws EN EE a _ v _ (FrFresh e v) true Hpoints
        (pre_target_reachable EV a e Hlaw He)).
      * exact (pre_build_fresh_present EB EBE EN EE EV EU a e v Hlaw He Hcomputed Hflag).
      * reflexivity.
      * reflexivity.
      * split; [intro Htrue; exists e; split; [exact Hget|apply dominates_refl]|intros Hreal;
        reflexivity].
    + rewrite (pre_rename_alters_query EB EE EV EU a family e _ u Hlaw Hu He Hufamily).
      cbn [fst snd]; apply (pre_frame_unchanged_instruction EN EE EV a _ u e
        (pre_rename_top EU scope u) Hlaw Hpoints Hu He Hi); [|exact Hoccurrences| |exact Hframeu].
      * apply (pre_build_no_definition_at_target EB EBE EN EE EV EU a b e u Hlaw Hblocks Hb Hin).
        -- apply (pre_build_fresh_absent EB EBE EN EE EV EU a e u Hlaw); right; congruence.
        -- intro Heq; rewrite Heq, Pos.eqb_refl in Hparameter; discriminate.
      * intro Hcurrent; rewrite Hget in Hcurrent; injection Hcurrent as Heq.
        pose proof (proj1 Hframeu) as Hexpru; rewrite <- Heq in Hexpru.
        cbn [frg_version_expr] in Hexpru; congruence.
Qed.

Local Definition pre_build_phi_blocks {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :=
  fold_left (pre_group_add EB EU)
    (FinSet.elements (frg_phi_index (build_frg EB EBE EN EE EV EU a))) Map.empty.

Local Definition pre_instruction_step {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b :=
  pre_rename_instruction EB EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
    (pre_build_phi_blocks EB EBE EN EE EV EU a) b.

Local Lemma pre_rename_instruction_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b e scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  In e (instruction_edges (pre_ssa_points a) b) ->
  Map.get EE e (pre_rename_occurrences acc) = None ->
  FinSet.mem EE e (pre_rename_fresh acc) = false ->
  pre_instruction_packet EE a (build_frg EB EBE EN EE EV EU a) e
    (pre_instruction_step EB EBE EN EE EV EU a family exits b (scope, acc) e) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (fst (pre_instruction_step EB EBE EN EE EV EU a family exits b (scope, acc) e)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hin Hnone Hfresh Hpacket Hscope.
  destruct (pre_recomputed (pre_expression a) e) as [v|] eqn:Hcomputed.
  - destruct (pre_total_pure (pre_expression a) v) eqn:Hpure.
    + exact (pre_rename_instruction_real_laws EB EBE EN EE EV EU a family exits b e v scope acc
        Hlaw Hblocks Hpoints Hfamily Hb Hin Hcomputed Hpure Hfresh Hpacket Hscope).
    + assert (Hskip : pre_recomputed (pre_expression a) e = None \/ exists u,
        pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u =
          false).
      { right; exists v; auto. }
      destruct (pre_instruction_packet_ineligible EB EN EE EU a _ _ _ _ b e scope acc
        Hskip Hnone Hfresh Hpacket) as [Hget Hflag].
      exact (pre_rename_instruction_skipped_laws EB EBE EN EE EV EU a family exits b e scope acc
        Hlaw Hblocks Hpoints Hfamily Hb Hin Hskip Hget Hflag Hscope).
  - assert (Hskip : pre_recomputed (pre_expression a) e = None \/ exists u,
      pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u = false).
    { left; exact Hcomputed. }
    destruct (pre_instruction_packet_ineligible EB EN EE EU a _ _ _ _ b e scope acc
      Hskip Hnone Hfresh Hpacket) as [Hget Hflag].
    exact (pre_rename_instruction_skipped_laws EB EBE EN EE EV EU a family exits b e scope acc
      Hlaw Hblocks Hpoints Hfamily Hb Hin Hskip Hget Hflag Hscope).
Qed.

Local Definition pre_instruction_table {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) f es
    (result : pre_rename_scope B E U * pre_rename_acc B BE E U) : Prop :=
  forall e, In e es -> pre_instruction_packet EE a f e result.

Local Definition pre_unwritten {B BE E U} (EE : encoding E) es (acc : pre_rename_acc B BE E U) :
    Prop := forall e, In e es -> Map.get EE e (pre_rename_occurrences acc) = None /\
      FinSet.mem EE e (pre_rename_fresh acc) = false.

Local Lemma pre_rename_instructions_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b ns es first default :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  point_chain (live_graph (point_model (pre_ssa_points a))) ns es -> NoDup es ->
  (forall e, In e es -> In e (instruction_edges (pre_ssa_points a) b)) ->
  nth_error ns 0 = Some first -> forall work,
  pre_unwritten EE es (snd work) ->
  pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a) es
    (fold_left (pre_instruction_step EB EBE EN EE EV EU a family exits b) es work) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first (fst work) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) (last ns default)
    (fst (fold_left (pre_instruction_step EB EBE EN EE EV EU a family exits b) es work)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hchain; revert first.
  induction Hchain as [n|n m ns edge es Hedge Htarget Hchain IH];
    intros first Hnodup Hinstructions Hfirst [scope acc] Hunwritten Htable Hscope;
    cbn in Hfirst; inversion Hfirst; subst first; [exact Hscope|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Hnodup].
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (out_source (points_graph_wf Hssa) n edge Hedge) as Hsource.
  destruct (Hunwritten edge (or_introl eq_refl)) as [Hnone Hfreshflag].
  pose proof (Htable edge (or_introl eq_refl)) as Hpacket.
  cbn [fold_left] in Hpacket.
  unfold pre_instruction_packet, pre_instruction_step in Hpacket.
  rewrite pre_rename_instructions_other in Hpacket by exact Hfresh.
  rewrite pre_rename_instructions_fresh_other in Hpacket by exact Hfresh.
  assert (Hscope_source : pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) edge) scope).
  { rewrite Hsource; exact Hscope. }
  pose proof (pre_rename_instruction_laws EB EBE EN EE EV EU a family exits b edge scope acc
    Hlaw Hblocks Hpoints Hfamily Hb (Hinstructions edge (or_introl eq_refl))
    Hnone Hfreshflag Hpacket Hscope_source) as Hnext.
  rewrite Htarget in Hnext; cbn [fold_left].
  apply (IH m Hnodup ltac:(intros e He; apply Hinstructions; right; exact He) eq_refl).
  - intros e He; destruct (Hunwritten e (or_intror He)) as [Hget Hflag].
    unfold pre_instruction_step; rewrite pre_rename_instruction_other,
      pre_rename_instruction_fresh_other.
    + exact (conj Hget Hflag).
    + intro Heq; apply Hfresh; rewrite <- Heq; exact He.
    + intro Heq; apply Hfresh; rewrite <- Heq; exact He.
  - intros e He; exact (Htable e (or_intror He)).
  - exact Hnext.
Qed.

Local Lemma pre_rename_block_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments b first scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  pre_unwritten EE (instruction_edges (pre_ssa_points a) b) acc ->
  pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
    (instruction_edges (pre_ssa_points a) b)
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first scope ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (last (points_in_block (pre_ssa_points a) b) first)
    (fst (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hfirst Hunwritten Htable Hscope.
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  set (entered := pre_rename_exit EB EN EU exits first (scope, acc)).
  assert (Hentered : (match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end) = entered).
  { destruct (points_in_block (pre_ssa_points a) b) as [|head rest]; cbn in Hfirst;
      [discriminate|inversion Hfirst; reflexivity]. }
  assert (Hwritten : pre_unwritten EE (instruction_edges (pre_ssa_points a) b) (snd entered)).
  { intros e He; unfold entered; destruct (Hunwritten e He) as [Hget Hfresh].
    rewrite (proj2 (pre_rename_exit_scope EB EN EU exits first scope acc)),
      (pre_rename_exit_fresh EB EN EU exits first scope acc); exact (conj Hget Hfresh). }
  assert (Hscope_entered : pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first
    (fst entered)).
  { unfold entered; rewrite (proj1 (pre_rename_exit_scope EB EN EU exits first scope acc));
      exact Hscope. }
  assert (Hbodytable : pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
    (instruction_edges (pre_ssa_points a) b)
    (fold_left (pre_instruction_step EB EBE EN EE EV EU a family exits b)
      (instruction_edges (pre_ssa_points a) b) entered)).
  { intros e He; pose proof (Htable e He) as Hentry.
    unfold pre_rename_block in Hentry; rewrite Hentered in Hentry.
    unfold pre_instruction_step.
    destruct (fold_left (pre_rename_instruction EB EN EE EU a
      (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV EU a)
        b)
      (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
    unfold pre_instruction_packet in Hentry |- *; cbn [fst snd] in Hentry |- *.
    rewrite (pre_fold_projection _ pre_rename_occurrences _ output
      (pre_rename_argument_occurrences EB EBE EU a frames)),
      (pre_fold_projection _ pre_rename_fresh _ output
        (pre_rename_argument_fresh EB EBE EU a frames)) in Hentry.
    exact Hentry. }
  pose proof (pre_rename_instructions_laws EB EBE EN EE EV EU a family exits b
    (points_in_block (pre_ssa_points a) b) (instruction_edges (pre_ssa_points a) b) first first
    Hlaw Hblocks Hpoints Hfamily Hb (points_ordered Hssa b Hb)
    (pre_chain_edges_nodup _ _ _ (points_graph_wf Hssa) (points_ordered Hssa b Hb)
      (points_unique Hssa b)) ltac:(intros e He; exact He) Hfirst entered Hwritten Hbodytable
    Hscope_entered) as Hlast.
  unfold pre_rename_block; rewrite Hentered; unfold pre_instruction_step in Hlast.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a
    (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV EU a) b)
    (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
  exact Hlast.
Qed.

Local Definition pre_pending_laws {S O B BE N E V K C U} (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) f
    (tasks : list (B * pre_rename_scope B E U)) : Prop :=
  forall b scope, In (b, scope) tasks -> In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
    exists first, nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first /\
      pre_scope_laws EE EU a f first scope.

Local Definition pre_block_input_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments b scope acc : Prop :=
  In b (Graph.nodes (block_graph (pre_ssa_points a))) /\
  exists first, nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first /\
    pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first scope /\
    pre_unwritten EE (instruction_edges (pre_ssa_points a) b) acc /\
    pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
      (instruction_edges (pre_ssa_points a) b)
      (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
        (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc).

Local Definition pre_step_input_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments
    (work : pre_rename_work B BE E U) : Prop :=
  let '(tasks, seen, acc) := work in match tasks with
  | [] => True
  | (b, scope) :: _ => if FinSet.mem EB b seen then True
      else pre_block_input_laws EB EBE EN EE EV EU a family exits arguments b scope acc
  end.

(** The proof trace certifies the actual inputs at each executed block. *)
Inductive pre_checked_trace {X : Type} (step : X -> X) (good : X -> Prop) : X -> X -> Prop :=
  | pre_checked_done : forall x, pre_checked_trace step good x x
  | pre_checked_next : forall x final, good x -> pre_checked_trace step good (step x) final ->
      pre_checked_trace step good x final.

Local Lemma pre_checked_trace_forget {X} (step : X -> X) good x final :
  pre_checked_trace step good x final -> pre_walk_trace step x final.
Proof.
  intro Htrace; induction Htrace; [constructor|constructor; exact IHHtrace].
Qed.

Local Lemma pre_rename_child_parent {S O B BE N E V K C U} (EB : encoding B)
    (a : pre_expr_ssa S O B BE N E V K C U) b c :
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In c (index_edges EB (dom_children EB (Map.elements
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))))) b) ->
  Map.get EB c (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))) = Some b /\
    In c (Graph.nodes (block_graph (pre_ssa_points a))).
Proof.
  intros Hready Hin; apply dom_children_in in Hin.
  apply (Map.elements_sound EB c b _ (chk_idom_wf EB _ _ Hready)) in Hin; split; [exact Hin|].
  destruct (simple_lt_idom_exact EB _ _ Hready) as [Hmap [[Hdomain Hforest] Hexact]].
  exact (reachable_in_nodes _ c (proj1 Hready) (proj1 (Hdomain c b Hin))).
Qed.

Local Lemma pre_rename_children_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b default scope :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (last (points_in_block (pre_ssa_points a) b) default) scope ->
  pre_pending_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (map (fun c => (c, scope)) (index_edges EB (dom_children EB (Map.elements
      (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))))) b)).
Proof.
  intros Hlaw Hblocks Hpoints Hb Hscope c frames Hin; apply in_map_iff in Hin.
  destruct Hin as [child [Heq Hchild]]; inversion Heq; subst child frames.
  destruct (pre_rename_child_parent EB a b c Hblocks Hchild) as [Hparent Hc].
  split; [exact Hc|]; pose proof (pre_expr_points EV a Hlaw) as Hssa.
  destruct (points_in_block (pre_ssa_points a) c) as [|first rest] eqn:Hlist.
  { exfalso; apply (blocks_nonempty Hssa c Hc); exact Hlist. }
  exists first; split; [reflexivity|].
  apply (pre_scope_parent_laws EB EN EE EV EU a _ b c first scope Hlaw Hblocks Hpoints
    (pre_build_definition_edges EB EBE EN EE EV EU a Hlaw Hblocks)
    (build_frg_occurrence_provenance EB EBE EN EE EV EU a Hlaw Hblocks) Hb Hc Hparent
    ltac:(rewrite Hlist; reflexivity)).
  rewrite (pre_last_default (points_in_block (pre_ssa_points a) b) first default
    (blocks_nonempty Hssa b Hb)); exact Hscope.
Qed.

Local Definition pre_walk_step {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments :=
  pre_rename_step EB EBE EN EE EU a (dom_children EB (Map.elements
    (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a)))))))
    (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV EU a)
      arguments.

Local Lemma pre_rename_step_inputs {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments work final :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  pre_work_sound EE EU a work -> pre_work_completed EB EE a work ->
  pre_work_fresh_completed EB EE a work ->
  pre_pending_laws EE EU a (build_frg EB EBE EN EE EV EU a) (fst (fst work)) ->
  pre_walk_trace (pre_walk_step EB EBE EN EE EV EU a family exits arguments)
    (pre_walk_step EB EBE EN EE EV EU a family exits arguments work) final ->
  (forall e, Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) =
      Map.get EE e (pre_rename_occurrences (snd final)) /\
    FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) =
      FinSet.mem EE e (pre_rename_fresh (snd final))) ->
  pre_step_input_laws EB EBE EN EE EV EU a family exits arguments work /\
  pre_pending_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (fst (fst (pre_walk_step EB EBE EN EE EV EU a family exits arguments work))).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hsound Hcompleted Hfresh Hpending Hfuture Horacle.
  pose proof (pre_rename_step_sound EB EBE EN EE EV EU a
    (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV EU a)
    arguments work Hlaw Hblocks Hsound) as Hnextsound.
  destruct work as [[[|[b scope] rest] seen] acc].
  - split; [exact I|exact Hpending].
  - cbn [pre_step_input_laws pre_walk_step pre_rename_step fst snd].
    destruct (FinSet.mem EB b seen) eqn:Hseen.
    + split; [exact I|].
      intros c frames Hin; apply Hpending; right; exact Hin.
    + destruct (Hpending b scope (or_introl eq_refl)) as [Hb [first [Hfirst Hscope]]].
      pose proof (pre_expr_points EV a Hlaw) as Hssa.
      pose proof (pre_block_unwritten EB EE a b seen acc Hssa Hb Hseen Hcompleted Hfresh)
        as Hunwritten.
      destruct (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
        (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc)
        as [frames output] eqn:Hblock.
      assert (Hstep : pre_walk_step EB EBE EN EE EV EU a family exits arguments
        ((b, scope) :: rest, seen, acc) =
        (map (fun c => (c, frames)) (index_edges EB (dom_children EB (Map.elements
          (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))))) b) ++ rest,
         FinSet.add EB b seen, output)).
      { unfold pre_walk_step, pre_rename_step; cbn [fst snd]; rewrite Hseen, Hblock; reflexivity. }
      change (pre_work_sound EE EU a (pre_walk_step EB EBE EN EE EV EU a family exits arguments
        ((b, scope) :: rest, seen, acc))) in Hnextsound.
      rewrite Hstep in Hfuture, Hnextsound.
      assert (Htable : pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
        (instruction_edges (pre_ssa_points a) b)
        (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
          (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc)).
      { intros e He; pose proof (pre_instruction_owner _ b e Hssa Hb He) as Howner.
        assert (Hseenkey : FinSet.mem EB
          (block_of_point (pre_ssa_points a)
            (Graph.source (live_graph (point_model (pre_ssa_points a))) e))
          (FinSet.add EB b seen) = true).
        { rewrite Howner; apply FinSet.mem_add; left; reflexivity. }
        pose proof (pre_rename_trace_protected EB EBE EN EE EV EU a
          (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV
            EU a)
          arguments _ final e Hlaw Hblocks Hnextsound Hfuture Hseenkey) as [Hquery Hflag].
        destruct (Horacle e) as [Hget Hfreshflag].
        unfold pre_instruction_packet; rewrite Hblock; cbn [snd] in Hquery, Hflag |- *.
        split; [exact (eq_trans Hget Hquery)|exact (eq_trans Hfreshflag Hflag)]. }
      pose proof (pre_rename_block_laws EB EBE EN EE EV EU a family exits arguments b first scope
        acc
        Hlaw Hblocks Hpoints Hfamily Hb Hfirst Hunwritten Htable Hscope) as Hlast.
      rewrite Hblock in Hlast; cbn [fst] in Hlast.
      pose proof (pre_rename_children_laws EB EBE EN EE EV EU a b first frames
        Hlaw Hblocks Hpoints Hb Hlast) as Hchildren.
      split.
      * split; [exact Hb|]; exists first; split; [exact Hfirst|]; split; [exact Hscope|].
        split; [exact Hunwritten|exact Htable].
      * intros c values Hin; apply in_app_iff in Hin; destruct Hin as [Hchild|Hrest].
        -- exact (Hchildren c values Hchild).
        -- apply Hpending; right; exact Hrest.
Qed.

Local Lemma pre_rename_certify_trace {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments work final :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  pre_walk_trace (pre_walk_step EB EBE EN EE EV EU a family exits arguments) work final ->
  pre_work_sound EE EU a work -> pre_work_completed EB EE a work ->
  pre_work_fresh_completed EB EE a work ->
  pre_pending_laws EE EU a (build_frg EB EBE EN EE EV EU a) (fst (fst work)) ->
  (forall e, Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) =
      Map.get EE e (pre_rename_occurrences (snd final)) /\
    FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) =
      FinSet.mem EE e (pre_rename_fresh (snd final))) ->
  pre_checked_trace (pre_walk_step EB EBE EN EE EV EU a family exits arguments)
    (pre_step_input_laws EB EBE EN EE EV EU a family exits arguments) work final.
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Htrace; induction Htrace as [work|work final Hfuture IH];
    intros Hsound Hcompleted Hfresh Hpending Horacle; [constructor|].
  destruct (pre_rename_step_inputs EB EBE EN EE EV EU a family exits arguments work final
    Hlaw Hblocks Hpoints Hfamily Hsound Hcompleted Hfresh Hpending Hfuture Horacle)
    as [Hinput Hnextpending].
  constructor; [exact Hinput|]; apply IH.
  - exact (pre_rename_step_sound EB EBE EN EE EV EU a _ _ _ _ work Hlaw Hblocks Hsound).
  - exact (proj1 (pre_rename_step_completed EB EBE EN EE EV EU a _ _ _ _ _ work
      Hlaw Hsound Hcompleted)).
  - exact (pre_rename_step_fresh_completed EB EBE EN EE EV EU a _ _ _ _ _ work
      Hlaw Hsound Hfresh).
  - exact Hnextpending.
  - exact Horacle.
Qed.

(** Proof abbreviations expose the producer's final walk without adding executable passes. *)
Local Definition pre_built_family {S O B BE N E V K C U} (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :=
  filter (pre_total_pure (pre_expression a)) (pre_expr_universe EBE EV EU a).

Local Definition pre_built_exits {S O B BE N E V K C U} (EBE : encoding BE)
    (EN : encoding N) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :=
  pre_rename_exit_index EN a (pre_built_family EBE EV EU a).

Local Definition pre_built_arguments {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :=
  pre_rename_argument_index EB EBE EU a (prepare EB (block_graph (pre_ssa_points a)))
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)).

Local Definition pre_built_initial {S O B BE N E V K C U} (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
    pre_rename_work B BE E U :=
  (map (fun b => (b, pre_initial_scope EU a (pre_built_family EBE EV EU a)))
    (Graph.entries (block_graph (pre_ssa_points a))), FinSet.empty,
    PreRenameAcc Map.empty FinSet.empty Map.empty FinSet.empty).

Local Definition pre_built_final {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :=
  pre_rename_run (pre_walk_step EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
    (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a))
    (Pos.of_succ_nat (length (Graph.entries (block_graph (pre_ssa_points a))) +
      length (Map.elements (idom (dominator_tree (prepare EB (block_graph (pre_ssa_points a))))))))
    (pre_built_initial EBE EV EU a).

Local Lemma pre_built_family_exact {S O B BE N E V K C U} (EBE : encoding BE)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a -> forall u, In u (pre_built_family EBE EV EU a) <->
    pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true.
Proof.
  intros Hlaw u; unfold pre_built_family; rewrite filter_In,
    (proj2 (pre_expr_universe_exact EBE EV EU a Hlaw) u); reflexivity.
Qed.

Local Lemma pre_built_data {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e :
  Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) =
    Map.get EE e (pre_rename_occurrences (snd (pre_built_final EB EBE EN EE EV EU a))) /\
  FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) =
    FinSet.mem EE e (pre_rename_fresh (snd (pre_built_final EB EBE EN EE EV EU a))).
Proof.
  split; reflexivity.
Qed.

Local Lemma pre_built_trace {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_walk_trace (pre_walk_step EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
    (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a))
    (pre_built_initial EBE EV EU a) (pre_built_final EB EBE EN EE EV EU a).
Proof.
  unfold pre_built_final; rewrite pre_rename_run_agrees by reflexivity; apply pre_walk_trace_iter.
Qed.

Local Lemma pre_built_initial_pending {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_pending_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (fst (fst (pre_built_initial EBE EV EU a))).
Proof.
  intros Hlaw Hready b scope Hin; apply in_map_iff in Hin.
  destruct Hin as [entry [Heq Hentry]]; inversion Heq; subst entry scope.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  pose proof (entries_in (blocks_graph_wf Hpoints) b Hentry) as Hb; split; [exact Hb|].
  destruct (pre_expr_entry_position EV a Hlaw) as [entry [first [Hblocks [Hpoint Hfirst]]]].
  rewrite Hblocks in Hentry; destruct Hentry as [Hsame|Hfalse]; [subst b|contradiction].
  exists first; split; [exact Hfirst|].
  exact (pre_build_initial_scope_laws EB EBE EN EE EV EU a entry first
    Hlaw Hready Hb Hfirst Hpoint).
Qed.

Local Lemma pre_built_checked_trace {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_checked_trace (pre_walk_step EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
    (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a))
    (pre_step_input_laws EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
      (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a))
    (pre_built_initial EBE EV EU a) (pre_built_final EB EBE EN EE EV EU a).
Proof.
  intros Hlaw Hblocks Hpoints; apply (pre_rename_certify_trace EB EBE EN EE EV EU a
    (pre_built_family EBE EV EU a) (pre_built_exits EBE EN EV EU a)
    (pre_built_arguments EB EBE EN EE EV EU a) _ _ Hlaw Hblocks Hpoints
    (pre_built_family_exact EBE EV EU a Hlaw) (pre_built_trace EB EBE EN EE EV EU a)).
  - exact (pre_initial_work_sound EE EV EU a _ Hlaw).
  - intros e d Hget; cbn [pre_built_initial fst snd pre_rename_occurrences] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros e Hget; cbn [pre_built_initial fst snd pre_rename_fresh] in Hget.
    rewrite FinSet.mem_empty in Hget; discriminate.
  - exact (pre_built_initial_pending EB EBE EN EE EV EU a Hlaw Hblocks).
  - apply pre_built_data.
Qed.

Local Lemma pre_built_seen_all {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall b, In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
    FinSet.mem EB b (snd (fst (pre_built_final EB EBE EN EE EV EU a))) = true.
Proof.
  intros Hlaw Hready; apply (pre_rename_seen_all EB EBE EN EE EV EU a _ _ _ _ _ _ Hlaw Hready).
Qed.

Local Lemma pre_reusable_not_current {S O B BE N E V K C U} (EN : encoding N)
    (EV : encoding V) (a : pre_expr_ssa S O B BE N E V K C U) f u e d :
  pre_expr_ssa_laws EV a ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  block_edge_of (pre_ssa_points a) e = None ->
  frg_reusable a f u (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d ->
  forall v, d <> FrFresh e v.
Proof.
  intros Hlaw Hready He Hi Hreuse v Heq; subst d.
  destruct Hreuse as [[Hd [Hexpr [q [Hpoint [Hdom Hnearest]]]]] Hsafe].
  inversion Hpoint; subst q.
  pose proof (pre_internal_immediate EV a e Hlaw He Hi) as [[Hforward Hne] Hminimal].
  pose proof (pre_expr_points EV a Hlaw) as Hpoints; apply Hne.
  apply (idf_dominance_antisym EN _ _ Hready).
  - exact (pre_expr_reachable_points EV a Hlaw _
      (proj1 (pre_listed_edge_out _ e (points_graph_wf Hpoints) He))).
  - exact (pre_target_reachable EV a e Hlaw He).
  - exact Hforward.
  - exact Hdom.
Qed.

Local Definition pre_occurrence_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e u : Prop :=
  let f := build_frg EB EBE EN EE EV EU a in
  (exists d, Map.get EE e (frg_occurrence_index f) = Some d /\ In d (frg_versions f) /\
    frg_version_expr d = u /\ (d = FrFresh e u \/
      frg_reusable a f u (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d)) /\
  (FinSet.mem EE e (frg_fresh_index f) = true <->
    Map.get EE e (frg_occurrence_index f) = Some (FrFresh e u)) /\
  (FinSet.mem EE e (frg_fresh_index f) = true <->
    ~ exists d, frg_reusable a f u
      (Graph.source (live_graph (point_model (pre_ssa_points a))) e) d).

Local Lemma pre_occurrence_from_frame {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b e u scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  FinSet.mem EE e (pre_rename_fresh acc) = false ->
  pre_instruction_packet EE a (build_frg EB EBE EN EE EV EU a) e
    (pre_rename_instruction EB EN EE EU a alterations exits phis b (scope, acc) e) ->
  pre_frame_laws EE a (build_frg EB EBE EN EE EV EU a) u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) (pre_rename_top EU scope u) ->
  pre_occurrence_laws EB EBE EN EE EV EU a e u.
Proof.
  intros Hlaw Hblocks Hpoints He Hcomputed Hpure Hfresh Hpacket Hframe.
  assert (Hu : pre_expr_in_family a u).
  { apply pre_family_seed; exact (pre_expr_occurrences EV a Hlaw e u Hcomputed). }
  assert (Hobserved : pre_observed_point a
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e)).
  { left; exists e, u; repeat split; assumption. }
  assert (Hphis : forall block, frg_phi_needed EB EU a u block ->
    In (FrPhi block u) (frg_versions (build_frg EB EBE EN EE EV EU a))).
  { intros block Hneeded; apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw).
    apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hblocks); auto. }
  destruct (pre_frame_availability EB EN EE EV EU a (build_frg EB EBE EN EE EV EU a) u
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) (pre_rename_top EU scope u)
    Hlaw Hblocks Hpoints Hu Hobserved Hphis Hframe) as [Hiff Husable].
  pose proof (pre_instruction_packet_real EB EN EE EU a _ alterations exits phis b e u _ scope acc
    Hcomputed Hpure (pre_frame_laws_sound EE a _ u _ _ Hframe) Hfresh Hpacket) as Hdata.
  unfold pre_occurrence_laws.
  destruct (pre_rename_top EU scope u) as [operand available] eqn:Htop.
  cbn [fst snd] in Hiff, Husable, Hdata; destruct available; cbn [fst snd] in Hiff, Husable, Hdata;
    destruct Hdata as [Hget Hflag].
  - pose proof (Husable eq_refl) as Hreuse; split.
    + exists (frg_operand_version operand); split; [exact Hget|].
      split; [exact (proj1 (proj1 Hreuse))|].
      split; [exact (proj1 (proj2 (proj1 Hreuse)))|right; exact Hreuse].
    + split.
      * rewrite Hflag; split; [discriminate|intro Hcurrent].
        rewrite Hget in Hcurrent; injection Hcurrent as Heq; exfalso.
        exact (pre_reusable_not_current EN EV a _ u e _ Hlaw Hpoints He
          (proj1 (pre_expr_real_internal EV a Hlaw e u Hcomputed)) Hreuse u Heq).
      * rewrite Hflag; split; [discriminate|intro Hnone; exfalso; apply Hnone].
        exists (frg_operand_version operand); exact Hreuse.
  - split.
    + exists (FrFresh e u); split; [exact Hget|]; split.
      * exact (pre_build_fresh_present EB EBE EN EE EV EU a e u Hlaw He Hcomputed Hflag).
      * split; [reflexivity|left; reflexivity].
    + split.
      * split; [intro Htrue; exact Hget|intro Hcurrent; exact Hflag].
      * split.
        -- intros Htrue Hexists; pose proof (proj2 Hiff Hexists) as Hfalse; discriminate.
        -- intro Hnone; exact Hflag.
Qed.

Inductive pre_checked_fold {X A : Type} (step : X -> A -> X) (good : A -> X -> Prop) :
    list A -> X -> Prop :=
  | pre_fold_checked_done : forall x, pre_checked_fold step good [] x
  | pre_fold_checked_next : forall a xs x, good a x ->
      pre_checked_fold step good xs (step x a) -> pre_checked_fold step good (a :: xs) x.

Local Lemma pre_checked_fold_member {X A} (step : X -> A -> X) good xs x a :
  pre_checked_fold step good xs x -> In a xs -> exists state, good a state.
Proof.
  intros Hchecked; induction Hchecked as [x|head xs x Hgood Hchecked IH]; intro Hin;
    [contradiction|].
  destruct Hin as [Heq|Hin]; [subst head; exists x; exact Hgood|exact (IH Hin)].
Qed.

Local Definition pre_instruction_input_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) : Prop :=
  In e (instruction_edges (pre_ssa_points a) b) /\
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) (fst work) /\
  Map.get EE e (pre_rename_occurrences (snd work)) = None /\
  FinSet.mem EE e (pre_rename_fresh (snd work)) = false /\
  pre_instruction_packet EE a (build_frg EB EBE EN EE EV EU a) e
    (pre_instruction_step EB EBE EN EE EV EU a family exits b work e).

Local Lemma pre_rename_instructions_checked {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits b ns es first :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  point_chain (live_graph (point_model (pre_ssa_points a))) ns es -> NoDup es ->
  (forall e, In e es -> In e (instruction_edges (pre_ssa_points a) b)) ->
  nth_error ns 0 = Some first -> forall work,
  pre_unwritten EE es (snd work) ->
  pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a) es
    (fold_left (pre_instruction_step EB EBE EN EE EV EU a family exits b) es work) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) first (fst work) ->
  pre_checked_fold (pre_instruction_step EB EBE EN EE EV EU a family exits b)
    (pre_instruction_input_laws EB EBE EN EE EV EU a family exits b) es work.
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hb Hchain; revert first.
  induction Hchain as [n|n m ns edge es Hedge Htarget Hchain IH];
    intros first Hnodup Hinstructions Hfirst [scope acc] Hunwritten Htable Hscope;
    cbn in Hfirst; inversion Hfirst; subst first; [constructor|].
  apply NoDup_cons_iff in Hnodup; destruct Hnodup as [Hfresh Hnodup].
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (out_source (points_graph_wf Hssa) n edge Hedge) as Hsource.
  destruct (Hunwritten edge (or_introl eq_refl)) as [Hnone Hfreshflag].
  pose proof (Htable edge (or_introl eq_refl)) as Hpacket; cbn [fold_left] in Hpacket.
  unfold pre_instruction_packet, pre_instruction_step in Hpacket.
  rewrite pre_rename_instructions_other in Hpacket by exact Hfresh.
  rewrite pre_rename_instructions_fresh_other in Hpacket by exact Hfresh.
  assert (Hscope_source : pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) edge) scope).
  { rewrite Hsource; exact Hscope. }
  constructor.
  - split; [apply Hinstructions; left; reflexivity|].
    split; [exact Hscope_source|]; split; [exact Hnone|]; split; [exact Hfreshflag|exact Hpacket].
  - pose proof (pre_rename_instruction_laws EB EBE EN EE EV EU a family exits b edge scope acc
      Hlaw Hblocks Hpoints Hfamily Hb (Hinstructions edge (or_introl eq_refl))
      Hnone Hfreshflag Hpacket Hscope_source) as Hnext.
    rewrite Htarget in Hnext.
    apply (IH m Hnodup ltac:(intros e He; apply Hinstructions; right; exact He) eq_refl).
    + intros e He; destruct (Hunwritten e (or_intror He)) as [Hget Hflag].
      unfold pre_instruction_step; rewrite pre_rename_instruction_other,
        pre_rename_instruction_fresh_other.
      * exact (conj Hget Hflag).
      * intro Heq; apply Hfresh; rewrite <- Heq; exact He.
      * intro Heq; apply Hfresh; rewrite <- Heq; exact He.
    + intros e He; exact (Htable e (or_intror He)).
    + exact Hnext.
Qed.

Local Lemma pre_block_body_table {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments b first scope acc :
  nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first ->
  pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
    (instruction_edges (pre_ssa_points a) b)
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc) ->
  pre_instruction_table EE a (build_frg EB EBE EN EE EV EU a)
    (instruction_edges (pre_ssa_points a) b)
    (fold_left (pre_instruction_step EB EBE EN EE EV EU a family exits b)
      (instruction_edges (pre_ssa_points a) b) (pre_rename_exit EB EN EU exits first (scope, acc))).
Proof.
  intros Hfirst Htable e He; pose proof (Htable e He) as Hentry.
  assert (Hentered : (match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end) = pre_rename_exit EB EN EU exits first (scope, acc)).
  { destruct (points_in_block (pre_ssa_points a) b) as [|head rest]; cbn in Hfirst;
      [discriminate|inversion Hfirst; reflexivity]. }
  unfold pre_rename_block in Hentry; rewrite Hentered in Hentry; unfold pre_instruction_step.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a
    (pre_rename_alter_index EE EV EU a family) exits (pre_build_phi_blocks EB EBE EN EE EV EU a) b)
    (instruction_edges (pre_ssa_points a) b) (pre_rename_exit EB EN EU exits first (scope, acc)))
    as [frames output].
  unfold pre_instruction_packet in Hentry |- *; cbn [fst snd] in Hentry |- *.
  rewrite (pre_fold_projection _ pre_rename_occurrences _ output
    (pre_rename_argument_occurrences EB EBE EU a frames)),
    (pre_fold_projection _ pre_rename_fresh _ output
      (pre_rename_argument_fresh EB EBE EU a frames)) in Hentry; exact Hentry.
Qed.

Local Lemma pre_block_checked_fold {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments b scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  pre_block_input_laws EB EBE EN EE EV EU a family exits arguments b scope acc ->
  exists first, nth_error (points_in_block (pre_ssa_points a) b) 0 = Some first /\
    pre_checked_fold (pre_instruction_step EB EBE EN EE EV EU a family exits b)
      (pre_instruction_input_laws EB EBE EN EE EV EU a family exits b)
      (instruction_edges (pre_ssa_points a) b) (pre_rename_exit EB EN EU exits first (scope, acc)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily [Hb [first [Hfirst [Hscope [Hwritten Htable]]]]].
  exists first; split; [exact Hfirst|]; pose proof (pre_expr_points EV a Hlaw) as Hssa.
  apply (pre_rename_instructions_checked EB EBE EN EE EV EU a family exits b
    (points_in_block (pre_ssa_points a) b) (instruction_edges (pre_ssa_points a) b) first
    Hlaw Hblocks Hpoints Hfamily Hb (points_ordered Hssa b Hb)
    (pre_chain_edges_nodup _ _ _ (points_graph_wf Hssa) (points_ordered Hssa b Hb)
      (points_unique Hssa b)) ltac:(intros e He; exact He) Hfirst).
  - intros e He; destruct (Hwritten e He) as [Hget Hfresh].
    rewrite (proj2 (pre_rename_exit_scope EB EN EU exits first scope acc)),
      (pre_rename_exit_fresh EB EN EU exits first scope acc); exact (conj Hget Hfresh).
  - exact (pre_block_body_table EB EBE EN EE EV EU a family exits arguments b first scope acc
      Hfirst Htable).
  - rewrite (proj1 (pre_rename_exit_scope EB EN EU exits first scope acc)); exact Hscope.
Qed.

Local Lemma pre_checked_block_visited {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments work final b :
  pre_checked_trace (pre_walk_step EB EBE EN EE EV EU a family exits arguments)
    (pre_step_input_laws EB EBE EN EE EV EU a family exits arguments) work final ->
  FinSet.mem EB b (snd (fst work)) = false -> FinSet.mem EB b (snd (fst final)) = true ->
  exists scope acc, pre_block_input_laws EB EBE EN EE EV EU a family exits arguments b scope acc.
Proof.
  intro Hchecked; induction Hchecked as [work|work final Hinput Hchecked IH];
    intros Hnew Hfinal; [congruence|].
  destruct work as [[[|[block scope] rest] seen] acc].
  - apply IH; assumption.
  - cbn [fst snd] in Hnew; destruct (FinSet.mem EB block seen) eqn:Hseen.
    + apply IH; [|exact Hfinal].
      unfold pre_walk_step, pre_rename_step; cbn [fst snd]; rewrite Hseen; exact Hnew.
    + destruct (dfs_eq_dec EB b block) as [Heq|Hne].
      * subst block; exists scope, acc; unfold pre_step_input_laws in Hinput;
          cbn [fst snd] in Hinput; rewrite Hseen in Hinput; exact Hinput.
      * apply IH; [|exact Hfinal].
        unfold pre_walk_step, pre_rename_step; cbn [fst snd]; rewrite Hseen.
        destruct (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family)
          exits
          (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments block scope acc).
        cbn [fst snd]; rewrite dfs_mem_add; destruct (dfs_eq_dec EB b block);
          [congruence|exact Hnew].
Qed.

Local Lemma pre_built_block_inputs {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  exists scope acc, pre_block_input_laws EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
    (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a) b scope acc.
Proof.
  intros Hlaw Hblocks Hpoints Hb; apply (pre_checked_block_visited EB EBE EN EE EV EU a _ _ _ _ _ b
    (pre_built_checked_trace EB EBE EN EE EV EU a Hlaw Hblocks Hpoints)).
  - cbn [pre_built_initial fst snd]; rewrite FinSet.mem_empty; reflexivity.
  - exact (pre_built_seen_all EB EBE EN EE EV EU a Hlaw Hblocks b Hb).
Qed.

Local Lemma pre_built_occurrence_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall e u, In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_recomputed (pre_expression a) e = Some u -> pre_total_pure (pre_expression a) u = true ->
  pre_occurrence_laws EB EBE EN EE EV EU a e u.
Proof.
  intros Hlaw Hblocks Hpoints e u He Hcomputed Hpure.
  destruct (pre_internal_edge_block _ e (pre_expr_points EV a Hlaw) He
    (proj1 (pre_expr_real_internal EV a Hlaw e u Hcomputed))) as [b [Hb [Hin Htarget]]].
  destruct (pre_built_block_inputs EB EBE EN EE EV EU a b Hlaw Hblocks Hpoints Hb)
    as [scope [acc Hinput]].
  destruct (pre_block_checked_fold EB EBE EN EE EV EU a (pre_built_family EBE EV EU a)
    (pre_built_exits EBE EN EV EU a) (pre_built_arguments EB EBE EN EE EV EU a) b scope acc
    Hlaw Hblocks Hpoints (pre_built_family_exact EBE EV EU a Hlaw) Hinput)
    as [first [Hfirst Hchecked]].
  destruct (pre_checked_fold_member _ _ _ _ e Hchecked Hin) as [[frames output] Hgood].
  destruct Hgood as [Hlisted [Hscope [Hnone [Hfresh Hpacket]]]].
  assert (Hu : pre_expr_in_family a u).
  { apply pre_family_seed; exact (pre_expr_occurrences EV a Hlaw e u Hcomputed). }
  exact (pre_occurrence_from_frame EB EBE EN EE EV EU a
    (pre_rename_alter_index EE EV EU a (pre_built_family EBE EV EU a)) (pre_built_exits EBE EN EV
      EU a)
    (pre_build_phi_blocks EB EBE EN EE EV EU a) b e u frames output Hlaw Hblocks Hpoints
    He Hcomputed Hpure Hfresh Hpacket (Hscope u Hu Hpure)).
Qed.

Local Lemma pre_fold_invariant_in {A X} (step : A -> X -> A) (P : A -> Prop) xs initial :
  (forall acc x, In x xs -> P acc -> P (step acc x)) -> P initial -> P (fold_left step xs initial).
Proof.
  revert initial; induction xs as [|x xs IH]; intros initial Hstep Hinitial; [exact Hinitial|].
  cbn [fold_left]; apply IH.
  - intros acc y Hy Hacc; apply Hstep; [right; exact Hy|exact Hacc].
  - apply Hstep; [left; reflexivity|exact Hinitial].
Qed.

Local Definition pre_fresh_entry_sound {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) e : Prop :=
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) /\
  exists u, pre_recomputed (pre_expression a) e = Some u /\ pre_total_pure (pre_expression a) u =
    true.

Local Definition pre_fresh_index_sound {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) (fresh : FinSet.t E) : Prop :=
  forall e, FinSet.mem EE e fresh = true -> pre_fresh_entry_sound a e.

Local Lemma pre_rename_occurrence_fresh_sound {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e scope
    (acc : pre_rename_acc B BE E U) :
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_fresh_index_sound EE a (pre_rename_fresh acc) ->
  pre_fresh_index_sound EE a (pre_rename_fresh
    (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc))))).
Proof.
  intros He Hsound; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|] eqn:Hcomputed; [|exact Hsound].
  destruct (pre_total_pure (pre_expression a) u) eqn:Hpure; [|exact Hsound].
  destruct (pre_rename_top EU scope u) as [[d real] available]; cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true); cbn [fst snd pre_rename_fresh]; [|exact Hsound].
  intros key Hkey; apply FinSet.mem_add in Hkey; destruct Hkey as [Heq|Hkey].
  - subst key; split; [exact He|exists u; auto].
  - exact (Hsound key Hkey).
Qed.

Local Lemma pre_rename_instruction_fresh_sound {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e :
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_fresh_index_sound EE a (pre_rename_fresh (snd work)) ->
  pre_fresh_index_sound EE a (pre_rename_fresh (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis b work e))).
Proof.
  intros He Hsound; rewrite pre_rename_instruction_fresh; destruct work as [scope acc].
  exact (pre_rename_occurrence_fresh_sound EB EE EU a e scope acc He Hsound).
Qed.

Local Lemma pre_rename_block_fresh_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc :
  ssa_point_laws (pre_ssa_points a) -> In b (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_fresh_index_sound EE a (pre_rename_fresh acc) ->
  pre_fresh_index_sound EE a (pre_rename_fresh (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intros Hpoints Hb Hsound; unfold pre_rename_block.
  set (entered := match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end).
  assert (Hentered : pre_fresh_index_sound EE a (pre_rename_fresh (snd entered))).
  { unfold entered; destruct (points_in_block (pre_ssa_points a) b); [exact Hsound|].
    rewrite (pre_rename_exit_fresh EB EN EU exits n scope acc); exact Hsound. }
  assert (Hbody : pre_fresh_index_sound EE a (pre_rename_fresh (snd (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered)))).
  { apply (pre_fold_invariant_in _ (fun state => pre_fresh_index_sound EE a
      (pre_rename_fresh (snd state))) _ entered); [|exact Hentered].
    intros state e He Hstate; apply pre_rename_instruction_fresh_sound; [|exact Hstate].
    exact (pre_instruction_edge_listed _ b e Hpoints Hb He). }
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered) as [frames output].
  cbn [snd] in Hbody |- *; rewrite (pre_fold_projection _ pre_rename_fresh _ output
    (pre_rename_argument_fresh EB EBE EU a frames)); exact Hbody.
Qed.

Local Lemma pre_rename_step_fresh_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_expr_ssa_laws EV a -> pre_work_sound EE EU a work ->
  pre_fresh_index_sound EE a (pre_rename_fresh (snd work)) ->
  pre_fresh_index_sound EE a (pre_rename_fresh (snd
    (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work))).
Proof.
  intros Hlaw; destruct work as [[[|[b scope] rest] seen] acc];
    intros [Hpending Hindex] Hfresh; [exact Hfresh|].
  unfold pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen); [exact Hfresh|].
  destruct (Hpending b scope (or_introl eq_refl)) as [Hb Hframes].
  pose proof (pre_rename_block_fresh_sound EB EBE EN EE EU a alterations exits phis arguments
    b scope acc (pre_expr_points EV a Hlaw) Hb Hfresh) as Hblock.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc)
    as [frames output]; exact Hblock.
Qed.

Local Lemma pre_built_fresh_sound {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_fresh_index_sound EE a (frg_fresh_index (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw Hready.
  assert (Hfinal : pre_work_sound EE EU a (pre_built_final EB EBE EN EE EV EU a) /\
    pre_fresh_index_sound EE a (pre_rename_fresh (snd (pre_built_final EB EBE EN EE EV EU a)))).
  { refine (pre_walk_trace_invariant _ (fun work => pre_work_sound EE EU a work /\
      pre_fresh_index_sound EE a (pre_rename_fresh (snd work))) _ _
      (pre_built_trace EB EBE EN EE EV EU a) _ _).
    - intros work [Hsound Hfresh]; split.
      + exact (pre_rename_step_sound EB EBE EN EE EV EU a _ _ _ _ work Hlaw Hready Hsound).
      + exact (pre_rename_step_fresh_sound EB EBE EN EE EV EU a _ _ _ _ _ work Hlaw Hsound Hfresh).
    - split; [exact (pre_initial_work_sound EE EV EU a _ Hlaw)|].
      intros e Hfalse; cbn [pre_built_initial fst snd pre_rename_fresh] in Hfalse.
      rewrite FinSet.mem_empty in Hfalse; discriminate. }
  intros e Hfresh; rewrite (proj2 (pre_built_data EB EBE EN EE EV EU a e)) in Hfresh.
  exact (proj2 Hfinal e Hfresh).
Qed.

Local Lemma pre_built_fresh_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall e u, pre_recomputed (pre_expression a) e = Some u ->
  (FinSet.mem EE e (frg_fresh_index (build_frg EB EBE EN EE EV EU a)) = true <->
    Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) = Some (FrFresh e u)).
Proof.
  intros Hlaw Hblocks Hpoints e u Hcomputed.
  destruct (in_dec (dfs_eq_dec EE) e (edges_of (live_graph (point_model (pre_ssa_points a)))))
    as [He|Houtside].
  - destruct (pre_total_pure (pre_expression a) u) eqn:Hpure.
    + exact (proj1 (proj2 (pre_built_occurrence_laws EB EBE EN EE EV EU a
        Hlaw Hblocks Hpoints e u He Hcomputed Hpure))).
    + split.
      * intro Hfresh; destruct (pre_built_fresh_sound EB EBE EN EE EV EU a Hlaw Hblocks e Hfresh)
          as [Hlisted [v [Hvalue Htotal]]]; assert (Heq : v = u) by congruence; subst v; congruence.
      * intro Hget; destruct (build_frg_occurrence_provenance EB EBE EN EE EV EU a
          Hlaw Hblocks e (FrFresh e u) Hget) as [Hlisted [Hvalue [Htotal Hpoint]]]; congruence.
  - split.
    + intro Hfresh; exfalso; apply Houtside.
      exact (proj1 (pre_built_fresh_sound EB EBE EN EE EV EU a Hlaw Hblocks e Hfresh)).
    + intro Hget; exfalso; apply Houtside.
      exact (proj1 (build_frg_occurrence_provenance EB EBE EN EE EV EU a
        Hlaw Hblocks e (FrFresh e u) Hget)).
Qed.

(** * Incoming-edge operands *)

Local Lemma pre_cross_source_last {B BE N E V} (s : ssa_points B BE N E V) be pe default :
  ssa_point_laws s -> In pe (edges_of (live_graph (point_model s))) ->
  block_edge_of s pe = Some be ->
  Graph.source (live_graph (point_model s)) pe =
    last (points_in_block s (Graph.source (block_graph s) be)) default.
Proof.
  intros Hpoints Hpe Hcross; apply in_flat_map in Hpe; destruct Hpe as [n [Hn Hout]].
  pose proof (point_edge_projection Hpoints n pe Hn Hout) as Hprojection.
  rewrite Hcross in Hprojection; destruct Hprojection as [Hbe [Htarget [Hlast Hfirst]]].
  rewrite (out_source (points_graph_wf Hpoints) n pe Hout),
    (out_source (blocks_graph_wf Hpoints) (block_of_point s n) be Hbe).
  pose proof (proj1 (pre_point_owner_listed s n Hpoints Hn)) as Hb.
  rewrite <- (pre_last_default (points_in_block s (block_of_point s n)) n default
    (blocks_nonempty Hpoints _ Hb)); symmetry; exact Hlast.
Qed.

Local Lemma pre_incoming_point_exists {B BE N E V} (EBE : encoding BE)
    (s : ssa_points B BE N E V) be :
  ssa_point_laws s -> In be (edges_of (block_graph s)) ->
  exists pe, Map.get EBE be (pre_point_edge_index EBE s) = Some pe /\
    In pe (edges_of (live_graph (point_model s))) /\ block_edge_of s pe = Some be.
Proof.
  intros Hpoints Hbe; destruct (block_edge_covered Hpoints be Hbe)
    as [n [pe [Hn [Hout Hcross]]]].
  assert (Hlisted : In pe (edges_of (live_graph (point_model s)))).
  { apply in_flat_map; exists n; auto. }
  exists pe; split.
  - apply (pre_point_edge_index_exact EBE s Hpoints be pe); auto.
  - auto.
Qed.

Local Lemma pre_built_materializes_phis {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_expr_in_family a u -> pre_total_pure (pre_expression a) u = true ->
  forall b, frg_phi_needed EB EU a u b ->
    In (FrPhi b u) (frg_versions (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw Hready Hu Hpure b Hneeded.
  apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw).
  apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready); auto.
Qed.

Local Definition pre_selected_operand {B E U} (EU : encoding U) (u : U)
    (frame : frg_operand B E U * bool) : frg_operand B E U :=
  let '(operand, available) := frame in
  if available && Pos.eqb (encode EU (frg_version_expr (frg_operand_version operand))) (encode EU u)
  then operand else FrgOperand (FrUnavailable u) false.

Local Lemma pre_selected_operand_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u n frame :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_expr_in_family a u -> pre_total_pure (pre_expression a) u = true ->
  pre_observed_point a n -> pre_frame_laws EE a (build_frg EB EBE EN EE EV EU a) u n frame ->
  let f := build_frg EB EBE EN EE EV EU a in let op := pre_selected_operand EU u frame in
  frg_version_expr (frg_operand_version op) = u /\
  ((frg_operand_version op = FrUnavailable u <-> ~ exists d, frg_reusable a f u n d) /\
   (frg_operand_version op <> FrUnavailable u -> frg_reusable a f u n (frg_operand_version op))) /\
  (frg_operand_real_use op = true <-> pre_real_use_at EE a f n (frg_operand_version op)) /\
  In (frg_operand_version op) (frg_versions f).
Proof.
  intros Hlaw Hblocks Hpoints Hu Hpure Hobserved Hframe f op.
  pose proof (proj1 Hframe) as Hexpr; pose proof (proj1 (proj2 Hframe)) as Hreal.
  destruct (pre_frame_availability EB EN EE EV EU a f u n frame Hlaw Hblocks Hpoints Hu Hobserved
    (pre_built_materializes_phis EB EBE EN EE EV EU a u Hlaw Hblocks Hu Hpure) Hframe)
    as [Hiff Husable].
  unfold op, pre_selected_operand; destruct frame as [operand available].
  cbn [fst snd] in Hexpr, Hreal, Hiff, Husable |- *; rewrite Hexpr, Pos.eqb_refl, andb_true_r.
  destruct available; cbn [fst snd frg_operand_version frg_operand_real_use frg_version_expr]
    in Hiff, Husable |- *.
  - pose proof (Husable eq_refl) as Hreuse.
    assert (Hnonunavailable : frg_operand_version operand <> FrUnavailable u).
    { intro Heq; destruct (proj2 Hreuse) as [q [Hpoint Hsafe]]; rewrite Heq in Hpoint; discriminate.
      }
    split; [exact Hexpr|]; split.
    + split.
      * split; [intro Heq; exfalso; exact (Hnonunavailable Heq)|].
        intro Hnone; exfalso; apply Hnone; exists (frg_operand_version operand); exact Hreuse.
      * intros Hdefined; exact Hreuse.
    + split; [exact Hreal|exact (proj1 (proj1 Hreuse))].
  - split; [reflexivity|]; split.
    + split.
      * split.
        -- intros Heq Hexists; pose proof (proj2 Hiff Hexists) as Hfalse; discriminate.
        -- intros Hnone; reflexivity.
      * intros Hfalse; exfalso; apply Hfalse; reflexivity.
    + split.
      * split; [discriminate|intros [e [Hget Hdom]]].
        destruct (build_frg_occurrence_provenance EB EBE EN EE EV EU a Hlaw Hblocks e
          (FrUnavailable u) Hget) as [He [Hcomputed [Htotal [q [Hpoint Hreach]]]]]; discriminate.
      * unfold f; apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw); auto.
Qed.

Local Definition pre_link_entry_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b u be (op : frg_operand B E U) : Prop :=
  let f := build_frg EB EBE EN EE EV EU a in
  (FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index f) = true /\
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.target (block_graph (pre_ssa_points a)) be = b) /\
  exists v pe, pre_phi_translate a be u = Some v /\
    Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe /\
    frg_version_expr (frg_operand_version op) = v /\
    ((frg_operand_version op = FrUnavailable v <-> ~ exists d, frg_reusable a f v
        (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) d) /\
      (frg_operand_version op <> FrUnavailable v -> frg_reusable a f v
        (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) (frg_operand_version op)))
          /\
    (frg_operand_real_use op = true <-> pre_real_use_at EE a f
      (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) (frg_operand_version op)) /\
    In (frg_operand_version op) (frg_versions f).

Local Definition pre_link_index_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U)
    (index : Map.t ((B * U) * BE) (frg_operand B E U)) : Prop :=
  forall key op, Map.get (pair_encoding (pair_encoding EB EU) EBE) key index = Some op ->
    let '((b, u), be) := key in pre_link_entry_laws EB EBE EN EE EV EU a b u be op.

Local Lemma pre_map_sound_set {X Y} (EX : encoding X) (P : X -> Y -> Prop)
    index key value :
  (forall x y, Map.get EX x index = Some y -> P x y) -> P key value ->
  forall x y, Map.get EX x (Map.set EX key value index) = Some y -> P x y.
Proof.
  intros Hindex Hvalue x y Hget; destruct (dfs_eq_dec EX x key) as [Heq|Hne].
  - subst x; rewrite Map.get_set_same in Hget; inversion Hget; subst y; exact Hvalue.
  - rewrite Map.get_set_other in Hget by exact Hne; exact (Hindex x y Hget).
Qed.

Local Lemma pre_link_index_set {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) index b u be op :
  pre_link_index_sound EB EBE EN EE EV EU a index ->
  pre_link_entry_laws EB EBE EN EE EV EU a b u be op ->
  pre_link_index_sound EB EBE EN EE EV EU a
    (Map.set (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be) op index).
Proof.
  intros Hindex Hentry; unfold pre_link_index_sound; apply pre_map_sound_set;
    [exact Hindex|exact Hentry].
Qed.

Local Lemma pre_argument_selected_laws {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b default scope be u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In be (edges_of (block_graph (pre_ssa_points a))) ->
  Graph.source (block_graph (pre_ssa_points a)) be = b ->
  FinSet.mem (pair_encoding EB EU) (Graph.target (block_graph (pre_ssa_points a)) be, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (last (points_in_block (pre_ssa_points a) b) default) scope ->
  exists v, pre_phi_translate a be u = Some v /\
    pre_link_entry_laws EB EBE EN EE EV EU a
      (Graph.target (block_graph (pre_ssa_points a)) be) u be
      (pre_selected_operand EU v (pre_rename_top EU scope v)).
Proof.
  intros Hlaw Hblocks Hpoints Hbe Hsource Hphi Hscope.
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  destruct (proj1 (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hblocks _ u) Hphi)
    as [Hu [Hpure Hneeded]].
  destruct (pre_expr_closed_translation EV a Hlaw be u Hbe Hu) as [v Htranslate].
  assert (Hv : pre_expr_in_family a v) by (eapply pre_family_translate; eassumption).
  pose proof (pre_expr_translation_pure EV a Hlaw be u v Hpure Htranslate) as Hpurev.
  destruct (pre_incoming_point_exists EBE _ be Hssa Hbe) as [pe [Hindex [Hpe Hcross]]].
  pose proof (pre_cross_source_last _ be pe default Hssa Hpe Hcross) as Hlast.
  rewrite Hsource in Hlast.
  assert (Hframe : pre_frame_laws EE a (build_frg EB EBE EN EE EV EU a) v
    (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) (pre_rename_top EU scope v)).
  { rewrite Hlast; exact (Hscope v Hv Hpurev). }
  assert (Hobserved : pre_observed_point a
    (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)).
  { right; exists pe, be; repeat split; assumption. }
  exists v; split; [exact Htranslate|]; split.
  - split; [exact Hphi|]; split; [exact Hbe|reflexivity].
  - exists v, pe; split; [exact Htranslate|]; split; [exact Hindex|].
    exact (pre_selected_operand_laws EB EBE EN EE EV EU a v _ _
      Hlaw Hblocks Hpoints Hv Hpurev Hobserved Hframe).
Qed.

Local Lemma pre_rename_argument_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) b default scope acc be u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In be (edges_of (block_graph (pre_ssa_points a))) ->
  Graph.source (block_graph (pre_ssa_points a)) be = b ->
  FinSet.mem (pair_encoding EB EU) (Graph.target (block_graph (pre_ssa_points a)) be, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (last (points_in_block (pre_ssa_points a) b) default) scope ->
  pre_link_index_sound EB EBE EN EE EV EU a (pre_rename_links acc) ->
  pre_link_index_sound EB EBE EN EE EV EU a
    (pre_rename_links (pre_rename_argument EB EBE EU a scope acc (be, u))).
Proof.
  intros Hlaw Hblocks Hpoints Hbe Hsource Hphi Hscope Hindex.
  destruct (pre_argument_selected_laws EB EBE EN EE EV EU a b default scope be u
    Hlaw Hblocks Hpoints Hbe Hsource Hphi Hscope) as [v [Htranslate Hentry]].
  unfold pre_rename_argument; rewrite Htranslate.
  destruct (pre_rename_top EU scope v) as [operand available]; cbn [pre_rename_links].
  apply pre_link_index_set; [exact Hindex|exact Hentry].
Qed.

Local Lemma pre_rename_occurrence_links {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) :
  pre_rename_links (snd (fst (pre_rename_occurrence EB EE EU a e work))) =
    pre_rename_links (snd work).
Proof.
  destruct work as [scope acc]; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|]; [|reflexivity].
  destruct (pre_total_pure (pre_expression a) u); [|reflexivity].
  destruct (pre_rename_top EU scope u) as [operand available]; reflexivity.
Qed.

Local Lemma pre_rename_alter_links {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) u :
  pre_rename_links (snd (pre_rename_alter EB EU a e work u)) = pre_rename_links (snd work).
Proof.
  destruct work as [scope acc]; unfold pre_rename_alter; cbn [snd].
  destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) u);
    [reflexivity|exact (proj2 (proj2 (pre_rename_mark_data EB EU scope acc u)))].
Qed.

Local Lemma pre_rename_exit_links {B BE N E U} (EB : encoding B) (EN : encoding N)
    (EU : encoding U) exits n scope (acc : pre_rename_acc B BE E U) :
  pre_rename_links (snd (pre_rename_exit EB EN EU exits n (scope, acc))) = pre_rename_links acc.
Proof.
  unfold pre_rename_exit; cbn [snd]; apply pre_fold_projection; intros output u.
  exact (proj2 (proj2 (pre_rename_mark_data EB EU scope output u))).
Qed.

Local Lemma pre_rename_instruction_links {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b
    (work : pre_rename_scope B E U * pre_rename_acc B BE E U) e :
  pre_rename_links (snd (pre_rename_instruction EB EN EE EU a alterations exits phis b work e)) =
    pre_rename_links (snd work).
Proof.
  pose proof (pre_rename_occurrence_links EB EE EU a e work) as Hoccurrence.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e work) as [[scope acc] fresh]; cbn [fst snd] in
    Hoccurrence.
  pose proof (pre_fold_projection (pre_rename_alter EB EU a e)
    (fun state => pre_rename_links (snd state))
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)
    (pre_rename_alter_links EB EU a e)) as Haltered.
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (scope, acc)) as [frames output].
  cbn [fst snd] in Haltered |- *.
  exact (eq_trans (pre_rename_exit_links EB EN EU exits
    (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
    (pre_rename_definitions EB EE EU a phis b e fresh frames) output)
    (eq_trans Haltered Hoccurrence)).
Qed.

Local Lemma pre_rename_body_links {S O B BE N E V K C U} (EB : encoding B)
    (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis b scope
    (acc : pre_rename_acc B BE E U) :
  let entered := match points_in_block (pre_ssa_points a) b with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
    end in
  pre_rename_links (snd (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b) entered)) = pre_rename_links acc.
Proof.
  intro entered; rewrite (pre_fold_projection _ (fun state => pre_rename_links (snd state)) _
    entered (pre_rename_instruction_links EB EN EE EU a alterations exits phis b)).
  unfold entered; destruct (points_in_block (pre_ssa_points a) b); [reflexivity|].
  exact (pre_rename_exit_links EB EN EU exits n scope acc).
Qed.

Local Definition pre_argument_index_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (arguments : Map.t B (FinSet.t (BE * U))) : Prop :=
  forall b be u, In (be, u) (FinSet.elements (pre_group_lookup EB arguments b)) ->
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.source (block_graph (pre_ssa_points a)) be = b /\
    FinSet.mem (pair_encoding EB EU) (Graph.target (block_graph (pre_ssa_points a)) be, u)
      (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true.

Local Lemma pre_built_argument_index_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_argument_index_sound EB EBE EN EE EV EU a (pre_built_arguments EB EBE EN EE EV EU a).
Proof.
  intros Hready b be u Hin; apply (pre_rename_argument_index_exact EB EBE EU a _ _ b be u
    Hready (pre_build_phi_wf EB EBE EN EE EV EU a)); exact Hin.
Qed.

Local Lemma pre_rename_block_links_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments b scope acc :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  pre_argument_index_sound EB EBE EN EE EV EU a arguments ->
  pre_block_input_laws EB EBE EN EE EV EU a family exits arguments b scope acc ->
  pre_link_index_sound EB EBE EN EE EV EU a (pre_rename_links acc) ->
  pre_link_index_sound EB EBE EN EE EV EU a (pre_rename_links (snd
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
      (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc))).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Harguments [Hb [first [Hfirst [Hscope [Hwritten Htable]]]]]
    Hindex.
  pose proof (pre_rename_block_laws EB EBE EN EE EV EU a family exits arguments b first scope acc
    Hlaw Hblocks Hpoints Hfamily Hb Hfirst Hwritten Htable Hscope) as Hlast.
  pose proof (pre_rename_body_links EB EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
    (pre_build_phi_blocks EB EBE EN EE EV EU a) b scope acc) as Hlinks.
  cbn zeta in Hlinks.
  unfold pre_rename_block in Hlast |- *.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a (pre_rename_alter_index EE EV EU a
    family)
    exits (pre_build_phi_blocks EB EBE EN EE EV EU a) b) (instruction_edges (pre_ssa_points a) b)
    (match points_in_block (pre_ssa_points a) b with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end)) as [frames output] eqn:Hbody.
  rewrite ?Hbody in Hlinks; cbn [fst snd] in Hlast, Hlinks |- *.
  apply (pre_fold_invariant_in _ (fun output => pre_link_index_sound EB EBE EN EE EV EU a
    (pre_rename_links output)) _ output).
  - intros current [be u] Hin Hcurrent.
    destruct (Harguments b be u Hin) as [Hbe [Hsource Hphi]].
    exact (pre_rename_argument_sound EB EBE EN EE EV EU a b first frames current be u
      Hlaw Hblocks Hpoints Hbe Hsource Hphi Hlast Hcurrent).
  - rewrite Hlinks; exact Hindex.
Qed.

Local Lemma pre_checked_trace_invariant {X} (step : X -> X) good (P : X -> Prop) x final :
  pre_checked_trace step good x final ->
  (forall state, good state -> P state -> P (step state)) -> P x -> P final.
Proof.
  intros Hchecked Hstep; induction Hchecked; intro Hinitial; [exact Hinitial|].
  apply IHHchecked; apply Hstep; assumption.
Qed.

Local Lemma pre_rename_step_links_sound {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall u, In u family <-> pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true)
    ->
  pre_argument_index_sound EB EBE EN EE EV EU a arguments ->
  pre_step_input_laws EB EBE EN EE EV EU a family exits arguments work ->
  pre_link_index_sound EB EBE EN EE EV EU a (pre_rename_links (snd work)) ->
  pre_link_index_sound EB EBE EN EE EV EU a
    (pre_rename_links (snd (pre_walk_step EB EBE EN EE EV EU a family exits arguments work))).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Harguments; destruct work as [[[|[b scope] rest] seen] acc];
    intros Hinput Hindex; [exact Hindex|].
  unfold pre_walk_step, pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen) eqn:Hseen;
    [exact Hindex|].
  unfold pre_step_input_laws in Hinput; cbn [fst snd] in Hinput; rewrite Hseen in Hinput.
  pose proof (pre_rename_block_links_sound EB EBE EN EE EV EU a family exits arguments b scope acc
    Hlaw Hblocks Hpoints Hfamily Harguments Hinput Hindex) as Hblock.
  destruct (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
    (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc); exact Hblock.
Qed.

Local Lemma pre_built_links {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  frg_phi_operands (build_frg EB EBE EN EE EV EU a) =
    pre_rename_links (snd (pre_built_final EB EBE EN EE EV EU a)).
Proof.
  reflexivity.
Qed.

Local Lemma pre_built_links_sound {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  pre_link_index_sound EB EBE EN EE EV EU a (frg_phi_operands (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw Hblocks Hpoints; rewrite pre_built_links.
  refine (pre_checked_trace_invariant _ _ (fun work => pre_link_index_sound EB EBE EN EE EV EU a
    (pre_rename_links (snd work))) _ _ (pre_built_checked_trace EB EBE EN EE EV EU a
      Hlaw Hblocks Hpoints) _ _).
  - intros work Hinput Hindex; exact (pre_rename_step_links_sound EB EBE EN EE EV EU a
      _ _ _ work Hlaw Hblocks Hpoints (pre_built_family_exact EBE EV EU a Hlaw)
      (pre_built_argument_index_sound EB EBE EN EE EV EU a Hblocks) Hinput Hindex).
  - intros [[b u] be] op Hget; cbn [pre_built_initial fst snd pre_rename_links] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
Qed.

Local Definition pre_map_present {X Y} (EX : encoding X) key (index : Map.t X Y) : Prop :=
  exists value, Map.get EX key index = Some value.

Local Lemma pre_map_present_set {X Y} (EX : encoding X) query key (value : Y) index :
  pre_map_present EX query index -> pre_map_present EX query (Map.set EX key value index).
Proof.
  intros [old Hold]; destruct (dfs_eq_dec EX query key) as [Heq|Hne].
  - subst query; exists value; apply Map.get_set_same.
  - exists old; rewrite Map.get_set_other by exact Hne; exact Hold.
Qed.

Local Lemma pre_rename_argument_present {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope (acc : pre_rename_acc B BE E U) argument key :
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key (pre_rename_links acc) ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key
    (pre_rename_links (pre_rename_argument EB EBE EU a scope acc argument)).
Proof.
  intro Hpresent; destruct argument as [be u]; unfold pre_rename_argument.
  destruct (pre_phi_translate a be u) as [v|]; [|exact Hpresent].
  destruct (pre_rename_top EU scope v) as [operand available]; cbn [pre_rename_links].
  apply pre_map_present_set; exact Hpresent.
Qed.

Local Lemma pre_rename_arguments_present {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope (acc : pre_rename_acc B BE E U) arguments key :
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key (pre_rename_links acc) ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key
    (pre_rename_links (fold_left (pre_rename_argument EB EBE EU a scope) arguments acc)).
Proof.
  intro Hpresent; apply (pre_fold_invariant _ (fun output => pre_map_present
    (pair_encoding (pair_encoding EB EU) EBE) key (pre_rename_links output)) _ acc);
    [|exact Hpresent].
  intros output argument Hold; apply pre_rename_argument_present; exact Hold.
Qed.

Local Lemma pre_rename_argument_writes {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope (acc : pre_rename_acc B BE E U) be u v :
  pre_phi_translate a be u = Some v ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE)
    ((Graph.target (block_graph (pre_ssa_points a)) be, u), be)
    (pre_rename_links (pre_rename_argument EB EBE EU a scope acc (be, u))).
Proof.
  intro Htranslate; unfold pre_rename_argument; rewrite Htranslate.
  destruct (pre_rename_top EU scope v) as [operand available]; cbn [pre_rename_links].
  eexists; apply Map.get_set_same.
Qed.

Local Lemma pre_rename_arguments_contains {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope arguments be u v : In (be, u) arguments -> pre_phi_translate a be u = Some v ->
  forall acc : pre_rename_acc B BE E U,
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE)
    ((Graph.target (block_graph (pre_ssa_points a)) be, u), be)
    (pre_rename_links (fold_left (pre_rename_argument EB EBE EU a scope) arguments acc)).
Proof.
  intros Hin Htranslate; induction arguments as [|argument arguments IH]; intro acc;
    [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst argument; cbn [fold_left]; apply pre_rename_arguments_present.
    exact (pre_rename_argument_writes EB EBE EU a scope acc be u v Htranslate).
  - cbn [fold_left]; exact (IH Hin _).
Qed.

Local Lemma pre_rename_block_link_present {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc key :
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key (pre_rename_links acc) ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE) key (pre_rename_links (snd
    (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intro Hpresent; pose proof (pre_rename_body_links EB EN EE EU a alterations exits phis b scope
    acc)
    as Hlinks; cbn zeta in Hlinks; unfold pre_rename_block.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b)
    (match points_in_block (pre_ssa_points a) b with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end)) as [frames output] eqn:Hbody.
  rewrite ?Hbody in Hlinks; cbn [snd] in Hlinks |- *; apply pre_rename_arguments_present.
  rewrite Hlinks; exact Hpresent.
Qed.

Local Lemma pre_rename_block_contains {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments b scope acc be u v :
  In (be, u) (FinSet.elements (pre_group_lookup EB arguments b)) ->
  pre_phi_translate a be u = Some v ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE)
    ((Graph.target (block_graph (pre_ssa_points a)) be, u), be) (pre_rename_links (snd
      (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments b scope acc))).
Proof.
  intros Hin Htranslate; unfold pre_rename_block.
  destruct (fold_left (pre_rename_instruction EB EN EE EU a alterations exits phis b)
    (instruction_edges (pre_ssa_points a) b)
    (match points_in_block (pre_ssa_points a) b with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end)) as [frames output]; cbn [snd].
  exact (pre_rename_arguments_contains EB EBE EU a frames _ be u v Hin Htranslate output).
Qed.

Local Definition pre_argument_index_complete {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) (arguments : Map.t B (FinSet.t (BE * U))) : Prop :=
  forall b be u, In be (edges_of (block_graph (pre_ssa_points a))) ->
    Graph.source (block_graph (pre_ssa_points a)) be = b ->
    FinSet.mem (pair_encoding EB EU) (Graph.target (block_graph (pre_ssa_points a)) be, u)
      (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
    In (be, u) (FinSet.elements (pre_group_lookup EB arguments b)).

Local Lemma pre_built_argument_index_complete {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_argument_index_complete EB EBE EN EE EV EU a (pre_built_arguments EB EBE EN EE EV EU a).
Proof.
  intros Hready b be u Hbe Hsource Hphi; apply (pre_rename_argument_index_exact EB EBE EU a _ _ b be
    u
    Hready (pre_build_phi_wf EB EBE EN EE EV EU a)); auto.
Qed.

Local Definition pre_links_total {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) seen
    (index : Map.t ((B * U) * BE) (frg_operand B E U)) : Prop :=
  forall be u, In be (edges_of (block_graph (pre_ssa_points a))) ->
  FinSet.mem (pair_encoding EB EU) (Graph.target (block_graph (pre_ssa_points a)) be, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
  FinSet.mem EB (Graph.source (block_graph (pre_ssa_points a)) be) seen = true ->
  pre_map_present (pair_encoding (pair_encoding EB EU) EBE)
    ((Graph.target (block_graph (pre_ssa_points a)) be, u), be) index.

Local Lemma pre_rename_step_links_total {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family exits arguments work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_argument_index_complete EB EBE EN EE EV EU a arguments ->
  pre_links_total EB EBE EN EE EV EU a (snd (fst work)) (pre_rename_links (snd work)) ->
  let result := pre_walk_step EB EBE EN EE EV EU a family exits arguments work in
  pre_links_total EB EBE EN EE EV EU a (snd (fst result)) (pre_rename_links (snd result)).
Proof.
  intros Hlaw Hready Harguments; destruct work as [[[|[b scope] rest] seen] acc];
    intro Htotal; [exact Htotal|].
  unfold pre_walk_step, pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB b seen) eqn:Hseen;
    [exact Htotal|].
  destruct (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family) exits
    (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc) as [frames output]
      eqn:Hblock.
  cbn [fst snd]; intros be u Hbe Hphi Hsource; rewrite dfs_mem_add in Hsource.
  destruct (dfs_eq_dec EB (Graph.source (block_graph (pre_ssa_points a)) be) b) as [Heq|Hne].
  - destruct (proj1 (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready _ u) Hphi)
      as [Hu [Hpure Hneeded]].
    destruct (pre_expr_closed_translation EV a Hlaw be u Hbe Hu) as [v Htranslate].
    pose proof (pre_rename_block_contains EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a
      family)
      exits (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc be u v
      (Harguments b be u Hbe Heq Hphi) Htranslate) as Hpresent.
    rewrite Hblock in Hpresent; exact Hpresent.
  - pose proof (pre_rename_block_link_present EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a
    family)
      exits (pre_build_phi_blocks EB EBE EN EE EV EU a) arguments b scope acc _
      (Htotal be u Hbe Hphi Hsource)) as Hpresent.
    rewrite Hblock in Hpresent; exact Hpresent.
Qed.

Local Lemma pre_built_link_total {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  forall b u be, FinSet.mem (pair_encoding EB EU) (b, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
  In be (edges_of (block_graph (pre_ssa_points a))) ->
  Graph.target (block_graph (pre_ssa_points a)) be = b ->
  exists op, Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
    (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op.
Proof.
  intros Hlaw Hready.
  assert (Htotal : pre_links_total EB EBE EN EE EV EU a
    (snd (fst (pre_built_final EB EBE EN EE EV EU a)))
    (pre_rename_links (snd (pre_built_final EB EBE EN EE EV EU a)))).
  { refine (pre_walk_trace_invariant _ (fun work => pre_links_total EB EBE EN EE EV EU a
      (snd (fst work)) (pre_rename_links (snd work))) _ _ (pre_built_trace EB EBE EN EE EV EU a) _
        _).
    - intros work Hcovered; exact (pre_rename_step_links_total EB EBE EN EE EV EU a _ _ _ work
        Hlaw Hready (pre_built_argument_index_complete EB EBE EN EE EV EU a Hready) Hcovered).
    - intros be u Hbe Hphi Hfalse; cbn [pre_built_initial fst snd] in Hfalse;
        rewrite FinSet.mem_empty in Hfalse; discriminate. }
  intros b u be Hphi Hbe Htarget; rewrite <- Htarget in Hphi |- *; rewrite pre_built_links.
  apply (Htotal be u Hbe Hphi).
  exact (pre_built_seen_all EB EBE EN EE EV EU a Hlaw Hready _
    (proj1 (pre_listed_edge_out _ be (blocks_graph_wf (pre_expr_points EV a Hlaw)) Hbe))).
Qed.

Local Lemma pre_built_operand_domain {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u be op, Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
    (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op ->
  FinSet.mem (pair_encoding EB EU) (b, u) (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true /\
    In be (edges_of (block_graph (pre_ssa_points a))) /\
    Graph.target (block_graph (pre_ssa_points a)) be = b.
Proof.
  intros Hlaw Hblocks Hpoints b u be op Hget.
  exact (proj1 (pre_built_links_sound EB EBE EN EE EV EU a Hlaw Hblocks Hpoints _ op Hget)).
Qed.

Local Lemma pre_built_operand_selection {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u be op pe v, Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
    (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
  pre_phi_translate a be u = Some v ->
  (frg_operand_version op = FrUnavailable v <-> ~ exists d, frg_reusable a
    (build_frg EB EBE EN EE EV EU a) v
    (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) d) /\
  (frg_operand_version op <> FrUnavailable v -> frg_reusable a (build_frg EB EBE EN EE EV EU a) v
    (Graph.source (live_graph (point_model (pre_ssa_points a))) pe) (frg_operand_version op)).
Proof.
  intros Hlaw Hblocks Hpoints b u be op pe v Hget Hpoint Htranslate.
  destruct (pre_built_links_sound EB EBE EN EE EV EU a Hlaw Hblocks Hpoints _ op Hget)
    as [Hdomain [value [point [Hvalue [Hindex [Hexpr [Hselection Hrest]]]]]]].
  assert (Hsamevalue : value = v) by congruence; assert (Hsamepoint : point = pe) by congruence.
  rewrite Hsamevalue, Hsamepoint in Hselection; exact Hselection.
Qed.

Local Lemma pre_built_operand_real_use {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u be op pe, Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
    (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op ->
  Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe ->
  (frg_operand_real_use op = true <-> exists e,
    Map.get EE e (frg_occurrence_index (build_frg EB EBE EN EE EV EU a)) =
      Some (frg_operand_version op) /\
    dominates (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e)
      (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)).
Proof.
  intros Hlaw Hblocks Hpoints b u be op pe Hget Hpoint.
  destruct (pre_built_links_sound EB EBE EN EE EV EU a Hlaw Hblocks Hpoints _ op Hget)
    as [Hdomain [value [point [Hvalue [Hindex [Hexpr [Hselection [Hreal Hmember]]]]]]]].
  assert (Hsamepoint : point = pe) by congruence; subst point; exact Hreal.
Qed.

Local Lemma pre_built_operand_exact {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u be, FinSet.mem (pair_encoding EB EU) (b, u)
    (frg_phi_index (build_frg EB EBE EN EE EV EU a)) = true ->
  In be (edges_of (block_graph (pre_ssa_points a))) ->
  Graph.target (block_graph (pre_ssa_points a)) be = b ->
  exists op v, pre_phi_translate a be u = Some v /\
    Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
      (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op /\
    frg_version_expr (frg_operand_version op) = v /\
    (frg_operand_version op = FrUnavailable v \/ exists n pe,
      frg_version_point a (frg_operand_version op) = Some n /\
      Map.get EBE be (pre_point_edge_index EBE (pre_ssa_points a)) = Some pe /\
      dominates (live_graph (point_model (pre_ssa_points a))) n
        (Graph.source (live_graph (point_model (pre_ssa_points a))) pe)).
Proof.
  intros Hlaw Hblocks Hpoints b u be Hphi Hbe Htarget.
  destruct (pre_built_link_total EB EBE EN EE EV EU a Hlaw Hblocks b u be Hphi Hbe Htarget)
    as [op Hget].
  destruct (pre_built_links_sound EB EBE EN EE EV EU a Hlaw Hblocks Hpoints _ op Hget)
    as [Hdomain [v [pe [Htranslate [Hindex [Hexpr [Hselection Hrest]]]]]]].
  exists op, v; split; [exact Htranslate|]; split; [exact Hget|]; split; [exact Hexpr|].
  destruct (dfs_eq_dec (frg_version_encoding EB EE EU) (frg_operand_version op) (FrUnavailable v))
    as [Heq|Hne]; [left; exact Heq|right].
  destruct (proj1 (proj2 Hselection Hne)) as [Hd [Hu [n [Hpoint [Hdom Hnearest]]]]].
  exists n, pe; auto.
Qed.

(** * Exact unsafe events *)

Local Lemma pre_built_version_point_injective {S O B BE N E V K C U}
    (EB : encoding B) (EBE : encoding BE) (EN : encoding N) (EE : encoding E)
    (EV : encoding V) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) d d' q :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In d (frg_versions (build_frg EB EBE EN EE EV EU a)) ->
  In d' (frg_versions (build_frg EB EBE EN EE EV EU a)) ->
  frg_version_expr d = frg_version_expr d' ->
  frg_version_point a d = Some q -> frg_version_point a d' = Some q -> d = d'.
Proof.
  intros Hlaw Hready Hd Hd' Hexpr Hpoint Hpoint'.
  apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw) in Hd, Hd'.
  pose proof (pre_expr_points EV a Hlaw) as Hpoints.
  destruct d as [u|u|e u|b u], d' as [v|v|e' v|c v];
    cbn [frg_version_point frg_version_expr] in Hexpr, Hpoint, Hpoint';
    try discriminate; subst v; try reflexivity.
  - exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact (proj1 Hd')| | |].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
    + apply nth_error_In in Hpoint; inversion Hpoint'; subst q; exact Hpoint.
    + inversion Hpoint'; reflexivity.
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He Hi].
    exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |].
    + apply nth_error_In in Hpoint; inversion Hpoint'; subst q; exact Hpoint.
    + inversion Hpoint'; reflexivity.
  - exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact (proj1 Hd)| | |].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
    + apply nth_error_In in Hpoint'; inversion Hpoint; subst q; exact Hpoint'.
    + inversion Hpoint; reflexivity.
  - inversion Hpoint; inversion Hpoint'; subst q.
    f_equal; eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd)|
      exact (proj1 Hd')| | |congruence].
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
    + exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He Hi].
    assert (Heq : e = parameter_edge (pre_ssa_points a) c).
    { eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd)|exact He| |exact Hi|].
      - exact (proj1 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd)))).
      - congruence. }
    exfalso; exact (proj2 (pre_expr_real_internal EV a Hlaw e u (proj1 (proj2 Hd))) c Heq).
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    exfalso; eapply pre_internal_target_not_entry; [exact Hlaw|exact He|exact Hi| |].
    + apply nth_error_In in Hpoint'; inversion Hpoint; subst q; exact Hpoint'.
    + inversion Hpoint; reflexivity.
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    assert (Heq : e' = parameter_edge (pre_ssa_points a) b).
    { eapply pre_internal_target_unique; [exact Hpoints|exact (proj1 Hd')|exact He| |exact Hi|].
      - exact (proj1 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd')))).
      - congruence. }
    exfalso; exact (proj2 (pre_expr_real_internal EV a Hlaw e' u (proj1 (proj2 Hd'))) b Heq).
  - apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hready) in Hd, Hd'.
    pose proof (frg_phi_needed_nodes EB EU a u b (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd))) as Hb.
    pose proof (frg_phi_needed_nodes EB EU a u c (blocks_graph_wf Hpoints)
      (proj2 (proj2 Hd'))) as Hc.
    destruct (pre_parameter_edge_listed _ b Hpoints Hb) as [He Hi].
    destruct (pre_parameter_edge_listed _ c Hpoints Hc) as [He' Hi'].
    destruct (pre_internal_edge_block _ _ Hpoints He Hi) as [owner [Ho [Hedge Htarget]]].
    pose proof (pre_chain_target _ _ _ _ (points_ordered Hpoints b Hb)
      (nth_error_In _ _ (parameter_edge_first Hpoints b Hb))) as Htargetb.
    pose proof (pre_chain_target _ _ _ _ (points_ordered Hpoints c Hc)
      (nth_error_In _ _ (parameter_edge_first Hpoints c Hc))) as Htargetc.
    f_equal; rewrite <- (points_owner Hpoints b _ Hb (pre_tail_member _ _ Htargetb)).
    replace (Graph.target (live_graph (point_model (pre_ssa_points a)))
      (parameter_edge (pre_ssa_points a) b)) with
      (Graph.target (live_graph (point_model (pre_ssa_points a)))
        (parameter_edge (pre_ssa_points a) c)) by congruence.
    exact (points_owner Hpoints c _ Hc (pre_tail_member _ _ Htargetc)).
Qed.

Local Lemma pre_built_nearest_unique {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u n d d' :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  frg_nearest_version a (build_frg EB EBE EN EE EV EU a) u n d ->
  frg_nearest_version a (build_frg EB EBE EN EE EV EU a) u n d' -> d = d'.
Proof.
  intros Hlaw Hblocks Hpoints Hreach Hnear Hnear'; pose proof Hnear as Hleft; pose proof Hnear' as
    Hright.
  destruct Hleft as [Hd [Hu [q [Hq [Hdom Hminimal]]]]].
  destruct Hright as [Hd' [Hu' [q' [Hq' [Hdom' Hminimal']]]]].
  pose proof (pre_nearest_points_agree EN a _ u n d q d' q' Hpoints Hreach Hnear Hq Hnear' Hq')
    as Heq.
  apply (pre_built_version_point_injective EB EBE EN EE EV EU a d d' q
    Hlaw Hblocks Hd Hd'); [congruence|exact Hq|rewrite Heq; exact Hq'].
Qed.

Local Lemma pre_frame_real_unused {S O B BE N E V K C U} (EE : encoding E)
    (a : pre_expr_ssa S O B BE N E V K C U) f u n frame :
  pre_frame_laws EE a f u n frame ->
  (frg_operand_real_use (fst frame) = false <->
    frg_no_dominating_real_use EE a f n (frg_operand_version (fst frame))).
Proof.
  intro Hframe; pose proof (proj1 (proj2 Hframe)) as Hreal; split.
  - intros Hfalse e Hget Hdom; pose proof (proj2 Hreal (ex_intro _ e (conj Hget Hdom))) as Htrue;
      congruence.
  - intro Hnone; destruct (frg_operand_real_use (fst frame)) eqn:Hflag; [|reflexivity].
    destruct (proj1 Hreal eq_refl) as [e [Hget Hdom]]; exfalso; exact (Hnone e Hget Hdom).
Qed.

Local Lemma pre_frame_phi_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) u n frame b :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  reachable (live_graph (point_model (pre_ssa_points a))) n ->
  pre_frame_laws EE a (build_frg EB EBE EN EE EV EU a) u n frame ->
  ((frg_operand_version (fst frame) = FrPhi b u /\ frg_operand_real_use (fst frame) = false) <->
    frg_nearest_version a (build_frg EB EBE EN EE EV EU a) u n (FrPhi b u) /\
    frg_no_dominating_real_use EE a (build_frg EB EBE EN EE EV EU a) n (FrPhi b u)).
Proof.
  intros Hlaw Hblocks Hpoints Hreach Hframe.
  pose proof (pre_frame_real_unused EE a _ u n frame Hframe) as Hunused.
  pose proof (proj2 (proj2 Hframe)) as Hdefinition; split.
  - intros [Hversion Hreal]; split.
    + rewrite Hversion in Hdefinition; cbn [frg_version_point] in Hdefinition;
        exact (proj1 Hdefinition).
    + pose proof (proj1 Hunused Hreal) as Hnone; rewrite Hversion in Hnone; exact Hnone.
  - intros [Hnearest Hnone].
    destruct (frg_version_point a (frg_operand_version (fst frame))) as [q|] eqn:Hq.
    + destruct Hdefinition as [Hactual Havailable].
      pose proof (pre_built_nearest_unique EB EBE EN EE EV EU a u n _ (FrPhi b u)
        Hlaw Hblocks Hpoints Hreach Hactual Hnearest) as Hversion.
      split; [exact Hversion|]; apply Hunused; rewrite Hversion; exact Hnone.
    + destruct Hdefinition as [Hsentinel [Hfalse Habsent]].
      destruct Hnearest as [Hd [Hu [point [Hpoint [Hdom Hnearest]]]]].
      exfalso; exact (Habsent _ point Hd Hu Hpoint Hdom).
Qed.

Local Lemma pre_fold_membership {X A} (step : X -> A -> X) (member : X -> Prop)
    (event : A -> Prop) xs x :
  (forall state a, member (step state a) <-> member state \/ event a) ->
  (member (fold_left step xs x) <-> member x \/ exists a, In a xs /\ event a).
Proof.
  intro Hstep; revert x; induction xs as [|a xs IH]; intro x; cbn [fold_left].
  - split; [tauto|intros [Hx|[a [Hfalse Ha]]]; [exact Hx|contradiction]].
  - rewrite IH, Hstep; split.
    + intros [[Hx|Ha]|[b [Hb Hevent]]]; [left; exact Hx| |].
      * right; exists a; split; [left; reflexivity|exact Ha].
      * right; exists b; split; [right; exact Hb|exact Hevent].
    + intros [Hx|[b [[Heq|Hb] Hevent]]]; [left; left; exact Hx| |].
      * subst b; left; right; exact Hevent.
      * right; exists b; auto.
Qed.

Local Lemma pre_checked_fold_membership {X A} (step : X -> A -> X) good
    (member : X -> Prop) (event : A -> Prop) xs x :
  pre_checked_fold step good xs x ->
  (forall a state, good a state -> (member (step state a) <-> member state \/ event a)) ->
  (member (fold_left step xs x) <-> member x \/ exists a, In a xs /\ event a).
Proof.
  intros Hchecked Hstep; induction Hchecked as [x|a xs x Hgood Hchecked IH]; cbn [fold_left].
  - split; [tauto|intros [Hx|[a [Hfalse Ha]]]; [exact Hx|contradiction]].
  - rewrite IH, (Hstep a x Hgood); split.
    + intros [[Hx|Ha]|[b [Hb Hevent]]]; [left; exact Hx| |].
      * right; exists a; split; [left; reflexivity|exact Ha].
      * right; exists b; split; [right; exact Hb|exact Hevent].
    + intros [Hx|[b [[Heq|Hb] Hevent]]]; [left; left; exact Hx| |].
      * subst b; left; right; exact Hevent.
      * right; exists b; auto.
Qed.

Local Lemma pre_rename_mark_exact {B BE E U} (EB : encoding B) (EU : encoding U)
    scope (acc : pre_rename_acc B BE E U) v b u :
  (FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_unsafe (pre_rename_mark EB EU scope acc v)) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    fst (pre_rename_top EU scope v) = FrgOperand (FrPhi b u) false).
Proof.
  unfold pre_rename_mark; destruct (pre_rename_top EU scope v) as [[d real] available]; cbn [fst].
  destruct d as [value|value|e value|block value], real; cbn [pre_rename_unsafe];
    try (split; [tauto|intros [Hmem|Hbad]; [exact Hmem|discriminate]]).
  rewrite FinSet.mem_add; split.
  - intros [Heq|Hmem]; [right; inversion Heq; reflexivity|left; exact Hmem].
  - intros [Hmem|Heq]; [right; exact Hmem|left; inversion Heq; reflexivity].
Qed.

Local Lemma pre_rename_marks_exact {B BE E U} (EB : encoding B) (EU : encoding U)
    scope xs (acc : pre_rename_acc B BE E U) b u :
  (FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_unsafe (fold_left (pre_rename_mark EB EU scope) xs acc)) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    exists v, In v xs /\ fst (pre_rename_top EU scope v) = FrgOperand (FrPhi b u) false).
Proof.
  apply (pre_fold_membership _ (fun output => FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_unsafe output) = true)); intros output v; apply pre_rename_mark_exact.
Qed.

Local Lemma pre_same_expression_false {U} (EU : encoding U) value u :
  pre_same_expression EU value u = false <-> value <> Some u.
Proof.
  destruct value as [v|]; cbn [pre_same_expression]; [|split; congruence].
  rewrite Pos.eqb_neq; split.
  - intros Hne Heq; inversion Heq; subst v; contradiction.
  - intros Hne Heq; apply Hne; f_equal; apply (encode_injective EU); exact Heq.
Qed.

Local Lemma pre_rename_alter_operand {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e work v u :
  fst (pre_rename_top EU (fst (pre_rename_alter EB EU a e work v)) u) =
    fst (pre_rename_top EU (fst work) u).
Proof.
  destruct work as [scope acc]; unfold pre_rename_alter; cbn [fst].
  rewrite pre_rename_top_set; destruct (dfs_eq_dec EU u v) as [Heq|Hne];
    [subst v|]; reflexivity.
Qed.

Local Lemma pre_rename_alters_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e xs work b u :
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe
    (snd (fold_left (pre_rename_alter EB EU a e) xs work))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd work)) = true \/
    exists v, In v xs /\ pre_recomputed (pre_expression a) e <> Some v /\
      fst (pre_rename_top EU (fst work) v) = FrgOperand (FrPhi b u) false).
Proof.
  revert work; induction xs as [|v xs IH]; intros [scope acc]; cbn [fold_left].
  - split; [tauto|intros [Hmem|[v [Hfalse Hrest]]]; [exact Hmem|contradiction]].
  - rewrite IH; set (updated := pre_rename_alter EB EU a e (scope, acc) v).
    assert (Hone : FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd updated)) = true
      <->
      FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
      (pre_recomputed (pre_expression a) e <> Some v /\
       fst (pre_rename_top EU scope v) = FrgOperand (FrPhi b u) false)).
    { unfold updated, pre_rename_alter; cbn [snd].
      destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) v) eqn:Hsame.
      - split; [tauto|intros [Hmem|[Hne Htop]]; [exact Hmem|]].
        exfalso; apply (proj2 (pre_same_expression_false EU _ v)) in Hne; congruence.
      - rewrite pre_rename_mark_exact; apply (proj1 (pre_same_expression_false EU _ v)) in Hsame;
          tauto. }
    rewrite Hone; split.
    + intros [[Hmem|[Hdifferent Htop]]|[value [Hin [Hdifferent Htop]]]].
      * left; exact Hmem.
      * right; exists v; split; [left; reflexivity|auto].
      * right; exists value; split; [right; exact Hin|]; split; [exact Hdifferent|].
        change (fst (pre_rename_top EU
          (fst (pre_rename_alter EB EU a e (scope, acc) v)) value) =
          FrgOperand (FrPhi b u) false) in Htop.
        rewrite (pre_rename_alter_operand EB EU a e (scope, acc) v value) in Htop; exact Htop.
    + intros [Hmem|[value [[Heq|Hin] [Hdifferent Htop]]]].
      * left; left; exact Hmem.
      * subst value; left; right; auto.
      * right; exists value; split; [exact Hin|]; split; [exact Hdifferent|].
        change (fst (pre_rename_top EU
          (fst (pre_rename_alter EB EU a e (scope, acc) v)) value) =
          FrgOperand (FrPhi b u) false).
        rewrite (pre_rename_alter_operand EB EU a e (scope, acc) v value); exact Htop.
Qed.

Local Lemma pre_exit_index_pairs {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (family : list U) n (values : list U) :
  In (n, values) (flat_map (fun point =>
    if pre_exit_point a point then [(point, family)] else
    match Graph.out (live_graph (point_model (pre_ssa_points a))) point with
    | [] => [(point, family)]
    | _ => []
    end)
      (Graph.nodes (live_graph (point_model (pre_ssa_points a))))) <->
  In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) /\
  (pre_exit_point a n = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) n = []) /\
  values = family.
Proof.
  rewrite in_flat_map; split.
  - intros [point [Hpoint Hin]]; destruct (pre_exit_point a point) eqn:Hexit.
    + cbn in Hin; destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; auto|contradiction].
    + destruct (Graph.out (live_graph (point_model (pre_ssa_points a))) point) as [|e es] eqn:Hout;
        cbn in Hin; [|contradiction].
      destruct Hin as [Heq|Hfalse]; [inversion Heq; subst; auto|contradiction].
  - intros [Hn [[Hexit|Hout] Heq]]; subst values; exists n; split; [exact Hn| |exact Hn|].
    + rewrite Hexit; left; reflexivity.
    + destruct (pre_exit_point a n); [left; reflexivity|rewrite Hout; left; reflexivity].
Qed.

Local Lemma pre_exit_index_exact {S O B BE N E V K C U} (EN : encoding N)
    (a : pre_expr_ssa S O B BE N E V K C U) family n u :
  (In u (index_edges EN (pre_rename_exit_index EN a family) n) <->
    In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) /\
    (pre_exit_point a n = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) n = []) /\
    In u family).
Proof.
  unfold index_edges; split.
  - destruct (Map.get EN n (pre_rename_exit_index EN a family)) as [values|] eqn:Hget;
      [|contradiction].
    intro Hin; unfold pre_rename_exit_index in Hget; apply (pre_map_list_sound EN) in Hget.
    apply pre_exit_index_pairs in Hget; destruct Hget as [Hn [Hending Heq]]; subst values; auto.
  - intros [Hn [Hending Hu]].
    assert (Hget : Map.get EN n (pre_rename_exit_index EN a family) = Some family).
    { unfold pre_rename_exit_index; apply pre_map_list_unique.
      - intros values Hvalues; exact (proj2 (proj2 (proj1 (pre_exit_index_pairs a family n values)
        Hvalues))).
      - apply pre_exit_index_pairs; auto. }
    rewrite Hget; exact Hu.
Qed.

Local Lemma pre_rename_occurrence_unsafe {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e scope acc :
  pre_rename_unsafe (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc)))) =
    pre_rename_unsafe acc.
Proof.
  unfold pre_rename_occurrence; destruct (pre_recomputed (pre_expression a) e) as [u|];
    [destruct (pre_total_pure (pre_expression a) u)|]; try reflexivity.
  destruct (pre_rename_top EU scope u) as [[d real] available]; reflexivity.
Qed.

Local Lemma pre_rename_occurrence_other_operand {S O B BE N E V K C U} (EB : encoding B)
    (EE : encoding E) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U) e scope acc u :
  pre_recomputed (pre_expression a) e <> Some u ->
  fst (pre_rename_top EU (fst (fst (pre_rename_occurrence EB EE EU a e (scope, acc)))) u) =
    fst (pre_rename_top EU scope u).
Proof.
  intro Hne; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [v|] eqn:Hcomputed; [|reflexivity].
  destruct (pre_total_pure (pre_expression a) v); [|reflexivity].
  destruct (pre_rename_top EU scope v) as [[d real] available].
  cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU v))
    end else true);
    cbn [fst]; [reflexivity|].
  rewrite pre_rename_top_set; destruct (dfs_eq_dec EU u v) as [Heq|Hdifferent];
    [subst v; contradiction|reflexivity].
Qed.

Local Definition pre_phi_unused {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (EE : encoding E) n b u : Prop :=
  frg_nearest_version a f u n (FrPhi b u) /\ frg_no_dominating_real_use EE a f n (FrPhi b u).

Local Lemma pre_scope_phi_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) n scope b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) n scope ->
  pre_expr_in_family a u -> pre_total_pure (pre_expression a) u = true ->
  (fst (pre_rename_top EU scope u) = FrgOperand (FrPhi b u) false <->
    pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE n b u).
Proof.
  intros Hlaw Hblocks Hpoints Hn Hscope Hfamily Hpure.
  pose proof (pre_frame_phi_exact EB EBE EN EE EV EU a u n (pre_rename_top EU scope u) b
    Hlaw Hblocks Hpoints (pre_expr_reachable_points EV a Hlaw n Hn) (Hscope u Hfamily Hpure)) as
      Hiff.
  destruct (pre_rename_top EU scope u) as [[d real] available];
    cbn [fst frg_operand_version frg_operand_real_use] in Hiff |- *.
  rewrite <- Hiff; split; [intro Heq; inversion Heq; auto|intros [Heq Hreal]; subst; reflexivity].
Qed.

Local Lemma pre_phi_unused_family {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) n b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE n b u ->
  pre_expr_in_family a u /\ pre_total_pure (pre_expression a) u = true.
Proof.
  intros Hlaw Hblocks [[Hd Hnearest] Hnone].
  apply (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw) in Hd.
  apply (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hblocks) in Hd; tauto.
Qed.

Local Lemma pre_rename_exit_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family n scope
    (acc : pre_rename_acc B BE E U) b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a) n scope ->
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
      (pre_rename_exit EB EN EU (pre_rename_exit_index EN a family) n (scope, acc)))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    ((pre_exit_point a n = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) n = [])
      /\
     pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE n b u)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hn Hscope; unfold pre_rename_exit; cbn [snd].
  rewrite pre_rename_marks_exact; split.
  - intros [Hmem|[v [Hin Htop]]]; [left; exact Hmem|right].
    apply pre_exit_index_exact in Hin; destruct Hin as [Hlisted [Hending Hv]].
    destruct (proj1 (Hfamily v) Hv) as [Hmember Hpure].
    pose proof (proj1 (Hscope v Hmember Hpure)) as Hexpr; rewrite Htop in Hexpr.
    cbn [frg_version_expr frg_operand_version] in Hexpr; subst v; split; [exact Hending|].
    apply (pre_scope_phi_exact EB EBE EN EE EV EU a n scope b u
      Hlaw Hblocks Hpoints Hn Hscope Hmember Hpure); exact Htop.
  - intros [Hmem|[Hending Hphi]]; [left; exact Hmem|right; exists u].
    destruct (pre_phi_unused_family EB EBE EN EE EV EU a n b u Hlaw Hblocks Hphi)
      as [Hmember Hpure]; split.
    + apply pre_exit_index_exact; split; [exact Hn|]; split; [exact Hending|apply Hfamily; auto].
    + apply (pre_scope_phi_exact EB EBE EN EE EV EU a n scope b u
        Hlaw Hblocks Hpoints Hn Hscope Hmember Hpure); exact Hphi.
Qed.

Local Lemma pre_rename_kills_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family e scope
    (acc : pre_rename_acc B BE E U) b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  In e (edges_of (live_graph (point_model (pre_ssa_points a)))) ->
  pre_scope_laws EE EU a (build_frg EB EBE EN EE EV EU a)
    (Graph.source (live_graph (point_model (pre_ssa_points a))) e) scope ->
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
    (fold_left (pre_rename_alter EB EU a e)
      (FinSet.elements (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e))
      (fst (pre_rename_occurrence EB EE EU a e (scope, acc)))))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    (kill (pre_genkill (pre_expression a)) e u = true /\
     pre_recomputed (pre_expression a) e <> Some u /\
     pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE
       (Graph.source (live_graph (point_model (pre_ssa_points a))) e) b u)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily He Hscope.
  pose proof (proj1 (pre_listed_edge_out _ e (points_graph_wf (pre_expr_points EV a Hlaw)) He)) as
    Hn.
  rewrite pre_rename_alters_unsafe_exact, pre_rename_occurrence_unsafe; split.
  - intros [Hmem|[v [Hin [Hdifferent Htop]]]]; [left; exact Hmem|right].
    apply pre_rename_alter_index_sound in Hin; destruct Hin as [Hedge [Hv Hkill]].
    rewrite (pre_rename_occurrence_other_operand EB EE EU a e scope acc v Hdifferent) in Htop.
    destruct (proj1 (Hfamily v) Hv) as [Hmember Hpure].
    pose proof (proj1 (Hscope v Hmember Hpure)) as Hexpr; rewrite Htop in Hexpr.
    cbn [frg_version_expr frg_operand_version] in Hexpr; subst v.
    split; [exact Hkill|]; split; [exact Hdifferent|].
    apply (pre_scope_phi_exact EB EBE EN EE EV EU a _ scope b u
      Hlaw Hblocks Hpoints Hn Hscope Hmember Hpure); exact Htop.
  - intros [Hmem|[Hkill [Hdifferent Hphi]]]; [left; exact Hmem|right; exists u].
    destruct (pre_phi_unused_family EB EBE EN EE EV EU a _ b u Hlaw Hblocks Hphi)
      as [Hmember Hpure]; split.
    + apply (pre_rename_alter_index_exact EE EV EU a family e u Hlaw Hmember).
      split; [exact He|]; split; [apply Hfamily; auto|exact Hkill].
    + split; [exact Hdifferent|].
      rewrite (pre_rename_occurrence_other_operand EB EE EU a e scope acc u Hdifferent).
      apply (pre_scope_phi_exact EB EBE EN EE EV EU a _ scope b u
        Hlaw Hblocks Hpoints Hn Hscope Hmember Hpure); exact Hphi.
Qed.

Local Definition pre_instruction_unsafe_event {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (EE : encoding E) e b u : Prop :=
  (kill (pre_genkill (pre_expression a)) e u = true /\
   pre_recomputed (pre_expression a) e <> Some u /\
   pre_phi_unused a f EE (Graph.source (live_graph (point_model (pre_ssa_points a))) e) b u) \/
  ((pre_exit_point a (Graph.target (live_graph (point_model (pre_ssa_points a))) e) = true \/
    Graph.out (live_graph (point_model (pre_ssa_points a)))
      (Graph.target (live_graph (point_model (pre_ssa_points a))) e) = []) /\
   pre_phi_unused a f EE (Graph.target (live_graph (point_model (pre_ssa_points a))) e) b u).

Local Lemma pre_rename_instruction_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family owner e scope acc b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  In owner (Graph.nodes (block_graph (pre_ssa_points a))) ->
  pre_instruction_input_laws EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
    owner e (scope, acc) ->
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
    (pre_instruction_step EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
      owner (scope, acc) e))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    pre_instruction_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE e b u).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Howner [Hin [Hscope [Hnone [Hfresh Hpacket]]]].
  pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (pre_instruction_edge_listed _ owner e Hssa Howner Hin) as He.
  destruct (pre_listed_edge_out _ e (points_graph_wf Hssa) He) as [Hsource Hout].
  pose proof (out_target_in (points_graph_wf Hssa) _ e Hsource Hout) as Htarget.
  pose proof (pre_rename_instruction_laws EB EBE EN EE EV EU a family
    (pre_rename_exit_index EN a family) owner e scope acc Hlaw Hblocks Hpoints Hfamily
    Howner Hin Hnone Hfresh Hpacket Hscope) as Hafter.
  pose proof (pre_rename_kills_unsafe_exact EB EBE EN EE EV EU a family e scope acc b u
    Hlaw Hblocks Hpoints Hfamily He Hscope) as Hkills.
  unfold pre_instruction_step, pre_rename_instruction in Hafter |- *.
  destruct (pre_rename_occurrence EB EE EU a e (scope, acc)) as [[observed output] fresh]
    eqn:Hobserved.
  rewrite ?Hobserved in Hkills; cbn [fst snd] in Hkills.
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE (pre_rename_alter_index EE EV EU a family) e))
    (observed, output)) as [frames altered] eqn:Haltered.
  rewrite ?Haltered in Hkills; cbn [fst snd] in Hkills, Hafter |- *.
  rewrite (proj1 (pre_rename_exit_scope EB EN EU (pre_rename_exit_index EN a family)
    _ _ altered)) in Hafter.
  rewrite (pre_rename_exit_unsafe_exact EB EBE EN EE EV EU a family _ _ altered b u
    Hlaw Hblocks Hpoints Hfamily Htarget Hafter), Hkills.
  unfold pre_instruction_unsafe_event; tauto.
Qed.

Local Lemma pre_rename_argument_unsafe {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EU : encoding U) (a : pre_expr_ssa S O B BE N E V K C U)
    scope acc argument :
  pre_rename_unsafe (pre_rename_argument EB EBE EU a scope acc argument) = pre_rename_unsafe acc.
Proof.
  destruct argument as [be u]; unfold pre_rename_argument.
  destruct (pre_phi_translate a be u) as [v|]; [|reflexivity].
  destruct (pre_rename_top EU scope v); reflexivity.
Qed.

Local Lemma pre_rename_block_unsafe_body {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments owner scope acc :
  pre_rename_unsafe (snd (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments
    owner scope acc)) = pre_rename_unsafe (snd (fold_left
      (pre_rename_instruction EB EN EE EU a alterations exits phis owner)
      (instruction_edges (pre_ssa_points a) owner)
      (match points_in_block (pre_ssa_points a) owner with
       | [] => (scope, acc)
       | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
       end))).
Proof.
  unfold pre_rename_block; destruct (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis owner)
    (instruction_edges (pre_ssa_points a) owner)
    (match points_in_block (pre_ssa_points a) owner with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end))
    as [frames output]; cbn [snd]; apply pre_fold_projection.
  intros current argument; apply pre_rename_argument_unsafe.
Qed.

Local Lemma pre_rename_block_unsafe_observations {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family arguments owner first scope acc b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  nth_error (points_in_block (pre_ssa_points a) owner) 0 = Some first ->
  pre_block_input_laws EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
    arguments owner scope acc ->
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family)
      (pre_rename_exit_index EN a family) (pre_build_phi_blocks EB EBE EN EE EV EU a)
      arguments owner scope acc))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    ((pre_exit_point a first = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) first
      = []) /\
      pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE first b u) \/
    exists e, In e (instruction_edges (pre_ssa_points a) owner) /\
      pre_instruction_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE e b u).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hfirst Hinput.
  pose proof (proj1 Hinput) as Howner.
  destruct (pre_block_checked_fold EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
    arguments owner scope acc Hlaw Hblocks Hpoints Hfamily Hinput) as [head [Hhead Hchecked]].
  assert (Heq : head = first) by congruence; subst head.
  destruct Hinput as [Hb [head [Hhead' [Hscope Hrest]]]].
  assert (Heq : head = first) by congruence; subst head.
  assert (Hlisted : In first (Graph.nodes (live_graph (point_model (pre_ssa_points a))))).
  { apply (points_covered (pre_expr_points EV a Hlaw)); exists owner; split;
      [exact Howner|exact (nth_error_In _ _ Hfirst)]. }
  rewrite pre_rename_block_unsafe_body.
  assert (Hentered : (match points_in_block (pre_ssa_points a) owner with
    | [] => (scope, acc)
    | n :: _ => pre_rename_exit EB EN EU (pre_rename_exit_index EN a family) n (scope, acc)
    end) = pre_rename_exit EB EN EU (pre_rename_exit_index EN a family) first (scope, acc)).
  { destruct (points_in_block (pre_ssa_points a) owner); cbn in Hfirst;
      [discriminate|inversion Hfirst; reflexivity]. }
  rewrite Hentered.
  fold (pre_instruction_step EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family) owner).
  rewrite (pre_checked_fold_membership _ _ (fun work => FinSet.mem (pair_encoding EB EU) (b, u)
    (pre_rename_unsafe (snd work)) = true)
    (fun e => pre_instruction_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE e b u)
    _ _ Hchecked).
  - rewrite (pre_rename_exit_unsafe_exact EB EBE EN EE EV EU a family first scope acc b u
      Hlaw Hblocks Hpoints Hfamily Hlisted Hscope); tauto.
  - intros e [frames output] Hgood; exact (pre_rename_instruction_unsafe_exact EB EBE EN EE EV EU a
      family owner e frames output b u Hlaw Hblocks Hpoints Hfamily Howner Hgood).
Qed.

Local Lemma pre_chain_point_cases {N E} (g : Graph.t N E) ns es first n :
  point_chain g ns es -> nth_error ns 0 = Some first -> In n ns ->
  n = first \/ exists e, In e es /\ Graph.target g e = n.
Proof.
  intros Hchain; revert first; induction Hchain as [point|point next ns edge es Hedge Htarget Hchain
    IH];
    intros first Hfirst Hin; cbn in Hfirst; inversion Hfirst; subst first.
  - cbn in Hin; destruct Hin as [Heq|Hfalse]; [left; congruence|contradiction].
  - destruct Hin as [Heq|Hin]; [left; congruence|].
    destruct (IH next eq_refl Hin) as [Heq|[e [He Hn]]].
    + right; exists edge; split; [left; reflexivity|congruence].
    + right; exists e; split; [right; exact He|exact Hn].
Qed.

Local Definition pre_unsafe_event {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) n u : Prop :=
  pre_exit_point a n = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) n = [] \/
  exists e, In e (Graph.out (live_graph (point_model (pre_ssa_points a))) n) /\
    kill (pre_genkill (pre_expression a)) e u = true /\ pre_recomputed (pre_expression a) e <> Some
      u.

Local Definition pre_block_unsafe_event {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (EE : encoding E) owner b u : Prop := exists n,
  In n (points_in_block (pre_ssa_points a) owner) /\ pre_phi_unused a f EE n b u /\
    pre_unsafe_event a n u.

Local Lemma pre_block_unsafe_events_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) owner first b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  In owner (Graph.nodes (block_graph (pre_ssa_points a))) ->
  nth_error (points_in_block (pre_ssa_points a) owner) 0 = Some first ->
  ((((pre_exit_point a first = true \/ Graph.out (live_graph (point_model (pre_ssa_points a))) first
    = []) /\
      pre_phi_unused a (build_frg EB EBE EN EE EV EU a) EE first b u) \/
    exists e, In e (instruction_edges (pre_ssa_points a) owner) /\
      pre_instruction_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE e b u) <->
    pre_block_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE owner b u).
Proof.
  intros Hlaw Hblocks Howner Hfirst; pose proof (pre_expr_points EV a Hlaw) as Hssa.
  pose proof (points_ordered Hssa owner Howner) as Hchain; split.
  - intros [[Hending Hphi]|[e [Hin [[Hkill [Hdifferent Hphi]]|[Hending Hphi]]]]].
    + exists first; split; [exact (nth_error_In _ _ Hfirst)|]; split; [exact Hphi|].
      unfold pre_unsafe_event; tauto.
    + exists (Graph.source (live_graph (point_model (pre_ssa_points a))) e); split.
      * exact (pre_chain_source_member _ _ _ e (points_graph_wf Hssa) Hchain Hin).
      * split; [exact Hphi|]; right; right; exists e; split; [|auto].
        exact (proj2 (pre_listed_edge_out _ e (points_graph_wf Hssa)
          (pre_instruction_edge_listed _ owner e Hssa Howner Hin))).
    + exists (Graph.target (live_graph (point_model (pre_ssa_points a))) e); split.
      * apply pre_tail_member; exact (pre_chain_target _ _ _ e Hchain Hin).
      * split; [exact Hphi|]; unfold pre_unsafe_event; tauto.
  - intros [n [Hn [Hphi Hevent]]]; destruct Hevent as [Hexit|[Hout|[e [He [Hkill Hdifferent]]]]].
    + destruct (pre_chain_point_cases _ _ _ first n Hchain Hfirst Hn)
        as [Heq|[e [Hin Htarget]]].
      * subst n; left; auto.
      * right; exists e; split; [exact Hin|]; right; rewrite Htarget; auto.
    + destruct (pre_chain_point_cases _ _ _ first n Hchain Hfirst Hn)
        as [Heq|[e [Hin Htarget]]].
      * subst n; left; auto.
      * right; exists e; split; [exact Hin|]; right; rewrite Htarget; auto.
    + assert (Hlisted : In n (Graph.nodes (live_graph (point_model (pre_ssa_points a))))).
      { apply (points_covered Hssa); exists owner; auto. }
      assert (Hedge : In e (edges_of (live_graph (point_model (pre_ssa_points a))))).
      { apply in_flat_map; exists n; auto. }
      destruct (pre_phi_unused_family EB EBE EN EE EV EU a n b u Hlaw Hblocks Hphi)
        as [Hfamily Hpure].
      pose proof (pre_kill_internal EV a e u Hlaw Hfamily Hedge Hkill) as Hinternal.
      pose proof (instruction_edges_complete Hssa n e Hlisted He Hinternal) as Hin.
      rewrite (points_owner Hssa owner n Howner Hn) in Hin.
      right; exists e; split; [exact Hin|]; left.
      rewrite (out_source (points_graph_wf Hssa) n e He); auto.
Qed.

Local Lemma pre_rename_block_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family arguments owner scope acc b u :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  pre_block_input_laws EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
    arguments owner scope acc ->
  (FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family)
      (pre_rename_exit_index EN a family) (pre_build_phi_blocks EB EBE EN EE EV EU a)
      arguments owner scope acc))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    pre_block_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE owner b u).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily Hinput; pose proof (proj1 Hinput) as Howner.
  destruct (proj2 Hinput) as [first [Hfirst Hrest]].
  rewrite (pre_rename_block_unsafe_observations EB EBE EN EE EV EU a family arguments owner first
    scope acc b u Hlaw Hblocks Hpoints Hfamily Hfirst Hinput).
  rewrite <- (pre_block_unsafe_events_exact EB EBE EN EE EV EU a owner first b u
    Hlaw Hblocks Howner Hfirst); tauto.
Qed.

Local Definition pre_unsafe_seen_exact {S O B BE N E V K C U}
    (a : pre_expr_ssa S O B BE N E V K C U) (f : factored_redundancy_graph B BE E U)
    (EB : encoding B) (EE : encoding E) (EU : encoding U) seen seeds : Prop := forall b u,
  (FinSet.mem (pair_encoding EB EU) (b, u) seeds = true <-> exists owner,
    In owner (Graph.nodes (block_graph (pre_ssa_points a))) /\ FinSet.mem EB owner seen = true /\
    pre_block_unsafe_event a f EE owner b u).

Local Lemma pre_rename_step_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) family arguments work :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  (forall v, In v family <-> pre_expr_in_family a v /\ pre_total_pure (pre_expression a) v = true)
    ->
  pre_step_input_laws EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family) arguments work
    ->
  pre_unsafe_seen_exact a (build_frg EB EBE EN EE EV EU a) EB EE EU
    (snd (fst work)) (pre_rename_unsafe (snd work)) ->
  let result := pre_walk_step EB EBE EN EE EV EU a family (pre_rename_exit_index EN a family)
    arguments work in
  pre_unsafe_seen_exact a (build_frg EB EBE EN EE EV EU a) EB EE EU
    (snd (fst result)) (pre_rename_unsafe (snd result)).
Proof.
  intros Hlaw Hblocks Hpoints Hfamily; destruct work as [[[|[owner scope] rest] seen] acc];
    intros Hinput Hindex; [exact Hindex|].
  unfold pre_walk_step, pre_rename_step; cbn [fst snd]; destruct (FinSet.mem EB owner seen)
    eqn:Hseen;
    [exact Hindex|].
  unfold pre_step_input_laws in Hinput; cbn [fst snd] in Hinput; rewrite Hseen in Hinput.
  pose proof (proj1 Hinput) as Howner.
  assert (Hlocal : forall b u, FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe (snd
    (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family)
      (pre_rename_exit_index EN a family) (pre_build_phi_blocks EB EBE EN EE EV EU a)
      arguments owner scope acc))) = true <->
    FinSet.mem (pair_encoding EB EU) (b, u) (pre_rename_unsafe acc) = true \/
    pre_block_unsafe_event a (build_frg EB EBE EN EE EV EU a) EE owner b u).
  { intros b u; exact (pre_rename_block_unsafe_exact EB EBE EN EE EV EU a family arguments
      owner scope acc b u Hlaw Hblocks Hpoints Hfamily Hinput). }
  destruct (pre_rename_block EB EBE EN EE EU a (pre_rename_alter_index EE EV EU a family)
    (pre_rename_exit_index EN a family) (pre_build_phi_blocks EB EBE EN EE EV EU a)
    arguments owner scope acc) as [frames output] eqn:Hblock.
  cbn [fst snd] in Hlocal |- *; intros b u; rewrite (Hlocal b u), (Hindex b u); split.
  - intros [[block [Hb [Hmem Hevent]]]|Hevent].
    + exists block; split; [exact Hb|]; split; [apply FinSet.mem_add; right; exact Hmem|exact
      Hevent].
    + exists owner; split; [exact Howner|]; split; [apply FinSet.mem_add; left; reflexivity|exact
      Hevent].
  - intros [block [Hb [Hmem Hevent]]]; apply FinSet.mem_add in Hmem; destruct Hmem as [Heq|Hmem].
    + subst block; right; exact Hevent.
    + left; exists block; auto.
Qed.

Local Lemma pre_built_unsafe {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  frg_unsafe_seeds (build_frg EB EBE EN EE EV EU a) =
    pre_rename_unsafe (snd (pre_built_final EB EBE EN EE EV EU a)).
Proof.
  reflexivity.
Qed.

Local Lemma pre_built_unsafe_exact {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u, (FinSet.mem (pair_encoding EB EU) (b, u)
    (frg_unsafe_seeds (build_frg EB EBE EN EE EV EU a)) = true <->
    exists n, In n (Graph.nodes (live_graph (point_model (pre_ssa_points a)))) /\
      frg_nearest_version a (build_frg EB EBE EN EE EV EU a) u n (FrPhi b u) /\
      frg_no_dominating_real_use EE a (build_frg EB EBE EN EE EV EU a) n (FrPhi b u) /\
      pre_unsafe_event a n u).
Proof.
  intros Hlaw Hblocks Hpoints.
  assert (Hfinal : pre_unsafe_seen_exact a (build_frg EB EBE EN EE EV EU a) EB EE EU
    (snd (fst (pre_built_final EB EBE EN EE EV EU a)))
    (pre_rename_unsafe (snd (pre_built_final EB EBE EN EE EV EU a)))).
  { refine (pre_checked_trace_invariant _ _ (fun work => pre_unsafe_seen_exact a
      (build_frg EB EBE EN EE EV EU a) EB EE EU (snd (fst work)) (pre_rename_unsafe (snd work)))
      _ _ (pre_built_checked_trace EB EBE EN EE EV EU a Hlaw Hblocks Hpoints) _ _).
    - intros work Hinput Hindex; exact (pre_rename_step_unsafe_exact EB EBE EN EE EV EU a
        (pre_built_family EBE EV EU a) (pre_built_arguments EB EBE EN EE EV EU a) work
        Hlaw Hblocks Hpoints (pre_built_family_exact EBE EV EU a Hlaw) Hinput Hindex).
    - intros b u; cbn [pre_built_initial fst snd pre_rename_unsafe]; rewrite FinSet.mem_empty;
      split.
      + discriminate.
      + intros [owner [Howner [Hfalse Hevent]]]; rewrite FinSet.mem_empty in Hfalse; discriminate. }
  intros b u; rewrite pre_built_unsafe, (Hfinal b u); split.
  - intros [owner [Howner [Hseen [n [Hn [[Hnearest Hnone] Hevent]]]]]].
    exists n; split; [|auto].
    apply (points_covered (pre_expr_points EV a Hlaw)); exists owner; auto.
  - intros [n [Hn [Hnearest [Hnone Hevent]]]].
    destruct (proj1 (points_covered (pre_expr_points EV a Hlaw) n) Hn) as [owner [Howner Hmember]].
    exists owner; split; [exact Howner|]; split.
    + exact (pre_built_seen_all EB EBE EN EE EV EU a Hlaw Hblocks owner Howner).
    + exists n; split; [exact Hmember|]; split; [split; assumption|exact Hevent].
Qed.

(** The concrete indexed producer satisfies every adopted graph obligation. *)
Theorem build_frg_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  frg_wf EB EBE EN EE EV EU a (build_frg EB EBE EN EE EV EU a).
Proof.
  intros Hlaw Hblocks Hpoints; constructor.
  - apply build_frg_versions_nodup.
  - exact (build_frg_versions_exact EB EBE EN EE EV EU a Hlaw).
  - exact (build_frg_phi_exact EB EBE EN EE EV EU a Hlaw Hblocks).
  - intros e u He Hcomputed Hpure; exact (proj1 (pre_built_occurrence_laws EB EBE EN EE EV EU a
      Hlaw Hblocks Hpoints e u He Hcomputed Hpure)).
  - intros e d Hget; destruct (build_frg_occurrence_provenance EB EBE EN EE EV EU a
      Hlaw Hblocks e d Hget) as [He [Hcomputed [Hpure Hpoint]]]; auto.
  - exact (pre_built_fresh_exact EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
  - intros e Hfresh; exact (proj1 (pre_built_fresh_sound EB EBE EN EE EV EU a Hlaw Hblocks e
    Hfresh)).
  - intros e u He Hcomputed Hpure; exact (proj2 (proj2 (pre_built_occurrence_laws EB EBE EN EE EV EU
    a
      Hlaw Hblocks Hpoints e u He Hcomputed Hpure))).
  - exact (pre_built_operand_exact EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
  - exact (pre_built_operand_domain EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
  - exact (pre_built_operand_selection EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
  - exact (pre_built_operand_real_use EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
  - exact (pre_built_unsafe_exact EB EBE EN EE EV EU a Hlaw Hblocks Hpoints).
Qed.

(** * Canonical output indexes *)

Local Definition pre_rename_acc_wf {B BE E U} (EB : encoding B) (EBE : encoding BE)
    (EE : encoding E) (EU : encoding U) (acc : pre_rename_acc B BE E U) : Prop :=
  Map.wf EE (pre_rename_occurrences acc) /\ FinSet.wf EE (pre_rename_fresh acc) /\
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (pre_rename_links acc) /\
  FinSet.wf (pair_encoding EB EU) (pre_rename_unsafe acc).

Local Lemma pre_rename_mark_acc_wf {B BE E U} (EB : encoding B) (EBE : encoding BE)
    (EE : encoding E) (EU : encoding U) scope (acc : pre_rename_acc B BE E U) u :
  pre_rename_acc_wf EB EBE EE EU acc ->
  pre_rename_acc_wf EB EBE EE EU (pre_rename_mark EB EU scope acc u).
Proof.
  intros [Hocc [Hfresh [Hlinks Hunsafe]]]; unfold pre_rename_mark.
  destruct (pre_rename_top EU scope u) as [[d real] available]; destruct d, real;
    cbn [pre_rename_acc_wf pre_rename_occurrences pre_rename_fresh pre_rename_links
      pre_rename_unsafe];
    repeat split; try assumption.
  apply Map.wf_set; exact Hunsafe.
Qed.

Local Lemma pre_rename_occurrence_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e scope acc :
  pre_rename_acc_wf EB EBE EE EU acc ->
  pre_rename_acc_wf EB EBE EE EU
    (snd (fst (pre_rename_occurrence EB EE EU a e (scope, acc)))).
Proof.
  intro Hwf; unfold pre_rename_occurrence.
  destruct (pre_recomputed (pre_expression a) e) as [u|]; [|exact Hwf].
  destruct (pre_total_pure (pre_expression a) u); [|exact Hwf].
  destruct (pre_rename_top EU scope u) as [[d real] available]; cbn [frg_operand_version].
  destruct (if available then match d with
    | FrUnavailable _ => true
    | _ => negb (Pos.eqb (encode EU (frg_version_expr d)) (encode EU u))
    end else true);
    destruct Hwf as [Hocc [Hfresh [Hlinks Hunsafe]]];
    cbn [fst snd pre_rename_acc_wf pre_rename_occurrences pre_rename_fresh
      pre_rename_links pre_rename_unsafe]; repeat split; try assumption;
    apply Map.wf_set; assumption.
Qed.

Local Lemma pre_rename_alter_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) e work u :
  pre_rename_acc_wf EB EBE EE EU (snd work) ->
  pre_rename_acc_wf EB EBE EE EU (snd (pre_rename_alter EB EU a e work u)).
Proof.
  destruct work as [scope acc]; intro Hwf; unfold pre_rename_alter; cbn [snd].
  destruct (pre_same_expression EU (pre_recomputed (pre_expression a) e) u);
    [exact Hwf|apply pre_rename_mark_acc_wf; exact Hwf].
Qed.

Local Lemma pre_rename_exit_acc_wf {B BE N E U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EU : encoding U) exits n scope
    (acc : pre_rename_acc B BE E U) :
  pre_rename_acc_wf EB EBE EE EU acc ->
  pre_rename_acc_wf EB EBE EE EU (snd (pre_rename_exit EB EN EU exits n (scope, acc))).
Proof.
  intro Hwf; unfold pre_rename_exit; cbn [snd]; apply pre_fold_invariant.
  - intros output u Houtput; apply pre_rename_mark_acc_wf; exact Houtput.
  - exact Hwf.
Qed.

Local Lemma pre_rename_instruction_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis owner work e :
  pre_rename_acc_wf EB EBE EE EU (snd work) ->
  pre_rename_acc_wf EB EBE EE EU (snd
    (pre_rename_instruction EB EN EE EU a alterations exits phis owner work e)).
Proof.
  destruct work as [scope acc]; intro Hwf.
  pose proof (pre_rename_occurrence_acc_wf EB EBE EE EU a e scope acc Hwf) as Hobserved.
  unfold pre_rename_instruction.
  destruct (pre_rename_occurrence EB EE EU a e (scope, acc)) as [[frames output] fresh].
  cbn [fst snd] in Hobserved.
  assert (Haltered : pre_rename_acc_wf EB EBE EE EU (snd
    (fold_left (pre_rename_alter EB EU a e)
      (FinSet.elements (pre_group_lookup EE alterations e)) (frames, output)))).
  { apply (pre_fold_invariant _ (fun work => pre_rename_acc_wf EB EBE EE EU (snd work))).
    - intros current u Hcurrent; apply pre_rename_alter_acc_wf; exact Hcurrent.
    - exact Hobserved. }
  destruct (fold_left (pre_rename_alter EB EU a e)
    (FinSet.elements (pre_group_lookup EE alterations e)) (frames, output)) as [altered result].
  cbn [snd] in Haltered |- *; apply pre_rename_exit_acc_wf; exact Haltered.
Qed.

Local Lemma pre_rename_argument_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) scope acc argument :
  pre_rename_acc_wf EB EBE EE EU acc ->
  pre_rename_acc_wf EB EBE EE EU (pre_rename_argument EB EBE EU a scope acc argument).
Proof.
  intro Hwf; destruct argument as [be u]; unfold pre_rename_argument.
  destruct (pre_phi_translate a be u) as [v|]; [|exact Hwf].
  destruct (pre_rename_top EU scope v) as [operand available].
  destruct Hwf as [Hocc [Hfresh [Hlinks Hunsafe]]].
  cbn [pre_rename_acc_wf pre_rename_occurrences pre_rename_fresh pre_rename_links
    pre_rename_unsafe];
    repeat split; try assumption; apply Map.wf_set; exact Hlinks.
Qed.

Local Lemma pre_rename_block_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) alterations exits phis arguments owner scope acc :
  pre_rename_acc_wf EB EBE EE EU acc ->
  pre_rename_acc_wf EB EBE EE EU (snd (pre_rename_block EB EBE EN EE EU a alterations exits phis
    arguments owner scope acc)).
Proof.
  intro Hwf.
  assert (Hentered : pre_rename_acc_wf EB EBE EE EU (snd
    (match points_in_block (pre_ssa_points a) owner with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end))).
  { destruct (points_in_block (pre_ssa_points a) owner); [exact Hwf|].
    apply pre_rename_exit_acc_wf; exact Hwf. }
  assert (Hbody : pre_rename_acc_wf EB EBE EE EU (snd (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis owner)
    (instruction_edges (pre_ssa_points a) owner)
    (match points_in_block (pre_ssa_points a) owner with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end)))).
  { apply (pre_fold_invariant _ (fun work => pre_rename_acc_wf EB EBE EE EU (snd work))).
    - intros current e Hcurrent; apply pre_rename_instruction_acc_wf; exact Hcurrent.
    - exact Hentered. }
  unfold pre_rename_block; destruct (fold_left
    (pre_rename_instruction EB EN EE EU a alterations exits phis owner)
    (instruction_edges (pre_ssa_points a) owner)
    (match points_in_block (pre_ssa_points a) owner with
     | [] => (scope, acc)
     | n :: _ => pre_rename_exit EB EN EU exits n (scope, acc)
     end)) as [frames output]; cbn [snd] in Hbody |- *.
  apply pre_fold_invariant.
  - intros result argument Hresult; apply pre_rename_argument_acc_wf; exact Hresult.
  - exact Hbody.
Qed.

Local Lemma pre_rename_step_acc_wf {S O B BE N E V K C U} (EB : encoding B)
    (EBE : encoding BE) (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) children alterations exits phis arguments work :
  pre_rename_acc_wf EB EBE EE EU (snd work) ->
  pre_rename_acc_wf EB EBE EE EU (snd
    (pre_rename_step EB EBE EN EE EU a children alterations exits phis arguments work)).
Proof.
  destruct work as [[[|[owner scope] rest] seen] acc]; intro Hwf; [exact Hwf|].
  unfold pre_rename_step; cbn [snd]; destruct (FinSet.mem EB owner seen); [exact Hwf|].
  pose proof (pre_rename_block_acc_wf EB EBE EN EE EU a alterations exits phis arguments
    owner scope acc Hwf) as Hblock.
  destruct (pre_rename_block EB EBE EN EE EU a alterations exits phis arguments owner scope acc);
    exact Hblock.
Qed.

Local Lemma pre_built_acc_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_rename_acc_wf EB EBE EE EU (snd (pre_built_final EB EBE EN EE EV EU a)).
Proof.
  apply (pre_walk_trace_invariant _ (fun work => pre_rename_acc_wf EB EBE EE EU (snd work))
    _ _ (pre_built_trace EB EBE EN EE EV EU a)).
  - intros work Hwf; unfold pre_walk_step; apply pre_rename_step_acc_wf; exact Hwf.
  - cbn [pre_built_initial snd pre_rename_acc_wf pre_rename_occurrences pre_rename_fresh
      pre_rename_links pre_rename_unsafe]; repeat split; apply Map.wf_empty.
Qed.

(** Every output index stores keys at canonical encoded positions, even on raw input. *)
Theorem build_frg_indexes_wf {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  let f := build_frg EB EBE EN EE EV EU a in
  Map.wf EE (frg_occurrence_index f) /\ FinSet.wf EE (frg_fresh_index f) /\
  FinSet.wf (pair_encoding EB EU) (frg_phi_index f) /\
  Map.wf (pair_encoding (pair_encoding EB EU) EBE) (frg_phi_operands f) /\
  FinSet.wf (pair_encoding EB EU) (frg_unsafe_seeds f).
Proof.
  cbn zeta; destruct (pre_built_acc_wf EB EBE EN EE EV EU a) as [Hocc [Hfresh [Hlinks Hunsafe]]].
  split; [exact Hocc|]; split; [exact Hfresh|]; split; [apply pre_build_phi_wf|]; auto.
Qed.

(** Canonical indexes enumerate distinct occurrence, fresh, phi, operand-link and unsafe keys. *)
Theorem build_frg_index_keys_nodup {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  let f := build_frg EB EBE EN EE EV EU a in
  NoDup (map fst (Map.elements (frg_occurrence_index f))) /\
  NoDup (FinSet.elements (frg_fresh_index f)) /\ NoDup (FinSet.elements (frg_phi_index f)) /\
  NoDup (map fst (Map.elements (frg_phi_operands f))) /\
  NoDup (FinSet.elements (frg_unsafe_seeds f)).
Proof.
  cbn zeta; destruct (build_frg_indexes_wf EB EBE EN EE EV EU a)
    as [Hocc [Hfresh [Hphi [Hlinks Hunsafe]]]]; repeat split.
  - exact (Map.elements_nodup EE _ Hocc).
  - exact (FinSet.elements_nodup EE _ Hfresh).
  - exact (FinSet.elements_nodup (pair_encoding EB EU) _ Hphi).
  - exact (Map.elements_nodup (pair_encoding (pair_encoding EB EU) EBE) _ Hlinks).
  - exact (FinSet.elements_nodup (pair_encoding EB EU) _ Hunsafe).
Qed.

(** Every selected incoming version, including the unavailable sentinel, is a graph node. *)
Theorem build_frg_operand_membership {S O B BE N E V K C U} (EB : encoding B) (EBE : encoding BE)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (EU : encoding U)
    (a : pre_expr_ssa S O B BE N E V K C U) :
  pre_expr_ssa_laws EV a ->
  ready EB (block_graph (pre_ssa_points a)) (prepare EB (block_graph (pre_ssa_points a))) ->
  ready EN (live_graph (point_model (pre_ssa_points a)))
    (prepare EN (live_graph (point_model (pre_ssa_points a)))) ->
  forall b u be op, Map.get (pair_encoding (pair_encoding EB EU) EBE) ((b, u), be)
    (frg_phi_operands (build_frg EB EBE EN EE EV EU a)) = Some op ->
  In (frg_operand_version op) (frg_versions (build_frg EB EBE EN EE EV EU a)).
Proof.
  intros Hlaw Hblocks Hpoints b u be op Hget.
  destruct (pre_built_links_sound EB EBE EN EE EV EU a Hlaw Hblocks Hpoints _ op Hget)
    as [Hdomain [v [pe [Htranslate [Hindex [Hexpr [Hselection [Hreal Hmember]]]]]]]].
  exact Hmember.
Qed.
