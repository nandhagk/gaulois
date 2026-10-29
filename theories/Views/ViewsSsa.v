(** * SSA views and sparse conditional systems

    SSA views connect value definitions and guarded control flow to concrete executions.
    For example, an executable incoming edge transfers its arguments to block parameters.
    Builds on: ViewsGraph, CollectionsEncoding, OrderLift and FixpointSystem. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph.
Import List.ListNotations.

(** A value is computed, received as a block parameter, or unconstrained. *)
Inductive definition (N V K : Type) : Type :=
  | Op (o : K) (args : list V)
  | Param (b : N) (i : nat)
  | Arbitrary.

Arguments Op {N V K}.
Arguments Param {N V K}.
Arguments Arbitrary {N V K}.

(** Guards test truth or equality with a concrete constant. *)
Inductive guard_kind (C : Type) : Type :=
  | GTrue
  | GFalse
  | GConst (c : C)
  | GNotConst (c : C).

Arguments GTrue {C}.
Arguments GFalse {C}.
Arguments GConst {C}.
Arguments GNotConst {C}.

(** A condition associates a guard with its SSA subject. *)
Record condition (V C : Type) : Type := Condition {
  subject : V;
  kind : guard_kind C
}.

Arguments Condition {V C}.
Arguments subject {V C}.
Arguments kind {V C}.

(** The view exposes the client's definitions, edge operands and current valuation. *)
Record ssa_view (S O N E V K C : Type) : Type := SsaView {
  base : graph_view S O N E;
  def : V -> definition N V K;
  home : V -> N;
  params : N -> list V;
  edge_args : E -> list V;
  edge_guard : E -> list (condition V C);
  val : S -> V -> option C;
  op_eval : K -> list C -> option C;
  truth : C -> bool
}.

Arguments SsaView {S O N E V K C}.
Arguments base {S O N E V K C}.
Arguments def {S O N E V K C}.
Arguments home {S O N E V K C}.
Arguments params {S O N E V K C}.
Arguments edge_args {S O N E V K C}.
Arguments edge_guard {S O N E V K C}.
Arguments val {S O N E V K C}.
Arguments op_eval {S O N E V K C}.
Arguments truth {S O N E V K C}.

(** Guard meanings require no equality decision on concrete values. *)
Definition holds_guard {C} (truth : C -> bool) (k : guard_kind C) (c : C) : Prop :=
  match k with
  | GTrue => truth c = true
  | GFalse => truth c = false
  | GConst c0 => c = c0
  | GNotConst c0 => c <> c0
  end.

(** A condition holds when its subject is defined and satisfies its guard. *)
Definition cond_holds {S O N E V K C} (sv : ssa_view S O N E V K C) (s : S)
    (cd : condition V C) : Prop :=
  exists c, val sv s (subject cd) = Some c /\ holds_guard (truth sv) (kind cd) c.

(** Operation guard subjects agree with their operands in the same state. *)
Definition guard_ops_consistent {S O N E V K C} (sv : ssa_view S O N E V K C)
    (s : S) (e : E) : Prop :=
  forall cd o args, In cd (edge_guard sv e) -> def sv (subject cd) = Op o args ->
    exists cs c, Forall2 (fun y d => val sv s y = Some d) args cs /\
      val sv s (subject cd) = Some c /\ op_eval sv o cs = Some c.

(** Concrete steps preserve a binding or provide its constructive definition origin. *)
Record ssa_view_laws {S O N E V K C} (m : semantics S O)
    (sv : ssa_view S O N E V K C) : Prop := {
  base_laws : graph_view_laws m (base sv);
  param_defs : forall x b i, def sv x = Param b i -> nth_error (params sv b) i = Some x;
  guards_ok : forall s l s' e, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> Forall (cond_holds sv s) (edge_guard sv e);
  guard_op_defined : forall s l s' e, reachable_state m s -> step m s l s' ->
    taken (base sv) s l s' e -> guard_ops_consistent sv s e;
  value_origin : forall s l s' x c, reachable_state m s -> step m s l s' ->
    val sv s' x = Some c -> val sv s x = Some c \/
    (exists o args cs, def sv x = Op o args /\
       Forall2 (fun y d => val sv s y = Some d) args cs /\ op_eval sv o cs = Some c) \/
    (exists e b i z, def sv x = Param b i /\ taken (base sv) s l s' e /\
       Graph.target (cfg (base sv)) e = b /\ nth_error (edge_args sv e) i = Some z /\
       val sv s z = Some c) \/ def sv x = Arbitrary
}.

Arguments base_laws {S O N E V K C m sv}.
Arguments param_defs {S O N E V K C m sv}.
Arguments guards_ok {S O N E V K C m sv}.
Arguments guard_op_defined {S O N E V K C m sv}.
Arguments value_origin {S O N E V K C m sv}.

(** Sparse domains provide value transfer and inverse guard transfer. *)
Record sparse_domain (A C K : Type) : Type := SparseDomain {
  fact_lat : lattice A;
  fact_conc : concretisation A C;
  top_fact : A;
  op_abs : K -> list A -> A;
  assume_value : guard_kind C -> A -> A;
  assume_args : K -> bool -> list A -> list A
}.

Arguments SparseDomain {A C K}.
Arguments fact_lat {A C K}.
Arguments fact_conc {A C K}.
Arguments top_fact {A C K}.
Arguments op_abs {A C K}.
Arguments assume_value {A C K}.
Arguments assume_args {A C K}.

(** Every sparse transfer preserves the concrete values to which it applies. *)
Record sparse_domain_laws {A C K} (D : sparse_domain A C K) (truth : C -> bool)
    (op_eval : K -> list C -> option C) : Prop := {
  dom_lattice : lattice_laws (fact_lat D);
  dom_conc : concretisation_laws (fact_lat D) (fact_conc D);
  fact_bot_empty : forall c, ~ gamma (fact_conc D) (bot (fact_lat D)) c;
  top_sound : forall c, gamma (fact_conc D) (top_fact D) c;
  op_sound : forall o fs cs c, Forall2 (gamma (fact_conc D)) fs cs ->
    op_eval o cs = Some c -> gamma (fact_conc D) (op_abs D o fs) c;
  assume_value_sound : forall k a c, gamma (fact_conc D) a c -> holds_guard truth k c ->
    gamma (fact_conc D) (assume_value D k a) c;
  assume_args_sound : forall o b fs cs c, Forall2 (gamma (fact_conc D)) fs cs ->
    op_eval o cs = Some c -> truth c = b ->
    Forall2 (gamma (fact_conc D)) (assume_args D o b fs) cs
}.

Arguments dom_lattice {A C K D truth op_eval}.
Arguments dom_conc {A C K D truth op_eval}.
Arguments fact_bot_empty {A C K D truth op_eval}.
Arguments top_sound {A C K D truth op_eval}.
Arguments op_sound {A C K D truth op_eval}.
Arguments assume_value_sound {A C K D truth op_eval}.
Arguments assume_args_sound {A C K D truth op_eval}.

(** Executability distinguishes the fresh unreachable bottom from reached facts. *)
Definition executable {A} (LB : lattice (lift_bot A)) (a : lift_bot A) : bool :=
  negb (leb LB a (bot LB)).

(** The sparse unknown space keeps values, edge occurrences and blocks distinct. *)
Inductive sparse_unknown (N E V : Type) : Type :=
  | UVal (x : V)
  | UEdge (e : E)
  | UBlock (b : N).

Arguments UVal {N E V}.
Arguments UEdge {N E V}.
Arguments UBlock {N E V}.

(** Unknown codes follow the sum of values, edges and blocks. *)
Definition sparse_unknown_encoding {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) : encoding (sparse_unknown N E V).
Proof.
  let ES := constr:(sum_encoding EV (sum_encoding EE EN)) in
  refine (Encoding _ (fun u => encode ES
    (match u with
    | UVal x => inl x
    | UEdge e => inr (inl e)
    | UBlock b => inr (inr b)
    end)) _).
  intros [x|e|b] [x'|e'|b'] Hcode;
    apply (encode_injective (sum_encoding EV (sum_encoding EE EN))) in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** A reached lower bound forces the upper lifted fact to be reached. *)
Lemma sparse_reached_upper {A} (L : lattice A) (a : A) (b : lift_bot A) :
  leb (lift_bot_lattice L) (Some a) b = true -> executable (lift_bot_lattice L) b = true.
Proof.
  destruct b as [b|]; cbn; [reflexivity|discriminate].
Qed.

(** Lifted concretisation moves along a post-solution bound. *)
Lemma sparse_gamma_upper {A C K} (D : sparse_domain A C K) truth eval a b c :
  sparse_domain_laws D truth eval -> leb (lift_bot_lattice (fact_lat D)) a b = true ->
  gamma (lift_bot_gamma (fact_conc D)) a c -> gamma (lift_bot_gamma (fact_conc D)) b c.
Proof.
  intro Hdomain; apply (gamma_monotone (option_gamma_laws _ _ (dom_conc Hdomain))).
Qed.

(** Rows seed entries, evaluate definitions and propagate edge and parameter facts. *)
Inductive sparse_constraint (N E V : Type) : Type :=
  | CBlockEntry (b : N)
  | CEntryFact (x : V)
  | COp (x : V)
  | CArbitrary (x : V)
  | CArg (e : E) (i : nat)
  | CEdge (e : E)
  | CBlock (e : E).

Arguments CBlockEntry {N E V}.
Arguments CEntryFact {N E V}.
Arguments COp {N E V}.
Arguments CArbitrary {N E V}.
Arguments CArg {N E V}.
Arguments CEdge {N E V}.
Arguments CBlock {N E V}.

(** Constraint codes retain the documented seven constructor tags. *)
Definition sparse_constraint_encoding {N E V} (EN : encoding N) (EE : encoding E)
    (EV : encoding V) : encoding (sparse_constraint N E V).
Proof.
  let ES := constr:(sum_encoding EN (sum_encoding EV (sum_encoding EV (sum_encoding EV
    (sum_encoding (pair_encoding EE nat_encoding) (sum_encoding EE EE)))))) in
  refine (Encoding _ (fun c => encode ES
    (match c with
    | CBlockEntry b => inl b
    | CEntryFact x => inr (inl x)
    | COp x => inr (inr (inl x))
    | CArbitrary x => inr (inr (inr (inl x)))
    | CArg e i => inr (inr (inr (inr (inl (e, i)))))
    | CEdge e => inr (inr (inr (inr (inr (inl e)))))
    | CBlock e => inr (inr (inr (inr (inr (inr e)))))
    end)) _).
  intros [b|x|x|x|e i|e|e] [b'|x'|x'|x'|e' i'|e'|e'] Hcode;
    apply (encode_injective (sum_encoding EN (sum_encoding EV (sum_encoding EV
      (sum_encoding EV (sum_encoding (pair_encoding EE nat_encoding)
        (sum_encoding EE EE))))))) in Hcode;
    inversion Hcode; reflexivity.
Defined.

(** A sparse problem supplies a finite value inventory and initial parameter facts. *)
Record sparse_problem (S O N E V K C A : Type) : Type := SparseProblem {
  view : ssa_view S O N E V K C;
  domain : sparse_domain A C K;
  sparse_values : list V;
  entry_fact : V -> A
}.

Arguments SparseProblem {S O N E V K C A}.
Arguments view {S O N E V K C A}.
Arguments domain {S O N E V K C A}.
Arguments sparse_values {S O N E V K C A}.
Arguments entry_fact {S O N E V K C A}.

(** * Shared refinement computation

    The generator and ViewsRefine share this implementation to avoid a dependency cycle.
    Operand lists are traversed together; selecting a repeated operand never rescans a list. *)

Module SsaRefinement.

Definition same {V} (EV : encoding V) (x y : V) : bool :=
  Pos.eqb (encode EV x) (encode EV y).

Lemma same_spec {V} (EV : encoding V) x y : same EV x y = true <-> x = y.
Proof.
  unfold same; rewrite Pos.eqb_eq; split; [apply encode_injective|congruence].
Qed.

(** Collecting lifted facts fails at the first unavailable operand. *)
Fixpoint collect {A} (fs : list (lift_bot A)) : option (list A) :=
  match fs with
  | [] => Some []
  | None :: _ => None
  | Some a :: rest => option_map (cons a) (collect rest)
  end.

(** The accumulated fact replaces every occurrence of the selected operand. *)
Fixpoint substitute {V A} (EV : encoding V) (z : V) (a : lift_bot A)
    (args : list V) (fs : list (lift_bot A)) : list (lift_bot A) * bool :=
  match args, fs with
  | y :: args', f :: fs' =>
    let '(rest, occurs) := substitute EV z a args' fs' in
    let here := same EV y z in
    ((if here then a else f) :: rest, here || occurs)
  | _, _ => ([], false)
  end.

(** Select the first refined occurrence, retaining the start fact when none exists. *)
Fixpoint select {V A} (EV : encoding V) (z : V) (args : list V) (fs : list A) (a : A) : A :=
  match args, fs with
  | y :: args', f :: fs' => if same EV y z then f else select EV z args' fs' a
  | _, _ => a
  end.

(** Only truth guards request inverse operation transfer. *)
Definition guard_truth {C} (k : guard_kind C) : option bool :=
  match k with
  | GTrue => Some true
  | GFalse => Some false
  | _ => None
  end.

Section Refinement.
Context {S O N E V K C A : Type} (EV : encoding V)
  (pr : sparse_problem S O N E V K C A).
Let sv := view pr.
Let D := domain pr.
Let X := sparse_unknown N E V.

Definition backprop (z : V) (a : A) (o : K) (b : bool) (args : list V)
    (fs : list (lift_bot A)) : lift_bot A :=
  let '(inputs, occurs) := substitute EV z (Some a) args fs in
  if occurs then
    match collect inputs with
    | Some facts => Some (select EV z args (assume_args D o b facts) a)
    | None => None
    end
  else Some a.

Definition one (sigma : X -> lift_bot A) (z : V) (cd : condition V C)
    (a0 : lift_bot A) : lift_bot A :=
  match a0, sigma (UVal (subject cd)) with
  | Some a, Some _ =>
    if same EV (subject cd) z then Some (assume_value D (kind cd) a)
    else match def sv (subject cd), guard_truth (kind cd) with
    | Op o args, Some b => backprop z a o b args (map (fun y => sigma (UVal y)) args)
    | _, _ => Some a
    end
  | _, _ => None
  end.

Fixpoint conditions (sigma : X -> lift_bot A) (cds : list (condition V C))
    (z : V) (a : lift_bot A) : lift_bot A :=
  match cds with
  | [] => a
  | cd :: rest => conditions sigma rest z (one sigma z cd a)
  end.

Definition fact (sigma : X -> lift_bot A) (e : E) (z : V) (a : lift_bot A) : lift_bot A :=
  conditions sigma (edge_guard sv e) z a.

Definition on_edge (sigma : X -> lift_bot A) (e : E) (z : V) : lift_bot A :=
  fact sigma e z (sigma (UVal z)).

Definition feasible (sigma : X -> lift_bot A) (e : E) : bool :=
  forallb (fun cd =>
    match on_edge sigma e (subject cd) with
    | Some a => negb (leb (fact_lat D) a (bot (fact_lat D)))
    | None => false
    end) (edge_guard sv e).

End Refinement.

Section RefinementQueries.
Context {S O N E V K C A : Type} (EV : encoding V)
  (pr : sparse_problem S O N E V K C A).
Let sv := view pr.
Let D := domain pr.
Let X := sparse_unknown N E V.
Let Q := Query.t X (lift_bot A).

Definition one_deps (cd : condition V C) : list X :=
  UVal (subject cd) ::
  match def sv (subject cd) with
  | Op _ args => map UVal args
  | _ => []
  end.

Definition one_query (z : V) (cd : condition V C) (a0 : lift_bot A)
    (k : lift_bot A -> Q) : Q :=
  match a0 with
  | None => k None
  | Some a => Query.Ask (UVal (subject cd)) (fun subject_fact =>
    match subject_fact with
    | None => k None
    | Some _ =>
      if same EV (subject cd) z then k (Some (assume_value D (kind cd) a))
      else match def sv (subject cd), guard_truth (kind cd) with
      | Op o args, Some b => ask_all (map UVal args) (fun fs => k (backprop EV pr z a o b args fs))
      | _, _ => k (Some a)
      end
    end)
  end.

Fixpoint conditions_query (cds : list (condition V C)) (z : V) (a : lift_bot A)
    (k : lift_bot A -> Q) : Q :=
  match cds with
  | [] => k a
  | cd :: rest => one_query z cd a (fun a' => conditions_query rest z a' k)
  end.

Definition refinement_deps (cds : list (condition V C)) : list X := flat_map one_deps cds.

Definition on_edge_query (e : E) (z : V) (k : lift_bot A -> Q) : Q :=
  Query.Ask (UVal z) (fun a => conditions_query (edge_guard sv e) z a k).

Fixpoint feasible_query (e : E) (cds : list (condition V C)) (k : bool -> Q) : Q :=
  match cds with
  | [] => k true
  | cd :: rest => on_edge_query e (subject cd) (fun a =>
    match a with
    | None => k false
    | Some f => if leb (fact_lat D) f (bot (fact_lat D)) then k false
      else feasible_query e rest k
    end)
  end.

Definition feasibility_deps (e : E) (cds : list (condition V C)) : list X :=
  flat_map (fun cd => UVal (subject cd) :: refinement_deps (edge_guard sv e)) cds.

Lemma one_query_eval sigma z cd a k :
  Query.eval (one_query z cd a k) sigma = Query.eval (k (one EV pr sigma z cd a)) sigma.
Proof.
  unfold one_query, one; fold sv D.
  destruct a as [a|]; cbn; [|reflexivity].
  destruct (sigma (UVal (subject cd))) as [f|]; cbn; [|reflexivity].
  destruct (same EV (subject cd) z); [reflexivity|].
  destruct (def sv (subject cd)) as [o args|b i|]; try reflexivity.
  destruct (guard_truth (kind cd)); [|reflexivity].
  rewrite (proj1 (proj2 (ask_all_spec sigma _ _))), map_map; reflexivity.
Qed.

Lemma conditions_query_eval sigma cds z a k :
  Query.eval (conditions_query cds z a k) sigma =
    Query.eval (k (conditions EV pr sigma cds z a)) sigma.
Proof.
  revert a; induction cds as [|cd cds IH]; intro a; cbn; [reflexivity|].
  rewrite one_query_eval; apply IH.
Qed.

Lemma on_edge_query_eval sigma e z k :
  Query.eval (on_edge_query e z k) sigma = Query.eval (k (on_edge EV pr sigma e z)) sigma.
Proof.
  cbn [on_edge_query Query.eval]; apply conditions_query_eval.
Qed.

Lemma feasible_query_eval sigma e cds k :
  Query.eval (feasible_query e cds k) sigma =
  Query.eval (k (forallb (fun cd =>
    match on_edge EV pr sigma e (subject cd) with
    | Some a => negb (leb (fact_lat D) a (bot (fact_lat D)))
    | None => false
    end) cds)) sigma.
Proof.
  induction cds as [|cd cds IH]; cbn [feasible_query forallb]; [reflexivity|].
  rewrite on_edge_query_eval.
  destruct (on_edge EV pr sigma e (subject cd)) as [a|]; [|reflexivity].
  destruct (leb _ _ _); cbn; [reflexivity|apply IH].
Qed.

End RefinementQueries.

(** A query summary bounds reads and rules out side contributions. *)
Definition bounded {X A} (q : Query.t X A) (sigma : X -> A) (rs : list X) : Prop :=
  incl (Query.reads q sigma) rs /\ Query.sides q sigma = [].

Lemma bounded_mono {X A} (q : Query.t X A) sigma rs rs' :
  bounded q sigma rs -> incl rs rs' -> bounded q sigma rs'.
Proof.
  intros [Hr Hs] Hin; split; [eapply incl_tran; eassumption|exact Hs].
Qed.

Lemma bounded_ret {X A} (a : A) sigma (rs : list X) : bounded (Query.Ret a) sigma rs.
Proof.
  split; [intros x Hx; contradiction|reflexivity].
Qed.

Lemma bounded_ask {X A} (x : X) (k : A -> Query.t X A) sigma rs :
  (forall a, bounded (k a) sigma rs) -> bounded (Query.Ask x k) sigma (x :: rs).
Proof.
  intro Hk; destruct (Hk (sigma x)) as [Hr Hs]; split; cbn; [|exact Hs].
  intros y [Heq|Hin]; [now left|right; apply Hr; exact Hin].
Qed.

Lemma bounded_all {X A} (xs : list X) (k : list A -> Query.t X A) sigma rs :
  (forall fs, bounded (k fs) sigma rs) -> bounded (ask_all xs k) sigma (xs ++ rs).
Proof.
  intro Hk; destruct (ask_all_spec sigma xs k) as [Hr [Hv Hs]].
  destruct (Hk (map sigma xs)) as [Hreads Hsides]; split.
  - rewrite Hr; apply incl_app; [apply incl_appl; apply incl_refl|].
    apply incl_appr; exact Hreads.
  - rewrite Hs; exact Hsides.
Qed.

Section QueryBounds.
Context {S O N E V K C A : Type} (EV : encoding V)
  (pr : sparse_problem S O N E V K C A).
Let sv := view pr.
Let X := sparse_unknown N E V.
Let Q := Query.t X (lift_bot A).
Context (sigma : X -> lift_bot A).

Lemma one_query_bounded z cd a (k : lift_bot A -> Q) rs :
  (forall f, bounded (k f) sigma rs) ->
  bounded (one_query EV pr z cd a k) sigma (one_deps pr cd ++ rs).
Proof.
  intro Hk; unfold one_query, one_deps; fold sv.
  destruct a as [a|].
  - apply bounded_ask; intros [f|].
    + destruct (same EV (subject cd) z).
      * eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
      * destruct (def sv (subject cd)) as [o args|b i|]; cbn.
        -- destruct (guard_truth (kind cd)).
           ++ apply bounded_all; intro fs; apply Hk.
           ++ eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
        -- apply Hk.
        -- apply Hk.
    + eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
  - eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
Qed.

Lemma conditions_query_bounded cds z a (k : lift_bot A -> Q) rs :
  (forall f, bounded (k f) sigma rs) ->
  bounded (conditions_query EV pr cds z a k) sigma (refinement_deps pr cds ++ rs).
Proof.
  intro Hk; revert a; induction cds as [|cd cds IH]; intro a; cbn [conditions_query].
  - apply Hk.
  - unfold refinement_deps in *; cbn [flat_map]; rewrite <- app_assoc.
    apply one_query_bounded; exact IH.
Qed.

Lemma on_edge_query_bounded e z (k : lift_bot A -> Q) rs :
  (forall f, bounded (k f) sigma rs) ->
  bounded (on_edge_query EV pr e z k) sigma
    (UVal z :: refinement_deps pr (edge_guard sv e) ++ rs).
Proof.
  intro Hk; apply bounded_ask; intro a; apply conditions_query_bounded; exact Hk.
Qed.

Lemma feasible_query_bounded e cds (k : bool -> Q) rs :
  (forall b, bounded (k b) sigma rs) ->
  bounded (feasible_query EV pr e cds k) sigma (feasibility_deps pr e cds ++ rs).
Proof.
  intro Hk; induction cds as [|cd cds IH]; cbn [feasible_query].
  - apply Hk.
  - unfold feasibility_deps in *; cbn [flat_map]; rewrite <- app_assoc; cbn [app].
    apply on_edge_query_bounded; intros [f|].
    + destruct (leb _ _ _); [|exact IH].
      eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
    + eapply bounded_mono; [apply Hk|apply incl_appr; apply incl_refl].
Qed.

End QueryBounds.

Lemma collect_sound {A C} (G : concretisation A C) fs cs :
  Forall2 (gamma (lift_bot_gamma G)) fs cs ->
  exists facts, collect fs = Some facts /\ Forall2 (gamma G) facts cs.
Proof.
  intro Hfacts; induction Hfacts as [|f c fs cs Hf Hfacts [facts [Hcollect Hsound]]].
  - exists []; split; [reflexivity|constructor].
  - destruct f as [a|]; [|contradiction].
    exists (a :: facts); cbn; rewrite Hcollect; split; [reflexivity|constructor; assumption].
Qed.

Section RefinementSound.
Context {S O N E V K C A : Type} (EV : encoding V)
  (pr : sparse_problem S O N E V K C A).
Let sv := view pr.
Let D := domain pr.
Let X := sparse_unknown N E V.
Context (sigma : X -> lift_bot A) (s : S) (z : V) (c : C).
Hypothesis Hdomain : sparse_domain_laws D (truth sv) (op_eval sv).
Hypothesis Hfacts : forall x d, val sv s x = Some d ->
  gamma (lift_bot_gamma (fact_conc D)) (sigma (UVal x)) d.
Hypothesis Hz : val sv s z = Some c.

Lemma substituted_sound args cs a :
  Forall2 (fun y d => val sv s y = Some d) args cs ->
  gamma (fact_conc D) a c ->
  Forall2 (gamma (lift_bot_gamma (fact_conc D)))
    (fst (substitute EV z (Some a) args (map (fun y => sigma (UVal y)) args))) cs.
Proof.
  intros Hargs Ha; induction Hargs as [|y d args cs Hy Hargs IH].
  - constructor.
  - cbn [map substitute].
    destruct (substitute EV z (Some a) args (map (fun y => sigma (UVal y)) args))
      as [inputs occurs]; cbn in IH |- *.
    constructor; [|exact IH].
    destruct (same EV y z) eqn:Heq.
    + apply same_spec in Heq; subst y; rewrite Hz in Hy; injection Hy as Hvalue; subst d.
      exact Ha.
    + apply Hfacts; exact Hy.
Qed.

Lemma selected_sound args cs fs a :
  Forall2 (fun y d => val sv s y = Some d) args cs ->
  Forall2 (gamma (fact_conc D)) fs cs -> gamma (fact_conc D) a c ->
  gamma (fact_conc D) (select EV z args fs a) c.
Proof.
  intro Hargs; revert fs; induction Hargs as [|y d args cs Hy Hargs IH];
    intros fs Hfs Ha; inversion Hfs as [|f d' fs' cs' Hf Hrest]; subst; cbn.
  - exact Ha.
  - destruct (same EV y z) eqn:Heq.
    + apply same_spec in Heq; subst y; rewrite Hz in Hy; injection Hy as Hvalue; subst d.
      exact Hf.
    + apply IH; assumption.
Qed.

Lemma backprop_sound a o b args cs d :
  gamma (fact_conc D) a c -> Forall2 (fun y v => val sv s y = Some v) args cs ->
  op_eval sv o cs = Some d -> truth sv d = b ->
  gamma (lift_bot_gamma (fact_conc D))
    (backprop EV pr z a o b args (map (fun y => sigma (UVal y)) args)) c.
Proof.
  intros Ha Hargs Hop Htruth.
  pose proof (substituted_sound _ _ _ Hargs Ha) as Hinputs.
  unfold backprop.
  destruct (substitute EV z (Some a) args (map (fun y => sigma (UVal y)) args))
    as [inputs occurs]; cbn in Hinputs.
  destruct occurs; [|exact Ha].
  destruct (collect_sound (fact_conc D) _ _ Hinputs) as [fs [Hcollect Hfs]].
  rewrite Hcollect; cbn.
  eapply selected_sound; [exact Hargs| |exact Ha].
  eapply (assume_args_sound Hdomain); eassumption.
Qed.

Lemma one_sound cd a :
  cond_holds sv s cd ->
  (forall o args, def sv (subject cd) = Op o args ->
    exists cs d, Forall2 (fun y v => val sv s y = Some v) args cs /\
      val sv s (subject cd) = Some d /\ op_eval sv o cs = Some d) ->
  gamma (lift_bot_gamma (fact_conc D)) a c ->
  gamma (lift_bot_gamma (fact_conc D)) (one EV pr sigma z cd a) c.
Proof.
  intros [d [Hy Hguard]] Hops Ha.
  pose proof (Hfacts _ _ Hy) as Hsubject.
  destruct a as [a|]; [|contradiction].
  unfold one; fold sv D; destruct (sigma (UVal (subject cd))) as [f|] eqn:Hget;
    [|contradiction].
  destruct (same EV (subject cd) z) eqn:Heq.
  - apply same_spec in Heq; rewrite Heq, Hz in Hy; injection Hy as Hvalue; subst d.
    apply (assume_value_sound Hdomain); assumption.
  - destruct (def sv (subject cd)) as [o args|b i|] eqn:Hdef; try exact Ha.
    destruct (guard_truth (kind cd)) as [b|] eqn:Htruth; [|exact Ha].
    destruct (Hops _ _ eq_refl) as [cs [d' [Hargs [Hy' Hop]]]].
    rewrite Hy in Hy'; injection Hy' as Hvalue; subst d'.
    eapply backprop_sound; [exact Ha|exact Hargs|exact Hop|].
    destruct (kind cd); cbn in Htruth, Hguard; inversion Htruth; exact Hguard.
Qed.

Lemma conditions_sound cds e a :
  Forall (cond_holds sv s) cds ->
  incl cds (edge_guard sv e) -> guard_ops_consistent sv s e ->
  gamma (lift_bot_gamma (fact_conc D)) a c ->
  gamma (lift_bot_gamma (fact_conc D)) (conditions EV pr sigma cds z a) c.
Proof.
  intro Hguards; revert a; induction Hguards as [|cd cds Hcd Hguards IH];
    intros a Hin Hops Ha; cbn.
  - exact Ha.
  - apply IH; [intros q Hq; apply Hin; now right|exact Hops|].
    apply one_sound; [exact Hcd| |exact Ha].
    intros o args Hdef; apply (Hops cd o args); [apply Hin; now left|exact Hdef].
Qed.

(** Shared refinement preserves the supplied fact under the documented local premises. *)
Lemma fact_sound e a :
  Forall (cond_holds sv s) (edge_guard sv e) -> guard_ops_consistent sv s e ->
  gamma (lift_bot_gamma (fact_conc D)) a c ->
  gamma (lift_bot_gamma (fact_conc D)) (fact EV pr sigma e z a) c.
Proof.
  intros Hguards Hops Ha; apply (conditions_sound _ e); try assumption; apply incl_refl.
Qed.

End RefinementSound.

(** A concretely inhabited fact cannot be below the domain's empty bottom. *)
Lemma inhabited_not_bottom {A C K} (D : sparse_domain A C K) truth eval a c :
  sparse_domain_laws D truth eval -> gamma (fact_conc D) a c ->
  negb (leb (fact_lat D) a (bot (fact_lat D))) = true.
Proof.
  intros Hdomain Hc; apply negb_true_iff; destruct (leb _ _ _) eqn:Hle; [|reflexivity].
  exfalso; apply (fact_bot_empty Hdomain c).
  eapply (gamma_monotone (dom_conc Hdomain)); eassumption.
Qed.

(** Taken edges pass the shared feasibility test whenever the current facts are sound. *)
Lemma feasible_sound {S O N E V K C A} (EV : encoding V) (m : semantics S O)
    (pr : sparse_problem S O N E V K C A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  forall s l s' e, reachable_state m s -> step m s l s' -> taken (base (view pr)) s l s' e ->
  (forall x d, val (view pr) s x = Some d ->
    gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  feasible EV pr sigma e = true.
Proof.
  intros Hview Hdomain s l s' e Hreachable Hstep Htaken Hfacts.
  pose proof (guards_ok Hview _ _ _ _ Hreachable Hstep Htaken) as Hguards.
  pose proof (guard_op_defined Hview _ _ _ _ Hreachable Hstep Htaken) as Hops.
  unfold feasible; apply forallb_forall; intros cd Hcd.
  pose proof (proj1 (Forall_forall _ _) Hguards cd Hcd) as [c [Hval Hguard]].
  pose proof (fact_sound EV pr sigma s (subject cd) c Hdomain Hfacts Hval e
    (sigma (UVal (subject cd))) Hguards Hops (Hfacts _ _ Hval)) as Hrefined.
  unfold on_edge; destruct (fact EV pr sigma e (subject cd) (sigma (UVal (subject cd))))
    as [a|]; [|contradiction].
  exact (inhabited_not_bottom _ _ _ _ _ Hdomain Hrefined).
Qed.

End SsaRefinement.
Import SsaRefinement.

(** * Sparse constraint generation *)

Module SsaSystem.

Section Generator.
Context {S O N E V K C A : Type} (EN : encoding N) (EV : encoding V)
  (pr : sparse_problem S O N E V K C A).
Let sv := view pr.
Let D := domain pr.
Let g := cfg (base sv).
Let X := sparse_unknown N E V.
Let Row := sparse_constraint N E V.
Let Q := Query.t X (lift_bot A).

Definition value_rows (entries : FinSet.t N) (x : V) : list Row :=
  match def sv x with
  | Op _ _ => [COp x]
  | Param b _ => if FinSet.mem EN b entries then [CEntryFact x] else []
  | Arbitrary => [CArbitrary x]
  end.

Definition edge_rows (e : E) : list Row :=
  CEdge e :: CBlock e :: map (CArg e) (seq 0 (length (edge_args sv e))).

Definition rows : list Row :=
  let entries := FinSet.of_list EN (Graph.entries g) in
  map CBlockEntry (Graph.entries g) ++
    flat_map (value_rows entries) (sparse_values pr) ++ flat_map edge_rows (edges_of g).

Definition target (r : Row) : X :=
  match r with
  | CBlockEntry b => UBlock b
  | CEntryFact x | COp x | CArbitrary x => UVal x
  | CArg e i =>
    match nth_error (params sv (Graph.target g e)) i with
    | Some y => UVal y
    | None => UEdge e
    end
  | CEdge e => UEdge e
  | CBlock e => UBlock (Graph.target g e)
  end.

Definition op_query (x : V) : Q :=
  match def sv x with
  | Op o args => ask_all (map UVal args) (fun fs => Query.Ret
    (option_map (op_abs D o) (collect fs)))
  | _ => Query.Ret None
  end.

Definition arg_query (e : E) (i : nat) : Q :=
  match nth_error (params sv (Graph.target g e)) i, nth_error (edge_args sv e) i with
  | Some _, Some z => Query.Ask (UEdge e) (fun a =>
    if executable (lift_bot_lattice (fact_lat D)) a
    then on_edge_query EV pr e z Query.Ret else Query.Ret None)
  | _, _ => Query.Ret None
  end.

Definition edge_query (e : E) : Q :=
  Query.Ask (UBlock (Graph.source g e)) (fun a =>
    if executable (lift_bot_lattice (fact_lat D)) a
    then feasible_query EV pr e (edge_guard sv e)
      (fun b => Query.Ret (if b then Some (top_fact D) else None))
    else Query.Ret None).

Definition rhs (r : Row) : Q :=
  match r with
  | CBlockEntry _ | CArbitrary _ => Query.Ret (Some (top_fact D))
  | CEntryFact x => Query.Ret (Some (entry_fact pr x))
  | COp x => op_query x
  | CArg e i => arg_query e i
  | CEdge e => edge_query e
  | CBlock e => Query.Ask (UEdge e) Query.Ret
  end.

Definition row_deps (r : Row) : list X :=
  match r with
  | COp x =>
    match def sv x with
    | Op _ args => map UVal args
    | _ => []
    end
  | CArg e i =>
    match nth_error (params sv (Graph.target g e)) i, nth_error (edge_args sv e) i with
    | Some _, Some z => UEdge e :: UVal z :: refinement_deps pr (edge_guard sv e)
    | _, _ => []
    end
  | CEdge e => UBlock (Graph.source g e) :: feasibility_deps pr e (edge_guard sv e)
  | CBlock e => [UEdge e]
  | _ => []
  end.

Lemma rhs_bounded r sigma : bounded (rhs r) sigma (row_deps r).
Proof.
  destruct r as [b|x|x|x|e i|e|e]; cbn [rhs row_deps]; try apply bounded_ret.
  - unfold op_query; destruct (def sv x) as [o args|b i|]; try apply bounded_ret.
    eapply bounded_mono with (rs := map UVal args ++ []).
    + apply bounded_all; intro fs; apply bounded_ret.
    + rewrite app_nil_r; apply incl_refl.
  - unfold arg_query; destruct (nth_error (params sv (Graph.target g e)) i);
      [|apply bounded_ret].
    destruct (nth_error (edge_args sv e) i) as [z|]; [|apply bounded_ret].
    apply bounded_ask; intro a; destruct (executable _ a); [|apply bounded_ret].
    eapply bounded_mono with
      (rs := UVal z :: refinement_deps pr (edge_guard sv e) ++ []).
    + apply on_edge_query_bounded; intro f; apply bounded_ret.
    + rewrite app_nil_r; apply incl_refl.
  - unfold edge_query; apply bounded_ask; intro a; destruct (executable _ a);
      [|apply bounded_ret].
    eapply bounded_mono with (rs := feasibility_deps pr e (edge_guard sv e) ++ []).
    + apply feasible_query_bounded; intro b; apply bounded_ret.
    + rewrite app_nil_r; apply incl_refl.
  - apply bounded_ask; intro a; apply bounded_ret.
Qed.

Lemma entry_row b : In b (Graph.entries g) -> In (CBlockEntry b) rows.
Proof.
  intro Hb; unfold rows; apply in_or_app; left; apply in_map; exact Hb.
Qed.

Lemma value_row x r : In x (sparse_values pr) ->
  In r (value_rows (FinSet.of_list EN (Graph.entries g)) x) -> In r rows.
Proof.
  intros Hx Hr; unfold rows; apply in_or_app; right; apply in_or_app; left.
  apply in_flat_map; exists x; split; assumption.
Qed.

Lemma edge_row e r : In e (edges_of g) -> In r (edge_rows e) -> In r rows.
Proof.
  intros He Hr; unfold rows; apply in_or_app; right; apply in_or_app; right.
  apply in_flat_map; exists e; split; assumption.
Qed.

End Generator.

End SsaSystem.
Import SsaSystem.

(** The sparse generator shares one lifted carrier across blocks, edges and values. *)
Definition sparse_system {S O N E V K C A} (EN : encoding N) (EV : encoding V)
    (pr : sparse_problem S O N E V K C A) :
    System.t (sparse_unknown N E V) (sparse_constraint N E V) (lift_bot A) :=
  {| System.constraints := SsaSystem.rows EN pr;
     System.target := SsaSystem.target pr;
     System.rhs := SsaSystem.rhs EV pr |}.

(** Static dependencies bound every query read, and sparse queries emit no sides. *)
Definition sparse_static {S O N E V K C A} (EN : encoding N) (EV : encoding V)
    (pr : sparse_problem S O N E V K C A) : System.static (sparse_system EN EV pr).
Proof.
  refine {| System.deps := SsaSystem.row_deps pr; System.side_targets := fun _ => [] |}.
  - intros r sigma; apply (proj1 (rhs_bounded EV pr r sigma)).
  - intros r sigma; cbn; rewrite (proj2 (rhs_bounded EV pr r sigma)); apply incl_refl.
Defined.

(** * The simultaneous block and value invariant *)

Section SparseSoundness.
Context {S O N E V K C A : Type} (EN : encoding N) (EV : encoding V)
  (m : semantics S O) (pr : sparse_problem S O N E V K C A)
  (sigma : sparse_unknown N E V -> lift_bot A).
Let sv := view pr.
Let D := domain pr.
Let g := cfg (base sv).
Let LB := lift_bot_lattice (fact_lat D).
Let G := lift_bot_gamma (fact_conc D).
Hypothesis Hview : ssa_view_laws m sv.
Hypothesis Hdomain : sparse_domain_laws D (truth sv) (op_eval sv).
Hypothesis Hcoverage : forall s x c, reachable_state m s -> val sv s x = Some c ->
  In x (sparse_values pr).
Hypothesis Hinitial : forall s x c, initial m s -> val sv s x = Some c ->
  exists b i, def sv x = Param b i /\ In b (Graph.entries g) /\
    gamma (fact_conc D) (entry_fact pr x) c.
Hypothesis Hpost : post_solution LB (sparse_system EN EV pr) sigma.

Definition sparse_values_sound (s : S) : Prop :=
  forall x c, val sv s x = Some c -> gamma G (sigma (UVal x)) c.

Definition sparse_invariant (s : S) : Prop :=
  executable LB (sigma (UBlock (point (base sv) s))) = true /\ sparse_values_sound s.

Lemma sparse_row_bound r : In r (SsaSystem.rows EN pr) ->
  leb LB (Query.eval (SsaSystem.rhs EV pr r) sigma) (sigma (SsaSystem.target pr r)) = true.
Proof.
  intro Hr; exact (proj1 (Hpost r Hr)).
Qed.

Lemma sparse_entry_block s : initial m s ->
  executable LB (sigma (UBlock (point (base sv) s))) = true.
Proof.
  intro Hs; apply sparse_reached_upper with (a := top_fact D).
  apply (sparse_row_bound (CBlockEntry (point (base sv) s))).
  apply entry_row; apply (entry_points (base_laws Hview)); exact Hs.
Qed.

Lemma sparse_initial_value s x c : initial m s -> val sv s x = Some c ->
  gamma G (sigma (UVal x)) c.
Proof.
  intros Hs Hval; destruct (Hinitial _ _ _ Hs Hval) as [b [i [Hdef [Hb Hfact]]]].
  assert (Hreachable : reachable_state m s).
  { exists s, []; split; [exact Hs|constructor]. }
  assert (Hr : In (CEntryFact x) (SsaSystem.rows EN pr)).
  { apply value_row with (x := x); [eapply Hcoverage; eassumption|].
    unfold value_rows; fold sv g; rewrite Hdef.
    rewrite (proj2 (FinSet.of_list_spec EN b (Graph.entries g)) Hb); now left. }
  eapply (sparse_gamma_upper D _ _ _ _ c Hdomain).
  - exact (sparse_row_bound _ Hr).
  - exact Hfact.
Qed.

Lemma sparse_initial_invariant s : initial m s -> sparse_invariant s.
Proof.
  intro Hs; split; [apply sparse_entry_block; exact Hs|].
  intros x c Hval; eapply sparse_initial_value; eassumption.
Qed.

Lemma sparse_argument_facts s args cs : sparse_values_sound s ->
  Forall2 (fun y d => val sv s y = Some d) args cs ->
  Forall2 (gamma G) (map (fun y => sigma (UVal y)) args) cs.
Proof.
  intros Hfacts Hargs; induction Hargs as [|y d args cs Hy Hargs IH]; cbn.
  - constructor.
  - constructor; [apply Hfacts; exact Hy|exact IH].
Qed.

Lemma sparse_operation_value s x c o args cs :
  In x (sparse_values pr) -> sparse_values_sound s -> def sv x = Op o args ->
  Forall2 (fun y d => val sv s y = Some d) args cs -> op_eval sv o cs = Some c ->
  gamma G (sigma (UVal x)) c.
Proof.
  intros Hx Hfacts Hdef Hargs Hop.
  assert (Hr : In (COp x) (SsaSystem.rows EN pr)).
  { apply value_row with (x := x); [exact Hx|].
    unfold value_rows; fold sv; rewrite Hdef; now left. }
  pose proof (sparse_row_bound _ Hr) as Hbound.
  cbn [SsaSystem.rhs SsaSystem.target] in Hbound.
  unfold op_query in Hbound; fold sv D in Hbound; rewrite Hdef in Hbound.
  rewrite (proj1 (proj2 (ask_all_spec sigma _ _))), map_map in Hbound.
  destruct (collect_sound (fact_conc D) _ _ (sparse_argument_facts _ _ _ Hfacts Hargs))
    as [fs [Hcollect Hfs]].
  cbn [Query.eval] in Hbound; rewrite Hcollect in Hbound; cbn [option_map] in Hbound.
  eapply (sparse_gamma_upper D _ _ _ _ c Hdomain); [exact Hbound|].
  eapply (op_sound Hdomain); eassumption.
Qed.

Lemma sparse_arbitrary_value x c : In x (sparse_values pr) -> def sv x = Arbitrary ->
  gamma G (sigma (UVal x)) c.
Proof.
  intros Hx Hdef.
  eapply (sparse_gamma_upper D _ _ (Some (top_fact D)) _ c Hdomain).
  - apply (sparse_row_bound (CArbitrary x)); apply value_row with (x := x); [exact Hx|].
    unfold value_rows; fold sv; rewrite Hdef; now left.
  - apply (top_sound Hdomain).
Qed.

Lemma sparse_taken_edge s l s' e :
  reachable_state m s -> step m s l s' -> taken (base sv) s l s' e ->
  sparse_invariant s -> executable LB (sigma (UEdge e)) = true.
Proof.
  intros Hreachable Hstep Htaken [Hblock Hfacts].
  destruct (view_taken_edge m (base sv) _ _ _ _ (base_laws Hview)
    Hreachable Hstep Htaken) as [He [Hsource Htarget]].
  fold g in Hsource, Htarget.
  assert (Hr : In (CEdge e) (SsaSystem.rows EN pr)).
  { apply edge_row with (e := e); [exact He|now left]. }
  pose proof (sparse_row_bound _ Hr) as Hbound.
  cbn [SsaSystem.rhs SsaSystem.target edge_query Query.eval] in Hbound.
  fold sv D g LB in Hbound; rewrite Hsource, Hblock in Hbound.
  rewrite feasible_query_eval in Hbound.
  change (leb LB (if feasible EV pr sigma e then Some (top_fact D) else None)
    (sigma (UEdge e)) = true) in Hbound.
  rewrite (feasible_sound EV m pr sigma Hview Hdomain _ _ _ _ Hreachable Hstep Htaken Hfacts)
    in Hbound.
  apply sparse_reached_upper with (a := top_fact D); exact Hbound.
Qed.

Lemma sparse_parameter_value s l s' x c e b i z :
  reachable_state m s -> step m s l s' -> sparse_invariant s ->
  def sv x = Param b i -> taken (base sv) s l s' e -> Graph.target g e = b ->
  nth_error (edge_args sv e) i = Some z -> val sv s z = Some c ->
  gamma G (sigma (UVal x)) c.
Proof.
  intros Hreachable Hstep Hinv Hdef Htaken Htarget Harg Hval.
  pose proof (sparse_taken_edge _ _ _ _ Hreachable Hstep Htaken Hinv) as Hexec.
  destruct (view_taken_edge m (base sv) _ _ _ _ (base_laws Hview)
    Hreachable Hstep Htaken) as [He Hends].
  assert (Hparam : nth_error (params sv (Graph.target g e)) i = Some x).
  { rewrite Htarget; apply (param_defs Hview _ _ _ Hdef). }
  assert (Hr : In (CArg e i) (SsaSystem.rows EN pr)).
  { apply edge_row with (e := e); [exact He|right; right; apply in_map; apply in_seq; split].
    - apply Nat.le_0_l.
    - change (i < length (edge_args sv e)).
      apply (proj1 (nth_error_Some _ _)); rewrite Harg; discriminate. }
  pose proof (sparse_row_bound _ Hr) as Hbound.
  cbn [SsaSystem.rhs SsaSystem.target] in Hbound; unfold arg_query in Hbound.
  fold sv g LB in Hbound; rewrite Hparam, Harg in Hbound.
  change (leb LB (Query.eval (if executable LB (sigma (UEdge e))
    then on_edge_query EV pr e z Query.Ret else Query.Ret None) sigma)
    (sigma (UVal x)) = true) in Hbound.
  rewrite Hexec, on_edge_query_eval in Hbound.
  eapply (sparse_gamma_upper D _ _ _ _ c Hdomain); [exact Hbound|].
  unfold on_edge; eapply fact_sound; [exact Hdomain|exact (proj2 Hinv)|exact Hval| | |].
  - eapply (guards_ok Hview); eassumption.
  - eapply (guard_op_defined Hview); eassumption.
  - apply (proj2 Hinv); exact Hval.
Qed.

Lemma sparse_successor_block s l s' :
  reachable_state m s -> step m s l s' -> sparse_invariant s ->
  executable LB (sigma (UBlock (point (base sv) s'))) = true.
Proof.
  intros Hreachable Hstep Hinv.
  destruct (edge_covers (base_laws Hview) _ _ _ Hreachable Hstep) as [Hstay|[e Htaken]].
  - rewrite (stays_point (base_laws Hview) _ _ _ Hreachable Hstep Hstay); exact (proj1 Hinv).
  - destruct (view_taken_edge m (base sv) _ _ _ _ (base_laws Hview)
      Hreachable Hstep Htaken) as [He [Hsource Htarget]].
    fold g in Hsource, Htarget.
    pose proof (sparse_taken_edge _ _ _ _ Hreachable Hstep Htaken Hinv) as Hexec.
    assert (Hr : In (CBlock e) (SsaSystem.rows EN pr)).
    { apply edge_row with (e := e); [exact He|right; now left]. }
    pose proof (sparse_row_bound _ Hr) as Hbound.
    change (leb LB (sigma (UEdge e)) (sigma (UBlock (Graph.target g e))) = true) in Hbound.
    rewrite <- Htarget; destruct (sigma (UEdge e)) as [a|]; [|discriminate].
    apply sparse_reached_upper with (a := a); exact Hbound.
Qed.

Lemma sparse_successor_values s l s' :
  reachable_state m s -> step m s l s' -> sparse_invariant s -> sparse_values_sound s'.
Proof.
  intros Hreachable Hstep Hinv x c Hval.
  assert (Hx : In x (sparse_values pr)).
  { eapply Hcoverage; [eapply reachable_state_step; eassumption|exact Hval]. }
  destruct (value_origin Hview _ _ _ _ _ Hreachable Hstep Hval) as [Hsame|Horigin].
  - apply (proj2 Hinv); exact Hsame.
  - destruct Horigin as [[o [args [cs [Hdef [Hargs Hop]]]]]|Horigin].
    + eapply sparse_operation_value; [exact Hx|exact (proj2 Hinv)|eassumption|eassumption|].
      exact Hop.
    + destruct Horigin as [[e [b [i [z [Hdef [Htaken [Htarget [Harg Hz]]]]]]]]|Harbitrary].
      * eapply sparse_parameter_value; eassumption.
      * eapply sparse_arbitrary_value; eassumption.
Qed.

Lemma sparse_invariant_step s l s' :
  reachable_state m s -> step m s l s' -> sparse_invariant s -> sparse_invariant s'.
Proof.
  intros Hreachable Hstep Hinv; split.
  - eapply sparse_successor_block; eassumption.
  - eapply sparse_successor_values; eassumption.
Qed.

Lemma sparse_reachable_invariant s : reachable_state m s -> sparse_invariant s.
Proof.
  intros [s0 [tr [Hstart Hrun]]].
  assert (Hreachable : reachable_state m s0).
  { exists s0, []; split; [exact Hstart|constructor]. }
  pose proof (sparse_initial_invariant s0 Hstart) as Hinv.
  clear Hstart.
  revert Hreachable Hinv; induction Hrun as [s|s l s' tr t Hstep Hrun IH];
    intros Hreachable Hinv; [exact Hinv|].
  apply IH.
  - eapply reachable_state_step; eassumption.
  - eapply sparse_invariant_step; eassumption.
Qed.

End SparseSoundness.

(** Every reachable block, taken edge and present value is covered by a sparse post-solution. *)
Theorem sparse_sound {S O N E V K C A} (EN : encoding N) (EV : encoding V)
    (m : semantics S O) (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  (forall s x c, reachable_state m s -> val (view pr) s x = Some c -> In x (sparse_values pr)) ->
  (forall s x c, initial m s -> val (view pr) s x = Some c ->
    exists b i, def (view pr) x = Param b i /\ In b (Graph.entries (cfg (base (view pr)))) /\
      gamma (fact_conc (domain pr)) (entry_fact pr x) c) ->
  post_solution (lift_bot_lattice (fact_lat (domain pr))) (sparse_system EN EV pr) sigma ->
  (forall s, reachable_state m s ->
    executable (lift_bot_lattice (fact_lat (domain pr)))
      (sigma (UBlock (point (base (view pr)) s))) = true) /\
  (forall s l s' e, reachable_state m s -> step m s l s' -> taken (base (view pr)) s l s' e ->
    executable (lift_bot_lattice (fact_lat (domain pr))) (sigma (UEdge e)) = true) /\
  (forall s x c, reachable_state m s -> val (view pr) s x = Some c ->
    gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) c).
Proof.
  intros Hview Hdomain Hcoverage Hinitial Hpost.
  pose proof (sparse_reachable_invariant EN EV m pr sigma Hview Hdomain
    Hcoverage Hinitial Hpost) as Hsound.
  split; [intros s Hs; exact (proj1 (Hsound s Hs))|split].
  - intros s l s' e Hs Hstep Htaken.
    eapply sparse_taken_edge; [exact Hview|exact Hdomain|exact Hpost|exact Hs|
      exact Hstep|exact Htaken|exact (Hsound s Hs)].
  - intros s x c Hs Hval; exact (proj2 (Hsound s Hs) x c Hval).
Qed.
