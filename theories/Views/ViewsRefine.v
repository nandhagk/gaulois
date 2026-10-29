(** * Guard and edge operand refinement

    Refinement folds edge conditions over a value fact and checks edge feasibility.
    For example, a true comparison refines an operand through the domain's inverse transfer.
    Builds on: ViewsSsa and OrderLift. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderConcrete OrderLift.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa.

(** Refine a supplied start fact by each edge guard in order. *)
Definition refine_fact {S O N E V K C A} (EV : encoding V)
    (pr : sparse_problem S O N E V K C A) (s : sparse_unknown N E V -> lift_bot A)
    (e : E) (z : V) (a0 : lift_bot A) : lift_bot A :=
  SsaRefinement.fact EV pr s e z a0.

(** Edge refinement starts with the assignment's own fact for the value. *)
Definition refine_on_edge {S O N E V K C A} (EV : encoding V)
    (pr : sparse_problem S O N E V K C A) (s : sparse_unknown N E V -> lift_bot A)
    (e : E) (z : V) : lift_bot A :=
  refine_fact EV pr s e z (s (UVal z)).

(** An edge is feasible precisely when each refined guard subject is above empty bottom. *)
Definition edge_feasible {S O N E V K C A} (EV : encoding V)
    (pr : sparse_problem S O N E V K C A) (s : sparse_unknown N E V -> lift_bot A)
    (e : E) : bool :=
  SsaRefinement.feasible EV pr s e.

(** Refining a supplied fact preserves its value when the guards and operand equations hold. *)
Theorem refine_fact_sound {S O N E V K C A} (EV : encoding V)
    (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) (s : S) (e : E) (z : V)
    (a0 : lift_bot A) (c : C) :
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  Forall (cond_holds (view pr) s) (edge_guard (view pr) e) ->
  guard_ops_consistent (view pr) s e ->
  (forall x d, val (view pr) s x = Some d ->
    gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  val (view pr) s z = Some c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) a0 c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) (refine_fact EV pr sigma e z a0) c.
Proof.
  intros Hdomain Hguards Hops Hfacts Hz Ha.
  exact (SsaRefinement.fact_sound EV pr sigma s z c Hdomain Hfacts Hz e a0 Hguards Hops Ha).
Qed.

(** Refinement from the assignment's own value fact preserves every value it contains. *)
Theorem refine_on_edge_sound {S O N E V K C A} (EV : encoding V)
    (pr : sparse_problem S O N E V K C A)
    (sigma : sparse_unknown N E V -> lift_bot A) (s : S) (e : E) (z : V) (c : C) :
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  Forall (cond_holds (view pr) s) (edge_guard (view pr) e) ->
  guard_ops_consistent (view pr) s e ->
  (forall x d, val (view pr) s x = Some d ->
    gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
  val (view pr) s z = Some c ->
  gamma (lift_bot_gamma (fact_conc (domain pr))) (refine_on_edge EV pr sigma e z) c.
Proof.
  intros Hdomain Hguards Hops Hfacts Hz.
  apply refine_fact_sound with (s := s); try assumption; apply Hfacts; exact Hz.
Qed.

(** A concretely taken edge passes feasibility whenever its source valuation is covered. *)
Theorem edge_feasible_sound {S O N E V K C A} (EV : encoding V) (m : semantics S O)
    (pr : sparse_problem S O N E V K C A) (sigma : sparse_unknown N E V -> lift_bot A) :
  ssa_view_laws m (view pr) ->
  sparse_domain_laws (domain pr) (truth (view pr)) (op_eval (view pr)) ->
  forall s l s' e, reachable_state m s -> step m s l s' -> taken (base (view pr)) s l s' e ->
    (forall x d, val (view pr) s x = Some d ->
      gamma (lift_bot_gamma (fact_conc (domain pr))) (sigma (UVal x)) d) ->
    edge_feasible EV pr sigma e = true.
Proof.
  exact (SsaRefinement.feasible_sound EV m pr sigma).
Qed.
