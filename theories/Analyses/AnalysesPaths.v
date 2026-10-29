(** * Bounded path facts and dominated guards

    Path facts retain bounded alternatives and guard chains read prepared dominator indexes.
    For example, a cap of one merges two incoming constants into one covering fact.
    Builds on: OrderDisjunction, ViewsSsa and ViewsDominated. *)

From Stdlib Require Import List.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderDisjunction.
From Gaulois.Graph Require Import GraphEdgeDominance.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsDominated.
Import List.ListNotations.

(** Cartesian choices retain operand order and every combination of alternatives. *)
Fixpoint path_choices {A} (fs : list (list A)) : list (list A) :=
  match fs with
  | [] => [[]]
  | xs :: rest =>
    let tails := path_choices rest in
    flat_map (fun x => map (cons x) tails) xs
  end.

(** Forward transfer retains alternatives; backward transfer first joins each operand's facts. *)
Definition path_domain {A C K} (k : nat) (D : sparse_domain A C K) :
    sparse_domain (list A) C K :=
  {| fact_lat := disjunction_lattice k (fact_lat D);
     fact_conc := disjunction_gamma (fact_conc D);
     top_fact := [top_fact D];
     op_abs o fs := compact k (fact_lat D) (map (op_abs D o) (path_choices fs));
     assume_value g xs := compact k (fact_lat D) (map (assume_value D g) xs);
     assume_args o b fs :=
       map (fun a => [a]) (assume_args D o b (map (join_all (fact_lat D)) fs)) |}.

(** The guards on dominating edges are listed in the prepared context's outermost-first order. *)
Definition guard_chain {S O N E V K C} (sv : ssa_view S O N E V K C) (EN : encoding N)
    (b : N) : list (condition V C) :=
  flat_map (edge_guard sv) (dominating_edges_in (make_dom_context EN (cfg (base sv))) b).

Lemma path_compact_sound {A C} k (L : lattice A) (G : concretisation A C) :
  lattice_laws L -> concretisation_laws L G -> forall xs c,
  gamma (disjunction_gamma G) xs c -> gamma (disjunction_gamma G) (compact k L xs) c.
Proof.
  intros Hl Hg xs c Hfact.
  exact (gamma_monotone (disjunction_gamma_laws k L G Hl Hg) xs _ c
    (compact_covers L Hl k xs) Hfact).
Qed.

Lemma path_choices_sound {A C} (G : concretisation A C) fs cs :
  Forall2 (gamma (disjunction_gamma G)) fs cs ->
  exists xs, In xs (path_choices fs) /\ Forall2 (gamma G) xs cs.
Proof.
  intro Hfacts. induction Hfacts as [|alts c fs cs [x [Hx Hfact]] Htail IH].
  - exists []; split; [left; reflexivity|constructor].
  - destruct IH as [xs [Hin Hxs]]. exists (x :: xs); split.
    + cbn. apply in_flat_map. exists x; split; [exact Hx|].
      apply in_map. exact Hin.
    + constructor; assumption.
Qed.

Lemma path_join_arguments {A C} (L : lattice A) (G : concretisation A C) :
  lattice_laws L -> concretisation_laws L G -> forall fs cs,
  Forall2 (gamma (disjunction_gamma G)) fs cs ->
  Forall2 (gamma G) (map (join_all L) fs) cs.
Proof.
  intros Hl Hg fs cs Hfacts.
  induction Hfacts as [|xs c fs cs [x [Hin Hfact]] Htail IH]; cbn; constructor.
  - exact (gamma_monotone Hg x _ c (join_all_upper L Hl xs x Hin) Hfact).
  - exact IH.
Qed.

Lemma path_singleton_arguments {A C} (G : concretisation A C) fs cs :
  Forall2 (gamma G) fs cs ->
  Forall2 (gamma (disjunction_gamma G)) (map (fun a => [a]) fs) cs.
Proof.
  intro Hfacts. induction Hfacts as [|a c fs cs Hfact Htail IH]; cbn; constructor.
  - exists a. split; [left; reflexivity|exact Hfact].
  - exact IH.
Qed.

(** Bounded disjunction preserves every sparse-domain law. *)
Theorem path_domain_laws {A C K} (k : nat) (D : sparse_domain A C K) (truth : C -> bool)
    (op_eval : K -> list C -> option C) :
  sparse_domain_laws D truth op_eval -> sparse_domain_laws (path_domain k D) truth op_eval.
Proof.
  intro Hdomain. constructor.
  - apply disjunction_laws, (dom_lattice Hdomain).
  - apply disjunction_gamma_laws; [apply (dom_lattice Hdomain)|apply (dom_conc Hdomain)].
  - intros c [a [Hin _]]. exact Hin.
  - intro c. exists (top_fact D). split; [left; reflexivity|apply (top_sound Hdomain)].
  - intros o fs cs c Hfacts Heval. apply path_compact_sound;
      [apply (dom_lattice Hdomain)|apply (dom_conc Hdomain)|].
    destruct (path_choices_sound (fact_conc D) fs cs Hfacts) as [xs [Hin Hxs]].
    exists (op_abs D o xs). split; [apply in_map; exact Hin|].
    exact (op_sound Hdomain o xs cs c Hxs Heval).
  - intros g xs c [a [Hin Hfact]] Hguard. apply path_compact_sound;
      [apply (dom_lattice Hdomain)|apply (dom_conc Hdomain)|].
    exists (assume_value D g a). split; [apply in_map; exact Hin|].
    exact (assume_value_sound Hdomain g a c Hfact Hguard).
  - intros o b fs cs c Hfacts Heval Htruth. apply path_singleton_arguments.
    apply (assume_args_sound Hdomain o b _ cs c); [|exact Heval|exact Htruth].
    apply path_join_arguments; [apply (dom_lattice Hdomain)|apply (dom_conc Hdomain)|exact Hfacts].
Qed.

(** Every guard in a reachable block's chain holds with a defined subject. *)
Theorem guard_chain_holds {S O N E V K C} (m : semantics S O) (sv : ssa_view S O N E V K C)
    (EN : encoding N) :
  ssa_view_laws m sv -> strict_ssa_laws m sv ->
  forall s, reachable_state m s ->
    Forall (cond_holds sv s) (guard_chain sv EN (point (base sv) s)).
Proof.
  intros Hview Hstrict s Hreachable. apply Forall_forall. intros cd Hin.
  apply in_flat_map in Hin. destruct Hin as [e [Hedge Hguard]].
  assert (Hdom : edge_dominates (cfg (base sv)) e (point (base sv) s)).
  { apply (dominating_edges_graph_wf EN (cfg (base sv)) _ e
      (cfg_wf (base_laws Hview))). exact Hedge. }
  pose proof (proj1 (dominated_guard_holds m sv Hview Hstrict s e Hreachable Hdom)) as Hguards.
  exact (proj1 (Forall_forall _ _) Hguards cd Hguard).
Qed.
