(** * Order facts for rewriting

    Order concretisations describe successful results while allowing undefined evaluation.
    For example, a full top fact covers both a word result and an undefined expression.
    Builds on: OrderLattice, OrderConcrete and RewriteAnalysis. *)

From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph RewriteAnalysis.

(** A concretisation constrains successful evaluation and leaves undefined results permitted. *)
Definition rw_order_holds {A C} (G : concretisation A C) (a : A) (result : option C) : Prop :=
  match result with
  | None => True
  | Some c => gamma G a c
  end.

(** An Order analysis uses top for unknown information and join to combine sound facts. *)
Definition rw_order_analysis {K Sort V A C} (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) :
    rw_analysis K Sort V C A :=
  RwAnalysis K Sort V C A (rw_order_holds G) (top_value T) (join L) transfer.

(** A client separately proves that its transfer covers every represented evaluation. *)
Definition rw_order_transfer_sound {K Sort V A C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) : Prop :=
  forall g facts c, rw_graph_wf sig g ->
    rw_facts_valid admissible (rw_order_analysis L T G transfer) g facts ->
    rw_fact_valid admissible (rw_order_analysis L T G transfer) g c (transfer g facts c).

(** Weak lattice laws and the client's transfer proof establish the Rewrite analysis laws. *)
Theorem rw_order_analysis_laws {K Sort V A C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (L : lattice A) (T : top L)
    (G : concretisation A C) (transfer : rw_graph K Sort V -> (rw_id -> A) -> rw_id -> A) :
  lattice_laws L -> concretisation_laws L G -> top_full T G ->
  rw_order_transfer_sound sig admissible L T G transfer ->
  rw_analysis_laws sig admissible (rw_order_analysis L T G transfer).
Proof.
  intros Hlattice Hconcrete Htop Htransfer; constructor.
  - intros [c|]; cbn [rw_order_analysis rw_order_holds]; [apply (gamma_top_full Htop)|exact I].
  - intros a b [c|] Ha Hb; cbn [rw_order_analysis rw_order_holds] in *.
    + exact (gamma_join_l L G a b c Hlattice Hconcrete Ha).
    + exact I.
  - exact Htransfer.
Qed.
