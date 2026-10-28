(** * Validated e-class facts

    Clients interpret facts over complete partial-evaluation outcomes and prove their own laws.
    For example, a nonzero fact must exclude both zero and an undefined result before division.
    Builds on: RewriteSyntax, RewriteRules, RewriteEgraph and Rocq Stdlib positive keys. *)

From Stdlib Require Import PArith.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEgraph.

(** * Client operations and validity *)

(** An analysis supplies operations independently of any particular lattice or fact carrier. *)
Record rw_analysis (K Sort V C F : Type) : Type := RwAnalysis {
  rw_fact_holds : F -> option C -> Prop;
  rw_fact_unknown : F;
  rw_fact_combine : F -> F -> F;
  rw_fact_transfer : rw_graph K Sort V -> (rw_id -> F) -> rw_id -> F
}.

Arguments rw_fact_holds {K Sort V C F}.
Arguments rw_fact_unknown {K Sort V C F}.
Arguments rw_fact_combine {K Sort V C F}.
Arguments rw_fact_transfer {K Sort V C F}.

(** A valid fact covers every represented term's whole result in each admissible environment. *)
Definition rw_fact_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (c : rw_id) (f : F) : Prop :=
  forall t sem, rw_represents g c t -> admissible sem ->
    rw_fact_holds an f (rw_denote sem t).

(** The fact environment is valid pointwise, including facts at aliases and absent identifiers. *)
Definition rw_facts_valid {K Sort V C F} (admissible : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (facts : rw_id -> F) : Prop :=
  forall c, rw_fact_valid admissible an g c (facts c).

(** Client laws preserve validity without requiring convergence, ordering or graph soundness. *)
Record rw_analysis_laws {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F) : Prop := {
  rw_unknown_valid : forall result, rw_fact_holds an (rw_fact_unknown an) result;
  rw_combine_valid : forall f h result, rw_fact_holds an f result ->
    rw_fact_holds an h result -> rw_fact_holds an (rw_fact_combine an f h) result;
  rw_transfer_valid : forall g facts c, rw_graph_wf sig g ->
    rw_facts_valid admissible an g facts ->
    rw_fact_valid admissible an g c (rw_fact_transfer an g facts c)
}.

Arguments rw_unknown_valid {K Sort V C F sig admissible an}.
Arguments rw_combine_valid {K Sort V C F sig admissible an}.
Arguments rw_transfer_valid {K Sort V C F sig admissible an}.

(** Unknown facts can initialize or reset the environment after any graph change. *)
Lemma rw_unknown_facts_valid {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) :
  rw_analysis_laws sig admissible an ->
  rw_facts_valid admissible an g (fun _ => rw_fact_unknown an).
Proof.
  intros Hlaws c t sem Hrepr Hsem.
  exact (rw_unknown_valid Hlaws (rw_denote sem t)).
Qed.

(** Validity may be restricted to fewer environments without promoting contextual facts. *)
Lemma rw_fact_valid_restrict {K Sort V C F}
    (admissible restricted : rw_semantics K Sort V C -> Prop)
    (an : rw_analysis K Sort V C F) (g : rw_graph K Sort V) (c : rw_id) (f : F) :
  (forall sem, restricted sem -> admissible sem) ->
  rw_fact_valid admissible an g c f -> rw_fact_valid restricted an g c f.
Proof.
  intros Hrestrict Hvalid t sem Hrepr Hsem.
  exact (Hvalid t sem Hrepr (Hrestrict sem Hsem)).
Qed.

(** A fact for an extension covers the old terms; the converse needs renewed validation. *)
Lemma rw_fact_valid_old_graph {K Sort V C F}
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g g' : rw_graph K Sort V) (c : rw_id) (f : F) :
  rw_extends g g' -> rw_fact_valid admissible an g' c f ->
  rw_fact_valid admissible an g c f.
Proof.
  intros Hextends Hvalid t sem Hrepr Hsem.
  exact (Hvalid t sem (Hextends c t Hrepr) Hsem).
Qed.

(** * Single-class update *)

(** A step combines at the selected identifier using the old environment for the transfer. *)
Definition rw_analyse_step {K Sort V C F} (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) : rw_id -> F :=
  fun d =>
    if Pos.eqb d c then rw_fact_combine an (facts c) (rw_fact_transfer an g facts c)
    else facts d.

Lemma rw_analyse_step_same {K Sort V C F} (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) :
  rw_analyse_step an g facts c c =
    rw_fact_combine an (facts c) (rw_fact_transfer an g facts c).
Proof.
  unfold rw_analyse_step; now rewrite Pos.eqb_refl.
Qed.

Lemma rw_analyse_step_other {K Sort V C F} (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c d : rw_id) :
  d <> c -> rw_analyse_step an g facts c d = facts d.
Proof.
  intro Hdifferent; unfold rw_analyse_step.
  apply Pos.eqb_neq in Hdifferent; now rewrite Hdifferent.
Qed.

(** Each step preserves all class facts using the client's combination and transfer laws. *)
Theorem rw_analyse_step_valid {K Sort V C F} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (an : rw_analysis K Sort V C F)
    (g : rw_graph K Sort V) (facts : rw_id -> F) (c : rw_id) :
  rw_analysis_laws sig admissible an -> rw_graph_wf sig g ->
  rw_facts_valid admissible an g facts ->
  rw_facts_valid admissible an g (rw_analyse_step an g facts c).
Proof.
  intros Hlaws Hwf Hfacts d t sem Hrepr Hsem.
  destruct (Pos.eq_dec d c) as [->|Hdifferent].
  - rewrite rw_analyse_step_same.
    apply (rw_combine_valid Hlaws).
    + exact (Hfacts c t sem Hrepr Hsem).
    + exact (rw_transfer_valid Hlaws g facts c Hwf Hfacts t sem Hrepr Hsem).
  - rewrite rw_analyse_step_other by exact Hdifferent.
    exact (Hfacts d t sem Hrepr Hsem).
Qed.
