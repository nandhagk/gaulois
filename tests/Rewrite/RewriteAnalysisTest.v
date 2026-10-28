(** * Client facts for partial evaluation

    A client derives nonzero facts from a refined sort and proves a guarded division action.
    For example, zero and undefined variables both fail the successful-nonzero guard.
    Builds on: RewriteAnalysis, RewriteEgraph and Rocq Stdlib natural division. *)

From Stdlib Require Import List Bool PArith PeanoNat.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteAnalysis.
Import List.ListNotations.

Bind Scope positive_scope with rw_id.

(** * A no-op client *)

Definition analysis_noop {K Sort V C} : rw_analysis K Sort V C unit :=
  RwAnalysis _ _ _ _ _ (fun _ _ => True) tt (fun _ _ => tt) (fun _ _ _ => tt).

Example analysis_noop_laws {K Sort V C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) :
  rw_analysis_laws sig admissible analysis_noop.
Proof.
  constructor.
  - intros result; exact I.
  - intros f h result Hf Hh; exact I.
  - intros g facts c Hwf Hfacts t sem Hrepr Hsem; exact I.
Qed.

Example analysis_noop_computes :
  rw_analyse_step (@analysis_noop bool bool nat nat) rw_empty (fun _ => tt) 1 1 = tt.
Proof.
  reflexivity.
Qed.

(** * A nonzero and definedness client *)

Inductive analysis_fact : Type :=
  | AnalysisUnknown
  | AnalysisDefined
  | AnalysisNonzero.

Definition analysis_holds (f : analysis_fact) (result : option nat) : Prop :=
  match f with
  | AnalysisUnknown => True
  | AnalysisDefined => exists n, result = Some n
  | AnalysisNonzero => exists n, result = Some n /\ n <> 0
  end.

Definition analysis_combine (f h : analysis_fact) : analysis_fact :=
  match f, h with
  | AnalysisNonzero, _ => AnalysisNonzero
  | _, AnalysisNonzero => AnalysisNonzero
  | AnalysisDefined, _ => AnalysisDefined
  | _, AnalysisDefined => AnalysisDefined
  | AnalysisUnknown, AnalysisUnknown => AnalysisUnknown
  end.

(** True is a refined sort inhabited only by the distinguished nonzero variable. *)
Definition analysis_signature : rw_signature bool bool nat :=
  RwSignature _ _ _ (fun v => Some (Nat.eqb v 1))
    (fun (op : bool) (sorts : list bool) (result : bool) => negb result &&
      if op then
        match sorts with
        | [true; true] => true
        | _ => false
        end
      else
        match sorts with
        | [] => true
        | _ => false
        end).

(** The true operator divides; false is the nullary constant one. *)
Definition analysis_eval_op (op : bool) (args : list nat) : option nat :=
  if op then
    match args with
    | [x; y] => if Nat.eqb y 0 then None else Some (Nat.div x y)
    | _ => None
    end
  else
    match args with
    | [] => Some 1
    | _ => None
    end.

Definition analysis_admissible (sem : rw_semantics bool bool nat nat) : Prop :=
  (exists n, rw_var_value sem 1 = Some n /\ n <> 0) /\
  forall op args, rw_eval_op sem op args = analysis_eval_op op args.

Definition analysis_transfer (g : rw_graph bool bool nat) (facts : rw_id -> analysis_fact)
    (c : rw_id) : analysis_fact :=
  match rw_class_sort g c with
  | Some true => AnalysisNonzero
  | _ => facts c
  end.

Definition analysis_client : rw_analysis bool bool nat nat analysis_fact :=
  RwAnalysis _ _ _ _ _ analysis_holds AnalysisUnknown analysis_combine analysis_transfer.

Lemma analysis_refined_term t :
  rw_typed analysis_signature t -> rw_sort t = true -> t = RWVar true 1.
Proof.
  intros Htyped Hsort; destruct Htyped as [s v Hvar|s op args Hargs Hshape].
  - cbn in Hsort; subst s.
    cbn in Hvar; injection Hvar as Hvar; apply Nat.eqb_eq in Hvar; now subst v.
  - cbn in Hsort; subst s; discriminate Hshape.
Qed.

Lemma analysis_transfer_holds g facts c :
  rw_graph_wf analysis_signature g ->
  rw_facts_valid analysis_admissible analysis_client g facts ->
  rw_fact_valid analysis_admissible analysis_client g c (analysis_transfer g facts c).
Proof.
  intros Hwf Hfacts t sem Hrepr Hsem.
  unfold analysis_transfer.
  destruct (rw_class_sort g c) as [[|]|] eqn:Hsort;
    try exact (Hfacts c t sem Hrepr Hsem).
  pose proof (rw_wf_layout analysis_signature g Hwf) as Hlayout.
  pose proof (rw_layout_represents_sort analysis_signature g c t Hlayout Hrepr) as Hterm_sort.
  rewrite Hsort in Hterm_sort; injection Hterm_sort as Hterm_sort.
  pose proof (rw_layout_represents_typed analysis_signature g Hlayout c t Hrepr) as Htyped.
  rewrite (analysis_refined_term t Htyped (eq_sym Hterm_sort)).
  exact (proj1 Hsem).
Qed.

Example analysis_client_laws :
  rw_analysis_laws analysis_signature analysis_admissible analysis_client.
Proof.
  constructor.
  - intros result; exact I.
  - intros f h result Hf Hh; destruct f, h; cbn in *; assumption.
  - exact analysis_transfer_holds.
Qed.

Definition analysis_semantics : rw_semantics bool bool nat nat :=
  RwSemantics _ _ _ _
    (fun v => if Nat.eqb v 1 then Some 7 else if Nat.eqb v 0 then Some 0 else None)
    analysis_eval_op.

Example analysis_context_inhabited : analysis_admissible analysis_semantics.
Proof.
  split.
  - exists 7; split; [reflexivity|discriminate].
  - intros op args; reflexivity.
Qed.

Example analysis_nonzero_excludes_undefined : ~ analysis_holds AnalysisNonzero None.
Proof.
  intros [n [Hresult Hnonzero]]; discriminate.
Qed.

Example analysis_nonzero_excludes_zero : ~ analysis_holds AnalysisNonzero (Some 0).
Proof.
  intros [n [Hresult Hnonzero]]; injection Hresult as <-; exact (Hnonzero eq_refl).
Qed.

Example analysis_defined_includes_zero : analysis_holds AnalysisDefined (Some 0).
Proof.
  exists 0; reflexivity.
Qed.

Example analysis_defined_excludes_undefined : ~ analysis_holds AnalysisDefined None.
Proof.
  intros [n Hresult]; discriminate.
Qed.

Definition analysis_add := rw_add bool_encoding bool_encoding nat_encoding.

Definition analysis_variable : rw_term bool bool nat := RWVar true 1.

Definition analysis_start := analysis_add rw_empty analysis_variable.

Definition analysis_graph := fst analysis_start.

Definition analysis_class := snd analysis_start.

Example analysis_start_valid :
  rw_graph_wf analysis_signature analysis_graph /\
  rw_represents analysis_graph analysis_class analysis_variable.
Proof.
  assert (Htyped : rw_typed analysis_signature analysis_variable).
  { apply rw_typed_var; reflexivity. }
  pose proof (rw_add_correct bool_encoding bool_encoding nat_encoding analysis_signature
    analysis_admissible ([] : list (rw_rule bool bool nat unit)) rw_empty analysis_variable
    (rw_empty_wf analysis_signature)
    (rw_empty_sound analysis_signature analysis_admissible []) rw_empty_productive Htyped)
    as Hadded.
  fold analysis_add analysis_start in Hadded.
  unfold analysis_graph, analysis_class; destruct analysis_start as [g c].
  destruct Hadded as [Hwf [Hsound [Hproductive [Hextends Hrepr]]]]; split; assumption.
Qed.

Definition analysis_initial : rw_id -> analysis_fact := fun _ => AnalysisUnknown.

Definition analysis_updated :=
  rw_analyse_step analysis_client analysis_graph analysis_initial analysis_class.

Example analysis_update_computes :
  analysis_updated analysis_class = AnalysisNonzero /\
  analysis_updated 1 = AnalysisUnknown.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example analysis_update_valid :
  rw_facts_valid analysis_admissible analysis_client analysis_graph analysis_updated.
Proof.
  apply (rw_analyse_step_valid analysis_signature analysis_admissible analysis_client).
  - exact analysis_client_laws.
  - exact (proj1 analysis_start_valid).
  - exact (rw_unknown_facts_valid analysis_signature analysis_admissible analysis_client
      analysis_graph analysis_client_laws).
Qed.

Example analysis_nonzero_fact_valid :
  rw_fact_valid analysis_admissible analysis_client analysis_graph analysis_class AnalysisNonzero.
Proof.
  pose proof (analysis_update_valid analysis_class) as Hvalid.
  rewrite (proj1 analysis_update_computes) in Hvalid; exact Hvalid.
Qed.

Example analysis_defined_fact_valid :
  rw_fact_valid analysis_admissible analysis_client analysis_graph analysis_class AnalysisDefined.
Proof.
  intros t sem Hrepr Hsem.
  destruct (analysis_nonzero_fact_valid t sem Hrepr Hsem) as [n [Hresult Hnonzero]].
  exists n; exact Hresult.
Qed.

Definition analysis_defined_initial (c : rw_id) : analysis_fact :=
  if Pos.eqb c analysis_class then AnalysisDefined else AnalysisUnknown.

Example analysis_defined_initial_valid :
  rw_facts_valid analysis_admissible analysis_client analysis_graph analysis_defined_initial.
Proof.
  intros c t sem Hrepr Hsem; unfold analysis_defined_initial.
  destruct (Pos.eqb c analysis_class) eqn:Hsame.
  - apply Pos.eqb_eq in Hsame; subst c.
    exact (analysis_defined_fact_valid t sem Hrepr Hsem).
  - exact I.
Qed.

Example analysis_defined_fact_refined :
  rw_analyse_step analysis_client analysis_graph analysis_defined_initial analysis_class
    analysis_class = AnalysisNonzero.
Proof.
  vm_compute; reflexivity.
Qed.

(** * A fact-justified semantic action *)

Definition analysis_guard (f : analysis_fact) : bool :=
  match f with
  | AnalysisNonzero => true
  | _ => false
  end.

Lemma analysis_guard_sound g facts c t :
  rw_facts_valid analysis_admissible analysis_client g facts ->
  analysis_guard (facts c) = true -> rw_represents g c t ->
  forall sem, analysis_admissible sem ->
    exists n, rw_denote sem t = Some n /\ n <> 0.
Proof.
  intros Hfacts Hguard Hrepr sem Hsem.
  specialize (Hfacts c t sem Hrepr Hsem).
  destruct (facts c); try discriminate Hguard; exact Hfacts.
Qed.

(** Successful nonzero evaluation is the premise that licenses self-division. *)
Lemma analysis_division_sound g facts c t :
  rw_facts_valid analysis_admissible analysis_client g facts ->
  analysis_guard (facts c) = true -> rw_represents g c t ->
  rw_equiv analysis_admissible (RWApp false true [t; t]) (RWApp false false []).
Proof.
  intros Hfacts Hguard Hrepr sem Hsem.
  destruct (analysis_guard_sound g facts c t Hfacts Hguard Hrepr sem Hsem)
    as [n [Hvalue Hnonzero]].
  assert (Hargs : rw_denote_args sem [t; t] = Some [n; n]).
  { rewrite !rw_denote_args_cons, Hvalue; reflexivity. }
  rewrite !rw_denote_app, Hargs.
  cbn [rw_denote_args]; rewrite !(proj2 Hsem).
  cbn [analysis_eval_op].
  assert (Htest : Nat.eqb n 0 = false) by (apply Nat.eqb_neq; exact Hnonzero).
  rewrite Htest, Nat.div_same by exact Hnonzero; reflexivity.
Qed.

Example analysis_guard_accepts_nonzero :
  analysis_guard (analysis_updated analysis_class) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example analysis_division_action_valid :
  rw_equiv analysis_admissible
    (RWApp false true [analysis_variable; analysis_variable]) (RWApp false false []).
Proof.
  exact (analysis_division_sound analysis_graph analysis_updated analysis_class analysis_variable
    analysis_update_valid analysis_guard_accepts_nonzero (proj2 analysis_start_valid)).
Qed.

Example analysis_partial_results :
  rw_denote analysis_semantics (RWVar false 0) = Some 0 /\
  rw_denote analysis_semantics (RWVar false 2) = None /\
  rw_denote analysis_semantics (RWApp false true [RWVar false 0; RWVar false 0]) = None /\
  rw_denote analysis_semantics (RWApp false true [RWVar false 2; RWVar false 2]) = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example analysis_guard_rejects_zero_and_undefined :
  analysis_guard AnalysisDefined = false /\ analysis_guard AnalysisUnknown = false.
Proof.
  split; reflexivity.
Qed.

Definition analysis_initial_guard (t : rw_term bool bool nat) : bool :=
  let '(g, c) := analysis_add rw_empty t in
  analysis_guard (rw_analyse_step analysis_client g analysis_initial c c).

Example analysis_zero_and_undefined_guards_compute :
  analysis_initial_guard (RWVar false 0) = false /\
  analysis_initial_guard (RWVar false 2) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example analysis_zero_action_invalid :
  ~ rw_equiv analysis_admissible
    (RWApp false true [RWVar false 0; RWVar false 0]) (RWApp false false []).
Proof.
  intro Hequiv; specialize (Hequiv analysis_semantics analysis_context_inhabited).
  discriminate Hequiv.
Qed.

Example analysis_undefined_action_invalid :
  ~ rw_equiv analysis_admissible
    (RWApp false true [RWVar false 2; RWVar false 2]) (RWApp false false []).
Proof.
  intro Hequiv; specialize (Hequiv analysis_semantics analysis_context_inhabited).
  discriminate Hequiv.
Qed.

(** * The same proof obligation for an analysis-triggered union *)

Definition analysis_lhs : rw_term bool bool nat :=
  RWApp false true [analysis_variable; analysis_variable].

Definition analysis_rhs : rw_term bool bool nat := RWApp false false [].

(** This ground rule captures the validated fact rather than supplying an arbitrary action hook. *)
Definition analysis_action_rule : rw_rule bool bool nat unit :=
  RwRule _ _ _ _ [] (fun _ => None)
    (RWPApp false true [RWPVar true 1; RWPVar true 1]) (RWPApp false false [])
    (fun _ => analysis_guard (analysis_updated analysis_class)).

Example analysis_action_rule_wf : rw_rule_wf analysis_signature analysis_action_rule.
Proof.
  split; [constructor|]; split.
  - intros h; split; [contradiction|intros [s Hsort]; discriminate Hsort].
  - split.
    + apply rwp_typed_app.
      * constructor; [apply rwp_typed_var; reflexivity|].
        constructor; [apply rwp_typed_var; reflexivity|constructor].
      * reflexivity.
    + split.
      * apply rwp_typed_app; [constructor|reflexivity].
      * reflexivity.
Qed.

Example analysis_action_rule_sound :
  rw_rule_sound analysis_signature analysis_admissible analysis_action_rule.
Proof.
  intros sub l r Hsub Hguard Hlhs Hrhs.
  injection Hlhs as <-; injection Hrhs as <-.
  exact (analysis_division_sound analysis_graph analysis_updated analysis_class analysis_variable
    analysis_update_valid Hguard (proj2 analysis_start_valid)).
Qed.

Example analysis_action_terms_typed :
  rw_typed analysis_signature analysis_lhs /\ rw_typed analysis_signature analysis_rhs.
Proof.
  split.
  - apply rw_typed_app.
    + constructor; [apply rw_typed_var; reflexivity|].
      constructor; [apply rw_typed_var; reflexivity|constructor].
    + reflexivity.
  - apply rw_typed_app; [constructor|reflexivity].
Qed.

Definition analysis_action_start := analysis_add rw_empty analysis_lhs.

Definition analysis_action_pair :=
  let '(g, c) := analysis_action_start in
  let '(h, d) := analysis_add g analysis_rhs in
  (h, (c, d)).

Lemma analysis_action_setup :
  let '(g, (c, d)) := analysis_action_pair in
  rw_graph_wf analysis_signature g /\
  rw_graph_sound analysis_signature analysis_admissible [analysis_action_rule] g /\
  rw_productive g /\ rw_represents g c analysis_lhs /\ rw_represents g d analysis_rhs.
Proof.
  unfold analysis_action_pair.
  destruct analysis_action_start as [g c] eqn:Hfirst_pair.
  destruct (analysis_add g analysis_rhs) as [h d] eqn:Hsecond_pair.
  pose proof (rw_add_correct bool_encoding bool_encoding nat_encoding analysis_signature
    analysis_admissible [analysis_action_rule] rw_empty analysis_lhs
    (rw_empty_wf analysis_signature)
    (rw_empty_sound analysis_signature analysis_admissible [analysis_action_rule])
    rw_empty_productive (proj1 analysis_action_terms_typed)) as Hfirst.
  fold analysis_add analysis_action_start in Hfirst; rewrite Hfirst_pair in Hfirst.
  destruct Hfirst as [Hwf [Hsound [Hproductive [Hextends Hlhs]]]].
  pose proof (rw_add_correct bool_encoding bool_encoding nat_encoding analysis_signature
    analysis_admissible [analysis_action_rule] g analysis_rhs Hwf Hsound Hproductive
    (proj2 analysis_action_terms_typed)) as Hsecond.
  fold analysis_add in Hsecond; rewrite Hsecond_pair in Hsecond.
  destruct Hsecond as [Hwf' [Hsound' [Hproductive' [Hextends' Hrhs]]]].
  split; [exact Hwf'|]; split; [exact Hsound'|]; split; [exact Hproductive'|].
  split; [exact (Hextends' c analysis_lhs Hlhs)|exact Hrhs].
Qed.

Example analysis_action_joinable :
  let '(g, (c, d)) := analysis_action_pair in
  rw_joinable analysis_signature analysis_admissible [analysis_action_rule] g c d.
Proof.
  pose proof analysis_action_setup as Hsetup.
  destruct analysis_action_pair as [g [c d]].
  destruct Hsetup as [Hwf [Hsound [Hproductive [Hlhs Hrhs]]]].
  split; [exists analysis_lhs; exact Hlhs|].
  split; [exists analysis_rhs; exact Hrhs|].
  intros t u Ht Hu.
  apply (rw_eq_trans _ _ _ t analysis_lhs u); [exact (Hsound c t analysis_lhs Ht Hlhs)|].
  apply (rw_eq_trans _ _ _ analysis_lhs analysis_rhs u).
  - apply (rw_eq_rule _ _ _ analysis_action_rule (fun _ => None)).
    + cbn; auto.
    + intros hole s Hsort; discriminate Hsort.
    + exact analysis_guard_accepts_nonzero.
    + reflexivity.
    + reflexivity.
  - exact (Hsound d analysis_rhs u Hrhs Hu).
Qed.

Example analysis_action_union_computes :
  let '(g, (c, d)) := analysis_action_pair in
  match rw_union bool_encoding g c d with
  | Some h => rw_find h c = rw_find h d
  | None => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

(** The computed merge retains the full library guarantee under the proved joinability premise. *)
Example analysis_action_union_preserves :
  let '(g, (c, d)) := analysis_action_pair in
  forall h, rw_union bool_encoding g c d = Some h ->
    rw_graph_wf analysis_signature h /\
    rw_graph_sound analysis_signature analysis_admissible [analysis_action_rule] h /\
    rw_productive h /\ rw_extends g h /\ rw_find h c = rw_find h d.
Proof.
  pose proof analysis_action_setup as Hsetup.
  pose proof analysis_action_joinable as Hjoinable.
  destruct analysis_action_pair as [g [c d]].
  destruct Hsetup as [Hwf [Hsound [Hproductive [Hlhs Hrhs]]]].
  intros h Hunion.
  exact (rw_union_correct bool_encoding analysis_signature analysis_admissible
    [analysis_action_rule] g h c d Hwf Hsound Hproductive Hjoinable Hunion).
Qed.

(** * Graph and environment invalidation *)

Definition analysis_zero_start := analysis_add rw_empty (RWVar false 0).

Lemma analysis_zero_represented :
  rw_represents (fst analysis_zero_start) (snd analysis_zero_start) (RWVar false 0).
Proof.
  pose proof (rw_add_correct bool_encoding bool_encoding nat_encoding analysis_signature
    analysis_admissible ([] : list (rw_rule bool bool nat unit)) rw_empty (RWVar false 0)
    (rw_empty_wf analysis_signature) (rw_empty_sound analysis_signature analysis_admissible [])
    rw_empty_productive (rw_typed_var analysis_signature false 0 eq_refl)) as Hadded.
  fold analysis_add analysis_zero_start in Hadded.
  destruct analysis_zero_start as [g c].
  exact (proj2 (proj2 (proj2 (proj2 Hadded)))).
Qed.

Example analysis_empty_facts_valid :
  rw_facts_valid analysis_admissible analysis_client rw_empty (fun _ => AnalysisNonzero).
Proof.
  intros c t sem Hrepr Hsem; exact (False_rect _ (rw_empty_no_represents c t Hrepr)).
Qed.

Example analysis_extension_invalidates_fact :
  ~ rw_facts_valid analysis_admissible analysis_client (fst analysis_zero_start)
    (fun _ => AnalysisNonzero).
Proof.
  intro Hvalid.
  specialize (Hvalid (snd analysis_zero_start) (RWVar false 0) analysis_semantics
    analysis_zero_represented analysis_context_inhabited).
  exact (analysis_nonzero_excludes_zero Hvalid).
Qed.

Example analysis_reset_after_extension_valid :
  rw_facts_valid analysis_admissible analysis_client (fst analysis_zero_start) analysis_initial.
Proof.
  exact (rw_unknown_facts_valid analysis_signature analysis_admissible analysis_client
    (fst analysis_zero_start) analysis_client_laws).
Qed.

Definition analysis_outside_context : rw_semantics bool bool nat nat :=
  RwSemantics _ _ _ _ (fun _ => None) analysis_eval_op.

Example analysis_context_cannot_be_enlarged :
  ~ rw_fact_valid (fun _ => True) analysis_client analysis_graph analysis_class AnalysisNonzero.
Proof.
  intro Hvalid.
  specialize (Hvalid analysis_variable analysis_outside_context (proj2 analysis_start_valid) I).
  exact (analysis_nonzero_excludes_undefined Hvalid).
Qed.
