(** * Direct rewriting with legacy explanations

    A one-sort adapter connects legacy terms and guarded rules to the verified Rewrite core.
    For example, an explanation replaces a multiplication by one with its first argument.
    Builds on: CollectionsMap, RewriteRun and RewriteExtract. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteRebuild RewriteRun RewriteExtract.
Import List.ListNotations.

(** * Legacy syntax and its one-sort interpretation *)

(** Legacy variables are free variables in terms and substitution holes in rule patterns. *)
Inductive term (K : Type) : Type :=
  | TVar (i : nat)
  | TApp (o : K) (args : list (term K)).

Arguments TVar {K}.
Arguments TApp {K}.

(** Every legacy variable and application belongs to the single unrestricted sort. *)
Definition legacy_signature {K} : rw_signature K unit nat :=
  RwSignature K unit nat (fun _ => Some tt) (fun _ _ _ => true).

(** Embedding retains every constructor, operator and ordered child occurrence. *)
Fixpoint legacy_embed {K} (t : term K) : rw_term K unit nat :=
  match t with
  | TVar i => RWVar tt i
  | TApp o args => RWApp tt o (map legacy_embed args)
  end.

(** Projection removes the unique sort annotation. *)
Fixpoint legacy_project {K} (t : rw_term K unit nat) : term K :=
  match t with
  | RWVar _ i => TVar i
  | RWApp _ o args => TApp o (map legacy_project args)
  end.

(** The legacy interpreter is the strict partial interpreter of the one-sort embedding. *)
Definition legacy_semantics {K C} (ev : K -> list C -> option C) (env : nat -> option C) :
    rw_semantics K unit nat C := RwSemantics K unit nat C env ev.

(** Evaluation propagates absent variables and failed children before invoking the operator. *)
Definition denote {K C} (ev : K -> list C -> option C) (env : nat -> option C) (t : term K) :
    option C := rw_denote (legacy_semantics ev env) (legacy_embed t).

Definition denote_args {K C} (ev : K -> list C -> option C) (env : nat -> option C)
    (args : list (term K)) : option (list C) :=
  rw_denote_args (legacy_semantics ev env) (map legacy_embed args).

Lemma denote_app {K C} (ev : K -> list C -> option C) env op args :
  denote ev env (TApp op args) =
    match denote_args ev env args with
    | Some cs => ev op cs
    | None => None
    end.
Proof.
  reflexivity.
Qed.

Lemma denote_binary {K C} (ev : K -> list C -> option C) env op t u :
  denote ev env (TApp op [t; u]) =
    match denote ev env t with
    | None => None
    | Some x =>
      match denote ev env u with
      | Some y => ev op [x; y]
      | None => None
      end
    end.
Proof.
  unfold denote; cbn [legacy_embed]; rewrite rw_denote_app.
  cbn [map rw_denote_args];
    destruct (rw_denote (legacy_semantics ev env) (legacy_embed t));
    destruct (rw_denote (legacy_semantics ev env) (legacy_embed u)); reflexivity.
Qed.

(** Equivalence compares complete option results in every allowed environment. *)
Definition equiv_term {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (t u : term K) : Prop :=
  forall env, ok env -> denote ev env t = denote ev env u.

(** Substitution preserves application structure and replaces each variable occurrence. *)
Fixpoint subst_term {K} (sub : nat -> term K) (t : term K) : term K :=
  match t with
  | TVar i => sub i
  | TApp o args => TApp o (map (subst_term sub) args)
  end.

(** Variable occurrences are enumerated left to right, including repetitions. *)
Fixpoint term_vars {K} (t : term K) : list nat :=
  match t with
  | TVar i => [i]
  | TApp _ args => flat_map term_vars args
  end.

(** The supplied finite witness is extended by the original variable at missing indices. *)
Definition legacy_subst {K} (bindings : list (term K)) (i : nat) : term K :=
  match nth_error bindings i with
  | Some t => t
  | None => TVar i
  end.

(** Pattern variables must have supplied entries, independently of guard-only indices. *)
Definition legacy_subst_bound {K} (bindings : list (term K)) (t : term K) : bool :=
  let bound := length bindings in
  forallb (fun i => Nat.ltb i bound) (term_vars t).

(** A supplied entry is returned without changing its term. *)
Theorem legacy_subst_present {K} (bindings : list (term K)) (i : nat) (t : term K) :
  nth_error bindings i = Some t -> legacy_subst bindings i = t.
Proof.
  intro Hget; unfold legacy_subst; now rewrite Hget.
Qed.

(** A missing guard-only entry denotes its original variable. *)
Theorem legacy_subst_missing {K} (bindings : list (term K)) (i : nat) :
  nth_error bindings i = None -> legacy_subst bindings i = TVar i.
Proof.
  intro Hget; unfold legacy_subst; now rewrite Hget.
Qed.

(** The finite bounds test checks exactly the variables occurring in the pattern. *)
Theorem legacy_subst_bound_spec {K} (bindings : list (term K)) (t : term K) :
  legacy_subst_bound bindings t = true <->
  forall i, In i (term_vars t) -> exists u, nth_error bindings i = Some u.
Proof.
  unfold legacy_subst_bound; rewrite forallb_forall; split.
  - intros Hbound i Hin; specialize (Hbound i Hin); apply Nat.ltb_lt in Hbound.
    destruct (nth_error bindings i) as [u|] eqn:Hget; [eauto|].
    apply nth_error_None in Hget; lia.
  - intros Hbound i Hin; destruct (Hbound i Hin) as [u Hget].
    apply Nat.ltb_lt, nth_error_Some; rewrite Hget; discriminate.
Qed.

(** Embedding followed by projection returns the exact original syntax. *)
Theorem legacy_project_embed {K} (t : term K) : legacy_project (legacy_embed t) = t.
Proof.
  induction t as [i|o args IHargs]; cbn; [reflexivity|].
  f_equal; rewrite map_map; induction IHargs as [|a Ha args Hargs IHargs]; cbn.
  - reflexivity.
  - now rewrite Ha, IHargs.
Qed.

Lemma legacy_embed_project {K} (t : rw_term K unit nat) :
  legacy_embed (legacy_project t) = t.
Proof.
  induction t as [[] i|[] o args IHargs]; cbn; [reflexivity|].
  f_equal; rewrite map_map; induction IHargs as [|a Ha args Hargs IHargs]; cbn.
  - reflexivity.
  - now rewrite Ha, IHargs.
Qed.

(** The unrestricted one-sort signature types every embedded legacy term. *)
Theorem legacy_embed_typed {K} (t : term K) : rw_typed legacy_signature (legacy_embed t).
Proof.
  induction t as [i|o args IHargs]; cbn; constructor; try reflexivity.
  apply Forall_map; induction IHargs as [|a Ha args Hargs IHargs]; constructor; assumption.
Qed.

(** The one-sort interpretation has exactly the legacy option result. *)
Theorem legacy_denote_agrees {K C} (ev : K -> list C -> option C) (env : nat -> option C)
    (t : term K) : rw_denote (legacy_semantics ev env) (legacy_embed t) = denote ev env t.
Proof.
  reflexivity.
Qed.

(** Admissible interpretations retain the same environment and the same operator evaluator. *)
Definition legacy_admissible {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (sem : rw_semantics K unit nat C) : Prop :=
  exists env, ok env /\ sem = legacy_semantics ev env.

(** Legacy and core equivalence quantify over exactly the same interpretations. *)
Theorem legacy_equiv_agrees {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (t u : term K) :
  equiv_term ev ok t u <-> rw_equiv (legacy_admissible ev ok) (legacy_embed t) (legacy_embed u).
Proof.
  split.
  - intros Heq sem [env [Hok ->]]; exact (Heq env Hok).
  - intros Heq env Hok; apply Heq; exists env; auto.
Qed.

(** Preorder structural codes use the supplied injective operator encoding. *)
Definition legacy_encoding {K} (EK : encoding K) : encoding (term K).
Proof.
  refine (Encoding (term K)
    (fun t => encode (list_encoding positive_encoding)
      (rw_tree_code EK unit_encoding nat_encoding (legacy_embed t))) _).
  intros t u Heq; apply (encode_injective (list_encoding positive_encoding)) in Heq.
  apply (rw_tree_code_injective EK unit_encoding nat_encoding) in Heq.
  apply (f_equal legacy_project) in Heq; now rewrite !legacy_project_embed in Heq.
Defined.

(** Structural equality compares constructor, variable, arity and encoded operator tokens. *)
Definition term_eqb {K} (EK : encoding K) (t u : term K) : bool :=
  Pos.eqb (encode (legacy_encoding EK) t) (encode (legacy_encoding EK) u).

(** Injective operator codes make structural comparison decide syntactic equality. *)
Theorem term_eqb_spec {K} (EK : encoding K) (t u : term K) : term_eqb EK t u = true <-> t = u.
Proof.
  unfold term_eqb; rewrite Pos.eqb_eq; split.
  - apply encode_injective.
  - now intros ->.
Qed.

(** Legacy cost sums operator weights and assigns zero to each variable occurrence. *)
Definition term_cost {K} (cost : K -> nat) (t : term K) : nat :=
  rw_tree_cost (fun _ => 0) cost (legacy_embed t).

(** The tree objective counts precisely the same repeated occurrences as legacy cost. *)
Theorem legacy_cost_agrees {K} (cost : K -> nat) (t : term K) :
  rw_tree_cost (fun _ => 0) cost (legacy_embed t) = term_cost cost t.
Proof.
  reflexivity.
Qed.

(** * Guarded rule translation *)

(** A legacy rule carries two patterns and a predicate on its exact total witness. *)
Record rewrite_rule (K : Type) : Type := RewriteRule {
  rule_lhs : term K;
  rule_rhs : term K;
  rule_side : (nat -> term K) -> bool
}.

Arguments RewriteRule {K}.
Arguments rule_lhs {K}.
Arguments rule_rhs {K}.
Arguments rule_side {K}.

(** Rule soundness applies to the very total substitution inspected by its guard. *)
Definition rule_sound {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (r : rewrite_rule K) : Prop :=
  forall sub, rule_side r sub = true ->
    equiv_term ev ok (subst_term sub (rule_lhs r)) (subst_term sub (rule_rhs r)).

(** Pattern translation interprets each legacy variable occurrence as a sorted hole. *)
Fixpoint legacy_pattern {K} (t : term K) : rw_pattern K unit nat nat :=
  match t with
  | TVar i => RWHole tt i
  | TApp o args => RWPApp tt o (map legacy_pattern args)
  end.

(** A total legacy witness supplies an embedded term for every core hole. *)
Definition legacy_substitution {K} (sub : nat -> term K) : rw_substitution K unit nat nat :=
  fun i => Some (legacy_embed (sub i)).

(** The public variable enumeration retains order and repeated occurrences. *)
Definition legacy_variables {K} (t : term K) : list nat := term_vars t.

(** A rule declares the duplicate-free union of both patterns' variable indices. *)
Definition legacy_rule_holes {K} (r : rewrite_rule K) : list nat :=
  nodup Nat.eq_dec (legacy_variables (rule_lhs r) ++ legacy_variables (rule_rhs r)).

(** Partial core witnesses extend to one exact total legacy witness, with extras retained. *)
Definition legacy_total_sub {K} (sub : rw_substitution K unit nat nat) (i : nat) : term K :=
  match sub i with
  | Some t => legacy_project t
  | None => TVar i
  end.

(** The translated guard receives the same concrete witness as the soundness proof. *)
Definition legacy_rule {K} (r : rewrite_rule K) : rw_rule K unit nat nat :=
  let holes := legacy_rule_holes r in
  RwRule K unit nat nat holes
    (fun i => if existsb (Nat.eqb i) holes then Some tt else None)
    (legacy_pattern (rule_lhs r)) (legacy_pattern (rule_rhs r))
    (fun sub => rule_side r (legacy_total_sub sub)).

(** No extensionality or guard-invariance assumption changes the inspected witness. *)
Theorem legacy_guard_uses_witness {K} (r : rewrite_rule K)
    (sub : rw_substitution K unit nat nat) :
  rw_condition (legacy_rule r) sub = rule_side r (legacy_total_sub sub).
Proof.
  reflexivity.
Qed.

Lemma legacy_instantiate_agrees {K} (sub : rw_substitution K unit nat nat) (t : term K) :
  forall u, rw_instantiate sub (legacy_pattern t) = Some u ->
    u = legacy_embed (subst_term (legacy_total_sub sub) t).
Proof.
  induction t as [i|o args IHargs]; intros u Hinst.
  - cbn [legacy_pattern rw_instantiate] in Hinst.
    cbn [subst_term]; unfold legacy_total_sub; rewrite Hinst.
    symmetry; apply legacy_embed_project.
  - cbn [legacy_pattern] in Hinst; rewrite rw_instantiate_app in Hinst.
    assert (Hargs : forall us, rw_instantiate_args sub (map legacy_pattern args) = Some us ->
      us = map (fun t => legacy_embed (subst_term (legacy_total_sub sub) t)) args).
    { clear Hinst u.
      induction IHargs as [|a Ha args Hargs IHargs]; intros us Hlist; cbn in Hlist.
      - now inversion Hlist.
      - change (match rw_instantiate sub (legacy_pattern a) with
          | Some v => match rw_instantiate_args sub (map legacy_pattern args) with
            | Some vs => Some (v :: vs)
            | None => None
            end
          | None => None end = Some us) in Hlist.
        destruct (rw_instantiate sub (legacy_pattern a)) as [v|] eqn:Ha';
          [|discriminate].
        destruct (rw_instantiate_args sub (map legacy_pattern args)) as [vs|] eqn:Hrest;
          [|discriminate].
        injection Hlist as <-; cbn; rewrite (Ha v eq_refl), (IHargs vs eq_refl); reflexivity. }
    destruct (rw_instantiate_args sub (map legacy_pattern args)) as [us|] eqn:Hlist;
      [|discriminate].
    injection Hinst as <-; cbn; f_equal; rewrite map_map; exact (Hargs us eq_refl).
Qed.

Lemma legacy_instantiate_total {K} (sub : nat -> term K) (t : term K) :
  rw_instantiate (legacy_substitution sub) (legacy_pattern t) =
    Some (legacy_embed (subst_term sub t)).
Proof.
  induction t as [i|o args IHargs]; cbn [legacy_pattern subst_term]; [reflexivity|].
  rewrite rw_instantiate_app.
  assert (Hargs : rw_instantiate_args (legacy_substitution sub) (map legacy_pattern args) =
    Some (map (fun t => legacy_embed (subst_term sub t)) args)).
  { induction IHargs as [|a Ha args Hargs IHargs]; cbn; [reflexivity|].
    change (match rw_instantiate (legacy_substitution sub) (legacy_pattern a) with
      | Some v => match rw_instantiate_args (legacy_substitution sub)
          (map legacy_pattern args) with
        | Some vs => Some (v :: vs)
        | None => None
        end
      | None => None end = Some (legacy_embed (subst_term sub a) ::
        map (fun t => legacy_embed (subst_term sub t)) args)).
    now rewrite Ha, IHargs. }
  rewrite Hargs; cbn; now rewrite map_map.
Qed.

(** Total substitution commutes with the legacy pattern embedding. *)
Theorem legacy_substitute_agrees {K} (sub : nat -> term K) (t : term K) :
  rw_instantiate (legacy_substitution sub) (legacy_pattern t) =
    Some (legacy_embed (subst_term sub t)).
Proof.
  apply legacy_instantiate_total.
Qed.

Lemma legacy_hole_present (holes : list nat) i :
  existsb (Nat.eqb i) holes = true <-> In i holes.
Proof.
  rewrite existsb_exists; split.
  - intros [j [Hin Heq]]; apply Nat.eqb_eq in Heq; now subst j.
  - intro Hin; exists i; split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma legacy_pattern_typed {K} (holes : list nat) (t : term K) :
  (forall i, In i (term_vars t) -> In i holes) ->
  rwp_typed legacy_signature
    (fun i => if existsb (Nat.eqb i) holes then Some tt else None) (legacy_pattern t).
Proof.
  induction t as [i|o args IHargs]; intro Hholes; cbn [legacy_pattern].
  - constructor.
    rewrite (proj2 (legacy_hole_present holes i) (Hholes i (or_introl eq_refl))); reflexivity.
  - constructor; [|reflexivity]; apply Forall_map.
    induction IHargs as [|a Ha args Hargs IHargs]; constructor.
    + apply Ha; intros i Hin; apply Hholes; apply in_flat_map; exists a.
      split; [left; reflexivity|exact Hin].
    + apply IHargs; intros i Hin; apply Hholes; apply in_flat_map.
      apply in_flat_map in Hin; destruct Hin as [a' [Hin Hvar]]; exists a'.
      split; [right; exact Hin|exact Hvar].
Qed.

(** Every translated legacy rule is well formed, including rhs-only variables. *)
Theorem legacy_rule_wf {K} (r : rewrite_rule K) :
  rw_rule_wf legacy_signature (legacy_rule r).
Proof.
  unfold rw_rule_wf, legacy_rule; cbn [rw_holes rw_hole_sort rw_lhs rw_rhs].
  split; [apply NoDup_nodup|].
  split.
  - intro i; rewrite <- legacy_hole_present.
    destruct (existsb (Nat.eqb i) (legacy_rule_holes r)).
    + split; intro H; [exists tt; reflexivity|reflexivity].
    + split; [discriminate|intros [s Hsort]; discriminate].
  - split.
    + apply legacy_pattern_typed; intros i Hin; unfold legacy_rule_holes, legacy_variables.
      apply nodup_In, in_or_app; auto.
    + split.
      * apply legacy_pattern_typed; intros i Hin; unfold legacy_rule_holes, legacy_variables.
        apply nodup_In, in_or_app; auto.
      * destruct (rule_lhs r), (rule_rhs r); reflexivity.
Qed.

(** A sound legacy guard is invoked on exactly the translated total witness. *)
Theorem legacy_rule_sound {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (r : rewrite_rule K) :
  rule_sound ev ok r -> rw_rule_sound legacy_signature (legacy_admissible ev ok) (legacy_rule r).
Proof.
  intros Hsound sub l u Htyped Hguard Hlhs Hrhs.
  cbn [legacy_rule] in Hguard, Hlhs, Hrhs.
  rewrite (legacy_instantiate_agrees sub (rule_lhs r) l Hlhs).
  rewrite (legacy_instantiate_agrees sub (rule_rhs r) u Hrhs).
  apply legacy_equiv_agrees; exact (Hsound (legacy_total_sub sub) Hguard).
Qed.

(** * Positions and compositional replacement *)

Fixpoint legacy_set_nth {A} (i : nat) (xs : list A) (v : A) : option (list A) :=
  match i, xs with
  | 0, _ :: rest => Some (v :: rest)
  | S j, x :: rest => option_map (cons x) (legacy_set_nth j rest v)
  | _, [] => None
  end.

(** A position follows ordered application children and rejects variables or missing children. *)
Fixpoint rw_at {K Sort V} (pos : list nat) (t : rw_term K Sort V) :
    option (rw_term K Sort V) :=
  match pos with
  | [] => Some t
  | i :: rest =>
    match t with
    | RWVar _ _ => None
    | RWApp _ _ args =>
      match nth_error args i with
      | Some child => rw_at rest child
      | None => None
      end
    end
  end.

(** Replacement changes exactly the selected subtree while retaining its surrounding context. *)
Fixpoint rw_replace_at {K Sort V} (pos : list nat) (t u : rw_term K Sort V) :
    option (rw_term K Sort V) :=
  match pos with
  | [] => Some u
  | i :: rest =>
    match t with
    | RWVar _ _ => None
    | RWApp s op args =>
      match nth_error args i with
      | Some child =>
        match rw_replace_at rest child u with
        | Some replacement => option_map (RWApp s op) (legacy_set_nth i args replacement)
        | None => None
        end
      | None => None
      end
    end
  end.

(** Legacy selection is the projection of the same ordered core position. *)
Definition legacy_at {K} (pos : list nat) (t : term K) : option (term K) :=
  option_map legacy_project (rw_at pos (legacy_embed t)).

(** Legacy replacement preserves the entire context through the one-sort bridge. *)
Definition legacy_replace_at {K} (pos : list nat) (t u : term K) : option (term K) :=
  option_map legacy_project (rw_replace_at pos (legacy_embed t) (legacy_embed u)).

(** Selecting a legacy position commutes with embedding, including invalid positions. *)
Theorem legacy_at_agrees {K} (pos : list nat) (t : term K) :
  rw_at pos (legacy_embed t) = option_map legacy_embed (legacy_at pos t).
Proof.
  unfold legacy_at; destruct (rw_at pos (legacy_embed t)); cbn;
    [symmetry; f_equal; apply legacy_embed_project|reflexivity].
Qed.

(** Replacing a legacy position commutes with embedding, including invalid positions. *)
Theorem legacy_replace_agrees {K} (pos : list nat) (t u : term K) :
  rw_replace_at pos (legacy_embed t) (legacy_embed u) =
    option_map legacy_embed (legacy_replace_at pos t u).
Proof.
  unfold legacy_replace_at; destruct (rw_replace_at pos (legacy_embed t) (legacy_embed u));
    cbn; [symmetry; f_equal; apply legacy_embed_project|reflexivity].
Qed.

Lemma legacy_set_nth_relation {A} (R : A -> A -> Prop) :
  (forall x, R x x) -> forall i xs x y ys,
  nth_error xs i = Some x -> legacy_set_nth i xs y = Some ys -> R x y -> Forall2 R xs ys.
Proof.
  intros Hrefl i; induction i as [|i IHi]; intros [|a xs] x y ys Hget Hset Hxy;
    cbn in Hget, Hset; try discriminate.
  - injection Hget as <-; injection Hset as <-; constructor; [exact Hxy|].
    induction xs; constructor; auto.
  - destruct (legacy_set_nth i xs y) as [rest|] eqn:Hrest; [|discriminate].
    injection Hset as <-; constructor; [apply Hrefl|eapply IHi; eauto].
Qed.

Lemma rw_replace_at_denote {K Sort V C} (sem : rw_semantics K Sort V C) pos :
  forall t selected replacement result,
  rw_at pos t = Some selected -> rw_denote sem selected = rw_denote sem replacement ->
  rw_replace_at pos t replacement = Some result -> rw_denote sem t = rw_denote sem result.
Proof.
  induction pos as [|i pos IHpos]; intros t selected replacement result Hat Heq Hreplace.
  - cbn in Hat, Hreplace; injection Hat as <-; injection Hreplace as <-; exact Heq.
  - destruct t as [s v|s op args]; [discriminate|].
    cbn [rw_at rw_replace_at] in Hat, Hreplace.
    destruct (nth_error args i) as [child|] eqn:Hchild; [|discriminate].
    destruct (rw_replace_at pos child replacement) as [changed|] eqn:Hchanged;
      [|discriminate].
    destruct (legacy_set_nth i args changed) as [children|] eqn:Hchildren;
      [|discriminate].
    injection Hreplace as <-; rewrite !rw_denote_app.
    rewrite (rw_denote_args_agrees sem args children); [reflexivity|].
    eapply legacy_set_nth_relation; [intro a; reflexivity|exact Hchild|exact Hchildren|].
    eapply IHpos; eauto.
Qed.

Lemma legacy_replace_equiv {K C} (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) pos t selected replacement result :
  legacy_at pos t = Some selected -> equiv_term ev ok selected replacement ->
  legacy_replace_at pos t replacement = Some result -> equiv_term ev ok t result.
Proof.
  intros Hat Heq Hreplace env Hok; unfold denote.
  eapply rw_replace_at_denote.
  - rewrite legacy_at_agrees, Hat; reflexivity.
  - exact (Heq env Hok).
  - rewrite legacy_replace_agrees, Hreplace; reflexivity.
Qed.

(** * Independent external replay *)

(** A replay step records a position, a rule position, its direction and supplied bindings. *)
Record rewrite_step (K : Type) : Type := RewriteStep {
  step_pos : list nat;
  step_rule : nat;
  step_forward : bool;
  step_subst : list (term K)
}.

Arguments RewriteStep {K}.
Arguments step_pos {K}.
Arguments step_rule {K}.
Arguments step_forward {K}.
Arguments step_subst {K}.

(** A positional list index is built once before processing a sequence of steps. *)
Fixpoint legacy_list_table {A} (xs : list A) (start : nat) : Map.t nat A :=
  match xs with
  | [] => Map.empty
  | x :: rest => Map.set nat_encoding start x (legacy_list_table rest (S start))
  end.

Lemma legacy_list_table_agrees {A} (xs : list A) :
  forall start i, Map.get nat_encoding (start + i) (legacy_list_table xs start) = nth_error xs i.
Proof.
  induction xs as [|x xs IHxs]; intros start [|i]; cbn [legacy_list_table nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same.
  - rewrite Map.get_set_other by lia.
    replace (start + S i) with (S start + i) by lia; apply IHxs.
Qed.

(** A single step checks both pattern domains before inspecting its exact total substitution. *)
Definition legacy_replay_step {K} (EK : encoding K)
    (lookup : nat -> option (rewrite_rule K)) (t : term K) (step : rewrite_step K) :
    option (term K) :=
  match lookup (step_rule step) with
  | None => None
  | Some r =>
    let sub := legacy_subst (step_subst step) in
    if legacy_subst_bound (step_subst step) (rule_lhs r) &&
       legacy_subst_bound (step_subst step) (rule_rhs r) && rule_side r sub then
      let source := subst_term sub (if step_forward step then rule_lhs r else rule_rhs r) in
      let target := subst_term sub (if step_forward step then rule_rhs r else rule_lhs r) in
      match legacy_at (step_pos step) t with
      | Some actual =>
        if term_eqb EK actual source then legacy_replace_at (step_pos step) t target else None
      | None => None
      end
    else None
  end.

Fixpoint legacy_replay_from {K} (EK : encoding K)
    (lookup : nat -> option (rewrite_rule K)) (t : term K) (steps : list (rewrite_step K)) :
    option (term K) :=
  match steps with
  | [] => Some t
  | step :: rest =>
    match legacy_replay_step EK lookup t step with
    | Some u => legacy_replay_from EK lookup u rest
    | None => None
    end
  end.

(** Replay resolves rules through one prepared table and processes checked positions in order. *)
Definition replay {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t : term K)
    (steps : list (rewrite_step K)) : option (term K) :=
  let table := legacy_list_table rules 0 in
  legacy_replay_from EK (fun i => Map.get nat_encoding i table) t steps.

(** An external explanation must replay successfully and reach its claimed exact syntax. *)
Definition check_explanation {K} (EK : encoding K) (rules : list (rewrite_rule K)) (t u : term K)
    (steps : list (rewrite_step K)) : bool :=
  match replay EK rules t steps with
  | Some v => term_eqb EK v u
  | None => false
  end.

Lemma legacy_replay_step_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) lookup :
  (forall i r, lookup i = Some r -> rule_sound ev ok r) ->
  forall t step u, legacy_replay_step EK lookup t step = Some u -> equiv_term ev ok t u.
Proof.
  intros Hrules t step u Hstep; unfold legacy_replay_step in Hstep.
  destruct (lookup (step_rule step)) as [r|] eqn:Hrule; [|discriminate].
  destruct (legacy_subst_bound (step_subst step) (rule_lhs r) &&
    legacy_subst_bound (step_subst step) (rule_rhs r) &&
    rule_side r (legacy_subst (step_subst step))) eqn:Hcheck; [|discriminate].
  apply andb_true_iff in Hcheck; destruct Hcheck as [Hbounds Hguard].
  pose proof (Hrules _ r Hrule (legacy_subst (step_subst step)) Hguard) as Hsound.
  destruct (legacy_at (step_pos step) t) as [actual|] eqn:Hat; [|discriminate].
  destruct (term_eqb EK actual
    (subst_term (legacy_subst (step_subst step))
      (if step_forward step then rule_lhs r else rule_rhs r))) eqn:Heq; [|discriminate].
  apply term_eqb_spec in Heq; subst actual.
  eapply legacy_replace_equiv; [exact Hat| |exact Hstep].
  destruct (step_forward step); cbn; [exact Hsound|].
  intros env Hok; symmetry; exact (Hsound env Hok).
Qed.

Lemma legacy_replay_from_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) lookup :
  (forall i r, lookup i = Some r -> rule_sound ev ok r) ->
  forall steps t u, legacy_replay_from EK lookup t steps = Some u -> equiv_term ev ok t u.
Proof.
  intros Hrules steps; induction steps as [|step steps IHsteps]; intros t u Hreplay.
  - cbn in Hreplay; injection Hreplay as <-; intros env Hok; reflexivity.
  - cbn [legacy_replay_from] in Hreplay.
    destruct (legacy_replay_step EK lookup t step) as [v|] eqn:Hstep; [|discriminate].
    intros env Hok; transitivity (denote ev env v).
    + exact (legacy_replay_step_sound EK ev ok lookup Hrules t step v Hstep env Hok).
    + exact (IHsteps v u Hreplay env Hok).
Qed.

(** Accepted replay proves equivalence over the original typed environments and sound rules. *)
Theorem check_explanation_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (t u : term K)
    (steps : list (rewrite_step K)) :
  Forall (rule_sound ev ok) rules -> check_explanation EK rules t u steps = true ->
  equiv_term ev ok t u.
Proof.
  intros Hrules Hcheck; unfold check_explanation in Hcheck.
  destruct (replay EK rules t steps) as [v|] eqn:Hreplay; [|discriminate].
  apply term_eqb_spec in Hcheck; subst v; unfold replay in Hreplay.
  eapply legacy_replay_from_sound; [|exact Hreplay].
  intros i r Hget.
  pose proof (legacy_list_table_agrees rules 0 i) as Htable; cbn [Nat.add] in Htable.
  change (Map.get nat_encoding i (legacy_list_table rules 0) = Some r) in Hget.
  rewrite Htable in Hget.
  apply nth_error_In in Hget; rewrite Forall_forall in Hrules; auto.
Qed.

(** The empty explanation accepts every input independently of its evaluation result. *)
Theorem check_explanation_refl {K} (EK : encoding K) (rules : list (rewrite_rule K))
    (t : term K) : check_explanation EK rules t t nil = true.
Proof.
  unfold check_explanation, replay; cbn [legacy_replay_from]; apply term_eqb_spec; reflexivity.
Qed.

(** * Finite positional scheduling of the proved core *)

(** Matching supplies finite concrete witnesses; repeated holes must match the same syntax. *)
Fixpoint legacy_match {K} (EK : encoding K) (pattern actual : term K)
    (sub : Map.t nat (term K)) {struct pattern} : option (Map.t nat (term K)) :=
  match pattern with
  | TVar i =>
    match Map.get nat_encoding i sub with
    | Some previous => if term_eqb EK previous actual then Some sub else None
    | None => Some (Map.set nat_encoding i actual sub)
    end
  | TApp op ps =>
    match actual with
    | TVar _ => None
    | TApp other ts =>
      if Pos.eqb (encode EK op) (encode EK other) then
        (fix go (ps ts : list (term K)) (sub : Map.t nat (term K)) :=
          match ps, ts with
          | [], [] => Some sub
          | p :: ps, t :: ts =>
            match legacy_match EK p t sub with
            | Some next => go ps ts next
            | None => None
            end
          | _, _ => None
          end) ps ts sub
      else None
    end
  end.

(** Prepared scheduling metadata caches the finite binding-list length for each rule. *)
Record legacy_plan (K : Type) : Type := LegacyPlan {
  legacy_plan_index : nat;
  legacy_plan_rule : rewrite_rule K;
  legacy_plan_bound : nat
}.

Arguments LegacyPlan {K}.
Arguments legacy_plan_index {K}.
Arguments legacy_plan_rule {K}.
Arguments legacy_plan_bound {K}.

Definition legacy_head {K} (t : term K) : option K :=
  match t with
  | TVar _ => None
  | TApp op _ => Some op
  end.

(** A rule's operator bucket and its list-index metadata are prepared before binary iteration. *)
Fixpoint legacy_plan_table {K} (EK : encoding K) (rules : list (rewrite_rule K)) (i : nat) :
    Map.t (option K) (list (legacy_plan K)) :=
  match rules with
  | [] => Map.empty
  | r :: rest =>
    let table := legacy_plan_table EK rest (S i) in
    let key := legacy_head (rule_lhs r) in
    let plans := match Map.get (option_encoding EK) key table with
      | Some plans => plans
      | None => []
      end in
    Map.set (option_encoding EK) key
      (LegacyPlan i r (fold_right (fun j n => Nat.max (S j) n) 0 (legacy_rule_holes r)) :: plans)
      table
  end.

(** Missing rhs-only holes receive their original variable as a concrete finite witness. *)
Definition legacy_bindings {K} (bound : nat) (sub : Map.t nat (term K)) : list (term K) :=
  map (fun i => match Map.get nat_encoding i sub with
    | Some t => t
    | None => TVar i
    end) (seq 0 bound).

(** Positions carry the exact materialized subtree and the class located by a prepared memo. *)
Record legacy_position (K : Type) : Type := LegacyPosition {
  legacy_position_path : list nat;
  legacy_position_term : term K;
  legacy_position_class : rw_id
}.

Arguments LegacyPosition {K}.
Arguments legacy_position_path {K}.
Arguments legacy_position_term {K}.
Arguments legacy_position_class {K}.

(** One bottom-up traversal resolves node keys and emits positions without rescanning subtrees. *)
Fixpoint legacy_positions {K} (EK : encoding K) (g : rw_graph K unit nat)
    (memo : Map.t rw_id rw_id) (t : term K) : option rw_id * list (legacy_position K) :=
  let '(children, positions) :=
    match t with
    | TVar _ => (Some [], [])
    | TApp _ args =>
      (fix go (args : list (term K)) (i : nat) :
          option (list rw_id) * list (legacy_position K) :=
        match args with
        | [] => (Some [], [])
        | a :: rest =>
          let '(root, rows) := legacy_positions EK g memo a in
          let '(roots, others) := go rest (S i) in
          (match root, roots with
          | Some c, Some cs => Some (c :: cs)
          | _, _ => None
          end,
            map (fun row => LegacyPosition (i :: legacy_position_path row)
              (legacy_position_term row) (legacy_position_class row)) rows ++ others)
        end) args 0
    end in
  let node := match t with
    | TVar i => RWNVar tt i
    | TApp op _ => RWNApp tt op []
    end in
  let root :=
    match children with
    | None => None
    | Some ids =>
      let node := match node with
        | RWNVar s i => RWNVar s i
        | RWNApp s op _ => RWNApp s op ids
        end in
      match Map.get positive_encoding
        (encode (rw_node_encoding EK unit_encoding nat_encoding) node) memo with
      | Some n =>
        match rw_node_at g n with
        | Some (owner, _) => rw_find g owner
        | None => None
        end
      | None => None
      end
    end in
  (root, match root with
    | Some c => LegacyPosition [] t c :: positions
    | None => positions
    end).

(** An offer couples one legacy replay step to the concrete attempt submitted to the core. *)
Record legacy_offer (K : Type) : Type := LegacyOffer {
  legacy_offer_attempt : rw_attempt K unit nat nat;
  legacy_offer_step : rewrite_step K;
  legacy_offer_result : term K
}.

Arguments LegacyOffer {K}.
Arguments legacy_offer_attempt {K}.
Arguments legacy_offer_step {K}.
Arguments legacy_offer_result {K}.

Fixpoint legacy_try_plans {K} (EK : encoding K) (lookup : nat -> option (rewrite_rule K))
    (whole : term K) (position : legacy_position K) (plans : list (legacy_plan K)) :
    option (legacy_offer K) :=
  match plans with
  | [] => None
  | plan :: rest =>
    let r := legacy_plan_rule plan in
    let candidate :=
      match legacy_match EK (rule_lhs r) (legacy_position_term position) Map.empty with
      | None => None
      | Some sub =>
        let bindings := legacy_bindings (legacy_plan_bound plan) sub in
        let step := RewriteStep (legacy_position_path position) (legacy_plan_index plan)
          true bindings in
        match legacy_replay_step EK lookup whole step with
        | Some changed =>
          if term_eqb EK whole changed then None else
            Some (LegacyOffer
              (RwAttempt (legacy_plan_index plan) (legacy_position_class position)
                (legacy_list_table (map legacy_embed bindings) 0)) step changed)
        | None => None
        end
      end in
    match candidate with
    | Some offer => Some offer
    | None => legacy_try_plans EK lookup whole position rest
    end
  end.

Fixpoint legacy_choose_offer {K} (EK : encoding K) (lookup : nat -> option (rewrite_rule K))
    (plans : Map.t (option K) (list (legacy_plan K))) (whole : term K)
    (positions : list (legacy_position K)) : option (legacy_offer K) :=
  match positions with
  | [] => None
  | position :: rest =>
    let bucket := fun key => match Map.get (option_encoding EK) key plans with
      | Some ps => ps
      | None => []
      end in
    let candidate := match legacy_head (legacy_position_term position) with
      | None => legacy_try_plans EK lookup whole position (bucket None)
      | Some op =>
        match legacy_try_plans EK lookup whole position (bucket (Some op)) with
        | Some offer => Some offer
        | None => legacy_try_plans EK lookup whole position (bucket None)
        end
      end in
    match candidate with
    | Some offer => Some offer
    | None => legacy_choose_offer EK lookup plans whole rest
    end
  end.

(** Certificates share reversed trace tails; only a requested explanation is reversed at export. *)
Record legacy_state (K : Type) : Type := LegacyState {
  legacy_state_core : rw_run_state K unit nat;
  legacy_state_term : term K;
  legacy_state_steps : list (rewrite_step K);
  legacy_state_certificates : Map.t (term K) (list (rewrite_step K));
  legacy_state_stopped : bool
}.

Arguments LegacyState {K}.
Arguments legacy_state_core {K}.
Arguments legacy_state_term {K}.
Arguments legacy_state_steps {K}.
Arguments legacy_state_certificates {K}.
Arguments legacy_state_stopped {K}.

(** Each charged scheduler transition uses the existing verified runner step unchanged. *)
Definition legacy_engine_step {K} (EK : encoding K)
    (table : Map.t nat (rw_rule K unit nat nat))
    (lookup : nat -> option (rewrite_rule K))
    (plans : Map.t (option K) (list (legacy_plan K))) (st : legacy_state K) : legacy_state K :=
  let core := legacy_state_core st in
  let g := rw_run_graph (rw_run_current core) in
  let positions := snd (legacy_positions EK g
    (rw_memo (rw_node_encoding EK unit_encoding nat_encoding) g) (legacy_state_term st)) in
  match legacy_choose_offer EK lookup plans (legacy_state_term st) positions with
  | None => LegacyState core (legacy_state_term st) (legacy_state_steps st)
      (legacy_state_certificates st) true
  | Some offer =>
    let next := rw_run_step EK unit_encoding nat_encoding nat_encoding legacy_signature
      table (fun _ => Some (legacy_offer_attempt offer)) core in
    let steps := legacy_offer_step offer :: legacy_state_steps st in
    LegacyState next (legacy_offer_result offer) steps
      (Map.set (legacy_encoding EK) (legacy_offer_result offer) steps
        (legacy_state_certificates st)) false
  end.

(** The facade stores a directly produced graph and optional replay evidence beside its root. *)
Record egraph (K : Type) : Type := LegacyEgraph {
  legacy_egraph_encoding : encoding K;
  legacy_egraph_rules : list (rewrite_rule K);
  legacy_egraph_root : rw_id;
  legacy_egraph_state : legacy_state K
}.

Arguments LegacyEgraph {K}.
Arguments legacy_egraph_encoding {K}.
Arguments legacy_egraph_rules {K}.
Arguments legacy_egraph_root {K}.
Arguments legacy_egraph_state {K}.

(** The graph observer exposes the actual result of the proved Rewrite runner. *)
Definition legacy_graph {K} (eg : egraph K) : rw_graph K unit nat :=
  rw_run_graph (rw_run_current (legacy_state_core (legacy_egraph_state eg))).

(** Every facade producer retains the class allocated for its original input. *)
Definition legacy_root {K} (eg : egraph K) : option rw_id := Some (legacy_egraph_root eg).

(** Saturation uses binary fuel and a finite positional witness schedule over the direct core. *)
Definition saturate {K} (EK : encoding K) (rules : list (rewrite_rule K)) (fuel : positive)
    (t : term K) : egraph K :=
  let '(g, root) := rw_add EK unit_encoding nat_encoding rw_empty (legacy_embed t) in
  let table := rw_rule_table_from (map legacy_rule rules) 0 in
  let original := legacy_list_table rules 0 in
  let plans := legacy_plan_table EK rules 0 in
  let initial := LegacyState (rw_prepare_run EK nat_encoding g RWFuelExhausted) t []
    (Map.set (legacy_encoding EK) t [] Map.empty) false in
  LegacyEgraph EK rules root
    (rw_repeat legacy_state_stopped
      (legacy_engine_step EK table (fun i => Map.get nat_encoding i original) plans) fuel initial).

Lemma legacy_engine_step_preserved {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) rules initial lookup plans :
  Forall (rule_sound ev ok) rules -> forall st,
  rw_run_state_valid EK nat_encoding legacy_signature (legacy_admissible ev ok)
    (map legacy_rule rules) initial (legacy_state_core st) ->
  rw_run_state_valid EK nat_encoding legacy_signature (legacy_admissible ev ok)
    (map legacy_rule rules) initial
    (legacy_state_core (legacy_engine_step EK (rw_rule_table_from (map legacy_rule rules) 0)
      lookup plans st)).
Proof.
  intros Hrules st Hvalid; unfold legacy_engine_step.
  destruct (legacy_choose_offer EK lookup plans (legacy_state_term st)
    (snd (legacy_positions EK (rw_run_graph (rw_run_current (legacy_state_core st)))
      (rw_memo (rw_node_encoding EK unit_encoding nat_encoding)
        (rw_run_graph (rw_run_current (legacy_state_core st)))) (legacy_state_term st))))
      as [offer|]; [|exact Hvalid].
  cbn [legacy_state_core]; apply rw_run_step_preserved; [| |exact Hvalid].
  - apply Forall_map, Forall_forall; intros r Hin; apply legacy_rule_wf.
  - apply Forall_map; eapply Forall_impl; [|exact Hrules].
    intros r Hsound; apply legacy_rule_sound; exact Hsound.
Qed.

(** The directly proved producer retains structure, semantic equality, productivity and input. *)
Theorem legacy_saturate_direct {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (fuel : positive)
    (t : term K) :
  Forall (rule_sound ev ok) rules ->
  let eg := saturate EK rules fuel t in
  rw_graph_wf legacy_signature (legacy_graph eg) /\
  rw_graph_sound legacy_signature (legacy_admissible ev ok) (map legacy_rule rules)
    (legacy_graph eg) /\
  rw_productive (legacy_graph eg) /\
  exists c, legacy_root eg = Some c /\ rw_represents (legacy_graph eg) c (legacy_embed t).
Proof.
  intro Hrules; unfold saturate.
  destruct (rw_add EK unit_encoding nat_encoding rw_empty (legacy_embed t)) as [g root] eqn:Hadd.
  pose proof (rw_add_correct EK unit_encoding nat_encoding legacy_signature
    (legacy_admissible ev ok) (map legacy_rule rules) rw_empty (legacy_embed t)
    (rw_empty_wf legacy_signature) (rw_empty_sound legacy_signature _ _)
    rw_empty_productive (legacy_embed_typed t)) as Hinitial.
  rewrite Hadd in Hinitial; destruct Hinitial as [Hwf [Hsound [Hproductive [Hempty Hinput]]]].
  assert (Hvalid : rw_run_state_valid EK nat_encoding legacy_signature (legacy_admissible ev ok)
      (map legacy_rule rules) g
      (legacy_state_core
        (rw_repeat legacy_state_stopped
          (legacy_engine_step EK (rw_rule_table_from (map legacy_rule rules) 0)
            (fun i => Map.get nat_encoding i (legacy_list_table rules 0))
            (legacy_plan_table EK rules 0)) fuel
          (LegacyState (rw_prepare_run EK nat_encoding g RWFuelExhausted) t []
            (Map.set (legacy_encoding EK) t [] Map.empty) false)))).
  { apply (rw_repeat_preserved legacy_state_stopped _
      (fun st => rw_run_state_valid EK nat_encoding legacy_signature (legacy_admissible ev ok)
        (map legacy_rule rules) g (legacy_state_core st))).
    - apply legacy_engine_step_preserved; exact Hrules.
    - cbn [legacy_state_core]; apply rw_prepare_run_valid; try assumption.
      apply rw_extends_refl. }
  destruct Hvalid as [Hfinalwf [Hfinalsound [Hfinalproductive [Hextends Hindexes]]]].
  split; [exact Hfinalwf|]; split; [exact Hfinalsound|]; split; [exact Hfinalproductive|].
  exists root; split; [reflexivity|apply Hextends; exact Hinput].
Qed.

(** Exact core tree extraction exports a candidate only with an accepted legacy explanation. *)
Definition extract {K} (cost : K -> nat) (eg : egraph K) (t : term K) :
    option (term K * list (rewrite_step K)) :=
  let EK := legacy_egraph_encoding eg in
  match rw_extract_tree EK unit_encoding nat_encoding (fun _ => 0) cost
    (legacy_graph eg) (legacy_egraph_root eg) with
  | None => None
  | Some output =>
    let u := legacy_project output in
    match Map.get (legacy_encoding EK) u
      (legacy_state_certificates (legacy_egraph_state eg)) with
    | None => None
    | Some backwards =>
      let steps := rev backwards in
      if check_explanation EK (legacy_egraph_rules eg) t u steps then Some (u, steps) else None
    end
  end.

(** Certificate availability restricts success, while the selected tree retains core optimality. *)
Lemma legacy_extract_minimal {K} (cost : K -> nat) (eg : egraph K) (t u : term K) steps :
  rw_graph_wf legacy_signature (legacy_graph eg) -> extract cost eg t = Some (u, steps) ->
  rw_represents (legacy_graph eg) (legacy_egraph_root eg) (legacy_embed u) /\
  forall v, rw_represents (legacy_graph eg) (legacy_egraph_root eg) (legacy_embed v) ->
    term_cost cost u <= term_cost cost v.
Proof.
  intros Hwf Hextract; unfold extract in Hextract.
  destruct (rw_extract_tree (legacy_egraph_encoding eg) unit_encoding nat_encoding
    (fun _ => 0) cost (legacy_graph eg) (legacy_egraph_root eg)) as [output|] eqn:Houtput;
    [|discriminate].
  destruct (Map.get (legacy_encoding (legacy_egraph_encoding eg)) (legacy_project output)
    (legacy_state_certificates (legacy_egraph_state eg))) as [backwards|]; [|discriminate].
  destruct (check_explanation (legacy_egraph_encoding eg) (legacy_egraph_rules eg) t
    (legacy_project output) (rev backwards)); [|discriminate].
  injection Hextract as <- <-.
  destruct (rw_extract_tree_some (legacy_egraph_encoding eg) unit_encoding nat_encoding
    legacy_signature (fun _ => 0) cost (legacy_graph eg) (legacy_egraph_root eg) output
    Hwf Houtput) as [Hrep Hminimal].
  split; [now rewrite legacy_embed_project|].
  intros v Hv; unfold term_cost; rewrite legacy_embed_project; exact (Hminimal _ Hv).
Qed.

(** Facade extraction also has a direct semantic proof from the producer and core optimum. *)
Lemma legacy_extract_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) rules cost fuel t u steps :
  Forall (rule_sound ev ok) rules ->
  extract cost (saturate EK rules fuel t) t = Some (u, steps) ->
  equiv_term ev ok t u /\ term_cost cost u <= term_cost cost t.
Proof.
  intros Hrules Hextract.
  destruct (legacy_saturate_direct EK ev ok rules fuel t Hrules)
    as [Hwf [Hsound [Hproductive [root [Hroot Hinput]]]]].
  unfold legacy_root in Hroot; injection Hroot as <-.
  destruct (legacy_extract_minimal cost (saturate EK rules fuel t) t u steps Hwf Hextract)
    as [Houtput Hminimal].
  split; [|exact (Hminimal t Hinput)].
  apply legacy_equiv_agrees.
  apply (rw_equal_sound legacy_signature (legacy_admissible ev ok) (map legacy_rule rules)).
  - apply Forall_map; eapply Forall_impl; [|exact Hrules].
    intros r Hrule; apply legacy_rule_sound; exact Hrule.
  - eapply Hsound; [exact Hinput|exact Houtput].
Qed.

(** Compatibility optimisation retains its independent explanation and non-increasing cost tests. *)
Definition optimise {K} (EK : encoding K) (rules : list (rewrite_rule K)) (cost : K -> nat)
    (fuel : positive) (t : term K) : option (term K) :=
  match extract cost (saturate EK rules fuel t) t with
  | Some (u, steps) =>
    if check_explanation EK rules t u steps && Nat.leb (term_cost cost u) (term_cost cost t)
      then Some u else None
  | None => None
  end.

(** Accepted optimisation preserves complete option results and never increases tree cost. *)
Theorem optimise_sound {K C} (EK : encoding K) (ev : K -> list C -> option C)
    (ok : (nat -> option C) -> Prop) (rules : list (rewrite_rule K)) (cost : K -> nat)
    (fuel : positive) (t u : term K) :
  Forall (rule_sound ev ok) rules -> optimise EK rules cost fuel t = Some u ->
  equiv_term ev ok t u /\ term_cost cost u <= term_cost cost t.
Proof.
  intros Hrules Hoptimise; unfold optimise in Hoptimise.
  destruct (extract cost (saturate EK rules fuel t) t) as [[v steps]|]; [|discriminate].
  destruct (check_explanation EK rules t v steps &&
    Nat.leb (term_cost cost v) (term_cost cost t)) eqn:Hcheck; [|discriminate].
  injection Hoptimise as <-; apply andb_true_iff in Hcheck; destruct Hcheck as [Hcheck Hcost].
  split; [eapply check_explanation_sound; eauto|apply Nat.leb_le; exact Hcost].
Qed.
