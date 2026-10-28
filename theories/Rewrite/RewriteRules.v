(** * Partial rewrite semantics and guarded rules

    Interpretations evaluate terms strictly, and clients supply soundness proofs for their rules.
    For example, two undefined operator applications have equal option results.
    Builds on: RewriteSyntax and Rocq Stdlib lists. *)

From Stdlib Require Import List.
From Gaulois.Rewrite Require Import RewriteSyntax.
Import List.ListNotations.

(** A semantics supplies partial values for variables and partial operator interpretations. *)
Record rw_semantics (K Sort V C : Type) : Type := RwSemantics {
  rw_var_value : V -> option C;
  rw_eval_op : K -> list C -> option C
}.

Arguments rw_var_value {K Sort V C}.
Arguments rw_eval_op {K Sort V C}.

(** Evaluation checks children from left to right before applying the partial operator. *)
Fixpoint rw_denote {K Sort V C} (sem : rw_semantics K Sort V C)
    (t : rw_term K Sort V) : option C :=
  match t with
  | RWVar _ v => rw_var_value sem v
  | RWApp _ op args =>
    match (fix go (ts : list (rw_term K Sort V)) : option (list C) :=
      match ts with
      | [] => Some []
      | t :: rest =>
        match rw_denote sem t with
        | None => None
        | Some c =>
          match go rest with
          | None => None
          | Some cs => Some (c :: cs)
          end
        end
      end) args with
    | None => None
    | Some cs => rw_eval_op sem op cs
    end
  end.

(** Argument evaluation exposes the strict traversal without invoking an operator. *)
Definition rw_denote_args {K Sort V C} (sem : rw_semantics K Sort V C)
    (ts : list (rw_term K Sort V)) : option (list C) :=
  (fix go (ts : list (rw_term K Sort V)) : option (list C) :=
    match ts with
    | [] => Some []
    | t :: rest =>
      match rw_denote sem t with
      | None => None
      | Some c =>
        match go rest with
        | None => None
        | Some cs => Some (c :: cs)
        end
      end
    end) ts.

Lemma rw_denote_args_cons {K Sort V C} (sem : rw_semantics K Sort V C) t ts :
  rw_denote_args sem (t :: ts) =
    match rw_denote sem t with
    | None => None
    | Some c =>
      match rw_denote_args sem ts with
      | None => None
      | Some cs => Some (c :: cs)
      end
    end.
Proof.
  reflexivity.
Qed.

Lemma rw_denote_app {K Sort V C} (sem : rw_semantics K Sort V C) s op args :
  rw_denote sem (RWApp s op args) =
    match rw_denote_args sem args with
    | None => None
    | Some cs => rw_eval_op sem op cs
    end.
Proof.
  reflexivity.
Qed.

(** Semantic equality compares complete option results in every admissible interpretation. *)
Definition rw_equiv {K Sort V C} (admissible : rw_semantics K Sort V C -> Prop)
    (t u : rw_term K Sort V) : Prop :=
  forall sem, admissible sem -> rw_denote sem t = rw_denote sem u.

(** Rules declare their finite hole domain, patterns and substitution-dependent guard. *)
Record rw_rule (K Sort V H : Type) : Type := RwRule {
  rw_holes : list H;
  rw_hole_sort : H -> option Sort;
  rw_lhs : rw_pattern K Sort V H;
  rw_rhs : rw_pattern K Sort V H;
  rw_condition : rw_substitution K Sort V H -> bool
}.

Arguments rw_holes {K Sort V H}.
Arguments rw_hole_sort {K Sort V H}.
Arguments rw_lhs {K Sort V H}.
Arguments rw_rhs {K Sort V H}.
Arguments rw_condition {K Sort V H}.

(** Well-formed rules declare exactly their hole environment and preserve the result sort. *)
Definition rw_rule_wf {K Sort V H} (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) : Prop :=
  NoDup (rw_holes r) /\
  (forall h, In h (rw_holes r) <-> exists s, rw_hole_sort r h = Some s) /\
  rwp_typed sig (rw_hole_sort r) (rw_lhs r) /\
  rwp_typed sig (rw_hole_sort r) (rw_rhs r) /\
  rwp_sort (rw_lhs r) = rwp_sort (rw_rhs r).

(** A sound rule preserves option results whenever its checked substitution satisfies the guard. *)
Definition rw_rule_sound {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (r : rw_rule K Sort V H) : Prop :=
  forall sub l r', rw_sub_typed sig (rw_hole_sort r) sub -> rw_condition r sub = true ->
    rw_instantiate sub (rw_lhs r) = Some l -> rw_instantiate sub (rw_rhs r) = Some r' ->
    rw_equiv admissible l r'.
