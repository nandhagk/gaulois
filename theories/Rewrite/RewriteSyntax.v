(** * Sorted rewrite syntax and substitution

    Terms distinguish free variables from pattern holes, and signatures check complete shapes.
    For example, substituting a variable for a repeated hole duplicates that same term.
    Builds on: Rocq Stdlib lists. *)

From Stdlib Require Import List.
Import List.ListNotations.

Scheme All for list.
Scheme All for Forall.

(** * Terms and patterns *)

(** Terms retain their result sort independently of the signature's typing check. *)
Inductive rw_term (K Sort V : Type) : Type :=
  | RWVar (s : Sort) (v : V)
  | RWApp (s : Sort) (op : K) (args : list (rw_term K Sort V)).

Arguments RWVar {K Sort V}.
Arguments RWApp {K Sort V}.

(** Pattern holes and literal free variables inhabit distinct constructors. *)
Inductive rw_pattern (K Sort V H : Type) : Type :=
  | RWHole (s : Sort) (h : H)
  | RWPVar (s : Sort) (v : V)
  | RWPApp (s : Sort) (op : K) (args : list (rw_pattern K Sort V H)).

Arguments RWHole {K Sort V H}.
Arguments RWPVar {K Sort V H}.
Arguments RWPApp {K Sort V H}.

(** The sort annotation of a term is available without evaluating it. *)
Definition rw_sort {K Sort V} (t : rw_term K Sort V) : Sort :=
  match t with
  | RWVar s _ => s
  | RWApp s _ _ => s
  end.

(** The sort annotation of a pattern is independent of its hole environment. *)
Definition rwp_sort {K Sort V H} (p : rw_pattern K Sort V H) : Sort :=
  match p with
  | RWHole s _ => s
  | RWPVar s _ => s
  | RWPApp s _ _ => s
  end.

(** * Signature checking *)

(** A signature checks variable declarations and full operator shapes, including variadic ones. *)
Record rw_signature (K Sort V : Type) : Type := RwSignature {
  rw_var_sort : V -> option Sort;
  rw_operator_shape : K -> list Sort -> Sort -> bool
}.

Arguments rw_var_sort {K Sort V}.
Arguments rw_operator_shape {K Sort V}.

(** A typed application checks every child and its complete list of argument sorts. *)
Inductive rw_typed {K Sort V} (sig : rw_signature K Sort V) : rw_term K Sort V -> Prop :=
  | rw_typed_var : forall s v,
      rw_var_sort sig v = Some s -> rw_typed sig (RWVar s v)
  | rw_typed_app : forall s op args,
      Forall (rw_typed sig) args ->
      rw_operator_shape sig op (map rw_sort args) s = true ->
      rw_typed sig (RWApp s op args).

(** Pattern typing checks declared holes while preserving literal free variables. *)
Inductive rwp_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort) :
    rw_pattern K Sort V H -> Prop :=
  | rwp_typed_hole : forall s h,
      hs h = Some s -> rwp_typed sig hs (RWHole s h)
  | rwp_typed_var : forall s v,
      rw_var_sort sig v = Some s -> rwp_typed sig hs (RWPVar s v)
  | rwp_typed_app : forall s op args,
      Forall (rwp_typed sig hs) args ->
      rw_operator_shape sig op (map rwp_sort args) s = true ->
      rwp_typed sig hs (RWPApp s op args).

(** * Partial substitution *)

(** A substitution may omit a hole and never replaces a literal free variable. *)
Definition rw_substitution (K Sort V H : Type) := H -> option (rw_term K Sort V).

(** A checked substitution provides a typed term of the declared sort for every declared hole. *)
Definition rw_sub_typed {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort)
    (sub : rw_substitution K Sort V H) : Prop :=
  forall h s, hs h = Some s ->
    exists t, sub h = Some t /\ rw_sort t = s /\ rw_typed sig t.

(** Instantiation traverses children in order and stops when a hole is absent. *)
Fixpoint rw_instantiate {K Sort V H} (sub : rw_substitution K Sort V H)
    (p : rw_pattern K Sort V H) : option (rw_term K Sort V) :=
  match p with
  | RWHole _ h => sub h
  | RWPVar s v => Some (RWVar s v)
  | RWPApp s op args =>
    match (fix go (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K Sort V)) :=
      match ps with
      | [] => Some []
      | p :: rest =>
        match rw_instantiate sub p with
        | None => None
        | Some t =>
          match go rest with
          | None => None
          | Some ts => Some (t :: ts)
          end
        end
      end) args with
    | None => None
    | Some ts => Some (RWApp s op ts)
    end
  end.

(** Argument instantiation exposes the same strict traversal for list proofs and clients. *)
Definition rw_instantiate_args {K Sort V H} (sub : rw_substitution K Sort V H)
    (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K Sort V)) :=
  (fix go (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K Sort V)) :=
    match ps with
    | [] => Some []
    | p :: rest =>
      match rw_instantiate sub p with
      | None => None
      | Some t =>
        match go rest with
        | None => None
        | Some ts => Some (t :: ts)
        end
      end
    end) ps.

Lemma rw_instantiate_app {K Sort V H} (sub : rw_substitution K Sort V H) s op args :
  rw_instantiate sub (RWPApp s op args) =
    match rw_instantiate_args sub args with
    | None => None
    | Some ts => Some (RWApp s op ts)
    end.
Proof.
  reflexivity.
Qed.

(** Nested induction supplies one hypothesis for every typed application child. *)
Lemma rwp_typed_ind_all {K Sort V H} (sig : rw_signature K Sort V) (hs : H -> option Sort)
    (P : rw_pattern K Sort V H -> Prop)
    (Hhole : forall s h, hs h = Some s -> P (RWHole s h))
    (Hvar : forall s v, rw_var_sort sig v = Some s -> P (RWPVar s v))
    (Happ : forall s op args, Forall (rwp_typed sig hs) args -> Forall P args ->
      rw_operator_shape sig op (map rwp_sort args) s = true -> P (RWPApp s op args)) :
  forall p, rwp_typed sig hs p -> P p.
Proof.
  fix IH 2.
  intros p Htyped.
  destruct Htyped as [s h Hsort|s v Hsort|s op args Hargs Hshape].
  - exact (Hhole s h Hsort).
  - exact (Hvar s v Hsort).
  - apply Happ; [exact Hargs| |exact Hshape].
    clear Hshape.
    induction Hargs as [|p ps Hp Hps IHps].
    + constructor.
    + constructor; [exact (IH p Hp)|exact IHps].
Qed.

Lemma rw_instantiate_args_typed {K Sort V H} (sig : rw_signature K Sort V)
    (sub : rw_substitution K Sort V H) (ps : list (rw_pattern K Sort V H)) :
  Forall (fun p => exists t, rw_instantiate sub p = Some t /\
    rw_typed sig t /\ rw_sort t = rwp_sort p) ps ->
  exists ts, rw_instantiate_args sub ps = Some ts /\
    Forall (rw_typed sig) ts /\ map rw_sort ts = map rwp_sort ps.
Proof.
  intros Hargs.
  induction Hargs as [|p ps [t [Hinst [Htyped Hsort]]] Hps [ts [Hinsts [Htypeds Hsorts]]]].
  - exists []; split; [reflexivity|split; [constructor|reflexivity]].
  - exists (t :: ts).
    split.
    + change (match rw_instantiate sub p with
        | None => None
        | Some u =>
          match rw_instantiate_args sub ps with
          | None => None
          | Some us => Some (u :: us)
          end
        end = Some (t :: ts)).
      rewrite Hinst, Hinsts; reflexivity.
    + split; [now constructor|cbn; now rewrite Hsort, Hsorts].
Qed.

(** Checked substitution always instantiates a typed pattern at its annotated sort. *)
Theorem rw_instantiate_typed {K Sort V H} (sig : rw_signature K Sort V)
    (hs : H -> option Sort) (sub : rw_substitution K Sort V H) (p : rw_pattern K Sort V H) :
  rwp_typed sig hs p -> rw_sub_typed sig hs sub ->
  exists t, rw_instantiate sub p = Some t /\ rw_typed sig t /\ rw_sort t = rwp_sort p.
Proof.
  intros Htyped Hsub.
  apply (rwp_typed_ind_all sig hs
    (fun p => exists t, rw_instantiate sub p = Some t /\
      rw_typed sig t /\ rw_sort t = rwp_sort p)); [| | |exact Htyped].
  - intros s h Hsort.
    destruct (Hsub h s Hsort) as [t [Hinst [Hsortt Htypedt]]].
    exists t; split; [exact Hinst|split; assumption].
  - intros s v Hsort.
    exists (RWVar s v); split; [reflexivity|split; [now constructor|reflexivity]].
  - intros s op args Hargs IHargs Hshape.
    destruct (rw_instantiate_args_typed sig sub args IHargs)
      as [ts [Hinst [Htypeds Hsorts]]].
    exists (RWApp s op ts); split.
    + rewrite rw_instantiate_app, Hinst; reflexivity.
    + split; [apply rw_typed_app; [exact Htypeds|now rewrite Hsorts]|reflexivity].
Qed.
