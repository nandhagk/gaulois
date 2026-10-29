(** * Checked bounded rewriting

    The runner validates finite substitutions and source membership before merging a rule result.
    For example, a false guard consumes an attempt while retaining the original graph.
    Builds on: RewriteSyntax, RewriteRules, RewriteEquality, RewriteEgraph and RewriteRebuild. *)

From Stdlib Require Import List Bool NArith PeanoNat Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteMatch.
Import List.ListNotations.

(** * Finite typed substitutions *)

(** An attempt carries a rule position, a source class and finite concrete hole witnesses. *)
Record rw_attempt (K Sort V H : Type) : Type := RwAttempt {
  rw_attempt_rule : nat;
  rw_attempt_root : rw_id;
  rw_attempt_sub : Map.t H (rw_term K Sort V)
}.

Arguments RwAttempt {K Sort V H}.
Arguments rw_attempt_rule {K Sort V H}.
Arguments rw_attempt_root {K Sort V H}.
Arguments rw_attempt_sub {K Sort V H}.

(** Finite map lookup is the exact substitution passed to instantiation and the guard. *)
Definition rw_attempt_substitution {K Sort V H} (EH : encoding H)
    (a : rw_attempt K Sort V H) : rw_substitution K Sort V H :=
  fun h => Map.get EH h (rw_attempt_sub a).

(** Recursive typing checks each variable declaration and the full application shape. *)
Fixpoint rw_type_test {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V)
    (t : rw_term K Sort V) : bool :=
  match t with
  | RWVar s v =>
    match rw_var_sort sig v with
    | Some ty => if rw_key_eq_dec ES s ty then true else false
    | None => false
    end
  | RWApp s op ts =>
    forallb (rw_type_test ES sig) ts && rw_operator_shape sig op (map rw_sort ts) s
  end.

Lemma rw_forall_test_spec {A} (f : A -> bool) (P : A -> Prop) xs :
  Forall (fun x => f x = true <-> P x) xs ->
  (forallb f xs = true <-> Forall P xs).
Proof.
  intro Hspec; induction Hspec as [|x xs Hx Hxs IHxs]; cbn.
  - split; [intro H; constructor|intro H; reflexivity].
  - rewrite andb_true_iff, Hx, IHxs; split.
    + intros [Hhead Htail]; now constructor.
    + intro H; inversion H; auto.
Qed.

(** The recursive typing test recognizes exactly the signature's typing judgment. *)
Lemma rw_type_test_spec {K Sort V} (ES : encoding Sort) (sig : rw_signature K Sort V) t :
  rw_type_test ES sig t = true <-> rw_typed sig t.
Proof.
  induction t as [s v|s op ts IHts].
  - cbn [rw_type_test]; destruct (rw_var_sort sig v) as [ty|] eqn:Hsort.
    + destruct (rw_key_eq_dec ES s ty) as [->|Hne]; split; intro H.
      * now constructor.
      * reflexivity.
      * discriminate.
      * inversion H; congruence.
    + split; intro H; [discriminate|inversion H; congruence].
  - assert (Hspec : Forall (fun t => rw_type_test ES sig t = true <-> rw_typed sig t) ts).
    { induction IHts as [|t Ht ts Hts IHts]; constructor; assumption. }
    cbn [rw_type_test]; rewrite andb_true_iff, (rw_forall_test_spec _ _ _ Hspec).
    split.
    + intros [Hargs Hshape]; now constructor.
    + intro H; inversion H; auto.
Qed.

(** Every listed hole must have a recursively typed binding at its declared sort. *)
Definition rw_check_sub {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) : bool :=
  forallb (fun h =>
    match rw_hole_sort r h, sub h with
    | Some s, Some t =>
      if rw_key_eq_dec ES (rw_sort t) s then rw_type_test ES sig t else false
    | _, _ => false
    end) (rw_holes r).

(** Successful finite checking provides all bindings required by the rule's hole environment. *)
Theorem rw_check_sub_sound {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_check_sub EK ES EV EH sig r sub = true ->
  rw_sub_typed sig (rw_hole_sort r) sub.
Proof.
  intros [_ [Hholes Hrest]] Hcheck h s Hsort.
  apply forallb_forall with (x := h) in Hcheck.
  - rewrite Hsort in Hcheck; destruct (sub h) as [t|] eqn:Hsub; [|discriminate].
    destruct (rw_key_eq_dec ES (rw_sort t) s) as [Heq|Hne]; [|discriminate].
    exists t; split; [reflexivity|]; split; [exact Heq|].
    apply (proj1 (rw_type_test_spec ES sig t)); exact Hcheck.
  - apply Hholes; eauto.
Qed.

(** Every well-typed substitution for a well-formed rule passes the finite checker. *)
Theorem rw_check_sub_complete {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (r : rw_rule K Sort V H) (sub : rw_substitution K Sort V H) :
  rw_rule_wf sig r -> rw_sub_typed sig (rw_hole_sort r) sub ->
  rw_check_sub EK ES EV EH sig r sub = true.
Proof.
  intros [_ [Hholes Hrest]] Hsub; apply forallb_forall; intros h Hin.
  apply Hholes in Hin; destruct Hin as [s Hsort].
  destruct (Hsub h s Hsort) as [t [Hget [Hty Htyped]]].
  rewrite Hsort, Hget.
  destruct (rw_key_eq_dec ES (rw_sort t) s) as [Heq|Hne]; [|contradiction].
  apply (proj2 (rw_type_test_spec ES sig t)); exact Htyped.
Qed.

(** * Indexed finite-term membership *)

(** Child checks preserve arity and order while descending through a finite term. *)
Fixpoint rw_rep_children (fs : list (rw_id -> bool)) (ids : list rw_id) : bool :=
  match fs, ids with
  | [], [] => true
  | f :: rest, id :: ids => f id && rw_rep_children rest ids
  | _, _ => false
  end.

Lemma rw_rep_children_spec {K Sort V} (g : rw_graph K Sort V) ts fs :
  Forall2 (fun t f => forall c, f c = true <-> rw_represents g c t) ts fs ->
  forall ids, rw_rep_children fs ids = true <-> Forall2 (rw_represents g) ids ts.
Proof.
  intro Hfs; induction Hfs as [|t f ts fs Hf Hfs IHfs]; intros [|id ids]; cbn;
    split; intro H; try discriminate; try (inversion H).
  - constructor.
  - reflexivity.
  - apply andb_true_iff in H; destruct H as [Hhead Htail].
    constructor; [apply Hf; exact Hhead|apply IHfs; exact Htail].
  - inversion H as [|id' t' ids' ts' Hhead Htail]; subst.
    apply andb_true_iff; split; [apply Hf; exact Hhead|apply IHfs; exact Htail].
Qed.

(** Prepared operator and variable buckets avoid scanning all graph nodes at recursive calls. *)
Fixpoint rw_rep_on {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (ops : Map.t K (list rw_id))
    (vars : Map.t V (list rw_id)) (t : rw_term K Sort V) (c : rw_id) {struct t} : bool :=
  match t with
  | RWVar s v =>
    existsb (fun n =>
      match rw_node_at g n with
      | Some (owner, RWNVar ty w) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EV v w then rw_same_class g c owner else false
        else false
      | _ => false
      end) (rw_lookup_list EV v vars)
  | RWApp s op ts =>
    existsb (fun n =>
      match rw_node_at g n with
      | Some (owner, RWNApp ty other ids) =>
        if rw_key_eq_dec ES s ty then
          if rw_key_eq_dec EK op other then
            rw_same_class g c owner &&
              rw_rep_children (map (rw_rep_on EK ES EV g ops vars) ts) ids
          else false
        else false
      | _ => false
      end) (rw_lookup_list EK op ops)
  end.

Lemma rw_rep_on_spec {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) ops vars :
  rw_table_incidence EK g rw_operator_keys ops ->
  rw_table_incidence EV g rw_variable_keys vars ->
  forall t c, rw_rep_on EK ES EV g ops vars t c = true <-> rw_represents g c t.
Proof.
  intros [Hops Hopsinc] [Hvars Hvarsinc] t; induction t as [s v|s op ts IHts]; intro c.
  - cbn [rw_rep_on]; rewrite existsb_exists; split.
    + intros [n [Hin Htest]].
      destruct (rw_node_at g n) as [[owner [ty w|ty other ids]]|] eqn:Hnode;
        try discriminate.
      destruct (rw_key_eq_dec ES s ty) as [->|Hne]; [|discriminate].
      destruct (rw_key_eq_dec EV v w) as [->|Hne]; [|discriminate].
      apply rw_same_class_spec in Htest; destruct Htest as [root [Hc Ho]].
      eapply rw_repr_var; eauto.
    + intro Hrepr; inversion Hrepr as [id n owner root ty w Hnode Ho Hc|]; subst.
      exists n; split.
      * apply Hvarsinc; exists owner, (RWNVar s v); cbn; auto.
      * rewrite Hnode.
        destruct (rw_key_eq_dec ES s s) as [Heq|Hne]; [|contradiction].
        destruct (rw_key_eq_dec EV v v) as [Heqv|Hnev]; [|contradiction].
        apply rw_same_class_spec; eauto.
  - assert (Hfs : Forall2 (fun t f => forall c,
        f c = true <-> rw_represents g c t) ts (map (rw_rep_on EK ES EV g ops vars) ts)).
    { induction IHts as [|t Ht ts Hts IHts]; cbn; constructor; assumption. }
    cbn [rw_rep_on]; rewrite existsb_exists; split.
    + intros [n [Hin Htest]].
      destruct (rw_node_at g n) as [[owner [ty w|ty other ids]]|] eqn:Hnode;
        try discriminate.
      destruct (rw_key_eq_dec ES s ty) as [->|Hne]; [|discriminate].
      destruct (rw_key_eq_dec EK op other) as [->|Hne]; [|discriminate].
      apply andb_true_iff in Htest; destruct Htest as [Hsame Hchildren].
      apply rw_same_class_spec in Hsame; destruct Hsame as [root [Hc Ho]].
      eapply rw_repr_app; [exact Hnode|exact Ho|exact Hc|].
      apply (proj1 (rw_rep_children_spec g ts _ Hfs ids)); exact Hchildren.
    + intro Hrepr.
      inversion Hrepr as [|id n owner root ty other ids us Hnode Ho Hc Hchildren]; subst.
      exists n; split.
      * apply Hopsinc; exists owner, (RWNApp s op ids); cbn; auto.
      * rewrite Hnode.
        destruct (rw_key_eq_dec ES s s) as [Heq|Hne]; [|contradiction].
        destruct (rw_key_eq_dec EK op op) as [Heqop|Hneop]; [|contradiction].
        apply andb_true_iff; split.
        -- apply rw_same_class_spec; eauto.
        -- apply (proj2 (rw_rep_children_spec g ts _ Hfs ids)); exact Hchildren.
Qed.

(** Membership builds its finite incidence tables once, including on cyclic graphs. *)
Definition rw_rep_test {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (g : rw_graph K Sort V) (c : rw_id) (t : rw_term K Sort V) : bool :=
  rw_rep_on EK ES EV g (rw_build_table EK g rw_operator_keys)
    (rw_build_table EV g rw_variable_keys) t c.

(** Membership testing recognizes exactly finite representation in any well-formed graph. *)
Theorem rw_rep_test_spec {K Sort V} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (sig : rw_signature K Sort V) (g : rw_graph K Sort V) (c : rw_id)
    (t : rw_term K Sort V) :
  rw_graph_wf sig g -> (rw_rep_test EK ES EV g c t = true <-> rw_represents g c t).
Proof.
  intro Hwf; apply rw_rep_on_spec; apply (rw_build_table_correct _ sig); exact Hwf.
Qed.

(** * Atomic rule application *)

(** Application accepts prepared lookup and membership operations for bounded scheduling. *)
Definition rw_apply_using {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (lookup : nat -> option (rw_rule K Sort V H))
    (member : rw_id -> rw_term K Sort V -> bool)
    (g : rw_graph K Sort V) (a : rw_attempt K Sort V H) : option (rw_graph K Sort V) :=
  match lookup (rw_attempt_rule a) with
  | None => None
  | Some r =>
    let sub := rw_attempt_substitution EH a in
    if rw_check_sub EK ES EV EH sig r sub && rw_condition r sub then
      match rw_instantiate sub (rw_lhs r), rw_instantiate sub (rw_rhs r) with
      | Some lhs, Some rhs =>
        if member (rw_attempt_root a) lhs then
          let '(added, c) := rw_add EK ES EV g rhs in
          match rw_union ES added (rw_attempt_root a) c with
          | Some merged => Some (rw_rebuild EK ES EV merged)
          | None => None
          end
        else None
      | _, _ => None
      end
    else None
  end.

(** Standalone application prepares membership indexes for this graph phase. *)
Definition rw_apply_lookup {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (lookup : nat -> option (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a : rw_attempt K Sort V H) : option (rw_graph K Sort V) :=
  rw_apply_using EK ES EV EH sig lookup (rw_rep_test EK ES EV g) g a.

(** Rejections expose no tentative additions; successes rebuild the justified union. *)
Definition rw_apply {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) (a : rw_attempt K Sort V H) : option (rw_graph K Sort V) :=
  rw_apply_lookup EK ES EV EH sig (nth_error rules) g a.

(** Sound graph classes make one justified pair of representatives sufficient for union. *)
Lemma rw_equal_joinable {K Sort V H C} (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g : rw_graph K Sort V) a b lhs rhs :
  rw_graph_sound sig admissible rules g -> rw_represents g a lhs ->
  rw_represents g b rhs -> rw_equal sig admissible rules lhs rhs ->
  rw_joinable sig admissible rules g a b.
Proof.
  intros Hsound Hlhs Hrhs Hequal; split; [eauto|]; split; [eauto|].
  intros t u Ht Hu; eapply rw_eq_trans; [exact (Hsound a t lhs Ht Hlhs)|].
  eapply rw_eq_trans; [exact Hequal|exact (Hsound b rhs u Hrhs Hu)].
Qed.

(** An accepted rule application directly preserves the graph invariants and existing terms. *)
Theorem rw_apply_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (g g' : rw_graph K Sort V) (a : rw_attempt K Sort V H) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_apply EK ES EV EH sig rules g a = Some g' ->
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_clean g' /\ rw_extends g g'.
Proof.
  intros Hrules Hsoundrules Hwf Hsound Hproductive Happly.
  unfold rw_apply, rw_apply_lookup, rw_apply_using in Happly.
  destruct (nth_error rules (rw_attempt_rule a)) as [r|] eqn:Hrule; [|discriminate].
  set (sub := rw_attempt_substitution EH a) in *.
  destruct (rw_check_sub EK ES EV EH sig r sub && rw_condition r sub) eqn:Hcheck;
    [|discriminate].
  apply andb_true_iff in Hcheck; destruct Hcheck as [Hsub Hguard].
  destruct (rw_instantiate sub (rw_lhs r)) as [lhs|] eqn:Hlhs;
    destruct (rw_instantiate sub (rw_rhs r)) as [rhs|] eqn:Hrhs; try discriminate.
  destruct (rw_rep_test EK ES EV g (rw_attempt_root a) lhs) eqn:Hrep; [|discriminate].
  destruct (rw_add EK ES EV g rhs) as [added c] eqn:Hadd.
  destruct (rw_union ES added (rw_attempt_root a) c) as [merged|] eqn:Hunion;
    [|discriminate].
  injection Happly as <-.
  assert (Hin : In r rules) by (apply nth_error_In in Hrule; exact Hrule).
  assert (Hrulewf : rw_rule_wf sig r) by (rewrite Forall_forall in Hrules; auto).
  pose proof (rw_check_sub_sound EK ES EV EH sig r sub Hrulewf Hsub) as Htypedsub.
  destruct Hrulewf as [_ [_ [Hlhstyped [Hrhstyped Hsort]]]].
  destruct (rw_instantiate_typed sig _ sub _ Hrhstyped Htypedsub)
    as [term [Hterm [Htyped Htermsort]]].
  assert (term = rhs) by congruence; subst term.
  pose proof (rw_add_correct EK ES EV sig admissible rules g rhs
    Hwf Hsound Hproductive Htyped) as Hadded.
  rewrite Hadd in Hadded; destruct Hadded as [Hawf [Hasound [Haproductive [Haext Harhs]]]].
  apply (proj1 (rw_rep_test_spec EK ES EV sig g _ _ Hwf)) in Hrep.
  assert (Hjoin : rw_joinable sig admissible rules added (rw_attempt_root a) c).
  { eapply rw_equal_joinable; [exact Hasound|apply Haext; exact Hrep|exact Harhs|].
    eapply rw_eq_rule; eauto. }
  destruct (rw_union_correct ES sig admissible rules added merged _ _
    Hawf Hasound Haproductive Hjoin Hunion) as [Hmwf [Hmsound [Hmproductive [Hmext Hfind]]]].
  destruct (rw_rebuild_correct EK ES EV sig admissible rules merged Hmwf Hmsound Hmproductive)
    as [Hrwf [Hrsound [Hrproductive [Hclean Hrext]]]].
  do 4 (split; [assumption|]).
  eapply rw_extends_trans; [exact Haext|].
  eapply rw_extends_trans; eauto.
Qed.

(** * Binary bounded scheduling *)

(** Stopping records a consumer decision or exhausted fuel, without a saturation claim. *)
Inductive rw_stop : Type :=
  | RWStopped
  | RWFuelExhausted.

(** A run returns the graph reached and its observed stopping reason. *)
Record rw_run_result (K Sort V : Type) : Type := RwRunResult {
  rw_run_graph : rw_graph K Sort V;
  rw_run_stop : rw_stop
}.

Arguments RwRunResult {K Sort V}.
Arguments rw_run_graph {K Sort V}.
Arguments rw_run_stop {K Sort V}.

(** The consumer chooses the next attempt from the current graph or explicitly stops. *)
Definition rw_strategy (K Sort V H : Type) :=
  rw_graph K Sort V -> option (rw_attempt K Sort V H).

(** Rule positions are indexed once before entering the scheduling loop. *)
Fixpoint rw_rule_table_from {K Sort V H} (rules : list (rw_rule K Sort V H))
    (start : nat) : Map.t nat (rw_rule K Sort V H) :=
  match rules with
  | [] => Map.empty
  | r :: rest => Map.set nat_encoding start r (rw_rule_table_from rest (S start))
  end.

Lemma rw_rule_table_lookup {K Sort V H} (rules : list (rw_rule K Sort V H)) :
  forall start index, Map.get nat_encoding (start + index) (rw_rule_table_from rules start) =
    nth_error rules index.
Proof.
  induction rules as [|r rest IHrest]; intros start [|index]; cbn [rw_rule_table_from nth_error].
  - apply Map.get_empty.
  - apply Map.get_empty.
  - rewrite Nat.add_0_r; apply Map.get_set_same.
  - rewrite Map.get_set_other by lia.
    replace (start + S index) with (S start + index) by lia; apply IHrest.
Qed.

(** Prepared rule lookup agrees with the public list-position interface, including absent rules. *)
Lemma rw_apply_indexed_agrees {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (rules : list (rw_rule K Sort V H)) g a :
  rw_apply_lookup EK ES EV EH sig
    (fun index => Map.get nat_encoding index (rw_rule_table_from rules 0)) g a =
    rw_apply EK ES EV EH sig rules g a.
Proof.
  unfold rw_apply, rw_apply_lookup, rw_apply_using.
  pose proof (rw_rule_table_lookup rules 0 (rw_attempt_rule a)) as Hlookup.
  cbn [Nat.add] in Hlookup; rewrite Hlookup; reflexivity.
Qed.

(** Reusing valid membership indexes preserves every acceptance and rejection outcome. *)
Lemma rw_apply_prepared_agrees {K Sort V H} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (lookup : nat -> option (rw_rule K Sort V H)) g ops vars a :
  rw_graph_wf sig g -> rw_table_incidence EK g rw_operator_keys ops ->
  rw_table_incidence EV g rw_variable_keys vars ->
  rw_apply_using EK ES EV EH sig lookup
    (fun c t => rw_rep_on EK ES EV g ops vars t c) g a =
    rw_apply_lookup EK ES EV EH sig lookup g a.
Proof.
  intros Hwf Hops Hvars.
  assert (Hmember : forall c t, rw_rep_on EK ES EV g ops vars t c =
      rw_rep_test EK ES EV g c t).
  { intros c t.
    pose proof (rw_rep_on_spec EK ES EV g ops vars Hops Hvars t c) as Hon.
    pose proof (rw_rep_test_spec EK ES EV sig g c t Hwf) as Htest.
    destruct (rw_rep_on EK ES EV g ops vars t c);
      destruct (rw_rep_test EK ES EV g c t); try reflexivity; exfalso; intuition discriminate. }
  unfold rw_apply_lookup, rw_apply_using.
  destruct (lookup (rw_attempt_rule a)) as [r|]; [|reflexivity].
  destruct (rw_check_sub EK ES EV EH sig r (rw_attempt_substitution EH a) &&
    rw_condition r (rw_attempt_substitution EH a)); [|reflexivity].
  destruct (rw_instantiate (rw_attempt_substitution EH a) (rw_lhs r));
    destruct (rw_instantiate (rw_attempt_substitution EH a) (rw_rhs r)); try reflexivity.
  rewrite Hmember; reflexivity.
Qed.

(** Prepared source indexes survive rejected attempts and are refreshed after graph changes. *)
Record rw_run_state (K Sort V : Type) : Type := RwRunState {
  rw_run_current : rw_run_result K Sort V;
  rw_run_ops : Map.t K (list rw_id);
  rw_run_vars : Map.t V (list rw_id)
}.

Arguments RwRunState {K Sort V}.
Arguments rw_run_current {K Sort V}.
Arguments rw_run_ops {K Sort V}.
Arguments rw_run_vars {K Sort V}.

(** Preparing a graph phase constructs both source-membership tables exactly once. *)
Definition rw_prepare_run {K Sort V} (EK : encoding K) (EV : encoding V)
    (g : rw_graph K Sort V) (reason : rw_stop) : rw_run_state K Sort V :=
  RwRunState (RwRunResult g reason) (rw_build_table EK g rw_operator_keys)
    (rw_build_table EV g rw_variable_keys).

(** One charged attempt retains the original graph on every rejection path. *)
Definition rw_run_step {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (table : Map.t nat (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (st : rw_run_state K Sort V) :
    rw_run_state K Sort V :=
  match rw_run_stop (rw_run_current st) with
  | RWStopped => st
  | RWFuelExhausted =>
    let g := rw_run_graph (rw_run_current st) in
    match strategy g with
    | None => RwRunState (RwRunResult g RWStopped) (rw_run_ops st) (rw_run_vars st)
    | Some a =>
      match rw_apply_using EK ES EV EH sig (fun index => Map.get nat_encoding index table)
        (fun c t => rw_rep_on EK ES EV g (rw_run_ops st) (rw_run_vars st) t c) g a with
      | Some accepted => rw_prepare_run EK EV accepted RWFuelExhausted
      | None => st
      end
    end
  end.

(** The stopping flag lets binary iteration skip all remaining fuel after a consumer stop. *)
Definition rw_run_done {K Sort V} (st : rw_run_state K Sort V) : bool :=
  match rw_run_stop (rw_run_current st) with
  | RWStopped => true
  | RWFuelExhausted => false
  end.

(** Repeated binary steps preserve any invariant maintained by an individual step. *)
Lemma rw_repeat_preserved {A} (done : A -> bool) (step : A -> A) (P : A -> Prop) fuel :
  (forall st, P st -> P (step st)) -> forall st, P st -> P (rw_repeat done step fuel st).
Proof.
  intro Hstep; induction fuel as [p IHp|p IHp|]; intros st Hst; cbn [rw_repeat];
    destruct (done st); [exact Hst| |exact Hst| |exact Hst|].
  - apply IHp, IHp, Hstep; exact Hst.
  - apply IHp, IHp; exact Hst.
  - apply Hstep; exact Hst.
Qed.

(** Zero fuel performs no work, and positive binary fuel stops immediately when requested. *)
Definition rw_run {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (EH : encoding H) (sig : rw_signature K Sort V) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
    rw_run_result K Sort V :=
  match fuel with
  | N0 => RwRunResult g RWFuelExhausted
  | Npos p =>
    let table := rw_rule_table_from rules 0 in
    rw_run_current (rw_repeat rw_run_done (rw_run_step EK ES EV EH sig table strategy) p
      (rw_prepare_run EK EV g RWFuelExhausted))
  end.

(** The scheduling invariant ties both prepared tables to the same current graph. *)
Definition rw_run_state_valid {K Sort V H C} (EK : encoding K) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) (initial : rw_graph K Sort V)
    (st : rw_run_state K Sort V) : Prop :=
  let g := rw_run_graph (rw_run_current st) in
  rw_graph_wf sig g /\ rw_graph_sound sig admissible rules g /\ rw_productive g /\
  rw_extends initial g /\ rw_table_incidence EK g rw_operator_keys (rw_run_ops st) /\
  rw_table_incidence EV g rw_variable_keys (rw_run_vars st).

Lemma rw_prepare_run_valid {K Sort V H C} (EK : encoding K) (EV : encoding V)
    (sig : rw_signature K Sort V) (admissible : rw_semantics K Sort V C -> Prop)
    (rules : list (rw_rule K Sort V H)) initial g reason :
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  rw_extends initial g ->
  rw_run_state_valid EK EV sig admissible rules initial (rw_prepare_run EK EV g reason).
Proof.
  intros Hwf Hsound Hproductive Hext; unfold rw_run_state_valid; cbn [rw_prepare_run].
  do 4 (split; [assumption|]); split; apply (rw_build_table_correct _ sig); exact Hwf.
Qed.

Lemma rw_run_step_preserved {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) initial :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  forall st, rw_run_state_valid EK EV sig admissible rules initial st ->
  rw_run_state_valid EK EV sig admissible rules initial
    (rw_run_step EK ES EV EH sig (rw_rule_table_from rules 0) strategy st).
Proof.
  intros Hrules Hsoundrules [[current reason] ops vars] Hvalid.
  destruct Hvalid as [Hwf [Hsound [Hproductive [Hext [Hops Hvars]]]]].
  destruct reason; [exact (conj Hwf (conj Hsound (conj Hproductive
    (conj Hext (conj Hops Hvars)))))|].
  cbn [rw_run_step rw_run_current rw_run_stop rw_run_graph rw_run_ops rw_run_vars].
  destruct (strategy current) as [a|].
  2: { unfold rw_run_state_valid; cbn; do 5 (split; [assumption|]); assumption. }
  rewrite (rw_apply_prepared_agrees EK ES EV EH sig _ current ops vars a Hwf Hops Hvars).
  rewrite rw_apply_indexed_agrees.
  destruct (rw_apply EK ES EV EH sig rules current a) as [accepted|] eqn:Happly.
  2: { unfold rw_run_state_valid; cbn; do 5 (split; [assumption|]); assumption. }
  destruct (rw_apply_correct EK ES EV EH sig admissible rules current accepted a
    Hrules Hsoundrules Hwf Hsound Hproductive Happly)
    as [Hawf [Hasound [Haproductive [Hclean Haext]]]].
  apply rw_prepare_run_valid; [exact Hawf|exact Hasound|exact Haproductive|].
  eapply rw_extends_trans; eauto.
Qed.

(** Every bounded run directly preserves graph invariants and all initially represented terms. *)
Theorem rw_run_correct {K Sort V H C} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (EH : encoding H) (sig : rw_signature K Sort V)
    (admissible : rw_semantics K Sort V C -> Prop) (rules : list (rw_rule K Sort V H))
    (strategy : rw_strategy K Sort V H) (fuel : N) (g : rw_graph K Sort V) :
  Forall (rw_rule_wf sig) rules -> Forall (rw_rule_sound sig admissible) rules ->
  rw_graph_wf sig g -> rw_graph_sound sig admissible rules g -> rw_productive g ->
  let g' := rw_run_graph (rw_run EK ES EV EH sig rules strategy fuel g) in
  rw_graph_wf sig g' /\ rw_graph_sound sig admissible rules g' /\ rw_productive g' /\
  rw_extends g g'.
Proof.
  intros Hrules Hsoundrules Hwf Hsound Hproductive; unfold rw_run.
  destruct fuel as [|fuel].
  { cbn; do 3 (split; [assumption|]); apply rw_extends_refl. }
  assert (Hvalid : rw_run_state_valid EK EV sig admissible rules g
      (rw_repeat rw_run_done
        (rw_run_step EK ES EV EH sig (rw_rule_table_from rules 0) strategy) fuel
        (rw_prepare_run EK EV g RWFuelExhausted))).
  { apply rw_repeat_preserved.
    - apply rw_run_step_preserved; assumption.
    - apply rw_prepare_run_valid; [exact Hwf|exact Hsound|exact Hproductive|].
      apply rw_extends_refl. }
  destruct Hvalid as [Hfinalwf [Hfinalsound [Hfinalproductive [Hext Hindexes]]]]; auto.
Qed.
