(** * Semi-naive evaluation of stratified rules

    Each stratum maintains accumulated tuples, a frontier, and incrementally updated join indexes.
    For example, a transitive rule joins a new path with all previously accumulated paths.
    Builds on: RulesJoin, RulesModel, RulesSolve and CollectionsFinSet. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia Arith.Wf_nat
  Relations.Relation_Operators Relations.Operators_Properties Init.Wf.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTable.
From Gaulois.Order Require Import OrderPowerset.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesModel RulesSolve
  RulesJoin.
Import List.ListNotations.

(** * Observational equality of enumerations *)

Definition delta_list_equiv {A} (xs ys : list A) : Prop := forall x, In x xs <-> In x ys.

Lemma delta_flat_map_equiv {A B} (f g : A -> list B) xs ys :
  delta_list_equiv xs ys ->
  (forall x, In x xs -> delta_list_equiv (f x) (g x)) ->
  delta_list_equiv (flat_map f xs) (flat_map g ys).
Proof.
  intros Hxs Hfg y; repeat rewrite in_flat_map; split.
  - intros [x [Hx Hy]]; exists x; split; [apply Hxs; exact Hx | apply Hfg; assumption].
  - intros [x [Hx Hy]]; apply Hxs in Hx; exists x; split; [exact Hx | apply Hfg; assumption].
Qed.

Lemma delta_filter_equiv {A} (f : A -> bool) xs ys :
  delta_list_equiv xs ys -> delta_list_equiv (filter f xs) (filter f ys).
Proof.
  intros Hxs x; repeat rewrite filter_In; rewrite (Hxs x); reflexivity.
Qed.

(** * Retained search indexes *)

Definition delta_nested_cache Q := list (atom Q * nested_search).

Fixpoint delta_prepare_nested {Q} (ps : list (atom Q)) bound env : delta_nested_cache Q :=
  match ps with
  | [] => []
  | a :: rest =>
    (a, NestedSearch bound (args a)
      (build_index bound (args a) (FinSet.elements (env (pred a))))) ::
      delta_prepare_nested rest (bound_add bound a) env
  end.

Definition delta_rebuild_nested {Q} env (cache : delta_nested_cache Q) : list nested_search :=
  map (fun node => let '(a, search) := node in
    NestedSearch (nested_bound search) (nested_terms search)
      (build_index (nested_bound search) (nested_terms search)
        (FinSet.elements (env (pred a))))) cache.

Definition delta_nested_exact {Q} env (cache : delta_nested_cache Q) : Prop :=
  forall a search, In (a, search) cache -> forall key row,
    In row (index_get (nested_index search) key) <->
    FinSet.mem tuple_encoding row (env (pred a)) = true /\
      tuple_key (nested_bound search) (nested_terms search) row = Some key.

Lemma delta_prepare_nested_shape {Q} (ps : list (atom Q)) bound env env' :
  delta_rebuild_nested env' (delta_prepare_nested ps bound env) =
    prepare_nested ps bound (fun p => FinSet.elements (env' p)).
Proof.
  revert bound; induction ps as [|a ps IH]; intro bound; cbn; [reflexivity |].
  f_equal; apply IH.
Qed.

Lemma delta_prepare_nested_exact {Q} (ps : list (atom Q)) bound env :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_nested_exact env (delta_prepare_nested ps bound env).
Proof.
  intros Hwf; revert bound; induction ps as [|a ps IH]; intros bound x search Hin key row.
  - contradiction.
  - cbn in Hin; destruct Hin as [Heq | Hin].
    + injection Heq as Heqa Heqs; subst x search; cbn.
      rewrite build_index_spec, FinSet.elements_spec by apply Hwf; reflexivity.
    + apply (IH (bound_add bound a) x search Hin key row).
Qed.

Definition delta_update_nested {Q} (reset : Q -> bool) (rows : Q -> list tuple)
    (cache : delta_nested_cache Q) : delta_nested_cache Q :=
  map (fun node => let '(a, search) := node in
    (a, NestedSearch (nested_bound search) (nested_terms search)
      (fold_right (index_add (nested_bound search) (nested_terms search))
        (if reset (pred a) then Map.empty else nested_index search) (rows (pred a))))) cache.

Definition delta_updated_env {Q} (reset : Q -> bool) (rows : Q -> list tuple) env q :=
  let batch := FinSet.of_list tuple_encoding (rows q) in
  if reset q then batch else FinSet.union tuple_encoding (env q) batch.

Lemma delta_index_extend bound ts rows idx key row :
  In row (index_get (fold_right (index_add bound ts) idx rows) key) <->
    In row (index_get idx key) \/ (In row rows /\ tuple_key bound ts row = Some key).
Proof.
  induction rows as [|cs rows IH]; cbn [fold_right In].
  - tauto.
  - rewrite index_add_spec, IH; cbn [In]; intuition congruence.
Qed.

Lemma delta_update_nested_shape {Q} reset rows (cache : delta_nested_cache Q) env :
  delta_rebuild_nested env (delta_update_nested reset rows cache) =
    delta_rebuild_nested env cache.
Proof.
  induction cache as [|[a search] cache IH]; cbn; [reflexivity | f_equal; exact IH].
Qed.

Lemma delta_update_nested_exact {Q} reset rows env (cache : delta_nested_cache Q) :
  delta_nested_exact env cache ->
  delta_nested_exact (delta_updated_env reset rows env) (delta_update_nested reset rows cache).
Proof.
  intros Hexact a search Hin key row; apply in_map_iff in Hin.
  destruct Hin as [[x old] [Heq Hin]]; cbn in Heq; injection Heq as Heqa Heqs.
  subst a search; cbn; rewrite delta_index_extend; unfold delta_updated_env.
  destruct (reset (pred x)) eqn:Hreset.
  - unfold index_get; rewrite Map.get_empty; cbn; rewrite FinSet.of_list_spec; tauto.
  - rewrite (Hexact x old Hin), FinSet.mem_union, FinSet.of_list_spec; tauto.
Qed.

Lemma delta_nested_probe_equiv {Q} env (a : atom Q) search bs :
  (forall key row, In row (index_get (nested_index search) key) <->
    FinSet.mem tuple_encoding row (env (pred a)) = true /\
      tuple_key (nested_bound search) (nested_terms search) row = Some key) ->
  FinSet.wf tuple_encoding (env (pred a)) ->
  delta_list_equiv (nested_probe search bs)
    (nested_probe (NestedSearch (nested_bound search) (nested_terms search)
      (build_index (nested_bound search) (nested_terms search)
        (FinSet.elements (env (pred a))))) bs).
Proof.
  intros Hexact Hwf; unfold nested_probe; apply delta_flat_map_equiv.
  - intro b; reflexivity.
  - intros b _; apply delta_flat_map_equiv.
    + intro row; cbn; rewrite Hexact, build_index_spec, FinSet.elements_spec by exact Hwf.
      reflexivity.
    + intros row _ x; reflexivity.
Qed.

Lemma delta_run_nested_inputs searches bs bs' :
  delta_list_equiv bs bs' ->
  delta_list_equiv (run_nested searches bs) (run_nested searches bs').
Proof.
  revert bs bs'; induction searches as [|search searches IH]; intros bs bs' Heq; cbn.
  - exact Heq.
  - apply IH; unfold nested_probe; apply delta_flat_map_equiv; [exact Heq |].
    intros b _ x; reflexivity.
Qed.

Lemma delta_run_nested_exact {Q} env (cache : delta_nested_cache Q) bs :
  (forall p, FinSet.wf tuple_encoding (env p)) -> delta_nested_exact env cache ->
  delta_list_equiv (run_nested (map snd cache) bs)
    (run_nested (delta_rebuild_nested env cache) bs).
Proof.
  intros Hwf; revert bs; induction cache as [|[a search] cache IH]; intros bs Hexact; cbn.
  - intro b; reflexivity.
  - intro b; rewrite (IH (nested_probe search bs) ltac:(
      intros x s Hin; apply Hexact; now right) b).
    apply delta_run_nested_inputs; apply delta_nested_probe_equiv; [|apply Hwf].
    apply Hexact; now left.
Qed.

Record delta_variable_cache (Q : Type) : Type := DeltaVariableCache {
  delta_variable : nat;
  delta_bound : FinSet.t nat;
  delta_domains : list (atom Q * variable_search)
}.

Arguments DeltaVariableCache {Q}.
Arguments delta_variable {Q}.
Arguments delta_bound {Q}.
Arguments delta_domains {Q}.

Fixpoint delta_prepare_multiway {Q} (vs : list nat) bound (ps : list (atom Q)) env
    : list (delta_variable_cache Q) :=
  match vs with
  | [] => []
  | v :: rest =>
    DeltaVariableCache v bound
      (map (fun a => (a, VariableSearch (args a)
        (build_variable_index bound (args a) v (FinSet.elements (env (pred a))))))
        (atoms_with_variable v ps)) ::
      delta_prepare_multiway rest (FinSet.add nat_encoding v bound) ps env
  end.

Definition delta_erase_variable {Q} (layer : delta_variable_cache Q) : multiway_search :=
  MultiwaySearch (delta_variable layer) (delta_bound layer) (map snd (delta_domains layer)).

Definition delta_rebuild_variable {Q} env (layer : delta_variable_cache Q) : multiway_search :=
  MultiwaySearch (delta_variable layer) (delta_bound layer)
    (map (fun node => let '(a, search) := node in
      VariableSearch (variable_terms search)
        (build_variable_index (delta_bound layer) (variable_terms search) (delta_variable layer)
          (FinSet.elements (env (pred a))))) (delta_domains layer)).

Definition delta_multiway_exact {Q} env (cache : list (delta_variable_cache Q)) : Prop :=
  forall layer, In layer cache -> forall a search, In (a, search) (delta_domains layer) ->
    (forall key, FinSet.wf positive_encoding (variable_index_get (variable_table search) key)) /\
    forall key c, FinSet.mem positive_encoding c
      (variable_index_get (variable_table search) key) = true <->
      exists cs b, FinSet.mem tuple_encoding cs (env (pred a)) = true /\
        tuple_key (delta_bound layer) (variable_terms search) cs = Some key /\
        bind_terms (variable_terms search) cs Map.empty = Some b /\ c = binding_value b
          (delta_variable layer).

Lemma delta_prepare_multiway_shape {Q} vs bound (ps : list (atom Q)) env env' :
  map (delta_rebuild_variable env') (delta_prepare_multiway vs bound ps env) =
    prepare_multiway vs bound ps (fun p => FinSet.elements (env' p)).
Proof.
  revert bound; induction vs as [|v vs IH]; intro bound;
    cbn [delta_prepare_multiway map prepare_multiway]; [reflexivity |].
  rewrite IH; f_equal; unfold delta_rebuild_variable, prepare_variable; cbn.
  rewrite map_map; reflexivity.
Qed.

Lemma delta_prepare_multiway_exact {Q} vs bound (ps : list (atom Q)) env :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_multiway_exact env (delta_prepare_multiway vs bound ps env).
Proof.
  intros Hwf; revert bound; induction vs as [|v vs IH]; intros bound layer Hin a search Hnode.
  - contradiction.
  - cbn in Hin; destruct Hin as [Heq | Hin].
    + subst layer; cbn in Hnode; apply in_map_iff in Hnode.
      destruct Hnode as [x [Heq _]]; injection Heq as Heqa Heqs; subst a search; cbn; split.
      * intro key; apply build_variable_index_wf.
      * intros key c; rewrite build_variable_index_spec; setoid_rewrite FinSet.elements_spec;
          [reflexivity | apply Hwf].
    + apply (IH _ layer Hin a search Hnode).
Qed.

Definition delta_update_variable {Q} (reset : Q -> bool) (rows : Q -> list tuple)
    (layer : delta_variable_cache Q) : delta_variable_cache Q :=
  DeltaVariableCache (delta_variable layer) (delta_bound layer)
    (map (fun node => let '(a, search) := node in
      (a, VariableSearch (variable_terms search)
        (fold_right (variable_index_add (delta_bound layer) (variable_terms search)
          (delta_variable layer))
          (if reset (pred a) then Table.empty else variable_table search)
          (rows (pred a))))) (delta_domains layer)).

Lemma delta_variable_extend bound ts v rows idx key c :
  FinSet.mem positive_encoding c
    (variable_index_get (fold_right (variable_index_add bound ts v) idx rows) key) = true <->
    FinSet.mem positive_encoding c (variable_index_get idx key) = true \/
    exists cs b, In cs rows /\ tuple_key bound ts cs = Some key /\
      bind_terms ts cs Map.empty = Some b /\ c = binding_value b v.
Proof.
  induction rows as [|cs rows IH]; cbn [fold_right].
  - split; [auto | intros [Hin | [cs [b [Hbad _]]]]; [exact Hin | contradiction]].
  - rewrite variable_index_add_spec, IH; split.
    + intros [[Hin | [row [b [Hin Hrest]]]] | [b Hrest]].
      * now left.
      * right; exists row, b; split; [now right | exact Hrest].
      * right; exists cs, b; split; [now left | exact Hrest].
    + intros [Hin | [row [b [[Heq | Hin] Hrest]]]].
      * now left; left.
      * subst row; right; exists b; exact Hrest.
      * left; right; exists row, b; auto.
Qed.

Lemma delta_variable_extend_wf bound ts v rows idx :
  (forall key, FinSet.wf positive_encoding (variable_index_get idx key)) ->
  forall key, FinSet.wf positive_encoding
    (variable_index_get (fold_right (variable_index_add bound ts v) idx rows) key).
Proof.
  intro Hwf; induction rows as [|cs rows IH]; intro key; cbn [fold_right].
  - apply Hwf.
  - apply variable_index_add_wf; exact IH.
Qed.

Lemma delta_update_multiway_shape {Q} reset rows (cache : list (delta_variable_cache Q)) env :
  map (delta_rebuild_variable env) (map (delta_update_variable reset rows) cache) =
    map (delta_rebuild_variable env) cache.
Proof.
  induction cache as [|layer cache IH]; cbn; [reflexivity |].
  rewrite IH; f_equal; unfold delta_rebuild_variable, delta_update_variable; cbn.
  rewrite map_map; f_equal; apply map_ext; intros [a search]; reflexivity.
Qed.

Lemma delta_update_multiway_exact {Q} reset rows env (cache : list (delta_variable_cache Q)) :
  delta_multiway_exact env cache ->
  delta_multiway_exact (delta_updated_env reset rows env)
    (map (delta_update_variable reset rows) cache).
Proof.
  intros Hexact layer Hin a search Hnode; apply in_map_iff in Hin.
  destruct Hin as [old [Heq Hin]]; subst layer; cbn in Hnode; apply in_map_iff in Hnode.
  destruct Hnode as [[x domain] [Heq Hdomain]]; cbn in Heq.
  injection Heq as Heqa Heqs; subst a search; cbn.
  destruct (Hexact old Hin x domain Hdomain) as [Hwf Hmember]; split.
  - apply delta_variable_extend_wf; intro key; destruct (reset (pred x)); [|apply Hwf].
    unfold variable_index_get; rewrite Table.get_empty; apply Map.wf_empty.
  - intros key c; rewrite delta_variable_extend; unfold delta_updated_env.
    destruct (reset (pred x)) eqn:Hreset.
    + unfold variable_index_get; rewrite Table.get_empty, FinSet.mem_empty.
      setoid_rewrite FinSet.of_list_spec; split.
      * intros [Hbad | Hex]; [discriminate | exact Hex].
      * intro Hex; now right.
    + rewrite Hmember; setoid_rewrite FinSet.mem_union; setoid_rewrite FinSet.of_list_spec.
      split.
      * intros [[cs [b [Hmem Hrest]]] | [cs [b [Hmem Hrest]]]];
          exists cs, b; split; [now left | exact Hrest | now right | exact Hrest].
      * intros [cs [b [[Hmem | Hmem] Hrest]]]; [left | right]; exists cs, b; auto.
Qed.

Lemma delta_candidates_wf bound b searches :
  (forall search, In search searches ->
    FinSet.wf positive_encoding (variable_probe bound b search)) ->
  FinSet.wf positive_encoding (variable_candidates bound b searches).
Proof.
  intro Hwf; destruct searches as [|search rest]; cbn [variable_candidates].
  - apply Map.wf_empty.
  - apply intersect_variable_domains_wf.
    + apply Hwf; now left.
    + intros x Hx; apply Hwf; now right.
Qed.

Lemma delta_layer_candidates {Q} env (layer : delta_variable_cache Q) b :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_multiway_exact env [layer] ->
  delta_list_equiv
    (FinSet.elements (variable_candidates (delta_bound layer) b
      (multiway_domains (delta_erase_variable layer))))
    (FinSet.elements (variable_candidates (delta_bound layer) b
      (multiway_domains (delta_rebuild_variable env layer)))).
Proof.
  intros Hwf Hexact.
  assert (Hdomain : forall a search, In (a, search) (delta_domains layer) -> forall c,
    FinSet.mem positive_encoding c (variable_probe (delta_bound layer) b search) = true <->
    FinSet.mem positive_encoding c (variable_probe (delta_bound layer) b
      (VariableSearch (variable_terms search)
        (build_variable_index (delta_bound layer) (variable_terms search)
          (delta_variable layer) (FinSet.elements (env (pred a)))))) = true).
  { intros a search Hin c; unfold variable_probe; cbn.
    rewrite (proj2 (Hexact layer (or_introl eq_refl) a search Hin)).
    rewrite build_variable_index_spec; setoid_rewrite FinSet.elements_spec;
      [reflexivity | apply Hwf]. }
  intro c; repeat rewrite FinSet.elements_spec.
  - repeat rewrite variable_candidates_spec; unfold delta_erase_variable,
      delta_rebuild_variable; cbn.
    split; intros [Hnon Hall]; split.
    + intro Hbad; apply Hnon; apply map_eq_nil in Hbad; rewrite Hbad; reflexivity.
    + intros search Hin; apply in_map_iff in Hin; destruct Hin as [[a old] [Heq Hin]].
      subst search; apply (Hdomain a old); [exact Hin |].
      apply Hall, in_map_iff; exists (a, old); split; [reflexivity | exact Hin].
    + intro Hbad; apply Hnon; apply map_eq_nil in Hbad; rewrite Hbad; reflexivity.
    + intros search Hin; apply in_map_iff in Hin; destruct Hin as [[a old] [Heq Hin]].
      subst search; apply (Hdomain a old); [exact Hin |].
      apply Hall, in_map_iff; exists (a, old); split; [reflexivity | exact Hin].
  - apply delta_candidates_wf; intros search Hin; unfold delta_rebuild_variable in Hin;
      cbn in Hin; apply in_map_iff in Hin; destruct Hin as [[a old] [Heq _]].
    subst search; apply build_variable_index_wf.
  - apply delta_candidates_wf; intros search Hin; unfold delta_erase_variable in Hin;
      cbn in Hin; apply in_map_iff in Hin; destruct Hin as [[a old] [Heq Hin]].
    subst search; apply (proj1 (Hexact layer (or_introl eq_refl) a old Hin)).
Qed.

Lemma delta_layer_step_equiv {Q} env (layer : delta_variable_cache Q) bs :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_multiway_exact env [layer] ->
  delta_list_equiv (multiway_step (delta_erase_variable layer) bs)
    (multiway_step (delta_rebuild_variable env layer) bs).
Proof.
  intros Hwf Hexact; unfold multiway_step; apply delta_flat_map_equiv.
  - intro b; reflexivity.
  - intros b _; apply delta_flat_map_equiv.
    + apply delta_layer_candidates; assumption.
    + intros c _ x; reflexivity.
Qed.

Lemma delta_run_multiway_inputs searches bs bs' :
  delta_list_equiv bs bs' ->
  delta_list_equiv (run_multiway searches bs) (run_multiway searches bs').
Proof.
  revert bs bs'; induction searches as [|search searches IH]; intros bs bs' Heq; cbn.
  - exact Heq.
  - apply IH; unfold multiway_step; apply delta_flat_map_equiv; [exact Heq |].
    intros b _ x; reflexivity.
Qed.

Lemma delta_run_multiway_exact {Q} env (cache : list (delta_variable_cache Q)) bs :
  (forall p, FinSet.wf tuple_encoding (env p)) -> delta_multiway_exact env cache ->
  delta_list_equiv (run_multiway (map delta_erase_variable cache) bs)
    (run_multiway (map (delta_rebuild_variable env) cache) bs).
Proof.
  intros Hwf; revert bs; induction cache as [|layer cache IH]; intros bs Hexact; cbn.
  - intro b; reflexivity.
  - intro b; rewrite (IH (multiway_step (delta_erase_variable layer) bs) ltac:(
      intros x Hin; apply Hexact; now right) b).
    apply delta_run_multiway_inputs, delta_layer_step_equiv; [exact Hwf |].
    intros x [Heq | Hbad]; [subst x; apply Hexact; now left | contradiction].
Qed.

Lemma delta_prepare_variable_rows {Q} bound v (ps : list (atom Q)) rows rows' :
  (forall a, In a ps -> rows (pred a) = rows' (pred a)) ->
  prepare_variable bound v ps rows = prepare_variable bound v ps rows'.
Proof.
  intro Hrows; unfold prepare_variable; apply map_ext_in; intros a Ha.
  apply atoms_with_variable_spec in Ha; rewrite (Hrows a (proj1 Ha)); reflexivity.
Qed.

Lemma delta_prepare_multiway_rows {Q} vs bound (ps : list (atom Q)) rows rows' :
  (forall a, In a ps -> rows (pred a) = rows' (pred a)) ->
  prepare_multiway vs bound ps rows = prepare_multiway vs bound ps rows'.
Proof.
  intro Hrows; revert bound; induction vs as [|v vs IH]; intro bound; cbn; [reflexivity |].
  rewrite (delta_prepare_variable_rows bound v ps rows rows' Hrows), IH; reflexivity.
Qed.

Inductive delta_join_plan (Q : Type) : Type :=
  | DeltaNested (cache : delta_nested_cache Q)
  | DeltaMultiway (cache : list (delta_variable_cache Q)).

Arguments DeltaNested {Q}.
Arguments DeltaMultiway {Q}.

Definition delta_prepare_plan {Q} strategy (ps : list (atom Q)) env : delta_join_plan Q :=
  match strategy with
  | IndexedNested => DeltaNested (delta_prepare_nested ps FinSet.empty env)
  | IndexedMultiway =>
    DeltaMultiway (delta_prepare_multiway (join_variables ps) FinSet.empty ps env)
  end.

Definition delta_plan_exact {Q} strategy (ps : list (atom Q)) env
    (plan : delta_join_plan Q) : Prop :=
  match strategy, plan with
  | IndexedNested, DeltaNested cache => delta_nested_exact env cache /\
      forall env', delta_rebuild_nested env' cache =
        prepare_nested ps FinSet.empty (fun p => FinSet.elements (env' p))
  | IndexedMultiway, DeltaMultiway cache => delta_multiway_exact env cache /\
      forall env', map (delta_rebuild_variable env') cache =
        prepare_multiway (join_variables ps) FinSet.empty ps
          (fun p => FinSet.elements (env' p))
  | _, _ => False
  end.

Definition delta_update_plan {Q} reset rows (plan : delta_join_plan Q) : delta_join_plan Q :=
  match plan with
  | DeltaNested cache => DeltaNested (delta_update_nested reset rows cache)
  | DeltaMultiway cache => DeltaMultiway (map (delta_update_variable reset rows) cache)
  end.

Definition delta_plan_bindings {Q} (ps : list (atom Q)) env (plan : delta_join_plan Q) :=
  match plan with
  | DeltaNested cache => run_nested (map snd cache) [Map.empty]
  | DeltaMultiway cache => filter (positive_ok ps env)
      (run_multiway (map delta_erase_variable cache) [Map.empty])
  end.

Lemma delta_prepare_plan_exact {Q} strategy (ps : list (atom Q)) env :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_plan_exact strategy ps env (delta_prepare_plan strategy ps env).
Proof.
  intro Hwf; destruct strategy; cbn; split.
  - apply delta_prepare_nested_exact; exact Hwf.
  - apply delta_prepare_nested_shape.
  - apply delta_prepare_multiway_exact; exact Hwf.
  - apply delta_prepare_multiway_shape.
Qed.

Lemma delta_update_plan_exact {Q} strategy (ps : list (atom Q)) env plan reset rows :
  delta_plan_exact strategy ps env plan ->
  delta_plan_exact strategy ps (delta_updated_env reset rows env)
    (delta_update_plan reset rows plan).
Proof.
  destruct strategy, plan; cbn; try contradiction; intros [Hexact Hshape]; split.
  - apply delta_update_nested_exact; exact Hexact.
  - intro env'; rewrite delta_update_nested_shape; apply Hshape.
  - apply delta_update_multiway_exact; exact Hexact.
  - intro env'; rewrite delta_update_multiway_shape; apply Hshape.
Qed.

Lemma delta_plan_bindings_exact {Q} strategy (prog : program Q) r env plan :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  delta_plan_exact strategy (positive_atoms (body r)) env plan ->
  delta_list_equiv (delta_plan_bindings (positive_atoms (body r)) env plan)
    (selected_bindings strategy prog r env).
Proof.
  intros Hwf; destruct strategy, plan; cbn [delta_plan_exact]; try contradiction;
    intros [Hexact Hshape]; unfold delta_plan_bindings, selected_bindings.
  - intro b; rewrite (delta_run_nested_exact env cache [Map.empty] Hwf Hexact b), Hshape.
    rewrite !run_nested_agrees with (env := env).
    + reflexivity.
    + intros a Ha; apply prepare_join_relations_get; exact Ha.
    + intros a _; reflexivity.
  - apply delta_filter_equiv; intro b.
    rewrite (delta_run_multiway_exact env cache [Map.empty] Hwf Hexact b), Hshape.
    rewrite (delta_prepare_multiway_rows (join_variables (positive_atoms (body r)))
      FinSet.empty (positive_atoms (body r))
      (join_relation_rows (penc prog)
        (prepare_join_relations (penc prog) (positive_atoms (body r)) env))
      (fun p => FinSet.elements (env p))).
    + reflexivity.
    + intros a Ha; apply prepare_join_relations_get; exact Ha.
Qed.

(** * Delta rule variants *)

Definition delta_term_eqb (x y : term) : bool :=
  match x, y with
  | TVar v, TVar w => Nat.eqb v w
  | TConst c, TConst d => Pos.eqb c d
  | _, _ => false
  end.

Fixpoint delta_terms_eqb (xs ys : list term) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => delta_term_eqb x y && delta_terms_eqb xs ys
  | _, _ => false
  end.

Lemma delta_terms_eqb_spec xs ys : delta_terms_eqb xs ys = true <-> xs = ys.
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn; try (split; congruence).
  rewrite andb_true_iff, IH.
  assert (Hterm : delta_term_eqb x y = true <-> x = y).
  { destruct x, y; cbn; try rewrite Nat.eqb_eq; try rewrite Pos.eqb_eq; split; congruence. }
  rewrite Hterm; split; [intros [Hx Hxs]; now subst | intro Heq; injection Heq; auto].
Qed.

Definition delta_atom_eqb {P} (E : encoding P) (x y : atom P) : bool :=
  Pos.eqb (encode E (pred x)) (encode E (pred y)) && delta_terms_eqb (args x) (args y).

Lemma delta_atom_eqb_spec {P} (E : encoding P) x y : delta_atom_eqb E x y = true <-> x = y.
Proof.
  destruct x as [p ts], y as [q us]; unfold delta_atom_eqb; cbn.
  rewrite andb_true_iff, Pos.eqb_eq, delta_terms_eqb_spec; split.
  - intros [Hp Hts]; apply (encode_injective E) in Hp; subst q us; reflexivity.
  - intro Heq; injection Heq as Hp Hts; subst q us; auto.
Qed.

Definition delta_tag_atom {P} (E : encoding P) (pivot a : atom P) : atom (P * bool) :=
  Atom (pred a, delta_atom_eqb E a pivot) (args a).

Definition delta_tag_rule {P} (E : encoding P) (r : rule P) pivot : rule (P * bool) :=
  Rule (Atom (pred (head r), false) (args (head r)))
    (map (fun a => LPos (delta_tag_atom E pivot a)) (positive_atoms (body r))).

Definition delta_tag_program {P} (prog : program P) : program (P * bool) :=
  Program (pair_encoding (penc prog) bool_encoding) (fun q => arity prog (fst q)) [].

Lemma delta_tag_positive {P} (E : encoding P) r pivot :
  positive_atoms (body (delta_tag_rule E r pivot)) =
    map (delta_tag_atom E pivot) (positive_atoms (body r)).
Proof.
  unfold delta_tag_rule; cbn [body]; generalize (positive_atoms (body r)) as ps.
  intros ps; induction ps as [|a ps IH]; cbn [positive_atoms flat_map map app];
    [reflexivity | f_equal; exact IH].
Qed.

Definition delta_recursive_atoms {P} (st : stratification P) k (r : rule P) :=
  filter (fun a => Nat.eqb (level st (pred a)) k) (positive_atoms (body r)).

Lemma delta_recursive_atoms_spec {P} (st : stratification P) k r a :
  In a (delta_recursive_atoms st k r) <-> In (LPos a) (body r) /\ level st (pred a) = k.
Proof.
  unfold delta_recursive_atoms; rewrite filter_In, positive_atoms_spec, Nat.eqb_eq; reflexivity.
Qed.

Definition delta_specs {P} (prog : program P) (st : stratification P) k : list (rule P * atom P) :=
  flat_map (fun r => map (fun a => (r, a)) (delta_recursive_atoms st k r))
    (filter (fun r => Nat.eqb (level st (pred (head r))) k) (rules prog)).

Lemma delta_specs_spec {P} (prog : program P) st k r a :
  In (r, a) (delta_specs prog st k) <->
    In r (rules prog) /\ level st (pred (head r)) = k /\
      In (LPos a) (body r) /\ level st (pred a) = k.
Proof.
  unfold delta_specs; rewrite in_flat_map; split.
  - intros [x [Hx Hin]]; apply filter_In in Hx; apply in_map_iff in Hin.
    destruct Hin as [b [Heq Hb]]; injection Heq as Hr Ha; subst x b.
    apply delta_recursive_atoms_spec in Hb; destruct Hx as [Hr Hlevel].
    apply Nat.eqb_eq in Hlevel; tauto.
  - intros [Hr [Hlevel Ha]]; exists r; split.
    + apply filter_In; split; [exact Hr | apply Nat.eqb_eq; exact Hlevel].
    + apply in_map_iff; exists a; split; [reflexivity | apply delta_recursive_atoms_spec; exact Ha].
Qed.

Definition delta_body_holds {P} (r : rule P) env lower sigma : Prop :=
  (forall a, In (LPos a) (body r) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
  (forall a, In (LNeg a) (body r) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (lower (pred a)) = false).

Definition delta_cached_universe {P} (prog : program P) facts : P -> tuple -> bool :=
  let predicates := preds prog facts in
  let alphabet := constants prog facts in
  fun p ts => FinSet.mem (penc prog) p predicates && Nat.eqb (length ts) (arity prog p) &&
    forallb (fun c => FinSet.mem positive_encoding c alphabet) ts.

Definition delta_variant_rows {P} (prog : program P) facts lower (r : rule P) pivot env
    (plan : delta_join_plan (P * bool)) : list tuple :=
  filter (in_universe prog facts (pred (head r)))
    (map (fun b => map (inst (binding_value b)) (args (head r)))
      (filter (negative_ok r lower)
        (delta_plan_bindings (positive_atoms (body (delta_tag_rule (penc prog) r pivot)))
          env plan))).

Lemma delta_variant_rows_exact {P} strategy (prog : program P) facts lower r pivot env plan ts :
  safe_rule r -> (forall q, FinSet.wf tuple_encoding (env q)) ->
  delta_plan_exact strategy (positive_atoms (body (delta_tag_rule (penc prog) r pivot)))
    env plan ->
  (In ts (delta_variant_rows prog facts lower r pivot env plan) <->
    in_universe prog facts (pred (head r)) ts = true /\
    exists sigma, ts = map (inst sigma) (args (head r)) /\
      (forall a, In (LPos a) (body r) -> FinSet.mem tuple_encoding
        (map (inst sigma) (args a)) (env (pred (delta_tag_atom (penc prog) pivot a))) = true) /\
      (forall a, In (LNeg a) (body r) -> FinSet.mem tuple_encoding
        (map (inst sigma) (args a)) (lower (pred a)) = false)).
Proof.
  intros Hsafe Hwf Hplan; unfold delta_variant_rows.
  rewrite filter_In, in_map_iff; split.
  - intros [[b [Hts Hin]] Huniv]; apply filter_In in Hin; destruct Hin as [Hb Hneg].
    apply (delta_plan_bindings_exact strategy (delta_tag_program prog) _ env plan Hwf Hplan)
      in Hb.
    split; [exact Huniv | exists (binding_value b); split; [symmetry; exact Hts | split]].
    + intros a Ha; apply (selected_bindings_sound strategy (delta_tag_program prog)
        (delta_tag_rule (penc prog) r pivot) env b Hwf Hb
        (delta_tag_atom (penc prog) pivot a)).
      apply positive_atoms_spec; rewrite delta_tag_positive; apply in_map,
        positive_atoms_spec; exact Ha.
    + apply negative_ok_spec; exact Hneg.
  - intros [Huniv [sigma [Hts [Hpos Hneg]]]].
    destruct (selected_bindings_complete strategy (delta_tag_program prog)
      (delta_tag_rule (penc prog) r pivot) env sigma Hwf) as [b [Hb [Hagree Hbound]]].
    + intros a Ha; apply positive_atoms_spec in Ha; rewrite delta_tag_positive in Ha.
      apply in_map_iff in Ha; destruct Ha as [x [Heq Hx]]; subst a; cbn.
      apply Hpos, positive_atoms_spec; exact Hx.
    + assert (Horiginal : forall a, In (LPos a) (body r) -> forall v,
        In (TVar v) (args a) -> exists c, Map.get nat_encoding v b = Some c).
      { intros a Ha; apply (Hbound (delta_tag_atom (penc prog) pivot a)).
        apply positive_atoms_spec; rewrite delta_tag_positive; apply in_map,
          positive_atoms_spec; exact Ha. }
      destruct (safe_binding_agrees r b sigma Hsafe Hagree Horiginal) as [Hhead Hnegative].
      split; [|exact Huniv]; exists b; split.
      * rewrite Hhead; symmetry; exact Hts.
      * apply filter_In; split.
        -- apply (delta_plan_bindings_exact strategy (delta_tag_program prog) _ env plan
            Hwf Hplan); exact Hb.
        -- apply negative_ok_spec; intros a Ha; rewrite Hnegative by exact Ha.
           apply Hneg; exact Ha.
Qed.

(** * Indexed tuple batches *)

Definition delta_ground_encoding {P} (prog : program P) : encoding (ground_atom P) :=
  pair_encoding (penc prog) tuple_encoding.

Definition delta_add_atoms {P} (prog : program P) (xs : list (ground_atom P))
    (db : database P) : database P :=
  fold_right (fun f acc => Map.set (penc prog) (fst f)
    (FinSet.add tuple_encoding (snd f) (rel_of prog acc (fst f))) acc) db xs.

Lemma delta_add_atoms_exact {P} (prog : program P) xs db p ts :
  FinSet.mem tuple_encoding ts (rel_of prog (delta_add_atoms prog xs db) p) = true <->
    FinSet.mem tuple_encoding ts (rel_of prog db p) = true \/ In (p, ts) xs.
Proof.
  induction xs as [|[q us] xs IH]; cbn [delta_add_atoms fold_right fst snd].
  - cbn [In]; tauto.
  - unfold rel_of at 1; destruct (encoded_eq_dec (penc prog) p q) as [Heq | Hne].
    + subst q; rewrite Map.get_set_same, FinSet.mem_add, IH; cbn [In]; intuition congruence.
    + rewrite Map.get_set_other by exact Hne; fold (rel_of prog (delta_add_atoms prog xs db) p).
      rewrite IH; cbn [In]; intuition congruence.
Qed.

Lemma delta_add_atoms_wf {P} (prog : program P) xs db :
  (forall p, FinSet.wf tuple_encoding (rel_of prog db p)) ->
  forall p, FinSet.wf tuple_encoding (rel_of prog (delta_add_atoms prog xs db) p).
Proof.
  intros Hwf; induction xs as [|[q us] xs IH]; intro p; cbn [delta_add_atoms fold_right fst snd].
  - apply Hwf.
  - unfold rel_of at 1; destruct (encoded_eq_dec (penc prog) p q) as [Heq | Hne].
    + subst q; rewrite Map.get_set_same; apply Map.wf_set, IH.
    + rewrite Map.get_set_other by exact Hne; apply IH.
Qed.

Definition delta_index {P} (prog : program P) (s : FinSet.t (ground_atom P)) : database P :=
  delta_add_atoms prog (FinSet.elements s) Map.empty.

Lemma delta_index_exact {P} (prog : program P) s p ts :
  FinSet.wf (delta_ground_encoding prog) s ->
  (FinSet.mem tuple_encoding ts (rel_of prog (delta_index prog s) p) = true <->
    FinSet.mem (delta_ground_encoding prog) (p, ts) s = true).
Proof.
  intro Hwf; unfold delta_index; rewrite delta_add_atoms_exact, FinSet.elements_spec by exact Hwf.
  unfold rel_of; rewrite Map.get_empty, FinSet.mem_empty; intuition discriminate.
Qed.

Lemma delta_empty_db_wf {P} (prog : program P) p :
  FinSet.wf tuple_encoding (rel_of prog Map.empty p).
Proof.
  unfold rel_of; rewrite Map.get_empty; apply Map.wf_empty.
Qed.

Definition delta_rows {P} (prog : program P) (db : database P) : P -> list tuple :=
  let snapshot := Map.map FinSet.elements db in
  fun p => match Map.get (penc prog) p snapshot with Some xs => xs | None => [] end.

Lemma delta_rows_exact {P} (prog : program P) db p :
  delta_rows prog db p = FinSet.elements (rel_of prog db p).
Proof.
  unfold delta_rows, rel_of; rewrite Map.get_map.
  destruct (Map.get (penc prog) p db); reflexivity.
Qed.

Definition delta_current_env {P} (prog : program P) (st : stratification P) k lower db p :=
  if Nat.eqb (level st p) k then rel_of prog db p else lower p.

Definition delta_tag_env {P} (prog : program P) st k lower acc front (q : P * bool) :=
  if snd q then rel_of prog front (fst q)
  else delta_current_env prog st k lower acc (fst q).

Definition delta_job P := ((rule P * atom P) * delta_join_plan (P * bool))%type.

Fixpoint delta_nested_rows {Q} (ps : list (atom Q)) bound rows : delta_nested_cache Q :=
  match ps with
  | [] => []
  | a :: rest =>
    (a, NestedSearch bound (args a) (build_index bound (args a) (rows (pred a)))) ::
      delta_nested_rows rest (bound_add bound a) rows
  end.

Lemma delta_nested_rows_agrees {Q} (ps : list (atom Q)) bound rows env :
  (forall a, In a ps -> rows (pred a) = FinSet.elements (env (pred a))) ->
  delta_nested_rows ps bound rows = delta_prepare_nested ps bound env.
Proof.
  revert bound; induction ps as [|a ps IH]; intros bound Hrows; cbn; [reflexivity |].
  rewrite (Hrows a (or_introl eq_refl)); f_equal; apply IH.
  intros x Hx; apply Hrows; now right.
Qed.

Fixpoint delta_multiway_rows {Q} vs bound (ps : list (atom Q)) rows
    : list (delta_variable_cache Q) :=
  match vs with
  | [] => []
  | v :: rest => DeltaVariableCache v bound
      (map (fun a => (a, VariableSearch (args a)
        (build_variable_index bound (args a) v (rows (pred a))))) (atoms_with_variable v ps)) ::
      delta_multiway_rows rest (FinSet.add nat_encoding v bound) ps rows
  end.

Lemma delta_multiway_rows_agrees {Q} vs bound (ps : list (atom Q)) rows env :
  (forall a, In a ps -> rows (pred a) = FinSet.elements (env (pred a))) ->
  delta_multiway_rows vs bound ps rows = delta_prepare_multiway vs bound ps env.
Proof.
  intro Hrows; revert bound; induction vs as [|v vs IH]; intro bound; cbn; [reflexivity |].
  rewrite IH; f_equal; f_equal; apply map_ext_in; intros a Ha.
  apply atoms_with_variable_spec in Ha; rewrite (Hrows a (proj1 Ha)); reflexivity.
Qed.

Definition delta_plan_rows {Q} strategy (ps : list (atom Q)) rows : delta_join_plan Q :=
  match strategy with
  | IndexedNested => DeltaNested (delta_nested_rows ps FinSet.empty rows)
  | IndexedMultiway => DeltaMultiway
      (delta_multiway_rows (join_variables ps) FinSet.empty ps rows)
  end.

Lemma delta_plan_rows_agrees {Q} strategy (ps : list (atom Q)) rows env :
  (forall a, In a ps -> rows (pred a) = FinSet.elements (env (pred a))) ->
  delta_plan_rows strategy ps rows = delta_prepare_plan strategy ps env.
Proof.
  intro Hrows; destruct strategy; cbn.
  - rewrite (delta_nested_rows_agrees ps FinSet.empty rows env Hrows); reflexivity.
  - rewrite (delta_multiway_rows_agrees _ FinSet.empty ps rows env Hrows); reflexivity.
Qed.

Definition delta_prepare_jobs {P} strategy (prog : program P) st k lower acc front
    : list (delta_job P) :=
  let specs := delta_specs prog st k in
  let env := delta_tag_env prog st k lower acc front in
  let atoms := flat_map (fun spec =>
    positive_atoms (body (delta_tag_rule (penc prog) (fst spec) (snd spec)))) specs in
  let rows := join_relation_rows (pair_encoding (penc prog) bool_encoding)
    (prepare_join_relations (pair_encoding (penc prog) bool_encoding) atoms env) in
  map (fun spec => let '(r, pivot) := spec in
    (spec, delta_plan_rows strategy
      (positive_atoms (body (delta_tag_rule (penc prog) r pivot))) rows)) specs.

Lemma delta_prepare_jobs_exact {P} strategy (prog : program P) st k lower acc front :
  (forall q, FinSet.wf tuple_encoding (delta_tag_env prog st k lower acc front q)) ->
  forall r pivot plan, In ((r, pivot), plan)
    (delta_prepare_jobs strategy prog st k lower acc front) ->
    delta_plan_exact strategy (positive_atoms (body (delta_tag_rule (penc prog) r pivot)))
      (delta_tag_env prog st k lower acc front) plan.
Proof.
  intros Hwf r pivot plan Hin; unfold delta_prepare_jobs in Hin; apply in_map_iff in Hin.
  destruct Hin as [[x a] [Heq Hspec]]; cbn in Heq; injection Heq as Heqr Heqa Heqp.
  subst x a plan; rewrite delta_plan_rows_agrees with
    (env := delta_tag_env prog st k lower acc front).
  - apply delta_prepare_plan_exact; exact Hwf.
  - intros a Ha; apply prepare_join_relations_get, in_flat_map.
    exists (r, pivot); split; [exact Hspec | exact Ha].
Qed.

Definition delta_update_jobs {P} (prog : program P) rows (jobs : list (delta_job P)) :=
  map (fun job => (fst job, delta_update_plan (@snd P bool)
    (fun q => rows (fst q)) (snd job))) jobs.

Definition delta_candidates {P} (prog : program P) facts st k lower acc front
    (jobs : list (delta_job P)) : FinSet.t (ground_atom P) :=
  FinSet.of_list (delta_ground_encoding prog)
    (flat_map (fun job => let '((r, pivot), plan) := job in
      map (fun ts => (pred (head r), ts))
        (delta_variant_rows prog facts lower r pivot
          (delta_tag_env prog st k lower acc front) plan)) jobs).

Record delta_state (P : Type) : Type := DeltaState {
  delta_accumulated : FinSet.t (ground_atom P);
  delta_frontier : FinSet.t (ground_atom P);
  delta_accumulated_index : database P;
  delta_frontier_index : database P;
  delta_jobs : list (delta_job P)
}.

Arguments DeltaState {P}.
Arguments delta_accumulated {P}.
Arguments delta_frontier {P}.
Arguments delta_accumulated_index {P}.
Arguments delta_frontier_index {P}.
Arguments delta_jobs {P}.

Section DeltaIteration.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (k : nat) (lower : P -> FinSet.t tuple).

Local Abbreviation GE := (delta_ground_encoding prog).

Definition delta_new (s : delta_state P) :=
  FinSet.diff GE (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s))
    (delta_accumulated s).

Lemma delta_new_fresh s f : FinSet.mem GE f (delta_new s) = true ->
  FinSet.mem GE f (delta_accumulated s) = false.
Proof.
  intro Hin; apply FinSet.mem_diff in Hin; exact (proj2 Hin).
Qed.

Definition delta_advance (s : delta_state P) (batch : FinSet.t (ground_atom P)) : delta_state P :=
  let new_index := delta_index prog batch in
  let rows := delta_rows prog new_index in
  DeltaState (FinSet.union GE (delta_accumulated s) batch) batch
    (delta_add_atoms prog (FinSet.elements batch) (delta_accumulated_index s))
    new_index (delta_update_jobs prog rows (delta_jobs s)).

Definition delta_step (s : delta_state P) : option (delta_state P) :=
  let batch := delta_new s in
  if FinSet.is_empty batch then None else Some (delta_advance s batch).

(** The finite universe occurs only in proof terms used to establish accessibility. *)
Definition delta_support : list (ground_atom P) :=
  flat_map (fun p => map (fun ts => (p, ts)) (herbrand prog facts))
    (FinSet.elements (preds prog facts)).

Definition delta_valid (s : delta_state P) : Prop :=
  FinSet.wf GE (delta_accumulated s) /\
  forall f, FinSet.mem GE f (delta_accumulated s) = true -> In f delta_support.

Lemma delta_universe_support p ts :
  in_universe prog facts p ts = true -> In (p, ts) delta_support.
Proof.
  intro Huniv; apply in_universe_spec in Huniv; destruct Huniv as [Hp [Hlen Hcs]].
  unfold delta_support; apply in_flat_map; exists p; split.
  - apply (FinSet.elements_spec (penc prog)); [apply preds_wf | exact Hp].
  - apply in_map, (proj2 (herbrand_spec prog facts ts)); exists p; auto.
Qed.

Lemma delta_candidates_support s :
  FinSet.wf GE (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s)) /\
  forall f, FinSet.mem GE f (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s)) = true ->
    In f delta_support.
Proof.
  split; [apply FinSet.wf_fold_add, Map.wf_empty |].
  intros f Hmem; apply FinSet.of_list_spec in Hmem; apply in_flat_map in Hmem.
  destruct Hmem as [[[r pivot] plan] [_ Hin]]; apply in_map_iff in Hin.
  destruct Hin as [ts [Heq Hin]]; subst f; apply delta_universe_support.
  apply filter_In in Hin; exact (proj2 Hin).
Qed.

Lemma delta_new_wf s : delta_valid s -> FinSet.wf GE (delta_new s).
Proof.
  intros [Hwf _]; apply FinSet.wf_diff;
    [exact (proj1 (delta_candidates_support s)) | exact Hwf].
Qed.

Lemma delta_advance_valid s : delta_valid s -> delta_valid (delta_advance s (delta_new s)).
Proof.
  intros [Hwf Hsupport]; split; cbn [delta_advance delta_accumulated].
  - apply FinSet.wf_union; [exact Hwf | apply delta_new_wf; split; assumption].
  - intros f Hin; apply FinSet.mem_union in Hin; destruct Hin as [Hin | Hin].
    + apply Hsupport; exact Hin.
    + apply FinSet.mem_diff in Hin; apply (proj2 (delta_candidates_support s)); exact (proj1 Hin).
Qed.

Lemma delta_step_valid s t : delta_valid s -> delta_step s = Some t -> delta_valid t.
Proof.
  intros Hvalid Hstep; unfold delta_step in Hstep.
  destruct (FinSet.is_empty (delta_new s)); [discriminate |].
  injection Hstep as Heq; subst t; apply delta_advance_valid; exact Hvalid.
Qed.

Definition delta_remaining (s : delta_state P) :=
  length delta_support - FinSet.size (delta_accumulated s).

Lemma delta_step_decreases s t :
  delta_valid s -> delta_step s = Some t -> delta_remaining t < delta_remaining s.
Proof.
  intros Hvalid Hstep; unfold delta_step in Hstep.
  destruct (FinSet.is_empty (delta_new s)) eqn:Hempty; [discriminate |].
  injection Hstep as Heq; subst t.
  assert (Hnew := delta_new_wf s Hvalid).
  assert (Hnext := delta_advance_valid s Hvalid).
  assert (Hgrow : FinSet.size (delta_accumulated s) <
    FinSet.size (FinSet.union GE (delta_accumulated s) (delta_new s))).
  { apply (FinSet.size_lt GE); [exact (proj1 Hvalid) | exact (proj1 Hnext) |
      apply set_union_left |].
    destruct (FinSet.subset GE (FinSet.union GE (delta_accumulated s) (delta_new s))
      (delta_accumulated s)) eqn:Hsubset; [|reflexivity].
    exfalso; assert (Hnone : forall f, FinSet.mem GE f (delta_new s) = false).
    { intro f; destruct (FinSet.mem GE f (delta_new s)) eqn:Hmem; [|reflexivity].
      pose proof (set_member_subset GE _ _ Hsubset f
        (proj2 (FinSet.mem_union GE f _ _) (or_intror Hmem))) as Hold.
      apply FinSet.mem_diff in Hmem; destruct Hmem as [_ Habsent]; congruence. }
    apply (proj2 (FinSet.is_empty_spec GE _ Hnew)) in Hnone; congruence. }
  pose proof (FinSet.size_le_length GE _ delta_support (proj1 Hnext) (proj2 Hnext)) as Hbound.
  unfold delta_remaining; cbn [delta_advance delta_accumulated] in *; lia.
Qed.

Lemma delta_accessible s : delta_valid s ->
  Acc (fun t s => delta_step s = Some t) s.
Proof.
  refine (well_founded_induction (well_founded_ltof _ delta_remaining)
    (fun s => delta_valid s -> Acc (fun t s => delta_step s = Some t) s) _ s).
  intros x IH Hvalid; constructor; intros y Hstep.
  apply IH; [apply (delta_step_decreases x y Hvalid Hstep) |].
  apply (delta_step_valid x y Hvalid Hstep).
Defined.

Definition delta_result s : Type :=
  {t : delta_state P | delta_step t = None /\
    clos_refl_trans _ (fun x y => delta_step x = Some y) s t}.

(** Source sets are captured before entering the round loop; joins use retained search indexes. *)
Definition delta_prepared_step : delta_state P -> option (delta_state P) :=
  let accepts := delta_cached_universe prog facts in
  let firing := fun r pivot env plan =>
    filter (accepts (pred (head r)))
      (map (fun b => map (inst (binding_value b)) (args (head r)))
        (filter (negative_ok r lower)
          (delta_plan_bindings (positive_atoms (body (delta_tag_rule (penc prog) r pivot)))
            env plan))) in
  fun s =>
    let candidates := FinSet.of_list GE (flat_map
      (fun job => let '((r, pivot), plan) := job in
        map (fun ts => (pred (head r), ts))
          (firing r pivot (delta_tag_env prog st k lower
            (delta_accumulated_index s) (delta_frontier_index s)) plan)) (delta_jobs s)) in
    let batch := FinSet.diff GE candidates (delta_accumulated s) in
    if FinSet.is_empty batch then None else Some (delta_advance s batch).

Lemma delta_prepared_step_agrees s : delta_prepared_step s = delta_step s.
Proof.
  reflexivity.
Qed.

Definition delta_prepared_body (step : delta_state P -> option (delta_state P))
    (Hstep : forall s, step s = delta_step s) s
    (rec : forall t, delta_step s = Some t -> delta_result t) : delta_result s.
Proof.
  destruct (step s) as [t |] eqn:Hnext.
  - pose proof (eq_trans (eq_sym (Hstep s)) Hnext) as Hactual.
    destruct (rec t Hactual) as [last [Hdone Htrace]].
    refine (exist _ last _); split; [exact Hdone |].
    eapply rt_trans; [apply rt_step; exact Hactual | exact Htrace].
  - refine (exist _ s _); split; [exact (eq_trans (eq_sym (Hstep s)) Hnext) | apply rt_refl].
Defined.

(** Accessibility gives a finite run ending only after every pending candidate is already known. *)
Definition delta_execute s (Hvalid : delta_valid s) : delta_result s :=
  Fix_F delta_result (delta_prepared_body delta_prepared_step delta_prepared_step_agrees)
    (delta_accessible s Hvalid).

End DeltaIteration.

(** * Initialization and total stratum scheduling *)

Definition delta_seed_atoms {P} strategy (prog : program P) facts st k lower
    : list (ground_atom P) :=
  let accepts := delta_cached_universe prog facts in
  let env := delta_current_env prog st k lower Map.empty in
  let firing := fun r => FinSet.of_list tuple_encoding
    (filter (accepts (pred (head r)))
      (map (fun b => map (inst (binding_value b)) (args (head r)))
        (filter (negative_ok r env) (selected_bindings strategy prog r env)))) in
  filter (fun f => Nat.eqb (level st (fst f)) k &&
    accepts (fst f) (snd f)) facts ++
  flat_map (fun r => map (fun ts => (pred (head r), ts))
    (FinSet.elements (firing r)))
    (filter (fun r => Nat.eqb (level st (pred (head r))) k &&
      match delta_recursive_atoms st k r with [] => true | _ :: _ => false end) (rules prog)).

Definition delta_initial {P} strategy (prog : program P) facts st k lower : delta_state P :=
  let seeds := FinSet.of_list (delta_ground_encoding prog)
    (delta_seed_atoms strategy prog facts st k lower) in
  let idx := delta_index prog seeds in
  DeltaState seeds seeds idx idx (delta_prepare_jobs strategy prog st k lower idx idx).

Lemma delta_initial_valid {P} strategy (prog : program P) facts st k lower :
  delta_valid prog facts (delta_initial strategy prog facts st k lower).
Proof.
  split; [apply FinSet.wf_fold_add, Map.wf_empty |].
  intros f Hin; apply FinSet.of_list_spec in Hin; unfold delta_seed_atoms in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
  - apply filter_In in Hin; destruct Hin as [_ Htest]; apply andb_true_iff in Htest.
    destruct f as [p ts]; apply delta_universe_support; exact (proj2 Htest).
  - apply in_flat_map in Hin; destruct Hin as [r [_ Hin]]; apply in_map_iff in Hin.
    destruct Hin as [ts [Heq Hin]]; subst f; apply delta_universe_support.
    apply (FinSet.elements_spec tuple_encoding) in Hin.
    + apply fire_rule_join_members in Hin; exact (proj1 Hin).
    + apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Definition delta_solve_stratum {P} strategy (prog : program P) facts st k lower : delta_state P :=
  proj1_sig (delta_execute prog facts st k lower
    (delta_initial strategy prog facts st k lower)
    (delta_initial_valid strategy prog facts st k lower)).

Fixpoint delta_solve_levels {P} strategy (prog : program P) facts st (n : nat) : database P :=
  match n with
  | O => Map.empty
  | S k =>
    let lower := delta_solve_levels strategy prog facts st k in
    let result := delta_solve_stratum strategy prog facts st k (rel_of prog lower) in
    delta_add_atoms prog (FinSet.elements (delta_accumulated result)) lower
  end.

(** The semi-naive solver completes each lower stratum before interpreting negated literals. *)
Definition solve_program_delta {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) : option (database P) :=
  match stratify prog with
  | Some st => Some (delta_solve_levels strategy prog facts st (count st))
  | None => None
  end.

(** * Index and frontier invariants *)

Lemma delta_plan_ext {Q} strategy (ps : list (atom Q)) env env' plan :
  (forall q, env q = env' q) -> delta_plan_exact strategy ps env plan ->
  delta_plan_exact strategy ps env' plan.
Proof.
  intros Henv; destruct strategy, plan; cbn; try contradiction; intros [Hexact Hshape]; split.
  - intros a search Hin key row; rewrite <- Henv; apply Hexact; exact Hin.
  - exact Hshape.
  - intros layer Hin a search Hnode; destruct (Hexact layer Hin a search Hnode) as [Hwf Hmem].
    split; [exact Hwf |]; intros key c; rewrite <- Henv; apply Hmem.
  - exact Hshape.
Qed.

Lemma delta_tag_env_wf {P} (prog : program P) st k lower acc front :
  (forall p, FinSet.wf tuple_encoding (lower p)) ->
  (forall p, FinSet.wf tuple_encoding (rel_of prog acc p)) ->
  (forall p, FinSet.wf tuple_encoding (rel_of prog front p)) ->
  forall q, FinSet.wf tuple_encoding (delta_tag_env prog st k lower acc front q).
Proof.
  intros Hlower Hacc Hfront [p b]; unfold delta_tag_env; cbn.
  destruct b; [apply Hfront |]; unfold delta_current_env.
  destruct (Nat.eqb (level st p) k); [apply Hacc | apply Hlower].
Qed.

Lemma delta_seed_level {P} strategy (prog : program P) facts st k lower f :
  In f (delta_seed_atoms strategy prog facts st k lower) -> level st (fst f) = k.
Proof.
  unfold delta_seed_atoms; rewrite in_app_iff; intros [Hin | Hin].
  - apply filter_In in Hin; destruct Hin as [_ Htest]; apply andb_true_iff in Htest.
    apply Nat.eqb_eq; exact (proj1 Htest).
  - apply in_flat_map in Hin; destruct Hin as [r [Hr Hin]].
    apply filter_In in Hr; destruct Hr as [_ Htest]; apply andb_true_iff in Htest.
    apply in_map_iff in Hin; destruct Hin as [ts [Heq _]]; subst f; cbn.
    apply Nat.eqb_eq; exact (proj1 Htest).
Qed.

Section DeltaInvariants.
Context {P : Type} (strategy : join_strategy) (prog : program P)
  (facts : list (ground_atom P)) (st : stratification P) (k : nat)
  (lower : P -> FinSet.t tuple).
Local Abbreviation GE := (delta_ground_encoding prog).
Local Abbreviation member := (FinSet.mem GE).
Local Abbreviation environment s :=
  (delta_current_env prog st k lower (delta_accumulated_index s)).
Local Abbreviation tagged s :=
  (delta_tag_env prog st k lower (delta_accumulated_index s) (delta_frontier_index s)).

(** Index agreement couples the finite termination support to the relations used by every join. *)
Record delta_ready (s : delta_state P) : Prop := DeltaReady {
  delta_ready_valid : delta_valid prog facts s;
  delta_ready_front_wf : FinSet.wf GE (delta_frontier s);
  delta_ready_acc_index_wf : forall p,
    FinSet.wf tuple_encoding (rel_of prog (delta_accumulated_index s) p);
  delta_ready_front_index_wf : forall p,
    FinSet.wf tuple_encoding (rel_of prog (delta_frontier_index s) p);
  delta_ready_acc_index_exact : forall p ts,
    FinSet.mem tuple_encoding ts (rel_of prog (delta_accumulated_index s) p) = true <->
      member (p, ts) (delta_accumulated s) = true;
  delta_ready_front_index_exact : forall p ts,
    FinSet.mem tuple_encoding ts (rel_of prog (delta_frontier_index s) p) = true <->
      member (p, ts) (delta_frontier s) = true;
  delta_ready_front_subset : forall f, member f (delta_frontier s) = true ->
    member f (delta_accumulated s) = true;
  delta_ready_level : forall f, member f (delta_accumulated s) = true -> level st (fst f) = k;
  delta_ready_specs : map fst (delta_jobs s) = delta_specs prog st k;
  delta_ready_plans : forall r pivot plan, In ((r, pivot), plan) (delta_jobs s) ->
    delta_plan_exact strategy (positive_atoms (body (delta_tag_rule (penc prog) r pivot)))
      (tagged s) plan
}.

Lemma delta_ready_tagged_wf s :
  (forall p, FinSet.wf tuple_encoding (lower p)) -> delta_ready s ->
  forall q, FinSet.wf tuple_encoding (tagged s q).
Proof.
  intros Hlower Hready; apply delta_tag_env_wf; [exact Hlower |
    apply (delta_ready_acc_index_wf s Hready) | apply (delta_ready_front_index_wf s Hready)].
Qed.

Lemma delta_job_member s r pivot plan : delta_ready s ->
  In ((r, pivot), plan) (delta_jobs s) ->
  In r (rules prog) /\ level st (pred (head r)) = k /\
    In (LPos pivot) (body r) /\ level st (pred pivot) = k.
Proof.
  intros Hready Hin; apply delta_specs_spec.
  rewrite <- (delta_ready_specs s Hready); apply in_map_iff.
  exists ((r, pivot), plan); split; [reflexivity | exact Hin].
Qed.

Lemma delta_job_exists s r pivot : delta_ready s -> In r (rules prog) ->
  level st (pred (head r)) = k -> In (LPos pivot) (body r) -> level st (pred pivot) = k ->
  exists plan, In ((r, pivot), plan) (delta_jobs s).
Proof.
  intros Hready Hr Hlevel Hp Hplevel.
  assert (Hin : In (r, pivot) (delta_specs prog st k)).
  { apply delta_specs_spec; auto. }
  rewrite <- (delta_ready_specs s Hready) in Hin; apply in_map_iff in Hin.
  destruct Hin as [[[x a] plan] [Heq Hin]]; cbn in Heq; injection Heq as Heqr Heqa.
  subst x a; exists plan; exact Hin.
Qed.

Lemma delta_initial_ready :
  (forall p, FinSet.wf tuple_encoding (lower p)) ->
  delta_ready (delta_initial strategy prog facts st k lower).
Proof.
  intro Hlower; constructor; cbn [delta_initial].
  - exact (delta_initial_valid strategy prog facts st k lower).
  - apply FinSet.wf_fold_add, Map.wf_empty.
  - apply delta_add_atoms_wf, delta_empty_db_wf.
  - apply delta_add_atoms_wf, delta_empty_db_wf.
  - intros p ts; apply delta_index_exact, FinSet.wf_fold_add, Map.wf_empty.
  - intros p ts; apply delta_index_exact, FinSet.wf_fold_add, Map.wf_empty.
  - intros f Hin; exact Hin.
  - intros f Hin; apply (delta_seed_level strategy prog facts st k lower f).
    apply FinSet.of_list_spec in Hin; exact Hin.
  - cbn [delta_initial delta_jobs]; unfold delta_prepare_jobs; rewrite map_map.
    rewrite <- (map_id (delta_specs prog st k)) at 2; apply map_ext; intros [r pivot]; reflexivity.
  - intros r pivot plan Hin; cbn [delta_initial delta_jobs] in Hin.
    eapply delta_prepare_jobs_exact; [|exact Hin].
    apply delta_tag_env_wf; [exact Hlower | apply delta_add_atoms_wf, delta_empty_db_wf |
      apply delta_add_atoms_wf, delta_empty_db_wf].
Qed.

Lemma delta_new_level s : delta_ready s ->
  forall f, member f (delta_new prog facts st k lower s) = true -> level st (fst f) = k.
Proof.
  intros Hready f Hin; apply FinSet.mem_diff in Hin; destruct Hin as [Hin _].
  apply FinSet.of_list_spec in Hin; apply in_flat_map in Hin.
  destruct Hin as [[[r pivot] plan] [Hjob Hin]]; apply in_map_iff in Hin.
  destruct Hin as [ts [Heq _]]; subst f; cbn.
  exact (proj1 (proj2 (delta_job_member s r pivot plan Hready Hjob))).
Qed.

Lemma delta_advance_index_exact s p ts :
  delta_ready s ->
  (FinSet.mem tuple_encoding ts
    (rel_of prog (delta_accumulated_index
      (delta_advance prog s (delta_new prog facts st k lower s))) p) = true <->
    member (p, ts) (delta_accumulated
      (delta_advance prog s (delta_new prog facts st k lower s))) = true).
Proof.
  intro Hready; cbn [delta_advance delta_accumulated_index delta_accumulated].
  rewrite delta_add_atoms_exact, FinSet.mem_union.
  rewrite FinSet.elements_spec by
    (apply delta_new_wf; apply (delta_ready_valid s Hready)).
  rewrite (delta_ready_acc_index_exact s Hready); reflexivity.
Qed.

Lemma delta_advance_tagged s : (forall p, FinSet.wf tuple_encoding (lower p)) -> delta_ready s ->
  forall q, delta_updated_env (@snd P bool)
    (fun q => delta_rows prog (delta_index prog (delta_new prog facts st k lower s)) (fst q))
    (tagged s) q =
    tagged (delta_advance prog s (delta_new prog facts st k lower s)) q.
Proof.
  intros Hlower Hready [p b].
  set (batch := delta_new prog facts st k lower s).
  assert (Hbatch : FinSet.wf GE batch) by
    (apply delta_new_wf, (delta_ready_valid s Hready)).
  assert (Hbatchdb : forall p, FinSet.wf tuple_encoding (rel_of prog (delta_index prog batch) p)).
  { apply delta_add_atoms_wf, delta_empty_db_wf. }
  assert (Hadded : FinSet.of_list tuple_encoding
    (delta_rows prog (delta_index prog batch) p) = rel_of prog (delta_index prog batch) p).
  { rewrite delta_rows_exact; apply (FinSet.extensionality tuple_encoding).
    - apply FinSet.wf_fold_add, Map.wf_empty.
    - apply Hbatchdb.
    - intro ts; apply eq_true_iff_eq; rewrite FinSet.of_list_spec,
        FinSet.elements_spec by apply Hbatchdb; reflexivity. }
  unfold delta_updated_env; cbn [fst snd]; rewrite Hadded.
  unfold delta_tag_env; cbn [fst snd]; destruct b; [reflexivity |].
  cbn [delta_advance delta_accumulated_index].
  unfold delta_current_env; destruct (Nat.eqb (level st p) k) eqn:Hlevel.
  - apply (FinSet.extensionality tuple_encoding).
    + apply FinSet.wf_union; [apply (delta_ready_acc_index_wf s Hready) | apply Hbatchdb].
    + apply delta_add_atoms_wf, (delta_ready_acc_index_wf s Hready).
    + intro ts; apply eq_true_iff_eq; rewrite FinSet.mem_union, delta_add_atoms_exact,
        FinSet.elements_spec by exact Hbatch; rewrite delta_index_exact by exact Hbatch.
      reflexivity.
  - assert (Hempty : forall ts, FinSet.mem tuple_encoding ts
      (rel_of prog (delta_index prog batch) p) = false).
    { intro ts; destruct (FinSet.mem tuple_encoding ts
        (rel_of prog (delta_index prog batch) p)) eqn:Hmem; [|reflexivity].
      apply (delta_index_exact prog batch p ts Hbatch) in Hmem.
      pose proof (delta_new_level s Hready (p, ts) Hmem) as Heq.
      cbn in Heq; rewrite Heq, Nat.eqb_refl in Hlevel; discriminate. }
    apply (FinSet.extensionality tuple_encoding).
    + apply FinSet.wf_union; [apply Hlower | apply Hbatchdb].
    + apply Hlower.
    + intro ts; apply eq_true_iff_eq; rewrite FinSet.mem_union, Hempty; intuition discriminate.
Qed.

Lemma delta_advance_ready s : (forall p, FinSet.wf tuple_encoding (lower p)) ->
  delta_ready s -> delta_ready (delta_advance prog s (delta_new prog facts st k lower s)).
Proof.
  intros Hlower Hready; constructor.
  - apply delta_advance_valid, (delta_ready_valid s Hready).
  - apply delta_new_wf, (delta_ready_valid s Hready).
  - apply delta_add_atoms_wf, (delta_ready_acc_index_wf s Hready).
  - apply delta_add_atoms_wf, delta_empty_db_wf.
  - intros p ts; apply delta_advance_index_exact; exact Hready.
  - intros p ts; apply delta_index_exact, delta_new_wf, (delta_ready_valid s Hready).
  - intros f Hin; apply FinSet.mem_union; now right.
  - intros f Hin; apply FinSet.mem_union in Hin; destruct Hin as [Hin | Hin].
    + apply (delta_ready_level s Hready); exact Hin.
    + apply (delta_new_level s Hready); exact Hin.
  - cbn [delta_advance delta_jobs]; unfold delta_update_jobs; rewrite map_map.
    rewrite <- (delta_ready_specs s Hready); apply map_ext; intros [[r pivot] plan]; reflexivity.
  - intros r pivot plan Hin; cbn [delta_advance delta_jobs] in Hin.
    unfold delta_update_jobs in Hin; apply in_map_iff in Hin.
    destruct Hin as [[[x a] old] [Heq Hjob]]; cbn in Heq.
    injection Heq as Heqr Heqa Heqp; subst x a plan.
    eapply delta_plan_ext.
    + apply delta_advance_tagged; assumption.
    + apply delta_update_plan_exact, (delta_ready_plans s Hready r pivot old Hjob).
Qed.

Lemma delta_step_ready s t : (forall p, FinSet.wf tuple_encoding (lower p)) ->
  delta_ready s -> delta_step prog facts st k lower s = Some t -> delta_ready t.
Proof.
  intros Hlower Hready Hstep; unfold delta_step in Hstep.
  destruct (FinSet.is_empty (delta_new prog facts st k lower s)); [discriminate |].
  injection Hstep as Heq; subst t; apply delta_advance_ready; assumption.
Qed.

End DeltaInvariants.

(** * Finite observations of the same transition system *)

Lemma delta_terminal_unique {A} (step : A -> option A) x y z :
  clos_refl_trans _ (fun a b => step a = Some b) x y -> step y = None ->
  clos_refl_trans _ (fun a b => step a = Some b) x z -> step z = None -> y = z.
Proof.
  intros Hxy Hynone Hxz Hznone; apply clos_rt_rt1n in Hxy; apply clos_rt_rt1n in Hxz.
  revert z Hxz Hznone; induction Hxy as [x | x u y Hstep Huy IH]; intros z Hxz Hznone.
  - destruct Hxz as [|v z Hstep Huz]; [reflexivity | congruence].
  - destruct Hxz as [|v z Hstep' Hvz]; [congruence |].
    assert (Heq : u = v) by congruence; subst v; apply IH; assumption.
Qed.

Definition delta_one {P} prog facts st k lower (s : delta_state P) : delta_state P :=
  match delta_step prog facts st k lower s with
  | Some next => next
  | None => s
  end.

Fixpoint delta_observe_steps {P} prog facts st k lower (fuel : positive)
    (s : delta_state P) : delta_state P :=
  match fuel with
  | xH => delta_one prog facts st k lower s
  | xO rest =>
    delta_observe_steps prog facts st k lower rest
      (delta_observe_steps prog facts st k lower rest s)
  | xI rest =>
    delta_one prog facts st k lower
      (delta_observe_steps prog facts st k lower rest
        (delta_observe_steps prog facts st k lower rest s))
  end.

Lemma delta_one_trace {P} prog facts st k lower (s : delta_state P) :
  clos_refl_trans _ (fun a b => delta_step prog facts st k lower a = Some b)
    s (delta_one prog facts st k lower s).
Proof.
  unfold delta_one; destruct (delta_step prog facts st k lower s) eqn:Hstep.
  - apply rt_step; exact Hstep.
  - apply rt_refl.
Qed.

Lemma delta_observe_steps_trace {P} prog facts st k lower fuel (s : delta_state P) :
  clos_refl_trans _ (fun a b => delta_step prog facts st k lower a = Some b)
    s (delta_observe_steps prog facts st k lower fuel s).
Proof.
  revert s; induction fuel as [fuel IH | fuel IH |]; intro s; cbn.
  - eapply rt_trans; [eapply rt_trans; [apply IH | apply IH] | apply delta_one_trace].
  - eapply rt_trans; apply IH.
  - apply delta_one_trace.
Qed.

Lemma delta_execute_observation {P} prog facts st k lower fuel (s : delta_state P) Hvalid :
  delta_step prog facts st k lower (delta_observe_steps prog facts st k lower fuel s) = None ->
  proj1_sig (delta_execute prog facts st k lower s Hvalid) =
    delta_observe_steps prog facts st k lower fuel s.
Proof.
  intro Hdone; destruct (proj2_sig (delta_execute prog facts st k lower s Hvalid)) as
    [Hlast Htrace].
  eapply delta_terminal_unique; [exact Htrace | exact Hlast | | exact Hdone].
  apply delta_observe_steps_trace.
Qed.

Definition delta_bounded_stratum {P} strategy (prog : program P) facts st k lower fuel
    : option (delta_state P) :=
  let result := delta_observe_steps prog facts st k lower fuel
    (delta_initial strategy prog facts st k lower) in
  match delta_step prog facts st k lower result with
  | Some _ => None
  | None => Some result
  end.

Lemma delta_bounded_stratum_agrees {P} strategy (prog : program P) facts st k lower fuel result :
  delta_bounded_stratum strategy prog facts st k lower fuel = Some result ->
  delta_solve_stratum strategy prog facts st k lower = result.
Proof.
  unfold delta_bounded_stratum; destruct (delta_step prog facts st k lower
    (delta_observe_steps prog facts st k lower fuel
      (delta_initial strategy prog facts st k lower))) eqn:Hstep; [discriminate |].
  intro Heq; injection Heq as Heq; subst result; apply delta_execute_observation; exact Hstep.
Qed.

Fixpoint delta_bounded_levels {P} strategy (prog : program P) facts st fuel n
    : option (database P) :=
  match n with
  | O => Some Map.empty
  | S k =>
    match delta_bounded_levels strategy prog facts st fuel k with
    | None => None
    | Some lower =>
      match delta_bounded_stratum strategy prog facts st k (rel_of prog lower) fuel with
      | None => None
      | Some result => Some (delta_add_atoms prog
          (FinSet.elements (delta_accumulated result)) lower)
      end
    end
  end.

Lemma delta_bounded_levels_agrees {P} strategy (prog : program P) facts st fuel n db :
  delta_bounded_levels strategy prog facts st fuel n = Some db ->
  delta_solve_levels strategy prog facts st n = db.
Proof.
  revert db; induction n as [|k IH]; intros db Hrun; cbn in Hrun.
  - injection Hrun as Heq; exact Heq.
  - destruct (delta_bounded_levels strategy prog facts st fuel k) as [lower |] eqn:Hlower;
      [|discriminate].
    destruct (delta_bounded_stratum strategy prog facts st k (rel_of prog lower) fuel)
      as [result |] eqn:Hresult; [|discriminate].
    injection Hrun as Heq; subst db; cbn [delta_solve_levels].
    rewrite (IH lower eq_refl), (delta_bounded_stratum_agrees _ _ _ _ _ _ _ _ Hresult).
    reflexivity.
Qed.

Definition delta_bounded_program {P} strategy (prog : program P) facts fuel : option (database P) :=
  match stratify prog with
  | Some st => delta_bounded_levels strategy prog facts st fuel (count st)
  | None => None
  end.

(** A successful finite observation is the exact result of the total semi-naive solver. *)
Theorem delta_bounded_program_agrees {P} strategy (prog : program P) facts fuel db :
  delta_bounded_program strategy prog facts fuel = Some db ->
  solve_program_delta strategy prog facts = Some db.
Proof.
  unfold delta_bounded_program, solve_program_delta; destruct (stratify prog) as [st |];
    [|discriminate].
  intro Hrun; f_equal; apply (delta_bounded_levels_agrees strategy prog facts st fuel _ _ Hrun).
Qed.

(** * Derivability and pending work *)

Section DeltaCorrectness.
Context {P : Type} (strategy : join_strategy) (prog : program P)
  (facts : list (ground_atom P)) (st : stratification P) (k : nat)
  (lower : P -> FinSet.t tuple).
Hypotheses (Hprogram : program_wf prog facts) (Hstrat : stratified prog st)
  (Hlower : represents lower (model_below prog facts st k)).
Local Abbreviation GE := (delta_ground_encoding prog).
Local Abbreviation member := (FinSet.mem GE).
Local Abbreviation ready := (delta_ready strategy prog facts st k lower).
Local Abbreviation environment s :=
  (delta_current_env prog st k lower (delta_accumulated_index s)).
Local Abbreviation tagged s :=
  (delta_tag_env prog st k lower (delta_accumulated_index s) (delta_frontier_index s)).
Local Abbreviation derivation := (derives prog facts st k (model_below prog facts st k)).
Local Abbreviation batch s := (delta_new prog facts st k lower s).
Local Abbreviation advance s := (delta_advance prog s (batch s)).

Definition delta_derived (s : delta_state P) : Prop :=
  forall f, member f (delta_accumulated s) = true -> derivation f.

(** A satisfied rule is already closed or has a recursive premise in the current frontier. *)
Definition delta_pending (s : delta_state P) : Prop :=
  forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
    in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
    delta_body_holds r (environment s) lower sigma ->
    member (ground sigma (head r)) (delta_accumulated s) = true \/
    exists a, In (LPos a) (body r) /\ level st (pred a) = k /\
      member (ground sigma a) (delta_frontier s) = true.

Definition delta_facts_present (s : delta_state P) : Prop :=
  forall f, In f facts -> level st (fst f) = k -> member f (delta_accumulated s) = true.

Lemma delta_tagged_positive s pivot a ts : ready s -> level st (pred pivot) = k ->
  FinSet.mem tuple_encoding ts (tagged s (pred (delta_tag_atom (penc prog) pivot a))) = true ->
  FinSet.mem tuple_encoding ts (environment s (pred a)) = true.
Proof.
  intros Hready Hpivot Hin; unfold delta_tag_atom in Hin; cbn [pred] in Hin.
  destruct (delta_atom_eqb (penc prog) a pivot) eqn:Heq.
  - apply delta_atom_eqb_spec in Heq; subst a; unfold delta_tag_env in Hin; cbn in Hin.
    unfold delta_current_env; rewrite Hpivot, Nat.eqb_refl.
    apply (delta_ready_acc_index_exact _ _ _ _ _ _ _ Hready).
    apply (delta_ready_front_subset _ _ _ _ _ _ _ Hready).
    apply (delta_ready_front_index_exact _ _ _ _ _ _ _ Hready); exact Hin.
  - exact Hin.
Qed.

Lemma delta_tagged_complete s pivot sigma : ready s ->
  (forall a, In (LPos a) (body (fst pivot)) -> FinSet.mem tuple_encoding
    (map (inst sigma) (args a)) (environment s (pred a)) = true) ->
  member (ground sigma (snd pivot)) (delta_frontier s) = true ->
  forall a, In (LPos a) (body (fst pivot)) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a))
      (tagged s (pred (delta_tag_atom (penc prog) (snd pivot) a))) = true.
Proof.
  intros Hready Hpos Hdelta a Ha; unfold delta_tag_atom; cbn [pred].
  destruct (delta_atom_eqb (penc prog) a (snd pivot)) eqn:Heq.
  - apply delta_atom_eqb_spec in Heq; subst a; unfold delta_tag_env; cbn.
    apply (delta_ready_front_index_exact _ _ _ _ _ _ _ Hready); exact Hdelta.
  - apply Hpos; exact Ha.
Qed.

Lemma delta_candidates_cover s r sigma pivot :
  ready s -> In r (rules prog) -> level st (pred (head r)) = k ->
  In (LPos pivot) (body r) -> level st (pred pivot) = k ->
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
  delta_body_holds r (environment s) lower sigma ->
  member (ground sigma pivot) (delta_frontier s) = true ->
  member (ground sigma (head r)) (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s)) = true.
Proof.
  intros Hready Hr Hlevel Hpivot Hplevel Huniv [Hpos Hneg] Hdelta.
  destruct (delta_job_exists strategy prog facts st k lower s r pivot
    Hready Hr Hlevel Hpivot Hplevel) as [plan Hjob].
  apply FinSet.of_list_spec, in_flat_map; exists ((r, pivot), plan); split; [exact Hjob |].
  apply in_map_iff; exists (map (inst sigma) (args (head r))); split; [reflexivity |].
  apply (proj2 (delta_variant_rows_exact strategy prog facts lower r pivot
    (tagged s) plan _ (proj1 (proj1 Hprogram r Hr))
    (delta_ready_tagged_wf strategy prog facts st k lower s (proj1 Hlower) Hready)
    (delta_ready_plans _ _ _ _ _ _ _ Hready r pivot plan Hjob))).
  split; [exact Huniv | exists sigma; split; [reflexivity | split; [|exact Hneg]]].
  apply (delta_tagged_complete s (r, pivot) sigma Hready Hpos Hdelta).
Qed.

Lemma delta_candidates_derived s : ready s -> delta_derived s ->
  forall f, member f (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s)) = true ->
    derivation f.
Proof.
  intros Hready Hderived f Hin; apply FinSet.of_list_spec in Hin; apply in_flat_map in Hin.
  destruct Hin as [[[r pivot] plan] [Hjob Hin]]; apply in_map_iff in Hin.
  destruct Hin as [ts [Heq Hin]]; subst f.
  destruct (delta_job_member strategy prog facts st k lower s r pivot plan Hready Hjob) as
    [Hr [Hlevel [_ Hplevel]]].
  apply (proj1 (delta_variant_rows_exact strategy prog facts lower r pivot
    (tagged s) plan ts (proj1 (proj1 Hprogram r Hr))
    (delta_ready_tagged_wf strategy prog facts st k lower s (proj1 Hlower) Hready)
    (delta_ready_plans _ _ _ _ _ _ _ Hready r pivot plan Hjob))) in Hin.
  destruct Hin as [_ [sigma [Hts [Hpos Hneg]]]]; subst ts.
  change (derivation (ground sigma (head r))).
  apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hlevel | | |].
  - intros a Ha Hlt; apply (proj1 (proj2 Hlower _ _)).
    pose proof (delta_tagged_positive s pivot a _ Hready Hplevel (Hpos a Ha)) as Hmem.
    assert (Hne : Nat.eqb (level st (pred a)) k = false) by (apply Nat.eqb_neq; lia).
    unfold delta_current_env in Hmem; rewrite Hne in Hmem; exact Hmem.
  - intros a Ha Heq; apply Hderived.
    pose proof (delta_tagged_positive s pivot a _ Hready Hplevel (Hpos a Ha)) as Hmem.
    unfold delta_current_env in Hmem; rewrite Heq, Nat.eqb_refl in Hmem.
    apply (delta_ready_acc_index_exact _ _ _ _ _ _ _ Hready); exact Hmem.
  - intros a Ha Hbelow; apply (proj2 (proj2 Hlower _ _)) in Hbelow.
    specialize (Hneg a Ha); congruence.
Qed.

Lemma delta_candidate_inserted s f :
  member f (delta_candidates prog facts st k lower
    (delta_accumulated_index s) (delta_frontier_index s) (delta_jobs s)) = true ->
  member f (delta_accumulated (advance s)) = true.
Proof.
  intro Hcandidate; apply FinSet.mem_union.
  destruct (member f (delta_accumulated s)) eqn:Hold; [now left | right].
  apply FinSet.mem_diff; auto.
Qed.

Lemma delta_advance_environment s p ts : ready s ->
  (FinSet.mem tuple_encoding ts (environment (advance s) p) = true <->
    FinSet.mem tuple_encoding ts (environment s p) = true \/ member (p, ts) (batch s) = true).
Proof.
  intro Hready; unfold delta_current_env; destruct (Nat.eqb (level st p) k) eqn:Hlevel.
  - rewrite (delta_advance_index_exact strategy prog facts st k lower s p ts Hready).
    cbn [delta_advance delta_accumulated].
    rewrite FinSet.mem_union, (delta_ready_acc_index_exact _ _ _ _ _ _ _ Hready); reflexivity.
  - assert (Hnone : member (p, ts) (batch s) = false).
    { destruct (member (p, ts) (batch s)) eqn:Hmem; [|reflexivity].
      pose proof (delta_new_level strategy prog facts st k lower s Hready (p, ts) Hmem) as Heq.
      cbn in Heq; rewrite Heq, Nat.eqb_refl in Hlevel; discriminate. }
    rewrite Hnone; intuition discriminate.
Qed.

Lemma delta_advance_pending s : ready s -> delta_pending s -> delta_pending (advance s).
Proof.
  intros Hready Hpending r sigma Hr Hlevel Huniv [Hpos Hneg].
  destruct (existsb (fun a => member (ground sigma a) (batch s)) (positive_atoms (body r)))
    eqn:Hnew.
  - apply existsb_exists in Hnew; destruct Hnew as [a [Ha Hmem]].
    right; exists a; split; [apply positive_atoms_spec; exact Ha | split; [|exact Hmem]].
    exact (delta_new_level strategy prog facts st k lower s Hready (ground sigma a) Hmem).
  - assert (Hold : delta_body_holds r (environment s) lower sigma).
    { split; [|exact Hneg]; intros a Ha.
      pose proof (Hpos a Ha) as Hmem.
      apply (delta_advance_environment s (pred a) _ Hready) in Hmem.
      destruct Hmem as [Hmem | Hmem]; [exact Hmem |].
      assert (Hyes : existsb (fun a => member (ground sigma a) (batch s))
        (positive_atoms (body r)) = true).
      { apply existsb_exists; exists a; split; [apply positive_atoms_spec; exact Ha | exact Hmem]. }
      congruence. }
    destruct (Hpending r sigma Hr Hlevel Huniv Hold) as [Hknown | [a [Ha [Halevel Hdelta]]]].
    + left; apply FinSet.mem_union; now left.
    + left; apply delta_candidate_inserted.
      apply (delta_candidates_cover s r sigma a Hready Hr Hlevel Ha Halevel Huniv Hold Hdelta).
Qed.

Lemma delta_advance_derived s : ready s -> delta_derived s -> delta_derived (advance s).
Proof.
  intros Hready Hderived f Hin; apply FinSet.mem_union in Hin; destruct Hin as [Hin | Hin].
  - apply Hderived; exact Hin.
  - apply FinSet.mem_diff in Hin; apply (delta_candidates_derived s Hready Hderived f (proj1 Hin)).
Qed.

Lemma delta_advance_facts s : delta_facts_present s -> delta_facts_present (advance s).
Proof.
  intros Hfacts f Hf Hlevel; apply FinSet.mem_union; left; apply Hfacts; assumption.
Qed.

Lemma delta_base_wf : env_wf prog (delta_current_env prog st k lower Map.empty).
Proof.
  pose proof (represented_lower_wf prog facts st k lower Hprogram Hstrat Hlower) as Hwf.
  intro p; unfold delta_current_env; destruct (Nat.eqb (level st p) k).
  - split; [apply delta_empty_db_wf |].
    intros ts Hmem; unfold rel_of in Hmem; rewrite Map.get_empty, FinSet.mem_empty in Hmem.
    discriminate.
  - apply Hwf.
Qed.

Lemma delta_nonrecursive_absent r a : delta_recursive_atoms st k r = [] ->
  In (LPos a) (body r) -> level st (pred a) <> k.
Proof.
  intros Hempty Ha Heq; assert (Hin : In a (delta_recursive_atoms st k r)).
  { apply delta_recursive_atoms_spec; auto. }
  rewrite Hempty in Hin; contradiction.
Qed.

Lemma delta_current_lower db p : level st p <> k ->
  delta_current_env prog st k lower db p = lower p.
Proof.
  intro Hne; unfold delta_current_env; apply Nat.eqb_neq in Hne; rewrite Hne; reflexivity.
Qed.

Lemma delta_seed_derived f :
  In f (delta_seed_atoms strategy prog facts st k lower) -> derivation f.
Proof.
  unfold delta_seed_atoms; rewrite in_app_iff; intros [Hin | Hin].
  - apply filter_In in Hin; destruct Hin as [Hfact Htest]; apply andb_true_iff in Htest.
    apply derive_fact; [exact Hfact | apply Nat.eqb_eq; exact (proj1 Htest)].
  - apply in_flat_map in Hin; destruct Hin as [r [Hr Hin]]; apply filter_In in Hr.
    destruct Hr as [Hr Htest]; apply andb_true_iff in Htest; destruct Htest as [Hlevel Hnone].
    apply Nat.eqb_eq in Hlevel; destruct (delta_recursive_atoms st k r) eqn:Hrec;
      [|discriminate].
    apply in_map_iff in Hin; destruct Hin as [ts [Heq Hin]]; subst f.
    apply (FinSet.elements_spec tuple_encoding) in Hin;
      [|apply FinSet.wf_fold_add, Map.wf_empty].
    apply (proj1 (fire_rule_join_exact strategy prog facts r _ Hprogram Hr delta_base_wf ts))
      in Hin.
    apply (proj1 (fire_rule_exact prog facts _ r Hprogram Hr delta_base_wf ts)) in Hin.
    destruct Hin as [_ [sigma [Hts [Hpos Hneg]]]]; subst ts.
    change (derivation (ground sigma (head r))).
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hlevel | | |].
    + intros a Ha Hlt; apply (proj1 (proj2 Hlower _ _)).
      specialize (Hpos a Ha); rewrite delta_current_lower in Hpos by lia; exact Hpos.
    + intros a Ha Heq; exfalso; apply (delta_nonrecursive_absent r a Hrec Ha Heq).
    + intros a Ha Hbelow; apply (proj2 (proj2 Hlower _ _)) in Hbelow.
      specialize (Hneg a Ha); rewrite delta_current_lower in Hneg by
        (pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia).
      congruence.
Qed.

Lemma delta_seed_rule r ts : In r (rules prog) -> level st (pred (head r)) = k ->
  delta_recursive_atoms st k r = [] -> FinSet.mem tuple_encoding ts
    (fire_rule_join strategy prog facts r (delta_current_env prog st k lower Map.empty)) = true ->
  In (pred (head r), ts) (delta_seed_atoms strategy prog facts st k lower).
Proof.
  intros Hr Hlevel Hrec Hmem; unfold delta_seed_atoms; apply in_app_iff; right.
  apply in_flat_map; exists r; split.
  - apply filter_In; split; [exact Hr | rewrite Hlevel, Nat.eqb_refl, Hrec; reflexivity].
  - apply in_map, (FinSet.elements_spec tuple_encoding); [|exact Hmem].
    apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Lemma delta_nonrecursive_complete s r sigma :
  In r (rules prog) -> level st (pred (head r)) = k -> delta_recursive_atoms st k r = [] ->
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
  delta_body_holds r (environment s) lower sigma ->
  FinSet.mem tuple_encoding (map (inst sigma) (args (head r)))
    (fire_rule_join strategy prog facts r (delta_current_env prog st k lower Map.empty)) = true.
Proof.
  intros Hr Hlevel Hrec Huniv [Hpos Hneg].
  apply (proj2 (fire_rule_join_exact strategy prog facts r _ Hprogram Hr delta_base_wf _)).
  apply fire_rule_complete; [exact Hprogram | exact Hr | intro p; apply delta_base_wf |
    exact Huniv | |].
  - intros a Ha; rewrite delta_current_lower by (apply (delta_nonrecursive_absent r a Hrec Ha)).
    specialize (Hpos a Ha); rewrite delta_current_lower in Hpos by
      (apply (delta_nonrecursive_absent r a Hrec Ha)); exact Hpos.
  - intros a Ha; rewrite delta_current_lower by
      (pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia).
    apply Hneg; exact Ha.
Qed.

Lemma delta_initial_derived : delta_derived (delta_initial strategy prog facts st k lower).
Proof.
  intros f Hin; apply delta_seed_derived; apply FinSet.of_list_spec in Hin; exact Hin.
Qed.

Lemma delta_initial_facts : delta_facts_present (delta_initial strategy prog facts st k lower).
Proof.
  intros f Hfact Hlevel; apply FinSet.of_list_spec; unfold delta_seed_atoms.
  apply in_app_iff; left; apply filter_In; split; [exact Hfact |].
  rewrite Hlevel, Nat.eqb_refl; cbn; apply (fact_universe prog facts Hprogram f Hfact).
Qed.

Lemma delta_initial_pending : delta_pending (delta_initial strategy prog facts st k lower).
Proof.
  intros r sigma Hr Hlevel Huniv Hbody.
  destruct (delta_recursive_atoms st k r) as [|a rest] eqn:Hrec.
  - left; apply FinSet.of_list_spec; apply (delta_seed_rule r _ Hr Hlevel Hrec).
    apply (delta_nonrecursive_complete (delta_initial strategy prog facts st k lower)
      r sigma Hr Hlevel Hrec Huniv Hbody).
  - assert (Ha : In a (delta_recursive_atoms st k r)) by (rewrite Hrec; now left).
    apply delta_recursive_atoms_spec in Ha; destruct Ha as [Ha Halevel].
    right; exists a; split; [exact Ha | split; [exact Halevel |]].
    pose proof (proj1 Hbody a Ha) as Hmem; unfold delta_current_env in Hmem.
    rewrite Halevel, Nat.eqb_refl in Hmem.
    apply (delta_ready_acc_index_exact strategy prog facts st k lower _
      (delta_initial_ready strategy prog facts st k lower (proj1 Hlower))) in Hmem.
    exact Hmem.
Qed.

(** The invariant includes derivability, fact seeds, and coverage of every pending rule instance. *)
Definition delta_correct (s : delta_state P) : Prop :=
  ready s /\ delta_derived s /\ delta_facts_present s /\ delta_pending s.

Lemma delta_initial_correct : delta_correct (delta_initial strategy prog facts st k lower).
Proof.
  split; [apply delta_initial_ready; exact (proj1 Hlower) |].
  split; [apply delta_initial_derived | split].
  - apply delta_initial_facts.
  - apply delta_initial_pending.
Qed.

Lemma delta_step_correct s t : delta_correct s ->
  delta_step prog facts st k lower s = Some t -> delta_correct t.
Proof.
  intros [Hready [Hderived [Hfacts Hpending]]] Hstep; unfold delta_step in Hstep.
  destruct (FinSet.is_empty (batch s)); [discriminate |]; injection Hstep as Heq; subst t.
  split; [apply delta_advance_ready; [exact (proj1 Hlower) | exact Hready] |].
  split; [apply delta_advance_derived; assumption | split].
  - apply delta_advance_facts; exact Hfacts.
  - apply delta_advance_pending; assumption.
Qed.

Lemma delta_trace_correct s t : delta_correct s ->
  clos_refl_trans _ (fun a b => delta_step prog facts st k lower a = Some b) s t ->
  delta_correct t.
Proof.
  intros Hcorrect Htrace; induction Htrace as
    [s t Hstep | s | s u t Hsu IHsu Hut IHut].
  - apply (delta_step_correct s t Hcorrect Hstep).
  - exact Hcorrect.
  - apply IHut, IHsu; exact Hcorrect.
Qed.

Lemma delta_quiescent_closed s : delta_correct s -> delta_step prog facts st k lower s = None ->
  forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
    in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
    delta_body_holds r (environment s) lower sigma ->
    member (ground sigma (head r)) (delta_accumulated s) = true.
Proof.
  intros [Hready [_ [_ Hpending]]] Hdone r sigma Hr Hlevel Huniv Hbody.
  destruct (Hpending r sigma Hr Hlevel Huniv Hbody) as [Hknown | [a [Ha [Halevel Hdelta]]]];
    [exact Hknown |].
  pose proof (delta_candidates_cover s r sigma a Hready Hr Hlevel Ha Halevel Huniv Hbody Hdelta)
    as Hcandidate.
  destruct (member (ground sigma (head r)) (delta_accumulated s)) eqn:Hold;
    [reflexivity | exfalso].
  assert (Hnew : member (ground sigma (head r)) (batch s) = true).
  { apply FinSet.mem_diff; auto. }
  unfold delta_step in Hdone; destruct (FinSet.is_empty (batch s)) eqn:Hempty; [|discriminate].
  pose proof (proj1 (FinSet.is_empty_spec GE _
    (delta_new_wf prog facts st k lower s (delta_ready_valid _ _ _ _ _ _ _ Hready)))
    Hempty (ground sigma (head r))) as Habsent; congruence.
Qed.

Lemma delta_closed_contains s : delta_correct s -> delta_step prog facts st k lower s = None ->
  forall f, derivation f -> member f (delta_accumulated s) = true.
Proof.
  intros Hcorrect Hdone f Hderive; destruct Hcorrect as [Hready [Hderived [Hfacts Hpending]]].
  induction Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame IH Hneg].
  - apply Hfacts; assumption.
  - apply (delta_quiescent_closed s
      (conj Hready (conj Hderived (conj Hfacts Hpending))) Hdone r sigma Hr Hlevel).
    + apply (stratum_derives_universe prog facts st k Hprogram Hstrat (ground sigma (head r))).
      apply derive_rule with (r := r) (sigma := sigma); assumption.
    + split.
      * intros a Ha; pose proof (proj2 Hstrat r (LPos a) Hr Ha) as Hbound; cbn in Hbound.
        unfold delta_current_env; destruct (Nat.eqb (level st (pred a)) k) eqn:Heq.
        -- apply Nat.eqb_eq in Heq; apply (delta_ready_acc_index_exact _ _ _ _ _ _ _ Hready).
           apply IH; assumption.
        -- apply Nat.eqb_neq in Heq; apply (proj2 (proj2 Hlower _ _)), Hlow; [exact Ha | lia].
      * intros a Ha; destruct (FinSet.mem tuple_encoding (map (inst sigma) (args a))
          (lower (pred a))) eqn:Hmem; [|reflexivity].
        exfalso; apply (Hneg a Ha), (proj1 (proj2 Hlower _ _)); exact Hmem.
Qed.

Lemma delta_stratum_exact :
  let result := delta_solve_stratum strategy prog facts st k lower in
  delta_correct result /\ forall f, member f (delta_accumulated result) = true <-> derivation f.
Proof.
  set (result := delta_solve_stratum strategy prog facts st k lower).
  destruct (proj2_sig (delta_execute prog facts st k lower
    (delta_initial strategy prog facts st k lower)
    (delta_initial_valid strategy prog facts st k lower))) as [Hdone Htrace].
  assert (Hcorrect : delta_correct result).
  { eapply delta_trace_correct; [apply delta_initial_correct | exact Htrace]. }
  split; [exact Hcorrect | intro f; split].
  - apply (proj1 (proj2 Hcorrect)).
  - apply delta_closed_contains; assumption.
Qed.

End DeltaCorrectness.

(** * The perfect model and compatibility *)

Lemma delta_solve_levels_represents {P} strategy (prog : program P) facts st :
  program_wf prog facts -> stratified prog st -> forall n,
  represents (rel_of prog (delta_solve_levels strategy prog facts st n))
    (model_below prog facts st n).
Proof.
  intros Hprogram Hstrat n; induction n as [|k IH].
  - split; [apply delta_empty_db_wf |].
    intros p ts; unfold rel_of; cbn [delta_solve_levels]; rewrite Map.get_empty, FinSet.mem_empty.
    cbn [model_below]; split; [discriminate | contradiction].
  - set (lowerdb := delta_solve_levels strategy prog facts st k).
    change (represents (rel_of prog lowerdb) (model_below prog facts st k)) in IH.
    set (result := delta_solve_stratum strategy prog facts st k (rel_of prog lowerdb)).
    destruct (delta_stratum_exact strategy prog facts st k (rel_of prog lowerdb)
      Hprogram Hstrat IH) as [Hcorrect Hexact].
    change (delta_correct strategy prog facts st k (rel_of prog lowerdb) result) in Hcorrect.
    change (forall f, FinSet.mem (delta_ground_encoding prog) f (delta_accumulated result) = true
      <-> derives prog facts st k (model_below prog facts st k) f) in Hexact.
    change (represents (rel_of prog (delta_add_atoms prog
      (FinSet.elements (delta_accumulated result)) lowerdb)) (model_below prog facts st (S k))).
    split.
    + apply delta_add_atoms_wf; exact (proj1 IH).
    + intros p ts; rewrite delta_add_atoms_exact.
      rewrite FinSet.elements_spec by
        (exact (proj1 (delta_ready_valid _ _ _ _ _ _ _ (proj1 Hcorrect)))).
      rewrite (proj2 IH p ts), (Hexact (p, ts)); cbn [model_below]; reflexivity.
Qed.

(** A well-formed stratifiable program is evaluated directly to its perfect model. *)
Theorem solve_program_delta_exact {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) :
  program_wf prog facts -> (exists st, stratified prog st) ->
  exists db, solve_program_delta strategy prog facts = Some db /\
    represents (rel_of prog db) (least_model prog facts).
Proof.
  intros Hprogram Hstrat; destruct (stratify_complete prog Hstrat) as [st Hst].
  exists (delta_solve_levels strategy prog facts st (count st)).
  unfold solve_program_delta, least_model; rewrite Hst; split; [reflexivity |].
  apply delta_solve_levels_represents; [exact Hprogram | apply (stratify_sound prog st Hst)].
Qed.

(** Failure is exactly the absence of any stratification. *)
Theorem solve_program_delta_none {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) :
  (forall st, ~ stratified prog st) -> solve_program_delta strategy prog facts = None.
Proof.
  intro Hnone; unfold solve_program_delta; destruct (stratify prog) as [st |] eqn:Hst;
    [|reflexivity].
  exfalso; apply (Hnone st), (stratify_sound prog st Hst).
Qed.

(** Both direct evaluation strategies agree pointwise with the reference solver. *)
Theorem solve_program_delta_agrees {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (db delta : database P) :
  program_wf prog facts -> solve_program prog facts = Some db ->
  solve_program_delta strategy prog facts = Some delta ->
  forall p ts, db_holds prog db p ts = db_holds prog delta p ts.
Proof.
  intros Hprogram Hsolve Hdelta.
  assert (Hstrat : exists st, stratified prog st).
  { unfold solve_program in Hsolve; destruct (stratify prog) as [st |] eqn:Hst;
      [exists st; apply (stratify_sound prog st Hst) | discriminate]. }
  destruct (solve_program_exact prog facts Hprogram Hstrat) as [reference [Href Hrep]].
  rewrite Hsolve in Href; injection Href as Heq; subst reference.
  destruct (solve_program_delta_exact strategy prog facts Hprogram Hstrat) as
    [result [Hresult Hdelta_rep]].
  rewrite Hdelta in Hresult; injection Hresult as Heq; subst result.
  intros p ts; unfold db_holds; apply eq_true_iff_eq.
  rewrite (proj2 Hrep p ts), (proj2 Hdelta_rep p ts); reflexivity.
Qed.
