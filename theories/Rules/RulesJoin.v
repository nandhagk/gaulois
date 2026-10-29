(** * Selectable indexed rule joins

    Nested joins probe bound-position row indexes. Multiway joins intersect variable domains
    obtained from prepared bound-position indexes, then perform terminal relation lookups.
    For example, joining R(x,y), S(y,z), T(x,z) intersects the indexed domains for each variable.
    Builds on: RulesCompile, CollectionsTable and CollectionsFinSet. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTable.
From Gaulois.Rules Require Import RulesSyntax RulesCompile.
Import List.ListNotations.

(** The strategies choose literal-at-a-time or variable-at-a-time indexed enumeration. *)
Inductive join_strategy : Type :=
  | IndexedNested
  | IndexedMultiway.

(** * Shared relation preparation *)

Definition join_relation_keys {P} (E : encoding P) (ps : list (atom P)) : list P :=
  FinSet.elements (FinSet.of_list E (map pred ps)).

(** Each distinct input relation is enumerated once; all search indexes share this snapshot. *)
Definition prepare_join_relations {P} (E : encoding P) (ps : list (atom P))
    (env : P -> FinSet.t tuple) : Map.t P (list tuple) :=
  let keys := join_relation_keys E ps in
  fill_values E keys (map (fun p => FinSet.elements (env p)) keys).

Definition join_relation_rows {P} (E : encoding P) (idx : Map.t P (list tuple)) p : list tuple :=
  match Map.get E p idx with
  | Some rows => rows
  | None => []
  end.

(** Every atom reads the exact row snapshot for its predicate. *)
Lemma prepare_join_relations_get {P} (E : encoding P) ps env (a : atom P) :
  In a ps ->
  join_relation_rows E (prepare_join_relations E ps env) (pred a) =
    FinSet.elements (env (pred a)).
Proof.
  intro Ha; unfold join_relation_rows, prepare_join_relations.
  rewrite fill_values_member; [reflexivity |].
  unfold join_relation_keys; apply (FinSet.elements_spec E).
  - apply FinSet.wf_fold_add, Map.wf_empty.
  - apply FinSet.of_list_spec, in_map; exact Ha.
Qed.

(** * Prepared nested joins *)

Record nested_search : Type := NestedSearch {
  nested_bound : FinSet.t nat;
  nested_terms : list term;
  nested_index : tuple_index
}.

Fixpoint prepare_nested {P} (ps : list (atom P)) (bound : FinSet.t nat)
    (rows : P -> list tuple) : list nested_search :=
  match ps with
  | [] => []
  | a :: rest =>
    NestedSearch bound (args a) (build_index bound (args a) (rows (pred a))) ::
      prepare_nested rest (bound_add bound a) rows
  end.

Definition nested_probe (search : nested_search) (bs : list binding) : list binding :=
  flat_map (fun b => flat_map (fun cs => option_binding (bind_terms (nested_terms search) cs b))
    (index_get (nested_index search) (bound_key (nested_bound search) b (nested_terms search)))) bs.

Fixpoint run_nested (searches : list nested_search) (bs : list binding) : list binding :=
  match searches with
  | [] => bs
  | search :: rest => run_nested rest (nested_probe search bs)
  end.

(** Preparing before enumeration preserves the reference nested join exactly, including order. *)
Lemma run_nested_agrees {P} (ps : list (atom P)) bound rows env bs :
  (forall a, In a ps -> rows (pred a) = FinSet.elements (env (pred a))) ->
  run_nested (prepare_nested ps bound rows) bs = join_positive ps bound env bs.
Proof.
  revert bound bs; induction ps as [|a ps IH]; intros bound bs Hrows.
  - reflexivity.
  - cbn [prepare_nested run_nested join_positive].
    assert (Hrest : forall x, In x ps -> rows (pred x) = FinSet.elements (env (pred x))).
    { intros x Hx; apply Hrows; now right. }
    rewrite (IH _ _ Hrest).
    assert (Hstep : nested_probe
      (NestedSearch bound (args a) (build_index bound (args a) (rows (pred a)))) bs =
      join_step bound a env bs).
    { unfold nested_probe, join_step; cbn; rewrite (Hrows a (or_introl eq_refl)); reflexivity. }
    rewrite Hstep; reflexivity.
Qed.

(** * Variable-domain indexes *)

Definition variable_index := Table.t (FinSet.t positive).

Definition variable_index_get (idx : variable_index) (key : tuple) : FinSet.t positive :=
  match Table.get key idx with
  | Some values => values
  | None => FinSet.empty
  end.

(** A row contributes only when its arity, constants and repeated variables all match. *)
Definition variable_index_add bound ts v cs (idx : variable_index) : variable_index :=
  match tuple_key bound ts cs, bind_terms ts cs Map.empty with
  | Some key, Some b =>
    Table.set key (FinSet.add positive_encoding (binding_value b v)
      (variable_index_get idx key)) idx
  | _, _ => idx
  end.

Definition build_variable_index bound ts v (rows : list tuple) : variable_index :=
  fold_right (variable_index_add bound ts v) Table.empty rows.

(** Adding a matching row inserts its variable value at exactly its bound-position key. *)
Lemma variable_index_add_spec bound ts v cs idx key c :
  FinSet.mem positive_encoding c (variable_index_get (variable_index_add bound ts v cs idx) key)
    = true <->
  FinSet.mem positive_encoding c (variable_index_get idx key) = true \/
  exists b, tuple_key bound ts cs = Some key /\ bind_terms ts cs Map.empty = Some b /\
    c = binding_value b v.
Proof.
  unfold variable_index_add.
  destruct (tuple_key bound ts cs) as [key' |] eqn:Hkey;
    destruct (bind_terms ts cs Map.empty) as [b |] eqn:Hbind.
  - destruct (list_eq_dec Pos.eq_dec key key') as [Heq | Hne].
    + subst key'; unfold variable_index_get at 1; rewrite Table.get_set_same.
      rewrite FinSet.mem_add; split.
      * intros [Heq | Hin]; [right; exists b; auto | now left].
      * intros [Hin | [b' [_ [Hsome Heq]]]]; [now right |].
        injection Hsome as Hb; subst b'; now left.
    + unfold variable_index_get at 1; rewrite Table.get_set_other by exact Hne.
      fold (variable_index_get idx key); split; [auto |].
      intros [Hin | [b' [Hbad _]]]; [exact Hin | injection Hbad as Heq; congruence].
  - split; [auto |].
    intros [Hin | [b' [_ [Hbad _]]]]; [exact Hin | discriminate].
  - split; [auto |].
    intros [Hin | [b' [Hbad _]]]; [exact Hin | discriminate].
  - split; [auto |].
    intros [Hin | [b' [Hbad _]]]; [exact Hin | discriminate].
Qed.

(** A domain probe is exactly the projection of matching rows at the requested bound key. *)
Lemma build_variable_index_spec bound ts v rows key c :
  FinSet.mem positive_encoding c
    (variable_index_get (build_variable_index bound ts v rows) key) = true <->
  exists cs b, In cs rows /\ tuple_key bound ts cs = Some key /\
    bind_terms ts cs Map.empty = Some b /\ c = binding_value b v.
Proof.
  induction rows as [|cs rows IH]; cbn [build_variable_index fold_right].
  - unfold variable_index_get; rewrite Table.get_empty, FinSet.mem_empty.
    split; [discriminate | intros [row [b [Hbad _]]]; contradiction].
  - rewrite variable_index_add_spec, IH; split.
    + intros [[row [b [Hin Hrest]]] | [b Hrest]].
      * exists row, b; split; [now right | exact Hrest].
      * exists cs, b; split; [now left | exact Hrest].
    + intros [row [b [[Heq | Hin] Hrest]]].
      * subst row; right; exists b; exact Hrest.
      * left; exists row, b; auto.
Qed.

Lemma variable_index_add_wf bound ts v cs idx :
  (forall key, FinSet.wf positive_encoding (variable_index_get idx key)) ->
  forall key, FinSet.wf positive_encoding
    (variable_index_get (variable_index_add bound ts v cs idx) key).
Proof.
  intros Hwf key; unfold variable_index_add.
  destruct (tuple_key bound ts cs) as [key' |];
    destruct (bind_terms ts cs Map.empty) as [b |]; try apply Hwf.
  destruct (list_eq_dec Pos.eq_dec key key') as [Heq | Hne].
  - subst key'; unfold variable_index_get at 1; rewrite Table.get_set_same.
    apply Map.wf_set, Hwf.
  - unfold variable_index_get at 1; rewrite Table.get_set_other by exact Hne; apply Hwf.
Qed.

Lemma build_variable_index_wf bound ts v rows key :
  FinSet.wf positive_encoding
    (variable_index_get (build_variable_index bound ts v rows) key).
Proof.
  revert key; induction rows as [|cs rows IH]; intro key; cbn [build_variable_index fold_right].
  - unfold variable_index_get; rewrite Table.get_empty; apply Map.wf_empty.
  - apply variable_index_add_wf, IH.
Qed.

Lemma binding_value_on_variable ts cs b sigma v :
  bind_terms ts cs Map.empty = Some b -> binding_agrees b sigma ->
  In (TVar v) ts -> binding_value b v = sigma v.
Proof.
  intros Hbind Hagree Hv.
  destruct (bind_terms_sound ts cs Map.empty b Hbind) as [_ [_ Hvars]].
  destruct (Hvars v Hv) as [c Hget]; unfold binding_value; rewrite Hget.
  symmetry; apply Hagree; exact Hget.
Qed.

(** Every satisfying valuation is present in the indexed variable domain. *)
Lemma build_variable_index_complete bound ts v rows b sigma :
  binding_covers bound b -> binding_agrees b sigma -> In (TVar v) ts ->
  In (map (inst sigma) ts) rows ->
  FinSet.mem positive_encoding (sigma v)
    (variable_index_get (build_variable_index bound ts v rows) (bound_key bound b ts)) = true.
Proof.
  intros Hcover Hagree Hv Hrow; apply build_variable_index_spec.
  destruct (bind_terms_complete ts Map.empty sigma (empty_binding_agrees sigma)) as
    [row_binding [Hbind Hrow_agrees]].
  exists (map (inst sigma) ts), row_binding; split; [exact Hrow | split].
  - rewrite tuple_key_instance, (bound_key_agrees bound b ts sigma Hcover Hagree).
    reflexivity.
  - split; [exact Hbind | symmetry; eapply binding_value_on_variable; eassumption].
Qed.

(** Domain lookup agrees with valuations satisfying all constants, repetitions and arities. *)
Lemma build_variable_index_matching bound ts v rows key c :
  In (TVar v) ts ->
  (FinSet.mem positive_encoding c
    (variable_index_get (build_variable_index bound ts v rows) key) = true <->
  exists sigma, In (map (inst sigma) ts) rows /\
    key = map (inst sigma) (filter (bound_term bound) ts) /\ c = sigma v).
Proof.
  intro Hv; rewrite build_variable_index_spec; split.
  - intros [cs [b [Hrow [Hkey [Hbind Hvalue]]]]].
    destruct (bind_terms_sound ts cs Map.empty b Hbind) as [_ [Hterms _]].
    pose proof (Hterms (binding_value b) (binding_value_agrees b)) as Hcs.
    exists (binding_value b); split; [now rewrite <- Hcs | split; [|exact Hvalue]].
    rewrite Hcs, tuple_key_instance in Hkey; injection Hkey as Heq; symmetry; exact Heq.
  - intros [sigma [Hrow [Hkey Hvalue]]].
    destruct (bind_terms_complete ts Map.empty sigma (empty_binding_agrees sigma)) as
      [b [Hbind Hagree]].
    exists (map (inst sigma) ts), b; split; [exact Hrow | split].
    + rewrite tuple_key_instance, Hkey; reflexivity.
    + split; [exact Hbind | rewrite Hvalue; symmetry].
      eapply binding_value_on_variable; eassumption.
Qed.

(** * Multiway search plans *)

Record variable_search : Type := VariableSearch {
  variable_terms : list term;
  variable_table : variable_index
}.

Definition atoms_with_variable {P} v (ps : list (atom P)) : list (atom P) :=
  filter (fun a => FinSet.mem nat_encoding v (FinSet.of_list nat_encoding (atom_vars a))) ps.

Lemma atoms_with_variable_spec {P} v (ps : list (atom P)) a :
  In a (atoms_with_variable v ps) <-> In a ps /\ In (TVar v) (args a).
Proof.
  unfold atoms_with_variable; rewrite filter_In, FinSet.of_list_spec, atom_vars_spec; reflexivity.
Qed.

Definition prepare_variable {P} bound v (ps : list (atom P)) (rows : P -> list tuple) :=
  map (fun a => VariableSearch (args a)
    (build_variable_index bound (args a) v (rows (pred a)))) (atoms_with_variable v ps).

Definition variable_probe bound b (search : variable_search) : FinSet.t positive :=
  variable_index_get (variable_table search) (bound_key bound b (variable_terms search)).

Fixpoint intersect_variable_domains bound b (first : FinSet.t positive)
    (searches : list variable_search) : FinSet.t positive :=
  match searches with
  | [] => first
  | search :: rest =>
    intersect_variable_domains bound b
      (FinSet.inter positive_encoding first (variable_probe bound b search)) rest
  end.

Definition variable_candidates bound b (searches : list variable_search) : FinSet.t positive :=
  match searches with
  | [] => FinSet.empty
  | search :: rest => intersect_variable_domains bound b (variable_probe bound b search) rest
  end.

(** Intersection retains exactly the values present in every requested domain. *)
Lemma intersect_variable_domains_spec bound b first searches c :
  FinSet.mem positive_encoding c (intersect_variable_domains bound b first searches) = true <->
  FinSet.mem positive_encoding c first = true /\
  forall search, In search searches ->
    FinSet.mem positive_encoding c (variable_probe bound b search) = true.
Proof.
  revert first; induction searches as [|search rest IH]; intro first; cbn.
  - split; [intro Hin; split; [exact Hin | intros x Hbad; contradiction] | tauto].
  - rewrite IH, FinSet.mem_inter; split.
    + intros [[Hfirst Hsearch] Hrest]; split; [exact Hfirst |].
      intros x [Heq | Hx]; [subst x; exact Hsearch | apply Hrest; exact Hx].
    + intros [Hfirst Hall]; split.
      * split; [exact Hfirst | apply Hall; now left].
      * intros x Hx; apply Hall; now right.
Qed.

Lemma variable_candidates_spec bound b searches c :
  FinSet.mem positive_encoding c (variable_candidates bound b searches) = true <->
  searches <> [] /\ forall search, In search searches ->
    FinSet.mem positive_encoding c (variable_probe bound b search) = true.
Proof.
  destruct searches as [|search rest]; cbn [variable_candidates].
  - rewrite FinSet.mem_empty; split; [discriminate | tauto].
  - rewrite intersect_variable_domains_spec; split.
    + intros [Hsearch Hrest]; split; [discriminate |].
      intros x [Heq | Hx]; [subst x; exact Hsearch | apply Hrest; exact Hx].
    + intros [_ Hall]; split.
      * apply Hall; now left.
      * intros x Hx; apply Hall; now right.
Qed.

Lemma intersect_variable_domains_wf bound b first searches :
  FinSet.wf positive_encoding first ->
  (forall search, In search searches ->
    FinSet.wf positive_encoding (variable_probe bound b search)) ->
  FinSet.wf positive_encoding (intersect_variable_domains bound b first searches).
Proof.
  revert first; induction searches as [|search rest IH]; intros first Hfirst Hsearch; cbn.
  - exact Hfirst.
  - apply IH.
    + apply FinSet.wf_inter; [exact Hfirst | apply Hsearch; now left].
    + intros x Hx; apply Hsearch; now right.
Qed.

Lemma prepared_candidates_wf {P} bound b v (ps : list (atom P)) rows :
  FinSet.wf positive_encoding (variable_candidates bound b (prepare_variable bound v ps rows)).
Proof.
  assert (Hsearch : forall search, In search (prepare_variable bound v ps rows) ->
    FinSet.wf positive_encoding (variable_probe bound b search)).
  { intros search Hin; apply in_map_iff in Hin; destruct Hin as [a [Heq _]]; subst search.
    apply build_variable_index_wf. }
  destruct (prepare_variable bound v ps rows) as [|search rest] eqn:Hprepared;
    cbn [variable_candidates].
  - apply Map.wf_empty.
  - apply intersect_variable_domains_wf.
    + apply Hsearch; now left.
    + intros x Hx; apply Hsearch; now right.
Qed.

Definition join_variables {P} (ps : list (atom P)) : list nat :=
  FinSet.elements (FinSet.of_list nat_encoding (flat_map atom_vars ps)).

Lemma join_variables_spec {P} (ps : list (atom P)) v :
  In v (join_variables ps) <-> exists a, In a ps /\ In (TVar v) (args a).
Proof.
  unfold join_variables; rewrite FinSet.elements_spec.
  - rewrite FinSet.of_list_spec, in_flat_map; split.
    + intros [a [Ha Hv]]; exists a; split; [exact Ha | apply atom_vars_spec; exact Hv].
    + intros [a [Ha Hv]]; exists a; split; [exact Ha | apply atom_vars_spec; exact Hv].
  - apply FinSet.wf_fold_add, Map.wf_empty.
Qed.

Record multiway_search : Type := MultiwaySearch {
  multiway_variable : nat;
  multiway_bound : FinSet.t nat;
  multiway_domains : list variable_search
}.

Fixpoint prepare_multiway {P} (vs : list nat) bound (ps : list (atom P)) rows
    : list multiway_search :=
  match vs with
  | [] => []
  | v :: rest =>
    MultiwaySearch v bound (prepare_variable bound v ps rows) ::
      prepare_multiway rest (FinSet.add nat_encoding v bound) ps rows
  end.

Definition multiway_step (search : multiway_search) (bs : list binding) : list binding :=
  flat_map (fun b => flat_map (fun c => option_binding
    (bind_term b (TVar (multiway_variable search)) c))
    (FinSet.elements (variable_candidates (multiway_bound search) b (multiway_domains search)))) bs.

Fixpoint run_multiway (searches : list multiway_search) (bs : list binding) : list binding :=
  match searches with
  | [] => bs
  | search :: rest => run_multiway rest (multiway_step search bs)
  end.

Lemma binding_covers_variable bound b b' v c :
  binding_covers bound b -> bind_term b (TVar v) c = Some b' ->
  binding_covers (FinSet.add nat_encoding v bound) b'.
Proof.
  intros Hcover Hbind w Hin; apply FinSet.mem_add in Hin.
  destruct (bind_term_sound b (TVar v) c b' Hbind) as [Hext [_ Hvar]].
  destruct Hin as [Heq | Hin].
  - subst w; apply Hvar; reflexivity.
  - destruct (Hcover w Hin) as [d Hget]; exists d; apply Hext; exact Hget.
Qed.

Lemma prepared_candidates_complete {P} bound b v (ps : list (atom P)) rows sigma :
  (exists a, In a ps /\ In (TVar v) (args a)) ->
  binding_covers bound b -> binding_agrees b sigma ->
  (forall a, In a ps -> In (map (inst sigma) (args a)) (rows (pred a))) ->
  FinSet.mem positive_encoding (sigma v)
    (variable_candidates bound b (prepare_variable bound v ps rows)) = true.
Proof.
  intros [a [Ha Hv]] Hcover Hagree Hrows; apply variable_candidates_spec; split.
  - intro Hempty; assert (Hin : In a (atoms_with_variable v ps)).
    { apply atoms_with_variable_spec; auto. }
    pose proof (in_map (fun x => VariableSearch (args x)
      (build_variable_index bound (args x) v (rows (pred x)))) _ _ Hin) as Hmapped.
    unfold prepare_variable in Hempty.
    rewrite Hempty in Hmapped; contradiction.
  - intros search Hin; apply in_map_iff in Hin; destruct Hin as [x [Heq Hx]]; subst search.
    apply atoms_with_variable_spec in Hx; destruct Hx as [Hx Hvar].
    apply build_variable_index_complete.
    + exact Hcover.
    + exact Hagree.
    + exact Hvar.
    + apply Hrows; exact Hx.
Qed.

(** A satisfying valuation follows one branch through every indexed variable intersection. *)
Lemma run_multiway_complete {P} vs bound (ps : list (atom P)) rows bs b sigma :
  (forall v, In v vs -> exists a, In a ps /\ In (TVar v) (args a)) ->
  In b bs -> binding_covers bound b -> binding_agrees b sigma ->
  (forall a, In a ps -> In (map (inst sigma) (args a)) (rows (pred a))) ->
  exists b', In b' (run_multiway (prepare_multiway vs bound ps rows) bs) /\
    binding_agrees b' sigma /\ binding_extends b b' /\
    (forall v, In v vs -> exists c, Map.get nat_encoding v b' = Some c).
Proof.
  revert bound bs b; induction vs as [|v vs IH]; intros bound bs b Hvars Hb Hcover Hagree Hrows.
  - exists b; split; [exact Hb | split; [exact Hagree | split]].
    + intros w c Hget; exact Hget.
    + intros w Hbad; contradiction.
  - destruct (bind_term_complete b (TVar v) sigma Hagree) as [b1 [Hbind Hagree1]].
    assert (Hb1 : In b1 (multiway_step
      (MultiwaySearch v bound (prepare_variable bound v ps rows)) bs)).
    { unfold multiway_step; apply in_flat_map; exists b; split; [exact Hb |].
      apply in_flat_map; exists (sigma v); split.
      - apply (FinSet.elements_spec positive_encoding).
        + apply prepared_candidates_wf.
        + apply prepared_candidates_complete; auto; apply Hvars; now left.
      - apply option_binding_spec; exact Hbind. }
    destruct (bind_term_sound b (TVar v) (sigma v) b1 Hbind) as [Hext [_ Hvar]].
    destruct (IH (FinSet.add nat_encoding v bound)
      (multiway_step (MultiwaySearch v bound (prepare_variable bound v ps rows)) bs) b1) as
      [b' [Hb' [Hagree' [Hext' Hbound]]]].
    + intros w Hw; apply Hvars; now right.
    + exact Hb1.
    + eapply binding_covers_variable; eassumption.
    + exact Hagree1.
    + exact Hrows.
    + exists b'; split; [exact Hb' | split; [exact Hagree' | split]].
      * eapply binding_extends_trans; eassumption.
      * intros w [Heq | Hw].
        -- subst w; destruct (Hvar v eq_refl) as [c Hget]; exists c; apply Hext'; exact Hget.
        -- apply Hbound; exact Hw.
Qed.

(** * Terminal lookups and firing *)

(** Terminal trie lookups also handle ground literals and confirm full tuple compatibility. *)
Definition positive_ok {P} (ps : list (atom P)) (env : P -> FinSet.t tuple) b : bool :=
  forallb (fun a => FinSet.mem tuple_encoding
    (map (inst (binding_value b)) (args a)) (env (pred a))) ps.

Lemma positive_ok_spec {P} (ps : list (atom P)) env b :
  positive_ok ps env b = true <-> forall a, In a ps ->
    FinSet.mem tuple_encoding (map (inst (binding_value b)) (args a)) (env (pred a)) = true.
Proof.
  unfold positive_ok; apply forallb_forall.
Qed.

Definition selected_bindings {P} strategy (prog : program P) (r : rule P) env : list binding :=
  let ps := positive_atoms (body r) in
  let relations := prepare_join_relations (penc prog) ps env in
  let rows := join_relation_rows (penc prog) relations in
  match strategy with
  | IndexedNested => run_nested (prepare_nested ps FinSet.empty rows) [Map.empty]
  | IndexedMultiway => filter (positive_ok ps env)
      (run_multiway (prepare_multiway (join_variables ps) FinSet.empty ps rows) [Map.empty])
  end.

(** Both strategies enumerate exactly the satisfying positive valuations, up to unbound values. *)
Lemma selected_bindings_complete {P} strategy (prog : program P) r env sigma :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  (forall a, In (LPos a) (body r) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) ->
  exists b, In b (selected_bindings strategy prog r env) /\ binding_agrees b sigma /\
    (forall a, In (LPos a) (body r) -> forall v, In (TVar v) (args a) ->
      exists c, Map.get nat_encoding v b = Some c).
Proof.
  intros Hwf Hpos; destruct strategy; unfold selected_bindings.
  - rewrite run_nested_agrees with (env := env).
    + destruct (join_positive_complete (positive_atoms (body r)) FinSet.empty env
        [Map.empty] Map.empty sigma Hwf (or_introl eq_refl) empty_binding_covers
        (empty_binding_agrees sigma)) as [b [Hb [Hagree [_ Hbound]]]].
      * intros a Ha; apply Hpos, positive_atoms_spec, Ha.
      * exists b; split; [exact Hb | split; [exact Hagree |]].
        intros a Ha; apply Hbound, positive_atoms_spec, Ha.
    + intros a Ha; apply prepare_join_relations_get; exact Ha.
  - destruct (run_multiway_complete (join_variables (positive_atoms (body r))) FinSet.empty
      (positive_atoms (body r))
      (join_relation_rows (penc prog)
        (prepare_join_relations (penc prog) (positive_atoms (body r)) env))
      [Map.empty] Map.empty sigma) as [b [Hb [Hagree [_ Hbound]]]].
    + intros v Hv; apply join_variables_spec; exact Hv.
    + now left.
    + apply empty_binding_covers.
    + apply empty_binding_agrees.
    + intros a Ha; rewrite prepare_join_relations_get by exact Ha.
      apply (FinSet.elements_spec tuple_encoding); [apply Hwf |].
      apply Hpos, positive_atoms_spec, Ha.
    + assert (Hcovered : forall a, In (LPos a) (body r) -> forall v,
        In (TVar v) (args a) -> exists c, Map.get nat_encoding v b = Some c).
      { intros a Ha v Hv; apply Hbound, join_variables_spec; exists a; split;
          [apply positive_atoms_spec; exact Ha | exact Hv]. }
      exists b; split; [apply filter_In; split; [exact Hb |] | auto].
      apply positive_ok_spec; intros a Ha.
      rewrite (inst_agrees_on_bound (args a) b sigma Hagree).
      * apply Hpos, positive_atoms_spec, Ha.
      * apply Hcovered, positive_atoms_spec, Ha.
Qed.

Lemma selected_bindings_sound {P} strategy (prog : program P) r env b :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  In b (selected_bindings strategy prog r env) ->
  forall a, In (LPos a) (body r) ->
    FinSet.mem tuple_encoding (map (inst (binding_value b)) (args a)) (env (pred a)) = true.
Proof.
  intros Hwf Hb; destruct strategy; unfold selected_bindings in Hb.
  - rewrite run_nested_agrees with (env := env) in Hb.
    + destruct (join_positive_sound (positive_atoms (body r)) FinSet.empty env [Map.empty] b
        Hwf) as [b0 [_ [_ [Hvalues _]]]].
      * intros b' [Heq | Hbad]; [subst b'; apply empty_binding_covers | contradiction].
      * exact Hb.
      * intros a Ha; apply Hvalues.
        -- apply binding_value_agrees.
        -- apply positive_atoms_spec; exact Ha.
    + intros a Ha; apply prepare_join_relations_get; exact Ha.
  - apply filter_In in Hb; destruct Hb as [_ Hpos].
    intros a Ha; apply (proj1 (positive_ok_spec _ _ _) Hpos), positive_atoms_spec, Ha.
Qed.

(** Firing prepares the selected indexes, tests completed lower relations and normalizes heads. *)
Definition fire_rule_join {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
    FinSet.t tuple :=
  FinSet.of_list tuple_encoding (filter (in_universe prog facts (pred (head r)))
    (map (fun b => map (inst (binding_value b)) (args (head r)))
      (filter (negative_ok r env) (selected_bindings strategy prog r env)))).

Lemma fire_rule_join_members {P} strategy (prog : program P) facts r env ts :
  FinSet.mem tuple_encoding ts (fire_rule_join strategy prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts = true /\
  exists b, In b (selected_bindings strategy prog r env) /\ negative_ok r env b = true /\
    ts = map (inst (binding_value b)) (args (head r)).
Proof.
  unfold fire_rule_join; rewrite FinSet.of_list_spec, filter_In, in_map_iff; split.
  - intros [[b [Heq Hin]] Huniv]; apply filter_In in Hin; split; [exact Huniv |].
    exists b; intuition congruence.
  - intros [Huniv [b [Hin [Hneg Heq]]]]; split; [|exact Huniv].
    exists b; split; [symmetry; exact Heq | apply filter_In; auto].
Qed.

(** Selected firing has precisely the same satisfying valuations as reference firing. *)
Theorem fire_rule_join_exact {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
  program_wf prog facts -> In r (rules prog) -> env_wf prog env ->
  forall ts, FinSet.mem tuple_encoding ts (fire_rule_join strategy prog facts r env) = true <->
    FinSet.mem tuple_encoding ts (fire_rule prog facts r env) = true.
Proof.
  intros Hprogram Hr Henv ts; rewrite fire_rule_join_members.
  rewrite (fire_rule_exact prog facts env r Hprogram Hr Henv ts).
  assert (Hwf : forall p, FinSet.wf tuple_encoding (env p)) by (intro p; exact (proj1 (Henv p))).
  split.
  - intros [Huniv [b [Hb [Hneg Heq]]]]; split; [exact Huniv |].
    exists (binding_value b); split; [exact Heq | split].
    + apply selected_bindings_sound with (strategy := strategy) (prog := prog) (r := r); assumption.
    + apply negative_ok_spec; exact Hneg.
  - intros [Huniv [sigma [Heq [Hpos Hneg]]]].
    destruct (selected_bindings_complete strategy prog r env sigma Hwf Hpos) as
      [b [Hb [Hagree Hbound]]].
    destruct Hprogram as [Hrules _].
    destruct (safe_binding_agrees r b sigma (proj1 (Hrules r Hr)) Hagree Hbound) as
      [Hhead Hnegative].
    split; [exact Huniv | exists b; split; [exact Hb | split]].
    + apply negative_ok_spec; intros a Ha; rewrite Hnegative by exact Ha; apply Hneg; exact Ha.
    + rewrite Hhead; exact Heq.
Qed.

(** Both strategies return a well-formed canonical finite set. *)
Theorem fire_rule_join_wf {P} (strategy : join_strategy) (prog : program P)
    (facts : list (ground_atom P)) (r : rule P) (env : P -> FinSet.t tuple) :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  FinSet.wf tuple_encoding (fire_rule_join strategy prog facts r env).
Proof.
  intros _; apply FinSet.wf_fold_add, Map.wf_empty.
Qed.
