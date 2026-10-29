(** * Exact solving of stratified rule programs

    The joining engine computes each inductively defined stratum over completed lower relations.
    For example, facts at a recursive predicate seed its least solution in the same stratum.
    Builds on: RulesModel, RulesCompile and FixpointTotal. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone OrderPowerset.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointWorklist
  FixpointTotal FixpointSchedule.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesModel.
Import List.ListNotations.

(** Databases store a finite tuple set at each explicitly represented predicate. *)
Definition database (P : Type) : Type := Map.t P (FinSet.t tuple).

(** Absent database predicates denote empty relations. *)
Definition rel_of {P} (prog : program P) (db : database P) (p : P) : FinSet.t tuple :=
  match Map.get (penc prog) p db with
  | Some s => s
  | None => FinSet.empty
  end.

(** Database membership is the finite-set test at the requested predicate. *)
Definition db_holds {P} (prog : program P) (db : database P) (p : P) (ts : tuple) : bool :=
  FinSet.mem tuple_encoding ts (rel_of prog db p).

(** Representation requires well-formed sets and pointwise agreement with the semantic model. *)
Definition represents {P} (db : P -> FinSet.t tuple) (M : ground_atom P -> Prop) : Prop :=
  (forall p, FinSet.wf tuple_encoding (db p)) /\
  forall p ts, FinSet.mem tuple_encoding ts (db p) = true <-> M (p, ts).

Section Stratum.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : stratification P).

Lemma numbered_rules_complete n r : In r (rules prog) ->
  exists i, In (i, r) (numbered_rules n (rules prog)).
Proof.
  generalize (rules prog) as rs; intros rs; revert n.
  induction rs as [|r' rs IH]; intros n Hr; [contradiction |].
  destruct Hr as [Heq | Hr].
  - subst r'; exists n; now left.
  - destruct (IH (S n) Hr) as [i Hi]; exists i; now right.
Qed.

Lemma rule_constraint_member k r : In r (rules prog) -> level st (pred (head r)) = k ->
  exists i, In (FromRule i (pred (head r))) (stratum_constraints prog facts st k) /\
    Map.get nat_encoding i (index_rules_from 0 (rules prog)) = Some r.
Proof.
  intros Hr Hlevel; destruct (numbered_rules_complete 0 r Hr) as [i Hi].
  exists i; split; [|apply index_rules_member; exact Hi].
  unfold stratum_constraints; apply in_app_iff; left; apply in_flat_map.
  exists (i, r); split; [exact Hi | cbn [fst snd]; rewrite Hlevel, Nat.eqb_refl; now left].
Qed.

Lemma rule_constraint_view k i h :
  In (FromRule i h) (stratum_constraints prog facts st k) ->
  exists r, In r (rules prog) /\ h = pred (head r) /\ level st h = k /\
    Map.get nat_encoding i (index_rules_from 0 (rules prog)) = Some r.
Proof.
  unfold stratum_constraints; rewrite in_app_iff; intros [Hin | Hbad].
  - apply in_flat_map in Hin; destruct Hin as [[j r] [Hindex Hin]]; cbn [fst snd] in Hin.
    destruct (Nat.eqb (level st (pred (head r))) k) eqn:Hlevel; [|contradiction].
    destruct Hin as [Heq | Hbad]; [|contradiction]; injection Heq as Hi Hh; subst j h.
    exists r; split; [exact (proj2 (numbered_rules_member 0 _ i r Hindex)) |].
    split; [reflexivity | split; [apply Nat.eqb_eq; exact Hlevel |]].
    apply index_rules_member; exact Hindex.
  - apply in_map_iff in Hbad; destruct Hbad as [p [Hbad _]]; discriminate.
Qed.

Lemma fact_constraint_member k p ts : In (p, ts) facts -> level st p = k ->
  In (FromFact p) (stratum_constraints prog facts st k).
Proof.
  intros Hfact Hlevel; unfold stratum_constraints; apply in_app_iff; right.
  apply in_map, filter_In; split; [|rewrite Hlevel; apply Nat.eqb_refl].
  apply (FinSet.elements_spec (penc prog)); [apply FinSet.wf_fold_add, Map.wf_empty |].
  apply FinSet.of_list_spec, in_map_iff; exists (p, ts); split; [reflexivity | exact Hfact].
Qed.

Lemma fact_constraint_level k p : In (FromFact p) (stratum_constraints prog facts st k) ->
  level st p = k.
Proof.
  unfold stratum_constraints; rewrite in_app_iff; intros [Hbad | Hin].
  - apply in_flat_map in Hbad; destruct Hbad as [[i r] [_ Hbad]]; cbn [fst snd] in Hbad.
    destruct (Nat.eqb (level st (pred (head r))) k); [|contradiction].
    destruct Hbad as [Hbad | Hbad]; [discriminate | contradiction].
  - apply in_map_iff in Hin; destruct Hin as [q [Heq Hin]]; injection Heq as Heq; subst q.
    apply filter_In in Hin; apply Nat.eqb_eq; exact (proj2 Hin).
Qed.

Lemma facts_by_pred_exact p ts :
  FinSet.mem tuple_encoding ts (relation_get (penc prog) (facts_by_pred prog facts) p) = true
    <-> In (p, ts) facts.
Proof.
  unfold facts_by_pred; induction facts as [|[q us] fs IH]; cbn [fold_right fst snd].
  - unfold relation_get; rewrite Map.get_empty, FinSet.mem_empty; cbn; split;
      [discriminate | contradiction].
  - unfold relation_get at 1; destruct (encoded_eq_dec (penc prog) p q) as [Heq | Hne].
    + subst q; rewrite Map.get_set_same; rewrite FinSet.mem_add; rewrite IH.
      cbn; split.
      * intros [Heq | Hin]; [subst us; now left | now right].
      * intros [Heq | Hin]; [injection Heq as Heq; now left | now right].
    + rewrite Map.get_set_other by exact Hne; fold (relation_get (penc prog)
        (fold_right (fun f idx => Map.set (penc prog) (fst f)
          (FinSet.add tuple_encoding (snd f) (relation_get (penc prog) idx (fst f))) idx)
          Map.empty fs) p).
      rewrite IH; cbn; split; [now right |].
      intros [Heq | Hin]; [injection Heq as Heq; congruence | exact Hin].
Qed.

Lemma facts_by_pred_wf p :
  FinSet.wf tuple_encoding (relation_get (penc prog) (facts_by_pred prog facts) p).
Proof.
  unfold facts_by_pred; revert p; induction facts as [|[q us] fs IH]; intro p;
    cbn [fold_right fst snd]; unfold relation_get at 1.
  - rewrite Map.get_empty; apply Map.wf_empty.
  - destruct (encoded_eq_dec (penc prog) p q) as [Heq | Hne].
    + subst q; rewrite Map.get_set_same; apply Map.wf_set; apply IH.
    + rewrite Map.get_set_other by exact Hne; apply IH.
Qed.

Lemma level_dependencies_member k r a : In (LPos a) (body r) -> level st (pred a) = k ->
  In (pred a) (level_dependencies prog st k r).
Proof.
  intros Ha Hlevel; unfold level_dependencies.
  apply (FinSet.elements_spec (penc prog)); [apply FinSet.wf_fold_add, Map.wf_empty |].
  apply FinSet.of_list_spec, in_map_iff; exists a; split; [reflexivity |].
  apply filter_In; split; [apply positive_atoms_spec; exact Ha |].
  rewrite Hlevel; apply Nat.eqb_refl.
Qed.

(** A rule sees queried current-stratum values and immutable lower relations. *)
Definition rule_env k lower (s : P -> relation prog facts) (r : rule P) :=
  stratum_env prog facts st lower k
    (fill_values (penc prog) (level_dependencies prog st k r)
      (map s (level_dependencies prog st k r))).

Lemma rule_env_same k lower s r a : In (LPos a) (body r) -> level st (pred a) = k ->
  rule_env k lower s r (pred a) = proj1_sig (s (pred a)).
Proof.
  intros Ha Hlevel; unfold rule_env, stratum_env; rewrite Hlevel, Nat.eqb_refl.
  rewrite fill_values_member; [reflexivity | apply level_dependencies_member; assumption].
Qed.

Lemma rule_env_lower k lower s r p : level st p <> k -> rule_env k lower s r p = lower p.
Proof.
  apply stratum_env_constant.
Qed.

Lemma rule_env_wf k lower s r : (forall p, FinSet.wf tuple_encoding (lower p)) ->
  forall p, FinSet.wf tuple_encoding (rule_env k lower s r p).
Proof.
  apply stratum_env_wf.
Qed.

Lemma rule_rhs_eval k lower s i h r :
  Map.get nat_encoding i (index_rules_from 0 (rules prog)) = Some r ->
  Query.eval (System.rhs (stratum_system prog facts st lower k) (FromRule i h)) s =
    restrict prog facts h (fire_rule prog facts r (rule_env k lower s r)).
Proof.
  intro Hindex; cbn [stratum_system System.rhs stratum_rhs]; rewrite Hindex.
  rewrite (proj1 (proj2 (ask_all_spec _ _ _))); reflexivity.
Qed.

Lemma stratum_sides_nil k lower s c :
  Query.sides (System.rhs (stratum_system prog facts st lower k) c) s = [].
Proof.
  destruct c as [i h | p]; cbn [stratum_system System.rhs stratum_rhs]; [|reflexivity].
  destruct (Map.get nat_encoding i (index_rules_from 0 (rules prog))); [|reflexivity].
  rewrite (proj2 (proj2 (ask_all_spec _ _ _))); reflexivity.
Qed.

Lemma represented_lower_wf k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) -> env_wf prog lower.
Proof.
  intros Hwf Hstrat [Hsets Hexact] p; split; [apply Hsets |].
  intros ts Hmem; apply (proj1 (Hexact p ts)) in Hmem.
  apply (model_constants prog facts st Hwf Hstrat) in Hmem.
  apply in_universe_spec in Hmem; exact (proj1 (proj2 Hmem)).
Qed.

Lemma stratum_derives_universe k : program_wf prog facts -> stratified prog st ->
  forall f, derives prog facts st k (model_below prog facts st k) f ->
    in_universe prog facts (fst f) (snd f) = true.
Proof.
  intros Hwf Hstrat f Hderive; eapply derives_universe.
  - exact Hwf.
  - exact Hstrat.
  - intros a Ha; eapply model_constants; eassumption.
  - exact Hderive.
Qed.

Lemma derives_contained k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, post_solution (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s ->
  forall f, derives prog facts st k (model_below prog facts st k) f ->
    FinSet.mem tuple_encoding (snd f) (proj1_sig (s (fst f))) = true.
Proof.
  intros Hwf Hstrat [Hlower Hexact] s Hpost f Hderive.
  induction Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame IH Hneg].
  - destruct f as [p ts]; cbn [fst snd] in *.
    pose proof (proj1 (Hpost (FromFact p)
      (fact_constraint_member k p ts Hfact Hlevel))) as Hle.
    apply (set_member_subset tuple_encoding _ _ Hle).
    cbn [stratum_system System.rhs stratum_rhs Query.eval].
    apply (proj2 (restrict_spec prog facts p ts _ (facts_by_pred_wf p))).
    split; [apply facts_by_pred_exact; exact Hfact |].
    exact (fact_universe prog facts Hwf (p, ts) Hfact).
  - destruct (rule_constraint_member k r Hr Hlevel) as [i [Hc Hindex]].
    pose proof (proj1 (Hpost (FromRule i (pred (head r))) Hc)) as Hle.
    rewrite (rule_rhs_eval k lower s i _ r Hindex) in Hle.
    apply (set_member_subset tuple_encoding _ _ Hle).
    apply (proj2 (restrict_spec prog facts _ _ _
      (fire_rule_wf prog facts _ r (rule_env_wf k lower s r Hlower)))).
    assert (Huniv : in_universe prog facts (pred (head r))
      (map (inst sigma) (args (head r))) = true).
    { apply (stratum_derives_universe k Hwf Hstrat (ground sigma (head r))).
      apply derive_rule with (r := r) (sigma := sigma); assumption. }
    split; [|exact Huniv].
    apply fire_rule_complete; [exact Hwf | exact Hr | apply rule_env_wf; exact Hlower | |
      |]; [exact Huniv | |].
    + intros a Ha; pose proof (proj2 Hstrat r (LPos a) Hr Ha) as Hbound; cbn in Hbound.
      destruct (Nat.eq_dec (level st (pred a)) k) as [Heq | Hne].
      * rewrite rule_env_same by assumption; apply IH; assumption.
      * rewrite rule_env_lower by exact Hne; apply (proj2 (Hexact _ _)).
        apply Hlow; [exact Ha | lia].
    + intros a Ha; rewrite rule_env_lower by
        (pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia).
      destruct (FinSet.mem tuple_encoding (map (inst sigma) (args a)) (lower (pred a)))
        eqn:Hmem; [|reflexivity].
      exfalso; apply (Hneg a Ha); apply (proj1 (Hexact _ _)); exact Hmem.
Qed.

(** Every stratum post-solution contains the inductive closure over the represented lower model. *)
Theorem stratum_post_solution_contains k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, post_solution (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k ->
    derives prog facts st k (model_below prog facts st k) (p', ts') ->
    FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true.
Proof.
  intros Hwf Hstrat Hlower s Hpost p ts _ Hderive.
  exact (derives_contained k lower Hwf Hstrat Hlower s Hpost (p, ts) Hderive).
Qed.

(** Every member of a reached assignment has a derivation in the current stratum. *)
Definition stratum_derived k (s : P -> relation prog facts) : Prop :=
  forall p ts, FinSet.mem tuple_encoding ts (proj1_sig (s p)) = true ->
    derives prog facts st k (model_below prog facts st k) (p, ts).

Lemma stratum_rhs_derives k lower s c : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) -> stratum_derived k s ->
  In c (stratum_constraints prog facts st k) -> forall ts,
  FinSet.mem tuple_encoding ts
    (proj1_sig (Query.eval (System.rhs (stratum_system prog facts st lower k) c) s)) = true ->
  derives prog facts st k (model_below prog facts st k)
    (System.target (stratum_system prog facts st lower k) c, ts).
Proof.
  intros Hwf Hstrat [Hlower Hexact] Hderived Hc ts Hmem; destruct c as [i h | p].
  - destruct (rule_constraint_view k i h Hc) as [r [Hr [Hhead [Hlevel Hindex]]]].
    rewrite (rule_rhs_eval k lower s i h r Hindex) in Hmem.
    apply (proj1 (restrict_spec prog facts h ts _
      (fire_rule_wf prog facts _ r (rule_env_wf k lower s r Hlower)))) in Hmem.
    destruct Hmem as [Hmem _].
    apply (proj1 (fire_rule_exact_core prog facts r _ (proj1 (proj1 Hwf r Hr))
      (rule_env_wf k lower s r Hlower) ts)) in Hmem as [Huniv [sigma [Heq [Hpos Hneg]]]].
    subst h ts; change (derives prog facts st k (model_below prog facts st k)
      (ground sigma (head r))).
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | exact Hlevel | | |].
    + intros a Ha Hlt; apply (proj1 (Hexact _ _)).
      specialize (Hpos a Ha); rewrite rule_env_lower in Hpos by lia; exact Hpos.
    + intros a Ha Heq; apply Hderived.
      specialize (Hpos a Ha); rewrite rule_env_same in Hpos by assumption; exact Hpos.
    + intros a Ha Hbelow; apply (proj2 (Hexact _ _)) in Hbelow.
      specialize (Hneg a Ha); rewrite rule_env_lower in Hneg by
        (pose proof (proj2 Hstrat r (LNeg a) Hr Ha); cbn in *; lia).
      congruence.
  - cbn [stratum_system System.rhs stratum_rhs Query.eval] in Hmem.
    apply (proj1 (restrict_spec prog facts p ts _ (facts_by_pred_wf p))) in Hmem.
    apply derive_fact; [apply facts_by_pred_exact; exact (proj1 Hmem) |].
    apply fact_constraint_level; exact Hc.
Qed.

Lemma stratum_join_preserved k s p (v : relation prog facts) : stratum_derived k s ->
  (forall ts, FinSet.mem tuple_encoding ts (proj1_sig v) = true ->
    derives prog facts st k (model_below prog facts st k) (p, ts)) ->
  stratum_derived k (join_update (penc prog) (relation_lattice prog facts) p v s).
Proof.
  intros Hs Hv q ts; unfold join_update.
  destruct (Pos.eqb (encode (penc prog) p) (encode (penc prog) q)) eqn:Heq.
  - apply Pos.eqb_eq in Heq; apply (encode_injective (penc prog)) in Heq; subst q.
    destruct (leb (relation_lattice prog facts) v (s p)); [apply Hs |].
    cbn [relation_lattice finite_powerset_lattice join proj1_sig].
    rewrite FinSet.mem_union; intros [Hmem | Hmem]; [apply Hs | apply Hv]; exact Hmem.
  - apply Hs.
Qed.

Lemma stratum_raise_preserved k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) -> forall s t,
  stratum_derived k s -> raise (penc prog) (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s t -> stratum_derived k t.
Proof.
  intros Hwf Hstrat Hlower s t Hs [c [Hc Ht]] p ts Hmem.
  rewrite Ht in Hmem; unfold run_updates in Hmem; rewrite run_spec in Hmem.
  rewrite stratum_sides_nil in Hmem; cbn [apply_updates fold_left fst snd] in Hmem.
  eapply stratum_join_preserved; [exact Hs | |exact Hmem].
  intros us Hus; eapply stratum_rhs_derives; eassumption.
Qed.

Lemma reached_derived k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) -> forall s,
  reached (penc prog) (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s -> stratum_derived k s.
Proof.
  intros Hwf Hstrat Hlower s [s0 [Hbot Hsteps]].
  assert (Hpreserve : forall u v, clos_refl_trans _
    (raise (penc prog) (relation_lattice prog facts)
      (stratum_system prog facts st lower k)) u v ->
    stratum_derived k u -> stratum_derived k v).
  { intros u v Hrun; induction Hrun as [u v Hraise | u | u v w Huv IHuv Hvw IHvw];
      intro Hu.
    - eapply stratum_raise_preserved; eassumption.
    - exact Hu.
    - apply IHvw, IHuv; exact Hu. }
  apply (Hpreserve s0 s Hsteps); intros p ts Hmem; rewrite Hbot in Hmem.
  change (FinSet.mem tuple_encoding ts FinSet.empty = true) in Hmem.
  rewrite FinSet.mem_empty in Hmem; discriminate.
Qed.

(** Every tuple reached by joining constraint runs has an inductive stratum derivation. *)
Theorem stratum_reached_derives k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  forall s, reached (penc prog) (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k ->
    FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true ->
    derives prog facts st k (model_below prog facts st k) (p', ts').
Proof.
  intros Hwf Hstrat Hlower s Hreached p ts _ Hmem.
  exact (reached_derived k lower Hwf Hstrat Hlower s Hreached p ts Hmem).
Qed.

(** The total joining solver uses finite powerset height and a prepared reverse postorder. *)
Definition solve_stratum k lower : {s : P -> relation prog facts |
    post_solution (relation_lattice prog facts) (stratum_system prog facts st lower k) s} :=
  solve_total (penc prog) (rconstraint_encoding (penc prog)) (relation_lattice prog facts)
    (finite_powerset_laws tuple_encoding (herbrand prog facts))
    (rpo_scheduler (penc prog) (stratum_system prog facts st lower k)
      (stratum_static prog facts st lower k)) Joining
    (stratum_system prog facts st lower k) (stratum_static prog facts st lower k)
    (inhabits (base_height
      (finite_powerset_height tuple_encoding (herbrand prog facts) (herbrand_nodup prog facts)))).

Lemma solve_stratum_reached k lower : reached (penc prog) (relation_lattice prog facts)
  (stratum_system prog facts st lower k) (proj1_sig (solve_stratum k lower)).
Proof.
  apply solve_total_reached.
Qed.

Lemma solve_stratum_least k lower : program_wf prog facts -> stratified prog st ->
  represents lower (model_below prog facts st k) ->
  least_solution (relation_lattice prog facts) (stratum_system prog facts st lower k)
    (proj1_sig (solve_stratum k lower)).
Proof.
  intros Hwf Hstrat Hlower; apply solve_total_least.
  - apply finite_powerset_lub.
  - apply stratum_system_monotone; [exact Hwf | | exact Hstrat].
    apply (represented_lower_wf k lower); assumption.
Qed.

(** Least stratum solutions contain exactly the derivations over the completed lower model. *)
Theorem stratum_least_is_derives k lower : program_wf prog facts -> stratified prog st ->
  (k < count st)%nat -> represents lower (model_below prog facts st k) ->
  forall s, least_solution (relation_lattice prog facts)
    (stratum_system prog facts st lower k) s ->
  forall p' ts', level st p' = k ->
    (FinSet.mem tuple_encoding ts' (proj1_sig (s p')) = true <->
      derives prog facts st k (model_below prog facts st k) (p', ts')).
Proof.
  intros Hwf Hstrat _ Hlower s Hleast p ts Hlevel; split.
  - intro Hmem; eapply stratum_reached_derives;
      [exact Hwf | exact Hstrat | exact Hlower | apply solve_stratum_reached | exact Hlevel |].
    destruct (least_solution_unique _ _ _ _ Hleast
      (solve_stratum_least k lower Hwf Hstrat Hlower)) as [Hle _].
    apply (set_member_subset tuple_encoding _ _ (Hle p)); exact Hmem.
  - apply (stratum_post_solution_contains k lower); [exact Hwf | exact Hstrat | exact Hlower |
      exact (proj1 Hleast) | exact Hlevel].
Qed.

End Stratum.

Section Program.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : stratification P).

(** Only distinct targets of the current stratum are copied into the persistent database. *)
Definition stratum_targets k : list P :=
  FinSet.elements (FinSet.of_list (penc prog)
    (map (fun c => match c with FromRule _ h => h | FromFact p => p end)
      (stratum_constraints prog facts st k))).

(** Copying targets preserves all other database relations. *)
Definition store_relations (ps : list P) (s : P -> relation prog facts) (db : database P) :=
  fold_right (fun p acc => Map.set (penc prog) p (proj1_sig (s p)) acc) db ps.

(** Computing the first n strata recurses over the finite stratification, with no solver fuel. *)
Fixpoint solve_levels (n : nat) : database P :=
  match n with
  | O => Map.empty
  | S k =>
    let db := solve_levels k in
    let s := proj1_sig (solve_stratum prog facts st k (rel_of prog db)) in
    store_relations (stratum_targets k) s db
  end.

Lemma stratum_targets_spec k p : In p (stratum_targets k) <->
  exists c, In c (stratum_constraints prog facts st k) /\
    System.target (stratum_system prog facts st (fun _ => FinSet.empty) k) c = p.
Proof.
  unfold stratum_targets; rewrite FinSet.elements_spec by
    (apply FinSet.wf_fold_add, Map.wf_empty).
  rewrite FinSet.of_list_spec, in_map_iff; split;
    intros [c [Hfirst Hsecond]]; exists c; split; assumption.
Qed.

Lemma stratum_targets_level k p : In p (stratum_targets k) -> level st p = k.
Proof.
  rewrite stratum_targets_spec; intros [[i h | q] [Hc Heq]]; cbn in Heq; subst p.
  - destruct (rule_constraint_view prog facts st k i h Hc) as [r [_ [_ [Hlevel _]]]].
    exact Hlevel.
  - apply (fact_constraint_level prog facts st k q); exact Hc.
Qed.

Lemma derives_target k f : derives prog facts st k (model_below prog facts st k) f ->
  In (fst f) (stratum_targets k).
Proof.
  intro Hderive; destruct Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame Hneg].
  - destruct f as [p ts]; apply stratum_targets_spec; exists (FromFact p); split;
      [apply (fact_constraint_member prog facts st k p ts); assumption | reflexivity].
  - destruct (rule_constraint_member prog facts st k r Hr Hlevel) as [i [Hc _]].
    apply stratum_targets_spec; exists (FromRule i (pred (head r))); split;
      [exact Hc | reflexivity].
Qed.

Lemma store_relations_member ps s db p : In p ps ->
  rel_of prog (store_relations ps s db) p = proj1_sig (s p).
Proof.
  induction ps as [|q ps IH]; intro Hin; [contradiction |].
  cbn [store_relations fold_right]; unfold rel_of at 1.
  destruct (encoded_eq_dec (penc prog) p q) as [Heq | Hne].
  - subst q; rewrite Map.get_set_same; reflexivity.
  - rewrite Map.get_set_other by exact Hne; apply IH; cbn in Hin; intuition congruence.
Qed.

Lemma store_relations_absent ps s db p : ~ In p ps ->
  rel_of prog (store_relations ps s db) p = rel_of prog db p.
Proof.
  induction ps as [|q ps IH]; intro Hout; [reflexivity |].
  cbn [store_relations fold_right]; unfold rel_of at 1.
  rewrite Map.get_set_other.
  - apply IH; intro Hin; apply Hout; now right.
  - intro Heq; subst q; apply Hout; now left.
Qed.

Lemma store_relations_wf ps s db : (forall p, FinSet.wf tuple_encoding (rel_of prog db p)) ->
  forall p, FinSet.wf tuple_encoding (rel_of prog (store_relations ps s db) p).
Proof.
  intros Hwf p; destruct (in_dec (encoded_eq_dec (penc prog)) p ps) as [Hin | Hout].
  - rewrite store_relations_member by exact Hin; exact (proj1 (proj2_sig (s p))).
  - rewrite store_relations_absent by exact Hout; apply Hwf.
Qed.

Lemma solve_levels_represents : program_wf prog facts -> stratified prog st ->
  forall n, n <= count st -> represents (rel_of prog (solve_levels n))
    (model_below prog facts st n).
Proof.
  intros Hwf Hstrat n; induction n as [|k IH]; intro Hbound.
  - split.
    + intro p; unfold rel_of; cbn [solve_levels]; rewrite Map.get_empty; apply Map.wf_empty.
    + intros p ts; unfold rel_of; cbn [solve_levels]; rewrite Map.get_empty, FinSet.mem_empty.
      cbn [model_below]; split; [discriminate | contradiction].
  - assert (Hbelow := IH (Nat.le_trans _ _ _ (Nat.le_succ_diag_r k) Hbound)).
    set (db := solve_levels k).
    change (represents (rel_of prog db) (model_below prog facts st k)) in Hbelow.
    set (s := proj1_sig (solve_stratum prog facts st k (rel_of prog db))).
    change (represents (rel_of prog (store_relations (stratum_targets k) s db))
      (model_below prog facts st (S k))).
    assert (Hleast : least_solution (relation_lattice prog facts)
      (stratum_system prog facts st (rel_of prog db) k) s).
    { apply solve_stratum_least; assumption. }
    split; [apply store_relations_wf; exact (proj1 Hbelow) |].
    intros p ts; destruct (in_dec (encoded_eq_dec (penc prog)) p (stratum_targets k))
      as [Hin | Hout].
    + rewrite store_relations_member by exact Hin.
      pose proof (stratum_targets_level k p Hin) as Hlevel.
      assert (Hk : k < count st) by lia.
      rewrite (stratum_least_is_derives prog facts st k (rel_of prog db) Hwf Hstrat
        Hk Hbelow s Hleast p ts Hlevel).
      cbn [model_below]; split; [now right |].
      intros [Hbad | Hderive]; [|exact Hderive].
      pose proof (model_below_level prog facts st k (p, ts) Hbad); cbn in *; lia.
    + rewrite store_relations_absent by exact Hout.
      rewrite (proj2 Hbelow p ts); cbn [model_below]; split; [now left |].
      intros [Hmember | Hderive]; [exact Hmember |].
      exfalso; apply Hout; exact (derives_target k (p, ts) Hderive).
Qed.

End Program.

(** Cache the universe sets and rule/fact indexes before constructing any stratum engine.
    Both the right-hand sides and static dependencies capture the same rule index [ri].
    Proof projections in [clamp] and [static] are erased; their data uses the shared closures.
    Unfolding the lets gives the reference compiler definitionally, including its proofs. *)
Definition prepared_levels {P} (prog : program P) (facts : list (ground_atom P)) :
    stratification P -> nat -> database P :=
  let ps := preds prog facts in
  let cs := constants prog facts in
  let accepts := fun p ts => FinSet.mem (penc prog) p ps &&
    Nat.eqb (length ts) (arity prog p) &&
    forallb (fun c => FinSet.mem positive_encoding c cs) ts in
  let clamp : P -> FinSet.t tuple -> relation prog facts := fun p s =>
    exist _ (FinSet.of_list tuple_encoding (filter (accepts p) (FinSet.elements s)))
      (proj2_sig (restrict prog facts p s)) in
  let firing := fun r env => FinSet.of_list tuple_encoding
    (filter (accepts (pred (head r)))
      (map (fun b => map (inst (binding_value b)) (args (head r)))
        (filter (negative_ok r env)
          (join_positive (positive_atoms (body r)) FinSet.empty env [Map.empty])))) in
  let ri := index_rules_from 0 (rules prog) in
  let fi := facts_by_pred prog facts in
  let system := fun st lower k =>
    {| System.constraints := stratum_constraints prog facts st k;
       System.target := fun c => match c with FromRule _ h => h | FromFact p => p end;
       System.rhs := fun c =>
         match c with
         | FromRule i h =>
           match Map.get nat_encoding i ri with
           | Some r =>
             let ds := level_dependencies prog st k r in
             ask_all ds (fun vs => Query.Ret (clamp h
               (firing r (stratum_env prog facts st lower k (fill_values (penc prog) ds vs)))))
           | None => Query.Ret (bot (relation_lattice prog facts))
           end
         | FromFact p => Query.Ret (clamp p (relation_get (penc prog) fi p))
         end |} in
  let static : forall st lower k, System.static (system st lower k) := fun st lower k =>
    {| System.deps := stratum_deps prog st k ri;
       System.side_targets := fun _ => [];
       System.reads_within := System.reads_within (stratum_static prog facts st lower k);
       System.sides_within := System.sides_within (stratum_static prog facts st lower k) |} in
  fun st =>
    fix levels (n : nat) : database P :=
      match n with
      | O => Map.empty
      | S k =>
        let db := levels k in
        let lower := rel_of prog db in
        let sys := system st lower k in
        let ss := static st lower k in
        let s := proj1_sig (solve_total (penc prog) (rconstraint_encoding (penc prog))
          (relation_lattice prog facts)
          (finite_powerset_laws tuple_encoding (herbrand prog facts))
          (rpo_scheduler (penc prog) sys ss) Joining sys ss
          (inhabits (base_height (finite_powerset_height tuple_encoding (herbrand prog facts)
            (herbrand_nodup prog facts))))) in
        store_relations prog facts (stratum_targets prog facts st k) s db
      end.

Lemma prepared_levels_agrees {P} (prog : program P) (facts : list (ground_atom P)) st n :
  prepared_levels prog facts st n = solve_levels prog facts st n.
Proof.
  reflexivity.
Qed.

(** Stratification failure is the only failure of the total stratum-by-stratum solver. *)
Definition solve_program {P} (prog : program P) (facts : list (ground_atom P)) :
    option (database P) :=
  match stratify prog with
  | Some st => Some (prepared_levels prog facts st (count st))
  | None => None
  end.

(** A well-formed stratifiable program is solved exactly by its least semantic model. *)
Theorem solve_program_exact {P} (prog : program P) (facts : list (ground_atom P)) :
  program_wf prog facts -> (exists st', stratified prog st') ->
  exists db, solve_program prog facts = Some db /\
    represents (rel_of prog db) (least_model prog facts).
Proof.
  intros Hwf Hstrat; destruct (stratify_complete prog Hstrat) as [st Hst].
  exists (solve_levels prog facts st (count st)); unfold solve_program, least_model.
  rewrite Hst, prepared_levels_agrees; split;
    [reflexivity | apply solve_levels_represents; auto].
  apply (stratify_sound prog st); exact Hst.
Qed.

(** A program with no stratification yields no database. *)
Theorem solve_program_none {P} (prog : program P) (facts : list (ground_atom P)) :
  (forall st', ~ stratified prog st') -> solve_program prog facts = None.
Proof.
  intro Hnone; unfold solve_program; destruct (stratify prog) as [st |] eqn:Hst;
    [|reflexivity].
  exfalso; apply (Hnone st); apply stratify_sound; exact Hst.
Qed.
