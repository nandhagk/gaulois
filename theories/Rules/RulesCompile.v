(** * Finite relations and compilation of rule strata

    Rule firing joins positive relations through prepared indexes and tests negative literals.
    For example, a unary copy rule fires exactly the tuples present in its source relation.
    Builds on: RulesSyntax, RulesStratify, OrderPowerset and FixpointSystem. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone OrderPowerset.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Rules Require Import RulesSyntax RulesStratify.
Import List.ListNotations.

(** Tuple keys use the shared injective list encoding. *)
Definition tuple_encoding : encoding tuple := list_encoding positive_encoding.

(** Predicates occurring in either a rule or an extensional fact form the predicate universe. *)
Definition preds {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t P :=
  FinSet.of_list (penc prog)
    (flat_map rule_predicates (rules prog) ++ map fst facts).

Definition atom_constants {P} (a : atom P) : tuple :=
  flat_map (fun t => match t with TVar _ => [] | TConst c => [c] end) (args a).

(** Constants include rule constants and every component of every extensional fact. *)
Definition constants {P} (prog : program P) (facts : list (ground_atom P)) : FinSet.t positive :=
  FinSet.of_list positive_encoding
    (flat_map (fun r => atom_constants (head r) ++
      flat_map (fun l => atom_constants (lit_atom l)) (body r)) (rules prog) ++
      flat_map snd facts).

(** Universe membership checks occurrence, arity and the finite constant alphabet. *)
Definition in_universe {P} (prog : program P) (facts : list (ground_atom P))
  (p : P) : tuple -> bool :=
  let present := FinSet.mem (penc prog) p (preds prog facts) in
  let n := arity prog p in
  let cs := constants prog facts in
  fun ts => present && Nat.eqb (length ts) n &&
    forallb (fun c => FinSet.mem positive_encoding c cs) ts.

Fixpoint tuple_words (n : nat) (cs : tuple) : list tuple :=
  match n with
  | 0 => [[]]
  | S n' => let tails := tuple_words n' cs in flat_map (fun c => map (cons c) tails) cs
  end.

Lemma tuple_words_spec n cs ts :
  In ts (tuple_words n cs) <-> length ts = n /\ forall c, In c ts -> In c cs.
Proof.
  revert ts; induction n as [|n IH]; intros [|c ts]; cbn [tuple_words].
  - cbn; intuition.
  - cbn; split.
    + intros [Hbad | Hbad]; [discriminate | contradiction].
    + intros [Hbad _]; discriminate.
  - rewrite in_flat_map; split.
    + intros [c [Hin Hbad]]; apply in_map_iff in Hbad.
      destruct Hbad as [ts [Hbad _]]; discriminate.
    + intros [Hbad _]; discriminate.
  - rewrite in_flat_map; split.
    + intros [c' [Hc Hmap]]; apply in_map_iff in Hmap.
      destruct Hmap as [ts' [Heq Hts]]; injection Heq as Heqc Heqt; subst c' ts'.
      apply IH in Hts; cbn; destruct Hts as [Hlen Hin]; split; [lia |].
      intros d [Heq | Hd]; [subst d; exact Hc | apply Hin; exact Hd].
    + intros [Hlen Hin]; exists c; split; [apply Hin; now left |].
      apply in_map_iff; exists ts; split; [reflexivity | apply IH].
      cbn in Hlen; split; [lia | intros d Hd; apply Hin; now right].
Qed.

(** The proof-only universe enumerates each tuple of every occurring arity once. *)
Definition herbrand {P} (prog : program P) (facts : list (ground_atom P)) : list tuple :=
  FinSet.elements (FinSet.of_list tuple_encoding
    (flat_map (fun p => tuple_words (arity prog p) (FinSet.elements (constants prog facts)))
      (FinSet.elements (preds prog facts)))).

Lemma preds_wf {P} (prog : program P) facts : FinSet.wf (penc prog) (preds prog facts).
Proof.
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

Lemma constants_wf {P} (prog : program P) facts :
  FinSet.wf positive_encoding (constants prog facts).
Proof.
  apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

(** The proof-only list contains exactly the tuples of occurring arities over program constants. *)
Theorem herbrand_spec {P} (prog : program P) (facts : list (ground_atom P)) ts :
  In ts (herbrand prog facts) <-> exists p',
    FinSet.mem (penc prog) p' (preds prog facts) = true /\
    length ts = arity prog p' /\
    forall c, In c ts -> FinSet.mem positive_encoding c (constants prog facts) = true.
Proof.
  unfold herbrand; rewrite FinSet.elements_spec.
  - rewrite FinSet.of_list_spec, in_flat_map; split.
    + intros [p [Hp Hts]]; apply tuple_words_spec in Hts; exists p; split.
      * apply (FinSet.elements_spec (penc prog)); [apply preds_wf | exact Hp].
      * destruct Hts as [Hlen Hcs]; split; [exact Hlen |].
        intros c Hc; apply (FinSet.elements_spec positive_encoding);
          [apply constants_wf | apply Hcs; exact Hc].
    + intros [p [Hp [Hlen Hcs]]]; exists p; split.
      * apply (FinSet.elements_spec (penc prog)); [apply preds_wf | exact Hp].
      * apply tuple_words_spec; split; [exact Hlen |].
        intros c Hc; apply (FinSet.elements_spec positive_encoding);
          [apply constants_wf | apply Hcs; exact Hc].
  - apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

(** Deduplication makes the proof-only universe free of repeated tuples. *)
Theorem herbrand_nodup {P} (prog : program P) (facts : list (ground_atom P)) :
  NoDup (herbrand prog facts).
Proof.
  apply (FinSet.elements_nodup tuple_encoding); apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

(** Relations carry erased proofs of well-formedness and support in the universe. *)
Definition relation {P} (prog : program P) (facts : list (ground_atom P)) : Type :=
  finite_set tuple_encoding (herbrand prog facts).

(** Strata use inclusion and union on the finite relation carrier. *)
Definition relation_lattice {P} (prog : program P) (facts : list (ground_atom P)) :
  lattice (relation prog facts) := finite_powerset_lattice tuple_encoding (herbrand prog facts).

Lemma in_universe_spec {P} (prog : program P) facts p ts :
  in_universe prog facts p ts = true <->
  FinSet.mem (penc prog) p (preds prog facts) = true /\
  length ts = arity prog p /\
  forall c, In c ts -> FinSet.mem positive_encoding c (constants prog facts) = true.
Proof.
  unfold in_universe; rewrite !andb_true_iff, Nat.eqb_eq, forallb_forall; tauto.
Qed.

(** Restriction filters by predicate universe and rebuilds a canonical well-formed set. *)
Definition restrict {P} (prog : program P) (facts : list (ground_atom P))
  (p : P) (s : FinSet.t tuple) : relation prog facts.
Proof.
  refine (exist _ (FinSet.of_list tuple_encoding
    (filter (in_universe prog facts p) (FinSet.elements s))) _).
  abstract (split; [apply FinSet.wf_fold_add; apply Map.wf_empty |];
    intros ts Hts; apply FinSet.of_list_spec in Hts; apply filter_In in Hts;
    apply herbrand_spec; exists p; apply in_universe_spec; exact (proj2 Hts)).
Defined.

(** Restriction keeps exactly the original members that pass the universe test. *)
Theorem restrict_spec {P} (prog : program P) (facts : list (ground_atom P)) p ts s0 :
  FinSet.wf tuple_encoding s0 ->
  FinSet.mem tuple_encoding ts (proj1_sig (restrict prog facts p s0)) = true <->
  FinSet.mem tuple_encoding ts s0 = true /\ in_universe prog facts p ts = true.
Proof.
  intro Hwf; cbn [restrict proj1_sig]; rewrite FinSet.of_list_spec, filter_In.
  rewrite FinSet.elements_spec by exact Hwf; reflexivity.
Qed.

(** A relation environment is well formed and respects each predicate's arity. *)
Definition env_wf {P} (prog : program P) (env : P -> FinSet.t tuple) : Prop :=
  forall p, FinSet.wf tuple_encoding (env p) /\
    forall ts, FinSet.mem tuple_encoding ts (env p) = true -> length ts = arity prog p.

(** * Partial valuations *)

Definition binding := Map.t nat positive.

Definition binding_value (b : binding) v : positive :=
  match Map.get nat_encoding v b with Some c => c | None => 1%positive end.

Definition binding_agrees (b : binding) (sigma : nat -> positive) : Prop :=
  forall v c, Map.get nat_encoding v b = Some c -> sigma v = c.

Definition binding_extends (b b' : binding) : Prop :=
  forall v c, Map.get nat_encoding v b = Some c -> Map.get nat_encoding v b' = Some c.

Lemma binding_value_agrees b : binding_agrees b (binding_value b).
Proof.
  intros v c Hget; unfold binding_value; rewrite Hget; reflexivity.
Qed.

Lemma binding_agrees_extends b b' sigma :
  binding_extends b b' -> binding_agrees b' sigma -> binding_agrees b sigma.
Proof.
  intros Hext Hagree v c Hget; apply Hagree, Hext, Hget.
Qed.

Lemma binding_extends_trans b b' b'' :
  binding_extends b b' -> binding_extends b' b'' -> binding_extends b b''.
Proof.
  intros Hleft Hright v c Hget; apply Hright, Hleft, Hget.
Qed.

Lemma binding_set_extends b v c : Map.get nat_encoding v b = None ->
  binding_extends b (Map.set nat_encoding v c b).
Proof.
  intros Hnone w d Hget; destruct (Nat.eq_dec w v) as [Heq | Hne].
  - subst w; congruence.
  - rewrite Map.get_set_other by exact Hne; exact Hget.
Qed.

Lemma binding_set_agrees b sigma v c :
  binding_agrees b sigma -> sigma v = c -> binding_agrees (Map.set nat_encoding v c b) sigma.
Proof.
  intros Hagree Hvalue w d Hget; destruct (Nat.eq_dec w v) as [Heq | Hne].
  - subst w; rewrite Map.get_set_same in Hget; injection Hget as Heq; subst d; exact Hvalue.
  - rewrite Map.get_set_other in Hget by exact Hne; apply Hagree; exact Hget.
Qed.

Definition bind_term (b : binding) (t : term) (c : positive) : option binding :=
  match t with
  | TConst d => if Pos.eqb c d then Some b else None
  | TVar v =>
    match Map.get nat_encoding v b with
    | Some d => if Pos.eqb c d then Some b else None
    | None => Some (Map.set nat_encoding v c b)
    end
  end.

Fixpoint bind_terms (ts : list term) (cs : tuple) (b : binding) : option binding :=
  match ts, cs with
  | [], [] => Some b
  | t :: ts', c :: cs' =>
    match bind_term b t c with
    | Some b' => bind_terms ts' cs' b'
    | None => None
    end
  | _, _ => None
  end.

Lemma bind_term_sound b t c b' : bind_term b t c = Some b' ->
  binding_extends b b' /\
  (forall sigma, binding_agrees b' sigma -> inst sigma t = c) /\
  (forall v, t = TVar v -> exists d, Map.get nat_encoding v b' = Some d).
Proof.
  destruct t as [v | d]; cbn [bind_term].
  - destruct (Map.get nat_encoding v b) as [d |] eqn:Hget.
    + destruct (Pos.eqb c d) eqn:Heq; [|discriminate].
      apply Pos.eqb_eq in Heq; subst d; intro Hsome; injection Hsome as Hb; subst b'.
      split; [intros w d Hwd; exact Hwd | split].
      * intros sigma Hagree; apply Hagree; exact Hget.
      * intros w Heq; injection Heq as Heq; subst w; exists c; exact Hget.
    + intro Hsome; injection Hsome as Hb; subst b'; split.
      * apply binding_set_extends; exact Hget.
      * split.
        -- intros sigma Hagree; apply Hagree; apply Map.get_set_same.
        -- intros w Heq; injection Heq as Heq; subst w; exists c; apply Map.get_set_same.
  - destruct (Pos.eqb c d) eqn:Heq; [|discriminate].
    apply Pos.eqb_eq in Heq; subst d; intro Hsome; injection Hsome as Hb; subst b'.
    split; [intros w d Hwd; exact Hwd | split].
    + intros sigma _; reflexivity.
    + intros v Hbad; discriminate.
Qed.

Lemma bind_term_complete b t sigma : binding_agrees b sigma ->
  exists b', bind_term b t (inst sigma t) = Some b' /\ binding_agrees b' sigma.
Proof.
  intro Hagree; destruct t as [v | c]; cbn [bind_term inst].
  - destruct (Map.get nat_encoding v b) as [d |] eqn:Hget.
    + rewrite (Hagree v d Hget), Pos.eqb_refl; exists b; auto.
    + eexists; split; [reflexivity | apply binding_set_agrees; [exact Hagree | reflexivity]].
  - rewrite Pos.eqb_refl; exists b; auto.
Qed.

Lemma bind_terms_sound ts cs b b' : bind_terms ts cs b = Some b' ->
  binding_extends b b' /\
  (forall sigma, binding_agrees b' sigma -> cs = map (inst sigma) ts) /\
  (forall v, In (TVar v) ts -> exists d, Map.get nat_encoding v b' = Some d).
Proof.
  revert cs b b'; induction ts as [|t ts IH]; intros [|c cs] b b';
    cbn [bind_terms]; try discriminate.
  - intro Hsome; injection Hsome as Hb; subst b'; split.
    + intros v d Hget; exact Hget.
    + split; [intros sigma _; reflexivity | intros v Hbad; contradiction].
  - destruct (bind_term b t c) as [b1 |] eqn:Hterm; [|discriminate].
    intro Hrest; destruct (bind_term_sound b t c b1 Hterm) as [Hext [Hvalue Hbound]].
    destruct (IH cs b1 b' Hrest) as [Hrestext [Hvalues Hbounds]].
    split; [eapply binding_extends_trans; eassumption | split].
    + intros sigma Hagree; cbn [map]; f_equal.
      * symmetry; apply Hvalue; eapply binding_agrees_extends; eassumption.
      * apply Hvalues; exact Hagree.
    + intros v [Heq | Hin].
      * destruct (Hbound v Heq) as [d Hget]; exists d; apply Hrestext; exact Hget.
      * apply Hbounds; exact Hin.
Qed.

Lemma bind_terms_complete ts b sigma : binding_agrees b sigma ->
  exists b', bind_terms ts (map (inst sigma) ts) b = Some b' /\ binding_agrees b' sigma.
Proof.
  revert b; induction ts as [|t ts IH]; intros b Hagree; cbn [bind_terms map].
  - exists b; auto.
  - destruct (bind_term_complete b t sigma Hagree) as [b1 [Hterm Hagree1]].
    rewrite Hterm; apply IH; exact Hagree1.
Qed.

Lemma atom_vars_spec {P} (a : atom P) v : In v (atom_vars a) <-> In (TVar v) (args a).
Proof.
  unfold atom_vars; rewrite in_flat_map; split.
  - intros [t [Hin Hvar]]; destruct t as [w | c]; cbn in Hvar.
    + destruct Hvar as [Heq | Hbad]; [subst w; exact Hin | contradiction].
    + contradiction.
  - intro Hin; exists (TVar v); cbn; auto.
Qed.

Lemma inst_agrees_on_bound ts b sigma : binding_agrees b sigma ->
  (forall v, In (TVar v) ts -> exists d, Map.get nat_encoding v b = Some d) ->
  map (inst (binding_value b)) ts = map (inst sigma) ts.
Proof.
  intros Hagree Hbound; apply map_ext_in; intros t Hin; destruct t as [v | c]; [|reflexivity].
  destruct (Hbound v Hin) as [d Hget]; cbn [inst]; unfold binding_value; rewrite Hget.
  symmetry; apply Hagree; exact Hget.
Qed.

(** * Prepared indexes on bound argument positions *)

Definition bound_term (bound : FinSet.t nat) (t : term) : bool :=
  match t with
  | TVar v => FinSet.mem nat_encoding v bound
  | TConst _ => true
  end.

Definition bound_key bound b ts : tuple :=
  map (inst (binding_value b)) (filter (bound_term bound) ts).

Fixpoint tuple_key (bound : FinSet.t nat) (ts : list term) (cs : tuple) : option tuple :=
  match ts, cs with
  | [], [] => Some []
  | t :: ts', c :: cs' =>
    match tuple_key bound ts' cs' with
    | Some key => Some (if bound_term bound t then c :: key else key)
    | None => None
    end
  | _, _ => None
  end.

Definition tuple_index := Map.t tuple (list tuple).

Definition index_get (idx : tuple_index) (key : tuple) : list tuple :=
  match Map.get tuple_encoding key idx with Some rows => rows | None => [] end.

Definition index_add bound ts cs (idx : tuple_index) : tuple_index :=
  match tuple_key bound ts cs with
  | Some key => Map.set tuple_encoding key (cs :: index_get idx key) idx
  | None => idx
  end.

Definition build_index bound ts rows : tuple_index :=
  fold_right (index_add bound ts) Map.empty rows.

Lemma index_add_spec bound ts cs idx key row :
  In row (index_get (index_add bound ts cs idx) key) <->
  In row (index_get idx key) \/ (row = cs /\ tuple_key bound ts cs = Some key).
Proof.
  unfold index_add; destruct (tuple_key bound ts cs) as [key' |] eqn:Hkey.
  - destruct (list_eq_dec Pos.eq_dec key key') as [Heq | Hne].
    + subst key'; unfold index_get at 1; rewrite Map.get_set_same; cbn.
      intuition congruence.
    + unfold index_get at 1; rewrite Map.get_set_other by exact Hne.
      fold (index_get idx key); split; [auto |].
      intros [Hin | [_ Hbad]]; [exact Hin | injection Hbad as Hbad; congruence].
  - intuition discriminate.
Qed.

(** An index probe returns precisely the correctly sized rows with the requested bound key. *)
Lemma build_index_spec bound ts rows key row :
  In row (index_get (build_index bound ts rows) key) <->
  In row rows /\ tuple_key bound ts row = Some key.
Proof.
  induction rows as [|cs rows IH]; cbn [build_index fold_right].
  - unfold index_get; rewrite Map.get_empty; cbn; tauto.
  - rewrite index_add_spec, IH; cbn [In]; intuition congruence.
Qed.

Definition binding_covers bound (b : binding) : Prop :=
  forall v, FinSet.mem nat_encoding v bound = true ->
    exists c, Map.get nat_encoding v b = Some c.

Lemma bound_key_agrees bound b ts sigma :
  binding_covers bound b -> binding_agrees b sigma ->
  bound_key bound b ts = map (inst sigma) (filter (bound_term bound) ts).
Proof.
  intros Hcover Hagree; unfold bound_key; apply map_ext_in; intros t Hin.
  apply filter_In in Hin; destruct Hin as [_ Hbound]; destruct t as [v | c]; [|reflexivity].
  destruct (Hcover v Hbound) as [d Hget]; cbn [inst]; unfold binding_value; rewrite Hget.
  symmetry; apply Hagree; exact Hget.
Qed.

Lemma tuple_key_instance bound ts sigma :
  tuple_key bound ts (map (inst sigma) ts) =
    Some (map (inst sigma) (filter (bound_term bound) ts)).
Proof.
  induction ts as [|t ts IH]; cbn [tuple_key map filter]; [reflexivity |].
  rewrite IH; destruct (bound_term bound t); reflexivity.
Qed.

Definition bound_add {P} (bound : FinSet.t nat) (a : atom P) :=
  FinSet.union nat_encoding bound (FinSet.of_list nat_encoding (atom_vars a)).

Lemma binding_covers_extends bound b b' :
  binding_covers bound b -> binding_extends b b' -> binding_covers bound b'.
Proof.
  intros Hcover Hext v Hin; destruct (Hcover v Hin) as [c Hget]; exists c; apply Hext; exact Hget.
Qed.

Lemma binding_covers_add {P} bound (a : atom P) b :
  binding_covers bound b ->
  (forall v, In (TVar v) (args a) -> exists c, Map.get nat_encoding v b = Some c) ->
  binding_covers (bound_add bound a) b.
Proof.
  intros Hcover Hvars v Hin; apply FinSet.mem_union in Hin; destruct Hin as [Hin | Hin].
  - apply Hcover; exact Hin.
  - apply FinSet.of_list_spec in Hin; apply Hvars; apply atom_vars_spec; exact Hin.
Qed.

Definition positive_atoms {P} (ls : list (literal P)) : list (atom P) :=
  flat_map (fun l => match l with LPos a => [a] | LNeg _ => [] end) ls.

Lemma positive_atoms_spec {P} (ls : list (literal P)) a :
  In a (positive_atoms ls) <-> In (LPos a) ls.
Proof.
  unfold positive_atoms; rewrite in_flat_map; split.
  - intros [l [Hin Hpos]]; destruct l as [b | b]; cbn in Hpos; [|contradiction].
    destruct Hpos as [Heq | Hbad]; [subst b; exact Hin | contradiction].
  - intro Hin; exists (LPos a); cbn; auto.
Qed.

Definition option_binding (o : option binding) : list binding :=
  match o with Some b => [b] | None => [] end.

Lemma option_binding_spec o b : In b (option_binding o) <-> o = Some b.
Proof.
  destruct o as [b' |]; cbn; intuition congruence.
Qed.

Definition join_step {P} bound (a : atom P) (env : P -> FinSet.t tuple) bs : list binding :=
  let idx := build_index bound (args a) (FinSet.elements (env (pred a))) in
  flat_map (fun b => flat_map (fun cs => option_binding (bind_terms (args a) cs b))
    (index_get idx (bound_key bound b (args a)))) bs.

Lemma join_step_sound {P} bound (a : atom P) env bs b' :
  FinSet.wf tuple_encoding (env (pred a)) ->
  (forall b, In b bs -> binding_covers bound b) ->
  In b' (join_step bound a env bs) -> exists b, In b bs /\ binding_extends b b' /\
    (forall sigma, binding_agrees b' sigma ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    binding_covers (bound_add bound a) b' /\
    (forall v, In (TVar v) (args a) -> exists c, Map.get nat_encoding v b' = Some c).
Proof.
  intros Hwf Hcovers Hin; unfold join_step in Hin; apply in_flat_map in Hin.
  destruct Hin as [b [Hb Hin]]; apply in_flat_map in Hin; destruct Hin as [cs [Hcs Hmatch]].
  apply build_index_spec in Hcs; apply option_binding_spec in Hmatch.
  destruct (bind_terms_sound (args a) cs b b' Hmatch) as [Hext [Hvalue Hvars]].
  exists b; split; [exact Hb | split; [exact Hext | split]].
  - intros sigma Hagree; rewrite <- (Hvalue sigma Hagree).
    apply (FinSet.elements_spec tuple_encoding); [exact Hwf | exact (proj1 Hcs)].
  - split; [|exact Hvars]; apply binding_covers_add; [|exact Hvars].
    eapply binding_covers_extends; [apply Hcovers; exact Hb | exact Hext].
Qed.

Lemma join_step_complete {P} bound (a : atom P) env bs b sigma :
  FinSet.wf tuple_encoding (env (pred a)) -> In b bs ->
  binding_covers bound b -> binding_agrees b sigma ->
  FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true ->
  exists b', In b' (join_step bound a env bs) /\ binding_agrees b' sigma /\
    binding_extends b b' /\ binding_covers (bound_add bound a) b' /\
    (forall v, In (TVar v) (args a) -> exists c, Map.get nat_encoding v b' = Some c).
Proof.
  intros Hwf Hb Hcover Hagree Hmem.
  destruct (bind_terms_complete (args a) b sigma Hagree) as [b' [Hmatch Hagree']].
  destruct (bind_terms_sound (args a) _ b b' Hmatch) as [Hext [_ Hvars]].
  exists b'; split.
  - unfold join_step; apply in_flat_map; exists b; split; [exact Hb |].
    apply in_flat_map; exists (map (inst sigma) (args a)); split.
    + apply build_index_spec; split.
      * apply (FinSet.elements_spec tuple_encoding); assumption.
      * rewrite tuple_key_instance, (bound_key_agrees bound b (args a) sigma Hcover Hagree).
        reflexivity.
    + apply option_binding_spec; exact Hmatch.
  - split; [exact Hagree' | split; [exact Hext | split; [|exact Hvars]]].
    apply binding_covers_add; [|exact Hvars]; eapply binding_covers_extends; eassumption.
Qed.

Fixpoint join_positive {P} (ps : list (atom P)) bound env bs : list binding :=
  match ps with
  | [] => bs
  | a :: ps' => join_positive ps' (bound_add bound a) env (join_step bound a env bs)
  end.

Lemma join_positive_sound {P} (ps : list (atom P)) bound env bs b' :
  (forall p, FinSet.wf tuple_encoding (env p)) ->
  (forall b, In b bs -> binding_covers bound b) ->
  In b' (join_positive ps bound env bs) ->
  exists b, In b bs /\ binding_extends b b' /\
    (forall sigma, binding_agrees b' sigma -> forall a, In a ps ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    (forall a, In a ps -> forall v, In (TVar v) (args a) ->
      exists c, Map.get nat_encoding v b' = Some c).
Proof.
  revert bound bs; induction ps as [|a ps IH]; intros bound bs Hwf Hcover Hin.
  - exists b'; split; [exact Hin | split].
    + intros v c Hget; exact Hget.
    + split; intros; contradiction.
  - destruct (IH (bound_add bound a) (join_step bound a env bs) Hwf) as
      [b1 [Hb1 [Hext1 [Hvalues Hvars]]]].
    + intros b Hb; destruct (join_step_sound bound a env bs b (Hwf _) Hcover Hb) as
        [b0 [_ [_ [_ [Hcover' _]]]]]; exact Hcover'.
    + exact Hin.
    + destruct (join_step_sound bound a env bs b1 (Hwf _) Hcover Hb1) as
        [b0 [Hb0 [Hext0 [Hvalue [_ Hbound]]]]].
      exists b0; split; [exact Hb0 | split].
      * eapply binding_extends_trans; eassumption.
      * split.
        -- intros sigma Hagree x [Heq | Hx].
           ++ subst x; apply Hvalue; eapply binding_agrees_extends; eassumption.
           ++ apply Hvalues; assumption.
        -- intros x [Heq | Hx] v Hv.
           ++ subst x; destruct (Hbound v Hv) as [c Hget]; exists c; apply Hext1; exact Hget.
           ++ apply Hvars with x; assumption.
Qed.

Lemma join_positive_complete {P} (ps : list (atom P)) bound env bs b sigma :
  (forall p, FinSet.wf tuple_encoding (env p)) -> In b bs ->
  binding_covers bound b -> binding_agrees b sigma ->
  (forall a, In a ps ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) ->
  exists b', In b' (join_positive ps bound env bs) /\ binding_agrees b' sigma /\
    binding_extends b b' /\
    (forall a, In a ps -> forall v, In (TVar v) (args a) ->
      exists c, Map.get nat_encoding v b' = Some c).
Proof.
  revert bound bs b; induction ps as [|a ps IH];
    intros bound bs b Hwf Hb Hcover Hagree Hvalues.
  - exists b; split; [exact Hb | split; [exact Hagree | split]].
    + intros v c Hget; exact Hget.
    + intros x Hbad; contradiction.
  - destruct (join_step_complete bound a env bs b sigma (Hwf _) Hb Hcover Hagree
      (Hvalues a (or_introl eq_refl))) as [b1 [Hb1 [Hagree1 [Hext1 [Hcover1 Hbound1]]]]].
    destruct (IH (bound_add bound a) (join_step bound a env bs) b1 Hwf Hb1 Hcover1 Hagree1)
      as [b' [Hb' [Hagree' [Hext' Hvars]]]].
    + intros x Hx; apply Hvalues; now right.
    + exists b'; split; [exact Hb' | split; [exact Hagree' | split]].
      * eapply binding_extends_trans; eassumption.
      * intros x [Heq | Hx] v Hv.
        -- subst x; destruct (Hbound1 v Hv) as [c Hget]; exists c; apply Hext'; exact Hget.
        -- apply Hvars with x; assumption.
Qed.

(** * Rule firing *)

Definition negative_ok {P} (r : rule P) (env : P -> FinSet.t tuple) b : bool :=
  forallb (fun l => match l with
    | LPos _ => true
    | LNeg a => negb (FinSet.mem tuple_encoding
        (map (inst (binding_value b)) (args a)) (env (pred a)))
    end) (body r).

Lemma negative_ok_spec {P} (r : rule P) env b : negative_ok r env b = true <->
  forall a, In (LNeg a) (body r) ->
    FinSet.mem tuple_encoding (map (inst (binding_value b)) (args a)) (env (pred a)) = false.
Proof.
  unfold negative_ok; rewrite forallb_forall; split.
  - intros H a Hin; specialize (H _ Hin); apply negb_true_iff; exact H.
  - intros H [a | a] Hin; [reflexivity | apply negb_true_iff; apply H; exact Hin].
Qed.

(** Firing joins positives, tests negatives, filters head tuples and normalizes the output set. *)
Definition fire_rule {P} (prog : program P) (facts : list (ground_atom P)) (r : rule P)
  (env : P -> FinSet.t tuple) : FinSet.t tuple :=
  FinSet.of_list tuple_encoding (filter (in_universe prog facts (pred (head r)))
    (map (fun b => map (inst (binding_value b)) (args (head r)))
      (filter (negative_ok r env)
        (join_positive (positive_atoms (body r)) FinSet.empty env [Map.empty])))).

Lemma fire_rule_members {P} (prog : program P) facts r env ts :
  FinSet.mem tuple_encoding ts (fire_rule prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts = true /\
  exists b, In b (join_positive (positive_atoms (body r)) FinSet.empty env [Map.empty]) /\
    negative_ok r env b = true /\ ts = map (inst (binding_value b)) (args (head r)).
Proof.
  unfold fire_rule; rewrite FinSet.of_list_spec, filter_In, in_map_iff; split.
  - intros [[b [Heq Hin]] Huniv]; apply filter_In in Hin; split; [exact Huniv |].
    exists b; intuition congruence.
  - intros [Huniv [b [Hin [Hneg Heq]]]]; split; [|exact Huniv].
    exists b; split; [symmetry; exact Heq | apply filter_In; auto].
Qed.

Lemma empty_binding_covers : binding_covers FinSet.empty Map.empty.
Proof.
  intros v Hin; rewrite FinSet.mem_empty in Hin; discriminate.
Qed.

Lemma empty_binding_agrees sigma : binding_agrees Map.empty sigma.
Proof.
  intros v c Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma safe_binding_agrees {P} (r : rule P) b sigma :
  safe_rule r -> binding_agrees b sigma ->
  (forall a, In (LPos a) (body r) -> forall v, In (TVar v) (args a) ->
    exists c, Map.get nat_encoding v b = Some c) ->
  map (inst (binding_value b)) (args (head r)) = map (inst sigma) (args (head r)) /\
  forall a, In (LNeg a) (body r) ->
    map (inst (binding_value b)) (args a) = map (inst sigma) (args a).
Proof.
  intros Hsafe Hagree Hbound; split.
  - apply inst_agrees_on_bound; [exact Hagree |].
    intros v Hin; apply atom_vars_spec in Hin.
    destruct (Hsafe v (or_introl Hin)) as [a [Ha Hv]]; apply Hbound with a;
      [exact Ha | apply atom_vars_spec; exact Hv].
  - intros a Ha; apply inst_agrees_on_bound; [exact Hagree |].
    intros v Hin; apply atom_vars_spec in Hin.
    destruct (Hsafe v (or_intror (ex_intro _ a (conj Ha Hin)))) as [a' [Ha' Hv]].
    apply Hbound with a'; [exact Ha' | apply atom_vars_spec; exact Hv].
Qed.

(** Exact firing requires safety but does not require an arity invariant on stored relations. *)
Lemma fire_rule_exact_core {P} (prog : program P) facts r env :
  safe_rule r -> (forall p, FinSet.wf tuple_encoding (env p)) -> forall ts,
  FinSet.mem tuple_encoding ts (fire_rule prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts = true /\
  exists sigma, ts = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    (forall a, In (LNeg a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false).
Proof.
  intros Hsafe Hwf ts; rewrite fire_rule_members; split.
  - intros [Huniv [b [Hin [Hneg Heq]]]]; split; [exact Huniv |].
    exists (binding_value b); split; [exact Heq | split].
    + destruct (join_positive_sound (positive_atoms (body r)) FinSet.empty env
        [Map.empty] b Hwf) as [b0 [_ [_ [Hvalues _]]]].
      * intros b' [Hb' | Hbad]; [subst b'; apply empty_binding_covers | contradiction].
      * exact Hin.
      * intros a Ha; apply Hvalues.
        -- apply binding_value_agrees.
        -- apply positive_atoms_spec; exact Ha.
    + apply negative_ok_spec; exact Hneg.
  - intros [Huniv [sigma [Heq [Hpos Hneg]]]].
    destruct (join_positive_complete (positive_atoms (body r)) FinSet.empty env
      [Map.empty] Map.empty sigma Hwf (or_introl eq_refl) empty_binding_covers
      (empty_binding_agrees sigma)) as [b [Hin [Hagree [_ Hbound]]]].
    + intros a Ha; apply Hpos; apply positive_atoms_spec; exact Ha.
    + assert (Hbound' : forall a, In (LPos a) (body r) -> forall v,
        In (TVar v) (args a) -> exists c, Map.get nat_encoding v b = Some c).
      { intros a Ha; apply Hbound; apply positive_atoms_spec; exact Ha. }
      destruct (safe_binding_agrees r b sigma Hsafe Hagree Hbound') as [Hhead Hnegative].
      split; [exact Huniv | exists b; split; [exact Hin | split]].
      * apply negative_ok_spec; intros a Ha; rewrite Hnegative by exact Ha; apply Hneg; exact Ha.
      * rewrite Hhead; exact Heq.
Qed.

(** Firing is exactly satisfaction of the body by an in-universe head valuation. *)
Theorem fire_rule_exact {P} (prog : program P) (facts : list (ground_atom P)) env r :
  program_wf prog facts -> In r (rules prog) -> env_wf prog env -> forall ts',
  FinSet.mem tuple_encoding ts' (fire_rule prog facts r env) = true <->
  in_universe prog facts (pred (head r)) ts' = true /\
  exists sigma, ts' = map (inst sigma) (args (head r)) /\
    (forall a, In (LPos a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) /\
    (forall a, In (LNeg a) (body r) ->
      FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false).
Proof.
  intros [Hrules _] Hr Henv; apply fire_rule_exact_core.
  - exact (proj1 (Hrules r Hr)).
  - intro p; exact (proj1 (Henv p)).
Qed.

(** Every firing result is a well-formed finite tuple set. *)
Theorem fire_rule_wf {P} (prog : program P) (facts : list (ground_atom P)) env r :
  (forall q, FinSet.wf tuple_encoding (env q)) ->
  FinSet.wf tuple_encoding (fire_rule prog facts r env).
Proof.
  intros _; apply FinSet.wf_fold_add; apply Map.wf_empty.
Qed.

(** Every satisfying in-universe valuation is fired, even with malformed stored arities. *)
Theorem fire_rule_complete {P} (prog : program P) (facts : list (ground_atom P)) env r :
  program_wf prog facts -> In r (rules prog) ->
  (forall q, FinSet.wf tuple_encoding (env q)) -> forall sigma,
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true ->
  (forall a, In (LPos a) (body r) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = true) ->
  (forall a, In (LNeg a) (body r) ->
    FinSet.mem tuple_encoding (map (inst sigma) (args a)) (env (pred a)) = false) ->
  FinSet.mem tuple_encoding (map (inst sigma) (args (head r))) (fire_rule prog facts r env) = true.
Proof.
  intros [Hrules _] Hr Hwf sigma Huniv Hpos Hneg.
  apply (proj2 (fire_rule_exact_core prog facts r env (proj1 (Hrules r Hr)) Hwf _)).
  split; [exact Huniv | exists sigma; auto].
Qed.

(** * Compilation of one stratum *)

(** Rule positions and extensional predicates identify the finite constraints. *)
Inductive rconstraint (P : Type) : Type :=
  | FromRule (i : nat) (h : P)
  | FromFact (p : P).

Arguments FromRule {P}.
Arguments FromFact {P}.

(** A constructor tag separates rule-position keys from fact-predicate keys. *)
Definition rconstraint_encoding {P} (EP : encoding P) : encoding (rconstraint P).
Proof.
  refine (Encoding _ (fun c => match c with
    | FromRule i h => xO (encode (pair_encoding nat_encoding EP) (i, h))
    | FromFact p => xI (encode EP p)
    end) _).
  intros [i h | p] [j h' | p'] Heq; try discriminate.
  - injection Heq as Heq.
    change (encode (pair_encoding nat_encoding EP) (i, h) =
      encode (pair_encoding nat_encoding EP) (j, h')) in Heq.
    apply (encode_injective (pair_encoding nat_encoding EP)) in Heq.
    injection Heq as Hi Hh; subst j h'; reflexivity.
  - injection Heq as Heq; apply (encode_injective EP) in Heq; subst p'; reflexivity.
Defined.

Fixpoint numbered_rules {P} (n : nat) (rs : list (rule P)) : list (nat * rule P) :=
  match rs with
  | [] => []
  | r :: rs' => (n, r) :: numbered_rules (S n) rs'
  end.

Fixpoint index_rules_from {P} (n : nat) (rs : list (rule P)) : Map.t nat (rule P) :=
  match rs with
  | [] => Map.empty
  | r :: rs' => Map.set nat_encoding n r (index_rules_from (S n) rs')
  end.

Lemma numbered_rules_member {P} n (rs : list (rule P)) i r :
  In (i, r) (numbered_rules n rs) -> n <= i /\ In r rs.
Proof.
  revert n; induction rs as [|r' rs IH]; intros n Hin; cbn in Hin; [contradiction |].
  destruct Hin as [Heq | Hin].
  - injection Heq as Hi Hr; subst i r'; cbn; auto.
  - destruct (IH (S n) Hin) as [Hle Hr]; cbn; split; [lia | now right].
Qed.

Lemma index_rules_member {P} n (rs : list (rule P)) i r :
  In (i, r) (numbered_rules n rs) -> Map.get nat_encoding i (index_rules_from n rs) = Some r.
Proof.
  revert n; induction rs as [|r' rs IH]; intros n Hin; cbn in Hin; [contradiction |].
  cbn [index_rules_from]; destruct Hin as [Heq | Hin].
  - injection Heq as Hi Hr; subst i r'; apply Map.get_set_same.
  - rewrite Map.get_set_other; [apply IH; exact Hin |].
    pose proof (proj1 (numbered_rules_member (S n) rs i r Hin)); lia.
Qed.

Definition level_dependencies {P} (prog : program P) (st : stratification P) k (r : rule P) :=
  FinSet.elements (FinSet.of_list (penc prog)
    (map pred (filter (fun a => Nat.eqb (level st (pred a)) k) (positive_atoms (body r))))).

Fixpoint fill_values {X A} (E : encoding X) (ps : list X) (vs : list A) : Map.t X A :=
  match ps, vs with
  | p :: ps', v :: vs' => Map.set E p v (fill_values E ps' vs')
  | _, _ => Map.empty
  end.

Definition stratum_env {P} (prog : program P) (facts : list (ground_atom P)) st lower k
  (reads : Map.t P (relation prog facts)) (p : P) : FinSet.t tuple :=
  if Nat.eqb (level st p) k then
    match Map.get (penc prog) p reads with Some v => proj1_sig v | None => FinSet.empty end
  else lower p.

Definition relation_get {P} (E : encoding P) (idx : Map.t P (FinSet.t tuple)) p :=
  match Map.get E p idx with Some s => s | None => FinSet.empty end.

Definition facts_by_pred {P} (prog : program P) (facts : list (ground_atom P)) :=
  fold_right (fun f idx => Map.set (penc prog) (fst f)
    (FinSet.add tuple_encoding (snd f) (relation_get (penc prog) idx (fst f))) idx)
    Map.empty facts.

Definition stratum_constraints {P} (prog : program P) (facts : list (ground_atom P)) st k :=
  flat_map (fun ir => if Nat.eqb (level st (pred (head (snd ir)))) k
    then [FromRule (fst ir) (pred (head (snd ir)))] else []) (numbered_rules 0 (rules prog)) ++
  map FromFact (filter (fun p => Nat.eqb (level st p) k)
    (FinSet.elements (FinSet.of_list (penc prog) (map fst facts)))).

Definition stratum_rhs {P} (prog : program P) (facts : list (ground_atom P)) st lower k
  (ri : Map.t nat (rule P)) (fi : Map.t P (FinSet.t tuple)) (c : rconstraint P) :
  Query.t P (relation prog facts) :=
  match c with
  | FromRule i h =>
    match Map.get nat_encoding i ri with
    | Some r =>
      let ds := level_dependencies prog st k r in
      ask_all ds (fun vs => Query.Ret (restrict prog facts h
        (fire_rule prog facts r
          (stratum_env prog facts st lower k (fill_values (penc prog) ds vs)))))
    | None => Query.Ret (bot (relation_lattice prog facts))
    end
  | FromFact p => Query.Ret (restrict prog facts p (relation_get (penc prog) fi p))
  end.

(** Each stratum has one constraint per applicable rule and distinct fact predicate. *)
Definition stratum_system {P} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (lower : P -> FinSet.t tuple) (k : nat) :
  System.t P (rconstraint P) (relation prog facts) :=
  let ri := index_rules_from 0 (rules prog) in
  let fi := facts_by_pred prog facts in
  {| System.constraints := stratum_constraints prog facts st k;
     System.target := fun c => match c with FromRule _ h => h | FromFact p => p end;
     System.rhs := stratum_rhs prog facts st lower k ri fi |}.

Definition stratum_deps {P} (prog : program P) st k (ri : Map.t nat (rule P))
  (c : rconstraint P) :=
  match c with
  | FromRule i _ =>
    match Map.get nat_encoding i ri with
    | Some r => level_dependencies prog st k r
    | None => []
    end
  | FromFact _ => []
  end.

(** Static summaries contain every read of a compiled rule and no side contributions. *)
Definition stratum_static {P} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) (lower : P -> FinSet.t tuple) (k : nat) :
  System.static (stratum_system prog facts st lower k).
Proof.
  refine {| System.deps := stratum_deps prog st k (index_rules_from 0 (rules prog));
    System.side_targets := fun _ => [] |}.
  - intros [i h | p] s; cbn [stratum_system System.rhs stratum_rhs stratum_deps].
    + destruct (Map.get nat_encoding i (index_rules_from 0 (rules prog))) as [r |];
        [|intros x Hbad; contradiction].
      rewrite (proj1 (ask_all_spec _ _ _)); cbn; rewrite app_nil_r; apply incl_refl.
    + intros x Hbad; contradiction.
  - intros [i h | p] s; cbn [stratum_system System.rhs stratum_rhs].
    + destruct (Map.get nat_encoding i (index_rules_from 0 (rules prog))) as [r |];
        [|intros x Hbad; contradiction].
      rewrite (proj2 (proj2 (ask_all_spec _ _ _))); cbn; apply incl_refl.
    + apply incl_refl.
Defined.

Definition encoded_eq_dec {X} (E : encoding X) (x y : X) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode E x) (encode E y)) as [Heq | Hne].
  - left; apply (encode_injective E); exact Heq.
  - right; intro Heq; subst y; contradiction.
Defined.

Lemma fill_values_member {X A} (E : encoding X) ps (s : X -> A) p :
  In p ps -> Map.get E p (fill_values E ps (map s ps)) = Some (s p).
Proof.
  induction ps as [|q ps IH]; intro Hin; [contradiction |].
  cbn [fill_values map]; destruct (encoded_eq_dec E p q) as [Heq | Hne].
  - subst q; apply Map.get_set_same.
  - rewrite Map.get_set_other by exact Hne; apply IH; cbn in Hin; intuition congruence.
Qed.

Lemma fill_values_absent {X A} (E : encoding X) ps (s : X -> A) p :
  ~ In p ps -> Map.get E p (fill_values E ps (map s ps)) = None.
Proof.
  induction ps as [|q ps IH]; intro Hout; cbn [fill_values map]; [apply Map.get_empty |].
  rewrite Map.get_set_other.
  - apply IH; intro Hin; apply Hout; now right.
  - intro Heq; subst q; apply Hout; now left.
Qed.

Lemma stratum_env_wf {P} (prog : program P) facts st lower k reads :
  (forall p, FinSet.wf tuple_encoding (lower p)) ->
  forall p, FinSet.wf tuple_encoding (stratum_env prog facts st lower k reads p).
Proof.
  intros Hlower p; unfold stratum_env; destruct (Nat.eqb (level st p) k).
  - destruct (Map.get (penc prog) p reads) as [s |];
      [exact (proj1 (proj2_sig s)) | apply Map.wf_empty].
  - apply Hlower.
Qed.

Lemma stratum_env_grows {P} (prog : program P) facts st lower k ds s1 s2 :
  fun_leb (relation_lattice prog facts) s1 s2 -> forall p,
  FinSet.subset tuple_encoding
    (stratum_env prog facts st lower k (fill_values (penc prog) ds (map s1 ds)) p)
    (stratum_env prog facts st lower k (fill_values (penc prog) ds (map s2 ds)) p) = true.
Proof.
  intros Hle p; unfold stratum_env; destruct (Nat.eqb (level st p) k).
  - destruct (in_dec (encoded_eq_dec (penc prog)) p ds) as [Hin | Hout].
    + rewrite !fill_values_member by exact Hin; apply Hle.
    + rewrite !fill_values_absent by exact Hout; apply set_subset_refl.
  - apply set_subset_refl.
Qed.

Lemma stratum_env_constant {P} (prog : program P) facts st lower k reads p :
  level st p <> k -> stratum_env prog facts st lower k reads p = lower p.
Proof.
  intro Hne; unfold stratum_env; apply Nat.eqb_neq in Hne; rewrite Hne; reflexivity.
Qed.

Lemma fire_rule_mono {P} (prog : program P) facts r env1 env2 :
  safe_rule r ->
  (forall p, FinSet.wf tuple_encoding (env1 p)) ->
  (forall p, FinSet.wf tuple_encoding (env2 p)) ->
  (forall a, In (LPos a) (body r) ->
    FinSet.subset tuple_encoding (env1 (pred a)) (env2 (pred a)) = true) ->
  (forall a, In (LNeg a) (body r) -> env1 (pred a) = env2 (pred a)) ->
  forall ts, FinSet.mem tuple_encoding ts (fire_rule prog facts r env1) = true ->
    FinSet.mem tuple_encoding ts (fire_rule prog facts r env2) = true.
Proof.
  intros Hsafe Hwf1 Hwf2 Hpos Hneg ts Hmem.
  apply (proj1 (fire_rule_exact_core prog facts r env1 Hsafe Hwf1 ts)) in Hmem.
  destruct Hmem as [Huniv [sigma [Hhead [Hpositives Hnegatives]]]].
  apply (proj2 (fire_rule_exact_core prog facts r env2 Hsafe Hwf2 ts)).
  split; [exact Huniv | exists sigma; split; [exact Hhead | split]].
  - intros a Ha; apply (set_member_subset tuple_encoding (env1 (pred a)) (env2 (pred a))
      (Hpos a Ha)); apply Hpositives; exact Ha.
  - intros a Ha; rewrite <- (Hneg a Ha); apply Hnegatives; exact Ha.
Qed.

Lemma rule_query_monotone {P} (prog : program P) facts st lower k r h ds :
  safe_rule r -> (forall p, FinSet.wf tuple_encoding (lower p)) ->
  (forall a, In (LNeg a) (body r) -> level st (pred a) <> k) ->
  monotone_query (relation_lattice prog facts)
    (ask_all ds (fun vs => Query.Ret (restrict prog facts h
      (fire_rule prog facts r
        (stratum_env prog facts st lower k (fill_values (penc prog) ds vs)))))).
Proof.
  intros Hsafe Hlower Hneg; split.
  - intros s1 s2 Hle; rewrite ! (proj1 (proj2 (ask_all_spec _ _ _))).
    cbn [Query.eval relation_lattice finite_powerset_lattice leb].
    set (env1 := stratum_env prog facts st lower k (fill_values (penc prog) ds (map s1 ds))).
    set (env2 := stratum_env prog facts st lower k (fill_values (penc prog) ds (map s2 ds))).
    assert (Hwf1 : forall p, FinSet.wf tuple_encoding (env1 p)).
    { apply stratum_env_wf; exact Hlower. }
    assert (Hwf2 : forall p, FinSet.wf tuple_encoding (env2 p)).
    { apply stratum_env_wf; exact Hlower. }
    apply FinSet.subset_spec.
    + exact (proj1 (proj2_sig (restrict prog facts h
        (fire_rule prog facts r env1)))).
    + intros ts Hmem.
      apply (proj1 (restrict_spec prog facts h ts _
        (fire_rule_wf prog facts env1 r Hwf1))) in Hmem.
      apply (proj2 (restrict_spec prog facts h ts _ (fire_rule_wf prog facts env2 r Hwf2))).
      split; [|exact (proj2 Hmem)]; eapply fire_rule_mono.
        -- exact Hsafe.
        -- exact Hwf1.
        -- exact Hwf2.
        -- intros a _; apply stratum_env_grows; exact Hle.
        -- intros a Ha; unfold env1, env2.
           rewrite !stratum_env_constant by (apply Hneg; exact Ha); reflexivity.
        -- exact (proj1 Hmem).
  - intros s1 s2 Hle x a Hin.
    rewrite (proj2 (proj2 (ask_all_spec _ _ _))) in Hin; contradiction.
Qed.

(** Fixing lower levels makes every compiled stratum monotone in its queried relations. *)
Theorem stratum_system_monotone {P} (prog : program P) (facts : list (ground_atom P))
  (st : stratification P) k lower :
  program_wf prog facts -> env_wf prog lower -> stratified prog st ->
  monotone_system (relation_lattice prog facts) (stratum_system prog facts st lower k).
Proof.
  intros [Hrules _] Hlower [_ Hstrat] [i h | p] Hc.
  - change (In (FromRule i h) (stratum_constraints prog facts st k)) in Hc.
    unfold stratum_constraints in Hc; apply in_app_iff in Hc; destruct Hc as [Hc | Hbad].
    + apply in_flat_map in Hc; destruct Hc as [[j r] [Hindexed Hc]].
      cbn [fst snd] in Hc; destruct (Nat.eqb (level st (pred (head r))) k) eqn:Hlevel;
        cbn in Hc; [|contradiction].
      destruct Hc as [Heq | Hbad]; [|contradiction]; injection Heq as Hi Hh; subst j h.
      pose proof (proj2 (numbered_rules_member 0 (rules prog) i r Hindexed)) as Hr.
      change (monotone_query (relation_lattice prog facts)
        (stratum_rhs prog facts st lower k (index_rules_from 0 (rules prog))
          (facts_by_pred prog facts) (FromRule i (pred (head r))))).
      unfold stratum_rhs; rewrite (index_rules_member 0 (rules prog) i r Hindexed).
      apply rule_query_monotone.
      * exact (proj1 (Hrules r Hr)).
      * intro q; exact (proj1 (Hlower q)).
      * intros a Ha; specialize (Hstrat r (LNeg a) Hr Ha); apply Nat.eqb_eq in Hlevel.
        cbn in Hstrat; lia.
    + apply in_map_iff in Hbad; destruct Hbad as [p [Hbad _]]; discriminate.
  - change (monotone_query (relation_lattice prog facts)
      (@Query.Ret P _
        (restrict prog facts p (relation_get (penc prog) (facts_by_pred prog facts) p)))).
    split.
    + intros s1 s2 Hle.
      apply (leb_refl (finite_powerset_laws tuple_encoding (herbrand prog facts))).
    + intros s1 s2 Hle x a Hbad; contradiction.
Qed.
