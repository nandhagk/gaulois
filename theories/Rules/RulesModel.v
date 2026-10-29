(** * Stratum derivations and the perfect model

    Each stratum is the inductive closure of its facts and rules over completed lower strata.
    For example, a recursive copy rule derives every fact reachable from its seed facts.
    Builds on: RulesSyntax, RulesStratify and RulesCompile. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesCompile.
Import List.ListNotations.

(** A stratum derives facts and rule instances using only completed lower negative relations. *)
Inductive derives {P} (prog : program P) (facts : list (ground_atom P)) (st : stratification P)
    (k : nat) (lower : ground_atom P -> Prop) : ground_atom P -> Prop :=
  | derive_fact : forall f, In f facts -> level st (fst f) = k ->
      derives prog facts st k lower f
  | derive_rule : forall r sigma, In r (rules prog) -> level st (pred (head r)) = k ->
      (forall a, In (LPos a) (body r) -> level st (pred a) < k -> lower (ground sigma a)) ->
      (forall a, In (LPos a) (body r) -> level st (pred a) = k ->
        derives prog facts st k lower (ground sigma a)) ->
      (forall a, In (LNeg a) (body r) -> ~ lower (ground sigma a)) ->
      derives prog facts st k lower (ground sigma (head r)).

Arguments derive_fact {P prog facts st k lower}.
Arguments derive_rule {P prog facts st k lower}.

(** The model below a bound combines precisely the completed strata preceding that bound. *)
Fixpoint model_below {P} (prog : program P) (facts : list (ground_atom P))
    (st : stratification P) (n : nat) : ground_atom P -> Prop :=
  match n with
  | O => fun _ => False
  | S k => fun f => model_below prog facts st k f \/
      derives prog facts st k (model_below prog facts st k) f
  end.

(** The perfect model contains the derivations from every stratum of the stratification. *)
Definition perfect_model {P} (prog : program P) (facts : list (ground_atom P))
    (st : stratification P) : ground_atom P -> Prop :=
  model_below prog facts st (count st).

(** Failed stratification selects the empty model. *)
Definition least_model {P} (prog : program P) (facts : list (ground_atom P)) :
    ground_atom P -> Prop :=
  match stratify prog with
  | Some st => perfect_model prog facts st
  | None => fun _ => False
  end.

(** Holding an atom means membership of its predicate and encoded argument tuple. *)
Definition holds {P} (M : ground_atom P -> Prop) (p : P) (args : tuple) : Prop := M (p, args).

Section Model.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : stratification P).

Lemma derives_level k lower f : derives prog facts st k lower f -> level st (fst f) = k.
Proof.
  intro Hderive; destruct Hderive; assumption.
Qed.

Lemma model_below_level n f : model_below prog facts st n f -> level st (fst f) < n.
Proof.
  induction n as [|n IH]; cbn; [contradiction |].
  intros [Hbelow | Hderive].
  - specialize (IH Hbelow); lia.
  - pose proof (derives_level n _ _ Hderive); lia.
Qed.

Lemma model_below_mono n m f : n <= m ->
  model_below prog facts st n f -> model_below prog facts st m f.
Proof.
  intro Hle; induction Hle as [|m Hle IH]; intro Hbelow.
  - exact Hbelow.
  - left; apply IH; exact Hbelow.
Qed.

Lemma model_below_stage n f : level st (fst f) < n ->
  (model_below prog facts st n f <->
    derives prog facts st (level st (fst f))
      (model_below prog facts st (level st (fst f))) f).
Proof.
  induction n as [|n IH]; intro Hlevel; [lia |].
  cbn [model_below]; split.
  - intros [Hbelow | Hderive].
    + apply IH; [eapply model_below_level; exact Hbelow | exact Hbelow].
    + pose proof (derives_level n _ _ Hderive) as Heq; rewrite Heq; exact Hderive.
  - intro Hderive; destruct (Nat.eq_dec (level st (fst f)) n) as [Heq | Hne].
    + right; rewrite Heq in Hderive; exact Hderive.
    + left; apply IH; [lia | exact Hderive].
Qed.

Lemma model_below_agrees n m f : level st (fst f) < n -> level st (fst f) < m ->
  (model_below prog facts st n f <-> model_below prog facts st m f).
Proof.
  intros Hn Hm; rewrite (model_below_stage n f Hn), (model_below_stage m f Hm).
  reflexivity.
Qed.

(** Every fact and satisfied rule belongs to the successfully stratified least model. *)
Theorem least_model_closed (r : rule P) : stratify prog = Some st ->
  (forall f, In f facts -> least_model prog facts f) /\
  forall sigma, In r (rules prog) ->
    (forall a, In (LPos a) (body r) -> least_model prog facts (ground sigma a)) ->
    (forall a, In (LNeg a) (body r) -> ~ least_model prog facts (ground sigma a)) ->
    least_model prog facts (ground sigma (head r)).
Proof.
  intro Hstratify; pose proof (stratify_sound prog st Hstratify) as [Hcount Hstrat].
  unfold least_model; rewrite Hstratify; unfold perfect_model; split.
  - intros f Hfact; apply (model_below_stage (count st) f (Hcount (fst f))).
    apply derive_fact; [exact Hfact | reflexivity].
  - intros sigma Hr Hpos Hneg.
    apply (model_below_stage (count st) (ground sigma (head r)) (Hcount _)).
    apply derive_rule with (r := r) (sigma := sigma); [exact Hr | reflexivity | | |].
    + intros a Ha Hlt; apply (model_below_agrees (count st) _ (ground sigma a));
        [apply Hcount | exact Hlt | apply Hpos; exact Ha].
    + intros a Ha Heq; pose proof (Hpos a Ha) as Hmember.
      apply (model_below_stage (count st) (ground sigma a) (Hcount _)) in Hmember.
      cbn [ground fst] in Hmember; rewrite Heq in Hmember; exact Hmember.
    + intros a Ha Hbelow; apply (Hneg a Ha).
      eapply model_below_mono; [|exact Hbelow]; apply Nat.lt_le_incl; apply Hcount.
Qed.

Lemma fact_universe : program_wf prog facts -> forall f, In f facts ->
  in_universe prog facts (fst f) (snd f) = true.
Proof.
  intros [_ Hfacts] f Hf; apply in_universe_spec; split.
  - unfold preds; apply FinSet.of_list_spec, in_app_iff; right; apply in_map; exact Hf.
  - split; [apply Hfacts; exact Hf |].
    intros c Hc; unfold constants; apply FinSet.of_list_spec, in_app_iff; right.
    apply in_flat_map; exists f; split; assumption.
Qed.

Lemma head_universe (r : rule P) sigma : program_wf prog facts -> In r (rules prog) ->
  (forall a, In (LPos a) (body r) ->
    in_universe prog facts (pred a) (map (inst sigma) (args a)) = true) ->
  in_universe prog facts (pred (head r)) (map (inst sigma) (args (head r))) = true.
Proof.
  intros [Hrules _] Hr Hpos; destruct (Hrules r Hr) as [Hsafe [Harity _]].
  apply in_universe_spec; split.
  - unfold preds; apply FinSet.of_list_spec, in_app_iff; left; apply in_flat_map.
    exists r; split; [exact Hr | unfold rule_predicates; now left].
  - split; [rewrite length_map; exact Harity |].
    intros c Hc; apply in_map_iff in Hc; destruct Hc as [[v | d] [Heq Hterm]].
    + cbn [inst] in Heq; subst c.
      assert (Hv : In v (atom_vars (head r))) by (apply atom_vars_spec; exact Hterm).
      destruct (Hsafe v (or_introl Hv)) as [a [Ha Hva]].
      pose proof (proj2 (proj2 (proj1 (in_universe_spec prog facts _ _) (Hpos a Ha)))) as Hcs.
      apply Hcs; apply in_map_iff; exists (TVar v); split; [reflexivity |].
      apply atom_vars_spec; exact Hva.
    + cbn [inst] in Heq; subst c; unfold constants; apply FinSet.of_list_spec.
      apply in_app_iff; left; apply in_flat_map; exists r; split; [exact Hr |].
      apply in_app_iff; left; unfold atom_constants; apply in_flat_map.
      exists (TConst d); split; [exact Hterm | now left].
Qed.

Lemma derives_universe k lower : program_wf prog facts -> stratified prog st ->
  (forall f, lower f -> in_universe prog facts (fst f) (snd f) = true) ->
  forall f, derives prog facts st k lower f ->
    in_universe prog facts (fst f) (snd f) = true.
Proof.
  intros Hwf [_ Hstrat] Hlower f Hderive.
  induction Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame IH Hneg].
  - apply fact_universe; assumption.
  - apply head_universe; [exact Hwf | exact Hr |].
    intros a Ha; pose proof (Hstrat r (LPos a) Hr Ha) as Hle; cbn in Hle.
    destruct (Nat.eq_dec (level st (pred a)) k) as [Heq | Hne].
    + exact (IH a Ha Heq).
    + apply (Hlower (ground sigma a)); apply Hlow; [exact Ha | lia].
Qed.

(** Safety ensures every model atom uses a declared arity and program constants. *)
Theorem model_constants : program_wf prog facts -> stratified prog st ->
  forall n a, model_below prog facts st n a ->
    in_universe prog facts (fst a) (snd a) = true.
Proof.
  intros Hwf Hstrat n; induction n as [|n IH]; intros a Hmodel; [contradiction |].
  destruct Hmodel as [Hbelow | Hderive].
  - apply IH; exact Hbelow.
  - eapply derives_universe; [exact Hwf | exact Hstrat | exact IH | exact Hderive].
Qed.

End Model.
