(** * Perfect-model and total-solver examples

    These examples exercise recursive seeds, completed-stratum negation and rejected cycles.
    For example, a fact at a recursive predicate propagates around a positive dependency cycle.
    Builds on: RulesModel, RulesSolve and RulesCompile. *)

From Stdlib Require Import List Bool PeanoNat PArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointCheck.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesModel RulesSolve.
Import List.ListNotations.

Definition empty_program : program nat := Program nat_encoding (fun _ => 1) [].

Definition chosen_strata (prog : program nat) : stratification nat :=
  match stratify prog with
  | Some st => st
  | None => Stratification (fun _ => 0) 1
  end.

(** Empty input has a stratum, and its compiled system has no constraints. *)
Example empty_system :
  option_map count (stratify empty_program) = Some 1 /\
  stratum_constraints empty_program [] (chosen_strata empty_program) 0 = [].
Proof.
  vm_compute; auto.
Qed.

(** Total solving succeeds on empty input and represents an empty relation at every predicate. *)
Example empty_solver : exists db, solve_program empty_program [] = Some db /\
  forall p ts, db_holds empty_program db p ts = false.
Proof.
  assert (Hwf : program_wf empty_program []).
  { split; intros x Hbad; contradiction. }
  assert (Hstrat : stratify empty_program = Some (chosen_strata empty_program)).
  { vm_compute; reflexivity. }
  destruct (solve_program_exact empty_program [] Hwf
    (ex_intro _ _ (stratify_sound _ _ Hstrat))) as [db [Hsolve [_ Hexact]]].
  exists db; split; [exact Hsolve | intros p ts].
  unfold db_holds; destruct (FinSet.mem tuple_encoding ts (rel_of empty_program db p))
    eqn:Hmem; [|reflexivity].
  apply (proj1 (Hexact p ts)) in Hmem.
  pose proof (model_constants empty_program [] (chosen_strata empty_program) Hwf
    (stratify_sound _ _ Hstrat) 1 (p, ts)) as Hconstant.
  unfold least_model in Hmem; rewrite Hstrat in Hmem; apply Hconstant in Hmem.
  unfold in_universe, preds in Hmem.
  apply andb_true_iff in Hmem as [Hmem _]; apply andb_true_iff in Hmem as [Hmem _].
  change (FinSet.mem nat_encoding p FinSet.empty = true) in Hmem.
  rewrite FinSet.mem_empty in Hmem; discriminate.
Qed.

Definition copy_atom (p : nat) : atom nat := Atom p [TVar 0].
Definition copy_between (h b : nat) : rule nat := Rule (copy_atom h) [LPos (copy_atom b)].
Definition recursive_program : program nat :=
  Program nat_encoding (fun _ => 1) [copy_between 0 1; copy_between 1 0].
Definition recursive_facts : list (ground_atom nat) := [(0, [2%positive])].

(** The recursive cycle is accepted at one level, including its derived-predicate fact target. *)
Example recursive_constraints :
  option_map count (stratify recursive_program) = Some 1 /\
  stratum_constraints recursive_program recursive_facts (chosen_strata recursive_program) 0 =
    [FromRule 0 0; FromRule 1 1; FromFact 0].
Proof.
  vm_compute; auto.
Qed.

(** Each copy rule binds its head variable through its sole positive literal. *)
Example copy_between_safe h b : safe_rule (copy_between h b).
Proof.
  intros v [Hv | [a [Ha _]]].
  - exists (copy_atom b); split; [now left | exact Hv].
  - cbn in Ha; destruct Ha as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

(** Both cycle rules and the seed have the program's declared unary arity. *)
Example recursive_wf : program_wf recursive_program recursive_facts.
Proof.
  split.
  - intros r [Heq | [Heq | Hbad]]; [subst r | subst r | contradiction];
      split; [apply copy_between_safe | | apply copy_between_safe |];
      split; [reflexivity | intros l [Heq | Hbad]; [subst l; reflexivity | contradiction]
        | reflexivity | intros l [Heq | Hbad]; [subst l; reflexivity | contradiction]].
  - intros f [Heq | Hbad]; [subst f; reflexivity | contradiction].
Qed.

(** The chosen recursive strata are exactly the producer's successful result. *)
Example recursive_stratified :
  stratify recursive_program = Some (chosen_strata recursive_program).
Proof.
  vm_compute; reflexivity.
Qed.

(** A fact at a predicate which also has a rule belongs to the least model. *)
Example recursive_seed_model : least_model recursive_program recursive_facts (0, [2%positive]).
Proof.
  apply (proj1 (least_model_closed recursive_program recursive_facts
    (chosen_strata recursive_program) (copy_between 0 1) recursive_stratified)).
  now left.
Qed.

(** The seed propagates to the other predicate through a recursive copy rule. *)
Example recursive_derived_model : least_model recursive_program recursive_facts (1, [2%positive]).
Proof.
  change (least_model recursive_program recursive_facts
    (ground (fun _ => 2%positive) (head (copy_between 1 0)))).
  apply (proj2 (least_model_closed recursive_program recursive_facts
    (chosen_strata recursive_program) (copy_between 1 0) recursive_stratified)).
  - now right; left.
  - intros a [Heq | Hbad]; [|contradiction].
    injection Heq as Heq; subst a; exact recursive_seed_model.
  - intros a [Hbad | Hbad]; [discriminate | contradiction].
Qed.

(** The total engine contains the seed and its consequence without creating a new constant. *)
Example recursive_solver : exists db,
  solve_program recursive_program recursive_facts = Some db /\
  db_holds recursive_program db 0 [2%positive] = true /\
  db_holds recursive_program db 1 [2%positive] = true /\
  db_holds recursive_program db 1 [3%positive] = false.
Proof.
  destruct (solve_program_exact recursive_program recursive_facts recursive_wf
    (ex_intro _ _ (stratify_sound _ _ recursive_stratified))) as [db [Hsolve [_ Hexact]]].
  exists db; split; [exact Hsolve | split].
  - apply (proj2 (Hexact _ _)); exact recursive_seed_model.
  - split; [apply (proj2 (Hexact _ _)); exact recursive_derived_model |].
    unfold db_holds; destruct (FinSet.mem tuple_encoding [3%positive]
      (rel_of recursive_program db 1)) eqn:Hmem; [|reflexivity].
    apply (proj1 (Hexact _ _)) in Hmem; unfold least_model in Hmem.
    rewrite recursive_stratified in Hmem.
    apply (model_constants recursive_program recursive_facts _ recursive_wf
      (stratify_sound _ _ recursive_stratified)) in Hmem.
    vm_compute in Hmem; discriminate.
Qed.

Definition negation_rule : rule nat := Rule (copy_atom 2)
  [LPos (copy_atom 1); LNeg (copy_atom 3)].
Definition negation_program : program nat := Program nat_encoding (fun _ => 1) [negation_rule].
Definition negation_facts : list (ground_atom nat) :=
  [(1, [2%positive]); (1, [3%positive]); (3, [3%positive])].

(** Negation places its head above both input relations and reads no unfinished lower value. *)
Example negation_strata :
  option_map (fun st => (level st 1, level st 2, level st 3, count st))
    (stratify negation_program) = Some (0, 1, 0, 2).
Proof.
  vm_compute; reflexivity.
Qed.

(** The negated variable is also bound by the positive input, so the program is safe. *)
Example negation_wf : program_wf negation_program negation_facts.
Proof.
  split.
  - intros r [Heq | Hbad]; [subst r | contradiction]; split.
    + intros v [Hv | [a [Ha Hv]]]; exists (copy_atom 1); split; try now left.
      * exact Hv.
      * destruct Ha as [Hbad | [Heq | Hbad]]; [discriminate | | contradiction].
        injection Heq as Heq; subst a; exact Hv.
    + split; [reflexivity |].
      intros l [Heq | [Heq | Hbad]]; [subst l; reflexivity | subst l; reflexivity |
        contradiction].
  - intros f [Heq | [Heq | [Heq | Hbad]]]; subst; try reflexivity; contradiction.
Qed.

(** The producer succeeds on this program with its single negative dependency. *)
Example negation_stratified : stratify negation_program = Some (chosen_strata negation_program).
Proof.
  vm_compute; reflexivity.
Qed.

Definition negation_lower (p : nat) : FinSet.t tuple :=
  relation_get (penc negation_program) (facts_by_pred negation_program negation_facts) p.

(** The completed first stratum consists exactly of the extensional input facts. *)
Example negation_lower_represents : represents negation_lower
  (model_below negation_program negation_facts (chosen_strata negation_program) 1).
Proof.
  split; [apply facts_by_pred_wf | intros p ts; unfold negation_lower].
  rewrite facts_by_pred_exact; cbn [model_below]; split.
  - intro Hfact; right; apply derive_fact; [exact Hfact |].
    destruct Hfact as [Heq | [Heq | [Heq | Hbad]]]; [| | |contradiction];
      injection Heq as Hp Hts; subst p ts; vm_compute; reflexivity.
  - intros [Hbad | Hderive]; [contradiction |].
    destruct Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame Hneg].
    + exact Hfact.
    + destruct Hr as [Heq | Hbad]; [subst r | contradiction].
      vm_compute in Hlevel; discriminate.
Qed.

(** An absent tuple in the lower negative relation permits the corresponding head derivation. *)
Example negation_allowed_derives :
  derives negation_program negation_facts (chosen_strata negation_program) 1
    (model_below negation_program negation_facts (chosen_strata negation_program) 1)
    (2, [2%positive]).
Proof.
  change (derives negation_program negation_facts (chosen_strata negation_program) 1
    (model_below negation_program negation_facts (chosen_strata negation_program) 1)
    (ground (fun _ => 2%positive) (head negation_rule))).
  apply derive_rule with (r := negation_rule) (sigma := fun _ => 2%positive).
  - now left.
  - vm_compute; reflexivity.
  - intros a [Heq | [Hbad | Hbad]] Hlt; [|discriminate | contradiction].
    injection Heq as Heq; subst a; apply (proj1 (proj2 negation_lower_represents _ _)).
    vm_compute; reflexivity.
  - intros a [Heq | [Hbad | Hbad]] Hlevel; [|discriminate | contradiction].
    injection Heq as Heq; subst a; vm_compute in Hlevel; discriminate.
  - intros a [Hbad | [Heq | Hbad]] Hbelow; [discriminate | | contradiction].
    injection Heq as Heq; subst a; apply (proj2 (proj2 negation_lower_represents _ _)) in Hbelow.
    vm_compute in Hbelow; discriminate.
Qed.

(** A tuple present in the completed lower negative relation cannot be derived at the head. *)
Example negation_blocked_derives :
  ~ derives negation_program negation_facts (chosen_strata negation_program) 1
    (model_below negation_program negation_facts (chosen_strata negation_program) 1)
    (2, [3%positive]).
Proof.
  intro Hderive; remember (2, [3%positive]) as f eqn:Hf in Hderive.
  revert Hf; destruct Hderive as [f Hfact Hlevel | r sigma Hr Hlevel Hlow Hsame Hneg];
    intro Hf.
  - destruct Hfact as [Heq | [Heq | [Heq | Hbad]]]; [| | |contradiction];
      subst f; vm_compute in Hlevel; discriminate.
  - destruct Hr as [Heq | Hbad]; [subst r | contradiction].
    change ((2, [sigma 0]) = (2, [3%positive])) in Hf.
    assert (Hsigma : sigma 0 = 3%positive) by congruence.
    apply (Hneg (copy_atom 3) (or_intror (or_introl eq_refl))).
    change (model_below negation_program negation_facts (chosen_strata negation_program) 1
      (3, [sigma 0])); rewrite Hsigma.
    apply (proj1 (proj2 negation_lower_represents _ _)); vm_compute; reflexivity.
Qed.

(** The perfect model accepts the unblocked tuple and excludes the blocked tuple. *)
Example negation_model : least_model negation_program negation_facts (2, [2%positive]) /\
  ~ least_model negation_program negation_facts (2, [3%positive]).
Proof.
  unfold least_model; rewrite negation_stratified; split.
  - change (model_below negation_program negation_facts (chosen_strata negation_program) 2
      (2, [2%positive])); right; exact negation_allowed_derives.
  - intro Hmodel; change (model_below negation_program negation_facts
      (chosen_strata negation_program) 2 (2, [3%positive])) in Hmodel.
    apply (proj1 (model_below_stage negation_program negation_facts
      (chosen_strata negation_program) 2 (2, [3%positive]) ltac:(vm_compute; auto))) in Hmodel.
    apply negation_blocked_derives; exact Hmodel.
Qed.

(** The integrated total solver makes exactly the completed-stratum negation decision. *)
Example negation_solver : exists db, solve_program negation_program negation_facts = Some db /\
  db_holds negation_program db 2 [2%positive] = true /\
  db_holds negation_program db 2 [3%positive] = false.
Proof.
  destruct (solve_program_exact negation_program negation_facts negation_wf
    (ex_intro _ _ (stratify_sound _ _ negation_stratified))) as [db [Hsolve [_ Hexact]]].
  exists db; split; [exact Hsolve | split].
  - apply (proj2 (Hexact _ _)); exact (proj1 negation_model).
  - unfold db_holds; destruct (FinSet.mem tuple_encoding [3%positive]
      (rel_of negation_program db 2)) eqn:Hmem; [|reflexivity].
    exfalso; apply (proj2 negation_model); apply (proj1 (Hexact _ _)); exact Hmem.
Qed.

Definition negation_candidate (p : nat) : relation negation_program negation_facts :=
  restrict negation_program negation_facts p
    (if Nat.eqb p 2 then FinSet.of_list tuple_encoding [[2%positive]] else FinSet.empty).

(** A nontrivial completed-negation stratum is accepted by the full post-solution checker. *)
Example negation_post_check : check_post (relation_lattice negation_program negation_facts)
  (stratum_system negation_program negation_facts (chosen_strata negation_program)
    negation_lower 1) negation_candidate = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition failure_program : program nat := Program nat_encoding (fun _ => 1)
  [Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 0 [TConst 2%positive])]].

(** A negative self-cycle is rejected by stratification and by the program solver. *)
Example failure_solver : stratify failure_program = None /\ solve_program failure_program [] = None.
Proof.
  vm_compute; auto.
Qed.
