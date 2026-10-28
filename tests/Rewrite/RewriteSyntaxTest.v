(** * Sorted rewriting examples

    Small signatures exercise substitution, guarded equality and strict partial interpretation.
    For example, a guarded identity rule rewrites an application inside a variadic sum.
    Builds on: RewriteSyntax, RewriteRules, RewriteEquality and Rocq Stdlib naturals and lists. *)

From Stdlib Require Import Arith Bool List.
From Gaulois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality.
Import List.ListNotations.

(** The sum is variadic, while the other operators have fixed shapes. *)
Inductive rewrite_test_op : Type :=
  | TestZero
  | TestId
  | TestSum
  | TestOrdered
  | TestPartial.

(** True and false are distinct sorts; variable one has the latter sort. *)
Definition rewrite_test_signature : rw_signature rewrite_test_op bool nat :=
  {| rw_var_sort := fun v => Some (negb (Nat.eqb v 1));
     rw_operator_shape := fun op ss s =>
       s && match op with
       | TestZero => match ss with [] => true | _ => false end
       | TestId | TestPartial => match ss with [true] => true | _ => false end
       | TestSum => forallb (fun s => s) ss
       | TestOrdered => match ss with [true; true] => true | _ => false end
       end |}.

(** Variable three is absent, and the partial operator is undefined at zero. *)
Definition rewrite_test_semantics : rw_semantics rewrite_test_op bool nat nat :=
  {| rw_var_value := fun v => if Nat.eqb v 3 then None else Some v;
     rw_eval_op := fun op xs =>
       match op, xs with
       | TestZero, [] => Some 0
       | TestId, [x] => Some x
       | TestSum, _ => Some (fold_right Nat.add 0 xs)
       | TestOrdered, [x; y] => Some (10 * x + y)
       | TestPartial, [S x] => Some x
       | _, _ => None
       end |}.

(** Admissible interpretations may vary except that the identity operator returns its input. *)
Definition rewrite_test_admissible (sem : rw_semantics rewrite_test_op bool nat nat) : Prop :=
  forall c, rw_eval_op sem TestId [c] = Some c.

Example rewrite_admissible_inhabited : rewrite_test_admissible rewrite_test_semantics.
Proof.
  intro c; reflexivity.
Qed.

Example rewrite_empty_application :
  rw_denote rewrite_test_semantics (RWApp true TestZero []) = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_variadic_empty :
  rw_denote rewrite_test_semantics (RWApp true TestSum []) = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_variadic_many :
  rw_denote rewrite_test_semantics
    (RWApp true TestSum [RWVar true 0; RWVar true 2; RWVar true 4]) = Some 6.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_argument_order :
  rw_denote rewrite_test_semantics
    (RWApp true TestOrdered [RWVar true 2; RWVar true 4]) = Some 24.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_partial_defined :
  rw_denote rewrite_test_semantics (RWApp true TestPartial [RWVar true 2]) = Some 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_partial_undefined :
  rw_denote rewrite_test_semantics (RWApp true TestPartial [RWVar true 0]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_strict_children :
  rw_denote rewrite_test_semantics
    (RWApp true TestSum [RWVar true 2; RWVar true 3; RWVar true 4]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_undefined_options_equal :
  rw_denote rewrite_test_semantics (RWApp true TestPartial [RWVar true 0]) =
  rw_denote rewrite_test_semantics (RWVar true 3).
Proof.
  vm_compute; reflexivity.
Qed.

(** The single declared hole can be repeated in either rule side. *)
Definition rewrite_test_holes (_ : unit) : option bool := Some true.

Definition rewrite_test_sub : rw_substitution rewrite_test_op bool nat unit :=
  fun _ => Some (RWVar true 0).

Definition rewrite_test_other_sub : rw_substitution rewrite_test_op bool nat unit :=
  fun _ => Some (RWVar true 2).

Definition rewrite_test_missing_sub : rw_substitution rewrite_test_op bool nat unit :=
  fun _ => None.

Definition rewrite_test_wrong_sub : rw_substitution rewrite_test_op bool nat unit :=
  fun _ => Some (RWVar false 1).

Example rewrite_repeated_hole :
  rw_instantiate rewrite_test_other_sub
    (RWPApp true TestSum [RWHole true tt; RWHole true tt]) =
  Some (RWApp true TestSum [RWVar true 2; RWVar true 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_free_variable_preserved :
  rw_instantiate rewrite_test_other_sub
    (RWPApp true TestSum [RWPVar true 0; RWHole true tt]) =
  Some (RWApp true TestSum [RWVar true 0; RWVar true 2]).
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_missing_hole :
  rw_instantiate rewrite_test_missing_sub
    (RWPApp true TestSum [RWPVar true 0; RWHole true tt]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_missing_sub_keeps_literal :
  rw_instantiate rewrite_test_missing_sub (RWPVar true 0) = Some (RWVar true 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_empty_instantiation :
  rw_instantiate rewrite_test_missing_sub (RWPApp true TestZero []) =
  Some (RWApp true TestZero []).
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_sub_checked :
  rw_sub_typed rewrite_test_signature rewrite_test_holes rewrite_test_sub.
Proof.
  intros [] s Hsort.
  change (Some true = Some s) in Hsort; injection Hsort as Hsort; subst s.
  exists (RWVar true 0); split; [reflexivity|split; [reflexivity|constructor; reflexivity]].
Qed.

Example rewrite_typed_repeated_instantiation :
  exists t, rw_instantiate rewrite_test_sub
      (RWPApp true TestSum [RWHole true tt; RWHole true tt]) = Some t /\
    rw_typed rewrite_test_signature t /\ rw_sort t = true.
Proof.
  apply (rw_instantiate_typed rewrite_test_signature rewrite_test_holes rewrite_test_sub
    (RWPApp true TestSum [RWHole true tt; RWHole true tt])).
  - apply rwp_typed_app.
    + constructor; [constructor; reflexivity|].
      constructor; [constructor; reflexivity|constructor].
    + reflexivity.
  - exact rewrite_sub_checked.
Qed.

Example rewrite_variadic_empty_typed :
  rw_typed rewrite_test_signature (RWApp true TestSum []).
Proof.
  apply rw_typed_app; [constructor|reflexivity].
Qed.

Example rewrite_fixed_arity_rejected :
  rw_operator_shape rewrite_test_signature TestId [] true = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_sort_mismatch :
  ~ rw_sub_typed rewrite_test_signature rewrite_test_holes rewrite_test_wrong_sub.
Proof.
  intro Hsub.
  destruct (Hsub tt true eq_refl) as [t [Hinst [Hsort Htyped]]].
  change (Some (RWVar false 1) = Some t) in Hinst.
  injection Hinst as Hterm; subst t; discriminate Hsort.
Qed.

Example rewrite_missing_sub_rejected :
  ~ rw_sub_typed rewrite_test_signature rewrite_test_holes rewrite_test_missing_sub.
Proof.
  intro Hsub.
  destruct (Hsub tt true eq_refl) as [t [Hinst Htyped]].
  discriminate Hinst.
Qed.

Example rewrite_operator_sort_mismatch :
  ~ rw_typed rewrite_test_signature (RWApp true TestId [RWVar false 1]).
Proof.
  intro Htyped.
  destruct (rw_typed_app_inv rewrite_test_signature true TestId [RWVar false 1] Htyped)
    as [Hargs Hshape].
  discriminate Hshape.
Qed.

(** This guard accepts only the substitution of the literal free variable zero. *)
Definition rewrite_test_rule : rw_rule rewrite_test_op bool nat unit :=
  {| rw_holes := [tt];
     rw_hole_sort := rewrite_test_holes;
     rw_lhs := RWPApp true TestId [RWHole true tt];
     rw_rhs := RWHole true tt;
     rw_condition := fun sub =>
       match sub tt with
       | Some (RWVar _ v) => Nat.eqb v 0
       | _ => false
       end |}.

Example rewrite_rule_guard_passes : rw_condition rewrite_test_rule rewrite_test_sub = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_rule_guard_fails : rw_condition rewrite_test_rule rewrite_test_other_sub = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example rewrite_rule_well_formed : rw_rule_wf rewrite_test_signature rewrite_test_rule.
Proof.
  split.
  - constructor; [intro Hin; inversion Hin|constructor].
  - split.
    + intros []; split; intro Hdomain.
      * exists true; reflexivity.
      * now left.
    + split.
      * apply rwp_typed_app.
        -- constructor; [constructor; reflexivity|constructor].
        -- reflexivity.
      * split; [constructor; reflexivity|reflexivity].
Qed.

Example rewrite_rule_sound :
  rw_rule_sound rewrite_test_signature rewrite_test_admissible rewrite_test_rule.
Proof.
  intros sub l u Hsub Hguard Hlhs Hrhs.
  change (sub tt = Some u) in Hrhs.
  change (rw_instantiate sub (RWPApp true TestId [RWHole true tt]) = Some l) in Hlhs.
  cbn [rw_instantiate] in Hlhs.
  rewrite Hrhs in Hlhs; injection Hlhs as Hlhs; subst l.
  intros sem Hsem.
  rewrite rw_denote_app, rw_denote_args_cons.
  destruct (rw_denote sem u) as [c|] eqn:Hvalue.
  - cbn [rw_denote_args]; exact (Hsem c).
  - reflexivity.
Qed.

Example rewrite_guarded_rule_applied :
  rw_equal rewrite_test_signature rewrite_test_admissible [rewrite_test_rule]
    (RWApp true TestId [RWVar true 0]) (RWVar true 0).
Proof.
  apply rw_eq_rule with (r := rewrite_test_rule) (sub := rewrite_test_sub).
  - now left.
  - exact rewrite_sub_checked.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Example rewrite_rule_under_application :
  rw_equal rewrite_test_signature rewrite_test_admissible [rewrite_test_rule]
    (RWApp true TestSum [RWApp true TestId [RWVar true 0]; RWVar true 2])
    (RWApp true TestSum [RWVar true 0; RWVar true 2]).
Proof.
  apply rw_eq_app.
  constructor; [exact rewrite_guarded_rule_applied|].
  constructor; [apply rw_eq_refl|constructor].
Qed.

Example rewrite_applied_rule_semantics :
  rw_equiv rewrite_test_admissible
    (RWApp true TestSum [RWApp true TestId [RWVar true 0]; RWVar true 2])
    (RWApp true TestSum [RWVar true 0; RWVar true 2]).
Proof.
  apply (rw_equal_sound rewrite_test_signature rewrite_test_admissible [rewrite_test_rule]).
  - constructor; [exact rewrite_rule_sound|constructor].
  - exact rewrite_rule_under_application.
Qed.

Example rewrite_reversed_rule_typed :
  rw_typed rewrite_test_signature (RWApp true TestId [RWVar true 0]) /\
    rw_sort (RWVar true 0 : rw_term rewrite_test_op bool nat) =
    rw_sort (RWApp true TestId [RWVar true 0]).
Proof.
  apply (rw_equal_typed rewrite_test_signature rewrite_test_admissible [rewrite_test_rule]).
  - constructor; [exact rewrite_rule_well_formed|constructor].
  - constructor; reflexivity.
  - apply rw_eq_sym; exact rewrite_guarded_rule_applied.
Qed.

Example rewrite_transitive_round_trip :
  rw_equal rewrite_test_signature rewrite_test_admissible [rewrite_test_rule]
    (RWApp true TestId [RWVar true 0]) (RWApp true TestId [RWVar true 0]).
Proof.
  apply rw_eq_trans with (u := RWVar true 0).
  - exact rewrite_guarded_rule_applied.
  - apply rw_eq_sym; exact rewrite_guarded_rule_applied.
Qed.
