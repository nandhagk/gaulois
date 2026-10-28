(** * Rule syntax, stratification and indexed firing examples

    These examples distinguish successful joins, rejected negative cycles and unsafe syntax.
    For example, repeated occurrences of a variable must match the same encoded constant.
    Builds on: RulesSyntax, RulesStratify, RulesCompile and FixpointQuery. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesCompile.
Import List.ListNotations.

Definition copy_rule : rule nat := Rule (Atom 1 [TVar 0]) [LPos (Atom 0 [TVar 0])].

Definition negative_rule : rule nat := Rule (Atom 2 [TVar 0])
  [LPos (Atom 1 [TVar 0]); LNeg (Atom 3 [TVar 0])].

Definition unary_program : program nat := Program nat_encoding (fun _ => 1)
  [copy_rule; negative_rule].

Definition unary_facts : list (ground_atom nat) :=
  [(0, [2%positive]); (0, [3%positive]); (1, [2%positive]); (3, [3%positive])].

Definition unary_env (p : nat) : FinSet.t tuple :=
  if Nat.eqb p 3 then FinSet.of_list tuple_encoding [[3%positive]]
  else FinSet.of_list tuple_encoding [[2%positive]; [3%positive]].

(** A variable shared by the head and positive body satisfies range restriction. *)
Example copy_rule_safe : safe_rule copy_rule.
Proof.
  intros v [Hv | [a [Ha _]]].
  - exists (Atom 0 [TVar 0]); split; [now left | exact Hv].
  - cbn in Ha; destruct Ha as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

(** An unbound head variable is rejected by the safety proposition. *)
Example unsafe_head : ~ safe_rule (Rule (Atom 0 [TVar 0]) []).
Proof.
  intro Hsafe; destruct (Hsafe 0 (or_introl (or_introl eq_refl))) as [a [Hbad _]].
  contradiction.
Qed.

(** A variable occurring only under negation is also unsafe. *)
Example unsafe_negation :
  ~ safe_rule (Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 1 [TVar 0])]).
Proof.
  intro Hsafe.
  assert (Hnegative : exists a, In (LNeg a) [LNeg (Atom 1 [TVar 0])] /\ In 0 (atom_vars a)).
  { exists (Atom 1 [TVar 0]); cbn; auto. }
  destruct (Hsafe 0 (or_intror Hnegative)) as [a [Hbad _]].
  cbn in Hbad; destruct Hbad as [Hbad | Hbad]; [discriminate | contradiction].
Qed.

(** The producer accepts positive and negative dependencies with the required strict level. *)
Example stratify_negative_dependency :
  option_map (fun st => (level st 0, level st 1, level st 2, level st 3, count st))
    (stratify unary_program) = Some (0, 0, 1, 0, 2).
Proof.
  vm_compute; reflexivity.
Qed.

(** With no rules the global level bound still covers predicates outside the finite support. *)
Example stratify_empty :
  option_map (fun st => (level st 42, count st))
    (stratify (Program nat_encoding (fun _ => 0) [])) = Some (0, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Definition cycle_program : program nat := Program nat_encoding (fun _ => 1)
  [Rule (Atom 0 [TConst 2%positive]) [LNeg (Atom 1 [TConst 2%positive])];
   Rule (Atom 1 [TConst 2%positive]) [LPos (Atom 0 [TConst 2%positive])]].

(** A cycle containing a negative dependency has no computed stratification. *)
Example stratify_negative_cycle : stratify cycle_program = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition positive_cycle : program nat := Program nat_encoding (fun _ => 1)
  [copy_rule; Rule (Atom 0 [TVar 0]) [LPos (Atom 1 [TVar 0])]].

(** A positive cycle is accepted at one shared level. *)
Example stratify_positive_cycle :
  option_map (fun st => (level st 0, level st 1, count st)) (stratify positive_cycle) =
    Some (0, 0, 1).
Proof.
  vm_compute; reflexivity.
Qed.

(** Universe membership accepts an occurring predicate, arity and constant. *)
Example universe_accepts : in_universe unary_program unary_facts 2 [2%positive] = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Universe membership rejects unseen predicates, wrong arities and unseen constants. *)
Example universe_rejects :
  (in_universe unary_program unary_facts 9 [2%positive],
   in_universe unary_program unary_facts 2 [],
   in_universe unary_program unary_facts 2 [7%positive]) = (false, false, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Empty facts and relations produce no instances of a positive copy rule. *)
Example fire_empty_facts :
  FinSet.is_empty (fire_rule unary_program [] copy_rule (fun _ => FinSet.empty)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Positive firing keeps both matching unary tuples. *)
Example fire_positive :
  FinSet.mem tuple_encoding [2%positive]
    (fire_rule unary_program unary_facts copy_rule unary_env) = true /\
  FinSet.mem tuple_encoding [3%positive]
    (fire_rule unary_program unary_facts copy_rule unary_env) = true.
Proof.
  vm_compute; auto.
Qed.

(** Negative membership removes precisely the blocked head tuple. *)
Example fire_negative :
  (FinSet.mem tuple_encoding [2%positive]
     (fire_rule unary_program unary_facts negative_rule unary_env),
   FinSet.mem tuple_encoding [3%positive]
     (fire_rule unary_program unary_facts negative_rule unary_env)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Definition constant_rule : rule nat := Rule (Atom 0 [TConst 2%positive]) [].

(** A ground rule needs no extensional facts to fire. *)
Example fire_ground_without_facts : FinSet.mem tuple_encoding [2%positive]
  (fire_rule (Program nat_encoding (fun _ => 1) [constant_rule]) [] constant_rule
    (fun _ => FinSet.empty)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition repeated_rule : rule nat := Rule (Atom 1 [TVar 0])
  [LPos (Atom 0 [TVar 0; TVar 0]); LPos (Atom 2 [TVar 0; TConst 3%positive])].

Definition repeated_program : program nat :=
  Program nat_encoding (fun p => if Nat.eqb p 1 then 1 else 2) [repeated_rule].

Definition repeated_facts : list (ground_atom nat) := [(0, [2%positive; 2%positive])].

Definition repeated_env p : FinSet.t tuple :=
  if Nat.eqb p 0 then FinSet.of_list tuple_encoding
    [[2%positive; 2%positive]; [2%positive; 3%positive]; [3%positive; 3%positive]; [2%positive]]
  else FinSet.of_list tuple_encoding [[2%positive; 3%positive]; [3%positive; 2%positive]].

(** An indexed second join respects an existing variable binding and a constant argument. *)
Example fire_indexed_repeated_and_constant :
  (FinSet.mem tuple_encoding [2%positive]
     (fire_rule repeated_program repeated_facts repeated_rule repeated_env),
   FinSet.mem tuple_encoding [3%positive]
     (fire_rule repeated_program repeated_facts repeated_rule repeated_env)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Short tuples, unequal repeated variables and mismatching constants each reject a join. *)
Example fire_rejects_each_mismatch :
  (FinSet.is_empty (fire_rule repeated_program repeated_facts repeated_rule
     (fun p => if Nat.eqb p 0 then FinSet.of_list tuple_encoding [[2%positive]]
       else FinSet.of_list tuple_encoding [[2%positive; 3%positive]])),
   FinSet.is_empty (fire_rule repeated_program repeated_facts repeated_rule
     (fun _ => FinSet.of_list tuple_encoding [[2%positive; 3%positive]])),
   FinSet.is_empty (fire_rule repeated_program repeated_facts repeated_rule
     (fun _ => FinSet.of_list tuple_encoding [[2%positive; 2%positive]]))) = (true, true, true).
Proof.
  vm_compute; reflexivity.
Qed.

(** A nullary rule fires its empty tuple even when the constant alphabet is empty. *)
Example fire_nullary :
  let r := Rule (Atom 0 []) [] in
  FinSet.mem tuple_encoding []
    (fire_rule (Program nat_encoding (fun _ => 0) [r]) [] r (fun _ => FinSet.empty)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition unary_strata : stratification nat :=
  Stratification (fun p => if Nat.eqb p 2 then 1 else 0) 2.

Definition unary_assignment (p : nat) : relation unary_program unary_facts :=
  restrict unary_program unary_facts p (unary_env p).

Definition unary_system := stratum_system unary_program unary_facts unary_strata
  (fun _ => FinSet.empty) 0.

(** A compiled recursive query asks its distinct current-level positive predicate. *)
Example compile_reads : Query.reads (System.rhs unary_system (FromRule 0 1)) unary_assignment = [0].
Proof.
  vm_compute; reflexivity.
Qed.

(** Evaluating the compiled copy query returns its source tuple. *)
Example compile_fires : FinSet.mem tuple_encoding [2%positive]
  (proj1_sig (Query.eval (System.rhs unary_system (FromRule 0 1)) unary_assignment)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Facts contribute even to a predicate which also has rules. *)
Example compile_fact_contribution : FinSet.mem tuple_encoding [2%positive]
  (proj1_sig (Query.eval (System.rhs unary_system (FromFact 1)) unary_assignment)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Out-of-range rule identifiers return the empty relation without reading an unknown. *)
Example compile_missing_rule :
  (Query.reads (System.rhs unary_system (FromRule 99 1)) unary_assignment,
   FinSet.is_empty
     (proj1_sig (Query.eval (System.rhs unary_system (FromRule 99 1)) unary_assignment))) =
    ([], true).
Proof.
  vm_compute; reflexivity.
Qed.

(** A later stratum tests completed lower relations without querying them. *)
Example compile_lower_negation :
  let sys := stratum_system unary_program unary_facts unary_strata unary_env 1 in
  (Query.reads (System.rhs sys (FromRule 1 2)) unary_assignment,
   FinSet.mem tuple_encoding [2%positive]
     (proj1_sig (Query.eval (System.rhs sys (FromRule 1 2)) unary_assignment)),
   FinSet.mem tuple_encoding [3%positive]
     (proj1_sig (Query.eval (System.rhs sys (FromRule 1 2)) unary_assignment))) = ([], true, false).
Proof.
  vm_compute; reflexivity.
Qed.
