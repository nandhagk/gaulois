(** * Semi-naive solver computations

    These examples compute observable relations with both indexed join strategies.
    For example, nonlinear transitive closure combines a frontier path with an older path.
    Builds on: RulesDelta and RulesSyntax. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Gaulois.Rules Require Import RulesSyntax RulesStratify RulesJoin RulesSolve RulesDelta.
Import List.ListNotations.

Definition delta_observe strategy (prog : program nat) facts queries :=
  option_map (fun db => map (fun f => db_holds prog db (fst f) (snd f)) queries)
    (solve_program_delta strategy prog facts).

Lemma delta_observe_bounded strategy (prog : program nat) facts queries result :
  option_map (fun db => map (fun f => db_holds prog db (fst f) (snd f)) queries)
    (delta_bounded_program strategy prog facts 8%positive) = Some result ->
  delta_observe strategy prog facts queries = Some result.
Proof.
  destruct (delta_bounded_program strategy prog facts 8%positive) as [db |] eqn:Hdb;
    cbn; [|discriminate].
  intro Hresult; unfold delta_observe.
  rewrite (delta_bounded_program_agrees strategy prog facts 8%positive db Hdb); exact Hresult.
Qed.

Definition delta_empty : program nat := Program nat_encoding (fun _ => 1) [].

(** Both strategies terminate with no facts on the empty program. *)
Example delta_empty_computes strategy :
  delta_observe strategy delta_empty [] [(0, [1%positive])] = Some [false].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_unary (p : nat) : atom nat := Atom p [TVar 0].
Definition delta_copy (h b : nat) : rule nat := Rule (delta_unary h) [LPos (delta_unary b)].
Definition delta_recursive : program nat :=
  Program nat_encoding (fun _ => 1) [delta_copy 0 1; delta_copy 1 0].

(** A fact in a recursive cycle propagates exactly once to each predicate. *)
Example delta_recursive_computes strategy :
  delta_observe strategy delta_recursive [(0, [2%positive])]
    [(0, [2%positive]); (1, [2%positive]); (1, [3%positive])] = Some [true; true; false].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_path x y := Atom 0 [TVar x; TVar y].
Definition delta_transitive : program nat :=
  Program nat_encoding (fun _ => 2)
    [Rule (delta_path 0 2) [LPos (delta_path 0 1); LPos (delta_path 1 2)]].
Definition delta_edges : list (ground_atom nat) :=
  [(0, [1%positive; 2%positive]); (0, [2%positive; 3%positive]);
   (0, [3%positive; 4%positive])].

(** Two recursive occurrences require mixed accumulated/frontier variants to reach length three. *)
Example delta_multiple_recursive_computes strategy :
  delta_observe strategy delta_transitive delta_edges
    [(0, [1%positive; 4%positive]); (0, [4%positive; 1%positive]);
     (0, [1%positive; 3%positive])] = Some [true; false; true].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

(** Duplicate seeds and duplicate rule firings do not change membership or prevent termination. *)
Example delta_duplicates_computes strategy :
  delta_observe strategy delta_recursive [(0, [2%positive]); (0, [2%positive])]
    [(0, [2%positive]); (1, [2%positive])] = Some [true; true].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_ground_fact : program nat :=
  Program nat_encoding (fun _ => 1) [Rule (Atom 0 [TConst 5%positive]) []].

(** Nonrecursive rules, including an empty body, initialize the frontier. *)
Example delta_nonrecursive_computes strategy :
  delta_observe strategy delta_ground_fact []
    [(0, [5%positive]); (0, [6%positive])] = Some [true; false].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

(** Facts and nonrecursive rules seed a set even when they produce the same tuple. *)
Example delta_initial_duplicates strategy :
  FinSet.size (delta_accumulated (delta_initial strategy delta_ground_fact
    [(0, [5%positive]); (0, [5%positive])] (Stratification (fun _ => 0) 1) 0
    (fun _ => FinSet.empty))) = 1.
Proof.
  destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_repeated_body : program nat :=
  Program nat_encoding (fun _ => 1)
    [Rule (delta_unary 1) [LPos (delta_unary 0); LPos (delta_unary 0)]].

(** Identical recursive literals and duplicate variants still produce one accumulated fact. *)
Example delta_repeated_body_computes strategy :
  delta_observe strategy delta_repeated_body [(0, [2%positive])]
    [(1, [2%positive]); (1, [3%positive])] = Some [true; false].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_negation : program nat :=
  Program nat_encoding (fun _ => 1)
    [delta_copy 1 0;
     Rule (delta_unary 2) [LPos (delta_unary 0); LNeg (delta_unary 1)];
     Rule (delta_unary 3) [LPos (delta_unary 0); LNeg (delta_unary 4)]].

(** A negated recursive lower predicate is observed after its closure has been completed. *)
Example delta_negation_computes strategy :
  delta_observe strategy delta_negation [(0, [2%positive])]
    [(1, [2%positive]); (2, [2%positive]); (3, [2%positive])] = Some [true; false; true].
Proof.
  apply delta_observe_bounded; destruct strategy; vm_compute; reflexivity.
Qed.

Definition delta_negative_cycle : program nat :=
  Program nat_encoding (fun _ => 1)
    [Rule (Atom 0 [TConst 1%positive]) [LNeg (Atom 1 [TConst 1%positive])];
     Rule (Atom 1 [TConst 1%positive]) [LNeg (Atom 0 [TConst 1%positive])]].

(** Both strategies reject a cycle containing negation. *)
Example delta_negative_cycle_computes strategy :
  solve_program_delta strategy delta_negative_cycle [] = None.
Proof.
  destruct strategy; vm_compute; reflexivity.
Qed.
