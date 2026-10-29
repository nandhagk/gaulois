(** * Indexed nested and multiway join examples

    These computations check both join strategies on matching, filtering and empty inputs.
    For example, a triangle join intersects three relation domains before producing a head.
    Builds on: RulesJoin, RulesCompile and RulesSyntax. *)

From Stdlib Require Import List Bool PeanoNat PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Rules Require Import RulesSyntax RulesCompile RulesJoin.
Import List.ListNotations.

Definition join_test_atom p ts : atom nat := Atom p ts.

Definition join_test_program (rs : list (rule nat)) : program nat :=
  Program nat_encoding (fun p => if Nat.eqb p 0 then 1 else 2) rs.

Definition join_test_facts : list (ground_atom nat) :=
  [(1%nat, [2; 2]); (1%nat, [2; 2]); (1%nat, [2; 3]); (1%nat, [3; 3]);
   (1%nat, [4; 4]); (2%nat, [2; 5]); (2%nat, [3; 6]); (3%nat, [2; 5]);
   (3%nat, [4; 6]); (4%nat, [3; 3])]%positive.

Definition join_test_env p : FinSet.t tuple :=
  FinSet.of_list tuple_encoding
    (map snd (filter (fun f => Nat.eqb p (fst f)) join_test_facts)).

Definition repeated_join_rule : rule nat :=
  Rule (join_test_atom 0 [TVar 0])
    [LPos (join_test_atom 1 [TVar 0; TVar 0]);
     LNeg (join_test_atom 4 [TVar 0; TVar 0])].

(** Repeated variables reject unequal components; completed lower negation excludes three. *)
Example repeated_and_negative_both : forall strategy,
  let result := fire_rule_join strategy (join_test_program [repeated_join_rule])
    join_test_facts repeated_join_rule join_test_env in
  FinSet.mem tuple_encoding [2%positive] result = true /\
  FinSet.mem tuple_encoding [3%positive] result = false /\
  FinSet.mem tuple_encoding [4%positive] result = true /\
  FinSet.mem tuple_encoding [5%positive] result = false /\ FinSet.size result = 2.
Proof.
  intros []; vm_compute; repeat split; reflexivity.
Qed.

Definition constant_join_rule : rule nat :=
  Rule (join_test_atom 0 [TVar 0])
    [LPos (join_test_atom 1 [TVar 0; TConst 3])].

(** Constants select their exact indexed column and reject other rows. *)
Example constant_both : forall strategy,
  let result := fire_rule_join strategy (join_test_program [constant_join_rule])
    join_test_facts constant_join_rule join_test_env in
  FinSet.mem tuple_encoding [2%positive] result = true /\
  FinSet.mem tuple_encoding [3%positive] result = true /\
  FinSet.mem tuple_encoding [4%positive] result = false.
Proof.
  intros []; vm_compute; repeat split; reflexivity.
Qed.

Definition triangle_atoms : list (literal nat) :=
  [LPos (join_test_atom 1 [TVar 0; TVar 1]);
   LPos (join_test_atom 2 [TVar 1; TVar 2]);
   LPos (join_test_atom 3 [TVar 0; TVar 2])].

Definition triangle_rule : rule nat := Rule (join_test_atom 0 [TVar 0]) triangle_atoms.
Definition triangle_reversed : rule nat := Rule (join_test_atom 0 [TVar 0]) (rev triangle_atoms).

(** A three-relation intersection produces only the shared triangle in either literal order. *)
Example triangle_orders_both : forall strategy,
  let prog := join_test_program [triangle_rule; triangle_reversed] in
  let forward := fire_rule_join strategy prog join_test_facts triangle_rule join_test_env in
  let backward := fire_rule_join strategy prog join_test_facts triangle_reversed join_test_env in
  FinSet.elements forward = [[2%positive]] /\ FinSet.elements backward = [[2%positive]].
Proof.
  intros []; vm_compute; split; reflexivity.
Qed.

Definition absent_join_rule : rule nat :=
  Rule (join_test_atom 0 [TVar 0]) [LPos (join_test_atom 8 [TVar 0; TVar 1])].

(** An empty input relation gives no result, including in multiway domain intersection. *)
Example empty_relation_both : forall strategy,
  FinSet.elements (fire_rule_join strategy (join_test_program [absent_join_rule])
    join_test_facts absent_join_rule join_test_env) = [].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Definition empty_join_rule : rule nat := Rule (join_test_atom 0 [TConst 2]) [].

(** An empty body has its one constant head valuation. *)
Example empty_body_both : forall strategy,
  FinSet.elements (fire_rule_join strategy (join_test_program [empty_join_rule])
    [] empty_join_rule (fun _ => FinSet.empty)) = [[2%positive]].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Definition ground_join_rule : rule nat :=
  Rule (join_test_atom 0 [TConst 2]) [LPos (join_test_atom 1 [TConst 2; TConst 2])].
Definition absent_ground_rule : rule nat :=
  Rule (join_test_atom 0 [TConst 2]) [LPos (join_test_atom 1 [TConst 2; TConst 4])].

(** Ground positive atoms use terminal membership even when no variables are enumerated. *)
Example ground_literals_both : forall strategy,
  let prog := join_test_program [ground_join_rule; absent_ground_rule] in
  FinSet.elements (fire_rule_join strategy prog join_test_facts ground_join_rule join_test_env)
    = [[2%positive]] /\
  FinSet.elements (fire_rule_join strategy prog join_test_facts absent_ground_rule join_test_env)
    = [].
Proof.
  intros []; vm_compute; split; reflexivity.
Qed.

Definition malformed_join_env (_ : nat) : FinSet.t tuple :=
  FinSet.of_list tuple_encoding [[2%positive]; [2%positive; 2%positive; 2%positive]].

(** Stored rows of either wrong length cannot satisfy a binary literal. *)
Example malformed_rows_both : forall strategy,
  FinSet.elements (fire_rule_join strategy (join_test_program [repeated_join_rule])
    join_test_facts repeated_join_rule malformed_join_env) = [].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Definition nullary_join_rule : rule nat :=
  Rule (join_test_atom 0 []) [LPos (join_test_atom 1 [])].

(** The empty tuple remains a fact for zero-arity predicates. *)
Example nullary_both : forall strategy,
  FinSet.elements (fire_rule_join strategy
    (Program nat_encoding (fun _ => 0) [nullary_join_rule]) [(1, [])] nullary_join_rule
    (fun p => if Nat.eqb p 1 then FinSet.of_list tuple_encoding [[]] else FinSet.empty)) = [[]].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Definition ground_negative_rule : rule nat :=
  Rule (join_test_atom 0 [TConst 2]) [LNeg (join_test_atom 4 [TConst 3; TConst 3])].

(** With no positive literals, a completed lower relation alone decides a ground negative. *)
Example ground_negative_both : forall strategy,
  let prog := join_test_program [ground_negative_rule] in
  FinSet.elements (fire_rule_join strategy prog join_test_facts ground_negative_rule
    (fun _ => FinSet.empty)) = [[2%positive]] /\
  FinSet.elements (fire_rule_join strategy prog join_test_facts ground_negative_rule join_test_env)
    = [].
Proof.
  intros []; vm_compute; split; reflexivity.
Qed.

(** Matching foreign constants in the environment still fail the head-universe filter. *)
Example universe_filter_both : forall strategy,
  FinSet.elements (fire_rule_join strategy (join_test_program [repeated_join_rule])
    join_test_facts repeated_join_rule
    (fun p => if Nat.eqb p 1 then FinSet.of_list tuple_encoding [[9%positive; 9%positive]]
      else FinSet.empty)) = [].
Proof.
  intros []; vm_compute; reflexivity.
Qed.

(** A bound-position domain contains exactly the legal rows' matching variable values. *)
Example variable_domain_intersection :
  let bound := FinSet.of_list nat_encoding [0] in
  let b := Map.set nat_encoding 0 2%positive Map.empty in
  let ps := [join_test_atom 1 [TVar 0; TVar 1]; join_test_atom 3 [TVar 0; TVar 1]] in
  let rows := fun p => FinSet.elements (join_test_env p) in
  FinSet.elements (variable_candidates bound b (prepare_variable bound 1 ps rows)) = [].
Proof.
  vm_compute; reflexivity.
Qed.

(** Domain intersection keeps a shared value and excludes values present in only one relation. *)
Example variable_domain_shared_value :
  let bound := FinSet.of_list nat_encoding [0] in
  let b := Map.set nat_encoding 0 2%positive Map.empty in
  let ps := [join_test_atom 1 [TVar 0; TVar 1]; join_test_atom 2 [TVar 0; TVar 1]] in
  let rows := fun p => if Nat.eqb p 1 then
    [[2%positive; 3%positive]; [2%positive; 4%positive]; [3%positive; 5%positive]]
    else [[2%positive; 3%positive]; [2%positive; 5%positive]] in
  FinSet.elements (variable_candidates bound b (prepare_variable bound 1 ps rows)) = [3%positive].
Proof.
  vm_compute; reflexivity.
Qed.

Definition triangle_with_variable_order vs : FinSet.t tuple :=
  let ps := positive_atoms (body triangle_rule) in
  let relations := prepare_join_relations nat_encoding ps join_test_env in
  let rows := join_relation_rows nat_encoding relations in
  let bindings := filter (positive_ok ps join_test_env)
    (run_multiway (prepare_multiway vs FinSet.empty ps rows) [Map.empty]) in
  FinSet.of_list tuple_encoding
    (map (fun b => map (inst (binding_value b)) (args (head triangle_rule))) bindings).

(** Distinct variable orders probe different conditional indexes and find the same triangle. *)
Example triangle_variable_orders :
  FinSet.elements (triangle_with_variable_order [0; 1; 2]) = [[2%positive]] /\
  FinSet.elements (triangle_with_variable_order [2; 0; 1]) = [[2%positive]] /\
  FinSet.elements (triangle_with_variable_order [1; 2; 0]) = [[2%positive]].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Updating an index adds a tuple once as a domain member even when its row is repeated. *)
Example variable_index_duplicate_update :
  let idx := build_variable_index FinSet.empty [TVar 0; TVar 0] 0
    [[2%positive; 2%positive]; [2%positive; 3%positive]] in
  let updated := variable_index_add FinSet.empty [TVar 0; TVar 0] 0
    [2%positive; 2%positive] idx in
  FinSet.elements (variable_index_get updated []) = [2%positive].
Proof.
  vm_compute; reflexivity.
Qed.
