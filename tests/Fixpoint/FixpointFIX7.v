(** * Direct local closure and precise cyclic solving

    These examples compute contributor closure, ordered restriction and projected total results.
    For example, a side contribution seeds one bit around a cycle without making its root top.
    Builds on: FixpointLocalDirect, FixpointTotal, OrderBasic and OrderProduct. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderProduct.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal FixpointPartial FixpointLocal FixpointLocalDirect.
Import List.ListNotations.

Definition direct_lattice : lattice (bool * bool) := product_lattice bool_lattice bool_lattice.

Definition direct_laws : lattice_laws direct_lattice :=
  product_laws bool_lattice bool_lattice bool_laws bool_laws.

Definition direct_schedule : scheduler nat :=
  Scheduler (fun _ => 1%positive) (fun _ => false).

(* Constraint 2 contributes into the cycle, although its nominal target is 10.
   Constraint 3 is unrelated and would contribute top to its own target 20.
   The duplicate constraint 1 checks that restriction preserves list multiplicity. *)
Definition direct_cycle : System.t nat nat (bool * bool) :=
  System.Make [3; 1; 2; 0; 1]
    (fun c => if Nat.eqb c 2 then 10 else if Nat.eqb c 3 then 20 else c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 0 Query.Ret
      else if Nat.eqb c 2 then Query.Side 0 (true, false) (Query.Ret (false, false))
      else Query.Ret (true, true)).

Definition direct_static : System.static direct_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [0] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [0; 42] else []) _ _).
  - intros c s x Hin; unfold direct_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2); cbn in *; exact Hin.
  - intros c s x Hin; unfold direct_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2); cbn in *; intuition.
Defined.

Definition direct_index : sys_index nat nat :=
  index_system nat_encoding direct_cycle direct_static.

Definition direct_region (roots : list nat) : FinSet.t nat :=
  local_direct_closure nat_encoding nat_encoding direct_cycle direct_static direct_index roots.

Definition direct_restricted (roots : list nat) : System.t nat nat (bool * bool) :=
  local_direct_system nat_encoding nat_encoding direct_cycle direct_static direct_index roots.

Definition direct_declarations (roots : list nat) : System.static (direct_restricted roots) :=
  local_direct_static nat_encoding nat_encoding direct_cycle direct_static direct_index roots.

(** The product height supplies termination for every restricted system, including an empty one. *)
Definition direct_termination (roots : list nat) :
  terminates direct_lattice (direct_declarations roots) direct_schedule Joining :=
  inhabits (base_height (product_height bool_laws bool_laws bool_height bool_height)).

Definition direct_result (roots : list nat) : local_result nat (bool * bool) :=
  local_direct nat_encoding nat_encoding direct_lattice direct_laws direct_schedule Joining
    direct_cycle direct_static direct_index roots (direct_termination roots).

Example contributor_closure_includes_nominal_side_and_read_targets :
  map (fun x => FinSet.mem nat_encoding x (direct_region [0; 99]))
    [0; 1; 10; 20; 42; 99] = [true; true; true; false; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example restriction_preserves_original_order_and_duplicates :
  System.constraints (direct_restricted [0; 99]) = [1; 2; 0; 1].
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_roots_preserve_closure :
  direct_region [0; 99; 0; 1] = direct_region [0; 99].
Proof.
  vm_compute; reflexivity.
Qed.

Example unknown_root_has_no_constraints :
  (FinSet.elements (direct_region [99]), System.constraints (direct_restricted [99])) =
    ([99], []).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_roots_have_empty_closure :
  (FinSet.elements (direct_region []), System.constraints (direct_restricted [])) = ([], []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition direct_expected : assignment nat (bool * bool) :=
  Map.of_list nat_encoding [(0, (true, false)); (1, (true, false))].

Example cyclic_restricted_run_computes_precise_values :
  run_worklist nat_encoding nat_encoding direct_lattice direct_schedule Joining
    (direct_restricted [0; 99])
    (Declared (direct_declarations [0; 99])
      (index_system nat_encoding (direct_restricted [0; 99]) (direct_declarations [0; 99])))
    64 = Some direct_expected.
Proof.
  vm_compute; reflexivity.
Qed.

(* Accessibility proofs are intentionally opaque. Fuel agreement exposes the same completed
   execution for computation without changing the total solver's proof erasure boundary. *)
Lemma direct_total_from_run (roots : list nat) fuel m :
  run_worklist nat_encoding nat_encoding direct_lattice direct_schedule Joining
    (direct_restricted roots)
    (Declared (direct_declarations roots)
      (index_system nat_encoding (direct_restricted roots) (direct_declarations roots)))
    fuel = Some m ->
  proj1_sig (solve_total nat_encoding nat_encoding direct_lattice direct_laws direct_schedule
    Joining (direct_restricted roots) (direct_declarations roots) (direct_termination roots)) =
    lookup nat_encoding direct_lattice m.
Proof.
  intro Hrun.
  destruct (solve_total_run nat_encoding nat_encoding direct_lattice (direct_restricted roots)
    direct_schedule Joining direct_laws (direct_declarations roots) (direct_termination roots))
    as [f Hfuel].
  destruct (Hfuel f (Pos.le_refl f)) as [result [Hresult Heq]].
  pose proof (total_completed_runs_unique nat_encoding nat_encoding direct_lattice direct_schedule
    Joining (direct_restricted roots) _ f fuel result m Hresult Hrun) as Hmap.
  rewrite Hmap in Heq; exact Heq.
Qed.

Lemma direct_result_from_run (roots : list nat) fuel m :
  run_worklist nat_encoding nat_encoding direct_lattice direct_schedule Joining
    (direct_restricted roots)
    (Declared (direct_declarations roots)
      (index_system nat_encoding (direct_restricted roots) (direct_declarations roots)))
    fuel = Some m ->
  values (direct_result roots) = local_direct_project nat_encoding
    (FinSet.elements (direct_region roots)) (lookup nat_encoding direct_lattice m).
Proof.
  intro Hrun.
  change (local_direct_project nat_encoding (FinSet.elements (direct_region roots))
    (proj1_sig (solve_total nat_encoding nat_encoding direct_lattice direct_laws direct_schedule
      Joining (direct_restricted roots) (direct_declarations roots) (direct_termination roots))) =
    local_direct_project nat_encoding (FinSet.elements (direct_region roots))
      (lookup nat_encoding direct_lattice m)).
  rewrite (direct_total_from_run roots fuel m Hrun); reflexivity.
Qed.

Example cyclic_side_contribution_has_precise_non_top_root :
  map (lookup nat_encoding direct_lattice (values (direct_result [0; 99])))
    [0; 1; 10; 20; 42; 99] =
    [(true, false); (true, false); (false, false); (false, false);
      (false, false); (false, false)] /\
  lookup nat_encoding direct_lattice (values (direct_result [0; 99])) 0 <>
    top_value (product_top bool_top bool_top).
Proof.
  rewrite (direct_result_from_run [0; 99] 64 direct_expected
    cyclic_restricted_run_computes_precise_values).
  vm_compute; split; [reflexivity|discriminate].
Qed.

Example unknown_root_is_explicitly_stored_at_bottom :
  Map.get nat_encoding 99 (values (direct_result [99])) = Some (false, false) /\
  Map.get nat_encoding 20 (values (direct_result [99])) = None.
Proof.
  assert (Hrun : run_worklist nat_encoding nat_encoding direct_lattice direct_schedule Joining
    (direct_restricted [99])
    (Declared (direct_declarations [99])
      (index_system nat_encoding (direct_restricted [99]) (direct_declarations [99])))
    1 = Some Map.empty) by (vm_compute; reflexivity).
  rewrite (direct_result_from_run [99] 1 Map.empty Hrun); vm_compute; split; reflexivity.
Qed.

Example empty_roots_have_empty_assignment : values (direct_result []) = Map.empty.
Proof.
  assert (Hrun : run_worklist nat_encoding nat_encoding direct_lattice direct_schedule Joining
    (direct_restricted [])
    (Declared (direct_declarations [])
      (index_system nat_encoding (direct_restricted []) (direct_declarations [])))
    1 = Some Map.empty) by (vm_compute; reflexivity).
  rewrite (direct_result_from_run [] 1 Map.empty Hrun); vm_compute; reflexivity.
Qed.

Example external_partial_checker_remains_available :
  check_partial nat_encoding direct_lattice direct_cycle direct_static direct_index
    (direct_region [0; 99]) (local_direct_project nat_encoding
      (FinSet.elements (direct_region [0; 99]))
      (lookup nat_encoding direct_lattice direct_expected))
    = true.
Proof.
  vm_compute; reflexivity.
Qed.
