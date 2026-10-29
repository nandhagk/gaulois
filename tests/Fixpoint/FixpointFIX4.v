(** * Closed partial and cyclic local examples

    These computations distinguish dependency closure, output checking and local coverage.
    For example, a three-unknown cycle is accepted while an unrelated constant remains unsolved.
    Builds on: FixpointPartial, FixpointLocal and OrderBasic. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointWorklist FixpointPartial FixpointLocal.
Import List.ListNotations.

Definition partial_cycle : System.t nat nat bool :=
  System.Make [0; 1; 2; 3; 4]
    (fun c => if Nat.eqb c 3 then 10 else if Nat.eqb c 4 then 11 else c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 2 Query.Ret
      else if Nat.eqb c 2 then
        Query.Ask 0 (fun a => Query.Side 1 true (Query.Side 20 true (Query.Ret a)))
      else if Nat.eqb c 4 then Query.Side 2 true (Query.Ret true)
      else Query.Ret true).

Definition partial_cycle_static : System.static partial_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2]
      else if Nat.eqb c 2 then [0] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [1; 20] else if Nat.eqb c 4 then [2; 42] else []) _ _).
  - intros c s x Hin; unfold partial_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2), (Nat.eqb c 4);
      cbn in *; exact Hin.
  - intros c s x Hin; unfold partial_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2), (Nat.eqb c 4);
      cbn in *; intuition.
Defined.

Definition partial_cycle_index : sys_index nat nat :=
  index_system nat_encoding partial_cycle partial_cycle_static.

Definition partial_region : FinSet.t nat := FinSet.of_list nat_encoding [0; 1; 2].

Definition partial_values : assignment nat bool :=
  Map.of_list nat_encoding [(0, true); (1, true); (2, true)].

Example closed_region_accepts :
  check_partial nat_encoding bool_lattice partial_cycle partial_cycle_static partial_cycle_index
    partial_region partial_values = true.
Proof.
  vm_compute; reflexivity.
Qed.

(* Neither an out-of-region nominal target nor an out-of-region side output is required. *)
Example accepted_partial_is_not_a_global_solution :
  check_post bool_lattice partial_cycle (lookup nat_encoding bool_lattice partial_values) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example incomplete_read_region_rejects :
  check_partial nat_encoding bool_lattice partial_cycle partial_cycle_static partial_cycle_index
    (FinSet.of_list nat_encoding [0; 1]) partial_values = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example insufficient_side_value_rejects :
  check_partial nat_encoding bool_lattice partial_cycle partial_cycle_static partial_cycle_index
    partial_region (Map.of_list nat_encoding [(0, true); (1, true)]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example insufficient_return_value_rejects :
  check_partial nat_encoding bool_lattice partial_cycle partial_cycle_static partial_cycle_index
    partial_region (Map.of_list nat_encoding [(1, true); (2, true)]) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition partial_side_only : System.t nat nat bool :=
  System.Make [0] (fun _ => 11) (fun _ => Query.Side 2 true (Query.Ret false)).

Definition partial_side_static : System.static partial_side_only.
Proof.
  refine (System.Static (fun _ => []) (fun _ => [2]) _ _).
  - intros c s x Hin; exact Hin.
  - intros c s x Hin; exact Hin.
Defined.

Example isolated_side_output_is_checked :
  check_partial nat_encoding bool_lattice partial_side_only partial_side_static
    (index_system nat_encoding partial_side_only partial_side_static)
    (FinSet.of_list nat_encoding [2]) Map.empty = false /\
  check_partial nat_encoding bool_lattice partial_side_only partial_side_static
    (index_system nat_encoding partial_side_only partial_side_static)
    (FinSet.of_list nat_encoding [2]) (Map.set nat_encoding 2 true Map.empty) = true.
Proof.
  vm_compute; auto.
Qed.

Example declared_but_absent_side_output_is_permitted :
  check_partial nat_encoding bool_lattice partial_cycle partial_cycle_static partial_cycle_index
    (FinSet.of_list nat_encoding [42]) Map.empty = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example closed_region_has_declared_dependencies :
  dependency_closed nat_encoding partial_cycle partial_cycle_static partial_region.
Proof.
  intros c Hc Htouch y Hy.
  cbn [partial_cycle System.constraints] in Hc.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]; try contradiction; subst c;
    vm_compute in Hy; try contradiction.
  all: destruct Hy as [Hy|Hy]; [subst y; vm_compute; reflexivity|contradiction].
Qed.

Definition local_schedule : scheduler nat := Scheduler (fun _ => 1%positive) (fun _ => false).

Definition local_observation (r : local_result nat bool) : list bool * list bool :=
  (map (fun x => FinSet.mem nat_encoding x (explored r)) [0; 1; 2; 10; 11; 99],
   map (lookup nat_encoding bool_lattice (values r)) [0; 1; 2; 10; 11; 20; 99]).

Example cyclic_local_run_accepts :
  option_map local_observation
    (local_checked nat_encoding nat_encoding bool_lattice local_schedule Joining partial_cycle
      partial_cycle_static partial_cycle_index [0] 64) =
    Some ([true; true; true; false; false; false], [true; true; true; false; true; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example duplicate_roots_preserve_cyclic_result :
  option_map local_observation
    (local_checked nat_encoding nat_encoding bool_lattice local_schedule Widening partial_cycle
      partial_cycle_static partial_cycle_index [0; 0; 2] 64) =
    Some ([true; true; true; false; false; false], [true; true; true; false; true; true; false]).
Proof.
  vm_compute; reflexivity.
Qed.

Example traversal_exhaustion_rejects :
  local_checked nat_encoding nat_encoding bool_lattice local_schedule Joining partial_cycle
    partial_cycle_static partial_cycle_index [0] 1 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example unconstrained_root_is_covered :
  option_map (fun r =>
    (FinSet.mem nat_encoding 99 (explored r), lookup nat_encoding bool_lattice (values r) 99))
    (local_checked nat_encoding nat_encoding bool_lattice local_schedule Joining partial_cycle
      partial_cycle_static partial_cycle_index [99] 4) = Some (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_roots_accept_empty_region :
  option_map (fun r => (FinSet.elements (explored r), Map.elements (values r)))
    (local_checked nat_encoding nat_encoding bool_lattice local_schedule Joining partial_cycle
      partial_cycle_static partial_cycle_index [] 1) = Some ([], []).
Proof.
  vm_compute; reflexivity.
Qed.
