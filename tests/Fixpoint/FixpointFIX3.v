(** * Static schedules and checked narrowing examples

    Cyclic dependencies exercise graph priorities, cycle cuts and topological plans.
    For example, a simultaneous narrowing candidate can fail after its reads decrease.
    Builds on: FixpointSchedule, FixpointNarrow and OrderLattice. *)

From Stdlib Require Import List Bool Arith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Graph Require Import GraphCore GraphPrepare GraphWto.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointCycles FixpointCut FixpointWorklist FixpointSchedule FixpointNarrow.
Import List.ListNotations.

Definition schedule_test_system : System.t nat nat bool :=
  System.Make [0; 1; 2; 3] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 2 Query.Ret
      else if Nat.eqb c 2 then Query.Ask 0 Query.Ret
      else Query.Ask 2 (fun b => Query.Side 4 b (Query.Ret b))).

Definition schedule_test_static : System.static schedule_test_system.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1; 1] else if Nat.eqb c 1 then [2]
      else if Nat.eqb c 2 then [0] else [2])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [] else [4; 4]) _ _);
    intros c s x Hin; unfold schedule_test_system in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2); cbn in *; intuition.
Defined.

Definition schedule_test_graph :=
  dependency_graph nat_encoding schedule_test_system schedule_test_static.

Definition schedule_test_index :=
  index_system nat_encoding schedule_test_system schedule_test_static.

Definition schedule_test_rpo :=
  rpo_scheduler nat_encoding schedule_test_system schedule_test_static.

Definition schedule_test_wto :=
  wto_scheduler nat_encoding schedule_test_system schedule_test_static.

Definition schedule_test_scc :=
  scc_scheduler nat_encoding schedule_test_system schedule_test_static.

Example dependency_graph_deduplicates_reads_and_side_targets :
  map (Graph.out schedule_test_graph) [0; 1; 2; 3; 4] =
    [[(0, 2)]; [(1, 0)]; [(2, 3); (2, 1); (2, 4)]; []; []].
Proof.
  vm_compute; reflexivity.
Qed.

Example scheduler_priorities_are_prepared_graph_orders :
  map (priority schedule_test_rpo) [0; 1; 2; 3; 4] = [2; 1; 3; 5; 4]%positive /\
  map (priority schedule_test_wto) [0; 1; 2; 3; 4] = [2; 1; 3; 5; 4]%positive /\
  map (priority schedule_test_scc) [0; 1; 2; 3; 4] = [2; 1; 3; 15; 9]%positive.
Proof.
  vm_compute; auto.
Qed.

Example scheduler_widening_points_select_the_cycle_head :
  map (widening_point schedule_test_rpo) [0; 1; 2; 3; 4] =
    [false; true; false; false; false] /\
  map (widening_point schedule_test_wto) [0; 1; 2; 3; 4] =
    [false; true; false; false; false] /\
  map (widening_point schedule_test_scc) [0; 1; 2; 3; 4] =
    [false; true; false; false; false].
Proof.
  vm_compute; auto.
Qed.

Example all_three_schedulers_cut_the_cycle :
  cuts_every_cycle schedule_test_static (widening_point schedule_test_rpo) /\
  cuts_every_cycle schedule_test_static (widening_point schedule_test_wto) /\
  cuts_every_cycle schedule_test_static (widening_point schedule_test_scc).
Proof.
  split; [apply rpo_scheduler_cuts|]; split; [apply wto_scheduler_cuts|apply scc_scheduler_cuts].
Qed.

Definition schedule_test_cuts : FinSet.t nat := FinSet.of_list nat_encoding [0].

Example cut_cycle_accepts_its_topological_plan :
  plan_of nat_encoding schedule_test_system schedule_test_static schedule_test_index
    schedule_test_cuts = Some [2; 4; 1; 3].
Proof.
  vm_compute; reflexivity.
Qed.

Example computed_plan_is_valid_and_its_cuts_intersect_every_cycle :
  plan_valid nat_encoding schedule_test_system schedule_test_static schedule_test_index
    schedule_test_cuts [2; 4; 1; 3] /\
  cuts_every_cycle schedule_test_static (fun x => FinSet.mem nat_encoding x schedule_test_cuts).
Proof.
  destruct (plan_of_valid nat_encoding schedule_test_system schedule_test_static schedule_test_index
    schedule_test_cuts (index_system_laws _ _ _)) as [Hexists Hvalid].
  split.
  - apply Hvalid; exact cut_cycle_accepts_its_topological_plan.
  - apply Hexists; exists [2; 4; 1; 3]; exact cut_cycle_accepts_its_topological_plan.
Qed.

Example uncut_cycle_rejects_a_plan :
  plan_of nat_encoding schedule_test_system schedule_test_static schedule_test_index
    FinSet.empty = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition schedule_nested_system : System.t nat nat bool :=
  System.Make [0; 1; 2] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 2 Query.Ret
      else Query.Ask 0 (fun a => Query.Ask 2 (fun b => Query.Ret (orb a b)))).

Definition schedule_nested_static : System.static schedule_nested_system.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [2] else [0; 2])
    (fun _ => []) _ _);
    intros c s x Hin; unfold schedule_nested_system in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Defined.

Example nested_wto_exposes_the_inner_self_cycle :
  wto_total (prepare nat_encoding
    (dependency_graph nat_encoding schedule_nested_system schedule_nested_static)) =
    [WOpen 1; WVertex 0; WOpen 2; WClose; WClose] /\
  map (widening_point (wto_scheduler nat_encoding schedule_nested_system schedule_nested_static))
    [0; 1; 2] = [false; true; true].
Proof.
  vm_compute; auto.
Qed.

Definition schedule_empty_system : System.t nat nat bool :=
  System.Make [] (fun c => c) (fun _ => Query.Ret false).

Definition schedule_empty_static : System.static schedule_empty_system.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _); intros c s x Hin; exact Hin.
Defined.

Example empty_system_has_an_empty_plan_and_no_widening_points :
  unknowns nat_encoding schedule_empty_system schedule_empty_static = [] /\
  plan_of nat_encoding schedule_empty_system schedule_empty_static
    (index_system nat_encoding schedule_empty_system schedule_empty_static) FinSet.empty =
    Some [] /\
  widening_point (rpo_scheduler nat_encoding schedule_empty_system schedule_empty_static) 0 =
    false /\
  widening_point (wto_scheduler nat_encoding schedule_empty_system schedule_empty_static) 0 =
    false /\
  widening_point (scc_scheduler nat_encoding schedule_empty_system schedule_empty_static) 0 = false.
Proof.
  vm_compute; auto.
Qed.

(** The test domain narrows to its second argument, enabling observable decreases. *)
Definition narrow_test_lattice : lattice bool :=
  {| leb := implb;
     bot := false;
     join := orb;
     widen := orb;
     narrow := fun _ b => b |}.

Definition narrow_test_laws : lattice_laws narrow_test_lattice.
Proof.
  constructor; intros; repeat match goal with b : bool |- _ => destruct b end;
    cbn in *; congruence.
Qed.

Definition narrow_test_accepted : System.t nat nat bool :=
  System.Make [0; 1] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Side 2 false (Query.Ret false)
      else Query.Ask 0 Query.Ret).

Definition narrow_test_accepted_static : System.static narrow_test_accepted.
Proof.
  refine (System.Static (fun c => if Nat.eqb c 0 then [] else [0])
    (fun c => if Nat.eqb c 0 then [2] else []) _ _);
    intros c s x Hin; unfold narrow_test_accepted in *; cbn in *;
    destruct (Nat.eqb c 0); cbn in *; exact Hin.
Defined.

Definition narrow_test_initial : assignment nat bool :=
  Map.set nat_encoding 0 true (Map.set nat_encoding 1 true
    (Map.set nat_encoding 2 true (Map.set nat_encoding 99 true Map.empty))).

Definition narrow_test_accepted_index :=
  index_system nat_encoding narrow_test_accepted narrow_test_accepted_static.

Definition narrow_test_candidate :=
  narrow_pass nat_encoding narrow_test_lattice narrow_test_accepted narrow_test_accepted_static
    narrow_test_accepted_index narrow_test_initial.

Example narrowing_pass_reads_the_old_assignment :
  map (lookup nat_encoding narrow_test_lattice narrow_test_candidate) [0; 1; 2; 99; 100] =
    [false; true; false; true; false] /\
  check_post narrow_test_lattice narrow_test_accepted
    (lookup nat_encoding narrow_test_lattice narrow_test_candidate) = true.
Proof.
  vm_compute; auto.
Qed.

Example accepted_two_rounds_decrease_and_preserve_unrelated_values :
  map (lookup nat_encoding narrow_test_lattice
    (narrow_checked nat_encoding narrow_test_lattice narrow_test_accepted
      narrow_test_accepted_static narrow_test_accepted_index 2 narrow_test_initial))
    [0; 1; 2; 99; 100] = [false; false; false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example zero_narrowing_rounds_preserve_the_assignment :
  narrow_checked nat_encoding narrow_test_lattice narrow_test_accepted narrow_test_accepted_static
    narrow_test_accepted_index 0 narrow_test_initial = narrow_test_initial.
Proof.
  vm_compute; reflexivity.
Qed.

Definition narrow_test_rejected : System.t nat nat bool :=
  System.Make [0; 1] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 (fun b => Query.Ret (negb b))
      else Query.Ret false).

Definition narrow_test_rejected_static : System.static narrow_test_rejected.
Proof.
  refine (System.Static (fun c => if Nat.eqb c 0 then [1] else []) (fun _ => []) _ _);
    intros c s x Hin; unfold narrow_test_rejected in *; cbn in *;
    destruct (Nat.eqb c 0); cbn in *; exact Hin.
Defined.

Definition narrow_test_rejected_index :=
  index_system nat_encoding narrow_test_rejected narrow_test_rejected_static.

Example decreasing_candidate_can_break_a_constraint :
  check_post narrow_test_lattice narrow_test_rejected
    (lookup nat_encoding narrow_test_lattice narrow_test_initial) = true /\
  check_post narrow_test_lattice narrow_test_rejected
    (lookup nat_encoding narrow_test_lattice
      (narrow_pass nat_encoding narrow_test_lattice narrow_test_rejected
        narrow_test_rejected_static narrow_test_rejected_index narrow_test_initial)) = false /\
  narrow_checked nat_encoding narrow_test_lattice narrow_test_rejected narrow_test_rejected_static
    narrow_test_rejected_index 1 narrow_test_initial = narrow_test_initial.
Proof.
  vm_compute; auto.
Qed.

Example checked_narrowing_has_both_universal_guarantees :
  post_solution narrow_test_lattice narrow_test_accepted
    (lookup nat_encoding narrow_test_lattice
      (narrow_checked nat_encoding narrow_test_lattice narrow_test_accepted
        narrow_test_accepted_static narrow_test_accepted_index 2 narrow_test_initial)) /\
  fun_leb narrow_test_lattice
    (lookup nat_encoding narrow_test_lattice
      (narrow_checked nat_encoding narrow_test_lattice narrow_test_accepted
        narrow_test_accepted_static narrow_test_accepted_index 2 narrow_test_initial))
    (lookup nat_encoding narrow_test_lattice narrow_test_initial).
Proof.
  split.
  - apply narrow_checked_post, check_post_iff; vm_compute; reflexivity.
  - apply narrow_checked_below; exact narrow_test_laws.
Qed.
