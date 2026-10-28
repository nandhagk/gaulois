(** * Total solver and fuel agreement examples

    Cyclic runs exercise finite height and a widening cut in an unbounded numeric domain.
    For example, repeated side contributions propagate through non-widening points to a loop head.
    Builds on: FixpointTotal, FixpointCheck and OrderBasic. *)

From Stdlib Require Import List Bool Arith PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderBasic OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCycles
  FixpointLeast FixpointCheck FixpointWorklist FixpointTotal.
Import List.ListNotations.

Definition total_test_schedule : scheduler nat :=
  Scheduler (fun _ => 1%positive) (fun _ => false).

Definition total_test_empty : System.t nat nat bool :=
  System.Make [] (fun c => c) (fun _ => Query.Ret true).

Definition total_test_empty_static : System.static total_test_empty.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _);
    intros c s x Hin; exact Hin.
Defined.

Definition total_test_empty_evidence :
  terminates bool_lattice total_test_empty_static total_test_schedule Joining :=
  inhabits (base_height bool_height).

Example empty_total_agrees_with_one_probe :
  proj1_sig (solve_total nat_encoding nat_encoding bool_lattice bool_laws total_test_schedule
    Joining total_test_empty total_test_empty_static total_test_empty_evidence) =
    lookup nat_encoding bool_lattice Map.empty.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding bool_lattice total_test_empty
    total_test_schedule Joining bool_laws total_test_empty_static total_test_empty_evidence)
    as [f Hfuel].
  destruct (Hfuel f (Pos.le_refl f)) as [m [Hrun Heq]].
  assert (Hone : run_worklist nat_encoding nat_encoding bool_lattice total_test_schedule Joining
    total_test_empty (Declared total_test_empty_static
      (index_system nat_encoding total_test_empty total_test_empty_static)) 1 = Some Map.empty).
  { vm_compute; reflexivity. }
  pose proof (total_completed_runs_unique nat_encoding nat_encoding bool_lattice
    total_test_schedule Joining total_test_empty _ f 1 m Map.empty Hrun Hone) as Hmap.
  now rewrite Hmap in Heq.
Qed.

(* Constraint 2 seeds the cycle by contributing twice to 0. The repeated constraint and
   repeated declared side target also exercise idempotent queue membership. *)
Definition total_test_cycle : System.t nat nat bool :=
  System.Make [0; 1; 2; 0] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 1 Query.Ret
      else if Nat.eqb c 1 then Query.Ask 0 Query.Ret
      else Query.Side 0 true (Query.Side 0 false (Query.Ret false))).

Definition total_test_cycle_static : System.static total_test_cycle.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [1] else if Nat.eqb c 1 then [0] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then [] else [0; 0]) _ _);
    intros c s x Hin; unfold total_test_cycle in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in *; exact Hin.
Defined.

Definition total_test_cycle_evidence :
  terminates bool_lattice total_test_cycle_static total_test_schedule Joining :=
  inhabits (base_height bool_height).

Definition total_test_cycle_map : assignment nat bool :=
  Map.set nat_encoding 1 true (Map.set nat_encoding 0 true Map.empty).

Example joining_cycle_needs_its_final_probe :
  run_worklist nat_encoding nat_encoding bool_lattice total_test_schedule Joining
    total_test_cycle (Declared total_test_cycle_static
      (index_system nat_encoding total_test_cycle total_test_cycle_static)) 5 = None /\
  run_worklist nat_encoding nat_encoding bool_lattice total_test_schedule Joining
    total_test_cycle (Declared total_test_cycle_static
      (index_system nat_encoding total_test_cycle total_test_cycle_static)) 6 =
      Some total_test_cycle_map.
Proof.
  vm_compute; auto.
Qed.

Example joining_cycle_recorded_agrees :
  run_worklist nat_encoding nat_encoding bool_lattice total_test_schedule Joining
    total_test_cycle Recorded 6 = Some total_test_cycle_map.
Proof.
  vm_compute; reflexivity.
Qed.

Example joining_cycle_total_agrees :
  proj1_sig (solve_total nat_encoding nat_encoding bool_lattice bool_laws total_test_schedule
    Joining total_test_cycle total_test_cycle_static total_test_cycle_evidence) =
    lookup nat_encoding bool_lattice total_test_cycle_map.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding bool_lattice total_test_cycle
    total_test_schedule Joining bool_laws total_test_cycle_static total_test_cycle_evidence)
    as [f Hfuel].
  destruct (Hfuel f (Pos.le_refl f)) as [m [Hrun Heq]].
  pose proof (total_completed_runs_unique nat_encoding nat_encoding bool_lattice
    total_test_schedule Joining total_test_cycle _ f 6 m total_test_cycle_map Hrun
    (proj2 joining_cycle_needs_its_final_probe)) as Hmap.
  now rewrite Hmap in Heq.
Qed.

Example joining_cycle_full_checker_accepts :
  check_post bool_lattice total_test_cycle
    (lookup nat_encoding bool_lattice total_test_cycle_map) = true /\
  map (lookup nat_encoding bool_lattice total_test_cycle_map) [0; 1; 2; 99] =
    [true; true; false; false].
Proof.
  vm_compute; auto.
Qed.

Definition total_test_cycle_monotone : monotone_system bool_lattice total_test_cycle.
Proof.
  intros c Hc; split.
  - intros s t Hle; unfold total_test_cycle; cbn.
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn; first [apply Hle|reflexivity].
  - intros s t Hle x a Hin; unfold total_test_cycle in *; cbn in *.
    destruct (Nat.eqb c 0), (Nat.eqb c 1); cbn in Hin; try contradiction.
    exists a; split; [exact Hin|apply (leb_refl bool_laws)].
Qed.

Example joining_cycle_is_reached_and_least :
  reached nat_encoding bool_lattice total_test_cycle
    (lookup nat_encoding bool_lattice total_test_cycle_map) /\
  least_solution bool_lattice total_test_cycle
    (lookup nat_encoding bool_lattice total_test_cycle_map).
Proof.
  rewrite <- joining_cycle_total_agrees; split.
  - apply solve_total_reached.
  - apply solve_total_least; [exact bool_lub|exact total_test_cycle_monotone].
Qed.

Example joining_fuel_exact_keeps_the_reached_assignment :
  exists f, forall fuel, (f <= fuel)%positive ->
    proj1_sig (solve_fuel nat_encoding nat_encoding bool_lattice bool_laws bool_top
      total_test_schedule Joining total_test_cycle fuel) =
      lookup nat_encoding bool_lattice total_test_cycle_map.
Proof.
  destruct (solve_fuel_exact nat_encoding nat_encoding bool_lattice total_test_cycle
    total_test_schedule Joining bool_top bool_laws total_test_cycle_static
    total_test_cycle_evidence) as [f Hfuel].
  exists f; intros fuel Hge; destruct (Hfuel fuel Hge) as [m [Hrun Heq]].
  pose proof (total_completed_runs_unique nat_encoding nat_encoding bool_lattice
    total_test_schedule Joining total_test_cycle Recorded fuel 6 m total_test_cycle_map Hrun
    joining_cycle_recorded_agrees) as Hmap.
  now rewrite Hmap in Heq.
Qed.

(** * An unbounded domain with a one-step widening *)

Definition total_number_le (a b : option nat) : bool :=
  match a, b with
  | Some x, Some y => Nat.leb x y
  | None, Some _ => false
  | _, None => true
  end.

Definition total_number_join (a b : option nat) : option nat :=
  match a, b with
  | Some x, Some y => Some (Nat.max x y)
  | _, _ => None
  end.

Definition total_number_lattice : lattice (option nat) :=
  Lattice (option nat) total_number_le (Some 0) total_number_join
    (fun _ _ => None) (fun _ b => b).

Definition total_number_laws : lattice_laws total_number_lattice.
Proof.
  constructor.
  - intros [a|]; cbn; [apply Nat.leb_refl|reflexivity].
  - intros [a|] [b|] [c|]; cbn; try discriminate; try reflexivity.
    intros Hab Hbc; apply Nat.leb_le in Hab; apply Nat.leb_le in Hbc; apply Nat.leb_le; lia.
  - intros [a|]; cbn; reflexivity.
  - intros [a|] [b|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_l.
  - intros [a|] [b|]; cbn; try reflexivity; apply Nat.leb_le, Nat.le_max_r.
  - intros [a|] [b|]; reflexivity.
  - intros [a|] [b|]; reflexivity.
  - intros a b Hab; exact Hab.
  - intros [a|] [b|] Hab; cbn; [apply Nat.leb_refl|reflexivity|apply Nat.leb_refl|reflexivity].
Qed.

Definition total_number_wrank : widening_rank total_number_lattice.
Proof.
  refine (@WideningRank (option nat) total_number_lattice
    (fun a => match a with Some _ => 1 | None => 0 end) _ _).
  - intros [a|] [b|] Hbelow; cbn; lia.
  - intros [a|] [b|] Hbelow; cbn in *; try discriminate; lia.
Defined.

(** Arbitrarily many strict finite numbers exclude a bounded joining height. *)
Lemma total_number_has_no_height : ~ inhabited (height total_number_lattice).
Proof.
  intros [Hheight].
  assert (Hrank : forall n, n <= rank Hheight (Some n)).
  { intro n; induction n as [|n IH]; [lia|].
    assert (Hjoin : join total_number_lattice (Some n) (Some (Datatypes.S n)) =
      Some (Datatypes.S n)).
    { cbn; f_equal; apply Nat.max_r; lia. }
    assert (Hstrict : leb total_number_lattice
      (join total_number_lattice (Some n) (Some (Datatypes.S n))) (Some n) = false).
    { rewrite Hjoin; change (Nat.leb (Datatypes.S n) n = false); apply Nat.leb_gt; lia. }
    pose proof (join_rank_grows Hheight _ _ Hstrict) as Hgrow; rewrite Hjoin in Hgrow; lia. }
  pose proof (Hrank (Datatypes.S (bound Hheight))).
  pose proof (rank_bounded Hheight (Some (Datatypes.S (bound Hheight)))); lia.
Qed.

Definition total_number_succ (a : option nat) : option nat :=
  match a with
  | Some n => Some (Datatypes.S n)
  | None => None
  end.

Definition total_number_system : System.t nat nat (option nat) :=
  System.Make [0; 1; 2; 3] (fun c => c)
    (fun c => if Nat.eqb c 0 then Query.Ask 2 (fun a => Query.Ret (total_number_succ a))
      else if Nat.eqb c 1 then Query.Ask 0 Query.Ret
      else if Nat.eqb c 2 then Query.Ask 1 Query.Ret
      else Query.Side 1 (Some 2) (Query.Side 1 (Some 1) (Query.Ret (Some 0)))).

Definition total_number_static : System.static total_number_system.
Proof.
  refine (System.Static
    (fun c => if Nat.eqb c 0 then [2] else if Nat.eqb c 1 then [0]
      else if Nat.eqb c 2 then [1] else [])
    (fun c => if Nat.eqb c 0 then [] else if Nat.eqb c 1 then []
      else if Nat.eqb c 2 then [] else [1; 1]) _ _);
    intros c s x Hin; unfold total_number_system in *; cbn in *;
    destruct (Nat.eqb c 0), (Nat.eqb c 1), (Nat.eqb c 2); cbn in *; exact Hin.
Defined.

Definition total_number_schedule : scheduler nat :=
  Scheduler (fun x => if Nat.eqb x 3 then 1%positive else 2%positive) (fun x => Nat.eqb x 0).

Lemma total_number_uncut_edge (y z : nat) :
  flows total_number_static y z /\ widening_point total_number_schedule z = false -> y < z.
Proof.
  intros [[c [Hc [Hread Hout]]] Hnonwidening].
  cbn in Hc; destruct Hc as [Heq|[Heq|[Heq|[Heq|Hbad]]]]; try contradiction;
    subst c; cbn in Hread, Hout, Hnonwidening; try contradiction;
    destruct Hread as [Heq|Hbad]; try contradiction; subst y;
    destruct Hout as [Heq|Hbad]; try contradiction; subst z; cbn in Hnonwidening;
    discriminate || lia.
Qed.

Definition total_number_cuts :
  cuts_every_cycle total_number_static (widening_point total_number_schedule).
Proof.
  intros x Hcycle.
  assert (Hincreases : forall y z,
    clos_trans nat (fun y z => flows total_number_static y z /\
      widening_point total_number_schedule z = false) y z -> y < z).
  { intros y z Hpath; induction Hpath as [y z Hedge|y z w Hyz IH1 Hzw IH2].
    - apply total_number_uncut_edge; exact Hedge.
    - lia. }
  pose proof (Hincreases x x Hcycle); lia.
Qed.

Definition total_number_evidence :
  terminates total_number_lattice total_number_static total_number_schedule Widening :=
  conj (inhabits total_number_wrank) total_number_cuts.

Example widening_rank_without_a_cycle_cut_is_insufficient :
  ~ terminates total_number_lattice total_number_static
    (Scheduler (priority total_number_schedule) (fun _ => false)) Widening.
Proof.
  intros [Hrank Hcut]; apply (Hcut 0).
  eapply t_trans with (y := 1).
  - apply t_step; split; [exists 1; cbn; tauto|reflexivity].
  - eapply t_trans with (y := 2).
    + apply t_step; split; [exists 2; cbn; tauto|reflexivity].
    + apply t_step; split; [exists 0; cbn; tauto|reflexivity].
Qed.

Definition total_number_map : assignment nat (option nat) :=
  Map.set nat_encoding 2 None
    (Map.set nat_encoding 1 None (Map.set nat_encoding 0 None Map.empty)).

Example widening_cut_finishes_while_joining_remains_pending :
  run_worklist nat_encoding nat_encoding total_number_lattice total_number_schedule Widening
    total_number_system (Declared total_number_static
      (index_system nat_encoding total_number_system total_number_static)) 6 =
      Some total_number_map /\
  run_worklist nat_encoding nat_encoding total_number_lattice total_number_schedule Joining
    total_number_system (Declared total_number_static
      (index_system nat_encoding total_number_system total_number_static)) 8 = None.
Proof.
  vm_compute; auto.
Qed.

Example widening_recorded_finishes :
  run_worklist nat_encoding nat_encoding total_number_lattice total_number_schedule Widening
    total_number_system Recorded 6 = Some total_number_map.
Proof.
  vm_compute; reflexivity.
Qed.

Example widening_total_agrees :
  proj1_sig (solve_total nat_encoding nat_encoding total_number_lattice total_number_laws
    total_number_schedule Widening total_number_system total_number_static total_number_evidence) =
    lookup nat_encoding total_number_lattice total_number_map.
Proof.
  destruct (solve_total_run nat_encoding nat_encoding total_number_lattice total_number_system
    total_number_schedule Widening total_number_laws total_number_static total_number_evidence)
    as [f Hfuel].
  destruct (Hfuel f (Pos.le_refl f)) as [m [Hrun Heq]].
  pose proof (total_completed_runs_unique nat_encoding nat_encoding total_number_lattice
    total_number_schedule Widening total_number_system _ f 6 m total_number_map Hrun
    (proj1 widening_cut_finishes_while_joining_remains_pending)) as Hmap.
  now rewrite Hmap in Heq.
Qed.

Example widening_full_checker_accepts :
  check_post total_number_lattice total_number_system
    (lookup nat_encoding total_number_lattice total_number_map) = true /\
  map (lookup nat_encoding total_number_lattice total_number_map) [0; 1; 2; 3; 99] =
    [None; None; None; Some 0; Some 0].
Proof.
  vm_compute; auto.
Qed.
