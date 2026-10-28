(** * Query, index and certificate examples

    Computation checks traces, accepted solutions and accepted and rejected cut certificates.
    For example, one constraint contributes to a side target while another copies its target.
    Builds on: FixpointQuery, FixpointSystem, FixpointIndex, FixpointCheck, FixpointCut,
    FixpointLeast and OrderBasic. *)

From Stdlib Require Import List Bool Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderBasic.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointCut FixpointLeast.
Import List.ListNotations.

Example empty_query_run : Query.run (@Query.Ret nat bool false) (fun _ => true) =
  (false, [], []).
Proof.
  vm_compute; reflexivity.
Qed.

Definition traced_query : Query.t nat bool :=
  Query.Side 2 true (Query.Ask 0 (fun a => Query.Side 2 a (Query.Ask 0 Query.Ret))).

Example side_query_run : Query.run traced_query (fun _ => false) =
  (false, [0; 0], [(2, true); (2, false)]).
Proof.
  vm_compute; reflexivity.
Qed.

Example sequence_queries :
  Query.run (ask_all [0; 1] (fun vs =>
    side_all [(2, true); (2, false)] (Query.Ret (forallb (fun b => b) vs))))
    (fun x => Nat.eqb x 0) = (false, [0; 1], [(2, true); (2, false)]).
Proof.
  vm_compute; reflexivity.
Qed.

Definition sample_system : System.t nat bool bool :=
  System.Make [false; true] (fun c : bool => if c then 1 else 0)
    (fun c : bool => if c then Query.Ask 0 Query.Ret else Query.Side 2 true (Query.Ret true)).

Definition sample_static : System.static sample_system.
Proof.
  refine (System.Static (fun c : bool => if c then [0] else [])
    (fun c : bool => if c then [] else [2; 2]) _ _).
  - intros [] s x Hin; cbn in *; exact Hin.
  - intros [] s x Hin; cbn in *; intuition.
Defined.

Definition sample_index : sys_index nat bool :=
  index_system nat_encoding sample_system sample_static.

Example distinct_index_lists :
  contributors_of nat_encoding sample_index 2 = [false] /\
  readers_of nat_encoding sample_index 0 = [true] /\
  contributors_of nat_encoding sample_index 7 = [].
Proof.
  vm_compute; auto.
Qed.

Example full_checker_accepts : check_post bool_lattice sample_system (fun _ => true) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example full_checker_rejects_side :
  check_post bool_lattice sample_system (fun x => negb (Nat.eqb x 2)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition sample_certificate : cut_certificate nat bool :=
  CutCertificate (FinSet.of_list nat_encoding [0])
    (Map.of_list nat_encoding [(0, true); (99, true)]) [2; 1].

Definition sample_expansion :=
  expand nat_encoding bool_lattice sample_system sample_static sample_index sample_certificate.

Example cut_checker_accepts :
  option_map (fun m => map (lookup nat_encoding bool_lattice m) [0; 1; 2; 99])
    sample_expansion = Some [true; true; true; false].
Proof.
  vm_compute; reflexivity.
Qed.

Example no_cut_checker_accepts :
  option_map (fun m => map (lookup nat_encoding bool_lattice m) [0; 1; 2])
    (expand nat_encoding bool_lattice sample_system sample_static sample_index
      (CutCertificate FinSet.empty Map.empty [0; 2; 1])) = Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_checker_rejects_missing_value :
  expand nat_encoding bool_lattice sample_system sample_static sample_index
    (CutCertificate (FinSet.of_list nat_encoding [0]) Map.empty [2; 1]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_checker_rejects_bad_order :
  expand nat_encoding bool_lattice sample_system sample_static sample_index
    (CutCertificate FinSet.empty Map.empty [1; 0; 2]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_checker_rejects_duplicate :
  expand nat_encoding bool_lattice sample_system sample_static sample_index
    (CutCertificate (FinSet.of_list nat_encoding [0]) (stored sample_certificate) [2; 1; 2]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_checker_rejects_uncovered_output :
  expand nat_encoding bool_lattice sample_system sample_static sample_index
    (CutCertificate (FinSet.of_list nat_encoding [0]) (stored sample_certificate) [1]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition loop_system : System.t nat bool bool :=
  System.Make [false; true] (fun c : bool => if c then 1 else 0)
    (fun c : bool => if c then Query.Ask 0 (fun a => Query.Side 2 a (Query.Ret a))
      else Query.Ask 1 Query.Ret).

Definition loop_static : System.static loop_system.
Proof.
  refine (System.Static (fun c : bool => if c then [0] else [1])
    (fun c : bool => if c then [2] else []) _ _).
  - intros [] s x Hin; exact Hin.
  - intros [] s x Hin; exact Hin.
Defined.

Example cut_checker_accepts_loop :
  option_map (fun m => map (lookup nat_encoding bool_lattice m) [0; 1; 2])
    (expand nat_encoding bool_lattice loop_system loop_static
      (index_system nat_encoding loop_system loop_static)
      (CutCertificate (FinSet.of_list nat_encoding [0])
        (Map.set nat_encoding 0 true Map.empty) [1; 2])) = Some [true; true; true].
Proof.
  vm_compute; reflexivity.
Qed.

Example cut_checker_rejects_uncut_loop :
  expand nat_encoding bool_lattice loop_system loop_static
    (index_system nat_encoding loop_system loop_static)
    (CutCertificate FinSet.empty Map.empty [0; 1; 2]) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition empty_system : System.t nat bool bool :=
  System.Make [] (fun _ => 0) (fun _ => Query.Ret false).

Definition empty_static : System.static empty_system.
Proof.
  refine (System.Static (fun _ => []) (fun _ => []) _ _);
    intros c s x Hin; exact Hin.
Defined.

Example empty_checker_accepts :
  check_post bool_lattice empty_system (fun _ => false) = true /\
  expand nat_encoding bool_lattice empty_system empty_static
    (index_system nat_encoding empty_system empty_static)
    (CutCertificate FinSet.empty Map.empty []) = Some Map.empty.
Proof.
  vm_compute; auto.
Qed.

Example replay_visits_order :
  replay (fun acc x a => (x, a) :: acc) [] [2; 0; 1] (fun x => Nat.eqb x 0) =
    [(1, false); (0, true); (2, false)].
Proof.
  vm_compute; reflexivity.
Qed.

Example updates_skip_below :
  map (apply_updates nat_encoding bool_lattice [(0, false); (1, true); (1, false)]
    (fun _ => false)) [0; 1; 2] = [false; true; false].
Proof.
  vm_compute; reflexivity.
Qed.
