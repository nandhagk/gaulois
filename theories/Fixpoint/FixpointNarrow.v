(** * Checked simultaneous narrowing

    Each pass evaluates every constraint once against the previous assignment.
    For example, a candidate that decreases a value but breaks a constraint is discarded.
    Builds on: FixpointCheck, FixpointIndex and OrderLattice. *)

From Stdlib Require Import List Bool PArith Arith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck.
Import List.ListNotations.

(** Join one evaluated contribution into its destination's aggregate. *)
Definition narrow_collect {X A} (EX : encoding X) (L : lattice A)
    (acc : assignment X A) (xa : X * A) : assignment X A :=
  Map.set EX (fst xa) (join L (lookup EX L acc (fst xa)) (snd xa)) acc.

(** Run each constraint once, collecting its return followed by all its side contributions. *)
Definition narrow_contributions {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (m : assignment X A) : assignment X A :=
  fold_left (fun acc c =>
    let '(v, _, ss) := Query.run (System.rhs S c) (lookup EX L m) in
    fold_left (narrow_collect EX L) ((System.target S c, v) :: ss) acc)
    (System.constraints S) Map.empty.

(** An indexed output is narrowed only when its aggregate is below its old value. *)
Definition narrow_output {X A} (EX : encoding X) (L : lattice A)
    (m sums acc : assignment X A) (x : X) : assignment X A :=
  let old := lookup EX L m x in
  let a := lookup EX L sums x in
  Map.set EX x (if leb L a old then narrow L old a else old) acc.

(** Simultaneous narrowing reads the input only and retains every unindexed binding. *)
Definition narrow_pass {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (ix : sys_index X C) : assignment X A -> assignment X A :=
  let outputs := distinct_unknowns EX (flat_map (fun c =>
    System.target S c :: side_targets SS c) (System.constraints S)) in
  fun m =>
    let sums := narrow_contributions EX L S m in
    fold_left (fun acc x =>
      match contributors_of EX ix x with
      | [] => acc
      | _ :: _ => narrow_output EX L m sums acc x
      end) outputs m.

(** Keep a bounded candidate exactly when the full post-solution checker accepts it. *)
Definition narrow_checked {X C A} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) (ix : sys_index X C)
    (rounds : nat) (m : assignment X A) : assignment X A :=
  let m' := Nat.iter rounds (narrow_pass EX L S SS ix) m in
  if check_post L S (lookup EX L m') then m' else m.

Section NarrowLaws.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C).

Lemma narrow_output_below (HL : lattice_laws L) (m sums acc : assignment X A) :
  fun_leb L (lookup EX L acc) (lookup EX L m) -> forall x,
  fun_leb L (lookup EX L (narrow_output EX L m sums acc x)) (lookup EX L m).
Proof.
  intros Hacc x y; unfold narrow_output, lookup at 1.
  destruct (Pos.eqb (encode EX y) (encode EX x)) eqn:Heq.
  - apply Pos.eqb_eq in Heq; apply (encode_injective EX) in Heq; subst y.
    rewrite Map.get_set_same.
    destruct (leb L (lookup EX L sums x) (lookup EX L m x)) eqn:Hbelow.
    + apply (narrow_lower HL); exact Hbelow.
    + apply (leb_refl HL).
  - rewrite Map.get_set_other.
    + exact (Hacc y).
    + intro Hequal; subst y; rewrite Pos.eqb_refl in Heq; discriminate.
Qed.

Lemma narrow_outputs_below (HL : lattice_laws L) (m sums acc : assignment X A)
    (outputs : list X) :
  fun_leb L (lookup EX L acc) (lookup EX L m) ->
  fun_leb L (lookup EX L (fold_left (fun acc x =>
    match contributors_of EX ix x with
    | [] => acc
    | _ :: _ => narrow_output EX L m sums acc x
    end) outputs acc)) (lookup EX L m).
Proof.
  revert acc; induction outputs as [|x rest IH]; intros acc Hacc; cbn.
  - exact Hacc.
  - apply IH; destruct (contributors_of EX ix x);
      [exact Hacc|apply narrow_output_below; assumption].
Qed.

Lemma narrow_pass_below (HL : lattice_laws L) (m : assignment X A) :
  fun_leb L (lookup EX L (narrow_pass EX L S SS ix m)) (lookup EX L m).
Proof.
  unfold narrow_pass; apply (narrow_outputs_below HL); intro x; apply (leb_refl HL).
Qed.

Lemma narrow_rounds_below (HL : lattice_laws L) (rounds : nat) (m : assignment X A) :
  fun_leb L (lookup EX L (Nat.iter rounds (narrow_pass EX L S SS ix) m)) (lookup EX L m).
Proof.
  induction rounds as [|rounds IH]; cbn [Nat.iter].
  - intro x; apply (leb_refl HL).
  - intro x; eapply (leb_trans HL); [apply narrow_pass_below; exact HL|apply IH].
Qed.

(** An accepted candidate is a post-solution, and rejection retains the input proof. *)
Theorem narrow_checked_post (rounds : nat) (m : assignment X A) :
  post_solution L S (lookup EX L m) ->
  post_solution L S (lookup EX L (narrow_checked EX L S SS ix rounds m)).
Proof.
  intro Hpost; unfold narrow_checked.
  destruct (check_post L S (lookup EX L (Nat.iter rounds (narrow_pass EX L S SS ix) m)))
    eqn:Hcheck.
  - apply check_post_iff; exact Hcheck.
  - exact Hpost.
Qed.

(** Every bounded candidate decreases pointwise, as does the checked result. *)
Theorem narrow_checked_below (rounds : nat) (m : assignment X A) :
  lattice_laws L ->
  fun_leb L (lookup EX L (narrow_checked EX L S SS ix rounds m)) (lookup EX L m).
Proof.
  intro HL; unfold narrow_checked.
  destruct (check_post L S (lookup EX L (Nat.iter rounds (narrow_pass EX L S SS ix) m))).
  - apply narrow_rounds_below; exact HL.
  - intro x; apply (leb_refl HL).
Qed.

End NarrowLaws.
