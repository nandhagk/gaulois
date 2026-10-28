(** * Interval lattice examples

    These examples exercise basic hull, threshold and narrowing computations.
    For example, widening a finite endpoint can jump to a supplied threshold.
    Builds on: DomainsInterval and OrderLattice. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsOp.
From Gaulois.Domains Require Import DomainsInterval.
Import List.ListNotations.
Local Open Scope Z_scope.

Example interval_hull :
  join (interval_lattice []) (Itv (Fin 1) (Fin 3)) (Itv (Fin 2) (Fin 5)) =
  Itv (Fin 1) (Fin 5).
Proof.
  reflexivity.
Qed.

Example interval_thresholds :
  widen (interval_lattice [0; 10; 20]) (Itv (Fin 2) (Fin 4))
    (Itv (Fin 1) (Fin 12)) = Itv (Fin 0) (Fin 20).
Proof.
  reflexivity.
Qed.

Example interval_narrow_infinities :
  narrow (interval_lattice []) (Itv NegInf PosInf) (Itv (Fin 0) (Fin 8)) =
  Itv (Fin 0) (Fin 8).
Proof.
  reflexivity.
Qed.

Example interval_unsorted_thresholds :
  widen (interval_lattice [20; 0; 10; 10]) (Itv (Fin 8) (Fin 9))
    (Itv (Fin 7) (Fin 11)) = Itv (Fin 0) (Fin 20).
Proof.
  reflexivity.
Qed.

Example interval_duplicate_threshold_index :
  threshold_index [10; 10; 10] = ThresholdNode ThresholdEmpty 10 ThresholdEmpty.
Proof.
  reflexivity.
Qed.

Example interval_sorted_threshold_index :
  threshold_index [1; 2; 3] =
    ThresholdNode ThresholdEmpty 1
      (ThresholdNode ThresholdEmpty 2 (ThresholdNode ThresholdEmpty 3 ThresholdEmpty)).
Proof.
  reflexivity.
Qed.

Example interval_threshold_infinity :
  widen (interval_lattice [0; 10]) (Itv (Fin 0) (Fin 10))
    (Itv (Fin (-1)) (Fin 11)) = Itv NegInf PosInf.
Proof.
  reflexivity.
Qed.

Example interval_empty_meet :
  interval_meet (Itv (Fin 1) (Fin 2)) (Itv (Fin 3) (Fin 4)) = IBot.
Proof.
  reflexivity.
Qed.

Example interval_infinite_empty_meet :
  interval_meet (Itv PosInf PosInf) (Itv NegInf PosInf) = IBot /\
  interval_meet (Itv NegInf NegInf) (Itv NegInf PosInf) = IBot.
Proof.
  split; reflexivity.
Qed.

Example interval_rank_counts_duplicates :
  interval_rank [0; 0; 5] (Itv (Fin 1) (Fin 3)) = 5%nat.
Proof.
  reflexivity.
Qed.

Example interval_add_in_range :
  interval_add 8%positive (Itv (Fin 1) (Fin 4)) (Itv (Fin 2) (Fin 5)) =
  Itv (Fin 3) (Fin 9).
Proof.
  reflexivity.
Qed.

Example interval_add_wrap_fallback :
  interval_add 8%positive (Itv (Fin 250) (Fin 255)) (Itv (Fin 1) (Fin 2)) =
  Itv (Fin 0) (Fin 255).
Proof.
  reflexivity.
Qed.

Example interval_operand_clip :
  interval_meet (Itv NegInf PosInf) (interval_top 8%positive) =
  Itv (Fin 0) (Fin 255).
Proof.
  reflexivity.
Qed.

Example interval_assume_comparison :
  interval_assume_ult (Itv (Fin 0) (Fin 20)) (Itv (Fin 5) (Fin 10)) =
  (Itv (Fin 0) (Fin 9), Itv (Fin 5) (Fin 10)).
Proof.
  reflexivity.
Qed.

Example interval_comparison_decided :
  interval_ult (Itv (Fin 0) (Fin 3)) (Itv (Fin 5) (Fin 10)) = Itv (Fin 1) (Fin 1).
Proof.
  reflexivity.
Qed.

Example interval_forward_clips_operand :
  interval_forward bvadd [(8%positive, Itv NegInf (Fin 3));
                          (8%positive, Itv (Fin 2) (Fin 4))] 8%positive =
  Itv (Fin 2) (Fin 7).
Proof.
  reflexivity.
Qed.

Example interval_forward_empty :
  interval_forward bvadd [(8%positive, IBot); (8%positive, Itv NegInf PosInf)] 8%positive = IBot.
Proof.
  reflexivity.
Qed.

Example interval_assume_unsigned_false :
  interval_assume bvult [(8%positive, Itv (Fin 0) (Fin 20));
                         (8%positive, Itv (Fin 5) (Fin 10))] 1%positive
    (Itv (Fin 0) (Fin 0)) = [Itv (Fin 5) (Fin 20); Itv (Fin 5) (Fin 10)].
Proof.
  reflexivity.
Qed.

Example interval_signed_mod_singletons :
  interval_forward bvsmod [(8%positive, Itv (Fin 251) (Fin 251));
                           (8%positive, Itv (Fin 3) (Fin 3))] 8%positive =
  Itv (Fin 1) (Fin 1).
Proof.
  reflexivity.
Qed.

Example interval_signed_mod_positive_divisor :
  interval_forward bvsmod [(8%positive, Itv (Fin 251) (Fin 252));
                           (8%positive, Itv (Fin 2) (Fin 3))] 8%positive =
  Itv (Fin 0) (Fin 2).
Proof.
  reflexivity.
Qed.

Example interval_signed_shift :
  interval_forward bvashr [(8%positive, Itv (Fin 248) (Fin 252));
                           (8%positive, Itv (Fin 1) (Fin 2))] 8%positive =
  Itv (Fin 252) (Fin 255).
Proof.
  reflexivity.
Qed.

Example interval_signed_division_zero_and_minimum :
  interval_forward bvsdiv [(8%positive, Itv (Fin 128) (Fin 129));
                           (8%positive, Itv (Fin 0) (Fin 1))] 8%positive =
    Itv (Fin 1) (Fin 129) /\
  interval_forward bvsdiv [(8%positive, Itv (Fin 128) (Fin 129));
                           (8%positive, Itv (Fin 255) (Fin 255))] 8%positive =
    Itv (Fin 127) (Fin 128).
Proof.
  split; reflexivity.
Qed.

Example interval_signed_shift_saturation :
  interval_forward bvashr [(8%positive, Itv (Fin 248) (Fin 252));
                           (8%positive, Itv (Fin 7) (Fin 8))] 8%positive =
    Itv (Fin 255) (Fin 255) /\
  interval_forward bvashr [(8%positive, Itv (Fin 2) (Fin 4));
                           (8%positive, Itv (Fin 8) (Fin 9))] 8%positive =
    Itv (Fin 0) (Fin 0).
Proof.
  split; reflexivity.
Qed.

Example interval_signed_remainder_precision_gap :
  interval_forward bvsrem [(8%positive, Itv (Fin 5) (Fin 5));
                           (8%positive, Itv (Fin 2) (Fin 3))] 8%positive =
    Itv (Fin 0) (Fin 2) /\
  eval_op bvsrem [(8%positive, 5); (8%positive, 2)] = Some (8%positive, 1) /\
  eval_op bvsrem [(8%positive, 5); (8%positive, 3)] = Some (8%positive, 2).
Proof.
  repeat split; reflexivity.
Qed.
