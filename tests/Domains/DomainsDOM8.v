(** * Precise known-bit multiplication computations

    These examples check partial products, carries, contradictory masks and width truncation.
    For example, four times an unknown low bit is either zero or four, with seven known zero bits.
    Builds on: DomainsKnownBitsFast and the existing known-bit domain. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp.
From Gaulois.Domains Require Import DomainsNumeric DomainsKnownBits DomainsKnownBitsFast.
Import List.ListNotations.

Open Scope Z_scope.

(** A zero multiplicand remains zero through every unknown multiplier choice. *)
Example tnum_precise_zero_left :
  tnum_mul_precise 8%positive (tnum_const 8%positive 0) tnum_top = Tnum 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A zero multiplier leaves the initial accumulator unchanged. *)
Example tnum_precise_zero_right :
  tnum_mul_precise 8%positive tnum_top (tnum_const 8%positive 0) = Tnum 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** One unknown multiplier bit selects either zero or a single shifted constant. *)
Example tnum_precise_unknown_bit :
  tnum_mul_precise 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 251 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A known-one stage followed by an unknown stage joins three with nine. *)
Example tnum_precise_known_and_unknown :
  tnum_mul_precise 8%positive (tnum_const 8%positive 3) (Tnum 252 1) = Tnum 244 1.
Proof.
  vm_compute. reflexivity.
Qed.

(** Adding a shifted partial product propagates carries before the unknown-bit join. *)
Example tnum_precise_carry :
  tnum_mul_precise 8%positive (tnum_const 8%positive 7) (Tnum 252 1) = Tnum 232 5.
Proof.
  vm_compute. reflexivity.
Qed.

(** A known-one multiplier bit shifts the multiplicand's partial information. *)
Example tnum_precise_known_multiplier :
  tnum_mul_precise 8%positive (Tnum 252 1) (tnum_const 8%positive 2) = Tnum 249 2.
Proof.
  vm_compute. reflexivity.
Qed.

(** A conflict in the multiplicand returns the canonical bottom, even with a zero multiplier. *)
Example tnum_precise_conflicting_left :
  tnum_mul_precise 8%positive (Tnum 1 1) (tnum_const 8%positive 0) =
    bot (tnum_lattice 8%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** A conflict in the multiplier is rejected before processing its bits. *)
Example tnum_precise_conflicting_right :
  tnum_mul_precise 8%positive tnum_top (Tnum 128 128) = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

(** Shifted bits beyond the result width are discarded at each stage. *)
Example tnum_precise_truncated_unknown :
  tnum_mul_precise 8%positive (tnum_const 8%positive 128) (Tnum 252 1) = Tnum 127 128.
Proof.
  vm_compute. reflexivity.
Qed.

(** Constant addition wraps an overflowing partial-product sum. *)
Example tnum_precise_constant_overflow :
  tnum_mul_precise 8%positive (tnum_const 8%positive 200) (tnum_const 8%positive 3) =
    Tnum 167 88.
Proof.
  vm_compute. reflexivity.
Qed.

(** Arbitrary integer constants are normalized before their exact word product. *)
Example tnum_precise_wrapped_constants :
  tnum_mul_precise 8%positive (tnum_const 8%positive (-1)) (tnum_const 8%positive 258) =
    Tnum 1 254.
Proof.
  vm_compute. reflexivity.
Qed.

(** The loop works at a non-power-of-two width. *)
Example tnum_precise_three_bits :
  tnum_mul_precise 3%positive (tnum_const 3%positive 5) (Tnum 6 0) = Tnum 2 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A single-bit word still processes its only multiplier bit. *)
Example tnum_precise_one_bit :
  tnum_mul_precise 1%positive (tnum_const 1%positive 1) tnum_top = Tnum 0 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Negative and oversized masks retain their width-normalized interpretation. *)
Example tnum_precise_normalized_masks :
  tnum_mul_precise 8%positive (tnum_const 8%positive 4) (Tnum (-2) 256) = Tnum 251 0 /\
  tnum_mul_precise 8%positive (Tnum 256 256) (tnum_const 8%positive 0) = Tnum 255 0.
Proof.
  vm_compute. auto.
Qed.

(** Precise partial products retain high zeros discarded by the trailing-zero transfer. *)
Example tnum_precise_improves_trailing_zeros :
  tnum_mul 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 3 0 /\
  tnum_mul_precise 8%positive (tnum_const 8%positive 4) (Tnum 254 0) = Tnum 251 0 /\
  leb (tnum_lattice 8%positive) (Tnum 251 0) (Tnum 3 0) = true /\
  leb (tnum_lattice 8%positive) (Tnum 3 0) (Tnum 251 0) = false.
Proof.
  vm_compute. auto.
Qed.

(** The selected domain uses the precise transfer for a well-formed multiplication. *)
Example tnum_precise_selected_transfer :
  pforward known_bits_precise_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 8%positive =
    Tnum 251 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Another operator keeps the existing known-bit transfer. *)
Example tnum_precise_preserves_addition :
  pforward known_bits_precise_domain bvadd
    [(8%positive, Tnum 240 7); (8%positive, tnum_const 8%positive 1)] 8%positive =
    Tnum 231 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A mismatched result width keeps the original domain's fallback. *)
Example tnum_precise_preserves_invalid_width :
  pforward known_bits_precise_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive =
  pforward known_bits_domain bvmul
    [(8%positive, tnum_const 8%positive 4); (8%positive, Tnum 254 0)] 4%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Multiplication with the wrong arity also keeps the original domain's fallback. *)
Example tnum_precise_preserves_invalid_arity :
  pforward known_bits_precise_domain bvmul [(8%positive, tnum_top)] 8%positive =
  pforward known_bits_domain bvmul [(8%positive, tnum_top)] 8%positive.
Proof.
  vm_compute. reflexivity.
Qed.
