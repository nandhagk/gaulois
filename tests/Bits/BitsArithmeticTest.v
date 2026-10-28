(** * Boundary examples for word arithmetic

    Computation exercises signed arithmetic, rotations, counts and changes of width.
    For example, dividing the signed minimum by minus one wraps back to the minimum.
    Builds on: BitsSigned, BitsArith, BitsExtend and BitsExpr. *)

From Stdlib Require Import ZArith List.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsExpr BitsSigned BitsArith BitsExtend.
Import List.ListNotations Bits.

Open Scope Z_scope.

(** The signed endpoints straddle the sign bit. *)
Example signed_minimum : signed 8%positive 128 = -128 /\ signed 8%positive 127 = 127.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Width one retains both distinct signed values. *)
Example signed_one_bit : signed 1%positive 1 = -1 /\ signed 1%positive 0 = 0.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** The only overflowing signed quotient wraps to the minimum. *)
Example signed_minimum_division : wsdiv 8%positive 128 255 = 128 /\ wsrem 8%positive 128 255 = 0.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Truncating signed division handles each negative-operand case. *)
Example signed_division_signs :
  wsdiv 8%positive 249 3 = 254 /\ wsdiv 8%positive 7 253 = 254 /\ wsdiv 8%positive 249 253 = 2.
Proof.
  vm_compute. split; [reflexivity|]. split; reflexivity.
Qed.

(** Signed remainder and modulus differ when the operand signs differ. *)
Example signed_remainder_and_modulus :
  wsrem 8%positive 249 3 = 255 /\ wsmod 8%positive 249 3 = 2 /\
  wsrem 8%positive 7 253 = 1 /\ wsmod 8%positive 7 253 = 254 /\ wsmod 8%positive 249 253 = 255.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; reflexivity.
Qed.

(** Both positive and negative dividends have defined zero-divisor results. *)
Example zero_divisors :
  wudiv 8%positive 7 0 = 255 /\ wurem 8%positive 7 0 = 7 /\
  wsdiv 8%positive 7 0 = 255 /\ wsdiv 8%positive 249 0 = 1 /\
  wsrem 8%positive 249 0 = 249 /\ wsmod 8%positive 249 0 = 249.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

(** Normalized zero divisors and exact negative division retain their special cases. *)
Example zero_after_normalization :
  wudiv 8%positive 7 256 = 255 /\ wsmod 8%positive 249 256 = 249 /\ wsmod 8%positive 250 3 = 0.
Proof.
  vm_compute. split; [reflexivity|]. split; reflexivity.
Qed.

(** Flipping the high bit converts a signed comparison into an unsigned comparison. *)
Example sign_bit_bias :
  wslt 8%positive 255 1 = true /\
  wult 8%positive (wxor 8%positive 255 128) (wxor 8%positive 1 128) = true.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Powers of two expose matching multiplication, division, shift and mask results. *)
Example powers_of_two :
  wmul 8%positive 173 8 = 104 /\ wshl 8%positive 173 3 = 104 /\
  wudiv 8%positive 173 8 = 21 /\ wlshr 8%positive 173 3 = 21 /\
  wurem 8%positive 173 8 = 5 /\ wand 8%positive 173 7 = 5.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

(** Zero, full-width and repeated rotation amounts obey the cyclic convention. *)
Example rotation_counts :
  wrotl 8%positive 129 0 = 129 /\ wrotl 8%positive 129 1 = 3 /\
  wrotl 8%positive 129 8 = 129 /\ wrotl 8%positive 129 17 = 3 /\ wrotr 8%positive 3 17 = 129.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; reflexivity.
Qed.

(** Rotation inverses also work at a width that is not a power of two. *)
Example rotation_non_power_width : wrotl 3%positive 5 2 = 6 /\ wrotr 3%positive 6 2 = 5.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Zero distinguishes leading and trailing counts from population count. *)
Example zero_counts : wclz 8%positive 0 = 8 /\ wctz 8%positive 0 = 8 /\ wpopcnt 8%positive 0 = 0.
Proof.
  vm_compute. split; [reflexivity|]. split; reflexivity.
Qed.

(** Nonzero count examples cover separated set bits and the sign bit alone. *)
Example nonzero_counts :
  wclz 8%positive 24 = 3 /\ wctz 8%positive 24 = 3 /\ wpopcnt 8%positive 24 = 2 /\
  wpopcnt 8%positive (wnot 8%positive 24) = 6 /\ wctz 8%positive 128 = 7.
Proof.
  vm_compute. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; reflexivity.
Qed.

(** Zero and sign extension give different larger unsigned representations. *)
Example extension_values :
  eval (env_of [(8%positive, 255)]) (App (bvzext 8%positive) [Var 0]) = Some (16%positive, 255) /\
  eval (env_of [(8%positive, 255)]) (App (bvsext 8%positive) [Var 0]) = Some (16%positive, 65535).
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Truncation recovers an extended word and commutes with an overflowing sum. *)
Example truncation_values :
  eval (env_of [(8%positive, 511)])
    (App (bvtrunc 8%positive) [App (bvsext 8%positive) [Var 0]]) = Some (8%positive, 255) /\
  eval (env_of [(8%positive, 250); (8%positive, 20)])
    (App (bvtrunc 4%positive) [App bvadd [Var 0; Var 1]]) = Some (4%positive, 14).
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Unequal operand widths discriminate the high and low concatenation parts. *)
Example concat_parts :
  eval (env_of [(3%positive, 5); (5%positive, 19)])
    (App (bvextract 7 5) [App bvconcat [Var 0; Var 1]]) = Some (3%positive, 5) /\
  eval (env_of [(3%positive, 5); (5%positive, 19)])
    (App (bvtrunc 5%positive) [App bvconcat [Var 0; Var 1]]) = Some (5%positive, 19).
Proof.
  vm_compute. split; reflexivity.
Qed.
