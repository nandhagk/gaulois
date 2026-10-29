(** * Known-bit boundary computations

    These examples distinguish normalized masks, carry propagation and multiplication precision.
    For example, the two possible values seven and fifteen become eight and sixteen after addition.
    Builds on: DomainsKnownBits and Bits word operations. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp.
From Gaulois.Domains Require Import DomainsNumeric DomainsKnownBits.
Import List.ListNotations.

Open Scope Z_scope.

(** High garbage bits do not change the known-bit preorder. *)
Example tnum_masks_modulo :
  leb (tnum_lattice 8%positive) (Tnum (-16) 257) (Tnum 240 1) = true /\
  leb (tnum_lattice 8%positive) (Tnum 240 1) (Tnum (-16) 257) = true.
Proof.
  vm_compute. auto.
Qed.

(** A local conflict really excludes concrete values even when it is not the lattice bottom. *)
Example tnum_conflicting_bit : ~ tnum_gamma 8%positive (Tnum 1 1) 0.
Proof.
  vm_compute. intros [_ Hbad]. discriminate.
Qed.

(** A carry through three known one bits exposes uncertainty in the fourth and fifth bits. *)
Example tnum_carry_propagation :
  tnum_add 8%positive (Tnum 240 7) (tnum_const 8%positive 1) = Tnum 231 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Borrow propagation preserves all bits outside the affected low nibble. *)
Example tnum_borrow_propagation :
  tnum_sub 8%positive (Tnum 246 8) (tnum_const 8%positive 1) = Tnum 240 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Constant multiplication retains every product bit. *)
Example tnum_constant_multiplication :
  tnum_mul 8%positive (tnum_const 8%positive 3) (tnum_const 8%positive 7) = Tnum 234 21.
Proof.
  vm_compute. reflexivity.
Qed.

(** Nonconstant multiplication retains the sum of the operands' trailing zero counts. *)
Example tnum_nonconstant_multiplication :
  tnum_mul 8%positive (Tnum 3 0) (Tnum 1 0) = Tnum 7 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** A contradictory operand makes the integrated transfer empty. *)
Example tnum_forward_conflicting_masks :
  pforward known_bits_domain bvadd [(8%positive, Tnum 1 1);
    (8%positive, tnum_const 8%positive 1)] 8%positive = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

(** Contradictory amount masks are rejected before the factored shift stages. *)
Example tnum_shift_conflicting_amount :
  pforward known_bits_domain bvshl [(8%positive, tnum_top); (8%positive, Tnum 1 1)]
    8%positive = Tnum 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

(** Four allowed shift amounts retain the common high zero bits. *)
Example tnum_variable_logical_shift :
  pforward known_bits_domain bvshl [(8%positive, tnum_const 8%positive 1);
    (8%positive, Tnum 252 0)] 8%positive = Tnum 240 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** The high unknown amount bit contributes the single saturated logical result. *)
Example tnum_variable_oversized_shift :
  pforward known_bits_domain bvlshr [(8%positive, tnum_const 8%positive 128);
    (8%positive, Tnum 247 0)] 8%positive = Tnum 127 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Arithmetic right shifts preserve the common sign and low fill information. *)
Example tnum_variable_arithmetic_shift :
  pforward known_bits_domain bvashr [(8%positive, tnum_const 8%positive 128);
    (8%positive, Tnum 252 0)] 8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

(** An unknown oversized arithmetic shift joins the all-sign-bits result. *)
Example tnum_variable_arithmetic_oversized :
  pforward known_bits_domain bvashr [(8%positive, tnum_const 8%positive 128);
    (8%positive, Tnum 247 0)] 8%positive = Tnum 0 128.
Proof.
  vm_compute. reflexivity.
Qed.

(** A known oversized amount is guarded before exponentiation. *)
Example tnum_oversized_base :
  pforward known_bits_domain bvshl [(8%positive, tnum_top);
    (8%positive, tnum_const 8%positive 255)] 8%positive = Tnum 255 0 /\
  pforward known_bits_domain bvashr [(8%positive, Tnum 128 0);
    (8%positive, tnum_const 8%positive 255)] 8%positive = Tnum 255 0.
Proof.
  vm_compute. auto.
Qed.

(** Amount masks are wrapped, so a garbage bit above the width does not request a shift. *)
Example tnum_wrapped_amount :
  pforward known_bits_domain bvshl [(8%positive, Tnum 15 128);
    (8%positive, tnum_const 8%positive 256)] 8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

(** Higher amount bits remain relevant when the rotation width is not a power of two. *)
Example tnum_rotation_nonpower_width :
  pforward known_bits_domain bvrotl [(5%positive, tnum_const 5%positive 1);
    (5%positive, Tnum 15 0)] 5%positive = Tnum 28 0 /\
  pforward known_bits_domain bvrotr [(5%positive, tnum_const 5%positive 1);
    (5%positive, Tnum 15 0)] 5%positive = Tnum 14 0.
Proof.
  vm_compute. auto.
Qed.

(** Every one-bit rotation is the identity, even with a fully unknown count. *)
Example tnum_rotation_width_one :
  pforward known_bits_domain bvrotl [(1%positive, tnum_const 1%positive 1);
    (1%positive, tnum_top)] 1%positive = Tnum 0 1 /\
  pforward known_bits_domain bvrotr [(1%positive, tnum_const 1%positive 1);
    (1%positive, tnum_top)] 1%positive = Tnum 0 1.
Proof.
  vm_compute. auto.
Qed.

(** Logical shifts at width one still distinguish zero and one counts. *)
Example tnum_shift_width_one :
  pforward known_bits_domain bvshl [(1%positive, tnum_const 1%positive 1);
    (1%positive, tnum_top)] 1%positive = Tnum 0 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** The forward rule retains leading zeros only when unsigned division cannot divide by zero. *)
Example tnum_division_zero_boundary :
  pforward known_bits_domain bvudiv [(8%positive, Tnum 240 0);
    (8%positive, tnum_const 8%positive 0)] 8%positive = tnum_top /\
  pforward known_bits_domain bvudiv [(8%positive, Tnum 240 0);
    (8%positive, Tnum 0 1)] 8%positive = Tnum 240 0 /\
  pforward known_bits_domain bvurem [(8%positive, Tnum 240 0);
    (8%positive, tnum_const 8%positive 0)] 8%positive = Tnum 240 0.
Proof.
  vm_compute. auto.
Qed.

(** Nonnegative signed remainders retain the sign-bit zero fact. *)
Example tnum_signed_remainder_sign :
  pforward known_bits_domain bvsrem [(8%positive, Tnum 128 0);
    (8%positive, tnum_top)] 8%positive = Tnum 128 0 /\
  pforward known_bits_domain bvsdiv [(8%positive, tnum_const 8%positive 7);
    (8%positive, tnum_const 8%positive 2)] 8%positive = tnum_top.
Proof.
  vm_compute. auto.
Qed.

(** Counts on zero keep their specified wrapped result, including the width-one boundary. *)
Example tnum_zero_counts :
  eval_op bvclz [(1%positive, 0)] = Some (1%positive, 1) /\
  eval_op bvctz [(1%positive, 0)] = Some (1%positive, 1) /\
  pforward known_bits_domain bvclz [(5%positive, tnum_const 5%positive 0)]
    5%positive = Tnum 24 0 /\
  pforward known_bits_domain bvpopcnt [(8%positive, tnum_top)] 8%positive = Tnum 240 0.
Proof.
  vm_compute. auto.
Qed.

(** Highest known differing bits decide unsigned and signed comparisons. *)
Example tnum_comparison_precision :
  pforward known_bits_domain bvult [(8%positive, Tnum 128 0);
    (8%positive, tnum_const 8%positive 128)] 1%positive = Tnum 0 1 /\
  pforward known_bits_domain bvslt [(8%positive, Tnum 0 128);
    (8%positive, Tnum 128 0)] 1%positive = Tnum 0 1 /\
  pforward known_bits_domain bveq [(8%positive, Tnum 1 0);
    (8%positive, Tnum 0 1)] 1%positive = Tnum 1 0.
Proof.
  vm_compute. auto.
Qed.

(** Conditional selection retains the chosen branch's exact masks. *)
Example tnum_conditional_precision :
  pforward known_bits_domain bvite [(1%positive, tnum_const 1%positive 1);
    (8%positive, Tnum 15 128); (8%positive, tnum_top)] 8%positive = Tnum 15 128.
Proof.
  vm_compute. reflexivity.
Qed.

(** Width changes copy exactly the corresponding mask bits. *)
Example tnum_width_change_precision :
  pforward known_bits_domain (bvzext 4%positive) [(4%positive, Tnum 8 1)]
    8%positive = Tnum 248 1 /\
  pforward known_bits_domain (bvsext 4%positive) [(4%positive, Tnum 0 8)]
    8%positive = Tnum 0 248 /\
  pforward known_bits_domain (bvtrunc 4%positive) [(8%positive, Tnum 128 1)]
    4%positive = Tnum 0 1 /\
  pforward known_bits_domain (bvextract 5 2) [(8%positive, Tnum 24 4)]
    4%positive = Tnum 6 1 /\
  pforward known_bits_domain bvconcat [(3%positive, Tnum 2 4); (2%positive, Tnum 1 2)]
    5%positive = Tnum 9 18.
Proof.
  vm_compute. auto.
Qed.

(** An arithmetic result with a constant operand refines the other operand to its inverse. *)
Example tnum_assume_add_constant :
  passume known_bits_domain bvadd [(8%positive, tnum_top);
    (8%positive, tnum_const 8%positive 1)] 8%positive (tnum_const 8%positive 7) =
    [Tnum 249 6; Tnum 254 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** Arithmetic sign fill projects a known high result bit back even for an oversized shift. *)
Example tnum_assume_sign_fill :
  passume known_bits_domain bvashr [(8%positive, tnum_top);
    (8%positive, tnum_const 8%positive 8)] 8%positive (tnum_const 8%positive 255) =
    [Tnum 0 128; Tnum 247 8].
Proof.
  vm_compute. reflexivity.
Qed.

(** Strict unsigned bounds project the leading zero bits implied by the comparison. *)
Example tnum_assume_unsigned_comparison :
  passume known_bits_domain bvult [(8%positive, tnum_top);
    (8%positive, tnum_const 8%positive 8)] 1%positive (tnum_const 1%positive 1) =
    [Tnum 248 0; Tnum 247 8].
Proof.
  vm_compute. reflexivity.
Qed.

(** Concatenation projects result bits into the two correctly sized source facts. *)
Example tnum_assume_concat :
  passume known_bits_domain bvconcat [(3%positive, tnum_top); (2%positive, tnum_top)]
    5%positive (tnum_const 5%positive 21) = [Tnum 2 5; Tnum 2 1].
Proof.
  vm_compute. reflexivity.
Qed.

(** The tagged facade rejects malformed operand widths before dispatch. *)
Example tnum_malformed_width :
  forward (tagged_domain known_bits_domain) bvadd
    [TVal 8%positive tnum_top; TVal 4%positive tnum_top] = TBot.
Proof.
  vm_compute. reflexivity.
Qed.

(** Variable-shift projection intersects the inverse copied bits without inventing fill facts. *)
Example tnum_assume_variable_shift :
  passume known_bits_domain bvshl [(8%positive, tnum_top); (8%positive, Tnum 254 0)]
    8%positive (tnum_const 8%positive 3) = [Tnum 124 1; Tnum 254 0] /\
  passume known_bits_domain bvashr [(8%positive, tnum_top); (8%positive, tnum_top)]
    8%positive (Tnum 0 128) = [Tnum 0 128; Tnum 0 0].
Proof.
  vm_compute. auto.
Qed.

(** Backward rotations also retain the high unknown amount bits at non-power-of-two widths. *)
Example tnum_assume_variable_rotation :
  passume known_bits_domain bvrotl [(5%positive, tnum_top); (5%positive, Tnum 15 0)]
    5%positive (tnum_const 5%positive 1) = [Tnum 14 0; Tnum 15 0].
Proof.
  vm_compute. reflexivity.
Qed.

(** Bitwise result bits refine both operands, including bits conditioned on the other operand. *)
Example tnum_assume_bitwise :
  passume known_bits_domain bvand [(8%positive, tnum_top); (8%positive, Tnum 0 2)]
    8%positive (Tnum 2 1) = [Tnum 2 1; Tnum 0 3] /\
  passume known_bits_domain bvor [(8%positive, tnum_top); (8%positive, Tnum 2 0)]
    8%positive (Tnum 1 2) = [Tnum 1 2; Tnum 3 0].
Proof.
  vm_compute. auto.
Qed.

(** Extension sign copies and extraction offsets return facts at the original operand width. *)
Example tnum_assume_width_changes :
  passume known_bits_domain (bvsext 4%positive) [(4%positive, tnum_top)]
    8%positive (Tnum 0 128) = [Tnum 0 8] /\
  passume known_bits_domain (bvextract 4 2) [(8%positive, tnum_top)]
    3%positive (tnum_const 3%positive 5) = [Tnum 8 20] /\
  passume known_bits_domain (bvtrunc 4%positive) [(8%positive, tnum_top)]
    4%positive (tnum_const 4%positive 3) = [Tnum 12 3].
Proof.
  vm_compute. auto.
Qed.

(** Equality meets both facts and subtraction uses the inverse constant arithmetic. *)
Example tnum_assume_equality_and_subtraction :
  passume known_bits_domain bveq [(8%positive, Tnum 15 0); (8%positive, Tnum 0 128)]
    1%positive (tnum_const 1%positive 1) = [Tnum 15 128; Tnum 15 128] /\
  passume known_bits_domain bvsub [(8%positive, tnum_top);
    (8%positive, tnum_const 8%positive 1)] 8%positive (tnum_const 8%positive 7) =
    [Tnum 247 8; Tnum 254 1].
Proof.
  vm_compute. auto.
Qed.
