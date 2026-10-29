(** * Demanded-bit boundary examples

    These examples compute the masks at operation boundaries. For example, a large arithmetic
    shift demands the sign bit, while a large logical shift demands no data bits.
    Builds on: DomainsDemanded, BitsOp, OrderLattice. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsOp.
From Gaulois.Domains Require Import DomainsDemanded.
Import List.ListNotations.

Open Scope Z_scope.

Example demand_zero_add : demand bvadd [8; 8]%positive [None; None] 0 = [0; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_zero_conditional :
  demand bvite [1; 8; 8]%positive [None; None; None] 0 = [0; 0; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_ignored_high_bits : demand bvxor [8; 8]%positive [] 256 = [0; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_add_carries : demand bvadd [8; 8]%positive [] 40 = [63; 63].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_and_constants :
  demand bvand [8; 8]%positive [Some 170; Some 15] 255 = [15; 170].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_or_constants :
  demand bvor [8; 8]%positive [Some 170; Some 15] 255 = [240; 85].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_ashr_sign_fill :
  demand bvashr [8; 8]%positive [None; Some 3] 224 = [128; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_ashr_mixed :
  demand bvashr [8; 8]%positive [None; Some 3] 33 = [136; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_ashr_large :
  demand bvashr [8; 8]%positive [None; Some 255] 1 = [128; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_lshr_large :
  demand bvlshr [8; 8]%positive [None; Some 8] 255 = [0; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_wrapped_amount :
  demand bvshl [8; 8]%positive [None; Some 257] 128 = [64; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_variable_left : demand bvshl [8; 8]%positive [] 16 = [31; 255].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_variable_right : demand bvashr [8; 8]%positive [] 16 = [240; 255].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_rotate_left :
  demand bvrotl [8; 8]%positive [None; Some 1] 1 = [128; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_rotate_right :
  demand bvrotr [8; 8]%positive [None; Some 1] 128 = [1; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_rotate_non_power_width :
  demand bvrotl [3; 3]%positive [None; Some 5] 1 = [2; 0].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_unknown_rotation : demand bvrotl [8; 8]%positive [] 1 = [255; 255].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_sign_extension : demand (bvsext 8) [8]%positive [] 256 = [128].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_concat : demand bvconcat [8; 8]%positive [] 385 = [1; 129].
Proof.
  vm_compute. reflexivity.
Qed.

Example demand_conditional : demand bvite [1; 8; 8]%positive [] 129 = [1; 129; 129].
Proof.
  vm_compute. reflexivity.
Qed.

Example mask_inclusion_ignores_high : leb (mask_lattice 8%positive) 257 1 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example mask_inclusion_rejects_missing : leb (mask_lattice 8%positive) 3 1 = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example mask_population_rank : rank (base_height (mask_height 8%positive)) 257 = 1%nat.
Proof.
  vm_compute. reflexivity.
Qed.
