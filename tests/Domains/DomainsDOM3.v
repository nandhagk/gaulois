(** * Circular interval boundary computations

    These examples exercise normalization, joins, widening and both transfer directions.
    For example, truncating the eight-bit range [250, 255] to four bits yields [10, 15].
    Builds on: DomainsWrapped. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsOp.
From Gaulois.Domains Require Import DomainsNumeric DomainsWrapped.
Import List.ListNotations.

Local Open Scope Z_scope.
Local Abbreviation w8 := 8%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w16 := 16%positive.

Example wrapped_bottom_size : wrapped_size w8 WBot = 0.
Proof.
  reflexivity.
Qed.

Example wrapped_cross_zero_size : wrapped_size w8 (WItv 250 3) = 10.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_raw_endpoints : wrapped_norm w8 (WItv (-6) 259) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_normalization : wrapped_norm w8 (WItv 10 9) = WFull.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_equivalence : leb (wrapped_lattice w8) WFull (WItv 10 9) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_inside_cross_zero :
  leb (wrapped_lattice w8) (WItv 250 3) (WItv 240 5) = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_outside_cross_zero :
  leb (wrapped_lattice w8) (WItv 240 5) (WItv 250 3) = false.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_join_bottom : join (wrapped_lattice w8) WBot (WItv (-6) 259) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_join_across_zero :
  join (wrapped_lattice w8) (WItv 250 3) (WItv 4 8) = WItv 250 8.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_join_equal_candidates :
  join (wrapped_lattice w8) (WItv 0 0) (WItv 128 128) = WItv 0 128.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_join_covers_circle :
  join (wrapped_lattice w8) (WItv 0 200) (WItv 150 10) = WFull.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_widen_bottom : widen (wrapped_lattice w8) WBot (WItv 250 3) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_widen_doubles :
  widen (wrapped_lattice w8) (WItv 10 11) (WItv 10 12) = WItv 8 13.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_widen_stable :
  widen (wrapped_lattice w8) (WItv 250 3) (WItv 255 1) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_widen_full :
  widen (wrapped_lattice w8) (WItv 0 100) (WItv 100 101) = WFull.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_rank_progress :
  (wrank (base_wrank (wrapped_wrank w8)) (WItv 8 13) <
   wrank (base_wrank (wrapped_wrank w8)) (WItv 10 11))%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_single_arc :
  pmeet wrapped_domain w8 (WItv 250 3) (WItv 0 2) = WItv 0 2.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_two_arcs :
  pmeet wrapped_domain w8 (WItv 0 200) (WItv 150 50) = WItv 0 200.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_disjoint : pmeet wrapped_domain w8 (WItv 250 3) (WItv 10 20) = WBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_add_wrap :
  pforward wrapped_domain bvadd [(w8, WItv 250 255); (w8, WItv 1 7)] w8 =
  WItv 251 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_sub_wrap :
  pforward wrapped_domain bvsub [(w8, WItv 0 3); (w8, WItv 250 255)] w8 =
  WItv 1 9.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_neg_wrap :
  pforward wrapped_domain bvneg [(w8, WItv 250 3)] w8 = WItv 253 6.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_unsigned :
  pforward wrapped_domain bvmul [(w8, WItv 10 12); (w8, WItv 2 3)] w8 =
  WItv 20 36.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_signed :
  pforward wrapped_domain bvmul [(w8, WItv 250 255); (w8, WItv 2 3)] w8 =
  WItv 238 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_unsigned_zero_divisor :
  pforward wrapped_domain bvudiv [(w8, WItv 1 3); (w8, WItv 0 0)] w8 =
  WItv 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_division_cross_zero :
  pforward wrapped_domain bvsdiv [(w8, WItv 250 255); (w8, WItv 2 2)] w8 =
  WItv 253 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_remainder_cross_zero :
  pforward wrapped_domain bvsrem [(w8, WItv 250 255); (w8, WItv 2 2)] w8 =
  WItv 255 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_trunc_modular_span :
  pforward wrapped_domain (bvtrunc w4) [(w8, WItv 250 255)] w4 = WItv 10 15.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_zext :
  pforward wrapped_domain (bvzext w8) [(w8, WItv 250 255)] w16 = WItv 250 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_sext :
  pforward wrapped_domain (bvsext w8) [(w8, WItv 250 255)] w16 = WItv 65530 65535.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_unsigned_comparison :
  pforward wrapped_domain bvult [(w8, WItv 0 3); (w8, WItv 10 20)] w1 =
  WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_comparison :
  pforward wrapped_domain bvslt [(w8, WItv 250 3); (w8, WItv 10 20)] w1 =
  WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_unsigned_true :
  passume wrapped_domain bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
    (WItv 1 1) = [WItv 0 9; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_equal :
  passume wrapped_domain bveq [(w8, WItv 250 3); (w8, WItv 0 2)] w1
    (WItv 1 1) = [WItv 0 2; WItv 0 2].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_modular_add :
  passume wrapped_domain bvadd [(w8, WItv 250 3); (w8, WItv 10 10)] w8
    (WItv 5 5) = [WItv 251 251; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_sext :
  passume wrapped_domain (bvsext w8) [(w8, WItv 250 255)] w16
    (WItv 65532 65534) = [WItv 252 254].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_trunc_fitting :
  passume wrapped_domain (bvtrunc w4) [(w8, WItv 0 10)] w4
    (WItv 3 5) = [WItv 3 5].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_and_mask :
  pforward wrapped_domain bvand [(w8, WItv 240 255); (w8, WItv 15 15)] w8 = WItv 0 15.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_or_bound :
  pforward wrapped_domain bvor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_xor_bound :
  pforward wrapped_domain bvxor [(w8, WItv 1 2); (w8, WItv 4 4)] w8 = WItv 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_modulus_negative_divisor :
  pforward wrapped_domain bvsmod [(w8, WItv 3 3); (w8, WItv 254 254)] w8 = WItv 255 255.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_negative_division_by_zero :
  pforward wrapped_domain bvsdiv [(w8, WItv 250 255); (w8, WItv 0 0)] w8 = WItv 1 1.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_signed_division_bottom :
  pforward wrapped_domain bvsdiv [(w8, WBot); (w8, WItv 2 2)] w8 = WBot.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_ite_cover :
  pforward wrapped_domain bvite [(w1, WFull); (w8, WItv 250 3); (w8, WItv 4 8)] w8 =
  WItv 250 8.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_unsigned_false :
  passume wrapped_domain bvult [(w8, WItv 0 20); (w8, WItv 10 10)] w1
    (WItv 0 0) = [WItv 10 20; WItv 10 10].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_signed_true :
  passume wrapped_domain bvslt [(w8, WItv 250 20); (w8, WItv 255 255)] w1
    (WItv 1 1) = [WItv 250 254; WItv 255 255].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_modular_sub :
  passume wrapped_domain bvsub [(w8, WItv 250 3); (w8, WItv 250 250)] w8
    (WItv 5 5) = [WItv 255 255; WItv 250 250].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_zext :
  passume wrapped_domain (bvzext w8) [(w8, WItv 250 3)] w16
    (WItv 0 3) = [WItv 0 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_assume_impossible_signed :
  passume wrapped_domain bvslt [(w8, WItv 0 20); (w8, WItv 255 255)] w1
    (WItv 1 1) = [WBot; WBot].
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_rank : wrank (base_wrank (wrapped_wrank w8)) (WItv 10 9) = 0%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_narrow_full : narrow (wrapped_lattice w8) (WItv 10 9) (WItv 250 3) =
  WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_meet_full_neutral : pmeet wrapped_domain w8 WFull (WItv 250 3) = WItv 250 3.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_both_poles :
  pforward wrapped_domain bvmul [(w8, WItv 100 50); (w8, WItv 2 2)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_both_poles_right :
  pforward wrapped_domain bvmul [(w8, WItv 2 2); (w8, WItv 100 50)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_mul_full_by_two :
  pforward wrapped_domain bvmul [(w8, WFull); (w8, WItv 2 2)] w8 = WItv 0 254.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_parts :
  map (wrapped_parts w8) [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
  repeat (wrapped_parts w8 WFull) 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_sext :
  map (fun a => pforward wrapped_domain (bvsext w8) [(w8, a)] w16)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_zext :
  map (fun a => pforward wrapped_domain (bvzext w8) [(w8, a)] w16)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat (WItv 0 255) 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_trunc :
  map (fun a => pforward wrapped_domain (bvtrunc w4) [(w8, a)] w4)
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat WFull 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_assume_sext :
  map (fun a => passume wrapped_domain (bvsext w8) [(w8, a)] w16 (WItv 65532 65534))
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] = repeat [WItv 252 254] 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrapped_full_alias_assume_unsigned :
  map (fun a => passume wrapped_domain bvult [(w8, a); (w8, WItv 10 10)] w1 (WItv 1 1))
    [WFull; WItv 128 127; WItv 10 9; WItv (-128) 127] =
  repeat [WItv 0 9; WItv 10 10] 4.
Proof.
  vm_compute. reflexivity.
Qed.
