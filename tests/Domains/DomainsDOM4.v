(** * Congruence and product boundary examples

    Examples exercise congruence arithmetic, CRT meets and three word-product reductions.
    For example, the raw eight-bit constant 256 denotes an integer but no eight-bit word.
    Builds on: DomainsCongruence, DomainsConst, DomainsInterval and DomainsProduct. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderFlat OrderProduct OrderReduced.
From Gaulois.Bits Require Import BitsWord BitsOp.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst DomainsInterval DomainsCongruence
  DomainsProduct DomainsKnownBits DomainsWrapped.
Import List.ListNotations.

Open Scope Z_scope.

Definition dom4_const_exact (_ : width) (q : flat Z) : option Z :=
  match q with
  | FVal c => Some c
  | _ => None
  end.

Lemma dom4_const_meet_word : forall w c q, is_word w c ->
  pmeet const_domain w q (pconst const_domain w c) = const_meet q (FVal c).
Proof.
  intros w c q Hword; cbn; now rewrite (wrap_id w c Hword).
Qed.

(** The exact query remains lawful on raw nonwords and empty payloads. *)
Example dom4_const_exact_laws :
  const_reduction_laws const_domain const_gamma dom4_const_exact.
Proof.
  constructor.
  - intros w [|x|] c z He Hword Hmeaning; cbn in He, Hmeaning;
      try discriminate; inversion He; subst c; exact Hmeaning.
  - intros w [|x|] [|y|] c Hle He; cbn in Hle, He; try discriminate;
      try (left; reflexivity).
    apply Z.eqb_eq in Hle; subst y; inversion He; subst c; right; reflexivity.
  - intros w c [|x|] [|y|] Hword Hle;
      rewrite !dom4_const_meet_word by exact Hword;
      cbn in Hle; try discriminate; cbn; try reflexivity.
    + apply Z.eqb_eq in Hle; subst y.
      destruct (x =? c); cbn; auto using Z.eqb_refl.
    + destruct (x =? c) eqn:Hxc; cbn; [exact Hxc|reflexivity].
    + apply Z.eqb_refl.
  - intros w c [|x|] Hword; rewrite !dom4_const_meet_word by exact Hword; cbn.
    + reflexivity.
    + destruct (x =? c) eqn:Hxc; cbn; [rewrite Hxc; apply Z.eqb_refl|reflexivity].
    + now rewrite !Z.eqb_refl.
  - intros w c [|x|] Hword He; cbn in He; try discriminate.
    inversion He; subst x; rewrite dom4_const_meet_word by exact Hword.
    cbn; rewrite Z.eqb_refl; cbn; apply Z.eqb_refl.
  - intros w c [|x|] d Hword He Hneq; cbn in He; try discriminate.
    inversion He; subst x; rewrite dom4_const_meet_word by exact Hword.
    cbn; rewrite (proj2 (Z.eqb_neq d c) (not_eq_sym Hneq)); reflexivity.
Qed.

Definition dom4_reduce := reduce_const_with const_domain dom4_const_exact 8%positive.

Example dom4_compatible : dom4_reduce (FVal 7, FVal 7) = (FVal 7, FVal 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_conflicting : dom4_reduce (FVal 7, FVal 8) = (FBot, FBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_out_of_range_constant : dom4_reduce (FVal 256, FTop) = (FBot, FBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_out_of_range_exact : dom4_reduce (FTop, FVal 256) = (FBot, FBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_empty_payload : dom4_reduce (FVal 7, FBot) = (FBot, FBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_exact_refines : dom4_reduce (FTop, FVal 7) = (FVal 7, FVal 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_repeated :
  dom4_reduce (dom4_reduce (FTop, FVal 7)) = dom4_reduce (FTop, FVal 7).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_raw_nonword :
  gamma (product_gamma (payload_concretisation const_gamma 8%positive)
    (payload_concretisation const_gamma 8%positive)) (FVal 256, FTop) 256.
Proof.
  split; [reflexivity|exact I].
Qed.

Example dom4_product_nonword_empty : forall z,
  ~ product_pgamma const_gamma const_gamma 8%positive (FVal 256, FTop) z.
Proof.
  intros z [Hword [Hconstant _]]; cbn in Hconstant; subst z.
  change (0 <= 256 < 256) in Hword; lia.
Qed.

Example dom4_reduction_sound : reduction_sound
  (word_payload_concretisation const_gamma 8%positive)
  (word_payload_concretisation const_gamma 8%positive) dom4_reduce.
Proof.
  exact (proj1 (proj2 (reduce_const_with_laws 8%positive const_domain const_gamma
    dom4_const_exact const_word_laws dom4_const_exact_laws))).
Qed.

Example dom4_reduction_idempotent : forall pq,
  leb (product_lattice (flat_lattice Z.eqb) (flat_lattice Z.eqb))
    (dom4_reduce pq) (dom4_reduce (dom4_reduce pq)) = true.
Proof.
  apply (reduce_idempotent (proj1 (reduce_const_with_laws 8%positive const_domain
    const_gamma dom4_const_exact const_word_laws dom4_const_exact_laws))).
Qed.

Example dom4_cong_residue : cong_norm 8%positive (Cong 4 6) = Cong 4 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_negative_modulus : cong_norm 8%positive (Cong (-4) 6) = Cong 4 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_large_modulus : cong_norm 8%positive (Cong 512 1) = Cong 0 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_large_empty : cong_norm 8%positive (Cong 512 300) = CBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_raw_exact_empty : cong_norm 8%positive (Cong 0 256) = CBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_join : join (cong_lattice 8%positive) (Cong 0 3) (Cong 0 7) = Cong 4 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_meet_incompatible : cong_meet 8%positive (Cong 2 0) (Cong 2 1) = CBot.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_meet_compatible : cong_meet 8%positive (Cong 4 1) (Cong 6 3) = Cong 12 9.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_height : rank (base_height (cong_height 8%positive)) (Cong 1 0) = 10%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_add : cong_add 8%positive (Cong 4 1) (Cong 8 2) = Cong 4 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_cong_constant_mul : cong_mul 8%positive (Cong 0 17) (Cong 0 17) = Cong 0 33.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_round :
  reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 18), Cong 4 1) =
    (Itv (Fin 5) (Fin 17), Cong 4 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_singleton :
  reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 6), Cong 4 1) =
    (Itv (Fin 5) (Fin 5), Cong 0 5).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_incompatible :
  reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 3), Cong 4 1) = (IBot, CBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_unbounded :
  reduce_interval_cong 8%positive (Itv NegInf PosInf, Cong 4 1) =
    (Itv (Fin 1) (Fin 253), Cong 4 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_nonword :
  reduce_interval_cong 8%positive (Itv (Fin 300) (Fin 400), Cong 1 0) = (IBot, CBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_raw_empty :
  reduce_interval_cong 8%positive (Itv (Fin 12) (Fin 4), Cong 1 0) = (IBot, CBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_exact_conflict :
  reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 6), Cong 0 7) = (IBot, CBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_repeated :
  let pair := (Itv (Fin 2) (Fin 18), Cong 4 1) in
  reduce_interval_cong 8%positive (reduce_interval_cong 8%positive pair) =
    reduce_interval_cong 8%positive pair.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_interval_cong_direct_sound :
  product_pgamma interval_pgamma cong_gamma 8%positive
    (reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 18), Cong 4 1)) 9.
Proof.
  apply reduce_interval_cong_keeps; vm_compute; repeat split; congruence.
Qed.

Example dom4_interval_cong_point_monotone :
  leb (product_lattice (interval_lattice []) (cong_lattice 8%positive))
    (reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 6), Cong 4 1))
    (reduce_interval_cong 8%positive (Itv (Fin 2) (Fin 18), Cong 4 1)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_ceiling : product_tnum_ceiling 2%positive (Tnum 1 0) 1 = Some 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_floor : product_tnum_floor 2%positive (Tnum 1 0) 1 = Some 0.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_ceiling_empty : product_tnum_ceiling 2%positive (Tnum 1 1) 0 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_ceiling_above_range : product_tnum_ceiling 2%positive (Tnum 0 0) 4 = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_floor_below_range : product_tnum_floor 2%positive (Tnum 0 0) (-1) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_raw_masks : product_tnum_ceiling 2%positive (Tnum 5 4) 1 = Some 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_full_width2 :
  reduce_bits_wrapped 2%positive (Tnum 1 0, WFull) = (Tnum 1 0, WFull).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_full_representation :
  reduce_bits_wrapped 2%positive (Tnum 1 0, WItv 1 0) = (Tnum 1 0, WFull).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_contradictory_full :
  reduce_bits_wrapped 2%positive (Tnum 1 1, WFull) = (Tnum 3 3, WBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_empty_arc :
  reduce_bits_wrapped 2%positive (Tnum 0 0, WBot) = (Tnum 3 3, WBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_bottom_component :
  reduce_bits_wrapped 2%positive (Tnum 3 3, WItv 0 0) = (Tnum 3 3, WBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_width2_incomparable :
  wrapped_leb 2%positive (WItv 2 0) (WItv 0 2) = false /\
  wrapped_leb 2%positive (WItv 0 2) (WItv 2 0) = false.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dom4_bits_width2_left_monotone :
  leb (product_lattice (tnum_lattice 2%positive) (wrapped_lattice 2%positive))
    (Tnum 1 0, WItv 2 0) (Tnum 1 0, WFull) = true /\
  leb (product_lattice (tnum_lattice 2%positive) (wrapped_lattice 2%positive))
    (reduce_bits_wrapped 2%positive (Tnum 1 0, WItv 2 0))
    (reduce_bits_wrapped 2%positive (Tnum 1 0, WFull)) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dom4_bits_width2_right_monotone :
  leb (product_lattice (tnum_lattice 2%positive) (wrapped_lattice 2%positive))
    (Tnum 1 0, WItv 0 2) (Tnum 1 0, WFull) = true /\
  leb (product_lattice (tnum_lattice 2%positive) (wrapped_lattice 2%positive))
    (reduce_bits_wrapped 2%positive (Tnum 1 0, WItv 0 2))
    (reduce_bits_wrapped 2%positive (Tnum 1 0, WFull)) = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example dom4_bits_proper_round :
  reduce_bits_wrapped 4%positive (Tnum 1 0, WItv 3 11) = (Tnum 1 0, WItv 4 10).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_leading_exchange :
  reduce_bits_wrapped 4%positive (Tnum 1 0, WItv 4 7) = (Tnum 9 4, WItv 4 6).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_singleton :
  reduce_bits_wrapped 4%positive (Tnum 3 8, WItv 9 14) = (Tnum 3 12, WItv 12 12).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_wrapping_high_piece :
  reduce_bits_wrapped 4%positive (Tnum 3 8, WItv 9 4) = (Tnum 3 12, WItv 12 12).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_wrapping_low_piece :
  reduce_bits_wrapped 4%positive (Tnum 3 8, WItv 13 8) = (Tnum 7 8, WItv 8 8).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_wrapping_both_pieces :
  reduce_bits_wrapped 4%positive (Tnum 3 8, WItv 10 8) = (Tnum 3 8, WItv 12 8).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_no_compatible_word :
  reduce_bits_wrapped 4%positive (Tnum 3 8, WItv 13 7) = (Tnum 15 15, WBot).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_raw_arc :
  reduce_bits_wrapped 2%positive (Tnum 5 4, WItv (-2) 4) = (Tnum 5 4, WItv 2 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_one_bit :
  reduce_bits_wrapped 1%positive (Tnum 0 0, WItv 0 0) = (Tnum 1 0, WItv 0 0).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_wide_selector :
  product_tnum_ceiling 256%positive (Tnum 0 0) (2^200) = Some (2^200).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_wide_prefix :
  reduce_bits_wrapped 64%positive (Tnum 0 0, WItv 4 5) =
    (Tnum (modulus 64%positive - 6) 4, WItv 4 5).
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_two_rounds : forall w pair,
  reduce_bits_wrapped w pair = product_bits_round w (product_bits_round w pair).
Proof.
  reflexivity.
Qed.

Example dom4_bits_repeated :
  let pair := (Tnum 1 0, WItv 4 7) in
  reduce_bits_wrapped 4%positive (reduce_bits_wrapped 4%positive pair) =
    reduce_bits_wrapped 4%positive pair.
Proof.
  vm_compute; reflexivity.
Qed.

Example dom4_bits_direct_sound :
  product_pgamma tnum_gamma wrapped_gamma 4%positive
    (reduce_bits_wrapped 4%positive (Tnum 1 0, WItv 4 7)) 6.
Proof.
  unfold reduce_bits_wrapped; apply product_bits_round_sound, product_bits_round_sound.
  vm_compute; repeat split; congruence.
Qed.

Example dom4_bits_reduction_sound :
  reduction_sound (word_payload_concretisation tnum_gamma 4%positive)
    (word_payload_concretisation wrapped_gamma 4%positive) (reduce_bits_wrapped 4%positive).
Proof.
  exact (proj1 (proj2 (reduce_bits_wrapped_laws 4%positive))).
Qed.

Example dom4_bits_reduction_idempotent : forall pair,
  leb (product_lattice (tnum_lattice 4%positive) (wrapped_lattice 4%positive))
    (reduce_bits_wrapped 4%positive pair)
    (reduce_bits_wrapped 4%positive (reduce_bits_wrapped 4%positive pair)) = true.
Proof.
  apply (reduce_idempotent (proj1 (reduce_bits_wrapped_laws 4%positive))).
Qed.

(** The lawful exact query instantiates the generic product without additional assumptions. *)
Example dom4_const_product_word_laws :
  word_laws (const_product_domain const_domain dom4_const_exact)
    (product_pgamma const_gamma const_gamma).
Proof.
  apply product_word_laws; try apply const_word_laws.
  - intro w; exact (proj1 (reduce_const_with_laws w const_domain const_gamma
      dom4_const_exact const_word_laws dom4_const_exact_laws)).
  - intro w; exact (proj1 (proj2 (reduce_const_with_laws w const_domain const_gamma
      dom4_const_exact const_word_laws dom4_const_exact_laws))).
Qed.

Example dom4_const_product_forward :
  pforward (const_product_domain const_domain dom4_const_exact) bvadd
    [(8%positive, (FVal 3, FVal 3)); (8%positive, (FVal 4, FVal 4))] 8%positive =
    (FVal 7, FVal 7).
Proof.
  vm_compute; reflexivity.
Qed.
