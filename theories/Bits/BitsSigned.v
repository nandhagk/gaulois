(** * Signed word arithmetic

    The signed view connects two's-complement words with integer arithmetic.
    For example, the eight-bit word 255 has signed value -1.
    Builds on: BitsWord, BitsFun and BitsTestbit. *)

From Stdlib Require Import ZArith Bool Lia Ring.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit.

Open Scope Z_scope.

(** * Signed interpretations and comparison *)

(** Signed values stay in the symmetric two's-complement interval. *)
Theorem signed_range : forall w x, - half w <= signed w x < half w.
Proof.
  intros w x. pose proof (wrap_is_word w x) as Hrange.
  pose proof (modulus_half w). unfold signed, is_word in *.
  destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. lia.
  - apply Z.ltb_ge in Hlt. lia.
Qed.

Lemma lxor_pow2_low : forall a k, 0 <= k -> 0 <= a < 2 ^ k ->
  Z.lxor a (2 ^ k) = a + 2 ^ k.
Proof.
  intros a k Hk Ha. symmetry. apply Z.add_nocarry_lxor.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k i) as [<-|Hne].
  - assert (Hbit : Z.testbit a k = false).
    { rewrite <- (Z.mod_small a (2 ^ k) Ha) at 1.
      apply Z.mod_pow2_bits_high. lia. }
    now rewrite Hbit.
  - rewrite Z.pow2_bits_false by exact Hne. apply Bool.andb_false_r.
Qed.

Lemma wxor_half_value : forall w x, wxor w x (half w) = signed w x + half w.
Proof.
  intros w x. pose proof (half_pos w) as Hhalf.
  pose proof (modulus_half w) as Hmodulus.
  pose proof (wrap_is_word w x) as Hrange. unfold is_word in Hrange.
  unfold wxor. rewrite (wrap_id w (half w)) by (unfold is_word; lia).
  unfold signed. destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. apply lxor_pow2_low; [lia|exact (conj (proj1 Hrange) Hlt)].
  - apply Z.ltb_ge in Hlt.
    assert (Hlow : 0 <= wrap w x - half w < half w) by lia.
    assert (Hsplit : wrap w x = Z.lxor (wrap w x - half w) (half w)).
    { pose proof (lxor_pow2_low (wrap w x - half w) (Zpos w - 1) ltac:(lia) Hlow)
        as Hxor. fold (half w) in Hxor. rewrite Hxor. lia. }
    rewrite Hsplit at 1. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. lia.
Qed.

(** Flipping the sign bit biases signed order into unsigned order. *)
Theorem wslt_bias : forall w x y,
  wslt w x y = wult w (wxor w x (half w)) (wxor w y (half w)).
Proof.
  intros w x y. unfold wslt, wult.
  rewrite !wrap_id by apply wxor_is_word. rewrite !wxor_half_value.
  destruct (signed w x <? signed w y) eqn:Hsigned;
    destruct (signed w x + half w <? signed w y + half w) eqn:Hbiased;
    try reflexivity;
    apply Z.ltb_lt in Hsigned || apply Z.ltb_ge in Hsigned;
    apply Z.ltb_lt in Hbiased || apply Z.ltb_ge in Hbiased; lia.
Qed.

(** Wrapping a signed view recovers the original word. *)
Theorem wrap_signed : forall w x, wrap w (signed w x) = wrap w x.
Proof.
  intros w x. unfold signed. destruct (wrap w x <? half w).
  - apply wrap_wrap.
  - replace (wrap w x - modulus w) with (wrap w x + (-1) * modulus w) by ring.
    now rewrite wrap_add_modulus, wrap_wrap.
Qed.

(** Normalization does not change the signed interpretation. *)
Theorem signed_wrap : forall w x, signed w (wrap w x) = signed w x.
Proof.
  intros w x. unfold signed. now rewrite wrap_wrap.
Qed.

(** Every integer in the signed interval is its own signed interpretation. *)
Theorem signed_id : forall w z, - half w <= z < half w -> signed w z = z.
Proof.
  intros w z Hz. pose proof (half_pos w). pose proof (modulus_half w).
  destruct (Z_le_gt_dec 0 z) as [Hnonneg|Hneg].
  - unfold signed. rewrite wrap_id by (unfold is_word; lia).
    now rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hz)).
  - assert (Hwrap : wrap w z = z + modulus w).
    { unfold wrap. symmetry. apply Z.mod_unique with (q := -1).
      - left. lia.
      - ring. }
    unfold signed. rewrite Hwrap.
    rewrite (proj2 (Z.ltb_ge (z + modulus w) (half w)) ltac:(lia)). lia.
Qed.

(** Equal signed views identify the normalized words. *)
Theorem signed_inj : forall w x y,
  signed w x = signed w y -> wrap w x = wrap w y.
Proof.
  intros w x y Heq. rewrite <- (wrap_signed w x), <- (wrap_signed w y).
  now rewrite Heq.
Qed.

(** The sign bit is set exactly for negative signed values. *)
Theorem signed_neg_iff_msb : forall w x, signed w x < 0 <-> msb w x = true.
Proof.
  intros w x. rewrite msb_half. unfold signed.
  pose proof (wrap_is_word w x) as Hrange. unfold is_word in Hrange.
  destruct (wrap w x <? half w) eqn:Hlt.
  - change (wrap w x < 0 <-> false = true). split; [lia|discriminate].
  - change (wrap w x - modulus w < 0 <-> true = true). split; [reflexivity|lia].
Qed.

(** Word addition may use the signed interpretations of both operands. *)
Theorem wadd_signed : forall w x y,
  wadd w x y = wrap w (signed w x + signed w y).
Proof.
  intros w x y. unfold wadd. rewrite (wrap_add w x y),
    (wrap_add w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

(** Word subtraction may use the signed interpretations of both operands. *)
Theorem wsub_signed : forall w x y,
  wsub w x y = wrap w (signed w x - signed w y).
Proof.
  intros w x y. unfold wsub. rewrite (wrap_sub w x y),
    (wrap_sub w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

(** Equal sign bits make signed and unsigned strict comparisons agree. *)
Theorem wslt_wult : forall w x y,
  msb w x = msb w y -> wslt w x y = wult w x y.
Proof.
  intros w x y Hsign. rewrite !msb_half in Hsign. unfold wslt, wult, signed.
  destruct (wrap w x <? half w), (wrap w y <? half w); cbn in Hsign;
    try discriminate; [reflexivity|].
  destruct (wrap w x - modulus w <? wrap w y - modulus w) eqn:Hsigned;
    destruct (wrap w x <? wrap w y) eqn:Hunsigned; try reflexivity;
    apply Z.ltb_lt in Hsigned || apply Z.ltb_ge in Hsigned;
    apply Z.ltb_lt in Hunsigned || apply Z.ltb_ge in Hunsigned; lia.
Qed.

Lemma signed_nonnegative : forall w x, msb w x = false -> signed w x = wrap w x.
Proof.
  intros w x Hsign. rewrite msb_half in Hsign. unfold signed.
  destruct (wrap w x <? half w); [reflexivity|discriminate].
Qed.

Lemma signed_negative : forall w x, msb w x = true -> signed w x = - wneg w x.
Proof.
  intros w x Hsign. pose proof (signed_range w x) as Hrange.
  pose proof (proj2 (signed_neg_iff_msb w x) Hsign) as Hnegative.
  pose proof (modulus_half w). pose proof (half_pos w).
  assert (Hwrap : wrap w (- x) = wrap w (- signed w x)).
  { rewrite <- (wrap_opp w x), <- (wrap_opp w (signed w x)), wrap_signed.
    reflexivity. }
  unfold wneg. rewrite Hwrap, wrap_id by (unfold is_word; lia). lia.
Qed.

Lemma wneg_positive : forall w x, msb w x = true -> 0 < wneg w x.
Proof.
  intros w x Hsign. pose proof (proj2 (signed_neg_iff_msb w x) Hsign) as Hnegative.
  rewrite (signed_negative w x Hsign) in Hnegative. lia.
Qed.

(** * Signed division and remainders *)

Lemma wudiv_quot : forall w a b, wrap w b <> 0 ->
  wudiv w a b = wrap w (Z.quot (wrap w a) (wrap w b)).
Proof.
  intros w a b Hnz. pose proof (wrap_is_word w a) as Ha.
  pose proof (wrap_is_word w b) as Hb.
  assert (Hpos : 0 < wrap w b) by (unfold is_word in Hb; lia).
  unfold wudiv. rewrite (proj2 (Z.eqb_neq _ _) Hnz).
  rewrite Z.quot_div_nonneg by (try exact Hpos; exact (proj1 Ha)).
  symmetry. apply wrap_id. now apply word_div_is_word.
Qed.

Lemma rem_zero_r : forall a, Z.rem a 0 = a.
Proof.
  intros [|a|a]; reflexivity.
Qed.

Lemma wurem_rem : forall w a b,
  wurem w a b = wrap w (Z.rem (wrap w a) (wrap w b)).
Proof.
  intros w a b. unfold wurem. destruct (wrap w b =? 0) eqn:Hb.
  - apply Z.eqb_eq in Hb. rewrite Hb, rem_zero_r. symmetry. apply wrap_wrap.
  - apply Z.eqb_neq in Hb. pose proof (wrap_is_word w b) as Hrange.
    assert (Hpos : 0 < wrap w b) by (unfold is_word in Hrange; lia).
    rewrite Z.rem_mod_nonneg by (try exact Hpos; exact (proj1 (wrap_is_word w a))).
    symmetry. apply wrap_id. pose proof (Z.mod_pos_bound (wrap w a) (wrap w b) Hpos).
    unfold is_word in *. lia.
Qed.

(** Signed division agrees with truncating integer division for nonzero divisors. *)
Theorem wsdiv_signed : forall w x y, signed w y <> 0 ->
  wsdiv w x y = wrap w (Z.quot (signed w x) (signed w y)).
Proof.
  intros w x y Hnz. unfold wsdiv.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy.
  - rewrite (signed_negative w x Hx), (signed_negative w y Hy) in *.
    rewrite Z.quot_opp_opp by lia.
    rewrite wudiv_quot by (rewrite wrap_id by apply wrap_is_word; lia).
    now rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
  - rewrite (signed_negative w x Hx), (signed_nonnegative w y Hy) in *.
    rewrite Z.quot_opp_l by exact Hnz. unfold wneg at 1.
    rewrite wudiv_quot by exact Hnz. rewrite wrap_opp.
    now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
  - rewrite (signed_nonnegative w x Hx), (signed_negative w y Hy) in *.
    rewrite Z.quot_opp_r by lia. unfold wneg at 1.
    rewrite wudiv_quot by (rewrite wrap_id by apply wrap_is_word; lia).
    rewrite wrap_opp. now rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
  - rewrite (signed_nonnegative w x Hx), (signed_nonnegative w y Hy) in *.
    now apply wudiv_quot.
Qed.

(** Signed remainder agrees with truncating integer remainder, including zero divisors. *)
Theorem wsrem_signed : forall w x y,
  wsrem w x y = wrap w (Z.rem (signed w x) (signed w y)).
Proof.
  intros w x y. unfold wsrem.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy;
    rewrite ?(signed_negative w x Hx), ?(signed_negative w y Hy),
      ?(signed_nonnegative w x Hx), ?(signed_nonnegative w y Hy).
  - destruct (Z.eq_dec (wneg w y) 0) as [Hz|Hnz].
    + rewrite Hz, Z.opp_0, rem_zero_r, wurem_rem, !wrap_0, rem_zero_r.
      unfold wneg at 1. rewrite wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    + rewrite Z.rem_opp_opp by exact Hnz. unfold wneg at 1.
      rewrite wurem_rem, wrap_opp.
      now rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
  - destruct (Z.eq_dec (wrap w y) 0) as [Hz|Hnz].
    + rewrite Hz, rem_zero_r, wurem_rem, Hz, rem_zero_r.
      unfold wneg at 1. rewrite wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    + rewrite Z.rem_opp_l by exact Hnz. unfold wneg at 1.
      rewrite wurem_rem, wrap_opp.
      now rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
  - destruct (Z.eq_dec (wneg w y) 0) as [Hz|Hnz].
    + rewrite Hz, Z.opp_0, rem_zero_r, wurem_rem, wrap_0, rem_zero_r. reflexivity.
    + rewrite Z.rem_opp_r by exact Hnz. rewrite wurem_rem.
      now rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
  - apply wurem_rem.
Qed.

Lemma wurem_mod : forall w a b, wurem w a b = wrap w a mod wrap w b.
Proof.
  intros w a b. unfold wurem. destruct (wrap w b =? 0) eqn:Hb; [|reflexivity].
  apply Z.eqb_eq in Hb. now rewrite Hb, Z.mod_0_r.
Qed.

Lemma wrap_add_right : forall w a b, wrap w (a + b) = wrap w (a + wrap w b).
Proof.
  intros w a b. unfold wrap. symmetry. apply Z.add_mod_idemp_r. apply modulus_nonzero.
Qed.

Lemma wrap_add_left : forall w a b, wrap w (a + b) = wrap w (wrap w a + b).
Proof.
  intros w a b. unfold wrap. symmetry. apply Z.add_mod_idemp_l. apply modulus_nonzero.
Qed.

Lemma signed_zero : forall w, signed w 0 = 0.
Proof.
  intros w. apply signed_id. pose proof (half_pos w). lia.
Qed.

Lemma msb_zero : forall w, msb w 0 = false.
Proof.
  intros w. unfold msb. rewrite wrap_0. apply Z.bits_0.
Qed.

(** Signed division by zero follows the SMT-LIB sign-dependent total convention. *)
Theorem wsdiv_zero : forall w x,
  wsdiv w x 0 = if msb w x then 1 else modulus w - 1.
Proof.
  intros w x. unfold wsdiv. rewrite msb_zero. destruct (msb w x); [|].
  - unfold wneg at 1. unfold wudiv. rewrite wrap_0.
    change (wrap w (- (modulus w - 1)) = 1).
    replace (- (modulus w - 1)) with (1 + (-1) * modulus w) by ring.
    now rewrite wrap_add_modulus, wrap_1.
  - unfold wudiv. now rewrite wrap_0.
Qed.

(** Signed quotient and remainder reconstruct the dividend modulo the width. *)
Theorem wsdiv_wsrem_euclid : forall w x y,
  wadd w (wmul w y (wsdiv w x y)) (wsrem w x y) = wrap w x.
Proof.
  intros w x y. destruct (Z.eq_dec (signed w y) 0) as [Hz|Hnz].
  - assert (Hy : wrap w y = 0).
    { rewrite <- (wrap_signed w y), Hz. apply wrap_0. }
    rewrite wsrem_signed, Hz, rem_zero_r, wrap_signed.
    unfold wadd, wmul. rewrite (wrap_mul w y _), Hy, Z.mul_0_l, wrap_0, Z.add_0_l.
    apply wrap_wrap.
  - rewrite wsdiv_signed by exact Hnz. rewrite wsrem_signed.
    unfold wadd, wmul. rewrite (wrap_mul w y _), wrap_wrap.
    rewrite <- (wrap_signed w y), <- (wrap_mul w (signed w y) _).
    rewrite <- wrap_add.
    rewrite <- Z.quot_rem by exact Hnz. apply wrap_signed.
Qed.

Lemma wadd_wrapped_neg : forall w a y,
  wadd w (wneg w a) y = wrap w (wrap w y - a).
Proof.
  intros w a y. unfold wadd, wneg.
  rewrite <- wrap_add_left, wrap_add_right. f_equal. ring.
Qed.

Lemma wadd_signed_right : forall w a y,
  wadd w a y = wrap w (a + signed w y).
Proof.
  intros w a y. unfold wadd. rewrite (wrap_add_right w a y),
    (wrap_add_right w a (signed w y)), wrap_signed. reflexivity.
Qed.

(** Signed modulus agrees with flooring integer modulo, including zero divisors. *)
Theorem wsmod_signed : forall w x y,
  wsmod w x y = wrap w (Z.modulo (signed w x) (signed w y)).
Proof.
  intros w x y. unfold wsmod.
  destruct (msb w x) eqn:Hx; destruct (msb w y) eqn:Hy.
  - rewrite (signed_negative w x Hx), (signed_negative w y Hy).
    assert (Hnz : wneg w y <> 0) by (pose proof (wneg_positive w y Hy); lia).
    rewrite Z.mod_opp_opp by exact Hnz.
    rewrite (wurem_mod w (wneg w x) (wneg w y)).
    rewrite (wrap_id w (wneg w x)), (wrap_id w (wneg w y)) by apply wrap_is_word.
    destruct (wneg w x mod wneg w y =? 0) eqn:Hu.
    + apply Z.eqb_eq in Hu. rewrite Hu, Z.opp_0, wrap_0. reflexivity.
    + reflexivity.
  - rewrite (signed_negative w x Hx), (signed_nonnegative w y Hy).
    rewrite (wurem_mod w (wneg w x) (wrap w y)), wrap_wrap.
    rewrite (wrap_id w (wneg w x)) by apply wrap_is_word.
    destruct (Z.eq_dec (wrap w y) 0) as [Hz|Hnz].
    + rewrite Hz, !Z.mod_0_r.
      pose proof (wneg_positive w x Hx) as Hpositive.
      rewrite (proj2 (Z.eqb_neq (wneg w x) 0) ltac:(lia)), wadd_wrapped_neg, Hz.
      f_equal.
    + destruct (wneg w x mod wrap w y =? 0) eqn:Hu.
      * apply Z.eqb_eq in Hu. rewrite Z.mod_opp_l_z by assumption.
        rewrite Hu, wrap_0. reflexivity.
      * apply Z.eqb_neq in Hu. rewrite Z.mod_opp_l_nz by assumption.
        apply wadd_wrapped_neg.
  - rewrite (signed_nonnegative w x Hx), (signed_negative w y Hy).
    assert (Hnz : wneg w y <> 0) by (pose proof (wneg_positive w y Hy); lia).
    rewrite (wurem_mod w (wrap w x) (wneg w y)), wrap_wrap.
    rewrite (wrap_id w (wneg w y)) by apply wrap_is_word.
    destruct (wrap w x mod wneg w y =? 0) eqn:Hu.
    + apply Z.eqb_eq in Hu. rewrite Z.mod_opp_r_z by assumption.
      rewrite Hu, wrap_0. reflexivity.
    + apply Z.eqb_neq in Hu. rewrite Z.mod_opp_r_nz by assumption.
      rewrite wadd_signed_right, (signed_negative w y Hy). reflexivity.
  - rewrite (signed_nonnegative w x Hx), (signed_nonnegative w y Hy).
    pose proof (wurem_is_word w (wrap w x) (wrap w y)) as Hrange.
    rewrite wurem_mod, !wrap_wrap in Hrange |- *.
    destruct (wrap w x mod wrap w y =? 0); symmetry; now apply wrap_id.
Qed.

(** A nonzero signed modulus has the divisor's sign and a smaller magnitude. *)
Theorem wsmod_sign : forall w x y,
  (0 < signed w y -> 0 <= signed w (wsmod w x y) < signed w y) /\
  (signed w y < 0 -> signed w y < signed w (wsmod w x y) <= 0).
Proof.
  intros w x y. rewrite wsmod_signed, signed_wrap.
  pose proof (signed_range w y) as Hrange. pose proof (half_pos w) as Hhalf.
  split; intro Hy.
  - pose proof (Z.mod_pos_bound (signed w x) (signed w y) Hy) as Hmod.
    rewrite (signed_id w (signed w x mod signed w y)) by lia. exact Hmod.
  - pose proof (Z.mod_neg_bound (signed w x) (signed w y) Hy) as Hmod.
    rewrite (signed_id w (signed w x mod signed w y)) by lia. exact Hmod.
Qed.
