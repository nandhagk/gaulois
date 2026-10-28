(** * Unsigned arithmetic and bit counts

    Unsigned operations agree with integer division and modular multiplication.
    For example, dividing an eight-bit word by zero gives 255.
    Builds on: BitsWord, BitsFun, BitsTestbit and BitsSigned. *)

From Stdlib Require Import ZArith List Bool Lia Ring.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsSigned.

Open Scope Z_scope.

(** * Unsigned division and powers of two *)

(** Unsigned division by zero gives the all-ones word. *)
Theorem wudiv_zero : forall w x, wudiv w x 0 = modulus w - 1.
Proof.
  intros w x. unfold wudiv. now rewrite wrap_0.
Qed.

(** Unsigned remainder by zero preserves the normalized dividend. *)
Theorem wurem_zero : forall w x, wurem w x 0 = wrap w x.
Proof.
  intros w x. unfold wurem. now rewrite wrap_0.
Qed.

(** Unsigned division agrees with integer division on words with nonzero divisor. *)
Theorem wudiv_spec : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wudiv w x y = x / y.
Proof.
  intros w x y Hx Hy Hnz. unfold wudiv. rewrite !wrap_id by assumption.
  now rewrite (proj2 (Z.eqb_neq y 0) Hnz).
Qed.

(** Unsigned remainder agrees with integer modulo on words with nonzero divisor. *)
Theorem wurem_spec : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wurem w x y = x mod y.
Proof.
  intros w x y Hx Hy Hnz. unfold wurem. rewrite !wrap_id by assumption.
  now rewrite (proj2 (Z.eqb_neq y 0) Hnz).
Qed.

(** A nonzero unsigned divisor strictly bounds its remainder. *)
Theorem wurem_lt : forall w x y, is_word w x -> is_word w y -> y <> 0 ->
  wurem w x y < y.
Proof.
  intros w x y Hx Hy Hnz. rewrite wurem_spec by assumption.
  apply Z.mod_pos_bound. unfold is_word in Hy. lia.
Qed.

(** Quotient and remainder reconstruct the dividend modulo its width. *)
Theorem wudiv_wurem_euclid : forall w x y,
  wadd w (wmul w y (wudiv w x y)) (wurem w x y) = wrap w x.
Proof.
  intros w x y. unfold wadd, wmul.
  rewrite (wrap_add w (wrap w _) _), wrap_wrap, (wrap_mul w y _).
  rewrite (wrap_id w _ (wudiv_is_word w x y)).
  rewrite <- (wrap_add w (wrap w y * _) _).
  unfold wudiv, wurem.
  destruct (wrap w y =? 0) eqn:Hy.
  - apply Z.eqb_eq in Hy. rewrite Hy. cbn.
    apply wrap_wrap.
  - apply Z.eqb_neq in Hy.
    rewrite <- Z.div_mod by exact Hy. apply wrap_wrap.
Qed.

(** Multiplication may use the signed interpretations of its operands. *)
Theorem wmul_signed : forall w x y,
  wmul w x y = wrap w (signed w x * signed w y).
Proof.
  intros w x y. unfold wmul. rewrite (wrap_mul w x y),
    (wrap_mul w (signed w x) (signed w y)), !wrap_signed. reflexivity.
Qed.

Lemma small_amount_word : forall w k, 0 <= k < Zpos w -> is_word w k.
Proof.
  intros w k Hk. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

Lemma pow2_word : forall w k, 0 <= k < Zpos w -> is_word w (2 ^ k).
Proof.
  intros w k Hk. split.
  - apply Z.pow_nonneg. lia.
  - apply Z.pow_lt_mono_r; lia.
Qed.

(** Multiplication by a representable power of two is a left shift. *)
Theorem wmul_wshl : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wmul w x (2 ^ k) = wshl w x k.
Proof.
  intros w x k Hx Hk. unfold wmul, wshl.
  rewrite (wrap_id w k (small_amount_word w k Hk)), (wrap_id w x Hx).
  now rewrite (proj2 (Z.leb_gt (Zpos w) k) (proj2 Hk)).
Qed.

(** Unsigned division by a representable power of two is a logical right shift. *)
Theorem wudiv_wlshr : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wudiv w x (2 ^ k) = wlshr w x k.
Proof.
  intros w x k Hx Hk. rewrite wudiv_spec by
    (try assumption; try apply pow2_word; try assumption;
      pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk)); lia).
  unfold wlshr. rewrite (wrap_id w k (small_amount_word w k Hk)), (wrap_id w x Hx).
  now rewrite (proj2 (Z.leb_gt (Zpos w) k) (proj2 Hk)).
Qed.

(** Unsigned remainder by a power of two keeps exactly the lower bits. *)
Theorem wurem_mask : forall w x k, is_word w x -> 0 <= k < Zpos w ->
  wurem w x (2 ^ k) = wand w x (2 ^ k - 1).
Proof.
  intros w x k Hx Hk. pose proof (pow2_word w k Hk) as Hpow.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk)) as Hpos.
  rewrite wurem_spec by (try assumption; lia).
  unfold wand. rewrite (wrap_id w x Hx), wrap_id by (unfold is_word in *; lia).
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  symmetry. apply Z.land_ones. exact (proj1 Hk).
Qed.

(** * Counts *)

(** Zero has one leading zero for each bit position. *)
Theorem wclz_zero : forall w, wclz w 0 = Zpos w.
Proof.
  intros w. unfold wclz. now rewrite wrap_0.
Qed.

(** Zero has one trailing zero for each bit position. *)
Theorem wctz_zero : forall w, wctz w 0 = Zpos w.
Proof.
  intros w. unfold wctz. now rewrite wrap_0.
Qed.

(** The highest set bit determines the leading-zero count of a nonzero word. *)
Theorem wclz_spec : forall w x, is_word w x -> x <> 0 ->
  wclz w x = Zpos w - 1 - Z.log2 x.
Proof.
  intros w x Hx Hnz. unfold wclz. rewrite (wrap_id w x Hx).
  now rewrite (proj2 (Z.eqb_neq x 0) Hnz).
Qed.

(** Leading-zero counts lie between zero and the width. *)
Theorem wclz_range : forall w x, 0 <= wclz w x <= Zpos w.
Proof.
  intros w x. unfold wclz. destruct (wrap w x =? 0); [lia|].
  pose proof (log2_word w _ (wrap_is_word w x)).
  pose proof (Z.log2_nonneg (wrap w x)). lia.
Qed.

(** Population counts lie between zero and the width. *)
Theorem wpopcnt_range : forall w x, 0 <= wpopcnt w x <= Zpos w.
Proof.
  intros w x. unfold wpopcnt. split; [lia|].
  rewrite <- (positive_nat_Z w). apply Nat2Z.inj_le.
  eapply Nat.le_trans; [apply List.filter_length_le|]. rewrite List.length_seq. lia.
Qed.

Lemma filter_complement_length : forall (A : Type) (f : A -> bool) xs,
  (length (filter f xs) + length (filter (fun a => negb (f a)) xs) = length xs)%nat.
Proof.
  intros A f xs. induction xs as [|a xs IH]; [reflexivity|].
  cbn [filter]. destruct (f a); cbn; lia.
Qed.

(** Complement exchanges set and clear bits below the width. *)
Theorem wpopcnt_wnot : forall w x, is_word w x ->
  wpopcnt w (wnot w x) = Zpos w - wpopcnt w x.
Proof.
  intros w x Hx. unfold wpopcnt. rewrite (wrap_id w (wnot w x)) by apply wnot_is_word.
  assert (Hfilter :
    filter (fun i => Z.testbit (wnot w x) (Z.of_nat i)) (seq 0 (Pos.to_nat w)) =
    filter (fun i => negb (Z.testbit (wrap w x) (Z.of_nat i))) (seq 0 (Pos.to_nat w))).
  { apply filter_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite testbit_wnot by (try exact Hx; lia).
    rewrite (wrap_id w x Hx).
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) (Zpos w))) by
      (rewrite <- positive_nat_Z; lia). reflexivity. }
  rewrite Hfilter.
  pose proof (filter_complement_length nat
    (fun i => Z.testbit (wrap w x) (Z.of_nat i)) (seq 0 (Pos.to_nat w))) as Hlength.
  rewrite length_seq in Hlength. rewrite <- (positive_nat_Z w). lia.
Qed.

(** An odd integer has its lowest set bit at position zero. *)
Lemma lowbit_odd : forall a, Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  intros a. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_opp by exact Hi.
  replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite Z.pow2_bits_false with (n := 0) by lia.
    destruct (Z.testbit a (i - 1)); reflexivity.
Qed.

Lemma lowbit_double : forall a,
  Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (-a).
Proof.
  intros a. replace (- (2 * a)) with (2 * (-a)) by ring.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hnz].
  - now rewrite !Z.testbit_even_0.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

(** The isolated low bit is a power of two whose position precedes every other set bit. *)
Lemma positive_lowbit : forall p, exists k,
  0 <= k /\ Z.land (Zpos p) (- Zpos p) = 2 ^ k /\
  Z.testbit (Zpos p) k = true /\
  forall j, 0 <= j < k -> Z.testbit (Zpos p) j = false.
Proof.
  intros p. induction p as [p IH|p IH|].
  - exists 0. split; [lia|]. split.
    + change (Z.land (2 * Zpos p + 1) (- (2 * Zpos p + 1)) = 1).
      apply lowbit_odd.
    + split; [reflexivity|]. intros j Hj. lia.
  - destruct IH as [k [Hk [Hlow [Hset Hclear]]]]. exists (Z.succ k).
    split; [lia|]. split.
    + change (Z.land (2 * Zpos p) (- (2 * Zpos p)) = 2 ^ Z.succ k).
      rewrite lowbit_double, Hlow, Z.pow_succ_r by exact Hk. reflexivity.
    + split.
      * change (Z.testbit (2 * Zpos p) (Z.succ k) = true).
        now rewrite Z.testbit_even_succ by exact Hk.
      * intros j Hj. change (Z.testbit (2 * Zpos p) j = false).
        destruct (Z.eq_dec j 0) as [->|Hnz]; [apply Z.testbit_even_0|].
        replace j with (Z.succ (j - 1)) by lia.
        rewrite Z.testbit_even_succ by lia. apply Hclear. lia.
  - exists 0. split; [lia|]. split; [reflexivity|].
    split; [reflexivity|]. intros j Hj. lia.
Qed.

(** The trailing-zero count names the first set bit of a nonzero word. *)
Theorem wctz_spec : forall w x, is_word w x -> x <> 0 ->
  Z.testbit x (wctz w x) = true /\
  forall j, 0 <= j < wctz w x -> Z.testbit x j = false.
Proof.
  intros w x Hx Hnz. unfold wctz. rewrite (wrap_id w x Hx).
  rewrite (proj2 (Z.eqb_neq x 0) Hnz).
  destruct x as [|p|p]; try (unfold is_word in Hx; lia).
  destruct (positive_lowbit p) as [k [Hk [Hlow Hbits]]].
  rewrite Hlow, Z.log2_pow2 by exact Hk. exact Hbits.
Qed.

(** * Rotations *)

(** Disjoint low and high parts contribute their bits without a carry. *)
Lemma split_sum_bits : forall a b k i, 0 <= k -> 0 <= b < 2 ^ k -> 0 <= i ->
  Z.testbit (a * 2 ^ k + b) i =
    if i <? k then Z.testbit b i else Z.testbit a (i - k).
Proof.
  intros a b k i Hk Hb Hi.
  assert (Hdisjoint : Z.land (a * 2 ^ k) b = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_ge_dec j k) as [Hlow|Hhigh].
    - rewrite Z.mul_pow2_bits_low by exact Hlow. reflexivity.
    - assert (Hbit : Z.testbit b j = false).
      { rewrite <- (Z.mod_small b (2 ^ k) Hb) at 1.
        apply Z.mod_pow2_bits_high. lia. }
      rewrite Hbit. apply Bool.andb_false_r. }
  rewrite Z.add_nocarry_lxor by exact Hdisjoint. rewrite Z.lxor_spec.
  destruct (i <? k) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite Z.mul_pow2_bits_low by exact Hlow. reflexivity.
  - apply Z.ltb_ge in Hlow. rewrite Z.mul_pow2_bits by exact Hk.
    assert (Hbit : Z.testbit b i = false).
    { rewrite <- (Z.mod_small b (2 ^ k) Hb) at 1.
      apply Z.mod_pow2_bits_high. lia. }
    rewrite Hbit. apply Bool.xorb_false_r.
Qed.

Lemma rotation_index : forall n i y, 0 < n -> 0 <= i < n ->
  (i - y) mod n = if i <? y mod n then i + n - y mod n else i - y mod n.
Proof.
  intros n i y Hn Hi. pose proof (Z.mod_pos_bound y n Hn) as Hk.
  replace (i - y) with ((i - y mod n) + (- (y / n)) * n)
    by (pose proof (Z.div_mod y n ltac:(lia)); nia).
  rewrite Z.mod_add by lia. destruct (i <? y mod n) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. symmetry. apply Z.mod_unique with (q := -1).
    + left. lia.
    + ring.
  - apply Z.ltb_ge in Hlow. apply Z.mod_small. lia.
Qed.

Lemma rotate_high_part : forall w x k, 0 <= k < Zpos w ->
  0 <= wrap w x / 2 ^ (Zpos w - k) < 2 ^ k.
Proof.
  intros w x k Hk. pose proof (wrap_is_word w x) as Hx.
  assert (Hd : 0 < 2 ^ (Zpos w - k)) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_pos; [exact (proj1 Hx)|lia].
  - apply Z.div_lt_upper_bound; [exact Hd|].
    rewrite <- Z.pow_add_r by lia.
    replace (Zpos w - k + k) with (Zpos w) by lia. exact (proj2 Hx).
Qed.

(** Left rotation reads each source bit at the corresponding cyclic index. *)
Theorem testbit_wrotl : forall w x y i, 0 <= i < Zpos w ->
  Z.testbit (wrotl w x y) i =
    Z.testbit (wrap w x) ((i - wrap w y) mod Zpos w).
Proof.
  intros w x y i Hi.
  pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
  unfold wrotl. rewrite testbit_wrap by exact (proj1 Hi).
  rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)). cbn [andb].
  rewrite split_sum_bits by
    (try exact (proj1 Hk); try exact (proj1 Hi); now apply rotate_high_part).
  rewrite rotation_index by lia.
  destruct (i <? wrap w y mod Zpos w).
  - rewrite Z.div_pow2_bits by lia. f_equal. lia.
  - reflexivity.
Qed.

(** Reducing a rotation amount modulo the width leaves the rotation unchanged. *)
Theorem wrotl_mod : forall w x y,
  wrotl w x y = wrotl w x (wrap w y mod Zpos w).
Proof.
  intros w x y. unfold wrotl.
  pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
  rewrite (wrap_id w (wrap w y mod Zpos w)) by (apply small_amount_word; exact Hk).
  now rewrite Z.mod_mod by lia.
Qed.

(** Right rotation undoes left rotation by the same amount. *)
Theorem wrotr_wrotl : forall w x y, wrotr w (wrotl w x y) y = wrap w x.
Proof.
  intros w x y. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold wrotr. rewrite testbit_wrotl by lia.
    rewrite (wrap_id w (wrotl w x y)) by (unfold wrotl; apply wrap_is_word).
    rewrite testbit_wrotl by (apply Z.mod_pos_bound; lia).
    pose proof (Z.mod_pos_bound (wrap w y) (Zpos w) ltac:(lia)) as Hk.
    assert (Hamount : is_word w (Zpos w - wrap w y mod Zpos w)).
    { pose proof (width_lt_modulus w). unfold is_word. lia. }
    rewrite (wrap_id w _ Hamount).
    replace (((i - (Zpos w - wrap w y mod Zpos w)) mod Zpos w - wrap w y)
      mod Zpos w) with i; [reflexivity|].
    rewrite Zminus_mod, Z.mod_mod by lia.
    rewrite <- Zminus_mod by lia.
    replace (i - (Zpos w - wrap w y mod Zpos w) - wrap w y) with
      (i - Zpos w - (wrap w y / Zpos w) * Zpos w)
      by (pose proof (Z.div_mod (wrap w y) (Zpos w) ltac:(lia)); nia).
    replace (i - Zpos w - wrap w y / Zpos w * Zpos w) with
      (i + (-1 - wrap w y / Zpos w) * Zpos w) by ring.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  - unfold wrotr, wrotl. rewrite testbit_wrap, testbit_wrap by exact Hi.
    now rewrite (proj2 (Z.ltb_ge i (Zpos w)) ltac:(lia)).
Qed.
