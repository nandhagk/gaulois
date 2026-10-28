(** * Word bits and algebra

    The bit equations connect modular words to integer arithmetic and Boolean operations.
    For example, complement flips each bit below the width and clears every higher bit.
    Builds on: BitsWord, BitsFun and Rocq Stdlib integer bit laws. *)

From Stdlib Require Import ZArith Bool Lia Ring.
From Gaulois.Bits Require Import BitsWord BitsFun.

Open Scope Z_scope.

(** Wrapping preserves exactly the bits below the width. *)
Theorem testbit_wrap : forall w x i, 0 <= i ->
  Z.testbit (wrap w x) i = (i <? Zpos w) && Z.testbit x i.
Proof.
  intros w x i Hi. unfold wrap, modulus.
  destruct (i <? Zpos w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. now rewrite Z.mod_pow2_bits_low.
  - apply Z.ltb_ge in Hlt. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** Equality of all nonnegative bits determines a word. *)
Theorem word_ext : forall w x y, is_word w x -> is_word w y ->
  (forall j, 0 <= j -> Z.testbit x j = Z.testbit y j) -> x = y.
Proof.
  intros w x y _ _ Hbits. now apply Z.bits_inj'.
Qed.

Lemma word_bits_high : forall w x i, is_word w x -> Zpos w <= i ->
  Z.testbit x i = false.
Proof.
  intros w x i Hword Hi. rewrite <- (wrap_id w x Hword), testbit_wrap by lia.
  rewrite (proj2 (Z.ltb_ge _ _) Hi). reflexivity.
Qed.

Lemma word_of_bits : forall w x,
  (forall i, Zpos w <= i -> Z.testbit x i = false) -> is_word w x.
Proof.
  intros w x Hbits.
  assert (Heq : x = wrap w x).
  { apply Z.bits_inj'. intros i Hi. rewrite testbit_wrap by exact Hi.
    destruct (i <? Zpos w) eqn:Hlt; simpl; [reflexivity|].
    apply Z.ltb_ge in Hlt. now apply Hbits. }
  rewrite Heq. apply wrap_is_word.
Qed.

Lemma wand_is_word : forall w x y, is_word w (wand w x y).
Proof.
  intros w x y. apply word_of_bits. intros i Hi.
  unfold wand. rewrite Z.land_spec.
  rewrite (word_bits_high w (wrap w x) i (wrap_is_word w x) Hi). reflexivity.
Qed.

Lemma wor_is_word : forall w x y, is_word w (wor w x y).
Proof.
  intros w x y. apply word_of_bits. intros i Hi.
  unfold wor. rewrite Z.lor_spec.
  rewrite (word_bits_high w (wrap w x) i (wrap_is_word w x) Hi).
  rewrite (word_bits_high w (wrap w y) i (wrap_is_word w y) Hi). reflexivity.
Qed.

Lemma wxor_is_word : forall w x y, is_word w (wxor w x y).
Proof.
  intros w x y. apply word_of_bits. intros i Hi.
  unfold wxor. rewrite Z.lxor_spec.
  rewrite (word_bits_high w (wrap w x) i (wrap_is_word w x) Hi).
  rewrite (word_bits_high w (wrap w y) i (wrap_is_word w y) Hi). reflexivity.
Qed.

Lemma wnot_is_word : forall w x, is_word w (wnot w x).
Proof.
  intros w x. pose proof (wrap_is_word w x). unfold wnot, is_word in *. lia.
Qed.

Lemma lnot_value : forall x, Z.lnot x = - x - 1.
Proof.
  intros x. pose proof (Z.add_lnot_diag x). lia.
Qed.

Lemma wnot_lnot : forall w x, wnot w x = wrap w (Z.lnot (wrap w x)).
Proof.
  intros w x. unfold wrap at 2. apply Z.mod_unique with (q := -1).
  - left. apply wnot_is_word.
  - rewrite lnot_value. unfold wnot, wrap. ring.
Qed.

(** Conjunction agrees with Boolean conjunction on each bit of words. *)
Theorem testbit_wand : forall w x y i, is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wand w x y) i = Z.testbit x i && Z.testbit y i.
Proof.
  intros w x y i Hx Hy _. unfold wand. rewrite !wrap_id by assumption.
  apply Z.land_spec.
Qed.

(** Disjunction agrees with Boolean disjunction on each bit of words. *)
Theorem testbit_wor : forall w x y i, is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wor w x y) i = Z.testbit x i || Z.testbit y i.
Proof.
  intros w x y i Hx Hy _. unfold wor. rewrite !wrap_id by assumption.
  apply Z.lor_spec.
Qed.

(** Exclusive disjunction agrees with Boolean xor on each bit of words. *)
Theorem testbit_wxor : forall w x y i, is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wxor w x y) i = xorb (Z.testbit x i) (Z.testbit y i).
Proof.
  intros w x y i Hx Hy _. unfold wxor. rewrite !wrap_id by assumption.
  apply Z.lxor_spec.
Qed.

(** Complement flips each low bit and has no high bits. *)
Theorem testbit_wnot : forall w x i, is_word w x -> 0 <= i ->
  Z.testbit (wnot w x) i = (i <? Zpos w) && negb (Z.testbit x i).
Proof.
  intros w x i Hx Hi. rewrite wnot_lnot, testbit_wrap by exact Hi.
  rewrite Z.lnot_spec by exact Hi. now rewrite wrap_id by exact Hx.
Qed.

(** Large logical shifts produce zero in either direction. *)
Theorem wshl_big : forall w x y, is_word w y -> Zpos w <= y ->
  wshl w x y = 0 /\ wlshr w x y = 0.
Proof.
  intros w x y Hy Hbig. unfold wshl, wlshr. rewrite wrap_id by exact Hy.
  rewrite (proj2 (Z.leb_le _ _) Hbig). split; reflexivity.
Qed.

(** Large arithmetic shifts produce the sign fill. *)
Theorem washr_big : forall w x y, is_word w y -> Zpos w <= y ->
  washr w x y = if msb w x then modulus w - 1 else 0.
Proof.
  intros w x y Hy Hbig. unfold washr. rewrite wrap_id by exact Hy.
  now rewrite (proj2 (Z.leb_le _ _) Hbig).
Qed.

(** Left shift moves each bit by the unsigned amount and clears the overflow. *)
Theorem testbit_wshl : forall w x y i,
  is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wshl w x y) i =
    (i <? Zpos w) && (y <=? i) && Z.testbit x (i - y).
Proof.
  intros w x y i Hx Hy Hi. unfold wshl. rewrite !wrap_id by assumption.
  destruct (Zpos w <=? y) eqn:Hbig.
  - apply Z.leb_le in Hbig. rewrite Z.bits_0.
    destruct (i <? Zpos w) eqn:Hlow; simpl; [|reflexivity].
    apply Z.ltb_lt in Hlow.
    rewrite (proj2 (Z.leb_gt y i) ltac:(lia)). reflexivity.
  - rewrite testbit_wrap by exact Hi. rewrite Z.mul_pow2_bits by exact (proj1 Hy).
    rewrite (wrap_id w x Hx).
    destruct (y <=? i) eqn:Hyi.
    + now rewrite Bool.andb_true_r.
    + apply Z.leb_gt in Hyi. rewrite Z.testbit_neg_r by lia.
      now rewrite !Bool.andb_false_r.
Qed.

(** Logical right shift reads the corresponding higher bit and clears high result bits. *)
Theorem testbit_wlshr : forall w x y i,
  is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wlshr w x y) i = (i <? Zpos w) && Z.testbit x (i + y).
Proof.
  intros w x y i Hx Hy Hi. unfold wlshr. rewrite !wrap_id by assumption.
  destruct (Zpos w <=? y) eqn:Hbig.
  - apply Z.leb_le in Hbig. rewrite Z.bits_0.
    rewrite (word_bits_high w x (i + y) Hx) by lia.
    now rewrite Bool.andb_false_r.
  - rewrite Z.div_pow2_bits by (try exact Hi; exact (proj1 Hy)).
    destruct (i <? Zpos w) eqn:Hlow; simpl; [reflexivity|].
    apply Z.ltb_ge in Hlow.
    exact (word_bits_high w x (i + y) Hx ltac:(pose proof (proj1 Hy); lia)).
Qed.

Lemma msb_half : forall w x, msb w x = negb (wrap w x <? half w).
Proof.
  intros w x.
  pose proof (Z.testbit_spec' (wrap w x) (Zpos w - 1) ltac:(lia)) as Hbit.
  fold (half w) in Hbit. fold (msb w x) in Hbit.
  pose proof (wrap_is_word w x) as Hword.
  pose proof (half_pos w) as Hhalf.
  pose proof (modulus_half w) as Hmodulus.
  destruct (wrap w x <? half w) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. rewrite Z.div_small in Hbit by (unfold is_word in Hword; lia).
    destruct (msb w x); cbn in Hbit |- *; congruence.
  - apply Z.ltb_ge in Hlt.
    assert (Hdiv : wrap w x / half w = 1).
    { symmetry. apply Z.div_unique with (r := wrap w x - half w).
      - left. unfold is_word in Hword. lia.
      - ring. }
    rewrite Hdiv in Hbit. destruct (msb w x); cbn in Hbit |- *; congruence.
Qed.

Lemma signed_msb : forall w x,
  signed w x = if msb w x then Z.lnot (wnot w x) else wrap w x.
Proof.
  intros w x. unfold signed. rewrite msb_half.
  destruct (wrap w x <? half w); [reflexivity|].
  change (wrap w x - modulus w = Z.lnot (wnot w x)).
  rewrite lnot_value. unfold wnot. ring.
Qed.

Lemma signed_bits : forall w x i, is_word w x -> 0 <= i ->
  Z.testbit (signed w x) i = if i <? Zpos w then Z.testbit x i else msb w x.
Proof.
  intros w x i Hx Hi. rewrite signed_msb. destruct (msb w x) eqn:Hsign.
  - rewrite Z.lnot_spec, testbit_wnot by assumption.
    destruct (i <? Zpos w), (Z.testbit x i); reflexivity.
  - rewrite wrap_id by exact Hx. destruct (i <? Zpos w) eqn:Hlt; [reflexivity|].
    apply Z.ltb_ge in Hlt. now apply word_bits_high with (w := w).
Qed.

Lemma all_ones_bits : forall w i, 0 <= i ->
  Z.testbit (modulus w - 1) i = (i <? Zpos w).
Proof.
  intros w i Hi.
  replace (modulus w - 1) with (wnot w 0) by (unfold wnot; rewrite wrap_0; ring).
  rewrite testbit_wnot by (try exact Hi; apply zero_is_word).
  rewrite Z.bits_0. apply Bool.andb_true_r.
Qed.

(** Arithmetic right shift saturates source indices at the sign bit. *)
Theorem testbit_washr : forall w x y i,
  is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (washr w x y) i =
    (i <? Zpos w) && Z.testbit x (Z.min (i + y) (Zpos w - 1)).
Proof.
  intros w x y i Hx Hy Hi. pose proof (proj1 Hy) as Hy0.
  unfold washr. rewrite (wrap_id w y Hy).
  destruct (Zpos w <=? y) eqn:Hbig.
  - apply Z.leb_le in Hbig. rewrite Z.min_r by lia.
    change (Z.testbit (if msb w x then modulus w - 1 else 0) i =
      (i <? Zpos w) && Z.testbit x (Zpos w - 1)).
    assert (Hsign : Z.testbit x (Zpos w - 1) = msb w x).
    { unfold msb. now rewrite wrap_id by exact Hx. }
    rewrite Hsign. destruct (msb w x).
    + rewrite all_ones_bits by exact Hi. now rewrite Bool.andb_true_r.
    + rewrite Z.bits_0. now rewrite Bool.andb_false_r.
  - rewrite testbit_wrap, Z.div_pow2_bits by lia.
    rewrite signed_bits by (try exact Hx; lia).
    destruct (i <? Zpos w) eqn:Hlow; [|reflexivity].
    change ((if i + y <? Zpos w then Z.testbit x (i + y) else msb w x) =
      Z.testbit x (Z.min (i + y) (Zpos w - 1))).
    destruct (i + y <? Zpos w) eqn:Hsource.
    + apply Z.ltb_lt in Hsource. rewrite Z.min_l by lia. reflexivity.
    + apply Z.ltb_ge in Hsource. rewrite Z.min_r by lia.
      unfold msb. now rewrite wrap_id by exact Hx.
Qed.

(** * Operation ranges *)

Lemma ones_is_word : forall w, is_word w (modulus w - 1).
Proof.
  intros w. pose proof (modulus_pos w). unfold is_word. lia.
Qed.

Lemma count_is_word : forall w n, 0 <= n <= Zpos w -> is_word w n.
Proof.
  intros w n Hn. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

Lemma log2_word : forall w x, is_word w x -> Z.log2 x < Zpos w.
Proof.
  intros w x Hx. destruct (Z.eq_dec x 0) as [->|Hnonzero].
  - cbn. lia.
  - apply (proj1 (Z.log2_lt_pow2 x (Zpos w) ltac:(unfold is_word in Hx; lia))).
    exact (proj2 Hx).
Qed.

Lemma word_div_is_word : forall w x d, is_word w x -> 0 < d -> is_word w (x / d).
Proof.
  intros w x d Hx Hd. split.
  - apply Z.div_pos; [exact (proj1 Hx)|lia].
  - assert (Hle : x / d <= x).
    { apply Z.div_le_upper_bound; [exact Hd|]. pose proof (proj1 Hx). nia. }
    pose proof (proj2 Hx). lia.
Qed.

Lemma wudiv_is_word : forall w x y, is_word w (wudiv w x y).
Proof.
  intros w x y. unfold wudiv. destruct (wrap w y =? 0) eqn:Hy.
  - apply ones_is_word.
  - apply Z.eqb_neq in Hy. apply word_div_is_word; [apply wrap_is_word|].
    pose proof (wrap_is_word w y). unfold is_word in *. lia.
Qed.

Lemma wurem_is_word : forall w x y, is_word w (wurem w x y).
Proof.
  intros w x y. unfold wurem. destruct (wrap w y =? 0) eqn:Hy.
  - apply wrap_is_word.
  - apply Z.eqb_neq in Hy. pose proof (wrap_is_word w y) as Hrange.
    assert (Hpos : 0 < wrap w y) by (unfold is_word in Hrange; lia).
    pose proof (Z.mod_pos_bound (wrap w x) (wrap w y) Hpos).
    unfold is_word in *. lia.
Qed.

Lemma wsdiv_is_word : forall w x y, is_word w (wsdiv w x y).
Proof.
  intros w x y. unfold wsdiv. destruct (msb w x), (msb w y);
    first [apply wrap_is_word|apply wudiv_is_word].
Qed.

Lemma wsrem_is_word : forall w x y, is_word w (wsrem w x y).
Proof.
  intros w x y. unfold wsrem. destruct (msb w x), (msb w y);
    first [apply wrap_is_word|apply wurem_is_word].
Qed.

Lemma wsmod_is_word : forall w x y, is_word w (wsmod w x y).
Proof.
  intros w x y. unfold wsmod.
  destruct (msb w x), (msb w y); destruct (wurem w _ _ =? 0);
    first [apply wrap_is_word|apply wurem_is_word].
Qed.

Lemma wshl_is_word : forall w x y, is_word w (wshl w x y).
Proof.
  intros w x y. unfold wshl. destruct (Zpos w <=? wrap w y).
  - apply zero_is_word.
  - apply wrap_is_word.
Qed.

Lemma wlshr_is_word : forall w x y, is_word w (wlshr w x y).
Proof.
  intros w x y. unfold wlshr. destruct (Zpos w <=? wrap w y).
  - apply zero_is_word.
  - apply word_div_is_word; [apply wrap_is_word|].
    apply Z.pow_pos_nonneg; [lia|exact (proj1 (wrap_is_word w y))].
Qed.

Lemma washr_is_word : forall w x y, is_word w (washr w x y).
Proof.
  intros w x y. unfold washr. destruct (Zpos w <=? wrap w y).
  - destruct (msb w x); [apply ones_is_word|apply zero_is_word].
  - apply wrap_is_word.
Qed.

Lemma wclz_is_word : forall w x, is_word w (wclz w x).
Proof.
  intros w x. unfold wclz. destruct (wrap w x =? 0).
  - apply count_is_word. lia.
  - apply count_is_word. pose proof (log2_word w _ (wrap_is_word w x)).
    pose proof (Z.log2_nonneg (wrap w x)). lia.
Qed.

Lemma wctz_is_word : forall w x, is_word w (wctz w x).
Proof.
  intros w x. unfold wctz. destruct (wrap w x =? 0).
  - apply count_is_word. lia.
  - assert (Hland : is_word w (Z.land (wrap w x) (- wrap w x))).
    { apply word_of_bits. intros i Hi. rewrite Z.land_spec.
      rewrite (word_bits_high w _ i (wrap_is_word w x) Hi). reflexivity. }
    apply count_is_word. pose proof (log2_word w _ Hland).
    pose proof (Z.log2_nonneg (Z.land (wrap w x) (- wrap w x))). lia.
Qed.

Lemma wpopcnt_is_word : forall w x, is_word w (wpopcnt w x).
Proof.
  intros w x. apply count_is_word. unfold wpopcnt. split; [lia|].
  rewrite <- (positive_nat_Z w). apply Nat2Z.inj_le.
  eapply Nat.le_trans; [apply List.filter_length_le|]. rewrite List.length_seq. lia.
Qed.

(** * Bitwise algebra *)

(** Conjunction is commutative. *)
Theorem wand_comm : forall w x y, wand w x y = wand w y x.
Proof.
  intros w x y. apply Z.land_comm.
Qed.

(** Conjunction is associative, including normalization at intermediate words. *)
Theorem wand_assoc : forall w x y z,
  wand w x (wand w y z) = wand w (wand w x y) z.
Proof.
  intros w x y z. change (Z.land (wrap w x) (wrap w (wand w y z)) =
    Z.land (wrap w (wand w x y)) (wrap w z)).
  rewrite (wrap_id _ _ (wand_is_word w y z)), (wrap_id _ _ (wand_is_word w x y)).
  apply Z.land_assoc.
Qed.

(** Disjunction is commutative. *)
Theorem wor_comm : forall w x y, wor w x y = wor w y x.
Proof.
  intros w x y. apply Z.lor_comm.
Qed.

(** Disjunction is associative. *)
Theorem wor_assoc : forall w x y z,
  wor w x (wor w y z) = wor w (wor w x y) z.
Proof.
  intros w x y z. change (Z.lor (wrap w x) (wrap w (wor w y z)) =
    Z.lor (wrap w (wor w x y)) (wrap w z)).
  rewrite (wrap_id _ _ (wor_is_word w y z)), (wrap_id _ _ (wor_is_word w x y)).
  apply Z.lor_assoc.
Qed.

(** Exclusive disjunction is commutative. *)
Theorem wxor_comm : forall w x y, wxor w x y = wxor w y x.
Proof.
  intros w x y. apply Z.lxor_comm.
Qed.

(** Exclusive disjunction is associative. *)
Theorem wxor_assoc : forall w x y z,
  wxor w x (wxor w y z) = wxor w (wxor w x y) z.
Proof.
  intros w x y z. change (Z.lxor (wrap w x) (wrap w (wxor w y z)) =
    Z.lxor (wrap w (wxor w x y)) (wrap w z)).
  rewrite (wrap_id _ _ (wxor_is_word w y z)), (wrap_id _ _ (wxor_is_word w x y)).
  symmetry. apply Z.lxor_assoc.
Qed.

(** A word xor itself is zero. *)
Theorem wxor_self : forall w x, wxor w x x = 0.
Proof.
  intros w x. apply Z.lxor_nilpotent.
Qed.

(** Conjunction of a word with itself fixes it. *)
Theorem wand_idem : forall w x, is_word w x -> wand w x x = x.
Proof.
  intros w x Hx. unfold wand. rewrite wrap_id by exact Hx. apply Z.land_diag.
Qed.

(** Complementing a word twice fixes it. *)
Theorem wnot_involutive : forall w x, is_word w x -> wnot w (wnot w x) = x.
Proof.
  intros w x Hx. unfold wnot at 1. rewrite wrap_id by apply wnot_is_word.
  unfold wnot. rewrite wrap_id by exact Hx. ring.
Qed.

Lemma testbit_wnot_full : forall w x i, 0 <= i ->
  Z.testbit (wnot w x) i = (i <? Zpos w) && negb (Z.testbit x i).
Proof.
  intros w x i Hi. rewrite wnot_lnot, testbit_wrap, Z.lnot_spec, testbit_wrap
    by exact Hi.
  destruct (i <? Zpos w); reflexivity.
Qed.

Lemma testbit_wand_full : forall w x y i, 0 <= i ->
  Z.testbit (wand w x y) i = (i <? Zpos w) && (Z.testbit x i && Z.testbit y i).
Proof.
  intros w x y i Hi. unfold wand. rewrite Z.land_spec, !testbit_wrap by exact Hi.
  destruct (i <? Zpos w); reflexivity.
Qed.

Lemma testbit_wor_full : forall w x y i, 0 <= i ->
  Z.testbit (wor w x y) i = (i <? Zpos w) && (Z.testbit x i || Z.testbit y i).
Proof.
  intros w x y i Hi. unfold wor. rewrite Z.lor_spec, !testbit_wrap by exact Hi.
  destruct (i <? Zpos w); reflexivity.
Qed.

(** Complement turns conjunction into disjunction of complements. *)
Theorem wnot_wand : forall w x y,
  wnot w (wand w x y) = wor w (wnot w x) (wnot w y).
Proof.
  intros w x y. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wnot_full, testbit_wor_full, testbit_wand_full,
    !testbit_wnot_full by exact Hi.
  destruct (i <? Zpos w), (Z.testbit x i), (Z.testbit y i); reflexivity.
Qed.

(** Complement turns disjunction into conjunction of complements. *)
Theorem wnot_wor : forall w x y,
  wnot w (wor w x y) = wand w (wnot w x) (wnot w y).
Proof.
  intros w x y. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wnot_full, testbit_wand_full, testbit_wor_full,
    !testbit_wnot_full by exact Hi.
  destruct (i <? Zpos w), (Z.testbit x i), (Z.testbit y i); reflexivity.
Qed.

(** A word and its complement have no common set bit. *)
Theorem wand_wnot : forall w x, wand w x (wnot w x) = 0.
Proof.
  intros w x. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wand_full, testbit_wnot_full, Z.bits_0 by exact Hi.
  destruct (i <? Zpos w), (Z.testbit x i); reflexivity.
Qed.

(** * Modular arithmetic *)

(** Word addition commutes. *)
Theorem wadd_comm : forall w x y, wadd w x y = wadd w y x.
Proof.
  intros w x y. unfold wadd. f_equal. ring.
Qed.

(** Word addition associates. *)
Theorem wadd_assoc : forall w x y z,
  wadd w x (wadd w y z) = wadd w (wadd w x y) z.
Proof.
  intros w x y z. unfold wadd, wrap.
  rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by apply modulus_nonzero.
  f_equal. ring.
Qed.

(** Zero is a right identity for word addition. *)
Theorem wadd_0_r : forall w x, is_word w x -> wadd w x 0 = x.
Proof.
  intros w x Hx. unfold wadd. rewrite Z.add_0_r. now apply wrap_id.
Qed.

(** Two's-complement negation is complement followed by addition of one. *)
Theorem wneg_wnot : forall w x, wneg w x = wadd w (wnot w x) 1.
Proof.
  intros w x. unfold wneg, wadd, wnot.
  replace (modulus w - 1 - wrap w x + 1) with (- wrap w x + 1 * modulus w) by ring.
  now rewrite wrap_add_modulus, wrap_opp.
Qed.

(** A word and its modular negation add to zero. *)
Theorem wadd_wneg : forall w x, wadd w x (wneg w x) = 0.
Proof.
  intros w x. unfold wadd, wneg, wrap.
  rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
  rewrite Z.add_opp_diag_r. apply Z.mod_0_l. apply modulus_nonzero.
Qed.

(** Subtraction is addition of the modular negation. *)
Theorem wsub_wneg : forall w x y, wsub w x y = wadd w x (wneg w y).
Proof.
  intros w x y. unfold wsub, wadd, wneg, wrap.
  now rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
Qed.

(** Word multiplication commutes. *)
Theorem wmul_comm : forall w x y, wmul w x y = wmul w y x.
Proof.
  intros w x y. unfold wmul. f_equal. ring.
Qed.

(** Word multiplication associates. *)
Theorem wmul_assoc : forall w x y z,
  wmul w x (wmul w y z) = wmul w (wmul w x y) z.
Proof.
  intros w x y z. unfold wmul, wrap.
  rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by apply modulus_nonzero.
  f_equal. ring.
Qed.

(** One is a right identity for word multiplication. *)
Theorem wmul_1_r : forall w x, is_word w x -> wmul w x 1 = x.
Proof.
  intros w x Hx. unfold wmul. rewrite Z.mul_1_r. now apply wrap_id.
Qed.

(** Word multiplication distributes over word addition. *)
Theorem wmul_wadd_distr : forall w x y z,
  wmul w x (wadd w y z) = wadd w (wmul w x y) (wmul w x z).
Proof.
  intros w x y z. unfold wmul, wadd, wrap.
  rewrite Z.mul_mod_idemp_r, <- Z.add_mod by apply modulus_nonzero.
  f_equal. ring.
Qed.

(** A zero left-shift amount fixes a word. *)
Theorem wshl_0 : forall w x, is_word w x -> wshl w x 0 = x.
Proof.
  intros w x Hx. unfold wshl.
  rewrite (wrap_id w 0) by (pose proof (modulus_pos w); unfold is_word; lia).
  rewrite (proj2 (Z.leb_gt (Zpos w) 0) ltac:(lia)).
  cbn. rewrite Z.mul_1_r, wrap_wrap. now apply wrap_id.
Qed.
