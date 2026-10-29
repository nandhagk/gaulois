(** * Demanded bits

    Masks describe the bits on which two words must agree, and transfers propagate those needs
    backwards through operators. For example, demanding the low nibble of an addition demands
    only the low nibble of each operand.
    Builds on: OrderLattice, OrderConcrete, BitsWord, BitsFun, BitsTestbit and BitsArith. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsArith BitsOp.
Import List.ListNotations.

Open Scope Z_scope.

(** Mask inclusion ignores all positions outside the word. *)
Definition mask_lattice (w : width) : lattice Z :=
  {| leb := fun a b => Z.land (wrap w a) (Z.lnot (wrap w b)) =? 0;
     bot := 0;
     join := Z.lor;
     widen := Z.lor;
     narrow := fun a _ => a |}.

Lemma mask_leb_bits : forall w a b,
  leb (mask_lattice w) a b = true <->
  forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit b i = true.
Proof.
  intros w a b. cbn [mask_lattice leb]. rewrite Z.eqb_eq. split.
  - intros Hzero i Hi Ha.
    apply (f_equal (fun z => Z.testbit z i)) in Hzero.
    rewrite Z.land_spec, Z.lnot_spec, !testbit_wrap, Z.bits_0 in Hzero by lia.
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)), Ha in Hzero.
    destruct (Z.testbit b i); cbn in Hzero; congruence.
  - intros Hsub. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.lnot_spec, !testbit_wrap, Z.bits_0 by exact Hi.
    destruct (i <? Zpos w) eqn:Hlow; cbn; [|reflexivity].
    apply Z.ltb_lt in Hlow.
    destruct (Z.testbit a i) eqn:Ha; cbn; [|reflexivity].
    now rewrite (Hsub i ltac:(lia) Ha).
Qed.

Lemma demand_wrap_bit : forall w x i, 0 <= i < Zpos w ->
  Z.testbit (wrap w x) i = Z.testbit x i.
Proof.
  intros w x i Hi. rewrite testbit_wrap by lia.
  now rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)).
Qed.

(** Masks have the weak lattice laws under bit inclusion. *)
Theorem mask_laws : forall w, lattice_laws (mask_lattice w).
Proof.
  intro w. constructor.
  - intro a. apply mask_leb_bits. auto.
  - intros a b c Hab Hbc. apply mask_leb_bits. intros i Hi Hbit.
    apply (proj1 (mask_leb_bits w b c) Hbc i Hi).
    exact (proj1 (mask_leb_bits w a b) Hab i Hi Hbit).
  - intro a. apply mask_leb_bits. intros i Hi Hbit.
    cbn [mask_lattice bot] in Hbit. now rewrite Z.bits_0 in Hbit.
  - intros a b. apply mask_leb_bits. intros i Hi Hbit.
    cbn [mask_lattice join]. rewrite Z.lor_spec, Hbit. reflexivity.
  - intros a b. apply mask_leb_bits. intros i Hi Hbit.
    cbn [mask_lattice join]. rewrite Z.lor_spec, Hbit, Bool.orb_true_r. reflexivity.
  - intros a b. apply mask_leb_bits. intros i Hi Hbit.
    cbn [mask_lattice widen]. rewrite Z.lor_spec, Hbit. reflexivity.
  - intros a b. apply mask_leb_bits. intros i Hi Hbit.
    cbn [mask_lattice widen]. rewrite Z.lor_spec, Hbit, Bool.orb_true_r. reflexivity.
  - intros a b Hba. apply mask_leb_bits. auto.
  - intros a b Hba. exact Hba.
Qed.

(** Disjunction is the least upper bound of masks. *)
Theorem mask_lub : forall w, lub_laws (mask_lattice w).
Proof.
  intro w. constructor. intros a b c Ha Hb. apply mask_leb_bits. intros i Hi Hbit.
  cbn [mask_lattice join] in Hbit. rewrite Z.lor_spec in Hbit.
  apply Bool.orb_true_iff in Hbit. destruct Hbit as [Hbit|Hbit].
  - exact (proj1 (mask_leb_bits w a c) Ha i Hi Hbit).
  - exact (proj1 (mask_leb_bits w b c) Hb i Hi Hbit).
Qed.

(** Agreement observes exactly the masked bits of the payloads. *)
Definition mask_agreement (w : width) : agreement Z word :=
  {| agree := fun m x y =>
       Z.land (wrap w (snd x)) (wrap w m) = Z.land (wrap w (snd y)) (wrap w m) |}.

Lemma mask_agree_bits : forall w m x y,
  agree (mask_agreement w) m x y <->
  forall i, 0 <= i < Zpos w -> Z.testbit m i = true ->
    Z.testbit (snd x) i = Z.testbit (snd y) i.
Proof.
  intros w m x y. cbn [mask_agreement agree]. split.
  - intros Heq i Hi Hbit. apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite !Z.land_spec, !testbit_wrap in Heq by lia.
    rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi)), Hbit in Heq.
    now rewrite !Bool.andb_true_r in Heq.
  - intros Hbits. apply Z.bits_inj'. intros i Hi.
    rewrite !Z.land_spec, !testbit_wrap by exact Hi.
    destruct (i <? Zpos w) eqn:Hlow; cbn; [|reflexivity].
    destruct (Z.testbit m i) eqn:Hbit; [|now rewrite !Bool.andb_false_r].
    rewrite (Hbits i ltac:(apply Z.ltb_lt in Hlow; lia) Hbit). reflexivity.
Qed.

(** Larger masks require agreement on at least as many bits. *)
Theorem mask_agreement_laws : forall w,
  agreement_laws (mask_lattice w) (mask_agreement w).
Proof.
  intro w. constructor.
  - intros m x. reflexivity.
  - intros a b x y Hsub Hxy. apply mask_agree_bits. intros i Hi Hbit.
    apply (proj1 (mask_agree_bits w b x y) Hxy i Hi).
    exact (proj1 (mask_leb_bits w a b) Hsub i Hi Hbit).
Qed.

(** The zero mask relates every pair of words. *)
Theorem mask_agreement_bot : forall w,
  agreement_bot (mask_lattice w) (mask_agreement w).
Proof.
  intro w. constructor. intros x y. cbn [mask_lattice bot mask_agreement agree].
  now rewrite wrap_0, !Z.land_0_r.
Qed.

(** Agreement on two masks gives agreement on their union. *)
Theorem mask_agreement_join : forall w,
  agreement_join_law (mask_lattice w) (mask_agreement w).
Proof.
  intro w. constructor. intros a b x y Ha Hb. apply mask_agree_bits.
  intros i Hi Hbit. cbn [mask_lattice join] in Hbit. rewrite Z.lor_spec in Hbit.
  apply Bool.orb_true_iff in Hbit. destruct Hbit as [Hbit|Hbit].
  - exact (proj1 (mask_agree_bits w a x y) Ha i Hi Hbit).
  - exact (proj1 (mask_agree_bits w b x y) Hb i Hi Hbit).
Qed.

(** Mask agreement is symmetric and transitive. *)
Theorem mask_agreement_equivalence : forall w, agreement_equivalence (mask_agreement w).
Proof.
  intro w. constructor.
  - intros m x y Hxy. symmetry. exact Hxy.
  - intros m x y z Hxy Hyz. transitivity (Z.land (wrap w (snd y)) (wrap w m));
      assumption.
Qed.

(** * Finite height *)

Lemma demand_filter_count : forall {A} (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  (length (filter f xs) <= length (filter g xs))%nat /\
  (length (filter f xs) = length (filter g xs) ->
    forall x, In x xs -> f x = g x).
Proof.
  intros A f g xs. induction xs as [|a xs IH]; intro Hsub.
  - cbn. split; [lia|intros _ x Hin; contradiction].
  - destruct (IH (fun x Hin => Hsub x (or_intror Hin))) as [Hle Heq].
    pose proof (Hsub a (or_introl eq_refl)) as Ha.
    cbn [filter]. destruct (f a) eqn:Hf, (g a) eqn:Hg; cbn in *.
    + split; [lia|]. intros Hcount x [->|Hin]; [congruence|].
      apply Heq; [lia|exact Hin].
    + specialize (Ha eq_refl). discriminate.
    + split; [lia|]. intro Hcount. lia.
    + split; [exact Hle|]. intros Hcount x [->|Hin]; [congruence|].
      now apply Heq.
Qed.

(** Population count is the rank of a mask. *)
Definition mask_rank (w : width) (m : Z) : nat :=
  length (filter (fun i => Z.testbit m (Z.of_nat i)) (seq 0 (Pos.to_nat w))).

Lemma mask_rank_monotone : forall w a b,
  leb (mask_lattice w) a b = true -> (mask_rank w a <= mask_rank w b)%nat.
Proof.
  intros w a b Hsub.
  assert (Himp : forall i, In i (seq 0 (Pos.to_nat w)) ->
    Z.testbit a (Z.of_nat i) = true -> Z.testbit b (Z.of_nat i) = true).
  { intros i Hin Hbit. apply in_seq in Hin. apply (proj1 (mask_leb_bits w a b) Hsub).
    - rewrite <- positive_nat_Z. lia.
    - exact Hbit. }
  exact (proj1 (demand_filter_count _ _ _ Himp)).
Qed.

Lemma mask_rank_equal : forall w a b,
  leb (mask_lattice w) a b = true -> mask_rank w a = mask_rank w b ->
  leb (mask_lattice w) b a = true.
Proof.
  intros w a b Hsub Hcount.
  assert (Himp : forall i, In i (seq 0 (Pos.to_nat w)) ->
    Z.testbit a (Z.of_nat i) = true -> Z.testbit b (Z.of_nat i) = true).
  { intros i Hin Hbit. apply in_seq in Hin. apply (proj1 (mask_leb_bits w a b) Hsub).
    - rewrite <- positive_nat_Z. lia.
    - exact Hbit. }
  pose proof (proj2 (demand_filter_count _ _ _ Himp) Hcount) as Heq.
  apply mask_leb_bits. intros i Hi Hbit.
  specialize (Heq (Z.to_nat i)). cbn in Heq. rewrite Z2Nat.id in Heq by lia.
  rewrite Heq; [exact Hbit|]. apply in_seq. rewrite <- positive_nat_Z in Hi. lia.
Qed.

(** At most one strict increase is possible per bit position. *)
Definition mask_height (w : width) : monotone_height (mask_lattice w).
Proof.
  unshelve refine (@MonotoneHeight Z (mask_lattice w)
    (@Height Z (mask_lattice w) (mask_rank w) (Pos.to_nat w) _ _) _).
  - intro a. unfold mask_rank. eapply Nat.le_trans; [apply filter_length_le|].
    now rewrite length_seq.
  - intros a b Hstrict.
    pose proof (mask_rank_monotone w a (Z.lor a b) (join_upper_l (mask_laws w) a b))
      as Hle.
    destruct (Nat.eq_dec (mask_rank w a) (mask_rank w (Z.lor a b))) as [Heq|Hne].
    + pose proof (mask_rank_equal w a (Z.lor a b) (join_upper_l (mask_laws w) a b) Heq)
        as Hreverse. change (leb (mask_lattice w) (Z.lor a b) a = false) in Hstrict.
      rewrite Hstrict in Hreverse. discriminate.
    + cbn [mask_lattice join] in *. lia.
  - exact (mask_rank_monotone w).
Defined.

(** * Backward transfers *)

(** Carry-sensitive operations demand every position below the highest demanded bit. *)
Definition demand_fill_down (m : Z) : Z :=
  if m =? 0 then 0 else Z.ones (Z.log2 m + 1).

(** Right shifts with unknown amounts can read every position above the lowest demanded bit. *)
Definition demand_fill_up (w : width) (m : Z) : Z :=
  if m =? 0 then 0 else wrap w (Z.lnot (Z.ones (wctz w m))).

Definition demand_all (w : width) : Z := modulus w - 1.

Definition demand_known (consts : list (option Z)) (i : nat) : option Z :=
  match nth_error consts i with
  | Some co => co
  | None => None
  end.

Definition demand_and (w : width) (co : option Z) (m : Z) : Z :=
  match co with
  | Some c => Z.land m (wrap w c)
  | None => m
  end.

Definition demand_or (w : width) (co : option Z) (m : Z) : Z :=
  match co with
  | Some c => Z.land m (Z.lnot (wrap w c))
  | None => m
  end.

(* Guarding large amounts prevents constructing an integer with an oversized shift. *)
Definition demand_shl (w : width) (k m : Z) : Z :=
  if Zpos w <=? k then 0 else Z.shiftr m k.

Definition demand_lshr (w : width) (k m : Z) : Z :=
  if Zpos w <=? k then 0 else wrap w (Z.shiftl m k).

Definition demand_ashr (w : width) (k m : Z) : Z :=
  if Zpos w <=? k then half w
  else Z.lor (demand_lshr w k m)
    (if Z.shiftr m (Zpos w - k) =? 0 then 0 else half w).

Definition demand_sext (w : width) (m : Z) : Z :=
  Z.lor (wrap w m) (if Z.shiftr m (Zpos w - 1) =? 0 then 0 else half w).

Definition demand_shift (o : op) (w : width) (co : option Z) (m : Z) : list Z :=
  match co with
  | Some c =>
    let k := wrap w c in
    [match o with
     | bvshl => demand_shl w k m
     | bvlshr => demand_lshr w k m
     | bvashr => demand_ashr w k m
     | bvrotl => wrotr w m k
     | bvrotr => wrotl w m k
     | _ => demand_all w
     end; 0]
  | None =>
    [match o with
     | bvshl => demand_fill_down m
     | bvlshr | bvashr => demand_fill_up w m
     | _ => demand_all w
     end; demand_all w]
  end.

Definition demand_raw (o : op) (ws : list width) (consts : list (option Z))
  (m : Z) : list Z :=
  match o, ws with
  | bvnot, [_] => [m]
  | bvneg, [_] => [demand_fill_down m]
  | (bvadd | bvsub | bvmul), [_; _] => [demand_fill_down m; demand_fill_down m]
  | bvand, [w; _] =>
    [demand_and w (demand_known consts 1) m; demand_and w (demand_known consts 0) m]
  | bvor, [w; _] =>
    [demand_or w (demand_known consts 1) m; demand_or w (demand_known consts 0) m]
  | bvxor, [_; _] => [m; m]
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [w; _] =>
    demand_shift o w (demand_known consts 1) m
  | bvzext _, [w] => [wrap w m]
  | bvsext _, [w] => [demand_sext w m]
  | bvtrunc _, [_] => [m]
  | bvextract _ lo, [_] => [Z.shiftl m (Z.of_nat lo)]
  | bvconcat, [_; w2] => [Z.shiftr m (Zpos w2); wrap w2 m]
  | bvite, [_; _; _] => [1; m; m]
  | _, _ => map demand_all ws
  end.

(** Each valid operator propagates its normalized result mask using its documented bit rule. *)
Definition demand (o : op) (ws : list width) (consts : list (option Z)) (m : Z) : list Z :=
  match result_width o ws with
  | Some rw =>
    let m := wrap rw m in
    if m =? 0 then repeat 0 (arity o) else demand_raw o ws consts m
  | None => repeat 0 (arity o)
  end.

(** Operand masks are aligned with pairs of concrete inputs. *)
Definition agree_masks (ms : list Z) (xs ys : list word) : Prop :=
  Forall2 (fun m p => agree (mask_agreement (fst (fst p))) m (fst p) (snd p))
    ms (combine xs ys).

(** A known operand constant describes its wrapped concrete value. *)
Definition consts_hold (consts : list (option Z)) (xs : list word) : Prop :=
  Forall2 (fun co x => forall c, co = Some c ->
    wrap (fst x) (snd x) = wrap (fst x) c) consts xs.

(** Inclusion of operand masks uses each operand's own width. *)
Definition masks_leb (ws : list width) (ms ms' : list Z) : Prop :=
  Forall2 (fun w p => leb (mask_lattice w) (fst p) (snd p) = true)
    ws (combine ms ms').

(** A zero result mask demands no operand bits. *)
Theorem demand_zero : forall o ws consts, length ws = arity o ->
  demand o ws consts 0 = repeat 0 (arity o).
Proof.
  intros o ws consts Hlen. unfold demand. destruct (result_width o ws); [|reflexivity].
  rewrite wrap_0. reflexivity.
Qed.

Lemma demand_raw_length : forall o ws consts m,
  length (demand_raw o ws consts m) = length ws.
Proof.
  intros o ws consts m. destruct o; destruct ws as [|a [|b [|c [|d ws]]]];
    cbn [demand_raw]; try rewrite length_map; try reflexivity;
    unfold demand_shift; destruct (demand_known consts 1); reflexivity.
Qed.

(** Demand returns one mask for every operand of the operator's arity. *)
Theorem demand_length : forall o ws consts m, length ws = arity o ->
  length (demand o ws consts m) = arity o.
Proof.
  intros o ws consts m Hlen. unfold demand. destruct (result_width o ws) as [rw|].
  - destruct (wrap rw m =? 0); [apply repeat_length|].
    now rewrite demand_raw_length.
  - apply repeat_length.
Qed.

(** * Dependencies of individual result bits *)

Lemma demand_bit_bound : forall m i, 0 <= m -> Z.testbit m i = true -> i <= Z.log2 m.
Proof.
  intros m i Hm Hbit. destruct (Z_le_gt_dec i (Z.log2 m)); [assumption|].
  rewrite Z.bits_above_log2 in Hbit by lia. discriminate.
Qed.

Lemma demand_down_covers : forall m i j, 0 <= m -> Z.testbit m i = true ->
  0 <= j <= i -> Z.testbit (demand_fill_down m) j = true.
Proof.
  intros m i j Hm Hbit Hj. unfold demand_fill_down.
  destruct (m =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst m. now rewrite Z.bits_0 in Hbit.
  - apply Z.ones_spec_low. pose proof (demand_bit_bound m i Hm Hbit). lia.
Qed.

Lemma demand_down_source : forall m j, 0 <= m -> 0 <= j ->
  Z.testbit (demand_fill_down m) j = true ->
  exists i, j <= i /\ Z.testbit m i = true.
Proof.
  intros m j Hm Hj Hbit. unfold demand_fill_down in Hbit.
  destruct (m =? 0) eqn:Hzero; [now rewrite Z.bits_0 in Hbit|].
  apply Z.eqb_neq in Hzero. apply Z.ones_spec_iff in Hbit; [|pose proof (Z.log2_nonneg m); lia].
  exists (Z.log2 m). split; [lia|apply Z.bit_log2; lia].
Qed.

Lemma demand_up_covers : forall w m i j, is_word w m -> Z.testbit m i = true ->
  0 <= i <= j -> j < Zpos w -> Z.testbit (demand_fill_up w m) j = true.
Proof.
  intros w m i j Hm Hbit Hij Hj. unfold demand_fill_up.
  destruct (m =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst m. now rewrite Z.bits_0 in Hbit.
  - apply Z.eqb_neq in Hzero.
    destruct (wctz_spec w m Hm Hzero) as [Hleast Hbelow].
    assert (Hle : wctz w m <= i).
    { destruct (Z_le_gt_dec (wctz w m) i); [assumption|].
      rewrite Hbelow in Hbit by lia. discriminate. }
    rewrite demand_wrap_bit by lia. rewrite Z.lnot_spec by lia.
    rewrite Z.ones_spec_high by (pose proof (proj1 (wctz_is_word w m)); lia).
    reflexivity.
Qed.

Lemma demand_up_source : forall w m j, is_word w m -> 0 <= j < Zpos w ->
  Z.testbit (demand_fill_up w m) j = true ->
  exists i, 0 <= i <= j /\ Z.testbit m i = true.
Proof.
  intros w m j Hm Hj Hbit. unfold demand_fill_up in Hbit.
  destruct (m =? 0) eqn:Hzero; [now rewrite Z.bits_0 in Hbit|].
  apply Z.eqb_neq in Hzero. rewrite demand_wrap_bit, Z.lnot_spec,
    Z.testbit_ones_nonneg in Hbit by (pose proof (proj1 (wctz_is_word w m)); lia).
  apply Bool.negb_true_iff in Hbit. apply Z.ltb_ge in Hbit.
  exists (wctz w m). split; [pose proof (proj1 (wctz_is_word w m)); lia|].
  exact (proj1 (wctz_spec w m Hm Hzero)).
Qed.

Lemma demand_below_mod : forall n x y, 0 <= n ->
  (forall i, 0 <= i < n -> Z.testbit x i = Z.testbit y i) ->
  x mod 2 ^ n = y mod 2 ^ n.
Proof.
  intros n x y Hn Hbits. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.testbit_mod_pow2 by exact Hn.
  destruct (i <? n) eqn:Hlow; [|reflexivity].
  rewrite Hbits by (apply Z.ltb_lt in Hlow; lia). reflexivity.
Qed.

Lemma demand_low_arithmetic : forall i x x' y y', 0 <= i ->
  (forall j, 0 <= j <= i -> Z.testbit x j = Z.testbit x' j) ->
  (forall j, 0 <= j <= i -> Z.testbit y j = Z.testbit y' j) ->
  Z.testbit (x + y) i = Z.testbit (x' + y') i /\
  Z.testbit (x - y) i = Z.testbit (x' - y') i /\
  Z.testbit (x * y) i = Z.testbit (x' * y') i.
Proof.
  intros i x x' y y' Hi Hx Hy.
  assert (Hxmod : x mod 2 ^ (i + 1) = x' mod 2 ^ (i + 1)).
  { apply demand_below_mod; [lia|]. intros j Hj. apply Hx. lia. }
  assert (Hymod : y mod 2 ^ (i + 1) = y' mod 2 ^ (i + 1)).
  { apply demand_below_mod; [lia|]. intros j Hj. apply Hy. lia. }
  assert (Hpow : 2 ^ (i + 1) <> 0) by (apply Z.pow_nonzero; lia).
  assert (Hadd : (x + y) mod 2 ^ (i + 1) = (x' + y') mod 2 ^ (i + 1)).
  { rewrite (Z.add_mod x y _ Hpow), (Z.add_mod x' y' _ Hpow).
    now rewrite Hxmod, Hymod. }
  assert (Hsub : (x - y) mod 2 ^ (i + 1) = (x' - y') mod 2 ^ (i + 1)).
  { rewrite (Zminus_mod x y _), (Zminus_mod x' y' _). now rewrite Hxmod, Hymod. }
  assert (Hmul : (x * y) mod 2 ^ (i + 1) = (x' * y') mod 2 ^ (i + 1)).
  { rewrite (Z.mul_mod x y _ Hpow), (Z.mul_mod x' y' _ Hpow).
    now rewrite Hxmod, Hymod. }
  apply (f_equal (fun z => Z.testbit z i)) in Hadd, Hsub, Hmul.
  rewrite !Z.mod_pow2_bits_low in Hadd, Hsub, Hmul by lia. auto.
Qed.

(** * Inclusion preserved by mask constructors *)

Definition demand_subset (a b : Z) : Prop :=
  forall i, 0 <= i -> Z.testbit a i = true -> Z.testbit b i = true.

Lemma demand_subset_refl : forall a, demand_subset a a.
Proof.
  intros a i Hi Hbit. exact Hbit.
Qed.

Lemma demand_subset_wrap : forall w a b, demand_subset a b ->
  demand_subset (wrap w a) (wrap w b).
Proof.
  intros w a b Hsub i Hi Hbit. rewrite testbit_wrap in Hbit |- * by exact Hi.
  apply Bool.andb_true_iff in Hbit. destruct Hbit as [Hlow Hbit].
  rewrite Hlow, (Hsub i Hi Hbit). reflexivity.
Qed.

Lemma demand_subset_mask : forall w a b, demand_subset a b -> leb (mask_lattice w) a b = true.
Proof.
  intros w a b Hsub. apply mask_leb_bits. intros i Hi. apply Hsub. lia.
Qed.

Lemma demand_mask_subset : forall w a b, leb (mask_lattice w) a b = true ->
  demand_subset (wrap w a) (wrap w b).
Proof.
  intros w a b Hsub i Hi Hbit. rewrite testbit_wrap in Hbit |- * by exact Hi.
  apply Bool.andb_true_iff in Hbit. destruct Hbit as [Hlow Hbit].
  rewrite Hlow. cbn. apply (proj1 (mask_leb_bits w a b) Hsub); [|exact Hbit].
  apply Z.ltb_lt in Hlow. lia.
Qed.

Lemma demand_subset_land : forall a b c, demand_subset a b ->
  demand_subset (Z.land a c) (Z.land b c).
Proof.
  intros a b c Hsub i Hi Hbit. rewrite Z.land_spec in Hbit |- *.
  apply Bool.andb_true_iff in Hbit. destruct Hbit as [Ha Hc].
  now rewrite (Hsub i Hi Ha), Hc.
Qed.

Lemma demand_subset_lor : forall a b c d, demand_subset a b -> demand_subset c d ->
  demand_subset (Z.lor a c) (Z.lor b d).
Proof.
  intros a b c d Hab Hcd i Hi Hbit. rewrite Z.lor_spec in Hbit |- *.
  apply Bool.orb_true_iff in Hbit. destruct Hbit as [Ha|Hc].
  - now rewrite (Hab i Hi Ha).
  - now rewrite (Hcd i Hi Hc), Bool.orb_true_r.
Qed.

Lemma demand_subset_shiftr : forall a b k, 0 <= k -> demand_subset a b ->
  demand_subset (Z.shiftr a k) (Z.shiftr b k).
Proof.
  intros a b k Hk Hsub i Hi Hbit. rewrite Z.shiftr_spec in Hbit |- * by exact Hi.
  apply Hsub; [lia|exact Hbit].
Qed.

Lemma demand_subset_shiftl : forall a b k, 0 <= k -> demand_subset a b ->
  demand_subset (Z.shiftl a k) (Z.shiftl b k).
Proof.
  intros a b k Hk Hsub i Hi Hbit. rewrite Z.shiftl_spec in Hbit |- * by exact Hi.
  destruct (Z_le_gt_dec k i).
  - apply Hsub; [lia|exact Hbit].
  - rewrite Z.testbit_neg_r in Hbit by lia. discriminate.
Qed.

Lemma demand_subset_down : forall a b, 0 <= a -> 0 <= b -> demand_subset a b ->
  demand_subset (demand_fill_down a) (demand_fill_down b).
Proof.
  intros a b Ha Hb Hsub i Hi Hbit.
  destruct (demand_down_source a i Ha Hi Hbit) as [j [Hij Hj]].
  apply (demand_down_covers b j i Hb (Hsub j ltac:(lia) Hj)). lia.
Qed.

Lemma demand_subset_up : forall w a b, is_word w a -> is_word w b -> demand_subset a b ->
  demand_subset (demand_fill_up w a) (demand_fill_up w b).
Proof.
  intros w a b Ha Hb Hsub i Hi Hbit.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - destruct (demand_up_source w a i Ha ltac:(lia) Hbit) as [j [Hj Hset]].
    apply (demand_up_covers w b j i Hb (Hsub j ltac:(lia) Hset)); lia.
  - unfold demand_fill_up in Hbit. destruct (a =? 0).
    + now rewrite Z.bits_0 in Hbit.
    + rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)) in Hbit. discriminate.
Qed.

Lemma demand_subset_nonzero : forall a b, 0 <= a -> a <> 0 -> demand_subset a b -> b <> 0.
Proof.
  intros a b Ha Hnonzero Hsub ->.
  pose proof (Hsub (Z.log2 a) (Z.log2_nonneg a) (Z.bit_log2 a ltac:(lia))) as Hbit.
  now rewrite Z.bits_0 in Hbit.
Qed.

Lemma demand_subset_trigger : forall a b k v, 0 <= a -> 0 <= k -> demand_subset a b ->
  demand_subset (if Z.shiftr a k =? 0 then 0 else v)
    (if Z.shiftr b k =? 0 then 0 else v).
Proof.
  intros a b k v Ha Hk Hsub.
  destruct (Z.shiftr a k =? 0) eqn:Hzero.
  - intros i Hi Hbit. now rewrite Z.bits_0 in Hbit.
  - apply Z.eqb_neq in Hzero.
    assert (Hnonzero : Z.shiftr b k <> 0).
    { eapply demand_subset_nonzero; [apply Z.shiftr_nonneg; exact Ha|exact Hzero|].
      now apply demand_subset_shiftr. }
    rewrite (proj2 (Z.eqb_neq _ _) Hnonzero). apply demand_subset_refl.
Qed.

Lemma demand_subset_sext : forall w a b, 0 <= a -> demand_subset a b ->
  demand_subset (demand_sext w a) (demand_sext w b).
Proof.
  intros w a b Ha Hsub. unfold demand_sext. apply demand_subset_lor.
  - now apply demand_subset_wrap.
  - apply demand_subset_trigger; [exact Ha|lia|exact Hsub].
Qed.

Lemma demand_subset_shl : forall w k a b, 0 <= k -> demand_subset a b ->
  demand_subset (demand_shl w k a) (demand_shl w k b).
Proof.
  intros w k a b Hk Hsub. unfold demand_shl. destruct (Zpos w <=? k).
  - apply demand_subset_refl.
  - now apply demand_subset_shiftr.
Qed.

Lemma demand_subset_lshr : forall w k a b, 0 <= k -> demand_subset a b ->
  demand_subset (demand_lshr w k a) (demand_lshr w k b).
Proof.
  intros w k a b Hk Hsub. unfold demand_lshr. destruct (Zpos w <=? k).
  - apply demand_subset_refl.
  - apply demand_subset_wrap. now apply demand_subset_shiftl.
Qed.

Lemma demand_subset_ashr : forall w k a b, 0 <= k -> 0 <= a -> demand_subset a b ->
  demand_subset (demand_ashr w k a) (demand_ashr w k b).
Proof.
  intros w k a b Hk Ha Hsub. unfold demand_ashr. destruct (Zpos w <=? k) eqn:Hbig.
  - apply demand_subset_refl.
  - apply Z.leb_gt in Hbig. apply demand_subset_lor.
    + now apply demand_subset_lshr.
    + apply demand_subset_trigger; [exact Ha|lia|exact Hsub].
Qed.

Lemma demand_subset_rotl : forall w k a b, demand_subset a b ->
  demand_subset (wrotl w a k) (wrotl w b k).
Proof.
  intros w k a b Hsub i Hi Hbit. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite testbit_wrotl in Hbit |- * by lia.
    apply (demand_subset_wrap w a b Hsub); [|exact Hbit].
    pose proof (Z.mod_pos_bound (i - wrap w k) (Zpos w) ltac:(lia)). lia.
  - unfold wrotl in Hbit.
    rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)) in Hbit. discriminate.
Qed.

Lemma demand_subset_rotr : forall w k a b, demand_subset a b ->
  demand_subset (wrotr w a k) (wrotr w b k).
Proof.
  intros w k a b Hsub. unfold wrotr. now apply demand_subset_rotl.
Qed.

Lemma demand_raw_monotone : forall o ws rw consts a b,
  result_width o ws = Some rw -> is_word rw a -> is_word rw b -> demand_subset a b ->
  Forall2 demand_subset (demand_raw o ws consts a) (demand_raw o ws consts b).
Proof.
  intros o ws rw consts a b Hwidth Ha Hb Hsub.
  destruct o; destruct ws as [|u [|v [|t [|s ws]]]];
    cbn [result_width] in Hwidth; try discriminate;
    repeat match type of Hwidth with
    | (if ?guard then _ else _) = _ => destruct guard eqn:?; try discriminate
    end;
    injection Hwidth as <-; cbn [demand_raw map];
    try (unfold demand_and, demand_or; destruct (demand_known consts 0);
      destruct (demand_known consts 1));
    try (unfold demand_shift; destruct (demand_known consts 1));
    repeat first [apply Forall2_cons | apply Forall2_nil |
      apply demand_subset_refl | exact Hsub |
      apply demand_subset_down; [exact (proj1 Ha)|exact (proj1 Hb)|exact Hsub] |
      apply demand_subset_up; assumption |
      apply demand_subset_land; exact Hsub |
      apply demand_subset_wrap; exact Hsub |
      apply demand_subset_sext; [exact (proj1 Ha)|exact Hsub] |
      apply demand_subset_shiftl; [lia|exact Hsub] |
      apply demand_subset_shiftr; [lia|exact Hsub] |
      apply demand_subset_shl; [apply (proj1 (wrap_is_word _ _))|exact Hsub] |
      apply demand_subset_lshr; [apply (proj1 (wrap_is_word _ _))|exact Hsub] |
      apply demand_subset_ashr;
        [apply (proj1 (wrap_is_word _ _))|exact (proj1 Ha)|exact Hsub] |
      apply demand_subset_rotl; exact Hsub |
      apply demand_subset_rotr; exact Hsub].
Qed.

Lemma demand_masks_subset : forall ws ms ms', Forall2 demand_subset ms ms' ->
  length ws = length ms -> masks_leb ws ms ms'.
Proof.
  intros ws ms ms' Hsub. revert ws. induction Hsub as [|m m' ms ms' Hhead Htail IH];
    intros [|w ws] Hlen; cbn in Hlen; try discriminate.
  - constructor.
  - constructor; [now apply demand_subset_mask|]. apply IH. lia.
Qed.

Lemma demand_masks_zero : forall ws ms, length ws = length ms ->
  masks_leb ws (repeat 0 (length ws)) ms.
Proof.
  intro ws. induction ws as [|w ws IH]; intros [|m ms] Hlen;
    cbn in Hlen; try discriminate; cbn [repeat masks_leb combine].
  - constructor.
  - constructor; [apply (bot_least (mask_laws w))|]. apply IH. lia.
Qed.

(** Increasing the normalized output mask can only increase the required operand masks. *)
Theorem demand_monotone : forall o ws consts m m' rw,
  result_width o ws = Some rw -> leb (mask_lattice rw) m m' = true ->
  masks_leb ws (demand o ws consts m) (demand o ws consts m').
Proof.
  intros o ws consts m m' rw Hwidth Hle.
  pose proof (result_width_arity o ws rw Hwidth) as Hlen.
  pose proof (demand_mask_subset rw m m' Hle) as Hsub.
  unfold demand. rewrite Hwidth. destruct (wrap rw m =? 0) eqn:Hzero.
  - rewrite <- Hlen. apply demand_masks_zero.
    destruct (wrap rw m' =? 0); [now rewrite repeat_length|].
    symmetry. apply demand_raw_length.
  - apply Z.eqb_neq in Hzero.
    assert (Hnonzero : wrap rw m' <> 0).
    { exact (demand_subset_nonzero (wrap rw m) (wrap rw m')
        (proj1 (wrap_is_word rw m)) Hzero Hsub). }
    rewrite (proj2 (Z.eqb_neq _ _) Hnonzero).
    apply demand_masks_subset; [|symmetry; apply demand_raw_length].
    eapply demand_raw_monotone; [exact Hwidth|apply wrap_is_word|apply wrap_is_word|exact Hsub].
Qed.

(** * Scalar agreement *)

Definition demand_bits_equal (w : width) (m x y : Z) : Prop :=
  forall i, 0 <= i < Zpos w -> Z.testbit m i = true -> Z.testbit x i = Z.testbit y i.

Lemma demand_bits_all : forall w x y, demand_bits_equal w (demand_all w) x y ->
  wrap w x = wrap w y.
Proof.
  intros w x y Hbits. apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_wrap by exact Hi. destruct (i <? Zpos w) eqn:Hlow; [|reflexivity].
  rewrite Hbits; [reflexivity|apply Z.ltb_lt in Hlow; lia|].
  unfold demand_all. now rewrite all_ones_bits by exact Hi.
Qed.

Lemma demand_bits_normalize : forall w m x y,
  demand_bits_equal w m x y -> demand_bits_equal w m (wrap w x) (wrap w y).
Proof.
  intros w m x y Hbits i Hi Hbit. rewrite !demand_wrap_bit by exact Hi. now apply Hbits.
Qed.

Lemma demand_bits_mask_wrap : forall w m x y,
  demand_bits_equal w (wrap w m) x y <-> demand_bits_equal w m x y.
Proof.
  intros w m x y. unfold demand_bits_equal.
  split; intros Hbits i Hi Hbit; apply Hbits; try exact Hi;
    rewrite demand_wrap_bit in * by exact Hi; exact Hbit.
Qed.

Lemma demand_bits_full : forall w m x y, wrap w x = wrap w y -> demand_bits_equal w m x y.
Proof.
  intros w m x y Heq i Hi Hbit.
  rewrite <- (demand_wrap_bit w x i Hi), <- (demand_wrap_bit w y i Hi). now rewrite Heq.
Qed.

Lemma demand_bits_arithmetic : forall w m x x' y y', is_word w m ->
  demand_bits_equal w (demand_fill_down m) x x' ->
  demand_bits_equal w (demand_fill_down m) y y' ->
  demand_bits_equal w m (x + y) (x' + y') /\
  demand_bits_equal w m (x - y) (x' - y') /\
  demand_bits_equal w m (x * y) (x' * y').
Proof.
  intros w m x x' y y' Hm Hx Hy.
  assert (Hbits : forall i, 0 <= i < Zpos w -> Z.testbit m i = true ->
    Z.testbit (x + y) i = Z.testbit (x' + y') i /\
    Z.testbit (x - y) i = Z.testbit (x' - y') i /\
    Z.testbit (x * y) i = Z.testbit (x' * y') i).
  { intros i Hi Hbit. apply demand_low_arithmetic; [lia| |];
      intros j Hj; [apply Hx|apply Hy]; try lia;
      apply (demand_down_covers m i j (proj1 Hm) Hbit Hj). }
  split; [intros i Hi Hbit; exact (proj1 (Hbits i Hi Hbit))|].
  split; intros i Hi Hbit;
    [exact (proj1 (proj2 (Hbits i Hi Hbit)))|exact (proj2 (proj2 (Hbits i Hi Hbit)))].
Qed.

Lemma demand_bits_neg : forall w m x x', is_word w m ->
  demand_bits_equal w (demand_fill_down m) x x' -> demand_bits_equal w m (-x) (-x').
Proof.
  intros w m x x' Hm Hx.
  pose proof (demand_bits_arithmetic w m 0 0 x x' Hm (fun _ _ _ => eq_refl) Hx)
    as [_ [Hsub _]]. exact Hsub.
Qed.

Lemma demand_bits_not : forall w m x x', demand_bits_equal w m x x' ->
  demand_bits_equal w m (wnot w x) (wnot w x').
Proof.
  intros w m x x' Hx i Hi Hbit.
  rewrite !testbit_wnot_full by lia. now rewrite (Hx i Hi Hbit).
Qed.

Lemma demand_bits_xor : forall w m x x' y y',
  demand_bits_equal w m x x' -> demand_bits_equal w m y y' ->
  demand_bits_equal w m (wxor w x y) (wxor w x' y').
Proof.
  intros w m x x' y y' Hx Hy i Hi Hbit. unfold wxor.
  rewrite !Z.lxor_spec, !demand_wrap_bit by exact Hi.
  now rewrite (Hx i Hi Hbit), (Hy i Hi Hbit).
Qed.

Definition demand_constant (w : width) (co : option Z) (x x' : Z) : Prop :=
  forall c, co = Some c -> wrap w x = wrap w c /\ wrap w x' = wrap w c.

Lemma demand_constant_bits : forall w co x x' c i,
  demand_constant w co x x' -> co = Some c -> 0 <= i < Zpos w ->
  Z.testbit x i = Z.testbit c i /\ Z.testbit x' i = Z.testbit c i.
Proof.
  intros w co x x' c i Hconst Hco Hi. destruct (Hconst c Hco) as [Hx Hx'].
  apply (f_equal (fun z => Z.testbit z i)) in Hx, Hx'.
  rewrite !demand_wrap_bit in Hx, Hx' by exact Hi. auto.
Qed.

Lemma demand_bits_and : forall w m x x' y y' co1 co2,
  demand_constant w co1 x x' -> demand_constant w co2 y y' ->
  demand_bits_equal w (demand_and w co2 m) x x' ->
  demand_bits_equal w (demand_and w co1 m) y y' ->
  demand_bits_equal w m (wand w x y) (wand w x' y').
Proof.
  intros w m x x' y y' co1 co2 Hc1 Hc2 Hx Hy i Hi Hbit.
  unfold wand. rewrite !Z.land_spec, !demand_wrap_bit by exact Hi.
  assert (Ha : Z.testbit y i = false /\ Z.testbit y' i = false \/
    Z.testbit x i = Z.testbit x' i).
  { destruct co2 as [c|].
    - destruct (demand_constant_bits w (Some c) y y' c i Hc2 eq_refl Hi) as [Hc Hc'].
      destruct (Z.testbit c i) eqn:Hci.
      + right. apply Hx; [exact Hi|]. cbn [demand_and].
        rewrite Z.land_spec, demand_wrap_bit, Hbit, Hci by exact Hi. reflexivity.
      + left. auto.
    - right. apply Hx; assumption. }
  assert (Hb : Z.testbit x i = false /\ Z.testbit x' i = false \/
    Z.testbit y i = Z.testbit y' i).
  { destruct co1 as [c|].
    - destruct (demand_constant_bits w (Some c) x x' c i Hc1 eq_refl Hi) as [Hc Hc'].
      destruct (Z.testbit c i) eqn:Hci.
      + right. apply Hy; [exact Hi|]. cbn [demand_and].
        rewrite Z.land_spec, demand_wrap_bit, Hbit, Hci by exact Hi. reflexivity.
      + left. auto.
    - right. apply Hy; assumption. }
  destruct Ha as [[-> ->]|Ha]; [now rewrite !Bool.andb_false_r|].
  destruct Hb as [[-> ->]|Hb]; [reflexivity|now rewrite Ha, Hb].
Qed.

Lemma demand_bits_or : forall w m x x' y y' co1 co2,
  demand_constant w co1 x x' -> demand_constant w co2 y y' ->
  demand_bits_equal w (demand_or w co2 m) x x' ->
  demand_bits_equal w (demand_or w co1 m) y y' ->
  demand_bits_equal w m (wor w x y) (wor w x' y').
Proof.
  intros w m x x' y y' co1 co2 Hc1 Hc2 Hx Hy i Hi Hbit.
  unfold wor. rewrite !Z.lor_spec, !demand_wrap_bit by exact Hi.
  assert (Ha : Z.testbit y i = true /\ Z.testbit y' i = true \/
    Z.testbit x i = Z.testbit x' i).
  { destruct co2 as [c|].
    - destruct (demand_constant_bits w (Some c) y y' c i Hc2 eq_refl Hi) as [Hc Hc'].
      destruct (Z.testbit c i) eqn:Hci.
      + left. auto.
      + right. apply Hx; [exact Hi|]. cbn [demand_or].
        rewrite Z.land_spec, Z.lnot_spec, demand_wrap_bit, Hbit, Hci by lia. reflexivity.
    - right. apply Hx; assumption. }
  assert (Hb : Z.testbit x i = true /\ Z.testbit x' i = true \/
    Z.testbit y i = Z.testbit y' i).
  { destruct co1 as [c|].
    - destruct (demand_constant_bits w (Some c) x x' c i Hc1 eq_refl Hi) as [Hc Hc'].
      destruct (Z.testbit c i) eqn:Hci.
      + left. auto.
      + right. apply Hy; [exact Hi|]. cbn [demand_or].
        rewrite Z.land_spec, Z.lnot_spec, demand_wrap_bit, Hbit, Hci by lia. reflexivity.
    - right. apply Hy; assumption. }
  destruct Ha as [[-> ->]|Ha]; [now rewrite !Bool.orb_true_r|].
  destruct Hb as [[-> ->]|Hb]; [reflexivity|now rewrite Ha, Hb].
Qed.

Lemma demand_const_head : forall w x x' xs ys consts,
  consts_hold consts ((w, x) :: xs) -> consts_hold consts ((w, x') :: ys) ->
  demand_constant w (demand_known consts 0) x x'.
Proof.
  intros w x x' xs ys [|co consts] Hx Hy; inversion Hx as [|? ? ? ? Hhead Htail].
  inversion Hy as [|? ? ? ? Hhead' Htail']. cbn [demand_known nth_error].
  intros c Hco. split; [exact (Hhead c Hco)|exact (Hhead' c Hco)].
Qed.

Lemma demand_const_second : forall w x x' a b xs ys consts,
  consts_hold consts (a :: (w, x) :: xs) -> consts_hold consts (b :: (w, x') :: ys) ->
  demand_constant w (demand_known consts 1) x x'.
Proof.
  intros w x x' a b xs ys [|co consts] Hx Hy; inversion Hx as [|? ? ? ? Hhead Htail].
  inversion Hy as [|? ? ? ? Hhead' Htail']. cbn [demand_known nth_error].
  exact (demand_const_head w x x' xs ys consts Htail Htail').
Qed.

Lemma demand_agree_cons : forall w x x' xs ys m ms,
  agree_masks (m :: ms) ((w, x) :: xs) ((w, x') :: ys) ->
  demand_bits_equal w m x x' /\ agree_masks ms xs ys.
Proof.
  intros w x x' xs ys m ms Hagree.
  inversion Hagree as [|? ? ? ? Hhead Htail]. split; [|exact Htail].
  exact (proj1 (mask_agree_bits w m (w, x) (w, x')) Hhead).
Qed.

Lemma demand_shl_covers : forall w m k i, is_word w k -> 0 <= i < Zpos w ->
  Z.testbit m i = true -> k <= i -> Z.testbit (demand_shl w k m) (i - k) = true.
Proof.
  intros w m k i Hk Hi Hbit Hki. unfold demand_shl.
  rewrite (proj2 (Z.leb_gt (Zpos w) k) ltac:(lia)). rewrite Z.shiftr_spec by lia.
  now replace (i - k + k) with i by ring.
Qed.

Lemma demand_lshr_covers : forall w m k i, is_word w k -> 0 <= i -> i + k < Zpos w ->
  Z.testbit m i = true -> Z.testbit (demand_lshr w k m) (i + k) = true.
Proof.
  intros w m k i Hk Hi Hlow Hbit. unfold demand_lshr.
  rewrite (proj2 (Z.leb_gt (Zpos w) k) ltac:(pose proof (proj1 Hk); lia)).
  rewrite demand_wrap_bit by (pose proof (proj1 Hk); lia).
  rewrite Z.shiftl_spec by (pose proof (proj1 Hk); lia).
  now replace (i + k - k) with i by ring.
Qed.

Lemma demand_shift_nonzero : forall m n i, 0 <= n <= i -> Z.testbit m i = true ->
  Z.shiftr m n <> 0.
Proof.
  intros m n i Hni Hbit Hzero. apply (f_equal (fun z => Z.testbit z (i - n))) in Hzero.
  rewrite Z.shiftr_spec, Z.bits_0 in Hzero by lia.
  replace (i - n + n) with i in Hzero by ring. congruence.
Qed.

Lemma demand_ashr_covers : forall w m k i, is_word w k -> 0 <= i < Zpos w ->
  Z.testbit m i = true ->
  Z.testbit (demand_ashr w k m) (Z.min (i + k) (Zpos w - 1)) = true.
Proof.
  intros w m k i Hk Hi Hbit. pose proof (proj1 Hk) as Hk0.
  unfold demand_ashr. destruct (Zpos w <=? k) eqn:Hbig.
  - apply Z.leb_le in Hbig. rewrite Z.min_r by lia.
    unfold half. apply Z.pow2_bits_true. lia.
  - apply Z.leb_gt in Hbig. rewrite Z.lor_spec.
    destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hlow|Hhigh].
    + rewrite Z.min_l by lia. rewrite (demand_lshr_covers w m k i Hk ltac:(lia) Hlow Hbit).
      reflexivity.
    + rewrite Z.min_r by lia.
      rewrite (proj2 (Z.eqb_neq _ _)
        (demand_shift_nonzero m (Zpos w - k) i ltac:(lia) Hbit)).
      unfold half. rewrite Z.pow2_bits_true by lia. apply Bool.orb_true_r.
Qed.

Lemma demand_rotr_bit : forall w x k i, is_word w k -> 0 <= i < Zpos w ->
  Z.testbit (wrotr w x k) i = Z.testbit (wrap w x) ((i + k) mod Zpos w).
Proof.
  intros w x k i Hk Hi. unfold wrotr. rewrite (wrap_id w k Hk).
  rewrite testbit_wrotl by exact Hi.
  assert (Hamount : is_word w (Zpos w - k mod Zpos w)).
  { pose proof (Z.mod_pos_bound k (Zpos w) ltac:(lia)). apply count_is_word. lia. }
  rewrite (wrap_id w _ Hamount). f_equal.
  replace (i - (Zpos w - k mod Zpos w)) with (i + k mod Zpos w + (-1) * Zpos w)
    by ring.
  rewrite Z.mod_add, Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. reflexivity.
Qed.

Lemma demand_rotl_covers : forall w m k i, is_word w k -> 0 <= i < Zpos w ->
  Z.testbit m i = true -> Z.testbit (wrotr w m k) ((i - k) mod Zpos w) = true.
Proof.
  intros w m k i Hk Hi Hbit.
  rewrite demand_rotr_bit by (try exact Hk; apply Z.mod_pos_bound; lia).
  replace (((i - k) mod Zpos w + k) mod Zpos w) with i.
  - now rewrite demand_wrap_bit by exact Hi.
  - rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia.
    replace (i - k + k) with i by ring. symmetry. apply Z.mod_small. exact Hi.
Qed.

Lemma demand_rotr_covers : forall w m k i, is_word w k -> 0 <= i < Zpos w ->
  Z.testbit m i = true -> Z.testbit (wrotl w m k) ((i + k) mod Zpos w) = true.
Proof.
  intros w m k i Hk Hi Hbit.
  rewrite testbit_wrotl by (apply Z.mod_pos_bound; lia).
  rewrite (wrap_id w k Hk).
  replace (((i + k) mod Zpos w - k) mod Zpos w) with i.
  - now rewrite demand_wrap_bit by exact Hi.
  - rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    replace (i + k - k) with i by ring. symmetry. apply Z.mod_small. exact Hi.
Qed.

Definition demand_shift_op (o : op) : Prop :=
  o = bvshl \/ o = bvlshr \/ o = bvashr \/ o = bvrotl \/ o = bvrotr.

Definition demand_shift_value (o : op) (w : width) (x k : Z) : Z :=
  match o with
  | bvshl => wshl w x k
  | bvlshr => wlshr w x k
  | bvashr => washr w x k
  | bvrotl => wrotl w x k
  | bvrotr => wrotr w x k
  | _ => 0
  end.

Lemma demand_known_shift_sound : forall o w m k x x', demand_shift_op o ->
  is_word w k -> is_word w x -> is_word w x' ->
  demand_bits_equal w (hd 0 (demand_shift o w (Some k) m)) x x' ->
  demand_bits_equal w m (demand_shift_value o w x k) (demand_shift_value o w x' k).
Proof.
  intros o w m k x x' Ho Hk Hx Hx' Hequal.
  destruct Ho as [-> | [-> | [-> | [-> | ->]]]];
    cbn [demand_shift demand_shift_value hd] in *;
    rewrite (wrap_id w k Hk) in Hequal; intros i Hi Hbit.
  - rewrite !testbit_wshl by (try assumption; lia).
    destruct (k <=? i) eqn:Hki; [|now rewrite !Bool.andb_false_r].
    apply Z.leb_le in Hki. rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
    exact (demand_shl_covers w m k i Hk Hi Hbit Hki).
  - rewrite !testbit_wlshr by (try assumption; lia).
    destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hlow|Hhigh].
    + rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
      apply demand_lshr_covers; try assumption; lia.
    + rewrite (word_bits_high w x (i + k) Hx ltac:(lia)),
        (word_bits_high w x' (i + k) Hx' ltac:(lia)). reflexivity.
  - rewrite !testbit_washr by (try assumption; lia).
    rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
    now apply demand_ashr_covers.
  - rewrite !testbit_wrotl by exact Hi. rewrite (wrap_id w x Hx), (wrap_id w x' Hx').
    rewrite (wrap_id w k Hk). apply Hequal.
    + apply Z.mod_pos_bound. lia.
    + now apply demand_rotl_covers.
  - rewrite !demand_rotr_bit by assumption. rewrite (wrap_id w x Hx), (wrap_id w x' Hx').
    apply Hequal.
    + apply Z.mod_pos_bound. lia.
    + now apply demand_rotr_covers.
Qed.

Lemma demand_variable_shift_sound : forall o w m k x x', demand_shift_op o ->
  is_word w m -> is_word w k -> is_word w x -> is_word w x' ->
  demand_bits_equal w (hd 0 (demand_shift o w None m)) x x' ->
  demand_bits_equal w m (demand_shift_value o w x k) (demand_shift_value o w x' k).
Proof.
  intros o w m k x x' Ho Hm Hk Hx Hx' Hequal.
  destruct Ho as [-> | [-> | [-> | [-> | ->]]]];
    cbn [demand_shift demand_shift_value hd] in *.
  - intros i Hi Hbit. rewrite !testbit_wshl by (try assumption; lia).
    destruct (k <=? i) eqn:Hki; [|now rewrite !Bool.andb_false_r].
    apply Z.leb_le in Hki. rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
    apply (demand_down_covers m i (i - k) (proj1 Hm) Hbit). pose proof (proj1 Hk). lia.
  - intros i Hi Hbit. rewrite !testbit_wlshr by (try assumption; lia).
    destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hlow|Hhigh].
    + rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
      apply (demand_up_covers w m i (i + k) Hm Hbit); pose proof (proj1 Hk); lia.
    + rewrite (word_bits_high w x (i + k) Hx ltac:(lia)),
        (word_bits_high w x' (i + k) Hx' ltac:(lia)). reflexivity.
  - intros i Hi Hbit. rewrite !testbit_washr by (try assumption; lia).
    rewrite Hequal; [reflexivity|pose proof (proj1 Hk); lia|].
    apply (demand_up_covers w m i (Z.min (i + k) (Zpos w - 1)) Hm Hbit);
      pose proof (proj1 Hk); lia.
  - apply demand_bits_full.
    pose proof (demand_bits_all w x x' Hequal) as Heq. unfold wrotl. now rewrite Heq.
  - apply demand_bits_full.
    pose proof (demand_bits_all w x x' Hequal) as Heq. unfold wrotr, wrotl. now rewrite Heq.
Qed.

Lemma demand_shift_sound : forall o w m co x x' y y', demand_shift_op o -> is_word w m ->
  demand_constant w co y y' ->
  demand_bits_equal w (hd 0 (demand_shift o w co m)) x x' ->
  demand_bits_equal w (hd 0 (tl (demand_shift o w co m))) y y' ->
  demand_bits_equal w m (demand_shift_value o w (wrap w x) (wrap w y))
    (demand_shift_value o w (wrap w x') (wrap w y')).
Proof.
  intros o w m co x x' y y' Ho Hm Hconst Hx Hy.
  destruct co as [c|].
  - destruct (Hconst c eq_refl) as [Hc Hc']. rewrite Hc, Hc'.
    apply demand_known_shift_sound; try assumption; try apply wrap_is_word.
    apply demand_bits_normalize. unfold demand_shift in Hx |- *.
    now rewrite wrap_wrap.
  - assert (Hyfull : demand_bits_equal w (demand_all w) y y').
    { destruct Ho as [-> | [-> | [-> | [-> | ->]]]]; exact Hy. }
    rewrite (demand_bits_all w y y' Hyfull).
    apply demand_variable_shift_sound; try assumption; try apply wrap_is_word.
    now apply demand_bits_normalize.
Qed.

(** * Changes of width *)

Lemma demand_unsigned_sound : forall sw rw m x x',
  demand_bits_equal sw m x x' -> demand_bits_equal rw m (wrap sw x) (wrap sw x').
Proof.
  intros sw rw m x x' Hequal i Hi Hbit.
  destruct (Z_lt_ge_dec i (Zpos sw)) as [Hlow|Hhigh].
  - rewrite !demand_wrap_bit by lia. apply Hequal; [lia|exact Hbit].
  - rewrite !word_bits_high with (w := sw) by (try apply wrap_is_word; lia). reflexivity.
Qed.

Lemma demand_sext_sound : forall sw rw m x x',
  demand_bits_equal sw (demand_sext sw m) x x' ->
  demand_bits_equal rw m (signed sw (wrap sw x)) (signed sw (wrap sw x')).
Proof.
  intros sw rw m x x' Hequal i Hi Hbit.
  rewrite !signed_bits by (try apply wrap_is_word; lia).
  destruct (i <? Zpos sw) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite !demand_wrap_bit by lia. apply Hequal; [lia|].
    unfold demand_sext. rewrite Z.lor_spec, demand_wrap_bit, Hbit by lia. reflexivity.
  - apply Z.ltb_ge in Hlow. unfold msb. rewrite !wrap_wrap.
    rewrite !demand_wrap_bit by lia. apply Hequal; [lia|].
    unfold demand_sext. rewrite Z.lor_spec.
    rewrite (proj2 (Z.eqb_neq _ _)
      (demand_shift_nonzero m (Zpos sw - 1) i ltac:(lia) Hbit)).
    unfold half. rewrite Z.pow2_bits_true by lia. apply Bool.orb_true_r.
Qed.

Lemma demand_extract_sound : forall sw rw lo m x x', 0 <= lo ->
  demand_bits_equal sw (Z.shiftl m lo) x x' ->
  demand_bits_equal rw m (wrap sw x / 2 ^ lo) (wrap sw x' / 2 ^ lo).
Proof.
  intros sw rw lo m x x' Hlo Hequal i Hi Hbit.
  rewrite !Z.div_pow2_bits by lia.
  destruct (Z_lt_ge_dec (i + lo) (Zpos sw)) as [Hlow|Hhigh].
  - rewrite !demand_wrap_bit by lia. apply Hequal; [lia|].
    rewrite Z.shiftl_spec by lia. now replace (i + lo - lo) with i by ring.
  - rewrite !word_bits_high with (w := sw) by (try apply wrap_is_word; lia). reflexivity.
Qed.

Lemma demand_concat_sound : forall w1 w2 m x x' y y',
  demand_bits_equal w1 (Z.shiftr m (Zpos w2)) x x' ->
  demand_bits_equal w2 (wrap w2 m) y y' ->
  demand_bits_equal (w1 + w2)%positive m
    (wrap w1 x * modulus w2 + wrap w2 y) (wrap w1 x' * modulus w2 + wrap w2 y').
Proof.
  intros w1 w2 m x x' y y' Hx Hy i Hi Hbit. unfold modulus.
  rewrite !split_sum_bits by (try lia; apply wrap_is_word).
  destruct (i <? Zpos w2) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite !demand_wrap_bit by lia. apply Hy; [lia|].
    now rewrite demand_wrap_bit by lia.
  - apply Z.ltb_ge in Hlow. rewrite Pos2Z.inj_add in Hi.
    rewrite !demand_wrap_bit by lia. apply Hx; [lia|].
    rewrite Z.shiftr_spec by lia. now replace (i - Zpos w2 + Zpos w2) with i by ring.
Qed.

Lemma demand_ite_sound : forall w m c c' x x' y y',
  demand_bits_equal 1%positive 1 c c' -> demand_bits_equal w m x x' ->
  demand_bits_equal w m y y' ->
  demand_bits_equal w m
    (if wrap 1%positive c =? 1 then wrap w x else wrap w y)
    (if wrap 1%positive c' =? 1 then wrap w x' else wrap w y').
Proof.
  intros w m c c' x x' y y' Hc Hx Hy.
  assert (Heq : wrap 1%positive c = wrap 1%positive c').
  { apply demand_bits_all. exact Hc. }
  rewrite Heq. destruct (wrap 1%positive c' =? 1); now apply demand_bits_normalize.
Qed.

(** * Operator evaluation *)

Lemma demand_unary_sound : forall o w rw m x x' consts,
  result_width o [w] = Some rw -> is_word rw m ->
  agree_masks (demand_raw o [w] consts m) [(w, x)] [(w, x')] ->
  demand_bits_equal rw m (op_value o [normalize_word (w, x)])
    (op_value o [normalize_word (w, x')]).
Proof.
  intros o w rw m x x' consts Hwidth Hm Hagree.
  destruct o; cbn [result_width] in Hwidth; try discriminate;
    repeat match type of Hwidth with
    | (if ?guard then _ else _) = _ => destruct guard eqn:?; try discriminate
    end; injection Hwidth as <-;
    cbn [demand_raw] in Hagree; apply demand_agree_cons in Hagree;
    destruct Hagree as [Hbits Htail];
    cbn [normalize_word fst snd op_value word_fun1].
  - apply demand_bits_not. now apply demand_bits_normalize.
  - unfold wneg. apply demand_bits_normalize. apply demand_bits_neg; [exact Hm|].
    now apply demand_bits_normalize.
  - apply demand_bits_full. now rewrite (demand_bits_all w x x' Hbits).
  - apply demand_bits_full. now rewrite (demand_bits_all w x x' Hbits).
  - apply demand_bits_full. now rewrite (demand_bits_all w x x' Hbits).
  - apply demand_unsigned_sound. exact (proj1 (demand_bits_mask_wrap w m x x') Hbits).
  - now apply demand_sext_sound.
  - apply demand_unsigned_sound. exact Hbits.
  - apply demand_extract_sound; [lia|exact Hbits].
Qed.

Lemma demand_binary_all : forall o w v rw m x x' y y',
  demand_bits_equal w (demand_all w) x x' -> demand_bits_equal v (demand_all v) y y' ->
  demand_bits_equal rw m (op_value o [normalize_word (w, x); normalize_word (v, y)])
    (op_value o [normalize_word (w, x'); normalize_word (v, y')]).
Proof.
  intros o w v rw m x x' y y' Hx Hy. apply demand_bits_full.
  unfold normalize_word. cbn [fst snd].
  now rewrite (demand_bits_all w x x' Hx), (demand_bits_all v y y' Hy).
Qed.

Lemma demand_binary_arithmetic : forall w m x x' y y', is_word w m ->
  demand_bits_equal w (demand_fill_down m) x x' ->
  demand_bits_equal w (demand_fill_down m) y y' ->
  demand_bits_equal w m (wadd w (wrap w x) (wrap w y))
    (wadd w (wrap w x') (wrap w y')) /\
  demand_bits_equal w m (wsub w (wrap w x) (wrap w y))
    (wsub w (wrap w x') (wrap w y')) /\
  demand_bits_equal w m (wmul w (wrap w x) (wrap w y))
    (wmul w (wrap w x') (wrap w y')).
Proof.
  intros w m x x' y y' Hm Hx Hy.
  destruct (demand_bits_arithmetic w m (wrap w x) (wrap w x') (wrap w y) (wrap w y') Hm
    (demand_bits_normalize w _ _ _ Hx) (demand_bits_normalize w _ _ _ Hy))
    as [Hadd [Hsub Hmul]].
  split; [now apply demand_bits_normalize|]. split; now apply demand_bits_normalize.
Qed.

Lemma demand_pair_agree : forall w v x x' y y' ms,
  agree_masks ms [(w, x); (v, y)] [(w, x'); (v, y')] ->
  demand_bits_equal w (hd 0 ms) x x' /\ demand_bits_equal v (hd 0 (tl ms)) y y'.
Proof.
  intros w v x x' y y' [|m ms] Hagree; [inversion Hagree|].
  apply demand_agree_cons in Hagree. destruct Hagree as [Hx Htail].
  destruct ms as [|n ms]; [inversion Htail|].
  apply demand_agree_cons in Htail. destruct Htail as [Hy Hrest].
  split; assumption.
Qed.

Lemma demand_binary_sound : forall o w v rw m x x' y y' consts,
  result_width o [w; v] = Some rw -> is_word rw m ->
  consts_hold consts [(w, x); (v, y)] -> consts_hold consts [(w, x'); (v, y')] ->
  agree_masks (demand_raw o [w; v] consts m) [(w, x); (v, y)] [(w, x'); (v, y')] ->
  demand_bits_equal rw m (op_value o [normalize_word (w, x); normalize_word (v, y)])
    (op_value o [normalize_word (w, x'); normalize_word (v, y')]).
Proof.
  intros o w v rw m x x' y y' consts Hwidth Hm Hconsts Hconsts' Hagree.
  pose proof (demand_const_head w x x' [(v, y)] [(v, y')] consts Hconsts Hconsts') as Hcx.
  pose proof (demand_const_second v y y' (w, x) (w, x') [] [] consts Hconsts Hconsts') as Hcy.
  destruct (demand_pair_agree w v x x' y y' _ Hagree) as [Hx Hy].
  destruct o; cbn [result_width] in Hwidth; try discriminate;
    repeat match type of Hwidth with
    | (if ?guard then _ else _) = _ => destruct guard eqn:Hguard; try discriminate
    end;
    repeat match goal with
    | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H; subst v
    end; injection Hwidth as <-;
    cbn [demand_raw map hd tl] in Hx, Hy;
    cbn [normalize_word fst snd op_value word_fun2 word_cmp];
    try solve [apply demand_bits_full;
      repeat match goal with
      | H : demand_bits_equal ?u (demand_all ?u) ?a ?b |- _ =>
        rewrite (demand_bits_all u a b H); clear H
      end; reflexivity].
  - exact (proj1 (demand_binary_arithmetic w m x x' y y' Hm Hx Hy)).
  - exact (proj1 (proj2 (demand_binary_arithmetic w m x x' y y' Hm Hx Hy))).
  - exact (proj2 (proj2 (demand_binary_arithmetic w m x x' y y' Hm Hx Hy))).
  - rewrite !word_fun2_normalised with (o := bvand) (f := wand) by reflexivity.
    exact (demand_bits_and w m x x' y y' _ _ Hcx Hcy Hx Hy).
  - rewrite !word_fun2_normalised with (o := bvor) (f := wor) by reflexivity.
    exact (demand_bits_or w m x x' y y' _ _ Hcx Hcy Hx Hy).
  - rewrite !word_fun2_normalised with (o := bvxor) (f := wxor) by reflexivity.
    now apply demand_bits_xor.
  - apply (demand_shift_sound bvshl w m (demand_known consts 1)); try assumption.
    left. reflexivity.
  - apply (demand_shift_sound bvlshr w m (demand_known consts 1)); try assumption.
    right. left. reflexivity.
  - apply (demand_shift_sound bvashr w m (demand_known consts 1)); try assumption.
    right. right. left. reflexivity.
  - apply (demand_shift_sound bvrotl w m (demand_known consts 1)); try assumption.
    right. right. right. left. reflexivity.
  - apply (demand_shift_sound bvrotr w m (demand_known consts 1)); try assumption.
    right. right. right. right. reflexivity.
  - now apply demand_concat_sound.
Qed.

Lemma demand_ternary_sound : forall o c w v rw m b b' x x' y y' consts,
  result_width o [c; w; v] = Some rw ->
  agree_masks (demand_raw o [c; w; v] consts m)
    [(c, b); (w, x); (v, y)] [(c, b'); (w, x'); (v, y')] ->
  demand_bits_equal rw m
    (op_value o [normalize_word (c, b); normalize_word (w, x); normalize_word (v, y)])
    (op_value o [normalize_word (c, b'); normalize_word (w, x'); normalize_word (v, y')]).
Proof.
  intros o c w v rw m b b' x x' y y' consts Hwidth Hagree.
  destruct o; cbn [result_width] in Hwidth; try discriminate.
  destruct (Pos.eqb c 1 && Pos.eqb w v) eqn:Hguard; [|discriminate].
  apply Bool.andb_true_iff in Hguard. destruct Hguard as [Hc Hwv].
  apply Pos.eqb_eq in Hc, Hwv. subst c v. injection Hwidth as <-.
  cbn [demand_raw] in Hagree. apply demand_agree_cons in Hagree.
  destruct Hagree as [Hcondition Htail]. apply demand_agree_cons in Htail.
  destruct Htail as [Hx Htail]. apply demand_agree_cons in Htail.
  destruct Htail as [Hy Htail].
  cbn [normalize_word fst snd op_value]. now apply demand_ite_sound.
Qed.

Lemma demand_values_sound : forall o xs ys consts rw m,
  result_width o (map fst xs) = Some rw -> map fst xs = map fst ys -> is_word rw m ->
  consts_hold consts xs -> consts_hold consts ys ->
  agree_masks (demand_raw o (map fst xs) consts m) xs ys ->
  demand_bits_equal rw m (op_value o (map normalize_word xs))
    (op_value o (map normalize_word ys)).
Proof.
  intros o xs ys consts rw m Hwidth Hsame Hm Hconsts Hconsts' Hagree.
  pose proof (result_width_arity o _ rw Hwidth) as Hlen. rewrite length_map in Hlen.
  assert (Hbound : (length xs <= 3)%nat) by (rewrite Hlen; destruct o; cbn; lia).
  destruct xs as [|[w x] [|[v y] [|[t z] [|q xs]]]]; cbn in Hbound; try lia.
  - destruct o; discriminate.
  - destruct ys as [|[u x'] [|[v' y'] [|[t' z'] [|q ys]]]];
      cbn [map fst] in Hsame; try discriminate; inversion Hsame; subst.
    cbn [map] in *. eapply demand_unary_sound; eassumption.
  - destruct ys as [|[u x'] [|[v' y'] [|[t' z'] [|q ys]]]];
      cbn [map fst] in Hsame; try discriminate; inversion Hsame; subst.
    cbn [map] in *. eapply demand_binary_sound; eassumption.
  - destruct ys as [|[u x'] [|[v' y'] [|[t' z'] [|q ys]]]];
      cbn [map fst] in Hsame; try discriminate; inversion Hsame; subst.
    cbn [map] in *. eapply demand_ternary_sound; eassumption.
Qed.

(** Evaluations of operands agreeing on the demanded masks agree on the result mask. *)
Theorem demand_sound : forall o consts m xs ys r1 r2,
  map fst xs = map fst ys -> consts_hold consts xs -> consts_hold consts ys ->
  agree_masks (demand o (map fst xs) consts m) xs ys ->
  eval_op o xs = Some r1 -> eval_op o ys = Some r2 ->
  agree (mask_agreement (fst r1)) m r1 r2.
Proof.
  intros o consts m xs ys r1 r2 Hsame Hconsts Hconsts' Hagree Heval Heval'.
  unfold eval_op in Heval, Heval'. rewrite <- Hsame in Heval'.
  destruct (result_width o (map fst xs)) as [rw|] eqn:Hwidth; [|discriminate].
  injection Heval as <-. injection Heval' as <-. cbn [fst].
  apply mask_agree_bits. change (demand_bits_equal rw m
    (wrap rw (op_value o (map normalize_word xs)))
    (wrap rw (op_value o (map normalize_word ys)))).
  apply (proj1 (demand_bits_mask_wrap rw m _ _)).
  apply demand_bits_normalize. unfold demand in Hagree. rewrite Hwidth in Hagree.
  destruct (wrap rw m =? 0) eqn:Hzero.
  - intros i Hi Hbit. apply Z.eqb_eq in Hzero. rewrite Hzero, Z.bits_0 in Hbit.
    discriminate.
  - eapply demand_values_sound; try eassumption. apply wrap_is_word.
Qed.
