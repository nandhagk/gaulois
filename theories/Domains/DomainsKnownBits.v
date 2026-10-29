(** * Known zero and one bits

    Two masks describe independent facts about the bits of a machine word.
    For example, [Tnum 15 128] describes eight-bit words with a clear low nibble and set sign bit.
    Builds on: OrderLattice, DomainsNumeric and the Bits word and bit equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import
  BitsWord BitsFun BitsOp BitsTestbit BitsArith BitsSigned BitsExtend.
From Gaulois.Domains Require Import DomainsNumeric.
Import List.ListNotations.

Open Scope Z_scope.

(** A set bit in either mask records the corresponding known Boolean value. *)
Record tnum : Type := Tnum {
  zeros : Z;
  ones : Z
}.

Definition tnum_normalise (w : width) (t : tnum) : tnum :=
  Tnum (wrap w (zeros t)) (wrap w (ones t)).

Definition tnum_join (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_meet (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_subset (w : width) (a b : Z) : bool :=
  Z.eqb (wand w a b) (wrap w a).

(** More precise facts contain every known bit of the less precise fact. *)
Definition tnum_lattice (w : width) : lattice tnum :=
  {| leb a b := tnum_subset w (zeros b) (zeros a) &&
       tnum_subset w (ones b) (ones a);
     bot := Tnum (modulus w - 1) (modulus w - 1);
     join := tnum_join w;
     widen := tnum_join w;
     narrow a _ := a |}.

(** Concretisation reads masks modulo the word width, including conflicting masks. *)
Definition tnum_gamma (w : width) (t : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros t)) = 0 /\
  Z.land (wrap w (ones t)) (Z.lnot z) = 0.

Lemma tnum_subset_bits : forall w a b,
  tnum_subset w a b = true <->
  forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit b i = true.
Proof.
  intros w a b. unfold tnum_subset. rewrite Z.eqb_eq. split.
  - intros Heq i [Hi Hiw] Hbit.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    unfold wand in Heq. rewrite Z.land_spec, !testbit_wrap in Heq by exact Hi.
    rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw), Hbit in Heq. cbn in Heq.
    exact Heq.
  - intros Hbits. apply Z.bits_inj'. intros i Hi.
    unfold wand. rewrite Z.land_spec, !testbit_wrap by exact Hi.
    destruct (i <? Zpos w) eqn:Hlow; cbn; [|reflexivity].
    destruct (Z.testbit a i) eqn:Ha; cbn; [|reflexivity].
    apply Hbits; [apply Z.ltb_lt in Hlow; lia|exact Ha].
Qed.

(** * Transfer equality at the finite-width boundary *)

Definition tnum_equiv (w : width) (a b : tnum) : Prop :=
  wrap w (zeros a) = wrap w (zeros b) /\ wrap w (ones a) = wrap w (ones b).

Lemma tnum_equiv_bits : forall w a b,
  tnum_equiv w a b <->
  forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros a) i = Z.testbit (zeros b) i /\
    Z.testbit (ones a) i = Z.testbit (ones b) i.
Proof.
  intros w a b. unfold tnum_equiv. split.
  - intros [Hz Ho] i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hz, Ho.
    rewrite !testbit_wrap in Hz, Ho by lia.
    rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)) in Hz, Ho.
    exact (conj Hz Ho).
  - intro Hbits. split; apply Z.bits_inj'; intros i Hi;
      rewrite !testbit_wrap by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try reflexivity;
      apply Z.ltb_lt in Hlow;
      first [apply (proj1 (Hbits i ltac:(lia)))|apply (proj2 (Hbits i ltac:(lia)))].
Qed.

Lemma tnum_leb_bits : forall w a b,
  leb (tnum_lattice w) a b = true <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros b) i = true -> Z.testbit (zeros a) i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones b) i = true -> Z.testbit (ones a) i = true).
Proof.
  intros w a b. cbn [tnum_lattice leb]. rewrite andb_true_iff, !tnum_subset_bits.
  reflexivity.
Qed.

Lemma tnum_join_bits : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (zeros (tnum_join w a b)) i =
    (Z.testbit (zeros a) i && Z.testbit (zeros b) i) /\
  Z.testbit (ones (tnum_join w a b)) i =
    (Z.testbit (ones a) i && Z.testbit (ones b) i).
Proof.
  intros w a b i [Hi Hiw]. cbn [tnum_join zeros ones]. unfold wand.
  rewrite !Z.land_spec, !testbit_wrap by exact Hi.
  rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw). split; reflexivity.
Qed.

Lemma tnum_all_bits : forall w i, 0 <= i < Zpos w ->
  Z.testbit (modulus w - 1) i = true.
Proof.
  intros w i Hi. unfold modulus. replace (2 ^ Zpos w - 1) with (Z.ones (Zpos w))
    by (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.ones_spec_low by exact Hi. reflexivity.
Qed.

(** The reverse inclusion order and mask intersection satisfy the weak lattice laws. *)
Theorem tnum_laws : forall w, lattice_laws (tnum_lattice w).
Proof.
  intro w. constructor.
  - intro a. apply tnum_leb_bits. split; auto.
  - intros a b c Hab Hbc. apply tnum_leb_bits in Hab, Hbc.
    apply tnum_leb_bits. destruct Hab as [Haz Hao], Hbc as [Hbz Hbo].
    split; intros i Hi Hbit; [apply Haz, Hbz|apply Hao, Hbo]; assumption.
  - intro a. apply tnum_leb_bits. split; intros i Hi _; apply tnum_all_bits; exact Hi.
  - intros a b. apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [join tnum_lattice] in Hbit;
      (rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hbit ||
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Hbit);
      apply andb_true_iff in Hbit; tauto.
  - intros a b. apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [join tnum_lattice] in Hbit;
      (rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hbit ||
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Hbit);
      apply andb_true_iff in Hbit; tauto.
  - intros a b. apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [widen tnum_lattice] in Hbit;
      (rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hbit ||
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Hbit);
      apply andb_true_iff in Hbit; tauto.
  - intros a b. apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [widen tnum_lattice] in Hbit;
      (rewrite (proj1 (tnum_join_bits w a b i Hi)) in Hbit ||
      rewrite (proj2 (tnum_join_bits w a b i Hi)) in Hbit);
      apply andb_true_iff in Hbit; tauto.
  - intros a b _. apply tnum_leb_bits. split; auto.
  - intros a b Hle. exact Hle.
Qed.

(** Mask intersection is the least upper bound for the known-bit order. *)
Theorem tnum_lub : forall w, lub_laws (tnum_lattice w).
Proof.
  intro w. constructor. intros a b c Ha Hb.
  apply tnum_leb_bits in Ha, Hb. destruct Ha as [Haz Hao], Hb as [Hbz Hbo].
  apply tnum_leb_bits. split; intros i Hi Hbit.
  - cbn [join tnum_lattice]. rewrite (proj1 (tnum_join_bits w a b i Hi)).
    apply andb_true_iff. split; auto.
  - cbn [join tnum_lattice]. rewrite (proj2 (tnum_join_bits w a b i Hi)).
    apply andb_true_iff. split; auto.
Qed.

(** Mask meaning is equivalent to its independent per-bit implications. *)
Lemma tnum_gamma_bits : forall w t z,
  tnum_gamma w t z <->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros t) i = true -> Z.testbit z i = false) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (ones t) i = true -> Z.testbit z i = true).
Proof.
  intros w t z. unfold tnum_gamma. split.
  - intros [Hz Ho]. split; intros i [Hi Hiw] Hbit.
    + apply (f_equal (fun x => Z.testbit x i)) in Hz.
      rewrite Z.land_spec, testbit_wrap, Z.bits_0 in Hz by exact Hi.
      rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw), Hbit, andb_true_r in Hz.
      exact Hz.
    + apply (f_equal (fun x => Z.testbit x i)) in Ho.
      rewrite Z.land_spec, testbit_wrap, Z.lnot_spec, Z.bits_0 in Ho by exact Hi.
      rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw), Hbit in Ho. cbn in Ho.
      now apply negb_false_iff in Ho.
  - intros [Hz Ho]. split; apply Z.bits_inj'; intros i Hi;
      rewrite Z.land_spec, testbit_wrap, ?Z.lnot_spec, Z.bits_0 by exact Hi;
      destruct (i <? Zpos w) eqn:Hlow; cbn; try apply andb_false_r; try reflexivity;
      apply Z.ltb_lt in Hlow.
    + destruct (Z.testbit (zeros t) i) eqn:Hbit; [rewrite (Hz i ltac:(lia) Hbit)|];
        cbn; now rewrite ?andb_false_r.
    + destruct (Z.testbit (ones t) i) eqn:Hbit; [rewrite (Ho i ltac:(lia) Hbit)|];
        reflexivity.
Qed.

Lemma tnum_gamma_monotone : forall w a b z,
  leb (tnum_lattice w) a b = true -> tnum_gamma w a z -> tnum_gamma w b z.
Proof.
  intros w a b z Hle Hgamma. apply tnum_leb_bits in Hle.
  apply tnum_gamma_bits in Hgamma. apply tnum_gamma_bits.
  destruct Hle as [Hlez Hleo], Hgamma as [Hz Ho].
  split; intros i Hi Hbit; [apply Hz, Hlez|apply Ho, Hleo]; assumption.
Qed.

Lemma tnum_gamma_bot_empty : forall w z, ~ tnum_gamma w (bot (tnum_lattice w)) z.
Proof.
  intros w z Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  pose proof (tnum_all_bits w 0 ltac:(lia)) as Hbit.
  specialize (Hz 0 ltac:(lia) Hbit). specialize (Ho 0 ltac:(lia) Hbit).
  congruence.
Qed.

(** * The finite height *)

Definition tnum_unknown (w : width) (m : Z) : nat :=
  length (filter (fun i => negb (Z.testbit m (Z.of_nat i))) (seq 0 (Pos.to_nat w))).

Definition tnum_rank (w : width) (a : tnum) : nat :=
  (tnum_unknown w (zeros a) + tnum_unknown w (ones a))%nat.

Lemma filter_count_monotone : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  (length (filter f xs) <= length (filter g xs))%nat.
Proof.
  intros A f g xs. induction xs as [|x xs IH]; intro Hsub; [reflexivity|].
  assert (Htail : (length (filter f xs) <= length (filter g xs))%nat).
  { apply IH. intros y Hy. apply Hsub. now right. }
  specialize (Hsub x (or_introl eq_refl)). cbn [filter].
  destruct (f x), (g x); cbn in *; try discriminate; lia.
Qed.

Lemma filter_count_equal : forall (A : Type) (f g : A -> bool) xs,
  (forall x, In x xs -> f x = true -> g x = true) ->
  length (filter f xs) = length (filter g xs) ->
  forall x, In x xs -> f x = g x.
Proof.
  intros A f g xs. induction xs as [|y xs IH]; intros Hsub Hcount x Hin.
  - contradiction.
  - assert (Htailsub : forall a, In a xs -> f a = true -> g a = true).
    { intros a Ha. apply Hsub. now right. }
    pose proof (filter_count_monotone A f g xs Htailsub) as Htail.
    pose proof (Hsub y (or_introl eq_refl)) as Hhead.
    cbn [filter] in Hcount.
    destruct (f y) eqn:Hf, (g y) eqn:Hg; cbn in Hcount;
      try discriminate; try lia.
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|lia|exact Hin].
    + destruct Hin as [->|Hin]; [now rewrite Hf, Hg|].
      apply IH; [exact Htailsub|exact Hcount|exact Hin].
Qed.

Lemma tnum_unknown_monotone : forall w a b,
  tnum_subset w b a = true -> (tnum_unknown w a <= tnum_unknown w b)%nat.
Proof.
  intros w a b Hsub. rewrite tnum_subset_bits in Hsub.
  apply filter_count_monotone. intros i Hi Hbit. apply in_seq in Hi.
  apply negb_true_iff in Hbit. apply negb_true_iff.
  destruct (Z.testbit b (Z.of_nat i)) eqn:Hb; [|reflexivity].
  specialize (Hsub (Z.of_nat i) ltac:(rewrite <- positive_nat_Z; lia) Hb).
  congruence.
Qed.

Lemma tnum_unknown_equal : forall w a b,
  tnum_subset w b a = true -> tnum_unknown w a = tnum_unknown w b ->
  tnum_subset w a b = true.
Proof.
  intros w a b Hsub Hcount. apply tnum_subset_bits. intros i Hi Hbit.
  assert (Himp : forall j, In j (seq 0 (Pos.to_nat w)) ->
    negb (Z.testbit a (Z.of_nat j)) = true ->
    negb (Z.testbit b (Z.of_nat j)) = true).
  { intros j Hj Hzero. apply in_seq in Hj. apply negb_true_iff in Hzero.
    apply negb_true_iff. rewrite tnum_subset_bits in Hsub.
    destruct (Z.testbit b (Z.of_nat j)) eqn:Hb; [|reflexivity].
    specialize (Hsub (Z.of_nat j) ltac:(rewrite <- positive_nat_Z; lia) Hb).
    congruence. }
  pose proof (filter_count_equal nat _ _ _ Himp Hcount (Z.to_nat i)
    ltac:(apply in_seq; cbn [Nat.add]; split; [lia|]; apply Nat2Z.inj_lt;
      rewrite Z2Nat.id, positive_nat_Z by lia; lia)) as Heq.
  cbn beta in Heq. rewrite Z2Nat.id in Heq by lia. rewrite Hbit in Heq.
  destruct (Z.testbit b i); cbn in Heq; congruence.
Qed.

Lemma tnum_rank_monotone : forall w a b,
  leb (tnum_lattice w) a b = true -> (tnum_rank w a <= tnum_rank w b)%nat.
Proof.
  intros w a b Hle. apply andb_true_iff in Hle as [Hz Ho].
  apply tnum_unknown_monotone in Hz, Ho. unfold tnum_rank. lia.
Qed.

Lemma tnum_rank_equal : forall w a b,
  leb (tnum_lattice w) a b = true -> tnum_rank w a = tnum_rank w b ->
  leb (tnum_lattice w) b a = true.
Proof.
  intros w a b Hle Heq. apply andb_true_iff in Hle as [Hz Ho].
  pose proof (tnum_unknown_monotone w _ _ Hz).
  pose proof (tnum_unknown_monotone w _ _ Ho).
  apply andb_true_iff. unfold tnum_rank in Heq.
  split; apply tnum_unknown_equal; try assumption; lia.
Qed.

(** Each strictly ascending join forgets at least one of the [2w] independent bit facts. *)
Definition tnum_height (w : width) : monotone_height (tnum_lattice w).
Proof.
  unshelve refine (@MonotoneHeight _ _
    (@Height _ _ (tnum_rank w) (2 * Pos.to_nat w)%nat _ _) _).
  - intro a. unfold tnum_rank, tnum_unknown.
    pose proof (filter_length_le (fun i => negb (Z.testbit (zeros a) (Z.of_nat i)))
      (seq 0 (Pos.to_nat w))) as Hz.
    pose proof (filter_length_le (fun i => negb (Z.testbit (ones a) (Z.of_nat i)))
      (seq 0 (Pos.to_nat w))) as Ho.
    rewrite length_seq in Hz, Ho. lia.
  - intros a b Hstrict.
    pose proof (join_upper_l (tnum_laws w) a b) as Hle.
    pose proof (tnum_rank_monotone w _ _ Hle) as Hrank.
    destruct (Nat.eq_dec (tnum_rank w a) (tnum_rank w (join (tnum_lattice w) a b)))
      as [Heq|Hneq]; [|lia].
    pose proof (tnum_rank_equal w _ _ Hle Heq). congruence.
  - exact (tnum_rank_monotone w).
Defined.

(** The height rank is the specified complement of the two population counts. *)
Lemma tnum_rank_popcount : forall w a,
  Z.of_nat (tnum_rank w a) =
    2 * Zpos w - wpopcnt w (zeros a) - wpopcnt w (ones a).
Proof.
  intros w a. unfold tnum_rank, tnum_unknown, wpopcnt.
  assert (Hmask : forall m,
    filter (fun i => Z.testbit (wrap w m) (Z.of_nat i)) (seq 0 (Pos.to_nat w)) =
    filter (fun i => Z.testbit m (Z.of_nat i)) (seq 0 (Pos.to_nat w))).
  { intro m. apply filter_ext_in. intros i Hi. apply in_seq in Hi.
    rewrite testbit_wrap by lia.
    rewrite (proj2 (Z.ltb_lt (Z.of_nat i) (Zpos w))) by
      (rewrite <- positive_nat_Z; lia). reflexivity. }
  rewrite !Hmask, Nat2Z.inj_add.
  pose proof (filter_complement_length nat (fun i => Z.testbit (zeros a) (Z.of_nat i))
    (seq 0 (Pos.to_nat w))) as Hz.
  pose proof (filter_complement_length nat (fun i => Z.testbit (ones a) (Z.of_nat i))
    (seq 0 (Pos.to_nat w))) as Ho.
  rewrite length_seq in Hz, Ho. rewrite <- positive_nat_Z. lia.
Qed.

(** * Elementary mask operations *)

Lemma tnum_wrap_bit : forall w m i, 0 <= i < Zpos w ->
  Z.testbit (wrap w m) i = Z.testbit m i.
Proof.
  intros w m i [Hi Hiw]. rewrite testbit_wrap by exact Hi.
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) Hiw).
Qed.

Lemma tnum_and_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wand w a b) i = (Z.testbit a i && Z.testbit b i).
Proof.
  intros w a b i Hi. unfold wand. now rewrite Z.land_spec, !tnum_wrap_bit by exact Hi.
Qed.

Lemma tnum_or_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wor w a b) i = (Z.testbit a i || Z.testbit b i).
Proof.
  intros w a b i Hi. unfold wor. now rewrite Z.lor_spec, !tnum_wrap_bit by exact Hi.
Qed.

Lemma tnum_xor_bit : forall w a b i, 0 <= i < Zpos w ->
  Z.testbit (wxor w a b) i = xorb (Z.testbit a i) (Z.testbit b i).
Proof.
  intros w a b i Hi. unfold wxor. now rewrite Z.lxor_spec, !tnum_wrap_bit by exact Hi.
Qed.

Lemma tnum_not_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (wnot w a) i = negb (Z.testbit a i).
Proof.
  intros w a i Hi. rewrite wnot_lnot, tnum_wrap_bit, Z.lnot_spec,
    tnum_wrap_bit by (try exact Hi; lia). reflexivity.
Qed.

Definition tnum_top : tnum := Tnum 0 0.

Definition tnum_const (w : width) (z : Z) : tnum := Tnum (wnot w z) (wrap w z).

Definition tnum_not (w : width) (a : tnum) : tnum :=
  Tnum (wrap w (ones a)) (wrap w (zeros a)).

Definition tnum_and (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (zeros a) (zeros b)) (wand w (ones a) (ones b)).

Definition tnum_or (w : width) (a b : tnum) : tnum :=
  Tnum (wand w (zeros a) (zeros b)) (wor w (ones a) (ones b)).

Definition tnum_xor (w : width) (a b : tnum) : tnum :=
  Tnum (wor w (wand w (zeros a) (zeros b)) (wand w (ones a) (ones b)))
    (wor w (wand w (zeros a) (ones b)) (wand w (ones a) (zeros b))).

Lemma tnum_top_sound : forall w z, tnum_gamma w tnum_top z.
Proof.
  intros w z. unfold tnum_gamma, tnum_top. cbn [zeros ones].
  rewrite wrap_0, Z.land_0_r, Z.land_0_l. auto.
Qed.

Lemma tnum_const_sound : forall w z, tnum_gamma w (tnum_const w z) (wrap w z).
Proof.
  intros w z. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_const zeros ones] in Hbit.
  - rewrite (tnum_not_bit w z i Hi) in Hbit.
    rewrite (tnum_wrap_bit w z i Hi). now apply negb_true_iff in Hbit.
  - rewrite (tnum_wrap_bit w z i Hi) in Hbit |- *. exact Hbit.
Qed.

Lemma tnum_normalise_sound : forall w a z,
  tnum_gamma w (tnum_normalise w a) z <-> tnum_gamma w a z.
Proof.
  intros w a z. rewrite !tnum_gamma_bits.
  assert (Hz : forall i, 0 <= i < Zpos w ->
    Z.testbit (zeros (tnum_normalise w a)) i = Z.testbit (zeros a) i).
  { intros i Hi. apply tnum_wrap_bit. exact Hi. }
  assert (Ho : forall i, 0 <= i < Zpos w ->
    Z.testbit (ones (tnum_normalise w a)) i = Z.testbit (ones a) i).
  { intros i Hi. apply tnum_wrap_bit. exact Hi. }
  split; intros [Hgz Hgo]; split; intros i Hi Hbit.
  - apply (Hgz i Hi). now rewrite Hz.
  - apply (Hgo i Hi). now rewrite Ho.
  - apply (Hgz i Hi). now rewrite Hz in Hbit.
  - apply (Hgo i Hi). now rewrite Ho in Hbit.
Qed.

Lemma tnum_meet_sound : forall w a b z,
  tnum_gamma w a z -> tnum_gamma w b z -> tnum_gamma w (tnum_meet w a b) z.
Proof.
  intros w a b z Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_meet zeros ones] in Hbit;
    rewrite tnum_or_bit in Hbit by exact Hi; apply orb_true_iff in Hbit as [Hbit|Hbit].
  - now apply Haz.
  - now apply Hbz.
  - now apply Hao.
  - now apply Hbo.
Qed.

Lemma tnum_meet_lower_left : forall w a b,
  leb (tnum_lattice w) (tnum_meet w a b) a = true.
Proof.
  intros w a b. apply tnum_leb_bits. split; intros i Hi Hbit;
    cbn [tnum_meet zeros ones]; rewrite tnum_or_bit, Hbit by exact Hi; reflexivity.
Qed.

Lemma tnum_join_sound : forall w a b z,
  tnum_gamma w a z \/ tnum_gamma w b z -> tnum_gamma w (tnum_join w a b) z.
Proof.
  intros w a b z [Ha|Hb]; eapply tnum_gamma_monotone; try eassumption.
  - apply (join_upper_l (tnum_laws w)).
  - apply (join_upper_r (tnum_laws w)).
Qed.

Lemma tnum_not_sound : forall w a z,
  tnum_gamma w a z -> tnum_gamma w (tnum_not w a) (wnot w z).
Proof.
  intros w a z Hgamma. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_not zeros ones] in Hbit;
    rewrite tnum_wrap_bit in Hbit by exact Hi; rewrite tnum_not_bit by exact Hi.
  - now rewrite (Ho i Hi Hbit).
  - now rewrite (Hz i Hi Hbit).
Qed.

Lemma tnum_and_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_and w a b) (wand w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_and zeros ones] in Hbit;
    rewrite tnum_and_bit by exact Hi.
  - rewrite tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Hz|Hz].
    + now rewrite (Haz i Hi Hz).
    + rewrite (Hbz i Hi Hz). apply andb_false_r.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Ho Ho'].
    now rewrite (Hao i Hi Ho), (Hbo i Hi Ho').
Qed.

Lemma tnum_or_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_or w a b) (wor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_or zeros ones] in Hbit;
    rewrite tnum_or_bit by exact Hi.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hz Hz'].
    now rewrite (Haz i Hi Hz), (Hbz i Hi Hz').
  - rewrite tnum_or_bit in Hbit by exact Hi. apply orb_true_iff in Hbit as [Ho|Ho].
    + now rewrite (Hao i Hi Ho).
    + rewrite (Hbo i Hi Ho). apply orb_true_r.
Qed.

Lemma tnum_xor_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_xor w a b) (wxor w x y).
Proof.
  intros w a b x y Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_xor zeros ones] in Hbit;
    rewrite tnum_or_bit, !tnum_and_bit in Hbit by exact Hi;
    rewrite tnum_xor_bit by exact Hi;
    apply orb_true_iff in Hbit as [Hbit|Hbit]; apply andb_true_iff in Hbit as [Hl Hr].
  - now rewrite (Haz i Hi Hl), (Hbz i Hi Hr).
  - now rewrite (Hao i Hi Hl), (Hbo i Hi Hr).
  - now rewrite (Haz i Hi Hl), (Hbo i Hi Hr).
  - now rewrite (Hao i Hi Hl), (Hbz i Hi Hr).
Qed.

(** * Carry bounds for arithmetic *)

Definition tnum_carry (a b c : Z) (initial : bool) : Prop :=
  c / 2 = Z.lor (Z.land a b) (Z.land c (Z.lor a b)) /\ Z.testbit c 0 = initial.

Lemma tnum_carry_step : forall a b c initial i,
  tnum_carry a b c initial -> 0 <= i ->
  Z.testbit c (Z.succ i) =
    ((Z.testbit a i && Z.testbit b i) ||
      (Z.testbit c i && (Z.testbit a i || Z.testbit b i))).
Proof.
  intros a b c initial i [Hstep _] Hi.
  rewrite <- Z.div2_bits by exact Hi.
  rewrite Hstep, !Z.lor_spec, !Z.land_spec, !Z.lor_spec.
  reflexivity.
Qed.

Lemma tnum_carry_monotone : forall w a b a' b' c c' initial,
  tnum_carry a b c initial -> tnum_carry a' b' c' initial ->
  (forall i, 0 <= i < Zpos w -> Z.testbit a i = true -> Z.testbit a' i = true) ->
  (forall i, 0 <= i < Zpos w -> Z.testbit b i = true -> Z.testbit b' i = true) ->
  forall i, 0 <= i <= Zpos w -> Z.testbit c i = true -> Z.testbit c' i = true.
Proof.
  intros w a b a' b' c c' initial Hc Hc' Ha Hb i Hi.
  assert (Hnat : forall n, (n <= Pos.to_nat w)%nat ->
    Z.testbit c (Z.of_nat n) = true -> Z.testbit c' (Z.of_nat n) = true).
  { intro n. induction n as [|n IH]; intros Hn Hbit.
    - change (Z.testbit c 0 = true) in Hbit. rewrite (proj2 Hc) in Hbit.
      change (Z.testbit c' 0 = true). now rewrite (proj2 Hc').
    - rewrite Nat2Z.inj_succ,
        (tnum_carry_step a b c initial (Z.of_nat n) Hc ltac:(lia)) in Hbit.
      rewrite Nat2Z.inj_succ,
        (tnum_carry_step a' b' c' initial (Z.of_nat n) Hc' ltac:(lia)).
      pose proof (Ha (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Haa.
      pose proof (Hb (Z.of_nat n) ltac:(rewrite <- positive_nat_Z; lia)) as Hbb.
      specialize (IH ltac:(lia)).
      destruct (Z.testbit a (Z.of_nat n)), (Z.testbit b (Z.of_nat n)),
        (Z.testbit a' (Z.of_nat n)), (Z.testbit b' (Z.of_nat n)),
        (Z.testbit c (Z.of_nat n)), (Z.testbit c' (Z.of_nat n));
        cbn in *; intuition discriminate. }
  replace i with (Z.of_nat (Z.to_nat i)) by (rewrite Z2Nat.id; lia).
  apply Hnat. apply Nat2Z.inj_le. rewrite positive_nat_Z, Z2Nat.id by lia. lia.
Qed.

Definition tnum_min (w : width) (a : tnum) : Z := wrap w (ones a).

Definition tnum_max (w : width) (a : tnum) : Z := wnot w (zeros a).

Definition tnum_mask (w : width) (a : tnum) : Z := wnot w (wor w (zeros a) (ones a)).

Lemma tnum_value_bounds : forall w a x, tnum_gamma w a x ->
  (forall i, 0 <= i < Zpos w ->
    Z.testbit (tnum_min w a) i = true -> Z.testbit x i = true) /\
  (forall i, 0 <= i < Zpos w ->
    Z.testbit x i = true -> Z.testbit (tnum_max w a) i = true).
Proof.
  intros w a x Hgamma. apply tnum_gamma_bits in Hgamma. destruct Hgamma as [Hz Ho].
  split; intros i Hi Hbit.
  - unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hi. now apply Ho.
  - unfold tnum_max. rewrite tnum_not_bit by exact Hi.
    destruct (Z.testbit (zeros a) i) eqn:Hknown; [|reflexivity].
    specialize (Hz i Hi Hknown). congruence.
Qed.

Lemma tnum_known_bit : forall w a x i,
  tnum_gamma w a x -> 0 <= i < Zpos w -> Z.testbit (tnum_mask w a) i = false ->
  Z.testbit (tnum_min w a) i = Z.testbit x i /\
  Z.testbit (tnum_max w a) i = Z.testbit x i.
Proof.
  intros w a x i Hgamma Hi Hmask. apply tnum_gamma_bits in Hgamma.
  destruct Hgamma as [Hz Ho]. unfold tnum_mask in Hmask.
  rewrite tnum_not_bit, tnum_or_bit in Hmask by exact Hi.
  unfold tnum_min, tnum_max. rewrite tnum_wrap_bit, tnum_not_bit by exact Hi.
  specialize (Hz i Hi). specialize (Ho i Hi).
  destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
    cbn in *; intuition discriminate.
Qed.

Lemma tnum_sum_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i = false -> Z.testbit (tnum_mask w b) i = false ->
  Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i =
    Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hma Hmb Heq.
  destruct (Z.add_carry_bits x y initial) as [c [Hsum [Hstep Hzero]]].
  destruct (Z.add_carry_bits (tnum_min w a) (tnum_min w b) initial)
    as [cl [Hsuml [Hstepl Hzerol]]].
  destruct (Z.add_carry_bits (tnum_max w a) (tnum_max w b) initial)
    as [ch [Hsumh [Hsteph Hzeroh]]].
  destruct (tnum_value_bounds w a x Ha) as [Hal Hah].
  destruct (tnum_value_bounds w b y Hb) as [Hbl Hbh].
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstepl Hzerol)
    (conj Hstep Hzero) Hal Hbl i ltac:(lia)) as Hlower.
  pose proof (tnum_carry_monotone w _ _ _ _ _ _ initial (conj Hstep Hzero)
    (conj Hsteph Hzeroh) Hah Hbh i ltac:(lia)) as Hupper.
  destruct (tnum_known_bit w a x i Ha Hi Hma) as [Halbit Hahbit].
  destruct (tnum_known_bit w b y i Hb Hi Hmb) as [Hblbit Hbhbit].
  rewrite Hsuml, Hsumh, !Z.lxor_spec, Halbit, Hahbit, Hblbit, Hbhbit in Heq.
  rewrite Hsum, Hsuml, !Z.lxor_spec, Halbit, Hblbit.
  destruct (Z.testbit x i), (Z.testbit y i), (Z.testbit c i),
    (Z.testbit cl i), (Z.testbit ch i); cbn in *; intuition discriminate.
Qed.

Definition tnum_adc_uncertain (w : width) (a b : tnum) (initial : bool) : Z :=
  Z.lor (Z.lxor (tnum_min w a + tnum_min w b + Z.b2z initial)
      (tnum_max w a + tnum_max w b + Z.b2z initial))
    (Z.lor (tnum_mask w a) (tnum_mask w b)).

(** The low and high carry streams bound the result bits that may change. *)
Definition tnum_adc (w : width) (a b : tnum) (initial : bool) : tnum :=
  let v := tnum_min w a + tnum_min w b + Z.b2z initial in
  let m := tnum_adc_uncertain w a b initial in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

Lemma tnum_adc_known : forall w a b x y initial i,
  tnum_gamma w a x -> tnum_gamma w b y -> 0 <= i < Zpos w ->
  Z.testbit (tnum_adc_uncertain w a b initial) i = false ->
  Z.testbit (x + y + Z.b2z initial) i =
    Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i.
Proof.
  intros w a b x y initial i Ha Hb Hi Hm.
  unfold tnum_adc_uncertain in Hm. rewrite !Z.lor_spec, Z.lxor_spec in Hm.
  apply orb_false_iff in Hm as [Hsum Hm]. apply orb_false_iff in Hm as [Hma Hmb].
  eapply tnum_sum_known; try eassumption.
  destruct (Z.testbit (tnum_min w a + tnum_min w b + Z.b2z initial) i),
    (Z.testbit (tnum_max w a + tnum_max w b + Z.b2z initial) i);
    cbn in Hsum; congruence.
Qed.

Lemma tnum_adc_sound : forall w a b x y initial,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_adc w a b initial) (wrap w (x + y + Z.b2z initial)).
Proof.
  intros w a b x y initial Ha Hb. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_adc zeros ones] in Hbit;
    rewrite tnum_wrap_bit, ?Z.land_spec, ?Z.lnot_spec, ?Z.lor_spec in Hbit by
      (try exact Hi; lia).
  - apply negb_true_iff in Hbit. apply orb_false_iff in Hbit as [Hv Hm].
    rewrite tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
  - apply andb_true_iff in Hbit as [Hv Hm]. apply negb_true_iff in Hm.
    rewrite tnum_wrap_bit, (tnum_adc_known w a b x y initial i Ha Hb Hi Hm)
      by exact Hi. exact Hv.
Qed.

Definition tnum_add (w : width) (a b : tnum) : tnum := tnum_adc w a b false.

Definition tnum_sub (w : width) (a b : tnum) : tnum := tnum_adc w a (tnum_not w b) true.

Lemma tnum_add_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w (tnum_add w a b) (wadd w x y).
Proof.
  intros w a b x y Ha Hb. unfold tnum_add, wadd.
  replace (x + y) with (x + y + Z.b2z false) by (cbn [Z.b2z]; ring).
  now apply tnum_adc_sound.
Qed.

Lemma tnum_sub_sound : forall w a b x y,
  is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_sub w a b) (wsub w x y).
Proof.
  intros w a b x y Hy Ha Hb.
  pose proof (tnum_adc_sound w a (tnum_not w b) x (wnot w y) true Ha
    (tnum_not_sound w b y Hb)) as Hresult.
  unfold tnum_sub. cbn [Z.b2z] in Hresult. unfold wnot in Hresult.
  rewrite (wrap_id w y Hy) in Hresult.
  replace (x + (modulus w - 1 - y) + 1) with ((x - y) + 1 * modulus w)
    in Hresult by ring.
  rewrite wrap_add_modulus in Hresult. exact Hresult.
Qed.

(** * Constants and trailing-zero multiplication *)

Definition tnum_constant (w : width) (a : tnum) : option Z :=
  if wrap w (zeros a) =? wnot w (ones a) then Some (tnum_min w a) else None.

Lemma tnum_constant_value : forall w a x c,
  is_word w x -> tnum_gamma w a x -> tnum_constant w a = Some c -> x = c.
Proof.
  intros w a x c Hx Ha Hconst. unfold tnum_constant in Hconst.
  destruct (wrap w (zeros a) =? wnot w (ones a)) eqn:Heq; [|discriminate].
  inversion Hconst; subst c. apply Z.eqb_eq in Heq.
  apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho]. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_min. rewrite tnum_wrap_bit by lia.
    apply (f_equal (fun z => Z.testbit z i)) in Heq.
    rewrite tnum_wrap_bit, tnum_not_bit in Heq by lia.
    specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
      cbn in *; intuition discriminate.
  - rewrite (word_bits_high w x i Hx ltac:(lia)).
    symmetry. apply (word_bits_high w (tnum_min w a) i); [apply wrap_is_word|lia].
Qed.

Definition tnum_trailing (w : width) (a : tnum) : Z := wctz w (wnot w (zeros a)).

Lemma tnum_ctz_range : forall w x, 0 <= wctz w x <= Zpos w.
Proof.
  intros w x. destruct (Z.eq_dec (wrap w x) 0) as [Hz|Hnz].
  - unfold wctz. rewrite Hz. cbn. lia.
  - assert (Hsame : wctz w x = wctz w (wrap w x)) by
      (unfold wctz; now rewrite wrap_wrap).
    rewrite Hsame. destruct (wctz_spec w _ (wrap_is_word w x) Hnz) as [Hset _].
    split.
    + destruct (Z_le_gt_dec 0 (wctz w (wrap w x))); [assumption|].
      rewrite Z.testbit_neg_r in Hset by lia. discriminate.
    + destruct (Z_lt_ge_dec (wctz w (wrap w x)) (Zpos w)); [lia|].
      rewrite (word_bits_high w (wrap w x) (wctz w (wrap w x))
        (wrap_is_word w x) ltac:(lia)) in Hset.
      discriminate.
Qed.

Lemma tnum_trailing_clear : forall w a x i,
  tnum_gamma w a x -> 0 <= i < tnum_trailing w a -> Z.testbit x i = false.
Proof.
  intros w a x i Ha Hi. apply tnum_gamma_bits in Ha. destruct Ha as [Hz _].
  pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hrange.
  apply (Hz i ltac:(unfold tnum_trailing in Hi; lia)).
  assert (Hclear : Z.testbit (wnot w (zeros a)) i = false).
  { destruct (Z.eq_dec (wnot w (zeros a)) 0) as [Hnone|Hsome].
    - now rewrite Hnone, Z.bits_0.
    - apply (proj2 (wctz_spec w _ (wnot_is_word w _) Hsome)). exact Hi. }
  rewrite tnum_not_bit in Hclear by (unfold tnum_trailing in Hi; lia).
  now apply negb_false_iff in Hclear.
Qed.

Lemma tnum_trailing_factor : forall w a x,
  tnum_gamma w a x -> exists q, x = q * 2 ^ tnum_trailing w a.
Proof.
  intros w a x Ha. pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hrange.
  assert (Hmod : x mod 2 ^ tnum_trailing w a = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z_lt_ge_dec i (tnum_trailing w a)) as [Hlow|Hhigh].
    - rewrite Z.mod_pow2_bits_low by exact Hlow.
      eapply tnum_trailing_clear; [exact Ha|lia].
    - apply Z.mod_pow2_bits_high. unfold tnum_trailing in *. lia. }
  exists (x / 2 ^ tnum_trailing w a).
  pose proof (Z.div_mod x (2 ^ tnum_trailing w a)
    ltac:(pose proof (Z.pow_pos_nonneg 2 (tnum_trailing w a) ltac:(lia)
      ltac:(unfold tnum_trailing; lia)); lia)) as Heq.
  rewrite Hmod in Heq. lia.
Qed.

Definition tnum_mul_low (w : width) (a b : tnum) : tnum :=
  Tnum (wrap w (Z.ones (tnum_trailing w a + tnum_trailing w b))) 0.

Definition tnum_mul (w : width) (a b : tnum) : tnum :=
  match tnum_constant w a, tnum_constant w b with
  | Some x, Some y => tnum_const w (wmul w x y)
  | _, _ => tnum_mul_low w a b
  end.

Lemma tnum_mul_low_sound : forall w a b x y,
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_low w a b) (wmul w x y).
Proof.
  intros w a b x y Ha Hb.
  destruct (tnum_trailing_factor w a x Ha) as [qa Hx].
  destruct (tnum_trailing_factor w b y Hb) as [qb Hy].
  pose proof (tnum_ctz_range w (wnot w (zeros a))) as Hra.
  pose proof (tnum_ctz_range w (wnot w (zeros b))) as Hrb.
  change (0 <= tnum_trailing w a <= Zpos w) in Hra.
  change (0 <= tnum_trailing w b <= Zpos w) in Hrb.
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_mul_low zeros] in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hi.
    assert (Hlow : i < tnum_trailing w a + tnum_trailing w b).
    { destruct (Z_lt_ge_dec i (tnum_trailing w a + tnum_trailing w b)); [assumption|].
      rewrite Z.ones_spec_high in Hbit by lia. discriminate. }
    unfold wmul. rewrite tnum_wrap_bit by exact Hi. rewrite Hx, Hy.
    replace (qa * 2 ^ tnum_trailing w a * (qb * 2 ^ tnum_trailing w b)) with
      ((qa * qb) * 2 ^ (tnum_trailing w a + tnum_trailing w b)) by
      (rewrite Z.pow_add_r by lia; ring).
    apply Z.mul_pow2_bits_low. exact Hlow.
  - cbn [tnum_mul_low ones] in Hbit. rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Lemma tnum_mul_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_mul.
  destruct (tnum_constant w a) as [ca|] eqn:Hca,
    (tnum_constant w b) as [cb|] eqn:Hcb; try now apply tnum_mul_low_sound.
  rewrite (tnum_constant_value w a x ca Hx Ha Hca),
    (tnum_constant_value w b y cb Hy Hb Hcb).
  rewrite <- (wrap_id w (wmul w ca cb) (wrap_is_word w _)) at 2.
  apply tnum_const_sound.
Qed.

(** * Unsigned bounds and leading zero bits *)

Lemma tnum_bitwise_le : forall w x y,
  is_word w x -> is_word w y ->
  (forall i, 0 <= i < Zpos w -> Z.testbit x i = true -> Z.testbit y i = true) -> x <= y.
Proof.
  intros w x y Hx Hy Hbits.
  assert (Hdiff : Z.ldiff x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
    destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
    - specialize (Hbits i ltac:(lia)).
      destruct (Z.testbit x i), (Z.testbit y i); cbn in *; intuition discriminate.
    - rewrite (word_bits_high w x i Hx ltac:(lia)). reflexivity. }
  exact (proj2 (Z.ldiff_le x y (proj1 Hy) Hdiff)).
Qed.

Lemma tnum_unsigned_bounds : forall w a x,
  is_word w x -> tnum_gamma w a x -> tnum_min w a <= x <= tnum_max w a.
Proof.
  intros w a x Hx Ha. destruct (tnum_value_bounds w a x Ha) as [Hlo Hhi].
  split; apply (tnum_bitwise_le w); try assumption;
    try apply wrap_is_word; try apply wnot_is_word.
Qed.

Definition tnum_bitlen (h : Z) : Z := if h =? 0 then 0 else Z.succ (Z.log2 h).

Lemma tnum_bitlen_bound : forall h, 0 <= h ->
  0 <= tnum_bitlen h /\ h < 2 ^ tnum_bitlen h.
Proof.
  intros h Hh. unfold tnum_bitlen. destruct (h =? 0) eqn:Hz.
  - apply Z.eqb_eq in Hz. subst h. cbn. lia.
  - apply Z.eqb_neq in Hz. pose proof (Z.log2_nonneg h).
    pose proof (Z.log2_spec h ltac:(lia)). lia.
Qed.

Definition tnum_upper (w : width) (h : Z) : tnum :=
  Tnum (wnot w (Z.ones (tnum_bitlen h))) 0.

Lemma tnum_upper_sound : forall w h x,
  0 <= x <= h -> tnum_gamma w (tnum_upper w h) x.
Proof.
  intros w h x Hx. pose proof (tnum_bitlen_bound h ltac:(lia)) as [Hk Hbound].
  apply tnum_gamma_bits. split; intros i Hi Hbit.
  - cbn [tnum_upper zeros] in Hbit. rewrite tnum_not_bit in Hbit by exact Hi.
    apply negb_true_iff in Hbit.
    assert (Hhigh : tnum_bitlen h <= i).
    { destruct (Z_lt_ge_dec i (tnum_bitlen h)); [|lia].
      rewrite Z.ones_spec_low in Hbit by lia. discriminate. }
    rewrite <- (Z.mod_small x (2 ^ tnum_bitlen h) ltac:(lia)).
    apply Z.mod_pow2_bits_high. lia.
  - cbn [tnum_upper ones] in Hbit. rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Lemma tnum_udiv_bound : forall w x y,
  is_word w x -> is_word w y -> y <> 0 -> 0 <= wudiv w x y <= x.
Proof.
  intros w x y Hx Hy Hnz. rewrite wudiv_spec by assumption.
  split; [apply Z.div_pos; unfold is_word in *; lia|].
  apply Z.div_le_upper_bound; unfold is_word in *; nia.
Qed.

Lemma tnum_urem_bound : forall w x y,
  is_word w x -> is_word w y -> 0 <= wurem w x y <= x.
Proof.
  intros w x y Hx Hy. destruct (Z.eq_dec y 0) as [->|Hnz].
  - rewrite wurem_zero, (wrap_id w x Hx). unfold is_word in Hx. lia.
  - rewrite wurem_spec by assumption. split.
    + apply Z.mod_pos_bound. unfold is_word in Hy. lia.
    + apply Z.mod_le; unfold is_word in *; lia.
Qed.

Definition tnum_udiv (w : width) (a b : tnum) : tnum :=
  if wrap w (ones b) =? 0 then tnum_top else tnum_upper w (tnum_max w a).

Definition tnum_urem (w : width) (a : tnum) : tnum := tnum_upper w (tnum_max w a).

Lemma tnum_udiv_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_udiv w a b) (wudiv w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_udiv.
  destruct (wrap w (ones b) =? 0) eqn:Hnonzero; [apply tnum_top_sound|].
  apply Z.eqb_neq in Hnonzero.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hbounds.
  pose proof (wrap_is_word w (ones b)) as Hones.
  assert (Hy_nonzero : y <> 0) by (unfold tnum_min, is_word in *; lia).
  pose proof (tnum_udiv_bound w x y Hx Hy Hy_nonzero) as Hquotient.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hdividend.
  apply tnum_upper_sound. lia.
Qed.

Lemma tnum_urem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_urem w a) (wurem w x y).
Proof.
  intros w a x y Hx Hy Ha. pose proof (tnum_urem_bound w x y Hx Hy).
  pose proof (tnum_unsigned_bounds w a x Hx Ha). apply tnum_upper_sound. lia.
Qed.

(** * Copying and clearing bit positions *)

Definition tnum_bit_copy (sw rw : width) (f : Z -> Z) : Prop :=
  forall i, 0 <= i < Zpos rw ->
    (forall x, is_word sw x -> Z.testbit (f x) i = false) \/
    exists j, 0 <= j < Zpos sw /\
      forall x, is_word sw x -> Z.testbit (f x) i = Z.testbit x j.

Definition tnum_map (sw rw : width) (f : Z -> Z) (a : tnum) : tnum :=
  Tnum (wnot rw (f (tnum_max sw a))) (wrap rw (f (tnum_min sw a))).

Lemma tnum_map_sound : forall sw rw f a x,
  tnum_bit_copy sw rw f -> is_word sw x -> tnum_gamma sw a x ->
  tnum_gamma rw (tnum_map sw rw f a) (f x).
Proof.
  intros sw rw f a x Hcopy Hx Ha. apply tnum_gamma_bits in Ha.
  destruct Ha as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_map zeros ones] in Hbit.
  - rewrite tnum_not_bit in Hbit by exact Hi. apply negb_true_iff in Hbit.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]]; [now apply Hclear|].
    rewrite Hsource in Hbit by apply wnot_is_word.
    rewrite Hsource by exact Hx. unfold tnum_max in Hbit.
    rewrite tnum_not_bit in Hbit by exact Hj. apply negb_false_iff in Hbit.
    now apply Hz.
  - rewrite tnum_wrap_bit in Hbit by exact Hi.
    destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
    + rewrite Hclear in Hbit by apply wrap_is_word. discriminate.
    + rewrite Hsource in Hbit by apply wrap_is_word. rewrite Hsource by exact Hx.
      unfold tnum_min in Hbit. rewrite tnum_wrap_bit in Hbit by exact Hj.
      now apply Ho.
Qed.

Definition tnum_shift (o : op) (w : width) (a : tnum) (k : Z) : tnum :=
  match word_fun2 o with
  | Some f => tnum_map w w (fun x => f w x k) a
  | None => tnum_top
  end.

Lemma tnum_shl_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wshl w x k).
Proof.
  intros w k Hk i Hi. destruct (k <=? i) eqn:Hsmall.
  - apply Z.leb_le in Hsmall. right. exists (i - k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)),
      (proj2 (Z.leb_le k i) Hsmall). reflexivity.
  - left. intros x Hx. rewrite testbit_wshl by (try assumption; lia).
    rewrite Hsmall, andb_false_r. reflexivity.
Qed.

Lemma tnum_lshr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => wlshr w x k).
Proof.
  intros w k Hk i Hi. destruct (Z_lt_ge_dec (i + k) (Zpos w)) as [Hsmall|Hbig].
  - right. exists (i + k). split; [unfold is_word in Hk; lia|].
    intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
  - left. intros x Hx. rewrite testbit_wlshr by (try assumption; lia).
    rewrite (word_bits_high w x (i + k) Hx ltac:(lia)). apply andb_false_r.
Qed.

Lemma tnum_ashr_copy : forall w k, is_word w k ->
  tnum_bit_copy w w (fun x => washr w x k).
Proof.
  intros w k Hk i Hi. right. exists (Z.min (i + k) (Zpos w - 1)).
  split; [unfold is_word in Hk; lia|]. intros x Hx.
  rewrite testbit_washr by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos w)) (proj2 Hi)).
Qed.

Lemma tnum_rotl_copy : forall w k, tnum_bit_copy w w (fun x => wrotl w x k).
Proof.
  intros w k i Hi. right. exists ((i - wrap w k) mod Zpos w).
  split; [apply Z.mod_pos_bound; lia|]. intros x Hx.
  rewrite testbit_wrotl by exact Hi. now rewrite (wrap_id w x Hx).
Qed.

Lemma tnum_rotr_copy : forall w k, tnum_bit_copy w w (fun x => wrotr w x k).
Proof.
  intros w k. unfold wrotr. apply tnum_rotl_copy.
Qed.

Lemma tnum_shift_sound : forall o w a x k f,
  (o = bvshl \/ o = bvlshr \/ o = bvashr \/ o = bvrotl \/ o = bvrotr) ->
  word_fun2 o = Some f -> is_word w x -> is_word w k -> tnum_gamma w a x ->
  tnum_gamma w (tnum_shift o w a k) (f w x k).
Proof.
  intros o w a x k f Ho Hf Hx Hk Ha. unfold tnum_shift. rewrite Hf.
  apply (tnum_map_sound w w (fun z => f w z k) a x); try assumption.
  destruct Ho as [Ho | [Ho | [Ho | [Ho | Ho]]]]; subst o; inversion Hf; subst f.
  - now apply tnum_shl_copy.
  - now apply tnum_lshr_copy.
  - now apply tnum_ashr_copy.
  - apply tnum_rotl_copy.
  - apply tnum_rotr_copy.
Qed.

Lemma tnum_zext_copy : forall sw rw, (sw <= rw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. destruct (Z_lt_ge_dec i (Zpos sw)) as [Hlow|Hhigh].
  - right. exists i. split; [lia|]. intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
  - left. intros x Hx. rewrite tnum_wrap_bit by exact Hi.
    apply (word_bits_high sw x i Hx). lia.
Qed.

Lemma tnum_trunc_copy : forall sw rw, (rw <= sw)%positive ->
  tnum_bit_copy sw rw (fun x => wrap rw x).
Proof.
  intros sw rw Hwidth i Hi. right. exists i. split.
  - apply Pos2Z.pos_le_pos in Hwidth. lia.
  - intros x Hx. now rewrite tnum_wrap_bit by exact Hi.
Qed.

Lemma tnum_sext_copy : forall sw rw,
  tnum_bit_copy sw rw (fun x => wrap rw (signed sw x)).
Proof.
  intros sw rw i Hi. right. exists (Z.min i (Zpos sw - 1)). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. rewrite signed_bits by (try exact Hx; lia).
  destruct (i <? Zpos sw) eqn:Hlow.
  - apply Z.ltb_lt in Hlow. rewrite Z.min_l by lia. reflexivity.
  - apply Z.ltb_ge in Hlow. rewrite Z.min_r by lia. unfold msb.
    now rewrite (wrap_id sw x Hx).
Qed.

Lemma tnum_extract_copy : forall sw rw lo,
  0 <= lo -> Zpos rw + lo <= Zpos sw ->
  tnum_bit_copy sw rw (fun x => wrap rw (x / 2 ^ lo)).
Proof.
  intros sw rw lo Hlo Hwidth i Hi. right. exists (i + lo). split; [lia|].
  intros x Hx. rewrite tnum_wrap_bit by exact Hi. now rewrite Z.div_pow2_bits by lia.
Qed.

Definition tnum_concat (w v : width) (a b : tnum) : tnum :=
  Tnum (wrap (w + v)%positive (wrap w (zeros a) * modulus v + wrap v (zeros b)))
    (wrap (w + v)%positive (wrap w (ones a) * modulus v + wrap v (ones b))).

Lemma tnum_concat_sound : forall w v a b x y,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  tnum_gamma (w + v)%positive (tnum_concat w v a b) (x * modulus v + y).
Proof.
  intros w v a b x y Hx Hy Ha Hb. apply tnum_gamma_bits in Ha, Hb.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_concat zeros ones] in Hbit;
    rewrite tnum_wrap_bit in Hbit by exact Hi;
    unfold modulus in Hbit |- *;
    rewrite split_sum_bits in Hbit by (try apply wrap_is_word; lia);
    rewrite split_sum_bits by (try exact Hy; lia);
    destruct (i <? Zpos v) eqn:Hpart.
  - apply Z.ltb_lt in Hpart. rewrite tnum_wrap_bit in Hbit by lia. now apply Hbz.
  - apply Z.ltb_ge in Hpart. rewrite tnum_wrap_bit in Hbit by
      (rewrite Pos2Z.inj_add in Hi; lia). apply Haz; [rewrite Pos2Z.inj_add in Hi; lia|exact Hbit].
  - apply Z.ltb_lt in Hpart. rewrite tnum_wrap_bit in Hbit by lia. now apply Hbo.
  - apply Z.ltb_ge in Hpart. rewrite tnum_wrap_bit in Hbit by
      (rewrite Pos2Z.inj_add in Hi; lia). apply Hao; [rewrite Pos2Z.inj_add in Hi; lia|exact Hbit].
Qed.

(** * Constant transfers preserve finite joins *)

Lemma tnum_map_bits : forall sw rw f a i,
  tnum_bit_copy sw rw f -> 0 <= i < Zpos rw ->
  (Z.testbit (zeros (tnum_map sw rw f a)) i = true /\
    Z.testbit (ones (tnum_map sw rw f a)) i = false) \/
  exists j, 0 <= j < Zpos sw /\
    Z.testbit (zeros (tnum_map sw rw f a)) i = Z.testbit (zeros a) j /\
    Z.testbit (ones (tnum_map sw rw f a)) i = Z.testbit (ones a) j.
Proof.
  intros sw rw f a i Hcopy Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]].
  - left. cbn [tnum_map zeros ones].
    rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
    rewrite !Hclear by first [apply wnot_is_word|apply wrap_is_word]. auto.
  - right. exists j. split; [exact Hj|]. cbn [tnum_map zeros ones].
    rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
    rewrite !Hsource by first [apply wnot_is_word|apply wrap_is_word].
    unfold tnum_min, tnum_max. rewrite tnum_not_bit, tnum_wrap_bit by exact Hj.
    now rewrite negb_involutive.
Qed.

(** A constant transfer copies each mask bit or supplies a fixed zero-fill fact. *)
Lemma tnum_map_join : forall sw rw f a b,
  tnum_bit_copy sw rw f ->
  tnum_equiv rw (tnum_map sw rw f (tnum_join sw a b))
    (tnum_join rw (tnum_map sw rw f a) (tnum_map sw rw f b)).
Proof.
  intros sw rw f a b Hcopy. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    rewrite (proj1 (tnum_join_bits rw _ _ i Hi)),
      (proj2 (tnum_join_bits rw _ _ i Hi));
    cbn [tnum_map zeros ones];
    rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite !Hclear by first [apply wnot_is_word|apply wrap_is_word]. auto.
  - rewrite !Hsource by first [apply wnot_is_word|apply wrap_is_word].
    unfold tnum_min, tnum_max.
    rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hj.
    rewrite (proj1 (tnum_join_bits sw a b j Hj)),
      (proj2 (tnum_join_bits sw a b j Hj)), !negb_involutive. auto.
Qed.

Lemma tnum_map_composition : forall sw mw rw f g a,
  tnum_bit_copy mw rw g ->
  (forall x, is_word sw x -> is_word mw (f x)) ->
  tnum_equiv rw (tnum_map mw rw g (tnum_map sw mw f a))
    (tnum_map sw rw (fun x => g (f x)) a).
Proof.
  intros sw mw rw f g a Hcopy Hword. apply tnum_equiv_bits. intros i Hi.
  destruct (Hcopy i Hi) as [Hclear|[j [Hj Hsource]]];
    cbn [tnum_map zeros ones];
    rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hi.
  - rewrite !Hclear by first [apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply wnot_is_word|apply wrap_is_word]]. auto.
  - rewrite !Hsource by first [apply wnot_is_word|apply wrap_is_word|apply Hword;
      first [apply wnot_is_word|apply wrap_is_word]].
    unfold tnum_min, tnum_max, tnum_map. cbn [zeros ones].
    rewrite !tnum_not_bit, !tnum_wrap_bit by exact Hj.
    now rewrite negb_involutive.
Qed.

Lemma tnum_consistent : forall w a x,
  tnum_gamma w a x -> wand w (zeros a) (ones a) = 0.
Proof.
  intros w a x Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply (word_ext w); [apply wand_is_word|unfold is_word; pose proof (modulus_pos w); lia|].
  intros i Hi. rewrite Z.bits_0.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_and_bit by lia. specialize (Hz i ltac:(lia)).
    specialize (Ho i ltac:(lia)).
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit x i);
      cbn in *; intuition discriminate.
  - apply (word_bits_high w); [apply wand_is_word|lia].
Qed.

Definition tnum_empty (w : width) (a : tnum) : bool :=
  negb (wand w (zeros a) (ones a) =? 0).

Lemma tnum_empty_sound : forall w a x,
  tnum_gamma w a x -> tnum_empty w a = false.
Proof.
  intros w a x Ha. unfold tnum_empty. rewrite (tnum_consistent w a x Ha), Z.eqb_refl.
  reflexivity.
Qed.

Lemma tnum_endpoints_sound : forall w a,
  tnum_empty w a = false ->
  tnum_gamma w a (tnum_min w a) /\ tnum_gamma w a (tnum_max w a).
Proof.
  intros w a Hempty. unfold tnum_empty in Hempty.
  apply negb_false_iff, Z.eqb_eq in Hempty.
  assert (Hdisjoint : forall i, 0 <= i < Zpos w ->
    (Z.testbit (zeros a) i && Z.testbit (ones a) i) = false).
  { intros i Hi. apply (f_equal (fun z => Z.testbit z i)) in Hempty.
    rewrite tnum_and_bit, Z.bits_0 in Hempty by exact Hi. exact Hempty. }
  split; apply tnum_gamma_bits; split; intros i Hi Hbit;
    unfold tnum_min, tnum_max;
    rewrite ?tnum_wrap_bit, ?tnum_not_bit by exact Hi;
    specialize (Hdisjoint i Hi);
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i);
    cbn in *; congruence.
Qed.

(** * Saturating scalar amounts *)

Definition tnum_shift_op (o : op) : Prop :=
  o = bvshl \/ o = bvlshr \/ o = bvashr \/ o = bvrotl \/ o = bvrotr.

Definition tnum_scalar_value (o : op) (w : width) (k x : Z) : Z :=
  match o with
  | bvshl => wshl w x (Z.min k (Zpos w))
  | bvlshr => wlshr w x (Z.min k (Zpos w))
  | bvashr => washr w x (Z.min k (Zpos w))
  | bvrotl => wrotl w x (k mod Zpos w)
  | bvrotr => wrotl w x ((-k) mod Zpos w)
  | _ => wrap w x
  end.

Definition tnum_source (o : op) (w : width) (k i : Z) : option Z :=
  match o with
  | bvshl => if k <=? i then Some (i - k) else None
  | bvlshr => if i + k <? Zpos w then Some (i + k) else None
  | bvashr => Some (Z.min (i + k) (Zpos w - 1))
  | bvrotl => Some ((i - k) mod Zpos w)
  | bvrotr => Some ((i + k) mod Zpos w)
  | _ => Some i
  end.

Lemma tnum_scalar_word : forall o w k x,
  is_word w (tnum_scalar_value o w k x).
Proof.
  intros o w k x. destruct o; cbn [tnum_scalar_value];
    first [apply wrap_is_word|apply wshl_is_word|apply wlshr_is_word|
      apply washr_is_word|unfold wrotl; apply wrap_is_word].
Qed.

Lemma tnum_scalar_bits : forall o w k x i,
  0 <= k -> is_word w x -> 0 <= i < Zpos w ->
  Z.testbit (tnum_scalar_value o w k x) i =
    match tnum_source o w k i with
    | Some j => Z.testbit x j
    | None => false
    end.
Proof.
  intros o w k x i Hk Hx Hi.
  assert (Hsat : is_word w (Z.min k (Zpos w))) by (apply count_is_word; lia).
  assert (Hres : forall n, is_word w (n mod Zpos w)).
  { intro n. apply small_amount_word. apply Z.mod_pos_bound. lia. }
  assert (Hlow : (i <? Zpos w) = true) by (apply Z.ltb_lt; lia).
  destruct o; cbn [tnum_scalar_value tnum_source];
    try (rewrite (wrap_id w x Hx); reflexivity).
  - rewrite testbit_wshl, Hlow by (try assumption; lia). cbn [andb].
    destruct (k <=? i) eqn:Hki.
    + apply Z.leb_le in Hki. rewrite Z.min_l by lia.
      now rewrite (proj2 (Z.leb_le k i) Hki).
    + apply Z.leb_gt in Hki. rewrite (proj2 (Z.leb_gt (Z.min k (Zpos w)) i)) by lia.
      reflexivity.
  - rewrite testbit_wlshr, Hlow by (try assumption; lia). cbn [andb].
    destruct (i + k <? Zpos w) eqn:Hsmall.
    + apply Z.ltb_lt in Hsmall. now rewrite Z.min_l by lia.
    + apply Z.ltb_ge in Hsmall. apply (word_bits_high w x); [exact Hx|lia].
  - rewrite testbit_washr, Hlow by (try assumption; lia). cbn [andb].
    f_equal. lia.
  - rewrite testbit_wrotl by exact Hi.
    rewrite (wrap_id w _ (Hres k)), (wrap_id w x Hx).
    rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia. reflexivity.
  - rewrite testbit_wrotl by exact Hi.
    rewrite (wrap_id w _ (Hres (-k))), (wrap_id w x Hx).
    rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    replace (i - - k) with (i + k) by ring. reflexivity.
Qed.

Lemma tnum_source_range : forall o w k i j,
  0 <= k -> 0 <= i < Zpos w -> tnum_source o w k i = Some j ->
  0 <= j < Zpos w.
Proof.
  intros o w k i j Hk Hi Hsource.
  destruct o; cbn [tnum_source] in Hsource;
    try (inversion Hsource; lia).
  - destruct (k <=? i) eqn:Hki; [apply Z.leb_le in Hki|discriminate].
    inversion Hsource. lia.
  - destruct (i + k <? Zpos w) eqn:Hki; [apply Z.ltb_lt in Hki|discriminate].
    inversion Hsource. lia.
  - change (Some (Z.min (i + k) (Zpos w - 1)) = Some j) in Hsource.
    injection Hsource as <-. change (0 <= Z.min (i + k) (Zpos w - 1) < Zpos w).
    lia.
  - inversion Hsource. apply Z.mod_pos_bound. lia.
  - inversion Hsource. apply Z.mod_pos_bound. lia.
Qed.

Lemma tnum_scalar_copy : forall o w k, 0 <= k ->
  tnum_bit_copy w w (tnum_scalar_value o w k).
Proof.
  intros o w k Hk i Hi. destruct (tnum_source o w k i) as [j|] eqn:Hsource.
  - right. exists j. split; [eapply tnum_source_range; eassumption|].
    intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
  - left. intros x Hx. now rewrite tnum_scalar_bits, Hsource by assumption.
Qed.

Definition tnum_scalar (o : op) (w : width) (k : Z) (a : tnum) : tnum :=
  tnum_map w w (tnum_scalar_value o w k) a.

(** Every guarded scalar shift and rotation commutes with the mask-intersection join. *)
Lemma tnum_scalar_join : forall o w k a b, 0 <= k ->
  tnum_equiv w (tnum_scalar o w k (tnum_join w a b))
    (tnum_join w (tnum_scalar o w k a) (tnum_scalar o w k b)).
Proof.
  intros o w k a b Hk. apply tnum_map_join. now apply tnum_scalar_copy.
Qed.

Lemma tnum_scalar_sound : forall o w k a x,
  0 <= k -> is_word w x -> tnum_gamma w a x ->
  tnum_gamma w (tnum_scalar o w k a) (tnum_scalar_value o w k x).
Proof.
  intros o w k a x Hk Hx Ha. apply tnum_map_sound; try assumption.
  now apply tnum_scalar_copy.
Qed.

Lemma tnum_source_composition : forall o w h k i,
  0 <= h -> 0 <= k -> 0 <= i < Zpos w ->
  (match tnum_source o w k i with
   | Some j => tnum_source o w h j
   | None => None
   end) = tnum_source o w (h + k) i.
Proof.
  intros o w h k i Hh Hk Hi. destruct o; cbn [tnum_source]; try reflexivity.
  - destruct (k <=? i) eqn:Hki.
    + apply Z.leb_le in Hki. destruct (h <=? i - k) eqn:Hhi.
      * apply Z.leb_le in Hhi. rewrite (proj2 (Z.leb_le (h + k) i)) by lia.
        f_equal. lia.
      * apply Z.leb_gt in Hhi. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia.
        reflexivity.
    + apply Z.leb_gt in Hki. rewrite (proj2 (Z.leb_gt (h + k) i)) by lia.
      reflexivity.
  - destruct (i + k <? Zpos w) eqn:Hki.
    + apply Z.ltb_lt in Hki. destruct (i + k + h <? Zpos w) eqn:Hhi.
      * apply Z.ltb_lt in Hhi. rewrite (proj2 (Z.ltb_lt (i + (h + k)) (Zpos w)))
          by lia. f_equal. lia.
      * apply Z.ltb_ge in Hhi. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
          by lia. reflexivity.
    + apply Z.ltb_ge in Hki. rewrite (proj2 (Z.ltb_ge (i + (h + k)) (Zpos w)))
        by lia. reflexivity.
  - f_equal. lia.
  - rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    f_equal. f_equal. ring.
  - rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia.
    f_equal. f_equal. ring.
Qed.

Lemma tnum_scalar_value_composition : forall o w h k x,
  0 <= h -> 0 <= k -> is_word w x ->
  tnum_scalar_value o w k (tnum_scalar_value o w h x) =
    tnum_scalar_value o w (h + k) x.
Proof.
  intros o w h k x Hh Hk Hx. apply (word_ext w);
    [apply tnum_scalar_word|apply tnum_scalar_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite !tnum_scalar_bits by (try assumption; try apply tnum_scalar_word; lia).
    pose proof (tnum_source_composition o w h k i Hh Hk ltac:(lia)) as Hcomp.
    destruct (tnum_source o w k i) as [j|] eqn:Hsource.
    + rewrite tnum_scalar_bits by
        (try assumption; exact (tnum_source_range o w k i j Hk ltac:(lia) Hsource)).
      cbn in Hcomp. now rewrite <- Hcomp.
    + cbn in Hcomp. now rewrite <- Hcomp.
  - rewrite !(word_bits_high w) by (try apply tnum_scalar_word; lia). reflexivity.
Qed.

Lemma tnum_map_ext : forall sw rw f g a,
  (forall x, is_word sw x -> f x = g x) ->
  tnum_map sw rw f a = tnum_map sw rw g a.
Proof.
  intros sw rw f g a Hfg. unfold tnum_map.
  rewrite !Hfg by first [apply wnot_is_word|apply wrap_is_word]. reflexivity.
Qed.

(** Successive scalar transfers compose by ordinary addition before amount normalization. *)
Lemma tnum_scalar_composition : forall o w h k a,
  0 <= h -> 0 <= k ->
  tnum_equiv w (tnum_scalar o w k (tnum_scalar o w h a))
    (tnum_scalar o w (h + k) a).
Proof.
  intros o w h k a Hh Hk.
  pose proof (tnum_map_composition w w w (tnum_scalar_value o w h)
    (tnum_scalar_value o w k) a (tnum_scalar_copy o w k Hk)
    (fun x _ => tnum_scalar_word o w h x)) as Hcomp.
  unfold tnum_scalar. rewrite (tnum_map_ext w w
    (fun x => tnum_scalar_value o w k (tnum_scalar_value o w h x))
    (tnum_scalar_value o w (h + k)) a) in Hcomp.
  - exact Hcomp.
  - intros x Hx. now apply tnum_scalar_value_composition.
Qed.

Lemma tnum_equiv_leb : forall w a b c,
  tnum_equiv w a b ->
  (leb (tnum_lattice w) a c = true <-> leb (tnum_lattice w) b c = true).
Proof.
  intros w a b c Heq. pose proof (proj1 (tnum_equiv_bits w a b) Heq) as Hbits.
  clear Heq. rewrite !tnum_leb_bits.
  split; intros [Hz Ho]; split; intros i Hi Hbit;
    specialize (Hbits i Hi) as [Heqz Heqo];
    first [rewrite <- Heqz; now apply Hz|rewrite <- Heqo; now apply Ho|
      rewrite Heqz; now apply Hz|rewrite Heqo; now apply Ho].
Qed.

Lemma tnum_join_leb : forall w a b c,
  leb (tnum_lattice w) (tnum_join w a b) c = true <->
  leb (tnum_lattice w) a c = true /\ leb (tnum_lattice w) b c = true.
Proof.
  intros w a b c. split.
  - intro Hle. split; eapply (leb_trans (tnum_laws w)); try exact Hle.
    + apply (join_upper_l (tnum_laws w)).
    + apply (join_upper_r (tnum_laws w)).
  - intros [Ha Hb]. apply (join_least (tnum_lub w)); assumption.
Qed.

Lemma tnum_scalar_zero : forall o w a,
  tnum_equiv w (tnum_scalar o w 0 a) a.
Proof.
  intros o w a. apply tnum_equiv_bits. intros i Hi.
  assert (Hsource : tnum_source o w 0 i = Some i).
  { destruct o; cbn [tnum_source]; try reflexivity.
    - rewrite (proj2 (Z.leb_le 0 i)) by lia. now rewrite Z.sub_0_r.
    - rewrite Z.add_0_r, (proj2 (Z.ltb_lt i (Zpos w))) by lia. reflexivity.
    - change (Some (Z.min (i + 0) (Zpos w - 1)) = Some i). f_equal. lia.
    - rewrite Z.sub_0_r, Z.mod_small by exact Hi. reflexivity.
    - rewrite Z.add_0_r, Z.mod_small by exact Hi. reflexivity. }
  unfold tnum_scalar, tnum_map. cbn [zeros ones].
  rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
  rewrite !tnum_scalar_bits, Hsource by
    (try lia; try exact Hi; first [apply wnot_is_word|apply wrap_is_word]).
  unfold tnum_min, tnum_max. rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
  now rewrite negb_involutive.
Qed.

Definition tnum_rotation (o : op) : bool :=
  match o with
  | bvrotl | bvrotr => true
  | _ => false
  end.

Definition tnum_stride (o : op) (w : width) (d : Z) : Z :=
  if tnum_rotation o then (2 * d) mod Zpos w else 2 * d.

Lemma tnum_scalar_period : forall o w h k a,
  tnum_rotation o = true -> h mod Zpos w = k mod Zpos w ->
  tnum_scalar o w h a = tnum_scalar o w k a.
Proof.
  intros o w h k a Hrot Hmod. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate.
  - now rewrite Hmod.
  - assert (Hneg : (-h) mod Zpos w = (-k) mod Zpos w).
    { replace (-h) with (0 - h) by ring. replace (-k) with (0 - k) by ring.
      rewrite (Zminus_mod 0 h), (Zminus_mod 0 k) by lia. now rewrite Hmod. }
    now rewrite Hneg.
Qed.

Lemma tnum_stride_nonnegative : forall o w d,
  0 <= d -> 0 <= tnum_stride o w d.
Proof.
  intros o w d Hd. unfold tnum_stride. destruct (tnum_rotation o).
  - apply Z.mod_pos_bound. lia.
  - lia.
Qed.

Lemma tnum_stride_agrees : forall o w d c a,
  tnum_scalar o w (tnum_stride o w d * c) a = tnum_scalar o w (d * (2 * c)) a.
Proof.
  intros o w d c a. unfold tnum_stride. destruct (tnum_rotation o) eqn:Hrot.
  - apply tnum_scalar_period; [exact Hrot|].
    rewrite Zmult_mod, Z.mod_mod, <- Zmult_mod by lia. f_equal. ring.
  - f_equal. ring.
Qed.

(** The choices select each set bit of a nonnegative unknown-bit mask independently. *)
Fixpoint tnum_choices (p : positive) (c : Z) : Prop :=
  match p with
  | xH => c = 0 \/ c = 1
  | xO q => exists t, tnum_choices q t /\ c = 2 * t
  | xI q => exists t, tnum_choices q t /\ (c = 2 * t \/ c = 2 * t + 1)
  end.

Lemma tnum_choices_nonnegative : forall p c, tnum_choices p c -> 0 <= c.
Proof.
  intro p. induction p as [p IH|p IH|]; intros c Hchoice; cbn [tnum_choices] in Hchoice.
  - destruct Hchoice as [t [Ht [Hc|Hc]]]; subst c; specialize (IH t Ht); lia.
  - destruct Hchoice as [t [Ht ->]]. specialize (IH t Ht). lia.
  - destruct Hchoice as [Hc|Hc]; subst c; lia.
Qed.

(** Each stage joins the current result with its image under one additional unknown amount bit.
    Rotation strides are reduced after doubling, keeping their representation width-bounded. *)
Fixpoint tnum_expand (o : op) (w : width) (p : positive) (d : Z) (r : tnum) : tnum :=
  match p with
  | xH => tnum_join w r (tnum_scalar o w d r)
  | xO q => tnum_expand o w q (tnum_stride o w d) r
  | xI q => tnum_expand o w q (tnum_stride o w d)
      (tnum_join w r (tnum_scalar o w d r))
  end.

Lemma tnum_stride_offset_agrees : forall o w d c b a,
  tnum_scalar o w (b + tnum_stride o w d * c) a =
    tnum_scalar o w (b + d * (2 * c)) a.
Proof.
  intros o w d c b a. unfold tnum_stride. destruct (tnum_rotation o) eqn:Hrot.
  - apply tnum_scalar_period; [exact Hrot|].
    rewrite Zplus_mod, Zmult_mod, Z.mod_mod, <- Zmult_mod, <- Zplus_mod by lia.
    f_equal. ring.
  - f_equal. ring.
Qed.

Lemma tnum_scalar_stage_leb : forall o w d k r target,
  0 <= d -> 0 <= k ->
  (leb (tnum_lattice w) (tnum_scalar o w k
     (tnum_join w r (tnum_scalar o w d r))) target = true <->
   leb (tnum_lattice w) (tnum_scalar o w k r) target = true /\
   leb (tnum_lattice w) (tnum_scalar o w (d + k) r) target = true).
Proof.
  intros o w d k r target Hd Hk.
  rewrite (tnum_equiv_leb w _ _ target (tnum_scalar_join o w k _ _ Hk)).
  rewrite tnum_join_leb.
  rewrite (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w d k r Hd Hk)).
  reflexivity.
Qed.

(** Stage invariant: the accumulator is the exact join for all subsets of the processed bits. *)
Lemma tnum_expand_join : forall o w p d r target,
  0 <= d ->
  (leb (tnum_lattice w) (tnum_expand o w p d r) target = true <->
   forall c, tnum_choices p c ->
     leb (tnum_lattice w) (tnum_scalar o w (d * c) r) target = true).
Proof.
  intros o w p. induction p as [p IH|p IH|]; intros d r target Hd.
  - cbn [tnum_expand]. rewrite IH by (now apply tnum_stride_nonnegative).
    assert (Hstage : forall t, tnum_choices p t ->
      (leb (tnum_lattice w)
        (tnum_scalar o w (tnum_stride o w d * t)
          (tnum_join w r (tnum_scalar o w d r))) target = true <->
       leb (tnum_lattice w) (tnum_scalar o w (d * (2 * t)) r) target = true /\
       leb (tnum_lattice w) (tnum_scalar o w (d * (2 * t + 1)) r) target = true)).
    { intros t Ht. pose proof (tnum_choices_nonnegative p t Ht) as Ht0.
      rewrite tnum_scalar_stage_leb by
        (try assumption; pose proof (tnum_stride_nonnegative o w d Hd); nia).
      rewrite tnum_stride_agrees, tnum_stride_offset_agrees.
      replace (d + d * (2 * t)) with (d * (2 * t + 1)) by ring. reflexivity. }
    split.
    + intros H c [t [Ht [Hc|Hc]]]; subst c; specialize (H t Ht);
        apply (Hstage t Ht) in H; tauto.
    + intros H t Ht. apply (Hstage t Ht). split; apply H; exists t; auto.
  - cbn [tnum_expand]. rewrite IH by (now apply tnum_stride_nonnegative).
    split.
    + intros H c [t [Ht ->]]. rewrite <- tnum_stride_agrees. now apply H.
    + intros H t Ht. rewrite tnum_stride_agrees. apply H. exists t. auto.
  - cbn [tnum_expand]. rewrite tnum_join_leb. split.
    + intros [Hr Hshift] c [-> | ->].
      * replace (d * 0) with 0 by ring.
        apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
      * now replace (d * 1) with d by ring.
    + intro H. split.
      * apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
        replace 0 with (d * 0) by ring. apply H. now left.
      * replace d with (d * 1) by ring. apply H. now right.
Qed.

Lemma tnum_land_div2 : forall c u,
  Z.land c u = c <->
  Z.land (c / 2) (u / 2) = c / 2 /\
    (Z.testbit c 0 = true -> Z.testbit u 0 = true).
Proof.
  intros c u. split.
  - intro Hland. split.
    + apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.div2_bits by exact Hi.
      apply (f_equal (fun z => Z.testbit z (Z.succ i))) in Hland.
      now rewrite Z.land_spec in Hland.
    + apply (f_equal (fun z => Z.testbit z 0)) in Hland.
      rewrite Z.land_spec in Hland. destruct (Z.testbit c 0), (Z.testbit u 0);
        cbn in *; congruence.
  - intros [Htail Hlow]. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 0) as [->|Hnonzero].
    + destruct (Z.testbit c 0), (Z.testbit u 0); cbn in *; intuition discriminate.
    + apply (f_equal (fun z => Z.testbit z (i - 1))) in Htail.
      rewrite Z.land_spec, !Z.div2_bits in Htail by lia.
      replace (Z.succ (i - 1)) with i in Htail by lia. exact Htail.
Qed.

Lemma tnum_double_div2 : forall t,
  (2 * t) / 2 = t /\ (2 * t + 1) / 2 = t.
Proof.
  intro t. split.
  - replace (2 * t) with (t * 2) by ring. apply Z.div_mul. lia.
  - replace (2 * t + 1) with (1 + t * 2) by ring.
    rewrite Z.div_add by lia. cbn. ring.
Qed.

(** The structural selection relation is exactly the set of integer submasks. *)
Lemma tnum_choices_land : forall p c, tnum_choices p c <-> Z.land c (Zpos p) = c.
Proof.
  intro p. induction p as [p IH|p IH|]; intro c.
  - rewrite tnum_land_div2. rewrite (Pos2Z.inj_xI p).
    rewrite (proj2 (tnum_double_div2 (Zpos p))), Z.testbit_odd_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht [-> | ->]]]; rewrite ?(proj1 (tnum_double_div2 t)),
        ?(proj2 (tnum_double_div2 t)); split; try reflexivity; now apply IH.
    + intros [Htail _]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit. rewrite Z.div2_div in Hsplit.
      destruct (Z.odd c); cbn [Z.b2z] in Hsplit; [right|left]; lia.
  - rewrite tnum_land_div2. rewrite (Pos2Z.inj_xO p).
    rewrite (proj1 (tnum_double_div2 (Zpos p))), Z.testbit_even_0.
    cbn [tnum_choices]. split.
    + intros [t [Ht ->]]. rewrite (proj1 (tnum_double_div2 t)), Z.testbit_even_0.
      split; [now apply IH|discriminate].
    + intros [Htail Hlow]. apply IH in Htail. exists (c / 2). split; [exact Htail|].
      pose proof (Z.div2_odd c) as Hsplit.
      rewrite Z.div2_div, <- Z.bit0_odd in Hsplit.
      destruct (Z.testbit c 0); cbn [Z.b2z] in *;
        [specialize (Hlow eq_refl); discriminate|lia].
  - cbn [tnum_choices]. split.
    + intros [-> | ->]; reflexivity.
    + intro Hland. change (Z.land c (Z.ones 1) = c) in Hland.
      rewrite Z.land_ones in Hland by lia.
      pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hbounds.
      change (c mod 2 = c) in Hland. lia.
Qed.

Lemma tnum_submask_word : forall w u c,
  is_word w u -> Z.land c u = c -> is_word w c.
Proof.
  intros w u c Hu Hsub. apply word_of_bits. intros i Hi.
  apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, (word_bits_high w u i Hu Hi), andb_false_r in Hsub.
  now symmetry.
Qed.

Lemma tnum_mask_bit : forall w a i, 0 <= i < Zpos w ->
  Z.testbit (tnum_mask w a) i =
    negb (Z.testbit (zeros a) i || Z.testbit (ones a) i).
Proof.
  intros w a i Hi. unfold tnum_mask. now rewrite tnum_not_bit, tnum_or_bit by exact Hi.
Qed.

Lemma tnum_amount_disjoint : forall w a c,
  Z.land c (tnum_mask w a) = c -> Z.land (tnum_min w a) c = 0.
Proof.
  intros w a c Hsub. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - apply (f_equal (fun z => Z.testbit z i)) in Hsub.
    rewrite Z.land_spec, tnum_mask_bit in Hsub by lia.
    unfold tnum_min. rewrite tnum_wrap_bit by lia.
    destruct (Z.testbit c i), (Z.testbit (zeros a) i), (Z.testbit (ones a) i);
      cbn in *; congruence.
  - unfold tnum_min. rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)).
    reflexivity.
Qed.

(** Concrete amounts are precisely the known-one base plus an independently chosen submask. *)
Lemma tnum_amounts : forall w a k,
  tnum_empty w a = false ->
  (is_word w k /\ tnum_gamma w a k <->
   exists c, Z.land c (tnum_mask w a) = c /\ k = tnum_min w a + c).
Proof.
  intros w a k Hempty. split.
  - intros [Hk Ha]. exists (Z.land k (tnum_mask w a)). split.
    + rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
    + assert (Hdisjoint : Z.land (tnum_min w a) (Z.land k (tnum_mask w a)) = 0).
      { apply tnum_amount_disjoint. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. }
      rewrite Z.add_nocarry_lxor by exact Hdisjoint.
      apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
      apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec.
      destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
      * unfold tnum_min. rewrite tnum_wrap_bit, tnum_mask_bit by lia.
        specialize (Hz i ltac:(lia)). specialize (Ho i ltac:(lia)).
        destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i), (Z.testbit k i);
          cbn in *; intuition discriminate.
      * rewrite (word_bits_high w k i Hk ltac:(lia)). unfold tnum_min.
        rewrite (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)). reflexivity.
  - intros [c [Hsub ->]].
    pose proof (tnum_submask_word w _ c (wnot_is_word w _) Hsub) as Hc.
    rewrite Z.add_nocarry_lxor by (now apply tnum_amount_disjoint).
    split.
    + apply word_of_bits. intros i Hi. rewrite Z.lxor_spec.
      unfold tnum_min. rewrite (word_bits_high w _ i (wrap_is_word w _) Hi),
        (word_bits_high w c i Hc Hi). reflexivity.
    + pose proof (proj1 (tnum_endpoints_sound w a Hempty)) as Hbase.
      apply tnum_gamma_bits in Hbase. destruct Hbase as [Hz Ho].
      apply tnum_gamma_bits. split; intros i Hi Hbit;
        apply (f_equal (fun z => Z.testbit z i)) in Hsub;
        rewrite Z.land_spec, tnum_mask_bit in Hsub by exact Hi;
        rewrite Z.lxor_spec;
        unfold tnum_min; rewrite tnum_wrap_bit by exact Hi;
        specialize (Hz i Hi); unfold tnum_min in Hz;
        rewrite tnum_wrap_bit in Hz by exact Hi;
        destruct (Z.testbit c i), (Z.testbit (zeros a) i), (Z.testbit (ones a) i);
        cbn in *; intuition discriminate.
Qed.

Definition tnum_expand_mask (o : op) (w : width) (u : Z) (r : tnum) : tnum :=
  match u with
  | Zpos p => tnum_expand o w p 1 r
  | _ => tnum_normalise w r
  end.

Lemma tnum_expand_mask_join : forall o w u r target,
  0 <= u ->
  (leb (tnum_lattice w) (tnum_expand_mask o w u r) target = true <->
   forall c, Z.land c u = c ->
     leb (tnum_lattice w) (tnum_scalar o w c r) target = true).
Proof.
  intros o w [|p|p] r target Hu; [| |lia].
  - cbn [tnum_expand_mask].
    assert (Hnorm : tnum_equiv w (tnum_normalise w r) r).
    { unfold tnum_equiv, tnum_normalise. cbn [zeros ones]. now rewrite !wrap_wrap. }
    rewrite (tnum_equiv_leb w _ _ target Hnorm). split.
    + intros Hr c Hc. rewrite Z.land_0_r in Hc. subst c.
      apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)). exact Hr.
    + intro H. apply (tnum_equiv_leb w _ _ target (tnum_scalar_zero o w r)).
      apply H. reflexivity.
  - cbn [tnum_expand_mask]. rewrite tnum_expand_join by lia.
    setoid_rewrite tnum_choices_land. split; intros H c Hc;
      specialize (H c Hc).
    + replace (1 * c) with c in H by ring. exact H.
    + replace (1 * c) with c by ring. exact H.
Qed.

Lemma tnum_expand_base_join : forall o w u base a target,
  0 <= u -> 0 <= base ->
  (leb (tnum_lattice w)
     (tnum_expand_mask o w u (tnum_scalar o w base a)) target = true <->
   forall c, Z.land c u = c ->
     leb (tnum_lattice w) (tnum_scalar o w (base + c) a) target = true).
Proof.
  intros o w u base a target Hu Hb. rewrite tnum_expand_mask_join by exact Hu.
  split; intros H c Hc;
    assert (Hnonneg : 0 <= c) by
      (rewrite <- Hc; apply Z.land_nonneg; right; exact Hu);
    specialize (H c Hc);
    apply (tnum_equiv_leb w _ _ target (tnum_scalar_composition o w base c a Hb Hnonneg));
    exact H.
Qed.

Lemma tnum_submask_bound : forall w u c,
  is_word w u -> Z.land c u = c -> 0 <= c <= u.
Proof.
  intros w u c Hu Hsub. pose proof (tnum_submask_word w u c Hu Hsub) as Hc.
  split; [exact (proj1 Hc)|]. apply (tnum_bitwise_le w); try assumption.
  intros i Hi Hbit. apply (f_equal (fun z => Z.testbit z i)) in Hsub.
  rewrite Z.land_spec, Hbit in Hsub. cbn in Hsub. now symmetry.
Qed.

Lemma tnum_submask_trans : forall c u v,
  Z.land c u = c -> Z.land u v = u -> Z.land c v = c.
Proof.
  intros c u v Hcu Huv. rewrite <- Hcu at 1.
  now rewrite <- Z.land_assoc, Huv.
Qed.

Lemma tnum_submask_low : forall u n, 0 <= n -> Z.land (u mod 2 ^ n) u = u mod 2 ^ n.
Proof.
  intros u n Hn. rewrite <- Z.land_ones by exact Hn.
  rewrite (Z.land_comm u (Z.ones n)), <- Z.land_assoc, Z.land_diag, Z.land_comm.
  reflexivity.
Qed.

Lemma tnum_submask_mod : forall c u n,
  0 <= n -> Z.land c u = c ->
  Z.land (c mod 2 ^ n) (u mod 2 ^ n) = c mod 2 ^ n.
Proof.
  intros c u n Hn Hsub. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_ge_dec i n) as [Hlow|Hhigh].
  - rewrite !Z.mod_pow2_bits_low by exact Hlow.
    apply (f_equal (fun z => Z.testbit z i)) in Hsub. now rewrite Z.land_spec in Hsub.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma tnum_scalar_oversized : forall o w k a,
  tnum_rotation o = false -> Zpos w <= k ->
  tnum_scalar o w k a = tnum_scalar o w (Zpos w) a.
Proof.
  intros o w k a Hrot Hk. unfold tnum_scalar, tnum_scalar_value.
  destruct o; cbn [tnum_rotation] in Hrot; try discriminate; try reflexivity;
    rewrite !Z.min_r by lia; reflexivity.
Qed.

Definition tnum_shift_cutoff (w : width) : Z := tnum_bitlen (Zpos w - 1).

Lemma tnum_shift_cutoff_bound : forall w,
  0 <= tnum_shift_cutoff w /\ Zpos w <= 2 ^ tnum_shift_cutoff w.
Proof.
  intro w. unfold tnum_shift_cutoff.
  pose proof (tnum_bitlen_bound (Zpos w - 1) ltac:(lia)). lia.
Qed.

Definition tnum_variable_raw (o : op) (w : width) (a b : tnum) : tnum :=
  let base := tnum_min w b in
  let u := tnum_mask w b in
  let r := tnum_scalar o w base a in
  if tnum_rotation o then tnum_expand_mask o w u r
  else
    let cutoff := 2 ^ tnum_shift_cutoff w in
    let low := tnum_expand_mask o w (u mod cutoff) r in
    if u <? cutoff then low else tnum_join w low (tnum_scalar o w (Zpos w) a).

(** The factored algorithm computes precisely the join of all independently allowed amounts. *)
Lemma tnum_variable_raw_join : forall o w a b target,
  (leb (tnum_lattice w) (tnum_variable_raw o w a b) target = true <->
   forall c, Z.land c (tnum_mask w b) = c ->
     leb (tnum_lattice w) (tnum_scalar o w (tnum_min w b + c) a) target = true).
Proof.
  intros o w a b target. unfold tnum_variable_raw.
  pose proof (wrap_is_word w (ones b)) as Hb.
  pose proof (wnot_is_word w (wor w (zeros b) (ones b))) as Hu.
  change (is_word w (tnum_min w b)) in Hb.
  change (is_word w (tnum_mask w b)) in Hu.
  destruct (tnum_rotation o) eqn:Hrot.
  - apply tnum_expand_base_join; exact (proj1 Hu) || exact (proj1 Hb).
  - pose proof (tnum_shift_cutoff_bound w) as [Hcut Hwidth].
    assert (Hpow : 0 < 2 ^ tnum_shift_cutoff w) by
      (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound (tnum_mask w b) (2 ^ tnum_shift_cutoff w) Hpow)
      as Hlow.
    destruct (tnum_mask w b <? 2 ^ tnum_shift_cutoff w) eqn:Hhigh.
    + apply Z.ltb_lt in Hhigh. rewrite Z.mod_small by (unfold is_word in Hu; lia).
      apply tnum_expand_base_join; exact (proj1 Hu) || exact (proj1 Hb).
    + apply Z.ltb_ge in Hhigh. rewrite tnum_join_leb.
      rewrite tnum_expand_base_join by (unfold is_word in *; lia).
      split.
      * intros [Hsmall Hbig] c Hc.
        pose proof (tnum_submask_bound w _ c Hu Hc) as Hcbound.
        destruct (c <? 2 ^ tnum_shift_cutoff w) eqn:Hcsmall.
        -- apply Z.ltb_lt in Hcsmall. apply Hsmall.
           pose proof (tnum_submask_mod c (tnum_mask w b) (tnum_shift_cutoff w)
             Hcut Hc) as Hmod.
           now rewrite Z.mod_small in Hmod by lia.
        -- apply Z.ltb_ge in Hcsmall.
           rewrite tnum_scalar_oversized by (try exact Hrot; unfold is_word in Hb; lia).
           exact Hbig.
      * intro H. split.
        -- intros c Hc. apply H. eapply tnum_submask_trans; [exact Hc|].
           apply tnum_submask_low. exact Hcut.
        -- specialize (H (tnum_mask w b) (Z.land_diag _)).
           rewrite tnum_scalar_oversized in H by
             (try exact Hrot; unfold is_word in Hb; lia). exact H.
Qed.

Definition tnum_variable (o : op) (w : width) (a b : tnum) : tnum :=
  if tnum_empty w a || tnum_empty w b then bot (tnum_lattice w)
  else tnum_variable_raw o w a b.

Lemma tnum_rotr_bits : forall w x k i,
  is_word w x -> is_word w k -> 0 <= i < Zpos w ->
  Z.testbit (wrotr w x k) i = Z.testbit x ((i + k) mod Zpos w).
Proof.
  intros w x k i Hx Hk Hi. unfold wrotr. rewrite (wrap_id w k Hk).
  rewrite testbit_wrotl by exact Hi.
  assert (Hamount : is_word w (Zpos w - k mod Zpos w)).
  { pose proof (Z.mod_pos_bound k (Zpos w) ltac:(lia)). apply count_is_word. lia. }
  rewrite (wrap_id w _ Hamount), (wrap_id w x Hx).
  f_equal.
  replace (i - (Zpos w - k mod Zpos w)) with (i + k mod Zpos w + (-1) * Zpos w)
    by ring.
  rewrite Z.mod_add, Zplus_mod, Z.mod_mod, <- Zplus_mod by lia. reflexivity.
Qed.

Lemma tnum_scalar_agrees : forall o w f k x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_scalar_value o w k x = f w x k.
Proof.
  intros o w f k x Ho Hf Hk Hx.
  assert (Hk0 : 0 <= k) by exact (proj1 Hk).
  apply (word_ext w); [apply tnum_scalar_word|now apply (word_fun2_is_word o f)|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite tnum_scalar_bits by (try assumption; lia).
    destruct Ho as [-> | [-> | [-> | [-> | ->]]]]; inversion Hf; subst f;
      cbn [tnum_source].
    + rewrite testbit_wshl by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia.
      destruct (k <=? i); reflexivity.
    + rewrite testbit_wlshr by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia. cbn [andb].
      destruct (i + k <? Zpos w) eqn:Hsmall; [reflexivity|].
      symmetry. apply (word_bits_high w x); [exact Hx|now apply Z.ltb_ge in Hsmall].
    + rewrite testbit_washr by (try assumption; lia).
      rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia. reflexivity.
    + rewrite testbit_wrotl, (wrap_id w k Hk), (wrap_id w x Hx) by lia.
      reflexivity.
    + rewrite tnum_rotr_bits by (try assumption; lia). reflexivity.
  - rewrite (word_bits_high w _ i (tnum_scalar_word o w k x) ltac:(lia)).
    rewrite (word_bits_high w _ i (word_fun2_is_word o f w x k Hf) ltac:(lia)).
    reflexivity.
Qed.

(** The exact join ranges over concrete wrapped amount words, with contradictory inputs empty. *)
Lemma tnum_variable_join : forall o w a b target,
  tnum_empty w a = false -> tnum_empty w b = false ->
  (leb (tnum_lattice w) (tnum_variable o w a b) target = true <->
   forall k, is_word w k -> tnum_gamma w b k ->
     leb (tnum_lattice w) (tnum_scalar o w k a) target = true).
Proof.
  intros o w a b target Ha Hb. unfold tnum_variable. rewrite Ha, Hb.
  cbn [orb]. rewrite tnum_variable_raw_join. split.
  - intros H k Hk Hgamma. pose proof (conj Hk Hgamma) as Hamount.
    apply (tnum_amounts w b k Hb) in Hamount as [c [Hc ->]]. now apply H.
  - intros H c Hc. destruct (proj2 (tnum_amounts w b (tnum_min w b + c) Hb)
      (ex_intro _ c (conj Hc eq_refl))) as [Hword Hgamma].
    now apply H.
Qed.

Lemma tnum_variable_sound : forall o w f a b x k,
  tnum_shift_op o -> word_fun2 o = Some f ->
  is_word w x -> is_word w k -> tnum_gamma w a x -> tnum_gamma w b k ->
  tnum_gamma w (tnum_variable o w a b) (f w x k).
Proof.
  intros o w f a b x k Ho Hf Hx Hk Ha Hb.
  pose proof (tnum_empty_sound w a x Ha) as Hae.
  pose proof (tnum_empty_sound w b k Hb) as Hbe.
  pose proof (proj1 (tnum_variable_join o w a b (tnum_variable o w a b) Hae Hbe)
    (leb_refl (tnum_laws w) _) k Hk Hb) as Hle.
  apply (tnum_gamma_monotone w _ _ _ Hle).
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx).
  apply tnum_scalar_sound; try assumption. exact (proj1 Hk).
Qed.

(** * Comparisons, counts and signed remainder *)

Definition tnum_order (strict : bool) (w : width) (a b : tnum) : tnum :=
  if (if strict then tnum_max w a <? tnum_min w b
      else tnum_max w a <=? tnum_min w b) then tnum_const 1%positive 1
  else if (if strict then tnum_max w b <=? tnum_min w a
           else tnum_max w b <? tnum_min w a) then tnum_const 1%positive 0
  else tnum_top.

Lemma tnum_order_sound : forall strict w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_order strict w a b)
    (if (if strict then x <? y else x <=? y) then 1 else 0).
Proof.
  intros strict w a b x y Hx Hy Ha Hb.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hax.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hby.
  unfold tnum_order. destruct strict.
  - destruct (tnum_max w a <? tnum_min w b) eqn:Htrue.
    + apply Z.ltb_lt in Htrue. rewrite (proj2 (Z.ltb_lt x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <=? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.leb_le in Hfalse. rewrite (proj2 (Z.ltb_ge x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_max w a <=? tnum_min w b) eqn:Htrue.
    + apply Z.leb_le in Htrue. rewrite (proj2 (Z.leb_le x y)) by lia.
      exact (tnum_const_sound 1%positive 1).
    + destruct (tnum_max w b <? tnum_min w a) eqn:Hfalse; [|apply tnum_top_sound].
      apply Z.ltb_lt in Hfalse. rewrite (proj2 (Z.leb_gt x y)) by lia.
      exact (tnum_const_sound 1%positive 0).
Qed.

Definition tnum_equal (w : width) (a b : tnum) : tnum :=
  if tnum_empty w (tnum_meet w a b) then tnum_const 1%positive 0
  else
    match tnum_constant w a, tnum_constant w b with
    | Some x, Some y => tnum_const 1%positive (if x =? y then 1 else 0)
    | _, _ => tnum_top
    end.

Lemma tnum_equal_sound : forall w a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_equal w a b) (if x =? y then 1 else 0).
Proof.
  intros w a b x y Hx Hy Ha Hb. unfold tnum_equal.
  destruct (tnum_empty w (tnum_meet w a b)) eqn:Hempty.
  - destruct (x =? y) eqn:Hxy.
    + apply Z.eqb_eq in Hxy. subst y.
      pose proof (tnum_empty_sound w _ x (tnum_meet_sound w a b x Ha Hb)). congruence.
    + exact (tnum_const_sound 1%positive 0).
  - destruct (tnum_constant w a) as [ca|] eqn:Hca,
      (tnum_constant w b) as [cb|] eqn:Hcb; try apply tnum_top_sound.
    rewrite (tnum_constant_value w a x ca Hx Ha Hca),
      (tnum_constant_value w b y cb Hy Hb Hcb).
    destruct (ca =? cb); apply tnum_const_sound.
Qed.

Definition tnum_bias (w : width) (a : tnum) : tnum :=
  tnum_xor w a (tnum_const w (half w)).

Lemma tnum_bias_sound : forall w a x,
  tnum_gamma w a x -> tnum_gamma w (tnum_bias w a) (wxor w x (half w)).
Proof.
  intros w a x Ha. unfold tnum_bias. apply tnum_xor_sound; [exact Ha|].
  rewrite <- (wrap_id w (half w)) at 2 by
    (unfold is_word; pose proof (half_pos w); pose proof (modulus_half w); lia).
  apply tnum_const_sound.
Qed.

Definition tnum_compare (o : op) (w : width) (a b : tnum) : tnum :=
  match o with
  | bveq => tnum_equal w a b
  | bvne => tnum_not 1%positive (tnum_equal w a b)
  | bvult => tnum_order true w a b
  | bvule => tnum_order false w a b
  | bvslt => tnum_order true w (tnum_bias w a) (tnum_bias w b)
  | bvsle => tnum_order false w (tnum_bias w a) (tnum_bias w b)
  | _ => tnum_top
  end.

Lemma tnum_compare_sound : forall o w f a b x y,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive (tnum_compare o w a b) (if f w x y then 1 else 0).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb. destruct o; cbn [word_cmp] in Hf;
    try discriminate; injection Hf as <-; cbn [tnum_compare].
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy). now apply tnum_equal_sound.
  - rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    pose proof (tnum_not_sound 1%positive (tnum_equal w a b)
      (if x =? y then 1 else 0) (tnum_equal_sound w a b x y Hx Hy Ha Hb)) as Hnot.
    destruct (x =? y); exact Hnot.
  - unfold wult. rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound true w a b x y Hx Hy Ha Hb).
  - unfold wule. rewrite (wrap_id w x Hx), (wrap_id w y Hy).
    exact (tnum_order_sound false w a b x y Hx Hy Ha Hb).
  - rewrite wslt_bias. unfold wult. rewrite !wrap_id by apply wxor_is_word.
    apply (tnum_order_sound true w); try apply wxor_is_word; now apply tnum_bias_sound.
  - assert (Hbias : wsle w x y =
      (wxor w x (half w) <=? wxor w y (half w))).
    { unfold wsle. rewrite !wxor_half_value.
      destruct (signed w x <=? signed w y) eqn:Hxy;
        destruct (signed w x + half w <=? signed w y + half w) eqn:Hbias;
        try reflexivity; apply Z.leb_le in Hxy || apply Z.leb_gt in Hxy;
        apply Z.leb_le in Hbias || apply Z.leb_gt in Hbias; lia. }
    rewrite Hbias. apply (tnum_order_sound false w);
      try apply wxor_is_word; now apply tnum_bias_sound.
Qed.

Definition tnum_count (w : width) : tnum := tnum_upper w (Zpos w).

Lemma tnum_count_sound : forall o w f x,
  (o = bvclz \/ o = bvctz \/ o = bvpopcnt) -> word_fun1 o = Some f ->
  tnum_gamma w (tnum_count w) (f w x).
Proof.
  intros o w f x [-> | [-> | ->]] Hf; inversion Hf; subst f;
    apply tnum_upper_sound; first [apply wclz_range|apply tnum_ctz_range|apply wpopcnt_range].
Qed.

Definition tnum_srem (w : width) (a : tnum) : tnum :=
  Tnum (wand w (zeros a) (half w)) 0.

Lemma tnum_srem_sound : forall w a x y,
  is_word w x -> is_word w y -> tnum_gamma w a x ->
  tnum_gamma w (tnum_srem w a) (wsrem w x y).
Proof.
  intros w a x y Hx Hy Ha. apply tnum_gamma_bits in Ha. destruct Ha as [Hz Ho].
  apply tnum_gamma_bits. split; intros i Hi Hbit; cbn [tnum_srem zeros ones] in Hbit.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hclear Hsign].
    unfold half in Hsign.
    destruct (Z.eq_dec (Zpos w - 1) i) as [Heq|Hne];
      [subst i|rewrite Z.pow2_bits_false in Hsign by exact Hne; discriminate].
    assert (Hmsb : msb w x = false).
    { unfold msb. rewrite (wrap_id w x Hx). now apply Hz. }
    assert (Hhalf : x < half w).
    { rewrite msb_half, (wrap_id w x Hx) in Hmsb.
      apply negb_false_iff, Z.ltb_lt in Hmsb. exact Hmsb. }
    unfold wsrem. rewrite Hmsb. destruct (msb w y).
    + pose proof (tnum_urem_bound w x (wneg w y) Hx (wrap_is_word w _)) as Hbound.
      rewrite <- (Z.mod_small (wurem w x (wneg w y)) (half w) ltac:(lia)).
      apply Z.mod_pow2_bits_high. lia.
    + pose proof (tnum_urem_bound w x y Hx Hy) as Hbound.
      rewrite <- (Z.mod_small (wurem w x y) (half w) ltac:(lia)).
      apply Z.mod_pow2_bits_high. lia.
  - rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Lemma tnum_gamma_wrap : forall w a z,
  tnum_gamma w a (wrap w z) <-> tnum_gamma w a z.
Proof.
  intros w a z. rewrite !tnum_gamma_bits. split; intros [Hz Ho]; split;
    intros i Hi Hbit; specialize (Hz i Hi); specialize (Ho i Hi);
    rewrite ?tnum_wrap_bit in * by exact Hi; auto.
Qed.

Definition tnum_ite (w : width) (c a b : tnum) : tnum :=
  match tnum_constant 1%positive c with
  | Some k => tnum_normalise w (if k =? 1 then a else b)
  | None => tnum_join w a b
  end.

Lemma tnum_ite_sound : forall w c a b k x y,
  is_word 1%positive k -> tnum_gamma 1%positive c k ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_ite w c a b) (if k =? 1 then x else y).
Proof.
  intros w c a b k x y Hk Hc Ha Hb. unfold tnum_ite.
  destruct (tnum_constant 1%positive c) as [v|] eqn:Hconstant.
  - rewrite (tnum_constant_value 1%positive c k v Hk Hc Hconstant).
    apply tnum_normalise_sound. destruct (v =? 1); assumption.
  - apply tnum_join_sound. destruct (k =? 1); auto.
Qed.

Definition tnum_forward_raw (o : op) (wps : list (width * tnum)) (rw : width) : tnum :=
  match o, wps with
  | bvnot, [(_, a)] => tnum_not rw a
  | bvneg, [(_, a)] => tnum_sub rw (tnum_const rw 0) a
  | (bvclz | bvctz | bvpopcnt), [_] => tnum_count rw
  | bvadd, [(_, a); (_, b)] => tnum_add rw a b
  | bvsub, [(_, a); (_, b)] => tnum_sub rw a b
  | bvmul, [(_, a); (_, b)] => tnum_mul rw a b
  | bvudiv, [(_, a); (_, b)] => tnum_udiv rw a b
  | bvurem, [(_, a); _] => tnum_urem rw a
  | bvsrem, [(_, a); _] => tnum_srem rw a
  | bvand, [(_, a); (_, b)] => tnum_and rw a b
  | bvor, [(_, a); (_, b)] => tnum_or rw a b
  | bvxor, [(_, a); (_, b)] => tnum_xor rw a b
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(_, a); (_, b)] =>
    tnum_variable o rw a b
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
    tnum_compare o w a b
  | bvite, [(_, c); (_, a); (_, b)] => tnum_ite rw c a b
  | (bvzext _ | bvtrunc _), [(w, a)] => tnum_map w rw (wrap rw) a
  | bvsext _, [(w, a)] => tnum_map w rw (fun x => wrap rw (signed w x)) a
  | bvextract _ lo, [(w, a)] =>
    tnum_map w rw (fun x => wrap rw (x / 2 ^ Z.of_nat lo)) a
  | bvconcat, [(w, a); (v, b)] => tnum_concat w v a b
  | _, _ => tnum_top
  end.

Definition tnum_any_empty (wps : list (width * tnum)) : bool :=
  existsb (fun wp => tnum_empty (fst wp) (snd wp)) wps.

Definition tnum_forward (o : op) (wps : list (width * tnum)) (rw : width) : tnum :=
  if tnum_any_empty wps then bot (tnum_lattice rw) else tnum_forward_raw o wps rw.

Lemma tnum_forward_one_sound : forall o w a x rw z,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Hx Ha Heval. destruct o;
    try (exact (tnum_top_sound rw z)).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvnot w x wnot eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply tnum_not_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. change (tnum_gamma w
      (tnum_sub w (tnum_const w 0) a) (wneg w x)).
    change (wneg w x) with (wsub w 0 x).
    apply tnum_sub_sound; try assumption. exact (tnum_const_sound w 0).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvclz w x wclz eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. exact (tnum_count_sound bvclz w wclz x ltac:(tauto) eq_refl).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvctz w x wctz eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. exact (tnum_count_sound bvctz w wctz x ltac:(tauto) eq_refl).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvpopcnt w x wpopcnt eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z.
    exact (tnum_count_sound bvpopcnt w wpopcnt x ltac:(tauto) eq_refl).
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    inversion Heval; subst rw z. rewrite (wrap_id w x Hx).
    apply tnum_map_sound; try assumption. apply tnum_zext_copy. apply width_add_le.
  - change (Some ((w + extra)%positive,
      wrap (w + extra)%positive (signed w (wrap w x))) = Some (rw, z)) in Heval.
    inversion Heval; subst rw z. rewrite (wrap_id w x Hx).
    apply (tnum_map_sound w (w + extra)%positive
      (fun v => wrap (w + extra)%positive (signed w v)) a x); try assumption.
    apply tnum_sext_copy.
  - pose proof (eval_op_width _ _ _ Heval) as Hwidth.
    cbn [result_width map fst] in Hwidth. destruct (Pos.leb target w) eqn:Hle;
      [|discriminate]. inversion Hwidth; subst rw.
    unfold eval_op in Heval. cbn [result_width map fst] in Heval. rewrite Hle in Heval.
    change (Some (target, wrap target (wrap w x)) = Some (target, z)) in Heval.
    injection Heval as <-. rewrite (wrap_id w x Hx).
    apply tnum_map_sound; try assumption. apply tnum_trunc_copy. now apply Pos.leb_le.
  - pose proof (eval_op_width _ _ _ Heval) as Hwidth.
    cbn [result_width map fst] in Hwidth.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)) eqn:Hshape; [|discriminate].
    inversion Hwidth; subst rw.
    unfold eval_op in Heval. cbn [result_width map fst] in Heval. rewrite Hshape in Heval.
    apply andb_true_iff in Hshape as [Hlo Hhi].
    apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi.
    change (Some (Pos.of_nat (S (hi - lo)),
      wrap (Pos.of_nat (S (hi - lo))) (wrap w x / 2 ^ Z.of_nat lo)) =
      Some (Pos.of_nat (S (hi - lo)), z)) in Heval.
    injection Heval as <-. rewrite (wrap_id w x Hx).
    apply (tnum_map_sound w (Pos.of_nat (S (hi - lo)))
      (fun v => wrap (Pos.of_nat (S (hi - lo))) (v / 2 ^ Z.of_nat lo)) a x);
      try assumption. apply tnum_extract_copy; [lia|].
    rewrite <- positive_nat_Z, Nat2Pos.id by lia.
    rewrite <- (positive_nat_Z w). lia.
Qed.

Lemma tnum_binary_transfer_sound : forall o w f a b x y,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_forward_raw o [(w, a); (w, b)] w) (f w x y).
Proof.
  intros o w f a b x y Hf Hx Hy Ha Hb. destruct o; cbn [word_fun2] in Hf;
    try discriminate; injection Hf as <-; cbn [tnum_forward_raw];
    first [now apply tnum_add_sound|now apply tnum_sub_sound|now apply tnum_mul_sound|
      now apply tnum_udiv_sound|now apply tnum_urem_sound|apply tnum_top_sound|
      now apply tnum_srem_sound|now apply tnum_and_sound|now apply tnum_or_sound|
      now apply tnum_xor_sound|
      eapply tnum_variable_sound; try eassumption; try reflexivity;
        unfold tnum_shift_op; tauto].
Qed.

Lemma tnum_binary_same_width : forall o w v x y rw z,
  (word_fun2 o <> None \/ word_cmp o <> None) ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> w = v.
Proof.
  intros o w v x y rw z Ho Heval. pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  destruct o; cbn [word_fun2 word_cmp] in Ho; try tauto.
  all: cbn [result_width map fst] in Hwidth;
    destruct (Pos.eqb w v) eqn:Hwv; [now apply Pos.eqb_eq|discriminate].
Qed.

Lemma tnum_forward_fun2_sound : forall o w v f a b x y rw z,
  word_fun2 o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  assert (Hwv : w = v) by
    (eapply tnum_binary_same_width; [left; rewrite Hf; discriminate|exact Heval]).
  subst v. rewrite (eval_op_fun2 o w x y f Hf) in Heval.
  injection Heval as <- <-. now apply (tnum_binary_transfer_sound o w f).
Qed.

Lemma tnum_forward_cmp_sound : forall o w v f a b x y rw z,
  word_cmp o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v f a b x y rw z Hf Hx Hy Ha Hb Heval.
  assert (Hwv : w = v) by
    (eapply tnum_binary_same_width; [right; rewrite Hf; discriminate|exact Heval]).
  subst v. rewrite (eval_op_cmp o w x y f Hf) in Heval.
  injection Heval as <- <-.
  pose proof (tnum_compare_sound o w f a b x y Hf Hx Hy Ha Hb) as Hsound.
  destruct o; cbn [word_cmp] in Hf; try discriminate; exact Hsound.
Qed.

Lemma tnum_forward_two_sound : forall o w v a b x y rw z,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Hx Hy Ha Hb Heval.
  destruct o; try apply tnum_top_sound;
    try (eapply tnum_forward_fun2_sound; try eassumption; reflexivity);
    try (eapply tnum_forward_cmp_sound; try eassumption; reflexivity).
  change (Some ((w + v)%positive, wrap (w + v)%positive
    (wrap w x * modulus v + wrap v y)) = Some (rw, z)) in Heval.
  injection Heval as <- <-. rewrite (wrap_id w x Hx), (wrap_id v y Hy).
  apply tnum_gamma_wrap. now apply tnum_concat_sound.
Qed.

Lemma tnum_forward_three_sound : forall o w v u c a b k x y rw z,
  is_word w k -> is_word v x -> is_word u y ->
  tnum_gamma w c k -> tnum_gamma v a x -> tnum_gamma u b y ->
  eval_op o [(w, k); (v, x); (u, y)] = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o [(w, c); (v, a); (u, b)] rw) z.
Proof.
  intros o w v u c a b k x y rw z Hk Hx Hy Hc Ha Hb Heval.
  destruct o; try apply tnum_top_sound.
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  cbn [result_width map fst] in Hwidth.
  destruct (Pos.eqb w 1 && Pos.eqb v u) eqn:Hshape; [|discriminate].
  apply andb_true_iff in Hshape as [Hw Hvu]. apply Pos.eqb_eq in Hw, Hvu. subst w u.
  rewrite eval_op_ite in Heval. injection Heval as <- <-.
  rewrite (wrap_id 1%positive k Hk), (wrap_id v x Hx), (wrap_id v y Hy).
  now apply tnum_ite_sound.
Qed.

Lemma tnum_forward_raw_sound : forall o wps ys rw z,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw (tnum_forward_raw o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval.
  destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
  - destruct o; apply tnum_top_sound.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    exact (tnum_forward_one_sound o w a x rw z Hx Ha Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (tnum_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
    inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
    inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
    cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
    exact (tnum_forward_three_sound o w v u a b c x y t rw z Hx Hy Ht Ha Hb Hc Heval).
  - destruct o; apply tnum_top_sound.
Qed.

Lemma tnum_any_empty_sound : forall wps ys,
  Forall2 (payload_sound tnum_gamma) wps ys -> tnum_any_empty wps = false.
Proof.
  intros wps ys Hgamma. induction Hgamma as [|[w a] [v z] rest tail Hhead Htail IH].
  - reflexivity.
  - destruct Hhead as [Hwv [_ Ha]]. cbn in Hwv, Ha. subst v.
    change (tnum_empty w a || tnum_any_empty rest = false).
    rewrite (tnum_empty_sound w a z Ha), IH. reflexivity.
Qed.

Lemma tnum_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw (tnum_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval. unfold tnum_forward.
  rewrite (tnum_any_empty_sound wps ys Hgamma). now apply (tnum_forward_raw_sound o wps ys).
Qed.

(** * Pulling result bits back to operands *)

Definition tnum_project (sw rw : width) (g : Z -> Z) (q : tnum) : tnum :=
  Tnum (wrap sw (g (wrap rw (zeros q)))) (wrap sw (g (wrap rw (ones q)))).

Definition tnum_projects (sw rw : width) (f g : Z -> Z) : Prop :=
  forall i m, 0 <= i < Zpos sw -> is_word rw m -> Z.testbit (g m) i = true ->
    exists j, 0 <= j < Zpos rw /\ Z.testbit m j = true /\
      forall x, is_word sw x -> Z.testbit (f x) j = Z.testbit x i.

Lemma tnum_project_sound : forall sw rw f g q x,
  tnum_projects sw rw f g -> is_word sw x -> tnum_gamma rw q (f x) ->
  tnum_gamma sw (tnum_project sw rw g q) x.
Proof.
  intros sw rw f g q x Hproject Hx Hq. apply tnum_gamma_bits in Hq.
  destruct Hq as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_project zeros ones] in Hbit; rewrite tnum_wrap_bit in Hbit by exact Hi.
  - destruct (Hproject i _ Hi (wrap_is_word rw _) Hbit) as [j [Hj [Hm Hcopy]]].
    rewrite tnum_wrap_bit in Hm by exact Hj. rewrite <- Hcopy by exact Hx.
    now apply Hz.
  - destruct (Hproject i _ Hi (wrap_is_word rw _) Hbit) as [j [Hj [Hm Hcopy]]].
    rewrite tnum_wrap_bit in Hm by exact Hj. rewrite <- Hcopy by exact Hx.
    now apply Ho.
Qed.

Definition tnum_inverse_shift (o : op) : op :=
  match o with
  | bvshl => bvlshr
  | bvlshr | bvashr => bvshl
  | bvrotl => bvrotr
  | bvrotr => bvrotl
  | _ => o
  end.

Lemma tnum_inverse_source : forall o w k i j,
  tnum_shift_op o -> 0 <= k -> 0 <= i < Zpos w ->
  tnum_source (tnum_inverse_shift o) w k i = Some j ->
  tnum_source o w k j = Some i.
Proof.
  intros o w k i j Ho Hk Hi Hsource.
  destruct Ho as [-> | [-> | [-> | [-> | ->]]]];
    cbn [tnum_inverse_shift tnum_source] in Hsource |- *.
  - destruct (i + k <? Zpos w) eqn:Hsmall; [|discriminate].
    injection Hsource as <-. rewrite (proj2 (Z.leb_le k (i + k))) by lia.
    f_equal. lia.
  - destruct (k <=? i) eqn:Hsmall; [apply Z.leb_le in Hsmall|discriminate].
    injection Hsource as <-. rewrite (proj2 (Z.ltb_lt (i - k + k) (Zpos w))) by lia.
    f_equal. lia.
  - destruct (k <=? i) eqn:Hsmall; [apply Z.leb_le in Hsmall|discriminate].
    injection Hsource as <-. change (Some (Z.min (i - k + k) (Zpos w - 1)) = Some i).
    f_equal. lia.
  - injection Hsource as <-.
    rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
    replace (i + k - k) with i by ring. now rewrite Z.mod_small by exact Hi.
  - injection Hsource as <-.
    rewrite Zplus_mod, Z.mod_mod, <- Zplus_mod by lia.
    replace (i - k + k) with i by ring. now rewrite Z.mod_small by exact Hi.
Qed.

Lemma tnum_projects_shift : forall o w k,
  tnum_shift_op o -> 0 <= k ->
  tnum_projects w w (tnum_scalar_value o w k)
    (tnum_scalar_value (tnum_inverse_shift o) w k).
Proof.
  intros o w k Ho Hk i m Hi Hm Hbit.
  rewrite tnum_scalar_bits in Hbit by assumption.
  destruct (tnum_source (tnum_inverse_shift o) w k i) as [j|] eqn:Hsource;
    [|discriminate].
  exists j. pose proof (tnum_source_range _ w k i j Hk Hi Hsource) as Hj.
  split; [exact Hj|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_scalar_bits by assumption.
  now rewrite (tnum_inverse_source o w k i j Ho Hk Hi Hsource).
Qed.

Lemma tnum_projects_resize : forall sw rw,
  tnum_projects sw rw (wrap rw) (fun m => m).
Proof.
  intros sw rw i m Hi Hm Hbit.
  assert (Hlow : i < Zpos rw).
  { destruct (Z_lt_ge_dec i (Zpos rw)); [assumption|].
    rewrite (word_bits_high rw m i Hm ltac:(lia)) in Hbit. discriminate. }
  exists i. split; [lia|]. split; [exact Hbit|].
  intros x Hx. apply tnum_wrap_bit. lia.
Qed.

Lemma tnum_projects_sext_low : forall sw rw,
  tnum_projects sw rw (fun x => wrap rw (signed sw x)) (fun m => m).
Proof.
  intros sw rw i m Hi Hm Hbit.
  assert (Hlow : i < Zpos rw).
  { destruct (Z_lt_ge_dec i (Zpos rw)); [assumption|].
    rewrite (word_bits_high rw m i Hm ltac:(lia)) in Hbit. discriminate. }
  exists i. split; [lia|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_wrap_bit, signed_bits by (try assumption; lia).
  now rewrite (proj2 (Z.ltb_lt i (Zpos sw))) by lia.
Qed.

Lemma tnum_projects_extract : forall sw rw lo,
  0 <= lo ->
  tnum_projects sw rw (fun x => wrap rw (x / 2 ^ lo)) (fun m => Z.shiftl m lo).
Proof.
  intros sw rw lo Hlo i m Hi Hm Hbit.
  rewrite Z.shiftl_spec in Hbit by lia.
  assert (Hsource : 0 <= i - lo < Zpos rw).
  { split.
    - destruct (Z_le_gt_dec 0 (i - lo)); [assumption|].
      rewrite Z.testbit_neg_r in Hbit by lia. discriminate.
    - destruct (Z_lt_ge_dec (i - lo) (Zpos rw)); [assumption|].
      rewrite (word_bits_high rw m (i - lo) Hm ltac:(lia)) in Hbit. discriminate. }
  exists (i - lo). split; [exact Hsource|]. split; [exact Hbit|]. intros x Hx.
  rewrite tnum_wrap_bit, Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Definition tnum_and_back (w : width) (q b : tnum) : tnum :=
  Tnum (wand w (zeros q) (ones b)) (wrap w (ones q)).

Definition tnum_or_back (w : width) (q b : tnum) : tnum :=
  Tnum (wrap w (zeros q)) (wand w (ones q) (zeros b)).

Lemma tnum_and_back_sound : forall w q b x y,
  tnum_gamma w b y -> tnum_gamma w q (wand w x y) ->
  tnum_gamma w (tnum_and_back w q b) x.
Proof.
  intros w q b x y Hb Hq. apply tnum_gamma_bits in Hb, Hq.
  destruct Hb as [Hbz Hbo], Hq as [Hqz Hqo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_and_back zeros ones] in Hbit.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hq Hb].
    specialize (Hqz i Hi Hq). rewrite tnum_and_bit, (Hbo i Hi Hb), andb_true_r
      in Hqz by exact Hi. exact Hqz.
  - rewrite tnum_wrap_bit in Hbit by exact Hi. specialize (Hqo i Hi Hbit).
    rewrite tnum_and_bit in Hqo by exact Hi. apply andb_true_iff in Hqo. tauto.
Qed.

Lemma tnum_or_back_sound : forall w q b x y,
  tnum_gamma w b y -> tnum_gamma w q (wor w x y) ->
  tnum_gamma w (tnum_or_back w q b) x.
Proof.
  intros w q b x y Hb Hq. apply tnum_gamma_bits in Hb, Hq.
  destruct Hb as [Hbz Hbo], Hq as [Hqz Hqo]. apply tnum_gamma_bits.
  split; intros i Hi Hbit; cbn [tnum_or_back zeros ones] in Hbit.
  - rewrite tnum_wrap_bit in Hbit by exact Hi. specialize (Hqz i Hi Hbit).
    rewrite tnum_or_bit in Hqz by exact Hi. apply orb_false_iff in Hqz. tauto.
  - rewrite tnum_and_bit in Hbit by exact Hi. apply andb_true_iff in Hbit as [Hq Hb].
    specialize (Hqo i Hi Hq). rewrite tnum_or_bit, (Hbz i Hi Hb), orb_false_r
      in Hqo by exact Hi. exact Hqo.
Qed.

Lemma tnum_xor_back_sound : forall w q b x y,
  is_word w x -> tnum_gamma w b y -> tnum_gamma w q (wxor w x y) ->
  tnum_gamma w (tnum_xor w q b) x.
Proof.
  intros w q b x y Hx Hb Hq.
  pose proof (tnum_xor_sound w q b (wxor w x y) y Hq Hb) as Hback.
  rewrite <- wxor_assoc, wxor_self in Hback. unfold wxor in Hback.
  rewrite wrap_0, Z.lxor_0_r, (wrap_id w x Hx) in Hback. exact Hback.
Qed.

Lemma tnum_add_sub_cancel : forall w x y, is_word w x -> is_word w y ->
  wsub w (wadd w x y) y = x /\ wadd w (wsub w x y) y = x /\
  wsub w x (wsub w x y) = y.
Proof.
  intros w x y Hx Hy. unfold wsub, wadd.
  assert (Hsub : forall a b, is_word w b ->
    wrap w (wrap w a - b) = wrap w (a - b)).
  { intros a b Hb. rewrite (wrap_sub w a b), (wrap_id w b Hb). reflexivity. }
  assert (Hadd : forall a b, is_word w b ->
    wrap w (wrap w a + b) = wrap w (a + b)).
  { intros a b Hb. rewrite (wrap_add w a b), (wrap_id w b Hb). reflexivity. }
  split.
  - rewrite Hsub by exact Hy. replace (x + y - y) with x by ring. now apply wrap_id.
  - split.
    + rewrite Hadd by exact Hy. replace (x - y + y) with x by ring. now apply wrap_id.
    + transitivity (wrap w (x - (x - y))).
      * rewrite (wrap_sub w x (x - y)), (wrap_id w x Hx). reflexivity.
      * replace (x - (x - y)) with y by ring. now apply wrap_id.
Qed.

Lemma tnum_add_back_sound : forall w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w q (wadd w x y) ->
  tnum_gamma w (tnum_sub w q b) x /\ tnum_gamma w (tnum_sub w q a) y.
Proof.
  intros w q a b x y Hx Hy Ha Hb Hq. split.
  - rewrite <- (proj1 (tnum_add_sub_cancel w x y Hx Hy)).
    now apply tnum_sub_sound.
  - rewrite wadd_comm in Hq. rewrite <- (proj1 (tnum_add_sub_cancel w y x Hy Hx)).
    now apply tnum_sub_sound.
Qed.

Lemma tnum_sub_back_sound : forall w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w q (wsub w x y) ->
  tnum_gamma w (tnum_add w q b) x /\ tnum_gamma w (tnum_sub w a q) y.
Proof.
  intros w q a b x y Hx Hy Ha Hb Hq. split.
  - rewrite <- (proj1 (proj2 (tnum_add_sub_cancel w x y Hx Hy))).
    now apply tnum_add_sound.
  - rewrite <- (proj2 (proj2 (tnum_add_sub_cancel w x y Hx Hy))).
    apply tnum_sub_sound; [apply wrap_is_word|exact Ha|exact Hq].
Qed.

Lemma tnum_high_set_bit : forall rw m n,
  is_word rw m -> 0 <= n -> Z.shiftr m n <> 0 ->
  exists j, n <= j < Zpos rw /\ Z.testbit m j = true.
Proof.
  intros rw m n Hm Hn Hnonzero.
  assert (Hnonneg : 0 <= Z.shiftr m n) by (apply Z.shiftr_nonneg; exact (proj1 Hm)).
  pose proof (Z.bit_log2 (Z.shiftr m n) ltac:(lia)) as Hbit.
  pose proof (Z.log2_nonneg (Z.shiftr m n)) as Hlog.
  rewrite Z.shiftr_spec in Hbit by exact Hlog.
  exists (Z.log2 (Z.shiftr m n) + n). split; [|exact Hbit].
  split; [lia|]. destruct (Z_lt_ge_dec (Z.log2 (Z.shiftr m n) + n) (Zpos rw));
    [assumption|].
  rewrite (word_bits_high rw m (Z.log2 (Z.shiftr m n) + n) Hm ltac:(lia)) in Hbit.
  discriminate.
Qed.

Definition tnum_sign_project (sw rw : width) (n : Z) (q : tnum) : tnum :=
  Tnum (if Z.shiftr (wrap rw (zeros q)) n =? 0 then 0 else half sw)
    (if Z.shiftr (wrap rw (ones q)) n =? 0 then 0 else half sw).

Lemma tnum_sign_project_sound : forall sw rw n q x z,
  0 <= n -> tnum_gamma rw q z ->
  (forall j, n <= j < Zpos rw -> Z.testbit z j = Z.testbit x (Zpos sw - 1)) ->
  tnum_gamma sw (tnum_sign_project sw rw n q) x.
Proof.
  intros sw rw n q x z Hn Hq Hfill. apply tnum_gamma_bits in Hq.
  destruct Hq as [Hz Ho]. apply tnum_gamma_bits. split; intros i Hi Hbit;
    cbn [tnum_sign_project zeros ones] in Hbit.
  - destruct (Z.shiftr (wrap rw (zeros q)) n =? 0) eqn:Hnone;
      [rewrite Z.bits_0 in Hbit; discriminate|].
    apply Z.eqb_neq in Hnone.
    destruct (tnum_high_set_bit rw _ n (wrap_is_word rw _) Hn Hnone)
      as [j [Hj Hset]].
    unfold half in Hbit. destruct (Z.eq_dec (Zpos sw - 1) i) as [Heq|Hne];
      [subst i|rewrite Z.pow2_bits_false in Hbit by exact Hne; discriminate].
    rewrite <- (Hfill j Hj). apply Hz; [lia|].
    rewrite <- (tnum_wrap_bit rw (zeros q) j ltac:(lia)). exact Hset.
  - destruct (Z.shiftr (wrap rw (ones q)) n =? 0) eqn:Hnone;
      [rewrite Z.bits_0 in Hbit; discriminate|].
    apply Z.eqb_neq in Hnone.
    destruct (tnum_high_set_bit rw _ n (wrap_is_word rw _) Hn Hnone)
      as [j [Hj Hset]].
    unfold half in Hbit. destruct (Z.eq_dec (Zpos sw - 1) i) as [Heq|Hne];
      [subst i|rewrite Z.pow2_bits_false in Hbit by exact Hne; discriminate].
    rewrite <- (Hfill j Hj). apply Ho; [lia|].
    rewrite <- (tnum_wrap_bit rw (ones q) j ltac:(lia)). exact Hset.
Qed.

Definition tnum_back_shift (o : op) (w : width) (k : Z) (q : tnum) : tnum :=
  let copied := tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q in
  match o with
  | bvashr => tnum_meet w copied
      (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - k)) q)
  | _ => copied
  end.

Lemma tnum_back_shift_sound : forall o w f k q x,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w k -> is_word w x ->
  tnum_gamma w q (f w x k) -> tnum_gamma w (tnum_back_shift o w k q) x.
Proof.
  intros o w f k q x Ho Hf Hk Hx Hq.
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx) in Hq.
  assert (Hcopied : tnum_gamma w
    (tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q) x).
  { eapply tnum_project_sound; [apply tnum_projects_shift; [exact Ho|exact (proj1 Hk)]|
      exact Hx|exact Hq]. }
  unfold tnum_back_shift. destruct o; try exact Hcopied.
  apply tnum_meet_sound; [exact Hcopied|].
  apply (tnum_sign_project_sound w w (Z.max 0 (Zpos w - 1 - k)) q x
    (tnum_scalar_value bvashr w k x)); [lia|exact Hq|].
  intros j Hj. rewrite tnum_scalar_bits by (try assumption; unfold is_word in Hk; lia).
  change (Z.testbit x (Z.min (j + k) (Zpos w - 1)) = Z.testbit x (Zpos w - 1)).
  f_equal. lia.
Qed.

Definition tnum_back_sext (sw rw : width) (q : tnum) : tnum :=
  tnum_meet sw (tnum_project sw rw (fun m => m) q)
    (tnum_sign_project sw rw (Zpos sw - 1) q).

Lemma tnum_back_sext_sound : forall sw rw q x,
  is_word sw x -> tnum_gamma rw q (wrap rw (signed sw x)) ->
  tnum_gamma sw (tnum_back_sext sw rw q) x.
Proof.
  intros sw rw q x Hx Hq. apply tnum_meet_sound.
  - eapply tnum_project_sound; [apply tnum_projects_sext_low|exact Hx|exact Hq].
  - apply (tnum_sign_project_sound sw rw (Zpos sw - 1) q x
      (wrap rw (signed sw x))); [lia|exact Hq|].
    intros j Hj. rewrite tnum_wrap_bit, signed_bits by (try assumption; lia).
    destruct (j <? Zpos sw) eqn:Hlow.
    + apply Z.ltb_lt in Hlow. f_equal. lia.
    + unfold msb. now rewrite (wrap_id sw x Hx).
Qed.

Lemma tnum_boolean_sound : forall q (b : bool),
  tnum_gamma 1%positive q (if b then 1 else 0) ->
  (Z.testbit (ones q) 0 = true -> b = true) /\
  (Z.testbit (zeros q) 0 = true -> b = false).
Proof.
  intros q b Hq. apply tnum_gamma_bits in Hq. destruct Hq as [Hz Ho].
  split; intro Hbit; destruct b; try reflexivity.
  - specialize (Ho 0 ltac:(lia) Hbit). discriminate.
  - specialize (Hz 0 ltac:(lia) Hbit). discriminate.
Qed.

Definition tnum_lower (w : width) (l : Z) : tnum :=
  tnum_not w (tnum_upper w (wnot w l)).

Lemma tnum_lower_sound : forall w l x,
  is_word w x -> 0 <= l <= x -> tnum_gamma w (tnum_lower w l) x.
Proof.
  intros w l x Hx Hl. unfold tnum_lower.
  assert (Hlword : is_word w l) by (unfold is_word in *; lia).
  rewrite <- (wnot_involutive w x Hx). apply tnum_not_sound.
  apply tnum_upper_sound. unfold wnot.
  rewrite (wrap_id w x Hx), (wrap_id w l Hlword).
  unfold is_word in Hx. lia.
Qed.

Definition tnum_order_back (strict : bool) (w : width) (q a b : tnum) : tnum * tnum :=
  let d := if strict then 1 else 0 in
  if Z.testbit (ones q) 0 then
    (tnum_upper w (tnum_max w b - d), tnum_lower w (tnum_min w a + d))
  else if Z.testbit (zeros q) 0 then
    (tnum_lower w (tnum_min w b + (1 - d)), tnum_upper w (tnum_max w a - (1 - d)))
  else (tnum_top, tnum_top).

Lemma tnum_order_back_sound : forall (strict : bool) w q a b x y,
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive q (if (if strict then x <? y else x <=? y) then 1 else 0) ->
  tnum_gamma w (fst (tnum_order_back strict w q a b)) x /\
  tnum_gamma w (snd (tnum_order_back strict w q a b)) y.
Proof.
  intros strict w q a b x y Hx Hy Ha Hb Hq.
  pose proof (tnum_unsigned_bounds w a x Hx Ha) as Hax.
  pose proof (tnum_unsigned_bounds w b y Hy Hb) as Hby.
  pose proof (proj1 (wrap_is_word w (ones a))) as Hamin.
  pose proof (proj1 (wrap_is_word w (ones b))) as Hbmin.
  change (0 <= tnum_min w a) in Hamin. change (0 <= tnum_min w b) in Hbmin.
  destruct (tnum_boolean_sound q _ Hq) as [Htrue Hfalse]. unfold tnum_order_back.
  destruct (Z.testbit (ones q) 0) eqn:Hone.
  - specialize (Htrue eq_refl). destruct strict; cbn in Htrue |- *;
      [apply Z.ltb_lt in Htrue|apply Z.leb_le in Htrue]; split;
      first [apply tnum_upper_sound; unfold is_word in Hx; lia|
        apply tnum_lower_sound; [exact Hy|lia]].
  - destruct (Z.testbit (zeros q) 0) eqn:Hzero; [|split; apply tnum_top_sound].
    specialize (Hfalse eq_refl). destruct strict; cbn in Hfalse |- *;
      [apply Z.ltb_ge in Hfalse|apply Z.leb_gt in Hfalse]; split;
      first [apply tnum_lower_sound; [exact Hx|lia]|
        apply tnum_upper_sound; unfold is_word in Hy; lia].
Qed.

Definition tnum_project_variable (o : op) (w : width) (b q : tnum) : tnum :=
  let inv := tnum_inverse_shift o in
  Tnum (ones (tnum_variable_raw inv w (Tnum 0 (zeros q)) b))
    (ones (tnum_variable_raw inv w (Tnum 0 (ones q)) b)).

Lemma tnum_variable_raw_amount_bound : forall o w a b k,
  is_word w k -> tnum_gamma w b k ->
  leb (tnum_lattice w) (tnum_scalar o w k a) (tnum_variable_raw o w a b) = true.
Proof.
  intros o w a b k Hk Hb.
  pose proof (tnum_empty_sound w b k Hb) as Hempty.
  destruct (proj1 (tnum_amounts w b k Hempty) (conj Hk Hb)) as [c [Hc Hkc]].
  subst k. exact (proj1 (tnum_variable_raw_join o w a b (tnum_variable_raw o w a b))
    (leb_refl (tnum_laws w) _) c Hc).
Qed.

Lemma tnum_project_variable_sound : forall o w b q x k,
  tnum_shift_op o -> is_word w x -> is_word w k -> tnum_gamma w b k ->
  tnum_gamma w q (tnum_scalar_value o w k x) ->
  tnum_gamma w (tnum_project_variable o w b q) x.
Proof.
  intros o w b q x k Ho Hx Hk Hb Hq.
  apply (tnum_gamma_monotone w
    (tnum_project w w (tnum_scalar_value (tnum_inverse_shift o) w k) q)).
  - pose proof (tnum_variable_raw_amount_bound (tnum_inverse_shift o) w
      (Tnum 0 (zeros q)) b k Hk Hb) as Hz.
    pose proof (tnum_variable_raw_amount_bound (tnum_inverse_shift o) w
      (Tnum 0 (ones q)) b k Hk Hb) as Hone.
    apply tnum_leb_bits in Hz, Hone. destruct Hz as [_ Hz], Hone as [_ Hone].
    apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [tnum_project zeros ones]; rewrite tnum_wrap_bit by exact Hi.
    + specialize (Hz i Hi Hbit). unfold tnum_scalar, tnum_map, tnum_min in Hz.
      cbn [ones] in Hz. now rewrite tnum_wrap_bit in Hz by exact Hi.
    + specialize (Hone i Hi Hbit). unfold tnum_scalar, tnum_map, tnum_min in Hone.
      cbn [ones] in Hone. now rewrite tnum_wrap_bit in Hone by exact Hi.
  - eapply tnum_project_sound; [apply tnum_projects_shift; [exact Ho|exact (proj1 Hk)]|
      exact Hx|exact Hq].
Qed.

Definition tnum_back_variable_shift (o : op) (w : width) (b q : tnum) : tnum :=
  let copied := tnum_project_variable o w b q in
  match o with
  | bvashr => tnum_meet w copied
      (tnum_sign_project w w (Z.max 0 (Zpos w - 1 - tnum_min w b)) q)
  | _ => copied
  end.

Lemma tnum_back_variable_shift_sound : forall o w f b q x k,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w x -> is_word w k ->
  tnum_gamma w b k -> tnum_gamma w q (f w x k) ->
  tnum_gamma w (tnum_back_variable_shift o w b q) x.
Proof.
  intros o w f b q x k Ho Hf Hx Hk Hb Hq.
  rewrite <- (tnum_scalar_agrees o w f k x Ho Hf Hk Hx) in Hq.
  pose proof (tnum_project_variable_sound o w b q x k Ho Hx Hk Hb Hq) as Hcopied.
  unfold tnum_back_variable_shift. destruct o; try exact Hcopied.
  apply tnum_meet_sound; [exact Hcopied|].
  pose proof (tnum_unsigned_bounds w b k Hk Hb) as Hbounds.
  apply (tnum_sign_project_sound w w (Z.max 0 (Zpos w - 1 - tnum_min w b)) q x
    (tnum_scalar_value bvashr w k x)); [lia|exact Hq|].
  intros j Hj. rewrite tnum_scalar_bits by (try assumption; unfold is_word in Hk; lia).
  change (Z.testbit x (Z.min (j + k) (Zpos w - 1)) = Z.testbit x (Zpos w - 1)).
  f_equal. lia.
Qed.

Lemma tnum_concat_back_sound : forall w v q x y,
  is_word w x -> is_word v y ->
  tnum_gamma (w + v)%positive q (x * modulus v + y) ->
  tnum_gamma w (tnum_project w (w + v)%positive (fun m => Z.shiftr m (Zpos v)) q) x /\
  tnum_gamma v (tnum_project v (w + v)%positive (fun m => m) q) y.
Proof.
  intros w v q x y Hx Hy Hq. split.
  - apply (tnum_project_sound w (w + v)%positive
      (fun z => z * modulus v + y)); [|exact Hx|exact Hq].
    intros i m Hi Hm Hbit. rewrite Z.shiftr_spec in Hbit by lia.
    exists (i + Zpos v). split; [rewrite Pos2Z.inj_add; lia|]. split; [exact Hbit|].
    intros z Hz. unfold modulus. rewrite split_sum_bits by (try exact Hy; lia).
    rewrite (proj2 (Z.ltb_ge (i + Zpos v) (Zpos v))) by lia. f_equal. lia.
  - apply (tnum_project_sound v (w + v)%positive
      (fun z => x * modulus v + z)); [|exact Hy|exact Hq].
    intros i m Hi Hm Hbit. exists i. split; [rewrite Pos2Z.inj_add; lia|].
    split; [exact Hbit|]. intros z Hz. unfold modulus.
    rewrite split_sum_bits by (try exact Hz; lia).
    now rewrite (proj2 (Z.ltb_lt i (Zpos v))) by lia.
Qed.

Definition tnum_backward_raw (o : op) (wps : list (width * tnum))
    (rw : width) (q : tnum) : list tnum :=
  match o, wps with
  | bvnot, [(w, _)] => [tnum_not w q]
  | (bvzext _ | bvtrunc _), [(w, _)] => [tnum_project w rw (fun m => m) q]
  | bvsext _, [(w, _)] => [tnum_back_sext w rw q]
  | bvextract _ lo, [(w, _)] => [tnum_project w rw (fun m => Z.shiftl m (Z.of_nat lo)) q]
  | bvand, [(w, a); (v, b)] => [tnum_and_back w q b; tnum_and_back v q a]
  | bvor, [(w, a); (v, b)] => [tnum_or_back w q b; tnum_or_back v q a]
  | bvxor, [(w, a); (v, b)] => [tnum_xor w q b; tnum_xor v q a]
  | bvadd, [(w, a); (v, b)] => [tnum_sub w q b; tnum_sub v q a]
  | bvsub, [(w, a); (v, b)] => [tnum_add w q b; tnum_sub v a q]
  | (bvshl | bvlshr | bvashr | bvrotl | bvrotr), [(w, a); (v, b)] =>
    match tnum_constant v b with
    | Some k => [tnum_back_shift o w k q; b]
    | None => [tnum_back_variable_shift o w b q; b]
    end
  | bveq, [(_, a); (_, b)] => if Z.testbit (ones q) 0 then [b; a] else [a; b]
  | bvult, [(w, a); (_, b)] =>
    let p := tnum_order_back true w q a b in [fst p; snd p]
  | bvule, [(w, a); (_, b)] =>
    let p := tnum_order_back false w q a b in [fst p; snd p]
  | bvconcat, [(w, _); (v, _)] =>
    [tnum_project w rw (fun m => Z.shiftr m (Zpos v)) q;
     tnum_project v rw (fun m => m) q]
  | _, _ => map snd wps
  end.

Fixpoint tnum_refine (wps : list (width * tnum)) (qs : list tnum) : list tnum :=
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => tnum_meet w a q :: tnum_refine rest tail
  | (_, a) :: rest, [] => a :: tnum_refine rest []
  end.

Definition tnum_assume (o : op) (wps : list (width * tnum)) (rw : width) (q : tnum) :
    list tnum :=
  tnum_refine wps (tnum_backward_raw o wps rw q).

Lemma tnum_refine_refines : forall wps qs,
  Forall2 (fun wp q => leb (tnum_lattice (fst wp)) q (snd wp) = true)
    wps (tnum_refine wps qs).
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q tail]; cbn; constructor;
    first [apply (leb_refl (tnum_laws w))|apply tnum_meet_lower_left|apply IH].
Qed.

Lemma tnum_refine_sound : forall wps ys qs,
  Forall2 (payload_sound tnum_gamma) wps ys ->
  Forall2 (fun wp_y q => tnum_gamma (fst (fst wp_y)) q (snd (snd wp_y)))
    (combine wps ys) qs ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (tnum_refine wps qs)) ys.
Proof.
  intros wps ys qs Hgamma. revert qs.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - inversion Hqs as [|wp_y q rest' qs' Hq Hrest]; subst qs.
    destruct Hhead as [Hwv [Hx Ha]]. cbn in Hwv, Hx, Ha, Hq. subst v.
    cbn [tnum_refine combine map fst snd]. constructor.
    + now apply tnum_meet_sound.
    + now apply IH.
Qed.

Lemma tnum_backward_one_sound : forall o w a x rw z q,
  is_word w x -> tnum_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun p v => tnum_gamma w p v) (tnum_backward_raw o [(w, a)] rw q) [x].
Proof.
  intros o w a x rw z q Hx Ha Heval Hq. destruct o.
  all: cbn [tnum_backward_raw]; constructor; [|constructor].
  all: try exact Ha.
  - rewrite (eval_op_fun1 bvnot w x wnot eq_refl) in Heval. injection Heval as <- <-.
    rewrite <- (wnot_involutive w x Hx). now apply tnum_not_sound.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval. injection Heval as <- <-.
    rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - change (Some ((w + extra)%positive,
      wrap (w + extra)%positive (signed w (wrap w x))) = Some (rw, z)) in Heval.
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    now apply tnum_back_sext_sound.
  - unfold eval_op in Heval. cbn [result_width map fst] in Heval.
    destruct (Pos.leb target w); [|discriminate].
    change (Some (target, wrap target (wrap w x)) = Some (rw, z)) in Heval.
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_resize|exact Hx|exact Hq].
  - unfold eval_op in Heval. cbn [result_width map fst] in Heval.
    destruct (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w)); [|discriminate].
    change (Some (Pos.of_nat (S (hi - lo)),
      wrap (Pos.of_nat (S (hi - lo))) (wrap w x / 2 ^ Z.of_nat lo)) = Some (rw, z))
      in Heval.
    injection Heval as <- <-. rewrite (wrap_id w x Hx) in Hq.
    eapply tnum_project_sound; [apply tnum_projects_extract; lia|exact Hx|exact Hq].
Qed.

Lemma tnum_backward_shift_sound : forall o w f a b x y q,
  tnum_shift_op o -> word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Ho Hf Hx Hy Ha Hb Hq.
  assert (Hknown : forall k, tnum_constant w b = Some k ->
    tnum_gamma w (tnum_back_shift o w k q) x).
  { intros k Hconstant. pose proof (tnum_constant_value w b y k Hy Hb Hconstant) as Hyk.
    subst k. now apply (tnum_back_shift_sound o w f). }
  assert (Hvariable : tnum_gamma w (tnum_back_variable_shift o w b q) x).
  { now apply (tnum_back_variable_shift_sound o w f b q x y). }
  destruct Ho as [-> | [-> | [-> | [-> | ->]]]].
  all: cbn [tnum_backward_raw]; destruct (tnum_constant w b) as [k|] eqn:Hconstant.
  all: constructor; [first [now apply Hknown|exact Hvariable]|
    constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_fun2_sound : forall o w f a b x y q,
  word_fun2 o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y -> tnum_gamma w q (f w x y) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] w q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq. destruct o;
    cbn [word_fun2] in Hf; try discriminate; injection Hf as <-;
    try (change (Forall2 (fun p v => tnum_gamma w p v) [a; b] [x; y]);
      constructor; [exact Ha|constructor; [exact Hb|constructor]]);
    try solve [eapply tnum_backward_shift_sound; try eassumption; try reflexivity;
      unfold tnum_shift_op; tauto].
  - destruct (tnum_add_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hleft Hright].
    constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  - destruct (tnum_sub_back_sound w q a b x y Hx Hy Ha Hb Hq) as [Hleft Hright].
    constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  - cbn [tnum_backward_raw]. constructor; [now apply (tnum_and_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wand_comm in Hq.
    now apply (tnum_and_back_sound w q a y x).
  - cbn [tnum_backward_raw]. constructor; [now apply (tnum_or_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wor_comm in Hq.
    now apply (tnum_or_back_sound w q a y x).
  - cbn [tnum_backward_raw]. constructor; [now apply (tnum_xor_back_sound w q b x y)|].
    constructor; [|constructor]. rewrite wxor_comm in Hq.
    now apply (tnum_xor_back_sound w q a y x).
Qed.

Lemma tnum_backward_cmp_sound : forall o w f a b x y q,
  word_cmp o = Some f -> is_word w x -> is_word w y ->
  tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma 1%positive q (if f w x y then 1 else 0) ->
  Forall2 (fun p v => tnum_gamma w p v)
    (tnum_backward_raw o [(w, a); (w, b)] 1%positive q) [x; y].
Proof.
  intros o w f a b x y q Hf Hx Hy Ha Hb Hq.
  destruct o; cbn [word_cmp] in Hf; try discriminate; injection Hf as <-.
  - cbn [tnum_backward_raw]. destruct (Z.testbit (ones q) 0) eqn:Htrue.
    + apply tnum_boolean_sound in Hq. destruct Hq as [Hq _]. specialize (Hq Htrue).
      apply Z.eqb_eq in Hq. rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
      subst y. constructor; [exact Hb|constructor; [exact Ha|constructor]].
    + constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - unfold wult in Hq. rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound true w q a b x y Hx Hy Ha Hb Hq) as [Hleft Hright].
    constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  - unfold wule in Hq. rewrite (wrap_id w x Hx), (wrap_id w y Hy) in Hq.
    destruct (tnum_order_back_sound false w q a b x y Hx Hy Ha Hb Hq) as [Hleft Hright].
    constructor; [exact Hleft|constructor; [exact Hright|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
  - constructor; [exact Ha|constructor; [exact Hb|constructor]].
Qed.

Lemma tnum_backward_two_fun_sound : forall o w v f a b x y rw z q,
  word_fun2 o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine [(w, a); (v, b)] [(w, x); (v, y)])
    (tnum_backward_raw o [(w, a); (v, b)] rw q).
Proof.
  intros o w v f a b x y rw z q Hf Hx Hy Ha Hb Heval Hq.
  assert (Hwv : w = v) by
    (eapply tnum_binary_same_width; [left; rewrite Hf; discriminate|exact Heval]).
  subst v. rewrite (eval_op_fun2 o w x y f Hf) in Heval. injection Heval as <- <-.
  pose proof (tnum_backward_fun2_sound o w f a b x y q Hf Hx Hy Ha Hb Hq) as Hback.
  inversion Hback as [|p x' ps xs Hleft Htail]; subst.
  inversion Htail as [|p' y' ps' xs' Hright Hnil]; subst. inversion Hnil; subst.
  constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

Lemma tnum_backward_two_cmp_sound : forall o w v f a b x y rw z q,
  word_cmp o = Some f -> is_word w x -> is_word v y ->
  tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine [(w, a); (v, b)] [(w, x); (v, y)])
    (tnum_backward_raw o [(w, a); (v, b)] rw q).
Proof.
  intros o w v f a b x y rw z q Hf Hx Hy Ha Hb Heval Hq.
  assert (Hwv : w = v) by
    (eapply tnum_binary_same_width; [right; rewrite Hf; discriminate|exact Heval]).
  subst v. rewrite (eval_op_cmp o w x y f Hf) in Heval. injection Heval as <- <-.
  pose proof (tnum_backward_cmp_sound o w f a b x y q Hf Hx Hy Ha Hb Hq) as Hback.
  inversion Hback as [|p x' ps xs Hleft Htail]; subst.
  inversion Htail as [|p' y' ps' xs' Hright Hnil]; subst. inversion Hnil; subst.
  constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

Lemma tnum_backward_two_sound : forall o w v a b x y rw z q,
  is_word w x -> is_word v y -> tnum_gamma w a x -> tnum_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) -> tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine [(w, a); (v, b)] [(w, x); (v, y)])
    (tnum_backward_raw o [(w, a); (v, b)] rw q).
Proof.
  intros o w v a b x y rw z q Hx Hy Ha Hb Heval Hq. destruct o;
    try (change (Forall2
      (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
      [((w, a), (w, x)); ((v, b), (v, y))] [a; b]);
      constructor; [exact Ha|constructor; [exact Hb|constructor]]);
    try (eapply tnum_backward_two_fun_sound; try eassumption; reflexivity);
    try (eapply tnum_backward_two_cmp_sound; try eassumption; reflexivity).
  change (Some ((w + v)%positive, wrap (w + v)%positive
    (wrap w x * modulus v + wrap v y)) = Some (rw, z)) in Heval.
  injection Heval as <- <-. rewrite (wrap_id w x Hx), (wrap_id v y Hy) in Hq.
  apply (proj1 (tnum_gamma_wrap (w + v)%positive q (x * modulus v + y))) in Hq.
  destruct (tnum_concat_back_sound w v q x y Hx Hy Hq) as [Hleft Hright].
  constructor; [exact Hleft|constructor; [exact Hright|constructor]].
Qed.

Lemma tnum_backward_identity_sound : forall wps ys,
  Forall2 (payload_sound tnum_gamma) wps ys ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (map snd wps).
Proof.
  intros wps ys Hgamma.
  induction Hgamma as [|[w a] [v x] rest tail Hhead Htail IH]; cbn; constructor.
  - exact (proj2 (proj2 Hhead)).
  - exact IH.
Qed.

Lemma tnum_backward_raw_sound : forall o wps ys rw z q,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun wp_y p => tnum_gamma (fst (fst wp_y)) p (snd (snd wp_y)))
    (combine wps ys) (tnum_backward_raw o wps rw q).
Proof.
  intros o wps ys rw z q Hgamma Heval Hq.
  destruct wps as [|[w a] [|[v b] [|wp rest]]].
  - destruct o; constructor.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    pose proof (tnum_backward_one_sound o w a x rw z q Hx Ha Heval Hq) as Hback.
    inversion Hback as [|p x' ps xs Hleft Hnil]; subst. inversion Hnil; subst.
    constructor; [exact Hleft|constructor].
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (tnum_backward_two_sound o w v a b x y rw z q Hx Hy Ha Hb Heval Hq).
  - destruct o; now apply tnum_backward_identity_sound.
Qed.

Lemma tnum_assume_sound : forall o wps ys rw z q,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw q z ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (tnum_assume o wps rw q)) ys.
Proof.
  intros o wps ys rw z q Hgamma Heval Hq. apply tnum_refine_sound; [exact Hgamma|].
  now apply (tnum_backward_raw_sound o wps ys rw z q).
Qed.

(** Known bits use width-indexed masks and meet every backward refinement with its input. *)
Definition known_bits_domain : word_domain tnum :=
  {| plat := tnum_lattice;
     ptop _ := tnum_top;
     pconst := tnum_const;
     pforward := tnum_forward;
     passume := tnum_assume;
     pmeet := tnum_meet |}.

(** Every forward transfer and every backward refinement obeys the total word-domain contract. *)
Theorem known_bits_word_laws : word_laws known_bits_domain tnum_gamma.
Proof.
  constructor.
  - apply tnum_laws.
  - apply tnum_gamma_monotone.
  - apply tnum_gamma_bot_empty.
  - intros w z _. apply tnum_top_sound.
  - apply tnum_const_sound.
  - apply tnum_forward_sound.
  - apply tnum_assume_sound.
  - intros o wps rw q. apply tnum_refine_refines.
  - apply tnum_meet_sound.
  - apply tnum_meet_lower_left.
Qed.

(** The scalar result contains every known bit shared by all of its concrete outputs. *)
Lemma tnum_scalar_best : forall o w k a target,
  tnum_empty w a = false ->
  (forall x, is_word w x -> tnum_gamma w a x ->
    tnum_gamma w target (tnum_scalar_value o w k x)) ->
  leb (tnum_lattice w) (tnum_scalar o w k a) target = true.
Proof.
  intros o w k a target Hempty Hall.
  destruct (tnum_endpoints_sound w a Hempty) as [Hmin Hmax].
  pose proof (Hall _ (wrap_is_word w _) Hmin) as Hlow.
  pose proof (Hall _ (wnot_is_word w _) Hmax) as Hhigh.
  apply tnum_gamma_bits in Hlow, Hhigh. destruct Hlow as [_ Hlo], Hhigh as [Hhi _].
  apply tnum_leb_bits. split; intros i Hi Hbit; unfold tnum_scalar, tnum_map;
    cbn [zeros ones].
  - rewrite tnum_not_bit by exact Hi. apply negb_true_iff. exact (Hhi i Hi Hbit).
  - rewrite tnum_wrap_bit by exact Hi. now apply Hlo.
Qed.

(** Variable shifts and rotations return the best known-bit fact for all allowed results. *)
Lemma tnum_variable_best : forall o w f a b target,
  tnum_shift_op o -> word_fun2 o = Some f ->
  (forall x k, is_word w x -> is_word w k -> tnum_gamma w a x -> tnum_gamma w b k ->
    tnum_gamma w target (f w x k)) ->
  leb (tnum_lattice w) (tnum_variable o w a b) target = true.
Proof.
  intros o w f a b target Ho Hf Hall.
  destruct (tnum_empty w a) eqn:Ha, (tnum_empty w b) eqn:Hb.
  all: try (unfold tnum_variable; rewrite Ha, Hb; apply (bot_least (tnum_laws w))).
  apply (tnum_variable_join o w a b target Ha Hb). intros k Hk Hgamma.
  apply tnum_scalar_best; [exact Ha|]. intros x Hx Hax.
  rewrite (tnum_scalar_agrees o w f k x Ho Hf Hk Hx). now apply Hall.
Qed.

(** * Agreement with the closed arithmetic formulas *)

Lemma tnum_max_value_mask : forall w a,
  tnum_empty w a = false -> tnum_max w a = tnum_min w a + tnum_mask w a.
Proof.
  intros w a Hempty.
  rewrite Z.add_nocarry_lxor by (apply tnum_amount_disjoint; apply Z.land_diag).
  destruct (tnum_endpoints_sound w a Hempty) as [Hmin _].
  apply tnum_gamma_bits in Hmin. destruct Hmin as [Hz _].
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - unfold tnum_max, tnum_min. rewrite tnum_not_bit, tnum_wrap_bit, tnum_mask_bit by lia.
    specialize (Hz i ltac:(lia)). unfold tnum_min in Hz.
    rewrite tnum_wrap_bit in Hz by lia.
    destruct (Z.testbit (zeros a) i), (Z.testbit (ones a) i); cbn in *;
      intuition discriminate.
  - unfold tnum_max, tnum_min, tnum_mask.
    rewrite (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wrap_is_word w _) ltac:(lia)),
      (word_bits_high w _ i (wnot_is_word w _) ltac:(lia)). reflexivity.
Qed.

Definition tnum_linux_add (w : width) (a b : tnum) : tnum :=
  let v := tnum_min w a + tnum_min w b in
  let m := Z.lor (Z.lxor (v + (tnum_mask w a + tnum_mask w b)) v)
    (Z.lor (tnum_mask w a) (tnum_mask w b)) in
  Tnum (wrap w (Z.lnot (Z.lor v m))) (wrap w (Z.land v (Z.lnot m))).

(** The carry proof implements the Linux addition closed form on every consistent input. *)
Lemma tnum_add_linux_agrees : forall w a b,
  tnum_empty w a = false -> tnum_empty w b = false ->
  tnum_add w a b = tnum_linux_add w a b.
Proof.
  intros w a b Ha Hb. unfold tnum_add, tnum_adc, tnum_adc_uncertain, tnum_linux_add.
  cbn [Z.b2z]. rewrite !Z.add_0_r, (tnum_max_value_mask w a Ha),
    (tnum_max_value_mask w b Hb).
  replace (tnum_min w a + tnum_mask w a + (tnum_min w b + tnum_mask w b)) with
    (tnum_min w a + tnum_min w b + (tnum_mask w a + tnum_mask w b)) by ring.
  rewrite Z.lxor_comm. reflexivity.
Qed.

Definition tnum_linux_sub_uncertain (w : width) (a b : tnum) : Z :=
  let d := tnum_min w a - tnum_min w b in
  Z.lor (Z.lxor (d + tnum_mask w a) (d - tnum_mask w b))
    (Z.lor (tnum_mask w a) (tnum_mask w b)).

Definition tnum_linux_sub (w : width) (a b : tnum) : tnum :=
  let d := tnum_min w a - tnum_min w b in
  let m := tnum_linux_sub_uncertain w a b in
  Tnum (wrap w (Z.lnot (Z.lor d m))) (wrap w (Z.land d (Z.lnot m))).

Lemma tnum_not_mask : forall w a, tnum_mask w (tnum_not w a) = tnum_mask w a.
Proof.
  intros w a. apply (word_ext w); [apply wnot_is_word|apply wnot_is_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - rewrite !tnum_mask_bit by lia. cbn [tnum_not zeros ones].
    rewrite !tnum_wrap_bit by lia. now rewrite orb_comm.
  - rewrite !(word_bits_high w) by (try apply wnot_is_word; lia). reflexivity.
Qed.

Lemma tnum_sub_endpoints : forall w a b,
  tnum_empty w a = false -> tnum_empty w b = false ->
  tnum_min w a + tnum_min w (tnum_not w b) + 1 =
    tnum_min w a - tnum_min w b - tnum_mask w b + modulus w /\
  tnum_max w a + tnum_max w (tnum_not w b) + 1 =
    tnum_min w a - tnum_min w b + tnum_mask w a + modulus w.
Proof.
  intros w a b Ha Hb.
  assert (Hmin : tnum_min w (tnum_not w b) = modulus w - 1 - tnum_max w b).
  { unfold tnum_min, tnum_max, tnum_not. cbn [ones zeros]. rewrite wrap_wrap.
    unfold wnot. ring. }
  assert (Hmax : tnum_max w (tnum_not w b) = modulus w - 1 - tnum_min w b).
  { unfold tnum_min, tnum_max, tnum_not. cbn [ones zeros]. unfold wnot.
    now rewrite wrap_wrap. }
  rewrite Hmin, Hmax, (tnum_max_value_mask w a Ha), (tnum_max_value_mask w b Hb).
  split; ring.
Qed.

Lemma tnum_add_modulus_bit : forall w x i, 0 <= i < Zpos w ->
  Z.testbit (x + modulus w) i = Z.testbit x i.
Proof.
  intros w x i Hi. rewrite <- (tnum_wrap_bit w (x + modulus w) i Hi).
  replace (x + modulus w) with (x + 1 * modulus w) by ring.
  rewrite wrap_add_modulus. now apply tnum_wrap_bit.
Qed.

Lemma tnum_sub_uncertain_agrees : forall w a b i,
  tnum_empty w a = false -> tnum_empty w b = false -> 0 <= i < Zpos w ->
  Z.testbit (tnum_adc_uncertain w a (tnum_not w b) true) i =
    Z.testbit (tnum_linux_sub_uncertain w a b) i.
Proof.
  intros w a b i Ha Hb Hi.
  destruct (tnum_sub_endpoints w a b Ha Hb) as [Hlow Hhigh].
  unfold tnum_adc_uncertain. cbn [Z.b2z]. rewrite Hlow, Hhigh, tnum_not_mask.
  unfold tnum_linux_sub_uncertain. rewrite !Z.lor_spec, !Z.lxor_spec,
    !tnum_add_modulus_bit by exact Hi. now rewrite xorb_comm.
Qed.

Lemma tnum_sub_value_known : forall w a b i,
  tnum_empty w a = false -> tnum_empty w b = false -> 0 <= i < Zpos w ->
  Z.testbit (tnum_linux_sub_uncertain w a b) i = false ->
  Z.testbit (tnum_min w a - tnum_min w b) i =
    Z.testbit (tnum_min w a - tnum_min w b - tnum_mask w b) i.
Proof.
  intros w a b i Ha Hb Hi Hmask.
  destruct (tnum_endpoints_sound w a Ha) as [Hamin _].
  destruct (tnum_endpoints_sound w b Hb) as [Hbmin _].
  assert (Huncertain : Z.testbit (tnum_adc_uncertain w a (tnum_not w b) true) i = false).
  { now rewrite tnum_sub_uncertain_agrees by assumption. }
  pose proof (tnum_adc_known w a (tnum_not w b) (tnum_min w a)
    (wnot w (tnum_min w b)) true i Hamin
    (tnum_not_sound w b _ Hbmin) Hi Huncertain) as Hknown.
  cbn [Z.b2z] in Hknown.
  rewrite (proj1 (tnum_sub_endpoints w a b Ha Hb)) in Hknown.
  assert (Hvalue : tnum_min w a + wnot w (tnum_min w b) + 1 =
    tnum_min w a - tnum_min w b + modulus w).
  { unfold wnot. rewrite (wrap_id w (tnum_min w b)) by apply wrap_is_word. ring. }
  rewrite Hvalue, !tnum_add_modulus_bit in Hknown by exact Hi. exact Hknown.
Qed.

(** The endpoint carry formulation agrees bit for bit with Linux subtraction's alpha/beta masks. *)
Lemma tnum_sub_linux_agrees : forall w a b,
  tnum_empty w a = false -> tnum_empty w b = false ->
  tnum_sub w a b = tnum_linux_sub w a b.
Proof.
  intros w a b Ha Hb.
  assert (Hequiv : tnum_equiv w (tnum_sub w a b) (tnum_linux_sub w a b)).
  { apply tnum_equiv_bits. intros i Hi.
    pose proof (tnum_sub_uncertain_agrees w a b i Ha Hb Hi) as Hmask.
    pose proof (proj1 (tnum_sub_endpoints w a b Ha Hb)) as Hlow.
    unfold tnum_sub, tnum_adc, tnum_linux_sub. cbn [zeros ones Z.b2z].
    rewrite !tnum_wrap_bit, !Z.lnot_spec, !Z.lor_spec, !Z.land_spec by
      (try exact Hi; lia).
    rewrite !Z.lnot_spec by lia.
    rewrite !Hmask, !Hlow, !tnum_add_modulus_bit by exact Hi.
    destruct (Z.testbit (tnum_linux_sub_uncertain w a b) i) eqn:Hunknown.
    - cbn. rewrite ?orb_true_r, ?andb_false_r. auto.
    - rewrite (tnum_sub_value_known w a b i Ha Hb Hi Hunknown). auto. }
  destruct Hequiv as [Hz Ho].
  unfold tnum_sub, tnum_adc, tnum_linux_sub in Hz, Ho |- *.
  cbn [zeros ones] in Hz, Ho. rewrite !wrap_wrap in Hz, Ho.
  now rewrite Hz, Ho.
Qed.
