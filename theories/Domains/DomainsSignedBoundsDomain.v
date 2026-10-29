(** * A selectable signed bit-and-bounds domain

    Exact half reduction supports component joins, intersections and per-sign queries.
    For example, a negative alternative can retain different known bits from a positive one.
    Builds on: DomainsSignedBounds, DomainsNumeric, DomainsKnownBitsFast and DomainsWrapped. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit.
From Gaulois.Domains Require Import
  DomainsNumeric DomainsKnownBits DomainsKnownBitsFast DomainsInterval DomainsWrapped
  DomainsSignedBounds.
Import List.ListNotations.

Local Open Scope Z_scope.

Lemma sb_half_word_sign : forall w s h z,
  sb_half_gamma w s h z -> is_word w z /\ msb w z = s.
Proof.
  intros w s [|t lo hi] z Hz;
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma in Hz; tauto.
Qed.

Definition sb_order (w : width) (a b : sb_half) : bool :=
  match a, b with
  | SBEmpty, _ => true
  | _, SBEmpty => false
  | SBRange ta la ua, SBRange tb lb ub =>
    leb (tnum_lattice w) ta tb && (lb <=? la) && (ua <=? ub)
  end.

Definition sb_leb (w : width) (s : bool) (a b : sb_half) : bool :=
  sb_order w (sb_reduce_half w s a) (sb_reduce_half w s b).

Lemma sb_order_summary : forall w s S a b,
  sb_summary w S a ->
  (forall x, S x -> sb_half_gamma w s b x) -> sb_order w a b = true.
Proof.
  intros w s S [|ta la ua] [|tb lb ub] Ha Hsub; try reflexivity.
  - destruct Ha as [_ [Hlo _]]. specialize (Hsub la Hlo). destruct Hsub. contradiction.
  - destruct Ha as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    pose proof (Hsub la Hlo) as Hlower. pose proof (Hsub ua Hhi) as Hupper.
    apply sb_half_gamma_range in Hlower, Hupper.
    unfold sb_order. rewrite !andb_true_iff, !Z.leb_le. split; [split|]; try tauto.
    apply Hbest. intros x Hx. pose proof (Hsub x Hx) as Hout.
    apply sb_half_gamma_range in Hout. tauto.
Qed.

Lemma sb_order_sound : forall w s a b z,
  sb_order w a b = true -> sb_half_gamma w s a z -> sb_half_gamma w s b z.
Proof.
  intros w s [|ta la ua] [|tb lb ub] z Hle Hz;
    try discriminate; try (destruct Hz; contradiction).
  unfold sb_order in Hle. rewrite !andb_true_iff, !Z.leb_le in Hle.
  apply sb_half_gamma_range in Hz. apply sb_half_gamma_range.
  destruct Hle as [[Hbits Hlo] Hhi], Hz as [Hw [Hs [Ht Hb]]].
  split; [exact Hw|]. split; [exact Hs|]. split;
    [eapply tnum_gamma_monotone; eassumption|lia].
Qed.

Lemma sb_leb_spec : forall w s a b,
  sb_leb w s a b = true <->
  forall z, sb_half_gamma w s a z -> sb_half_gamma w s b z.
Proof.
  intros w s a b. split.
  - intros Hle z Hz. apply (proj1 (sb_reduce_half_gamma w s b z)).
    eapply sb_order_sound; [exact Hle|]. now apply sb_reduce_half_gamma.
  - intro Hsub. unfold sb_leb. eapply sb_order_summary; [apply sb_reduce_half_summary|].
    intros x Hx. apply sb_reduce_half_gamma. now apply Hsub.
Qed.

(** Component inclusion before normalization remains inclusion between exact reduced hulls. *)
Lemma sb_reduce_half_monotone : forall w s a b,
  sb_order w a b = true ->
  sb_order w (sb_reduce_half w s a) (sb_reduce_half w s b) = true.
Proof.
  intros w s a b Hle. change (sb_leb w s a b = true).
  apply (proj2 (sb_leb_spec w s a b)). intros z Hz.
  now apply (sb_order_sound w s a b z Hle).
Qed.

Lemma sb_summary_cover : forall w s S a q,
  sb_summary w S a -> (forall x, S x -> sb_half_gamma w s q x) ->
  forall z, sb_half_gamma w s a z -> sb_half_gamma w s q z.
Proof.
  intros w s S a q Hsummary Hsub z Hz. eapply sb_order_sound; [|exact Hz].
  now apply (sb_order_summary w s S).
Qed.

Definition sb_join (w : width) (s : bool) (a b : sb_half) : sb_half :=
  sb_reduce_half w s (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)).

Lemma sb_join_summary : forall w s a b,
  sb_summary w (fun x => sb_half_gamma w s a x \/ sb_half_gamma w s b x)
    (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)).
Proof.
  intros. apply sb_merge_summary; apply sb_reduce_half_summary.
Qed.

Lemma sb_join_upper : forall w s a b z,
  sb_half_gamma w s a z \/ sb_half_gamma w s b z -> sb_half_gamma w s (sb_join w s a b) z.
Proof.
  intros w s a b z Hz. unfold sb_join. apply sb_reduce_half_gamma.
  pose proof (sb_join_summary w s a b) as Hsummary.
  destruct (sb_merge w (sb_reduce_half w s a) (sb_reduce_half w s b)) as [|t lo hi].
  - exfalso. exact (Hsummary z Hz).
  - destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    destruct (Hsound z Hz) as [Hw [Ht Hb]]. apply sb_half_gamma_range.
    split; [exact Hw|]. split; [|now split].
    destruct Hz as [Hz|Hz]; exact (proj2 (sb_half_word_sign w s _ z Hz)).
Qed.

Lemma sb_join_least : forall w s a b q,
  sb_leb w s a q = true -> sb_leb w s b q = true -> sb_leb w s (sb_join w s a b) q = true.
Proof.
  intros w s a b q Ha Hb.
  pose proof (proj1 (sb_leb_spec w s a q) Ha) as Hacover.
  pose proof (proj1 (sb_leb_spec w s b q) Hb) as Hbcover.
  apply (proj2 (sb_leb_spec w s (sb_join w s a b) q)).
  intros z Hz. unfold sb_join in Hz. rewrite sb_reduce_half_gamma in Hz.
  eapply sb_summary_cover; [apply sb_join_summary| |exact Hz].
  intros x [Hx|Hx]; [now apply Hacover|now apply Hbcover].
Qed.

Definition signed_bounds_leb (w : width) (a b : signed_bounds) : bool :=
  sb_leb w false (sb_zero a) (sb_zero b) && sb_leb w true (sb_one a) (sb_one b).

Definition signed_bounds_join (w : width) (a b : signed_bounds) : signed_bounds :=
  SignedBounds (sb_join w false (sb_zero a) (sb_zero b))
    (sb_join w true (sb_one a) (sb_one b)).

(** The preorder compares exact normalized components; widening is this finite-width join. *)
Definition signed_bounds_lattice (w : width) : lattice signed_bounds :=
  {| leb := signed_bounds_leb w;
     bot := SignedBounds SBEmpty SBEmpty;
     join := signed_bounds_join w;
     widen := signed_bounds_join w;
     narrow a _ := signed_bounds_reduce w a |}.

Lemma signed_bounds_leb_spec : forall w a b,
  signed_bounds_leb w a b = true <->
  forall z, signed_bounds_gamma w a z -> signed_bounds_gamma w b z.
Proof.
  intros w a b. unfold signed_bounds_leb. rewrite andb_true_iff, !sb_leb_spec.
  split.
  - intros [H0 H1] z [Hz|Hz]; [left; now apply H0|right; now apply H1].
  - intro Hsub. split; intros z Hz; specialize (Hsub z);
      destruct (Hsub ltac:(unfold signed_bounds_gamma; tauto)) as [Hout|Hout];
      try exact Hout; apply sb_half_word_sign in Hz, Hout;
      destruct Hz as [_ Hs], Hout as [_ Ht]; congruence.
Qed.

Lemma signed_bounds_join_sound : forall w a b z,
  signed_bounds_gamma w a z \/ signed_bounds_gamma w b z ->
  signed_bounds_gamma w (signed_bounds_join w a b) z.
Proof.
  intros w a b z Hz. unfold signed_bounds_gamma, signed_bounds_join in *.
  cbn [sb_zero sb_one]. destruct Hz as [[Hz|Hz]|[Hz|Hz]];
    first [left; apply sb_join_upper; tauto|right; apply sb_join_upper; tauto].
Qed.

Lemma signed_bounds_join_least : forall w a b q,
  signed_bounds_leb w a q = true -> signed_bounds_leb w b q = true ->
  signed_bounds_leb w (signed_bounds_join w a b) q = true.
Proof.
  intros w a b q Ha Hb. unfold signed_bounds_leb, signed_bounds_join in *.
  cbn [sb_zero sb_one]. rewrite andb_true_iff in *. destruct Ha, Hb.
  split; now apply sb_join_least.
Qed.

(** The exact component order, join and canonical narrowing satisfy the weak lattice laws. *)
Theorem signed_bounds_laws : forall w, lattice_laws (signed_bounds_lattice w).
Proof.
  intro w. constructor; cbn [signed_bounds_lattice leb bot join widen narrow].
  - intro a. apply signed_bounds_leb_spec. auto.
  - intros a b c Hab Hbc. rewrite signed_bounds_leb_spec in Hab, Hbc |- *.
    auto.
  - intro a. reflexivity.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now left.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now right.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now left.
  - intros a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_join_sound. now right.
  - intros a b _. apply signed_bounds_leb_spec. intros z Hz.
    now rewrite signed_bounds_reduce_gamma in Hz.
  - intros a b Hba. rewrite signed_bounds_leb_spec in Hba |- *.
    intros z Hz. rewrite signed_bounds_reduce_gamma. now apply Hba.
Qed.

Definition sb_raw_measure (w : width) (h : sb_half) : nat :=
  match h with
  | SBEmpty => 0%nat
  | SBRange t lo hi => (1 + tnum_rank w t + Z.to_nat (hi - lo))%nat
  end.

Definition sb_measure_bound (w : width) : nat :=
  (1 + 2 * Pos.to_nat w + Z.to_nat (modulus w))%nat.

Lemma sb_reduced_bounds : forall w s h t lo hi,
  sb_reduce_half w s h = SBRange t lo hi ->
  0 <= lo <= hi /\ hi < modulus w.
Proof.
  intros w s h t lo hi Heq. pose proof (sb_reduce_half_summary w s h) as Hsummary.
  rewrite Heq in Hsummary. destruct Hsummary as [_ [Hlo [Hhi [Hsound _]]]].
  pose proof (Hsound lo Hlo) as [Hword Hbounds].
  pose proof (Hsound hi Hhi) as [Hword' Hbounds'].
  unfold is_word in *. tauto || lia.
Qed.

Lemma sb_order_measure : forall w a b,
  sb_order w a b = true ->
  (sb_raw_measure w a <= sb_raw_measure w b)%nat.
Proof.
  intros w [|ta la ua] [|tb lb ub] Hle; try discriminate;
    cbn [sb_raw_measure]; try lia.
  unfold sb_order in Hle. rewrite !andb_true_iff, !Z.leb_le in Hle.
  destruct Hle as [[Ht Hl] Hu]. pose proof (tnum_rank_monotone w ta tb Ht).
  assert (Hspan : (Z.to_nat (ua - la) <= Z.to_nat (ub - lb))%nat).
  { destruct (Z_le_dec 0 (ua - la)).
    - apply Z2Nat.inj_le; lia.
    - assert (Hzero : Z.to_nat (ua - la) = 0%nat)
        by (destruct (ua - la); cbn; try reflexivity; lia).
      rewrite Hzero. lia. }
  lia.
Qed.

Definition sb_ordered (h : sb_half) : Prop :=
  match h with
  | SBEmpty => True
  | SBRange _ lo hi => lo <= hi
  end.

Lemma sb_reduce_ordered : forall w s h, sb_ordered (sb_reduce_half w s h).
Proof.
  intros w s h. destruct (sb_reduce_half w s h) as [|t lo hi] eqn:Heq; [exact I|].
  pose proof (sb_reduced_bounds w s h t lo hi Heq). cbn [sb_ordered]. lia.
Qed.

Lemma sb_order_measure_equal : forall w a b,
  sb_ordered a -> sb_ordered b ->
  sb_order w a b = true -> sb_raw_measure w a = sb_raw_measure w b ->
  sb_order w b a = true.
Proof.
  intros w [|ta la ua] [|tb lb ub] Ha Hb Hle Heq; try discriminate; try reflexivity.
  unfold sb_order in Hle |- *. rewrite !andb_true_iff, !Z.leb_le in *.
  destruct Hle as [[Ht Hl] Hu]. pose proof (tnum_rank_monotone w ta tb Ht) as Hrank.
  assert (Hspan : (Z.to_nat (ua - la) <= Z.to_nat (ub - lb))%nat).
  { cbn [sb_ordered] in Ha, Hb. apply Z2Nat.inj_le; lia. }
  cbn [sb_raw_measure] in Heq.
  assert (Hrankeq : tnum_rank w ta = tnum_rank w tb) by lia.
  assert (Hspaneq : Z.to_nat (ua - la) = Z.to_nat (ub - lb)) by lia.
  cbn [sb_ordered] in Ha, Hb.
  apply (f_equal Z.of_nat) in Hspaneq. rewrite !Z2Nat.id in Hspaneq by lia.
  split; [split; [now apply tnum_rank_equal|]|]; lia.
Qed.

Definition signed_bounds_measure (w : width) (a : signed_bounds) : nat :=
  (sb_raw_measure w (sb_reduce_half w false (sb_zero a)) +
    sb_raw_measure w (sb_reduce_half w true (sb_one a)))%nat.

Lemma signed_bounds_measure_bounded : forall w a,
  (signed_bounds_measure w a <= 2 * sb_measure_bound w)%nat.
Proof.
  intros w a.
  assert (Hhalf : forall s h, (sb_raw_measure w (sb_reduce_half w s h) <=
    sb_measure_bound w)%nat).
  { intros s h. destruct (sb_reduce_half w s h) as [|t lo hi] eqn:Heq;
      [cbn; lia|].
    pose proof (sb_reduced_bounds w s h t lo hi Heq) as Hbounds.
    pose proof (rank_bounded (base_height (tnum_height w)) t) as Hrank.
    change (tnum_rank w t <= 2 * Pos.to_nat w)%nat in Hrank.
    assert (Hspan : (Z.to_nat (hi - lo) <= Z.to_nat (modulus w))%nat).
    { apply Z2Nat.inj_le; pose proof (modulus_pos w); lia. }
    unfold sb_raw_measure, sb_measure_bound. lia. }
  unfold signed_bounds_measure. specialize (Hhalf false (sb_zero a)) as H0.
  specialize (Hhalf true (sb_one a)) as H1. lia.
Qed.

Lemma signed_bounds_measure_monotone : forall w a b,
  signed_bounds_leb w a b = true ->
  (signed_bounds_measure w a <= signed_bounds_measure w b)%nat.
Proof.
  intros w a b Hle. apply andb_true_iff in Hle as [H0 H1].
  apply sb_order_measure in H0, H1. unfold signed_bounds_measure. lia.
Qed.

Lemma signed_bounds_measure_equal : forall w a b,
  signed_bounds_leb w a b = true -> signed_bounds_measure w a = signed_bounds_measure w b ->
  signed_bounds_leb w b a = true.
Proof.
  intros w a b Hle Heq. apply andb_true_iff in Hle as [H0 H1].
  pose proof (sb_order_measure w _ _ H0) as Hr0.
  pose proof (sb_order_measure w _ _ H1) as Hr1.
  unfold signed_bounds_measure in Heq. unfold signed_bounds_leb.
  apply andb_true_iff. split; apply sb_order_measure_equal;
    try apply sb_reduce_ordered; try assumption; lia.
Qed.

(** The decreasing rank counts remaining interval growth and remaining fixed-bit loss
    after the actual raw-input normalization used by comparison and widening. *)
Definition signed_bounds_wrank (w : width) :
  bounded_widening_rank (signed_bounds_lattice w).
Proof.
  unshelve refine (@BoundedWideningRank _ _
    (@WideningRank _ _ (fun a => (2 * sb_measure_bound w - signed_bounds_measure w a)%nat)
      _ _) (2 * sb_measure_bound w)%nat _).
  - intros a b Hstable.
    pose proof (join_upper_l (signed_bounds_laws w) a b) as Hupper.
    apply signed_bounds_measure_monotone in Hupper.
    change (signed_bounds_measure w a <=
      signed_bounds_measure w (signed_bounds_join w a b))%nat in Hupper.
    change (2 * sb_measure_bound w - signed_bounds_measure w (signed_bounds_join w a b) <=
      2 * sb_measure_bound w - signed_bounds_measure w a)%nat. lia.
  - intros a b Hstrict.
    pose proof (join_upper_l (signed_bounds_laws w) a b) as Hupper.
    pose proof (join_upper_r (signed_bounds_laws w) a b) as Hright.
    pose proof (signed_bounds_measure_monotone w _ _ Hupper) as Hrank.
    change (signed_bounds_measure w a <=
      signed_bounds_measure w (signed_bounds_join w a b))%nat in Hrank.
    pose proof (signed_bounds_measure_bounded w (signed_bounds_join w a b)) as Hbound.
    assert (Hprogress : (signed_bounds_measure w a <
      signed_bounds_measure w (signed_bounds_join w a b))%nat).
    { destruct (Nat.eq_dec (signed_bounds_measure w a)
        (signed_bounds_measure w (signed_bounds_join w a b))) as [Heq|Hne]; [|lia].
      pose proof (signed_bounds_measure_equal w _ _ Hupper Heq) as Hreverse.
      pose proof (leb_trans (signed_bounds_laws w) b _ a Hright Hreverse). congruence. }
    change (2 * sb_measure_bound w - signed_bounds_measure w (signed_bounds_join w a b) <
      2 * sb_measure_bound w - signed_bounds_measure w a)%nat. lia.
  - intros a. change (2 * sb_measure_bound w - signed_bounds_measure w a <=
      2 * sb_measure_bound w)%nat. lia.
Defined.

Definition sb_half_meet (w : width) (s : bool) (a b : sb_half) : sb_half :=
  sb_reduce_half w s
    (match sb_reduce_half w s a, sb_reduce_half w s b with
     | SBRange ta la ua, SBRange tb lb ub =>
       SBRange (tnum_meet w ta tb) (Z.max la lb) (Z.min ua ub)
     | _, _ => SBEmpty
     end).

Lemma sb_half_meet_gamma : forall w s a b z,
  sb_half_gamma w s (sb_half_meet w s a b) z <->
  sb_half_gamma w s a z /\ sb_half_gamma w s b z.
Proof.
  intros w s a b z. unfold sb_half_meet. rewrite sb_reduce_half_gamma.
  rewrite <- (sb_reduce_half_gamma w s a z), <- (sb_reduce_half_gamma w s b z).
  destruct (sb_reduce_half w s a) as [|ta la ua],
    (sb_reduce_half w s b) as [|tb lb ub];
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma; try tauto.
  rewrite sb_meet_gamma. rewrite Z.max_lub_iff, Z.min_glb_iff. tauto.
Qed.

Definition signed_bounds_meet (w : width) (a b : signed_bounds) : signed_bounds :=
  SignedBounds (sb_half_meet w false (sb_zero a) (sb_zero b))
    (sb_half_meet w true (sb_one a) (sb_one b)).

Lemma signed_bounds_meet_gamma : forall w a b z,
  signed_bounds_gamma w (signed_bounds_meet w a b) z <->
  signed_bounds_gamma w a z /\ signed_bounds_gamma w b z.
Proof.
  intros w a b z. unfold signed_bounds_gamma, signed_bounds_meet. cbn [sb_zero sb_one].
  rewrite !sb_half_meet_gamma. split; [tauto|].
  intros [[Ha|Ha] [Hb|Hb]]; try tauto;
    pose proof (sb_half_word_sign w _ _ z Ha) as [_ Hsa];
    pose proof (sb_half_word_sign w _ _ z Hb) as [_ Hsb]; congruence.
Qed.

(** A linear bit-and-bounds conjunction is split and reduced into both result hemispheres. *)
Definition sb_lift (w : width) (t : tnum) (lo hi : Z) : signed_bounds :=
  signed_bounds_reduce w (SignedBounds (SBRange t lo hi) (SBRange t lo hi)).

Lemma sb_lift_gamma : forall w t lo hi z,
  signed_bounds_gamma w (sb_lift w t lo hi) z <->
  is_word w z /\ tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros w t lo hi z. unfold sb_lift. rewrite signed_bounds_reduce_gamma.
  unfold signed_bounds_gamma. cbn [sb_zero sb_one].
  rewrite !sb_half_gamma_range. destruct (msb w z); tauto.
Qed.

Definition signed_bounds_top (w : width) : signed_bounds :=
  sb_lift w tnum_top 0 (modulus w - 1).

Lemma signed_bounds_top_sound : forall w z,
  is_word w z -> signed_bounds_gamma w (signed_bounds_top w) z.
Proof.
  intros w z Hz. apply sb_lift_gamma. split; [exact Hz|]. split;
    [apply tnum_top_sound|unfold is_word in Hz; lia].
Qed.

Definition signed_bounds_const (w : width) (z : Z) : signed_bounds :=
  sb_lift w (tnum_const w z) (wrap w z) (wrap w z).

Lemma signed_bounds_const_sound : forall w z,
  signed_bounds_gamma w (signed_bounds_const w z) (wrap w z).
Proof.
  intros w z. apply sb_lift_gamma. split; [apply wrap_is_word|].
  split; [apply tnum_const_sound|lia].
Qed.

Definition sb_from_interval (w : width) (t : tnum) (i : interval) : signed_bounds :=
  match i with
  | IBot => SignedBounds SBEmpty SBEmpty
  | Itv lo hi =>
    sb_lift w t
      (match lo with
       | Fin l => l
       | _ => 0
       end)
      (match hi with
       | Fin u => u
       | _ => modulus w - 1
       end)
  end.

Lemma sb_from_interval_sound : forall w t i z,
  tnum_gamma w t z -> interval_pgamma w i z ->
  signed_bounds_gamma w (sb_from_interval w t i) z.
Proof.
  intros w t [|l u] z Ht [Hw Hi]; [contradiction|].
  destruct l as [|l|], u as [|u|]; cbn [interval_gamma gamma bound_leb] in Hi;
    try (destruct Hi; discriminate).
  all: apply sb_lift_gamma; split; [exact Hw|split; [exact Ht|]].
  all: rewrite ?Z.leb_le in Hi; unfold is_word in Hw; intuition lia.
Qed.

(** Splitting both circular pieces before joining also covers two intersections in one sign. *)
Definition sb_from_components (w : width) (t : tnum) (arc : wrapped) : signed_bounds :=
  let pieces := wrapped_parts w arc in
  signed_bounds_join w (sb_from_interval w t (fst pieces))
    (sb_from_interval w t (snd pieces)).

Lemma sb_from_components_sound : forall w t arc z,
  tnum_gamma w t z -> wrapped_gamma w arc z ->
  signed_bounds_gamma w (sb_from_components w t arc) z.
Proof.
  intros w t arc z Ht Harc. apply wrapped_parts_spec in Harc.
  unfold sb_from_components. apply signed_bounds_join_sound.
  destruct Harc as [Hpiece|Hpiece]; [left|right]; now apply sb_from_interval_sound.
Qed.

Definition sb_plain_gamma (w : width) (h : sb_half) (z : Z) : Prop :=
  match h with
  | SBEmpty => False
  | SBRange t lo hi => is_word w z /\ tnum_gamma w t z /\ lo <= z <= hi
  end.

Lemma sb_half_plain : forall w s h z,
  sb_half_gamma w s h z -> sb_plain_gamma w h z.
Proof.
  intros w s [|t lo hi] z Hz;
    unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma, sb_plain_gamma in *; tauto.
Qed.

Definition sb_half_bits (w : width) (h : sb_half) : tnum :=
  match h with
  | SBEmpty => bot (tnum_lattice w)
  | SBRange t _ _ => t
  end.

Definition sb_half_arc (w : width) (h : sb_half) : wrapped :=
  match h with
  | SBEmpty => WBot
  | SBRange _ lo hi => wrapped_range w lo hi
  end.

Lemma sb_half_components : forall w h z,
  sb_plain_gamma w h z ->
  tnum_gamma w (sb_half_bits w h) z /\ wrapped_gamma w (sb_half_arc w h) z.
Proof.
  intros w [|t lo hi] z Hz; [contradiction|]. destruct Hz as [Hw [Ht Hb]].
  split; [exact Ht|]. cbn [sb_half_arc]. rewrite <- (wrap_id w z Hw).
  now apply wrapped_range_sound.
Qed.

Definition sb_lift_half (w : width) (h : sb_half) : signed_bounds :=
  match h with
  | SBEmpty => SignedBounds SBEmpty SBEmpty
  | SBRange t lo hi => sb_lift w t lo hi
  end.

Lemma sb_lift_half_gamma : forall w h z,
  signed_bounds_gamma w (sb_lift_half w h) z <-> sb_plain_gamma w h z.
Proof.
  intros w [|t lo hi] z; [unfold signed_bounds_gamma, sb_half_gamma; cbn; tauto|].
  apply sb_lift_gamma.
Qed.

(** Operand alternatives are constructed once; callers restrict the shape to at most three. *)
Fixpoint sb_choices (wps : list (width * signed_bounds)) : list (list (width * sb_half)) :=
  match wps with
  | [] => [[]]
  | (w, a) :: rest =>
    let tails := sb_choices rest in
    let a' := signed_bounds_reduce w a in
    map (cons (w, sb_zero a')) tails ++ map (cons (w, sb_one a')) tails
  end.

Lemma sb_choices_sound : forall wps ys,
  Forall2 (payload_sound signed_bounds_gamma) wps ys ->
  exists hs, In hs (sb_choices wps) /\ Forall2 (payload_sound sb_plain_gamma) hs ys.
Proof.
  intros wps ys Hpayload.
  induction Hpayload as [|[w a] [v z] rest values Hhead Htail IH].
  - exists []. split; [now left|constructor].
  - destruct IH as [hs [Hin Hhs]]. destruct Hhead as [Hwidth [Hw Ha]].
    cbn in Hwidth, Hw, Ha. subst v.
    apply (proj2 (signed_bounds_reduce_gamma w a z)) in Ha.
    destruct Ha as [Ha|Ha].
    + exists ((w, sb_zero (signed_bounds_reduce w a)) :: hs). split.
      * cbn [sb_choices]. apply in_or_app. left. apply in_map. exact Hin.
      * constructor; [split; [reflexivity|split; [exact Hw|now apply sb_half_plain in Ha]]|
          exact Hhs].
    + exists ((w, sb_one (signed_bounds_reduce w a)) :: hs). split.
      * cbn [sb_choices]. apply in_or_app. right. apply in_map. exact Hin.
      * constructor; [split; [reflexivity|split; [exact Hw|now apply sb_half_plain in Ha]]|
          exact Hhs].
Qed.

Lemma sb_choices_widths : forall wps hs,
  In hs (sb_choices wps) -> map fst hs = map fst wps.
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros hs Hin.
  - destruct Hin as [<-|Hnone]; [reflexivity|contradiction].
  - cbn [sb_choices] in Hin. apply in_app_iff in Hin as [Hin|Hin];
      apply in_map_iff in Hin as [tail [<- Hin]]; cbn; f_equal; now apply IH.
Qed.

Lemma sb_component_payloads : forall hs ys,
  Forall2 (payload_sound sb_plain_gamma) hs ys ->
  Forall2 (payload_sound tnum_gamma)
    (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) ys /\
  Forall2 (payload_sound wrapped_gamma)
    (map (fun wh => (fst wh, sb_half_arc (fst wh) (snd wh))) hs) ys.
Proof.
  intros hs ys Hpayload.
  induction Hpayload as [|[w h] [v z] rest values Hhead Htail IH].
  - split; constructor.
  - destruct Hhead as [Hwidth [Hw Hh]]. cbn in Hwidth, Hw, Hh. subst v.
    destruct (sb_half_components w h z Hh) as [Ht Ha].
    destruct IH as [IHt IHa]. split.
    + constructor; [split; [reflexivity|split; assumption]|exact IHt].
    + constructor; [split; [reflexivity|split; assumption]|exact IHa].
Qed.

(** One hemisphere combination uses the selected known-bit forward transfer and wrapped bounds. *)
Definition sb_case_forward (D : word_domain tnum) (o : op)
    (hs : list (width * sb_half)) (rw : width) : signed_bounds :=
  sb_from_components rw
    (pforward D o
      (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) rw)
    (pforward wrapped_domain o
      (map (fun wh => (fst wh, sb_half_arc (fst wh) (snd wh))) hs) rw).

Lemma sb_case_forward_sound : forall D, word_laws D tnum_gamma -> forall o hs ys rw z,
  Forall2 (payload_sound sb_plain_gamma) hs ys -> eval_op o ys = Some (rw, z) ->
  signed_bounds_gamma rw (sb_case_forward D o hs rw) z.
Proof.
  intros D laws o hs ys rw z Hpayload Heval. destruct (sb_component_payloads hs ys Hpayload)
    as [Ht Ha]. unfold sb_case_forward. apply sb_from_components_sound.
  - exact (pforward_sound laws o _ ys rw z Ht Heval).
  - exact (pforward_sound wrapped_word_laws o _ ys rw z Ha Heval).
Qed.

Definition sb_join_all (w : width) (xs : list signed_bounds) : signed_bounds :=
  fold_right (signed_bounds_join w) (SignedBounds SBEmpty SBEmpty) xs.

Lemma sb_join_all_sound : forall w xs a z,
  In a xs -> signed_bounds_gamma w a z -> signed_bounds_gamma w (sb_join_all w xs) z.
Proof.
  intros w xs. induction xs as [|h rest IH]; intros a z Hin Hz; [contradiction|].
  cbn [sb_join_all fold_right]. apply signed_bounds_join_sound.
  destruct Hin as [<-|Hin]; [now left|right; now apply (IH a z)].
Qed.

Lemma sb_join_all_least : forall w xs q,
  (forall a, In a xs -> signed_bounds_leb w a q = true) ->
  signed_bounds_leb w (sb_join_all w xs) q = true.
Proof.
  intros w xs. induction xs as [|a rest IH]; intros q Hsub; [reflexivity|].
  cbn [sb_join_all fold_right]. apply signed_bounds_join_least.
  - apply Hsub. now left.
  - apply IH. intros b Hb. apply Hsub. now right.
Qed.

(** Malformed long shapes return top; valid Bits operators have at most eight alternatives. *)
Definition signed_bounds_forward (D : word_domain tnum) (o : op)
    (wps : list (width * signed_bounds)) (rw : width) : signed_bounds :=
  if Nat.leb (length wps) 3 then
    sb_join_all rw (map (fun hs => sb_case_forward D o hs rw) (sb_choices wps))
  else signed_bounds_top rw.

Lemma signed_bounds_forward_sound : forall D, word_laws D tnum_gamma ->
  forall o wps ys rw z,
  Forall2 (payload_sound signed_bounds_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  signed_bounds_gamma rw (signed_bounds_forward D o wps rw) z.
Proof.
  intros D laws o wps ys rw z Hpayload Heval. unfold signed_bounds_forward.
  destruct (Nat.leb (length wps) 3).
  - destruct (sb_choices_sound wps ys Hpayload) as [hs [Hin Hhs]].
    apply (sb_join_all_sound rw _ (sb_case_forward D o hs rw) z).
    + apply in_map_iff. exists hs. now split.
    + now apply (sb_case_forward_sound D laws o hs ys).
  - apply signed_bounds_top_sound. exact (eval_op_is_word o ys (rw, z) Heval).
Qed.

Definition sb_is_empty (h : sb_half) : bool :=
  match h with
  | SBEmpty => true
  | SBRange _ _ _ => false
  end.

Lemma sb_payload_nonempty : forall hs ys,
  Forall2 (payload_sound sb_plain_gamma) hs ys ->
  existsb (fun wh => sb_is_empty (snd wh)) hs = false.
Proof.
  intros hs ys Hpayload. induction Hpayload as [|[w h] y rest values Hhead Htail IH];
    [reflexivity|].
  destruct Hhead as [_ [_ Hh]]. destruct h; [contradiction|]. cbn. exact IH.
Qed.

(** Each candidate is intersected with its own original hemisphere before alternatives join. *)
Fixpoint sb_candidates (hs : list (width * sb_half)) (ts : list tnum) (arcs : list wrapped) :
    list signed_bounds :=
  match hs, ts, arcs with
  | [], _, _ => []
  | (w, h) :: rest, t :: tail, arc :: more =>
    signed_bounds_meet w (sb_lift_half w h) (sb_from_components w t arc) ::
      sb_candidates rest tail more
  | (w, h) :: rest, _, _ => sb_lift_half w h :: sb_candidates rest [] []
  end.

Lemma sb_candidates_length : forall hs ts arcs,
  length (sb_candidates hs ts arcs) = length hs.
Proof.
  intro hs. induction hs as [|[w h] rest IH]; intros [|t ts] [|arc arcs]; cbn;
    [reflexivity|reflexivity|reflexivity|reflexivity| | | |]; f_equal; apply IH.
Qed.

Lemma sb_candidates_sound : forall hs ys ts arcs,
  Forall2 (payload_sound sb_plain_gamma) hs ys ->
  Forall2 (fun p y => tnum_gamma (fst p) (snd p) (snd y)) (combine (map fst hs) ts) ys ->
  Forall2 (fun p y => wrapped_gamma (fst p) (snd p) (snd y))
    (combine (map fst hs) arcs) ys ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine (map fst hs) (sb_candidates hs ts arcs)) ys.
Proof.
  intros hs ys ts arcs Hpayload. revert ts arcs.
  induction Hpayload as [|[w h] [v z] rest values Hhead Htail IH];
    intros [|t ts] [|arc arcs] Hbits Harcs; cbn in *;
    try solve [inversion Hbits]; try solve [inversion Harcs]; try solve [constructor].
  destruct Hhead as [Hwidth [Hw Hh]]. cbn in Hwidth, Hw, Hh. subst v.
  inversion Hbits as [|p y tail ys Ht Hts]; subst.
  inversion Harcs as [|p y tail ys Ha Has]; subst.
  constructor.
  - apply signed_bounds_meet_gamma. split.
    + now apply sb_lift_half_gamma.
    + now apply sb_from_components_sound.
  - now apply IH.
Qed.

Definition sb_case_assume (o : op) (hs : list (width * sb_half)) (rw : width) (q : sb_half) :
    list signed_bounds :=
  if sb_is_empty q || existsb (fun wh => sb_is_empty (snd wh)) hs
  then map (fun _ => SignedBounds SBEmpty SBEmpty) hs
  else sb_candidates hs
    (passume known_bits_domain o
      (map (fun wh => (fst wh, sb_half_bits (fst wh) (snd wh))) hs) rw (sb_half_bits rw q))
    (passume wrapped_domain o
      (map (fun wh => (fst wh, sb_half_arc (fst wh) (snd wh))) hs) rw (sb_half_arc rw q)).

Lemma sb_case_assume_sound : forall o hs ys rw z q,
  Forall2 (payload_sound sb_plain_gamma) hs ys -> eval_op o ys = Some (rw, z) ->
  sb_plain_gamma rw q z ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine (map fst hs) (sb_case_assume o hs rw q)) ys.
Proof.
  intros o hs ys rw z q Hpayload Heval Hq.
  pose proof (sb_payload_nonempty hs ys Hpayload) as Hnonempty.
  assert (Hqnonempty : sb_is_empty q = false) by (destruct q; [contradiction|reflexivity]).
  unfold sb_case_assume. rewrite Hnonempty, Hqnonempty. cbn [orb].
  destruct (sb_component_payloads hs ys Hpayload) as [Hbits Harcs].
  destruct (sb_half_components rw q z Hq) as [Hqt Hqa].
  pose proof (passume_sound known_bits_word_laws o _ ys rw z (sb_half_bits rw q)
    Hbits Heval Hqt) as Hbackbits.
  pose proof (passume_sound wrapped_word_laws o _ ys rw z (sb_half_arc rw q)
    Harcs Heval Hqa) as Hbackarcs.
  rewrite map_map in Hbackbits, Hbackarcs. cbn [fst] in Hbackbits, Hbackarcs.
  now apply sb_candidates_sound.
Qed.

(** Column joins retain one output per operand even when there are no feasible alternatives. *)
Fixpoint sb_columns (ws : list width) (alternatives : list (list signed_bounds)) :
    list signed_bounds :=
  match ws with
  | [] => []
  | w :: rest =>
    sb_join_all w (map (hd (SignedBounds SBEmpty SBEmpty)) alternatives) ::
      sb_columns rest (map (@tl signed_bounds) alternatives)
  end.

Lemma sb_columns_sound : forall ws alternatives qs (ys : list word),
  In qs alternatives ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y)) (combine ws qs) ys ->
  length ws = length ys ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine ws (sb_columns ws alternatives)) ys.
Proof.
  intro ws. induction ws as [|w rest IH]; intros alternatives [|q qs] [|[v z] values]
    Hin Hsound Hlength; cbn in *; try discriminate;
    try solve [inversion Hsound]; try solve [constructor].
  inversion Hsound as [|p y tail ys Hq Hqs]; subst. constructor.
  - apply (sb_join_all_sound w _ q z); [|exact Hq].
    apply in_map_iff. exists (q :: qs). now split.
  - apply (IH _ qs); [|exact Hqs|lia]. apply in_map_iff. exists (q :: qs). now split.
Qed.

(** The final meet also protects refinement for arbitrary raw inputs and malformed shapes. *)
Fixpoint sb_refine_original (wps : list (width * signed_bounds)) (qs : list signed_bounds) :
    list signed_bounds :=
  match wps, qs with
  | [], _ => []
  | (w, a) :: rest, q :: tail => signed_bounds_meet w a q :: sb_refine_original rest tail
  | (w, a) :: rest, [] => signed_bounds_reduce w a :: sb_refine_original rest []
  end.

Lemma sb_refine_original_refines : forall wps qs,
  Forall2 (fun wp q => signed_bounds_leb (fst wp) q (snd wp) = true)
    wps (sb_refine_original wps qs).
Proof.
  intro wps. induction wps as [|[w a] rest IH]; intros [|q qs]; cbn; constructor.
  - apply signed_bounds_leb_spec. intros z Hz. now rewrite signed_bounds_reduce_gamma in Hz.
  - apply IH.
  - apply signed_bounds_leb_spec. intros z Hz. apply signed_bounds_meet_gamma in Hz. tauto.
  - apply IH.
Qed.

Lemma sb_refine_original_sound : forall wps ys qs,
  Forall2 (payload_sound signed_bounds_gamma) wps ys ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) qs) ys ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (sb_refine_original wps qs)) ys.
Proof.
  intros wps ys qs Hpayload. revert qs.
  induction Hpayload as [|[w a] [v z] rest values Hhead Htail IH];
    intros [|q qs] Hqs; cbn in *; try solve [inversion Hqs]; try solve [constructor].
  inversion Hqs as [|p y tail ys Hq Hrest]; subst. constructor.
  - apply signed_bounds_meet_gamma. split; [exact (proj2 (proj2 Hhead))|exact Hq].
  - now apply IH.
Qed.

Definition sb_valid_shape (o : op) (wps : list (width * signed_bounds)) (rw : width) : bool :=
  Nat.leb (length wps) 3 &&
    match result_width o (map fst wps) with
    | Some w => Pos.eqb w rw
    | None => false
    end.

Definition signed_bounds_assume (o : op) (wps : list (width * signed_bounds))
    (rw : width) (q : signed_bounds) : list signed_bounds :=
  if sb_valid_shape o wps rw then
    let q' := signed_bounds_reduce rw q in
    let alternatives := flat_map (fun hs =>
      [sb_case_assume o hs rw (sb_zero q'); sb_case_assume o hs rw (sb_one q')])
      (sb_choices wps) in
    sb_refine_original wps (sb_columns (map fst wps) alternatives)
  else map (fun wp => signed_bounds_reduce (fst wp) (snd wp)) wps.

Lemma signed_bounds_assume_refines : forall o wps rw q,
  Forall2 (fun wp q' => signed_bounds_leb (fst wp) q' (snd wp) = true)
    wps (signed_bounds_assume o wps rw q).
Proof.
  intros o wps rw q. unfold signed_bounds_assume. destruct (sb_valid_shape o wps rw).
  - apply sb_refine_original_refines.
  - induction wps as [|[w a] rest IH]; cbn; constructor; [|exact IH].
    apply signed_bounds_leb_spec. intros z Hz. now rewrite signed_bounds_reduce_gamma in Hz.
Qed.

Lemma signed_bounds_assume_sound : forall o wps ys rw z q,
  Forall2 (payload_sound signed_bounds_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  signed_bounds_gamma rw q z ->
  Forall2 (fun p y => signed_bounds_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (signed_bounds_assume o wps rw q)) ys.
Proof.
  intros o wps ys rw z q Hpayload Heval Hq. unfold signed_bounds_assume.
  destruct (sb_valid_shape o wps rw).
  - destruct (sb_choices_sound wps ys Hpayload) as [hs [Hin Hhs]].
    pose proof (sb_choices_widths wps hs Hin) as Hwidths.
    apply sb_refine_original_sound; [exact Hpayload|].
    apply (proj2 (signed_bounds_reduce_gamma rw q z)) in Hq.
    destruct Hq as [Hq|Hq].
    + apply (sb_columns_sound _ _ (sb_case_assume o hs rw
        (sb_zero (signed_bounds_reduce rw q)))).
      * apply in_flat_map. exists hs. split; [exact Hin|now left].
      * rewrite <- Hwidths. eapply sb_case_assume_sound; try eassumption.
        now apply sb_half_plain in Hq.
      * rewrite length_map. now apply Forall2_length in Hpayload.
    + apply (sb_columns_sound _ _ (sb_case_assume o hs rw
        (sb_one (signed_bounds_reduce rw q)))).
      * apply in_flat_map. exists hs. split; [exact Hin|right; now left].
      * rewrite <- Hwidths. eapply sb_case_assume_sound; try eassumption.
        now apply sb_half_plain in Hq.
      * rewrite length_map. now apply Forall2_length in Hpayload.
  - clear Heval Hq. induction Hpayload as [|[w a] [v x] rest values Hhead Htail IH];
      cbn; constructor.
    + apply signed_bounds_reduce_gamma. exact (proj2 (proj2 Hhead)).
    + exact IH.
Qed.

(** The shared lifting selects only the known-bit forward dictionary; backward stays DOM-2. *)
Local Definition sb_domain (D : word_domain tnum) : word_domain signed_bounds :=
  {| plat := signed_bounds_lattice;
     ptop := signed_bounds_top;
     pconst := signed_bounds_const;
     pforward := signed_bounds_forward D;
     passume := signed_bounds_assume;
     pmeet := signed_bounds_meet |}.

Local Lemma sb_domain_laws : forall D, word_laws D tnum_gamma ->
  word_laws (sb_domain D) signed_bounds_gamma.
Proof.
  intros D laws. constructor.
  - apply signed_bounds_laws.
  - intros w a b z Hle Hz. exact (proj1 (signed_bounds_leb_spec w a b) Hle z Hz).
  - intros w z Hz. destruct Hz as [[Hempty _]|[Hempty _]]; contradiction.
  - apply signed_bounds_top_sound.
  - apply signed_bounds_const_sound.
  - now apply signed_bounds_forward_sound.
  - apply signed_bounds_assume_sound.
  - apply signed_bounds_assume_refines.
  - intros w a b z Ha Hb. apply signed_bounds_meet_gamma. now split.
  - intros w a b. apply signed_bounds_leb_spec. intros z Hz.
    apply signed_bounds_meet_gamma in Hz. tauto.
Qed.

(** The default dictionary lifts DOM-8's precise multiplication with exact half reduction. *)
Definition signed_bounds_domain : word_domain signed_bounds :=
  sb_domain known_bits_precise_domain.

(** The classic dictionary lifts DOM-2's multiplication with the same remaining operations. *)
Definition signed_bounds_classic_domain : word_domain signed_bounds :=
  sb_domain known_bits_domain.

(** Precise forward and DOM-2 backward calls compose for every total Bits evaluation. *)
Theorem signed_bounds_word_laws : word_laws signed_bounds_domain signed_bounds_gamma.
Proof.
  apply sb_domain_laws. apply known_bits_precise_word_laws.
Qed.

(** Classic forward and backward calls obey the same total raw-input word interface. *)
Theorem signed_bounds_classic_word_laws :
  word_laws signed_bounds_classic_domain signed_bounds_gamma.
Proof.
  apply sb_domain_laws. apply known_bits_word_laws.
Qed.

(** Width tags add the shared malformed-width, bottom and unrestricted-top behavior. *)
Definition signed_bounds_numeric : numeric_domain (tagged signed_bounds) :=
  tagged_domain signed_bounds_domain.

(** Capped clients widen width overflow to the shared tagged top. *)
Definition signed_bounds_capped (maxw : width) : numeric_domain (@capped signed_bounds maxw) :=
  capped_domain signed_bounds_domain maxw.

(** Tagged clients inherit the complete numeric-domain laws. *)
Theorem signed_bounds_numeric_laws :
  numeric_laws signed_bounds_numeric (tagged_gamma signed_bounds_gamma).
Proof.
  apply tagged_numeric_laws. apply signed_bounds_word_laws.
Qed.

(** Clamping preserves soundness and refinement for every cap. *)
Theorem signed_bounds_capped_laws : forall maxw,
  numeric_laws (signed_bounds_capped maxw) (capped_gamma signed_bounds_gamma maxw).
Proof.
  intro maxw. apply capped_numeric_laws. apply signed_bounds_word_laws.
Qed.

(** A query returns the exact reduced mask and feasible extrema for the selected sign. *)
Definition signed_bounds_query (w : width) (a : signed_bounds) (s : bool) :
    option (tnum * Z * Z) :=
  match sb_reduce_half w s (if s then sb_one a else sb_zero a) with
  | SBEmpty => None
  | SBRange t lo hi => Some (t, lo, hi)
  end.

(** Each query answer contains every original feasible value in its selected hemisphere. *)
Theorem signed_bounds_query_sound : forall w a s t lo hi z,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) z ->
  tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros w a s t lo hi z Hquery Hz. unfold signed_bounds_query in Hquery.
  pose proof (proj2 (sb_reduce_half_gamma w s _ z) Hz) as Hreduced.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  apply sb_half_gamma_range in Hreduced. tauto.
Qed.

(** Query failure decides emptiness of the original selected hemisphere. *)
Theorem signed_bounds_query_empty : forall w a s,
  signed_bounds_query w a s = None <->
  forall z, ~ sb_half_gamma w s (if s then sb_one a else sb_zero a) z.
Proof.
  intros w a s. unfold signed_bounds_query.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t lo hi].
  - split; [intro Hquery; exact Hsummary|intro Hempty; reflexivity].
  - split; [discriminate|]. intro Hempty.
    destruct Hsummary as [_ [Hlo _]]. exfalso. exact (Hempty lo Hlo).
Qed.

(** Both returned endpoints are themselves feasible original words. *)
Theorem signed_bounds_query_bounds_exact : forall w a s t lo hi,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) lo /\
  sb_half_gamma w s (if s then sb_one a else sb_zero a) hi.
Proof.
  intros w a s t lo hi Hquery. unfold signed_bounds_query in Hquery.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  destruct Hsummary as [_ [Hlo [Hhi _]]]. now split.
Qed.
