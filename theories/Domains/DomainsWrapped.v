(** * Circular word intervals

    Circular arcs represent contiguous sets of words across either numeric pole.
    For example, the eight-bit arc [250, 3] contains 255 and 0, but excludes 4.
    Builds on: Bits word arithmetic, DomainsNumeric and DomainsInterval. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsSigned BitsArith.
From Gaulois.Domains Require Import DomainsNumeric DomainsInterval.
Import List.ListNotations.

Local Open Scope Z_scope.

(** A circular interval is empty, full, or the inclusive arc between its endpoints. *)
Inductive wrapped : Type :=
  | WBot
  | WFull
  | WItv (lo hi : Z).

(** Offsets measure clockwise distance on the word circle. *)
Definition wrapped_offset (w : width) (origin x : Z) : Z :=
  (x - origin) mod modulus w.

(** Sizes count words, including both endpoints of a nonempty arc. *)
Definition wrapped_size (w : width) (a : wrapped) : Z :=
  match a with
  | WBot => 0
  | WFull => modulus w
  | WItv lo hi => wrapped_offset w lo hi + 1
  end.

(** An arc denotes exactly its word-valued clockwise offsets. *)
Definition wrapped_gamma (w : width) (a : wrapped) (z : Z) : Prop :=
  match a with
  | WBot => False
  | WFull => is_word w z
  | WItv lo hi => is_word w z /\ (z - lo) mod modulus w <= (hi - lo) mod modulus w
  end.

(** Normalization reads endpoints modulo the word size and canonicalizes the full circle. *)
Definition wrapped_norm (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi =>
    if wrapped_offset w lo hi =? modulus w - 1
    then WFull else WItv (wrap w lo) (wrap w hi)
  | _ => a
  end.

Lemma wrapped_offset_range : forall w c x,
  0 <= wrapped_offset w c x < modulus w.
Proof.
  intros w c x. apply Z.mod_pos_bound. apply modulus_pos.
Qed.

Lemma wrapped_offset_self : forall w c, wrapped_offset w c c = 0.
Proof.
  intros w c. unfold wrapped_offset. rewrite Z.sub_diag.
  apply Z.mod_0_l. apply modulus_nonzero.
Qed.

Lemma wrapped_offset_wrap : forall w c x,
  wrapped_offset w (wrap w c) (wrap w x) = wrapped_offset w c x.
Proof.
  intros w c x. unfold wrapped_offset, wrap. symmetry. apply Zminus_mod.
Qed.

Lemma wrapped_offset_word : forall w c x,
  wrapped_offset w c (wrap w x) = wrapped_offset w c x.
Proof.
  intros w c x. unfold wrapped_offset, wrap.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Lemma wrapped_offset_origin : forall w c x,
  wrapped_offset w (wrap w c) x = wrapped_offset w c x.
Proof.
  intros w c x. unfold wrapped_offset, wrap.
  rewrite Zminus_mod, Z.mod_mod by apply modulus_nonzero.
  symmetry. apply Zminus_mod.
Qed.

Lemma wrapped_offset_add : forall w c a x,
  wrapped_offset w c x =
  (wrapped_offset w c a + wrapped_offset w a x) mod modulus w.
Proof.
  intros w c a x. unfold wrapped_offset.
  replace (x - c) with ((a - c) + (x - a)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Lemma wrapped_offset_sub : forall w c a x,
  wrapped_offset w a x =
  (wrapped_offset w c x - wrapped_offset w c a) mod modulus w.
Proof.
  intros w c a x. unfold wrapped_offset.
  replace (x - a) with ((x - c) - (a - c)) by ring.
  apply Zminus_mod.
Qed.

Lemma wrapped_offset_step : forall w c k,
  0 <= k < modulus w -> wrapped_offset w c (wrap w (c + k)) = k.
Proof.
  intros w c k Hk. rewrite wrapped_offset_word.
  unfold wrapped_offset. replace (c + k - c) with k by ring.
  apply Z.mod_small. exact Hk.
Qed.

Lemma wrapped_gamma_word : forall w a z, wrapped_gamma w a z -> is_word w z.
Proof.
  intros w [| |lo hi] z Hz; cbn in Hz; tauto.
Qed.

Lemma wrapped_norm_gamma : forall w a z,
  wrapped_gamma w (wrapped_norm w a) z <-> wrapped_gamma w a z.
Proof.
  intros w [| |lo hi] z; cbn [wrapped_norm]; try tauto.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_gamma].
    pose proof (wrapped_offset_range w lo z) as Hrange.
    unfold wrapped_offset in Hfull, Hrange. split; [intro Hz; split; [exact Hz|lia]|tauto].
  - cbn [wrapped_gamma].
    change (is_word w z /\ wrapped_offset w (wrap w lo) z <=
      wrapped_offset w (wrap w lo) (wrap w hi) <->
      is_word w z /\ wrapped_offset w lo z <= wrapped_offset w lo hi).
    rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Lemma wrapped_norm_size : forall w a,
  wrapped_size w (wrapped_norm w a) = wrapped_size w a.
Proof.
  intros w [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. cbn [wrapped_size]. lia.
  - cbn [wrapped_size]. now rewrite wrapped_offset_wrap.
Qed.

Lemma wrapped_size_bounds : forall w a, 0 <= wrapped_size w a <= modulus w.
Proof.
  intros w [| |lo hi]; cbn [wrapped_size];
    pose proof (modulus_pos w); try lia.
  pose proof (wrapped_offset_range w lo hi). lia.
Qed.

(** Containment is tested by fitting the entire source span in the target's offset order. *)
Definition wrapped_leb (w : width) (a b : wrapped) : bool :=
  match a, b with
  | WBot, _ => true
  | _, WFull => true
  | _, WBot => false
  | WFull, WItv lo hi => wrapped_offset w lo hi =? modulus w - 1
  | WItv a b, WItv c d =>
    (wrapped_offset w c d =? modulus w - 1) ||
    (wrapped_offset w c a + wrapped_offset w a b <=? wrapped_offset w c d)
  end.

Lemma wrapped_arc_inclusion : forall w a b c d,
  (forall z, is_word w z -> wrapped_offset w a z <= wrapped_offset w a b ->
    wrapped_offset w c z <= wrapped_offset w c d) <->
  wrapped_offset w c d = modulus w - 1 \/
  wrapped_offset w c a + wrapped_offset w a b <= wrapped_offset w c d.
Proof.
  intros w a b c d.
  pose proof (wrapped_offset_range w a b) as Hab.
  pose proof (wrapped_offset_range w c d) as Hcd.
  pose proof (wrapped_offset_range w c a) as Hca.
  split.
  - intro Hincl. destruct (Z.eq_dec (wrapped_offset w c d) (modulus w - 1))
      as [Hfull|Hproper]; [now left|right].
    pose proof (Hincl (wrap w a) (wrap_is_word w a)) as Hstart.
    rewrite wrapped_offset_word, wrapped_offset_self in Hstart.
    specialize (Hstart ltac:(lia)).
    assert (Hsum : wrapped_offset w c a + wrapped_offset w a b < modulus w).
    { destruct (Z_lt_ge_dec (wrapped_offset w c a + wrapped_offset w a b)
        (modulus w)) as [Hlt|Hge]; [exact Hlt|].
      set (k := modulus w - 1 - wrapped_offset w c a).
      assert (Hk : 0 <= k < modulus w) by (unfold k; lia).
      specialize (Hincl (wrap w (a + k)) (wrap_is_word w (a + k))).
      rewrite wrapped_offset_step in Hincl by exact Hk.
      specialize (Hincl ltac:(unfold k; lia)).
      rewrite (wrapped_offset_add w c a), wrapped_offset_step in Hincl by exact Hk.
      replace (wrapped_offset w c a + k) with (modulus w - 1) in Hincl
        by (unfold k; ring).
      rewrite Z.mod_small in Hincl by lia. lia. }
    pose proof (Hincl (wrap w b) (wrap_is_word w b)) as Hend.
    rewrite !wrapped_offset_word in Hend. specialize (Hend ltac:(lia)).
    rewrite (wrapped_offset_add w c a b), Z.mod_small in Hend by lia. exact Hend.
  - intros [Hfull|Hsum] z Hz Haz.
    + pose proof (wrapped_offset_range w c z). lia.
    + pose proof (wrapped_offset_range w a z).
      rewrite (wrapped_offset_add w c a z), Z.mod_small; lia.
Qed.

Lemma wrapped_leb_spec : forall w a b,
  wrapped_leb w a b = true <->
  forall z, wrapped_gamma w a z -> wrapped_gamma w b z.
Proof.
  intros w [| |a b] [| |c d]; cbn [wrapped_leb wrapped_gamma];
    try (split; [intros; tauto|intros; reflexivity]).
  - split; [discriminate|intro Hempty].
    exfalso. exact (Hempty 0 (zero_is_word w)).
  - rewrite Z.eqb_eq. split.
    + intros Hfull z Hz. split; [exact Hz|].
      pose proof (wrapped_offset_range w c z). unfold wrapped_offset in *. lia.
    + intro Hall.
      specialize (Hall (wrap w (c + (modulus w - 1)))
        (wrap_is_word w (c + (modulus w - 1)))).
      destruct Hall as [_ Hlast].
      change (wrapped_offset w c (wrap w (c + (modulus w - 1))) <=
        wrapped_offset w c d) in Hlast.
      rewrite wrapped_offset_step in Hlast by (pose proof (modulus_pos w); lia).
      pose proof (wrapped_offset_range w c d). unfold wrapped_offset in *. lia.
  - split; [discriminate|intro Hempty].
    exfalso. apply (Hempty (wrap w a)). split; [apply wrap_is_word|].
    change (wrapped_offset w a (wrap w a) <= wrapped_offset w a b).
    rewrite wrapped_offset_word, wrapped_offset_self.
    pose proof (wrapped_offset_range w a b). lia.
  - rewrite Bool.orb_true_iff, Z.eqb_eq, Z.leb_le, <- wrapped_arc_inclusion.
    split.
    + intros Hincl z [Hz Haz]. split; [exact Hz|]. now apply Hincl.
    + intros Hincl z Hz Haz. apply (Hincl z). split; assumption.
Qed.

Lemma wrapped_leb_refl : forall w a, wrapped_leb w a a = true.
Proof.
  intros w a. apply wrapped_leb_spec. tauto.
Qed.

Lemma wrapped_leb_trans : forall w a b c,
  wrapped_leb w a b = true -> wrapped_leb w b c = true -> wrapped_leb w a c = true.
Proof.
  intros w a b c Hab Hbc. apply wrapped_leb_spec.
  pose proof (proj1 (wrapped_leb_spec w a b) Hab) as Hab_gamma.
  pose proof (proj1 (wrapped_leb_spec w b c) Hbc) as Hbc_gamma. auto.
Qed.

Lemma wrapped_norm_leb : forall w a,
  wrapped_leb w a (wrapped_norm w a) = true /\
  wrapped_leb w (wrapped_norm w a) a = true.
Proof.
  intros w a. split; apply wrapped_leb_spec; intros z Hz.
  - exact (proj2 (wrapped_norm_gamma w a z) Hz).
  - exact (proj1 (wrapped_norm_gamma w a z) Hz).
Qed.

(** * Covers and minimal joins *)

(** A candidate covers both inputs when both containment tests succeed. *)
Definition wrapped_cover (w : width) (a b candidate : wrapped) : bool :=
  wrapped_leb w a candidate && wrapped_leb w b candidate.

(** Among two covering candidates, choose the smaller, breaking ties toward the first. *)
Definition wrapped_choose (w : width) (a b first second : wrapped) : wrapped :=
  if wrapped_cover w a b first then
    if wrapped_cover w a b second then
      if wrapped_size w first <=? wrapped_size w second then first else second
    else first
  else if wrapped_cover w a b second then second else WFull.

(** The join uses the two endpoint covers after testing containment. *)
Definition wrapped_join (w : width) (a b : wrapped) : wrapped :=
  wrapped_norm w
    (if wrapped_leb w a b then b else
     if wrapped_leb w b a then a else
     match a, b with
     | WItv lo hi, WItv lo' hi' =>
       wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
     | _, _ => WFull
     end).

Lemma wrapped_size_monotone : forall w a b,
  wrapped_leb w a b = true -> wrapped_size w a <= wrapped_size w b.
Proof.
  intros w left right Hle.
  pose proof (wrapped_size_bounds w left) as Ha.
  pose proof (wrapped_size_bounds w right) as Hb.
  destruct left as [| |a b]; destruct right as [| |c d];
    cbn [wrapped_leb wrapped_size] in *; try discriminate;
    try (apply Z.eqb_eq in Hle); try lia.
  apply Bool.orb_true_iff in Hle. destruct Hle as [Hfull|Hspan].
  - apply Z.eqb_eq in Hfull. lia.
  - apply Z.leb_le in Hspan. pose proof (wrapped_offset_range w c a). lia.
Qed.

Lemma wrapped_choose_cover : forall w a b first second,
  wrapped_cover w a b (wrapped_choose w a b first second) = true.
Proof.
  intros w a b first second. unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second));
    try assumption.
  all: unfold wrapped_cover; destruct a, b; reflexivity.
Qed.

Lemma wrapped_choose_size : forall w a b first second target,
  (wrapped_cover w a b first = true /\ wrapped_size w first <= target) \/
  (wrapped_cover w a b second = true /\ wrapped_size w second <= target) ->
  wrapped_size w (wrapped_choose w a b first second) <= target.
Proof.
  intros w a b first second target Hcandidate. unfold wrapped_choose.
  destruct (wrapped_cover w a b first) eqn:Hfirst;
    destruct (wrapped_cover w a b second) eqn:Hsecond;
    try (destruct (wrapped_size w first <=? wrapped_size w second) eqn:Hsize);
    try (apply Z.leb_le in Hsize); try (apply Z.leb_gt in Hsize);
    destruct Hcandidate as [[Hcandidate Hbound]|[Hcandidate Hbound]];
    try discriminate; lia.
Qed.

Lemma wrapped_join_cover : forall w a b,
  wrapped_cover w a b (wrapped_join w a b) = true.
Proof.
  intros w a b. unfold wrapped_cover. apply Bool.andb_true_iff.
  unfold wrapped_join.
  destruct (wrapped_leb w a b) eqn:Hab.
  - split.
    + eapply wrapped_leb_trans; [exact Hab|apply wrapped_norm_leb].
    + apply wrapped_norm_leb.
  - destruct (wrapped_leb w b a) eqn:Hba.
    + split.
      * apply wrapped_norm_leb.
      * eapply wrapped_leb_trans; [exact Hba|apply wrapped_norm_leb].
    + assert (Hcover : wrapped_cover w a b
        (match a, b with
         | WItv lo hi, WItv lo' hi' =>
           wrapped_choose w a b (WItv lo hi') (WItv lo' hi)
         | _, _ => WFull
         end) = true).
      { destruct a, b; try reflexivity. apply wrapped_choose_cover. }
      apply Bool.andb_true_iff in Hcover. destruct Hcover as [Hleft Hright].
      split; eapply wrapped_leb_trans; try eassumption; apply wrapped_norm_leb.
Qed.

Lemma wrapped_offset_linear : forall w c a x,
  wrapped_offset w c a + wrapped_offset w a x < modulus w ->
  wrapped_offset w c x = wrapped_offset w c a + wrapped_offset w a x.
Proof.
  intros w c a x Hbound. rewrite (wrapped_offset_add w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w a x). lia.
Qed.

Lemma wrapped_offset_difference : forall w c a x,
  wrapped_offset w c a <= wrapped_offset w c x ->
  wrapped_offset w a x = wrapped_offset w c x - wrapped_offset w c a.
Proof.
  intros w c a x Hle. rewrite (wrapped_offset_sub w c a x).
  apply Z.mod_small. pose proof (wrapped_offset_range w c a).
  pose proof (wrapped_offset_range w c x). lia.
Qed.

Lemma wrapped_candidate_size : forall w a b c d e f,
  wrapped_offset w e a + wrapped_offset w a b <= wrapped_offset w e f ->
  wrapped_offset w e c + wrapped_offset w c d <= wrapped_offset w e f ->
  wrapped_offset w e a <= wrapped_offset w e c ->
  wrapped_offset w e a + wrapped_offset w a b <=
    wrapped_offset w e c + wrapped_offset w c d ->
  wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
  wrapped_size w (WItv a d) <= wrapped_size w (WItv e f).
Proof.
  intros w a b c d e f Hab Hcd Hstart Hend.
  pose proof (wrapped_offset_range w e f) as Hspan.
  pose proof (wrapped_offset_range w e a) as Ha.
  pose proof (wrapped_offset_range w e c) as Hc.
  pose proof (wrapped_offset_range w c d) as Hcd_range.
  assert (Hd : wrapped_offset w e d = wrapped_offset w e c + wrapped_offset w c d).
  { apply wrapped_offset_linear. lia. }
  assert (Had : wrapped_offset w a d =
      wrapped_offset w e c + wrapped_offset w c d - wrapped_offset w e a).
  { rewrite (wrapped_offset_difference w e a d) by lia. lia. }
  assert (Hac : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a).
  { apply wrapped_offset_difference. exact Hstart. }
  split.
  - unfold wrapped_cover. apply Bool.andb_true_iff. split;
      cbn [wrapped_leb]; apply Bool.orb_true_iff; right; apply Z.leb_le.
    + rewrite wrapped_offset_self, Had. lia.
    + rewrite Hac, Had. lia.
  - cbn [wrapped_size]. rewrite Had. lia.
Qed.

Lemma wrapped_candidate_exists : forall w a b c d e f,
  wrapped_offset w e f <> modulus w - 1 ->
  wrapped_leb w (WItv a b) (WItv e f) = true ->
  wrapped_leb w (WItv c d) (WItv e f) = true ->
  wrapped_leb w (WItv a b) (WItv c d) = false ->
  wrapped_leb w (WItv c d) (WItv a b) = false ->
  (wrapped_cover w (WItv a b) (WItv c d) (WItv a d) = true /\
   wrapped_size w (WItv a d) <= wrapped_size w (WItv e f)) \/
  (wrapped_cover w (WItv a b) (WItv c d) (WItv c b) = true /\
   wrapped_size w (WItv c b) <= wrapped_size w (WItv e f)).
Proof.
  intros w a b c d e f Hproper Hac Hbc Hab Hba.
  cbn [wrapped_leb] in Hac, Hbc.
  destruct (wrapped_offset w e f =? modulus w - 1) eqn:Hfull.
  - apply Z.eqb_eq in Hfull. contradiction.
  - cbn in Hac, Hbc. apply Z.leb_le in Hac, Hbc.
    destruct (Z_le_gt_dec (wrapped_offset w e a) (wrapped_offset w e c))
      as [Hstart|Hstart].
    + left. apply wrapped_candidate_size; try assumption.
      destruct (Z_le_gt_dec (wrapped_offset w e a + wrapped_offset w a b)
        (wrapped_offset w e c + wrapped_offset w c d)) as [Hend|Hend]; [exact Hend|].
      assert (Hca : wrapped_offset w a c = wrapped_offset w e c - wrapped_offset w e a)
        by (apply wrapped_offset_difference; exact Hstart).
      assert (Hcontra : wrapped_leb w (WItv c d) (WItv a b) = true).
      { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
      congruence.
    + right.
      assert (Hend : wrapped_offset w e c + wrapped_offset w c d <=
          wrapped_offset w e a + wrapped_offset w a b).
      { destruct (Z_le_gt_dec (wrapped_offset w e c + wrapped_offset w c d)
          (wrapped_offset w e a + wrapped_offset w a b)) as [Hend|Hend]; [exact Hend|].
        assert (Hac' : wrapped_offset w c a = wrapped_offset w e a - wrapped_offset w e c)
          by (apply wrapped_offset_difference; lia).
        assert (Hcontra : wrapped_leb w (WItv a b) (WItv c d) = true).
        { cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le. lia. }
        congruence. }
      destruct (wrapped_candidate_size w c d a b e f Hbc Hac ltac:(lia) Hend)
        as [Hcover Hsize]. split; [|exact Hsize].
      unfold wrapped_cover in *. now rewrite Bool.andb_comm.
Qed.

Lemma wrapped_join_size : forall w a b c,
  wrapped_leb w a c = true -> wrapped_leb w b c = true ->
  wrapped_size w (wrapped_join w a b) <= wrapped_size w c.
Proof.
  intros w left right target Hac Hbc. unfold wrapped_join. rewrite wrapped_norm_size.
  destruct (wrapped_leb w left right) eqn:Hab.
  - now apply wrapped_size_monotone.
  - destruct (wrapped_leb w right left) eqn:Hba.
    + now apply wrapped_size_monotone.
    + destruct left as [| |a b]; destruct right as [| |c d];
        cbn [wrapped_leb] in Hab, Hba; try discriminate.
      destruct target as [| |e f].
      * discriminate.
      * apply wrapped_size_bounds.
      * destruct (Z.eq_dec (wrapped_offset w e f) (modulus w - 1)) as [Hfull|Hproper].
        -- pose proof (wrapped_size_bounds w
             (wrapped_choose w (WItv a b) (WItv c d) (WItv a d) (WItv c b))).
           cbn [wrapped_size]. lia.
        -- apply wrapped_choose_size.
           exact (wrapped_candidate_exists w a b c d e f Hproper Hac Hbc Hab Hba).
Qed.

(** * Doubling widening *)

(** Doubling extends an arc by its size at each end, or saturates to the full circle. *)
Definition wrapped_double (w : width) (a : wrapped) : wrapped :=
  match a with
  | WBot => WBot
  | WFull => WFull
  | WItv lo hi =>
    let size := wrapped_size w a in
    if modulus w <=? 3 * size then WFull
    else wrapped_norm w (WItv (lo - size) (hi + size))
  end.

(** Widening retains a containing old value, otherwise it joins an expanded old arc. *)
Definition wrapped_widen (w : width) (a b : wrapped) : wrapped :=
  if wrapped_leb w b a then wrapped_norm w a
  else wrapped_join w (wrapped_double w a) b.

(** Narrowing replaces the full circle and otherwise retains the old arc. *)
Definition wrapped_narrow (w : width) (a b : wrapped) : wrapped :=
  match wrapped_norm w a with
  | WFull => wrapped_norm w b
  | _ => wrapped_norm w a
  end.

Lemma wrapped_expand_span : forall w lo hi size,
  wrapped_offset w (lo - size) (hi + size) =
  (wrapped_offset w lo hi + 2 * size) mod modulus w.
Proof.
  intros w lo hi size. unfold wrapped_offset.
  replace (hi + size - (lo - size)) with ((hi - lo) + 2 * size) by ring.
  symmetry. apply Z.add_mod_idemp_l. apply modulus_nonzero.
Qed.

Lemma wrapped_expand_size : forall w lo hi,
  let size := wrapped_size w (WItv lo hi) in
  3 * size < modulus w ->
  wrapped_size w (WItv (lo - size) (hi + size)) = 3 * size.
Proof.
  intros w lo hi size Hbound. cbn [wrapped_size]. rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi). unfold size, wrapped_size in *.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma wrapped_double_upper : forall w a, wrapped_leb w a (wrapped_double w a) = true.
Proof.
  intros w [| |lo hi]; cbn [wrapped_double]; try reflexivity.
  set (size := wrapped_size w (WItv lo hi)).
  destruct (modulus w <=? 3 * size) eqn:Hfull; [reflexivity|].
  apply Z.leb_gt in Hfull.
  eapply (wrapped_leb_trans w _ (WItv (lo - size) (hi + size))).
  2: exact (proj1 (wrapped_norm_leb w (WItv (lo - size) (hi + size)))).
  cbn [wrapped_leb]. apply Bool.orb_true_iff. right. apply Z.leb_le.
  rewrite wrapped_expand_span.
  pose proof (wrapped_offset_range w lo hi) as Hspan.
  assert (Hsize : size = wrapped_offset w lo hi + 1) by reflexivity.
  assert (Hstart : wrapped_offset w (lo - size) lo = size).
  { unfold wrapped_offset. replace (lo - (lo - size)) with size by ring.
    apply Z.mod_small. lia. }
  rewrite Hstart, Z.mod_small by lia. lia.
Qed.

Lemma wrapped_double_size : forall w a,
  wrapped_size w (wrapped_double w a) =
  Z.min (modulus w) (3 * wrapped_size w a).
Proof.
  intros w [| |lo hi]; cbn [wrapped_double].
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - cbn [wrapped_size]. pose proof (modulus_pos w). lia.
  - destruct (modulus w <=? 3 * wrapped_size w (WItv lo hi)) eqn:Hfull.
    + apply Z.leb_le in Hfull. cbn [wrapped_size] in *. lia.
    + apply Z.leb_gt in Hfull. rewrite wrapped_norm_size, wrapped_expand_size by exact Hfull.
      lia.
Qed.

(** The lattice uses semantic arc containment, candidate-cover join and doubling widening. *)
Definition wrapped_lattice (w : width) : lattice wrapped :=
  {| leb := wrapped_leb w;
     bot := WBot;
     join := wrapped_join w;
     widen := wrapped_widen w;
     narrow := wrapped_narrow w |}.

(** Circular intervals satisfy the weak lattice laws, including both widening upper bounds. *)
Theorem wrapped_laws : forall w, lattice_laws (wrapped_lattice w).
Proof.
  intro w. constructor; cbn.
  - apply wrapped_leb_refl.
  - apply wrapped_leb_trans.
  - intro a. reflexivity.
  - intros a b. exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  - intros a b. apply (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w a b))).
  - intros a b. unfold wrapped_widen. destruct (wrapped_leb w b a) eqn:Hba.
    + apply wrapped_norm_leb.
    + eapply wrapped_leb_trans; [apply wrapped_double_upper|].
      exact (proj1 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  - intros a b. unfold wrapped_widen. destruct (wrapped_leb w b a) eqn:Hba.
    + eapply wrapped_leb_trans; [exact Hba|apply wrapped_norm_leb].
    + exact (proj2 (proj1 (Bool.andb_true_iff _ _) (wrapped_join_cover w _ b))).
  - intros a b Hba. unfold wrapped_narrow.
    destruct (wrapped_norm w a) eqn:Ha.
    + reflexivity.
    + eapply wrapped_leb_trans; [exact (proj2 (wrapped_norm_leb w b))|exact Hba].
    + rewrite <- Ha. exact (proj2 (wrapped_norm_leb w a)).
  - intros a b Hba. unfold wrapped_narrow.
    destruct (wrapped_norm w a) eqn:Ha.
    + rewrite <- Ha. eapply wrapped_leb_trans; [exact Hba|].
      exact (proj1 (wrapped_norm_leb w a)).
    + exact (proj1 (wrapped_norm_leb w b)).
    + rewrite <- Ha. eapply wrapped_leb_trans; [exact Hba|].
      exact (proj1 (wrapped_norm_leb w a)).
Qed.

(** Candidate-cover join has minimum cardinality among all circular upper bounds. *)
Theorem wrapped_join_minimal : forall w a b c,
  leb (wrapped_lattice w) a c = true -> leb (wrapped_lattice w) b c = true ->
  wrapped_size w (join (wrapped_lattice w) a b) <= wrapped_size w c.
Proof.
  apply wrapped_join_size.
Qed.

(** Arc concretisation is monotone in the circular containment order. *)
Theorem wrapped_gamma_laws : forall w,
  concretisation_laws (wrapped_lattice w) (Concretisation wrapped Z (wrapped_gamma w)).
Proof.
  intro w. constructor. intros a b z Hle Hz. exact (proj1 (wrapped_leb_spec w a b) Hle z Hz).
Qed.

(** The integer rank distinguishes bottom, proper arcs and the canonical full circle. *)
Definition wrapped_size_rank (w : width) (size : Z) : Z :=
  if size =? 0 then Zpos w + 2 else
  if size =? modulus w then 0 else Zpos w + 1 - Z.log2 size.

Lemma wrapped_size_rank_bounds : forall w size,
  0 <= size <= modulus w -> 0 <= wrapped_size_rank w size <= Zpos w + 2.
Proof.
  intros w size Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [lia|].
  pose proof (Z.log2_nonneg size) as Hnonneg.
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  unfold modulus in Hlog. rewrite Z.log2_pow2 in Hlog by lia. lia.
Qed.

Lemma wrapped_size_rank_positive : forall w size,
  0 <= size < modulus w -> 0 < wrapped_size_rank w size.
Proof.
  intros w size Hsize. unfold wrapped_size_rank.
  destruct (size =? 0) eqn:Hzero; [lia|].
  destruct (size =? modulus w) eqn:Hfull; [apply Z.eqb_eq in Hfull; lia|].
  pose proof (Z.log2_le_mono size (modulus w) ltac:(lia)) as Hlog.
  unfold modulus in Hlog. rewrite Z.log2_pow2 in Hlog by lia. lia.
Qed.

Lemma wrapped_size_rank_progress : forall w old next,
  0 <= old < modulus w -> 0 < next <= modulus w ->
  Z.min (modulus w) (3 * old) <= next ->
  wrapped_size_rank w next < wrapped_size_rank w old.
Proof.
  intros w old next Hold Hnext Hgrow.
  pose proof (wrapped_size_rank_positive w old Hold) as Hpositive.
  unfold wrapped_size_rank.
  destruct (next =? 0) eqn:Hnext_zero; [apply Z.eqb_eq in Hnext_zero; lia|].
  destruct (next =? modulus w) eqn:Hnext_full.
  - unfold wrapped_size_rank in Hpositive. exact Hpositive.
  - apply Z.eqb_neq in Hnext_full.
    destruct (old =? 0) eqn:Hold_zero.
    + pose proof (Z.log2_nonneg next). lia.
    + apply Z.eqb_neq in Hold_zero.
      destruct (old =? modulus w) eqn:Hold_full; [apply Z.eqb_eq in Hold_full; lia|].
      assert (Hdouble : 2 * old <= next) by lia.
      pose proof (Z.log2_le_mono (2 * old) next Hdouble) as Hlog.
      rewrite Z.log2_double in Hlog by lia. lia.
Qed.

Lemma wrapped_size_zero : forall w a, wrapped_size w a = 0 <-> a = WBot.
Proof.
  intros w [| |lo hi]; cbn [wrapped_size].
  - tauto.
  - pose proof (modulus_pos w). split; [lia|discriminate].
  - pose proof (wrapped_offset_range w lo hi). split; [lia|discriminate].
Qed.

Lemma wrapped_full_contains : forall w a b,
  wrapped_size w a = modulus w -> wrapped_leb w b a = true.
Proof.
  intros w a b Hsize. apply wrapped_leb_spec. intros z Hz.
  pose proof (wrapped_gamma_word w b z Hz) as Hword.
  destruct a as [| |lo hi]; cbn [wrapped_size wrapped_gamma] in *.
  - pose proof (modulus_pos w). lia.
  - exact Hword.
  - split; [exact Hword|]. pose proof (wrapped_offset_range w lo z).
    unfold wrapped_offset in *. lia.
Qed.

Lemma wrapped_widen_size_progress : forall w a b,
  wrapped_leb w b a = false ->
  0 < wrapped_size w (wrapped_widen w a b) <= modulus w /\
  Z.min (modulus w) (3 * wrapped_size w a) <= wrapped_size w (wrapped_widen w a b).
Proof.
  intros w a b Hescape. unfold wrapped_widen. rewrite Hescape.
  pose proof (wrapped_join_cover w (wrapped_double w a) b) as Hcover.
  apply Bool.andb_true_iff in Hcover. destruct Hcover as [Hleft Hright].
  pose proof (wrapped_size_monotone w _ _ Hleft) as Hsize.
  rewrite wrapped_double_size in Hsize.
  pose proof (wrapped_size_bounds w (wrapped_join w (wrapped_double w a) b)) as Hbounds.
  split; [split; [|lia]|exact Hsize].
  destruct (Z.eq_dec (wrapped_size w (wrapped_join w (wrapped_double w a) b)) 0)
    as [Hzero|Hnonzero]; [|lia].
  apply wrapped_size_zero in Hzero.
  rewrite Hzero in Hright.
  destruct b; cbn [wrapped_leb] in Hright; try discriminate.
Qed.

(** The bounded rank drops whenever the next value escapes the old arc. *)
Definition wrapped_wrank (w : width) : bounded_widening_rank (wrapped_lattice w).
Proof.
  unshelve refine (@BoundedWideningRank wrapped (wrapped_lattice w)
    (@WideningRank wrapped (wrapped_lattice w)
      (fun a => Z.to_nat (wrapped_size_rank w (wrapped_size w a))) _ _)
    (Z.to_nat (Zpos w + 2)) _).
  - intros a b Hba. cbn in Hba. change
      (Z.to_nat (wrapped_size_rank w (wrapped_size w (wrapped_widen w a b))) <=
       Z.to_nat (wrapped_size_rank w (wrapped_size w a)))%nat.
    unfold wrapped_widen. rewrite Hba, wrapped_norm_size. lia.
  - intros a b Hba. cbn in Hba. change
      (Z.to_nat (wrapped_size_rank w (wrapped_size w (wrapped_widen w a b))) <
       Z.to_nat (wrapped_size_rank w (wrapped_size w a)))%nat.
    pose proof (wrapped_size_bounds w a) as Ha.
    assert (Hproper : wrapped_size w a < modulus w).
    { destruct (Z.eq_dec (wrapped_size w a) (modulus w)) as [Hfull|Hproper]; [|lia].
      pose proof (wrapped_full_contains w a b Hfull). congruence. }
    destruct (wrapped_widen_size_progress w a b Hba) as [Hnext Hgrow].
    pose proof (wrapped_size_rank_progress w (wrapped_size w a)
      (wrapped_size w (wrapped_widen w a b)) ltac:(lia) Hnext Hgrow) as Hrank.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w a) Ha) as Hrank_old.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w (wrapped_widen w a b))
      ltac:(lia)) as Hrank_next.
    apply Z2Nat.inj_lt; lia.
  - intro a. change
      (Z.to_nat (wrapped_size_rank w (wrapped_size w a)) <= Z.to_nat (Zpos w + 2))%nat.
    pose proof (wrapped_size_rank_bounds w (wrapped_size w a) (wrapped_size_bounds w a)).
    apply Z2Nat.inj_le; lia.
Defined.

(** * Linear pieces and intersections *)

(** A linear mathematical range is projected onto the circle, saturating when it covers it. *)
Definition wrapped_range (w : width) (lo hi : Z) : wrapped :=
  if hi <? lo then WBot else
  if modulus w - 1 <=? hi - lo then WFull else wrapped_norm w (WItv lo hi).

Lemma wrapped_range_sound : forall w lo hi z,
  lo <= z <= hi -> wrapped_gamma w (wrapped_range w lo hi) (wrap w z).
Proof.
  intros w lo hi z Hz. unfold wrapped_range.
  destruct (hi <? lo) eqn:Hempty; [apply Z.ltb_lt in Hempty; lia|].
  destruct (modulus w - 1 <=? hi - lo) eqn:Hfull; [apply wrap_is_word|].
  apply Z.leb_gt in Hfull. apply (proj2 (wrapped_norm_gamma w (WItv lo hi) _)).
  split; [apply wrap_is_word|].
  change (wrapped_offset w lo (wrap w z) <= wrapped_offset w lo hi).
  rewrite wrapped_offset_word. unfold wrapped_offset.
  rewrite !Z.mod_small by lia. lia.
Qed.

(** Interval bounds become a circular range; unbounded intervals conservatively give the circle. *)
Definition wrapped_of_interval (w : width) (i : interval) : wrapped :=
  match i with
  | IBot => WBot
  | Itv (Fin lo) (Fin hi) => wrapped_range w lo hi
  | _ => WFull
  end.

Lemma wrapped_of_interval_sound : forall w i z,
  gamma interval_gamma i z -> wrapped_gamma w (wrapped_of_interval w i) (wrap w z).
Proof.
  intros w [|lo hi] z Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|]; cbn [wrapped_of_interval];
    try apply wrap_is_word.
  cbn [interval_gamma gamma bound_leb] in Hz.
  destruct Hz as [Hlo Hhi]. apply Z.leb_le in Hlo, Hhi.
  apply wrapped_range_sound. lia.
Qed.

Lemma wrapped_interval_value_sound : forall w i z,
  interval_pgamma w i z -> wrapped_gamma w (wrapped_of_interval w i) z.
Proof.
  intros w i z [Hword Hz]. rewrite <- (wrap_id w z Hword).
  now apply wrapped_of_interval_sound.
Qed.

(** The raw cut reads endpoints modulo the width; callers normalize full circles first. *)
Definition wrapped_parts_raw (w : width) (a : wrapped) : interval * interval :=
  match a with
  | WBot => (IBot, IBot)
  | WFull => (interval_top w, IBot)
  | WItv lo hi =>
    let lo' := wrap w lo in
    let hi' := wrap w hi in
    if lo' <=? hi' then (Itv (Fin lo') (Fin hi'), IBot)
    else (Itv (Fin lo') (Fin (modulus w - 1)), Itv (Fin 0) (Fin hi'))
  end.

(** Cutting a canonical arc at zero gives up to two nonempty unsigned pieces. *)
Definition wrapped_parts (w : width) (a : wrapped) : interval * interval :=
  wrapped_parts_raw w (wrapped_norm w a).

Lemma wrapped_offset_word_cases : forall w c z,
  is_word w c -> is_word w z ->
  wrapped_offset w c z = if c <=? z then z - c else z - c + modulus w.
Proof.
  intros w c z Hc Hz. unfold wrapped_offset.
  destruct (c <=? z) eqn:Hle.
  - apply Z.leb_le in Hle. apply Z.mod_small. unfold is_word in *. lia.
  - apply Z.leb_gt in Hle. symmetry. apply Z.mod_unique with (q := -1);
      unfold is_word in *; lia.
Qed.

Lemma wrapped_arc_normalize_gamma : forall w lo hi z,
  wrapped_gamma w (WItv lo hi) z <->
  wrapped_gamma w (WItv (wrap w lo) (wrap w hi)) z.
Proof.
  intros w lo hi z. cbn [wrapped_gamma]. change
    (is_word w z /\ wrapped_offset w lo z <= wrapped_offset w lo hi <->
     is_word w z /\ wrapped_offset w (wrap w lo) z <=
       wrapped_offset w (wrap w lo) (wrap w hi)).
  rewrite wrapped_offset_origin, wrapped_offset_wrap. reflexivity.
Qed.

Lemma wrapped_parts_raw_spec : forall w a z,
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts_raw w a)) z \/
  interval_pgamma w (snd (wrapped_parts_raw w a)) z.
Proof.
  intros w [| |lo hi] z.
  - change (False <-> (is_word w z /\ False) \/ (is_word w z /\ False)). tauto.
  - cbn [wrapped_gamma wrapped_parts_raw fst snd interval_pgamma interval_gamma gamma].
    split; [intro Hz; left; now apply interval_top_sound|].
    intros [[Hz _]|[_ Hempty]]; [exact Hz|contradiction].
  - rewrite wrapped_arc_normalize_gamma. cbn [wrapped_parts_raw fst snd].
    pose proof (wrap_is_word w lo) as Hlo.
    pose proof (wrap_is_word w hi) as Hhi.
    destruct (wrap w lo <=? wrap w hi) eqn:Hends;
      cbn [fst snd wrapped_gamma]; unfold interval_pgamma, interval_gamma;
      cbn [gamma bound_leb];
      rewrite !Z.leb_le; split.
    + intros [Hz Hoffset]. left. split; [exact Hz|].
      change (wrapped_offset w (wrap w lo) z <= wrapped_offset w (wrap w lo) (wrap w hi))
        in Hoffset.
      rewrite !wrapped_offset_word_cases in Hoffset by assumption.
      rewrite Hends in Hoffset. apply Z.leb_le in Hends.
      destruct (wrap w lo <=? z) eqn:Hzlo; [apply Z.leb_le in Hzlo|apply Z.leb_gt in Hzlo];
        unfold is_word in *; lia.
    + intros [[Hz [Hzlo Hzhi]]|[_ Hempty]]; [|contradiction].
      split; [exact Hz|].
      change (wrapped_offset w (wrap w lo) z <= wrapped_offset w (wrap w lo) (wrap w hi)).
      rewrite !wrapped_offset_word_cases by assumption. rewrite Hends.
      assert (Hlower : (wrap w lo <=? z) = true) by (apply Z.leb_le; exact Hzlo).
      rewrite Hlower. lia.
    + intros [Hz Hoffset].
      change (wrapped_offset w (wrap w lo) z <= wrapped_offset w (wrap w lo) (wrap w hi))
        in Hoffset.
      rewrite !wrapped_offset_word_cases in Hoffset by assumption. rewrite Hends in Hoffset.
      destruct (wrap w lo <=? z) eqn:Hzlo.
      * apply Z.leb_le in Hzlo. left. split; [exact Hz|]. unfold is_word in Hz. lia.
      * apply Z.leb_gt in Hzlo. right. split; [exact Hz|]. unfold is_word in Hz. lia.
    + intros [[Hz [Hzlo Hzhi]]|[Hz [Hzlo Hzhi]]]; split; try exact Hz;
        change (wrapped_offset w (wrap w lo) z <= wrapped_offset w (wrap w lo) (wrap w hi));
        rewrite !wrapped_offset_word_cases by assumption; rewrite Hends;
        destruct (wrap w lo <=? z) eqn:Hzlo';
        try (apply Z.leb_le in Hzlo'); try (apply Z.leb_gt in Hzlo');
        unfold is_word in *; apply Z.leb_gt in Hends; lia.
Qed.

Lemma wrapped_parts_spec : forall w a z,
  wrapped_gamma w a z <->
  interval_pgamma w (fst (wrapped_parts w a)) z \/
  interval_pgamma w (snd (wrapped_parts w a)) z.
Proof.
  intros w a z. unfold wrapped_parts. rewrite <- wrapped_parts_raw_spec.
  symmetry. apply wrapped_norm_gamma.
Qed.

Lemma wrapped_norm_idempotent : forall w a,
  wrapped_norm w (wrapped_norm w a) = wrapped_norm w a.
Proof.
  intros w [| |lo hi]; cbn [wrapped_norm]; try reflexivity.
  destruct (wrapped_offset w lo hi =? modulus w - 1) eqn:Hfull; [reflexivity|].
  cbn [wrapped_norm]. rewrite wrapped_offset_wrap, Hfull, !wrap_wrap. reflexivity.
Qed.

Lemma wrapped_parts_normalized : forall w a,
  wrapped_parts w (wrapped_norm w a) = wrapped_parts w a.
Proof.
  intros w a. unfold wrapped_parts. now rewrite wrapped_norm_idempotent.
Qed.

(** Four-way joins combine the fixed number of cases introduced by cutting two arcs. *)
Definition wrapped_join_four (w : width) (a b c d : wrapped) : wrapped :=
  wrapped_join w (wrapped_join w a b) (wrapped_join w c d).

Lemma wrapped_join_sound : forall w a b z,
  wrapped_gamma w a z \/ wrapped_gamma w b z -> wrapped_gamma w (wrapped_join w a b) z.
Proof.
  intros w a b z [Ha|Hb].
  - exact (gamma_monotone (wrapped_gamma_laws w) a _ z
      (join_upper_l (wrapped_laws w) a b) Ha).
  - exact (gamma_monotone (wrapped_gamma_laws w) b _ z
      (join_upper_r (wrapped_laws w) a b) Hb).
Qed.

Lemma wrapped_join_four_sound : forall w a b c d z,
  wrapped_gamma w a z \/ wrapped_gamma w b z \/
  wrapped_gamma w c z \/ wrapped_gamma w d z ->
  wrapped_gamma w (wrapped_join_four w a b c d) z.
Proof.
  intros w a b c d z Hcases. unfold wrapped_join_four.
  apply wrapped_join_sound. destruct Hcases as [Ha|[Hb|[Hc|Hd]]].
  - left. apply wrapped_join_sound. now left.
  - left. apply wrapped_join_sound. now right.
  - right. apply wrapped_join_sound. now left.
  - right. apply wrapped_join_sound. now right.
Qed.

(** Four linear intersections cover the meet, and a guard preserves the left bound. *)
Definition wrapped_meet (w : width) (a b : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pb := wrapped_parts w b in
  let candidate := wrapped_join_four w
    (wrapped_of_interval w (interval_meet (fst pa) (fst pb)))
    (wrapped_of_interval w (interval_meet (fst pa) (snd pb)))
    (wrapped_of_interval w (interval_meet (snd pa) (fst pb)))
    (wrapped_of_interval w (interval_meet (snd pa) (snd pb))) in
  if wrapped_leb w candidate a then candidate else wrapped_norm w a.

Lemma wrapped_meet_sound : forall w a b z,
  wrapped_gamma w a z -> wrapped_gamma w b z -> wrapped_gamma w (wrapped_meet w a b) z.
Proof.
  intros w a b z Ha Hb. unfold wrapped_meet.
  destruct (wrapped_leb w _ a) eqn:Hleft.
  - apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
    pose proof (wrapped_gamma_word w a z) as Hword.
    assert (Hz : is_word w z).
    { destruct Ha as [[Hz _]|[Hz _]]; exact Hz. }
    rewrite <- (wrap_id w z Hz). apply wrapped_join_four_sound.
    destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
    + left. apply wrapped_of_interval_sound. eapply interval_meet_sound; eassumption.
    + right; left. apply wrapped_of_interval_sound. eapply interval_meet_sound; eassumption.
    + right; right; left. apply wrapped_of_interval_sound. eapply interval_meet_sound; eassumption.
    + right; right; right. apply wrapped_of_interval_sound. eapply interval_meet_sound; eassumption.
  - exact (proj2 (wrapped_norm_gamma w a z) Ha).
Qed.

Lemma wrapped_meet_lower_left : forall w a b, wrapped_leb w (wrapped_meet w a b) a = true.
Proof.
  intros w a b. unfold wrapped_meet.
  match goal with
  | |- context [if ?test then _ else _] => destruct test eqn:Hleft
  end.
  - exact Hleft.
  - exact (proj2 (wrapped_norm_leb w a)).
Qed.

(** * Modular arithmetic transfers *)

(** Addition adds the two endpoint pairs unless their combined spans cover the circle. *)
Definition wrapped_add (w : width) (a b : wrapped) : wrapped :=
  match a, b with
  | WBot, _ | _, WBot => WBot
  | WItv lo hi, WItv lo' hi' =>
    if modulus w <? wrapped_size w a + wrapped_size w b then WFull
    else wrapped_norm w (WItv (lo + lo') (hi + hi'))
  | _, _ => WFull
  end.

(** Negation reverses the endpoint order around zero. *)
Definition wrapped_neg (w : width) (a : wrapped) : wrapped :=
  match a with
  | WItv lo hi => wrapped_norm w (WItv (- hi) (- lo))
  | _ => a
  end.

(** Subtraction is addition of the reversed arc. *)
Definition wrapped_sub (w : width) (a b : wrapped) : wrapped :=
  wrapped_add w a (wrapped_neg w b).

Lemma wrapped_offset_sum : forall w a b x y,
  wrapped_offset w (a + b) (x + y) =
  (wrapped_offset w a x + wrapped_offset w b y) mod modulus w.
Proof.
  intros w a b x y. unfold wrapped_offset.
  replace (x + y - (a + b)) with ((x - a) + (y - b)) by ring.
  apply Z.add_mod. apply modulus_nonzero.
Qed.

Lemma wrapped_offset_neg : forall w a b,
  wrapped_offset w (- b) (- a) = wrapped_offset w a b.
Proof.
  intros w a b. unfold wrapped_offset. f_equal. ring.
Qed.

Lemma wrapped_add_sound : forall w a b x y,
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_add w a b) (wrap w (x + y)).
Proof.
  intros w [| |lo hi] [| |lo' hi'] x y Hx Hy;
    cbn [wrapped_add] in *; try contradiction; try apply wrap_is_word.
  destruct (modulus w <? wrapped_size w (WItv lo hi) + wrapped_size w (WItv lo' hi'))
    eqn:Hfull; [apply wrap_is_word|].
  apply Z.ltb_ge in Hfull.
  apply (proj2 (wrapped_norm_gamma w (WItv (lo + lo') (hi + hi')) _)).
  destruct Hx as [Hx Hoffsetx], Hy as [Hy Hoffsety].
  split; [apply wrap_is_word|].
  change (wrapped_offset w (lo + lo') (wrap w (x + y)) <=
    wrapped_offset w (lo + lo') (hi + hi')).
  rewrite wrapped_offset_word, !wrapped_offset_sum.
  pose proof (wrapped_offset_range w lo x).
  pose proof (wrapped_offset_range w lo' y).
  cbn [wrapped_size] in Hfull. unfold wrapped_offset in Hoffsetx, Hoffsety.
  change (wrapped_offset w lo x <= wrapped_offset w lo hi) in Hoffsetx.
  change (wrapped_offset w lo' y <= wrapped_offset w lo' hi') in Hoffsety.
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma wrapped_neg_sound : forall w a x,
  wrapped_gamma w a x -> wrapped_gamma w (wrapped_neg w a) (wrap w (- x)).
Proof.
  intros w [| |lo hi] x Hx; cbn [wrapped_neg] in *;
    try contradiction; try apply wrap_is_word.
  apply (proj2 (wrapped_norm_gamma w (WItv (- hi) (- lo)) _)).
  destruct Hx as [Hx Hoffset]. split; [apply wrap_is_word|].
  change (wrapped_offset w (- hi) (wrap w (- x)) <= wrapped_offset w (- hi) (- lo)).
  rewrite wrapped_offset_word, !wrapped_offset_neg.
  change (wrapped_offset w lo x <= wrapped_offset w lo hi) in Hoffset.
  rewrite (wrapped_offset_difference w lo x hi) by exact Hoffset.
  pose proof (wrapped_offset_range w lo x). lia.
Qed.

Lemma wrapped_sub_sound : forall w a b x y,
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_sub w a b) (wrap w (x - y)).
Proof.
  intros w a b x y Hx Hy. unfold wrapped_sub.
  replace (wrap w (x - y)) with (wrap w (x + wrap w (- y))).
  - apply wrapped_add_sound; [exact Hx|now apply wrapped_neg_sound].
  - replace (x - y) with (x + - y) by ring.
    rewrite (wrap_add w x (- y)), (wrap_add w x (wrap w (- y))), wrap_wrap. reflexivity.
Qed.

(** A piece product uses all four corners of its integer rectangle. *)
Definition wrapped_mul_piece (w : width) (a b : interval) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | Itv (Fin lo) (Fin hi), Itv (Fin lo') (Fin hi') =>
    wrapped_range w
      (Z.min (Z.min (lo * lo') (lo * hi')) (Z.min (hi * lo') (hi * hi')))
      (Z.max (Z.max (lo * lo') (lo * hi')) (Z.max (hi * lo') (hi * hi')))
  | _, _ => WFull
  end.

Lemma wrapped_product_bounds : forall a b c d x y,
  a <= x <= b -> c <= y <= d ->
  Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d)) <= x * y <=
  Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)).
Proof.
  intros a b c d x y Hx Hy.
  set (lo := Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))).
  set (hi := Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d))).
  assert (Hlo : lo <= a * c /\ lo <= a * d /\ lo <= b * c /\ lo <= b * d).
  { unfold lo. repeat split; repeat rewrite Z.min_le_iff; intuition lia. }
  assert (Hhi : a * c <= hi /\ a * d <= hi /\ b * c <= hi /\ b * d <= hi).
  { unfold hi. repeat split; repeat rewrite Z.max_le_iff; intuition lia. }
  destruct Hlo as [Hac [Had [Hbc Hbd]]], Hhi as [Hac' [Had' [Hbc' Hbd']]].
  destruct (Z_le_gt_dec 0 x); destruct (Z_le_gt_dec 0 c); destruct (Z_le_gt_dec 0 d); nia.
Qed.

Lemma wrapped_mul_piece_sound : forall w a b x y,
  gamma interval_gamma a x -> gamma interval_gamma b y ->
  wrapped_gamma w (wrapped_mul_piece w a b) (wrap w (x * y)).
Proof.
  intros w [|lo hi] [|lo' hi'] x y Hx Hy; cbn [wrapped_mul_piece];
    try contradiction; try apply wrap_is_word.
  destruct lo as [|lo|], hi as [|hi|], lo' as [|lo'|], hi' as [|hi'|];
    cbn [wrapped_mul_piece]; try apply wrap_is_word.
  cbn [interval_gamma gamma bound_leb] in Hx, Hy.
  destruct Hx as [Hlo Hhi], Hy as [Hlo' Hhi'].
  apply Z.leb_le in Hlo, Hhi, Hlo', Hhi'.
  apply wrapped_range_sound. now apply wrapped_product_bounds.
Qed.

(** Translating finite bounds preserves the mathematical interval meaning. *)
Definition wrapped_shift_interval (delta : Z) (a : interval) : interval :=
  let shift := fun b =>
    match b with
    | Fin z => Fin (z + delta)
    | _ => b
    end in
  match a with
  | IBot => IBot
  | Itv lo hi => Itv (shift lo) (shift hi)
  end.

Lemma wrapped_shift_interval_sound : forall delta a z,
  gamma interval_gamma a z -> gamma interval_gamma (wrapped_shift_interval delta a) (z + delta).
Proof.
  intros delta [|lo hi] z Hz; [exact Hz|].
  destruct lo as [|lo|], hi as [|hi|];
    cbn [wrapped_shift_interval interval_gamma gamma bound_leb] in *;
    try tauto; rewrite ?Z.leb_le in *; intuition lia.
Qed.

Lemma wrapped_signed_bias : forall w x,
  is_word w x -> signed w x = wrap w (x + half w) - half w.
Proof.
  intros w x Hx. unfold signed. rewrite (wrap_id w x Hx).
  pose proof (modulus_half w) as Hmod.
  pose proof (half_pos w) as Hhalf. unfold is_word in Hx.
  destruct (x <? half w) eqn:Hsign.
  - apply Z.ltb_lt in Hsign. unfold wrap. rewrite Z.mod_small by lia. lia.
  - apply Z.ltb_ge in Hsign.
    assert (Hwrap : wrap w (x + half w) = x + half w - modulus w).
    { unfold wrap. symmetry. apply Z.mod_unique with (q := 1); lia. }
    rewrite Hwrap. lia.
Qed.

(** The signed cut is the unsigned cut after biasing by the sign bit, translated back. *)
Definition wrapped_signed_parts (w : width) (a : wrapped) : interval * interval :=
  let biased := wrapped_parts w (wrapped_add w a (WItv (half w) (half w))) in
  (wrapped_shift_interval (- half w) (fst biased),
   wrapped_shift_interval (- half w) (snd biased)).

Lemma wrapped_signed_parts_sound : forall w a z,
  wrapped_gamma w a z ->
  gamma interval_gamma (fst (wrapped_signed_parts w a)) (signed w z) \/
  gamma interval_gamma (snd (wrapped_signed_parts w a)) (signed w z).
Proof.
  intros w a z Hz. pose proof (wrapped_gamma_word w a z Hz) as Hword.
  assert (Hhalf : wrapped_gamma w (WItv (half w) (half w)) (half w)).
  { split.
    - unfold is_word. pose proof (half_pos w). pose proof (modulus_half w). lia.
    - change (wrapped_offset w (half w) (half w) <= wrapped_offset w (half w) (half w)).
      lia. }
  pose proof (wrapped_add_sound w a _ z _ Hz Hhalf) as Hbiased.
  apply wrapped_parts_spec in Hbiased.
  unfold wrapped_signed_parts. cbn [fst snd].
  rewrite (wrapped_signed_bias w z Hword).
  replace (wrap w (z + half w) - half w) with (wrap w (z + half w) + - half w) by ring.
  destruct Hbiased as [[_ Hfirst]|[_ Hsecond]].
  - left. now apply wrapped_shift_interval_sound.
  - right. now apply wrapped_shift_interval_sound.
Qed.

(** Products of pieces are covered with four constant-size combinations. *)
Definition wrapped_mul_parts (w : width) (a b : interval * interval) : wrapped :=
  wrapped_join_four w
    (wrapped_mul_piece w (fst a) (fst b))
    (wrapped_mul_piece w (fst a) (snd b))
    (wrapped_mul_piece w (snd a) (fst b))
    (wrapped_mul_piece w (snd a) (snd b)).

Lemma wrapped_mul_parts_sound : forall w a b x y,
  (gamma interval_gamma (fst a) x \/ gamma interval_gamma (snd a) x) ->
  (gamma interval_gamma (fst b) y \/ gamma interval_gamma (snd b) y) ->
  wrapped_gamma w (wrapped_mul_parts w a b) (wrap w (x * y)).
Proof.
  intros w a b x y Hx Hy. unfold wrapped_mul_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. now apply wrapped_mul_piece_sound.
  - right; left. now apply wrapped_mul_piece_sound.
  - right; right; left. now apply wrapped_mul_piece_sound.
  - right; right; right. now apply wrapped_mul_piece_sound.
Qed.

Lemma wrapped_interval_meet_gamma : forall a b z,
  gamma interval_gamma a z -> gamma interval_gamma b z ->
  gamma interval_gamma (interval_meet a b) z.
Proof.
  intros [|la ha] [|lb hb] z Ha Hb; try contradiction.
  destruct Ha as [Hla Hha], Hb as [Hlb Hhb].
  assert (Hlo : bound_leb (bound_max la lb) (Fin z) = true).
  { apply bound_max_least; assumption. }
  assert (Hhi : bound_leb (Fin z) (bound_min ha hb) = true).
  { apply bound_min_greatest; assumption. }
  assert (Hordered : bound_leb (bound_max la lb) (bound_min ha hb) = true).
  { eapply bound_leb_trans; eassumption. }
  assert (Hnonempty : bounds_nonempty (bound_max la lb) (bound_min ha hb) = true).
  { destruct (bound_max la lb), (bound_min ha hb); cbn in *; try discriminate; assumption. }
  cbn [interval_meet]. rewrite Hnonempty. split; assumption.
Qed.

(** A linear piece is split below and above a second pole without changing its integer meaning. *)
Definition wrapped_mul_cut (pole : Z) (a : interval) : interval * interval :=
  (interval_meet a (Itv NegInf (Fin (pole - 1))),
   interval_meet a (Itv (Fin pole) PosInf)).

Lemma wrapped_mul_cut_sound : forall pole a z,
  gamma interval_gamma a z ->
  gamma interval_gamma (fst (wrapped_mul_cut pole a)) z \/
  gamma interval_gamma (snd (wrapped_mul_cut pole a)) z.
Proof.
  intros pole a z Ha. unfold wrapped_mul_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z pole) as [Hlow|Hhigh].
  - left. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_gamma gamma bound_leb]. split; [reflexivity|]. apply Z.leb_le. lia.
  - right. apply wrapped_interval_meet_gamma; [exact Ha|].
    cbn [interval_gamma gamma bound_leb]. split; [apply Z.leb_le; lia|reflexivity].
Qed.

(** An arc's two pole cuts occupy four fixed slots, at most three of them nonempty. *)
Definition wrapped_mul_both_parts (w : width) (pole : Z) (a b : interval * interval) : wrapped :=
  let a0 := wrapped_mul_cut pole (fst a) in
  let a1 := wrapped_mul_cut pole (snd a) in
  let b0 := wrapped_mul_cut pole (fst b) in
  let b1 := wrapped_mul_cut pole (snd b) in
  wrapped_join_four w
    (wrapped_mul_parts w a0 b0) (wrapped_mul_parts w a0 b1)
    (wrapped_mul_parts w a1 b0) (wrapped_mul_parts w a1 b1).

Lemma wrapped_mul_both_parts_sound : forall w pole a b x y,
  (gamma interval_gamma (fst a) x \/ gamma interval_gamma (snd a) x) ->
  (gamma interval_gamma (fst b) y \/ gamma interval_gamma (snd b) y) ->
  wrapped_gamma w (wrapped_mul_both_parts w pole a b) (wrap w (x * y)).
Proof.
  intros w pole a b x y Hx Hy. unfold wrapped_mul_both_parts. apply wrapped_join_four_sound.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; left. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
  - right; right; right. apply wrapped_mul_parts_sound; now apply wrapped_mul_cut_sound.
Qed.

(** Multiplication retains the smaller of the unsigned and signed pole-cut covers. *)
Definition wrapped_mul (w : width) (a b : wrapped) : wrapped :=
  let unsigned := wrapped_mul_both_parts w (half w) (wrapped_parts w a) (wrapped_parts w b) in
  let signed := wrapped_mul_both_parts w 0 (wrapped_signed_parts w a) (wrapped_signed_parts w b) in
  if wrapped_size w unsigned <=? wrapped_size w signed then unsigned else signed.

Lemma wrapped_mul_sound : forall w a b x y,
  wrapped_gamma w a x -> wrapped_gamma w b y ->
  wrapped_gamma w (wrapped_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Hx Hy. unfold wrapped_mul.
  destruct (wrapped_size w _ <=? wrapped_size w _) eqn:Hsize.
  - unfold wmul. apply wrapped_mul_both_parts_sound.
    + apply wrapped_parts_spec in Hx. unfold interval_pgamma in Hx. tauto.
    + apply wrapped_parts_spec in Hy. unfold interval_pgamma in Hy. tauto.
  - rewrite wmul_signed. apply wrapped_mul_both_parts_sound;
      now apply wrapped_signed_parts_sound.
Qed.

(** * Forward evaluation through pole pieces *)

(** Signed quotient and remainder apply circular negation after their unsigned magnitude bounds. *)
Definition wrapped_signed_piece_raw (division : bool) (w : width) (a b : interval) : wrapped :=
  match interval_sign w a, interval_sign w b with
  | Some sa, Some sb =>
    let aa := if sa then interval_neg w a else a in
    let bb := if sb then interval_neg w b else b in
    let magnitude := wrapped_of_interval w
      (if division then interval_udiv w aa bb else interval_urem w aa bb) in
    if (if division then xorb sa sb else sa) then wrapped_neg w magnitude else magnitude
  | _, _ => WFull
  end.

Lemma wrapped_signed_piece_raw_sound : forall division w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  wrapped_gamma w (wrapped_signed_piece_raw division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  intros division w a b x y Ha Hb. unfold wrapped_signed_piece_raw.
  destruct (interval_sign w a) as [sa|] eqn:Hsa;
    destruct (interval_sign w b) as [sb|] eqn:Hsb;
    try (destruct division; [apply wsdiv_is_word|apply wsrem_is_word]).
  pose proof (interval_sign_sound w a x sa Ha Hsa) as Hx.
  pose proof (interval_sign_sound w b y sb Hb Hsb) as Hy.
  destruct division; destruct sa, sb; unfold wsdiv, wsrem; rewrite Hx, Hy; cbn;
    try apply wrapped_neg_sound; apply wrapped_interval_value_sound;
    first [apply interval_udiv_sound|apply interval_urem_sound];
    try apply interval_neg_sound; assumption.
Qed.

(** Empty pole pieces contribute no forward outcomes. *)
Definition wrapped_signed_piece (division : bool) (w : width) (a b : interval) : wrapped :=
  match a, b with
  | IBot, _ | _, IBot => WBot
  | _, _ => wrapped_signed_piece_raw division w a b
  end.

Lemma wrapped_signed_piece_sound : forall division w a b x y,
  interval_pgamma w a x -> interval_pgamma w b y ->
  wrapped_gamma w (wrapped_signed_piece division w a b)
    (if division then wsdiv w x y else wsrem w x y).
Proof.
  intros division w [|lo hi] [|lo' hi'] x y Ha Hb;
    try (exact (False_rect _ (proj2 Ha))); try (exact (False_rect _ (proj2 Hb))).
  apply wrapped_signed_piece_raw_sound; assumption.
Qed.

(** Projection wraps both linear pieces to a new width without discarding a fitting modular span. *)
Definition wrapped_project (target source : width) (q : wrapped) : wrapped :=
  let pieces := wrapped_parts source q in
  wrapped_join target
    (wrapped_of_interval target (fst pieces)) (wrapped_of_interval target (snd pieces)).

Lemma wrapped_project_sound : forall target source q z,
  wrapped_gamma source q z ->
  wrapped_gamma target (wrapped_project target source q) (wrap target z).
Proof.
  intros target source q z Hq. apply wrapped_parts_spec in Hq.
  unfold wrapped_project. apply wrapped_join_sound. destruct Hq as [[_ Hq]|[_ Hq]].
  - left. now apply wrapped_of_interval_sound.
  - right. now apply wrapped_of_interval_sound.
Qed.

(** A finite unsigned piece is cut again at the sign pole before bound-based binary operations. *)
Definition wrapped_pole_cut (w : width) (a : interval) : interval * interval :=
  (interval_meet a (Itv (Fin 0) (Fin (half w - 1))),
   interval_meet a (Itv (Fin (half w)) (Fin (modulus w - 1)))).

Lemma wrapped_pole_cut_sound : forall w a z,
  interval_pgamma w a z ->
  interval_pgamma w (fst (wrapped_pole_cut w a)) z \/
  interval_pgamma w (snd (wrapped_pole_cut w a)) z.
Proof.
  intros w a z Ha. pose proof (proj1 Ha) as Hword.
  unfold wrapped_pole_cut. cbn [fst snd].
  destruct (Z_lt_ge_dec z (half w)) as [Hlow|Hhigh].
  - left. apply interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; unfold is_word in Hword; lia.
  - right. apply interval_meet_sound; [exact Ha|].
    split; [exact Hword|]. cbn [interval_gamma gamma bound_leb].
    split; apply Z.leb_le; unfold is_word in Hword; lia.
Qed.

(** A linear transfer result is projected back to a circular arc. *)
Definition wrapped_piece_forward (o : op) (wps : list (width * interval)) (rw : width) :
  wrapped := wrapped_of_interval rw (interval_forward o wps rw).

Lemma wrapped_piece_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound interval_pgamma) wps ys -> eval_op o ys = Some (rw, z) ->
  wrapped_gamma rw (wrapped_piece_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hpayload Heval.
  destruct (interval_forward_sound o wps ys rw z Hpayload Heval) as [Hword Hz].
  unfold wrapped_piece_forward. rewrite <- (wrap_id rw z Hword).
  now apply wrapped_of_interval_sound.
Qed.

(** Unary transfers cover both pieces independently. *)
Definition wrapped_forward_unary (o : op) (w : width) (a : wrapped) (rw : width) : wrapped :=
  let pieces := wrapped_parts w a in
  wrapped_join rw
    (wrapped_piece_forward o [(w, fst pieces)] rw)
    (wrapped_piece_forward o [(w, snd pieces)] rw).

Lemma wrapped_forward_unary_sound : forall o w a x rw z,
  wrapped_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward_unary o w a rw) z.
Proof.
  intros o w a x rw z Ha Heval. apply wrapped_parts_spec in Ha.
  unfold wrapped_forward_unary. apply wrapped_join_sound.
  destruct Ha as [Ha|Ha].
  - left. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [|constructor]. unfold payload_sound. cbn.
    split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
  - right. eapply wrapped_piece_forward_sound; [|exact Heval].
    constructor; [|constructor]. unfold payload_sound. cbn.
    split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
Qed.

(** Bound transfers cut an unsigned pair at the sign pole as well. *)
Definition wrapped_piece_forward_binary (o : op) (wa wb : width) (a b : interval) (rw : width) :
  wrapped :=
  match o with
  | bvsdiv => wrapped_signed_piece true rw a b
  | bvsrem => wrapped_signed_piece false rw a b
  | _ => wrapped_piece_forward o [(wa, a); (wb, b)] rw
  end.

(** Bound transfers cut an unsigned pair at the sign pole as well. *)
Definition wrapped_piece_forward_cut (o : op) (wa wb : width) (a b : interval) (rw : width) :
  wrapped :=
  let pa := wrapped_pole_cut wa a in
  let pb := wrapped_pole_cut wb b in
  wrapped_join_four rw
    (wrapped_piece_forward_binary o wa wb (fst pa) (fst pb) rw)
    (wrapped_piece_forward_binary o wa wb (fst pa) (snd pb) rw)
    (wrapped_piece_forward_binary o wa wb (snd pa) (fst pb) rw)
    (wrapped_piece_forward_binary o wa wb (snd pa) (snd pb) rw).

(** Binary transfers use the four possible pairs of unsigned pieces, each cut at the sign pole. *)
Definition wrapped_forward_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width) :
  wrapped :=
  let pa := wrapped_parts wa a in
  let pb := wrapped_parts wb b in
  wrapped_join_four rw
    (wrapped_piece_forward_cut o wa wb (fst pa) (fst pb) rw)
    (wrapped_piece_forward_cut o wa wb (fst pa) (snd pb) rw)
    (wrapped_piece_forward_cut o wa wb (snd pa) (fst pb) rw)
    (wrapped_piece_forward_cut o wa wb (snd pa) (snd pb) rw).

Lemma wrapped_piece_binary_sound : forall o wa wb a b x y rw z,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_piece_forward_binary o wa wb a b rw) z.
Proof.
  intros o wa wb a b x y rw z Ha Hb Heval.
  assert (Hbase : wrapped_gamma rw (wrapped_piece_forward o [(wa, a); (wb, b)] rw) z).
  { eapply wrapped_piece_forward_sound; [|exact Heval]. constructor.
    - unfold payload_sound. cbn. split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
    - constructor; [|constructor]. unfold payload_sound. cbn.
      split; [reflexivity|]. split; [exact (proj1 Hb)|exact Hb]. }
  destruct o; try exact Hbase.
  all: assert (Hsame : wa = wb) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb wa wb) eqn:Hsame; [now apply Pos.eqb_eq|discriminate]); subst wb.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsdiv wa x y wsdiv eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply (wrapped_signed_piece_sound true); assumption.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsrem wa x y wsrem eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply (wrapped_signed_piece_sound false); assumption.
Qed.

Lemma wrapped_piece_forward_cut_sound : forall o wa wb a b x y rw z,
  interval_pgamma wa a x -> interval_pgamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_piece_forward_cut o wa wb a b rw) z.
Proof.
  intros o wa wb a b x y rw z Ha Hb Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold wrapped_piece_forward_cut. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_binary_sound; eassumption.
  - right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; left. eapply wrapped_piece_binary_sound; eassumption.
  - right; right; right. eapply wrapped_piece_binary_sound; eassumption.
Qed.

Lemma wrapped_forward_binary_sound : forall o wa wb a b x y rw z,
  wrapped_gamma wa a x -> wrapped_gamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward_binary o wa wb a b rw) z.
Proof.
  intros o wa wb a b x y rw z Ha Hb Heval.
  apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hb.
  unfold wrapped_forward_binary. apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; left. eapply wrapped_piece_forward_cut_sound; eassumption.
  - right; right; right. eapply wrapped_piece_forward_cut_sound; eassumption.
Qed.

(** Forward transfer selects the modular rules and the constant number of pole-cut bound rules. *)
Definition wrapped_forward (o : op) (wps : list (width * wrapped)) (rw : width) : wrapped :=
  match o, wps with
  | bvneg, [(_, a)] => wrapped_neg rw a
  | (bvzext _ | bvtrunc _), [(w, a)] => wrapped_project rw w a
  | bvadd, [(_, a); (_, b)] => wrapped_add rw a b
  | bvsub, [(_, a); (_, b)] => wrapped_sub rw a b
  | bvmul, [(_, a); (_, b)] => wrapped_mul rw a b
  | bvite, [_; (_, a); (_, b)] => wrapped_join rw a b
  | _, [(w, a)] => wrapped_forward_unary o w a rw
  | _, [(wa, a); (wb, b)] => wrapped_forward_binary o wa wb a b rw
  | _, _ => WFull
  end.

Lemma wrapped_forward_one_sound : forall o w a x rw z,
  wrapped_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Ha Heval. destruct o;
    try (eapply wrapped_forward_unary_sound; eassumption).
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. apply wrapped_neg_sound. exact Ha.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    inversion Heval; subst rw z. rewrite (wrap_id w x (wrapped_gamma_word _ _ _ Ha)).
    now apply wrapped_project_sound.
  - unfold eval_op in Heval. cbn [result_width map fst] in Heval.
    destruct (Pos.leb target w) eqn:Hwidth; [|discriminate].
    cbn [op_value normalize_word map fst snd] in Heval.
    inversion Heval; subst rw z. rewrite (wrap_id w x (wrapped_gamma_word _ _ _ Ha)).
    now apply wrapped_project_sound.
Qed.

Lemma wrapped_forward_two_sound : forall o wa wb a b x y rw z,
  wrapped_gamma wa a x -> wrapped_gamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward o [(wa, a); (wb, b)] rw) z.
Proof.
  intros o wa wb a b x y rw z Ha Hb Heval. destruct o;
    try (eapply wrapped_forward_binary_sound; eassumption).
  all: assert (Hsame : wa = wb) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb wa wb) eqn:Hsame; [now apply Pos.eqb_eq|discriminate]); subst wb.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd wa x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_add_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub wa x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_sub_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvmul wa x y wmul eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_mul_sound.
Qed.

Lemma wrapped_forward_three_sound : forall o wc wa wb condition a b c x y rw z,
  wrapped_gamma wc condition c -> wrapped_gamma wa a x -> wrapped_gamma wb b y ->
  eval_op o [(wc, c); (wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward o [(wc, condition); (wa, a); (wb, b)] rw) z.
Proof.
  intros o wc wa wb condition a b c x y rw z Hc Ha Hb Heval.
  destruct o; try exact (eval_op_is_word _ _ _ Heval).
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  cbn [result_width map fst] in Hwidth.
  destruct (Pos.eqb wc 1 && Pos.eqb wa wb) eqn:Hsame; [|discriminate].
  apply Bool.andb_true_iff in Hsame. destruct Hsame as [Hcondition Hsame].
  apply Pos.eqb_eq in Hcondition, Hsame. subst wc wb.
  inversion Hwidth; subst rw.
  rewrite eval_op_ite in Heval.
  destruct (wrap 1%positive c =? 1); inversion Heval; subst z;
    rewrite ?(wrap_id _ _ (wrapped_gamma_word _ _ _ Ha)),
      ?(wrap_id _ _ (wrapped_gamma_word _ _ _ Hb));
    apply wrapped_join_sound; tauto.
Qed.

Lemma wrapped_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound wrapped_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  wrapped_gamma rw (wrapped_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hpayload Heval.
  destruct wps as [|[wa a] rest]; inversion Hpayload as [|wp value tail values Ha Hrest]; subst.
  - destruct o; exact (eval_op_is_word _ _ _ Heval).
  - destruct value as [wx x]. destruct Ha as [Hwidth [Hx Ha]]. cbn in Hwidth, Ha. subst wx.
    destruct rest as [|[wb b] rest];
      inversion Hrest as [|second_wp second_value second_tail second_values Hb Htail]; subst.
    + eapply wrapped_forward_one_sound; eassumption.
    + destruct second_value as [wy y]. destruct Hb as [Hwidth [Hy Hb]].
      cbn in Hwidth, Hb. subst wy.
      destruct rest as [|[wc c] rest];
        inversion Htail as [|third_wp third_value third_tail third_values Hc Hlast]; subst.
      * eapply wrapped_forward_two_sound; eassumption.
      * destruct third_value as [wz value]. destruct Hc as [Hwidth [Hvalue Hc]].
        cbn in Hwidth, Hc. subst wz.
        destruct rest as [|wp rest].
        -- inversion Hlast; subst. eapply wrapped_forward_three_sound; eassumption.
        -- destruct o; exact (eval_op_is_word _ _ _ Heval).
Qed.

(** * Backward refinement through pieces *)

(** Pair joins independently cover refinements of the two operands. *)
Definition wrapped_pair_join (wa wb : width) (a b : wrapped * wrapped) : wrapped * wrapped :=
  (wrapped_join wa (fst a) (fst b), wrapped_join wb (snd a) (snd b)).

Definition wrapped_pair_gamma (wa wb : width) (a : wrapped * wrapped) (x y : Z) : Prop :=
  wrapped_gamma wa (fst a) x /\ wrapped_gamma wb (snd a) y.

Lemma wrapped_pair_join_sound : forall wa wb a b x y,
  wrapped_pair_gamma wa wb a x y \/ wrapped_pair_gamma wa wb b x y ->
  wrapped_pair_gamma wa wb (wrapped_pair_join wa wb a b) x y.
Proof.
  intros wa wb a b x y Hcase. destruct Hcase as [[Ha Hb]|[Ha Hb]];
    split; apply wrapped_join_sound; tauto.
Qed.

(** One linear backward case is projected independently at each operand width. *)
Definition wrapped_assume_consistent (o : op) (wa wb : width) (a b q : interval) : bool :=
  match result_width o [wa; wb] with
  | Some rw =>
    match interval_meet (interval_forward o [(wa, a); (wb, b)] rw) q with
    | IBot => false
    | _ => true
    end
  | None => false
  end.

Lemma wrapped_assume_consistent_sound : forall o wa wb a b q x y rw z,
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_assume_consistent o wa wb a b q = true.
Proof.
  intros o wa wb a b q x y rw z Ha Hb Hq Heval.
  assert (Hpayload : Forall2 (payload_sound interval_pgamma)
      [(wa, a); (wb, b)] [(wa, x); (wb, y)]).
  { constructor.
    - split; [reflexivity|]. split; [exact (proj1 Ha)|exact Ha].
    - constructor; [|constructor].
      split; [reflexivity|]. split; [exact (proj1 Hb)|exact Hb]. }
  pose proof (interval_forward_sound o _ _ rw z Hpayload Heval) as Hforward.
  pose proof (interval_meet_sound rw _ _ z Hforward Hq) as Hmeet.
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  change (result_width o [wa; wb] = Some rw) in Hwidth.
  unfold wrapped_assume_consistent. rewrite Hwidth.
  destruct (interval_meet (interval_forward o [(wa, a); (wb, b)] rw) q).
  - exact (False_rect _ (proj2 Hmeet)).
  - reflexivity.
Qed.

(** A consistent nonempty case invokes the linear backward rule. *)
Definition wrapped_assume_piece_raw (o : op) (wa wb : width) (a b q : interval) :
  wrapped * wrapped :=
  match a, b, q with
  | IBot, _, _ | _, IBot, _ | _, _, IBot => (WBot, WBot)
  | _, _, _ =>
    if wrapped_assume_consistent o wa wb a b q then
      let refined := interval_assume_pair o wa a b q in
      (wrapped_of_interval wa (fst refined), wrapped_of_interval wb (snd refined))
    else (WBot, WBot)
  end.

Lemma wrapped_assume_piece_raw_sound : forall o wa wb a b q x y rw z,
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (wrapped_assume_piece_raw o wa wb a b q) x y.
Proof.
  intros o wa wb a b q x y rw z Ha Hb Hq Heval.
  destruct (interval_assume_pair_sound o wa wb a b q x y rw z Ha Hb Hq Heval)
    as [Hleft Hright].
  assert (Ha_nonempty : a <> IBot) by (intro Hempty; subst a; exact (proj2 Ha)).
  assert (Hb_nonempty : b <> IBot) by (intro Hempty; subst b; exact (proj2 Hb)).
  assert (Hq_nonempty : q <> IBot) by (intro Hempty; subst q; exact (proj2 Hq)).
  pose proof (wrapped_assume_consistent_sound o wa wb a b q x y rw z Ha Hb Hq Heval) as Hcheck.
  destruct a; [contradiction|]. destruct b; [contradiction|]. destruct q; [contradiction|].
  unfold wrapped_pair_gamma, wrapped_assume_piece_raw. rewrite Hcheck. cbn [fst snd]. split.
  - rewrite <- (wrap_id wa x (proj1 Hleft)). apply wrapped_of_interval_sound. exact (proj2 Hleft).
  - rewrite <- (wrap_id wb y (proj1 Hright)). apply wrapped_of_interval_sound. exact (proj2 Hright).
Qed.

(** Comparisons refine sign-homogeneous pieces, then cover the four possible sign pairs. *)
Definition wrapped_assume_piece (o : op) (wa wb : width) (a b q : interval) : wrapped * wrapped :=
  let pa := wrapped_pole_cut wa a in
  let pb := wrapped_pole_cut wb b in
  wrapped_pair_join wa wb
    (wrapped_pair_join wa wb
      (wrapped_assume_piece_raw o wa wb (fst pa) (fst pb) q)
      (wrapped_assume_piece_raw o wa wb (fst pa) (snd pb) q))
    (wrapped_pair_join wa wb
      (wrapped_assume_piece_raw o wa wb (snd pa) (fst pb) q)
      (wrapped_assume_piece_raw o wa wb (snd pa) (snd pb) q)).

Lemma wrapped_assume_piece_sound : forall o wa wb a b q x y rw z,
  interval_pgamma wa a x -> interval_pgamma wb b y -> interval_pgamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (wrapped_assume_piece o wa wb a b q) x y.
Proof.
  intros o wa wb a b q x y rw z Ha Hb Hq Heval.
  apply wrapped_pole_cut_sound in Ha. apply wrapped_pole_cut_sound in Hb.
  unfold wrapped_assume_piece. apply wrapped_pair_join_sound.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - left. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - left. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. left.
    eapply wrapped_assume_piece_raw_sound; eassumption.
  - right. apply wrapped_pair_join_sound. right.
    eapply wrapped_assume_piece_raw_sound; eassumption.
Qed.

(** Both result pieces contribute backward cases, including guards whose result is a singleton. *)
Definition wrapped_assume_result (o : op) (wa wb : width) (a b : interval) (rw : width)
  (q : wrapped) : wrapped * wrapped :=
  let results := wrapped_parts rw q in
  wrapped_pair_join wa wb
    (wrapped_assume_piece o wa wb a b (fst results))
    (wrapped_assume_piece o wa wb a b (snd results)).

Lemma wrapped_assume_result_sound : forall o wa wb a b rw q x y z,
  interval_pgamma wa a x -> interval_pgamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (wrapped_assume_result o wa wb a b rw q) x y.
Proof.
  intros o wa wb a b rw q x y z Ha Hb Hq Heval.
  apply wrapped_parts_spec in Hq. unfold wrapped_assume_result. apply wrapped_pair_join_sound.
  destruct Hq as [Hq|Hq].
  - left. eapply wrapped_assume_piece_sound; eassumption.
  - right. eapply wrapped_assume_piece_sound; eassumption.
Qed.

(** The fixed eight backward cases are joined before meeting each original operand. *)
Definition wrapped_assume_binary_base (o : op) (wa wb : width) (a b : wrapped) (rw : width)
  (q : wrapped) : wrapped * wrapped :=
  let pa := wrapped_parts wa a in
  let pb := wrapped_parts wb b in
  let candidates := wrapped_pair_join wa wb
    (wrapped_pair_join wa wb
      (wrapped_assume_result o wa wb (fst pa) (fst pb) rw q)
      (wrapped_assume_result o wa wb (fst pa) (snd pb) rw q))
    (wrapped_pair_join wa wb
      (wrapped_assume_result o wa wb (snd pa) (fst pb) rw q)
      (wrapped_assume_result o wa wb (snd pa) (snd pb) rw q)) in
  (wrapped_meet wa a (fst candidates), wrapped_meet wb b (snd candidates)).

Lemma wrapped_assume_binary_base_sound : forall o wa wb a b rw q x y z,
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (wrapped_assume_binary_base o wa wb a b rw q) x y.
Proof.
  intros o wa wb a b rw q x y z Ha Hb Hq Heval.
  pose proof (proj1 (wrapped_parts_spec wa a x) Ha) as Hpa.
  pose proof (proj1 (wrapped_parts_spec wb b y) Hb) as Hpb.
  unfold wrapped_assume_binary_base.
  match goal with |- wrapped_pair_gamma _ _
    (wrapped_meet _ _ (fst ?candidates), _) _ _ =>
    assert (Hcandidates : wrapped_pair_gamma wa wb candidates x y)
  end.
  { apply wrapped_pair_join_sound. destruct Hpa as [Hpa|Hpa]; destruct Hpb as [Hpb|Hpb].
    - left. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - left. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. left.
      eapply wrapped_assume_result_sound; eassumption.
    - right. apply wrapped_pair_join_sound. right.
      eapply wrapped_assume_result_sound; eassumption. }
  destruct Hcandidates as [Hleft Hright]. split; now apply wrapped_meet_sound.
Qed.

Lemma wrapped_assume_binary_base_lower : forall o wa wb a b rw q,
  wrapped_leb wa (fst (wrapped_assume_binary_base o wa wb a b rw q)) a = true /\
  wrapped_leb wb (snd (wrapped_assume_binary_base o wa wb a b rw q)) b = true.
Proof.
  intros o wa wb a b rw q. unfold wrapped_assume_binary_base.
  split; apply wrapped_meet_lower_left.
Qed.

(** Rewrapping a result arc projects its two unsigned pieces to a new width. *)
Definition wrapped_rewrap (target source : width) (q : wrapped) : wrapped :=
  wrapped_project target source q.

Lemma wrapped_rewrap_sound : forall target source q z,
  wrapped_gamma source q z -> wrapped_gamma target (wrapped_rewrap target source q) (wrap target z).
Proof.
  apply wrapped_project_sound.
Qed.

(** Truncation refines the pieces that fit the result width; other pieces retain their bounds. *)
Definition wrapped_assume_trunc (w : width) (a : wrapped) (rw : width) (q : wrapped) : wrapped :=
  let pa := wrapped_parts w a in
  let pq := wrapped_parts rw q in
  wrapped_meet w a (wrapped_join_four w
    (wrapped_of_interval w (interval_assume_rewrap rw (fst pa) (fst pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (fst pa) (snd pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (snd pa) (fst pq)))
    (wrapped_of_interval w (interval_assume_rewrap rw (snd pa) (snd pq)))).

Lemma wrapped_assume_trunc_sound : forall w a rw q x,
  wrapped_gamma w a x -> wrapped_gamma rw q (wrap rw x) ->
  wrapped_gamma w (wrapped_assume_trunc w a rw q) x.
Proof.
  intros w a rw q x Ha Hq. unfold wrapped_assume_trunc. apply wrapped_meet_sound; [exact Ha|].
  pose proof (wrapped_gamma_word w a x Ha) as Hword.
  apply wrapped_parts_spec in Ha. apply wrapped_parts_spec in Hq.
  rewrite <- (wrap_id w x Hword). apply wrapped_join_four_sound.
  destruct Ha as [Ha|Ha]; destruct Hq as [Hq|Hq].
  - left. apply wrapped_of_interval_sound.
    exact (proj2 (interval_assume_rewrap_sound rw w _ _ x Ha Hq)).
  - right; left. apply wrapped_of_interval_sound.
    exact (proj2 (interval_assume_rewrap_sound rw w _ _ x Ha Hq)).
  - right; right; left. apply wrapped_of_interval_sound.
    exact (proj2 (interval_assume_rewrap_sound rw w _ _ x Ha Hq)).
  - right; right; right. apply wrapped_of_interval_sound.
    exact (proj2 (interval_assume_rewrap_sound rw w _ _ x Ha Hq)).
Qed.

Lemma wrapped_add_cancel : forall w x y, wrap w (wrap w (x + y) - y) = wrap w x.
Proof.
  intros w x y. rewrite (wrap_sub w (wrap w (x + y)) y), wrap_wrap, <- wrap_sub.
  replace (x + y - y) with x by ring. reflexivity.
Qed.

Lemma wrapped_sub_cancel_left : forall w x y, wrap w (wrap w (x - y) + y) = wrap w x.
Proof.
  intros w x y. rewrite (wrap_add w (wrap w (x - y)) y), wrap_wrap, <- wrap_add.
  replace (x - y + y) with x by ring. reflexivity.
Qed.

Lemma wrapped_sub_cancel_right : forall w x y, wrap w (x - wrap w (x - y)) = wrap w y.
Proof.
  intros w x y. rewrite (wrap_sub w x (wrap w (x - y))), wrap_wrap, <- wrap_sub.
  replace (x - (x - y)) with y by ring. reflexivity.
Qed.

(** Add and subtract assumptions invert the modular operation before meeting each operand. *)
Definition wrapped_assume_binary (o : op) (wa wb : width) (a b : wrapped) (rw : width)
  (q : wrapped) : wrapped * wrapped :=
  match o with
  | bvadd => (wrapped_meet wa a (wrapped_sub wa q b), wrapped_meet wb b (wrapped_sub wb q a))
  | bvsub => (wrapped_meet wa a (wrapped_add wa q b), wrapped_meet wb b (wrapped_sub wb a q))
  | _ => wrapped_assume_binary_base o wa wb a b rw q
  end.

Lemma wrapped_assume_add_sound : forall w a b q x y,
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wadd w x y) ->
  wrapped_pair_gamma w w (wrapped_assume_binary bvadd w w a b w q) x y.
Proof.
  intros w a b q x y Ha Hb Hq. unfold wrapped_pair_gamma, wrapped_assume_binary.
  cbn [fst snd]. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_sub_sound w q b (wadd w x y) y Hq Hb) as Hleft.
    unfold wadd in Hleft. rewrite wrapped_add_cancel, (wrap_id w x (wrapped_gamma_word _ _ _ Ha))
      in Hleft. exact Hleft.
  - pose proof (wrapped_sub_sound w q a (wadd w x y) x Hq Ha) as Hright.
    unfold wadd in Hright. replace (x + y) with (y + x) in Hright by ring.
    rewrite wrapped_add_cancel, (wrap_id w y (wrapped_gamma_word _ _ _ Hb)) in Hright.
    exact Hright.
Qed.

Lemma wrapped_assume_sub_sound : forall w a b q x y,
  wrapped_gamma w a x -> wrapped_gamma w b y -> wrapped_gamma w q (wsub w x y) ->
  wrapped_pair_gamma w w (wrapped_assume_binary bvsub w w a b w q) x y.
Proof.
  intros w a b q x y Ha Hb Hq. unfold wrapped_pair_gamma, wrapped_assume_binary.
  cbn [fst snd]. split; apply wrapped_meet_sound; try assumption.
  - pose proof (wrapped_add_sound w q b (wsub w x y) y Hq Hb) as Hleft.
    unfold wsub in Hleft.
    rewrite wrapped_sub_cancel_left, (wrap_id w x (wrapped_gamma_word _ _ _ Ha)) in Hleft.
    exact Hleft.
  - pose proof (wrapped_sub_sound w a q x (wsub w x y) Ha Hq) as Hright.
    unfold wsub in Hright.
    rewrite wrapped_sub_cancel_right, (wrap_id w y (wrapped_gamma_word _ _ _ Hb)) in Hright.
    exact Hright.
Qed.

Lemma wrapped_assume_binary_sound : forall o wa wb a b rw q x y z,
  wrapped_gamma wa a x -> wrapped_gamma wb b y -> wrapped_gamma rw q z ->
  eval_op o [(wa, x); (wb, y)] = Some (rw, z) ->
  wrapped_pair_gamma wa wb (wrapped_assume_binary o wa wb a b rw q) x y.
Proof.
  intros o wa wb a b rw q x y z Ha Hb Hq Heval. destruct o;
    try (eapply wrapped_assume_binary_base_sound; eassumption).
  all: assert (Hsame : wa = wb) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb wa wb) eqn:Hsame; [now apply Pos.eqb_eq|discriminate]); subst wb.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd wa x y wadd eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_assume_add_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub wa x y wsub eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply wrapped_assume_sub_sound.
Qed.

Lemma wrapped_assume_binary_lower : forall o wa wb a b rw q,
  wrapped_leb wa (fst (wrapped_assume_binary o wa wb a b rw q)) a = true /\
  wrapped_leb wb (snd (wrapped_assume_binary o wa wb a b rw q)) b = true.
Proof.
  intros o wa wb a b rw q. destruct o;
    try apply wrapped_assume_binary_base_lower; split; apply wrapped_meet_lower_left.
Qed.

(** Extension assumptions project the result's low bits; truncation projects fitting pieces. *)
Definition wrapped_assume_unary (o : op) (w : width) (a : wrapped) (rw : width) (q : wrapped) :
  wrapped :=
  match o with
  | bvzext _ | bvsext _ => wrapped_meet w a (wrapped_rewrap w rw q)
  | bvtrunc _ => wrapped_assume_trunc w a rw q
  | _ => wrapped_norm w a
  end.

Lemma wrapped_assume_unary_sound : forall o w a rw q x z,
  wrapped_gamma w a x -> wrapped_gamma rw q z -> eval_op o [(w, x)] = Some (rw, z) ->
  wrapped_gamma w (wrapped_assume_unary o w a rw q) x.
Proof.
  intros o w a rw q x z Ha Hq Heval.
  pose proof (wrapped_gamma_word w a x Ha) as Hword.
  destruct o; try exact (proj2 (wrapped_norm_gamma w a x) Ha).
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    inversion Heval; subst rw z. apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_rewrap_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_wrap, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + lia.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (signed w (wrap w x))) =
      Some (rw, z)) in Heval.
    inversion Heval; subst rw z. apply wrapped_meet_sound; [exact Ha|].
    pose proof (wrapped_rewrap_sound w (w + extra)%positive q _ Hq) as Hproject.
    rewrite wrap_narrow, wrap_signed, wrap_wrap, (wrap_id w x Hword) in Hproject.
    + exact Hproject.
    + lia.
  - unfold eval_op in Heval. cbn [result_width map fst] in Heval.
    destruct (Pos.leb target w) eqn:Hwidth; [|discriminate].
    cbn [op_value normalize_word map fst snd] in Heval.
    rewrite (wrap_id w x Hword) in Heval. inversion Heval; subst rw z.
    now apply wrapped_assume_trunc_sound.
Qed.

Lemma wrapped_assume_unary_lower : forall o w a rw q,
  wrapped_leb w (wrapped_assume_unary o w a rw q) a = true.
Proof.
  intros o w a rw q. destruct o; try exact (proj2 (wrapped_norm_leb w a));
    try apply wrapped_meet_lower_left.
Qed.

(** Backward transfer retains the operand count and refines each supported operand. *)
Definition wrapped_assume (o : op) (wps : list (width * wrapped)) (rw : width) (q : wrapped) :
  list wrapped :=
  match wps with
  | [(w, a)] => [wrapped_assume_unary o w a rw q]
  | [(wa, a); (wb, b)] =>
    let refined := wrapped_assume_binary o wa wb a b rw q in [fst refined; snd refined]
  | _ => map (fun wp => wrapped_norm (fst wp) (snd wp)) wps
  end.

Lemma wrapped_assume_identity_sound : forall wps ys,
  Forall2 (payload_sound wrapped_gamma) wps ys ->
  Forall2 (fun p y => wrapped_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (map (fun wp => wrapped_norm (fst wp) (snd wp)) wps)) ys.
Proof.
  intros wps ys Hpayload. induction Hpayload as [|[w a] [v z] rest values Ha Hrest IH].
  - constructor.
  - destruct Ha as [Hwidth [Hword Ha]]. cbn in Hwidth, Ha. subst v.
    constructor; [|exact IH]. exact (proj2 (wrapped_norm_gamma w a z) Ha).
Qed.

Lemma wrapped_assume_sound : forall o wps ys rw z q,
  Forall2 (payload_sound wrapped_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  wrapped_gamma rw q z ->
  Forall2 (fun p y => wrapped_gamma (fst p) (snd p) (snd y))
    (combine (map fst wps) (wrapped_assume o wps rw q)) ys.
Proof.
  intros o wps ys rw z q Hpayload Heval Hq.
  destruct wps as [|[wa a] rest].
  - inversion Hpayload; subst. constructor.
  - destruct rest as [|[wb b] rest].
    + inversion Hpayload as [|wp [wx x] tail values Ha Htail]; subst.
      inversion Htail; subst. destruct Ha as [Hwidth [Hword Ha]]. cbn in Hwidth, Ha. subst wx.
      constructor; [|constructor]. eapply wrapped_assume_unary_sound; eassumption.
    + destruct rest as [|wp rest].
      * inversion Hpayload as [|wp [wx x] tail values Ha Htail]; subst.
        inversion Htail as [|wp [wy y] tail' values' Hb Hlast]; subst.
        inversion Hlast; subst.
        destruct Ha as [Hwidtha [Hworda Ha]], Hb as [Hwidthb [Hwordb Hb]].
        cbn in Hwidtha, Hwidthb, Ha, Hb. subst wx wy.
        destruct (wrapped_assume_binary_sound o wa wb a b rw q x y z Ha Hb Hq Heval)
          as [Hleft Hright]. constructor; [exact Hleft|constructor; [exact Hright|constructor]].
      * exact (wrapped_assume_identity_sound _ _ Hpayload).
Qed.

Lemma wrapped_assume_identity_lower : forall wps,
  Forall2 (fun wp p' => wrapped_leb (fst wp) p' (snd wp) = true) wps
    (map (fun wp => wrapped_norm (fst wp) (snd wp)) wps).
Proof.
  intro wps. induction wps as [|[w a] rest IH]; constructor; [|exact IH].
  exact (proj2 (wrapped_norm_leb w a)).
Qed.

Lemma wrapped_assume_lower : forall o wps rw q,
  Forall2 (fun wp p' => wrapped_leb (fst wp) p' (snd wp) = true) wps
    (wrapped_assume o wps rw q).
Proof.
  intros o [|[wa a] rest] rw q; [constructor|].
  destruct rest as [|[wb b] rest].
  - constructor; [apply wrapped_assume_unary_lower|constructor].
  - destruct rest as [|wp rest].
    + destruct (wrapped_assume_binary_lower o wa wb a b rw q) as [Hleft Hright].
      constructor; [exact Hleft|constructor; [exact Hright|constructor]].
    + apply wrapped_assume_identity_lower.
Qed.

(** The word dictionary provides circular constants, transfers, refinements and intersections. *)
Definition wrapped_domain : word_domain wrapped :=
  {| plat := wrapped_lattice;
     ptop _ := WFull;
     pconst w z := WItv (wrap w z) (wrap w z);
     pforward := wrapped_forward;
     passume := wrapped_assume;
     pmeet := wrapped_meet |}.

(** Every forward result and backward refinement preserves the total concrete word semantics. *)
Theorem wrapped_word_laws : word_laws wrapped_domain wrapped_gamma.
Proof.
  constructor.
  - apply wrapped_laws.
  - intros w a b z Hle Hz. exact (proj1 (wrapped_leb_spec w a b) Hle z Hz).
  - intros w z Hempty. exact Hempty.
  - intros w z Hz. exact Hz.
  - intros w z. split; [apply wrap_is_word|lia].
  - apply wrapped_forward_sound.
  - apply wrapped_assume_sound.
  - apply wrapped_assume_lower.
  - apply wrapped_meet_sound.
  - apply wrapped_meet_lower_left.
Qed.
