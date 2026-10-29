(** * Exact sign-separated bits and bounds

    A hemisphere stores the conjunction of known bits and an inclusive interval.
    For example, intersecting the four-bit mask for {0,4} with [1,6] gives singleton 4.
    Builds on: BitsWord, BitsTestbit and DomainsKnownBits. *)

From Stdlib Require Import ZArith Bool Lia.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit.
From Gaulois.Domains Require Import DomainsKnownBits.

Local Open Scope Z_scope.

(** Empty halves have one representation; ranges carry independent bit and bound components. *)
Inductive sb_half : Type :=
  | SBEmpty
  | SBRange (bits : tnum) (lo hi : Z).

(** The two fields describe the clear and set sign-bit hemispheres independently. *)
Record signed_bounds : Type := SignedBounds {
  sb_zero : sb_half;
  sb_one : sb_half
}.

(** Bit meaning includes the word range and the selected sign hemisphere. *)
Definition sb_bit_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop :=
  match h with
  | SBEmpty => False
  | SBRange t _ _ => is_word w z /\ msb w z = sign /\ tnum_gamma w t z
  end.

(** Interval meaning intersects raw inclusive endpoints with the selected hemisphere. *)
Definition sb_interval_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop :=
  match h with
  | SBEmpty => False
  | SBRange _ lo hi => is_word w z /\ msb w z = sign /\ lo <= z <= hi
  end.

(** A half means the conjunction of its independently interpreted components. *)
Definition sb_half_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop :=
  sb_bit_gamma w sign h z /\ sb_interval_gamma w sign h z.

(** The payload means the union of its two disjoint sign hemispheres. *)
Definition signed_bounds_gamma (w : width) (a : signed_bounds) (z : Z) : Prop :=
  sb_half_gamma w false (sb_zero a) z \/ sb_half_gamma w true (sb_one a) z.

(** Summaries specify least component hulls without enumerating their represented set. *)
Definition sb_summary (w : width) (S : Z -> Prop) (h : sb_half) : Prop :=
  match h with
  | SBEmpty => forall x, ~ S x
  | SBRange t lo hi =>
    tnum_normalise w t = t /\ S lo /\ S hi /\
    (forall x, S x -> is_word w x /\ tnum_gamma w t x /\ lo <= x <= hi) /\
    (forall q, (forall x, S x -> tnum_gamma w q x) ->
      leb (tnum_lattice w) t q = true)
  end.

Definition sb_cube (w : width) (t : tnum) (x : Z) : Prop :=
  is_word w x /\ tnum_gamma w t x.

Lemma sb_normalise_idempotent : forall w t,
  tnum_normalise w (tnum_normalise w t) = tnum_normalise w t.
Proof.
  intros w [z o]. unfold tnum_normalise. cbn. now rewrite !wrap_wrap.
Qed.

Lemma sb_normalise_leb : forall w t,
  leb (tnum_lattice w) (tnum_normalise w t) t = true /\
  leb (tnum_lattice w) t (tnum_normalise w t) = true.
Proof.
  intros w t. split; apply tnum_leb_bits; split; intros i Hi Hbit;
    cbn [tnum_normalise zeros ones] in *;
    rewrite ?tnum_wrap_bit in * by exact Hi; exact Hbit.
Qed.

Lemma sb_meet_gamma : forall w a b z,
  tnum_gamma w (tnum_meet w a b) z <-> tnum_gamma w a z /\ tnum_gamma w b z.
Proof.
  intros w a b z. split; [|intros [Ha Hb]; now apply tnum_meet_sound].
  intro Hz. split.
  - eapply tnum_gamma_monotone; [apply tnum_meet_lower_left|exact Hz].
  - eapply tnum_gamma_monotone; [|exact Hz].
    apply tnum_leb_bits. split; intros i Hi Hbit;
      cbn [tnum_meet zeros ones]; rewrite tnum_or_bit, Hbit by exact Hi;
      now rewrite orb_true_r.
Qed.

Lemma sb_cube_best : forall w t q,
  tnum_empty w t = false ->
  (forall x, sb_cube w t x -> tnum_gamma w q x) ->
  leb (tnum_lattice w) t q = true.
Proof.
  intros w t q Hempty Hall.
  destruct (tnum_endpoints_sound w t Hempty) as [Hmin Hmax].
  pose proof (Hall _ (conj (wrap_is_word w _) Hmin)) as Hlow.
  pose proof (Hall _ (conj (wnot_is_word w _) Hmax)) as Hhigh.
  apply tnum_gamma_bits in Hlow, Hhigh.
  destruct Hlow as [_ Hone], Hhigh as [Hzero _].
  apply tnum_leb_bits. split; intros i Hi Hbit.
  - specialize (Hzero i Hi Hbit). unfold tnum_max in Hzero.
    rewrite tnum_not_bit in Hzero by exact Hi. now apply negb_false_iff in Hzero.
  - specialize (Hone i Hi Hbit). unfold tnum_min in Hone.
    now rewrite tnum_wrap_bit in Hone by exact Hi.
Qed.

Lemma sb_cube_summary : forall w t,
  tnum_empty w t = false ->
  sb_summary w (sb_cube w t)
    (SBRange (tnum_normalise w t) (tnum_min w t) (tnum_max w t)).
Proof.
  intros w t Hempty.
  destruct (tnum_endpoints_sound w t Hempty) as [Hmin Hmax].
  cbn [sb_summary]. split; [apply sb_normalise_idempotent|].
  split; [exact (conj (wrap_is_word w _) Hmin)|].
  split; [exact (conj (wnot_is_word w _) Hmax)|]. split.
  - intros x [Hx Ht]. split; [exact Hx|]. split.
    + now apply tnum_normalise_sound.
    + now apply tnum_unsigned_bounds.
  - intros q Hq. eapply (leb_trans (tnum_laws w)).
    + exact (proj1 (sb_normalise_leb w t)).
    + now apply sb_cube_best.
Qed.

(** A merge takes the independently least bit and interval hulls of two summaries. *)
Definition sb_merge (w : width) (a b : sb_half) : sb_half :=
  match a, b with
  | SBEmpty, _ => b
  | _, SBEmpty => a
  | SBRange ta la ua, SBRange tb lb ub =>
    SBRange (tnum_join w ta tb) (Z.min la lb) (Z.max ua ub)
  end.

Lemma sb_join_normalised : forall w a b,
  tnum_normalise w (tnum_join w a b) = tnum_join w a b.
Proof.
  intros w a b. unfold tnum_normalise, tnum_join. cbn [zeros ones].
  rewrite !wrap_id by apply wand_is_word. reflexivity.
Qed.

Lemma sb_summary_transport : forall w S T h,
  (forall x, S x <-> T x) -> sb_summary w S h -> sb_summary w T h.
Proof.
  intros w S T [|t lo hi] Hequiv Hsummary; cbn [sb_summary] in *.
  - intros x Hx. apply (Hsummary x). now apply Hequiv.
  - destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    split; [exact Hnorm|]. split; [now apply Hequiv|].
    split; [now apply Hequiv|]. split.
    + intros x Hx. apply Hsound. now apply Hequiv.
    + intros q Hq. apply Hbest. intros x Hx. apply Hq. now apply Hequiv.
Qed.

Lemma sb_merge_summary : forall w S T a b,
  sb_summary w S a -> sb_summary w T b ->
  sb_summary w (fun x => S x \/ T x) (sb_merge w a b).
Proof.
  intros w S T [|ta la ua] [|tb lb ub] Ha Hb; cbn [sb_merge sb_summary] in *.
  - intros x [Hx|Hx]; [exact (Ha x Hx)|exact (Hb x Hx)].
  - apply (sb_summary_transport w T (fun x => S x \/ T x) (SBRange tb lb ub));
      [|exact Hb]. intros x. split; [now right|].
    intros [Hx|Hx]; [exfalso; exact (Ha x Hx)|exact Hx].
  - apply (sb_summary_transport w S (fun x => S x \/ T x) (SBRange ta la ua));
      [|exact Ha]. intros x. split; [now left|].
    intros [Hx|Hx]; [exact Hx|exfalso; exact (Hb x Hx)].
  - destruct Ha as [Hna [Hla [Hua [Hsa Hba]]]].
    destruct Hb as [Hnb [Hlb [Hub [Hsb Hbb]]]].
    split; [apply sb_join_normalised|]. split.
    + destruct (Z_le_dec la lb); [rewrite Z.min_l; [now left|assumption]|].
      rewrite Z.min_r; [now right|lia].
    + split.
      * destruct (Z_le_dec ua ub); [rewrite Z.max_r; [now right|assumption]|].
        rewrite Z.max_l; [now left|lia].
      * split.
        -- intros x [Hx|Hx].
           ++ destruct (Hsa x Hx) as [Hw [Ht Hbounds]]. split; [exact Hw|].
              split; [apply tnum_join_sound; now left|].
              pose proof (Z.le_min_l la lb). pose proof (Z.le_max_l ua ub). lia.
           ++ destruct (Hsb x Hx) as [Hw [Ht Hbounds]]. split; [exact Hw|].
              split; [apply tnum_join_sound; now right|].
              pose proof (Z.le_min_r la lb). pose proof (Z.le_max_r ua ub). lia.
        -- intros q Hq. apply (join_least (tnum_lub w)).
           ++ apply Hba. intros x Hx. apply Hq. now left.
           ++ apply Hbb. intros x Hx. apply Hq. now right.
Qed.

(** A one-bit mask records a branch decision without constraining any other position. *)
Definition sb_bit (i : Z) (b : bool) : tnum :=
  if b then Tnum 0 (2 ^ i) else Tnum (2 ^ i) 0.

Lemma sb_bit_gamma_exact : forall w i b z,
  0 <= i < Zpos w ->
  (tnum_gamma w (sb_bit i b) z <-> Z.testbit z i = b).
Proof.
  intros w i b z Hi. rewrite tnum_gamma_bits. unfold sb_bit.
  destruct b; cbn [zeros ones]; split.
  - intros [_ H]. apply (H i Hi). now apply Z.pow2_bits_true.
  - intro H. split; intros j Hj Hbit.
    + rewrite Z.bits_0 in Hbit. discriminate.
    + rewrite Z.pow2_bits_eqb in Hbit by lia. apply Z.eqb_eq in Hbit. now subst j.
  - intros [H _]. apply (H i Hi). now apply Z.pow2_bits_true.
  - intro H. split; intros j Hj Hbit.
    + rewrite Z.pow2_bits_eqb in Hbit by lia. apply Z.eqb_eq in Hbit. now subst j.
    + rewrite Z.bits_0 in Hbit. discriminate.
Qed.

Definition sb_fix_bit (w : width) (t : tnum) (i : Z) (b : bool) : tnum :=
  tnum_meet w t (sb_bit i b).

Lemma sb_fix_bit_gamma : forall w t i b z,
  0 <= i < Zpos w ->
  (tnum_gamma w (sb_fix_bit w t i b) z <->
    tnum_gamma w t z /\ Z.testbit z i = b).
Proof.
  intros w t i b z Hi. unfold sb_fix_bit. rewrite sb_meet_gamma, sb_bit_gamma_exact by
    exact Hi. reflexivity.
Qed.

(** Every position above the unprocessed suffix has already received a branch decision. *)
Definition sb_fixed_above (w : width) (n : Z) (t : tnum) : Prop :=
  forall i, n <= i < Zpos w ->
    Z.testbit (zeros t) i = true \/ Z.testbit (ones t) i = true.

Lemma sb_fix_bit_above : forall w t n b,
  0 <= n < Zpos w -> sb_fixed_above w (Z.succ n) t ->
  sb_fixed_above w n (sb_fix_bit w t n b).
Proof.
  intros w t n b Hn Hfixed i Hi. unfold sb_fix_bit, tnum_meet. cbn [zeros ones].
  rewrite !tnum_or_bit by lia.
  destruct (Z.eq_dec i n) as [->|Hne].
  - unfold sb_bit. destruct b; cbn [zeros ones];
      rewrite Z.pow2_bits_true by lia;
      [right|left]; now rewrite orb_true_r.
  - destruct (Hfixed i ltac:(lia)) as [Hz|Ho]; [left|right];
      rewrite ?Hz, ?Ho; reflexivity.
Qed.

Lemma sb_fixed_singleton : forall w t,
  tnum_empty w t = false -> sb_fixed_above w 0 t -> tnum_min w t = tnum_max w t.
Proof.
  intros w t Hempty Hfixed.
  destruct (tnum_endpoints_sound w t Hempty) as [Hmin Hmax].
  apply tnum_gamma_bits in Hmin, Hmax.
  destruct Hmin as [Hminz Hmino], Hmax as [Hmaxz Hmaxo].
  apply (word_ext w); [apply wrap_is_word|apply wnot_is_word|].
  intros i Hi. destruct (Z_lt_ge_dec i (Zpos w)) as [Hlow|Hhigh].
  - destruct (Hfixed i ltac:(lia)) as [Hz|Ho].
    + now rewrite (Hminz i ltac:(lia) Hz), (Hmaxz i ltac:(lia) Hz).
    + now rewrite (Hmino i ltac:(lia) Ho), (Hmaxo i ltac:(lia) Ho).
  - now rewrite !(word_bits_high w) by (try apply wrap_is_word; try apply wnot_is_word; lia).
Qed.

(** The positive marker provides structural MSB-first traversal, with one sentinel digit.
    Fully covered subcubes are summarized directly. Only the two interval boundary paths
    can remain partial at any depth; their other children stop at the next range check. *)
Fixpoint sb_search (p : positive) (w : width) (t : tnum) (lo hi : Z) : sb_half :=
  if tnum_empty w t then SBEmpty else
  if (tnum_max w t <? lo) || (hi <? tnum_min w t) then SBEmpty else
  if (lo <=? tnum_min w t) && (tnum_max w t <=? hi)
  then SBRange (tnum_normalise w t) (tnum_min w t) (tnum_max w t)
  else
    match p with
    | xH => SBEmpty
    | xO q | xI q =>
      let i := Z.log2 (Zpos q) in
      sb_merge w (sb_search q w (sb_fix_bit w t i false) lo hi)
        (sb_search q w (sb_fix_bit w t i true) lo hi)
    end.

Lemma sb_search_disjoint : forall w t lo hi,
  (tnum_max w t <? lo) || (hi <? tnum_min w t) = true ->
  sb_summary w (fun x => sb_cube w t x /\ lo <= x <= hi) SBEmpty.
Proof.
  intros w t lo hi Houtside x [[Hx Ht] Hbounds].
  pose proof (tnum_unsigned_bounds w t x Hx Ht) as Hcube.
  apply orb_true_iff in Houtside as [Houtside|Houtside];
    apply Z.ltb_lt in Houtside; lia.
Qed.

Lemma sb_search_full : forall w t lo hi,
  tnum_empty w t = false ->
  (lo <=? tnum_min w t) && (tnum_max w t <=? hi) = true ->
  sb_summary w (fun x => sb_cube w t x /\ lo <= x <= hi)
    (SBRange (tnum_normalise w t) (tnum_min w t) (tnum_max w t)).
Proof.
  intros w t lo hi Hempty Hinside. apply andb_true_iff in Hinside as [Hlo Hhi].
  apply Z.leb_le in Hlo, Hhi. eapply sb_summary_transport; [|now apply sb_cube_summary].
  intros x. split; [|tauto]. intros [Hx Ht]. split; [now split|].
  pose proof (tnum_unsigned_bounds w t x Hx Ht). lia.
Qed.

Lemma sb_search_branch : forall w t lo hi i f,
  0 <= i < Zpos w ->
  (forall b, sb_summary w (fun x => sb_cube w (sb_fix_bit w t i b) x /\ lo <= x <= hi)
    (f b)) ->
  sb_summary w (fun x => sb_cube w t x /\ lo <= x <= hi)
    (sb_merge w (f false) (f true)).
Proof.
  intros w t lo hi i f Hi Hbranches.
  eapply sb_summary_transport; [|apply sb_merge_summary; apply Hbranches].
  intros x. unfold sb_cube. rewrite !sb_fix_bit_gamma by exact Hi.
  destruct (Z.testbit x i); tauto.
Qed.

Lemma sb_search_summary : forall p w t lo hi,
  Z.log2 (Zpos p) <= Zpos w -> sb_fixed_above w (Z.log2 (Zpos p)) t ->
  sb_summary w (fun x => sb_cube w t x /\ lo <= x <= hi) (sb_search p w t lo hi).
Proof.
  intro p. induction p as [p IH|p IH|]; intros w t lo hi Hdepth Hfixed;
    cbn [sb_search]; destruct (tnum_empty w t) eqn:Hempty.
  all: try (intros x [[Hx Ht] Hbounds];
    pose proof (tnum_empty_sound w t x Ht); congruence).
  all: destruct ((tnum_max w t <? lo) || (hi <? tnum_min w t)) eqn:Houtside;
    [now apply sb_search_disjoint|].
  all: destruct ((lo <=? tnum_min w t) && (tnum_max w t <=? hi)) eqn:Hinside;
    [now apply sb_search_full|].
  - rewrite Pos2Z.inj_xI, Z.log2_succ_double in Hdepth, Hfixed by lia.
    apply (sb_search_branch w t lo hi (Z.log2 (Zpos p))
      (fun b => sb_search p w (sb_fix_bit w t (Z.log2 (Zpos p)) b) lo hi));
      [pose proof (Z.log2_nonneg (Zpos p)); lia|].
    intro b. apply IH; [lia|]. apply sb_fix_bit_above; [|exact Hfixed].
    pose proof (Z.log2_nonneg (Zpos p)). lia.
  - rewrite Pos2Z.inj_xO, Z.log2_double in Hdepth, Hfixed by lia.
    apply (sb_search_branch w t lo hi (Z.log2 (Zpos p))
      (fun b => sb_search p w (sb_fix_bit w t (Z.log2 (Zpos p)) b) lo hi));
      [pose proof (Z.log2_nonneg (Zpos p)); lia|].
    intro b. apply IH; [lia|]. apply sb_fix_bit_above; [|exact Hfixed].
    pose proof (Z.log2_nonneg (Zpos p)). lia.
  - change (sb_fixed_above w 0 t) in Hfixed.
    pose proof (sb_fixed_singleton w t Hempty Hfixed) as Heq.
    apply orb_false_iff in Houtside as [Hlo Hhi].
    apply Z.ltb_ge in Hlo, Hhi. apply andb_false_iff in Hinside as [Hbad|Hbad];
      apply Z.leb_gt in Hbad; lia.
Qed.

Lemma sb_clipped_bounds : forall w lo hi z,
  is_word w z ->
  (Z.max 0 lo <= z <= Z.min (modulus w - 1) hi <-> lo <= z <= hi).
Proof.
  intros w lo hi z Hz. unfold is_word in Hz.
  rewrite Z.max_lub_iff, Z.min_glb_iff. lia.
Qed.

(** Reduction clips raw endpoints once, fixes the sign bit and searches the finite cube. *)
Definition sb_reduce_half (w : width) (sign : bool) (h : sb_half) : sb_half :=
  match h with
  | SBEmpty => SBEmpty
  | SBRange t lo hi =>
    let lo' := Z.max 0 lo in
    let hi' := Z.min (modulus w - 1) hi in
    if hi' <? lo' then SBEmpty else
    sb_search (Z.to_pos (modulus w)) w (sb_fix_bit w t (Zpos w - 1) sign) lo' hi'
  end.

(** Each sign hemisphere is reduced independently. *)
Definition signed_bounds_reduce (w : width) (a : signed_bounds) : signed_bounds :=
  SignedBounds (sb_reduce_half w false (sb_zero a)) (sb_reduce_half w true (sb_one a)).

Lemma sb_reduce_half_summary : forall w s h,
  sb_summary w (sb_half_gamma w s h) (sb_reduce_half w s h).
Proof.
  intros w s [|t lo hi]; [intros x [Hempty _]; exact Hempty|].
  unfold sb_reduce_half.
  destruct (Z.min (modulus w - 1) hi <? Z.max 0 lo) eqn:Hempty.
  { intros x [[Hw [Hs Ht]] [_ [_ Hbounds]]].
    apply (proj2 (sb_clipped_bounds w lo hi x Hw)) in Hbounds.
    apply Z.ltb_lt in Hempty. lia. }
  eapply sb_summary_transport with
    (S := fun x => sb_cube w (sb_fix_bit w t (Zpos w - 1) s) x /\
      Z.max 0 lo <= x <= Z.min (modulus w - 1) hi).
  - intros x. unfold sb_cube, sb_half_gamma, sb_bit_gamma, sb_interval_gamma.
    rewrite sb_fix_bit_gamma by lia. unfold msb. split.
    + intros [[Hx [Ht Hsign]] Hbounds].
      apply (proj1 (sb_clipped_bounds w lo hi x Hx)) in Hbounds.
      rewrite wrap_id by exact Hx. tauto.
    + intros [[Hx [Hsign Ht]] [_ [_ Hbounds]]].
      rewrite wrap_id in Hsign by exact Hx.
      apply (proj2 (sb_clipped_bounds w lo hi x Hx)) in Hbounds. tauto.
  - apply sb_search_summary.
    + rewrite Z2Pos.id by apply modulus_pos. unfold modulus. rewrite Z.log2_pow2 by lia.
      lia.
    + rewrite Z2Pos.id by apply modulus_pos. unfold modulus. rewrite Z.log2_pow2 by lia.
      intros i Hi. lia.
Qed.

Lemma sb_half_gamma_range : forall w s t lo hi z,
  sb_half_gamma w s (SBRange t lo hi) z <->
  is_word w z /\ msb w z = s /\ tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros. unfold sb_half_gamma, sb_bit_gamma, sb_interval_gamma. tauto.
Qed.

(** Exact reduction preserves precisely the feasible words in the selected hemisphere. *)
Theorem sb_reduce_half_gamma : forall w s h z,
  sb_half_gamma w s (sb_reduce_half w s h) z <-> sb_half_gamma w s h z.
Proof.
  intros w s [|t lo hi] z; [reflexivity|].
  pose proof (sb_reduce_half_summary w s (SBRange t lo hi)) as Hsummary.
  destruct (sb_reduce_half w s (SBRange t lo hi)) as [|t' lo' hi'] eqn:Hreduce.
  - split; [intros [Hempty _]; contradiction|].
    intro Hz. exfalso. exact (Hsummary z Hz).
  - cbn [sb_summary] in Hsummary.
    destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
    apply sb_half_gamma_range in Hlo, Hhi.
    rewrite (sb_half_gamma_range w s t' lo' hi' z).
    rewrite (sb_half_gamma_range w s t lo hi z).
    assert (Hbits : leb (tnum_lattice w) t' t = true).
    { apply Hbest. intros x Hx. apply sb_half_gamma_range in Hx. tauto. }
    split.
    + intros [Hw [Hs [Ht Hb]]]. split; [exact Hw|]. split; [exact Hs|].
      split; [eapply tnum_gamma_monotone; eassumption|lia].
    + intro Hz. assert (Hraw : sb_half_gamma w s (SBRange t lo hi) z)
        by (apply sb_half_gamma_range; exact Hz).
      destruct (Hsound z Hraw) as [Hw [Ht Hb]]. tauto.
Qed.

Lemma sb_tnum_antisym : forall w a b,
  tnum_normalise w a = a -> tnum_normalise w b = b ->
  leb (tnum_lattice w) a b = true -> leb (tnum_lattice w) b a = true -> a = b.
Proof.
  intros w a b Ha Hb Hab Hba.
  assert (Hequiv : tnum_equiv w a b).
  { apply tnum_equiv_bits. apply tnum_leb_bits in Hab, Hba.
    destruct Hab as [Haz Hao], Hba as [Hbz Hbo]. intros i Hi. split.
    - specialize (Haz i Hi). specialize (Hbz i Hi).
      destruct (Z.testbit (zeros a) i), (Z.testbit (zeros b) i); intuition congruence.
    - specialize (Hao i Hi). specialize (Hbo i Hi).
      destruct (Z.testbit (ones a) i), (Z.testbit (ones b) i); intuition congruence. }
  destruct Hequiv as [Hz Ho]. rewrite <- Ha, <- Hb. unfold tnum_normalise.
  now rewrite Hz, Ho.
Qed.

Lemma sb_summary_unique : forall w S a b,
  sb_summary w S a -> sb_summary w S b -> a = b.
Proof.
  intros w S [|ta la ua] [|tb lb ub] Ha Hb; cbn [sb_summary] in *; [reflexivity| | |].
  - destruct Hb as [_ [Hlo _]]. exfalso. exact (Ha lb Hlo).
  - destruct Ha as [_ [Hlo _]]. exfalso. exact (Hb la Hlo).
  - destruct Ha as [Hna [Hla [Hua [Hsa Hba]]]].
    destruct Hb as [Hnb [Hlb [Hub [Hsb Hbb]]]].
    assert (Hbits : ta = tb).
    { apply (sb_tnum_antisym w); try assumption.
      - apply Hba. intros x Hx. exact (proj1 (proj2 (Hsb x Hx))).
      - apply Hbb. intros x Hx. exact (proj1 (proj2 (Hsa x Hx))). }
    pose proof (Hsa lb Hlb) as Hlbounds. pose proof (Hsa ub Hub) as Hubounds.
    pose proof (Hsb la Hla) as Hlabounds. pose proof (Hsb ua Hua) as Huabounds.
    f_equal; try exact Hbits; tauto || lia.
Qed.

(** Canonical least hulls are unchanged by a second reduction. *)
Theorem sb_reduce_half_idempotent : forall w s h,
  sb_reduce_half w s (sb_reduce_half w s h) = sb_reduce_half w s h.
Proof.
  intros w s h. apply (sb_summary_unique w (sb_half_gamma w s h)).
  - eapply sb_summary_transport; [|apply sb_reduce_half_summary].
    intro x. apply sb_reduce_half_gamma.
  - apply sb_reduce_half_summary.
Qed.

(** The returned mask is the least bit component containing the original feasible set. *)
Theorem sb_reduce_half_hulls : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_bit_gamma w s q x) ->
  (forall z, sb_bit_gamma w s (sb_reduce_half w s h) z -> sb_bit_gamma w s q z).
Proof.
  intros w s h q Hcover z Hz.
  pose proof (sb_reduce_half_summary w s h) as Hsummary.
  destruct (sb_reduce_half w s h) as [|t lo hi]; [contradiction|].
  destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
  destruct q as [|tq lq uq].
  - exact (Hcover lo Hlo).
  - destruct Hz as [Hw [Hs Ht]]. split; [exact Hw|]. split; [exact Hs|].
    eapply tnum_gamma_monotone; [apply Hbest|exact Ht].
    intros x Hx. exact (proj2 (proj2 (Hcover x Hx))).
Qed.

(** The returned interval is the least interval component containing all feasible words. *)
Theorem sb_reduce_half_interval_hull : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_interval_gamma w s q x) ->
  (forall z, sb_interval_gamma w s (sb_reduce_half w s h) z -> sb_interval_gamma w s q z).
Proof.
  intros w s h q Hcover z Hz.
  pose proof (sb_reduce_half_summary w s h) as Hsummary.
  destruct (sb_reduce_half w s h) as [|t lo hi]; [contradiction|].
  destruct Hsummary as [Hnorm [Hlo [Hhi [Hsound Hbest]]]].
  destruct q as [|tq lq uq].
  - exact (Hcover lo Hlo).
  - pose proof (Hcover lo Hlo) as Hlower. pose proof (Hcover hi Hhi) as Hupper.
    cbn [sb_interval_gamma] in *. destruct Hz as [Hw [Hs Hb]].
    split; [exact Hw|]. split; [exact Hs|]. tauto || lia.
Qed.

(** Independent hemisphere reduction preserves the complete payload meaning. *)
Theorem signed_bounds_reduce_gamma : forall w a z,
  signed_bounds_gamma w (signed_bounds_reduce w a) z <-> signed_bounds_gamma w a z.
Proof.
  intros w [a b] z. unfold signed_bounds_gamma, signed_bounds_reduce.
  cbn [sb_zero sb_one]. now rewrite !sb_reduce_half_gamma.
Qed.

(** Both canonical hemisphere representations are syntactically idempotent. *)
Theorem signed_bounds_reduce_idempotent : forall w a,
  signed_bounds_reduce w (signed_bounds_reduce w a) = signed_bounds_reduce w a.
Proof.
  intros w [a b]. unfold signed_bounds_reduce. cbn [sb_zero sb_one].
  now rewrite !sb_reduce_half_idempotent.
Qed.
