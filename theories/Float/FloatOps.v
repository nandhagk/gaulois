(** * Floating-point operations and NaN choices

    Concrete arithmetic exposes the hardware's NaN policy as an explicit dictionary.
    For example, infinity divided by infinity uses that policy to produce a NaN.
    Builds on: Flocq Binary and FloatInterval. *)

From Stdlib Require Import Bool ZArith Reals Lra Lia.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary.
From Gaulois.Float Require Import FloatInterval.

Local Arguments B754_nan {prec emax} _ _ _.
Local Arguments B754_zero {prec emax} _.
Local Arguments B754_infinity {prec emax} _.
Local Arguments B754_finite {prec emax} _ _ _ _.

Section Float.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).

(** Arithmetic operations return floats and preserve the explicit NaN model. *)
Inductive farith : Type :=
  | FAdd
  | FSub
  | FMul
  | FDiv.

(** Less-than returns an integer truth value rather than a float. *)
Inductive fbop : Type :=
  | FArith (o : farith)
  | FLt.

(** Binary NaN choices depend only on which operands are NaNs and their complete NaN data. *)
Record nan_model : Type := NanModel {
  nan_choice : farith -> fl -> fl -> fl;
  nan_choice_nan : forall o x y, is_nan prec emax (nan_choice o x y) = true;
  nan_choice_local : forall o x y x' y',
    is_nan prec emax x = is_nan prec emax x' ->
    is_nan prec emax y = is_nan prec emax y' ->
    (is_nan prec emax x = true -> B2FF prec emax x = B2FF prec emax x') ->
    (is_nan prec emax y = true -> B2FF prec emax y = B2FF prec emax y') ->
    nan_choice o x y = nan_choice o x' y';
  nan_neg : fl -> fl;
  nan_neg_nan : forall x, is_nan prec emax (nan_neg x) = true;
  nan_abs : fl -> fl;
  nan_abs_nan : forall x, is_nan prec emax (nan_abs x) = true
}.

Definition quiet_payload : positive := Z.to_pos (2 ^ (prec - 2)).

Lemma quiet_payload_valid (Hp : (2 <= prec)%Z) : nan_pl prec quiet_payload = true.
Proof.
  unfold nan_pl, quiet_payload; apply Zlt_bool_true.
  rewrite Zpos_digits2_pos, Z2Pos.id by
    (exact (Zpower_gt_0 radix2 (prec - 2) ltac:(lia))).
  change (Zdigits radix2 (2 ^ (prec - 2)) < prec)%Z.
  rewrite Zdigits_Zpower by lia; lia.
Qed.

Definition quiet_nan (Hp : (2 <= prec)%Z) : fl :=
  B754_nan false quiet_payload (quiet_payload_valid Hp).

(** The fixed quiet NaN of positive sign makes the model interface inhabited. *)
Definition default_nan_model (Hp : (2 <= prec)%Z) : nan_model.
Proof.
  refine {| nan_choice := fun _ _ _ => quiet_nan Hp;
            nan_neg := fun _ => quiet_nan Hp;
            nan_abs := fun _ => quiet_nan Hp |}.
  - intros o x y; reflexivity.
  - intros o x y x' y' Hx Hy Hnx Hny; reflexivity.
  - intro x; reflexivity.
  - intro x; reflexivity.
Defined.

(** Concrete arithmetic uses round-to-nearest, ties-to-even, and the supplied binary NaN choice. *)
Definition fl_eval_bin (nm : nan_model) (o : farith) (x y : fl) : fl :=
  let choose := fun u v => exist _ (nan_choice nm o u v) (nan_choice_nan nm o u v) in
  match o with
  | FAdd => Bplus prec emax Hprec Hmax choose mode_NE x y
  | FSub => Bminus prec emax Hprec Hmax choose mode_NE x y
  | FMul => Bmult prec emax Hprec Hmax choose mode_NE x y
  | FDiv => Bdiv prec emax Hprec Hmax choose mode_NE x y
  end.

(** Negation flips every non-NaN sign and uses the unary NaN choice otherwise. *)
Definition fl_eval_neg (nm : nan_model) (x : fl) : fl :=
  Bopp prec emax (fun u => exist _ (nan_neg nm u) (nan_neg_nan nm u)) x.

(** Absolute value clears every non-NaN sign and uses the absolute-value NaN choice otherwise. *)
Definition fl_eval_abs (nm : nan_model) (x : fl) : fl :=
  Babs prec emax (fun u => exist _ (nan_abs nm u) (nan_abs_nan nm u)) x.

(** Unordered comparisons, including every NaN comparison, return false. *)
Definition fl_lt (x y : fl) : bool :=
  match Bcompare prec emax x y with
  | Some Lt => true
  | _ => false
  end.

(** * Exact unary transfers *)

Definition fl_flip (x : fl) : fl :=
  match x with
  | B754_zero s => B754_zero (negb s)
  | B754_infinity s => B754_infinity (negb s)
  | B754_nan _ _ _ => x
  | B754_finite s m e Hbound => B754_finite (negb s) m e Hbound
  end.

Definition fl_magnitude (x : fl) : fl :=
  match x with
  | B754_zero _ => B754_zero false
  | B754_infinity _ => B754_infinity false
  | B754_nan _ _ _ => x
  | B754_finite _ m e Hbound => B754_finite false m e Hbound
  end.

Lemma fl_flip_nan x : is_nan prec emax (fl_flip x) = is_nan prec emax x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma fl_magnitude_nan x : is_nan prec emax (fl_magnitude x) = is_nan prec emax x.
Proof.
  destruct x; reflexivity.
Qed.

Definition nn_neg (x : fl_nn) : fl_nn :=
  exist _ (fl_flip (proj1_sig x)) (eq_trans (fl_flip_nan _) (proj2_sig x)).

Definition nn_abs (x : fl_nn) : fl_nn :=
  exist _ (fl_magnitude (proj1_sig x)) (eq_trans (fl_magnitude_nan _) (proj2_sig x)).

Definition fl_zero : @fl_nn prec emax := exist _ (B754_zero false) eq_refl.

Lemma fl_flip_real x : B2R prec emax (fl_flip x) = (- B2R prec emax x)%R.
Proof.
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [fl_flip B2R]; try lra.
  destruct s; unfold F2R; cbn [SpecFloat.cond_Zopp negb Fnum Fexp];
    rewrite opp_IZR; ring.
Qed.

Lemma fl_magnitude_real x : B2R prec emax (fl_magnitude x) = Rabs (B2R prec emax x).
Proof.
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [fl_magnitude B2R]; try now rewrite Rabs_R0.
  unfold F2R; cbn [Fnum Fexp].
  pose proof (bpow_gt_0 radix2 e) as Hpow.
  pose proof (IZR_lt 0 (Z.pos m) (Pos2Z.is_pos m)) as Hmantissa.
  destruct s; cbn [SpecFloat.cond_Zopp]; rewrite ?opp_IZR.
  - rewrite Rabs_left by nra; ring.
  - rewrite Rabs_right by nra; reflexivity.
Qed.

Lemma fle_flip x y : is_nan prec emax x = false -> is_nan prec emax y = false ->
  fle x y -> fle (fl_flip y) (fl_flip x).
Proof.
  intros Hx Hy Hle.
  apply (proj1 (fle_order x y Hx Hy)) in Hle.
  apply (proj2 (fle_order _ _ (eq_trans (fl_flip_nan _) Hy)
    (eq_trans (fl_flip_nan _) Hx))).
  pose proof (fl_flip_real x) as Hrx; pose proof (fl_flip_real y) as Hry.
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    destruct y as [sy|sy|sy py Hpy|sy my ey Hyb];
    cbn [is_nan] in Hx, Hy; try discriminate;
    cbn [fl_flip fl_order] in *;
    try solve [destruct sx; destruct sy; cbn in *; tauto];
    try solve [destruct sx; cbn in *; tauto];
    try solve [destruct sy; cbn in *; tauto].
  all: cbn [fl_flip B2R] in Hrx, Hry; cbn [B2R] in *; lra.
Qed.

Lemma subnormal_flip x : subnormal (fl_flip x) <-> subnormal x.
Proof.
  unfold subnormal; rewrite fl_flip_real, Rabs_Ropp.
  assert (Hfinite : is_finite prec emax (fl_flip x) = is_finite prec emax x)
    by (destruct x; reflexivity).
  rewrite Hfinite; intuition lra.
Qed.

Lemma subnormal_magnitude x : subnormal (fl_magnitude x) <-> subnormal x.
Proof.
  unfold subnormal; rewrite fl_magnitude_real, Rabs_Rabsolu.
  assert (Hfinite : is_finite prec emax (fl_magnitude x) = is_finite prec emax x)
    by (destruct x; reflexivity).
  rewrite Hfinite; split; intros [Hfin [Hnonzero Hsmall]]; repeat split; try assumption.
  - intro Hz; rewrite Hz, Rabs_R0 in Hnonzero; contradiction.
  - apply Rabs_no_R0; exact Hnonzero.
Qed.

(** Negation reverses the nonzero bounds and exchanges the two zero flags. *)
Definition fl_neg (I : fl_interval) : fl_interval :=
  FlInterval (nn_neg (fhi I)) (nn_neg (flo I)) (may_nan I)
    (may_pos_zero I) (may_neg_zero I) (may_subnormal I).

Lemma fl_gamma_flip I x : fl_gamma I x -> fl_gamma (fl_neg I) (fl_flip x).
Proof.
  destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_gamma B2FF fl_flip fl_neg flo fhi may_nan may_neg_zero may_pos_zero
      may_subnormal nn_neg proj1_sig];
    intro Hgamma; try exact Hgamma.
  - destruct s; exact Hgamma.
  - destruct Hgamma as [Hlo [Hhi Hsub]]; split.
    + exact (fle_flip (B754_infinity s) _ eq_refl (proj2_sig (fhi I)) Hhi).
    + split; [exact (fle_flip _ (B754_infinity s) (proj2_sig (flo I)) eq_refl Hlo)|].
      intro Hnormal; apply Hsub, (proj1 (subnormal_flip (B754_infinity s))); exact Hnormal.
  - destruct Hgamma as [Hlo [Hhi Hsub]]; split.
    + exact (fle_flip (B754_finite s m e Hb) _ eq_refl (proj2_sig (fhi I)) Hhi).
    + split; [exact (fle_flip _ (B754_finite s m e Hb)
        (proj2_sig (flo I)) eq_refl Hlo)|].
      intro Hnormal; apply Hsub, (proj1 (subnormal_flip (B754_finite s m e Hb))).
      exact Hnormal.
Qed.

(** Negation contains the concrete result for every unary NaN policy. *)
Theorem fl_neg_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_neg I) (fl_eval_neg nm x).
Proof.
  intro Hgamma; destruct x as [s|s|s p Hp|s m e Hb];
    exact (fl_gamma_flip I _ Hgamma).
Qed.

Lemma fle_trans x y z :
  is_nan prec emax x = false -> is_nan prec emax y = false ->
  is_nan prec emax z = false -> fle x y -> fle y z -> fle x z.
Proof.
  intros Hx Hy Hz Hxy Hyz; apply fl_le_spec.
  apply (fl_le_trans x y z Hx Hy Hz); apply fl_le_spec; assumption.
Qed.

Lemma fl_nonzero_active I x : is_nan prec emax x = false ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) -> fl_active I = true.
Proof.
  intros Hx Hlo Hhi; apply fl_le_spec.
  eapply fle_trans; [apply proj2_sig|exact Hx|apply proj2_sig|exact Hlo|exact Hhi].
Qed.

Lemma fl_magnitude_flip x : fl_magnitude (fl_flip x) = fl_magnitude x.
Proof.
  destruct x; reflexivity.
Qed.

Lemma fle_self_abs x : is_nan prec emax x = false -> fle x (fl_magnitude x).
Proof.
  intro Hx; apply (proj2 (fle_order _ _ Hx (eq_trans (fl_magnitude_nan _) Hx))).
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [is_nan] in Hx; try discriminate.
  - cbn [fl_magnitude fl_order B2R]; lra.
  - destruct s; exact I.
  - change (B2R prec emax (B754_finite s m e Hb) <=
      B2R prec emax (fl_magnitude (B754_finite s m e Hb)))%R.
    rewrite fl_magnitude_real; apply Rle_abs.
Qed.

Lemma fle_flip_abs x : is_nan prec emax x = false -> fle (fl_flip x) (fl_magnitude x).
Proof.
  intro Hx; rewrite <- fl_magnitude_flip; apply fle_self_abs.
  rewrite fl_flip_nan; exact Hx.
Qed.

Lemma fle_zero_abs x : is_nan prec emax x = false ->
  fle (B754_zero false) (fl_magnitude x).
Proof.
  intro Hx; apply (proj2 (fle_order (B754_zero false) (fl_magnitude x)
    eq_refl (eq_trans (fl_magnitude_nan _) Hx))).
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [is_nan] in Hx; try discriminate.
  - cbn [fl_magnitude fl_order B2R]; lra.
  - exact I.
  - change (0 <= B2R prec emax (fl_magnitude (B754_finite s m e Hb)))%R.
    rewrite fl_magnitude_real; apply Rabs_pos.
Qed.

Lemma fl_magnitude_cases x : is_nan prec emax x = false ->
  fl_magnitude x = x \/ fl_magnitude x = fl_flip x.
Proof.
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [is_nan]; intro Hnan; try discriminate.
  all: destruct s; [right|left]; reflexivity.
Qed.

Definition fl_abs_lo (I : fl_interval) : fl_nn :=
  if nn_le fl_zero (flo I) then flo I else
  if nn_le (fhi I) fl_zero then nn_neg (fhi I) else fl_zero.

Definition fl_abs_hi (I : fl_interval) : fl_nn := nn_max (nn_abs (flo I)) (nn_abs (fhi I)).

(** Absolute value preserves empty numeric bounds and combines the two zero flags. *)
Definition fl_abs (I : fl_interval) : fl_interval :=
  FlInterval (if fl_active I then fl_abs_lo I else fl_pinf)
    (if fl_active I then fl_abs_hi I else fl_ninf) (may_nan I) false
    (may_neg_zero I || may_pos_zero I) (may_subnormal I).

Lemma fl_abs_lower I x : is_nan prec emax x = false ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) ->
  fle (proj1_sig (fl_abs_lo I)) (fl_magnitude x).
Proof.
  intros Hx Hlo Hhi; unfold fl_abs_lo.
  destruct (nn_le fl_zero (flo I)); [|destruct (nn_le (fhi I) fl_zero)].
  - eapply fle_trans; [apply proj2_sig|exact Hx|rewrite fl_magnitude_nan; exact Hx|
      exact Hlo|apply fle_self_abs; exact Hx].
  - eapply fle_trans; [apply proj2_sig|rewrite fl_flip_nan; exact Hx|
      rewrite fl_magnitude_nan; exact Hx| |apply fle_flip_abs; exact Hx].
    apply fle_flip; [exact Hx|apply proj2_sig|exact Hhi].
  - apply fle_zero_abs; exact Hx.
Qed.

Lemma fl_abs_upper I x : is_nan prec emax x = false ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) ->
  fle (fl_magnitude x) (proj1_sig (fl_abs_hi I)).
Proof.
  intros Hx Hlo Hhi; destruct (fl_magnitude_cases x Hx) as [Hsame|Hflip].
  - rewrite Hsame; eapply (fle_trans _ (proj1_sig (fhi I)) _);
      [exact Hx|apply proj2_sig|apply proj2_sig|exact Hhi|].
    eapply (fle_trans _ (proj1_sig (nn_abs (fhi I))) _);
      [apply proj2_sig|apply proj2_sig|apply proj2_sig|
      apply fle_self_abs, proj2_sig|].
    apply fl_le_spec; exact (nn_max_r (nn_abs (flo I)) (nn_abs (fhi I))).
  - rewrite Hflip; eapply (fle_trans _ (proj1_sig (nn_neg (flo I))) _);
      [rewrite fl_flip_nan; exact Hx|apply proj2_sig|apply proj2_sig| |].
    + apply fle_flip; [apply proj2_sig|exact Hx|exact Hlo].
    + eapply (fle_trans _ (proj1_sig (nn_abs (flo I))) _);
        [apply proj2_sig|apply proj2_sig|apply proj2_sig|
        apply fle_flip_abs, proj2_sig|].
      apply fl_le_spec; exact (nn_max_l (nn_abs (flo I)) (nn_abs (fhi I))).
Qed.

Lemma fl_gamma_magnitude I x : fl_gamma I x -> fl_gamma (fl_abs I) (fl_magnitude x).
Proof.
  destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_gamma B2FF fl_magnitude fl_abs flo fhi may_nan may_neg_zero may_pos_zero
      may_subnormal];
    intro Hgamma; try exact Hgamma.
  - apply orb_true_iff; destruct s; [left|right]; exact Hgamma.
  - destruct Hgamma as [Hlo [Hhi Hsub]].
    rewrite (fl_nonzero_active I (B754_infinity s) eq_refl Hlo Hhi); split.
    + exact (fl_abs_lower I (B754_infinity s) eq_refl Hlo Hhi).
    + split; [exact (fl_abs_upper I (B754_infinity s) eq_refl Hlo Hhi)|].
      intro Hnormal; apply Hsub, (proj1 (subnormal_magnitude (B754_infinity s))).
      exact Hnormal.
  - destruct Hgamma as [Hlo [Hhi Hsub]].
    rewrite (fl_nonzero_active I (B754_finite s m e Hb) eq_refl Hlo Hhi); split.
    + exact (fl_abs_lower I (B754_finite s m e Hb) eq_refl Hlo Hhi).
    + split; [exact (fl_abs_upper I (B754_finite s m e Hb) eq_refl Hlo Hhi)|].
      intro Hnormal; apply Hsub, (proj1 (subnormal_magnitude (B754_finite s m e Hb))).
      exact Hnormal.
Qed.

(** Absolute value contains the concrete result for every absolute-value NaN policy. *)
Theorem fl_abs_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_abs I) (fl_eval_abs nm x).
Proof.
  intro Hgamma; destruct x as [s|s|s p Hp|s m e Hb];
    exact (fl_gamma_magnitude I _ Hgamma).
Qed.

(** * Ordered comparison refinement *)

Definition fl_has_zero (I : @fl_interval prec emax) : bool := may_neg_zero I || may_pos_zero I.

Definition fl_full_lo (I : fl_interval) : fl_nn :=
  if fl_has_zero I then
    if fl_active I then nn_min (flo I) fl_zero else fl_zero
  else flo I.

Definition fl_full_hi (I : fl_interval) : fl_nn :=
  if fl_has_zero I then
    if fl_active I then nn_max (fhi I) fl_zero else fl_zero
  else fhi I.

Lemma fl_full_nonzero_bounds I x : is_nan prec emax x = false ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) ->
  fle (proj1_sig (fl_full_lo I)) x /\ fle x (proj1_sig (fl_full_hi I)).
Proof.
  intros Hx Hlo Hhi; pose proof (fl_nonzero_active I x Hx Hlo Hhi) as Hactive.
  unfold fl_full_lo, fl_full_hi; rewrite Hactive; destruct (fl_has_zero I).
  - split.
    + eapply (fle_trans _ (proj1_sig (flo I)) _);
        [apply proj2_sig|apply proj2_sig|exact Hx| |exact Hlo].
      apply fl_le_spec; apply nn_min_l.
    + eapply (fle_trans _ (proj1_sig (fhi I)) _);
        [exact Hx|apply proj2_sig|apply proj2_sig|exact Hhi|].
      apply fl_le_spec; apply nn_max_l.
  - split; assumption.
Qed.

Lemma fl_full_zero_bounds I (s : bool) :
  (if s then may_neg_zero I else may_pos_zero I) = true ->
  fle (proj1_sig (fl_full_lo I)) (B754_zero s) /\
  fle (B754_zero s) (proj1_sig (fl_full_hi I)).
Proof.
  intro Hz; assert (Hhas : fl_has_zero I = true).
  { unfold fl_has_zero; apply orb_true_iff; destruct s; [left|right]; exact Hz. }
  assert (Hzz : @fle prec emax (B754_zero false) (B754_zero s) /\
    @fle prec emax (B754_zero s) (B754_zero false))
    by (destruct s; split; constructor).
  unfold fl_full_lo, fl_full_hi; rewrite Hhas; destruct (fl_active I).
  - split.
    + eapply (fle_trans _ (B754_zero false) _);
        [apply proj2_sig|reflexivity|reflexivity| |exact (proj1 Hzz)].
      apply fl_le_spec; exact (nn_min_r (flo I) fl_zero).
    + eapply (fle_trans _ (B754_zero false) _);
        [reflexivity|reflexivity|apply proj2_sig|exact (proj2 Hzz)|].
      apply fl_le_spec; exact (nn_max_r (fhi I) fl_zero).
  - exact Hzz.
Qed.

(** Ordered envelopes include separately flagged zeros, even when the nonzero bounds are empty. *)
Lemma fl_gamma_full_bounds I x : fl_gamma I x -> is_nan prec emax x = false ->
  fle (proj1_sig (fl_full_lo I)) x /\ fle x (proj1_sig (fl_full_hi I)).
Proof.
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [is_nan fl_gamma B2FF];
    intros Hgamma Hnan; try discriminate.
  - apply fl_full_zero_bounds; exact Hgamma.
  - destruct Hgamma as [Hlo [Hhi Hsub]]; apply fl_full_nonzero_bounds;
      [reflexivity|exact Hlo|exact Hhi].
  - destruct Hgamma as [Hlo [Hhi Hsub]]; apply fl_full_nonzero_bounds;
      [reflexivity|exact Hlo|exact Hhi].
Qed.

Definition fl_restrict_hi (I : @fl_interval prec emax) (bound : fl_nn) : fl_interval :=
  FlInterval (flo I) (nn_min (fhi I) bound) false (may_neg_zero I)
    (may_pos_zero I) (may_subnormal I).

Definition fl_restrict_lo (I : @fl_interval prec emax) (bound : fl_nn) : fl_interval :=
  FlInterval (nn_max (flo I) bound) (fhi I) false (may_neg_zero I)
    (may_pos_zero I) (may_subnormal I).

Lemma fl_restrict_hi_sound I bound x : fl_gamma I x -> is_nan prec emax x = false ->
  fle x (proj1_sig bound) -> fl_gamma (fl_restrict_hi I bound) x.
Proof.
  destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_gamma B2FF fl_restrict_hi is_nan flo fhi may_nan may_neg_zero may_pos_zero
      may_subnormal];
    intros Hgamma Hnan Hbound; try discriminate; try exact Hgamma.
  all: destruct Hgamma as [Hlo [Hhi Hsub]]; split; [exact Hlo|]; split; [|exact Hsub].
  all: unfold nn_min; destruct (nn_le (fhi I) bound); assumption.
Qed.

Lemma fl_restrict_lo_sound I bound x : fl_gamma I x -> is_nan prec emax x = false ->
  fle (proj1_sig bound) x -> fl_gamma (fl_restrict_lo I bound) x.
Proof.
  destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_gamma B2FF fl_restrict_lo is_nan flo fhi may_nan may_neg_zero may_pos_zero
      may_subnormal];
    intros Hgamma Hnan Hbound; try discriminate; try exact Hgamma.
  all: destruct Hgamma as [Hlo [Hhi Hsub]]; split; [|split; assumption].
  all: unfold nn_max; destruct (nn_le (flo I) bound); assumption.
Qed.

(** Strict comparison excludes NaNs and intersects both operands with their ordered envelopes. *)
Definition fl_assume_lt (I J : fl_interval) : fl_interval * fl_interval :=
  (fl_restrict_hi I (fl_full_hi J), fl_restrict_lo J (fl_full_lo I)).

Lemma fl_compare_ordered x y : Bcompare prec emax x y = Some Lt ->
  is_nan prec emax x = false /\ is_nan prec emax y = false /\ fle x y.
Proof.
  intro Hlt; assert (Hx : is_nan prec emax x = false).
  { destruct x; try reflexivity; destruct y; discriminate. }
  assert (Hy : is_nan prec emax y = false).
  { destruct y; try reflexivity; destruct x; discriminate. }
  split; [exact Hx|]; split; [exact Hy|unfold fle; rewrite Hlt; exact I].
Qed.

(** Both operands of a successful strict comparison remain in their refined intervals. *)
Theorem fl_assume_lt_sound (I J : fl_interval) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> Bcompare prec emax x y = Some Lt ->
  fl_gamma (fst (fl_assume_lt I J)) x /\ fl_gamma (snd (fl_assume_lt I J)) y.
Proof.
  intros Hix Hjy Hlt; destruct (fl_compare_ordered x y Hlt) as [Hx [Hy Hxy]].
  destruct (fl_gamma_full_bounds I x Hix Hx) as [Hloi Hhii].
  destruct (fl_gamma_full_bounds J y Hjy Hy) as [Hloj Hhij].
  split.
  - apply fl_restrict_hi_sound; [exact Hix|exact Hx|].
    eapply fle_trans; [exact Hx|exact Hy|apply proj2_sig|exact Hxy|exact Hhij].
  - apply fl_restrict_lo_sound; [exact Hjy|exact Hy|].
    eapply fle_trans; [apply proj2_sig|exact Hx|exact Hy|exact Hloi|exact Hxy].
Qed.

Local Abbreviation fl_round_real := (round radix2 (SpecFloat.fexp prec emax)).

(** * Finite arithmetic envelopes *)

Lemma fl_max_finite : is_finite prec emax (@Bmax_float prec emax Hprec Hmax) = true.
Proof.
  reflexivity.
Qed.
Lemma fl_max_finite_real : B2R prec emax (@Bmax_float prec emax Hprec Hmax) =
  (bpow radix2 emax - bpow radix2 (emax - prec))%R.
Proof.
  pose proof (@prec_gt_0 prec Hprec) as Hp.
  unfold Bmax_float; rewrite B2R_BSN2B'.
  unfold BinarySingleNaN.Bmax_float; rewrite BinarySingleNaN.B2R_SF2B.
  cbn [SF2R]; unfold F2R; cbn [Fnum Fexp SpecFloat.cond_Zopp].
  assert (Hshift : (Z.pos (shift_pos (Z.to_pos prec) 1) = 2 ^ prec)%Z).
  { rewrite shift_pos_correct, Z.mul_1_r, Z.pow_pos_fold, Z2Pos.id by exact Hprec.
    reflexivity. }
  rewrite Pos2Z.inj_sub by
    (change (1 < Z.pos (shift_pos (Z.to_pos prec) 1))%Z;
      rewrite Hshift; exact (Zpower_gt_1 radix2 prec Hprec)).
  rewrite Hshift, minus_IZR.
  change ((IZR (Zpower radix2 prec) - 1) * bpow radix2 (emax - prec) =
    bpow radix2 emax - bpow radix2 (emax - prec))%R.
  rewrite (IZR_Zpower radix2 prec) by lia.
  rewrite Rmult_minus_distr_r, Rmult_1_l, <- bpow_plus.
  replace (prec + (emax - prec))%Z with emax by lia; reflexivity.
Qed.

Definition fl_min_normal : fl :=
  binary_normalize prec emax Hprec Hmax mode_NE 1 (2 - emax) false.

Lemma fl_min_normal_correct : B2R prec emax fl_min_normal = bpow radix2 (2 - emax) /\
  is_finite prec emax fl_min_normal = true.
Proof.
  pose proof (@prec_gt_0 prec Hprec) as Hp.
  pose proof (@prec_lt_emax prec emax Hmax) as Hm.
  assert (Hformat : generic_format radix2 (SpecFloat.fexp prec emax)
      (bpow radix2 (2 - emax))).
  { apply generic_format_bpow; unfold SpecFloat.fexp, FLT_exp, SpecFloat.emin.
    apply Z.max_lub; lia. }
  pose proof (binary_normalize_correct prec emax Hprec Hmax mode_NE 1 (2 - emax) false)
    as Hcorrect.
  unfold F2R in Hcorrect; cbn [Fnum Fexp] in Hcorrect.
  rewrite Rmult_1_l in Hcorrect.
  rewrite round_generic in Hcorrect by
    (first [apply valid_rnd_round_mode|exact Hformat]).
  rewrite Rabs_right in Hcorrect by (pose proof (bpow_gt_0 radix2 (2 - emax)); lra).
  rewrite Rlt_bool_true in Hcorrect by
    (apply bpow_lt; lia).
  exact (conj (proj1 Hcorrect) (proj1 (proj2 Hcorrect))).
Qed.

Definition fl_finite_bound : Type := {x : fl | is_finite prec emax x = true}.

Lemma fl_finite_not_nan x : is_finite prec emax x = true -> is_nan prec emax x = false.
Proof.
  destruct x; cbn; intro Hfinite; try discriminate; reflexivity.
Qed.

Definition fl_finite_nn (x : fl_finite_bound) : fl_nn :=
  exist _ (proj1_sig x) (fl_finite_not_nan _ (proj2_sig x)).

Definition nn_finite_clamp (x : @fl_nn prec emax) : fl_finite_bound.
Proof.
  destruct x as [[s|s|s p Hp|s m e Hb] Hnan].
  - exact (exist _ (B754_zero s) eq_refl).
  - destruct s.
    + exact (exist _ (fl_flip (@Bmax_float prec emax Hprec Hmax)) eq_refl).
    + exact (exist _ (@Bmax_float prec emax Hprec Hmax) eq_refl).
  - discriminate Hnan.
  - exact (exist _ (B754_finite s m e Hb) eq_refl).
Defined.

Lemma nn_finite_clamp_lower bound x : is_finite prec emax x = true ->
  fle (proj1_sig bound) x -> fle (proj1_sig (nn_finite_clamp bound)) x.
Proof.
  intros Hfinite Hle; destruct bound as [[s|s|s p Hp|s m e Hb] Hnan];
    try exact Hle; try discriminate Hnan.
  destruct s.
  - apply fle_finite; [reflexivity|exact Hfinite|].
    change (B2R prec emax (fl_flip (@Bmax_float prec emax Hprec Hmax)) <=
      B2R prec emax x)%R.
    rewrite fl_flip_real, fl_max_finite_real.
    pose proof (abs_B2R_le_emax_minus_prec prec emax Hprec x) as Habs.
    pose proof (Rle_abs (- B2R prec emax x)) as Hlower; rewrite Rabs_Ropp in Hlower; lra.
  - destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
      cbn [is_finite] in Hfinite; try discriminate;
      cbn [fle Bcompare B2BSN] in Hle; contradiction.
Qed.

Lemma nn_finite_clamp_upper bound x : is_finite prec emax x = true ->
  fle x (proj1_sig bound) -> fle x (proj1_sig (nn_finite_clamp bound)).
Proof.
  intros Hfinite Hle; destruct bound as [[s|s|s p Hp|s m e Hb] Hnan];
    try exact Hle; try discriminate Hnan.
  destruct s.
  - destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
      cbn [is_finite] in Hfinite; try discriminate;
      cbn [fle Bcompare B2BSN] in Hle; contradiction.
  - apply fle_finite; [exact Hfinite|reflexivity|].
    change (B2R prec emax x <= B2R prec emax (@Bmax_float prec emax Hprec Hmax))%R.
    rewrite fl_max_finite_real.
    pose proof (abs_B2R_le_emax_minus_prec prec emax Hprec x) as Habs.
    pose proof (Rle_abs (B2R prec emax x)) as Hupper; lra.
Qed.

Lemma finite_lower_not_pinf bound x : is_finite prec emax x = true ->
  fle (proj1_sig bound) x -> nn_is_pinf bound = false.
Proof.
  intros Hfinite Hle; destruct bound as [[s|s|s p Hp|s m e Hb] Hnan];
    try reflexivity; destruct s; [reflexivity|].
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    cbn [is_finite] in Hfinite; try discriminate;
    cbn [fle Bcompare B2BSN] in Hle; contradiction.
Qed.

Lemma finite_upper_not_ninf bound x : is_finite prec emax x = true ->
  fle x (proj1_sig bound) -> nn_is_ninf bound = false.
Proof.
  intros Hfinite Hle; destruct bound as [[s|s|s p Hp|s m e Hb] Hnan];
    try reflexivity; destruct s; [|reflexivity].
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    cbn [is_finite] in Hfinite; try discriminate;
    cbn [fle Bcompare B2BSN] in Hle; contradiction.
Qed.

Definition fl_finite_bounds (I : fl_interval) : option (fl_finite_bound * fl_finite_bound) :=
  let lo := fl_full_lo I in
  let hi := fl_full_hi I in
  if nn_le lo hi && negb (nn_is_pinf lo) && negb (nn_is_ninf hi)
  then Some (nn_finite_clamp lo, nn_finite_clamp hi) else None.

(** The finite envelope includes signed zeros and clamps infinite bounds to finite extrema. *)
Lemma fl_finite_bounds_sound I x : fl_gamma I x -> is_finite prec emax x = true ->
  exists lo hi, fl_finite_bounds I = Some (lo, hi) /\
    fle (proj1_sig lo) x /\ fle x (proj1_sig hi).
Proof.
  intros Hgamma Hfinite.
  destruct (fl_gamma_full_bounds I x Hgamma (fl_finite_not_nan x Hfinite)) as [Hlo Hhi].
  assert (Hactive : nn_le (fl_full_lo I) (fl_full_hi I) = true).
  { apply fl_le_spec; eapply (fle_trans _ x _);
      [apply proj2_sig|apply fl_finite_not_nan; exact Hfinite|apply proj2_sig|
        exact Hlo|exact Hhi]. }
  unfold fl_finite_bounds; rewrite Hactive,
    (finite_lower_not_pinf _ x Hfinite Hlo), (finite_upper_not_ninf _ x Hfinite Hhi).
  eexists; eexists; split; [reflexivity|]; split.
  - apply nn_finite_clamp_lower; assumption.
  - apply nn_finite_clamp_upper; assumption.
Qed.

(** * Rounded finite operations *)

Definition fl_eval_mode (nm : nan_model) (o : farith) (mode : mode) (x y : fl) : fl :=
  let choose := fun u v => exist _ (nan_choice nm o u v) (nan_choice_nan nm o u v) in
  match o with
  | FAdd => Bplus prec emax Hprec Hmax choose mode x y
  | FSub => Bminus prec emax Hprec Hmax choose mode x y
  | FMul => Bmult prec emax Hprec Hmax choose mode x y
  | FDiv => Bdiv prec emax Hprec Hmax choose mode x y
  end.

Definition fl_real_bin (o : farith) (x y : R) : R :=
  match o with
  | FAdd => (x + y)%R
  | FSub => (x - y)%R
  | FMul => (x * y)%R
  | FDiv => (x / y)%R
  end.

Definition fl_signed (s : bool) (r : R) : Prop := if s then (r <= 0)%R else (0 <= r)%R.

Lemma fl_sign_real x : fl_signed (Bsign prec emax x) (B2R prec emax x).
Proof.
  destruct x as [s|s|s p Hp|s m e Hb]; cbn [Bsign B2R];
    try solve [destruct s; cbn [fl_signed]; lra].
  pose proof (bpow_gt_0 radix2 e) as Hpow.
  pose proof (IZR_lt 0 (Z.pos m) (Pos2Z.is_pos m)) as Hmantissa.
  destruct s; unfold F2R; cbn [Fnum Fexp SpecFloat.cond_Zopp fl_signed];
    rewrite ?opp_IZR; nra.
Qed.

Lemma fl_sign_plus sx sy x y : fl_signed sx x -> fl_signed sy y -> sx = sy ->
  fl_signed sx (x + y).
Proof.
  intros Hx Hy <-; destruct sx; cbn [fl_signed] in *; lra.
Qed.

Lemma fl_sign_minus sx sy x y : fl_signed sx x -> fl_signed sy y -> sx = negb sy ->
  fl_signed sx (x - y).
Proof.
  destruct sx, sy; cbn [fl_signed negb]; intros Hx Hy Heq; try discriminate; lra.
Qed.

Lemma fl_sign_mult sx sy x y : fl_signed sx x -> fl_signed sy y ->
  fl_signed (xorb sx sy) (x * y).
Proof.
  destruct sx, sy; cbn [fl_signed xorb]; intros Hx Hy.
  - replace (x * y)%R with ((-x) * (-y))%R by ring; apply Rmult_le_pos; lra.
  - replace 0%R with (0 * y)%R by ring; apply Rmult_le_compat_r; assumption.
  - replace 0%R with (x * 0)%R by ring; apply Rmult_le_compat_l; assumption.
  - apply Rmult_le_pos; assumption.
Qed.

Lemma fl_sign_div sx sy x y : fl_signed sx x -> fl_signed sy y -> y <> 0%R ->
  fl_signed (xorb sx sy) (x / y).
Proof.
  intros Hx Hy Hnonzero; apply fl_sign_mult; [exact Hx|].
  destruct sy; cbn [fl_signed] in *.
  - apply Rlt_le, Rinv_lt_0_compat; lra.
  - apply Rlt_le, Rinv_0_lt_compat; lra.
Qed.

Lemma fl_overflow_sign mode r s : fl_signed s r ->
  Rlt_bool (Rabs (fl_round_real (round_mode mode) r)) (bpow radix2 emax) = false ->
  Rlt_bool r 0 = s.
Proof.
  intros Hsign Hoverflow.
  assert (Hnonzero : r <> 0%R).
  { intro Hz; subst r; rewrite round_0 in Hoverflow by apply valid_rnd_round_mode.
    rewrite Rabs_R0, Rlt_bool_true in Hoverflow by apply bpow_gt_0; discriminate. }
  destruct s; cbn [fl_signed] in Hsign.
  - apply Rlt_bool_true; lra.
  - apply Rlt_bool_false; exact Hsign.
Qed.

(** Finite arithmetic agrees with real rounding, including signed overflow at every mode. *)
Lemma fl_eval_mode_spec (nm : nan_model) o mode x y :
  is_finite prec emax x = true -> is_finite prec emax y = true ->
  (o = FDiv -> B2R prec emax y <> 0%R) ->
  fl_rounded_spec mode (fl_real_bin o (B2R prec emax x) (B2R prec emax y))
    (fl_eval_mode nm o mode x y).
Proof.
  intros Hx Hy Hdiv; destruct o; unfold fl_rounded_spec;
    cbn [fl_eval_mode fl_real_bin].
  - pose proof (Bplus_correct prec emax Hprec Hmax
      (fun u v => exist _ (nan_choice nm FAdd u v) (nan_choice_nan nm FAdd u v))
      mode x y Hx Hy) as Hcorrect.
    destruct (Rlt_bool (Rabs (fl_round_real (round_mode mode)
      (B2R prec emax x + B2R prec emax y))) (bpow radix2 emax)) eqn:Hnormal.
    + destruct Hcorrect as [Hreal [Hfinite Hsign]]; split; assumption.
    + destruct Hcorrect as [Hoverflow Hsame].
      rewrite (fl_overflow_sign mode _ (Bsign prec emax x)
        (fl_sign_plus _ _ _ _ (fl_sign_real x) (fl_sign_real y) Hsame) Hnormal).
      exact Hoverflow.
  - pose proof (Bminus_correct prec emax Hprec Hmax
      (fun u v => exist _ (nan_choice nm FSub u v) (nan_choice_nan nm FSub u v))
      mode x y Hx Hy) as Hcorrect.
    destruct (Rlt_bool (Rabs (fl_round_real (round_mode mode)
      (B2R prec emax x - B2R prec emax y))) (bpow radix2 emax)) eqn:Hnormal.
    + destruct Hcorrect as [Hreal [Hfinite Hsign]]; split; assumption.
    + destruct Hcorrect as [Hoverflow Hsame].
      rewrite (fl_overflow_sign mode _ (Bsign prec emax x)
        (fl_sign_minus _ _ _ _ (fl_sign_real x) (fl_sign_real y) Hsame) Hnormal).
      exact Hoverflow.
  - pose proof (Bmult_correct prec emax Hprec Hmax
      (fun u v => exist _ (nan_choice nm FMul u v) (nan_choice_nan nm FMul u v))
      mode x y) as Hcorrect.
    destruct (Rlt_bool (Rabs (fl_round_real (round_mode mode)
      (B2R prec emax x * B2R prec emax y))) (bpow radix2 emax)) eqn:Hnormal.
    + destruct Hcorrect as [Hreal [Hfinite Hsign]]; split; [|exact Hreal].
      rewrite Hx, Hy in Hfinite; exact Hfinite.
    + rewrite (fl_overflow_sign mode _ (xorb (Bsign prec emax x) (Bsign prec emax y))
        (fl_sign_mult _ _ _ _ (fl_sign_real x) (fl_sign_real y)) Hnormal).
      exact Hcorrect.
  - pose proof (Bdiv_correct prec emax Hprec Hmax
      (fun u v => exist _ (nan_choice nm FDiv u v) (nan_choice_nan nm FDiv u v))
      mode x y (Hdiv eq_refl)) as Hcorrect.
    destruct (Rlt_bool (Rabs (fl_round_real (round_mode mode)
      (B2R prec emax x / B2R prec emax y))) (bpow radix2 emax)) eqn:Hnormal.
    + destruct Hcorrect as [Hreal [Hfinite Hsign]]; split; [|exact Hreal].
      rewrite Hx in Hfinite; exact Hfinite.
    + rewrite (fl_overflow_sign mode _ (xorb (Bsign prec emax x) (Bsign prec emax y))
        (fl_sign_div _ _ _ _ (fl_sign_real x) (fl_sign_real y) (Hdiv eq_refl)) Hnormal).
      exact Hcorrect.
Qed.

(** * Directed arithmetic and exceptional values *)

Local Open Scope R_scope.

Lemma rectangle_product_lower a b c d x y :
  a <= x <= b -> c <= y <= d ->
  exists u v, (u = a \/ u = b) /\ (v = c \/ v = d) /\ u * v <= x * y.
Proof.
  intros Hx Hy; destruct (Rle_dec 0 y) as [Hypos|Hyneg].
  - destruct (Rle_dec 0 a) as [Hapos|Haneg].
    + exists a, c; repeat split; auto; nra.
    + exists a, d; repeat split; auto; nra.
  - destruct (Rle_dec 0 b) as [Hbpos|Hbneg].
    + exists b, c; repeat split; auto; nra.
    + exists b, d; repeat split; auto; nra.
Qed.

Lemma rectangle_product_upper a b c d x y :
  a <= x <= b -> c <= y <= d ->
  exists u v, (u = a \/ u = b) /\ (v = c \/ v = d) /\ x * y <= u * v.
Proof.
  intros Hx Hy; destruct (Rle_dec 0 y) as [Hypos|Hyneg].
  - destruct (Rle_dec 0 b) as [Hbpos|Hbneg].
    + exists b, d; repeat split; auto; nra.
    + exists b, c; repeat split; auto; nra.
  - destruct (Rle_dec 0 a) as [Hapos|Haneg].
    + exists a, d; repeat split; auto; nra.
    + exists a, c; repeat split; auto; nra.
Qed.

Lemma inverse_interval c d y : c <= y <= d -> (0 < c \/ d < 0) ->
  / d <= / y <= / c.
Proof.
  intros Hy [Hpos|Hneg].
  - split; apply Rinv_le_contravar; lra.
  - assert (Ha : / (- y) <= / (- d)) by (apply Rinv_le_contravar; lra).
    assert (Hb : / (- c) <= / (- y)) by (apply Rinv_le_contravar; lra).
    rewrite !Rinv_opp in Ha, Hb; lra.
Qed.

Lemma rectangle_operation_lower o a b c d x y : a <= x <= b -> c <= y <= d ->
  (o = FDiv -> 0 < c \/ d < 0) ->
  exists u v, (u = a \/ u = b) /\ (v = c \/ v = d) /\
    fl_real_bin o u v <= fl_real_bin o x y.
Proof.
  intros Hx Hy Hdiv; destruct o; cbn [fl_real_bin].
  - exists a, c; repeat split; auto; lra.
  - exists a, d; repeat split; auto; lra.
  - apply rectangle_product_lower; assumption.
  - destruct (rectangle_product_lower a b (/ d) (/ c) x (/ y) Hx
      (inverse_interval c d y Hy (Hdiv eq_refl))) as [u [v [Hu [Hv Hle]]]].
    destruct Hv as [-> | ->].
    + exists u, d; repeat split; auto.
    + exists u, c; repeat split; auto.
Qed.

Lemma rectangle_operation_upper o a b c d x y : a <= x <= b -> c <= y <= d ->
  (o = FDiv -> 0 < c \/ d < 0) ->
  exists u v, (u = a \/ u = b) /\ (v = c \/ v = d) /\
    fl_real_bin o x y <= fl_real_bin o u v.
Proof.
  intros Hx Hy Hdiv; destruct o; cbn [fl_real_bin].
  - exists b, d; repeat split; auto; lra.
  - exists b, c; repeat split; auto; lra.
  - apply rectangle_product_upper; assumption.
  - destruct (rectangle_product_upper a b (/ d) (/ c) x (/ y) Hx
      (inverse_interval c d y Hy (Hdiv eq_refl))) as [u [v [Hu [Hv Hle]]]].
    destruct Hv as [-> | ->].
    + exists u, d; repeat split; auto.
    + exists u, c; repeat split; auto.
Qed.

Local Abbreviation sfl := (BinarySingleNaN.binary_float prec emax).

Definition fl_single_bin (o : farith) (m : mode) (x y : fl) : sfl :=
  match o with
  | FAdd => @BinarySingleNaN.Bplus prec emax Hprec Hmax m
      (B2BSN prec emax x) (B2BSN prec emax y)
  | FSub => @BinarySingleNaN.Bminus prec emax Hprec Hmax m
      (B2BSN prec emax x) (B2BSN prec emax y)
  | FMul => @BinarySingleNaN.Bmult prec emax Hprec Hmax m
      (B2BSN prec emax x) (B2BSN prec emax y)
  | FDiv => @BinarySingleNaN.Bdiv prec emax Hprec Hmax m
      (B2BSN prec emax x) (B2BSN prec emax y)
  end.

Definition fl_from_single (x : sfl) : option (@fl_nn prec emax) :=
  match x with
  | BinarySingleNaN.B754_zero s => Some (exist _ (@B754_zero prec emax s) eq_refl)
  | BinarySingleNaN.B754_infinity s => Some (exist _ (@B754_infinity prec emax s) eq_refl)
  | BinarySingleNaN.B754_nan => None
  | BinarySingleNaN.B754_finite s m e Hb =>
    Some (exist _ (@B754_finite prec emax s m e Hb) eq_refl)
  end.

Lemma fl_single_eval nm o m x y :
  B2BSN prec emax (fl_eval_mode nm o m x y) = fl_single_bin o m x y.
Proof.
  destruct o; unfold fl_eval_mode, fl_single_bin, Bplus, Bminus, Bmult, Bdiv;
    apply B2BSN_BSN2B.
Qed.

Lemma fl_from_single_sound x y : is_nan prec emax y = false ->
  x = B2BSN prec emax y -> exists z, fl_from_single x = Some z /\ proj1_sig z = y.
Proof.
  intros Hnan ->; destruct y; cbn in Hnan; try discriminate;
    eexists; split; reflexivity.
Qed.

Lemma fl_single_rounded (nm : nan_model) o m x y :
  is_finite prec emax x = true ->
  is_finite prec emax y = true -> (o = FDiv -> B2R prec emax y <> 0) ->
  exists z, fl_from_single (fl_single_bin o m x y) = Some z /\
    fl_rounded_spec m (fl_real_bin o (B2R prec emax x) (B2R prec emax y)) (proj1_sig z).
Proof.
  intros Hx Hy Hdiv.
  pose proof (fl_eval_mode_spec nm o m x y Hx Hy Hdiv) as Hspec.
  destruct (fl_from_single_sound _ _ (fl_rounded_nan _ _ _ Hspec)
    (eq_sym (fl_single_eval nm o m x y))) as [z [Hz Hvalue]].
  exists z; rewrite Hvalue; auto.
Qed.

Definition fl_directed (o : farith) (m : mode) (fallback : @fl_nn prec emax)
    (x y : fl) : @fl_nn prec emax :=
  match fl_from_single (fl_single_bin o m x y) with Some z => z | None => fallback end.

Definition nn_min4 (a b c d : @fl_nn prec emax) := nn_min (nn_min a b) (nn_min c d).
Definition nn_max4 (a b c d : @fl_nn prec emax) := nn_max (nn_max a b) (nn_max c d).

Lemma nn_min4_member a b c d z : z = a \/ z = b \/ z = c \/ z = d ->
  nn_le (nn_min4 a b c d) z = true.
Proof.
  intros [-> | [-> | [-> | ->]]]; unfold nn_min4.
  - eapply nn_le_trans; [apply nn_min_l|apply nn_min_l].
  - eapply nn_le_trans; [apply nn_min_l|apply nn_min_r].
  - eapply nn_le_trans; [apply nn_min_r|apply nn_min_l].
  - eapply nn_le_trans; [apply nn_min_r|apply nn_min_r].
Qed.

Lemma nn_max4_member a b c d z : z = a \/ z = b \/ z = c \/ z = d ->
  nn_le z (nn_max4 a b c d) = true.
Proof.
  intros [-> | [-> | [-> | ->]]]; unfold nn_max4.
  - eapply nn_le_trans; [apply nn_max_l|apply nn_max_l].
  - eapply nn_le_trans; [apply nn_max_r|apply nn_max_l].
  - eapply nn_le_trans; [apply nn_max_l|apply nn_max_r].
  - eapply nn_le_trans; [apply nn_max_r|apply nn_max_r].
Qed.

Definition fl_lower_corners o a b c d : @fl_nn prec emax :=
  nn_min4 (fl_directed o mode_DN fl_ninf a c) (fl_directed o mode_DN fl_ninf a d)
    (fl_directed o mode_DN fl_ninf b c) (fl_directed o mode_DN fl_ninf b d).

Definition fl_upper_corners o a b c d : @fl_nn prec emax :=
  nn_max4 (fl_directed o mode_UP fl_pinf a c) (fl_directed o mode_UP fl_pinf a d)
    (fl_directed o mode_UP fl_pinf b c) (fl_directed o mode_UP fl_pinf b d).

Lemma fl_directed_spec (nm : nan_model) o m fallback x y :
  is_finite prec emax x = true -> is_finite prec emax y = true ->
  (o = FDiv -> B2R prec emax y <> 0) ->
  fl_rounded_spec m (fl_real_bin o (B2R prec emax x) (B2R prec emax y))
    (proj1_sig (fl_directed o m fallback x y)).
Proof.
  intros Hx Hy Hdiv; destruct (fl_single_rounded nm o m x y Hx Hy Hdiv) as [z [Hz Hspec]].
  unfold fl_directed; rewrite Hz; exact Hspec.
Qed.

Lemma fle_finite_real x y : is_finite prec emax x = true ->
  is_finite prec emax y = true -> fle x y -> B2R prec emax x <= B2R prec emax y.
Proof.
  intros Hx Hy Hle; apply (proj1 (fle_order _ _
    (fl_finite_not_nan _ Hx) (fl_finite_not_nan _ Hy))) in Hle.
  destruct x, y; cbn in Hx, Hy; try discriminate; exact Hle.
Qed.

Lemma fl_corners_sound nm o (a b c d : fl_finite_bound) x y :
  is_finite prec emax x = true -> is_finite prec emax y = true ->
  fle (proj1_sig a) x -> fle x (proj1_sig b) ->
  fle (proj1_sig c) y -> fle y (proj1_sig d) ->
  (o = FDiv -> 0 < B2R prec emax (proj1_sig c) \/ B2R prec emax (proj1_sig d) < 0) ->
  fle (proj1_sig (fl_lower_corners o (proj1_sig a) (proj1_sig b) (proj1_sig c)
    (proj1_sig d))) (fl_eval_bin nm o x y) /\
  fle (fl_eval_bin nm o x y) (proj1_sig (fl_upper_corners o (proj1_sig a) (proj1_sig b)
    (proj1_sig c) (proj1_sig d))).
Proof.
  intros Hx Hy Hax Hxb Hcy Hyd Hdiv.
  assert (Hxrange : B2R prec emax (proj1_sig a) <= B2R prec emax x <=
      B2R prec emax (proj1_sig b)).
  { split; eapply fle_finite_real; try apply proj2_sig; eassumption. }
  assert (Hyrange : B2R prec emax (proj1_sig c) <= B2R prec emax y <=
      B2R prec emax (proj1_sig d)).
  { split; eapply fle_finite_real; try apply proj2_sig; eassumption. }
  assert (Hnz : o = FDiv -> B2R prec emax y <> 0)
    by (intro Ho; destruct (Hdiv Ho); lra).
  pose proof (fl_eval_mode_spec nm o mode_NE x y Hx Hy Hnz) as Hresult.
  change (fl_rounded_spec mode_NE (fl_real_bin o (B2R prec emax x) (B2R prec emax y))
    (fl_eval_bin nm o x y)) in Hresult.
  split.
  - destruct (rectangle_operation_lower o _ _ _ _ _ _ Hxrange Hyrange Hdiv)
      as [u [v [Hu [Hv Hle]]]].
    destruct Hu as [-> | ->]; destruct Hv as [-> | ->].
    all: match type of Hle with
    | fl_real_bin _ (B2R _ _ ?u) (B2R _ _ ?v) <= _ =>
      eapply fle_trans with (y := proj1_sig (fl_directed o mode_DN fl_ninf u v))
    end; [apply proj2_sig|apply proj2_sig|exact (fl_rounded_nan _ _ _ Hresult)| |].
    all: unfold fl_lower_corners.
    all: try (apply fl_le_spec, nn_min4_member; auto).
    all: eapply fl_rounded_lower; [eapply (fl_directed_spec nm); try apply proj2_sig|
      exact Hresult|exact Hle].
    all: intro Ho; destruct (Hdiv Ho); lra.
  - destruct (rectangle_operation_upper o _ _ _ _ _ _ Hxrange Hyrange Hdiv)
      as [u [v [Hu [Hv Hle]]]].
    destruct Hu as [-> | ->]; destruct Hv as [-> | ->].
    all: match type of Hle with
    | _ <= fl_real_bin _ (B2R _ _ ?u) (B2R _ _ ?v) =>
      eapply fle_trans with (y := proj1_sig (fl_directed o mode_UP fl_pinf u v))
    end; [exact (fl_rounded_nan _ _ _ Hresult)|apply proj2_sig|apply proj2_sig| |].
    all: unfold fl_upper_corners.
    all: try (apply fl_le_spec, nn_max4_member; auto).
    all: eapply fl_rounded_upper; [exact Hresult|
      eapply (fl_directed_spec nm); try apply proj2_sig|exact Hle].
    all: intro Ho; destruct (Hdiv Ho); lra.
Qed.

Definition fl_normal_bound : @fl_nn prec emax := exist _ fl_min_normal
  (fl_finite_not_nan _ (proj2 fl_min_normal_correct)).

Definition fl_zero_range (lo hi : @fl_nn prec emax) : bool :=
  nn_le lo fl_zero && nn_le fl_zero hi.

Definition fl_nonzero_range (lo hi : @fl_nn prec emax) : bool :=
  negb (nn_le fl_zero lo && nn_le hi fl_zero).

Definition fl_subnormal_range (lo hi : @fl_nn prec emax) : bool :=
  negb (nn_le fl_normal_bound lo) && negb (nn_le hi (nn_neg fl_normal_bound)) &&
    fl_nonzero_range lo hi.

Lemma fl_zero_range_sound lo hi s :
  fle (proj1_sig lo) (@B754_zero prec emax s) ->
  fle (@B754_zero prec emax s) (proj1_sig hi) -> fl_zero_range lo hi = true.
Proof.
  intros Hlo Hhi; apply andb_true_iff; split; apply fl_le_spec.
  - eapply fle_trans with (y := @B754_zero prec emax s).
    + apply proj2_sig.
    + reflexivity.
    + reflexivity.
    + exact Hlo.
    + destruct s; exact I.
  - eapply fle_trans with (y := @B754_zero prec emax s).
    + reflexivity.
    + reflexivity.
    + apply proj2_sig.
    + destruct s; exact I.
    + exact Hhi.
Qed.

Lemma fl_nonzero_range_sound lo hi x : fle (proj1_sig lo) x -> fle x (proj1_sig hi) ->
  is_finite prec emax x = true -> B2R prec emax x <> 0 -> fl_nonzero_range lo hi = true.
Proof.
  intros Hlo Hhi Hfinite Hnonzero; apply negb_true_iff; apply not_true_is_false; intro Hbad.
  apply andb_true_iff in Hbad as [Hlower Hupper].
  apply fl_le_spec in Hlower; apply fl_le_spec in Hupper.
  assert (Hlozero : fle (@B754_zero prec emax false) x).
  { eapply fle_trans with (y := proj1_sig lo);
      [reflexivity|apply proj2_sig|apply fl_finite_not_nan; exact Hfinite|
        exact Hlower|exact Hlo]. }
  assert (Hhizero : fle x (@B754_zero prec emax false)).
  { eapply fle_trans with (y := proj1_sig hi);
      [apply fl_finite_not_nan; exact Hfinite|apply proj2_sig|reflexivity|
        exact Hhi|exact Hupper]. }
  pose proof (fle_finite_real (@B754_zero prec emax false) x eq_refl Hfinite Hlozero).
  pose proof (fle_finite_real x (@B754_zero prec emax false) Hfinite eq_refl Hhizero).
  apply Hnonzero; change (B2R prec emax x = B2R prec emax (@B754_zero prec emax false)); lra.
Qed.

Lemma fl_subnormal_range_sound lo hi x :
  fle (proj1_sig lo) x -> fle x (proj1_sig hi) ->
  subnormal x -> fl_subnormal_range lo hi = true.
Proof.
  intros Hlo Hhi [Hfinite [Hnonzero Hsmall]].
  pose proof (proj1 fl_min_normal_correct) as Hnormal.
  pose proof (proj2 fl_min_normal_correct) as Hnormal_finite.
  pose proof (Rle_abs (B2R prec emax x)) as Habs.
  pose proof (Rle_abs (- B2R prec emax x)) as Habsneg; rewrite Rabs_Ropp in Habsneg.
  apply andb_true_iff; split; [|exact (fl_nonzero_range_sound lo hi x Hlo Hhi Hfinite Hnonzero)].
  apply andb_true_iff; split; apply negb_true_iff; apply not_true_is_false; intro Hbad.
  - apply fl_le_spec in Hbad.
    assert (Hle : fle fl_min_normal x).
    { eapply fle_trans with (y := proj1_sig lo);
        [exact (proj2_sig fl_normal_bound)|apply proj2_sig|
        apply fl_finite_not_nan; exact Hfinite|exact Hbad|exact Hlo]. }
    pose proof (fle_finite_real _ _ Hnormal_finite Hfinite Hle); lra.
  - apply fl_le_spec in Hbad.
    assert (Hneg_finite : is_finite prec emax (fl_flip fl_min_normal) = true)
      by (destruct fl_min_normal; exact Hnormal_finite).
    assert (Hle : fle x (fl_flip fl_min_normal)).
    { eapply fle_trans with (y := proj1_sig hi);
        [apply fl_finite_not_nan; exact Hfinite|apply proj2_sig|
        exact (proj2_sig (nn_neg fl_normal_bound))|exact Hhi|exact Hbad]. }
    pose proof (fle_finite_real _ _ Hfinite Hneg_finite Hle) as Hreal.
    rewrite fl_flip_real, Hnormal in Hreal; lra.
Qed.

(** A zero-containing range retains both zero signs; subnormality follows the normal threshold. *)
Definition fl_bounds_interval (lo hi : @fl_nn prec emax) : @fl_interval prec emax :=
  FlInterval lo hi false (fl_zero_range lo hi) (fl_zero_range lo hi)
    (fl_subnormal_range lo hi).

Lemma fl_bounds_interval_sound lo hi x : is_nan prec emax x = false ->
  fle (proj1_sig lo) x -> fle x (proj1_sig hi) -> fl_gamma (fl_bounds_interval lo hi) x.
Proof.
  intros Hnan Hlo Hhi; destruct x as [s|s|s p Hp|s m e Hb];
    cbn [is_nan] in Hnan; try discriminate;
    cbn [fl_gamma B2FF fl_bounds_interval flo fhi may_nan may_neg_zero may_pos_zero
      may_subnormal].
  - pose proof (fl_zero_range_sound lo hi s Hlo Hhi); destruct s; assumption.
  - split; [exact Hlo|split; [exact Hhi|]].
    apply fl_subnormal_range_sound; assumption.
  - split; [exact Hlo|split; [exact Hhi|]].
    apply fl_subnormal_range_sound; assumption.
Qed.

Lemma fl_lt_finite_spec x y : is_finite prec emax x = true ->
  is_finite prec emax y = true ->
  (fl_lt x y = true <-> B2R prec emax x < B2R prec emax y).
Proof.
  intros Hx Hy; unfold fl_lt; rewrite Bcompare_correct by assumption.
  destruct (Rcompare_spec (B2R prec emax x) (B2R prec emax y)); cbn;
    split; intro Hlt; try reflexivity; try discriminate; lra.
Qed.

Definition fl_denominator_safe o (lo hi : fl_finite_bound) : bool :=
  match o with
  | FDiv => fl_lt (@B754_zero prec emax false) (proj1_sig lo) ||
      fl_lt (proj1_sig hi) (@B754_zero prec emax false)
  | _ => true
  end.

Lemma fl_denominator_safe_sound o lo hi : fl_denominator_safe o lo hi = true ->
  o = FDiv -> 0 < B2R prec emax (proj1_sig lo) \/ B2R prec emax (proj1_sig hi) < 0.
Proof.
  intros Hsafe ->; apply orb_true_iff in Hsafe as [Hpos|Hneg].
  - left; exact (proj1 (fl_lt_finite_spec (@B754_zero prec emax false)
      (proj1_sig lo) eq_refl (proj2_sig lo)) Hpos).
  - right; exact (proj1 (fl_lt_finite_spec (proj1_sig hi)
      (@B754_zero prec emax false) (proj2_sig hi) eq_refl) Hneg).
Qed.

Definition fl_only_zero (lo hi : fl_finite_bound) : bool :=
  nn_le fl_zero (fl_finite_nn lo) && nn_le (fl_finite_nn hi) fl_zero.

Lemma fl_only_zero_sound lo hi y : fl_only_zero lo hi = true ->
  is_finite prec emax y = true -> fle (proj1_sig lo) y -> fle y (proj1_sig hi) ->
  B2R prec emax y = 0.
Proof.
  intros Hzero Hfinite Hlo Hhi; apply andb_true_iff in Hzero as [Hlower Hupper].
  apply fl_le_spec in Hlower; apply fl_le_spec in Hupper.
  pose proof (fle_finite_real _ _ (proj2_sig lo) Hfinite Hlo) as Hylower.
  pose proof (fle_finite_real _ _ Hfinite (proj2_sig hi) Hhi) as Hyupper.
  pose proof (fle_finite_real (@B754_zero prec emax false) (proj1_sig lo)
    eq_refl (proj2_sig lo) Hlower) as Hnonnegative.
  pose proof (fle_finite_real (proj1_sig hi) (@B754_zero prec emax false)
    (proj2_sig hi) eq_refl Hupper) as Hnonpositive.
  change (0 <= B2R prec emax (proj1_sig lo)) in Hnonnegative.
  change (B2R prec emax (proj1_sig hi) <= 0) in Hnonpositive; lra.
Qed.

(** Division through zero uses the full ordered hull; a zero-only divisor adds no finite case. *)
Definition fl_finite_bin o (I J : @fl_interval prec emax) : @fl_interval prec emax :=
  match fl_finite_bounds I, fl_finite_bounds J with
  | Some (a, b), Some (c, d) =>
    if fl_denominator_safe o c d then
      fl_bounds_interval
        (fl_lower_corners o (proj1_sig a) (proj1_sig b) (proj1_sig c) (proj1_sig d))
        (fl_upper_corners o (proj1_sig a) (proj1_sig b) (proj1_sig c) (proj1_sig d))
    else if fl_only_zero c d then fl_bottom else fl_bounds_interval fl_ninf fl_pinf
  | _, _ => fl_bottom
  end.

Lemma fl_finite_bin_sound nm o I J x y : fl_gamma I x -> fl_gamma J y ->
  is_finite prec emax x = true -> is_finite prec emax y = true ->
  (o = FDiv -> B2R prec emax y <> 0) ->
  fl_gamma (fl_finite_bin o I J) (fl_eval_bin nm o x y).
Proof.
  intros Hix Hjy Hx Hy Hdiv.
  destruct (fl_finite_bounds_sound I x Hix Hx) as [a [b [HI [Hax Hxb]]]].
  destruct (fl_finite_bounds_sound J y Hjy Hy) as [c [d [HJ [Hcy Hyd]]]].
  pose proof (fl_eval_mode_spec nm o mode_NE x y Hx Hy Hdiv) as Hspec.
  assert (Hnan : is_nan prec emax (fl_eval_bin nm o x y) = false)
    by (exact (fl_rounded_nan _ _ _ Hspec)).
  unfold fl_finite_bin; rewrite HI, HJ.
  destruct (fl_denominator_safe o c d) eqn:Hsafe.
  - apply fl_bounds_interval_sound; [exact Hnan| |].
    + exact (proj1 (fl_corners_sound nm o a b c d x y Hx Hy Hax Hxb Hcy Hyd
      (fl_denominator_safe_sound o c d Hsafe))).
    + exact (proj2 (fl_corners_sound nm o a b c d x y Hx Hy Hax Hxb Hcy Hyd
      (fl_denominator_safe_sound o c d Hsafe))).
  - destruct (fl_only_zero c d) eqn:Hzero.
    + assert (Ho : o = FDiv) by (destruct o; try discriminate; reflexivity).
      exfalso; exact (Hdiv Ho (fl_only_zero_sound c d y Hzero Hy Hcy Hyd)).
    + apply fl_bounds_interval_sound; [exact Hnan|apply fle_ninf; exact Hnan|
        apply fle_pinf; exact Hnan].
Qed.

Inductive fl_class : Type :=
  | FlNaN
  | FlInfinity (negative : bool)
  | FlZero (negative : bool)
  | FlFinite (negative : bool).

Definition fl_class_of (x : fl) : fl_class :=
  match x with
  | @B754_nan _ _ _ _ _ => FlNaN
  | @B754_infinity _ _ s => FlInfinity s
  | @B754_zero _ _ s => FlZero s
  | @B754_finite _ _ s _ _ _ => FlFinite s
  end.

Definition fl_class_result (o : farith) (a b : fl_class) : option fl_class :=
  match a, b with
  | FlNaN, _ | _, FlNaN => Some FlNaN
  | _, _ =>
    match o with
    | FAdd =>
      match a, b with
      | FlInfinity s, FlInfinity t =>
        Some (if Bool.eqb s t then FlInfinity s else FlNaN)
      | FlInfinity s, _ | _, FlInfinity s => Some (FlInfinity s)
      | _, _ => None
      end
    | FSub =>
      match a, b with
      | FlInfinity s, FlInfinity t =>
        Some (if Bool.eqb s t then FlNaN else FlInfinity s)
      | FlInfinity s, _ => Some (FlInfinity s)
      | _, FlInfinity t => Some (FlInfinity (negb t))
      | _, _ => None
      end
    | FMul =>
      match a, b with
      | FlInfinity _, FlZero _ | FlZero _, FlInfinity _ => Some FlNaN
      | FlInfinity s, FlInfinity t | FlInfinity s, FlFinite t
      | FlFinite s, FlInfinity t => Some (FlInfinity (xorb s t))
      | _, _ => None
      end
    | FDiv =>
      match a, b with
      | FlInfinity _, FlInfinity _ | FlZero _, FlZero _ => Some FlNaN
      | FlInfinity s, FlZero t | FlInfinity s, FlFinite t
      | FlFinite s, FlZero t => Some (FlInfinity (xorb s t))
      | FlZero s, FlInfinity t | FlFinite s, FlInfinity t =>
        Some (FlZero (xorb s t))
      | _, _ => None
      end
    end
  end.

Lemma fl_finite_strict_sign (s : bool) m e Hb :
  if s then B2R prec emax (@B754_finite prec emax s m e Hb) < 0
  else 0 < B2R prec emax (@B754_finite prec emax s m e Hb).
Proof.
  pose proof (bpow_gt_0 radix2 e) as Hpow.
  pose proof (IZR_lt 0 (Z.pos m) (Pos2Z.is_pos m)) as Hmantissa.
  destruct s; cbn [B2R]; unfold F2R; cbn [Fnum Fexp SpecFloat.cond_Zopp];
    rewrite ?opp_IZR; nra.
Qed.

Lemma fl_class_nan x : is_nan prec emax x = true -> fl_class_of x = FlNaN.
Proof.
  destruct x; cbn; intro Hnan; try discriminate; reflexivity.
Qed.

Lemma fl_class_result_sound nm o x y :
  match fl_class_result o (fl_class_of x) (fl_class_of y) with
  | Some c => fl_class_of (fl_eval_bin nm o x y) = c
  | None => is_finite prec emax x = true /\ is_finite prec emax y = true /\
      (o = FDiv -> B2R prec emax y <> 0)
  end.
Proof.
  destruct o; destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    destruct y as [sy|sy|sy py Hpy|sy my ey Hyb];
    destruct sx, sy; cbn [fl_class_of fl_class_result].
  all: try solve [split; [reflexivity|]; split; [reflexivity|]; intro Ho;
    try discriminate; intro Hzero;
    match type of Hzero with
    | B2R _ _ (@B754_finite _ _ ?s ?m ?e ?Hb) = 0 =>
      pose proof (fl_finite_strict_sign s m e Hb) as Hsign; cbn -[B2R] in Hsign; lra
    end].
  all: cbn [fl_eval_bin Bplus Bminus Bmult Bdiv B2BSN
    BinarySingleNaN.Bplus BinarySingleNaN.Bminus BinarySingleNaN.Bmult
    BinarySingleNaN.Bdiv BSN2B]; try reflexivity.
  all: apply fl_class_nan, nan_choice_nan.
Qed.

Definition fl_has_class (I : @fl_interval prec emax) (c : fl_class) : bool :=
  match c with
  | FlNaN => may_nan I
  | FlZero s => if s then may_neg_zero I else may_pos_zero I
  | FlInfinity s => fl_active I &&
      if s then nn_le (flo I) fl_ninf else nn_le fl_pinf (fhi I)
  | FlFinite s =>
    match fl_finite_bounds I with
    | Some (lo, hi) =>
      if s then negb (nn_le fl_zero (fl_finite_nn lo))
      else negb (nn_le (fl_finite_nn hi) fl_zero)
    | None => false
    end
  end.

Lemma fl_bounds_active I x : is_nan prec emax x = false ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) -> fl_active I = true.
Proof.
  intros Hnan Hlo Hhi; eapply fl_le_trans;
    [apply proj2_sig|exact Hnan|apply proj2_sig|apply fl_le_spec; exact Hlo|
      apply fl_le_spec; exact Hhi].
Qed.

Lemma fl_has_class_sound I x : fl_gamma I x -> fl_has_class I (fl_class_of x) = true.
Proof.
  destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_gamma B2FF fl_class_of fl_has_class]; intro Hgamma; try exact Hgamma.
  - destruct Hgamma as [Hlo [Hhi Hsub]].
    rewrite (fl_bounds_active I (@B754_infinity prec emax s) eq_refl Hlo Hhi); cbn.
    destruct s; apply fl_le_spec; assumption.
  - destruct Hgamma as [Hlo [Hhi Hsub]].
    destruct (fl_finite_bounds_sound I (@B754_finite prec emax s m e Hb)
      (conj Hlo (conj Hhi Hsub)) eq_refl) as [lo [hi [Hbounds [Hlower Hupper]]]].
    rewrite Hbounds.
    pose proof (fl_finite_strict_sign s m e Hb) as Hsign.
    destruct s; cbn -[B2R] in Hsign; apply negb_true_iff;
      apply not_true_is_false; intro Hbad; apply fl_le_spec in Hbad.
    + assert (Hle : fle (@B754_zero prec emax false) (@B754_finite prec emax true m e Hb)).
      { eapply fle_trans with (y := proj1_sig lo);
          [reflexivity|exact (proj2_sig (fl_finite_nn lo))|reflexivity|
            exact Hbad|exact Hlower]. }
      pose proof (fle_finite_real (@B754_zero prec emax false)
        (@B754_finite prec emax true m e Hb) eq_refl eq_refl Hle) as Hreal.
      change (0 <= B2R prec emax (@B754_finite prec emax true m e Hb)) in Hreal; lra.
    + assert (Hle : fle (@B754_finite prec emax false m e Hb) (@B754_zero prec emax false)).
      { eapply fle_trans with (y := proj1_sig hi);
          [reflexivity|exact (proj2_sig (fl_finite_nn hi))|reflexivity|
            exact Hupper|exact Hbad]. }
      pose proof (fle_finite_real (@B754_finite prec emax false m e Hb)
        (@B754_zero prec emax false) eq_refl eq_refl Hle) as Hreal.
      change (B2R prec emax (@B754_finite prec emax false m e Hb) <= 0) in Hreal; lra.
Qed.

Definition fl_class_interval (c : fl_class) : @fl_interval prec emax :=
  match c with
  | FlNaN => FlInterval fl_pinf fl_ninf true false false false
  | FlInfinity s =>
    let x := exist _ (@B754_infinity prec emax s) eq_refl in
    FlInterval x x false false false false
  | FlZero s => FlInterval fl_pinf fl_ninf false s (negb s) false
  | FlFinite _ => fl_top
  end.

Lemma fl_class_interval_sound c x : fl_class_of x = c -> fl_gamma (fl_class_interval c) x.
Proof.
  intros <-; destruct x as [s|s|s p Hp|s m e Hb];
    cbn [fl_class_of fl_class_interval fl_gamma B2FF flo fhi may_nan may_neg_zero
      may_pos_zero may_subnormal proj1_sig].
  - destruct s; reflexivity.
  - split; [|split].
    + apply fl_le_spec, fl_le_refl; reflexivity.
    + apply fl_le_spec, fl_le_refl; reflexivity.
    + intros [Hfinite _]; discriminate Hfinite.
  - reflexivity.
  - exact (fl_top_sound (@B754_finite prec emax s m e Hb)).
Qed.

Definition fl_join7 (a b c d e f g : @fl_interval prec emax) : @fl_interval prec emax :=
  fl_join a (fl_join b (fl_join c (fl_join d (fl_join e (fl_join f g))))).

Lemma fl_join7_member a b c d e f g z :
  z = a \/ z = b \/ z = c \/ z = d \/ z = e \/ z = f \/ z = g ->
  fl_leb z (fl_join7 a b c d e f g) = true.
Proof.
  intros [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; unfold fl_join7.
  all: repeat first [apply fl_leb_refl|apply fl_join_upper_l|
    eapply fl_leb_trans; [|apply fl_join_upper_r]].
Qed.

Definition fl_special_pair o I J a b : @fl_interval prec emax :=
  if fl_has_class I a && fl_has_class J b then
    match fl_class_result o a b with Some c => fl_class_interval c | None => fl_bottom end
  else fl_bottom.

Definition fl_special_row o I J a : @fl_interval prec emax :=
  fl_join7 (fl_special_pair o I J a FlNaN)
    (fl_special_pair o I J a (FlInfinity true)) (fl_special_pair o I J a (FlInfinity false))
    (fl_special_pair o I J a (FlZero true)) (fl_special_pair o I J a (FlZero false))
    (fl_special_pair o I J a (FlFinite true)) (fl_special_pair o I J a (FlFinite false)).

(** The fixed category product adds exceptional IEEE outputs without enumerating float values. *)
Definition fl_special_bin o I J : @fl_interval prec emax :=
  fl_join7 (fl_special_row o I J FlNaN)
    (fl_special_row o I J (FlInfinity true)) (fl_special_row o I J (FlInfinity false))
    (fl_special_row o I J (FlZero true)) (fl_special_row o I J (FlZero false))
    (fl_special_row o I J (FlFinite true)) (fl_special_row o I J (FlFinite false)).

Lemma fl_special_pair_upper o I J a b :
  fl_leb (fl_special_pair o I J a b) (fl_special_bin o I J) = true.
Proof.
  eapply fl_leb_trans with (J := fl_special_row o I J a).
  - unfold fl_special_row; apply fl_join7_member; destruct b as [|[]|[]|[]]; auto 7.
  - unfold fl_special_bin; apply fl_join7_member; destruct a as [|[]|[]|[]]; auto 7.
Qed.

Definition fl_bin (o : farith) (I J : @fl_interval prec emax) : @fl_interval prec emax :=
  fl_join (fl_finite_bin o I J) (fl_special_bin o I J).

(** Directed finite enclosures and the exceptional-value table cover every concrete result. *)
Theorem fl_bin_sound (nm : nan_model) (o : farith)
    (I J : @fl_interval prec emax) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> fl_gamma (fl_bin o I J) (fl_eval_bin nm o x y).
Proof.
  intros Hix Hjy; pose proof (fl_class_result_sound nm o x y) as Hresult.
  destruct (fl_class_result o (fl_class_of x) (fl_class_of y)) as [c|] eqn:Hclass.
  - eapply fl_gamma_mono; [apply fl_join_upper_r|].
    eapply fl_gamma_mono; [apply fl_special_pair_upper|].
    unfold fl_special_pair; rewrite (fl_has_class_sound I x Hix),
      (fl_has_class_sound J y Hjy), Hclass; cbn.
    apply fl_class_interval_sound; exact Hresult.
  - destruct Hresult as [Hx [Hy Hdiv]].
    eapply fl_gamma_mono; [apply fl_join_upper_l|].
    apply fl_finite_bin_sound; assumption.
Qed.

End Float.
