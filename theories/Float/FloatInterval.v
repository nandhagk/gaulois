(** * Floating-point intervals

    Non-NaN bounds enclose nonzero values, while separate flags retain exceptional values.
    For example, the two signed zeros can be distinguished even when their bounds coincide.
    Builds on: Flocq Binary and Order lattice and concretisation dictionaries. *)

From Stdlib Require Import Bool ZArith Reals Lra Lia.
From Flocq Require Import Core IEEE754.BinarySingleNaN IEEE754.Binary.
From Gaulois.Order Require Import OrderLattice OrderConcrete.

Local Arguments B754_zero {prec emax} _.
Local Arguments B754_infinity {prec emax} _.
Local Arguments B754_nan {prec emax} _ _ _.
Local Arguments B754_finite {prec emax} _ _ _ _.

Section Float.
Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}.
Local Abbreviation fl := (binary_float prec emax).

(** Ordered comparison accepts equality, including the two signs of zero. *)
Definition fle (x y : fl) : Prop :=
  match Bcompare prec emax x y with
  | Some Lt | Some Eq => True
  | _ => False
  end.

(** Subnormal values are finite, nonzero and smaller in magnitude than the normal threshold. *)
Definition subnormal (x : fl) : Prop :=
  is_finite prec emax x = true /\ B2R prec emax x <> 0%R /\
  (Rabs (B2R prec emax x) < bpow radix2 (2 - emax))%R.

(** A bound excludes NaN but includes either infinity and either zero. *)
Definition fl_nn : Type := {x : fl | is_nan prec emax x = false}.

(** Bounds describe nonzero values independently of the four exceptional-value flags. *)
Record fl_interval : Type := FlInterval {
  flo : fl_nn;
  fhi : fl_nn;
  may_nan : bool;
  may_neg_zero : bool;
  may_pos_zero : bool;
  may_subnormal : bool
}.

(** Concrete membership retains signed zeros and NaNs separately from ordered values. *)
Definition fl_gamma (I : fl_interval) (x : fl) : Prop :=
  match B2FF prec emax x with
  | F754_nan _ _ => may_nan I = true
  | F754_zero s => (if s then may_neg_zero I else may_pos_zero I) = true
  | _ => fle (proj1_sig (flo I)) x /\ fle x (proj1_sig (fhi I)) /\
      (subnormal x -> may_subnormal I = true)
  end.

Definition fl_le (x y : fl) : bool :=
  match Bcompare prec emax x y with
  | Some Lt | Some Eq => true
  | _ => false
  end.

Lemma fl_le_spec x y : fl_le x y = true <-> fle x y.
Proof.
  unfold fl_le, fle; destruct (Bcompare prec emax x y) as [[]|]; cbn; intuition discriminate.
Qed.

(** Extended real order is used only to prove the executable Flocq comparison laws. *)
Definition fl_order (x y : fl) : Prop :=
  match x, y with
  | B754_infinity true, _ => True
  | _, B754_infinity false => True
  | B754_infinity false, _ => False
  | _, B754_infinity true => False
  | _, _ => (B2R prec emax x <= B2R prec emax y)%R
  end.

Lemma fle_order x y : is_nan prec emax x = false -> is_nan prec emax y = false ->
  (fle x y <-> fl_order x y).
Proof.
  intros Hx Hy; unfold fle, fl_order.
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxbound];
    destruct y as [sy|sy|sy py Hpy|sy my ey Hybound];
    cbn [is_nan] in Hx, Hy; try discriminate.
  all: try solve [destruct sx; destruct sy; cbn [Bcompare B2BSN]; tauto].
  all: try solve [destruct sx; cbn [Bcompare B2BSN]; tauto].
  all: try solve [destruct sy; cbn [Bcompare B2BSN]; tauto].
  all: rewrite Bcompare_correct by reflexivity.
  all: match goal with
  | |- context [Rcompare ?a ?b] => destruct (Rcompare_spec a b)
  end; cbn [B2R] in *; split; intros; try tauto; lra.
Qed.

Lemma fl_le_refl x : is_nan prec emax x = false -> fl_le x x = true.
Proof.
  intro Hx; apply fl_le_spec, (proj2 (fle_order x x Hx Hx)).
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hbound];
    cbn [is_nan] in Hx; try discriminate; cbn [fl_order]; try lra.
  destruct sx; exact I.
Qed.

Lemma fl_le_trans x y z :
  is_nan prec emax x = false -> is_nan prec emax y = false ->
  is_nan prec emax z = false ->
  fl_le x y = true -> fl_le y z = true -> fl_le x z = true.
Proof.
  intros Hx Hy Hz Hxy Hyz; apply fl_le_spec, (proj2 (fle_order x z Hx Hz)).
  apply fl_le_spec, (proj1 (fle_order x y Hx Hy)) in Hxy.
  apply fl_le_spec, (proj1 (fle_order y z Hy Hz)) in Hyz.
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    destruct y as [sy|sy|sy py Hpy|sy my ey Hyb];
    destruct z as [sz|sz|sz pz Hpz|sz mz ez Hzb];
    cbn [is_nan] in Hx, Hy, Hz; try discriminate;
    unfold fl_order in *;
    repeat match goal with
    | s : bool |- _ => destruct s
    end; cbn in *; tauto || lra.
Qed.

Lemma fl_le_total x y : is_nan prec emax x = false -> is_nan prec emax y = false ->
  fl_le x y = true \/ fl_le y x = true.
Proof.
  intros Hx Hy.
  destruct (fl_le x y) eqn:Hxy; [now left|right].
  apply fl_le_spec, (proj2 (fle_order y x Hy Hx)).
  assert (Hnot : ~ fl_order x y).
  { intro Horder; apply (proj2 (fle_order x y Hx Hy)), fl_le_spec in Horder; congruence. }
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb];
    destruct y as [sy|sy|sy py Hpy|sy my ey Hyb];
    cbn [is_nan] in Hx, Hy; try discriminate;
    unfold fl_order in *;
    repeat match goal with
    | s : bool |- _ => destruct s
    end; cbn in *; tauto || lra.
Qed.

Definition fl_ninf : fl_nn := exist _ (B754_infinity true) eq_refl.
Definition fl_pinf : fl_nn := exist _ (B754_infinity false) eq_refl.
Definition nn_le (x y : fl_nn) : bool := fl_le (proj1_sig x) (proj1_sig y).

Lemma nn_le_refl x : nn_le x x = true.
Proof.
  apply fl_le_refl, proj2_sig.
Qed.

Lemma nn_le_trans x y z : nn_le x y = true -> nn_le y z = true -> nn_le x z = true.
Proof.
  apply fl_le_trans; apply proj2_sig.
Qed.

Lemma nn_le_total x y : nn_le x y = true \/ nn_le y x = true.
Proof.
  apply fl_le_total; apply proj2_sig.
Qed.

Lemma nn_ninf_le x : nn_le fl_ninf x = true.
Proof.
  destruct x as [x Hx].
  apply fl_le_spec, (proj2 (fle_order (B754_infinity true) x eq_refl Hx)); exact I.
Qed.

Lemma nn_le_pinf x : nn_le x fl_pinf = true.
Proof.
  destruct x as [x Hx].
  apply fl_le_spec, (proj2 (fle_order x (B754_infinity false) Hx eq_refl)).
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hxb]; cbn [fl_order]; try exact I.
  destruct sx; exact I.
Qed.

Definition nn_min (x y : fl_nn) : fl_nn := if nn_le x y then x else y.
Definition nn_max (x y : fl_nn) : fl_nn := if nn_le x y then y else x.

Lemma nn_min_l x y : nn_le (nn_min x y) x = true.
Proof.
  unfold nn_min; destruct (nn_le x y) eqn:Hxy; [apply nn_le_refl|].
  destruct (nn_le_total x y); congruence.
Qed.

Lemma nn_min_r x y : nn_le (nn_min x y) y = true.
Proof.
  unfold nn_min; destruct (nn_le x y) eqn:Hxy; [exact Hxy|apply nn_le_refl].
Qed.

Lemma nn_max_l x y : nn_le x (nn_max x y) = true.
Proof.
  unfold nn_max; destruct (nn_le x y) eqn:Hxy; [exact Hxy|apply nn_le_refl].
Qed.

Lemma nn_max_r x y : nn_le y (nn_max x y) = true.
Proof.
  unfold nn_max; destruct (nn_le x y) eqn:Hxy; [apply nn_le_refl|].
  destruct (nn_le_total x y); congruence.
Qed.

Definition fl_flags_le (I J : fl_interval) : bool :=
  implb (may_nan I) (may_nan J) && implb (may_neg_zero I) (may_neg_zero J) &&
  implb (may_pos_zero I) (may_pos_zero J) && implb (may_subnormal I) (may_subnormal J).

Definition fl_active (I : fl_interval) : bool := nn_le (flo I) (fhi I).

Definition fl_leb (I J : fl_interval) : bool :=
  fl_flags_le I J &&
    (negb (fl_active I) || (nn_le (flo J) (flo I) && nn_le (fhi I) (fhi J))).

Lemma fl_flags_spec I J : fl_flags_le I J = true <->
  (may_nan I = true -> may_nan J = true) /\
  (may_neg_zero I = true -> may_neg_zero J = true) /\
  (may_pos_zero I = true -> may_pos_zero J = true) /\
  (may_subnormal I = true -> may_subnormal J = true).
Proof.
  unfold fl_flags_le; rewrite !andb_true_iff, !implb_true_iff; tauto.
Qed.

Lemma fl_leb_spec I J : fl_leb I J = true <->
  fl_flags_le I J = true /\
  (fl_active I = true -> nn_le (flo J) (flo I) = true /\ nn_le (fhi I) (fhi J) = true).
Proof.
  unfold fl_leb; rewrite andb_true_iff.
  destruct (fl_active I); cbn; rewrite ?andb_true_iff; intuition discriminate.
Qed.

Lemma fl_active_mono I J : fl_leb I J = true -> fl_active I = true -> fl_active J = true.
Proof.
  intros Hle Hactive; apply fl_leb_spec in Hle as [_ Hbounds].
  destruct (Hbounds Hactive) as [Hlo Hhi].
  eapply nn_le_trans; [exact Hlo|]; eapply nn_le_trans; eassumption.
Qed.

Lemma fl_leb_refl I : fl_leb I I = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; repeat split; auto.
  - intro Hactive; split; apply nn_le_refl.
Qed.

Lemma fl_leb_trans I J K : fl_leb I J = true -> fl_leb J K = true -> fl_leb I K = true.
Proof.
  intros Hij Hjk; pose proof (fl_active_mono I J Hij) as Hactive.
  apply fl_leb_spec in Hij as [Hij Hboundsij]; apply fl_leb_spec in Hjk as [Hjk Hboundsjk].
  apply fl_leb_spec; split.
  - apply fl_flags_spec in Hij; apply fl_flags_spec in Hjk; apply fl_flags_spec; tauto.
  - intro Hi; destruct (Hboundsij Hi) as [Hloij Hhiij].
    destruct (Hboundsjk (Hactive Hi)) as [Hlojk Hhijk].
    split; eapply nn_le_trans; eassumption.
Qed.

Definition fl_bottom : fl_interval :=
  FlInterval fl_pinf fl_ninf false false false false.

Definition fl_join (I J : fl_interval) : fl_interval :=
  let lo := if fl_active I then
    if fl_active J then nn_min (flo I) (flo J) else flo I else flo J in
  let hi := if fl_active I then
    if fl_active J then nn_max (fhi I) (fhi J) else fhi I else fhi J in
  FlInterval lo hi (may_nan I || may_nan J) (may_neg_zero I || may_neg_zero J)
    (may_pos_zero I || may_pos_zero J) (may_subnormal I || may_subnormal J).

Definition fl_widen (I J : fl_interval) : fl_interval :=
  FlInterval
    (if nn_le (flo I) (flo J) then flo I else fl_ninf)
    (if nn_le (fhi J) (fhi I) then fhi I else fl_pinf)
    (may_nan I || may_nan J) (may_neg_zero I || may_neg_zero J)
    (may_pos_zero I || may_pos_zero J) (may_subnormal I || may_subnormal J).

Definition nn_is_ninf (x : fl_nn) : bool :=
  match proj1_sig x with
  | B754_infinity true => true
  | _ => false
  end.

Definition nn_is_pinf (x : fl_nn) : bool :=
  match proj1_sig x with
  | B754_infinity false => true
  | _ => false
  end.

Definition fl_narrow (I J : fl_interval) : fl_interval :=
  FlInterval
    (if nn_is_ninf (flo I) then flo J else flo I)
    (if nn_is_pinf (fhi I) then fhi J else fhi I)
    (may_nan I) (may_neg_zero I) (may_pos_zero I) (may_subnormal I).

Lemma nn_narrow_lo x y : nn_le x (if nn_is_ninf x then y else x) = true.
Proof.
  destruct x as [x Hx]; destruct x as [sx|[]|sx px Hpx|sx mx ex Hxb];
    cbn [nn_is_ninf]; try apply nn_le_refl.
  apply nn_ninf_le.
Qed.

Lemma nn_narrow_hi x y : nn_le (if nn_is_pinf x then y else x) x = true.
Proof.
  destruct x as [x Hx]; destruct x as [sx|[]|sx px Hpx|sx mx ex Hxb];
    cbn [nn_is_pinf]; try apply nn_le_refl.
  apply nn_le_pinf.
Qed.

Lemma fl_join_upper_l I J : fl_leb I (fl_join I J) = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; repeat split; intro Hflag;
      apply orb_true_iff; left; exact Hflag.
  - intro Hactive; unfold fl_join; rewrite Hactive; destruct (fl_active J); cbn.
    + split; [apply nn_min_l|apply nn_max_l].
    + split; apply nn_le_refl.
Qed.

Lemma fl_join_upper_r I J : fl_leb J (fl_join I J) = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; repeat split; intro Hflag;
      apply orb_true_iff; right; exact Hflag.
  - intro Hactive; unfold fl_join; rewrite Hactive; destruct (fl_active I); cbn.
    + split; [apply nn_min_r|apply nn_max_r].
    + split; apply nn_le_refl.
Qed.

Lemma fl_widen_upper_l I J : fl_leb I (fl_widen I J) = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; repeat split; intro Hflag;
      apply orb_true_iff; left; exact Hflag.
  - intro Hactive; cbn [fl_widen flo fhi]; split.
    + destruct (nn_le (flo I) (flo J)); [apply nn_le_refl|apply nn_ninf_le].
    + destruct (nn_le (fhi J) (fhi I)); [apply nn_le_refl|apply nn_le_pinf].
Qed.

Lemma fl_widen_upper_r I J : fl_leb J (fl_widen I J) = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; repeat split; intro Hflag;
      apply orb_true_iff; right; exact Hflag.
  - intro Hactive; cbn [fl_widen flo fhi]; split.
    + destruct (nn_le (flo I) (flo J)) eqn:Hlo; [exact Hlo|apply nn_ninf_le].
    + destruct (nn_le (fhi J) (fhi I)) eqn:Hhi; [exact Hhi|apply nn_le_pinf].
Qed.

Lemma fl_narrow_lower I J : fl_leb (fl_narrow I J) I = true.
Proof.
  apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; repeat split; auto.
  - intro Hactive; cbn [fl_narrow flo fhi]; split; [apply nn_narrow_lo|apply nn_narrow_hi].
Qed.

Lemma fl_narrow_upper I J : fl_leb J I = true -> fl_leb J (fl_narrow I J) = true.
Proof.
  intro Hle; apply fl_leb_spec in Hle as [Hflags Hbounds]; apply fl_leb_spec; split.
  - exact Hflags.
  - intro Hactive; destruct (Hbounds Hactive) as [Hlo Hhi]; cbn [fl_narrow flo fhi]; split.
    + destruct (nn_is_ninf (flo I)); [apply nn_le_refl|exact Hlo].
    + destruct (nn_is_pinf (fhi I)); [apply nn_le_refl|exact Hhi].
Qed.

(** The lattice compares flags and nonempty bounds and uses infinity widening. *)
Definition fl_lattice : lattice fl_interval :=
  {| leb := fl_leb;
     bot := fl_bottom;
     join := fl_join;
     widen := fl_widen;
     narrow := fl_narrow |}.

(** Interval membership supplies the forward concretisation dictionary. *)
Definition fl_concretisation : concretisation fl_interval fl := Concretisation _ _ fl_gamma.

(** The top interval includes all exceptional values and all ordered values. *)
Definition fl_top : fl_interval := FlInterval fl_ninf fl_pinf true true true true.

(** Top bounds every interval in the executable preorder. *)
Definition fl_top_lattice : top fl_lattice.
Proof.
  refine {| top_value := fl_top |}.
  intro I; apply fl_leb_spec; split.
  - apply fl_flags_spec; cbn; tauto.
  - intro Hactive; split; [apply nn_ninf_le|apply nn_le_pinf].
Defined.

Lemma fl_between_mono I J x : is_nan prec emax x = false ->
  fl_leb I J = true ->
  fle (proj1_sig (flo I)) x -> fle x (proj1_sig (fhi I)) ->
  fle (proj1_sig (flo J)) x /\ fle x (proj1_sig (fhi J)).
Proof.
  intros Hx Hle Hlo Hhi; apply fl_le_spec in Hlo; apply fl_le_spec in Hhi.
  assert (Hactive : fl_active I = true).
  { eapply fl_le_trans; [apply proj2_sig|exact Hx|apply proj2_sig|exact Hlo|exact Hhi]. }
  apply fl_leb_spec in Hle as [_ Hbounds]; destruct (Hbounds Hactive) as [Hlower Hupper].
  split; apply fl_le_spec.
  - eapply (fl_le_trans _ (proj1_sig (flo I)) _);
      [apply proj2_sig|apply proj2_sig|exact Hx|exact Hlower|exact Hlo].
  - eapply (fl_le_trans _ (proj1_sig (fhi I)) _);
      [exact Hx|apply proj2_sig|apply proj2_sig|exact Hhi|exact Hupper].
Qed.

Lemma fl_gamma_mono I J x : fl_leb I J = true -> fl_gamma I x -> fl_gamma J x.
Proof.
  intros Hle Hgamma.
  pose proof Hle as Hflags; apply fl_leb_spec in Hflags as [Hflags _].
  apply fl_flags_spec in Hflags as [Hnan [Hneg [Hpos Hsub]]].
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hbound]; cbn [fl_gamma B2FF] in *.
  - destruct sx; auto.
  - destruct Hgamma as [Hlo [Hhi Hsubnormal]].
    destruct (fl_between_mono I J (B754_infinity sx) eq_refl Hle Hlo Hhi) as [Hlo' Hhi'].
    repeat split; auto.
  - auto.
  - destruct Hgamma as [Hlo [Hhi Hsubnormal]].
    destruct (fl_between_mono I J (B754_finite sx mx ex Hbound) eq_refl Hle Hlo Hhi)
      as [Hlo' Hhi'].
    repeat split; auto.
Qed.

(** Every float is contained in the unbounded interval with all exceptional flags. *)
Theorem fl_top_sound (x : fl) : fl_gamma fl_top x.
Proof.
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hbound];
    cbn [fl_gamma B2FF fl_top flo fhi may_nan may_neg_zero may_pos_zero may_subnormal].
  - destruct sx; reflexivity.
  - repeat split; try reflexivity;
      unfold fle, fl_ninf, fl_pinf; destruct sx; cbn [Bcompare B2BSN]; exact I.
  - reflexivity.
  - repeat split; try reflexivity;
      unfold fle, fl_ninf, fl_pinf; cbn [Bcompare B2BSN]; exact I.
Qed.

(** Bottom excludes zero, NaN and every ordered nonzero value. *)
Theorem fl_bot_empty (x : fl) : ~ fl_gamma (bot fl_lattice) x.
Proof.
  destruct x as [sx|sx|sx px Hpx|sx mx ex Hbound];
    cbn [bot fl_lattice fl_bottom fl_gamma B2FF flo fhi may_nan may_neg_zero may_pos_zero].
  - destruct sx; discriminate.
  - destruct sx; cbn [fle fl_pinf fl_ninf Bcompare B2BSN]; tauto.
  - discriminate.
  - cbn [fle fl_pinf fl_ninf Bcompare B2BSN]; tauto.
Qed.

(** The executable interval operations and membership satisfy the weak lattice laws. *)
Theorem fl_lattice_laws :
  lattice_laws fl_lattice /\ concretisation_laws fl_lattice fl_concretisation.
Proof.
  split.
  - constructor.
    + apply fl_leb_refl.
    + apply fl_leb_trans.
    + intro I; apply fl_leb_spec; split.
      * apply fl_flags_spec; cbn [fl_bottom]; intuition discriminate.
      * cbn [fl_active fl_bottom nn_le fl_pinf fl_ninf fl_le Bcompare B2BSN]; discriminate.
    + apply fl_join_upper_l.
    + apply fl_join_upper_r.
    + apply fl_widen_upper_l.
    + apply fl_widen_upper_r.
    + intros I J Hle; apply fl_narrow_lower.
    + apply fl_narrow_upper.
  - constructor; apply fl_gamma_mono.
Qed.

Definition fl_flag_rank (I : fl_interval) : nat :=
  (if may_nan I then 0 else 1) + (if may_neg_zero I then 0 else 1) +
  (if may_pos_zero I then 0 else 1) + (if may_subnormal I then 0 else 1).

Definition fl_rank (I : fl_interval) : nat :=
  (if nn_is_ninf (flo I) then 0 else 1) + (if nn_is_pinf (fhi I) then 0 else 1) +
  fl_flag_rank I.

Lemma nn_lo_rank_step x y :
  (if nn_is_ninf (if nn_le x y then x else fl_ninf) then 0 else 1) <=
  (if nn_is_ninf x then 0 else 1).
Proof.
  destruct (nn_le x y); cbn; lia.
Qed.

Lemma nn_hi_rank_step x y :
  (if nn_is_pinf (if nn_le y x then x else fl_pinf) then 0 else 1) <=
  (if nn_is_pinf x then 0 else 1).
Proof.
  destruct (nn_le y x); cbn; lia.
Qed.

Lemma nn_ninf_is_le x y : nn_is_ninf x = true -> nn_le x y = true.
Proof.
  destruct x as [x Hx]; destruct x as [sx|[]|sx px Hpx|sx mx ex Hxb];
    cbn [nn_is_ninf]; try discriminate.
  intros _; apply nn_ninf_le.
Qed.

Lemma nn_pinf_is_ge x y : nn_is_pinf x = true -> nn_le y x = true.
Proof.
  destruct x as [x Hx]; destruct x as [sx|[]|sx px Hpx|sx mx ex Hxb];
    cbn [nn_is_pinf]; try discriminate.
  intros _; apply nn_le_pinf.
Qed.

Lemma nn_lo_rank_progress x y : nn_le x y = false ->
  (if nn_is_ninf (if nn_le x y then x else fl_ninf) then 0 else 1) <
  (if nn_is_ninf x then 0 else 1).
Proof.
  intro Hle; rewrite Hle; cbn.
  destruct (nn_is_ninf x) eqn:Hinf; [|lia].
  pose proof (nn_ninf_is_le x y Hinf); congruence.
Qed.

Lemma nn_hi_rank_progress x y : nn_le y x = false ->
  (if nn_is_pinf (if nn_le y x then x else fl_pinf) then 0 else 1) <
  (if nn_is_pinf x then 0 else 1).
Proof.
  intro Hle; rewrite Hle; cbn.
  destruct (nn_is_pinf x) eqn:Hinf; [|lia].
  pose proof (nn_pinf_is_ge x y Hinf); congruence.
Qed.

Lemma fl_flag_rank_step I J : fl_flag_rank (fl_widen I J) <= fl_flag_rank I.
Proof.
  unfold fl_flag_rank; cbn [fl_widen may_nan may_neg_zero may_pos_zero may_subnormal].
  destruct (may_nan I), (may_nan J), (may_neg_zero I), (may_neg_zero J),
    (may_pos_zero I), (may_pos_zero J), (may_subnormal I), (may_subnormal J); cbn; lia.
Qed.

Lemma fl_flag_rank_progress I J : fl_flags_le J I = false ->
  fl_flag_rank (fl_widen I J) < fl_flag_rank I.
Proof.
  unfold fl_flag_rank, fl_flags_le; cbn [fl_widen may_nan may_neg_zero may_pos_zero may_subnormal].
  destruct (may_nan I), (may_nan J), (may_neg_zero I), (may_neg_zero J),
    (may_pos_zero I), (may_pos_zero J), (may_subnormal I), (may_subnormal J);
    cbn; intros Hflags; try discriminate; lia.
Qed.

Lemma fl_rank_step I J : fl_rank (fl_widen I J) <= fl_rank I.
Proof.
  pose proof (nn_lo_rank_step (flo I) (flo J)) as Hlo.
  pose proof (nn_hi_rank_step (fhi I) (fhi J)) as Hhi.
  pose proof (fl_flag_rank_step I J) as Hflags.
  unfold fl_rank; cbn [fl_widen flo fhi]; lia.
Qed.

Lemma fl_rank_progress I J : fl_leb J I = false -> fl_rank (fl_widen I J) < fl_rank I.
Proof.
  intro Hle.
  pose proof (nn_lo_rank_step (flo I) (flo J)) as Hlo.
  pose proof (nn_hi_rank_step (fhi I) (fhi J)) as Hhi.
  pose proof (fl_flag_rank_step I J) as Hflags.
  destruct (nn_le (flo I) (flo J)) eqn:Hlob.
  - destruct (nn_le (fhi J) (fhi I)) eqn:Hhib.
    + assert (Hbad : fl_flags_le J I = false).
      { unfold fl_leb in Hle; rewrite Hlob, Hhib, orb_true_r, andb_true_r in Hle.
        exact Hle. }
      pose proof (fl_flag_rank_progress I J Hbad) as Hstrict.
      unfold fl_rank; cbn [fl_widen flo fhi] in *; rewrite Hlob, Hhib; lia.
    + pose proof (nn_hi_rank_progress (fhi I) (fhi J) Hhib) as Hstrict.
      unfold fl_rank; cbn [fl_widen flo fhi] in *; rewrite Hlob, Hhib in *; lia.
  - pose proof (nn_lo_rank_progress (flo I) (flo J) Hlob) as Hstrict.
    unfold fl_rank; cbn [fl_widen flo fhi] in *; rewrite Hlob in *; lia.
Qed.

(** At most two bounds and four flags can change strictly under widening. *)
Definition fl_widening_rank : bounded_widening_rank fl_lattice.
Proof.
  unshelve refine (@BoundedWideningRank _ _ (@WideningRank _ _ fl_rank _ _) 6 _).
  - intros I J Hle; apply fl_rank_step.
  - apply fl_rank_progress.
  - intro I; change (fl_rank I <= 6); unfold fl_rank, fl_flag_rank.
    destruct (nn_is_ninf (flo I)), (nn_is_pinf (fhi I)), (may_nan I),
      (may_neg_zero I), (may_pos_zero I), (may_subnormal I); cbn; lia.
Defined.

(** Both a genuine subnormal and the normal value one exist at every supported precision. *)
Theorem subnormal_proper (Hp : (2 <= prec)%Z) :
  (exists x : fl, subnormal x) /\
  (exists y : fl, B2R prec emax y = 1%R /\ ~ subnormal y).
Proof.
  split.
  - exists (B754_finite false 1 (SpecFloat.emin prec emax)
      (Bulp_correct_aux prec emax Hprec Hmax)).
    unfold subnormal; cbn [is_finite B2R F2R Fnum Fexp SpecFloat.cond_Zopp].
    unfold F2R; cbn [Fnum Fexp].
    rewrite Rmult_1_l; split; [reflexivity|]; split.
    + pose proof (bpow_gt_0 radix2 (SpecFloat.emin prec emax)); lra.
    + rewrite Rabs_right by
        (pose proof (bpow_gt_0 radix2 (SpecFloat.emin prec emax)); lra).
      apply bpow_lt; unfold SpecFloat.emin; lia.
  - exists (Bone prec emax Hprec Hmax); split; [apply Bone_correct|].
    unfold subnormal; rewrite Bone_correct; intros [_ [_ Hsmall]].
    rewrite Rabs_R1 in Hsmall.
    pose proof (@prec_lt_emax prec emax Hmax) as Hemax.
    pose proof (bpow_le radix2 (2 - emax) 0 ltac:(lia)) as Hthreshold.
    change (bpow radix2 (2 - emax) <= 1)%R in Hthreshold; lra.
Qed.

(** * Directed rounding bounds *)

Local Abbreviation fl_round_real := (round radix2 (SpecFloat.fexp prec emax)).

Lemma fl_round_enclosure r :
  (fl_round_real Zfloor r <= fl_round_real ZnearestE r <= fl_round_real Zceil r)%R.
Proof.
  pose proof (round_DN_pt radix2 (SpecFloat.fexp prec emax) r) as [_ [Hdn _]].
  pose proof (round_UP_pt radix2 (SpecFloat.fexp prec emax) r) as [_ [Hup _]].
  destruct (round_DN_or_UP radix2 (SpecFloat.fexp prec emax) ZnearestE r) as [Hlo|Hhi];
    rewrite Hlo || rewrite Hhi; split; lra.
Qed.

Definition fl_rounded_spec (mode : mode) (r : R) (x : fl) : Prop :=
  if Rlt_bool (Rabs (fl_round_real (round_mode mode) r)) (bpow radix2 emax) then
    is_finite prec emax x = true /\ B2R prec emax x = fl_round_real (round_mode mode) r
  else B2FF prec emax x = binary_overflow prec emax mode (Rlt_bool r 0).

Lemma fl_rounded_nonnegative mode r : (0 <= r)%R -> (0 <= fl_round_real (round_mode mode) r)%R.
Proof.
  intro Hr; pose proof (round_le radix2 (SpecFloat.fexp prec emax)
    (round_mode mode) 0 r Hr) as Hround.
  rewrite round_0 in Hround by apply valid_rnd_round_mode; exact Hround.
Qed.

Lemma fl_rounded_nonpositive mode r : (r <= 0)%R -> (fl_round_real (round_mode mode) r <= 0)%R.
Proof.
  intro Hr; pose proof (round_le radix2 (SpecFloat.fexp prec emax)
    (round_mode mode) r 0 Hr) as Hround.
  rewrite round_0 in Hround by apply valid_rnd_round_mode; exact Hround.
Qed.

Lemma fl_rounded_nan mode r x : fl_rounded_spec mode r x -> is_nan prec emax x = false.
Proof.
  unfold fl_rounded_spec; destruct Rlt_bool; intro Hspec.
  - destruct Hspec as [Hfinite _]; destruct x; try reflexivity; discriminate.
  - rewrite <- is_nan_B2FF, Hspec.
    destruct mode, (Rlt_bool r 0); reflexivity.
Qed.

Lemma fle_finite x y : is_finite prec emax x = true -> is_finite prec emax y = true ->
  (B2R prec emax x <= B2R prec emax y)%R -> fle x y.
Proof.
  intros Hx Hy Hle; unfold fle; rewrite Bcompare_correct by assumption.
  destruct (Rcompare_spec (B2R prec emax x) (B2R prec emax y)); cbn; tauto || lra.
Qed.

Lemma fle_ninf x : is_nan prec emax x = false -> fle (@B754_infinity prec emax true) x.
Proof.
  intro Hnan; apply fl_le_spec; exact (nn_ninf_le (exist _ x Hnan)).
Qed.

Lemma fle_pinf x : is_nan prec emax x = false -> fle x (@B754_infinity prec emax false).
Proof.
  intro Hnan; apply fl_le_spec; exact (nn_le_pinf (exist _ x Hnan)).
Qed.

Lemma fl_rounded_lower rlo r lower result : fl_rounded_spec mode_DN rlo lower ->
  fl_rounded_spec mode_NE r result -> (rlo <= r)%R -> fle lower result.
Proof.
  intros Hlower Hresult Hle.
  pose proof (fl_rounded_nan _ _ _ Hlower) as Hlower_nan.
  pose proof (fl_rounded_nan _ _ _ Hresult) as Hresult_nan.
  assert (Hrounded : (fl_round_real Zfloor rlo <= fl_round_real ZnearestE r)%R).
  { pose proof (round_le radix2 (SpecFloat.fexp prec emax) Zfloor rlo r Hle).
    pose proof (fl_round_enclosure r); lra. }
  pose proof (bpow_gt_0 radix2 emax) as Hmaxpos.
  pose proof (Rle_abs (fl_round_real Zfloor rlo)) as Habslo.
  pose proof (Rle_abs (- fl_round_real Zfloor rlo)) as Habsloneg.
  pose proof (Rle_abs (fl_round_real ZnearestE r)) as Habsr.
  pose proof (Rle_abs (- fl_round_real ZnearestE r)) as Habsrneg.
  rewrite Rabs_Ropp in Habsloneg, Habsrneg.
  unfold fl_rounded_spec in Hlower, Hresult.
  cbn [round_mode] in Hlower, Hresult.
  destruct (Rlt_bool_spec (Rabs (fl_round_real Zfloor rlo)) (bpow radix2 emax))
    as [Hlo_small|Hlo_large];
    destruct (Rlt_bool_spec (Rabs (fl_round_real ZnearestE r)) (bpow radix2 emax))
      as [Hr_small|Hr_large].
  - destruct Hlower as [Hlfinite Hlreal], Hresult as [Hrfinite Hrreal].
    apply fle_finite; try assumption; rewrite Hlreal, Hrreal; exact Hrounded.
  - destruct Hlower as [Hlfinite Hlreal].
    destruct (Rlt_bool_spec r 0) as [Hrneg|Hrpos].
    + pose proof (fl_rounded_nonpositive mode_NE r (Rlt_le _ _ Hrneg)) as Hrround.
      cbn [round_mode] in Hrround.
      rewrite Rabs_left1 in Hr_large by exact Hrround; lra.
    + change (B2FF prec emax result = F754_infinity false) in Hresult.
      assert (Heq : result = B754_infinity false) by
        (apply B2FF_inj; exact Hresult).
      subst result; apply fle_pinf; exact Hlower_nan.
  - destruct (Rlt_bool_spec rlo 0) as [Hlneg|Hlpos].
    + change (B2FF prec emax lower = F754_infinity true) in Hlower.
      assert (Heq : lower = B754_infinity true) by
        (apply B2FF_inj; exact Hlower).
      subst lower; apply fle_ninf; exact Hresult_nan.
    + pose proof (fl_rounded_nonnegative mode_DN rlo Hlpos) as Hlround.
      cbn [round_mode] in Hlround.
      rewrite Rabs_right in Hlo_large by lra; lra.
  - destruct (Rlt_bool_spec rlo 0) as [Hlneg|Hlpos].
    + change (B2FF prec emax lower = F754_infinity true) in Hlower.
      assert (Heq : lower = B754_infinity true) by
        (apply B2FF_inj; exact Hlower).
      subst lower; apply fle_ninf; exact Hresult_nan.
    + rewrite Rlt_bool_false in Hresult by lra.
      change (B2FF prec emax result = F754_infinity false) in Hresult.
      assert (Heq : result = B754_infinity false) by
        (apply B2FF_inj; exact Hresult).
      subst result; apply fle_pinf; exact Hlower_nan.
Qed.

Lemma fl_rounded_upper r rhi result upper : fl_rounded_spec mode_NE r result ->
  fl_rounded_spec mode_UP rhi upper -> (r <= rhi)%R -> fle result upper.
Proof.
  intros Hresult Hupper Hle.
  pose proof (fl_rounded_nan _ _ _ Hresult) as Hresult_nan.
  pose proof (fl_rounded_nan _ _ _ Hupper) as Hupper_nan.
  assert (Hrounded : (fl_round_real ZnearestE r <= fl_round_real Zceil rhi)%R).
  { pose proof (round_le radix2 (SpecFloat.fexp prec emax) Zceil r rhi Hle).
    pose proof (fl_round_enclosure r); lra. }
  pose proof (bpow_gt_0 radix2 emax) as Hmaxpos.
  pose proof (Rle_abs (fl_round_real ZnearestE r)) as Habsr.
  pose proof (Rle_abs (- fl_round_real ZnearestE r)) as Habsrneg.
  pose proof (Rle_abs (fl_round_real Zceil rhi)) as Habshi.
  pose proof (Rle_abs (- fl_round_real Zceil rhi)) as Habshineg.
  rewrite Rabs_Ropp in Habsrneg, Habshineg.
  unfold fl_rounded_spec in Hresult, Hupper; cbn [round_mode] in Hresult, Hupper.
  destruct (Rlt_bool_spec (Rabs (fl_round_real ZnearestE r)) (bpow radix2 emax))
    as [Hr_small|Hr_large];
    destruct (Rlt_bool_spec (Rabs (fl_round_real Zceil rhi)) (bpow radix2 emax))
      as [Hhi_small|Hhi_large].
  - destruct Hresult as [Hrfinite Hrreal], Hupper as [Hhfinite Hhreal].
    apply fle_finite; try assumption; rewrite Hrreal, Hhreal; exact Hrounded.
  - destruct (Rlt_bool_spec rhi 0) as [Hhineg|Hhipos].
    + pose proof (fl_rounded_nonpositive mode_UP rhi (Rlt_le _ _ Hhineg)) as Hhiround.
      cbn [round_mode] in Hhiround.
      rewrite Rabs_left1 in Hhi_large by exact Hhiround; lra.
    + change (B2FF prec emax upper = F754_infinity false) in Hupper.
      assert (Heq : upper = B754_infinity false) by
        (apply B2FF_inj; exact Hupper).
      subst upper; apply fle_pinf; exact Hresult_nan.
  - destruct (Rlt_bool_spec r 0) as [Hrneg|Hrpos].
    + change (B2FF prec emax result = F754_infinity true) in Hresult.
      assert (Heq : result = B754_infinity true) by
        (apply B2FF_inj; exact Hresult).
      subst result; apply fle_ninf; exact Hupper_nan.
    + pose proof (fl_rounded_nonnegative mode_NE r Hrpos) as Hrround.
      cbn [round_mode] in Hrround.
      rewrite Rabs_right in Hr_large by lra; lra.
  - destruct (Rlt_bool_spec rhi 0) as [Hhineg|Hhipos].
    + rewrite Rlt_bool_true in Hresult by lra.
      change (B2FF prec emax result = F754_infinity true) in Hresult.
      assert (Heq : result = B754_infinity true) by
        (apply B2FF_inj; exact Hresult).
      subst result; apply fle_ninf; exact Hupper_nan.
    + change (B2FF prec emax upper = F754_infinity false) in Hupper.
      assert (Heq : upper = B754_infinity false) by
        (apply B2FF_inj; exact Hupper).
      subst upper; apply fle_pinf; exact Hresult_nan.
Qed.

End Float.
