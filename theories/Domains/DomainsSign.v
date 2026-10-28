(** * Sign sets for words

    Three booleans describe the possible signed classes of a word.
    For example, intersecting nonnegative and nonpositive facts leaves only zero.
    Builds on: DomainsNumeric and Bits signed views and bit equations. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit.
From Gaulois.Domains Require Import DomainsNumeric.
Import List.ListNotations.

Open Scope Z_scope.

(** Each flag permits one of the negative, zero, and positive signed classes. *)
Record sign : Type := Sign {
  neg : bool;
  zero : bool;
  pos : bool
}.

(** Sign inclusion and union are computed fieldwise. *)
Definition sign_lattice : lattice sign :=
  {| leb a b := (negb (neg a) || neg b) && (negb (zero a) || zero b) &&
       (negb (pos a) || pos b);
     bot := Sign false false false;
     join a b := Sign (neg a || neg b) (zero a || zero b) (pos a || pos b);
     widen a b := Sign (neg a || neg b) (zero a || zero b) (pos a || pos b);
     narrow a _ := a |}.

(** Sign sets satisfy the weak lattice laws. *)
Theorem sign_laws : lattice_laws sign_lattice.
Proof.
  constructor.
  - intros [a b c]. destruct a, b, c; reflexivity.
  - intros [a b c] [d e f] [g h i]. destruct a, b, c, d, e, f, g, h, i;
      cbn; intros; try discriminate; reflexivity.
  - intros [a b c]. reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
  - intros [a b c] s Hle. destruct a, b, c; reflexivity.
  - intros a b Hle. exact Hle.
Qed.

(** Union is the least upper bound of sign sets. *)
Theorem sign_lub : lub_laws sign_lattice.
Proof.
  constructor. intros [a b c] [d e f] [g h i].
  destruct a, b, c, d, e, f, g, h, i; cbn; intros; try discriminate; reflexivity.
Qed.

(** The number of enabled classes is a monotone height bounded by three. *)
Definition sign_height : monotone_height sign_lattice.
Proof.
  set (r := fun s => ((if neg s then 1 else 0) + (if zero s then 1 else 0) +
    (if pos s then 1 else 0))%nat).
  unshelve refine (@MonotoneHeight _ _ (@Height _ _ r 3%nat _ _) _).
  - unfold r. intros [a b c]. destruct a, b, c; cbn; lia.
  - unfold r. intros [a b c] [d e f]. destruct a, b, c, d, e, f;
      cbn; intro Hstrict; try discriminate; lia.
  - cbn [rank]. unfold r. intros [a b c] [d e f]. destruct a, b, c, d, e, f;
      cbn; intro Hle; try discriminate; lia.
Defined.

(** A sign set permits every signed class inhabited by its concrete word. *)
Definition sign_gamma (w : width) (s : sign) (z : Z) : Prop :=
  (signed w z < 0 -> neg s = true) /\ (signed w z = 0 -> zero s = true) /\
  (0 < signed w z -> pos s = true).

(** Intersection retains exactly the classes allowed by both operands. *)
Definition sign_meet (a b : sign) : sign :=
  Sign (neg a && neg b) (zero a && zero b) (pos a && pos b).

Definition sign_top : sign := Sign true true true.

Definition sign_const (w : width) (z : Z) : sign :=
  Sign (signed w z <? 0) (signed w z =? 0) (0 <? signed w z).

Lemma signed_wrap_value : forall w z, signed w (wrap w z) = signed w z.
Proof.
  intros w z. unfold signed. now rewrite wrap_wrap.
Qed.

Lemma signed_range_value : forall w z, - half w <= signed w z < half w.
Proof.
  intros w z. unfold signed. pose proof (wrap_is_word w z) as [Hlo Hhi].
  pose proof (modulus_half w). pose proof (half_pos w).
  destruct (wrap w z <? half w) eqn:Hhalf;
    [apply Z.ltb_lt in Hhalf|apply Z.ltb_ge in Hhalf]; lia.
Qed.

Lemma signed_zero_value : forall w z, signed w z = 0 <-> wrap w z = 0.
Proof.
  intros w z. unfold signed. pose proof (wrap_is_word w z) as [Hlo Hhi].
  pose proof (modulus_half w). pose proof (half_pos w).
  destruct (wrap w z <? half w) eqn:Hhalf;
    [apply Z.ltb_lt in Hhalf|apply Z.ltb_ge in Hhalf]; lia.
Qed.

Lemma signed_msb_value : forall w z,
  (signed w z < 0 <-> msb w z = true) /\ (0 <= signed w z <-> msb w z = false).
Proof.
  intros w z. rewrite msb_half. unfold signed.
  pose proof (wrap_is_word w z) as [Hlo Hhi]. pose proof (modulus_half w).
  pose proof (half_pos w). destruct (wrap w z <? half w) eqn:Hhalf; cbn [negb];
    [apply Z.ltb_lt in Hhalf|apply Z.ltb_ge in Hhalf];
    split; split; intros; try discriminate; try reflexivity; lia.
Qed.

Lemma sign_nonnegative : forall w s z,
  sign_gamma w s z -> msb w z = false -> zero s || pos s = true.
Proof.
  intros w s z [_ [Hz Hp]] Hmsb.
  apply (proj2 (signed_msb_value w z)) in Hmsb.
  destruct (Z.eq_dec (signed w z) 0) as [Heq|Hneq].
  - rewrite (Hz Heq). reflexivity.
  - rewrite (Hp ltac:(lia)). apply orb_true_r.
Qed.

Lemma sign_negative : forall w s z,
  sign_gamma w s z -> msb w z = true -> neg s = true.
Proof.
  intros w s z [Hneg _] Hmsb. apply Hneg. now apply (proj1 (signed_msb_value w z)).
Qed.

Lemma sign_from_msb : forall w s z,
  (msb w z = true -> neg s = true) ->
  (msb w z = false -> zero s = true /\ pos s = true) -> sign_gamma w s z.
Proof.
  intros w s z Hneg Hnonneg. split; [|split]; intro Hsign.
  - apply Hneg. now apply (proj1 (signed_msb_value w z)).
  - apply (proj1 (Hnonneg ltac:(apply (proj2 (signed_msb_value w z)); lia))).
  - apply (proj2 (Hnonneg ltac:(apply (proj2 (signed_msb_value w z)); lia))).
Qed.

Definition sign_nonneg (s : sign) : bool := zero s || pos s.

Definition sign_bits (n nn : bool) : sign := Sign n nn nn.

(** Signed interval bounds are exact for each nonempty individual sign class. *)
Definition sign_lo (w : width) (s : sign) : Z :=
  if neg s then - half w else if zero s then 0 else 1.

Definition sign_hi (w : width) (s : sign) : Z :=
  if pos s then half w - 1 else if zero s then 0 else -1.

Definition sign_ulo (w : width) (s : sign) : Z :=
  if zero s then 0 else if pos s then 1 else half w.

Definition sign_uhi (w : width) (s : sign) : Z :=
  if neg s then modulus w - 1 else if pos s then half w - 1 else 0.

Lemma sign_bounds : forall w s z, sign_gamma w s z ->
  sign_lo w s <= signed w z <= sign_hi w s.
Proof.
  intros w [n q p] z [Hn [Hq Hp]].
  pose proof (signed_range_value w z). pose proof (half_pos w).
  destruct n, q, p; cbn in *; unfold sign_lo, sign_hi; cbn; try lia.
Qed.

Lemma sign_unsigned_bounds : forall w s z, sign_gamma w s z ->
  sign_ulo w s <= wrap w z <= sign_uhi w s.
Proof.
  intros w [n q p] z Hgamma. pose proof (sign_bounds w (Sign n q p) z Hgamma) as Hbounds.
  destruct Hgamma as [Hn [Hq Hp]]. pose proof (wrap_is_word w z) as [Hlo Hhi].
  pose proof (half_pos w). pose proof (modulus_half w).
  unfold signed in Hn, Hq, Hp, Hbounds.
  destruct (wrap w z <? half w) eqn:Hhalf;
    [apply Z.ltb_lt in Hhalf|apply Z.ltb_ge in Hhalf];
    destruct n, q, p; cbn in *; unfold sign_ulo, sign_uhi; cbn; lia.
Qed.

(** A decided comparison has one sign class; an undecided one permits both boolean words. *)
Definition sign_boolean (b : bool) : sign :=
  if b then Sign true false false else Sign false true false.

Definition sign_bool_top : sign := Sign true true false.

Definition sign_cmp_lt (lo hi lo' hi' : Z) : sign :=
  if hi <? lo' then sign_boolean true else
  if hi' <=? lo then sign_boolean false else sign_bool_top.

Definition sign_cmp_le (lo hi lo' hi' : Z) : sign :=
  if hi <=? lo' then sign_boolean true else
  if hi' <? lo then sign_boolean false else sign_bool_top.

Definition sign_cmp_eq (lo hi lo' hi' : Z) : sign :=
  if (hi <? lo') || (hi' <? lo) then sign_boolean false else
  if (lo =? hi) && (lo' =? hi') && (lo =? lo') then sign_boolean true else sign_bool_top.

Definition sign_bool_not (s : sign) : sign := Sign (zero s) (neg s) false.

Definition sign_compare (o : op) (w : width) (a b : sign) : sign :=
  match o with
  | bveq => sign_cmp_eq (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | bvne => sign_bool_not
      (sign_cmp_eq (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b))
  | bvslt => sign_cmp_lt (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | bvsle => sign_cmp_le (sign_lo w a) (sign_hi w a) (sign_lo w b) (sign_hi w b)
  | bvult => sign_cmp_lt (sign_ulo w a) (sign_uhi w a) (sign_ulo w b) (sign_uhi w b)
  | bvule => sign_cmp_le (sign_ulo w a) (sign_uhi w a) (sign_ulo w b) (sign_uhi w b)
  | _ => sign_bool_top
  end.

(** Sign transfers preserve sign bits and use range bounds to decide comparisons. *)
Definition sign_forward (o : op) (wps : list (width * sign)) (rw : width) : sign :=
  match o, wps with
  | bvand, [(_, a); (_, b)] =>
    sign_bits (neg a && neg b) (sign_nonneg a || sign_nonneg b)
  | bvor, [(_, a); (_, b)] =>
    sign_bits (neg a || neg b) (sign_nonneg a && sign_nonneg b)
  | bvxor, [(_, a); (_, b)] =>
    sign_bits ((neg a && sign_nonneg b) || (sign_nonneg a && neg b))
      ((neg a && neg b) || (sign_nonneg a && sign_nonneg b))
  | bvnot, [(_, a)] => sign_bits (sign_nonneg a) (neg a)
  | bvneg, [(_, a)] => Sign (neg a || pos a) (zero a) (neg a)
  | bvzext _, [_] => Sign false true true
  | bvsext _, [(_, a)] => a
  | bvite, [_; (_, a); (_, b)] => join sign_lattice a b
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [(w, a); (_, b)] =>
    sign_compare o w a b
  | _, _ => sign_top
  end.

(** Sign payload operations use intersection for direct-variable refinement. *)
Definition sign_domain : word_domain sign :=
  {| plat _ := sign_lattice;
     ptop _ := sign_top;
     pconst := sign_const;
     pforward := sign_forward;
     passume _ wps _ _ := map snd wps;
     pmeet _ := sign_meet |}.

Lemma sign_gamma_boolean : forall (s : sign) (b : bool),
  sign_gamma 1%positive s (if b then 1 else 0) <->
  (if b then neg s = true else zero s = true).
Proof.
  intros s []; unfold sign_gamma; cbn; split; intros H;
    try solve [intuition lia].
  exact (proj1 H ltac:(lia)).
Qed.

Lemma sign_boolean_sound : forall b,
  sign_gamma 1%positive (sign_boolean b) (if b then 1 else 0).
Proof.
  intros []. apply (proj2 (sign_gamma_boolean (sign_boolean true) true)). reflexivity.
  apply (proj2 (sign_gamma_boolean (sign_boolean false) false)). reflexivity.
Qed.

Lemma sign_bool_top_sound : forall b : bool,
  sign_gamma 1%positive sign_bool_top (if b then 1 else 0).
Proof.
  intros []. apply (proj2 (sign_gamma_boolean sign_bool_top true)). reflexivity.
  apply (proj2 (sign_gamma_boolean sign_bool_top false)). reflexivity.
Qed.

Lemma sign_bool_not_sound : forall (s : sign) (b : bool),
  sign_gamma 1%positive s (if b then 1 else 0) ->
  sign_gamma 1%positive (sign_bool_not s) (if negb b then 1 else 0).
Proof.
  intros s [] Hgamma.
  - apply (proj2 (sign_gamma_boolean (sign_bool_not s) false)).
    exact (proj1 (sign_gamma_boolean s true) Hgamma).
  - apply (proj2 (sign_gamma_boolean (sign_bool_not s) true)).
    exact (proj1 (sign_gamma_boolean s false) Hgamma).
Qed.

Lemma sign_cmp_lt_sound : forall lo hi lo' hi' x y,
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_lt lo hi lo' hi') (if x <? y then 1 else 0).
Proof.
  intros lo hi lo' hi' x y Hx Hy. unfold sign_cmp_lt.
  destruct (hi <? lo') eqn:Htrue.
  - apply Z.ltb_lt in Htrue.
    assert (Hxy : (x <? y) = true) by (apply Z.ltb_lt; lia).
    rewrite Hxy. apply (sign_boolean_sound true).
  - destruct (hi' <=? lo) eqn:Hfalse; [|apply sign_bool_top_sound].
    apply Z.leb_le in Hfalse.
    assert (Hxy : (x <? y) = false) by (apply Z.ltb_ge; lia).
    rewrite Hxy. apply (sign_boolean_sound false).
Qed.

Lemma sign_cmp_le_sound : forall lo hi lo' hi' x y,
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_le lo hi lo' hi') (if x <=? y then 1 else 0).
Proof.
  intros lo hi lo' hi' x y Hx Hy. unfold sign_cmp_le.
  destruct (hi <=? lo') eqn:Htrue.
  - apply Z.leb_le in Htrue.
    assert (Hxy : (x <=? y) = true) by (apply Z.leb_le; lia).
    rewrite Hxy. apply (sign_boolean_sound true).
  - destruct (hi' <? lo) eqn:Hfalse; [|apply sign_bool_top_sound].
    apply Z.ltb_lt in Hfalse.
    assert (Hxy : (x <=? y) = false) by (apply Z.leb_gt; lia).
    rewrite Hxy. apply (sign_boolean_sound false).
Qed.

Lemma sign_cmp_eq_sound : forall lo hi lo' hi' x y,
  lo <= x <= hi -> lo' <= y <= hi' ->
  sign_gamma 1%positive (sign_cmp_eq lo hi lo' hi') (if x =? y then 1 else 0).
Proof.
  intros lo hi lo' hi' x y Hx Hy. unfold sign_cmp_eq.
  destruct ((hi <? lo') || (hi' <? lo)) eqn:Hfalse.
  - apply orb_true_iff in Hfalse as [Hfalse|Hfalse]; apply Z.ltb_lt in Hfalse;
      assert (Hxy : (x =? y) = false) by (apply Z.eqb_neq; lia);
      rewrite Hxy; apply (sign_boolean_sound false).
  - destruct ((lo =? hi) && (lo' =? hi') && (lo =? lo')) eqn:Htrue;
      [|apply sign_bool_top_sound].
    apply andb_true_iff in Htrue as [Hbounds Heq].
    apply andb_true_iff in Hbounds as [Hlo Hlo'].
    apply Z.eqb_eq in Hlo, Hlo', Heq.
    assert (Hxy : (x =? y) = true) by (apply Z.eqb_eq; lia).
    rewrite Hxy. apply (sign_boolean_sound true).
Qed.

Lemma signed_equality_value : forall w x y,
  (wrap w x =? wrap w y) = (signed w x =? signed w y).
Proof.
  intros w x y. unfold signed. pose proof (wrap_is_word w x) as [Hxl Hxh].
  pose proof (wrap_is_word w y) as [Hyl Hyh]. pose proof (modulus_half w).
  destruct (wrap w x <? half w) eqn:Hsx, (wrap w y <? half w) eqn:Hsy;
    try apply Z.ltb_lt in Hsx; try apply Z.ltb_ge in Hsx;
    try apply Z.ltb_lt in Hsy; try apply Z.ltb_ge in Hsy;
    apply Bool.eq_true_iff_eq; rewrite !Z.eqb_eq; lia.
Qed.

Lemma sign_compare_sound : forall o w a b x y rw z,
  (o = bveq \/ o = bvne \/ o = bvult \/ o = bvule \/ o = bvslt \/ o = bvsle) ->
  sign_gamma w a x -> sign_gamma w b y ->
  eval_op o [(w, x); (w, y)] = Some (rw, z) -> sign_gamma rw (sign_compare o w a b) z.
Proof.
  intros o w a b x y rw z Ho Ha Hb Heval.
  pose proof (sign_bounds w a x Ha) as Hx. pose proof (sign_bounds w b y Hb) as Hy.
  pose proof (sign_unsigned_bounds w a x Ha) as Hux.
  pose proof (sign_unsigned_bounds w b y Hb) as Huy.
  destruct Ho as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr. inversion Hr; subst rw z. cbn [sign_compare].
    rewrite signed_equality_value. now apply sign_cmp_eq_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y _ eq_refl)) Heval) as Hr.
    cbn beta in Hr. inversion Hr; subst rw z. cbn [sign_compare].
    apply sign_bool_not_sound.
    rewrite signed_equality_value. now apply sign_cmp_eq_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvult w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [sign_compare]. unfold wult. now apply sign_cmp_lt_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvule w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [sign_compare]. unfold wule. now apply sign_cmp_le_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvslt w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [sign_compare]. unfold wslt. now apply sign_cmp_lt_sound.
  - pose proof (eq_trans (eq_sym (eval_op_cmp bvsle w x y _ eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. cbn [sign_compare]. unfold wsle. now apply sign_cmp_le_sound.
Qed.

Lemma msb_and_value : forall w x y, is_word w x -> is_word w y ->
  msb w (wand w x y) = (msb w x && msb w y).
Proof.
  intros w x y Hx Hy. unfold msb.
  rewrite (wrap_id _ _ (wand_is_word w x y)), (wrap_id _ _ Hx), (wrap_id _ _ Hy).
  apply testbit_wand; try assumption; lia.
Qed.

Lemma msb_or_value : forall w x y, is_word w x -> is_word w y ->
  msb w (wor w x y) = (msb w x || msb w y).
Proof.
  intros w x y Hx Hy. unfold msb.
  rewrite (wrap_id _ _ (wor_is_word w x y)), (wrap_id _ _ Hx), (wrap_id _ _ Hy).
  apply testbit_wor; try assumption; lia.
Qed.

Lemma msb_xor_value : forall w x y, is_word w x -> is_word w y ->
  msb w (wxor w x y) = xorb (msb w x) (msb w y).
Proof.
  intros w x y Hx Hy. unfold msb.
  rewrite (wrap_id _ _ (wxor_is_word w x y)), (wrap_id _ _ Hx), (wrap_id _ _ Hy).
  apply testbit_wxor; try assumption; lia.
Qed.

Lemma msb_not_value : forall w x, is_word w x -> msb w (wnot w x) = negb (msb w x).
Proof.
  intros w x Hx. unfold msb.
  rewrite (wrap_id _ _ (wnot_is_word w x)), (wrap_id _ _ Hx).
  rewrite testbit_wnot by (try assumption; lia).
  assert (Hbit : (Zpos w - 1 <? Zpos w) = true) by (apply Z.ltb_lt; lia).
  now rewrite Hbit.
Qed.

Lemma sign_class_flag : forall w a x, sign_gamma w a x ->
  (if msb w x then neg a else sign_nonneg a) = true.
Proof.
  intros w a x Ha. destruct (msb w x) eqn:Hmsb.
  - exact (sign_negative w a x Ha Hmsb).
  - exact (sign_nonnegative w a x Ha Hmsb).
Qed.

Lemma sign_and_sound : forall w a b x y,
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w (sign_bits (neg a && neg b) (sign_nonneg a || sign_nonneg b))
    (wand w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sign_class_flag w a x Ha) as Hfa.
  pose proof (sign_class_flag w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_bits neg zero pos];
    rewrite (msb_and_value w x y Hx Hy);
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

Lemma sign_or_sound : forall w a b x y,
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w (sign_bits (neg a || neg b) (sign_nonneg a && sign_nonneg b))
    (wor w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sign_class_flag w a x Ha) as Hfa.
  pose proof (sign_class_flag w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_bits neg zero pos];
    rewrite (msb_or_value w x y Hx Hy);
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

Lemma sign_xor_sound : forall w a b x y,
  is_word w x -> is_word w y -> sign_gamma w a x -> sign_gamma w b y ->
  sign_gamma w
    (sign_bits ((neg a && sign_nonneg b) || (sign_nonneg a && neg b))
      ((neg a && neg b) || (sign_nonneg a && sign_nonneg b))) (wxor w x y).
Proof.
  intros w a b x y Hx Hy Ha Hb.
  pose proof (sign_class_flag w a x Ha) as Hfa.
  pose proof (sign_class_flag w b y Hb) as Hfb.
  apply sign_from_msb; cbn [sign_bits neg zero pos];
    rewrite (msb_xor_value w x y Hx Hy);
    destruct (msb w x), (msb w y); cbn in Hfa, Hfb |- *;
    intro Hresult; try discriminate; rewrite ?Hfa, ?Hfb, ?orb_true_r, ?andb_true_r; cbn; auto.
Qed.

Lemma sign_not_sound : forall w a x, is_word w x -> sign_gamma w a x ->
  sign_gamma w (sign_bits (sign_nonneg a) (neg a)) (wnot w x).
Proof.
  intros w a x Hx Ha. pose proof (sign_class_flag w a x Ha) as Hfa.
  apply sign_from_msb; cbn [sign_bits neg zero pos];
    rewrite (msb_not_value w x Hx); destruct (msb w x); cbn in Hfa |- *;
    intro Hresult; try discriminate; auto.
Qed.

Lemma sign_neg_sound : forall w a x, is_word w x -> sign_gamma w a x ->
  sign_gamma w (Sign (neg a || pos a) (zero a) (neg a)) (wneg w x).
Proof.
  intros w a x Hx [Hn [Hz Hp]].
  pose proof (wrap_is_word w (wneg w x)) as Hresult.
  pose proof (half_pos w). pose proof (modulus_half w).
  assert (Hwrap : wrap w (- x) = if x =? 0 then 0 else modulus w - x).
  { destruct (x =? 0) eqn:Hxzero.
    - apply Z.eqb_eq in Hxzero. subst x. apply wrap_0.
    - apply Z.eqb_neq in Hxzero.
      replace (- x) with ((modulus w - x) + (-1) * modulus w) by ring.
      rewrite wrap_add_modulus. apply wrap_id. unfold is_word in *. lia. }
  unfold sign_gamma. cbn [neg zero pos]. unfold wneg, signed in *.
  rewrite !wrap_wrap, Hwrap.
  rewrite (wrap_id w x Hx) in Hn, Hz, Hp.
  destruct (x =? 0) eqn:Hxzero.
  - apply Z.eqb_eq in Hxzero. subst x.
    assert (Hhalf : (0 <? half w) = true) by (apply Z.ltb_lt; lia).
    rewrite Hhalf in *. split; [lia|]. split; [intros _; now apply Hz|lia].
  - apply Z.eqb_neq in Hxzero.
    destruct (x <? half w) eqn:Hxhalf, (modulus w - x <? half w) eqn:Hnhalf;
      try apply Z.ltb_lt in Hxhalf; try apply Z.ltb_ge in Hxhalf;
      try apply Z.ltb_lt in Hnhalf; try apply Z.ltb_ge in Hnhalf;
      unfold is_word in Hx; (split; [|split]); intro Hsign; try lia.
    + rewrite (Hp ltac:(lia)). apply orb_true_r.
    + rewrite (Hn ltac:(lia)). reflexivity.
    + rewrite (Hn ltac:(lia)). reflexivity.
Qed.

Lemma signed_in_range : forall w z, - half w <= z < half w -> signed w z = z.
Proof.
  intros w z Hz. pose proof (modulus_half w). pose proof (half_pos w).
  unfold signed. destruct (Z_le_dec 0 z) as [Hnonneg|Hneg].
  - rewrite wrap_id by (unfold is_word; lia).
    assert (Hhalf : (z <? half w) = true) by (apply Z.ltb_lt; lia).
    now rewrite Hhalf.
  - assert (Hwrap : wrap w z = z + modulus w).
    { replace z with ((z + modulus w) + (-1) * modulus w) at 1 by ring.
      rewrite wrap_add_modulus. apply wrap_id. unfold is_word. lia. }
    rewrite Hwrap.
    assert (Hhalf : (z + modulus w <? half w) = false) by (apply Z.ltb_ge; lia).
    rewrite Hhalf. lia.
Qed.

Lemma half_extension : forall w extra, half w <= half (w + extra)%positive.
Proof.
  intros w extra. unfold half. rewrite Pos2Z.inj_add. apply Z.pow_le_mono_r; lia.
Qed.

Lemma modulus_extension : forall w extra, modulus w <= half (w + extra)%positive.
Proof.
  intros w extra. unfold modulus, half. rewrite Pos2Z.inj_add.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma signed_extension : forall w extra x,
  signed (w + extra)%positive (signed w x) = signed w x.
Proof.
  intros w extra x. apply signed_in_range.
  pose proof (signed_range_value w x). pose proof (half_extension w extra). lia.
Qed.

Lemma sign_top_sound : forall w z, sign_gamma w sign_top z.
Proof.
  intros w z. split; [|split]; intros _; reflexivity.
Qed.

Lemma sign_forward_one_sound : forall o w a x rw z,
  is_word w x -> sign_gamma w a x -> eval_op o [(w, x)] = Some (rw, z) ->
  sign_gamma rw (sign_forward o [(w, a)] rw) z.
Proof.
  intros o w a x rw z Hx Ha Heval. destruct o; try apply sign_top_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvnot w x wnot eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply sign_not_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply sign_neg_sound.
  - change (Some ((w + extra)%positive, wrap (w + extra)%positive (wrap w x)) =
      Some (rw, z)) in Heval.
    inversion Heval; subst rw z. unfold sign_gamma. cbn [sign_forward neg zero pos].
    rewrite signed_wrap_value.
    assert (Hsigned : signed (w + extra)%positive (wrap w x) = wrap w x).
    { apply signed_in_range. pose proof (wrap_is_word w x) as [Hlo Hhi].
      pose proof (modulus_extension w extra). pose proof (half_pos (w + extra)%positive).
      lia. }
    rewrite Hsigned. pose proof (wrap_is_word w x) as [Hlo Hhi].
    split; [intros Hbad; lia|]. split; intros _; reflexivity.
  - change (Some ((w + extra)%positive,
      wrap (w + extra)%positive (signed w (wrap w x))) = Some (rw, z)) in Heval.
    inversion Heval; subst rw z. change (sign_gamma (w + extra)%positive a
      (wrap (w + extra)%positive (signed w (wrap w x)))).
    unfold sign_gamma. rewrite !signed_wrap_value, signed_extension. exact Ha.
Qed.

Lemma sign_forward_two_sound : forall o w v a b x y rw z,
  is_word w x -> is_word v y -> sign_gamma w a x -> sign_gamma v b y ->
  eval_op o [(w, x); (v, y)] = Some (rw, z) ->
  sign_gamma rw (sign_forward o [(w, a); (v, b)] rw) z.
Proof.
  intros o w v a b x y rw z Hx Hy Ha Hb Heval.
  destruct o; try apply sign_top_sound.
  all: assert (Hwv : w = v) by
    (pose proof (eval_op_width _ _ _ Heval) as Hwidth;
     cbn [result_width map fst] in Hwidth;
     destruct (Pos.eqb w v) eqn:Hwv; [now apply Pos.eqb_eq|discriminate]); subst v.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvand w x y wand eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply sign_and_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvor w x y wor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply sign_or_sound.
  - pose proof (eq_trans (eq_sym (eval_op_fun2 bvxor w x y wxor eq_refl)) Heval) as Hr.
    inversion Hr; subst rw z. now apply sign_xor_sound.
  - exact (sign_compare_sound bveq w a b x y rw z ltac:(tauto) Ha Hb Heval).
  - exact (sign_compare_sound bvne w a b x y rw z ltac:(tauto) Ha Hb Heval).
  - exact (sign_compare_sound bvult w a b x y rw z ltac:(tauto) Ha Hb Heval).
  - exact (sign_compare_sound bvule w a b x y rw z ltac:(tauto) Ha Hb Heval).
  - exact (sign_compare_sound bvslt w a b x y rw z ltac:(tauto) Ha Hb Heval).
  - exact (sign_compare_sound bvsle w a b x y rw z ltac:(tauto) Ha Hb Heval).
Qed.

Lemma sign_join_sound : forall w a b z, sign_gamma w a z \/ sign_gamma w b z ->
  sign_gamma w (join sign_lattice a b) z.
Proof.
  intros w a b z [Ha|Hb]; unfold sign_gamma in *; cbn.
  - destruct Ha as [Hn [Hz Hp]]. split; [|split]; intro Hsign.
    + rewrite (Hn Hsign). reflexivity.
    + rewrite (Hz Hsign). reflexivity.
    + rewrite (Hp Hsign). reflexivity.
  - destruct Hb as [Hn [Hz Hp]]. split; [|split]; intro Hsign.
    + rewrite (Hn Hsign). apply orb_true_r.
    + rewrite (Hz Hsign). apply orb_true_r.
    + rewrite (Hp Hsign). apply orb_true_r.
Qed.

Lemma sign_forward_three_sound : forall o w v u a b c x y t rw z,
  is_word w x -> is_word v y -> is_word u t ->
  sign_gamma w a x -> sign_gamma v b y -> sign_gamma u c t ->
  eval_op o [(w, x); (v, y); (u, t)] = Some (rw, z) ->
  sign_gamma rw (sign_forward o [(w, a); (v, b); (u, c)] rw) z.
Proof.
  intros o w v u a b c x y t rw z Hx Hy Ht Ha Hb Hc Heval.
  destruct o; try apply sign_top_sound.
  pose proof (eval_op_width _ _ _ Heval) as Hwidth.
  cbn [result_width map fst] in Hwidth.
  destruct (Pos.eqb w 1 && Pos.eqb v u) eqn:Hshape; [|discriminate].
  apply andb_true_iff in Hshape as [Hw Hvu]. apply Pos.eqb_eq in Hw, Hvu. subst w u.
  pose proof (eq_trans (eq_sym (eval_op_ite v y t x)) Heval) as Hr.
  inversion Hr; subst rw z. cbn [sign_forward]. apply sign_join_sound.
  destruct (wrap 1%positive x =? 1); rewrite wrap_id by assumption; auto.
Qed.

Lemma sign_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound sign_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  sign_gamma rw (sign_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval.
  destruct wps as [|[w a] [|[v b] [|[u c] [|wp rest]]]].
  - destruct o; apply sign_top_sound.
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst. inversion Htail; subst.
    destruct y as [wy x]. destruct Hhead as [Hwx [Hx Ha]]. cbn in Hwx, Hx, Ha. subst wy.
    exact (sign_forward_one_sound o w a x rw z Hx Ha Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
    destruct y as [wy x], y' as [vy y].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
    cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
    exact (sign_forward_two_sound o w v a b x y rw z Hx Hy Ha Hb Heval).
  - inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
    inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst.
    inversion Htail' as [|wp y'' wps' tail'' Hhead'' Htail'']; subst.
    inversion Htail''; subst. destruct y as [wy x], y' as [vy y], y'' as [uy t].
    destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]], Hhead'' as [Hut [Ht Hc]].
    cbn in Hwx, Hvy, Hut, Hx, Hy, Ht, Ha, Hb, Hc. subst wy vy uy.
    exact (sign_forward_three_sound o w v u a b c x y t rw z Hx Hy Ht Ha Hb Hc Heval).
  - destruct o; apply sign_top_sound.
Qed.

Lemma sign_leb_fields : forall a b, leb sign_lattice a b = true ->
  (neg a = true -> neg b = true) /\ (zero a = true -> zero b = true) /\
  (pos a = true -> pos b = true).
Proof.
  intros [a b c] [d e f]. destruct a, b, c, d, e, f; cbn;
    intro Hle; try discriminate; intuition congruence.
Qed.

(** Sign sets satisfy the complete payload-domain contract. *)
Theorem sign_word_laws : word_laws sign_domain sign_gamma.
Proof.
  constructor.
  - intros w. exact sign_laws.
  - intros w a b z Hle [Hn [Hz Hp]].
    destruct (sign_leb_fields a b Hle) as [Hneg [Hzero Hpos]].
    split; [|split]; intro Hsign; auto.
  - intros w z [Hn [Hz Hp]].
    destruct (Z.lt_trichotomy (signed w z) 0) as [Hneg|[Hzero|Hpos]].
    + discriminate (Hn Hneg).
    + discriminate (Hz Hzero).
    + discriminate (Hp Hpos).
  - intros w z Hword. apply sign_top_sound.
  - intros w z. unfold sign_gamma. cbn [sign_domain pconst sign_const neg zero pos].
    rewrite signed_wrap_value. split; [|split]; intro Hsign.
    + now apply Z.ltb_lt.
    + now apply Z.eqb_eq.
    + now apply Z.ltb_lt.
  - apply sign_forward_sound.
  - intros o wps ys rw z q Hgamma Heval Hq.
    clear Heval Hq.
    induction Hgamma as [|[w p] y rest tail Hhead Htail IH]; cbn; constructor.
    + exact (proj2 (proj2 Hhead)).
    + exact IH.
  - intros o wps rw q. induction wps as [|[w p] rest IH]; cbn; constructor.
    + apply (leb_refl sign_laws).
    + exact IH.
  - intros w a b z [Hn [Hz Hp]] [Hn' [Hz' Hp']].
    split; [|split]; cbn; intro Hsign; apply andb_true_iff; auto.
  - intros w [a b c] [d e f]. destruct a, b, c, d, e, f; reflexivity.
Qed.
