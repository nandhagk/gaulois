(** * Selectable partial-product known-bit multiplication

    A width-bounded shift-and-add loop retains known bits of partial products.
    For example, multiplying an unknown low bit by four keeps every bit except bit two clear.
    Builds on: DomainsKnownBits, DomainsNumeric and the Bits word arithmetic. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Gaulois.Domains Require Import DomainsNumeric DomainsKnownBits.
Import List.ListNotations.

Open Scope Z_scope.

(** * The partial-product loop *)

Local Definition tnum_mul_step (w : width) (a b : tnum) (s : Z * tnum) : Z * tnum :=
  let '(i, r) := s in
  (Z.succ i,
    if Z.testbit (zeros b) i then r
    else
      let sum := tnum_add w r (tnum_scalar bvshl w i a) in
      if Z.testbit (ones b) i then sum else tnum_join w r sum).

(* The binary iterator performs exactly [n] stages; its index records the processed prefix. *)
Local Definition tnum_mul_loop (w : width) (a b : tnum) (n : N) : Z * tnum :=
  N.iter n (tnum_mul_step w a b) (0, tnum_const w 0).

(** Accumulate shifted partial products, joining the two choices of every unknown bit. *)
Definition tnum_mul_precise (w : width) (a b : tnum) : tnum :=
  if tnum_empty w a || tnum_empty w b then bot (tnum_lattice w)
  else snd (tnum_mul_loop w a b (Npos w)).

Local Lemma tnum_mul_prefix : forall y i, 0 <= i ->
  y mod 2 ^ (i + 1) = y mod 2 ^ i + Z.b2z (Z.testbit y i) * 2 ^ i.
Proof.
  intros y i Hi.
  pose proof (Z.pow_pos_nonneg 2 i ltac:(lia) Hi) as Hpower.
  destruct (Z.testbit_spec y i Hi) as [l [h [Hl Heq]]].
  assert (Hlow : y mod 2 ^ i = l).
  { symmetry. apply Z.mod_unique with (q := Z.b2z (Z.testbit y i) + 2 * h).
    - left. exact Hl.
    - nia. }
  rewrite Hlow. symmetry. apply Z.mod_unique with (q := h).
  - left. rewrite Z.pow_add_r, Z.pow_1_r by lia.
    destruct (Z.testbit y i); cbn [Z.b2z]; lia.
  - rewrite Z.pow_add_r, Z.pow_1_r by lia. nia.
Qed.

(** * Exact constants *)

Local Lemma tnum_mul_const_endpoints : forall w z,
  tnum_min w (tnum_const w z) = wrap w z /\
  tnum_max w (tnum_const w z) = wrap w z /\
  tnum_mask w (tnum_const w z) = 0.
Proof.
  intros w z. split.
  - apply wrap_wrap.
  - split.
    + unfold tnum_max, tnum_const. cbn [zeros]. unfold wnot at 1.
      rewrite wrap_id by apply wnot_is_word. unfold wnot. ring.
    + apply Z.bits_inj'. intros i Hi.
      unfold tnum_mask. rewrite testbit_wnot_full, Z.bits_0 by exact Hi.
      destruct (i <? Zpos w) eqn:Hlow; [|reflexivity].
      apply Z.ltb_lt in Hlow.
      rewrite tnum_or_bit by lia. cbn [tnum_const zeros ones].
      rewrite tnum_not_bit, tnum_wrap_bit by lia.
      destruct (Z.testbit z i); reflexivity.
Qed.

Local Lemma tnum_mul_wrap_not : forall w z, wrap w (Z.lnot z) = wnot w z.
Proof.
  intros w z. apply Z.bits_inj'. intros i Hi.
  rewrite testbit_wrap, Z.lnot_spec, testbit_wnot_full by exact Hi. reflexivity.
Qed.

Local Lemma tnum_mul_const_wrap : forall w z, tnum_const w (wrap w z) = tnum_const w z.
Proof.
  intros w z. unfold tnum_const, wnot. now rewrite wrap_wrap.
Qed.

Local Lemma tnum_mul_add_constants : forall w x y,
  tnum_add w (tnum_const w x) (tnum_const w y) = tnum_const w (wadd w x y).
Proof.
  intros w x y.
  destruct (tnum_mul_const_endpoints w x) as [Hxmin [Hxmax Hxmask]].
  destruct (tnum_mul_const_endpoints w y) as [Hymin [Hymax Hymask]].
  unfold tnum_add, tnum_adc, tnum_adc_uncertain.
  rewrite Hxmin, Hxmax, Hxmask, Hymin, Hymax, Hymask.
  cbn [Z.b2z]. rewrite Z.lxor_nilpotent, !Z.lor_0_r, Z.lnot_0, Z.land_m1_r.
  rewrite tnum_mul_wrap_not, !Z.add_0_r.
  rewrite <- (wrap_add w x y).
  unfold wadd. rewrite tnum_mul_const_wrap.
  unfold tnum_const, wnot. now rewrite <- wrap_add.
Qed.

Local Lemma tnum_mul_shift_constants : forall w i x,
  tnum_scalar bvshl w i (tnum_const w x) =
    tnum_const w (tnum_scalar_value bvshl w i x).
Proof.
  intros w i x.
  destruct (tnum_mul_const_endpoints w x) as [Hmin [Hmax _]].
  unfold tnum_scalar, tnum_map. rewrite Hmin, Hmax.
  cbn [tnum_scalar_value]. unfold wshl. rewrite wrap_wrap. reflexivity.
Qed.

Local Lemma tnum_mul_partial_add : forall w x y i, 0 <= i < Zpos w -> is_word w x ->
  wrap w (x * (y mod 2 ^ (i + 1))) =
    if Z.testbit y i then
      wadd w (wrap w (x * (y mod 2 ^ i))) (tnum_scalar_value bvshl w i x)
    else wrap w (x * (y mod 2 ^ i)).
Proof.
  intros w x y i Hi Hx. rewrite tnum_mul_prefix by lia.
  destruct (Z.testbit y i); cbn [Z.b2z].
  - cbn [tnum_scalar_value]. rewrite Z.min_l by lia.
    rewrite <- (wmul_wshl w x i Hx Hi).
    unfold wadd, wmul. rewrite <- wrap_add. f_equal. ring.
  - f_equal. ring.
Qed.

Local Lemma tnum_mul_step_sound : forall w a b x y i r,
  0 <= i < Zpos w -> is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w r (wrap w (x * (y mod 2 ^ i))) ->
  tnum_gamma w (snd (tnum_mul_step w a b (i, r)))
    (wrap w (x * (y mod 2 ^ (i + 1)))).
Proof.
  intros w a b x y i r Hi Hx Ha Hb Hr.
  pose proof (tnum_scalar_sound bvshl w i a x ltac:(lia) Hx Ha) as Hshift.
  pose proof (tnum_add_sound w r _ _ _ Hr Hshift) as Hsum.
  apply tnum_gamma_bits in Hb. destruct Hb as [Hz Ho].
  rewrite tnum_mul_partial_add by assumption. cbn [tnum_mul_step snd].
  destruct (Z.testbit (zeros b) i) eqn:Hbz.
  - rewrite (Hz i Hi Hbz). exact Hr.
  - destruct (Z.testbit (ones b) i) eqn:Hbo.
    + rewrite (Ho i Hi Hbo). exact Hsum.
    + apply tnum_join_sound. destruct (Z.testbit y i); auto.
Qed.

Local Lemma tnum_mul_loop_sound : forall w a b x y,
  is_word w x -> tnum_gamma w a x -> tnum_gamma w b y ->
  forall n, Z.of_N n <= Zpos w ->
  fst (tnum_mul_loop w a b n) = Z.of_N n /\
  tnum_gamma w (snd (tnum_mul_loop w a b n))
    (wrap w (x * (y mod 2 ^ Z.of_N n))).
Proof.
  intros w a b x y Hx Ha Hb n. induction n using N.peano_ind; intro Hbound.
  - cbn [tnum_mul_loop N.iter fst snd Z.of_N].
    rewrite Z.mod_1_r, Z.mul_0_r. split; [reflexivity|apply tnum_const_sound].
  - rewrite N2Z.inj_succ in Hbound |- *.
    specialize (IHn ltac:(lia)).
    unfold tnum_mul_loop in *. rewrite N.iter_succ.
    destruct (N.iter n (tnum_mul_step w a b) (0, tnum_const w 0)) as [i r].
    cbn [fst snd] in IHn. destruct IHn as [-> Hr].
    split; [reflexivity|]. replace (Z.succ (Z.of_N n)) with (Z.of_N n + 1) by lia.
    apply tnum_mul_step_sound; try assumption; lia.
Qed.

(** Every concrete product is contained in the accumulated fixed-width partial products. *)
Theorem tnum_mul_precise_sound (w : width) (a b : tnum) (x y : Z) :
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_precise w a b) (wmul w x y).
Proof.
  intros Hx Hy Ha Hb. unfold tnum_mul_precise.
  rewrite (tnum_empty_sound w a x Ha), (tnum_empty_sound w b y Hb). cbn [orb].
  pose proof (tnum_mul_loop_sound w a b x y Hx Ha Hb (Npos w) ltac:(lia)) as [_ Hresult].
  change (tnum_gamma w (snd (tnum_mul_loop w a b (Npos w)))
    (wrap w (x * (y mod modulus w)))) in Hresult.
  rewrite (Z.mod_small y (modulus w) Hy) in Hresult.
  exact Hresult.
Qed.

Local Lemma tnum_mul_step_constants : forall w x y i,
  0 <= i < Zpos w -> is_word w x ->
  tnum_mul_step w (tnum_const w x) (tnum_const w y)
    (i, tnum_const w (wrap w (x * (y mod 2 ^ i)))) =
  (Z.succ i, tnum_const w (wrap w (x * (y mod 2 ^ (i + 1))))).
Proof.
  intros w x y i Hi Hx. unfold tnum_mul_step. f_equal.
  rewrite tnum_mul_partial_add by assumption.
  cbn [tnum_const zeros ones]. rewrite tnum_not_bit, tnum_wrap_bit by exact Hi.
  destruct (Z.testbit y i); cbn [negb].
  - rewrite tnum_mul_shift_constants, tnum_mul_add_constants. reflexivity.
  - reflexivity.
Qed.

Local Lemma tnum_mul_loop_constants : forall w x y,
  is_word w x -> forall n, Z.of_N n <= Zpos w ->
  tnum_mul_loop w (tnum_const w x) (tnum_const w y) n =
    (Z.of_N n, tnum_const w (wrap w (x * (y mod 2 ^ Z.of_N n)))).
Proof.
  intros w x y Hx n. induction n using N.peano_ind; intro Hbound.
  - cbn [tnum_mul_loop N.iter Z.of_N].
    rewrite Z.mod_1_r, Z.mul_0_r, wrap_0. reflexivity.
  - rewrite N2Z.inj_succ in Hbound |- *.
    unfold tnum_mul_loop. rewrite N.iter_succ.
    change (tnum_mul_step w (tnum_const w x) (tnum_const w y)
      (tnum_mul_loop w (tnum_const w x) (tnum_const w y) n) =
      (Z.succ (Z.of_N n),
        tnum_const w (wrap w (x * (y mod 2 ^ Z.succ (Z.of_N n)))))).
    rewrite IHn by lia.
    replace (Z.succ (Z.of_N n)) with (Z.of_N n + 1) at 2 by lia.
    apply tnum_mul_step_constants; [lia|exact Hx].
Qed.

(** Constant operands retain every bit of their wrapped concrete product. *)
Theorem tnum_mul_precise_constants (w : width) (x y : Z) :
  tnum_mul_precise w (pconst known_bits_domain w x) (pconst known_bits_domain w y) =
  pconst known_bits_domain w (wmul w x y).
Proof.
  change (tnum_mul_precise w (tnum_const w x) (tnum_const w y) =
    tnum_const w (wmul w x y)).
  unfold tnum_mul_precise.
  rewrite (tnum_empty_sound w (tnum_const w x) (wrap w x) (tnum_const_sound w x)),
    (tnum_empty_sound w (tnum_const w y) (wrap w y) (tnum_const_sound w y)).
  cbn [orb].
  rewrite <- (tnum_mul_const_wrap w x), <- (tnum_mul_const_wrap w y).
  rewrite tnum_mul_loop_constants by (try apply wrap_is_word; lia).
  change (tnum_const w (wrap w (wrap w x * (wrap w y mod modulus w))) =
    tnum_const w (wmul w x y)).
  rewrite (Z.mod_small (wrap w y) (modulus w)) by apply wrap_is_word.
  unfold wmul. now rewrite <- wrap_mul.
Qed.

(** * The selectable word domain *)

Local Definition tnum_precise_forward (o : op) (wps : list (width * tnum))
    (rw : width) : tnum :=
  match o, wps with
  | bvmul, [(w, a); (v, b)] =>
    if Pos.eqb w rw && Pos.eqb v rw then tnum_mul_precise rw a b
    else pforward known_bits_domain o wps rw
  | _, _ => pforward known_bits_domain o wps rw
  end.

(** Select precise multiplication while retaining every other known-bit operation and law. *)
Definition known_bits_precise_domain : word_domain tnum :=
  {| plat := plat known_bits_domain;
     ptop := ptop known_bits_domain;
     pconst := pconst known_bits_domain;
     pforward := tnum_precise_forward;
     passume := passume known_bits_domain;
     pmeet := pmeet known_bits_domain |}.

Local Lemma tnum_precise_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound tnum_gamma) wps ys -> eval_op o ys = Some (rw, z) ->
  tnum_gamma rw (tnum_precise_forward o wps rw) z.
Proof.
  intros o wps ys rw z Hgamma Heval.
  pose proof (pforward_sound known_bits_word_laws o wps ys rw z Hgamma Heval) as Hold.
  destruct o; try exact Hold.
  destruct wps as [|[w a] [|[v b] [|extra rest]]]; try exact Hold.
  cbn [tnum_precise_forward].
  destruct (Pos.eqb w rw && Pos.eqb v rw) eqn:Hwidth; [|exact Hold].
  apply andb_true_iff in Hwidth as [Hw Hv].
  apply Pos.eqb_eq in Hw, Hv. subst w v.
  inversion Hgamma as [|wp y wps' tail Hhead Htail]; subst.
  inversion Htail as [|wp y' wps' tail' Hhead' Htail']; subst. inversion Htail'; subst.
  destruct y as [wy x], y' as [vy y].
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Hx, Hy, Ha, Hb. subst wy vy.
  pose proof (eval_op_fun2 bvmul rw x y wmul eq_refl) as Hmul.
  assert (Hresult : Some (rw, z) = Some (rw, wmul rw x y)).
  { transitivity (eval_op bvmul [(rw, x); (rw, y)]).
    - symmetry. exact Heval.
    - exact Hmul. }
  injection Hresult as Hz. rewrite Hz. now apply tnum_mul_precise_sound.
Qed.

(** The selectable domain satisfies the same total word soundness interface. *)
Theorem known_bits_precise_word_laws : word_laws known_bits_precise_domain tnum_gamma.
Proof.
  constructor.
  - exact (plat_laws known_bits_word_laws).
  - exact (pgamma_monotone known_bits_word_laws).
  - exact (pgamma_bot_empty known_bits_word_laws).
  - exact (ptop_sound known_bits_word_laws).
  - exact (pconst_sound known_bits_word_laws).
  - apply tnum_precise_forward_sound.
  - exact (passume_sound known_bits_word_laws).
  - exact (passume_refines known_bits_word_laws).
  - exact (pmeet_sound known_bits_word_laws).
  - exact (pmeet_lower_left known_bits_word_laws).
Qed.
