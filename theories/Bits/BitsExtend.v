(** * Changing word widths

    Extension preserves unsigned or signed values, while truncation keeps low bits.
    For example, sign-extending the eight-bit word 255 gives the sixteen-bit word 65535.
    Builds on: BitsWord, BitsFun, BitsTestbit, BitsSigned, BitsOp and BitsExpr. *)

From Stdlib Require Import ZArith List Bool Lia Ring.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsSigned BitsOp BitsExpr.
Import List.ListNotations Bits.

Open Scope Z_scope.

(** * Width bounds and extension *)

Lemma modulus_monotone : forall w t, (w <= t)%positive -> modulus w <= modulus t.
Proof.
  intros w t Hle. unfold modulus. apply Z.pow_le_mono_r; [lia|].
  apply Pos2Z.pos_le_pos. exact Hle.
Qed.

Lemma width_add_le : forall w n, (w <= w + n)%positive.
Proof.
  intros w n. apply Pos.lt_le_incl. apply Pos.lt_add_r.
Qed.

Lemma word_widen : forall w t x, (w <= t)%positive -> is_word w x -> is_word t x.
Proof.
  intros w t x Hle Hx. pose proof (modulus_monotone w t Hle).
  unfold is_word in *. lia.
Qed.

Lemma half_monotone : forall w t, (w <= t)%positive -> half w <= half t.
Proof.
  intros w t Hle. unfold half. apply Z.pow_le_mono_r; [lia|].
  apply Pos2Z.pos_le_pos in Hle. lia.
Qed.

(** Zero extension preserves the normalized unsigned value. *)
Theorem zext_value : forall env w n x, env 0%nat = (w, x) ->
  eval env (App (bvzext n) [Var 0]) = Some ((w + n)%positive, wrap w x).
Proof.
  intros env w n x Henv. cbn [eval]. rewrite Henv.
  cbn [eval_op result_width map fst snd normalize_word op_value].
  rewrite wrap_wrap. rewrite wrap_id; [reflexivity|].
  eapply word_widen; [apply width_add_le|apply wrap_is_word].
Qed.

(** Sign extension wraps the original signed interpretation at the larger width. *)
Theorem sext_value : forall env w n x, env 0%nat = (w, x) ->
  eval env (App (bvsext n) [Var 0]) =
    Some ((w + n)%positive, wrap (w + n)%positive (signed w x)).
Proof.
  intros env w n x Henv. cbn [eval]. rewrite Henv.
  cbn [eval_op result_width map fst snd normalize_word op_value].
  now rewrite wrap_wrap, signed_wrap.
Qed.

(** Sign extension preserves the signed value. *)
Theorem sext_signed : forall env w n x, env 0%nat = (w, x) -> exists z,
  eval env (App (bvsext n) [Var 0]) = Some ((w + n)%positive, z) /\
  signed (w + n)%positive z = signed w x.
Proof.
  intros env w n x Henv. exists (wrap (w + n)%positive (signed w x)).
  split; [now apply sext_value|]. rewrite signed_wrap. apply signed_id.
  pose proof (signed_range w x).
  pose proof (half_monotone w (w + n)%positive (width_add_le w n)). lia.
Qed.

(** * Truncation *)

Lemma eval_trunc_value : forall env e w t x, eval env e = Some (w, x) ->
  (t <= w)%positive -> eval env (App (bvtrunc t) [e]) = Some (t, wrap t x).
Proof.
  intros env e w t x Heval Hle. rewrite eval_app, eval_args_cons, Heval, eval_args_nil.
  assert (Hwidth : result_width (bvtrunc t) [w] = Some t).
  { cbn [result_width]. now rewrite (proj2 (Pos.leb_le t w) Hle). }
  change (eval_op (bvtrunc t) [(w, x)] = Some (t, wrap t x)).
  unfold eval_op. cbn [map fst]. rewrite Hwidth.
  cbn [op_value normalize_word map fst snd]. now rewrite wrap_narrow by exact Hle.
Qed.

(** Truncating a zero extension recovers the original word. *)
Theorem trunc_zext : forall env w n x, env 0%nat = (w, x) ->
  eval env (App (bvtrunc w) [App (bvzext n) [Var 0]]) = Some (w, wrap w x).
Proof.
  intros env w n x Henv. rewrite <- (wrap_wrap w x).
  eapply eval_trunc_value; [now apply zext_value|apply width_add_le].
Qed.

(** Truncating a sign extension recovers the original word. *)
Theorem trunc_sext : forall env w n x, env 0%nat = (w, x) ->
  eval env (App (bvtrunc w) [App (bvsext n) [Var 0]]) = Some (w, wrap w x).
Proof.
  intros env w n x Henv.
  pose proof (eval_trunc_value env (App (bvsext n) [Var 0])
    (w + n)%positive w _ (sext_value env w n x Henv) (width_add_le w n)) as Htrunc.
  rewrite wrap_narrow, wrap_signed in Htrunc by apply width_add_le. exact Htrunc.
Qed.

(** Truncation commutes with word addition. *)
Theorem trunc_wadd : forall env w t x y,
  env 0%nat = (w, x) -> env 1%nat = (w, y) -> (t <= w)%positive ->
  eval env (App (bvtrunc t) [App bvadd [Var 0; Var 1]]) = Some (t, wadd t x y).
Proof.
  intros env w t x y Hx Hy Hle.
  assert (Hadd : eval env (App bvadd [Var 0; Var 1]) = Some (w, wadd w x y)).
  { cbn [eval]. rewrite Hx, Hy. cbn [fst snd].
    rewrite (eval_op_fun2 bvadd w _ _ wadd eq_refl).
    unfold wadd. now rewrite <- wrap_add. }
  pose proof (eval_trunc_value env _ w t _ Hadd Hle) as Htrunc.
  unfold wadd in *. rewrite wrap_narrow in Htrunc by exact Hle. exact Htrunc.
Qed.

(** * Concatenation and extraction *)

Lemma modulus_add : forall w w2, modulus (w + w2)%positive = modulus w * modulus w2.
Proof.
  intros w w2. unfold modulus. rewrite Pos2Z.inj_add. apply Z.pow_add_r; lia.
Qed.

Lemma concat_is_word : forall w w2 x y,
  is_word (w + w2)%positive (wrap w x * modulus w2 + wrap w2 y).
Proof.
  intros w w2 x y. pose proof (wrap_is_word w x) as Hx.
  pose proof (wrap_is_word w2 y) as Hy. pose proof (modulus_pos w2).
  unfold is_word in *. rewrite modulus_add. nia.
Qed.

Lemma eval_concat_value : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval env (App bvconcat [Var 0; Var 1]) =
    Some ((w + w2)%positive, wrap w x * modulus w2 + wrap w2 y).
Proof.
  intros env w w2 x y Hx Hy. cbn [eval]. rewrite Hx, Hy.
  cbn [eval_op result_width map fst snd normalize_word op_value].
  rewrite !wrap_wrap. rewrite wrap_id by apply concat_is_word. reflexivity.
Qed.

(** Truncation of a concatenation recovers its low operand. *)
Theorem trunc_concat_lo : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval env (App (bvtrunc w2) [App bvconcat [Var 0; Var 1]]) = Some (w2, wrap w2 y).
Proof.
  intros env w w2 x y Hx Hy.
  assert (Hle : (w2 <= w + w2)%positive).
  { rewrite Pos.add_comm. apply width_add_le. }
  pose proof (eval_trunc_value env _ _ w2 _ (eval_concat_value env w w2 x y Hx Hy) Hle)
    as Htrunc.
  replace (wrap w x * modulus w2 + wrap w2 y) with
    (wrap w2 y + wrap w x * modulus w2) in Htrunc by ring.
  rewrite wrap_add_modulus, wrap_wrap in Htrunc. exact Htrunc.
Qed.

(** Extracting the high positions of a concatenation recovers its first operand. *)
Theorem extract_concat_hi : forall env w w2 x y,
  env 0%nat = (w, x) -> env 1%nat = (w2, y) ->
  eval env (App (bvextract (Pos.to_nat (w + w2)%positive - 1)%nat (Pos.to_nat w2))
    [App bvconcat [Var 0; Var 1]]) = Some (w, wrap w x).
Proof.
  intros env w w2 x y Hx Hy. rewrite eval_app, eval_args_cons,
    (eval_concat_value env w w2 x y Hx Hy), eval_args_nil.
  assert (Hw : (0 < Pos.to_nat w)%nat) by apply Pos2Nat.is_pos.
  assert (Hw2 : (0 < Pos.to_nat w2)%nat) by apply Pos2Nat.is_pos.
  assert (Hwidth : result_width
    (bvextract (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat w2))
    [(w + w2)%positive] = Some w).
  { change ((if (Nat.leb (Pos.to_nat w2) (Pos.to_nat (w + w2)%positive - 1) &&
      Nat.ltb (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat (w + w2)%positive))%bool
      then Some (Pos.of_nat (S (Pos.to_nat (w + w2)%positive - 1 - Pos.to_nat w2)))
      else None) = Some w).
    rewrite Pos2Nat.inj_add.
    rewrite (proj2 (Nat.leb_le (Pos.to_nat w2)
      (Pos.to_nat w + Pos.to_nat w2 - 1)) ltac:(lia)),
      (proj2 (Nat.ltb_lt (Pos.to_nat w + Pos.to_nat w2 - 1)
        (Pos.to_nat w + Pos.to_nat w2)) ltac:(lia)). cbn [andb].
    replace (S (Pos.to_nat w + Pos.to_nat w2 - 1 - Pos.to_nat w2))%nat
      with (Pos.to_nat w) by lia.
    now rewrite Pos2Nat.id. }
  change (eval_op (bvextract (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat w2))
    [((w + w2)%positive, wrap w x * modulus w2 + wrap w2 y)] = Some (w, wrap w x)).
  change ((match result_width
    (bvextract (Pos.to_nat (w + w2)%positive - 1) (Pos.to_nat w2)) [(w + w2)%positive]
    with
    | Some rw => Some (rw, wrap rw
        (wrap (w + w2)%positive (wrap w x * modulus w2 + wrap w2 y) /
          2 ^ Z.of_nat (Pos.to_nat w2)))
    | None => None
    end) = Some (w, wrap w x)).
  rewrite Hwidth.
  rewrite (wrap_id (w + w2)%positive _ (concat_is_word w w2 x y)).
  rewrite positive_nat_Z. fold (modulus w2).
  replace (wrap w x * modulus w2 + wrap w2 y) with
    (wrap w2 y + wrap w x * modulus w2) by ring.
  rewrite Z.div_add by apply modulus_nonzero.
  rewrite Z.div_small by apply wrap_is_word.
  rewrite Z.add_0_l, wrap_wrap. reflexivity.
Qed.
