(** * Fixed-width words

    Words are integers reduced modulo a power of two.
    For example, wrapping 260 at width eight gives 4.
    Builds on: Rocq Stdlib integer arithmetic. *)

From Stdlib Require Import ZArith Lia.

Open Scope Z_scope.

(** Widths are strictly positive binary integers. *)
Definition width := positive.

(** The modulus is the first integer outside the unsigned word range. *)
Definition modulus (w : width) : Z := 2 ^ Zpos w.

(** Wrapping keeps the low bits of an integer. *)
Definition wrap (w : width) (z : Z) : Z := z mod modulus w.

(** An unsigned word lies between zero and the modulus. *)
Definition is_word (w : width) (z : Z) : Prop := 0 <= z < modulus w.

(** A dynamic word records its width and its integer value. *)
Definition word : Type := (width * Z)%type.

(** Half the modulus is the weight of the sign bit. *)
Definition half (w : width) : Z := 2 ^ (Zpos w - 1).

(** The most significant bit is read after wrapping. *)
Definition msb (w : width) (z : Z) : bool := Z.testbit (wrap w z) (Zpos w - 1).

(** The signed view interprets the highest bit as a negative weight. *)
Definition signed (w : width) (z : Z) : Z :=
  let z' := wrap w z in if z' <? half w then z' else z' - modulus w.

Lemma modulus_pos : forall w, 0 < modulus w.
Proof.
  intros w. unfold modulus. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma modulus_nonzero : forall w, modulus w <> 0.
Proof.
  intros w. pose proof (modulus_pos w). lia.
Qed.

Lemma half_pos : forall w, 0 < half w.
Proof.
  intros w. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma modulus_half : forall w, modulus w = 2 * half w.
Proof.
  intros w. unfold modulus, half.
  replace (Zpos w) with (Z.succ (Zpos w - 1)) at 1 by lia.
  apply Z.pow_succ_r. lia.
Qed.

Lemma width_lt_modulus : forall w, Zpos w < modulus w.
Proof.
  intros w. apply Z.pow_gt_lin_r; lia.
Qed.

(** Wrapping always produces an unsigned word. *)
Theorem wrap_is_word : forall w z, is_word w (wrap w z).
Proof.
  intros w z. apply Z.mod_pos_bound. apply modulus_pos.
Qed.

(** Wrapping fixes every unsigned word. *)
Theorem wrap_id : forall w z, is_word w z -> wrap w z = z.
Proof.
  intros w z Hword. apply Z.mod_small. exact Hword.
Qed.

(** Wrapping an already wrapped value has no effect. *)
Theorem wrap_wrap : forall w z, wrap w (wrap w z) = wrap w z.
Proof.
  intros w z. apply wrap_id. apply wrap_is_word.
Qed.

Lemma zero_is_word : forall w, is_word w 0.
Proof.
  intros w. pose proof (modulus_pos w). unfold is_word. lia.
Qed.

Lemma one_is_word : forall w, is_word w 1.
Proof.
  intros w. pose proof (width_lt_modulus w). unfold is_word. lia.
Qed.

Lemma wrap_0 : forall w, wrap w 0 = 0.
Proof.
  intros w. apply wrap_id. apply zero_is_word.
Qed.

Lemma wrap_1 : forall w, wrap w 1 = 1.
Proof.
  intros w. apply wrap_id. apply one_is_word.
Qed.

Lemma wrap_opp : forall w x, wrap w (- wrap w x) = wrap w (- x).
Proof.
  intros w x. unfold wrap. replace (- x) with (0 - x) by ring.
  rewrite Zminus_mod, Z.mod_0_l by apply modulus_nonzero.
  reflexivity.
Qed.

Lemma wrap_sub : forall w x y,
  wrap w (x - y) = wrap w (wrap w x - wrap w y).
Proof.
  intros w x y. apply Zminus_mod.
Qed.

Lemma wrap_add_modulus : forall w x k, wrap w (x + k * modulus w) = wrap w x.
Proof.
  intros w x k. apply Z.mod_add. apply modulus_nonzero.
Qed.

(** Addition can wrap its operands before computing. *)
Theorem wrap_add : forall w x y,
  wrap w (x + y) = wrap w (wrap w x + wrap w y).
Proof.
  intros w x y. apply Z.add_mod. apply modulus_nonzero.
Qed.

(** Multiplication can wrap its operands before computing. *)
Theorem wrap_mul : forall w x y,
  wrap w (x * y) = wrap w (wrap w x * wrap w y).
Proof.
  intros w x y. apply Z.mul_mod. apply modulus_nonzero.
Qed.

(** Narrowing after a wider wrap keeps the same low bits. *)
Theorem wrap_narrow : forall w w2 z,
  (w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z.
Proof.
  intros w w2 z Hwidth.
  assert (Hle : Zpos w <= Zpos w2) by (apply Pos2Z.pos_le_pos; exact Hwidth).
  unfold wrap, modulus.
  replace (Zpos w2) with (Zpos w + (Zpos w2 - Zpos w)) at 1 by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.mod_mod_divide.
  exists (2 ^ (Zpos w2 - Zpos w)). ring.
Qed.
