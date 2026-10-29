(** * While word-operator bridge

    Independent While integer operations agree with expressions of the word language.
    For example, a masked shift uses the low five bits of its second operand.
    Builds on: While semantics and Bits expressions, operators and word laws. *)

From Stdlib Require Import List ZArith Lia.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit BitsOp BitsExpr.
From Gaulois.Examples.While Require Import ExamplesWhileSyntax ExamplesWhileSemantics.
Import List.ListNotations.

Open Scope Z_scope.

(** Unary operators use a 32-bit operand and extend a Boolean result when necessary. *)
Definition un_bits (o : unop) : Bits.expr :=
  match o with
  | Neg => Bits.App bvneg [Bits.Var 0]
  | BNot => Bits.App bvnot [Bits.Var 0]
  | LNot => Bits.App (bvzext 31) [Bits.App bveq [Bits.Var 0; Bits.Const 32%positive 0]]
  end.

(** Binary operators mask shift counts and extend one-bit comparison results. *)
Definition bin_bits (o : binop) : Bits.expr :=
  match o with
  | Add => Bits.App bvadd [Bits.Var 0; Bits.Var 1]
  | Sub => Bits.App bvsub [Bits.Var 0; Bits.Var 1]
  | Mul => Bits.App bvmul [Bits.Var 0; Bits.Var 1]
  | And => Bits.App bvand [Bits.Var 0; Bits.Var 1]
  | Or => Bits.App bvor [Bits.Var 0; Bits.Var 1]
  | Xor => Bits.App bvxor [Bits.Var 0; Bits.Var 1]
  | Shl => Bits.App bvshl [Bits.Var 0; Bits.App bvand [Bits.Var 1; Bits.Const 32%positive 31]]
  | ShrU => Bits.App bvlshr [Bits.Var 0; Bits.App bvand [Bits.Var 1; Bits.Const 32%positive 31]]
  | ShrS => Bits.App bvashr [Bits.Var 0; Bits.App bvand [Bits.Var 1; Bits.Const 32%positive 31]]
  | Eq => Bits.App (bvzext 31) [Bits.App bveq [Bits.Var 0; Bits.Var 1]]
  | Ne => Bits.App (bvzext 31) [Bits.App bvne [Bits.Var 0; Bits.Var 1]]
  | LtU => Bits.App (bvzext 31) [Bits.App bvult [Bits.Var 0; Bits.Var 1]]
  | LeU => Bits.App (bvzext 31) [Bits.App bvule [Bits.Var 0; Bits.Var 1]]
  | LtS => Bits.App (bvzext 31) [Bits.App bvslt [Bits.Var 0; Bits.Var 1]]
  | LeS => Bits.App (bvzext 31) [Bits.App bvsle [Bits.Var 0; Bits.Var 1]]
  end.

(** The two distinguished variables hold the supplied 32-bit operands. *)
Definition env2 (a b : Z) : nat -> width * Z :=
  fun i => (32%positive, if Nat.eqb i 0 then a else b).

Local Lemma eval_unary a b o f :
  word_fun1 o = Some f -> result_width o [32%positive] = Some 32%positive ->
  Bits.eval (env2 a b) (Bits.App o [Bits.Var 0]) =
    Some (32%positive, f 32%positive (wrap 32%positive a)).
Proof.
  intros Hfun Hwidth.
  pose proof (word_fun1_is_word o f 32%positive (wrap 32%positive a) Hfun) as Hrange.
  destruct o; cbn [word_fun1] in Hfun; try discriminate; injection Hfun as <-.
  all: cbn [Bits.eval env2 Nat.eqb Pos.eqb eval_op result_width List.map fst snd normalize_word
    op_value word_fun1]; rewrite !wrap_wrap, (wrap_id _ _ Hrange); reflexivity.
Qed.

Local Lemma eval_binary a b o f :
  word_fun2 o = Some f -> result_width o [32%positive; 32%positive] = Some 32%positive ->
  Bits.eval (env2 a b) (Bits.App o [Bits.Var 0; Bits.Var 1]) =
    Some (32%positive, f 32%positive (wrap 32%positive a) (wrap 32%positive b)).
Proof.
  intros Hfun Hwidth.
  pose proof (word_fun2_is_word o f 32%positive
    (wrap 32%positive a) (wrap 32%positive b) Hfun) as Hrange.
  destruct o; cbn [word_fun2] in Hfun; try discriminate; injection Hfun as <-.
  all: cbn [Bits.eval env2 Nat.eqb Pos.eqb eval_op result_width List.map fst snd normalize_word
    op_value word_fun2]; rewrite !wrap_wrap, (wrap_id _ _ Hrange); reflexivity.
Qed.

Local Lemma signed32_agrees a :
  is_word 32%positive a -> signed 32%positive a = signed32 a.
Proof.
  intro Hword; unfold signed; rewrite (wrap_id _ _ Hword); reflexivity.
Qed.

(** Each unary translation returns exactly the independently specified While value. *)
Theorem un_bridge (o : unop) (a : Z) :
  is_word 32%positive a ->
  Bits.eval (env2 a 0) (un_bits o) = Some (32%positive, eval_un o a).
Proof.
  intro Hword; destruct o; cbn [un_bits].
  - rewrite (eval_unary a 0 bvneg wneg eq_refl eq_refl).
    unfold wneg; rewrite (wrap_id _ _ Hword); reflexivity.
  - rewrite (eval_unary a 0 bvnot wnot eq_refl eq_refl).
    unfold wnot; rewrite wrap_wrap, (wrap_id _ _ Hword); reflexivity.
  - cbn [un_bits Bits.eval env2 Nat.eqb Pos.eqb eval_op result_width
      List.map normalize_word fst snd
      op_value word_fun2 word_cmp].
    rewrite !wrap_wrap, (wrap_id _ _ Hword), wrap_0.
    cbn [eval_un]; destruct (Z.eqb a 0); reflexivity.
Qed.

Local Lemma shift_mask b : Z.land b 31 = b mod 32.
Proof.
  change (Z.land b (Z.ones 5) = b mod 2 ^ 5).
  apply Z.land_ones; lia.
Qed.

Local Lemma shift_amount_word b : is_word 32%positive (b mod 32).
Proof.
  pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  unfold is_word, modulus; cbn; lia.
Qed.

Local Lemma eval_shift a b o f :
  word_fun2 o = Some f -> is_word 32%positive a -> is_word 32%positive b ->
  Bits.eval (env2 a b)
    (Bits.App o [Bits.Var 0; Bits.App bvand [Bits.Var 1; Bits.Const 32%positive 31]]) =
  Some (32%positive, f 32%positive a (b mod 32)).
Proof.
  intros Hfun Ha Hb.
  cbn [Bits.eval env2 Nat.eqb fst snd].
  rewrite (eval_op_fun2 bvand 32%positive _ _ wand eq_refl).
  unfold wand; rewrite !wrap_wrap, (wrap_id _ _ Hb), shift_mask.
  rewrite (wrap_id _ _ Ha).
  apply eval_op_fun2; exact Hfun.
Qed.

Local Lemma shift_small b : (32 <=? wrap 32%positive (b mod 32)) = false.
Proof.
  rewrite wrap_id by apply shift_amount_word.
  apply Z.leb_gt; apply Z.mod_pos_bound; lia.
Qed.

Local Lemma comparison_bridge (o : binop) (a b : Z) :
  is_word 32%positive a -> is_word 32%positive b ->
  match o with
  | Eq | Ne | LtU | LeU | LtS | LeS =>
    Bits.eval (env2 a b) (bin_bits o) = Some (32%positive, eval_bin o a b)
  | _ => True
  end.
Proof.
  intros Ha Hb; destruct o; try exact I.
  all: cbn [bin_bits Bits.eval env2 Nat.eqb Pos.eqb eval_op result_width
    List.map normalize_word fst snd op_value word_fun2 word_cmp];
    rewrite !wrap_wrap, (wrap_id _ _ Ha), (wrap_id _ _ Hb);
    unfold wult, wule, wslt, wsle;
    rewrite ?(wrap_id _ _ Ha), ?(wrap_id _ _ Hb),
      ?(signed32_agrees a Ha), ?(signed32_agrees b Hb); cbn [eval_bin].
  all: first [solve [destruct (Z.eqb a b); reflexivity] |
    solve [destruct (Z.ltb a b); reflexivity] |
    solve [destruct (Z.leb a b); reflexivity] |
    solve [destruct (Z.ltb (signed32 a) (signed32 b)); reflexivity] |
    solve [destruct (Z.leb (signed32 a) (signed32 b)); reflexivity]].
Qed.

(** Each binary translation returns exactly the independently specified While value. *)
Theorem bin_bridge (o : binop) (a b : Z) :
  is_word 32%positive a -> is_word 32%positive b ->
  Bits.eval (env2 a b) (bin_bits o) = Some (32%positive, eval_bin o a b).
Proof.
  intros Ha Hb; destruct o; cbn [bin_bits].
  - rewrite (eval_binary a b bvadd wadd eq_refl eq_refl).
    unfold wadd; rewrite (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_binary a b bvsub wsub eq_refl eq_refl).
    unfold wsub; rewrite (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_binary a b bvmul wmul eq_refl eq_refl).
    unfold wmul; rewrite (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_binary a b bvand wand eq_refl eq_refl).
    unfold wand; rewrite !wrap_wrap, (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_binary a b bvor wor eq_refl eq_refl).
    unfold wor; rewrite !wrap_wrap, (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_binary a b bvxor wxor eq_refl eq_refl).
    unfold wxor; rewrite !wrap_wrap, (wrap_id _ _ Ha), (wrap_id _ _ Hb); reflexivity.
  - rewrite (eval_shift a b bvshl wshl eq_refl Ha Hb).
    unfold wshl; rewrite shift_small, (wrap_id _ _ Ha).
    rewrite (wrap_id _ _ (shift_amount_word b)).
    unfold eval_bin, wrap32; rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
    reflexivity.
  - rewrite (eval_shift a b bvlshr wlshr eq_refl Ha Hb).
    unfold wlshr; rewrite shift_small, (wrap_id _ _ Ha).
    rewrite (wrap_id _ _ (shift_amount_word b)).
    unfold eval_bin; rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
    reflexivity.
  - rewrite (eval_shift a b bvashr washr eq_refl Ha Hb).
    unfold washr; rewrite shift_small, (signed32_agrees a Ha).
    rewrite (wrap_id _ _ (shift_amount_word b)).
    unfold eval_bin, wrap32; rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
    reflexivity.
  - exact (comparison_bridge Eq a b Ha Hb).
  - exact (comparison_bridge Ne a b Ha Hb).
  - exact (comparison_bridge LtU a b Ha Hb).
  - exact (comparison_bridge LeU a b Ha Hb).
  - exact (comparison_bridge LtS a b Ha Hb).
  - exact (comparison_bridge LeS a b Ha Hb).
Qed.

(** Evaluation preserves the 32-bit range, including arbitrary constant payloads. *)
Theorem eval_expr_word (sigma : store) (e : expr) :
  (forall x, is_word 32%positive (sigma x)) ->
  is_word 32%positive (eval_expr sigma e).
Proof.
  intro Hstore; induction e as [w|x|o e IH|o e1 IH1 e2 IH2]; cbn [eval_expr].
  - apply (wrap_is_word 32%positive w).
  - apply Hstore.
  - exact (eval_is_word _ _ _ (un_bridge o _ IH)).
  - exact (eval_is_word _ _ _ (bin_bridge o _ _ IH1 IH2)).
Qed.
