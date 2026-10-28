(** * Bitvector operators

    Operators check operand shapes and widths before evaluating normalized words.
    For example, adding two eight-bit words returns an eight-bit word, while comparing them
    returns a one-bit word. Builds on: BitsWord, BitsFun, BitsTestbit and CollectionsEncoding. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Collections Require Import CollectionsEncoding.
From Gaulois.Bits Require Import BitsWord BitsFun BitsTestbit.
Import List.ListNotations.

Open Scope Z_scope.

(** The operator vocabulary includes arithmetic, comparisons and changes of width. *)
Inductive op : Type :=
  | bvnot
  | bvneg
  | bvclz
  | bvctz
  | bvpopcnt
  | bvadd
  | bvsub
  | bvmul
  | bvudiv
  | bvurem
  | bvsdiv
  | bvsrem
  | bvsmod
  | bvand
  | bvor
  | bvxor
  | bvshl
  | bvlshr
  | bvashr
  | bvrotl
  | bvrotr
  | bveq
  | bvne
  | bvult
  | bvule
  | bvslt
  | bvsle
  | bvite
  | bvzext (extra : positive)
  | bvsext (extra : positive)
  | bvtrunc (target : width)
  | bvextract (hi lo : nat)
  | bvconcat.

(** Unary operators select their width-parametric word function. *)
Definition word_fun1 (o : op) : option (width -> Z -> Z) :=
  match o with
  | bvnot => Some wnot
  | bvneg => Some wneg
  | bvclz => Some wclz
  | bvctz => Some wctz
  | bvpopcnt => Some wpopcnt
  | _ => None
  end.

(** Binary same-width operators select their word function. *)
Definition word_fun2 (o : op) : option (width -> Z -> Z -> Z) :=
  match o with
  | bvadd => Some wadd
  | bvsub => Some wsub
  | bvmul => Some wmul
  | bvudiv => Some wudiv
  | bvurem => Some wurem
  | bvsdiv => Some wsdiv
  | bvsrem => Some wsrem
  | bvsmod => Some wsmod
  | bvand => Some wand
  | bvor => Some wor
  | bvxor => Some wxor
  | bvshl => Some wshl
  | bvlshr => Some wlshr
  | bvashr => Some washr
  | bvrotl => Some wrotl
  | bvrotr => Some wrotr
  | _ => None
  end.

(** Comparisons select the relation on normalized operands. *)
Definition word_cmp (o : op) : option (width -> Z -> Z -> bool) :=
  match o with
  | bveq => Some (fun w x y => wrap w x =? wrap w y)
  | bvne => Some (fun w x y => negb (wrap w x =? wrap w y))
  | bvult => Some wult
  | bvule => Some wule
  | bvslt => Some wslt
  | bvsle => Some wsle
  | _ => None
  end.

(** Arity counts operands independently of their widths. *)
Definition arity (o : op) : nat :=
  match o with
  | bvnot | bvneg | bvclz | bvctz | bvpopcnt
  | bvzext _ | bvsext _ | bvtrunc _ | bvextract _ _ => 1%nat
  | bvite => 3%nat
  | _ => 2%nat
  end.

(** Width checking rejects exactly the malformed operator shapes. *)
Definition result_width (o : op) (ws : list width) : option width :=
  match o, ws with
  | bvite, [c; a; b] => if Pos.eqb c 1 && Pos.eqb a b then Some a else None
  | bvconcat, [a; b] => Some (a + b)%positive
  | bvzext n, [w] | bvsext n, [w] => Some (w + n)%positive
  | bvtrunc t, [w] => if Pos.leb t w then Some t else None
  | bvextract hi lo, [w] =>
    if (Nat.leb lo hi && Nat.ltb hi (Pos.to_nat w))%bool
    then Some (Pos.of_nat (S (hi - lo))) else None
  | (bvnot | bvneg | bvclz | bvctz | bvpopcnt), [w] => Some w
  | (bveq | bvne | bvult | bvule | bvslt | bvsle), [a; b] =>
    if Pos.eqb a b then Some 1%positive else None
  | (bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod
    | bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bvrotl | bvrotr), [a; b] =>
    if Pos.eqb a b then Some a else None
  | _, _ => None
  end.

Definition normalize_word (x : word) : word := (fst x, wrap (fst x) (snd x)).

(* Width checking has already selected the meaningful shapes; the fallback is unreachable
   from a successful operator evaluation. *)
Definition op_value (o : op) (xs : list word) : Z :=
  match o, xs with
  | bvite, [(_, c); (_, x); (_, y)] => if c =? 1 then x else y
  | bvzext _, [(_, x)] => x
  | bvsext _, [(w, x)] => signed w x
  | bvtrunc _, [(_, x)] => x
  | bvextract _ lo, [(_, x)] => x / 2 ^ Z.of_nat lo
  | bvconcat, [(_, x); (w2, y)] => x * modulus w2 + y
  | _, [(w, x)] =>
    match word_fun1 o with Some f => f w x | None => 0 end
  | _, [(w, x); (_, y)] =>
    match word_fun2 o, word_cmp o with
    | Some f, _ => f w x y
    | _, Some f => if f w x y then 1 else 0
    | _, _ => 0
    end
  | _, _ => 0
  end.

(** Evaluation normalizes every operand and returns a word of the checked result width. *)
Definition eval_op (o : op) (xs : list word) : option word :=
  match result_width o (List.map fst xs) with
  | Some rw => Some (rw, wrap rw (op_value o (List.map normalize_word xs)))
  | None => None
  end.

Definition op_code (o : op) : nat * (positive * positive) :=
  match o with
  | bvnot => (0%nat, (1%positive, 1%positive))
  | bvneg => (1%nat, (1%positive, 1%positive))
  | bvclz => (2%nat, (1%positive, 1%positive))
  | bvctz => (3%nat, (1%positive, 1%positive))
  | bvpopcnt => (4%nat, (1%positive, 1%positive))
  | bvadd => (5%nat, (1%positive, 1%positive))
  | bvsub => (6%nat, (1%positive, 1%positive))
  | bvmul => (7%nat, (1%positive, 1%positive))
  | bvudiv => (8%nat, (1%positive, 1%positive))
  | bvurem => (9%nat, (1%positive, 1%positive))
  | bvsdiv => (10%nat, (1%positive, 1%positive))
  | bvsrem => (11%nat, (1%positive, 1%positive))
  | bvsmod => (12%nat, (1%positive, 1%positive))
  | bvand => (13%nat, (1%positive, 1%positive))
  | bvor => (14%nat, (1%positive, 1%positive))
  | bvxor => (15%nat, (1%positive, 1%positive))
  | bvshl => (16%nat, (1%positive, 1%positive))
  | bvlshr => (17%nat, (1%positive, 1%positive))
  | bvashr => (18%nat, (1%positive, 1%positive))
  | bvrotl => (19%nat, (1%positive, 1%positive))
  | bvrotr => (20%nat, (1%positive, 1%positive))
  | bveq => (21%nat, (1%positive, 1%positive))
  | bvne => (22%nat, (1%positive, 1%positive))
  | bvult => (23%nat, (1%positive, 1%positive))
  | bvule => (24%nat, (1%positive, 1%positive))
  | bvslt => (25%nat, (1%positive, 1%positive))
  | bvsle => (26%nat, (1%positive, 1%positive))
  | bvite => (27%nat, (1%positive, 1%positive))
  | bvzext n => (28%nat, (n, 1%positive))
  | bvsext n => (29%nat, (n, 1%positive))
  | bvtrunc t => (30%nat, (t, 1%positive))
  | bvextract hi lo => (31%nat, (Pos.of_succ_nat hi, Pos.of_succ_nat lo))
  | bvconcat => (32%nat, (1%positive, 1%positive))
  end.

Definition decode_op_code (code : nat * (positive * positive)) : op :=
  match code with
  | (0%nat, _) => bvnot
  | (1%nat, _) => bvneg
  | (2%nat, _) => bvclz
  | (3%nat, _) => bvctz
  | (4%nat, _) => bvpopcnt
  | (5%nat, _) => bvadd
  | (6%nat, _) => bvsub
  | (7%nat, _) => bvmul
  | (8%nat, _) => bvudiv
  | (9%nat, _) => bvurem
  | (10%nat, _) => bvsdiv
  | (11%nat, _) => bvsrem
  | (12%nat, _) => bvsmod
  | (13%nat, _) => bvand
  | (14%nat, _) => bvor
  | (15%nat, _) => bvxor
  | (16%nat, _) => bvshl
  | (17%nat, _) => bvlshr
  | (18%nat, _) => bvashr
  | (19%nat, _) => bvrotl
  | (20%nat, _) => bvrotr
  | (21%nat, _) => bveq
  | (22%nat, _) => bvne
  | (23%nat, _) => bvult
  | (24%nat, _) => bvule
  | (25%nat, _) => bvslt
  | (26%nat, _) => bvsle
  | (27%nat, _) => bvite
  | (28%nat, (n, _)) => bvzext n
  | (29%nat, (n, _)) => bvsext n
  | (30%nat, (t, _)) => bvtrunc t
  | (31%nat, (hi, lo)) => bvextract (Nat.pred (Pos.to_nat hi)) (Nat.pred (Pos.to_nat lo))
  | _ => bvconcat
  end.

Lemma decode_op_code_roundtrip : forall o, decode_op_code (op_code o) = o.
Proof.
  intros o. destruct o; cbn; try reflexivity.
  now rewrite !SuccNat2Pos.id_succ.
Qed.

(** Operators have an injective constructor-and-parameter code. *)
Definition op_encoding : encoding op.
Proof.
  pose (E := pair_encoding nat_encoding (pair_encoding positive_encoding positive_encoding)).
  refine (Encoding op (fun o => encode E (op_code o)) _).
  intros x y Hcode. apply (encode_injective E) in Hcode.
  apply (f_equal decode_op_code) in Hcode. now rewrite !decode_op_code_roundtrip in Hcode.
Defined.

(** Exactly the seven symmetric binary operators are marked commutative. *)
Definition commutative (o : op) : bool :=
  match o with
  | bvadd | bvmul | bvand | bvor | bvxor | bveq | bvne => true
  | _ => false
  end.

(** Evaluation fails exactly when width checking fails. *)
Theorem eval_op_total : forall o xs,
  eval_op o xs = None <-> result_width o (List.map fst xs) = None.
Proof.
  intros o xs. unfold eval_op. destruct (result_width o (map fst xs));
    split; intro H; try discriminate; reflexivity.
Qed.

(** A successful evaluation returns the width chosen by width checking. *)
Theorem eval_op_width : forall o xs r, eval_op o xs = Some r ->
  result_width o (List.map fst xs) = Some (fst r).
Proof.
  intros o xs r. unfold eval_op. destruct (result_width o (map fst xs)) eqn:Hwidth;
    intro Hresult; [inversion Hresult; reflexivity|discriminate].
Qed.

Lemma result_width_arity : forall o ws w,
  result_width o ws = Some w -> length ws = arity o.
Proof.
  intros o ws w. destruct o; destruct ws as [|a [|b [|c [|d rest]]]];
    cbn; try discriminate; intros H;
    repeat match type of H with
    | (if ?b then _ else _) = _ => destruct b; try discriminate
    end; reflexivity.
Qed.

(** A successful evaluation has the required operand count. *)
Theorem eval_op_arity : forall o xs r, eval_op o xs = Some r -> length xs = arity o.
Proof.
  intros o xs r Hresult. apply eval_op_width in Hresult.
  apply result_width_arity in Hresult. now rewrite length_map in Hresult.
Qed.

(** Every successful result is an unsigned word. *)
Theorem eval_op_is_word : forall o xs r,
  eval_op o xs = Some r -> is_word (fst r) (snd r).
Proof.
  intros o xs r. unfold eval_op. destruct (result_width o (map fst xs));
    intro Hresult; [inversion Hresult; apply wrap_is_word|discriminate].
Qed.

Lemma normalize_word_idempotent : forall x, normalize_word (normalize_word x) = normalize_word x.
Proof.
  intros [w x]. unfold normalize_word. cbn. now rewrite wrap_wrap.
Qed.

(** Pre-normalizing operands leaves evaluation unchanged. *)
Theorem eval_op_normalised : forall o xs,
  eval_op o xs = eval_op o (List.map (fun x => (fst x, wrap (fst x) (snd x))) xs).
Proof.
  intros o xs. change (eval_op o xs = eval_op o (map normalize_word xs)).
  unfold eval_op. rewrite !map_map.
  assert (Hwidths : map (fun x => fst (normalize_word x)) xs = map fst xs).
  { apply map_ext. intros [w x]. reflexivity. }
  rewrite Hwidths. f_equal.
  assert (Hvalues : map (fun x => normalize_word (normalize_word x)) xs =
    map normalize_word xs).
  { apply map_ext. apply normalize_word_idempotent. }
  now rewrite Hvalues.
Qed.

Lemma word_fun1_is_word : forall o f w x,
  word_fun1 o = Some f -> is_word w (f w x).
Proof.
  intros o f w x Hf. destruct o; cbn [word_fun1] in Hf; try discriminate;
    injection Hf as <-;
    first [apply wnot_is_word|apply wrap_is_word|apply wclz_is_word|
      apply wctz_is_word|apply wpopcnt_is_word].
Qed.

Lemma word_fun2_is_word : forall o f w x y,
  word_fun2 o = Some f -> is_word w (f w x y).
Proof.
  intros o f w x y Hf. destruct o; cbn [word_fun2] in Hf; try discriminate;
    injection Hf as <-;
    first [apply wrap_is_word|apply wudiv_is_word|apply wurem_is_word|
      apply wsdiv_is_word|apply wsrem_is_word|apply wsmod_is_word|
      apply wand_is_word|apply wor_is_word|apply wxor_is_word|apply wshl_is_word|
      apply wlshr_is_word|apply washr_is_word|
      unfold wrotr, wrotl; apply wrap_is_word|unfold wrotl; apply wrap_is_word].
Qed.

Lemma word_fun1_normalised : forall o f w x,
  word_fun1 o = Some f -> f w (wrap w x) = f w x.
Proof.
  intros o f w x Hf. destruct o; cbn [word_fun1] in Hf; try discriminate;
    injection Hf as <-; unfold wnot, wneg, wclz, wctz, wpopcnt;
    now rewrite ?wrap_wrap, ?wrap_opp.
Qed.

Lemma word_fun2_normalised : forall o f w x y,
  word_fun2 o = Some f -> f w (wrap w x) (wrap w y) = f w x y.
Proof.
  intros o f w x y Hf. destruct o; cbn [word_fun2] in Hf; try discriminate;
    injection Hf as <-;
    unfold wadd, wsub, wmul, wsdiv, wsrem, wsmod, wudiv, wurem, wneg,
      wand, wor, wxor, wshl, wlshr, washr, wrotr, wrotl, msb, signed;
    repeat rewrite wrap_wrap;
    try rewrite <- wrap_add; try rewrite <- wrap_sub; try rewrite <- wrap_mul;
    repeat rewrite wrap_opp; try reflexivity.
  unfold wadd, wrap. repeat rewrite Z.add_mod_idemp_r by apply modulus_nonzero.
  reflexivity.
Qed.

Lemma word_cmp_normalised : forall o f w x y,
  word_cmp o = Some f -> f w (wrap w x) (wrap w y) = f w x y.
Proof.
  intros o f w x y Hf. destruct o; cbn [word_cmp] in Hf; try discriminate;
    injection Hf as <-; unfold wult, wule, wslt, wsle, signed;
    now rewrite !wrap_wrap.
Qed.

(** Unary dispatch agrees with its public word function. *)
Theorem eval_op_fun1 : forall o w z f,
  word_fun1 o = Some f -> eval_op o [(w, z)] = Some (w, f w z).
Proof.
  intros o w z f Hf.
  pose proof (word_fun1_normalised o f w z Hf) as Hnorm.
  pose proof (word_fun1_is_word o f w z Hf) as Hrange.
  destruct o; cbn [word_fun1] in Hf; try discriminate;
    injection Hf as <-;
    cbn [eval_op result_width op_value normalize_word word_fun1 map fst snd];
    rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Binary dispatch agrees with its public word function. *)
Theorem eval_op_fun2 : forall o w x y f, word_fun2 o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (w, f w x y).
Proof.
  intros o w x y f Hf.
  pose proof (word_fun2_normalised o f w x y Hf) as Hnorm.
  pose proof (word_fun2_is_word o f w x y Hf) as Hrange.
  destruct o; cbn [word_fun2] in Hf; try discriminate;
    injection Hf as <-;
    unfold eval_op; cbn [result_width op_value normalize_word word_fun2 map fst snd];
    rewrite ?Pos.eqb_refl; cbn [word_cmp];
    rewrite Hnorm, wrap_id by exact Hrange; reflexivity.
Qed.

(** Comparison dispatch represents false and true by the one-bit words zero and one. *)
Theorem eval_op_cmp : forall o w x y f, word_cmp o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (1%positive, if f w x y then 1 else 0).
Proof.
  intros o w x y f Hf.
  pose proof (word_cmp_normalised o f w x y Hf) as Hnorm.
  destruct o; cbn [word_cmp] in Hf; try discriminate;
    injection Hf as <-;
    unfold eval_op;
    cbn [result_width op_value normalize_word word_cmp word_fun2 map fst snd];
    rewrite ?Pos.eqb_refl; cbn; rewrite ?Hnorm;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    end; reflexivity.
Qed.

(** Conditional selection reads its one-bit condition after wrapping. *)
Theorem eval_op_ite : forall w x y c,
  eval_op bvite [(1%positive, c); (w, x); (w, y)] =
    Some (w, if wrap 1%positive c =? 1 then wrap w x else wrap w y).
Proof.
  intros w x y c. unfold eval_op.
  cbn [result_width normalize_word op_value map fst snd].
  rewrite ?Pos.eqb_refl. cbn.
  destruct (wrap 1%positive c =? 1); now rewrite wrap_wrap.
Qed.

(** The marked operators evaluate symmetrically on every pair of dynamic words. *)
Theorem commutative_sound : forall o, commutative o = true -> forall a b : word,
  eval_op o [a; b] = eval_op o [b; a].
Proof.
  intros o Hcomm [w x] [w2 y]. destruct o; cbn [commutative] in Hcomm; try discriminate;
    unfold eval_op; cbn [result_width map fst snd];
    rewrite (Pos.eqb_sym w2 w);
    destruct (Pos.eqb w w2) eqn:Hwidth; try reflexivity;
    apply Pos.eqb_eq in Hwidth; subst w2;
    cbn [op_value normalize_word word_fun1 word_fun2 word_cmp map fst snd];
    repeat rewrite wrap_wrap;
    first [now rewrite wadd_comm|now rewrite wmul_comm|now rewrite wand_comm|
      now rewrite wor_comm|now rewrite wxor_comm|now rewrite (Z.eqb_sym (wrap w y))].
Qed.
