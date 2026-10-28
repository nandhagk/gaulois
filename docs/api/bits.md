# Gaulois.Bits

Bits gives n-bit machine words as plain integers: a word of width `w` is a `Z` in `[0, 2^w)`, and
every operator follows the SMT-LIB QF_BV theory, so every operator is total. There are no traps
here; division by zero has a defined answer. An expression language `expr` with an evaluator `eval`
lets other packages state one soundness theorem per operator and then reuse it for every client.
For example:

```coq
(* 8-bit addition wraps; unsigned division by zero is all ones; remainder by zero is the dividend *)
(* eval_op bvadd  [(8, 200); (8, 100)] = Some (8, 44)  *)
(* eval_op bvudiv [(8, 7); (8, 0)]     = Some (8, 255) *)
(* eval_op bvurem [(8, 7); (8, 0)]     = Some (8, 7)   *)
```

Conventions of this document. Statements sit in `Section`s whose `Context` and `Variables` lines
declare what they mention. Operators normalise: every operand `(w, z)` is read as `(w, wrap w z)`,
so results are always words of the stated width, with no well-formedness premise on inputs. Where a
lemma relates a result to unwrapped arithmetic, it assumes `is_word`. Stdlib imports (`ZArith`,
`List`, `Bool`) are implicit. `Open Scope Z_scope` applies throughout; natural-number arithmetic
uses `%nat` where needed.

`encoding` is the shared record from `Gaulois.Collections.CollectionsEncoding`; Bits depends on
`Gaulois.Collections` for `op_encoding`.

## Files

| File | Contents | Card |
|---|---|---|
| `BitsWord.v` | `width`, `modulus`, `wrap`, `is_word`, `word`, `half`, `signed` | BIT-1 |
| `BitsFun.v` | the total word functions `wadd`, `wudiv`, `wsdiv`, `wshl`, `wclz`, ... | BIT-1 |
| `BitsOp.v` | `op`, `arity`, `result_width`, `eval_op`, `op_encoding`, `commutative` | BIT-1 |
| `BitsExpr.v` | `expr`, `eval`, `eval_args`, `env_of`, `vars` | BIT-1 |
| `BitsBridge.v` | the bridge equations `bridge_op` and `bridge_expr` | BIT-1 |
| `BitsTestbit.v` | range and `testbit` lemmas, algebraic identities | BIT-1 |
| `BitsSigned.v` | signed view, comparisons, signed division and remainder | BIT-2 |
| `BitsArith.v` | unsigned division, multiplication, rotations, `clz`, `ctz`, `popcnt` | BIT-2 |
| `BitsExtend.v` | `zext`, `sext`, truncation, `extract`, `concat` | BIT-2 |

## Definitions

### Words (`BitsWord.v`)

```coq
Definition width := positive.
Definition modulus (w : width) : Z := 2 ^ Zpos w.
Definition wrap (w : width) (z : Z) : Z := z mod modulus w.
Definition is_word (w : width) (z : Z) : Prop := 0 <= z < modulus w.
Definition word : Type := (width * Z)%type.
Definition half (w : width) : Z := 2 ^ (Zpos w - 1).
Definition msb (w : width) (z : Z) : bool := Z.testbit (wrap w z) (Zpos w - 1).
Definition signed (w : width) (z : Z) : Z :=            (* two's-complement view of wrap w z *)
  let z' := wrap w z in if z' <? half w then z' else z' - modulus w.
```

### Word functions (`BitsFun.v`)

Each function takes the width first and wraps its operands, written `x'` and `y'` for `wrap w x`
and `wrap w y`. Each result is already a word. Division follows SMT-LIB's total definitions.

```coq
Definition wnot (w : width) (x : Z) : Z := modulus w - 1 - wrap w x.
Definition wneg (w : width) (x : Z) : Z := wrap w (- x).
Definition wadd (w : width) (x y : Z) : Z := wrap w (x + y).
Definition wsub (w : width) (x y : Z) : Z := wrap w (x - y).
Definition wmul (w : width) (x y : Z) : Z := wrap w (x * y).
Definition wand (w : width) (x y : Z) : Z := Z.land (wrap w x) (wrap w y).
Definition wor  (w : width) (x y : Z) : Z := Z.lor (wrap w x) (wrap w y).
Definition wxor (w : width) (x y : Z) : Z := Z.lxor (wrap w x) (wrap w y).
Definition wudiv (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then modulus w - 1 else wrap w x / wrap w y.
Definition wurem (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then wrap w x else wrap w x mod wrap w y.
Definition wsdiv (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wudiv w x y
  | true, false => wneg w (wudiv w (wneg w x) y)
  | false, true => wneg w (wudiv w x (wneg w y))
  | true, true => wudiv w (wneg w x) (wneg w y)
  end.
Definition wsrem (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wurem w x y
  | true, false => wneg w (wurem w (wneg w x) y)
  | false, true => wurem w x (wneg w y)
  | true, true => wneg w (wurem w (wneg w x) (wneg w y))
  end.
Definition wsmod (w : width) (x y : Z) : Z :=
  let ax := if msb w x then wneg w x else wrap w x in
  let ay := if msb w y then wneg w y else wrap w y in
  let u := wurem w ax ay in
  match u =? 0, msb w x, msb w y with
  | true, _, _ => u
  | _, false, false => u
  | _, true, false => wadd w (wneg w u) y
  | _, false, true => wadd w u y
  | _, true, true => wneg w u
  end.
Definition wshl  (w : width) (x y : Z) : Z :=                    (* the amount is the value of y *)
  if Zpos w <=? wrap w y then 0 else wrap w (wrap w x * 2 ^ wrap w y).
Definition wlshr (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then 0 else wrap w x / 2 ^ wrap w y.
Definition washr (w : width) (x y : Z) : Z :=                    (* fills with the sign bit *)
  if Zpos w <=? wrap w y then (if msb w x then modulus w - 1 else 0)
  else wrap w (signed w x / 2 ^ wrap w y).
Definition wrotl (w : width) (x y : Z) : Z :=                    (* the amount is y mod w *)
  let k := wrap w y mod Zpos w in wrap w (wrap w x * 2 ^ k + wrap w x / 2 ^ (Zpos w - k)).
Definition wrotr (w : width) (x y : Z) : Z := wrotl w x (Zpos w - wrap w y mod Zpos w).
Definition wclz (w : width) (x : Z) : Z :=                       (* leading zeros; w for zero *)
  if wrap w x =? 0 then Zpos w else Zpos w - 1 - Z.log2 (wrap w x).
Definition wctz (w : width) (x : Z) : Z :=                       (* trailing zeros; w for zero *)
  if wrap w x =? 0 then Zpos w else Z.log2 (Z.land (wrap w x) (- wrap w x)).
Definition wpopcnt (w : width) (x : Z) : Z := Z.of_nat (List.length
  (List.filter (fun i => Z.testbit (wrap w x) (Z.of_nat i)) (List.seq 0 (Pos.to_nat w)))).
Definition wult (w : width) (x y : Z) : bool := wrap w x <? wrap w y.
Definition wule (w : width) (x y : Z) : bool := wrap w x <=? wrap w y.
Definition wslt (w : width) (x y : Z) : bool := signed w x <? signed w y.
Definition wsle (w : width) (x y : Z) : bool := signed w x <=? signed w y.
```

`wpopcnt` is a specification by counting; an implementation may compute it differently if it
proves equality with this definition.

### Operators (`BitsOp.v`)

```coq
Inductive op : Type :=
  | bvnot | bvneg | bvclz | bvctz | bvpopcnt
  | bvadd | bvsub | bvmul | bvudiv | bvurem | bvsdiv | bvsrem | bvsmod
  | bvand | bvor | bvxor | bvshl | bvlshr | bvashr | bvrotl | bvrotr
  | bveq | bvne | bvult | bvule | bvslt | bvsle
  | bvite
  | bvzext (extra : positive)
  | bvsext (extra : positive)
  | bvtrunc (target : width)
  | bvextract (hi lo : nat)
  | bvconcat.
```

Arity, width rule and value. All operands are read as `x'` for `wrap w x`; `w` is the width of
the first operand.

| Operator | Arity | Operand widths | Result width | Value |
|---|---|---|---|---|
| `bvnot bvneg bvclz bvctz bvpopcnt` | 1 | `w` | `w` | `wnot wneg wclz wctz wpopcnt` |
| `bvadd bvsub bvmul bvudiv bvurem bvsdiv bvsrem bvsmod` | 2 | `w, w` | `w` | `wadd wsub wmul wudiv wurem wsdiv wsrem wsmod` |
| `bvand bvor bvxor bvshl bvlshr bvashr bvrotl bvrotr` | 2 | `w, w` | `w` | `wand wor wxor wshl wlshr washr wrotl wrotr` |
| `bveq bvne bvult bvule bvslt bvsle` | 2 | `w, w` | `1` | `1` if the relation holds, else `0` (`bveq`: `x' = y'`) |
| `bvite` | 3 | `1, w, w` | `w` | the second operand if the first is `1`, else the third |
| `bvzext n`, `bvsext n` | 1 | `w` | `w + n` | `x'`; `wrap (w + n) (signed w x)` |
| `bvtrunc t` | 1 | `w`, with `t <= w` | `t` | `wrap t x'` |
| `bvextract hi lo` | 1 | `w`, with `lo <= hi < w` | `hi - lo + 1` | `wrap (hi - lo + 1) (x' / 2 ^ lo)` |
| `bvconcat` | 2 | `w1, w2` | `w1 + w2` | `x' * 2 ^ w2 + y'` (the first operand is the high part) |

```coq
Definition arity (o : op) : nat.
Definition result_width (o : op) (ws : list width) : option width.
(* the Result width column; None exactly on an arity or width mismatch *)
Definition eval_op (o : op) (xs : list word) : option word.
(* match result_width o (map fst xs) with Some rw => Some (rw, value) | None => None end,
   with the value column; operands are wrapped to their own widths first *)

(* The word functions that eval_op applies, for the same-width operators. *)
Definition word_fun1 (o : op) : option (width -> Z -> Z).            (* bvnot bvneg bvclz bvctz bvpopcnt *)
Definition word_fun2 (o : op) : option (width -> Z -> Z -> Z).   (* 16 binary same-width operators *)
Definition word_cmp (o : op) : option (width -> Z -> Z -> bool).     (* bveq bvne bvult bvule bvslt bvsle *)

Definition op_encoding : encoding op.            (* injective; used by symbolic keys *)
Definition commutative (o : op) : bool.          (* true for bvadd bvmul bvand bvor bvxor bveq bvne *)
```

### Expressions (`BitsExpr.v`)

```coq
Module Bits.
Inductive expr : Type :=
  | Var (i : nat)
  | Const (w : width) (z : Z)
  | App (o : op) (args : list expr).
Definition eval_args (env : nat -> word) (es : list expr) : option (list word).
(* the values of es in order; None as soon as one is None *)
Fixpoint eval (env : nat -> word) (e : expr) : option word.
(* Var i -> the wrapped env i; Const w z -> (w, wrap w z); App o args -> eval_op o on eval_args.
   Defined by an inner fix over args; a plain List.map of eval is rejected by the guard checker. *)
Definition env_of (xs : list word) : nat -> word := fun i => List.nth i xs (1%positive, 0).
Definition vars (n : nat) : list expr := List.map Var (List.seq 0 n).
End Bits.
Import Bits.
```

### The bridge (`BitsBridge.v`)

A client has its own operators, values `V` and evaluation `client_eval : O -> list V -> option V`,
with a map `to_bits : V -> word` into `Bits` words. It proves, once per operator, an equation: if
the client operator evaluates to `r` on `xs`, then the `Bits` expression for that operator gives
`to_bits r` on `map to_bits xs`. Traps and undefined results stay on the client side: where
`client_eval` is `None`, the equation says nothing. For example, a 32-bit `Shl` that reduces its
amount modulo 32 maps to `App bvshl [Var 0; App bvand [Var 1; Const 32 31]]`; the equation holds
because the masked amount is below 32. A 32-bit `Div` that traps on a zero divisor maps to
`App bvudiv [Var 0; Var 1]`; its equation is only required where the divisor is non-zero. Each
domain, proved sound once for every `Bits` operator, is then sound for every client operator.

```coq
Definition bridge_op {O V} (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (bridge : O -> op) : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    eval_op (bridge o) (List.map to_bits xs) = Some (to_bits r).
Definition bridge_expr {O V} (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (bridge : O -> expr) : Prop :=
  forall o xs r, client_eval o xs = Some r ->
    eval (env_of (List.map to_bits xs)) (bridge o) = Some (to_bits r).
```

## Theorems

### Words and evaluation (BIT-1)

```coq
Section WordLaws.
Context (w w2 : width) (x y z : Z).

(** Wrapping lands in range, fixes words, is idempotent and commutes with ring operations. *)
Theorem wrap_is_word : is_word w (wrap w z).
Theorem wrap_id : is_word w z -> wrap w z = z.
Theorem wrap_wrap : wrap w (wrap w z) = wrap w z.
Theorem wrap_add : wrap w (x + y) = wrap w (wrap w x + wrap w y).
Theorem wrap_mul : wrap w (x * y) = wrap w (wrap w x * wrap w y).
Theorem wrap_narrow : (w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z.
(* Proof idea: Z.mod_mod, Z.add_mod, Z.mul_mod; narrowing divides the modulus. Card: BIT-1. *)
End WordLaws.

Section EvalLaws.
Context (o : op) (xs : list word) (r : word) (env : nat -> word) (e : expr) (args : list expr)
  (i : nat) (w : width) (x y z c : Z).

(** The operator rules: None only on arity or width mismatch; results are words of the rule's width. *)
Theorem eval_op_total : eval_op o xs = None <-> result_width o (List.map fst xs) = None.
Theorem eval_op_width : eval_op o xs = Some r -> result_width o (List.map fst xs) = Some (fst r).
Theorem eval_op_arity : eval_op o xs = Some r -> List.length xs = arity o.
Theorem eval_op_is_word : eval_op o xs = Some r -> is_word (fst r) (snd r).
Theorem eval_op_normalised :
  eval_op o xs = eval_op o (List.map (fun x => (fst x, wrap (fst x) (snd x))) xs).
(* Proof idea: case analysis on o against the table; wrap_wrap. Card: BIT-1. *)

(** The operator rules agree with the word functions. *)
Theorem eval_op_fun1 : forall f, word_fun1 o = Some f -> eval_op o [(w, z)] = Some (w, f w z).
Theorem eval_op_fun2 : forall f, word_fun2 o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (w, f w x y).
Theorem eval_op_cmp : forall f, word_cmp o = Some f ->
  eval_op o [(w, x); (w, y)] = Some (1%positive, if f w x y then 1 else 0).
Theorem eval_op_ite :
  eval_op bvite [(1%positive, c); (w, x); (w, y)] =
    Some (w, if wrap 1%positive c =? 1 then wrap w x else wrap w y).
(* Proof idea: unfold eval_op and result_width at the given shapes. Card: BIT-1. *)

(** The evaluator, by cases on the expression. *)
Theorem eval_var : eval env (Var i) = Some (fst (env i), wrap (fst (env i)) (snd (env i))).
Theorem eval_const : eval env (Const w z) = Some (w, wrap w z).
Theorem eval_app : eval env (App o args) =
  match eval_args env args with Some xs => eval_op o xs | None => None end.
Theorem eval_args_nil : eval_args env nil = Some nil.
Theorem eval_args_cons : eval_args env (e :: args) =
  match eval env e, eval_args env args with Some x, Some xs => Some (x :: xs) | _, _ => None end.
Theorem eval_is_word : eval env e = Some r -> is_word (fst r) (snd r).
(* Proof idea: the equations hold by computation of the nested fixpoint; eval_is_word is
   induction on e with eval_op_is_word and wrap_is_word. Card: BIT-1. *)

(** Commutative operators give the same result in either order. *)
Theorem commutative_sound : commutative o = true -> forall a b : word,
  eval_op o [a; b] = eval_op o [b; a].
(* Proof idea: the seven operators; wadd, wmul, wand, wor, wxor and the equalities commute. Card: BIT-1. *)
End EvalLaws.

Section BridgeLaws.
Context {O V : Type} (client_eval : O -> list V -> option V) (to_bits : V -> word)
  (bridge : O -> op).

(** An operator-level bridge is an expression-level bridge through the variables 0, 1, ... *)
Theorem bridge_op_expr : (forall v, is_word (fst (to_bits v)) (snd (to_bits v))) ->
  bridge_op client_eval to_bits bridge ->
  bridge_expr client_eval to_bits (fun o => App (bridge o) (vars (arity (bridge o)))).
(* Proof idea: eval_args on vars n with env_of xs returns xs when to_bits yields words of the
   right length (eval_op_arity gives the length). Card: BIT-1. *)
End BridgeLaws.
```

### Bit-level lemmas and identities (BIT-1)

```coq
Section TestbitLaws.
Context (w : width) (x y : Z) (i : Z).

(** The bits of a wrapped value, and equality of words by bits. *)
Theorem testbit_wrap : 0 <= i -> Z.testbit (wrap w x) i = (i <? Zpos w) && Z.testbit x i.
Theorem word_ext : is_word w x -> is_word w y ->
  (forall j, 0 <= j -> Z.testbit x j = Z.testbit y j) -> x = y.
(* Proof idea: Z.mod_pow2_bits_full; Z.bits_inj. Card: BIT-1. *)

(** The bitwise operators act bit by bit on words. *)
Theorem testbit_wand : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wand w x y) i = Z.testbit x i && Z.testbit y i.
Theorem testbit_wor : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wor w x y) i = Z.testbit x i || Z.testbit y i.
Theorem testbit_wxor : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wxor w x y) i = xorb (Z.testbit x i) (Z.testbit y i).
Theorem testbit_wnot : is_word w x -> 0 <= i ->
  Z.testbit (wnot w x) i = (i <? Zpos w) && negb (Z.testbit x i).
(* Proof idea: Z.land_spec, Z.lor_spec, Z.lxor_spec; wnot is Z.lnot below w. Card: BIT-1. *)

(** Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift. *)
Theorem testbit_wshl : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wshl w x y) i = (i <? Zpos w) && (y <=? i) && Z.testbit x (i - y).
Theorem testbit_wlshr : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (wlshr w x y) i = (i <? Zpos w) && Z.testbit x (i + y).
Theorem testbit_washr : is_word w x -> is_word w y -> 0 <= i ->
  Z.testbit (washr w x y) i = (i <? Zpos w) && Z.testbit x (Z.min (i + y) (Zpos w - 1)).
Theorem wshl_big : is_word w y -> Zpos w <= y -> wshl w x y = 0 /\ wlshr w x y = 0.
Theorem washr_big : is_word w y -> Zpos w <= y ->
  washr w x y = if msb w x then modulus w - 1 else 0.
(* Proof idea: Z.shiftl_spec and Z.shiftr_spec; the amount test splits the two regimes. Card: BIT-1. *)
End TestbitLaws.

Section AlgebraLaws.
Context (w : width) (x y z : Z).

(** Bitwise identities. *)
Theorem wand_comm : wand w x y = wand w y x.
Theorem wand_assoc : wand w x (wand w y z) = wand w (wand w x y) z.
Theorem wor_comm : wor w x y = wor w y x.
Theorem wor_assoc : wor w x (wor w y z) = wor w (wor w x y) z.
Theorem wxor_comm : wxor w x y = wxor w y x.
Theorem wxor_assoc : wxor w x (wxor w y z) = wxor w (wxor w x y) z.
Theorem wxor_self : wxor w x x = 0.
Theorem wand_idem : is_word w x -> wand w x x = x.
Theorem wnot_involutive : is_word w x -> wnot w (wnot w x) = x.
Theorem wnot_wand : wnot w (wand w x y) = wor w (wnot w x) (wnot w y).
Theorem wnot_wor : wnot w (wor w x y) = wand w (wnot w x) (wnot w y).
Theorem wand_wnot : wand w x (wnot w x) = 0.
(* Proof idea: word_ext with the testbit laws and Boolean identities. Card: BIT-1. *)

(** Modular arithmetic identities. *)
Theorem wadd_comm : wadd w x y = wadd w y x.
Theorem wadd_assoc : wadd w x (wadd w y z) = wadd w (wadd w x y) z.
Theorem wadd_0_r : is_word w x -> wadd w x 0 = x.
Theorem wneg_wnot : wneg w x = wadd w (wnot w x) 1.
Theorem wadd_wneg : wadd w x (wneg w x) = 0.
Theorem wsub_wneg : wsub w x y = wadd w x (wneg w y).
Theorem wmul_comm : wmul w x y = wmul w y x.
Theorem wmul_assoc : wmul w x (wmul w y z) = wmul w (wmul w x y) z.
Theorem wmul_1_r : is_word w x -> wmul w x 1 = x.
Theorem wmul_wadd_distr : wmul w x (wadd w y z) = wadd w (wmul w x y) (wmul w x z).
Theorem wshl_0 : is_word w x -> wshl w x 0 = x.
(* Proof idea: wrap_add and wrap_mul, then ring over Z. Card: BIT-1. *)
End AlgebraLaws.
```

### Signed views and division (BIT-2)

```coq
Section SignedLaws.
Context (w : width) (x y z : Z).

(** The signed view is the two's-complement value, and wrapping inverts it. *)
Theorem signed_range : - half w <= signed w x < half w.
Theorem signed_id : - half w <= z < half w -> signed w z = z.
Theorem wrap_signed : wrap w (signed w x) = wrap w x.
Theorem signed_wrap : signed w (wrap w x) = signed w x.
Theorem signed_inj : signed w x = signed w y -> wrap w x = wrap w y.
Theorem signed_neg_iff_msb : signed w x < 0 <-> msb w x = true.
(* Proof idea: case on wrap w x < half w; Z.mod_small and Z.mod_add. Card: BIT-2. *)

(** Addition and comparison through the signed view. *)
Theorem wadd_signed : wadd w x y = wrap w (signed w x + signed w y).
Theorem wsub_signed : wsub w x y = wrap w (signed w x - signed w y).
Theorem wslt_bias : wslt w x y = wult w (wxor w x (half w)) (wxor w y (half w)).
Theorem wslt_wult : msb w x = msb w y -> wslt w x y = wult w x y.
(* Proof idea: wrap_signed with wrap_add; flipping the sign bit biases signed order to unsigned. Card: BIT-2. *)

(** Signed division and remainders equal the mathematical ones on the signed views, with
    SMT-LIB's totality: remainder and modulus by zero give the dividend. *)
Theorem wsdiv_signed : signed w y <> 0 ->
  wsdiv w x y = wrap w (Z.quot (signed w x) (signed w y)).
Theorem wsrem_signed : wsrem w x y = wrap w (Z.rem (signed w x) (signed w y)).
Theorem wsmod_signed : wsmod w x y = wrap w (Z.modulo (signed w x) (signed w y)).
Theorem wsdiv_zero : wsdiv w x 0 = if msb w x then 1 else modulus w - 1.
Theorem wsdiv_wsrem_euclid : wadd w (wmul w y (wsdiv w x y)) (wsrem w x y) = wrap w x.
Theorem wsmod_sign : (0 < signed w y -> 0 <= signed w (wsmod w x y) < signed w y) /\
  (signed w y < 0 -> signed w y < signed w (wsmod w x y) <= 0).
(* Proof idea: the four sign cases of the SMT-LIB definitions reduce to wudiv and wurem on absolute
   values; Z.quot_opp, Z.rem_opp and Z.mod_opp relate them to the truncating and flooring
   operations. Card: BIT-2. *)
End SignedLaws.
```

### Unsigned arithmetic, rotations, counts (BIT-2)

```coq
Section ArithLaws.
Context (w : width) (x y : Z) (i k : Z).

(** Unsigned division and remainder, and SMT-LIB's totality at zero. *)
Theorem wudiv_zero : wudiv w x 0 = modulus w - 1.
Theorem wurem_zero : wurem w x 0 = wrap w x.
Theorem wudiv_spec : is_word w x -> is_word w y -> y <> 0 -> wudiv w x y = x / y.
Theorem wurem_spec : is_word w x -> is_word w y -> y <> 0 -> wurem w x y = x mod y.
Theorem wurem_lt : is_word w x -> is_word w y -> y <> 0 -> wurem w x y < y.
Theorem wudiv_wurem_euclid : wadd w (wmul w y (wudiv w x y)) (wurem w x y) = wrap w x.
(* Proof idea: Z.div_mod; the zero case by computation (all ones times zero is zero). Card: BIT-2. *)

(** Multiplication and powers of two. *)
Theorem wmul_signed : wmul w x y = wrap w (signed w x * signed w y).
Theorem wmul_wshl : is_word w x -> 0 <= k < Zpos w -> wmul w x (2 ^ k) = wshl w x k.
Theorem wudiv_wlshr : is_word w x -> 0 <= k < Zpos w -> wudiv w x (2 ^ k) = wlshr w x k.
Theorem wurem_mask : is_word w x -> 0 <= k < Zpos w -> wurem w x (2 ^ k) = wand w x (2 ^ k - 1).
(* Proof idea: wrap_signed; Z.shiftl_mul_pow2; Z.shiftr_div_pow2; Z.land_ones. Card: BIT-2. *)

(** Rotations move bits cyclically, by the amount modulo the width. *)
Theorem testbit_wrotl : 0 <= i < Zpos w ->
  Z.testbit (wrotl w x y) i = Z.testbit (wrap w x) ((i - wrap w y) mod Zpos w).
Theorem wrotl_mod : wrotl w x y = wrotl w x (wrap w y mod Zpos w).
Theorem wrotr_wrotl : wrotr w (wrotl w x y) y = wrap w x.
(* Proof idea: word_ext with testbit_wrotl; the amount reduces modulo w. Card: BIT-2. *)

(** Leading zeros, trailing zeros and population count; all three give w or 0..w on zero. *)
Theorem wclz_zero : wclz w 0 = Zpos w.
Theorem wctz_zero : wctz w 0 = Zpos w.
Theorem wclz_spec : is_word w x -> x <> 0 -> wclz w x = Zpos w - 1 - Z.log2 x.
Theorem wclz_range : 0 <= wclz w x <= Zpos w.
Theorem wctz_spec : is_word w x -> x <> 0 ->
  Z.testbit x (wctz w x) = true /\ forall j, 0 <= j < wctz w x -> Z.testbit x j = false.
Theorem wpopcnt_range : 0 <= wpopcnt w x <= Zpos w.
Theorem wpopcnt_wnot : is_word w x -> wpopcnt w (wnot w x) = Zpos w - wpopcnt w x.
(* Proof idea: Z.log2_spec; Z.land with the negation isolates the lowest set bit; counting
   over List.seq with testbit_wnot. Card: BIT-2. *)
End ArithLaws.
```

### Extension, truncation, concatenation (BIT-2)

```coq
Section ExtendLaws.
Context (env : nat -> word) (w w2 t : width) (n : positive) (x y : Z).

(** Zero extension keeps the value; sign extension keeps the signed view. *)
Theorem zext_value : env 0 = (w, x) ->
  eval env (App (bvzext n) [Var 0]) = Some ((w + n)%positive, wrap w x).
Theorem sext_value : env 0 = (w, x) ->
  eval env (App (bvsext n) [Var 0]) = Some ((w + n)%positive, wrap (w + n)%positive (signed w x)).
Theorem sext_signed : env 0 = (w, x) -> exists z,
  eval env (App (bvsext n) [Var 0]) = Some ((w + n)%positive, z) /\
  signed (w + n)%positive z = signed w x.
(* Proof idea: unfold eval; signed_id with signed_range, then wrap_signed. Card: BIT-2. *)

(** Truncation undoes extension and commutes with addition. *)
Theorem trunc_zext : env 0 = (w, x) ->
  eval env (App (bvtrunc w) [App (bvzext n) [Var 0]]) = Some (w, wrap w x).
Theorem trunc_sext : env 0 = (w, x) ->
  eval env (App (bvtrunc w) [App (bvsext n) [Var 0]]) = Some (w, wrap w x).
Theorem trunc_wadd : env 0 = (w, x) -> env 1 = (w, y) -> (t <= w)%positive ->
  eval env (App (bvtrunc t) [App bvadd [Var 0; Var 1]]) = Some (t, wadd t x y).
(* Proof idea: wrap_narrow and wrap_add. Card: BIT-2. *)

(** Concatenation puts the first operand high; extract and truncation recover the parts. *)
Theorem extract_concat_hi : env 0 = (w, x) -> env 1 = (w2, y) ->
  eval env (App (bvextract (Pos.to_nat (w + w2)%positive - 1)%nat (Pos.to_nat w2))
    [App bvconcat [Var 0; Var 1]])
    = Some (w, wrap w x).
Theorem trunc_concat_lo : env 0 = (w, x) -> env 1 = (w2, y) ->
  eval env (App (bvtrunc w2) [App bvconcat [Var 0; Var 1]]) = Some (w2, wrap w2 y).
(* Proof idea: Z.div_add and Z.mod_add on x' * 2^w2 + y' with y' < 2^w2. Card: BIT-2. *)
End ExtendLaws.
```

## Algorithms and references

- **Semantics.** SMT-LIB 2.6, theory `FixedSizeBitVectors` (Barrett, Fontaine and Tinelli): the
  definitions of `bvudiv`, `bvurem` (total, with `bvudiv x 0` all ones and `bvurem x 0 = x`),
  `bvsdiv`, `bvsrem` and `bvsmod` as case splits on the sign bits over `bvneg`, `bvudiv` and
  `bvurem`; shifts by at least the width give zero, or the sign fill for `bvashr`. The word
  functions above transcribe those definitions.
- **Counts and rotations.** `clz`, `ctz` and `popcnt` as in LLVM's `ctlz`, `cttz` and `ctpop` with
  the zero input defined to give the width; rotations by an amount reduced modulo the width, as in
  `fshl` and `fshr` with equal operands.
- **Identities.** Warren, *Hacker's Delight*, 2nd ed., 2012: two's-complement negation as
  `not x + 1`, the sign-bit bias that turns signed into unsigned order, and powers-of-two
  multiplication, division and remainder as shifts and masks.
- **Representation.** Words as `Z` with `Z.testbit`, `Z.land`, `Z.shiftl` from Stdlib, in the style
  of the bbv library and of Leroy's `Integers`, but with total SMT-LIB division and no trap cases.

## Performance notes

- Every operation is a constant number of `Z` operations on numbers of at most `2w` bits, except
  `wpopcnt` as specified (O(w), a count over `List.seq`) and `testbit`-based lemmas, which are proof
  only. An implementation may replace `wpopcnt` by a divide-and-conquer count if it proves it equal.
- `eval` is linear in the size of the expression and builds each argument list once; the inner
  `fix` makes it structurally recursive with no `List.map` of the evaluator.
- Prepared index: none. `op_encoding` is a table-free injective code from the constructor index
  paired with its parameters. Prove injectivity by a decoder that recovers each operator from its
  code. `commutative` and symbolic keys cost O(1).

## Open questions

1. **Normalising semantics.** `eval_op` wraps its operands instead of returning `None` on a value
  out
   of range, so results are words unconditionally. A strict alternative returns `None` on an
   ill-formed operand and adds `is_word` premises to every theorem; the anchors' comment "None only
   on arity or width mismatch" fits the normalising reading.
2. **Operator set.** `bvugt`, `bvuge`, `bvsgt` and `bvsge` are expressed by swapping operands of
   `bvult`, `bvule`, `bvslt` and `bvsle`; `bvnand`, `bvnor`, `bvxnor`, `bvcomp`, `repeat` and a
   constant
   `rotate` are omitted. Adding them is a card-level change to `op` and the table.
3. **`bvextract` takes `nat` indices** because a bit position can be zero, while `width` is
  `positive`.
4. **`wpopcnt` is a counting specification.** Whether to pin a fast definition is left to BIT-2.
5. **`op_encoding` and `commutative`** are additions to the anchors, made for the symbolic keys in
   Domains (DOM-7).
6. **`bridge_op` versus `bridge_expr`.** The brief's equation uses `eval_op (bridge op)`; the plan's
   uses an expression. Both are given, and `bridge_op_expr` converts one to the other.
7. **`env_of` default.** A missing variable reads as `(1, 0)`; the bridge theorem never reaches it.
