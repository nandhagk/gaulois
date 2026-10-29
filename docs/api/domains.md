# Gaulois.Domains

## Selectable known-bit multiplication (DOM-8)

`DomainsKnownBitsFast.v` adds a selectable `word_domain tnum` using the existing lattice,
concretisation and all existing transfers except multiplication. This is a precision choice:
it has the same soundness interface, but need not return the same abstract fact as DOM-2.
No existing public definition or theorem changes. The multiplication is a width-bounded
shift-and-add algorithm over tnums, processing multiplier bits from least to most significant.
Start at the constant zero tnum. For each bit, leave the accumulator unchanged when the bit is
known zero; add the shifted multiplicand with the DOM-2 tnum addition when it is known one;
and join the unchanged accumulator with that sum when the bit is unknown. Truncate each shift
and addition to the result width. A contradictory input mask returns the tnum bottom. Constants
therefore yield the exact concrete product. Iteration uses binary fuel or a structurally bounded
bit traversal and does not enumerate concrete operands.

```coq
Definition tnum_mul_precise (w : width) (a b : tnum) : tnum.
Definition known_bits_precise_domain : word_domain tnum.
(* Same fields as known_bits_domain except pforward bvmul on two operands of width rw uses
   tnum_mul_precise; all other inputs use pforward known_bits_domain unchanged. *)
Theorem tnum_mul_precise_sound (w : width) (a b : tnum) (x y : Z) :
  is_word w x -> is_word w y -> tnum_gamma w a x -> tnum_gamma w b y ->
  tnum_gamma w (tnum_mul_precise w a b) (wmul w x y).
Theorem known_bits_precise_word_laws : word_laws known_bits_precise_domain tnum_gamma.
Theorem tnum_mul_precise_constants (w : width) (x y : Z) :
  tnum_mul_precise w (pconst known_bits_domain w x) (pconst known_bits_domain w y) =
  pconst known_bits_domain w (wmul w x y).
```

The implementation proves the claims directly for all widths and the repository's total word
semantics. It does not claim an optimal abstract multiplication or equal results to DOM-2.
Card: DOM-8.

Domains provides abstract values for machine words and for memory, all proved sound once. A
`numeric_domain` is a record of a lattice, an abstraction of constants, a forward transfer for
every `Bits` operator and a backward `assume` that refines operands from a known result; one
generic theorem lifts a domain's operator soundness to whole `Bits.expr` evaluation. Instances are
constants, intervals, signs, known bits, wrapping intervals and congruences, reduced products of
them, demanded bits (a backward agreement domain), and the memory domains for addresses,
points-to sets and byte ranges, plus equality partitions and symbolic keys. For example, with known
bits, after `x := y & 0xF0` on 8-bit words the low nibble of `x` is known to be zero:

```coq
(* forward D bvand [top_at D 8; of_const D 8 240]  describes words with bits 0..3 known 0 *)
(* assume D bvult (of_const D 1 1) [x; of_const D 8 10]  refines x to [0, 9] in an interval domain *)
```

Conventions of this document. Statements sit in `Section`s whose `Context` and `Variables` lines
declare what they mention, and a `(* Proof idea ... Card ... *)` line follows each group of
theorems. Order and Bits names are used as in their documents: `lattice`, `leb`, `concretisation`,
`gamma`, `bottom_empty`, `top_full`, `agreement`, `word` (`width * Z`), `eval_op`, `eval`, `wrap`,
`is_word`. The expression names `expr` and `eval` are imported from `Bits`. The `numeric_domain`
field for the full set of one width is `top_at`, because `top` is the
Order record. Stdlib imports (`ZArith`, `List`, `Bool`, `Sorting.Sorted`) are implicit.

## Files

| File | Contents | Card |
|---|---|---|
| `DomainsNumeric.v` | `numeric_domain`, `numeric_laws`, `word_domain`, `word_laws`, `tagged`, `capped`, `capped_domain`, `abs_eval`, `abs_assume`, the generic soundness theorems | DOM-1a |
| `DomainsConst.v` | constants (flat) | DOM-1a |
| `DomainsInterval.v` | intervals over `Z` with infinite bounds, threshold widening, narrowing | DOM-1b |
| `DomainsSign.v` | signs | DOM-1a |
| `DomainsKnownBits.v` | known bits (tnum) | DOM-2 |
| `DomainsKnownBitsFast.v` | selectable tnum multiplication | DOM-8 |
| `DomainsSignedBounds.v` | sign-separated bit and interval reduction | DOM-9 |
| `DomainsSignedBoundsDomain.v` | selectable signed bit-and-bounds domain and queries | DOM-9 |
| `DomainsWrapped.v` | wrapping intervals with a widening rank | DOM-3 |
| `DomainsCongruence.v` | congruences | DOM-4 |
| `DomainsProduct.v` | the reduced-product functor and its three reductions | DOM-4 |
| `DomainsDemanded.v` | masks, `mask_agreement`, `demand` | DOM-5 |
| `DomainsAddress.v` | addresses, `covers`, `disjoint`, `may_overlap` | DOM-6 |
| `DomainsPointsTo.v` | points-to sets | DOM-6 |
| `DomainsByteRange.v` | byte-range sets | DOM-6 |
| `DomainsFootprint.v` | `footprint`, `covered`, `footprint_encoding`, canonical footprint lists, `range_must` and its lattice | DOM-6 |
| `DomainsEquality.v` | equality partitions over `UnionFind` | DOM-7 |
| `DomainsSymbolic.v` | symbolic hash-consed keys over `Table` | DOM-7 |

Prerequisites. DOM-1a needs ORD-1 and BIT-1; DOM-1b needs DOM-1a; DOM-2 and DOM-3 need DOM-1a and
BIT-2; the landed DOM-3 also reuses DOM-1b interval definitions and soundness lemmas. DOM-4 needs
DOM-2, DOM-3 and DOM-1b (`interval_cong_domain`); DOM-5 needs ORD-1 and BIT-2;
DOM-6
needs ORD-2 and DOM-1b (an address holds an `interval`); DOM-7 needs ORD-1, COL-2 and BIT-1.

## Definitions

### The numeric-domain interface (`DomainsNumeric.v`)

An element of `A` describes a set of words (pairs `(w, z)` of a width and a value). `forward` and
`assume` may return anything when `eval_op` would return `None`: there is no concrete result to
approximate. `assume` always returns one entry per input operand, even when evaluation would return
`None`. `meet` is an addition to the brief's field list: guards need it to refine a variable that is
read directly.

```coq
Record numeric_domain (A : Type) : Type := NumericDomain {
  lat : lattice A;
  top_at : width -> A;                       (* every word of that width *)
  of_const : width -> Z -> A;
  forward : op -> list A -> A;
  assume : op -> A -> list A -> list A;      (* assume o r xs: refine xs given that the result is in r *)
  meet : A -> A -> A
}.
Record numeric_laws {A} (D : numeric_domain A) (G : concretisation A word) : Prop := {
  lat_laws : lattice_laws (lat D);
  gamma_laws : concretisation_laws (lat D) G;
  bot_empty : bottom_empty (lat D) G;
  top_at_sound : forall w z, is_word w z -> gamma G (top_at D w) (w, z);
  of_const_sound : forall w z, gamma G (of_const D w z) (w, wrap w z);
  forward_sound : forall o xs ys r, Forall2 (gamma G) xs ys -> eval_op o ys = Some r ->
    gamma G (forward D o xs) r;
  assume_sound : forall o a xs ys r, Forall2 (gamma G) xs ys -> eval_op o ys = Some r ->
    gamma G a r -> Forall2 (gamma G) (assume D o a xs) ys;
  assume_length : forall o a xs, List.length (assume D o a xs) = List.length xs;
  assume_refines : forall o a xs,
    Forall2 (fun x' x => leb (lat D) x' x = true) (assume D o a xs) xs;
  meet_sound : forall a b c, gamma G a c -> gamma G b c -> gamma G (meet D a b) c;
  meet_lower_left : forall a b, leb (lat D) (meet D a b) a = true
}.
(* There is no right lower bound: a meet may over-approximate the intersection by its first argument
   (wrapped intervals), so it is below the first argument only. *)
```

Evaluation over expressions. `abs_eval` and `abs_assume` are structurally recursive with an inner
`fix` over the argument list (a `List.map` of the recursive call is rejected by the guard checker).

```coq
Fixpoint abs_eval {A} (D : numeric_domain A) (env : nat -> A) (e : expr) : A.
(* Var i -> env i; Const w z -> of_const D w z; App o args -> forward D o (the abs_eval of each arg) *)
Fixpoint abs_assume {A} (D : numeric_domain A) (env : nat -> A) (e : expr) (a : A) : nat -> A.
(* the environment refined by the fact that e's value is in a.
   Var i -> env with i set to meet D (env i) a; Const -> env;
   App o args -> let xs' := assume D o a (the abs_eval of each arg) in the arguments are refined
   one after another, each by its entry of xs', each seeing the environment refined so far *)
Definition env_ok (cenv : nat -> word) : Prop := forall i, is_word (fst (cenv i)) (snd (cenv i)).
Definition env_sound {A} (G : concretisation A word) (aenv : nat -> A) (cenv : nat -> word) : Prop :=
  forall i, gamma G (aenv i) (cenv i).
```

### Payload domains and width tags (`DomainsNumeric.v`)

Most instances describe a set of values without saying their width, and need the width to compute
(wrap-around, sign). A `word_domain` supplies width-indexed operations over a payload `P`; the
builder `tagged_domain` adds the width plumbing once and yields a `numeric_domain`.

```coq
Record word_domain (P : Type) : Type := WordDomain {
  plat : width -> lattice P;
  ptop : width -> P;
  pconst : width -> Z -> P;
  pforward : op -> list (width * P) -> width -> P;          (* operands with widths, result width *)
  passume : op -> list (width * P) -> width -> P -> list P;  (* ..., result width, result fact *)
  pmeet : width -> P -> P -> P
}.
Definition payload_sound {P} (G : width -> P -> Z -> Prop) (wp : width * P) (y : word) : Prop :=
  fst wp = fst y /\ is_word (fst y) (snd y) /\ G (fst wp) (snd wp) (snd y).
Record word_laws {P} (D : word_domain P) (G : width -> P -> Z -> Prop) : Prop := {
  plat_laws : forall w, lattice_laws (plat D w);
  pgamma_monotone : forall w a b z, leb (plat D w) a b = true -> G w a z -> G w b z;
  pgamma_bot_empty : forall w z, ~ G w (bot (plat D w)) z;
  ptop_sound : forall w z, is_word w z -> G w (ptop D w) z;
  pconst_sound : forall w z, G w (pconst D w z) (wrap w z);
  pforward_sound : forall o wps ys rw z, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw (pforward D o wps rw) z;
  passume_sound : forall o wps ys rw z q, Forall2 (payload_sound G) wps ys ->
    eval_op o ys = Some (rw, z) -> G rw q z ->
    Forall2 (fun p y => G (fst p) (snd p) (snd y)) (List.combine (List.map fst wps)
      (passume D o wps rw q)) ys;
  passume_refines : forall o wps rw q,
    Forall2 (fun wp p' => leb (plat D (fst wp)) p' (snd wp) = true) wps (passume D o wps rw q);
  pmeet_sound : forall w a b z, G w a z -> G w b z -> G w (pmeet D w a b) z;
  pmeet_lower_left : forall w a b, leb (plat D w) (pmeet D w a b) a = true
}.

Inductive tagged (P : Type) : Type :=
  | TBot
  | TVal (w : width) (p : P)
  | TAny.
Definition tagged_lattice {P} (plat : width -> lattice P) : lattice (tagged P).
(* TBot <= everything; everything <= TAny; TVal w a <= TVal w' b iff w = w' and leb (plat w) a b;
   nothing else. In particular no TVal is <= TBot and TAny <= TVal _ _ is false: an "a <= bot"
   disjunct, in either clause, would break transitivity through TBot (TVal 8 a <= TBot <= TVal 16 b).
   join and widen: TBot neutral, TAny absorbs, equal widths use the payload's join (widen),
   different widths give TAny. narrow (TVal w a) (TVal w b) uses the payload's narrow, else the
   first argument *)
Definition tagged_val {P} (D : word_domain P) (w : width) (p : P) : tagged P :=
  if leb (plat D w) p (bot (plat D w)) then TBot else TVal w p.         (* an empty payload is TBot *)
Definition tagged_domain {P} (D : word_domain P) : numeric_domain (tagged P).
(* top_at w = TVal w (ptop w); of_const w z = TVal w (pconst w z);
   forward o xs: an operand TBot, or TVal _ p with leb p bot -> TBot; all TVal wi pi and
     result_width o [wi] = Some rw -> tagged_val rw (pforward o [(wi, pi)] rw); all TVal with no
     result width -> TBot; otherwise (some TAny) TAny.
   assume o a xs: a is TBot, or TVal _ q with leb q bot -> every operand TBot; a = TVal rw q and
     every x = TVal wi pi with result_width o [wi] = Some rw -> each operand TVal wi pi becomes
     tagged_val wi (its entry of passume), so the result has the length of xs; a = TVal _ _, all
     operands TVal and no matching result width -> every operand TBot; otherwise xs unchanged.
   meet: TBot absorbs, TAny neutral, equal widths tagged_val w (pmeet w p q), different widths TBot.
   So forward, meet and assume return TBot whenever a payload is <= bot *)
Definition tagged_gamma {P} (G : width -> P -> Z -> Prop) : concretisation (tagged P) word.
(* TBot: nothing; TVal w p: (w', z) with w' = w, is_word w z and G w p z; TAny: every word *)
```

Termination needs a bound on ranks, which no single bound gives over all widths. `capped` restricts
the carrier to widths up to a cap, which is a program's real situation:

```coq
Definition width_ok {P} (maxw : width) (t : tagged P) : Prop :=
  match t with TVal w _ => (w <= maxw)%positive | _ => True end.
Definition capped {P} (maxw : width) : Type := { t : tagged P | width_ok maxw t }.
Definition capped_lattice {P} (maxw : width) (plat : width -> lattice P) : lattice (@capped P maxw).
Definition capped_height {P} (D : word_domain P) (maxw : width)
  (laws : forall w, lattice_laws (plat D w))
  (H : forall w, monotone_height (plat D w)) :
  monotone_height (capped_lattice maxw (plat D)).
Definition capped_wrank {P} (D : word_domain P) (maxw : width)
  (W : forall w, bounded_widening_rank (plat D w)) :
  bounded_widening_rank (capped_lattice maxw (plat D)).
(* with M the maximum, over the widths 1..maxw, of the payload bound (resp. wbound):
   capped_height: rank TBot = 0, TVal w p = 1 + the payload's rank, TAny = 2 + M; bound 2 + M;
   capped_wrank: wrank TAny = 0, TVal w p = 1 + the payload's wrank, TBot = 2 + M; wbound 2 + M *)

(* The domain over the capped carrier: the tagged domain with every result clamped. *)
Definition clamp {P} (maxw : width) (t : tagged P) : @capped P maxw.
(* t when width_ok maxw t; a TVal w _ with w > maxw becomes TAny *)
Definition capped_domain {P} (D : word_domain P) (maxw : width) : numeric_domain (@capped P maxw).
(* lat = capped_lattice maxw (plat D). top_at, of_const, forward and meet are those of
   tagged_domain D on the underlying values followed by clamp maxw, so in every operation a
   TVal w _ with w > maxw becomes TAny (top_at w for w > maxw is TAny; a bvzext or bvconcat that
   leaves the cap gives TAny). assume is that of tagged_domain D with each refined operand clamped:
   an operand within the cap refines within the cap, so the clamp changes nothing there *)
Definition capped_gamma {P} (G : width -> P -> Z -> Prop) (maxw : width) :
  concretisation (@capped P maxw) word.                 (* gamma t c = tagged_gamma G (proj1_sig t) c *)
```

### Constants, intervals, signs (DOM-1a: constants and signs; DOM-1b: intervals)

```coq
(* DomainsConst.v (DOM-1a): the payload is flat Z, the width lives in the tag *)
Definition const_domain : word_domain (flat Z).
(* plat _ = flat_lattice Z.eqb; ptop _ = FTop; pconst w z = FVal (wrap w z).
   pforward: all operands FVal -> FVal of the eval_op value (FBot if eval_op is None); some FBot
     -> FBot; otherwise FTop, except the annihilators: bvmul and bvand with a FVal 0 operand give
     FVal 0, bvor with an all-ones operand gives all ones, bvshl bvlshr bvashr bvurem with first
     operand FVal 0 give FVal 0.
   passume: bveq with result FVal 1 and bvne with result FVal 0 give each operand the other's
     constant when known; bvadd bvsub bvxor bvnot bvneg with the result and all but one operand known
     solve the remaining operand; every refinement uses pmeet with the old operand; otherwise
     unchanged.
   pmeet: FBot absorbs, FTop neutral, FVal a with FVal b is FVal a if a = b, else FBot *)
Definition const_gamma (w : width) (p : flat Z) (z : Z) : Prop :=
  match p with FBot => False | FVal c => z = c | FTop => True end.

(* DomainsInterval.v (DOM-1b): intervals of integers with infinite bounds *)
Inductive bound : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.
Inductive interval : Type :=
  | IBot
  | Itv (lo hi : bound).
Definition interval_lattice (thresholds : list Z) : lattice interval.
(* bounds order NegInf < Fin z < PosInf. IBot <= everything; Itv l1 h1 <= Itv l2 h2 iff l2 <= l1
   and h1 <= h2. join: the hull. widen a b: IBot neutral; a bound that moved outward jumps to the
   nearest threshold beyond it, or to the infinity if there is none; a bound that did not move
   stays. narrow (Itv l1 h1) (Itv l2 h2): an infinite bound of the first is replaced by the
   second's, a finite one is kept; narrow IBot _ = IBot; narrow a IBot = a *)
Definition interval_gamma : concretisation interval Z.        (* IBot: nothing; Itv lo hi: lo <= z <= hi *)
Definition interval_wrank (thresholds : list Z) : bounded_widening_rank (interval_lattice thresholds).
(* lower: NegInf 0, Fin z 1 + #{t in thresholds | t < z}, PosInf 1 + length thresholds;
   upper: PosInf 0, Fin z 1 + #{t | z < t}, NegInf 1 + length thresholds;
   wrank (Itv l h) = lower l + upper h; wrank IBot = wbound = 2 * (length thresholds + 1) + 1 *)
Definition interval_pgamma (w : width) (i : interval) (z : Z) : Prop :=
  is_word w z /\ gamma interval_gamma i z.                  (* unsigned view of the word *)
Definition interval_domain (thresholds : list Z) : word_domain interval.
(* plat _ = interval_lattice thresholds; ptop w = Itv (Fin 0) (Fin (modulus w - 1));
   pconst w z = the point wrap w z; pmeet = intersection (IBot if empty). Rules below. *)

(* DomainsSign.v (DOM-1a) *)
Record sign : Type := Sign { neg : bool; zero : bool; pos : bool }.
Definition sign_lattice : lattice sign.      (* field-wise implication; bot all false; join = widen = field-wise orb *)
Definition sign_height : monotone_height sign_lattice.            (* rank = the number of true fields; bound 3 *)
Definition sign_gamma (w : width) (s : sign) (z : Z) : Prop :=
  (signed w z < 0 -> neg s = true) /\ (signed w z = 0 -> zero s = true) /\
  (0 < signed w z -> pos s = true).
Definition sign_domain : word_domain sign.
(* ptop = all true; pconst w z = the sign of signed w z; pmeet = field-wise andb. Rules below. *)
```

Rules of the interval domain (unsigned view; a result that could wrap falls back to `[0, 2^rw -
1]`).
Before applying a rule, meet each operand of width `w` with `ptop w`.
`bvadd bvsub bvmul bvneg`: interval arithmetic, exact when in range. `bvand bvor bvxor bvnot`: from
the
bounds (`min hi` under an and; the next power of two minus one over an or or xor; `2^w - 1 - hi` for
not). Shifts by an amount interval below `w`: shifted bounds when in range. `bvudiv bvurem`: from
the
bounds when the divisor excludes zero, else also all ones (resp. the dividend). Signed operators
other than `bvsrem` and `bvsmod` are exact when every operand lies in one sign half. For `bvsrem`
and `bvsmod`, use sound sign-aware bounds in that case; their result need not be the least interval
hull. For example, 8-bit `[5, 5]` `bvsrem` `[2, 3]` may return `[0, 2]` although the least hull is
`[1, 2]`. The total word semantics, including a zero divisor, remains covered by `word_laws`.
Comparisons: `1` or `0` when decided, else `[0, 1]`.
Extensions, `bvtrunc`, `bvconcat`, `bvite`: bound arithmetic or the join. Counts: `[0, w]`;
rotations:
the whole range. `assume`: a comparison with a known result refines both operands (`bvult` = 1:
`x <= hi_y - 1` and `y >= lo_x + 1`; `bveq` = 1 meets; signed ones when both lie in one half);
`bvadd bvsub bvzext bvtrunc` invert when no wrap is possible; the rest leave operands unchanged.

Rules of the sign domain. Comparisons are decided when the signs decide them. `bvand`: negative only
if both operands are, and not negative if either operand is not. `bvor`: negative if either is.
`bvxor`: negative iff the signs differ. `bvnot`: a negative operand gives `{zero, pos}`, the others
`{neg}`. `bvneg`: negative gives `{neg, pos}` (the minimum maps to itself), positive `{neg}`, zero
`{zero}`. `bvzext`: not negative. `bvsext`: the same sign. `bvite`: the join. Anything else: all
three.

### Known bits (`DomainsKnownBits.v`, DOM-2)

```coq
Record tnum : Type := Tnum { zeros : Z; ones : Z }.     (* a set bit of zeros (ones): that bit is known 0 (1) *)
Definition tnum_lattice (w : width) : lattice tnum.
(* masks are read modulo 2^w. leb a b: everything b knows, a knows (zeros b and ones b are subsets
   of zeros a and ones a); bot = Tnum (2^w - 1) (2^w - 1) (every bit contradictory: no value);
   join: bitwise and of both masks; widen = join; narrow a _ = a *)
Definition tnum_height (w : width) : monotone_height (tnum_lattice w).
(* rank = 2w - popcount zeros - popcount ones over w bits; bound 2w *)
Definition tnum_gamma (w : width) (t : tnum) (z : Z) : Prop :=
  Z.land z (wrap w (zeros t)) = 0 /\ Z.land (wrap w (ones t)) (Z.lnot z) = 0.
Definition known_bits_domain : word_domain tnum.
(* ptop = Tnum 0 0; pconst w c = Tnum (2^w - 1 - c') c' with c' = wrap w c;
   pmeet: bitwise or of both masks *)
```

`pforward` classes. Bitwise operators, `bvite`, extensions, truncation, extract, concat and
constant-amount shifts and rotations: exact, bit by bit. `bvadd bvsub bvneg`: the closed forms of
the
Linux kernel's `tnum_add` and `tnum_sub` (`bvneg` is `tnum_sub` of the constant 0), proved by
induction on
the bit with the carry. `bvmul`: exact when both operands are constants; otherwise the low `tz(x) +
tz(y)`
bits are known 0, where `tz` counts the known-0 low bits, and no other bit is known; there is no
general
multiplication claim. Variable-amount shifts and rotations: the join over the amounts the known bits
allow, using the factored algorithm below. `bvudiv`: the leading zeros of the dividend are kept only
if some bit of the divisor is known 1
(division by zero gives all ones), else Top. `bvurem`: the leading zeros of the dividend are kept.
`bvsdiv bvsmod`: Top. `bvsrem`: Top, except that the sign bit is known 0 when the dividend's sign
bit is
known 0. Counts: the bits above `bitlen w` are zero. Comparisons: decided by the highest known
differing
bit. `passume`: project known result bits back through bitwise operators, shifts, extensions,
truncation
and concatenation; invert `bvadd bvsub` with one known operand; `bveq` = 1 meets; `bvult bvule` use
leading
bits; every refinement is a meet with the old fact.

For a well-formed same-width shift or rotation, let `w` be the positive operand width. Normalize
both masks to `w` bits; if either operand has a contradictory bit, return bottom. Otherwise the
allowed amounts are exactly the `w`-bit words with the amount's known-one bits set, known-zero bits
clear, and all other bits independently selectable. Let `S(k, a)` be the exact constant-amount
transfer for the operator, and `join` the tnum least upper bound. Start with `S(base, a)`, where
`base` is the normalized known-one mask. For each selected unknown amount bit `i`, replace the
accumulator `r` by `join r (S(2^i, r))`. The stages compose shifts by ordinary addition, with
oversized shifts saturating, and rotations by addition modulo `w`. Constant transfers preserve
these joins because every output bit is a copied input bit or a fixed fill bit. Prove this
preservation and the stage invariant; the final fact is the exact join of the constant transfers
over all allowed amounts, hence the best known-bits abstraction of their concrete results. This
claim is specific to these operations, not to every arithmetic transfer.

For shifts, select only unknown bits `i < ceil(log2 w)`. If any unknown higher bit can be set,
also join the oversized result: all zeros for logical shifts, and the dividend sign fill for
arithmetic right shift. The base may itself be oversized; handle that case without constructing
an oversized intermediate integer. For rotations, select every unknown bit below `w`, using
`2^i mod w` as the stage amount; update that residue by doubling modulo `w`. In particular,
non-power-of-two widths cannot discard higher amount bits. The amount is wrapped to `w` bits as
in `eval_op`; rotations reduce it modulo `w`. Widths are positive, so width zero is not a legal
word width. Counts retain the above rule, including the wrapped result of `clz` and `ctz` on zero.
Use binary fuel or a structurally bounded traversal, and prove the oversized and sign-fill cases.

### Wrapping intervals (`DomainsWrapped.v`, DOM-3)

```coq
Inductive wrapped : Type :=
  | WBot
  | WFull
  | WItv (lo hi : Z).
Definition wrapped_size (w : width) (a : wrapped) : Z.      (* the number of words in the arc *)
Definition wrapped_lattice (w : width) : lattice wrapped.
(* WItv lo hi with 0 <= lo, hi < 2^w is the arc lo, lo+1, ..., hi modulo 2^w; it passes through 0
   when lo > hi. An arc of size 2^w is WFull: every operation first normalises (ends read modulo
   2^w, a size-2^w arc becomes WFull). Write off c x = (x - c) mod 2^w. WBot <= everything;
   everything <= WFull; WFull <= only WFull; WItv a b <= WItv c d iff off c a <= off c b <= off c d.
   join a b: WBot is neutral; if leb a b then b; if leb b a then a; otherwise the smaller, by size,
   of the arcs [a.lo, b.hi] and [b.lo, a.hi] that leb-cover both a and b; if neither covers both,
   WFull (after Navas et al.). widen a b: a if leb b a, else join (double a) b, where double
   [lo, hi] is [lo - s, hi + s] with s = size (so of size 3s), or WFull when 3s >= 2^w, and
   double WBot = WBot. narrow a b: b if a is WFull, else a *)
Definition wrapped_wrank (w : width) : bounded_widening_rank (wrapped_lattice w).
(* wrank WBot = wbound = w + 2; WFull 0; WItv lo hi = w + 1 - Z.log2 (wrapped_size w (WItv lo hi)) *)
Definition wrapped_gamma (w : width) (a : wrapped) (z : Z) : Prop :=
  match a with
  | WBot => False
  | WFull => is_word w z
  | WItv lo hi => is_word w z /\ (z - lo) mod modulus w <= (hi - lo) mod modulus w
  end.
Definition wrapped_domain : word_domain wrapped.
(* ptop w = WFull; pconst w z = WItv z' z' with z' = wrap w z. pmeet w a b: WBot absorbs and WFull is
   neutral; for two arcs, WBot when they share no word, the common arc when the intersection is one
   arc, and a otherwise (the intersection is two arcs, a over-approximates it, and a is below no
   arc other than itself, so only the left lower bound pmeet_lower_left holds) *)
```

Rules, after Navas, Schachte, Søndergaard and Stuckey (APLAS 2012): `bvadd bvsub`: `[a,b] + [c,d] =
[a + c, b + d]` unless the sizes add to more than the circle, then `WFull`; `bvneg`: `[-b, -a]`;
`bvmul`:
cut each arc at the north pole (`0 | 2^w - 1`) and the south pole, multiply the unsigned and signed
pieces, keep the smaller arc; divisions and `bvand bvor bvxor`: through the bounds of the pieces;
`bvzext bvsext bvtrunc`: the same arc when it does not cross the relevant pole or fits, else `WFull`
or the joined pieces; comparisons: decided when the arcs are separated; `bvite`: the join; the rest
`WFull`. `assume`: refine by the arcs below or above the other operand for `bvult bvule bvslt
bvsle`,
meet for `bveq`, invert `bvadd bvsub`, project `bvzext bvsext bvtrunc`.

### Congruences (`DomainsCongruence.v`, DOM-4)

```coq
Inductive cong : Type :=
  | CBot
  | Cong (m r : Z).                         (* z = r modulo m; m = 0 means z = r exactly *)
Definition cong_norm (w : width) (c : cong) : cong.
(* reduce r modulo m; a modulus of at least 2^w denotes at most one word: an exact value, or CBot *)
Definition cong_lattice (w : width) : lattice cong.
(* every comparison, join, widen and rank first applies cong_norm w. CBot <= everything;
   Cong m1 r1 <= Cong m2 r2 iff m1 mod m2 = 0 and (r1 - r2) mod m2 = 0 (Rocq's mod by 0 is the
   dividend, so a zero modulus means "exactly"); join: Cong (Z.gcd (Z.gcd m1 m2) (r1 - r2)) r1 with
   CBot neutral, then normalised; widen = join; narrow a _ = a *)
Definition cong_height (w : width) : monotone_height (cong_lattice w).
(* rank CBot = 0; an exact value 1; on a normalised Cong m _ with 1 <= m < 2^w the rank is
   2 + w - Z.log2 m (no Omega: a proper divisor at least halves the modulus); bound w + 2 *)
Definition cong_gamma (w : width) (c : cong) (z : Z) : Prop :=
  match c with CBot => False | Cong m r => is_word w z /\ (z - r) mod m = 0 end.
Definition cong_domain : word_domain cong.
(* ptop w = Cong 1 0; pconst w z = Cong 0 (wrap w z); pmeet: the Chinese-remainder intersection,
   CBot if the residues clash; join, widen and pmeet normalise their arguments first.
   pforward: bvadd bvsub bvneg bvmul: congruence arithmetic, then the modulus is replaced by its gcd
   with 2^w (wrapping preserves only moduli dividing 2^w); constant-amount bvshl: Cong (m * 2^k)
   (r * 2^k) then the same gcd; bvurem by a constant c: modulus gcd m c; bvzext: unchanged; bvtrunc t:
   modulus gcd m 2^t; bvite: join; the rest Cong 1 0 *)
```

### Reduced products (`DomainsProduct.v`, DOM-4)

One functor builds every product; a reduction supplies the extra precision. Product meanings are
explicitly restricted to words at the supplied width. This restriction is local to products:
`payload_concretisation`, `const_gamma` and the other component meanings remain unchanged.

```coq
Definition product_word_domain {P Q} (D1 : word_domain P) (D2 : word_domain Q)
  (reduce : width -> P * Q -> P * Q) : word_domain (P * Q).
(* plat w = reduced_lattice (plat D1 w) (plat D2 w) (reduce w); ptop and pconst: pairs;
   pforward o wps rw = reduce rw (pforward D1 on the first components, pforward D2 on the second);
   passume: both refinements, each refined operand reduced at its width;
   pmeet w a b = reduce w (pmeet D1 w (fst a) (fst b), pmeet D2 w (snd a) (snd b)) *)
Definition product_pgamma {P Q} (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop) :
  width -> P * Q -> Z -> Prop :=
  fun w pq z => is_word w z /\ G1 w (fst pq) z /\ G2 w (snd pq) z.
Definition payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) : concretisation P Z :=
  {| gamma := G w |}.
Definition word_payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) :
  concretisation P Z := {| gamma := fun p z => is_word w z /\ G w p z |}.

(* Every reduction sends a pair with an empty component, one whose leb to its bottom holds, to the
   bottom pair; reduction_empty states it. *)
Definition reduction_empty {P Q} (LP : lattice P) (LQ : lattice Q) (reduce : P * Q -> P * Q) : Prop :=
  forall p q, leb LP p (bot LP) = true \/ leb LQ q (bot LQ) = true -> reduce (p, q) = (bot LP, bot LQ).

Definition reduce_bits_wrapped (w : width) : tnum * wrapped -> tnum * wrapped.
(* Normalize the arc first. A component <= bottom or contradictory known bits gives the bottom pair.
   With WFull, keep the pair unchanged after those checks. With a proper arc, round its end points
   to the nearest values consistent with the known bits in its circular order, returning the bottom
   pair if none exists; then, if the arc does not wrap, make its common leading bits known. Do two
   rounds. Keeping WFull avoids choosing between incomparable arcs when there is no least arc
   containing all the allowed words; it is required for monotonicity with these proper-arc rounds. *)
Definition reduce_interval_cong (w : width) : interval * cong -> interval * cong.
(* an empty component gives the bottom pair; otherwise round lo up and hi down to values congruent to
   r modulo m (Granger 1989); crossing end points give the bottom pair; equal end points make the
   congruence exact and the interval a point *)
Definition reduce_const_with {Q} (D : word_domain Q) (exact : width -> Q -> option Z) (w : width) :
  flat Z * Q -> flat Z * Q.
(* Let B = (FBot, bot (plat D w)) and f c q = pmeet D w q (pconst D w c).
   First return B for FBot or q <= bot. For FVal c, return B if c is not a word; otherwise
   compute q' = f c q, return B if q' <= bot, and return (FVal c, q') otherwise.
   For FTop, query exact w q: None returns (FTop, q); Some c returns (FVal c, q) if c is a word,
   and B otherwise. Test is_word using decidable integer bounds. In the FVal branch do not query
   exact: the mismatch law below makes an exact conflicting payload reduce to B via the meet. *)

(* These are additional caller obligations, not laws of all word domains. All comparisons use the
   payload's preorder; they do not assert that pmeet is a greatest lower bound. *)
Record const_reduction_laws {Q} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z) : Prop := {
  const_exact_sound : forall w q c z, exact w q = Some c -> is_word w z -> G w q z -> z = c;
  const_exact_monotone : forall w q1 q2 c, leb (plat D w) q1 q2 = true ->
    exact w q2 = Some c ->
    leb (plat D w) q1 (bot (plat D w)) = true \/ exact w q1 = Some c;
  const_meet_monotone : forall w c q1 q2, is_word w c ->
    leb (plat D w) q1 q2 = true ->
    leb (plat D w) (pmeet D w q1 (pconst D w c))
      (pmeet D w q2 (pconst D w c)) = true;
  const_meet_idempotent : forall w c q, is_word w c ->
    leb (plat D w) (pmeet D w q (pconst D w c))
      (pmeet D w (pmeet D w q (pconst D w c)) (pconst D w c)) = true;
  const_meet_exact_fixed : forall w c q, is_word w c -> exact w q = Some c ->
    leb (plat D w) q (pmeet D w q (pconst D w c)) = true;
  const_meet_mismatch : forall w c q d, is_word w c -> exact w q = Some d -> c <> d ->
    leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w)) = true
}.

Definition bits_wrapped_domain : word_domain (tnum * wrapped).
Definition interval_cong_domain (thresholds : list Z) : word_domain (interval * cong).
Definition const_product_domain {Q} (D : word_domain Q) (exact : width -> Q -> option Z) :
  word_domain (flat Z * Q).
(* each is product_word_domain with the matching reduction *)
```

### Demanded bits (`DomainsDemanded.v`, DOM-5)

A mask says which bits of a value matter. This is an agreement domain: a mask `m` relates two words
that are equal on the bits of `m`, and `demand` runs a transfer backwards, from the mask of a result
to
the masks of the operands.

```coq
Definition mask_lattice (w : width) : lattice Z.
(* bits at or above w are ignored: leb a b iff Z.land (wrap w a) (Z.lnot (wrap w b)) = 0;
   bot = 0; join = widen = Z.lor; narrow a _ = a *)
Definition mask_height (w : width) : monotone_height (mask_lattice w).    (* rank = popcount (wrap w m); bound w *)
Definition mask_agreement (w : width) : agreement Z word :=
  {| agree := fun m x y =>
       Z.land (wrap w (snd x)) (wrap w m) = Z.land (wrap w (snd y)) (wrap w m) |}.
Definition demand : op -> list width -> list (option Z) -> Z -> list Z.
(* demand o ws consts m: the masks, one per operand, on which operands of widths ws must agree so
   that the result agrees on m. consts holds each operand's value when forward facts know it. *)
Definition agree_masks (ms : list Z) (xs ys : list word) : Prop :=
  Forall2 (fun m p => agree (mask_agreement (fst (fst p))) m (fst p) (snd p)) ms (List.combine xs ys).
Definition consts_hold (consts : list (option Z)) (xs : list word) : Prop :=
  Forall2 (fun co x => forall c, co = Some c -> wrap (fst x) (snd x) = wrap (fst x) c) consts xs.
Definition masks_leb (ws : list width) (ms ms' : list Z) : Prop :=
  Forall2 (fun w p => leb (mask_lattice w) (fst p) (snd p) = true) ws (List.combine ms ms').
```

The rules of `demand`. Every rule starts with `m := wrap rw m`, where `rw` is the result width (bits
at
or above `rw` are ignored). Then, with `fill_down m` all bits at or below the highest bit of `m` (so
carries are covered), `fill_up m` all bits of the operand at or above the lowest bit of `m`, and
`all`
the full mask of an operand: if `m = 0` every operand mask is `0`. `bvand`: `m`, and `m & c` for an
operand whose other operand is the known constant `c`; `bvor`: `m`, and `m & ~c` likewise; `bvxor
bvnot`:
`m`. `bvadd bvsub bvmul bvneg`: `fill_down m` for each operand. `bvshl` by a known `k`: `m >> k` for
the
first operand; `bvlshr`: `m << k`; `bvashr`: `m << k` plus the sign bit `w - 1` iff some bit `i` of
`m` has
`i + k >= w`; the known amount itself needs `0`; a variable amount: `fill_down m` (`bvshl`) or
`fill_up m`
(`bvlshr`, `bvashr`) for the first operand, and `all` for the amount. `bvrotl` by a known `k`: `m`
rotated
right by `k` for the first operand; `bvrotr` by a known `k`: `m` rotated left by `k`; unknown
amount:
`all`. `bvzext`: `m` restricted to the operand's width; `bvsext`: the same plus the sign bit if `m`
has a
bit at or above it; `bvtrunc t`: `m`; `bvextract hi lo`: `m << lo`; `bvconcat`: `m >> w2` for the
high
part and `m` below `w2` for the low part. `bvite`: mask `1` for the condition, `m` for both
branches.
Every other operator (`bvudiv bvurem bvsdiv bvsrem bvsmod`, comparisons, `bvclz bvctz bvpopcnt`):
`all`
for every operand.

### Memory domains (DOM-6)

```coq
(* DomainsAddress.v: where an access happens *)
Record address : Type := Address {
  site : option positive;               (* singleton object; None: unknown or summary site *)
  offset : interval;                    (* byte offset from the base of the object *)
  size : nat                            (* bytes accessed *)
}.
Definition access : Type := (positive * Z * nat)%type.                (* object, byte offset, size *)
Definition bytes_of (c : access) (b : positive * Z) : Prop :=
  fst b = fst (fst c) /\ snd (fst c) <= snd b < snd (fst c) + Z.of_nat (snd c).
Definition address_gamma : concretisation address access.
(* gamma a (s, k, n): n = size a, site a is None or Some s, and k is in offset a *)
(* Some s denotes one concrete object. A summary site is represented by None, so equal summary
   sites never justify the same-object clauses of covers or disjoint. *)
Definition covers (a1 a2 : address) : bool.
(* the site of a1 is known and equals that of a2, the offset of a1 is one finite value k, and every
   offset of a2 lies in [k, k + Z.of_nat (size a1) - Z.of_nat (size a2)] *)
Definition disjoint (a1 a2 : address) : bool.
(* an offset is empty; or both sites are known and differ; or the sites are known and equal, the
   offsets have finite bounds, and hi1 + size a1 <= lo2 or hi2 + size a2 <= lo1 *)
Definition may_overlap (a1 a2 : address) : bool := negb (disjoint a1 a2).

(* DomainsPointsTo.v: what a pointer may point to *)
Definition points_to : Type := (FinSet.t positive * bool)%type.     (* sites, and whether an unknown object is possible *)
Definition points_to_lattice : lattice points_to :=
  product_lattice (powerset_lattice positive_encoding) bool_lattice.
Definition points_to_gamma : concretisation points_to positive.
(* gamma (s, u) p: FinSet.mem positive_encoding p s = true, or u = true *)
Definition pts_of_site (s : positive) : points_to := (FinSet.add positive_encoding s FinSet.empty, false).
Definition pts_unknown : points_to := (FinSet.empty, true).
Definition pts_may_alias (a b : points_to) : bool :=
  snd a || snd b || negb (FinSet.is_empty (FinSet.inter positive_encoding (fst a) (fst b))).
Definition pts_must_alias (a b : points_to) : bool.
(* neither has the unknown flag, and each has exactly one site, the same one *)

(* DomainsByteRange.v: sets of bytes as sorted disjoint half-open ranges *)
Definition range : Type := (Z * Z)%type.                          (* [lo, hi) *)
Definition ranges_wf (rs : list range) : Prop :=
  Forall (fun r => fst r < snd r) rs /\ StronglySorted (fun r1 r2 => snd r1 < fst r2) rs.
Definition byte_ranges : Type := { rs : list range | ranges_wf rs }.   (* canonical: no empty or adjacent ranges *)
Definition ranges_empty : byte_ranges.
Definition ranges_mem (rs : byte_ranges) (b : Z) : bool.
Definition ranges_add (r : range) (rs : byte_ranges) : byte_ranges.       (* an empty r changes nothing *)
Definition ranges_remove (r : range) (rs : byte_ranges) : byte_ranges.
Definition ranges_union (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_inter (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_diff (rs1 rs2 : byte_ranges) : byte_ranges.
Definition ranges_covers (rs : byte_ranges) (r : range) : bool.           (* every byte of r is in rs *)
Definition ranges_intersects (rs : byte_ranges) (r : range) : bool.       (* some byte of r is in rs *)
Definition ranges_lattice : lattice byte_ranges.                           (* may: inclusion; join = union *)
Definition ranges_gamma : concretisation byte_ranges Z.                    (* gamma rs b: ranges_mem rs b = true *)
```

```coq
(* DomainsFootprint.v: byte ranges of allocation sites; T is the site type (DOM-6) *)
Record footprint (T : Type) : Type := Footprint { fp_site : T; fp_lo : Z; fp_hi : Z }.
(* the bytes [fp_lo, fp_hi) of every block allocated at fp_site *)
Definition covered {T} (F : list (footprint T)) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, (o <= k < o + Z.of_nat w)%Z ->
    exists f, In f F /\ fp_site f = t /\ (fp_lo f <= k < fp_hi f)%Z.
(* every byte of the access lies in a footprint; zero bytes are always covered *)
Definition written {T} (F : list (footprint T)) (t : T) (k : Z) : Prop :=
  exists f, In f F /\ fp_site f = t /\ (fp_lo f <= k)%Z /\ (k < fp_hi f)%Z.     (* byte k of site t *)
Definition footprint_encoding {T} (ET : encoding T) : encoding (footprint T).
(* encode f = encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding)) (fp_site f, (fp_lo f, fp_hi f)) *)
Definition footprints_canonical {T} (ET : encoding T) (F : list (footprint T)) : Prop :=
  Forall (fun f => (fp_lo f < fp_hi f)%Z) F /\
  StronglySorted (fun f g => (encode ET (fp_site f) < encode ET (fp_site g))%positive \/
    (fp_site f = fp_site g /\ (fp_hi f < fp_lo g)%Z)) F.
(* canonical: sites in increasing code; per site the ranges are sorted, disjoint, non-adjacent and
   non-empty, exactly the byte_ranges of that site (site_ranges below) *)
Definition site_ranges {T} (ET : encoding T) (F : list (footprint T)) (t : T) : list range.
(* the (fp_lo, fp_hi) of the footprints of site t, in list order *)
Definition footprints_normalise {T} (ET : encoding T) (F : list (footprint T)) : list (footprint T).
Definition footprints_inter {T} (ET : encoding T) (F G : list (footprint T)) : list (footprint T).
Definition footprints_diff {T} (ET : encoding T) (F G : list (footprint T)) : list (footprint T).
(* Preparation buckets ranges by site, then filters, sorts and coalesces each bucket once, with a
   separate sort of occupied site codes. Inter and diff combine the prepared indexes using the public
   byte_ranges operations; the results are canonical. *)

(* The must-facts of written bytes. The reached carrier contains only canonical lists. *)
Definition canonical_footprints {T} (ET : encoding T) : Type :=
  { F : list (footprint T) | footprints_canonical ET F }.
Definition range_must {T} (ET : encoding T) : Type := lift_bot (canonical_footprints ET).
Definition range_reached {T} (ET : encoding T) (F : list (footprint T)) : range_must ET.
(* Reached (footprints_normalise ET F), with its canonicality proof *)
Definition range_written {T} {ET : encoding T} (a : range_must ET) (t : T) (k : Z) : Prop :=
  match a with Unreached => True | Reached F => written (proj1_sig F) t k end.
Definition range_must_lattice {T} (ET : encoding T) : lattice (range_must ET).
(* reverse coverage order: leb Unreached _ = true; leb (Reached F) Unreached = false; leb (Reached F)
   (Reached G): every byte of proj1_sig G is a byte of proj1_sig F (decided on normal forms);
   bot = Unreached; join: Unreached is neutral; two Reached values give range_reached ET
   (footprints_inter ET (proj1_sig F) (proj1_sig G));
   widen = join; narrow a _ = a. leb, join, range_add and range_remove normalise their list inputs;
   per-site work reuses byte_ranges operations. *)
Definition range_must_top {T} (ET : encoding T) : top (range_must_lattice ET). (* range_reached ET nil *)
Definition range_add {T} (ET : encoding T) (fs : list (footprint T))
  (a : range_must ET) : range_must ET.
(* Unreached stays; Reached F gives range_reached ET (fs ++ proj1_sig F) *)
Definition range_remove {T} (ET : encoding T) (fs : list (footprint T))
  (a : range_must ET) : range_must ET.
(* Unreached stays; Reached F removes every byte that fs overlaps, then normalises. *)
Definition range_covers {T} {ET : encoding T} (a : range_must ET) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, (o <= k < o + Z.of_nat w)%Z -> range_written a t k.
Definition range_must_gamma {T} {ET : encoding T} : concretisation (range_must ET) (T -> Z -> Prop).
(* Unreached: nothing; Reached F: the sets W of written bytes with W (fp_site f) k for every f in
   proj1_sig F and every k in [fp_lo f, fp_hi f) *)
```

### Equality partitions (`DomainsEquality.v`, DOM-7)

A fact "these keys are equal" is a partition of the keys; the join of two facts keeps the equalities
that hold in both, which is the intersection of the two equivalence relations.

```coq
Definition partition {K} (E : encoding K) : Type := lift_bot { u : UnionFind.t K | UnionFind.wf E u }.
(* Unreached: unreachable, every key equal to every other (the bottom) *)
Definition partition_equiv {K} (E : encoding K) (p : partition E) (x y : K) : Prop :=
  match p with Unreached => True | Reached u => UnionFind.equiv E (proj1_sig u) x y end.
Definition partition_lattice {K} (E : encoding K) : lattice (partition E).
(* leb Unreached _ = true; leb (Reached _) Unreached = false; leb (Reached u1) (Reached u2): every
   equality of u2 holds in u1; bot = Unreached; join Unreached p = p; join (Reached u1) (Reached u2)
   is Reached with the intersection of the
   equivalences (the keys of both supports grouped by the pair of their representatives);
   widen = join; narrow a _ = a *)
Definition partition_top {K} (E : encoding K) : top (partition_lattice E).  (* Reached UnionFind.make *)
Definition partition_union {K} (E : encoding K) (x y : K) (p : partition E) : partition E.   (* add x = y *)
Definition partition_forget {K} (E : encoding K) (x : K) (p : partition E) : partition E.
(* Unreached stays Unreached. Reached u: x's class is rebuilt without x and x becomes alone: the
   structure with the classes of u on the support keys other than x, e.g. each such key unioned with
   the first key of its class in u (x itself is skipped even when it is the representative) *)
Definition key_update {K V} (E : encoding K) (x : K) (v : V) (s : K -> V) : K -> V :=
  fun k => if Pos.eqb (encode E k) (encode E x) then v else s k.     (* s with x rebound to v *)
Definition partition_test {K} (E : encoding K) (x y : K) (p : partition E) : bool * partition E.
(* the test, and the structure with its paths compressed *)
Definition partition_gamma {K V} (E : encoding K) : concretisation (partition E) (K -> V).
(* Unreached: nothing; Reached u: values of equivalent keys are equal *)

(* DomainsSymbolic.v: symbolic keys for value numbering *)
Definition sym_key : Type := list positive.
Definition expr_key (o : op) (args : list positive) : sym_key.
(* encode op_encoding o, then args; for a commutative o the args are sorted by Pos.compare *)
Record numbering : Type := Numbering { ids : Table.t positive; next : positive }.
Definition numbering_empty : numbering := Numbering Table.empty 1%positive.
Definition intern (k : sym_key) (n : numbering) : positive * numbering.
(* the number of k if it is present; else next n, recorded, with next incremented *)
Definition numbering_wf (n : numbering) : Prop :=
  Table.wf (ids n) /\ (forall k i, Table.get k (ids n) = Some i -> (i < next n)%positive) /\
  (forall k1 k2 i, Table.get k1 (ids n) = Some i -> Table.get k2 (ids n) = Some i -> k1 = k2).
```

## Theorems

### The interface and the width tags (DOM-1a)

```coq
Section NumericLaws.
Context {A : Type} (D : numeric_domain A) (G : concretisation A word) (env : nat -> A)
  (cenv : nat -> word) (e : expr) (a : A) (r : word) (o : op) (args : list expr) (i : nat) (w : width) (z : Z).

(** The abstract evaluator follows the expression's structure. *)
Theorem abs_eval_var : abs_eval D env (Var i) = env i.
Theorem abs_eval_const : abs_eval D env (Const w z) = of_const D w z.
Theorem abs_eval_app : abs_eval D env (App o args) = forward D o (List.map (abs_eval D env) args).
(* Proof idea: unfolding the inner fix. Card: DOM-1a. *)

(** One generic soundness theorem: abstract evaluation over-approximates concrete evaluation. *)
Theorem abs_eval_sound : numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G (abs_eval D env e) r.
(* Proof idea: induction on e; the App case uses forward_sound on the pointwise-sound arguments,
   with the nested induction over args as an auxiliary lemma. Card: DOM-1a. *)

(** A guard keeps the environment sound, and refinement only goes down. *)
Theorem abs_assume_sound : numeric_laws D G -> env_ok cenv -> env_sound G env cenv ->
  eval cenv e = Some r -> gamma G a r -> env_sound G (abs_assume D env e a) cenv.
Theorem abs_assume_refines : numeric_laws D G ->
  leb (lat D) (abs_assume D env e a i) (env i) = true.
(* Proof idea: Var uses meet_sound and meet_lower_left; App uses assume_sound and assume_refines,
   threading the environment through the arguments. Card: DOM-1a. *)
End NumericLaws.

Section TaggedLaws.
Context {P : Type} (D : word_domain P) (G : width -> P -> Z -> Prop).

(** The tagged lattice is a lattice, and a payload domain lifts to a numeric domain. *)
Theorem tagged_laws : (forall w, lattice_laws (plat D w)) ->
  lattice_laws (tagged_lattice (plat D)).
Theorem capped_laws : (forall w, lattice_laws (plat D w)) -> forall maxw : width,
  lattice_laws (capped_lattice maxw (plat D)).
Theorem tagged_numeric_laws : word_laws D G ->
  numeric_laws (tagged_domain D) (tagged_gamma G).
(** Clamping to the cap only widens, and the capped domain is a sound numeric domain. *)
Theorem clamp_gamma : forall (maxw : width) (t : tagged P) (c : word),
  gamma (tagged_gamma G) t c -> gamma (capped_gamma G maxw) (clamp maxw t) c.
Theorem capped_numeric_laws : word_laws D G -> forall maxw : width,
  numeric_laws (capped_domain D maxw) (capped_gamma G maxw).
(* Proof idea: case analysis on TBot, TVal and TAny; Forall2 over the operands turns a list of tags
   into a list of payloads, and eval_op_width (Bits) gives the result width; a payload that is
   <= bot has an empty meaning (pgamma_bot_empty with pgamma_monotone), so returning TBot loses
   nothing; the capped case is the tagged one followed by clamp_gamma. Card: DOM-1a. *)
End TaggedLaws.
```

### Constants and signs (DOM-1a)

```coq
(** Constants and signs: sound payload domains; signs also have least upper bounds. *)
Theorem const_word_laws : word_laws const_domain const_gamma.
Theorem sign_laws : lattice_laws sign_lattice.
Theorem sign_lub : lub_laws sign_lattice.
Theorem sign_word_laws : word_laws sign_domain sign_gamma.
(* Proof idea: the lattice laws by case analysis on the constructors; each transfer rule by
   Bits lemmas (wrap_*, signed_range, testbit laws) for the operator it covers; the constant
   passume rules by inverting the operator with eval_op. Card: DOM-1a. *)
```

### Intervals (DOM-1b)

```coq
Section IntervalLaws.
Context (thresholds : list Z).

(** Intervals: a lattice with least upper bounds, monotone meaning, sound transfers. *)
Theorem interval_laws : lattice_laws (interval_lattice thresholds).
Theorem interval_lub : lub_laws (interval_lattice thresholds).
Theorem interval_gamma_laws : concretisation_laws (interval_lattice thresholds) interval_gamma.
Theorem interval_gamma_bot_empty : bottom_empty (interval_lattice thresholds) interval_gamma.
Theorem interval_word_laws : word_laws (interval_domain thresholds) interval_pgamma.
(* Proof idea: the lattice laws by case analysis on the bounds; each transfer rule by Bits
   lemmas (wrap_*, signed_range, testbit laws) for the operator it covers; assume by inverting
   the operator's rule on the interval bounds. Card: DOM-1b. *)
End IntervalLaws.
```

### Known bits, wrapping intervals, congruences (DOM-2, DOM-3, DOM-4)

```coq
Section WordInstanceLaws.
Context (w : width).

(** Known bits (DOM-2): least upper bounds, and every forward transfer and assume is sound. *)
Theorem tnum_laws : lattice_laws (tnum_lattice w).
Theorem tnum_lub : lub_laws (tnum_lattice w).
Theorem known_bits_word_laws : word_laws known_bits_domain tnum_gamma.
(* Proof idea: bit by bit with testbit_* for the exact operators; the add and sub closed forms
   by induction on the bit with the carry; mul by the trailing zeros of the factors (wmul with
   powers of two); the division rules from wudiv_spec, wurem_lt and the SMT-LIB definitions at a
   zero divisor. Card: DOM-2. *)

(** Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
    arcs; there is no least upper bound in general, so there is no lub_laws theorem. *)
Theorem wrapped_laws : lattice_laws (wrapped_lattice w).
Theorem wrapped_join_minimal : forall a b c : wrapped,
  leb (wrapped_lattice w) a c = true -> leb (wrapped_lattice w) b c = true ->
  wrapped_size w (join (wrapped_lattice w) a b) <= wrapped_size w c.
Theorem wrapped_gamma_laws : concretisation_laws (wrapped_lattice w)
  (Concretisation wrapped Z (wrapped_gamma w)).
Theorem wrapped_word_laws : word_laws wrapped_domain wrapped_gamma.
(* Proof idea: arcs through off c x = (x - c) mod 2^w; a proper arc c that covers a and b is an
   interval of its own linear order, so one of the two candidate arcs lies inside it
   (wrapped_join_minimal); the widening rank drops because 3s >= 2s raises Z.log2 of the size by
   one; the transfer rules by case analysis on the poles, as in Navas et al. Card: DOM-3. *)

(** Congruences (DOM-4). *)
Theorem cong_laws : lattice_laws (cong_lattice w).
Theorem cong_lub : lub_laws (cong_lattice w).
Theorem cong_word_laws : word_laws cong_domain cong_gamma.
(* Proof idea: divisibility and Z.gcd lemmas; wrapping keeps only moduli dividing 2^w. Card: DOM-4. *)
End WordInstanceLaws.
```

### Reduced products (DOM-4)

```coq
Section ProductWordLaws.
Context {P Q : Type} (D1 : word_domain P) (D2 : word_domain Q) (G1 : width -> P -> Z -> Prop)
  (G2 : width -> Q -> Z -> Prop) (reduce : width -> P * Q -> P * Q).

(** A product of two sound payload domains with a sound, monotone, idempotent reduction is sound. *)
Theorem product_word_laws : word_laws D1 G1 -> word_laws D2 G2 ->
  (forall w, reduction_laws (plat D1 w) (plat D2 w) (reduce w)) ->
  (forall w, reduction_sound (word_payload_concretisation G1 w)
    (word_payload_concretisation G2 w) (reduce w)) ->
  word_laws (product_word_domain D1 D2 reduce) (product_pgamma G1 G2).
(* Proof idea: Order's reduced_laws and reduced_gamma_laws per width; each transfer is the pair of
   transfers followed by reduce, and reduce_gamma keeps the word meaning. `eval_op_is_word` supplies
   the forward result's range; input and assumed operand words already have that range. Card: DOM-4. *)
End ProductWordLaws.

(** Adding the local word restriction does not change any tagged product meaning. *)
Theorem product_tagged_gamma_equiv : forall {P Q : Type}
  (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop) a v,
  gamma (tagged_gamma (product_pgamma G1 G2)) a v <->
  gamma (tagged_gamma (fun w pq z => G1 w (fst pq) z /\ G2 w (snd pq) z)) a v.
(* `tagged_gamma` already restricts TVal payloads to words; TBot and TAny are unchanged. Card: DOM-4. *)

Section ReductionLaws.
Context (thresholds : list Z) (w : width).

(** The three reductions only go down, are monotone and idempotent, keep the meaning, and send a
    pair with an empty component to the bottom pair. *)
Theorem reduce_bits_wrapped_laws :
  reduction_laws (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w) /\
  reduction_sound (word_payload_concretisation tnum_gamma w)
    (word_payload_concretisation wrapped_gamma w)
    (reduce_bits_wrapped w) /\
  reduction_empty (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w).
Theorem reduce_interval_cong_laws :
  reduction_laws (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w) /\
  reduction_sound (word_payload_concretisation interval_pgamma w)
    (word_payload_concretisation cong_gamma w)
    (reduce_interval_cong w) /\
  reduction_empty (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w).
Theorem reduce_const_with_laws : forall {Q : Type} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z), word_laws D G -> const_reduction_laws D G exact ->
  reduction_laws (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w) /\
  reduction_sound (word_payload_concretisation const_gamma w) (word_payload_concretisation G w)
    (reduce_const_with D exact w) /\
  reduction_empty (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w).
(* Proof idea: for proper wrapped arcs use the upper arc's circular linear order: every contained
   proper arc is a subinterval, and intersecting with more known bits only moves selected endpoints
   inward. If the upper rounded arc is nonwrapping, a contained nonempty arc is nonwrapping too,
   so its leading-bit refinement includes the upper one's. Full arcs and contradictions are separate
   cases. Prove one-round monotonicity and that two rounds are stable, including raw masks and arc
   representations. For intervals, the least and greatest consistent endpoints are monotone.
   For constants use the separate meet and exact-query laws, including noncanonical and empty
   payloads. A second application is equivalent in the preorder; soundness keeps every shared word.
   Card: DOM-4. *)
End ReductionLaws.

(** The three named products are sound numeric domains. *)
Theorem bits_wrapped_numeric_laws : numeric_laws (tagged_domain bits_wrapped_domain)
  (tagged_gamma (product_pgamma tnum_gamma wrapped_gamma)).
Theorem interval_cong_numeric_laws : forall thresholds : list Z,
  numeric_laws (tagged_domain (interval_cong_domain thresholds))
    (tagged_gamma (product_pgamma interval_pgamma cong_gamma)).
(* Proof idea: product_word_laws with the reductions' laws, then tagged_numeric_laws. Card: DOM-4. *)
```

### Demanded bits (DOM-5)

```coq
Section DemandedLaws.
Context (w : width) (o : op) (ws : list width) (consts : list (option Z)) (m m' : Z)
  (xs ys : list word) (r1 r2 : word) (rw : width).

(** Masks form a lattice with least upper bounds, and agree-on-the-mask is an agreement. *)
Theorem mask_laws : lattice_laws (mask_lattice w).
Theorem mask_lub : lub_laws (mask_lattice w).
Theorem mask_agreement_laws : agreement_laws (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_bot : agreement_bot (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_join : agreement_join_law (mask_lattice w) (mask_agreement w).
Theorem mask_agreement_equivalence : agreement_equivalence (mask_agreement w).
(* Proof idea: Z.land with Z.lnot and Z.lor; bits below w only, by testbit_wrap. Card: DOM-5. *)

(** Soundness: operands of equal widths that agree under the demanded masks, and whose known
    constants are right, give results that agree under the output mask. *)
Theorem demand_sound : List.map fst xs = List.map fst ys ->
  consts_hold consts xs -> consts_hold consts ys ->
  agree_masks (demand o (List.map fst xs) consts m) xs ys ->
  eval_op o xs = Some r1 -> eval_op o ys = Some r2 ->
  agree (mask_agreement (fst r1)) m r1 r2.
(* Proof idea: per operator, from testbit_* laws: a result bit depends on the operand bits the
   rule demands (carries on bits at or below it). Card: DOM-5. *)

(** Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone. *)
Theorem demand_zero : List.length ws = arity o ->
  demand o ws consts 0 = List.repeat 0 (arity o).
Theorem demand_length : List.length ws = arity o ->
  List.length (demand o ws consts m) = arity o.
Theorem demand_monotone : result_width o ws = Some rw -> leb (mask_lattice rw) m m' = true ->
  masks_leb ws (demand o ws consts m) (demand o ws consts m').
(* Proof idea: each rule is monotone in m (shifts, masks and fill_down preserve inclusion). Card: DOM-5. *)
End DemandedLaws.
```

### Memory domains (DOM-6)

```coq
Section MemoryLaws.
Context (a1 a2 : address) (c1 c2 : access) (b : positive * Z) (s s1 s2 : positive) (k : Z)
  (p q : positive) (pa pb : points_to).

(** Each predicate is sound for every pair of concrete accesses the addresses describe. *)
Theorem covers_sound : covers a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c2 b -> bytes_of c1 b.
Theorem disjoint_sound : disjoint a1 a2 = true -> gamma address_gamma a1 c1 ->
  gamma address_gamma a2 c2 -> bytes_of c1 b -> bytes_of c2 b -> False.
Theorem may_overlap_sound : gamma address_gamma a1 c1 -> gamma address_gamma a2 c2 ->
  bytes_of c1 b -> bytes_of c2 b -> may_overlap a1 a2 = true.
(** The predicates are not trivially false: an exact address covers itself, and objects at
    different known sites are disjoint. *)
Theorem covers_exact : site a1 = Some s -> offset a1 = Itv (Fin k) (Fin k) -> covers a1 a1 = true.
Theorem disjoint_sites : site a1 = Some s1 -> site a2 = Some s2 -> s1 <> s2 -> disjoint a1 a2 = true.
(* Proof idea: unfold bytes_of and address_gamma; the offset arithmetic by lia. Card: DOM-6. *)

(** Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries. *)
Theorem points_to_laws : lattice_laws points_to_lattice.
Theorem points_to_lub : lub_laws points_to_lattice.
Theorem points_to_gamma_laws : concretisation_laws points_to_lattice points_to_gamma.
Theorem pts_may_alias_sound : gamma points_to_gamma pa p -> gamma points_to_gamma pb p ->
  pts_may_alias pa pb = true.
Theorem pts_must_alias_sound : pts_must_alias pa pb = true -> gamma points_to_gamma pa p ->
  gamma points_to_gamma pb q -> p = q.
Theorem pts_of_site_gamma : gamma points_to_gamma (pts_of_site s) p <-> p = s.
(* Proof idea: Order's product_laws, powerset_laws and bool_laws; the queries by FinSet.mem_inter. Card: DOM-6. *)
End MemoryLaws.

Section ByteRangeLaws.
Context (rs rs1 rs2 : byte_ranges) (r : range) (b : Z).

(** Membership laws; a byte-range set is determined by its bytes, so equality is extensional. *)
Theorem ranges_mem_empty : ranges_mem ranges_empty b = false.
Theorem ranges_mem_add : ranges_mem (ranges_add r rs) b =
  ((fst r <=? b) && (b <? snd r) || ranges_mem rs b)%bool.
Theorem ranges_mem_remove : ranges_mem (ranges_remove r rs) b =
  (ranges_mem rs b && negb ((fst r <=? b) && (b <? snd r)))%bool.
Theorem ranges_mem_union : ranges_mem (ranges_union rs1 rs2) b = (ranges_mem rs1 b || ranges_mem rs2 b)%bool.
Theorem ranges_mem_inter : ranges_mem (ranges_inter rs1 rs2) b = (ranges_mem rs1 b && ranges_mem rs2 b)%bool.
Theorem ranges_mem_diff : ranges_mem (ranges_diff rs1 rs2) b = (ranges_mem rs1 b && negb (ranges_mem rs2 b))%bool.
Theorem ranges_ext : (forall b, ranges_mem rs1 b = ranges_mem rs2 b) -> proj1_sig rs1 = proj1_sig rs2.
Theorem ranges_covers_spec : ranges_covers rs r = true <->
  forall b, fst r <= b < snd r -> ranges_mem rs b = true.
Theorem ranges_intersects_spec : ranges_intersects rs r = true <->
  exists b, fst r <= b < snd r /\ ranges_mem rs b = true.
(* Proof idea: a linear merge of two sorted lists; the invariant ranges_wf makes neighbours
   non-adjacent, so a canonical list is a function of its bytes. Card: DOM-6. *)

(** The may lattice of byte ranges. *)
Theorem ranges_laws : lattice_laws ranges_lattice.
Theorem ranges_lub : lub_laws ranges_lattice.
Theorem ranges_gamma_laws : concretisation_laws ranges_lattice ranges_gamma.
(* Proof idea: from the membership laws and ranges_ext. Card: DOM-6. *)
End ByteRangeLaws.

Section FootprintLaws.
Context {T : Type} (ET : encoding T) (a b : range_must ET) (F G fs : list (footprint T)) (t : T)
  (o k : Z) (w : nat) (W : T -> Z -> Prop).

(** Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
    bytes; its per-site ranges are byte_ranges. *)
Theorem footprints_normalise_canonical : footprints_canonical ET (footprints_normalise ET F).
Theorem footprints_normalise_written : written (footprints_normalise ET F) t k <-> written F t k.
Theorem footprints_inter_canonical : footprints_canonical ET (footprints_inter ET F G).
Theorem footprints_inter_written : written (footprints_inter ET F G) t k <->
  written F t k /\ written G t k.
Theorem footprints_diff_canonical : footprints_canonical ET (footprints_diff ET F G).
Theorem footprints_diff_written : written (footprints_diff ET F G) t k <->
  written F t k /\ ~ written G t k.
Theorem footprints_ext : footprints_canonical ET F -> footprints_canonical ET G ->
  (forall t k, written F t k <-> written G t k) -> F = G.
Theorem footprints_canonical_ranges : footprints_canonical ET F -> ranges_wf (site_ranges ET F t).
(* Proof idea: the per-site claims are the ByteRangeLaws on site_ranges; the sort by encode
   orders the sites. Card: DOM-6. *)

(** covered is exactly bytewise coverage, including empty accesses and noncanonical lists. *)
Theorem covered_written : covered F t o w -> forall k, o <= k < o + Z.of_nat w -> written F t k.
Theorem covered_bytewise :
  (covered F t o w <-> forall k, o <= k < o + Z.of_nat w -> written F t k).
(* Proof idea: unfold covered and written. Card: DOM-6. *)

(** The must lattice of ranges: a lattice with least upper bounds, ordered by bytes. *)
Theorem range_must_laws : lattice_laws (range_must_lattice ET).
Theorem range_must_lub : lub_laws (range_must_lattice ET).
Theorem range_must_leb_spec : leb (range_must_lattice ET) (range_reached ET F)
  (range_reached ET G) = true <->
  forall t k, written G t k -> written F t k.
Theorem range_reached_written : range_written (range_reached ET F) t k <-> written F t k.
(** Meaning: Unreached has no concrete states; Reached F means every footprint byte is written. *)
Theorem range_must_gamma_laws : concretisation_laws (range_must_lattice ET) range_must_gamma.
Theorem range_must_gamma_bot_empty : bottom_empty (range_must_lattice ET) range_must_gamma.
Theorem range_must_gamma_top_full : top_full (range_must_top ET) range_must_gamma.
Theorem range_covers_sound : gamma range_must_gamma a W -> range_covers a t o w ->
  forall k, o <= k < o + Z.of_nat w -> W t k.
(** range_covers is exactly bytewise coverage, including an access of zero bytes. *)
Theorem range_covers_iff_written :
  (range_covers a t o w <-> forall k, o <= k < o + Z.of_nat w -> range_written a t k).
(** Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
    overlapped bytes away and keeps the others. *)
Theorem range_covers_add :
  (range_covers (range_add ET fs a) t o w <->
   forall k, o <= k < o + Z.of_nat w -> written fs t k \/ range_written a t k).
Theorem range_covers_remove :
  (range_covers (range_remove ET fs (range_reached ET F)) t o w <->
   forall k, o <= k < o + Z.of_nat w -> written F t k /\ ~ written fs t k).
(** The operations are sound for the meaning: added bytes that are written stay written, and bytes
    outside fs keep their status when fs may have been overwritten. *)
Theorem range_add_gamma : gamma range_must_gamma a W ->
  (forall f k, In f fs -> fp_lo f <= k < fp_hi f -> W (fp_site f) k) ->
  gamma range_must_gamma (range_add ET fs a) W.
Theorem range_remove_gamma : forall W' : T -> Z -> Prop, gamma range_must_gamma a W ->
  (forall t k, ~ written fs t k -> W t k -> W' t k) ->
  gamma range_must_gamma (range_remove ET fs a) W'.
(* Proof idea: bytes of the results by the footprints_*_written laws; the order is reverse byte
   inclusion, so reflexivity, transitivity and the upper bounds are propositional; join_least follows
   from intersection. Card: DOM-6. *)
End FootprintLaws.

(** footprint_encoding is the encoding of the triple of site code and bounds, by construction. *)
Theorem footprint_encoding_spec : forall {T} (ET : encoding T) (f : footprint T),
  encode (footprint_encoding ET) f =
  encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding)) (fp_site f, (fp_lo f, fp_hi f)).
(* Proof idea: unfolding the definition; injectivity comes from the pair encoding's. Card: DOM-6. *)
```

### Equality partitions and symbolic keys (DOM-7)

```coq
Section PartitionLaws.
Context {K V : Type} (E : encoding K) (x y a b : K) (p p1 p2 : partition E) (s : K -> V) (v : V).

(** Partitions form a lattice with least upper bounds; the join is the intersection of equivalences. *)
Theorem partition_laws : lattice_laws (partition_lattice E).
Theorem partition_lub : lub_laws (partition_lattice E).
Theorem partition_join_spec : partition_equiv E (join (partition_lattice E) p1 p2) a b <->
  partition_equiv E p1 a b /\ partition_equiv E p2 a b.
(** Adding an equality merges exactly the two classes. *)
Theorem partition_union_spec : partition_equiv E (partition_union E x y p) a b <->
  partition_equiv E p a b \/
  (partition_equiv E p a x /\ partition_equiv E p y b) \/
  (partition_equiv E p a y /\ partition_equiv E p x b).
(** Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
    specification needs p <> Unreached, whose equivalence relates every pair. *)
Theorem partition_forget_unreached : partition_forget E x Unreached = Unreached.
Theorem partition_forget_spec : p <> Unreached ->
  (partition_equiv E (partition_forget E x p) a b <->
   (partition_equiv E p a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
Theorem partition_forget_leb : leb (partition_lattice E) p (partition_forget E x p) = true.
Theorem partition_forget_gamma : gamma (@partition_gamma K V E) p s ->
  gamma (@partition_gamma K V E) (partition_forget E x p) (key_update E x v s).
(** The test agrees with the relation and returns an equivalent partition. *)
Theorem partition_test_correct :
  (fst (partition_test E x y p) = true <-> partition_equiv E p x y) /\
  (forall a b, partition_equiv E (snd (partition_test E x y p)) a b <-> partition_equiv E p a b).
(** Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything. *)
Theorem partition_gamma_laws : concretisation_laws (partition_lattice E) (@partition_gamma K V E).
Theorem partition_gamma_bot_empty : bottom_empty (partition_lattice E) (@partition_gamma K V E).
Theorem partition_top_full : top_full (partition_top E) (@partition_gamma K V E).
(* Proof idea: UnionFind.union_equiv, equivb_correct and keys_support; the join groups keys by the
   pair of representatives, which is the meet of the two equivalences; forget unions the support
   keys other than x with their first classmate, so classes of u lose only x (keys_support for keys
   outside the support), and the gamma law reads the specification at a and b. Card: DOM-7. *)
End PartitionLaws.

Section SymbolicLaws.
Context (n : numbering) (k k1 k2 k' : sym_key) (i : positive) (o : op) (args1 args2 : list positive)
  (a b : positive).

(** Interning: found keys keep their number, new keys get the next one, and the table only grows. *)
Theorem numbering_wf_empty : numbering_wf numbering_empty.
Theorem numbering_wf_intern : numbering_wf n -> numbering_wf (snd (intern k n)).
Theorem intern_get : Table.get k (ids (snd (intern k n))) = Some (fst (intern k n)).
Theorem intern_found : Table.get k (ids n) = Some i -> intern k n = (i, n).
Theorem intern_fresh : Table.get k (ids n) = None ->
  fst (intern k n) = next n /\ next (snd (intern k n)) = Pos.succ (next n).
Theorem intern_stable : Table.get k' (ids n) = Some i -> Table.get k' (ids (snd (intern k n))) = Some i.
(** Numbers identify keys: two keys that get one number from a threaded numbering are equal. *)
Theorem intern_injective : numbering_wf n ->
  fst (intern k2 (snd (intern k1 n))) = fst (intern k1 n) -> k2 = k1.
(** Keys respect commutativity, and equal keys denote equal values under any valuation. *)
Theorem expr_key_commutative : commutative o = true -> expr_key o [a; b] = expr_key o [b; a].
Theorem expr_key_eval : expr_key o args1 = expr_key o args2 -> forall val : positive -> word,
  eval_op o (List.map val args1) = eval_op o (List.map val args2).
(* Proof idea: Table.get_set_* and Table.wf_set; expr_key_eval by cases on commutative, using
   commutative_sound when the sorted lists are equal but the lists differ. Card: DOM-7. *)
End SymbolicLaws.
```

## Algorithms and references

- **Abstract domains.** P. Cousot and R. Cousot, POPL 1977 and 1979: lattices, widening, narrowing,
  reduced products, signs. Constants: Kildall, POPL 1973. Intervals with threshold widening:
  Cousot and Cousot 1977; Blanchet et al., PLDI 2003.
- **Known bits.** Vishwanathan, Shachnai, Narayana and Nagarakatte, "Sound, precise, and fast
  abstract
  interpretation with tristate numbers", CGO 2022 (`tnum_add`, `tnum_sub`, `our_mul`); the same
  representation as LLVM's `KnownBits` and the Linux eBPF verifier's `tnum`.
- **Wrapping intervals.** Navas, Schachte, Søndergaard and Stuckey, "Signedness-agnostic program
  analysis: precise integer bounds for low-level code", APLAS 2012: arcs of the circle, the north
  and
  south poles, join by minimal cover, widening by doubling.
- **Congruences.** Granger, "Static analysis of arithmetical congruences", Int. J. Computer
  Mathematics, 1989, which also gives the interval and congruence reduction.
- **Reduced product.** Cousot and Cousot 1979; Cousot, Cousot and Mauborgne, "The reduced product of
  abstract domains and the combination of decision procedures", FoSSaCS 2011.
- **Sign-separated bits and bounds.** Fan et al., "Program Analysis Combining Generalized
  Bit-Level and Word-Level Abstractions", ISSTA 2025, DOI 10.1145/3728905. DOM-9 specifies a
  Gaulois adaptation and a stronger reduction; it does not claim full paper transfer parity.
- **Demanded bits.** LLVM's `DemandedBits` analysis, stated here as a relational agreement so that
  soundness is a theorem about two evaluations, with forward constants as premises.
- **Memory.** Site-and-offset addresses as in Miné, "Field-sensitive value analysis of embedded C
  programs with union types and pointer arithmetics", LCTES 2006; points-to sets as in Andersen's
  thesis (1994); byte-range sets as sorted interval lists.
- **Equality and numbering.** Alpern, Wegman and Zadeck, "Detecting equality of variables in
  programs", POPL 1988 (partitions; the join is the intersection); Cocke and Schwartz 1970 and
  Briggs, Cooper and Simpson, "Value numbering", 1997; hash-consing as in Filliâtre and Conchon,
  ML Workshop 2006.

## Performance notes

- Constants, signs, intervals and congruence arithmetic cost a constant number of `Z` operations per
  transfer. Known-bits transfers use O(1) big-integer operations except variable shifts, which use
  O(1 + log w), and variable rotations, which use O(w), on O(w)-bit integers for operand width `w`.
  This counts big-integer operations, not bit complexity; scalar shifts guard oversized amounts.
  Wrapped-interval multiplication is a constant number of cases. `tagged_domain` adds one width
  comparison per join.
- `capped` carriers hold their proof in `Prop`: they extract to the bare payload. Ranks sum over
  widths
  up to the cap and occur only in proofs. A reduced product calls `reduce` after each transfer, join
  and meet; `reduce_bits_wrapped` is a fixed two rounds.
- Byte-range operations are linear merges of sorted lists; the ranges per object stay few. A
  partition's `leb` is O(n) finds with compression; its join groups the keys of both supports in one
  pass through a `Map` keyed by the pair of representatives, O(n log n) in the support. `intern` is
  one `Table.get` and at most one `Table.set`.
- Prepared indexes: `numbering_wf` (a table with its next number) and `ranges_wf` (the canonical
  list), with agreement lemmas `intern_injective` and `ranges_ext`.
- DOM-9's feasible-extremum search visits at most `w` positions with O(w)-bit operands. A transfer
  uses at most eight input-branch combinations, plus component costs and reduction. The proposed
  join widening may require exponentially many improvements in `w`; these are cost estimates,
  not benchmark results or a whole-analysis complexity claim.

## Open questions

1. **Monotone transfers.** The laws give soundness and widening termination only. No theorem claims
   that `forward` is monotone, so Fixpoint's least-solution theorems do not apply to numeric
   systems.
2. **Precision.** The rule lists describe the intended transfers. The proved contract is soundness
   (`word_laws`, `numeric_laws`); a card may be more precise if the laws hold.
3. **Open cards.** DOM-6 now also holds footprints and the must lattice of ranges, and DOM-7 holds
   partition forgetting; if either outgrows its budget it splits along the file boundaries of the
   Files table.

## Notes for other documents

Renames and requests that follow from this document (document, old name or text, new name or text).

1. analyses.md: `range_must T` becomes `range_must ET`; raw lists enter the canonical carrier via
   `range_reached ET F`. `range_add fs a` becomes `range_add ET fs a` (in `validated_system` and
   `dead_store_transfer`); `range_must_top ET`, `range_must_lattice ET`, `range_remove ET fs a`
   and `range_covers a t o w` use the same encoding-indexed carrier.
2. analyses.md: `range_must_lattice` merges adjacent footprints and `range_covers` means bytewise
   coverage, including zero-width accesses. `validated_sound` needs `accessible` to follow from
   bytewise coverage, including the empty access, or needs a suitable premise and statement.
3. analyses.md request 3: `partition_forget_spec` holds under `p <> Unreached`; use
   `partition_forget_unreached` at `Unreached`. `partition` is `lift_bot {u | UnionFind.wf E u}`.
4. examples.md: `const_domain : numeric_domain const_fact` becomes `tagged_domain const_domain :
   numeric_domain (tagged (flat Z))` with `tagged_gamma const_gamma`; `nlat` and `nconc` are `lat`
   and `gamma` of that domain. examples.md also names a toy constructor `Fin`; the interval bound
   constructor of this document is `Fin` too, so one of them should be renamed.
5. Analyses and Examples use `Bits.expr` and `Bits.eval` from the Bits expression module.
6. TASKS.md, LEDGER.md and the cards: DOM-1 becomes DOM-1a (ORD-1, BIT-1) and DOM-1b (DOM-1a);
   VIEW-4 and ANA-8 list DOM-1a; DOM-2 and DOM-3 list DOM-1a; DOM-4 and DOM-6 also list DOM-1b;
   DOM-7 lists BIT-1 (`expr_key` uses `op_encoding` and `commutative`).

## Selectable signed bit-and-bounds domain (DOM-9)

### Representation and meaning

```coq
Inductive sb_half : Type :=
  | SBEmpty
  | SBRange (bits : tnum) (lo hi : Z).

Record signed_bounds : Type := SignedBounds {
  sb_zero : sb_half;
  sb_one : sb_half
}.

Definition sb_bit_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition sb_interval_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition sb_half_gamma (w : width) (sign : bool) (h : sb_half) (z : Z) : Prop.
Definition signed_bounds_gamma (w : width) (a : signed_bounds) (z : Z) : Prop.
Definition sb_reduce_half (w : width) (sign : bool) (h : sb_half) : sb_half.
Definition signed_bounds_reduce (w : width) (a : signed_bounds) : signed_bounds.
```

For either component gamma, require `is_word w z` and the most significant bit of z equal to
`sign`. `SBEmpty` means false in both. In `SBRange t lo hi`, bit gamma additionally means
`tnum_gamma w t z`; interval gamma additionally means `lo <= z <= hi`. Half gamma is their
conjunction, and signed-bounds gamma is the union of the half gammas, with false/true sign for
`sb_zero`/`sb_one`. Thus out-of-range raw bounds are intersected with the hemisphere, not wrapped;
tnum masks have exactly DOM-2's modulo-width meaning. The stored constructor has no width: its
meaning and all operations take the width explicitly.

For a half, let S be exactly the finite words satisfying half gamma. If S is empty, reduction
returns `SBEmpty`. Otherwise return `SBRange t l u` with l and u respectively the minimum and
maximum of S, and t the unique normalized mask identifying exactly the bits constant throughout
S (and leaving all other bits unknown). Thus its two components are their independently least
abstractions of S. Normalize masks to w bits and use a single canonical empty representation.
`signed_bounds_reduce` applies this separately to both halves.

Implement S's extrema by traversing word bits most-significant first with tight lower/upper
constraints and known bits. Choose a feasible 0 or 1 and retain enough state to backtrack or use
dynamic feasibility; return `None` exactly when no word exists. Do not enumerate words in the
implementation. Compute the tnum hull by intersecting the old masks with the interval bit hull
of the computed feasible extrema, and prove that equality against the set definition above.
An independently proved equivalent bit algorithm is permitted. This strengthening is not a
claim that the paper's artifact uses nearest-feasible endpoints.

```coq
Theorem sb_reduce_half_gamma : forall w s h z,
  sb_half_gamma w s (sb_reduce_half w s h) z <-> sb_half_gamma w s h z.
Theorem sb_reduce_half_idempotent : forall w s h,
  sb_reduce_half w s (sb_reduce_half w s h) = sb_reduce_half w s h.
Theorem sb_reduce_half_hulls : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_bit_gamma w s q x) ->
  (forall z, sb_bit_gamma w s (sb_reduce_half w s h) z -> sb_bit_gamma w s q z).
Theorem sb_reduce_half_interval_hull : forall w s h q,
  (forall x, sb_half_gamma w s h x -> sb_interval_gamma w s q x) ->
  (forall z, sb_interval_gamma w s (sb_reduce_half w s h) z ->
    sb_interval_gamma w s q z).
Theorem signed_bounds_reduce_gamma : forall w a z,
  signed_bounds_gamma w (signed_bounds_reduce w a) z <-> signed_bounds_gamma w a z.
Theorem signed_bounds_reduce_idempotent : forall w a,
  signed_bounds_reduce w (signed_bounds_reduce w a) = signed_bounds_reduce w a.
```

The hull claims quantify over arbitrary raw `q` and only words in the indicated hemisphere.
They are stronger than soundness or stability of a particular sequence of exchanges. They do
not state that arbitrary operation transfer results are best abstractions of concrete results.
The raw-input conventions ensure the empty case is covered, including contradictory tnums.

### Lattice, operations and consumers

```coq
Definition signed_bounds_lattice (w : width) : lattice signed_bounds.
Definition signed_bounds_wrank (w : width) :
  bounded_widening_rank (signed_bounds_lattice w).
Definition signed_bounds_domain : word_domain signed_bounds.
Definition signed_bounds_classic_domain : word_domain signed_bounds.
Definition signed_bounds_numeric : numeric_domain (tagged signed_bounds) :=
  tagged_domain signed_bounds_domain.
Definition signed_bounds_capped (maxw : width) :
  numeric_domain (@capped signed_bounds maxw) := capped_domain signed_bounds_domain maxw.

Theorem signed_bounds_laws : forall w, lattice_laws (signed_bounds_lattice w).
Theorem signed_bounds_word_laws : word_laws signed_bounds_domain signed_bounds_gamma.
Theorem signed_bounds_classic_word_laws :
  word_laws signed_bounds_classic_domain signed_bounds_gamma.
Theorem signed_bounds_numeric_laws :
  numeric_laws signed_bounds_numeric (tagged_gamma signed_bounds_gamma).
Theorem signed_bounds_capped_laws : forall maxw,
  numeric_laws (signed_bounds_capped maxw) (capped_gamma signed_bounds_gamma maxw).
```

Every public lattice operation first reduces its raw input. The preorder compares the normalized
bit and interval components for inclusion separately per sign, with empty below all. Bottom has
both halves empty. Join takes the bit-mask join and interval hull per hemisphere, then reduces.
Widen is join; narrow returns its first input reduced. This finite-width widening is sound and
may take exponentially many strict interval-bound improvements in width; it deliberately omits
the paper's faster interval-doubling widening. Provide a decreasing bounded widening rank for
this exact definition, accounting for interval range growth and loss of fixed bits. Do not use
the bare weak lattice laws to infer leastness: prove any component hull or least join directly.
`pmeet` intersects both masks and intervals per sign and reduces. `ptop` has full hemispheres;
`pconst` creates the wrapped singleton in its sign hemisphere.

For forward transfer, split each input into at most two hemisphere branches, apply the landed
`known_bits_precise_domain` and `wrapped_domain` transfers to the corresponding masks and
non-wrapping interval arcs, split each result into its output sign hemispheres, join all
combinations, and reduce. The precise known-bit dictionary uses `tnum_mul_precise` for a
two-operand `bvmul` with both input widths equal to the result width, and otherwise delegates to
`known_bits_domain`. Its backward transfer is the existing DOM-2 transfer. The classic domain
uses `known_bits_domain` for forward transfer and otherwise has the same operations, reduction,
representation and meaning. `signed_bounds_domain`, `signed_bounds_numeric` and
`signed_bounds_capped` select the precise version; clients can use `tagged_domain` or
`capped_domain` with `signed_bounds_classic_domain` for the classic version. Both word-law
theorems hold for all raw inputs. Neither multiplier is required to dominate the other.

A circular output arc can intersect a hemisphere in two pieces; take the enclosing
interval hull of both pieces, rather than assuming their union is a single interval. There are
at most 2^3 combinations for valid Bits arity. The choice of widening and
the selected component transfers are a deliberate Gaulois adaptation; they do not promise the
paper's full tnum-plus operation precision. A result with a `WFull` arc splits to full intervals
in both output signs. For a malformed shape, use a sound fallback satisfying all `word_laws`.
For backward transfer, run each component `passume` on every input-branch combination and each
result branch, then intersect every returned branch with the corresponding original branch,
join all alternatives per operand and reduce. If the shape cannot be safely matched, return
the original operands reduced, preserving the exact list length. This guarantees
length/refinement even where evaluation is None.
The definitions must respect the existing component total zero-division, rotation, shift and
width-changing semantics. No non-emptiness assumption may be inferred from a merely consistent
mask without checking its interval intersection.

For numeric width `w`, DOM-8 multiplication returns bottom on contradictory masks; otherwise it
performs `w` stages, each with at most one scalar shift, tnum addition and join. The classic DOM-2
multiplication uses a constant number of big-integer operations, including its low-zero count.
Both return exact results for two constants, but DOM-8 still executes its width-bounded loop.
These are source-level operation counts, not bit complexity or benchmark results; operand sizes
and the cost of big-integer operations matter. Forward lifting invokes a component transfer for
at most eight branch combinations, with reduction and wrapped-transfer costs additional. Width is
positive, so there is no width-zero case. Malformed arities or widths retain the existing sound
fallback behavior; contradictory masks have empty concretisation.

### Pair-aware queries

Queries consume a whole reduced pair, not one constituent in isolation. They return `None` for
an empty selected sign. Otherwise unsigned bounds are the normalized inclusive endpoints, and
the known-bit answer is the normalized least mask for that half.

```coq
Definition signed_bounds_query (w : width) (a : signed_bounds) (s : bool) :
  option (tnum * Z * Z).
Theorem signed_bounds_query_sound : forall w a s t lo hi z,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) z ->
  tnum_gamma w t z /\ lo <= z <= hi.
Theorem signed_bounds_query_empty : forall w a s,
  signed_bounds_query w a s = None <->
  forall z, ~ sb_half_gamma w s (if s then sb_one a else sb_zero a) z.
Theorem signed_bounds_query_bounds_exact : forall w a s t lo hi,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) lo /\
  sb_half_gamma w s (if s then sb_one a else sb_zero a) hi.
```

For signed endpoints the consumer applies the existing `signed w` to these unsigned endpoints;
within each sign hemisphere the ordering is unchanged. Tagged clients pattern-match `TVal w a`,
and capped clients project the underlying tagged value; `TBot` has no values, while `TAny` has
no width-specific pair to query. No generic API record change is required.
