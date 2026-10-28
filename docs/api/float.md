# Gaulois.Float

The floating-point package, the only one that uses Flocq. It gives finite-float interval domains
over IEEE binary32 and binary64, a NaN-observability analysis, and float operators for the `Ssa`
toy. For example, `[1.0, 2.0]` plus `[1.0, 1.0]` is `[2.0, 3.0]` with no NaN, no zero and no
subnormal; and if no later instruction looks at the payload or the sign of a NaN, two runs that
differ only in NaN payloads behave the same, so a pass may replace one NaN by another.

Floats are not `Bits`: no operator here goes through the operator bridge, and a float operator has
its own soundness theorem. No other package imports `Float`; its card, FLT-1, is part of the build.
It depends on Order (lattices and meanings), Views (`sparse_domain`), Analyses (the demand
framework of ANA-4) and `Examples.Ssa`, which supplies `OExt`, `VF32` and `VF64`.

Conventions of this document:
- **Axioms.** Flocq's operator lemmas rest on Stdlib's classical real numbers, so a theorem of
  `Gaulois.Float` may depend on exactly these axioms and on no others:
  `Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec`,
  `Stdlib.Reals.ClassicalDedekindReals.sig_not_dec`, and
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`, the functional
  extensionality that `Reals` uses. `gaulois check claims` allows exactly this list for
  `Gaulois.Float`
  theorems. A theorem of any other package depends on no axiom.
- **Sections.** FloatInterval.v, FloatOps.v and FloatNan.v each open `Section Float` with
  `Context {prec emax : Z} {Hprec : Prec_gt_0 prec} {Hmax : Prec_lt_emax prec emax}` and
  `Notation fl := (binary_float prec emax)`, and close it at the end of the file. Everything is
  generic in `prec` and `emax`, which are implicit arguments; `@name 24 128` is the binary32
  instance and `@name 53 1024` the binary64 one. Argument conventions follow Flocq: `prec` and
  `emax` are explicit in `is_nan`, `B2R`, `B2FF` and `Bcompare`.
- **The `ext` argument.** Every `Ssa` definition takes `ext : nat -> list cval -> option cval`, the
  evaluation of `OExt tag`, as its first argument; examples.md omits it. In FloatSsa.v every Ssa
  definition is applied to `fx`, which stands for `float_ext nm32 nm64` for two NaN models, so
  every statement there quantifies over `nm32` and `nm64`.

## Files

| File | Contents | Card |
|---|---|---|
| `FloatInterval.v` | float intervals with NaN, signed-zero and subnormal flags; lattice, concretisation, top and widening rank | FLT-1 |
| `FloatOps.v` | NaN models, concrete and abstract operators, comparison refinement, soundness | FLT-1 |
| `FloatNan.v` | NaN observability as a demand domain, backward transfers | FLT-1 |
| `FloatSsa.v` | float operators in the `Ssa` toy, the value domain, the NaN demand view, the instantiation theorems | FLT-1 |

## Definitions

```coq
(* FloatInterval.v. Flocq 4 (From Flocq Require Import IEEE754.Binary). *)
Definition fle (x y : fl) : Prop :=
  match Bcompare prec emax x y with Some Lt | Some Eq => True | _ => False end.
(* The smallest normal number is 2^(2 - emax), 2^-1022 for binary64; a finite nonzero number of
   smaller magnitude is subnormal. *)
Definition subnormal (x : fl) : Prop :=
  is_finite prec emax x = true /\ B2R prec emax x <> 0%R /\
  (Rabs (B2R prec emax x) < bpow radix2 (2 - emax))%R.
Definition fl_nn : Type := {x : fl | is_nan prec emax x = false}.   (* a float that is not a NaN *)
Record fl_interval : Type := FlInterval {
  flo : fl_nn;               (* lower bound of the non-NaN, nonzero values; may be -inf *)
  fhi : fl_nn;               (* upper bound; may be +inf *)
  may_nan : bool;
  may_neg_zero : bool;
  may_pos_zero : bool;
  may_subnormal : bool       (* a nonzero subnormal may occur *)
}.
Definition fl_gamma (I : fl_interval) (x : fl) : Prop :=
  match B2FF prec emax x with
  | F754_nan _ _ => may_nan I = true
  | F754_zero s => (if s then may_neg_zero I else may_pos_zero I) = true
  | _ => fle (proj1_sig (flo I)) x /\ fle x (proj1_sig (fhi I)) /\
         (subnormal x -> may_subnormal I = true)
  end.
Definition fl_lattice : lattice fl_interval.
(* leb I J: every flag of I is a flag of J, and either I has no nonzero non-NaN value (flo I above
   fhi I) or its bounds lie within those of J; bot: flo = +inf, fhi = -inf, no flag; join: the
   smaller lower and the larger upper bound (an empty operand contributes none), flags or-ed;
   widen a b: a bound of b outside the bounds of a goes to infinity, flags or-ed; narrow a b: an
   infinite bound of a is replaced by that of b, the flags of a are kept *)
Definition fl_concretisation : concretisation fl_interval fl := Concretisation fl_gamma.
Definition fl_top : fl_interval.      (* flo = -inf, fhi = +inf, every flag set *)
Definition fl_top_lattice : top fl_lattice.      (* top_value = fl_top *)
Definition fl_widening_rank : bounded_widening_rank fl_lattice.
(* wrank I = (1 if flo I is not -inf) + (1 if fhi I is not +inf) + the number of flags of I that are
   false; wbound = 6. A widening step moves a bound to infinity or sets a flag. *)
```

```coq
(* FloatOps.v. Rounding is to nearest even. A NaN has a sign and a payload, and hardware decides
   which of an operation's NaN operands supplies them; that choice is a parameter. *)
Inductive farith : Type := FAdd | FSub | FMul | FDiv.       (* operators with a float result *)
Inductive fbop : Type := FArith (o : farith) | FLt.         (* FLt: x < y, integer result 1 or 0 *)
Record nan_model : Type := NanModel {
  nan_choice : farith -> fl -> fl -> fl;
  nan_choice_nan : forall o x y, is_nan prec emax (nan_choice o x y) = true;
  nan_choice_local : forall o x y x' y',
    is_nan prec emax x = is_nan prec emax x' -> is_nan prec emax y = is_nan prec emax y' ->
    (is_nan prec emax x = true -> B2FF prec emax x = B2FF prec emax x') ->
    (is_nan prec emax y = true -> B2FF prec emax y = B2FF prec emax y') ->
    nan_choice o x y = nan_choice o x' y';
  nan_neg : fl -> fl;
  nan_neg_nan : forall x, is_nan prec emax (nan_neg x) = true;
  nan_abs : fl -> fl;
  nan_abs_nan : forall x, is_nan prec emax (nan_abs x) = true
}.
(* The model whose every answer is the quiet NaN of payload 2^(prec - 2) and sign false. It makes
   the record inhabited, so no theorem about models is vacuous. A hardware model (the first NaN
   operand, quieted, on x86; the default NaN on Arm) is a client's definition with its own proof
   of the one law. *)
Definition default_nan_model (Hp : (2 <= prec)%Z) : nan_model.
Definition fl_eval_bin (nm : nan_model) (o : farith) (x y : fl) : fl.
(* Flocq's Bplus, Bminus, Bmult and Bdiv with mode_NE and, as the NaN choice,
   fun x y => exist _ (nan_choice nm o x y) (nan_choice_nan nm o x y) *)
Definition fl_eval_neg (nm : nan_model) (x : fl) : fl.
(* Flocq's Bopp with the NaN choice fun x => exist _ (nan_neg nm x) (nan_neg_nan nm x) *)
Definition fl_eval_abs (nm : nan_model) (x : fl) : fl.          (* Babs likewise, with nan_abs *)
Definition fl_lt (x y : fl) : bool :=
  match Bcompare prec emax x y with Some Lt => true | _ => false end.
Definition fl_bin (o : farith) (I J : fl_interval) : fl_interval.
(* interval arithmetic with outward rounding of the bounds (Flocq's mode_DN for the lower bound,
   mode_UP for the upper); may_nan when an operand may be NaN or an invalid operation is possible:
   inf - inf (inf + -inf), 0 * inf, 0 / 0 or inf / inf; zero flags by the signs of the bounds and
   the possibility of underflow to zero; may_subnormal when the nonzero result range reaches
   below the smallest normal number, bpow radix2 (2 - emax), in magnitude *)
Definition fl_neg (I : fl_interval) : fl_interval.      (* swaps the bounds and the zero flags *)
Definition fl_abs (I : fl_interval) : fl_interval.
Definition fl_assume_lt (I J : fl_interval) : fl_interval * fl_interval.
(* refine both operands under the assumption x < y, which is false when either is NaN: the upper
   bound of x is at most that of y, the lower bound of y at least that of x, neither may be NaN *)
```

```coq
(* FloatNan.v. Demand: not demanded at all, or demanded with the NaN sign and payload observed or
   not. A non-NaN value is always demanded exactly. *)
Inductive nan_demand : Type := NotDemanded | Demanded (sign payload : bool).
Definition ff_agree (sg pl : bool) (a b : full_float) : Prop :=
  match a, b with
  | F754_nan s1 p1, F754_nan s2 p2 => (sg = true -> s1 = s2) /\ (pl = true -> p1 = p2)
  | F754_nan _ _, _ => False
  | _, F754_nan _ _ => False
  | _, _ => a = b
  end.
Definition nan_agree (d : nan_demand) (x y : fl) : Prop :=
  match d with
  | NotDemanded => True
  | Demanded sg pl => ff_agree sg pl (B2FF prec emax x) (B2FF prec emax y)
  end.
Definition nan_domain : demand_domain nan_demand fl.
(* dlat: NotDemanded below Demanded false false below the two single-bit demands below
   Demanded true true; join is the least upper bound, widen = join, narrow a _ = a;
   dagree := Agreement nan_agree *)
Definition nan_back (o : fbop) (d : nan_demand) : nan_demand * nan_demand.
(* The demands on the two operands given the demand d on the result.
   NotDemanded gives (NotDemanded, NotDemanded). For a float result (FArith _): a demand of the
   sign or of the payload, Demanded true _ or Demanded _ true, gives Demanded true true on both
   operands, because the choice between two NaN operands depends on both of their signs and
   payloads; Demanded false false gives Demanded false false on both. For FLt the result is an
   integer, demanded exactly, and any demand gives Demanded false false on both: a comparison sees
   whether an operand is NaN and nothing else about it. *)
```

```coq
(* FloatSsa.v. The Ssa toy is Flocq-free: it carries float bit patterns (VF32 and VF64) and one
   extension operator (OExt tag), evaluated by the `ext` argument of every Ssa definition. This file
   supplies `ext` and the analyses over it. *)
Inductive fw : Type := F32 | F64.
Definition float_ext_tag (w : fw) (o : fbop) : nat.
(* 2 * i + (0 for F32, 1 for F64), where i numbers FAdd, FSub, FMul, FDiv and FLt from 0 to 4 *)
Definition float_ext_decode (tag : nat) : option (fw * fbop).   (* the inverse; None from 10 on *)
Definition float_ext (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024) :
  nat -> list cval -> option cval.
(* float_ext_decode tag gives (w, o), or the result is None. For w = F32 and the arguments
   [VF32 a; VF32 b] with a and b in [0, 2^32): for o = FArith o', VF32 (bits_of_b32 (fl_eval_bin nm32
   o' (b32_of_bits a) (b32_of_bits b))); for o = FLt, VInt W32 1 when fl_lt holds of the decoded
   operands and VInt W32 0 otherwise. F64 likewise with VF64, b64_of_bits, bits_of_b64 and nm64. A
   different arity or width, or an out-of-range pattern, gives None, and the toy traps. *)
Definition float_ext_sigs : list (nat * (list ty * ty)).
(* For each width, the four arithmetic tags take two operands of that width and return that
   width; the comparison tag takes two operands of that width and returns TyI32. *)

(* Facts about Ssa values: nothing, a binary32 interval, a binary64 interval, or any value. *)
Inductive fl_any : Type :=
  | FlBot
  | FlA32 (I : @fl_interval 24 128)
  | FlA64 (I : @fl_interval 53 1024)
  | FlOther.
Definition fl_any_lattice : lattice fl_any.
(* FlBot below everything; FlA32 I <= FlA32 J and FlA64 I <= FlA64 J as in fl_lattice, the two widths
   incomparable; everything below FlOther; the join of facts of two widths is FlOther; widen and
   narrow act within a width, and widening across widths gives FlOther *)
Definition fl_any_concretisation : concretisation fl_any cval.
(* FlBot contains nothing; FlA32 I contains VF32 b when 0 <= b < 2^32 and fl_gamma I (b32_of_bits b);
   FlA64 I contains VF64 b likewise with 2^64; FlOther contains every value *)
Definition fl_any_top : top fl_any_lattice.                (* FlOther *)
Definition fl_any_widening_rank : bounded_widening_rank fl_any_lattice.
(* wrank FlBot = 8; wrank (FlA32 I) = 1 + the rank of I, likewise FlA64; wrank FlOther = 0;
   wbound = 8 *)
Definition float_ssa_domain : sparse_domain fl_any cval sop.
(* fact_lat = fl_any_lattice, fact_conc = fl_any_concretisation, top_fact = FlOther;
   op_abs (OExt tag) [FlA32 I; FlA32 J] = FlA32 (fl_bin o' I J) when float_ext_decode tag =
   Some (F32, FArith o'), likewise FlA64 for F64; every other operator or fact gives FlOther;
   assume_value _ a = a; assume_args (OExt tag) true [FlA32 I; FlA32 J] = [FlA32 I'; FlA32 J']
   with (I', J') = fl_assume_lt I J when float_ext_decode tag = Some (F32, FLt), likewise for F64,
   and assume_args _ _ fs = fs otherwise *)
Definition float_problem (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024)
    (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any) :
  sparse_problem astate event label ssa_edge vid sop cval fl_any :=
  SparseProblem (ssa_block_view (float_ext nm32 nm64) P f) float_ssa_domain vals entry.

Definition nan_domain_ssa : demand_domain nan_demand cval.
(* dlat as in nan_domain; dagree d u v is True for NotDemanded; for a demand, nan_agree d of the
   decoded floats when u and v are both VF32 in range or both VF64 in range, and u = v otherwise:
   integers, pointers and functions agree exactly, and a float and a non-float never agree *)
Definition ssa_nan_demand_view (ext : nat -> list cval -> option cval) (P : program) (f : func) :
  demand_view astate event (label * nat) ssa_edge vid cval nan_demand.
(* dgraph, ddefs and dlookup are those of ssa_demand_view ext P f.
   dnec e: every operand that ssa_demand_view marks needed at e (the operands of an output, a
   branch, a switch, a call, a return, a store, a free and a possibly trapping instruction), with
   the demand Demanded true true, since their bit patterns are observable or steer control; and
   the operands of an IOp with OExt, which may trap on the shape of its operands, with
   Demanded false false. dexit n likewise, with Demanded true true.
   dback e x d, for def x = Op o args in ssa_block_view ext P f: for o = OExt tag with
   float_ext_decode tag = Some (_, b) and args = [a1; a2], the pairs (a1, d1) and (a2, d2) with
   (d1, d2) = nan_back b d; for every other operator, the arguments with Demanded true true when d
   is not NotDemanded and nothing otherwise; for a Param or an Arbitrary definition, nothing *)
```

## Theorems

```coq
(** The interval lattice satisfies the lattice laws, and its concretisation is monotone. *)
Theorem fl_lattice_laws :
  lattice_laws fl_lattice /\ concretisation_laws fl_lattice fl_concretisation.
(** Every float is in the top element, and nothing is in the bottom. *)
Theorem fl_top_sound (x : fl) : fl_gamma fl_top x.
Theorem fl_bot_empty (x : fl) : ~ fl_gamma (bot fl_lattice) x.
(** The subnormal threshold is the smallest normal number, so the predicate is neither empty nor
    everything: the smallest positive float is subnormal, and one is not. *)
Theorem subnormal_proper (Hp : (2 <= prec)%Z) :
  (exists x : fl, subnormal x) /\ (exists y : fl, B2R prec emax y = 1%R /\ ~ subnormal y).
```
Proof idea: unfold `fl_gamma` by the shape of `B2FF`; the order on bounds is `Bcompare`, which is
a total preorder on non-NaN floats (Flocq's `Bcompare_correct`); the interval lattice's laws are
case analyses on the flags and on the ordering of the bounds, an empty interval being below
everything. The smallest positive float is `B754_finite false 1 emin`, of magnitude
`2^(3 - emax - prec)`, which is below `2^(2 - emax)` because `prec >= 2`; the float `1` has
magnitude
at least `2^(2 - emax)` because `emax > prec >= 2`. Card: FLT-1.

```coq
(** Each abstract operator contains the float result, for every NaN model. *)
Theorem fl_bin_sound (nm : nan_model) (o : farith) (I J : fl_interval) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> fl_gamma (fl_bin o I J) (fl_eval_bin nm o x y).
Theorem fl_neg_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_neg I) (fl_eval_neg nm x).
Theorem fl_abs_sound (nm : nan_model) (I : fl_interval) (x : fl) :
  fl_gamma I x -> fl_gamma (fl_abs I) (fl_eval_abs nm x).
(** Comparison refinement keeps both operands that satisfy the comparison. *)
Theorem fl_assume_lt_sound (I J : fl_interval) (x y : fl) :
  fl_gamma I x -> fl_gamma J y -> Bcompare prec emax x y = Some Lt ->
  fl_gamma (fst (fl_assume_lt I J)) x /\ fl_gamma (snd (fl_assume_lt I J)) y.
```
Proof idea: Flocq's correctness of the operators (`Bplus_correct` and its siblings) gives the exact
rounded real result of finite operands, with the overflow and special cases as separate lemmas;
monotonicity of rounding bounds the result between the directed roundings of the exact bounds; the
flags handle NaN (an operand NaN, or an invalid operation, whatever `nan_choice` returns), zero
signs, underflow and subnormals. Negation and absolute value are exact except on NaN, where the
flag covers the model's answer. `Bcompare x y = Some Lt` excludes NaN operands. Card: FLT-1.

```coq
(** The demand lattice satisfies the lattice laws. *)
Theorem nan_lattice_laws : lattice_laws (dlat nan_domain).
(** NaN agreement is an agreement: reflexive, antitone in the demand, symmetric, and trivial at
    NotDemanded. *)
Theorem nan_domain_laws :
  agreement_laws (dlat nan_domain) (dagree nan_domain) /\
  agreement_symmetric (dagree nan_domain) /\
  (forall u v, agree (dagree nan_domain) (bot (dlat nan_domain)) u v).
(** NaN observability is sound for the arithmetic operators: if the operands agree on the demands
    that `nan_back` computes, the results agree on the demand on the result. *)
Theorem nan_back_sound (nm : nan_model) (o : farith) (d : nan_demand) (x y x' y' : fl) :
  nan_agree (fst (nan_back (FArith o) d)) x x' -> nan_agree (snd (nan_back (FArith o) d)) y y' ->
  nan_agree d (fl_eval_bin nm o x y) (fl_eval_bin nm o x' y').
(** A comparison sees whether an operand is NaN and nothing else about it. *)
Theorem fl_lt_agrees (x y x' y' : fl) :
  nan_agree (Demanded false false) x x' -> nan_agree (Demanded false false) y y' ->
  fl_lt x y = fl_lt x' y'.
```
Proof idea: `nan_lattice_laws` and `nan_domain_laws` by cases on the five demands and the shape of
`B2FF`. For `nan_back_sound`: a demand of the sign or the payload makes both operands agree fully,
so non-NaN operands are equal (`B2FF` is injective up to proof irrelevance) and NaN operands have
the same sign and payload, and `nan_choice_local` makes the choice, and so the result, identical,
the NaN produced from non-NaN operands (inf - inf) included; the demand `Demanded false false`
needs only that NaN-ness and the non-NaN values agree, from which the NaN-ness of the result and,
when it is not NaN, the result follow. For `fl_lt_agrees`, `Bcompare` is `None` when an operand is
NaN and depends only on the values otherwise. Card: FLT-1.

```coq
Section FloatSsaTheorems.
Context (nm32 : @nan_model 24 128) (nm64 : @nan_model 53 1024).
Local Notation fx := (float_ext nm32 nm64).

Theorem float_ext_respects (P : program) :
  ext_sigs P = float_ext_sigs -> ext_respects fx P.
(** The result type follows by decoding each tag and inspecting its operands. Card: FLT-1. *)

(** The operator numbering is injective: decoding inverts the tag, and a tag that decodes is the
    tag of what it decodes to. *)
Theorem float_ext_tag_decode (w : fw) (o : fbop) :
  float_ext_decode (float_ext_tag w o) = Some (w, o).
Theorem float_ext_decode_tag (tag : nat) (w : fw) (o : fbop) :
  float_ext_decode tag = Some (w, o) -> float_ext_tag w o = tag.
(** The Ssa NaN agreement is a lattice with an agreement, like the one on floats. *)
Theorem nan_domain_ssa_laws :
  lattice_laws (dlat nan_domain_ssa) /\
  agreement_laws (dlat nan_domain_ssa) (dagree nan_domain_ssa) /\
  agreement_symmetric (dagree nan_domain_ssa) /\
  (forall u v, agree (dagree nan_domain_ssa) (bot (dlat nan_domain_ssa)) u v).
(** The float value domain has the laws that VIEW-4 needs, for every truth function that reads a
    nonzero integer as true. *)
Theorem float_ssa_domain_laws (truth : cval -> bool) :
  (forall w z, truth (VInt w z) = negb (Z.eqb z 0)) ->
  sparse_domain_laws float_ssa_domain truth (op_eval fx).
```
Proof idea: the numbering is a case analysis on `w` and the five operators. `nan_domain_ssa_laws` is
`nan_lattice_laws` and `nan_domain_laws` read through the decoding, with exact equality outside
floats. For `float_ssa_domain_laws`: `fl_lattice_laws` and the lattice of facts give
`dom_lattice` and `dom_conc`; `fact_bot_empty` and `top_sound` are the cases `FlBot` and `FlOther`;
`op_sound` is `fl_bin_sound` composed with the round trip of `b32_of_bits` and `bits_of_b32`
(`bits_of_binary_float_of_bits` on an in-range pattern, and `fx` returns in-range patterns);
`assume_args_sound` for `FLt` and `true` is `fl_assume_lt_sound`, the result `VInt W32 1` meaning
that `fl_lt` holds, and every other case is the identity. Card: FLT-1.

```coq
(** Float value analysis is sound on Ssa: every float value defined in a reachable activation
    lies in the interval of its fact. *)
Theorem ssa_float_value_sound (P : program) (f : func) (vals : list vid) (entry : vid -> fl_any)
    (sigma : sparse_unknown label ssa_edge vid -> lift_bot fl_any) :
  wf_program P ->
  (forall s x c, reachable_state (activation fx P f) s ->
     val (ssa_block_view fx P f) s x = Some c -> In x vals) ->
  (forall s x c, initial (activation fx P f) s -> val (ssa_block_view fx P f) s x = Some c ->
     exists b i, def (ssa_block_view fx P f) x = Param b i /\
       In b (Graph.entries (cfg (base (ssa_block_view fx P f)))) /\
       gamma fl_any_concretisation (entry x) c) ->
  post_solution (lift_bot_lattice fl_any_lattice)
    (sparse_system (float_problem nm32 nm64 P f vals entry)) sigma ->
  forall s x c, reachable_state (activation fx P f) s ->
    val (ssa_block_view fx P f) s x = Some c ->
    gamma (lift_bot_gamma fl_any_concretisation) (sigma (UVal x)) c.
(** The NaN demand view of Ssa satisfies the laws of the demand framework. *)
Theorem ssa_nan_demand_view_laws (P : program) (f : func) :
  wf_program P ->
  demand_laws (activation fx P f) (activation_endings fx P f)
    (reachable_state (activation fx P f)) var_encoding nan_domain_ssa
    (ssa_nan_demand_view fx P f).
(** NaN observability on Ssa: two activation states that differ only in the payload and sign of
    NaNs that nothing observes behave the same. *)
Theorem ssa_nan_demand_sound (P : program) (f : func)
    (sigma : (label * nat) -> Map.t vid nan_demand) (s0 t0 : astate) :
  wf_program P ->
  post_solution (pointwise_lattice var_encoding (dlat nan_domain_ssa))
    (demand_system var_encoding nan_domain_ssa (ssa_nan_demand_view fx P f)) sigma ->
  initial (activation fx P f) s0 -> initial (activation fx P f) t0 ->
  point (dgraph (ssa_nan_demand_view fx P f)) t0 = point (dgraph (ssa_nan_demand_view fx P f)) s0 ->
  agree (demand_agreement var_encoding nan_domain_ssa (dlookup (ssa_nan_demand_view fx P f)))
    (sigma (point (dgraph (ssa_nan_demand_view fx P f)) s0)) s0 t0 ->
  same_behaviour (activation fx P f) (activation_endings fx P f) s0
    (activation fx P f) (activation_endings fx P f) t0.
End FloatSsaTheorems.
```
Proof idea: the first is `sparse_sound` for `float_problem`, with `ssa_block_view_laws` from EX-5a,
`float_ssa_domain_laws` (the view's `truth` is `ssa_truth_nonzero`) and `fl_bin_sound` inside; the
second checks the laws of the demand framework for the toy as for neededness, the per-operator
step being `nan_back_sound` for the float operators and `fl_lt_agrees` for the comparison, the
trap shape being fixed by the demand `Demanded false false` on the operands of `OExt`, and the rest
being exact; the third is `demand_sound` with `ssa_nan_demand_view_laws` and `reachable_invariant`.
Card: FLT-1.

## Algorithms and references

- IEEE 754-2019 for the operations and for the NaN payload and sign model; Flocq 4 (Boldo and
  Melquiond, "Flocq: a unified library for proving floating-point algorithms in Coq", 2011) for
  `binary_float`, `Bcompare`, `Bplus`, `B2FF`, the bit conversions `b32_of_bits` and `bits_of_b32`
  and the correctness lemmas of the operators. The NaN choice is the argument that Flocq's
  operations take for exactly this purpose; `nan_choice_local` is the one property that real
  hardware satisfies and the analysis needs.
- Float intervals with explicit NaN and signed-zero flags follow the treatment of floating-point in
  abstract interpreters (Miné, "Relational abstract domains for the detection of floating-point
  run-time errors", 2004); the NaN-observability demand is the shape of demanded bits with one
  bit pattern per NaN. The widening that sends a moving bound to infinity is that of the classical
  interval domain (Cousot and Cousot, 1977).

## Performance notes

- Every abstract operator is a constant number of Flocq operations on `binary_float` values, with
  directed rounding for the bounds; nothing loops over a list, and joins, widenings and
  comparisons are O(1).
- A bound is a sigma value `{x | is_nan x = false}`; the proof is erased by extraction, so a bound
  is the float itself. A fact of `fl_any` holds at most two bounds and four flags.
- `float_ext` decodes and encodes bit patterns with `b32_of_bits` and `bits_of_b32`, O(1) in the
  width, and the tag numbering is arithmetic.
- `fl_widening_rank` and `fl_any_widening_rank` have bounds 6 and 8, so `solve_total` with
  widening needs no fuel; the NaN demand is a five-point lattice of height 3 and `nan_agree` is
  O(1).

## Open questions

1. **Flocq conventions.** The arity of Flocq's operators (which of `prec`, `emax` and the proofs
   `Prec_gt_0` and `Prec_lt_emax` are explicit, and the shape of the NaN-choice argument) follows
   the
   installed Flocq 4.2.2; the card adapts the signatures, not the statements.
2. **Axiom names.** `Print Assumptions` on Flocq's operator lemmas at the pinned versions fixes the
   exact names of the axioms of the classical reals. The list in the conventions is the allowance;
   a theorem that depends on fewer is fine.
3. **Operators not covered.** Conversions between integers and floats, `sqrt`, fused multiply-add
   and `min` and `max` have no operator or theorem here; a client that needs them extends `fbop`
   and every theorem that cases on it.

## Requests to other documents

1. **Examples (EX-5a).** `ssa_truth_nonzero`:
   `forall ext P f w z, truth (ssa_block_view ext P f) (VInt w z) = negb (Z.eqb z 0)`. Why:
   `float_ssa_domain_laws` needs the view's `truth` to read a nonzero integer as true, and
   `ssa_float_value_sound` instantiates it.
