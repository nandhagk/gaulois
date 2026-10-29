# Gaulois.Order

Order provides the vocabulary of abstract values: a `lattice` record (comparison, bottom, join,
widening, narrowing), separate `Prop` records for its laws, evidence that ascending chains stop
(`height`, `widening_rank`), the two ways a value can mean something (`gamma`, forward;
`agree`, backward), and combinators that build new lattices with their laws and meanings from
old ones. For example, constants with an unreachable bottom, paired with a liveness flag:

```coq
Definition L : lattice (option (flat Z) * bool) :=
  product_lattice (option_lattice (flat_lattice Z.eqb)) bool_lattice.
(* join (Some (FVal 1), false) (Some (FVal 2), true) = (Some FTop, true) *)
```

Conventions of this document. Statements sit in `Section`s whose `Context` and `Variables` lines
declare what they mention, and a `(* Proof idea ... Card ... *)` line follows each group of
theorems. Record projections take their parameters implicitly (`Arguments leb {A}`), so `leb L a b`
type-checks as in the anchors. Stdlib imports (`ZArith`, `List`, `Bool`,
`Relations.Relation_Definitions`) are implicit. Every law is a premise of the theorem that needs it;
no combinator assumes `lattice_laws` of its arguments silently.

Collections' set module is `FinSet`. The laws of the powerset, must and pointwise lattices over raw
tries are proved through the position-level API of Collections (`FinSet.subset_code`,
`FinSet.union_code`, `Map.code_get_combine`, `Map.code_get_union_with`, `Map.forall2_spec`) and
quantify over every trie, well formed or not: none of those theorems takes `Map.wf` as a premise. A
carrier that must be well formed is a sigma type (`finite_set`, `finite_map`) whose proof component
is a `Prop`. Such a carrier has no boolean equality, so nothing in this package instantiates
`flat_lattice`, `Trie.beq` or `Map.beq` at a `finite_set` or a `finite_map`. Engines consume
`height` and `widening_rank` only inside `inhabited` (Fixpoint's `terminates`), so `rank`, `bound`
and `wrank`, which sum over the universe list, are never computed with.

## Files

| File | Contents | Card |
|---|---|---|
| `OrderLattice.v` | `lattice`, `lattice_laws`, `lub_laws`, `meet_laws`, `top`, `height`, `monotone_height`, `widening_rank`, `bounded_widening_rank` | ORD-1 |
| `OrderConcrete.v` | `concretisation`, `agreement`, their laws and extra laws, `order_embedding`, `comap_gamma`, `comap_agree`, join, widen and narrow transport | ORD-1 |
| `OrderMonotone.v` | `fun_leb`, `monotone_fun`, `monotone_fun2`, `monotone_on_assignments` and their closure theorems | ORD-1 |
| `OrderFlat.v` | `flat`: `FBot \| FVal \| FTop`, `flat_agree` | ORD-1 |
| `OrderLift.v` | `option_lattice` (also `lift_bot`), `lift_top`, `lift_top_agree` | ORD-1 |
| `OrderProduct.v` | `product_lattice`, `monotone_fst`, `monotone_snd`, `monotone_pair` | ORD-1 |
| `OrderReduced.v` | `reduced_lattice` with `reduce` | ORD-1 |
| `OrderDual.v` | `dual_lattice` | ORD-1 |
| `OrderBasic.v` | `bool_lattice`, `unit_lattice` | ORD-1 |
| `OrderPowerset.v` | `powerset_lattice`, `must_lattice`, finite-universe carriers, `finite_clamp` | ORD-2 |
| `OrderPointwise.v` | `pointwise_lattice`, `pointwise_top_lattice`, finite maps, `finite_map_clamp` | ORD-2 |
| `OrderDisjunction.v` | `disjunction_lattice`, `monotone_join_all` | ORD-2 |

## Definitions

### Core records (`OrderLattice.v`)

```coq
Record lattice (A : Type) : Type := Lattice {
  leb : A -> A -> bool;
  bot : A;
  join : A -> A -> A;
  widen : A -> A -> A;          (* join when a domain has no widening *)
  narrow : A -> A -> A          (* fun a _ => a when a domain has no narrowing *)
}.
Record lattice_laws {A} (L : lattice A) : Prop := {
  leb_refl : forall a, leb L a a = true;
  leb_trans : forall a b c, leb L a b = true -> leb L b c = true -> leb L a c = true;
  bot_least : forall a, leb L (bot L) a = true;
  join_upper_l : forall a b, leb L a (join L a b) = true;
  join_upper_r : forall a b, leb L b (join L a b) = true;
  widen_upper_l : forall a b, leb L a (widen L a b) = true;
  widen_upper_r : forall a b, leb L b (widen L a b) = true;
  narrow_lower : forall a b, leb L b a = true -> leb L (narrow L a b) a = true;
  narrow_upper : forall a b, leb L b a = true -> leb L b (narrow L a b) = true
}.
(* The strong law, needed only for least-solution theorems. *)
Record lub_laws {A} (L : lattice A) : Prop := {
  join_least : forall a b c, leb L a c = true -> leb L b c = true -> leb L (join L a b) c = true
}.
Record top {A} (L : lattice A) : Type := Top {
  top_value : A;
  top_greatest : forall a, leb L a top_value = true
}.
Record height {A} (L : lattice A) : Type := Height {
  rank : A -> nat;
  bound : nat;
  rank_bounded : forall a, rank a <= bound;
  join_rank_grows : forall a b, leb L (join L a b) a = false -> rank a < rank (join L a b)
}.
Record widening_rank {A} (L : lattice A) : Type := WideningRank {
  wrank : A -> nat;
  widen_rank_stable : forall a b, leb L b a = true -> wrank (widen L a b) <= wrank a;
  widen_rank_progress : forall a b, leb L b a = false -> wrank (widen L a b) < wrank a
}.
```

Additions:

```coq
Definition eqb_spec {A} (eqb : A -> A -> bool) : Prop := forall a b, eqb a b = true <-> a = b.
Definition equivalent {A} (L : lattice A) (a b : A) : Prop := leb L a b = true /\ leb L b a = true.

(* A greatest lower bound; needed to build a dual. *)
Record meet_laws {A} (L : lattice A) (meet : A -> A -> A) : Prop := {
  meet_lower_l : forall a b, leb L (meet a b) a = true;
  meet_lower_r : forall a b, leb L (meet a b) b = true;
  meet_greatest : forall a b c, leb L c a = true -> leb L c b = true -> leb L c (meet a b) = true
}.

(* A height whose rank never decreases upward; products and maps need it. *)
Record monotone_height {A} (L : lattice A) : Type := MonotoneHeight {
  base_height : height L;
  rank_monotone : forall a b, leb L a b = true -> rank base_height a <= rank base_height b
}.

(* A widening rank with a uniform bound; lifting and sums of ranks need it. *)
Record bounded_widening_rank {A} (L : lattice A) : Type := BoundedWideningRank {
  base_wrank : widening_rank L;
  wbound : nat;
  wrank_bounded : forall a, wrank base_wrank a <= wbound
}.
```

### Meanings (`OrderConcrete.v`)

```coq
Record concretisation (A C : Type) : Type := Concretisation { gamma : A -> C -> Prop }.   (* forward *)
Record concretisation_laws {A C} (L : lattice A) (G : concretisation A C) : Prop := {
  gamma_monotone : forall a b c, leb L a b = true -> gamma G a c -> gamma G b c
}.
Record agreement (A C : Type) : Type := Agreement { agree : A -> C -> C -> Prop }.        (* backward *)
Record agreement_laws {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_refl : forall a c, agree R a c c;
  agree_antitone : forall a b x y, leb L a b = true -> agree R b x y -> agree R a x y
}.
```

Additions, each a separate `Prop` record so that a domain claims only what it satisfies:

```coq
(* the bottom denotes no concrete value *)
Record bottom_empty {A C} (L : lattice A) (G : concretisation A C) : Prop := {
  gamma_bot_empty : forall c, ~ gamma G (bot L) c
}.
(* a top denotes every concrete value *)
Record top_full {A C} {L : lattice A} (T : top L) (G : concretisation A C) : Prop := {
  gamma_top_full : forall c, gamma G (top_value T) c
}.
(* agreement is an equivalence on each element's needs *)
Record agreement_equivalence {A C} (R : agreement A C) : Prop := {
  agree_sym : forall a x y, agree R a x y -> agree R a y x;
  agree_trans : forall a x y z, agree R a x y -> agree R a y z -> agree R a x z
}.
(* needing nothing agrees on everything *)
Record agreement_bot {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_bot : forall x y, agree R (bot L) x y
}.
(* the needs of a join are the union of the needs *)
Record agreement_join_law {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_join : forall a b x y, agree R a x y -> agree R b x y -> agree R (join L a b) x y
}.

(* a pullback of a meaning along an embedding of carriers; the finite_* carriers use it at proj1_sig *)
Definition order_embedding {A B} (LA : lattice A) (LB : lattice B) (f : B -> A) : Prop :=
  forall b1 b2, leb LB b1 b2 = leb LA (f b1) (f b2).
Definition comap_gamma {A B C} (f : B -> A) (G : concretisation A C) : concretisation B C.
(* gamma b c = gamma G (f b) c *)
Definition comap_agree {A B C} (f : B -> A) (R : agreement A C) : agreement B C.
(* agree b x y = agree R (f b) x y *)
```

### Monotone functions (`OrderMonotone.v`)

```coq
Definition fun_leb {X A} (L : lattice A) (s1 s2 : X -> A) : Prop :=
  forall x, leb L (s1 x) (s2 x) = true.
Definition monotone_fun {A B} (L1 : lattice A) (L2 : lattice B) (f : A -> B) : Prop :=
  forall a b, leb L1 a b = true -> leb L2 (f a) (f b) = true.
Definition monotone_fun2 {A B C} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C)
  (f : A -> B -> C) : Prop :=
  forall a1 a2 b1 b2, leb L1 a1 a2 = true -> leb L2 b1 b2 = true ->
  leb L3 (f a1 b1) (f a2 b2) = true.
Definition monotone_on_assignments {X A B} (L1 : lattice A) (L2 : lattice B) (f : (X -> A) -> B) : Prop :=
  forall s1 s2, fun_leb L1 s1 s2 -> leb L2 (f s1) (f s2) = true.
```

### Combinators

Each combinator below defines a `lattice`, and the theorems of the next section state its laws.
Where a combinator has no widening, `widen` is `join` and `narrow a _` is `a`.

**Flat** (`OrderFlat.v`). Constructors are `FBot`, `FVal` and `FTop`, because `Top` is the
constructor of the record `top`.

```coq
Inductive flat (A : Type) : Type :=
  | FBot
  | FVal (a : A)
  | FTop.
Definition flat_lattice {A} (eqb : A -> A -> bool) : lattice (flat A).
(* leb: FBot <= anything; FVal a <= FVal b iff eqb a b; anything <= FTop; otherwise false.
   join: FBot neutral; FVal a, FVal b -> FVal a if eqb a b, else FTop; FTop absorbs. *)
Definition flat_top {A} (eqb : A -> A -> bool) : top (flat_lattice eqb).     (* FTop *)
Definition flat_height {A} (eqb : A -> A -> bool) (Hspec : eqb_spec eqb) :
  monotone_height (flat_lattice eqb).                                     (* rank 0, 1, 2; bound 2 *)
Definition flat_gamma {A C} (G : A -> C -> Prop) : concretisation (flat A) C.
(* FBot: nothing; FVal a: G a; FTop: everything *)
Definition flat_agree {A C} (R : A -> C -> C -> Prop) : agreement (flat A) C.
(* FBot: every pair agrees; FVal a: R a; FTop: only equal values agree *)
```

**Lifting** (`OrderLift.v`). `lift_bot A` is `option A`: `Unreached` (`None`) is a fresh bottom
meaning "unreachable", and `Reached a` (`Some a`) is ordered as `a`. `lift_bot_lattice`,
`lift_bot_gamma` and `lift_bot_agree` are the names of `option_lattice`, `option_gamma` and
`option_agree`. `lift_top` adds a fresh top.

```coq
Definition option_lattice {A} (L : lattice A) : lattice (option A).
(* leb None _ = true; leb (Some _) None = false; leb (Some a) (Some b) = leb L a b; bot = None;
   join/widen: None neutral, Some a, Some b -> Some (join L a b) (resp. widen);
   narrow (Some a) (Some b) = Some (narrow L a b); narrow a None = a; narrow None b = None *)
Definition lift_bot (A : Type) : Type := option A.
Notation Unreached := None.
Notation Reached := Some.
Notation lift_bot_lattice := option_lattice.
Definition option_top {A} {L : lattice A} (T : top L) : top (option_lattice L).     (* Some top *)
Definition option_height {A} {L : lattice A} (laws : lattice_laws L) (H : monotone_height L) :
  monotone_height (option_lattice L).
(* rank None = 0, rank (Some a) = S (rank a); bound S *)
Definition option_wrank {A} {L : lattice A} (W : bounded_widening_rank L) :
  bounded_widening_rank (option_lattice L).        (* wrank None = S wbound, wrank (Some a) = wrank a *)
Definition option_gamma {A C} (G : concretisation A C) : concretisation (option A) C.   (* None: nothing *)
Definition option_agree {A C} (R : agreement A C) : agreement (option A) C.        (* None: trivial *)
Notation lift_bot_gamma := option_gamma.
Notation lift_bot_agree := option_agree.

Inductive lift_top (A : Type) : Type :=
  | Elem (a : A)
  | Unknown.
Definition lift_top_lattice {A} (L : lattice A) : lattice (lift_top A).
(* bot = Elem (bot L); Elem a <= Elem b iff leb L a b; anything <= Unknown; Unknown absorbs join
   and widen; narrow Unknown (Elem b) = Elem b *)
Definition lift_top_top {A} (L : lattice A) : top (lift_top_lattice L).               (* Unknown *)
Definition lift_top_height {A} {L : lattice A} (H : monotone_height L) :
  monotone_height (lift_top_lattice L).      (* rank (Elem a) = rank a, rank Unknown = S bound *)
Definition lift_top_gamma {A C} (G : concretisation A C) : concretisation (lift_top A) C.
(* Unknown: everything *)
Definition lift_top_agree {A C} (R : agreement A C) : agreement (lift_top A) C.
(* Elem a: agree R a; Unknown: only equal values agree *)
```

**Product** (`OrderProduct.v`). Componentwise order, join, widening and narrowing.

```coq
Definition product_lattice {A B} (LA : lattice A) (LB : lattice B) : lattice (A * B).
Definition product_top {A B} {LA : lattice A} {LB : lattice B} (TA : top LA) (TB : top LB) :
  top (product_lattice LA LB).
Definition product_height {A B} {LA : lattice A} {LB : lattice B}
  (lawsA : lattice_laws LA) (lawsB : lattice_laws LB)
  (HA : monotone_height LA) (HB : monotone_height LB) : monotone_height (product_lattice LA LB).
Definition product_wrank {A B} {LA : lattice A} {LB : lattice B}
  (WA : bounded_widening_rank LA) (WB : bounded_widening_rank LB) :
  bounded_widening_rank (product_lattice LA LB).         (* sums of ranks and bounds *)
Definition product_gamma {A B C} (GA : concretisation A C) (GB : concretisation B C) :
  concretisation (A * B) C.                                  (* both components hold: intersection *)
Definition product_agree {A B C} (RA : agreement A C) (RB : agreement B C) : agreement (A * B) C.
(* both components agree *)
```

**Reduced product** (`OrderReduced.v`). A product with `reduce : A * B -> A * B`. The comparison is
made after reducing the left operand, `join` reduces its result, `widen` does not reduce (reducing
after widening can break termination), and `narrow` reduces its second argument.

`reduction_sound` is relative to the supplied concretisations and quantifies over their entire
concrete carrier. A client may supply a restricted meaning explicitly. Domains supplies
word-restricted meanings at a fixed width for its reductions; the raw Order product and component
meanings stay unchanged. `reduction_laws` still requires monotonicity and idempotence up to the
component preorder, independently of semantic soundness.

```coq
Record reduction_laws {A B} (LA : lattice A) (LB : lattice B) (reduce : A * B -> A * B) : Prop := {
  reduce_lower : forall x, leb (product_lattice LA LB) (reduce x) x = true;      (* only goes down *)
  reduce_monotone : forall x y, leb (product_lattice LA LB) x y = true ->
    leb (product_lattice LA LB) (reduce x) (reduce y) = true;
  reduce_idempotent : forall x,
    leb (product_lattice LA LB) (reduce x) (reduce (reduce x)) = true
}.
Record reduction_sound {A B C} (GA : concretisation A C) (GB : concretisation B C)
  (reduce : A * B -> A * B) : Prop := {
  reduce_gamma : forall x c, gamma (product_gamma GA GB) x c ->
    gamma (product_gamma GA GB) (reduce x) c                      (* gamma (reduce x) contains gamma x *)
}.
Definition reduced_lattice {A B} (LA : lattice A) (LB : lattice B) (reduce : A * B -> A * B) :
  lattice (A * B) :=
  let P := product_lattice LA LB in
  {| leb := fun x y => leb P (reduce x) y; bot := bot P;
     join := fun x y => reduce (join P x y); widen := widen P;
     narrow := fun x y => narrow P x (reduce y) |}.
Definition reduced_top {A B} {LA : lattice A} {LB : lattice B} (reduce : A * B -> A * B)
  (TA : top LA) (TB : top LB) : top (reduced_lattice LA LB reduce).
Definition reduced_wrank {A B} {LA : lattice A} {LB : lattice B} (reduce : A * B -> A * B)
  (lawsA : lattice_laws LA) (lawsB : lattice_laws LB) (Hred : reduction_laws LA LB reduce)
  (WA : bounded_widening_rank LA) (WB : bounded_widening_rank LB) :
  bounded_widening_rank (reduced_lattice LA LB reduce).                (* the product's rank *)
(* widen skips reduce, so stability needs no law; progress needs reduce_lower and leb_trans: if every
   component of b were below a, then reduce b would be below a too *)
```

**Dual** (`OrderDual.v`). A dual reverses the order. It needs an explicit `meet` (becoming the
join) with `meet_laws`, and a `top` (becoming the bottom).

```coq
Definition dual_lattice {A} (L : lattice A) (T : top L) (meet : A -> A -> A) : lattice A :=
  {| leb := fun a b => leb L b a; bot := top_value T; join := meet; widen := meet;
     narrow := fun a _ => a |}.
Definition dual_top {A} {L : lattice A} (T : top L) (meet : A -> A -> A) (laws : lattice_laws L) :
  top (dual_lattice L T meet).                                       (* value: bot L *)
Definition dual_height {A} {L : lattice A} (T : top L) (meet : A -> A -> A)
  (rank : A -> nat) (bound : nat) (rank_le : forall a, rank a <= bound)
  (rank_anti : forall a b, leb L b a = true -> rank a <= rank b)
  (meet_grows : forall a b, leb L a (meet a b) = false -> rank a < rank (meet a b)) :
  monotone_height (dual_lattice L T meet).
```

A `height` of the dual is built from a rank that grows when `meet` descends. It cannot be derived
from a `height L`: a lattice can have finite ascending chains and infinite descending ones.

**Basic** (`OrderBasic.v`). `bool_lattice` has `leb = implb`, `bot = false`, `join = widen = orb`.
`unit_lattice` has one element.

```coq
Definition bool_lattice : lattice bool.
Definition bool_top : top bool_lattice.                                   (* true *)
Definition bool_height : monotone_height bool_lattice.                    (* rank 0, 1; bound 1 *)
Definition bool_agree {C} : agreement bool C :=
  {| agree := fun b x y => b = true -> x = y |}.                (* liveness: a live value agrees *)
Definition unit_lattice : lattice unit.
Definition unit_top : top unit_lattice.
Definition unit_height : monotone_height unit_lattice.                    (* bound 0 *)
```

**Powerset** (`OrderPowerset.v`). `powerset_lattice E` orders `FinSet.t K` by `FinSet.subset E`,
with
`bot = FinSet.empty`, `join = widen = FinSet.union E`. Every operation is position-wise on codes, so
its
laws hold for every trie. `must_lattice E` is the reverse-inclusion lattice of must-facts.

```coq
Definition powerset_lattice {K} (E : encoding K) : lattice (FinSet.t K).
Definition powerset_gamma {K} (E : encoding K) : concretisation (FinSet.t K) K.          (* members *)
Definition powerset_agree {K V} (E : encoding K) : agreement (FinSet.t K) (K -> V).
(* agree s x y: x and y are equal on every key of s *)

Inductive must (K : Type) : Type :=
  | All
  | Only (s : FinSet.t K).
Definition must_lattice {K} (E : encoding K) : lattice (must K).
(* All <= everything; Only s <= All false; Only s <= Only t iff FinSet.subset E t s; bot = All;
   join: All neutral, Only s, Only t -> Only (FinSet.inter E s t); widen = join *)
Definition must_top {K} (E : encoding K) : top (must_lattice E).                      (* Only empty *)
Definition must_gamma {K C} (E : encoding K) (holds : K -> C -> Prop) : concretisation (must K) C.
(* All: nothing; Only s: every key of s holds *)
```

Over a finite universe the carrier is restricted so that `height` can hold:

```coq
Definition within_set {K} (E : encoding K) (U : list K) (s : FinSet.t K) : Prop :=
  FinSet.wf E s /\ forall k, FinSet.mem E k s = true -> In k U.
Definition finite_set {K} (E : encoding K) (U : list K) : Type := { s : FinSet.t K | within_set E U s }.
Definition finite_powerset_lattice {K} (E : encoding K) (U : list K) : lattice (finite_set E U).
Definition finite_powerset_top {K} (E : encoding K) (U : list K) : top (finite_powerset_lattice E U).
Definition finite_powerset_height {K} (E : encoding K) (U : list K) (Hnodup : NoDup U) :
  monotone_height (finite_powerset_lattice E U).               (* rank = FinSet.size, bound = length U *)
```

The proof component of `finite_set` is erased by extraction, so a `finite_set` is the trie itself.
A must-analysis over a finite universe (available expressions) is the dual of this lattice, with the
universe as bottom and intersection as join:

```coq
Definition finite_set_inter {K} (E : encoding K) (U : list K) (a b : finite_set E U) : finite_set E U.
Definition finite_must_lattice {K} (E : encoding K) (U : list K) : lattice (finite_set E U) :=
  dual_lattice (finite_powerset_lattice E U) (finite_powerset_top E U) (finite_set_inter E U).
Definition finite_must_height {K} (E : encoding K) (U : list K) (Hnodup : NoDup U) :
  monotone_height (finite_must_lattice E U).          (* rank = length U - FinSet.size; bound = length U *)
Definition finite_must_top {K} (E : encoding K) (U : list K) : top (finite_must_lattice E U).
(* the empty set: the top of the dual is the bottom of the powerset *)
Definition finite_clamp {K} (E : encoding K) (U : list K) (s : FinSet.t K) : finite_set E U.
(* the members of s that lie in U: a fold of FinSet.add over U, keeping the k with FinSet.mem E k s *)
Definition finite_powerset_gamma {K} (E : encoding K) (U : list K) :
  concretisation (finite_set E U) K := comap_gamma (@proj1_sig _ _) (powerset_gamma E).
Definition finite_powerset_agree {K V} (E : encoding K) (U : list K) :
  agreement (finite_set E U) (K -> V) := comap_agree (@proj1_sig _ _) (powerset_agree E).
Definition finite_must_embed {K} (E : encoding K) (U : list K) (a : finite_set E U) : must K :=
  Only (proj1_sig a).
Definition finite_must_gamma {K C} (E : encoding K) (U : list K) (holds : K -> C -> Prop) :
  concretisation (finite_set E U) C := comap_gamma (finite_must_embed E U) (must_gamma E holds).
```

**Pointwise maps** (`OrderPointwise.v`). A `Map.t K A` stands for a function from keys to `A`
with a default for missing keys. Comparisons and combinations operate position-wise on codes, so
their laws hold for every map, well-formed or not.

```coq
Definition pointwise_lookup {K A} (E : encoding K) (d : A) (m : Map.t K A) (k : K) : A :=
  match Map.get E k m with Some a => a | None => d end.

(* Missing keys hold bot L. *)
Definition pointwise_lattice {K A} (E : encoding K) (L : lattice A) : lattice (Map.t K A).
(* leb m1 m2 = Map.forall2 (fun a o => leb L a (the value of o, or bot L)) m1 m2: at every position
   bound in m1, leb L a (the value of m2, or bot L), stopping at the first failure; bot = Map.empty;
   join = Map.union_with (join L): a position bound in one map only keeps its value, and a subtree
   bound on one side is shared;
   widen: Map.combine with (Some a, Some b) -> Some (widen L a b); (Some a, None) -> Some a;
         (None, Some b) -> Some (widen L (bot L) b) (it must not keep b: see Open question 8);
   narrow m1 m2: (Some a, Some b) -> Some (narrow L a b); (Some a, None) -> Some a; (None, _) -> None *)
Definition pointwise_gamma {K A V} (E : encoding K) (L : lattice A) (G : concretisation A V) :
  concretisation (Map.t K A) (K -> V).    (* for every k, gamma G (pointwise_lookup E (bot L) m k) (s k) *)
Definition pointwise_agree {K A V} (E : encoding K) (L : lattice A) (R : agreement A V) :
  agreement (Map.t K A) (K -> V).         (* for every k, agree R (pointwise_lookup ...) (x k) (y k) *)

(* Missing keys hold top_value T. The all-bot map is not finite, so the bottom is an explicit
   None meaning unreachable. *)
Definition pointwise_top_lattice {K A} (E : encoding K) (L : lattice A) (T : top L) :
  lattice (option (Map.t K A)).
(* leb None _ = true; leb (Some _) None = false; leb (Some m1) (Some m2) = Map.forall2 on m2 and m1:
   at every position bound in m2, leb L (the value of m1, or top) b; bot = None;
   join: None is neutral on both sides; on (Some m1, Some m2): (Some a, Some b) -> Some (join L a b),
   one-sided -> None (joining with top gives top); widen likewise with widen L;
   narrow None _ = None; narrow (Some m1) None = Some m1; narrow (Some m1) (Some m2):
   (Some a, Some b) -> Some (narrow L a b), (Some a, None) -> Some a, (None, Some b) -> Some b *)
Definition pointwise_top_gamma {K A V} (E : encoding K) (L : lattice A) (T : top L)
  (G : concretisation A V) : concretisation (option (Map.t K A)) (K -> V).
(* None: nothing; Some m: for every k, gamma G (value of m at k, or top_value T) (s k) *)

Definition within_map {K A} (E : encoding K) (U : list K) (m : Map.t K A) : Prop :=
  Map.wf E m /\ forall k, Map.get E k m <> None -> In k U.
Definition finite_map {K} (E : encoding K) (U : list K) (A : Type) : Type := { m : Map.t K A | within_map E U m }.
Definition finite_pointwise_lattice {K A} (E : encoding K) (U : list K) (L : lattice A) :
  lattice (finite_map E U A).
Definition finite_pointwise_top {K A} {L : lattice A} (E : encoding K) (U : list K) (T : top L) :
  top (finite_pointwise_lattice E U L).                       (* every key of U bound to top *)
Definition finite_pointwise_height {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (laws : lattice_laws L) (lub : lub_laws L) (H : monotone_height L) :
  monotone_height (finite_pointwise_lattice E U L).
(* rank m = sum over k in U of rank H (lookup m k); bound = length U * bound. A key bound on one side
   keeps its value in the join, so strict growth at a key bound only on the right needs
   rank (bot L) < rank b when leb L b (bot L) = false: join_rank_grows, rank_monotone and join_least *)
Definition finite_pointwise_wrank {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (W : bounded_widening_rank L) :
  bounded_widening_rank (finite_pointwise_lattice E U L).    (* the same sums, over wrank *)
Definition finite_pointwise_gamma {K A V} (E : encoding K) (U : list K) (L : lattice A)
  (G : concretisation A V) : concretisation (finite_map E U A) (K -> V) :=
  comap_gamma (@proj1_sig _ _) (pointwise_gamma E L G).
Definition finite_pointwise_agree {K A V} (E : encoding K) (U : list K) (L : lattice A)
  (R : agreement A V) : agreement (finite_map E U A) (K -> V) :=
  comap_agree (@proj1_sig _ _) (pointwise_agree E L R).

(* Missing keys hold top, as in pointwise_top_lattice, over a finite universe. pointwise_top_lattice
   itself has no height: its carrier is infinite. *)
Definition finite_pointwise_top_lattice {K A} (E : encoding K) (U : list K) (L : lattice A)
  (T : top L) : lattice (option (finite_map E U A)).
(* the order, join, widening and narrowing of pointwise_top_lattice on the underlying maps *)
Definition finite_pointwise_top_top {K A} (E : encoding K) (U : list K) (L : lattice A) (T : top L) :
  top (finite_pointwise_top_lattice E U L T).                              (* Some empty *)
Definition finite_pointwise_top_height {K A} {L : lattice A} (E : encoding K) (U : list K)
  (Hnodup : NoDup U) (laws : lattice_laws L) (T : top L) (H : monotone_height L) :
  monotone_height (finite_pointwise_top_lattice E U L T).
(* rank None = 0; rank (Some m) = 1 + sum over k in U of rank H (the value of m at k, or top);
   bound = 1 + length U * bound *)
(* the bindings of m whose key lies in U, rebuilt through Map.get so that the result is well formed *)
Definition finite_map_clamp {K A} (E : encoding K) (U : list K) (m : Map.t K A) : finite_map E U A.
(* a fold over U: bind k to v when Map.get E k m = Some v *)
```

**Bounded disjunction** (`OrderDisjunction.v`). An element is a list of disjuncts, standing for
their union; the cap `k` bounds the list that `join` returns.

```coq
Definition join_all {A} (L : lattice A) (l : list A) : A :=
  match l with nil => bot L | x :: l' => List.fold_left (join L) l' x end.
Definition disjunction_leb {A} (L : lattice A) (xs ys : list A) : bool :=
  List.forallb (fun x => List.existsb (leb L x) ys) xs.       (* every disjunct sits under one of ys *)
Definition compact {A} (k : nat) (L : lattice A) (l : list A) : list A :=
  if Nat.leb (List.length l) k then l
  else List.firstn (k - 1) l ++ [join_all L (List.skipn (k - 1) l)].
Definition disjunction_lattice {A} (k : nat) (L : lattice A) : lattice (list A) :=
  {| leb := disjunction_leb L; bot := nil;
     join := fun xs ys => compact k L (xs ++ ys);
     widen := fun xs ys =>
       if disjunction_leb L ys xs then xs
       else [widen L (join_all L xs) (join_all L (xs ++ ys))];
     narrow := fun xs _ => xs |}.
Definition disjunction_wrank {A} {L : lattice A} (k : nat) (laws : lattice_laws L)
  (W : bounded_widening_rank L) : bounded_widening_rank (disjunction_lattice k L).
(* wrank xs = 2 * wrank (join_all L xs) + (if length xs = 1 then 0 else 1); wbound = 2 * wbound + 1;
   progress needs the laws: if the join of xs ++ ys were below the single disjunct of xs, then every
   disjunct of ys would be below it *)
Definition disjunction_gamma {A C} (G : concretisation A C) : concretisation (list A) C.
(* gamma xs c: some disjunct x in xs has gamma G x c *)
```

`widen` collapses to a single disjunct as soon as the second argument is not covered, which keeps
the rank argument simple. There is no `top`: a disjunction has one only when `L` has one, and then
`[top_value T]` is it.

**From a height to a widening rank** (`OrderLattice.v`). A lattice with `widen = join` and a
monotone height has a bounded widening rank.

```coq
Definition height_wrank {A} (L : lattice A) (laws : lattice_laws L)
  (Hw : forall a b, widen L a b = join L a b) (H : monotone_height L) : bounded_widening_rank L.
(* wrank a = bound - rank a *)
```

## Theorems

### Core and monotone functions

```coq
Section CoreLaws.
Context {A C : Type} (L : lattice A) (G : concretisation A C) (R : agreement A C).
Variables (a a' b b' : A) (c x y : C).

(** Join is monotone in both arguments when it is a least upper bound. *)
Theorem join_monotone : lattice_laws L -> lub_laws L -> leb L a a' = true -> leb L b b' = true ->
  leb L (join L a b) (join L a' b') = true.
Theorem join_bot_equivalent : lattice_laws L -> lub_laws L -> equivalent L (join L (bot L) a) a.
(* Proof idea: join_least with join_upper_l/r and leb_trans. Card: ORD-1. *)

(** What a join, widening or narrowing keeps of the meaning of its arguments. *)
Theorem gamma_join_l : lattice_laws L -> concretisation_laws L G ->
  gamma G a c -> gamma G (join L a b) c.
Theorem gamma_join_r : lattice_laws L -> concretisation_laws L G ->
  gamma G b c -> gamma G (join L a b) c.
Theorem gamma_widen_l : lattice_laws L -> concretisation_laws L G ->
  gamma G a c -> gamma G (widen L a b) c.
Theorem gamma_widen_r : lattice_laws L -> concretisation_laws L G ->
  gamma G b c -> gamma G (widen L a b) c.
Theorem gamma_narrow : lattice_laws L -> concretisation_laws L G -> leb L b a = true ->
  gamma G b c -> gamma G (narrow L a b) c.
(* Proof idea: gamma_monotone with join_upper_*, widen_upper_* and narrow_upper. Card: ORD-1. *)

(** Backward: needing something of a join or widening needs it of each argument. *)
Theorem agree_join_l : lattice_laws L -> agreement_laws L R ->
  agree R (join L a b) x y -> agree R a x y.
Theorem agree_join_r : lattice_laws L -> agreement_laws L R ->
  agree R (join L a b) x y -> agree R b x y.
Theorem agree_widen_l : lattice_laws L -> agreement_laws L R ->
  agree R (widen L a b) x y -> agree R a x y.
Theorem agree_widen_r : lattice_laws L -> agreement_laws L R ->
  agree R (widen L a b) x y -> agree R b x y.
(* Proof idea: agree_antitone with the upper-bound laws. Card: ORD-1. *)
End CoreLaws.

Section MonotoneLaws.
Context {X A B C : Type} (L1 : lattice A) (L2 : lattice B) (L3 : lattice C).

(** Identity, constants and composition are monotone; join is monotone as a binary function. *)
Theorem monotone_id : lattice_laws L1 -> monotone_fun L1 L1 (fun a => a).
Theorem monotone_const : forall b : B, lattice_laws L2 -> monotone_fun L1 L2 (fun _ => b).
Theorem monotone_compose : forall (f : A -> B) (g : B -> C),
  monotone_fun L1 L2 f -> monotone_fun L2 L3 g -> monotone_fun L1 L3 (fun a => g (f a)).
Theorem monotone_join : lattice_laws L1 -> lub_laws L1 -> monotone_fun2 L1 L1 L1 (join L1).
(** The same closure for functions of assignments, which is what a right-hand side is: a constant,
    the read of one unknown, a join and a composition with a monotone function are monotone. *)
Theorem monotone_on_const : forall b : B, lattice_laws L2 ->
  @monotone_on_assignments X A B L1 L2 (fun _ => b).
Theorem monotone_on_lookup : forall x : X, @monotone_on_assignments X A A L1 L1 (fun s => s x).
Theorem monotone_on_join : forall f g : (X -> A) -> A, lattice_laws L1 -> lub_laws L1 ->
  monotone_on_assignments L1 L1 f -> monotone_on_assignments L1 L1 g ->
  monotone_on_assignments L1 L1 (fun s => join L1 (f s) (g s)).
Theorem monotone_on_compose : forall (f : (X -> A) -> B) (g : B -> C),
  monotone_on_assignments L1 L2 f -> monotone_fun L2 L3 g ->
  monotone_on_assignments L1 L3 (fun s => g (f s)).
(** The pointwise order on assignments is a preorder. *)
Theorem fun_leb_preorder : lattice_laws L1 -> preorder (X -> A) (fun s1 s2 => fun_leb L1 s1 s2).
(* Proof idea: unfolding, leb_refl, leb_trans and join_monotone. Card: ORD-1. *)
End MonotoneLaws.
```

### Flat, lifts, product

```coq
Section FlatLaws.
Context {A C : Type} (eqb : A -> A -> bool) (G : A -> C -> Prop).

(** A flat lattice is a lattice with least upper bounds when eqb decides equality. *)
Theorem flat_laws : eqb_spec eqb -> lattice_laws (flat_lattice eqb).
Theorem flat_lub : eqb_spec eqb -> lub_laws (flat_lattice eqb).
(** Its meaning: bottom is empty, top is everything, and the order is inclusion. *)
Theorem flat_gamma_laws : eqb_spec eqb -> concretisation_laws (flat_lattice eqb) (flat_gamma G).
Theorem flat_gamma_bot_empty : bottom_empty (flat_lattice eqb) (flat_gamma G).
Theorem flat_gamma_top_full : top_full (flat_top eqb) (flat_gamma G).
(* Proof idea: case analysis on the three constructors, with eqb_spec for the FVal case. Card: ORD-1. *)
End FlatLaws.

Section LiftLaws.
Context {A C : Type} (L : lattice A) (G : concretisation A C) (R : agreement A C).

(** Adding a fresh bottom (lift_bot, option) keeps the laws, the meaning and the needs. *)
Theorem option_laws : lattice_laws L -> lattice_laws (option_lattice L).
Theorem option_lub : lub_laws L -> lub_laws (option_lattice L).
Theorem option_gamma_laws : concretisation_laws L G ->
  concretisation_laws (option_lattice L) (option_gamma G).
Theorem option_gamma_bot_empty : bottom_empty (option_lattice L) (option_gamma G).
Theorem option_agree_laws : agreement_laws L R ->
  agreement_laws (option_lattice L) (option_agree R).
Theorem option_agree_bot : agreement_bot (option_lattice L) (option_agree R).
Theorem option_agree_join : agreement_join_law L R ->
  agreement_join_law (option_lattice L) (option_agree R).
(* Proof idea: case analysis on None and Some, delegating the Some case to L. Card: ORD-1. *)

(** Adding a fresh top. *)
Theorem lift_top_laws : lattice_laws L -> lattice_laws (lift_top_lattice L).
Theorem lift_top_lub : lub_laws L -> lub_laws (lift_top_lattice L).
Theorem lift_top_gamma_laws : concretisation_laws L G ->
  concretisation_laws (lift_top_lattice L) (lift_top_gamma G).
Theorem lift_top_gamma_top_full : top_full (lift_top_top L) (lift_top_gamma G).
(* Proof idea: case analysis on Elem and Unknown. Card: ORD-1. *)
End LiftLaws.

Section ProductLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (GA : concretisation A C)
  (GB : concretisation B C) (RA : agreement A C) (RB : agreement B C).

(** A product is a lattice componentwise; its meaning is the intersection of the components'. *)
Theorem product_laws : lattice_laws LA -> lattice_laws LB -> lattice_laws (product_lattice LA LB).
Theorem product_lub : lub_laws LA -> lub_laws LB -> lub_laws (product_lattice LA LB).
Theorem product_gamma_laws : concretisation_laws LA GA -> concretisation_laws LB GB ->
  concretisation_laws (product_lattice LA LB) (product_gamma GA GB).
Theorem product_gamma_bot_empty : bottom_empty LA GA \/ bottom_empty LB GB ->
  bottom_empty (product_lattice LA LB) (product_gamma GA GB).
Theorem product_agree_laws : agreement_laws LA RA -> agreement_laws LB RB ->
  agreement_laws (product_lattice LA LB) (product_agree RA RB).
Theorem product_agree_join : agreement_join_law LA RA -> agreement_join_law LB RB ->
  agreement_join_law (product_lattice LA LB) (product_agree RA RB).
(* Proof idea: componentwise; destructure the pairs. Card: ORD-1. *)
End ProductLaws.
```

### Pullback, agreements of flat and lifted lattices, pairs

```coq
Section TransportLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (G : concretisation A C)
  (R : agreement A C) (f : B -> A).

(** Pulling a meaning back along an order-embedding keeps its laws; the bottom and top transport when
    `f` maps them below and above the corresponding element. *)
Theorem comap_gamma_laws : order_embedding LA LB f -> concretisation_laws LA G ->
  concretisation_laws LB (comap_gamma f G).
Theorem comap_gamma_bot_empty : order_embedding LA LB f -> concretisation_laws LA G ->
  bottom_empty LA G -> leb LA (f (bot LB)) (bot LA) = true -> bottom_empty LB (comap_gamma f G).
Theorem comap_gamma_top_full : forall (TA : top LA) (TB : top LB), order_embedding LA LB f ->
  concretisation_laws LA G -> top_full TA G -> leb LA (top_value TA) (f (top_value TB)) = true ->
  top_full TB (comap_gamma f G).
Theorem comap_agree_laws : order_embedding LA LB f -> agreement_laws LA R ->
  agreement_laws LB (comap_agree f R).
Theorem comap_agree_bot : agreement_laws LA R -> agreement_bot LA R ->
  leb LA (f (bot LB)) (bot LA) = true -> agreement_bot LB (comap_agree f R).
Theorem comap_agree_join : agreement_laws LA R -> agreement_join_law LA R ->
  (forall a b, leb LA (f (join LB a b)) (join LA (f a) (f b)) = true) ->
  agreement_join_law LB (comap_agree f R).
(* Proof idea: unfolding; the laws of LA at f of each argument; antitonicity of agree for the bottom
   and join laws; monotonicity of gamma for the bottom and top laws. Card: ORD-1. *)
End TransportLaws.

Section AgreeLaws.
Context {A C : Type} (eqb : A -> A -> bool) (RV : A -> C -> C -> Prop) (L : lattice A)
  (R : agreement A C).

(** A flat agreement: the bottom needs nothing and the top needs equality. *)
Theorem flat_agree_laws : eqb_spec eqb -> (forall a c, RV a c c) ->
  agreement_laws (flat_lattice eqb) (flat_agree RV).
Theorem flat_agree_bot : agreement_bot (flat_lattice eqb) (flat_agree RV).
(** The same for a fresh top over an agreement. *)
Theorem lift_top_agree_laws : agreement_laws L R ->
  agreement_laws (lift_top_lattice L) (lift_top_agree R).
Theorem lift_top_agree_bot : agreement_bot L R -> agreement_bot (lift_top_lattice L) (lift_top_agree R).
Theorem lift_top_agree_join : agreement_join_law L R ->
  agreement_join_law (lift_top_lattice L) (lift_top_agree R).
(* Proof idea: case analysis on the constructors; equal values agree, and Unknown absorbs. Card: ORD-1. *)
End AgreeLaws.

Section PairMonotone.
Context {A B D : Type} (LA : lattice A) (LB : lattice B) (LD : lattice D).

(** Projections and pairing are monotone. *)
Theorem monotone_fst : monotone_fun (product_lattice LA LB) LA fst.
Theorem monotone_snd : monotone_fun (product_lattice LA LB) LB snd.
Theorem monotone_pair : forall (f : D -> A) (g : D -> B), monotone_fun LD LA f -> monotone_fun LD LB g ->
  monotone_fun LD (product_lattice LA LB) (fun d => (f d, g d)).
(* Proof idea: the product order is componentwise. Card: ORD-1. *)
End PairMonotone.
```

### Reduced product, dual, basic

```coq
Section ReducedLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (GA : concretisation A C)
  (GB : concretisation B C) (reduce : A * B -> A * B) (TA : top LA) (TB : top LB).
Variables (x : A * B) (c : C).

(** A reduction that goes down, is monotone and is idempotent yields a lattice. *)
Theorem reduced_laws : lattice_laws LA -> lattice_laws LB -> reduction_laws LA LB reduce ->
  lattice_laws (reduced_lattice LA LB reduce).
(** If it also preserves meaning, the order is inclusion of meanings. *)
Theorem reduced_gamma_laws : lattice_laws LA -> lattice_laws LB ->
  concretisation_laws LA GA -> concretisation_laws LB GB ->
  reduction_laws LA LB reduce -> reduction_sound GA GB reduce ->
  concretisation_laws (reduced_lattice LA LB reduce) (product_gamma GA GB).
(** Reducing never changes the meaning: it goes down (so gamma shrinks) and gamma contains the old. *)
Theorem reduce_gamma_exact : lattice_laws LA -> lattice_laws LB ->
  concretisation_laws LA GA -> concretisation_laws LB GB ->
  reduction_laws LA LB reduce -> reduction_sound GA GB reduce ->
  (gamma (product_gamma GA GB) (reduce x) c <-> gamma (product_gamma GA GB) x c).
Theorem reduced_top_full : top_full TA GA -> top_full TB GB ->
  top_full (@reduced_top A B LA LB reduce TA TB) (product_gamma GA GB).
(* Proof idea: leb is transitive because reduce is monotone and idempotent up to the order;
   join is an upper bound because reduce is monotone; widen skips reduce, so the product laws
   apply; narrow reduces its second argument to meet the hypothesis of the product laws. Card: ORD-1. *)
End ReducedLaws.

Section DualLaws.
Context {A : Type} (L : lattice A) (T : top L) (meet : A -> A -> A).

(** The dual of a lattice with a greatest lower bound is a lattice, with least upper bounds. *)
Theorem dual_laws : lattice_laws L -> meet_laws L meet -> lattice_laws (dual_lattice L T meet).
Theorem dual_lub : lattice_laws L -> meet_laws L meet -> lub_laws (dual_lattice L T meet).
(* Proof idea: the dual's join_upper laws are meet_lower_*, join_least is meet_greatest, and
   bot_least is top_greatest. Card: ORD-1. *)
End DualLaws.

Section BasicLaws.
Context {C : Type}.

(** Booleans and the one-point lattice, with liveness as the booleans' agreement. *)
Theorem bool_laws : lattice_laws bool_lattice.
Theorem bool_lub : lub_laws bool_lattice.
Theorem bool_agree_laws : agreement_laws bool_lattice (@bool_agree C).
Theorem bool_agree_bot : agreement_bot bool_lattice (@bool_agree C).
Theorem bool_agree_join : agreement_join_law bool_lattice (@bool_agree C).
Theorem bool_agree_equivalence : agreement_equivalence (@bool_agree C).
Theorem unit_laws : lattice_laws unit_lattice.
Theorem unit_lub : lub_laws unit_lattice.
(* Proof idea: case analysis on the booleans. Card: ORD-1. *)
End BasicLaws.
```

### Powerset, pointwise, disjunction

```coq
Section PowersetLaws.
Context {K V C : Type} (E : encoding K) (holds : K -> C -> Prop) (U : list K).

(** Sets under inclusion form a lattice with least upper bounds; the meaning of a set is its members. *)
Theorem powerset_laws : lattice_laws (powerset_lattice E).
Theorem powerset_lub : lub_laws (powerset_lattice E).
Theorem powerset_gamma_laws : concretisation_laws (powerset_lattice E) (powerset_gamma E).
Theorem powerset_gamma_bot_empty : bottom_empty (powerset_lattice E) (powerset_gamma E).
(** Liveness over a set of variables: the live ones must agree. *)
Theorem powerset_agree_laws : agreement_laws (powerset_lattice E) (@powerset_agree K V E).
Theorem powerset_agree_bot : agreement_bot (powerset_lattice E) (@powerset_agree K V E).
Theorem powerset_agree_join : agreement_join_law (powerset_lattice E) (@powerset_agree K V E).
Theorem powerset_agree_equivalence : agreement_equivalence (@powerset_agree K V E).
(* Proof idea: FinSet.subset_code, FinSet.union_code and the FinSet.mem_* laws, each at one position;
   a position without a key is a position like any other, so no wf premise arises. Card: ORD-2. *)

(** Must-facts: join is intersection, All is the neutral element, and the order is reverse inclusion. *)
Theorem must_laws : lattice_laws (must_lattice E).
Theorem must_lub : lub_laws (must_lattice E).
Theorem must_gamma_laws : concretisation_laws (must_lattice E) (must_gamma E holds).
Theorem must_gamma_bot_empty : bottom_empty (must_lattice E) (must_gamma E holds).
Theorem must_gamma_top_full : top_full (must_top E) (must_gamma E holds).
(* Proof idea: case analysis on All and Only, then FinSet.inter_code and FinSet.subset_code. Card: ORD-2. *)

(** Over a finite universe the carrier is restricted, and the laws still hold. *)
Theorem finite_powerset_laws : lattice_laws (finite_powerset_lattice E U).
Theorem finite_powerset_lub : lub_laws (finite_powerset_lattice E U).
Theorem finite_set_inter_meet : meet_laws (finite_powerset_lattice E U) (finite_set_inter E U).
Theorem finite_must_laws : lattice_laws (finite_must_lattice E U).
Theorem finite_must_lub : lub_laws (finite_must_lattice E U).
(* Proof idea: the powerset laws on the underlying sets; the proof component is preserved by
   FinSet.wf_ops and membership in U; the must lattice is dual_laws and dual_lub with the meet. Card: ORD-2. *)

(** The finite carriers embed in the raw ones, and meanings pull back along the embedding. *)
Theorem finite_powerset_embedding :
  order_embedding (powerset_lattice E) (finite_powerset_lattice E U) (@proj1_sig _ _).
Theorem finite_must_embedding :
  order_embedding (must_lattice E) (finite_must_lattice E U) (finite_must_embed E U).
Theorem finite_powerset_gamma_laws :
  concretisation_laws (finite_powerset_lattice E U) (finite_powerset_gamma E U).
Theorem finite_powerset_gamma_bot_empty :
  bottom_empty (finite_powerset_lattice E U) (finite_powerset_gamma E U).
Theorem finite_powerset_agree_laws :
  agreement_laws (finite_powerset_lattice E U) (@finite_powerset_agree K V E U).
Theorem finite_must_gamma_laws :
  concretisation_laws (finite_must_lattice E U) (finite_must_gamma E U holds).
Theorem finite_must_gamma_top_full : top_full (finite_must_top E U) (finite_must_gamma E U holds).
(* Proof idea: the embeddings are the definitions of the finite orders; then comap_gamma_laws,
   comap_agree_laws and the powerset and must laws. Card: ORD-2. *)

(** Clamping puts a raw set inside the universe and keeps exactly its members that lie there. *)
Theorem finite_clamp_mem : forall (s : FinSet.t K) (k : K), In k U ->
  FinSet.mem E k (proj1_sig (finite_clamp E U s)) = FinSet.mem E k s.
Theorem finite_clamp_in : forall (s : FinSet.t K) (k : K),
  FinSet.mem E k (proj1_sig (finite_clamp E U s)) = true -> In k U.
(* Proof idea: a fold of FinSet.add over U with the FinSet.mem_add laws, for every raw s; the proof
   component is FinSet.wf_ops and membership in U. Card: ORD-2. *)
End PowersetLaws.

Section PointwiseLaws.
Context {K A V : Type} (E : encoding K) (L : lattice A) (T : top L) (G : concretisation A V)
  (R : agreement A V) (U : list K).

(** Maps with default bot are a lattice when the values are; their meaning is pointwise. *)
Theorem pointwise_laws : lattice_laws L -> lattice_laws (pointwise_lattice E L).
Theorem pointwise_lub : lattice_laws L -> lub_laws L -> lub_laws (pointwise_lattice E L).
Theorem pointwise_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (pointwise_lattice E L) (pointwise_gamma E L G).
Theorem pointwise_agree_laws : lattice_laws L -> agreement_laws L R ->
  agreement_laws (pointwise_lattice E L) (pointwise_agree E L R).
Theorem pointwise_agree_bot : agreement_bot L R ->
  agreement_bot (pointwise_lattice E L) (pointwise_agree E L R).
Theorem pointwise_agree_join : lattice_laws L -> agreement_laws L R -> agreement_bot L R ->
  agreement_join_law L R -> agreement_join_law (pointwise_lattice E L) (pointwise_agree E L R).
(* Proof idea: Map.forall2_spec for leb, Map.code_get_union_with and Map.code_get_combine for the
   operations; each position splits into the cases bound or unbound on each side. Card: ORD-2. *)

(** Maps with default top, under an explicit unreachable bottom. *)
Theorem pointwise_top_laws : lattice_laws L -> lattice_laws (pointwise_top_lattice E L T).
Theorem pointwise_top_lub : lattice_laws L -> lub_laws L -> lub_laws (pointwise_top_lattice E L T).
Theorem pointwise_top_gamma_laws : lattice_laws L -> concretisation_laws L G -> top_full T G ->
  concretisation_laws (pointwise_top_lattice E L T) (pointwise_top_gamma E L T G).
Theorem pointwise_top_gamma_bot_empty :
  bottom_empty (pointwise_top_lattice E L T) (pointwise_top_gamma E L T G).
(* Proof idea: as for default bot, with top_greatest and top_full for the missing keys. Card: ORD-2. *)

(** Over a finite key universe the carrier is restricted, and the laws still hold. *)
Theorem finite_pointwise_laws : lattice_laws L -> lattice_laws (finite_pointwise_lattice E U L).
Theorem finite_pointwise_lub : lattice_laws L -> lub_laws L ->
  lub_laws (finite_pointwise_lattice E U L).
(* Proof idea: the pointwise laws on the underlying maps, with Map.wf_combine and the support in U. Card: ORD-2. *)

(** Reading one key is monotone, on the raw and on the finite maps. *)
Theorem monotone_pointwise_lookup : lattice_laws L -> forall k : K,
  monotone_fun (pointwise_lattice E L) L (fun m => pointwise_lookup E (bot L) m k).
Theorem monotone_finite_pointwise_lookup : lattice_laws L -> forall k : K,
  monotone_fun (finite_pointwise_lattice E U L) L
    (fun m => pointwise_lookup E (bot L) (proj1_sig m) k).
(* Proof idea: the order is read at the position of the key (Map.forall2_spec); an unbound key holds
   bot, below everything by bot_least. Card: ORD-2. *)

(** The finite maps with default top, under an explicit unreachable bottom. *)
Theorem finite_pointwise_top_laws : lattice_laws L ->
  lattice_laws (finite_pointwise_top_lattice E U L T).
Theorem finite_pointwise_top_lub : lattice_laws L -> lub_laws L ->
  lub_laws (finite_pointwise_top_lattice E U L T).
Theorem finite_pointwise_top_embedding : order_embedding (pointwise_top_lattice E L T)
  (finite_pointwise_top_lattice E U L T) (option_map (@proj1_sig _ _)).
(* Proof idea: as for pointwise_top_laws, with Map.wf_combine and the support in U. Card: ORD-2. *)

(** Meanings of the finite maps pull back from the raw ones; clamping a map keeps its lookups in U. *)
Theorem finite_pointwise_embedding :
  order_embedding (pointwise_lattice E L) (finite_pointwise_lattice E U L) (@proj1_sig _ _).
Theorem finite_pointwise_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (finite_pointwise_lattice E U L) (finite_pointwise_gamma E U L G).
Theorem finite_pointwise_agree_laws : lattice_laws L -> agreement_laws L R ->
  agreement_laws (finite_pointwise_lattice E U L) (finite_pointwise_agree E U L R).
Theorem finite_map_clamp_get : forall (m : Map.t K A) (k : K), In k U ->
  Map.get E k (proj1_sig (finite_map_clamp E U m)) = Map.get E k m.
(* Proof idea: comap_gamma_laws and comap_agree_laws along the embedding, which is the definition of
   the finite order; the clamp is a fold of Map.set over U, so Map.get_set_same and Map.get_set_other
   give the lookup for every raw m, and Map.wf_set the proof component. Card: ORD-2. *)
End PointwiseLaws.

Section DisjunctionLaws.
Context {A C : Type} (k : nat) (L : lattice A) (G : concretisation A C).
Variables (xs ys : list A).

(** Disjunctions under the Hoare order form a lattice, and a join respects the cap. *)
Theorem disjunction_laws : lattice_laws L -> lattice_laws (disjunction_lattice k L).
Theorem disjunction_join_size : 1 <= k ->
  List.length (join (disjunction_lattice k L) xs ys) <= k.
(** The meaning of a disjunction is the union of the meanings of its disjuncts. *)
Theorem disjunction_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (disjunction_lattice k L) (disjunction_gamma G).
Theorem disjunction_gamma_bot_empty :
  bottom_empty (disjunction_lattice k L) (disjunction_gamma G).
(* Proof idea: join_all is an upper bound of its list; compact keeps each disjunct below a result
   disjunct; the collapsing widening is above both arguments by widen_upper_*. Card: ORD-2. *)

(** The join of a list is monotone in the list, element by element. *)
Theorem monotone_join_all : lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys -> leb L (join_all L xs) (join_all L ys) = true.
(* Proof idea: induction on the lists with join_monotone. Card: ORD-2. *)
End DisjunctionLaws.
```

Every `*_height`, `*_wrank` and `*_top` item above is a `Definition` whose record fields are
proved inside it (opaque proofs, transparent data), so each is itself a claim: it is closed under
the global context.

Least upper bounds (`lub_laws`) hold for flat, option, lift_top, product, dual, bool, unit,
powerset, must, pointwise and their finite variants. They do not hold for `reduced_lattice`
(reducing the join of unreduced arguments can leave a pair that is not below a common upper bound)
nor for `disjunction_lattice` (a capped join collapses disjuncts that a single upper bound may cover
separately). Fixpoint's least-solution theorems therefore apply to the first group only.

## Algorithms and references

- **Lattices, widening, narrowing.** P. Cousot and R. Cousot, "Abstract interpretation: a unified
  lattice model for static analysis of programs", POPL 1977; and "Systematic design of program
  analysis frameworks", POPL 1979, which also introduces the reduced product and the disjunctive
  completion. Only a preorder, bottom and upper bounds are required; least upper bounds are the
  separate `lub_laws`, since several useful domains (wrapped intervals, disjunctions) have none.
- **Concretisation only.** Soundness is stated through `gamma` alone, with no abstraction function,
  as in Pichardie's thesis (2005) and in Verasco (Jourdan et al., POPL 2015).
- **Flat constants.** Kildall, "A unified approach to global program optimization", POPL 1973.
- **Threshold widening.** Blanchet et al., "A static analyzer for large safety-critical software",
  PLDI 2003: widen to the next threshold; a finite threshold set gives a finite `wrank`.
- **Reduced product.** Cousot and Cousot 1979; reduction before comparison and after join, but not
  after widening, follows the practice of Granger, "Improving the results of static analyses of
  programs by local decreasing iterations", FSTTCS 1992.
- **Bounded disjunction.** The Hoare (lower) powerdomain order of Abramsky and Jung, "Domain
  theory",
  1994, with a cap and a collapsing widening in the spirit of Bagnara, Hill and Zaffanella,
  "Widening operators for powerset domains", STTT 2006 (their certificate-based widenings are
  future work).
- **Must-facts and dual.** The reverse-inclusion lattice of available expressions, in Nielson,
  Nielson and Hankin, *Principles of Program Analysis*, 1999.
- **Agreement.** A relation `agree a x y` says that `x` and `y` are indistinguishable on what `a`
  marks as needed; liveness and demanded bits are its instances, and the antitone law is what makes
  a backward fixpoint sound.

## Performance notes

- Position-wise operations (`powerset`, `pointwise`, `must`) run in O(trie nodes), with no list of
  keys. Pointwise `leb` uses `Map.forall2` and stops at the first failure; pointwise join with a
  bottom default uses `Map.union_with` and shares one-sided subtrees.
- The restricted carriers (`finite_set`, `finite_map`) store a proof that extraction erases: they
  run
  as the bare tries. Their ranks sum over the universe list `U`, but ranks occur only in proofs and
  are never executed, so a scan of `U` costs nothing at run time.
- `disjunction_leb` costs O(|xs| * |ys|) comparisons of `L`; `compact` is linear in the list; `k` is
  small in practice (2 to 8). A `reduced` comparison calls `reduce` once on the left operand.
- Prepared indexes: none. The agreement between a map and its keys is `Map.wf` from Collections.

## Open questions

1. **`Top` is taken.** The anchors' record constructor `Top` forbids a flat constructor of that
  name,
   so `flat` uses `FBot | FVal | FTop`; `lift_top` uses `Elem | Unknown`.
2. **Additions to the anchors:** `meet_laws`, `monotone_height`, `bounded_widening_rank`,
   `eqb_spec`, `equivalent`, and the extra meaning laws (`bottom_empty`, `top_full`,
   `agreement_equivalence`, `agreement_bot`, `agreement_join_law`). `monotone_height` is needed
   because the anchors' `height` does not force ranks to grow with the order, and sums of ranks
   (product, pointwise) need that. `bounded_widening_rank` is needed because lifting adds a bottom
   whose rank must exceed every other rank.
3. **`All` is a bottom here.** The brief calls `All` the top of `must_powerset`. With join as
   intersection and the order as reverse inclusion, `All` (the whole universe) is the least element
   and the empty set is the top; `must_top` is `Only FinSet.empty`.
4. **Finite universes use sigma carriers.** `finite_set` and `finite_map` restrict the type so that
   the unconditional `rank_bounded` field of `height` can hold. The alternative, a `height` with an
   `inside` predicate, would change the anchors and Fixpoint's termination theorem.
5. **`widen` of a disjunction collapses** to one disjunct when the second argument is not covered.
   It is sound and has a rank, but loses precision at loop heads; a certificate-limited widening
   is future work.
6. **`reduce_idempotent` is idempotence up to the order**, which is what transitivity needs and is
   easier for clients to prove than syntactic equality.
7. **`reduced_lattice` has no `lub_laws` and no `height`;** termination comes from `reduced_wrank`
   because `widen` skips `reduce`.
8. **Pointwise one-sided joins.** `join` keeps the value of a position bound on one side only, so a
   subtree bound on one side is shared (`Map.union_with`), and `finite_pointwise_height` takes
   `lub_laws`: strict growth at a key bound only on the right needs `rank (bot L) < rank b`.
   `widen` cannot share: it joins a right-only value with `bot L` through `widen`, because `wrank b`
   is unrelated to the rank of `widen L (bot L) b`.
9. **Clamping.** `finite_clamp` and `finite_map_clamp` fold over the universe list, so each costs
   O(|U|) map operations; a prepared set of `U` carried by the carrier would make them
   proportional to the raw set. They answer the requests of Analyses by name and by lemma.

## Notes for other documents

- `FinSet` replaces `Set` in every name used here (`FinSet.t`, `FinSet.subset`, `FinSet.mem`, ...).
- Signatures that changed: `option_height laws H`; `reduced_top reduce TA TB`;
  `reduced_wrank reduce lawsA lawsB Hred WA WB`; `disjunction_wrank k laws W`;
  `finite_pointwise_height E U Hnodup laws lub H`, whose `lub_laws L` argument is new (`bool_lub`
  and `mask_lub` supply it). `analyses.md` names `option_height` and `finite_pointwise_height` as
  evidence, and `domains.md` uses `reduced_laws` and `reduced_gamma_laws` unchanged.
- New names: `finite_clamp`, `finite_map_clamp` (requested by `analyses.md`), `finite_must_top`,
  `order_embedding`, `comap_gamma`, `comap_agree`, `lift_top_agree`, `flat_agree`,
  `finite_pointwise_top_lattice` with its top and height, `monotone_on_const`, `monotone_on_lookup`,
  `monotone_on_join`, `monotone_on_compose`, `monotone_fst`, `monotone_snd`, `monotone_pair`,
  `monotone_pointwise_lookup` and `monotone_join_all`.
