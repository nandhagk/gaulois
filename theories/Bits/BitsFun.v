(** * Total word operations

    Each operation interprets its operands at the supplied width and follows total bitvector
    arithmetic. For example, unsigned division by zero gives the all-ones word.
    Builds on: BitsWord and Rocq Stdlib integer bit operations. *)

From Stdlib Require Import ZArith List Bool.
From Gaulois.Bits Require Import BitsWord.

Open Scope Z_scope.

(** Complement flips exactly the bits below the width. *)
Definition wnot (w : width) (x : Z) : Z := modulus w - 1 - wrap w x.

(** Negation computes the additive inverse modulo the word modulus. *)
Definition wneg (w : width) (x : Z) : Z := wrap w (- x).

(** Addition reduces the integer sum to the word range. *)
Definition wadd (w : width) (x y : Z) : Z := wrap w (x + y).

(** Subtraction reduces the integer difference to the word range. *)
Definition wsub (w : width) (x y : Z) : Z := wrap w (x - y).

(** Multiplication reduces the integer product to the word range. *)
Definition wmul (w : width) (x y : Z) : Z := wrap w (x * y).

(** Conjunction acts on the wrapped operands. *)
Definition wand (w : width) (x y : Z) : Z := Z.land (wrap w x) (wrap w y).

(** Disjunction acts on the wrapped operands. *)
Definition wor (w : width) (x y : Z) : Z := Z.lor (wrap w x) (wrap w y).

(** Exclusive disjunction acts on the wrapped operands. *)
Definition wxor (w : width) (x y : Z) : Z := Z.lxor (wrap w x) (wrap w y).

(** Unsigned division by zero returns all ones. *)
Definition wudiv (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then modulus w - 1 else wrap w x / wrap w y.

(** Unsigned remainder by zero returns the wrapped dividend. *)
Definition wurem (w : width) (x y : Z) : Z :=
  if wrap w y =? 0 then wrap w x else wrap w x mod wrap w y.

(** Signed division uses the SMT-LIB sign cases over unsigned division. *)
Definition wsdiv (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wudiv w x y
  | true, false => wneg w (wudiv w (wneg w x) y)
  | false, true => wneg w (wudiv w x (wneg w y))
  | true, true => wudiv w (wneg w x) (wneg w y)
  end.

(** Signed remainder has the sign of the dividend. *)
Definition wsrem (w : width) (x y : Z) : Z :=
  match msb w x, msb w y with
  | false, false => wurem w x y
  | true, false => wneg w (wurem w (wneg w x) y)
  | false, true => wurem w x (wneg w y)
  | true, true => wneg w (wurem w (wneg w x) (wneg w y))
  end.

(** Signed modulus has the sign of the divisor when the remainder is nonzero. *)
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

(** Left shift discards bits above the width and gives zero for large amounts. *)
Definition wshl (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then 0 else wrap w (wrap w x * 2 ^ wrap w y).

(** Logical right shift fills with zero and gives zero for large amounts. *)
Definition wlshr (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then 0 else wrap w x / 2 ^ wrap w y.

(** Arithmetic right shift fills with the sign bit. *)
Definition washr (w : width) (x y : Z) : Z :=
  if Zpos w <=? wrap w y then (if msb w x then modulus w - 1 else 0)
  else wrap w (signed w x / 2 ^ wrap w y).

(** Left rotation reduces the shift amount modulo the width. *)
Definition wrotl (w : width) (x y : Z) : Z :=
  let k := wrap w y mod Zpos w in
  wrap w (wrap w x * 2 ^ k + wrap w x / 2 ^ (Zpos w - k)).

(** Right rotation uses the complementary left rotation amount. *)
Definition wrotr (w : width) (x y : Z) : Z :=
  wrotl w x (Zpos w - wrap w y mod Zpos w).

(** Leading-zero count returns the width on zero. *)
Definition wclz (w : width) (x : Z) : Z :=
  if wrap w x =? 0 then Zpos w else Zpos w - 1 - Z.log2 (wrap w x).

(** Trailing-zero count returns the width on zero. *)
Definition wctz (w : width) (x : Z) : Z :=
  if wrap w x =? 0 then Zpos w else Z.log2 (Z.land (wrap w x) (- wrap w x)).

(** Population count counts the set bits below the width. *)
Definition wpopcnt (w : width) (x : Z) : Z := Z.of_nat (List.length
  (List.filter (fun i => Z.testbit (wrap w x) (Z.of_nat i)) (List.seq 0 (Pos.to_nat w)))).

(** Unsigned strict comparison compares the wrapped values. *)
Definition wult (w : width) (x y : Z) : bool := wrap w x <? wrap w y.

(** Unsigned non-strict comparison compares the wrapped values. *)
Definition wule (w : width) (x y : Z) : bool := wrap w x <=? wrap w y.

(** Signed strict comparison compares the signed views. *)
Definition wslt (w : width) (x y : Z) : bool := signed w x <? signed w y.

(** Signed non-strict comparison compares the signed views. *)
Definition wsle (w : width) (x y : Z) : bool := signed w x <=? signed w y.
