(** * Scalar evolution of finite triangular loop recurrences

    Scalar recurrences describe values at successive header arrivals during one loop stay.
    For example, an additive recurrence with base zero and step one evaluates to its index.
    Builds on: BitsWord, CollectionsMap, ViewsSsa and ViewsDominated. *)

From Stdlib Require Import List Bool Arith Lia ZArith NArith PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Bits Require Import BitsWord.
From Gaulois.Graph Require Import GraphCore.
From Gaulois.Views Require Import ViewsSemantics ViewsGraph ViewsSsa ViewsDominated.
From Gaulois.Analyses Require AnalysesNumbering.
Import List.ListNotations.

(** * Integer expressions and chains of recurrences *)

(** Invariant expressions distinguish mathematical coefficients from client word literals. *)
Inductive iexpr (V : Type) : Type :=
  | IVar (x : V)
  | IConst (z : Z)
  | IWordConst (z : Z)
  | IAdd (a b : iexpr V)
  | IMul (a b : iexpr V).

Arguments IVar {V}.
Arguments IConst {V}.
Arguments IWordConst {V}.
Arguments IAdd {V}.
Arguments IMul {V}.

(** Invariant evaluation uses integer arithmetic and the supplied entry valuation. *)
Fixpoint eval_iexpr {V} (inv : V -> Z) (e : iexpr V) : Z :=
  match e with
  | IVar x => inv x
  | IConst z => z
  | IWordConst z => z
  | IAdd a b => (eval_iexpr inv a + eval_iexpr inv b)%Z
  | IMul a b => (eval_iexpr inv a * eval_iexpr inv b)%Z
  end.

(** A chain integrates additive or multiplicative steps, with total pointwise fallbacks. *)
Inductive chrec (V : Type) : Type :=
  | CInv (e : iexpr V)
  | CRec (base step : chrec V)
  | CGeo (base ratio : chrec V)
  | CSum (left right : chrec V)
  | CProduct (left right : chrec V).

Arguments CInv {V}.
Arguments CRec {V}.
Arguments CGeo {V}.
Arguments CSum {V}.
Arguments CProduct {V}.

(** Every chain starts with its base evaluated at zero and advances with the preceding step. *)
Fixpoint eval_chrec {V} (inv : V -> Z) (c : chrec V) : nat -> Z :=
  match c with
  | CInv e => fun _ => eval_iexpr inv e
  | CRec b s =>
    fix iter k :=
      match k with
      | O => eval_chrec inv b O
      | S n => (iter n + eval_chrec inv s n)%Z
      end
  | CGeo b r =>
    fix iter k :=
      match k with
      | O => eval_chrec inv b O
      | S n => (iter n * eval_chrec inv r n)%Z
      end
  | CSum a b => fun k => (eval_chrec inv a k + eval_chrec inv b k)%Z
  | CProduct a b => fun k => (eval_chrec inv a k * eval_chrec inv b k)%Z
  end.

(** Adding an invariant descends through additive bases and preserves every step. *)
Fixpoint chrec_add_invariant {V} (e : iexpr V) (c : chrec V) : chrec V :=
  match c with
  | CInv f => CInv (IAdd e f)
  | CRec b s => CRec (chrec_add_invariant e b) s
  | _ => CSum (CInv e) c
  end.

(** Addition combines additive chains structurally and retains other sums explicitly. *)
Fixpoint chrec_add {V} (a b : chrec V) {struct a} : chrec V :=
  match a with
  | CInv e => chrec_add_invariant e b
  | CRec base step =>
    match b with
    | CInv e => CRec (chrec_add base (CInv e)) step
    | CRec base' step' => CRec (chrec_add base base') (chrec_add step step')
    | _ => CSum a b
    end
  | _ => CSum a b
  end.

(** Invariant multiplication distributes through additive chains and geometric bases. *)
Fixpoint chrec_mul_invariant {V} (e : iexpr V) (c : chrec V) : chrec V :=
  match c with
  | CInv f => CInv (IMul e f)
  | CRec b s => CRec (chrec_mul_invariant e b) (chrec_mul_invariant e s)
  | CGeo b r => CGeo (chrec_mul_invariant e b) r
  | _ => CProduct (CInv e) c
  end.

(** Multiplication normalizes invariant, affine and geometric products before falling back. *)
Fixpoint chrec_mul {V} (a b : chrec V) {struct a} : chrec V :=
  match a with
  | CInv e => chrec_mul_invariant e b
  | CRec (CInv x) (CInv s) =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | CRec (CInv y) (CInv t) =>
      CRec (CInv (IMul x y))
        (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
          (CInv (IMul (IConst 2) (IMul s t))))
    | _ => CProduct a b
    end
  | CGeo base ratio =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | CGeo base' ratio' => CGeo (chrec_mul base base') (chrec_mul ratio ratio')
    | _ => CProduct a b
    end
  | _ =>
    match b with
    | CInv e => chrec_mul_invariant e a
    | _ => CProduct a b
    end
  end.

(** Scaling is multiplication by a mathematical invariant coefficient. *)
Definition chrec_scale {V} (z : Z) (c : chrec V) : chrec V :=
  chrec_mul (CInv (IConst z)) c.

Lemma eval_chrec_add_invariant {V} (inv : V -> Z) e c k :
  eval_chrec inv (chrec_add_invariant e c) k =
    (eval_iexpr inv e + eval_chrec inv c k)%Z.
Proof.
  revert k; induction c as [f|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k; cbn [chrec_add_invariant]; try reflexivity.
  induction k as [|k IHk].
  - cbn; apply IHb.
  - change ((eval_chrec inv (CRec (chrec_add_invariant e b) s) k +
      eval_chrec inv s k)%Z =
      (eval_iexpr inv e + (eval_chrec inv (CRec b s) k + eval_chrec inv s k))%Z).
    rewrite IHk; ring.
Qed.

(** * Word observations *)

(** Comparisons describe strict, inclusive and disequality continuation tests. *)
Inductive cmp_kind : Type :=
  | CmpLt
  | CmpLe
  | CmpNe.

(** Signedness chooses the representative of a wrapped word. *)
Inductive signedness : Type :=
  | Unsigned
  | Signed.

(** A word is observed through its canonical unsigned or signed representative. *)
Definition view_z (w : width) (sg : signedness) (a : Z) : Z :=
  let r := wrap w a in
  match sg with
  | Unsigned => r
  | Signed => if (r <? modulus w / 2)%Z then r else (r - modulus w)%Z
  end.

(** Continuation compares the word observations of the recurrence and its bound. *)
Definition test_holds (w : width) (sg : signedness) (c : cmp_kind) (a b : Z) : Prop :=
  let a' := view_z w sg a in
  let b' := view_z w sg b in
  match c with
  | CmpLt => (a' < b')%Z
  | CmpLe => (a' <= b')%Z
  | CmpNe => a' <> b'
  end.

(** The no-wrap range is the representable interval under the chosen signedness. *)
Definition in_range (w : width) (sg : signedness) (v : Z) : Prop :=
  match sg with
  | Unsigned => (0 <= v < modulus w)%Z
  | Signed => (- (modulus w / 2) <= v < modulus w / 2)%Z
  end.

(** * Binary first-failure search *)

(** The executable comparison agrees with the continuation proposition. *)
Definition test_check (w : width) (sg : signedness) (c : cmp_kind) (a b : Z) : bool :=
  match c with
  | CmpLt => (view_z w sg a <? view_z w sg b)%Z
  | CmpLe => (view_z w sg a <=? view_z w sg b)%Z
  | CmpNe => negb (Z.eqb (view_z w sg a) (view_z w sg b))
  end.

Lemma test_check_spec w sg c a b :
  test_check w sg c a b = true <-> test_holds w sg c a b.
Proof.
  destruct c; unfold test_check, test_holds.
  - apply Z.ltb_lt.
  - apply Z.leb_le.
  - rewrite Bool.negb_true_iff, Z.eqb_neq; reflexivity.
Qed.

(** An interval result either finds its first failure or certifies every point in the interval. *)
Definition failure_interval (f : N -> bool) (start len : N) (r : option N) : Prop :=
  match r with
  | Some t =>
    (start <= t < start + len)%N /\ f t = false /\
      forall k, (start <= k < t)%N -> f k = true
  | None => forall k, (start <= k < start + len)%N -> f k = true
  end.

(** Searching a singleton reads exactly its sole index. *)
Definition failure_one (f : N -> bool) (start : N) : option N :=
  if f start then None else Some start.

(** Sequential interval search keeps the earliest discovered failure. *)
Definition failure_append (r : option N) (next : unit -> option N) : option N :=
  match r with
  | Some t => Some t
  | None => next tt
  end.

Lemma failure_one_correct f start : failure_interval f start 1 (failure_one f start).
Proof.
  unfold failure_one; destruct (f start) eqn:Htest; cbn [failure_interval].
  - intros k Hk; assert (k = start) by lia; subst k; exact Htest.
  - split; [lia|]; split; [exact Htest|]; intros k Hk; lia.
Qed.

Lemma failure_append_correct f start n m r next :
  failure_interval f start n r ->
  (r = None -> failure_interval f (start + n) m (next tt)) ->
  failure_interval f start (n + m) (failure_append r next).
Proof.
  destruct r as [t|]; cbn [failure_interval failure_append].
  - intros [Ht [Htest Hbefore]] _; split; [lia|]; split; assumption.
  - intros Hfirst Hnext; specialize (Hnext eq_refl).
    destruct (next tt) as [t|]; cbn [failure_interval] in *.
    + destruct Hnext as [Ht [Htest Hbefore]]; split; [lia|]; split; [exact Htest|].
      intros k Hk; destruct (N.lt_ge_cases k (start + n)) as [Hleft|Hright].
      * apply Hfirst; lia.
      * apply Hbefore; lia.
    + intros k Hk; destruct (N.lt_ge_cases k (start + n)) as [Hleft|Hright].
      * apply Hfirst; lia.
      * apply Hnext; lia.
Qed.

(** Binary length recursion visits successive indices without a unary fuel representation. *)
Fixpoint failure_search (len : positive) (f : N -> bool) (start : N) : option N :=
  match len with
  | xH => failure_one f start
  | xO p =>
    failure_append (failure_search p f start)
      (fun _ => failure_search p f (start + N.pos p))
  | xI p =>
    failure_append (failure_search p f start)
      (fun _ => failure_append (failure_search p f (start + N.pos p))
        (fun _ => failure_one f (start + N.pos p + N.pos p)))
  end.

Lemma binary_length_even p : N.pos (xO p) = (N.pos p + N.pos p)%N.
Proof.
  change (N.double (N.pos p) = (N.pos p + N.pos p)%N).
  rewrite N.double_spec; lia.
Qed.

Lemma binary_length_odd p : N.pos (xI p) = (N.pos p + (N.pos p + 1))%N.
Proof.
  change (N.succ_double (N.pos p) = (N.pos p + (N.pos p + 1))%N).
  rewrite N.succ_double_spec; lia.
Qed.

(** Binary search returns the first failure in exactly its stated finite interval. *)
Theorem failure_search_correct len f start :
  failure_interval f start (N.pos len) (failure_search len f start).
Proof.
  revert start; induction len as [p IH|p IH|]; intro start; cbn [failure_search].
  - rewrite binary_length_odd.
    apply failure_append_correct; [apply IH|]; intro Hnone.
    apply failure_append_correct; [apply IH|]; intro Hnone'.
    apply failure_one_correct.
  - rewrite binary_length_even.
    apply failure_append_correct; [apply IH|]; intro Hnone; apply IH.
  - apply failure_one_correct.
Qed.

(** The recurrence addition algebra computes pointwise integer addition at every index. *)
Theorem eval_chrec_add {V} (inv : V -> Z) (a b : chrec V) (k : nat) :
  eval_chrec inv (chrec_add a b) k = (eval_chrec inv a k + eval_chrec inv b k)%Z.
Proof.
  revert b k; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intros other k; cbn [chrec_add]; try reflexivity.
  - apply eval_chrec_add_invariant.
  - destruct other as [e|b t|b r|b c|b c]; try reflexivity.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval_chrec inv (CRec (chrec_add a (CInv e)) s) k +
          eval_chrec inv s k)%Z =
          (eval_chrec inv (CRec a s) k + eval_chrec inv s k + eval_iexpr inv e)%Z).
        change (eval_chrec inv (CRec (chrec_add a (CInv e)) s) k =
          (eval_chrec inv (CRec a s) k + eval_iexpr inv e)%Z) in IHk.
        rewrite IHk; ring.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval_chrec inv (CRec (chrec_add a b) (chrec_add s t)) k +
          eval_chrec inv (chrec_add s t) k)%Z =
          (eval_chrec inv (CRec a s) k + eval_chrec inv s k +
          (eval_chrec inv (CRec b t) k + eval_chrec inv t k))%Z).
        rewrite IHk, IHs; ring.
Qed.

Lemma eval_chrec_mul_invariant {V} (inv : V -> Z) e c k :
  eval_chrec inv (chrec_mul_invariant e c) k =
    (eval_iexpr inv e * eval_chrec inv c k)%Z.
Proof.
  revert k; induction c as [f|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k; cbn [chrec_mul_invariant]; try reflexivity.
  - induction k as [|k IHk].
    + cbn; apply IHb.
    + change ((eval_chrec inv
        (CRec (chrec_mul_invariant e b) (chrec_mul_invariant e s)) k +
        eval_chrec inv (chrec_mul_invariant e s) k)%Z =
        (eval_iexpr inv e * (eval_chrec inv (CRec b s) k + eval_chrec inv s k))%Z).
      rewrite IHk, IHs; ring.
  - induction k as [|k IHk].
    + cbn; apply IHb.
    + change ((eval_chrec inv (CGeo (chrec_mul_invariant e b) r) k *
        eval_chrec inv r k)%Z =
        (eval_iexpr inv e * (eval_chrec inv (CGeo b r) k * eval_chrec inv r k))%Z).
      rewrite IHk; ring.
Qed.

Lemma eval_chrec_affine {V} (inv : V -> Z) b s k :
  eval_chrec inv (CRec b (CInv s)) k =
    (eval_chrec inv b O + Z.of_nat k * eval_iexpr inv s)%Z.
Proof.
  induction k as [|k IHk].
  - cbn; ring.
  - change ((eval_chrec inv (CRec b (CInv s)) k + eval_iexpr inv s)%Z =
      (eval_chrec inv b O + Z.of_nat (S k) * eval_iexpr inv s)%Z).
    rewrite IHk, Nat2Z.inj_succ; ring.
Qed.

Lemma eval_chrec_affine_product {V} (inv : V -> Z) x s y t k :
  eval_chrec inv
    (CRec (CInv (IMul x y))
      (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
        (CInv (IMul (IConst 2) (IMul s t))))) k =
    (eval_chrec inv (CRec (CInv x) (CInv s)) k *
      eval_chrec inv (CRec (CInv y) (CInv t)) k)%Z.
Proof.
  induction k as [|k IHk]; [reflexivity|].
  change ((eval_chrec inv
    (CRec (CInv (IMul x y))
      (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
        (CInv (IMul (IConst 2) (IMul s t))))) k +
      eval_chrec inv
        (CRec (CInv (IAdd (IAdd (IMul x t) (IMul y s)) (IMul s t)))
          (CInv (IMul (IConst 2) (IMul s t)))) k)%Z =
    ((eval_chrec inv (CRec (CInv x) (CInv s)) k + eval_iexpr inv s) *
      (eval_chrec inv (CRec (CInv y) (CInv t)) k + eval_iexpr inv t))%Z).
  rewrite IHk, !eval_chrec_affine.
  change (((eval_iexpr inv x + Z.of_nat k * eval_iexpr inv s) *
      (eval_iexpr inv y + Z.of_nat k * eval_iexpr inv t) +
      (eval_iexpr inv x * eval_iexpr inv t + eval_iexpr inv y * eval_iexpr inv s +
        eval_iexpr inv s * eval_iexpr inv t +
        Z.of_nat k * (2 * (eval_iexpr inv s * eval_iexpr inv t))))%Z =
    ((eval_iexpr inv x + Z.of_nat k * eval_iexpr inv s + eval_iexpr inv s) *
      (eval_iexpr inv y + Z.of_nat k * eval_iexpr inv t + eval_iexpr inv t))%Z).
  ring.
Qed.

(** The recurrence multiplication algebra computes pointwise products at every index. *)
Theorem eval_chrec_mul {V} (inv : V -> Z) (a b : chrec V) (k : nat) :
  eval_chrec inv (chrec_mul a b) k = (eval_chrec inv a k * eval_chrec inv b k)%Z.
Proof.
  assert (Hright : forall c e k, eval_chrec inv (chrec_mul_invariant e c) k =
    (eval_chrec inv c k * eval_iexpr inv e)%Z).
  { intros c e j; rewrite eval_chrec_mul_invariant; ring. }
  revert b k; induction a as [e|a IHa s IHs|a IHa r IHr|a IHa b IHb|a IHa b IHb];
    intros other k.
  - apply eval_chrec_mul_invariant.
  - destruct other as [e|b t|b t|b t|b t].
    + destruct a, s; apply Hright.
    + destruct a, s, b, t; try reflexivity; apply eval_chrec_affine_product.
    + destruct a, s; reflexivity.
    + destruct a, s; reflexivity.
    + destruct a, s; reflexivity.
  - destruct other as [e|b s|b t|b s|b s]; try reflexivity.
    + apply Hright.
    + induction k as [|k IHk].
      * cbn; apply IHa.
      * change ((eval_chrec inv (CGeo (chrec_mul a b) (chrec_mul r t)) k *
          eval_chrec inv (chrec_mul r t) k)%Z =
          ((eval_chrec inv (CGeo a r) k * eval_chrec inv r k) *
            (eval_chrec inv (CGeo b t) k * eval_chrec inv t k))%Z).
        change (eval_chrec inv (CGeo (chrec_mul a b) (chrec_mul r t)) k =
          (eval_chrec inv (CGeo a r) k * eval_chrec inv (CGeo b t) k)%Z) in IHk.
        rewrite IHk, IHr; ring.
  - destruct other; try reflexivity.
    apply Hright.
  - destruct other; try reflexivity.
    apply Hright.
Qed.

(** Scaling multiplies every point of a recurrence by its mathematical coefficient. *)
Theorem eval_chrec_scale {V} (inv : V -> Z) (z : Z) (c : chrec V) (k : nat) :
  eval_chrec inv (chrec_scale z c) k = (z * eval_chrec inv c k)%Z.
Proof.
  unfold chrec_scale; rewrite eval_chrec_mul; reflexivity.
Qed.

(** * Sign normalization *)

(** Sign normalization changes word literals and leaves mathematical coefficients intact. *)
Fixpoint signed_iexpr {V} (w : width) (sg : signedness) (e : iexpr V) : iexpr V :=
  match e with
  | IVar x => IVar x
  | IConst z => IConst z
  | IWordConst z => IConst (view_z w sg z)
  | IAdd a b => IAdd (signed_iexpr w sg a) (signed_iexpr w sg b)
  | IMul a b => IMul (signed_iexpr w sg a) (signed_iexpr w sg b)
  end.

(** Every recurrence node normalizes its invariant leaves structurally. *)
Fixpoint signed_chrec {V} (w : width) (sg : signedness) (c : chrec V) : chrec V :=
  match c with
  | CInv e => CInv (signed_iexpr w sg e)
  | CRec b s => CRec (signed_chrec w sg b) (signed_chrec w sg s)
  | CGeo b r => CGeo (signed_chrec w sg b) (signed_chrec w sg r)
  | CSum a b => CSum (signed_chrec w sg a) (signed_chrec w sg b)
  | CProduct a b => CProduct (signed_chrec w sg a) (signed_chrec w sg b)
  end.

Lemma wrap_view_z w sg z : wrap w (view_z w sg z) = wrap w z.
Proof.
  unfold view_z; destruct sg; [apply wrap_wrap|].
  destruct (wrap w z <? modulus w / 2)%Z; [apply wrap_wrap|].
  replace (wrap w z - modulus w)%Z with (wrap w z + (-1) * modulus w)%Z by ring.
  rewrite wrap_add_modulus; apply wrap_wrap.
Qed.

(** Sign normalization preserves an invariant expression's wrapped value. *)
Theorem signed_iexpr_wrap {V} (w : width) (sg : signedness)
    (inv : V -> Z) (e : iexpr V) :
  wrap w (eval_iexpr inv e) =
  wrap w (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg e)).
Proof.
  induction e as [x|z|z|a IHa b IHb|a IHa b IHb]; cbn.
  - symmetry; apply wrap_view_z.
  - reflexivity.
  - symmetry; apply wrap_view_z.
  - rewrite (wrap_add w (eval_iexpr inv a) (eval_iexpr inv b)).
    rewrite (wrap_add w
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg a))
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg b))).
    rewrite IHa, IHb; reflexivity.
  - rewrite (wrap_mul w (eval_iexpr inv a) (eval_iexpr inv b)).
    rewrite (wrap_mul w
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg a))
      (eval_iexpr (fun y => view_z w sg (inv y)) (signed_iexpr w sg b))).
    rewrite IHa, IHb; reflexivity.
Qed.

(** Sign normalization preserves a recurrence's wrapped value at every index. *)
Theorem signed_chrec_wrap {V} (w : width) (sg : signedness)
    (inv : V -> Z) (c : chrec V) (k : nat) :
  wrap w (eval_chrec inv c k) =
  wrap w (eval_chrec (fun y => view_z w sg (inv y)) (signed_chrec w sg c) k).
Proof.
  revert k; induction c as [e|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb];
    intro k.
  - apply signed_iexpr_wrap.
  - induction k as [|k IHk]; [apply IHb|].
    change (wrap w (eval_chrec inv (CRec b s) k + eval_chrec inv s k) =
      wrap w (eval_chrec (fun y => view_z w sg (inv y))
        (CRec (signed_chrec w sg b) (signed_chrec w sg s)) k +
        eval_chrec (fun y => view_z w sg (inv y)) (signed_chrec w sg s) k))%Z.
    rewrite (wrap_add w), IHk, IHs; symmetry; apply wrap_add.
  - induction k as [|k IHk]; [apply IHb|].
    change (wrap w (eval_chrec inv (CGeo b r) k * eval_chrec inv r k) =
      wrap w (eval_chrec (fun y => view_z w sg (inv y))
        (CGeo (signed_chrec w sg b) (signed_chrec w sg r)) k *
        eval_chrec (fun y => view_z w sg (inv y)) (signed_chrec w sg r) k))%Z.
    rewrite (wrap_mul w), IHk, IHr; symmetry; apply wrap_mul.
  - cbn; rewrite (wrap_add w), IHa, IHb; symmetry; apply wrap_add.
  - cbn; rewrite (wrap_mul w), IHa, IHb; symmetry; apply wrap_mul.
Qed.

(** * Exact wrapped affine trip counts *)

(** A whole word modulus is a binary period for every affine word sequence. *)
Definition word_period (w : width) : positive := Pos.pow 2 w.

Lemma word_period_modulus w : Z.of_N (N.pos (word_period w)) = modulus w.
Proof.
  exact (Pos2Z.inj_pow 2 w).
Qed.

(** Congruent integers have identical observations under either signedness. *)
Lemma view_z_congruent w sg a b : wrap w a = wrap w b -> view_z w sg a = view_z w sg b.
Proof.
  intro Heq; unfold view_z; rewrite Heq; reflexivity.
Qed.

(** Reducing an affine index modulo the binary period leaves the observed word unchanged. *)
Theorem affine_word_period w a step k :
  wrap w (a + step * Z.of_N k) =
  wrap w (a + step * Z.of_N (k mod N.pos (word_period w))).
Proof.
  rewrite N2Z.inj_mod, word_period_modulus.
  pose proof (Z.div_mod (Z.of_N k) (modulus w) (modulus_nonzero w)) as Hdiv.
  replace (a + step * Z.of_N k)%Z with
    (a + step * (Z.of_N k mod modulus w) +
      (step * (Z.of_N k / modulus w)) * modulus w)%Z by nia.
  apply wrap_add_modulus.
Qed.

(** An affine predicate reads its base once and computes word observations from binary indices. *)
Definition affine_test w sg cmp a step bound (k : N) : bool :=
  test_check w sg cmp (a + step * Z.of_N k) bound.

Lemma affine_test_period w sg cmp a step bound k :
  affine_test w sg cmp a step bound k =
    affine_test w sg cmp a step bound (k mod N.pos (word_period w)).
Proof.
  unfold affine_test, test_check.
  rewrite (view_z_congruent w sg _ _ (affine_word_period w a step k)); reflexivity.
Qed.

Lemma affine_test_zero_step w sg cmp a step bound : wrap w step = 0%Z ->
  forall k, affine_test w sg cmp a step bound k = affine_test w sg cmp a step bound 0.
Proof.
  intros Hzero k; unfold affine_test.
  assert (Heq : wrap w (a + step * Z.of_N k) = wrap w a).
  { rewrite wrap_add, wrap_mul, Hzero; cbn [Z.mul]; rewrite wrap_0, Z.add_0_r;
      apply wrap_wrap. }
  unfold test_check.
  rewrite (view_z_congruent w sg _ _ Heq), Z.mul_0_r, Z.add_0_r; reflexivity.
Qed.

(** Affine search handles constant words directly and otherwise searches one word period. *)
Definition affine_first_failure w sg cmp a step bound : option N :=
  if (wrap w step =? 0)%Z then
    failure_one (affine_test w sg cmp a step bound) 0
  else failure_search (word_period w) (affine_test w sg cmp a step bound) 0.

(** A successful affine search identifies the exact first failed wrapped comparison. *)
Theorem affine_first_failure_sound w sg cmp a step bound t :
  affine_first_failure w sg cmp a step bound = Some t ->
  (forall k, (k < t)%N -> affine_test w sg cmp a step bound k = true) /\
    affine_test w sg cmp a step bound t = false.
Proof.
  unfold affine_first_failure; destruct (wrap w step =? 0)%Z eqn:Hzero.
  - unfold failure_one; destruct (affine_test w sg cmp a step bound 0) eqn:Htest;
      intro Heq; [discriminate|]; inversion Heq; subst t.
    split; [intros k Hk; lia|exact Htest].
  - intro Hsearch.
    pose proof (failure_search_correct (word_period w)
      (affine_test w sg cmp a step bound) 0) as Hcorrect.
    rewrite Hsearch in Hcorrect; cbn [failure_interval] in Hcorrect.
    destruct Hcorrect as [Ht [Htest Hbefore]]; split; [|exact Htest].
    intros k Hk; apply Hbefore; lia.
Qed.

(** No affine failure means that every index satisfies the wrapped continuation test. *)
Theorem affine_first_failure_none w sg cmp a step bound :
  affine_first_failure w sg cmp a step bound = None <->
    forall k, affine_test w sg cmp a step bound k = true.
Proof.
  unfold affine_first_failure; destruct (wrap w step =? 0)%Z eqn:Hzero.
  - apply Z.eqb_eq in Hzero; unfold failure_one.
    destruct (affine_test w sg cmp a step bound 0) eqn:Htest; split.
    + intros _ k; rewrite (affine_test_zero_step w sg cmp a step bound Hzero); exact Htest.
    + intro Hall; reflexivity.
    + discriminate.
    + intro Hall; specialize (Hall 0%N); congruence.
  - pose proof (failure_search_correct (word_period w)
      (affine_test w sg cmp a step bound) 0) as Hcorrect.
    destruct (failure_search (word_period w) (affine_test w sg cmp a step bound) 0)
      as [t|] eqn:Hsearch; cbn [failure_interval] in Hcorrect; split.
    + discriminate.
    + intro Hall; destruct Hcorrect as [_ [Htest _]]; specialize (Hall t); congruence.
    + intros _ k; rewrite affine_test_period; apply Hcorrect.
      split; [apply N.le_0_l|]; rewrite N.add_0_l; apply N.mod_lt; discriminate.
    + intro Hall; reflexivity.
Qed.

(** Trip counts are exact first failures for additive recurrences with invariant steps. *)
Definition trip_count {V} (inv : V -> Z) (w : width) (sg : signedness) (c : cmp_kind)
    (ch : chrec V) (bound : iexpr V) : option N :=
  match ch with
  | CRec base (CInv step) =>
    affine_first_failure w sg c (eval_chrec inv base O) (eval_iexpr inv step)
      (eval_iexpr inv bound)
  | _ => None
  end.

(** Successful trip counting establishes first failure without any no-wrap premise. *)
Theorem trip_count_first_failure {V} (inv : V -> Z) w sg cmp ch bound t :
  trip_count inv w sg cmp ch bound = Some t ->
  (forall k, (N.of_nat k < t)%N ->
    test_holds w sg cmp (eval_chrec inv ch k) (eval_iexpr inv bound)) /\
  ~ test_holds w sg cmp (eval_chrec inv ch (N.to_nat t)) (eval_iexpr inv bound).
Proof.
  destruct ch as [e|base step|base ratio|a b|a b]; try discriminate.
  destruct step as [step|a b|a b|a b|a b]; try discriminate.
  intro Hcount; apply affine_first_failure_sound in Hcount.
  destruct Hcount as [Hbefore Hfailed]; split.
  - intros k Hk; rewrite eval_chrec_affine; apply test_check_spec.
    specialize (Hbefore (N.of_nat k) Hk); unfold affine_test in Hbefore.
    rewrite nat_N_Z, Z.mul_comm in Hbefore; exact Hbefore.
  - rewrite eval_chrec_affine; intro Hholds; apply test_check_spec in Hholds.
    unfold affine_test in Hfailed; rewrite N_nat_Z, Z.mul_comm in Hholds; congruence.
Qed.

(** A first failed affine comparison is returned at its unique earliest index. *)
Theorem affine_first_failure_complete w sg cmp a step bound t :
  (forall k, (k < t)%N -> affine_test w sg cmp a step bound k = true) ->
  affine_test w sg cmp a step bound t = false ->
  affine_first_failure w sg cmp a step bound = Some t.
Proof.
  intros Hbefore Hfailed.
  destruct (affine_first_failure w sg cmp a step bound) as [j|] eqn:Hsearch.
  - destruct (affine_first_failure_sound w sg cmp a step bound j Hsearch)
      as [Hbefore' Hfailed'].
    assert (j = t).
    { destruct (N.lt_trichotomy j t) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
      - specialize (Hbefore j Hlt); congruence.
      - specialize (Hbefore' t Hgt); congruence. }
    subst j; reflexivity.
  - pose proof (proj1 (affine_first_failure_none w sg cmp a step bound) Hsearch t)
      as Hholds; congruence.
Qed.

(** An affine trip counter returns None exactly for a continuation that never fails. *)
Theorem trip_count_affine_none {V} (inv : V -> Z) w sg cmp base step bound :
  trip_count inv w sg cmp (CRec base (CInv step)) bound = None <->
  forall k, test_holds w sg cmp
    (eval_chrec inv (CRec base (CInv step)) k) (eval_iexpr inv bound).
Proof.
  unfold trip_count.
  rewrite affine_first_failure_none; split.
  - intros Hall k; rewrite eval_chrec_affine; apply test_check_spec.
    specialize (Hall (N.of_nat k)); unfold affine_test in Hall.
    rewrite nat_N_Z, Z.mul_comm in Hall; exact Hall.
  - intros Hall k; unfold affine_test; apply test_check_spec.
    specialize (Hall (N.to_nat k));
      rewrite eval_chrec_affine, N_nat_Z, Z.mul_comm in Hall; exact Hall.
Qed.

(** * Separate no-wrap evidence *)

(** The representable-range checker is exact for both signednesses. *)
Definition in_range_check (w : width) (sg : signedness) (z : Z) : bool :=
  match sg with
  | Unsigned => (0 <=? z)%Z && (z <? modulus w)%Z
  | Signed => (- (modulus w / 2) <=? z)%Z && (z <? modulus w / 2)%Z
  end.

Lemma in_range_check_spec w sg z : in_range_check w sg z = true <-> in_range w sg z.
Proof.
  destruct sg; unfold in_range_check, in_range;
    rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

(** No-wrap checking bounds the mathematical base, endpoint and invariant bound independently. *)
Definition nowrap_check {V} (w : width) (sg : signedness) (inv : V -> Z) (ch : chrec V)
    (bound : iexpr V) (t : N) : bool :=
  match ch with
  | CRec base (CInv step) =>
    let a := eval_chrec inv base O in
    let s := eval_iexpr inv step in
    in_range_check w sg a && in_range_check w sg (a + s * Z.of_N t) &&
      in_range_check w sg (eval_iexpr inv bound)
  | _ => false
  end.

Lemma affine_range_between w sg a step t k :
  (0 <= k <= t)%Z -> in_range w sg a -> in_range w sg (a + step * t) ->
  in_range w sg (a + step * k).
Proof.
  intros Hindex Hbase Hend; destruct sg; cbn [in_range] in *;
    destruct (Z.le_gt_cases 0 step); nia.
Qed.

(** Endpoint checking proves that every recurrence value through the endpoint stays in range. *)
Theorem nowrap_check_sound {V} w sg (inv : V -> Z) ch bound t :
  nowrap_check w sg inv ch bound t = true ->
  (forall k, (N.of_nat k <= t)%N -> in_range w sg (eval_chrec inv ch k)) /\
    in_range w sg (eval_iexpr inv bound).
Proof.
  destruct ch as [e|base step|base ratio|a b|a b]; try discriminate.
  destruct step as [step|a b|a b|a b|a b]; try discriminate.
  unfold nowrap_check; rewrite !Bool.andb_true_iff, !in_range_check_spec.
  intros [[Hbase Hend] Hbound]; split; [|exact Hbound].
  intros k Hindex; rewrite eval_chrec_affine, Z.mul_comm; eapply affine_range_between;
    [|exact Hbase|exact Hend].
  apply N2Z.inj_le in Hindex; rewrite nat_N_Z in Hindex; lia.
Qed.

(** Exact wrapped trip counts and separate no-wrap evidence establish all four arithmetic claims. *)
Theorem trip_count_sound {V} (inv : V -> Z) (w : width) (sg : signedness) (cmp : cmp_kind)
    (ch : chrec V) (bound : iexpr V) (t : N) :
  trip_count inv w sg cmp ch bound = Some t -> nowrap_check w sg inv ch bound t = true ->
  (forall k, (N.of_nat k < t)%N ->
    test_holds w sg cmp (eval_chrec inv ch k) (eval_iexpr inv bound)) /\
  ~ test_holds w sg cmp (eval_chrec inv ch (N.to_nat t)) (eval_iexpr inv bound) /\
  (forall k, (N.of_nat k <= t)%N -> in_range w sg (eval_chrec inv ch k)) /\
  in_range w sg (eval_iexpr inv bound).
Proof.
  intros Htrip Hnowrap.
  destruct (trip_count_first_failure inv w sg cmp ch bound t Htrip) as [Hbefore Hfailed].
  destruct (nowrap_check_sound w sg inv ch bound t Hnowrap) as [Hrange Hbound].
  split; [exact Hbefore|]; split; [exact Hfailed|]; split; assumption.
Qed.

(** * Loop interfaces and finite recognition plans *)

(** A loop test describes the comparison whose truth permits another iteration. *)
Record loop_test (V : Type) : Type := LoopTest {
  t_cmp : cmp_kind;
  t_sign : signedness;
  t_lhs : V;
  t_bound : iexpr V
}.

Arguments LoopTest {V}.
Arguments t_cmp {V}.
Arguments t_sign {V}.
Arguments t_lhs {V}.
Arguments t_bound {V}.

(** A simple loop has one designated entry and one designated feedback edge. *)
Record loop_view (S O N E V K C : Type) : Type := LoopView {
  lssa : ssa_view S O N E V K C;
  lheader : N;
  lbody : N -> bool;
  lentry : E;
  lback : E;
  ltest : option (loop_test V)
}.

Arguments LoopView {S O N E V K C}.
Arguments lssa {S O N E V K C}.
Arguments lheader {S O N E V K C}.
Arguments lbody {S O N E V K C}.
Arguments lentry {S O N E V K C}.
Arguments lback {S O N E V K C}.
Arguments ltest {S O N E V K C}.

(** A client supplies its word observation and the operation flags used by recognition. *)
Record scev_ops (K C : Type) : Type := ScevOps {
  width_of : width;
  to_Z : C -> Z;
  add_op : K -> bool;
  mul_op : K -> bool;
  const_op : K -> option Z
}.

Arguments ScevOps {K C}.
Arguments width_of {K C}.
Arguments to_Z {K C}.
Arguments add_op {K C}.
Arguments mul_op {K C}.
Arguments const_op {K C}.

(** Client observations are canonical and recognized operations agree with wrapped arithmetic. *)
Record scev_ops_laws {K C} (so : scev_ops K C)
    (op_eval : K -> list C -> option C) : Prop := {
  to_Z_canonical : forall c, to_Z so c = wrap (width_of so) (to_Z so c);
  add_laws : forall o a b r, add_op so o = true -> op_eval o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (to_Z so a + to_Z so b);
  mul_laws : forall o a b r, mul_op so o = true -> op_eval o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (to_Z so a * to_Z so b);
  const_laws : forall o z r, const_op so o = Some z -> op_eval o nil = Some r ->
    to_Z so r = wrap (width_of so) z
}.

(** The raw invariant valuation retains the client's canonical word observations. *)
Definition inv_env {S O N E V K C} (lv : loop_view S O N E V K C)
    (so : scev_ops K C) (s : S) (y : V) : Z :=
  match val (lssa lv) s y with
  | Some d => to_Z so d
  | None => 0%Z
  end.

(** Signed invariant valuation changes representatives without changing wrapped words. *)
Definition signed_inv_env {S O N E V K C} (lv : loop_view S O N E V K C)
    (so : scev_ops K C) (sg : signedness) (s : S) (y : V) : Z :=
  view_z (width_of so) sg (inv_env lv so s y).

(** Header arrivals count feedback edges since the most recent loop entry. *)
Definition stay_arrivals {S O N E V K C} (EE : encoding E)
    (lv : loop_view S O N E V K C) (es : list E) : nat :=
  arrivals_since (fun e => Pos.eqb (encode EE e) (encode EE (lentry lv)))
    (fun e => Pos.eqb (encode EE e) (encode EE (lback lv))) es.

(** Plan expressions name outside invariants, completed header recurrences and local operations. *)
Inductive scev_expr (V : Type) : Type :=
  | SOutside (x : V)
  | SPhi (x : V)
  | SAdd (result : V) (left right : scev_expr V)
  | SMul (result : V) (left right : scev_expr V)
  | SConst (result : V) (z : Z).

Arguments SOutside {V}.
Arguments SPhi {V}.
Arguments SAdd {V}.
Arguments SMul {V}.
Arguments SConst {V}.

(** A distinguished feedback occurrence adds, multiplies or doubles the current phi. *)
Inductive scev_update : Type :=
  | SAddUpdate
  | SMulUpdate
  | SDoubleUpdate.

(** A binding records its phi, selected incoming values and distinguished feedback operation. *)
Record scev_binding (V : Type) : Type := ScevBinding {
  sb_phi : V;
  sb_base : V;
  sb_update_value : V;
  sb_kind : scev_update;
  sb_other : option (scev_expr V);
  sb_phi_first : bool
}.

(** A finite plan orders dependencies before their users and ends with its target. *)
Record scev_plan (V : Type) : Type := ScevPlan {
  sp_bindings : list (scev_binding V);
  sp_target : V
}.

Arguments ScevBinding {V}.
Arguments ScevPlan {V}.
Arguments sb_phi {V}.
Arguments sb_base {V}.
Arguments sb_update_value {V}.
Arguments sb_kind {V}.
Arguments sb_other {V}.
Arguments sb_phi_first {V}.
Arguments sp_bindings {V}.
Arguments sp_target {V}.

(** Variable leaves of an invariant expression determine its loop-stability obligation. *)
Fixpoint iexpr_variables {V} (e : iexpr V) : list V :=
  match e with
  | IVar x => [x]
  | IConst _ => []
  | IWordConst _ => []
  | IAdd a b => iexpr_variables a ++ iexpr_variables b
  | IMul a b => iexpr_variables a ++ iexpr_variables b
  end.

(** Every expression exposes the value represented at its root. *)
Definition scev_expr_root {V} (e : scev_expr V) : V :=
  match e with
  | SOutside x => x
  | SPhi x => x
  | SConst x _ => x
  | SAdd x _ _ => x
  | SMul x _ _ => x
  end.

(** Expression operation results identify the local equations needed at feedback. *)
Fixpoint scev_expr_operations {V} (e : scev_expr V) : list V :=
  match e with
  | SOutside _ => []
  | SPhi _ => []
  | SAdd x a b => x :: scev_expr_operations a ++ scev_expr_operations b
  | SMul x a b => x :: scev_expr_operations a ++ scev_expr_operations b
  | SConst x _ => [x]
  end.

(** A plan requires equations for every update and every operation in its dependencies. *)
Definition scev_plan_operations {V} (p : scev_plan V) : list V :=
  flat_map (fun b => sb_update_value b ::
    match sb_other b with
    | Some e => scev_expr_operations e
    | None => []
    end) (sp_bindings p).

(** * Prepared expression compilation *)

(** Expression codes retain tags, result values and both ordered child codes. *)
Fixpoint scev_expr_code {V} (EV : encoding V) (e : scev_expr V) : positive :=
  encode (list_encoding positive_encoding)
    (match e with
    | SOutside x => [1%positive; encode EV x]
    | SPhi x => [2%positive; encode EV x]
    | SAdd x a b => [3%positive; encode EV x; scev_expr_code EV a; scev_expr_code EV b]
    | SMul x a b => [4%positive; encode EV x; scev_expr_code EV a; scev_expr_code EV b]
    | SConst x z => [5%positive; encode EV x; encode Z_encoding z]
    end).

(** Codes distinguish complete expression trees, including operand order and literal values. *)
Theorem scev_expr_code_injective {V} (EV : encoding V) a b :
  scev_expr_code EV a = scev_expr_code EV b -> a = b.
Proof.
  revert b; induction a as [x|x|x a IHa b IHb|x a IHa b IHb|x z];
    intros other Hcode; destruct other; cbn [scev_expr_code] in Hcode;
    apply (encode_injective (list_encoding positive_encoding)) in Hcode;
    inversion Hcode; subst; f_equal;
    first [apply (encode_injective EV); assumption |
      apply (encode_injective Z_encoding); assumption | apply IHa; assumption |
      apply IHb; assumption].
Qed.

(** Prepared expressions cache their structural code before the compilation work begins. *)
Inductive scev_prepared_expr (V : Type) : Type :=
  | POutside (code : positive) (phis : FinSet.t V) (x : V)
  | PPhi (code : positive) (phis : FinSet.t V) (x : V)
  | PAdd (code : positive) (phis : FinSet.t V) (x : V) (a b : scev_prepared_expr V)
  | PMul (code : positive) (phis : FinSet.t V) (x : V) (a b : scev_prepared_expr V)
  | PConst (code : positive) (phis : FinSet.t V) (x : V) (z : Z).

Arguments POutside {V}.
Arguments PPhi {V}.
Arguments PAdd {V}.
Arguments PMul {V}.
Arguments PConst {V}.

(** Reading a prepared node's code never traverses either child. *)
Definition scev_prepared_code {V} (e : scev_prepared_expr V) : positive :=
  match e with
  | POutside p _ _ => p
  | PPhi p _ _ => p
  | PAdd p _ _ _ _ => p
  | PMul p _ _ _ _ => p
  | PConst p _ _ _ => p
  end.

(** Prepared phi supports are shared finite tries, independent of the current rank or valuation. *)
Definition scev_prepared_phis {V} (e : scev_prepared_expr V) : FinSet.t V :=
  match e with
  | POutside _ phis _ => phis
  | PPhi _ phis _ => phis
  | PAdd _ phis _ _ _ => phis
  | PMul _ phis _ _ _ => phis
  | PConst _ phis _ _ => phis
  end.

(** Smart binary preparation consumes completed children without visiting their descendants. *)
Definition scev_prepare_binary {V} (EV : encoding V) (multiply : bool) x
    (a b : scev_prepared_expr V) : scev_prepared_expr V :=
  let code := encode (list_encoding positive_encoding)
    [if multiply then 4%positive else 3%positive; encode EV x;
     scev_prepared_code a; scev_prepared_code b] in
  let phis := FinSet.union EV (scev_prepared_phis a) (scev_prepared_phis b) in
  if multiply then PMul code phis x a b else PAdd code phis x a b.

(** External ingestion inspects trees; integrated source preparation links completed smart nodes. *)
Fixpoint scev_prepare_expr {V} (EV : encoding V) (e : scev_expr V) : scev_prepared_expr V :=
  match e with
  | SOutside x => POutside
      (encode (list_encoding positive_encoding) [1%positive; encode EV x]) FinSet.empty x
  | SPhi x => PPhi
      (encode (list_encoding positive_encoding) [2%positive; encode EV x])
      (FinSet.add EV x FinSet.empty) x
  | SAdd x a b => scev_prepare_binary EV false x
      (scev_prepare_expr EV a) (scev_prepare_expr EV b)
  | SMul x a b => scev_prepare_binary EV true x
      (scev_prepare_expr EV a) (scev_prepare_expr EV b)
  | SConst x z => PConst
      (encode (list_encoding positive_encoding) [5%positive; encode EV x; encode Z_encoding z])
      FinSet.empty x z
  end.

(** Preparation stores exactly the structural code of the source expression. *)
Theorem scev_prepare_expr_code {V} (EV : encoding V) e :
  scev_prepared_code (scev_prepare_expr EV e) = scev_expr_code EV e.
Proof.
  induction e; cbn [scev_prepare_expr scev_prepare_binary scev_prepared_code scev_expr_code];
    try reflexivity; rewrite IHe1, IHe2; reflexivity.
Qed.

(** Declarative expression translation reads only previously completed phi recurrences. *)
Fixpoint scev_translate_expr {V} (lookup : V -> option (chrec V)) (e : scev_expr V)
    : option (chrec V) :=
  match e with
  | SOutside x => Some (CInv (IVar x))
  | SPhi x => lookup x
  | SAdd _ a b =>
    match scev_translate_expr lookup a, scev_translate_expr lookup b with
    | Some a', Some b' => Some (chrec_add a' b')
    | _, _ => None
    end
  | SMul _ a b =>
    match scev_translate_expr lookup a, scev_translate_expr lookup b with
    | Some a', Some b' => Some (chrec_mul a' b')
    | _, _ => None
    end
  | SConst _ z => Some (CInv (IWordConst z))
  end.

(** Compilation memoizes completed structural expressions and never expands a cached dependency. *)
Fixpoint scev_compile_expr {V} (lookup : V -> option (chrec V))
    (e : scev_prepared_expr V) (memo : Map.t positive (chrec V))
    : option (chrec V * Map.t positive (chrec V)) :=
  let code := scev_prepared_code e in
  match Map.get positive_encoding code memo with
  | Some c => Some (c, memo)
  | None =>
    let finish := fun c memo' => Some (c, Map.set positive_encoding code c memo') in
    match e with
    | POutside _ _ x => finish (CInv (IVar x)) memo
    | PPhi _ _ x =>
      match lookup x with
      | Some c => finish c memo
      | None => None
      end
    | PAdd _ _ _ a b =>
      match scev_compile_expr lookup a memo with
      | Some (a', memo') =>
        match scev_compile_expr lookup b memo' with
        | Some (b', memo'') => finish (chrec_add a' b') memo''
        | None => None
        end
      | None => None
      end
    | PMul _ _ _ a b =>
      match scev_compile_expr lookup a memo with
      | Some (a', memo') =>
        match scev_compile_expr lookup b memo' with
        | Some (b', memo'') => finish (chrec_mul a' b') memo''
        | None => None
        end
      | None => None
      end
    | PConst _ _ _ z => finish (CInv (IWordConst z)) memo
    end
  end.

(** A compilation cache agrees with declarative translation at every stored structural key. *)
Definition scev_compile_memo_laws {V} (EV : encoding V)
    (lookup : V -> option (chrec V)) (memo : Map.t positive (chrec V)) : Prop :=
  forall e c, Map.get positive_encoding (scev_expr_code EV e) memo = Some c ->
    scev_translate_expr lookup e = Some c.

Lemma scev_compile_memo_empty {V} (EV : encoding V) (lookup : V -> option (chrec V)) :
  scev_compile_memo_laws EV lookup Map.empty.
Proof.
  intros e c Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma scev_compile_memo_set {V} (EV : encoding V) (lookup : V -> option (chrec V))
    memo e c :
  scev_compile_memo_laws EV lookup memo -> scev_translate_expr lookup e = Some c ->
  scev_compile_memo_laws EV lookup (Map.set positive_encoding (scev_expr_code EV e) c memo).
Proof.
  intros Hmemo Hvalue other d Hget.
  destruct (Pos.eq_dec (scev_expr_code EV other) (scev_expr_code EV e)) as [Heq|Hne].
  - apply scev_expr_code_injective in Heq; subst other.
    rewrite Map.get_set_same in Hget; inversion Hget; subst d; exact Hvalue.
  - rewrite Map.get_set_other in Hget by exact Hne; apply Hmemo; exact Hget.
Qed.

(** A compiled expression returns its declarative translation and preserves cache agreement. *)
Theorem scev_compile_expr_correct {V} (EV : encoding V) (lookup : V -> option (chrec V)) e :
  forall memo, scev_compile_memo_laws EV lookup memo ->
  match scev_compile_expr lookup (scev_prepare_expr EV e) memo with
  | Some (c, memo') => scev_translate_expr lookup e = Some c /\
      scev_compile_memo_laws EV lookup memo'
  | None => scev_translate_expr lookup e = None
  end.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; intros memo Hmemo;
    cbn [scev_prepare_expr scev_prepare_binary scev_compile_expr scev_prepared_code];
    rewrite ?scev_prepare_expr_code;
    match goal with
    | |- context [Map.get positive_encoding ?code memo] =>
      destruct (Map.get positive_encoding code memo) eqn:Hget
    end.
  - split; [eapply Hmemo; exact Hget|exact Hmemo].
  - split; [reflexivity|].
    exact (scev_compile_memo_set EV lookup memo (SOutside x) (CInv (IVar x))
      Hmemo eq_refl).
  - split; [eapply Hmemo; exact Hget|exact Hmemo].
  - destruct (lookup x) as [c|] eqn:Hlookup; [|exact Hlookup].
    split; [exact Hlookup|].
    exact (scev_compile_memo_set EV lookup memo (SPhi x) c Hmemo Hlookup).
  - split; [eapply Hmemo; exact Hget|exact Hmemo].
  - specialize (IHa memo Hmemo).
    destruct (scev_compile_expr lookup (scev_prepare_expr EV a) memo)
      as [[ca ma]|] eqn:Ha.
    + destruct IHa as [Hta Hma]; specialize (IHb ma Hma).
      destruct (scev_compile_expr lookup (scev_prepare_expr EV b) ma)
        as [[cb mb]|] eqn:Hb.
      * destruct IHb as [Htb Hmb]; split.
        -- cbn [scev_translate_expr]; rewrite Hta, Htb; reflexivity.
        -- apply (scev_compile_memo_set EV lookup mb (SAdd x a b) (chrec_add ca cb));
             [exact Hmb|].
           cbn [scev_translate_expr]; rewrite Hta, Htb; reflexivity.
      * cbn [scev_translate_expr]; rewrite Hta, IHb; reflexivity.
    + cbn [scev_translate_expr]; rewrite IHa; reflexivity.
  - split; [eapply Hmemo; exact Hget|exact Hmemo].
  - specialize (IHa memo Hmemo).
    destruct (scev_compile_expr lookup (scev_prepare_expr EV a) memo)
      as [[ca ma]|] eqn:Ha.
    + destruct IHa as [Hta Hma]; specialize (IHb ma Hma).
      destruct (scev_compile_expr lookup (scev_prepare_expr EV b) ma)
        as [[cb mb]|] eqn:Hb.
      * destruct IHb as [Htb Hmb]; split.
        -- cbn [scev_translate_expr]; rewrite Hta, Htb; reflexivity.
        -- apply (scev_compile_memo_set EV lookup mb (SMul x a b) (chrec_mul ca cb));
             [exact Hmb|].
           cbn [scev_translate_expr]; rewrite Hta, Htb; reflexivity.
      * cbn [scev_translate_expr]; rewrite Hta, IHb; reflexivity.
    + cbn [scev_translate_expr]; rewrite IHa; reflexivity.
  - split; [eapply Hmemo; exact Hget|exact Hmemo].
  - split; [reflexivity|].
    exact (scev_compile_memo_set EV lookup memo (SConst x z) (CInv (IWordConst z))
      Hmemo eq_refl).
Qed.

(** Prepared expression compilation has exactly the declarative option result. *)
Theorem scev_compile_expr_agrees {V} (EV : encoding V) (lookup : V -> option (chrec V)) e :
  option_map fst (scev_compile_expr lookup (scev_prepare_expr EV e) Map.empty) =
    scev_translate_expr lookup e.
Proof.
  pose proof (scev_compile_expr_correct EV lookup e Map.empty
    (scev_compile_memo_empty EV lookup)) as Hcorrect.
  destruct (scev_compile_expr lookup (scev_prepare_expr EV e) Map.empty) as [[c memo]|];
    cbn [option_map fst]; [symmetry; exact (proj1 Hcorrect)|symmetry; exact Hcorrect].
Qed.

(** Translation depends pointwise on the previously compiled phi environment. *)
Lemma scev_translate_expr_extensional {V} (left right : V -> option (chrec V)) e :
  (forall x, left x = right x) -> scev_translate_expr left e = scev_translate_expr right e.
Proof.
  intro Heq; induction e; cbn [scev_translate_expr]; try reflexivity; try apply Heq;
    rewrite IHe1, IHe2; reflexivity.
Qed.

(** Binding translation integrates its other expression or uses mathematical doubling. *)
Definition scev_translate_binding {V} (lookup : V -> option (chrec V)) (b : scev_binding V)
    : option (chrec V) :=
  let base := CInv (IVar (sb_base b)) in
  match sb_kind b with
  | SDoubleUpdate => Some (CGeo base (CInv (IConst 2)))
  | SAddUpdate =>
    match sb_other b with
    | Some e => option_map (CRec base) (scev_translate_expr lookup e)
    | None => None
    end
  | SMulUpdate =>
    match sb_other b with
    | Some e => option_map (CGeo base) (scev_translate_expr lookup e)
    | None => None
    end
  end.

(** Plan preparation caches expression codes before any binding is compiled. *)
Definition scev_prepare_bindings {V} (EV : encoding V) (bs : list (scev_binding V)) :=
  map (fun b => (b, option_map (scev_prepare_expr EV) (sb_other b))) bs.

(** Prepared bindings compile with indexed completed phis and memoized expressions. *)
Definition scev_compile_binding {V} (EV : encoding V) (env : Map.t V (chrec V))
    (b : scev_binding V) (other : option (scev_prepared_expr V)) : option (chrec V) :=
  let base := CInv (IVar (sb_base b)) in
  let compile := fun e => option_map fst
    (scev_compile_expr (fun x => Map.get EV x env) e Map.empty) in
  match sb_kind b with
  | SDoubleUpdate => Some (CGeo base (CInv (IConst 2)))
  | SAddUpdate =>
    match other with
    | Some e => option_map (CRec base) (compile e)
    | None => None
    end
  | SMulUpdate =>
    match other with
    | Some e => option_map (CGeo base) (compile e)
    | None => None
    end
  end.

Lemma scev_compile_binding_agrees {V} (EV : encoding V) env b :
  scev_compile_binding EV env b (option_map (scev_prepare_expr EV) (sb_other b)) =
    scev_translate_binding (fun x => Map.get EV x env) b.
Proof.
  unfold scev_compile_binding, scev_translate_binding.
  destruct (sb_kind b); [| |reflexivity]; destruct (sb_other b) as [e|];
    try reflexivity; cbn [option_map]; rewrite scev_compile_expr_agrees; reflexivity.
Qed.

(** The binding traversal compiles each rank once and indexes its completed recurrence by phi. *)
Fixpoint scev_compile_bindings {V} (EV : encoding V)
    (bs : list (scev_binding V * option (scev_prepared_expr V)))
    (env : Map.t V (chrec V)) : option (Map.t V (chrec V)) :=
  match bs with
  | [] => Some env
  | (b, other) :: rest =>
    match scev_compile_binding EV env b other with
    | Some c => scev_compile_bindings EV rest (Map.set EV (sb_phi b) c env)
    | None => None
    end
  end.

(** The indexed compiler returns the completed target recurrence after one binding traversal. *)
Definition scev_compile_plan {V} (EV : encoding V) (plan : scev_plan V) : option (chrec V) :=
  match scev_compile_bindings EV (scev_prepare_bindings EV (sp_bindings plan)) Map.empty with
  | Some env => Map.get EV (sp_target plan) env
  | None => None
  end.

(** Declarative updates retain exactly the most recent binding for each encoded phi. *)
Definition scev_translation_set {V} (EV : encoding V) (lookup : V -> option (chrec V)) x c :=
  fun y => if Pos.eqb (encode EV y) (encode EV x) then Some c else lookup y.

(** The reference compiler translates bindings in list order using a pointwise environment. *)
Fixpoint scev_translate_bindings {V} (EV : encoding V) (bs : list (scev_binding V))
    (lookup : V -> option (chrec V)) : option (V -> option (chrec V)) :=
  match bs with
  | [] => Some lookup
  | b :: rest =>
    match scev_translate_binding lookup b with
    | Some c => scev_translate_bindings EV rest (scev_translation_set EV lookup (sb_phi b) c)
    | None => None
    end
  end.

(** The declarative plan result is its target in the completed translation environment. *)
Definition scev_translate_plan {V} (EV : encoding V) (p : scev_plan V) : option (chrec V) :=
  match scev_translate_bindings EV (sp_bindings p) (fun _ => None) with
  | Some lookup => lookup (sp_target p)
  | None => None
  end.

Lemma scev_translation_set_agrees {V} (EV : encoding V) env lookup x c :
  (forall y, Map.get EV y env = lookup y) ->
  forall y, Map.get EV y (Map.set EV x c env) = scev_translation_set EV lookup x c y.
Proof.
  intros Heq y; unfold scev_translation_set.
  destruct (Pos.eqb (encode EV y) (encode EV x)) eqn:Hcode.
  - apply Pos.eqb_eq in Hcode; apply (encode_injective EV) in Hcode; subst y.
    apply Map.get_set_same.
  - rewrite Map.get_set_other; [apply Heq|].
    intro Hxy; subst y; rewrite Pos.eqb_refl in Hcode; discriminate.
Qed.

Lemma scev_translate_binding_extensional {V} (left right : V -> option (chrec V)) b :
  (forall x, left x = right x) ->
  scev_translate_binding left b = scev_translate_binding right b.
Proof.
  intro Heq; unfold scev_translate_binding; destruct (sb_kind b);
    try reflexivity; destruct (sb_other b) as [e|]; try reflexivity;
    rewrite (scev_translate_expr_extensional left right e Heq); reflexivity.
Qed.

(** Indexed binding compilation agrees with the reference environment at every completed rank. *)
Theorem scev_compile_bindings_agrees {V} (EV : encoding V) bs :
  forall env lookup, (forall y, Map.get EV y env = lookup y) ->
  match scev_compile_bindings EV (scev_prepare_bindings EV bs) env,
      scev_translate_bindings EV bs lookup with
  | Some env', Some lookup' => forall y, Map.get EV y env' = lookup' y
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction bs as [|b bs IH]; intros env lookup Heq; [exact Heq|].
  cbn [scev_prepare_bindings map scev_compile_bindings scev_translate_bindings].
  rewrite scev_compile_binding_agrees.
  rewrite (scev_translate_binding_extensional (fun y => Map.get EV y env) lookup b Heq).
  destruct (scev_translate_binding lookup b) as [c|]; [|exact I].
  apply IH; apply scev_translation_set_agrees; exact Heq.
Qed.

(** The public indexed compiler implements precisely the stated recurrence translation. *)
Theorem scev_compile_plan_agrees {V} (EV : encoding V) p :
  scev_compile_plan EV p = scev_translate_plan EV p.
Proof.
  unfold scev_compile_plan, scev_translate_plan.
  pose proof (scev_compile_bindings_agrees EV (sp_bindings p) Map.empty (fun _ => None)
    (fun y => Map.get_empty EV y)) as Hagrees.
  destruct (scev_compile_bindings EV (scev_prepare_bindings EV (sp_bindings p)) Map.empty)
    as [env|];
    destruct (scev_translate_bindings EV (sp_bindings p) (fun _ => None)) as [lookup|];
    try contradiction; [apply Hagrees|reflexivity].
Qed.

(** * Prepared finite inventory *)

(** Inventory preparation reads each source definition and home once before recognition. *)
Fixpoint scev_inventory_index {S O N E V K C} (EV : encoding V)
    (sv : ssa_view S O N E V K C) (inventory : list V) : Map.t V (N * definition N V K) :=
  match inventory with
  | [] => Map.empty
  | x :: rest => Map.set EV x (home sv x, def sv x) (scev_inventory_index EV sv rest)
  end.

(** The prepared inventory has a binding exactly for each listed source value. *)
Theorem scev_inventory_index_mem {S O N E V K C} (EV : encoding V)
    (sv : ssa_view S O N E V K C) inventory x :
  Map.mem EV x (scev_inventory_index EV sv inventory) = true <-> In x inventory.
Proof.
  induction inventory as [|y rest IH].
  - cbn [scev_inventory_index]; unfold Map.mem; rewrite Map.get_empty;
      cbn; split; [discriminate|contradiction].
  - cbn [scev_inventory_index]; destruct (Pos.eq_dec (encode EV x) (encode EV y))
      as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x; unfold Map.mem;
        rewrite Map.get_set_same; cbn; split; [intro H; left; reflexivity|intro H; reflexivity].
    + unfold Map.mem at 1; rewrite Map.get_set_other.
      * fold (Map.mem EV x (scev_inventory_index EV sv rest)); rewrite IH.
        cbn; split; [intro Hin; right; exact Hin|intros [Heq|Hin]; [|exact Hin]].
        subst y; contradiction.
      * intro Heq; subst y; contradiction.
Qed.

(** An indexed value retains its exact source home and full ordered definition operands. *)
Theorem scev_inventory_index_get {S O N E V K C} (EV : encoding V)
    (sv : ssa_view S O N E V K C) inventory x :
  In x inventory ->
    Map.get EV x (scev_inventory_index EV sv inventory) = Some (home sv x, def sv x).
Proof.
  induction inventory as [|y rest IH]; [contradiction|].
  cbn [scev_inventory_index]; intros Hin.
  destruct (Pos.eq_dec (encode EV x) (encode EV y)) as [Heq|Hne].
  - apply (encode_injective EV) in Heq; subst x; apply Map.get_set_same.
  - rewrite Map.get_set_other; [apply IH|].
    + destruct Hin as [Heq|Hin]; [subst y; contradiction|exact Hin].
    + intro Heq; subst y; contradiction.
Qed.

(** Missing inventory values cannot acquire fabricated source metadata. *)
Theorem scev_inventory_index_none {S O N E V K C} (EV : encoding V)
    (sv : ssa_view S O N E V K C) inventory x :
  ~ In x inventory -> Map.get EV x (scev_inventory_index EV sv inventory) = None.
Proof.
  intro Hmissing.
  destruct (Map.get EV x (scev_inventory_index EV sv inventory)) as [info|] eqn:Hget;
    [|reflexivity].
  exfalso; apply Hmissing; apply (proj1 (scev_inventory_index_mem EV sv inventory x)).
  unfold Map.mem; rewrite Hget; reflexivity.
Qed.

(** Prepared plan ranks remember duplicate detection and the final binding without rescanning. *)
Record scev_rank_index (V : Type) : Type := ScevRankIndex {
  sri_ranks : Map.t V nat;
  sri_distinct : bool;
  sri_final : option V
}.

Arguments ScevRankIndex {V}.
Arguments sri_ranks {V}.
Arguments sri_distinct {V}.
Arguments sri_final {V}.

(** Rank preparation indexes the first binding position and checks every duplicate phi. *)
Fixpoint scev_rank_index_from {V} (EV : encoding V) (rank : nat)
    (bs : list (scev_binding V)) : scev_rank_index V :=
  match bs with
  | [] => ScevRankIndex Map.empty true None
  | b :: rest =>
    let tail := scev_rank_index_from EV (S rank) rest in
    ScevRankIndex (Map.set EV (sb_phi b) rank (sri_ranks tail))
      (negb (Map.mem EV (sb_phi b) (sri_ranks tail)) && sri_distinct tail)
      (match sri_final tail with
      | Some x => Some x
      | None => Some (sb_phi b)
      end)
  end.

Lemma scev_rank_index_mem {V} (EV : encoding V) bs rank x :
  Map.mem EV x (sri_ranks (scev_rank_index_from EV rank bs)) = true <->
    In x (map sb_phi bs).
Proof.
  revert rank; induction bs as [|b bs IH]; intro rank.
  - cbn [scev_rank_index_from sri_ranks]; unfold Map.mem; rewrite Map.get_empty;
      cbn; split; [discriminate|contradiction].
  - cbn [scev_rank_index_from sri_ranks map].
    destruct (Pos.eq_dec (encode EV x) (encode EV (sb_phi b))) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x; unfold Map.mem;
        rewrite Map.get_set_same; cbn; split; [intro H; left; reflexivity|intro H; reflexivity].
    + unfold Map.mem at 1; rewrite Map.get_set_other.
      * fold (Map.mem EV x (sri_ranks (scev_rank_index_from EV (S rank) bs))).
        rewrite IH; split; [intro Hin; right; exact Hin|intros [Heq|Hin]; [|exact Hin]].
        rewrite Heq in Hne; contradiction.
      * intro Heq; subst x; contradiction.
Qed.

(** The prepared duplicate flag is exactly the declarative uniqueness condition. *)
Theorem scev_rank_index_distinct {V} (EV : encoding V) bs rank :
  sri_distinct (scev_rank_index_from EV rank bs) = true <-> NoDup (map sb_phi bs).
Proof.
  revert rank; induction bs as [|b bs IH]; intro rank.
  - cbn; split; [intro H; constructor|intro H; reflexivity].
  - cbn [scev_rank_index_from sri_distinct map].
    rewrite Bool.andb_true_iff, Bool.negb_true_iff, IH; split.
    + intros [Hmissing Hdistinct]; constructor; [|exact Hdistinct].
      intro Hin; apply (proj2 (scev_rank_index_mem EV bs (S rank) (sb_phi b))) in Hin.
      congruence.
    + intro Hdistinct; inversion Hdistinct as [|x xs Hfresh Htail]; subst.
      split; [|exact Htail].
      destruct (Map.mem EV (sb_phi b)
        (sri_ranks (scev_rank_index_from EV (S rank) bs))) eqn:Hmember; [|reflexivity].
      apply scev_rank_index_mem in Hmember; contradiction.
Qed.

(** Rank lookups coincide with actual list positions when the phi inventory is duplicate-free. *)
Theorem scev_rank_index_get {V} (EV : encoding V) bs rank i b :
  NoDup (map sb_phi bs) -> nth_error bs i = Some b ->
  Map.get EV (sb_phi b) (sri_ranks (scev_rank_index_from EV rank bs)) = Some (rank + i)%nat.
Proof.
  revert rank i b; induction bs as [|a bs IH]; intros rank [|i] b Hdistinct Hnth;
    cbn [nth_error] in Hnth; try discriminate.
  - inversion Hnth; subst b; cbn [scev_rank_index_from sri_ranks].
    rewrite Nat.add_0_r; apply Map.get_set_same.
  - inversion Hdistinct as [|x xs Hfresh Htail]; subst.
    cbn [scev_rank_index_from sri_ranks]; rewrite Map.get_set_other.
    + replace (rank + S i)%nat with (S rank + i)%nat by lia; apply IH; assumption.
    + intro Heq; apply Hfresh; rewrite <- Heq; apply in_map.
      apply nth_error_In with (n := i); exact Hnth.
Qed.

(** The static index stores inventory metadata, both argument maps and all phi ranks. *)
Record scev_static_index (N V K : Type) : Type := ScevStaticIndex {
  ssi_values : Map.t V (N * definition N V K);
  ssi_entry : Map.t nat V;
  ssi_back : Map.t nat V;
  ssi_phi : scev_rank_index V
}.

Arguments ScevStaticIndex {N V K}.
Arguments ssi_values {N V K}.
Arguments ssi_entry {N V K}.
Arguments ssi_back {N V K}.
Arguments ssi_phi {N V K}.

(** Static preparation reads both edge lists once and reuses the established positional index. *)
Definition scev_prepare_index {S O N E V K C} (EV : encoding V) (inventory : list V)
    (lv : loop_view S O N E V K C) (p : scev_plan V) : scev_static_index N V K :=
  ScevStaticIndex (scev_inventory_index EV (lssa lv) inventory)
    (AnalysesNumbering.NumberingIndex.argument_index (edge_args (lssa lv) (lentry lv)))
    (AnalysesNumbering.NumberingIndex.argument_index (edge_args (lssa lv) (lback lv)))
    (scev_rank_index_from EV 0 (sp_bindings p)).

(** The prepared edge maps return exactly the selected source argument at each phi position. *)
Theorem scev_prepare_index_arguments {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) p i :
  Map.get nat_encoding i (ssi_entry (scev_prepare_index EV inventory lv p)) =
    nth_error (edge_args (lssa lv) (lentry lv)) i /\
  Map.get nat_encoding i (ssi_back (scev_prepare_index EV inventory lv p)) =
    nth_error (edge_args (lssa lv) (lback lv)) i.
Proof.
  split; apply AnalysesNumbering.NumberingIndex.argument_index_get.
Qed.

(** * Indexed plan checking *)

(** Key comparisons use the explicit injective encoding of their own carrier. *)
Definition scev_key_eq {A} (EA : encoding A) (x y : A) : bool :=
  Pos.eqb (encode EA x) (encode EA y).

Lemma scev_key_eq_spec {A} (EA : encoding A) x y : scev_key_eq EA x y = true <-> x = y.
Proof.
  unfold scev_key_eq; rewrite Pos.eqb_eq; split;
    [apply (encode_injective EA)|intro Heq; subst y; reflexivity].
Qed.

(** Prepared roots expose their source value without traversing the expression. *)
Definition scev_prepared_root {V} (e : scev_prepared_expr V) : V :=
  match e with
  | POutside _ _ x => x
  | PPhi _ _ x => x
  | PAdd _ _ x _ _ => x
  | PMul _ _ x _ _ => x
  | PConst _ _ x _ => x
  end.

Lemma scev_prepare_expr_root {V} (EV : encoding V) e :
  scev_prepared_root (scev_prepare_expr EV e) = scev_expr_root e.
Proof.
  destruct e; reflexivity.
Qed.

(** A binary result must have its actual ordered operands and the appropriate operation flag. *)
Definition scev_binary_check {N V K} (EV : encoding V) (body : N -> bool)
    (values : Map.t V (N * definition N V K)) (flag : K -> bool) x left right : bool :=
  match Map.get EV x values with
  | Some (n, Op o [a; b]) => body n && flag o && scev_key_eq EV a left && scev_key_eq EV b right
  | _ => false
  end.

(** A literal result must be an inside-body nullary operation with the exact tagged integer. *)
Definition scev_constant_check {N V K C} (EV : encoding V) (body : N -> bool)
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C) x z : bool :=
  match Map.get EV x values with
  | Some (n, Op o []) =>
    body n &&
      match const_op so o with
      | Some z' => Z.eqb z' z
      | None => false
      end
  | _ => false
  end.

(** A checker result carries exactly the completed-phi references used by its expression. *)
Definition scev_expr_check_result (V : Type) : Type := (bool * FinSet.t V)%type.

(** Expression checking memoizes shared syntax and collects its lower-ranked phi dependencies. *)
Fixpoint scev_check_expr {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) (rank : nat)
    (e : scev_prepared_expr V) (memo : Map.t positive (scev_expr_check_result V))
    : scev_expr_check_result V * Map.t positive (scev_expr_check_result V) :=
  let code := scev_prepared_code e in
  match Map.get positive_encoding code memo with
  | Some result => (result, memo)
  | None =>
    let finish := fun (result : scev_expr_check_result V)
      (memo' : Map.t positive (scev_expr_check_result V)) =>
      (result, Map.set positive_encoding code result memo') in
    let failed := (false, FinSet.empty) in
    let binary := fun (flag : K -> bool) (x : V) (a b : scev_prepared_expr V)
      (recurse_a recurse_b : Map.t positive (scev_expr_check_result V) ->
        scev_expr_check_result V * Map.t positive (scev_expr_check_result V)) =>
      if scev_binary_check EV body (ssi_values ix) flag x
        (scev_prepared_root a) (scev_prepared_root b) then
        let '(ra, memo') := recurse_a memo in
        if fst ra then
          let '(rb, memo'') := recurse_b memo' in
          finish (fst rb, FinSet.union EV (snd ra) (snd rb)) memo''
        else finish failed memo'
      else finish failed memo in
    match e with
    | POutside _ _ x =>
      finish ((match Map.get EV x (ssi_values ix) with
        | Some (n, _) => negb (body n)
        | None => false
        end), FinSet.empty) memo
    | PPhi _ _ x =>
      finish (Map.mem EV x (ssi_values ix) &&
        match Map.get EV x (sri_ranks (ssi_phi ix)) with
        | Some i => Nat.ltb i rank
        | None => false
        end, FinSet.add EV x FinSet.empty) memo
    | PAdd _ _ x a b => binary (add_op so) x a b
        (scev_check_expr EV body ix so rank a) (scev_check_expr EV body ix so rank b)
    | PMul _ _ x a b => binary (mul_op so) x a b
        (scev_check_expr EV body ix so rank a) (scev_check_expr EV body ix so rank b)
    | PConst _ _ x z => finish
        (scev_constant_check EV body (ssi_values ix) so x z, FinSet.empty) memo
    end
  end.

(** Ordinary feedback consumes exactly the designated phi and the checked other-expression root. *)
Definition scev_check_update {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) (rank : nat)
    (b : scev_binding V) (other : option (scev_prepared_expr V)) : option (FinSet.t V) :=
  match sb_kind b, other with
  | SDoubleUpdate, None =>
    if sb_phi_first b && scev_binary_check EV body (ssi_values ix) (add_op so)
      (sb_update_value b) (sb_phi b) (sb_phi b) then Some FinSet.empty else None
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    let root := scev_prepared_root e in
    let flag :=
      match sb_kind b with
      | SAddUpdate => add_op so
      | _ => mul_op so
      end in
    let left := if sb_phi_first b then sb_phi b else root in
    let right := if sb_phi_first b then root else sb_phi b in
    if negb (scev_key_eq EV root (sb_phi b)) &&
      scev_binary_check EV body (ssi_values ix) flag (sb_update_value b) left right then
      let '(result, _) := scev_check_expr EV body ix so rank e Map.empty in
      if fst result then Some (snd result) else None
    else None
  | _, _ => None
  end.

(** Binding checking validates the exact phi position, both incoming values and both homes. *)
Definition scev_check_binding {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (rank : nat) (b : scev_binding V) (other : option (scev_prepared_expr V))
    : option (FinSet.t V) :=
  match Map.get EV (sb_phi b) (ssi_values ix), Map.get EV (sb_base b) (ssi_values ix),
      Map.get EV (sb_update_value b) (ssi_values ix) with
  | Some (phi_home, Param header i), Some (base_home, _), Some (update_home, _) =>
    if scev_key_eq EN phi_home (lheader lv) && scev_key_eq EN header (lheader lv) &&
      negb (lbody lv base_home) && lbody lv update_home then
      match Map.get nat_encoding i (ssi_entry ix), Map.get nat_encoding i (ssi_back ix) with
      | Some base, Some update =>
        if scev_key_eq EV base (sb_base b) && scev_key_eq EV update (sb_update_value b) then
          scev_check_update EV (lbody lv) ix so rank b other
        else None
      | _, _ => None
      end
    else None
  | _, _, _ => None
  end.

(** Successful forward checking emits a reverse dependency list without rescanning bindings. *)
Fixpoint scev_check_bindings {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (rank : nat) (bs : list (scev_binding V * option (scev_prepared_expr V)))
    (checked : list (V * FinSet.t V)) : option (list (V * FinSet.t V)) :=
  match bs with
  | [] => Some checked
  | (b, other) :: rest =>
    match scev_check_binding EN EV lv so ix rank b other with
    | Some deps => scev_check_bindings EN EV lv so ix (Nat.succ rank) rest
        ((sb_phi b, deps) :: checked)
    | None => None
    end
  end.

(** Reverse reachability rejects every binding unrelated to the target recurrence. *)
Fixpoint scev_check_dependencies {V} (EV : encoding V) (rows : list (V * FinSet.t V))
    (needed : FinSet.t V) : bool :=
  match rows with
  | [] => true
  | (x, deps) :: rest =>
    if FinSet.mem EV x needed then
      scev_check_dependencies EV rest (FinSet.union EV needed deps)
    else false
  end.

(** The checker validates inventory, unique ranks, exact source shape and target connectivity. *)
Definition scev_plan_check_index {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (plan : scev_plan V) : bool :=
  if Map.mem EV (sp_target plan) (ssi_values ix) && sri_distinct (ssi_phi ix) then
    match sri_final (ssi_phi ix) with
    | Some target =>
      if scev_key_eq EV target (sp_target plan) then
        match scev_check_bindings EN EV lv so ix 0
          (scev_prepare_bindings EV (sp_bindings plan)) [] with
        | Some checked =>
          scev_check_dependencies EV checked (FinSet.add EV (sp_target plan) FinSet.empty)
        | None => false
        end
      else false
    | None => false
    end
  else false.

(** Public plan checking prepares its source and rank indexes once before traversing the plan. *)
Definition scev_plan_check {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (inventory : list V) (lv : loop_view S O N E V K C) (so : scev_ops K C)
    (plan : scev_plan V) : bool :=
  scev_plan_check_index EN EV lv so (scev_prepare_index EV inventory lv plan) plan.

(** * Local semantic obligations *)

(** Loop laws supply exact local source equations and frames for actual stays. *)
Record loop_view_laws {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) (inventory : list V)
    (so : scev_ops K C) (lv : loop_view S O N E V K C) : Prop := {
  l_ssa : ssa_view_laws m (lssa lv);
  l_strict : strict_ssa_laws m (lssa lv);
  l_header_not_entry : ~ In (lheader lv) (Graph.entries (cfg (base (lssa lv))));
  l_entry_edge : In (lentry lv) (edges_of (cfg (base (lssa lv)))) /\
    Graph.target (cfg (base (lssa lv))) (lentry lv) = lheader lv /\
    lbody lv (Graph.source (cfg (base (lssa lv))) (lentry lv)) = false;
  l_back_edge : In (lback lv) (edges_of (cfg (base (lssa lv)))) /\
    Graph.target (cfg (base (lssa lv))) (lback lv) = lheader lv /\
    lbody lv (Graph.source (cfg (base (lssa lv))) (lback lv)) = true;
  l_simple : forall e, In e (edges_of (cfg (base (lssa lv)))) ->
    Graph.target (cfg (base (lssa lv))) e = lheader lv -> e = lentry lv \/ e = lback lv;
  l_header_inside : lbody lv (lheader lv) = true;
  l_initial_outside : forall n,
    In n (Graph.entries (cfg (base (lssa lv)))) -> lbody lv n = false;
  l_single_ingress : forall e, In e (edges_of (cfg (base (lssa lv)))) ->
    lbody lv (Graph.source (cfg (base (lssa lv))) e) = false ->
    lbody lv (Graph.target (cfg (base (lssa lv))) e) = true -> e = lentry lv;
  l_phi_binding : forall s tr s' e x i,
    reachable_state m s -> step m s tr s' -> taken (base (lssa lv)) s tr s' e ->
    Graph.target (cfg (base (lssa lv))) e = lheader lv ->
    def (lssa lv) x = Param (lheader lv) i ->
    val (lssa lv) s' x =
      match nth_error (edge_args (lssa lv) e) i with
      | Some y => val (lssa lv) s y
      | None => None
      end;
  l_phi_stay : forall s tr s' x i,
    reachable_state m s -> step m s tr s' -> stays (base (lssa lv)) s tr s' ->
    point (base (lssa lv)) s = lheader lv -> def (lssa lv) x = Param (lheader lv) i ->
    val (lssa lv) s' x = val (lssa lv) s x;
  l_test_outside : forall t y, ltest lv = Some t ->
    In y (iexpr_variables (t_bound t)) -> lbody lv (home (lssa lv) y) = false;
  l_back_test : forall s tr s' t,
    reachable_state m s -> step m s tr s' ->
    taken (base (lssa lv)) s tr s' (lback lv) -> ltest lv = Some t ->
    exists c, val (lssa lv) s (t_lhs t) = Some c /\
      test_holds (width_of so) (t_sign t) (t_cmp t) (to_Z so c)
        (eval_iexpr (inv_env lv so s) (t_bound t));
  l_plan_op_at_back : forall s tr s' plan x o args c,
    reachable_state m s -> step m s tr s' -> taken (base (lssa lv)) s tr s' (lback lv) ->
    scev_plan_check EN EV inventory lv so plan = true ->
    In x (scev_plan_operations plan) -> def (lssa lv) x = Op o args ->
    val (lssa lv) s x = Some c ->
    exists cs, Forall2 (fun y d => val (lssa lv) s y = Some d) args cs /\
      op_eval (lssa lv) o cs = Some c
}.

(** Successful inventory lookup identifies both membership and the exact source metadata. *)
Theorem scev_inventory_index_sound {S O N E V K C} (EV : encoding V)
    (sv : ssa_view S O N E V K C) inventory x info :
  Map.get EV x (scev_inventory_index EV sv inventory) = Some info ->
    In x inventory /\ info = (home sv x, def sv x).
Proof.
  intro Hget.
  assert (Hin : In x inventory).
  { apply (proj1 (scev_inventory_index_mem EV sv inventory x));
      unfold Map.mem; rewrite Hget; reflexivity. }
  split; [exact Hin|].
  pose proof (scev_inventory_index_get EV sv inventory x Hin) as Hsource; congruence.
Qed.

(** Binary-node acceptance requires the exact inside-body definition and ordered operands. *)
Theorem scev_binary_check_correct {N V K} (EV : encoding V) (body : N -> bool)
    (values : Map.t V (N * definition N V K)) flag x a b :
  scev_binary_check EV body values flag x a b = true <->
    exists n o, Map.get EV x values = Some (n, Op o [a; b]) /\ body n = true /\ flag o = true.
Proof.
  unfold scev_binary_check.
  destruct (Map.get EV x values) as [[n d]|] eqn:Hget.
  - destruct d as [o args|header i|].
    + destruct args as [|u [|v [|w rest]]].
      all: try (split; [discriminate|intros [n' [o' [Hbad _]]];
        discriminate Hbad]).
      rewrite !Bool.andb_true_iff, !scev_key_eq_spec; split.
      * intros [[[Hbody Hflag] Hu] Hv]; subst u v.
        exists n, o; split; [reflexivity|split; assumption].
      * intros [n' [o' [Hsource [Hbody Hflag]]]].
        inversion Hsource; subst n' o' u v.
        repeat split; try assumption; reflexivity.
    + split; [discriminate|intros [n' [o' [Hbad _]]]; discriminate Hbad].
    + split; [discriminate|intros [n' [o' [Hbad _]]]; discriminate Hbad].
  - split; [discriminate|intros [n [o [Hbad _]]]; discriminate Hbad].
Qed.

(** Constant-node acceptance requires an inside-body nullary operation with the exact literal. *)
Theorem scev_constant_check_correct {N V K C} (EV : encoding V) (body : N -> bool)
    (values : Map.t V (N * definition N V K)) (so : scev_ops K C) x z :
  scev_constant_check EV body values so x z = true <->
    exists n o, Map.get EV x values = Some (n, Op o []) /\ body n = true /\
      const_op so o = Some z.
Proof.
  unfold scev_constant_check.
  destruct (Map.get EV x values) as [[n d]|] eqn:Hget.
  - destruct d as [o [|a args]|header i|].
    + destruct (const_op so o) as [z'|] eqn:Hconst.
      * rewrite Bool.andb_true_iff, Z.eqb_eq; split.
        -- intros [Hbody Heq]; subst z'.
           exists n, o; split; [reflexivity|split; assumption].
        -- intros [n' [o' [Hsource [Hbody Hliteral]]]].
           inversion Hsource; subst n' o'.
           split; [exact Hbody|congruence].
      * rewrite Bool.andb_false_r; split; [discriminate|].
        intros [n' [o' [Hsource [_ Hliteral]]]].
        inversion Hsource; subst n' o'; congruence.
    + split; [discriminate|intros [n' [o' [Hbad _]]]; discriminate Hbad].
    + split; [discriminate|intros [n' [o' [Hbad _]]]; discriminate Hbad].
    + split; [discriminate|intros [n' [o' [Hbad _]]]; discriminate Hbad].
  - split; [discriminate|intros [n [o [Hbad _]]]; discriminate Hbad].
Qed.

(** * Expression-checker cache agreement *)

(** The reference expression checker follows the declarative tree and its ordered dependencies. *)
Fixpoint scev_expr_check_reference {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) (rank : nat) (e : scev_expr V)
    : scev_expr_check_result V :=
  let binary := fun (flag : K -> bool) (x : V) (a b : scev_expr V)
    (check_a check_b : scev_expr_check_result V) =>
    if scev_binary_check EV body (ssi_values ix) flag x (scev_expr_root a) (scev_expr_root b) then
      if fst check_a then (fst check_b, FinSet.union EV (snd check_a) (snd check_b))
      else (false, FinSet.empty)
    else (false, FinSet.empty) in
  match e with
  | SOutside x =>
    ((match Map.get EV x (ssi_values ix) with
    | Some (n, _) => negb (body n)
    | None => false
    end), FinSet.empty)
  | SPhi x =>
    (Map.mem EV x (ssi_values ix) &&
      match Map.get EV x (sri_ranks (ssi_phi ix)) with
      | Some i => Nat.ltb i rank
      | None => false
      end, FinSet.add EV x FinSet.empty)
  | SAdd x a b => binary (add_op so) x a b
      (scev_expr_check_reference EV body ix so rank a)
      (scev_expr_check_reference EV body ix so rank b)
  | SMul x a b => binary (mul_op so) x a b
      (scev_expr_check_reference EV body ix so rank a)
      (scev_expr_check_reference EV body ix so rank b)
  | SConst x z => (scev_constant_check EV body (ssi_values ix) so x z, FinSet.empty)
  end.

(** Checker caches store the exact reference result for every complete structural key. *)
Definition scev_check_memo_laws {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) (rank : nat)
    (memo : Map.t positive (scev_expr_check_result V)) : Prop :=
  forall e result, Map.get positive_encoding (scev_expr_code EV e) memo = Some result ->
    scev_expr_check_reference EV body ix so rank e = result.

Lemma scev_check_memo_empty {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank :
  scev_check_memo_laws EV body ix so rank Map.empty.
Proof.
  intros e result Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma scev_check_memo_set {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank memo e result :
  scev_check_memo_laws EV body ix so rank memo ->
  scev_expr_check_reference EV body ix so rank e = result ->
  scev_check_memo_laws EV body ix so rank
    (Map.set positive_encoding (scev_expr_code EV e) result memo).
Proof.
  intros Hmemo Hresult other value Hget.
  destruct (Pos.eq_dec (scev_expr_code EV other) (scev_expr_code EV e)) as [Heq|Hne].
  - apply scev_expr_code_injective in Heq; subst other.
    rewrite Map.get_set_same in Hget; inversion Hget; subst value; exact Hresult.
  - rewrite Map.get_set_other in Hget by exact Hne; apply Hmemo; exact Hget.
Qed.

(** Expression-checker correctness couples its exact result to the resulting cache invariant. *)
Definition scev_check_expr_laws {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank (e : scev_expr V) : Prop :=
  forall memo, scev_check_memo_laws EV body ix so rank memo ->
  let '(result, memo') := scev_check_expr EV body ix so rank (scev_prepare_expr EV e) memo in
    scev_expr_check_reference EV body ix so rank e = result /\
      scev_check_memo_laws EV body ix so rank memo'.

(** The two binary constructors share one cache-hit, operand and preservation argument. *)
Lemma scev_check_binary_correct {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank (multiply : bool) x a b :
  scev_check_expr_laws EV body ix so rank a ->
  scev_check_expr_laws EV body ix so rank b ->
  scev_check_expr_laws EV body ix so rank
    (if multiply then SMul x a b else SAdd x a b).
Proof.
  intros IHa IHb; destruct multiply;
    match goal with
    | |- scev_check_expr_laws _ _ _ _ _ ?source => pose (original := source)
    end;
    intros memo Hmemo;
    cbn [scev_prepare_expr scev_prepare_binary scev_check_expr scev_prepared_code];
    rewrite ?scev_prepare_expr_code, ?scev_prepare_expr_root;
    match goal with
    | |- context [Map.get positive_encoding ?code memo] =>
      destruct (Map.get positive_encoding code memo) eqn:Hget
    end.
  all: try (split; [eapply (Hmemo original); exact Hget|exact Hmemo]).
  all: match goal with
    | |- context [if ?condition then _ else _] => destruct condition eqn:Hlocal
    end.
  all: try (split; [cbn [original scev_expr_check_reference]; rewrite ?Hlocal; reflexivity|];
    eapply (scev_check_memo_set EV body ix so rank memo original); [exact Hmemo|];
    cbn [original scev_expr_check_reference]; rewrite ?Hlocal; reflexivity).
  all: specialize (IHa memo Hmemo);
    destruct (scev_check_expr EV body ix so rank (scev_prepare_expr EV a) memo)
      as [[ba da] ma] eqn:Ha; destruct IHa as [Hta Hma]; destruct ba.
  all: try (split;
    [cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta; reflexivity|];
    eapply (scev_check_memo_set EV body ix so rank ma original); [exact Hma|];
    cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta; reflexivity).
  all: specialize (IHb ma Hma);
    destruct (scev_check_expr EV body ix so rank (scev_prepare_expr EV b) ma)
      as [[bb db] mb] eqn:Hb; destruct IHb as [Htb Hmb]; split.
  all: first
    [cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta, ?Htb; reflexivity|
     eapply (scev_check_memo_set EV body ix so rank mb original); [exact Hmb|];
       cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta, ?Htb; reflexivity].
Qed.

Lemma scev_check_add_correct {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank x a b :
  scev_check_expr_laws EV body ix so rank a ->
  scev_check_expr_laws EV body ix so rank b ->
  scev_check_expr_laws EV body ix so rank (SAdd x a b).
Proof.
  exact (scev_check_binary_correct EV body ix so rank false x a b).
Qed.

Lemma scev_check_mul_correct {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank x a b :
  scev_check_expr_laws EV body ix so rank a ->
  scev_check_expr_laws EV body ix so rank b ->
  scev_check_expr_laws EV body ix so rank (SMul x a b).
Proof.
  exact (scev_check_binary_correct EV body ix so rank true x a b).
Qed.

(** Prepared memoized expression checking preserves the exact tree result and cache invariant. *)
Theorem scev_check_expr_correct {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e :
  forall memo, scev_check_memo_laws EV body ix so rank memo ->
  let '(result, memo') := scev_check_expr EV body ix so rank (scev_prepare_expr EV e) memo in
    scev_expr_check_reference EV body ix so rank e = result /\
      scev_check_memo_laws EV body ix so rank memo'.
Proof.
  change (scev_check_expr_laws EV body ix so rank e).
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z].
  - intros memo Hmemo.
    cbn [scev_prepare_expr scev_prepare_binary scev_check_expr scev_prepared_code].
    match goal with
    | |- context [Map.get positive_encoding ?code memo] =>
      destruct (Map.get positive_encoding code memo) eqn:Hget
    end.
    + split; [eapply Hmemo; exact Hget|exact Hmemo].
    + split; [reflexivity|].
      apply (scev_check_memo_set EV body ix so rank memo (SOutside x));
        [exact Hmemo|reflexivity].
  - intros memo Hmemo.
    cbn [scev_prepare_expr scev_prepare_binary scev_check_expr scev_prepared_code].
    match goal with
    | |- context [Map.get positive_encoding ?code memo] =>
      destruct (Map.get positive_encoding code memo) eqn:Hget
    end.
    + split; [eapply Hmemo; exact Hget|exact Hmemo].
    + split; [reflexivity|].
      apply (scev_check_memo_set EV body ix so rank memo (SPhi x));
        [exact Hmemo|reflexivity].
  - apply scev_check_add_correct; assumption.
  - apply scev_check_mul_correct; assumption.
  - intros memo Hmemo.
    cbn [scev_prepare_expr scev_prepare_binary scev_check_expr scev_prepared_code].
    match goal with
    | |- context [Map.get positive_encoding ?code memo] =>
      destruct (Map.get positive_encoding code memo) eqn:Hget
    end.
    + split; [eapply Hmemo; exact Hget|exact Hmemo].
    + split; [reflexivity|].
      apply (scev_check_memo_set EV body ix so rank memo (SConst x z));
        [exact Hmemo|reflexivity].
Qed.

(** Starting from an empty cache, expression checking returns the exact declarative tree result. *)
Theorem scev_check_expr_agrees {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e :
  fst (scev_check_expr EV body ix so rank (scev_prepare_expr EV e) Map.empty) =
    scev_expr_check_reference EV body ix so rank e.
Proof.
  pose proof (scev_check_expr_correct EV body ix so rank e Map.empty
    (scev_check_memo_empty EV body ix so rank)) as Hcorrect.
  destruct (scev_check_expr EV body ix so rank (scev_prepare_expr EV e) Map.empty)
    as [result memo]; cbn [fst]; symmetry; exact (proj1 Hcorrect).
Qed.

(** * Shared preparation and context-validated expression summaries *)

(** Prepared phi supports contain exactly the expression's referenced phis. *)
Lemma scev_prepare_phis_wf {V} (EV : encoding V) e :
  FinSet.wf EV (scev_prepared_phis (scev_prepare_expr EV e)).
Proof.
  induction e; cbn [scev_prepare_expr scev_prepare_binary scev_prepared_phis].
  - apply Map.wf_empty.
  - apply Map.wf_set; apply Map.wf_empty.
  - apply Map.wf_union_with; assumption.
  - apply Map.wf_union_with; assumption.
  - apply Map.wf_empty.
Qed.

(** A trie fold tests a predicate on its stored keys without constructing an element list. *)
Definition scev_phis_check {V} (test : V -> bool) (phis : FinSet.t V) : bool :=
  Map.fold (fun ok x _ => ok && test x) phis true.

Lemma scev_fold_and {A} (test : A -> bool) xs acc :
  fold_left (fun ok x => ok && test x) xs acc = (acc && forallb test xs).
Proof.
  revert acc; induction xs as [|x xs IH]; intro acc; cbn.
  - symmetry; apply Bool.andb_true_r.
  - rewrite IH, Bool.andb_assoc; reflexivity.
Qed.

(** Successful support validation supplies the predicate at every referenced phi. *)
Lemma scev_phis_check_spec {V} (EV : encoding V) test phis :
  FinSet.wf EV phis ->
  (scev_phis_check test phis = true <->
    forall x, FinSet.mem EV x phis = true -> test x = true).
Proof.
  intro Hwf; unfold scev_phis_check; rewrite Map.fold_elements.
  rewrite (scev_fold_and (fun kv : V * unit => test (fst kv))), Bool.andb_true_l.
  rewrite forallb_forall; split.
  - intros Hall x Hmem.
    assert (Hget : Map.get EV x phis = Some tt).
    { unfold FinSet.mem, Map.mem in Hmem.
      destruct (Map.get EV x phis) as [[]|]; congruence. }
    apply (Hall (x, tt)); apply Map.elements_complete with (E := EV); assumption.
  - intros Hall [x []] Hin; cbn; apply Hall.
    apply Map.elements_sound with (E := EV) in Hin; [|exact Hwf].
    unfold FinSet.mem, Map.mem; rewrite Hin; reflexivity.
Qed.

(** Translation needs agreement only on the prepared support, including missing phi values. *)
Lemma scev_translate_expr_phis {V} (EV : encoding V) (left right : V -> option (chrec V)) e :
  (forall x, FinSet.mem EV x (scev_prepared_phis (scev_prepare_expr EV e)) = true ->
    left x = right x) -> scev_translate_expr left e = scev_translate_expr right e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; intro Hagree;
    cbn [scev_translate_expr]; try reflexivity.
  - apply Hagree; cbn [scev_prepare_expr scev_prepared_phis].
    apply FinSet.mem_add; left; reflexivity.
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_prepare_expr scev_prepare_binary scev_prepared_phis];
      apply FinSet.mem_union; auto.
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_prepare_expr scev_prepare_binary scev_prepared_phis];
      apply FinSet.mem_union; auto.
Qed.

(** Reference checking depends on a rank only through the earlier-phi tests in its support. *)
Lemma scev_check_reference_phis {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) left right e :
  (forall x, FinSet.mem EV x (scev_prepared_phis (scev_prepare_expr EV e)) = true ->
    (match Map.get EV x (sri_ranks (ssi_phi ix)) with
     | Some i => Nat.ltb i left | None => false end) =
    (match Map.get EV x (sri_ranks (ssi_phi ix)) with
     | Some i => Nat.ltb i right | None => false end)) ->
  scev_expr_check_reference EV body ix so left e =
    scev_expr_check_reference EV body ix so right e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; intro Hagree;
    cbn [scev_expr_check_reference]; try reflexivity.
  - rewrite Hagree; [reflexivity|].
    cbn [scev_prepare_expr scev_prepared_phis]; apply FinSet.mem_add; left; reflexivity.
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_prepare_expr scev_prepare_binary scev_prepared_phis];
      apply FinSet.mem_union; auto.
  - rewrite IHa, IHb; try reflexivity; intros y Hy; apply Hagree;
      cbn [scev_prepare_expr scev_prepare_binary scev_prepared_phis];
      apply FinSet.mem_union; auto.
Qed.

Definition scev_value_eq_dec {V} (EV : encoding V) (x y : V) : {x = y} + {x <> y}.
Proof.
  destruct (Pos.eq_dec (encode EV x) (encode EV y)) as [Heq|Hne].
  - left; apply (encode_injective EV); exact Heq.
  - right; intro Heq; subst y; contradiction.
Defined.

Definition scev_iexpr_eq_dec {V} (EV : encoding V) (a b : iexpr V) : {a = b} + {a <> b}.
Proof.
  decide equality; first [apply Z.eq_dec|apply (scev_value_eq_dec EV)].
Defined.

Definition scev_chrec_eq_dec {V} (EV : encoding V) (a b : chrec V) : {a = b} + {a <> b}.
Proof.
  decide equality; apply (scev_iexpr_eq_dec EV).
Defined.

(** Lookup equality distinguishes absence and the entire recurrence syntax. *)
Definition scev_lookup_eqb {V} (EV : encoding V) (a b : option (chrec V)) : bool :=
  match a, b with
  | Some a', Some b' => if scev_chrec_eq_dec EV a' b' then true else false
  | None, None => true
  | _, _ => false
  end.

Lemma scev_lookup_eqb_spec {V} (EV : encoding V) a b :
  scev_lookup_eqb EV a b = true <-> a = b.
Proof.
  destruct a as [a|], b as [b|]; cbn [scev_lookup_eqb]; try (split; congruence).
  destruct (scev_chrec_eq_dec EV a b); split; congruence.
Qed.

(** Cache traces record actual hits and recomputations in the execution used by recognition. *)
Record scev_cache (A : Type) : Type := ScevCache {
  scc_entries : Map.t positive A;
  scc_hits : list positive;
  scc_misses : list positive
}.

Arguments ScevCache {A}.
Arguments scc_entries {A}.
Arguments scc_hits {A}.
Arguments scc_misses {A}.

Definition scev_cache_empty {A} : scev_cache A := ScevCache Map.empty [] [].

Definition scev_cache_get {A} code (memo : scev_cache A) : option A :=
  Map.get positive_encoding code (scc_entries memo).

Definition scev_cache_store {A} code (value : A) (memo : scev_cache A) : scev_cache A :=
  ScevCache (Map.set positive_encoding code value (scc_entries memo))
    (scc_hits memo) (code :: scc_misses memo).

Definition scev_cache_reuse {A} code (memo : scev_cache A) : scev_cache A :=
  ScevCache (scc_entries memo) (code :: scc_hits memo) (scc_misses memo).

(** Compiler entries retain their actual phi valuation snapshot, independently of later bindings. *)
Definition scev_shared_compile_memo (V : Type) :=
  scev_cache ((V -> option (chrec V)) * chrec V).

(** A stored structural key has its exact translation under the entry's captured environment. *)
Definition scev_shared_compile_laws {V} (EV : encoding V)
    (memo : scev_shared_compile_memo V) : Prop :=
  forall e snapshot c,
    scev_cache_get (scev_expr_code EV e) memo = Some (snapshot, c) ->
      scev_translate_expr snapshot e = Some c.

Lemma scev_shared_compile_empty {V} (EV : encoding V) :
  scev_shared_compile_laws EV scev_cache_empty.
Proof.
  intros e snapshot c Hget.
  change (Map.get positive_encoding (scev_expr_code EV e) Map.empty =
    Some (snapshot, c)) in Hget.
  rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma scev_shared_compile_set {V} (EV : encoding V) memo e lookup c :
  scev_shared_compile_laws EV memo -> scev_translate_expr lookup e = Some c ->
  scev_shared_compile_laws EV
    (scev_cache_store (scev_expr_code EV e) (lookup, c) memo).
Proof.
  intros Hmemo Htranslated other snapshot d Hget.
  change (Map.get positive_encoding (scev_expr_code EV other)
    (Map.set positive_encoding (scev_expr_code EV e) (lookup, c) (scc_entries memo)) =
      Some (snapshot, d)) in Hget.
  destruct (Pos.eq_dec (scev_expr_code EV other) (scev_expr_code EV e)) as [Heq|Hne].
  - apply scev_expr_code_injective in Heq; subst other.
    rewrite Map.get_set_same in Hget; inversion Hget; subst snapshot d; exact Htranslated.
  - rewrite Map.get_set_other in Hget by exact Hne; eapply Hmemo; exact Hget.
Qed.

(** A hit validates the whole referenced environment before reusing the completed recurrence. *)
Definition scev_shared_compile_hit {V} (EV : encoding V)
    (lookup : V -> option (chrec V)) (e : scev_prepared_expr V)
    (memo : scev_shared_compile_memo V) : option (chrec V) :=
  match scev_cache_get (scev_prepared_code e) memo with
  | Some (snapshot, c) =>
    if scev_phis_check (fun x => scev_lookup_eqb EV (lookup x) (snapshot x))
      (scev_prepared_phis e) then Some c else None
  | None => None
  end.

Lemma scev_shared_compile_hit_sound {V} (EV : encoding V) lookup e memo c :
  scev_shared_compile_laws EV memo ->
  scev_shared_compile_hit EV lookup (scev_prepare_expr EV e) memo = Some c ->
  scev_translate_expr lookup e = Some c.
Proof.
  intros Hmemo; unfold scev_shared_compile_hit; rewrite scev_prepare_expr_code.
  destruct (scev_cache_get (scev_expr_code EV e) memo)
    as [[snapshot d]|] eqn:Hget; [|discriminate].
  destruct (scev_phis_check _ _) eqn:Hvalid; [|discriminate].
  intro Heq; inversion Heq; subst d.
  rewrite (scev_translate_expr_phis EV lookup snapshot e).
  - eapply Hmemo; exact Hget.
  - intros x Hmem; apply (proj1 (scev_lookup_eqb_spec EV _ _)).
    apply (proj1 (scev_phis_check_spec EV _ _ (scev_prepare_phis_wf EV e)) Hvalid x Hmem).
Qed.

(** Shared compilation consults valid completed summaries before visiting either child. *)
Fixpoint scev_compile_shared_expr {V} (EV : encoding V) (lookup : V -> option (chrec V))
    (e : scev_prepared_expr V) (memo : scev_shared_compile_memo V)
    : option (chrec V * scev_shared_compile_memo V) :=
  match scev_shared_compile_hit EV lookup e memo with
  | Some c => Some (c, scev_cache_reuse (scev_prepared_code e) memo)
  | None =>
    let finish := fun c memo' =>
      Some (c, scev_cache_store (scev_prepared_code e) (lookup, c) memo') in
    match e with
    | POutside _ _ x => finish (CInv (IVar x)) memo
    | PPhi _ _ x =>
      match lookup x with Some c => finish c memo | None => None end
    | PAdd _ _ _ a b =>
      match scev_compile_shared_expr EV lookup a memo with
      | Some (ca, ma) =>
        match scev_compile_shared_expr EV lookup b ma with
        | Some (cb, mb) => finish (chrec_add ca cb) mb
        | None => None
        end
      | None => None
      end
    | PMul _ _ _ a b =>
      match scev_compile_shared_expr EV lookup a memo with
      | Some (ca, ma) =>
        match scev_compile_shared_expr EV lookup b ma with
        | Some (cb, mb) => finish (chrec_mul ca cb) mb
        | None => None
        end
      | None => None
      end
    | PConst _ _ _ z => finish (CInv (IWordConst z)) memo
    end
  end.

(** Expression compilation couples its exact option result with snapshot preservation. *)
Definition scev_compile_shared_expr_laws {V} (EV : encoding V) lookup (e : scev_expr V) : Prop :=
  forall memo, scev_shared_compile_laws EV memo ->
  match scev_compile_shared_expr EV lookup (scev_prepare_expr EV e) memo with
  | Some (c, memo') => scev_translate_expr lookup e = Some c /\
      scev_shared_compile_laws EV memo'
  | None => scev_translate_expr lookup e = None
  end.

(** Both arithmetic constructors share one cache-hit, child-compilation and preservation proof. *)
Lemma scev_compile_shared_binary_correct {V} (EV : encoding V) lookup (multiply : bool) x a b :
  scev_compile_shared_expr_laws EV lookup a ->
  scev_compile_shared_expr_laws EV lookup b ->
  scev_compile_shared_expr_laws EV lookup (if multiply then SMul x a b else SAdd x a b).
Proof.
  intros IHa IHb; destruct multiply;
    match goal with
    | |- scev_compile_shared_expr_laws _ _ ?source => pose (original := source)
    end;
    intros memo Hmemo; cbn -[scev_shared_compile_hit];
    match goal with
    | |- context [scev_shared_compile_hit EV lookup ?prepared memo] =>
      destruct (scev_shared_compile_hit EV lookup prepared memo) as [cached|] eqn:Hhit
    end.
  all: try (split;
    [eapply (scev_shared_compile_hit_sound EV lookup original memo cached); eassumption|
      exact Hmemo]).
  all: cbn [scev_prepare_expr scev_prepare_binary]; rewrite ?scev_prepare_expr_code.
  all: specialize (IHa memo Hmemo);
    destruct (scev_compile_shared_expr EV lookup (scev_prepare_expr EV a) memo)
      as [[ca ma]|] eqn:Ha.
  all: try (cbn [original scev_translate_expr]; rewrite IHa; reflexivity).
  all: destruct IHa as [Hta Hma]; specialize (IHb ma Hma);
    destruct (scev_compile_shared_expr EV lookup (scev_prepare_expr EV b) ma)
      as [[cb mb]|] eqn:Hb.
  all: try (cbn [original scev_translate_expr]; rewrite Hta, IHb; reflexivity).
  all: destruct IHb as [Htb Hmb]; split.
  all: first [cbn [original scev_translate_expr]; rewrite Hta, Htb; reflexivity|
    eapply (scev_shared_compile_set EV mb original); [exact Hmb|];
      cbn [original scev_translate_expr]; rewrite Hta, Htb; reflexivity].
Qed.

(** Shared compilation is exact even after arbitrary environment changes and invalidated hits. *)
Theorem scev_compile_shared_expr_correct {V} (EV : encoding V) lookup e :
  forall memo, scev_shared_compile_laws EV memo ->
  match scev_compile_shared_expr EV lookup (scev_prepare_expr EV e) memo with
  | Some (c, memo') => scev_translate_expr lookup e = Some c /\
      scev_shared_compile_laws EV memo'
  | None => scev_translate_expr lookup e = None
  end.
Proof.
  change (scev_compile_shared_expr_laws EV lookup e).
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z].
  - intros memo Hmemo; cbn -[scev_shared_compile_hit];
      match goal with
      | |- context [scev_shared_compile_hit EV lookup ?prepared memo] =>
        destruct (scev_shared_compile_hit EV lookup prepared memo) as [cached|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_compile_hit_sound EV lookup (SOutside x) memo cached);
          eassumption|exact Hmemo].
    + split; [reflexivity|]; apply (scev_shared_compile_set EV memo (SOutside x));
        [exact Hmemo|reflexivity].
  - intros memo Hmemo; cbn -[scev_shared_compile_hit];
      match goal with
      | |- context [scev_shared_compile_hit EV lookup ?prepared memo] =>
        destruct (scev_shared_compile_hit EV lookup prepared memo) as [cached|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_compile_hit_sound EV lookup (SPhi x) memo cached);
          eassumption|exact Hmemo].
    + destruct (lookup x) as [c|] eqn:Hlookup; [|reflexivity].
      split; [reflexivity|]; apply (scev_shared_compile_set EV memo (SPhi x)); assumption.
  - exact (scev_compile_shared_binary_correct EV lookup false x a b IHa IHb).
  - exact (scev_compile_shared_binary_correct EV lookup true x a b IHa IHb).
  - intros memo Hmemo; cbn -[scev_shared_compile_hit];
      match goal with
      | |- context [scev_shared_compile_hit EV lookup ?prepared memo] =>
        destruct (scev_shared_compile_hit EV lookup prepared memo) as [cached|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_compile_hit_sound EV lookup (SConst x z) memo cached);
          eassumption|exact Hmemo].
    + split; [reflexivity|]; apply (scev_shared_compile_set EV memo (SConst x z));
        [exact Hmemo|reflexivity].
Qed.

(** Checker entries retain the rank context in which their complete result was computed. *)
Definition scev_shared_check_memo (V : Type) :=
  scev_cache (nat * scev_expr_check_result V).

(** Rank snapshots make cache correctness independent of the current binding position. *)
Definition scev_shared_check_laws {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C)
    (memo : scev_shared_check_memo V) : Prop :=
  forall e rank result,
    scev_cache_get (scev_expr_code EV e) memo = Some (rank, result) ->
    scev_expr_check_reference EV body ix so rank e = result.

Lemma scev_shared_check_empty {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) :
  scev_shared_check_laws EV body ix so scev_cache_empty.
Proof.
  intros e rank result Hget.
  change (Map.get positive_encoding (scev_expr_code EV e) Map.empty =
    Some (rank, result)) in Hget.
  rewrite Map.get_empty in Hget; discriminate.
Qed.

Lemma scev_shared_check_set {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) memo e rank result :
  scev_shared_check_laws EV body ix so memo ->
  scev_expr_check_reference EV body ix so rank e = result ->
  scev_shared_check_laws EV body ix so
    (scev_cache_store (scev_expr_code EV e) (rank, result) memo).
Proof.
  intros Hmemo Hresult other old value Hget.
  change (Map.get positive_encoding (scev_expr_code EV other)
    (Map.set positive_encoding (scev_expr_code EV e) (rank, result) (scc_entries memo)) =
      Some (old, value)) in Hget.
  destruct (Pos.eq_dec (scev_expr_code EV other) (scev_expr_code EV e)) as [Heq|Hne].
  - apply scev_expr_code_injective in Heq; subst other.
    rewrite Map.get_set_same in Hget; inversion Hget; subst old value; exact Hresult.
  - rewrite Map.get_set_other in Hget by exact Hne; eapply Hmemo; exact Hget.
Qed.

(** Earlier-phi observations are the only rank-sensitive part of expression validation. *)
Definition scev_phi_before {N V K} (EV : encoding V) (ix : scev_static_index N V K)
    rank x : bool :=
  match Map.get EV x (sri_ranks (ssi_phi ix)) with
  | Some i => Nat.ltb i rank
  | None => false
  end.

(** A checker hit validates every referenced phi's earlier-rank observation before reuse. *)
Definition scev_shared_check_hit {N V K} (EV : encoding V) (ix : scev_static_index N V K)
    rank (e : scev_prepared_expr V) (memo : scev_shared_check_memo V)
    : option (scev_expr_check_result V) :=
  match scev_cache_get (scev_prepared_code e) memo with
  | Some (old, result) =>
    if scev_phis_check (fun x =>
      Bool.eqb (scev_phi_before EV ix rank x) (scev_phi_before EV ix old x))
      (scev_prepared_phis e) then Some result else None
  | None => None
  end.

Lemma scev_shared_check_hit_sound {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e memo result :
  scev_shared_check_laws EV body ix so memo ->
  scev_shared_check_hit EV ix rank (scev_prepare_expr EV e) memo = Some result ->
  scev_expr_check_reference EV body ix so rank e = result.
Proof.
  intros Hmemo; unfold scev_shared_check_hit; rewrite scev_prepare_expr_code.
  destruct (scev_cache_get (scev_expr_code EV e) memo)
    as [[old value]|] eqn:Hget; [|discriminate].
  destruct (scev_phis_check _ _) eqn:Hvalid; [|discriminate].
  intro Heq; inversion Heq; subst value.
  rewrite (scev_check_reference_phis EV body ix so rank old e).
  - eapply Hmemo; exact Hget.
  - intros x Hmem; apply Bool.eqb_prop.
    apply (proj1 (scev_phis_check_spec EV _ _ (scev_prepare_phis_wf EV e)) Hvalid x Hmem).
Qed.

(** Shared checking consults its context-validated summary before checking either child. *)
Fixpoint scev_check_shared_expr {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank
    (e : scev_prepared_expr V) (memo : scev_shared_check_memo V)
    : scev_expr_check_result V * scev_shared_check_memo V :=
  match scev_shared_check_hit EV ix rank e memo with
  | Some result => (result, scev_cache_reuse (scev_prepared_code e) memo)
  | None =>
    let finish := fun result memo' =>
      (result, scev_cache_store (scev_prepared_code e) (rank, result) memo') in
    let failed := (false, FinSet.empty) in
    let binary := fun (flag : K -> bool) (x : V) (a b : scev_prepared_expr V)
      (recurse_a recurse_b : scev_shared_check_memo V ->
        scev_expr_check_result V * scev_shared_check_memo V) =>
      if scev_binary_check EV body (ssi_values ix) flag x
        (scev_prepared_root a) (scev_prepared_root b) then
        let '(ra, ma) := recurse_a memo in
        if fst ra then
          let '(rb, mb) := recurse_b ma in
          finish (fst rb, FinSet.union EV (snd ra) (snd rb)) mb
        else finish failed ma
      else finish failed memo in
    match e with
    | POutside _ _ x =>
      finish ((match Map.get EV x (ssi_values ix) with
        | Some (n, _) => negb (body n)
        | None => false
        end), FinSet.empty) memo
    | PPhi _ _ x => finish
        (Map.mem EV x (ssi_values ix) && scev_phi_before EV ix rank x,
          FinSet.add EV x FinSet.empty) memo
    | PAdd _ _ x a b => binary (add_op so) x a b
        (scev_check_shared_expr EV body ix so rank a)
        (scev_check_shared_expr EV body ix so rank b)
    | PMul _ _ x a b => binary (mul_op so) x a b
        (scev_check_shared_expr EV body ix so rank a)
        (scev_check_shared_expr EV body ix so rank b)
    | PConst _ _ x z => finish
        (scev_constant_check EV body (ssi_values ix) so x z, FinSet.empty) memo
    end
  end.

(** Shared expression correctness records its exact result and preserves every snapshot entry. *)
Definition scev_check_shared_expr_laws {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank (e : scev_expr V) : Prop :=
  forall memo, scev_shared_check_laws EV body ix so memo ->
  let '(result, memo') := scev_check_shared_expr EV body ix so rank (scev_prepare_expr EV e) memo in
    scev_expr_check_reference EV body ix so rank e = result /\
      scev_shared_check_laws EV body ix so memo'.

(** One binary-node proof handles both operation flags and their context-validated cache hits. *)
Lemma scev_check_shared_binary_correct {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank (multiply : bool) x a b :
  scev_check_shared_expr_laws EV body ix so rank a ->
  scev_check_shared_expr_laws EV body ix so rank b ->
  scev_check_shared_expr_laws EV body ix so rank
    (if multiply then SMul x a b else SAdd x a b).
Proof.
  intros IHa IHb; destruct multiply;
    match goal with
    | |- scev_check_shared_expr_laws _ _ _ _ _ ?source => pose (original := source)
    end;
    intros memo Hmemo;
    cbn -[scev_shared_check_hit];
    match goal with
    | |- context [scev_shared_check_hit EV ix rank ?prepared memo] =>
      destruct (scev_shared_check_hit EV ix rank prepared memo) as [result|] eqn:Hhit
    end.
  all: try (split;
    [eapply (scev_shared_check_hit_sound EV body ix so rank original memo result); eassumption|
      exact Hmemo]).
  all: cbn [scev_prepare_expr scev_prepare_binary scev_prepared_root scev_prepared_code];
    rewrite ?scev_prepare_expr_root, ?scev_prepare_expr_code.
  all: match goal with
    | |- context [if ?condition then _ else _] => destruct condition eqn:Hlocal
    end.
  all: try (split; [cbn [original scev_expr_check_reference]; rewrite ?Hlocal; reflexivity|];
    eapply (scev_shared_check_set EV body ix so memo original); [exact Hmemo|];
    cbn [original scev_expr_check_reference]; rewrite ?Hlocal; reflexivity).
  all: specialize (IHa memo Hmemo);
    destruct (scev_check_shared_expr EV body ix so rank (scev_prepare_expr EV a) memo)
      as [[ba da] ma] eqn:Ha; destruct IHa as [Hta Hma]; destruct ba.
  all: try (split; [cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta; reflexivity|];
    eapply (scev_shared_check_set EV body ix so ma original); [exact Hma|];
    cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta; reflexivity).
  all: specialize (IHb ma Hma);
    destruct (scev_check_shared_expr EV body ix so rank (scev_prepare_expr EV b) ma)
      as [[bb db] mb] eqn:Hb; destruct IHb as [Htb Hmb]; split.
  all: first [cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta, ?Htb; reflexivity |
    eapply (scev_shared_check_set EV body ix so mb original); [exact Hmb|];
      cbn [original scev_expr_check_reference]; rewrite ?Hlocal, ?Hta, ?Htb; reflexivity].
Qed.

(** Shared checking preserves exact malformed-tree behavior under arbitrary rank changes. *)
Theorem scev_check_shared_expr_correct {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e :
  scev_check_shared_expr_laws EV body ix so rank e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z].
  - intros memo Hmemo; cbn -[scev_shared_check_hit];
      match goal with
      | |- context [scev_shared_check_hit EV ix rank ?prepared memo] =>
        destruct (scev_shared_check_hit EV ix rank prepared memo) as [result|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_check_hit_sound EV body ix so rank (SOutside x) memo result);
          eassumption|exact Hmemo].
    + split; [reflexivity|]; apply (scev_shared_check_set EV body ix so memo (SOutside x));
        [exact Hmemo|reflexivity].
  - intros memo Hmemo; cbn -[scev_shared_check_hit];
      match goal with
      | |- context [scev_shared_check_hit EV ix rank ?prepared memo] =>
        destruct (scev_shared_check_hit EV ix rank prepared memo) as [result|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_check_hit_sound EV body ix so rank (SPhi x) memo result);
          eassumption|exact Hmemo].
    + split; [reflexivity|]; apply (scev_shared_check_set EV body ix so memo (SPhi x));
        [exact Hmemo|reflexivity].
  - exact (scev_check_shared_binary_correct EV body ix so rank false x a b IHa IHb).
  - exact (scev_check_shared_binary_correct EV body ix so rank true x a b IHa IHb).
  - intros memo Hmemo; cbn -[scev_shared_check_hit];
      match goal with
      | |- context [scev_shared_check_hit EV ix rank ?prepared memo] =>
        destruct (scev_shared_check_hit EV ix rank prepared memo) as [result|] eqn:Hhit
      end.
    + split;
        [eapply (scev_shared_check_hit_sound EV body ix so rank (SConst x z) memo result);
          eassumption|exact Hmemo].
    + split; [reflexivity|]; apply (scev_shared_check_set EV body ix so memo (SConst x z));
        [exact Hmemo|reflexivity].
Qed.

(** A validated compiler hit returns immediately and records reuse without another miss. *)
Lemma scev_compile_shared_expr_reuses {V} (EV : encoding V) lookup e memo c :
  scev_shared_compile_hit EV lookup e memo = Some c ->
  scev_compile_shared_expr EV lookup e memo =
    Some (c, scev_cache_reuse (scev_prepared_code e) memo).
Proof.
  destruct e; cbn -[scev_shared_compile_hit]; intro Hhit; rewrite Hhit; reflexivity.
Qed.

(** A validated checker hit returns immediately and retains every completed dependency summary. *)
Lemma scev_check_shared_expr_reuses {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e memo result :
  scev_shared_check_hit EV ix rank e memo = Some result ->
  scev_check_shared_expr EV body ix so rank e memo =
    (result, scev_cache_reuse (scev_prepared_code e) memo).
Proof.
  destruct e; cbn -[scev_shared_check_hit]; intro Hhit; rewrite Hhit; reflexivity.
Qed.

(** Completed values retain their prepared dependency graph and an erased agreement proof. *)
Record scev_completed {V} (EV : encoding V) : Type := ScevCompleted {
  sc_source : scev_expr V;
  sc_prepared : scev_prepared_expr V;
  sc_agrees : sc_prepared = scev_prepare_expr EV sc_source
}.

Arguments ScevCompleted {V EV}.
Arguments sc_source {V EV}.
Arguments sc_prepared {V EV}.
Arguments sc_agrees {V EV}.

(** Terminal preparation has no recursive source dependency. *)
Definition scev_complete_leaf {V} (EV : encoding V) (e : scev_expr V) : scev_completed EV :=
  ScevCompleted e (scev_prepare_expr EV e) eq_refl.

(** Binary completion links already prepared children and preserves exact source structure. *)
Definition scev_complete_binary {V} (EV : encoding V) (multiply : bool) (x : V)
    (a b : scev_completed EV) : scev_completed EV.
Proof.
  refine (ScevCompleted (if multiply then SMul x (sc_source a) (sc_source b)
    else SAdd x (sc_source a) (sc_source b))
    (scev_prepare_binary EV multiply x (sc_prepared a) (sc_prepared b)) _).
  destruct multiply; cbn [scev_prepare_expr]; rewrite <- !sc_agrees; reflexivity.
Defined.

(** Each retained binding couples its public tree to the prepared expression actually consumed. *)
Record scev_prepared_binding {V} (EV : encoding V) : Type := ScevPreparedBinding {
  spb_source : scev_binding V;
  spb_other : option (scev_prepared_expr V);
  spb_agrees : spb_other = option_map (scev_prepare_expr EV) (sb_other spb_source)
}.

Arguments ScevPreparedBinding {V EV}.
Arguments spb_source {V EV}.
Arguments spb_other {V EV}.
Arguments spb_agrees {V EV}.

Definition scev_complete_binding {V} (EV : encoding V) (x base update : V)
    (kind : scev_update) (first : bool)
    (other : scev_completed EV) : scev_prepared_binding EV.
Proof.
  refine (ScevPreparedBinding
    (ScevBinding x base update kind (Some (sc_source other)) first)
    (Some (sc_prepared other)) _).
  cbn; rewrite sc_agrees; reflexivity.
Defined.

Definition scev_complete_double {V} (EV : encoding V) x base update : scev_prepared_binding EV :=
  ScevPreparedBinding (ScevBinding x base update SDoubleUpdate None true) None eq_refl.

(** External plans are ingested structurally once, preserving every malformed tree distinction. *)
Definition scev_ingest_bindings {V} (EV : encoding V) (bs : list (scev_binding V))
    : list (scev_prepared_binding EV) :=
  map (fun b => ScevPreparedBinding b
    (option_map (scev_prepare_expr EV) (sb_other b)) eq_refl) bs.

(** Ingestion preserves every public tree without assuming that the plan is valid. *)
Lemma scev_ingest_bindings_source {V} (EV : encoding V) bs :
  map spb_source (scev_ingest_bindings EV bs) = bs.
Proof.
  unfold scev_ingest_bindings; rewrite map_map.
  change (map (fun b : scev_binding V => b) bs = bs); apply map_id.
Qed.

(** The public prepared representation is recovered without re-preparing any source expression. *)
Lemma scev_prepared_bindings_agree {V} (EV : encoding V) (bs : list (scev_prepared_binding EV)) :
  map (fun b => (spb_source b, spb_other b)) bs =
    scev_prepare_bindings EV (map spb_source bs).
Proof.
  induction bs as [|b bs IH]; cbn [scev_prepare_bindings map]; [reflexivity|].
  rewrite spb_agrees, IH; reflexivity.
Qed.

(** Binding compilation keeps the shared expression cache across every phi environment update. *)
Definition scev_compile_shared_binding {V} (EV : encoding V) env
    (b : scev_prepared_binding EV) (memo : scev_shared_compile_memo V)
    : option (chrec V * scev_shared_compile_memo V) :=
  let source := spb_source b in
  let base := CInv (IVar (sb_base source)) in
  match sb_kind source with
  | SDoubleUpdate => Some (CGeo base (CInv (IConst 2)), memo)
  | SAddUpdate | SMulUpdate =>
    match spb_other b with
    | Some e =>
      match scev_compile_shared_expr EV (fun x => Map.get EV x env) e memo with
      | Some (c, memo') => Some
          ((match sb_kind source with
            | SAddUpdate => CRec base c
            | _ => CGeo base c
            end), memo')
      | None => None
      end
    | None => None
    end
  end.

(** A retained prepared binding compiles exactly its public tree, including all failure cases. *)
Lemma scev_compile_shared_binding_correct {V} (EV : encoding V) env
    (b : scev_prepared_binding EV) memo :
  scev_shared_compile_laws EV memo ->
  match scev_compile_shared_binding EV env b memo with
  | Some (c, memo') =>
    scev_translate_binding (fun x => Map.get EV x env) (spb_source b) = Some c /\
      scev_shared_compile_laws EV memo'
  | None => scev_translate_binding (fun x => Map.get EV x env) (spb_source b) = None
  end.
Proof.
  intro Hmemo; unfold scev_compile_shared_binding, scev_translate_binding; rewrite spb_agrees.
  destruct (sb_kind (spb_source b)); [| |split; [reflexivity|exact Hmemo]];
    destruct (sb_other (spb_source b)) as [e|]; cbn [option_map]; try reflexivity.
  all: pose proof (scev_compile_shared_expr_correct EV (fun x => Map.get EV x env) e memo Hmemo)
    as Hcorrect;
    destruct (scev_compile_shared_expr EV (fun x => Map.get EV x env)
      (scev_prepare_expr EV e) memo) as [[c memo']|] eqn:Hrun.
  all: try (destruct Hcorrect as [Hvalue Hcache]; rewrite Hvalue;
    split; [reflexivity|exact Hcache]).
  all: rewrite Hcorrect; reflexivity.
Qed.

(** One traversal threads completed phis and expression summaries with their valuation snapshots. *)
Fixpoint scev_compile_shared_bindings {V} (EV : encoding V)
    (bs : list (scev_prepared_binding EV)) env (memo : scev_shared_compile_memo V)
    : option (Map.t V (chrec V) * scev_shared_compile_memo V) :=
  match bs with
  | [] => Some (env, memo)
  | b :: rest =>
    match scev_compile_shared_binding EV env b memo with
    | Some (c, memo') =>
      scev_compile_shared_bindings EV rest (Map.set EV (sb_phi (spb_source b)) c env) memo'
    | None => None
    end
  end.

(** The shared traversal agrees with the public compiler while retaining its actual reuse trace. *)
Lemma scev_compile_shared_bindings_agrees {V} (EV : encoding V) bs :
  forall env memo, scev_shared_compile_laws EV memo ->
  match scev_compile_shared_bindings EV bs env memo with
  | Some (env', memo') =>
    scev_compile_bindings EV (scev_prepare_bindings EV (map spb_source bs)) env = Some env' /\
      scev_shared_compile_laws EV memo'
  | None => scev_compile_bindings EV (scev_prepare_bindings EV (map spb_source bs)) env = None
  end.
Proof.
  induction bs as [|b bs IH]; intros env memo Hmemo; [split; [reflexivity|exact Hmemo]|].
  cbn [scev_compile_shared_bindings].
  pose proof (scev_compile_shared_binding_correct EV env b memo Hmemo) as Hcorrect.
  destruct (scev_compile_shared_binding EV env b memo) as [[c memo']|] eqn:Hrun.
  - destruct Hcorrect as [Hvalue Hcache].
    specialize (IH (Map.set EV (sb_phi (spb_source b)) c env) memo' Hcache).
    cbn [map scev_prepare_bindings scev_compile_bindings]; rewrite scev_compile_binding_agrees,
      Hvalue; exact IH.
  - cbn [map scev_prepare_bindings scev_compile_bindings]; rewrite scev_compile_binding_agrees,
      Hcorrect; reflexivity.
Qed.

(** Plan compilation returns the target and the shared cache used by its binding traversal. *)
Definition scev_compile_shared_plan {V} (EV : encoding V)
    (bs : list (scev_prepared_binding EV)) target : option (chrec V * scev_shared_compile_memo V) :=
  match scev_compile_shared_bindings EV bs Map.empty scev_cache_empty with
  | Some (env, memo) =>
    match Map.get EV target env with
    | Some c => Some (c, memo)
    | None => None
    end
  | None => None
  end.

(** Shared compilation preserves the public translation on every plan, including malformed ones. *)
Theorem scev_compile_shared_plan_agrees {V} (EV : encoding V) bs target :
  option_map fst (scev_compile_shared_plan EV bs target) =
    scev_compile_plan EV (ScevPlan (map spb_source bs) target).
Proof.
  unfold scev_compile_shared_plan, scev_compile_plan; cbn [sp_bindings sp_target].
  pose proof (scev_compile_shared_bindings_agrees EV bs Map.empty scev_cache_empty
    (scev_shared_compile_empty EV)) as Hagrees.
  destruct (scev_compile_shared_bindings EV bs Map.empty scev_cache_empty)
    as [[env memo]|] eqn:Hrun.
  - rewrite (proj1 Hagrees).
    destruct (Map.get EV target env); reflexivity.
  - rewrite Hagrees; reflexivity.
Qed.

(** Arbitrary external tree plans retain the public compiler's exact translation and failures. *)
Theorem scev_compile_ingested_plan_agrees {V} (EV : encoding V) (p : scev_plan V) :
  option_map fst (scev_compile_shared_plan EV (scev_ingest_bindings EV (sp_bindings p))
    (sp_target p)) = scev_compile_plan EV p.
Proof.
  rewrite scev_compile_shared_plan_agrees, scev_ingest_bindings_source.
  destruct p; reflexivity.
Qed.

(** Local feedback shape checks do not inspect the other expression's descendants. *)
Definition scev_update_gate {N V K C} (EV : encoding V) body
    (ix : scev_static_index N V K) (so : scev_ops K C)
    (b : scev_binding V) (other : option (scev_prepared_expr V)) : bool :=
  match sb_kind b, other with
  | SDoubleUpdate, None => sb_phi_first b &&
      scev_binary_check EV body (ssi_values ix) (add_op so)
        (sb_update_value b) (sb_phi b) (sb_phi b)
  | SAddUpdate, Some e | SMulUpdate, Some e =>
    let root := scev_prepared_root e in
    let flag := match sb_kind b with SAddUpdate => add_op so | _ => mul_op so end in
    negb (scev_key_eq EV root (sb_phi b)) &&
      scev_binary_check EV body (ssi_values ix) flag (sb_update_value b)
        (if sb_phi_first b then sb_phi b else root)
        (if sb_phi_first b then root else sb_phi b)
  | _, _ => false
  end.

(** Binding shape validation reuses the prepared source and positional indexes. *)
Definition scev_binding_gate {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (b : scev_binding V) (other : option (scev_prepared_expr V)) : bool :=
  match Map.get EV (sb_phi b) (ssi_values ix), Map.get EV (sb_base b) (ssi_values ix),
      Map.get EV (sb_update_value b) (ssi_values ix) with
  | Some (phi_home, Param header i), Some (base_home, _), Some (update_home, _) =>
    if scev_key_eq EN phi_home (lheader lv) && scev_key_eq EN header (lheader lv) &&
      negb (lbody lv base_home) && lbody lv update_home then
      match Map.get nat_encoding i (ssi_entry ix), Map.get nat_encoding i (ssi_back ix) with
      | Some base, Some update =>
        if scev_key_eq EV base (sb_base b) && scev_key_eq EV update (sb_update_value b) then
          scev_update_gate EV (lbody lv) ix so b other
        else false
      | _, _ => false
      end
    else false
  | _, _, _ => false
  end.

(** The factored shape gate preserves the old checker's ordering and exact option result. *)
Lemma scev_binding_gate_agrees {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix rank b other :
  scev_check_binding EN EV lv so ix rank b other =
  if scev_binding_gate EN EV lv so ix b other then
    match sb_kind b, other with
    | SDoubleUpdate, None => Some FinSet.empty
    | SAddUpdate, Some e | SMulUpdate, Some e =>
      let '(result, _) := scev_check_expr EV (lbody lv) ix so rank e Map.empty in
      if fst result then Some (snd result) else None
    | _, _ => None
    end
  else None.
Proof.
  unfold scev_check_binding, scev_binding_gate.
  destruct (Map.get EV (sb_phi b) (ssi_values ix)) as [[phi_home d]|];
    [|reflexivity].
  destruct d as [o args|header i|]; try reflexivity.
  destruct (Map.get EV (sb_base b) (ssi_values ix)) as [[base_home bd]|];
    [|reflexivity].
  destruct (Map.get EV (sb_update_value b) (ssi_values ix)) as [[update_home ud]|];
    [|reflexivity].
  destruct (scev_key_eq EN phi_home (lheader lv) && scev_key_eq EN header (lheader lv) &&
    negb (lbody lv base_home) && lbody lv update_home); [|reflexivity].
  destruct (Map.get nat_encoding i (ssi_entry ix)) as [base|]; [|reflexivity].
  destruct (Map.get nat_encoding i (ssi_back ix)) as [update|]; [|reflexivity].
  destruct (scev_key_eq EV base (sb_base b) && scev_key_eq EV update (sb_update_value b));
    [|reflexivity].
  unfold scev_check_update, scev_update_gate; destruct (sb_kind b), other as [e|];
    try reflexivity.
  all: match goal with
    | |- context [if ?condition then _ else _] => destruct condition; reflexivity
    end.
Qed.

(** Binding validation threads a shared cache through the exact local shape gate. *)
Definition scev_check_shared_binding {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix rank
    (b : scev_prepared_binding EV) (memo : scev_shared_check_memo V)
    : option (FinSet.t V * scev_shared_check_memo V) :=
  if scev_binding_gate EN EV lv so ix (spb_source b) (spb_other b) then
    match sb_kind (spb_source b), spb_other b with
    | SDoubleUpdate, None => Some (FinSet.empty, memo)
    | SAddUpdate, Some e | SMulUpdate, Some e =>
      let '(result, memo') := scev_check_shared_expr EV (lbody lv) ix so rank e memo in
      if fst result then Some (snd result, memo') else None
    | _, _ => None
    end
  else None.

(** Shared binding validation agrees exactly with public validation and preserves all snapshots. *)
Lemma scev_check_shared_binding_correct {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix rank
    (b : scev_prepared_binding EV) memo :
  scev_shared_check_laws EV (lbody lv) ix so memo ->
  match scev_check_shared_binding EN EV lv so ix rank b memo with
  | Some (deps, memo') =>
    scev_check_binding EN EV lv so ix rank (spb_source b) (spb_other b) = Some deps /\
      scev_shared_check_laws EV (lbody lv) ix so memo'
  | None => scev_check_binding EN EV lv so ix rank (spb_source b) (spb_other b) = None
  end.
Proof.
  intro Hmemo; unfold scev_check_shared_binding; rewrite scev_binding_gate_agrees.
  destruct (scev_binding_gate EN EV lv so ix (spb_source b) (spb_other b));
    [|reflexivity].
  rewrite spb_agrees.
  destruct (sb_kind (spb_source b)), (sb_other (spb_source b)) as [e|];
    cbn [option_map]; try reflexivity; try (split; [reflexivity|exact Hmemo]).
  all: pose proof (scev_check_shared_expr_correct EV (lbody lv) ix so rank e memo Hmemo)
    as Hcorrect;
    destruct (scev_check_shared_expr EV (lbody lv) ix so rank (scev_prepare_expr EV e) memo)
      as [[ok deps] memo'] eqn:Hrun; destruct Hcorrect as [Hvalue Hcache];
    rewrite <- scev_check_expr_agrees in Hvalue;
    destruct (scev_check_expr EV (lbody lv) ix so rank (scev_prepare_expr EV e) Map.empty)
      as [result unused] eqn:Hold; cbn [fst] in Hvalue; subst result;
    destruct ok; cbn [fst snd]; [split; [reflexivity|exact Hcache]|reflexivity].
Qed.

(** Shared checking retains summaries while moving through ranks, including rejected plans. *)
Fixpoint scev_check_shared_bindings {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix rank
    (bs : list (scev_prepared_binding EV)) checked (memo : scev_shared_check_memo V)
    : option (list (V * FinSet.t V) * scev_shared_check_memo V) :=
  match bs with
  | [] => Some (checked, memo)
  | b :: rest =>
    match scev_check_shared_binding EN EV lv so ix rank b memo with
    | Some (deps, memo') =>
      scev_check_shared_bindings EN EV lv so ix (Nat.succ rank) rest
        ((sb_phi (spb_source b), deps) :: checked) memo'
    | None => None
    end
  end.

(** The shared checker traversal has the old exact option result at every rank and accumulator. *)
Lemma scev_check_shared_bindings_agrees {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix bs :
  forall rank checked memo, scev_shared_check_laws EV (lbody lv) ix so memo ->
  match scev_check_shared_bindings EN EV lv so ix rank bs checked memo with
  | Some (out, memo') =>
    scev_check_bindings EN EV lv so ix rank
      (map (fun b => (spb_source b, spb_other b)) bs) checked = Some out /\
      scev_shared_check_laws EV (lbody lv) ix so memo'
  | None => scev_check_bindings EN EV lv so ix rank
      (map (fun b => (spb_source b, spb_other b)) bs) checked = None
  end.
Proof.
  induction bs as [|b bs IH]; intros rank checked memo Hmemo;
    [split; [reflexivity|exact Hmemo]|].
  cbn [scev_check_shared_bindings].
  pose proof (scev_check_shared_binding_correct EN EV lv so ix rank b memo Hmemo) as Hcorrect.
  destruct (scev_check_shared_binding EN EV lv so ix rank b memo)
    as [[deps memo']|] eqn:Hrun.
  - destruct Hcorrect as [Hvalue Hcache].
    specialize (IH (Nat.succ rank) ((sb_phi (spb_source b), deps) :: checked) memo' Hcache).
    cbn [map scev_check_bindings]; rewrite Hvalue; exact IH.
  - cbn [map scev_check_bindings]; rewrite Hcorrect; reflexivity.
Qed.

(** Prepared plan checking returns the same public Boolean and the cache used to obtain it. *)
Definition scev_check_shared_plan {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix
    (bs : list (scev_prepared_binding EV)) target
    : bool * scev_shared_check_memo V :=
  if Map.mem EV target (ssi_values ix) && sri_distinct (ssi_phi ix) then
    match sri_final (ssi_phi ix) with
    | Some last =>
      if scev_key_eq EV last target then
        match scev_check_shared_bindings EN EV lv so ix 0 bs [] scev_cache_empty with
        | Some (checked, memo) =>
          (scev_check_dependencies EV checked (FinSet.add EV target FinSet.empty), memo)
        | None => (false, scev_cache_empty)
        end
      else (false, scev_cache_empty)
    | None => (false, scev_cache_empty)
    end
  else (false, scev_cache_empty).

(** Exact plan-level agreement includes malformed trees, duplicate phis and unrelated bindings. *)
Theorem scev_check_shared_plan_agrees {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix bs target :
  fst (scev_check_shared_plan EN EV lv so ix bs target) =
    scev_plan_check_index EN EV lv so ix (ScevPlan (map spb_source bs) target).
Proof.
  unfold scev_check_shared_plan, scev_plan_check_index; cbn [sp_target sp_bindings].
  destruct (Map.mem EV target (ssi_values ix) && sri_distinct (ssi_phi ix));
    [|reflexivity].
  destruct (sri_final (ssi_phi ix)) as [last|]; [|reflexivity].
  destruct (scev_key_eq EV last target); [|reflexivity].
  pose proof (scev_check_shared_bindings_agrees EN EV lv so ix bs 0 [] scev_cache_empty
    (scev_shared_check_empty EV (lbody lv) ix so)) as Hagrees.
  destruct (scev_check_shared_bindings EN EV lv so ix 0 bs [] scev_cache_empty)
    as [[checked memo]|] eqn:Hrun; cbn [fst].
  - destruct Hagrees as [Hvalue _]; rewrite scev_prepared_bindings_agree in Hvalue.
    rewrite Hvalue; reflexivity.
  - rewrite scev_prepared_bindings_agree in Hagrees; rewrite Hagrees; reflexivity.
Qed.

(** Arbitrary external tree plans retain the public checker's exact acceptance Boolean. *)
Theorem scev_check_ingested_plan_agrees {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) (p : scev_plan V) :
  fst (scev_check_shared_plan EN EV lv so (scev_prepare_index EV inventory lv p)
    (scev_ingest_bindings EV (sp_bindings p)) (sp_target p)) =
    scev_plan_check EN EV inventory lv so p.
Proof.
  rewrite scev_check_shared_plan_agrees, scev_ingest_bindings_source.
  destruct p; reflexivity.
Qed.

(** * Recognition work machine *)

(** Work commands keep operands in indexed completed storage until their parent can be emitted. *)
Inductive scev_work (V : Type) : Type :=
  | SVisit (x : V)
  | SFinishAdd (x left right : V)
  | SFinishMul (x left right : V)
  | SFinishPhi (x base update other : V) (kind : scev_update) (phi_first : bool).

Arguments SVisit {V}.
Arguments SFinishAdd {V}.
Arguments SFinishMul {V}.
Arguments SFinishPhi {V}.

(** The producer retains completed prepared dependencies and the actual preparation trace. *)
Record scev_producer_state {V} (EV : encoding V) : Type := ScevProducerState {
  sps_work : list (scev_work V);
  sps_active : FinSet.t V;
  sps_done : Map.t V (scev_completed EV);
  sps_bindings : list (scev_prepared_binding EV);
  sps_hits : list V;
  sps_prepared : list V
}.

Arguments ScevProducerState {V EV}.
Arguments sps_work {V EV}.
Arguments sps_active {V EV}.
Arguments sps_done {V EV}.
Arguments sps_bindings {V EV}.
Arguments sps_hits {V EV}.
Arguments sps_prepared {V EV}.

(** Finishing a terminal records one preparation and its proved structural correspondence. *)
Definition scev_finish_value {V} (EV : encoding V) (rest : list (scev_work V))
    (st : scev_producer_state EV) (x : V) (e : scev_expr V) :=
  ScevProducerState rest (FinSet.remove EV x (sps_active st))
    (Map.set EV x (scev_complete_leaf EV e) (sps_done st)) (sps_bindings st)
    (sps_hits st) (x :: sps_prepared st).

(** Direct feedback is consumed before cycle checking, with self-add preferred as doubling. *)
Definition scev_expand_phi {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (rest : list (scev_work V)) (st : scev_producer_state EV) (x : V) (header : N) (i : nat)
    : option (scev_producer_state EV) :=
  if scev_key_eq EN header (lheader lv) then
    match Map.get nat_encoding i (ssi_entry ix), Map.get nat_encoding i (ssi_back ix) with
    | Some base, Some update =>
      match Map.get EV base (ssi_values ix), Map.get EV update (ssi_values ix) with
      | Some (base_home, _), Some (update_home, Op o [arg_left; arg_right]) =>
        if negb (lbody lv base_home) && lbody lv update_home then
          let left_phi := scev_key_eq EV arg_left x in
          let right_phi := scev_key_eq EV arg_right x in
          if add_op so o && left_phi && right_phi then
            Some (ScevProducerState rest (sps_active st)
              (Map.set EV x (scev_complete_leaf EV (SPhi x)) (sps_done st))
              (scev_complete_double EV x base update :: sps_bindings st)
              (sps_hits st) (x :: sps_prepared st))
          else if left_phi || right_phi then
            let other := if left_phi then arg_right else arg_left in
            let kind := if add_op so o then Some SAddUpdate else
              if mul_op so o then Some SMulUpdate else None in
            match kind with
            | Some kind => Some (ScevProducerState
                (SVisit other :: SFinishPhi x base update other kind left_phi :: rest)
                (FinSet.add EV x (sps_active st)) (sps_done st) (sps_bindings st)
                (sps_hits st) (sps_prepared st))
            | None => None
            end
          else None
        else None
      | _, _ => None
      end
    | _, _ => None
    end
  else None.

(** A successful expansion visits one fresh indexed value and schedules only its dependencies. *)
Definition scev_expand_value {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (rest : list (scev_work V)) (st : scev_producer_state EV) (x : V)
    : option (scev_producer_state EV) :=
  match Map.get EV x (ssi_values ix) with
  | Some (n, d) =>
    if lbody lv n then
      match d with
      | Param header i => scev_expand_phi EN EV lv so ix rest st x header i
      | Op o [] =>
        match const_op so o with
        | Some z => Some (scev_finish_value EV rest st x (SConst x z))
        | None => None
        end
      | Op o [a; b] =>
        let command := if add_op so o then Some (SFinishAdd x a b) else
          if mul_op so o then Some (SFinishMul x a b) else None in
        match command with
        | Some command => Some (ScevProducerState (SVisit a :: SVisit b :: command :: rest)
            (FinSet.add EV x (sps_active st)) (sps_done st) (sps_bindings st)
            (sps_hits st) (sps_prepared st))
        | None => None
        end
      | _ => None
      end
    else Some (scev_finish_value EV rest st x (SOutside x))
  | None => None
  end.

(** Administrative completion links prepared children and consumes visits to completed values. *)
Fixpoint scev_producer_advance {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (ix : scev_static_index N V K)
    (work : list (scev_work V)) (active : FinSet.t V) (done : Map.t V (scev_completed EV))
    (bindings : list (scev_prepared_binding EV)) (hits prepared : list V)
    : option (scev_producer_state EV) :=
  match work with
  | [] => Some (ScevProducerState [] active done bindings hits prepared)
  | command :: rest =>
    let st := ScevProducerState work active done bindings hits prepared in
    match command with
    | SVisit x =>
      if Map.mem EV x done then
        scev_producer_advance EN EV lv so ix rest active done bindings (x :: hits) prepared
      else if FinSet.mem EV x active then None
      else scev_expand_value EN EV lv so ix rest st x
    | SFinishAdd x a b | SFinishMul x a b =>
      match Map.get EV a done, Map.get EV b done with
      | Some expr_left, Some expr_right =>
        let multiply := match command with SFinishMul _ _ _ => true | _ => false end in
        scev_producer_advance EN EV lv so ix rest (FinSet.remove EV x active)
          (Map.set EV x (scev_complete_binary EV multiply x expr_left expr_right) done)
          bindings hits (x :: prepared)
      | _, _ => None
      end
    | SFinishPhi x base update other kind phi_first =>
      match Map.get EV other done with
      | Some e => scev_producer_advance EN EV lv so ix rest (FinSet.remove EV x active)
          (Map.set EV x (scev_complete_leaf EV (SPhi x)) done)
          (scev_complete_binding EV x base update kind phi_first e :: bindings)
          hits (x :: prepared)
      | None => None
      end
    end
  end.

(** Completed source visits reuse the stored prepared value before scheduling any dependency. *)
Lemma scev_producer_advance_reuses {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) ix x rest active done bindings
    hits prepared :
  Map.mem EV x done = true ->
  scev_producer_advance EN EV lv so ix (SVisit x :: rest) active done bindings hits prepared =
    scev_producer_advance EN EV lv so ix rest active done bindings (x :: hits) prepared.
Proof.
  intro Hdone; cbn [scev_producer_advance]; rewrite Hdone; reflexivity.
Qed.

(** The binary iteration budget counts fresh visits and absorbs completed work immediately. *)
Fixpoint scev_producer_iterate {V} {EV : encoding V} (fuel : positive)
    (next : scev_producer_state EV -> option (scev_producer_state EV))
    (st : scev_producer_state EV) : option (scev_producer_state EV) :=
  match sps_work st with
  | [] => Some st
  | _ =>
    match fuel with
    | xH => next st
    | xO p =>
      match scev_producer_iterate p next st with
      | Some st' => scev_producer_iterate p next st'
      | None => None
      end
    | xI p =>
      match scev_producer_iterate p next st with
      | Some st' =>
        match scev_producer_iterate p next st' with
        | Some st'' => next st''
        | None => None
        end
      | None => None
      end
    end
  end.

(** Integrated execution exposes the caches and preparation traces it actually used. *)
Record scev_recognition_execution {V} (EV : encoding V) : Type := ScevRecognitionExecution {
  sre_chrec : chrec V;
  sre_plan : scev_plan V;
  sre_preparation_hits : list V;
  sre_preparation_nodes : list V;
  sre_checker_cache : scev_shared_check_memo V;
  sre_compiler_cache : scev_shared_compile_memo V
}.

Arguments ScevRecognitionExecution {V EV}.
Arguments sre_chrec {V EV}.
Arguments sre_plan {V EV}.
Arguments sre_preparation_hits {V EV}.
Arguments sre_preparation_nodes {V EV}.
Arguments sre_checker_cache {V EV}.
Arguments sre_compiler_cache {V EV}.

(** Recognition prepares each completed dependency once and passes it to both shared consumers. *)
Definition recognise_plan_execution {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (inventory : list V) (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V)
    : option (scev_recognition_execution EV) :=
  let source_ix := scev_prepare_index EV inventory lv (ScevPlan [] x) in
  let next := fun st => scev_producer_advance EN EV lv so source_ix
    (sps_work st) (sps_active st) (sps_done st) (sps_bindings st)
    (sps_hits st) (sps_prepared st) in
  match scev_producer_iterate (Pos.of_succ_nat (length inventory)) next
    (ScevProducerState [SVisit x] FinSet.empty Map.empty [] [] []) with
  | Some st =>
    match sps_work st with
    | [] =>
      let bs := rev (sps_bindings st) in
      let plan := ScevPlan (map spb_source bs) x in
      let ix := ScevStaticIndex (ssi_values source_ix) (ssi_entry source_ix) (ssi_back source_ix)
        (scev_rank_index_from EV 0 (sp_bindings plan)) in
      let '(accepted, check_memo) := scev_check_shared_plan EN EV lv so ix bs x in
      if accepted then
        match scev_compile_shared_plan EV bs x with
        | Some (c, compile_memo) => Some
            (ScevRecognitionExecution c plan (sps_hits st) (sps_prepared st)
              check_memo compile_memo)
        | None => None
        end
      else None
    | _ => None
    end
  | None => None
  end.

(** Integrated recognition has exactly the public plan-checker and compiler observations. *)
Theorem recognise_plan_execution_checked {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) x execution :
  recognise_plan_execution EN EV inventory lv so x = Some execution ->
  sp_target (sre_plan execution) = x /\
  scev_plan_check EN EV inventory lv so (sre_plan execution) = true /\
  scev_compile_plan EV (sre_plan execution) = Some (sre_chrec execution).
Proof.
  unfold recognise_plan_execution.
  destruct (scev_producer_iterate _ _ _) as [st|] eqn:Hrun; [|discriminate].
  destruct (sps_work st) as [|command rest]; [|discriminate].
  destruct (scev_check_shared_plan _ _ _ _ _ _ _) as [accepted check_memo] eqn:Hcheck.
  destruct accepted; [|discriminate].
  destruct (scev_compile_shared_plan EV (rev (sps_bindings st)) x)
    as [[c compile_memo]|] eqn:Hcompile; [|discriminate].
  intro Heq; inversion Heq; subst execution; cbn [sre_plan sre_chrec sp_target].
  split; [reflexivity|]; split.
  - change (scev_check_shared_plan EN EV lv so
      (scev_prepare_index EV inventory lv
        (ScevPlan (map spb_source (rev (sps_bindings st))) x))
      (rev (sps_bindings st)) x = (true, check_memo)) in Hcheck.
    pose proof (scev_check_shared_plan_agrees EN EV lv so
      (scev_prepare_index EV inventory lv
        (ScevPlan (map spb_source (rev (sps_bindings st))) x))
      (rev (sps_bindings st)) x) as Hagrees.
    rewrite Hcheck in Hagrees; exact (eq_sym Hagrees).
  - pose proof (scev_compile_shared_plan_agrees EV (rev (sps_bindings st)) x) as Hagrees.
    rewrite Hcompile in Hagrees; exact (eq_sym Hagrees).
Qed.

(** The public result projects the checked plan and recurrence of integrated execution. *)
Definition recognise_plan {S O N E V K C} (EN : encoding N) (EV : encoding V)
    (inventory : list V) (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V)
    : option (chrec V * scev_plan V) :=
  option_map (fun execution => (sre_chrec execution, sre_plan execution))
    (recognise_plan_execution EN EV inventory lv so x).

(** Successful recognition returns its exact checked plan and its compiled recurrence. *)
Theorem recognise_plan_checked {S O N E V K C}
    (EN : encoding N) (EV : encoding V) (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V) ch plan :
  recognise_plan EN EV inventory lv so x = Some (ch, plan) ->
  sp_target plan = x /\ scev_plan_check EN EV inventory lv so plan = true /\
    scev_compile_plan EV plan = Some ch.
Proof.
  unfold recognise_plan.
  destruct (recognise_plan_execution EN EV inventory lv so x) as [execution|] eqn:Hrun;
    [|discriminate].
  cbn [option_map]; intro Heq; inversion Heq; subst ch plan.
  exact (recognise_plan_execution_checked EN EV inventory lv so x execution Hrun).
Qed.

(** Recurrence recognition projects the recurrence of a successful checked plan producer. *)
Definition recognise {S O N E V K C} (EN : encoding N) (EV : encoding V) (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V) : option (chrec V) :=
  option_map fst (recognise_plan EN EV inventory lv so x).

(** * Independent expression conditions *)

(** An earlier phi is witnessed by its actual position in the declarative binding list. *)
Definition scev_earlier {V} (bs : list (scev_binding V)) (rank : nat) (x : V) : Prop :=
  exists i b, nth_error bs i = Some b /\ sb_phi b = x /\ (i < rank)%nat.

(** Every successful rank lookup names an actual binding at its recorded position. *)
Lemma scev_rank_index_source {V} (EV : encoding V) bs start x rank :
  Map.get EV x (sri_ranks (scev_rank_index_from EV start bs)) = Some rank ->
  exists i b, nth_error bs i = Some b /\ sb_phi b = x /\ rank = (start + i)%nat.
Proof.
  revert start rank; induction bs as [|b bs IH]; intros start rank Hget.
  - cbn [scev_rank_index_from sri_ranks] in Hget; rewrite Map.get_empty in Hget;
      discriminate.
  - cbn [scev_rank_index_from sri_ranks] in Hget.
    destruct (Pos.eq_dec (encode EV x) (encode EV (sb_phi b))) as [Heq|Hne].
    + apply (encode_injective EV) in Heq; subst x.
      rewrite Map.get_set_same in Hget; inversion Hget; subst rank.
      exists 0%nat, b; split; [reflexivity|]; split; [reflexivity|lia].
    + rewrite Map.get_set_other in Hget by (intro Heq; subst x; contradiction).
      destruct (IH (S start) rank Hget) as [i [a [Hnth [Hphi Hrank]]]].
      exists (S i), a; split; [exact Hnth|]; split; [exact Hphi|lia].
Qed.

(** Prepared rank comparisons express precisely the strictly earlier binding relation. *)
Theorem scev_rank_index_earlier {V} (EV : encoding V) bs rank x :
  NoDup (map sb_phi bs) ->
  (exists i, Map.get EV x (sri_ranks (scev_rank_index_from EV 0 bs)) = Some i /\
    (i < rank)%nat) <-> scev_earlier bs rank x.
Proof.
  intro Hdistinct; split.
  - intros [i [Hget Hlt]].
    destruct (scev_rank_index_source EV bs 0 x i Hget)
      as [j [b [Hnth [Hphi Heq]]]].
    exists j, b; split; [exact Hnth|]; split; [exact Hphi|lia].
  - intros [i [b [Hnth [Hphi Hlt]]]]; exists i; split; [|exact Hlt].
    subst x; exact (scev_rank_index_get EV bs 0 i b Hdistinct Hnth).
Qed.

(** These source conditions describe expression trees without referring to an executable checker. *)
Inductive scev_expression_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C)
    (bs : list (scev_binding V)) (rank : nat) : scev_expr V -> Prop :=
  | ScevOutsideValid : forall x,
      In x inventory -> lbody lv (home (lssa lv) x) = false ->
      scev_expression_valid inventory lv so bs rank (SOutside x)
  | ScevPhiValid : forall x,
      In x inventory -> scev_earlier bs rank x ->
      scev_expression_valid inventory lv so bs rank (SPhi x)
  | ScevAddValid : forall x a b o,
      In x inventory -> lbody lv (home (lssa lv) x) = true ->
      def (lssa lv) x = Op o [scev_expr_root a; scev_expr_root b] -> add_op so o = true ->
      scev_expression_valid inventory lv so bs rank a ->
      scev_expression_valid inventory lv so bs rank b ->
      scev_expression_valid inventory lv so bs rank (SAdd x a b)
  | ScevMulValid : forall x a b o,
      In x inventory -> lbody lv (home (lssa lv) x) = true ->
      def (lssa lv) x = Op o [scev_expr_root a; scev_expr_root b] -> mul_op so o = true ->
      scev_expression_valid inventory lv so bs rank a ->
      scev_expression_valid inventory lv so bs rank b ->
      scev_expression_valid inventory lv so bs rank (SMul x a b)
  | ScevConstValid : forall x z o,
      In x inventory -> lbody lv (home (lssa lv) x) = true ->
      def (lssa lv) x = Op o [] -> const_op so o = Some z ->
      scev_expression_valid inventory lv so bs rank (SConst x z).

(** A prepared binary test is equivalent to the original source's exact operation shape. *)
Lemma scev_source_binary_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) flag x a b :
  scev_binary_check EV (lbody lv) (scev_inventory_index EV (lssa lv) inventory)
    flag x a b = true <->
  In x inventory /\ lbody lv (home (lssa lv) x) = true /\
    exists o, def (lssa lv) x = Op o [a; b] /\ flag o = true.
Proof.
  rewrite scev_binary_check_correct; split.
  - intros [n [o [Hget [Hbody Hflag]]]].
    destruct (scev_inventory_index_sound EV (lssa lv) inventory x _ Hget)
      as [Hin Heq]; inversion Heq; subst n.
    split; [exact Hin|]; split; [exact Hbody|]; exists o; split; [congruence|exact Hflag].
  - intros [Hin [Hbody [o [Hdef Hflag]]]].
    exists (home (lssa lv) x), o; split.
    + rewrite scev_inventory_index_get by exact Hin; rewrite Hdef; reflexivity.
    + split; assumption.
Qed.

(** A prepared literal test is equivalent to the original source's exact constant definition. *)
Lemma scev_source_constant_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) x z :
  scev_constant_check EV (lbody lv) (scev_inventory_index EV (lssa lv) inventory)
    so x z = true <->
  In x inventory /\ lbody lv (home (lssa lv) x) = true /\
    exists o, def (lssa lv) x = Op o [] /\ const_op so o = Some z.
Proof.
  rewrite scev_constant_check_correct; split.
  - intros [n [o [Hget [Hbody Hconst]]]].
    destruct (scev_inventory_index_sound EV (lssa lv) inventory x _ Hget)
      as [Hin Heq]; inversion Heq; subst n.
    split; [exact Hin|]; split; [exact Hbody|]; exists o; split; [congruence|exact Hconst].
  - intros [Hin [Hbody [o [Hdef Hconst]]]].
    exists (home (lssa lv) x), o; split.
    + rewrite scev_inventory_index_get by exact Hin; rewrite Hdef; reflexivity.
    + split; assumption.
Qed.

(** Expression dependencies are exactly the phi leaves, retaining their syntactic occurrences. *)
Fixpoint scev_expression_phis {V} (e : scev_expr V) : list V :=
  match e with
  | SOutside _ => []
  | SPhi x => [x]
  | SAdd _ a b => scev_expression_phis a ++ scev_expression_phis b
  | SMul _ a b => scev_expression_phis a ++ scev_expression_phis b
  | SConst _ _ => []
  end.

(** Accepted expression dependency sets contain precisely the declarative phi leaves. *)
Theorem scev_expression_dependencies {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank e :
  fst (scev_expr_check_reference EV body ix so rank e) = true ->
  forall x, FinSet.mem EV x (snd (scev_expr_check_reference EV body ix so rank e)) = true <->
    In x (scev_expression_phis e).
Proof.
  induction e as [y|y|y a IHa b IHb|y a IHa b IHb|y z].
  - intros Hvalid x; cbn [scev_expr_check_reference snd scev_expression_phis].
    rewrite FinSet.mem_empty; split; [discriminate|contradiction].
  - intros Hvalid x; cbn [scev_expr_check_reference snd scev_expression_phis].
    rewrite FinSet.mem_add, FinSet.mem_empty; cbn; intuition congruence.
  - cbn [scev_expr_check_reference fst].
    destruct (scev_binary_check EV body (ssi_values ix) (add_op so) y
      (scev_expr_root a) (scev_expr_root b)); [|discriminate].
    destruct (scev_expr_check_reference EV body ix so rank a) as [va da] eqn:Ha.
    destruct va; [|discriminate].
    destruct (scev_expr_check_reference EV body ix so rank b) as [vb db] eqn:Hb.
    cbn [fst]; intro Hvalid; subst vb; intro x.
    specialize (IHa eq_refl x); specialize (IHb eq_refl x); cbn [snd] in *.
    cbn [scev_expression_phis]; rewrite FinSet.mem_union, IHa, IHb, in_app_iff; reflexivity.
  - cbn [scev_expr_check_reference fst].
    destruct (scev_binary_check EV body (ssi_values ix) (mul_op so) y
      (scev_expr_root a) (scev_expr_root b)); [|discriminate].
    destruct (scev_expr_check_reference EV body ix so rank a) as [va da] eqn:Ha.
    destruct va; [|discriminate].
    destruct (scev_expr_check_reference EV body ix so rank b) as [vb db] eqn:Hb.
    cbn [fst]; intro Hvalid; subst vb; intro x.
    specialize (IHa eq_refl x); specialize (IHb eq_refl x); cbn [snd] in *.
    cbn [scev_expression_phis]; rewrite FinSet.mem_union, IHa, IHb, in_app_iff; reflexivity.
  - intros Hvalid x; cbn [scev_expr_check_reference snd scev_expression_phis].
    rewrite FinSet.mem_empty; split; [discriminate|contradiction].
Qed.

(** The prepared outside-leaf test requires inventory membership and an outside source home. *)
Lemma scev_source_outside_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) x :
  (match Map.get EV x (scev_inventory_index EV (lssa lv) inventory) with
  | Some (n, _) => negb (lbody lv n)
  | None => false
  end) = true <-> In x inventory /\ lbody lv (home (lssa lv) x) = false.
Proof.
  destruct (Map.get EV x (scev_inventory_index EV (lssa lv) inventory))
    as [[n d]|] eqn:Hget; cbn.
  - destruct (scev_inventory_index_sound EV (lssa lv) inventory x _ Hget)
      as [Hin Heq]; inversion Heq; subst n d.
    rewrite Bool.negb_true_iff; intuition.
  - split; [discriminate|intros [Hin Hbody]].
    rewrite scev_inventory_index_get in Hget by exact Hin; discriminate.
Qed.

(** The prepared phi-leaf test requires inventory membership and a strictly earlier binding. *)
Lemma scev_source_phi_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) bs rank x :
  NoDup (map sb_phi bs) ->
  (Map.mem EV x (scev_inventory_index EV (lssa lv) inventory) &&
    match Map.get EV x (sri_ranks (scev_rank_index_from EV 0 bs)) with
    | Some i => Nat.ltb i rank
    | None => false
    end) = true <-> In x inventory /\ scev_earlier bs rank x.
Proof.
  intro Hdistinct; rewrite Bool.andb_true_iff, scev_inventory_index_mem.
  rewrite <- (scev_rank_index_earlier EV bs rank x Hdistinct).
  destruct (Map.get EV x (sri_ranks (scev_rank_index_from EV 0 bs))) as [i|];
    [rewrite Nat.ltb_lt|]; split.
  - intros [Hin Hlt]; split; [exact Hin|exists i; split; [reflexivity|exact Hlt]].
  - intros [Hin [j [Heq Hlt]]]; inversion Heq; subst j; split; assumption.
  - intros [_ Hbad]; discriminate.
  - intros [_ [j [Hbad _]]]; discriminate.
Qed.

(** Binary acceptance requires all three local and child booleans, including failure propagation. *)
Lemma scev_binary_accepts (local left right : bool) :
  (if local then if left then right else false else false) = true <->
    local = true /\ left = true /\ right = true.
Proof.
  destruct local, left, right; cbn; intuition discriminate.
Qed.

Lemma scev_fst_if {A B} (test : bool) (left right : A * B) :
  fst (if test then left else right) = if test then fst left else fst right.
Proof.
  destruct test; reflexivity.
Qed.

(** The tree checker accepts exactly the independent inventory, rank and source-expression laws. *)
Theorem scev_expression_valid_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) p rank e :
  NoDup (map sb_phi (sp_bindings p)) ->
  fst (scev_expr_check_reference EV (lbody lv) (scev_prepare_index EV inventory lv p)
    so rank e) = true <-> scev_expression_valid inventory lv so (sp_bindings p) rank e.
Proof.
  intro Hdistinct; induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z].
  - change ((match Map.get EV x (scev_inventory_index EV (lssa lv) inventory) with
      | Some (n, _) => negb (lbody lv n)
      | None => false
      end) = true <-> scev_expression_valid inventory lv so (sp_bindings p) rank (SOutside x)).
    rewrite scev_source_outside_correct; split.
    + intros [Hin Hhome]; constructor; assumption.
    + intro Hvalid; inversion Hvalid; subst; split; assumption.
  - change ((Map.mem EV x (scev_inventory_index EV (lssa lv) inventory) &&
      match Map.get EV x (sri_ranks (scev_rank_index_from EV 0 (sp_bindings p))) with
      | Some i => Nat.ltb i rank
      | None => false
      end) = true <-> scev_expression_valid inventory lv so (sp_bindings p) rank (SPhi x)).
    rewrite scev_source_phi_correct by exact Hdistinct; split.
    + intros [Hin Hearlier]; constructor; assumption.
    + intro Hvalid; inversion Hvalid; subst; split; assumption.
  - cbn [scev_expr_check_reference]; rewrite !scev_fst_if.
    change ((if scev_binary_check EV (lbody lv)
      (scev_inventory_index EV (lssa lv) inventory) (add_op so) x
      (scev_expr_root a) (scev_expr_root b) then
      if fst (scev_expr_check_reference EV (lbody lv) (scev_prepare_index EV inventory lv p)
        so rank a) then
        fst (scev_expr_check_reference EV (lbody lv) (scev_prepare_index EV inventory lv p)
          so rank b) else false else false) = true <->
      scev_expression_valid inventory lv so (sp_bindings p) rank (SAdd x a b)).
    rewrite scev_binary_accepts, scev_source_binary_correct, IHa, IHb; split.
    + intros [[Hin [Hhome [o [Hdef Hflag]]]] [Ha Hb]].
      eapply ScevAddValid; eassumption.
    + intro Hvalid; inversion Hvalid; subst; split; [|split; assumption].
      split; [assumption|]; split; [assumption|]; eexists; split; eassumption.
  - cbn [scev_expr_check_reference]; rewrite !scev_fst_if.
    change ((if scev_binary_check EV (lbody lv)
      (scev_inventory_index EV (lssa lv) inventory) (mul_op so) x
      (scev_expr_root a) (scev_expr_root b) then
      if fst (scev_expr_check_reference EV (lbody lv) (scev_prepare_index EV inventory lv p)
        so rank a) then
        fst (scev_expr_check_reference EV (lbody lv) (scev_prepare_index EV inventory lv p)
          so rank b) else false else false) = true <->
      scev_expression_valid inventory lv so (sp_bindings p) rank (SMul x a b)).
    rewrite scev_binary_accepts, scev_source_binary_correct, IHa, IHb; split.
    + intros [[Hin [Hhome [o [Hdef Hflag]]]] [Ha Hb]].
      eapply ScevMulValid; eassumption.
    + intro Hvalid; inversion Hvalid; subst; split; [|split; assumption].
      split; [assumption|]; split; [assumption|]; eexists; split; eassumption.
  - change (scev_constant_check EV (lbody lv)
      (scev_inventory_index EV (lssa lv) inventory) so x z = true <->
      scev_expression_valid inventory lv so (sp_bindings p) rank (SConst x z)).
    rewrite scev_source_constant_correct; split.
    + intros [Hin [Hhome [o [Hdef Hconst]]]]; eapply ScevConstValid; eassumption.
    + intro Hvalid; inversion Hvalid; subst.
      split; [assumption|]; split; [assumption|]; eexists; split; eassumption.
Qed.

(** The executable memoized checker accepts exactly the independent expression conditions. *)
Theorem scev_check_expression_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) p rank e :
  NoDup (map sb_phi (sp_bindings p)) ->
  fst (fst (scev_check_expr EV (lbody lv) (scev_prepare_index EV inventory lv p)
    so rank (scev_prepare_expr EV e) Map.empty)) = true <->
  scev_expression_valid inventory lv so (sp_bindings p) rank e.
Proof.
  intro Hdistinct; rewrite scev_check_expr_agrees.
  apply scev_expression_valid_correct; exact Hdistinct.
Qed.

(** The header condition fixes a binding's actual parameter position and both selected arguments. *)
Definition scev_binding_header_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (b : scev_binding V) : Prop :=
  In (sb_phi b) inventory /\ In (sb_base b) inventory /\
  In (sb_update_value b) inventory /\ home (lssa lv) (sb_phi b) = lheader lv /\
  lbody lv (home (lssa lv) (sb_base b)) = false /\
  lbody lv (home (lssa lv) (sb_update_value b)) = true /\
  exists i, def (lssa lv) (sb_phi b) = Param (lheader lv) i /\
    nth_error (edge_args (lssa lv) (lentry lv)) i = Some (sb_base b) /\
    nth_error (edge_args (lssa lv) (lback lv)) i = Some (sb_update_value b).

(** Ordinary update conditions preserve operand order and exclude an additional direct feedback. *)
Definition scev_ordinary_update_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (flag : K -> bool) (b : scev_binding V)
    (e : scev_expr V) : Prop :=
  scev_expr_root e <> sb_phi b /\ In (sb_update_value b) inventory /\
  lbody lv (home (lssa lv) (sb_update_value b)) = true /\
  exists o, def (lssa lv) (sb_update_value b) =
    Op o (if sb_phi_first b then [sb_phi b; scev_expr_root e]
      else [scev_expr_root e; sb_phi b]) /\ flag o = true.

(** Update validity states the three supported feedback forms using original source definitions. *)
Definition scev_update_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C)
    (bs : list (scev_binding V)) (rank : nat) (b : scev_binding V) : Prop :=
  match sb_kind b, sb_other b with
  | SAddUpdate, Some e =>
    scev_ordinary_update_valid inventory lv (add_op so) b e /\
      scev_expression_valid inventory lv so bs rank e
  | SMulUpdate, Some e =>
    scev_ordinary_update_valid inventory lv (mul_op so) b e /\
      scev_expression_valid inventory lv so bs rank e
  | SDoubleUpdate, None =>
    sb_phi_first b = true /\ In (sb_update_value b) inventory /\
      lbody lv (home (lssa lv) (sb_update_value b)) = true /\
      exists o, def (lssa lv) (sb_update_value b) = Op o [sb_phi b; sb_phi b] /\
        add_op so o = true
  | _, _ => False
  end.

(** Binding validity combines its incoming-parameter equations and supported feedback expression. *)
Definition scev_binding_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C)
    (bs : list (scev_binding V)) (rank : nat) (b : scev_binding V) : Prop :=
  scev_binding_header_valid inventory lv b /\ scev_update_valid inventory lv so bs rank b.

(** A false encoded key comparison is exactly source-value disequality. *)
Lemma scev_key_ne_spec {A} (EA : encoding A) x y :
  negb (scev_key_eq EA x y) = true <-> x <> y.
Proof.
  rewrite Bool.negb_true_iff; split.
  - intros Hfalse Heq; subst y.
    pose proof (proj2 (scev_key_eq_spec EA x x) eq_refl); congruence.
  - intro Hne; destruct (scev_key_eq EA x y) eqn:Heq; [|reflexivity].
    apply scev_key_eq_spec in Heq; contradiction.
Qed.

(** The ordinary update's local boolean checks precisely its source operand and feedback laws. *)
Lemma scev_ordinary_update_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) flag (b : scev_binding V) e :
  (negb (scev_key_eq EV (scev_expr_root e) (sb_phi b)) &&
    scev_binary_check EV (lbody lv) (scev_inventory_index EV (lssa lv) inventory) flag
      (sb_update_value b) (if sb_phi_first b then sb_phi b else scev_expr_root e)
      (if sb_phi_first b then scev_expr_root e else sb_phi b)) = true <->
  scev_ordinary_update_valid inventory lv flag b e.
Proof.
  rewrite Bool.andb_true_iff, scev_key_ne_spec, scev_source_binary_correct.
  unfold scev_ordinary_update_valid; destruct (sb_phi_first b); reflexivity.
Qed.

(** Update checking accepts exactly the independent supported-feedback conditions. *)
Theorem scev_check_update_correct {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) p rank b :
  NoDup (map sb_phi (sp_bindings p)) ->
  (exists deps, scev_check_update EV (lbody lv) (scev_prepare_index EV inventory lv p) so
    rank b (option_map (scev_prepare_expr EV) (sb_other b)) = Some deps) <->
  scev_update_valid inventory lv so (sp_bindings p) rank b.
Proof.
  intro Hdistinct.
  destruct b as [phi base update kind other first]; destruct kind;
    destruct other as [e|]; cbn [scev_check_update scev_update_valid sb_kind sb_other
      sb_phi sb_update_value sb_phi_first option_map];
    try (split; [intros [deps Hbad]; discriminate|contradiction]).
  - rewrite scev_prepare_expr_root.
    pose proof (scev_ordinary_update_correct EV inventory lv (add_op so)
      (ScevBinding phi base update SAddUpdate (Some e) first) e) as Hlocal.
    cbn [sb_phi sb_update_value sb_phi_first] in Hlocal.
    destruct (negb (scev_key_eq EV (scev_expr_root e) phi) &&
      scev_binary_check EV (lbody lv) (ssi_values (scev_prepare_index EV inventory lv p))
        (add_op so) update (if first then phi else scev_expr_root e)
        (if first then scev_expr_root e else phi)) eqn:Hshape.
    + apply Hlocal in Hshape.
      pose proof (scev_check_expression_correct EV inventory lv so p rank e Hdistinct) as Hexpr.
      destruct (scev_check_expr EV (lbody lv) (scev_prepare_index EV inventory lv p)
        so rank (scev_prepare_expr EV e) Map.empty) as [[accept deps] memo] eqn:Hrun.
      cbn [fst] in Hexpr; destruct accept; cbn; split.
      * intros _; split; [exact Hshape|apply Hexpr; reflexivity].
      * intros _; exists deps; reflexivity.
      * intros [d Hbad]; discriminate.
      * intros [_ Hvalid]; apply Hexpr in Hvalid; discriminate.
    + split; [intros [deps Hbad]; discriminate|intros [Hvalid _]].
      apply Hlocal in Hvalid; cbn [scev_prepare_index ssi_values] in Hshape; congruence.
  - rewrite scev_prepare_expr_root.
    pose proof (scev_ordinary_update_correct EV inventory lv (mul_op so)
      (ScevBinding phi base update SMulUpdate (Some e) first) e) as Hlocal.
    cbn [sb_phi sb_update_value sb_phi_first] in Hlocal.
    destruct (negb (scev_key_eq EV (scev_expr_root e) phi) &&
      scev_binary_check EV (lbody lv) (ssi_values (scev_prepare_index EV inventory lv p))
        (mul_op so) update (if first then phi else scev_expr_root e)
        (if first then scev_expr_root e else phi)) eqn:Hshape.
    + apply Hlocal in Hshape.
      pose proof (scev_check_expression_correct EV inventory lv so p rank e Hdistinct) as Hexpr.
      destruct (scev_check_expr EV (lbody lv) (scev_prepare_index EV inventory lv p)
        so rank (scev_prepare_expr EV e) Map.empty) as [[accept deps] memo] eqn:Hrun.
      cbn [fst] in Hexpr; destruct accept; cbn; split.
      * intros _; split; [exact Hshape|apply Hexpr; reflexivity].
      * intros _; exists deps; reflexivity.
      * intros [d Hbad]; discriminate.
      * intros [_ Hvalid]; apply Hexpr in Hvalid; discriminate.
    + split; [intros [deps Hbad]; discriminate|intros [Hvalid _]].
      apply Hlocal in Hvalid; cbn [scev_prepare_index ssi_values] in Hshape; congruence.
  - pose proof (scev_source_binary_correct EV inventory lv (add_op so) update phi phi)
      as Hsource.
    destruct (first && scev_binary_check EV (lbody lv)
      (ssi_values (scev_prepare_index EV inventory lv p)) (add_op so) update phi phi)
      eqn:Hshape; split.
    + intro Hsuccess; apply Bool.andb_true_iff in Hshape.
      destruct Hshape as [Hfirst Hbinary]; apply Hsource in Hbinary; tauto.
    + intro Hvalid; exists FinSet.empty; reflexivity.
    + intros [deps Hbad]; discriminate.
    + intros [Hfirst Hbinary]; apply Hsource in Hbinary.
      assert (Htrue : first && scev_binary_check EV (lbody lv)
        (ssi_values (scev_prepare_index EV inventory lv p)) (add_op so) update phi phi = true).
      { apply Bool.andb_true_iff; split; assumption. }
      congruence.
Qed.

(** Successful binding checking establishes the exact source phi and preserves the update result. *)
Theorem scev_check_binding_header_sound {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C)
    p rank b other deps :
  scev_check_binding EN EV lv so (scev_prepare_index EV inventory lv p) rank b other =
    Some deps ->
  scev_binding_header_valid inventory lv b /\
    scev_check_update EV (lbody lv) (scev_prepare_index EV inventory lv p)
      so rank b other = Some deps.
Proof.
  unfold scev_check_binding; cbn [scev_prepare_index ssi_values ssi_entry ssi_back].
  destruct (Map.get EV (sb_phi b) (scev_inventory_index EV (lssa lv) inventory))
    as [[phi_home phi_def]|] eqn:Hphi; [|discriminate].
  destruct phi_def as [o args|header i|]; try discriminate.
  destruct (Map.get EV (sb_base b) (scev_inventory_index EV (lssa lv) inventory))
    as [[base_home base_def]|] eqn:Hbase; [|discriminate].
  destruct (Map.get EV (sb_update_value b) (scev_inventory_index EV (lssa lv) inventory))
    as [[update_home update_def]|] eqn:Hupdate; [|discriminate].
  destruct (scev_key_eq EN phi_home (lheader lv) && scev_key_eq EN header (lheader lv) &&
    negb (lbody lv base_home) && lbody lv update_home) eqn:Hhomes; [|discriminate].
  rewrite !AnalysesNumbering.NumberingIndex.argument_index_get.
  destruct (nth_error (edge_args (lssa lv) (lentry lv)) i) as [base_arg|] eqn:Hentry;
    [|discriminate].
  destruct (nth_error (edge_args (lssa lv) (lback lv)) i) as [back_arg|] eqn:Hback;
    [|discriminate].
  destruct (scev_key_eq EV base_arg (sb_base b) &&
    scev_key_eq EV back_arg (sb_update_value b)) eqn:Hargs; [|discriminate].
  intro Hsuccess; split; [|exact Hsuccess].
  apply Bool.andb_true_iff in Hargs; destruct Hargs as [Hbase_arg Hback_arg].
  apply scev_key_eq_spec in Hbase_arg; apply scev_key_eq_spec in Hback_arg;
    subst base_arg back_arg.
  rewrite !Bool.andb_true_iff, !scev_key_eq_spec, Bool.negb_true_iff in Hhomes.
  destruct Hhomes as [[[Hphi_home Hheader] Hbase_home] Hupdate_home].
  subst phi_home header.
  destruct (scev_inventory_index_sound EV (lssa lv) inventory (sb_phi b) _ Hphi)
    as [Hinphi Heqphi].
  destruct (scev_inventory_index_sound EV (lssa lv) inventory (sb_base b) _ Hbase)
    as [Hinbase Heqbase].
  destruct (scev_inventory_index_sound EV (lssa lv) inventory (sb_update_value b) _ Hupdate)
    as [Hinupdate Hequpdate].
  inversion Heqphi; inversion Heqbase; inversion Hequpdate; subst base_home update_home.
  unfold scev_binding_header_valid; repeat split; try assumption; try congruence.
  exists i; repeat split; assumption || congruence.
Qed.

(** A source-valid phi header leaves precisely the separately checked feedback obligation. *)
Theorem scev_check_binding_header_complete {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C)
    p rank b other :
  scev_binding_header_valid inventory lv b ->
  scev_check_binding EN EV lv so (scev_prepare_index EV inventory lv p) rank b other =
    scev_check_update EV (lbody lv) (scev_prepare_index EV inventory lv p) so rank b other.
Proof.
  intros [Hinphi [Hinbase [Hinupdate [Hhome [Hbase [Hupdate [i [Hdef [Hentry Hback]]]]]]]]].
  unfold scev_check_binding; cbn [scev_prepare_index ssi_values ssi_entry ssi_back].
  rewrite !scev_inventory_index_get by assumption.
  rewrite Hdef, Hhome, Hbase, Hupdate.
  rewrite !AnalysesNumbering.NumberingIndex.argument_index_get, Hentry, Hback.
  assert (Hnode : scev_key_eq EN (lheader lv) (lheader lv) = true).
  { apply scev_key_eq_spec; reflexivity. }
  assert (Hbase_key : scev_key_eq EV (sb_base b) (sb_base b) = true).
  { apply scev_key_eq_spec; reflexivity. }
  assert (Hupdate_key : scev_key_eq EV (sb_update_value b) (sb_update_value b) = true).
  { apply scev_key_eq_spec; reflexivity. }
  rewrite Hnode, Hbase_key, Hupdate_key; reflexivity.
Qed.

(** A binding is accepted exactly when its independent phi and feedback source conditions hold. *)
Theorem scev_check_binding_correct {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C)
    p rank b :
  NoDup (map sb_phi (sp_bindings p)) ->
  (exists deps, scev_check_binding EN EV lv so (scev_prepare_index EV inventory lv p)
    rank b (option_map (scev_prepare_expr EV) (sb_other b)) = Some deps) <->
  scev_binding_valid inventory lv so (sp_bindings p) rank b.
Proof.
  intro Hdistinct; split.
  - intros [deps Hchecked].
    destruct (scev_check_binding_header_sound EN EV inventory lv so p rank b _ deps Hchecked)
      as [Hheader Hupdate].
    split; [exact Hheader|].
    apply (proj1 (scev_check_update_correct EV inventory lv so p rank b Hdistinct)).
    exists deps; exact Hupdate.
  - intros [Hheader Hvalid].
    destruct (proj2 (scev_check_update_correct EV inventory lv so p rank b Hdistinct) Hvalid)
      as [deps Hupdate].
    exists deps; rewrite scev_check_binding_header_complete by exact Hheader; exact Hupdate.
Qed.

(** Valid expression dependencies always name completed, strictly lower-ranked phis. *)
Theorem scev_expression_earlier {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rank e :
  scev_expression_valid inventory lv so bs rank e ->
  forall x, In x (scev_expression_phis e) -> scev_earlier bs rank x.
Proof.
  intro Hvalid; induction Hvalid; intros y Hin; cbn [scev_expression_phis] in Hin;
    try contradiction.
  - destruct Hin as [Heq|Hbad]; [subst y; assumption|contradiction].
  - apply in_app_iff in Hin; destruct Hin; [apply IHHvalid1|apply IHHvalid2]; assumption.
  - apply in_app_iff in Hin; destruct Hin; [apply IHHvalid1|apply IHHvalid2]; assumption.
Qed.

(** A binding's dependency list contains exactly its other expression's phi leaves. *)
Definition scev_binding_phis {V} (b : scev_binding V) : list V :=
  match sb_other b with
  | Some e => scev_expression_phis e
  | None => []
  end.

(** Successful update checking emits exactly the binding's declarative dependencies. *)
Theorem scev_check_update_dependencies {N V K C} (EV : encoding V) (body : N -> bool)
    (ix : scev_static_index N V K) (so : scev_ops K C) rank b deps :
  scev_check_update EV body ix so rank b
    (option_map (scev_prepare_expr EV) (sb_other b)) = Some deps ->
  forall x, FinSet.mem EV x deps = true <-> In x (scev_binding_phis b).
Proof.
  destruct b as [phi base update kind other first]; destruct kind;
    destruct other as [e|]; cbn [scev_check_update sb_other sb_kind sb_phi
      sb_update_value sb_phi_first option_map]; try discriminate.
  - destruct (negb (scev_key_eq EV (scev_prepared_root (scev_prepare_expr EV e)) phi) &&
      scev_binary_check EV body (ssi_values ix) (add_op so) update
        (if first then phi else scev_prepared_root (scev_prepare_expr EV e))
        (if first then scev_prepared_root (scev_prepare_expr EV e) else phi));
      [|discriminate].
    pose proof (scev_check_expr_agrees EV body ix so rank e) as Hagrees.
    destruct (scev_check_expr EV body ix so rank (scev_prepare_expr EV e) Map.empty)
      as [[accept found] memo] eqn:Hrun; cbn [fst] in Hagrees.
    destruct accept; [|discriminate]; intro Heq; inversion Heq; subst deps.
    intros x; cbn [scev_binding_phis sb_other].
    pose proof (scev_expression_dependencies EV body ix so rank e) as Hdeps.
    rewrite <- Hagrees in Hdeps; cbn [fst snd] in Hdeps; exact (Hdeps eq_refl x).
  - destruct (negb (scev_key_eq EV (scev_prepared_root (scev_prepare_expr EV e)) phi) &&
      scev_binary_check EV body (ssi_values ix) (mul_op so) update
        (if first then phi else scev_prepared_root (scev_prepare_expr EV e))
        (if first then scev_prepared_root (scev_prepare_expr EV e) else phi));
      [|discriminate].
    pose proof (scev_check_expr_agrees EV body ix so rank e) as Hagrees.
    destruct (scev_check_expr EV body ix so rank (scev_prepare_expr EV e) Map.empty)
      as [[accept found] memo] eqn:Hrun; cbn [fst] in Hagrees.
    destruct accept; [|discriminate]; intro Heq; inversion Heq; subst deps.
    intros x; cbn [scev_binding_phis sb_other].
    pose proof (scev_expression_dependencies EV body ix so rank e) as Hdeps.
    rewrite <- Hagrees in Hdeps; cbn [fst snd] in Hdeps; exact (Hdeps eq_refl x).
  - destruct (first && scev_binary_check EV body (ssi_values ix) (add_op so)
      update phi phi); [|discriminate].
    intro Heq; inversion Heq; subst deps; intro x.
    cbn [scev_binding_phis sb_other]; rewrite FinSet.mem_empty;
      split; [discriminate|contradiction].
Qed.

(** Successful binding checking preserves the exact declared phi dependency occurrences as a set. *)
Theorem scev_check_binding_dependencies {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C)
    p rank b deps :
  scev_check_binding EN EV lv so (scev_prepare_index EV inventory lv p) rank b
    (option_map (scev_prepare_expr EV) (sb_other b)) = Some deps ->
  forall x, FinSet.mem EV x deps = true <-> In x (scev_binding_phis b).
Proof.
  intro Hchecked.
  destruct (scev_check_binding_header_sound EN EV inventory lv so p rank b _ deps Hchecked)
    as [_ Hupdate].
  eapply scev_check_update_dependencies; exact Hupdate.
Qed.

(** A row edge follows one declared phi dependency, independently of the reachability checker. *)
Definition scev_row_edge {V} (EV : encoding V) (rows : list (V * FinSet.t V)) x y : Prop :=
  exists deps, In (x, deps) rows /\ FinSet.mem EV y deps = true.

(** Reachability is ordinary finite graph reachability from the supplied target set. *)
Inductive scev_row_reachable {V} (EV : encoding V) (rows : list (V * FinSet.t V))
    (seeds : FinSet.t V) : V -> Prop :=
  | ScevRowSeed : forall x,
      FinSet.mem EV x seeds = true -> scev_row_reachable EV rows seeds x
  | ScevRowStep : forall x y,
      scev_row_reachable EV rows seeds x -> scev_row_edge EV rows x y ->
      scev_row_reachable EV rows seeds y.

(** Triangular rows are distinct and every edge points to a strictly later row. *)
Inductive scev_rows_triangular {V} (EV : encoding V) : list (V * FinSet.t V) -> Prop :=
  | ScevRowsNil : scev_rows_triangular EV []
  | ScevRowsCons : forall x deps rows,
      ~ In x (map fst rows) ->
      (forall y, FinSet.mem EV y deps = true -> In y (map fst rows)) ->
      scev_rows_triangular EV rows -> scev_rows_triangular EV ((x, deps) :: rows).

(** Every dependency of a triangular row is another listed row. *)
Lemma scev_rows_closed {V} (EV : encoding V) rows : scev_rows_triangular EV rows ->
  forall x y, scev_row_edge EV rows x y -> In y (map fst rows).
Proof.
  intro Htriangle; induction Htriangle as [|x deps rows Hfresh Hdeps Htriangle IH];
    intros a y [found [Hin Hmember]]; cbn in Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst a found; right; apply Hdeps; exact Hmember.
  - right; apply (IH a y); exists found; split; assumption.
Qed.

(** The first triangular row has no incoming edge from any remaining row. *)
Lemma scev_rows_head_no_incoming {V} (EV : encoding V) x deps rows :
  scev_rows_triangular EV ((x, deps) :: rows) ->
  forall y, ~ scev_row_edge EV ((x, deps) :: rows) y x.
Proof.
  intro Htriangle; inversion Htriangle as [|a ds rest Hfresh Hdeps Htail]; subst.
  intros y [found [[Heq|Hin] Hmember]].
  - inversion Heq; subst y found; apply Hfresh; apply Hdeps; exact Hmember.
  - apply Hfresh; apply (scev_rows_closed EV rows Htail y x).
    exists found; split; assumption.
Qed.

(** A reachable first triangular row must itself be a seed. *)
Lemma scev_rows_head_seed {V} (EV : encoding V) x deps rows seeds :
  scev_rows_triangular EV ((x, deps) :: rows) ->
  scev_row_reachable EV ((x, deps) :: rows) seeds x -> FinSet.mem EV x seeds = true.
Proof.
  intros Htriangle Hreachable; inversion Hreachable; subst; [assumption|].
  exfalso; eapply scev_rows_head_no_incoming; eassumption.
Qed.

(** Consuming a seeded row preserves reachability by adding precisely its outgoing dependencies. *)
Lemma scev_row_reachable_cons {V} (EV : encoding V) x deps rows seeds :
  FinSet.mem EV x seeds = true -> forall y,
  scev_row_reachable EV ((x, deps) :: rows) seeds y <->
  scev_row_reachable EV rows (FinSet.union EV seeds deps) y.
Proof.
  intros Hseed y; split; intro Hreachable.
  - induction Hreachable as [y Hmember|parent y Hparent IH Hlink].
    + apply ScevRowSeed; apply FinSet.mem_union; left; exact Hmember.
    + destruct Hlink as [found [[Heq|Hin] Hmember]].
      * inversion Heq; subst parent found; apply ScevRowSeed.
        apply FinSet.mem_union; right; exact Hmember.
      * eapply ScevRowStep; [exact IH|]; exists found; split; assumption.
  - induction Hreachable as [y Hmember|parent y Hparent IH Hlink].
    + apply FinSet.mem_union in Hmember; destruct Hmember as [Hold|Hdep].
      * apply ScevRowSeed; exact Hold.
      * eapply ScevRowStep; [apply ScevRowSeed; exact Hseed|].
        exists deps; split; [left; reflexivity|exact Hdep].
    + eapply ScevRowStep; [exact IH|].
      destruct Hlink as [found [Hin Hmember]]; exists found; split;
        [right; exact Hin|exact Hmember].
Qed.

(** Reverse dependency checking accepts exactly when every triangular row is target-reachable. *)
Theorem scev_check_dependencies_correct {V} (EV : encoding V) rows seeds :
  scev_rows_triangular EV rows ->
  scev_check_dependencies EV rows seeds = true <->
    forall x deps, In (x, deps) rows -> scev_row_reachable EV rows seeds x.
Proof.
  intro Htriangle; revert seeds.
  induction Htriangle as [|x deps rows Hfresh Hdeps Htriangle IH]; intro seeds.
  - cbn [scev_check_dependencies]; split; [intros _ x ds Hin; contradiction|intros _; reflexivity].
  - cbn [scev_check_dependencies]; destruct (FinSet.mem EV x seeds) eqn:Hseed.
    + rewrite IH; split.
      * intros Htail y ds [Heq|Hin].
        -- inversion Heq; subst y ds; apply ScevRowSeed; exact Hseed.
        -- apply (proj2 (scev_row_reachable_cons EV x deps rows seeds Hseed y)).
           apply Htail with (deps := ds); exact Hin.
      * intros Hall y ds Hin.
        apply (proj1 (scev_row_reachable_cons EV x deps rows seeds Hseed y)).
        apply Hall with (deps := ds); right; exact Hin.
    + split; [discriminate|intro Hall].
      specialize (Hall x deps (or_introl eq_refl)).
      pose proof (scev_rows_head_seed EV x deps rows seeds
        (ScevRowsCons EV x deps rows Hfresh Hdeps Htriangle) Hall) as Htrue; congruence.
Qed.

(** A dependency row records its source phi and exactly its expression's phi leaves. *)
Definition scev_binding_row {V} (EV : encoding V) (b : scev_binding V)
    (row : V * FinSet.t V) : Prop :=
  fst row = sb_phi b /\
    forall x, FinSet.mem EV x (snd row) = true <-> In x (scev_binding_phis b).

(** List validity states all source conditions at their actual increasing ranks. *)
Fixpoint scev_bindings_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (full : list (scev_binding V))
    (rank : nat) (bs : list (scev_binding V)) : Prop :=
  match bs with
  | [] => True
  | b :: rest => scev_binding_valid inventory lv so full rank b /\
      scev_bindings_valid inventory lv so full (Nat.succ rank) rest
  end.

(** Forward checking establishes all independent binding conditions and exact reverse rows. *)
Theorem scev_check_bindings_sound {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p bs :
  NoDup (map sb_phi (sp_bindings p)) -> forall rank checked out,
  scev_check_bindings EN EV lv so (scev_prepare_index EV inventory lv p) rank
    (scev_prepare_bindings EV bs) checked = Some out ->
  scev_bindings_valid inventory lv so (sp_bindings p) rank bs /\
    exists rows, Forall2 (scev_binding_row EV) bs rows /\ out = rev rows ++ checked.
Proof.
  intro Hdistinct; induction bs as [|b bs IH]; intros rank checked out Hrun.
  - cbn [scev_prepare_bindings scev_check_bindings] in Hrun; inversion Hrun; subst out.
    split; [exact I|]; exists []; split; [constructor|reflexivity].
  - cbn [scev_prepare_bindings map scev_check_bindings] in Hrun.
    destruct (scev_check_binding EN EV lv so (scev_prepare_index EV inventory lv p) rank b
      (option_map (scev_prepare_expr EV) (sb_other b))) as [deps|] eqn:Hbinding;
      [|discriminate].
    destruct (IH (Nat.succ rank) ((sb_phi b, deps) :: checked) out Hrun)
      as [Htail [rows [Hrows Hout]]].
    split.
    + split; [|exact Htail].
      apply (proj1 (scev_check_binding_correct EN EV inventory lv so p rank b Hdistinct)).
      exists deps; exact Hbinding.
    + exists ((sb_phi b, deps) :: rows); split.
      * constructor; [|exact Hrows]; split; [reflexivity|].
        eapply scev_check_binding_dependencies; exact Hbinding.
      * cbn [rev]; rewrite <- app_assoc; exact Hout.
Qed.

(** Every list satisfying the independent binding conditions is accepted by forward checking. *)
Theorem scev_check_bindings_complete {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p bs :
  NoDup (map sb_phi (sp_bindings p)) -> forall rank checked,
  scev_bindings_valid inventory lv so (sp_bindings p) rank bs ->
  exists out, scev_check_bindings EN EV lv so (scev_prepare_index EV inventory lv p) rank
    (scev_prepare_bindings EV bs) checked = Some out.
Proof.
  intro Hdistinct; induction bs as [|b bs IH]; intros rank checked Hvalid.
  - exists checked; reflexivity.
  - destruct Hvalid as [Hbinding Htail].
    destruct (proj2 (scev_check_binding_correct EN EV inventory lv so p rank b Hdistinct)
      Hbinding) as [deps Hchecked].
    cbn [scev_prepare_bindings map scev_check_bindings]; rewrite Hchecked.
    apply IH; exact Htail.
Qed.

(** Positionwise row correspondence preserves lengths and all phi positions. *)
Lemma scev_binding_rows_positions {V} (EV : encoding V) bs rows :
  Forall2 (scev_binding_row EV) bs rows ->
  length bs = length rows /\
    forall i b, nth_error bs i = Some b ->
      exists deps, nth_error rows i = Some (sb_phi b, deps) /\
        forall x, FinSet.mem EV x deps = true <-> In x (scev_binding_phis b).
Proof.
  intro Hrows; induction Hrows as [|b [x deps] bs rows Hrow Hrows IH].
  - split; [reflexivity|]; intros i b Hnth; destruct i; discriminate.
  - destruct Hrow as [Hphi Hdeps]; cbn [fst snd] in Hphi, Hdeps; subst x.
    destruct IH as [Hlength IH]; split; [cbn; congruence|].
    intros [|i] a Hnth; cbn [nth_error] in Hnth.
    + inversion Hnth; subst a; exists deps; split; [reflexivity|exact Hdeps].
    + destruct (IH i a Hnth) as [found [Hget Hfound]].
      exists found; split; [exact Hget|exact Hfound].
Qed.

(** Every checked row corresponds to a source binding at the same position. *)
Lemma scev_binding_rows_source {V} (EV : encoding V) bs rows :
  Forall2 (scev_binding_row EV) bs rows ->
  forall i x deps, nth_error rows i = Some (x, deps) ->
    exists b, nth_error bs i = Some b /\ sb_phi b = x /\
      forall y, FinSet.mem EV y deps = true <-> In y (scev_binding_phis b).
Proof.
  intro Hrows; induction Hrows as [|b [x deps] bs rows Hrow Hrows IH];
    intros [|i] y found Hnth; cbn [nth_error] in Hnth; try discriminate.
  - inversion Hnth; subst y found.
    exists b; split; [reflexivity|]; destruct Hrow as [Hphi Hdeps]; split;
      [symmetry; exact Hphi|exact Hdeps].
  - destruct (IH i y found Hnth) as [a [Ha [Hphi Hdeps]]].
    exists a; split; [exact Ha|]; split; assumption.
Qed.

(** Binding-list validity assigns the declared rank to every listed binding. *)
Lemma scev_bindings_valid_position {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) full bs :
  forall rank i b, scev_bindings_valid inventory lv so full rank bs ->
    nth_error bs i = Some b -> scev_binding_valid inventory lv so full (rank + i)%nat b.
Proof.
  induction bs as [|a bs IH]; intros rank [|i] b Hvalid Hnth;
    cbn [nth_error] in Hnth; try discriminate.
  - inversion Hnth; subst b; rewrite Nat.add_0_r; exact (proj1 Hvalid).
  - destruct Hvalid as [_ Htail].
    rewrite Nat.add_succ_r; exact (IH (Nat.succ rank) i b Htail Hnth).
Qed.

(** Every valid binding dependency is witnessed by a strictly lower source position. *)
Lemma scev_binding_earlier {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rank b :
  scev_binding_valid inventory lv so bs rank b ->
  forall x, In x (scev_binding_phis b) -> scev_earlier bs rank x.
Proof.
  intros [_ Hupdate]; destruct b as [phi base update kind other first];
    destruct kind; destruct other as [e|]; cbn [scev_update_valid sb_kind sb_other
      scev_binding_phis] in *; try contradiction.
  - intros x Hin; eapply scev_expression_earlier; [exact (proj2 Hupdate)|exact Hin].
  - intros x Hin; eapply scev_expression_earlier; [exact (proj2 Hupdate)|exact Hin].
Qed.

(** Phi identifiers in corresponding rows are exactly the source list's phi identifiers. *)
Lemma scev_binding_rows_phis {V} (EV : encoding V) bs rows :
  Forall2 (scev_binding_row EV) bs rows -> map fst rows = map sb_phi bs.
Proof.
  intro Hrows; induction Hrows as [|b row bs rows Hrow Hrows IH]; [reflexivity|].
  cbn [map]; rewrite (proj1 Hrow), IH; reflexivity.
Qed.

(** Source validity makes every dependency point to a strictly lower position in forward rows. *)
Theorem scev_binding_rows_lower {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rows :
  scev_bindings_valid inventory lv so bs 0 bs -> Forall2 (scev_binding_row EV) bs rows ->
  forall i x deps y, nth_error rows i = Some (x, deps) -> FinSet.mem EV y deps = true ->
    exists j found, nth_error rows j = Some (y, found) /\ (j < i)%nat.
Proof.
  intros Hvalid Hrows i x deps y Hrow Hmember.
  destruct (scev_binding_rows_source EV bs rows Hrows i x deps Hrow)
    as [b [Hnth [Hphi Hdeps]]].
  pose proof (scev_bindings_valid_position inventory lv so bs bs 0 i b Hvalid Hnth)
    as Hbinding.
  cbn [Nat.add] in Hbinding.
  apply Hdeps in Hmember.
  destruct (scev_binding_earlier inventory lv so bs i b Hbinding y Hmember)
    as [j [a [Ha [Haphi Hlt]]]].
  destruct (proj2 (scev_binding_rows_positions EV bs rows Hrows) j a Ha)
    as [found [Hfound _]].
  exists j, found; rewrite <- Haphi; split; assumption.
Qed.

(** A successful reversed-list lookup has the complementary original position. *)
Lemma scev_reverse_position {A} (xs : list A) i x : nth_error (rev xs) i = Some x ->
  exists j, nth_error xs j = Some x /\ (i + j + 1 = length xs)%nat.
Proof.
  rewrite nth_error_rev; destruct (i <? length xs)%nat eqn:Hlt; [|discriminate].
  apply Nat.ltb_lt in Hlt; intro Hnth; exists (length xs - S i)%nat; split; [exact Hnth|lia].
Qed.

(** Original positions can be read at their complementary reversed positions. *)
Lemma scev_reverse_lookup {A} (xs : list A) i x : nth_error xs i = Some x ->
  nth_error (rev xs) (length xs - S i) = Some x.
Proof.
  intro Hnth; assert (Hlt : (i < length xs)%nat).
  { apply nth_error_Some; rewrite Hnth; discriminate. }
  rewrite nth_error_rev.
  assert (Htest : (length xs - S i <? length xs)%nat = true) by (apply Nat.ltb_lt; lia).
  rewrite Htest; replace (length xs - S (length xs - S i))%nat with i by lia; exact Hnth.
Qed.

(** Strictly forward dependency positions imply the inductive triangular graph condition. *)
Lemma scev_rows_positions_triangular {V} (EV : encoding V) rows :
  NoDup (map fst rows) ->
  (forall i x deps y, nth_error rows i = Some (x, deps) -> FinSet.mem EV y deps = true ->
    exists j found, nth_error rows j = Some (y, found) /\ (i < j)%nat) ->
  scev_rows_triangular EV rows.
Proof.
  induction rows as [|[x deps] rows IH]; intros Hdistinct Hpositions; [constructor|].
  inversion Hdistinct as [|a xs Hfresh Htail]; subst; constructor; [exact Hfresh| |].
  - intros y Hmember.
    destruct (Hpositions 0%nat x deps y eq_refl Hmember) as [j [found [Hnth Hlt]]].
    destruct j as [|j]; [lia|]; cbn [nth_error] in Hnth.
    apply in_map_iff; exists (y, found); split; [reflexivity|].
    eapply nth_error_In; exact Hnth.
  - apply IH; [exact Htail|].
    intros i a found y Hnth Hmember.
    destruct (Hpositions (S i) a found y Hnth Hmember) as [j [target [Htarget Hlt]]].
    destruct j as [|j]; [lia|]; exists j, target; split; [exact Htarget|lia].
Qed.

(** Reversing distinct rows with lower dependencies yields a triangular dependency graph. *)
Theorem scev_rows_reverse_triangular {V} (EV : encoding V) rows :
  NoDup (map fst rows) ->
  (forall i x deps y, nth_error rows i = Some (x, deps) -> FinSet.mem EV y deps = true ->
    exists j found, nth_error rows j = Some (y, found) /\ (j < i)%nat) ->
  scev_rows_triangular EV (rev rows).
Proof.
  intros Hdistinct Hlower; apply scev_rows_positions_triangular.
  - rewrite map_rev; apply NoDup_rev; exact Hdistinct.
  - intros i x deps y Hnth Hmember.
    destruct (scev_reverse_position rows i (x, deps) Hnth) as [j [Hsource Hsum]].
    destruct (Hlower j x deps y Hsource Hmember) as [k [found [Htarget Hlt]]].
    assert (Hk : (k < length rows)%nat).
    { apply nth_error_Some; rewrite Htarget; discriminate. }
    exists (length rows - S k)%nat, found; split.
    + apply scev_reverse_lookup; exact Htarget.
    + lia.
Qed.

(** Checked binding rows form the finite triangular graph expected by reverse reachability. *)
Theorem scev_binding_rows_triangular {S O N E V K C} (EV : encoding V) inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rows :
  NoDup (map sb_phi bs) -> scev_bindings_valid inventory lv so bs 0 bs ->
  Forall2 (scev_binding_row EV) bs rows -> scev_rows_triangular EV (rev rows).
Proof.
  intros Hdistinct Hvalid Hrows; apply scev_rows_reverse_triangular.
  - rewrite (scev_binding_rows_phis EV bs rows Hrows); exact Hdistinct.
  - eapply scev_binding_rows_lower; eassumption.
Qed.

(** A source plan edge names an actual binding and one of its declared phi leaves. *)
Definition scev_plan_edge {V} (bs : list (scev_binding V)) x y : Prop :=
  exists b, In b bs /\ sb_phi b = x /\ In y (scev_binding_phis b).

(** A source phi is reachable through zero or more declarative plan dependency edges. *)
Inductive scev_plan_reachable {V} (bs : list (scev_binding V)) (target : V) : V -> Prop :=
  | ScevPlanRoot : scev_plan_reachable bs target target
  | ScevPlanStep : forall x y,
      scev_plan_reachable bs target x -> scev_plan_edge bs x y ->
      scev_plan_reachable bs target y.

(** Row correspondence identifies source and indexed dependency edges exactly. *)
Lemma scev_binding_rows_edges {V} (EV : encoding V) bs rows :
  Forall2 (scev_binding_row EV) bs rows -> forall x y,
    scev_row_edge EV (rev rows) x y <-> scev_plan_edge bs x y.
Proof.
  intro Hrows; induction Hrows as [|b [phi deps] bs rows Hrow Hrows IH]; intros x y.
  - split; [intros [found [Hin Hmember]]; contradiction|intros [a [Hin _]]; contradiction].
  - destruct Hrow as [Hphi Hdeps]; cbn [fst snd] in Hphi, Hdeps; subst phi.
    unfold scev_row_edge; cbn [rev]; split.
    + intros [found [Hin Hmember]]; apply in_app_iff in Hin.
      destruct Hin as [Hin|[Heq|Hbad]]; [| |contradiction].
      * pose proof (proj1 (IH x y) (ex_intro _ found (conj Hin Hmember))) as Hedge.
        destruct Hedge as [a [Ha [Howner Hleaf]]].
        exists a; split; [right; exact Ha|split; assumption].
      * inversion Heq; subst x found; exists b; split; [left; reflexivity|].
        split; [reflexivity|apply Hdeps; exact Hmember].
    + intros [a [[Heq|Hin] [Howner Hleaf]]].
      * subst a; subst x; exists deps; split; [apply in_app_iff; right; left; reflexivity|].
        apply Hdeps; exact Hleaf.
      * assert (Hedge : scev_plan_edge bs x y).
        { exists a; split; [exact Hin|split; assumption]. }
        apply IH in Hedge; destruct Hedge as [found [Hfound Hmember]].
        exists found; split; [apply in_app_iff; left; exact Hfound|exact Hmember].
Qed.

(** Row reachability agrees with declarative target reachability for corresponding binding rows. *)
Theorem scev_binding_rows_reachable {V} (EV : encoding V) bs rows target :
  Forall2 (scev_binding_row EV) bs rows -> forall x,
    scev_row_reachable EV (rev rows) (FinSet.add EV target FinSet.empty) x <->
    scev_plan_reachable bs target x.
Proof.
  intros Hrows x; split; intro Hreachable.
  - induction Hreachable as [x Hseed|parent x Hparent IH Hedge].
    + apply FinSet.mem_add in Hseed; destruct Hseed as [Heq|Hbad].
      * subst x; constructor.
      * rewrite FinSet.mem_empty in Hbad; discriminate.
    + eapply ScevPlanStep; [exact IH|].
      apply (proj1 (scev_binding_rows_edges EV bs rows Hrows parent x)); exact Hedge.
  - induction Hreachable as [|parent x Hparent IH Hedge].
    + apply ScevRowSeed; apply FinSet.mem_add; left; reflexivity.
    + eapply ScevRowStep; [exact IH|].
      apply (proj2 (scev_binding_rows_edges EV bs rows Hrows parent x)); exact Hedge.
Qed.

(** The prepared final-phi field is absent exactly for the empty binding list. *)
Lemma scev_rank_index_final_none {V} (EV : encoding V) bs start :
  sri_final (scev_rank_index_from EV start bs) = None <-> bs = [].
Proof.
  destruct bs as [|b bs]; [split; reflexivity|].
  cbn [scev_rank_index_from sri_final].
  destruct (sri_final (scev_rank_index_from EV (S start) bs));
    split; discriminate.
Qed.

(** The prepared final phi names exactly the last binding of a nonempty source list. *)
Theorem scev_rank_index_final {V} (EV : encoding V) bs : forall start target,
  sri_final (scev_rank_index_from EV start bs) = Some target <->
    exists prefix b, bs = prefix ++ [b] /\ sb_phi b = target.
Proof.
  induction bs as [|b bs IH]; intros start target.
  - split; [discriminate|intros [prefix [a [Heq Hphi]]]].
    symmetry in Heq; apply app_eq_nil in Heq; destruct Heq as [_ Hbad]; discriminate.
  - destruct bs as [|a bs].
    + cbn [scev_rank_index_from sri_final]; split.
      * intro Heq; inversion Heq; exists [], b; split; reflexivity.
      * intros [prefix [last [Heq Hphi]]].
        destruct prefix as [|p prefix].
        -- inversion Heq; subst last; rewrite Hphi; reflexivity.
        -- cbn in Heq; inversion Heq as [[Hhead Htail]].
           symmetry in Htail; apply app_eq_nil in Htail; destruct Htail as [_ Hbad]; discriminate.
    + assert (Hnonempty : a :: bs <> []) by discriminate.
      change ((match sri_final (scev_rank_index_from EV (S start) (a :: bs)) with
        | Some x => Some x
        | None => Some (sb_phi b)
        end) = Some target <->
        exists prefix last, b :: a :: bs = prefix ++ [last] /\ sb_phi last = target).
      destruct (sri_final (scev_rank_index_from EV (S start) (a :: bs)))
        as [last_phi|] eqn:Htail.
      * split.
        -- intro Heq; inversion Heq; subst last_phi.
           apply IH in Htail; destruct Htail as [prefix [last [Hlist Hphi]]].
           exists (b :: prefix), last; split; [cbn; rewrite Hlist; reflexivity|exact Hphi].
        -- intros [prefix [last [Hlist Hphi]]].
           destruct prefix as [|p prefix]; [cbn in Hlist; discriminate|].
           cbn in Hlist; inversion Hlist as [[Hhead Hrest]].
           assert (Hlast : sri_final (scev_rank_index_from EV (S start) (a :: bs)) =
             Some target).
           { apply IH; exists prefix, last; split; assumption. }
           congruence.
      * apply scev_rank_index_final_none in Htail; contradiction.
Qed.

(** Source reachability of every binding equals indexed reachability of every matching row. *)
Lemma scev_binding_rows_all_reachable {V} (EV : encoding V) bs rows target :
  Forall2 (scev_binding_row EV) bs rows ->
  (forall x deps, In (x, deps) (rev rows) ->
    scev_row_reachable EV (rev rows) (FinSet.add EV target FinSet.empty) x) <->
  (forall b, In b bs -> scev_plan_reachable bs target (sb_phi b)).
Proof.
  intro Hrows; split.
  - intros Hall b Hin.
    assert (Hphi : In (sb_phi b) (map fst (rev rows))).
    { rewrite map_rev; apply (proj1 (in_rev (map fst rows) (sb_phi b))).
      rewrite (scev_binding_rows_phis EV bs rows Hrows).
      apply in_map; exact Hin. }
    apply in_map_iff in Hphi; destruct Hphi as [[x deps] [Hphi Hmember]].
    cbn [fst] in Hphi; subst x.
    apply (proj1 (scev_binding_rows_reachable EV bs rows target Hrows (sb_phi b))).
    apply Hall with (deps := deps); exact Hmember.
  - intros Hall x deps Hin.
    assert (Hphi : In x (map sb_phi bs)).
    { rewrite <- (scev_binding_rows_phis EV bs rows Hrows).
      apply (proj2 (in_rev (map fst rows) x)); rewrite <- map_rev.
      apply in_map_iff; exists (x, deps); split; [reflexivity|exact Hin]. }
    apply in_map_iff in Hphi; destruct Hphi as [b [Hphi Hmember]].
    apply (proj2 (scev_binding_rows_reachable EV bs rows target Hrows x)).
    rewrite <- Hphi; apply Hall; exact Hmember.
Qed.

(** The independent plan contract fixes inventory, ranked source shape and target reachability. *)
Record scev_plan_valid {S O N E V K C} (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (p : scev_plan V) : Prop := {
  spv_target_inventory : In (sp_target p) inventory;
  spv_distinct : NoDup (map sb_phi (sp_bindings p));
  spv_last : exists prefix b, sp_bindings p = prefix ++ [b] /\ sb_phi b = sp_target p;
  spv_bindings : scev_bindings_valid inventory lv so (sp_bindings p) 0 (sp_bindings p);
  spv_reachable : forall b, In b (sp_bindings p) ->
    scev_plan_reachable (sp_bindings p) (sp_target p) (sb_phi b)
}.

(** Acceptance establishes precisely the independent source-plan conditions. *)
Theorem scev_plan_check_sound {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p :
  scev_plan_check EN EV inventory lv so p = true -> scev_plan_valid inventory lv so p.
Proof.
  unfold scev_plan_check, scev_plan_check_index.
  destruct (Map.mem EV (sp_target p) (ssi_values (scev_prepare_index EV inventory lv p)) &&
    sri_distinct (ssi_phi (scev_prepare_index EV inventory lv p))) eqn:Hglobal;
    [|discriminate].
  apply Bool.andb_true_iff in Hglobal; destruct Hglobal as [Hinventory Hdistinct].
  apply scev_inventory_index_mem in Hinventory.
  apply scev_rank_index_distinct in Hdistinct.
  destruct (sri_final (ssi_phi (scev_prepare_index EV inventory lv p))) as [target|]
    eqn:Hfinal; [|discriminate].
  destruct (scev_key_eq EV target (sp_target p)) eqn:Htarget; [|discriminate].
  apply scev_key_eq_spec in Htarget; subst target.
  destruct (scev_check_bindings EN EV lv so (scev_prepare_index EV inventory lv p) 0
    (scev_prepare_bindings EV (sp_bindings p)) []) as [checked|] eqn:Hbindings;
    [|discriminate].
  intro Hdependencies.
  destruct (scev_check_bindings_sound EN EV inventory lv so p (sp_bindings p) Hdistinct
    0 [] checked Hbindings) as [Hvalid [rows [Hrows Hchecked]]].
  rewrite app_nil_r in Hchecked; subst checked.
  constructor; try assumption.
  - apply (proj1 (scev_rank_index_final EV (sp_bindings p) 0 (sp_target p))); exact Hfinal.
  - apply (proj1 (scev_binding_rows_all_reachable EV (sp_bindings p) rows (sp_target p) Hrows)).
    apply (proj1 (scev_check_dependencies_correct EV (rev rows)
      (FinSet.add EV (sp_target p) FinSet.empty)
      (scev_binding_rows_triangular EV inventory lv so (sp_bindings p) rows
        Hdistinct Hvalid Hrows))); exact Hdependencies.
Qed.

(** Every plan satisfying exactly the independent source conditions is accepted. *)
Theorem scev_plan_check_complete {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p :
  scev_plan_valid inventory lv so p -> scev_plan_check EN EV inventory lv so p = true.
Proof.
  intros [Hinventory Hdistinct Hlast Hvalid Hreachable].
  assert (Hmember : Map.mem EV (sp_target p)
    (ssi_values (scev_prepare_index EV inventory lv p)) = true).
  { apply scev_inventory_index_mem; exact Hinventory. }
  assert (Hunique : sri_distinct (ssi_phi (scev_prepare_index EV inventory lv p)) = true).
  { apply scev_rank_index_distinct; exact Hdistinct. }
  assert (Hfinal : sri_final (ssi_phi (scev_prepare_index EV inventory lv p)) =
    Some (sp_target p)).
  { apply scev_rank_index_final; exact Hlast. }
  assert (Htarget : scev_key_eq EV (sp_target p) (sp_target p) = true).
  { apply scev_key_eq_spec; reflexivity. }
  unfold scev_plan_check, scev_plan_check_index; rewrite Hmember, Hunique, Hfinal, Htarget.
  destruct (scev_check_bindings_complete EN EV inventory lv so p (sp_bindings p) Hdistinct
    0 [] Hvalid) as [checked Hchecked].
  rewrite Hchecked.
  destruct (scev_check_bindings_sound EN EV inventory lv so p (sp_bindings p) Hdistinct
    0 [] checked Hchecked) as [_ [rows [Hrows Hout]]].
  rewrite app_nil_r in Hout; subst checked.
  apply (proj2 (scev_check_dependencies_correct EV (rev rows)
    (FinSet.add EV (sp_target p) FinSet.empty)
    (scev_binding_rows_triangular EV inventory lv so (sp_bindings p) rows
      Hdistinct Hvalid Hrows))).
  apply (proj2 (scev_binding_rows_all_reachable EV (sp_bindings p) rows (sp_target p) Hrows));
    exact Hreachable.
Qed.

(** The indexed plan checker decides all four declarative syntactic conditions exactly. *)
Theorem scev_plan_check_correct {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p :
  scev_plan_check EN EV inventory lv so p = true <-> scev_plan_valid inventory lv so p.
Proof.
  split; [apply scev_plan_check_sound|apply scev_plan_check_complete].
Qed.

(** The integrated checker decides the same four source conditions after structural ingestion. *)
Theorem scev_shared_plan_check_correct {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) bs target :
  fst (scev_check_shared_plan EN EV lv so
    (scev_prepare_index EV inventory lv (ScevPlan (map spb_source bs) target)) bs target) = true
  <-> scev_plan_valid inventory lv so (ScevPlan (map spb_source bs) target).
Proof.
  rewrite scev_check_shared_plan_agrees.
  exact (scev_plan_check_correct EN EV inventory lv so (ScevPlan (map spb_source bs) target)).
Qed.

(** * Constructive same-stay transport *)

(** An invariant expression depends only on its explicitly listed variable leaves. *)
Lemma eval_iexpr_variables_agree {V} (left right : V -> Z) e :
  (forall x, In x (iexpr_variables e) -> left x = right x) ->
  eval_iexpr left e = eval_iexpr right e.
Proof.
  induction e as [x|z|z|a IHa b IHb|a IHa b IHb]; intro Hagree; cbn [eval_iexpr].
  - apply Hagree; left; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb; [reflexivity| |]; intros x Hin; apply Hagree;
      cbn [iexpr_variables]; apply in_app_iff; [right|left]; exact Hin.
  - rewrite IHa, IHb; [reflexivity| |]; intros x Hin; apply Hagree;
      cbn [iexpr_variables]; apply in_app_iff; [right|left]; exact Hin.
Qed.

(** Pointwise invariant-environment agreement preserves every recurrence at every index. *)
Lemma eval_chrec_environment_agrees {V} (left right : V -> Z) c :
  (forall x, left x = right x) -> forall k, eval_chrec left c k = eval_chrec right c k.
Proof.
  intro Hagree; induction c as [e|b IHb s IHs|b IHb r IHr|a IHa b IHb|a IHa b IHb]; intro k.
  - apply eval_iexpr_variables_agree; intros x _; apply Hagree.
  - induction k as [|k IHk]; [apply IHb|].
    change ((eval_chrec left (CRec b s) k + eval_chrec left s k)%Z =
      (eval_chrec right (CRec b s) k + eval_chrec right s k)%Z).
    rewrite IHk, IHs; reflexivity.
  - induction k as [|k IHk]; [apply IHb|].
    change ((eval_chrec left (CGeo b r) k * eval_chrec left r k)%Z =
      (eval_chrec right (CGeo b r) k * eval_chrec right r k)%Z).
    rewrite IHk, IHr; reflexivity.
  - cbn [eval_chrec]; rewrite IHa, IHb; reflexivity.
  - cbn [eval_chrec]; rewrite IHa, IHb; reflexivity.
Qed.

(** Distinct outside and inside homes let the positive SSA frames preserve exact option values. *)
Theorem scev_body_step_outside_frame {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s tr t y,
  reachable_state m s -> step m s tr t ->
  lbody lv (point (base (lssa lv)) s) = true ->
  lbody lv (point (base (lssa lv)) t) = true ->
  lbody lv (home (lssa lv) y) = false -> val (lssa lv) t y = val (lssa lv) s y.
Proof.
  intros Hloop s tr t y Hreachable Hstep Hinside Hinside' Houtside.
  destruct (edge_covers (base_laws (l_ssa m EN EV inventory so lv Hloop)) s tr t Hreachable Hstep)
    as [Hstay|[e Htaken]].
  - apply (frame_in_stay (l_strict m EN EV inventory so lv Hloop) s tr t y
      Hreachable Hstep Hstay); intro Heq; rewrite Heq in Hinside; congruence.
  - apply (frame_on_edge (l_strict m EN EV inventory so lv Hloop) s tr t e y
      Hreachable Hstep Htaken); intro Heq; rewrite <- Heq in Hinside'; congruence.
Qed.

(** Restricted body runs preserve exact outside-home option values from their own source state. *)
Theorem scev_body_run_outside_frame {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s tr t,
  reachable_state m s ->
  exec_in m (fun u => lbody lv (point (base (lssa lv)) u) = true) s tr t ->
  forall y, lbody lv (home (lssa lv) y) = false ->
    val (lssa lv) t y = val (lssa lv) s y.
Proof.
  intros Hloop s tr t Hreachable Hrun; revert Hreachable.
  induction Hrun as [s Hinside|s tr u rest t Hinside Hstep Hrun IH];
    intros Hreachable y Houtside; [reflexivity|].
  rewrite (IH (reachable_state_step m s tr u Hreachable Hstep) y Houtside).
  apply (scev_body_step_outside_frame m EN EV inventory so lv Hloop s tr u y);
    try assumption.
  inversion Hrun; assumption.
Qed.

(** Every bound expression is stable along the actual body run of the same stay. *)
Theorem scev_body_run_bound_frame {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s tr t tst,
  reachable_state m s ->
  exec_in m (fun u => lbody lv (point (base (lssa lv)) u) = true) s tr t ->
  ltest lv = Some tst ->
  eval_iexpr (inv_env lv so t) (t_bound tst) = eval_iexpr (inv_env lv so s) (t_bound tst).
Proof.
  intros Hloop s tr t tst Hreachable Hrun Htest.
  apply eval_iexpr_variables_agree; intros y Hin; unfold inv_env.
  rewrite (scev_body_run_outside_frame m EN EV inventory so lv Hloop s tr t
    Hreachable Hrun y); [reflexivity|].
  eapply (l_test_outside m EN EV inventory so lv Hloop); eassumption.
Qed.

(** Header parameters retain their exact option values during a semantic stay at any point. *)
Theorem scev_phi_stay_frame {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s tr t x i,
  reachable_state m s -> step m s tr t -> stays (base (lssa lv)) s tr t ->
  def (lssa lv) x = Param (lheader lv) i -> home (lssa lv) x = lheader lv ->
  val (lssa lv) t x = val (lssa lv) s x.
Proof.
  intros Hloop s tr t x i Hreachable Hstep Hstay Hdef Hhome.
  destruct (scev_key_eq EN (point (base (lssa lv)) s) (lheader lv)) eqn:Hpoint.
  - apply scev_key_eq_spec in Hpoint.
    eapply (l_phi_stay m EN EV inventory so lv Hloop); eassumption.
  - apply (frame_in_stay (l_strict m EN EV inventory so lv Hloop) s tr t x
      Hreachable Hstep Hstay); intro Heq.
    rewrite Hhome in Heq; apply (proj2 (scev_key_eq_spec EN _ _)) in Heq; congruence.
Qed.

(** A path with no new header edge preserves every header parameter, including header stays. *)
Theorem scev_phi_run_frame {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s es t x i,
  reachable_state m s -> run_edges m (base (lssa lv)) s es t ->
  Forall (fun e => Graph.target (cfg (base (lssa lv))) e <> lheader lv) es ->
  def (lssa lv) x = Param (lheader lv) i -> home (lssa lv) x = lheader lv ->
  val (lssa lv) t x = val (lssa lv) s x.
Proof.
  intros Hloop s es t x i Hreachable Hrun; revert Hreachable.
  induction Hrun as [s|s tr u e es t Hstep Htaken Hrun IH|
    s tr u es t Hstep Hstay Hrun IH]; intros Hreachable Hedges Hdef Hhome; [reflexivity| |].
  - inversion Hedges as [|a rest Htarget Htail]; subst.
    rewrite (IH (reachable_state_step m s tr u Hreachable Hstep) Htail Hdef Hhome).
    apply (frame_on_edge (l_strict m EN EV inventory so lv Hloop) s tr u e x
      Hreachable Hstep Htaken).
    destruct (taken_edge (base_laws (l_ssa m EN EV inventory so lv Hloop)) s tr u e
      Hreachable Hstep Htaken) as [_ Hpoint].
    rewrite Hhome, <- Hpoint; congruence.
  - rewrite (IH (reachable_state_step m s tr u Hreachable Hstep) Hedges Hdef Hhome).
    eapply scev_phi_stay_frame; eassumption.
Qed.

(** Edge-history invariants can be established by actual semantic steps in execution order. *)
Lemma scev_run_edges_invariant {S O N E} (m : semantics S O) (gv : graph_view S O N E)
    (P : S -> list E -> Prop) :
  (forall s tr t e prefix, reachable_state m s -> P s prefix -> step m s tr t ->
    taken gv s tr t e -> P t (prefix ++ [e])) ->
  (forall s tr t prefix, reachable_state m s -> P s prefix -> step m s tr t ->
    stays gv s tr t -> P t prefix) ->
  forall s es t, run_edges m gv s es t -> forall prefix,
    reachable_state m s -> P s prefix -> P t (prefix ++ es).
Proof.
  intros Hedge Hstay s es t Hrun.
  induction Hrun as [s|s tr u e es t Hstep Htaken Hrun IH|
    s tr u es t Hstep Hstays Hrun IH]; intros prefix Hreachable HP.
  - rewrite app_nil_r; exact HP.
  - replace (prefix ++ e :: es) with ((prefix ++ [e]) ++ es) by
      (rewrite <- app_assoc; reflexivity).
    apply IH; [eapply reachable_state_step; eassumption|].
    eapply Hedge; eassumption.
  - apply IH; [eapply reachable_state_step; eassumption|].
    eapply Hstay; eassumption.
Qed.

(** A history records the actual most recent header arrival and its uninterrupted body suffix. *)
Definition scev_header_history {S O N E V K C} (m : semantics S O)
    (lv : loop_view S O N E V K C) (s0 : S) (es : list E) (s : S) : Prop :=
  exists before h after tr,
    es = before ++ after /\ run_edges m (base (lssa lv)) s0 before h /\
    point (base (lssa lv)) h = lheader lv /\
    run_edges m (base (lssa lv)) h after s /\
    Forall (fun e => Graph.target (cfg (base (lssa lv))) e <> lheader lv) after /\
    exec_in m (fun u => lbody lv (point (base (lssa lv)) u) = true) h tr s.

(** A new header edge provides a fresh concrete history with an empty body suffix. *)
Lemma scev_header_history_arrive {S O N E V K C} (m : semantics S O)
    (lv : loop_view S O N E V K C) s0 prefix s tr t e :
  run_edges m (base (lssa lv)) s0 prefix s -> step m s tr t ->
  taken (base (lssa lv)) s tr t e -> point (base (lssa lv)) t = lheader lv ->
  lbody lv (lheader lv) = true -> scev_header_history m lv s0 (prefix ++ [e]) t.
Proof.
  intros Hprefix Hstep Htaken Hheader Hinside.
  exists (prefix ++ [e]), t, [], []; split; [rewrite app_nil_r; reflexivity|].
  split.
  - eapply run_edges_app; [exact Hprefix|].
    eapply run_cons; [exact Hstep|exact Htaken|constructor].
  - split; [exact Hheader|]; split; [constructor|]; split; [constructor|].
    constructor; rewrite Hheader; exact Hinside.
Qed.

(** A body edge avoiding the header extends the same witnessed stay and its same-source suffix. *)
Lemma scev_header_history_edge {S O N E V K C} (m : semantics S O)
    (lv : loop_view S O N E V K C) s0 prefix s tr t e :
  scev_header_history m lv s0 prefix s -> step m s tr t ->
  taken (base (lssa lv)) s tr t e ->
  Graph.target (cfg (base (lssa lv))) e <> lheader lv ->
  lbody lv (point (base (lssa lv)) s) = true ->
  lbody lv (point (base (lssa lv)) t) = true ->
  scev_header_history m lv s0 (prefix ++ [e]) t.
Proof.
  intros [before [h [after [events [Hprefix [Hbefore [Hheader [Hafter [Hedges Hbody]]]]]]]]]
    Hstep Htaken Htarget Hinside Hinside'.
  exists before, h, (after ++ [e]), (events ++ tr).
  split; [rewrite Hprefix, app_assoc; reflexivity|].
  split; [exact Hbefore|]; split; [exact Hheader|]; split.
  - eapply run_edges_app; [exact Hafter|].
    eapply run_cons; [exact Hstep|exact Htaken|constructor].
  - split.
    + apply Forall_app; split; [exact Hedges|constructor; [exact Htarget|constructor]].
    + eapply exec_in_app; [exact Hbody|].
      replace tr with (tr ++ []) at 1 by apply app_nil_r.
      eapply exec_in_step; [exact Hinside|exact Hstep|constructor; exact Hinside'].
Qed.

(** Instruction stays extend the same witnessed stay without inventing a header edge. *)
Lemma scev_header_history_stay {S O N E V K C} (m : semantics S O)
    (lv : loop_view S O N E V K C) s0 prefix s tr t :
  scev_header_history m lv s0 prefix s -> step m s tr t ->
  stays (base (lssa lv)) s tr t ->
  lbody lv (point (base (lssa lv)) s) = true ->
  lbody lv (point (base (lssa lv)) t) = true -> scev_header_history m lv s0 prefix t.
Proof.
  intros [before [h [after [events [Hprefix [Hbefore [Hheader [Hafter [Hedges Hbody]]]]]]]]]
    Hstep Hstay Hinside Hinside'.
  exists before, h, after, (events ++ tr).
  split; [exact Hprefix|]; split; [exact Hbefore|]; split; [exact Hheader|]; split.
  - rewrite <- (app_nil_r after); eapply run_edges_app; [exact Hafter|].
    eapply run_stay; [exact Hstep|exact Hstay|constructor].
  - split; [exact Hedges|]; eapply exec_in_app; [exact Hbody|].
    replace tr with (tr ++ []) at 1 by apply app_nil_r.
    eapply exec_in_step; [exact Hinside|exact Hstep|constructor; exact Hinside'].
Qed.

(** Every reachable body state has a previous-header history in the same uninterrupted stay. *)
Theorem scev_same_stay_history {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s0 es s,
  initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
  lbody lv (point (base (lssa lv)) s) = true -> scev_header_history m lv s0 es s.
Proof.
  intros Hloop s0 es s Hinitial Hrun.
  assert (Hview := base_laws (l_ssa m EN EV inventory so lv Hloop)).
  assert (Hproperty :
    (fun u prefix => run_edges m (base (lssa lv)) s0 prefix u /\
      (lbody lv (point (base (lssa lv)) u) = true ->
        scev_header_history m lv s0 prefix u)) s es).
  { change ((fun u prefix => run_edges m (base (lssa lv)) s0 prefix u /\
      (lbody lv (point (base (lssa lv)) u) = true ->
        scev_header_history m lv s0 prefix u)) s ([] ++ es)).
    eapply scev_run_edges_invariant; [| |exact Hrun| |].
    - intros u tr t e prefix Hreachable [Hprefix Hhistory] Hstep Htaken; split.
      + eapply run_edges_app; [exact Hprefix|].
        eapply run_cons; [exact Hstep|exact Htaken|constructor].
      + intro Hinside'.
        destruct (view_taken_edge m (base (lssa lv)) u tr t e Hview Hreachable Hstep Htaken)
          as [Hlisted [Hsource Htarget]].
        destruct (scev_key_eq EN (point (base (lssa lv)) t) (lheader lv)) eqn:Hheader.
        * apply scev_key_eq_spec in Hheader.
          exact (scev_header_history_arrive m lv s0 prefix u tr t e Hprefix Hstep Htaken
            Hheader (l_header_inside m EN EV inventory so lv Hloop)).
        * assert (Hnotheader : Graph.target (cfg (base (lssa lv))) e <> lheader lv).
          { intro Heq; rewrite Htarget in Heq.
            pose proof (proj2 (scev_key_eq_spec EN _ _) Heq); congruence. }
          assert (Hinside : lbody lv (point (base (lssa lv)) u) = true).
          { destruct (lbody lv (point (base (lssa lv)) u)) eqn:Hbody; [reflexivity|].
            assert (Hentry : e = lentry lv).
            { eapply (l_single_ingress m EN EV inventory so lv Hloop); [exact Hlisted| |].
              - rewrite Hsource; exact Hbody.
              - rewrite Htarget; exact Hinside'. }
            destruct (l_entry_edge m EN EV inventory so lv Hloop) as [_ [Hentry_target _]].
            subst e; contradiction. }
          eapply scev_header_history_edge; [apply Hhistory; exact Hinside|exact Hstep|
            exact Htaken|exact Hnotheader|exact Hinside|exact Hinside'].
    - intros u tr t prefix Hreachable [Hprefix Hhistory] Hstep Hstay; split.
      + rewrite <- (app_nil_r prefix); eapply run_edges_app; [exact Hprefix|].
        eapply run_stay; [exact Hstep|exact Hstay|constructor].
      + intro Hinside'.
        assert (Hinside : lbody lv (point (base (lssa lv)) u) = true).
        { rewrite <- (stays_point Hview u tr t Hreachable Hstep Hstay); exact Hinside'. }
        eapply scev_header_history_stay; [apply Hhistory; exact Hinside|exact Hstep|
          exact Hstay|exact Hinside|exact Hinside'].
    - exists s0, []; split; [exact Hinitial|constructor].
    - split; [constructor|]; intro Hinside.
      pose proof (entry_points Hview s0 Hinitial) as Hentry.
      pose proof (l_initial_outside m EN EV inventory so lv Hloop _ Hentry); congruence. }
  exact (proj2 Hproperty).
Qed.

(** The designated entry and back edges differ because their source body observations differ. *)
Lemma scev_entry_back_distinct {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> lentry lv <> lback lv.
Proof.
  intro Hloop; destruct (l_entry_edge m EN EV inventory so lv Hloop) as [_ [_ Hentry]].
  destruct (l_back_edge m EN EV inventory so lv Hloop) as [_ [_ Hback]].
  intro Heq; rewrite Heq in Hentry; congruence.
Qed.

(** Appending the actual entry edge resets the stay's arrival count. *)
Lemma scev_arrivals_entry {S O N E V K C} (EE : encoding E)
    (lv : loop_view S O N E V K C) es : stay_arrivals EE lv (es ++ [lentry lv]) = 0%nat.
Proof.
  unfold stay_arrivals; rewrite arrivals_since_snoc, Pos.eqb_refl; reflexivity.
Qed.

(** Appending the actual back edge advances the same stay's arrival count exactly once. *)
Lemma scev_arrivals_back {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) es :
  loop_view_laws m EN EV inventory so lv ->
  stay_arrivals EE lv (es ++ [lback lv]) = Nat.succ (stay_arrivals EE lv es).
Proof.
  intro Hloop; unfold stay_arrivals; rewrite arrivals_since_snoc, Pos.eqb_refl.
  destruct (Pos.eqb (encode EE (lback lv)) (encode EE (lentry lv))) eqn:Heq;
    [|reflexivity].
  apply Pos.eqb_eq in Heq; apply (encode_injective EE) in Heq.
  exfalso; apply (scev_entry_back_distinct m EN EV inventory so lv Hloop); symmetry; exact Heq.
Qed.

(** A suffix without a header edge changes neither the current stay nor its arrival index. *)
Theorem scev_arrivals_header_suffix {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) before after :
  loop_view_laws m EN EV inventory so lv ->
  Forall (fun e => Graph.target (cfg (base (lssa lv))) e <> lheader lv) after ->
  stay_arrivals EE lv (before ++ after) = stay_arrivals EE lv before.
Proof.
  intros Hloop Hafter; unfold stay_arrivals, arrivals_since; rewrite fold_left_app.
  generalize (fold_left (fun n e =>
    if Pos.eqb (encode EE e) (encode EE (lentry lv)) then 0%nat
    else if Pos.eqb (encode EE e) (encode EE (lback lv)) then Nat.succ n else n) before 0%nat).
  induction Hafter as [|e rest Htarget Hrest IH]; intro count; [reflexivity|].
  cbn [fold_left].
  assert (Hentry : Pos.eqb (encode EE e) (encode EE (lentry lv)) = false).
  { destruct (Pos.eqb (encode EE e) (encode EE (lentry lv))) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; apply (encode_injective EE) in Heq; subst e.
    destruct (l_entry_edge m EN EV inventory so lv Hloop) as [_ [Hentry _]]; contradiction. }
  assert (Hback : Pos.eqb (encode EE e) (encode EE (lback lv)) = false).
  { destruct (Pos.eqb (encode EE e) (encode EE (lback lv))) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; apply (encode_injective EE) in Heq; subst e.
    destruct (l_back_edge m EN EV inventory so lv Hloop) as [_ [Hback _]]; contradiction. }
  rewrite Hentry, Hback; exact (IH count).
Qed.

(** Actual back-source test evidence transports to the same witnessed preceding header state. *)
Theorem scev_previous_header_guard {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall h after events s tr t tst i,
  reachable_state m h -> run_edges m (base (lssa lv)) h after s ->
  Forall (fun e => Graph.target (cfg (base (lssa lv))) e <> lheader lv) after ->
  exec_in m (fun u => lbody lv (point (base (lssa lv)) u) = true) h events s ->
  step m s tr t -> taken (base (lssa lv)) s tr t (lback lv) -> ltest lv = Some tst ->
  def (lssa lv) (t_lhs tst) = Param (lheader lv) i ->
  home (lssa lv) (t_lhs tst) = lheader lv ->
  exists c, val (lssa lv) h (t_lhs tst) = Some c /\
    test_holds (width_of so) (t_sign tst) (t_cmp tst) (to_Z so c)
      (eval_iexpr (inv_env lv so h) (t_bound tst)).
Proof.
  intros Hloop h after events s tr t tst i Hreachable Hrun Hedges Hbody Hstep Hback Htest
    Hdef Hhome.
  assert (Hsource : reachable_state m s).
  { destruct (run_edges_exec m (base (lssa lv)) h s after Hrun) as [observations Hexec].
    exact (reachable_state_exec m h observations s Hreachable Hexec). }
  destruct (l_back_test m EN EV inventory so lv Hloop s tr t tst Hsource Hstep Hback Htest)
    as [c [Hvalue Hholds]].
  exists c; split.
  - rewrite <- (scev_phi_run_frame m EN EV inventory so lv Hloop h after s (t_lhs tst) i
      Hreachable Hrun Hedges Hdef Hhome); exact Hvalue.
  - rewrite (scev_body_run_bound_frame m EN EV inventory so lv Hloop h events s tst
      Hreachable Hbody Htest) in Hholds; exact Hholds.
Qed.

(** Every feedback step has a concrete previous header carrying its continuation test. *)
Theorem scev_actual_previous_header_guard {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s0 es s tr t tst i,
  initial m s0 -> run_edges m (base (lssa lv)) s0 es s -> step m s tr t ->
  taken (base (lssa lv)) s tr t (lback lv) -> ltest lv = Some tst ->
  def (lssa lv) (t_lhs tst) = Param (lheader lv) i ->
  home (lssa lv) (t_lhs tst) = lheader lv ->
  exists before h after events c,
    es = before ++ after /\ run_edges m (base (lssa lv)) s0 before h /\
    point (base (lssa lv)) h = lheader lv /\
    run_edges m (base (lssa lv)) h after s /\
    Forall (fun e => Graph.target (cfg (base (lssa lv))) e <> lheader lv) after /\
    exec_in m (fun u => lbody lv (point (base (lssa lv)) u) = true) h events s /\
    val (lssa lv) h (t_lhs tst) = Some c /\
    test_holds (width_of so) (t_sign tst) (t_cmp tst) (to_Z so c)
      (eval_iexpr (inv_env lv so h) (t_bound tst)).
Proof.
  intros Hloop s0 es s tr t tst i Hinitial Hrun Hstep Hback Htest Hdef Hhome.
  assert (Hreachable : reachable_state m s).
  { exists s0; destruct (run_edges_exec m (base (lssa lv)) s0 s es Hrun)
      as [events Hexec]; exists events; split; assumption. }
  destruct (view_taken_edge m (base (lssa lv)) s tr t (lback lv)
    (base_laws (l_ssa m EN EV inventory so lv Hloop)) Hreachable Hstep Hback)
    as [_ [Hsource Htarget]].
  assert (Hinside : lbody lv (point (base (lssa lv)) s) = true).
  { rewrite <- Hsource; exact (proj2 (proj2 (l_back_edge m EN EV inventory so lv Hloop))). }
  destruct (scev_same_stay_history m EN EV inventory so lv Hloop s0 es s Hinitial Hrun Hinside)
    as [before [h [after [events [Hes [Hbefore [Hheader [Hafter [Hedges Hbody]]]]]]]]].
  assert (Hheader_reachable : reachable_state m h).
  { exists s0; destruct (run_edges_exec m (base (lssa lv)) s0 h before Hbefore)
      as [observations Hexec]; exists observations; split; assumption. }
  destruct (scev_previous_header_guard m EN EV inventory so lv Hloop h after events s tr t
    tst i Hheader_reachable Hafter Hedges Hbody Hstep Hback Htest Hdef Hhome)
    as [c [Hvalue Hholds]].
  exists before, h, after, events, c; repeat split; assumption.
Qed.

(** * Completed-plan recurrence equations *)

(** Translation reads only the explicitly declared phi leaves of an expression. *)
Lemma scev_translate_expr_phis_agree {V} (left right : V -> option (chrec V)) e :
  (forall x, In x (scev_expression_phis e) -> left x = right x) ->
  scev_translate_expr left e = scev_translate_expr right e.
Proof.
  induction e as [x|x|x a IHa b IHb|x a IHa b IHb|x z]; intro Hagree;
    cbn [scev_translate_expr]; try reflexivity.
  - apply Hagree; left; reflexivity.
  - rewrite IHa, IHb; [reflexivity| |]; intros y Hin; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; [right|left]; exact Hin.
  - rewrite IHa, IHb; [reflexivity| |]; intros y Hin; apply Hagree;
      cbn [scev_expression_phis]; apply in_app_iff; [right|left]; exact Hin.
Qed.

(** Binding translation reads only its declared dependency leaves. *)
Lemma scev_translate_binding_phis_agree {V} (left right : V -> option (chrec V)) b :
  (forall x, In x (scev_binding_phis b) -> left x = right x) ->
  scev_translate_binding left b = scev_translate_binding right b.
Proof.
  intro Hagree; unfold scev_translate_binding; destruct (sb_kind b);
    try reflexivity; destruct (sb_other b) as [e|] eqn:Hother; try reflexivity.
  - rewrite (scev_translate_expr_phis_agree left right e); [reflexivity|].
    intros x Hin; apply Hagree; unfold scev_binding_phis; rewrite Hother; exact Hin.
  - rewrite (scev_translate_expr_phis_agree left right e); [reflexivity|].
    intros x Hin; apply Hagree; unfold scev_binding_phis; rewrite Hother; exact Hin.
Qed.

(** Translating a suffix preserves every key that the suffix does not define. *)
Lemma scev_translate_bindings_preserves {V} (EV : encoding V) bs :
  forall before after, scev_translate_bindings EV bs before = Some after ->
  forall x, ~ In x (map sb_phi bs) -> after x = before x.
Proof.
  induction bs as [|b bs IH]; intros before after Hrun x Hfresh.
  - cbn [scev_translate_bindings] in Hrun; inversion Hrun; reflexivity.
  - cbn [scev_translate_bindings] in Hrun.
    destruct (scev_translate_binding before b) as [c|] eqn:Hbinding; [|discriminate].
    rewrite (IH _ after Hrun x) by (intro Hin; apply Hfresh; right; exact Hin).
    unfold scev_translation_set.
    destruct (Pos.eqb (encode EV x) (encode EV (sb_phi b))) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; apply (encode_injective EV) in Heq; subst x.
    exfalso; apply Hfresh; left; reflexivity.
Qed.

(** Future independence excludes every own or later phi from a binding's dependency leaves. *)
Fixpoint scev_future_independent {V} (bs : list (scev_binding V)) : Prop :=
  match bs with
  | [] => True
  | b :: rest =>
    (forall x, In x (scev_binding_phis b) -> ~ In x (map sb_phi (b :: rest))) /\
      scev_future_independent rest
  end.

(** Distinct concatenated lists have disjoint left and right inventories. *)
Lemma scev_nodup_app_disjoint {A} (left right : list A) :
  NoDup (left ++ right) -> forall x, In x left -> ~ In x right.
Proof.
  intro Hdistinct; induction left as [|a left IH]; intros x Hin; [contradiction|].
  inversion Hdistinct as [|b rest Hfresh Htail]; subst.
  destruct Hin as [Heq|Hin].
  - subst x; intro Hright; apply Hfresh; apply in_app_iff; right; exact Hright.
  - apply IH; [exact Htail|exact Hin].
Qed.

(** A genuinely earlier list position cannot also name a phi in the remaining suffix. *)
Lemma scev_earlier_not_suffix {V} (prefix suffix : list (scev_binding V)) x :
  NoDup (map sb_phi (prefix ++ suffix)) ->
  scev_earlier (prefix ++ suffix) (length prefix) x -> ~ In x (map sb_phi suffix).
Proof.
  intros Hdistinct [i [b [Hnth [Hphi Hlt]]]].
  rewrite nth_error_app1 in Hnth by exact Hlt.
  rewrite map_app in Hdistinct.
  apply (scev_nodup_app_disjoint (map sb_phi prefix) (map sb_phi suffix) Hdistinct x).
  apply in_map_iff; exists b; split; [exact Hphi|eapply nth_error_In; exact Hnth].
Qed.

(** Ranked source validity establishes future independence for every remaining binding suffix. *)
Lemma scev_bindings_future_independent {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) full suffix :
  forall prefix, full = prefix ++ suffix -> NoDup (map sb_phi full) ->
  scev_bindings_valid inventory lv so full (length prefix) suffix ->
    scev_future_independent suffix.
Proof.
  induction suffix as [|b suffix IH]; intros prefix Hfull Hdistinct Hvalid; [exact I|].
  destruct Hvalid as [Hbinding Htail]; split.
  - intros x Hin; apply (scev_earlier_not_suffix prefix (b :: suffix) x).
    + rewrite <- Hfull; exact Hdistinct.
    + rewrite <- Hfull; eapply scev_binding_earlier; eassumption.
  - apply (IH (prefix ++ [b])).
    + rewrite <- app_assoc; cbn; exact Hfull.
    + exact Hdistinct.
    + rewrite length_app; cbn [length]; rewrite Nat.add_1_r; exact Htail.
Qed.

(** Every completed binding keeps both its own recurrence and its final-environment equation. *)
Theorem scev_translate_bindings_equations {V} (EV : encoding V) bs :
  NoDup (map sb_phi bs) -> scev_future_independent bs ->
  forall before after, scev_translate_bindings EV bs before = Some after ->
  forall b, In b bs -> exists c, after (sb_phi b) = Some c /\
    scev_translate_binding after b = Some c.
Proof.
  intros Hdistinct Hindependent; induction bs as [|b bs IH];
    intros before after Hrun a Hin; [contradiction|].
  inversion Hdistinct as [|x xs Hfresh Htail]; subst.
  destruct Hindependent as [Hown Hrest].
  cbn [scev_translate_bindings] in Hrun.
  destruct (scev_translate_binding before b) as [c|] eqn:Hbinding; [|discriminate].
  destruct Hin as [Heq|Hin].
  - subst a; exists c; split.
    + rewrite (scev_translate_bindings_preserves EV bs _ after Hrun (sb_phi b) Hfresh).
      unfold scev_translation_set; rewrite Pos.eqb_refl; reflexivity.
    + rewrite (scev_translate_binding_phis_agree after before b); [exact Hbinding|].
      intros x Hleaf.
      apply (scev_translate_bindings_preserves EV (b :: bs) before after).
      * cbn [scev_translate_bindings]; rewrite Hbinding; exact Hrun.
      * apply Hown; exact Hleaf.
  - apply (IH Htail Hrest (scev_translation_set EV before (sb_phi b) c) after Hrun a Hin).
Qed.

(** An accepted compiled plan supplies equations for every binding in its final phi environment. *)
Theorem scev_checked_compilation_equations {S O N E V K C} (EN : encoding N)
    (EV : encoding V) inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p ch :
  scev_plan_check EN EV inventory lv so p = true -> scev_compile_plan EV p = Some ch ->
  exists lookup, lookup (sp_target p) = Some ch /\
    forall b, In b (sp_bindings p) -> exists c, lookup (sb_phi b) = Some c /\
      scev_translate_binding lookup b = Some c.
Proof.
  intros Hchecked Hcompiled; apply scev_plan_check_sound in Hchecked.
  destruct Hchecked as [Hinventory Hdistinct Hlast Hvalid Hreachable].
  rewrite scev_compile_plan_agrees in Hcompiled; unfold scev_translate_plan in Hcompiled.
  destruct (scev_translate_bindings EV (sp_bindings p) (fun _ => None))
    as [lookup|] eqn:Hrun; [|discriminate].
  exists lookup; split; [exact Hcompiled|].
  assert (Hindependent : scev_future_independent (sp_bindings p)).
  { eapply scev_bindings_future_independent with (prefix := []);
      [reflexivity|exact Hdistinct|exact Hvalid]. }
  exact (scev_translate_bindings_equations EV (sp_bindings p) Hdistinct Hindependent
    (fun _ => None) lookup Hrun).
Qed.

(** * Local recurrence semantics *)

(** Local equations expose actual operands and operator evaluation in one source state. *)
Definition scev_operation_equations {S O N E V K C} (sv : ssa_view S O N E V K C)
    (s : S) (operations : list V) : Prop :=
  forall x o args c, In x operations -> def sv x = Op o args -> val sv s x = Some c ->
    exists cs, Forall2 (fun y d => val sv s y = Some d) args cs /\ op_eval sv o cs = Some c.

(** Restricting a local equation inventory preserves each actual same-source equation. *)
Lemma scev_operation_equations_subset {S O N E V K C} (sv : ssa_view S O N E V K C)
    s smaller larger :
  scev_operation_equations sv s larger ->
  (forall x, In x smaller -> In x larger) -> scev_operation_equations sv s smaller.
Proof.
  intros Hequations Hsubset x o args c Hin Hdef Hvalue.
  apply (Hequations x o args c (Hsubset x Hin) Hdef Hvalue).
Qed.

(** A two-operand equation gives exactly two concrete operand witnesses in source order. *)
Lemma scev_forall2_pair {A B} (R : A -> B -> Prop) a b values :
  Forall2 R [a; b] values -> exists va vb, values = [va; vb] /\ R a va /\ R b vb.
Proof.
  intro Hvalues; inversion Hvalues as [|a' va rest values' Ha Htail]; subst.
  inversion Htail as [|b' vb rest' values'' Hb Hnil]; subst.
  inversion Hnil; subst; exists va, vb; split; [reflexivity|split; assumption].
Qed.

(** An earlier phi is among the source plan's declared phi identifiers. *)
Lemma scev_earlier_member {V} bs rank (x : V) :
  scev_earlier bs rank x -> In x (map sb_phi bs).
Proof.
  intros [i [b [Hnth [Hphi Hlt]]]]; rewrite <- Hphi.
  apply in_map; eapply nth_error_In; exact Hnth.
Qed.

(** Expression translation agrees with actual source values under the simultaneous phi invariant. *)
Theorem scev_expression_value_sound {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rank e
    (lookup : V -> option (chrec V)) (inv : V -> Z) k s :
  scev_ops_laws so (op_eval (lssa lv)) ->
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so s y) ->
  (forall x c d, In x (map sb_phi bs) -> lookup x = Some c -> val (lssa lv) s x = Some d ->
    to_Z so d = wrap (width_of so) (eval_chrec inv c k)) ->
  scev_expression_valid inventory lv so bs rank e -> forall c,
  scev_translate_expr lookup e = Some c ->
  scev_operation_equations (lssa lv) s (scev_expr_operations e) -> forall d,
  val (lssa lv) s (scev_expr_root e) = Some d ->
    to_Z so d = wrap (width_of so) (eval_chrec inv c k).
Proof.
  intros Hops Hinv Hphis Hvalid.
  induction Hvalid as [x Hin Houtside|x Hin Hearlier|
    x a b o Hin Hinside Hdef Hflag Ha IHa Hb IHb|
    x a b o Hin Hinside Hdef Hflag Ha IHa Hb IHb|
    x z o Hin Hinside Hdef Hconst]; intros c Htranslate Hlocal d Hvalue.
  - cbn [scev_translate_expr] in Htranslate; inversion Htranslate; subst c.
    cbn [eval_chrec eval_iexpr]; rewrite (Hinv x Houtside).
    unfold inv_env; cbn [scev_expr_root] in Hvalue; rewrite Hvalue.
    apply (to_Z_canonical so (op_eval (lssa lv)) Hops).
  - cbn [scev_translate_expr] in Htranslate; cbn [scev_expr_root] in Hvalue.
    apply (Hphis x c d (scev_earlier_member bs rank x Hearlier) Htranslate Hvalue).
  - cbn [scev_translate_expr] in Htranslate.
    destruct (scev_translate_expr lookup a) as [ca|] eqn:Hca; [|discriminate].
    destruct (scev_translate_expr lookup b) as [cb|] eqn:Hcb; [|discriminate].
    inversion Htranslate; subst c; cbn [scev_expr_root] in Hvalue.
    destruct (Hlocal x o [scev_expr_root a; scev_expr_root b] d (or_introl eq_refl)
      Hdef Hvalue) as [values [Hvalues Heval]].
    destruct (scev_forall2_pair _ _ _ values Hvalues) as [va [vb [Hlist [Hva Hvb]]]];
      subst values.
    assert (Hleft : to_Z so va = wrap (width_of so) (eval_chrec inv ca k)).
    { apply (IHa ca eq_refl); [|exact Hva].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros y Hy; right; apply in_app_iff; left; exact Hy. }
    assert (Hright : to_Z so vb = wrap (width_of so) (eval_chrec inv cb k)).
    { apply (IHb cb eq_refl); [|exact Hvb].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros y Hy; right; apply in_app_iff; right; exact Hy. }
    rewrite (add_laws so (op_eval (lssa lv)) Hops o va vb d Hflag Heval),
      eval_chrec_add, Hleft, Hright; symmetry; apply wrap_add.
  - cbn [scev_translate_expr] in Htranslate.
    destruct (scev_translate_expr lookup a) as [ca|] eqn:Hca; [|discriminate].
    destruct (scev_translate_expr lookup b) as [cb|] eqn:Hcb; [|discriminate].
    inversion Htranslate; subst c; cbn [scev_expr_root] in Hvalue.
    destruct (Hlocal x o [scev_expr_root a; scev_expr_root b] d (or_introl eq_refl)
      Hdef Hvalue) as [values [Hvalues Heval]].
    destruct (scev_forall2_pair _ _ _ values Hvalues) as [va [vb [Hlist [Hva Hvb]]]];
      subst values.
    assert (Hleft : to_Z so va = wrap (width_of so) (eval_chrec inv ca k)).
    { apply (IHa ca eq_refl); [|exact Hva].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros y Hy; right; apply in_app_iff; left; exact Hy. }
    assert (Hright : to_Z so vb = wrap (width_of so) (eval_chrec inv cb k)).
    { apply (IHb cb eq_refl); [|exact Hvb].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros y Hy; right; apply in_app_iff; right; exact Hy. }
    rewrite (mul_laws so (op_eval (lssa lv)) Hops o va vb d Hflag Heval),
      eval_chrec_mul, Hleft, Hright; symmetry; apply wrap_mul.
  - cbn [scev_translate_expr] in Htranslate; inversion Htranslate; subst c.
    cbn [scev_expr_root] in Hvalue.
    destruct (Hlocal x o [] d (or_introl eq_refl) Hdef Hvalue) as [values [Hvalues Heval]].
    inversion Hvalues; subst values.
    exact (const_laws so (op_eval (lssa lv)) Hops o z d Hconst Heval).
Qed.

(** Every compiled supported binding starts with its selected invariant base. *)
Lemma scev_binding_initial_value {V} (lookup : V -> option (chrec V)) b c (inv : V -> Z) :
  scev_translate_binding lookup b = Some c -> eval_chrec inv c 0 = inv (sb_base b).
Proof.
  unfold scev_translate_binding; destruct (sb_kind b); destruct (sb_other b) as [e|];
    try discriminate; try (intro Heq; inversion Heq; reflexivity).
  - destruct (scev_translate_expr lookup e); cbn [option_map];
      intro Heq; inversion Heq; reflexivity.
  - destruct (scev_translate_expr lookup e); cbn [option_map];
      intro Heq; inversion Heq; reflexivity.
Qed.

(** Update operands provide phi and other-root witnesses independently of their order. *)
Lemma scev_forall2_update {A B} (R : A -> B -> Prop) (first : bool) phi other values :
  Forall2 R (if first then [phi; other] else [other; phi]) values ->
  exists p q, R phi p /\ R other q /\
    values = if first then [p; q] else [q; p].
Proof.
  destruct first; intro Hvalues; destruct (scev_forall2_pair R _ _ values Hvalues)
    as [a [b [Heq [Ha Hb]]]].
  - exists a, b; split; [exact Ha|]; split; assumption.
  - exists b, a; split; [exact Hb|]; split; assumption.
Qed.

(** Commutative update evaluation preserves the phi/other distinction in either operand order. *)
Lemma scev_binary_update_value {S O N E V K C} (sv : ssa_view S O N E V K C)
    (so : scev_ops K C) (combine : Z -> Z -> Z) s operations update phi other
    (first : bool) o d :
  (forall a b, combine a b = combine b a) ->
  (forall a b r, op_eval sv o [a; b] = Some r ->
    to_Z so r = wrap (width_of so) (combine (to_Z so a) (to_Z so b))) ->
  scev_operation_equations sv s operations -> In update operations ->
  def sv update = Op o (if first then [phi; other] else [other; phi]) ->
  val sv s update = Some d ->
  exists p q, val sv s phi = Some p /\ val sv s other = Some q /\
    to_Z so d = wrap (width_of so) (combine (to_Z so p) (to_Z so q)).
Proof.
  intros Hcomm Heval Hlocal Hin Hdef Hvalue.
  destruct (Hlocal update o _ d Hin Hdef Hvalue) as [values [Hvalues Hresult]].
  destruct (scev_forall2_update _ first phi other values Hvalues)
    as [p [q [Hp [Hq Hlist]]]]; subst values.
  exists p, q; split; [exact Hp|]; split; [exact Hq|].
  destruct first; [apply Heval; exact Hresult|].
  rewrite Hcomm; apply Heval; exact Hresult.
Qed.

(** The simultaneous invariant observes every compiled phi in one invariant environment. *)
Definition scev_phi_values {S O N E V K C} (lv : loop_view S O N E V K C)
    (so : scev_ops K C) (bs : list (scev_binding V)) (lookup : V -> option (chrec V))
    (inv : V -> Z) (k : nat) (s : S) : Prop :=
  forall x c d, In x (map sb_phi bs) -> lookup x = Some c -> val (lssa lv) s x = Some d ->
    to_Z so d = wrap (width_of so) (eval_chrec inv c k).

(** An actual update evaluates to its next recurrence point, with backward definedness. *)
Theorem scev_binding_update_sound {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rank b
    (lookup : V -> option (chrec V)) (inv : V -> Z) k s c d :
  scev_ops_laws so (op_eval (lssa lv)) ->
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so s y) ->
  scev_phi_values lv so bs lookup inv k s -> In (sb_phi b) (map sb_phi bs) ->
  lookup (sb_phi b) = Some c ->
  scev_binding_valid inventory lv so bs rank b -> scev_translate_binding lookup b = Some c ->
  scev_operation_equations (lssa lv) s
    (sb_update_value b :: match sb_other b with
      | Some e => scev_expr_operations e
      | None => []
      end) ->
  val (lssa lv) s (sb_update_value b) = Some d ->
    to_Z so d = wrap (width_of so) (eval_chrec inv c (Nat.succ k)).
Proof.
  intros Hops Hinv Hphis Hmember Hlookup [_ Hvalid] Htranslate Hlocal Hvalue.
  destruct b as [phi base update kind other first]; destruct kind;
    destruct other as [e|]; cbn [scev_update_valid sb_kind sb_other sb_phi sb_update_value
      sb_base sb_phi_first] in *; try contradiction.
  - unfold scev_translate_binding in Htranslate; cbn [sb_kind sb_other sb_base] in Htranslate.
    destruct (scev_translate_expr lookup e) as [other_c|] eqn:Hother; [|discriminate].
    cbn [option_map] in Htranslate; inversion Htranslate; subst c.
    destruct Hvalid as [[Hdifferent [Hin [Hinside [o [Hdef Hflag]]]]] Hexpr].
    destruct (scev_binary_update_value (lssa lv) so Z.add s _ update phi
      (scev_expr_root e) first o d Z.add_comm
      (fun a b r => add_laws so (op_eval (lssa lv)) Hops o a b r Hflag)
      Hlocal (or_introl eq_refl) Hdef Hvalue) as [p [q [Hp [Hq Hresult]]]].
    assert (Hphi : to_Z so p = wrap (width_of so)
      (eval_chrec inv (CRec (CInv (IVar base)) other_c) k)).
    { apply (Hphis phi (CRec (CInv (IVar base)) other_c) p Hmember); [|exact Hp].
      exact Hlookup. }
    assert (Hrhs : to_Z so q = wrap (width_of so) (eval_chrec inv other_c k)).
    { eapply scev_expression_value_sound; [exact Hops|exact Hinv|exact Hphis|exact Hexpr|
        exact Hother| |exact Hq].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros x Hinop; right; exact Hinop. }
    change (to_Z so d = wrap (width_of so)
      (eval_chrec inv (CRec (CInv (IVar base)) other_c) k + eval_chrec inv other_c k)).
    rewrite Hresult, Hphi, Hrhs; symmetry; apply wrap_add.
  - unfold scev_translate_binding in Htranslate; cbn [sb_kind sb_other sb_base] in Htranslate.
    destruct (scev_translate_expr lookup e) as [other_c|] eqn:Hother; [|discriminate].
    cbn [option_map] in Htranslate; inversion Htranslate; subst c.
    destruct Hvalid as [[Hdifferent [Hin [Hinside [o [Hdef Hflag]]]]] Hexpr].
    destruct (scev_binary_update_value (lssa lv) so Z.mul s _ update phi
      (scev_expr_root e) first o d Z.mul_comm
      (fun a b r => mul_laws so (op_eval (lssa lv)) Hops o a b r Hflag)
      Hlocal (or_introl eq_refl) Hdef Hvalue) as [p [q [Hp [Hq Hresult]]]].
    assert (Hphi : to_Z so p = wrap (width_of so)
      (eval_chrec inv (CGeo (CInv (IVar base)) other_c) k)).
    { apply (Hphis phi (CGeo (CInv (IVar base)) other_c) p Hmember); [|exact Hp].
      exact Hlookup. }
    assert (Hrhs : to_Z so q = wrap (width_of so) (eval_chrec inv other_c k)).
    { eapply scev_expression_value_sound; [exact Hops|exact Hinv|exact Hphis|exact Hexpr|
        exact Hother| |exact Hq].
      eapply scev_operation_equations_subset; [exact Hlocal|].
      intros x Hinop; right; exact Hinop. }
    change (to_Z so d = wrap (width_of so)
      (eval_chrec inv (CGeo (CInv (IVar base)) other_c) k * eval_chrec inv other_c k)).
    rewrite Hresult, Hphi, Hrhs; symmetry; apply wrap_mul.
  - unfold scev_translate_binding in Htranslate; cbn [sb_kind sb_base] in Htranslate.
    inversion Htranslate; subst c.
    destruct Hvalid as [Hfirst [Hin [Hinside [o [Hdef Hflag]]]]]; subst first.
    destruct (scev_binary_update_value (lssa lv) so Z.add s [update] update phi phi true o d
      Z.add_comm (fun a b r => add_laws so (op_eval (lssa lv)) Hops o a b r Hflag)
      Hlocal (or_introl eq_refl) Hdef Hvalue) as [p [q [Hp [Hq Hresult]]]].
    assert (Heq : p = q) by congruence; subst q.
    assert (Hphi : to_Z so p = wrap (width_of so)
      (eval_chrec inv (CGeo (CInv (IVar base)) (CInv (IConst 2))) k)).
    { apply (Hphis phi (CGeo (CInv (IVar base)) (CInv (IConst 2))) p Hmember);
        [exact Hlookup|exact Hp]. }
    change (to_Z so d = wrap (width_of so)
      (eval_chrec inv (CGeo (CInv (IVar base)) (CInv (IConst 2))) k * 2)).
    rewrite Hresult, Hphi, <- wrap_add.
    f_equal; ring.
Qed.

(** Every listed valid binding carries its actual rank and all independent source conditions. *)
Lemma scev_plan_binding_rank {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) p b :
  scev_plan_valid inventory lv so p -> In b (sp_bindings p) ->
  exists rank, scev_binding_valid inventory lv so (sp_bindings p) rank b.
Proof.
  intros Hvalid Hin; apply In_nth_error in Hin; destruct Hin as [rank Hnth].
  exists rank; exact (scev_bindings_valid_position inventory lv so (sp_bindings p)
    (sp_bindings p) 0 rank b (spv_bindings _ _ _ _ Hvalid) Hnth).
Qed.

(** Each binding's local equation inventory is contained in the checked plan's inventory. *)
Lemma scev_plan_binding_operations {V} (p : scev_plan V) b : In b (sp_bindings p) ->
  forall x, In x (sb_update_value b :: match sb_other b with
    | Some e => scev_expr_operations e
    | None => []
    end) -> In x (scev_plan_operations p).
Proof.
  intros Hb x Hx; unfold scev_plan_operations; apply in_flat_map.
  exists b; split; assumption.
Qed.

(** Compilation equations identify the recurrence of any binding by its final phi lookup. *)
Definition scev_compilation_equations {V} (p : scev_plan V)
    (lookup : V -> option (chrec V)) : Prop :=
  forall b c, In b (sp_bindings p) -> lookup (sb_phi b) = Some c ->
    scev_translate_binding lookup b = Some c.

(** A consistent state supports every invariant environment matching its actual outside values. *)
Definition scev_state_consistent {S O N E V K C} (lv : loop_view S O N E V K C)
    (so : scev_ops K C) (p : scev_plan V) (lookup : V -> option (chrec V))
    (k : nat) (s : S) : Prop :=
  forall inv, (forall y, lbody lv (home (lssa lv) y) = false ->
    inv y = inv_env lv so s y) -> scev_phi_values lv so (sp_bindings p) lookup inv k s.

(** Actual entry copies every recognized base and establishes all zero-index recurrences. *)
Theorem scev_entry_values {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) p lookup :
  loop_view_laws m EN EV inventory so lv -> scev_ops_laws so (op_eval (lssa lv)) ->
  scev_plan_valid inventory lv so p -> scev_compilation_equations p lookup ->
  forall s tr t, reachable_state m s -> step m s tr t ->
  taken (base (lssa lv)) s tr t (lentry lv) -> scev_state_consistent lv so p lookup 0 t.
Proof.
  intros Hloop Hops Hvalid Hcompile s tr t Hreachable Hstep Htaken inv Hinv x c d
    Hin Hlookup Hvalue.
  apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
  destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb) as [rank [Hheader Hupdate]].
  destruct Hheader as [Hinphi [Hinbase [Hinupdate [Hhome [Hbase [Huphome
    [i [Hdef [Hentry Hback]]]]]]]]].
  destruct (taken_edge (base_laws (l_ssa m EN EV inventory so lv Hloop)) s tr t (lentry lv)
    Hreachable Hstep Htaken) as [_ Htarget].
  destruct (l_entry_edge m EN EV inventory so lv Hloop) as [_ [Hentry_target _]].
  assert (Hpoint : point (base (lssa lv)) t = lheader lv) by congruence.
  pose proof (l_phi_binding m EN EV inventory so lv Hloop s tr t (lentry lv) (sb_phi b) i
    Hreachable Hstep Htaken Hentry_target Hdef) as Hbinding.
  rewrite Hentry in Hbinding; rewrite Hbinding in Hvalue.
  assert (Hbase_frame : val (lssa lv) t (sb_base b) = val (lssa lv) s (sb_base b)).
  { apply (frame_on_edge (l_strict m EN EV inventory so lv Hloop) s tr t (lentry lv)
      (sb_base b) Hreachable Hstep Htaken).
    intro Heq; rewrite Heq, Hpoint in Hbase.
    pose proof (l_header_inside m EN EV inventory so lv Hloop); congruence. }
  rewrite (scev_binding_initial_value lookup b c inv (Hcompile b c Hb Hlookup)).
  rewrite (Hinv (sb_base b) Hbase); unfold inv_env; rewrite Hbase_frame, Hvalue.
  apply (to_Z_canonical so (op_eval (lssa lv)) Hops).
Qed.

(** Actual feedback copies each checked update and advances all compiled recurrences together. *)
Theorem scev_back_values {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) p lookup :
  loop_view_laws m EN EV inventory so lv -> scev_ops_laws so (op_eval (lssa lv)) ->
  scev_plan_check EN EV inventory lv so p = true ->
  scev_compilation_equations p lookup -> forall s tr t k,
  reachable_state m s -> step m s tr t -> taken (base (lssa lv)) s tr t (lback lv) ->
  scev_state_consistent lv so p lookup k s ->
    scev_state_consistent lv so p lookup (Nat.succ k) t.
Proof.
  intros Hloop Hops Hchecked Hcompile s tr t k Hreachable Hstep Htaken Hstate.
  pose proof (scev_plan_check_sound EN EV inventory lv so p Hchecked) as Hvalid.
  destruct (view_taken_edge m (base (lssa lv)) s tr t (lback lv)
    (base_laws (l_ssa m EN EV inventory so lv Hloop)) Hreachable Hstep Htaken)
    as [_ [Hsource Htarget]].
  destruct (l_back_edge m EN EV inventory so lv Hloop) as [_ [Hback_target Hsource_inside]].
  assert (Hinside : lbody lv (point (base (lssa lv)) s) = true) by
    (rewrite <- Hsource; exact Hsource_inside).
  assert (Hinside' : lbody lv (point (base (lssa lv)) t) = true) by
    (rewrite <- Htarget, Hback_target; exact (l_header_inside m EN EV inventory so lv Hloop)).
  intros inv Hinv x c d Hin Hlookup Hvalue.
  assert (Hinv_source : forall y, lbody lv (home (lssa lv) y) = false ->
    inv y = inv_env lv so s y).
  { intros y Houtside; rewrite Hinv by exact Houtside; unfold inv_env.
    rewrite (scev_body_step_outside_frame m EN EV inventory so lv Hloop s tr t y
      Hreachable Hstep Hinside Hinside' Houtside); reflexivity. }
  apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
  destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb) as [rank Hbinding].
  destruct (proj1 Hbinding) as [Hinphi [Hinbase [Hinupdate [Hhome [Hbase [Huphome
    [i [Hdef [Hentry Hback]]]]]]]]].
  pose proof (l_phi_binding m EN EV inventory so lv Hloop s tr t (lback lv) (sb_phi b) i
    Hreachable Hstep Htaken Hback_target Hdef) as Hphi.
  rewrite Hback in Hphi; rewrite Hphi in Hvalue.
  eapply scev_binding_update_sound with (rank := rank); [exact Hops|exact Hinv_source|
    apply Hstate; exact Hinv_source| |exact Hlookup|exact Hbinding|
    exact (Hcompile b c Hb Hlookup)| |exact Hvalue].
  - apply in_map; exact Hb.
  - intros y o args value Hy Hdefinition Hval.
    eapply (l_plan_op_at_back m EN EV inventory so lv Hloop s tr t p y o args value);
      [exact Hreachable|exact Hstep|exact Htaken|exact Hchecked|
        apply (scev_plan_binding_operations p b Hb y Hy)|exact Hdefinition|exact Hval].
Qed.

(** Exact outside and phi frames transport the simultaneous invariant without changing its index. *)
Lemma scev_state_frames {S O N E V K C} (lv : loop_view S O N E V K C)
    (so : scev_ops K C) p lookup k s t :
  (forall y, lbody lv (home (lssa lv) y) = false -> val (lssa lv) t y = val (lssa lv) s y) ->
  (forall x, In x (map sb_phi (sp_bindings p)) -> val (lssa lv) t x = val (lssa lv) s x) ->
  scev_state_consistent lv so p lookup k s -> scev_state_consistent lv so p lookup k t.
Proof.
  intros Houtside Hphis Hstate inv Hinv x c d Hin Hlookup Hvalue.
  assert (Hmatch : forall y, lbody lv (home (lssa lv) y) = false ->
    inv y = inv_env lv so s y).
  { intros y Hy; rewrite Hinv by exact Hy; unfold inv_env; rewrite Houtside by exact Hy;
      reflexivity. }
  rewrite (Hphis x Hin) in Hvalue.
  exact (Hstate inv Hmatch x c d Hin Hlookup Hvalue).
Qed.

(** An ordinary body edge has an inside source and avoids the header and both special edges. *)
Lemma scev_ordinary_edge_inside {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) :
  loop_view_laws m EN EV inventory so lv -> forall s tr t e,
  reachable_state m s -> step m s tr t -> taken (base (lssa lv)) s tr t e ->
  e <> lentry lv -> e <> lback lv -> lbody lv (point (base (lssa lv)) t) = true ->
  lbody lv (point (base (lssa lv)) s) = true /\
    Graph.target (cfg (base (lssa lv))) e <> lheader lv.
Proof.
  intros Hloop s tr t e Hreachable Hstep Htaken Hentry Hback Hinside'.
  destruct (view_taken_edge m (base (lssa lv)) s tr t e
    (base_laws (l_ssa m EN EV inventory so lv Hloop)) Hreachable Hstep Htaken)
    as [Hlisted [Hsource Htarget]].
  split.
  - destruct (lbody lv (point (base (lssa lv)) s)) eqn:Hinside; [reflexivity|].
    exfalso; apply Hentry; eapply (l_single_ingress m EN EV inventory so lv Hloop);
      [exact Hlisted|rewrite Hsource; exact Hinside|rewrite Htarget; exact Hinside'].
  - intro Heq; destruct (l_simple m EN EV inventory so lv Hloop e Hlisted Heq);
      contradiction.
Qed.

(** Every body point on every actual run satisfies all checked-plan recurrences simultaneously. *)
Theorem scev_plan_run_sound {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) p lookup :
  loop_view_laws m EN EV inventory so lv -> scev_ops_laws so (op_eval (lssa lv)) ->
  scev_plan_check EN EV inventory lv so p = true -> scev_compilation_equations p lookup ->
  forall s0 es s, initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
  lbody lv (point (base (lssa lv)) s) = true ->
    scev_state_consistent lv so p lookup (stay_arrivals EE lv es) s.
Proof.
  intros Hloop Hops Hchecked Hcompile s0 es s Hinitial Hrun.
  pose proof (scev_plan_check_sound EN EV inventory lv so p Hchecked) as Hvalid.
  pose proof (base_laws (l_ssa m EN EV inventory so lv Hloop)) as Hview.
  change ((fun u prefix => lbody lv (point (base (lssa lv)) u) = true ->
    scev_state_consistent lv so p lookup (stay_arrivals EE lv prefix) u) s ([] ++ es)).
  eapply scev_run_edges_invariant; [| |exact Hrun| |].
  - intros u tr t e prefix Hreachable Hstate Hstep Htaken Hinside'.
    destruct (scev_key_eq EE e (lentry lv)) eqn:Hentry.
    + apply scev_key_eq_spec in Hentry; subst e; rewrite scev_arrivals_entry.
      eapply scev_entry_values; eassumption.
    + assert (Hnotentry : e <> lentry lv).
      { intro Heq; pose proof (proj2 (scev_key_eq_spec EE _ _) Heq); congruence. }
      destruct (scev_key_eq EE e (lback lv)) eqn:Hback.
      * apply scev_key_eq_spec in Hback; subst e.
        rewrite (scev_arrivals_back m EN EE EV inventory so lv prefix Hloop).
        eapply scev_back_values; [exact Hloop|exact Hops|exact Hchecked|exact Hcompile|
          exact Hreachable|exact Hstep|exact Htaken|].
        apply Hstate.
        destruct (view_taken_edge m (base (lssa lv)) u tr t (lback lv) Hview
          Hreachable Hstep Htaken) as [_ [Hsource _]].
        rewrite <- Hsource; exact (proj2 (proj2 (l_back_edge m EN EV inventory so lv Hloop))).
      * assert (Hnotback : e <> lback lv).
        { intro Heq; pose proof (proj2 (scev_key_eq_spec EE _ _) Heq); congruence. }
        destruct (scev_ordinary_edge_inside m EN EV inventory so lv Hloop u tr t e
          Hreachable Hstep Htaken Hnotentry Hnotback Hinside') as [Hinside Htarget].
        rewrite (scev_arrivals_header_suffix m EN EE EV inventory so lv prefix [e] Hloop)
          by (constructor; [exact Htarget|constructor]).
        apply (scev_state_frames lv so p lookup _ u t); [| |apply Hstate; exact Hinside].
        -- intros y Hy; eapply scev_body_step_outside_frame; eassumption.
        -- intros x Hin; apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
           destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb)
             as [rank [Hheader Hupdate]].
           destruct Hheader as [_ [_ [_ [Hhome Hrest]]]].
           apply (frame_on_edge (l_strict m EN EV inventory so lv Hloop) u tr t e
             (sb_phi b) Hreachable Hstep Htaken).
           destruct (taken_edge Hview u tr t e Hreachable Hstep Htaken) as [_ Hpoint].
           rewrite Hhome, <- Hpoint; congruence.
  - intros u tr t prefix Hreachable Hstate Hstep Hstay Hinside'.
    assert (Hinside : lbody lv (point (base (lssa lv)) u) = true).
    { rewrite <- (stays_point Hview u tr t Hreachable Hstep Hstay); exact Hinside'. }
    apply (scev_state_frames lv so p lookup _ u t); [| |apply Hstate; exact Hinside].
    + intros y Hy; eapply scev_body_step_outside_frame; eassumption.
    + intros x Hin; apply in_map_iff in Hin; destruct Hin as [b [Hphi Hb]]; subst x.
      destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb)
        as [rank [Hheader Hupdate]].
      destruct Hheader as [_ [_ [_ [Hhome [_ [_ [i [Hdef Hargs]]]]]]]].
      eapply scev_phi_stay_frame; eassumption.
  - exists s0, []; split; [exact Hinitial|constructor].
  - intro Hinside; pose proof (entry_points Hview s0 Hinitial) as Hentry.
    pose proof (l_initial_outside m EN EV inventory so lv Hloop _ Hentry); congruence.
Qed.

(** Recognition agrees with the wrapped recurrence at every actual header arrival of the stay. *)
Theorem scev_sound {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EE : encoding E) (EV : encoding V) (inventory : list V)
    (lv : loop_view S O N E V K C) (so : scev_ops K C) (x : V) (ch : chrec V) :
  loop_view_laws m EN EV inventory so lv ->
  scev_ops_laws so (op_eval (lssa lv)) ->
  recognise EN EV inventory lv so x = Some ch ->
  forall s0 es s c, initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
    point (base (lssa lv)) s = lheader lv -> val (lssa lv) s x = Some c ->
    to_Z so c = wrap (width_of so)
      (eval_chrec (inv_env lv so s) ch (stay_arrivals EE lv es)).
Proof.
  intros Hloop Hops Hrecognise; unfold recognise in Hrecognise.
  destruct (recognise_plan EN EV inventory lv so x) as [[found p]|] eqn:Hplan;
    [|discriminate].
  inversion Hrecognise; subst found.
  destruct (recognise_plan_checked EN EV inventory lv so x ch p Hplan)
    as [Htarget [Hchecked Hcompiled]].
  destruct (scev_checked_compilation_equations EN EV inventory lv so p ch Hchecked Hcompiled)
    as [lookup [Hlookup Hequations]].
  assert (Hcompile : scev_compilation_equations p lookup).
  { intros b c Hb Hc; destruct (Hequations b Hb) as [own [Hown Htranslation]].
    assert (own = c) by congruence; subst own; exact Htranslation. }
  pose proof (scev_plan_check_sound EN EV inventory lv so p Hchecked) as Hvalid.
  intros s0 es s c Hinitial Hrun Hheader Hvalue.
  pose proof (scev_plan_run_sound m EN EE EV inventory so lv p lookup Hloop Hops Hchecked
    Hcompile s0 es s Hinitial Hrun) as Hstate.
  rewrite Hheader in Hstate; specialize (Hstate (l_header_inside m EN EV inventory so lv Hloop)).
  assert (Hin : In x (map sb_phi (sp_bindings p))).
  { destruct (spv_last _ _ _ _ Hvalid) as [prefix [b [Hbindings Hphi]]].
    rewrite <- Htarget, <- Hphi, Hbindings, map_app; apply in_app_iff; right; left; reflexivity.
  }
  assert (Hlookup_x : lookup x = Some ch) by (rewrite <- Htarget; exact Hlookup).
  exact (Hstate (inv_env lv so s) (fun y _ => eq_refl) x ch c Hin Hlookup_x Hvalue).
Qed.

(** Equal wrapped operands give exactly the same continuation observation. *)
Lemma scev_test_congruent w sg cmp a a' b b' :
  wrap w a = wrap w a' -> wrap w b = wrap w b' ->
  test_holds w sg cmp a b <-> test_holds w sg cmp a' b'.
Proof.
  intros Ha Hb; unfold test_holds.
  rewrite (view_z_congruent w sg a a' Ha), (view_z_congruent w sg b b' Hb); reflexivity.
Qed.

(** Normalized trip evidence retains the exact wrapped first-failure observation. *)
Definition scev_normalized_trip {V} (inv : V -> Z) w sg cmp (ch : chrec V)
    (bound : iexpr V) (t : N) : Prop :=
  trip_count (fun y => view_z w sg (inv y)) w sg cmp (signed_chrec w sg ch)
    (signed_iexpr w sg bound) = Some t.

(** An actual continuing raw recurrence point cannot equal its normalized first failed index. *)
Lemma scev_normalized_failure_excludes_guard {V} (inv : V -> Z) w sg cmp ch bound t k :
  scev_normalized_trip inv w sg cmp ch bound t ->
  test_holds w sg cmp (eval_chrec inv ch k) (eval_iexpr inv bound) -> N.of_nat k <> t.
Proof.
  intros Htrip Hguard Hindex.
  destruct (trip_count_first_failure _ w sg cmp _ _ t Htrip) as [_ Hfailed].
  rewrite <- Hindex, Nat2N.id in Hfailed; apply Hfailed.
  apply (proj1 (scev_test_congruent w sg cmp _ _ _ _
    (signed_chrec_wrap w sg inv ch k) (signed_iexpr_wrap w sg inv bound))); exact Hguard.
Qed.

(** The actual back-source guard holds on the recurrence in any matching outside environment. *)
Lemma scev_back_recurrence_guard {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) p lookup tst ch :
  loop_view_laws m EN EV inventory so lv -> ltest lv = Some tst ->
  In (t_lhs tst) (map sb_phi (sp_bindings p)) -> lookup (t_lhs tst) = Some ch ->
  forall s tr t inv k, reachable_state m s -> step m s tr t ->
  taken (base (lssa lv)) s tr t (lback lv) ->
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so s y) ->
  scev_phi_values lv so (sp_bindings p) lookup inv k s ->
  test_holds (width_of so) (t_sign tst) (t_cmp tst) (eval_chrec inv ch k)
    (eval_iexpr inv (t_bound tst)).
Proof.
  intros Hloop Htest Hmember Hlookup s tr t inv k Hreachable Hstep Htaken Hinv Hphis.
  destruct (l_back_test m EN EV inventory so lv Hloop s tr t tst Hreachable Hstep Htaken Htest)
    as [c [Hvalue Hguard]].
  pose proof (Hphis (t_lhs tst) ch c Hmember Hlookup Hvalue) as Hphi.
  assert (Hbound : eval_iexpr inv (t_bound tst) = eval_iexpr (inv_env lv so s) (t_bound tst)).
  { apply eval_iexpr_variables_agree; intros y Hy; apply Hinv.
    eapply (l_test_outside m EN EV inventory so lv Hloop); eassumption. }
  assert (Hwrap_phi : wrap (width_of so) (to_Z so c) =
    wrap (width_of so) (eval_chrec inv ch k)) by (rewrite Hphi, wrap_wrap; reflexivity).
  assert (Hwrap_bound : wrap (width_of so) (eval_iexpr (inv_env lv so s) (t_bound tst)) =
    wrap (width_of so) (eval_iexpr inv (t_bound tst))) by (rewrite Hbound; reflexivity).
  exact (proj1 (scev_test_congruent (width_of so) (t_sign tst) (t_cmp tst)
    (to_Z so c) (eval_chrec inv ch k) (eval_iexpr (inv_env lv so s) (t_bound tst))
      (eval_iexpr inv (t_bound tst)) Hwrap_phi Hwrap_bound) Hguard).
Qed.

(** A final matching environment also matches the source of an inside-body step. *)
Lemma scev_body_step_environment {S O N E V K C} (m : semantics S O)
    (EN : encoding N) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O N E V K C) u tr v inv :
  loop_view_laws m EN EV inventory so lv -> reachable_state m u -> step m u tr v ->
  lbody lv (point (base (lssa lv)) u) = true ->
  lbody lv (point (base (lssa lv)) v) = true ->
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so v y) ->
  forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so u y.
Proof.
  intros Hloop Hreachable Hstep Hinside Hinside' Hinv y Hy.
  rewrite Hinv by exact Hy; unfold inv_env.
  rewrite (scev_body_step_outside_frame m EN EV inventory so lv Hloop u tr v y
    Hreachable Hstep Hinside Hinside' Hy); reflexivity.
Qed.

(** An actual feedback step cannot pass the normalized first failure in its own stay. *)
Lemma scev_back_trip_bound_step {S O Node E V K C} (m : semantics S O)
    (EN : encoding Node) (EE : encoding E) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O Node E V K C) p lookup tst ch s0 prefix u tr v inv t :
  loop_view_laws m EN EV inventory so lv -> scev_ops_laws so (op_eval (lssa lv)) ->
  scev_plan_check EN EV inventory lv so p = true -> scev_compilation_equations p lookup ->
  ltest lv = Some tst -> In (t_lhs tst) (map sb_phi (sp_bindings p)) ->
  lookup (t_lhs tst) = Some ch -> initial m s0 ->
  run_edges m (base (lssa lv)) s0 prefix u ->
  reachable_state m u -> step m u tr v -> taken (base (lssa lv)) u tr v (lback lv) ->
  lbody lv (point (base (lssa lv)) v) = true ->
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so v y) ->
  scev_normalized_trip inv (width_of so) (t_sign tst) (t_cmp tst) ch (t_bound tst) t ->
  (lbody lv (point (base (lssa lv)) u) = true ->
    (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so u y) ->
    (N.of_nat (stay_arrivals EE lv prefix) <= t)%N) ->
  (N.of_nat (stay_arrivals EE lv (prefix ++ [lback lv])) <= t)%N.
Proof.
  intros Hloop Hops Hchecked Hcompile Htest Hmember Hlookup Hinitial Hprefix
    Hreachable Hstep Htaken Hinside' Hinv Htrip Hprevious.
  pose proof (base_laws (l_ssa m EN EV inventory so lv Hloop)) as Hview.
  destruct (view_taken_edge m (base (lssa lv)) u tr v (lback lv) Hview
    Hreachable Hstep Htaken) as [_ [Hsource _]].
  assert (Hinside : lbody lv (point (base (lssa lv)) u) = true).
  { rewrite <- Hsource; exact (proj2 (proj2
      (l_back_edge m EN EV inventory so lv Hloop))). }
  pose proof (scev_body_step_environment m EN EV inventory so lv u tr v inv Hloop
    Hreachable Hstep Hinside Hinside' Hinv) as Hinv_source.
  specialize (Hprevious Hinside Hinv_source).
  pose proof (scev_plan_run_sound m EN EE EV inventory so lv p lookup Hloop Hops
    Hchecked Hcompile s0 prefix u Hinitial Hprefix Hinside inv Hinv_source) as Hphis.
  pose proof (scev_back_recurrence_guard m EN EV inventory so lv p lookup tst ch
    Hloop Htest Hmember Hlookup u tr v inv (stay_arrivals EE lv prefix)
    Hreachable Hstep Htaken Hinv_source Hphis) as Hguard.
  pose proof (scev_normalized_failure_excludes_guard inv (width_of so) (t_sign tst)
    (t_cmp tst) ch (t_bound tst) t (stay_arrivals EE lv prefix) Htrip Hguard) as Hne.
  rewrite (scev_arrivals_back m EN EE EV inventory so lv prefix Hloop), Nat2N.inj_succ; lia.
Qed.

(** A checked plan's exact first failure bounds every arrival in the same actual stay. *)
Theorem scev_plan_trip_bound {S O Node E V K C} (m : semantics S O)
    (EN : encoding Node) (EE : encoding E) (EV : encoding V) inventory (so : scev_ops K C)
    (lv : loop_view S O Node E V K C) p lookup tst ch :
  loop_view_laws m EN EV inventory so lv -> scev_ops_laws so (op_eval (lssa lv)) ->
  scev_plan_check EN EV inventory lv so p = true -> scev_compilation_equations p lookup ->
  ltest lv = Some tst -> In (t_lhs tst) (map sb_phi (sp_bindings p)) ->
  lookup (t_lhs tst) = Some ch -> forall s0 es s,
  initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
  lbody lv (point (base (lssa lv)) s) = true -> forall inv t,
  (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so s y) ->
  scev_normalized_trip inv (width_of so) (t_sign tst) (t_cmp tst) ch (t_bound tst) t ->
    (N.of_nat (stay_arrivals EE lv es) <= t)%N.
Proof.
  intros Hloop Hops Hchecked Hcompile Htest Hmember Hlookup s0 es s Hinitial Hrun.
  pose proof (base_laws (l_ssa m EN EV inventory so lv Hloop)) as Hview.
  assert (Hproperty :
    (fun u prefix => run_edges m (base (lssa lv)) s0 prefix u /\
      (lbody lv (point (base (lssa lv)) u) = true -> forall inv t,
        (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so u y) ->
        scev_normalized_trip inv (width_of so) (t_sign tst) (t_cmp tst) ch (t_bound tst) t ->
          (N.of_nat (stay_arrivals EE lv prefix) <= t)%N)) s es).
  { change ((fun u prefix => run_edges m (base (lssa lv)) s0 prefix u /\
      (lbody lv (point (base (lssa lv)) u) = true -> forall inv t,
        (forall y, lbody lv (home (lssa lv) y) = false -> inv y = inv_env lv so u y) ->
        scev_normalized_trip inv (width_of so) (t_sign tst) (t_cmp tst) ch (t_bound tst) t ->
          (N.of_nat (stay_arrivals EE lv prefix) <= t)%N)) s ([] ++ es)).
    eapply scev_run_edges_invariant; [| |exact Hrun| |].
    - intros u tr v e prefix Hreachable [Hprefix Hbound] Hstep Htaken; split.
      + eapply run_edges_app; [exact Hprefix|].
        eapply run_cons; [exact Hstep|exact Htaken|constructor].
      + intros Hinside' inv t Hinv Htrip.
        destruct (scev_key_eq EE e (lentry lv)) eqn:Hentry.
        * apply scev_key_eq_spec in Hentry; subst e; rewrite scev_arrivals_entry; apply N.le_0_l.
        * assert (Hnotentry : e <> lentry lv).
          { intro Heq; pose proof (proj2 (scev_key_eq_spec EE _ _) Heq); congruence. }
          destruct (scev_key_eq EE e (lback lv)) eqn:Hback.
          -- apply scev_key_eq_spec in Hback; subst e.
             eapply (scev_back_trip_bound_step m EN EE EV inventory so lv p lookup tst ch
               s0 prefix u tr v inv t); try eassumption.
             intros Hinside Hinv_source; exact (Hbound Hinside inv t Hinv_source Htrip).
          -- assert (Hnotback : e <> lback lv).
             { intro Heq; pose proof (proj2 (scev_key_eq_spec EE _ _) Heq); congruence. }
             destruct (scev_ordinary_edge_inside m EN EV inventory so lv Hloop u tr v e
               Hreachable Hstep Htaken Hnotentry Hnotback Hinside') as [Hinside Htarget].
             rewrite (scev_arrivals_header_suffix m EN EE EV inventory so lv prefix [e] Hloop)
               by (constructor; [exact Htarget|constructor]).
             apply (Hbound Hinside inv t); [|exact Htrip].
             eapply scev_body_step_environment; eassumption.
    - intros u tr v prefix Hreachable [Hprefix Hbound] Hstep Hstay; split.
      + rewrite <- (app_nil_r prefix); eapply run_edges_app; [exact Hprefix|].
        eapply run_stay; [exact Hstep|exact Hstay|constructor].
      + intros Hinside' inv t Hinv Htrip.
        assert (Hinside : lbody lv (point (base (lssa lv)) u) = true).
        { rewrite <- (stays_point Hview u tr v Hreachable Hstep Hstay); exact Hinside'. }
        apply (Hbound Hinside inv t); [|exact Htrip].
        eapply scev_body_step_environment; eassumption.
    - exists s0, []; split; [exact Hinitial|constructor].
    - split; [constructor|]; intro Hinside.
      pose proof (entry_points Hview s0 Hinitial) as Hentry.
      pose proof (l_initial_outside m EN EV inventory so lv Hloop _ Hentry); congruence. }
  exact (proj2 Hproperty).
Qed.

(** Exact normalized trip counts bound header arrivals in every actual stay, including re-entry. *)
Theorem loop_trip_sound {S O Node E V K C} (m : semantics S O)
    (EN : encoding Node) (EE : encoding E) (EV : encoding V) (inventory : list V)
    (lv : loop_view S O Node E V K C) (so : scev_ops K C)
    (tst : loop_test V) (ch : chrec V) (t : N) :
  loop_view_laws m EN EV inventory so lv ->
  scev_ops_laws so (op_eval (lssa lv)) -> ltest lv = Some tst ->
  recognise EN EV inventory lv so (t_lhs tst) = Some ch ->
  forall s0 es s, initial m s0 -> run_edges m (base (lssa lv)) s0 es s ->
    point (base (lssa lv)) s = lheader lv ->
    trip_count (signed_inv_env lv so (t_sign tst) s) (width_of so) (t_sign tst) (t_cmp tst)
      (signed_chrec (width_of so) (t_sign tst) ch)
      (signed_iexpr (width_of so) (t_sign tst) (t_bound tst)) = Some t ->
    nowrap_check (width_of so) (t_sign tst) (signed_inv_env lv so (t_sign tst) s)
      (signed_chrec (width_of so) (t_sign tst) ch)
      (signed_iexpr (width_of so) (t_sign tst) (t_bound tst)) t = true ->
    (N.of_nat (stay_arrivals EE lv es) <= t)%N.
Proof.
  intros Hloop Hops Htest Hrecognise; unfold recognise in Hrecognise.
  destruct (recognise_plan EN EV inventory lv so (t_lhs tst)) as [[found p]|] eqn:Hplan;
    [|discriminate].
  inversion Hrecognise; subst found.
  destruct (recognise_plan_checked EN EV inventory lv so (t_lhs tst) ch p Hplan)
    as [Htarget [Hchecked Hcompiled]].
  destruct (scev_checked_compilation_equations EN EV inventory lv so p ch Hchecked Hcompiled)
    as [lookup [Hlookup Hequations]].
  assert (Hcompile : scev_compilation_equations p lookup).
  { intros b c Hb Hc; destruct (Hequations b Hb) as [own [Hown Htranslation]].
    assert (own = c) by congruence; subst own; exact Htranslation. }
  pose proof (scev_plan_check_sound EN EV inventory lv so p Hchecked) as Hvalid.
  assert (Hmember : In (t_lhs tst) (map sb_phi (sp_bindings p))).
  { destruct (spv_last _ _ _ _ Hvalid) as [prefix [b [Hbindings Hphi]]].
    rewrite <- Htarget, <- Hphi, Hbindings, map_app; apply in_app_iff; right; left; reflexivity. }
  rewrite Htarget in Hlookup.
  intros s0 es s Hinitial Hrun Hheader Htrip Hnowrap.
  eapply (scev_plan_trip_bound m EN EE EV inventory so lv p lookup tst ch Hloop Hops Hchecked
    Hcompile Htest Hmember Hlookup s0 es s Hinitial Hrun).
  - rewrite Hheader; exact (l_header_inside m EN EV inventory so lv Hloop).
  - intros y Hy; reflexivity.
  - exact Htrip.
Qed.

(** Every operation named by a valid expression belongs to the finite source inventory. *)
Lemma scev_expression_operations_inventory {S O N E V K C} inventory
    (lv : loop_view S O N E V K C) (so : scev_ops K C) bs rank e :
  scev_expression_valid inventory lv so bs rank e ->
  forall x, In x (scev_expr_operations e) -> In x inventory.
Proof.
  intro Hvalid; induction Hvalid; intros y Hy; cbn [scev_expr_operations] in Hy;
    try contradiction.
  - destruct Hy as [Heq|Hy]; [subst y; assumption|].
    apply in_app_iff in Hy; destruct Hy; [apply IHHvalid1|apply IHHvalid2]; assumption.
  - destruct Hy as [Heq|Hy]; [subst y; assumption|].
    apply in_app_iff in Hy; destruct Hy; [apply IHHvalid1|apply IHHvalid2]; assumption.
  - destruct Hy as [Heq|Hbad]; [subst y; assumption|contradiction].
Qed.

(** Every checked plan operation is a member of the prepared finite source inventory. *)
Theorem scev_plan_operations_inventory {S O N E V K C} (EN : encoding N) (EV : encoding V)
    inventory (lv : loop_view S O N E V K C) (so : scev_ops K C) p :
  scev_plan_check EN EV inventory lv so p = true ->
  forall x, In x (scev_plan_operations p) -> In x inventory.
Proof.
  intro Hchecked; pose proof (scev_plan_check_sound EN EV inventory lv so p Hchecked) as Hvalid.
  intros x Hin; unfold scev_plan_operations in Hin; apply in_flat_map in Hin.
  destruct Hin as [b [Hb [Heq|Hother]]].
  - subst x; destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb)
      as [rank [[_ [_ [Hin Hrest]]] Hupdate]]; exact Hin.
  - destruct (scev_plan_binding_rank inventory lv so p b Hvalid Hb) as [rank [_ Hupdate]].
    destruct b as [phi base update kind other first]; destruct kind;
      destruct other as [e|]; cbn [scev_update_valid sb_kind sb_other] in Hupdate;
      cbn [sb_other] in Hother; try contradiction.
    + eapply scev_expression_operations_inventory; [exact (proj2 Hupdate)|exact Hother].
    + eapply scev_expression_operations_inventory; [exact (proj2 Hupdate)|exact Hother].
Qed.
