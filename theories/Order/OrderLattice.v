(** * Lattice dictionaries

    Explicit operations and separate laws describe abstract values and their termination measures.
    For example, a height bounds the number of strict join steps.
    Builds on: Stdlib arithmetic and booleans. *)

From Stdlib Require Import Bool Arith Lia.

(** A lattice dictionary contains operations, without assuming any laws. *)
Record lattice (A : Type) : Type := Lattice {
  leb : A -> A -> bool;
  bot : A;
  join : A -> A -> A;
  widen : A -> A -> A;
  narrow : A -> A -> A
}.

Arguments leb {A}.
Arguments bot {A}.
Arguments join {A}.
Arguments widen {A}.
Arguments narrow {A}.

(** The weak laws give a preorder, bottom, upper bounds and bounded narrowing. *)
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

(** Least upper bounds are a separate optional law. *)
Record lub_laws {A} (L : lattice A) : Prop := {
  join_least : forall a b c, leb L a c = true -> leb L b c = true -> leb L (join L a b) c = true
}.

(** A top bounds every abstract value. *)
Record top {A} (L : lattice A) : Type := Top {
  top_value : A;
  top_greatest : forall a, leb L a top_value = true
}.

(** A bounded rank grows at every strict join step. *)
Record height {A} (L : lattice A) : Type := Height {
  rank : A -> nat;
  bound : nat;
  rank_bounded : forall a, rank a <= bound;
  join_rank_grows : forall a b, leb L (join L a b) a = false -> rank a < rank (join L a b)
}.

(** A widening rank decreases whenever the new argument escapes the old one. *)
Record widening_rank {A} (L : lattice A) : Type := WideningRank {
  wrank : A -> nat;
  widen_rank_stable : forall a b, leb L b a = true -> wrank (widen L a b) <= wrank a;
  widen_rank_progress : forall a b, leb L b a = false -> wrank (widen L a b) < wrank a
}.

Arguments top_value {A L}.
Arguments top_greatest {A L}.
Arguments rank {A L}.
Arguments bound {A L}.
Arguments rank_bounded {A L}.
Arguments join_rank_grows {A L}.
Arguments wrank {A L}.
Arguments widen_rank_stable {A L}.
Arguments widen_rank_progress {A L}.
Arguments leb_refl {A L}.
Arguments leb_trans {A L}.
Arguments bot_least {A L}.
Arguments join_upper_l {A L}.
Arguments join_upper_r {A L}.
Arguments widen_upper_l {A L}.
Arguments widen_upper_r {A L}.
Arguments narrow_lower {A L}.
Arguments narrow_upper {A L}.
Arguments join_least {A L}.

(** A boolean equality reflects equality of carrier values. *)
Definition eqb_spec {A} (eqb : A -> A -> bool) : Prop :=
  forall a b, eqb a b = true <-> a = b.

(** Equivalent values bound each other in the preorder. *)
Definition equivalent {A} (L : lattice A) (a b : A) : Prop :=
  leb L a b = true /\ leb L b a = true.

(** A meet is a greatest lower bound. *)
Record meet_laws {A} (L : lattice A) (meet : A -> A -> A) : Prop := {
  meet_lower_l : forall a b, leb L (meet a b) a = true;
  meet_lower_r : forall a b, leb L (meet a b) b = true;
  meet_greatest : forall a b c, leb L c a = true -> leb L c b = true -> leb L c (meet a b) = true
}.

Arguments meet_lower_l {A L meet}.
Arguments meet_lower_r {A L meet}.
Arguments meet_greatest {A L meet}.

(** A monotone height also preserves the preorder in its ranks. *)
Record monotone_height {A} (L : lattice A) : Type := MonotoneHeight {
  base_height : height L;
  rank_monotone : forall a b, leb L a b = true -> rank base_height a <= rank base_height b
}.

(** A bounded widening rank has one uniform upper bound. *)
Record bounded_widening_rank {A} (L : lattice A) : Type := BoundedWideningRank {
  base_wrank : widening_rank L;
  wbound : nat;
  wrank_bounded : forall a, wrank base_wrank a <= wbound
}.

Arguments base_height {A L}.
Arguments rank_monotone {A L}.
Arguments base_wrank {A L}.
Arguments wbound {A L}.
Arguments wrank_bounded {A L}.

Section CoreLaws.
Context {A : Type} (L : lattice A).
Variables (a a' b b' : A).

(** A least upper bound is monotone in both arguments. *)
Theorem join_monotone : lattice_laws L -> lub_laws L ->
  leb L a a' = true -> leb L b b' = true ->
  leb L (join L a b) (join L a' b') = true.
Proof.
  intros laws lub Ha Hb.
  apply (join_least lub).
  - eapply (leb_trans laws); [exact Ha | apply (join_upper_l laws)].
  - eapply (leb_trans laws); [exact Hb | apply (join_upper_r laws)].
Qed.

(** Joining bottom changes a value only up to preorder equivalence. *)
Theorem join_bot_equivalent : lattice_laws L -> lub_laws L ->
  equivalent L (join L (bot L) a) a.
Proof.
  intros laws lub; split.
  - apply (join_least lub); [apply (bot_least laws) | apply (leb_refl laws)].
  - apply (join_upper_r laws).
Qed.
End CoreLaws.

(** Complementing a monotone height gives a bounded rank when widening is join. *)
Definition height_wrank {A} (L : lattice A) (laws : lattice_laws L)
  (Hw : forall a b, widen L a b = join L a b) (H : monotone_height L) :
  bounded_widening_rank L.
Proof.
  unshelve refine (@BoundedWideningRank A L
    (@WideningRank A L (fun a => bound (base_height H) - rank (base_height H) a) _ _)
    (bound (base_height H)) _).
  - abstract (intros a b _; rewrite Hw;
      pose proof (rank_monotone H _ _ (join_upper_l laws a b)) as Hgrow; lia).
  - abstract (intros a b Hba; rewrite Hw;
      assert (Hstrict : leb L (join L a b) a = false) by
        (destruct (leb L (join L a b) a) eqn:Hjoin; [| reflexivity];
         pose proof (leb_trans laws _ _ _ (join_upper_r laws a b) Hjoin) as Hcontra;
         rewrite Hba in Hcontra; discriminate);
      pose proof (join_rank_grows (base_height H) a b Hstrict) as Hgrow;
      pose proof (rank_bounded (base_height H) (join L a b)) as Hbound; lia).
  - abstract (intro a; cbn; lia).
Defined.
