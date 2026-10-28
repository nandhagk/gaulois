(** * Reduced products

    Reduction refines product comparisons and joins while widening keeps the original product step.
    For example, identity reduction gives the ordinary product operations.
    Builds on: OrderLattice, OrderConcrete and OrderProduct. *)

From Stdlib Require Import Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderProduct.

(** A reduction descends, preserves order and is idempotent up to the preorder. *)
Record reduction_laws {A B} (LA : lattice A) (LB : lattice B)
  (reduce : A * B -> A * B) : Prop := {
  reduce_lower : forall x, leb (product_lattice LA LB) (reduce x) x = true;
  reduce_monotone : forall x y, leb (product_lattice LA LB) x y = true ->
    leb (product_lattice LA LB) (reduce x) (reduce y) = true;
  reduce_idempotent : forall x,
    leb (product_lattice LA LB) (reduce x) (reduce (reduce x)) = true
}.

(** Sound reduction retains every concrete value of the original pair. *)
Record reduction_sound {A B C} (GA : concretisation A C) (GB : concretisation B C)
  (reduce : A * B -> A * B) : Prop := {
  reduce_gamma : forall x c, gamma (product_gamma GA GB) x c ->
    gamma (product_gamma GA GB) (reduce x) c
}.

Arguments reduce_lower {A B LA LB reduce}.
Arguments reduce_monotone {A B LA LB reduce}.
Arguments reduce_idempotent {A B LA LB reduce}.
Arguments reduce_gamma {A B C GA GB reduce}.

(** Reduced comparison normalises its left input; widening deliberately skips reduction. *)
Definition reduced_lattice {A B} (LA : lattice A) (LB : lattice B)
  (reduce : A * B -> A * B) : lattice (A * B) :=
  let P := product_lattice LA LB in
  {| leb := fun x y => leb P (reduce x) y;
     bot := bot P;
     join := fun x y => reduce (join P x y);
     widen := widen P;
     narrow := fun x y => narrow P x (reduce y) |}.

(** The pair of original tops also bounds every reduced left operand. *)
Definition reduced_top {A B} {LA : lattice A} {LB : lattice B}
  (reduce : A * B -> A * B) (TA : top LA) (TB : top LB) :
  top (reduced_lattice LA LB reduce).
Proof.
  refine {| top_value := (top_value TA, top_value TB) |}.
  abstract (intro x; exact (top_greatest (product_top TA TB) (reduce x))).
Defined.

Section ReducedLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (GA : concretisation A C)
  (GB : concretisation B C) (reduce : A * B -> A * B) (TA : top LA) (TB : top LB).
Variables (x : A * B) (c : C).

(** Descending monotone idempotent reduction yields a weak lattice. *)
Theorem reduced_laws : lattice_laws LA -> lattice_laws LB -> reduction_laws LA LB reduce ->
  lattice_laws (reduced_lattice LA LB reduce).
Proof.
  intros lawsA lawsB Hred.
  pose proof (product_laws LA LB lawsA lawsB) as lawsP.
  constructor.
  - exact (reduce_lower Hred).
  - intros a b d Hab Hbd.
    eapply (leb_trans lawsP); [apply (reduce_idempotent Hred a) |].
    eapply (leb_trans lawsP); [apply (reduce_monotone Hred _ _ Hab) | exact Hbd].
  - intro a; eapply (leb_trans lawsP); [apply (reduce_lower Hred) | apply (bot_least lawsP)].
  - intros a b; apply (reduce_monotone Hred); apply (join_upper_l lawsP).
  - intros a b; apply (reduce_monotone Hred); apply (join_upper_r lawsP).
  - intros a b; eapply (leb_trans lawsP);
      [apply (reduce_lower Hred) | apply (widen_upper_l lawsP)].
  - intros a b; eapply (leb_trans lawsP);
      [apply (reduce_lower Hred) | apply (widen_upper_r lawsP)].
  - intros a b Hab; eapply (leb_trans lawsP).
    + apply (reduce_lower Hred).
    + apply (narrow_lower lawsP _ _ Hab).
  - intros a b Hab; apply (narrow_upper lawsP _ _ Hab).
Qed.

(** Sound reduction makes reduced comparison preserve concretisation. *)
Theorem reduced_gamma_laws : lattice_laws LA -> lattice_laws LB ->
  concretisation_laws LA GA -> concretisation_laws LB GB ->
  reduction_laws LA LB reduce -> reduction_sound GA GB reduce ->
  concretisation_laws (reduced_lattice LA LB reduce) (product_gamma GA GB).
Proof.
  intros _ _ HGA HGB _ Hsound; constructor; intros a b d Hab Hd.
  eapply (gamma_monotone (product_gamma_laws LA LB GA GB HGA HGB));
    [exact Hab | apply (reduce_gamma Hsound); exact Hd].
Qed.

(** A descending sound reduction preserves the exact product meaning. *)
Theorem reduce_gamma_exact : lattice_laws LA -> lattice_laws LB ->
  concretisation_laws LA GA -> concretisation_laws LB GB ->
  reduction_laws LA LB reduce -> reduction_sound GA GB reduce ->
  (gamma (product_gamma GA GB) (reduce x) c <-> gamma (product_gamma GA GB) x c).
Proof.
  intros _ _ HGA HGB Hred Hsound; split.
  - apply (gamma_monotone (product_gamma_laws LA LB GA GB HGA HGB) _ _ c
      (reduce_lower Hred x)).
  - apply (reduce_gamma Hsound).
Qed.

(** Component full tops give a full reduced top. *)
Theorem reduced_top_full : top_full TA GA -> top_full TB GB ->
  top_full (@reduced_top A B LA LB reduce TA TB) (product_gamma GA GB).
Proof.
  intros HtopA HtopB; constructor; intro d; split;
    [apply (gamma_top_full HtopA) | apply (gamma_top_full HtopB)].
Qed.
End ReducedLaws.

(** Product widening ranks remain valid because widening never invokes reduction. *)
Definition reduced_wrank {A B} {LA : lattice A} {LB : lattice B}
  (reduce : A * B -> A * B) (lawsA : lattice_laws LA) (lawsB : lattice_laws LB)
  (Hred : reduction_laws LA LB reduce)
  (WA : bounded_widening_rank LA) (WB : bounded_widening_rank LB) :
  bounded_widening_rank (reduced_lattice LA LB reduce).
Proof.
  pose (W := product_wrank WA WB).
  pose proof (product_laws LA LB lawsA lawsB) as lawsP.
  unshelve refine (@BoundedWideningRank _ (reduced_lattice LA LB reduce)
    (@WideningRank _ (reduced_lattice LA LB reduce) (wrank (base_wrank W)) _ _)
    (wbound W) _).
  - abstract (intros a b _; apply (widening_rank_nonincreasing (base_wrank W))).
  - abstract (intros a b Hstrict; apply (widen_rank_progress (base_wrank W));
      destruct (leb (product_lattice LA LB) b a) eqn:Hba; [| reflexivity];
      assert (Hreduced : leb (product_lattice LA LB) (reduce b) a = true) by
        (eapply (leb_trans lawsP); [apply (reduce_lower Hred) | exact Hba]);
      change (leb (product_lattice LA LB) (reduce b) a = false) in Hstrict;
      rewrite Hreduced in Hstrict; discriminate).
  - abstract (apply (wrank_bounded W)).
Defined.
