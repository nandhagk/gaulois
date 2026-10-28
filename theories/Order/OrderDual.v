(** * Dual order

    Reversing an order exchanges top with bottom and meet with join.
    For example, boolean conjunction becomes the join in the reverse boolean order.
    Builds on: OrderLattice. *)

From Gaulois.Order Require Import OrderLattice.

(** Dual comparison reverses the original comparison and uses meet for join and widening. *)
Definition dual_lattice {A} (L : lattice A) (T : top L) (meet : A -> A -> A) : lattice A :=
  {| leb := fun a b => leb L b a;
     bot := top_value T;
     join := meet;
     widen := meet;
     narrow := fun a _ => a |}.

(** The original bottom is greatest in the dual order. *)
Definition dual_top {A} {L : lattice A} (T : top L) (meet : A -> A -> A)
  (laws : lattice_laws L) : top (dual_lattice L T meet).
Proof.
  refine {| top_value := bot L |}; abstract (intro a; apply (bot_least laws)).
Defined.

(** A supplied descending-chain rank gives the dual a monotone height. *)
Definition dual_height {A} {L : lattice A} (T : top L) (meet : A -> A -> A)
  (rank : A -> nat) (bound : nat) (rank_le : forall a, rank a <= bound)
  (rank_anti : forall a b, leb L b a = true -> rank a <= rank b)
  (meet_grows : forall a b, leb L a (meet a b) = false -> rank a < rank (meet a b)) :
  monotone_height (dual_lattice L T meet) :=
  @MonotoneHeight A (dual_lattice L T meet)
    (@Height A (dual_lattice L T meet) rank bound rank_le meet_grows) rank_anti.

Section DualLaws.
Context {A : Type} (L : lattice A) (T : top L) (meet : A -> A -> A).

(** A greatest lower bound yields the weak lattice laws for the dual. *)
Theorem dual_laws : lattice_laws L -> meet_laws L meet ->
  lattice_laws (dual_lattice L T meet).
Proof.
  intros laws Hmeet; constructor; cbn.
  - apply (leb_refl laws).
  - intros a b c Hab Hbc; eapply (leb_trans laws); eassumption.
  - apply (top_greatest T).
  - apply (meet_lower_l Hmeet).
  - apply (meet_lower_r Hmeet).
  - apply (meet_lower_l Hmeet).
  - apply (meet_lower_r Hmeet).
  - intros a b _; apply (leb_refl laws).
  - intros a b Hab; exact Hab.
Qed.

(** Greatest lower bounds become least upper bounds in the dual. *)
Theorem dual_lub : lattice_laws L -> meet_laws L meet -> lub_laws (dual_lattice L T meet).
Proof.
  intros _ Hmeet; constructor; apply (meet_greatest Hmeet).
Qed.
End DualLaws.
