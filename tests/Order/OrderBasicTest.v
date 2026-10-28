(** * Basic order examples

    Computed examples distinguish bottom, top, equality and componentwise behavior.
    For example, distinct flat constants join to top rather than choosing either constant.
    Builds on: Order's basic combinators and Stdlib booleans and naturals. *)

From Stdlib Require Import Bool Arith.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderMonotone OrderFlat
  OrderLift OrderProduct OrderReduced OrderDual OrderBasic.

Example flat_equal_join : join (flat_lattice Nat.eqb) (FVal 2) (FVal 2) = FVal 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_unequal_join : join (flat_lattice Nat.eqb) (FVal 2) (FVal 3) = FTop.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_bottom_join : join (flat_lattice Nat.eqb) FBot (FVal 3) = FVal 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_top_join : join (flat_lattice Nat.eqb) (FVal 3) FTop = FTop.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_order_rejects_distinct : leb (flat_lattice Nat.eqb) (FVal 2) (FVal 3) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_order_rejects_top_below_value : leb (flat_lattice Nat.eqb) FTop (FVal 2) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_height_levels :
  rank (base_height (flat_height Nat.eqb Nat.eqb_eq)) (FVal 3) = 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_bottom_neutral :
  join (lift_bot_lattice bool_lattice) Unreached (Reached false) = Reached false.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_bottom_distinct : leb (option_lattice bool_lattice) (Some false) None = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example option_widen_values :
  widen (option_lattice bool_lattice) (Some false) (Some true) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example option_narrow_bottom : narrow (option_lattice bool_lattice) (Some true) None = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example option_height_boundary :
  rank (base_height (option_height bool_laws bool_height)) (Some false) = 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example option_wrank_boundary :
  wrank (base_wrank (option_wrank
    (height_wrank bool_lattice bool_laws (fun _ _ => eq_refl) bool_height))) None = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_top_absorbs : join (lift_top_lattice bool_lattice) (Elem false) Unknown = Unknown.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_top_narrow_descends :
  narrow (lift_top_lattice bool_lattice) Unknown (Elem false) = Elem false.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_top_order_rejects : leb (lift_top_lattice bool_lattice) Unknown (Elem true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example fresh_top_height_boundary :
  rank (base_height (lift_top_height bool_height)) Unknown = 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_join_coordinates :
  join (product_lattice (flat_lattice Nat.eqb) bool_lattice)
    (FVal 1, false) (FVal 2, true) = (FTop, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example product_order_checks_both :
  leb (product_lattice bool_lattice bool_lattice) (true, false) (false, true) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example product_height_sums :
  rank (base_height (product_height bool_laws bool_laws bool_height bool_height))
    (true, true) = 2.
Proof.
  vm_compute; reflexivity.
Qed.

(** This concrete reduction makes both coordinates carry their conjunction. *)
Definition test_reduce (x : bool * bool) : bool * bool :=
  (andb (fst x) (snd x), andb (fst x) (snd x)).

Example test_reduce_laws : reduction_laws bool_lattice bool_lattice test_reduce.
Proof.
  constructor.
  - intros [[] []]; vm_compute; reflexivity.
  - intros [[] []] [[] []]; vm_compute; congruence.
  - intros [[] []]; vm_compute; reflexivity.
Qed.

Example reduced_comparison_uses_reduction :
  leb (reduced_lattice bool_lattice bool_lattice test_reduce) (true, false) (false, false) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_join_uses_reduction :
  join (reduced_lattice bool_lattice bool_lattice test_reduce)
    (true, false) (false, false) = (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_widen_skips_reduction :
  widen (reduced_lattice bool_lattice bool_lattice test_reduce)
    (true, false) (false, false) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** Conjunction narrowing exposes the reduced second argument in a computed result. *)
Definition test_meet_lattice : lattice bool :=
  {| leb := implb;
     bot := false;
     join := orb;
     widen := orb;
     narrow := andb |}.

Example reduced_narrow_reduces_second :
  narrow (reduced_lattice test_meet_lattice test_meet_lattice test_reduce)
    (true, true) (true, false) = (false, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example reduced_wrank_keeps_product_rank :
  wrank (base_wrank (reduced_wrank test_reduce bool_laws bool_laws test_reduce_laws
    (height_wrank bool_lattice bool_laws (fun _ _ => eq_refl) bool_height)
    (height_wrank bool_lattice bool_laws (fun _ _ => eq_refl) bool_height)))
    (true, false) = 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_order_reverses :
  leb (dual_lattice bool_lattice bool_top andb) true false = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example dual_join_is_meet : join (dual_lattice bool_lattice bool_top andb) true false = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example bool_join_live : join bool_lattice false true = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example bool_order_rejects_live_below_dead : leb bool_lattice true false = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example bool_narrow_keeps_first : narrow bool_lattice true false = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example unit_join_unique : join unit_lattice tt tt = tt.
Proof.
  vm_compute; reflexivity.
Qed.

Example unit_order_accepts : leb unit_lattice tt tt = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example flat_bottom_meaning_empty :
  gamma (flat_gamma (fun a c : nat => a = c)) FBot 3 <-> False.
Proof.
  vm_compute; tauto.
Qed.

Example top_meaning_full : gamma (lift_top_gamma (flat_gamma (fun a c : nat => a = c))) Unknown 3.
Proof.
  vm_compute; exact I.
Qed.

Example dead_agreement_unrestricted : agree (@bool_agree nat) false 2 3.
Proof.
  vm_compute; discriminate.
Qed.

Example live_agreement_rejects_distinct : ~ agree (@bool_agree nat) true 2 3.
Proof.
  vm_compute; intros Hxy; discriminate (Hxy eq_refl).
Qed.

Example pulled_back_meaning :
  gamma (comap_gamma (fun b : bool => if b then 1 else 0)
    {| gamma := fun a c : nat => a = c |}) true 1.
Proof.
  vm_compute; reflexivity.
Qed.

Example pointwise_assignment_order :
  fun_leb bool_lattice (fun _ : nat => false) (fun _ => true).
Proof.
  intro x; vm_compute; reflexivity.
Qed.
