(** * Numeric-domain boundary examples

    Computed examples exercise tags, caps, constant inverses, and sign refinements.
    For example, an eight-bit extension beyond an eight-bit cap becomes unrestricted top.
    Builds on: DomainsNumeric, DomainsConst and DomainsSign. *)

From Stdlib Require Import ZArith List.
From Gaulois.Order Require Import OrderLattice OrderFlat.
From Gaulois.Bits Require Import BitsWord BitsOp BitsExpr.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst DomainsSign.
Import List.ListNotations Bits.

Open Scope Z_scope.

Definition constants := tagged_domain const_domain.
Definition signs := tagged_domain sign_domain.

Definition w1 : width := 1%positive.
Definition w8 : width := 8%positive.
Definition w16 : width := 16%positive.

Example constant_add_wrap :
  forward constants bvadd [of_const constants w8 250; of_const constants w8 10] =
    TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example constant_annihilators :
  [forward constants bvmul [of_const constants w8 0; top_at constants w8];
   forward constants bvand [top_at constants w8; of_const constants w8 0];
   forward constants bvor [top_at constants w8; of_const constants w8 255];
   forward constants bvshl [of_const constants w8 0; top_at constants w8];
   forward constants bvlshr [of_const constants w8 0; top_at constants w8];
   forward constants bvashr [of_const constants w8 0; top_at constants w8];
   forward constants bvurem [of_const constants w8 0; top_at constants w8]] =
  [TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 255); TVal w8 (FVal 0);
   TVal w8 (FVal 0); TVal w8 (FVal 0); TVal w8 (FVal 0)].
Proof.
  vm_compute. reflexivity.
Qed.

Example tagged_payload_bottom :
  forward constants bvadd [TVal w8 FBot; TAny] = TBot /\
  meet constants (TVal w8 FBot) TAny = TBot.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example incompatible_widths :
  join (lat constants) (TVal w8 (FVal 0)) (TVal w16 (FVal 0)) = TAny /\
  forward constants bvadd [TVal w8 (FVal 0); TVal w16 (FVal 0)] = TBot /\
  assume constants bvadd (TVal w8 (FVal 0)) [TVal w8 FTop; TVal w16 FTop] = [TBot; TBot].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example inverse_add :
  assume constants bvadd (TVal w8 (FVal 7)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 4); TVal w8 (FVal 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example inverse_subtract_and_xor :
  assume constants bvsub (TVal w8 (FVal 250)) [TVal w8 (FVal 3); TVal w8 FTop] =
    [TVal w8 (FVal 3); TVal w8 (FVal 9)] /\
  assume constants bvxor (TVal w8 (FVal 5)) [TVal w8 FTop; TVal w8 (FVal 3)] =
    [TVal w8 (FVal 6); TVal w8 (FVal 3)].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example inverse_unary_and_equality :
  assume constants bvnot (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 5)] /\
  assume constants bvneg (TVal w8 (FVal 250)) [TVal w8 FTop] = [TVal w8 (FVal 6)] /\
  assume constants bveq (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 (FVal 42)] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)] /\
  assume constants bvne (TVal w1 (FVal 0)) [TVal w8 (FVal 42); TVal w8 FTop] =
    [TVal w8 (FVal 42); TVal w8 (FVal 42)].
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example nested_expression_refinement :
  abs_assume constants (fun _ => top_at constants w8)
    (App bvadd [Var 0; Const w8 3]) (TVal w8 (FVal 7)) 0%nat = TVal w8 (FVal 4).
Proof.
  vm_compute. reflexivity.
Qed.

Example cap_excessive_widths :
  proj1_sig (top_at (capped_domain const_domain w8) w16) = TAny /\
  proj1_sig (forward (capped_domain const_domain w8) (bvzext w8)
    [of_const (capped_domain const_domain w8) w8 255]) = TAny /\
  proj1_sig (forward (capped_domain const_domain w8) bvconcat
    [of_const (capped_domain const_domain w8) w8 1;
     of_const (capped_domain const_domain w8) w8 2]) = TAny.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example cap_refinement_stays_within :
  map (@proj1_sig _ _) (assume (capped_domain const_domain w8) bvadd
    (of_const (capped_domain const_domain w8) w8 7)
    [top_at (capped_domain const_domain w8) w8;
     of_const (capped_domain const_domain w8) w8 3]) =
  [TVal w8 (FVal 4); TVal w8 (FVal 3)].
Proof.
  vm_compute. reflexivity.
Qed.

Example capped_height_payload_rank :
  rank (base_height (capped_height const_domain w8 (plat_laws const_word_laws)
    (fun _ => flat_height Z.eqb Z.eqb_eq))) (of_const (capped_domain const_domain w8) w8 42) =
  2%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example capped_widening_ranks :
  let W := fun _ : width =>
    height_wrank sign_lattice sign_laws (fun _ _ => eq_refl) sign_height in
  let R := base_wrank (capped_wrank sign_domain w8 W) in
  wrank R (clamp w8 TBot) = 5%nat /\
  wrank R (clamp w8 (TVal w8 (Sign true false false))) = 3%nat /\
  wrank R (clamp w8 TAny) = 0%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example one_bit_signed_boolean :
  of_const signs w1 1 = TVal w1 (Sign true false false) /\
  forward signs bveq [of_const signs w1 1; of_const signs w1 1] =
    TVal w1 (Sign true false false).
Proof.
  vm_compute. split; reflexivity.
Qed.

Example impossible_result_refines_every_operand :
  assume constants bvadd TBot [TAny; TVal w8 FTop] = [TBot; TBot] /\
  assume constants bvadd (TVal w1 (FVal 1)) [TVal w8 FTop; TVal w8 FTop] = [TBot; TBot].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example nested_abstract_evaluation :
  abs_eval constants (fun _ => of_const constants w8 5)
    (App bvadd [App bvmul [Var 0; Const w8 3]; Const w8 250]) = TVal w8 (FVal 9).
Proof.
  vm_compute. reflexivity.
Qed.

Example signed_comparison_decisions :
  forward signs bvslt [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w1 (Sign true false false) /\
  forward signs bvult [TVal w8 (Sign true false false); TVal w8 (Sign false true true)] =
    TVal w1 (Sign false true false) /\
  forward signs bveq [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w1 (Sign false true false).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_transfer_table :
  forward signs bvand [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w8 (Sign false true true) /\
  forward signs bvor [TVal w8 (Sign true false false); TVal w8 (Sign false false true)] =
    TVal w8 (Sign true false false) /\
  forward signs bvxor [TVal w8 (Sign true false false); TVal w8 (Sign true false false)] =
    TVal w8 (Sign false true true) /\
  forward signs bvnot [TVal w8 (Sign true false false)] = TVal w8 (Sign false true true) /\
  forward signs bvneg [of_const signs w8 128] = TVal w8 (Sign true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example sign_refinement :
  abs_assume signs (fun _ => TVal w8 (Sign false true true)) (Var 0)
    (TVal w8 (Sign true true false)) 0%nat = TVal w8 (Sign false true false).
Proof.
  vm_compute. reflexivity.
Qed.

Example sign_extensions :
  forward signs (bvzext w8) [TVal w8 (Sign true false false)] =
    TVal w16 (Sign false true true) /\
  forward signs (bvsext w8) [TVal w8 (Sign true false false)] =
    TVal w16 (Sign true false false) /\
  forward signs bvite [top_at signs w1; TVal w8 (Sign true false false);
    TVal w8 (Sign false false true)] = TVal w8 (Sign true false true).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.
