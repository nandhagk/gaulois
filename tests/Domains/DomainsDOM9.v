(** * Signed bit-and-bounds computations

    These examples distinguish exact reduction, hemisphere lifting and client boundaries.
    For example, the {0,4} mask inside [1,6] reduces to the singleton 4.
    Builds on: DomainsSignedBoundsDomain and the shared tagged and capped clients. *)

From Stdlib Require Import ZArith List Bool.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp.
From Gaulois.Domains Require Import
  DomainsNumeric DomainsKnownBits DomainsKnownBitsFast DomainsWrapped DomainsSignedBounds
  DomainsSignedBoundsDomain.
Import List.ListNotations.

Local Open Scope Z_scope.
Local Abbreviation w1 := 1%positive.
Local Abbreviation w2 := 2%positive.
Local Abbreviation w3 := 3%positive.
Local Abbreviation w4 := 4%positive.
Local Abbreviation w5 := 5%positive.

Definition dom9_const := pconst signed_bounds_domain.

Definition dom9_forward (w : width) (o : op) (xs : list signed_bounds) : signed_bounds :=
  pforward signed_bounds_domain o (map (fun a => (w, a)) xs) w.

Definition dom9_classic_forward (w : width) (o : op) (xs : list signed_bounds) :
    signed_bounds :=
  pforward signed_bounds_classic_domain o (map (fun a => (w, a)) xs) w.

Definition dom9_contains (w : width) (a : signed_bounds) (z : Z) : bool :=
  match if msb w z then sb_one a else sb_zero a with
  | SBEmpty => false
  | SBRange t lo hi =>
    (Z.land z (wrap w (zeros t)) =? 0) &&
      (Z.land (wrap w (ones t)) (Z.lnot z) =? 0) && (lo <=? z) && (z <=? hi)
  end.

Example dom9_width_one : signed_bounds_top w1 =
  SignedBounds (SBRange (Tnum 1 0) 0 0) (SBRange (Tnum 0 1) 1 1).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_non_power_width :
  signed_bounds_query w3 (signed_bounds_top w3) false = Some (Tnum 4 0, 0, 3) /\
  signed_bounds_query w3 (signed_bounds_top w3) true = Some (Tnum 0 4, 4, 7).
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_conflicting : sb_reduce_half w4 false (SBRange (Tnum 1 1) 0 15) = SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_raw_masks :
  sb_reduce_half w4 false (SBRange (Tnum 27 16) 1 6) = SBRange (Tnum 11 4) 4 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_inverted : sb_reduce_half w4 false (SBRange tnum_top 6 1) = SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_out_of_range :
  sb_reduce_half w4 false (SBRange tnum_top (-5) 20) = SBRange (Tnum 8 0) 0 7.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_outside_words :
  sb_reduce_half w3 true (SBRange tnum_top 8 15) = SBEmpty /\
  dom9_const w3 (-1) = dom9_const w3 7.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_wrong_hemisphere : sb_reduce_half w4 false (SBRange tnum_top 8 15) = SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_both_empty : signed_bounds_reduce w4
  (SignedBounds (SBRange tnum_top 8 15) (SBRange tnum_top 0 7)) =
  SignedBounds SBEmpty SBEmpty.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_exact_four :
  sb_reduce_half w4 false (SBRange (Tnum 11 0) 1 6) = SBRange (Tnum 11 4) 4 4.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_empty_queries :
  signed_bounds_query w4 (dom9_const w4 4) true = None /\
  signed_bounds_query w4 (SignedBounds SBEmpty SBEmpty) false = None /\
  signed_bounds_query w4 (SignedBounds SBEmpty SBEmpty) true = None.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Definition dom9_different_masks : signed_bounds :=
  SignedBounds (SBRange (Tnum 9 0) 0 7) (SBRange (Tnum 0 9) 8 15).

Example dom9_pair_query :
  signed_bounds_query w4 dom9_different_masks false = Some (Tnum 9 0, 0, 6) /\
  signed_bounds_query w4 dom9_different_masks true = Some (Tnum 0 9, 9, 15) /\
  signed w4 9 = -7 /\ signed w4 15 = -1.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_wrap_add :
  dom9_forward w4 bvadd [dom9_const w4 15; dom9_const w4 1] = dom9_const w4 0.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_sign_crossing :
  dom9_forward w4 bvadd [sb_lift w4 tnum_top 6 7; dom9_const w4 1] =
  SignedBounds (SBRange (Tnum 8 7) 7 7) (SBRange (Tnum 7 8) 8 8).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_zero_divisors :
  dom9_forward w4 bvudiv [dom9_const w4 7; dom9_const w4 0] = dom9_const w4 15 /\
  dom9_forward w4 bvsdiv [dom9_const w4 8; dom9_const w4 0] = dom9_const w4 1 /\
  dom9_forward w4 bvurem [dom9_const w4 7; dom9_const w4 0] = dom9_const w4 7 /\
  dom9_contains w4 (dom9_forward w4 bvsrem [dom9_const w4 9; dom9_const w4 0]) 9 = true /\
  dom9_contains w4 (dom9_forward w4 bvsmod [dom9_const w4 9; dom9_const w4 0]) 9 = true /\
  eval_op bvsrem [(w4, 9); (w4, 0)] = Some (w4, 9) /\
  eval_op bvsmod [(w4, 9); (w4, 0)] = Some (w4, 9).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_overshifts_and_rotation :
  dom9_forward w3 bvshl [dom9_const w3 1; dom9_const w3 7] = dom9_const w3 0 /\
  dom9_forward w3 bvlshr [dom9_const w3 4; dom9_const w3 7] = dom9_const w3 0 /\
  dom9_forward w3 bvashr [dom9_const w3 4; dom9_const w3 7] = dom9_const w3 7 /\
  dom9_forward w3 bvrotl [dom9_const w3 1; dom9_const w3 4] = dom9_const w3 2.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_width_changes :
  pforward signed_bounds_domain (bvzext w1) [(3%positive, dom9_const w3 7)] w4 =
    dom9_const w4 7 /\
  pforward signed_bounds_domain (bvsext w1) [(3%positive, dom9_const w3 7)] w4 =
    dom9_const w4 15 /\
  pforward signed_bounds_domain (bvtrunc w2) [(3%positive, dom9_const w3 7)] w2 =
    dom9_const w2 3 /\
  pforward signed_bounds_domain (bvextract 2 1) [(3%positive, dom9_const w3 7)] w2 =
    dom9_const w2 3 /\
  pforward signed_bounds_domain bvconcat
    [(3%positive, dom9_const w3 2); (2%positive, dom9_const w2 3)] w5 = dom9_const w5 11.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_all_eight_ite_branches :
  pforward signed_bounds_domain bvite
    [(1%positive, signed_bounds_top w1); (3%positive, sb_lift w3 (Tnum 3 0) 0 7);
     (3%positive, sb_lift w3 (Tnum 2 1) 0 7)] w3 =
  SignedBounds (SBRange (Tnum 6 0) 0 1) (SBRange (Tnum 2 4) 4 5).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_two_arc_pieces_one_sign :
  signed_bounds_query w4 (sb_from_components w4 tnum_top (WItv 6 3)) false =
  Some (Tnum 8 0, 0, 7).
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_full_arc_split : sb_from_components w3 tnum_top WFull = signed_bounds_top w3.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_guard_equality :
  passume signed_bounds_domain bveq
    [(4%positive, sb_lift w4 tnum_top 0 7); (4%positive, dom9_const w4 3)] w1 (dom9_const w1 1) =
  [dom9_const w4 3; dom9_const w4 3].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_guard_unsigned :
  passume signed_bounds_domain bvult
    [(4%positive, sb_lift w4 tnum_top 0 7); (4%positive, dom9_const w4 4)] w1 (dom9_const w1 1) =
  [sb_lift w4 tnum_top 0 3; dom9_const w4 4].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_guard_signed_crossing :
  passume signed_bounds_domain bvslt
    [(w4, signed_bounds_top w4); (w4, dom9_const w4 0)] w1 (dom9_const w1 1) =
  [sb_lift w4 tnum_top 8 15; dom9_const w4 0] /\
  passume signed_bounds_domain bvslt
    [(w1, signed_bounds_top w1); (w1, dom9_const w1 0)] w1 (dom9_const w1 1) =
  [dom9_const w1 1; dom9_const w1 0].
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_empty_guard : passume signed_bounds_domain bvadd
  [(3%positive, signed_bounds_top w3); (3%positive, signed_bounds_top w3)] w3
  (SignedBounds SBEmpty SBEmpty) =
  [SignedBounds SBEmpty SBEmpty; SignedBounds SBEmpty SBEmpty].
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_ite_backward_fallback :
  passume signed_bounds_domain bvite
    [(w1, signed_bounds_top w1); (w3, sb_lift w3 (Tnum 3 0) 0 7);
     (w3, sb_lift w3 (Tnum 2 1) 0 7)] w3 (dom9_const w3 4) =
  [signed_bounds_top w1; sb_lift w3 (Tnum 3 0) 0 7; sb_lift w3 (Tnum 2 1) 0 7] /\
  pmeet signed_bounds_domain w3 (dom9_const w3 0) (dom9_const w3 1) =
    SignedBounds SBEmpty SBEmpty.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_malformed_refinement :
  passume signed_bounds_domain bvadd
    [(3%positive, dom9_different_masks); (4%positive, dom9_different_masks)] w3
    (signed_bounds_top w3) =
  [signed_bounds_reduce w3 dom9_different_masks; signed_bounds_reduce w4 dom9_different_masks] /\
  length (passume signed_bounds_domain bvite
    [(3%positive, signed_bounds_top w3); (3%positive, signed_bounds_top w3);
     (3%positive, signed_bounds_top w3); (3%positive, signed_bounds_top w3)] w3
    (signed_bounds_top w3)) = 4%nat.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_tagged_and_capped :
  forward signed_bounds_numeric bvadd
    [TVal w3 (dom9_const w3 1); TVal w4 (dom9_const w4 1)] = TBot /\
  forward signed_bounds_numeric bvadd [TBot; TAny] = TBot /\
  forward signed_bounds_numeric bvadd [TAny; TVal w3 (dom9_const w3 1)] = TAny /\
  proj1_sig (forward (signed_bounds_capped w3) (bvzext w1)
    [of_const (signed_bounds_capped w3) w3 7]) = TAny /\
  proj1_sig (top_at (signed_bounds_capped w3) w4) = TAny.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_widening_progress :
  Nat.ltb (wrank (base_wrank (signed_bounds_wrank w3))
    (widen (signed_bounds_lattice w3) (dom9_const w3 0) (dom9_const w3 1)))
    (wrank (base_wrank (signed_bounds_wrank w3)) (dom9_const w3 0)) = true /\
  narrow (signed_bounds_lattice w3) dom9_different_masks (signed_bounds_top w3) =
    signed_bounds_reduce w3 dom9_different_masks.
Proof.
  vm_compute. split; reflexivity.
Qed.

Example dom9_raw_widening_progress :
  let raw := SignedBounds (SBRange (Tnum 27 16) 1 6) SBEmpty in
  wrank (base_wrank (signed_bounds_wrank w4)) raw =
    wrank (base_wrank (signed_bounds_wrank w4)) (dom9_const w4 4) /\
  Nat.ltb (wrank (base_wrank (signed_bounds_wrank w4))
    (widen (signed_bounds_lattice w4) raw (dom9_const w4 5)))
    (wrank (base_wrank (signed_bounds_wrank w4)) raw) = true.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** These operands represent exactly {1,3} and {3} in the positive five-bit hemisphere. *)
Definition dom9_mul_choices : signed_bounds := sb_lift w5 (Tnum 28 1) 1 3.

Example dom9_precise_multiplication :
  let precise := dom9_forward w5 bvmul [dom9_mul_choices; dom9_const w5 3] in
  let classic := dom9_classic_forward w5 bvmul [dom9_mul_choices; dom9_const w5 3] in
  signed_bounds_query w5 precise false = Some (Tnum 16 1, 3, 9) /\
  signed_bounds_query w5 precise true = None /\
  dom9_contains w5 precise 3 = true /\ dom9_contains w5 precise 9 = true /\
  dom9_contains w5 precise 4 = false /\ dom9_contains w5 classic 4 = true.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Both public word-law records justify containment of each concrete product. *)
Example dom9_both_multiplication_laws : forall x,
  signed_bounds_gamma w5 dom9_mul_choices x ->
  signed_bounds_gamma w5
    (dom9_forward w5 bvmul [dom9_mul_choices; dom9_const w5 3]) (wmul w5 x 3) /\
  signed_bounds_gamma w5
    (dom9_classic_forward w5 bvmul [dom9_mul_choices; dom9_const w5 3]) (wmul w5 x 3).
Proof.
  intros x Hx.
  assert (Hpayload : Forall2 (payload_sound signed_bounds_gamma)
    [(w5, dom9_mul_choices); (w5, dom9_const w5 3)] [(w5, x); (w5, 3)]).
  { constructor.
    - split; [reflexivity|]. split; [|exact Hx].
      destruct Hx as [Hx|Hx]; exact (proj1 (sb_half_word_sign w5 _ _ x Hx)).
    - constructor; [|constructor]. split; [reflexivity|]. split.
      + exact (wrap_is_word w5 3).
      + exact (pconst_sound signed_bounds_word_laws w5 3). }
  split.
  - exact (pforward_sound signed_bounds_word_laws bvmul _ _ w5 _ Hpayload
      (eval_op_fun2 bvmul w5 x 3 wmul eq_refl)).
  - exact (pforward_sound signed_bounds_classic_word_laws bvmul _ _ w5 _ Hpayload
      (eval_op_fun2 bvmul w5 x 3 wmul eq_refl)).
Qed.

Example dom9_both_multiplication_boundaries :
  let check := fun D =>
    pforward D bvmul [(w1, dom9_const w1 1); (w1, dom9_const w1 1)] w1 =
      dom9_const w1 1 /\
    pforward D bvmul [(w5, dom9_const w5 7); (w5, dom9_const w5 5)] w5 =
      dom9_const w5 3 /\
    pforward D bvmul [(w5, SignedBounds (SBRange (Tnum 1 1) 0 15) SBEmpty);
      (w5, dom9_const w5 3)] w5 = SignedBounds SBEmpty SBEmpty /\
    pforward D bvmul [(w5, dom9_const w5 0);
      (w5, SignedBounds SBEmpty (SBRange (Tnum 1 1) 16 31))] w5 =
      SignedBounds SBEmpty SBEmpty in
  check signed_bounds_domain /\ check signed_bounds_classic_domain.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_multiplication_fallbacks :
  let check := fun xs rw =>
    pforward signed_bounds_domain bvmul xs rw =
      pforward signed_bounds_classic_domain bvmul xs rw in
  check [] w5 /\ check [(w5, dom9_mul_choices)] w5 /\
  check [(w5, dom9_mul_choices); (w4, dom9_const w4 3)] w5 /\
  check [(w5, dom9_mul_choices); (w5, dom9_const w5 3)] w4 /\
  check [(w5, dom9_mul_choices); (w5, dom9_const w5 3); (w5, dom9_mul_choices)] w5 /\
  check [(w5, dom9_mul_choices); (w5, dom9_mul_choices);
    (w5, dom9_mul_choices); (w5, dom9_mul_choices)] w5.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Example dom9_shared_backward_and_lattice :
  passume signed_bounds_domain = passume signed_bounds_classic_domain /\
  plat signed_bounds_domain = plat signed_bounds_classic_domain /\
  pmeet signed_bounds_domain = pmeet signed_bounds_classic_domain /\
  pconst signed_bounds_domain = pconst signed_bounds_classic_domain /\
  ptop signed_bounds_domain = ptop signed_bounds_classic_domain.
Proof.
  repeat split; reflexivity.
Qed.

(** Every non-multiplication forward case agrees for arbitrary raw operands and result widths. *)
Example dom9_nonmultiplication_agrees : forall o wps rw, o <> bvmul ->
  pforward signed_bounds_domain o wps rw =
    pforward signed_bounds_classic_domain o wps rw.
Proof.
  intros o wps rw Hother.
  change (signed_bounds_forward known_bits_precise_domain o wps rw =
    signed_bounds_forward known_bits_domain o wps rw).
  unfold signed_bounds_forward. destruct (Nat.leb (length wps) 3); [|reflexivity].
  f_equal. apply map_ext. intro hs. unfold sb_case_forward.
  destruct o; try reflexivity. contradiction.
Qed.

Example dom9_multiplication_clients :
  let precise := SignedBounds (SBRange (Tnum 16 1) 3 9) SBEmpty in
  let classic := SignedBounds (SBRange (Tnum 16 0) 3 9) SBEmpty in
  forward signed_bounds_numeric bvmul
    [TVal w5 dom9_mul_choices; TVal w5 (dom9_const w5 3)] = TVal w5 precise /\
  forward (tagged_domain signed_bounds_classic_domain) bvmul
    [TVal w5 dom9_mul_choices; TVal w5 (dom9_const w5 3)] = TVal w5 classic /\
  proj1_sig (forward (signed_bounds_capped w5) bvmul
    [clamp w5 (TVal w5 dom9_mul_choices); of_const (signed_bounds_capped w5) w5 3]) =
    TVal w5 precise /\
  proj1_sig (forward (capped_domain signed_bounds_classic_domain w5) bvmul
    [clamp w5 (TVal w5 dom9_mul_choices);
     of_const (capped_domain signed_bounds_classic_domain w5) w5 3]) = TVal w5 classic.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** The independent finite reference below enumerates words only in this test module. *)
Definition dom9_words (w : width) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat (modulus w))).

Example dom9_multiplication_sets :
  filter (dom9_contains w5
    (dom9_forward w5 bvmul [dom9_mul_choices; dom9_const w5 3])) (dom9_words w5) =
    [3; 5; 7; 9] /\
  map (fun x => wmul w5 x 3) (filter (dom9_contains w5 dom9_mul_choices) (dom9_words w5)) =
    [3; 9].
Proof.
  vm_compute. split; reflexivity.
Qed.

Definition dom9_feasible (w : width) (s : bool) (t : tnum) (lo hi z : Z) : bool :=
  Bool.eqb (msb w z) s && (Z.land z (wrap w (zeros t)) =? 0) &&
    (Z.land (wrap w (ones t)) (Z.lnot z) =? 0) && (lo <=? z) && (z <=? hi).

Definition dom9_reference (w : width) (s : bool) (t : tnum) (lo hi : Z) : sb_half :=
  match filter (dom9_feasible w s t lo hi) (dom9_words w) with
  | [] => SBEmpty
  | z :: rest =>
    SBRange (fold_left (fun acc x => tnum_join w acc (tnum_const w x)) rest (tnum_const w z))
      (fold_left Z.min rest z) (fold_left Z.max rest z)
  end.

Definition dom9_half_eqb (a b : sb_half) : bool :=
  match a, b with
  | SBEmpty, SBEmpty => true
  | SBRange ta la ua, SBRange tb lb ub =>
    (zeros ta =? zeros tb) && (ones ta =? ones tb) && (la =? lb) && (ua =? ub)
  | _, _ => false
  end.

Definition dom9_exhaustive (w : width) : bool :=
  let words := dom9_words w in
  forallb (fun zeros => forallb (fun ones => forallb (fun lo => forallb (fun hi =>
    forallb (fun s => dom9_half_eqb (sb_reduce_half w s (SBRange (Tnum zeros ones) lo hi))
      (dom9_reference w s (Tnum zeros ones) lo hi)) [false; true]) words) words) words) words.

Example dom9_exhaustive_width_two : dom9_exhaustive w2 = true.
Proof.
  vm_compute. reflexivity.
Qed.

Example dom9_exhaustive_width_three : dom9_exhaustive w3 = true.
Proof.
  vm_compute. reflexivity.
Qed.
