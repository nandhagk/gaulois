(** * Word congruences

    Congruences describe words in one residue class, including exact values and the empty set.
    For example, the eight-bit class 6 modulo 4 normalises to the class 2 modulo 4.
    Builds on: BitsWord, DomainsNumeric and Stdlib integer divisibility. *)

From Stdlib Require Import ZArith Zcong List Bool Lia.
From Gaulois.Order Require Import OrderLattice.
From Gaulois.Bits Require Import BitsWord BitsFun BitsOp BitsExtend BitsTestbit.
From Gaulois.Domains Require Import DomainsNumeric.
Import List.ListNotations.

Open Scope Z_scope.

(** Modulus zero denotes an exact integer, while bottom denotes no integer. *)
Inductive cong : Type :=
  | CBot
  | Cong (m r : Z).

(** The raw residue-class meaning is restricted to words of the supplied width. *)
Definition cong_gamma (w : width) (c : cong) (z : Z) : Prop :=
  match c with
  | CBot => False
  | Cong m r => is_word w z /\ (z - r) mod m = 0
  end.

Definition cong_wordb (w : width) (z : Z) : bool := (0 <=? z) && (z <? modulus w).

Lemma cong_wordb_spec : forall w z, cong_wordb w z = true <-> is_word w z.
Proof.
  intros w z; unfold cong_wordb, is_word.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

(** Normalisation uses positive moduli and collapses classes containing at most one word. *)
Definition cong_norm (w : width) (c : cong) : cong :=
  match c with
  | CBot => CBot
  | Cong m r =>
    let m' := Z.abs m in
    if m' =? 0 then
      if cong_wordb w r then Cong 0 r else CBot
    else
      let r' := r mod m' in
      if modulus w <=? m' then
        if cong_wordb w r' then Cong 0 r' else CBot
      else Cong m' r'
  end.

(** Modulo zero is included in the divisibility bridge. *)
Lemma cong_mod_divide : forall a m, a mod m = 0 <-> (m | a).
Proof.
  intros a m; destruct (Z.eq_dec m 0) as [->|Hnonzero].
  - rewrite Z.mod_0_r; split.
    + intro Hzero; subst a; exists 0; reflexivity.
    + intros [k Hk]; lia.
  - apply Z.mod_divide; exact Hnonzero.
Qed.

Lemma cong_mod_abs : forall a m, a mod (Z.abs m) = 0 <-> a mod m = 0.
Proof.
  intros a m; rewrite !cong_mod_divide.
  split; [apply Z.divide_abs_l|intro H; now apply Z.divide_abs_l].
Qed.

Lemma cong_mod_residue : forall z m r, 0 < m ->
  (z - r mod m) mod m = 0 <-> (z - r) mod m = 0.
Proof.
  intros z m r Hm.
  rewrite (Zminus_mod z (r mod m) m), Z.mod_mod by lia.
  rewrite (Zminus_mod z r m); reflexivity.
Qed.

Lemma cong_large_modulus : forall w m r z, modulus w <= m ->
  0 <= r < m -> is_word w z -> ((z - r) mod m = 0 <-> z = r).
Proof.
  intros w m r z Hlarge Hr Hword; unfold is_word in Hword.
  pose proof (modulus_pos w) as Hmod.
  rewrite cong_mod_divide; split.
  - intros [k Hk]. assert (k = 0) by nia; nia.
  - intro Heq; subst z; exists 0; ring.
Qed.

(** Normalisation preserves exactly the words in a residue class, including raw negative moduli. *)
Theorem cong_norm_gamma : forall w c z, cong_gamma w (cong_norm w c) z <-> cong_gamma w c z.
Proof.
  intros w [|m r] z; [reflexivity|].
  unfold cong_norm; fold (Z.abs m); destruct (Z.abs m =? 0) eqn:Hm.
  - apply Z.eqb_eq in Hm; assert (m = 0) by (destruct m; cbn in Hm; congruence); subst m.
    destruct (cong_wordb w r) eqn:Hr; cbn [cong_gamma]; rewrite Z.mod_0_r.
    + reflexivity.
    + split; [contradiction|]. intros [Hword Hzero].
      assert (z = r) by lia; subst z.
      pose proof (proj2 (cong_wordb_spec w r) Hword) as Htrue; congruence.
  - apply Z.eqb_neq in Hm; assert (Hpositive : 0 < Z.abs m) by
      (pose proof (Z.abs_nonneg m); lia).
    destruct (modulus w <=? Z.abs m) eqn:Hlarge.
    + apply Z.leb_le in Hlarge.
      pose proof (Z.mod_pos_bound r (Z.abs m) Hpositive) as Hr.
      destruct (cong_wordb w (r mod Z.abs m)) eqn:Hwordr; cbn [cong_gamma].
      * rewrite Z.mod_0_r; split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
        -- apply (proj1 (cong_mod_abs (z - r) m)).
           apply (proj1 (cong_mod_residue z (Z.abs m) r Hpositive)).
           rewrite Hz; apply Z.mod_0_l; lia.
        -- apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
           apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
           apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz; lia.
      * split; [contradiction|]. intros [Hword Hz].
        apply (proj2 (cong_mod_abs (z - r) m)) in Hz.
        apply (proj2 (cong_mod_residue z (Z.abs m) r Hpositive)) in Hz.
        apply (proj1 (cong_large_modulus w _ _ _ Hlarge Hr Hword)) in Hz; subst z.
        pose proof (proj2 (cong_wordb_spec w _) Hword) as Htrue; congruence.
    + cbn [cong_gamma]; split; intros [Hword Hz]; split; [exact Hword| |exact Hword|].
      * apply (proj1 (cong_mod_abs (z - r) m)).
        apply (proj1 (cong_mod_residue _ _ _ Hpositive)); exact Hz.
      * apply (proj2 (cong_mod_residue _ _ _ Hpositive)).
        now apply (proj2 (cong_mod_abs (z - r) m)).
Qed.

Definition cong_raw_leb (a b : cong) : bool :=
  match a, b with
  | CBot, _ => true
  | _, CBot => false
  | Cong m r, Cong n s => (m mod n =? 0) && ((r - s) mod n =? 0)
  end.

Definition cong_leb (w : width) (a b : cong) : bool :=
  cong_raw_leb (cong_norm w a) (cong_norm w b).

Definition cong_join (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | CBot, c => c
  | c, CBot => c
  | Cong m r, Cong n s => cong_norm w (Cong (Z.gcd (Z.gcd m n) (r - s)) r)
  end.

(** Comparisons and joins normalise first; widening is the gcd join and narrowing keeps its left. *)
Definition cong_lattice (w : width) : lattice cong :=
  {| leb := cong_leb w;
     bot := CBot;
     join := cong_join w;
     widen := cong_join w;
     narrow := fun a _ => a |}.

(** CRT intersection is computed only after incompatible residues have been rejected. *)
Definition cong_meet (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ => CBot
  | _, CBot => CBot
  | Cong m r, Cong n s =>
    if r mod Z.gcd m n =? s mod Z.gcd m n then
      cong_norm w (Cong (Z.lcm m n) (Z.combinecong m n r s))
    else CBot
  end.

(** Canonical classes have small positive moduli or an in-range exact value. *)
Definition cong_canonical (w : width) (c : cong) : Prop :=
  match c with
  | CBot => True
  | Cong m r =>
    (m = 0 /\ is_word w r) \/ (0 < m < modulus w /\ 0 <= r < m)
  end.

Lemma cong_norm_canonical : forall w c, cong_canonical w (cong_norm w c).
Proof.
  intros w [|m r]; [exact I|]; unfold cong_norm.
  destruct (Z.abs m =? 0) eqn:Hm.
  - destruct (cong_wordb w r) eqn:Hr; cbn; [left; split|exact I];
      [reflexivity|now apply cong_wordb_spec].
  - apply Z.eqb_neq in Hm; pose proof (Z.abs_nonneg m) as Hnonnegative.
    destruct (modulus w <=? Z.abs m) eqn:Hlarge.
    + destruct (cong_wordb w (r mod Z.abs m)) eqn:Hr; cbn;
        [left; split|exact I]; [reflexivity|now apply cong_wordb_spec].
    + apply Z.leb_gt in Hlarge; right; split; [lia|apply Z.mod_pos_bound; lia].
Qed.

Lemma cong_canonical_fixed : forall w c, cong_canonical w c -> cong_norm w c = c.
Proof.
  intros w [|m r] Hcanonical; [reflexivity|].
  destruct Hcanonical as [[-> Hword]|[[Hpositive Hsmall] Hr]]; unfold cong_norm.
  - cbn; now rewrite (proj2 (cong_wordb_spec w r) Hword).
  - rewrite Z.abs_eq by lia.
    rewrite (proj2 (Z.eqb_neq m 0)) by lia.
    rewrite Z.mod_small by exact Hr.
    rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia; reflexivity.
Qed.

(** A second normalisation changes no representation. *)
Theorem cong_norm_idempotent : forall w c, cong_norm w (cong_norm w c) = cong_norm w c.
Proof.
  intros w c; apply cong_canonical_fixed; apply cong_norm_canonical.
Qed.

Lemma cong_raw_leb_spec : forall m r n s,
  cong_raw_leb (Cong m r) (Cong n s) = true <-> (n | m) /\ (n | r - s).
Proof.
  intros m r n s; unfold cong_raw_leb; rewrite andb_true_iff, !Z.eqb_eq,
    !cong_mod_divide; reflexivity.
Qed.

Lemma cong_raw_leb_refl : forall c, cong_raw_leb c c = true.
Proof.
  intros [|m r]; [reflexivity|]; apply cong_raw_leb_spec.
  split; [exists 1|exists 0]; ring.
Qed.

Lemma cong_raw_leb_trans : forall a b c,
  cong_raw_leb a b = true -> cong_raw_leb b c = true -> cong_raw_leb a c = true.
Proof.
  intros [|m r] [|n s] [|p t] Hab Hbc; cbn in Hab, Hbc |- *;
    try discriminate; try reflexivity.
  apply cong_raw_leb_spec in Hab as [Hnm Hrs].
  apply cong_raw_leb_spec in Hbc as [Hpn Hst].
  apply cong_raw_leb_spec; split.
  - destruct Hnm as [k Hk], Hpn as [j Hj]; exists (k * j); nia.
  - destruct Hrs as [k Hk], Hpn as [j Hj], Hst as [l Hl].
    exists (k * j + l); nia.
Qed.

Lemma cong_raw_leb_gamma : forall w a b z,
  cong_raw_leb a b = true -> cong_gamma w a z -> cong_gamma w b z.
Proof.
  intros w [|m r] [|n s] z Hle Ha; cbn in Ha; try contradiction; try discriminate.
  destruct Ha as [Hword Hz]; split; [exact Hword|].
  apply cong_raw_leb_spec in Hle as [Hnm Hrs]; apply cong_mod_divide in Hz.
  apply cong_mod_divide; destruct Hnm as [k Hk], Hrs as [j Hj], Hz as [l Hl].
  exists (l * k + j); nia.
Qed.

(** Normalised comparison preserves every word denoted by its left operand. *)
Theorem cong_gamma_monotone : forall w a b z,
  cong_leb w a b = true -> cong_gamma w a z -> cong_gamma w b z.
Proof.
  intros w a b z Hle Hmeaning.
  apply (proj1 (cong_norm_gamma w b z)).
  eapply cong_raw_leb_gamma; [exact Hle|].
  now apply (proj2 (cong_norm_gamma w a z)).
Qed.

(** Normalised comparison is reflexive. *)
Lemma cong_leb_refl : forall w a, cong_leb w a a = true.
Proof.
  intros w a; apply cong_raw_leb_refl.
Qed.

(** Normalised comparison is transitive. *)
Lemma cong_leb_trans : forall w a b c,
  cong_leb w a b = true -> cong_leb w b c = true -> cong_leb w a c = true.
Proof.
  intros w a b c; apply cong_raw_leb_trans.
Qed.

Lemma cong_divide_trans : forall a b c, (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [k Hk] [j Hj]; exists (j * k); nia.
Qed.

Lemma cong_residue_difference : forall m r, (m | r - r mod m).
Proof.
  intros m r; destruct (Z.eq_dec m 0) as [->|Hnonzero].
  - rewrite Z.mod_0_r; exists 0; ring.
  - exists (r / m); pose proof (Z.div_mod r m Hnonzero); nia.
Qed.

Lemma cong_small_norm_equivalent : forall w m r,
  0 <= m < modulus w -> is_word w r ->
  cong_raw_leb (Cong m r) (cong_norm w (Cong m r)) = true /\
  cong_raw_leb (cong_norm w (Cong m r)) (Cong m r) = true.
Proof.
  intros w m r Hm Hword; unfold cong_norm; rewrite Z.abs_eq by lia.
  destruct (m =? 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero; subst m.
    rewrite (proj2 (cong_wordb_spec w r) Hword); split; apply cong_raw_leb_refl.
  - rewrite (proj2 (Z.leb_gt (modulus w) m)) by lia.
    split; apply cong_raw_leb_spec; split; try (exists 1; ring).
    + apply cong_residue_difference.
    + destruct (cong_residue_difference m r) as [k Hk]; exists (-k); nia.
Qed.

Lemma cong_divisor_bound : forall a d, 0 < a -> 0 <= d -> (d | a) -> d <= a.
Proof.
  intros a d Ha Hd [k Hk].
  destruct (Z.eq_dec d 0) as [->|Hnonzero]; [lia|].
  assert (Hpositive : 0 < d) by lia; assert (Hfactor : 0 < k) by nia; nia.
Qed.

Lemma cong_join_modulus_bound : forall w m r n s,
  cong_canonical w (Cong m r) -> cong_canonical w (Cong n s) ->
  0 <= Z.gcd (Z.gcd m n) (r - s) < modulus w.
Proof.
  intros w m r n s Ha Hb.
  pose proof (Z.gcd_nonneg (Z.gcd m n) (r - s)) as Hnonnegative.
  pose proof (Z.gcd_divide_l (Z.gcd m n) (r - s)) as Hdivisor.
  assert (Hdividesm : (Z.gcd (Z.gcd m n) (r - s) | m)).
  { eapply cong_divide_trans; [exact Hdivisor|apply Z.gcd_divide_l]. }
  assert (Hdividesn : (Z.gcd (Z.gcd m n) (r - s) | n)).
  { eapply cong_divide_trans; [exact Hdivisor|apply Z.gcd_divide_r]. }
  destruct Ha as [[-> Hr]|[[Hm Hsmall] Hr]].
  - destruct Hb as [[-> Hs]|[[Hn Hsmall] Hs]].
    + change (0 <= Z.abs (r - s) < modulus w).
      unfold is_word in Hr, Hs; pose proof (Z.abs_nonneg (r - s)).
      split; [assumption|]; apply Z.abs_lt; lia.
    + pose proof (cong_divisor_bound _ _ Hn Hnonnegative Hdividesn); lia.
  - pose proof (cong_divisor_bound _ _ Hm Hnonnegative Hdividesm); lia.
Qed.

Lemma cong_canonical_word_residue : forall w m r,
  cong_canonical w (Cong m r) -> is_word w r.
Proof.
  intros w m r [[_ Hword]|[[Hm Hsmall] Hr]]; [exact Hword|].
  unfold is_word; lia.
Qed.

Lemma cong_raw_join_upper : forall m r n s,
  let c := Cong (Z.gcd (Z.gcd m n) (r - s)) r in
  cong_raw_leb (Cong m r) c = true /\ cong_raw_leb (Cong n s) c = true.
Proof.
  intros m r n s; cbn zeta; split; apply cong_raw_leb_spec; split.
  - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_l].
  - exists 0; ring.
  - eapply cong_divide_trans; [apply Z.gcd_divide_l|apply Z.gcd_divide_r].
  - destruct (Z.gcd_divide_r (Z.gcd m n) (r - s)) as [k Hk].
    exists (-k); nia.
Qed.

Lemma cong_raw_join_least : forall m r n s c,
  cong_raw_leb (Cong m r) c = true -> cong_raw_leb (Cong n s) c = true ->
  cong_raw_leb (Cong (Z.gcd (Z.gcd m n) (r - s)) r) c = true.
Proof.
  intros m r n s [|p t] Ha Hb; [discriminate|].
  apply cong_raw_leb_spec in Ha as [Hpm Hrt].
  apply cong_raw_leb_spec in Hb as [Hpn Hst].
  apply cong_raw_leb_spec; split; [|exact Hrt].
  apply Z.gcd_greatest; [now apply Z.gcd_greatest|].
  destruct Hrt as [k Hk], Hst as [j Hj]; exists (k - j); nia.
Qed.

Lemma cong_join_upper : forall w a b,
  cong_leb w a (cong_join w a b) = true /\ cong_leb w b (cong_join w a b) = true.
Proof.
  intros w a b.
  pose proof (cong_norm_canonical w a) as Ha.
  pose proof (cong_norm_canonical w b) as Hb.
  unfold cong_leb, cong_join.
  destruct (cong_norm w a) as [|m r] eqn:Hna,
    (cong_norm w b) as [|n s] eqn:Hnb.
  - split; reflexivity.
  - rewrite (cong_canonical_fixed w _ Hb); split; [reflexivity|apply cong_raw_leb_refl].
  - rewrite (cong_canonical_fixed w _ Ha); split; [apply cong_raw_leb_refl|reflexivity].
  - rewrite cong_norm_idempotent.
    destruct (cong_small_norm_equivalent w _ r (cong_join_modulus_bound w _ _ _ _ Ha Hb)
      (cong_canonical_word_residue w _ _ Ha)) as [Hnorm _].
    destruct (cong_raw_join_upper m r n s) as [Hleft Hright].
    split; eapply cong_raw_leb_trans; eassumption.
Qed.

(** Normalised gcd joins and the residue-class preorder satisfy the weak lattice laws. *)
Theorem cong_laws : forall w, lattice_laws (cong_lattice w).
Proof.
  intro w; constructor.
  - apply cong_leb_refl.
  - apply cong_leb_trans.
  - intro a; reflexivity.
  - intros a b; apply (proj1 (cong_join_upper w a b)).
  - intros a b; apply (proj2 (cong_join_upper w a b)).
  - intros a b; apply (proj1 (cong_join_upper w a b)).
  - intros a b; apply (proj2 (cong_join_upper w a b)).
  - intros a b _; apply cong_leb_refl.
  - intros a b Hle; exact Hle.
Qed.

(** The gcd join is a least upper bound in the normalised residue-class preorder. *)
Theorem cong_lub : forall w, lub_laws (cong_lattice w).
Proof.
  intro w; constructor; intros a b c Ha Hb.
  pose proof (cong_norm_canonical w a) as Hcanonicala.
  pose proof (cong_norm_canonical w b) as Hcanonicalb.
  change (cong_leb w a c = true) in Ha; change (cong_leb w b c = true) in Hb.
  change (cong_leb w (cong_join w a b) c = true).
  unfold cong_leb, cong_join in *.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s].
  - reflexivity.
  - now rewrite (cong_canonical_fixed w _ Hcanonicalb).
  - now rewrite (cong_canonical_fixed w _ Hcanonicala).
  - rewrite cong_norm_idempotent.
    destruct (cong_small_norm_equivalent w _ r
      (cong_join_modulus_bound w _ _ _ _ Hcanonicala Hcanonicalb)
      (cong_canonical_word_residue w _ _ Hcanonicala)) as [_ Hnorm].
    eapply cong_raw_leb_trans; [exact Hnorm|].
    now apply cong_raw_join_least.
Qed.

Lemma cong_abs_multiple : forall m, (m | Z.abs m).
Proof.
  intros [|p|p]; [exists 0|exists 1|exists (-1)]; cbn; ring.
Qed.

Lemma cong_normalised_residue_difference : forall m r, (m | r mod Z.abs m - r).
Proof.
  intros m r; eapply cong_divide_trans; [apply cong_abs_multiple|].
  destruct (cong_residue_difference (Z.abs m) r) as [k Hk]; exists (-k); nia.
Qed.

Lemma cong_norm_raw_lower : forall w c, cong_raw_leb (cong_norm w c) c = true.
Proof.
  intros w [|m r]; [reflexivity|]; unfold cong_norm.
  destruct (Z.abs m =? 0) eqn:Hm.
  - apply Z.eqb_eq in Hm; assert (m = 0) by (destruct m; cbn in Hm; congruence).
    subst m; destruct (cong_wordb w r); [apply cong_raw_leb_refl|reflexivity].
  - destruct (modulus w <=? Z.abs m).
    + destruct (cong_wordb w (r mod Z.abs m)); [|reflexivity].
      apply cong_raw_leb_spec; split; [exists 0; ring|].
      apply cong_normalised_residue_difference.
    + apply cong_raw_leb_spec; split;
        [apply cong_abs_multiple|apply cong_normalised_residue_difference].
Qed.

(** Chinese-remainder intersection retains every word shared by its two inputs. *)
Theorem cong_meet_sound : forall w a b z,
  cong_gamma w a z -> cong_gamma w b z -> cong_gamma w (cong_meet w a b) z.
Proof.
  intros w a b z Ha Hb.
  apply (proj2 (cong_norm_gamma w a z)) in Ha.
  apply (proj2 (cong_norm_gamma w b z)) in Hb.
  unfold cong_meet.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s];
    cbn in Ha, Hb; try contradiction.
  destruct Ha as [Hword Hr], Hb as [_ Hs].
  apply <- Z.cong_iff_0 in Hr; apply <- Z.cong_iff_0 in Hs.
  pose proof (Z.combinecong_complete' z m n r s Hr Hs) as Hcompatible.
  rewrite (proj2 (Z.eqb_eq _ _) Hcompatible).
  apply (proj2 (cong_norm_gamma w _ z)); split; [exact Hword|].
  apply Z.cong_iff_0.
  rewrite Z.mod_combinecong_lcm; now apply Z.combinecong_complete.
Qed.

(** Chinese-remainder intersection descends below its left operand. *)
Theorem cong_meet_lower_left : forall w a b,
  cong_leb w (cong_meet w a b) a = true.
Proof.
  intros w a b; unfold cong_leb, cong_meet.
  destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s]; try reflexivity.
  destruct (r mod Z.gcd m n =? s mod Z.gcd m n) eqn:Hcompatible; [|reflexivity].
  rewrite cong_norm_idempotent; eapply cong_raw_leb_trans;
    [apply cong_norm_raw_lower|].
  apply cong_raw_leb_spec; split; [apply Z.divide_lcm_l|].
  apply cong_mod_divide; apply Z.cong_iff_0.
  apply (proj1 (Z.combinecong_sound m n r s (proj1 (Z.eqb_eq _ _) Hcompatible))).
Qed.

Definition cong_raw_rank (w : width) (c : cong) : Z :=
  match c with
  | CBot => 0
  | Cong m _ => if m =? 0 then 1 else 2 + Zpos w - Z.log2 m
  end.

Lemma cong_modulus_log_bound : forall w m, 0 < m < modulus w ->
  0 <= Z.log2 m < Zpos w.
Proof.
  intros w m [Hpositive Hsmall]; split; [apply Z.log2_nonneg|].
  apply (proj1 (Z.log2_lt_pow2 m (Zpos w) Hpositive)); exact Hsmall.
Qed.

Lemma cong_raw_rank_bounds : forall w c, cong_canonical w c ->
  0 <= cong_raw_rank w c <= 2 + Zpos w.
Proof.
  intros w [|m r] Hcanonical; cbn [cong_raw_rank]; [lia|].
  destruct Hcanonical as [[-> Hword]|[Hm Hr]]; [cbn; lia|].
  rewrite (proj2 (Z.eqb_neq m 0)) by lia.
  pose proof (cong_modulus_log_bound w m Hm); lia.
Qed.

Lemma cong_proper_divisor_log : forall m n, 0 < m -> 0 < n -> (n | m) -> m <> n ->
  Z.log2 n < Z.log2 m.
Proof.
  intros m n Hm Hn [k Hk] Hdifferent.
  assert (Hpositive : 0 < k) by nia.
  assert (Hnotone : k <> 1) by (intro Heq; subst k; nia).
  assert (Hfactor : 2 <= k) by lia.
  assert (Hdouble : 2 * n <= m) by nia.
  pose proof (Z.log2_le_mono (2 * n) m Hdouble) as Hlog.
  rewrite Z.log2_double in Hlog by exact Hn; lia.
Qed.

Lemma cong_raw_rank_monotone : forall w a b,
  cong_canonical w a -> cong_canonical w b -> cong_raw_leb a b = true ->
  cong_raw_rank w a <= cong_raw_rank w b.
Proof.
  intros w [|m r] [|n s] Ha Hb Hle;
    try (exact (proj1 (cong_raw_rank_bounds w _ Hb))); try discriminate.
  apply cong_raw_leb_spec in Hle as [Hdivisor _].
  destruct Ha as [[-> Hr]|[Hm Hr]], Hb as [[-> Hs]|[Hn Hs]];
    cbn [cong_raw_rank]; rewrite ?Z.eqb_refl; try lia.
  - rewrite (proj2 (Z.eqb_neq n 0)) by lia.
    pose proof (cong_modulus_log_bound w n Hn); lia.
  - destruct Hdivisor as [k Hk]; nia.
  - rewrite (proj2 (Z.eqb_neq m 0)), (proj2 (Z.eqb_neq n 0)) by lia.
    pose proof (cong_divisor_bound m n ltac:(lia) ltac:(lia) Hdivisor) as Hnm.
    pose proof (Z.log2_le_mono n m Hnm); lia.
Qed.

Lemma cong_same_modulus_reverse : forall m r s,
  cong_raw_leb (Cong m r) (Cong m s) = true ->
  cong_raw_leb (Cong m s) (Cong m r) = true.
Proof.
  intros m r s Hle; apply cong_raw_leb_spec in Hle as [Hm [k Hk]].
  apply cong_raw_leb_spec; split; [exact Hm|exists (-k); nia].
Qed.

Lemma cong_raw_rank_strict : forall w a b,
  cong_canonical w a -> cong_canonical w b -> cong_raw_leb a b = true ->
  cong_raw_leb b a = false -> cong_raw_rank w a < cong_raw_rank w b.
Proof.
  intros w [|m r] [|n s] Ha Hb Hle Hstrict; try discriminate.
  - cbn [cong_raw_rank].
    destruct Hb as [[-> Hword]|[Hn Hs]]; cbn; [lia|].
    rewrite (proj2 (Z.eqb_neq n 0)) by lia.
    change (0 < 2 + Zpos w - Z.log2 n).
    pose proof (cong_modulus_log_bound w n Hn); lia.
  - pose proof Hle as Horder; apply cong_raw_leb_spec in Hle as [Hdivisor Hresidue].
    destruct Ha as [[-> Hr]|[Hm Hr]], Hb as [[-> Hs]|[Hn Hs]];
      cbn [cong_raw_rank]; rewrite ?Z.eqb_refl.
    + pose proof (cong_same_modulus_reverse 0 r s Horder) as Hreverse.
      congruence.
    + rewrite (proj2 (Z.eqb_neq n 0)) by lia.
      pose proof (cong_modulus_log_bound w n Hn); lia.
    + destruct Hdivisor as [k Hk]; nia.
    + rewrite (proj2 (Z.eqb_neq m 0)), (proj2 (Z.eqb_neq n 0)) by lia.
      assert (Hdifferent : m <> n).
      { intro Heq; subst n.
        pose proof (cong_same_modulus_reverse m r s Horder); congruence. }
      pose proof (cong_proper_divisor_log m n ltac:(lia) ltac:(lia)
        Hdivisor Hdifferent); lia.
Qed.

(** The height counts strict modulus losses, with exact values immediately above bottom. *)
Definition cong_height (w : width) : monotone_height (cong_lattice w).
Proof.
  unshelve refine (@MonotoneHeight _ (cong_lattice w)
    (@Height _ (cong_lattice w) (fun c => Z.to_nat (cong_raw_rank w (cong_norm w c)))
      (Z.to_nat (2 + Zpos w)) _ _) _).
  - intro c; apply Z2Nat.inj_le; [|lia|];
      pose proof (cong_raw_rank_bounds w _ (cong_norm_canonical w c)); lia.
  - intros a b Hstrict; apply Z2Nat.inj_lt.
    + apply (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w a))).
    + apply (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w (cong_join w a b)))).
    + apply cong_raw_rank_strict; try apply cong_norm_canonical.
      * exact (join_upper_l (cong_laws w) a b).
      * exact Hstrict.
  - intros a b Hle; apply Z2Nat.inj_le.
    + apply (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w a))).
    + apply (proj1 (cong_raw_rank_bounds w _ (cong_norm_canonical w b))).
    + apply cong_raw_rank_monotone; try apply cong_norm_canonical; exact Hle.
Defined.

Lemma cong_top_sound : forall w z, is_word w z -> cong_gamma w (Cong 1 0) z.
Proof.
  intros w z Hword; split; [exact Hword|apply Z.mod_1_r].
Qed.

Lemma cong_const_sound : forall w z, cong_gamma w (Cong 0 (wrap w z)) (wrap w z).
Proof.
  intros w z; split; [apply wrap_is_word|rewrite Z.sub_diag; reflexivity].
Qed.

(** Only a divisor of the word modulus is preserved by modular wraparound. *)
Definition cong_wrap_class (w : width) (m r : Z) : cong :=
  cong_norm w (Cong (Z.gcd m (modulus w)) r).

Lemma cong_wrap_class_sound : forall w m r z, (z - r) mod m = 0 ->
  cong_gamma w (cong_wrap_class w m r) (wrap w z).
Proof.
  intros w m r z Hz; unfold cong_wrap_class.
  apply (proj2 (cong_norm_gamma w _ _)); split; [apply wrap_is_word|].
  apply cong_mod_divide; apply cong_mod_divide in Hz.
  pose proof (cong_residue_difference (modulus w) z) as Hwrap.
  fold (wrap w z) in Hwrap.
  destruct (Z.gcd_divide_l m (modulus w)) as [k Hk].
  destruct (Z.gcd_divide_r m (modulus w)) as [j Hj].
  destruct Hz as [l Hl], Hwrap as [n Hn].
  exists (l * k - n * j); nia.
Qed.

Definition cong_neg (w : width) (a : cong) : cong :=
  match cong_norm w a with
  | CBot => CBot
  | Cong m r => cong_wrap_class w m (-r)
  end.

Definition cong_add (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s => cong_wrap_class w (Z.gcd m n) (r + s)
  | _, _ => CBot
  end.

Definition cong_sub (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s => cong_wrap_class w (Z.gcd m n) (r - s)
  | _, _ => CBot
  end.

Definition cong_mul (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | Cong m r, Cong n s =>
    cong_wrap_class w (Z.gcd (m * n) (Z.gcd (m * s) (n * r))) (r * s)
  | _, _ => CBot
  end.

Lemma cong_neg_sound : forall w a x, cong_gamma w a x -> cong_gamma w (cong_neg w a) (wneg w x).
Proof.
  intros w a x Ha; apply (proj2 (cong_norm_gamma w a x)) in Ha.
  unfold cong_neg; destruct (cong_norm w a) as [|m r]; [contradiction|].
  destruct Ha as [_ Hresidue]; unfold wneg; apply cong_wrap_class_sound.
  apply cong_mod_divide; apply cong_mod_divide in Hresidue.
  destruct Hresidue as [k Hk]; exists (-k); nia.
Qed.

Lemma cong_add_sound : forall w a b x y,
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_add w a b) (wadd w x y).
Proof.
  intros w a b x y Ha Hb.
  apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb.
  unfold cong_add; destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s];
    try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]; unfold wadd; apply cong_wrap_class_sound.
  apply cong_mod_divide; apply cong_mod_divide in Hx; apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
  exists (i * k + j * l); nia.
Qed.

Lemma cong_sub_sound : forall w a b x y,
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_sub w a b) (wsub w x y).
Proof.
  intros w a b x y Ha Hb.
  apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb.
  unfold cong_sub; destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s];
    try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]; unfold wsub; apply cong_wrap_class_sound.
  apply cong_mod_divide; apply cong_mod_divide in Hx; apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  destruct (Z.gcd_divide_l m n) as [k Hk], (Z.gcd_divide_r m n) as [l Hl].
  exists (i * k - j * l); nia.
Qed.

Lemma cong_mul_sound : forall w a b x y,
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_mul w a b) (wmul w x y).
Proof.
  intros w a b x y Ha Hb.
  apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb.
  unfold cong_mul; destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n s];
    try contradiction.
  destruct Ha as [_ Hx], Hb as [_ Hy]; unfold wmul; apply cong_wrap_class_sound.
  apply cong_mod_divide; apply cong_mod_divide in Hx; apply cong_mod_divide in Hy.
  destruct Hx as [i Hi], Hy as [j Hj].
  pose (g := Z.gcd (m * n) (Z.gcd (m * s) (n * r))).
  assert (Hmn : (g | m * n)) by apply Z.gcd_divide_l.
  assert (Hms : (g | m * s)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_l]. }
  assert (Hnr : (g | n * r)).
  { eapply cong_divide_trans; [apply Z.gcd_divide_r|apply Z.gcd_divide_r]. }
  destruct Hmn as [k Hk], Hms as [l Hl], Hnr as [p Hp].
  exists (i * j * k + i * l + j * p).
  replace (x * y - r * s) with (i * j * (m * n) + i * (m * s) + j * (n * r)) by nia.
  fold g; rewrite Hk, Hl, Hp; ring.
Qed.

Definition cong_project (source target : width) (a : cong) : cong :=
  match cong_norm source a with
  | CBot => CBot
  | Cong m r => cong_wrap_class target m r
  end.

Lemma cong_project_sound : forall source target a x,
  cong_gamma source a x -> cong_gamma target (cong_project source target a) (wrap target x).
Proof.
  intros source target a x Ha; apply (proj2 (cong_norm_gamma source a x)) in Ha.
  unfold cong_project; destruct (cong_norm source a) as [|m r]; [contradiction|].
  apply cong_wrap_class_sound; exact (proj2 Ha).
Qed.

Definition cong_shl (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ => CBot
  | _, CBot => CBot
  | Cong m r, Cong 0 k =>
    if Zpos w <=? k then Cong 0 0 else cong_wrap_class w (m * 2^k) (r * 2^k)
  | _, _ => Cong 1 0
  end.

Lemma cong_shl_sound : forall w a b x y,
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_shl w a b) (wshl w x y).
Proof.
  intros w a b x y Ha Hb.
  apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb.
  unfold cong_shl; destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n k];
    try contradiction.
  destruct n as [|n|n]; try (apply cong_top_sound; apply wshl_is_word).
  destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
  rewrite Z.mod_0_r in Hy; assert (y = k) by lia; subst y.
  unfold wshl; rewrite (wrap_id w k Hwordy), (wrap_id w x Hwordx).
  destruct (Zpos w <=? k).
  - split; [apply zero_is_word|reflexivity].
  - apply cong_wrap_class_sound; apply cong_mod_divide; apply cong_mod_divide in Hx.
    destruct Hx as [i Hi]; exists i; nia.
Qed.

Definition cong_urem (w : width) (a b : cong) : cong :=
  match cong_norm w a, cong_norm w b with
  | CBot, _ => CBot
  | _, CBot => CBot
  | Cong m r, Cong 0 c => cong_norm w (Cong (Z.gcd m c) r)
  | _, _ => Cong 1 0
  end.

Lemma cong_urem_sound : forall w a b x y,
  cong_gamma w a x -> cong_gamma w b y -> cong_gamma w (cong_urem w a b) (wurem w x y).
Proof.
  intros w a b x y Ha Hb.
  apply (proj2 (cong_norm_gamma w a x)) in Ha.
  apply (proj2 (cong_norm_gamma w b y)) in Hb.
  unfold cong_urem; destruct (cong_norm w a) as [|m r], (cong_norm w b) as [|n c];
    try contradiction.
  destruct n as [|n|n]; try (apply cong_top_sound; apply wurem_is_word).
  destruct Ha as [Hwordx Hx], Hb as [Hwordy Hy].
  rewrite Z.mod_0_r in Hy; assert (y = c) by lia; subst y.
  apply (proj2 (cong_norm_gamma w _ _)); split; [apply wurem_is_word|].
  unfold wurem; rewrite (wrap_id w c Hwordy), (wrap_id w x Hwordx).
  apply cong_mod_divide in Hx; apply cong_mod_divide.
  destruct (Z.gcd_divide_l m c) as [k Hk], (Z.gcd_divide_r m c) as [j Hj].
  destruct Hx as [i Hi]; destruct (c =? 0).
  - exists (i * k); nia.
  - destruct (cong_residue_difference c x) as [l Hl].
    exists (i * k - l * j); nia.
Qed.

Definition cong_forward_unary (o : op) (source target : width) (a : cong) : cong :=
  match o with
  | bvneg => if Pos.eqb source target then cong_neg target a else Cong 1 0
  | bvzext _ => if Pos.leb source target then cong_norm target a else Cong 1 0
  | bvtrunc _ => cong_project source target a
  | _ => Cong 1 0
  end.

Definition cong_forward_binary (o : op) (wa wb target : width) (a b : cong) : cong :=
  if Pos.eqb wa target && Pos.eqb wb target then
    match o with
    | bvadd => cong_add target a b
    | bvsub => cong_sub target a b
    | bvmul => cong_mul target a b
    | bvshl => cong_shl target a b
    | bvurem => cong_urem target a b
    | _ => Cong 1 0
    end
  else Cong 1 0.

Definition cong_forward (o : op) (wps : list (width * cong)) (target : width) : cong :=
  match wps with
  | [(w, a)] => cong_forward_unary o w target a
  | [(wa, a); (wb, b)] => cong_forward_binary o wa wb target a b
  | [(_, _); (wa, a); (wb, b)] =>
    match o with
    | bvite => if Pos.eqb wa target && Pos.eqb wb target then cong_join target a b else Cong 1 0
    | _ => Cong 1 0
    end
  | _ => Cong 1 0
  end.

(** Congruence transfers preserve the stated modular arithmetic information. *)
Definition cong_domain : word_domain cong :=
  {| plat := cong_lattice;
     ptop := fun _ => Cong 1 0;
     pconst := fun w z => Cong 0 (wrap w z);
     pforward := cong_forward;
     passume := fun _ wps _ _ => map snd wps;
     pmeet := cong_meet |}.

Lemma cong_change_width : forall source target a x,
  cong_gamma source a x -> is_word target x -> cong_gamma target a x.
Proof.
  intros source target [|m r] x Ha Hword; [contradiction|].
  exact (conj Hword (proj2 Ha)).
Qed.

Lemma cong_gamma_word : forall w a x, cong_gamma w a x -> is_word w x.
Proof.
  intros w [|m r] x Ha; [contradiction|exact (proj1 Ha)].
Qed.

Lemma cong_forward_unary_sound : forall o source target a x z,
  cong_gamma source a x -> eval_op o [(source, x)] = Some (target, z) ->
  cong_gamma target (cong_forward_unary o source target a) z.
Proof.
  intros o source target a x z Ha Heval.
  pose proof (eval_op_is_word _ _ _ Heval) as Hword; cbn in Hword.
  destruct o; cbn [cong_forward_unary]; try (now apply cong_top_sound).
  - destruct (Pos.eqb source target) eqn:Hwidth; [|now apply cong_top_sound].
    apply Pos.eqb_eq in Hwidth; subst target.
    rewrite (eval_op_fun1 bvneg source x wneg eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_neg_sound.
  - destruct (Pos.leb source target) eqn:Hwidth; [|now apply cong_top_sound].
    apply Pos.leb_le in Hwidth.
    unfold eval_op in Heval; cbn [result_width map fst snd op_value normalize_word] in Heval.
    inversion Heval; subst target z.
    assert (Hsource : is_word source x).
    { destruct a as [|m r]; [contradiction|exact (proj1 Ha)]. }
    rewrite (wrap_id source x Hsource),
      (wrap_id (source + extra)%positive x (word_widen _ _ _ Hwidth Hsource)).
    apply (proj2 (cong_norm_gamma _ _ _)); eapply cong_change_width;
      [exact Ha|eapply word_widen; eassumption].
  - unfold eval_op in Heval; cbn [result_width map fst snd] in Heval.
    destruct (Pos.leb target0 source) eqn:Hwidth; [|discriminate].
    cbn [op_value normalize_word map fst snd] in Heval.
    inversion Heval; subst target z.
    assert (Hsource : is_word source x).
    { destruct a as [|m r]; [contradiction|exact (proj1 Ha)]. }
    rewrite (wrap_id source x Hsource); now apply cong_project_sound.
Qed.

Lemma cong_forward_binary_sound : forall o wa wb target a b x y z,
  cong_gamma wa a x -> cong_gamma wb b y ->
  eval_op o [(wa, x); (wb, y)] = Some (target, z) ->
  cong_gamma target (cong_forward_binary o wa wb target a b) z.
Proof.
  intros o wa wb target a b x y z Ha Hb Heval.
  pose proof (eval_op_is_word _ _ _ Heval) as Hword; cbn in Hword.
  unfold cong_forward_binary.
  destruct (Pos.eqb wa target && Pos.eqb wb target) eqn:Hwidth;
    [|now apply cong_top_sound].
  apply andb_true_iff in Hwidth as [Hwa Hwb].
  apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb; subst wa wb.
  destruct o; try (now apply cong_top_sound).
  - rewrite (eval_op_fun2 bvadd target x y wadd eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_add_sound.
  - rewrite (eval_op_fun2 bvsub target x y wsub eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_sub_sound.
  - rewrite (eval_op_fun2 bvmul target x y wmul eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_mul_sound.
  - rewrite (eval_op_fun2 bvurem target x y wurem eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_urem_sound.
  - rewrite (eval_op_fun2 bvshl target x y wshl eq_refl) in Heval.
    inversion Heval; subst z; now apply cong_shl_sound.
Qed.

Lemma cong_forward_ternary_sound : forall o wc wa wb target condition a b c x y z,
  cong_gamma wc condition c -> cong_gamma wa a x -> cong_gamma wb b y ->
  eval_op o [(wc, c); (wa, x); (wb, y)] = Some (target, z) ->
  cong_gamma target (cong_forward o [(wc, condition); (wa, a); (wb, b)] target) z.
Proof.
  intros o wc wa wb target condition a b c x y z Hc Ha Hb Heval.
  pose proof (eval_op_is_word _ _ _ Heval) as Hword; cbn in Hword.
  destruct o; cbn [cong_forward]; try (now apply cong_top_sound).
  destruct (Pos.eqb wa target && Pos.eqb wb target) eqn:Hwidth;
    [|now apply cong_top_sound].
  apply andb_true_iff in Hwidth as [Hwa Hwb].
  apply Pos.eqb_eq in Hwa; apply Pos.eqb_eq in Hwb; subst wa wb.
  pose proof (eval_op_width _ _ _ Heval) as Hchecked.
  cbn [result_width map fst snd] in Hchecked.
  rewrite Pos.eqb_refl in Hchecked.
  destruct (Pos.eqb wc 1) eqn:Hcondition; cbn in Hchecked; [|discriminate].
  apply Pos.eqb_eq in Hcondition; subst wc.
  rewrite eval_op_ite in Heval.
  destruct (wrap 1%positive c =? 1) eqn:Hselect; inversion Heval; subst z.
  - rewrite (wrap_id target x (cong_gamma_word _ _ _ Ha)).
    eapply cong_gamma_monotone; [apply (proj1 (cong_join_upper target a b))|exact Ha].
  - rewrite (wrap_id target y (cong_gamma_word _ _ _ Hb)).
    eapply cong_gamma_monotone; [apply (proj2 (cong_join_upper target a b))|exact Hb].
Qed.

Lemma cong_forward_sound : forall o wps ys target z,
  Forall2 (payload_sound cong_gamma) wps ys -> eval_op o ys = Some (target, z) ->
  cong_gamma target (cong_forward o wps target) z.
Proof.
  intros o wps ys target z Hargs Heval.
  pose proof (eval_op_is_word _ _ _ Heval) as Hword; cbn in Hword.
  destruct wps as [|[w a] ws]; [now apply cong_top_sound|].
  inversion Hargs as [|wp y rest tail Hhead Htail]; subst.
  destruct y as [v x]; destruct Hhead as [Hwidth [Hx Ha]].
  cbn in Hwidth, Hx, Ha; subst v.
  destruct ws as [|[wb b] ws].
  - inversion Htail; subst; eapply cong_forward_unary_sound; eassumption.
  - inversion Htail as [|wpb yb restb tailb Hheadb Htailb]; subst.
    destruct yb as [vb y]; destruct Hheadb as [Hwidthb [Hy Hb]].
    cbn in Hwidthb, Hy, Hb; subst vb.
    destruct ws as [|[wc c] ws].
    + inversion Htailb; subst; eapply cong_forward_binary_sound; eassumption.
    + inversion Htailb as [|wpc yc restc tailc Hheadc Htailc]; subst.
      destruct yc as [vc t]; destruct Hheadc as [Hwidthc [Ht Hc]].
      cbn in Hwidthc, Ht, Hc; subst vc.
      destruct ws as [|wp ws].
      * inversion Htailc; subst; eapply cong_forward_ternary_sound; eassumption.
      * apply cong_top_sound; exact Hword.
Qed.

Lemma cong_assume_identity : forall wps : list (width * cong),
  combine (map fst wps) (map snd wps) = wps.
Proof.
  intros wps; induction wps as [|[w a] ws IH]; cbn; [reflexivity|now rewrite IH].
Qed.

(** Congruence transfers, unchanged assumptions and CRT meet satisfy the payload laws. *)
Theorem cong_word_laws : word_laws cong_domain cong_gamma.
Proof.
  constructor.
  - apply cong_laws.
  - apply cong_gamma_monotone.
  - intros w z Hbot; exact Hbot.
  - apply cong_top_sound.
  - apply cong_const_sound.
  - apply cong_forward_sound.
  - intros o wps ys rw z q Hargs Heval Hq.
    change (Forall2 (fun p y => cong_gamma (fst p) (snd p) (snd y))
      (combine (map fst wps) (map snd wps)) ys).
    rewrite cong_assume_identity.
    clear Heval Hq.
    induction Hargs as [|[w a] [v x] ws ys Hhead Htail IH].
    + constructor.
    + constructor; [exact (proj2 (proj2 Hhead))|exact IH].
  - intros o wps rw q; induction wps as [|[w a] ws IH].
    + constructor.
    + constructor; [apply (leb_refl (cong_laws w))|exact IH].
  - apply cong_meet_sound.
  - apply cong_meet_lower_left.
Qed.
