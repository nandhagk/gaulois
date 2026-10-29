(** * Products of word payloads

    Products exchange information through reductions and restrict their shared meaning to words.
    For example, a known constant refines the other component by meeting with that constant.
    Builds on: DomainsNumeric, DomainsConst, DomainsInterval, DomainsCongruence,
    DomainsKnownBits, DomainsWrapped and OrderReduced. *)

From Stdlib Require Import ZArith List Bool Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderProduct OrderReduced OrderFlat.
From Gaulois.Bits Require Import BitsWord BitsOp BitsFun BitsTestbit.
From Gaulois.Domains Require Import DomainsNumeric DomainsConst DomainsInterval DomainsCongruence
  DomainsKnownBits DomainsWrapped.
Import List.ListNotations.

Open Scope Z_scope.

(** Raw component meanings remain available independently of products. *)
Definition payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) :
  concretisation P Z := {| gamma := G w |}.

(** Reduction soundness observes only values in the supplied word width. *)
Definition word_payload_concretisation {P} (G : width -> P -> Z -> Prop) (w : width) :
  concretisation P Z := {| gamma := fun p z => is_word w z /\ G w p z |}.

(** Both payload meanings must hold for the same word. *)
Definition product_pgamma {P Q} (G1 : width -> P -> Z -> Prop)
  (G2 : width -> Q -> Z -> Prop) : width -> P * Q -> Z -> Prop :=
  fun w pq z => is_word w z /\ G1 w (fst pq) z /\ G2 w (snd pq) z.

Definition product_operands_left {P Q} (wps : list (width * (P * Q))) :
  list (width * P) := List.map (fun wp => (fst wp, fst (snd wp))) wps.

Definition product_operands_right {P Q} (wps : list (width * (P * Q))) :
  list (width * Q) := List.map (fun wp => (fst wp, snd (snd wp))) wps.

Fixpoint product_refine {P Q} (reduce : width -> P * Q -> P * Q)
  (wps : list (width * (P * Q))) (ps : list P) (qs : list Q) : list (P * Q) :=
  match wps, ps, qs with
  | (w, _) :: rest, p :: ps', q :: qs' =>
    reduce w (p, q) :: product_refine reduce rest ps' qs'
  | _, _, _ => []
  end.

(** Each transfer computes both components before reducing their pair. *)
Definition product_word_domain {P Q} (D1 : word_domain P) (D2 : word_domain Q)
  (reduce : width -> P * Q -> P * Q) : word_domain (P * Q) :=
  {| plat := fun w => reduced_lattice (plat D1 w) (plat D2 w) (reduce w);
     ptop := fun w => (ptop D1 w, ptop D2 w);
     pconst := fun w z => (pconst D1 w z, pconst D2 w z);
     pforward := fun o wps rw => reduce rw
       (pforward D1 o (product_operands_left wps) rw,
        pforward D2 o (product_operands_right wps) rw);
     passume := fun o wps rw pq => product_refine reduce wps
       (passume D1 o (product_operands_left wps) rw (fst pq))
       (passume D2 o (product_operands_right wps) rw (snd pq));
     pmeet := fun w a b => reduce w
       (pmeet D1 w (fst a) (fst b), pmeet D2 w (snd a) (snd b)) |}.

(** The word restriction is redundant after a width tag has already imposed it. *)
Theorem product_tagged_gamma_equiv : forall {P Q : Type}
  (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop) a v,
  gamma (tagged_gamma (product_pgamma G1 G2)) a v <->
  gamma (tagged_gamma (fun w pq z => G1 w (fst pq) z /\ G2 w (snd pq) z)) a v.
Proof.
  intros P Q G1 G2 [|w [p q]|] [v z]; cbn;
    unfold product_pgamma; cbn; tauto.
Qed.

(** Exact queries and constant meets obey these additional caller obligations. *)
Record const_reduction_laws {Q} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z) : Prop := {
  const_exact_sound : forall w q c z, exact w q = Some c -> is_word w z -> G w q z -> z = c;
  const_exact_monotone : forall w q1 q2 c, leb (plat D w) q1 q2 = true ->
    exact w q2 = Some c ->
    leb (plat D w) q1 (bot (plat D w)) = true \/ exact w q1 = Some c;
  const_meet_monotone : forall w c q1 q2, is_word w c ->
    leb (plat D w) q1 q2 = true ->
    leb (plat D w) (pmeet D w q1 (pconst D w c))
      (pmeet D w q2 (pconst D w c)) = true;
  const_meet_idempotent : forall w c q, is_word w c ->
    leb (plat D w) (pmeet D w q (pconst D w c))
      (pmeet D w (pmeet D w q (pconst D w c)) (pconst D w c)) = true;
  const_meet_exact_fixed : forall w c q, is_word w c -> exact w q = Some c ->
    leb (plat D w) q (pmeet D w q (pconst D w c)) = true;
  const_meet_mismatch : forall w c q d, is_word w c -> exact w q = Some d -> c <> d ->
    leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w)) = true
}.

Arguments const_exact_sound {Q D G exact}.
Arguments const_exact_monotone {Q D G exact}.
Arguments const_meet_monotone {Q D G exact}.
Arguments const_meet_idempotent {Q D G exact}.
Arguments const_meet_exact_fixed {Q D G exact}.
Arguments const_meet_mismatch {Q D G exact}.

Definition product_wordb (w : width) (c : Z) : bool := (0 <=? c) && (c <? modulus w).

Lemma product_wordb_spec : forall w c, product_wordb w c = true <-> is_word w c.
Proof.
  intros w c; unfold product_wordb, is_word.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt; reflexivity.
Qed.

(** Constant reduction rejects nonwords and uses one meet for a known constant. *)
Definition reduce_const_with {Q} (D : word_domain Q) (exact : width -> Q -> option Z)
  (w : width) (pq : flat Z * Q) : flat Z * Q :=
  let B := (FBot, bot (plat D w)) in
  let q := snd pq in
  if leb (plat D w) q (bot (plat D w)) then B else
  match fst pq with
  | FBot => B
  | FVal c =>
    if product_wordb w c then
      let q' := pmeet D w q (pconst D w c) in
      if leb (plat D w) q' (bot (plat D w)) then B else (FVal c, q')
    else B
  | FTop =>
    match exact w q with
    | None => (FTop, q)
    | Some c => if product_wordb w c then (FVal c, q) else B
    end
  end.

(** Constants combine with any payload whose exact query satisfies the extra laws. *)
Definition const_product_domain {Q} (D : word_domain Q) (exact : width -> Q -> option Z) :
  word_domain (flat Z * Q) := product_word_domain const_domain D (reduce_const_with D exact).

(** An empty component forces the canonical bottom pair. *)
Definition reduction_empty {P Q} (LP : lattice P) (LQ : lattice Q)
  (reduce : P * Q -> P * Q) : Prop :=
  forall p q, leb LP p (bot LP) = true \/ leb LQ q (bot LQ) = true ->
    reduce (p, q) = (bot LP, bot LQ).

Lemma product_operand_sound : forall {P Q} G1 G2 wps ys,
  Forall2 (payload_sound (@product_pgamma P Q G1 G2)) wps ys ->
  Forall2 (payload_sound G1) (product_operands_left wps) ys /\
  Forall2 (payload_sound G2) (product_operands_right wps) ys.
Proof.
  intros P Q G1 G2 wps ys Hsound; induction Hsound as [|[w [p q]] [v z] ws ys Hhead Htail IH].
  - split; constructor.
  - destruct Hhead as [Hwidth [Hword [_ [Hp Hq]]]]; destruct IH as [IHp IHq].
    cbn in Hwidth, Hword, Hp, Hq; subst v.
    split.
    + constructor; [|exact IHp].
      unfold payload_sound; cbn; split; [reflexivity|split; assumption].
    + constructor; [|exact IHq].
      unfold payload_sound; cbn; split; [reflexivity|split; assumption].
Qed.

Lemma product_refine_lower : forall {P Q} (D1 : word_domain P) (D2 : word_domain Q)
  reduce, (forall w, lattice_laws (plat D1 w)) ->
  (forall w, lattice_laws (plat D2 w)) ->
  (forall w, reduction_laws (plat D1 w) (plat D2 w) (reduce w)) ->
  forall wps ps qs,
  Forall2 (fun wp p => leb (plat D1 (fst wp)) p (snd wp) = true)
    (product_operands_left wps) ps ->
  Forall2 (fun wp q => leb (plat D2 (fst wp)) q (snd wp) = true)
    (product_operands_right wps) qs ->
  Forall2 (fun wp pq =>
    leb (plat (product_word_domain D1 D2 reduce) (fst wp)) pq (snd wp) = true)
    wps (product_refine reduce wps ps qs).
Proof.
  intros P Q D1 D2 reduce HL HR Hred wps; induction wps as [|[w [p q]] ws IH];
    intros ps qs Hp Hq.
  - constructor.
  - inversion Hp as [|wp p' rest ps' Hple Hps]; subst.
    inversion Hq as [|wp q' rest qs' Hqle Hqs]; subst.
    cbn [product_refine]; constructor.
    + change (leb (product_lattice (plat D1 w) (plat D2 w))
        (reduce w (reduce w (p', q'))) (p, q) = true).
      eapply (leb_trans (product_laws _ _ (HL w) (HR w))).
      * apply (reduce_lower (Hred w)).
      * eapply (leb_trans (product_laws _ _ (HL w) (HR w))).
        -- apply (reduce_lower (Hred w)).
        -- apply andb_true_iff; split; assumption.
    + apply IH; assumption.
Qed.

Lemma product_refine_sound : forall {P Q} G1 G2
  (reduce : width -> P * Q -> P * Q),
  (forall w, reduction_sound (word_payload_concretisation G1 w)
    (word_payload_concretisation G2 w) (reduce w)) ->
  forall wps ys ps qs,
  Forall2 (payload_sound (product_pgamma G1 G2)) wps ys ->
  Forall2 (fun p y => G1 (fst p) (snd p) (snd y))
    (combine (map fst wps) ps) ys ->
  Forall2 (fun q y => G2 (fst q) (snd q) (snd y))
    (combine (map fst wps) qs) ys ->
  Forall2 (fun pq y => product_pgamma G1 G2 (fst pq) (snd pq) (snd y))
    (combine (map fst wps) (product_refine reduce wps ps qs)) ys.
Proof.
  intros P Q G1 G2 reduce Hred wps ys ps qs Hargs; revert ps qs.
  induction Hargs as [|[w [p q]] [v z] ws ys Hhead Htail IH];
    intros ps qs Hp Hq.
  - constructor.
  - destruct ps as [|p' ps], qs as [|q' qs]; inversion Hp; inversion Hq.
    inversion Hp as [|wp yp restp ysp Hpg Hps]; subst.
    inversion Hq as [|wq yq restq ysq Hqg Hqs]; subst.
    cbn [product_refine]; constructor.
    + destruct Hhead as [Hwidth [Hword Hmeaning]].
      cbn in Hwidth, Hword, Hpg, Hqg; subst v.
      pose proof (reduce_gamma (Hred w) (p', q') z
        (conj (conj Hword Hpg) (conj Hword Hqg))) as [[Hr Hp'] [_ Hq']].
      exact (conj Hr (conj Hp' Hq')).
    + apply IH; assumption.
Qed.

Section ProductTransfers.
Context {P Q : Type} (D1 : word_domain P) (D2 : word_domain Q)
  (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
  (reduce : width -> P * Q -> P * Q) (HL : word_laws D1 G1) (HR : word_laws D2 G2)
  (Hsound : forall w, reduction_sound (word_payload_concretisation G1 w)
    (word_payload_concretisation G2 w) (reduce w)).

Lemma product_forward_sound : forall o wps ys rw z,
  Forall2 (payload_sound (product_pgamma G1 G2)) wps ys ->
  eval_op o ys = Some (rw, z) -> product_pgamma G1 G2 rw
    (pforward (product_word_domain D1 D2 reduce) o wps rw) z.
Proof.
  intros o wps ys rw z Hargs Heval.
  destruct (product_operand_sound G1 G2 _ _ Hargs) as [Hleft Hright].
  pose proof (eval_op_is_word o ys (rw, z) Heval) as Hword; cbn in Hword.
  pose proof (reduce_gamma (Hsound rw)
    (pforward D1 o (product_operands_left wps) rw,
     pforward D2 o (product_operands_right wps) rw) z) as Hkeep.
  destruct Hkeep as [[_ Hp] [_ Hq]].
  - split; split; auto; [eapply (pforward_sound HL)|eapply (pforward_sound HR)]; eassumption.
  - exact (conj Hword (conj Hp Hq)).
Qed.

Lemma product_assume_sound : forall o wps ys rw z pq,
  Forall2 (payload_sound (product_pgamma G1 G2)) wps ys ->
  eval_op o ys = Some (rw, z) -> product_pgamma G1 G2 rw pq z ->
  Forall2 (fun p y => product_pgamma G1 G2 (fst p) (snd p) (snd y))
    (combine (map fst wps) (passume (product_word_domain D1 D2 reduce) o wps rw pq)) ys.
Proof.
  intros o wps ys rw z pq Hargs Heval [_ [Hp Hq]].
  destruct (product_operand_sound G1 G2 _ _ Hargs) as [Hleft Hright].
  pose proof (passume_sound HL o _ ys rw z (fst pq) Hleft Heval Hp) as Hps.
  pose proof (passume_sound HR o _ ys rw z (snd pq) Hright Heval Hq) as Hqs.
  unfold product_operands_left in Hps; unfold product_operands_right in Hqs.
  rewrite map_map in Hps, Hqs.
  eapply product_refine_sound; eassumption.
Qed.

End ProductTransfers.

(** Sound reductions lift component soundness to the word-restricted product. *)
Theorem product_word_laws : forall {P Q : Type} (D1 : word_domain P) (D2 : word_domain Q)
  (G1 : width -> P -> Z -> Prop) (G2 : width -> Q -> Z -> Prop)
  (reduce : width -> P * Q -> P * Q),
  word_laws D1 G1 -> word_laws D2 G2 ->
  (forall w, reduction_laws (plat D1 w) (plat D2 w) (reduce w)) ->
  (forall w, reduction_sound (word_payload_concretisation G1 w)
    (word_payload_concretisation G2 w) (reduce w)) ->
  word_laws (product_word_domain D1 D2 reduce) (product_pgamma G1 G2).
Proof.
  intros P Q D1 D2 G1 G2 reduce HL HR Hred Hsound; constructor.
  - intro w; apply reduced_laws;
      [apply (plat_laws HL)|apply (plat_laws HR)|apply Hred].
  - intros w a b z Hle [Hword [Ha Hb]].
    pose proof (reduce_gamma (Hsound w) a z
      (conj (conj Hword Ha) (conj Hword Hb))) as [[_ Ha'] [_ Hb']].
    apply andb_true_iff in Hle as [Hple Hqle].
    split; [exact Hword|split];
      [eapply (pgamma_monotone HL)|eapply (pgamma_monotone HR)]; eassumption.
  - intros w z [_ [Hbot _]]; exact (pgamma_bot_empty HL w z Hbot).
  - intros w z Hword; split; [exact Hword|split];
      [apply (ptop_sound HL)|apply (ptop_sound HR)]; exact Hword.
  - intros w z; split; [apply wrap_is_word|split];
      [apply (pconst_sound HL)|apply (pconst_sound HR)].
  - apply (product_forward_sound D1 D2 G1 G2 reduce HL HR Hsound).
  - apply (product_assume_sound D1 D2 G1 G2 reduce HL HR Hsound).
  - intros o wps rw pq; apply product_refine_lower.
    + apply (plat_laws HL).
    + apply (plat_laws HR).
    + exact Hred.
    + apply (passume_refines HL).
    + apply (passume_refines HR).
  - intros w a b z [Hword [Ha Hb]] [_ [Ha' Hb']].
    pose proof (reduce_gamma (Hsound w)
      (pmeet D1 w (fst a) (fst b), pmeet D2 w (snd a) (snd b)) z) as Hkeep.
    destruct Hkeep as [[_ Hp] [_ Hq]].
    + split; split; auto; [eapply (pmeet_sound HL)|eapply (pmeet_sound HR)]; eassumption.
    + exact (conj Hword (conj Hp Hq)).
  - intros w a b.
    change (leb (product_lattice (plat D1 w) (plat D2 w))
      (reduce w (reduce w (pmeet D1 w (fst a) (fst b),
        pmeet D2 w (snd a) (snd b)))) a = true).
    pose proof (product_laws _ _ (plat_laws HL w) (plat_laws HR w)) as Hlat.
    eapply (leb_trans Hlat); [apply (reduce_lower (Hred w))|].
    eapply (leb_trans Hlat); [apply (reduce_lower (Hred w))|].
    apply andb_true_iff; split;
      [apply (pmeet_lower_left HL)|apply (pmeet_lower_left HR)].
Qed.

Section ConstantReduction.
Context {Q : Type} (D : word_domain Q) (G : width -> Q -> Z -> Prop)
  (exact : width -> Q -> option Z) (laws : word_laws D G)
  (extra : const_reduction_laws D G exact) (w : width).

Let L := product_lattice (flat_lattice Z.eqb) (plat D w).
Let B : flat Z * Q := (FBot, bot (plat D w)).

Lemma const_pair_laws : lattice_laws L.
Proof.
  apply product_laws; [apply flat_laws; exact Z.eqb_eq|apply (plat_laws laws)].
Qed.

Lemma const_pair_bottom : forall pq, leb L B pq = true.
Proof.
  apply (bot_least const_pair_laws).
Qed.

Lemma const_reduce_empty : reduction_empty (flat_lattice Z.eqb) (plat D w)
  (reduce_const_with D exact w).
Proof.
  intros [|c|] q Hempty; unfold reduce_const_with; cbn in *;
    destruct (leb (plat D w) q (bot (plat D w))) eqn:Hq; try reflexivity;
    destruct Hempty; discriminate.
Qed.

Lemma const_reduce_lower : forall pq,
  leb L (reduce_const_with D exact w pq) pq = true.
Proof.
  intros [p q]; unfold reduce_const_with; cbn [fst snd].
  destruct (leb (plat D w) q (bot (plat D w))) eqn:Hq;
    [apply const_pair_bottom|].
  destruct p as [|c|]; [apply const_pair_bottom| |].
  - destruct (product_wordb w c) eqn:Hword; [|apply const_pair_bottom].
    destruct (leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w)));
      [apply const_pair_bottom|].
    change ((c =? c) && leb (plat D w) (pmeet D w q (pconst D w c)) q = true).
    rewrite Z.eqb_refl; apply (pmeet_lower_left laws).
  - destruct (exact w q) as [c|]; [destruct (product_wordb w c)|];
      try apply const_pair_bottom;
      change (leb (plat D w) q q = true); apply (leb_refl (plat_laws laws w)).
Qed.

Lemma const_reduce_sound : reduction_sound (word_payload_concretisation const_gamma w)
  (word_payload_concretisation G w) (reduce_const_with D exact w).
Proof.
  constructor; intros [[|c|] q] z [[Hword Hp] [_ Hq]]; cbn in Hp; [contradiction| |].
  all: unfold reduce_const_with; cbn [fst snd].
  all: assert (Hnonempty : leb (plat D w) q (bot (plat D w)) = false).
  all: try (destruct (leb (plat D w) q (bot (plat D w))) eqn:He;
    [exfalso; apply (pgamma_bot_empty laws w z);
      eapply (pgamma_monotone laws); eassumption|reflexivity]).
  all: rewrite Hnonempty.
  - subst z. rewrite (proj2 (product_wordb_spec w c) Hword).
    assert (Hconst : G w (pconst D w c) c).
    { pose proof (pconst_sound laws w c) as Hc. now rewrite (wrap_id w c Hword) in Hc. }
    pose proof (pmeet_sound laws w q (pconst D w c) c Hq Hconst) as Hmeet.
    destruct (leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w))) eqn:He.
    + exfalso; apply (pgamma_bot_empty laws w c).
      eapply (pgamma_monotone laws); eassumption.
    + exact (conj (conj Hword eq_refl) (conj Hword Hmeet)).
  - destruct (exact w q) as [c|] eqn:He.
    + pose proof (const_exact_sound extra w q c z He Hword Hq) as Hvalue; subst c.
      rewrite (proj2 (product_wordb_spec w z) Hword).
      exact (conj (conj Hword eq_refl) (conj Hword Hq)).
    + exact (conj (conj Hword I) (conj Hword Hq)).
Qed.

Lemma const_reduce_known_monotone : forall c q1 q2,
  leb (plat D w) q1 q2 = true ->
  leb L (reduce_const_with D exact w (FVal c, q1))
    (reduce_const_with D exact w (FVal c, q2)) = true.
Proof.
  intros c q1 q2 Hle; unfold reduce_const_with; cbn [fst snd].
  destruct (leb (plat D w) q1 (bot (plat D w))) eqn:Hempty1;
    [apply const_pair_bottom|].
  destruct (leb (plat D w) q2 (bot (plat D w))) eqn:Hempty2.
  { pose proof (leb_trans (plat_laws laws w) _ _ _ Hle Hempty2) as Hempty.
    rewrite Hempty1 in Hempty; discriminate. }
  destruct (product_wordb w c) eqn:Hword; [|apply const_pair_bottom].
  pose proof (const_meet_monotone extra w c q1 q2
    (proj1 (product_wordb_spec w c) Hword) Hle) as Hmeet.
  destruct (leb (plat D w) (pmeet D w q1 (pconst D w c)) (bot (plat D w)))
    eqn:Hmeet1; [apply const_pair_bottom|].
  destruct (leb (plat D w) (pmeet D w q2 (pconst D w c)) (bot (plat D w)))
    eqn:Hmeet2.
  { pose proof (leb_trans (plat_laws laws w) _ _ _ Hmeet Hmeet2) as Hempty.
    rewrite Hmeet1 in Hempty; discriminate. }
  change ((c =? c) && leb (plat D w)
    (pmeet D w q1 (pconst D w c)) (pmeet D w q2 (pconst D w c)) = true).
  now rewrite Z.eqb_refl.
Qed.

Lemma const_reduce_known_top : forall c q1 q2,
  leb (plat D w) q1 q2 = true ->
  leb L (reduce_const_with D exact w (FVal c, q1))
    (reduce_const_with D exact w (FTop, q2)) = true.
Proof.
  intros c q1 q2 Hle.
  destruct (leb (plat D w) q1 (bot (plat D w))) eqn:Hempty1.
  { rewrite (const_reduce_empty (FVal c) q1 (or_intror Hempty1));
      apply const_pair_bottom. }
  destruct (leb (plat D w) q2 (bot (plat D w))) eqn:Hempty2.
  { pose proof (leb_trans (plat_laws laws w) _ _ _ Hle Hempty2) as Hempty.
    rewrite Hempty1 in Hempty; discriminate. }
  destruct (exact w q2) as [d|] eqn:Hexact.
  - unfold reduce_const_with; cbn [fst snd]; rewrite Hempty1, Hempty2, Hexact.
    destruct (product_wordb w c) eqn:Hword; [|apply const_pair_bottom].
    destruct (Z.eq_dec c d) as [Hsame|Hdifferent].
    + subst d; rewrite Hword.
      destruct (leb (plat D w) (pmeet D w q1 (pconst D w c)) (bot (plat D w)));
        [apply const_pair_bottom|].
      change ((c =? c) && leb (plat D w) (pmeet D w q1 (pconst D w c)) q2 = true).
      rewrite Z.eqb_refl; cbn.
      eapply (leb_trans (plat_laws laws w)); [apply (pmeet_lower_left laws)|exact Hle].
    + destruct (const_exact_monotone extra w q1 q2 d Hle Hexact) as [Hempty|Hexact1].
      * rewrite Hempty1 in Hempty; discriminate.
      * rewrite (const_meet_mismatch extra w c q1 d
          (proj1 (product_wordb_spec w c) Hword) Hexact1 Hdifferent).
        apply const_pair_bottom.
  - assert (Hunchanged : reduce_const_with D exact w (FTop, q2) = (FTop, q2)).
    { unfold reduce_const_with; cbn; now rewrite Hempty2, Hexact. }
    rewrite Hunchanged; eapply (leb_trans const_pair_laws); [apply const_reduce_lower|].
    exact Hle.
Qed.

Lemma const_reduce_top_monotone : forall q1 q2,
  leb (plat D w) q1 q2 = true ->
  leb L (reduce_const_with D exact w (FTop, q1))
    (reduce_const_with D exact w (FTop, q2)) = true.
Proof.
  intros q1 q2 Hle; unfold reduce_const_with; cbn [fst snd].
  destruct (leb (plat D w) q1 (bot (plat D w))) eqn:Hempty1;
    [apply const_pair_bottom|].
  destruct (leb (plat D w) q2 (bot (plat D w))) eqn:Hempty2.
  { pose proof (leb_trans (plat_laws laws w) _ _ _ Hle Hempty2) as Hempty.
    rewrite Hempty1 in Hempty; discriminate. }
  destruct (exact w q2) as [c|] eqn:Hexact2.
  - destruct (const_exact_monotone extra w q1 q2 c Hle Hexact2) as [Hempty|Hexact1].
    + rewrite Hempty1 in Hempty; discriminate.
    + rewrite Hexact1; destruct (product_wordb w c); [|apply const_pair_bottom].
      change ((c =? c) && leb (plat D w) q1 q2 = true); now rewrite Z.eqb_refl.
  - destruct (exact w q1) as [c|]; [destruct (product_wordb w c)|];
      try apply const_pair_bottom; exact Hle.
Qed.

Lemma const_reduce_monotone : forall x y, leb L x y = true ->
  leb L (reduce_const_with D exact w x) (reduce_const_with D exact w y) = true.
Proof.
  intros [[|c|] q1] [[|d|] q2] Hle; cbn in Hle;
    try discriminate; try (rewrite (const_reduce_empty FBot q1 (or_introl eq_refl));
      apply const_pair_bottom).
  - apply andb_true_iff in Hle as [Hcd Hq]; apply Z.eqb_eq in Hcd; subst d.
    now apply const_reduce_known_monotone.
  - now apply const_reduce_known_top.
  - now apply const_reduce_top_monotone.
Qed.

Lemma const_reduce_known_stable : forall c q,
  product_wordb w c = true -> leb (plat D w) q (bot (plat D w)) = false ->
  leb (plat D w) q (pmeet D w q (pconst D w c)) = true ->
  leb L (FVal c, q) (reduce_const_with D exact w (FVal c, q)) = true.
Proof.
  intros c q Hword Hnonempty Hfixed; unfold reduce_const_with; cbn [fst snd].
  rewrite Hword, Hnonempty.
  destruct (leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w))) eqn:Hempty.
  - pose proof (leb_trans (plat_laws laws w) _ _ _ Hfixed Hempty) as Hcontra.
    rewrite Hnonempty in Hcontra; discriminate.
  - change ((c =? c) && leb (plat D w) q (pmeet D w q (pconst D w c)) = true).
    now rewrite Z.eqb_refl.
Qed.

Lemma const_reduce_idempotent : forall x,
  leb L (reduce_const_with D exact w x)
    (reduce_const_with D exact w (reduce_const_with D exact w x)) = true.
Proof.
  intros [p q]; unfold reduce_const_with at 1 3; cbn [fst snd].
  destruct (leb (plat D w) q (bot (plat D w))) eqn:Hempty;
    [apply const_pair_bottom|].
  destruct p as [|c|]; [apply const_pair_bottom| |].
  - destruct (product_wordb w c) eqn:Hword; [|apply const_pair_bottom].
    destruct (leb (plat D w) (pmeet D w q (pconst D w c)) (bot (plat D w)))
      eqn:Hmeet; [apply const_pair_bottom|].
    apply const_reduce_known_stable; try assumption.
    apply (const_meet_idempotent extra); now apply product_wordb_spec.
  - destruct (exact w q) as [c|] eqn:Hexact.
    + destruct (product_wordb w c) eqn:Hword; [|apply const_pair_bottom].
      apply const_reduce_known_stable; try assumption.
      apply (const_meet_exact_fixed extra); [now apply product_wordb_spec|exact Hexact].
    + unfold reduce_const_with; cbn; rewrite Hempty, Hexact.
      cbn; apply (leb_refl (plat_laws laws w)).
Qed.

End ConstantReduction.

(** Constant reduction descends, preserves order and shared words, and is stable. *)
Theorem reduce_const_with_laws : forall (w : width) {Q : Type} (D : word_domain Q)
  (G : width -> Q -> Z -> Prop) (exact : width -> Q -> option Z),
  word_laws D G -> const_reduction_laws D G exact ->
  reduction_laws (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w) /\
  reduction_sound (word_payload_concretisation const_gamma w)
    (word_payload_concretisation G w) (reduce_const_with D exact w) /\
  reduction_empty (flat_lattice Z.eqb) (plat D w) (reduce_const_with D exact w).
Proof.
  intros w Q D G exact laws extra; split; [constructor|split].
  - apply (const_reduce_lower D G exact laws w).
  - apply (const_reduce_monotone D G exact laws extra w).
  - apply (const_reduce_idempotent D G exact laws extra w).
  - apply (const_reduce_sound D G exact laws extra w).
  - apply const_reduce_empty.
Qed.

(** * Interval and congruence reduction *)

Definition product_round_up (m r lo : Z) : Z := lo + (r - lo) mod m.

Definition product_round_down (m r hi : Z) : Z := hi - (hi - r) mod m.

(** Congruence-compatible endpoints are selected inside the word-clipped interval. *)
Definition reduce_interval_cong (w : width) (pq : interval * cong) : interval * cong :=
  let B := (IBot, CBot) in
  match interval_finite (interval_clip w (fst pq)), cong_norm w (snd pq) with
  | Some (lo, hi), Cong 0 r =>
    if (lo <=? r) && (r <=? hi) then (Itv (Fin r) (Fin r), Cong 0 r) else B
  | Some (lo, hi), Cong m r =>
    let lo' := product_round_up m r lo in
    let hi' := product_round_down m r hi in
    if lo' <=? hi' then
      (Itv (Fin lo') (Fin hi'), if lo' =? hi' then Cong 0 lo' else Cong m r)
    else B
  | _, _ => B
  end.

(** The interval product applies the shared reducer after its component operations. *)
Definition interval_cong_domain (thresholds : list Z) : word_domain (interval * cong) :=
  product_word_domain (interval_domain thresholds) cong_domain reduce_interval_cong.

Lemma product_round_up_sound : forall m r lo z,
  0 < m -> lo <= z -> (z - r) mod m = 0 -> product_round_up m r lo <= z.
Proof.
  intros m r lo z Hm Hlo Hresidue; unfold product_round_up.
  apply cong_mod_divide in Hresidue; destruct Hresidue as [k Hk].
  pose proof (Z.div_mod (r - lo) m ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound (r - lo) m Hm) as Hremainder.
  assert (Hfactor : 0 <= k + (r - lo) / m) by nia.
  nia.
Qed.

Lemma product_round_down_sound : forall m r hi z,
  0 < m -> z <= hi -> (z - r) mod m = 0 -> z <= product_round_down m r hi.
Proof.
  intros m r hi z Hm Hhi Hresidue; unfold product_round_down.
  apply cong_mod_divide in Hresidue; destruct Hresidue as [k Hk].
  pose proof (Z.div_mod (hi - r) m ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound (hi - r) m Hm) as Hremainder.
  assert (Hfactor : 0 <= (hi - r) / m - k) by nia.
  nia.
Qed.

Lemma product_round_up_congruent : forall m r lo, 0 < m ->
  (product_round_up m r lo - r) mod m = 0.
Proof.
  intros m r lo Hm; unfold product_round_up; apply cong_mod_divide.
  destruct (cong_residue_difference m (r - lo)) as [k Hk]; exists (-k); nia.
Qed.

Lemma product_round_down_congruent : forall m r hi, 0 < m ->
  (product_round_down m r hi - r) mod m = 0.
Proof.
  intros m r hi Hm; unfold product_round_down; apply cong_mod_divide.
  replace (hi - (hi - r) mod m - r) with ((hi - r) - (hi - r) mod m) by ring.
  apply cong_residue_difference.
Qed.

Lemma product_round_inward : forall m r lo hi, 0 < m ->
  lo <= product_round_up m r lo /\ product_round_down m r hi <= hi.
Proof.
  intros m r lo hi Hm; unfold product_round_up, product_round_down.
  pose proof (Z.mod_pos_bound (r - lo) m Hm).
  pose proof (Z.mod_pos_bound (hi - r) m Hm); lia.
Qed.

Definition product_clip_shape (w : width) (i : interval) : Prop :=
  match interval_clip w i with
  | IBot => True
  | Itv (Fin lo) (Fin hi) => 0 <= lo /\ lo <= hi /\ hi < modulus w
  | _ => False
  end.

(* Split only endpoint comparisons generated by clipping, then reflect them for arithmetic. *)
Local Ltac product_clip_cases :=
  repeat match goal with
  | |- context [if ?test then _ else _] => destruct test eqn:?
  end;
  cbn [bounds_nonempty bound_leb] in *;
  repeat match goal with
  | H : (?a <=? ?b) = true |- _ => apply Z.leb_le in H
  | H : (?a <=? ?b) = false |- _ => apply Z.leb_gt in H
  end;
  try exact I; try lia.

Lemma product_clip_shape_holds : forall w i, product_clip_shape w i.
Proof.
  intros w [|[|lo|] [|hi|]]; unfold product_clip_shape, interval_clip,
    interval_meet, interval_top; cbn [bound_max bound_min bound_leb];
    unfold bound_max, bound_min in *; cbn [bound_leb] in *;
    pose proof (modulus_pos w) as Hmod; product_clip_cases.
Qed.

Lemma product_clip_finite : forall w i z, interval_pgamma w i z ->
  exists lo hi, interval_finite (interval_clip w i) = Some (lo, hi) /\ lo <= z <= hi.
Proof.
  intros w i z Hinput.
  pose proof (interval_clip_sound w i z Hinput) as Hclip.
  pose proof (product_clip_shape_holds w i) as Hshape.
  unfold product_clip_shape in Hshape.
  destruct (interval_clip w i) as [|[|lo|] [|hi|]] eqn:Hclipvalue;
    try contradiction; try (destruct Hclip as [_ Hbot]; contradiction).
  exists lo, hi; split; [reflexivity|].
  eapply interval_finite_sound; [exact Hclip|reflexivity].
Qed.

(** Interval/congruence reduction preserves every shared word. *)
Theorem reduce_interval_cong_sound : forall w,
  reduction_sound (word_payload_concretisation interval_pgamma w)
    (word_payload_concretisation cong_gamma w) (reduce_interval_cong w).
Proof.
  intro w; constructor; intros [i c] z [[Hword Hi] [_ Hc]].
  destruct (product_clip_finite w i z Hi) as [lo [hi [Hfinite Hbounds]]].
  apply (proj2 (cong_norm_gamma w c z)) in Hc.
  pose proof (cong_norm_canonical w c) as Hcanonical.
  unfold reduce_interval_cong; cbn [fst snd]; rewrite Hfinite.
  destruct (cong_norm w c) as [|m r]; [contradiction|].
  destruct m as [|m|m].
  - destruct Hc as [_ Hz]; rewrite Z.mod_0_r in Hz.
    assert (Heq : z = r) by lia; subst z.
    rewrite (proj2 (Z.leb_le lo r)) by lia.
    rewrite (proj2 (Z.leb_le r hi)) by lia.
    split; split; try exact Hword.
    + split; [exact Hword|]; cbn; now rewrite Z.leb_refl.
    + split; [exact Hword|]; cbn; now rewrite Z.sub_diag.
  - destruct Hc as [_ Hz].
    pose proof (product_round_up_sound (Zpos m) r lo z ltac:(lia) ltac:(lia) Hz) as Hlo.
    pose proof (product_round_down_sound (Zpos m) r hi z ltac:(lia) ltac:(lia) Hz) as Hhi.
    rewrite (proj2 (Z.leb_le _ _)) by lia.
    assert (Hinterval : interval_pgamma w
      (Itv (Fin (product_round_up (Zpos m) r lo))
        (Fin (product_round_down (Zpos m) r hi))) z).
    { split; [exact Hword|]; split; apply Z.leb_le; assumption. }
    destruct (product_round_up (Zpos m) r lo =? product_round_down (Zpos m) r hi)
      eqn:Hpoint.
    + apply Z.eqb_eq in Hpoint; split; [exact (conj Hword Hinterval)|].
      split; [exact Hword|]; split; [exact Hword|]; rewrite Z.mod_0_r; lia.
    + exact (conj (conj Hword Hinterval) (conj Hword (conj Hword Hz))).
  - destruct Hcanonical as [[Hzero _]|[[Hpositive _] _]]; lia.
Qed.

Lemma product_finite_value : forall i lo hi, interval_finite i = Some (lo, hi) ->
  i = Itv (Fin lo) (Fin hi).
Proof.
  intros [|[|l|] [|h|]] lo hi Hfinite; cbn in Hfinite; try discriminate.
  now inversion Hfinite.
Qed.

Lemma product_clip_endpoint : forall w i lo hi z,
  interval_finite (interval_clip w i) = Some (lo, hi) -> lo <= z <= hi ->
  interval_pgamma w i z.
Proof.
  intros w i lo hi z Hfinite Hz.
  pose proof (product_clip_shape_holds w i) as Hshape.
  unfold product_clip_shape in Hshape.
  pose proof (product_finite_value _ _ _ Hfinite) as Hvalue; rewrite Hvalue in Hshape.
  assert (Hclip : interval_pgamma w (interval_clip w i) z).
  { rewrite Hvalue; split; [unfold is_word; lia|].
    split; apply Z.leb_le; lia. }
  eapply (pgamma_monotone (interval_word_laws [])); [|exact Hclip].
  apply interval_meet_lower_left.
Qed.

Lemma product_cong_endpoint : forall w i c m r lo hi z,
  interval_finite (interval_clip w i) = Some (lo, hi) ->
  cong_norm w c = Cong m r -> lo <= z <= hi -> (z - r) mod m = 0 ->
  product_pgamma interval_pgamma cong_gamma w (i, c) z.
Proof.
  intros w i c m r lo hi z Hfinite Hnormal Hz Hresidue.
  pose proof (product_clip_endpoint w i lo hi z Hfinite Hz) as Hinterval.
  split; [exact (proj1 Hinterval)|split; [exact Hinterval|]].
  apply (proj1 (cong_norm_gamma w c z)); rewrite Hnormal.
  exact (conj (proj1 Hinterval) Hresidue).
Qed.

Definition interval_cong_shape (w : width) (pq result : interval * cong) : Prop :=
  result = (IBot, CBot) \/
  exists lo hi, result = (Itv (Fin lo) (Fin hi),
    if lo =? hi then Cong 0 lo else cong_norm w (snd pq)) /\
    lo <= hi /\ product_pgamma interval_pgamma cong_gamma w pq lo /\
    product_pgamma interval_pgamma cong_gamma w pq hi.

Lemma reduce_interval_cong_shape : forall w pq,
  interval_cong_shape w pq (reduce_interval_cong w pq).
Proof.
  intros w [i c]; unfold interval_cong_shape, reduce_interval_cong; cbn [fst snd].
  destruct (interval_finite (interval_clip w i)) as [[lo hi]|] eqn:Hfinite;
    [|left; reflexivity].
  pose proof (cong_norm_canonical w c) as Hcanonical.
  destruct (cong_norm w c) as [|m r] eqn:Hnormal; [left; reflexivity|].
  destruct m as [|m|m].
  - destruct ((lo <=? r) && (r <=? hi)) eqn:Hinside; [|left; reflexivity].
    apply andb_true_iff in Hinside as [Hlo Hhi]; apply Z.leb_le in Hlo;
      apply Z.leb_le in Hhi.
    right; exists r, r; rewrite Z.eqb_refl; split; [reflexivity|].
    split; [lia|split]; eapply product_cong_endpoint;
      try eassumption; [lia|rewrite Z.sub_diag; reflexivity|lia|rewrite Z.sub_diag; reflexivity].
  - destruct (product_round_up (Zpos m) r lo <=? product_round_down (Zpos m) r hi)
      eqn:Hordered; [|left; reflexivity].
    apply Z.leb_le in Hordered.
    pose proof (product_round_inward (Zpos m) r lo hi ltac:(lia)) as Hinward.
    right; exists (product_round_up (Zpos m) r lo), (product_round_down (Zpos m) r hi).
    split; [reflexivity|split; [exact Hordered|split]].
    + eapply product_cong_endpoint; try eassumption; [lia|].
      apply product_round_up_congruent; lia.
    + eapply product_cong_endpoint; try eassumption; [lia|].
      apply product_round_down_congruent; lia.
  - destruct Hcanonical as [[Hzero _]|[[Hpositive _] _]]; lia.
Qed.

Lemma product_interval_endpoint_lower : forall ts i lo hi,
  gamma interval_gamma i lo -> gamma interval_gamma i hi ->
  leb (interval_lattice ts) (Itv (Fin lo) (Fin hi)) i = true.
Proof.
  intros ts [|lower upper] lo hi Hlo Hhi; [contradiction|].
  apply andb_true_iff; exact (conj (proj1 Hlo) (proj2 Hhi)).
Qed.

Lemma product_cong_exact_lower : forall w c z, cong_gamma w c z ->
  cong_leb w (Cong 0 z) c = true.
Proof.
  intros w c z Hc; pose proof (cong_gamma_word w c z Hc) as Hword.
  apply (proj2 (cong_norm_gamma w c z)) in Hc; unfold cong_leb.
  rewrite (cong_canonical_fixed w (Cong 0 z) (or_introl (conj eq_refl Hword))).
  destruct (cong_norm w c) as [|m r]; [contradiction|].
  apply cong_raw_leb_spec; split; [exists 0; ring|].
  apply cong_mod_divide; exact (proj2 Hc).
Qed.

Lemma product_cong_norm_order : forall w a b,
  cong_leb w a b = true -> cong_leb w (cong_norm w a) b = true.
Proof.
  intros w a b Hle; unfold cong_leb in *; now rewrite cong_norm_idempotent.
Qed.

(** Interval/congruence reduction only refines its input components. *)
Theorem reduce_interval_cong_lower : forall thresholds w pq,
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w))
    (reduce_interval_cong w pq) pq = true.
Proof.
  intros thresholds w [i c].
  destruct (reduce_interval_cong_shape w (i, c)) as [Hbottom|[lo [hi [Hshape
    [Hordered [[Hwordlo [[_ Hil] Hcl]] [Hwordhi [[_ Hih] Hch]]]]]]]].
  - rewrite Hbottom; apply (bot_least (product_laws _ _ (interval_laws thresholds)
      (cong_laws w))).
  - rewrite Hshape; apply andb_true_iff; split.
    + now apply product_interval_endpoint_lower.
    + destruct (lo =? hi).
      * now apply product_cong_exact_lower.
      * apply product_cong_norm_order; apply cong_leb_refl.
Qed.

(** Empty components produce the canonical interval/congruence bottom pair. *)
Theorem reduce_interval_cong_empty : forall thresholds w,
  reduction_empty (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w).
Proof.
  intros thresholds w i c [Hi|Hc].
  - destruct i; [reflexivity|discriminate].
  - change (cong_leb w c CBot = true) in Hc.
    unfold cong_leb in Hc; cbn [cong_norm] in Hc.
    unfold reduce_interval_cong; cbn [fst snd].
    destruct (cong_norm w c); [|discriminate].
    destruct (interval_finite (interval_clip w i)) as [[lo hi]|]; reflexivity.
Qed.

Lemma product_interval_cong_monotone : forall thresholds w x y z,
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w)) x y = true ->
  product_pgamma interval_pgamma cong_gamma w x z ->
  product_pgamma interval_pgamma cong_gamma w y z.
Proof.
  intros thresholds w [i c] [j d] z Hle [Hword [Hi Hc]].
  apply andb_true_iff in Hle as [Hij Hcd].
  split; [exact Hword|split].
  - eapply (pgamma_monotone (interval_word_laws thresholds)); eassumption.
  - exact (cong_gamma_monotone w c d z Hcd Hc).
Qed.

Lemma reduce_interval_cong_keeps : forall w pq z,
  product_pgamma interval_pgamma cong_gamma w pq z ->
  product_pgamma interval_pgamma cong_gamma w (reduce_interval_cong w pq) z.
Proof.
  intros w pq z [Hword [Hi Hc]].
  pose proof (reduce_gamma (reduce_interval_cong_sound w) pq z
    (conj (conj Hword Hi) (conj Hword Hc))) as [[Hrange Hi'] [_ Hc']].
  exact (conj Hrange (conj Hi' Hc')).
Qed.

Lemma product_cong_norm_both_order : forall w a b,
  cong_leb w a b = true -> cong_leb w (cong_norm w a) (cong_norm w b) = true.
Proof.
  intros w a b Hle; unfold cong_leb in *; now rewrite !cong_norm_idempotent.
Qed.

Lemma interval_cong_shape_order : forall thresholds w x y rx ry,
  interval_cong_shape w x rx -> interval_cong_shape w y ry ->
  cong_leb w (snd x) (snd y) = true ->
  (forall z, product_pgamma interval_pgamma cong_gamma w x z ->
    product_pgamma interval_pgamma cong_gamma w ry z) ->
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w)) rx ry = true.
Proof.
  intros thresholds w x y rx ry Hx Hy Hcong Hcross.
  destruct Hx as [->|[lo [hi [-> [Hordered [Hlo Hhi]]]]]].
  - apply (bot_least (product_laws _ _ (interval_laws thresholds) (cong_laws w))).
  - specialize (Hcross lo Hlo) as Hlo'; specialize (Hcross hi Hhi) as Hhi'.
    destruct Hy as [->|[lo' [hi' [-> [Hordered' [Hlower Hupper]]]]]].
    + destruct Hlo' as [_ [[_ Hbot] _]]; contradiction.
    + destruct Hlo' as [Hwordlo [[_ Hil] Hcl]], Hhi' as [Hwordhi [[_ Hih] Hch]].
      apply andb_true_iff; split.
      * eapply product_interval_endpoint_lower; eassumption.
      * destruct (lo =? hi) eqn:Hpoint.
        -- now apply product_cong_exact_lower.
        -- destruct (lo' =? hi') eqn:Hpoint'.
           ++ apply Z.eqb_eq in Hpoint'; subst hi'.
              cbn [interval_gamma gamma bound_leb fst snd] in Hil, Hih.
              destruct Hil as [Hlow _], Hih as [_ Hhigh].
              apply Z.leb_le in Hlow; apply Z.leb_le in Hhigh.
              assert (Heq : lo = hi) by lia; subst hi.
              now rewrite Z.eqb_refl in Hpoint.
           ++ now apply product_cong_norm_both_order.
Qed.

(** Refining either component can only refine the reduced pair. *)
Theorem reduce_interval_cong_monotone : forall thresholds w x y,
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w)) x y = true ->
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w))
    (reduce_interval_cong w x) (reduce_interval_cong w y) = true.
Proof.
  intros thresholds w x y Hle; apply interval_cong_shape_order with (x := x) (y := y).
  - apply reduce_interval_cong_shape.
  - apply reduce_interval_cong_shape.
  - apply andb_true_iff in Hle; exact (proj2 Hle).
  - intros z Hz; apply reduce_interval_cong_keeps.
    eapply product_interval_cong_monotone; eassumption.
Qed.

Lemma reduce_interval_cong_self_shape : forall w pq,
  interval_cong_shape w (reduce_interval_cong w pq) (reduce_interval_cong w pq).
Proof.
  intros w pq; pose proof (reduce_interval_cong_shape w pq) as Hshape.
  destruct Hshape as [Hbottom|[lo [hi [Hvalue [Hordered [Hlo Hhi]]]]]].
  - left; exact Hbottom.
  - right; exists lo, hi; split.
    + rewrite Hvalue; cbn [snd].
      destruct (lo =? hi) eqn:Hpoint; [reflexivity|].
      now rewrite cong_norm_idempotent.
    + split; [exact Hordered|split]; now apply reduce_interval_cong_keeps.
Qed.

(** A second interval/congruence reduction adds no information in the product preorder. *)
Theorem reduce_interval_cong_idempotent : forall thresholds w pq,
  leb (product_lattice (interval_lattice thresholds) (cong_lattice w))
    (reduce_interval_cong w pq) (reduce_interval_cong w (reduce_interval_cong w pq)) = true.
Proof.
  intros thresholds w pq; apply interval_cong_shape_order with
    (x := reduce_interval_cong w pq) (y := reduce_interval_cong w pq).
  - apply reduce_interval_cong_self_shape.
  - apply reduce_interval_cong_shape.
  - apply cong_leb_refl.
  - apply reduce_interval_cong_keeps.
Qed.

(** Interval and congruence reduction preserves meaning and is a stable monotone refinement. *)
Theorem reduce_interval_cong_laws : forall thresholds w,
  reduction_laws (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w) /\
  reduction_sound (word_payload_concretisation interval_pgamma w)
    (word_payload_concretisation cong_gamma w) (reduce_interval_cong w) /\
  reduction_empty (interval_lattice thresholds) (cong_lattice w) (reduce_interval_cong w).
Proof.
  intros thresholds w; split; [constructor|split].
  - apply reduce_interval_cong_lower.
  - apply reduce_interval_cong_monotone.
  - apply reduce_interval_cong_idempotent.
  - apply reduce_interval_cong_sound.
  - apply reduce_interval_cong_empty.
Qed.

(** The interval/congruence product lifts to a sound tagged numeric domain. *)
Theorem interval_cong_numeric_laws : forall thresholds : list Z,
  numeric_laws (tagged_domain (interval_cong_domain thresholds))
    (tagged_gamma (product_pgamma interval_pgamma cong_gamma)).
Proof.
  intro thresholds; apply tagged_numeric_laws; apply product_word_laws.
  - apply interval_word_laws.
  - apply cong_word_laws.
  - intro w; exact (proj1 (reduce_interval_cong_laws thresholds w)).
  - intro w; exact (proj1 (proj2 (reduce_interval_cong_laws thresholds w))).
Qed.

(** * Structural selection of compatible words *)

Definition product_minimum (P : Z -> Prop) (lo : Z) (answer : option Z) : Prop :=
  match answer with
  | None => forall x, P x -> lo <= x -> False
  | Some x => P x /\ lo <= x /\ forall y, P y -> lo <= y -> x <= y
  end.

Definition product_free_digit (lo upper : Z) : Z :=
  if upper =? lo / 2 then lo mod 2 else 0.

Lemma product_half_up : forall lo,
  lo <= 2 * ((lo + 1) / 2) /\ forall v, lo <= 2 * v -> (lo + 1) / 2 <= v.
Proof.
  intro lo; pose proof (Z.div_mod (lo + 1) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (lo + 1) 2 ltac:(lia)); split; intros; lia.
Qed.

Lemma product_half_down : forall lo v, lo <= 2 * v + 1 <-> lo / 2 <= v.
Proof.
  intros lo v; pose proof (Z.div_mod lo 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound lo 2 ltac:(lia)); lia.
Qed.

Lemma product_free_digit_bounds : forall lo v, lo / 2 <= v ->
  0 <= product_free_digit lo v <= 1 /\ lo <= 2 * v + product_free_digit lo v /\
  forall u b, v <= u -> 0 <= b <= 1 -> lo <= 2 * u + b ->
    2 * v + product_free_digit lo v <= 2 * u + b.
Proof.
  intros lo v Hupper; unfold product_free_digit.
  pose proof (Z.div_mod lo 2 ltac:(lia)) as Hdivision.
  pose proof (Z.mod_pos_bound lo 2 ltac:(lia)) as Hremainder.
  destruct (v =? lo / 2) eqn:Heq.
  - apply Z.eqb_eq in Heq; subst v; split; [lia|split; [lia|intros; lia]].
  - apply Z.eqb_neq in Heq; split; [lia|split; [lia|intros; lia]].
Qed.

Lemma product_minimum_even : forall P lo answer,
  product_minimum P ((lo + 1) / 2) answer ->
  product_minimum (fun x => exists v, P v /\ x = 2 * v) lo
    (option_map (fun v => 2 * v) answer).
Proof.
  intros P lo [v|] Hmin; cbn [product_minimum option_map] in Hmin |- *.
  - destruct Hmin as [Hv [Hlo Hleast]]; split; [exists v; auto|split].
    + pose proof (proj1 (product_half_up lo)); lia.
    + intros x [u [Hu ->]] Hx; apply (proj2 (product_half_up lo)) in Hx.
      specialize (Hleast u Hu Hx); lia.
  - intros x [v [Hv ->]] Hx; apply (proj2 (product_half_up lo)) in Hx.
    exact (Hmin v Hv Hx).
Qed.

Lemma product_minimum_odd : forall P lo answer,
  product_minimum P (lo / 2) answer ->
  product_minimum (fun x => exists v, P v /\ x = 2 * v + 1) lo
    (option_map (fun v => 2 * v + 1) answer).
Proof.
  intros P lo [v|] Hmin; cbn [product_minimum option_map] in Hmin |- *.
  - destruct Hmin as [Hv [Hlo Hleast]]; split; [exists v; auto|split].
    + now apply product_half_down.
    + intros x [u [Hu ->]] Hx; apply product_half_down in Hx.
      specialize (Hleast u Hu Hx); lia.
  - intros x [v [Hv ->]] Hx; apply product_half_down in Hx.
    exact (Hmin v Hv Hx).
Qed.

Lemma product_minimum_free : forall P lo answer,
  product_minimum P (lo / 2) answer ->
  product_minimum (fun x => exists v b, P v /\ 0 <= b <= 1 /\ x = 2 * v + b) lo
    (option_map (fun v => 2 * v + product_free_digit lo v) answer).
Proof.
  intros P lo [v|] Hmin; cbn [product_minimum option_map] in Hmin |- *.
  - destruct Hmin as [Hv [Hlo Hleast]].
    destruct (product_free_digit_bounds lo v Hlo) as [Hdigit [Hbound Hlast]].
    split; [exists v, (product_free_digit lo v); auto|split; [exact Hbound|]].
    intros x [u [b [Hu [Hb ->]]]] Hx.
    assert (Hquotient : lo / 2 <= u) by (apply product_half_down; lia).
    exact (Hlast u b (Hleast u Hu Hquotient) Hb Hx).
  - intros x [v [b [Hv [Hb ->]]]] Hx.
    apply (Hmin v Hv); apply product_half_down; lia.
Qed.

Lemma product_minimum_equiv : forall P Q lo answer,
  (forall x, P x <-> Q x) -> product_minimum P lo answer -> product_minimum Q lo answer.
Proof.
  intros P Q lo [v|] Hequiv Hmin; cbn in *.
  - destruct Hmin as [Hv [Hlo Hleast]]; split; [now apply Hequiv|split; [exact Hlo|]].
    intros x Hx Hbound; apply Hleast; [now apply Hequiv|exact Hbound].
  - intros x Hx Hbound; apply (Hmin x); [now apply Hequiv|exact Hbound].
Qed.

Fixpoint product_bit_depth (p : positive) : Z :=
  match p with
  | xH => 0
  | xO q | xI q => 1 + product_bit_depth q
  end.

Fixpoint product_bit_values (p : positive) (zero one x : Z) : Prop :=
  match p with
  | xH => x = 0
  | xO q | xI q =>
    exists v b, product_bit_values q (zero / 2) (one / 2) v /\
      0 <= b <= 1 /\ (Z.odd zero = true -> b = 0) /\
      (Z.odd one = true -> b = 1) /\ x = 2 * v + b
  end.

Fixpoint product_bit_ceiling (p : positive) (zero one lo : Z) : option Z :=
  match p with
  | xH => if lo <=? 0 then Some 0 else None
  | xO q | xI q =>
    match Z.odd zero, Z.odd one with
    | true, true => None
    | true, false => option_map (fun v => 2 * v)
        (product_bit_ceiling q (zero / 2) (one / 2) ((lo + 1) / 2))
    | false, true => option_map (fun v => 2 * v + 1)
        (product_bit_ceiling q (zero / 2) (one / 2) (lo / 2))
    | false, false => option_map (fun v => 2 * v + product_free_digit lo v)
        (product_bit_ceiling q (zero / 2) (one / 2) (lo / 2))
    end
  end.

Lemma product_bit_values_cases : forall p zero one x,
  (exists v b, product_bit_values p (zero / 2) (one / 2) v /\
    0 <= b <= 1 /\ (Z.odd zero = true -> b = 0) /\
    (Z.odd one = true -> b = 1) /\ x = 2 * v + b) <->
  match Z.odd zero, Z.odd one with
  | true, true => False
  | true, false => exists v, product_bit_values p (zero / 2) (one / 2) v /\ x = 2 * v
  | false, true => exists v, product_bit_values p (zero / 2) (one / 2) v /\ x = 2 * v + 1
  | false, false => exists v b, product_bit_values p (zero / 2) (one / 2) v /\
      0 <= b <= 1 /\ x = 2 * v + b
  end.
Proof.
  intros p zero one x; destruct (Z.odd zero), (Z.odd one); split.
  - intros [v [b [Hv [Hb [Hz [Ho Hx]]]]]]; specialize (Hz eq_refl); specialize (Ho eq_refl).
    lia.
  - contradiction.
  - intros [v [b [Hv [Hb [Hz [Ho Hx]]]]]]; specialize (Hz eq_refl).
    exists v; split; [exact Hv|lia].
  - intros [v [Hv Hx]]; exists v, 0; repeat split; try assumption; try discriminate; lia.
  - intros [v [b [Hv [Hb [Hz [Ho Hx]]]]]]; specialize (Ho eq_refl).
    exists v; split; [exact Hv|lia].
  - intros [v [Hv Hx]]; exists v, 1; repeat split; try assumption; try discriminate; lia.
  - intros [v [b [Hv [Hb [Hz [Ho Hx]]]]]]; exists v, b; auto.
  - intros [v [b [Hv [Hb Hx]]]]; exists v, b; repeat split;
      try assumption; try discriminate; lia.
Qed.

(** The structural selector returns exactly the least compatible value above its bound. *)
Theorem product_bit_ceiling_correct : forall p zero one lo,
  product_minimum (product_bit_values p zero one) lo (product_bit_ceiling p zero one lo).
Proof.
  intro p; induction p as [p IH|p IH|]; intros zero one lo.
  1,2: cbn [product_bit_ceiling product_bit_values];
    eapply product_minimum_equiv;
      [intro x; symmetry; apply product_bit_values_cases|];
    destruct (Z.odd zero), (Z.odd one).
  - intros x Hfalse; contradiction.
  - apply product_minimum_even; apply IH.
  - apply product_minimum_odd; apply IH.
  - apply product_minimum_free; apply IH.
  - intros x Hfalse; contradiction.
  - apply product_minimum_even; apply IH.
  - apply product_minimum_odd; apply IH.
  - apply product_minimum_free; apply IH.
  - cbn [product_bit_ceiling product_bit_values]; destruct (lo <=? 0) eqn:Hbound.
    + apply Z.leb_le in Hbound; split; [reflexivity|split; [exact Hbound|intros; lia]].
    + apply Z.leb_gt in Hbound; intros x -> Hx; lia.
Qed.

Definition product_numeric_bits (k zero one x : Z) : Prop :=
  0 <= x < 2^k /\
  (forall i, 0 <= i < k -> Z.testbit zero i = true -> Z.testbit x i = false) /\
  (forall i, 0 <= i < k -> Z.testbit one i = true -> Z.testbit x i = true).

Lemma product_double_quotient : forall v b, 0 <= b <= 1 -> (2 * v + b) / 2 = v.
Proof.
  intros v b Hb; symmetry; apply Z.div_unique_pos with (r := b); [lia|ring].
Qed.

Lemma product_double_bit0 : forall v b, 0 <= b <= 1 ->
  Z.testbit (2 * v + b) 0 = (b =? 1).
Proof.
  intros v b Hb; destruct (Z.eq_dec b 0) as [->|Hnonzero].
  - rewrite Z.add_0_r; apply Z.testbit_even_0.
  - assert (b = 1) by lia; subst b; apply Z.testbit_odd_0.
Qed.

Lemma product_lower_bit : forall x i, 0 < i -> Z.testbit (x / 2) (i - 1) = Z.testbit x i.
Proof.
  intros x i Hi; rewrite Z.div2_bits by lia; f_equal; lia.
Qed.

Lemma product_numeric_bits_split : forall k zero one x, 0 <= k ->
  product_numeric_bits (1 + k) zero one x <->
  exists v b, product_numeric_bits k (zero / 2) (one / 2) v /\
    0 <= b <= 1 /\ (Z.odd zero = true -> b = 0) /\
    (Z.odd one = true -> b = 1) /\ x = 2 * v + b.
Proof.
  intros k zero one x Hk; unfold product_numeric_bits.
  replace (1 + k) with (Z.succ k) by lia; rewrite Z.pow_succ_r by lia.
  split.
  - intros [Hrange [Hz Ho]]. exists (x / 2), (x mod 2).
    pose proof (Z.div_mod x 2 ltac:(lia)) as Hdivision.
    pose proof (Z.mod_pos_bound x 2 ltac:(lia)) as Hremainder.
    split.
    + split; [lia|split]; intros i Hi Hbit;
        rewrite Z.div2_bits in Hbit |- * by lia;
        [apply Hz|apply Ho]; [lia|exact Hbit|lia|exact Hbit].
    + split; [lia|split].
      * intro Hbit; rewrite Zmod_odd.
        pose proof (Hz 0 ltac:(lia) ltac:(now rewrite Z.bit0_odd)) as Hclear.
        rewrite Z.bit0_odd in Hclear; now rewrite Hclear.
      * split.
        -- intro Hbit; rewrite Zmod_odd.
           pose proof (Ho 0 ltac:(lia) ltac:(now rewrite Z.bit0_odd)) as Hset.
           rewrite Z.bit0_odd in Hset; now rewrite Hset.
        -- lia.
  - intros [v [b [[Hrange [Hz Ho]] [Hb [Hclear [Hset ->]]]]]].
    split; [nia|split]; intros i Hi Hbit;
      destruct (Z.eq_dec i 0) as [->|Hnonzero].
    + rewrite product_double_bit0 by exact Hb.
      rewrite Z.bit0_odd in Hbit; rewrite (Hclear Hbit); reflexivity.
    + rewrite <- (product_lower_bit (2 * v + b) i ltac:(lia)),
        product_double_quotient by exact Hb.
      apply Hz; [lia|]; rewrite product_lower_bit by lia; exact Hbit.
    + rewrite product_double_bit0 by exact Hb.
      rewrite Z.bit0_odd in Hbit; rewrite (Hset Hbit); reflexivity.
    + rewrite <- (product_lower_bit (2 * v + b) i ltac:(lia)),
        product_double_quotient by exact Hb.
      apply Ho; [lia|]; rewrite product_lower_bit by lia; exact Hbit.
Qed.

Lemma product_bit_depth_nonnegative : forall p, 0 <= product_bit_depth p.
Proof.
  intro p; induction p; cbn [product_bit_depth]; lia.
Qed.

(** Recursive digit constraints agree with the bitwise word predicate. *)
Theorem product_bit_values_correct : forall p zero one x,
  product_bit_values p zero one x <-> product_numeric_bits (product_bit_depth p) zero one x.
Proof.
  intro p; induction p as [p IH|p IH|]; intros zero one x.
  - cbn [product_bit_values product_bit_depth].
    rewrite product_numeric_bits_split by apply product_bit_depth_nonnegative; split.
    + intros [v [b [Hv Hrest]]]; exists v, b; split; [now apply IH|exact Hrest].
    + intros [v [b [Hv Hrest]]]; exists v, b; split; [now apply IH|exact Hrest].
  - cbn [product_bit_values product_bit_depth].
    rewrite product_numeric_bits_split by apply product_bit_depth_nonnegative; split.
    + intros [v [b [Hv Hrest]]]; exists v, b; split; [now apply IH|exact Hrest].
    + intros [v [b [Hv Hrest]]]; exists v, b; split; [now apply IH|exact Hrest].
  - unfold product_numeric_bits; cbn [product_bit_values product_bit_depth Z.pow].
    split.
    + intro Heq; subst x; split; [lia|split; intros; lia].
    + intros [Hrange _]; lia.
Qed.

Definition product_word_tree (w : width) : positive := N.iter (Npos w) xO xH.

Lemma product_iter_depth : forall n,
  product_bit_depth (N.iter n xO xH) = Z.of_N n.
Proof.
  intro n; induction n using N.peano_ind.
  - reflexivity.
  - rewrite N.iter_succ; cbn [product_bit_depth]; rewrite IHn, N2Z.inj_succ; lia.
Qed.

Lemma product_word_tree_depth : forall w, product_bit_depth (product_word_tree w) = Zpos w.
Proof.
  intro w; apply product_iter_depth.
Qed.

(** The public endpoint selector visits one stored binary digit per word bit. *)
Definition product_tnum_ceiling (w : width) (a : tnum) (lo : Z) : option Z :=
  product_bit_ceiling (product_word_tree w) (zeros a) (ones a) lo.

Theorem product_tnum_ceiling_correct : forall w a lo,
  product_minimum (fun x => is_word w x /\ tnum_gamma w a x) lo
    (product_tnum_ceiling w a lo).
Proof.
  intros w a lo; unfold product_tnum_ceiling.
  eapply product_minimum_equiv; [|apply product_bit_ceiling_correct].
  intro x; rewrite product_bit_values_correct, product_word_tree_depth.
  unfold product_numeric_bits, is_word, modulus; rewrite tnum_gamma_bits; tauto.
Qed.

Definition product_maximum (P : Z -> Prop) (hi : Z) (answer : option Z) : Prop :=
  match answer with
  | None => forall x, P x -> x <= hi -> False
  | Some x => P x /\ x <= hi /\ forall y, P y -> y <= hi -> y <= x
  end.

Lemma product_tnum_mirror : forall w a x, is_word w x -> tnum_gamma w a x ->
  is_word w (modulus w - 1 - x) /\
  tnum_gamma w (tnum_not w a) (modulus w - 1 - x).
Proof.
  intros w a x Hword Hbits.
  pose proof (tnum_not_sound w a x Hbits) as Hnot.
  unfold wnot in Hnot; rewrite (wrap_id w x Hword) in Hnot.
  split; [unfold is_word in *; lia|exact Hnot].
Qed.

Lemma product_tnum_unmirror : forall w a x, is_word w x ->
  tnum_gamma w (tnum_not w a) x ->
  is_word w (modulus w - 1 - x) /\ tnum_gamma w a (modulus w - 1 - x).
Proof.
  intros w a x Hword Hbits.
  destruct (product_tnum_mirror w (tnum_not w a) x Hword Hbits) as [Hrange Hmirror].
  assert (Hdouble : tnum_not w (tnum_not w a) = tnum_normalise w a).
  { unfold tnum_not, tnum_normalise; cbn [zeros ones]; now rewrite !wrap_wrap. }
  rewrite Hdouble, tnum_normalise_sound in Hmirror; exact (conj Hrange Hmirror).
Qed.

Definition product_tnum_floor (w : width) (a : tnum) (hi : Z) : option Z :=
  option_map (fun x => modulus w - 1 - x)
    (product_tnum_ceiling w (tnum_not w a) (modulus w - 1 - hi)).

(** Mirroring the least selector gives the greatest compatible word below an upper bound. *)
Theorem product_tnum_floor_correct : forall w a hi,
  product_maximum (fun x => is_word w x /\ tnum_gamma w a x) hi
    (product_tnum_floor w a hi).
Proof.
  intros w a hi; unfold product_tnum_floor.
  pose proof (product_tnum_ceiling_correct w (tnum_not w a) (modulus w - 1 - hi)) as Hmin.
  destruct (product_tnum_ceiling w (tnum_not w a) (modulus w - 1 - hi)) as [v|];
    cbn [product_minimum product_maximum option_map] in Hmin |- *.
  - destruct Hmin as [[Hword Hbits] [Hbound Hleast]].
    split; [now apply product_tnum_unmirror|split; [lia|]].
    intros y [Hyword Hybits] Hy.
    destruct (product_tnum_mirror w a y Hyword Hybits) as [Hmy Hby].
    specialize (Hleast _ (conj Hmy Hby) ltac:(lia)); lia.
  - intros x [Hword Hbits] Hbound.
    destruct (product_tnum_mirror w a x Hword Hbits) as [Hmx Hbx].
    apply (Hmin _ (conj Hmx Hbx)); lia.
Qed.

Definition product_linear_bounds (w : width) (a : tnum) (lo hi : Z) : option (Z * Z) :=
  match product_tnum_ceiling w a lo, product_tnum_floor w a hi with
  | Some first, Some last => if first <=? last then Some (first, last) else None
  | _, _ => None
  end.

Definition product_bounds (P : Z -> Prop) (lo hi : Z) (answer : option (Z * Z)) : Prop :=
  match answer with
  | None => forall x, P x -> lo <= x <= hi -> False
  | Some (first, last) =>
    P first /\ P last /\ lo <= first /\ first <= last /\ last <= hi /\
    forall x, P x -> lo <= x <= hi -> first <= x <= last
  end.

(** Linear endpoint selection returns the first and last compatible word in the closed interval. *)
Theorem product_linear_bounds_correct : forall w a lo hi,
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) lo hi
    (product_linear_bounds w a lo hi).
Proof.
  intros w a lo hi; unfold product_linear_bounds.
  pose proof (product_tnum_ceiling_correct w a lo) as Hmin.
  pose proof (product_tnum_floor_correct w a hi) as Hmax.
  destruct (product_tnum_ceiling w a lo) as [first|],
    (product_tnum_floor w a hi) as [last|];
    cbn [product_minimum product_maximum] in Hmin, Hmax.
  - destruct Hmin as [Hfirst [Hlo Hleast]], Hmax as [Hlast [Hhi Hgreatest]].
    destruct (first <=? last) eqn:Horder.
    + apply Z.leb_le in Horder; cbn [product_bounds].
      split; [exact Hfirst|split; [exact Hlast|split; [exact Hlo|split;
        [exact Horder|split; [exact Hhi|]]]]].
      intros x Hx [Hxl Hxh]; split; [now apply Hleast|now apply Hgreatest].
    + apply Z.leb_gt in Horder; intros x Hx [Hxl Hxh].
      specialize (Hleast x Hx Hxl); specialize (Hgreatest x Hx Hxh); lia.
  - intros x Hx [Hxl Hxh]; exact (Hmax x Hx Hxh).
  - intros x Hx [Hxl Hxh]; exact (Hmin x Hx Hxl).
  - intros x Hx [Hxl Hxh]; exact (Hmin x Hx Hxl).
Qed.

(** * Common leading bits of a linear interval *)

Fixpoint product_bit_pack (p : positive) (f : Z -> bool) : Z :=
  match p with
  | xH => 0
  | xO q | xI q =>
    let lower := product_bit_pack q f in
    if f (product_bit_depth q) then Z.setbit lower (product_bit_depth q) else lower
  end.

Lemma product_bit_pack_step : forall k lower f, 0 <= k ->
  (forall i, 0 <= i -> Z.testbit lower i = if i <? k then f i else false) ->
  forall i, 0 <= i ->
  Z.testbit (if f k then Z.setbit lower k else lower) i =
    if i <? 1 + k then f i else false.
Proof.
  intros k lower f Hk Hlower i Hi.
  destruct (Z.eq_dec i k) as [->|Hdifferent].
  - destruct (f k) eqn:Hf;
      rewrite ?Z.setbit_eqb, Hlower by assumption;
      rewrite (proj2 (Z.ltb_ge k k)), (proj2 (Z.ltb_lt k (1 + k))) by lia;
      rewrite ?Z.eqb_refl; reflexivity.
  - destruct (f k); rewrite ?Z.setbit_eqb, Hlower by assumption;
      rewrite ?(proj2 (Z.eqb_neq k i)) by lia;
      destruct (i <? k) eqn:Hlow.
    + apply Z.ltb_lt in Hlow; rewrite (proj2 (Z.ltb_lt i (1 + k))) by lia; reflexivity.
    + apply Z.ltb_ge in Hlow; rewrite (proj2 (Z.ltb_ge i (1 + k))) by lia; reflexivity.
    + apply Z.ltb_lt in Hlow; rewrite (proj2 (Z.ltb_lt i (1 + k))) by lia; reflexivity.
    + apply Z.ltb_ge in Hlow; rewrite (proj2 (Z.ltb_ge i (1 + k))) by lia; reflexivity.
Qed.

Lemma product_bit_pack_bits : forall p f i, 0 <= i ->
  Z.testbit (product_bit_pack p f) i = if i <? product_bit_depth p then f i else false.
Proof.
  intro p; induction p as [p IH|p IH|]; intros f i Hi.
  - apply product_bit_pack_step; [apply product_bit_depth_nonnegative|apply IH|exact Hi].
  - apply product_bit_pack_step; [apply product_bit_depth_nonnegative|apply IH|exact Hi].
  - cbn [product_bit_pack product_bit_depth]; rewrite Z.bits_0.
    rewrite (proj2 (Z.ltb_ge i 0)) by lia; reflexivity.
Qed.

Definition product_prefix (w : width) (lo hi : Z) : tnum :=
  Tnum
    (product_bit_pack (product_word_tree w) (fun i =>
      (lo / 2^i =? hi / 2^i) && negb (Z.testbit lo i)))
    (product_bit_pack (product_word_tree w) (fun i =>
      (lo / 2^i =? hi / 2^i) && Z.testbit lo i)).

Lemma product_prefix_bits : forall w lo hi i, 0 <= i < Zpos w ->
  Z.testbit (zeros (product_prefix w lo hi)) i =
    ((lo / 2^i =? hi / 2^i) && negb (Z.testbit lo i)) /\
  Z.testbit (ones (product_prefix w lo hi)) i =
    ((lo / 2^i =? hi / 2^i) && Z.testbit lo i).
Proof.
  intros w lo hi i Hi; cbn [product_prefix zeros ones].
  rewrite !product_bit_pack_bits, product_word_tree_depth by lia.
  rewrite (proj2 (Z.ltb_lt i (Zpos w))) by lia; split; reflexivity.
Qed.

Lemma product_quotient_between : forall lo hi x i, 0 <= i -> lo <= x <= hi ->
  lo / 2^i = hi / 2^i -> x / 2^i = lo / 2^i.
Proof.
  intros lo hi x i Hi Hbounds Heq.
  assert (Hpower : 0 < 2^i) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_le_mono lo x (2^i) Hpower ltac:(lia)).
  pose proof (Z.div_le_mono x hi (2^i) Hpower ltac:(lia)); lia.
Qed.

Lemma product_equal_quotient_bit : forall x y i, 0 <= i -> x / 2^i = y / 2^i ->
  Z.testbit x i = Z.testbit y i.
Proof.
  intros x y i Hi Heq; rewrite !Z.testbit_eqb by exact Hi; now rewrite Heq.
Qed.

(** Every shared leading bit of the endpoints holds throughout the linear interval. *)
Theorem product_prefix_sound : forall w lo hi x,
  lo <= x <= hi -> tnum_gamma w (product_prefix w lo hi) x.
Proof.
  intros w lo hi x Hbounds; apply tnum_gamma_bits; split; intros i Hi Hbit.
  - rewrite (proj1 (product_prefix_bits w lo hi i Hi)) in Hbit.
    apply andb_true_iff in Hbit as [Heq Hclear]; apply Z.eqb_eq in Heq.
    rewrite (product_equal_quotient_bit x lo i ltac:(lia)
      (product_quotient_between lo hi x i ltac:(lia) Hbounds Heq)).
    now apply negb_true_iff in Hclear.
  - rewrite (proj2 (product_prefix_bits w lo hi i Hi)) in Hbit.
    apply andb_true_iff in Hbit as [Heq Hset]; apply Z.eqb_eq in Heq.
    rewrite (product_equal_quotient_bit x lo i ltac:(lia)
      (product_quotient_between lo hi x i ltac:(lia) Hbounds Heq)); exact Hset.
Qed.

Lemma product_prefix_interval : forall lo hi lo' hi' i,
  0 <= i -> lo <= lo' <= hi' -> hi' <= hi -> lo / 2^i = hi / 2^i ->
  lo' / 2^i = hi' / 2^i /\ Z.testbit lo' i = Z.testbit lo i.
Proof.
  intros lo hi lo' hi' i Hi Hbounds Hupper Heq.
  pose proof (product_quotient_between lo hi lo' i Hi ltac:(lia) Heq) as Hlo.
  pose proof (product_quotient_between lo hi hi' i Hi ltac:(lia) Heq) as Hhi.
  split; [lia|now apply product_equal_quotient_bit].
Qed.

(** Shrinking a linear interval only adds common leading bits. *)
Theorem product_prefix_monotone : forall w lo hi lo' hi',
  lo <= lo' <= hi' -> hi' <= hi ->
  leb (tnum_lattice w) (product_prefix w lo' hi') (product_prefix w lo hi) = true.
Proof.
  intros w lo hi lo' hi' Hbounds Hupper; apply tnum_leb_bits; split; intros i Hi Hbit;
    rewrite (proj1 (product_prefix_bits w lo hi i Hi)) in Hbit ||
    rewrite (proj2 (product_prefix_bits w lo hi i Hi)) in Hbit.
  - apply andb_true_iff in Hbit as [Heq Hclear]; apply Z.eqb_eq in Heq.
    destruct (product_prefix_interval lo hi lo' hi' i ltac:(lia) Hbounds Hupper Heq)
      as [Hsame Hbit].
    rewrite (proj1 (product_prefix_bits w lo' hi' i Hi)), Hbit,
      (proj2 (Z.eqb_eq _ _) Hsame); exact Hclear.
  - apply andb_true_iff in Hbit as [Heq Hset]; apply Z.eqb_eq in Heq.
    destruct (product_prefix_interval lo hi lo' hi' i ltac:(lia) Hbounds Hupper Heq)
      as [Hsame Hbit].
    rewrite (proj2 (product_prefix_bits w lo' hi' i Hi)), Hbit,
      (proj2 (Z.eqb_eq _ _) Hsame); exact Hset.
Qed.

(** * Circular endpoint selection *)

Lemma product_arc_word_spec : forall w lo hi z,
  is_word w lo -> is_word w hi -> is_word w z ->
  (wrapped_gamma w (WItv lo hi) z <->
    if lo <=? hi then lo <= z <= hi else lo <= z \/ z <= hi).
Proof.
  intros w lo hi z Hlo Hhi Hz; rewrite wrapped_parts_raw_spec.
  cbn [wrapped_parts_raw]; rewrite (wrap_id w lo Hlo), (wrap_id w hi Hhi).
  destruct (lo <=? hi); cbn [fst snd]; unfold interval_pgamma, interval_gamma;
    cbn [gamma bound_leb]; rewrite !Z.leb_le; unfold is_word in *; intuition lia.
Qed.

Lemma product_offset_high : forall w origin x,
  is_word w origin -> is_word w x -> origin <= x -> wrapped_offset w origin x = x - origin.
Proof.
  intros w origin x Horigin Hx Hle; rewrite wrapped_offset_word_cases by assumption.
  now rewrite (proj2 (Z.leb_le origin x) Hle).
Qed.

Lemma product_offset_low : forall w origin x,
  is_word w origin -> is_word w x -> x < origin ->
  wrapped_offset w origin x = x - origin + modulus w.
Proof.
  intros w origin x Horigin Hx Hlt; rewrite wrapped_offset_word_cases by assumption.
  now rewrite (proj2 (Z.leb_gt origin x) Hlt).
Qed.

Definition product_arc_select (w : width) (a : tnum) (lo hi : Z) : option (Z * Z) :=
  if lo <=? hi then product_linear_bounds w a lo hi else
  match product_linear_bounds w a lo (modulus w - 1), product_linear_bounds w a 0 hi with
  | Some (first, _), Some (_, last) => Some (first, last)
  | Some bounds, None => Some bounds
  | None, Some bounds => Some bounds
  | None, None => None
  end.

Definition product_arc_bounds (w : width) (a : tnum) (lo hi : Z)
  (answer : option (Z * Z)) : Prop :=
  let P := product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) in
  match answer with
  | None => forall x, P x -> False
  | Some (first, last) => P first /\ P last /\
    wrapped_offset w lo first <= wrapped_offset w lo last /\
    forall x, P x -> wrapped_offset w lo first <= wrapped_offset w lo x <=
      wrapped_offset w lo last
  end.

Lemma product_arc_member : forall w a lo hi x,
  is_word w lo -> is_word w hi -> is_word w x -> tnum_gamma w a x ->
  (if lo <=? hi then lo <= x <= hi else lo <= x \/ x <= hi) ->
  product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) x.
Proof.
  intros w a lo hi x Hlo Hhi Hx Hbits Hrange.
  split; [exact Hx|split; [exact Hbits|]].
  now apply product_arc_word_spec.
Qed.

Lemma product_arc_nonwrapping : forall w a lo hi,
  is_word w lo -> is_word w hi -> lo <= hi ->
  product_arc_bounds w a lo hi (product_linear_bounds w a lo hi).
Proof.
  intros w a lo hi Hlo Hhi Horder.
  pose proof (product_linear_bounds_correct w a lo hi) as Hbounds.
  destruct (product_linear_bounds w a lo hi) as [[first last]|];
    cbn [product_bounds product_arc_bounds] in Hbounds |- *.
  - destruct Hbounds as [[Hfw Hfb] [[Hlw Hlb] [Hfirst [Hends [Hlast Hall]]]]].
    assert (Hfirstm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) first).
    { apply product_arc_member; try assumption;
        rewrite (proj2 (Z.leb_le lo hi) Horder); lia. }
    assert (Hlastm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) last).
    { apply product_arc_member; try assumption;
        rewrite (proj2 (Z.leb_le lo hi) Horder); lia. }
    split; [exact Hfirstm|split; [exact Hlastm|split]].
    + rewrite !product_offset_high by (try assumption; lia); lia.
    + intros x [Hx [Hb Ha]]; apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
      rewrite (proj2 (Z.leb_le lo hi) Horder) in Ha.
      specialize (Hall x (conj Hx Hb) Ha).
      rewrite !product_offset_high by (try assumption; lia); lia.
  - intros x [Hx [Hb Ha]]; apply (Hbounds x (conj Hx Hb)).
    apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
    now rewrite (proj2 (Z.leb_le lo hi) Horder) in Ha.
Qed.

Lemma product_arc_wrap_both : forall w a lo hi f1 l1 f2 l2,
  is_word w lo -> is_word w hi -> hi < lo ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) lo (modulus w - 1) (Some (f1, l1)) ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) 0 hi (Some (f2, l2)) ->
  product_arc_bounds w a lo hi (Some (f1, l2)).
Proof.
  intros w a lo hi f1 l1 f2 l2 Hlo Hhi Hwrap Hfirst Hlast.
  cbn [product_bounds product_arc_bounds] in Hfirst, Hlast |- *.
  destruct Hfirst as [[Hf1w Hf1b] [[Hl1w Hl1b] [Hf1 [Hord1 [Hl1 Hall1]]]]].
  destruct Hlast as [[Hf2w Hf2b] [[Hl2w Hl2b] [Hf2 [Hord2 [Hl2 Hall2]]]]].
  assert (Hfm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) f1).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      left; exact Hf1. }
  assert (Hlm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) l2).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      right; exact Hl2. }
  split; [exact Hfm|split; [exact Hlm|split]].
  + rewrite product_offset_high, product_offset_low by (try assumption; lia).
    unfold is_word in *; lia.
  + intros x [Hx [Hb Ha]]; apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
    rewrite (proj2 (Z.leb_gt lo hi) Hwrap) in Ha; destruct Ha as [Hupper|Hlower].
    * specialize (Hall1 x (conj Hx Hb) ltac:(unfold is_word in Hx; lia)).
      rewrite !product_offset_high, product_offset_low by (try assumption; lia).
      unfold is_word in *; lia.
    * specialize (Hall2 x (conj Hx Hb) ltac:(unfold is_word in Hx; lia)).
      rewrite product_offset_high, !product_offset_low by (try assumption; lia).
      unfold is_word in *; lia.
Qed.

Lemma product_arc_wrap_high : forall w a lo hi f1 l1,
  is_word w lo -> is_word w hi -> hi < lo ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) lo (modulus w - 1) (Some (f1, l1)) ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) 0 hi None ->
  product_arc_bounds w a lo hi (Some (f1, l1)).
Proof.
  intros w a lo hi f1 l1 Hlo Hhi Hwrap Hfirst Hlast.
  cbn [product_bounds product_arc_bounds] in Hfirst, Hlast |- *.
  destruct Hfirst as [[Hfw Hfb] [[Hlw Hlb] [Hfirstbound [Horder [Hlastbound Hall]]]]].
  assert (Hfm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) f1).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      left; exact Hfirstbound. }
  assert (Hlm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) l1).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      left; lia. }
  split; [exact Hfm|split; [exact Hlm|split]].
  + rewrite !product_offset_high by (try assumption; lia); lia.
  + intros x [Hx [Hb Ha]]; apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
    rewrite (proj2 (Z.leb_gt lo hi) Hwrap) in Ha; destruct Ha as [Hupper|Hlower].
    * specialize (Hall x (conj Hx Hb) ltac:(unfold is_word in Hx; lia)).
      rewrite !product_offset_high by (try assumption; lia); lia.
    * exfalso; apply (Hlast x (conj Hx Hb)); unfold is_word in Hx; lia.
Qed.

Lemma product_arc_wrap_low : forall w a lo hi f2 l2,
  is_word w lo -> is_word w hi -> hi < lo ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) lo (modulus w - 1) None ->
  product_bounds (fun x => is_word w x /\ tnum_gamma w a x) 0 hi (Some (f2, l2)) ->
  product_arc_bounds w a lo hi (Some (f2, l2)).
Proof.
  intros w a lo hi f2 l2 Hlo Hhi Hwrap Hfirst Hlast.
  cbn [product_bounds product_arc_bounds] in Hfirst, Hlast |- *.
  destruct Hlast as [[Hfw Hfb] [[Hlw Hlb] [Hfirstbound [Horder [Hlastbound Hall]]]]].
  assert (Hfm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) f2).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      right; lia. }
  assert (Hlm : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) l2).
  { apply product_arc_member; try assumption; rewrite (proj2 (Z.leb_gt lo hi) Hwrap);
      right; exact Hlastbound. }
  split; [exact Hfm|split; [exact Hlm|split]].
  + rewrite !product_offset_low by (try assumption; lia); lia.
  + intros x [Hx [Hb Ha]]; apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
    rewrite (proj2 (Z.leb_gt lo hi) Hwrap) in Ha; destruct Ha as [Hupper|Hlower].
    * exfalso; apply (Hfirst x (conj Hx Hb)); unfold is_word in Hx; lia.
    * specialize (Hall x (conj Hx Hb) ltac:(unfold is_word in Hx; lia)).
      rewrite !product_offset_low by (try assumption; lia); lia.
Qed.

Lemma product_arc_wrapping : forall w a lo hi,
  is_word w lo -> is_word w hi -> hi < lo ->
  product_arc_bounds w a lo hi (product_arc_select w a lo hi).
Proof.
  intros w a lo hi Hlo Hhi Hwrap; unfold product_arc_select.
  rewrite (proj2 (Z.leb_gt lo hi) Hwrap).
  pose proof (product_linear_bounds_correct w a lo (modulus w - 1)) as Hfirst.
  pose proof (product_linear_bounds_correct w a 0 hi) as Hlast.
  destruct (product_linear_bounds w a lo (modulus w - 1)) as [[f1 l1]|],
    (product_linear_bounds w a 0 hi) as [[f2 l2]|];
    cbn [product_bounds product_arc_bounds] in Hfirst, Hlast |- *.
  - exact (product_arc_wrap_both w a lo hi f1 l1 f2 l2 Hlo Hhi Hwrap Hfirst Hlast).
  - exact (product_arc_wrap_high w a lo hi f1 l1 Hlo Hhi Hwrap Hfirst Hlast).
  - exact (product_arc_wrap_low w a lo hi f2 l2 Hlo Hhi Hwrap Hfirst Hlast).
  - intros x [Hx [Hb Ha]]; apply (product_arc_word_spec w lo hi x Hlo Hhi Hx) in Ha.
    rewrite (proj2 (Z.leb_gt lo hi) Hwrap) in Ha; destruct Ha as [Hupper|Hlower].
    + apply (Hfirst x (conj Hx Hb)); unfold is_word in Hx; lia.
    + apply (Hlast x (conj Hx Hb)); unfold is_word in Hx; lia.
Qed.

(** The circular selector chooses the first and last shared words in the input arc's order. *)
Theorem product_arc_select_correct : forall w a lo hi,
  is_word w lo -> is_word w hi ->
  product_arc_bounds w a lo hi (product_arc_select w a lo hi).
Proof.
  intros w a lo hi Hlo Hhi; destruct (lo <=? hi) eqn:Horder.
  - unfold product_arc_select; rewrite Horder; apply product_arc_nonwrapping;
      try assumption; now apply Z.leb_le.
  - apply product_arc_wrapping; try assumption; now apply Z.leb_gt.
Qed.

Lemma product_arc_coordinate : forall w origin first last,
  wrapped_offset w origin first <= wrapped_offset w origin last -> forall z,
  (wrapped_gamma w (WItv first last) z <-> is_word w z /\
    wrapped_offset w origin first <= wrapped_offset w origin z <=
      wrapped_offset w origin last).
Proof.
  intros w origin first last Hordered z.
  pose proof (wrapped_offset_range w origin last) as Hlast.
  pose proof (wrapped_offset_range w first z) as Hoffset.
  pose proof (wrapped_offset_difference w origin first last Hordered) as Hlength.
  split.
  - intros [Hword Hspan]; change (wrapped_offset w first z <= wrapped_offset w first last)
      in Hspan; rewrite Hlength in Hspan.
    assert (Hsum : wrapped_offset w origin first + wrapped_offset w first z < modulus w)
      by lia.
    rewrite (wrapped_offset_linear w origin first z Hsum).
    split; [exact Hword|lia].
  - intros [Hword Hbounds]; split; [exact Hword|].
    change (wrapped_offset w first z <= wrapped_offset w first last).
    rewrite (wrapped_offset_difference w origin first z ltac:(lia)), Hlength; lia.
Qed.

Lemma product_arc_subinterval : forall w origin hi first last,
  wrapped_offset w origin first <= wrapped_offset w origin last ->
  wrapped_offset w origin last <= wrapped_offset w origin hi ->
  wrapped_leb w (WItv first last) (WItv origin hi) = true.
Proof.
  intros w origin hi first last Horder Hbound; apply wrapped_leb_spec; intros z Hz.
  apply (product_arc_coordinate w origin first last Horder z) in Hz.
  destruct Hz as [Hword Hbounds]; split; [exact Hword|].
  change (wrapped_offset w origin z <= wrapped_offset w origin hi); lia.
Qed.

Definition product_proper_arc (w : width) (lo hi : Z) : Prop :=
  is_word w lo /\ is_word w hi /\ wrapped_offset w lo hi < modulus w - 1.

Lemma product_normal_arc_proper : forall w a lo hi,
  wrapped_norm w a = WItv lo hi -> product_proper_arc w lo hi.
Proof.
  intros w [| |a b] lo hi Hnormal; try discriminate.
  unfold wrapped_norm in Hnormal.
  destruct (wrapped_offset w a b =? modulus w - 1) eqn:Hfull; [discriminate|].
  inversion Hnormal; subst lo hi; split; [apply wrap_is_word|split; [apply wrap_is_word|]].
  rewrite wrapped_offset_wrap.
  apply Z.eqb_neq in Hfull; pose proof (wrapped_offset_range w a b); lia.
Qed.

Lemma product_proper_arc_normal : forall w lo hi,
  product_proper_arc w lo hi -> wrapped_norm w (WItv lo hi) = WItv lo hi.
Proof.
  intros w lo hi [Hlo [Hhi Hproper]]; unfold wrapped_norm.
  rewrite (proj2 (Z.eqb_neq _ _)) by lia.
  now rewrite (wrap_id w lo Hlo), (wrap_id w hi Hhi).
Qed.

Lemma product_arc_selected_proper : forall w a lo hi first last,
  product_proper_arc w lo hi -> product_arc_bounds w a lo hi (Some (first, last)) ->
  product_proper_arc w first last /\
  wrapped_leb w (WItv first last) (WItv lo hi) = true.
Proof.
  intros w a lo hi first last [Hlo [Hhi Hproper]] [Hfirst [Hlast [Horder Hall]]].
  destruct Hfirst as [Hfw [Hfb Hfa]], Hlast as [Hlw [Hlb Hla]].
  change (is_word w last /\ wrapped_offset w lo last <= wrapped_offset w lo hi) in Hla.
  split.
  - split; [exact Hfw|split; [exact Hlw|]].
    rewrite (wrapped_offset_difference w lo first last Horder).
    pose proof (wrapped_offset_range w lo first); lia.
  - apply product_arc_subinterval; [exact Horder|exact (proj2 Hla)].
Qed.

Definition product_arc_bits (w : width) (a : tnum) (lo hi : Z) : tnum :=
  if lo <=? hi then tnum_meet w a (product_prefix w lo hi) else a.

Lemma product_arc_bits_lower : forall w a lo hi,
  leb (tnum_lattice w) (product_arc_bits w a lo hi) a = true.
Proof.
  intros w a lo hi; unfold product_arc_bits; destruct (lo <=? hi);
    [apply tnum_meet_lower_left|apply (leb_refl (tnum_laws w))].
Qed.

Lemma product_arc_bits_sound : forall w a lo hi z,
  is_word w lo -> is_word w hi -> tnum_gamma w a z -> wrapped_gamma w (WItv lo hi) z ->
  tnum_gamma w (product_arc_bits w a lo hi) z.
Proof.
  intros w a lo hi z Hlo Hhi Hbits Harc; unfold product_arc_bits.
  destruct (lo <=? hi) eqn:Horder; [|exact Hbits].
  apply tnum_meet_sound; [exact Hbits|apply product_prefix_sound].
  apply (product_arc_word_spec w lo hi z Hlo Hhi (wrapped_gamma_word _ _ _ Harc)) in Harc.
  now rewrite Horder in Harc.
Qed.

(** One round retains full arcs and refines proper arcs by their compatible endpoints. *)
Definition product_bits_round (w : width) (pq : tnum * wrapped) : tnum * wrapped :=
  let a := fst pq in
  let B := (bot (tnum_lattice w), WBot) in
  if tnum_empty w a then B else
  match wrapped_norm w (snd pq) with
  | WBot => B
  | WFull => (a, WFull)
  | WItv lo hi =>
    match product_arc_select w a lo hi with
    | None => B
    | Some (first, last) => (product_arc_bits w a first last, WItv first last)
    end
  end.

(** The required reducer performs exactly two proper-arc information-exchange rounds. *)
Definition reduce_bits_wrapped (w : width) (pq : tnum * wrapped) : tnum * wrapped :=
  product_bits_round w (product_bits_round w pq).

(** Known bits and circular intervals share the common reduced-product construction. *)
Definition bits_wrapped_domain : word_domain (tnum * wrapped) :=
  product_word_domain known_bits_domain wrapped_domain reduce_bits_wrapped.

(** One information-exchange round retains every shared word. *)
Theorem product_bits_round_sound : forall w pq z,
  product_pgamma tnum_gamma wrapped_gamma w pq z ->
  product_pgamma tnum_gamma wrapped_gamma w (product_bits_round w pq) z.
Proof.
  intros w [a arc] z [Hword [Hbits Harc]]; unfold product_bits_round; cbn [fst snd].
  rewrite (tnum_empty_sound w a z Hbits).
  apply (proj2 (wrapped_norm_gamma w arc z)) in Harc.
  destruct (wrapped_norm w arc) as [| |lo hi] eqn:Hnormal; [contradiction| |].
  - exact (conj Hword (conj Hbits Hword)).
  - destruct (product_normal_arc_proper w arc lo hi Hnormal) as [Hlo [Hhi Hproper]].
    pose proof (product_arc_select_correct w a lo hi Hlo Hhi) as Hbounds.
    destruct (product_arc_select w a lo hi) as [[first last]|].
    + destruct Hbounds as [Hfirst [Hlast [Horder Hall]]].
      assert (Hinput : product_pgamma tnum_gamma wrapped_gamma w (a, WItv lo hi) z)
        by exact (conj Hword (conj Hbits Harc)).
      pose proof (Hall z Hinput) as Hselected.
      assert (Harc' : wrapped_gamma w (WItv first last) z).
      { apply (product_arc_coordinate w lo first last Horder); exact (conj Hword Hselected). }
      split; [exact Hword|split; [|exact Harc']].
      apply product_arc_bits_sound; [exact (proj1 Hfirst)|exact (proj1 Hlast)|
        exact Hbits|exact Harc'].
    + exfalso; apply (Hbounds z); exact (conj Hword (conj Hbits Harc)).
Qed.

(** One information-exchange round only refines both components. *)
Theorem product_bits_round_lower : forall w pq,
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) (product_bits_round w pq) pq = true.
Proof.
  intros w [a arc]; unfold product_bits_round; cbn [fst snd].
  destruct (tnum_empty w a); [apply (bot_least (product_laws _ _ (tnum_laws w)
    (wrapped_laws w)))|].
  destruct (wrapped_norm w arc) as [| |lo hi] eqn:Hnormal.
  - apply (bot_least (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
  - apply andb_true_iff; split; [apply (leb_refl (tnum_laws w))|].
    pose proof (proj2 (wrapped_norm_leb w arc)) as Hback; now rewrite Hnormal in Hback.
  - pose proof (product_normal_arc_proper w arc lo hi Hnormal) as Hproper.
    pose proof (product_arc_select_correct w a lo hi (proj1 Hproper)
      (proj1 (proj2 Hproper))) as Hbounds.
    destruct (product_arc_select w a lo hi) as [[first last]|];
      [|apply (bot_least (product_laws _ _ (tnum_laws w) (wrapped_laws w)))].
    apply andb_true_iff; split; [apply product_arc_bits_lower|].
    eapply wrapped_leb_trans.
    + exact (proj2 (product_arc_selected_proper w a lo hi first last Hproper Hbounds)).
    + pose proof (proj2 (wrapped_norm_leb w arc)) as Hback; now rewrite Hnormal in Hback.
Qed.

Lemma product_arc_inside_coordinate : forall w origin hi first last,
  product_proper_arc w origin hi ->
  wrapped_leb w (WItv first last) (WItv origin hi) = true ->
  wrapped_offset w origin first <= wrapped_offset w origin last.
Proof.
  intros w origin hi first last [_ [_ Hproper]] Hle.
  change ((wrapped_offset w origin hi =? modulus w - 1) ||
    (wrapped_offset w origin first + wrapped_offset w first last <=?
      wrapped_offset w origin hi) = true) in Hle.
  rewrite (proj2 (Z.eqb_neq _ _)) in Hle by lia; cbn in Hle; apply Z.leb_le in Hle.
  pose proof (wrapped_offset_range w first last) as Hspan.
  rewrite (wrapped_offset_linear w origin first last ltac:(lia)); lia.
Qed.

Lemma product_arc_hull_below : forall w origin hi first last first' last',
  product_proper_arc w origin hi ->
  wrapped_leb w (WItv first last) (WItv origin hi) = true ->
  wrapped_leb w (WItv first' last') (WItv origin hi) = true ->
  wrapped_gamma w (WItv first' last') first ->
  wrapped_gamma w (WItv first' last') last ->
  wrapped_leb w (WItv first last) (WItv first' last') = true.
Proof.
  intros w origin hi first last first' last' Hproper Hsmall Hlarge Hfirst Hlast.
  pose proof (product_arc_inside_coordinate w origin hi first last Hproper Hsmall) as Horder.
  pose proof (product_arc_inside_coordinate w origin hi first' last' Hproper Hlarge)
    as Horder'.
  apply (product_arc_coordinate w origin first' last' Horder') in Hfirst, Hlast.
  apply wrapped_leb_spec; intros z Hz.
  apply (product_arc_coordinate w origin first last Horder) in Hz.
  apply (product_arc_coordinate w origin first' last' Horder').
  destruct Hz as [Hword Hbounds], Hfirst as [_ Hlower], Hlast as [_ Hupper].
  split; [exact Hword|lia].
Qed.

Lemma product_arc_endpoints : forall w first last,
  is_word w first -> is_word w last ->
  wrapped_gamma w (WItv first last) first /\ wrapped_gamma w (WItv first last) last.
Proof.
  intros w first last Hfirst Hlast; split; split; try assumption.
  - change (wrapped_offset w first first <= wrapped_offset w first last).
    rewrite wrapped_offset_self; pose proof (wrapped_offset_range w first last); lia.
  - apply Z.le_refl.
Qed.

Lemma product_arc_nonwrapping_contained : forall w first last first' last',
  product_proper_arc w first last -> product_proper_arc w first' last' -> first' <= last' ->
  wrapped_leb w (WItv first last) (WItv first' last') = true ->
  first' <= first <= last /\ last <= last'.
Proof.
  intros w first last first' last' [Hfw [Hlw Hproper]] Hupper Hlinear Hle.
  pose proof (product_arc_inside_coordinate w first' last' first last Hupper Hle) as Horder.
  destruct (product_arc_endpoints w first last Hfw Hlw) as [Hfirst Hlast].
  apply (proj1 (wrapped_leb_spec w _ _) Hle) in Hfirst, Hlast.
  destruct Hupper as [Hf'w [Hl'w Hupperproper]].
  apply (product_arc_word_spec w first' last' first Hf'w Hl'w Hfw) in Hfirst.
  apply (product_arc_word_spec w first' last' last Hf'w Hl'w Hlw) in Hlast.
  rewrite (proj2 (Z.leb_le first' last') Hlinear) in Hfirst, Hlast.
  rewrite !product_offset_high in Horder by (try assumption; lia); lia.
Qed.

Lemma product_tnum_meet_monotone : forall w a b a' b',
  leb (tnum_lattice w) a a' = true -> leb (tnum_lattice w) b b' = true ->
  leb (tnum_lattice w) (tnum_meet w a b) (tnum_meet w a' b') = true.
Proof.
  intros w a b a' b' Ha Hb; apply tnum_leb_bits in Ha, Hb; apply tnum_leb_bits.
  destruct Ha as [Haz Hao], Hb as [Hbz Hbo]; split; intros i Hi Hbit;
    cbn [tnum_meet zeros ones] in Hbit |- *;
    rewrite tnum_or_bit in Hbit |- * by exact Hi;
    apply orb_true_iff in Hbit as [Hleft|Hright]; apply orb_true_iff.
  - left; now apply Haz.
  - right; now apply Hbz.
  - left; now apply Hao.
  - right; now apply Hbo.
Qed.

Lemma product_arc_bits_monotone : forall w a b first last first' last',
  leb (tnum_lattice w) a b = true ->
  product_proper_arc w first last -> product_proper_arc w first' last' ->
  wrapped_leb w (WItv first last) (WItv first' last') = true ->
  leb (tnum_lattice w) (product_arc_bits w a first last)
    (product_arc_bits w b first' last') = true.
Proof.
  intros w a b first last first' last' Hab Hsmall Hlarge Harcs.
  unfold product_arc_bits; destruct (first' <=? last') eqn:Hlinear.
  - apply Z.leb_le in Hlinear.
    destruct (product_arc_nonwrapping_contained w first last first' last'
      Hsmall Hlarge Hlinear Harcs) as [Hbounds Hupper].
    rewrite (proj2 (Z.leb_le first last)) by lia.
    apply product_tnum_meet_monotone; [exact Hab|].
    now apply product_prefix_monotone.
  - destruct (first <=? last).
    + eapply (leb_trans (tnum_laws w)); [apply tnum_meet_lower_left|exact Hab].
    + exact Hab.
Qed.

(** A nonbottom round result retains its provenance and its original compatible endpoints. *)
Inductive product_round_shape (w : width) (a : tnum) (arc : wrapped) : tnum * wrapped -> Prop :=
  | ProductRoundBottom : product_round_shape w a arc (bot (tnum_lattice w), WBot)
  | ProductRoundFull : wrapped_norm w arc = WFull -> tnum_empty w a = false ->
      product_round_shape w a arc (a, WFull)
  | ProductRoundArc : forall lo hi first last,
      wrapped_norm w arc = WItv lo hi -> product_proper_arc w first last ->
      wrapped_leb w (WItv first last) arc = true ->
      product_pgamma tnum_gamma wrapped_gamma w (a, arc) first ->
      product_pgamma tnum_gamma wrapped_gamma w (a, arc) last ->
      product_round_shape w a arc (product_arc_bits w a first last, WItv first last).

Lemma product_bits_round_shape : forall w a arc,
  product_round_shape w a arc (product_bits_round w (a, arc)).
Proof.
  intros w a arc; unfold product_bits_round; cbn [fst snd].
  destruct (tnum_empty w a) eqn:Hempty; [constructor|].
  destruct (wrapped_norm w arc) as [| |lo hi] eqn:Hnormal; [constructor|constructor; assumption|].
  pose proof (product_normal_arc_proper w arc lo hi Hnormal) as Hproper.
  pose proof (product_arc_select_correct w a lo hi (proj1 Hproper)
    (proj1 (proj2 Hproper))) as Hbounds.
  destruct (product_arc_select w a lo hi) as [[first last]|]; [|constructor].
  destruct (product_arc_selected_proper w a lo hi first last Hproper Hbounds)
    as [Hselected Hbelow].
  destruct Hbounds as [Hfirst [Hlast [Hordered Hall]]].
  apply ProductRoundArc with (lo := lo) (hi := hi); try assumption.
  - eapply wrapped_leb_trans; [exact Hbelow|].
    pose proof (proj2 (wrapped_norm_leb w arc)) as Hback; now rewrite Hnormal in Hback.
  - destruct Hfirst as [Hword [Hbits Harc]].
    split; [exact Hword|split; [exact Hbits|]].
    apply (proj1 (wrapped_norm_gamma w arc first)); now rewrite Hnormal.
  - destruct Hlast as [Hword [Hbits Harc]].
    split; [exact Hword|split; [exact Hbits|]].
    apply (proj1 (wrapped_norm_gamma w arc last)); now rewrite Hnormal.
Qed.

Lemma product_round_shape_witness : forall w a arc result,
  product_round_shape w a arc result -> result = (bot (tnum_lattice w), WBot) \/
    exists z, product_pgamma tnum_gamma wrapped_gamma w (a, arc) z.
Proof.
  intros w a arc result Hshape; destruct Hshape as [|Hnormal Hempty|lo hi first last
    Hnormal Hproper Hbelow Hfirst Hlast]; [left; reflexivity| |right; now exists first].
  right; exists (tnum_min w a).
  assert (Hword : is_word w (tnum_min w a)) by apply wrap_is_word.
  split; [exact Hword|split; [exact (proj1 (tnum_endpoints_sound w a Hempty))|]].
  apply (proj1 (wrapped_norm_gamma w arc _)); rewrite Hnormal; exact Hword.
Qed.

(** An input component below bottom forces the canonical pair bottom in one round. *)
Theorem product_bits_round_empty : forall w,
  reduction_empty (tnum_lattice w) (wrapped_lattice w) (product_bits_round w).
Proof.
  intros w a arc Hempty.
  destruct (product_round_shape_witness w a arc _ (product_bits_round_shape w a arc))
    as [Hbottom|[z [Hword [Hbits Harc]]]]; [exact Hbottom|].
  exfalso; destruct Hempty as [Hbitsbot|Harcbot].
  - apply (tnum_gamma_bot_empty w z).
    exact (tnum_gamma_monotone w a _ z Hbitsbot Hbits).
  - exact (proj1 (wrapped_leb_spec w arc WBot) Harcbot z Harc).
Qed.

Lemma product_bits_input_monotone : forall w x y z,
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) x y = true ->
  product_pgamma tnum_gamma wrapped_gamma w x z ->
  product_pgamma tnum_gamma wrapped_gamma w y z.
Proof.
  intros w [a arc] [b other] z Hle [Hword [Hbits Harc]].
  apply andb_true_iff in Hle as [Hab Harcs].
  split; [exact Hword|split].
  - exact (tnum_gamma_monotone w a b z Hab Hbits).
  - exact (proj1 (wrapped_leb_spec w arc other) Harcs z Harc).
Qed.

Lemma product_round_shape_lower : forall w a arc result,
  product_round_shape w a arc result ->
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) result (a, arc) = true.
Proof.
  intros w a arc result Hshape; destruct Hshape as [|Hnormal Hempty|lo hi first last
    Hnormal Hproper Hbelow Hfirst Hlast].
  - apply (bot_least (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
  - apply andb_true_iff; split; [apply (leb_refl (tnum_laws w))|].
    pose proof (proj2 (wrapped_norm_leb w arc)) as Hback; now rewrite Hnormal in Hback.
  - apply andb_true_iff; split; [apply product_arc_bits_lower|exact Hbelow].
Qed.

Lemma product_full_below_proper : forall w arc other lo hi,
  wrapped_norm w arc = WFull -> wrapped_norm w other = WItv lo hi ->
  wrapped_leb w arc other = true -> False.
Proof.
  intros w arc other lo hi Hfull Hnormal Hle.
  pose proof (product_normal_arc_proper w other lo hi Hnormal) as [_ [_ Hproper]].
  pose proof (proj2 (wrapped_norm_leb w arc)) as Hback.
  pose proof (proj1 (wrapped_norm_leb w other)) as Hfront.
  rewrite Hfull in Hback; rewrite Hnormal in Hfront.
  pose proof (wrapped_leb_trans w _ _ _ Hback Hle) as Hmiddle.
  pose proof (wrapped_leb_trans w _ _ _ Hmiddle Hfront) as Hcontra.
  change ((wrapped_offset w lo hi =? modulus w - 1) = true) in Hcontra.
  apply Z.eqb_eq in Hcontra; lia.
Qed.

Lemma product_round_proper_order : forall w a arc b other lo' hi' first last first' last',
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) (a, arc) (b, other) = true ->
  wrapped_norm w other = WItv lo' hi' ->
  product_proper_arc w first last -> product_proper_arc w first' last' ->
  wrapped_leb w (WItv first last) arc = true ->
  wrapped_leb w (WItv first' last') other = true ->
  product_pgamma tnum_gamma wrapped_gamma w (a, arc) first ->
  product_pgamma tnum_gamma wrapped_gamma w (a, arc) last ->
  (forall z, product_pgamma tnum_gamma wrapped_gamma w (b, other) z ->
    product_pgamma tnum_gamma wrapped_gamma w
      (product_arc_bits w b first' last', WItv first' last') z) ->
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w))
    (product_arc_bits w a first last, WItv first last)
    (product_arc_bits w b first' last', WItv first' last') = true.
Proof.
  intros w a arc b other lo' hi' first last first' last' Hinput Hnormal
    Hproper Hproper' Hbelow Hbelow' Hfirst Hlast Hkeep.
  pose proof (product_normal_arc_proper w other lo' hi' Hnormal) as Hroot.
  pose proof (proj1 (wrapped_norm_leb w other)) as Hfront; rewrite Hnormal in Hfront.
  pose proof Hinput as Hcomponents; apply andb_true_iff in Hcomponents as [Hab Harcs].
  assert (Hsmall : wrapped_leb w (WItv first last) (WItv lo' hi') = true).
  { eapply wrapped_leb_trans; [exact Hbelow|].
    exact (wrapped_leb_trans w arc other _ Harcs Hfront). }
  assert (Hlarge : wrapped_leb w (WItv first' last') (WItv lo' hi') = true).
  { exact (wrapped_leb_trans w _ other _ Hbelow' Hfront). }
  pose proof (Hkeep first (product_bits_input_monotone w _ _ _ Hinput Hfirst)) as Hfirst'.
  pose proof (Hkeep last (product_bits_input_monotone w _ _ _ Hinput Hlast)) as Hlast'.
  destruct Hfirst' as [_ [_ Hfirstarc]], Hlast' as [_ [_ Hlastarc]].
  pose proof (product_arc_hull_below w lo' hi' first last first' last' Hroot
    Hsmall Hlarge Hfirstarc Hlastarc) as Hrounded.
  apply andb_true_iff; split; [|exact Hrounded].
  now apply product_arc_bits_monotone.
Qed.

Lemma product_round_shapes_monotone : forall w a arc b other rx ry,
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) (a, arc) (b, other) = true ->
  product_round_shape w a arc rx -> product_round_shape w b other ry ->
  (forall z, product_pgamma tnum_gamma wrapped_gamma w (b, other) z ->
    product_pgamma tnum_gamma wrapped_gamma w ry z) ->
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) rx ry = true.
Proof.
  intros w a arc b other rx ry Hinput Hx Hy Hkeep.
  destruct Hy as [|Hnormal Hempty|lo' hi' first' last' Hnormal Hproper' Hbelow' Hfirst' Hlast'].
  - destruct (product_round_shape_witness w a arc rx Hx) as [->|[z Hz]].
    + apply (leb_refl (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
    + pose proof (Hkeep z (product_bits_input_monotone w _ _ _ Hinput Hz)) as Hbad.
      destruct Hbad as [_ [_ Hbot]]; contradiction.
  - eapply (leb_trans (product_laws _ _ (tnum_laws w) (wrapped_laws w)));
      [exact (product_round_shape_lower w a arc rx Hx)|].
    eapply (leb_trans (product_laws _ _ (tnum_laws w) (wrapped_laws w))); [exact Hinput|].
    apply andb_true_iff; split; [apply (leb_refl (tnum_laws w))|].
    pose proof (proj1 (wrapped_norm_leb w other)) as Hfront; now rewrite Hnormal in Hfront.
  - destruct Hx as [|Hxnormal Hxempty|lo hi first last Hxnormal Hproper Hbelow Hfirst Hlast].
    + apply (bot_least (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
    + exfalso; apply (product_full_below_proper w arc other lo' hi' Hxnormal Hnormal).
      apply andb_true_iff in Hinput; exact (proj2 Hinput).
    + eapply product_round_proper_order; eassumption.
Qed.

(** One round is monotone in both input components, including full arcs. *)
Theorem product_bits_round_monotone : forall w x y,
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) x y = true ->
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w))
    (product_bits_round w x) (product_bits_round w y) = true.
Proof.
  intros w [a arc] [b other] Hinput; eapply product_round_shapes_monotone.
  - exact Hinput.
  - apply product_bits_round_shape.
  - apply product_bits_round_shape.
  - apply product_bits_round_sound.
Qed.

Lemma product_offset_injective : forall w origin x y,
  is_word w origin -> is_word w x -> is_word w y ->
  wrapped_offset w origin x = wrapped_offset w origin y -> x = y.
Proof.
  intros w origin x y Horigin Hx Hy Heq.
  rewrite !wrapped_offset_word_cases in Heq by assumption.
  destruct (origin <=? x) eqn:Hleft, (origin <=? y) eqn:Hright;
    first [apply Z.leb_le in Hleft|apply Z.leb_gt in Hleft];
    first [apply Z.leb_le in Hright|apply Z.leb_gt in Hright]; unfold is_word in *; lia.
Qed.

Lemma product_arc_same_endpoints : forall w first last first' last',
  product_proper_arc w first last -> product_proper_arc w first' last' ->
  wrapped_leb w (WItv first' last') (WItv first last) = true ->
  wrapped_gamma w (WItv first' last') first ->
  wrapped_gamma w (WItv first' last') last -> first' = first /\ last' = last.
Proof.
  intros w first last first' last' Hproper Hproper' Hbelow Hfirst Hlast.
  pose proof (product_arc_inside_coordinate w first last first' last' Hproper Hbelow)
    as Hordered.
  apply (product_arc_coordinate w first first' last' Hordered) in Hfirst, Hlast.
  rewrite wrapped_offset_self in Hfirst.
  destruct Hproper as [Hfw [Hlw Hproper]], Hproper' as [Hf'w [Hl'w Hproper']].
  pose proof (proj2 (product_arc_endpoints w first' last' Hf'w Hl'w)) as Hlast'.
  apply (proj1 (wrapped_leb_spec w _ _) Hbelow) in Hlast'.
  change (is_word w last' /\ wrapped_offset w first last' <= wrapped_offset w first last)
    in Hlast'.
  pose proof (wrapped_offset_range w first first') as Hrange.
  assert (Hstart : wrapped_offset w first first' = wrapped_offset w first first).
  { rewrite wrapped_offset_self; lia. }
  assert (Hend : wrapped_offset w first last' = wrapped_offset w first last) by lia.
  split.
  - exact (product_offset_injective w first first' first Hfw Hf'w Hfw Hstart).
  - exact (product_offset_injective w first last' last Hfw Hl'w Hlw Hend).
Qed.

Lemma product_arc_bits_stable : forall w a first last,
  leb (tnum_lattice w) (product_arc_bits w a first last)
    (product_arc_bits w (product_arc_bits w a first last) first last) = true.
Proof.
  intros w a first last; unfold product_arc_bits; destruct (first <=? last);
    [|apply (leb_refl (tnum_laws w))].
  apply tnum_leb_bits; split; intros i Hi Hbit;
    cbn [tnum_meet zeros ones] in Hbit |- *;
    rewrite !tnum_or_bit in Hbit |- * by exact Hi;
    rewrite tnum_or_bit in Hbit by exact Hi;
    now rewrite <- orb_assoc, orb_diag in Hbit.
Qed.

Lemma product_bits_round_proper_stable : forall w a arc first last,
  product_bits_round w (a, arc) =
    (product_arc_bits w a first last, WItv first last) ->
  product_proper_arc w first last ->
  product_pgamma tnum_gamma wrapped_gamma w (a, arc) first ->
  product_pgamma tnum_gamma wrapped_gamma w (a, arc) last ->
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w))
    (product_arc_bits w a first last, WItv first last)
    (product_bits_round w (product_arc_bits w a first last, WItv first last)) = true.
Proof.
  intros w a arc first last Hvalue Hproper Hfirst Hlast.
  pose proof (product_bits_round_sound w _ first Hfirst) as Hfirst'.
  pose proof (product_bits_round_sound w _ last Hlast) as Hlast'.
  rewrite Hvalue in Hfirst', Hlast'.
  pose proof (product_bits_round_sound w _ first Hfirst') as Hfirst''.
  pose proof (product_bits_round_sound w _ last Hlast') as Hlast''.
  remember (product_bits_round w (product_arc_bits w a first last, WItv first last))
    as result eqn:Hresult.
  pose proof (product_bits_round_shape w (product_arc_bits w a first last)
    (WItv first last)) as Hshape; rewrite <- Hresult in Hshape.
  destruct Hshape as [|Hnormal Hempty|lower upper f l Hnormal Hproper' Hbelow Hf Hl].
  - destruct Hfirst'' as [_ [_ Hbot]]; contradiction.
  - rewrite (product_proper_arc_normal w first last Hproper) in Hnormal; discriminate.
  - destruct Hfirst'' as [_ [_ Hfirstarc]], Hlast'' as [_ [_ Hlastarc]].
    destruct (product_arc_same_endpoints w first last f l Hproper Hproper'
      Hbelow Hfirstarc Hlastarc) as [-> ->].
    apply andb_true_iff; split; [apply product_arc_bits_stable|apply wrapped_leb_refl].
Qed.

(** Compatible endpoints and their common leading bits already make one round stable. *)
Theorem product_bits_round_idempotent : forall w pq,
  leb (product_lattice (tnum_lattice w) (wrapped_lattice w)) (product_bits_round w pq)
    (product_bits_round w (product_bits_round w pq)) = true.
Proof.
  intros w [a arc].
  remember (product_bits_round w (a, arc)) as result eqn:Hresult.
  pose proof (product_bits_round_shape w a arc) as Hshape; rewrite <- Hresult in Hshape.
  destruct Hshape as [|Hnormal Hempty|lo hi first last Hnormal Hproper Hbelow Hfirst Hlast].
  - rewrite (product_bits_round_empty w _ WBot (or_intror eq_refl)).
    apply (leb_refl (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
  - unfold product_bits_round; cbn [fst snd wrapped_norm]; rewrite Hempty.
    apply (leb_refl (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
  - eapply product_bits_round_proper_stable.
    + symmetry; exact Hresult.
    + exact Hproper.
    + exact Hfirst.
    + exact Hlast.
Qed.

(** Two rounds descend, preserve order and meaning, are stable, and collapse empty components. *)
Theorem reduce_bits_wrapped_laws : forall w,
  reduction_laws (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w) /\
  reduction_sound (word_payload_concretisation tnum_gamma w)
    (word_payload_concretisation wrapped_gamma w) (reduce_bits_wrapped w) /\
  reduction_empty (tnum_lattice w) (wrapped_lattice w) (reduce_bits_wrapped w).
Proof.
  intro w; split; [constructor|split].
  - intro x; unfold reduce_bits_wrapped.
    eapply (leb_trans (product_laws _ _ (tnum_laws w) (wrapped_laws w)));
      apply product_bits_round_lower.
  - intros x y Hle; unfold reduce_bits_wrapped.
    apply product_bits_round_monotone; now apply product_bits_round_monotone.
  - intro x; unfold reduce_bits_wrapped.
    eapply (leb_trans (product_laws _ _ (tnum_laws w) (wrapped_laws w))).
    + apply product_bits_round_idempotent.
    + apply product_bits_round_monotone; apply product_bits_round_idempotent.
  - constructor; intros x z [[Hword Hbits] [_ Harc]].
    pose proof (product_bits_round_sound w _ z (conj Hword (conj Hbits Harc))) as Hfirst.
    pose proof (product_bits_round_sound w _ z Hfirst) as [Hrange [Hbits' Harc']].
    exact (conj (conj Hrange Hbits') (conj Hrange Harc')).
  - intros a arc Hempty; unfold reduce_bits_wrapped.
    rewrite (product_bits_round_empty w a arc Hempty).
    apply product_bits_round_empty; right; reflexivity.
Qed.

(** The known-bits and circular-interval product lifts to a sound tagged numeric domain. *)
Theorem bits_wrapped_numeric_laws : numeric_laws (tagged_domain bits_wrapped_domain)
  (tagged_gamma (product_pgamma tnum_gamma wrapped_gamma)).
Proof.
  apply tagged_numeric_laws; apply product_word_laws.
  - apply known_bits_word_laws.
  - apply wrapped_word_laws.
  - intro w; exact (proj1 (reduce_bits_wrapped_laws w)).
  - intro w; exact (proj1 (proj2 (reduce_bits_wrapped_laws w))).
Qed.
