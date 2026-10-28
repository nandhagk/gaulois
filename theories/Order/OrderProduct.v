(** * Product lattices

    Product operations work componentwise, while meanings and agreements intersect.
    For example, a pair of boolean values joins by disjoining each coordinate.
    Builds on: OrderLattice, OrderConcrete and OrderMonotone. *)

From Stdlib Require Import Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderMonotone.

(** Products compare and combine their coordinates independently. *)
Definition product_lattice {A B} (LA : lattice A) (LB : lattice B) : lattice (A * B) :=
  {| leb := fun x y => andb (leb LA (fst x) (fst y)) (leb LB (snd x) (snd y));
     bot := (bot LA, bot LB);
     join := fun x y => (join LA (fst x) (fst y), join LB (snd x) (snd y));
     widen := fun x y => (widen LA (fst x) (fst y), widen LB (snd x) (snd y));
     narrow := fun x y => (narrow LA (fst x) (fst y), narrow LB (snd x) (snd y)) |}.

(** The pair of component tops bounds every pair. *)
Definition product_top {A B} {LA : lattice A} {LB : lattice B} (TA : top LA) (TB : top LB) :
  top (product_lattice LA LB).
Proof.
  refine {| top_value := (top_value TA, top_value TB) |}.
  abstract (intros [a b]; cbn; rewrite (top_greatest TA), (top_greatest TB); reflexivity).
Defined.

(** Product concretisation requires both component meanings. *)
Definition product_gamma {A B C} (GA : concretisation A C) (GB : concretisation B C) :
  concretisation (A * B) C :=
  {| gamma := fun x c => gamma GA (fst x) c /\ gamma GB (snd x) c |}.

(** Product agreement requires both component agreements. *)
Definition product_agree {A B C} (RA : agreement A C) (RB : agreement B C) :
  agreement (A * B) C :=
  {| agree := fun a x y => agree RA (fst a) x y /\ agree RB (snd a) x y |}.

Section ProductLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (GA : concretisation A C)
  (GB : concretisation B C) (RA : agreement A C) (RB : agreement B C).

(** Products preserve the weak lattice laws componentwise. *)
Theorem product_laws : lattice_laws LA -> lattice_laws LB ->
  lattice_laws (product_lattice LA LB).
Proof.
  intros lawsA lawsB; constructor; cbn.
  - intros [a b]; cbn; rewrite (leb_refl lawsA), (leb_refl lawsB); reflexivity.
  - intros [a b] [a' b'] [a'' b'']; cbn.
    intros Hfirst Hsecond; apply andb_true_iff in Hfirst as [Ha Hb];
      apply andb_true_iff in Hsecond as [Ha' Hb']; apply andb_true_iff; split;
      [eapply (leb_trans lawsA) | eapply (leb_trans lawsB)]; eassumption.
  - intros [a b]; cbn; rewrite (bot_least lawsA), (bot_least lawsB); reflexivity.
  - intros [a b] [a' b']; cbn;
      rewrite (join_upper_l lawsA), (join_upper_l lawsB); reflexivity.
  - intros [a b] [a' b']; cbn;
      rewrite (join_upper_r lawsA), (join_upper_r lawsB); reflexivity.
  - intros [a b] [a' b']; cbn;
      rewrite (widen_upper_l lawsA), (widen_upper_l lawsB); reflexivity.
  - intros [a b] [a' b']; cbn;
      rewrite (widen_upper_r lawsA), (widen_upper_r lawsB); reflexivity.
  - intros [a b] [a' b']; cbn; intros Hle; apply andb_true_iff in Hle as [Ha Hb].
    rewrite (narrow_lower lawsA _ _ Ha), (narrow_lower lawsB _ _ Hb); reflexivity.
  - intros [a b] [a' b']; cbn; intros Hle; apply andb_true_iff in Hle as [Ha Hb].
    rewrite (narrow_upper lawsA _ _ Ha), (narrow_upper lawsB _ _ Hb); reflexivity.
Qed.

(** A pair of least upper bounds is a least upper bound. *)
Theorem product_lub : lub_laws LA -> lub_laws LB -> lub_laws (product_lattice LA LB).
Proof.
  intros lubA lubB; constructor; intros [a b] [a' b'] [a'' b'']; cbn.
  intros Hfirst Hsecond; apply andb_true_iff in Hfirst as [Ha Hb];
    apply andb_true_iff in Hsecond as [Ha' Hb']; apply andb_true_iff; split;
    [apply (join_least lubA) | apply (join_least lubB)]; assumption.
Qed.

(** The intersection of monotone meanings is monotone. *)
Theorem product_gamma_laws : concretisation_laws LA GA -> concretisation_laws LB GB ->
  concretisation_laws (product_lattice LA LB) (product_gamma GA GB).
Proof.
  intros HGA HGB; constructor; intros [a b] [a' b'] c Hle [Ha Hb]; cbn in *.
  apply andb_true_iff in Hle as [Haa Hbb]; split;
    [eapply (gamma_monotone HGA) | eapply (gamma_monotone HGB)]; eassumption.
Qed.

(** An empty bottom in either component makes the product bottom empty. *)
Theorem product_gamma_bot_empty : bottom_empty LA GA \/ bottom_empty LB GB ->
  bottom_empty (product_lattice LA LB) (product_gamma GA GB).
Proof.
  intros Hbot; constructor; intros c [Ha Hb]; destruct Hbot as [HA | HB].
  - exact (gamma_bot_empty HA c Ha).
  - exact (gamma_bot_empty HB c Hb).
Qed.

(** Intersecting agreements preserves reflexivity and antitonicity. *)
Theorem product_agree_laws : agreement_laws LA RA -> agreement_laws LB RB ->
  agreement_laws (product_lattice LA LB) (product_agree RA RB).
Proof.
  intros HRA HRB; constructor.
  - intros [a b] c; split; [apply (agree_refl HRA) | apply (agree_refl HRB)].
  - intros [a b] [a' b'] x y Hle [Ha Hb]; cbn in *.
    apply andb_true_iff in Hle as [Haa Hbb]; split;
      [eapply (agree_antitone HRA) | eapply (agree_antitone HRB)]; eassumption.
Qed.

(** Component join agreement gives product join agreement. *)
Theorem product_agree_join : agreement_join_law LA RA -> agreement_join_law LB RB ->
  agreement_join_law (product_lattice LA LB) (product_agree RA RB).
Proof.
  intros HRA HRB; constructor; intros [a b] [a' b'] x y [Ha Hb] [Ha' Hb']; split;
    [apply (agree_join HRA) | apply (agree_join HRB)]; assumption.
Qed.
End ProductLaws.

(** Sums of monotone component heights measure strict product joins. *)
Definition product_height {A B} {LA : lattice A} {LB : lattice B}
  (lawsA : lattice_laws LA) (lawsB : lattice_laws LB)
  (HA : monotone_height LA) (HB : monotone_height LB) :
  monotone_height (product_lattice LA LB).
Proof.
  unshelve refine (@MonotoneHeight (A * B) (product_lattice LA LB)
    (@Height _ (product_lattice LA LB)
      (fun x => rank (base_height HA) (fst x) + rank (base_height HB) (snd x))
      (bound (base_height HA) + bound (base_height HB)) _ _) _).
  - abstract (intros [a b]; cbn;
      pose proof (rank_bounded (base_height HA) a) as HboundA;
      pose proof (rank_bounded (base_height HB) b) as HboundB; lia).
  - abstract (intros [a b] [a' b']; cbn; intro Hstrict;
      pose proof (rank_monotone HA _ _ (join_upper_l lawsA a a')) as HgrowA;
      pose proof (rank_monotone HB _ _ (join_upper_l lawsB b b')) as HgrowB;
      apply andb_false_iff in Hstrict as [Hstrict | Hstrict];
      [pose proof (join_rank_grows (base_height HA) a a' Hstrict) as HstrictA; lia |
       pose proof (join_rank_grows (base_height HB) b b' Hstrict) as HstrictB; lia]).
  - abstract (intros [a b] [a' b']; cbn; intro Hle;
      apply andb_true_iff in Hle as [Ha Hb];
      pose proof (rank_monotone HA _ _ Ha) as HgrowA;
      pose proof (rank_monotone HB _ _ Hb) as HgrowB; lia).
Defined.

Lemma widening_rank_nonincreasing {A} {L : lattice A} (W : widening_rank L) :
  forall a b, wrank W (widen L a b) <= wrank W a.
Proof.
  intros a b; destruct (leb L b a) eqn:Hle.
  - apply (widen_rank_stable W _ _ Hle).
  - pose proof (widen_rank_progress W _ _ Hle) as Hprogress; lia.
Qed.

(** Sums of bounded component widening ranks measure product widening. *)
Definition product_wrank {A B} {LA : lattice A} {LB : lattice B}
  (WA : bounded_widening_rank LA) (WB : bounded_widening_rank LB) :
  bounded_widening_rank (product_lattice LA LB).
Proof.
  unshelve refine (@BoundedWideningRank (A * B) (product_lattice LA LB)
    (@WideningRank _ (product_lattice LA LB)
      (fun x => wrank (base_wrank WA) (fst x) + wrank (base_wrank WB) (snd x)) _ _)
    (wbound WA + wbound WB) _).
  - abstract (intros [a b] [a' b'] _; cbn;
      pose proof (widening_rank_nonincreasing (base_wrank WA) a a') as HgrowA;
      pose proof (widening_rank_nonincreasing (base_wrank WB) b b') as HgrowB; lia).
  - abstract (intros [a b] [a' b']; cbn; intro Hstrict;
      pose proof (widening_rank_nonincreasing (base_wrank WA) a a') as HgrowA;
      pose proof (widening_rank_nonincreasing (base_wrank WB) b b') as HgrowB;
      apply andb_false_iff in Hstrict as [Hstrict | Hstrict];
      [pose proof (widen_rank_progress (base_wrank WA) a a' Hstrict) as HstrictA; lia |
       pose proof (widen_rank_progress (base_wrank WB) b b' Hstrict) as HstrictB; lia]).
  - abstract (intros [a b]; cbn;
      pose proof (wrank_bounded WA a) as HboundA;
      pose proof (wrank_bounded WB b) as HboundB; lia).
Defined.

Section PairMonotone.
Context {A B D : Type} (LA : lattice A) (LB : lattice B) (LD : lattice D).

(** The first projection preserves product order. *)
Theorem monotone_fst : monotone_fun (product_lattice LA LB) LA fst.
Proof.
  intros [a b] [a' b'] Hle; apply andb_true_iff in Hle; exact (proj1 Hle).
Qed.

(** The second projection preserves product order. *)
Theorem monotone_snd : monotone_fun (product_lattice LA LB) LB snd.
Proof.
  intros [a b] [a' b'] Hle; apply andb_true_iff in Hle; exact (proj2 Hle).
Qed.

(** Pairing monotone functions preserves order. *)
Theorem monotone_pair : forall (f : D -> A) (g : D -> B),
  monotone_fun LD LA f -> monotone_fun LD LB g ->
  monotone_fun LD (product_lattice LA LB) (fun d => (f d, g d)).
Proof.
  intros f g Hf Hg a b Hab; apply andb_true_iff; split; [apply Hf | apply Hg]; exact Hab.
Qed.
End PairMonotone.
