(** * Meanings of abstract values

    Forward meanings grow with the order; backward agreement shrinks with it.
    For example, a join preserves every concrete value of either input.
    Builds on: OrderLattice. *)

From Gaulois.Order Require Import OrderLattice.

(** A concretisation assigns concrete values to each abstract value. *)
Record concretisation (A C : Type) : Type := Concretisation {
  gamma : A -> C -> Prop
}.

Arguments gamma {A C}.

(** Concretisation preserves the abstract order. *)
Record concretisation_laws {A C} (L : lattice A) (G : concretisation A C) : Prop := {
  gamma_monotone : forall a b c, leb L a b = true -> gamma G a c -> gamma G b c
}.

(** Agreement records which pairs cannot be distinguished by an abstract need. *)
Record agreement (A C : Type) : Type := Agreement {
  agree : A -> C -> C -> Prop
}.

Arguments agree {A C}.

(** Agreement is reflexive and antitone in the abstract need. *)
Record agreement_laws {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_refl : forall a c, agree R a c c;
  agree_antitone : forall a b x y, leb L a b = true -> agree R b x y -> agree R a x y
}.

(** An empty bottom denotes no concrete value. *)
Record bottom_empty {A C} (L : lattice A) (G : concretisation A C) : Prop := {
  gamma_bot_empty : forall c, ~ gamma G (bot L) c
}.

(** A full top denotes every concrete value. *)
Record top_full {A C} {L : lattice A} (T : top L) (G : concretisation A C) : Prop := {
  gamma_top_full : forall c, gamma G (top_value T) c
}.

(** Agreement can additionally be symmetric and transitive for each need. *)
Record agreement_equivalence {A C} (R : agreement A C) : Prop := {
  agree_sym : forall a x y, agree R a x y -> agree R a y x;
  agree_trans : forall a x y z, agree R a x y -> agree R a y z -> agree R a x z
}.

(** Bottom needs nothing and therefore relates every pair. *)
Record agreement_bot {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_bot : forall x y, agree R (bot L) x y
}.

(** Agreement on both inputs suffices for agreement on their join. *)
Record agreement_join_law {A C} (L : lattice A) (R : agreement A C) : Prop := {
  agree_join : forall a b x y, agree R a x y -> agree R b x y -> agree R (join L a b) x y
}.

Arguments gamma_monotone {A C L G}.
Arguments agree_refl {A C L R}.
Arguments agree_antitone {A C L R}.
Arguments gamma_bot_empty {A C L G}.
Arguments gamma_top_full {A C L T G}.
Arguments agree_sym {A C R}.
Arguments agree_trans {A C R}.
Arguments agree_bot {A C L R}.
Arguments agree_join {A C L R}.

(** An embedding preserves and reflects boolean comparison. *)
Definition order_embedding {A B} (LA : lattice A) (LB : lattice B) (f : B -> A) : Prop :=
  forall b1 b2, leb LB b1 b2 = leb LA (f b1) (f b2).

(** A concretisation pulls back by applying the carrier map first. *)
Definition comap_gamma {A B C} (f : B -> A) (G : concretisation A C) : concretisation B C :=
  {| gamma := fun b c => gamma G (f b) c |}.

(** An agreement pulls back by applying the carrier map first. *)
Definition comap_agree {A B C} (f : B -> A) (R : agreement A C) : agreement B C :=
  {| agree := fun b x y => agree R (f b) x y |}.

Section CoreLaws.
Context {A C : Type} (L : lattice A) (G : concretisation A C) (R : agreement A C).
Variables (a b : A) (c x y : C).

(** Join preserves the left input's concrete meaning. *)
Theorem gamma_join_l : lattice_laws L -> concretisation_laws L G ->
  gamma G a c -> gamma G (join L a b) c.
Proof.
  intros laws HG; apply (gamma_monotone HG _ _ _ (join_upper_l laws a b)).
Qed.

(** Join preserves the right input's concrete meaning. *)
Theorem gamma_join_r : lattice_laws L -> concretisation_laws L G ->
  gamma G b c -> gamma G (join L a b) c.
Proof.
  intros laws HG; apply (gamma_monotone HG _ _ _ (join_upper_r laws a b)).
Qed.

(** Widening preserves the left input's concrete meaning. *)
Theorem gamma_widen_l : lattice_laws L -> concretisation_laws L G ->
  gamma G a c -> gamma G (widen L a b) c.
Proof.
  intros laws HG; apply (gamma_monotone HG _ _ _ (widen_upper_l laws a b)).
Qed.

(** Widening preserves the right input's concrete meaning. *)
Theorem gamma_widen_r : lattice_laws L -> concretisation_laws L G ->
  gamma G b c -> gamma G (widen L a b) c.
Proof.
  intros laws HG; apply (gamma_monotone HG _ _ _ (widen_upper_r laws a b)).
Qed.

(** Narrowing retains the lower input's meaning when the inputs are ordered. *)
Theorem gamma_narrow : lattice_laws L -> concretisation_laws L G -> leb L b a = true ->
  gamma G b c -> gamma G (narrow L a b) c.
Proof.
  intros laws HG Hba; apply (gamma_monotone HG _ _ _ (narrow_upper laws a b Hba)).
Qed.

(** Agreement at a join implies agreement at its left input. *)
Theorem agree_join_l : lattice_laws L -> agreement_laws L R ->
  agree R (join L a b) x y -> agree R a x y.
Proof.
  intros laws HR; apply (agree_antitone HR _ _ _ _ (join_upper_l laws a b)).
Qed.

(** Agreement at a join implies agreement at its right input. *)
Theorem agree_join_r : lattice_laws L -> agreement_laws L R ->
  agree R (join L a b) x y -> agree R b x y.
Proof.
  intros laws HR; apply (agree_antitone HR _ _ _ _ (join_upper_r laws a b)).
Qed.

(** Agreement at a widening implies agreement at its left input. *)
Theorem agree_widen_l : lattice_laws L -> agreement_laws L R ->
  agree R (widen L a b) x y -> agree R a x y.
Proof.
  intros laws HR; apply (agree_antitone HR _ _ _ _ (widen_upper_l laws a b)).
Qed.

(** Agreement at a widening implies agreement at its right input. *)
Theorem agree_widen_r : lattice_laws L -> agreement_laws L R ->
  agree R (widen L a b) x y -> agree R b x y.
Proof.
  intros laws HR; apply (agree_antitone HR _ _ _ _ (widen_upper_r laws a b)).
Qed.
End CoreLaws.

Section TransportLaws.
Context {A B C : Type} (LA : lattice A) (LB : lattice B) (G : concretisation A C)
  (R : agreement A C) (f : B -> A).

(** Concretisation remains monotone along an embedding. *)
Theorem comap_gamma_laws : order_embedding LA LB f -> concretisation_laws LA G ->
  concretisation_laws LB (comap_gamma f G).
Proof.
  intros Hembed HG; constructor; intros a b c Hab Hc.
  apply (gamma_monotone HG (f a) (f b) c); [rewrite <- Hembed |]; assumption.
Qed.

(** Pullback bottom is empty when its image lies below the original bottom. *)
Theorem comap_gamma_bot_empty : order_embedding LA LB f -> concretisation_laws LA G ->
  bottom_empty LA G -> leb LA (f (bot LB)) (bot LA) = true ->
  bottom_empty LB (comap_gamma f G).
Proof.
  intros _ HG Hbot Hle; constructor; intros c Hc.
  apply (gamma_bot_empty Hbot c); eapply (gamma_monotone HG); eassumption.
Qed.

(** Pullback top is full when its image lies above the original top. *)
Theorem comap_gamma_top_full : forall (TA : top LA) (TB : top LB),
  order_embedding LA LB f -> concretisation_laws LA G -> top_full TA G ->
  leb LA (top_value TA) (f (top_value TB)) = true -> top_full TB (comap_gamma f G).
Proof.
  intros TA TB _ HG Htop Hle; constructor; intro c.
  apply (gamma_monotone HG _ _ c Hle); apply (gamma_top_full Htop).
Qed.

(** Agreement remains antitone along an embedding. *)
Theorem comap_agree_laws : order_embedding LA LB f -> agreement_laws LA R ->
  agreement_laws LB (comap_agree f R).
Proof.
  intros Hembed HR; constructor.
  - intros a c; apply (agree_refl HR).
  - intros a b x y Hab Hxy.
    apply (agree_antitone HR (f a) (f b) x y); [rewrite <- Hembed |]; assumption.
Qed.

(** Pullback bottom needs nothing when its image lies below the original bottom. *)
Theorem comap_agree_bot : agreement_laws LA R -> agreement_bot LA R ->
  leb LA (f (bot LB)) (bot LA) = true -> agreement_bot LB (comap_agree f R).
Proof.
  intros HR Hbot Hle; constructor; intros x y.
  apply (agree_antitone HR _ _ x y Hle); apply (agree_bot Hbot).
Qed.

(** Pullback preserves join agreement when the mapped join lies below the original join. *)
Theorem comap_agree_join : agreement_laws LA R -> agreement_join_law LA R ->
  (forall a b, leb LA (f (join LB a b)) (join LA (f a) (f b)) = true) ->
  agreement_join_law LB (comap_agree f R).
Proof.
  intros HR Hjoin Hle; constructor; intros a b x y Ha Hb.
  apply (agree_antitone HR _ _ x y (Hle a b)); apply (agree_join Hjoin); assumption.
Qed.
End TransportLaws.
