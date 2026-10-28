(** * Bounded disjunctions

    Lists represent unions of meanings and compare by the Hoare order.
    For example, a cap of one joins all alternatives into a single abstract value.
    Builds on: OrderLattice, OrderConcrete and OrderMonotone. *)

From Stdlib Require Import List Bool Arith Lia.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderMonotone.

Import List.ListNotations.

(** A nonempty list joins left to right, avoiding an extra join with bottom. *)
Definition join_all {A} (L : lattice A) (l : list A) : A :=
  match l with
  | nil => bot L
  | x :: rest => fold_left (join L) rest x
  end.

(** Every left disjunct must be covered by a right disjunct. *)
Definition disjunction_leb {A} (L : lattice A) (xs ys : list A) : bool :=
  forallb (fun x => existsb (leb L x) ys) xs.

(** Compaction keeps a prefix and joins the remaining alternatives. *)
Definition compact {A} (k : nat) (L : lattice A) (l : list A) : list A :=
  if Nat.leb (length l) k then l
  else firstn (k - 1) l ++ [join_all L (skipn (k - 1) l)].

(** Joining respects the cap, while an escaping widening collapses to one disjunct. *)
Definition disjunction_lattice {A} (k : nat) (L : lattice A) : lattice (list A) :=
  {| leb := disjunction_leb L;
     bot := nil;
     join := fun xs ys => compact k L (xs ++ ys);
     widen := fun xs ys =>
       if disjunction_leb L ys xs then xs
       else [widen L (join_all L xs) (join_all L (xs ++ ys))];
     narrow := fun xs _ => xs |}.

(** A disjunction denotes any concrete value denoted by one of its alternatives. *)
Definition disjunction_gamma {A C} (G : concretisation A C) : concretisation (list A) C :=
  {| gamma := fun xs c => exists x, In x xs /\ gamma G x c |}.

Section ListLaws.
Context {A : Type} (L : lattice A) (laws : lattice_laws L).

Lemma disjunction_leb_spec (xs ys : list A) : disjunction_leb L xs ys = true <->
  forall x, In x xs -> exists y, In y ys /\ leb L x y = true.
Proof.
  unfold disjunction_leb; rewrite forallb_forall; split.
  - intros Hcover x Hin; apply existsb_exists; apply Hcover; exact Hin.
  - intros Hcover x Hin; apply existsb_exists; apply Hcover; exact Hin.
Qed.

Lemma disjunction_refl (xs : list A) : disjunction_leb L xs xs = true.
Proof.
  apply disjunction_leb_spec; intros x Hin; exists x; split; [exact Hin | apply (leb_refl laws)].
Qed.

Lemma disjunction_trans (xs ys zs : list A) :
  disjunction_leb L xs ys = true -> disjunction_leb L ys zs = true ->
  disjunction_leb L xs zs = true.
Proof.
  rewrite !disjunction_leb_spec; intros Hxy Hyz x Hin.
  destruct (Hxy x Hin) as [y [Hy Hle]]; destruct (Hyz y Hy) as [z [Hz Hle']].
  exists z; split; [exact Hz | eapply (leb_trans laws); eassumption].
Qed.

Lemma fold_join_upper_start (xs : list A) a : leb L a (fold_left (join L) xs a) = true.
Proof.
  revert a; induction xs as [|x xs IH]; intro a; cbn.
  - apply (leb_refl laws).
  - eapply (leb_trans laws); [apply (join_upper_l laws) | apply IH].
Qed.

Lemma fold_join_upper_member (xs : list A) a x : In x xs ->
  leb L x (fold_left (join L) xs a) = true.
Proof.
  revert a; induction xs as [|y xs IH]; intros a Hin; cbn in *; [contradiction |].
  destruct Hin as [Heq | Hin].
  - subst y; eapply (leb_trans laws); [apply (join_upper_r laws) | apply fold_join_upper_start].
  - apply IH; exact Hin.
Qed.

Lemma join_all_upper (xs : list A) x : In x xs -> leb L x (join_all L xs) = true.
Proof.
  destruct xs as [|a xs]; cbn; intro Hin; [contradiction |].
  destruct Hin as [Heq | Hin].
  - subst a; apply fold_join_upper_start.
  - apply fold_join_upper_member; exact Hin.
Qed.

Lemma compact_covers k (xs : list A) : disjunction_leb L xs (compact k L xs) = true.
Proof.
  unfold compact; destruct (Nat.leb (length xs) k); [apply disjunction_refl |].
  apply disjunction_leb_spec; intros x Hin.
  rewrite <- (firstn_skipn (k - 1) xs) in Hin; apply in_app_iff in Hin.
  destruct Hin as [Hprefix | Hsuffix].
  - exists x; split; [apply in_app_iff; left; exact Hprefix | apply (leb_refl laws)].
  - exists (join_all L (skipn (k - 1) xs)); split.
    + apply in_app_iff; right; left; reflexivity.
    + apply join_all_upper; exact Hsuffix.
Qed.

Lemma disjunction_append_left (xs ys : list A) : disjunction_leb L xs (xs ++ ys) = true.
Proof.
  apply disjunction_leb_spec; intros x Hin; exists x; split.
  - apply in_app_iff; left; exact Hin.
  - apply (leb_refl laws).
Qed.

Lemma disjunction_append_right (xs ys : list A) : disjunction_leb L ys (xs ++ ys) = true.
Proof.
  apply disjunction_leb_spec; intros x Hin; exists x; split.
  - apply in_app_iff; right; exact Hin.
  - apply (leb_refl laws).
Qed.

Lemma collapse_upper_left (xs ys : list A) : disjunction_leb L xs
  [widen L (join_all L xs) (join_all L (xs ++ ys))] = true.
Proof.
  apply disjunction_leb_spec; intros x Hin.
  exists (widen L (join_all L xs) (join_all L (xs ++ ys))); split; [left; reflexivity |].
  eapply (leb_trans laws); [apply join_all_upper; exact Hin | apply (widen_upper_l laws)].
Qed.

Lemma collapse_upper_right (xs ys : list A) : disjunction_leb L ys
  [widen L (join_all L xs) (join_all L (xs ++ ys))] = true.
Proof.
  apply disjunction_leb_spec; intros x Hin.
  exists (widen L (join_all L xs) (join_all L (xs ++ ys))); split; [left; reflexivity |].
  eapply (leb_trans laws); [apply join_all_upper; apply in_app_iff; right; exact Hin |].
  apply (widen_upper_r laws).
Qed.

(** The Hoare order and capped joins satisfy the weak lattice laws. *)
Lemma disjunction_lattice_laws k : lattice_laws (disjunction_lattice k L).
Proof.
  constructor; cbn.
  - apply disjunction_refl.
  - apply disjunction_trans.
  - intro xs; reflexivity.
  - intros xs ys; eapply disjunction_trans; [apply disjunction_append_left | apply compact_covers].
  - intros xs ys; eapply disjunction_trans; [apply disjunction_append_right | apply compact_covers].
  - intros xs ys; destruct (disjunction_leb L ys xs).
    + apply disjunction_refl.
    + apply collapse_upper_left.
  - intros xs ys; destruct (disjunction_leb L ys xs) eqn:Hcovered.
    + exact Hcovered.
    + apply collapse_upper_right.
  - intros xs ys _; apply disjunction_refl.
  - intros xs ys Hcovered; exact Hcovered.
Qed.

Lemma join_all_singleton_coverage x (ys : list A) :
  leb L (join_all L ([x] ++ ys)) x = true -> disjunction_leb L ys [x] = true.
Proof.
  intro Hjoin; apply disjunction_leb_spec; intros y Hin; exists x; split; [left; reflexivity |].
  eapply (leb_trans laws); [apply join_all_upper; apply in_app_iff; right; exact Hin | exact Hjoin].
Qed.
End ListLaws.

(** The Hoare order and capped joins satisfy the weak lattice laws. *)
Theorem disjunction_laws {A} (k : nat) (L : lattice A) :
  lattice_laws L -> lattice_laws (disjunction_lattice k L).
Proof.
  intro laws; apply disjunction_lattice_laws; exact laws.
Qed.

(** A positive cap bounds every joined list, including arbitrary oversized inputs. *)
Theorem disjunction_join_size {A} (k : nat) (L : lattice A) (xs ys : list A) :
  1 <= k -> length (join (disjunction_lattice k L) xs ys) <= k.
Proof.
  intro Hk; cbn [disjunction_lattice join]; unfold compact.
  destruct (Nat.leb (length (xs ++ ys)) k) eqn:Hlength.
  - apply Nat.leb_le; exact Hlength.
  - rewrite length_app, length_firstn; cbn.
    pose proof (Nat.le_min_l (k - 1) (length (xs ++ ys))) as Hprefix; lia.
Qed.

Section MeaningLaws.
Context {A C : Type} (k : nat) (L : lattice A) (G : concretisation A C).

(** Hoare coverage preserves the union of disjunct meanings. *)
Theorem disjunction_gamma_laws : lattice_laws L -> concretisation_laws L G ->
  concretisation_laws (disjunction_lattice k L) (disjunction_gamma G).
Proof.
  intros laws HG; constructor; intros xs ys c Hcover [x [Hin Hgamma]].
  rewrite (disjunction_leb_spec L xs ys) in Hcover.
  destruct (Hcover x Hin) as [y [Hy Hle]]; exists y; split; [exact Hy |].
  eapply (gamma_monotone HG); eassumption.
Qed.

(** The empty disjunction denotes no concrete value. *)
Theorem disjunction_gamma_bot_empty : bottom_empty (disjunction_lattice k L) (disjunction_gamma G).
Proof.
  constructor; intros c [x [Hin Hgamma]]; exact Hin.
Qed.
End MeaningLaws.

Lemma fold_join_monotone {A} (L : lattice A) (laws : lattice_laws L) (lub : lub_laws L)
  (xs ys : list A) : Forall2 (fun x y => leb L x y = true) xs ys ->
  forall a b, leb L a b = true ->
  leb L (fold_left (join L) xs a) (fold_left (join L) ys b) = true.
Proof.
  intro Hxy; induction Hxy as [|x y xs ys Hle Htail IH]; intros a b Hab; cbn.
  - exact Hab.
  - apply IH; apply (join_monotone L); assumption.
Qed.

(** Joining corresponding ordered alternatives preserves their order. *)
Theorem monotone_join_all {A} (L : lattice A) (xs ys : list A) : lattice_laws L -> lub_laws L ->
  Forall2 (fun x y => leb L x y = true) xs ys -> leb L (join_all L xs) (join_all L ys) = true.
Proof.
  intros laws lub Hxy; destruct Hxy as [|x y xs ys Hle Htail]; cbn [join_all].
  - apply (leb_refl laws).
  - apply (fold_join_monotone L laws lub); assumption.
Qed.

Lemma disjunction_wrank_decreases {A} (L : lattice A) (laws : lattice_laws L)
  (W : bounded_widening_rank L) (xs ys : list A) : disjunction_leb L ys xs = false ->
  2 * wrank (base_wrank W) (widen L (join_all L xs) (join_all L (xs ++ ys))) <
  2 * wrank (base_wrank W) (join_all L xs) +
    (if Nat.eqb (length xs) 1 then 0 else 1).
Proof.
  intro Hescape; destruct (Nat.eqb (length xs) 1) eqn:Hsingle.
  - apply Nat.eqb_eq in Hsingle.
    destruct xs as [|x xs]; cbn in Hsingle; [discriminate |].
    destruct xs as [|y xs]; [|cbn in Hsingle; discriminate].
    assert (Hbad : leb L (join_all L ([x] ++ ys)) x = false).
    { destruct (leb L (join_all L ([x] ++ ys)) x) eqn:Hle; [|reflexivity].
      pose proof (join_all_singleton_coverage L laws x ys Hle) as Hcovered; congruence. }
    pose proof (widen_rank_progress (base_wrank W) x (join_all L ([x] ++ ys)) Hbad) as Hlt.
    cbn [join_all fold_left] in *; lia.
  - destruct (leb L (join_all L (xs ++ ys)) (join_all L xs)) eqn:Hle.
    + pose proof (widen_rank_stable (base_wrank W) _ _ Hle) as Hrank; lia.
    + pose proof (widen_rank_progress (base_wrank W) _ _ Hle) as Hrank; lia.
Qed.

(** A collapsing widening decreases twice the base rank plus a nonsingleton flag. *)
Definition disjunction_wrank {A} {L : lattice A} (k : nat) (laws : lattice_laws L)
  (W : bounded_widening_rank L) : bounded_widening_rank (disjunction_lattice k L).
Proof.
  set (measure := fun xs => 2 * wrank (base_wrank W) (join_all L xs) +
    (if Nat.eqb (length xs) 1 then 0 else 1)).
  unshelve refine (@BoundedWideningRank _ (disjunction_lattice k L)
    (@WideningRank _ (disjunction_lattice k L) measure _ _) (2 * wbound W + 1) _).
  - abstract (intros xs ys Hcovered;
      change (disjunction_leb L ys xs = true) in Hcovered;
      change (measure (if disjunction_leb L ys xs then xs else
        [widen L (join_all L xs) (join_all L (xs ++ ys))]) <= measure xs);
      rewrite Hcovered; lia).
  - abstract (intros xs ys Hescape;
      change (disjunction_leb L ys xs = false) in Hescape;
      change (measure (if disjunction_leb L ys xs then xs else
        [widen L (join_all L xs) (join_all L (xs ++ ys))]) < measure xs);
      rewrite Hescape; unfold measure; cbn [join_all fold_left length Nat.eqb];
      pose proof (disjunction_wrank_decreases L laws W xs ys Hescape) as Hlt; lia).
  - abstract (intro xs; change (measure xs <= 2 * wbound W + 1); unfold measure;
      pose proof (wrank_bounded W (join_all L xs)) as Hbound;
      destruct (Nat.eqb (length xs) 1); lia).
Defined.
