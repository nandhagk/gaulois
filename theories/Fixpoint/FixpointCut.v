(** * Cut certificates and observer replay

    A certificate retains cut values and recomputes the other outputs in dependency order.
    For example, storing a loop head permits the remaining acyclic chain to be reconstructed.
    Builds on: FixpointIndex, FixpointCycles, FixpointLeast and CollectionsFinSet. *)

From Stdlib Require Import List Bool PArith Lia Relations.Relation_Operators.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Gaulois.Order Require Import OrderLattice OrderMonotone.
From Gaulois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex
  FixpointCycles FixpointLeast.
Import List.ListNotations.

(** A cut certificate stores cut values and the order for recomputing other outputs. *)
Record cut_certificate (X A : Type) : Type := CutCertificate {
  cuts : FinSet.t X;
  stored : assignment X A;
  plan : list X
}.

Arguments CutCertificate {X A}.
Arguments cuts {X A}.
Arguments stored {X A}.
Arguments plan {X A}.

(** A valid plan covers outputs exactly once outside the cuts and orders all declared reads. *)
Definition plan_valid {X C A} (EX : encoding X) (S : System.t X C A)
  (SS : System.static S) (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) : Prop :=
  NoDup plan /\ (forall x, In x plan -> FinSet.mem EX x cuts = false) /\
  (forall c, In c (System.constraints S) ->
    forall x, (x = System.target S c \/ In x (side_targets SS c)) ->
      FinSet.mem EX x cuts = true \/ In x plan) /\
  forall l1 x l2, plan = l1 ++ x :: l2 -> forall c, In c (contributors_of EX ix x) ->
    forall y, In y (deps SS c) ->
      FinSet.mem EX y cuts = true \/ In y l1 \/ contributors_of EX ix y = [].

Section CutImplementation.
Context {X C A : Type} (EX : encoding X) (L : lattice A) (S : System.t X C A).

Definition cut_key_eqb (x y : X) : bool := Pos.eqb (encode EX x) (encode EX y).

Lemma cut_key_eqb_spec (x y : X) : cut_key_eqb x y = true <-> x = y.
Proof.
  unfold cut_key_eqb; rewrite Pos.eqb_eq; split; [apply encode_injective|congruence].
Qed.

Fixpoint cut_seed (xs : list X) (s : X -> A) : assignment X A :=
  match xs with
  | [] => Map.empty
  | x :: xs' => Map.set EX x (s x) (cut_seed xs' s)
  end.

Fixpoint cut_prepare (xs : list X) (seen : FinSet.t X) : option (FinSet.t X) :=
  match xs with
  | [] => Some seen
  | x :: xs' =>
    if FinSet.mem EX x seen then None else cut_prepare xs' (FinSet.add EX x seen)
  end.

Definition cut_coverage (SS : System.static S) (covered : FinSet.t X) : bool :=
  forallb (fun c => forallb (fun x => FinSet.mem EX x covered)
    (System.target S c :: side_targets SS c)) (System.constraints S).

Definition cut_ready (ix : sys_index X C) (cur : assignment X A) (y : X) : bool :=
  Map.mem EX y cur || match contributors_of EX ix y with
    | [] => true
    | _ :: _ => false
    end.

Fixpoint cut_join (x : X) (ups : list (X * A)) (a : A) : A :=
  match ups with
  | [] => a
  | (y, b) :: ups' =>
    cut_join x ups' (if cut_key_eqb x y then join L a b else a)
  end.

Fixpoint cut_gather (ix : sys_index X C) (x : X) (cs : list C)
  (cur : assignment X A) (a : A) : option A :=
  match cs with
  | [] => Some a
  | c :: cs' =>
    let '(v, rs, ss) := Query.run (System.rhs S c) (lookup EX L cur) in
    if forallb (cut_ready ix cur) rs
    then cut_gather ix x cs' cur (cut_join x ((System.target S c, v) :: ss) a)
    else None
  end.

Fixpoint cut_compute (ix : sys_index X C) (xs : list X) (cur : assignment X A) :
  option (assignment X A) :=
  match xs with
  | [] => Some cur
  | x :: xs' =>
    if Map.mem EX x cur then None
    else match cut_gather ix x (contributors_of EX ix x) cur (bot L) with
      | None => None
      | Some a => cut_compute ix xs' (Map.set EX x a cur)
      end
  end.

Definition cut_check_at (ix : sys_index X C) (m : assignment X A) (x : X) : bool :=
  forallb (fun c =>
    let '(v, _, ss) := Query.run (System.rhs S c) (lookup EX L m) in
    (if cut_key_eqb x (System.target S c) then leb L v (lookup EX L m x) else true) &&
    forallb (fun ya => if cut_key_eqb x (fst ya)
      then leb L (snd ya) (lookup EX L m x) else true) ss)
    (contributors_of EX ix x).

(** Validate coverage, recompute each planned unknown once, then check only the cut outputs. *)
Definition expand (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  option (assignment X A) :=
  match cut_prepare (plan cert) (cuts cert) with
  | None => None
  | Some covered =>
    if cut_coverage SS covered then
      match cut_compute ix (plan cert)
        (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert))) with
      | None => None
      | Some m => if forallb (cut_check_at ix m) (FinSet.elements (cuts cert))
        then Some m else None
      end
    else None
  end.

Lemma cut_seed_get (xs : list X) (s : X -> A) (x : X) :
  Map.get EX x (cut_seed xs s) =
    if FinSet.mem EX x (FinSet.of_list EX xs) then Some (s x) else None.
Proof.
  induction xs as [|y xs IH]; cbn [cut_seed].
  - rewrite Map.get_empty.
    change (None = if FinSet.mem EX x FinSet.empty then Some (s x) else None).
    rewrite FinSet.mem_empty; reflexivity.
  - destruct (cut_key_eqb x y) eqn:Hxy.
    + apply cut_key_eqb_spec in Hxy; subst y; rewrite Map.get_set_same.
      assert (Hmem : FinSet.mem EX x (FinSet.of_list EX (x :: xs)) = true).
      { apply FinSet.of_list_spec; now left. }
      rewrite Hmem; reflexivity.
    + assert (Hne : x <> y).
      { intro Heq; subst y; unfold cut_key_eqb in Hxy; rewrite Pos.eqb_refl in Hxy;
          discriminate. }
      rewrite Map.get_set_other by exact Hne; rewrite IH.
      assert (Hmem : FinSet.mem EX x (FinSet.of_list EX (y :: xs)) =
        FinSet.mem EX x (FinSet.of_list EX xs)).
      { destruct (FinSet.mem EX x (FinSet.of_list EX (y :: xs))) eqn:Hcons,
          (FinSet.mem EX x (FinSet.of_list EX xs)) eqn:Htail; try reflexivity.
        - apply FinSet.of_list_spec in Hcons; cbn in Hcons.
          destruct Hcons as [Heq|Hin]; [congruence|].
          apply (proj2 (FinSet.of_list_spec EX x xs)) in Hin; congruence.
        - assert (Hin : In x (y :: xs)).
          { right; exact (proj1 (FinSet.of_list_spec EX x xs) Htail). }
          apply (proj2 (FinSet.of_list_spec EX x (y :: xs))) in Hin; congruence. }
      rewrite Hmem; reflexivity.
Qed.

Lemma cut_prepare_sound (xs : list X) (seen covered : FinSet.t X) :
  cut_prepare xs seen = Some covered ->
  NoDup xs /\ (forall x, In x xs -> FinSet.mem EX x seen = false) /\
  forall x, FinSet.mem EX x covered = true <-> FinSet.mem EX x seen = true \/ In x xs.
Proof.
  revert seen; induction xs as [|x xs IH]; intros seen Hprepare; cbn in Hprepare.
  - inversion Hprepare; subst covered; split; [constructor|]; split; cbn; tauto.
  - destruct (FinSet.mem EX x seen) eqn:Hx; [discriminate|].
    destruct (IH _ Hprepare) as [Hnodup [Hdisjoint Hmem]].
    assert (Hnotin : ~ In x xs).
    { intro Hin; specialize (Hdisjoint x Hin).
      assert (Hpresent : FinSet.mem EX x (FinSet.add EX x seen) = true).
      { apply FinSet.mem_add; now left. }
      congruence. }
    split; [now constructor|]; split.
    + intros y [Heq|Hin]; [now subst y|].
      specialize (Hdisjoint y Hin).
      destruct (FinSet.mem EX y seen) eqn:Hy; [|reflexivity].
      assert (Hpresent : FinSet.mem EX y (FinSet.add EX x seen) = true).
      { apply FinSet.mem_add; now right. }
      congruence.
    + intro y; rewrite Hmem, FinSet.mem_add; cbn; intuition congruence.
Qed.

Lemma cut_prepare_complete (xs : list X) (seen : FinSet.t X) :
  NoDup xs -> (forall x, In x xs -> FinSet.mem EX x seen = false) ->
  exists covered, cut_prepare xs seen = Some covered.
Proof.
  intros Hnodup; revert seen; induction Hnodup as [|x xs Hnotin Hnodup IH];
    intros seen Hdisjoint; cbn.
  - eexists; reflexivity.
  - rewrite Hdisjoint by now left.
    apply IH; intros y Hin.
    destruct (FinSet.mem EX y (FinSet.add EX x seen)) eqn:Hy; [|reflexivity].
    apply FinSet.mem_add in Hy as [Heq|Hy]; [subst y; contradiction|].
    pose proof (Hdisjoint y (or_intror Hin)) as Habsent; congruence.
Qed.

Lemma cut_coverage_spec (SS : System.static S) (covered : FinSet.t X) :
  cut_coverage SS covered = true <-> forall c, In c (System.constraints S) ->
    forall x, x = System.target S c \/ In x (side_targets SS c) ->
    FinSet.mem EX x covered = true.
Proof.
  unfold cut_coverage; rewrite forallb_forall; split.
  - intros H c Hc x Hx; apply (proj1 (forallb_forall _ _) (H c Hc) x).
    cbn; intuition congruence.
  - intros H c Hc; apply forallb_forall; intros x Hx; apply (H c Hc x).
    cbn in Hx; intuition congruence.
Qed.

Lemma cut_join_upper (HL : lattice_laws L) (x : X) (ups : list (X * A)) (a : A) :
  leb L a (cut_join x ups a) = true /\
  forall b, In (x, b) ups -> leb L b (cut_join x ups a) = true.
Proof.
  revert a; induction ups as [|[y b] ups IH]; intro a; cbn [cut_join].
  - split; [apply (leb_refl HL)|intros b Hin; contradiction].
  - destruct (cut_key_eqb x y) eqn:Hxy.
    + apply cut_key_eqb_spec in Hxy; subst y.
      destruct (IH (join L a b)) as [Hacc Hups]; split.
      * eapply (leb_trans HL); [apply (join_upper_l HL)|exact Hacc].
      * intros d [Heq|Hin].
        -- inversion Heq; subst d.
           eapply (leb_trans HL); [apply (join_upper_r HL)|exact Hacc].
        -- exact (Hups d Hin).
    + destruct (IH a) as [Hacc Hups]; split; [exact Hacc|].
      intros d [Heq|Hin].
      * inversion Heq; subst y; unfold cut_key_eqb in Hxy;
          rewrite Pos.eqb_refl in Hxy; discriminate.
      * exact (Hups d Hin).
Qed.

Lemma cut_join_below (HJ : lub_laws L) (x : X) (ups : list (X * A)) (a b : A) :
  leb L a b = true -> (forall d, In (x, d) ups -> leb L d b = true) ->
  leb L (cut_join x ups a) b = true.
Proof.
  revert a; induction ups as [|[y d] ups IH]; intros a Ha Hups; cbn [cut_join].
  - exact Ha.
  - apply IH.
    + destruct (cut_key_eqb x y) eqn:Hxy; [|exact Ha].
      apply cut_key_eqb_spec in Hxy; subst y.
      apply (join_least HJ); [exact Ha|apply Hups; now left].
    + intros e Hin; apply Hups; now right.
Qed.

Lemma cut_lookup_set (cur : assignment X A) (x : X) (a : A) :
  lookup EX L (Map.set EX x a cur) x = a.
Proof.
  unfold lookup; rewrite Map.get_set_same; reflexivity.
Qed.

Lemma cut_lookup_other (cur : assignment X A) (x y : X) (a : A) :
  y <> x -> lookup EX L (Map.set EX x a cur) y = lookup EX L cur y.
Proof.
  intro Hne; unfold lookup; rewrite Map.get_set_other by exact Hne; reflexivity.
Qed.

Lemma cut_mem_false (cur : assignment X A) (x : X) :
  Map.mem EX x cur = false -> Map.get EX x cur = None.
Proof.
  unfold Map.mem; destruct (Map.get EX x cur); congruence.
Qed.

Lemma cut_ready_set (ix : sys_index X C) (cur : assignment X A) (x y : X) (a : A) :
  cut_ready ix cur y = true -> cut_ready ix (Map.set EX x a cur) y = true.
Proof.
  unfold cut_ready; rewrite !orb_true_iff; intros [Hmem|Hnone]; [left|now right].
  unfold Map.mem in *.
  destruct (cut_key_eqb y x) eqn:Hyx.
  - apply cut_key_eqb_spec in Hyx; subst y; rewrite Map.get_set_same; reflexivity.
  - assert (Hne : y <> x).
    { intro Heq; subst; unfold cut_key_eqb in Hyx; rewrite Pos.eqb_refl in Hyx; discriminate. }
    rewrite Map.get_set_other by exact Hne; exact Hmem.
Qed.

Lemma cut_ready_written (ix : sys_index X C) (cur : assignment X A) (x : X) (a : A) :
  cut_ready ix (Map.set EX x a cur) x = true.
Proof.
  unfold cut_ready, Map.mem; rewrite Map.get_set_same; reflexivity.
Qed.

Lemma cut_write_stable (ix : sys_index X C) (cur : assignment X A) (x : X) (a : A) :
  Map.mem EX x cur = false -> (contributors_of EX ix x = [] -> a = bot L) ->
  forall y, cut_ready ix cur y = true ->
    lookup EX L cur y = lookup EX L (Map.set EX x a cur) y.
Proof.
  intros Hfresh Hbot y Hready.
  destruct (cut_key_eqb y x) eqn:Hyx.
  - apply cut_key_eqb_spec in Hyx; subst y.
    unfold cut_ready in Hready; rewrite Hfresh in Hready; cbn in Hready.
    destruct (contributors_of EX ix x) eqn:Hcs; [|discriminate].
    rewrite cut_lookup_set, (Hbot eq_refl).
    unfold lookup; rewrite (cut_mem_false cur x Hfresh); reflexivity.
  - symmetry; apply cut_lookup_other.
    intro Heq; subst y; unfold cut_key_eqb in Hyx; rewrite Pos.eqb_refl in Hyx; discriminate.
Qed.

Lemma cut_compute_stable (ix : sys_index X C) (xs : list X) (cur m : assignment X A) :
  cut_compute ix xs cur = Some m -> forall y, cut_ready ix cur y = true ->
    lookup EX L cur y = lookup EX L m y.
Proof.
  revert cur; induction xs as [|x xs IH]; intros cur Hcompute y Hready; cbn in Hcompute.
  - inversion Hcompute; reflexivity.
  - destruct (Map.mem EX x cur) eqn:Hfresh; [discriminate|].
    destruct (cut_gather ix x (contributors_of EX ix x) cur (bot L)) as [a|] eqn:Hgather;
      [|discriminate].
    transitivity (lookup EX L (Map.set EX x a cur) y).
    + apply (cut_write_stable ix); [exact Hfresh| |exact Hready].
      intro Hnone; rewrite Hnone in Hgather; cbn in Hgather; now inversion Hgather.
    + apply (IH _ Hcompute y); apply cut_ready_set; exact Hready.
Qed.

Lemma cut_updates_determined (c : C) (cur : assignment X A) (t : X -> A) :
  (forall y, In y (Query.reads (System.rhs S c) (lookup EX L cur)) -> lookup EX L cur y = t y) ->
  run_updates S c (lookup EX L cur) = run_updates S c t.
Proof.
  intro Hagree; destruct (query_determined _ _ _ Hagree) as [Hv [_ Hs]].
  unfold run_updates; rewrite !run_spec, Hv, Hs; reflexivity.
Qed.

Lemma cut_gather_sound (HL : lattice_laws L) (ix : sys_index X C) (x : X)
  (cs : list C) (cur : assignment X A) (t : X -> A) (a r : A) :
  (forall y, cut_ready ix cur y = true -> lookup EX L cur y = t y) ->
  cut_gather ix x cs cur a = Some r -> leb L a r = true /\
  forall c, In c cs -> forall b, In (x, b) (run_updates S c t) -> leb L b r = true.
Proof.
  revert a; induction cs as [|c cs IH]; intros a Hagree Hgather; cbn in Hgather.
  - inversion Hgather; subst r; split; [apply (leb_refl HL)|intros c Hc; contradiction].
  - rewrite run_spec in Hgather; cbn in Hgather.
    destruct (forallb (cut_ready ix cur) (Query.reads (System.rhs S c) (lookup EX L cur)))
      eqn:Hready; [|discriminate].
    destruct (IH _ Hagree Hgather) as [Hacc Hcs].
    destruct (cut_join_upper HL x (run_updates S c (lookup EX L cur)) a) as [Ha Hups].
    unfold run_updates in Ha, Hups; rewrite run_spec in Ha, Hups.
    split.
    + eapply (leb_trans HL); [exact Ha|exact Hacc].
    + intros d [Heq|Hd] b Hb; [subst d|exact (Hcs d Hd b Hb)].
      assert (Hsame : run_updates S c (lookup EX L cur) = run_updates S c t).
      { apply cut_updates_determined; intros y Hy; apply Hagree.
        exact (proj1 (forallb_forall _ _) Hready y Hy). }
      rewrite <- Hsame in Hb; unfold run_updates in Hb; rewrite run_spec in Hb.
      eapply (leb_trans HL); [exact (Hups b Hb)|exact Hacc].
Qed.

Lemma cut_compute_outputs (HL : lattice_laws L) (ix : sys_index X C)
  (xs : list X) (cur m : assignment X A) :
  cut_compute ix xs cur = Some m -> forall x, In x xs ->
    forall c, In c (contributors_of EX ix x) -> forall b,
    In (x, b) (run_updates S c (lookup EX L m)) -> leb L b (lookup EX L m x) = true.
Proof.
  revert cur; induction xs as [|x xs IH]; intros cur Hcompute y Hy c Hc b Hb.
  - contradiction.
  - cbn in Hcompute.
    destruct (Map.mem EX x cur) eqn:Hfresh; [discriminate|].
    destruct (cut_gather ix x (contributors_of EX ix x) cur (bot L)) as [a|] eqn:Hgather;
      [|discriminate].
    destruct Hy as [Heq|Hy]; [subst y|exact (IH _ Hcompute y Hy c Hc b Hb)].
    assert (Hagree : forall y, cut_ready ix cur y = true ->
      lookup EX L cur y = lookup EX L m y).
    { apply (cut_compute_stable ix (x :: xs) cur m); cbn; rewrite Hfresh, Hgather;
        exact Hcompute. }
    pose proof (cut_gather_sound HL ix x _ cur _ _ _ Hagree Hgather) as [_ Hbounds].
    assert (Hvalue : a = lookup EX L m x).
    { rewrite <- (cut_lookup_set cur x a).
      apply (cut_compute_stable ix xs _ m Hcompute x); apply cut_ready_written. }
    rewrite <- Hvalue; exact (Hbounds c Hc b Hb).
Qed.

Lemma cut_seed_in (xs : list X) (s : X -> A) (x : X) :
  In x xs -> Map.get EX x (cut_seed xs s) = Some (s x).
Proof.
  intro Hin; rewrite cut_seed_get, (proj2 (FinSet.of_list_spec EX x xs) Hin); reflexivity.
Qed.

Lemma cut_seed_notin (xs : list X) (s : X -> A) (x : X) :
  ~ In x xs -> Map.get EX x (cut_seed xs s) = None.
Proof.
  intro Hnotin; rewrite cut_seed_get.
  destruct (FinSet.mem EX x (FinSet.of_list EX xs)) eqn:Hmem; [|reflexivity].
  exfalso; apply Hnotin; exact (proj1 (FinSet.of_list_spec EX x xs) Hmem).
Qed.

Lemma cut_check_at_spec (ix : sys_index X C) (m : assignment X A) (x : X) :
  cut_check_at ix m x = true <-> forall c, In c (contributors_of EX ix x) ->
    forall b, In (x, b) (run_updates S c (lookup EX L m)) -> leb L b (lookup EX L m x) = true.
Proof.
  unfold cut_check_at; rewrite forallb_forall; split.
  - intros H c Hc b Hb; specialize (H c Hc); rewrite run_spec in H; cbn in H.
    apply andb_true_iff in H as [Hv Hs].
    unfold run_updates in Hb; rewrite run_spec in Hb; cbn in Hb.
    destruct Hb as [Heq|Hin].
    + injection Heq as Htarget Hvalue; subst b.
      rewrite Htarget in Hv.
      unfold cut_key_eqb in Hv; rewrite Pos.eqb_refl in Hv; exact Hv.
    + pose proof (proj1 (forallb_forall _ _) Hs (x, b) Hin) as Hbound.
      cbn in Hbound; unfold cut_key_eqb in Hbound; rewrite Pos.eqb_refl in Hbound;
        exact Hbound.
  - intros H c Hc; rewrite run_spec; cbn; apply andb_true_iff; split.
    + destruct (cut_key_eqb x (System.target S c)) eqn:Htarget; [|reflexivity].
      apply cut_key_eqb_spec in Htarget; apply (H c Hc).
      unfold run_updates; rewrite run_spec; cbn; left; now rewrite Htarget.
    + apply forallb_forall; intros [y b] Hin; cbn.
      destruct (cut_key_eqb x y) eqn:Hxy; [|reflexivity].
      apply cut_key_eqb_spec in Hxy; subst y; apply (H c Hc).
      unfold run_updates; rewrite run_spec; cbn; now right.
Qed.

Lemma expand_accepted (SS : System.static S) (ix : sys_index X C)
  (cert : cut_certificate X A) (m : assignment X A) :
  expand SS ix cert = Some m -> exists covered,
    cut_prepare (plan cert) (cuts cert) = Some covered /\ cut_coverage SS covered = true /\
    cut_compute ix (plan cert)
      (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert))) = Some m /\
    forallb (cut_check_at ix m) (FinSet.elements (cuts cert)) = true.
Proof.
  unfold expand.
  destruct (cut_prepare (plan cert) (cuts cert)) as [covered|] eqn:Hprepare;
    [|discriminate].
  destruct (cut_coverage SS covered) eqn:Hcoverage; [|discriminate].
  destruct (cut_compute ix (plan cert)
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert)))) as [result|]
    eqn:Hcompute; [|discriminate].
  destruct (forallb (cut_check_at ix result) (FinSet.elements (cuts cert))) eqn:Hcheck;
    [|discriminate].
  intro Heq; inversion Heq; subst result; exists covered; auto.
Qed.

Lemma cut_preserves_stored (ix : sys_index X C) (cert : cut_certificate X A)
  (m : assignment X A) :
  FinSet.wf EX (cuts cert) ->
  cut_compute ix (plan cert)
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert))) = Some m ->
  forall p, FinSet.mem EX p (cuts cert) = true ->
    lookup EX L m p = lookup EX L (stored cert) p.
Proof.
  intros Hwf Hcompute p Hp.
  assert (Hin : In p (FinSet.elements (cuts cert))).
  { exact (proj2 (FinSet.elements_spec EX p _ Hwf) Hp). }
  pose proof (cut_seed_in (FinSet.elements (cuts cert)) (lookup EX L (stored cert)) p Hin)
    as Hseed.
  assert (Hready : cut_ready ix
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert))) p = true).
  { unfold cut_ready, Map.mem; rewrite Hseed; reflexivity. }
  rewrite <- (cut_compute_stable ix _ _ m Hcompute p Hready).
  unfold lookup at 1; rewrite Hseed; reflexivity.
Qed.

(** An accepted expansion satisfies every constraint and preserves the stored cut values. *)
Theorem expand_sound (m : assignment X A) (SS : System.static S) (ix : sys_index X C)
  (cert : cut_certificate X A) :
  lattice_laws L -> sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) ->
  expand SS ix cert = Some m -> post_solution L S (lookup EX L m) /\
  forall p, FinSet.mem EX p (cuts cert) = true ->
    lookup EX L m p = lookup EX L (stored cert) p.
Proof.
  intros HL Hix Hwf Hexpand.
  destruct (expand_accepted SS ix cert m Hexpand) as
    [covered [Hprepare [Hcoverage [Hcompute Hcheck]]]].
  destruct (cut_prepare_sound _ _ _ Hprepare) as [_ [_ Hcovered]].
  assert (Houtputs : forall x c, In c (System.constraints S) ->
    (x = System.target S c \/ In x (side_targets SS c)) ->
    forall b, In (x, b) (run_updates S c (lookup EX L m)) -> leb L b (lookup EX L m x) = true).
  { intros x c Hc Hx b Hb.
    assert (Hcontributor : In c (contributors_of EX ix x)).
    { apply (contributors_agree Hix); split; [exact Hc|intuition congruence]. }
    pose proof (proj1 (cut_coverage_spec SS covered) Hcoverage c Hc x Hx) as Hpresent.
    apply Hcovered in Hpresent as [Hcut|Hplan].
    - assert (Hchecked : cut_check_at ix m x = true).
      { apply (proj1 (forallb_forall _ _) Hcheck x).
        exact (proj2 (FinSet.elements_spec EX x _ Hwf) Hcut). }
      exact (proj1 (cut_check_at_spec ix m x) Hchecked c Hcontributor b Hb).
    - exact (cut_compute_outputs HL ix _ _ m Hcompute x Hplan c Hcontributor b Hb). }
  split.
  - intros c Hc; split.
    + apply (Houtputs (System.target S c) c Hc); [now left|].
      unfold run_updates; rewrite run_spec; cbn; now left.
    + intros x a Hin; apply (Houtputs x c Hc).
      * right; apply (System.sides_within SS c (lookup EX L m)).
        apply in_map_iff; exists (x, a); auto.
      * unfold run_updates; rewrite run_spec; cbn; now right.
  - exact (cut_preserves_stored ix cert m Hwf Hcompute).
Qed.

Lemma cut_gather_complete (HL : lattice_laws L) (HJ : lub_laws L)
  (HM : monotone_system L S) (t : X -> A) (ix : sys_index X C) (x : X)
  (cs : list C) (cur : assignment X A) (a : A) :
  post_solution L S t -> fun_leb L (lookup EX L cur) t -> leb L a (t x) = true ->
  (forall c, In c cs -> In c (System.constraints S)) ->
  (forall c, In c cs -> forall y,
    In y (Query.reads (System.rhs S c) (lookup EX L cur)) -> cut_ready ix cur y = true) ->
  exists r, cut_gather ix x cs cur a = Some r /\ leb L r (t x) = true.
Proof.
  intros Hpost Hbelow; revert a; induction cs as [|c cs IH];
    intros a Ha Hlisted Hready; cbn.
  - exists a; auto.
  - rewrite run_spec; cbn.
    assert (Hreads : forallb (cut_ready ix cur)
      (Query.reads (System.rhs S c) (lookup EX L cur)) = true).
    { apply forallb_forall; intros y Hy; apply (Hready c (or_introl eq_refl) y Hy). }
    rewrite Hreads; apply IH.
    + change (leb L (cut_join x
        ((System.target S c, Query.eval (System.rhs S c) (lookup EX L cur)) ::
          Query.sides (System.rhs S c) (lookup EX L cur)) a) (t x) = true).
      apply (cut_join_below HJ); [exact Ha|].
      intros b Hb.
      apply (run_updates_below L S HL (lookup EX L cur) t c).
      * apply HM; apply Hlisted; now left.
      * exact Hpost.
      * apply Hlisted; now left.
      * exact Hbelow.
      * unfold run_updates; rewrite run_spec; exact Hb.
    + intros d Hd; apply Hlisted; now right.
    + intros d Hd y Hy; apply (Hready d (or_intror Hd) y Hy).
Qed.

Definition cut_ordered (SS : System.static S) (ix : sys_index X C)
  (xs : list X) (cur : assignment X A) : Prop :=
  forall l1 x l2, xs = l1 ++ x :: l2 -> forall c, In c (contributors_of EX ix x) ->
    forall y, In y (deps SS c) -> cut_ready ix cur y = true \/ In y l1.

Lemma cut_ordered_tail (SS : System.static S) (ix : sys_index X C)
  (x : X) (xs : list X) (cur : assignment X A) (a : A) :
  cut_ordered SS ix (x :: xs) cur -> cut_ordered SS ix xs (Map.set EX x a cur).
Proof.
  intros Horder l1 y l2 Heq c Hc z Hz.
  destruct (Horder (x :: l1) y l2 (f_equal (cons x) Heq) c Hc z Hz) as [Hready|Hin].
  - left; apply cut_ready_set; exact Hready.
  - destruct Hin as [Heqz|Hin]; [subst z; left; apply cut_ready_written|now right].
Qed.

Lemma cut_fresh_tail (x : X) (xs : list X) (cur : assignment X A) (a : A) :
  ~ In x xs -> (forall y, In y (x :: xs) -> Map.mem EX y cur = false) ->
  forall y, In y xs -> Map.mem EX y (Map.set EX x a cur) = false.
Proof.
  intros Hnotin Hfresh y Hin; unfold Map.mem.
  assert (Hne : y <> x) by (intro Heq; subst y; contradiction).
  rewrite Map.get_set_other by exact Hne.
  exact (Hfresh y (or_intror Hin)).
Qed.

Lemma cut_write_below (cur : assignment X A) (t : X -> A) (x : X) (a : A) :
  fun_leb L (lookup EX L cur) t -> leb L a (t x) = true ->
  fun_leb L (lookup EX L (Map.set EX x a cur)) t.
Proof.
  intros Hbelow Ha y; destruct (cut_key_eqb y x) eqn:Hyx.
  - apply cut_key_eqb_spec in Hyx; subst y; rewrite cut_lookup_set; exact Ha.
  - rewrite cut_lookup_other; [apply Hbelow|].
    intro Heq; subst y; unfold cut_key_eqb in Hyx; rewrite Pos.eqb_refl in Hyx; discriminate.
Qed.

Lemma cut_compute_complete (HL : lattice_laws L) (HJ : lub_laws L)
  (HM : monotone_system L S) (SS : System.static S) (ix : sys_index X C)
  (t : X -> A) (xs : list X) (cur : assignment X A) :
  sys_index_laws EX S SS ix -> post_solution L S t -> NoDup xs ->
  (forall x, In x xs -> Map.mem EX x cur = false) ->
  cut_ordered SS ix xs cur -> fun_leb L (lookup EX L cur) t ->
  exists m, cut_compute ix xs cur = Some m /\ fun_leb L (lookup EX L m) t.
Proof.
  intros Hix Hpost Hnodup; revert cur;
    induction Hnodup as [|x xs Hnotin Hnodup IH]; intros cur Hfresh Horder Hbelow; cbn.
  - exists cur; auto.
  - rewrite Hfresh by now left.
    destruct (cut_gather_complete HL HJ HM t ix x (contributors_of EX ix x) cur (bot L)
      Hpost Hbelow (bot_least HL _) ) as [a [Hgather Ha]].
    + intros c Hc; exact (proj1 (proj1 (contributors_agree Hix x c) Hc)).
    + intros c Hc y Hy.
      destruct (Horder [] x xs eq_refl c Hc y
        (System.reads_within SS c (lookup EX L cur) y Hy)) as [Hready|Hin];
        [exact Hready|contradiction].
    + rewrite Hgather; apply IH.
      * apply (cut_fresh_tail x xs cur a Hnotin Hfresh).
      * apply cut_ordered_tail; exact Horder.
      * apply cut_write_below; assumption.
Qed.

Lemma cut_initial_below (HL : lattice_laws L) (cert : cut_certificate X A) (s : X -> A) :
  FinSet.wf EX (cuts cert) ->
  (forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L (stored cert) p = s p) ->
  fun_leb L (lookup EX L
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert)))) s.
Proof.
  intros Hwf Hstored x; unfold lookup at 1; rewrite cut_seed_get.
  destruct (FinSet.mem EX x (FinSet.of_list EX (FinSet.elements (cuts cert)))) eqn:Hx.
  - apply FinSet.of_list_spec in Hx.
    rewrite Hstored; [apply (leb_refl HL)|].
    exact (proj1 (FinSet.elements_spec EX x _ Hwf) Hx).
  - apply (bot_least HL).
Qed.

Lemma cut_initial_ordered (SS : System.static S) (ix : sys_index X C)
  (cert : cut_certificate X A) :
  FinSet.wf EX (cuts cert) -> plan_valid EX S SS ix (cuts cert) (plan cert) ->
  cut_ordered SS ix (plan cert)
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert))).
Proof.
  intros Hwf [_ [_ [_ Horder]]] l1 x l2 Heq c Hc y Hy.
  destruct (Horder l1 x l2 Heq c Hc y Hy) as [Hcut|[Hin|Hnone]].
  - left; unfold cut_ready, Map.mem.
    rewrite cut_seed_in; [reflexivity|].
    exact (proj2 (FinSet.elements_spec EX y _ Hwf) Hcut).
  - now right.
  - left; unfold cut_ready; rewrite Hnone; apply orb_true_r.
Qed.

(** A post-solution's cut values and any valid plan are accepted and reconstruct values below it. *)
Theorem expand_complete (s : X -> A) (SS : System.static S) (ix : sys_index X C)
  (cert : cut_certificate X A) :
  lattice_laws L -> lub_laws L -> monotone_system L S -> sys_index_laws EX S SS ix ->
  FinSet.wf EX (cuts cert) -> post_solution L S s ->
  plan_valid EX S SS ix (cuts cert) (plan cert) ->
  (forall p, FinSet.mem EX p (cuts cert) = true -> lookup EX L (stored cert) p = s p) ->
  exists m, expand SS ix cert = Some m /\ fun_leb L (lookup EX L m) s.
Proof.
  intros HL HJ HM Hix Hwf Hpost Hvalid Hstored.
  destruct Hvalid as [Hnodup [Hdisjoint [Hcovers Horder]]].
  destruct (cut_prepare_complete (plan cert) (cuts cert) Hnodup Hdisjoint)
    as [covered Hprepare].
  destruct (cut_prepare_sound _ _ _ Hprepare) as [_ [_ Hcovered]].
  assert (Hcoverage : cut_coverage SS covered = true).
  { apply cut_coverage_spec; intros c Hc x Hx; apply Hcovered; exact (Hcovers c Hc x Hx). }
  destruct (cut_compute_complete HL HJ HM SS ix s (plan cert)
    (cut_seed (FinSet.elements (cuts cert)) (lookup EX L (stored cert)))
    Hix Hpost Hnodup) as [m [Hcompute Hbelow]].
  - intros x Hx; unfold Map.mem; rewrite cut_seed_notin; [reflexivity|].
    intro Hin; apply (FinSet.elements_spec EX x _ Hwf) in Hin.
    rewrite (Hdisjoint x Hx) in Hin; discriminate.
  - apply cut_initial_ordered; [exact Hwf|].
    split; [exact Hnodup|]; split; [exact Hdisjoint|]; now split.
  - exact (cut_initial_below HL cert s Hwf Hstored).
  - assert (Hcheck : forallb (cut_check_at ix m) (FinSet.elements (cuts cert)) = true).
    { apply forallb_forall; intros x Hx; apply cut_check_at_spec; intros c Hc b Hb.
      assert (Hcut : FinSet.mem EX x (cuts cert) = true).
      { exact (proj1 (FinSet.elements_spec EX x _ Hwf) Hx). }
      rewrite (cut_preserves_stored ix cert m Hwf Hcompute x Hcut), (Hstored x Hcut).
      apply (run_updates_below L S HL (lookup EX L m) s c).
      - apply HM; exact (proj1 (proj1 (contributors_agree Hix x c) Hc)).
      - exact Hpost.
      - exact (proj1 (proj1 (contributors_agree Hix x c) Hc)).
      - exact Hbelow.
      - exact Hb. }
    exists m; split; [|exact Hbelow].
    unfold expand; rewrite Hprepare, Hcoverage, Hcompute, Hcheck; reflexivity.
Qed.

End CutImplementation.

(** Replay folds an observer through the requested order without retaining intermediate results. *)
Definition replay {X A B} (obs : B -> X -> A -> B) (b0 : B) (order : list X) (s : X -> A) : B :=
  fold_left (fun b x => obs b x (s x)) order b0.

Section PlanCycles.
Context {X C A : Type} (EX : encoding X) (S : System.t X C A) (SS : System.static S).

Fixpoint cut_position (x : X) (xs : list X) : nat :=
  match xs with
  | [] => 0
  | y :: xs' => if cut_key_eqb EX x y then 0 else Datatypes.S (cut_position x xs')
  end.

Lemma cut_key_neq (x y : X) : x <> y -> cut_key_eqb EX x y = false.
Proof.
  intro Hne; destruct (cut_key_eqb EX x y) eqn:Hxy; [|reflexivity].
  apply cut_key_eqb_spec in Hxy; contradiction.
Qed.

Lemma cut_position_prefix (l1 l2 : list X) (x y : X) :
  NoDup (l1 ++ x :: l2) -> In y l1 ->
  cut_position y (l1 ++ x :: l2) < cut_position x (l1 ++ x :: l2).
Proof.
  induction l1 as [|z l1 IH]; intros Hnodup Hin; [contradiction|].
  inversion Hnodup as [|z' tail Hfresh Htail]; subst z' tail.
  assert (Hxz : x <> z).
  { intro Heq; subst z; apply Hfresh; apply in_or_app; right; now left. }
  cbn [app cut_position]; rewrite (cut_key_neq x z Hxz).
  destruct Hin as [Heq|Hin].
  - subst y; unfold cut_key_eqb at 1; rewrite Pos.eqb_refl; lia.
  - assert (Hyz : y <> z).
    { intro Heq; subst z; apply Hfresh; apply in_or_app; now left. }
    rewrite (cut_key_neq y z Hyz); specialize (IH Htail Hin); lia.
Qed.

Lemma flow_has_contributor (ix : sys_index X C) (y x : X) :
  sys_index_laws EX S SS ix -> flows SS y x -> contributors_of EX ix x <> [].
Proof.
  intros Hix [c [Hc [_ Hx]]] Hempty.
  assert (Hin : In c (contributors_of EX ix x)).
  { apply (contributors_agree Hix); split; [exact Hc|intuition congruence]. }
  rewrite Hempty in Hin; contradiction.
Qed.

Lemma flow_position (ix : sys_index X C) (cut : FinSet.t X) (order : list X) (y x : X) :
  sys_index_laws EX S SS ix -> plan_valid EX S SS ix cut order ->
  flows SS y x -> FinSet.mem EX y cut = false -> FinSet.mem EX x cut = false ->
  contributors_of EX ix y <> [] -> cut_position y order < cut_position x order.
Proof.
  intros Hix [Hnodup [_ [Hcoverage Horder]]] [c [Hc [Hy Hx]]] Hcy Hcx Hcontrib.
  destruct (Hcoverage c Hc x Hx) as [Hcut|Hin]; [congruence|].
  apply in_split in Hin as [l1 [l2 Heq]].
  assert (Hmember : In c (contributors_of EX ix x)).
  { apply (contributors_agree Hix); split; [exact Hc|intuition congruence]. }
  destruct (Horder l1 x l2 Heq c Hmember y Hy) as [Hcut|[Hbefore|Hnone]];
    [congruence| |contradiction].
  rewrite Heq; apply cut_position_prefix; [now rewrite <- Heq|exact Hbefore].
Qed.

Lemma cut_path_position (ix : sys_index X C) (cut : FinSet.t X) (order : list X) :
  sys_index_laws EX S SS ix -> plan_valid EX S SS ix cut order ->
  forall x y, clos_trans X (fun u v => flows SS u v /\ FinSet.mem EX v cut = false) x y ->
    FinSet.mem EX y cut = false /\ contributors_of EX ix y <> [] /\
    (FinSet.mem EX x cut = false -> contributors_of EX ix x <> [] ->
      cut_position x order < cut_position y order).
Proof.
  intros Hix Hvalid x y Hpath; induction Hpath as [x y [Hflow Hcut]|x y z Hxy IHxy Hyz IHyz].
  - split; [exact Hcut|]; split.
    + exact (flow_has_contributor ix x y Hix Hflow).
    + intros Hx Hcontrib; exact (flow_position ix cut order x y Hix Hvalid Hflow Hx Hcut Hcontrib).
  - destruct IHxy as [Hcy [Hcontriby Hposxy]].
    destruct IHyz as [Hcz [Hcontribz Hposyz]].
    split; [exact Hcz|]; split; [exact Hcontribz|].
    intros Hcx Hcontribx; specialize (Hposxy Hcx Hcontribx);
      specialize (Hposyz Hcy Hcontriby); lia.
Qed.

(** A valid non-cut plan forces strict progress along every flow and therefore cuts all cycles. *)
Theorem plan_valid_cuts (ix : sys_index X C) (cuts : FinSet.t X) (plan : list X) :
  sys_index_laws EX S SS ix -> plan_valid EX S SS ix cuts plan ->
  cuts_every_cycle SS (fun x => FinSet.mem EX x cuts).
Proof.
  intros Hix Hvalid x Hcycle.
  destruct (cut_path_position ix cuts plan Hix Hvalid x x Hcycle) as [Hcut [Hcontrib Hpos]].
  specialize (Hpos Hcut Hcontrib); lia.
Qed.

End PlanCycles.

Section ReplayLaws.
Context {X A : Type}.

(** An observer that preserves an invariant at each visited unknown preserves it for the fold. *)
Theorem replay_invariant (s : X -> A) {B} (I : B -> Prop) (obs : B -> X -> A -> B)
  (b0 : B) (order : list X) :
  I b0 -> (forall b x, In x order -> I b -> I (obs b x (s x))) ->
  I (replay obs b0 order s).
Proof.
  revert b0; induction order as [|x order IH]; intros b0 Hinitial Hstep; cbn [replay].
  - exact Hinitial.
  - apply IH.
    + apply Hstep; [now left|exact Hinitial].
    + intros b y Hy Hb; apply Hstep; [now right|exact Hb].
Qed.

End ReplayLaws.

(** An accepted certificate lists every output once among its cut points and planned unknowns. *)
Theorem replay_covers {X C A} (EX : encoding X) (L : lattice A) (S : System.t X C A)
  (m : assignment X A) (SS : System.static S) (ix : sys_index X C) (cert : cut_certificate X A) :
  sys_index_laws EX S SS ix -> FinSet.wf EX (cuts cert) -> expand EX L S SS ix cert = Some m ->
  NoDup (FinSet.elements (cuts cert) ++ plan cert) /\
  forall x, (exists c, In c (System.constraints S) /\
    (x = System.target S c \/ In x (side_targets SS c))) ->
    In x (FinSet.elements (cuts cert) ++ plan cert).
Proof.
  intros Hix Hwf Hexpand.
  destruct (expand_accepted EX L S SS ix cert m Hexpand) as
    [covered [Hprepare [Hcoverage _]]].
  destruct (cut_prepare_sound EX _ _ _ Hprepare) as [Hnodup [Hdisjoint Hcovered]].
  split.
  - apply NoDup_app.
    + apply (FinSet.elements_nodup EX); exact Hwf.
    + exact Hnodup.
    + intros x Hcut Hplan.
      apply (FinSet.elements_spec EX x _ Hwf) in Hcut.
      rewrite (Hdisjoint x Hplan) in Hcut; discriminate.
  - intros x [c [Hc Hx]]; apply in_or_app.
    pose proof (proj1 (cut_coverage_spec EX S SS covered) Hcoverage c Hc x Hx) as Hpresent.
    apply Hcovered in Hpresent as [Hcut|Hplan]; [left|now right].
    exact (proj2 (FinSet.elements_spec EX x _ Hwf) Hcut).
Qed.
