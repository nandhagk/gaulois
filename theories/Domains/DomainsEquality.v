(** * Equality partitions with forgetting

    Well-formed union-find forests describe equal keys; unreachable states form a fresh bottom.
    For example, forgetting the middle key of a three-key class preserves the other equality.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsUnionFind and Order. *)

From Stdlib Require Import List Bool PArith.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
Import List.ListNotations.

(** Reached partitions carry the forest invariant needed by every union-find operation. *)
Definition partition {K} (E : encoding K) : Type :=
  lift_bot { u : UnionFind.t K | UnionFind.wf E u }.

(** Unreachable partitions relate all keys; reached partitions compare representatives. *)
Definition partition_equiv {K} (E : encoding K) (p : partition E) (x y : K) : Prop :=
  match p with
  | Unreached => True
  | Reached u => UnionFind.equiv E (proj1_sig u) x y
  end.

Section Grouping.
Context {K J : Type} (E : encoding K) (F : encoding J) (label : K -> J).

(* The index records one classmate per label, so each support key needs one lookup. *)
Fixpoint partition_group (keys : list K) : Map.t J K * UnionFind.t K :=
  match keys with
  | [] => (Map.empty, UnionFind.make)
  | x :: rest =>
    let '(index, u) := partition_group rest in
    match Map.get F (label x) index with
    | Some r => (index, UnionFind.union E x r u)
    | None => (Map.set F (label x) x index, u)
    end
  end.

Definition partition_group_invariant (keys : list K) (index : Map.t J K)
  (u : UnionFind.t K) : Prop :=
  UnionFind.wf E u /\
  (forall j r, Map.get F j index = Some r -> In r keys /\ label r = j) /\
  (forall a, In a keys -> exists r, Map.get F (label a) index = Some r /\
    UnionFind.equiv E u a r) /\
  (forall a b, UnionFind.equiv E u a b ->
    a = b \/ In a keys /\ In b keys /\ label a = label b).

Lemma partition_group_step_found keys index u x r :
  partition_group_invariant keys index u -> Map.get F (label x) index = Some r ->
  partition_group_invariant (x :: keys) index (UnionFind.union E x r u).
Proof.
  intros [Hwf [Hindex [Hcomplete Hsound]]] Hget.
  destruct (Hindex (label x) r Hget) as [Hr Hlabel].
  split; [now apply UnionFind.wf_union|]; split.
  - intros j a Hread; destruct (Hindex j a Hread) as [Ha Hj]; split; [now right|exact Hj].
  - split.
    + intros a [Heq|Ha].
      * subst a; exists r; split; [exact Hget|].
        apply UnionFind.union_equiv; [exact Hwf|]; right; left; split; reflexivity.
      * destruct (Hcomplete a Ha) as [b [Hread Hab]]; exists b; split; [exact Hread|].
        apply UnionFind.union_equiv; [exact Hwf|]; now left.
    + intros a b Hab; apply UnionFind.union_equiv in Hab; [|exact Hwf].
      destruct Hab as [Hab|[[Hax Hrb]|[Har Hxb]]].
      * destruct (Hsound a b Hab) as [Heq|[Ha [Hb Hj]]]; [now left|].
        right; split; [now right|]; split; [now right|exact Hj].
      * destruct (Hsound a x Hax) as [Heq|[Ha [Hx Hj]]];
          destruct (Hsound r b Hrb) as [Heq'|[Hr' [Hb Hj']]]; subst;
          right; cbn; intuition congruence.
      * destruct (Hsound a r Har) as [Heq|[Ha [Hr' Hj]]];
          destruct (Hsound x b Hxb) as [Heq'|[Hx [Hb Hj']]]; subst;
          right; cbn; intuition congruence.
Qed.

Lemma partition_group_step_new keys index u x :
  partition_group_invariant keys index u -> Map.get F (label x) index = None ->
  partition_group_invariant (x :: keys) (Map.set F (label x) x index) u.
Proof.
  intros [Hwf [Hindex [Hcomplete Hsound]]] Hget.
  split; [exact Hwf|]; split.
  - intros j r Hread; destruct (UnionFind.key_dec F j (label x)) as [Heq|Hne].
    + subst j; rewrite Map.get_set_same in Hread; inversion Hread; subst r; cbn; auto.
    + rewrite Map.get_set_other in Hread by exact Hne.
      destruct (Hindex j r Hread) as [Hr Hj]; split; [now right|exact Hj].
  - split.
    + intros a [Heq|Ha].
      * subst a; exists x; split; [apply Map.get_set_same|reflexivity].
      * destruct (Hcomplete a Ha) as [r [Hread Har]]; exists r; split; [|exact Har].
        rewrite Map.get_set_other; [exact Hread|]; congruence.
    + intros a b Hab; destruct (Hsound a b Hab) as [Heq|[Ha [Hb Hj]]]; [now left|].
      right; split; [now right|]; split; [now right|exact Hj].
Qed.

Lemma partition_group_correct keys :
  partition_group_invariant keys (fst (partition_group keys)) (snd (partition_group keys)).
Proof.
  induction keys as [|x rest IH]; cbn [partition_group].
  - split; [apply UnionFind.wf_make|]; split.
    + intros j r Hget; change (Map.get F j Map.empty = Some r) in Hget.
      rewrite Map.get_empty in Hget; discriminate.
    + split; [intros a Ha; contradiction|].
      intros a b Hab; left; now apply UnionFind.make_equiv in Hab.
  - destruct (partition_group rest) as [index u]; cbn in IH.
    destruct (Map.get F (label x) index) as [r|] eqn:Hget; cbn.
    + now apply partition_group_step_found.
    + now apply partition_group_step_new.
Qed.

Lemma partition_group_equiv keys a b :
  UnionFind.equiv E (snd (partition_group keys)) a b <->
  a = b \/ In a keys /\ In b keys /\ label a = label b.
Proof.
  destruct (partition_group_correct keys) as [Hwf [Hindex [Hcomplete Hsound]]].
  split; [apply Hsound|]; intros [Heq|[Ha [Hb Hlabel]]]; [now subst|].
  destruct (Hcomplete a Ha) as [r [Hread Har]].
  destruct (Hcomplete b Hb) as [s [Hread' Hbs]].
  rewrite <- Hlabel in Hread'; assert (r = s) by congruence; subst s.
  unfold UnionFind.equiv in *; congruence.
Qed.
End Grouping.

Section Forests.
Context {K : Type} (E : encoding K).

Definition partition_forest : Type := {u : UnionFind.t K | UnionFind.wf E u}.

Definition partition_representative (u : UnionFind.t K) (x : K) : K :=
  fst (UnionFind.find E x u).

(** Preparing representatives retains compression before visiting the next support key. *)
Fixpoint partition_prepare (keys : list K) (u : UnionFind.t K) : Map.t K K :=
  match keys with
  | [] => Map.empty
  | x :: rest =>
    let '(r, u') := UnionFind.find E x u in
    Map.set E x r (partition_prepare rest u')
  end.

Lemma partition_prepare_get keys u a : UnionFind.wf E u -> In a keys ->
  Map.get E a (partition_prepare keys u) = Some (partition_representative u a).
Proof.
  revert u; induction keys as [|x rest IH]; intros u Hwf Ha; [contradiction|].
  cbn [partition_prepare].
  pose proof (UnionFind.wf_find E u x Hwf) as Hwf'.
  pose proof (UnionFind.find_rep_stable E u a x Hwf) as Hrep.
  destruct (UnionFind.find E x u) as [r u'] eqn:Hfind; cbn [snd] in Hwf', Hrep.
  destruct (UnionFind.key_dec E a x) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same; unfold partition_representative; now rewrite Hfind.
  - rewrite Map.get_set_other by exact Hne.
    destruct Ha as [Heq|Ha]; [congruence|].
    rewrite IH by assumption; unfold partition_representative; now rewrite Hrep.
Qed.

Lemma partition_prepare_absent keys u a : ~ In a keys ->
  Map.get E a (partition_prepare keys u) = None.
Proof.
  revert u; induction keys as [|x rest IH]; intros u Ha.
  - apply Map.get_empty.
  - cbn [partition_prepare]; destruct (UnionFind.find E x u) as [r u'].
    rewrite Map.get_set_other by (intro Heq; apply Ha; now left).
    apply IH; intro Hin; apply Ha; now right.
Qed.

(** Missing cache entries represent keys outside the prepared support, which are singletons. *)
Definition partition_cached_representative (cache : Map.t K K) (x : K) : K :=
  match Map.get E x cache with
  | Some r => r
  | None => x
  end.

(** The prepared cache agrees everywhere with finding in the original well-formed forest. *)
Lemma partition_prepare_agrees u a : UnionFind.wf E u ->
  partition_cached_representative (partition_prepare (UnionFind.keys E u) u) a =
  partition_representative u a.
Proof.
  intro Hwf; unfold partition_cached_representative.
  destruct (in_dec (UnionFind.key_dec E) a (UnionFind.keys E u)) as [Ha|Ha].
  - now rewrite partition_prepare_get by assumption.
  - rewrite partition_prepare_absent by exact Ha.
    symmetry; apply (UnionFind.keys_support E u a (partition_representative u a) Hwf Ha).
    unfold UnionFind.equiv, partition_representative.
    symmetry; now apply UnionFind.find_rep_canonical.
Qed.

Definition partition_intersection (u v : partition_forest) : partition_forest :=
  let keys_u := UnionFind.keys E (proj1_sig u) in
  let keys_v := UnionFind.keys E (proj1_sig v) in
  let cache_u := partition_prepare keys_u (proj1_sig u) in
  let cache_v := partition_prepare keys_v (proj1_sig v) in
  let keys := keys_u ++ keys_v in
  let label := fun x =>
    (partition_cached_representative cache_u x, partition_cached_representative cache_v x) in
  exist _ (snd (partition_group E (pair_encoding E E) label keys))
    (proj1 (partition_group_correct E (pair_encoding E E) label keys)).

Lemma partition_support_pair u a b : UnionFind.wf E u ->
  UnionFind.equiv E u a b -> a <> b ->
  In a (UnionFind.keys E u) /\ In b (UnionFind.keys E u).
Proof.
  intros Hwf Hab Hne; split.
  - destruct (in_dec (UnionFind.key_dec E) a (UnionFind.keys E u)) as [Ha|Ha]; [exact Ha|].
    exfalso; apply Hne; symmetry; exact (UnionFind.keys_support E u a b Hwf Ha Hab).
  - destruct (in_dec (UnionFind.key_dec E) b (UnionFind.keys E u)) as [Hb|Hb]; [exact Hb|].
    exfalso; apply Hne; apply (UnionFind.keys_support E u b a Hwf Hb).
    unfold UnionFind.equiv in *; symmetry; exact Hab.
Qed.

Lemma partition_intersection_equiv u v a b :
  UnionFind.equiv E (proj1_sig (partition_intersection u v)) a b <->
  UnionFind.equiv E (proj1_sig u) a b /\ UnionFind.equiv E (proj1_sig v) a b.
Proof.
  unfold partition_intersection; cbn [proj1_sig]; rewrite partition_group_equiv.
  rewrite !partition_prepare_agrees by apply proj2_sig.
  split.
  - intros [Heq|[_ [_ Hlabel]]]; [subst b; split; reflexivity|].
    unfold partition_representative in Hlabel; unfold UnionFind.equiv; now injection Hlabel.
  - intros [Hu Hv]; destruct (UnionFind.key_dec E a b) as [Heq|Hne]; [now left|].
    destruct (partition_support_pair _ a b (proj2_sig u) Hu Hne) as [Ha Hb].
    right; split; [apply in_or_app; now left|]; split; [apply in_or_app; now left|].
    unfold partition_representative; unfold UnionFind.equiv in Hu, Hv; now rewrite Hu, Hv.
Qed.

(* Both forests are threaded through the scan so path compression is retained between keys. *)
Fixpoint partition_scan (keys : list K) (u v : UnionFind.t K) : bool :=
  match keys with
  | [] => true
  | x :: rest =>
    let '(r, v') := UnionFind.find E x v in
    let '(ok, u') := UnionFind.equivb E x r u in
    if ok then partition_scan rest u' v' else false
  end.

Lemma partition_scan_correct keys u v : UnionFind.wf E u -> UnionFind.wf E v ->
  (partition_scan keys u v = true <-> forall x, In x keys ->
    UnionFind.equiv E u x (partition_representative v x)).
Proof.
  revert u v; induction keys as [|x rest IH]; intros u v Hu Hv.
  - cbn; split; [intros _ a Ha; contradiction|reflexivity].
  - cbn [partition_scan].
    pose proof (UnionFind.wf_find E v x Hv) as Hv'.
    pose proof (UnionFind.find_rep_stable E v) as Hstable.
    pose proof (UnionFind.equivb_correct E u x (fst (UnionFind.find E x v)) Hu)
      as [Htest [Hu' Hagrees]].
    destruct (UnionFind.find E x v) as [r v'] eqn:Hfind;
      cbn [fst snd] in Hv', Htest, Hu', Hagrees.
    destruct (UnionFind.equivb E x r u) as [ok u'] eqn:Htest';
      cbn [fst snd] in Htest, Hu', Hagrees.
    assert (Htail : partition_scan rest u' v' = true <->
      forall a, In a rest -> UnionFind.equiv E u a (partition_representative v a)).
    { rewrite (IH u' v' Hu' Hv'); split; intros Hall a Ha.
      - apply (proj1 (Hagrees _ _)); specialize (Hall a Ha).
        unfold partition_representative in *.
        pose proof (Hstable a x Hv) as Hrep; rewrite Hfind in Hrep; cbn [snd] in Hrep.
        now rewrite <- Hrep.
      - apply (proj2 (Hagrees _ _)); specialize (Hall a Ha).
        unfold partition_representative in *.
        pose proof (Hstable a x Hv) as Hrep; rewrite Hfind in Hrep; cbn [snd] in Hrep.
        now rewrite Hrep. }
    assert (Hhead : ok = true <->
      UnionFind.equiv E u x (partition_representative v x)).
    { unfold partition_representative; rewrite Hfind; exact Htest. }
    destruct ok.
    + rewrite Htail; split.
      * intros Hall a [Heq|Ha]; [subst a; apply Hhead; reflexivity|now apply Hall].
      * intros Hall a Ha; apply Hall; now right.
    + split; [discriminate|]; intro Hall.
      assert (Hfalse : false = true) by (apply Hhead; apply Hall; now left).
      discriminate.
Qed.

Definition partition_forest_leb (u v : partition_forest) : bool :=
  partition_scan (UnionFind.keys E (proj1_sig v)) (proj1_sig u) (proj1_sig v).

Lemma partition_forest_leb_spec u v : partition_forest_leb u v = true <->
  forall a b, UnionFind.equiv E (proj1_sig v) a b -> UnionFind.equiv E (proj1_sig u) a b.
Proof.
  unfold partition_forest_leb; rewrite partition_scan_correct by apply proj2_sig.
  split.
  - intros Hall a b Hab; destruct (UnionFind.key_dec E a b) as [Heq|Hne]; [now subst|].
    destruct (partition_support_pair _ a b (proj2_sig v) Hab Hne) as [Ha Hb].
    specialize (Hall a Ha) as Har; specialize (Hall b Hb) as Hbr.
    unfold UnionFind.equiv in *; unfold partition_representative in *.
    rewrite <- Hab in Hbr; congruence.
  - intros Hall a Ha; apply Hall; unfold UnionFind.equiv, partition_representative.
    symmetry; apply UnionFind.find_rep_canonical; apply proj2_sig.
Qed.
End Forests.

(** Reverse inclusion of reached equivalences is decided by a compressed support scan. *)
Definition partition_leb {K} (E : encoding K) (p q : partition E) : bool :=
  match p, q with
  | Unreached, _ => true
  | Reached u, Reached v => partition_forest_leb E u v
  | Reached _, Unreached => false
  end.

(** Joining reached facts groups their support keys by pairs of old representatives. *)
Definition partition_join {K} (E : encoding K) (p q : partition E) : partition E :=
  match p, q with
  | Unreached, _ => q
  | _, Unreached => p
  | Reached u, Reached v => Reached (partition_intersection E u v)
  end.

(** Partitions use intersection for joining and widening, with identity narrowing. *)
Definition partition_lattice {K} (E : encoding K) : lattice (partition E) :=
  {| leb := partition_leb E;
     bot := Unreached;
     join := partition_join E;
     widen := partition_join E;
     narrow := fun a _ => a |}.

(** The join keeps exactly the equalities shared by its inputs. *)
Theorem partition_join_spec {K} (E : encoding K) (a b : K) (p1 p2 : partition E) :
  partition_equiv E (join (partition_lattice E) p1 p2) a b <->
  partition_equiv E p1 a b /\ partition_equiv E p2 a b.
Proof.
  destruct p1 as [u|], p2 as [v|]; cbn [partition_lattice partition_join partition_equiv join].
  - apply partition_intersection_equiv.
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma partition_leb_sound {K} (E : encoding K) p q :
  partition_leb E p q = true ->
  forall a b, partition_equiv E q a b -> partition_equiv E p a b.
Proof.
  destruct p as [u|], q as [v|]; cbn [partition_leb partition_equiv];
    try discriminate; try tauto.
  apply partition_forest_leb_spec.
Qed.

Lemma partition_leb_refl {K} (E : encoding K) p : partition_leb E p p = true.
Proof.
  destruct p as [u|]; [apply partition_forest_leb_spec; tauto|reflexivity].
Qed.

Lemma partition_leb_trans {K} (E : encoding K) p q r :
  partition_leb E p q = true -> partition_leb E q r = true -> partition_leb E p r = true.
Proof.
  destruct p as [u|], q as [v|], r as [w|]; cbn [partition_leb];
    intros Huv Hvw; try discriminate; try reflexivity.
  pose proof (proj1 (partition_forest_leb_spec E u v) Huv) as Huv'.
  pose proof (proj1 (partition_forest_leb_spec E v w) Hvw) as Hvw'.
  apply partition_forest_leb_spec; intros a b Hab; apply Huv'; now apply Hvw'.
Qed.

Lemma partition_join_upper {K} (E : encoding K) p q :
  partition_leb E p (partition_join E p q) = true /\
  partition_leb E q (partition_join E p q) = true.
Proof.
  destruct p as [u|], q as [v|]; cbn [partition_join partition_leb].
  - split; apply partition_forest_leb_spec; intros a b Hab;
      apply partition_intersection_equiv in Hab; tauto.
  - split; [apply partition_forest_leb_spec; tauto|reflexivity].
  - split; [reflexivity|apply partition_forest_leb_spec; tauto].
  - split; reflexivity.
Qed.

(** Reverse equivalence inclusion supplies all weak lattice laws. *)
Theorem partition_laws {K} (E : encoding K) : lattice_laws (partition_lattice E).
Proof.
  constructor.
  - apply partition_leb_refl.
  - apply partition_leb_trans.
  - intros a; reflexivity.
  - intros a b; apply (proj1 (partition_join_upper E a b)).
  - intros a b; apply (proj2 (partition_join_upper E a b)).
  - intros a b; apply (proj1 (partition_join_upper E a b)).
  - intros a b; apply (proj2 (partition_join_upper E a b)).
  - intros a b _; apply partition_leb_refl.
  - intros a b Hba; exact Hba.
Qed.

(** Intersecting equivalences is the least upper bound for reverse inclusion. *)
Theorem partition_lub {K} (E : encoding K) : lub_laws (partition_lattice E).
Proof.
  constructor; intros [u|] [v|] [w|]; cbn [partition_lattice leb join partition_join
    partition_leb]; intros Huw Hvw; try discriminate; try assumption; try reflexivity.
  pose proof (proj1 (partition_forest_leb_spec E u w) Huw) as Huw'.
  pose proof (proj1 (partition_forest_leb_spec E v w) Hvw) as Hvw'.
  apply partition_forest_leb_spec; intros a b Hab; apply partition_intersection_equiv.
  split; [apply Huw'|apply Hvw']; exact Hab.
Qed.

(** The empty forest imposes only reflexive equalities and is the greatest partition. *)
Definition partition_top {K} (E : encoding K) : top (partition_lattice E).
Proof.
  refine {| top_value := Reached (exist _ UnionFind.make (UnionFind.wf_make E)) |}.
  intros [u|]; [|reflexivity].
  apply partition_forest_leb_spec; intros a b Hab.
  apply UnionFind.make_equiv in Hab; now subst b.
Defined.

(** Adding one equality merges the two classes while keeping bottom unreachable. *)
Definition partition_union {K} (E : encoding K) (x y : K) (p : partition E) : partition E :=
  match p with
  | Unreached => Unreached
  | Reached u => Reached (exist _ (UnionFind.union E x y (proj1_sig u))
      (UnionFind.wf_union E (proj1_sig u) x y (proj2_sig u)))
  end.

(** Union adds exactly the equalities induced by merging its two argument classes. *)
Theorem partition_union_spec {K} (E : encoding K) (x y a b : K) p :
  partition_equiv E (partition_union E x y p) a b <->
  partition_equiv E p a b \/
  (partition_equiv E p a x /\ partition_equiv E p y b) \/
  (partition_equiv E p a y /\ partition_equiv E p x b).
Proof.
  destruct p as [[u Hu]|]; cbn [partition_union partition_equiv proj1_sig].
  - apply UnionFind.union_equiv; exact Hu.
  - tauto.
Qed.

Definition partition_forget_forest {K} (E : encoding K) x
  (u : partition_forest E) : partition_forest E :=
  let support := UnionFind.keys E (proj1_sig u) in
  let cache := partition_prepare E support (proj1_sig u) in
  let keys := filter (fun k => negb (UnionFind.key_eqb E k x)) support in
  let label := partition_cached_representative E cache in
  exist _ (snd (partition_group E E label keys))
    (proj1 (partition_group_correct E E label keys)).

(** Forgetting rebuilds the old classes over support keys other than the forgotten key. *)
Definition partition_forget {K} (E : encoding K) (x : K) (p : partition E) : partition E :=
  match p with
  | Unreached => Unreached
  | Reached u => Reached (partition_forget_forest E x u)
  end.

(** Updating a key compares its injective code with the rebound key's code. *)
Definition key_update {K V} (E : encoding K) (x : K) (v : V) (s : K -> V) : K -> V :=
  fun k => if Pos.eqb (encode E k) (encode E x) then v else s k.

Lemma partition_forget_keys {K} (E : encoding K) x u a :
  In a (filter (fun k => negb (UnionFind.key_eqb E k x)) (UnionFind.keys E u)) <->
  In a (UnionFind.keys E u) /\ a <> x.
Proof.
  rewrite filter_In, Bool.negb_true_iff, UnionFind.key_eqb_false; reflexivity.
Qed.

(** Unreachable facts remain unreachable after forgetting. *)
Theorem partition_forget_unreached {K} (E : encoding K) x :
  partition_forget E x Unreached = Unreached.
Proof.
  reflexivity.
Qed.

(** Forgetting isolates its key and preserves every equality between other keys. *)
Theorem partition_forget_spec {K} (E : encoding K) (x a b : K) p : p <> Unreached ->
  (partition_equiv E (partition_forget E x p) a b <->
   (partition_equiv E p a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
Proof.
  destruct p as [[u Hu]|]; [intro Hreached|contradiction].
  cbn [partition_forget partition_equiv partition_forget_forest proj1_sig].
  rewrite partition_group_equiv, !partition_forget_keys.
  rewrite !partition_prepare_agrees by exact Hu.
  change (a = b \/ (In a (UnionFind.keys E u) /\ a <> x) /\
    (In b (UnionFind.keys E u) /\ b <> x) /\ UnionFind.equiv E u a b <->
    (UnionFind.equiv E u a b /\ a <> x /\ b <> x) \/ (a = x /\ b = x)).
  split.
  - intros [Heq|[[Ha Hax] [[Hb Hbx] Hab]]]; [|now left].
    subst b; destruct (UnionFind.key_dec E a x) as [Heq|Hne].
    + now right.
    + left; repeat split; try assumption; reflexivity.
  - intros [[Hab [Hax Hbx]]|[Hax Hbx]]; [|left; congruence].
    destruct (UnionFind.key_dec E a b) as [Heq|Hne]; [now left|].
    destruct (partition_support_pair E u a b Hu Hab Hne) as [Ha Hb].
    right; tauto.
Qed.

(** Forgetting only loses equalities, hence moves upward in the partition order. *)
Theorem partition_forget_leb {K} (E : encoding K) x p :
  leb (partition_lattice E) p (partition_forget E x p) = true.
Proof.
  destruct p as [u|]; [|reflexivity].
  apply partition_forest_leb_spec; intros a b Hab.
  change (partition_equiv E (partition_forget E x (Reached u)) a b) in Hab.
  apply partition_forget_spec in Hab; [|discriminate].
  destruct Hab as [[Hab _]|[Hax Hbx]]; [exact Hab|subst; reflexivity].
Qed.

(** The boolean test also returns the compressed, invariant-carrying partition. *)
Definition partition_test {K} (E : encoding K) (x y : K) (p : partition E) :
  bool * partition E :=
  match p with
  | Unreached => (true, Unreached)
  | Reached u =>
    let result := UnionFind.equivb E x y (proj1_sig u) in
    (fst result, Reached (exist _ (snd result)
      (proj1 (proj2 (UnionFind.equivb_correct E (proj1_sig u) x y (proj2_sig u))))))
  end.

(** Testing agrees with the old relation and preserves every equality in the returned fact. *)
Theorem partition_test_correct {K} (E : encoding K) x y p :
  (fst (partition_test E x y p) = true <-> partition_equiv E p x y) /\
  (forall a b, partition_equiv E (snd (partition_test E x y p)) a b <->
    partition_equiv E p a b).
Proof.
  destruct p as [[u Hu]|]; cbn [partition_test partition_equiv fst snd proj1_sig].
  - destruct (UnionFind.equivb_correct E u x y Hu) as [Htest [_ Hagrees]].
    split; assumption.
  - tauto.
Qed.

(** Reached states assign equal values to every pair of equivalent keys; bottom denotes nothing. *)
Definition partition_gamma {K V} (E : encoding K) : concretisation (partition E) (K -> V) :=
  {| gamma := fun p s =>
       match p with
       | Unreached => False
       | Reached u => forall a b, UnionFind.equiv E (proj1_sig u) a b -> s a = s b
       end |}.

(** Removing equalities preserves the meaning of a partition. *)
Theorem partition_gamma_laws {K V} (E : encoding K) :
  concretisation_laws (partition_lattice E) (@partition_gamma K V E).
Proof.
  constructor; intros [u|] [w|] s Hle Hgamma; try contradiction; try discriminate.
  intros a b Hab; apply Hgamma; exact (partition_leb_sound E _ _ Hle a b Hab).
Qed.

(** No valuation belongs to the unreachable partition. *)
Theorem partition_gamma_bot_empty {K V} (E : encoding K) :
  bottom_empty (partition_lattice E) (@partition_gamma K V E).
Proof.
  constructor; intros s Hgamma; exact Hgamma.
Qed.

(** Every valuation satisfies the discrete top partition. *)
Theorem partition_top_full {K V} (E : encoding K) :
  top_full (partition_top E) (@partition_gamma K V E).
Proof.
  constructor; intros s a b Hab; apply UnionFind.make_equiv in Hab; now subst b.
Qed.

(** A value update satisfies the partition after all old equalities of that key are forgotten. *)
Theorem partition_forget_gamma {K V} (E : encoding K) x p (s : K -> V) v :
  gamma (@partition_gamma K V E) p s ->
  gamma (@partition_gamma K V E) (partition_forget E x p) (key_update E x v s).
Proof.
  destruct p as [u|]; [intro Hgamma|contradiction].
  intros a b Hab.
  change (partition_equiv E (partition_forget E x (Reached u)) a b) in Hab.
  apply partition_forget_spec in Hab; [|discriminate].
  destruct Hab as [[Hab [Hax Hbx]]|[Hax Hbx]].
  - unfold key_update.
    assert (Ha : Pos.eqb (encode E a) (encode E x) = false).
    { apply Pos.eqb_neq; intro Heq; apply Hax; now apply (encode_injective E). }
    assert (Hb : Pos.eqb (encode E b) (encode E x) = false).
    { apply Pos.eqb_neq; intro Heq; apply Hbx; now apply (encode_injective E). }
    rewrite Ha, Hb; exact (Hgamma a b Hab).
  - subst a b; reflexivity.
Qed.
