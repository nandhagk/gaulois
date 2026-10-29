(** * Canonical byte ranges

    Sorted, nonadjacent half-open integer ranges represent finite sets of bytes.
    For example, the union of [0, 2) and [2, 4) is the single range [0, 4).
    Builds on: Stdlib sorted lists and Order lattice and concretisation dictionaries. *)

From Stdlib Require Import ZArith List Bool Lia Sorting.Sorted.
From Gaulois.Order Require Import OrderLattice OrderConcrete.
Import List.ListNotations.

Local Open Scope Z_scope.

(** A byte range includes its lower endpoint and excludes its upper endpoint. *)
Definition range : Type := (Z * Z)%type.

(** Canonical ranges are nonempty and separated by at least one absent integer byte. *)
Definition ranges_wf (rs : list range) : Prop :=
  Forall (fun r => fst r < snd r) rs /\
  StronglySorted (fun r1 r2 => snd r1 < fst r2) rs.

(** The public carrier contains only canonical lists. *)
Definition byte_ranges : Type := { rs : list range | ranges_wf rs }.

(** Propositional membership is independent of any boolean query implementation. *)
Definition ranges_in (rs : list range) (b : Z) : Prop :=
  exists r, In r rs /\ fst r <= b < snd r.

Lemma ranges_in_nil : forall b, ~ ranges_in [] b.
Proof.
  intros b [r [Hfalse _]]. exact Hfalse.
Qed.

Lemma ranges_in_cons : forall r rs b,
  ranges_in (r :: rs) b <-> fst r <= b < snd r \/ ranges_in rs b.
Proof.
  intros r rs b. unfold ranges_in. cbn. split.
  - intros [s [[Heq|Hin] Hb]]; [subst s; now left|right; now exists s].
  - intros [Hb|[s [Hin Hb]]]; [exists r|exists s]; intuition.
Qed.

Lemma ranges_wf_nil : ranges_wf [].
Proof.
  split; constructor.
Qed.

Lemma ranges_wf_cons : forall r rs,
  ranges_wf (r :: rs) <->
  fst r < snd r /\ ranges_wf rs /\ Forall (fun s => snd r < fst s) rs.
Proof.
  intros r rs. unfold ranges_wf. split.
  - intros [Hpositive Hsorted]. inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsorted as [|? ? Hsort Hafter]; subst. intuition.
  - intros [Hr [[Hpositive Hsorted] Hafter]]. split; constructor; assumption.
Qed.

Lemma ranges_in_lower : forall rs low b,
  Forall (fun r => low <= fst r) rs -> ranges_in rs b -> low <= b.
Proof.
  intros rs low b Hlow [r [Hin Hb]]. rewrite Forall_forall in Hlow.
  specialize (Hlow r Hin). lia.
Qed.

Lemma ranges_wf_order : forall rs,
  ranges_wf rs -> StronglySorted (fun r s => fst r <= fst s) rs.
Proof.
  induction rs as [|r rs IH]; intro Hwf; [constructor|].
  apply ranges_wf_cons in Hwf as [Hr [Hrest Hafter]]. constructor.
  - now apply IH.
  - rewrite Forall_forall in Hafter |- *. intros s Hin.
    specialize (Hafter s Hin). lia.
Qed.

(** Merge two lists ordered by lower endpoint without restarting either traversal. *)
Fixpoint ranges_merge (xs ys : list range) {struct xs} : list range :=
  match xs with
  | [] => ys
  | x :: xt =>
    (fix merge_right (zs : list range) : list range :=
       match zs with
       | [] => x :: xt
       | y :: yt =>
         if fst x <=? fst y then x :: ranges_merge xt zs
         else y :: merge_right yt
       end) ys
  end.

Lemma ranges_merge_in : forall xs ys r,
  In r (ranges_merge xs ys) <-> In r xs \/ In r ys.
Proof.
  induction xs as [|x xt IH]; intros ys r; [cbn; tauto|].
  induction ys as [|y yt IHr]; [cbn; tauto|].
  cbn [ranges_merge]. destruct (fst x <=? fst y).
  - cbn. rewrite IH. cbn. tauto.
  - cbn in IHr |- *. tauto.
Qed.

Lemma ranges_merge_forall : forall (P : range -> Prop) xs ys,
  Forall P xs -> Forall P ys -> Forall P (ranges_merge xs ys).
Proof.
  intros P xs ys Hx Hy. rewrite Forall_forall in Hx, Hy |- *.
  intros r Hin. apply ranges_merge_in in Hin. destruct Hin; auto.
Qed.

Lemma ranges_merge_order : forall xs ys,
  StronglySorted (fun r s => fst r <= fst s) xs ->
  StronglySorted (fun r s => fst r <= fst s) ys ->
  StronglySorted (fun r s => fst r <= fst s) (ranges_merge xs ys).
Proof.
  induction xs as [|x xt IH]; intros ys Hx Hy; [exact Hy|].
  inversion Hx as [|? ? Hxt Hxa]; subst.
  induction ys as [|y yt IHr]; [exact Hx|].
  inversion Hy as [|? ? Hyt Hya]; subst. cbn [ranges_merge].
  destruct (fst x <=? fst y) eqn:Hxy.
  - apply Z.leb_le in Hxy. constructor.
    + apply IH; assumption.
    + apply ranges_merge_forall; [exact Hxa|constructor; [exact Hxy|]].
      rewrite Forall_forall in Hya |- *. intros r Hr. specialize (Hya r Hr). lia.
  - apply Z.leb_gt in Hxy. constructor.
    + apply IHr. exact Hyt.
    + change (Forall (fun s => fst y <= fst s) (ranges_merge (x :: xt) yt)).
      apply ranges_merge_forall; [|exact Hya]. constructor; [lia|].
      rewrite Forall_forall in Hxa |- *. intros r Hr. specialize (Hxa r Hr). lia.
Qed.

(** Coalescing carries one pending range and consumes each remaining range once. *)
Fixpoint ranges_coalesce_from (r : range) (rs : list range) : list range :=
  match rs with
  | [] => [r]
  | s :: rest =>
    if snd r <? fst s then r :: ranges_coalesce_from s rest
    else ranges_coalesce_from (fst r, Z.max (snd r) (snd s)) rest
  end.

Definition ranges_coalesce (rs : list range) : list range :=
  match rs with
  | [] => []
  | r :: rest => ranges_coalesce_from r rest
  end.

Lemma ranges_coalesce_lower : forall rs r low,
  low <= fst r -> Forall (fun s => low <= fst s) rs ->
  Forall (fun s => low <= fst s) (ranges_coalesce_from r rs).
Proof.
  induction rs as [|s rest IH]; intros r low Hr Hrs; cbn.
  - constructor; [exact Hr|constructor].
  - inversion Hrs as [|? ? Hs Hrest]; subst.
    destruct (snd r <? fst s).
    + constructor; [exact Hr|apply IH; assumption].
    + apply IH; assumption.
Qed.

Lemma ranges_coalesce_wf : forall rs r,
  fst r < snd r -> Forall (fun s => fst s < snd s) rs ->
  StronglySorted (fun s t => fst s <= fst t) rs ->
  Forall (fun s => fst r <= fst s) rs -> ranges_wf (ranges_coalesce_from r rs).
Proof.
  induction rs as [|s rest IH]; intros r Hr Hpositive Hsort Hlower; cbn.
  - apply ranges_wf_cons. repeat split; try constructor; exact Hr.
  - inversion Hpositive as [|? ? Hs Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    inversion Hlower as [|? ? Hrs Hlowerrest]; subst.
    destruct (snd r <? fst s) eqn:Hgap.
    + apply Z.ltb_lt in Hgap. apply ranges_wf_cons. split; [exact Hr|]. split.
      * apply IH; assumption.
      * eapply Forall_impl; [|apply (ranges_coalesce_lower rest s (fst s));
          [lia|exact Hafter]]. cbn. intros q Hq. lia.
    + apply IH; try assumption; cbn; lia.
Qed.

Lemma ranges_coalesce_in : forall rs r b,
  fst r < snd r -> Forall (fun s => fst s < snd s) rs ->
  StronglySorted (fun s t => fst s <= fst t) rs ->
  Forall (fun s => fst r <= fst s) rs ->
  (ranges_in (ranges_coalesce_from r rs) b <->
    fst r <= b < snd r \/ ranges_in rs b).
Proof.
  induction rs as [|s rest IH]; intros r b Hr Hpositive Hsort Hlower; cbn.
  - rewrite ranges_in_cons. split; intros H; destruct H as [H|H];
      try (now left); try (exfalso; apply (ranges_in_nil b); exact H).
  - inversion Hpositive as [|? ? Hs Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    inversion Hlower as [|? ? Hrs Hlowerrest]; subst.
    destruct (snd r <? fst s) eqn:Hgap.
    + rewrite ranges_in_cons, (IH s b Hs Hrest Hsortrest Hafter), ranges_in_cons. tauto.
    + apply Z.ltb_ge in Hgap.
      rewrite (IH (fst r, Z.max (snd r) (snd s)) b), ranges_in_cons;
        try assumption; cbn; try lia.
      destruct (Z.max_spec (snd r) (snd s)) as [[Hle Hmax]|[Hle Hmax]];
        rewrite Hmax; intuition lia.
Qed.

(** The empty canonical set contains no ranges. *)
Definition ranges_empty : byte_ranges := exist _ [] ranges_wf_nil.

(** Membership tests ranges without enumerating their individual bytes. *)
Definition ranges_mem (rs : byte_ranges) (b : Z) : bool :=
  existsb (fun r => (fst r <=? b) && (b <? snd r)) (proj1_sig rs).

Lemma ranges_mem_spec : forall rs b,
  ranges_mem rs b = true <-> ranges_in (proj1_sig rs) b.
Proof.
  intros rs b. unfold ranges_mem, ranges_in. rewrite existsb_exists. split.
  - intros [r [Hin Hb]]. exists r. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in Hb.
    tauto.
  - intros [r [Hin Hb]]. exists r. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

(** Union merges the two sorted streams and coalesces adjacent or overlapping ranges. *)
Definition ranges_union (rs1 rs2 : byte_ranges) : byte_ranges.
Proof.
  refine (exist _ (ranges_coalesce (ranges_merge (proj1_sig rs1) (proj1_sig rs2))) _).
  destruct rs1 as [xs Hx], rs2 as [ys Hy]; cbn.
  assert (Hpositive : Forall (fun r => fst r < snd r) (ranges_merge xs ys)).
  { apply ranges_merge_forall; [exact (proj1 Hx)|exact (proj1 Hy)]. }
  assert (Hsort : StronglySorted (fun r s => fst r <= fst s) (ranges_merge xs ys)).
  { apply ranges_merge_order; apply ranges_wf_order; assumption. }
  destruct (ranges_merge xs ys) as [|r rest]; [exact ranges_wf_nil|].
  inversion Hpositive as [|? ? Hr Hrest]; subst.
  inversion Hsort as [|? ? Hsortrest Hafter]; subst.
  exact (ranges_coalesce_wf rest r Hr Hrest Hsortrest Hafter).
Defined.

(** Membership in a union is the disjunction of the original memberships. *)
Theorem ranges_mem_union : forall rs1 rs2 b,
  ranges_mem (ranges_union rs1 rs2) b = (ranges_mem rs1 b || ranges_mem rs2 b)%bool.
Proof.
  intros [xs Hx] [ys Hy] b. apply Bool.eq_true_iff_eq.
  rewrite orb_true_iff, !ranges_mem_spec. cbn [ranges_union proj1_sig].
  assert (Hpositive : Forall (fun r => fst r < snd r) (ranges_merge xs ys)).
  { apply ranges_merge_forall; [exact (proj1 Hx)|exact (proj1 Hy)]. }
  assert (Hsort : StronglySorted (fun r s => fst r <= fst s) (ranges_merge xs ys)).
  { apply ranges_merge_order; apply ranges_wf_order; assumption. }
  assert (Hbytes : ranges_in (ranges_coalesce (ranges_merge xs ys)) b <->
    ranges_in (ranges_merge xs ys) b).
  { destruct (ranges_merge xs ys) as [|r rest]; [reflexivity|].
    inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsort as [|? ? Hsortrest Hafter]; subst.
    cbn [ranges_coalesce]. rewrite ranges_coalesce_in, ranges_in_cons;
      try reflexivity; assumption. }
  rewrite Hbytes. unfold ranges_in. setoid_rewrite ranges_merge_in. firstorder.
Qed.

(** Cut one pending range against the right stream, retaining the tail continuation. *)
Fixpoint ranges_cut (lo hi : Z) (tail : list range)
  (finish : list range -> list range) (ys : list range) : list range :=
  match ys with
  | [] => (lo, hi) :: tail
  | (m, n) :: rest =>
    if n <=? lo then ranges_cut lo hi tail finish rest
    else if hi <=? m then (lo, hi) :: finish ys
    else if m <=? lo then
      if hi <=? n then finish ys else ranges_cut n hi tail finish rest
    else (lo, m) ::
      if hi <=? n then finish ys else ranges_cut n hi tail finish rest
  end.

(** Difference consumes one original left range or one original right range at each step. *)
Fixpoint ranges_subtract (xs ys : list range) {struct xs} : list range :=
  match xs with
  | [] => []
  | (lo, hi) :: tail => ranges_cut lo hi tail (ranges_subtract tail) ys
  end.

Lemma ranges_cut_lower : forall ys lo hi tail finish low,
  low <= lo -> Forall (fun r => low <= fst r) tail ->
  (forall zs, Forall (fun r => low <= fst r) (finish zs)) ->
  Forall (fun r => low <= fst r) (ranges_cut lo hi tail finish ys).
Proof.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish low Hlo Htail Hfinish; cbn.
  - constructor; assumption.
  - destruct (n <=? lo) eqn:Hnlo; [apply IH; assumption|].
    apply Z.leb_gt in Hnlo.
    destruct (hi <=? m); [constructor; [exact Hlo|apply Hfinish]|].
    destruct (m <=? lo), (hi <=? n); try apply Hfinish;
      try (apply IH; try assumption; lia);
      constructor; try exact Hlo; try apply Hfinish;
      apply IH; try assumption; lia.
Qed.

Lemma ranges_subtract_lower : forall xs ys low,
  Forall (fun r => low <= fst r) xs ->
  Forall (fun r => low <= fst r) (ranges_subtract xs ys).
Proof.
  induction xs as [|[lo hi] tail IH]; intros ys low Hlower; [constructor|].
  inversion Hlower as [|? ? Hlo Htail]; subst. cbn [ranges_subtract].
  apply ranges_cut_lower; try assumption. intros zs. now apply IH.
Qed.

Lemma ranges_cut_wf : forall ys lo hi tail finish,
  ranges_wf ys -> lo < hi -> ranges_wf tail ->
  Forall (fun r => hi < fst r) tail ->
  (forall zs, ranges_wf zs -> ranges_wf (finish zs)) ->
  (forall zs, Forall (fun r => hi < fst r) (finish zs)) ->
  ranges_wf (ranges_cut lo hi tail finish ys).
Proof.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish Hys Hlo Htail Hafter Hfinish Hlow.
  - cbn. apply ranges_wf_cons. intuition.
  - pose proof Hys as Hysall. apply ranges_wf_cons in Hys as [Hmn [Hrest Hysafter]].
    cbn in Hmn. cbn [ranges_cut].
    destruct (n <=? lo) eqn:Hnlo; [apply IH; assumption|].
    apply Z.leb_gt in Hnlo.
    destruct (hi <=? m) eqn:Hhim.
    + apply ranges_wf_cons. split; [exact Hlo|].
      split; [apply Hfinish; exact Hysall|apply Hlow].
    + apply Z.leb_gt in Hhim. destruct (m <=? lo) eqn:Hmlo.
      * destruct (hi <=? n) eqn:Hhin; [apply Hfinish; exact Hysall|].
        apply Z.leb_gt in Hhin. apply IH; assumption.
      * apply Z.leb_gt in Hmlo. apply ranges_wf_cons. split; [cbn; lia|].
        destruct (hi <=? n) eqn:Hhin.
        -- split; [apply Hfinish; exact Hysall|].
           eapply Forall_impl; [|apply Hlow]. cbn. intros r Hr. lia.
        -- apply Z.leb_gt in Hhin. split; [apply IH; assumption|].
           assert (Hbound : Forall (fun r => n <= fst r)
             (ranges_cut n hi tail finish rest)).
           { apply ranges_cut_lower; [lia| |].
             - eapply Forall_impl; [|exact Hafter]. cbn. intros r Hr. lia.
             - intros zs. eapply Forall_impl; [|apply Hlow]. cbn. intros r Hr. lia. }
           eapply Forall_impl; [|exact Hbound]. cbn. intros r Hr. lia.
Qed.

Lemma ranges_subtract_wf : forall xs ys,
  ranges_wf xs -> ranges_wf ys -> ranges_wf (ranges_subtract xs ys).
Proof.
  induction xs as [|[lo hi] tail IH]; intros ys Hxs Hys; [exact ranges_wf_nil|].
  apply ranges_wf_cons in Hxs as [Hlo [Htail Hafter]]. cbn in Hlo, Hafter.
  cbn [ranges_subtract]. apply ranges_cut_wf; try assumption.
  - intros zs Hzs. apply IH; assumption.
  - intros zs. assert (Hlower : Forall (fun r => hi + 1 <= fst r) tail).
    { eapply Forall_impl; [|exact Hafter]. cbn. intros r Hr. lia. }
    pose proof (ranges_subtract_lower tail zs (hi + 1) Hlower) as Hresult.
    eapply Forall_impl; [|exact Hresult]. cbn. intros r Hr. lia.
Qed.

Lemma ranges_in_after : forall rs low b,
  Forall (fun r => low < fst r) rs -> ranges_in rs b -> low < b.
Proof.
  intros rs low b Hlow [r [Hin Hb]]. rewrite Forall_forall in Hlow.
  specialize (Hlow r Hin). lia.
Qed.

Lemma ranges_cut_in : forall ys lo hi tail finish b,
  ranges_wf ys -> lo < hi -> Forall (fun r => hi < fst r) tail ->
  (forall zs, ranges_wf zs ->
    (ranges_in (finish zs) b <-> ranges_in tail b /\ ~ ranges_in zs b)) ->
  (ranges_in (ranges_cut lo hi tail finish ys) b <->
    (lo <= b < hi \/ ranges_in tail b) /\ ~ ranges_in ys b).
Proof.
  induction ys as [|[m n] rest IH]; intros lo hi tail finish b Hys Hlo Hafter Hfinish.
  - cbn [ranges_cut]. rewrite ranges_in_cons. cbn [fst snd].
    pose proof (ranges_in_nil b). tauto.
  - pose proof Hys as Hysall. apply ranges_wf_cons in Hys as [Hmn [Hrest Hlater]].
    cbn in Hmn, Hlater.
    assert (Htailbyte : ranges_in tail b -> hi < b).
    { apply ranges_in_after. exact Hafter. }
    assert (Hrestbyte : ranges_in rest b -> n < b).
    { apply ranges_in_after. exact Hlater. }
    cbn [ranges_cut]. destruct (n <=? lo) eqn:Hnlo.
    + apply Z.leb_le in Hnlo.
      rewrite (IH lo hi tail finish b Hrest Hlo Hafter Hfinish), ranges_in_cons.
      cbn [fst snd]. intuition lia.
    + apply Z.leb_gt in Hnlo. destruct (hi <=? m) eqn:Hhim.
      * apply Z.leb_le in Hhim.
        rewrite (ranges_in_cons (lo, hi) (finish ((m, n) :: rest)) b),
          (Hfinish _ Hysall), (ranges_in_cons (m, n) rest b).
        cbn [fst snd]. intuition lia.
      * apply Z.leb_gt in Hhim. destruct (m <=? lo) eqn:Hmlo.
        -- apply Z.leb_le in Hmlo. destruct (hi <=? n) eqn:Hhin.
           ++ apply Z.leb_le in Hhin. rewrite (Hfinish _ Hysall), ranges_in_cons.
              cbn [fst snd]. intuition lia.
           ++ apply Z.leb_gt in Hhin.
              rewrite (IH n hi tail finish b Hrest Hhin Hafter Hfinish), ranges_in_cons.
              cbn [fst snd]. intuition lia.
        -- apply Z.leb_gt in Hmlo. destruct (hi <=? n) eqn:Hhin.
           ++ apply Z.leb_le in Hhin.
              rewrite (ranges_in_cons (lo, m) (finish ((m, n) :: rest)) b),
                (Hfinish _ Hysall), (ranges_in_cons (m, n) rest b).
              cbn [fst snd]. intuition lia.
           ++ apply Z.leb_gt in Hhin.
              rewrite (ranges_in_cons (lo, m) (ranges_cut n hi tail finish rest) b),
                (IH n hi tail finish b Hrest Hhin Hafter Hfinish),
                (ranges_in_cons (m, n) rest b). cbn [fst snd].
              destruct (Z_lt_ge_dec b m); intuition lia.
Qed.

Lemma ranges_subtract_in : forall xs ys b,
  ranges_wf xs -> ranges_wf ys ->
  (ranges_in (ranges_subtract xs ys) b <-> ranges_in xs b /\ ~ ranges_in ys b).
Proof.
  induction xs as [|[lo hi] tail IH]; intros ys b Hxs Hys.
  - cbn [ranges_subtract]. pose proof (ranges_in_nil b). tauto.
  - apply ranges_wf_cons in Hxs as [Hlo [Htail Hafter]].
    cbn in Hlo, Hafter. cbn [ranges_subtract]. rewrite ranges_cut_in, ranges_in_cons;
      try assumption; try reflexivity. intros zs Hzs. now apply IH.
Qed.

(** Difference removes right-hand bytes in a linear traversal of both canonical streams. *)
Definition ranges_diff (rs1 rs2 : byte_ranges) : byte_ranges :=
  exist _ (ranges_subtract (proj1_sig rs1) (proj1_sig rs2))
    (ranges_subtract_wf _ _ (proj2_sig rs1) (proj2_sig rs2)).

(** A byte survives difference exactly when it is present only on the left. *)
Theorem ranges_mem_diff : forall rs1 rs2 b,
  ranges_mem (ranges_diff rs1 rs2) b =
    (ranges_mem rs1 b && negb (ranges_mem rs2 b))%bool.
Proof.
  intros rs1 rs2 b. apply Bool.eq_true_iff_eq.
  rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, !ranges_mem_spec.
  apply ranges_subtract_in; apply proj2_sig.
Qed.

(** Intersection uses two linear differences; every intermediate range is canonical. *)
Definition ranges_inter (rs1 rs2 : byte_ranges) : byte_ranges :=
  ranges_diff rs1 (ranges_diff rs1 rs2).

(** Intersection keeps exactly the bytes present in both inputs. *)
Theorem ranges_mem_inter : forall rs1 rs2 b,
  ranges_mem (ranges_inter rs1 rs2) b = (ranges_mem rs1 b && ranges_mem rs2 b)%bool.
Proof.
  intros rs1 rs2 b. unfold ranges_inter. rewrite !ranges_mem_diff.
  destruct (ranges_mem rs1 b), (ranges_mem rs2 b); reflexivity.
Qed.

(** A nonempty singleton range is canonical, while an empty one denotes no bytes. *)
Definition ranges_single (r : range) : byte_ranges.
Proof.
  refine (if Z_lt_dec (fst r) (snd r) then exist _ [r] _ else ranges_empty).
  apply ranges_wf_cons. split; [assumption|]. split; [exact ranges_wf_nil|constructor].
Defined.

Lemma ranges_mem_single : forall r b,
  ranges_mem (ranges_single r) b = ((fst r <=? b) && (b <? snd r))%bool.
Proof.
  intros r b. unfold ranges_single. destruct (Z_lt_dec (fst r) (snd r)) as [Hr|Hr].
  - cbn [ranges_mem proj1_sig existsb]. apply orb_false_r.
  - cbn [ranges_empty ranges_mem proj1_sig existsb].
    symmetry. apply andb_false_iff. destruct (fst r <=? b) eqn:Hlo.
    + right. apply Z.ltb_ge. apply Z.leb_le in Hlo. lia.
    + left. reflexivity.
Qed.

(** Adding a range is union with its canonical singleton, including an empty range. *)
Definition ranges_add (r : range) (rs : byte_ranges) : byte_ranges :=
  ranges_union (ranges_single r) rs.

(** Removing a range is difference against its canonical singleton. *)
Definition ranges_remove (r : range) (rs : byte_ranges) : byte_ranges :=
  ranges_diff rs (ranges_single r).

(** The empty byte set has false membership at every integer. *)
Theorem ranges_mem_empty : forall b, ranges_mem ranges_empty b = false.
Proof.
  reflexivity.
Qed.

(** Adding a range inserts exactly its half-open bytes. *)
Theorem ranges_mem_add : forall rs r b,
  ranges_mem (ranges_add r rs) b =
    ((fst r <=? b) && (b <? snd r) || ranges_mem rs b)%bool.
Proof.
  intros rs r b. unfold ranges_add. rewrite ranges_mem_union, ranges_mem_single. reflexivity.
Qed.

(** Removing a range discards exactly its half-open bytes. *)
Theorem ranges_mem_remove : forall rs r b,
  ranges_mem (ranges_remove r rs) b =
    (ranges_mem rs b && negb ((fst r <=? b) && (b <? snd r)))%bool.
Proof.
  intros rs r b. unfold ranges_remove. rewrite ranges_mem_diff, ranges_mem_single. reflexivity.
Qed.

Lemma ranges_head_lower : forall r rs b,
  ranges_wf (r :: rs) -> ranges_in (r :: rs) b -> fst r <= b.
Proof.
  intros r rs b Hwf Hb. apply ranges_wf_cons in Hwf as [Hr [_ Hafter]].
  apply ranges_in_cons in Hb. destruct Hb as [Hb|Hb]; [lia|].
  pose proof (ranges_in_after rs (snd r) b Hafter Hb). lia.
Qed.

Lemma ranges_head_end_absent : forall r rs,
  ranges_wf (r :: rs) -> ~ ranges_in (r :: rs) (snd r).
Proof.
  intros r rs Hwf Hb. apply ranges_wf_cons in Hwf as [Hr [_ Hafter]].
  apply ranges_in_cons in Hb. destruct Hb as [Hb|Hb]; [lia|].
  pose proof (ranges_in_after rs (snd r) (snd r) Hafter Hb). lia.
Qed.

Lemma ranges_heads_equal : forall r rs s ss,
  ranges_wf (r :: rs) -> ranges_wf (s :: ss) ->
  (forall b, ranges_in (r :: rs) b <-> ranges_in (s :: ss) b) -> r = s.
Proof.
  intros [lo hi] rs [low high] ss Hr Hs Hequiv.
  pose proof Hr as Hrcons. pose proof Hs as Hscons.
  apply ranges_wf_cons in Hr as [Hpositive _].
  apply ranges_wf_cons in Hs as [Hpositive2 _]. cbn in Hpositive, Hpositive2.
  assert (Hlobyte : ranges_in ((lo, hi) :: rs) lo).
  { apply ranges_in_cons. left. cbn. lia. }
  assert (Hlowbyte : ranges_in ((low, high) :: ss) low).
  { apply ranges_in_cons. left. cbn. lia. }
  apply Hequiv in Hlobyte. apply Hequiv in Hlowbyte.
  pose proof (ranges_head_lower _ _ _ Hscons Hlobyte) as Hlowlo.
  pose proof (ranges_head_lower _ _ _ Hrcons Hlowbyte) as Hlolow. cbn in Hlowlo, Hlolow.
  assert (Heq : lo = low) by lia. subst low.
  assert (Hhi : hi = high).
  { destruct (Z.lt_trichotomy hi high) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
    - exfalso. apply (ranges_head_end_absent _ _ Hrcons). apply Hequiv.
      apply ranges_in_cons. left. cbn. lia.
    - exfalso. apply (ranges_head_end_absent _ _ Hscons). apply Hequiv.
      apply ranges_in_cons. left. cbn. lia. }
  now subst high.
Qed.

Lemma ranges_lists_ext : forall xs ys,
  ranges_wf xs -> ranges_wf ys ->
  (forall b, ranges_in xs b <-> ranges_in ys b) -> xs = ys.
Proof.
  induction xs as [|r rs IH]; intros [|s ss] Hx Hy Hequiv; [reflexivity| | |].
  - apply ranges_wf_cons in Hy as [Hs _]. exfalso. apply (ranges_in_nil (fst s)).
    apply Hequiv, ranges_in_cons. left. lia.
  - apply ranges_wf_cons in Hx as [Hr _]. exfalso. apply (ranges_in_nil (fst r)).
    apply Hequiv, ranges_in_cons. left. lia.
  - assert (Heq : r = s) by (eapply ranges_heads_equal; eassumption). subst s.
    apply ranges_wf_cons in Hx as [Hr [Hrs Hafterr]].
    apply ranges_wf_cons in Hy as [_ [Hss Hafters]]. f_equal. apply IH; try assumption.
    intro b. specialize (Hequiv b). rewrite !ranges_in_cons in Hequiv.
    pose proof (ranges_in_after rs (snd r) b Hafterr) as Hrb.
    pose proof (ranges_in_after ss (snd r) b Hafters) as Hsb.
    intuition lia.
Qed.

(** Canonical lists with identical byte membership have identical range endpoints. *)
Theorem ranges_ext : forall rs1 rs2,
  (forall b, ranges_mem rs1 b = ranges_mem rs2 b) -> proj1_sig rs1 = proj1_sig rs2.
Proof.
  intros rs1 rs2 Hequiv. apply ranges_lists_ext; try apply proj2_sig.
  intro b. rewrite <- !ranges_mem_spec, Hequiv. reflexivity.
Qed.

(** Emptiness uses the canonical representation rather than scanning endpoint values. *)
Definition ranges_is_empty (rs : byte_ranges) : bool :=
  match proj1_sig rs with
  | [] => true
  | _ :: _ => false
  end.

Lemma ranges_is_empty_spec : forall rs,
  ranges_is_empty rs = true <-> forall b, ranges_mem rs b = false.
Proof.
  intros [xs Hwf]. destruct xs as [|r rest].
  - split; [intros _ b; reflexivity|intros _; reflexivity].
  - split; [discriminate|]. intro Hempty. specialize (Hempty (fst r)).
    assert (Hmember : ranges_mem (exist ranges_wf (r :: rest) Hwf) (fst r) = true).
    { apply ranges_mem_spec, ranges_in_cons. left.
      pose proof (proj1 (ranges_wf_cons r rest) Hwf) as [Hr _]. lia. }
    change (ranges_mem (exist ranges_wf (r :: rest) Hwf) (fst r) = false) in Hempty.
    rewrite Hmember in Hempty. discriminate.
Qed.

Lemma ranges_nonempty_spec : forall rs,
  ranges_is_empty rs = false <-> exists b, ranges_mem rs b = true.
Proof.
  intros [xs Hwf]. destruct xs as [|r rest].
  - split; [discriminate|intros [b Hfalse]; discriminate].
  - split; [intros _|intros _; reflexivity]. exists (fst r).
    apply ranges_mem_spec, ranges_in_cons. left.
    pose proof (proj1 (ranges_wf_cons r rest) Hwf) as [Hr _]. lia.
Qed.

(** Inclusion is decided by emptiness of the linear range difference. *)
Definition ranges_subset (rs1 rs2 : byte_ranges) : bool :=
  ranges_is_empty (ranges_diff rs1 rs2).

Lemma ranges_subset_spec : forall rs1 rs2,
  ranges_subset rs1 rs2 = true <->
  forall b, ranges_mem rs1 b = true -> ranges_mem rs2 b = true.
Proof.
  intros rs1 rs2. unfold ranges_subset. rewrite ranges_is_empty_spec.
  split; intros Hsubset b; specialize (Hsubset b); rewrite ranges_mem_diff in *.
  - destruct (ranges_mem rs1 b), (ranges_mem rs2 b); cbn in *; congruence.
  - destruct (ranges_mem rs1 b), (ranges_mem rs2 b); cbn in *; intuition discriminate.
Qed.

(** Coverage includes every empty interval, even when its endpoints are inverted. *)
Definition ranges_covers (rs : byte_ranges) (r : range) : bool :=
  ranges_subset (ranges_single r) rs.

(** Intersection queries detect at least one shared byte of the queried range. *)
Definition ranges_intersects (rs : byte_ranges) (r : range) : bool :=
  negb (ranges_is_empty (ranges_inter (ranges_single r) rs)).

(** Coverage is exactly universal byte membership over the half-open query interval. *)
Theorem ranges_covers_spec : forall rs r,
  ranges_covers rs r = true <-> forall b, fst r <= b < snd r -> ranges_mem rs b = true.
Proof.
  intros rs r. unfold ranges_covers. rewrite ranges_subset_spec.
  setoid_rewrite ranges_mem_single. setoid_rewrite andb_true_iff.
  setoid_rewrite Z.leb_le. setoid_rewrite Z.ltb_lt. reflexivity.
Qed.

(** An intersection query succeeds exactly when a concrete shared byte exists. *)
Theorem ranges_intersects_spec : forall rs r,
  ranges_intersects rs r = true <->
  exists b, fst r <= b < snd r /\ ranges_mem rs b = true.
Proof.
  intros rs r. unfold ranges_intersects. rewrite negb_true_iff, ranges_nonempty_spec.
  setoid_rewrite ranges_mem_inter. setoid_rewrite ranges_mem_single.
  repeat setoid_rewrite andb_true_iff. setoid_rewrite Z.leb_le. setoid_rewrite Z.ltb_lt.
  firstorder.
Qed.

(** The may lattice orders finite byte sets by inclusion and joins by union. *)
Definition ranges_lattice : lattice byte_ranges :=
  {| leb := ranges_subset;
     bot := ranges_empty;
     join := ranges_union;
     widen := ranges_union;
     narrow := fun a _ => a |}.

(** A byte-range set denotes exactly its member bytes. *)
Definition ranges_gamma : concretisation byte_ranges Z :=
  {| gamma := fun rs b => ranges_mem rs b = true |}.

Lemma ranges_union_left : forall a b, ranges_subset a (ranges_union a b) = true.
Proof.
  intros a b. apply ranges_subset_spec. intros k Hk.
  rewrite ranges_mem_union, Hk. reflexivity.
Qed.

Lemma ranges_union_right : forall a b, ranges_subset b (ranges_union a b) = true.
Proof.
  intros a b. apply ranges_subset_spec. intros k Hk.
  rewrite ranges_mem_union, Hk, orb_true_r. reflexivity.
Qed.

(** Canonical finite byte sets satisfy the weak lattice laws. *)
Theorem ranges_laws : lattice_laws ranges_lattice.
Proof.
  constructor; cbn [ranges_lattice leb bot join widen narrow].
  - intro a. apply ranges_subset_spec. auto.
  - intros a b c Hab Hbc.
    pose proof (proj1 (ranges_subset_spec a b) Hab) as Habmem.
    pose proof (proj1 (ranges_subset_spec b c) Hbc) as Hbcmem.
    apply ranges_subset_spec. auto.
  - intro a. apply ranges_subset_spec. intros k Hfalse. discriminate Hfalse.
  - apply ranges_union_left.
  - apply ranges_union_right.
  - apply ranges_union_left.
  - apply ranges_union_right.
  - intros a b _. apply ranges_subset_spec. auto.
  - intros a b Hle. exact Hle.
Qed.

(** Union is the least upper bound for byte inclusion. *)
Theorem ranges_lub : lub_laws ranges_lattice.
Proof.
  constructor. intros a b c Ha Hb.
  change (ranges_subset a c = true) in Ha. change (ranges_subset b c = true) in Hb.
  pose proof (proj1 (ranges_subset_spec a c) Ha) as Hamem.
  pose proof (proj1 (ranges_subset_spec b c) Hb) as Hbmem.
  apply ranges_subset_spec. intros k Hk. rewrite ranges_mem_union, orb_true_iff in Hk.
  destruct Hk; auto.
Qed.

(** The may meaning grows monotonically with byte inclusion. *)
Theorem ranges_gamma_laws : concretisation_laws ranges_lattice ranges_gamma.
Proof.
  constructor. intros a b k Hle Hmem. change (ranges_subset a b = true) in Hle.
  exact (proj1 (ranges_subset_spec a b) Hle k Hmem).
Qed.
