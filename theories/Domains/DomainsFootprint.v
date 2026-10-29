(** * Footprints and must facts

    Footprints group canonical byte ranges by allocation site and describe definitely written bytes.
    For example, adjacent writes at one site normalize to one footprint, and joining writes keeps
    only their shared bytes.
    Builds on: DomainsByteRange, CollectionsMap and OrderLift. *)

From Stdlib Require Import ZArith List Bool Lia.
From Stdlib.Sorting Require Import Sorted Permutation Mergesort.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap.
From Gaulois.Order Require Import OrderLattice OrderConcrete OrderLift.
From Gaulois.Domains Require Import DomainsByteRange.
Import List.ListNotations.

Local Open Scope Z_scope.

(** A footprint covers one site's half-open interval of byte offsets. *)
Record footprint (T : Type) : Type := Footprint {
  fp_site : T;
  fp_lo : Z;
  fp_hi : Z
}.

Arguments Footprint {T}.
Arguments fp_site {T}.
Arguments fp_lo {T}.
Arguments fp_hi {T}.

(** Coverage allows each access byte to have its own footprint witness. *)
Definition covered {T} (F : list (footprint T)) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, o <= k < o + Z.of_nat w ->
    exists f, In f F /\ fp_site f = t /\ fp_lo f <= k < fp_hi f.

(** A written byte belongs to some footprint of its site. *)
Definition written {T} (F : list (footprint T)) (t : T) (k : Z) : Prop :=
  exists f, In f F /\ fp_site f = t /\ fp_lo f <= k /\ k < fp_hi f.

(** Encoding retains the site and both exact integer endpoints. *)
Definition footprint_encoding {T} (ET : encoding T) : encoding (footprint T).
Proof.
  refine (Encoding _ (fun f => encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding))
    (fp_site f, (fp_lo f, fp_hi f))) _).
  intros [s lo hi] [t low high] Heq.
  pose proof (encode_injective (pair_encoding ET (pair_encoding Z_encoding Z_encoding))
    (s, (lo, hi)) (t, (low, high)) Heq) as Hpair.
  now injection Hpair as -> -> ->.
Defined.

(** Canonical footprints have increasing site codes and canonical per-site byte ranges. *)
Definition footprints_canonical {T} (ET : encoding T) (F : list (footprint T)) : Prop :=
  Forall (fun f => fp_lo f < fp_hi f) F /\
  StronglySorted (fun f g => (encode ET (fp_site f) < encode ET (fp_site g))%positive \/
    (fp_site f = fp_site g /\ fp_hi f < fp_lo g)) F.

(** The ranges of one site retain their original list order. *)
Definition site_ranges {T} (ET : encoding T) (F : list (footprint T)) (t : T) : list range :=
  map (fun f => (fp_lo f, fp_hi f))
    (filter (fun f => Pos.eqb (encode ET (fp_site f)) (encode ET t)) F).

Lemma written_nil : forall T (t : T) k, ~ written [] t k.
Proof.
  intros T t k [f [Hfalse _]]. exact Hfalse.
Qed.

Lemma written_cons : forall T (f : footprint T) F t k,
  written (f :: F) t k <->
  (fp_site f = t /\ fp_lo f <= k < fp_hi f) \/ written F t k.
Proof.
  intros T f F t k. unfold written. cbn. split.
  - intros [g [[Heq|Hin] [Hsite Hb]]]; [subst g; now left|right; exists g; tauto].
  - intros [[Hsite Hb]|[g [Hin [Hsite Hb]]]]; [exists f|exists g]; intuition.
Qed.

Lemma written_app : forall T (F G : list (footprint T)) t k,
  written (F ++ G) t k <-> written F t k \/ written G t k.
Proof.
  intros T F G t k. unfold written. setoid_rewrite in_app_iff. firstorder.
Qed.

Lemma site_ranges_written : forall T (ET : encoding T) F t k,
  ranges_in (site_ranges ET F t) k <-> written F t k.
Proof.
  intros T ET F t k. unfold site_ranges, ranges_in, written. split.
  - intros [r [Hin Hb]]. apply in_map_iff in Hin as [f [Heq Hin]].
    apply filter_In in Hin as [Hin Hsite]. apply Pos.eqb_eq, (encode_injective ET) in Hsite.
    subst r. exists f. cbn in Hb. tauto.
  - intros [f [Hin [Hsite Hb]]]. exists (fp_lo f, fp_hi f). split; [|exact Hb].
    apply in_map_iff. exists f. split; [reflexivity|]. apply filter_In. split; [exact Hin|].
    rewrite Hsite, Pos.eqb_refl. reflexivity.
Qed.

(** Missing site bindings denote the empty byte set. *)
Definition footprint_lookup {T} (ET : encoding T) (m : Map.t T byte_ranges) (t : T) : byte_ranges :=
  match Map.get ET t m with
  | Some rs => rs
  | None => ranges_empty
  end.

Module FootprintRangeOrder.
  Definition t := range.
  Definition leb (r s : range) := Z.leb (fst r) (fst s).

  (** Lower-endpoint comparison is total, including duplicate lower endpoints. *)
  Theorem leb_total : forall r s, leb r s = true \/ leb s r = true.
  Proof.
    intros r s. unfold leb. destruct (Z.leb (fst r) (fst s)) eqn:Hle; [now left|right].
    apply Z.leb_gt in Hle. apply Z.leb_le. lia.
  Qed.
End FootprintRangeOrder.
Import FootprintRangeOrder.

Module FootprintRangeSort := Sort FootprintRangeOrder.
Import FootprintRangeSort.

Definition footprint_ranges_order (rs : list range) : list range :=
  FootprintRangeSort.sort (filter (fun r => fst r <? snd r) rs).

Lemma footprint_ranges_order_in : forall rs r,
  In r (footprint_ranges_order rs) <-> In r rs /\ fst r < snd r.
Proof.
  intros rs r. unfold footprint_ranges_order.
  assert (Hsortin : In r (FootprintRangeSort.sort (filter (fun s => fst s <? snd s) rs)) <->
    In r (filter (fun s => fst s <? snd s) rs)).
  { split; intro H.
    - eapply Permutation_in; [apply Permutation_sym, FootprintRangeSort.Permuted_sort|exact H].
    - eapply Permutation_in; [apply FootprintRangeSort.Permuted_sort|exact H]. }
  rewrite Hsortin, filter_In, Z.ltb_lt. reflexivity.
Qed.

Lemma footprint_ranges_order_positive : forall rs,
  Forall (fun r => fst r < snd r) (footprint_ranges_order rs).
Proof.
  intros rs. rewrite Forall_forall. intros r Hin.
  apply footprint_ranges_order_in in Hin. tauto.
Qed.

Lemma footprint_ranges_order_sorted : forall rs,
  StronglySorted (fun r s => fst r <= fst s) (footprint_ranges_order rs).
Proof.
  intros rs. unfold footprint_ranges_order.
  pose proof (FootprintRangeSort.StronglySorted_sort
    (filter (fun r => fst r <? snd r) rs)) as Hsort.
  assert (Htrans : forall r s t, FootprintRangeOrder.leb r s = true ->
    FootprintRangeOrder.leb s t = true -> FootprintRangeOrder.leb r t = true).
  { intros r s t Hr Hs. unfold FootprintRangeOrder.leb in *.
    apply Z.leb_le in Hr, Hs. apply Z.leb_le. lia. }
  specialize (Hsort Htrans).
  induction Hsort as [|r rest Hsort IH Hafter]; [constructor|].
  constructor; [exact IH|]. rewrite Forall_forall in Hafter |- *.
  intros s Hin. specialize (Hafter s Hin). apply Z.leb_le. exact Hafter.
Qed.

(** Each site's raw ranges are sorted and coalesced once, without repeated insertion scans. *)
Definition footprint_ranges_prepare (rs : list range) : byte_ranges.
Proof.
  refine (exist _ (ranges_coalesce (footprint_ranges_order rs)) _).
  pose proof (footprint_ranges_order_positive rs) as Hpositive.
  pose proof (footprint_ranges_order_sorted rs) as Hsort.
  destruct (footprint_ranges_order rs) as [|r rest]; [exact ranges_wf_nil|].
  inversion Hpositive as [|? ? Hr Hrest]; subst.
  inversion Hsort as [|? ? Hsorted Hafter]; subst.
  apply ranges_coalesce_wf; assumption.
Defined.

Lemma footprint_ranges_prepare_in : forall rs k,
  ranges_mem (footprint_ranges_prepare rs) k = true <-> ranges_in rs k.
Proof.
  intros rs k. rewrite ranges_mem_spec. cbn [footprint_ranges_prepare proj1_sig].
  assert (Hbytes : ranges_in (ranges_coalesce (footprint_ranges_order rs)) k <->
    ranges_in (footprint_ranges_order rs) k).
  { pose proof (footprint_ranges_order_positive rs) as Hpositive.
    pose proof (footprint_ranges_order_sorted rs) as Hsort.
    destruct (footprint_ranges_order rs) as [|r rest]; [reflexivity|].
    inversion Hpositive as [|? ? Hr Hrest]; subst.
    inversion Hsort as [|? ? Hsorted Hafter]; subst.
    cbn [ranges_coalesce]. rewrite ranges_coalesce_in, ranges_in_cons;
      try reflexivity; assumption. }
  rewrite Hbytes. unfold ranges_in. setoid_rewrite footprint_ranges_order_in.
  split; intros [r [Hin Hb]]; exists r; intuition lia.
Qed.

Definition footprint_raw_lookup {T} (ET : encoding T) (m : Map.t T (list range)) (t : T) :
  list range :=
  match Map.get ET t m with
  | Some rs => rs
  | None => []
  end.

(** Group raw ranges by site once; each update only prepends to its indexed bucket. *)
Fixpoint footprint_raw_index {T} (ET : encoding T) (F : list (footprint T)) :
  Map.t T (list range) :=
  match F with
  | [] => Map.empty
  | f :: rest =>
    let m := footprint_raw_index ET rest in
    Map.set ET (fp_site f) ((fp_lo f, fp_hi f) :: footprint_raw_lookup ET m (fp_site f)) m
  end.

Lemma footprint_raw_index_wf : forall T (ET : encoding T) F, Map.wf ET (footprint_raw_index ET F).
Proof.
  intros T ET F. induction F as [|f rest IH]; cbn [footprint_raw_index].
  - apply Map.wf_empty.
  - apply Map.wf_set. exact IH.
Qed.

Lemma footprint_raw_index_written : forall T (ET : encoding T) F t k,
  ranges_in (footprint_raw_lookup ET (footprint_raw_index ET F) t) k <-> written F t k.
Proof.
  intros T ET F. induction F as [|f rest IH]; intros t k.
  - unfold footprint_raw_lookup. cbn [footprint_raw_index]. rewrite Map.get_empty.
    split; [intro H; exfalso; exact (ranges_in_nil k H)|
      intro H; exfalso; exact (written_nil T t k H)].
  - cbn [footprint_raw_index]. rewrite written_cons. unfold footprint_raw_lookup at 1.
    destruct (Pos.eq_dec (encode ET t) (encode ET (fp_site f))) as [Heq|Hne].
    + apply (encode_injective ET) in Heq. subst t. rewrite Map.get_set_same.
      rewrite ranges_in_cons, IH. cbn [fst snd]. intuition.
    + rewrite Map.get_set_other by (intro Heq; apply Hne; now subst t).
      change (ranges_in (footprint_raw_lookup ET (footprint_raw_index ET rest) t) k <->
        (fp_site f = t /\ fp_lo f <= k < fp_hi f) \/ written rest t k).
      rewrite IH. split; [now right|intros [[Heq _]|H]; [exfalso; apply Hne; now subst t|exact H]].
Qed.

(** Preparing indexed buckets normalizes every site independently in one map traversal. *)
Definition footprint_index {T} (ET : encoding T) (F : list (footprint T)) : Map.t T byte_ranges :=
  Map.map footprint_ranges_prepare (footprint_raw_index ET F).

Lemma footprint_index_wf : forall T (ET : encoding T) F, Map.wf ET (footprint_index ET F).
Proof.
  intros T ET F. apply Map.wf_map, footprint_raw_index_wf.
Qed.

Lemma footprint_index_written : forall T (ET : encoding T) F t k,
  ranges_mem (footprint_lookup ET (footprint_index ET F) t) k = true <-> written F t k.
Proof.
  intros T ET F t k. rewrite <- (footprint_raw_index_written T ET F t k).
  unfold footprint_lookup, footprint_index, footprint_raw_lookup. rewrite Map.get_map.
  destruct (Map.get ET t (footprint_raw_index ET F)) as [rs|]; cbn [option_map].
  - apply footprint_ranges_prepare_in.
  - rewrite ranges_mem_empty. split; [discriminate|intro H; exfalso; exact (ranges_in_nil k H)].
Qed.

Module FootprintCodeOrder.
  Definition t := positive.
  Definition leb := Pos.leb.

  (** Positive-code comparison is total. *)
  Theorem leb_total : forall p q, leb p q = true \/ leb q p = true.
  Proof.
    intros p q. destruct (Pos.leb p q) eqn:Hle; [now left|right].
    apply Pos.leb_gt in Hle. apply Pos.leb_le. lia.
  Qed.
End FootprintCodeOrder.
Import FootprintCodeOrder.

Module FootprintSort := Sort FootprintCodeOrder.
Import FootprintSort.

(** Site codes are sorted once when converting an index back to its canonical list. *)
Definition footprint_codes {T} (m : Map.t T byte_ranges) : list positive :=
  FootprintSort.sort (map fst (Trie.elements m)).

Lemma footprint_codes_in : forall T (m : Map.t T byte_ranges) p,
  In p (footprint_codes m) <-> exists v, Trie.get p m = Some v.
Proof.
  intros T m p. unfold footprint_codes.
  assert (Hsortin : In p (FootprintSort.sort (map fst (Trie.elements m))) <->
    In p (map fst (Trie.elements m))).
  { split; intro H.
    - eapply Permutation_in; [apply Permutation_sym, FootprintSort.Permuted_sort|exact H].
    - eapply Permutation_in; [apply FootprintSort.Permuted_sort|exact H]. }
  rewrite Hsortin.
  rewrite in_map_iff. split.
  - intros [[q v] [Heq Hin]]. cbn in Heq. subst q. exists v. now apply Trie.elements_sound.
  - intros [v Hget]. exists (p, v). split; [reflexivity|now apply Trie.elements_complete].
Qed.

Lemma footprint_codes_sorted : forall T (m : Map.t T byte_ranges),
  StronglySorted Pos.lt (footprint_codes m).
Proof.
  intros T m.
  assert (Hnodup : NoDup (footprint_codes m)).
  { eapply Permutation_NoDup; [apply FootprintSort.Permuted_sort|apply Trie.elements_nodup]. }
  assert (Hsort : StronglySorted (fun p q => Pos.leb p q = true) (footprint_codes m)).
  { apply FootprintSort.StronglySorted_sort. intros p q r Hp Hq.
    apply Pos.leb_le in Hp, Hq. apply Pos.leb_le. lia. }
  induction Hsort as [|p ps Hsort IH Hafter]; [constructor|].
  inversion Hnodup as [|? ? Hnot Hrest]; subst. constructor; [now apply IH|].
  rewrite Forall_forall in Hafter |- *. intros q Hin. specialize (Hafter q Hin).
  apply Pos.leb_le in Hafter. assert (p <> q) by (intro Heq; subst q; contradiction). lia.
Qed.

(** One site's block is its canonical range list with the site attached. *)
Definition footprint_block {T} (t : T) (rs : byte_ranges) : list (footprint T) :=
  map (fun r => Footprint t (fst r) (snd r)) (proj1_sig rs).

Lemma footprint_block_in : forall T (t : T) rs f,
  In f (footprint_block t rs) <-> fp_site f = t /\ In (fp_lo f, fp_hi f) (proj1_sig rs).
Proof.
  intros T t rs [s lo hi]. unfold footprint_block. rewrite in_map_iff. cbn. split.
  - intros [[low high] [Heq Hin]]. cbn in Heq. injection Heq as -> -> ->. tauto.
  - intros [Heq Hin]. subst s. exists (lo, hi). split; [reflexivity|exact Hin].
Qed.

Lemma footprint_block_written : forall T (s t : T) rs k,
  written (footprint_block s rs) t k <-> s = t /\ ranges_mem rs k = true.
Proof.
  intros T s t rs k. unfold written. setoid_rewrite footprint_block_in.
  rewrite ranges_mem_spec. unfold ranges_in. split.
  - intros [f [[Hsite Hin] [Htarget Hb]]]. split; [congruence|].
    exists (fp_lo f, fp_hi f). tauto.
  - intros [Heq [[lo hi] [Hin Hb]]]. subst t. exists (Footprint s lo hi). cbn. tauto.
Qed.

Fixpoint footprint_emit_codes {T} (m : Map.t T byte_ranges) (ps : list positive) :
  list (footprint T) :=
  match ps with
  | [] => []
  | p :: rest =>
    match Trie.get p m with
    | Some (t, rs) => footprint_block t rs ++ footprint_emit_codes m rest
    | None => footprint_emit_codes m rest
    end
  end.

Definition footprint_emit {T} (m : Map.t T byte_ranges) : list (footprint T) :=
  footprint_emit_codes m (footprint_codes m).

Lemma footprint_emit_codes_written : forall T (m : Map.t T byte_ranges) ps t k,
  written (footprint_emit_codes m ps) t k <->
  exists p rs, In p ps /\ Trie.get p m = Some (t, rs) /\ ranges_mem rs k = true.
Proof.
  intros T m ps. induction ps as [|p rest IH]; intros t k; cbn [footprint_emit_codes].
  - split; [intro H; exfalso; exact (written_nil T t k H)|intros [q [rs [Hfalse _]]];
      contradiction].
  - destruct (Trie.get p m) as [[s rs]|] eqn:Hget.
    + rewrite written_app, footprint_block_written, IH. cbn. split.
      * intros [[Heq Hmem]|[q [qs [Hin Hdata]]]].
        -- subst s. exists p, rs. tauto.
        -- exists q, qs. tauto.
      * intros [q [qs [[Heq|Hin] [Hdata Hmem]]]].
        -- subst q. rewrite Hget in Hdata. injection Hdata as -> ->. now left.
        -- right. exists q, qs. tauto.
    + rewrite IH. cbn. split.
      * intros [q [qs [Hin Hdata]]]. exists q, qs. tauto.
      * intros [q [qs [[Heq|Hin] [Hdata Hmem]]]].
        -- subst q. rewrite Hget in Hdata. discriminate.
        -- exists q, qs. tauto.
Qed.

Lemma footprint_emit_written : forall T (ET : encoding T) (m : Map.t T byte_ranges) t k,
  Map.wf ET m ->
  (written (footprint_emit m) t k <-> ranges_mem (footprint_lookup ET m t) k = true).
Proof.
  intros T ET m t k Hwf. unfold footprint_emit. rewrite footprint_emit_codes_written.
  split.
  - intros [p [rs [Hin [Hget Hmem]]]].
    pose proof (Hwf p t rs Hget) as Hcode. unfold footprint_lookup, Map.get, Map.code_get.
    rewrite Hcode, Hget. exact Hmem.
  - unfold footprint_lookup. destruct (Map.get ET t m) as [rs|] eqn:Hget;
      [|rewrite ranges_mem_empty; discriminate].
    intro Hmem. apply (Map.get_pair ET) in Hget; [|exact Hwf].
    exists (encode ET t), rs. split.
    + apply footprint_codes_in. now exists (t, rs).
    + tauto.
Qed.

Lemma footprints_canonical_nil : forall T (ET : encoding T), footprints_canonical ET [].
Proof.
  intros T ET. split; constructor.
Qed.

Lemma footprints_canonical_cons : forall T (ET : encoding T) f F,
  footprints_canonical ET (f :: F) <-> fp_lo f < fp_hi f /\
  footprints_canonical ET F /\
  Forall (fun g => (encode ET (fp_site f) < encode ET (fp_site g))%positive \/
    (fp_site f = fp_site g /\ fp_hi f < fp_lo g)) F.
Proof.
  intros T ET f F. unfold footprints_canonical. split.
  - intros [Hpositive Hsort]. inversion Hpositive as [|? ? Hf HF]; subst.
    inversion Hsort as [|? ? Hsorted Hafter]; subst. intuition.
  - intros [Hf [[Hpositive Hsort] Hafter]]. split; constructor; assumption.
Qed.

Lemma footprints_canonical_app : forall T (ET : encoding T) F G,
  footprints_canonical ET F -> footprints_canonical ET G ->
  (forall f g, In f F -> In g G ->
    (encode ET (fp_site f) < encode ET (fp_site g))%positive \/
      (fp_site f = fp_site g /\ fp_hi f < fp_lo g)) ->
  footprints_canonical ET (F ++ G).
Proof.
  intros T ET F G [HF HsortF] [HG HsortG] Hcross. split.
  - now apply Forall_app.
  - apply Trie.strongly_sorted_app; assumption.
Qed.

Lemma footprint_block_canonical : forall T (ET : encoding T) t rs,
  footprints_canonical ET (footprint_block t rs).
Proof.
  intros T ET t [xs [Hpositive Hsort]]. unfold footprint_block. cbn [proj1_sig]. split.
  - rewrite Forall_forall in Hpositive |- *. intros f Hin.
    apply in_map_iff in Hin as [r [Heq Hin]]. subst f. cbn. now apply Hpositive.
  - eapply Trie.strongly_sorted_map; [|exact Hsort].
    intros r s Hbefore. right. cbn. auto.
Qed.

Lemma footprint_emit_codes_code : forall T (ET : encoding T) (m : Map.t T byte_ranges) ps f,
  Map.wf ET m -> In f (footprint_emit_codes m ps) -> In (encode ET (fp_site f)) ps.
Proof.
  intros T ET m ps. induction ps as [|p rest IH]; intros f Hwf Hin; [exact Hin|].
  cbn [footprint_emit_codes] in Hin. destruct (Trie.get p m) as [[t rs]|] eqn:Hget.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply footprint_block_in in Hin as [Hsite _]. left.
      rewrite Hsite. symmetry. exact (Hwf p t rs Hget).
    + right. now apply IH.
  - right. now apply IH.
Qed.

Lemma footprint_emit_codes_canonical : forall T (ET : encoding T) (m : Map.t T byte_ranges) ps,
  Map.wf ET m -> StronglySorted Pos.lt ps -> footprints_canonical ET (footprint_emit_codes m ps).
Proof.
  intros T ET m ps Hwf Hsort. induction Hsort as [|p rest Hsort IH Hafter].
  - apply footprints_canonical_nil.
  - cbn [footprint_emit_codes]. destruct (Trie.get p m) as [[t rs]|] eqn:Hget; [|exact IH].
    apply footprints_canonical_app; [apply footprint_block_canonical|exact IH|].
    intros f g Hf Hg. apply footprint_block_in in Hf as [Hsite _]. left.
    rewrite Hsite, (Hwf p t rs Hget).
    rewrite Forall_forall in Hafter. apply Hafter.
    exact (footprint_emit_codes_code T ET m rest g Hwf Hg).
Qed.

Lemma footprint_emit_canonical : forall T (ET : encoding T) (m : Map.t T byte_ranges),
  Map.wf ET m -> footprints_canonical ET (footprint_emit m).
Proof.
  intros T ET m Hwf. apply footprint_emit_codes_canonical; [exact Hwf|].
  apply footprint_codes_sorted.
Qed.

(** Normalization groups sites in an index and emits each site's canonical byte ranges. *)
Definition footprints_normalise {T} (ET : encoding T) (F : list (footprint T)) :
  list (footprint T) := footprint_emit (footprint_index ET F).

(** Normalization always produces a canonical footprint list. *)
Theorem footprints_normalise_canonical : forall {T} (ET : encoding T) F,
  footprints_canonical ET (footprints_normalise ET F).
Proof.
  intros T ET F. apply footprint_emit_canonical, footprint_index_wf.
Qed.

(** Normalization preserves every site's written bytes. *)
Theorem footprints_normalise_written : forall {T} (ET : encoding T) F t k,
  written (footprints_normalise ET F) t k <-> written F t k.
Proof.
  intros T ET F t k. unfold footprints_normalise.
  rewrite footprint_emit_written by apply footprint_index_wf. apply footprint_index_written.
Qed.

Definition footprint_inter_index {T} (ET : encoding T) (F G : list (footprint T)) :
  Map.t T byte_ranges :=
  Map.combine ET (fun a b =>
    match a, b with
    | Some x, Some y => Some (ranges_inter x y)
    | _, _ => None
    end) (footprint_index ET F) (footprint_index ET G).

Definition footprint_diff_index {T} (ET : encoding T) (F G : list (footprint T)) :
  Map.t T byte_ranges :=
  Map.combine ET (fun a b =>
    match a, b with
    | Some x, Some y => Some (ranges_diff x y)
    | Some x, None => Some x
    | None, _ => None
    end) (footprint_index ET F) (footprint_index ET G).

(** Intersection normalizes both site indexes and intersects their canonical range payloads. *)
Definition footprints_inter {T} (ET : encoding T) (F G : list (footprint T)) :
  list (footprint T) := footprint_emit (footprint_inter_index ET F G).

(** Difference normalizes both site indexes and subtracts their canonical range payloads. *)
Definition footprints_diff {T} (ET : encoding T) (F G : list (footprint T)) :
  list (footprint T) := footprint_emit (footprint_diff_index ET F G).

Lemma footprint_inter_index_wf : forall T (ET : encoding T) F G,
  Map.wf ET (footprint_inter_index ET F G).
Proof.
  intros T ET F G. apply Map.wf_combine; apply footprint_index_wf.
Qed.

Lemma footprint_diff_index_wf : forall T (ET : encoding T) F G,
  Map.wf ET (footprint_diff_index ET F G).
Proof.
  intros T ET F G. apply Map.wf_combine; apply footprint_index_wf.
Qed.

Lemma footprint_inter_lookup : forall T (ET : encoding T) F G t k,
  ranges_mem (footprint_lookup ET (footprint_inter_index ET F G) t) k =
  (ranges_mem (footprint_lookup ET (footprint_index ET F) t) k &&
    ranges_mem (footprint_lookup ET (footprint_index ET G) t) k)%bool.
Proof.
  intros T ET F G t k. unfold footprint_lookup, footprint_inter_index.
  rewrite Map.get_combine by reflexivity.
  destruct (Map.get ET t (footprint_index ET F)) as [rs|],
    (Map.get ET t (footprint_index ET G)) as [ss|];
    rewrite ?ranges_mem_inter, ?ranges_mem_empty, ?andb_false_r; reflexivity.
Qed.

Lemma footprint_diff_lookup : forall T (ET : encoding T) F G t k,
  ranges_mem (footprint_lookup ET (footprint_diff_index ET F G) t) k =
  (ranges_mem (footprint_lookup ET (footprint_index ET F) t) k &&
    negb (ranges_mem (footprint_lookup ET (footprint_index ET G) t) k))%bool.
Proof.
  intros T ET F G t k. unfold footprint_lookup, footprint_diff_index.
  rewrite Map.get_combine by reflexivity.
  destruct (Map.get ET t (footprint_index ET F)) as [rs|],
    (Map.get ET t (footprint_index ET G)) as [ss|];
    rewrite ?ranges_mem_diff, ?ranges_mem_empty; cbn; rewrite ?andb_true_r; reflexivity.
Qed.

(** Intersection always produces a canonical footprint list. *)
Theorem footprints_inter_canonical : forall {T} (ET : encoding T) F G,
  footprints_canonical ET (footprints_inter ET F G).
Proof.
  intros T ET F G. apply footprint_emit_canonical, footprint_inter_index_wf.
Qed.

(** Intersection keeps exactly the written bytes common to both inputs. *)
Theorem footprints_inter_written : forall {T} (ET : encoding T) F G t k,
  written (footprints_inter ET F G) t k <-> written F t k /\ written G t k.
Proof.
  intros T ET F G t k. unfold footprints_inter.
  rewrite footprint_emit_written by apply footprint_inter_index_wf.
  rewrite footprint_inter_lookup, andb_true_iff, !footprint_index_written. reflexivity.
Qed.

(** Difference always produces a canonical footprint list. *)
Theorem footprints_diff_canonical : forall {T} (ET : encoding T) F G,
  footprints_canonical ET (footprints_diff ET F G).
Proof.
  intros T ET F G. apply footprint_emit_canonical, footprint_diff_index_wf.
Qed.

(** Difference removes exactly the written bytes present in its second input. *)
Theorem footprints_diff_written : forall {T} (ET : encoding T) F G t k,
  written (footprints_diff ET F G) t k <-> written F t k /\ ~ written G t k.
Proof.
  intros T ET F G t k. unfold footprints_diff.
  rewrite footprint_emit_written by apply footprint_diff_index_wf.
  rewrite footprint_diff_lookup, andb_true_iff, negb_true_iff, <- not_true_iff_false,
    !footprint_index_written. reflexivity.
Qed.

(** Filtering a canonical footprint list at one site yields canonical byte ranges. *)
Theorem footprints_canonical_ranges : forall {T} (ET : encoding T) F t,
  footprints_canonical ET F -> ranges_wf (site_ranges ET F t).
Proof.
  intros T ET F. induction F as [|f rest IH]; intros t Hcanonical.
  - exact ranges_wf_nil.
  - apply footprints_canonical_cons in Hcanonical as [Hf [Hrest Hafter]].
    unfold site_ranges. cbn [filter].
    destruct (Pos.eqb (encode ET (fp_site f)) (encode ET t)) eqn:Hsite.
    + apply Pos.eqb_eq, (encode_injective ET) in Hsite. subst t.
      cbn [map]. apply ranges_wf_cons. split; [exact Hf|]. split; [now apply IH|].
      rewrite Forall_forall in Hafter |- *. intros r Hin.
      apply in_map_iff in Hin as [g [Heq Hin]]. subst r. cbn.
      apply filter_In in Hin as [Hin Hcode]. apply Pos.eqb_eq in Hcode.
      specialize (Hafter g Hin). destruct Hafter as [Hlt|[_ Hbefore]]; [lia|exact Hbefore].
    + apply IH. exact Hrest.
Qed.

Lemma footprint_head_lower : forall T (ET : encoding T) f F t k,
  footprints_canonical ET (f :: F) -> written (f :: F) t k ->
  (encode ET (fp_site f) <= encode ET t)%positive /\
  (fp_site f = t -> fp_lo f <= k).
Proof.
  intros T ET f F t k Hcanonical [g [Hin [Hsite Hb]]].
  apply footprints_canonical_cons in Hcanonical as [Hf [_ Hafter]].
  destruct Hin as [Heq|Hin].
  - subst g. subst t. split; [lia|intros _; lia].
  - rewrite Forall_forall in Hafter. specialize (Hafter g Hin).
    rewrite Hsite in Hafter. destruct Hafter as [Hlt|[Heq Hbefore]].
    + split; [lia|]. intro Heq. rewrite Heq in Hlt. lia.
    + split; [rewrite Heq; lia|intros _; lia].
Qed.

Lemma footprint_tail_at_site : forall T (ET : encoding T) f F k,
  footprints_canonical ET (f :: F) -> written F (fp_site f) k -> fp_hi f < k.
Proof.
  intros T ET f F k Hcanonical [g [Hin [Hsite Hb]]].
  apply footprints_canonical_cons in Hcanonical as [_ [_ Hafter]].
  rewrite Forall_forall in Hafter. specialize (Hafter g Hin).
  rewrite Hsite in Hafter. destruct Hafter as [Hlt|[_ Hbefore]]; lia.
Qed.

Lemma footprint_head_end_absent : forall T (ET : encoding T) f F,
  footprints_canonical ET (f :: F) -> ~ written (f :: F) (fp_site f) (fp_hi f).
Proof.
  intros T ET f F Hcanonical Hb. apply written_cons in Hb as [[_ Hb]|Hb]; [lia|].
  pose proof (footprint_tail_at_site T ET f F (fp_hi f) Hcanonical Hb). lia.
Qed.

Lemma footprints_heads_equal : forall T (ET : encoding T) f F g G,
  footprints_canonical ET (f :: F) -> footprints_canonical ET (g :: G) ->
  (forall t k, written (f :: F) t k <-> written (g :: G) t k) -> f = g.
Proof.
  intros T ET [s lo hi] F [t low high] G HF HG Hequiv.
  pose proof (proj1 (footprints_canonical_cons T ET _ _) HF) as [Hf _].
  pose proof (proj1 (footprints_canonical_cons T ET _ _) HG) as [Hg _]. cbn in Hf, Hg.
  assert (Hfb : written (Footprint s lo hi :: F) s lo).
  { apply written_cons. left. cbn. split; [reflexivity|lia]. }
  assert (Hgb : written (Footprint t low high :: G) t low).
  { apply written_cons. left. cbn. split; [reflexivity|lia]. }
  apply Hequiv in Hfb. apply Hequiv in Hgb.
  pose proof (footprint_head_lower T ET _ _ _ _ HG Hfb) as [Hst Hlow].
  pose proof (footprint_head_lower T ET _ _ _ _ HF Hgb) as [Hts Hlo]. cbn in *.
  assert (Hcode : encode ET s = encode ET t) by lia.
  apply (encode_injective ET) in Hcode. subst t.
  specialize (Hlow eq_refl). specialize (Hlo eq_refl).
  assert (Heqlo : lo = low) by lia. subst low.
  assert (Heqhi : hi = high).
  { destruct (Z.lt_trichotomy hi high) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
    - exfalso. apply (footprint_head_end_absent T ET _ _ HF). apply Hequiv.
      apply written_cons. left. cbn. split; [reflexivity|lia].
    - exfalso. apply (footprint_head_end_absent T ET _ _ HG). apply Hequiv.
      apply written_cons. left. cbn. split; [reflexivity|lia]. }
  now subst high.
Qed.

(** A canonical footprint list is uniquely determined by its site-indexed written bytes. *)
Theorem footprints_ext : forall {T} (ET : encoding T) F G,
  footprints_canonical ET F -> footprints_canonical ET G ->
  (forall t k, written F t k <-> written G t k) -> F = G.
Proof.
  intros T ET F. induction F as [|f rest IH]; intros [|g tail] HF HG Hequiv;
    [reflexivity| | |].
  - pose proof (proj1 (footprints_canonical_cons T ET _ _) HG) as [Hg _].
    exfalso. apply (written_nil T (fp_site g) (fp_lo g)), Hequiv, written_cons.
    left. split; [reflexivity|lia].
  - pose proof (proj1 (footprints_canonical_cons T ET _ _) HF) as [Hf _].
    exfalso. apply (written_nil T (fp_site f) (fp_lo f)), Hequiv, written_cons.
    left. split; [reflexivity|lia].
  - assert (Heq : f = g) by (eapply footprints_heads_equal; eassumption). subst g.
    pose proof (proj1 (footprints_canonical_cons T ET _ _) HF) as [_ [Hrest _]].
    pose proof (proj1 (footprints_canonical_cons T ET _ _) HG) as [_ [Htail _]].
    f_equal. apply IH; try assumption. intros t k. specialize (Hequiv t k).
    rewrite !written_cons in Hequiv.
    destruct (Pos.eq_dec (encode ET (fp_site f)) (encode ET t)) as [Hcode|Hne].
    + apply (encode_injective ET) in Hcode. subst t.
      pose proof (footprint_tail_at_site T ET f rest k HF) as Hrestbyte.
      pose proof (footprint_tail_at_site T ET f tail k HG) as Htailbyte.
      intuition lia.
    + assert (Hsite : fp_site f <> t) by (intro Heq; apply Hne; now rewrite Heq).
      tauto.
Qed.

(** Coverage entails written membership of each individual access byte. *)
Theorem covered_written : forall {T} (F : list (footprint T)) t o w,
  covered F t o w -> forall k, o <= k < o + Z.of_nat w -> written F t k.
Proof.
  intros T F t o w Hcovered k Hk. exact (Hcovered k Hk).
Qed.

(** Coverage and bytewise written membership coincide, including zero-width accesses. *)
Theorem covered_bytewise : forall {T} (F : list (footprint T)) t o w,
  covered F t o w <-> forall k, o <= k < o + Z.of_nat w -> written F t k.
Proof.
  reflexivity.
Qed.

(** Byte inclusion traverses site bindings once and consults the prebuilt right index. *)
Definition footprints_subset {T} (ET : encoding T) (F G : list (footprint T)) : bool :=
  let right := footprint_index ET G in
  forallb (fun entry => ranges_subset (snd entry) (footprint_lookup ET right (fst entry)))
    (Map.elements (footprint_index ET F)).

Lemma footprints_subset_spec : forall T (ET : encoding T) F G,
  footprints_subset ET F G = true <-> forall t k, written F t k -> written G t k.
Proof.
  intros T ET F G. unfold footprints_subset. rewrite forallb_forall. split.
  - intros Hsubset t k Hwritten.
    apply (proj2 (footprint_index_written T ET F t k)) in Hwritten.
    unfold footprint_lookup in Hwritten.
    destruct (Map.get ET t (footprint_index ET F)) as [rs|] eqn:Hget;
      [|rewrite ranges_mem_empty in Hwritten; discriminate].
    assert (Hin : In (t, rs) (Map.elements (footprint_index ET F))).
    { apply (Map.elements_complete ET); [apply footprint_index_wf|exact Hget]. }
    specialize (Hsubset (t, rs) Hin). cbn in Hsubset.
    apply (proj1 (footprint_index_written T ET G t k)).
    exact (proj1 (ranges_subset_spec _ _) Hsubset k Hwritten).
  - intros Hbytes [t rs] Hin. cbn.
    apply (Map.elements_sound ET) in Hin; [|apply footprint_index_wf].
    apply ranges_subset_spec. intros k Hmem.
    apply (proj2 (footprint_index_written T ET G t k)), Hbytes.
    apply (proj1 (footprint_index_written T ET F t k)).
    unfold footprint_lookup. now rewrite Hin.
Qed.

(** Reached must-facts contain a canonical footprint list. *)
Definition canonical_footprints {T} (ET : encoding T) : Type :=
  { F : list (footprint T) | footprints_canonical ET F }.

(** Unreached is the fresh bottom, distinct from a reached state with no known writes. *)
Definition range_must {T} (ET : encoding T) : Type := lift_bot (canonical_footprints ET).

(** Raw footprint lists enter the carrier through byte-preserving normalization. *)
Definition range_reached {T} (ET : encoding T) (F : list (footprint T)) : range_must ET :=
  Reached (exist _ (footprints_normalise ET F) (footprints_normalise_canonical ET F)).

(** Unreached entails all must-facts; a reached state entails its actual written bytes. *)
Definition range_written {T} {ET : encoding T} (a : range_must ET) (t : T) (k : Z) : Prop :=
  match a with
  | Unreached => True
  | Reached F => written (proj1_sig F) t k
  end.

(** Entering the reached carrier preserves exactly the raw list's written bytes. *)
Theorem range_reached_written : forall {T} (ET : encoding T) F t k,
  range_written (range_reached ET F) t k <-> written F t k.
Proof.
  intros T ET F t k. apply footprints_normalise_written.
Qed.

Definition range_must_join {T} (ET : encoding T) (a b : range_must ET) : range_must ET :=
  match a, b with
  | Unreached, _ => b
  | _, Unreached => a
  | Reached F, Reached G => range_reached ET (footprints_inter ET (proj1_sig F) (proj1_sig G))
  end.

(** Reverse byte inclusion orders reached facts; joining keeps their shared known writes. *)
Definition range_must_lattice {T} (ET : encoding T) : lattice (range_must ET) :=
  {| OrderLattice.leb := fun a b =>
       match a, b with
       | Unreached, _ => true
       | Reached _, Unreached => false
       | Reached F, Reached G => footprints_subset ET (proj1_sig G) (proj1_sig F)
       end;
     bot := Unreached;
     join := range_must_join ET;
     widen := range_must_join ET;
     narrow := fun a _ => a |}.

Lemma range_must_reached_order : forall T (ET : encoding T) (F G : canonical_footprints ET),
  OrderLattice.leb (range_must_lattice ET) (Reached F) (Reached G) = true <->
  forall t k, written (proj1_sig G) t k -> written (proj1_sig F) t k.
Proof.
  intros T ET F G. apply footprints_subset_spec.
Qed.

(** The reached order is exactly reverse inclusion of the original raw byte facts. *)
Theorem range_must_leb_spec : forall {T} (ET : encoding T) F G,
  OrderLattice.leb (range_must_lattice ET) (range_reached ET F) (range_reached ET G) = true <->
  forall t k, written G t k -> written F t k.
Proof.
  intros T ET F G. unfold range_reached. rewrite range_must_reached_order. cbn [proj1_sig].
  setoid_rewrite footprints_normalise_written. reflexivity.
Qed.

Lemma range_must_refl : forall T (ET : encoding T) (a : range_must ET),
  OrderLattice.leb (range_must_lattice ET) a a = true.
Proof.
  intros T ET [F|]; [apply range_must_reached_order; auto|reflexivity].
Qed.

Lemma range_must_trans : forall T (ET : encoding T) (a b c : range_must ET),
  OrderLattice.leb (range_must_lattice ET) a b = true ->
  OrderLattice.leb (range_must_lattice ET) b c = true ->
  OrderLattice.leb (range_must_lattice ET) a c = true.
Proof.
  intros T ET [F|] [G|] [H|] Hab Hbc; try discriminate; try reflexivity.
  pose proof (proj1 (range_must_reached_order T ET F G) Hab) as HFG.
  pose proof (proj1 (range_must_reached_order T ET G H) Hbc) as HGH.
  apply range_must_reached_order. auto.
Qed.

Lemma range_must_join_left : forall T (ET : encoding T) (a b : range_must ET),
  OrderLattice.leb (range_must_lattice ET) a (range_must_join ET a b) = true.
Proof.
  intros T ET [F|] [G|]; try reflexivity; [|apply range_must_refl].
  apply range_must_reached_order. cbn [range_must_join range_reached proj1_sig].
  intros t k Hwritten. apply footprints_normalise_written in Hwritten.
  apply footprints_inter_written in Hwritten. tauto.
Qed.

Lemma range_must_join_right : forall T (ET : encoding T) (a b : range_must ET),
  OrderLattice.leb (range_must_lattice ET) b (range_must_join ET a b) = true.
Proof.
  intros T ET [F|] [G|]; try reflexivity; [|apply range_must_refl].
  apply range_must_reached_order. cbn [range_must_join range_reached proj1_sig].
  intros t k Hwritten. apply footprints_normalise_written in Hwritten.
  apply footprints_inter_written in Hwritten. tauto.
Qed.

(** Must-facts satisfy the preorder, bottom, upper-bound and narrowing laws. *)
Theorem range_must_laws : forall {T} (ET : encoding T), lattice_laws (range_must_lattice ET).
Proof.
  intros T ET. constructor.
  - apply range_must_refl.
  - apply range_must_trans.
  - intros [F|]; reflexivity.
  - apply range_must_join_left.
  - apply range_must_join_right.
  - apply range_must_join_left.
  - apply range_must_join_right.
  - intros a b _. apply range_must_refl.
  - intros a b Hle. exact Hle.
Qed.

(** Intersection is the least upper bound in the reverse-inclusion must order. *)
Theorem range_must_lub : forall {T} (ET : encoding T), lub_laws (range_must_lattice ET).
Proof.
  intros T ET. constructor. intros [F|] [G|] [H|] HF HG;
    try discriminate; try reflexivity; try assumption.
  apply range_must_reached_order. cbn [range_must_join range_reached proj1_sig].
  pose proof (proj1 (range_must_reached_order T ET F H) HF) as HbytesF.
  pose proof (proj1 (range_must_reached_order T ET G H) HG) as HbytesG.
  intros t k Hwritten. apply footprints_normalise_written, footprints_inter_written.
  split; [apply HbytesF|apply HbytesG]; exact Hwritten.
Qed.

(** The reached state with no required written bytes is the greatest must-fact. *)
Definition range_must_top {T} (ET : encoding T) : top (range_must_lattice ET).
Proof.
  refine {| top_value := range_reached ET [] |}. intros [F|]; [|reflexivity].
  apply range_must_reached_order. cbn [range_reached proj1_sig].
  intros t k Hfalse. apply footprints_normalise_written in Hfalse.
  exfalso. exact (written_nil T t k Hfalse).
Defined.

(** Adding footprints normalizes their union with the reached state's old writes. *)
Definition range_add {T} (ET : encoding T) (fs : list (footprint T)) (a : range_must ET) :
  range_must ET :=
  match a with
  | Unreached => Unreached
  | Reached F => range_reached ET (fs ++ proj1_sig F)
  end.

(** Removing footprints subtracts their bytes from each reached site's old writes. *)
Definition range_remove {T} (ET : encoding T) (fs : list (footprint T)) (a : range_must ET) :
  range_must ET :=
  match a with
  | Unreached => Unreached
  | Reached F => range_reached ET (footprints_diff ET (proj1_sig F) fs)
  end.

(** Must coverage requires every byte, with vacuous coverage at width zero. *)
Definition range_covers {T} {ET : encoding T}
  (a : range_must ET) (t : T) (o : Z) (w : nat) : Prop :=
  forall k, o <= k < o + Z.of_nat w -> range_written a t k.

(** Reached facts require their known written bytes; Unreached denotes no concrete state. *)
Definition range_must_gamma {T} {ET : encoding T} :
  concretisation (range_must ET) (T -> Z -> Prop) :=
  {| gamma := fun a W =>
       match a with
       | Unreached => False
       | Reached F => forall t k, written (proj1_sig F) t k -> W t k
       end |}.

(** Forgetting must-facts enlarges the set of concrete written-byte states. *)
Theorem range_must_gamma_laws : forall {T} (ET : encoding T),
  concretisation_laws (range_must_lattice ET) range_must_gamma.
Proof.
  intros T ET. constructor. intros [F|] [G|] W Hle Hgamma;
    try discriminate; try contradiction.
  pose proof (proj1 (range_must_reached_order T ET F G) Hle) as Hbytes.
  intros t k Hwritten. apply Hgamma, Hbytes, Hwritten.
Qed.

(** Unreached has no concrete written-byte states. *)
Theorem range_must_gamma_bot_empty : forall {T} (ET : encoding T),
  bottom_empty (range_must_lattice ET) range_must_gamma.
Proof.
  intros T ET. constructor. intros W Hfalse. exact Hfalse.
Qed.

(** The top must-fact imposes no byte requirements on concrete states. *)
Theorem range_must_gamma_top_full : forall {T} (ET : encoding T),
  top_full (range_must_top ET) range_must_gamma.
Proof.
  intros T ET. constructor. intro W.
  change (forall t k, written (footprints_normalise ET []) t k -> W t k).
  intros t k Hfalse. apply footprints_normalise_written in Hfalse.
  exfalso. exact (written_nil T t k Hfalse).
Qed.

(** A covered access consists entirely of concretely written bytes. *)
Theorem range_covers_sound : forall {T} (ET : encoding T) (a : range_must ET) t o w W,
  gamma range_must_gamma a W -> range_covers a t o w ->
  forall k, o <= k < o + Z.of_nat w -> W t k.
Proof.
  intros T ET [F|] t o w W Hgamma Hcovers k Hk; [|contradiction].
  apply Hgamma, Hcovers, Hk.
Qed.

(** Coverage is precisely bytewise must membership, including an empty access. *)
Theorem range_covers_iff_written : forall {T} (ET : encoding T) (a : range_must ET) t o w,
  range_covers a t o w <-> forall k, o <= k < o + Z.of_nat w -> range_written a t k.
Proof.
  reflexivity.
Qed.

Lemma range_add_written : forall T (ET : encoding T) fs (a : range_must ET) t k,
  range_written (range_add ET fs a) t k <-> written fs t k \/ range_written a t k.
Proof.
  intros T ET fs [F|] t k; [|cbn [range_add range_written]; tauto].
  cbn [range_add]. rewrite range_reached_written, written_app. reflexivity.
Qed.

(** Adding preserves old coverage and inserts all explicitly added bytes. *)
Theorem range_covers_add : forall {T} (ET : encoding T) (a : range_must ET) fs t o w,
  range_covers (range_add ET fs a) t o w <->
  forall k, o <= k < o + Z.of_nat w -> written fs t k \/ range_written a t k.
Proof.
  intros T ET a fs t o w. unfold range_covers. setoid_rewrite range_add_written. reflexivity.
Qed.

(** Removing from a reached state keeps exactly the old bytes outside the removed footprints. *)
Theorem range_covers_remove : forall {T} (ET : encoding T) F fs t o w,
  range_covers (range_remove ET fs (range_reached ET F)) t o w <->
  forall k, o <= k < o + Z.of_nat w -> written F t k /\ ~ written fs t k.
Proof.
  intros T ET F fs t o w. unfold range_covers. cbn [range_remove range_reached proj1_sig].
  setoid_rewrite range_reached_written. setoid_rewrite footprints_diff_written.
  setoid_rewrite footprints_normalise_written. reflexivity.
Qed.

(** Added bytes preserve soundness when each added footprint is concretely written. *)
Theorem range_add_gamma : forall {T} (ET : encoding T) (a : range_must ET) fs W,
  gamma range_must_gamma a W ->
  (forall f k, In f fs -> fp_lo f <= k < fp_hi f -> W (fp_site f) k) ->
  gamma range_must_gamma (range_add ET fs a) W.
Proof.
  intros T ET [F|] fs W Hgamma Hadded; [|contradiction].
  change (forall t k, written (footprints_normalise ET (fs ++ proj1_sig F)) t k -> W t k).
  intros t k Hwritten. apply footprints_normalise_written in Hwritten.
  apply written_app in Hwritten as [Hnew|Hold].
  - destruct Hnew as [f [Hin [Hsite Hb]]]. subst t. exact (Hadded f k Hin Hb).
  - exact (Hgamma t k Hold).
Qed.

(** Removing potentially overwritten bytes preserves the requirements outside those footprints. *)
Theorem range_remove_gamma : forall {T} (ET : encoding T) (a : range_must ET) fs W,
  forall W' : T -> Z -> Prop, gamma range_must_gamma a W ->
  (forall t k, ~ written fs t k -> W t k -> W' t k) ->
  gamma range_must_gamma (range_remove ET fs a) W'.
Proof.
  intros T ET [F|] fs W W' Hgamma Hpreserved; [|contradiction].
  change (forall t k,
    written (footprints_normalise ET (footprints_diff ET (proj1_sig F) fs)) t k -> W' t k).
  intros t k Hwritten. apply footprints_normalise_written in Hwritten.
  apply footprints_diff_written in Hwritten as [Hold Houtside].
  apply Hpreserved; [exact Houtside|exact (Hgamma t k Hold)].
Qed.

(** Footprint codes are exactly the documented nested pair encoding of site and bounds. *)
Theorem footprint_encoding_spec : forall {T} (ET : encoding T) (f : footprint T),
  encode (footprint_encoding ET) f =
  encode (pair_encoding ET (pair_encoding Z_encoding Z_encoding))
    (fp_site f, (fp_lo f, fp_hi f)).
Proof.
  reflexivity.
Qed.
