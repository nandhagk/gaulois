(** * Prepared dense finite-universe sets

    A prepared universe connects encoded keys to packed binary set positions.
    For example, preparing [a; b; a] assigns a to bit zero and b to bit one.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsFinSet. *)

From Stdlib Require Import List Bool NArith Lia.
From Gaulois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.

Import List.ListNotations.

(** * Preparation *)

(** A universe stores its ordered keys, lookup index and binary length cache. *)
Record dense_universe (K : Type) : Type := DenseUniverse {
  dense_keys : list K;
  dense_index : Map.t K N;
  dense_length : N
}.

Arguments dense_keys {K}.
Arguments dense_index {K}.
Arguments dense_length {K}.

(** Well-formed universes have distinct keys and exact position and length caches. *)
Definition dense_universe_wf {K} (E : encoding K) (u : dense_universe K) : Prop :=
  NoDup (dense_keys u) /\ Map.wf E (dense_index u) /\
  dense_length u = N.of_nat (List.length (dense_keys u)) /\
  (forall k i, Map.get E k (dense_index u) = Some i <->
    nth_error (dense_keys u) (N.to_nat i) = Some k).

Fixpoint dense_unique {K} (E : encoding K) (seen : FinSet.t K) (keys : list K) : list K :=
  match keys with
  | [] => []
  | k :: rest =>
    if FinSet.mem E k seen then dense_unique E seen rest
    else k :: dense_unique E (FinSet.add E k seen) rest
  end.

Lemma dense_unique_spec {K} (E : encoding K) keys seen k :
  In k (dense_unique E seen keys) <-> In k keys /\ FinSet.mem E k seen = false.
Proof.
  revert seen; induction keys as [|x rest IH]; intro seen; cbn [dense_unique].
  - cbn; tauto.
  - destruct (FinSet.mem E x seen) eqn:Hseen.
    + rewrite IH; cbn; split.
      * intros [Hin Habsent]; auto.
      * intros [[Heq|Hin] Habsent]; [subst x; congruence|auto].
    + change (x = k \/ In k (dense_unique E (FinSet.add E x seen) rest) <->
        (x = k \/ In k rest) /\ FinSet.mem E k seen = false).
      rewrite IH.
      assert (Hadd : FinSet.mem E k (FinSet.add E x seen) = false <->
        k <> x /\ FinSet.mem E k seen = false).
      { pose proof (FinSet.mem_add E k x seen) as Hmem.
        destruct (FinSet.mem E k (FinSet.add E x seen)), (FinSet.mem E k seen);
          intuition congruence. }
      rewrite Hadd; split.
      * intros [Heq|[Hin [_ Hmem]]]; [subst x; auto|auto].
      * intros [[Heq|Hin] Hmem]; [now left|].
        destruct (Pos.eq_dec (encode E k) (encode E x)) as [Heq|Hne].
        -- left; symmetry; now apply (encode_injective E).
        -- right; split; [exact Hin|split; [|exact Hmem]].
           intro Heq; subst x; contradiction.
Qed.

Lemma dense_unique_nodup {K} (E : encoding K) keys seen :
  NoDup (dense_unique E seen keys).
Proof.
  revert seen; induction keys as [|k rest IH]; intro seen; cbn [dense_unique].
  - constructor.
  - destruct (FinSet.mem E k seen); [apply IH|].
    constructor; [|apply IH].
    rewrite dense_unique_spec; intros [_ Habsent].
    assert (Hpresent : FinSet.mem E k (FinSet.add E k seen) = true).
    { apply FinSet.mem_add; left; reflexivity. }
    congruence.
Qed.

Fixpoint dense_number {K} (E : encoding K) (keys : list K) (start : N) : Map.t K N :=
  match keys with
  | [] => Map.empty
  | k :: rest => Map.set E k start (dense_number E rest (N.succ start))
  end.

Lemma dense_number_wf {K} (E : encoding K) keys start :
  Map.wf E (dense_number E keys start).
Proof.
  revert start; induction keys as [|k rest IH]; intro start; cbn [dense_number].
  - apply Map.wf_empty.
  - apply Map.wf_set; apply IH.
Qed.

Lemma dense_number_spec {K} (E : encoding K) keys start k i :
  NoDup keys ->
  (Map.get E k (dense_number E keys start) = Some i <->
    exists n, nth_error keys n = Some k /\ i = (start + N.of_nat n)%N).
Proof.
  revert start; induction keys as [|x rest IH]; intros start Hnodup.
  - cbn [dense_number]; rewrite Map.get_empty; split; [discriminate|].
    intros [n [Hnth _]]; destruct n; discriminate.
  - inversion Hnodup as [|head tail Habsent Hrest]; subst head tail.
    cbn [dense_number].
    destruct (Pos.eq_dec (encode E k) (encode E x)) as [Heq|Hne].
    + apply (encode_injective E) in Heq; subst x; rewrite Map.get_set_same.
      split.
      * intro Heq; injection Heq as Heq; exists 0; cbn; split; [reflexivity|lia].
      * intros [[|n] [Hnth Heq]]; cbn in Hnth.
        -- f_equal; lia.
        -- exfalso; apply Habsent; eapply nth_error_In; exact Hnth.
    + assert (Hkeys : k <> x) by (intro Heq; subst x; contradiction).
      rewrite Map.get_set_other by exact Hkeys.
      rewrite IH by exact Hrest; split.
      * intros [n [Hnth Heq]]; exists (S n); cbn [nth_error].
        split; [exact Hnth|rewrite Nat2N.inj_succ; lia].
      * intros [[|n] [Hnth Heq]]; cbn [nth_error] in Hnth.
        -- injection Hnth as Hnth; congruence.
        -- exists n; split; [exact Hnth|rewrite Nat2N.inj_succ in Heq; lia].
Qed.

(** Preparation retains first occurrences and builds the position and length caches once. *)
Definition dense_prepare {K} (E : encoding K) (keys : list K) : dense_universe K :=
  let unique := dense_unique E FinSet.empty keys in
  DenseUniverse K unique (dense_number E unique 0%N) (N.of_nat (List.length unique)).

Lemma dense_prepare_members {K} (E : encoding K) keys k :
  In k (dense_keys (dense_prepare E keys)) <-> In k keys.
Proof.
  unfold dense_prepare; cbn [dense_keys]; rewrite dense_unique_spec, FinSet.mem_empty; tauto.
Qed.

(** Every prepared universe has exact caches and duplicate-free keys. *)
Theorem dense_prepare_wf {K} (E : encoding K) (keys : list K) :
  dense_universe_wf E (dense_prepare E keys).
Proof.
  unfold dense_universe_wf, dense_prepare; cbn.
  split; [apply dense_unique_nodup|].
  split; [apply dense_number_wf|].
  split; [reflexivity|].
  intros k i; rewrite dense_number_spec by apply dense_unique_nodup.
  split.
  - intros [n [Hnth Heq]]; cbn in Heq; subst i; rewrite Nat2N.id; exact Hnth.
  - intro Hnth; exists (N.to_nat i); split; [exact Hnth|].
    cbn; symmetry; apply N2Nat.id.
Qed.

(** * Packed operations *)

(** Dense sets use arbitrary-precision nonnegative binary integers. *)
Definition dense_set := N.

(** The empty bitset has no set position. *)
Definition dense_empty : dense_set := 0%N.

Definition dense_mask {K} (u : dense_universe K) (s : dense_set) : dense_set :=
  N.land s (N.ones (dense_length u)).

(** Membership uses one prepared lookup and one bit test. *)
Definition dense_mem {K} (E : encoding K) (u : dense_universe K) (k : K)
    (s : dense_set) : bool :=
  match Map.get E k (dense_index u) with
  | Some i => N.testbit s i
  | None => false
  end.

(** Adding an outside key leaves the bitset unchanged. *)
Definition dense_add {K} (E : encoding K) (u : dense_universe K) (k : K)
    (s : dense_set) : dense_set :=
  match Map.get E k (dense_index u) with
  | Some i => N.setbit (dense_mask u s) i
  | None => s
  end.

(** Removing an outside key leaves the bitset unchanged. *)
Definition dense_remove {K} (E : encoding K) (u : dense_universe K) (k : K)
    (s : dense_set) : dense_set :=
  match Map.get E k (dense_index u) with
  | Some i => N.clearbit (dense_mask u s) i
  | None => s
  end.

(** Union masks both raw inputs to the cached universe length. *)
Definition dense_union {K} (u : dense_universe K) (a b : dense_set) : dense_set :=
  N.lor (dense_mask u a) (dense_mask u b).

(** Intersection masks both raw inputs to the cached universe length. *)
Definition dense_inter {K} (u : dense_universe K) (a b : dense_set) : dense_set :=
  N.land (dense_mask u a) (dense_mask u b).

(** Difference masks both raw inputs to the cached universe length. *)
Definition dense_diff {K} (u : dense_universe K) (a b : dense_set) : dense_set :=
  N.ldiff (dense_mask u a) (dense_mask u b).

(** Inclusion tests whether the masked difference has any set bit. *)
Definition dense_subset {K} (u : dense_universe K) (a b : dense_set) : bool :=
  N.eqb (dense_diff u a b) 0%N.

Fixpoint dense_selected {K} (keys : list K) (s : dense_set) : list K :=
  match keys with
  | [] => []
  | k :: rest =>
    if N.testbit s 0 then k :: dense_selected rest (N.div2 s)
    else dense_selected rest (N.div2 s)
  end.

(** Conversion enumerates the universe in order and retains exactly its set positions. *)
Definition dense_to_finset {K} (E : encoding K) (u : dense_universe K)
    (s : dense_set) : FinSet.t K :=
  FinSet.of_list E (dense_selected (dense_keys u) s).

Fixpoint dense_pack {K} (E : encoding K) (keys : list K) (s : FinSet.t K) : dense_set :=
  match keys with
  | [] => 0%N
  | k :: rest =>
    if FinSet.mem E k s then (2 * dense_pack E rest s + 1)%N
    else (2 * dense_pack E rest s)%N
  end.

(** Conversion packs only members belonging to the prepared universe. *)
Definition dense_of_finset {K} (E : encoding K) (u : dense_universe K)
    (s : FinSet.t K) : dense_set :=
  dense_pack E (dense_keys u) s.

(** * Position and bit agreement *)

Lemma dense_lookup_bound {K} (E : encoding K) u k i :
  dense_universe_wf E u -> Map.get E k (dense_index u) = Some i ->
  (i < dense_length u)%N.
Proof.
  intros [_ [_ [Hlength Hindex]]] Hget.
  apply Hindex in Hget; rewrite Hlength.
  assert (Hbound : (N.to_nat i < List.length (dense_keys u))%nat).
  { apply nth_error_Some; rewrite Hget; discriminate. }
  lia.
Qed.

Lemma dense_lookup_member {K} (E : encoding K) u k :
  dense_universe_wf E u ->
  ((exists i, Map.get E k (dense_index u) = Some i) <-> In k (dense_keys u)).
Proof.
  intros [_ [_ [_ Hindex]]]; split.
  - intros [i Hget]; apply Hindex in Hget; eapply nth_error_In; exact Hget.
  - intro Hin; apply In_nth_error in Hin; destruct Hin as [n Hnth].
    exists (N.of_nat n); apply Hindex; rewrite Nat2N.id; exact Hnth.
Qed.

Lemma dense_existsb_member {K} (E : encoding K) keys k :
  existsb (fun x => Pos.eqb (encode E x) (encode E k)) keys = true <-> In k keys.
Proof.
  rewrite existsb_exists; split.
  - intros [x [Hin Heq]]; apply Pos.eqb_eq in Heq.
    apply (encode_injective E) in Heq; now subst x.
  - intro Hin; exists k; split; [exact Hin|apply Pos.eqb_refl].
Qed.

Lemma dense_lookup_existsb {K} (E : encoding K) u k :
  dense_universe_wf E u ->
  existsb (fun x => Pos.eqb (encode E x) (encode E k)) (dense_keys u) =
    match Map.get E k (dense_index u) with
    | Some _ => true
    | None => false
    end.
Proof.
  intro Hwf; apply eq_true_iff_eq; rewrite dense_existsb_member.
  rewrite <- (dense_lookup_member E u k Hwf).
  destruct (Map.get E k (dense_index u)) as [i|]; split; intros Hsome; try reflexivity;
    try discriminate; [now exists i|destruct Hsome as [j Hsome]; discriminate].
Qed.

Lemma dense_lookup_eqb {K} (E : encoding K) u k x i j :
  dense_universe_wf E u ->
  Map.get E k (dense_index u) = Some i -> Map.get E x (dense_index u) = Some j ->
  N.eqb i j = Pos.eqb (encode E x) (encode E k).
Proof.
  intros [_ [_ [_ Hindex]]] Hk Hx.
  apply eq_true_iff_eq; rewrite N.eqb_eq, Pos.eqb_eq; split.
  - intro Heq; subst j; apply Hindex in Hk; apply Hindex in Hx.
    assert (Hkeys : x = k) by congruence; now subst x.
  - intro Heq; apply (encode_injective E) in Heq; subst x; congruence.
Qed.

Lemma dense_mask_low {K} (u : dense_universe K) s i :
  (i < dense_length u)%N -> N.testbit (dense_mask u s) i = N.testbit s i.
Proof.
  intro Hbound; unfold dense_mask; rewrite N.land_spec, N.ones_spec_low by exact Hbound.
  apply andb_true_r.
Qed.

Lemma dense_mask_high {K} (u : dense_universe K) s i :
  (dense_length u <= i)%N -> N.testbit (dense_mask u s) i = false.
Proof.
  intro Hbound; unfold dense_mask; rewrite N.land_spec, N.ones_spec_high by exact Hbound.
  apply andb_false_r.
Qed.

Lemma dense_mask_mem {K} (E : encoding K) u s k :
  dense_universe_wf E u -> dense_mem E u k (dense_mask u s) = dense_mem E u k s.
Proof.
  intro Hwf; unfold dense_mem.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget; [|reflexivity].
  apply dense_mask_low; eapply dense_lookup_bound; eassumption.
Qed.

Lemma dense_binary_high {K} (u : dense_universe K) a b i :
  (dense_length u <= i)%N ->
  N.testbit (dense_union u a b) i = false /\
  N.testbit (dense_inter u a b) i = false /\
  N.testbit (dense_diff u a b) i = false.
Proof.
  intro Hbound; unfold dense_union, dense_inter, dense_diff.
  rewrite N.lor_spec, N.land_spec, N.ldiff_spec, !dense_mask_high by exact Hbound.
  repeat split; reflexivity.
Qed.

Lemma dense_selected_spec {K} (keys : list K) s k :
  In k (dense_selected keys s) <->
  exists n, nth_error keys n = Some k /\ N.testbit s (N.of_nat n) = true.
Proof.
  revert s; induction keys as [|x rest IH]; intro s.
  - cbn [dense_selected In]; split; [contradiction|].
    intros [[|n] [Hnth _]]; discriminate.
  - cbn [dense_selected]; destruct (N.testbit s 0) eqn:Hbit.
    + change (x = k \/ In k (dense_selected rest (N.div2 s)) <->
        exists n, nth_error (x :: rest) n = Some k /\
          N.testbit s (N.of_nat n) = true).
      rewrite IH; split.
      * intros [Heq|[n [Hnth Hset]]].
        -- exists 0; split; [cbn; now subst x|exact Hbit].
        -- exists (S n); split; [exact Hnth|].
           rewrite Nat2N.inj_succ, N.testbit_succ_r_div2 by lia; exact Hset.
      * intros [[|n] [Hnth Hset]].
        -- left; now injection Hnth.
        -- right; exists n; split; [exact Hnth|].
           rewrite Nat2N.inj_succ, N.testbit_succ_r_div2 in Hset by lia; exact Hset.
    + rewrite IH; split.
      * intros [n [Hnth Hset]]; exists (S n); split; [exact Hnth|].
        rewrite Nat2N.inj_succ, N.testbit_succ_r_div2 by lia; exact Hset.
      * intros [[|n] [Hnth Hset]].
        -- cbn in Hset; congruence.
        -- exists n; split; [exact Hnth|].
           rewrite Nat2N.inj_succ, N.testbit_succ_r_div2 in Hset by lia; exact Hset.
Qed.

Lemma dense_pack_spec {K} (E : encoding K) keys s n :
  N.testbit (dense_pack E keys s) (N.of_nat n) =
    match nth_error keys n with
    | Some k => FinSet.mem E k s
    | None => false
    end.
Proof.
  revert n; induction keys as [|k rest IH]; intros [|n].
  - reflexivity.
  - apply N.bits_0.
  - cbn [dense_pack nth_error]; destruct (FinSet.mem E k s).
    + apply N.testbit_odd_0.
    + apply N.testbit_even_0.
  - cbn [dense_pack nth_error]; rewrite Nat2N.inj_succ.
    destruct (FinSet.mem E k s).
    + rewrite N.testbit_odd_succ by lia; apply IH.
    + rewrite N.testbit_even_succ by lia; apply IH.
Qed.

(** * Membership refinement and set laws *)

(** Dense membership agrees exactly with the converted finite set, including raw high bits. *)
Theorem dense_mem_refines {K} (E : encoding K) (u : dense_universe K)
    (s : dense_set) (k : K) :
  dense_universe_wf E u ->
  dense_mem E u k s = FinSet.mem E k (dense_to_finset E u s).
Proof.
  intros Hwf; pose proof Hwf as [_ [_ [_ Hindex]]].
  apply eq_true_iff_eq; unfold dense_to_finset; rewrite FinSet.of_list_spec.
  rewrite dense_selected_spec; unfold dense_mem.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget.
  - split.
    + intro Hset; exists (N.to_nat i); split.
      * apply Hindex; exact Hget.
      * rewrite N2Nat.id; exact Hset.
    + intros [n [Hnth Hset]].
      assert (Hlookup : Map.get E k (dense_index u) = Some (N.of_nat n)).
      { apply Hindex; rewrite Nat2N.id; exact Hnth. }
      assert (Heq : i = N.of_nat n) by congruence; now rewrite Heq.
  - split; [discriminate|]; intros [n [Hnth _]].
    assert (Hlookup : Map.get E k (dense_index u) = Some (N.of_nat n)).
    { apply Hindex; rewrite Nat2N.id; exact Hnth. }
    congruence.
Qed.

(** Converting a finite set to dense form restricts its membership to the universe. *)
Theorem dense_roundtrip {K} (E : encoding K) (u : dense_universe K)
    (s : FinSet.t K) (k : K) :
  dense_universe_wf E u -> FinSet.wf E s ->
  dense_mem E u k (dense_of_finset E u s) =
    (FinSet.mem E k s &&
      existsb (fun x => Pos.eqb (encode E x) (encode E k)) (dense_keys u)).
Proof.
  intros Hwf Hset; rewrite (dense_lookup_existsb E u k Hwf).
  unfold dense_mem, dense_of_finset.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget.
  - destruct Hwf as [_ [_ [_ Hindex]]]; apply Hindex in Hget.
    rewrite <- (N2Nat.id i), dense_pack_spec, Hget, andb_true_r; reflexivity.
  - symmetry; apply andb_false_r.
Qed.

(** Union membership is disjunction in the prepared universe. *)
Theorem dense_union_mem {K} (E : encoding K) (u : dense_universe K)
    (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_union u a b) =
    (dense_mem E u k a || dense_mem E u k b).
Proof.
  intro Hwf; unfold dense_mem, dense_union.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget; [|reflexivity].
  rewrite N.lor_spec, !dense_mask_low; [reflexivity| |];
    eapply dense_lookup_bound; eassumption.
Qed.

(** Intersection membership is conjunction in the prepared universe. *)
Theorem dense_inter_mem {K} (E : encoding K) (u : dense_universe K)
    (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_inter u a b) =
    (dense_mem E u k a && dense_mem E u k b).
Proof.
  intro Hwf; unfold dense_mem, dense_inter.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget; [|reflexivity].
  rewrite N.land_spec, !dense_mask_low; [reflexivity| |];
    eapply dense_lookup_bound; eassumption.
Qed.

(** Difference retains exactly first-operand members missing from the second operand. *)
Theorem dense_diff_mem {K} (E : encoding K) (u : dense_universe K)
    (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_diff u a b) =
    (dense_mem E u k a && negb (dense_mem E u k b)).
Proof.
  intro Hwf; unfold dense_mem, dense_diff.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hget; [|reflexivity].
  rewrite N.ldiff_spec, !dense_mask_low; [reflexivity| |];
    eapply dense_lookup_bound; eassumption.
Qed.

Lemma dense_index_position {K} (E : encoding K) u i :
  dense_universe_wf E u -> (i < dense_length u)%N ->
  exists k, Map.get E k (dense_index u) = Some i.
Proof.
  intros [_ [_ [Hlength Hindex]]] Hbound; rewrite Hlength in Hbound.
  destruct (nth_error (dense_keys u) (N.to_nat i)) as [k|] eqn:Hnth.
  - exists k; apply Hindex; exact Hnth.
  - apply nth_error_None in Hnth; lia.
Qed.

(** The binary subset test decides inclusion of all universe-key memberships. *)
Theorem dense_subset_spec {K} (E : encoding K) (u : dense_universe K)
    (a b : dense_set) :
  dense_universe_wf E u ->
  (dense_subset u a b = true <->
    forall k, dense_mem E u k a = true -> dense_mem E u k b = true).
Proof.
  intro Hwf; unfold dense_subset; rewrite N.eqb_eq; split.
  - intros Hzero k Hmem.
    pose proof (dense_diff_mem E u a b k Hwf) as Hdiff.
    rewrite Hzero in Hdiff; unfold dense_mem at 1 in Hdiff.
    destruct (Map.get E k (dense_index u)); rewrite ?N.bits_0 in Hdiff;
      rewrite Hmem in Hdiff;
      destruct (dense_mem E u k b); cbn in Hdiff; congruence.
  - intro Hincl; apply N.bits_inj; intro i; rewrite N.bits_0.
    unfold dense_diff; rewrite N.ldiff_spec.
    destruct (N.lt_ge_cases i (dense_length u)) as [Hlow|Hhigh].
    + rewrite !dense_mask_low by exact Hlow.
      destruct (dense_index_position E u i Hwf Hlow) as [k Hget].
      specialize (Hincl k); unfold dense_mem in Hincl; rewrite Hget in Hincl.
      destruct (N.testbit a i), (N.testbit b i); cbn; intuition discriminate.
    + rewrite dense_mask_high by exact Hhigh; reflexivity.
Qed.

Lemma dense_lookup_mismatch {K} (E : encoding K) u k x i :
  Map.get E k (dense_index u) = None -> Map.get E x (dense_index u) = Some i ->
  Pos.eqb (encode E x) (encode E k) = false.
Proof.
  intros Hnone Hsome; apply not_true_is_false; intro Heq.
  apply Pos.eqb_eq in Heq; apply (encode_injective E) in Heq; subst x; congruence.
Qed.

(** Adding a universe key sets precisely its bit and preserves all other memberships. *)
Theorem dense_add_mem {K} (E : encoding K) (u : dense_universe K)
    (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_add E u k s) =
    (dense_mem E u x s ||
      (Pos.eqb (encode E x) (encode E k) &&
       existsb (fun y => Pos.eqb (encode E y) (encode E k)) (dense_keys u))).
Proof.
  intro Hwf; rewrite (dense_lookup_existsb E u k Hwf).
  unfold dense_add, dense_mem.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hk;
    destruct (Map.get E x (dense_index u)) as [j|] eqn:Hx.
  - rewrite N.setbit_eqb, dense_mask_low by (eapply dense_lookup_bound; eassumption).
    rewrite (dense_lookup_eqb E u k x i j Hwf Hk Hx), andb_true_r; apply orb_comm.
  - pose proof (dense_lookup_mismatch E u x k i Hx Hk) as Hne.
    rewrite Pos.eqb_sym in Hne; rewrite Hne; reflexivity.
  - rewrite andb_false_r, orb_false_r; reflexivity.
  - rewrite andb_false_r; reflexivity.
Qed.

(** Removing a key clears its membership and preserves precisely the other memberships. *)
Theorem dense_remove_mem {K} (E : encoding K) (u : dense_universe K)
    (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_remove E u k s) =
    (dense_mem E u x s && negb (Pos.eqb (encode E x) (encode E k))).
Proof.
  intro Hwf; unfold dense_remove, dense_mem.
  destruct (Map.get E k (dense_index u)) as [i|] eqn:Hk;
    destruct (Map.get E x (dense_index u)) as [j|] eqn:Hx.
  - rewrite N.clearbit_eqb, dense_mask_low by (eapply dense_lookup_bound; eassumption).
    rewrite (dense_lookup_eqb E u k x i j Hwf Hk Hx); reflexivity.
  - reflexivity.
  - rewrite (dense_lookup_mismatch E u k x j Hk Hx); cbn; symmetry; apply andb_true_r.
  - reflexivity.
Qed.
